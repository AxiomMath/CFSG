module

public import CFSG.Sporadic.Co1Patterson.TitsMultiCover
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.SuzRecog.TitsTwo

open SimpleGraph CFSG.Monster.B.Recog CFSG.Sporadic.Co1Patterson

section CosetGraph

variable {Z : Type*} [Group Z]

@[expose] def cosetGraph₂ (K L : Subgroup Z) (s : Z) : SimpleGraph ((Z ⧸ K) ⊕ (Z ⧸ L)) :=
  SimpleGraph.fromRel fun x y => ∃ z : Z,
    (x = .inl (z : Z ⧸ K) ∧ y = .inl ((z * s : Z) : Z ⧸ K)) ∨
      (x = .inl (z : Z ⧸ K) ∧ y = .inr (z : Z ⧸ L))

variable {K L : Subgroup Z} {s : Z}

theorem cosetGraph₂_adj_inl_inl {x y : Z ⧸ K} :
    (cosetGraph₂ K L s).Adj (.inl x) (.inl y) ↔ (cosetGraph K s).Adj x y := by
  simp [cosetGraph₂, cosetGraph]

theorem cosetGraph₂_adj_inl_inr {x : Z ⧸ K} {y : Z ⧸ L} :
    (cosetGraph₂ K L s).Adj (.inl x) (.inr y) ↔ ∃ z : Z, x = (z : Z ⧸ K) ∧ y = (z : Z ⧸ L) := by
  simp [cosetGraph₂]

theorem cosetGraph₂_adj_inr_inl {x : Z ⧸ L} {y : Z ⧸ K} :
    (cosetGraph₂ K L s).Adj (.inr x) (.inl y) ↔ ∃ z : Z, y = (z : Z ⧸ K) ∧ x = (z : Z ⧸ L) := by
  rw [SimpleGraph.adj_comm, cosetGraph₂_adj_inl_inr]

theorem cosetGraph₂_not_adj_inr_inr {x y : Z ⧸ L} :
    ¬ (cosetGraph₂ K L s).Adj (.inr x) (.inr y) := by
  simp [cosetGraph₂]

theorem cosetGraph₂_adj_smul (g : Z) {x y : (Z ⧸ K) ⊕ (Z ⧸ L)}
    (h : (cosetGraph₂ K L s).Adj x y) :
    (cosetGraph₂ K L s).Adj (Sum.map (g • ·) (g • ·) x) (Sum.map (g • ·) (g • ·) y) := by
  rcases x with x | x <;> rcases y with y | y
  · rw [cosetGraph₂_adj_inl_inl] at h
    simp only [Sum.map_inl]
    rw [cosetGraph₂_adj_inl_inl]
    exact cosetGraph_adj_smul g h
  · obtain ⟨z, rfl, rfl⟩ := cosetGraph₂_adj_inl_inr.1 h
    simp only [Sum.map_inl, Sum.map_inr]
    exact cosetGraph₂_adj_inl_inr.2 ⟨g * z, rfl, rfl⟩
  · obtain ⟨z, rfl, rfl⟩ := cosetGraph₂_adj_inr_inl.1 h
    simp only [Sum.map_inl, Sum.map_inr]
    exact cosetGraph₂_adj_inr_inl.2 ⟨g * z, rfl, rfl⟩
  · exact absurd h cosetGraph₂_not_adj_inr_inr

@[expose] def cosetGraph₂SMul (K L : Subgroup Z) (s g : Z) :
    cosetGraph₂ K L s →g cosetGraph₂ K L s where
  toFun := Sum.map (g • ·) (g • ·)
  map_rel' h := cosetGraph₂_adj_smul g h

theorem cosetGraph₂SMul_inl (g z : Z) :
    cosetGraph₂SMul K L s g (.inl (z : Z ⧸ K)) = .inl ((g * z : Z) : Z ⧸ K) := rfl

end CosetGraph

section Covering

variable {V : Type*} {Γ : SimpleGraph V} {X : Type*} [Group X] [MulAction X V]
  {Z : Type*} [Group Z]

@[expose] def cosetHom₂ (hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (π : Z →* X) (K L : Subgroup Z) (s : Z) (v w : V) (hK : ∀ a ∈ K, π a • v = v)
    (hL : ∀ a ∈ L, π a • w = w) (hs : Γ.Adj v (π s • v)) (hvw : Γ.Adj v w) :
    cosetGraph₂ K L s →g Γ where
  toFun := Sum.elim (cosetMap π K v hK) (cosetMap π L w hL)
  map_rel' {x y} h := by
    rcases x with x | x <;> rcases y with y | y
    · exact (cosetHom hadj π K s v hK hs).map_adj (cosetGraph₂_adj_inl_inl.1 h)
    · obtain ⟨z, rfl, rfl⟩ := cosetGraph₂_adj_inl_inr.1 h
      simpa [cosetMap_mk] using hadj (π z) hvw
    · obtain ⟨z, rfl, rfl⟩ := cosetGraph₂_adj_inr_inl.1 h
      simpa [cosetMap_mk] using (hadj (π z) hvw).symm
    · exact absurd h cosetGraph₂_not_adj_inr_inr

section Apply

variable (hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
  (π : Z →* X) (K L : Subgroup Z) (s : Z) (v w : V) (hK : ∀ a ∈ K, π a • v = v)
  (hL : ∀ a ∈ L, π a • w = w) (hs : Γ.Adj v (π s • v)) (hvw : Γ.Adj v w)

theorem cosetHom₂_inl (z : Z) :
    cosetHom₂ hadj π K L s v w hK hL hs hvw (.inl (z : Z ⧸ K)) = π z • v := rfl

theorem cosetHom₂_inr (z : Z) :
    cosetHom₂ hadj π K L s v w hK hL hs hvw (.inr (z : Z ⧸ L)) = π z • w := rfl

end Apply

open Tits

theorem mem_w_of_mem_v {w : V} {Xv Xw : Subgroup X} (hXw : ∀ g, g ∈ Xw ↔ g • w = w)
    (π : Z →* X) {Zv Zw : Subgroup Z} (hinjv : Set.InjOn π Zv) (himv : Zv.map π = Xv)
    (hvw' : Xv ⊓ Xw ≤ (Zv ⊓ Zw).map π) {z : Z} (hz : z ∈ Zv) (hzw : π z • w = w) : z ∈ Zw := by
  obtain ⟨c, hc, hcz⟩ := hvw' ⟨himv ▸ Subgroup.mem_map_of_mem π hz, (hXw _).2 hzw⟩
  rw [← hinjv hc.1 hz hcz]
  exact hc.2

theorem mem_v_of_mem_w {v : V} {Xv Xw : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (π : Z →* X) {Zv Zw : Subgroup Z} (hinjw : Set.InjOn π Zw) (himw : Zw.map π = Xw)
    (hvw' : Xv ⊓ Xw ≤ (Zv ⊓ Zw).map π) {z : Z} (hz : z ∈ Zw) (hzv : π z • v = v) : z ∈ Zv := by
  obtain ⟨c, hc, hcz⟩ := hvw' ⟨(hXv _).2 hzv, himw ▸ Subgroup.mem_map_of_mem π hz⟩
  rw [← hinjw hc.2 hz hcz]
  exact hc.1

theorem isCovering_cosetHom₂ (hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {v v₁ w : V} (hvv₁ : Γ.Adj v v₁) (hvw : Γ.Adj v w)
    {Xv Xw Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v) (hXw : ∀ g, g ∈ Xw ↔ g • w = w)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • v₁ = v₁) ∨ (g • v = v₁ ∧ g • v₁ = v))
    (π : Z →* X) {Zv Zw Ze : Subgroup Z}
    (hinjv : Set.InjOn π Zv) (hinjw : Set.InjOn π Zw) (hinje : Set.InjOn π Ze)
    (himv : Zv.map π = Xv) (himw : Zw.map π = Xw) (hime : Ze.map π = Xe)
    (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map π) (hvw' : Xv ⊓ Xw ≤ (Zv ⊓ Zw).map π)
    (hlocv : ∀ y, Γ.Adj v y → (∃ g ∈ Xv, g • v₁ = y) ∨ ∃ g ∈ Xv, g • w = y)
    (hlocw : ∀ y, Γ.Adj w y → ∃ g ∈ Xw, g • v = y) (hsep : ∀ g : X, g • w ≠ v)
    {s : Z} (hsZe : s ∈ Ze) (hsv : π s • v = v₁) (hsw : π s • v₁ = v) :
    IsCovering (cosetHom₂ hadj π Zv Zw s v w (fun _ ha => smul_eq_of_mem hXv π himv ha)
      (fun _ ha => smul_eq_of_mem hXw π himw ha) (hsv ▸ hvv₁) hvw) := by
  have hs := not_mem_of_smul_eq hvv₁ hXv π himv hsv
  have hs₂ := mul_self_mem hXv π hinje hime hve hsZe hsv hsw
  have hsep' : ∀ g h : X, g • v₁ ≠ h • w := by
    intro g h e
    refine hsep ((g * π s)⁻¹ * h) ?_
    rw [mul_smul, ← e, ← hsv, smul_smul g (π s), inv_smul_smul]
  refine IsCovering.of_existsUnique fun x y hxy => ?_
  rcases x with x | x
  · obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
    rw [cosetHom₂_inl] at hxy
    have hy : Γ.Adj v ((π z)⁻¹ • y) := by simpa using hadj (π z)⁻¹ hxy
    rcases hlocv _ hy with ⟨g, hg, hgy⟩ | ⟨g, hg, hgy⟩
    · obtain ⟨a, ha, rfl⟩ : g ∈ Zv.map π := himv ▸ hg
      refine ⟨.inl ((z * a * s : Z) : Z ⧸ Zv),
        ⟨cosetGraph₂_adj_inl_inl.2 ((cosetGraph_adj_mk_iff hs hs₂).2 ⟨a, ha, rfl⟩), ?_⟩, ?_⟩
      · rw [cosetHom₂_inl, map_mul, map_mul, mul_smul, mul_smul, hsv, hgy, smul_inv_smul]
      · rintro (b | b) ⟨hb, hby⟩
        · obtain ⟨a', ha', rfl⟩ :=
            (cosetGraph_adj_mk_iff hs hs₂).1 (cosetGraph₂_adj_inl_inl.1 hb)
          rw [cosetHom₂_inl, map_mul, map_mul, mul_smul, mul_smul, hsv] at hby
          have h₁ : π a' • v₁ = π a • v₁ := by rw [hgy, ← hby, inv_smul_smul]
          have hc : π (a'⁻¹ * a) • v₁ = v₁ := by
            rw [map_mul, mul_smul, ← h₁, map_inv, inv_smul_smul]
          have hcv : a'⁻¹ * a ∈ Zv := Zv.mul_mem (Zv.inv_mem ha') ha
          have hce : a'⁻¹ * a ∈ Ze := mem_of_mem_of_smul_eq' hXv hXe π hinjv himv hve hcv hc
          have hsc : s⁻¹ * (a'⁻¹ * a) * s ∈ Zv := by
            refine mem_of_mem_of_smul_eq hXv π hinje hime hve
              (Ze.mul_mem (Ze.mul_mem (Ze.inv_mem hsZe) hce) hsZe) ?_
            rw [map_mul, map_mul, mul_smul, mul_smul, hsv, hc, map_inv, inv_smul_eq_iff, hsv]
          congr 1
          rw [QuotientGroup.eq]
          convert hsc using 1
          group
        · obtain ⟨z', -, rfl⟩ := cosetGraph₂_adj_inl_inr.1 hb
          rw [cosetHom₂_inr] at hby
          exact absurd (by rw [mul_smul, hgy, smul_inv_smul, hby]) (hsep' (π z * π a) (π z'))
    · obtain ⟨a, ha, rfl⟩ : g ∈ Zv.map π := himv ▸ hg
      refine ⟨.inr ((z * a : Z) : Z ⧸ Zw),
        ⟨cosetGraph₂_adj_inl_inr.2 ⟨z * a, QuotientGroup.eq.2 (by simpa using ha), rfl⟩, ?_⟩, ?_⟩
      · rw [cosetHom₂_inr, map_mul, mul_smul, hgy, smul_inv_smul]
      · rintro (b | b) ⟨hb, hby⟩
        · obtain ⟨a', ha', rfl⟩ :=
            (cosetGraph_adj_mk_iff hs hs₂).1 (cosetGraph₂_adj_inl_inl.1 hb)
          rw [cosetHom₂_inl, map_mul, map_mul, mul_smul, mul_smul, hsv] at hby
          exact absurd (by rw [mul_smul, hby, mul_smul, hgy, smul_inv_smul])
            (hsep' (π z * π a') (π z * π a))
        · obtain ⟨z', hz', rfl⟩ := cosetGraph₂_adj_inl_inr.1 hb
          rw [cosetHom₂_inr] at hby
          have hcv : a⁻¹ * (z⁻¹ * z') ∈ Zv := Zv.mul_mem (Zv.inv_mem ha) (QuotientGroup.eq.1 hz')
          have hcw : π (a⁻¹ * (z⁻¹ * z')) • w = w := by
            rw [map_mul, map_mul, map_inv, map_inv, mul_smul, mul_smul, hby, ← hgy, inv_smul_smul]
          have hcW := mem_w_of_mem_v hXw π hinjv himv hvw' hcv hcw
          congr 1
          rw [QuotientGroup.eq]
          convert Zw.inv_mem hcW using 1
          group
  · obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
    rw [cosetHom₂_inr] at hxy
    have hy : Γ.Adj w ((π z)⁻¹ • y) := by simpa using hadj (π z)⁻¹ hxy
    obtain ⟨g, hg, hgy⟩ := hlocw _ hy
    obtain ⟨b, hb, rfl⟩ : g ∈ Zw.map π := himw ▸ hg
    refine ⟨.inl ((z * b : Z) : Z ⧸ Zv),
      ⟨cosetGraph₂_adj_inr_inl.2 ⟨z * b, rfl, QuotientGroup.eq.2 (by simpa using hb)⟩, ?_⟩, ?_⟩
    · rw [cosetHom₂_inl, map_mul, mul_smul, hgy, smul_inv_smul]
    · rintro (c | c) ⟨hc, hcy⟩
      · obtain ⟨z', rfl, hz'⟩ := cosetGraph₂_adj_inr_inl.1 hc
        rw [cosetHom₂_inl] at hcy
        have hdw : b⁻¹ * (z⁻¹ * z') ∈ Zw := Zw.mul_mem (Zw.inv_mem hb) (QuotientGroup.eq.1 hz')
        have hdv : π (b⁻¹ * (z⁻¹ * z')) • v = v := by
          rw [map_mul, map_mul, map_inv, map_inv, mul_smul, mul_smul, hcy, ← hgy, inv_smul_smul]
        have hdV := mem_v_of_mem_w hXv π hinjw himw hvw' hdw hdv
        congr 1
        rw [QuotientGroup.eq]
        convert Zv.inv_mem hdV using 1
        group
      · exact absurd hc cosetGraph₂_not_adj_inr_inr

theorem lift_triangle_inl {T : Set V → Prop}
    (hTinv : ∀ (g : X) (S : Set V), T S → T ((g • ·) '' S))
    (hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {v v₁ w : V} (hvv₁ : Γ.Adj v v₁)
    {Xv Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • v₁ = v₁) ∨ (g • v = v₁ ∧ g • v₁ = v))
    (π : Z →* X) {Zv Zw Ze : Subgroup Z} (hinje : Set.InjOn π Ze)
    (himv : Zv.map π = Xv) (hime : Ze.map π = Xe) (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map π)
    {s : Z} (hsZe : s ∈ Ze) (hsv : π s • v = v₁) (hsw : π s • v₁ = v)
    {ι : Type*} {u : ι → V} {Xt : ι → Subgroup X} {Zt : ι → Subgroup Z}
    (hinjt : ∀ j, Set.InjOn π (Zt j)) (himt : ∀ j, (Zt j).map π = Xt j)
    (hvt : ∀ j, Xv ⊓ Xt j ≤ (Zv ⊓ Zt j).map π) (het : ∀ j, Xe ⊓ Xt j ≤ (Ze ⊓ Zt j).map π)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = v₁ ∧ g • v₁ = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = v₁ ∧ g • v₁ = u j ∧ g • u j = v)
    {κ : Type*} (c c' : κ → Z) (hc : ∀ k, c k ∈ Zv) (hc' : ∀ k, c' k ∈ Zv)
    (hcell : ∀ k, (c k)⁻¹ * s * c' k ∈ Zw)
    (htri : ∀ y₁ y₂, Γ.Adj v y₁ → Γ.Adj y₁ y₂ → Γ.Adj y₂ v → T {v, y₁, y₂} →
      (∃ j, ∃ g ∈ Xv, g • v₁ = y₁ ∧ g • u j = y₂) ∨
      (∃ k, ∃ g ∈ Xv, g • v₁ = y₁ ∧ g • (π (c k) • w) = y₂) ∨
      (∃ k, ∃ g ∈ Xv, g • (π (c k) • w) = y₁ ∧ g • v₁ = y₂))
    (f : cosetGraph₂ Zv Zw s →g Γ) (hfl : ∀ z : Z, f (.inl (z : Z ⧸ Zv)) = π z • v)
    (hfr : ∀ z : Z, f (.inr (z : Z ⧸ Zw)) = π z • w)
    (x : Z ⧸ Zv) (y₁ y₂ : V) (h₁ : Γ.Adj (f (.inl x)) y₁) (h₂ : Γ.Adj y₁ y₂)
    (h₃ : Γ.Adj y₂ (f (.inl x))) (hT : T {f (.inl x), y₁, y₂}) :
    ∃ b c, (cosetGraph₂ Zv Zw s).Adj (.inl x) b ∧ (cosetGraph₂ Zv Zw s).Adj b c ∧
      (cosetGraph₂ Zv Zw s).Adj c (.inl x) ∧ f b = y₁ ∧ f c = y₂ := by
  have hs := not_mem_of_smul_eq hvv₁ hXv π himv hsv
  have hs₂ := mul_self_mem hXv π hinje hime hve hsZe hsv hsw
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  rw [hfl] at h₁ h₃ hT
  have hT' : T {v, (π z)⁻¹ • y₁, (π z)⁻¹ • y₂} := by
    have := hTinv (π z)⁻¹ _ hT
    simpa [Set.image_insert_eq, Set.image_singleton] using this
  rcases htri ((π z)⁻¹ • y₁) ((π z)⁻¹ • y₂) (by simpa using hadj (π z)⁻¹ h₁)
      (hadj (π z)⁻¹ h₂) (by simpa using hadj (π z)⁻¹ h₃) hT' with
    ⟨j, g, hg, hgv₁, hgu⟩ | ⟨k, g, hg, hgv₁, hgc⟩ | ⟨k, g, hg, hgc, hgv₁⟩
  · obtain ⟨a, ha, rfl⟩ : g ∈ Zv.map π := himv ▸ hg
    obtain ⟨τ, hτm, hτv, hτw⟩ := hτ j
    obtain ⟨t, ht, rfl⟩ : τ ∈ (Zt j).map π := (himt j).symm ▸ hτm
    obtain ⟨ρ, hρm, hρv, hρw, hρu⟩ := hρ j
    obtain ⟨r, hr, rfl⟩ : ρ ∈ (Zt j).map π := (himt j).symm ▸ hρm
    have hsr : s⁻¹ * r ∈ Zv :=
      inv_mul_mem_of_tri hXv hXe π hinje hime hve hinjt himt hvt het hsZe hsv ht hτv hτw hr hρv
    have hr₃ : r * r * r ∈ Zv := mem_of_mem_tri_of_smul_eq hXv π hinjt himt hvt
      ((Zt j).mul_mem ((Zt j).mul_mem hr hr) hr) (by simp only [map_mul, mul_smul, hρv, hρw, hρu])
    have e₁ : ((z : Z) : Z ⧸ Zv) = ((z * a : Z) : Z ⧸ Zv) :=
      QuotientGroup.eq.2 (by simpa using ha)
    have e₂ : ((z : Z) : Z ⧸ Zv) = ((z * a * r * r * r : Z) : Z ⧸ Zv) :=
      QuotientGroup.eq.2 (by simpa [mul_assoc] using Zv.mul_mem ha hr₃)
    refine ⟨.inl ((z * a * r : Z) : Z ⧸ Zv), .inl ((z * a * r * r : Z) : Z ⧸ Zv),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [cosetGraph₂_adj_inl_inl, e₁]
      exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
    · rw [cosetGraph₂_adj_inl_inl]
      exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
    · rw [cosetGraph₂_adj_inl_inl, e₂]
      exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
    · rw [hfl, map_mul, map_mul, mul_smul, mul_smul, hρv, hgv₁, smul_inv_smul]
    · rw [hfl, map_mul, map_mul, map_mul, mul_smul, mul_smul, mul_smul, hρv, hρw, hgu,
        smul_inv_smul]
  · obtain ⟨a, ha, rfl⟩ : g ∈ Zv.map π := himv ▸ hg
    refine ⟨.inl ((z * a * s : Z) : Z ⧸ Zv), .inr ((z * a * c k : Z) : Z ⧸ Zw),
      cosetGraph₂_adj_inl_inl.2 ((cosetGraph_adj_mk_iff hs hs₂).2 ⟨a, ha, rfl⟩),
      cosetGraph₂_adj_inl_inr.2 ⟨z * a * s * c' k,
        QuotientGroup.eq.2 (by simpa [mul_assoc] using hc' k),
        QuotientGroup.eq.2 (by simpa [mul_assoc] using hcell k)⟩,
      cosetGraph₂_adj_inr_inl.2 ⟨z * a * c k,
        QuotientGroup.eq.2 (by simpa [mul_assoc] using Zv.mul_mem ha (hc k)), rfl⟩, ?_, ?_⟩
    · rw [hfl, map_mul, map_mul, mul_smul, mul_smul, hsv, hgv₁, smul_inv_smul]
    · rw [hfr, map_mul, map_mul, mul_smul, mul_smul, hgc, smul_inv_smul]
  · obtain ⟨a, ha, rfl⟩ : g ∈ Zv.map π := himv ▸ hg
    refine ⟨.inr ((z * a * c k : Z) : Z ⧸ Zw), .inl ((z * a * s : Z) : Z ⧸ Zv),
      cosetGraph₂_adj_inl_inr.2 ⟨z * a * c k,
        QuotientGroup.eq.2 (by simpa [mul_assoc] using Zv.mul_mem ha (hc k)), rfl⟩,
      cosetGraph₂_adj_inr_inl.2 ⟨z * a * s * c' k,
        QuotientGroup.eq.2 (by simpa [mul_assoc] using hc' k),
        QuotientGroup.eq.2 (by simpa [mul_assoc] using hcell k)⟩,
      (cosetGraph₂_adj_inl_inl.2 ((cosetGraph_adj_mk_iff hs hs₂).2 ⟨a, ha, rfl⟩)).symm, ?_, ?_⟩
    · rw [hfr, map_mul, map_mul, mul_smul, mul_smul, hgc, smul_inv_smul]
    · rw [hfl, map_mul, map_mul, mul_smul, mul_smul, hsv, hgv₁, smul_inv_smul]

theorem liftsTrianglesBy_cosetHom₂ {T : Set V → Prop}
    (hTinv : ∀ (g : X) (S : Set V), T S → T ((g • ·) '' S))
    (hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {v v₁ w : V} (hvv₁ : Γ.Adj v v₁) (hvw : Γ.Adj v w)
    {Xv Xw Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v) (hXw : ∀ g, g ∈ Xw ↔ g • w = w)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • v₁ = v₁) ∨ (g • v = v₁ ∧ g • v₁ = v))
    (π : Z →* X) {Zv Zw Ze : Subgroup Z}
    (hinjv : Set.InjOn π Zv) (hinjw : Set.InjOn π Zw) (hinje : Set.InjOn π Ze)
    (himv : Zv.map π = Xv) (himw : Zw.map π = Xw) (hime : Ze.map π = Xe)
    (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map π) (hvw' : Xv ⊓ Xw ≤ (Zv ⊓ Zw).map π)
    (hlocv : ∀ y, Γ.Adj v y → (∃ g ∈ Xv, g • v₁ = y) ∨ ∃ g ∈ Xv, g • w = y)
    (hlocw : ∀ y, Γ.Adj w y → ∃ g ∈ Xw, g • v = y) (hsep : ∀ g : X, g • w ≠ v)
    {s : Z} (hsZe : s ∈ Ze) (hsv : π s • v = v₁) (hsw : π s • v₁ = v)
    {ι : Type*} {u : ι → V} {Xt : ι → Subgroup X} {Zt : ι → Subgroup Z}
    (hinjt : ∀ j, Set.InjOn π (Zt j)) (himt : ∀ j, (Zt j).map π = Xt j)
    (hvt : ∀ j, Xv ⊓ Xt j ≤ (Zv ⊓ Zt j).map π) (het : ∀ j, Xe ⊓ Xt j ≤ (Ze ⊓ Zt j).map π)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = v₁ ∧ g • v₁ = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = v₁ ∧ g • v₁ = u j ∧ g • u j = v)
    {κ : Type*} (c c' : κ → Z) (hc : ∀ k, c k ∈ Zv) (hc' : ∀ k, c' k ∈ Zv)
    (hcell : ∀ k, (c k)⁻¹ * s * c' k ∈ Zw)
    (htri : ∀ y₁ y₂, Γ.Adj v y₁ → Γ.Adj y₁ y₂ → Γ.Adj y₂ v → T {v, y₁, y₂} →
      (∃ j, ∃ g ∈ Xv, g • v₁ = y₁ ∧ g • u j = y₂) ∨
      (∃ k, ∃ g ∈ Xv, g • v₁ = y₁ ∧ g • (π (c k) • w) = y₂) ∨
      (∃ k, ∃ g ∈ Xv, g • (π (c k) • w) = y₁ ∧ g • v₁ = y₂)) :
    LiftsTrianglesBy (cosetHom₂ hadj π Zv Zw s v w (fun _ ha => smul_eq_of_mem hXv π himv ha)
      (fun _ ha => smul_eq_of_mem hXw π himw ha) (hsv ▸ hvv₁) hvw) T := by
  set f := cosetHom₂ hadj π Zv Zw s v w (fun _ ha => smul_eq_of_mem hXv π himv ha)
    (fun _ ha => smul_eq_of_mem hXw π himw ha) (hsv ▸ hvv₁) hvw with hf
  have hcov : IsCovering f := isCovering_cosetHom₂ hadj hvv₁ hvw hXv hXw hXe π hinjv hinjw
    hinje himv himw hime hve hvw' hlocv hlocw hsep hsZe hsv hsw
  have hl := lift_triangle_inl hTinv hadj hvv₁ hXv hXe π hinje himv hime hve hsZe hsv hsw hinjt
    himt hvt het hτ hρ c c' hc hc' hcell htri f (fun _ => rfl) (fun _ => rfl)
  rintro (x | x) y₁ y₂ h₁ h₂ h₃ hT
  · exact hl x y₁ y₂ h₁ h₂ h₃ hT
  · obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
    change Γ.Adj (π z • w) y₁ at h₁
    change Γ.Adj y₂ (π z • w) at h₃
    have hy : Γ.Adj w ((π z)⁻¹ • y₁) := by simpa using hadj (π z)⁻¹ h₁
    obtain ⟨g, hg, hgy⟩ := hlocw _ hy
    obtain ⟨b, hb, rfl⟩ : g ∈ Zw.map π := himw ▸ hg
    have hab : (cosetGraph₂ Zv Zw s).Adj (.inr (z : Z ⧸ Zw)) (.inl ((z * b : Z) : Z ⧸ Zv)) :=
      cosetGraph₂_adj_inr_inl.2 ⟨z * b, rfl, QuotientGroup.eq.2 (by simpa using hb)⟩
    have hfb : f (.inl ((z * b : Z) : Z ⧸ Zv)) = y₁ := by
      change π (z * b) • v = y₁
      rw [map_mul, mul_smul, hgy, smul_inv_smul]
    have hT' : T {f (.inl ((z * b : Z) : Z ⧸ Zv)), y₂, f (.inr (z : Z ⧸ Zw))} := by
      rw [hfb]
      change T {y₁, y₂, π z • w}
      change T {π z • w, y₁, y₂} at hT
      rwa [Set.insert_comm (π z • w) y₁, Set.pair_comm (π z • w) y₂] at hT
    obtain ⟨b', c', hb', hbc', hc', hfb', hfc'⟩ :=
      hl _ y₂ (f (.inr (z : Z ⧸ Zw))) (hfb ▸ h₂) h₃ (by rw [hfb]; exact h₁) hT'
    have hc'z : c' = .inr (z : Z ⧸ Zw) :=
      (hcov.existsUnique _ (f.map_adj hab.symm)).unique ⟨hc'.symm, hfc'⟩ ⟨hab.symm, rfl⟩
    subst hc'z
    exact ⟨_, b', hab, hb', hbc', hfb, hfb'⟩

theorem reachable_cosetGraph₂ {v v₁ : V} {Xv Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • v₁ = v₁) ∨ (g • v = v₁ ∧ g • v₁ = v))
    (π : Z →* X) {Zv Zw Ze : Subgroup Z} (hinje : Set.InjOn π Ze) (hime : Ze.map π = Xe)
    (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map π) {s : Z} (hs : s ∉ Zv) (hs₂ : s * s ∈ Zv) (hsZe : s ∈ Ze)
    (hsv : π s • v = v₁) {z : Z} (hz : z ∈ Zv ⊔ Zw ⊔ Ze) :
    (cosetGraph₂ Zv Zw s).Reachable (.inl ((1 : Z) : Z ⧸ Zv)) (.inl (z : Z ⧸ Zv)) := by
  have hcl : Zv ⊔ Zw ⊔ Ze = Subgroup.closure ((Zv : Set Z) ∪ Zw ∪ Ze) := by
    rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
      Subgroup.closure_eq]
  rw [hcl] at hz
  have hone : ∀ x ∈ Zv, ((x : Z) : Z ⧸ Zv) = ((1 : Z) : Z ⧸ Zv) := fun x hx =>
    QuotientGroup.eq.2 (by simpa using Zv.inv_mem hx)
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with (hx | hx) | hx
    · rw [hone x hx]
    · have h₁ : (cosetGraph₂ Zv Zw s).Adj (.inl ((1 : Z) : Z ⧸ Zv)) (.inr ((1 : Z) : Z ⧸ Zw)) :=
        cosetGraph₂_adj_inl_inr.2 ⟨1, rfl, rfl⟩
      have h₂ : (cosetGraph₂ Zv Zw s).Adj (.inl (x : Z ⧸ Zv)) (.inr ((1 : Z) : Z ⧸ Zw)) :=
        cosetGraph₂_adj_inl_inr.2 ⟨x, rfl, QuotientGroup.eq.2 (by simpa using hx)⟩
      exact h₁.reachable.trans h₂.symm.reachable
    · rcases (hXe (π x)).1 (hime ▸ Subgroup.mem_map_of_mem π hx) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [hone x (Tits.mem_of_mem_of_smul_eq hXv π hinje hime hve hx h)]
      · refine SimpleGraph.Adj.reachable ?_
        have hsx : s⁻¹ * x ∈ Zv := Tits.mem_of_mem_of_smul_eq hXv π hinje hime hve
          (Ze.mul_mem (Ze.inv_mem hsZe) hx)
          (by rw [map_mul, mul_smul, h, map_inv, inv_smul_eq_iff, hsv])
        rw [cosetGraph₂_adj_inl_inl]
        simpa using cosetGraph_adj_mk_mul hs hs₂ 1 hsx
  | one => rfl
  | mul x y _ _ ihx ihy =>
    refine ihx.trans ?_
    simpa [cosetGraph₂SMul_inl] using ihy.map (cosetGraph₂SMul Zv Zw s x)
  | inv x _ ih =>
    refine SimpleGraph.Reachable.symm ?_
    simpa [cosetGraph₂SMul_inl] using ih.map (cosetGraph₂SMul Zv Zw s x⁻¹)

theorem injOn_sup_two {T : Set V → Prop} (hΓ : TriangulableBy Γ T)
    (hTinv : ∀ (g : X) (S : Set V), T S → T ((g • ·) '' S))
    (hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {v v₁ w : V} (hvv₁ : Γ.Adj v v₁) (hvw : Γ.Adj v w)
    {Xv Xw Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v) (hXw : ∀ g, g ∈ Xw ↔ g • w = w)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • v₁ = v₁) ∨ (g • v = v₁ ∧ g • v₁ = v))
    (π : Z →* X) {Zv Zw Ze : Subgroup Z}
    (hinjv : Set.InjOn π Zv) (hinjw : Set.InjOn π Zw) (hinje : Set.InjOn π Ze)
    (himv : Zv.map π = Xv) (himw : Zw.map π = Xw) (hime : Ze.map π = Xe)
    (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map π) (hvw' : Xv ⊓ Xw ≤ (Zv ⊓ Zw).map π)
    (hlocv : ∀ y, Γ.Adj v y → (∃ g ∈ Xv, g • v₁ = y) ∨ ∃ g ∈ Xv, g • w = y)
    (hlocw : ∀ y, Γ.Adj w y → ∃ g ∈ Xw, g • v = y) (hsep : ∀ g : X, g • w ≠ v)
    {s : Z} (hsZe : s ∈ Ze) (hsv : π s • v = v₁) (hsw : π s • v₁ = v)
    {ι : Type*} {u : ι → V} {Xt : ι → Subgroup X} {Zt : ι → Subgroup Z}
    (hinjt : ∀ j, Set.InjOn π (Zt j)) (himt : ∀ j, (Zt j).map π = Xt j)
    (hvt : ∀ j, Xv ⊓ Xt j ≤ (Zv ⊓ Zt j).map π) (het : ∀ j, Xe ⊓ Xt j ≤ (Ze ⊓ Zt j).map π)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = v₁ ∧ g • v₁ = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = v₁ ∧ g • v₁ = u j ∧ g • u j = v)
    {κ : Type*} (c c' : κ → Z) (hc : ∀ k, c k ∈ Zv) (hc' : ∀ k, c' k ∈ Zv)
    (hcell : ∀ k, (c k)⁻¹ * s * c' k ∈ Zw)
    (htri : ∀ y₁ y₂, Γ.Adj v y₁ → Γ.Adj y₁ y₂ → Γ.Adj y₂ v → T {v, y₁, y₂} →
      (∃ j, ∃ g ∈ Xv, g • v₁ = y₁ ∧ g • u j = y₂) ∨
      (∃ k, ∃ g ∈ Xv, g • v₁ = y₁ ∧ g • (π (c k) • w) = y₂) ∨
      (∃ k, ∃ g ∈ Xv, g • (π (c k) • w) = y₁ ∧ g • v₁ = y₂)) :
    Set.InjOn π (Zv ⊔ Zw ⊔ Ze : Subgroup Z) := by
  have hs := Tits.not_mem_of_smul_eq hvv₁ hXv π himv hsv
  have hs₂ := Tits.mul_self_mem hXv π hinje hime hve hsZe hsv hsw
  have hcov := isCovering_cosetHom₂ hadj hvv₁ hvw hXv hXw hXe π hinjv hinjw hinje himv himw hime
    hve hvw' hlocv hlocw hsep hsZe hsv hsw
  have htr := liftsTrianglesBy_cosetHom₂ hTinv hadj hvv₁ hvw hXv hXw hXe π hinjv hinjw hinje himv
    himw hime hve hvw' hlocv hlocw hsep hsZe hsv hsw hinjt himt hvt het hτ hρ c c' hc hc' hcell htri
  have key : ∀ z ∈ Zv ⊔ Zw ⊔ Ze, π z = 1 → z = 1 := by
    intro z hz hπz
    have heq := eq_of_reachable_by hcov htr hΓ
      (reachable_cosetGraph₂ hXv hXe π hinje hime hve hs hs₂ hsZe hsv hz)
      (by rw [cosetHom₂_inl, cosetHom₂_inl, hπz, map_one])
    have hzv : z ∈ Zv := by simpa using QuotientGroup.eq.1 (Sum.inl_injective heq)
    exact hinjv hzv Zv.one_mem (by rw [hπz, map_one])
  intro z₁ h₁ z₂ h₂ h
  exact inv_mul_eq_one.1 (key _ ((Zv ⊔ Zw ⊔ Ze).mul_mem ((Zv ⊔ Zw ⊔ Ze).inv_mem h₁) h₂)
    (by rw [map_mul, map_inv, h, inv_mul_cancel]))

end Covering

theorem sup_eq_top_two {V : Type*} {Γ : SimpleGraph V} {X : Type*} [Group X] [MulAction X V]
    (hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b)) (hconn : Γ.Preconnected)
    {v v₁ w : V} {Xv Xw Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • v₁ = v₁) ∨ (g • v = v₁ ∧ g • v₁ = v))
    (hlocv : ∀ y, Γ.Adj v y → (∃ g ∈ Xv, g • v₁ = y) ∨ ∃ g ∈ Xv, g • w = y)
    (hlocw : ∀ y, Γ.Adj w y → ∃ g ∈ Xw, g • v = y) (hsep : ∀ g : X, g • w ≠ v)
    {s : X} (hs : s • v = v₁ ∧ s • v₁ = v) :
    Xv ⊔ Xw ⊔ Xe = ⊤ := by
  have hsXe : s ∈ Xe := (hXe s).2 (Or.inr hs)
  have hvL : Xv ≤ Xv ⊔ Xw ⊔ Xe := le_sup_left.trans le_sup_left
  have hwL : Xw ≤ Xv ⊔ Xw ⊔ Xe := le_sup_right.trans le_sup_left
  have heL : Xe ≤ Xv ⊔ Xw ⊔ Xe := le_sup_right
  have step : ∀ {a x : V} (q : Γ.Walk a x),
      ((∃ k ∈ Xv ⊔ Xw ⊔ Xe, k • v = a) ∨ ∃ k ∈ Xv ⊔ Xw ⊔ Xe, k • w = a) →
        (∃ k ∈ Xv ⊔ Xw ⊔ Xe, k • v = x) ∨ ∃ k ∈ Xv ⊔ Xw ⊔ Xe, k • w = x := by
    intro a x q
    induction q with
    | nil => exact id
    | @cons a b x h q ih =>
      intro ha
      apply ih
      rcases ha with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      · rcases hlocv _ (by simpa using hadj k⁻¹ h) with ⟨g, hg, hgb⟩ | ⟨g, hg, hgb⟩
        · exact Or.inl ⟨k * g * s, mul_mem (mul_mem hk (hvL hg)) (heL hsXe),
            by rw [mul_smul, mul_smul, hs.1, hgb, smul_inv_smul]⟩
        · exact Or.inr ⟨k * g, mul_mem hk (hvL hg), by rw [mul_smul, hgb, smul_inv_smul]⟩
      · obtain ⟨g, hg, hgb⟩ := hlocw _ (by simpa using hadj k⁻¹ h)
        exact Or.inl ⟨k * g, mul_mem hk (hwL hg), by rw [mul_smul, hgb, smul_inv_smul]⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨q⟩ := hconn v (x • v)
  rcases step q (Or.inl ⟨1, one_mem _, one_smul _ _⟩) with ⟨k, hk, hkx⟩ | ⟨k, hk, hkx⟩
  · have : k⁻¹ * x ∈ Xv := (hXv _).2 (by rw [mul_smul, ← hkx, inv_smul_smul])
    simpa using mul_mem hk (hvL this)
  · exact absurd (by rw [mul_smul, hkx, inv_smul_smul]) (hsep (x⁻¹ * k))

theorem tits_universal_completion_two {V : Type*} {Γ : SimpleGraph V} {X : Type*} [Group X]
    [MulAction X V] {T : Set V → Prop}
    (hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hTinv : ∀ (g : X) (S : Set V), T S → T ((g • ·) '' S))
    (hconn : Γ.Preconnected) (hΓ : TriangulableBy Γ T)
    {p p₁ q : V} (hpp₁ : Γ.Adj p p₁) (hpq : Γ.Adj p q) (hsep : ∀ g : X, g • q ≠ p)
    (Xp Xq Xe : Subgroup X)
    (hlocp : ∀ y, Γ.Adj p y → (∃ g ∈ Xp, g • p₁ = y) ∨ ∃ g ∈ Xp, g • q = y)
    (hlocq : ∀ y, Γ.Adj q y → ∃ g ∈ Xq, g • p = y)
    (hXp : ∀ g, g ∈ Xp ↔ g • p = p) (hXq : ∀ g, g ∈ Xq ↔ g • q = q)
    (hXe : ∀ g, g ∈ Xe ↔ (g • p = p ∧ g • p₁ = p₁) ∨ (g • p = p₁ ∧ g • p₁ = p))
    {ι : Type*} (u : ι → V) (Xt : ι → Subgroup X)
    (hXt : ∀ j, ∀ g ∈ Xt j, g • p = p ∨ g • p = p₁ ∨ g • p = u j)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • p = p₁ ∧ g • p₁ = p)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • p = p₁ ∧ g • p₁ = u j ∧ g • u j = p)
    (s : X) (hs : s • p = p₁ ∧ s • p₁ = p)
    {κ : Type*} (c c' : κ → X) (hc : ∀ k, c k ∈ Xp) (hc' : ∀ k, c' k ∈ Xp)
    (hcell : ∀ k, s • c' k • q = c k • q)
    (htri : ∀ y₁ y₂, Γ.Adj p y₁ → Γ.Adj y₁ y₂ → Γ.Adj y₂ p → T {p, y₁, y₂} →
      (∃ j, ∃ g ∈ Xp, g • p₁ = y₁ ∧ g • u j = y₂) ∨
      (∃ k, ∃ g ∈ Xp, g • p₁ = y₁ ∧ g • c k • q = y₂) ∨
      (∃ k, ∃ g ∈ Xp, g • c k • q = y₁ ∧ g • p₁ = y₂))
    {Y : Type*} [Group Y] (φp : Xp →* Y) (φq : Xq →* Y) (φe : Xe →* Y) (φt : ∀ j, Xt j →* Y)
    (hpq' : ∀ a (ha : a ∈ Xp) (hb : a ∈ Xq), φp ⟨a, ha⟩ = φq ⟨a, hb⟩)
    (hpe : ∀ a (ha : a ∈ Xp) (hb : a ∈ Xe), φp ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hpt : ∀ j a (ha : a ∈ Xp) (hb : a ∈ Xt j), φp ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ Xe) (hb : a ∈ Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (hrel : ∀ k (hk : (c k)⁻¹ * s * c' k ∈ Xq) (hse : s ∈ Xe),
      φq ⟨_, hk⟩ = (φp ⟨c k, hc k⟩)⁻¹ * φe ⟨s, hse⟩ * φp ⟨c' k, hc' k⟩) :
    ∃! Φ : X →* Y, (∀ a : Xp, Φ a = φp a) ∧ (∀ a : Xq, Φ a = φq a) ∧ (∀ a : Xe, Φ a = φe a) ∧
      ∀ j (a : Xt j), Φ a = φt j a := by
  have hsXe : s ∈ Xe := (hXe s).2 (Or.inr hs)
  have hcq : ∀ k, (c k)⁻¹ * s * c' k ∈ Xq := fun k =>
    (hXq _).2 (by rw [mul_smul, mul_smul, hcell, inv_smul_smul])
  set K := homGraph φp ⊔ homGraph φq ⊔ homGraph φe with hK
  have hcellZ : ∀ k, ((φp ⟨c k, hc k⟩, c k) : Y × X)⁻¹ * (φe ⟨s, hsXe⟩, s) *
      (φp ⟨c' k, hc' k⟩, c' k) ∈ homGraph φq := fun k => by
    have e : ((φp ⟨c k, hc k⟩, c k) : Y × X)⁻¹ * (φe ⟨s, hsXe⟩, s) * (φp ⟨c' k, hc' k⟩, c' k) =
        (φq ⟨_, hcq k⟩, (c k)⁻¹ * s * c' k) := Prod.ext (hrel k (hcq k) hsXe).symm rfl
    rw [e]
    exact mk_mem_homGraph φq ⟨_, hcq k⟩
  have hinj : Set.InjOn (MonoidHom.snd Y X) K :=
    injOn_sup_two hΓ hTinv hadj hpp₁ hpq hXp hXq hXe (MonoidHom.snd Y X)
      (injOn_snd_homGraph φp) (injOn_snd_homGraph φq) (injOn_snd_homGraph φe)
      (map_snd_homGraph φp) (map_snd_homGraph φq) (map_snd_homGraph φe)
      (inf_le_map_inf_homGraph hpe) (inf_le_map_inf_homGraph hpq') hlocp hlocq hsep
      (mk_mem_homGraph φe ⟨s, hsXe⟩) hs.1 hs.2
      (fun j => injOn_snd_homGraph (φt j)) (fun j => map_snd_homGraph (φt j))
      (fun j => inf_le_map_inf_homGraph (hpt j)) (fun j => inf_le_map_inf_homGraph (het j))
      hτ hρ (fun k => (φp ⟨c k, hc k⟩, c k)) (fun k => (φp ⟨c' k, hc' k⟩, c' k))
      (fun k => mk_mem_homGraph φp ⟨c k, hc k⟩) (fun k => mk_mem_homGraph φp ⟨c' k, hc' k⟩)
      hcellZ htri
  have htop : Xp ⊔ Xq ⊔ Xe = ⊤ := sup_eq_top_two hadj hconn hXp hXe hlocp hlocq hsep hs
  have hsurj : K.map (MonoidHom.snd Y X) = ⊤ := by
    rw [hK, Subgroup.map_sup, Subgroup.map_sup, map_snd_homGraph, map_snd_homGraph,
      map_snd_homGraph, htop]
  have hpK : ∀ a : Xp, (φp a, (a : X)) ∈ K := fun a =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (mk_mem_homGraph φp a))
  have hqK : ∀ a : Xq, (φq a, (a : X)) ∈ K := fun a =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (mk_mem_homGraph φq a))
  have heK : ∀ a : Xe, (φe a, (a : X)) ∈ K := fun a =>
    Subgroup.mem_sup_right (mk_mem_homGraph φe a)
  have htK : ∀ j (a : Xt j), (φt j a, (a : X)) ∈ K := by
    intro j
    let L := K.comap ((φt j).prod (Xt j).subtype)
    have hLv : ∀ a : Xt j, (a : X) • p = p → a ∈ L := fun ⟨a, ha⟩ hav => by
      change (φt j ⟨a, ha⟩, a) ∈ K
      rw [← hpt j a ((hXp a).2 hav) ha]
      exact hpK ⟨a, _⟩
    obtain ⟨τ, hτm, hτv, hτw⟩ := hτ j
    obtain ⟨ρ, hρm, hρv, hρw, -⟩ := hρ j
    have hτL : (⟨τ, hτm⟩ : Xt j) ∈ L := by
      change (φt j ⟨τ, hτm⟩, τ) ∈ K
      rw [← het j τ ((hXe τ).2 (Or.inr ⟨hτv, hτw⟩)) hτm]
      exact heK ⟨τ, _⟩
    have hLw : ∀ a : Xt j, (a : X) • p = p₁ → a ∈ L := fun a hav => by
      have : (⟨τ, hτm⟩ : Xt j)⁻¹ * a ∈ L := hLv _ (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hav, inv_smul_eq_iff, hτv])
      simpa using L.mul_mem hτL this
    intro a
    rcases hXt j a a.2 with h | h | h
    · exact hLv a h
    · exact hLw a h
    · have : (⟨ρ, hρm⟩ : Xt j)⁻¹ * a ∈ L := hLw _ (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h, inv_smul_eq_iff, hρw])
      exact (by simpa using L.mul_mem (hLw ⟨ρ, hρm⟩ hρv) this : a ∈ L)
  let f : K →* X := (MonoidHom.snd Y X).comp K.subtype
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (hinj x.2 y.2 h), fun x => ?_⟩
    obtain ⟨r, hr, hrx⟩ : x ∈ K.map (MonoidHom.snd Y X) := hsurj ▸ Subgroup.mem_top x
    exact ⟨⟨r, hr⟩, hrx⟩
  let e : K ≃* X := MulEquiv.ofBijective f hf
  have he : ∀ (r : Y × X) (hr : r ∈ K), e.symm r.2 = ⟨r, hr⟩ := fun r hr =>
    e.symm_apply_eq.2 rfl
  let Φ : X →* Y := (MonoidHom.fst Y X).comp (K.subtype.comp e.symm.toMonoidHom)
  have hΦ : ∀ (r : Y × X), r ∈ K → Φ r.2 = r.1 := fun r hr => by
    change ((e.symm r.2 : K) : Y × X).1 = r.1
    rw [he r hr]
  refine ⟨Φ, ⟨fun a => hΦ _ (hpK a), fun a => hΦ _ (hqK a), fun a => hΦ _ (heK a),
    fun j a => hΦ _ (htK j a)⟩, ?_⟩
  rintro Ψ ⟨hΨp, hΨq, hΨe, -⟩
  have hle : Xp ⊔ Xq ⊔ Xe ≤ MonoidHom.eqLocus Ψ Φ := sup_le (sup_le
    (fun a ha => (hΨp ⟨a, ha⟩).trans (hΦ _ (hpK ⟨a, ha⟩)).symm)
    (fun a ha => (hΨq ⟨a, ha⟩).trans (hΦ _ (hqK ⟨a, ha⟩)).symm))
    (fun a ha => (hΨe ⟨a, ha⟩).trans (hΦ _ (heK ⟨a, ha⟩)).symm)
  rw [htop] at hle
  exact MonoidHom.ext fun x => hle (Subgroup.mem_top x)

structure TitsDataTwo {V : Type*} (Γ : SimpleGraph V) (T : Set V → Prop) (X : Type*) [Group X]
    [MulAction X V] (ι κ : Type*) where
  p : V
  p₁ : V
  q : V
  u : ι → V
  Xp : Subgroup X
  Xq : Subgroup X
  Xe : Subgroup X
  Xt : ι → Subgroup X
  hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b)
  hTinv : ∀ (g : X) (S : Set V), T S → T ((g • ·) '' S)
  hconn : Γ.Preconnected
  hΓ : TriangulableBy Γ T
  hpp₁ : Γ.Adj p p₁
  hpq : Γ.Adj p q
  hsep : ∀ g : X, g • q ≠ p
  hlocp : ∀ y, Γ.Adj p y → (∃ g ∈ Xp, g • p₁ = y) ∨ ∃ g ∈ Xp, g • q = y
  hlocq : ∀ y, Γ.Adj q y → ∃ g ∈ Xq, g • p = y
  hXp : ∀ g, g ∈ Xp ↔ g • p = p
  hXq : ∀ g, g ∈ Xq ↔ g • q = q
  hXe : ∀ g, g ∈ Xe ↔ (g • p = p ∧ g • p₁ = p₁) ∨ (g • p = p₁ ∧ g • p₁ = p)
  hXt : ∀ j, ∀ g ∈ Xt j, g • p = p ∨ g • p = p₁ ∨ g • p = u j
  hτ : ∀ j, ∃ g ∈ Xt j, g • p = p₁ ∧ g • p₁ = p
  hρ : ∀ j, ∃ g ∈ Xt j, g • p = p₁ ∧ g • p₁ = u j ∧ g • u j = p
  s : X
  hs : s • p = p₁ ∧ s • p₁ = p
  c : κ → X
  c' : κ → X
  hc : ∀ k, c k ∈ Xp
  hc' : ∀ k, c' k ∈ Xp
  hcell : ∀ k, s • (c' k • q) = c k • q
  htri : ∀ y₁ y₂, Γ.Adj p y₁ → Γ.Adj y₁ y₂ → Γ.Adj y₂ p → T {p, y₁, y₂} →
    (∃ j, ∃ g ∈ Xp, g • p₁ = y₁ ∧ g • u j = y₂) ∨
    (∃ k, ∃ g ∈ Xp, g • p₁ = y₁ ∧ g • (c k • q) = y₂) ∨
    (∃ k, ∃ g ∈ Xp, g • (c k • q) = y₁ ∧ g • p₁ = y₂)

namespace TitsDataTwo

variable {V : Type*} {Γ : SimpleGraph V} {T : Set V → Prop} {X : Type*} [Group X]
  [MulAction X V] {ι κ : Type*}

theorem cell_mem (D : TitsDataTwo Γ T X ι κ) (k : κ) : (D.c k)⁻¹ * D.s * D.c' k ∈ D.Xq :=
  (D.hXq _).2 (by rw [mul_smul, mul_smul, D.hcell, inv_smul_smul])

theorem s_mem (D : TitsDataTwo Γ T X ι κ) : D.s ∈ D.Xe := (D.hXe _).2 (Or.inr D.hs)

theorem existsUnique_hom (D : TitsDataTwo Γ T X ι κ) {Y : Type*} [Group Y] (φp : D.Xp →* Y)
    (φq : D.Xq →* Y) (φe : D.Xe →* Y) (φt : ∀ j, D.Xt j →* Y)
    (hpq : ∀ a (ha : a ∈ D.Xp) (hb : a ∈ D.Xq), φp ⟨a, ha⟩ = φq ⟨a, hb⟩)
    (hpe : ∀ a (ha : a ∈ D.Xp) (hb : a ∈ D.Xe), φp ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hpt : ∀ j a (ha : a ∈ D.Xp) (hb : a ∈ D.Xt j), φp ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ D.Xe) (hb : a ∈ D.Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (hrel : ∀ k, φq ⟨_, D.cell_mem k⟩ =
      (φp ⟨D.c k, D.hc k⟩)⁻¹ * φe ⟨D.s, D.s_mem⟩ * φp ⟨D.c' k, D.hc' k⟩) :
    ∃! Φ : X →* Y, (∀ a : D.Xp, Φ a = φp a) ∧ (∀ a : D.Xq, Φ a = φq a) ∧
      (∀ a : D.Xe, Φ a = φe a) ∧ ∀ j (a : D.Xt j), Φ a = φt j a :=
  tits_universal_completion_two D.hadj D.hTinv D.hconn D.hΓ D.hpp₁ D.hpq D.hsep D.Xp D.Xq D.Xe
    D.hlocp D.hlocq D.hXp D.hXq D.hXe D.u D.Xt D.hXt D.hτ D.hρ D.s D.hs D.c D.c' D.hc D.hc'
    D.hcell D.htri φp φq φe φt hpq hpe hpt het (fun k _ _ => hrel k)

end TitsDataTwo

end CFSG.Sporadic.SuzRecog.TitsTwo
