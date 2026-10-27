module

public import CFSG.Monster.B.Recog.GenericTits
public import CFSG.Sporadic.Co1Patterson.TitsMultiHomotopy

public section

namespace CFSG.Sporadic.Co1Patterson

open SimpleGraph CFSG.Monster.B.Recog

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {T : Set V → Prop}

@[expose] def LiftsTrianglesBy (f : H →g G) (T : Set V → Prop) : Prop :=
  ∀ a y z, G.Adj (f a) y → G.Adj y z → G.Adj z (f a) → T {f a, y, z} →
    ∃ b c, H.Adj a b ∧ H.Adj b c ∧ H.Adj c a ∧ f b = y ∧ f c = z

theorem liftEnd_triangle_by {f : H →g G} (hf : IsCovering f) (ht : LiftsTrianglesBy f T)
    {x y z v : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) (hT : T {x, y, z})
    (q : G.Walk x v) (a : W) (ha : f a = x) :
    hf.liftEnd (.cons hxy (.cons hyz (.cons hzx q))) a ha = hf.liftEnd q a ha := by
  subst ha
  obtain ⟨b, c, hab, hbc, hca, rfl, rfl⟩ := ht a y z hxy hyz hzx hT
  have e : (Walk.cons hxy (.cons hyz (.cons hzx q)) : G.Walk (f a) v) =
      ((Walk.cons hab (.cons hbc (.cons hca .nil)) : H.Walk a a).map f).append q := by
    simp
  rw [e, hf.liftEnd_append]
  exact hf.liftEnd_congr q (hf.liftEnd_map _ rfl) _ _

theorem ElemMoveBy.liftEnd_eq {f : H →g G} (hf : IsCovering f) (ht : LiftsTrianglesBy f T)
    {u v : V} {p q : G.Walk u v} (hpq : ElemMoveBy T p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  cases hpq with
  | backtrack p q h => rw [hf.liftEnd_append, hf.liftEnd_append, hf.liftEnd_backtrack]
  | triangle p q hxy hyz hzx hT =>
    rw [hf.liftEnd_append, hf.liftEnd_append, liftEnd_triangle_by hf ht hxy hyz hzx hT]

theorem HomotopicBy.liftEnd_eq {f : H →g G} (hf : IsCovering f) (ht : LiftsTrianglesBy f T)
    {u v : V} {p q : G.Walk u v} (hpq : HomotopicBy T p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  induction hpq with
  | rel p q h => exact h.liftEnd_eq hf ht a ha
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem eq_of_reachable_by {f : H →g G} (hf : IsCovering f) (ht : LiftsTrianglesBy f T)
    (hG : TriangulableBy G T) {a a' : W} (hr : H.Reachable a a') (h : f a = f a') : a = a' := by
  obtain ⟨p⟩ := hr
  have h₁ := (hG (f a) ((p.map f).copy rfl h.symm)).liftEnd_eq hf ht a rfl
  rw [IsCovering.liftEnd_copy, IsCovering.liftEnd_map] at h₁
  have h₂ : hf.liftEnd (Walk.nil : G.Walk (f a) (f a)) a rfl = a := by
    simpa using hf.liftEnd_map (Walk.nil : H.Walk a a) rfl
  exact (h₁.trans h₂).symm

section Coset

variable {X Z : Type*} [Group X] [MulAction X V] [Group Z]

open Tits in
theorem liftsTrianglesBy_cosetHom
    (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    (hTinv : ∀ (g : X) (S : Set V), T S → T ((g • ·) '' S))
    {v w : V} (hvw : G.Adj v w) {Xv Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    (p : Z →* X) {Zv Ze : Subgroup Z} (hinje : Set.InjOn p Ze) (himv : Zv.map p = Xv)
    (hime : Ze.map p = Xe) (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map p)
    {ι : Type*} {u : ι → V} {Xt : ι → Subgroup X} {Zt : ι → Subgroup Z}
    (hinjt : ∀ j, Set.InjOn p (Zt j)) (himt : ∀ j, (Zt j).map p = Xt j)
    (hvt : ∀ j, Xv ⊓ Xt j ≤ (Zv ⊓ Zt j).map p) (het : ∀ j, Xe ⊓ Xt j ≤ (Ze ⊓ Zt j).map p)
    {s : Z} (hsZe : s ∈ Ze) (hsv : p s • v = w) (hsw : p s • w = v)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v → T {v, y₁, y₂} →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂) :
    LiftsTrianglesBy (cosetHom hadj p Zv s v (fun _ ha => smul_eq_of_mem hXv p himv ha)
      (hsv ▸ hvw)) T := by
  have hs := not_mem_of_smul_eq hvw hXv p himv hsv
  have hs₂ := mul_self_mem hXv p hinje hime hve hsZe hsv hsw
  intro x y₁ y₂ h₁ h₂ h₃ hT
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  rw [cosetHom_mk] at h₁ h₃ hT
  have hT' : T {v, (p z)⁻¹ • y₁, (p z)⁻¹ • y₂} := by
    have := hTinv (p z)⁻¹ _ hT
    simpa [Set.image_insert_eq, Set.image_singleton] using this
  obtain ⟨j, g, hgv, hgw, hgu⟩ := htri ((p z)⁻¹ • y₁) ((p z)⁻¹ • y₂)
    (by simpa using hadj (p z)⁻¹ h₁) (hadj (p z)⁻¹ h₂) (by simpa using hadj (p z)⁻¹ h₃) hT'
  obtain ⟨a, ha, rfl⟩ : g ∈ Zv.map p := himv ▸ (hXv g).2 hgv
  obtain ⟨τ, hτm, hτv, hτw⟩ := hτ j
  obtain ⟨t, ht, rfl⟩ : τ ∈ (Zt j).map p := (himt j).symm ▸ hτm
  obtain ⟨ρ, hρm, hρv, hρw, hρu⟩ := hρ j
  obtain ⟨r, hr, rfl⟩ : ρ ∈ (Zt j).map p := (himt j).symm ▸ hρm
  have hsr : s⁻¹ * r ∈ Zv :=
    inv_mul_mem_of_tri hXv hXe p hinje hime hve hinjt himt hvt het hsZe hsv ht hτv hτw hr hρv
  have hr₃ : r * r * r ∈ Zv := mem_of_mem_tri_of_smul_eq hXv p hinjt himt hvt
    ((Zt j).mul_mem ((Zt j).mul_mem hr hr) hr) (by simp only [map_mul, mul_smul, hρv, hρw, hρu])
  have e₁ : ((z : Z) : Z ⧸ Zv) = ((z * a : Z) : Z ⧸ Zv) :=
    QuotientGroup.eq.2 (by simpa using ha)
  have e₂ : ((z : Z) : Z ⧸ Zv) = ((z * a * r * r * r : Z) : Z ⧸ Zv) :=
    QuotientGroup.eq.2 (by simpa [mul_assoc] using Zv.mul_mem ha hr₃)
  refine ⟨((z * a * r : Z) : Z ⧸ Zv), ((z * a * r * r : Z) : Z ⧸ Zv), ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₁]
    exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
  · exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
  · rw [e₂]
    exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
  · rw [cosetHom_mk, map_mul, map_mul, mul_smul, mul_smul, hρv, hgw, smul_inv_smul]
  · rw [cosetHom_mk, map_mul, map_mul, map_mul, mul_smul, mul_smul, mul_smul, hρv, hρw, hgu,
      smul_inv_smul]

open Tits in
theorem injOn_sup_of_triangulableBy (hG : TriangulableBy G T)
    (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    (hTinv : ∀ (g : X) (S : Set V), T S → T ((g • ·) '' S))
    {v w : V} (hvw : G.Adj v w) (hloc : ∀ y, G.Adj v y → ∃ g : X, g • v = v ∧ g • w = y)
    (hswap : ∃ g : X, g • v = w ∧ g • w = v)
    {Xv Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    {ι : Type*} {u : ι → V} {Xt : ι → Subgroup X}
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v → T {v, y₁, y₂} →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂)
    (p : Z →* X) {Zv Ze : Subgroup Z} {Zt : ι → Subgroup Z}
    (hinjv : Set.InjOn p Zv) (hinje : Set.InjOn p Ze) (hinjt : ∀ j, Set.InjOn p (Zt j))
    (himv : Zv.map p = Xv) (hime : Ze.map p = Xe) (himt : ∀ j, (Zt j).map p = Xt j)
    (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map p) (hvt : ∀ j, Xv ⊓ Xt j ≤ (Zv ⊓ Zt j).map p)
    (het : ∀ j, Xe ⊓ Xt j ≤ (Ze ⊓ Zt j).map p) :
    Set.InjOn p (Zv ⊔ Ze : Subgroup Z) := by
  obtain ⟨s, hsZe, hsv, hsw⟩ := exists_swap_lift hXe p hime hswap
  have hs := not_mem_of_smul_eq hvw hXv p himv hsv
  have hs₂ := mul_self_mem hXv p hinje hime hve hsZe hsv hsw
  have hcov := isCovering_cosetHom hadj hvw hXv hXe p hinjv hinje himv hime hve hloc hsZe hsv hsw
  have htr := liftsTrianglesBy_cosetHom hadj hTinv hvw hXv hXe p hinje himv hime hve hinjt himt
    hvt het hsZe hsv hsw hτ hρ htri
  have key : ∀ z ∈ Zv ⊔ Ze, p z = 1 → z = 1 := by
    intro z hz hpz
    have heq := eq_of_reachable_by hcov htr hG
      (reachable_cosetGraph hXv hXe p hinje hime hve hs hs₂ hsZe hsv hz)
      (by rw [cosetHom_mk, cosetHom_mk, hpz, map_one])
    have hzv : z ∈ Zv := by simpa using QuotientGroup.eq.1 heq
    exact hinjv hzv Zv.one_mem (by rw [hpz, map_one])
  intro z₁ h₁ z₂ h₂ h
  exact inv_mul_eq_one.1 (key _ ((Zv ⊔ Ze).mul_mem ((Zv ⊔ Ze).inv_mem h₁) h₂)
    (by rw [map_mul, map_inv, h, inv_mul_cancel]))

end Coset

end CFSG.Sporadic.Co1Patterson
