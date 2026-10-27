module

public import CFSG.Quasithin.Background.G12Twelve
public import CFSG.Quasithin.Background.G12Facts

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def G12CommK (K : Subgroup (GLV V)) (T : V →ₗ[ZMod 2] V) : Prop :=
  ∀ k ∈ K, ∀ x, T (k x) = k (T x)

theorem G12CommK.injective {K : Subgroup (GLV V)} (hirr : IsIrr K ⊤) {T : V →ₗ[ZMod 2] V}
    (hT : G12CommK K T) (hT0 : T ≠ 0) : Function.Injective T := by
  have hinv : Invariant K (LinearMap.ker T) := by
    intro k hk u hu
    rw [LinearMap.mem_ker] at hu ⊢
    rw [hT k hk, hu, map_zero]
  rcases hirr.2.2 (LinearMap.ker T) hinv bot_le le_top with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exfalso
    apply hT0
    ext x
    have : x ∈ LinearMap.ker T := by rw [h]; trivial
    simpa using this

section Fin

variable [Finite V] {f : LinearMap.BilinForm (ZMod 2) V} {K Q H : Subgroup (GLV V)}

theorem g12_exists_radE_mem_of_fullTransvections (hf : IsSymplectic f) (hQ : Q ≤ spSub f)
    {W : Submodule (ZMod 2) V} {v : V} (hv_mem : v ∈ W) (hT : FullTransvections Q W v hv_mem)
    (hW : W = perp f v) {a : V} (hva : f v a = 0) : ∃ c, radE f v a c ∈ Q := by
  let φ : ↥W →ₗ[ZMod 2] ZMod 2 := (f.flip a).comp W.subtype
  have hφ : φ ⟨v, hv_mem⟩ = 0 := hva
  obtain ⟨y, hyQ, hy⟩ := hT.2 φ hφ
  obtain ⟨c, hc⟩ := eq_radE_of_fix hf hva (hQ hyQ) (fun u hu => hy ⟨u, by rw [hW]; exact hu⟩)
  exact ⟨c, hc ▸ hyQ⟩

theorem g12_exists_perp_not_mem_span (hf : IsSymplectic f) {v a : V} (hv0 : v ≠ 0)
    (hd : 4 ≤ Module.finrank (ZMod 2) V) :
    ∃ b, f v b = 0 ∧ b ∉ Submodule.span (ZMod 2) {a, v} := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle : perp f v ≤ Submodule.span (ZMod 2) {a, v} := fun x hx => hcon x (mem_perp_iff.1 hx)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {a, v}) ≤ 2 := by
    have h3 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (↑({a, v} : Finset V) : Set V)) ≤
        ({a, v} : Finset V).card := finrank_span_finset_le_card _
    have h4 : ({a, v} : Finset V).card ≤ 2 := Finset.card_le_two
    have h5 : (↑({a, v} : Finset V) : Set V) = {a, v} := by simp
    rw [h5] at h3
    omega
  have h6 := hf.finrank_perp hv0
  omega

theorem g12_exists_eq_radE_of_mem_Q (hf : IsSymplectic f) (hQ : Q ≤ spSub f)
    {W : Submodule (ZMod 2) V} {v : V} (hv_mem : v ∈ W) (hT : FullTransvections Q W v hv_mem)
    (hW : W = perp f v) {y : GLV V} (hy : y ∈ Q) : ∃ a c, f v a = 0 ∧ y = radE f v a c := by
  subst hW
  obtain ⟨φ, hφ0, hφ⟩ := hT.1 y hy
  obtain ⟨a, hva, ha⟩ := hf.exists_rep_perp hv_mem φ hφ0
  obtain ⟨c, hc⟩ := eq_radE_of_fix hf hva (hQ hy) (fun u hu => by
    have h1 := hφ ⟨u, hu⟩
    rw [← ha ⟨u, hu⟩] at h1
    exact h1)
  exact ⟨a, c, hva, hc⟩

theorem g12_commQ_of_five_le (hf : IsSymplectic f) (hd : 5 ≤ Module.finrank (ZMod 2) V)
    (hirr : IsIrr K ⊤) (hK2 : ∀ g ∈ Q, ∀ k ∈ K, g⁻¹ * k * g ∈ K) (hQ : Q ≤ spSub f)
    {W : Submodule (ZMod 2) V} {v : V} (hv_mem : v ∈ W) (hT : FullTransvections Q W v hv_mem)
    (hW : W = perp f v) {T : V →ₗ[ZMod 2] V} (hTK : G12CommK K T) {y : GLV V} (hy : y ∈ Q) (x : V) :
    T (y x) = y (T x) := by
  classical
  by_cases hT0 : T = 0
  · simp [hT0]
  obtain ⟨a, c, hva, hyr⟩ := g12_exists_eq_radE_of_mem_Q hf hQ hv_mem hT hW hy
  have hyy : ∀ z, y (y z) = z := fun z => by
    have h1 := radE_mul_self hf (c := c) hva
    rw [← hyr] at h1
    exact congrArg (fun g : GLV V => g z) h1
  have hyinv : y⁻¹ = y := by
    refine inv_eq_of_mul_eq_one_right ?_
    exact LinearEquiv.ext hyy
  let D : V →ₗ[ZMod 2] V := (y : V →ₗ[ZMod 2] V) ∘ₗ T ∘ₗ (y : V →ₗ[ZMod 2] V) - T
  have hD : ∀ z, D z = y (T (y z)) - T z := fun z => rfl
  have hDK : G12CommK K D := by
    intro k hk z
    have hk' : y * k * y ∈ K := by
      have := hK2 y hy k hk
      rwa [hyinv] at this
    have e1 : y (k z) = (y * k * y) (y z) := by
      show y (k z) = y (k (y (y z)))
      rw [hyy]
    rw [hD, hD, e1, hTK _ hk', hTK k hk]
    have e2 : y ((y * k * y) (T (y z))) = k (y (T (y z))) := by
      show y (y (k (y (T (y z))))) = k (y (T (y z)))
      rw [hyy]
    rw [e2, map_sub]
  have hrange : LinearMap.range D ≤ Submodule.span (ZMod 2) (↑({T a, T v, a, v} : Finset V) : Set V) := by
    classical
    rintro _ ⟨z, rfl⟩
    have hya : ∀ w, y w = w + f w v • a + (f w a + c * f w v) • v := fun w => by
      rw [hyr]; exact radE_apply hf hva w
    obtain ⟨w, hw⟩ : ∃ w : V, w = T z + f z v • T a + (f z a + c * f z v) • T v := ⟨_, rfl⟩
    have hTy : T (y z) = w := by
      rw [hya z, map_add, map_add, map_smul, map_smul, hw]
    have hDz : D z = y w - T z := by rw [hD, hTy]
    have hmem : ∀ u ∈ ({T a, T v, a, v} : Finset V),
        u ∈ Submodule.span (ZMod 2) (↑({T a, T v, a, v} : Finset V) : Set V) :=
      fun u hu => Submodule.subset_span (by simpa using hu)
    have h1 := hmem (T a) (by simp)
    have h2 := hmem (T v) (by simp)
    have h3 := hmem a (by simp)
    have h4 := hmem v (by simp)
    have e : y w - T z =
        f z v • T a + (f z a + c * f z v) • T v + f w v • a + (f w a + c * f w v) • v := by
      rw [hya w, hw]; abel
    rw [hDz, e]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3))
      (Submodule.smul_mem _ _ h4)
  have hrank : Module.finrank (ZMod 2) (LinearMap.range D) ≤ 4 := by
    classical
    have h1 := Submodule.finrank_mono hrange
    have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (↑({T a, T v, a, v} : Finset V) : Set V)) ≤
        ({T a, T v, a, v} : Finset V).card := finrank_span_finset_le_card _
    have h3 : ({T a, T v, a, v} : Finset V).card ≤ 4 := Finset.card_le_four
    omega
  have hD0 : D = 0 := by
    by_contra hne
    have hinj := hDK.injective hirr hne
    have h1 := LinearMap.finrank_range_add_finrank_ker D
    have h2 : Module.finrank (ZMod 2) (LinearMap.ker D) = 0 := by
      rw [LinearMap.ker_eq_bot.2 hinj]; exact finrank_bot _ _
    omega
  have h5 : y (T (y x)) = T x := by
    have := hD x
    rw [hD0] at this
    have h6 : y (T (y x)) - T x = 0 := by rw [← this]; rfl
    exact sub_eq_zero.1 h6
  have h7 := congrArg (fun w => y w) h5
  simp only [hyy] at h7
  exact h7

theorem g12_eq_id_of_commQ (hf : IsSymplectic f) (hd : 4 ≤ Module.finrank (ZMod 2) V)
    (hirr : IsIrr K ⊤) (hQ : Q ≤ spSub f) {W : Submodule (ZMod 2) V} {v : V} (hv_mem : v ∈ W)
    (hv0 : v ≠ 0) (hT : FullTransvections Q W v hv_mem) (hW : W = perp f v)
    {T : V →ₗ[ZMod 2] V} (hTK : G12CommK K T) (hTQ : ∀ y ∈ Q, ∀ x, T (y x) = y (T x))
    (hT0 : T ≠ 0) : T = LinearMap.id := by
  have hinj := hTK.injective hirr hT0
  have key : ∀ a, f v a = 0 → a ≠ 0 → a ≠ v → T v ∈ Submodule.span (ZMod 2) {a, v} := by
    intro a hva ha0 hav
    obtain ⟨c, hc⟩ := g12_exists_radE_mem_of_fullTransvections hf hQ hv_mem hT hW hva
    obtain ⟨x, hvx, hax⟩ := hf.exists_perp_one (v := v) (w := a) ha0 (Ne.symm hav)
    have hy := hTQ _ hc x
    have hxv : f x v = 0 := by rw [hf.symm']; exact hvx
    have hxa : f x a = 1 := by rw [hf.symm']; exact hax
    rw [radE_apply hf hva, radE_apply hf hva, hxv, hxa] at hy
    simp only [zero_smul, add_zero, mul_zero, map_add, map_smul] at hy
    rw [one_smul, add_assoc] at hy
    have h1 : T v = f (T x) v • a + (f (T x) a + c * f (T x) v) • v := add_left_cancel hy
    rw [h1, Submodule.mem_span_pair]
    exact ⟨_, _, rfl⟩
  obtain ⟨a1, hva1, ha1⟩ := g12_exists_perp_not_mem_span hf (a := v) hv0 hd
  obtain ⟨a2, hva2, ha2⟩ := g12_exists_perp_not_mem_span hf (a := a1) hv0 hd
  have ha1v : a1 ≠ v := fun h => ha1 (h ▸ Submodule.mem_span_pair.2 ⟨1, 0, by simp⟩)
  have ha10 : a1 ≠ 0 := fun h => ha1 (h ▸ Submodule.zero_mem _)
  have ha2v : a2 ≠ v := fun h => ha2 (h ▸ Submodule.mem_span_pair.2 ⟨0, 1, by simp⟩)
  have ha20 : a2 ≠ 0 := fun h => ha2 (h ▸ Submodule.zero_mem _)
  obtain ⟨α1, β1, h1⟩ := Submodule.mem_span_pair.1 (key a1 hva1 ha10 ha1v)
  obtain ⟨α2, β2, h2⟩ := Submodule.mem_span_pair.1 (key a2 hva2 ha20 ha2v)
  have hα2 : α2 = 0 := by
    by_contra hne
    have hα : α2 = 1 := g12_eq_one_of_ne_zero _ hne
    apply ha2
    rw [Submodule.mem_span_pair]
    refine ⟨α1, β1 + β2, ?_⟩
    rw [hα, one_smul] at h2
    have h3 : α1 • a1 + β1 • v = a2 + β2 • v := h1.trans h2.symm
    calc α1 • a1 + (β1 + β2) • v = (α1 • a1 + β1 • v) + β2 • v := by rw [add_smul]; abel
      _ = (a2 + β2 • v) + β2 • v := by rw [h3]
      _ = a2 + (β2 • v + β2 • v) := by rw [add_assoc]
      _ = a2 := by rw [g12_vadd_self, add_zero]
  have hTv : T v = v := by
    rw [hα2, zero_smul, zero_add] at h2
    rcases g12_eq_zero_or_one β2 with h0 | h1'
    · exfalso
      rw [h0, zero_smul] at h2
      exact hv0 (hinj (h2.symm.trans (map_zero T).symm))
    · rw [h1', one_smul] at h2
      exact h2.symm
  by_contra hne
  let S : V →ₗ[ZMod 2] V := T - LinearMap.id
  have hS : G12CommK K S := fun k hk x => by
    simp only [S, LinearMap.sub_apply, LinearMap.id_apply, hTK k hk]
    rw [map_sub]
  have hS0 : S ≠ 0 := fun h => hne (sub_eq_zero.1 h)
  have hSv : S v = S 0 := by
    simp [S, hTv]
  exact hv0 (hS.injective hirr hS0 hSv)

theorem g12_exists_commK_of_not_preserved (hf : IsSymplectic f) {h : GLV V}
    (hhK : ∀ k ∈ K, h⁻¹ * k * h ∈ K) (hfK : FormInv K f)
    (hne : ∃ x y, f (h x) (h y) ≠ f x y) :
    ∃ T : V →ₗ[ZMod 2] V, G12CommK K T ∧ T ≠ 0 ∧ T ≠ LinearMap.id := by
  let f' : LinearMap.BilinForm (ZMod 2) V :=
    f.compl₁₂ (h.symm : V →ₗ[ZMod 2] V) (h.symm : V →ₗ[ZMod 2] V)
  have hf'app : ∀ x y, f' x y = f (h.symm x) (h.symm y) := fun x y => rfl
  let T : V →ₗ[ZMod 2] V :=
    ((LinearMap.BilinForm.toDual f hf.nondegenerate).symm : Module.Dual (ZMod 2) V →ₗ[ZMod 2] V) ∘ₗ f'
  have hT : ∀ x y, f (T x) y = f' x y := fun x y => by
    have := LinearMap.BilinForm.toDual_def (B := f) hf.nondegenerate (m := T x) (n := y)
    rw [← this]
    show (LinearMap.BilinForm.toDual f hf.nondegenerate
      ((LinearMap.BilinForm.toDual f hf.nondegenerate).symm (f' x))) y = f' x y
    rw [LinearEquiv.apply_symm_apply]
  have hext : ∀ u w : V, (∀ y, f u y = f w y) → u = w := fun u w huw => by
    have h0 : u + w = 0 := by
      apply hf.2
      intro y
      rw [map_add, LinearMap.add_apply, huw y, g12_add_self]
    calc u = u + (w + w) := by rw [g12_vadd_self, add_zero]
      _ = (u + w) + w := by rw [add_assoc]
      _ = w := by rw [h0, zero_add]
  refine ⟨T, ?_, ?_, ?_⟩
  · intro k hk x
    apply hext
    intro y
    have hk' : h⁻¹ * k * h ∈ K := hhK k hk
    have e1 : f (k (T x)) y = f' x (k.symm y) := by
      have := hfK k hk (T x) (k.symm y)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [this, hT]
    have e2 : f (T (k x)) y = f' (k x) y := hT _ _
    rw [e1, e2, hf'app, hf'app]
    have e3 : h.symm (k x) = (h⁻¹ * k * h) (h.symm x) := by
      show h⁻¹ (k x) = h⁻¹ (k (h (h⁻¹ x)))
      simp
    have e4 : h.symm (k.symm y) = (h⁻¹ * k * h).symm (h.symm y) := by
      rw [eq_comm, LinearEquiv.symm_apply_eq]
      show h.symm y = h.symm (k (h (h.symm (k.symm y))))
      simp
    rw [e3, e4]
    have := hfK _ hk' (h.symm x) ((h⁻¹ * k * h).symm (h.symm y))
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  · intro h0
    obtain ⟨x, y, hxy⟩ := hne
    apply hxy
    have hz : ∀ u w, f u w = 0 := fun u w => by
      have := hT (h u) (h w)
      rw [h0, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, hf'app] at this
      simpa using this.symm
    rw [hz, hz]
  · intro h1
    obtain ⟨x, y, hxy⟩ := hne
    apply hxy
    have := hT (h x) (h y)
    rw [h1, LinearMap.id_apply, hf'app] at this
    simpa using this

theorem g1212_part4_of_four (h4 : G1212PartFourFact) : G1212Part4 := by
  intro V _ _ _ H K Q W v f hyp hf hKQ hW hconcl
  have hd4' : 4 ≤ Module.finrank (ZMod 2) V := by
    obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank hf.1 hf.nondegenerate
    have := hyp.dim
    omega
  by_cases hd4 : Module.finrank (ZMod 2) V = 4
  · exact h4 V H K Q W v f hyp hf hKQ hW hconcl hd4
  · left
    have hd5 : 5 ≤ Module.finrank (ZMod 2) V := by omega
    intro h hh
    by_contra hne
    have hne' : ∃ x y, f (h x) (h y) ≠ f x y := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hne (fun x y => hcon x y)
    have hKsp : K ≤ spSub f := le_trans le_sup_left hKQ
    have hQsp : Q ≤ spSub f := le_trans le_sup_right hKQ
    have hfK : FormInv K f := fun k hk x y => hKsp hk x y
    have hhK : ∀ k ∈ K, h⁻¹ * k * h ∈ K := fun k hk => by
      have := hyp.normal h⁻¹ (H.inv_mem hh) k hk
      simpa using this
    have hK2 : ∀ g ∈ Q, ∀ k ∈ K, g⁻¹ * k * g ∈ K := fun g hg k hk => by
      have := hyp.normal g⁻¹ (H.inv_mem (hyp.q_le hg)) k hk
      simpa using this
    obtain ⟨T, hTK, hT0, hT1⟩ := g12_exists_commK_of_not_preserved hf hhK hfK hne'
    have hTQ : ∀ y ∈ Q, ∀ x, T (y x) = y (T x) := fun y hy x =>
      g12_commQ_of_five_le hf hd5 hyp.irr hK2 hQsp hyp.v_mem hyp.transvections hW hTK hy x
    exact hT1 (g12_eq_id_of_commQ hf hd4' hyp.irr hQsp hyp.v_mem hyp.v_ne hyp.transvections hW hTK hTQ hT0)

theorem g12_12_of_four (h : G121Stmt) (hF : G1212PartFourFact) : G1212Stmt :=
  g12_12_of_part4 h (g1212_part4_of_four hF)

end Fin

end NoInst

end CFSG.Quasithin.G11
