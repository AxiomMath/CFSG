module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcSixE

public section

namespace CFSG.StandardType

namespace JCoreE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

private theorem exists_char_of_stdPos {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) [Finite k] [CharP k 2]
    (hlin : ∀ γ ∈ D.roots, ∀ h ∈ ggTorus D, ∃ χ : k, ∀ c, h * x γ c * h⁻¹ = x γ (χ * c))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {b : G}
    (hb : ∀ γ ∈ D.roots, ∃ h ∈ ggTorus D, ∀ z ∈ D.rootGroup γ,
      b * ψ z * b⁻¹ = ψ (h * z * h⁻¹)) :
    ∃ a : Fin D.rank → kˣ, ∀ i t,
      b * ψ (x (Pi.single i 1) t) * b⁻¹ = ψ (x (Pi.single i 1) ((a i : k) * t)) ∧
        b * ψ (x (-Pi.single i 1) t) * b⁻¹ = ψ (x (-Pi.single i 1) (((a i)⁻¹ : kˣ) * t)) := by
  have key : ∀ γ ∈ D.roots, ∃ χ : k, ∀ t, b * ψ (x γ t) * b⁻¹ = ψ (x γ (χ * t)) := by
    intro γ hγr
    obtain ⟨h, hh, hz⟩ := hb γ hγr
    obtain ⟨χ, hχ⟩ := hlin γ hγr h hh
    exact ⟨χ, fun t => by rw [hz _ (((hE.param γ hγr).1 _).mpr ⟨t, rfl⟩), hχ]⟩
  choose! χ hχ using key
  choose φ hφinj hφu hφl using hE.rankOne
  have hΦ : ∀ i, Function.Injective (ψ.comp (φ i)) := fun i =>
    PsiDiag.injective_comp_of_ker_le_center (φ i) (hφinj i) ψ hker
  have hx0 : ∀ γ ∈ D.roots, x γ 0 = 1 := by
    intro γ hγr
    have h := (hE.param γ hγr).2.1 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have hχ0 : ∀ i, χ (Pi.single i 1) ≠ 0 := by
    intro i h0
    have h := hχ _ (single_mem_roots i) 1
    rw [h0, zero_mul, hx0 _ (single_mem_roots i), map_one] at h
    have h' : ψ (x (Pi.single i 1) 1) = 1 := by
      calc ψ (x (Pi.single i 1) 1) = b⁻¹ * (b * ψ (x (Pi.single i 1) 1) * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group
    have h'' : (ψ.comp (φ i)) (sl2Upper 1) = (ψ.comp (φ i)) 1 := by
      rw [MonoidHom.comp_apply, hφu, h', map_one]
    have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 0 1) (hΦ i h'')
    simp [sl2Upper] at h3
  refine ⟨fun i => Units.mk0 (χ (Pi.single i 1)) (hχ0 i), fun i t => ⟨?_, ?_⟩⟩
  · exact hχ _ (single_mem_roots i) t
  · have hm := PsiDiagChar.mul_eq_one_of_conj_sl2 (ψ.comp (φ i)) (hΦ i) (d := b⁻¹)
      (Units.mk0 _ (hχ0 i)) (χ' := χ (-Pi.single i 1))
      (fun c' => by
        rw [inv_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hφu, hφu]
        exact hχ _ (single_mem_roots i) c')
      (fun c' => by
        rw [inv_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hφl, hφl]
        exact hχ _ (neg_single_mem_roots i) c')
    rw [hχ _ (neg_single_mem_roots i) t, eq_inv_of_mul_eq_one_right hm,
      Units.val_inv_eq_inv_val]

theorem exists_induces_rootDiag_E6
    {k : Type} [Field k] [Finite k] [CharP k 2] {G : Type*} [Group G]
    (ψ : ↥(Minuscule.e6Data_valid.minGroup k) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(Minuscule.e6Data_valid.minGroup k)) {y : G}
    (hyN : y ∈ Subgroup.normalizer (ψ.range : Set G)) {p : ℕ} (hyp : y ^ p = 1)
    (hy : ∀ γ ∈ (Minuscule.e6Datum k).roots, ∃ h ∈ ggTorus (Minuscule.e6Datum k),
      ∀ z ∈ (Minuscule.e6Datum k).rootGroup γ, y * ψ z * y⁻¹ = ψ (h * z * h⁻¹)) :
    ∃ a : Fin Tag.E6.rank → kˣ, a ^ p = 1 ∧
      LayerSixE.GGInduces (Isogeny.e6Isogeny k) ψ y
        (CFSG.LieType.Chevalley.rootDiagAutHom .E6 k a) := by
  obtain ⟨O⟩ := Minuscule.e6_nonempty_commOrder k
  have hE := (Minuscule.e6Data_valid.minDatum_chevalleyExtras_commC
    Minuscule.isFiniteType_cartan_E6 k Minuscule.posDef_cartan_E6 Minuscule.neighbour_E6 O).2
  have hlin : ∀ γ ∈ (Minuscule.e6Datum k).roots, ∀ h ∈ ggTorus (Minuscule.e6Datum k),
      ∃ χ : k, ∀ c, h * Minuscule.e6Data_valid.xm k γ c * h⁻¹ =
        Minuscule.e6Data_valid.xm k γ (χ * c) := by
    intro γ hγ h hh
    refine PsiDiag.Minu.conj_xm_eq_of_mem_normalizer Minuscule.e6Data_valid k ?_
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh γ hγ
  obtain ⟨a, ha⟩ := exists_char_of_stdPos hE hlin ψ hker hy
  have hkπ := LayerSixE.ker_le_ker_e6Isogeny hker
  have hδ : LayerSixE.GGInduces (Isogeny.e6Isogeny k) ψ y
      (CFSG.LieType.Chevalley.rootDiagAutHom .E6 k a) := by
    refine LayerSixE.GGInduces.of_generators hkπ
      (Isogeny.closure_xm_simple_eq_top Minuscule.e6Data_valid k) hyN ?_
    rintro z ⟨i, t, rfl | rfl⟩
    · refine ⟨Minuscule.e6Data_valid.xm k (Pi.single i 1) ((a i : k) * t), (ha i t).1.symm, ?_⟩
      rw [RootCentExc.e6Isogeny_xm_single_eq, RootCentExc.e6Isogeny_xm_single_eq,
        RootCentExc.rootDiagAutHom_adjX]
    · refine ⟨Minuscule.e6Data_valid.xm k (-Pi.single i 1) (((a i)⁻¹ : kˣ) * t),
        (ha i t).2.symm, ?_⟩
      rw [RootCentExc.e6Isogeny_xm_neg_single_eq, RootCentExc.e6Isogeny_xm_neg_single_eq,
        RootCentExc.rootDiagAutHom_adjY]
  refine ⟨a, CFSG.LieType.Chevalley.rootDiagAutHom_injective ?_, hδ⟩
  have h1 := hδ.pow hkπ hyN p
  rw [hyp] at h1
  rw [map_pow, map_one]
  exact LayerSixE.GGInduces.unique (Isogeny.e6Isogeny_surjective k) (Subgroup.one_mem _) h1
    (LayerSixE.GGInduces.one hkπ)

theorem le_derivedPreimage_of_isPGroup_two {L C : Type*} [Group L] [Group C] {π : L →* C}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L)
    (hodd : Odd (Nat.card π.ker)) {S : Subgroup C} (hS : Group.IsPerfect ↥S) {P : Subgroup L}
    (hP : IsPGroup 2 P) (hPS : P.map π ≤ S) :
    P ≤ CFSG.RankThree.PartOne.derivedPreimage π S := by
  intro x hx
  obtain ⟨e, he⟩ := hP ⟨x, hx⟩
  have hxe : x ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have hxS : π x ∈ S := hPS ⟨x, hx, rfl⟩
  rw [← CFSG.RankThree.PartOne.map_derivedPreimage_of_perfect hπ hS] at hxS
  obtain ⟨d, hd, hdx⟩ := hxS
  have hz : d⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
  have hzm : (d⁻¹ * x) ^ Nat.card π.ker = 1 := by
    have h := pow_card_eq_one' (G := π.ker) (x := ⟨_, hz⟩)
    simpa using congrArg Subtype.val h
  have hc : Commute d (d⁻¹ * x) := Subgroup.mem_center_iff.mp (hker hz) d
  have hxm : x ^ Nat.card π.ker ∈ CFSG.RankThree.PartOne.derivedPreimage π S := by
    have h : x ^ Nat.card π.ker = d ^ Nat.card π.ker := by
      calc x ^ Nat.card π.ker = (d * (d⁻¹ * x)) ^ Nat.card π.ker := by rw [mul_inv_cancel_left]
        _ = d ^ Nat.card π.ker := by rw [hc.mul_pow, hzm, mul_one]
    rw [h]
    exact pow_mem hd _
  have hcop : Nat.Coprime (Nat.card π.ker) (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxe)
      (Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hodd))
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu]
  exact pow_mem hxm u

end JCoreE6

end CFSG.StandardType

end
