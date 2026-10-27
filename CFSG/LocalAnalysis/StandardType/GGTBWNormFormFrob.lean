module

public import CFSG.LinearAlgebra.FrobeniusIsometryQuadratic
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearFrob
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRest
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusForms
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly

namespace FormFrob

theorem exists_conj_eq_pow_largeEvenProj {K : Type} [Field K] [Finite K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] {H : Subgroup (GL ι K)} {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp1 : ¬ p ∣ Nat.card K - 1)
    (hH : ∀ P : Subgroup H, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → Odd (Nat.card P) →
      ∃ g : H, ∀ s ∈ P, g * s * g⁻¹ = s ^ k)
    {E : Subgroup (LargeEvenProj H)} (hE : IsElemAbelian p E) :
    ∃ z : LargeEvenProj H, ∀ x ∈ E, z * x * z⁻¹ = x ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPp, -, hPmap, hPker⟩ := CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker
    (LargeEvenProjMk H) (QuotientGroup.mk'_surjective _)
    (LinearFrob.not_dvd_card_ker_largeEvenProjMk hp hp1) (TableB.isPGroup_of_isElemAbelian hE)
  have hinj : ∀ x ∈ P, LargeEvenProjMk H x = 1 → x = 1 := fun x hx h1 => by
    have hx' : x ∈ P ⊓ (LargeEvenProjMk H).ker := ⟨hx, h1⟩
    rw [hPker] at hx'
    exact hx'
  have hmemE : ∀ x ∈ P, LargeEvenProjMk H x ∈ E := fun x hx => hPmap ▸ ⟨x, hx, rfl⟩
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hc : x * y * x⁻¹ * y⁻¹ = 1 := hinj _
      (P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)) (by
        have hab : LargeEvenProjMk H x * LargeEvenProjMk H y =
            LargeEvenProjMk H y * LargeEvenProjMk H x :=
          TableB.IsElemAbelian.comm hE (hmemE x hx) (hmemE y hy)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
        group)
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [hc, one_mul]
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨g, hg⟩ := hH P hPcomm hPodd
  refine ⟨LargeEvenProjMk H g, fun x hx => ?_⟩
  rw [← hPmap] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, hg s hs]

open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating
  CFSG.LocalAnalysis.ComponentInitial in
theorem exists_conj_eq_pow_card_statedSp {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (P : Subgroup (StatedSp m K)) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hodd : Odd (Nat.card P)) : ∃ g : StatedSp m K, ∀ s ∈ P, g * s * g⁻¹ = s ^ Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin m ⊕ Fin m → K)
  let φ : StatedSp m K →* ((Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) :=
    e.toMonoidHom.comp ((bilinIsometryGroup (spForm m K)).subtype.comp spEquiv.toMonoidHom)
  have hφinj : Function.Injective φ :=
    e.injective.comp (Subtype.val_injective.comp spEquiv.injective)
  have hφiso : ∀ s v w, spForm m K (φ s v) (φ s w) = spForm m K v w := fun s v w =>
    (spEquiv s).2 v w
  have hsymm : ∀ v w, spForm m K v w = spForm m K w v := fun v w => by
    rw [← (spForm_isAlt (m := m) (K := K)).neg_eq w v, CharTwo.neg_eq]
  have : Finite P := Subtype.finite
  have : Finite (P.map φ) := inferInstanceAs (Finite ↥(φ '' (P : Set (StatedSp m K))))
  have hcomm' : ∀ x ∈ P.map φ, ∀ y ∈ P.map φ, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hodd' : Odd (Nat.card (P.map φ)) := by
    rwa [Subgroup.card_map_of_injective hφinj]
  obtain ⟨g, hg, hconj, -⟩ := CFSG.LinearAlgebra.exists_isometry_conj_eq_pow_card (spForm m K)
    hsymm (fun v hv => spForm_nondegenerate.1 v hv) hcomm' hodd'
    (by rintro _ ⟨s, -, rfl⟩ v w; exact hφiso s v w)
  let gs : Gsp (spForm m K) := ⟨e.symm g, fun v w => hg v w⟩
  have hφG : φ (spEquiv.symm gs) = g := by
    change e ((spEquiv (spEquiv.symm gs) : Gsp (spForm m K)) : LinearMap.GeneralLinearGroup K _) = g
    rw [MulEquiv.apply_symm_apply]
    exact e.apply_symm_apply g
  refine ⟨spEquiv.symm gs, fun s hs => hφinj ?_⟩
  rw [map_mul, map_mul, map_inv, hφG, map_pow, Nat.card_eq_fintype_card]
  exact hconj (φ s) ⟨s, hs, rfl⟩

open CFSG.ClassicalGroups.Orthogonal in
theorem exists_conj_eq_pow_card_sq_statedOmega {K : Type} [Field K] [Finite K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] (QF : QuadraticForm K (ι → K)) {Q₀ : (ι → K) → K}
    (hQ : ⇑QF = Q₀) (hnd : (QuadraticMap.polarBilin QF).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, QF x = 0)
    (P : Subgroup (StatedOmega Q₀)) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hodd : Odd (Nat.card P)) :
    ∃ g : StatedOmega Q₀, ∀ s ∈ P, g * s * g⁻¹ = s ^ (Nat.card K ^ 2) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let φ : StatedOmega Q₀ →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (toLinEquiv ι K).toMonoidHom.comp (StatedOmega Q₀).subtype
  have hφinj : Function.Injective φ := (toLinEquiv ι K).injective.comp Subtype.val_injective
  have hOO : ⁅TauCeti.QuadraticMap.orthogonalGroup QF, TauCeti.QuadraticMap.orthogonalGroup QF⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup QF :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hΩ : ∀ x : GL ι K, x ∈ StatedOmega Q₀ → toLinEquiv ι K x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup QF, TauCeti.QuadraticMap.orthogonalGroup QF⁆ :=
    fun x hx => by
      rw [statedOmega_eq_comap hQ, Subgroup.mem_comap] at hx
      exact hx
  have hφΩ : ∀ s, φ s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup QF,
      TauCeti.QuadraticMap.orthogonalGroup QF⁆ := fun s => hΩ s s.2
  have : Finite P := Subtype.finite
  have : Finite (P.map φ) := inferInstanceAs (Finite ↥(φ '' (P : Set (StatedOmega Q₀))))
  have hcomm' : ∀ x ∈ P.map φ, ∀ y ∈ P.map φ, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hodd' : Odd (Nat.card (P.map φ)) := by
    rwa [Subgroup.card_map_of_injective hφinj]
  obtain ⟨g, hgO, hconj, -⟩ := CFSG.LinearAlgebra.exists_mem_orthogonalGroup_conj_eq_pow_card QF hnd
    hcomm' hodd' (by rintro _ ⟨s, -, rfl⟩; exact hOO (hφΩ s))
  obtain ⟨-, -, -, -, -, hsq, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  have hG : (toLinEquiv ι K).symm (g ^ 2) ∈ StatedOmega Q₀ := by
    rw [statedOmega_eq_comap hQ, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    exact hsq g hgO
  have hφG : φ ⟨_, hG⟩ = g ^ 2 := (toLinEquiv ι K).apply_symm_apply _
  refine ⟨⟨_, hG⟩, fun s hs => hφinj ?_⟩
  rw [map_mul, map_mul, map_inv, hφG, map_pow]
  have h1 := hconj (φ s) ⟨s, hs, rfl⟩
  have h2 := hconj (φ s ^ Fintype.card K) (pow_mem (Subgroup.mem_map_of_mem φ hs) _)
  rw [Nat.card_eq_fintype_card]
  calc g ^ 2 * φ s * (g ^ 2)⁻¹ = g * (g * φ s * g⁻¹) * g⁻¹ := by
        simp only [sq, mul_inv_rev, mul_assoc]
    _ = (φ s ^ Fintype.card K) ^ Fintype.card K := by rw [h1, h2]
    _ = φ s ^ Fintype.card K ^ 2 := by rw [← pow_mul, sq]

end FormFrob

section Row


theorem natCast_sq_eq_one_of_pow_mem {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ)
    (C : Matrix Λ Λ ℤ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V)
    (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M C) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A = Subgroup.closure (Set.range φ))
    {k : ℕ} {u : MulAut ↥A} (hu : u ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hupow : ∀ a, u a = a ^ k) : (k : ZMod p) ^ 2 = 1 := by
  rw [hgen] at hu
  have hs : ggLin (p := p) ι u ∈
      Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i)) := by
    have h1 := Subgroup.mem_map_of_mem (ggLin (p := p) ι) hu
    rw [MonoidHom.map_closure] at h1
    convert h1 using 2
    ext x
    simp
  exact scalar_sq_eq_one_of_cartan_reflection_datum hp5 M hM C hC h α hpair
    (fun i => ggLin (p := p) ι (φ i)) hlin (ggLin (p := p) ι u) hs (k : ZMod p)
    (ggLin_apply_of_forall_pow ι hupow)

open LinearFrob FormFrob in
theorem ggTorusWNormSC_sp_frob {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} [NeZero m]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) := by
  intro L _ _ ψ hψ hker hperf A hA hAI _ hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hp1 : ¬ p ∣ Nat.card K - 1 := fun h1 => hpq (by
    rw [show Nat.card K ^ 2 - 1 = Nat.card K ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    exact h1.mul_left _)
  obtain ⟨u, hu, hupow⟩ := exists_pow_mem_ggAutomizer_of_innerModel hp
    TableBSymp.center_spProj_eq_bot (fun φ' hφ' _ => TableBSymp.sp_I_subset_inn hφ')
    (ggCenterPrime_sp hp hp2) ψ hψ hker hperf hA hAI hsc (k := Nat.card K)
    fun E hE _ _ => exists_conj_eq_pow_largeEvenProj hp hp2 hp1
      (fun P hc ho => exists_conj_eq_pow_card_statedSp P hc ho) hE
  exact hpq (dvd_sq_sub_one_of_natCast_sq_eq_one
    (natCast_sq_eq_one_of_pow_mem hp5 Λ M C V ι φ h α hM hC hpair hlin hgen hu hupow))

theorem not_dvd_sq_sub_one_of_not_dvd_pow_four_sub_one {p q : ℕ} (hpq : ¬ p ∣ q ^ 4 - 1) :
    ¬ p ∣ q ^ 2 - 1 := fun h => hpq (h.trans (by
  rw [show q ^ 4 - 1 = (q ^ 2) ^ 2 - 1 ^ 2 by rw [one_pow, ← pow_mul]]
  exact Nat.sub_dvd_pow_sub_pow _ _ _))

open LinearFrob FormFrob in
theorem ggTorusWNormSC_omegaPlus_frob {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card K ^ 4 - 1) :
    GGTorusWNormSC p (OrthRest.RPlus K m) (LargeEvenInnSet _) := by
  intro L _ _ ψ hψ hker hperf A hA hAI _ hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hpq2 := not_dvd_sq_sub_one_of_not_dvd_pow_four_sub_one hpq
  have hp1 : ¬ p ∣ Nat.card K - 1 := fun h1 => hpq2 (by
    rw [show Nat.card K ^ 2 - 1 = Nat.card K ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    exact h1.mul_left _)
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 hm
  obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) hm
  obtain ⟨u, hu, hupow⟩ := exists_pow_mem_ggAutomizer_of_innerModel hp hZ
    OrthRest.ggOutdiagPrime_inn hcp ψ hψ hker hperf hA hAI hsc (k := Nat.card K ^ 2)
    fun E hE _ _ => exists_conj_eq_pow_largeEvenProj hp hp2 hp1
      (fun P hc ho => exists_conj_eq_pow_card_sq_statedOmega _
        (CFSG.LieType.Universal.Spin.coe_quadPlus m K) hnd hT P hc ho) hE
  have hsq := natCast_sq_eq_one_of_pow_mem hp5 Λ M C V ι φ h α hM hC hpair hlin hgen hu hupow
  apply hpq
  rw [show Nat.card K ^ 4 = (Nat.card K ^ 2) ^ 2 by rw [← pow_mul]]
  exact dvd_sq_sub_one_of_natCast_sq_eq_one hsq

open LinearFrob FormFrob in
theorem ggTorusWNormSC_omegaMinus_frob {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    {b c : K} (hm : 3 ≤ m) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : ¬ p ∣ Nat.card K ^ 4 - 1) :
    GGTorusWNormSC p (OrthRest.RMinus K m b c) (LargeEvenInnSet _) := by
  intro L _ _ ψ hψ hker hperf A hA hAI _ hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hpq2 := not_dvd_sq_sub_one_of_not_dvd_pow_four_sub_one hpq
  have hp1 : ¬ p ∣ Nat.card K - 1 := fun h1 => hpq2 (by
    rw [show Nat.card K ^ 2 - 1 = Nat.card K ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    exact h1.mul_left _)
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 hm hbc
  obtain ⟨u, hu, hupow⟩ := exists_pow_mem_ggAutomizer_of_innerModel hp hZ
    OrthRest.ggOutdiagPrime_inn hcp ψ hψ hker hperf hA hAI hsc (k := Nat.card K ^ 2)
    fun E hE _ _ => exists_conj_eq_pow_largeEvenProj hp hp2 hp1
      (fun P hc ho => exists_conj_eq_pow_card_sq_statedOmega _ (TableBOrth.coe_qMinusForm m b c)
        (TableBOrth.nondegenerate_qMinusForm m hbc) ((OrthTorus.charSum_qMinusForm m hbc).2 hm)
        P hc ho) hE
  have hsq := natCast_sq_eq_one_of_pow_mem hp5 Λ M C V ι φ h α hM hC hpair hlin hgen hu hupow
  apply hpq
  rw [show Nat.card K ^ 4 = (Nat.card K ^ 2) ^ 2 by rw [← pow_mul]]
  exact dvd_sq_sub_one_of_natCast_sq_eq_one hsq

end Row

theorem largeEvenLabelAll_wnorm_sp_frob
    {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (ht : lab.tag = .B ∨ lab.tag = .C) (hr : 3 ≤ lab.rank)
    (hpq : ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  have hp5 := LinearFrob.five_le_of_not_dvd_four_pow_sub_one hp hp2 hpq
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hr hpq ⊢
  have : NeZero r := ⟨by omega⟩
  rcases ht with rfl | rfl <;>
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_sp_frob hp hp5 (by rwa [hK])

theorem largeEvenLabelAll_wnorm_orth_frob
    {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (ht : lab.tag = .D ∨ lab.tag = .twD) (hr : 4 ≤ lab.rank)
    (hpq : ¬ p ∣ (2 ^ lab.n) ^ 4 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  have hp5 := LinearFrob.five_le_of_not_dvd_four_pow_sub_one hp hp2
    (not_dvd_sq_sub_one_of_not_dvd_pow_four_sub_one hpq)
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hr hpq ⊢
  rcases ht with rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (by omega)] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_omegaPlus_frob (by omega) hp hp5 (by rwa [hK])
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, b, c, hbc, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, b, c, hbc, hQ, ?_⟩
    exact ggTorusWNormSC_omegaMinus_frob (m := r - 1) (by omega) hbc hp hp5 (by rwa [hK])

end CFSG.StandardType
