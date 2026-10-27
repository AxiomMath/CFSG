module

public import CFSG.LinearAlgebra.FrobeniusIsometryEigen
public import CFSG.LocalAnalysis.StandardType.GGTBWNormCartanEigen
public import CFSG.LocalAnalysis.StandardType.GGTBWNormFormFrob
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly

namespace OrthPhiFour

theorem exists_eigen_largeEvenProj {K : Type} [Field K] [Finite K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] {H : Subgroup (GL ι K)} {p k : ℕ} (hp : p.Prime)
    (hp1 : ¬ p ∣ Nat.card K - 1)
    (hH : ∀ P : Subgroup H, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x ^ p = 1) →
      (∀ c : H, (∀ x ∈ P, c * x = x * c) → c ^ p = 1 → c ∈ P) → p ^ 2 ≤ Nat.card P →
      ∃ g : H, (∀ x ∈ P, g * x * g⁻¹ ∈ P) ∧ (∀ x ∈ P, g * x * g⁻¹ = x → x = 1) ∧
        (∃ x ∈ P, x ≠ 1 ∧ g * x * g⁻¹ = x ^ k) ∧ ∀ x ∈ P, (g * x * g⁻¹) ^ k = x → x = 1)
    {E : Subgroup (LargeEvenProj H)} (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E)
    (hEsc : ∀ g : LargeEvenProj H, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ z : LargeEvenProj H, (∀ x ∈ E, z * x * z⁻¹ ∈ E) ∧ (∀ x ∈ E, z * x * z⁻¹ = x → x = 1) ∧
      (∃ x ∈ E, x ≠ 1 ∧ z * x * z⁻¹ = x ^ k) ∧ ∀ x ∈ E, (z * x * z⁻¹) ^ k = x → x = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hker := LinearFrob.not_dvd_card_ker_largeEvenProjMk (H := H) hp hp1
  obtain ⟨P, -, -, hPmap, hPker⟩ := CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker
    (LargeEvenProjMk H) (QuotientGroup.mk'_surjective _) hker
    (TableB.isPGroup_of_isElemAbelian hE)
  set π := LargeEvenProjMk H
  have hinj : ∀ x ∈ P, π x = 1 → x = 1 := fun x hx h1 => by
    have hx' : x ∈ P ⊓ π.ker := ⟨hx, h1⟩
    rw [hPker] at hx'
    exact hx'
  have hinj2 : ∀ x ∈ P, ∀ y ∈ P, π x = π y → x = y := fun x hx y hy h =>
    mul_inv_eq_one.mp (hinj _ (P.mul_mem hx (P.inv_mem hy)) (by rw [map_mul, map_inv, h,
      mul_inv_cancel]))
  have hmemE : ∀ x ∈ P, π x ∈ E := fun x hx => hPmap ▸ ⟨x, hx, rfl⟩
  have hsurjE : ∀ y ∈ E, ∃ x ∈ P, π x = y := fun y hy => by
    rw [← hPmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    hinj2 _ (P.mul_mem hx hy) _ (P.mul_mem hy hx) (by
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hE (hmemE x hx) (hmemE y hy))
  have hPexp : ∀ x ∈ P, x ^ p = 1 := fun x hx =>
    hinj _ (P.pow_mem hx p) (by rw [map_pow]; exact hE.2 _ (hmemE x hx))
  have hPsc : ∀ c : H, (∀ x ∈ P, c * x = x * c) → c ^ p = 1 → c ∈ P := by
    intro c hc hcp
    obtain ⟨s, hs, hsc⟩ := hsurjE (π c) (hEsc (π c) (fun e he => by
      obtain ⟨x, hx, rfl⟩ := hsurjE e he
      rw [← map_mul, ← map_mul, hc x hx]) (by rw [← map_pow, hcp, map_one]))
    have hcs : c * s⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsc, mul_inv_cancel]
    have hcsp : (c * s⁻¹) ^ p = 1 := by
      rw [(Commute.inv_right (hc s hs : Commute c s)).mul_pow, inv_pow, hcp, hPexp s hs,
        inv_one, one_mul]
    have h1 : c * s⁻¹ = 1 := by
      have hdvd := orderOf_dvd_of_pow_eq_one hcsp
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        apply hker
        have hk : orderOf (⟨c * s⁻¹, hcs⟩ : π.ker) = p := by
          rw [Subgroup.orderOf_mk, h]
        rw [← hk]
        exact orderOf_dvd_natCard _
    rw [mul_inv_eq_one] at h1
    rw [h1]
    exact hs
  have hPcard : p ^ 2 ≤ Nat.card P := by
    have h1 : Nat.card E = Nat.card P := by
      rw [← hPmap]
      change Nat.card ((P.map π : Set (LargeEvenProj H))) = Nat.card (P : Set H)
      rw [Subgroup.coe_map]
      exact Nat.card_image_of_injOn fun x hx y hy h => hinj2 x hx y hy h
    rwa [← h1]
  obtain ⟨g, hgN, hgfix, ⟨x₀, hx₀, hx₀1, hx₀k⟩, hginv⟩ := hH P hPcomm hPexp hPsc hPcard
  refine ⟨π g, fun x hx => ?_, fun x hx hxe => ?_, ⟨π x₀, hmemE x₀ hx₀, fun h1 =>
    hx₀1 (hinj x₀ hx₀ h1), by rw [← map_inv, ← map_mul, ← map_mul, hx₀k, map_pow]⟩,
    fun x hx hxe => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := hsurjE x hx
    rw [← map_inv, ← map_mul, ← map_mul]
    exact hmemE _ (hgN s hs)
  · obtain ⟨s, hs, rfl⟩ := hsurjE x hx
    rw [← map_inv, ← map_mul, ← map_mul] at hxe
    rw [hgfix s hs (hinj2 _ (hgN s hs) _ hs hxe), map_one]
  · obtain ⟨s, hs, rfl⟩ := hsurjE x hx
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow] at hxe
    rw [hginv s hs (hinj2 _ (P.pow_mem (hgN s hs) k) _ hs hxe), map_one]

open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions in
theorem exists_eigen_statedOmega {K : Type} [Field K] [Finite K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] (QF : QuadraticForm K (ι → K)) {Q₀ : (ι → K) → K}
    (hQ : ⇑QF = Q₀) (hnd : (QuadraticMap.polarBilin QF).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, QF x = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : ¬ p ∣ Nat.card K ^ 2 - 1)
    (hq3 : ¬ p ∣ Nat.card K ^ 3 - 1) (P : Subgroup (StatedOmega Q₀))
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hexp : ∀ x ∈ P, x ^ p = 1)
    (hsc : ∀ c : StatedOmega Q₀, (∀ x ∈ P, c * x = x * c) → c ^ p = 1 → c ∈ P)
    (hcard : p ^ 2 ≤ Nat.card P) :
    ∃ g : StatedOmega Q₀, (∀ x ∈ P, g * x * g⁻¹ ∈ P) ∧ (∀ x ∈ P, g * x * g⁻¹ = x → x = 1) ∧
      (∃ x ∈ P, x ≠ 1 ∧ g * x * g⁻¹ = x ^ Nat.card K) ∧
      ∀ x ∈ P, (g * x * g⁻¹) ^ Nat.card K = x → x = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let φ : StatedOmega Q₀ →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (toLinEquiv ι K).toMonoidHom.comp (StatedOmega Q₀).subtype
  have hφinj : Function.Injective φ := (toLinEquiv ι K).injective.comp Subtype.val_injective
  set O := TauCeti.QuadraticMap.orthogonalGroup QF
  have hOO : ⁅O, O⁆ ≤ O :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hmemD : ∀ x : GL ι K, x ∈ StatedOmega Q₀ ↔ toLinEquiv ι K x ∈ ⁅O, O⁆ := fun x => by
    rw [statedOmega_eq_comap hQ, Subgroup.mem_comap]
    rfl
  have hφD : ∀ s, φ s ∈ ⁅O, O⁆ := fun s => (hmemD s).mp s.2
  have hφsurj : ∀ d ∈ ⁅O, O⁆, ∃ s : StatedOmega Q₀, φ s = d := fun d hd =>
    ⟨⟨(toLinEquiv ι K).symm d, (hmemD _).mpr (by rwa [MulEquiv.apply_symm_apply])⟩,
      (toLinEquiv ι K).apply_symm_apply d⟩
  obtain ⟨-, -, -, -, -, hsq, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  have : Nontrivial (ι → K) := by
    obtain ⟨T, hT3, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hT3 ▸ Submodule.finrank_le T))
  have hΩ : ⁅O, O⁆ = omegaGroup QF hnd :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hnd)
      (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hnd hT)
  have hidx : ((omegaGroup QF hnd).subgroupOf O).index = 2 := relIndex_omegaGroup QF hnd
  have hmul : ∀ g ∈ O, ∀ g' ∈ O, g ∉ ⁅O, O⁆ → g' ∉ ⁅O, O⁆ → g * g' ∈ ⁅O, O⁆ := by
    intro g hg g' hg' h1 h2
    rw [hΩ] at h1 h2 ⊢
    have h3 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨g, hg⟩) (b := ⟨g', hg'⟩)).mpr
      (iff_of_false (by rwa [Subgroup.mem_subgroupOf]) (by rwa [Subgroup.mem_subgroupOf]))
    rwa [Subgroup.mem_subgroupOf] at h3
  have : Finite P := Subtype.finite
  have hcard' : p ^ 2 ≤ Nat.card (P.map φ) := by
    rwa [Subgroup.card_map_of_injective hφinj]
  have hq2' : ¬ p ∣ Fintype.card K ^ 2 - 1 := by rwa [← Nat.card_eq_fintype_card]
  have hq3' : ¬ p ∣ Fintype.card K ^ 3 - 1 := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨y, hyD, hyN, hyfix, ⟨x', hx', hx'1, hx'q⟩, hyinv⟩ :=
    CFSG.LinearAlgebra.exists_eigen_normalizer QF hnd (G := ⁅O, O⁆) hOO hsq hmul hp hp2 hq2' hq3'
      (E := P.map φ) (by rintro _ ⟨s, -, rfl⟩; exact hφD s)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul, hcomm x hx y hy])
      (by
        rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hexp x hx, map_one])
      (by
        intro c hc hcE hcp
        obtain ⟨s, rfl⟩ := hφsurj c hc
        refine Subgroup.mem_map_of_mem φ (hsc s (fun x hx => hφinj ?_) (hφinj ?_))
        · rw [map_mul, map_mul]
          exact hcE _ (Subgroup.mem_map_of_mem φ hx)
        · rw [map_pow, hcp, map_one])
      hcard'
  obtain ⟨g, rfl⟩ := hφsurj y hyD
  obtain ⟨x₀, hx₀, rfl⟩ := hx'
  refine ⟨g, fun x hx => ?_, fun x hx hxe => ?_, ⟨x₀, hx₀, fun h1 => hx'1 (by rw [h1, map_one]),
    hφinj (by rw [map_mul, map_mul, map_inv, map_pow, hx'q, Nat.card_eq_fintype_card])⟩,
    fun x hx hxe => ?_⟩
  · have h := hyN (φ x) (Subgroup.mem_map_of_mem φ hx)
    rw [← map_inv, ← map_mul, ← map_mul] at h
    exact (Subgroup.mem_map_iff_mem hφinj).mp h
  · have h := hyfix (φ x) (Subgroup.mem_map_of_mem φ hx)
      (by rw [← map_inv, ← map_mul, ← map_mul, hxe])
    exact hφinj (by rw [h, map_one])
  · have h := hyinv (φ x) (Subgroup.mem_map_of_mem φ hx)
      (by rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, Nat.card_eq_fintype_card.symm, hxe])
    exact hφinj (by rw [h, map_one])

theorem not_dvd_cube_sub_one {p q : ℕ} (hq : 1 ≤ q) (h2 : ¬ p ∣ q ^ 2 - 1)
    (h4 : p ∣ q ^ 4 - 1) : ¬ p ∣ q ^ 3 - 1 := by
  have hc : ∀ k : ℕ, p ∣ q ^ k - 1 ↔ (q : ZMod p) ^ k = 1 := fun k => by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), sub_eq_zero,
      Nat.cast_pow, Nat.cast_one]
  rw [hc] at h2 h4 ⊢
  intro h3
  apply h2
  have h1 : (q : ZMod p) = 1 := by rw [← h4, pow_succ, h3, one_mul]
  rw [h1, one_pow]

end OrthPhiFour

section Row


open OrthPhiFour in
theorem ggTorusWNormSC_omegaPlus_phi4 {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hp5 : 5 ≤ p) (hq2 : ¬ p ∣ Nat.card K ^ 2 - 1)
    (hq3 : ¬ p ∣ Nat.card K ^ 3 - 1) :
    GGTorusWNormSC p (OrthRest.RPlus K m) (LargeEvenInnSet _) := by
  intro L _ _ ψ hψ hker hperf A hA hAI hA3 hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hp1 : ¬ p ∣ Nat.card K - 1 := fun h1 => hq2 (h1.trans (by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2))
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 hm
  obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) hm
  obtain ⟨u, hu, hufix, huev, huinv⟩ := exists_eigen_mem_ggAutomizer_of_innerModel hp hZ
    OrthRest.ggOutdiagPrime_inn hcp ψ hψ hker hperf hA hAI hsc (k := Nat.card K)
    fun E hE hEc hEsc => exists_eigen_largeEvenProj hp hp1
      (fun P hc hx hs hcard => exists_eigen_statedOmega _
        (CFSG.LieType.Universal.Spin.coe_quadPlus m K) hnd hT hp hp2 hq2 hq3 P hc hx hs hcard) hE
      (by rw [hEc]; exact (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hA3) hEsc
  exact false_of_eigen_mem_ggAutomizer hp5 Λ M C V ι φ h α hM hC hpair hlin hgen hu hufix huev
    huinv

open OrthPhiFour in
theorem ggTorusWNormSC_omegaMinus_phi4 {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    {b c : K} (hm : 3 ≤ m) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq2 : ¬ p ∣ Nat.card K ^ 2 - 1) (hq3 : ¬ p ∣ Nat.card K ^ 3 - 1) :
    GGTorusWNormSC p (OrthRest.RMinus K m b c) (LargeEvenInnSet _) := by
  intro L _ _ ψ hψ hker hperf A hA hAI hA3 hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hp1 : ¬ p ∣ Nat.card K - 1 := fun h1 => hq2 (h1.trans (by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2))
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 hm hbc
  obtain ⟨u, hu, hufix, huev, huinv⟩ := exists_eigen_mem_ggAutomizer_of_innerModel hp hZ
    OrthRest.ggOutdiagPrime_inn hcp ψ hψ hker hperf hA hAI hsc (k := Nat.card K)
    fun E hE hEc hEsc => exists_eigen_largeEvenProj hp hp1
      (fun P hc hx hs hcard => exists_eigen_statedOmega _ (TableBOrth.coe_qMinusForm m b c)
        (TableBOrth.nondegenerate_qMinusForm m hbc) ((OrthTorus.charSum_qMinusForm m hbc).2 hm)
        hp hp2 hq2 hq3 P hc hx hs hcard) hE
      (by rw [hEc]; exact (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hA3) hEsc
  exact false_of_eigen_mem_ggAutomizer hp5 Λ M C V ι φ h α hM hC hpair hlin hgen hu hufix huev
    huinv

end Row

theorem largeEvenLabelAll_wnorm_orth_phi4
    {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (ht : lab.tag = .D ∨ lab.tag = .twD) (hr : 4 ≤ lab.rank)
    (hpq : ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  by_cases h4 : p ∣ (2 ^ lab.n) ^ 4 - 1
  swap
  · exact largeEvenLabelAll_wnorm_orth_frob hp hp2 ht hr h4
  have hp5 := LinearFrob.five_le_of_not_dvd_four_pow_sub_one hp hp2 hpq
  have h3 := OrthPhiFour.not_dvd_cube_sub_one (Nat.one_le_two_pow) hpq h4
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hr hpq h3 ⊢
  rcases ht with rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (by omega)] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_omegaPlus_phi4 (by omega) hp hp5 (by rwa [hK]) (by rwa [hK])
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, b, c, hbc, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, b, c, hbc, hQ, ?_⟩
    exact ggTorusWNormSC_omegaMinus_phi4 (m := r - 1) (by omega) hbc hp hp5 (by rwa [hK])
      (by rwa [hK])

end CFSG.StandardType
