module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestFrame
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvQV
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvariant
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestCenter
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestLevi
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestLeviInv
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs

open scoped commutatorElement

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private def e6pa_A {G : Type*} [Group G] (T V Z : Subgroup G)
    (hZcent : Z ≤ Subgroup.centralizer (V : Set G)) : Subgroup G where
  carrier := {x | x ∈ V ∧ ∀ t ∈ T, ⁅t, x⁆ ∈ Z}
  mul_mem' := by
    rintro x y ⟨hxV, hx⟩ ⟨hyV, hy⟩
    refine ⟨V.mul_mem hxV hyV, ?_⟩
    intro t htT
    have hxZ := hx t htT
    have hyZ := hy t htT
    have hc : x * ⁅t, y⁆ = ⁅t, y⁆ * x :=
      (Subgroup.mem_centralizer_iff.1 (hZcent hyZ)) x hxV
    have hconj : x * ⁅t, y⁆ * x⁻¹ = ⁅t, y⁆ := by
      rw [hc]; group
    have hkey : ⁅t, x * y⁆ = ⁅t, x⁆ * ⁅t, y⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      calc ⁅t, x⁆ * x * ⁅t, y⁆ * x⁻¹
          = ⁅t, x⁆ * (x * ⁅t, y⁆ * x⁻¹) := by group
        _ = ⁅t, x⁆ * ⁅t, y⁆ := by rw [hconj]
    rw [hkey]
    exact Z.mul_mem hxZ hyZ
  one_mem' := by
    refine ⟨V.one_mem, ?_⟩
    intro t _
    have h1 : ⁅t, (1 : G)⁆ = 1 := by rw [commutatorElement_def]; group
    rw [h1]
    exact Z.one_mem
  inv_mem' := by
    rintro x ⟨hxV, hx⟩
    refine ⟨V.inv_mem hxV, ?_⟩
    intro t htT
    have hxZ := hx t htT
    have hc : x⁻¹ * ⁅t, x⁆⁻¹ = ⁅t, x⁆⁻¹ * x⁻¹ :=
      (Subgroup.mem_centralizer_iff.1 (hZcent (Z.inv_mem hxZ))) x⁻¹ (V.inv_mem hxV)
    have hconj : x⁻¹ * ⁅t, x⁆⁻¹ * x = ⁅t, x⁆⁻¹ := by
      rw [hc]; group
    have hkey : ⁅t, x⁻¹⁆ = x⁻¹ * ⁅t, x⁆⁻¹ * x := by
      conv_lhs => rw [commutatorElement_def]
      conv_rhs => rw [commutatorElement_inv, commutatorElement_def]
      group
    rw [hkey, hconj]
    exact Z.inv_mem hxZ

private lemma e6pa_mem_A {G : Type*} [Group G] {T V Z : Subgroup G}
    (hZcent : Z ≤ Subgroup.centralizer (V : Set G)) {x : G} :
    x ∈ e6pa_A T V Z hZcent ↔ x ∈ V ∧ ∀ t ∈ T, ⁅t, x⁆ ∈ Z :=
  Iff.rfl

private lemma e6pa_le_A {G : Type*} [Group G] (T V Z : Subgroup G)
    (hZcent : Z ≤ Subgroup.centralizer (V : Set G))
    (hZV : Z ≤ V) (hTZ : ∀ t ∈ T, ∀ z : G, z ∈ Z → t * z * t⁻¹ ∈ Z) :
    Z ≤ e6pa_A T V Z hZcent := by
  intro z hz
  refine ⟨hZV hz, ?_⟩
  intro t htT
  have h1 : t * z * t⁻¹ ∈ Z := hTZ t htT z hz
  rw [show ⁅t, z⁆ = (t * z * t⁻¹) * z⁻¹ from by rw [commutatorElement_def]]
  exact Z.mul_mem h1 (Z.inv_mem hz)

private lemma e6pa_conj_mem_A {G : Type*} [Group G] (T N V Z : Subgroup G)
    (hZcent : Z ≤ Subgroup.centralizer (V : Set G))
    (hTV : N ≤ Subgroup.normalizer (V : Set G))
    (hTn : ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T)
    (hNZ : ∀ n ∈ N, ∀ z : G, z ∈ Z → n * z * n⁻¹ ∈ Z)
    {n : G} (hn : n ∈ N) {x : G} (hx : x ∈ e6pa_A T V Z hZcent) :
    n * x * n⁻¹ ∈ e6pa_A T V Z hZcent := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hTV hn) x).1 hx.1, ?_⟩
  intro t htT
  have hninv : n⁻¹ * t * n ∈ T := by
    have := hTn n⁻¹ (N.inv_mem hn) t htT
    simpa using this
  have hcomm : ⁅n⁻¹ * t * n, x⁆ ∈ Z := hx.2 (n⁻¹ * t * n) hninv
  have hconj : n * ⁅n⁻¹ * t * n, x⁆ * n⁻¹ = ⁅t, n * x * n⁻¹⁆ := by
    rw [conjugate_commutatorElement]
    have h1 : n * (n⁻¹ * t * n) * n⁻¹ = t := by group
    rw [h1]
  rw [← hconj]
  exact hNZ n hn _ hcomm

private lemma e6pa_le_normalizer_A {G : Type*} [Group G] (T N V Z : Subgroup G)
    (hZcent : Z ≤ Subgroup.centralizer (V : Set G))
    (hTV : N ≤ Subgroup.normalizer (V : Set G))
    (hTn : ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T)
    (hNZ : ∀ n ∈ N, ∀ z : G, z ∈ Z → n * z * n⁻¹ ∈ Z) :
    N ≤ Subgroup.normalizer (e6pa_A T V Z hZcent : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact e6pa_conj_mem_A T N V Z hZcent hTV hTn hNZ hn hx
  · intro hx
    have hninv : n⁻¹ ∈ N := N.inv_mem hn
    have h := e6pa_conj_mem_A T N V Z hZcent hTV hTn hNZ hninv hx
    have hx' : n⁻¹ * (n * x * n⁻¹) * (n⁻¹)⁻¹ = x := by group
    rwa [hx'] at h

private lemma e6pa_exists_fixed {G : Type*} [Group G] (T V Z : Subgroup G)
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTZ : ∀ t ∈ T, ∀ z : G, z ∈ Z ↔ t * z * t⁻¹ ∈ Z)
    (hZV : Z ≤ V) (hZnorm : (Z.subgroupOf V).Normal) [Finite V]
    (hVp : IsPGroup 2 V) (hTp : IsPGroup 2 T) (hZlt : Z < V) :
    ∃ v ∈ V, v ∉ Z ∧ ∀ t ∈ T, ⁅t, v⁆ ∈ Z := by
  classical
  letI : Subgroup.Normalizes T V := ⟨hTV⟩
  let K : Subgroup ↥V := Z.subgroupOf V
  haveI : K.Normal := hZnorm
  have hInv : CFSG.IsInvariant ↥T ↥V K := by
    refine ⟨?_⟩
    intro a x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    exact hTZ (a : G) a.2 (x : G)
  letI : MulDistribMulAction ↥T (↥V ⧸ K) := quotientMulDistribMulAction K hInv
  have hquotp : IsPGroup 2 (↥V ⧸ K) := hVp.to_quotient K
  have hcard_ne : Nat.card (↥V ⧸ K) ≠ 1 := by
    intro h1
    have hsub : Subsingleton (↥V ⧸ K) :=
      Finite.card_le_one_iff_subsingleton.mp (le_of_eq h1)
    have hvVZ : ∃ v, v ∈ V ∧ v ∉ Z := by
      by_contra h
      push Not at h
      exact hZlt.2 h
    obtain ⟨v, hvV, hvZ⟩ := hvVZ
    have hthis : (QuotientGroup.mk' K ⟨v, hvV⟩ : ↥V ⧸ K) = 1 := Subsingleton.elim _ _
    exact hvZ (Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := K) ⟨v, hvV⟩).1 hthis))
  have hdvd : 2 ∣ Nat.card (↥V ⧸ K) := by
    rcases hquotp.card_eq_or_dvd with h | h
    · exact absurd h hcard_ne
    · exact h
  obtain ⟨b, hbfix, hbne⟩ :=
    hTp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥V ⧸ K) hdvd
      (a := 1) (by rw [MulAction.mem_fixedPoints]; intro t; exact MulDistribMulAction.smul_one t)
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective K b
  rw [MulAction.mem_fixedPoints] at hbfix
  have hvnotK : v ∉ K := by
    intro hvK
    exact hbne ((QuotientGroup.eq_one_iff (N := K) v).2 hvK).symm
  refine ⟨(v : G), v.2, ?_, ?_⟩
  · intro hvZ
    exact hvnotK (Subgroup.mem_subgroupOf.2 hvZ)
  · intro t htT
    have hfix := hbfix (⟨t, htT⟩ : ↥T)
    have h2 : (((⟨t, htT⟩ : ↥T) • v) / v) ∈ K := by
      refine (QuotientGroup.eq_iff_div_mem (N := K)).1 ?_
      rw [← MulAction.Quotient.smul_coe (H := K) (⟨t, htT⟩ : ↥T) v]
      exact hfix
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : ((↑(((⟨t, htT⟩ : ↥T) • v) / v) : G)) =
        t * (v : G) * t⁻¹ * (v : G)⁻¹ := by
      simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    rw [h3] at h2
    simpa [commutatorElement_def, mul_assoc] using h2

private lemma e6pa_conj_mem_z0E_forward
    {n z : EC} (hn : n ∈ Subgroup.normalizer (qE : Set EC)) (hz : z ∈ z0E) :
    n * z * n⁻¹ ∈ z0E := by
  rw [← center_qE] at hz ⊢
  obtain ⟨y, hycent, hyeq⟩ := Subgroup.mem_map.1 hz
  have hy'n : n * (y : EC) * n⁻¹ ∈ qE :=
    (Subgroup.mem_normalizer_iff.mp hn (y : EC)).1 y.2
  let y' : ↥qE := ⟨n * (y : EC) * n⁻¹, hy'n⟩
  have hy'cent : y' ∈ Subgroup.center ↥qE := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hwinv : n⁻¹ * (w : EC) * n ∈ qE :=
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (qE : Set EC)).inv_mem hn) (w : EC)).1 w.2
    have hc := Subgroup.mem_center_iff.1 hycent ⟨n⁻¹ * (w : EC) * n, hwinv⟩
    have hc' : (n⁻¹ * (w : EC) * n) * (y : EC) = (y : EC) * (n⁻¹ * (w : EC) * n) :=
      congrArg Subtype.val hc
    show (w : EC) * (n * (y : EC) * n⁻¹) = (n * (y : EC) * n⁻¹) * (w : EC)
    calc (w : EC) * (n * (y : EC) * n⁻¹)
        = n * ((n⁻¹ * (w : EC) * n) * (y : EC)) * n⁻¹ := by group
      _ = n * ((y : EC) * (n⁻¹ * (w : EC) * n)) * n⁻¹ := by rw [hc']
      _ = (n * (y : EC) * n⁻¹) * (w : EC) := by group
  refine Subgroup.mem_map.2 ⟨y', hy'cent, ?_⟩
  show (y' : EC) = n * z * n⁻¹
  rw [← hyeq]
  rfl

private lemma e6pa_conj_mem_z0E_iff
    {n : EC} (hn : n ∈ Subgroup.normalizer (qE : Set EC)) (z : EC) :
    z ∈ z0E ↔ n * z * n⁻¹ ∈ z0E := by
  constructor
  · intro hz
    exact e6pa_conj_mem_z0E_forward hn hz
  · intro hz
    have hninv : n⁻¹ ∈ Subgroup.normalizer (qE : Set EC) :=
      (Subgroup.normalizer (qE : Set EC)).inv_mem hn
    have h := e6pa_conj_mem_z0E_forward hninv hz
    simpa [mul_assoc] using h

private lemma e6pa_mu1_mem :
    ∀ β ∈ mu1List.toFinset, β ∈ rootFinset Tag.E6 ∧ iform β lamE = 1 := by
  decide +kernel

private lemma e6pa_mu2_mem :
    ∀ β ∈ mu2List.toFinset, β ∈ rootFinset Tag.E6 ∧ iform β lamE = 1 := by
  decide +kernel

private lemma e6pa_mu1_subset_qRoots :
    {β : Fin Tag.E6.rank → ℤ | β ∈ mu1List} ⊆ qRoots := by
  intro β hβ
  have h := e6pa_mu1_mem β (List.mem_toFinset.2 hβ)
  exact ⟨mem_rootFinset.1 h.1, by rw [h.2]; norm_num⟩

private lemma e6pa_mu2_subset_qRoots :
    {β : Fin Tag.E6.rank → ℤ | β ∈ mu2List} ⊆ qRoots := by
  intro β hβ
  have h := e6pa_mu2_mem β (List.mem_toFinset.2 hβ)
  exact ⟨mem_rootFinset.1 h.1, by rw [h.2]; norm_num⟩

private lemma e6pa_uMu1_le_qE :
    uMu1 ≤ qE := by
  intro x hx
  simp only [uMu1, qE, Subgroup.mem_subgroupOf] at hx ⊢
  exact rootSpan_mono e6pa_mu1_subset_qRoots hx

private lemma e6pa_uMu2_le_qE :
    uMu2 ≤ qE := by
  intro x hx
  simp only [uMu2, qE, Subgroup.mem_subgroupOf] at hx ⊢
  exact rootSpan_mono e6pa_mu2_subset_qRoots hx

private lemma e6pa_l1Root_not_mem_z0E
    {c : ↥qE →* Multiplicative e6TwoRestQV} (hc : IsQCoord c) (i : Fin 16) :
    xr (l1Root i) ∉ z0E := by
  intro hz
  have hmem : c ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ = 1 := by
    rw [← MonoidHom.mem_ker]
    rw [hc.2.1, Subgroup.mem_subgroupOf]
    exact hz
  have hval := hc.2.2 i
  rw [hmem] at hval
  have hzero : (Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2)) = 0 := by
    have := congrArg Multiplicative.toAdd hval
    simpa using this.symm
  have h1 : (1 : ZMod 2) = 0 := by
    have := congrFun hzero i
    rw [Pi.single_eq_same] at this
    simpa using this
  exact one_ne_zero h1

private lemma e6pa_l1Root_not_mem_ZU1
    {c : ↥qE →* Multiplicative e6TwoRestQV} (hc : IsQCoord c) (i : Fin 16)
    (hi : 8 ≤ (i : ℕ)) :
    xr (l1Root i) ∉ (z0E ⊔ uMu1 : Subgroup EC) := by
  intro hmem
  have hnot : Multiplicative.toAdd (c ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩) ∉ invU1 := by
    intro hmem1
    have hzero := hmem1 i hi
    rw [hc.2.2 i, toAdd_ofAdd, Pi.single_eq_same] at hzero
    exact one_ne_zero hzero
  exact hnot ((qcoord_mem_U1_iff hc ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩).2 (by
    simpa using hmem))

private lemma e6pa_l1Root_not_mem_ZU2
    {c : ↥qE →* Multiplicative e6TwoRestQV} (hc : IsQCoord c) (i : Fin 16)
    (hi : (i : ℕ) < 8) :
    xr (l1Root i) ∉ (z0E ⊔ uMu2 : Subgroup EC) := by
  intro hmem
  have hnot : Multiplicative.toAdd (c ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩) ∉ invU2 := by
    intro hmem1
    have hzero := hmem1 i hi
    rw [hc.2.2 i, toAdd_ofAdd, Pi.single_eq_same] at hzero
    exact one_ne_zero hzero
  exact hnot ((qcoord_mem_U2_iff hc ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩).2 (by
    simpa using hmem))


theorem commutator_le_z0E_of_pCore
    {T : Subgroup EC} (hT : IsPGroup 2 T) (hTR : T ≤ Subgroup.normalizer (rE : Set EC))
    (hTn : ∀ n ∈ Subgroup.normalizer (rE : Set EC), ∀ t ∈ T, n * t * n⁻¹ ∈ T) :
    ∀ t ∈ T, ∀ q ∈ qE, ⁅t, q⁆ ∈ z0E := by
  classical
  let N : Subgroup EC := Subgroup.normalizer (rE : Set EC)
  obtain ⟨c, hc⟩ := exists_qcoord
  have hTQ : T ≤ Subgroup.normalizer (qE : Set EC) := hTR.trans normalizer_rE_le_normalizer_qE
  have hTZf : ∀ t ∈ T, ∀ z : EC, z ∈ z0E → t * z * t⁻¹ ∈ z0E := by
    intro t htT z hz
    exact (e6pa_conj_mem_z0E_iff (hTQ htT) z).1 hz
  have hTZi : ∀ t ∈ T, ∀ z : EC, z ∈ z0E ↔ t * z * t⁻¹ ∈ z0E := by
    intro t htT z
    exact e6pa_conj_mem_z0E_iff (hTQ htT) z
  have hNZ : ∀ n ∈ N, ∀ z : EC, z ∈ z0E → n * z * n⁻¹ ∈ z0E := by
    intro n hn z hz
    exact (e6pa_conj_mem_z0E_iff (normalizer_rE_le_normalizer_qE hn) z).1 hz
  have hZU1qE : (z0E ⊔ uMu1 : Subgroup EC) ≤ qE := sup_le z0E_le_qE e6pa_uMu1_le_qE
  have hZU2qE : (z0E ⊔ uMu2 : Subgroup EC) ≤ qE := sup_le z0E_le_qE e6pa_uMu2_le_qE
  have hZcentQ : z0E ≤ Subgroup.centralizer (qE : Set EC) := z0E_central
  have hZcent1 : z0E ≤ Subgroup.centralizer ((z0E ⊔ uMu1 : Subgroup EC) : Set EC) :=
    z0E_central.trans (Subgroup.centralizer_le hZU1qE)
  have hZcent2 : z0E ≤ Subgroup.centralizer ((z0E ⊔ uMu2 : Subgroup EC) : Set EC) :=
    z0E_central.trans (Subgroup.centralizer_le hZU2qE)
  have hNRV1 : N ≤ Subgroup.normalizer ((z0E ⊔ uMu1 : Subgroup EC) : Set EC) :=
    normalizer_rE_le_normalizer_qE.trans normalizer_qE_le_normalizer_z0E_sup_uMu1
  have hNRV2 : N ≤ Subgroup.normalizer ((z0E ⊔ uMu2 : Subgroup EC) : Set EC) :=
    normalizer_rE_le_normalizer_qE.trans normalizer_qE_le_normalizer_z0E_sup_uMu2
  have hTV1 : T ≤ Subgroup.normalizer ((z0E ⊔ uMu1 : Subgroup EC) : Set EC) := hTR.trans hNRV1
  have hTV2 : T ≤ Subgroup.normalizer ((z0E ⊔ uMu2 : Subgroup EC) : Set EC) := hTR.trans hNRV2
  have hV1p : IsPGroup 2 (z0E ⊔ uMu1 : Subgroup EC) := qE_isPGroup.to_le hZU1qE
  have hV2p : IsPGroup 2 (z0E ⊔ uMu2 : Subgroup EC) := qE_isPGroup.to_le hZU2qE
  have hZnormV1 : (z0E.subgroupOf (z0E ⊔ uMu1 : Subgroup EC)).Normal := by
    apply Subgroup.normal_of_le_center
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (hZcent1 (Subgroup.mem_subgroupOf.1 hx)) (y : EC) y.2
  have hZnormV2 : (z0E.subgroupOf (z0E ⊔ uMu2 : Subgroup EC)).Normal := by
    apply Subgroup.normal_of_le_center
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (hZcent2 (Subgroup.mem_subgroupOf.1 hx)) (y : EC) y.2
  have hZltV1 : z0E < (z0E ⊔ uMu1 : Subgroup EC) := by
    refine lt_of_le_of_ne (by intro x hx; exact Subgroup.mem_sup_left hx) ?_
    intro hEq
    have hxr : xr (l1Root 0) ∈ (z0E ⊔ uMu1 : Subgroup EC) :=
      Subgroup.mem_sup_right (xr_l1Root_mem_uMu1 0 (by norm_num))
    rw [← hEq] at hxr
    exact e6pa_l1Root_not_mem_z0E hc 0 hxr
  have hZltV2 : z0E < (z0E ⊔ uMu2 : Subgroup EC) := by
    have hle : z0E ≤ (z0E ⊔ uMu2 : Subgroup EC) := by
      intro x hx; exact Subgroup.mem_sup_left hx
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hxr : xr (l1Root 8) ∈ (z0E ⊔ uMu2 : Subgroup EC) :=
      Subgroup.mem_sup_right (xr_l1Root_mem_uMu2 8 (by norm_num))
    rw [← hEq] at hxr
    exact e6pa_l1Root_not_mem_z0E hc 8 hxr
  let Aq : Subgroup EC := e6pa_A T qE z0E hZcentQ
  let A1 : Subgroup EC := e6pa_A T (z0E ⊔ uMu1) z0E hZcent1
  let A2 : Subgroup EC := e6pa_A T (z0E ⊔ uMu2) z0E hZcent2
  have hAq_le : Aq ≤ qE := fun _ hx => hx.1
  have hA1_le : A1 ≤ z0E ⊔ uMu1 := fun _ hx => hx.1
  have hA2_le : A2 ≤ z0E ⊔ uMu2 := fun _ hx => hx.1
  have hZ_le_Aq : z0E ≤ Aq := e6pa_le_A T qE z0E hZcentQ z0E_le_qE hTZf
  have hZ_le_A1 : z0E ≤ A1 := e6pa_le_A T (z0E ⊔ uMu1) z0E hZcent1 (by intro x hx; exact Subgroup.mem_sup_left hx) hTZf
  have hZ_le_A2 : z0E ≤ A2 := e6pa_le_A T (z0E ⊔ uMu2) z0E hZcent2 (by intro x hx; exact Subgroup.mem_sup_left hx) hTZf
  have hA1_le_qE : A1 ≤ qE := hA1_le.trans hZU1qE
  have hA2_le_qE : A2 ≤ qE := hA2_le.trans hZU2qE
  have hNR_Aq : N ≤ Subgroup.normalizer (Aq : Set EC) :=
    e6pa_le_normalizer_A T N qE z0E hZcentQ normalizer_rE_le_normalizer_qE hTn hNZ
  have hNR_A1 : N ≤ Subgroup.normalizer (A1 : Set EC) :=
    e6pa_le_normalizer_A T N (z0E ⊔ uMu1) z0E hZcent1 hNRV1 hTn hNZ
  have hNR_A2 : N ≤ Subgroup.normalizer (A2 : Set EC) :=
    e6pa_le_normalizer_A T N (z0E ⊔ uMu2) z0E hZcent2 hNRV2 hTn hNZ
  have hZ_lt_A1 : z0E < A1 := by
    obtain ⟨v, hvV, hvZ, hvcomm⟩ :=
      e6pa_exists_fixed T (z0E ⊔ uMu1) z0E hTV1 hTZi (by intro x hx; exact Subgroup.mem_sup_left hx) hZnormV1 hV1p hT hZltV1
    refine lt_of_le_of_ne hZ_le_A1 ?_
    intro hEq
    have hvA1 : v ∈ A1 := (e6pa_mem_A hZcent1).mpr ⟨hvV, hvcomm⟩
    rw [← hEq] at hvA1
    exact hvZ hvA1
  have hZ_lt_A2 : z0E < A2 := by
    obtain ⟨v, hvV, hvZ, hvcomm⟩ :=
      e6pa_exists_fixed T (z0E ⊔ uMu2) z0E hTV2 hTZi (by intro x hx; exact Subgroup.mem_sup_left hx) hZnormV2 hV2p hT hZltV2
    refine lt_of_le_of_ne hZ_le_A2 ?_
    intro hEq
    have hvA2 : v ∈ A2 := (e6pa_mem_A hZcent2).mpr ⟨hvV, hvcomm⟩
    rw [← hEq] at hvA2
    exact hvZ hvA2
  have hA1_eq : A1 = z0E ⊔ uMu1 := by
    rcases invariant_between_z0E_qE A1 hZ_le_A1 hA1_le_qE hNR_A1 with h | h | h | h
    · exact absurd h.le hZ_lt_A1.2
    · exfalso
      have hxr : xr (l1Root 8) ∈ A1 := by rw [h]; exact xr_l1Root_mem_qE 8
      exact e6pa_l1Root_not_mem_ZU1 hc 8 (by norm_num) (hA1_le hxr)
    · exact h
    · exfalso
      have hxr : xr (l1Root 8) ∈ A1 := by
        rw [h]
        exact Subgroup.mem_sup_right (xr_l1Root_mem_uMu2 8 (by norm_num))
      exact e6pa_l1Root_not_mem_ZU1 hc 8 (by norm_num) (hA1_le hxr)
  have hA2_eq : A2 = z0E ⊔ uMu2 := by
    rcases invariant_between_z0E_qE A2 hZ_le_A2 hA2_le_qE hNR_A2 with h | h | h | h
    · exact absurd h.le hZ_lt_A2.2
    · exfalso
      have hxr : xr (l1Root 0) ∈ A2 := by rw [h]; exact xr_l1Root_mem_qE 0
      exact e6pa_l1Root_not_mem_ZU2 hc 0 (by norm_num) (hA2_le hxr)
    · exfalso
      have hxr : xr (l1Root 0) ∈ A2 := by
        rw [h]
        exact Subgroup.mem_sup_right (xr_l1Root_mem_uMu1 0 (by norm_num))
      exact e6pa_l1Root_not_mem_ZU2 hc 0 (by norm_num) (hA2_le hxr)
    · exact h
  have hA1_le_Aq : A1 ≤ Aq := by
    intro x hx
    exact (e6pa_mem_A hZcentQ).mpr ⟨hA1_le_qE hx, hx.2⟩
  have hA2_le_Aq : A2 ≤ Aq := by
    intro x hx
    exact (e6pa_mem_A hZcentQ).mpr ⟨hA2_le_qE hx, hx.2⟩
  have hV1_le_Aq : (z0E ⊔ uMu1 : Subgroup EC) ≤ Aq := by
    rw [← hA1_eq]; exact hA1_le_Aq
  have hV2_le_Aq : (z0E ⊔ uMu2 : Subgroup EC) ≤ Aq := by
    rw [← hA2_eq]; exact hA2_le_Aq
  have hAq_eq : Aq = qE := by
    rcases invariant_between_z0E_qE Aq hZ_le_Aq hAq_le hNR_Aq with h | h | h | h
    · exfalso
      have hxr : xr (l1Root 0) ∈ Aq :=
        hV1_le_Aq (Subgroup.mem_sup_right (xr_l1Root_mem_uMu1 0 (by norm_num)))
      rw [h] at hxr
      exact e6pa_l1Root_not_mem_z0E hc 0 hxr
    · exact h
    · exfalso
      have hxr : xr (l1Root 8) ∈ Aq :=
        hV2_le_Aq (Subgroup.mem_sup_right (xr_l1Root_mem_uMu2 8 (by norm_num)))
      rw [h] at hxr
      exact e6pa_l1Root_not_mem_ZU1 hc 8 (by norm_num) hxr
    · exfalso
      have hxr : xr (l1Root 0) ∈ Aq :=
        hV1_le_Aq (Subgroup.mem_sup_right (xr_l1Root_mem_uMu1 0 (by norm_num)))
      rw [h] at hxr
      exact e6pa_l1Root_not_mem_ZU2 hc 0 (by norm_num) hxr
  intro t htT q hq
  have hqA : q ∈ Aq := by rw [hAq_eq]; exact hq
  exact ((e6pa_mem_A hZcentQ).mp hqA).2 t htT

end CFSG.StandardType.GGSixE6Two

end
