module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs
public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.Timmesfeld.Transvection.ModelSURadical
import CFSG.RankThree.GF2n.Tim79aSUStatements
import CFSG.RankThree.GF2n.Tim79aRootSubgroupOf
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryPerpCount
import CFSG.Timmesfeld.Transvection.ModelSUCentre
import CFSG.Timmesfeld.Transvection.ModelSUCount
import CFSG.Timmesfeld.Transvection.ModelSURadCard
import CFSG.GroupTheory.PCore.SubgroupOfNormalizer
import CFSG.GroupTheory.SubgroupOfLattice
import CFSG.GroupTheory.ChiefFactors.RadicalCentralizer
public import CFSG.Timmesfeld.Transvection.AssembleRel

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG CFSG.Open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank
open scoped commutatorElement

theorem SUTrans.inSubgroup_pCore_normalizer_map_eq {K : Type} [Group K] {X : Subgroup K}
    {f m : ℕ} (hf : 1 ≤ f) (hm4 : 4 ≤ m)
    {Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) →* K}
    (hker : Φ.ker ≤ Subgroup.center _) (hrange : Φ.range = X)
    {v : Fin m → GaloisField 2 (2 * f)} (hv : v ≠ 0)
    (hvv : uForm (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) v v = 0)
    {Tv : Subgroup ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m)}
    (hTv : IsUTransGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) v Tv) :
    inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer ((Tv.map Φ : Subgroup K) : Set K)) =
      (uRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) v).map Φ := by
  have hF := CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution (GaloisField 2 (2 * f)) 2 f c = c →
      ∃ e, e + unitaryInvolution (GaloisField 2 (2 * f)) 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  have hmem : ∀ x, Φ x ∈ X := fun x => hrange.le (MonoidHom.mem_range.2 ⟨x, rfl⟩)
  have hΨ : Function.Surjective (Φ.codRestrict X hmem) := fun y => by
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hrange.ge y.2)
    exact ⟨x, Subtype.ext hx⟩
  have hkerΨ : (Φ.codRestrict X hmem).ker ≤ Subgroup.center _ := by
    rw [MonoidHom.ker_codRestrict]; exact hker
  have hPerp : SUPerpStmt (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m :=
    fun ha haa hvv' hav hva => exists_isotropic_perp_not_perp hσ htr ha haa hvv' hav hva
  have hcore := Tim79a.pCoreOf_normalizer_map_eq hF hΨ hkerΨ hv hvv hTv
    (fun hk => exists_mem_uLine_of_mem_normalizer_map hF hPerp hΨ hkerΨ hv hvv hTv hk)
    (Tim79a.suCoreStatement_holds m _ f hF hm4 v Tv hv hvv hTv)
  have hTX : Tv.map Φ ≤ X := (Subgroup.map_le_range Φ Tv).trans hrange.le
  rw [CFSG.map_codRestrict_eq_subgroupOf Φ hmem Tv] at hcore
  rw [← CFSG.GroupTheory.map_subtype_pCoreOf_normalizer_subgroupOf 2 hTX, hcore,
    Subgroup.map_map,
    show X.subtype.comp (Φ.codRestrict X hmem) = Φ from MonoidHom.ext fun _ => rfl]

theorem IsSUImage.rootIrrModel_subgroupOf {K : Type} [Group K] {X : Subgroup K}
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T : Subgroup K} (hT : T ∈ Δ) : Tim79a.RootIrrModel ↥X (T.subgroupOf X) := by
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  have hF := CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨v, Tv, hv0, hvv, hTv, rfl⟩ := SUTrans.exists_eq_map_of_mem hσ hm hΔ hT
  have hmem : ∀ x, Φ x ∈ X := fun x => hrange.le (MonoidHom.mem_range.2 ⟨x, rfl⟩)
  have hΨ : Function.Surjective (Φ.codRestrict X hmem) := fun y => by
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hrange.ge y.2)
    exact ⟨x, Subtype.ext hx⟩
  have hkerΨ : (Φ.codRestrict X hmem).ker ≤ Subgroup.center _ := by
    rw [MonoidHom.ker_codRestrict]; exact hker
  rw [← CFSG.map_codRestrict_eq_subgroupOf Φ hmem Tv]
  exact Tim79a.suModelIrr_of_statements Tim79a.suCoreStatement_holds
    Tim79a.suIrrStatement_holds m _ f hF hm4 ↥X _ hΨ hkerΨ v Tv hv0 hvv hTv

theorem IsSUImage.rootS2Model_subgroupOf {K : Type} [Group K] {X : Subgroup K}
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T : Subgroup K} (hT : T ∈ Δ) : Tim79a.RootS2Model ↥X (T.subgroupOf X) := by
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  have hF := CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨v, Tv, hv0, hvv, hTv, rfl⟩ := SUTrans.exists_eq_map_of_mem hσ hm hΔ hT
  have hmem : ∀ x, Φ x ∈ X := fun x => hrange.le (MonoidHom.mem_range.2 ⟨x, rfl⟩)
  have hΨ : Function.Surjective (Φ.codRestrict X hmem) := fun y => by
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hrange.ge y.2)
    exact ⟨x, Subtype.ext hx⟩
  have hkerΨ : (Φ.codRestrict X hmem).ker ≤ Subgroup.center _ := by
    rw [MonoidHom.ker_codRestrict]; exact hker
  rw [← CFSG.map_codRestrict_eq_subgroupOf Φ hmem Tv]
  exact Tim79a.suModelS2_holds m _ f hF hm4 ↥X _ hΨ hkerΨ v Tv hv0 hvv hTv

theorem IsSpImage.classicalRoot {K : Type} [Group K] {X : Subgroup K} {Δ : Set (Subgroup K)}
    {f m : ℕ} {hm1 : 1 ≤ m} (hX : IsSpImage X Δ f m hm1) (hf : 1 ≤ f) (hm : 2 ≤ m)
    {T : Subgroup K} (hT : T ∈ Δ) : Tim79a.ClassicalRoot ↥X (T.subgroupOf X) := by
  obtain ⟨Φ, hinj, hrange, hΔ⟩ := hX
  have hmem : ∀ x, Φ x ∈ X := fun x => hrange.le (MonoidHom.mem_range.2 ⟨x, rfl⟩)
  refine Or.inl ⟨f, (fun U => U.subgroupOf X) '' Δ, hf,
    ⟨m, hm, Φ.codRestrict X hmem, ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩,
      fun Y => ⟨?_, ?_⟩⟩, ⟨T, hT, rfl⟩⟩
  · intro y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hrange.ge y.2)
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨U, hU, rfl⟩
    obtain ⟨x, rfl⟩ := (hΔ U).1 hU
    exact ⟨x, (CFSG.map_codRestrict_eq_subgroupOf Φ hmem _).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, (hΔ _).2 ⟨x, rfl⟩, (CFSG.map_codRestrict_eq_subgroupOf Φ hmem _).symm⟩

theorem IsSUImage.le_inSubgroup_pCore_normalizer {K : Type} [Group K] {X : Subgroup K}
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T : Subgroup K} (hT : T ∈ Δ) :
    T ≤ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) ∧
      inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) ≤
        Subgroup.centralizer (T : Set K) := by
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  have hF := CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨v, Tv, hv0, hvv, hTv, rfl⟩ := SUTrans.exists_eq_map_of_mem hσ hm hΔ hT
  rw [SUTrans.inSubgroup_pCore_normalizer_map_eq hf hm4 hker hrange hv0 hvv hTv]
  refine ⟨Subgroup.map_mono (le_uRad_of_isUTransGroup hvv hTv), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨t, ht, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (uRad_le_centralizer hTv hy) t ht]

theorem IsSUImage.inSubgroup_pCore_cenOf_eq {K : Type} [Group K] {X : Subgroup K}
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T : Subgroup K} (hT : T ∈ Δ) :
    inSubgroup (pCore 2) (X ⊓ Subgroup.centralizer (T : Set K)) =
      inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) := by
  have hCN : X ⊓ Subgroup.centralizer (T : Set K) ≤ X ⊓ Subgroup.normalizer (T : Set K) :=
    inf_le_inf_left X (Subgroup.centralizer_le_normalizer (T : Set K))
  have hNC : Subgroup.normalizer (T : Set K) ≤
      Subgroup.normalizer (Subgroup.centralizer (T : Set K) : Set K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (T : Set K))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (T : Set K))
  refine le_antisymm (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_mono hCN
    fun x hx => CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_inf
      (Subgroup.le_normalizer hx.1) (hNC hx.2)) ?_
  exact CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore
    (CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 _)
    (le_inf ((CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 _).trans inf_le_left)
      (hX.le_inSubgroup_pCore_normalizer hm4 hT).2)
    (hCN.trans (CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 _))

theorem IsSUImage.natCard_pCore_normalizer {K : Type} [Group K] {X : Subgroup K}
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T : Subgroup K} (hT : T ∈ Δ) :
    Nat.card ↥(inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K))) =
      (2 ^ f) ^ (2 * m - 3) := by
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  have hF := CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution (GaloisField 2 (2 * f)) 2 f c = c →
      ∃ e, e + unitaryInvolution (GaloisField 2 (2 * f)) 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  obtain ⟨v, Tv, hv0, hvv, hTv, rfl⟩ := SUTrans.exists_eq_map_of_mem hσ hm hΔ hT
  rw [SUTrans.inSubgroup_pCore_normalizer_map_eq hf hm4 hker hrange hv0 hvv hTv]
  obtain ⟨d, hdd, had, Θ, G⟩ := Tim79a.exists_suFacts hF hm4 hv0 hvv hTv
  have hinj : Set.InjOn Φ (uRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) v : Set _) := by
    intro x hx y hy hxy
    have hk : x * y⁻¹ ∈ Φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.1 (eq_one_of_mem_uRad_of_mem_center hσ htr hvv hdd had hTv Θ G
      (mul_mem hx (inv_mem hy)) (hker hk))
  have h2 := Nat.card_image_of_injOn hinj
  rw [← Subgroup.coe_map] at h2
  calc Nat.card ↥((uRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) v).map Φ)
        = Nat.card (uRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) v) := h2
    _ = Nat.card ↥Tv * Nat.card
          ↥(perpPair (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) v d) :=
        natCard_uRad Θ (le_uRad_of_isUTransGroup hvv hTv)
    _ = 2 ^ f * ((2 ^ f) ^ 2) ^ (m - 2) := by
        rw [ModelRank.IsUTransGroup.natCard_eq hv0 hTv, CFSG.LieType.Steinberg.card_traceZero hF,
          natCard_perpPair hσ hvv hdd had (by omega), hF]
    _ = (2 ^ f) ^ (2 * m - 3) := by
        rw [show 2 * m - 3 = 2 * (m - 2) + 1 by omega]; ring

theorem IsSUImage.natCard_pCore_cenOf {K : Type} [Group K] {X : Subgroup K}
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T : Subgroup K} (hT : T ∈ Δ) :
    Nat.card ↥(inSubgroup (pCore 2) (X ⊓ cenOf T)) = (2 ^ f) ^ (2 * m - 3) := by
  rw [hX.inSubgroup_pCore_cenOf_eq hm4 hT]
  exact hX.natCard_pCore_normalizer hm4 hT

theorem IsSUImage.mem_of_forall_commutatorElement_mem {K : Type} [Group K] {X : Subgroup K}
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T : Subgroup K} (hT : T ∈ Δ) {r : K}
    (hr : r ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)))
    (hc : ∀ x ∈ X ⊓ Subgroup.centralizer (T : Set K), ⁅x, r⁆ ∈ T) : r ∈ T := by
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  have hF := CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution (GaloisField 2 (2 * f)) 2 f c = c →
      ∃ e, e + unitaryInvolution (GaloisField 2 (2 * f)) 2 f e = c :=
    fun c h => exists_add_unitaryInvolution_eq hF h
  obtain ⟨v, Tv, hv0, hvv, hTv, rfl⟩ := SUTrans.exists_eq_map_of_mem hσ hm hΔ hT
  rw [SUTrans.inSubgroup_pCore_normalizer_map_eq hf hm4 hker hrange hv0 hvv hTv] at hr
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hr
  obtain ⟨d, hdd, had, Θ, G⟩ := Tim79a.exists_suFacts hF hm4 hv0 hvv hTv
  refine Subgroup.mem_map_of_mem Φ ((Θ.eq_zero_iff hy).1 ?_)
  by_contra hne
  obtain ⟨e, he, hee, hey⟩ := G.nonorth (Θ.mem_perp y) hne
  have h1 : (1 : GaloisField 2 (2 * f)) + unitaryInvolution (GaloisField 2 (2 * f)) 2 f 1 = 0 := by
    rw [map_one, CharTwo.add_self_eq_zero]
  obtain ⟨t, ht⟩ := ModelRank.exists_suMat_eq_uTrans hσ hee h1
  obtain ⟨Te, hTe⟩ := ModelRank.exists_isUTransGroup hσ hee
  have hcomm := ModelRank.commuting_map Φ (hTv.commuting hσ hTe he.1)
  have hxC : Φ t ∈ X ⊓ Subgroup.centralizer ((Tv.map Φ : Subgroup K) : Set K) :=
    ⟨hrange.le (MonoidHom.mem_range.2 ⟨t, rfl⟩), Subgroup.mem_centralizer_iff.2 fun s hs =>
      hcomm s hs _ (Subgroup.mem_map_of_mem Φ ((hTe.1 t).2 ⟨1, h1, ht⟩))⟩
  have hty : ⁅t, y⁆ ∈ uRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) v := by
    have hta : suMat (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m t *ᵥ v =
        (1 : GaloisField 2 (2 * f)) • v := by
      rw [one_smul]; exact Θ.transv_a he ht
    rw [commutatorElement_def]
    exact mul_mem (conj_mem_uRad ⟨1, one_ne_zero, hta⟩ hy) (inv_mem hy)
  have h3 : Φ ⁅t, y⁆ ∈ Tv.map Φ := by rw [map_commutatorElement]; exact hc _ hxC
  obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.1 h3
  have hk : s⁻¹ * ⁅t, y⁆ ∈ Φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel]
  have h4 := eq_one_of_mem_uRad_of_mem_center hσ htr hvv hdd had hTv Θ G
    (mul_mem (inv_mem (le_uRad_of_isUTransGroup hvv hTv hs)) hty) (hker hk)
  have h5 : ⁅t, y⁆ ∈ Tv := by rw [← inv_mul_eq_one.1 h4]; exact hs
  have h6 := (Θ.eq_zero_iff hty).2 h5
  rw [radVec_commutatorElement_uTrans Θ he hee ht hy] at h6
  rcases smul_eq_zero.1 h6 with h7 | h7
  · exact hey h7
  · apply hey
    rw [h7, ← zero_smul (GaloisField 2 (2 * f)) (0 : Fin m → GaloisField 2 (2 * f)),
      uForm_smul_left, map_zero, zero_mul]

theorem IsSUImage.mem_of_forall_commute_pCore {K : Type} [Group K] {X : Subgroup K}
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T : Subgroup K} (hT : T ∈ Δ) {x : K}
    (hx : x ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)))
    (hxc : ∀ y ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)), x * y = y * x) :
    x ∈ T := by
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  have hF := CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution (GaloisField 2 (2 * f)) 2 f c = c →
      ∃ e, e + unitaryInvolution (GaloisField 2 (2 * f)) 2 f e = c :=
    fun c h => exists_add_unitaryInvolution_eq hF h
  obtain ⟨v, Tv, hv0, hvv, hTv, rfl⟩ := SUTrans.exists_eq_map_of_mem hσ hm hΔ hT
  rw [SUTrans.inSubgroup_pCore_normalizer_map_eq hf hm4 hker hrange hv0 hvv hTv] at hx hxc
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨d, hdd, had, Θ, G⟩ := Tim79a.exists_suFacts hF hm4 hv0 hvv hTv
  refine Subgroup.mem_map_of_mem Φ
    (mem_of_forall_commute_of_mem_uRad hσ htr hvv hdd had Θ G hy fun u hu => ?_)
  have hk : ⁅y, u⁆ ∈ Φ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hxc _ (Subgroup.mem_map_of_mem Φ hu))
  exact commutatorElement_eq_one_iff_mul_comm.1
    (eq_one_of_mem_isUTransGroup_of_mem_center hσ hvv hdd had hTv (Θ.comm_mem hy hu) (hker hk))

theorem IsSUImage.le_pCore_sup_cenOf {K : Type} [Group K] [Finite K] {X : Subgroup K} [X.Normal]
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T L : Subgroup K} (hT : T ∈ Δ) (hL : IsPGroup 2 L) (hLT : L ≤ cenOf T)
    (hNL : X ⊓ Subgroup.normalizer (T : Set K) ≤ Subgroup.normalizer (L : Set K)) :
    L ≤ inSubgroup (pCore 2) (X ⊓ cenOf T) ⊔ cenOf X := by
  have hTR := (hX.le_inSubgroup_pCore_normalizer hm4 hT).1
  have hTX : T ≤ X := hTR.trans
    ((CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 _).trans inf_le_left)
  rw [hX.inSubgroup_pCore_cenOf_eq hm4 hT]
  exact CFSG.GroupTheory.le_inSubgroup_pCore_sup_centralizer hTR
    (fun Y h1 h2 h3 => Tim79a.eq_or_eq_of_rootIrrModel hTX
      (hX.rootIrrModel_subgroupOf hm4 hT) h1 h2 h3)
    (fun l hl hb => Tim79a.mem_pCore_sup_centralizer_of_rootS2Model hTX
      (hX.rootS2Model_subgroupOf hm4 hT) hl hb) hL hLT hNL

theorem IsSUImage.centralizer_pCore_le {K : Type} [Group K] {X : Subgroup K} [X.Normal]
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (hm4 : 4 ≤ m) {T : Subgroup K} (hT : T ∈ Δ) :
    Subgroup.centralizer ((inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) :
      Subgroup K) : Set K) ≤ T ⊔ Subgroup.centralizer (X : Set K) := by
  obtain ⟨hTR, -⟩ := hX.le_inSubgroup_pCore_normalizer hm4 hT
  have hTX : T ≤ X :=
    hTR.trans ((CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 _).trans inf_le_left)
  intro l hl
  have hlT : l ∈ Subgroup.centralizer (T : Set K) := Subgroup.centralizer_le hTR hl
  obtain ⟨s, hs, hsl⟩ := Tim79a.exists_mem_pCore_inv_mul_mem_centralizer_of_rootS2Model hTX
    (hX.rootS2Model_subgroupOf hm4 hT) hlT fun b hb => by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hl b hb).symm]
      exact T.one_mem
  have hsT : s ∈ T := hX.mem_of_forall_commute_pCore hm4 hT hs fun b hb => by
    have hbX : b ∈ X := (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 _ hb).1
    have h1 := Subgroup.mem_centralizer_iff.1 hsl b hbX
    have h2 := Subgroup.mem_centralizer_iff.1 hl b hb
    calc s * b = s * b * (s⁻¹ * l) * (s⁻¹ * l)⁻¹ := by group
      _ = s * (s⁻¹ * l * b) * (s⁻¹ * l)⁻¹ := by rw [mul_assoc s b, h1]
      _ = l * b * l⁻¹ * s := by group
      _ = b * s := by rw [← h2]; group
  have h3 := Subgroup.mul_mem_sup hsT hsl
  rwa [mul_inv_cancel_left] at h3

end CFSG.RankThree.GF2n.Tim81
