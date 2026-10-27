module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FooteL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.L2Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.Transport
import CFSG.GroupTheory.TwoElementSquare

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.GH74.GLS.IVK
open CFSG.Blueprint (LieModel)

variable {W : Type} [CommGroup W] [Finite W]

private theorem subgroupOf_inf_eq {G : Type*} [Group G] (H₁ H₂ Y : Subgroup G) :
    (H₁ ⊓ H₂).subgroupOf Y = H₁.subgroupOf Y ⊓ H₂.subgroupOf Y := by
  ext g
  simp [Subgroup.mem_subgroupOf]

private theorem subgroupOf_centralizer_eq {G : Type*} [Group G] {B Y : Subgroup G}
    (hBY : B ≤ Y) :
    (Subgroup.centralizer (B : Set G)).subgroupOf Y =
      Subgroup.centralizer ((B.subgroupOf Y : Subgroup Y) : Set Y) := by
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    exact Subtype.ext (h b (Subgroup.mem_subgroupOf.mp hb))
  · intro h b hb
    exact congrArg Subtype.val (h ⟨b, hBY hb⟩ (Subgroup.mem_subgroupOf.mpr hb))

private theorem isElemAbelian_of_isElemAbelian2 {V : Type*} [CommGroup V]
    {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) : IsElemAbelian 2 A :=
  ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hA.1 a a.2 b b.2),
    fun x hx => hA.2 x hx⟩


private theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hmem : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [hH, Subgroup.mem_bot] at hmem
  exact e.injective (by rw [hmem, map_one])

omit [Finite W] in
private theorem isSimpleGroup_quotL {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLq : IsQuasisimple ↥L) : IsSimpleGroup (TenSix.QuotL Y L) := by
  obtain ⟨e⟩ := TenSix.nonempty_quotL_equiv hLY
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2.1
  exact e.isSimpleGroup

private theorem center_eq_bot_of_equiv_l2 {K : Type} [Group K]
    {F : Type} [Field F] [Finite F] (e : K ≃* L2 F) : Subgroup.center K = ⊥ :=
  center_eq_bot_of_mulEquiv (e.trans (L2.equivPSL F))
    (CFSG.GorensteinWalter.psl2_center_eq_bot F)

private theorem not_isSolvable_of_equiv_l2 {K : Type} [Group K]
    {F : Type} [Field F] [Finite F] (hFld : L2Field F) (e : K ≃* L2 F) :
    ¬ Group.IsSolvable K := by
  have : Fintype F := Fintype.ofFinite F
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have h3 : 3 < Nat.card F := hFld.2
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have : Nontrivial (CFSG.GorensteinWalter.PSL2 F) :=
    CFSG.LinearGroups.linear_projective_nontrivial (K := F) (n := 2) (by norm_num)
  have : Group.IsPerfect (CFSG.GorensteinWalter.PSL2 F) :=
    CFSG.LinearGroups.linear_projective_perfect (K := F) (n := 2) (by norm_num) (Or.inr h4)
  have hns : ¬ Group.IsSolvable (CFSG.GorensteinWalter.PSL2 F) :=
    Group.IsPerfect.not_isSolvable _
  intro h
  exact hns (Group.isSolvable_of_surjective (f := (e.trans (L2.equivPSL F)).toMonoidHom)
    (MulEquiv.surjective _))

private theorem exists_mul_ne_mul_of_not_isSolvable {K : Type} [Group K] [IsSimpleGroup K]
    (hns : ¬ Group.IsSolvable K) : ∃ a b : K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact hns (IsSimpleGroup.comm_iff_isSolvable.mp h)

private theorem centralizer_innAut_eq_bot {K : Type} [Group K]
    (hZ : Subgroup.center K = ⊥) :
    Subgroup.centralizer ((innAut K : Subgroup (MulAut K)) : Set (MulAut K)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  ext x
  have hι := CFSG.Fischer.mulAutConj_injective hZ
  have hconj : ∀ (β : MulAut K) (s : K), β * MulAut.conj s * β⁻¹ = MulAut.conj (β s) :=
    fun β s => by
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have h1 : MulAut.conj x * α = α * MulAut.conj x :=
    Subgroup.mem_centralizer_iff.1 hα (MulAut.conj x) ⟨x, rfl⟩
  have h2 : MulAut.conj (α x) = MulAut.conj x := by
    rw [← hconj α x, ← h1]
    group
  simpa using hι h2

omit [Finite W] in
private theorem card_map_subgroupOf {Y : Subgroup (MulAut W)} {K : Type} [Group K]
    (ψ : ↥Y →* MulAut K) (hodd : Odd (Nat.card ψ.ker)) {A : Subgroup (MulAut W)}
    (hA : IsPGroup 2 A) (hAY : A ≤ Y) :
    Nat.card ((A.subgroupOf Y).map ψ) = Nat.card A := by
  rw [TenSix.card_map_of_odd_ker ψ hodd (hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAY).symm),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv]

private theorem le_gammaRk_self {K : Type} [Group K] {Abar Ybar : Subgroup (MulAut K)} {m : ℕ}
    (hY : Abar ≤ Ybar) (hcard : 2 ^ m ≤ Nat.card Abar) : Abar ≤ TenSix.gammaRk m Abar Ybar := by
  have hmem : Abar ≤ Ybar ⊓ Subgroup.normalizer (Abar : Set (MulAut K)) :=
    fun x hx => ⟨hY hx, Subgroup.le_normalizer hx⟩
  exact hmem.trans
    (TenSix.inf_normalizer_le_gammaRk (A := Abar) (D := Abar) (Y := Ybar) le_rfl hcard)

omit [Finite W] in
private theorem innAut_sup_le_range {K : Type} [Group K] {L Y : Subgroup (MulAut W)}
    (ψ : ↥Y →* MulAut K) (hmap : (L.subgroupOf Y).map ψ = innAut K) {Abar : Subgroup (MulAut K)}
    (hAbar : Abar ≤ ψ.range) : innAut K ⊔ Abar ≤ ψ.range := by
  rw [← hmap]
  exact sup_le (Subgroup.map_le_range ψ (L.subgroupOf Y)) hAbar

private theorem centralizer_zpowers_eq {G : Type*} [Group G] (a : G) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx a (Subgroup.mem_zpowers a)
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hk]
    exact (show Commute a x from hx a rfl).zpow_left k

private theorem le_of_mem_aSet_card {Y : Subgroup (MulAut W)} {k n : ℕ}
    {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet k Y) (hAn : Nat.card A = 2 ^ n) : k ≤ n := by
  have h := E3.le_mQuot_bot_of_mem_aSet hA
  have h2 : E3.mQuot A ⊥ = n := by
    rw [E3.mQuot, Subgroup.relIndex_bot_left, hAn, padicValNat.prime_pow]
  omega

private theorem le_three_of_card_pow {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (hFld : L2Field F) (e : K ≃* CFSG.GH74.GLS.IVK.L2 F) {Abar : Subgroup (MulAut K)}
    (hAbar : IsElemAbelian 2 Abar) {n : ℕ} (hcard : Nat.card Abar = 2 ^ n) : n ≤ 3 := by
  have h8 := TenSix.card_le_eight_of_isElemAbelian hFld e hAbar
  rw [hcard] at h8
  have h23 : (2 : ℕ) ^ 3 = 8 := by norm_num
  rw [← h23] at h8
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h8

private theorem le_pCoreOf_map_gammaRk_inf_centralizer {Y : Subgroup (MulAut W)}
    {K : Type} [Group K] (ψ : ↥Y →* MulAut K) (hodd : Odd (Nat.card ψ.ker))
    (hW : ∀ w : W, w ^ 2 = 1) {k n : ℕ} (hk : 0 < k) {A B : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet k Y) (hAn : Nat.card A = 2 ^ n) (hBA : B ≤ A)
    (hm : E3.mQuot A B = k) :
    (A.subgroupOf Y).map ψ ≤
      pCoreOf 2 (TenSix.gammaRk (n + 1 - k) ((A.subgroupOf Y).map ψ) ψ.range ⊓
        Subgroup.centralizer ((B.subgroupOf Y).map ψ)) := by
  classical
  have hAY : A ≤ Y := hA.1
  have hBY : B ≤ Y := hBA.trans hAY
  have h1 : A ≤ pCoreOf 2 (TenSix.gammaRk (n + 1 - k) A Y ⊓
      Subgroup.centralizer (B : Set (MulAut W))) :=
    TenSix.le_pCoreOf_gammaRk_inf_centralizer hW hk hA hAn hBA hm
  have hHY : TenSix.gammaRk (n + 1 - k) A Y ⊓ Subgroup.centralizer (B : Set (MulAut W)) ≤ Y :=
    inf_le_left.trans (TenSix.gammaRk_le _ _ _)
  have h2 : A.subgroupOf Y ≤
      (pCoreOf 2 (TenSix.gammaRk (n + 1 - k) A Y ⊓
        Subgroup.centralizer (B : Set (MulAut W)))).subgroupOf Y :=
    Subgroup.subgroupOf_mono Y h1
  rw [TenSix.pCoreOf_subgroupOf 2 hHY, subgroupOf_inf_eq,
    TenSix.gammaRk_subgroupOf hAY, subgroupOf_centralizer_eq hBY] at h2
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hA'2 : IsPGroup 2 (A.subgroupOf Y) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAY).symm
  have hB'2 : IsPGroup 2 (B.subgroupOf Y) :=
    hA'2.to_le (Subgroup.subgroupOf_mono Y hBA)
  have hmle : n + 1 - k ≤ n := by omega
  have hcard : 2 ^ (n + 1 - k) ≤ Nat.card (A.subgroupOf Y) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv, hAn]
    exact Nat.pow_le_pow_right (by norm_num) hmle
  have hA'le : A.subgroupOf Y ≤ TenSix.gammaRk (n + 1 - k) (A.subgroupOf Y) ⊤ := by
    have hmem : A.subgroupOf Y ≤
        (⊤ : Subgroup ↥Y) ⊓ Subgroup.normalizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) :=
      fun x hx => ⟨trivial, Subgroup.le_normalizer hx⟩
    exact hmem.trans (TenSix.inf_normalizer_le_gammaRk (Y := ⊤) le_rfl hcard)
  have hBH : B.subgroupOf Y ≤ TenSix.gammaRk (n + 1 - k) (A.subgroupOf Y) ⊤ :=
    (Subgroup.subgroupOf_mono Y hBA).trans hA'le
  refine (Subgroup.map_mono h2).trans ?_
  refine (TenSix.map_pCoreOf_le ψ 2 _).trans (le_of_eq ?_)
  rw [TenSix.map_inf_centralizer_of_odd_ker ψ hodd hB'2 hBH,
    TenSix.map_gammaRk_of_odd_ker ψ hodd hA'2 le_top, Subgroup.map_top]

private theorem false_of_le_pCoreOf_gammaRk_one {Y : Subgroup (MulAut W)} {K : Type}
    [Group K] [Finite K] {F : Type} [Field F] [Finite F] (hFld : L2Field F) (e : K ≃* L2 F)
    (ψ : ↥Y →* MulAut K) (hodd : Odd (Nat.card ψ.ker)) (hsimple : IsSimpleGroup K)
    (hW : ∀ w : W, w ^ 2 = 1)
    {k n : ℕ} (hk : 0 < k) (hkn : k = n) {A : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet k Y) (hAn : Nat.card A = 2 ^ n)
    (hinnΓ : innAut K ≤ TenSix.gammaRk 1 ((A.subgroupOf Y).map ψ) ψ.range) : False := by
  classical
  set Abar : Subgroup (MulAut K) := (A.subgroupOf Y).map ψ with hAbar
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hAbar_card : Nat.card Abar = 2 ^ n := by
    rw [hAbar, card_map_subgroupOf ψ hodd hA2 hA.1, hAn]
  have hn1 : 1 ≤ n := by omega
  have hAbar_ne : Abar ≠ ⊥ := by
    intro h
    have hc : Nat.card Abar = 1 := by rw [h]; simp
    rw [hAbar_card] at hc
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    omega
  have hinnΓ' : innAut K ≤ TenSix.gammaRk 1 Abar ψ.range := hinnΓ
  have hm : E3.mQuot A ⊥ = k := by
    rw [E3.mQuot, Subgroup.relIndex_bot_left, hAn, padicValNat.prime_pow, hkn]
  have htr := le_pCoreOf_map_gammaRk_inf_centralizer ψ hodd hW hk hA hAn
    (bot_le : (⊥ : Subgroup (MulAut W)) ≤ A) hm
  have hm1 : n + 1 - k = 1 := by omega
  rw [hm1] at htr
  have hcentbot : Subgroup.centralizer ((⊥ : Subgroup (MulAut K)) : Set (MulAut K)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := by simpa using hy
    rw [hy1, mul_one, one_mul]
  have htr0 : Abar ≤ pCoreOf 2 (TenSix.gammaRk 1 Abar ψ.range ⊓
      Subgroup.centralizer (⊥ : Subgroup (MulAut K))) := by
    rw [← hAbar] at htr
    simpa only [Subgroup.map_bot, Subgroup.bot_subgroupOf] using htr
  have htr' : Abar ≤ pCoreOf 2 (TenSix.gammaRk 1 Abar ψ.range) := by
    rwa [hcentbot, inf_top_eq] at htr0
  set Γ : Subgroup (MulAut K) := TenSix.gammaRk 1 Abar ψ.range with hΓ
  set P : Subgroup (MulAut K) := pCoreOf 2 Γ with hP
  have hPΓ : P ≤ Γ := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 Γ
  have hP2 : IsPGroup 2 P := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 Γ
  have hPnorm : (P.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff hPΓ).2 fun h k hh hk =>
      CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hk hh
  have hPconj : ∀ h k : MulAut K, h ∈ P → k ∈ Γ → k * h * k⁻¹ ∈ P :=
    (Subgroup.normal_subgroupOf_iff hPΓ).1 hPnorm
  have hInΓ : innAut K ≤ Γ := hinnΓ'
  have hPIbot : P ⊓ innAut K = ⊥ := by
    have hNnorm : ((P ⊓ innAut K).subgroupOf (innAut K)).Normal :=
      (Subgroup.normal_subgroupOf_iff inf_le_right).2 fun h k hh hk =>
        ⟨hPconj h k hh.1 (hInΓ hk),
          (innAut K).mul_mem ((innAut K).mul_mem hk hh.2) ((innAut K).inv_mem hk)⟩
    have : ((P ⊓ innAut K).subgroupOf (innAut K)).Normal := hNnorm
    have hN2 : IsPGroup 2 ((P ⊓ innAut K).subgroupOf (innAut K)) :=
      (hP2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_equiv_l2 e
    have hns : ¬ Group.IsSolvable K := not_isSolvable_of_equiv_l2 hFld e
    have hnabK : ∃ a b : K, a * b ≠ b * a := exists_mul_ne_mul_of_not_isSolvable hns
    let eI : K ≃* innAut K := CFSG.Fischer.innerAutEquiv hZ
    have : IsSimpleGroup K := hsimple
    have : IsSimpleGroup (innAut K) := eI.symm.isSimpleGroup
    have hnab : ∃ a b : innAut K, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnabK
      exact ⟨eI a, eI b, fun h => hab (eI.injective (by simpa using h))⟩
    have hNbot := CFSG.eq_bot_of_normal_isPGroup_of_isSimpleGroup hnab hN2
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥(innAut K)) ∈ (P ⊓ innAut K).subgroupOf (innAut K) :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [hNbot, Subgroup.mem_bot] at hx'
    exact Subtype.ext_iff.mp hx'
  have hPcent : P ≤ Subgroup.centralizer ((innAut K : Subgroup (MulAut K)) : Set (MulAut K)) := by
    have : (P.subgroupOf Γ).Normal := hPnorm
    have hInormΓ : ((innAut K).subgroupOf Γ).Normal :=
      (Subgroup.normal_subgroupOf_iff hInΓ).2 fun h k hh hk =>
        (show (innAut K).Normal from
          CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K).conj_mem h hh k
    have : ((innAut K).subgroupOf Γ).Normal := hInormΓ
    have hbot : P.subgroupOf Γ ⊓ (innAut K).subgroupOf Γ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      have hx' : ((x : Γ) : MulAut K) ∈ P ⊓ innAut K :=
        ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
      rw [hPIbot, Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    have hcomm : ⁅P.subgroupOf Γ, (innAut K).subgroupOf Γ⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_le_inf _ _).trans (le_of_eq hbot))
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hpΓ : p ∈ Γ := hPΓ hp
    have hqΓ : q ∈ Γ := hInΓ hq
    have hmem : (⟨p, hpΓ⟩ : Γ) ∈
        Subgroup.centralizer (((innAut K).subgroupOf Γ : Subgroup Γ) : Set Γ) :=
      hcent (Subgroup.mem_subgroupOf.mpr hp)
    have hpq := Subgroup.mem_centralizer_iff.mp hmem ⟨q, hqΓ⟩ (Subgroup.mem_subgroupOf.mpr hq)
    exact congrArg Subtype.val hpq
  have hPbot : P = ⊥ := le_bot_iff.mp
    (hPcent.trans (le_of_eq (centralizer_innAut_eq_bot (center_eq_bot_of_equiv_l2 e))))
  exact hAbar_ne (le_bot_iff.mp (htr'.trans (le_of_eq hPbot)))


private theorem false_of_card_eq_three {Y L : Subgroup (MulAut W)} {K : Type} [Group K]
    [Finite K] {F : Type} [Field F] [Finite F] (hFld : L2Field F) (e : K ≃* L2 F)
    (ψ : ↥Y →* MulAut K) (hodd : Odd (Nat.card ψ.ker))
    (hmap : (L.subgroupOf Y).map ψ = innAut K) (hsimple : IsSimpleGroup K)
    (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 3 Y) (hAn : Nat.card A = 2 ^ 3) : False := by
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hA'ea : IsElemAbelian 2 (A.subgroupOf Y) :=
    CFSG.Open.IsElemAbelian.subgroupOf (isElemAbelian_of_isElemAbelian2 hA.2.2.1) Y
  have hAbar_ea : IsElemAbelian 2 ((A.subgroupOf Y).map ψ) :=
    CFSG.Open.IsElemAbelian.map hA'ea ψ
  have hAbar_card : Nat.card ((A.subgroupOf Y).map ψ) = 8 := by
    rw [card_map_subgroupOf ψ hodd hA2 hA.1, hAn]
    norm_num
  have hbase : innAut K ≤
      TenSix.gammaRk 1 ((A.subgroupOf Y).map ψ) (innAut K ⊔ (A.subgroupOf Y).map ψ) :=
    TenSix.innAut_le_gammaRk_one_of_card_eight (K := K) hFld e hAbar_ea hAbar_card
  have hsup : innAut K ⊔ (A.subgroupOf Y).map ψ ≤ ψ.range :=
    innAut_sup_le_range ψ hmap (Subgroup.map_le_range ψ (A.subgroupOf Y))
  exact false_of_le_pCoreOf_gammaRk_one hFld e ψ hodd hsimple hW (by norm_num) rfl hA hAn
    (hbase.trans (TenSix.gammaRk_mono hsup))

private theorem false_of_card_eq_four {Y L : Subgroup (MulAut W)} {K : Type} [Group K]
    [Finite K] {F : Type} [Field F] [Finite F] (hFld : L2Field F) (e : K ≃* L2 F)
    (ψ : ↥Y →* MulAut K) (hodd : Odd (Nat.card ψ.ker))
    (hmap : (L.subgroupOf Y).map ψ = innAut K) (hsimple : IsSimpleGroup K)
    (h9 : 9 < Nat.card F) (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 Y) (hAn : Nat.card A = 2 ^ 2) : False := by
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hA'ea : IsElemAbelian 2 (A.subgroupOf Y) :=
    CFSG.Open.IsElemAbelian.subgroupOf (isElemAbelian_of_isElemAbelian2 hA.2.2.1) Y
  have hAbar_ea : IsElemAbelian 2 ((A.subgroupOf Y).map ψ) :=
    CFSG.Open.IsElemAbelian.map hA'ea ψ
  have hAbar_card : Nat.card ((A.subgroupOf Y).map ψ) = 4 := by
    rw [card_map_subgroupOf ψ hodd hA2 hA.1, hAn]
    norm_num
  have hbase : innAut K ≤
      TenSix.gammaRk 1 ((A.subgroupOf Y).map ψ) (innAut K ⊔ (A.subgroupOf Y).map ψ) :=
    TenSix.innAut_le_gammaRk_one_of_card_four (K := K) hFld h9 e hAbar_ea hAbar_card
  have hsup : innAut K ⊔ (A.subgroupOf Y).map ψ ≤ ψ.range :=
    innAut_sup_le_range ψ hmap (Subgroup.map_le_range ψ (A.subgroupOf Y))
  exact false_of_le_pCoreOf_gammaRk_one hFld e ψ hodd hsimple hW (by norm_num) rfl hA hAn
    (hbase.trans (TenSix.gammaRk_mono hsup))

private theorem false_of_card_eight {Y L : Subgroup (MulAut W)} {K : Type} [Group K] [Finite K]
    {F : Type} [Field F] [Finite F] (hFld : L2Field F) (e : K ≃* L2 F)
    (ψ : ↥Y →* MulAut K) (hodd : Odd (Nat.card ψ.ker))
    (hmap : (L.subgroupOf Y).map ψ = innAut K)
    (h9 : 9 < Nat.card F) (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 Y) (hAn : Nat.card A = 2 ^ 3) : False := by
  classical
  set Abar : Subgroup (MulAut K) := (A.subgroupOf Y).map ψ with hAbar
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hA'ea : IsElemAbelian 2 (A.subgroupOf Y) :=
    CFSG.Open.IsElemAbelian.subgroupOf (isElemAbelian_of_isElemAbelian2 hA.2.2.1) Y
  have hAbar_ea : IsElemAbelian 2 Abar := CFSG.Open.IsElemAbelian.map hA'ea ψ
  have hAbar_card : Nat.card Abar = 8 := by
    rw [hAbar, card_map_subgroupOf ψ hodd hA2 hA.1, hAn]
    norm_num
  have hAbarY : Abar ≤ ψ.range := by
    rw [hAbar]
    exact Subgroup.map_le_range ψ (A.subgroupOf Y)
  have hsup : innAut K ⊔ Abar ≤ ψ.range := by
    rw [← hmap]
    exact sup_le (Subgroup.map_le_range ψ (L.subgroupOf Y)) hAbarY
  have hinnΓ : innAut K ≤ TenSix.gammaRk 2 Abar ψ.range :=
    (TenSix.innAut_le_gammaRk_two_of_card_eight (K := K) hFld h9 e hAbar_ea hAbar_card).trans
      (TenSix.gammaRk_mono hsup)
  obtain ⟨abar, habarA, habar_ne, habar_prop⟩ :=
    TenSix.exists_not_le_pCoreOf_of_card_eight (K := K) hFld h9 e hAbar_ea hAbar_card
  rw [hAbar] at habarA
  obtain ⟨x, hx, hψx⟩ := Subgroup.mem_map.mp habarA
  have hxY : (x : MulAut W) ∈ Y := x.2
  have hxA : (x : MulAut W) ∈ A := Subgroup.mem_subgroupOf.mp hx
  have ha_ne : (x : MulAut W) ≠ 1 := by
    intro h1
    apply habar_ne
    have hx1 : x = 1 := Subtype.ext h1
    rw [hx1, map_one] at hψx
    exact hψx.symm
  have ha_sq : (x : MulAut W) * (x : MulAut W) = 1 := by
    have := hA.2.2.1.2 (x : MulAut W) hxA
    rwa [pow_two] at this
  have horder : orderOf (x : MulAut W) = 2 := by
    have hdvd : orderOf (x : MulAut W) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h (by
        intro h1
        exact ha_ne (orderOf_eq_one_iff.mp h1))
    · exact h
  have hBcard : Nat.card (Subgroup.zpowers (x : MulAut W)) = 2 := by
    rw [Nat.card_zpowers, horder]
  have hBA : Subgroup.zpowers (x : MulAut W) ≤ A :=
    Subgroup.zpowers_le.mpr hxA
  have hm : E3.mQuot A (Subgroup.zpowers (x : MulAut W)) = 2 := by
    have hrel := Subgroup.relIndex_mul_card (Subgroup.zpowers (x : MulAut W)) A
    rw [inf_eq_left.mpr hBA, hBcard, hAn] at hrel
    have hrel2 : (Subgroup.zpowers (x : MulAut W)).relIndex A = 4 := by omega
    rw [E3.mQuot, hrel2]
    have h42 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h42, padicValNat.prime_pow]
  have htr := le_pCoreOf_map_gammaRk_inf_centralizer ψ hodd hW (by norm_num : 0 < 2) hA hAn
    hBA hm
  have hexp : 3 + 1 - 2 = 2 := by norm_num
  rw [hexp] at htr
  have hBbar : ((Subgroup.zpowers (x : MulAut W)).subgroupOf Y).map ψ =
      Subgroup.zpowers abar := by
    have hsub : (Subgroup.zpowers (x : MulAut W)).subgroupOf Y =
        Subgroup.zpowers (⟨(x : MulAut W), hxY⟩ : ↥Y) := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext hk⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, congrArg Subtype.val hk⟩
    rw [hsub, MonoidHom.map_zpowers]
    have hxeq : (⟨(x : MulAut W), hxY⟩ : ↥Y) = x := Subtype.ext rfl
    rw [hxeq, hψx]
  have hcentB : Subgroup.centralizer ((Subgroup.zpowers abar : Subgroup (MulAut K)) : Set _) =
      Subgroup.centralizer ({abar} : Set (MulAut K)) := centralizer_zpowers_eq abar
  rw [hBbar, hcentB] at htr
  set Γ : Subgroup (MulAut K) := TenSix.gammaRk 2 Abar ψ.range with hΓ
  set H : Subgroup (MulAut K) := Γ ⊓ Subgroup.centralizer ({abar} : Set (MulAut K)) with hH
  have hAbarΓ : Abar ≤ Γ := by
    have hcard : 2 ^ 2 ≤ Nat.card Abar := by rw [hAbar_card]; norm_num
    exact le_gammaRk_self hAbarY hcard
  have hAbarC : Abar ≤ Subgroup.centralizer ({abar} : Set (MulAut K)) := by
    have : IsMulCommutative ↥Abar := hAbar_ea.1
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hc := mul_comm' (⟨x, hx⟩ : Abar) ⟨abar, habarA⟩
    exact (congrArg Subtype.val hc).symm
  have hAH : Abar ≤ H := fun x hx => ⟨hAbarΓ hx, hAbarC hx⟩
  have hHle : H ≤ Subgroup.centralizer ({abar} : Set (MulAut K)) := inf_le_right
  have hmid : innAut K ⊓ Subgroup.centralizer ({abar} : Set (MulAut K)) ≤ H := by
    rintro x ⟨hxinn, hxc⟩
    exact ⟨hinnΓ hxinn, hxc⟩
  have htrH : Abar ≤ pCoreOf 2 H := htr
  exact habar_prop H hAH hHle hmid htrH

private theorem le_three_of_card_pow_eight {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (hcard8 : Nat.card F = 8) (e : K ≃* L2 F) {Abar : Subgroup (MulAut K)}
    (hAbar : IsElemAbelian 2 Abar) {n : ℕ} (hcard : Nat.card Abar = 2 ^ n) : n ≤ 3 := by
  have h8 := TenSix.card_le_eight_of_isElemAbelian_eight (K := K) hcard8 e hAbar
  rw [hcard] at h8
  have h23 : (2 : ℕ) ^ 3 = 8 := by norm_num
  rw [← h23] at h8
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h8

private theorem aParam_le_two {Y L : Subgroup (MulAut W)} {K : Type} [Group K] [Finite K]
    {F : Type} [Field F] [Finite F] (hFld : L2Field F) (e : K ≃* L2 F)
    (ψ : ↥Y →* MulAut K) (hodd : Odd (Nat.card ψ.ker))
    (hmap : (L.subgroupOf Y).map ψ = innAut K) (hsimple : IsSimpleGroup K)
    (hW : ∀ w : W, w ^ 2 = 1) : E3.aParam Y ≤ 2 := by
  classical
  by_cases hev : Even (Nat.card Y)
  · rw [E3.aParam, if_pos hev]
    by_cases hne : {k : ℕ | 0 < k ∧ (E3.aSet k Y).Nonempty}.Nonempty
    · refine csSup_le hne ?_
      rintro k ⟨hk, A, hA⟩
      by_contra hcon
      push Not at hcon
      have hk3 : 3 ≤ k := by omega
      have hA3 : A ∈ E3.aSet 3 Y := E3.aSet_anti hk3 Y hA
      have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA3.2.2.1
      obtain ⟨n, hAn⟩ := (IsPGroup.iff_card (p := 2)).mp hA2
      have h3n : 3 ≤ n := le_of_mem_aSet_card hA3 hAn
      have hA'ea : IsElemAbelian 2 (A.subgroupOf Y) :=
        CFSG.Open.IsElemAbelian.subgroupOf (isElemAbelian_of_isElemAbelian2 hA3.2.2.1) Y
      have hAbar_ea : IsElemAbelian 2 ((A.subgroupOf Y).map ψ) :=
        CFSG.Open.IsElemAbelian.map hA'ea ψ
      have hAbar_card : Nat.card ((A.subgroupOf Y).map ψ) = 2 ^ n := by
        rw [card_map_subgroupOf ψ hodd hA2 hA3.1, hAn]
      have hn3 : n ≤ 3 := le_three_of_card_pow hFld e hAbar_ea hAbar_card
      have hn : n = 3 := by omega
      exact false_of_card_eq_three hFld e ψ hodd hmap hsimple hW hA3 (by rw [hAn, hn])
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
      exact Nat.zero_le 2
  · rw [E3.aParam_of_odd hev]
    exact Nat.zero_le 2

private theorem aParam_eq_one {Y L : Subgroup (MulAut W)} {K : Type} [Group K] [Finite K]
    {F : Type} [Field F] [Finite F] (hFld : L2Field F) (e : K ≃* L2 F)
    (ψ : ↥Y →* MulAut K) (hodd : Odd (Nat.card ψ.ker))
    (hmap : (L.subgroupOf Y).map ψ = innAut K) (hsimple : IsSimpleGroup K)
    (h9 : 9 < Nat.card F) (hW : ∀ w : W, w ^ 2 = 1)
    (hinv : ∃ t : ↥Y, orderOf t = 2) : E3.aParam Y = 1 := by
  classical
  have hno2 : ∀ A : Subgroup (MulAut W), A ∈ E3.aSet 2 Y → False := by
    intro A hA
    have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
    obtain ⟨n, hAn⟩ := (IsPGroup.iff_card (p := 2)).mp hA2
    have h2n : 2 ≤ n := le_of_mem_aSet_card hA hAn
    have hA'ea : IsElemAbelian 2 (A.subgroupOf Y) :=
      CFSG.Open.IsElemAbelian.subgroupOf (isElemAbelian_of_isElemAbelian2 hA.2.2.1) Y
    have hAbar_ea : IsElemAbelian 2 ((A.subgroupOf Y).map ψ) :=
      CFSG.Open.IsElemAbelian.map hA'ea ψ
    have hAbar_card : Nat.card ((A.subgroupOf Y).map ψ) = 2 ^ n := by
      rw [card_map_subgroupOf ψ hodd hA2 hA.1, hAn]
    have hn3 : n ≤ 3 := le_three_of_card_pow hFld e hAbar_ea hAbar_card
    rcases (by omega : n = 2 ∨ n = 3) with hn | hn
    · exact false_of_card_eq_four hFld e ψ hodd hmap hsimple h9 hW hA (by rw [hAn, hn])
    · exact false_of_card_eight hFld e ψ hodd hmap h9 hW hA (by rw [hAn, hn])
  obtain ⟨t, ht⟩ := hinv
  have h2Y : 2 ∣ Nat.card ↥Y := by
    have h := orderOf_dvd_natCard t
    rwa [ht] at h
  have hEvenY : Even (Nat.card Y) := even_iff_two_dvd.mpr h2Y
  have htW : orderOf (t : MulAut W) = 2 := (Subgroup.orderOf_coe t).trans ht
  have ht2 : (t : MulAut W) ^ 2 = 1 := by
    rw [← htW]
    exact pow_orderOf_eq_one _
  have hmem : Subgroup.zpowers (t : MulAut W) ∈ E3.aSet 1 Y := by
    rw [E3.aSet_one]
    refine ⟨Subgroup.zpowers_le.mpr t.2, ?_, CFSG.Quasithin.StabLat.isElemAbelian2_zpowers ht2⟩
    intro hbot
    have h1 : (t : MulAut W) = 1 := Subgroup.zpowers_eq_bot.mp hbot
    rw [h1] at htW
    simp at htW
  have hset : {k : ℕ | 0 < k ∧ (E3.aSet k Y).Nonempty} = {1} := by
    ext k
    constructor
    · rintro ⟨hk, A, hA⟩
      have hk1 : k = 1 := by
        by_contra hne
        exact hno2 A (E3.aSet_anti (by omega : 2 ≤ k) Y hA)
      rw [hk1]
      rfl
    · intro hk
      rw [Set.mem_singleton_iff] at hk
      subst hk
      exact ⟨by norm_num, ⟨_, hmem⟩⟩
  rw [E3.aParam, if_pos hEvenY, hset, csSup_singleton]

private theorem aParam_le_three_eight {Y : Subgroup (MulAut W)} {K : Type} [Group K]
    [Finite K] {F : Type} [Field F] [Finite F] (hcard8 : Nat.card F = 8) (e : K ≃* L2 F)
    (ψ : ↥Y →* MulAut K) (hodd : Odd (Nat.card ψ.ker)) :
    E3.aParam Y ≤ 3 := by
  classical
  by_cases hev : Even (Nat.card Y)
  · rw [E3.aParam, if_pos hev]
    by_cases hne : {k : ℕ | 0 < k ∧ (E3.aSet k Y).Nonempty}.Nonempty
    · refine csSup_le hne ?_
      rintro k ⟨hk, A, hA⟩
      have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
      obtain ⟨n, hAn⟩ := (IsPGroup.iff_card (p := 2)).mp hA2
      have hkn : k ≤ n := le_of_mem_aSet_card hA hAn
      have hA'ea : IsElemAbelian 2 (A.subgroupOf Y) :=
        CFSG.Open.IsElemAbelian.subgroupOf (isElemAbelian_of_isElemAbelian2 hA.2.2.1) Y
      have hAbar_ea : IsElemAbelian 2 ((A.subgroupOf Y).map ψ) :=
        CFSG.Open.IsElemAbelian.map hA'ea ψ
      have hAbar_card : Nat.card ((A.subgroupOf Y).map ψ) = 2 ^ n := by
        rw [card_map_subgroupOf ψ hodd hA2 hA.1, hAn]
      have hn3 : n ≤ 3 := le_three_of_card_pow_eight hcard8 e hAbar_ea hAbar_card
      omega
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
      exact Nat.zero_le 3
  · rw [E3.aParam_of_odd hev]
    exact Nat.zero_le 3

theorem w4Lem10_6_psl2 (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} {p e : ℕ}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hLq : IsQuasisimple ↥L)
    (hO2 : O2Trivial L) (hp2 : p ≠ 2) (hM : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 p e) :
    (9 < p ^ e → E3.aParam Y = 1) ∧ E3.aParam Y ≤ 2 := by
  obtain ⟨hp, he1, h2, h3, F, hField, hFin, hcard, ⟨e₁⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hM
  have e₁' : (↥L ⧸ Subgroup.center ↥L) ≃* CFSG.GorensteinWalter.PSL2 F := e₁
  have hFld : L2Field F := by
    refine ⟨?_, ?_⟩
    · rw [hcard]
      exact (hp.odd_of_ne_two hp2).pow
    · rw [hcard]
      have hp2e : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (by omega) p)
      omega
  obtain ⟨e₂⟩ := TenSix.nonempty_quotL_equiv hLY
  let eL := e₂.trans (e₁'.trans (L2.equivPSL F).symm)
  have hodd := TenSix.odd_card_ker_quotAct hLY hLn hF hLq hO2
  have hmap := TenSix.map_quotAct hLn
  have hsimple := isSimpleGroup_quotL hLY hLq
  have hinv : ∃ t : ↥Y, orderOf t = 2 := by
    obtain ⟨h, hh1, hh2⟩ := CFSG.SectionRank.Ccomm.exists_involution_PSL2 F
    have h2P : 2 ∣ Nat.card (CFSG.GorensteinWalter.PSL2 F) := by
      have hdvd := orderOf_dvd_natCard h
      have hord : orderOf h = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime hh2 hh1
      rwa [hord] at hdvd
    have h2K : 2 ∣ Nat.card (TenSix.QuotL Y L) := by
      rwa [← Nat.card_congr (eL.trans (L2.equivPSL F)).toEquiv] at h2P
    have h2L : 2 ∣ Nat.card ↥L := by
      have h2Q : 2 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
        obtain ⟨ee⟩ := TenSix.nonempty_quotL_equiv hLY
        rw [Nat.card_congr ee.toEquiv] at h2K
        exact h2K
      exact h2Q.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥L))
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2
      (h2L.trans (Subgroup.card_dvd_of_le hLY))
    exact ⟨t, ht⟩
  refine ⟨?_, ?_⟩
  · intro h9
    have h9' : 9 < Nat.card F := by rw [hcard]; exact h9
    exact aParam_eq_one hFld eL (TenSix.quotAct Y L hLn) hodd hmap hsimple h9' hW hinv
  · exact aParam_le_two hFld eL (TenSix.quotAct Y L hLn) hodd hmap hsimple hW

theorem w4Lem10_6_psl2_eight {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hLq : IsQuasisimple ↥L)
    (hO2 : O2Trivial L) (hM : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 3) :
    E3.aParam Y ≤ 3 := by
  obtain ⟨hp, he1, h2, h3, F, hField, hFin, hcard, ⟨e₁⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hM
  have hcard8 : Nat.card F = 8 := by rw [hcard]; norm_num
  have e₁' : (↥L ⧸ Subgroup.center ↥L) ≃* CFSG.GorensteinWalter.PSL2 F := e₁
  obtain ⟨e₂⟩ := TenSix.nonempty_quotL_equiv hLY
  let eL := e₂.trans (e₁'.trans (L2.equivPSL F).symm)
  have hodd := TenSix.odd_card_ker_quotAct hLY hLn hF hLq hO2
  exact aParam_le_three_eight hcard8 eL (TenSix.quotAct Y L hLn) hodd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
