module

public import CFSG.RankThree.GF2n.Parrott.Section3RemarksU
public import CFSG.RankThree.GF2n.Parrott.Section3RemarksQ8
import CFSG.RankThree.GF2n.Parrott.Section3RemarksE9
import CFSG.RankThree.GF2n.Parrott.A1LocalData
import CFSG.RankThree.GF2n.Parrott.ActionZSimplicity
import CFSG.GroupTheory.SupCommute
import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting
import CFSG.LocalAnalysis.RankThreeUC.WeakModules

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (fixedSpace commSpace)
open scoped commutatorElement

theorem mulAut_eq_one_of_commute_of_isKleinFour {E : Type*} [Group E] [IsKleinFour E]
    {f g : MulAut E} (hf : f ^ 3 = 1) (hf1 : f ≠ 1) (hg : g ^ 2 = 1) (hfg : f * g = g * f) :
    g = 1 := by
  have key : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → b ^ 2 = 1 →
      a = 1 ∨ b = 1 ∨ a * b ≠ b * a := by decide +kernel
  let e := CFSG.kleinFourAutomorphismEquivSymmetricThree E
  have he : ∀ k : MulAut E, e k = 1 → k = 1 := fun k hk =>
    e.injective (hk.trans (map_one e).symm)
  rcases key (e f) (e g) (by rw [← map_pow, hf, map_one]) (by rw [← map_pow, hg, map_one]) with
    h | h | h
  · exact absurd (he f h) hf1
  · exact he g h
  · exact absurd (by rw [← map_mul, hfg, map_mul]) h

private noncomputable def restrictMulAut {W : Type*} [Group W] (F : Subgroup W) (f : MulAut W)
    (hf : ∀ x ∈ F, f x ∈ F) (hf' : ∀ x ∈ F, f⁻¹ x ∈ F) : MulAut ↥F where
  toFun x := ⟨f x, hf x x.2⟩
  invFun x := ⟨f⁻¹ x, hf' x x.2⟩
  left_inv x := Subtype.ext (MulAut.inv_apply_self _ f x)
  right_inv x := Subtype.ext (MulAut.apply_inv_self _ f x)
  map_mul' x y := Subtype.ext (map_mul f (x : W) y)

private theorem restrictMulAut_apply {W : Type*} [Group W] (F : Subgroup W) (f : MulAut W)
    (hf : ∀ x ∈ F, f x ∈ F) (hf' : ∀ x ∈ F, f⁻¹ x ∈ F) (x : ↥F) :
    ((restrictMulAut F f hf hf' x : ↥F) : W) = f x := rfl

private theorem restrictMulAut_pow_apply {W : Type*} [Group W] (F : Subgroup W) (f : MulAut W)
    (hf : ∀ x ∈ F, f x ∈ F) (hf' : ∀ x ∈ F, f⁻¹ x ∈ F) (n : ℕ) (x : ↥F) :
    (((restrictMulAut F f hf hf' ^ n) x : ↥F) : W) = (f ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, restrictMulAut_apply, ih, pow_succ', MulAut.mul_apply]

theorem fix_of_commute_of_isKleinFour {W : Type*} [Group W] {F : Subgroup W} [IsKleinFour F]
    {f g : MulAut W} (hf : ∀ x ∈ F, f x ∈ F) (hf' : ∀ x ∈ F, f⁻¹ x ∈ F)
    (hg : ∀ x ∈ F, g x ∈ F) (hg' : ∀ x ∈ F, g⁻¹ x ∈ F) (hf3 : ∀ x ∈ F, (f ^ 3) x = x)
    (hg2 : ∀ x ∈ F, (g ^ 2) x = x) (hfg : ∀ x ∈ F, f (g x) = g (f x)) (hmove : ∃ x ∈ F, f x ≠ x) :
    ∀ x ∈ F, g x = x := by
  set f' := restrictMulAut F f hf hf'
  set g' := restrictMulAut F g hg hg'
  have hf'3 : f' ^ 3 = 1 := by
    ext x
    rw [restrictMulAut_pow_apply, hf3 x x.2]
    rfl
  have hg'2 : g' ^ 2 = 1 := by
    ext x
    rw [restrictMulAut_pow_apply, hg2 x x.2]
    rfl
  have hf'1 : f' ≠ 1 := by
    obtain ⟨x, hx, hfx⟩ := hmove
    intro h
    apply hfx
    have := congrArg (fun k : MulAut ↥F => ((k ⟨x, hx⟩ : ↥F) : W)) h
    simpa only [f', restrictMulAut_apply, MulAut.one_apply] using this
  have hcomm : f' * g' = g' * f' := by
    ext x
    exact hfg x x.2
  have h1 := mulAut_eq_one_of_commute_of_isKleinFour hf'3 hf'1 hg'2 hcomm
  intro x hx
  have := congrArg (fun k : MulAut ↥F => ((k ⟨x, hx⟩ : ↥F) : W)) h1
  simpa only [g', restrictMulAut_apply, MulAut.one_apply] using this

theorem fix_or_of_cube_of_isKleinFour {W : Type*} [Group W] {F : Subgroup W} [IsKleinFour F]
    {f g : MulAut W} (hf : ∀ x ∈ F, f x ∈ F) (hf' : ∀ x ∈ F, f⁻¹ x ∈ F)
    (hg : ∀ x ∈ F, g x ∈ F) (hg' : ∀ x ∈ F, g⁻¹ x ∈ F) (hf3 : ∀ x ∈ F, (f ^ 3) x = x)
    (hg3 : ∀ x ∈ F, (g ^ 3) x = x) :
    (∀ x ∈ F, f x = x) ∨ (∀ x ∈ F, g x = x) ∨ (∀ x ∈ F, (f * g) x = x) ∨
      (∀ x ∈ F, (f * g * g) x = x) := by
  set f' := restrictMulAut F f hf hf'
  set g' := restrictMulAut F g hg hg'
  have hf'3 : f' ^ 3 = 1 := by
    ext x
    rw [restrictMulAut_pow_apply, hf3 x x.2]
    rfl
  have hg'3 : g' ^ 3 = 1 := by
    ext x
    rw [restrictMulAut_pow_apply, hg3 x x.2]
    rfl
  have hfix : ∀ k : MulAut ↥F, k = 1 → ∀ x (hx : x ∈ F), ((k ⟨x, hx⟩ : ↥F) : W) = x := by
    intro k hk x hx
    rw [hk]
    rfl
  rcases mulAut_eq_one_or_of_isKleinFour hf'3 hg'3 with h | h | h | h
  · exact Or.inl fun x hx => hfix _ h x hx
  · exact Or.inr (Or.inl fun x hx => hfix _ h x hx)
  · exact Or.inr (Or.inr (Or.inl fun x hx => hfix _ h x hx))
  · exact Or.inr (Or.inr (Or.inr fun x hx => hfix _ h x hx))

variable {G : Type} [Group G] [Finite G] {z : G}

theorem isExtraspecial2_CJ_of_card_ne_two (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {x : ↥(H z)} (hx : orderOf x = 3)
    (hne2 : Nat.card (CJ z (x : G)) ≠ 2) : IsExtraspecial2 (CJ z (x : G)) := by
  have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hB3 : IsPGroup 3 (Subgroup.zpowers (x : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxG, pow_one])
  have hBne : Subgroup.zpowers (x : G) ≠ ⊥ := by
    intro hbot
    have hmem : (x : G) ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers _
    rw [Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hxG
    norm_num at hxG
  have hprop := prop5_centralizer Nat.prime_three (by norm_num)
    (H := G) (J := J z) (P := Subgroup.zpowers (x : G)) hJ hB3 hBne (zpowers_le_normalizer_J x)
  have hCP : J z ⊓ Subgroup.centralizer (Subgroup.zpowers (x : G) : Set G) = CJ z (x : G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, inf_comm]
    rfl
  rcases hprop with hE | hE
  · rwa [hCP] at hE
  · exfalso
    rw [hCP] at hE
    apply hne2
    rw [hE, Subgroup.card_map_of_injective (J z).subtype_injective, card_center_J hJ hcomm]

theorem isKleinFour_of_card_eq_four_V (hJ : IsExtraspecial2 (J z))
    {F : Subgroup (QuotientV.V z)} (h4 : Nat.card F = 4) : IsKleinFour F := by
  have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [h4]; norm_num)
  refine ⟨h4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun v hv => ?_⟩
  exact orderOf_eq_prime (Subtype.ext (pow_two_eq_one_V hJ (v : QuotientV.V z))) hv

theorem two_mul_card_map_pi_of_le_J (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {K : Subgroup G} (hKJ : K ≤ J z) (hzK : z ∈ K) :
    2 * Nat.card ↥((K.subgroupOf (J z)).map (QuotientV.pi z)) = Nat.card K := by
  have h := Subgroup.card_ker_mul_card_range ((QuotientV.pi z).comp (K.subgroupOf (J z)).subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hker : ((QuotientV.pi z).comp (K.subgroupOf (J z)).subtype).ker =
      ((Subgroup.zpowers z).subgroupOf (J z)).subgroupOf (K.subgroupOf (J z)) := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, ← MonoidHom.mem_ker, QuotientV.pi_ker, Subgroup.mem_subgroupOf,
      centerIn_J_eq_zpowers hJ hcomm]
    rfl
  have hcard2 : Nat.card ((QuotientV.pi z).comp (K.subgroupOf (J z)).subtype).ker = 2 := by
    rw [hker]
    have hle : (Subgroup.zpowers z).subgroupOf (J z) ≤ K.subgroupOf (J z) := by
      intro k hk
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk
      rw [← hn]
      exact K.zpow_mem hzK n
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le_of_mem
        (z_mem_J hcomm))).toEquiv, Nat.card_zpowers, orderOf_z hJ hcomm]
  rw [hcard2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv] at h
  exact h

theorem commutator_CJ_eq_zpowers (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {x : ↥(H z)} (hP : IsExtraspecial2 (CJ z (x : G))) :
    ⁅CJ z (x : G), CJ z (x : G)⁆ = Subgroup.zpowers z := by
  have hzc : z ∈ ⁅CJ z (x : G), CJ z (x : G)⁆ := by
    rw [hP.2.1]
    refine ⟨⟨z, z_mem_CJ hcomm _⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgH : (g : G) ∈ H z := J_le_H (mem_CJ.mp g.2).2
    exact Subgroup.mem_centralizer_singleton_iff.mp hgH
  have hcZ : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_z hJ hcomm]
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hzc)
    (by rw [hP.2.2, hcZ])).symm

private theorem map_conj_eq_of_mem_J (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    {Q : Subgroup G} (hQJ : Q ≤ J z) (hzQ : z ∈ Q) {j : G} (hj : j ∈ J z) :
    Q.map (MulAut.conj j).toMonoidHom = Q := by
  have hle : Q.map (MulAut.conj j).toMonoidHom ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hcq : j * q * j⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator hj (hQJ hq)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcq
    have : j * q * j⁻¹ = z ^ n * q := by rw [hn]; group
    rw [this]
    exact Q.mul_mem (Q.zpow_mem hzQ n) hq
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj j).injective])

section Model


set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup)

private theorem nonEq_facts (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    orderOf σ₁ = 3 ∧ fixDimV hcomm hJ σ₁ = 2 ∧ fixDimV hcomm hJ σ₂ = 2 ∧
      σ₂ ∉ Subgroup.zpowers σ₁ ∧
      fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers σ₁ ⊔ Subgroup.zpowers σ₂) = ⊥ ∧
      fixDimV hcomm hJ (σ₁ * σ₂⁻¹) = 4 := by
  let _ : CommGroup (QuotientV.V z) := commGroupV hcomm
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have h2₁ : fixDimV hcomm hJ σ₁ = 2 := fixDimV_eq_two_of_cube hJ hcard hcomm hCHJ hy hyσ
  have h2₂ : fixDimV hcomm hJ σ₂ = 2 := by rw [← hu, fixDimV_conj, h2₁]
  have h8₁ : Nat.card (CJ z (σ₁ : G)) = 8 := by
    rw [card_CJ_eq_two_mul hJ hcard hcomm h3₁, h2₁]
    norm_num
  have h8₂ : Nat.card (CJ z (σ₂ : G)) = 8 := by
    rw [card_CJ_eq_two_mul hJ hcard hcomm h3₂, h2₂]
    norm_num
  have hCJ := CJ_inf_CJ_eq_zpowers hJ hcomm h3₂ hc h8₁ h8₂ hne
  have hE : fixedSpace (conjVRepresentation hcomm hJ)
      (Subgroup.zpowers σ₁ ⊔ Subgroup.zpowers σ₂) = ⊥ :=
    invariants_zpowers_sup_eq_bot hJ hcomm h3₁ h3₂ hCJ
  have hnot : σ₂ ∉ Subgroup.zpowers σ₁ := by
    intro h
    apply hne
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    have hle : CJ z (σ₁ : G) ≤ CJ z (((σ₁ ^ k : ↥(H z))) : G) := by
      intro g hg
      rw [mem_CJ] at hg ⊢
      refine ⟨?_, hg.2⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      rw [SubgroupClass.coe_zpow]
      exact ((show Commute g (σ₁ : G) from hg.1).zpow_right k).eq
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h8₁, h8₂])
  exact ⟨h3₁, h2₁, h2₂, hnot, hE,
    fixDimV_sigma1_mul_sigma2_inv_eq_four hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ hy hyσ⟩

omit [Finite G] in
private theorem orderOf_mul_inv_eq_three {σ₁ σ₂ : ↥(H z)} (h3₁ : orderOf σ₁ = 3)
    (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂) (hnot : σ₂ ∉ Subgroup.zpowers σ₁) :
    orderOf (σ₁ * σ₂⁻¹) = 3 := by
  have hp1 : σ₁ ^ 3 = 1 := by rw [← h3₁]; exact pow_orderOf_eq_one σ₁
  have hp2 : σ₂ ^ 3 = 1 := by rw [← h3₂]; exact pow_orderOf_eq_one σ₂
  refine orderOf_eq_prime ?_ fun h => hnot ?_
  · rw [hc.inv_right.mul_pow, inv_pow, hp1, hp2, inv_one, one_mul]
  · rw [← mul_inv_eq_one.mp h]
    exact Subgroup.mem_zpowers σ₁

theorem card_CJ_sigma1_mul_sigma2_inv_eq (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    orderOf (σ₁ * σ₂⁻¹) = 3 ∧ Nat.card (CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G)) = 32 := by
  obtain ⟨h3₁, -, -, hnot, -, h4⟩ :=
    nonEq_facts hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ hu
  have hs3 := orderOf_mul_inv_eq_three h3₁ h3₂ hc hnot
  refine ⟨hs3, ?_⟩
  rw [card_CJ_eq_two_mul hJ hcard hcomm hs3, h4]
  norm_num

theorem CJ_inf_CJ_sigma1_mul_sigma2_inv_eq (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    CJ z (σ₁ : G) ⊓ CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) = Subgroup.zpowers z := by
  let _ : CommGroup (QuotientV.V z) := commGroupV hcomm
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  obtain ⟨h3₁, -, -, hnot, hE, -⟩ :=
    nonEq_facts hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ hu
  have hind := iSupIndep_fixedSpace_of_fixedSpace_eq_bot (conjVRepresentation hcomm hJ)
    h3₁ h3₂ hc hnot hE
  have hdisj : Disjoint (fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers σ₁))
      (fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers (σ₁ * σ₂⁻¹))) :=
    hind.pairwiseDisjoint (show (0 : Fin 4) ≠ 3 by decide)
  have hfs : ∀ g : ↥(H z), fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g) =
      fixSubmodule hcomm hJ g := fun g => invariants_zpowers_eq_fixSubmodule hcomm hJ g
  rw [hfs, hfs] at hdisj
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxJ : x ∈ J z := (mem_CJ.mp hx1).2
    let j : J z := ⟨x, hxJ⟩
    have hfix : ∀ σ : ↥(H z), x ∈ CJ z (σ : G) →
        Additive.ofMul (QuotientV.pi z j) ∈ fixSubmodule hcomm hJ σ := by
      intro σ hxσ
      rw [mem_fixSubmodule_iff, mem_autFixedSubgroup]
      change conjVA z σ (QuotientV.pi z j) = QuotientV.pi z j
      rw [conjVA_mk]
      congr 1
      apply Subtype.ext
      rw [conjJ'_apply_coe]
      have hc' := Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hxσ).1
      change (σ : G) * x * (σ : G)⁻¹ = x
      rw [← hc']
      group
    have h0 := Submodule.disjoint_def.mp hdisj _ (hfix σ₁ hx1) (hfix _ hx2)
    have hpi : QuotientV.pi z j = 1 := h0
    have hker' : j ∈ (QuotientV.pi z).ker := MonoidHom.mem_ker.mpr hpi
    rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at hker'
    rw [← centerIn_J_eq_zpowers hJ hcomm]
    exact hker'
  · exact Subgroup.zpowers_le_of_mem ⟨z_mem_CJ hcomm σ₁, z_mem_CJ hcomm _⟩

theorem exists_quaternion_pair_CJ_sigma1_mul_sigma2_inv_of (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    ∃ Q₁ Q₂ : Subgroup G, Q₁ ⊔ Q₂ = CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) ∧
      Q₁ ⊓ Q₂ = Subgroup.zpowers z ∧ (∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) ∧
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) ∧ Nonempty (↥Q₂ ≃* QuaternionGroup 2) ∧
      (σ₁ : G) ∈ Subgroup.normalizer (Q₁ : Set G) ∧
      (σ₁ : G) ∈ Subgroup.normalizer (Q₂ : Set G) := by
  obtain ⟨h3₁, -, -, -, -, -⟩ :=
    nonEq_facts hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ hu
  obtain ⟨hs3, h32⟩ :=
    card_CJ_sigma1_mul_sigma2_inv_eq hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ hu
  have hinf := CJ_inf_CJ_sigma1_mul_sigma2_inv_eq hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc
    hne hy hyσ hu
  set P := CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) with hPdef
  have hP : IsExtraspecial2 P :=
    isExtraspecial2_CJ_of_card_ne_two hJ hcomm hs3 (by rw [h32]; norm_num)
  have hPP : ⁅P, P⁆ = Subgroup.zpowers z := commutator_CJ_eq_zpowers hJ hcomm hP
  have hcs : Commute (σ₁ * σ₂⁻¹) σ₁ := (Commute.refl σ₁).mul_left hc.inv_right.symm
  have hσP : (σ₁ : G) ∈ Subgroup.normalizer (P : Set G) := mem_normalizer_CJ_of_commute hcs
  have hfix : ∀ x ∈ P, (σ₁ : G) * x * (σ₁ : G)⁻¹ = x → x ∈ ⁅P, P⁆ := by
    intro x hx hσx
    rw [hPP, ← hinf]
    refine Subgroup.mem_inf.mpr ⟨?_, hx⟩
    rw [mem_CJ]
    refine ⟨?_, (mem_CJ.mp hx).2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (σ₁ : G) = (σ₁ : G) * x * (σ₁ : G)⁻¹ * (σ₁ : G) := by rw [hσx]
      _ = (σ₁ : G) * x := by group
  obtain ⟨Q₁, Q₂, -, -, hsup, hQinf, hQc, hQ₁, hQ₂, hN₁, hN₂⟩ :=
    exists_quaternion_pair_of_fixedPointFree hP h32 (by rw [Subgroup.orderOf_coe, h3₁]) hσP hfix
  exact ⟨Q₁, Q₂, hsup, hQinf.trans hPP, hQc, hQ₁, hQ₂, hN₁, hN₂⟩

theorem exists_lift_t_commute_of (hcard : Nat.card (J z) = 2 ^ 9)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₁ : orderOf σ₁ = 3) (h3₂ : orderOf σ₂ = 3)
    (hc : Commute σ₁ σ₂) :
    ∃ t' : ↥(H z), φ t' = tA ∧ Commute t' σ₁ ∧ Commute t' σ₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := isPGroup_ker_of_ker_eq hcard φ hker
  have hker3 : ∀ S : Subgroup ↥(H z), ¬ 3 ∣ Nat.card ↥(φ.ker ⊓ S) := by
    intro S h
    obtain ⟨n, hn⟩ := (h2.to_le inf_le_left).exists_card_eq
    rw [hn] at h
    have h3 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h3
  have hP1 : IsPGroup 3 (Subgroup.zpowers σ₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3₁, pow_one])
  have hP2 : IsPGroup 3 (Subgroup.zpowers σ₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3₂, pow_one])
  have htc : ∀ (σ : ↥(H z)) (y : Equiv.Perm (Fin 45)) (hy : y ∈ QA45.originalSubgroup),
      φ σ = ⟨y, hy⟩ → t * y = y * t → ∀ g ∈ Subgroup.zpowers σ, φ g * tA = tA * φ g := by
    intro σ y hy hσ hty g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [map_zpow, hσ]
    apply Commute.eq
    apply Commute.zpow_left
    exact Subtype.ext hty.symm
  obtain ⟨m₀, hm₀⟩ : tA ∈ φ.range := hQP (show tA ∈ QP45.originalSubgroup.subgroupOf
    QA45.originalSubgroup from t_mem_Q)
  obtain ⟨x₁, -, hx₁, hx₁σ⟩ := exists_commute_mem_fibre φ (S := ⊤) hP1 le_top (hker3 ⊤)
    (Subgroup.mem_top m₀) (by rw [hm₀]; exact htc σ₁ sigma1 sigma1_mem_A hσ₁ t_commute_sigma1)
  have hx₁C : x₁ ∈ Subgroup.centralizer ({σ₁} : Set ↥(H z)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx₁σ σ₁ (Subgroup.mem_zpowers _)).symm
  have hP2C : Subgroup.zpowers σ₂ ≤ Subgroup.centralizer ({σ₁} : Set ↥(H z)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hc.eq.symm
  obtain ⟨x, hxC, hx, hxσ⟩ := exists_commute_mem_fibre φ hP2 hP2C (hker3 _) hx₁C
    (by rw [hx₁, hm₀]; exact htc σ₂ sigma2 sigma2_mem_A hσ₂ t_commute_sigma2)
  refine ⟨x, hx.trans (hx₁.trans hm₀), ?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mp hxC
  · exact (hxσ σ₂ (Subgroup.mem_zpowers _)).symm

theorem mem_J_of_conjVA_eq_one (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (h3₁ : orderOf σ₁ = 3) {x : ↥(H z)}
    (hxP : φ x ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    (hx : conjVA z x = 1) : (x : G) ∈ J z := by
  have : IsSimpleGroup ↥QP45.originalSubgroup := isSimpleGroup_QP45_of_model
  have : IsSimpleGroup ↥(QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) :=
    MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe QP45_le_QA45)
  have hNn : (((conjVA z).ker.map φ).subgroupOf
      (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)).Normal := by
    constructor
    intro n hn p
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk, hkn⟩ := Subgroup.mem_map.mp hn
    obtain ⟨h, hh⟩ := hQP p.2
    refine Subgroup.mem_map.mpr ⟨h * k * h⁻¹, ?_, ?_⟩
    · rw [MonoidHom.mem_ker] at hk ⊢
      rw [map_mul, map_mul, map_inv, hk, mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv, hkn, hh]
      rfl
  by_contra hxJ
  have hφx : φ x ≠ 1 := by
    intro h1
    apply hxJ
    have h' : x ∈ φ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h'
    exact h'
  have hxN : (⟨φ x, hxP⟩ : ↥(QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)) ∈
      ((conjVA z).ker.map φ).subgroupOf
        (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (((conjVA z).ker.map φ).subgroupOf
      (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)) with hbot | htop
  · rw [hbot, Subgroup.mem_bot] at hxN
    exact hφx (congrArg Subtype.val hxN)
  · have hs1P : s1A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
      Subgroup.mem_subgroupOf.mpr sigma1_mem_Q
    have hs1 : (⟨s1A, hs1P⟩ : ↥(QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)) ∈
        ((conjVA z).ker.map φ).subgroupOf
          (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hs1
    obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp hs1
    have h' : conjVA z σ₁ = conjVA z k := conjVA_eq_of_map_eq hcomm φ hker (by rw [hσ₁, hks])
    exact conjVA_ne_one_of_order_three hJ hcomm hCHJ h3₁ (h'.trans hk)

theorem map_conj_t_quaternion_pair_of (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) {t' : ↥(H z)} (ht' : φ t' = tA)
    {Q₁ Q₂ : Subgroup G} (hQ : Q₁ ⊔ Q₂ = CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G))
    (hQi : Q₁ ⊓ Q₂ = Subgroup.zpowers z) (hQc : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (hQ₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (hQ₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2)) :
    Q₁.map (MulAut.conj (t' : G)).toMonoidHom = Q₂ := by
  let _ : CommGroup (QuotientV.V z) := commGroupV hcomm
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  obtain ⟨h3₁, h2₁, h2₂, hnot, hE, h4⟩ :=
    nonEq_facts hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ hu
  obtain ⟨hs3, h32⟩ :=
    card_CJ_sigma1_mul_sigma2_inv_eq hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ hu
  set P := CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) with hPdef
  have hP : IsExtraspecial2 P :=
    isExtraspecial2_CJ_of_card_ne_two hJ hcomm hs3 (by rw [h32]; norm_num)
  have hPP : ⁅P, P⁆ = Subgroup.zpowers z := commutator_CJ_eq_zpowers hJ hcomm hP
  have hQinf : Q₁ ⊓ Q₂ = ⁅P, P⁆ := hQi.trans hPP.symm
  have hQ₁P : Q₁ ≤ P := hQ ▸ le_sup_left
  have hQ₂P : Q₂ ≤ P := hQ ▸ le_sup_right
  have hPJ : P ≤ J z := inf_le_right
  have hzQ₁ : z ∈ Q₁ := (hQi ▸ inf_le_left : Subgroup.zpowers z ≤ Q₁) (Subgroup.mem_zpowers z)
  have hzQ₂ : z ∈ Q₂ := (hQi ▸ inf_le_right : Subgroup.zpowers z ≤ Q₂) (Subgroup.mem_zpowers z)
  have hQne : Q₁ ≠ Q₂ := by
    intro h
    have h8 : Nat.card Q₁ = 8 := by
      obtain ⟨e⟩ := hQ₁
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have h2 : Nat.card ↥(Q₁ ⊓ Q₂) = 2 := by rw [hQi, Nat.card_zpowers, orderOf_z hJ hcomm]
    rw [← h, inf_idem, h8] at h2
    norm_num at h2
  have hconj_mem : ∀ {g : G}, g ∈ Subgroup.normalizer (P : Set G) → ∀ {Q : Subgroup G},
      Q ≤ P → Nonempty (↥Q ≃* QuaternionGroup 2) →
        Q.map (MulAut.conj g).toMonoidHom = Q₁ ∨ Q.map (MulAut.conj g).toMonoidHom = Q₂ := by
    intro g hg Q hQP' hQq
    refine eq_or_eq_of_quaternion_of_fixedPointFree hQ hQinf hQc hQ₁ hQ₂ ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg q).mp (hQP' hq)
    · obtain ⟨e⟩ := hQq
      exact ⟨((Q.equivMapOfInjective _ (MulAut.conj g).injective).symm).trans e⟩
  obtain ⟨t₀, ht₀, hct₁, hct₂⟩ :=
    exists_lift_t_commute_of hcard φ hker hQP hσ₁ hσ₂ h3₁ h3₂ hc
  have hcts : Commute (σ₁ * σ₂⁻¹) t₀ := (hct₁.symm.mul_left hct₂.symm.inv_left)
  have ht₀P : (t₀ : G) ∈ Subgroup.normalizer (P : Set G) := mem_normalizer_CJ_of_commute hcts
  have ht₀sq : (conjVA z t₀) ^ 2 = 1 := by
    have hmem : t₀ ^ 2 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ht₀]
      apply Subtype.ext
      simp [pow_two, t_sq]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    rw [← map_pow]
    exact conjVA_eq_one_of_mem_J hcomm hmem
  have hpow3 : ∀ σ : ↥(H z), orderOf σ = 3 → (conjVA z σ) ^ 3 = 1 := fun σ hσ => by
    rw [← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  have hind := iSupIndep_fixedSpace_of_fixedSpace_eq_bot (conjVRepresentation hcomm hJ)
    h3₁ h3₂ hc hnot hE
  have hfs : ∀ g : ↥(H z), fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g) =
      fixSubmodule hcomm hJ g := fun g => invariants_zpowers_eq_fixSubmodule hcomm hJ g
  have hd12 : Disjoint (fixSubmodule hcomm hJ σ₁) (fixSubmodule hcomm hJ σ₂) := by
    have h : Disjoint (fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers σ₁))
        (fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers σ₂)) :=
      hind.pairwiseDisjoint (show (0 : Fin 4) ≠ 1 by decide)
    rwa [hfs, hfs] at h
  have hd14 : Disjoint (fixSubmodule hcomm hJ σ₁) (fixSubmodule hcomm hJ (σ₁ * σ₂⁻¹)) := by
    have h : Disjoint (fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers σ₁))
        (fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers (σ₁ * σ₂⁻¹))) :=
      hind.pairwiseDisjoint (show (0 : Fin 4) ≠ 3 by decide)
    rwa [hfs, hfs] at h
  have hzero : ∀ {a b : ↥(H z)}, Disjoint (fixSubmodule hcomm hJ a) (fixSubmodule hcomm hJ b) →
      ∀ v : QuotientV.V z, conjVA z a v = v → conjVA z b v = v → v = 1 := by
    intro a b hab v ha hb
    exact Submodule.disjoint_def.mp hab (Additive.ofMul v)
      ((mem_fixSubmodule_iff hcomm hJ a _).mpr (mem_autFixedSubgroup.mpr ha))
      ((mem_fixSubmodule_iff hcomm hJ b _).mpr (mem_autFixedSubgroup.mpr hb))
  have hmove : ∀ {F : Subgroup (QuotientV.V z)}, Nat.card F = 4 → ∀ {a : ↥(H z)},
      (∀ v ∈ F, conjVA z a v = v → v = 1) → ∃ v ∈ F, conjVA z a v ≠ v := by
    intro F h4 a htriv
    by_contra hcon
    push Not at hcon
    have hbot : F = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Subgroup.mem_bot]
      exact htriv v hv (hcon v hv)
    rw [hbot, Subgroup.card_bot] at h4
    norm_num at h4
  have hF4 : ∀ {σ : ↥(H z)}, fixDimV hcomm hJ σ = 2 →
      Nat.card ↥(autFixedSubgroup (conjVA z σ)) = 4 := by
    intro σ h2
    rw [card_fix hcomm hJ σ, h2]
    norm_num
  have hfixσ : ∀ {σ σ' : ↥(H z)}, Commute σ σ' → Commute t₀ σ → Commute t₀ σ' →
      orderOf σ' = 3 → fixDimV hcomm hJ σ = 2 →
      (∃ v ∈ autFixedSubgroup (conjVA z σ), conjVA z σ' v ≠ v) →
      ∀ v ∈ autFixedSubgroup (conjVA z σ), conjVA z t₀ v = v := by
    intro σ σ' hσσ' htσ htσ' h3σ' h2σ hmove
    have := isKleinFour_autFixedSubgroup hcomm hJ h2σ
    refine fix_of_commute_of_isKleinFour (f := conjVA z σ') (g := conjVA z t₀)
      (fun x hx => conjVA_mem_autFixedSubgroup hσσ' hx)
      (fun x hx => by rw [← map_inv]; exact conjVA_mem_autFixedSubgroup hσσ'.inv_right hx)
      (fun x hx => conjVA_mem_autFixedSubgroup htσ.symm hx)
      (fun x hx => by rw [← map_inv]; exact conjVA_mem_autFixedSubgroup htσ.symm.inv_right hx)
      (fun x _ => by rw [hpow3 σ' h3σ']; rfl) (fun x _ => by rw [ht₀sq]; rfl)
      (fun x _ => by rw [← MulAut.mul_apply, ← map_mul, ← htσ'.eq, map_mul, MulAut.mul_apply])
      hmove
  have hfix₁ : ∀ v ∈ autFixedSubgroup (conjVA z σ₁), conjVA z t₀ v = v :=
    hfixσ hc hct₁ hct₂ h3₂ h2₁ (hmove (hF4 h2₁) fun v hv h => hzero hd12 v
      (mem_autFixedSubgroup.mp hv) h)
  have hfix₂ : ∀ v ∈ autFixedSubgroup (conjVA z σ₂), conjVA z t₀ v = v :=
    hfixσ hc.symm hct₂ hct₁ h3₁ h2₂ (hmove (hF4 h2₂) fun v hv h => hzero hd12 v h
      (mem_autFixedSubgroup.mp hv))
  obtain ⟨Q₁', Q₂', hQ', hQi', hQc', hQ₁', hQ₂', hN₁', hN₂'⟩ :=
    exists_quaternion_pair_CJ_sigma1_mul_sigma2_inv_of hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂
      hc hne hy hyσ hu
  have hσN : ∀ {Q : Subgroup G}, Q ≤ P → Nonempty (↥Q ≃* QuaternionGroup 2) →
      (σ₁ : G) ∈ Subgroup.normalizer (Q : Set G) := by
    intro Q hQP' hQq
    rcases eq_or_eq_of_quaternion_of_fixedPointFree hQ' (hQi'.trans hPP.symm) hQc' hQ₁' hQ₂'
      hQP' hQq with h | h
    · rw [h]; exact hN₁'
    · rw [h]; exact hN₂'
  have hnorm_of_map : ∀ {g : G} {Q : Subgroup G}, Q.map (MulAut.conj g).toMonoidHom = Q →
      g ∈ Subgroup.normalizer (Q : Set G) := by
    intro g Q h
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      rw [← h]
      exact ⟨q, hq, rfl⟩
    · intro hq
      rw [← h] at hq
      obtain ⟨q', hq', hqq'⟩ := hq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqq'
      have : q' = q := mul_left_cancel (mul_right_cancel hqq')
      rw [← this]
      exact hq'
  have hfixQ : ∀ {Q : Subgroup G}, Q ≤ P → Nonempty (↥Q ≃* QuaternionGroup 2) →
      Q.map (MulAut.conj (t₀ : G)).toMonoidHom = Q →
      ∀ w ∈ (Q.subgroupOf (J z)).map (QuotientV.pi z), conjVA z t₀ w = w := by
    intro Q hQP' hQq hQt w hw
    have hQJ : Q ≤ J z := hQP'.trans hPJ
    have hzQ : z ∈ Q := by
      rcases eq_or_eq_of_quaternion_of_fixedPointFree hQ hQinf hQc hQ₁ hQ₂ hQP' hQq with h | h
      · rw [h]; exact hzQ₁
      · rw [h]; exact hzQ₂
    have h8 : Nat.card Q = 8 := by
      obtain ⟨e⟩ := hQq
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have h4 : Nat.card ↥((Q.subgroupOf (J z)).map (QuotientV.pi z)) = 4 := by
      have := two_mul_card_map_pi_of_le_J hJ hcomm hQJ hzQ
      omega
    have := isKleinFour_of_card_eq_four_V hJ h4
    have hmaps : ∀ {g : ↥(H z)}, (g : G) ∈ Subgroup.normalizer (Q : Set G) →
        ∀ x ∈ (Q.subgroupOf (J z)).map (QuotientV.pi z),
          conjVA z g x ∈ (Q.subgroupOf (J z)).map (QuotientV.pi z) := by
      intro g hg x hx
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
      rw [conjVA_mk]
      refine Subgroup.mem_map.mpr ⟨conjJ' z g j, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hj ⊢
      rw [conjJ'_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp hj
    have hσ₁QN := hσN hQP' hQq
    have ht₀QN := hnorm_of_map hQt
    refine fix_of_commute_of_isKleinFour (f := conjVA z σ₁) (g := conjVA z t₀)
      (hmaps hσ₁QN) (fun x hx => by
        rw [← map_inv]
        exact hmaps (g := σ₁⁻¹) (inv_mem hσ₁QN) x hx)
      (hmaps ht₀QN) (fun x hx => by
        rw [← map_inv]
        exact hmaps (g := t₀⁻¹) (inv_mem ht₀QN) x hx)
      (fun x _ => by rw [hpow3 σ₁ h3₁]; rfl) (fun x _ => by rw [ht₀sq]; rfl)
      (fun x _ => by rw [← MulAut.mul_apply, ← map_mul, ← hct₁.eq, map_mul, MulAut.mul_apply])
      (hmove h4 fun v hv h => hzero hd14 v h ?_) w hw
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hv
    rw [conjVA_mk]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hjP : (j : G) ∈ P := hQP' (Subgroup.mem_subgroupOf.mp hj)
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hjP).1
    rw [← hc']
    group
  have hswap : Q₁.map (MulAut.conj (t₀ : G)).toMonoidHom = Q₂ := by
    rcases hconj_mem ht₀P hQ₁P hQ₁ with h1 | h1
    · exfalso
      have h2 : Q₂.map (MulAut.conj (t₀ : G)).toMonoidHom = Q₂ := by
        rcases hconj_mem ht₀P hQ₂P hQ₂ with h2 | h2
        · exact absurd (Subgroup.map_injective (MulAut.conj (t₀ : G)).injective
            (h2.trans h1.symm)) (Ne.symm hQne)
        · exact h2
      have hfQ₁ := hfixQ hQ₁P hQ₁ h1
      have hfQ₂ := hfixQ hQ₂P hQ₂ h2
      have hd0 : fixSubmodule hcomm hJ (σ₁ * σ₂) = ⊥ := by
        have h0 := (fixDimV_sigma1_mul_sigma2_eq_zero hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂
          hc hne hy hyσ hu).2
        exact Submodule.finrank_eq_zero.mp h0
      have hle : fixSubmodule hcomm hJ σ₁ ⊔ fixSubmodule hcomm hJ σ₂ ⊔
          fixSubmodule hcomm hJ (σ₁ * σ₂) ⊔ fixSubmodule hcomm hJ (σ₁ * σ₂⁻¹) ≤
            fixSubmodule hcomm hJ t₀ := by
        have hlift : ∀ {σ : ↥(H z)}, (∀ v ∈ autFixedSubgroup (conjVA z σ), conjVA z t₀ v = v) →
            fixSubmodule hcomm hJ σ ≤ fixSubmodule hcomm hJ t₀ := by
          intro σ hσ w hw
          rw [mem_fixSubmodule_iff] at hw ⊢
          exact mem_autFixedSubgroup.mpr (hσ _ hw)
        refine sup_le (sup_le (sup_le (hlift hfix₁) (hlift hfix₂)) (by rw [hd0]; exact bot_le))
          (hlift ?_)
        intro v hv
        obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
        have hj : j ∈ centralizerJ (σ₁ * σ₂⁻¹) :=
          mem_centralizerJ_of_conjVA_pi_eq hJ hcomm (by rw [← hs3]; exact pow_orderOf_eq_one _)
            (mem_autFixedSubgroup.mp hv)
        have hjP : (j : G) ∈ P :=
          mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp hj), j.2⟩
        rw [← hQ, CFSG.mem_sup_of_commute (fun a ha b hb => hQc a ha b hb)] at hjP
        obtain ⟨q₁, hq₁, q₂, hq₂, hq⟩ := hjP
        have hq₁J : q₁ ∈ J z := hPJ (hQ₁P hq₁)
        have hq₂J : q₂ ∈ J z := hPJ (hQ₂P hq₂)
        have hjeq : j = ⟨q₁, hq₁J⟩ * ⟨q₂, hq₂J⟩ := Subtype.ext hq.symm
        rw [hjeq, map_mul, map_mul]
        rw [hfQ₁ _ (Subgroup.mem_map.mpr ⟨⟨q₁, hq₁J⟩, Subgroup.mem_subgroupOf.mpr hq₁, rfl⟩),
          hfQ₂ _ (Subgroup.mem_map.mpr ⟨⟨q₂, hq₂J⟩, Subgroup.mem_subgroupOf.mpr hq₂, rfl⟩)]
      have htop := sup_fixedSpace_eq_top (conjVRepresentation hcomm hJ) h3₁ h3₂ hc hnot
      rw [hfs, hfs, hfs, hfs] at htop
      have hV : conjVA z t₀ = 1 := by
        apply MulEquiv.ext
        intro v
        rw [MulAut.one_apply]
        have hv : Additive.ofMul v ∈ fixSubmodule hcomm hJ t₀ :=
          hle (htop ▸ Submodule.mem_top)
        exact mem_autFixedSubgroup.mp ((mem_fixSubmodule_iff hcomm hJ t₀ _).mp hv)
      have hJt := mem_J_of_conjVA_eq_one hJ hcomm hCHJ φ hker hQP hσ₁ h3₁
        (by rw [ht₀]; exact Subgroup.mem_subgroupOf.mpr t_mem_Q) hV
      have hker' : t₀ ∈ φ.ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        exact hJt
      rw [MonoidHom.mem_ker, ht₀] at hker'
      exact t_ne_one (congrArg Subtype.val hker')
    · exact h1
  have hj : ((t₀⁻¹ * t' : ↥(H z)) : G) ∈ J z := by
    have h' : t₀⁻¹ * t' ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ht₀, ht', inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at h'
    exact h'
  have hcomp : (MulAut.conj (t' : G)).toMonoidHom = (MulAut.conj (t₀ : G)).toMonoidHom.comp
      (MulAut.conj ((t₀⁻¹ * t' : ↥(H z)) : G)).toMonoidHom := by
    ext g
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply,
      Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hcomp, ← Subgroup.map_map, map_conj_eq_of_mem_J hcomm (hQ₁P.trans hPJ) hzQ₁ hj, hswap]

end Model

end CFSG.RankThree.GF2n.Parrott.Remarks
