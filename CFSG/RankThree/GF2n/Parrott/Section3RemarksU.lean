module

public import CFSG.RankThree.GF2n.Parrott.Section3RemarksCJ
public import CFSG.RankThree.GF2n.Parrott.OThreeSigma
public import CFSG.GroupTheory.KleinFourAutomorphism
import CFSG.RankThree.GF2n.Parrott.Section3RemarksE9
import CFSG.RankThree.GF2n.Parrott.A1LocalData
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

theorem mulAut_eq_one_or_of_isKleinFour {E : Type*} [Group E] [IsKleinFour E] {f g : MulAut E}
    (hf : f ^ 3 = 1) (hg : g ^ 3 = 1) : f = 1 ∨ g = 1 ∨ f * g = 1 ∨ f * g * g = 1 := by
  have key : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 →
      a = 1 ∨ b = 1 ∨ a * b = 1 ∨ a * b * b = 1 := by decide +kernel
  let e := CFSG.kleinFourAutomorphismEquivSymmetricThree E
  have he : ∀ k : MulAut E, e k = 1 → k = 1 := fun k hk =>
    e.injective (hk.trans (map_one e).symm)
  rcases key (e f) (e g) (by rw [← map_pow, hf, map_one]) (by rw [← map_pow, hg, map_one]) with
    h | h | h | h
  · exact Or.inl (he f h)
  · exact Or.inr (Or.inl (he g h))
  · exact Or.inr (Or.inr (Or.inl (he _ (by rw [map_mul]; exact h))))
  · exact Or.inr (Or.inr (Or.inr (he _ (by rw [map_mul, map_mul]; exact h))))

variable {G : Type} [Group G] [Finite G] {z : G}

theorem conjVA_eq_one_of_mem_J (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {g : ↥(H z)}
    (hg : (g : G) ∈ J z) : conjVA z g = 1 := by
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
  rw [MulAut.one_apply]
  exact conjVA_apply_pi_eq hcomm hg x

theorem conjVA_eq_of_map_eq (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {Q : Type*} [Group Q]
    (φ : ↥(H z) →* Q) (hker : φ.ker = (J z).subgroupOf (H z)) {x y : ↥(H z)}
    (h : φ x = φ y) : conjVA z x = conjVA z y := by
  have hmem : x⁻¹ * y ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  have h1 := conjVA_eq_one_of_mem_J hcomm hmem
  rwa [map_mul, map_inv, inv_mul_eq_one] at h1

theorem fixDimV_eq_of_conjVA_eq (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) {x y : ↥(H z)} (h : conjVA z x = conjVA z y) :
    fixDimV hcomm hJ x = fixDimV hcomm hJ y := by
  have h1 := card_fix hcomm hJ x
  rw [h, card_fix hcomm hJ y] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

theorem fixDimV_conj (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) (hJ : IsExtraspecial2 (J z))
    (g x : ↥(H z)) : fixDimV hcomm hJ (g * x * g⁻¹) = fixDimV hcomm hJ x := by
  have hmap : autFixedSubgroup (conjVA z (g * x * g⁻¹)) =
      (autFixedSubgroup (conjVA z x)).map (conjVA z g).toMonoidHom := by
    ext v
    rw [mem_autFixedSubgroup, Subgroup.mem_map]
    rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply]
    constructor
    · intro hv
      refine ⟨(conjVA z g)⁻¹ v, ?_, MulAut.apply_inv_self _ _ _⟩
      rw [mem_autFixedSubgroup]
      calc (conjVA z x) ((conjVA z g)⁻¹ v)
          = (conjVA z g)⁻¹ ((conjVA z g) ((conjVA z x) ((conjVA z g)⁻¹ v))) :=
            (MulAut.inv_apply_self _ _ _).symm
        _ = (conjVA z g)⁻¹ v := by rw [hv]
    · rintro ⟨w, hw, rfl⟩
      rw [mem_autFixedSubgroup] at hw
      change (conjVA z g) ((conjVA z x) ((conjVA z g)⁻¹ ((conjVA z g) w))) = (conjVA z g) w
      rw [MulAut.inv_apply_self, hw]
  have h1 := card_fix hcomm hJ (g * x * g⁻¹)
  rw [hmap, Subgroup.card_map_of_injective (conjVA z g).injective, card_fix hcomm hJ x] at h1
  exact Nat.pow_right_injective (le_refl 2) h1.symm

theorem fixDimV_eq_of_map_conj (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) {Q : Type*} [Group Q] (φ : ↥(H z) →* Q)
    (hker : φ.ker = (J z).subgroupOf (H z)) {x y : ↥(H z)} {c : Q} (hc : c ∈ φ.range)
    (h : c * φ y * c⁻¹ = φ x) : fixDimV hcomm hJ x = fixDimV hcomm hJ y := by
  obtain ⟨g, rfl⟩ := hc
  have hxy : φ x = φ (g * y * g⁻¹) := by rw [map_mul, map_mul, map_inv, h]
  rw [fixDimV_eq_of_conjVA_eq hcomm hJ (conjVA_eq_of_map_eq hcomm φ hker hxy), fixDimV_conj]

theorem isPGroup_ker_of_ker_eq (hcard : Nat.card (J z) = 2 ^ 9) {Q : Type*} [Group Q]
    (φ : ↥(H z) →* Q) (hker : φ.ker = (J z).subgroupOf (H z)) : IsPGroup 2 φ.ker := by
  rw [hker]
  exact IsPGroup.of_card (n := 9)
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).toEquiv).trans hcard)

theorem exists_lift_commute_of_orderOf_eq_three (hcard : Nat.card (J z) = 2 ^ 9) {Q : Type*}
    [Group Q] (φ : ↥(H z) →* Q) (hker : φ.ker = (J z).subgroupOf (H z)) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) {q : Q} (hq : q ∈ φ.range) (hq3 : orderOf q = 3)
    (hqσ : q * φ σ = φ σ * q) : ∃ x : ↥(H z), φ x = q ∧ Commute σ x ∧ orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := isPGroup_ker_of_ker_eq hcard φ hker
  obtain ⟨m₀, rfl⟩ := hq
  have hP : IsPGroup 3 (Subgroup.zpowers σ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ, pow_one])
  have hker3 : ¬ 3 ∣ Nat.card ↥(φ.ker ⊓ ⊤) := by
    rw [inf_top_eq]
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    rw [hn]
    intro h
    have h3 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h3
  have hc : Commute (φ σ) (φ m₀) := hqσ.symm
  obtain ⟨m, -, hm, hmc⟩ := exists_commute_mem_fibre φ hP le_top hker3 (Subgroup.mem_top m₀)
    (fun g hg => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [map_zpow]
      exact (hc.zpow_left k).eq)
  obtain ⟨n, hn, hord⟩ :=
    exists_pow_lift_orderOf_eq φ h2 (by decide : Odd 3) (by norm_num) (by rw [hm]; exact hq3)
  refine ⟨m ^ n, by rw [hn, hm], ?_, hord⟩
  exact (show Commute σ m from hmc σ (Subgroup.mem_zpowers σ)).pow_right n

theorem conjVA_mem_autFixedSubgroup {σ h : ↥(H z)} (hh : Commute σ h) {v : QuotientV.V z}
    (hv : v ∈ autFixedSubgroup (conjVA z σ)) :
    conjVA z h v ∈ autFixedSubgroup (conjVA z σ) := by
  rw [mem_autFixedSubgroup] at hv ⊢
  rw [← MulAut.mul_apply, ← map_mul, hh.eq, map_mul, MulAut.mul_apply, hv]

private noncomputable def resFix (σ : ↥(H z)) :
    ↥(Subgroup.centralizer ({σ} : Set ↥(H z))) →*
      MulAut ↥(autFixedSubgroup (conjVA z σ)) where
  toFun h :=
    { toFun := fun v => ⟨conjVA z h v, conjVA_mem_autFixedSubgroup
        (Subgroup.mem_centralizer_singleton_iff.mp h.2).symm v.2⟩
      invFun := fun v => ⟨conjVA z (h⁻¹ : ↥(Subgroup.centralizer ({σ} : Set ↥(H z)))) v,
        conjVA_mem_autFixedSubgroup
          (Subgroup.mem_centralizer_singleton_iff.mp (h⁻¹).2).symm v.2⟩
      left_inv := fun v => Subtype.ext (by
        change conjVA z ((h : ↥(H z))⁻¹) (conjVA z h (v : QuotientV.V z)) = v
        rw [map_inv, MulAut.inv_apply_self])
      right_inv := fun v => Subtype.ext (by
        change conjVA z h (conjVA z ((h : ↥(H z))⁻¹) (v : QuotientV.V z)) = v
        rw [map_inv, MulAut.apply_inv_self])
      map_mul' := fun v w => Subtype.ext (map_mul (conjVA z h) (v : QuotientV.V z) w) }
  map_one' := by
    ext v
    change conjVA z ((1 : ↥(Subgroup.centralizer ({σ} : Set ↥(H z)))) : ↥(H z))
      (v : QuotientV.V z) = v
    rw [OneMemClass.coe_one, map_one, MulAut.one_apply]
  map_mul' h₁ h₂ := by
    ext v
    change conjVA z ((h₁ : ↥(H z)) * h₂) (v : QuotientV.V z) =
      conjVA z h₁ (conjVA z h₂ (v : QuotientV.V z))
    rw [map_mul, MulAut.mul_apply]

private theorem resFix_apply (σ : ↥(H z)) (h : ↥(Subgroup.centralizer ({σ} : Set ↥(H z))))
    (v : ↥(autFixedSubgroup (conjVA z σ))) :
    ((resFix σ h v : ↥(autFixedSubgroup (conjVA z σ))) : QuotientV.V z) = conjVA z h v := rfl

theorem isKleinFour_autFixedSubgroup (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) {σ : ↥(H z)} (h2 : fixDimV hcomm hJ σ = 2) :
    IsKleinFour ↥(autFixedSubgroup (conjVA z σ)) := by
  have h4 : Nat.card ↥(autFixedSubgroup (conjVA z σ)) = 4 := by
    rw [card_fix hcomm hJ σ, h2]
    norm_num
  have : Nontrivial ↥(autFixedSubgroup (conjVA z σ)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h4]; norm_num)
  refine ⟨h4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun v hv => ?_⟩
  exact orderOf_eq_prime (Subtype.ext (pow_two_eq_one_V hJ (v : QuotientV.V z))) hv

omit [Finite G] in
private theorem orderOf_mul_eq_three_of_not_mem {σ₁ σ₂ : ↥(H z)} (h3₁ : orderOf σ₁ = 3)
    (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂) (hnot : σ₂ ∉ Subgroup.zpowers σ₁) :
    orderOf (σ₁ * σ₂) = 3 := by
  have hp1 : σ₁ ^ 3 = 1 := by rw [← h3₁]; exact pow_orderOf_eq_one σ₁
  have hp2 : σ₂ ^ 3 = 1 := by rw [← h3₂]; exact pow_orderOf_eq_one σ₂
  refine orderOf_eq_prime (by rw [hc.mul_pow, hp1, hp2, one_mul]) fun h => hnot ?_
  rw [eq_inv_of_mul_eq_one_right h]
  exact Subgroup.inv_mem _ (Subgroup.mem_zpowers σ₁)

section Model


set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)

theorem exists_fix_sigma1_of_mem_O3 (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (h3₁ : orderOf σ₁ = 3) (h2 : fixDimV hcomm hJ σ₁ = 2) :
    ∃ x : ↥(H z), Commute σ₁ x ∧ orderOf x = 3 ∧ φ x ∈ oThreeSigmaQA45 ∧
      φ x ∉ Subgroup.zpowers s1A ∧
      ∀ v ∈ autFixedSubgroup (conjVA z σ₁), conjVA z x v = v := by
  have hUc : ∀ c ∈ Subgroup.zpowers s1A, ∀ u ∈ oThreeSigmaQA45, c * u = u * c := by
    intro c hc u hu
    rw [← oThreeSigmaQA45_inf_centralizer] at hc
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) u hu).symm
  obtain ⟨⟨a', haU⟩, ⟨b', hbU⟩, hab₀⟩ : ∃ a b : ↥oThreeSigmaQA45, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact not_isMulCommutative_oThreeSigmaQA45 (isMulCommutative_iff.mpr hcon)
  have hab : a' * b' ≠ b' * a' := fun h => hab₀ (Subtype.ext h)
  have hna : a' ∉ Subgroup.zpowers s1A := fun h => hab (hUc a' h b' hbU)
  have hnb : b' ∉ Subgroup.zpowers s1A := fun h => hab (hUc b' h a' haU).symm
  have hnab : a' * b' ∉ Subgroup.zpowers s1A := by
    intro h
    apply hab
    have hca := hUc _ h a' haU
    calc a' * b' = a'⁻¹ * (a' * (a' * b')) := by group
      _ = a'⁻¹ * ((a' * b') * a') := by rw [hca]
      _ = b' * a' := by group
  have hnabb : a' * b' * b' ∉ Subgroup.zpowers s1A := by
    intro h
    apply hab
    have hb3 : b' * b' * b' = 1 := by
      rw [← pow_three']
      exact pow_three_oThreeSigmaQA45 b' hbU
    have ha : a' = a' * b' * b' * b' := by
      calc a' = a' * (b' * b' * b') := by rw [hb3, mul_one]
        _ = a' * b' * b' * b' := by group
    have hcb := hUc _ h b' hbU
    rw [ha, ← mul_assoc b', ← hcb]
  have hUφ : ∀ u ∈ oThreeSigmaQA45, u ∈ φ.range := fun u hu => hQP (oThreeSigmaQA45_le_QP45 hu)
  have hUσ : ∀ u ∈ oThreeSigmaQA45, u * φ σ₁ = φ σ₁ * u := fun u hu => by
    rw [hσ₁]
    exact Subgroup.mem_centralizer_singleton_iff.mp (oThreeSigmaQA45_le_centralizer hu)
  have hord : ∀ u ∈ oThreeSigmaQA45, u ∉ Subgroup.zpowers s1A → orderOf u = 3 :=
    fun u hu hnu => orderOf_eq_prime (pow_three_oThreeSigmaQA45 u hu)
      (fun h1 => hnu (h1 ▸ Subgroup.one_mem _))
  obtain ⟨a, hφa, hca, ha3⟩ := exists_lift_commute_of_orderOf_eq_three hcard φ hker h3₁
    (hUφ a' haU) (hord a' haU hna) (hUσ a' haU)
  obtain ⟨b, hφb, hcb, hb3⟩ := exists_lift_commute_of_orderOf_eq_three hcard φ hker h3₁
    (hUφ b' hbU) (hord b' hbU hnb) (hUσ b' hbU)
  have hK := isKleinFour_autFixedSubgroup hcomm hJ h2
  have hmem : ∀ h : ↥(H z), Commute σ₁ h → h ∈ Subgroup.centralizer ({σ₁} : Set ↥(H z)) :=
    fun h hh => Subgroup.mem_centralizer_singleton_iff.mpr hh.eq.symm
  let A : ↥(Subgroup.centralizer ({σ₁} : Set ↥(H z))) := ⟨a, hmem a hca⟩
  let B : ↥(Subgroup.centralizer ({σ₁} : Set ↥(H z))) := ⟨b, hmem b hcb⟩
  have hpow3 : ∀ c : ↥(H z), orderOf c = 3 → c ^ 3 = 1 := fun c hc => by
    rw [← hc]
    exact pow_orderOf_eq_one c
  have hA3 : A ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hpow3 a ha3)
  have hB3 : B ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hpow3 b hb3)
  have hf3 : resFix σ₁ A ^ 3 = 1 := by rw [← map_pow, hA3, map_one]
  have hg3 : resFix σ₁ B ^ 3 = 1 := by rw [← map_pow, hB3, map_one]
  have htriv : ∀ C : ↥(Subgroup.centralizer ({σ₁} : Set ↥(H z))), resFix σ₁ C = 1 →
      ∀ v ∈ autFixedSubgroup (conjVA z σ₁), conjVA z (C : ↥(H z)) v = v := by
    intro C hC v hv
    have h := congrArg (fun f : MulAut ↥(autFixedSubgroup (conjVA z σ₁)) =>
      ((f ⟨v, hv⟩ : ↥(autFixedSubgroup (conjVA z σ₁))) : QuotientV.V z)) hC
    simpa only [resFix_apply, MulAut.one_apply] using h
  obtain ⟨w, hcw, hwU, hwn, hwfix⟩ : ∃ w : ↥(H z), Commute σ₁ w ∧ φ w ∈ oThreeSigmaQA45 ∧
      φ w ∉ Subgroup.zpowers s1A ∧ ∀ v ∈ autFixedSubgroup (conjVA z σ₁), conjVA z w v = v := by
    rcases mulAut_eq_one_or_of_isKleinFour hf3 hg3 with h | h | h | h
    · exact ⟨a, hca, by rw [hφa]; exact haU, by rw [hφa]; exact hna, htriv A h⟩
    · exact ⟨b, hcb, by rw [hφb]; exact hbU, by rw [hφb]; exact hnb, htriv B h⟩
    · refine ⟨a * b, hca.mul_right hcb, ?_, ?_, htriv (A * B) (by rw [map_mul]; exact h)⟩
      · rw [map_mul, hφa, hφb]
        exact mul_mem haU hbU
      · rw [map_mul, hφa, hφb]
        exact hnab
    · refine ⟨a * b * b, (hca.mul_right hcb).mul_right hcb, ?_, ?_,
        htriv (A * B * B) (by rw [map_mul, map_mul]; exact h)⟩
      · rw [map_mul, map_mul, hφa, hφb]
        exact mul_mem (mul_mem haU hbU) hbU
      · rw [map_mul, map_mul, hφa, hφb]
        exact hnabb
  obtain ⟨n, hn, hxn⟩ := exists_pow_lift_orderOf_eq φ (isPGroup_ker_of_ker_eq hcard φ hker)
    (c := w) (m := 3) ⟨1, by norm_num⟩ (by norm_num) (hord _ hwU hwn)
  refine ⟨w ^ n, hcw.pow_right n, hxn, by rw [hn]; exact hwU, by rw [hn]; exact hwn, ?_⟩
  intro v hv
  have hpow : ∀ k : ℕ, (conjVA z w ^ k) v = v := by
    intro k
    induction k with
    | zero => rw [pow_zero, MulAut.one_apply]
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hwfix v hv, ih]
  rw [map_pow]
  exact hpow n

theorem fixDimV_sigma1_mul_sigma2_inv_eq_four (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) {y : ↥(H z)} (hy : orderOf y = 9) (hyσ : y ^ 3 = σ₁) :
    fixDimV hcomm hJ (σ₁ * σ₂⁻¹) = 4 := by
  let _ : CommGroup (QuotientV.V z) := commGroupV hcomm
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have h2 : fixDimV hcomm hJ σ₁ = 2 := fixDimV_eq_two_of_cube hJ hcard hcomm hCHJ hy hyσ
  obtain ⟨x, hcx, hx3, hxU, hxn, hxfix⟩ :=
    exists_fix_sigma1_of_mem_O3 hJ hcard hcomm φ hker hQP hσ₁ h3₁ h2
  have hs1U : s1A ∈ oThreeSigmaQA45 := s1A_mem_oThreeSigmaQA45
  have hφs : φ (σ₁ * σ₂⁻¹) = s1A * s2A⁻¹ := by rw [map_mul, map_inv, hσ₁, hσ₂]
  have hclass : ∀ g : ↥(H z), φ g ∈ oThreeSigmaQA45 → φ g ∉ Subgroup.zpowers s1A →
      fixDimV hcomm hJ g = fixDimV hcomm hJ (σ₁ * σ₂⁻¹) := by
    intro g hg hgn
    obtain ⟨c, hc, hcg⟩ := exists_conj_sigma12_QA45 hg hgn
    exact fixDimV_eq_of_map_conj hcomm hJ φ hker (hQP hc) (by rw [hφs]; exact hcg)
  have hnot : x ∉ Subgroup.zpowers σ₁ := by
    intro h
    apply hxn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [map_zpow, hσ₁]
    exact Subgroup.zpow_mem_zpowers _ k
  have hd1 : fixDimV hcomm hJ x = fixDimV hcomm hJ (σ₁ * σ₂⁻¹) := hclass x hxU hxn
  have hd2 : fixDimV hcomm hJ (σ₁ * x) = fixDimV hcomm hJ (σ₁ * σ₂⁻¹) := by
    refine hclass _ (by rw [map_mul, hσ₁]; exact mul_mem hs1U hxU) ?_
    rw [map_mul, hσ₁]
    intro h
    apply hxn
    have h' := mul_mem (inv_mem (Subgroup.mem_zpowers s1A)) h
    rwa [inv_mul_cancel_left] at h'
  have hd3 : fixDimV hcomm hJ (σ₁ * x⁻¹) = fixDimV hcomm hJ (σ₁ * σ₂⁻¹) := by
    refine hclass _ (by rw [map_mul, map_inv, hσ₁]; exact mul_mem hs1U (inv_mem hxU)) ?_
    rw [map_mul, map_inv, hσ₁]
    intro h
    apply hxn
    have h' := mul_mem (inv_mem (Subgroup.mem_zpowers s1A)) h
    rw [inv_mul_cancel_left] at h'
    exact inv_mem_iff.mp h'
  have hfs : ∀ g : ↥(H z), fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g) =
      fixSubmodule hcomm hJ g := fun g => invariants_zpowers_eq_fixSubmodule hcomm hJ g
  have hfr : ∀ g : ↥(H z),
      Module.finrank (ZMod 2) (fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g)) =
        fixDimV hcomm hJ g := fun g => by rw [hfs g]; rfl
  have hle : ∀ g : ↥(H z), (∀ v ∈ autFixedSubgroup (conjVA z σ₁), conjVA z g v = v) →
      fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers σ₁) ≤
        fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g) := by
    intro g hg v hv
    rw [hfs σ₁, mem_fixSubmodule_iff] at hv
    rw [hfs g, mem_fixSubmodule_iff, mem_autFixedSubgroup]
    exact hg _ hv
  have hfixσ : ∀ v ∈ autFixedSubgroup (conjVA z σ₁), conjVA z σ₁ v = v :=
    fun v hv => mem_autFixedSubgroup.mp hv
  have hfx1 := hle x hxfix
  have hfx2 := hle (σ₁ * x) fun v hv => by
    rw [map_mul, MulAut.mul_apply, hxfix v hv, hfixσ v hv]
  have hfx3 := hle (σ₁ * x⁻¹) fun v hv => by
    have hinv := MulAut.inv_apply_self _ (conjVA z x) v
    rw [hxfix v hv] at hinv
    rw [map_mul, MulAut.mul_apply, map_inv, hinv, hfixσ v hv]
  have e5 := finrank_fixedSpace_add_finrank_commSpace (conjVRepresentation hcomm hJ) h3₁
  have e10 := finrank_commSpace_eq_sum (conjVRepresentation hcomm hJ) h3₁ hx3 hcx hnot
  have e6a := finrank_fixedSpace_eq_add (conjVRepresentation hcomm hJ) h3₁ x hcx
  have e6b := finrank_fixedSpace_eq_add (conjVRepresentation hcomm hJ) h3₁ (σ₁ * x)
    ((Commute.refl σ₁).mul_right hcx)
  have e6c := finrank_fixedSpace_eq_add (conjVRepresentation hcomm hJ) h3₁ (σ₁ * x⁻¹)
    ((Commute.refl σ₁).mul_right hcx.inv_right)
  rw [inf_eq_left.mpr hfx1, hfr, hfr] at e6a
  rw [inf_eq_left.mpr hfx2, hfr, hfr] at e6b
  rw [inf_eq_left.mpr hfx3, hfr, hfr] at e6c
  rw [hfr, finrank_addV hJ hcard hcomm] at e5
  omega

theorem fixDimV_sigma1_mul_sigma2_eq_zero (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    orderOf (σ₁ * σ₂) = 3 ∧ fixDimV hcomm hJ (σ₁ * σ₂) = 0 := by
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
  have h3 := orderOf_mul_eq_three_of_not_mem h3₁ h3₂ hc hnot
  refine ⟨h3, ?_⟩
  have h4 := fixDimV_sigma1_mul_sigma2_inv_eq_four hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ hy hyσ
  have hfr : ∀ g : ↥(H z),
      Module.finrank (ZMod 2) (fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g)) =
        fixDimV hcomm hJ g := fun g => by
    rw [show fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers g) =
      fixSubmodule hcomm hJ g from invariants_zpowers_eq_fixSubmodule hcomm hJ g]
    rfl
  have hsum := finrank_eq_sum_fixedSpace_of_fixedSpace_eq_bot (conjVRepresentation hcomm hJ)
    h3₁ h3₂ hc hnot hE
  rw [hfr, hfr, hfr, hfr, finrank_addV hJ hcard hcomm, h2₁, h2₂, h4] at hsum
  omega

theorem CJ_sigma1_mul_sigma2_eq_zpowers (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    CJ z ((σ₁ * σ₂ : ↥(H z)) : G) = Subgroup.zpowers z := by
  obtain ⟨h3, h0⟩ := fixDimV_sigma1_mul_sigma2_eq_zero hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂
    h3₂ hc hne hy hyσ hu
  have hcardCJ : Nat.card (CJ z ((σ₁ * σ₂ : ↥(H z)) : G)) = 2 := by
    rw [card_CJ_eq_two_mul hJ hcard hcomm h3, h0]
    norm_num
  have hZ : Subgroup.zpowers z ≤ CJ z ((σ₁ * σ₂ : ↥(H z)) : G) :=
    Subgroup.zpowers_le_of_mem (z_mem_CJ hcomm _)
  have hcZ : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_z hJ hcomm]
  exact (Subgroup.eq_of_le_of_card_ge hZ (by rw [hcardCJ, hcZ])).symm

end Model

end CFSG.RankThree.GF2n.Parrott.Remarks
