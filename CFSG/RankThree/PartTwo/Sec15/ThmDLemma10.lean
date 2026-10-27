module

public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofFit
public import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptQ_of_centralizes {A : Subgroup G} (hA : IsE27 A)
    (h142 : Concl142 A (lB A)) (h143 : Concl143 A (lB A)) (h146 : Item146 A (lB A))
    {Y : Subgroup G} (hYΔ : Y = delta A (lB A) Y) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hV : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A))
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hcen : ∀ y ∈ Y, ⁅y, a⁆ ∈ CFSG.Open.pCoreOf 2 Y)
    {R : Subgroup G} (hRY : R ≤ Y) (hR3 : ¬ 3 ∣ Nat.card R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) : R ∈ scriptQ A (lB A) := by
  classical
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set V := CFSG.Open.pCoreOf 2 Y with hVdef
  have hVY : V ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have ha3 : a ^ 3 = 1 := hA.1.2 a haA
  have hz3 : IsPGroup 3 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers]
    have hd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
    have h1 : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd h h1
    · simp [h]
  have hpow : ∀ n : ℕ, ∀ y ∈ Y, ⁅y, a ^ n⁆ ∈ V := by
    intro n
    induction n with
    | zero => intro y hy; simpa using V.one_mem
    | succ n ih =>
      intro y hy
      have h : ⁅y, a ^ (n + 1)⁆ = ⁅y, a⁆ * (a * ⁅y, a ^ n⁆ * a⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h]
      refine V.mul_mem (hcen y hy) ?_
      exact (Subgroup.mem_normalizer_iff.mp (hAV haA) _).mp (ih y hy)
  have hcomm : ⁅Y, Subgroup.zpowers a⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro y hy x hx
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers).mpr hx
    exact hpow n y hy
  have hAcentr : A ≤ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) := by
    intro x hx
    refine Subgroup.le_normalizer ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hAab a haA x hx).symm
  have hCQ : ∀ Q ∈ scriptQ A (lB A), Q ⊓ Subgroup.centralizer ({a} : Set G) ∈ scriptQ A (lB A) :=
    fun Q hQ => mem_scriptQ_of_le hQ inf_le_left
      (Late.le_normalizer_inf (mem_scriptQ_iff.mp hQ).2.1 hAcentr)
  have hcz : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    apply le_antisymm
    · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers a))
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hc : Commute a x := (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
      exact (hc.zpow_left k).eq
  set D := delta A (lB A) (Subgroup.centralizer ({a} : Set G)) with hD
  have hDc : D ≤ Subgroup.centralizer ({a} : Set G) := delta_le _
  have hstep1 : Y ≤ V ⊔ (D ⊓ Y) := by
    refine hYΔ.le.trans (sSup_le fun Q hQ => ?_)
    obtain ⟨hQ𝒬, hQY⟩ := hQ
    have hQ3 : ¬ 3 ∣ Nat.card Q :=
      (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp (mem_scriptQ_iff.mp hQ𝒬).1
    have hAQ := (mem_scriptQ_iff.mp hQ𝒬).2.1
    have hQa : Subgroup.zpowers a ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.zpowers_le.mpr (hAQ haA)
    have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three (Subgroup.zpowers a) Q hz3 hQ3 hQa
    have hQV : ⁅Q, Subgroup.zpowers a⁆ ≤ V :=
      (Subgroup.commutator_mono hQY le_rfl).trans hcomm
    have hcQ : Q ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) ≤ D ⊓ Y := by
      rw [hcz]
      exact le_inf (le_delta (hCQ Q hQ𝒬) inf_le_right) (inf_le_left.trans hQY)
    calc Q = ⁅Q, Subgroup.zpowers a⁆ ⊔ (Q ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)) := hfac
      _ ≤ V ⊔ (D ⊓ Y) := sup_le_sup hQV hcQ
  have hstep2 : ∀ y ∈ Y, a * y = y * a → y ∈ D := by
    intro y hy hya
    have hZV : (D ⊓ Y) ≤ Subgroup.normalizer (V : Set G) :=
      inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    have hy' : y ∈ ((V : Set G) * ((D ⊓ Y : Subgroup G) : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left V (D ⊓ Y) hZV]
      exact hstep1 hy
    obtain ⟨v, hv, z, hz, rfl⟩ := hy'
    have hzc : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (hDc hz.1) |>.symm
    have hvc : v ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : a * (v * z) = (v * z) * a := hya
      calc v * a = v * a * z * z⁻¹ := by group
        _ = v * (a * z) * z⁻¹ := by rw [mul_assoc v a z]
        _ = v * (z * a) * z⁻¹ := by rw [hzc]
        _ = (v * z) * a * z⁻¹ := by group
        _ = a * (v * z) * z⁻¹ := by rw [← this]
        _ = a * v := by group
    have hvD : v ∈ D := le_delta (hCQ V hV) inf_le_right ⟨hv, hvc⟩
    exact D.mul_mem hvD hz.1
  have hfacR :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three (Subgroup.zpowers a) R hz3 hR3 (Subgroup.zpowers_le.mpr (hAR haA))
  set CR := R ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) with hCR
  have hCRle : CR ≤ D := by
    intro x hx
    have hxc : x ∈ Subgroup.centralizer ({a} : Set G) := hcz ▸ hx.2
    exact hstep2 x (hRY hx.1) (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
  have hAC : A ≤ Subgroup.normalizer (CR : Set G) := by
    refine Late.le_normalizer_inf hAR ?_
    rw [hcz]
    exact hAcentr
  have hCRQ : CR ∈ scriptQ A (lB A) :=
    Sec17.Proof171Steps.mem_scriptQ_of_le_delta h142 h143 haA ha1 hCRle
      (fun h => hR3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))) hAC
  have hVR : V ⊓ R ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hV inf_le_left (Late.le_normalizer_inf hAV hAR)
  have hRN : R ≤ Subgroup.normalizer ((V ⊓ R : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (hRY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
      Subgroup.le_normalizer
  have hsup : CR ⊔ (V ⊓ R) ∈ scriptQ A (lB A) :=
    Sec14.sup_mem_scriptQ_of_item146 hA h146 hCRQ hVR (inf_le_left.trans hRN)
  have hxN : Subgroup.zpowers a ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr (hAR haA)
  have hcR : ⁅R, Subgroup.zpowers a⁆ ≤ V ⊓ R := by
    refine le_inf ((Subgroup.commutator_mono hRY le_rfl).trans hcomm) ?_
    rw [Subgroup.commutator_le]
    intro r hr x hx
    rw [commutatorElement_def]
    have h := (Subgroup.mem_normalizer_iff.mp (hxN hx) r⁻¹).mp (R.inv_mem hr)
    simpa [mul_assoc] using R.mul_mem hr h
  have hRle : R ≤ CR ⊔ (V ⊓ R) := by
    calc R = ⁅R, Subgroup.zpowers a⁆ ⊔ CR := hfacR
      _ ≤ (V ⊓ R) ⊔ CR := sup_le_sup_right hcR _
      _ = CR ⊔ (V ⊓ R) := sup_comm _ _
  exact mem_scriptQ_of_le hsup hRle hAR

theorem mem_scriptQ_of_hyperplanes {A : Subgroup G} (hA : IsE27 A) (h142 : Concl142 A (lB A))
    {V P : Subgroup G} (hV : V ∈ scriptQ A (lB A)) (hP3 : ¬ 3 ∣ Nat.card P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (h : ∀ B, IsHyperplane A B → (∀ F ∈ omegaA A, ¬ F ≤ B) →
      P ⊓ Subgroup.centralizer (B : Set G) ≤ V) : P ∈ scriptQ A (lB A) := by
  have hP3' : IsPiSubgroup (piCompl 3) P := (isPiSubgroup_piCompl_iff Nat.prime_three P).mpr hP3
  refine mem_scriptQ_iff.mpr ⟨hP3', hAP, fun B hB => ?_⟩
  by_cases hΩ : ∀ F ∈ omegaA A, ¬ F ≤ B
  · exact (le_inf (h B hB hΩ) inf_le_right).trans (hV.2 B hB)
  · push Not at hΩ
    obtain ⟨F, hF, hFB⟩ := hΩ
    have hF' := hF
    obtain ⟨-, -, e, rfl, -⟩ := hF'
    have heB : e ∈ B := hFB (Subgroup.mem_zpowers e)
    have hPe := Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 hA h142 hF hP3' hAP
    have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heB)
    exact (le_inf (le_inf inf_le_left (inf_le_right.trans hCB)) inf_le_right).trans (hPe.2 B hB)

end CFSG.RankThree.PartTwo.Sec15.ThmD
