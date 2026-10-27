module

public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.RankThree.PartTwo.Sec19.Step196Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec13.Item13Theta
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Late.Uniqueness
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.RankThree.PartTwo.Sec18.Item181
import CFSG.RankThree.PartTwo.Sec18.Item181b
import CFSG.RankThree.PartTwo.KFacts.KS18OuterMain
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
public import CFSG.RankThree.PartTwo.Sec14.Item145Bot
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import Certificates.Certificate2202
public import Certificates.Certificate43
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import Certificates.Certificate3086
import Certificates.Certificate3139

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

namespace Step197Proof

section Heis

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem exists_heis_U (h : Sec13Data G A c L) (hcL : c ∈ L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) :
    ∃ U : Subgroup (lBarA c L A),
      (∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u) ∧
      U ⊔ (Sec12.lBar c L).subgroupOf (lBarA c L A) = ⊤ ∧
      (∀ x ∈ U, x ^ 3 = 1) ∧ Nat.card U = 27 ∧
      U ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) =
        Subgroup.zpowers (mkC (L := L) h.mem_A) ∧
      ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ Subgroup.zpowers (mkC (L := L) h.mem_A) := by
  obtain ⟨U, hU, hUΛ, hUV, hZU⟩ := isHeisCentral_facts h hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set z := mkC (L := L) h.mem_A with hz
  have hzΛ : z ∈ Λ := mkC_mem_lBar h hcL
  set ZΛ := (Subgroup.center Λ).map Λ.subtype with hZΛ
  have hZΛcard : Nat.card ZΛ = 3 := by
    rw [hZΛ, Subgroup.card_map_of_injective Λ.subtype_injective, card_center_lBar h, hZ3]
  have hUΛZ : U ⊓ Λ ≤ ZΛ := by
    rintro x ⟨hxU, hxΛ⟩
    refine ⟨⟨x, hxΛ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact (hUΛ x hxU y y.2).symm
  have hUΛcard : Nat.card (U ⊓ Λ : Subgroup _) = 3 := by
    rw [← hZU, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  have hUΛeq : U ⊓ Λ = ZΛ := Subgroup.eq_of_le_of_card_ge hUΛZ (by rw [hZΛcard, hUΛcard])
  have hzZ : z ∈ ZΛ := by
    refine ⟨⟨z, hzΛ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_center_iff.mp (mkC_mem_center h) y
  rw [← hUΛeq] at hzZ
  have hzpow : Subgroup.zpowers z = U ⊓ Λ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_
    rw [hUΛcard, Nat.card_zpowers, orderOf_mkC h]
  refine ⟨U, hUΛ, hUV, ?_, hU.2.1, hzpow.symm, ?_⟩
  · intro x hx
    have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : U)
    rw [hU.2.2] at h1
    simpa using congrArg Subtype.val h1
  · intro u hu v hv
    rw [hzpow, ← hZU]
    have h2 : (⁅(⟨u, hu⟩ : U), ⟨v, hv⟩⁆ : U) ∈ commutator U :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hU.1.2.1] at h2
    exact ⟨_, h2, by simp [commutatorElement_def]⟩

theorem range_inf_lBar_eq (h : Sec13Data G A c L) (hcL : c ∈ L) {U : Subgroup (lBarA c L A)}
    (hUΛ : ∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u)
    (hUV : U ⊔ (Sec12.lBar c L).subgroupOf (lBarA c L A) = ⊤) (hU27 : Nat.card U = 27)
    (hUΛz : U ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) =
      Subgroup.zpowers (mkC (L := L) h.mem_A)) :
    (aBarHom h).range ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) =
      Subgroup.zpowers (mkC (L := L) h.mem_A) := by
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set Ab := (aBarHom h).range with hAb
  set z := mkC (L := L) h.mem_A with hz
  have hzo : orderOf z = 3 := orderOf_mkC h
  have hzAb : z ∈ Ab := ⟨⟨c, h.mem_A⟩, (mkC_eq_aBarHom h).symm⟩
  have hzΛ : z ∈ Λ := mkC_mem_lBar h hcL
  have hΛn : Λ.Normal := lBar_normal h
  have hAbΛ : Ab ≤ Subgroup.normalizer (Λ : Set (lBarA c L A)) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hΛn.conj_mem y hy x, fun hy => ?_⟩
    have h1 := hΛn.conj_mem _ hy x⁻¹
    simpa [mul_assoc] using h1
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, ← Nat.card_congr (MonoidHom.ofInjective (aBarHom_injective h)).toEquiv,
      h.card_eq]
  have h1 := Sec6.card_sup_mul_card_inf hAbΛ
  have h2 : Ab ⊔ Λ = ⊤ := by rw [sup_comm]; exact lBar_sup_range_aBarHom h
  have h3 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U Λ hUΛ).1
  rw [hUV, hUΛz, Nat.card_zpowers, hzo, hU27] at h3
  rw [h2, hAb27] at h1
  have hΛpos : 0 < Nat.card Λ := Nat.card_pos
  have htop : 0 < Nat.card (⊤ : Subgroup (lBarA c L A)) := Nat.card_pos
  have h4 : Nat.card (Ab ⊓ Λ : Subgroup (lBarA c L A)) = 3 := by
    have h5 : Nat.card (⊤ : Subgroup (lBarA c L A)) * Nat.card (Ab ⊓ Λ : Subgroup _) =
        Nat.card (⊤ : Subgroup (lBarA c L A)) * 3 := by rw [h1, h3]
    exact Nat.eq_of_mul_eq_mul_left htop h5
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hzAb, hzΛ⟩) ?_
  rw [h4, Nat.card_zpowers, hzo]

theorem exists_EY (h : Sec13Data G A c L) (hcL : c ∈ L) {U : Subgroup (lBarA c L A)}
    (hUΛ : ∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u)
    (hUV : U ⊔ (Sec12.lBar c L).subgroupOf (lBarA c L A) = ⊤) (hU3 : ∀ x ∈ U, x ^ 3 = 1)
    (hU27 : Nat.card U = 27)
    (hUΛz : U ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) =
      Subgroup.zpowers (mkC (L := L) h.mem_A))
    (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ Subgroup.zpowers (mkC (L := L) h.mem_A))
    {a : A} (ha : (a : G) ∉ Subgroup.zpowers c) :
    ∃ EY : Subgroup (lBarA c L A), CFSG.Assembly.IsElemAbelian 3 EY ∧ Nat.card EY = 27 ∧
      mkC (L := L) h.mem_A ∈ EY ∧ aBarHom h a ∈ EY ∧
      EY ≤ Subgroup.normalizer ((aBarHom h).range : Set (lBarA c L A)) ∧
      (aBarHom h).range ≤ Subgroup.normalizer (EY : Set (lBarA c L A)) ∧
      (∃ u ∈ EY, (∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u) ∧
        u ∉ Subgroup.zpowers (mkC (L := L) h.mem_A)) ∧
      ∃ v ∈ EY, v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) ∧
        v ∉ Subgroup.zpowers (mkC (L := L) h.mem_A) := by
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set Ab := (aBarHom h).range with hAb
  set z := mkC (L := L) h.mem_A with hz
  have hzo : orderOf z = 3 := orderOf_mkC h
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzo] at this
  have hzAb : z ∈ Ab := ⟨⟨c, h.mem_A⟩, (mkC_eq_aBarHom h).symm⟩
  have hzΛ : z ∈ Λ := mkC_mem_lBar h hcL
  have hzU : z ∈ U := (hUΛz ▸ Subgroup.mem_zpowers z : z ∈ U ⊓ Λ).1
  have hzc : ∀ x : lBarA c L A, z * x = x * z := fun x =>
    (Subgroup.mem_center_iff.mp (mkC_mem_center h) x).symm
  have hF1 : ∀ b : A, aBarHom h b ∈ U → (b : G) ∈ Subgroup.zpowers c := fun b hb =>
    mem_zpowers_of_aBarHom_commute h b (fun y hy => hUΛ _ hb y hy)
  have hF2 : ∀ b : A, aBarHom h b ∈ Λ → (b : G) ∈ Subgroup.zpowers c := by
    intro b hb
    have hbz : aBarHom h b ∈ Subgroup.zpowers z := by
      rw [← range_inf_lBar_eq h hcL hUΛ hUV hU27 hUΛz]
      exact ⟨⟨b, rfl⟩, hb⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hbz
    have hbi : b = (⟨c, h.mem_A⟩ : A) ^ i := by
      apply aBarHom_injective h
      rw [map_zpow, ← mkC_eq_aBarHom h, ← hz, hi]
    rw [hbi]
    exact Subgroup.zpow_mem_zpowers _ _
  set ab := aBarHom h a with hab
  have hab3 : ab ^ 3 = 1 := by
    rw [hab, ← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using h.isElemAbelian.2 _ a.2)
    rw [this, map_one]
  have hcoe := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U Λ hUΛ).2
  have habUV : ab ∈ ((U ⊔ Λ : Subgroup _) : Set (lBarA c L A)) := by
    rw [hUV]; exact Subgroup.mem_top ab
  rw [hcoe] at habUV
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp habUV
  have hvu : u * v = v * u := hUΛ u hu v hv
  have hu3 : u ^ 3 = 1 := hU3 u hu
  have hv3 : v ^ 3 = 1 := by
    have h1 : (u * v) ^ 3 = u ^ 3 * v ^ 3 := (Commute.mul_pow hvu 3)
    rw [huv, hab3, hu3, one_mul] at h1
    exact h1.symm
  have huz : u ∉ Subgroup.zpowers z := by
    intro huz
    apply ha
    apply hF2 a
    rw [← hab, ← huv]
    exact Λ.mul_mem ((Subgroup.zpowers_le.mpr hzΛ) huz) hv
  set D := Subgroup.zpowers z ⊔ Subgroup.zpowers u with hD
  have hDab : CFSG.Assembly.IsElemAbelian 3 D := isElemAbelian_zpowers_sup hz3 hu3 (hzc u)
  have hD9 : Nat.card D = 9 := Sec4.card_zpowers_sup_zpowers hu3 hzo huz (hzc u).symm
  have hDU : D ≤ U := sup_le (Subgroup.zpowers_le.mpr hzU) (Subgroup.zpowers_le.mpr hu)
  have hvD : v ∉ D := by
    intro hvD
    apply ha
    apply hF1 a
    rw [← hab, ← huv]
    exact U.mul_mem hu (hDU hvD)
  have hDv : ∀ e ∈ D, e * v = v * e := fun e he => hUΛ e (hDU he) v hv
  have hEY : IsE27 (D ⊔ Subgroup.zpowers v) := isE27_sup_zpowers hDab hD9 hvD hv3 hDv
  have hcomm : ∀ b ∈ Ab, u * b * u⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
    intro b hb
    have hbUV : b ∈ ((U ⊔ Λ : Subgroup _) : Set (lBarA c L A)) := by
      rw [hUV]; exact Subgroup.mem_top b
    rw [hcoe] at hbUV
    obtain ⟨ub, hub, vb, hvb, rfl⟩ := Set.mem_mul.mp hbUV
    have hvbu : u * vb = vb * u := hUΛ u hu vb hvb
    have h2 : vb * u⁻¹ = u⁻¹ * vb := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hvbu, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : u * (ub * vb) * u⁻¹ * (ub * vb)⁻¹ = u * ub * u⁻¹ * ub⁻¹ := by
      calc u * (ub * vb) * u⁻¹ * (ub * vb)⁻¹ = u * ub * (vb * u⁻¹) * vb⁻¹ * ub⁻¹ := by group
        _ = u * ub * (u⁻¹ * vb) * vb⁻¹ * ub⁻¹ := by rw [h2]
        _ = u * ub * u⁻¹ * ub⁻¹ := by group
    rw [h1]
    exact hUc u hu ub hub
  have huN : u ∈ Subgroup.normalizer (Ab : Set (lBarA c L A)) := by
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    have h1 : u * b * u⁻¹ = (u * b * u⁻¹ * b⁻¹) * b := by group
    rw [h1]
    exact Ab.mul_mem ((Subgroup.zpowers_le.mpr hzAb) (hcomm b hb)) hb
  have habN : ab ∈ Subgroup.normalizer (Ab : Set (lBarA c L A)) :=
    Subgroup.le_normalizer ⟨a, rfl⟩
  have hv' : v = u⁻¹ * ab := by rw [← huv, inv_mul_cancel_left]
  have hvN : v ∈ Subgroup.normalizer (Ab : Set (lBarA c L A)) := by
    rw [hv']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ huN) habN
  have hzN : z ∈ Subgroup.normalizer (Ab : Set (lBarA c L A)) := Subgroup.le_normalizer hzAb
  set EY := D ⊔ Subgroup.zpowers v with hEYdef
  have hzEY : z ∈ EY := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have huEY : u ∈ EY := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
  have hvEY : v ∈ EY := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have habEY : ab ∈ EY := by rw [← huv]; exact EY.mul_mem huEY hvEY
  have hAbN : Ab ≤ Subgroup.normalizer (EY : Set (lBarA c L A)) := by
    intro b hb
    have hbab : b * ab = ab * b := by
      obtain ⟨b', rfl⟩ := hb
      have := h.isElemAbelian.1
      rw [hab, ← map_mul, ← map_mul, mul_comm' b' a]
    have hbu : b * u * b⁻¹ ∈ EY := by
      have h1 : b * u * b⁻¹ = (u * b * u⁻¹ * b⁻¹)⁻¹ * u := by group
      rw [h1]
      exact EY.mul_mem (EY.inv_mem ((Subgroup.zpowers_le.mpr hzEY) (hcomm b hb))) huEY
    have hle : EY ≤ EY.comap (MulAut.conj b).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      · change b * z * b⁻¹ ∈ EY
        rw [← hzc b, mul_inv_cancel_right]
        exact hzEY
      · exact hbu
      · change b * v * b⁻¹ ∈ EY
        have h1 : b * v * b⁻¹ = (b * u * b⁻¹)⁻¹ * ab := by
          calc b * v * b⁻¹ = (b * u * b⁻¹)⁻¹ * (b * ab * b⁻¹) := by rw [hv']; group
            _ = (b * u * b⁻¹)⁻¹ * ab := by rw [hbab, mul_inv_cancel_right]
        rw [h1]
        exact EY.mul_mem (EY.inv_mem hbu) habEY
    exact Subgroup.mem_normalizer_fintype fun y hy => hle hy
  refine ⟨EY, hEY.1, hEY.2, hzEY, habEY, ?_, hAbN, ⟨u, huEY, hUΛ u hu, huz⟩,
    ⟨v, hvEY, hv, fun hvz => hvD ((le_sup_left : Subgroup.zpowers z ≤ D) hvz)⟩⟩
  exact sup_le (sup_le (Subgroup.zpowers_le.mpr hzN) (Subgroup.zpowers_le.mpr huN))
    (Subgroup.zpowers_le.mpr hvN)

theorem exists_E_of_EY (h : Sec13Data G A c L) (hcL : c ∈ L) {EY : Subgroup (lBarA c L A)}
    (hEN : EY ≤ Subgroup.normalizer ((aBarHom h).range : Set (lBarA c L A)))
    (hAbN : (aBarHom h).range ≤ Subgroup.normalizer (EY : Set (lBarA c L A)))
    (hEe : CFSG.Assembly.IsElemAbelian 3 EY) (hE27 : Nat.card EY = 27)
    (hzE : mkC (L := L) h.mem_A ∈ EY) {u : lBarA c L A} (huE : u ∈ EY)
    (huΛ : ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u)
    (huz : u ∉ Subgroup.zpowers (mkC (L := L) h.mem_A)) {v : lBarA c L A} (hvE : v ∈ EY)
    (hvΛ : v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A))
    (hvz : v ∉ Subgroup.zpowers (mkC (L := L) h.mem_A)) {a : A} (haE : aBarHom h a ∈ EY) :
    ∃ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∧
      ¬ IsCyclic (E ⊓ L : Subgroup G) ∧ A ≤ Subgroup.normalizer (E : Set G) ∧ c ∈ E ∧
      (a : G) ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set θH := aschbacherSolvableCore 3 H with hθH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛdef
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hLAN : L ⊔ A ≤ Subgroup.normalizer (L : Set G) := sup_le hLN h.le_normalizer
  have hLAH : L ⊔ A ≤ H :=
    sup_le (le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt) h.A_le_normalizer_zpowers
  let ι : (L ⊔ A : Subgroup G) →* H := Subgroup.inclusion hLAH
  let φ : (L ⊔ A : Subgroup G) →* lBarA c L A :=
    ((QuotientGroup.mk' θH).comp ι).codRestrict (lBarA c L A) fun x =>
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  have hφv : ∀ x : (L ⊔ A : Subgroup G), ((φ x : lBarA c L A) : H ⧸ θH) =
      QuotientGroup.mk' θH ⟨(x : G), hLAH x.2⟩ := fun x => rfl
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have hker : Nat.Coprime 3 (Nat.card φ.ker) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    apply (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
    let j : φ.ker →* θH :=
      { toFun := fun x => ⟨ι x, by
          have h1 : ((φ x : lBarA c L A) : H ⧸ θH) = 1 := by rw [MonoidHom.mem_ker.mp x.2]; rfl
          rw [hφv, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
          exact h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := fun x y hxy => by
      have h1 : ((ι x : H) : G) = ((ι y : H) : G) := by
        have := congrArg (fun w : θH => ((w : H) : G)) hxy
        exact this
      exact Subtype.ext (Subtype.ext h1)
    exact h3.trans (Subgroup.card_dvd_of_injective j hj)
  set A_T := A.subgroupOf (L ⊔ A) with hA_T
  have hA_Tp : IsPGroup 3 A_T := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by
      simpa using h.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  have hĀ : A_T.map φ = (aBarHom h).range := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b, Subgroup.mem_sup_right b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, rfl⟩
  have hEN' : EY ≤ Subgroup.normalizer ((A_T.map φ : Subgroup (lBarA c L A)) :
      Set (lBarA c L A)) := by
    rw [hĀ]
    exact hEN
  have hEp : IsPGroup 3 EY := fun x => ⟨1, Subtype.ext (by simpa using hEe.2 _ x.2)⟩
  obtain ⟨ET, hmap, hinj, hETN, hAE⟩ := exists_lift_normalizing φ hφ hker hA_Tp hEN' hEp
  have hlift : ∀ y ∈ EY, ∃ x ∈ ET, φ x = y := fun y hy => by
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  have hinj' : ∀ x ∈ ET, ∀ y ∈ ET, φ x = φ y → x = y := fun x hx y hy hxy =>
    congrArg Subtype.val (hinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hETmem : ∀ x ∈ ET, φ x ∈ EY := fun x hx => hmap ▸ Subgroup.mem_map_of_mem φ hx
  have hET3 : ∀ x ∈ ET, x ^ 3 = 1 := fun x hx => hinj' _ (ET.pow_mem hx 3) _ ET.one_mem
    (by rw [map_pow, map_one]; exact hEe.2 _ (hETmem x hx))
  set E := ET.map (L ⊔ A).subtype with hEdef
  have hE3 : ∀ y ∈ E, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using congrArg Subtype.val (hET3 x hx)
  set cbar := mkC (L := L) h.mem_A with hcbar
  have hcT : (⟨c, Subgroup.mem_sup_right h.mem_A⟩ : (L ⊔ A : Subgroup G)) ∈ A_T :=
    Subgroup.mem_subgroupOf.mpr h.mem_A
  have hφc : φ ⟨c, Subgroup.mem_sup_right h.mem_A⟩ = cbar := rfl
  obtain ⟨xc, hxc, hφxc⟩ := hlift cbar hzE
  have hcE : c ∈ E := by
    have h1 := hAE _ hcT xc hxc (by rw [hφc, hφxc])
    exact ⟨_, h1 ▸ hxc, rfl⟩
  have haT : (⟨(a : G), Subgroup.mem_sup_right a.2⟩ : (L ⊔ A : Subgroup G)) ∈ A_T :=
    Subgroup.mem_subgroupOf.mpr a.2
  have hφa : φ ⟨(a : G), Subgroup.mem_sup_right a.2⟩ = aBarHom h a := rfl
  obtain ⟨xa, hxa, hφxa⟩ := hlift (aBarHom h a) haE
  have haE' : (a : G) ∈ E := by
    have h1 := hAE _ haT xa hxa (by rw [hφa, hφxa])
    exact ⟨_, h1 ▸ hxa, rfl⟩
  obtain ⟨xu, hxu, hφxu⟩ := hlift u huE
  have hxuC : (xu : G) ∈ Sec4.thetaQuotCentralizer L := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hLAN xu.2, fun l hl => ?_⟩
    have hg : l⁻¹ * ((xu : G) * l * (xu : G)⁻¹) ∈ L :=
      L.mul_mem (L.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp (hLAN xu.2) l).mp hl)
    refine mem_theta_of_mk_eq_one h.mem_thetaComponentsAt hg ?_
    set lT : (L ⊔ A : Subgroup G) := ⟨l, Subgroup.mem_sup_left hl⟩
    have hlΛ : φ lT ∈ Λ :=
      Subgroup.mem_subgroupOf.mpr ⟨⟨l, le_normalizer_zpowers_of_mem
        h.mem_thetaComponentsAt hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have h1 : φ xu * φ lT = φ lT * φ xu := by
      rw [hφxu]
      exact huΛ _ hlΛ
    have h2 : φ (lT⁻¹ * (xu * lT * xu⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have h3 := congrArg (fun w : lBarA c L A => (w : H ⧸ θH)) h2
    simp only [hφv] at h3
    exact h3
  have hxuc : (xu : G) ∉ Subgroup.zpowers c := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    have hxe : xu = (⟨c, Subgroup.mem_sup_right h.mem_A⟩ : (L ⊔ A : Subgroup G)) ^ k :=
      Subtype.ext (by simp [hk])
    apply huz
    rw [← hφxu, hxe, map_zpow, hφc]
    exact Subgroup.zpow_mem_zpowers _ _
  obtain ⟨xv, hxv, hφxv⟩ := hlift v hvE
  have hxvL : (xv : G) ∈ L := by
    have h1 : QuotientGroup.mk' θH (ι xv) ∈ Sec12.lBar c L := by
      have := hvΛ
      rw [← hφxv] at this
      exact Subgroup.mem_subgroupOf.mp this
    refine mem_of_mk_mem_lBar h.mem_thetaComponentsAt (k := 1) ?_ h1
    have := hET3 xv hxv
    rw [pow_one, ← map_pow, this, map_one]
  have hxvc : (xv : G) ∉ Subgroup.zpowers c := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    have hxe : xv = (⟨c, Subgroup.mem_sup_right h.mem_A⟩ : (L ⊔ A : Subgroup G)) ^ k :=
      Subtype.ext (by simp [hk])
    apply hvz
    rw [← hφxv, hxe, map_zpow, hφc]
    exact Subgroup.zpow_mem_zpowers _ _
  have hETp : IsPGroup 3 ET := fun x => ⟨1, Subtype.ext (by simpa using hET3 x x.2)⟩
  have hP3 : IsPGroup 3 (ET ⊔ A_T : Subgroup (L ⊔ A : Subgroup G)) :=
    hETp.to_sup_of_normal_right' hA_Tp hETN
  have hinjP := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_injective_on_pGroup 3
    Nat.prime_three φ hker (ET ⊔ A_T) hP3
  have hAN : A ≤ Subgroup.normalizer (E : Set G) := by
    intro b hb
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    set bT : (L ⊔ A : Subgroup G) := ⟨b, Subgroup.mem_sup_right hb⟩ with hbT
    have hbT : bT ∈ A_T := Subgroup.mem_subgroupOf.mpr hb
    have hφb : φ bT = aBarHom h ⟨b, hb⟩ := rfl
    have hw : φ (bT * x * bT⁻¹) ∈ EY := by
      rw [map_mul, map_mul, map_inv, hφb]
      exact (Subgroup.mem_normalizer_iff.mp (hAbN ⟨⟨b, hb⟩, rfl⟩) (φ x)).mp (hETmem x hx)
    obtain ⟨x', hx', hφx'⟩ := hlift _ hw
    have hwP : bT * x * bT⁻¹ ∈ ET ⊔ A_T :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hbT)
        (Subgroup.mem_sup_left hx)) (Subgroup.inv_mem _ (Subgroup.mem_sup_right hbT))
    have heq : x' = bT * x * bT⁻¹ := congrArg Subtype.val
      (hinjP (a₁ := ⟨x', Subgroup.mem_sup_left hx'⟩) (a₂ := ⟨_, hwP⟩) hφx')
    refine ⟨x', hx', ?_⟩
    rw [heq]
    rfl
  refine ⟨E, le_inf (Subgroup.map_subtype_le _) ?_, ⟨⟨⟨fun y y' => ?_⟩⟩, hE3⟩, ?_, ?_, ?_,
    hAN, hcE, haE'⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (hETN hx) ⟨b, Subgroup.mem_sup_right hb⟩).mp
      (Subgroup.mem_subgroupOf.mpr hb)
    exact Subgroup.mem_subgroupOf.mp h1
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := y
    obtain ⟨_, ⟨x', hx', rfl⟩⟩ := y'
    apply Subtype.ext
    change ((x * x' : (L ⊔ A : Subgroup G)) : G) = ((x' * x : (L ⊔ A : Subgroup G)) : G)
    congr 1
    refine hinj' _ (ET.mul_mem hx hx') _ (ET.mul_mem hx' hx) ?_
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨φ x, hETmem x hx⟩ ⟨φ x', hETmem x' hx'⟩)
  · rw [hEdef, Subgroup.card_map_of_injective (L ⊔ A).subtype_injective, ← hE27, ← hmap]
    have hrange : (φ.comp ET.subtype).range = ET.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  · exact not_isCyclic_of_mem (fun x hx => hE3 x hx.1) ⟨hcE,
      Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt⟩
      h.ne_one ⟨⟨xu, hxu, rfl⟩, hxuC⟩ hxuc
  · exact not_isCyclic_of_mem (fun x hx => hE3 x hx.1) ⟨hcE, hcL⟩ h.ne_one
      ⟨⟨xv, hxv, rfl⟩, hxvL⟩ hxvc

end Heis

section Main

variable {G : Type} [Group G] [Finite G] {A L E M : Subgroup G} {c : G}

theorem sec13Data_of_ctx195 (hctx : Ctx195 G A c L E M) : Sec13Data G A c L := by
  have hst := hctx.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  exact ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE, hctx.not_mem_partTwoT,
    hctx.zpowers_mem_omegaA, hctx.mem_lA⟩

theorem exists_ctx195_of_mem (h131 : Item131) (h1730 : Sec17.Item1730)
    (hspor : SporadicModels131) (h196 : Step196) (hctx : Ctx195 G A c L E M)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (haA : a ∈ A) (hac : a ∉ Subgroup.zpowers c) :
    ∃ E' : Subgroup G, Ctx195 G A c L E' M ∧ c ∈ E' ∧ a ∈ E' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := sec13Data_of_ctx195 hctx
  have hst := hctx.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hcL := hctx.mem_L
  obtain ⟨h7, -, hEcl⟩ := item131_seven_of_mem h131 hspor hD hcL
  have hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases h7 with hSL | ⟨-, hlist⟩
    · exfalso
      have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
      have : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hq.1
      have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore 3 L) ⧸
          Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := hq.2.1
      have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) :=
        (QuotientGroup.mk_surjective
          (s := Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))).nontrivial
      exact not_isHeisCentral_of_isSLThreePiTwo hSL hH
    · rcases hlist with h | h | h
      · exact card_center_of_isSLThreePi h
      · exact h.1
      · exact h.1
  obtain ⟨U, hUΛ, hUV, hU3, hU27, hUΛz, hUc⟩ := exists_heis_U hD hcL hH hZ3
  obtain ⟨EY, hEYe, hEY27, hzEY, haEY, hEYN, hAbN, ⟨u, huE, huΛ, huz⟩, ⟨v, hvE, hvΛ, hvz⟩⟩ :=
    exists_EY hD hcL hUΛ hUV hU3 hU27 hUΛz hUc (a := ⟨a, haA⟩) hac
  obtain ⟨E', hE'le, hE'e, hE'27, hE'θ, hE'L, hAE', hcE', haE'⟩ :=
    exists_E_of_EY hD hcL hEYN hAbN hEYe hEY27 hzEY huE huΛ huz hvE hvΛ hvz haEY
  obtain ⟨hEF, hEcl'⟩ := hEcl E' hE'le hE'e hE'27 hE'θ hE'L
  have hEE : E' ∈ partTwoE G := hFE ▸ hEF
  have hET : E' ∈ partTwoT G := by
    by_contra hET
    obtain ⟨-, -, e, -, -, hΩ, I, hI, ⟨φI⟩⟩ := hEcl' hET
    have he : Subgroup.zpowers e ∈ omegaA E' := by
      rw [hΩ]
      exact ⟨1, A.one_mem, (map_conj_one _).symm⟩
    have hIl : I ∈ lA E' e := hI ▸ Set.mem_singleton I
    exact (h1730 G hst hctx.partTwoS_eq E' hEE hET e he I hIl).2.false φI
  obtain ⟨-, M', hM'⟩ := mem_partTwoT_iff.mp hET
  have hE'M : E' ≤ M := (le_centralizer_of_mem hE'e.1 hcE').trans
    ((centralizer_le_normalizer_zpowers c).trans (h196 G A c L E M hctx))
  have hMM : M' = M :=
    rank3II_19_2 hctx.hyp191 ⟨hE'e, hE'27⟩ hctx.isE27 hM' hctx.mem_scriptM hE'M
  rw [hMM] at hM'
  exact ⟨E', { hctx with
    le_sup := hE'le
    isE27 := ⟨hE'e, hE'27⟩
    centralizer_noncyclic := hE'θ
    inf_noncyclic := hE'L
    le_normalizer := hAE'
    mem_partTwoT := hET
    mem_scriptM := hM' }, hcE', haE'⟩

theorem normalizer_le_of_mem (h131 : Item131) (h1730 : Sec17.Item1730)
    (hspor : SporadicModels131) (h196 : Step196) (hctx : Ctx195 G A c L E M)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    {B : Subgroup G} (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hcB : c ∈ B) :
    Subgroup.normalizer (B : Set G) ≤ M := by
  have hD := sec13Data_of_ctx195 hctx
  obtain ⟨a, haB, hac⟩ : ∃ a ∈ B, a ∉ Subgroup.zpowers c := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers c from hne)
    rw [hB9, Nat.card_zpowers, hD.orderOf_eq] at this
    omega
  have haA : a ∈ A := hBA haB
  obtain ⟨E', hctx', hcE', haE'⟩ := exists_ctx195_of_mem h131 h1730 hspor h196 hctx hH haA hac
  have hBE' : B ≤ E' := by
    have hca : c * a = a * c := hD.commute hD.mem_A haA
    have h9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers a : Subgroup G) = 9 :=
      Sec4.card_zpowers_sup_zpowers (hD.isElemAbelian.2 a haA) hD.orderOf_eq hac hca.symm
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ B :=
      sup_le (Subgroup.zpowers_le.mpr hcB) (Subgroup.zpowers_le.mpr haB)
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hB9, h9])
    rw [← heq]
    exact sup_le (Subgroup.zpowers_le.mpr hcE') (Subgroup.zpowers_le.mpr haE')
  exact (normalizer_le_gamma hBE' (two_le_pRank_of_elemAbelian
    (isElemAbelian_of_le hctx'.isE27.1 hBE') hB9.ge)).trans hctx'.mem_scriptM.2

theorem isSLThreePiTwo_or_exists_hyperplane (h131 : Item131) (h1730 : Sec17.Item1730)
    (hspor : SporadicModels131) (h196 : Step196) (hctx : Ctx195 G A c L E M) :
    Sec4.IsSLThreePiTwo (lBarA c L A) ∨
      (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
        ∃ B : Subgroup G, B ≤ A ∧ Nat.card B = 9 ∧ c ∉ B ∧
          ¬ Subgroup.normalizer (B : Set G) ≤ M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := sec13Data_of_ctx195 hctx
  obtain ⟨h7, hW, -⟩ := item131_seven_of_mem h131 hspor hD hctx.mem_L
  rcases h7 with hSL | ⟨hH, -⟩
  · exact Or.inl hSL
  refine Or.inr ⟨hH, ?_⟩
  have hNA : Subgroup.normalizer (A : Set G) ≤ M := (hW hH).trans (h196 G A c L E M hctx)
  have hΓ : ¬ gamma 2 A ≤ M := fun hle => hctx.not_mem_partTwoT
    (mem_partTwoT_iff.mpr ⟨hctx.mem_partTwoE, M, hctx.mem_scriptM.1, hle⟩)
  rw [gamma_le_iff] at hΓ
  push Not at hΓ
  obtain ⟨B, hBA, hB2, hBM⟩ := hΓ
  have hB9 : Nat.card B = 9 := by
    have hdvd : Nat.card B ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hD.card_eq]
      exact Subgroup.card_dvd_of_le hBA
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hlog := CFSG.RankThreeEvenClassification.Helpers.pRank_le_log_card 3 Nat.prime_three B
    rw [hk, Nat.log_pow (by norm_num)] at hlog
    have hk2 : 2 ≤ k := hB2.trans hlog
    interval_cases k
    · rw [hk]
      norm_num
    · exfalso
      have heq : B = A := Subgroup.eq_of_le_of_card_ge hBA (by rw [hk, hD.card_eq]; norm_num)
      exact hBM (heq ▸ hNA)
  by_cases hcB : c ∈ B
  · exact absurd (normalizer_le_of_mem h131 h1730 hspor h196 hctx hH hBA hB9 hcB) hBM
  · exact ⟨B, hBA, hB9, hcB, hBM⟩

theorem not_mem_zpowers_of_not_mem {B : Subgroup G} {d : G} (hc : orderOf c = 3) (hdB : d ∈ B)
    (hd1 : d ≠ 1) (hcB : c ∉ B) : d ∉ Subgroup.zpowers c := by
  intro hdc
  apply hcB
  have hdo : orderOf d = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (hc ▸ orderOf_dvd_of_mem_zpowers hdc) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hd1
    · exact h
  have heq : Subgroup.zpowers d = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hdo, hc])
  exact (Subgroup.zpowers_le.mpr hdB) (heq ▸ Subgroup.mem_zpowers c)

theorem exists_centralizer_not_le (h131 : Item131) (h1730 : Sec17.Item1730)
    (hspor : SporadicModels131) (h196 : Step196) (hctx : Ctx195 G A c L E M)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    {B : Subgroup G} (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hcB : c ∉ B)
    (hBM : ¬ Subgroup.normalizer (B : Set G) ≤ M) :
    ∃ d ∈ B, d ≠ 1 ∧ ¬ Subgroup.centralizer ({d} : Set G) ≤ M := by
  by_contra hall
  push Not at hall
  apply hBM
  obtain ⟨⟨d, hdB⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (show B ≠ ⊥ from fun h => by rw [h, Subgroup.card_bot] at hB9; omega)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdc : d ∉ Subgroup.zpowers c :=
    not_mem_zpowers_of_not_mem (sec13Data_of_ctx195 hctx).orderOf_eq hdB hd1' hcB
  obtain ⟨E', hctx', -, hdE'⟩ :=
    exists_ctx195_of_mem h131 h1730 hspor h196 hctx hH (hBA hdB) hdc
  intro g hg
  refine mem_of_map_conj_le hctx.hyp191 hctx'.isE27 hctx'.mem_scriptM ?_
  rintro _ ⟨e, he, rfl⟩
  have hdg : g * d * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hg d).mp hdB
  have hdg1 : g * d * g⁻¹ ≠ 1 := fun h => hd1' (by
    rw [mul_inv_eq_one] at h
    exact mul_left_cancel (h.trans (mul_one g).symm))
  apply hall _ hdg hdg1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm : e * d = d * e :=
    congrArg Subtype.val (hctx'.isE27.1.1.is_comm.comm ⟨e, he⟩ ⟨d, hdE'⟩)
  change g * e * g⁻¹ * (g * d * g⁻¹) = (g * d * g⁻¹) * (g * e * g⁻¹)
  calc g * e * g⁻¹ * (g * d * g⁻¹) = g * (e * d) * g⁻¹ := by group
    _ = g * (d * e) * g⁻¹ := by rw [hcomm]
    _ = (g * d * g⁻¹) * (g * e * g⁻¹) := by group

end Main

end Step197Proof

open Step197Proof

theorem step197_of_hyperplane
    (h45 : Sec4.Item4_5)
    (h131 : Item131) (h1730 : Sec17.Item1730) (hspor : SporadicModels131)
    (hgap : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
      Ctx195 G A c L E M →
      Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) →
      ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 → c ∉ B →
        Subgroup.normalizer (B : Set G) ≤ M) :
    Step197 := by
  intro G _ _ A c L E M hctx
  rcases isSLThreePiTwo_or_exists_hyperplane h131 h1730 hspor (step196_of h45 h131 hspor) hctx
    with h | ⟨hH, B, hBA, hB9, hcB, hBM⟩
  · exact h
  · exact absurd (hgap G A c L E M hctx hH B hBA hB9 hcB) hBM

theorem step197_of_item181
    (h45 : Sec4.Item4_5)
    (h131 : Item131) (h1730 : Sec17.Item1730) (hspor : SporadicModels131)
    (h181 : Sec18.Item181_1) (h1812 : Sec18.Item181_2) (h198 : Step198) (h1910 : Step1910)
    (h1911 : Step1911) (h1911E : Step1911End) : Step197 := by
  intro G _ _ A c L E M hctx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h196 := step196_of h45 h131 hspor
  rcases isSLThreePiTwo_or_exists_hyperplane h131 h1730 hspor h196 hctx
    with h | ⟨hH, B, hBA, hB9, hcB, hBM⟩
  · exact h
  exfalso
  obtain ⟨d, hdB, hd1, hCd⟩ :=
    exists_centralizer_not_le h131 h1730 hspor h196 hctx hH hBA hB9 hcB hBM
  have hdc : d ∉ Subgroup.zpowers c :=
    not_mem_zpowers_of_not_mem (sec13Data_of_ctx195 hctx).orderOf_eq hdB hd1 hcB
  obtain ⟨F, hctxF, -, hdF⟩ := exists_ctx195_of_mem h131 h1730 hspor h196 hctx hH (hBA hdB) hdc
  have hdD : d ∈ F ⊓ A := ⟨hdF, hBA hdB⟩
  have hO2 := rank3II_19_10_O2_of_spor h131 hspor G A c L F M hctxF d hdD hdc hCd
  have h18 : Sec18Std G F M :=
    ⟨hctxF.toPartTwoStanding, hctxF.partTwoS_eq, hctxF.mem_partTwoT.1, hctxF.mem_scriptM⟩
  have hQ := pCoreOf_centralizer_ne_bot h181 h1812 hctxF.hyp191 h18 hdF hd1 hO2
  set Y := Subgroup.centralizer ({d} : Set G) with hY
  obtain ⟨H, hH', -⟩ := exists_mem_scriptM_of_isTwoLocal (X := (Y : Set G))
    (H := Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G))
    ⟨CFSG.Open.pCoreOf 2 Y, hQ, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y, rfl⟩
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hHM : H ≠ M := fun h => hCd (fun x hx => h ▸ hH'.2 hx)
  obtain ⟨K, hK, hLK, hK8⟩ := h198 G A c L F M hctxF
  have hKJ := h1910 G A c L F M hctxF K hK hLK hK8 d hdD hdc hCd H hH' hHM
  obtain ⟨hKL, hpar⟩ := h1911 G A c L F M hctxF K hK hLK hK8 d hdD hdc H hH' hHM hKJ
  exact h1911E G A c L F M hctxF K hK hLK hKL d hdD hdc H hH' hHM hKJ hpar

theorem step197_of
    (h4441 : Sec4.Item4_44_1)
    (h4442 : Sec4.Item4_44_2) (h45 : Sec4.Item4_5) (h131 : Item131) (h1730 : Sec17.Item1730)
    (hspor : SporadicModels131) (h198 : Step198) (h1910 : Step1910) (h1911 : Step1911)
    (h1911E : Step1911End) : Step197 :=
  step197_of_item181 h45 h131 h1730 hspor (Sec18.rank3II_18_1_1_of h4441)
    (Sec18.rank3II_18_1_2_of h4442 KFacts.KS18.ks18OuterInvolution) h198 h1910 h1911 h1911E

end CFSG.RankThree.PartTwo.Sec19
