module

public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalBorel
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Levi
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalVertexTwo
import CFSG.Quasithin.Recognition.St84.Gen.SemidirectExtendConj
import CFSG.Quasithin.Recognition.St84.Gen.D4qTrialityAutM
import CFSG.Quasithin.Recognition.St84.Gen.D4qTrialityVertexTwo
import CFSG.Quasithin.Recognition.St84.Gen.L2WeylComplement
import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalYPrelim
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas


public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
  CFSG.LocalAnalysis.EvenBN.TrialityD4
open CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

open Subgroup

variable {G X : Type} [Group G] [Group X] [Finite G] [Finite X]
  {L1 L2 S H : Subgroup G} {f : ℕ}

theorem B_inf_centralizer_J₂_le (hf : 2 ≤ f) (d : TrialityD4Data X (2 ^ f)) :
    d.B ⊓ Subgroup.centralizer (d.J₂ : Set X) ≤ d.leviLong ⊔ d.J₂ := by
  intro b hb
  obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
  have hJcomm : ∀ a ∈ d.J, ∀ c ∈ d.J, a * c = c * a := by
    rintro a ⟨ha, rfl⟩ c ⟨hc, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hJnormS : d.J ≤ Subgroup.normalizer (d.S : Set X) := by
    rw [d.normalizer_S]
    exact le_sup_right
  obtain ⟨s, hsS, j, hjJ, hb_eq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := d.S) (K := d.J) hJnormS).mp hbB
  have hsjC : j ∈ Subgroup.centralizer (d.J₂ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hJcomm j hjJ x (Subgroup.mem_inf.mp hx).1).symm
  have hsC : s ∈ Subgroup.centralizer (d.J₂ : Set X) := by
    rw [Subgroup.mem_centralizer_iff] at hbC ⊢
    intro x hx
    have hjx : j * x = x * j := (Subgroup.mem_centralizer_iff.mp hsjC) x hx |>.symm
    calc x * s = x * s * (j * j⁻¹) := by group
      _ = x * (s * j) * j⁻¹ := by group
      _ = x * b * j⁻¹ := by rw [← hb_eq]
      _ = b * x * j⁻¹ := by rw [hbC x hx]
      _ = s * j * x * j⁻¹ := by rw [← hb_eq]
      _ = s * (j * x) * j⁻¹ := by group
      _ = s * (x * j) * j⁻¹ := by rw [hjx]
      _ = s * x * j * j⁻¹ := by group
      _ = s * x := by group
  have hsU : s ∈ d.U₂ := by
    rw [← S_inf_centralizer_J₂ hf d]
    exact Subgroup.mem_inf.mpr ⟨hsS, hsC⟩
  have hsL : s ∈ d.leviLong := d.U₂_le_leviLong hsU
  have hjL : j ∈ d.leviLong ⊔ d.J₂ :=
    (sup_le_sup_right d.J₄_le_leviLong d.J₂) (d.J_le_J₄_sup_J₂ hjJ)
  rw [hb_eq]
  exact (d.leviLong ⊔ d.J₂).mul_mem (Subgroup.mem_sup_left hsL) hjL

private theorem exists_partner_of_mem_inf_B (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (QleP : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S)
    (Θ : ↥(pCoreOf 2 L2) ≃* ↥d.M)
    (hΘ : ∀ x : ↥(pCoreOf 2 L2), (Θ x : X) = (ψ ⟨x, QleP x.2⟩ : X))
    {t : G}
    (htR : t ∈ (L2 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔ (H ⊓ trivOTwoQuot L2))
    (htB : t ∈ bigB L1 L2 S) :
    ∃ t' ∈ d.leviLong ⊔ d.J₂,
      t' = (ψ ⟨t, Subgroup.mem_sup_right htB⟩ : X) ∧
        ∀ x y : ↥(pCoreOf 2 L2), (y : G) = t * (x : G) * t⁻¹ →
          (Θ y : X) = t' * (Θ x : X) * t'⁻¹ := by
  classical
  have hP : t ∈ L1 ⊔ bigB L1 L2 S := Subgroup.mem_sup_right htB
  let tP : ↥(L1 ⊔ bigB L1 L2 S) := ⟨t, hP⟩
  have htS : t ∈ S ⊔ H := by rw [hSH]; exact htB
  have hHnormS : H ≤ Subgroup.normalizer (S : Set G) :=
    hHB.trans ((hD.bigB_le_normalizer hH h1).trans inf_le_right)
  obtain ⟨s, hsS, h, hhH, htsh⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := S) (K := H) hHnormS).mp htS
  have hsB : s ∈ bigB L1 L2 S := Subgroup.mem_sup_right hsS
  have hhB : h ∈ bigB L1 L2 S := hHB hhH
  have hsP : s ∈ L1 ⊔ bigB L1 L2 S := Subgroup.mem_sup_right hsB
  have hhP : h ∈ L1 ⊔ bigB L1 L2 S := Subgroup.mem_sup_right hhB
  have hψtB : (ψ tP : X) ∈ d.B := by
    have htsh' : tP = ⟨s, hsP⟩ * ⟨h, hhP⟩ := Subtype.ext htsh
    rw [htsh', map_mul]
    exact (d.S ⊔ d.J).mul_mem (Subgroup.mem_sup_left ((hψS _).mp hsS))
      (Subgroup.mem_sup_right ((hψH _).mp hhH))
  have hH0cent : H ⊓ trivOTwoQuot L2 ≤
      Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hHcomm a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1).symm
  have hRcent : (L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔ (H ⊓ trivOTwoQuot L2)
      ≤ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G) :=
    sup_le inf_le_right hH0cent
  have htcent : (ψ tP : X) ∈ Subgroup.centralizer (d.J₂ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjJ : j ∈ d.J := (Subgroup.mem_inf.mp hj).1
    have hjNV : j ∈ Subgroup.normalizer (d.V : Set X) := d.J_le_normalizer_V hjJ
    let jP : ↥(L1 ⊔ bigB L1 L2 S) := ψ.symm ⟨j, hjNV⟩
    have hψjP : (ψ jP : X) = j := congrArg Subtype.val (ψ.apply_symm_apply ⟨j, hjNV⟩)
    have hjPH : (jP : G) ∈ H := (hψH jP).mpr (by rw [hψjP]; exact hjJ)
    have hjPH0 : (jP : G) ∈ H ⊓ trivOTwoQuot L2 :=
      (D4qLocalData.mem_torus_right_iff_mem_J₂ hf hH hD h1 hHB hSH hSinfH hHcard hHcomm
        d ψ hψS hψH jP).mpr (by rw [hψjP]; exact hj)
    have hcomm : (jP : G) * t = t * (jP : G) :=
      Subgroup.mem_centralizer_iff.mp (hRcent htR) (jP : G) hjPH0
    have hcommP : jP * tP = tP * jP := Subtype.ext hcomm
    let jNV : ↥(Subgroup.normalizer (d.V : Set X)) := ⟨j, hjNV⟩
    have hψjP' : ψ jP = jNV := ψ.apply_symm_apply ⟨j, hjNV⟩
    have hcalc : jNV * ψ tP = ψ tP * jNV := by
      calc jNV * ψ tP = ψ jP * ψ tP := by rw [hψjP']
        _ = ψ (jP * tP) := (map_mul ψ jP tP).symm
        _ = ψ (tP * jP) := by rw [hcommP]
        _ = ψ tP * ψ jP := map_mul ψ tP jP
        _ = ψ tP * jNV := by rw [hψjP']
    exact congrArg Subtype.val hcalc
  have ht'R' : (ψ tP : X) ∈ d.leviLong ⊔ d.J₂ :=
    B_inf_centralizer_J₂_le hf d ⟨hψtB, htcent⟩
  refine ⟨(ψ tP : X), ht'R', rfl, ?_⟩
  intro x y hxy
  have hxP : (x : G) ∈ L1 ⊔ bigB L1 L2 S := QleP x.2
  have hyP : (y : G) ∈ L1 ⊔ bigB L1 L2 S := QleP y.2
  have hconjP : (⟨y, hyP⟩ : ↥(L1 ⊔ bigB L1 L2 S)) = tP * ⟨x, hxP⟩ * tP⁻¹ :=
    Subtype.ext hxy
  have hcalc : ψ (tP * ⟨x, hxP⟩ * tP⁻¹) =
      ψ tP * ψ ⟨x, hxP⟩ * (ψ tP)⁻¹ := by rw [map_mul, map_mul, map_inv]
  calc (Θ y : X) = (ψ ⟨y, hyP⟩ : X) := hΘ y
    _ = (ψ (tP * ⟨x, hxP⟩ * tP⁻¹) : X) := by rw [hconjP]
    _ = (ψ tP * ψ ⟨x, hxP⟩ * (ψ tP)⁻¹ :
          ↥(Subgroup.normalizer (d.V : Set X))) := congrArg Subtype.val hcalc
    _ = (ψ tP : X) * (ψ ⟨x, hxP⟩ : X) * (ψ tP : X)⁻¹ := rfl
    _ = (ψ tP : X) * (Θ x : X) * (ψ tP : X)⁻¹ := by rw [hΘ x]

private theorem exists_weyl_lift_data (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    {w : G} (hwInv : ∀ t ∈ H ⊓ L2, w * t * w⁻¹ = t⁻¹)
    (hwCent : ∀ t ∈ H ⊓ trivOTwoQuot L2, w * t * w⁻¹ = t)
    {h : X} (hhJ : h ∈ d.J) :
    ∃ (hP : ↥(L1 ⊔ bigB L1 L2 S)) (t1 : G) (h0 : G)
      (t1P : ↥(L1 ⊔ bigB L1 L2 S)) (h0P : ↥(L1 ⊔ bigB L1 L2 S)),
      (ψ hP : X) = h ∧
      (t1P : G) = t1 ∧
      (h0P : G) = h0 ∧
      t1 ∈ H ⊓ L2 ∧
      h0 ∈ H ⊓ trivOTwoQuot L2 ∧
      w * (hP : G) * w⁻¹ = t1⁻¹ * h0 ∧
      (ψ t1P : X) * (ψ h0P : X) = h := by
  classical
  have hhNV : h ∈ Subgroup.normalizer (d.V : Set X) := d.J_le_normalizer_V hhJ
  let hP : ↥(L1 ⊔ bigB L1 L2 S) := ψ.symm ⟨h, hhNV⟩
  have hψhP : (ψ hP : X) = h :=
    congrArg Subtype.val (ψ.apply_symm_apply ⟨h, hhNV⟩)
  have hhPH : (hP : G) ∈ H := (hψH hP).mpr (by rw [hψhP]; exact hhJ)
  have hTR := hD.torus_right_of_hall hf hH h1 hHB hSH hSinfH hHcard hHcomm
  have hHsup : (H ⊓ L2) ⊔ (H ⊓ trivOTwoQuot L2) = H := hTR.2.2.1
  have hH0norm : (H ⊓ trivOTwoQuot L2) ≤
      Subgroup.normalizer ((H ⊓ L2 : Subgroup G) : Set G) := by
    have hcent : (H ⊓ trivOTwoQuot L2) ≤
        Subgroup.centralizer ((H ⊓ L2 : Subgroup G) : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (hHcomm z (Subgroup.mem_inf.mp hz).1 t (Subgroup.mem_inf.mp ht).1).symm
    exact hcent.trans (centralizer_le_normalizer _)
  obtain ⟨t1, ht1, h0, hh0, ht1h0⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := H ⊓ L2) (K := H ⊓ trivOTwoQuot L2) hH0norm).mp
      (by rw [hHsup]; exact hhPH)
  have ht1H : t1 ∈ H := (Subgroup.mem_inf.mp ht1).1
  have hh0H : h0 ∈ H := (Subgroup.mem_inf.mp hh0).1
  have ht1P : t1 ∈ L1 ⊔ bigB L1 L2 S :=
    Subgroup.mem_sup_right (hHB ht1H)
  have hh0P : h0 ∈ L1 ⊔ bigB L1 L2 S :=
    Subgroup.mem_sup_right (hHB hh0H)
  let t1P : ↥(L1 ⊔ bigB L1 L2 S) := ⟨t1, ht1P⟩
  let h0P : ↥(L1 ⊔ bigB L1 L2 S) := ⟨h0, hh0P⟩
  have hP_eq : hP = t1P * h0P := Subtype.ext ht1h0
  have hψhP' : (ψ t1P : X) * (ψ h0P : X) = h := by
    calc (ψ t1P : X) * (ψ h0P : X) =
          ((ψ t1P * ψ h0P : ↥(Subgroup.normalizer (d.V : Set X))) : X) := rfl
      _ = (ψ (t1P * h0P) : X) :=
          congrArg Subtype.val (map_mul ψ t1P h0P).symm
      _ = (ψ hP : X) := by rw [← hP_eq]
      _ = h := hψhP
  have hwh : w * (hP : G) * w⁻¹ = t1⁻¹ * h0 := by
    rw [ht1h0]
    calc w * (t1 * h0) * w⁻¹ = (w * t1 * w⁻¹) * (w * h0 * w⁻¹) := by group
      _ = t1⁻¹ * h0 := by rw [hwInv t1 ht1, hwCent h0 hh0]
  exact ⟨hP, t1, h0, t1P, h0P, hψhP, rfl, rfl, ht1, hh0, hwh, hψhP'⟩

private theorem exists_weyl_lift_vconj (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    {h : X} (hhJ : h ∈ d.J)
    {hP : ↥(L1 ⊔ bigB L1 L2 S)} {t1 h0 : G}
    {t1P : ↥(L1 ⊔ bigB L1 L2 S)} {h0P : ↥(L1 ⊔ bigB L1 L2 S)}
    (hψhP : (ψ hP : X) = h)
    (ht1P : (t1P : G) = t1) (hh0P : (h0P : G) = h0)
    (ht1 : t1 ∈ H ⊓ L2) (hh0 : h0 ∈ H ⊓ trivOTwoQuot L2)
    (hψhP' : (ψ t1P : X) * (ψ h0P : X) = h) :
    ∃ (h1' : G) (h1'P : ↥(L1 ⊔ bigB L1 L2 S)),
      h1' = t1⁻¹ * h0 ∧
      (h1'P : G) = h1' ∧
      h1' ∈ (L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔ (H ⊓ trivOTwoQuot L2) ∧
      h1' ∈ bigB L1 L2 S ∧
      d.v * (ψ h1'P : X) * d.v = h := by
  classical
  have ht1H : t1 ∈ H := (Subgroup.mem_inf.mp ht1).1
  have ht1L : t1 ∈ L2 := (Subgroup.mem_inf.mp ht1).2
  have hh0H : h0 ∈ H := (Subgroup.mem_inf.mp hh0).1
  let h1' : G := t1⁻¹ * h0
  have hh1'B : h1' ∈ bigB L1 L2 S :=
    hHB (H.mul_mem (H.inv_mem ht1H) hh0H)
  have hh1'P : h1' ∈ L1 ⊔ bigB L1 L2 S := Subgroup.mem_sup_right hh1'B
  let h1'P : ↥(L1 ⊔ bigB L1 L2 S) := ⟨h1', hh1'P⟩
  have h1'P_eq : h1'P = t1P⁻¹ * h0P := by
    apply Subtype.ext
    change h1' = (t1P : G)⁻¹ * (h0P : G)
    rw [ht1P, hh0P]
  have hψh1' : (ψ h1'P : X) = (ψ t1P : X)⁻¹ * (ψ h0P : X) := by
    calc (ψ h1'P : X) = (ψ (t1P⁻¹ * h0P) : X) := by rw [h1'P_eq]
      _ = ((ψ (t1P⁻¹) * ψ h0P : ↥(Subgroup.normalizer (d.V : Set X))) : X) :=
          congrArg Subtype.val (map_mul ψ t1P⁻¹ h0P)
      _ = ((ψ t1P)⁻¹ * ψ h0P : ↥(Subgroup.normalizer (d.V : Set X))) := by rw [map_inv]
      _ = (ψ t1P : X)⁻¹ * (ψ h0P : X) := rfl
  have hψt1J4 : (ψ t1P : X) ∈ d.J₄ :=
    (D4qLocalData.mem_inf_right_iff_mem_J₄ hf hH hD h1 hHB hSH hSinfH hHcard hHcomm
      d ψ hψS hψH t1P).mp (by rw [ht1P]; exact ht1)
  have hψh0J2 : (ψ h0P : X) ∈ d.J₂ :=
    (D4qLocalData.mem_torus_right_iff_mem_J₂ hf hH hD h1 hHB hSH hSinfH hHcard hHcomm
      d ψ hψS hψH h0P).mp (by rw [hh0P]; exact hh0)
  have hconj_val : ∀ z : X, d.v * z * d.v = MulAut.conj d.v z := by
    intro z
    rw [MulAut.conj_apply, d.v_inv]
  have hvt1 : d.v * (ψ t1P : X) * d.v = (ψ t1P : X)⁻¹ :=
    d.v_conj_eq_inv_of_mem_J₄ hψt1J4
  have hv0 : d.v * (ψ h0P : X) * d.v = ψ h0P := by
    have hc : (ψ h0P : X) * d.v = d.v * (ψ h0P : X) :=
      (Subgroup.mem_centralizer_iff.mp d.v_mem_centralizer_J₂) (ψ h0P : X) hψh0J2
    calc d.v * (ψ h0P : X) * d.v = ((ψ h0P : X) * d.v) * d.v := by rw [← hc]
      _ = ψ h0P := by rw [mul_assoc, d.v_mul_self, mul_one]
  have hv_h1' : d.v * (ψ h1'P : X) * d.v = h := by
    rw [hψh1']
    calc d.v * ((ψ t1P : X)⁻¹ * (ψ h0P : X)) * d.v
        = MulAut.conj d.v ((ψ t1P : X)⁻¹) * MulAut.conj d.v (ψ h0P : X) := by
          rw [hconj_val, map_mul]
      _ = h := by
          rw [map_inv, ← hconj_val (ψ t1P), hvt1, inv_inv,
            ← hconj_val (ψ h0P), hv0, hψhP']
  have ht1K : t1 ∈ L2 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨ht1L, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hHcomm z (Subgroup.mem_inf.mp hz).1 t1 ht1H
  refine ⟨h1', h1'P, rfl, rfl, ?_, hh1'B, hv_h1'⟩
  exact ((L2 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
    (H ⊓ trivOTwoQuot L2)).mul_mem
    (Subgroup.mem_sup_left (Subgroup.inv_mem _ ht1K))
    (Subgroup.mem_sup_right hh0)

private theorem weylAut_conj_eq (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (QleP : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S)
    (Θ : ↥(pCoreOf 2 L2) ≃* ↥d.M)
    (hΘ : ∀ x : ↥(pCoreOf 2 L2), (Θ x : X) = (ψ ⟨x, QleP x.2⟩ : X))
    {w : G} {cw : ↥(pCoreOf 2 L2) ≃* ↥(pCoreOf 2 L2)}
    (hcw : ∀ x : ↥(pCoreOf 2 L2), (cw x : G) = w * (x : G) * w⁻¹)
    {h : X} (hhJ : h ∈ d.J)
    {hP : ↥(L1 ⊔ bigB L1 L2 S)} {h1' : G}
    {h1'P : ↥(L1 ⊔ bigB L1 L2 S)}
    (h1'P_val : (h1'P : G) = h1')
    (hψhP : (ψ hP : X) = h)
    (hwh : w * (hP : G) * w⁻¹ = h1')
    (hh1'R : h1' ∈ (L2 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔ (H ⊓ trivOTwoQuot L2))
    (hh1'B : h1' ∈ bigB L1 L2 S)
    (hv_h1' : d.v * (ψ h1'P : X) * d.v = h)
    {x y : ↥d.M} (hxy : (y : X) = h * (x : X) * h⁻¹) :
    (Θ (cw (Θ.symm y)) : X) =
      (ψ h1'P : X) * (Θ (cw (Θ.symm x)) : X) * (ψ h1'P : X)⁻¹ := by
  classical
  have hhPH : (hP : G) ∈ H := (hψH hP).mpr (by rw [hψhP]; exact hhJ)
  have hh1NQ : (hP : G) ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    hH.bigB_le_normalizer_pCoreOf_right (hHB hhPH)
  have hzQ : (hP : G) * (Θ.symm x : G) * (hP : G)⁻¹ ∈ pCoreOf 2 L2 :=
    (Subgroup.mem_normalizer_iff.mp hh1NQ (Θ.symm x : G)).mp (Θ.symm x).2
  let z : ↥(pCoreOf 2 L2) :=
    ⟨(hP : G) * (Θ.symm x : G) * (hP : G)⁻¹, hzQ⟩
  have hψx : (ψ ⟨Θ.symm x, QleP (Θ.symm x).2⟩ : X) = (x : X) := by
    rw [← hΘ (Θ.symm x)]
    exact congrArg Subtype.val (Θ.apply_symm_apply x)
  have hΘz : (Θ z : X) = h * (x : X) * h⁻¹ := by
    rw [hΘ z]
    have hzP_eq : (⟨z, QleP z.2⟩ : ↥(L1 ⊔ bigB L1 L2 S)) =
        hP * ⟨Θ.symm x, QleP (Θ.symm x).2⟩ * hP⁻¹ := Subtype.ext rfl
    calc (ψ ⟨z, QleP z.2⟩ : X)
        = (ψ (hP * ⟨Θ.symm x, QleP (Θ.symm x).2⟩ * hP⁻¹) : X) := by rw [hzP_eq]
      _ = ((ψ hP * ψ ⟨Θ.symm x, QleP (Θ.symm x).2⟩ * (ψ hP)⁻¹ :
            ↥(Subgroup.normalizer (d.V : Set X))) : X) :=
          congrArg Subtype.val (by rw [map_mul, map_mul, map_inv])
      _ = (ψ hP : X) * (ψ ⟨Θ.symm x, QleP (Θ.symm x).2⟩ : X) *
            (ψ hP : X)⁻¹ := rfl
      _ = h * (x : X) * h⁻¹ := by rw [hψhP, hψx]
  have hyQ : Θ.symm y = z := by
    have hΘzy : Θ z = y := Subtype.ext (hΘz.trans hxy.symm)
    rw [← hΘzy, Θ.symm_apply_apply]
  have hcw_yx : (cw (Θ.symm y) : G) = h1' * (cw (Θ.symm x) : G) * h1'⁻¹ := by
    rw [hcw, hcw, hyQ]
    change w * ((hP : G) * (Θ.symm x : G) * (hP : G)⁻¹) * w⁻¹ =
      h1' * (w * (Θ.symm x : G) * w⁻¹) * h1'⁻¹
    rw [← hwh]
    group
  obtain ⟨r', hr'R', hr'eq, hr'part⟩ :=
    exists_partner_of_mem_inf_B hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
      QleP Θ hΘ hh1'R hh1'B
  have hpart := hr'part (cw (Θ.symm x)) (cw (Θ.symm y)) hcw_yx
  rw [hr'eq] at hpart
  rw [← show (ψ h1'P : X) = (ψ ⟨h1', Subgroup.mem_sup_right hh1'B⟩ : X) from
    congrArg (fun z : ↥(L1 ⊔ bigB L1 L2 S) => (ψ z : X)) (Subtype.ext h1'P_val)] at hpart
  exact hpart

private theorem weylAut_commutes_J (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (QleP : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S)
    (Θ : ↥(pCoreOf 2 L2) ≃* ↥d.M)
    (hΘ : ∀ x : ↥(pCoreOf 2 L2), (Θ x : X) = (ψ ⟨x, QleP x.2⟩ : X))
    {w : G}
    (hwInv : ∀ t ∈ H ⊓ L2, w * t * w⁻¹ = t⁻¹)
    (hwCent : ∀ t ∈ H ⊓ trivOTwoQuot L2, w * t * w⁻¹ = t)
    {cw : ↥(pCoreOf 2 L2) ≃* ↥(pCoreOf 2 L2)}
    (hcw : ∀ x : ↥(pCoreOf 2 L2), (cw x : G) = w * (x : G) * w⁻¹)
    {u : ↥d.M ≃* ↥d.M}
    (huval : ∀ m : ↥d.M,
      (u m : X) = d.v * (Θ (cw (Θ.symm m)) : X) * d.v)
    (hconj_val : ∀ z : X, d.v * z * d.v = MulAut.conj d.v z)
    (hconj2 : ∀ z : X, d.v * (d.v * z * d.v) * d.v = z) :
    ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * (x : X) * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹ := by
  intro h hhJ x y hxy
  obtain ⟨hP, t1, h0, t1P, h0P, hψhP, ht1P, hh0P, ht1, hh0, hwh, hψhP'⟩ :=
    exists_weyl_lift_data hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
      hwInv hwCent hhJ
  obtain ⟨h1', h1'P, h1'_eq, h1'P_val, hh1'R, hh1'B, hv_h1'⟩ :=
    exists_weyl_lift_vconj hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
      hhJ hψhP ht1P hh0P ht1 hh0 hψhP'
  have hwh' : w * (hP : G) * w⁻¹ = h1' := by rw [hwh, h1'_eq]
  have hΘ_cwy := weylAut_conj_eq hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS
    hψH QleP Θ hΘ hcw hhJ h1'P_val hψhP hwh' hh1'R hh1'B hv_h1' hxy
  have huΘy : (u y : X) = MulAut.conj d.v (Θ (cw (Θ.symm y)) : X) := by
    rw [huval y, hconj_val]
  have huΘx : (u x : X) = MulAut.conj d.v (Θ (cw (Θ.symm x)) : X) := by
    rw [huval x, hconj_val]
  calc (u y : X) = MulAut.conj d.v (Θ (cw (Θ.symm y)) : X) := huΘy
    _ = MulAut.conj d.v ((ψ h1'P : X) * (Θ (cw (Θ.symm x)) : X) *
          (ψ h1'P : X)⁻¹) := by rw [hΘ_cwy]
    _ = MulAut.conj d.v (ψ h1'P : X) *
          MulAut.conj d.v (Θ (cw (Θ.symm x)) : X) *
          MulAut.conj d.v ((ψ h1'P : X)⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = h * MulAut.conj d.v (Θ (cw (Θ.symm x)) : X) * h⁻¹ := by
          rw [← hconj_val (ψ h1'P), hv_h1', map_inv, ← hconj_val (ψ h1'P), hv_h1']
    _ = h * (u x : X) * h⁻¹ := by rw [huΘx]

private theorem exists_weyl_aut (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (QleP : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S)
    (Θ : ↥(pCoreOf 2 L2) ≃* ↥d.M)
    (hΘ : ∀ x : ↥(pCoreOf 2 L2), (Θ x : X) = (ψ ⟨x, QleP x.2⟩ : X))
    {w : G}
    (hwK : w ∈ L2 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G))
    (hwInv : ∀ t ∈ H ⊓ L2, w * t * w⁻¹ = t⁻¹)
    (hwCent : ∀ t ∈ H ⊓ trivOTwoQuot L2, w * t * w⁻¹ = t) :
    ∃ (cw : ↥(pCoreOf 2 L2) ≃* ↥(pCoreOf 2 L2)) (u : ↥d.M ≃* ↥d.M),
      (∀ x : ↥(pCoreOf 2 L2), (cw x : G) = w * (x : G) * w⁻¹) ∧
      (∀ m : ↥d.M, (u m : X) = d.v * (Θ (cw (Θ.symm m)) : X) * d.v) ∧
      (∀ h ∈ d.J, ∀ x y : ↥d.M,
        (y : X) = h * (x : X) * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹) := by
  classical
  have hwL2 : w ∈ L2 := (Subgroup.mem_inf.mp hwK).1
  have hQnorm : w ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) L2 hwL2
  have hQmap : (pCoreOf 2 L2).map (↑(MulAut.conj w)) = pCoreOf 2 L2 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hQnorm
  let cw : ↥(pCoreOf 2 L2) ≃* ↥(pCoreOf 2 L2) :=
    (MulEquiv.subgroupMap (MulAut.conj w) (pCoreOf 2 L2)).trans
      (MulEquiv.subgroupCongr hQmap)
  have hcw : ∀ x : ↥(pCoreOf 2 L2), (cw x : G) = w * (x : G) * w⁻¹ := by
    intro x
    simp only [cw, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have hvM : d.v ∈ Subgroup.normalizer (d.M : Set X) :=
    d.leviLong_le_normalizer_M d.v_mem_leviLong
  have hMmap : d.M.map (↑(MulAut.conj d.v)) = d.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hvM
  let cv : ↥d.M ≃* ↥d.M :=
    (MulEquiv.subgroupMap (MulAut.conj d.v) d.M).trans (MulEquiv.subgroupCongr hMmap)
  have hcv : ∀ m : ↥d.M, (cv m : X) = d.v * (m : X) * d.v := by
    intro m
    simp only [cv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply, d.v_inv]
  let c : ↥d.M ≃* ↥d.M := Θ.symm.trans (cw.trans Θ)
  let u : ↥d.M ≃* ↥d.M := c.trans cv
  have huval : ∀ m : ↥d.M, (u m : X) = d.v * (Θ (cw (Θ.symm m)) : X) * d.v := by
    intro m
    simp only [u, c, MulEquiv.trans_apply, hcv]
  have hconj_val : ∀ z : X, d.v * z * d.v = MulAut.conj d.v z := by
    intro z
    rw [MulAut.conj_apply, d.v_inv]
  have hconj2 : ∀ z : X, d.v * (d.v * z * d.v) * d.v = z := by
    intro z
    calc d.v * (d.v * z * d.v) * d.v = (d.v * d.v) * z * (d.v * d.v) := by group
      _ = z := by rw [d.v_mul_self]; group
  refine ⟨cw, u, hcw, huval, ?_⟩
  exact weylAut_commutes_J hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
    QleP Θ hΘ hwInv hwCent hcw huval hconj_val hconj2

private theorem exists_partner_weyl (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (QleP : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S)
    (Θ : ↥(pCoreOf 2 L2) ≃* ↥d.M)
    (hΘ : ∀ x : ↥(pCoreOf 2 L2), (Θ x : X) = (ψ ⟨x, QleP x.2⟩ : X))
    {w : G}
    (hwK : w ∈ L2 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G))
    (hwInv : ∀ t ∈ H ⊓ L2, w * t * w⁻¹ = t⁻¹)
    (hwCent : ∀ t ∈ H ⊓ trivOTwoQuot L2, w * t * w⁻¹ = t) :
    ∃ t' ∈ d.leviLong ⊔ d.J₂,
      ∀ x y : ↥(pCoreOf 2 L2), (y : G) = w * (x : G) * w⁻¹ →
        (Θ y : X) = t' * (Θ x : X) * t'⁻¹ := by
  classical
  obtain ⟨cw, u, hcw, huval, huJ⟩ :=
    exists_weyl_aut hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
      QleP Θ hΘ hwK hwInv hwCent
  obtain ⟨h2, hh2J, hh2⟩ := exists_mem_J_conj_eq_of_commute hf d u huJ
  refine ⟨d.v * h2, ?_, ?_⟩
  · exact (d.leviLong ⊔ d.J₂).mul_mem (Subgroup.mem_sup_left d.v_mem_leviLong)
      ((sup_le_sup_right d.J₄_le_leviLong d.J₂) (d.J_le_J₄_sup_J₂ hh2J))
  · intro x y hxy
    have hcwx : cw x = y := by
      apply Subtype.ext
      rw [hcw]
      exact hxy.symm
    have huΘx : (u (Θ x) : X) = d.v * (Θ y : X) * d.v := by
      rw [huval (Θ x), Θ.symm_apply_apply, hcwx]
    have hB : d.v * (Θ y : X) * d.v = h2 * (Θ x : X) * h2⁻¹ := by
      rw [← huΘx]
      exact hh2 (Θ x)
    have hconj2 : ∀ z : X, d.v * (d.v * z * d.v) * d.v = z := by
      intro z
      calc d.v * (d.v * z * d.v) * d.v = (d.v * d.v) * z * (d.v * d.v) := by group
        _ = z := by rw [d.v_mul_self]; group
    calc (Θ y : X) = d.v * (h2 * (Θ x : X) * h2⁻¹) * d.v := by
          rw [← hB]
          exact (hconj2 (Θ y)).symm
      _ = (d.v * h2) * (Θ x : X) * (d.v * h2)⁻¹ := by
            rw [_root_.mul_inv_rev, d.v_inv]
            group

private theorem exists_iso_M (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (hHB : H ≤ bigB L1 L2 S) (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (QleP : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S) :
    ∃ Θ : ↥(pCoreOf 2 L2) ≃* ↥d.M,
      ∀ x : ↥(pCoreOf 2 L2), (Θ x : X) = (ψ ⟨x, QleP x.2⟩ : X) := by
  classical
  have hψQ : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L2 ↔
      (ψ x : X) ∈ d.M :=
    D4qLocalData.mem_pCoreOf_right_iff_mem_M hH hD hHB d ψ hψS hψH
  let Θhom : ↥(pCoreOf 2 L2) →* ↥d.M :=
    { toFun := fun x => ⟨ψ ⟨x, QleP x.2⟩, (hψQ ⟨x, QleP x.2⟩).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change (ψ ⟨((x * y : ↥(pCoreOf 2 L2)) : G), QleP (x * y).2⟩ : X) =
          (ψ ⟨x, QleP x.2⟩ : X) * (ψ ⟨y, QleP y.2⟩ : X)
        have hxy : (⟨((x * y : ↥(pCoreOf 2 L2)) : G), QleP (x * y).2⟩ :
              ↥(L1 ⊔ bigB L1 L2 S)) =
            ⟨x, QleP x.2⟩ * ⟨y, QleP y.2⟩ := Subtype.ext rfl
        rw [hxy, map_mul]
        rfl) }
  have hQcard : Nat.card ↥(pCoreOf 2 L2) = Nat.card ↥d.M := by
    rw [hD.card_right, d.card_M, ← pow_mul, Nat.mul_comm]
  have hΘinj : Function.Injective Θhom := by
    intro x y hxy
    have h1 : (ψ ⟨x, QleP x.2⟩ : X) = (ψ ⟨y, QleP y.2⟩ : X) :=
      congrArg (fun z : ↥d.M => (z : X)) hxy
    have h2 : (⟨x, QleP x.2⟩ : ↥(L1 ⊔ bigB L1 L2 S)) = ⟨y, QleP y.2⟩ :=
      ψ.injective (Subtype.ext h1)
    exact Subtype.ext (congrArg (fun z : ↥(L1 ⊔ bigB L1 L2 S) => (z : G)) h2)
  let Θ : ↥(pCoreOf 2 L2) ≃* ↥d.M := MulEquiv.ofBijective Θhom
    ((Nat.bijective_iff_injective_and_card Θhom).mpr ⟨hΘinj, hQcard⟩)
  exact ⟨Θ, fun _ => rfl⟩

private theorem exists_weyl_element (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J) :
    ∃ w : G,
      w ∈ L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G) ∧
      (∀ t ∈ H ⊓ L2, w * t * w⁻¹ = t⁻¹) ∧
      Subgroup.closure
        ((((L2 ⊓ Subgroup.centralizer
            ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊓
          Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪ {w}) =
        (L2 ⊓ Subgroup.centralizer
          ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) := by
  classical
  obtain ⟨c2⟩ := hD.exists_coordRight hH
  letI := c2.field
  letI := c2.fintype
  haveI : CharP c2.F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c2.card])
  have hTR := hD.torus_right_of_hall hf hH h1 hHB hSH hSinfH hHcard hHcomm
  have hHnormS : H ≤ Subgroup.normalizer (S : Set G) :=
    hHB.trans ((hD.bigB_le_normalizer hH h1).trans inf_le_right)
  have hTN : H ⊓ L2 ≤ Subgroup.normalizer (S : Set G) :=
    inf_le_left.trans hHnormS
  have hTcard : Nat.card ↥(H ⊓ L2) = Nat.card c2.F - 1 := by
    rw [hTR.1, c2.card]
  obtain ⟨⟨hsupQK, hinfQK⟩, hHL2K, -, -, -, -, -⟩ :=
    hD.vertexTwo_right hf hH h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
  obtain ⟨w, hwK, hwInv, hwgen⟩ :=
    exists_weyl_of_complement (Q := pCoreOf 2 L2)
      (K := L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G))
      (T := H ⊓ L2) (S := S) (L := L2)
      c2.α c2.surj c2.ker (hD.le_right hH) c2.memS hsupQK hinfQK hHL2K hTN hTcard
  exact ⟨w, hwK, hwInv, hwgen⟩

private theorem closure_T_eq_R (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (hHB : H ≤ bigB L1 L2 S) {w : G}
    (hwK : w ∈ L2 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G))
    (hwgen : Subgroup.closure
      ((((L2 ⊓ Subgroup.centralizer
          ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊓
        Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪ {w}) =
      (L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G))) :
    Subgroup.closure
      (((((L2 ⊓ Subgroup.centralizer
          ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L2)) ⊓ bigB L1 L2 S : Subgroup G) : Set G) ∪ {w}) =
      (L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔ (H ⊓ trivOTwoQuot L2) := by
  classical
  let K2 : Subgroup G := L2 ⊓ Subgroup.centralizer
    ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)
  let H0 : Subgroup G := H ⊓ trivOTwoQuot L2
  let R : Subgroup G := K2 ⊔ H0
  let T : Set G := ((R ⊓ bigB L1 L2 S : Subgroup G) : Set G) ∪ {w}
  change Subgroup.closure T = R
  have hwgen' : Subgroup.closure
      (((K2 ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪ {w}) = K2 := hwgen
  have hborel : borelOf L2 S = L2 ⊓ Subgroup.normalizer (S : Set G) := by
    rw [borelOf, inf_eq_left.mpr (hD.le_right hH)]
  have hL2NS : L2 ⊓ Subgroup.normalizer (S : Set G) ≤ bigB L1 L2 S := by
    rw [← hborel]
    exact le_sup_right.trans le_sup_left
  apply le_antisymm
  · refine (Subgroup.closure_le R).mpr ?_
    rintro x (hx | hx)
    · exact hx.1
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.mem_sup_left hwK
  · change (L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔ (H ⊓ trivOTwoQuot L2) ≤
      Subgroup.closure T
    rw [← hwgen]
    refine sup_le ?_ ?_
    · refine Subgroup.closure_mono ?_
      rintro x (hx | hx)
      · exact Or.inl ⟨Subgroup.mem_sup_left hx.1,
          hL2NS ⟨(Subgroup.mem_inf.mp hx.1).1, hx.2⟩⟩
      · exact Or.inr hx
    · intro x hx
      exact Subgroup.subset_closure
        (Or.inl ⟨Subgroup.mem_sup_right hx, hHB (Subgroup.mem_inf.mp hx).1⟩)

private theorem partners_of_T (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (QleP : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S)
    (Θ : ↥(pCoreOf 2 L2) ≃* ↥d.M)
    (hΘ : ∀ x : ↥(pCoreOf 2 L2), (Θ x : X) = (ψ ⟨x, QleP x.2⟩ : X))
    {w : G}
    (hwK : w ∈ L2 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G))
    (hwInv : ∀ t ∈ H ⊓ L2, w * t * w⁻¹ = t⁻¹)
    (hwCent : ∀ t ∈ H ⊓ trivOTwoQuot L2, w * t * w⁻¹ = t) :
    ∀ t : G,
      t ∈ (((((L2 ⊓ Subgroup.centralizer
          ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L2)) ⊓ bigB L1 L2 S : Subgroup G) : Set G) ∪ {w}) →
      ∃ t' ∈ d.leviLong ⊔ d.J₂,
        ∀ x y : ↥(pCoreOf 2 L2), (y : G) = t * (x : G) * t⁻¹ →
          (Θ y : X) = t' * (Θ x : X) * t'⁻¹ := by
  intro t ht
  rcases ht with ht | ht
  · obtain ⟨htR, htB⟩ := ht
    exact (exists_partner_of_mem_inf_B hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ
      hψS hψH QleP Θ hΘ htR htB).imp fun t' ht' => ⟨ht'.1, ht'.2.2⟩
  · rw [Set.mem_singleton_iff] at ht
    subst ht
    exact exists_partner_weyl hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS
      hψH QleP Θ hΘ hwK hwInv hwCent

private theorem extension_agrees_on_B (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (QleP : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S)
    (Θ : ↥(pCoreOf 2 L2) ≃* ↥d.M)
    (hΘ : ∀ x : ↥(pCoreOf 2 L2), (Θ x : X) = (ψ ⟨x, QleP x.2⟩ : X))
    (hQR : (pCoreOf 2 L2) ⊔
      ((L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
          (H ⊓ trivOTwoQuot L2)) = L2 ⊔ bigB L1 L2 S)
    (hRnorm : ((L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
          (H ⊓ trivOTwoQuot L2)) ≤
      Subgroup.normalizer (pCoreOf 2 L2 : Set G))
    (ψ' : ↥((pCoreOf 2 L2) ⊔
      ((L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
          (H ⊓ trivOTwoQuot L2))) ≃* ↥(d.M ⊔ (d.leviLong ⊔ d.J₂)))
    (hψ'Q : ∀ x : ↥(pCoreOf 2 L2),
      (ψ' ⟨x, Subgroup.mem_sup_left x.2⟩ : X) = (Θ x : X))
    (hψ'partner : ∀ (r : G) (hr : r ∈
        (L2 ⊓ Subgroup.centralizer
          ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
            (H ⊓ trivOTwoQuot L2)) (r' : X), r' ∈ d.leviLong ⊔ d.J₂ →
      (∀ x y : ↥(pCoreOf 2 L2), (y : G) = r * (x : G) * r⁻¹ →
        (Θ y : X) = r' * (Θ x : X) * r'⁻¹) →
      (ψ' ⟨r, Subgroup.mem_sup_right hr⟩ : X) = r') :
    ∀ (b : G) (hb : b ∈ bigB L1 L2 S),
      ∃ (hbQR : b ∈ (pCoreOf 2 L2) ⊔
        ((L2 ⊓ Subgroup.centralizer
          ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
            (H ⊓ trivOTwoQuot L2))),
      (ψ' ⟨b, hbQR⟩ : X) = (ψ ⟨b, Subgroup.mem_sup_right hb⟩ : X) := by
  classical
  let Q : Subgroup G := pCoreOf 2 L2
  let H0 : Subgroup G := H ⊓ trivOTwoQuot L2
  let K2 : Subgroup G := L2 ⊓ Subgroup.centralizer (H0 : Set G)
  let R : Subgroup G := K2 ⊔ H0
  change ∀ (b : G) (hb : b ∈ bigB L1 L2 S),
      ∃ (hbQR : b ∈ Q ⊔ R),
        (ψ' ⟨b, hbQR⟩ : X) = (ψ ⟨b, Subgroup.mem_sup_right hb⟩ : X)
  have hQR' : Q ⊔ R = L2 ⊔ bigB L1 L2 S := hQR
  have hRnorm' : R ≤ Subgroup.normalizer (Q : Set G) := hRnorm
  intro b hb
  have hbQR : b ∈ Q ⊔ R := by
    rw [hQR']
    exact Subgroup.mem_sup_right hb
  refine ⟨hbQR, ?_⟩
  obtain ⟨x, hxQ, r, hrR, hxr⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := Q) (K := R) hRnorm').mp hbQR
  have hxS : x ∈ S := hH.pCoreOf_le_right hxQ
  have hxB : x ∈ bigB L1 L2 S := Subgroup.mem_sup_right hxS
  have hrB : r ∈ bigB L1 L2 S := by
    have hr_eq : r = x⁻¹ * b := by rw [hxr]; group
    rw [hr_eq]
    exact (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hxB) hb
  obtain ⟨r', hr'R', hr'eq, hr'part⟩ :=
    exists_partner_of_mem_inf_B hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
      QleP Θ hΘ (t := r) (by change r ∈ (L2 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔ (H ⊓ trivOTwoQuot L2); exact hrR)
      hrB
  have hψ'r : (ψ' ⟨r, Subgroup.mem_sup_right hrR⟩ : X) =
      (ψ ⟨r, Subgroup.mem_sup_right hrB⟩ : X) := by
    rw [hψ'partner r hrR r' hr'R' hr'part]
    exact hr'eq
  have hψ'x : (ψ' ⟨x, Subgroup.mem_sup_left hxQ⟩ : X) =
      (ψ ⟨x, Subgroup.mem_sup_right hxB⟩ : X) := by
    rw [hψ'Q ⟨x, hxQ⟩, hΘ ⟨x, hxQ⟩]
  have hbprod : (ψ ⟨b, Subgroup.mem_sup_right hb⟩ : X) =
      (ψ ⟨x, Subgroup.mem_sup_right hxB⟩ : X) *
        (ψ ⟨r, Subgroup.mem_sup_right hrB⟩ : X) := by
    have hP_eq : (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(L1 ⊔ bigB L1 L2 S)) =
        ⟨x, Subgroup.mem_sup_right hxB⟩ * ⟨r, Subgroup.mem_sup_right hrB⟩ :=
      Subtype.ext hxr
    rw [hP_eq, map_mul]
    rfl
  have hψ'b : (ψ' ⟨b, hbQR⟩ : X) = (ψ ⟨b, Subgroup.mem_sup_right hb⟩ : X) := by
    have hsplit : (⟨b, hbQR⟩ : ↥(Q ⊔ R)) =
        ⟨x, Subgroup.mem_sup_left hxQ⟩ * ⟨r, Subgroup.mem_sup_right hrR⟩ :=
      Subtype.ext hxr
    have hmap : ψ' (⟨x, Subgroup.mem_sup_left hxQ⟩ * ⟨r, Subgroup.mem_sup_right hrR⟩) =
        ψ' ⟨x, Subgroup.mem_sup_left hxQ⟩ * ψ' ⟨r, Subgroup.mem_sup_right hrR⟩ :=
      map_mul ψ' _ _
    calc (ψ' ⟨b, hbQR⟩ : X)
        = (ψ' (⟨x, Subgroup.mem_sup_left hxQ⟩ * ⟨r, Subgroup.mem_sup_right hrR⟩) : X) := by
          rw [hsplit]
      _ = ((ψ' ⟨x, Subgroup.mem_sup_left hxQ⟩ * ψ' ⟨r, Subgroup.mem_sup_right hrR⟩ :
            ↥(d.M ⊔ (d.leviLong ⊔ d.J₂))) : X) := congrArg Subtype.val hmap
      _ = (ψ' ⟨x, Subgroup.mem_sup_left hxQ⟩ : X) *
            (ψ' ⟨r, Subgroup.mem_sup_right hrR⟩ : X) := rfl
      _ = (ψ ⟨x, Subgroup.mem_sup_right hxB⟩ : X) *
            (ψ ⟨r, Subgroup.mem_sup_right hrB⟩ : X) := by rw [hψ'x, hψ'r]
      _ = (ψ ⟨b, Subgroup.mem_sup_right hb⟩ : X) := by rw [← hbprod]
  exact hψ'b

theorem D4qLocalData.exists_mulEquiv_vertexTwo (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J) :
    ∃ ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.Y : Set X)),
      ∀ (x : G) (hx : x ∈ bigB L1 L2 S),
        (ψ₂ ⟨x, Subgroup.mem_sup_right hx⟩ : X) =
          (ψ ⟨x, Subgroup.mem_sup_right hx⟩ : X) := by
  classical
  let Q : Subgroup G := pCoreOf 2 L2
  let H0 : Subgroup G := H ⊓ trivOTwoQuot L2
  let K2 : Subgroup G := L2 ⊓ Subgroup.centralizer (H0 : Set G)
  let R : Subgroup G := K2 ⊔ H0
  let P : Subgroup G := L1 ⊔ bigB L1 L2 S
  let R' : Subgroup X := d.leviLong ⊔ d.J₂
  have hQleP : Q ≤ P :=
    hH.pCoreOf_le_right.trans (le_sup_right.trans le_sup_right)
  obtain ⟨⟨hsupQK, hinfQK⟩, hHL2K, hsupQR, hdisjQR, hhNorm, hfaith, hcardR⟩ :=
    hD.vertexTwo_right hf hH h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
  obtain ⟨Θ, hΘ⟩ := exists_iso_M hH hD hHB d ψ hψS hψH hQleP
  obtain ⟨w, hwK, hwInv, hwgen⟩ :=
    exists_weyl_element hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
  have hwCentH0 : ∀ t ∈ H0, w * t * w⁻¹ = t := by
    intro t ht
    have hwC : w ∈ Subgroup.centralizer (H0 : Set G) := (Subgroup.mem_inf.mp hwK).2
    have hcomm : w * t = t * w :=
      (Subgroup.mem_centralizer_iff.mp hwC) t ht |>.symm
    rw [hcomm]
    group
  let T : Set G := ((R ⊓ bigB L1 L2 S : Subgroup G) : Set G) ∪ {w}
  have hT : Subgroup.closure T = R := closure_T_eq_R hH hD hHB hwK hwgen
  have hTΘ : ∀ t ∈ T, ∃ t' ∈ R', ∀ x y : ↥Q,
      (y : G) = t * (x : G) * t⁻¹ → (Θ y : X) = t' * (Θ x : X) * t'⁻¹ :=
    partners_of_T hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
      hQleP Θ hΘ hwK hwInv hwCentH0
  have hRnorm : R ≤ Subgroup.normalizer (Q : Set G) := hhNorm
  have hdisj : Disjoint Q R := hdisjQR
  have hR'norm : R' ≤ Subgroup.normalizer (d.M : Set X) :=
    sup_le d.leviLong_le_normalizer_M d.J₂_le_normalizer_M
  have hdisj' : Disjoint d.M R' :=
    disjoint_iff.mpr d.yamada_three_eight_five.2.2.2.2.2
  have hcard : Nat.card R = Nat.card R' :=
    hcardR.trans (card_leviLong_sup_J₂ d).symm
  obtain ⟨ψ', hψ'Q, hψ'R, hψ'partner⟩ :=
    exists_mulEquiv_sup_of_conj hRnorm hdisj hR'norm hdisj' hfaith
      (fun r hr hc => eq_one_of_mem_leviLong_sup_J₂_of_commute d hr hc) hcard Θ hT hTΘ
  have hQR : Q ⊔ R = L2 ⊔ bigB L1 L2 S := hsupQR
  have hMY : d.M ⊔ R' = Subgroup.normalizer (d.Y : Set X) :=
    d.yamada_three_eight_five.2.2.1.symm
  let ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.Y : Set X)) :=
    (MulEquiv.subgroupCongr hQR.symm).trans (ψ'.trans (MulEquiv.subgroupCongr hMY))
  refine ⟨ψ₂, ?_⟩
  intro b hb
  obtain ⟨hbQR, hEq⟩ :=
    extension_agrees_on_B hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
      hQleP Θ hΘ hQR hRnorm ψ' hψ'Q hψ'partner b hb
  have hfirst : (MulEquiv.subgroupCongr hQR.symm
      ⟨b, Subgroup.mem_sup_right hb⟩ : ↥(Q ⊔ R)) = ⟨b, hbQR⟩ := by
    apply Subtype.ext
    exact MulEquiv.subgroupCongr_apply hQR.symm _
  have hψ₂val : (ψ₂ ⟨b, Subgroup.mem_sup_right hb⟩ : X) = (ψ' ⟨b, hbQR⟩ : X) := by
    dsimp only [ψ₂]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hfirst, MulEquiv.subgroupCongr_apply]
  rw [hψ₂val, hEq]

end CFSG.Quasithin.F112R.St84

end
