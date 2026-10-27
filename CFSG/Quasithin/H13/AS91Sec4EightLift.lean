module

public import CFSG.Quasithin.H13.AS91Sec4SevenN
public import CFSG.Quasithin.H13.AS91Sec4EightSplitInputs
public import Certificates.Certificate89409
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GF2Type.Smith1979.IdxFourCoset
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S3Asch
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LargeExtraspecial.S5Gen2
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.HMathieuStatements
public import CFSG.Quasithin.Background.HSecQuot
public import CFSG.Quasithin.H13.AS91Sec4EightInputs
public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch7Inputs
public import CFSG.Quasithin.Vol2.Ch7Setup
public import CFSG.Quasithin.Vol2.Ch8Inputs
public import CFSG.Quasithin.Vol2.Ch8InputsB
public import CFSG.Quasithin.Vol2.Ch8Sec2Defs
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.J4Count.Prim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_card_three {L A B : Subgroup G} (hA : A ≤ L) (hB : B ≤ L)
    (hAc : Nat.card A = 3) (hBc : Nat.card B = 3) (hL : (Nat.card L).factorization 3 = 1) :
    ∃ k ∈ L, ∀ b ∈ B, ∃ a ∈ A, b = k * a * k⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA' : Nat.card (A.subgroupOf L) = 3 ^ (Nat.card L).factorization 3 := by
    rw [hL, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hAc]
  have hB' : Nat.card (B.subgroupOf L) = 3 ^ (Nat.card L).factorization 3 := by
    rw [hL, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hBc]
  let PA : Sylow 3 ↥L := Sylow.ofCard (A.subgroupOf L) hA'
  let PB : Sylow 3 ↥L := Sylow.ofCard (B.subgroupOf L) hB'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥L PA PB
  refine ⟨k, k.2, fun b hb => ?_⟩
  have hbB : (⟨b, hB hb⟩ : ↥L) ∈ (PB : Subgroup ↥L) := by
    change (⟨b, hB hb⟩ : ↥L) ∈ B.subgroupOf L
    exact mem_subgroupOf.mpr hb
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply] at hbB
  change k⁻¹ * ⟨b, hB hb⟩ * k⁻¹⁻¹ ∈ A.subgroupOf L at hbB
  rw [mem_subgroupOf] at hbB
  refine ⟨_, hbB, ?_⟩
  simp only [coe_mul, coe_inv, inv_inv]
  group

theorem qg_pow_four_eq_one (S : Setting G) {q : G} (hq : q ∈ S.QG) : q ^ 4 = 1 := by
  have hz : S.z ^ 2 = 1 := by
    rcases S.sq_eq_one_or_z S.z_mem_QG with h | h
    · exact h
    · have : S.z * S.z = S.z := by rw [← pow_two, h]
      have h1 : S.z = 1 := by simpa using this
      rw [h1, one_pow]
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  rcases S.sq_eq_one_or_z hq with h | h
  · rw [h, one_pow]
  · rw [h, hz]

theorem M_le_normalizer_QG (S : Setting G) : S.M ≤ normalizer (S.QG : Set G) := fun m hm =>
  mem_normalizer_iff.mpr fun x => ⟨fun hx => S.conj_mem_QG hm hx, fun hx => by
    have := S.conj_mem_QG (inv_mem hm) hx
    simpa [mul_assoc] using this⟩

namespace Two

theorem splitOK48_parts :
    sOK48 () = true ∧ coreOK48 () = true ∧ uOK48 () = true ∧ cjOK48 () = true := by
  have h := Certificates.certificate89409
  simp only [splitOK48, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem coreOK48_spec :
    (∀ i ∈ sWord48, i < 6) ∧ (∀ i ∈ sWordInv48, i < 6) ∧ mulR (sRows48 ()) (sInvRows48 ()) = idR ∧
      appN (sRows48 ()) 3 = 3 ∧ (coreList48 ()).dedup.length = 32 := by
  have h := splitOK48_parts.2.1
  simp only [coreOK48, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem mem_coreList48 {r : Array ℕ} :
    r ∈ coreList48 () ↔ r ∈ enumGrp pRows ∧ mulR (mulR (sInvRows48 ()) r) (sRows48 ()) ∈ enumGrp pRows := by
  simp only [coreList48, List.mem_filter, Std.HashSet.contains_ofList, List.contains_iff_mem]

end Two

theorem rowsOf_okRows (U : V12 ≃ₗ[ZMod 2] V12) : okRows (rowsOf U) = true := by
  simp only [okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq]
  exact ⟨rowsOf_size U, fun x hx => rowsOf_lt U x hx⟩

namespace Data41

variable {z : G} {h : HypJ4 G z} (D : Data41 h)

local notation "Xc" => (zpowers ((D.c : h.setting.M) : G))

section Lift

theorem θ_inv : D.θ⁻¹ = D.θ * D.θ := by
  rw [inv_eq_iff_mul_eq_one, ← pow_three, D.θ_pow]

theorem eq_or_eq_mul_z_of_nx (hHat : HatM22SmallModules) {y y' : h.setting.M}
    (hy : (y : G) ∈ normalizer (Xc : Set G)) (hy' : (y' : G) ∈ normalizer (Xc : Set G))
    (hρ : h.setting.ρ y = h.setting.ρ y') : (y' : G) = y ∨ (y' : G) = y * z := by
  set q : G := (y : G)⁻¹ * y' with hqdef
  have hqQ : q ∈ h.setting.QG := by
    have h1 : h.setting.ρ (y⁻¹ * y') = 1 := by rw [map_mul, map_inv, hρ, inv_mul_cancel]
    exact (h.setting.ρ_eq_one_iff _).mp h1
  have hqN : q ∈ normalizer (Xc : Set G) := mul_mem (inv_mem hy) hy'
  have hc : (D.c : G) ∈ Xc := mem_zpowers _
  have hqc : q * (D.c : G) * q⁻¹ ∈ Xc := (mem_normalizer_iff.mp hqN _).mp hc
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hqc
  have hcomm : q * (D.c : G) * q⁻¹ * (D.c : G)⁻¹ ∈ h.setting.QG := by
    have := h.setting.conj_mem_QG D.c.2 (inv_mem hqQ)
    have e : q * (D.c : G) * q⁻¹ * (D.c : G)⁻¹ = q * ((D.c : G) * q⁻¹ * (D.c : G)⁻¹) := by group
    rw [e]
    exact mul_mem hqQ this
  have hk1 : (D.c : G) ^ (k - 1) ∈ h.setting.QG := by
    rw [zpow_sub_one, hk]
    exact hcomm
  have hρk : D.θ ^ (k - 1) = 1 := by
    have h1 := (h.setting.ρ_eq_one_iff (D.c ^ (k - 1))).mpr (by simpa using hk1)
    rwa [map_zpow, D.ρ_c] at h1
  have h3 : (3 : ℤ) ∣ k - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hρk
    rwa [D.orderOf_θ, Nat.cast_ofNat] at this
  have hcq : q * (D.c : G) * q⁻¹ = D.c := by
    obtain ⟨m, hm⟩ := h3
    have hc3 : (D.c : G) ^ (3 : ℤ) = 1 := by
      have := D.c_pow
      rw [zpow_ofNat]
      exact congrArg Subtype.val this
    rw [← hk, show k = 1 + 3 * m by omega, zpow_add, zpow_mul, hc3, one_zpow, mul_one, zpow_one]
  have hqC : q ∈ h.setting.QG ⊓ centralizer (Xc : Set G) := by
    refine ⟨hqQ, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨j, rfl⟩
    have hcq' : (D.c : G) * q = q * D.c := by
      calc (D.c : G) * q = q * (D.c : G) * q⁻¹ * q := by rw [hcq]
        _ = q * D.c := by group
    exact (Commute.zpow_left hcq' j).eq
  rw [inf_centralizer_eq hHat h.setting_width D.ρ_c D.θ_mem D.θ_ne D.hat, h.setting_z] at hqC
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hqC
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h.z_mul_z
  have hy'q : (y' : G) = y * q := by rw [hqdef]; group
  rcases Int.emod_two_eq_zero_or_one j with hj2 | hj2
  · left
    rw [hy'q, ← hj, ← Int.emod_add_mul_ediv j 2, hj2, zero_add, zpow_mul, hz2, one_zpow, mul_one]
  · right
    rw [hy'q, ← hj, ← Int.emod_add_mul_ediv j 2, hj2, zpow_add, zpow_mul, hz2, one_zpow, mul_one,
      zpow_one]

theorem exists_nx_lift {p : h.setting.O} (hp : p ∈ h.setting.Mbar) :
    ∃ y : h.setting.M, (y : G) ∈ normalizer (Xc : Set G) ∧ h.setting.ρ y = p := by
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hp
  have hm : (m : G) ∈ h.setting.QG ⊔ (h.setting.M ⊓ normalizer (Xc : Set G)) := by
    rw [← M_eq_sup_normalizer D.ρ_c D.orderOf_c D.θ_mem D.orderOf_θ D.θ_normal D.card_QG]
    exact m.2
  obtain ⟨q, hq, n, hn, hqn⟩ :=
    exists_mul_of_mem_sup (inf_le_left.trans (M_le_normalizer_QG h.setting)) hm
  refine ⟨⟨n, hn.1⟩, hn.2, ?_⟩
  have e : m = ⟨q, h.setting.QG_le_M hq⟩ * ⟨n, hn.1⟩ := Subtype.ext hqn.symm
  rw [e, map_mul, (h.setting.ρ_eq_one_iff ⟨q, h.setting.QG_le_M hq⟩).mpr hq, one_mul]

theorem sq_eq_one_of_nx (hHat : HatM22SmallModules) {y y' : h.setting.M}
    (hy : (y : G) ∈ normalizer (Xc : Set G)) (hy' : (y' : G) ∈ normalizer (Xc : Set G))
    (hρ : h.setting.ρ y = h.setting.ρ y') (hy2 : (y : G) * y = 1) : (y' : G) * y' = 1 := by
  rcases D.eq_or_eq_mul_z_of_nx hHat hy hy' hρ with e | e
  · rw [e, hy2]
  · have hzc : (y : G) * z = z * y := by
      have := h.setting.z_comm y.2
      rwa [h.setting_z] at this
    rw [e]
    calc (y : G) * z * (y * z) = y * y * (z * z) := by
          rw [mul_assoc, ← mul_assoc z, ← hzc]; group
      _ = 1 := by rw [hy2, h.z_mul_z, one_mul]

end Lift

section CE

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)
  (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem c_mem_G13 : (D.c : G) ∈ D.G13 :=
  D.QX_le hOut hTw (le_sup_right (a := Q z) (mem_zpowers _))

theorem exists_cE_lift {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ Two.ebGrp) :
    ∃ s : h.setting.M, (s : G) ∈ D.E ∧ (s : G) ∈ centralizer (Xc : Set G) ∧
      D.Φo (h.setting.ρ s) = U := by
  obtain ⟨e, heE, heU⟩ := D.exists_mem_E hOut hTw hU
  set c : h.setting.M := D.c with hcdef
  have hcG := D.c_mem_G13 hOut hTw hHat
  have hc2G : ((c * c : h.setting.M) : G) ∈ D.G13 := mul_mem hcG hcG
  set e1 : h.setting.M := c * e * c⁻¹ with he1
  set e2 : h.setting.M := (c * c) * e * (c * c)⁻¹ with he2
  have he1E : (e1 : G) ∈ D.E := D.conj_mem_E hcG heE
  have he2E : (e2 : G) ∈ D.E := D.conj_mem_E hc2G heE
  refine ⟨e * e1 * e2, mul_mem (mul_mem heE he1E) he2E, ?_, ?_⟩
  ·
    have hc3 : c * c * c = 1 := by rw [← pow_three', D.c_pow]
    have hcom : ∀ {a b : G}, a ∈ D.E → b ∈ D.E → a * b = b * a := fun ha hb =>
      D.E_comm hOut hTw hHat ha hb
    have key : (c : G) * ((e : G) * e1 * e2) * (c : G)⁻¹ = (e : G) * e1 * e2 := by
      have h3 : (c : G) * e2 * (c : G)⁻¹ = e := by
        rw [he2]
        simp only [coe_mul, coe_inv]
        have h3' : (c : G) * c * c = 1 := by
          have := congrArg Subtype.val hc3
          simpa using this
        calc (c : G) * ((c : G) * c * e * ((c : G) * c)⁻¹) * (c : G)⁻¹
            = ((c : G) * c * c) * e * ((c : G) * c * c)⁻¹ := by group
          _ = e := by rw [h3']; group
      have h1 : (c : G) * e * (c : G)⁻¹ = e1 := by rw [he1]; simp
      have h2 : (c : G) * e1 * (c : G)⁻¹ = e2 := by rw [he1, he2]; simp only [coe_mul, coe_inv]; group
      calc (c : G) * ((e : G) * e1 * e2) * (c : G)⁻¹
          = ((c : G) * e * (c : G)⁻¹) * ((c : G) * e1 * (c : G)⁻¹) * ((c : G) * e2 * (c : G)⁻¹) := by
            group
        _ = (e1 : G) * e2 * e := by rw [h1, h2, h3]
        _ = (e : G) * e1 * e2 := by
            rw [hcom (mul_mem he1E he2E) heE]
            group
    refine mem_centralizer_iff.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hcx : (c : G) * ((e : G) * e1 * e2) = ((e : G) * e1 * e2) * c := by
      calc (c : G) * ((e : G) * e1 * e2) = (c : G) * ((e : G) * e1 * e2) * (c : G)⁻¹ * c := by
            group
        _ = _ := by rw [key]
    exact (Commute.zpow_left hcx j).eq
  ·
    have hA : D.Φo (h.setting.ρ e) ∈ Two.ebGrp := by rw [heU]; exact hU
    have hcom : Commute (D.Φo (h.setting.ρ c)) (D.Φo (h.setting.ρ e)) := by
      rw [hcdef, D.ρ_c]
      exact D.Φo_θ_comm hOut hTw hA
    have hcom2 : Commute (D.Φo (h.setting.ρ (c * c))) (D.Φo (h.setting.ρ e)) := by
      rw [map_mul, map_mul]
      exact hcom.mul_left hcom
    have h1 : D.Φo (h.setting.ρ e1) = D.Φo (h.setting.ρ e) := by
      rw [he1, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hcom.eq, mul_inv_cancel_right]
    have h2 : D.Φo (h.setting.ρ e2) = D.Φo (h.setting.ρ e) := by
      rw [he2, map_mul h.setting.ρ (c * c * e), map_mul h.setting.ρ (c * c) e, map_inv, map_mul,
        map_mul, map_inv, hcom2.eq, mul_inv_cancel_right]
    have hsq := Two.ebGrp_sq hA
    rw [map_mul, map_mul, map_mul, map_mul, h1, h2, hsq, one_mul, heU]

theorem sq_eq_one_of_conj_eb {y : h.setting.M} (hy : (y : G) ∈ normalizer (Xc : Set G))
    {W e : V12 ≃ₗ[ZMod 2] V12} (hW : W ∈ Two.gamGrp) (he : e ∈ Two.ebGrp)
    (hρ : D.Φo (h.setting.ρ y) = W * e * W⁻¹) : (y : G) * y = 1 := by
  obtain ⟨s, hsE, hsX, hse⟩ := D.exists_cE_lift hOut hTw hHat he
  have hWN := Two.gamGrp_le_nGrp hW
  rw [← D.map_Mbar_Φo hOut hTw] at hWN
  obtain ⟨m, hmM, rfl⟩ := hWN
  have hmc : (m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) ∈ cMbar h.setting D.θ :=
    D.mem_cMbar_of_Φ hW
  obtain ⟨w, hwX, hwm⟩ := exists_centralizer_of_mem_cMbar D.c_pow D.ρ_c hmc
  have hwm' : h.setting.ρ w = m := Subtype.ext hwm
  set y' : h.setting.M := w * s * w⁻¹ with hy'
  have hy'X : (y' : G) ∈ centralizer (Xc : Set G) := by
    rw [hy']
    simp only [coe_mul, coe_inv]
    exact mul_mem (mul_mem hwX hsX) (inv_mem hwX)
  have hy'N : (y' : G) ∈ normalizer (Xc : Set G) :=
    mem_normalizer_fintype fun n hn => by
      rw [← (mem_centralizer_iff.mp hy'X n hn), mul_inv_cancel_right]
      exact hn
  have hρ' : h.setting.ρ y' = h.setting.ρ y := by
    apply D.Φo_injective
    rw [hρ, hy', map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hwm', hse]
  have hy'2 : (y' : G) * y' = 1 := by
    rw [hy']
    simp only [coe_mul, coe_inv]
    have hs2 := D.E_sq hHat hOut hTw hsE
    calc (w : G) * s * (w : G)⁻¹ * ((w : G) * s * (w : G)⁻¹) = (w : G) * ((s : G) * s) * (w : G)⁻¹ := by
          group
      _ = 1 := by rw [hs2]; group
  exact D.sq_eq_one_of_nx hHat hy'N hy hρ' hy'2

end CE

section Dihedral

theorem exists_nx_involution {x : h.setting.M} (hx : (x : G) * x = 1)
    (hinv : h.setting.ρ x * D.θ * (h.setting.ρ x)⁻¹ = D.θ⁻¹) :
    ∃ s : h.setting.M, (s : G) ∈ normalizer (Xc : Set G) ∧ (s : G) * s = 1 ∧
      h.setting.ρ s = h.setting.ρ x := by
  set c : h.setting.M := D.c with hcdef
  have hxx : x * x = 1 := Subtype.ext hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxiG : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hρxi : (h.setting.ρ x)⁻¹ = h.setting.ρ x := by rw [← map_inv, hxi]
  set w0 : h.setting.M := x * c * x * c⁻¹ with hw0
  have hρw0 : h.setting.ρ w0 = D.θ := by
    rw [hw0, map_mul, map_mul, map_mul, map_inv, hcdef, D.ρ_c]
    calc h.setting.ρ x * D.θ * h.setting.ρ x * D.θ⁻¹
        = h.setting.ρ x * D.θ * (h.setting.ρ x)⁻¹ * D.θ⁻¹ := by rw [hρxi]
      _ = D.θ⁻¹ * D.θ⁻¹ := by rw [hinv]
      _ = D.θ⁻¹ * D.θ⁻¹ * D.θ ^ 3 := by rw [D.θ_pow, mul_one]
      _ = D.θ := by group
  set u : h.setting.M := w0 ^ 4 with hu
  have hρu : h.setting.ρ u = D.θ := by
    rw [hu, map_pow, hρw0, show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, D.θ_pow, one_mul]
  have hu3 : (u : G) ^ 3 = 1 := by
    have hw3 : ((w0 ^ 3 : h.setting.M) : G) ∈ h.setting.QG := by
      refine (h.setting.ρ_eq_one_iff _).mp ?_
      rw [map_pow, hρw0, D.θ_pow]
    have := qg_pow_four_eq_one h.setting hw3
    rw [hu, Subgroup.coe_pow, ← pow_mul, show 4 * 3 = 3 * 4 by norm_num, pow_mul]
    simpa using this
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    apply D.θ_ne
    rw [← hρu, show u = 1 from Subtype.ext h1, map_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hou : orderOf (u : G) = 3 := orderOf_eq_prime hu3 hu1
  have hxw : (x : G) * w0 * (x : G)⁻¹ = (w0 : G)⁻¹ := by
    rw [hw0]
    simp only [coe_mul, coe_inv]
    rw [hxiG]
    calc (x : G) * ((x : G) * c * x * (c : G)⁻¹) * x = ((x : G) * x) * c * x * (c : G)⁻¹ * x := by
          group
      _ = (c : G) * x * (c : G)⁻¹ * x := by rw [hx, one_mul]
      _ = ((x : G) * c * x * (c : G)⁻¹)⁻¹ := by
          rw [show ((x : G) * c * x * (c : G)⁻¹)⁻¹ = (c : G) * (x : G)⁻¹ * (c : G)⁻¹ * (x : G)⁻¹ by
            group, hxiG]
  have hxu : (x : G) * u * (x : G)⁻¹ = (u : G)⁻¹ := by
    rw [hu, Subgroup.coe_pow, ← conj_pow, hxw, inv_pow]
  have hL : Nat.card (pre h.setting (zpowers D.θ)) = 3 * 2 ^ 13 := by
    rw [card_pre (zpowers_le.mpr D.θ_mem), Nat.card_zpowers, D.orderOf_θ, D.card_QG]
  have huL : (u : G) ∈ pre h.setting (zpowers D.θ) :=
    mem_pre_of_rho u (by rw [hρu]; exact mem_zpowers _)
  have hcL : (c : G) ∈ pre h.setting (zpowers D.θ) :=
    mem_pre_of_rho c (by rw [hcdef, D.ρ_c]; exact mem_zpowers _)
  obtain ⟨k, hkL, hk⟩ := exists_conj_of_card_three (zpowers_le.mpr huL) (zpowers_le.mpr hcL)
    (by rw [Nat.card_zpowers, hou]) (by rw [Nat.card_zpowers, hcdef, D.orderOf_c])
    (by rw [hL, factorization_three_mul_two_pow])
  obtain ⟨a, ⟨m, rfl⟩, hca⟩ := hk (c : G) (mem_zpowers _)
  obtain ⟨q, hq, j, rfl⟩ := exists_mul_zpow_of_mem_pre D.ρ_c hkL
  set q' : G := (c : G) ^ (-j) * q * (c : G) ^ j with hq'
  have hq'Q : q' ∈ h.setting.QG := by
    have := h.setting.conj_mem_QG (zpow_mem c.2 (-j)) hq
    rw [hq']
    simpa [zpow_neg] using this
  have hq'c : q' * (u : G) ^ m * q'⁻¹ = c := by
    have e : (c : G) ^ j * (q' * (u : G) ^ m * q'⁻¹) * (c : G) ^ (-j) = c := by
      rw [hq']
      calc (c : G) ^ j * ((c : G) ^ (-j) * q * (c : G) ^ j * (u : G) ^ m *
            ((c : G) ^ (-j) * q * (c : G) ^ j)⁻¹) * (c : G) ^ (-j)
          = q * (c : G) ^ j * (u : G) ^ m * (q * (c : G) ^ j)⁻¹ := by group
        _ = c := hca.symm
    calc q' * (u : G) ^ m * q'⁻¹ = (c : G) ^ (-j) * ((c : G) ^ j * (q' * (u : G) ^ m * q'⁻¹) *
          (c : G) ^ (-j)) * (c : G) ^ j := by group
      _ = (c : G) ^ (-j) * c * (c : G) ^ j := by rw [e]
      _ = c := by group
  set qm : h.setting.M := ⟨q', h.setting.QG_le_M hq'Q⟩ with hqm
  refine ⟨qm * x * qm⁻¹, ?_, ?_, ?_⟩
  ·
    have hsc : (q' * x * q'⁻¹) * (c : G) * (q' * x * q'⁻¹)⁻¹ = (c : G)⁻¹ := by
      have hxum : (x : G) * (u : G) ^ m * (x : G)⁻¹ = ((u : G) ^ m)⁻¹ := by
        rw [← conj_zpow, hxu, inv_zpow]
      calc (q' * x * q'⁻¹) * (c : G) * (q' * x * q'⁻¹)⁻¹
          = (q' * x * q'⁻¹) * (q' * (u : G) ^ m * q'⁻¹) * (q' * x * q'⁻¹)⁻¹ := by rw [hq'c]
        _ = q' * ((x : G) * (u : G) ^ m * (x : G)⁻¹) * q'⁻¹ := by group
        _ = (q' * (u : G) ^ m * q'⁻¹)⁻¹ := by rw [hxum]; group
        _ = (c : G)⁻¹ := by rw [hq'c]
    refine mem_normalizer_fintype fun n hn => ?_
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hn
    have e : ((qm * x * qm⁻¹ : h.setting.M) : G) = q' * x * q'⁻¹ := by
      simp only [hqm, coe_mul, coe_inv]
    rw [e, ← conj_zpow, hsc]
    exact zpow_mem (inv_mem (mem_zpowers _)) i
  · simp only [coe_mul, coe_inv, hqm]
    calc q' * (x : G) * q'⁻¹ * (q' * x * q'⁻¹) = q' * ((x : G) * x) * q'⁻¹ := by group
      _ = 1 := by rw [hx]; group
  · rw [map_mul, map_mul, map_inv, (h.setting.ρ_eq_one_iff qm).mpr hq'Q, one_mul, inv_one, mul_one]

end Dihedral

section Lbar

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem exists_involution_of_mem_Lbar {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
    {v : h.setting.O} (hv : v ∈ h.setting.Lbar g₁) (hv1 : v ≠ 1) :
    ∃ x : h.setting.M, (x : G) * x = 1 ∧ h.setting.ρ x = v := by
  obtain ⟨x0, hx0, rfl⟩ := hv
  have hx0a : (x0 : G) ∈ h.setting.Qa g₁ := (mem_subgroupOf.mp hx0).1
  have hx0Q : (x0 : G) ∉ h.setting.QG := fun hq => hv1 ((h.setting.ρ_eq_one_iff x0).mpr hq)
  set T' := h.setting.conjBy g₁ with hT'
  have hT'QG : T'.QG = h.setting.Qa g₁ := rfl
  have hT'z : T'.z = D.rep 3 := by
    rw [hT', Setting.conjBy_z, h.setting_z]
    exact hg₁
  obtain ⟨-, -, h3z⟩ := D.rep_props vecOf_three_ne q0_three
  have hzne : h.setting.z ≠ T'.z := by rw [hT'z, h.setting_z]; exact h3z.symm
  have hcardA := D.card_QG_inf_Qa_g₁ hOut hTw hg₁
  rcases T'.sq_eq_one_or_z (hT'QG ▸ hx0a) with h1 | h1
  · exact ⟨x0, by rw [← pow_two]; exact h1, rfl⟩
  have hne : g₁ * h.setting.z * g₁⁻¹ ≠ h.setting.z := by
    rw [← Setting.conjBy_z, ← hT']
    exact hzne.symm
  obtain ⟨f, hfA, hf⟩ : ∃ f ∈ (h.setting.QG ⊓ h.setting.Qa g₁ : Subgroup G),
      (x0 : G) * f ≠ f * x0 := by
    by_contra hcon
    push Not at hcon
    set K : Subgroup G := closure ((h.setting.QG ⊓ h.setting.Qa g₁ : Subgroup G) ∪ {(x0 : G)})
      with hK
    have hpair : ((h.setting.QG ⊓ h.setting.Qa g₁ : Subgroup G) ∪ {(x0 : G)} : Set G).Pairwise
        Commute := by
      intro a ha b hb _
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact h.setting.QG_inf_Qa_comm hne ha hb
      · rw [Set.mem_singleton_iff.mp hb]
        exact (hcon a ha).symm
      · rw [Set.mem_singleton_iff.mp ha]
        exact hcon b hb
      · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
    letI := closureCommGroupOfComm hpair
    have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥K) ⟨b, hb⟩)
    have hKQ : K ≤ T'.QG := by
      refine (closure_le _).mpr ?_
      rintro y (hy | hy)
      · exact hy.2
      · rw [Set.mem_singleton_iff.mp hy]
        exact hx0a
    have hle := T'.card_le_of_commute hKQ hKc
    rw [h.setting.width_conjBy, h.setting_width] at hle
    have hAK : (h.setting.QG ⊓ h.setting.Qa g₁ : Subgroup G) ≤ K :=
      fun y hy => subset_closure (Or.inl hy)
    have heq := Subgroup.eq_of_le_of_card_ge hAK (by rw [hcardA]; exact hle)
    have hx0K : (x0 : G) ∈ K := subset_closure (Or.inr rfl)
    rw [← heq] at hx0K
    exact hx0Q hx0K.1
  have hfQ := hfA.1
  have hfa := hfA.2
  have hcomm : (x0 : G) * f * (x0 : G)⁻¹ * f⁻¹ = T'.z := by
    rcases T'.commutator_eq_one_or_z (hT'QG ▸ hx0a) (hT'QG ▸ hfa) with hc | hc
    · exfalso
      apply hf
      calc (x0 : G) * f = (x0 : G) * f * (x0 : G)⁻¹ * f⁻¹ * f * x0 := by group
        _ = f * x0 := by rw [hc, one_mul]
    · exact hc
  have hf2 : f * f = 1 := by
    rcases h.setting.sq_eq_one_or_z hfQ with h2 | h2
    · rwa [pow_two] at h2
    · rcases T'.sq_eq_one_or_z (hT'QG ▸ hfa) with h3 | h3
      · rwa [pow_two] at h3
      · exact absurd (h2.symm.trans h3) hzne
  have hr2 : T'.z * T'.z = 1 := by
    rw [hT'z]
    exact (D.rep_props vecOf_three_ne q0_three).1
  have hrf : T'.z * f = f * T'.z := (T'.z_comm_QG (hT'QG ▸ hfa)).symm
  refine ⟨x0 * ⟨f, h.setting.QG_le_M hfQ⟩, ?_, ?_⟩
  · simp only [coe_mul]
    have hx2 : (x0 : G) * x0 = T'.z := by rw [← pow_two]; exact h1
    calc (x0 : G) * f * ((x0 : G) * f) = ((x0 : G) * f * (x0 : G)⁻¹ * f⁻¹) * f * ((x0 : G) * x0) * f :=
          by group
      _ = T'.z * f * T'.z * f := by rw [hcomm, hx2]
      _ = T'.z * (f * T'.z) * f := by group
      _ = T'.z * (T'.z * f) * f := by rw [← hrf]
      _ = (T'.z * T'.z) * (f * f) := by group
      _ = 1 := by rw [hr2, hf2, one_mul]
  · rw [map_mul, (h.setting.ρ_eq_one_iff ⟨f, h.setting.QG_le_M hfQ⟩).mpr hfQ, mul_one]

end Lbar

section Core

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem card_Lbar_g₁ {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) :
    Nat.card (h.setting.Lbar g₁) = 32 := by
  obtain ⟨-, -, h3z⟩ := D.rep_props vecOf_three_ne q0_three
  have hg₁' : g₁ * h.setting.z * g₁⁻¹ = D.rep 3 := hg₁
  have haQ : g₁ * h.setting.z * g₁⁻¹ ∈ h.setting.QG := by rw [hg₁']; exact D.rep_mem 3
  have hne : g₁ * h.setting.z * g₁⁻¹ ≠ h.setting.z := by rw [hg₁']; exact h3z
  have hmul := h.setting.card_Lbar_mul g₁
  rw [h.setting.card_L0 haQ hne, h.setting_width, D.card_QG_inf_Qa_g₁ hOut hTw hg₁] at hmul
  norm_num at hmul
  omega

theorem Lbar_le_Tbar {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) : h.setting.Lbar g₁ ≤ D.Tbar := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h31, h3z⟩ := D.rep_props vecOf_three_ne q0_three
  have hg₁' : g₁ * h.setting.z * g₁⁻¹ = D.rep 3 := hg₁
  have haQ : g₁ * h.setting.z * g₁⁻¹ ∈ h.setting.QG := by rw [hg₁']; exact D.rep_mem 3
  have ha1 : g₁ * h.setting.z * g₁⁻¹ ≠ 1 := by rw [hg₁']; exact h31
  have hne : g₁ * h.setting.z * g₁⁻¹ ≠ h.setting.z := by rw [hg₁']; exact h3z
  set St := stab h.setting (h.setting.cl (D.rep 3)) with hSt
  have hLs : h.setting.Lbar g₁ ≤ St := by
    have := Lbar_le_stab h.setting haQ
    rwa [hg₁'] at this
  have hTs : D.Tbar ≤ St := by
    intro v hv
    have hv' : D.Φo v ∈ Two.pGrp := hv
    have h1 : D.Φo v ∈ stabIn Two.nGrp (vecOf 3) :=
      mem_stabIn.mpr ⟨Two.pGrp_le_nGrp hv', Two.pGrp_fix_three hv'⟩
    rw [← D.map_stab hOut hTw 3] at h1
    obtain ⟨w, hw, hwv⟩ := h1
    rwa [D.Φo_injective hwv] at hw
  have hcardT : Nat.card D.Tbar = 256 := by
    rw [Tbar, D.card_comap hOut hTw Two.pGrp_le_nGrp, Two.card_pGrp]
  have hfac : (Nat.card St).factorization 2 = 8 := by
    rw [hSt, D.card_stab_three hOut hTw, show (3840 : ℕ) = 2 ^ 8 * 15 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd]
  let P : Sylow 2 ↥St := Sylow.ofCard (D.Tbar.subgroupOf St) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTs).toEquiv, hcardT, hfac]
    norm_num)
  haveI hN : ((h.setting.Lbar g₁).subgroupOf St).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact Lbar_conj_mem h.setting haQ ha1 hne (by rw [hg₁']; exact g.2) hn
  have hNp : IsPGroup 2 ((h.setting.Lbar g₁).subgroupOf St) :=
    IsPGroup.of_card (n := 5) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hLs).toEquiv, D.card_Lbar_g₁ hOut hTw hg₁]
      norm_num)
  have hle := hNp.le_sylow_of_normal P
  intro v hv
  have h1 : (⟨v, hLs hv⟩ : ↥St) ∈ (P : Subgroup ↥St) := hle (mem_subgroupOf.mpr hv)
  exact mem_subgroupOf.mp h1

theorem rowsOf_mem_enum_p {v : h.setting.O} (hv : v ∈ D.Tbar) :
    rowsOf (D.Φo v) ∈ enumGrp Two.pRows := by
  obtain ⟨-, -, hid, hc, -⟩ := Two.pOK45_spec
  obtain ⟨r, hr, hvr⟩ := complete hid hc _ (show D.Φo v ∈ Two.pGrp from hv)
  rw [rowsOf_eq (enumGrp_sound Two.gensOK_pRows r hr).1 hvr]
  exact hr

theorem rowsOf_mem_core {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) {v : h.setting.O}
    (hv : v ∈ h.setting.Lbar g₁) : rowsOf (D.Φo v) ∈ Two.coreList48 () := by
  obtain ⟨hw, hwi, hsi, h3, -⟩ := Two.coreOK48_spec
  obtain ⟨-, h31, h3z⟩ := D.rep_props vecOf_three_ne q0_three
  have hg₁' : g₁ * h.setting.z * g₁⁻¹ = D.rep 3 := hg₁
  have haQ : g₁ * h.setting.z * g₁⁻¹ ∈ h.setting.QG := by rw [hg₁']; exact D.rep_mem 3
  have ha1 : g₁ * h.setting.z * g₁⁻¹ ≠ 1 := by rw [hg₁']; exact h31
  have hne : g₁ * h.setting.z * g₁⁻¹ ≠ h.setting.z := by rw [hg₁']; exact h3z
  have hlen : Two.nGensI.length = 6 := rfl
  obtain ⟨hsok, U, hUN, hUs⟩ := rep_word Two.gensOK_nGensI Two.sWord48
    (fun i hi => hlen ▸ hw i hi)
  obtain ⟨hsiok, Ui, -, hUis⟩ := rep_word Two.gensOK_nGensI Two.sWordInv48
    (fun i hi => hlen ▸ hwi i hi)
  have hU3 : U (vecOf 3) = vecOf 3 := by
    rw [hUs, ← vecOf_appN]
    exact congrArg vecOf h3
  have hUst : U ∈ stabIn Two.nGrp (vecOf 3) := mem_stabIn.mpr ⟨hUN, hU3⟩
  rw [← D.map_stab hOut hTw 3] at hUst
  obtain ⟨sb, hsb, hsbU⟩ := hUst
  have hUiU : ∀ x, U⁻¹ x = Ui x := by
    intro x
    have hUUi : U (Ui x) = x := by
      rw [hUs, hUis, ← linOfRows_mulR]
      change linOfRows (mulR (Two.sRows48 ()) (Two.sInvRows48 ())) x = x
      rw [hsi, linOfRows_idR]
    calc U⁻¹ x = U⁻¹ (U (Ui x)) := by rw [hUUi]
      _ = Ui x := by simp
  have hLT := D.Lbar_le_Tbar hOut hTw hg₁
  have hconj : sb⁻¹ * v * sb ∈ h.setting.Lbar g₁ := by
    have := Lbar_conj_mem h.setting haQ ha1 hne (s := sb⁻¹) (by rw [hg₁']; exact inv_mem hsb) hv
    simpa using this
  have hrows : rowsOf (D.Φo (sb⁻¹ * v * sb)) =
      mulR (mulR (Two.sInvRows48 ()) (rowsOf (D.Φo v))) (Two.sRows48 ()) := by
    refine rowsOf_eq (okRows_mulR (okRows_mulR hsiok (rowsOf_okRows _)) hsok) fun x => ?_
    rw [map_mul, map_mul, map_inv, hsbU, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      linOfRows_mulR, linOfRows_mulR, linOfRows_rowsOf, hUiU, hUs, hUis]
    rfl
  refine Two.mem_coreList48.mpr ⟨D.rowsOf_mem_enum_p hOut hTw (hLT hv), ?_⟩
  rw [← hrows]
  exact D.rowsOf_mem_enum_p hOut hTw (hLT hconj)

theorem exists_Lbar_of_mem_core {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) {r : Array ℕ}
    (hr : r ∈ Two.coreList48 ()) :
    ∃ v ∈ h.setting.Lbar g₁, ∀ x, D.Φo v x = linOfRows r x := by
  classical
  obtain ⟨-, -, -, -, hlen⟩ := Two.coreOK48_spec
  let f : ↥(h.setting.Lbar g₁) → ↥(Two.coreList48 ()).toFinset := fun v =>
    ⟨rowsOf (D.Φo v), List.mem_toFinset.mpr (D.rowsOf_mem_core hOut hTw hg₁ v.2)⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have h1 : rowsOf (D.Φo v) = rowsOf (D.Φo w) := congrArg Subtype.val hvw
    refine Subtype.ext (D.Φo_injective (LinearEquiv.ext fun x => ?_))
    rw [← linOfRows_rowsOf (D.Φo v), h1, linOfRows_rowsOf]
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [D.card_Lbar_g₁ hOut hTw hg₁, Nat.card_eq_fintype_card, Fintype.card_coe,
      List.card_toFinset, hlen])
  obtain ⟨v, hv⟩ := hbij.2 ⟨r, List.mem_toFinset.mpr hr⟩
  refine ⟨v, v.2, fun x => ?_⟩
  have h1 : rowsOf (D.Φo v) = r := congrArg Subtype.val hv
  rw [← h1, linOfRows_rowsOf]

theorem sq_eq_one_of_conj_core (hHat : HatM22SmallModules) {g₁ : G}
    (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) {y : h.setting.M} (hy : (y : G) ∈ normalizer (Xc : Set G))
    {W : V12 ≃ₗ[ZMod 2] V12} (hW : W ∈ Two.nGrp) {r : Array ℕ} (hr : r ∈ Two.coreList48 ())
    (hr1 : r ≠ idR) (hρ : ∀ x, D.Φo (h.setting.ρ y) x = W (linOfRows r (W⁻¹ x)))
    (hinv : h.setting.ρ y * D.θ * (h.setting.ρ y)⁻¹ = D.θ⁻¹) : (y : G) * y = 1 := by
  obtain ⟨v, hvL, hvr⟩ := D.exists_Lbar_of_mem_core hOut hTw hg₁ hr
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hr1
    have hok : okRows r = true :=
      (enumGrp_sound Two.gensOK_pRows r (Two.mem_coreList48.mp hr).1).1
    have e1 : rowsOf (D.Φo 1) = r := rowsOf_eq hok hvr
    have e2 : rowsOf (D.Φo 1) = idR := rowsOf_eq idR_ok fun x => by
      rw [map_one, linOfRows_idR]
      rfl
    rw [← e1, e2]
  obtain ⟨x0, hx0, hx0v⟩ := D.exists_involution_of_mem_Lbar hOut hTw hg₁ hvL hv1
  have hWN := hW
  rw [← D.map_Mbar_Φo hOut hTw] at hWN
  obtain ⟨m, hmM, rfl⟩ := hWN
  obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hmM
  set x1 : h.setting.M := w * x0 * w⁻¹ with hx1def
  have hx1 : (x1 : G) * x1 = 1 := by
    rw [hx1def]
    simp only [coe_mul, coe_inv]
    calc (w : G) * x0 * (w : G)⁻¹ * ((w : G) * x0 * (w : G)⁻¹) = (w : G) * ((x0 : G) * x0) * (w : G)⁻¹ := by
          group
      _ = 1 := by rw [hx0]; group
  have hρ1 : h.setting.ρ x1 = h.setting.ρ y := by
    apply D.Φo_injective
    apply LinearEquiv.ext
    intro x
    rw [hρ x, hx1def, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hx0v,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply, hvr]
  obtain ⟨s, hsN, hs2, hsρ⟩ := D.exists_nx_involution hx1 (by rw [hρ1]; exact hinv)
  exact D.sq_eq_one_of_nx hHat hsN hy (hsρ.trans hρ1) hs2

end Core

end Data41

end CFSG.Quasithin.H13.AS91
