module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseOddCoreIndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionNormalizerInfConjugate
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
open scoped Pointwise
namespace CFSG.GorensteinWalter
universe u

private theorem exists_centralizing_involution_of_even_normalized
    {G : Type u} [Group G] [Finite G]
    (D : Subgroup G) {y : G} (hy : IsInvolution y)
    (hyN : y ∈ Subgroup.normalizer (D : Set G))
    (heven : Even (Nat.card D)) :
    ∃ s : G, IsInvolution s ∧ s ∈ D ∧ s * y = y * s := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  obtain ⟨T, hTinv⟩ := exists_invariant_sylow_two_of_involutive_normalizer_t26 D hyN hy2
  have h2dvd : 2 ∣ Nat.card D := by
    rcases heven with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hTcard : Nat.card (T : Subgroup D) =
      2 ^ (Nat.card D).factorization 2 := by
    simpa using T.card_eq_multiplicity
  have hfacpos : 0 < (Nat.card D).factorization 2 := by
    apply (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (Nat.card_pos (α := D)).ne').mp
    exact h2dvd
  have hTne : (T : Subgroup D) ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (T : Subgroup D) = 1 := by
      rw [hbot]
      simp
    have hpone : 2 ^ (Nat.card D).factorization 2 = 1 := by
      rw [← hTcard, hcard]
    have hfaczero : (Nat.card D).factorization 2 = 0 := by
      rcases (Nat.pow_eq_one).mp hpone with h | h
      · norm_num at h
      · exact h
    omega
  let : Fintype T := Fintype.ofFinite T
  let : Nontrivial T :=
    (Subgroup.nontrivial_iff_ne_bot (T : Subgroup D)).mpr hTne
  obtain ⟨z, hzord, hzcent⟩ := BenderGlauberman.exists_central_involution T.isPGroup'
  let a : G := (z : D)
  have haD : a ∈ D := (z : D).2
  have ha2 : a * a = 1 := by
    have haord : orderOf a = 2 := by
      simpa [a] using
        (Subgroup.orderOf_coe (z : D)).trans
          ((Subgroup.orderOf_coe z).trans hzord)
    have hpow : a ^ 2 = 1 := by
      rw [← haord]
      exact pow_orderOf_eq_one a
    simpa [pow_two] using hpow
  have haI : IsInvolution a := by
    exact ⟨by
      intro ha1
      have haord : orderOf a = 2 := by simpa [a] using hzord
      rw [ha1, orderOf_one] at haord
      omega, by simpa [pow_two] using ha2⟩
  let bD : D := ⟨y * a * y⁻¹, ((Subgroup.mem_normalizer_iff.mp hyN) a).mp haD⟩
  let b : G := (bD : G)
  have hb2 : b * b = 1 := by
    dsimp [b, bD]
    calc
      (y * a * y⁻¹) * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [ha2]; simp
  have hbI : IsInvolution b := by
    refine ⟨?_, by simpa [pow_two] using hb2⟩
    intro hb1
    apply haI.1
    calc
      a = y⁻¹ * b * y := by
        dsimp [b, bD]
        group
      _ = 1 := by rw [hb1]; simp
  have hbT : bD ∈ T := by
    simpa [bD, b] using hTinv (z : D) z.2
  have hab : a * b = b * a := by
    have hzc' := (Subgroup.mem_center_iff.mp hzcent) ⟨bD, hbT⟩
    have habD : (z : D) * bD = bD * (z : D) :=
      congrArg (fun q : T => (q : D)) hzc'.symm
    have hab0 := congrArg (fun q : D => (q : G)) habD
    simpa [a, b] using hab0
  by_cases hw : a * b = 1
  · refine ⟨a, haI, haD, ?_⟩
    have hba : b = a := by
      calc
        b = 1 * b := by simp
        _ = (a * b) * b := by simpa [hw]
        _ = a * (b * b) := by simp [mul_assoc]
        _ = a := by rw [hb2]; simp
    have hfix : y * a * y⁻¹ = a := by simpa [b, bD, hba]
    have hfix' := congrArg (fun t : G => t * y) hfix
    have hcomm : y * a = a * y := by simpa [mul_assoc] using hfix'
    exact hcomm.symm

  · let w : G := a * b
    have hwD : w ∈ D := D.mul_mem haD bD.2
    have hw2 : w * w = 1 := by
      dsimp [w]
      calc
        (a * b) * (a * b) = a * (b * a) * b := by simp [mul_assoc]
        _ = a * (a * b) * b := by rw [hab]
        _ = a * a * (b * b) := by group
        _ = 1 := by rw [ha2, hb2]; simp
    have hwI : IsInvolution w := ⟨hw, by simpa [pow_two] using hw2⟩
    refine ⟨w, hwI, hwD, ?_⟩
    have hconj : y * w * y⁻¹ = w := by
      dsimp [w]
      have hby : y * b * y⁻¹ = a := by
        dsimp [b, bD]
        rw [show y⁻¹ = y from inv_eq_of_mul_eq_one_right hy2]
        calc
          y * (y * a * y) * y = (y * y) * a * (y * y) := by group
          _ = a := by rw [hy2]; simp
      calc
        y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
        _ = b * a := by rw [show y * a * y⁻¹ = b by rfl, hby]
        _ = a * b := hab.symm
    have hconj' := congrArg (fun t : G => t * y) hconj
    have hcomm : y * w = w * y := by simpa [mul_assoc] using hconj'
    exact hcomm.symm

private theorem centralizes_of_inverted_card_one
    {G : Type u} [Group G] [Finite G]
    (X : Subgroup G) {t : G} (ht : IsInvolution t)
    (htnorm : ∀ x : G, x ∈ X → t * x * t⁻¹ ∈ X)
    (hcop : Nat.Coprime 2 (Nat.card (↥X)))
    (hcard : Nat.card {i : G // i ∈ invertedElements X t} = 1) :
    ∀ x : G, x ∈ X → t * x * t⁻¹ = x := by
  classical
  have hcardone := (Nat.card_eq_one_iff_exists).mp hcard
  rcases hcardone with ⟨i0, hi0⟩
  have hone : (1 : G) ∈ invertedElements X t := by
    exact ⟨X.one_mem, by simp⟩
  have hi_one : ∀ i : {i : G // i ∈ invertedElements X t}, i =
      (⟨1, hone⟩ : {i : G // i ∈ invertedElements X t}) := by
    intro i
    exact (hi0 i).trans (hi0 _).symm
  intro x hx
  obtain ⟨c, hc, i, hi, hxi⟩ := fact_1_5_ii_decomposition
    (G := G) (X := X) ht hcop htnorm x hx
  have hi1 : (i : G) = 1 := by
    have heq := congrArg Subtype.val (hi_one ⟨i, hi⟩)
    simpa using heq
  have hcomm : t * c = c * t :=
    (Subgroup.mem_centralizer_iff.mp hc.2) t (by simp)
  have hcent : t * c * t⁻¹ = c := by
    rw [hcomm]
    simp [mul_assoc]
  rw [hxi, hi1]
  simp [hcent]

private theorem firstCase_klein_restrictionSix_core
    {G : Type u} [Group G] [Finite G]
    (D : Subgroup G) {y : G} (hy : IsInvolution y)
    (hyN : y ∈ Subgroup.normalizer (D : Set G))
    (hyneD : y ∉ D)
    (hOindex : ((oddCoreOf D).subgroupOf D).index = 2)
    (hI : 4 ≤ Nat.card {x : G // x ∈ invertedElements D y}) :
    ∃ s : G, IsInvolution s ∧ s ∈ D ∧ s * y = y * s ∧
      (Nat.card {x : G // x ∈ invertedElements (oddCoreOf D) y} ≠ 1 ∨
       Nat.card {x : G // x ∈ invertedElements (oddCoreOf D) (s * y)} ≠ 1) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDcard : 2 ∣ Nat.card D := by
    have hOcard : Nat.card (oddCoreOf D) > 0 := Nat.card_pos
    have hmul := ((oddCoreOf D).subgroupOf D).card_mul_index
    rw [hOindex] at hmul
    have hsubcard : Nat.card ↥((oddCoreOf D).subgroupOf D) = Nat.card (oddCoreOf D) := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show oddCoreOf D ≤ D from by
          intro z hz
          rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
          exact w.2)).toEquiv
    rw [hsubcard] at hmul
    have : Nat.card D = Nat.card (oddCoreOf D) * 2 := hmul.symm
    rw [this]
    exact dvd_mul_of_dvd_right (dvd_refl 2) _
  have hevenD : Even (Nat.card D) := by
    rcases hDcard with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hyD : y ∈ Subgroup.normalizer (D : Set G) := hyN
  obtain ⟨s, hsI, hsD, hsy⟩ :=
    exists_centralizing_involution_of_even_normalized D hy hyD hevenD
  let O : Subgroup G := oddCoreOf D
  have hOnormD : IsNormalIn O D := by
    -- normality of the odd core
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (show oddCoreOf D ≤ D from by
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
        exact w.2) hx
    · intro d hd o ho
      rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
      refine Subgroup.mem_map.mpr ⟨(⟨d, hd⟩ : D) * o0 * (⟨d, hd⟩ : D)⁻¹, ?_, by simp⟩
      exact (pPrimeCore_normal (p := 2) (G := D)).conj_mem o0 ho0 (⟨d, hd⟩ : D)
  let α : D ≃* D := {
    toFun := fun d => ⟨y * (d : G) * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyN (d : G)).mp d.2⟩
    invFun := fun d => ⟨y * (d : G) * y⁻¹,
      (Subgroup.mem_normalizer_iff.mp hyN (d : G)).mp d.2⟩
    left_inv := by
      intro d; apply Subtype.ext
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right
        (by simpa [pow_two] using hy.2)
      have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
      calc
        y * (y * (d : G) * y⁻¹) * y⁻¹ =
            (y * y) * (d : G) * (y⁻¹ * y⁻¹) := by group
        _ = (d : G) := by rw [hy2, hyinv, hy2]; simp
    right_inv := by
      intro d; apply Subtype.ext
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right
        (by simpa [pow_two] using hy.2)
      have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
      calc
        y * (y * (d : G) * y⁻¹) * y⁻¹ =
            (y * y) * (d : G) * (y⁻¹ * y⁻¹) := by group
        _ = (d : G) := by rw [hy2, hyinv, hy2]; simp
    map_mul' := by intro a b; apply Subtype.ext; simp [mul_assoc] }
  have hOmap : (pPrimeCore 2 (↥D)).map α.toMonoidHom = pPrimeCore 2 (↥D) :=
    (Subgroup.characteristic_iff_map_eq.mp (pPrimeCore_characteristic (p := 2))) α
  have hyO_forward : ∀ o : G, o ∈ O → y * o * y⁻¹ ∈ O := by
    intro o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, hoeq⟩
    have hmap : α o0 ∈ pPrimeCore 2 (↥D) := by
      rw [← hOmap]
      exact Subgroup.mem_map.mpr ⟨o0, ho0, rfl⟩
    refine Subgroup.mem_map.mpr ⟨α o0, hmap, ?_⟩
    have hoeq' : (o0 : G) = o := hoeq
    calc
      (α o0 : G) = y * (o0 : G) * y⁻¹ := rfl
      _ = y * o * y⁻¹ := by rw [hoeq']
  have hyOnorm : y ∈ Subgroup.normalizer (O : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro o
    constructor
    · exact hyO_forward o
    · intro ho
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right
        (by simpa [pow_two] using hy.2)
      have hback := hyO_forward (y * o * y⁻¹) ho
      have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
      have hback' : y * (y * o * y⁻¹) * y⁻¹ ∈ O := by
        simpa [hyinv] using hback
      have heq : y * (y * o * y⁻¹) * y⁻¹ = o := by
        calc
          y * (y * o * y⁻¹) * y⁻¹ = (y * y) * o * (y⁻¹ * y⁻¹) := by group
          _ = o := by rw [hy2, hyinv, hy2]; simp
      rw [heq] at hback'
      exact hback'
  have hOcard : Nat.card (↥O) = Nat.card (pPrimeCore 2 (↥D)) := by
    simpa [O, oddCoreOf] using
      (Subgroup.card_map_of_injective (K := pPrimeCore 2 (↥D))
        (D : Subgroup G).subtype_injective)
  have hOcop : Nat.Coprime 2 (Nat.card (↥O)) := by
    rw [hOcard]
    exact pPrimeCore_coprime_card (p := 2) (G := D)
  have hsNormO : s ∈ Subgroup.normalizer (O : Set G) :=
    (le_normalizer_of_isNormalIn hOnormD) hsD
  have hsyI : IsInvolution (s * y) := by
    refine ⟨?_, ?_⟩
    · intro h
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right
        (by simpa [pow_two] using hy.2)
      have hs_eq : s = y⁻¹ := by
        calc
          s = s * (y * y⁻¹) := by simp
          _ = (s * y) * y⁻¹ := by group
          _ = y⁻¹ := by rw [h]; simp
      apply hyneD
      have hseq : s = y := hs_eq.trans hyinv
      simpa [← hseq] using hsD
    · have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
      have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
      calc
        (s * y) ^ 2 = s * y * (s * y) := by rw [pow_two]
        _ = s * (y * s) * y := by group
        _ = s * (s * y) * y := by rw [hsy]
        _ = (s * s) * (y * y) := by group
        _ = 1 := by rw [hs2, hy2]; simp
  have hsyNormO : s * y ∈ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normalizer (O : Set G)).mul_mem hsNormO hyOnorm
  by_cases hcardY : Nat.card {x : G // x ∈ invertedElements O y} = 1
  · by_cases hcardSY :
        Nat.card {x : G // x ∈ invertedElements O (s * y)} = 1
    · have hcy : ∀ o : G, o ∈ O → y * o * y⁻¹ = o :=
        centralizes_of_inverted_card_one O hy hyO_forward hOcop hcardY
      have hsy_forward : ∀ o : G, o ∈ O →
          s * y * o * (s * y)⁻¹ ∈ O := by
        intro o ho
        exact (Subgroup.mem_normalizer_iff.mp hsyNormO o).mp ho
      have hsycent : ∀ o : G, o ∈ O →
          s * y * o * (s * y)⁻¹ = o :=
        centralizes_of_inverted_card_one O hsyI hsy_forward hOcop hcardSY
      have hsfix : ∀ o : G, o ∈ O → s * o * s⁻¹ = o := by
        intro o ho
        have hyo := hcy o ho
        have hso := hsycent o ho
        calc
          s * o * s⁻¹ = s * (y * o * y⁻¹) * s⁻¹ := by rw [hyo]
          _ = (s * y) * o * (s * y)⁻¹ := by
            simp [mul_inv_rev]
            group
          _ = o := hso
      have hsnotO : s ∉ O := by
        intro hsO
        have hsOelem : (⟨s, hsO⟩ : O) ^ 2 = 1 := by
          apply Subtype.ext
          have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
          simpa [pow_two] using hs2
        have hsOone := eq_one_of_sq_eq_one_of_coprime_two
          (G := ↥O) hOcop hsOelem
        apply hsI.1
        simpa using congrArg Subtype.val hsOone
      have hcases : ∀ x : G, x ∈ invertedElements D y → x = 1 ∨ x = s := by
        intro x hx
        have hxD : x ∈ D := hx.1
        by_cases hxO : x ∈ O
        · have hyx := hcy x hxO
          have hxinv : x = x⁻¹ := by simpa [hyx] using hx.2
          have hxsq : x ^ 2 = 1 := by
            calc
              x ^ 2 = x * x := by rw [pow_two]
              _ = x * x⁻¹ := congrArg (fun z : G => x * z) hxinv
              _ = 1 := mul_inv_cancel x
          have hxoneO : (⟨x, hxO⟩ : O) = 1 := by
            apply eq_one_of_sq_eq_one_of_coprime_two hOcop
            apply Subtype.ext
            simpa [pow_two] using hxsq
          exact Or.inl (by simpa using congrArg Subtype.val hxoneO)
        · have hmulO : s * x ∈ O := by
            have hiff := Subgroup.mul_mem_iff_of_index_two hOindex
              (a := (⟨s, hsD⟩ : D)) (b := (⟨x, hxD⟩ : D))
            have haO : ¬ (⟨s, hsD⟩ : D) ∈ O.subgroupOf D := by
              intro ha
              exact hsnotO (Subgroup.mem_subgroupOf.mp ha)
            have hbO : ¬ (⟨x, hxD⟩ : D) ∈ O.subgroupOf D := by
              intro hb
              exact hxO (Subgroup.mem_subgroupOf.mp hb)
            have hmem : (⟨s, hsD⟩ : D) * (⟨x, hxD⟩ : D) ∈ O.subgroupOf D :=
              hiff.mpr ⟨fun ha => (haO ha).elim, fun hb => (hbO hb).elim⟩
            have hmem' := Subgroup.mem_subgroupOf.mp hmem
            simpa using hmem'
          have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
          have hxeq : x = s * (s * x) := by
            calc
              x = (s * s) * x := by rw [hs2]; simp
              _ = s * (s * x) := by group
          have hsyfix : y * s * y⁻¹ = s := by
            calc
              y * s * y⁻¹ = s * y * y⁻¹ := by rw [hsy]
              _ = s := by simp
          have hysxfix : y * (s * x) * y⁻¹ = s * x := hcy (s * x) hmulO
          have hxfix : y * x * y⁻¹ = x := by
            have hxeq' := congrArg (fun z : G => y * z * y⁻¹) hxeq
            calc
              y * x * y⁻¹ = y * (s * (s * x)) * y⁻¹ := hxeq'
              _ = (y * s * y⁻¹) * (y * (s * x) * y⁻¹) := by group
              _ = s * (s * x) := by rw [hsyfix, hysxfix]
              _ = x := hxeq.symm
          have hxinv : x = x⁻¹ := by simpa [hxfix] using hx.2
          have hxsq : x ^ 2 = 1 := by
            calc
              x ^ 2 = x * x := by rw [pow_two]
              _ = x * x⁻¹ := congrArg (fun z : G => x * z) hxinv
              _ = 1 := mul_inv_cancel x
          have hsxcomm : s * x = x * s := by
            have hsxfix : s * (s * x) * s⁻¹ = s * x := hsfix (s * x) hmulO
            have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
            have hh := congrArg (fun z : G => z * s) hsxfix
            rw [hs_inv] at hh
            have hh0 : s * (s * x) = (s * x) * s := by
              simpa [mul_assoc, hs2] using hh
            have hh0' : x = (s * x) * s := by
              calc
                x = (s * s) * x := by rw [hs2]; simp
                _ = s * (s * x) := by group
                _ = (s * x) * s := hh0
            have hh1 := congrArg (fun z : G => z * s) hh0'
            have hh' : x * s = s * x := by
              calc
                x * s = ((s * x) * s) * s := hh1
                _ = (s * x) * (s * s) := by group
                _ = s * x := by rw [hs2]; simp
            exact hh'.symm
          have hsqO : (s * x) ^ 2 = 1 := by
            calc
              (s * x) ^ 2 = (s * x) * (s * x) := by rw [pow_two]
              _ = s * (x * s) * x := by group
              _ = s * (s * x) * x := by rw [hsxcomm]
              _ = (s * s) * (x * x) := by group
              _ = x * x := by rw [hs2]; simp
              _ = 1 := by simpa [pow_two] using hxsq
          have hsoone : s * x = 1 := by
            have hsub : (⟨s * x, hmulO⟩ : O) ^ 2 = 1 := by
              apply Subtype.ext
              simpa using hsqO
            exact congrArg Subtype.val
              (eq_one_of_sq_eq_one_of_coprime_two hOcop hsub)
          exact Or.inr (by rw [hxeq, hsoone]; simp)
      let F : {x : G // x ∈ invertedElements D y} → Fin 2 := fun x =>
        if x.1 = 1 then 0 else 1
      have hF_inj : Function.Injective F := by
        intro x z hF
        have hsne : s ≠ 1 := hsI.1
        rcases hcases x x.2 with hx1 | hxs
        · rcases hcases z z.2 with hz1 | hzs
          · apply Subtype.ext; simpa [hx1, hz1]
          · exfalso
            have h01 : (0 : Fin 2) = 1 := by simpa [F, hx1, hzs, hsne] using hF
            exact Fin.zero_ne_one h01
        · rcases hcases z z.2 with hz1 | hzs
          · exfalso
            have h10 : (1 : Fin 2) = 0 := by simpa [F, hxs, hz1, hsne] using hF
            exact Fin.zero_ne_one h10.symm
          · apply Subtype.ext; simpa [hxs, hzs]
      have hle : Nat.card {x : G // x ∈ invertedElements D y} ≤ 2 := by
        simpa using Nat.card_le_card_of_injective F hF_inj
      exfalso
      omega
    · exact ⟨s, hsI, hsD, hsy, by simpa [O] using Or.inr hcardSY⟩
  · exact ⟨s, hsI, hsD, hsy, by simpa [O] using Or.inl hcardY⟩

/-- Source restriction (6), with the odd-core index-two fact exposed as the
separate structural premise used by the proof. -/
public theorem firstCase_klein_restrictionSix_oddCore_of_index_two
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hOindex :
      ((oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)).subgroupOf
        (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)).index = 2)
    (hI : 4 ≤ Nat.card {x : G // x ∈ invertedElements c.Hhat y}) :
    ∃ s : G, IsInvolution s ∧
      s ∈ (c.Hhat ⊓ conjugateSubgroup c.Hhat y) ∧ s * y = y * s ∧
      (Nat.card {x : G // x ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y} ≠ 1 ∨
       Nat.card {x : G // x ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) (s * y)} ≠ 1) := by
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyN : y ∈ Subgroup.normalizer (D : Set G) := by
    simpa [D] using involution_mem_normalizer_inf_conjugateSubgroup c.Hhat hy2
  have hyneD : y ∉ D := by
    intro hyD
    exact hyH ((show D ≤ c.Hhat from inf_le_left) hyD)
  have hI_D : 4 ≤ Nat.card {x : G // x ∈ invertedElements D y} := by
    let f : {x : G // x ∈ invertedElements c.Hhat y} →
        {x : G // x ∈ invertedElements D y} := fun x => by
      have hconj : x.1 ∈ conjugateSubgroup c.Hhat y := by
        change x.1 ∈ c.Hhat.map (MulAut.conj y).toMonoidHom
        exact Subgroup.mem_map.mpr ⟨x.1⁻¹, c.Hhat.inv_mem x.2.1,
          by
            change y * x.1⁻¹ * y⁻¹ = x.1
            calc
              y * x.1⁻¹ * y⁻¹ = (y * x.1 * y⁻¹)⁻¹ := by group
              _ = (x.1⁻¹)⁻¹ := by rw [x.2.2]
              _ = x.1 := by simp⟩
      exact ⟨x.1, ⟨x.2.1, hconj⟩, x.2.2⟩
    have hf : Function.Injective f := by
      intro x z h
      have hv : (x.1 : G) = z.1 :=
        congrArg (fun w : {x : G // x ∈ invertedElements D y} => (w : G)) h
      exact Subtype.ext hv
    exact le_trans hI (Nat.card_le_card_of_injective f hf)
  have hD := firstCase_klein_restrictionSix_core D hy hyN hyneD (by
    simpa [D] using hOindex) hI_D
  simpa [D] using hD

end CFSG.GorensteinWalter
