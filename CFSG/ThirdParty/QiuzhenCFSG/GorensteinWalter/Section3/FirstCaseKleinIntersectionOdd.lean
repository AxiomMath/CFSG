module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionD6
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseEvenNormalizedInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseDihedralThreeCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionFive
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionNormalizerInfConjugate
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
noncomputable section
open scoped Pointwise
namespace CFSG.GorensteinWalter
universe u

public theorem firstCase_klein_intersection_odd_of_index_six
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hindex :
      let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
      let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
      (N.subgroupOf D).index = 6) :
    let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
    let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
    Nat.Coprime 2 (Nat.card N) := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  let B : Subgroup G := V ⊔ c.U
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
  let N : Subgroup G := D ⊓ B
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyN : y ∈ Subgroup.normalizer (D : Set G) := by
    simpa [D] using involution_mem_normalizer_inf_conjugateSubgroup c.Hhat hy2
  have hBnorm : IsNormalIn B c.Hhat := by
    simpa [B, V] using firstCase_klein_VU_normal_in_Hhat hmin c
  have hDle : D ≤ c.Hhat := inf_le_left
  have hNnorm : (N.subgroupOf D).Normal := by
    apply (Subgroup.normal_subgroupOf_iff (show N ≤ D from inf_le_left)).2
    intro n d hn hd
    refine ⟨?_, ?_⟩
    · exact D.mul_mem (D.mul_mem hd ((show N ≤ D from inf_le_left) hn)) (D.inv_mem hd)
    · exact hBnorm.2 d (hDle hd) n ((show N ≤ B from inf_le_right) hn)
  let : (N.subgroupOf D).Normal := hNnorm
  have hindex' : (N.subgroupOf D).index = 6 := by
    simpa [D, N, B, V] using hindex
  obtain ⟨eD6⟩ := firstCase_klein_intersection_quotient_d6
    hmin c hfirst hklein hy hyH hindex'
  let q : D →* (D ⧸ N.subgroupOf D) := QuotientGroup.mk' (N.subgroupOf D)
  have hmaple : (pCore 2 (↥D)).map q ≤ pCore 2 (D ⧸ N.subgroupOf D) := by
    apply le_sSup
    constructor
    · exact (pCore_normal (p := 2) (G := D)).map q
        (QuotientGroup.mk'_surjective (N.subgroupOf D))
    · exact (pCore_isPGroup (p := 2) (G := D)).map q
  have hqcore : pCore 2 (D ⧸ N.subgroupOf D) = ⊥ := by
    have hmap : (pCore 2 (D ⧸ N.subgroupOf D)).map eD6.toMonoidHom = ⊥ := by
      rw [pCore_map_iso 2 eD6, pCore_two_dihedral_three_eq_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore 2 (D ⧸ N.subgroupOf D)) eD6.injective).mp hmap
  have hmapbot : (pCore 2 (↥D)).map q = ⊥ :=
    le_antisymm (hmaple.trans_eq hqcore) bot_le
  have hPcoreLe : pCore 2 (↥D) ≤ N.subgroupOf D := by
    have hker : q.ker = N.subgroupOf D := by
      ext z
      exact QuotientGroup.eq_one_iff (N := N.subgroupOf D) z
    have := (Subgroup.map_eq_bot_iff (pCore 2 (↥D))).mp hmapbot
    rw [hker] at this
    exact this
  have hVklein : IsKleinFour V := firstCase_klein_V_klein c hklein
  have hVcentU : V ≤ Subgroup.centralizer (c.U : Set G) := by
    have h26 := theorem_2_6 hmin c
    simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hVnormU : V ≤ Subgroup.normalizer (c.U : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv u hu
    have hcomm : v * u = u * v :=
      (Subgroup.mem_centralizer_iff.mp (hVcentU hv) u hu).symm
    have hfix : v * u * v⁻¹ = u := by rw [hcomm]; group
    simpa [hfix] using hu
  have hVUset : (B : Set G) = (V : Set G) * (c.U : Set G) := by
    exact Subgroup.coe_mul_of_left_le_normalizer_right V c.U hVnormU
  have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
    have h26 := theorem_2_6 hmin c
    rw [h26.1]
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
    rw [show Nat.card (oddCoreOf c.Hhat) = Nat.card (pPrimeCore 2 c.Hhat) by
      simpa [oddCoreOf] using
        (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.Hhat)
          c.Hhat.subtype_injective)]
    exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
  have hnotEven : ¬ Even (Nat.card N) := by
    intro hEven
    have h2dvd : 2 ∣ Nat.card N := by
      rcases hEven with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2dvd
    have hxordG : orderOf (x : G) = 2 := by
      simpa using (Subgroup.orderOf_coe x).trans hxord
    have hxI : IsInvolution (x : G) := by
      refine ⟨?_, ?_⟩
      · intro hx1
        have : orderOf (x : G) = 1 := by simpa [hx1]
        omega
      · rw [← hxordG]
        exact pow_orderOf_eq_one (x : G)
    have hxB : (x : G) ∈ B :=
      (show N ≤ B from (inf_le_right : D ⊓ B ≤ B)) x.2
    have hxVU : (x : G) ∈ (V : Set G) * (c.U : Set G) := by
      rw [← hVUset]
      exact hxB
    rcases Set.mem_mul.mp hxVU with ⟨v, hv, u, hu, hvux⟩
    have hvucomm : v * u = u * v :=
      (Subgroup.mem_centralizer_iff.mp (hVcentU hv) u hu).symm
    have hv2 : v * v = 1 := by
      simpa [pow_two] using congrArg Subtype.val
        (hVklein.mul_self (⟨v, hv⟩ : V))
    have hu2 : u ^ 2 = 1 := by
      calc
        u ^ 2 = (v * v) * (u * u) := by rw [pow_two, hv2]; simp
        _ = v * (v * u) * u := by group
        _ = v * (u * v) * u := by rw [hvucomm]
        _ = (v * u) ^ 2 := by rw [pow_two]; group
        _ = (x : G) ^ 2 := by rw [← hvux]
        _ = 1 := hxI.2
    have hu1 : u = 1 := by
      have huord : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
      have huordU : orderOf u ∣ Nat.card c.U :=
        Subgroup.orderOf_dvd_natCard c.U hu
      have hcop : Nat.Coprime 2 (orderOf u) :=
        Nat.Coprime.of_dvd_right huordU hUcop
      have huord1 : orderOf u = 1 := hcop.symm.eq_one_of_dvd huord
      exact orderOf_eq_one_iff.mp huord1
    have hxV : (x : G) ∈ V := by
      rw [← hvux, hu1]
      simpa using hv
    let W : Subgroup G := N ⊓ V
    have hWleD : W ≤ D :=
      (show W ≤ N from inf_le_left).trans (show N ≤ D from inf_le_left)
    have hVnormH : IsNormalIn V c.Hhat := by
      refine ⟨(show V ≤ c.Hhat from by
        dsimp [V, twoCoreOf]
        exact Subgroup.map_subtype_le (pCore 2 c.Hhat)), ?_⟩
      intro d hd v0 hv0
      have h26 := theorem_2_6 hmin c
      change d * v0 * d⁻¹ ∈ twoCoreOf c.Hhat
      rcases Subgroup.mem_map.mp hv0 with ⟨z0, hz0, hzval⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨d, hd⟩ : c.Hhat) * z0 * (⟨d, hd⟩ : c.Hhat)⁻¹,
        (pCore_normal (p := 2) (G := c.Hhat)).conj_mem z0 hz0
          (⟨d, hd⟩ : c.Hhat), ?_⟩
      simpa [hzval]
    have hWnorm : (W.subgroupOf D).Normal := by
      apply (Subgroup.normal_subgroupOf_iff hWleD).2
      intro w d hw hd
      refine ⟨?_, ?_⟩
      · have hconjN : d * w * d⁻¹ ∈ N := by
          refine ⟨D.mul_mem (D.mul_mem hd
            ((show N ≤ D from inf_le_left) ((show W ≤ N from inf_le_left) hw)))
            (D.inv_mem hd), ?_⟩
          exact hBnorm.2 d (hDle hd) w
            ((show W ≤ B from (show W ≤ N from inf_le_left).trans inf_le_right) hw)
        exact hconjN
      · exact hVnormH.2 d (hDle hd) w ((show W ≤ V from inf_le_right) hw)
    have hVp : IsPGroup 2 V := by
      apply IsPGroup.of_card (n := 2)
      simpa [hVklein.card_four]
    have hWp : IsPGroup 2 (W.subgroupOf D) := by
      intro w0
      obtain ⟨k, hk⟩ := hVp ⟨(w0 : G), (show W ≤ V from inf_le_right) w0.2⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      have hk' := congrArg (fun z : V => (z : G)) hk
      apply Subtype.ext
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hk'
    have hxW : (x : G) ∈ W := ⟨x.2, hxV⟩
    have hWne : W.subgroupOf D ≠ ⊥ := by
      intro hbot
      have hxbot : (⟨(x : G), hWleD hxW⟩ : D) ∈ (⊥ : Subgroup D) := by
        rw [← hbot]
        exact Subgroup.mem_subgroupOf.mpr hxW
      exact hxI.1 (congrArg Subtype.val (Subgroup.mem_bot.mp hxbot))
    have hPne : pCore 2 (↥D) ≠ ⊥ := by
      intro hbot
      have hPle : W.subgroupOf D ≤ pCore 2 (↥D) := le_sSup ⟨hWnorm, hWp⟩
      have hxP : (⟨(x : G), hWleD hxW⟩ : D) ∈ pCore 2 (↥D) :=
        hPle (Subgroup.mem_subgroupOf.mpr hxW)
      rw [hbot] at hxP
      exact hxI.1 (congrArg Subtype.val (Subgroup.mem_bot.mp hxP))
    let P0 : Subgroup G := (pCore 2 (↥D)).map D.subtype
    have hP0leN : P0 ≤ N := by
      have hmapN : (N.subgroupOf D).map D.subtype = N :=
        Subgroup.map_subgroupOf_eq_of_le (show N ≤ D from inf_le_left)
      rw [← hmapN]
      exact Subgroup.map_mono hPcoreLe
    have hP0ne : P0 ≠ ⊥ := by
      intro hbot
      exact hPne ((Subgroup.map_eq_bot_iff_of_injective
        (pCore 2 (↥D)) D.subtype_injective).mp hbot)
    have hP0p : IsPGroup 2 P0 := by
      simpa [P0] using
        (pCore_isPGroup (p := 2) (G := ↥D)).map D.subtype
    have hP0even : Even (Nat.card P0) := by
      obtain ⟨n, hn⟩ := hP0p.exists_card_eq
      have hn0 : n ≠ 0 := by
        intro hnzero
        apply hP0ne
        apply (Subgroup.eq_bot_iff_card P0).2
        rw [hn, hnzero]
        simp
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      refine ⟨2 ^ m, ?_⟩
      rw [hn, pow_succ]
      ring
    let α : D ≃* D := {
      toFun := fun d => ⟨y * (d : G) * y⁻¹,
        (Subgroup.mem_normalizer_iff.mp hyN (d : G)).mp d.2⟩
      invFun := fun d => ⟨y * (d : G) * y⁻¹,
        (Subgroup.mem_normalizer_iff.mp hyN (d : G)).mp d.2⟩
      left_inv := by
        intro d
        apply Subtype.ext
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
        calc
          y * (y * (d : G) * y⁻¹) * y⁻¹ =
              (y * y) * (d : G) * (y⁻¹ * y⁻¹) := by group
          _ = (d : G) := by rw [hy2, hyinv, hy2]; simp
      right_inv := by
        intro d
        apply Subtype.ext
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
        calc
          y * (y * (d : G) * y⁻¹) * y⁻¹ =
              (y * y) * (d : G) * (y⁻¹ * y⁻¹) := by group
          _ = (d : G) := by rw [hy2, hyinv, hy2]; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp [mul_assoc] }
    have hPmap : (pCore 2 (↥D)).map α.toMonoidHom = pCore 2 (↥D) :=
      (Subgroup.characteristic_iff_map_eq.mp
        (pCore_characteristic (p := 2))) α
    have hyP_forward : ∀ z : G, z ∈ P0 → y * z * y⁻¹ ∈ P0 := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, hzeq⟩
      have hzeq' : (z0 : G) = z := hzeq
      have hmap : α z0 ∈ pCore 2 (↥D) := by
        rw [← hPmap]
        exact Subgroup.mem_map.mpr ⟨z0, hz0, rfl⟩
      refine Subgroup.mem_map.mpr ⟨α z0, hmap, ?_⟩
      calc
        (α z0 : G) = y * (z0 : G) * y⁻¹ := rfl
        _ = y * z * y⁻¹ := by rw [hzeq']
    have hyP : y ∈ Subgroup.normalizer (P0 : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · exact hyP_forward z
      · intro hz
        have hback := hyP_forward (y * z * y⁻¹) hz
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
        have heq : y * (y * z * y⁻¹) * y⁻¹ = z := by
          calc
            y * (y * z * y⁻¹) * y⁻¹ =
                (y * y) * z * (y⁻¹ * y⁻¹) := by group
            _ = z := by rw [hy2, hyinv, hy2]; simp
        rw [heq] at hback
        exact hback
    obtain ⟨s, hsI, hsP0, hsy⟩ :=
      exists_centralizing_involution_of_even_normalized P0 hy hyP hP0even
    have hsB : s ∈ B := hP0leN hsP0 |>.2
    have hsInv : y * s * y⁻¹ = s⁻¹ := by
      have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
      rw [← hsy]
      simp [hsinv]
    have hcard := firstCase_klein_restrictionFive hmin c hfirst hklein y hy hyH
    have hone : (1 : G) ∈ invertedElements B y := ⟨B.one_mem, by simp⟩
    have hcardB : Nat.card {x : G // x ∈ invertedElements B y} = 1 := by
      change Nat.card {x : G // x ∈ invertedElements
        (twoCoreOf c.Hhat ⊔ c.U) y} = 1
      exact hcard
    obtain ⟨i0, hi0⟩ := (Nat.card_eq_one_iff_exists).mp hcardB
    have hsi : (⟨s, ⟨hsB, hsInv⟩⟩ : {x : G // x ∈ invertedElements B y}) = i0 :=
      hi0 _
    have h1i : (⟨1, hone⟩ : {x : G // x ∈ invertedElements B y}) = i0 :=
      hi0 _
    have hsone : s = 1 := by
      have heq := congrArg Subtype.val (hsi.trans h1i.symm)
      simpa using heq
    exact hsI.1 hsone
  simpa [D, N, B, V] using
    (Nat.coprime_two_left.mpr (Nat.not_even_iff_odd.mp hnotEven))

end CFSG.GorensteinWalter
