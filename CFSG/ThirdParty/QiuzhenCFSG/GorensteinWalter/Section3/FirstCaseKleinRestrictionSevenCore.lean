module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseBaseInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSix
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreFittingTI
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvertedPCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
open scoped Pointwise
namespace CFSG.GorensteinWalter
universe u

private theorem probe_U_coprime
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G) :
    Nat.Coprime 2 (Nat.card c.U) := by
  have h26 := theorem_2_6 hmin c
  rw [h26.1]
  change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
  rw [show Nat.card (oddCoreOf c.Hhat) = Nat.card (pPrimeCore 2 c.Hhat) by
    simpa [oddCoreOf] using
      (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.Hhat)
        c.Hhat.subtype_injective)]
  exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)

private theorem probe_B_involution_mem_V
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {z : G} (hzB : z ∈ twoCoreOf c.Hhat ⊔ c.U)
    (hzI : IsInvolution z) :
    z ∈ twoCoreOf c.Hhat := by
  let V : Subgroup G := twoCoreOf c.Hhat
  have hVK : IsKleinFour V := by simpa [V] using firstCase_klein_V_klein c hklein
  have hVcent : V ≤ Subgroup.centralizer (c.U : Set G) := by
    have h26 := theorem_2_6 hmin c
    simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hVnorm : V ≤ Subgroup.normalizer (c.U : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv u hu
    have hcomm : v * u = u * v :=
      (Subgroup.mem_centralizer_iff.mp (hVcent hv) u hu).symm
    have hfix : v * u * v⁻¹ = u := by rw [hcomm]; group
    simpa [hfix] using hu
  have hVUset : ((V ⊔ c.U : Subgroup G) : Set G) =
      (V : Set G) * (c.U : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right V c.U hVnorm
  have hzVU : z ∈ (V : Set G) * (c.U : Set G) := by
    rw [← hVUset]
    exact hzB
  rcases Set.mem_mul.mp hzVU with ⟨v, hv, u, hu, hvuz⟩
  have hv2 : v * v = 1 := by
    simpa [pow_two] using congrArg Subtype.val (hVK.mul_self (⟨v, hv⟩ : V))
  have hcomm : v * u = u * v :=
    (Subgroup.mem_centralizer_iff.mp (hVcent hv) u hu).symm
  have hu2 : u ^ 2 = 1 := by
    calc
      u ^ 2 = (v * v) * (u * u) := by rw [pow_two, hv2]; simp
      _ = v * (v * u) * u := by group
      _ = v * (u * v) * u := by rw [hcomm]
      _ = (v * u) ^ 2 := by rw [pow_two]; group
      _ = z ^ 2 := by rw [← hvuz]
      _ = 1 := by simpa using hzI.2
  have huord : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  have huordU : orderOf u ∣ Nat.card c.U :=
    Subgroup.orderOf_dvd_natCard c.U hu
  have hcop : Nat.Coprime 2 (orderOf u) :=
    Nat.Coprime.of_dvd_right huordU (probe_U_coprime hmin c)
  have huord1 : orderOf u = 1 := hcop.symm.eq_one_of_dvd huord
  have hu1 : u = 1 := orderOf_eq_one_iff.mp huord1
  rw [← hvuz, hu1]
  simpa using hv

private theorem probe_X_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) :
    Nat.card X = 3 := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  let B : Subgroup G := V ⊔ c.U
  have hBcard : Nat.card {z : G // z ∈ invertedElements B y} = 1 := by
    simpa [B, V] using firstCase_klein_restrictionFive hmin c hfirst hklein y hy hyH
  have hXBinf : X ⊓ B = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have hzI : z ∈ invertedElements B y := ⟨hz.2, (hXinv z hz.1).2⟩
    have hone : (1 : G) ∈ invertedElements B y := ⟨B.one_mem, by simp⟩
    obtain ⟨z0, hz0⟩ := Nat.card_eq_one_iff_exists.mp hBcard
    have hzEq : (⟨z, hzI⟩ : {w : G // w ∈ invertedElements B y}) = z0 := hz0 _
    have h1Eq : (⟨1, hone⟩ : {w : G // w ∈ invertedElements B y}) = z0 := hz0 _
    have hz1 : z = 1 := congrArg Subtype.val (hzEq.trans h1Eq.symm)
    exact Subgroup.mem_bot.mpr hz1
  let H : Subgroup G := c.Hhat
  let N0 : Subgroup H := pCore 2 H ⊔ pPrimeCore 2 H
  have hN0normal : N0.Normal := by
    dsimp [N0, H]
    infer_instance
  let q : H →* (H ⧸ N0) := QuotientGroup.mk' N0
  have hXleH : X ≤ H := hXle
  let i : X →* H :=
    { toFun := fun x => ⟨(x : G), hXleH x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  let f : X →* (H ⧸ N0) := q.comp i
  have hmapN : (N0.map H.subtype) = B := by
    have hUeq : c.U = oddCoreOf c.Hhat := (theorem_2_6 hmin c).1
    dsimp [N0, H, B, V]
    rw [Subgroup.map_sup]
    simp [twoCoreOf, oddCoreOf, hUeq]
  have hinj : Function.Injective f := by
    intro a b hab
    have hq : f a * (f b)⁻¹ = 1 := by rw [hab]; simp
    have hq' : q (i a * (i b)⁻¹) = 1 := by simpa [f] using hq
    have hmemN0 : i a * (i b)⁻¹ ∈ N0 :=
      (QuotientGroup.eq_one_iff (i a * (i b)⁻¹)).mp hq'
    have hmemB : (a : G) * (b : G)⁻¹ ∈ B := by
      have hmap : (i a * (i b)⁻¹ : H) ∈ N0 := hmemN0
      have hmapG : ((i a * (i b)⁻¹ : H) : G) ∈ N0.map H.subtype :=
        Subgroup.mem_map.mpr ⟨i a * (i b)⁻¹, hmemN0, rfl⟩
      rw [hmapN] at hmapG
      change (a : G) * (b : G)⁻¹ ∈ B at hmapG
      exact hmapG
    have hmemX : (a : G) * (b : G)⁻¹ ∈ X :=
      X.mul_mem a.2 (X.inv_mem b.2)
    have hbot : (a : G) * (b : G)⁻¹ ∈ X ⊓ B := ⟨hmemX, hmemB⟩
    rw [hXBinf] at hbot
    have habG : (a : G) * (b : G)⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    apply Subtype.ext
    exact mul_inv_eq_one.mp habG
  have hdiv : Nat.card X ∣ Nat.card (H ⧸ N0) := by
    have hdiv' : Nat.card f.range ∣ Nat.card (H ⧸ N0) :=
      f.range.card_subgroup_dvd_card
    have hcardrange : Nat.card f.range = Nat.card X :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hcardrange] at hdiv'
    exact hdiv'
  have hqcard : Nat.card (H ⧸ N0) = 6 := by
    obtain ⟨e⟩ := firstCase_klein_quotient_d6 hmin c hfirst hklein
    calc
      Nat.card (H ⧸ N0) = Nat.card (DihedralGroup 3) := Nat.card_congr e.toEquiv
      _ = 6 := DihedralGroup.nat_card
  rw [hqcard] at hdiv
  have hle : Nat.card X ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
  have hne1 : Nat.card X ≠ 1 := by
    intro h
    exact hXne (Subgroup.eq_bot_of_card_eq X h)
  have hne2 : Nat.card X ≠ 2 := by
    intro h
    rw [h] at hXodd
    norm_num at hXodd
  have hne6 : Nat.card X ≠ 6 := by
    intro h
    rw [h] at hXodd
    norm_num at hXodd
  interval_cases hcard : Nat.card X <;> simp_all

private theorem probe_FU_centralizes_X_of_inverted
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {X : Subgroup G} {s0 : G}
    (hXcard : Nat.card X = 3)
    (hXle : X ≤ c.Hhat)
    (hsH : s0 ∈ c.Hhat) (hsI : IsInvolution s0)
    (hsV : s0 ∉ twoCoreOf c.Hhat)
    (hsNorm : s0 ∈ Subgroup.normalizer (X : Set G))
    (hsInv : ∀ x : G, x ∈ X → s0 * x * s0⁻¹ = x⁻¹) :
    c.FU ≤ Subgroup.centralizer (X : Set G) := by
  obtain ⟨_d, _K, _hHall, _hKne, hKall⟩ :=
    firstCase_klein_data_complete hmin c hfirst hklein
  have hcomm : ⁅c.Hhat, Subgroup.zpowers s0⁆ ≤
      Subgroup.centralizer (c.FU : Set G) :=
    (hKall s0 hsH hsI hsV).2
  have hinv : BenderGlauberman.IsInvertedBy s0 X := by
    intro x hx
    exact hsInv x hx
  have hXleComm : X ≤ ⁅c.Hhat, Subgroup.zpowers s0⁆ := by
    intro x hx
    have hxord : orderOf x ∣ Nat.card X :=
      Subgroup.orderOf_dvd_natCard X hx
    have hx3 : x ^ 3 = 1 := by
      rw [hXcard] at hxord
      exact (orderOf_dvd_iff_pow_eq_one.mp hxord)
    have hx2comm := square_mem_commutator_of_inverted s0 hsI X hinv x hx
    have hx4comm : x ^ 4 ∈ ⁅X, Subgroup.zpowers s0⁆ := by
      simpa [pow_two, pow_succ, mul_assoc] using
        (⁅X, Subgroup.zpowers s0⁆).pow_mem hx2comm 2
    have hx4comm' : x ^ 4 ∈ ⁅c.Hhat, Subgroup.zpowers s0⁆ :=
      (Subgroup.commutator_mono hXle le_rfl) hx4comm
    have hx4 : x ^ 4 = x := by
      calc
        x ^ 4 = x ^ 3 * x := by rw [show 4 = 3 + 1 by norm_num, pow_succ]
        _ = x := by rw [hx3]; simp
    rw [hx4] at hx4comm'
    exact hx4comm'
  intro f hf
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hcomm (hXleComm hx)) f hf).symm

private theorem probe_dihedral_three_no_order_six
    (z : DihedralGroup 3) : orderOf z ≠ 6 := by
  rcases dihedralGroup_cases z with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hpow : (DihedralGroup.r i : DihedralGroup 3)^3 = 1 := by
      rw [DihedralGroup.r_pow]
      have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
      change DihedralGroup.r (i * (3 : ZMod 3)) = 1
      rw [h3, mul_zero, DihedralGroup.r_zero]
    have hdvd : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hpow
    intro h
    rw [h] at hdvd
    norm_num at hdvd
  · have hsq : (DihedralGroup.sr i : DihedralGroup 3)^2 = 1 := by
      simpa [pow_two] using DihedralGroup.sr_mul_self i
    have hdvd : orderOf (DihedralGroup.sr i : DihedralGroup 3) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hsq
    intro h
    rw [h] at hdvd
    norm_num at hdvd

private theorem probe_no_order_six_quotient
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hquot : Nonempty ((c.Hhat ⧸ (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) ≃* DihedralGroup 3))
    {s x : G} (hsH : s ∈ c.Hhat) (hxH : x ∈ c.Hhat)
    (hsB : s ∉ twoCoreOf c.Hhat ⊔ c.U)
    (hxB : x ∉ twoCoreOf c.Hhat ⊔ c.U)
    (hs2 : s ^ 2 = 1) (hx3 : x ^ 3 = 1)
    (hcomm : s * x = x * s) : False := by
  classical
  let H : Subgroup G := c.Hhat
  let N0 : Subgroup H := pCore 2 H ⊔ pPrimeCore 2 H
  have hN0normal : N0.Normal := by
    dsimp [N0, H]
    infer_instance
  let q : H →* (H ⧸ N0) := QuotientGroup.mk' N0
  obtain ⟨e⟩ := hquot
  have hmapN : (N0.map H.subtype) = twoCoreOf c.Hhat ⊔ c.U := by
    have hUeq : c.U = oddCoreOf c.Hhat := (theorem_2_6 hmin c).1
    dsimp [N0, H]
    rw [Subgroup.map_sup]
    simp [twoCoreOf, oddCoreOf, hUeq]
  let sH0 : H := ⟨s, hsH⟩
  let xH0 : H := ⟨x, hxH⟩
  let qs := q sH0
  let qx := q xH0
  have hqsne : qs ≠ 1 := by
    intro h
    have hm : sH0 ∈ N0 := (QuotientGroup.eq_one_iff sH0).mp h
    have hmG : s ∈ N0.map H.subtype := Subgroup.mem_map.mpr ⟨sH0, hm, rfl⟩
    exact hsB (by simpa [hmapN] using hmG)
  have hqxne : qx ≠ 1 := by
    intro h
    have hm : xH0 ∈ N0 := (QuotientGroup.eq_one_iff xH0).mp h
    have hmG : x ∈ N0.map H.subtype := Subgroup.mem_map.mpr ⟨xH0, hm, rfl⟩
    exact hxB (by simpa [hmapN] using hmG)
  have hqs2 : qs ^ 2 = 1 := by
    have hsH02 : sH0 ^ 2 = 1 := by
      apply Subtype.ext
      simpa [hs2]
    dsimp [qs]
    rw [← map_pow, hsH02, map_one]
  have hqx3 : qx ^ 3 = 1 := by
    have hxH03 : xH0 ^ 3 = 1 := by
      apply Subtype.ext
      simpa [hx3]
    dsimp [qx]
    rw [← map_pow, hxH03, map_one]
  have hqcomm : qs * qx = qx * qs := by
    have hsub : sH0 * xH0 = xH0 * sH0 := by
      apply Subtype.ext
      exact hcomm
    dsimp [qs, qx]
    exact congrArg q hsub
  have hqcomm' : Commute qs qx := (commute_iff_eq _ _).2 hqcomm
  let z := qs * qx
  have hz6 : z ^ 6 = 1 := by
    dsimp [z]
    rw [hqcomm'.mul_pow]
    calc
      qs ^ 6 * qx ^ 6 = (qs ^ 2) ^ 3 * (qx ^ 3) ^ 2 := by
        rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hqs2, hqx3]; simp
  have hz2ne : z ^ 2 ≠ 1 := by
    intro hz2
    have hqx2 : qx ^ 2 = 1 := by
      calc
        qx ^ 2 = 1 * qx ^ 2 := by simp
        _ = qs ^ 2 * qx ^ 2 := by rw [hqs2]
        _ = (qs * qx) ^ 2 := (hqcomm'.mul_pow 2).symm
        _ = 1 := hz2
    apply hqxne
    calc
      qx = qx ^ 3 * (qx ^ 2)⁻¹ := by group
      _ = 1 := by rw [hqx3, hqx2]; simp
  have hzord : orderOf z ∣ 6 := orderOf_dvd_of_pow_eq_one hz6
  have hzle : orderOf z ≤ 6 := Nat.le_of_dvd (by norm_num) hzord
  have hzorder6 : orderOf z = 6 := by
    have hz1ne : z ≠ 1 := by
      intro hz1
      apply hz2ne
      rw [hz1]
      simp
    have hne1 : orderOf z ≠ 1 := by
      intro h
      exact hz1ne (orderOf_eq_one_iff.mp h)
    have hne2 : orderOf z ≠ 2 := by
      intro h
      apply hz2ne
      rw [← h]
      exact pow_orderOf_eq_one z
    have hz3ne : z ^ 3 ≠ 1 := by
      intro hz3
      have hqs3 : qs ^ 3 = 1 := by
        calc
          qs ^ 3 = qs ^ 3 * 1 := by simp
          _ = qs ^ 3 * qx ^ 3 := by rw [hqx3]
          _ = (qs * qx) ^ 3 := (hqcomm'.mul_pow 3).symm
          _ = 1 := hz3
      apply hqsne
      calc
        qs = qs ^ 3 * (qs ^ 2)⁻¹ := by group
        _ = 1 := by rw [hqs3, hqs2]; simp
    have hne3 : orderOf z ≠ 3 := by
      intro h
      apply hz3ne
      rw [← h]
      exact pow_orderOf_eq_one z
    interval_cases h : orderOf z <;> simp_all
  exact probe_dihedral_three_no_order_six (e z) (by
    rw [MulEquiv.orderOf_eq]
    exact hzorder6)

private theorem probe_X_inf_B_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    {X : Subgroup G} (hXle : X ≤ c.Hhat)
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) :
    X ⊓ (twoCoreOf c.Hhat ⊔ c.U) = ⊥ := by
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  have hBcard : Nat.card {z : G // z ∈ invertedElements B y} = 1 := by
    simpa [B] using firstCase_klein_restrictionFive hmin c hfirst hklein y hy hyH
  apply le_bot_iff.mp
  intro z hz
  have hI : z ∈ invertedElements B y := ⟨hz.2, (hXinv z hz.1).2⟩
  have hone : (1 : G) ∈ invertedElements B y := ⟨B.one_mem, by simp⟩
  obtain ⟨z0, hz0⟩ := Nat.card_eq_one_iff_exists.mp hBcard
  have hzEq : (⟨z, hI⟩ : {w : G // w ∈ invertedElements B y}) = z0 := hz0 _
  have h1Eq : (⟨1, hone⟩ : {w : G // w ∈ invertedElements B y}) = z0 := hz0 _
  have hz1 : z = 1 := congrArg Subtype.val (hzEq.trans h1Eq.symm)
  exact Subgroup.mem_bot.mpr hz1

public theorem firstCase_klein_restrictionSeven_core
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {n : ℕ} {y : G} {X : Subgroup G}
    (hyJ : y ∈ firstCaseJ c n)
    (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN_even : Even (Nat.card
      (Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) :
    Nat.card X = 3 ∧ c.FU ≤ Subgroup.centralizer (X : Set G) := by
  classical
  have hyJ' : IsInvolution y ∧ y ∉ c.Hhat ∧
      firstCaseCosetInvolutions c y = n := by
    simpa [firstCaseJ] using hyJ
  have hXcard : Nat.card X = 3 :=
    probe_X_card_three hmin c hfirst hklein hyJ'.1 hyJ'.2.1
      hXne hXle hXodd hXinv
  have hXinf := probe_X_inf_B_bot hmin c hfirst hklein hyJ'.1 hyJ'.2.1 hXle hXinv
  let V : Subgroup G := twoCoreOf c.Hhat
  let B : Subgroup G := V ⊔ c.U
  have hVcent : V ≤ Subgroup.centralizer (c.U : Set G) := by
    have h26 := theorem_2_6 hmin c
    simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hVleS : V ≤ (c.S : Subgroup G) := by
    dsimp [V]
    rw [← (theorem_2_6 hmin c).2.1]
    exact inf_le_left
  have hVne : V ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card V = 1 := by rw [hbot]; simp
    have hVK := firstCase_klein_V_klein c hklein
    have hfour : Nat.card V = 4 := hVK.card_four
    rw [hcard] at hfour
    norm_num at hfour
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
  have htV : c.t ∈ V := centralizerStructure_t_mem_twoCore c (theorem_2_6 hmin c)
  have htC : c.t ∈ (c.S : Subgroup G) ⊓
      Subgroup.centralizer (c.U : Set G) :=
    ⟨hVleS htV, hVcent htV⟩
  have hVcentralizer_false : ∀ {s0 : G}, s0 ∈ V → IsInvolution s0 →
      (∀ x : G, x ∈ X → s0 * x * s0⁻¹ = x) → False := by
    intro s0 hs0V hs0I hs0Cent
    have hs0C : s0 ∈ (c.S : Subgroup G) ⊓
        Subgroup.centralizer (c.U : Set G) := ⟨hVleS hs0V, hVcent hs0V⟩
    obtain ⟨a, haH, has⟩ := theorem26_involutions_in_C_conjugate
      hmin c hNormU hs0I c.t_involution hs0C htC
    let Xa : Subgroup G := conjugateSubgroup X a
    have hXaH : Xa ≤ c.H := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hzx⟩
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have hcx : s0 * x = x * s0 := by
        have h := hs0Cent x hx
        exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using h)
      have hzx' : z = a * x * a⁻¹ := by simpa [conjugateSubgroup] using hzx.symm
      rw [hzx', ← has]
      change (a * x * a⁻¹) * (a * s0 * a⁻¹) =
        (a * s0 * a⁻¹) * (a * x * a⁻¹)
      calc
        (a * x * a⁻¹) * (a * s0 * a⁻¹) = a * (x * s0) * a⁻¹ := by group
        _ = a * (s0 * x) * a⁻¹ := by rw [hcx]
        _ = (a * s0 * a⁻¹) * (a * x * a⁻¹) := by group
    have hXacard : Nat.card Xa = Nat.card X := by
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective X (MulAut.conj a).toMonoidHom
          (MulAut.conj a).injective).toEquiv.symm
    have hXaU : Xa ≤ c.U := odd_order_subgroup_le_U_of_H_eq_SU hmin c hXaH (by
      rw [hXacard]
      exact hXodd)
    have hUnorm : IsNormalIn c.U c.Hhat := by
      have h26 := theorem_2_6 hmin c
      rw [h26.1]
      refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat), ?_⟩
      intro h hh x hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨h, hh⟩ : c.Hhat) * z * (⟨h, hh⟩ : c.Hhat)⁻¹, ?_, by simp⟩
      exact (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem
        z hz (⟨h, hh⟩ : c.Hhat)
    have hXleU : X ≤ c.U := by
      intro x hx
      have hxa : a * x * a⁻¹ ∈ c.U := hXaU
        (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      have hback := hUnorm.2 a⁻¹ (c.Hhat.inv_mem haH) (a * x * a⁻¹) hxa
      simpa [mul_assoc] using hback
    apply hXne
    apply le_antisymm
    · intro x hx
      have hmem : x ∈ X ⊓ B :=
        ⟨hx, (show c.U ≤ B from le_sup_right) (hXleU hx)⟩
      rw [hXinf] at hmem
      exact hmem
    · exact bot_le
  let Nhat : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ c.Hhat
  have h2dvd : 2 ∣ Nat.card Nhat := by
    change 2 ∣ Nat.card (Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G)
    exact even_iff_two_dvd.mp hN_even
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨sN, hsNorder⟩ := exists_prime_orderOf_dvd_card' (G := Nhat) 2 h2dvd
  let s : G := sN
  have hsord : orderOf s = 2 := by
    simpa [s] using (Subgroup.orderOf_coe sN).trans hsNorder
  have hsI : IsInvolution s := ⟨by
    intro hs1
    have : orderOf s = 1 := by simpa [hs1]
    rw [hsord] at this
    omega, by rw [← hsord]; exact pow_orderOf_eq_one s⟩
  have hsNorm : s ∈ Subgroup.normalizer (X : Set G) := sN.2.1
  have hsH : s ∈ c.Hhat := sN.2.2
  let sNorm : Subgroup.normalizer (X : Set G) := ⟨s, hsNorm⟩
  let alpha : MulAut X := X.normalizerMonoidHom sNorm
  rcases mulAut_eq_one_or_apply_eq_inv_of_card_eq_three hXcard alpha with
    halpha | halpha
  · have hsCentX : ∀ x : G, x ∈ X → s * x * s⁻¹ = x := by
      intro x hx
      let xX : X := ⟨x, hx⟩
      have hfix : alpha xX = xX := by simpa [halpha]
      simpa [alpha, sNorm, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hfix
    by_cases hsB : s ∈ B
    · exact False.elim (hVcentralizer_false
        (probe_B_involution_mem_V hmin c hklein hsB hsI) hsI hsCentX)
    · let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨xX, hxXorder⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hXcard])
      let x : G := xX
      have hxH : x ∈ c.Hhat := hXle xX.2
      have hxB : x ∉ B := by
        intro hxB
        have hxbot : x ∈ X ⊓ B := ⟨xX.2, hxB⟩
        rw [hXinf] at hxbot
        have hxone : x = 1 := Subgroup.mem_bot.mp hxbot
        have hxne : x ≠ 1 := by
          intro hxone'
          have h1 : orderOf x = 1 := by simpa [hxone']
          have h3 : orderOf x = 3 := by
            simpa [x] using (Subgroup.orderOf_coe xX).trans hxXorder
          omega
        exact hxne hxone
      have hx3 : x ^ 3 = 1 := by
        have hxorderG : orderOf x = 3 := by
          simpa [x] using (Subgroup.orderOf_coe xX).trans hxXorder
        rw [← hxorderG]
        exact pow_orderOf_eq_one x
      exact False.elim (probe_no_order_six_quotient hmin c
        (firstCase_klein_quotient_d6 hmin c hfirst hklein)
        hsH hxH hsB hxB hsI.2 hx3 (by
          have h := hsCentX x xX.2
          exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using h)))
  · have hsV : s ∉ V := by
      intro hsV
      have hBnorm : IsNormalIn B c.Hhat := firstCase_klein_VU_normal_in_Hhat hmin c
      have hsCentX : ∀ x : G, x ∈ X → s * x * s⁻¹ = x := by
        intro x hx
        have hxconj : s * x * s⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp hsNorm x).mp hx
        have hcommB : s * x * s⁻¹ * x⁻¹ ∈ B := by
          have hsB : s ∈ B := (show V ≤ B from le_sup_left) hsV
          have hsinvB : s⁻¹ ∈ B := B.inv_mem hsB
          have hconjB := hBnorm.2 x (hXle hx) s⁻¹ hsinvB
          exact by simpa [mul_assoc] using B.mul_mem hsB hconjB
        have hcommX : s * x * s⁻¹ * x⁻¹ ∈ X := X.mul_mem hxconj (X.inv_mem hx)
        have hbot : s * x * s⁻¹ * x⁻¹ ∈ X ⊓ B := ⟨hcommX, hcommB⟩
        rw [hXinf] at hbot
        exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)
      exact hVcentralizer_false hsV hsI hsCentX
    have hsInv : ∀ x : G, x ∈ X → s * x * s⁻¹ = x⁻¹ := by
      intro x hx
      let xX : X := ⟨x, hx⟩
      simpa [alpha, sNorm, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val (halpha xX)
    exact ⟨hXcard, probe_FU_centralizes_X_of_inverted hmin c hfirst hklein
      hXcard hXle hsH hsI hsV hsNorm hsInv⟩

end CFSG.GorensteinWalter

