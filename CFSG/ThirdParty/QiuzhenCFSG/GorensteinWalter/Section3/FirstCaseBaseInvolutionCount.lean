module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseOrderInfra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionCountInSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public meta import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! The first source identity, counting involutions in `H` and `Ĥ`. -/

private theorem firstCase_H_product_equiv_base
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    Nonempty (c.S × c.U ≃ c.H) := by
  classical
  have hSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU hmin c
  have hUnorm : IsNormalIn c.U c.H := by
    change IsNormalIn (oddCoreOf c.H) c.H
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.2
    · intro h hh x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨h, hh⟩ : c.H) * y * (⟨h, hh⟩ : c.H)⁻¹, ?_, by simp⟩
      exact (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        y hy (⟨h, hh⟩ : c.H)
  have hSleH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
  have hSnormU : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    hSleH.trans (le_normalizer_of_isNormalIn hUnorm)
  have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
    rw [show Nat.card (oddCoreOf c.H) = Nat.card (pPrimeCore 2 c.H) by
      simpa [oddCoreOf] using
        (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.H)
          c.H.subtype_injective)]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hScop : Nat.Coprime (Nat.card (c.S : Subgroup G)) (Nat.card c.U) := by
    have hSpow : ∃ n : ℕ, Nat.card (c.S : Subgroup G) = 2 ^ n := by
      have hcard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
        obtain ⟨e⟩ := c.dihedralEquiv
        simpa using (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
      refine ⟨c.m + 1, ?_⟩
      calc
        Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := hcard
        _ = 2 ^ (c.m + 1) := by rw [pow_succ]; ring
    obtain ⟨n, hn⟩ := hSpow
    rw [hn]
    exact hUcop.pow_left _
  have hdisj : Disjoint (c.S : Subgroup G) c.U :=
    Subgroup.disjoint_of_coprime_natCard hScop
  have hset : (c.H : Set G) = (c.S : Set G) * (c.U : Set G) := by
    rw [← hSU, Subgroup.coe_mul_of_left_le_normalizer_right c.S c.U hSnormU]
    rfl
  let f : c.S × c.U → c.H := fun z =>
    ⟨(z.1 : G) * (z.2 : G), by
      rw [← hSU]
      exact Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hxy
  have hf_surj : Function.Surjective f := by
    intro z
    have hz : (z : G) ∈ (c.S : Set G) * (c.U : Set G) := by
      rw [← hset]
      exact z.2
    rcases Set.mem_mul.mp hz with ⟨s, hs, u, hu, hsu⟩
    exact ⟨⟨⟨s, hs⟩, ⟨u, hu⟩⟩, Subtype.ext hsu⟩
  exact ⟨Equiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩

public theorem firstCase_product_involution_component
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    {s u : G} (hs : s ∈ c.S) (hu : u ∈ c.U)
    (hx : IsInvolution (s * u)) :
    IsInvolution s := by
  classical
  have hSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU hmin c
  have hUnorm : IsNormalIn c.U c.H := by
    change IsNormalIn (oddCoreOf c.H) c.H
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.2
    · intro h hh x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨h, hh⟩ : c.H) * y * (⟨h, hh⟩ : c.H)⁻¹, ?_, by simp⟩
      exact (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        y hy (⟨h, hh⟩ : c.H)
  have hSleH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
  have hdisj : Disjoint (c.S : Subgroup G) c.U := by
    have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
      change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
      rw [show Nat.card (oddCoreOf c.H) = Nat.card (pPrimeCore 2 c.H) by
        simpa [oddCoreOf] using
          (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.H)
            c.H.subtype_injective)]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    have hSpow : ∃ n : ℕ, Nat.card (c.S : Subgroup G) = 2 ^ n := by
      have hcard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
        obtain ⟨e⟩ := c.dihedralEquiv
        simpa using (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
      refine ⟨c.m + 1, ?_⟩
      calc
        Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := hcard
        _ = 2 ^ (c.m + 1) := by rw [pow_succ]; ring
    obtain ⟨n, hn⟩ := hSpow
    exact Subgroup.disjoint_of_coprime_natCard (by rw [hn]; exact hUcop.pow_left _)
  let U' : Subgroup (↥c.H) := c.U.subgroupOf c.H
  let : U'.Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hUnorm.1).2
      (le_normalizer_of_isNormalIn hUnorm)
  let q : ↥c.H →* (↥c.H ⧸ U') := QuotientGroup.mk' U'
  let sH : ↥c.H := ⟨s, hSleH hs⟩
  let uH : ↥c.H := ⟨u, hUnorm.1 hu⟩
  have hsq : q (sH ^ 2) = 1 := by
    have hxu : sH * uH = ⟨s * u, by
        exact c.H.mul_mem (hSleH hs) (hUnorm.1 hu)⟩ := by
      apply Subtype.ext
      rfl
    have hxH : IsInvolution (sH * uH) := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hx.1
        exact congrArg Subtype.val h
      · simpa [hxu] using hx.2
    have hqu : q uH = 1 := by
      apply (QuotientGroup.eq_one_iff (N := U') (x := uH)).2
      exact Subgroup.mem_subgroupOf.mpr hu
    have hqxu : q (sH * uH) ^ 2 = 1 := by
      have h := congrArg q hxH.2
      simpa [map_pow] using h
    calc
      q (sH ^ 2) = q sH ^ 2 := by rw [map_pow]
      _ = q (sH * uH) ^ 2 := by simp [map_mul, hqu]
      _ = 1 := hqxu
  have hsU : s ^ 2 ∈ c.U := by
    have hsHsq : sH ^ 2 ∈ U' :=
      (QuotientGroup.eq_one_iff (N := U') (x := sH ^ 2)).mp hsq
    exact Subgroup.mem_subgroupOf.mp hsHsq
  have hsSsq : s ^ 2 ∈ (c.S : Subgroup G) := by
    simpa [pow_two] using c.S.mul_mem hs hs
  have hsSqBot : s ^ 2 = 1 := by
    have hmem : s ^ 2 ∈ (c.S : Subgroup G) ⊓ c.U := ⟨hsSsq, hsU⟩
    have hmem' : s ^ 2 ∈ (⊥ : Subgroup G) := hdisj.le_bot hmem
    exact Subgroup.mem_bot.mp hmem'
  have hsne : s ≠ 1 := by
    intro hs1
    have huI : IsInvolution u := by simpa [hs1] using hx
    have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
      change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
      rw [show Nat.card (oddCoreOf c.H) = Nat.card (pPrimeCore 2 c.H) by
        simpa [oddCoreOf] using
          (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.H)
            c.H.subtype_injective)]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    have huord : orderOf u ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using huI.2)
    have huordU : orderOf u ∣ Nat.card c.U :=
      Subgroup.orderOf_dvd_natCard c.U hu
    have hcop : Nat.Coprime 2 (orderOf u) :=
      Nat.Coprime.of_dvd_right huordU hUcop
    have huord1 : orderOf u = 1 := hcop.symm.eq_one_of_dvd huord
    exact huI.1 (orderOf_eq_one_iff.mp huord1)
  exact ⟨hsne, hsSqBot⟩

private theorem firstCase_S_involutions_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hS8 : Nat.card (c.S : Subgroup G) = 8) :
    Nat.card {x : G // IsInvolution x ∧ x ∈ (c.S : Subgroup G)} = 5 := by
  let eS : c.S ≃* DihedralGroup 4 := by
    let e := Classical.choice c.dihedralEquiv
    have hm2 : c.m = 2 := by
      have h := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
      have hcard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
        simpa using h
      rw [hS8] at hcard
      have hmPow : 2 ^ c.m = 4 := by omega
      apply (Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2))
      simpa using hmPow
    rw [hm2] at e
    exact e
  let eI : {x : c.S // IsInvolution x} ≃
      {x : DihedralGroup 4 // IsInvolution x} :=
    Equiv.subtypeEquiv eS.toEquiv (by
      intro x
      constructor
      · intro hx
        constructor
        · intro h
          apply hx.1
          simpa using h
        · simpa [map_pow] using congrArg (fun z : c.S => eS z) hx.2
      · intro hx
        constructor
        · intro h
          exact hx.1 (by simpa [h])
        · apply eS.injective
          simpa [map_pow] using hx.2)
  have hD : Nat.card {x : DihedralGroup 4 // IsInvolution x} = 5 := by
    let : DecidablePred (fun x : DihedralGroup 4 => IsInvolution x) := fun x =>
      inferInstanceAs (Decidable (x ≠ 1 ∧ x ^ 2 = 1))
    let : Fintype {x : DihedralGroup 4 // IsInvolution x} :=
      Fintype.subtype
        ((Finset.univ : Finset (DihedralGroup 4)).filter
          (fun x => IsInvolution x)) (by intro x; simp)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  have hsub : Nat.card {x : G // IsInvolution x ∧ x ∈ (c.S : Subgroup G)} =
      Nat.card {x : c.S // IsInvolution x} := by
    let e : {x : G // IsInvolution x ∧ x ∈ (c.S : Subgroup G)} ≃
        {x : c.S // IsInvolution x} :=
      { toFun := fun x =>
          ⟨⟨x.1, x.2.2⟩, by
            constructor
            · intro h
              exact x.2.1.1 (congrArg Subtype.val h)
            · apply Subtype.ext
              simpa using x.2.1.2⟩
        invFun := fun x =>
          ⟨x.1, by
            constructor
            · constructor
              · intro h
                apply x.2.1
                apply Subtype.ext
                exact h
              · simpa using congrArg Subtype.val x.2.2
            · exact x.1.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact Nat.card_congr e
  rw [hsub, Nat.card_congr eI, hD]

private theorem firstCase_V_nontrivial_involutions_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nat.card {x : G // IsInvolution x ∧ x ∈ twoCoreOf c.Hhat} = 3 := by
  let V : Subgroup G := twoCoreOf c.Hhat
  have hVK : IsKleinFour V := firstCase_klein_V_klein c hklein
  let A : Type u := {x : V // x ≠ 1}
  let B : Type u := {x : G // IsInvolution x ∧ x ∈ V}
  have hAB : Nat.card A = Nat.card B := by
    let e : A ≃ B :=
      { toFun := fun x =>
          ⟨x.1, by
            change ((x.1 : G) ≠ 1 ∧ (x.1 : G) ^ 2 = 1) ∧
              (x.1 : G) ∈ V
            refine ⟨?_, x.1.2⟩
            refine ⟨?_, ?_⟩
            · intro h
              exact x.2 (Subtype.ext h)
            · have hsq := hVK.mul_self x.1
              simpa [pow_two] using congrArg Subtype.val hsq⟩
        invFun := fun x =>
          ⟨⟨x.1, x.2.2⟩, by
            intro h
            exact x.2.1.1 (congrArg Subtype.val h)⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact Nat.card_congr e
  have hA : Nat.card A = Nat.card V - 1 := by
    let : Fintype V := Fintype.ofFinite _
    let : Fintype A := Fintype.ofFinite _
    let : Fintype {x : V // x = 1} := Fintype.ofFinite _
    have h1 : Fintype.card {x : V // x = 1} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, rfl⟩, ?_⟩
      intro x
      apply Subtype.ext
      simpa using x.2
    have hsplit := Fintype.card_subtype_compl (α := V) (p := fun x : V => x = 1)
    rw [h1] at hsplit
    rw [Nat.card_eq_fintype_card (α := A), Nat.card_eq_fintype_card (α := V)]
    simpa [A] using hsplit.symm
  have hVcard : Nat.card V = 4 := hVK.card_four
  calc
    Nat.card {x : G // IsInvolution x ∧ x ∈ twoCoreOf c.Hhat} = Nat.card B := by rfl
    _ = Nat.card A := hAB.symm
    _ = Nat.card V - 1 := hA
    _ = 3 := by norm_num [hVcard]

public theorem firstCase_klein_V_involution_count
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nat.card {x : G // IsInvolution x ∧ x ∈ twoCoreOf c.Hhat} = 3 := by
  exact firstCase_V_nontrivial_involutions_card c hklein

public theorem firstCase_odd_subgroup_involution_eq_one
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hUcop : Nat.Coprime 2 (Nat.card c.U))
    {u : G} (hu : u ∈ c.U) (huI : IsInvolution u) :
    u = 1 := by
  have huord : orderOf u ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using huI.2)
  have huordU : orderOf u ∣ Nat.card c.U :=
    Subgroup.orderOf_dvd_natCard c.U hu
  have hcop : Nat.Coprime 2 (orderOf u) :=
    Nat.Coprime.of_dvd_right huordU hUcop
  have huord1 : orderOf u = 1 := hcop.symm.eq_one_of_dvd huord
  exact orderOf_eq_one_iff.mp huord1

private theorem firstCase_isInvolution_coe_subtype
    {G : Type u} [Group G] {M : Subgroup G} {x : M}
    (hx : IsInvolution x) : IsInvolution (x : G) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact hx.1 (Subtype.ext h)
  · simpa using congrArg Subtype.val hx.2

private theorem firstCase_S_U_disjoint
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    Disjoint (c.S : Subgroup G) c.U := by
  have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
    rw [show Nat.card (oddCoreOf c.H) = Nat.card (pPrimeCore 2 c.H) by
      simpa [oddCoreOf] using
        (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.H)
          c.H.subtype_injective)]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hSpow : ∃ n : ℕ, Nat.card (c.S : Subgroup G) = 2 ^ n := by
    have hcard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
      let e := Classical.choice c.dihedralEquiv
      simpa using (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    refine ⟨c.m + 1, ?_⟩
    calc
      Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := hcard
      _ = 2 ^ (c.m + 1) := by rw [pow_succ]; ring
  obtain ⟨n, hn⟩ := hSpow
  exact Subgroup.disjoint_of_coprime_natCard (by rw [hn]; exact hUcop.pow_left _)

public theorem firstCase_klein_H_involution_count
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    ∃ K : Subgroup G, IsHallIn K c.FU ∧ K ≠ ⊥ ∧
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} =
        3 + 2 * Nat.card K := by
  classical
  obtain ⟨_d, K, hKHall, hKne, hKall⟩ :=
    firstCase_klein_data_complete hmin c hfirst hklein
  let V : Subgroup G := twoCoreOf c.Hhat
  have hVleS : V ≤ (c.S : Subgroup G) := by
    dsimp [V]
    rw [← (theorem_2_6 hmin c).2.1]
    exact inf_le_left
  have hSleH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
  have hHleHhat : c.H ≤ c.Hhat := c.H_le_Hhat
  have hUleH : c.U ≤ c.H := by
    change oddCoreOf c.H ≤ c.H
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hFUleU : c.FU ≤ c.U := by
    exact Subgroup.map_subtype_le (fittingSubgroup c.U)
  have hKleU : K ≤ c.U := hKHall.1.trans hFUleU
  have hVcentU : V ≤ Subgroup.centralizer (c.U : Set G) := by
    dsimp [V]
    have h26 := theorem_2_6 hmin c
    simpa [h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
    have h26 := theorem_2_6 hmin c
    rw [h26.1]
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
    rw [show Nat.card (oddCoreOf c.Hhat) = Nat.card (pPrimeCore 2 c.Hhat) by
      simpa [oddCoreOf] using
        (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.Hhat)
          c.Hhat.subtype_injective)]
    exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
  have hS8 := firstCase_klein_S_card hmin c hfirst hklein
  have hSInv : Nat.card {x : G // IsInvolution x ∧ x ∈ (c.S : Subgroup G)} = 5 :=
    firstCase_S_involutions_card c hS8
  have hVInv : Nat.card {x : G // IsInvolution x ∧ x ∈ V} = 3 := by
    simpa [V] using firstCase_V_nontrivial_involutions_card c hklein
  have hSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU hmin c
  have hUnorm : IsNormalIn c.U c.H := by
    change IsNormalIn (oddCoreOf c.H) c.H
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.2
    · intro h hh x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨h, hh⟩ : c.H) * y * (⟨h, hh⟩ : c.H)⁻¹, ?_, by simp⟩
      exact (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        y hy (⟨h, hh⟩ : c.H)
  have hSnormal : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    hSleH.trans (le_normalizer_of_isNormalIn hUnorm)
  have hset : (c.H : Set G) = (c.S : Set G) * (c.U : Set G) := by
    rw [← hSU, Subgroup.coe_mul_of_left_le_normalizer_right c.S c.U hSnormal]
    rfl
  have hdecomp : ∀ {x : G}, x ∈ c.H →
      ∃ s : G, s ∈ c.S ∧ ∃ u : G, u ∈ c.U ∧ s * u = x := by
    intro x hx
    have hxprod : x ∈ (c.S : Set G) * (c.U : Set G) := by
      rw [← hset]
      exact hx
    rcases Set.mem_mul.mp hxprod with ⟨s, hs, u, hu, hsu⟩
    exact ⟨s, hs, u, hu, hsu⟩
  let IV : Type u := {s : c.S // IsInvolution s ∧ (s : G) ∈ V}
  let IR : Type u := {s : c.S // IsInvolution s ∧ (s : G) ∉ V}
  let IK : Type u := K
  let IH : Type u := {x : G // IsInvolution x ∧ x ∈ c.H}
  have hIVcard : Nat.card IV = 3 := by
    let eIV : IV ≃ {x : G // IsInvolution x ∧ x ∈ V} :=
      { toFun := fun s =>
          ⟨(s.1 : G), by
            constructor
            · exact ⟨by
                intro h
                exact s.2.1.1 (Subtype.ext h), by
                simpa using congrArg Subtype.val s.2.1.2⟩
            · exact s.2.2⟩
        invFun := fun x =>
          ⟨⟨x.1, hVleS x.2.2⟩, by
            refine ⟨?_, x.2.2⟩
            have hxS : IsInvolution (⟨x.1, hVleS x.2.2⟩ : c.S) := by
              refine ⟨?_, ?_⟩
              · intro h
                exact x.2.1.1 (congrArg Subtype.val h)
              · apply Subtype.ext
                simpa using x.2.1.2
            exact hxS⟩
        left_inv := by intro s; rfl
        right_inv := by intro x; rfl }
    rw [Nat.card_congr eIV, hVInv]
  have hSInv' : Nat.card {s : c.S // IsInvolution s} = 5 := by
    let eSI : {x : G // IsInvolution x ∧ x ∈ (c.S : Subgroup G)} ≃
        {s : c.S // IsInvolution s} :=
      { toFun := fun x =>
          ⟨⟨x.1, x.2.2⟩, by
            constructor
            · intro h
              exact x.2.1.1 (congrArg Subtype.val h)
            · apply Subtype.ext
              simpa using x.2.1.2⟩
        invFun := fun x =>
          ⟨x.1, by
            constructor
            · constructor
              · intro h
                apply x.2.1
                apply Subtype.ext
                exact h
              · simpa using congrArg Subtype.val x.2.2
            · exact x.1.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    rw [← Nat.card_congr eSI]
    exact hSInv
  have hIRcard : Nat.card IR = 2 := by
    let eSplit : IV ⊕ IR ≃ {s : c.S // IsInvolution s} :=
      { toFun := fun z => match z with
          | Sum.inl s => ⟨s.1, s.2.1⟩
          | Sum.inr s => ⟨s.1, s.2.1⟩
        invFun := fun s =>
          if hs : (s.1 : G) ∈ V then
            Sum.inl ⟨s.1, s.2, hs⟩
          else
            Sum.inr ⟨s.1, s.2, hs⟩
        left_inv := by
          intro z
          cases z with
          | inl s => simp [s.2.2]
          | inr s => simp [s.2.2]
        right_inv := by
          intro s
          by_cases hs : (s.1 : G) ∈ V <;> simp [hs] }
    have hcard := Nat.card_congr eSplit
    rw [Nat.card_sum, hIVcard, hSInv'] at hcard
    omega
  have hoddInv (u : G) (hu : u ∈ c.U) (huI : IsInvolution u) : u = 1 :=
    firstCase_odd_subgroup_involution_eq_one c hUcop hu huI
  have hmap : Sum IV (IR × IK) ≃ IH := by
    let f : Sum IV (IR × IK) → IH := fun z =>
      match z with
      | Sum.inl s =>
          ⟨(s.1 : G) * 1, by
            constructor
            · simpa using firstCase_isInvolution_coe_subtype s.2.1
            · simpa using hSleH s.1.2⟩
      | Sum.inr sk =>
          ⟨(sk.1.1 : G) * (sk.2 : G), by
            constructor
            · have hsI : IsInvolution (sk.1.1 : G) :=
                firstCase_isInvolution_coe_subtype sk.1.2.1
              have hsHhat : (sk.1.1 : G) ∈ c.Hhat :=
                hHleHhat (hSleH sk.1.1.2)
              have hsInv := hKall (sk.1.1 : G) hsHhat hsI sk.1.2.2
              have hku : (sk.2 : G) ∈ invertedElements c.U (sk.1.1 : G) :=
                by rw [← hsInv.1]; exact sk.2.2
              refine ⟨?_, ?_⟩
              · intro hzero
                have hsEq : (sk.1.1 : G) = (sk.2 : G)⁻¹ := by
                  calc
                    (sk.1.1 : G) =
                        ((sk.1.1 : G) * (sk.2 : G)) * (sk.2 : G)⁻¹ := by group
                    _ = (sk.2 : G)⁻¹ := by rw [hzero]; simp
                have hsU : (sk.1.1 : G) ∈ c.U := by
                  rw [hsEq]
                  exact c.U.inv_mem (hKleU sk.2.2)
                have hsBot : (sk.1.1 : G) ∈ (⊥ : Subgroup G) :=
                  (firstCase_S_U_disjoint c).le_bot ⟨sk.1.1.2, hsU⟩
                apply sk.1.2.1.1
                apply Subtype.ext
                exact Subgroup.mem_bot.mp hsBot
              · change ((sk.1.1 : G) * (sk.2 : G)) ^ 2 = 1
                rw [pow_two]
                calc
                  ((sk.1.1 : G) * (sk.2 : G)) *
                      ((sk.1.1 : G) * (sk.2 : G)) =
                      ((sk.1.1 : G) * (sk.2 : G) * (sk.1.1 : G)) *
                        (sk.2 : G) := by group
                  _ = (sk.2 : G)⁻¹ * (sk.2 : G) := by
                    rw [show (sk.1.1 : G) * (sk.2 : G) * (sk.1.1 : G) =
                      (sk.2 : G)⁻¹ by
                        simpa [inv_eq_of_mul_eq_one_right
                          (by simpa [pow_two] using hsI.2)] using hku.2]
                  _ = 1 := inv_mul_cancel _
            · exact c.H.mul_mem (hSleH sk.1.1.2) (hUleH (hKleU sk.2.2))⟩
    refine Equiv.ofBijective f ?_
    constructor
    · intro a b hab
      cases a with
      | inl a =>
          cases b with
          | inl b =>
              apply congrArg Sum.inl
              apply Subtype.ext
              simpa [f] using congrArg Subtype.val hab
          | inr b =>
              let bU : c.U := ⟨(b.2 : G), hKleU b.2.2⟩
              have hprod : (a.1 : G) * (1 : G) =
                  (b.1.1 : G) * (b.2 : G) := by
                simpa [f] using congrArg Subtype.val hab
              have hpair : (a.1, (1 : c.U)) = (b.1.1, bU) := by
                apply Subgroup.mul_injective_of_disjoint
                  (H₁ := (c.S : Subgroup G)) (H₂ := c.U)
                  (firstCase_S_U_disjoint c)
                simpa using hprod
              have hsEq : a.1 = b.1.1 := congrArg Prod.fst hpair
              exact False.elim (b.1.2.2 (by simpa [hsEq] using a.2.2))
      | inr a =>
          cases b with
          | inl b =>
              let aU : c.U := ⟨(a.2 : G), hKleU a.2.2⟩
              have hprod : (a.1.1 : G) * (a.2 : G) =
                  (b.1 : G) * (1 : G) := by
                simpa [f] using congrArg Subtype.val hab
              have hpair : (a.1.1, aU) = (b.1, (1 : c.U)) := by
                apply Subgroup.mul_injective_of_disjoint
                  (H₁ := (c.S : Subgroup G)) (H₂ := c.U)
                  (firstCase_S_U_disjoint c)
                simpa using hprod
              have hsEq : a.1.1 = b.1 := congrArg Prod.fst hpair
              exact False.elim (a.1.2.2 (by simpa [hsEq] using b.2.2))
          | inr b =>
              let aU : c.U := ⟨(a.2 : G), hKleU a.2.2⟩
              let bU : c.U := ⟨(b.2 : G), hKleU b.2.2⟩
              have hprod : (a.1.1 : G) * (a.2 : G) =
                  (b.1.1 : G) * (b.2 : G) := by
                simpa [f] using congrArg Subtype.val hab
              have hpair : (a.1.1, aU) = (b.1.1, bU) := by
                apply Subgroup.mul_injective_of_disjoint
                  (H₁ := (c.S : Subgroup G)) (H₂ := c.U)
                  (firstCase_S_U_disjoint c)
                simpa using hprod
              have ha1 : a.1 = b.1 := by
                apply Subtype.ext
                apply Subtype.ext
                exact congrArg Subtype.val
                  (congrArg (fun p : c.S × c.U => p.1) hpair)
              have ha2 : a.2 = b.2 := by
                have hkval : (a.2 : G) = (b.2 : G) :=
                  congrArg (fun z : c.U => (z : G))
                    (congrArg (fun p : c.S × c.U => p.2) hpair)
                exact Subtype.ext hkval
              exact congrArg Sum.inr (Prod.ext ha1 ha2)
    · intro x
      rcases hdecomp x.2.2 with ⟨s, hs, u, hu, hsu⟩
      have hsI : IsInvolution s :=
        firstCase_product_involution_component hmin c hs hu (by
          simpa [hsu] using x.2.1)
      let sS : c.S := ⟨s, hs⟩
      have hsIS : IsInvolution sS := by
        refine ⟨?_, ?_⟩
        · intro h
          exact hsI.1 (congrArg Subtype.val h)
        · apply Subtype.ext
          simpa using hsI.2
      by_cases hsV : s ∈ V
      · have hcomm : s * u = u * s := by
          exact (Subgroup.mem_centralizer_iff.mp (hVcentU hsV) u hu).symm
        have hsSq : s * s = 1 := by simpa [pow_two] using hsI.2
        have huSq : u ^ 2 = 1 := by
          calc
            u ^ 2 = (s * s) * (u * u) := by
              rw [pow_two, hsSq]
              simp
            _ = s * u * s * u := by
              calc
                s * s * (u * u) = s * (s * u) * u := by group
                _ = s * (u * s) * u := by rw [hcomm]
                _ = s * u * s * u := by group
            _ = 1 := by
              have hxSq : (s * u) ^ 2 = 1 := by
                calc
                  (s * u) ^ 2 = (x : G) ^ 2 := by rw [hsu]
                  _ = 1 := x.2.1.2
              simpa [pow_two, mul_assoc] using hxSq
        have huEq : u = 1 := by
          by_cases hu1 : u = 1
          · exact hu1
          · exact False.elim (hu1 (hoddInv u hu ⟨hu1, huSq⟩))
        refine ⟨Sum.inl ⟨sS, hsIS, hsV⟩, ?_⟩
        apply Subtype.ext
        simpa [f, huEq] using hsu
      · have hsHhat : s ∈ c.Hhat := hHleHhat (hSleH hs)
        have hsInv := hKall s hsHhat hsI hsV
        have hsuInv : s * u * s⁻¹ = u⁻¹ := by
          have hsInv' : s⁻¹ = s := inv_eq_of_mul_eq_one_right
            (by simpa [pow_two] using hsI.2)
          rw [hsInv']
          have hsq : s * u * s * u = 1 := by
            have hxSq : (s * u) ^ 2 = 1 := by
              calc
                (s * u) ^ 2 = (x : G) ^ 2 := by rw [hsu]
                _ = 1 := x.2.1.2
            simpa [pow_two, mul_assoc] using hxSq
          calc
            s * u * s = (s * u * s * u) * u⁻¹ := by group
            _ = u⁻¹ := by rw [hsq]; simp
        have huK : u ∈ K := by
          have huI : u ∈ invertedElements c.U s := ⟨hu, hsuInv⟩
          rw [← hsInv.1] at huI
          exact huI
        refine ⟨Sum.inr ⟨⟨sS, hsIS, hsV⟩, ⟨u, huK⟩⟩, ?_⟩
        apply Subtype.ext
        simpa [f, hsu]
  refine ⟨K, hKHall, hKne, ?_⟩
  have hcard := Nat.card_congr hmap
  rw [Nat.card_sum, Nat.card_prod, hIVcard, hIRcard] at hcard
  simpa [IH, IK] using hcard.symm

end CFSG.GorensteinWalter
