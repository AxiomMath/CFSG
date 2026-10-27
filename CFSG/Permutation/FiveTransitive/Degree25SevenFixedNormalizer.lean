module

public import CFSG.Permutation.FiveTransitive.Degree24Order96Normalizer
public import CFSG.Permutation.FiveTransitive.Degree24FixedSetSeven
public import CFSG.Permutation.FiveTransitive.Degree25ArithmeticTransfer

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem order_seven_mem_five_stabilizer_support_eq_fourteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (u : fixingSubgroup P s)
    (huorder : orderOf u = 7) :
    ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = 14) := by
  classical
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 7 := by
    calc
      orderOf g = orderOf (u : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 7 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsFixed :
      s ⊆ MulAction.fixedBy X (u : P) := by
    intro x hx
    exact
      (mem_fixingSubgroup_iff P).mp u.prop x hx
  have hfixedAtLeast :
      5 ≤ Fintype.card
        (MulAction.fixedBy X (u : P)) := by
    calc
      5 = s.ncard := hs.symm
      _ ≤ (MulAction.fixedBy X (u : P)).ncard :=
        Set.ncard_le_ncard hsFixed
      _ = Fintype.card
          (MulAction.fixedBy X (u : P)) := by
        rw [← Nat.card_coe_set_eq,
          Nat.card_eq_fintype_card]
  have hsupportLe : g.support.card ≤ 20 := by
    have huSupportLe :
        ((((u : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card ≤ 20) := by
      rw [Degree15.card_fixedBy_subgroup_perm,
        hcard] at hfixedAtLeast
      omega
    exact huSupportLe
  have hkCases :
      k + 1 = 1 ∨ k + 1 = 2 := by
    have hkLe : k + 1 ≤ 2 := by
      by_contra hle
      have hthree : 3 ≤ k + 1 := by omega
      have htwentyOne :
          21 ≤ g.support.card := by
        calc
          21 = 3 * 7 := by norm_num
          _ ≤ (k + 1) * 7 :=
            Nat.mul_le_mul_right 7 hthree
          _ = g.support.card := hsum
      omega
    omega
  rcases hkCases with hkOne | hkTwo
  · have hsupport : g.support.card = 7 := by
      omega
    have hgcycle : g.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one, hk,
        Multiset.card_replicate, hkOne]
    exact False.elim
      (hnotAlt
        (Degree25Seven.alternatingGroup_le_of_sevenCycle
          X P hcard h5 (u : P).prop hgcycle hsupport))
  · simpa only [g] using
      (show g.support.card = 14 by omega)

private theorem sylow_seven_card_eq_seven_of_dvd_not_square
    (G : Type) [Group G] [Fintype G]
    (hseven : 7 ∣ Nat.card G)
    (hnotSevenSq : ¬7 ^ 2 ∣ Nat.card G)
    (S : Sylow 7 G) :
    Nat.card S = 7 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := hseven
  have hmPos : m ≠ 0 := by
    intro hmZero
    rw [hmZero, mul_zero] at hm
    exact Nat.card_pos.ne' hm
  have hnotSeven : ¬7 ∣ m := by
    intro hsevenM
    obtain ⟨k, hk⟩ := hsevenM
    apply hnotSevenSq
    refine ⟨k, ?_⟩
    rw [hm, hk]
    norm_num [pow_two]
    ring
  apply Degree24.sylow_card_eq_prime_of_card_eq_prime_mul
    G 7 m hmPos hnotSeven
  exact hm

private theorem alternating_card_dvd_of_seven_dvd_five_point_stabilizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hseven :
      7 ∣ Nat.card (fixingSubgroup P s)) :
    19958400 ∣ Nat.card P ∧
      5 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  have hnotSevenSq :
      ¬7 ^ 2 ∣ Nat.card H := by
    simpa only [H] using
      seven_squared_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  let S : Sylow 7 H := Sylow.nonempty.some
  have hScard : Nat.card S = 7 :=
    sylow_seven_card_eq_seven_of_dvd_not_square
      H (by simpa only [H] using hseven)
        hnotSevenSq S
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hu : orderOf u = 7 :=
    huRaw.trans hScard
  have huNe : u ≠ 1 := by
    intro huOne
    rw [huOne, orderOf_one] at hu
    norm_num at hu
  let SP : Subgroup P :=
    (S : Subgroup H).map H.subtype
  have hSPcard : Nat.card SP = 7 := by
    calc
      Nat.card SP = Nat.card S :=
        Nat.card_congr
          ((S : Subgroup H).equivMapOfInjective
            H.subtype H.subtype_injective).toEquiv.symm
      _ = 7 := hScard
  let uP : P := (u : H)
  let g : Equiv.Perm X := uP
  have huP : orderOf uP = 7 := by
    calc
      orderOf uP = orderOf (u : H) :=
        Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 7 := hu
  have hgSupport : g.support.card = 14 :=
    order_seven_mem_five_stabilizer_support_eq_fourteen
      X P hcard h5 hnotAlt s hs (u : H) (by
        calc
          orderOf (u : H) = orderOf u :=
            Subgroup.orderOf_coe _
          _ = 7 := hu)
  let F : Set X := MulAction.fixedPoints SP X
  have hfixedEq :
      F = Function.fixedPoints g := by
    ext x
    rw [MulAction.mem_fixedPoints,
      Function.mem_fixedPoints_iff]
    constructor
    · intro hx
      change uP • x = x
      exact hx
        ⟨uP,
          Subgroup.mem_map_of_mem H.subtype u.prop⟩
    · intro hx z
      obtain ⟨zH, hzS, hzEq⟩ :=
        Subgroup.mem_map.mp z.prop
      let zS : S := ⟨zH, hzS⟩
      have hzPow : zS ∈ Subgroup.zpowers u :=
        mem_zpowers_of_prime_card hScard huNe
      obtain ⟨j, hj⟩ :=
        Subgroup.mem_zpowers_iff.mp hzPow
      have huStab :
          uP ∈ MulAction.stabilizer P x := by
        rw [MulAction.mem_stabilizer_iff]
        exact hx
      have hzPowers :
          ((zH : H) : P) ∈
            Subgroup.zpowers uP := by
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨j, ?_⟩
        let inclusion : S →* P :=
          H.subtype.comp (S : Subgroup H).subtype
        have hjP := congrArg inclusion hj
        rw [map_zpow] at hjP
        exact hjP
      have hzStab :
          ((zH : H) : P) ∈
            MulAction.stabilizer P x :=
        (Subgroup.zpowers_le.mpr huStab) hzPowers
      change (z : P) • x = x
      rw [← hzEq]
      exact MulAction.mem_stabilizer_iff.mp hzStab
  have hFcard : Fintype.card F = 11 := by
    rw [← Nat.card_eq_fintype_card]
    rw [show F = Function.fixedPoints g from hfixedEq,
      Nat.card_eq_fintype_card,
      Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, hcard, hgSupport]
  let N : Subgroup P :=
    Subgroup.normalizer (SP : Set P)
  letI : SMul N F :=
    Degree24.NormalizerFixedPoints.normalizerSMul X P SP
  letI : MulAction N F :=
    Degree24.NormalizerFixedPoints.normalizerMulAction X P SP
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  have hN5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ c : N, ∀ i, c • a i = b i := by
    intro a b ha hb
    let aX : Fin 5 ↪ X := {
      toFun := fun i => (a i).1
      inj' := fun i j hij =>
        ha (Subtype.ext hij) }
    let bX : Fin 5 ↪ X := {
      toFun := fun i => (b i).1
      inj' := fun i j hij =>
        hb (Subtype.ext hij) }
    obtain ⟨q, hq⟩ :=
      h5 aX bX aX.injective bX.injective
    let t : Set X := Set.range bX
    have ht : t.ncard = 5 := by
      rw [Set.ncard_range_of_injective bX.injective,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    let Ht : Subgroup P := fixingSubgroup P t
    have hHtcard : Nat.card Ht = Nat.card H := by
      exact
        (Degree24.five_point_stabilizers_have_equal_card
          X P h5 s t hs ht).symm
    have hsevenHt : 7 ∣ Nat.card Ht := by
      rw [hHtcard]
      simpa only [H] using hseven
    have hnotSevenSqHt :
        ¬7 ^ 2 ∣ Nat.card Ht := by
      simpa only [Ht] using
        seven_squared_not_dvd_five_point_stabilizer_of_not_alternating
          X P hcard h5 hnotAlt t ht
    have hSPleHt : SP ≤ Ht := by
      intro z hz
      rw [mem_fixingSubgroup_iff]
      rintro _ ⟨i, rfl⟩
      exact
        MulAction.mem_fixedPoints.mp
          (b i).2 ⟨z, hz⟩
    let QSP : Subgroup P :=
      SP.map (MulAut.conj q).toMonoidHom
    have hQSPleHt : QSP ≤ Ht := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ :=
        Subgroup.mem_map.mp hz
      rw [mem_fixingSubgroup_iff]
      rintro _ ⟨i, rfl⟩
      have hwFix :
          (w : P) • (a i).1 = (a i).1 :=
        MulAction.mem_fixedPoints.mp
          (a i).2 ⟨w, hw⟩
      calc
        (MulAut.conj q w : P) • bX i =
            q • ((w : P) • (q⁻¹ • bX i)) := by
          simp only [MulAut.conj_apply, mul_smul]
        _ = q • ((w : P) • aX i) := by
          rw [← hq i, inv_smul_smul]
        _ = q • aX i :=
          congrArg (fun x : X => q • x) hwFix
        _ = bX i := hq i
    have hQSPcard : Nat.card QSP = 7 := by
      calc
        Nat.card QSP = Nat.card SP :=
          Nat.card_congr
            (SP.equivMapOfInjective
              (MulAut.conj q).toMonoidHom
              (MulAut.conj q).injective).toEquiv.symm
        _ = 7 := hSPcard
    let SU : Subgroup Ht := SP.subgroupOf Ht
    let TU : Subgroup Ht := QSP.subgroupOf Ht
    have hSUcard : Nat.card SU = 7 := by
      calc
        Nat.card SU = Nat.card SP :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe
              hSPleHt).toEquiv
        _ = 7 := hSPcard
    have hTUcard : Nat.card TU = 7 := by
      calc
        Nat.card TU = Nat.card QSP :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe
              hQSPleHt).toEquiv
        _ = 7 := hQSPcard
    have hSUisP : IsPGroup 7 SU := by
      apply IsPGroup.of_card (n := 1)
      rw [hSUcard]
      norm_num
    have hTUisP : IsPGroup 7 TU := by
      apply IsPGroup.of_card (n := 1)
      rw [hTUcard]
      norm_num
    obtain ⟨U, hSUleU⟩ :=
      hSUisP.exists_le_sylow
    obtain ⟨T, hTUleT⟩ :=
      hTUisP.exists_le_sylow
    have hUcard : Nat.card U = 7 :=
      sylow_seven_card_eq_seven_of_dvd_not_square
        Ht hsevenHt hnotSevenSqHt U
    have hTcard : Nat.card T = 7 :=
      Nat.card_congr (Sylow.equiv T U).toEquiv |>.trans
        hUcard
    have hSUEq : SU = (U : Subgroup Ht) := by
      apply Subgroup.eq_of_le_of_card_ge hSUleU
      rw [hSUcard, hUcard]
    have hTUEq : TU = (T : Subgroup Ht) := by
      apply Subgroup.eq_of_le_of_card_ge hTUleT
      rw [hTUcard, hTcard]
    obtain ⟨k, hk⟩ :=
      exists_smul_eq Ht T U
    have hkSub :
        TU.map (MulAut.conj k).toMonoidHom = SU := by
      rw [hTUEq, hSUEq]
      exact congrArg Sylow.toSubgroup hk
    let kP : P := k
    have hkQSP :
        QSP.map (MulAut.conj kP).toMonoidHom = SP := by
      apply Subgroup.eq_of_le_of_card_ge
      · intro y hy
        obtain ⟨z, hz, rfl⟩ :=
          Subgroup.mem_map.mp hy
        let zHt : Ht := ⟨z, hQSPleHt hz⟩
        have hzTU : zHt ∈ TU := hz
        have hkzSU :
            MulAut.conj k zHt ∈ SU := by
          rw [← hkSub]
          exact
            Subgroup.mem_map_of_mem
              (MulAut.conj k).toMonoidHom hzTU
        change
          (MulAut.conj kP z : P) ∈ SP
        exact hkzSU
      · calc
          Nat.card SP = Nat.card QSP :=
            hSPcard.trans hQSPcard.symm
          _ = Nat.card
              (QSP.map
                (MulAut.conj kP).toMonoidHom) :=
            Nat.card_congr
              (QSP.equivMapOfInjective
                (MulAut.conj kP).toMonoidHom
                (MulAut.conj kP).injective).toEquiv
          _ ≤ Nat.card
              (QSP.map
                (MulAut.conj kP).toMonoidHom) :=
            le_rfl
    let cP : P := kP * q
    have hcMap :
        SP.map (MulAut.conj cP).toMonoidHom = SP := by
      apply Subgroup.eq_of_le_of_card_ge
      · intro y hy
        obtain ⟨z, hz, rfl⟩ :=
          Subgroup.mem_map.mp hy
        have hqz :
            MulAut.conj q z ∈ QSP :=
          Subgroup.mem_map_of_mem
            (MulAut.conj q).toMonoidHom hz
        have hkqz :
            MulAut.conj kP (MulAut.conj q z) ∈ SP := by
          rw [← hkQSP]
          exact
            Subgroup.mem_map_of_mem
              (MulAut.conj kP).toMonoidHom hqz
        have heq :
            MulAut.conj cP z =
              MulAut.conj kP (MulAut.conj q z) := by
          dsimp only [cP]
          simp only [MulAut.conj_apply]
          group
        change MulAut.conj cP z ∈ SP
        rw [heq]
        exact hkqz
      · calc
          Nat.card SP = Nat.card
              (SP.map
                (MulAut.conj cP).toMonoidHom) :=
            Nat.card_congr
              (SP.equivMapOfInjective
                (MulAut.conj cP).toMonoidHom
                (MulAut.conj cP).injective).toEquiv
          _ ≤ Nat.card
              (SP.map
                (MulAut.conj cP).toMonoidHom) :=
            le_rfl
    have hcNormalizer :
        cP ∈ Subgroup.normalizer SP :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        hcMap
    let cN : N := ⟨cP, hcNormalizer⟩
    refine ⟨cN, ?_⟩
    intro i
    apply Subtype.ext
    change cP • aX i = bX i
    calc
      cP • aX i = kP • (q • aX i) := by
        simp only [cP, mul_smul]
      _ = kP • bX i := by rw [hq i]
      _ = bX i :=
        (mem_fixingSubgroup_iff P).mp
          k.prop (bX i) ⟨i, rfl⟩
  have hNfive :
      MulAction.IsMultiplyPretransitive N F 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      hN5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Subtype.val (hq i)
  let eX : Fin 5 ↪ X :=
    Degree24.fiveEmbeddingOfSet X s hs
  have heXrange : Set.range eX = s :=
    Degree24.range_fiveEmbeddingOfSet X s hs
  have heFixed (i : Fin 5) : eX i ∈ F := by
    rw [MulAction.mem_fixedPoints]
    intro z
    obtain ⟨zH, hzS, hzEq⟩ :=
      Subgroup.mem_map.mp z.prop
    change (z : P) • eX i = eX i
    rw [← hzEq]
    exact
      (mem_fixingSubgroup_iff P).mp zH.prop
        (eX i) (by
          rw [← heXrange]
          exact ⟨i, rfl⟩)
  let eF : Fin 5 ↪ F := {
    toFun := fun i => ⟨eX i, heFixed i⟩
    inj' := fun i j hij =>
      eX.injective
        (congrArg (fun z : F => (z : X)) hij) }
  let sF : Set F := Set.range eF
  have hsF : sF.ncard = 5 := by
    rw [Set.ncard_range_of_injective eF.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let K : Subgroup N := fixingSubgroup N sF
  have hKindexRaw :=
    hNfive.index_of_fixingSubgroup_mul hsF
  rw [Nat.card_eq_fintype_card, hFcard] at hKindexRaw
  norm_num at hKindexRaw
  have hKindex : K.index = 55440 := by
    change (fixingSubgroup N sF).index = 55440
    omega
  have hNcardEq :
      Nat.card N = 55440 * Nat.card K := by
    have hproduct := K.index_mul_card
    rw [hKindex] at hproduct
    exact hproduct.symm
  let baseMap : K →* P :=
    N.subtype.comp K.subtype
  have hbaseMapMemH :
      ∀ q : K, baseMap q ∈ H := by
    intro q
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hxi : x ∈ Set.range eX := by
      simpa only [heXrange] using hx
    obtain ⟨i, rfl⟩ := hxi
    have hqfix :=
      (mem_fixingSubgroup_iff N).mp q.prop
        (eF i) ⟨i, rfl⟩
    exact congrArg Subtype.val hqfix
  let localMap : K →* H :=
    baseMap.codRestrict H hbaseMapMemH
  have hlocalMapInjective :
      Function.Injective localMap := by
    intro a b hab
    apply K.subtype_injective
    apply N.subtype_injective
    exact
      congrArg
        (fun q : H => (q : P)) hab
  have hKdvdH : Nat.card K ∣ Nat.card H :=
    Subgroup.card_dvd_of_injective
      localMap hlocalMapInjective
  let Q : Subgroup (Equiv.Perm F) := ρ.range
  have hQ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : Q, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ := hN5 a b ha hb
    exact ⟨⟨ρ q, ⟨q, rfl⟩⟩, hq⟩
  have hAlt :
      alternatingGroup F ≤
        (MulAction.toPermHom Q F).range :=
    Helpers.alternatingGroup_le_of_five_transitive_of_card_eq_eleven
      Q F hFcard hQ5
  have hAltDvdQ :
      Nat.card (alternatingGroup F) ∣ Nat.card Q :=
    (Subgroup.card_dvd_of_le hAlt).trans
      (Subgroup.card_range_dvd
        (MulAction.toPermHom Q F))
  have hAltDvdN :
      Nat.card (alternatingGroup F) ∣ Nat.card N :=
    hAltDvdQ.trans
      (by
        simpa only [Q] using
          Subgroup.card_range_dvd ρ)
  have hAltDvdP :
      Nat.card (alternatingGroup F) ∣ Nat.card P :=
    hAltDvdN.trans N.card_subgroup_dvd_card
  have hAltCard :
      Nat.card (alternatingGroup F) = 19958400 := by
    letI : Nontrivial F :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    rw [Nat.card_eq_fintype_card,
      card_alternatingGroup, hFcard]
    norm_num
  have hAltDvdNNumeric :
      19958400 ∣ Nat.card N := by
    rwa [hAltCard] at hAltDvdN
  have hAltDvdPNumeric :
      19958400 ∣ Nat.card P := by
    rwa [hAltCard] at hAltDvdP
  refine ⟨hAltDvdPNumeric, ?_⟩
  obtain ⟨m, hm⟩ := hAltDvdNNumeric
  rw [hNcardEq] at hm
  have hKcard : Nat.card K = 360 * m := by
    omega
  have hfiveK : 5 ∣ Nat.card K := by
    rw [hKcard]
    refine ⟨72 * m, ?_⟩
    ring
  exact hfiveK.trans (by
    simpa only [H] using hKdvdH)

private theorem seven_dvd_stabilizer_candidates_reduced
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hseven :
      7 ∣ Nat.card (fixingSubgroup P s)) :
    False := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hcases :
      h = 270 ∨ h = 10206 ∨ h = 2800 ∨ h = 6480 ∨
      h = 12000 ∨ h = 960 ∨ h = 36288 ∨
      h = 1944000 ∨ h = 67200 ∨ h = 288000 ∨
      h = 23040 ∨ h = 870912 ∨ h = 46656000 ∨
      h = 552960 ∨ h = 1024000 ∨ h = 81920 ∨
      h = 3096576 ∨ h = 165888000 := by
    simpa only [H, h] using
      five_point_stabilizer_card_cases_transfer
        X P hcard h5 hnotAlt s hs
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 6375600 := by
    change (fixingSubgroup P s).index = 6375600
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 6375600 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hNormalizerDivisibilities :=
    alternating_card_dvd_of_seven_dvd_five_point_stabilizer
      X P hcard h5 hnotAlt s hs hseven
  have hAltDvdP : 19958400 ∣ Nat.card P :=
    hNormalizerDivisibilities.1
  have hFiveH : 5 ∣ h := by
    simpa only [H, h] using hNormalizerDivisibilities.2
  rw [hPcard] at hAltDvdP
  have hsevenH : 7 ∣ h := by
    simpa only [H, h] using hseven
  rcases hcases with
    hcase | hcase | hcase | hcase | hcase | hcase |
    hcase | hcase | hcase | hcase | hcase | hcase |
    hcase | hcase | hcase | hcase | hcase | hcase
  all_goals try norm_num [hcase] at hsevenH
  all_goals try norm_num [hcase] at hFiveH
  all_goals try norm_num [hcase] at hAltDvdP

theorem seven_not_dvd_five_point_stabilizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬7 ∣ Nat.card (fixingSubgroup P s) := by
  intro hseven
  exact
    seven_dvd_stabilizer_candidates_reduced
      X P hcard h5 hnotAlt s hs hseven

end FiveTransitive.Degree25

end CFSG
