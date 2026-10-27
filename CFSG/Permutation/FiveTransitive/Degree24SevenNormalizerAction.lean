module

public import CFSG.Permutation.FiveTransitive.Degree24SevenSmallNormalizer
public import CFSG.Permutation.FiveTransitive.Degree24FixedSetSeven
public import CFSG.Permutation.FiveTransitive.Degree24StabilizerFixedPoints

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem stabilizer_card_ne_small_seven_normalizer_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hCases :
      Nat.card (fixingSubgroup P s) = 3360 ∨
      Nat.card (fixingSubgroup P s) = 4082400 ∨
      Nat.card (fixingSubgroup P s) = 48384 ∨
      Nat.card (fixingSubgroup P s) = 26127360 ∨
      Nat.card (fixingSubgroup P s) = 1161216) :
    False := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let S : Sylow 7 H := Sylow.nonempty.some
  have hScard : Nat.card S = 7 := by
    rcases hCases with hH | hH | hH | hH | hH
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 480 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 583200 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 6912 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 3732480 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 7 165888 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hu : orderOf u = 7 :=
    huRaw.trans hScard
  have huNe : u ≠ 1 := by
    intro huOne
    rw [huOne, orderOf_one] at hu
    omega
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
      _ = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 7 := hu
  have hg : orderOf g = 7 := by
    calc
      orderOf g = orderOf uP :=
        Subgroup.orderOf_coe _
      _ = 7 := huP
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
        change g x = x at hx
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
      have hzFix :
          ((zH : H) : P) • x = x :=
        MulAction.mem_stabilizer_iff.mp hzStab
      change (z : P) • x = x
      rw [← hzEq]
      exact hzFix
  have hFcard : Fintype.card F = 10 := by
    rw [← Nat.card_eq_fintype_card]
    rw [show F = Function.fixedPoints g from hfixedEq,
      Nat.card_eq_fintype_card,
      Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, hcard, hgSupport]
  let N : Subgroup P :=
    Subgroup.normalizer (SP : Set P)
  let fixedSmul : SMul N F := {
    smul := fun n x =>
      ⟨(n : P) • x.1, by
        rw [MulAction.mem_fixedPoints]
        intro z
        have hconj :
            (n : P)⁻¹ * (z : P) * (n : P) ∈ SP := by
          exact
            (Subgroup.mem_normalizer_iff''.mp n.prop
              (z : P)).mp z.prop
        let z' : SP :=
          ⟨(n : P)⁻¹ * (z : P) * (n : P), hconj⟩
        have hcommute :
            (z : P) * (n : P) =
              (n : P) * (z' : P) := by
          change
            (z : P) * (n : P) =
              (n : P) *
                ((n : P)⁻¹ * (z : P) * (n : P))
          simp [mul_assoc]
        calc
          (z : P) • ((n : P) • x.1) =
              ((z : P) * (n : P)) • x.1 :=
            (mul_smul (z : P) (n : P) x.1).symm
          _ = ((n : P) * (z' : P)) • x.1 :=
            congrArg (fun q : P => q • x.1) hcommute
          _ = (n : P) • ((z' : P) • x.1) :=
            mul_smul (n : P) (z' : P) x.1
          _ = (n : P) • x.1 :=
            congrArg (fun y : X => (n : P) • y)
              (MulAction.mem_fixedPoints.mp x.2 z')⟩ }
  letI : SMul N F := fixedSmul
  letI : MulAction N F :=
    Subtype.coe_injective.mulAction
      Subtype.val (fun _ _ => rfl)
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
    have htCases :
        Nat.card Ht = 3360 ∨
        Nat.card Ht = 4082400 ∨
        Nat.card Ht = 48384 ∨
        Nat.card Ht = 26127360 ∨
        Nat.card Ht = 1161216 := by
      have heq :=
        five_point_stabilizers_have_equal_card
          X P h5 s t hs ht
      rcases hCases with hH | hH | hH | hH | hH
      · exact Or.inl (by
          rw [← heq]
          simpa only [H] using hH)
      · exact Or.inr (Or.inl (by
          rw [← heq]
          simpa only [H] using hH))
      · exact Or.inr (Or.inr (Or.inl (by
          rw [← heq]
          simpa only [H] using hH)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by
          rw [← heq]
          simpa only [H] using hH))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by
          rw [← heq]
          simpa only [H] using hH))))
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
    have hUcard : Nat.card U = 7 := by
      rcases htCases with hHt | hHt | hHt | hHt | hHt
      · exact
          sylow_card_eq_prime_of_card_eq_prime_mul
            Ht 7 480 (by norm_num) (by norm_num)
              hHt U
      · exact
          sylow_card_eq_prime_of_card_eq_prime_mul
            Ht 7 583200 (by norm_num) (by norm_num)
              hHt U
      · exact
          sylow_card_eq_prime_of_card_eq_prime_mul
            Ht 7 6912 (by norm_num) (by norm_num)
              hHt U
      · exact
          sylow_card_eq_prime_of_card_eq_prime_mul
            Ht 7 3732480 (by norm_num) (by norm_num)
              hHt U
      · exact
          sylow_card_eq_prime_of_card_eq_prime_mul
            Ht 7 165888 (by norm_num) (by norm_num)
              hHt U
    have hTcard : Nat.card T = 7 := by
      exact Nat.card_congr (Sylow.equiv T U).toEquiv |>.trans hUcard
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
    have hkQSP : QSP.map
        (MulAut.conj kP).toMonoidHom = SP := by
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
      _ = bX i := by
        exact
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
    fiveEmbeddingOfSet X s hs
  have heXrange : Set.range eX = s :=
    range_fiveEmbeddingOfSet X s hs
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
  have hKindex : K.index = 30240 := by
    change (fixingSubgroup N sF).index = 30240
    omega
  have hNcardEq : Nat.card N = 30240 * Nat.card K := by
    have hproduct := K.index_mul_card
    rw [hKindex] at hproduct
    exact hproduct.symm
  let NL : Subgroup H :=
    Subgroup.normalizer (S : Set H)
  have hNLcardLe : Nat.card NL ≤ 28 := by
    simpa only [H, S, NL] using
      small_seven_local_normalizer_card_le
        X P hcard h5 hnotAlt s hs hCases S
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
  have hSPcomap :
      SP.comap H.subtype = (S : Subgroup H) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ :=
        Subgroup.mem_map.mp hz
      have hwEq : w = z :=
        H.subtype_injective hwz
      rwa [← hwEq]
    · intro hz
      exact
        Subgroup.mem_map_of_mem H.subtype hz
  have hlocalMapMemNL :
      ∀ q : K, localMap q ∈ NL := by
    intro q
    have hcomap :
        localMap q ∈
          (Subgroup.normalizer SP).comap H.subtype :=
      q.1.prop
    have hnormal :=
      Subgroup.le_normalizer_comap H.subtype hcomap
    change localMap q ∈
      Subgroup.normalizer (SP.comap H.subtype) at hnormal
    rw [hSPcomap] at hnormal
    exact hnormal
  let normalizerMap : K →* NL :=
    localMap.codRestrict NL hlocalMapMemNL
  have hnormalizerMapInjective :
      Function.Injective normalizerMap := by
    intro a b hab
    apply K.subtype_injective
    apply N.subtype_injective
    exact
      congrArg
        (fun q : NL => ((q : H) : P)) hab
  have hKdvdNL : Nat.card K ∣ Nat.card NL :=
    Subgroup.card_dvd_of_injective
      normalizerMap hnormalizerMapInjective
  have hKle : Nat.card K ≤ 28 :=
    (Nat.le_of_dvd Nat.card_pos hKdvdNL).trans
      hNLcardLe
  have hNupper : Nat.card N ≤ 846720 := by
    rw [hNcardEq]
    omega
  let J : Subgroup (Equiv.Perm F) := ρ.range
  have hJ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ := hN5 a b ha hb
    let qJ : J := ⟨ρ q, ⟨q, rfl⟩⟩
    refine ⟨qJ, ?_⟩
    intro i
    exact hq i
  have hAlt :
      alternatingGroup F ≤
        (MulAction.toPermHom J F).range :=
    FiveTransitive.Helpers.alternatingGroup_le_of_five_transitive_of_card_eq_ten
      J F hFcard hJ5
  have hAltDvdRange :
      Nat.card (alternatingGroup F) ∣
        Nat.card (MulAction.toPermHom J F).range :=
    Subgroup.card_dvd_of_le hAlt
  have hAltDvdJ :
      Nat.card (alternatingGroup F) ∣ Nat.card J :=
    hAltDvdRange.trans
      (Subgroup.card_range_dvd
        (MulAction.toPermHom J F))
  have hAltDvdN :
      Nat.card (alternatingGroup F) ∣ Nat.card N :=
    hAltDvdJ.trans
      (by
        simpa only [J] using
          Subgroup.card_range_dvd ρ)
  have hAltCard :
      Nat.card (alternatingGroup F) = 1814400 := by
    letI : Nontrivial F :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    rw [Nat.card_eq_fintype_card,
      card_alternatingGroup, hFcard]
    norm_num
  have hNlower : 1814400 ≤ Nat.card N := by
    rw [← hAltCard]
    exact Nat.le_of_dvd Nat.card_pos hAltDvdN
  omega

end FiveTransitive.Degree24

end CFSG
