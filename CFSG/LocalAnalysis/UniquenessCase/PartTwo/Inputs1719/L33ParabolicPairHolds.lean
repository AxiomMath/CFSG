module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33Parabolic
public import CFSG.GH74.KGroups.L33
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MaxParabolicTransport
public import CFSG.GroupTheory.SylowInfNormal
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.GroupTheory.PermutesPullback
public import Certificates.Certificate5176

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Certificates CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier
open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin
open CFSG.Blueprint (LieModel)
open scoped Pointwise

private theorem center_P_bot :
    Subgroup.center QP.originalSubgroup = ⊥ := by
  have hPSL : Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ := by
    let ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
      (QuotientGroup.quotientMulEquivOfEq center_bot).trans QuotientGroup.quotientBot
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply ePSL.injective
    rw [map_one]
    apply (Subgroup.eq_bot_iff_forall (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)))).mp center_bot (ePSL z)
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := ePSL.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg ePSL (Subgroup.mem_center_iff.mp hz x)
  obtain ⟨parabolicE1⟩ := equiv_psl_P13
  obtain ⟨parabolicE2⟩ := equiv_P13_P
  let eP : QP.originalSubgroup ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3) :=
    parabolicE2.symm.trans parabolicE1.symm
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  apply eP.injective
  rw [map_one]
  apply (Subgroup.eq_bot_iff_forall (Subgroup.center
    (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)))).mp hPSL (eP z)
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := eP.surjective y
  rw [← map_mul, ← map_mul]
  exact congrArg eP (Subgroup.mem_center_iff.mp hz x)

private theorem l33ParabolicIndex_le_two
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    (hKY : KYForm Y K S) (hLie : LieModel ↥K .PSL 3 3 1) :
    K.index ≤ 2 := by
  obtain ⟨hKN, hKq, hZodd, hCent, ⟨a, hKindex⟩, hSylY⟩ := hKY
  obtain ⟨e⟩ := equiv_of_lieModel hLie
  obtain ⟨M, hMP, hMA⟩ := autModel e
  have hZK : Subgroup.center ↥K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply e.injective
    rw [map_one]
    apply (Subgroup.eq_bot_iff_forall (Subgroup.center QP.originalSubgroup)).mp
      center_P_bot (e z)
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subgroup.mem_center_iff.mp hz x)
  let hYN : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKN]
  let conjK : Y →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom K).comp
      ((Subgroup.inclusion hYN).comp Subgroup.topEquiv.symm.toMonoidHom)
  have hconjK_apply : ∀ (y : Y) (x : ↥K),
      ((conjK y x : ↥K) : Y) = y * (x : Y) * y⁻¹ := by
    intro y x
    simp [conjK, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hconjK_inj : Function.Injective conjK := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro y hy
    have hy1 : conjK y = 1 := hy
    have hmem : y ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : conjK y ⟨k, hk⟩ = ⟨k, hk⟩ := by
        rw [hy1]
        rfl
      have h2 : y * k * y⁻¹ = k := by
        simpa [hconjK_apply] using congrArg (fun x : ↥K => (x : Y)) h1
      have h2' : y * k = k * y := by
        calc y * k = (y * k * y⁻¹) * y := by group
          _ = k * y := by rw [h2]
      exact h2'.symm
    rw [hCent] at hmem
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
    rw [hZK, Subgroup.mem_bot] at hz
    have h1 : (1 : Y) = y := by simpa [hz] using hzy
    exact h1.symm
  let ψ : Y →* M.A := M.Φ.toMonoidHom.comp conjK
  have hψ_inj : Function.Injective ψ := by
    intro y z h
    apply hconjK_inj
    apply M.Φ.injective
    exact Subtype.ext (congrArg Subtype.val h)
  have hAcard : Nat.card M.A = 11232 := by
    rw [← M.card_mulAut, card_mulAut e]
  have hYle : Nat.card Y ≤ 11232 := (Nat.card_le_card_of_injective ψ hψ_inj).trans_eq hAcard
  have hKcard : Nat.card ↥K = 5616 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  have hcardmul := Subgroup.card_mul_index (H := K)
  have hle : Nat.card ↥K * K.index ≤ 11232 := by
    rw [hcardmul]
    exact hYle
  rw [hKcard] at hle
  omega

private theorem checker_parts :
    ((((((((closedListCheck parabolicS0List = true ∧
        memGroupListCheck QP parabolicS0List = true) ∧
        e9ListCheck QP parabolicU1a parabolicU1b = true) ∧
        e9ListCheck QP parabolicU2a parabolicU2b = true) ∧
        normalizesListCheck parabolicS0List (pow3list parabolicU1a parabolicU1b) = true) ∧
        normalizesListCheck parabolicS0List (pow3list parabolicU2a parabolicU2b) = true) ∧
        order3PairsCheck parabolicS0List (pow3list parabolicU1a parabolicU1b)
          parabolicPairs1 = true) ∧
        order3PairsCheck parabolicS0List (pow3list parabolicU2a parabolicU2b)
          parabolicPairs2 = true) ∧
        (parabolicQU ()).check = true) ∧
    decide ((parabolicQU ()).orderCertificate = 5616) = true := by
  have h := Certificates.certificate5176
  unfold parabolicPairCheck at h
  repeat rw [Bool.and_eq_true] at h
  exact h

private theorem e9_inv_mem {L : List (Equiv.Perm (Fin 26))}
    (hcube : ∀ x ∈ L, x ^ 3 = 1) (hmul : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L)
    {x : Equiv.Perm (Fin 26)} (hx : x ∈ L) : x⁻¹ ∈ L := by
  have hxx : x * x ∈ L := hmul x hx x hx
  have hx3 : x ^ 3 = 1 := hcube x hx
  have hxinv : x⁻¹ = x * x := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_three] using hx3
  rw [hxinv]
  exact hxx

private theorem mem_flatMap_three_of_mem_mul_zpowers
    {S : List (Equiv.Perm (Fin 26))} {hnd h1 hmul hinv}
    {e x : Equiv.Perm (Fin 26)} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hx : x ∈ ((l33ParabolicListSubgroup S hnd h1 hmul hinv : Subgroup (Equiv.Perm (Fin 26))) :
      Set (Equiv.Perm (Fin 26))) * (Subgroup.zpowers e : Set (Equiv.Perm (Fin 26)))) :
    x ∈ S.flatMap (fun t => [t, t * e, t * e ^ 2]) := by
  obtain ⟨s, hs, z, hz, hsz⟩ := hx
  have hs' : s ∈ S := mem_l33ParabolicListSubgroup.1 hs
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  change z ∈ Subgroup.zpowers e at hz
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hz
  simp only [Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨k, hk, hkz⟩ := hz
  rw [← hsz, ← hkz]
  interval_cases k
  · simpa using (mem_flatMap_mul_three (S := S) (e := e) (x := s)).2
      ⟨s, hs', Or.inl rfl⟩
  · simpa using (mem_flatMap_mul_three (S := S) (e := e) (x := s * e)).2
      ⟨s, hs', Or.inr (Or.inl rfl)⟩
  · simpa using (mem_flatMap_mul_three (S := S) (e := e) (x := s * e ^ 2)).2
      ⟨s, hs', Or.inr (Or.inr rfl)⟩

private theorem l33ParabolicModelFacts :
    ∃ S0 U1 U2 : Subgroup (Equiv.Perm (Fin 26)),
      S0 ≤ QP.originalSubgroup ∧ Nat.card S0 = 16 ∧
      U1 ≤ QP.originalSubgroup ∧ U2 ≤ QP.originalSubgroup ∧
      IsElemAbelian 3 U1 ∧ Nat.card U1 = 9 ∧
      IsElemAbelian 3 U2 ∧ Nat.card U2 = 9 ∧
      S0 ≤ Subgroup.normalizer (U1 : Set (Equiv.Perm (Fin 26))) ∧
      S0 ≤ Subgroup.normalizer (U2 : Set (Equiv.Perm (Fin 26))) ∧
      (∀ E, E ≤ U1 → Permutes E S0 → E = ⊥ ∨ E = U1) ∧
      (∀ E, E ≤ U2 → Permutes E S0 → E = ⊥ ∨ E = U2) ∧
      U1 ⊔ U2 = QP.originalSubgroup := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hclosed, hmemS0⟩, he91⟩, he92⟩, hnorm1⟩, hnorm2⟩, ho1⟩, ho2⟩,
    hQUc⟩, hQUdec⟩ := checker_parts
  have hQUo : (parabolicQU ()).orderCertificate = 5616 := of_decide_eq_true hQUdec
  obtain ⟨hS0len, hS0nd, hS0one, hS0mul, hS0inv⟩ := closedListCheck_sound hclosed
  set S0 : Subgroup (Equiv.Perm (Fin 26)) :=
    l33ParabolicListSubgroup parabolicS0List hS0nd hS0one hS0mul hS0inv with hS0def
  have hS0card : Nat.card S0 = 16 := by
    rw [hS0def, card_l33ParabolicListSubgroup]
    exact hS0len
  have hS0P : S0 ≤ QP.originalSubgroup := by
    intro x hx
    exact memGroupListCheck_sound QP QP_ok hmemS0 x (mem_l33ParabolicListSubgroup.1 hx)
  obtain ⟨hU1nd, hU1len, hU1cube, hU1comm, hU1mul, hU1Pmem⟩ := e9ListCheck_sound QP he91
  have hU1inv : ∀ x ∈ pow3list parabolicU1a parabolicU1b,
      x⁻¹ ∈ pow3list parabolicU1a parabolicU1b :=
    fun x hx => e9_inv_mem hU1cube hU1mul hx
  have hU1one : 1 ∈ pow3list parabolicU1a parabolicU1b := by simp [pow3list]
  set U1 : Subgroup (Equiv.Perm (Fin 26)) :=
    l33ParabolicListSubgroup (pow3list parabolicU1a parabolicU1b) hU1nd hU1one hU1mul
      hU1inv with hU1def
  have hU1card : Nat.card U1 = 9 := by
    rw [hU1def, card_l33ParabolicListSubgroup (h1 := hU1one)]
    exact hU1len
  have hU1P : U1 ≤ QP.originalSubgroup := by
    intro x hx
    exact memGroupListCheck_sound QP QP_ok hU1Pmem x (mem_l33ParabolicListSubgroup.1 hx)
  have hU1el : IsElemAbelian 3 U1 := by
    refine (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 3) (E := U1)).mpr ?_
    refine CFSG.IsElementaryAbelian.of_forall ?_ ?_
    · intro a ha b hb
      have ha' : a ∈ pow3list parabolicU1a parabolicU1b := by simpa [hU1def] using ha
      have hb' : b ∈ pow3list parabolicU1a parabolicU1b := by simpa [hU1def] using hb
      exact hU1comm a ha' b hb'
    · intro x hx
      have hx' : x ∈ pow3list parabolicU1a parabolicU1b := by simpa [hU1def] using hx
      exact hU1cube x hx'
  obtain ⟨hU2nd, hU2len, hU2cube, hU2comm, hU2mul, hU2Pmem⟩ := e9ListCheck_sound QP he92
  have hU2inv : ∀ x ∈ pow3list parabolicU2a parabolicU2b,
      x⁻¹ ∈ pow3list parabolicU2a parabolicU2b :=
    fun x hx => e9_inv_mem hU2cube hU2mul hx
  have hU2one : 1 ∈ pow3list parabolicU2a parabolicU2b := by simp [pow3list]
  set U2 : Subgroup (Equiv.Perm (Fin 26)) :=
    l33ParabolicListSubgroup (pow3list parabolicU2a parabolicU2b) hU2nd hU2one hU2mul
      hU2inv with hU2def
  have hU2card : Nat.card U2 = 9 := by
    rw [hU2def, card_l33ParabolicListSubgroup (h1 := hU2one)]
    exact hU2len
  have hU2P : U2 ≤ QP.originalSubgroup := by
    intro x hx
    exact memGroupListCheck_sound QP QP_ok hU2Pmem x (mem_l33ParabolicListSubgroup.1 hx)
  have hU2el : IsElemAbelian 3 U2 := by
    refine (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 3) (E := U2)).mpr ?_
    refine CFSG.IsElementaryAbelian.of_forall ?_ ?_
    · intro a ha b hb
      have ha' : a ∈ pow3list parabolicU2a parabolicU2b := by simpa [hU2def] using ha
      have hb' : b ∈ pow3list parabolicU2a parabolicU2b := by simpa [hU2def] using hb
      exact hU2comm a ha' b hb'
    · intro x hx
      have hx' : x ∈ pow3list parabolicU2a parabolicU2b := by simpa [hU2def] using hx
      exact hU2cube x hx'
  have : Finite ↥U1 :=
    Finite.of_injective (Subtype.val : ↥U1 → Equiv.Perm (Fin 26)) Subtype.val_injective
  have : Finite ↥U2 :=
    Finite.of_injective (Subtype.val : ↥U2 → Equiv.Perm (Fin 26)) Subtype.val_injective
  have hS0norm1 : S0 ≤ Subgroup.normalizer (U1 : Set (Equiv.Perm (Fin 26))) := by
    intro s hs
    apply mem_normalizer_of_conj_mem (P := U1)
    intro x hx
    have hs' : s ∈ parabolicS0List := by simpa [hS0def] using mem_l33ParabolicListSubgroup.1 hs
    have hx' : x ∈ pow3list parabolicU1a parabolicU1b := by
      simpa [hU1def] using mem_l33ParabolicListSubgroup.1 hx
    exact mem_l33ParabolicListSubgroup.2 (normalizesListCheck_sound hnorm1 s hs' x hx')
  have hS0norm2 : S0 ≤ Subgroup.normalizer (U2 : Set (Equiv.Perm (Fin 26))) := by
    intro s hs
    apply mem_normalizer_of_conj_mem (P := U2)
    intro x hx
    have hs' : s ∈ parabolicS0List := by simpa [hS0def] using mem_l33ParabolicListSubgroup.1 hs
    have hx' : x ∈ pow3list parabolicU2a parabolicU2b := by
      simpa [hU2def] using mem_l33ParabolicListSubgroup.1 hx
    exact mem_l33ParabolicListSubgroup.2 (normalizesListCheck_sound hnorm2 s hs' x hx')
  obtain ⟨hW1len, hW1facts, hW1nodup, hW1len8, hW1cover⟩ := order3PairsCheck_sound ho1
  obtain ⟨hW2len, hW2facts, hW2nodup, hW2len8, hW2cover⟩ := order3PairsCheck_sound ho2
  have hU1rad : ∀ E, E ≤ U1 → Permutes E S0 → E = ⊥ ∨ E = U1 := by
    intro E hEU hperm
    have hdvd : Nat.card E ∣ 9 := by
      have h := Subgroup.card_dvd_of_le hEU
      rwa [hU1card] at h
    have hcases : Nat.card E = 1 ∨ Nat.card E = 3 ∨ Nat.card E = 9 := by
      have h9 : Nat.card E ∣ 3 ^ 2 := by simpa using hdvd
      rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3) (m := 2)).1 h9 with ⟨k, hk, hkE⟩
      interval_cases k
      · exact Or.inl (by simpa using hkE)
      · exact Or.inr (Or.inl (by simpa using hkE))
      · exact Or.inr (Or.inr (by simpa using hkE))
    rcases hcases with hcard | hcard | hcard
    · left; exact Subgroup.eq_bot_of_card_eq (H := E) hcard
    · exfalso
      have hEne : E ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcard
        norm_num at hcard
      obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
      have hxL : x.1 ∈ pow3list parabolicU1a parabolicU1b := by
        have hxU : x.1 ∈ U1 := hEU x.2
        simpa [hU1def] using mem_l33ParabolicListSubgroup.1 hxU
      have hx1 : (x : Equiv.Perm (Fin 26)) ≠ 1 := by
        intro h1
        exact hxne (Subtype.ext h1)
      obtain ⟨e, he_mem, hxe⟩ := by
        simpa only [List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil,
          or_false] using hW1cover x.1 ⟨hxL, hx1⟩
      obtain ⟨p, hpW, hp_e⟩ := he_mem
      rw [← hp_e] at hxe
      obtain ⟨hp1, hp3, hpL, hp2, hpwit⟩ := hW1facts p hpW
      have hordp : orderOf p.1 = 3 := orderOf_eq_prime hp3 hp1
      have hxzp : x.1 ∈ Subgroup.zpowers p.1 := by
        rcases hxe with hxp | hxp
        · rw [hxp]; exact Subgroup.mem_zpowers p.1
        · rw [hxp]; exact Subgroup.npow_mem_zpowers p.1 2
      have hxord : orderOf x.1 = 3 := by
        rcases hxe with hxp | hxp
        · rw [hxp]; exact hordp
        · rw [hxp, orderOf_pow' (x := p.1) (n := 2) (by norm_num), hordp]
          norm_num
      have hEeq : E = Subgroup.zpowers x.1 :=
        (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2)
          (by rw [hcard, Nat.card_zpowers, hxord])).symm
      have hEzp : Subgroup.zpowers x.1 = Subgroup.zpowers p.1 :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxzp)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hordp])
      have hperm' : Permutes (Subgroup.zpowers p.1) S0 := by
        rw [← hEzp, ← hEeq]
        exact hperm
      have hp2S0 : p.2 ∈ S0 := by
        rw [hS0def]
        exact mem_l33ParabolicListSubgroup.2 hp2
      have hmem1 : p.1 * p.2 ∈ (Subgroup.zpowers p.1 : Set (Equiv.Perm (Fin 26))) *
          (S0 : Set (Equiv.Perm (Fin 26))) :=
        ⟨p.1, Subgroup.mem_zpowers p.1, p.2, hp2S0, rfl⟩
      have hmem2 : p.1 * p.2 ∈ (S0 : Set (Equiv.Perm (Fin 26))) *
          (Subgroup.zpowers p.1 : Set (Equiv.Perm (Fin 26))) := by
        rwa [hperm'] at hmem1
      exact hpwit (mem_flatMap_three_of_mem_mul_zpowers hp3 hp1 hmem2)
    · right
      exact Subgroup.eq_of_le_of_card_ge hEU (by rw [hU1card, hcard])
  have hU2rad : ∀ E, E ≤ U2 → Permutes E S0 → E = ⊥ ∨ E = U2 := by
    intro E hEU hperm
    have hdvd : Nat.card E ∣ 9 := by
      have h := Subgroup.card_dvd_of_le hEU
      rwa [hU2card] at h
    have hcases : Nat.card E = 1 ∨ Nat.card E = 3 ∨ Nat.card E = 9 := by
      have h9 : Nat.card E ∣ 3 ^ 2 := by simpa using hdvd
      rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3) (m := 2)).1 h9 with ⟨k, hk, hkE⟩
      interval_cases k
      · exact Or.inl (by simpa using hkE)
      · exact Or.inr (Or.inl (by simpa using hkE))
      · exact Or.inr (Or.inr (by simpa using hkE))
    rcases hcases with hcard | hcard | hcard
    · left; exact Subgroup.eq_bot_of_card_eq (H := E) hcard
    · exfalso
      have hEne : E ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcard
        norm_num at hcard
      obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
      have hxL : x.1 ∈ pow3list parabolicU2a parabolicU2b := by
        have hxU : x.1 ∈ U2 := hEU x.2
        simpa [hU2def] using mem_l33ParabolicListSubgroup.1 hxU
      have hx1 : (x : Equiv.Perm (Fin 26)) ≠ 1 := by
        intro h1
        exact hxne (Subtype.ext h1)
      obtain ⟨e, he_mem, hxe⟩ := by
        simpa only [List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil,
          or_false] using hW2cover x.1 ⟨hxL, hx1⟩
      obtain ⟨p, hpW, hp_e⟩ := he_mem
      rw [← hp_e] at hxe
      obtain ⟨hp1, hp3, hpL, hp2, hpwit⟩ := hW2facts p hpW
      have hordp : orderOf p.1 = 3 := orderOf_eq_prime hp3 hp1
      have hxzp : x.1 ∈ Subgroup.zpowers p.1 := by
        rcases hxe with hxp | hxp
        · rw [hxp]; exact Subgroup.mem_zpowers p.1
        · rw [hxp]; exact Subgroup.npow_mem_zpowers p.1 2
      have hxord : orderOf x.1 = 3 := by
        rcases hxe with hxp | hxp
        · rw [hxp]; exact hordp
        · rw [hxp, orderOf_pow' (x := p.1) (n := 2) (by norm_num), hordp]
          norm_num
      have hEeq : E = Subgroup.zpowers x.1 :=
        (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2)
          (by rw [hcard, Nat.card_zpowers, hxord])).symm
      have hEzp : Subgroup.zpowers x.1 = Subgroup.zpowers p.1 :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxzp)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hordp])
      have hperm' : Permutes (Subgroup.zpowers p.1) S0 := by
        rw [← hEzp, ← hEeq]
        exact hperm
      have hp2S0 : p.2 ∈ S0 := by
        rw [hS0def]
        exact mem_l33ParabolicListSubgroup.2 hp2
      have hmem1 : p.1 * p.2 ∈ (Subgroup.zpowers p.1 : Set (Equiv.Perm (Fin 26))) *
          (S0 : Set (Equiv.Perm (Fin 26))) :=
        ⟨p.1, Subgroup.mem_zpowers p.1, p.2, hp2S0, rfl⟩
      have hmem2 : p.1 * p.2 ∈ (S0 : Set (Equiv.Perm (Fin 26))) *
          (Subgroup.zpowers p.1 : Set (Equiv.Perm (Fin 26))) := by
        rwa [hperm'] at hmem1
      exact hpwit (mem_flatMap_three_of_mem_mul_zpowers hp3 hp1 hmem2)
    · right
      exact Subgroup.eq_of_le_of_card_ge hEU (by rw [hU2card, hcard])
  have hPcard : Nat.card QP.originalSubgroup = 5616 := by
    rw [card_group QP QP_ok, QP_valid.2]
  have hQUcard : Nat.card (parabolicQU ()).originalSubgroup = 5616 := parabolicQU_card hQUc hQUo
  have hQUleP : (parabolicQU ()).originalSubgroup ≤ QP.originalSubgroup := by
    rw [parabolicQU_closure]
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hU1P (mem_l33ParabolicListSubgroup.2 (by simp [pow3list]))
    · exact hU1P (mem_l33ParabolicListSubgroup.2 (by simp [pow3list]))
    · exact hU2P (mem_l33ParabolicListSubgroup.2 (by simp [pow3list]))
    · exact hU2P (mem_l33ParabolicListSubgroup.2 (by simp [pow3list]))
  have hQUeqP : (parabolicQU ()).originalSubgroup = QP.originalSubgroup :=
    Subgroup.eq_of_le_of_card_ge hQUleP (by rw [hQUcard, hPcard])
  have hU1leQU : U1 ≤ (parabolicQU ()).originalSubgroup := by
    intro x hx
    have hxL : x ∈ pow3list parabolicU1a parabolicU1b := by simpa [hU1def] using hx
    have hgena : parabolicU1a ∈ (parabolicQU ()).originalSubgroup := by
      rw [parabolicQU_closure]
      exact Subgroup.subset_closure (by simp)
    have hgenb : parabolicU1b ∈ (parabolicQU ()).originalSubgroup := by
      rw [parabolicQU_closure]
      exact Subgroup.subset_closure (by simp)
    have hxcl : x ∈ Subgroup.closure ({parabolicU1a, parabolicU1b} : Set (Equiv.Perm (Fin 26))) :=
      pow3list_subset (Subgroup.closure ({parabolicU1a, parabolicU1b} : Set (Equiv.Perm (Fin 26))))
        (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) hxL
    exact (Subgroup.closure_le _).2
      (by intro y hy; rcases hy with rfl | rfl; exact hgena; exact hgenb) hxcl
  have hU2leQU : U2 ≤ (parabolicQU ()).originalSubgroup := by
    intro x hx
    have hxL : x ∈ pow3list parabolicU2a parabolicU2b := by simpa [hU2def] using hx
    have hgena : parabolicU2a ∈ (parabolicQU ()).originalSubgroup := by
      rw [parabolicQU_closure]
      exact Subgroup.subset_closure (by simp)
    have hgenb : parabolicU2b ∈ (parabolicQU ()).originalSubgroup := by
      rw [parabolicQU_closure]
      exact Subgroup.subset_closure (by simp)
    have hxcl : x ∈ Subgroup.closure ({parabolicU2a, parabolicU2b} : Set (Equiv.Perm (Fin 26))) :=
      pow3list_subset (Subgroup.closure ({parabolicU2a, parabolicU2b} : Set (Equiv.Perm (Fin 26))))
        (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) hxL
    exact (Subgroup.closure_le _).2
      (by intro y hy; rcases hy with rfl | rfl; exact hgena; exact hgenb) hxcl
  have hQUleU1U2 : (parabolicQU ()).originalSubgroup ≤ U1 ⊔ U2 := by
    rw [parabolicQU_closure]
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (mem_l33ParabolicListSubgroup.2 (by simp [pow3list]))
    · exact Subgroup.mem_sup_left (mem_l33ParabolicListSubgroup.2 (by simp [pow3list]))
    · exact Subgroup.mem_sup_right (mem_l33ParabolicListSubgroup.2 (by simp [pow3list]))
    · exact Subgroup.mem_sup_right (mem_l33ParabolicListSubgroup.2 (by simp [pow3list]))
  have hsup : U1 ⊔ U2 = QP.originalSubgroup := by
    have h1 : U1 ⊔ U2 = (parabolicQU ()).originalSubgroup :=
      le_antisymm (sup_le hU1leQU hU2leQU) hQUleU1U2
    rw [h1, hQUeqP]
  exact ⟨S0, U1, U2, hS0P, hS0card, hU1P, hU2P, hU1el, hU1card,
    hU2el, hU2card, hS0norm1, hS0norm2, hU1rad, hU2rad, hsup⟩

private theorem isRadical_of_comap
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} (hKN : K.Normal)
    (e : ↥K ≃* QP.originalSubgroup)
    {T : Subgroup Y} (hT : T = S ⊓ K)
    {U S0 : Subgroup QP.originalSubgroup} {V : Subgroup ↥K}
    (hVmap : V.map e.toMonoidHom = U)
    (hS0map : (T.subgroupOf K).map e.toMonoidHom = S0)
    (hUel : IsElemAbelian 3 U) (hUcard : Nat.card U = 9)
    (hUnorm : S0 ≤ Subgroup.normalizer (U : Set (QP.originalSubgroup)))
    (hUrad : ∀ E, E ≤ U → Permutes E S0 → E = ⊥ ∨ E = U) :
    IsL33ParabolicRadical K S (V.map K.subtype) := by
  classical
  have hVeq : V = U.comap e.toMonoidHom := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hVmap, Subgroup.map_comap_eq_self_of_surjective e.surjective U]
  have hVel : IsElemAbelian 3 V := by
    rw [hVeq]
    exact hUel.comap e.injective
  have hVcard : Nat.card V = 9 := by
    have h1 : Nat.card (V.map e.toMonoidHom) = Nat.card V :=
      Subgroup.card_map_of_injective e.injective
    rw [← h1, hVmap, hUcard]
  have hVYle : V.map K.subtype ≤ K := Subgroup.map_subtype_le V
  have hVYel : IsElemAbelian 3 (V.map K.subtype) := hVel.map K.subtype
  have hVYcard : Nat.card (V.map K.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hVcard]
  have hVYnorm : T ≤ Subgroup.normalizer ((V.map K.subtype : Subgroup Y) :
      Set Y) := by
    intro t ht
    apply mem_normalizer_of_conj_mem (P := V.map K.subtype)
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    have htK : t ∈ K := hT ▸ ht |>.2
    let tk : ↥K := ⟨t, htK⟩
    have htkT : tk ∈ T.subgroupOf K := ht
    have hetk : e tk ∈ S0 := by
      rw [← hS0map]
      exact Subgroup.mem_map_of_mem e.toMonoidHom htkT
    have hev : e v ∈ U := by rw [← hVmap]; exact Subgroup.mem_map_of_mem e.toMonoidHom hv
    have hconj : e tk * e v * (e tk)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hUnorm hetk) (e v)).mp hev
    have hconj' : e (tk * v * tk⁻¹) ∈ U := by
      simpa [map_mul, map_inv] using hconj
    have hmemV : tk * v * tk⁻¹ ∈ V := by
      rw [hVeq]
      exact hconj'
    exact Subgroup.mem_map.mpr ⟨tk * v * tk⁻¹, hmemV, rfl⟩
  have hVYrad : ∀ E : Subgroup Y, E ≤ V.map K.subtype → Permutes E T →
      E = ⊥ ∨ E = V.map K.subtype := by
    intro E hE hperm
    let Es : Subgroup ↥K := E.subgroupOf K
    have hEKs : E ≤ K := hE.trans hVYle
    have hEsmap : Es.map K.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEKs
    have hEsTK : Permutes Es (T.subgroupOf K) := by
      refine CFSG.GroupTheory.permutes_of_map_permutes K.subtype ?_ ?_
      · simp
      · rwa [hEsmap, Subgroup.map_subgroupOf_eq_of_le (hT ▸ inf_le_right : T ≤ K)]
    have hEsV : Es ≤ V := by
      intro x hx
      have hxE : x.1 ∈ E := Subgroup.mem_subgroupOf.mp hx
      have hxVY : x.1 ∈ V.map K.subtype := hE hxE
      obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hxVY
      have hveq : v = x := Subtype.ext hvx
      rwa [hveq] at hv
    have hFle : Es.map e.toMonoidHom ≤ U := by
      rw [← hVmap]
      exact Subgroup.map_mono hEsV
    have hFperm : Permutes (Es.map e.toMonoidHom) S0 := by
      have h := CFSG.GroupTheory.map_permutes_map e.toMonoidHom hEsTK
      rwa [hS0map] at h
    rcases hUrad (Es.map e.toMonoidHom) hFle hFperm with hbot | htop
    · left
      have hEsbot : Es = ⊥ := by
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        rw [hbot, Subgroup.map_bot]
      calc E = Es.map K.subtype := hEsmap.symm
        _ = ⊥ := by rw [hEsbot, Subgroup.map_bot]
    · right
      have hEsV : Es = V := by
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        rw [htop, hVmap]
      calc E = Es.map K.subtype := hEsmap.symm
        _ = V.map K.subtype := by rw [hEsV]
  have hVYrad' : ∀ E : Subgroup Y, E ≤ V.map K.subtype → Permutes E (S ⊓ K) →
      E = ⊥ ∨ E = V.map K.subtype := by
    simpa [hT] using hVYrad
  exact ⟨hVYle, hVYel, hVYcard, by simpa [hT] using hVYnorm, hVYrad'⟩

private theorem radical_map_aut {P : Type} [Group P] (τ : P ≃* P) {U S0 : Subgroup P}
    (hUel : IsElemAbelian 3 U) (hUcard : Nat.card U = 9)
    (hUnorm : S0 ≤ Subgroup.normalizer (U : Set P))
    (hUrad : ∀ E, E ≤ U → Permutes E S0 → E = ⊥ ∨ E = U) :
    IsElemAbelian 3 (U.map τ.symm.toMonoidHom) ∧
    Nat.card (U.map τ.symm.toMonoidHom) = 9 ∧
    (S0.map τ.symm.toMonoidHom ≤ Subgroup.normalizer
      ((U.map τ.symm.toMonoidHom : Subgroup P) : Set P)) ∧
    (∀ E, E ≤ U.map τ.symm.toMonoidHom → Permutes E (S0.map τ.symm.toMonoidHom) →
      E = ⊥ ∨ E = U.map τ.symm.toMonoidHom) := by
  have hUel' : IsElemAbelian 3 (U.map τ.symm.toMonoidHom) := hUel.map _
  have hUcard' : Nat.card (U.map τ.symm.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective τ.symm.injective, hUcard]
  have hUnorm' : S0.map τ.symm.toMonoidHom ≤ Subgroup.normalizer
      ((U.map τ.symm.toMonoidHom : Subgroup P) : Set P) := by
    rw [← Subgroup.map_equiv_normalizer_eq U τ.symm]
    exact Subgroup.map_mono hUnorm
  have hUrad' : ∀ E, E ≤ U.map τ.symm.toMonoidHom →
      Permutes E (S0.map τ.symm.toMonoidHom) → E = ⊥ ∨ E = U.map τ.symm.toMonoidHom := by
    intro E hE hperm
    have hE' : E.map τ.toMonoidHom ≤ U := by
      calc E.map τ.toMonoidHom ≤ (U.map τ.symm.toMonoidHom).map τ.toMonoidHom :=
            Subgroup.map_mono hE
        _ = U := by rw [Subgroup.map_map]; simp
    have hmapS0 : (S0.map τ.symm.toMonoidHom).map τ.toMonoidHom = S0 := by
      rw [Subgroup.map_map]; simp
    have hperm' : Permutes (E.map τ.toMonoidHom) S0 := by
      have h := CFSG.GroupTheory.map_permutes_map τ.toMonoidHom hperm
      rwa [hmapS0] at h
    rcases hUrad (E.map τ.toMonoidHom) hE' hperm' with hbot | htop
    · left
      apply Subgroup.map_injective (f := τ.toMonoidHom) τ.injective
      rw [hbot, Subgroup.map_bot]
    · right
      apply Subgroup.map_injective (f := τ.toMonoidHom) τ.injective
      rw [htop, Subgroup.map_map]
      simp
  exact ⟨hUel', hUcard', hUnorm', hUrad'⟩

theorem k_L33ParabolicPair_holds :
    K_L33ParabolicPair := by
  intro Y _ _ K S hKY hLie
  classical
  have hIndex_le : K.index ≤ 2 := l33ParabolicIndex_le_two hKY hLie
  obtain ⟨hKN, hKq, hZodd, hCent, ⟨a, hKindex⟩, hSylY⟩ := hKY
  obtain ⟨e⟩ := equiv_of_lieModel hLie
  obtain ⟨S0, U1, U2, hS0P, hS0card, hU1P, hU2P, hU1el, hU1card,
    hU2el, hU2card, hS0norm1, hS0norm2, hU1rad, hU2rad, hsup⟩ := l33ParabolicModelFacts
  have hParity : ∀ x ∈ S, ∀ y ∈ S, x ∉ K → y ∉ K → x * y ∈ K := by
    intro x hxS y hyS hxK hyK
    set T : Subgroup Y := S ⊓ K with hTdef
    have hTrel : T.relIndex S ≤ 2 := by
      have h1 : T.relIndex S = K.relIndex S := Subgroup.inf_relIndex_left S K
      have h2 : K.relIndex S = K.relIndex (S ⊔ K) := by
        rw [Subgroup.relIndex_sup_right]
      have hKpos : K.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
      have h3 : K.relIndex (S ⊔ K) ∣ K.index :=
        Subgroup.relIndex_dvd_index_of_le (le_sup_right : K ≤ S ⊔ K)
      rw [h1, h2]
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hKpos) h3).trans hIndex_le
    let TS : Subgroup S := T.subgroupOf S
    have hTSindex : TS.index = T.relIndex S := rfl
    have hTSle : TS.index ≤ 2 := by rw [hTSindex]; exact hTrel
    have : TS.FiniteIndex := Subgroup.finiteIndex_of_finite
    have hTSpos : TS.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hTS1or2 : TS.index = 1 ∨ TS.index = 2 := by omega
    rcases hTS1or2 with h1 | h2
    · have htop : TS = ⊤ := (Subgroup.index_eq_one).1 h1
      have hxT : (⟨x, hxS⟩ : S) ∈ TS := by rw [htop]; exact Subgroup.mem_top _
      exact absurd (Subgroup.mem_subgroupOf.mp hxT).2 hxK
    · have hmem : (⟨x, hxS⟩ : S) * ⟨y, hyS⟩ ∈ TS := by
        rw [Subgroup.mul_mem_iff_of_index_two h2]
        constructor
        · intro hxTS
          exact absurd (Subgroup.mem_subgroupOf.mp hxTS).2 hxK
        · intro hyTS
          exact absurd (Subgroup.mem_subgroupOf.mp hyTS).2 hyK
      exact (Subgroup.mem_subgroupOf.mp hmem).2
  refine ⟨hParity, ?_⟩
  let P : Subgroup (Equiv.Perm (Fin 26)) := QP.originalSubgroup
  set T : Subgroup Y := S ⊓ K with hTdef
  have hTsylK : IsSylowIn 2 T K := by
    have hSylTwo : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := hSylY
    have hT_two : CFSG.QuasithinUnique.IsSylowTwoOf (K ⊓ S) K :=
      CFSG.isSylowTwoOf_inf_of_normal (S := S) (X := ⊤) (N := K) hSylTwo
        le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hKN])
    have h' : IsSylowIn 2 (K ⊓ S) K := by
      refine ⟨hT_two.1, hT_two.2.1, ?_⟩
      simpa [Subgroup.relIndex] using hT_two.2.2
    simpa [hTdef, inf_comm] using h'
  set TK : Subgroup ↥K := T.subgroupOf K with hTKdef
  have hTKsyl : IsSylowIn 2 TK ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hTsylK.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTsylK.le).symm
    · rw [Subgroup.relIndex_top_right]
      simpa [Subgroup.relIndex, hTKdef] using hTsylK.not_dvd_relIndex
  have hTeP : IsSylowIn 2 (TK.map e.toMonoidHom) ⊤ := by
    have h := (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv e).mpr hTKsyl
    simpa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using h
  set S0P : Subgroup P := S0.subgroupOf P with hS0Pdef
  have hPcard : Nat.card P = 5616 := by
    dsimp [P]
    rw [card_group QP QP_ok, QP_valid.2]
  have hS0Pcard : Nat.card S0P = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0P).toEquiv, hS0card]
  have hS0syl : IsSylowIn 2 S0P ⊤ := by
    refine isSylowIn_of_card_eq (p := 2) le_top ?_
    have hfac : (5616 : ℕ).factorization 2 = 4 := by
      have h1 : (5616 : ℕ) = 2 ^ 4 * 351 := by norm_num
      rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (351 : ℕ))]
    rw [hS0Pcard, Subgroup.card_top, hPcard, hfac]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.exists_mulEquiv_map_eq_of_isSylowIn
      (p := 2) (e := MulEquiv.refl P) hTeP hS0syl
  set U1P : Subgroup P := U1.subgroupOf P with hU1Pdef
  set U2P : Subgroup P := U2.subgroupOf P with hU2Pdef
  have hU1Pcard : Nat.card U1P = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU1P).toEquiv, hU1card]
  have hU2Pcard : Nat.card U2P = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU2P).toEquiv, hU2card]
  have hU1Pel : IsElemAbelian 3 U1P := by
    simpa [hU1Pdef] using hU1el.subgroupOf P
  have hU2Pel : IsElemAbelian 3 U2P := by
    simpa [hU2Pdef] using hU2el.subgroupOf P
  have hS0Pnorm1 : S0P ≤ Subgroup.normalizer (U1P : Set P) := by
    rw [hS0Pdef, hU1Pdef, ← Subgroup.subgroupOf_normalizer_eq hU1P]
    exact Subgroup.subgroupOf_mono P hS0norm1
  have hS0Pnorm2 : S0P ≤ Subgroup.normalizer (U2P : Set P) := by
    rw [hS0Pdef, hU2Pdef, ← Subgroup.subgroupOf_normalizer_eq hU2P]
    exact Subgroup.subgroupOf_mono P hS0norm2
  have hU1Prad : ∀ E, E ≤ U1P → Permutes E S0P → E = ⊥ ∨ E = U1P := by
    intro E hE hperm
    have hE' : E.map P.subtype ≤ U1 := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hU1P]
      exact Subgroup.map_mono hE
    have hperm' : Permutes (E.map P.subtype) S0 := by
      have h := CFSG.GroupTheory.map_permutes_map P.subtype hperm
      rwa [Subgroup.map_subgroupOf_eq_of_le hS0P] at h
    rcases hU1rad (E.map P.subtype) hE' hperm' with hbot | htop
    · left
      apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
      rw [hbot, Subgroup.map_bot]
    · right
      apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
      rw [htop, Subgroup.map_subgroupOf_eq_of_le hU1P]
  have hU2Prad : ∀ E, E ≤ U2P → Permutes E S0P → E = ⊥ ∨ E = U2P := by
    intro E hE hperm
    have hE' : E.map P.subtype ≤ U2 := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hU2P]
      exact Subgroup.map_mono hE
    have hperm' : Permutes (E.map P.subtype) S0 := by
      have h := CFSG.GroupTheory.map_permutes_map P.subtype hperm
      rwa [Subgroup.map_subgroupOf_eq_of_le hS0P] at h
    rcases hU2rad (E.map P.subtype) hE' hperm' with hbot | htop
    · left
      apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
      rw [hbot, Subgroup.map_bot]
    · right
      apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
      rw [htop, Subgroup.map_subgroupOf_eq_of_le hU2P]
  set U1P' : Subgroup P := U1P.map τ.symm.toMonoidHom with hU1P'def
  set U2P' : Subgroup P := U2P.map τ.symm.toMonoidHom with hU2P'def
  obtain ⟨hU1P'el, hU1P'card, hU1P'norm, hU1P'rad⟩ :=
    radical_map_aut (τ := τ) (U := U1P) (S0 := S0P) hU1Pel hU1Pcard hS0Pnorm1 hU1Prad
  obtain ⟨hU2P'el, hU2P'card, hU2P'norm, hU2P'rad⟩ :=
    radical_map_aut (τ := τ) (U := U2P) (S0 := S0P) hU2Pel hU2Pcard hS0Pnorm2 hU2Prad
  rw [← hU1P'def] at hU1P'el hU1P'card hU1P'norm hU1P'rad
  rw [← hU2P'def] at hU2P'el hU2P'card hU2P'norm hU2P'rad
  have hS0map : TK.map e.toMonoidHom = S0P.map τ.symm.toMonoidHom := by
    rw [← hτ, Subgroup.map_map]
    simp
  set V1K : Subgroup ↥K := U1P'.comap e.toMonoidHom with hV1Kdef
  set V2K : Subgroup ↥K := U2P'.comap e.toMonoidHom with hV2Kdef
  have hV1map : V1K.map e.toMonoidHom = U1P' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective U1P'
  have hV2map : V2K.map e.toMonoidHom = U2P' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective U2P'
  have hRad1 : IsL33ParabolicRadical K S (V1K.map K.subtype) :=
    isRadical_of_comap hKN e hTdef hV1map hS0map hU1P'el hU1P'card hU1P'norm hU1P'rad
  have hRad2 : IsL33ParabolicRadical K S (V2K.map K.subtype) :=
    isRadical_of_comap hKN e hTdef hV2map hS0map hU2P'el hU2P'card hU2P'norm hU2P'rad
  have hU1Psup : U1P ⊔ U2P = ⊤ := by
    apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hU1P,
      Subgroup.map_subgroupOf_eq_of_le hU2P, hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hU1P'sup : U1P' ⊔ U2P' = ⊤ := by
    rw [hU1P'def, hU2P'def, ← Subgroup.map_sup, hU1Psup,
      Subgroup.map_top_of_surjective τ.symm.toMonoidHom τ.symm.surjective]
  have hVsup : V1K ⊔ V2K = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, hV1map, hV2map, hU1P'sup,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  have hVYsup : V1K.map K.subtype ⊔ V2K.map K.subtype = K := by
    rw [← Subgroup.map_sup, hVsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact ⟨V1K.map K.subtype, V2K.map K.subtype, hRad1, hRad2, hVYsup⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
