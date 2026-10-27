module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Lift
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Quasithin.Vol2.Ch11SKFIto
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.HardMathSupport.Foote.E27.LieTwo.SylowNormal

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155T51

theorem three_dvd_card_of_isComponent {Q : Type*} [Group Q] [Finite Q]
    (hO : CFSG.pPrimeCore 3 Q = ⊥) {Y : Subgroup Q} (hY : CFSG.IsComponent Y) :
    3 ∣ Nat.card Y := by
  by_contra h3
  have hcop : Nat.Coprime 3 (Nat.card Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hle : Y ≤ CFSG.pPrimeCore 3 Q := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hY.2 hcop
  rw [hO, le_bot_iff] at hle
  have hnt : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY.1
  exact (Subgroup.nontrivial_iff_ne_bot Y).mp hnt hle

theorem exists_pow_three_not_commute_of_isComponent {Q : Type*} [Group Q] [Finite Q]
    (hO : CFSG.pPrimeCore 3 Q = ⊥) {Y : Subgroup Q} (hY : CFSG.IsComponent Y) :
    ∃ u ∈ Y, u ^ 3 = 1 ∧ ∃ y ∈ Y, u * y ≠ y * u := by
  haveI : Group.IsPerfect Y := hY.1.1
  obtain ⟨x, hx3, hxc⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center (p := 3) (by norm_num)
      (three_dvd_card_of_isComponent hO hY)
  rw [Subgroup.mem_center_iff] at hxc
  push Not at hxc
  obtain ⟨y, hy⟩ := hxc
  refine ⟨x, x.2, by simpa using congrArg Subtype.val hx3, y, y.2, fun h => hy ?_⟩
  exact Subtype.ext h.symm

private theorem exists_isPGroup_two_ne_bot_of_isComponent {Q : Type*} [Group Q] [Finite Q]
    {Y : Subgroup Q} (hY : CFSG.IsComponent Y) :
    ∃ T : Subgroup Q, T ≤ Y ∧ T ≠ ⊥ ∧ IsPGroup 2 T := by
  have hnt : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY.1
  haveI : Group.IsPerfect Y := hY.1.1
  have h2 : 2 ∣ Nat.card Y := by
    by_contra h
    exact Group.IsPerfect.not_isSolvable Y
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)))
  obtain ⟨P⟩ : Nonempty (Sylow 2 Y) := inferInstance
  refine ⟨(P : Subgroup Y).map Y.subtype, ?_, ?_, P.isPGroup'.map _⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro h
    refine P.ne_bot_of_dvd_card h2 ?_
    exact Subgroup.map_injective Y.subtype_injective (by rw [h, Subgroup.map_bot])

private theorem exists_pow_three_mem_center_of_normal {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 3 P) {V : Subgroup P} [V.Normal] (hV : V ≠ ⊥) :
    ∃ w ∈ V, w ≠ 1 ∧ w ^ 3 = 1 ∧ w ∈ Subgroup.center P := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have h1 : V ⊓ Subgroup.center P ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hV
  haveI : Nontrivial ↥(V ⊓ Subgroup.center P) := (Subgroup.nontrivial_iff_ne_bot _).mpr h1
  obtain ⟨n, hn, hcard⟩ :=
    (hP.to_subgroup (V ⊓ Subgroup.center P)).nontrivial_iff_card.mp inferInstance
  have h3 : 3 ∣ Nat.card ↥(V ⊓ Subgroup.center P) := hcard ▸ dvd_pow_self 3 hn.ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨(x : P), x.2.1, ?_, ?_, x.2.2⟩
  · intro h
    have hx1 : x = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at hx
    omega
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this

private theorem exists_pow_three_commute_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {V A : Subgroup G} (hV3 : 3 ∣ Nat.card V) (hA : IsPGroup 3 A)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ w ∈ V, w ≠ 1 ∧ w ^ 3 = 1 ∧ ∀ a ∈ A, a * w = w * a := by
  set H : Subgroup G := V ⊔ A
  have hVH : V ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hnorm : (V.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVH).mpr (sup_le Subgroup.le_normalizer hAV)
  obtain ⟨S, hAS⟩ := (hA.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨P, hP⟩ :=
    CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq (V.subgroupOf H) S
  have h3V' : 3 ∣ Nat.card (V.subgroupOf H) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]
  have hP1 : (P : Subgroup ↥(V.subgroupOf H)) ≠ ⊥ := P.ne_bot_of_dvd_card h3V'
  obtain ⟨⟨x, hxP⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  rw [hP] at hxP
  have hxS : (x : ↥H) ∈ (S : Subgroup ↥H) := hxP
  have hW : (V.subgroupOf H).subgroupOf (S : Subgroup ↥H) ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨⟨(x : ↥H), hxS⟩, x.2⟩, fun h => hx1 ?_⟩
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun z : ↥(S : Subgroup ↥H) => (z : ↥H)) (Subtype.ext_iff.mp h))
  haveI : ((V.subgroupOf H).subgroupOf (S : Subgroup ↥H)).Normal := hnorm.subgroupOf _
  obtain ⟨w, hwW, hw1, hw3, hwc⟩ := exists_pow_three_mem_center_of_normal S.isPGroup' hW
  refine ⟨((w : ↥H) : G), hwW, ?_, ?_, fun a ha => ?_⟩
  · intro h
    exact hw1 (Subtype.ext (Subtype.ext h))
  · simpa using congrArg (fun z : ↥(S : Subgroup ↥H) => ((z : ↥H) : G)) hw3
  · have haS : (⟨a, hAH ha⟩ : ↥H) ∈ (S : Subgroup ↥H) := hAS ha
    exact congrArg (fun z : ↥(S : Subgroup ↥H) => ((z : ↥H) : G))
      (Subgroup.mem_center_iff.mp hwc ⟨⟨a, hAH ha⟩, haS⟩)

variable {M : Type*} [Group M] [Finite M]

theorem eq_of_isComponent {B : Subgroup M} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (hBZ : B ≤ Subgroup.center M)
    (hmax : ∀ E : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      (∃ U : Subgroup M, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set M)) →
      ∀ E' : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E' → E ≤ E' → E' = E)
    {Y₁ Y₂ : Subgroup (M ⧸ CFSG.pPrimeCore 3 M)} (hY₁ : CFSG.IsComponent Y₁)
    (hY₂ : CFSG.IsComponent Y₂) : Y₁ = Y₂ := by
  by_contra hne
  set N := CFSG.pPrimeCore 3 M
  set π := QuotientGroup.mk' N
  have hN : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hO : CFSG.pPrimeCore 3 (M ⧸ N) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hB3 : IsPGroup 3 B := hB.isPGroup
  have hcomm : ∀ x ∈ Y₁, ∀ y ∈ Y₂, x * y = y * x := by
    rcases CFSG.LocalCores.distinct_components_commute hY₁ hY₂ with h | h
    · exact absurd h hne
    · intro x hx y hy
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) y hy).symm
  set Bt : Subgroup (M ⧸ N) := B.map π
  have hBtel : CFSG.Assembly.IsElemAbelian 3 Bt := hB.map π
  have hBtcard : Nat.card Bt = 9 := (card_map_mk N hN hB3).trans hB9
  have hBtc : ∀ b ∈ Bt, ∀ z : M ⧸ N, b * z = z * b := by
    rintro _ ⟨b, hb, rfl⟩ z
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective z
    exact congrArg (QuotientGroup.mk (s := N)) (Subgroup.mem_center_iff.mp (hBZ hb) m).symm
  obtain ⟨u₁, hu₁Y, hu₁3, y₁, hy₁Y, hu₁y₁⟩ :=
    exists_pow_three_not_commute_of_isComponent hO hY₁
  obtain ⟨u₂, hu₂Y, hu₂3, y₂, hy₂Y, hu₂y₂⟩ :=
    exists_pow_three_not_commute_of_isComponent hO hY₂
  have hu₁Bt : u₁ ∉ Bt := fun h => hu₁y₁ (hBtc u₁ h y₁)
  obtain ⟨hE₁el, hE₁card⟩ :=
    CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hBtel hu₁Bt hu₁3
      (fun a ha => hBtc a ha u₁)
  set E₁ : Subgroup (M ⧸ N) := Bt ⊔ Subgroup.zpowers u₁
  have hE₁Y₂ : ∀ e ∈ E₁, ∀ z ∈ Y₂, e * z = z * e := by
    have hle : E₁ ≤ Subgroup.centralizer (Y₂ : Set (M ⧸ N)) := by
      refine sup_le ?_ ?_
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro z _
        exact (hBtc b hb z).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hcomm u₁ hu₁Y z hz).symm
    intro e he z hz
    exact (Subgroup.mem_centralizer_iff.mp (hle he) z hz).symm
  have hu₂E₁ : u₂ ∉ E₁ := fun h => hu₂y₂ (hE₁Y₂ u₂ h y₂ hy₂Y)
  obtain ⟨hE₂el, -⟩ :=
    CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hE₁el hu₂E₁ hu₂3
      (fun a ha => hE₁Y₂ a ha u₂ hu₂Y)
  set E₂ : Subgroup (M ⧸ N) := E₁ ⊔ Subgroup.zpowers u₂
  have hE₁E₂ : E₁ ≤ E₂ := le_sup_left
  obtain ⟨S, -, hSE₂, hSel, -⟩ :=
    exists_elemAbelian_lift_le N hN hB3 hE₂el (le_sup_left.trans hE₁E₂)
  set S₁ : Subgroup M := S ⊓ E₁.comap π
  have hS₁S : S₁ ≤ S := inf_le_left
  have hS₁map : S₁.map π = E₁ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact hs.2
    · intro e he
      have he₂ : e ∈ S.map π := by
        rw [hSE₂]
        exact hE₁E₂ he
      obtain ⟨s, hsS, rfl⟩ := he₂
      exact ⟨s, ⟨hsS, he⟩, rfl⟩
  have hS₁3 : IsPGroup 3 S₁ := hSel.isPGroup.to_le hS₁S
  have hS₁card : Nat.card S₁ = 27 := by
    rw [← card_map_mk N hN hS₁3, hS₁map, hE₁card, hBtcard]
  have hS₁el : CFSG.Assembly.IsElemAbelian 3 S₁ := hSel.mono hS₁S
  obtain ⟨T, hTY₂, hT1, hT2⟩ := exists_isPGroup_two_ne_bot_of_isComponent hY₂
  have hS₁T : S₁.map π ≤ Subgroup.normalizer (T : Set (M ⧸ N)) := by
    rw [hS₁map]
    intro e he
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (hE₁Y₂ e he t (hTY₂ ht)).symm
  obtain ⟨U, hU1, hU2, hS₁U⟩ := exists_two_subgroup_of_map_le_normalizer N hN hS₁3 hT2 hT1 hS₁T
  have hSS₁ : S = S₁ := hmax S₁ hS₁el hS₁card ⟨U, hU1, hU2, hS₁U⟩ S hSel hS₁S
  apply hu₂E₁
  have hu₂S : u₂ ∈ S.map π := by
    rw [hSE₂]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u₂)
  rwa [hSS₁, hS₁map] at hu₂S

theorem exists_mem_of_isComponent {A : Subgroup M} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ E : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E → A ≤ E → E = A)
    {Y : Subgroup (M ⧸ CFSG.pPrimeCore 3 M)} (hY : CFSG.IsComponent Y)
    (hAY : A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 M)) ≤
      Subgroup.normalizer (Y : Set (M ⧸ CFSG.pPrimeCore 3 M))) :
    ∃ a ∈ A, a ≠ 1 ∧ QuotientGroup.mk' (CFSG.pPrimeCore 3 M) a ∈ Y := by
  set N := CFSG.pPrimeCore 3 M
  set π := QuotientGroup.mk' N
  have hN : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hO : CFSG.pPrimeCore 3 (M ⧸ N) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hA3 : IsPGroup 3 A := hA.isPGroup
  obtain ⟨w, hwY, hw1, hw3, hwc⟩ := exists_pow_three_commute_of_le_normalizer
    (three_dvd_card_of_isComponent hO hY) (hA3.map π) hAY
  by_cases hwA : w ∈ A.map π
  · obtain ⟨a, haA, rfl⟩ := hwA
    refine ⟨a, haA, ?_, hwY⟩
    rintro rfl
    exact hw1 (map_one π)
  ·
    exfalso
    obtain ⟨hE, -⟩ :=
      CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers (hA.map π) hwA hw3 hwc
    obtain ⟨S, hAS, hSE, hSel, -⟩ := exists_elemAbelian_lift_le N hN hA3 hE le_sup_left
    have hSA : S = A := hAmax S hSel hAS
    apply hwA
    have hwS : w ∈ S.map π := by
      rw [hSE]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    rwa [hSA] at hwS

end CFSG.RankThree.PartTwo.Sec15.Sylow155T51
