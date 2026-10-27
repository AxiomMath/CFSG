module

public import CFSG.Quasithin.EmptyFaithful.S153DGen2
public import CFSG.Quasithin.EmptyFaithful.S153D12

public section

namespace CFSG.Quasithin.S153D

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Perfect

variable {G : Type*} [Group G]

omit [Group G] in
theorem eq_one_of_isPerfect_of_isSolvable {Q : Type*} [Group Q] [Group.IsPerfect Q]
    [Group.IsSolvable Q] (x : Q) : x = 1 := by
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable Q).solvable
  have h := Group.IsPerfect.derivedSeries_eq_top Q n
  rw [hn] at h
  have hx : x ∈ (⊤ : Subgroup Q) := Subgroup.mem_top x
  rw [← h] at hx
  exact Subgroup.mem_bot.mp hx

theorem isPerfect_of_commutator_eq {X : Subgroup G} (h : ⁅X, X⁆ = X) : Group.IsPerfect ↥X := by
  rw [Group.isPerfect_def]
  have e := Subgroup.map_commutator (⊤ : Subgroup ↥X) (⊤ : Subgroup ↥X) X.subtype
  have e2 : (⊤ : Subgroup ↥X).map X.subtype = X := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [e2, h] at e
  rw [commutator_def]
  exact Subgroup.map_injective X.subtype_injective (e.trans e2.symm)

theorem commutator_commutator_le_of_rotate {N A B C : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (N : Set G)) (hB : B ≤ Subgroup.normalizer (N : Set G))
    (hC : C ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅B, C⁆, A⁆ ≤ N) (h2 : ⁅⁅C, A⁆, B⁆ ≤ N) :
    ⁅⁅A, B⁆, C⁆ ≤ N := by
  set X : Subgroup G := Subgroup.normalizer (N : Set G) with hX
  have hNX : N ≤ X := Subgroup.le_normalizer
  have hnorm : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr le_rfl
  let π : ↥X →* ↥X ⧸ N.subgroupOf X := QuotientGroup.mk' (N.subgroupOf X)
  have hle : ∀ {U V : Subgroup G}, U ≤ X → V ≤ X → ⁅U, V⁆ ≤ X := fun hU hV =>
    (Subgroup.commutator_le_sup _ _).trans (sup_le hU hV)
  have hmap : ∀ {U V W : Subgroup G}, U ≤ X → V ≤ X → W ≤ X →
      ((⁅⁅U, V⁆, W⁆).subgroupOf X).map π =
        ⁅⁅(U.subgroupOf X).map π, (V.subgroupOf X).map π⁆, (W.subgroupOf X).map π⁆ := by
    intro U V W hU hV hW
    rw [commutator_subgroupOf_eq' (hle hU hV) hW, commutator_subgroupOf_eq' hU hV,
      Subgroup.map_commutator, Subgroup.map_commutator]
  have hbot : ∀ {U V W : Subgroup G}, U ≤ X → V ≤ X → W ≤ X → ⁅⁅U, V⁆, W⁆ ≤ N →
      ⁅⁅(U.subgroupOf X).map π, (V.subgroupOf X).map π⁆, (W.subgroupOf X).map π⁆ = ⊥ := by
    intro U V W hU hV hW h
    rw [← hmap hU hV hW, eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    have : y ∈ N.subgroupOf X := Subgroup.subgroupOf_mono X h hy
    simpa [π] using (QuotientGroup.eq_one_iff y).mpr this
  have e1 := hbot hB hC hA h1
  have e2 := hbot hC hA hB h2
  have e3 := Subgroup.commutator_commutator_eq_bot_of_rotate e1 e2
  have hAX := hbot (U := A) hA hB hC
  have hgoal : ((⁅⁅A, B⁆, C⁆).subgroupOf X).map π = ⊥ := by
    rw [hmap hA hB hC]
    exact e3
  intro x hx
  have hxX : x ∈ X := hle (hle hA hB) hC hx
  have hmem : (⟨x, hxX⟩ : ↥X) ∈ (⁅⁅A, B⁆, C⁆).subgroupOf X := hx
  have h0 : π ⟨x, hxX⟩ = 1 := by
    have : π ⟨x, hxX⟩ ∈ ((⁅⁅A, B⁆, C⁆).subgroupOf X).map π := ⟨_, hmem, rfl⟩
    rw [hgoal] at this
    exact Subgroup.mem_bot.mp this
  have : (⟨x, hxX⟩ : ↥X) ∈ N.subgroupOf X := (QuotientGroup.eq_one_iff _).mp h0
  exact this

end Perfect

section AutOn

variable {G : Type} [Group G]

@[expose] noncomputable def autOnHom {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G)) :
    ↥L →* ↥(autOn L W) :=
  ((conjAct W).comp (Subgroup.inclusion hLN)).codRestrict (autOn L W) fun l =>
    mem_autOn_iff_exists.mpr ⟨l, hLN l.2, l.2, rfl⟩

theorem autOnHom_coe {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G)) (l : ↥L) :
    ((autOnHom hLN l : ↥(autOn L W)) : MulAut ↥W) = conjAct W ⟨l, hLN l.2⟩ := rfl

theorem autOnHom_eq_one_iff {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (l : ↥L) : autOnHom hLN l = 1 ↔ (l : G) ∈ Subgroup.centralizer (W : Set G) := by
  rw [← Subtype.coe_inj, autOnHom_coe]
  exact A4.conjAct_eq_one_iff

theorem autOnHom_surjective {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G)) :
    Function.Surjective (autOnHom hLN) := by
  rintro ⟨a, ha⟩
  obtain ⟨x, hx, hxL, hxa⟩ := mem_autOn_iff_exists.mp ha
  exact ⟨⟨x, hxL⟩, Subtype.ext (by rw [autOnHom_coe]; exact hxa)⟩

@[expose] noncomputable def autOnQuot {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) :
    ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(autOn L W) :=
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  QuotientGroup.lift _ (autOnHom hLN) fun x hx => by
    rw [MonoidHom.mem_ker, autOnHom_eq_one_iff]
    exact hker ((mem_pCore_iff x).mp hx)

theorem autOnQuot_mk {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) (l : ↥L) :
    autOnQuot hLN hker (QuotientGroup.mk l) = autOnHom hLN l := rfl

theorem autOnQuot_surjective {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) :
    Function.Surjective (autOnQuot hLN hker) := by
  intro y
  obtain ⟨l, rfl⟩ := autOnHom_surjective hLN y
  exact ⟨QuotientGroup.mk l, rfl⟩

theorem exists_autOnQuot_ne_one {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (W : Set G)) : ∃ k, autOnQuot hLN hker k ≠ 1 := by
  have : ∃ l ∈ L, l ∉ Subgroup.centralizer (W : Set G) := by
    by_contra hcon
    exact hnt fun x hx => by_contra fun hx' => hcon ⟨x, hx, hx'⟩
  obtain ⟨l, hl, hl'⟩ := this
  exact ⟨QuotientGroup.mk ⟨l, hl⟩, fun h => hl' ((autOnHom_eq_one_iff hLN ⟨l, hl⟩).mp h)⟩

theorem isQuasisimple_autOn {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (W : Set G)) : CFSG.IsQuasisimple ↥(autOn L W) :=
  CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq (autOnQuot_surjective hLN hker)
    (exists_autOnQuot_ne_one hLN hker hnt)

end AutOn

end CFSG.Quasithin.S153D
