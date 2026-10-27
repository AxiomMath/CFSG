module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec14.Item148StepCases

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148M

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G]

@[expose] noncomputable def centPre148 (A Y J : Subgroup G) [(ker148 A Y).Normal] : Subgroup G :=
  ((Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))).comap
    ((QuotientGroup.mk' (ker148 A Y)).comp
      (Subgroup.inclusion (le_sup_left : Y ≤ Y ⊔ A)))).map Y.subtype

section Basic

variable {A Y J : Subgroup G} [(ker148 A Y).Normal]

theorem mem_centPre148_iff {g : G} :
    g ∈ centPre148 A Y J ↔ ∃ hg : g ∈ Y,
      QuotientGroup.mk' (ker148 A Y) (⟨g, Subgroup.mem_sup_left hg⟩ : ↥(Y ⊔ A)) ∈
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem centPre148_le : centPre148 A Y J ≤ Y :=
  Subgroup.map_subtype_le _

theorem pPrimeCoreOf_le_centPre148 : pPrimeCoreOf 3 Y ≤ centPre148 A Y J := by
  intro g hg
  have hgY : g ∈ Y := pPrimeCoreOf_le 3 Y hg
  refine mem_centPre148_iff.mpr ⟨hgY, ?_⟩
  have h1 : QuotientGroup.mk' (ker148 A Y) (⟨g, Subgroup.mem_sup_left hgY⟩ : ↥(Y ⊔ A)) = 1 :=
    mk'_ker148_eq_one_iff.mpr hg
  rw [h1]
  exact Subgroup.one_mem _

theorem le_normalizer_centPre148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    A ≤ Subgroup.normalizer (centPre148 A Y J : Set G) := by
  have key : ∀ a ∈ A, ∀ g ∈ centPre148 A Y J, a * g * a⁻¹ ∈ centPre148 A Y J := by
    intro a ha g hg
    obtain ⟨hgY, hc⟩ := mem_centPre148_iff.mp hg
    have hgY' : a * g * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hAY ha) g).mp hgY
    refine mem_centPre148_iff.mpr ⟨hgY', Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    obtain ⟨j, hjm, hj, rfl⟩ := mem_img148_iff.mp hx
    have hj' : a⁻¹ * j * a⁻¹⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hAJ (A.inv_mem ha)) j).mp hj
    have hj'm : a⁻¹ * j * a⁻¹⁻¹ ∈ Y ⊔ A := by
      have hmA : a ∈ Y ⊔ A := Subgroup.mem_sup_right ha
      exact (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem hmA) hjm)
        ((Y ⊔ A).inv_mem ((Y ⊔ A).inv_mem hmA))
    have himg : QuotientGroup.mk' (ker148 A Y) (⟨a⁻¹ * j * a⁻¹⁻¹, hj'm⟩ : ↥(Y ⊔ A)) ∈
        img148 A Y J := mem_img148_iff.mpr ⟨_, hj'm, hj', rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hc _ himg
    rw [← map_mul, ← map_mul, mk'_ker148_eq_iff] at hcomm ⊢
    have haN : a ∈ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
      normalizer_le_normalizer_pPrimeCoreOf 3 Y (hAY ha)
    have h2 := (Subgroup.mem_normalizer_iff.mp haN _).mp hcomm
    have e : a * ((↑(⟨a⁻¹ * j * a⁻¹⁻¹, hj'm⟩ * ⟨g, Subgroup.mem_sup_left hgY⟩ : ↥(Y ⊔ A)) :
          G)⁻¹ * ↑(⟨g, Subgroup.mem_sup_left hgY⟩ * ⟨a⁻¹ * j * a⁻¹⁻¹, hj'm⟩ : ↥(Y ⊔ A))) * a⁻¹ =
        (↑(⟨j, hjm⟩ * ⟨a * g * a⁻¹, Subgroup.mem_sup_left hgY'⟩ : ↥(Y ⊔ A)) : G)⁻¹ *
          ↑(⟨a * g * a⁻¹, Subgroup.mem_sup_left hgY'⟩ * ⟨j, hjm⟩ : ↥(Y ⊔ A)) := by
      simp only [Subgroup.coe_mul]
      group
    rwa [e] at h2
  intro a ha
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => key a ha g hg, fun hg => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hg
  simpa [mul_assoc] using this

theorem centPre148_mem_scriptY (hY : Y ∈ scriptY A) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    centPre148 A Y J ∈ scriptY A := by
  refine ⟨fun htop => hY.1 (eq_top_iff.mpr ?_), le_normalizer_centPre148 hY.2 hAJ⟩
  rw [← htop]
  exact centPre148_le

theorem centPre148_ne (hJY : J ≤ Y)
    (hnc : ∃ x ∈ img148 A Y J, ∃ y ∈ img148 A Y J, x * y ≠ y * x) :
    centPre148 A Y J ≠ Y := by
  intro heq
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  apply hxy
  obtain ⟨g, hgm, hgJ, rfl⟩ := mem_img148_iff.mp hx
  have hgC : g ∈ centPre148 A Y J := by
    rw [heq]
    exact hJY hgJ
  obtain ⟨hgY, hc⟩ := mem_centPre148_iff.mp hgC
  exact (Subgroup.mem_centralizer_iff.mp hc y hy).symm

variable [Finite G]

theorem card_centPre148_lt (hJY : J ≤ Y)
    (hnc : ∃ x ∈ img148 A Y J, ∃ y ∈ img148 A Y J, x * y ≠ y * x) :
    Nat.card (centPre148 A Y J) < Nat.card Y := by
  have hle : centPre148 A Y J ≤ Y := centPre148_le
  rcases lt_or_eq_of_le (Subgroup.card_le_of_le hle) with h | h
  · exact h
  · exact absurd (Subgroup.eq_of_le_of_card_ge hle h.ge) (centPre148_ne hJY hnc)

theorem item148At_centPre148
    {LB : Subgroup G → Subgroup G} (hY : Y ∈ scriptY A) (ih : Ind148 A LB Y)
    (hJY : J ≤ Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hnc : ∃ x ∈ img148 A Y J, ∃ y ∈ img148 A Y J, x * y ≠ y * x) :
    Item148At A LB (centPre148 A Y J) (centPre148_mem_scriptY hY hAJ) :=
  ih _ (centPre148_mem_scriptY hY hAJ) (card_centPre148_lt hJY hnc)

theorem exists_ne_comm_of_isPerfect (hp : Group.IsPerfect ↥(img148 A Y J))
    (hnt : img148 A Y J ≠ ⊥) :
    ∃ x ∈ img148 A Y J, ∃ y ∈ img148 A Y J, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hcomm : IsMulCommutative ↥(img148 A Y J) :=
    ⟨⟨fun u v => Subtype.ext (hcon u u.2 v v.2)⟩⟩
  have hs : Subsingleton ↥(img148 A Y J) :=
    Group.IsPerfect.subsingleton_of_isMulCommutative
  apply hnt
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : ↥(img148 A Y J)) = 1 := Subsingleton.elim _ _
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

end Basic

section Core

variable [Finite G] {A Y J : Subgroup G} [(ker148 A Y).Normal]

theorem pPrimeCoreOf_le_pPrimeCoreOf_centPre148 :
    pPrimeCoreOf 3 Y ≤ pPrimeCoreOf 3 (centPre148 A Y J) :=
  le_pPrimeCoreOf pPrimeCoreOf_le_centPre148
    (centPre148_le.trans (le_normalizer_pPrimeCoreOf 3 Y)) (coprime_card_pPrimeCoreOf 3 Y)

theorem centPre148_sup_le : centPre148 A Y J ⊔ A ≤ Y ⊔ A :=
  sup_le_sup_right centPre148_le A

@[expose] noncomputable def compare148 (hcore : pPrimeCoreOf 3 (centPre148 A Y J) ≤ pPrimeCoreOf 3 Y)
    [(ker148 A (centPre148 A Y J)).Normal] :
    ↥(centPre148 A Y J ⊔ A) ⧸ ker148 A (centPre148 A Y J) →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
  QuotientGroup.map (ker148 A (centPre148 A Y J)) (ker148 A Y)
    (Subgroup.inclusion centPre148_sup_le) (by
      intro g hg
      rw [ker148, Subgroup.mem_subgroupOf] at hg
      rw [Subgroup.mem_comap, ker148, Subgroup.mem_subgroupOf]
      exact hcore hg)

theorem compare148_mk (hcore : pPrimeCoreOf 3 (centPre148 A Y J) ≤ pPrimeCoreOf 3 Y)
    [(ker148 A (centPre148 A Y J)).Normal] (g : ↥(centPre148 A Y J ⊔ A)) :
    compare148 hcore (QuotientGroup.mk' (ker148 A (centPre148 A Y J)) g) =
      QuotientGroup.mk' (ker148 A Y) (Subgroup.inclusion centPre148_sup_le g) :=
  rfl

theorem compare148_injective (hcore : pPrimeCoreOf 3 (centPre148 A Y J) = pPrimeCoreOf 3 Y)
    [(ker148 A (centPre148 A Y J)).Normal] : Function.Injective (compare148 hcore.le) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [MonoidHom.mem_ker] at hx
    change compare148 hcore.le (QuotientGroup.mk' _ g) = 1 at hx
    rw [compare148_mk, mk'_ker148_eq_one_iff] at hx
    rw [Subgroup.mem_bot]
    change QuotientGroup.mk' (ker148 A (centPre148 A Y J)) g = 1
    rw [mk'_ker148_eq_one_iff, hcore]
    exact hx

theorem map_img148_compare148 (hcore : pPrimeCoreOf 3 (centPre148 A Y J) ≤ pPrimeCoreOf 3 Y)
    [(ker148 A (centPre148 A Y J)).Normal] {X : Subgroup G} (hX : X ≤ centPre148 A Y J ⊔ A) :
    (img148 A (centPre148 A Y J) X).map (compare148 hcore) = img148 A Y X := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨g, hg, hgX, rfl⟩ := mem_img148_iff.mp hu
    rw [compare148_mk]
    exact mem_img148_iff.mpr ⟨g, centPre148_sup_le hg, hgX, rfl⟩
  · intro hx
    obtain ⟨g, hg, hgX, rfl⟩ := mem_img148_iff.mp hx
    refine ⟨QuotientGroup.mk' _ ⟨g, hX hgX⟩, mem_img148_iff.mpr ⟨g, hX hgX, hgX, rfl⟩, ?_⟩
    rw [compare148_mk]
    rfl

theorem nonempty_img148_centPre148_equiv
    (hcore : pPrimeCoreOf 3 (centPre148 A Y J) = pPrimeCoreOf 3 Y)
    [(ker148 A (centPre148 A Y J)).Normal] {X : Subgroup G} (hX : X ≤ centPre148 A Y J ⊔ A) :
    Nonempty (↥(img148 A (centPre148 A Y J) X) ≃* ↥(img148 A Y X)) := by
  refine ⟨(Subgroup.equivMapOfInjective _ _ (compare148_injective hcore)).trans
    (MulEquiv.subgroupCongr (map_img148_compare148 hcore.le hX))⟩

theorem img148_deltaZero_centPre148_le {LB : Subgroup G → Subgroup G} :
    img148 A Y (deltaZero A LB (centPre148 A Y J)) ≤
      img148 A Y (deltaZero A LB Y) ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  refine le_inf (img148_mono (deltaZero_mono148 centPre148_le)) ?_
  intro x hx
  obtain ⟨g, hg, hgX, rfl⟩ := mem_img148_iff.mp hx
  have hle : deltaZero A LB (centPre148 A Y J) ≤ centPre148 A Y J := sSup_le fun _ hQ => hQ.2
  have hgC : g ∈ centPre148 A Y J := hle hgX
  obtain ⟨hgY, hc⟩ := mem_centPre148_iff.mp hgC
  exact hc

end Core

end CFSG.RankThree.PartTwo.Sec14.Ronan148M
