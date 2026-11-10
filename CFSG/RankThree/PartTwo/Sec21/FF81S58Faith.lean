module

public import CFSG.RankThree.PartTwo.Sec21.FF81S58Hom

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79

abbrev CommCenP {G : Type} [Group G] (T : Subgroup G) (x : G) : Prop :=
  ∀ u ∈ T, x * u * x⁻¹ * u⁻¹ ∈ T ⊓ CenS T

theorem inv_conj_mem_of_mem_nor {G : Type} [Group G] {T : Subgroup G} {g : G} (hg : g ∈ Nor T)
    {u : G} (hu : u ∈ T) : g⁻¹ * u * g ∈ T := by
  refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * u * g)).mpr ?_
  rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group]
  exact hu

theorem conj_mem_inf_cenS {G : Type} [Group G] {T : Subgroup G} {g : G} (hg : g ∈ Nor T)
    {z : G} (hz : z ∈ T ⊓ CenS T) : g * z * g⁻¹ ∈ T ⊓ CenS T := by
  obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzT, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
  have ht' : g⁻¹ * t * g ∈ T := inv_conj_mem_of_mem_nor hg (SetLike.mem_coe.mp ht)
  have hc := Subgroup.mem_centralizer_iff.mp hzC (g⁻¹ * t * g) ht'
  calc t * (g * z * g⁻¹) = g * (g⁻¹ * t * g * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * t := by group

theorem commPred_one {G : Type} [Group G] {T : Subgroup G} : CommCenP T 1 := by
  intro u _
  simp

theorem commPred_mul {G : Type} [Group G] {T : Subgroup G} {a b : G} (ha : a ∈ Nor T)
    (hPa : CommCenP T a) (hPb : CommCenP T b) : CommCenP T (a * b) := by
  intro u hu
  have h1 := conj_mem_inf_cenS ha (hPb u hu)
  have h2 := (T ⊓ CenS T).mul_mem h1 (hPa u hu)
  have e : a * b * u * (a * b)⁻¹ * u⁻¹ =
      a * (b * u * b⁻¹ * u⁻¹) * a⁻¹ * (a * u * a⁻¹ * u⁻¹) := by group
  rw [e]
  exact h2

theorem commPred_inv {G : Type} [Group G] {T : Subgroup G} {a : G} (ha : a ∈ Nor T)
    (hPa : CommCenP T a) : CommCenP T a⁻¹ := by
  intro u hu
  have h1 := (T ⊓ CenS T).inv_mem (hPa _ (inv_conj_mem_of_mem_nor ha hu))
  have e : a⁻¹ * u * a⁻¹⁻¹ * u⁻¹ =
      (a * (a⁻¹ * u * a) * a⁻¹ * (a⁻¹ * u * a)⁻¹)⁻¹ := by group
  rw [e]
  exact h1

theorem commPred_conj {G : Type} [Group G] {T : Subgroup G} {g n : G} (hg : g ∈ Nor T)
    (hn : CommCenP T n) : CommCenP T (g * n * g⁻¹) := by
  intro u hu
  have h1 := conj_mem_inf_cenS hg (hn _ (inv_conj_mem_of_mem_nor hg hu))
  have e : g * n * g⁻¹ * u * (g * n * g⁻¹)⁻¹ * u⁻¹ =
      g * (n * (g⁻¹ * u * g) * n⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact h1

@[expose] def commCenSub {G : Type} [Group G] {L T : Subgroup G} (hLN : L ≤ Nor T) :
    Subgroup ↥L where
  carrier := {l | CommCenP T (l : G)}
  mul_mem' {a b} ha hb := by
    have ha' : CommCenP T (a : G) := ha
    have hb' : CommCenP T (b : G) := hb
    exact commPred_mul (hLN a.2) ha' hb'
  one_mem' := (commPred_one : CommCenP T 1)
  inv_mem' {a} ha := by
    have ha' : CommCenP T (a : G) := ha
    exact commPred_inv (hLN a.2) ha'

theorem commCenSub_normal {G : Type} [Group G] {L T : Subgroup G} (hLN : L ≤ Nor T) :
    (commCenSub hLN).Normal :=
  ⟨fun n hn g => by
    have hn' : CommCenP T (n : G) := hn
    have h := commPred_conj (hLN g.2) hn'
    exact h⟩

theorem eq_one_of_comm_center {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    [IsSimpleGroup L] (hLN : L ≤ Nor T) {b : G} (hb : b ∈ L)
    (hcard : Nat.card ↥(T ⊓ Cen b) * Nat.card ↥(T ⊓ CenS T) < Nat.card T) :
    ∀ l ∈ L, (∀ u ∈ T, l * u * l⁻¹ * u⁻¹ ∈ T ⊓ CenS T) → l = 1 := by
  intro l hl hcomm
  haveI := commCenSub_normal hLN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commCenSub hLN) with h0 | h0
  · have hmem : (⟨l, hl⟩ : ↥L) ∈ commCenSub hLN := hcomm
    rw [h0, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hmem : (⟨b, hb⟩ : ↥L) ∈ commCenSub hLN := by
      rw [h0]
      exact Subgroup.mem_top _
    have hb' : ∀ u ∈ T, b * u * b⁻¹ * u⁻¹ ∈ T ⊓ CenS T := hmem
    exact (not_le.mpr hcard) (card_le_card_cen_mul_card_center hb')

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
