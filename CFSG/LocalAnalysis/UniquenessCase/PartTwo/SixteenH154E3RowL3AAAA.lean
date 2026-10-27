module

public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.B5Sec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {W : Type} [CommGroup W]

def s16h_sameSizeOrbits {α : Type*} [Group α] (G : Subgroup (MulAut α)) (a : α) : Set (Set α) :=
  {O | ∃ b : α, O = MulAction.orbit G b ∧ Nat.card O = Nat.card (MulAction.orbit G a)}

private theorem s16h_card_dvd_of_free {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : X, g • x ≠ x) : Nat.card G ∣ Nat.card X := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype X := Fintype.ofFinite X
  have hsum := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have hfixed : ∀ g : G, Fintype.card (MulAction.fixedBy X g) =
      if g = 1 then Fintype.card X else 0 := by
    intro g
    by_cases hg : g = 1
    · subst hg
      rw [if_pos rfl]
      have hone : MulAction.fixedBy X (1 : G) = Set.univ := by
        ext x
        simp [MulAction.mem_fixedBy]
      exact Fintype.card_congr ((Set.equivOfEq hone).trans (Equiv.Set.univ X))
    · rw [if_neg hg]
      have hempty : MulAction.fixedBy X g = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hfree g hg x ((MulAction.mem_fixedBy).mp hx)).elim
        · intro hx
          simp at hx
      haveI : IsEmpty ↥(MulAction.fixedBy X g) := by
        refine ⟨fun x => ?_⟩
        have hx : (x : X) ∈ (∅ : Set X) := hempty ▸ x.2
        simpa using hx
      exact Fintype.card_eq_zero_iff.mpr inferInstance
  rw [Finset.sum_congr rfl (fun g _ => hfixed g)] at hsum
  rw [Finset.sum_ite_eq' Finset.univ (1 : G) (fun _ => Fintype.card X)] at hsum
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp only [Finset.mem_univ, if_true] at hsum
  exact ⟨_, by rw [hsum, mul_comm]⟩

private def s16h_secIncl (Z I U : Subgroup W) (hIU : I ≤ U) : Sec I Z →* Sec U Z :=
  QuotientGroup.quotientMapSubgroupOfOfLe (le_refl Z) hIU

private theorem s16h_secIncl_mk (Z I U : Subgroup W) (hIU : I ≤ U) (x : ↥I) :
    s16h_secIncl Z I U hIU (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion hIU x) :=
  rfl

private theorem s16h_secIncl_injective (Z I U : Subgroup W) (hIU : I ≤ U) :
    Function.Injective (s16h_secIncl Z I U hIU) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [MonoidHom.mem_ker, s16h_secIncl_mk] at hx
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    have h1 := (QuotientGroup.eq_one_iff (Subgroup.inclusion hIU a)).mp hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h1)

private theorem s16h_secIncl_range (Z I U : Subgroup W) (hIU : I ≤ U) :
    (s16h_secIncl Z I U hIU).range =
      (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using QuotientGroup.induction_on with
    | H a =>
      rw [s16h_secIncl_mk]
      exact Subgroup.mem_map.mpr
        ⟨Subgroup.inclusion hIU a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨QuotientGroup.mk ⟨u, Subgroup.mem_subgroupOf.mp hu⟩, ?_⟩
    rw [s16h_secIncl_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)

private theorem s16h_secIncl_secHom {L : Subgroup (MulAut W)} (Z I U : Subgroup W) (hIU : I ≤ U)
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hLU : L ≤ stabSub U) (a : ↥L)
    (x : Sec I Z) :
    s16h_secIncl Z I U hIU (CFSG.Quasithin.B5.secHom L hLI hLZ a x) =
      CFSG.Quasithin.B5.secHom L hLU hLZ a (s16h_secIncl Z I U hIU x) := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [s16h_secIncl_mk, CFSG.Quasithin.B5.secHom_mk, CFSG.Quasithin.B5.secHom_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)

private theorem s16h_mem_autSec_range {L : Subgroup (MulAut W)} {Z U : Subgroup W}
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) {g : MulAut (Sec U Z)} :
    g ∈ autSec L U Z ↔ ∃ a : ↥L, CFSG.Quasithin.B5.secHom L hLU hLZ a = g := by
  rw [← CFSG.Quasithin.B5.map_secHom_eq_autSec L hLU hLZ (le_refl L),
    Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.mem_range]

private theorem s16h_secIncl_image_stable {L : Subgroup (MulAut W)} (Z I U : Subgroup W)
    (hIU : I ≤ U) (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hLU : L ≤ stabSub U) :
    ∀ g ∈ autSec L U Z, ∀ x ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)),
      g x ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  intro g hg x hx
  obtain ⟨a, rfl⟩ := (s16h_mem_autSec_range hLU hLZ).mp hg
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  have huI : (u : W) ∈ I := Subgroup.mem_subgroupOf.mp hu
  have haU : (a : MulAut W) (u : W) ∈ U := (hLU a.2 (u : W)).2 u.2
  have haI : (a : MulAut W) (u : W) ∈ I := (hLI a.2 (u : W)).2 huI
  rw [show QuotientGroup.mk' (Z.subgroupOf U) u = QuotientGroup.mk u from rfl,
    CFSG.Quasithin.B5.secHom_mk]
  exact Subgroup.mem_map.mpr ⟨⟨_, haU⟩, Subgroup.mem_subgroupOf.mpr haI, rfl⟩

private theorem s16h_card_sec_of_l3Data [Finite W] {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) :
    Nat.card (Sec I Z) = 8 := by
  classical
  have hβ := Subgroup.card_ker_mul_card_range D.β
  have hker : D.β.ker = Z.subgroupOf I := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact D.ker_β u
  have hkerCard : Nat.card ↥D.β.ker = Nat.card ↥Z := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv
  have hrange : D.β.range = ⊤ := MonoidHom.range_eq_top.mpr D.β_surj
  have hrangeCard : Nat.card ↥D.β.range = 8 := by
    rw [hrange, Subgroup.card_top]
    exact CFSG.Quasithin.L3Data.card_vec
  have hI : Nat.card ↥I = Nat.card ↥Z * 8 := by
    rw [hkerCard, hrangeCard] at hβ
    exact hβ.symm
  have hsec := CFSG.Quasithin.card_sec_mul (V := W) (W := I) (U := Z) hZI
  have hpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hmain : Nat.card (Sec I Z) * Nat.card ↥Z = 8 * Nat.card ↥Z := by
    rw [hsec, hI]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos hmain

private noncomputable def s16h_secEquivOfL3Data [Finite W] {L : Subgroup (MulAut W)}
    {I Z : Subgroup W} (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) :
    Sec I Z ≃* Multiplicative CFSG.Quasithin.L3.Vec := by
  classical
  have hker : Z.subgroupOf I ≤ D.β.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    exact (D.ker_β u).mpr (Subgroup.mem_subgroupOf.mp hu)
  let κ : Sec I Z →* Multiplicative CFSG.Quasithin.L3.Vec :=
    QuotientGroup.lift (Z.subgroupOf I) D.β hker
  have hκmk : ∀ u : ↥I, κ (QuotientGroup.mk u) = D.β u := fun u => rfl
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [hκmk] at hx
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr ((D.ker_β u).mp hx)
  have hκsurj : Function.Surjective κ := by
    intro y
    obtain ⟨u, hu⟩ := D.β_surj y
    exact ⟨QuotientGroup.mk u, by rw [hκmk, hu]⟩
  exact MulEquiv.ofBijective κ ⟨hκinj, hκsurj⟩

private theorem s16h_secEquivOfL3Data_mk [Finite W] {L : Subgroup (MulAut W)}
    {I Z : Subgroup W} (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (u : ↥I) :
    s16h_secEquivOfL3Data D hZI (QuotientGroup.mk u) = D.β u := by
  unfold s16h_secEquivOfL3Data
  rfl

private theorem s16h_secEquivOfL3Data_secHom [Finite W] {L : Subgroup (MulAut W)}
    {I Z : Subgroup W} (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (hLI : L ≤ stabSub I)
    (hLZ : L ≤ stabSub Z) {δ : CFSG.Quasithin.L3.Γ} (x : Sec I Z) :
    s16h_secEquivOfL3Data D hZI
        (CFSG.Quasithin.B5.secHom L hLI hLZ (D.π δ) x) =
      Multiplicative.ofAdd (CFSG.Quasithin.L3.act δ
        (Multiplicative.toAdd (s16h_secEquivOfL3Data D hZI x))) := by
  classical
  induction x using QuotientGroup.induction_on with
  | H u =>
    have hu : ((D.π δ : ↥L) : MulAut W) (u : W) ∈ I :=
      D.inv_U (D.π δ) (D.π δ).2 u u.2
    have h1 := D.equi δ u hu
    rw [CFSG.Quasithin.B5.secHom_mk]
    rw [s16h_secEquivOfL3Data_mk D hZI, s16h_secEquivOfL3Data_mk D hZI]
    exact h1

private def s16h_img (Z I U : Subgroup W) : Subgroup (Sec U Z) :=
  Subgroup.map (QuotientGroup.mk' (Z.subgroupOf U)) (I.subgroupOf U)

private theorem s16h_iSup_fin_two {α : Type*} [CompleteLattice α] (f : Fin 2 → α) :
    (⨆ i, f i) = f 0 ⊔ f 1 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i <;> simp
  · exact sup_le (le_iSup _ _) (le_iSup _ _)

private theorem s16h_iSup_ne_zero {α : Type*} [CompleteLattice α] (f : Fin 2 → α) :
    (⨆ (j : Fin 2) (_ : j ≠ 0), f j) = f 1 := by
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun hj => ?_
    have hj1 : j = 1 := by fin_cases j <;> simp_all
    rw [hj1]
  · exact le_iSup_of_le 1 (le_iSup_of_le (by norm_num) le_rfl)

private theorem s16h_img_inf_eq_bot [Finite W] {Z I J U : Subgroup W}
    (hZI : Z ≤ I) (hZJ : Z ≤ J) (hIU : I ≤ U) (hJU : J ≤ U) (hinf : I ⊓ J ≤ Z) :
    s16h_img Z I U ⊓ s16h_img Z J U = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxI, hxJ⟩ := hx
  rw [s16h_img] at hxI hxJ
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxI
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hxJ
  rw [Subgroup.mem_bot]
  have huI : (u : W) ∈ I := Subgroup.mem_subgroupOf.mp hu
  have hvJ : (v : W) ∈ J := Subgroup.mem_subgroupOf.mp hv
  have hzu : (u : W) ∈ Z := by
    have h1 : (v * u⁻¹ : ↥U) ∈ Z.subgroupOf U := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' (Z.subgroupOf U) (v * u⁻¹) = 1
      rw [map_mul, map_inv, hvu, mul_inv_cancel]
    have hz : ((v * u⁻¹ : ↥U) : W) ∈ Z := Subgroup.mem_subgroupOf.mp h1
    have hmemJ : (u : W) ∈ J := by
      have h2 : (((v * u⁻¹ : ↥U) : W))⁻¹ ∈ Z := Z.inv_mem hz
      have h3 : (((v * u⁻¹ : ↥U) : W))⁻¹ * (v : W) = (u : W) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [← h3]
      exact mul_mem (hZJ h2) hvJ
    exact hinf ⟨huI, hmemJ⟩
  exact (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr hzu)

private theorem s16h_img_sup_eq_top [Finite W] {Z I J U : Subgroup W}
    (hIU : I ≤ U) (hJU : J ≤ U) (hIJ : I ⊔ J = U) :
    s16h_img Z I U ⊔ s16h_img Z J U = ⊤ := by
  rw [s16h_img, s16h_img, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hIU hJU, hIJ,
    Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective (N := Z.subgroupOf U))

private theorem s16h_img_card [Finite W] {L : Subgroup (MulAut W)} {Z I U : Subgroup W}
    (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (hIU : I ≤ U) :
    Nat.card ↥(s16h_img Z I U) = 8 := by
  have hinj := s16h_secIncl_injective Z I U hIU
  have hrange := s16h_secIncl_range Z I U hIU
  let e : Sec I Z ≃ ↥(s16h_img Z I U) := Equiv.ofBijective
    (fun x => ⟨s16h_secIncl Z I U hIU x, by
      rw [show s16h_img Z I U = (s16h_secIncl Z I U hIU).range from hrange.symm]
      exact ⟨x, rfl⟩⟩)
    ⟨fun x y h => hinj (Subtype.ext_iff.mp h), fun y => by
      have hy : (y : Sec U Z) ∈ (s16h_secIncl Z I U hIU).range := by
        rw [hrange]
        exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩
  rw [← Nat.card_congr e]
  exact s16h_card_sec_of_l3Data D hZI

private structure s16h_Proj {Q : Type} [CommGroup Q] {k : ℕ} (I : Fin k → Subgroup Q)
    (Λ : Subgroup (MulAut Q)) where
  e : Fin k → Q →* Q
  e_mem : ∀ i x, e i x ∈ I i
  e_self : ∀ i x (hx : x ∈ I i), e i x = x
  e_other : ∀ i j, j ≠ i → ∀ x (hx : x ∈ I j), e i x = 1
  e_prod : ∀ x, ∏ i, e i x = x
  e_equiv : ∀ i, ∀ g ∈ Λ, ∀ x, e i (g x) = g (e i x)

private noncomputable def s16h_mkProj {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hspan : ⨆ i, I i = ⊤)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) :
    s16h_Proj I Λ := by
  classical
  have hcomm : Pairwise fun i j : Fin k => ∀ x y : Q, x ∈ I i → y ∈ I j → Commute x y :=
    fun i j _ x y _ _ => mul_comm x y
  let φ : (∀ i : Fin k, I i) →* Q := Subgroup.noncommPiCoprod hcomm
  have hInd : iSupIndep I := iSupIndep_def.mpr (fun i => disjoint_iff.mpr (hind i))
  have hφinj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hInd
  have hφrange : φ.range = ⊤ := by
    rw [Subgroup.noncommPiCoprod_range, hspan]
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hφrange
  let e : (∀ i : Fin k, I i) ≃* Q := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hφprod : ∀ f : (∀ i : Fin k, I i), φ f = ∏ i, (f i : Q) := by
    intro f
    rw [Subgroup.noncommPiCoprod_apply]
    exact Finset.noncommProd_eq_prod _ _
  let ei (i : Fin k) : Q →* I i :=
    (Pi.evalMonoidHom (fun j => I j) i).comp e.symm.toMonoidHom
  let eQ (i : Fin k) : Q →* Q := (I i).subtype.comp (ei i)
  have hmul : ∀ (i : Fin k) (x : Q) (hx : x ∈ I i), e.symm x = Pi.mulSingle i ⟨x, hx⟩ := by
    intro i x hx
    apply e.injective
    rw [e.apply_symm_apply]
    change x = φ (Pi.mulSingle i ⟨x, hx⟩)
    rw [Subgroup.noncommPiCoprod_mulSingle]
  have hself : ∀ (i : Fin k) (x : Q) (hx : x ∈ I i), eQ i x = x := by
    intro i x hx
    change (I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm x)) = x
    rw [hmul i x hx]
    simp
  have hother : ∀ (i j : Fin k), j ≠ i → ∀ (x : Q) (hx : x ∈ I j), eQ i x = 1 := by
    intro i j hij x hx
    change (I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm x)) = 1
    rw [hmul j x hx]
    simp [Pi.mulSingle_eq_of_ne (Ne.symm hij)]
  have hequiv : ∀ (i : Fin k) (g : MulAut Q), g ∈ Λ → ∀ x, eQ i (g x) = g (eQ i x) := by
    intro i g hg x
    have hgPi : ∀ f : (∀ j : Fin k, I j),
        φ (fun j => ⟨g (f j : Q), hstab j g hg (f j : Q) (f j).2⟩) = g (φ f) := by
      intro f
      rw [hφprod, hφprod]
      exact (map_prod (g : Q →* Q) (fun j => (f j : Q)) Finset.univ).symm
    have hsymm : e.symm (g x) =
        fun j => ⟨g ((e.symm x) j : Q), hstab j g hg ((e.symm x) j : Q) ((e.symm x j).2)⟩ := by
      apply e.injective
      rw [e.apply_symm_apply]
      change g x = φ (fun j => ⟨g ((e.symm x) j : Q),
        hstab j g hg ((e.symm x) j : Q) ((e.symm x j).2)⟩)
      rw [hgPi]
      have h2 : φ (e.symm x) = x := e.apply_symm_apply x
      rw [h2]
    change (I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm (g x))) =
      g ((I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm x)))
    rw [hsymm]
    rfl
  have hprod : ∀ x : Q, ∏ i : Fin k, eQ i x = x := by
    intro x
    have h : φ (e.symm x) = x := e.apply_symm_apply x
    rw [hφprod] at h
    simpa [eQ, ei] using h
  exact { e := eQ
          e_mem := fun i x => (ei i x).2
          e_self := hself
          e_other := hother
          e_prod := hprod
          e_equiv := hequiv }

private theorem s16h_eq_of_mul_eq_mul {Q : Type*} [CommGroup Q] {A B : Subgroup Q}
    (hinf : A ⊓ B = ⊥) {a a' b b' : Q} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hA : a'⁻¹ * a ∈ A := mul_mem (A.inv_mem ha') ha
  have hB : b' * b⁻¹ ∈ B := mul_mem hb' (B.inv_mem hb)
  have hbot : a'⁻¹ * a ∈ (⊥ : Subgroup Q) := by
    rw [← hinf]
    exact ⟨hA, h1 ▸ hB⟩
  have h2 : a'⁻¹ * a = 1 := Subgroup.mem_bot.mp hbot
  have haeq : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' * 1 := by rw [h2]
      _ = a' := mul_one _
  have hbeq : b = b' := mul_left_cancel (by rw [← h, haeq])
  exact ⟨haeq, hbeq⟩

private theorem s16h_e3_trans [Finite W] {L : Subgroup (MulAut W)} {I Z U : Subgroup W}
    (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (hIU : I ≤ U)
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hLU : L ≤ stabSub U)
    {x y : Sec U Z} (hx : x ∈ s16h_img Z I U) (hx1 : x ≠ 1)
    (hy : y ∈ s16h_img Z I U) (hy1 : y ≠ 1) :
    ∃ g : MulAut (Sec U Z), g ∈ autSec L U Z ∧ g x = y := by
  have hxr : x ∈ (s16h_secIncl Z I U hIU).range := by
    rw [s16h_secIncl_range]; exact hx
  have hyr : y ∈ (s16h_secIncl Z I U hIU).range := by
    rw [s16h_secIncl_range]; exact hy
  obtain ⟨xx, rfl⟩ := MonoidHom.mem_range.mp hxr
  obtain ⟨yy, hyy⟩ := MonoidHom.mem_range.mp hyr
  have hmap1 : s16h_secIncl Z I U hIU (1 : Sec I Z) = 1 := map_one _
  have hxx1 : xx ≠ 1 := fun h => hx1 (by rw [h, hmap1])
  have hyy1 : yy ≠ 1 := fun h => hy1 (by rw [← hyy, h, hmap1])
  let e := s16h_secEquivOfL3Data D hZI
  have he1 : e (1 : Sec I Z) = 1 := map_one e
  have hα0 : Multiplicative.toAdd (e xx) ≠ 0 := by
    intro h
    apply hxx1
    apply e.injective
    rw [he1]
    have h' : Multiplicative.ofAdd (Multiplicative.toAdd (e xx)) = Multiplicative.ofAdd 0 := by
      rw [h]
    simpa using h'
  have hβ0 : Multiplicative.toAdd (e yy) ≠ 0 := by
    intro h
    apply hyy1
    apply e.injective
    rw [he1]
    have h' : Multiplicative.ofAdd (Multiplicative.toAdd (e yy)) = Multiplicative.ofAdd 0 := by
      rw [h]
    simpa using h'
  obtain ⟨δ, hδ⟩ := CFSG.Quasithin.L3.act_trans (Multiplicative.toAdd (e xx))
    (Multiplicative.toAdd (e yy)) hα0 hβ0
  refine ⟨CFSG.Quasithin.B5.secHom L hLU hLZ (D.π δ),
    (s16h_mem_autSec_range hLU hLZ).mpr ⟨D.π δ, rfl⟩, ?_⟩
  rw [← hyy, ← s16h_secIncl_secHom Z I U hIU hLI hLZ hLU (D.π δ) xx]
  congr 1
  apply e.injective
  rw [s16h_secEquivOfL3Data_secHom D hZI hLI hLZ (δ := δ) xx, hδ]
  simp

private theorem s16h_e3_l_eq_one [Finite W] {L : Subgroup (MulAut W)} {I Z U : Subgroup W}
    (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (hIU : I ≤ U)
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hLU : L ≤ stabSub U) {l : ↥L}
    (hfix : ∀ x ∈ s16h_img Z I U, CFSG.Quasithin.B5.secHom L hLU hLZ l x = x) : l = 1 := by
  have hfixl : ∀ y : Sec I Z, CFSG.Quasithin.B5.secHom L hLI hLZ l y = y := by
    intro y
    apply s16h_secIncl_injective Z I U hIU
    rw [s16h_secIncl_secHom Z I U hIU hLI hLZ hLU l y]
    exact hfix (s16h_secIncl Z I U hIU y)
      (by rw [s16h_img, ← s16h_secIncl_range Z I U hIU]; exact ⟨y, rfl⟩)
  obtain ⟨δ, hδ⟩ := D.π_surj l
  let e := s16h_secEquivOfL3Data D hZI
  have hact : ∀ v : CFSG.Quasithin.L3.Vec, CFSG.Quasithin.L3.act δ v = v := by
    intro v
    obtain ⟨y, hy⟩ := e.surjective (Multiplicative.ofAdd v)
    have h1 : e (CFSG.Quasithin.B5.secHom L hLI hLZ (D.π δ) y) = e y := by
      rw [hδ, hfixl y]
    rw [s16h_secEquivOfL3Data_secHom D hZI hLI hLZ (δ := δ) y] at h1
    have h2 : Multiplicative.toAdd (e y) = v := by
      have := congrArg Multiplicative.toAdd hy
      simpa using this
    have h3 := congrArg Multiplicative.toAdd h1
    rw [h2] at h3
    simpa using h3
  have hδ1 : δ = 1 := CFSG.Quasithin.L3.act_injective δ hact
  rw [← hδ, hδ1, map_one]

private theorem s16h_e3_faithful [Finite W] {L : Subgroup (MulAut W)} {I Z U : Subgroup W}
    (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (hIU : I ≤ U)
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hLU : L ≤ stabSub U)
    {g : MulAut (Sec U Z)} (hg : g ∈ autSec L U Z)
    (hfix : ∀ x ∈ s16h_img Z I U, g x = x) : g = 1 := by
  obtain ⟨l, hl⟩ := (s16h_mem_autSec_range hLU hLZ).mp hg
  have hfixl : ∀ x ∈ s16h_img Z I U, CFSG.Quasithin.B5.secHom L hLU hLZ l x = x := by
    intro x hx
    rw [hl]
    exact hfix x hx
  rw [← hl, s16h_e3_l_eq_one D hZI hIU hLI hLZ hLU hfixl]
  exact map_one _

private theorem s16h_e3_G_card [Finite W] {L : Subgroup (MulAut W)} {I Z U : Subgroup W}
    (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (hIU : I ≤ U)
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hLU : L ≤ stabSub U)
    (hLcard : Nat.card ↥L = 168) :
    Nat.card ↥(autSec L U Z) = 168 := by
  have hinj : Function.Injective (CFSG.Quasithin.B5.secHom L hLU hLZ) := by
    rw [injective_iff_map_eq_one]
    intro l hl
    exact s16h_e3_l_eq_one D hZI hIU hLI hLZ hLU (l := l) (fun x _ => by rw [hl]; rfl)
  have hrange : (CFSG.Quasithin.B5.secHom L hLU hLZ).range = autSec L U Z :=
    CFSG.Quasithin.B5.range_secHom L hLU hLZ
  calc Nat.card ↥(autSec L U Z)
      = Nat.card ↥(CFSG.Quasithin.B5.secHom L hLU hLZ).range := by rw [hrange]
    _ = Nat.card ↥L := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    _ = 168 := hLcard

private theorem s16h_e3_Phi_card {Q : Type} [CommGroup Q] [Finite Q] {G : Subgroup (MulAut Q)}
    {A B : Subgroup Q} (hinf : A ⊓ B = ⊥)
    (hGA : ∀ g ∈ G, ∀ x ∈ A, g x ∈ A) (hGB : ∀ g ∈ G, ∀ x ∈ B, g x ∈ B)
    (a : Q) (ha : a ∈ A) (hGod : Nat.card (MulAction.orbit G a) = 7)
    (hHcard : Nat.card ↥(MulAction.stabilizer G a) = 24) (b : Q) (hb : b ∈ B) :
    Nat.card (MulAction.orbit G (a * b)) =
      7 * Nat.card (MulAction.orbit (MulAction.stabilizer G a) b) := by
  have hstab : MulAction.stabilizer G (a * b) =
      MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      have h1 : (g : MulAut Q) (a * b) = a * b := hg
      rw [map_mul] at h1
      exact s16h_eq_of_mul_eq_mul hinf (hGA _ g.2 a ha) ha (hGB _ g.2 b hb) hb h1
    · rintro ⟨hga, hgb⟩
      have hga' : (g : MulAut Q) a = a := hga
      have hgb' : (g : MulAut Q) b = b := hgb
      have h1 : (g : MulAut Q) (a * b) = a * b := by rw [map_mul, hga', hgb']
      exact h1
  have hstabH : MulAction.stabilizer (MulAction.stabilizer G a) b =
      (MulAction.stabilizer G b).subgroupOf (MulAction.stabilizer G a) := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rfl
  have hKleH : MulAction.stabilizer G (a * b) ≤ MulAction.stabilizer G a := by
    rw [hstab]; exact inf_le_left
  have hcardStabH : Nat.card ↥(MulAction.stabilizer (MulAction.stabilizer G a) b) =
      Nat.card ↥(MulAction.stabilizer G (a * b)) := by
    rw [hstabH, ← inf_subgroupOf_left (MulAction.stabilizer G b) (MulAction.stabilizer G a),
      ← hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleH).toEquiv
  have hG : Nat.card (MulAction.orbit G (a * b)) *
      Nat.card ↥(MulAction.stabilizer G (a * b)) = Nat.card ↥G := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (G := G) (a * b))
  have hGa : Nat.card (MulAction.orbit G a) * Nat.card ↥(MulAction.stabilizer G a) =
      Nat.card ↥G := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (G := G) a)
  have hH : Nat.card (MulAction.orbit (MulAction.stabilizer G a) b) *
      Nat.card ↥(MulAction.stabilizer (MulAction.stabilizer G a) b) =
      Nat.card ↥(MulAction.stabilizer G a) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr
      (MulAction.orbitProdStabilizerEquivGroup (G := MulAction.stabilizer G a) b)
  have hmain : Nat.card (MulAction.orbit G (a * b)) *
      Nat.card ↥(MulAction.stabilizer (MulAction.stabilizer G a) b) =
      7 * Nat.card (MulAction.orbit (MulAction.stabilizer G a) b) *
        Nat.card ↥(MulAction.stabilizer (MulAction.stabilizer G a) b) := by
    calc Nat.card (MulAction.orbit G (a * b)) *
          Nat.card ↥(MulAction.stabilizer (MulAction.stabilizer G a) b)
        = Nat.card (MulAction.orbit G (a * b)) *
            Nat.card ↥(MulAction.stabilizer G (a * b)) := by rw [hcardStabH]
      _ = Nat.card ↥G := hG
      _ = Nat.card (MulAction.orbit G a) * Nat.card ↥(MulAction.stabilizer G a) := hGa.symm
      _ = 7 * Nat.card ↥(MulAction.stabilizer G a) := by rw [hGod]
      _ = 7 * (Nat.card (MulAction.orbit (MulAction.stabilizer G a) b) *
            Nat.card ↥(MulAction.stabilizer (MulAction.stabilizer G a) b)) := by rw [hH]
      _ = 7 * Nat.card (MulAction.orbit (MulAction.stabilizer G a) b) *
            Nat.card ↥(MulAction.stabilizer (MulAction.stabilizer G a) b) := by ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmain

private theorem s16h_e3_fix_single_le_two {Q : Type*} [CommGroup Q] [Finite Q]
    {G : Subgroup (MulAut Q)} {B : Subgroup Q} (hBcard : Nat.card ↥B = 8)
    (hGB : ∀ g ∈ G, ∀ x ∈ B, g x ∈ B)
    (hfaithB : ∀ g ∈ G, (∀ x ∈ B, g x = x) → g = 1)
    {h : MulAut Q} (hhG : h ∈ G) (hh3 : orderOf h = 3) :
    Nat.card {x : Q // x ∈ B ∧ h x = x} ≤ 2 := by
  classical
  haveI : Fintype ↥B := Fintype.ofFinite ↥B
  let F : Subgroup Q :=
    B ⊓ { carrier := {x | h x = x}
          one_mem' := by simp
          mul_mem' := by intro a b ha hb; show h (a * b) = a * b; rw [map_mul, ha, hb]
          inv_mem' := by intro a ha; show h a⁻¹ = a⁻¹; rw [map_inv, ha] }
  let EF : {x : Q // x ∈ B ∧ h x = x} ≃ ↥F :=
    { toFun := fun x => ⟨x.1, Subgroup.mem_inf.mpr ⟨x.2.1, x.2.2⟩⟩
      invFun := fun x => ⟨x.1, (Subgroup.mem_inf.mp x.2).1, (Subgroup.mem_inf.mp x.2).2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hcardFE : Nat.card {x : Q // x ∈ B ∧ h x = x} = Nat.card ↥F := Nat.card_congr EF
  have hFdvd : Nat.card ↥F ∣ 8 := by
    have h := Subgroup.card_dvd_of_le (H := F) (K := B) inf_le_left
    rwa [hBcard] at h
  have hFle : Nat.card ↥F ≤ 8 := Nat.le_of_dvd (by norm_num) hFdvd
  have hFdvd' : Nat.card {x : Q // x ∈ B ∧ h x = x} ∣ 8 := by rw [hcardFE]; exact hFdvd
  have hFle' : Nat.card {x : Q // x ∈ B ∧ h x = x} ≤ 8 := by rw [hcardFE]; exact hFle
  let f : Function.End ↥B := fun x => ⟨h (x : Q), hGB h hhG (x : Q) x.2⟩
  have hf3 : f ^ 3 = 1 := by
    funext x
    apply Subtype.ext
    show h (h (h (x : Q))) = (x : Q)
    have hpow : h ^ 3 = 1 := by rw [← hh3]; exact pow_orderOf_eq_one h
    have hx := congrArg (fun e : MulAut Q => (e : Q → Q) (x : Q)) hpow
    simpa [pow_succ, MulAut.mul_apply] using hx
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥B) (f := f) (p := 3) (n := 1)
    (hp := ⟨Nat.prime_three⟩) hf3
  let E : ↥(Function.fixedPoints f) ≃ {x : Q // x ∈ B ∧ h x = x} :=
    { toFun := fun x => ⟨(x.1 : Q), x.1.2, by
        have hx := congrArg Subtype.val x.2
        simpa [f] using hx⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        apply Subtype.ext
        exact x.2.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hmod2 : Nat.card {x : Q // x ∈ B ∧ h x = x} ≡ 8 [MOD 3] := by
    have h1 : Nat.card {x : Q // x ∈ B ∧ h x = x} =
        Fintype.card (Function.fixedPoints f) := by
      rw [← Nat.card_congr E, Nat.card_eq_fintype_card]
    rw [h1]
    have hB : (Fintype.card ↥B : ℕ) = 8 := by rw [← Nat.card_eq_fintype_card, hBcard]
    rw [← hB]
    exact hmod.symm
  have hmodF : Nat.card ↥F ≡ 8 [MOD 3] := by rw [← hcardFE]; exact hmod2
  have hmodF3 : Nat.card ↥F % 3 = 2 := by
    have h := hmodF
    simp only [Nat.ModEq] at h
    omega
  have hcases : Nat.card ↥F = 2 ∨ Nat.card ↥F = 8 := by
    interval_cases Nat.card ↥F <;> simp_all [Nat.dvd_iff_mod_eq_zero]
  rcases hcases with h2 | h8
  · rw [hcardFE, h2]
  · exfalso
    have hFB : F = B := Subgroup.eq_of_le_of_card_ge inf_le_left
      (by rw [hBcard, h8])
    have hfixB : ∀ x ∈ B, h x = x := by
      intro x hx
      have hxF : x ∈ F := hFB.symm ▸ hx
      have := (Subgroup.mem_inf.mp hxF).2
      simpa using this
    have hh1 : h = 1 := hfaithB h hhG hfixB
    rw [hh1] at hh3
    simp at hh3

private theorem s16h_e3_fix_le_two {Q : Type*} [CommGroup Q] [Finite Q]
    {G : Subgroup (MulAut Q)} {B : Subgroup Q} (hBcard : Nat.card ↥B = 8)
    (hGB : ∀ g ∈ G, ∀ x ∈ B, g x ∈ B)
    (hfaithB : ∀ g ∈ G, (∀ x ∈ B, g x = x) → g = 1)
    (a : Q) (H24 : Nat.card ↥(MulAction.stabilizer G a) = 24) :
    Nat.card {x : Q // x ∈ B ∧ ∀ g : ↥(MulAction.stabilizer G a),
      (g : MulAut Q) x = x} ≤ 2 := by
  classical
  have h3dvd : 3 ∣ Nat.card ↥(MulAction.stabilizer G a) := by rw [H24]; norm_num
  obtain ⟨g, hg3⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hgG : ((g : ↥G) : MulAut Q) ∈ G := (g : ↥G).2
  have hg3' : orderOf (((g : ↥G) : MulAut Q)) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg3]
  have hsingle := s16h_e3_fix_single_le_two (h := ((g : ↥G) : MulAut Q)) hBcard hGB hfaithB
    hgG hg3'
  refine le_trans ?_ hsingle
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1, x.2.1, x.2.2 g⟩) ?_
  intro x y hxy
  have h1 : (x.1 : Q) = (y.1 : Q) :=
    congrArg (Subtype.val : {x : Q // x ∈ B ∧ ((g : ↥G) : MulAut Q) x = x} → Q) hxy
  exact Subtype.ext h1

private theorem s16h_mul_card_le_of_pairwiseDisjoint {ι α : Type*} [Finite ι] [Finite α]
    {f : ι → Set α} {T : Set α} {e : ℕ} (hdisj : Pairwise fun i j => Disjoint (f i) (f j))
    (hsub : ∀ i, f i ⊆ T) (hcard : ∀ i, e ≤ (f i).ncard) :
    e * Nat.card ι ≤ T.ncard := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hfin : ∀ i, (f i).Finite := fun i => Set.toFinite _
  have hsum : (⋃ i, f i).ncard = ∑ i : ι, (f i).ncard := by
    rw [Set.ncard_iUnion_of_finite hfin hdisj, finsum_eq_sum_of_fintype]
  have h1 : ∑ i : ι, e ≤ ∑ i : ι, (f i).ncard := Finset.sum_le_sum fun i _ => hcard i
  have h2 : ∑ i : ι, e = e * Nat.card ι := by
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]
  have h3 : (⋃ i, f i).ncard ≤ T.ncard :=
    Set.ncard_le_ncard (Set.iUnion_subset hsub) (Set.toFinite _)
  calc e * Nat.card ι = ∑ i : ι, e := h2.symm
    _ ≤ ∑ i : ι, (f i).ncard := h1
    _ = (⋃ i, f i).ncard := hsum.symm
    _ ≤ T.ncard := h3

private theorem s16h_exists_decomp {Q : Type*} [CommGroup Q] {A B : Subgroup Q}
    (hsup : A ⊔ B = ⊤) (x : Q) : ∃ α ∈ A, ∃ β ∈ B, α * β = x := by
  have hx : x ∈ A ⊔ B := by rw [hsup]; trivial
  exact Subgroup.mem_sup.mp hx

private theorem s16h_nat_card_subtype_le_sdiff_add_one {α : Type*} [Finite α]
    (P : α → Prop) (a : α) :
    Nat.card {x // P x} ≤ Nat.card {x // P x ∧ x ≠ a} + 1 := by
  classical
  let ψ : {x // P x} → {x // P x ∧ x ≠ a} ⊕ Unit := fun x =>
    if h : x.1 = a then Sum.inr () else Sum.inl ⟨x.1, x.2, h⟩
  have hψ : Function.Injective ψ := by
    intro x y hxy
    by_cases hx : x.1 = a
    · by_cases hy : y.1 = a
      · exact Subtype.ext (hx.trans hy.symm)
      · simp [ψ, hx, hy] at hxy
    · by_cases hy : y.1 = a
      · simp [ψ, hx, hy] at hxy
      · simp only [ψ, dif_neg hx, dif_neg hy, Sum.inl.injEq] at hxy
        exact Subtype.ext (by
          have := congrArg (Subtype.val : {x // P x ∧ x ≠ a} → α) hxy
          simpa using this)
  have hle := Nat.card_le_card_of_injective ψ hψ
  have hunit : Nat.card Unit = 1 := by rw [Nat.card_eq_fintype_card, Fintype.card_unit]
  rw [Nat.card_sum, hunit] at hle
  exact hle

private theorem s16h_e3_orbit_meets {Q : Type} [CommGroup Q] [Finite Q]
    {G : Subgroup (MulAut Q)} {A B : Subgroup Q}
    (hinf : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤)
    (hGA : ∀ g ∈ G, ∀ x ∈ A, g x ∈ A) (hGB : ∀ g ∈ G, ∀ x ∈ B, g x ∈ B)
    (a : Q) (ha : a ∈ A) (ha1 : a ≠ 1)
    (htransA : ∀ x ∈ A, x ≠ 1 → ∃ g : MulAut Q, g ∈ G ∧ g a = x)
    (hGod : Nat.card (MulAction.orbit G a) = 7)
    (hHcard : Nat.card ↥(MulAction.stabilizer G a) = 24)
    {O : Set Q} (hOorbit : ∃ y, O = MulAction.orbit G y)
    {e : ℕ} (hOsize : Nat.card O = 7 * e) (hnotB : ¬ O ⊆ (B : Set Q)) :
    ∃ b' ∈ B, a * b' ∈ O ∧
      (MulAction.orbit (MulAction.stabilizer G a) b').ncard = e := by
  classical
  have hx : ∃ x ∈ O, x ∉ B := by
    by_contra h
    exact hnotB fun x hxO => by
      by_contra hxB
      exact h ⟨x, hxO, hxB⟩
  obtain ⟨x, hxO, hxB⟩ := hx
  obtain ⟨α, hαA, β, hβB, hαβ⟩ := s16h_exists_decomp hsup x
  have hα1 : α ≠ 1 := by
    intro h; exact hxB (by rw [← hαβ, h, one_mul]; exact hβB)
  obtain ⟨g, hgG, hga⟩ := htransA α hαA hα1
  have hgGinv : (g : MulAut Q)⁻¹ ∈ G := G.inv_mem hgG
  have hb'B : (g : MulAut Q)⁻¹ β ∈ B := hGB _ hgGinv β hβB
  have hmem : a * (g : MulAut Q)⁻¹ β ∈ O := by
    have h1 : g (a * (g : MulAut Q)⁻¹ β) = x := by
      rw [map_mul, hga, MulAut.apply_inv_self, hαβ]
    have h2 : a * (g : MulAut Q)⁻¹ β = (g : MulAut Q)⁻¹ x := by
      conv_rhs => rw [← h1]
      rw [MulAut.inv_apply_self]
    obtain ⟨y, hy⟩ := hOorbit
    have hxOy : x ∈ MulAction.orbit G y := by rw [← hy]; exact hxO
    have hxo : MulAction.orbit G x = O := by
      rw [hy]; exact MulAction.orbit_eq_iff.mpr hxOy
    have hx' : (g : MulAut Q)⁻¹ x ∈ MulAction.orbit G x :=
      MulAction.mem_orbit_iff.mpr
        ⟨⟨(g : MulAut Q)⁻¹, hgGinv⟩, by rw [Submonoid.smul_def, MulAut.smul_def]⟩
    rw [h2, ← hxo]
    exact hx'
  refine ⟨(g : MulAut Q)⁻¹ β, hb'B, hmem, ?_⟩
  have hOeq : O = MulAction.orbit G (a * (g : MulAut Q)⁻¹ β) := by
    obtain ⟨y, hy⟩ := hOorbit
    have h1 : MulAction.orbit G (a * (g : MulAut Q)⁻¹ β) = MulAction.orbit G y :=
      MulAction.orbit_eq_iff.mpr (by rw [← hy]; exact hmem)
    rw [hy, h1]
  have hPhi := s16h_e3_Phi_card hinf hGA hGB a ha hGod hHcard
    ((g : MulAut Q)⁻¹ β) hb'B
  have heq : 7 * e = 7 * (MulAction.orbit (MulAction.stabilizer G a)
      ((g : MulAut Q)⁻¹ β)).ncard := by
    rw [← hOsize, hOeq, hPhi]
    rfl
  omega

private theorem s16h_e3_orbit_bounds {Q : Type} [CommGroup Q] [Finite Q]
    {G : Subgroup (MulAut Q)} {A B : Subgroup Q}
    (hinf : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤)
    (hGA : ∀ g ∈ G, ∀ x ∈ A, g x ∈ A) (hGB : ∀ g ∈ G, ∀ x ∈ B, g x ∈ B)
    (a : Q) (ha : a ∈ A) (ha1 : a ≠ 1)
    (htransA : ∀ x ∈ A, x ≠ 1 → ∃ g : MulAut Q, g ∈ G ∧ g a = x)
    (hGod : Nat.card (MulAction.orbit G a) = 7)
    (hHcard : Nat.card ↥(MulAction.stabilizer G a) = 24)
    (hBcard : Nat.card ↥B = 8)
    (hfaithB : ∀ g ∈ G, (∀ x ∈ B, g x = x) → g = 1)
    (b : Q) (hb : b ∈ B) :
    Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} ≤ 3 ∧
    (3 ∣ Nat.card (MulAction.orbit G (a * b)) →
      Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} ≤ 2) := by
  classical
  let H : Subgroup ↥G := MulAction.stabilizer G a
  set e : ℕ := Nat.card (MulAction.orbit H b) with he
  have hsize : Nat.card (MulAction.orbit G (a * b)) = 7 * e := by
    rw [he]; exact s16h_e3_Phi_card hinf hGA hGB a ha hGod hHcard b hb
  haveI : Nonempty (MulAction.orbit H b) := ⟨⟨b, MulAction.mem_orbit_self b⟩⟩
  have hepos : 0 < e := by rw [he]; exact Nat.card_pos
  let Bsharp : Set Q := {x : Q | x ∈ B ∧ x ≠ 1}
  let φ : Set Q → Set Q := fun O => {x : Q | x ∈ B ∧ a * x ∈ O}
  have hT : Bsharp.ncard = 7 := by
    have hEq : Bsharp = (B : Set Q) \ {1} := by ext x; simp [Bsharp]
    have hsub1 : ({1} : Set Q) ⊆ (B : Set Q) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact B.one_mem
    have hBn : (B : Set Q).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hBcard
    rw [hEq, Set.ncard_sdiff hsub1, Set.ncard_singleton, hBn]
  have hnotB_of_ne : ∀ (O : Set Q), (∃ y, O = MulAction.orbit G y) →
      Nat.card O = 7 * e → O ≠ Bsharp → ¬ O ⊆ (B : Set Q) := by
    intro O hOorbit hOsize hOne hsub
    by_cases he1 : e = 1
    · have hOncard : O.ncard = 7 := by
        rw [← Nat.card_coe_set_eq, hOsize, he1, mul_one]
      have h1not : (1 : Q) ∉ O := by
        intro h1mem
        have hO1 : MulAction.orbit G (1 : Q) = O := by
          obtain ⟨y, hy⟩ := hOorbit
          have : (1 : Q) ∈ MulAction.orbit G y := by rw [← hy]; exact h1mem
          rw [hy]; exact MulAction.orbit_eq_iff.mpr this
        have horbit1 : MulAction.orbit G (1 : Q) = ({1} : Set Q) := by
          ext x
          rw [MulAction.mem_orbit_iff]
          constructor
          · rintro ⟨g, rfl⟩; simp
          · intro hx
            rw [Set.mem_singleton_iff] at hx
            exact ⟨1, by rw [hx]; simp⟩
        have hcard1 : Nat.card O = 1 := by
          rw [← hO1, horbit1, Nat.card_coe_set_eq]; simp
        omega
      have hsubsharp : O ⊆ Bsharp := fun x hx => ⟨hsub hx, fun hx1 => h1not (hx1 ▸ hx)⟩
      have hBeq : O = Bsharp := by
        apply Set.eq_of_subset_of_ncard_le hsubsharp
        rw [hT, hOncard]
      exact hOne hBeq
    · have he2 : 2 ≤ e := by omega
      have hle : Nat.card O ≤ Nat.card ↥B := Set.ncard_le_ncard hsub
      rw [hOsize, hBcard] at hle
      omega
  have hmemφ : ∀ (O : Set Q), (∃ y, O = MulAction.orbit G y) → Nat.card O = 7 * e →
      O ≠ Bsharp → ∃ b' ∈ B, a * b' ∈ O ∧ (MulAction.orbit H b').ncard = e := by
    intro O hOorbit hOsize hOne
    exact s16h_e3_orbit_meets hinf hsup hGA hGB a ha ha1 htransA hGod hHcard hOorbit hOsize
      (hnotB_of_ne O hOorbit hOsize hOne)
  have hdisj_all : ∀ O1 O2 : Set Q, O1 ∈ s16h_sameSizeOrbits G (a * b) →
      O2 ∈ s16h_sameSizeOrbits G (a * b) → O1 ≠ O2 → Disjoint (φ O1) (φ O2) := by
    intro O1 O2 hO1 hO2 hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have hx1' : x ∈ B ∧ a * x ∈ O1 := hx1
    have hx2' : x ∈ B ∧ a * x ∈ O2 := hx2
    obtain ⟨y1, hy1, -⟩ := hO1
    obtain ⟨y2, hy2, -⟩ := hO2
    have h1 : MulAction.orbit G (a * x) = O1 := by
      have : a * x ∈ MulAction.orbit G y1 := by rw [← hy1]; exact hx1'.2
      rw [hy1]; exact MulAction.orbit_eq_iff.mpr this
    have h2 : MulAction.orbit G (a * x) = O2 := by
      have : a * x ∈ MulAction.orbit G y2 := by rw [← hy2]; exact hx2'.2
      rw [hy2]; exact MulAction.orbit_eq_iff.mpr this
    exact hne (by rw [← h1, h2])
  have hge2 : 2 ≤ e → e * Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} ≤ 7 := by
    intro he2
    have hdisj' : Pairwise fun O1 O2 : {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} =>
        Disjoint (φ O1.1) (φ O2.1) := by
      intro O1 O2 hne
      exact hdisj_all O1.1 O2.1 O1.2 O2.2 (fun h => hne (Subtype.ext h))
    have hsub' : ∀ O : {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)},
        φ O.1 ⊆ Bsharp := by
      intro O x hx
      obtain ⟨hxB, hxO⟩ := hx
      refine ⟨hxB, ?_⟩
      intro hx1
      have haO : a ∈ O.1 := by rw [hx1] at hxO; simpa using hxO
      obtain ⟨y, hy, hOcard⟩ := O.2
      have hOsize : Nat.card O.1 = 7 * e := by rw [hOcard, hsize]
      have hOa : O.1 = MulAction.orbit G a := by
        have : a ∈ MulAction.orbit G y := by rw [← hy]; exact haO
        rw [hy]; exact (MulAction.orbit_eq_iff.mpr this).symm
      rw [hOa, hGod] at hOsize
      omega
    have hcard' : ∀ O : {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)},
        e ≤ (φ O.1).ncard := by
      intro O
      obtain ⟨y, hy, hOcard⟩ := O.2
      have hOsize : Nat.card O.1 = 7 * e := by rw [hOcard, hsize]
      have hnotB : ¬ O.1 ⊆ (B : Set Q) := by
        intro hsub
        have hle : Nat.card O.1 ≤ Nat.card ↥B := Set.ncard_le_ncard hsub
        rw [hOsize, hBcard] at hle
        omega
      obtain ⟨b', hb'B, hab'O, hb'card⟩ :=
        s16h_e3_orbit_meets hinf hsup hGA hGB a ha ha1 htransA hGod hHcard ⟨y, hy⟩ hOsize hnotB
      have hsub2 : MulAction.orbit H b' ⊆ φ O.1 := by
        intro z hz
        rw [MulAction.mem_orbit_iff] at hz
        obtain ⟨h, hhz⟩ := hz
        rw [← hhz]
        refine ⟨?_, ?_⟩
        · rw [Subgroup.smul_def, Submonoid.smul_def, MulAut.smul_def]
          exact hGB _ (h : ↥G).2 b' hb'B
        · rw [Subgroup.smul_def, Submonoid.smul_def, MulAut.smul_def]
          have hha : (h : MulAut Q) a = a := by
            have h1 := MulAction.mem_stabilizer_iff.mp (h : ↥H).2
            rwa [Submonoid.smul_def, MulAut.smul_def] at h1
          have hmem : ((h : ↥G) : MulAut Q) (a * b') ∈ O.1 := by
            have hO_orbit : O.1 = MulAction.orbit G (a * b') := by
              have : a * b' ∈ MulAction.orbit G y := by rw [← hy]; exact hab'O
              rw [hy]; exact (MulAction.orbit_eq_iff.mpr this).symm
            rw [hO_orbit]
            exact MulAction.mem_orbit_iff.mpr
              ⟨(h : ↥G), by rw [Submonoid.smul_def, MulAut.smul_def]⟩
          rw [map_mul, hha] at hmem
          exact hmem
      have hb'card' : (MulAction.orbit H b').ncard = e := hb'card
      calc e = (MulAction.orbit H b').ncard := hb'card'.symm
        _ ≤ (φ O.1).ncard := Set.ncard_le_ncard hsub2
    have hmain := s16h_mul_card_le_of_pairwiseDisjoint
      (f := fun O : {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} => φ O.1)
      (T := Bsharp) (e := e) hdisj' hsub' hcard'
    rwa [hT] at hmain
  have hbound_e1 : e = 1 → Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} ≤ 3 := by
    intro he1
    have hsplit : Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} ≤
        Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b) ∧ O ≠ Bsharp} + 1 :=
      s16h_nat_card_subtype_le_sdiff_add_one
        (fun O : Set Q => O ∈ s16h_sameSizeOrbits G (a * b)) Bsharp
    have hfix : ({x : Q | x ∈ B ∧ ∀ h : ↥H, (h : MulAut Q) x = x} : Set Q).ncard ≤ 2 := by
      rw [← Nat.card_coe_set_eq]
      exact s16h_e3_fix_le_two hBcard hGB hfaithB a hHcard
    have hS'le : Nat.card
        {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b) ∧ O ≠ Bsharp} ≤ 2 := by
      have hdisj' : Pairwise fun O1 O2 :
          {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b) ∧ O ≠ Bsharp} =>
          Disjoint (φ O1.1) (φ O2.1) := by
        intro O1 O2 hne
        exact hdisj_all O1.1 O2.1 O1.2.1 O2.2.1 (fun h => hne (Subtype.ext h))
      have hsub' : ∀ O : {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b) ∧ O ≠ Bsharp},
          φ O.1 ⊆ {x : Q | x ∈ B ∧ ∀ h : ↥H, (h : MulAut Q) x = x} := by
        intro O x hx
        obtain ⟨hxB, hxO⟩ := hx
        refine ⟨hxB, ?_⟩
        intro h
        obtain ⟨y, hy, hOcard⟩ := O.2.1
        have hOsize : Nat.card O.1 = 7 * e := by rw [hOcard, hsize]
        have hOsize7 : Nat.card O.1 = 7 := by rw [hOsize, he1, mul_one]
        have hOax : O.1 = MulAction.orbit G (a * x) := by
          have : a * x ∈ MulAction.orbit G y := by rw [← hy]; exact hxO
          rw [hy]; exact (MulAction.orbit_eq_iff.mpr this).symm
        have hPhi := s16h_e3_Phi_card hinf hGA hGB a ha hGod hHcard x hxB
        have hHx : Nat.card (MulAction.orbit H x) = 1 := by
          have : Nat.card O.1 = 7 * Nat.card (MulAction.orbit H x) := by rw [hOax, hPhi]
          omega
        have hmem : (h : MulAut Q) x ∈ MulAction.orbit H x :=
          MulAction.mem_orbit_iff.mpr
            ⟨h, by rw [Subgroup.smul_def, Submonoid.smul_def, MulAut.smul_def]⟩
        haveI : Subsingleton (MulAction.orbit H x) :=
          Finite.card_le_one_iff_subsingleton.mp (le_of_eq hHx)
        exact congrArg Subtype.val
          (Subsingleton.elim ⟨(h : MulAut Q) x, hmem⟩ ⟨x, MulAction.mem_orbit_self x⟩)
      have hcard' : ∀ O : {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b) ∧ O ≠ Bsharp},
          1 ≤ (φ O.1).ncard := by
        intro O
        obtain ⟨y, hy, hOcard⟩ := O.2.1
        have hOsize : Nat.card O.1 = 7 * e := by rw [hOcard, hsize]
        obtain ⟨b', hb'B, hab'O, -⟩ := hmemφ O.1 ⟨y, hy⟩ hOsize O.2.2
        have hne : (φ O.1).Nonempty := ⟨b', hb'B, hab'O⟩
        have : (0 : ℕ) < (φ O.1).ncard := (Set.ncard_pos (s := φ O.1)).mpr hne
        omega
      have hmain := s16h_mul_card_le_of_pairwiseDisjoint
        (f := fun O : {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b) ∧ O ≠ Bsharp} => φ O.1)
        (T := {x : Q | x ∈ B ∧ ∀ h : ↥H, (h : MulAut Q) x = x}) (e := 1)
        hdisj' hsub' hcard'
      rw [one_mul] at hmain
      exact hmain.trans hfix
    omega
  constructor
  · by_cases he1 : e = 1
    · exact hbound_e1 he1
    · have he2 : 2 ≤ e := by omega
      have hle := hge2 he2
      have : 2 * Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} ≤
          e * Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} :=
        Nat.mul_le_mul_right _ he2
      omega
  · intro h3
    by_cases he1 : e = 1
    · rw [hsize, he1, mul_one] at h3; norm_num at h3
    · have he2 : 2 ≤ e := by omega
      have hle := hge2 he2
      have h3e : 3 ∣ e := by
        rw [hsize] at h3
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
        · norm_num at h
        · exact h
      have h3e' : 3 ≤ e := by
        obtain ⟨k, hk⟩ := h3e
        have hkpos : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; omega)
        nlinarith
      have : 3 * Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} ≤
          e * Nat.card {O : Set Q // O ∈ s16h_sameSizeOrbits G (a * b)} :=
        Nat.mul_le_mul_right _ h3e'
      omega

private theorem s16h_twoNat_bounds [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hS : SumOfNat (fun H U Z => CFSG.Quasithin.BinaryNaturalSL H U Z 3 1) L U Z 2)
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hLcard : Nat.card ↥L = 168) :
    ∀ v : Sec U Z, v ≠ 1 →
      Nat.card {O : Set (Sec U Z) // O ∈ s16h_sameSizeOrbits (autSec L U Z) v} ≤ 3 ∧
      (3 ∣ Nat.card (MulAction.orbit (autSec L U Z) v) →
        Nat.card {O : Set (Sec U Z) // O ∈ s16h_sameSizeOrbits (autSec L U Z) v} ≤ 2) := by
  classical
  obtain ⟨I, hZI, hind, hsup, hN⟩ := hS
  have hIU : ∀ i, I i ≤ U := fun i => (le_iSup I i).trans (le_sup_right.trans_eq hsup)
  have hLI : ∀ i, L ≤ stabSub (I i) := by
    intro i
    obtain ⟨K, hKf, hKfin, hKcard, hReal⟩ := hN i
    obtain ⟨π, hπ⟩ := hReal
    have hinv : ∀ g : ↥L, ∀ u ∈ I i, (g : MulAut W) u ∈ I i := fun g u hu => hπ.2.2.2.1 g u hu
    intro l hl
    rw [mem_stabSub]
    intro x
    constructor
    · intro hx
      have h := hinv ⟨l⁻¹, L.inv_mem hl⟩ (l x) hx
      simpa using h
    · intro hx
      exact hinv ⟨l, hl⟩ x hx
  have hsup' : I 0 ⊔ I 1 = U := by
    rw [← hsup, s16h_iSup_fin_two]
    exact (sup_eq_right.mpr ((hZI 0).trans le_sup_left)).symm
  have hinf' : I 0 ⊓ I 1 = Z := by
    refine le_antisymm ?_ (le_inf (hZI 0) (hZI 1))
    have h0 := hind 0
    rw [s16h_iSup_ne_zero] at h0
    rw [sup_eq_right.mpr (hZI 1)] at h0
    exact h0
  have hD : ∀ i, CFSG.Quasithin.L3Data L (I i) Z := fun i =>
    Classical.choice (CFSG.Quasithin.BinaryNaturalSL.toL3Coord (hN i))
  let A : Subgroup (Sec U Z) := s16h_img Z (I 0) U
  let B : Subgroup (Sec U Z) := s16h_img Z (I 1) U
  let G : Subgroup (MulAut (Sec U Z)) := autSec L U Z
  have hAcard : Nat.card ↥A = 8 := s16h_img_card (hD 0) (hZI 0) (hIU 0)
  have hBcard : Nat.card ↥B = 8 := s16h_img_card (hD 1) (hZI 1) (hIU 1)
  have hinfAB : A ⊓ B = ⊥ :=
    s16h_img_inf_eq_bot (hZI 0) (hZI 1) (hIU 0) (hIU 1) hinf'.le
  have hsupAB : A ⊔ B = ⊤ := s16h_img_sup_eq_top (hIU 0) (hIU 1) hsup'
  have hGA : ∀ g ∈ G, ∀ x ∈ A, g x ∈ A := fun g hg x hx =>
    s16h_secIncl_image_stable Z (I 0) U (hIU 0) (hLI 0) hLZ hLU g hg x hx
  have hGB : ∀ g ∈ G, ∀ x ∈ B, g x ∈ B := fun g hg x hx =>
    s16h_secIncl_image_stable Z (I 1) U (hIU 1) (hLI 1) hLZ hLU g hg x hx
  have hfaithB : ∀ g ∈ G, (∀ x ∈ B, g x = x) → g = 1 := fun g hg hfix =>
    s16h_e3_faithful (hD 1) (hZI 1) (hIU 1) (hLI 1) hLZ hLU hg hfix
  have hGcard : Nat.card ↥G = 168 :=
    s16h_e3_G_card (hD 0) (hZI 0) (hIU 0) (hLI 0) hLZ hLU hLcard
  let v0 : CFSG.Quasithin.L3.Vec := fun _ => 1
  have hv0 : v0 ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  let eA := s16h_secEquivOfL3Data (hD 0) (hZI 0)
  let a0 : Sec U Z := s16h_secIncl Z (I 0) U (hIU 0) (eA.symm (Multiplicative.ofAdd v0))
  have ha0A : a0 ∈ A := by
    rw [show A = s16h_img Z (I 0) U from rfl, s16h_img,
      ← s16h_secIncl_range Z (I 0) U (hIU 0)]
    exact ⟨_, rfl⟩
  have ha0ne : a0 ≠ 1 := by
    intro h
    have h1 : eA.symm (Multiplicative.ofAdd v0) = 1 :=
      s16h_secIncl_injective Z (I 0) U (hIU 0) h
    have h2 : Multiplicative.ofAdd v0 = 1 := by simpa using congrArg eA h1
    exact hv0 (by simpa using congrArg Multiplicative.toAdd h2)
  have htransA : ∀ x ∈ A, x ≠ 1 → ∃ g : MulAut (Sec U Z), g ∈ G ∧ g a0 = x := fun x hxA hxne =>
    s16h_e3_trans (hD 0) (hZI 0) (hIU 0) (hLI 0) hLZ hLU ha0A ha0ne hxA hxne
  have htransB : ∀ x ∈ B, x ≠ 1 → ∀ y ∈ B, y ≠ 1 →
      ∃ g : MulAut (Sec U Z), g ∈ G ∧ g x = y := fun x hxB hxne y hyB hyne =>
    s16h_e3_trans (hD 1) (hZI 1) (hIU 1) (hLI 1) hLZ hLU hxB hxne hyB hyne
  have horbitA : MulAction.orbit G a0 = (A : Set (Sec U Z)) \ {1} := by
    ext x
    constructor
    · intro hx
      rw [MulAction.mem_orbit_iff] at hx
      obtain ⟨g, hg⟩ := hx
      refine ⟨?_, ?_⟩
      · rw [← hg, Submonoid.smul_def, MulAut.smul_def]
        exact hGA _ g.2 a0 ha0A
      · intro h1
        apply ha0ne
        rw [← hg, Submonoid.smul_def, MulAut.smul_def] at h1
        exact (g : MulAut (Sec U Z)).injective (by rw [h1, map_one])
    · rintro ⟨hxA, hx1⟩
      rw [MulAction.mem_orbit_iff]
      obtain ⟨g, hg, hga⟩ := htransA x hxA hx1
      exact ⟨⟨g, hg⟩, by rw [Submonoid.smul_def, MulAut.smul_def]; exact hga⟩
  have hsub1A : ({1} : Set (Sec U Z)) ⊆ (A : Set (Sec U Z)) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact A.one_mem
  have hGod : Nat.card (MulAction.orbit G a0) = 7 := by
    have hAn : (A : Set (Sec U Z)).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hAcard
    rw [horbitA, Nat.card_coe_set_eq, Set.ncard_sdiff hsub1A, Set.ncard_singleton, hAn]
  have hHcard : Nat.card ↥(MulAction.stabilizer G a0) = 24 := by
    have h1 : Nat.card (MulAction.orbit G a0) * Nat.card ↥(MulAction.stabilizer G a0) =
        Nat.card ↥G := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (G := G) a0)
    rw [hGod, hGcard] at h1
    omega
  intro v hv
  obtain ⟨α, hαA, β, hβB, hαβ⟩ := s16h_exists_decomp hsupAB v
  by_cases hα1 : α = 1
  · have hvB : v ∈ B := by rw [← hαβ, hα1, one_mul]; exact hβB
    have horbitv : MulAction.orbit G v = (B : Set (Sec U Z)) \ {1} := by
      ext x
      constructor
      · intro hx
        rw [MulAction.mem_orbit_iff] at hx
        obtain ⟨g, hg⟩ := hx
        refine ⟨?_, ?_⟩
        · rw [← hg, Submonoid.smul_def, MulAut.smul_def]
          exact hGB _ g.2 v hvB
        · intro h1
          apply hv
          rw [← hg, Submonoid.smul_def, MulAut.smul_def] at h1
          exact (g : MulAut (Sec U Z)).injective (by rw [h1, map_one])
      · rintro ⟨hxB, hx1⟩
        rw [MulAction.mem_orbit_iff]
        obtain ⟨g, hg, hgv⟩ := htransB v hvB hv x hxB hx1
        exact ⟨⟨g, hg⟩, by rw [Submonoid.smul_def, MulAut.smul_def]; exact hgv⟩
    have hsub1B : ({1} : Set (Sec U Z)) ⊆ (B : Set (Sec U Z)) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact B.one_mem
    have hvsize : Nat.card (MulAction.orbit G v) = Nat.card (MulAction.orbit G a0) := by
      rw [horbitv, horbitA, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
        Set.ncard_sdiff hsub1B, Set.ncard_sdiff hsub1A, Set.ncard_singleton]
      have hBn : (B : Set (Sec U Z)).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hBcard
      have hAn : (A : Set (Sec U Z)).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hAcard
      rw [hBn, hAn]
    have hset : s16h_sameSizeOrbits G v = s16h_sameSizeOrbits G (a0 * 1) := by
      simp only [s16h_sameSizeOrbits, mul_one]
      rw [hvsize]
    have hsize1 : Nat.card (MulAction.orbit G (a0 * 1)) = Nat.card (MulAction.orbit G v) := by
      rw [mul_one, hvsize]
    rw [hset, ← hsize1]
    exact s16h_e3_orbit_bounds hinfAB hsupAB hGA hGB a0 ha0A ha0ne htransA hGod hHcard
      hBcard hfaithB 1 B.one_mem
  · obtain ⟨g, hgG, hga⟩ := htransA α hαA hα1
    let bb : Sec U Z := (g : MulAut (Sec U Z))⁻¹ β
    have hbbB : bb ∈ B := hGB _ (G.inv_mem hgG) β hβB
    have hv_eq : v = g (a0 * bb) := by
      have h1 : g (a0 * bb) = α * β := by
        rw [map_mul, hga]
        congr 1
        rw [show bb = (g : MulAut (Sec U Z))⁻¹ β from rfl, MulAut.apply_inv_self]
      rw [h1, hαβ]
    have horb : MulAction.orbit G v = MulAction.orbit G (a0 * bb) := by
      rw [hv_eq]
      exact MulAction.orbit_eq_iff.mpr
        (MulAction.mem_orbit_iff.mpr ⟨⟨g, hgG⟩, by rw [Submonoid.smul_def, MulAut.smul_def]⟩)
    have hset : s16h_sameSizeOrbits G v = s16h_sameSizeOrbits G (a0 * bb) := by
      simp only [s16h_sameSizeOrbits]
      rw [horb]
    rw [hset, horb]
    exact s16h_e3_orbit_bounds hinfAB hsupAB hGA hGB a0 ha0A ha0ne htransA hGod hHcard
      hBcard hfaithB bb hbbB

public theorem s16h_twoNat_orbit_same_size [Finite W] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W}
    (hS : SumOfNat (fun H U Z => CFSG.Quasithin.BinaryNaturalSL H U Z 3 1) L U Z 2)
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hLcard : Nat.card ↥L = 168)
    (v : Sec U Z) (hv : v ≠ 1) :
    Nat.card {O : Set (Sec U Z) // O ∈ s16h_sameSizeOrbits (autSec L U Z) v} ≤ 3 :=
  (s16h_twoNat_bounds hS hLU hLZ hLcard v hv).1

public theorem s16h_twoNat_orbit_same_size_three [Finite W] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W}
    (hS : SumOfNat (fun H U Z => CFSG.Quasithin.BinaryNaturalSL H U Z 3 1) L U Z 2)
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hLcard : Nat.card ↥L = 168)
    (v : Sec U Z) (hv : v ≠ 1)
    (h3 : 3 ∣ Nat.card (MulAction.orbit (autSec L U Z) v)) :
    Nat.card {O : Set (Sec U Z) // O ∈ s16h_sameSizeOrbits (autSec L U Z) v} ≤ 2 :=
  (s16h_twoNat_bounds hS hLU hLZ hLcard v hv).2 h3

public theorem s16h_orbit_fix_count {α : Type*} [Group α] [Finite α]
    (G E : Subgroup (MulAut α))
    (hEN : E ≤ Subgroup.normalizer (G : Set (MulAut α)))
    (hE9 : Nat.card ↥E = 9)
    (a : α) (ha9 : ¬ 9 ∣ Nat.card (MulAction.orbit G a))
    (h3 : Nat.card {O : Set α // O ∈ s16h_sameSizeOrbits G a} ≤ 3)
    (h3dvd : 3 ∣ Nat.card (MulAction.orbit G a) →
      Nat.card {O : Set α // O ∈ s16h_sameSizeOrbits G a} ≤ 2) :
    ∃ e : ↥E, (e : MulAut α) ≠ 1 ∧ ∃ x ∈ MulAction.orbit G a, (e : MulAut α) x = x := by
  classical
  set O : Set α := MulAction.orbit G a with hO
  set K : Subgroup ↥E := MulAction.stabilizer ↥E O with hK
  have hsub : MulAction.orbit ↥E O ⊆ s16h_sameSizeOrbits G a := by
    intro O' hO'
    rw [MulAction.mem_orbit_iff] at hO'
    obtain ⟨e, rfl⟩ := hO'
    have hsm : (e : ↥E) • O = (e : MulAut α) '' O := rfl
    refine ⟨(e : MulAut α) a, ?_, ?_⟩
    · rw [hsm, hO]
      ext x
      constructor
      · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
        refine ⟨⟨(e : MulAut α) * (g : MulAut α) * (e : MulAut α)⁻¹, ?_⟩, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hEN e.2) (g : MulAut α)).mp g.2
        · change ((e : MulAut α) * (g : MulAut α) * (e : MulAut α)⁻¹) ((e : MulAut α) a) =
            (e : MulAut α) ((g : MulAut α) a)
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      · rintro ⟨g, rfl⟩
        have hmemG : (e : MulAut α)⁻¹ * (g : MulAut α) * (e : MulAut α) ∈ G := by
          have he : (e : MulAut α)⁻¹ ∈ Subgroup.normalizer (G : Set (MulAut α)) :=
            Subgroup.inv_mem (Subgroup.normalizer (G : Set (MulAut α))) (hEN e.2)
          exact (Subgroup.mem_normalizer_iff.mp he (g : MulAut α)).mp g.2
        refine ⟨((e : MulAut α)⁻¹ * (g : MulAut α) * (e : MulAut α)) a,
          ⟨⟨(e : MulAut α)⁻¹ * (g : MulAut α) * (e : MulAut α), hmemG⟩, rfl⟩, ?_⟩
        change (e : MulAut α) (((e : MulAut α)⁻¹ * (g : MulAut α) * (e : MulAut α)) a) =
          (g : MulAut α) ((e : MulAut α) a)
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    · rw [hsm, hO]
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq,
        Set.ncard_image_of_injective _ (e : MulAut α).injective]
  have hOrbBound : Nat.card (MulAction.orbit ↥E O) ≤ 3 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub).trans (by
      rw [← Nat.card_coe_set_eq]; exact h3)
  have hKcard : Nat.card ↥K * Nat.card (MulAction.orbit ↥E O) = 9 := by
    have h1 : (MulAction.stabilizer ↥E O).index = (MulAction.orbit ↥E O).ncard :=
      MulAction.index_stabilizer ↥E O
    have h2 : Nat.card ↥K * K.index = Nat.card ↥E := Subgroup.card_mul_index K
    rw [← hK] at h1
    rw [h1, hE9] at h2
    simpa [Nat.card_coe_set_eq] using h2
  haveI : Nonempty (MulAction.orbit ↥E O) := ⟨O, MulAction.mem_orbit_self O⟩
  have hKge3 : 3 ≤ Nat.card ↥K := by
    have hpos : 0 < Nat.card (MulAction.orbit ↥E O) := Nat.card_pos
    nlinarith [hKcard, hOrbBound, hpos]
  have hKO : ∀ k : ↥K, ∀ x : ↥O, (k.1 : MulAut α) x ∈ O := by
    intro k x
    have hsm : (k.1 : ↥E) • O = O :=
      MulAction.mem_stabilizer_iff.mp (by rw [← hK]; exact k.2)
    have : (k.1 : MulAut α) x ∈ (k.1 : ↥E) • O := by
      rw [show (k.1 : ↥E) • O = (k.1 : MulAut α) '' O from rfl]
      exact ⟨x.1, x.2, rfl⟩
    rwa [hsm] at this
  letI : MulAction ↥K ↥O :=
    { smul := fun k x => ⟨(k.1 : MulAut α) x, hKO k x⟩
      one_smul := fun x => Subtype.ext rfl
      mul_smul := fun k l x => Subtype.ext (by rfl) }
  have hkey : ∃ k : ↥K, k ≠ 1 ∧ ∃ x : ↥O, k • x = x := by
    by_cases hO3 : 3 ∣ Nat.card (MulAction.orbit G a)
    · have hOrbBound2 : Nat.card (MulAction.orbit ↥E O) ≤ 2 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_le_ncard hsub).trans (by
          rw [← Nat.card_coe_set_eq]; exact h3dvd hO3)
      have hK9 : Nat.card ↥K = 9 := by
        have hOrbDvd : Nat.card (MulAction.orbit ↥E O) ∣ 9 :=
          ⟨Nat.card ↥K, by rw [mul_comm, hKcard]⟩
        have hOrb1 : Nat.card (MulAction.orbit ↥E O) = 1 := by
          have hpos : 0 < Nat.card (MulAction.orbit ↥E O) := Nat.card_pos
          interval_cases Nat.card (MulAction.orbit ↥E O) <;> omega
        rw [hOrb1, mul_one] at hKcard
        exact hKcard
      by_contra hcon
      have hfree : ∀ k : ↥K, k ≠ 1 → ∀ x : ↥O, k • x ≠ x :=
        fun k hk x hx => hcon ⟨k, hk, x, hx⟩
      have hdvd : Nat.card ↥K ∣ Nat.card ↥O := s16h_card_dvd_of_free hfree
      rw [hK9, Nat.card_coe_set_eq, hO] at hdvd
      exact ha9 hdvd
    · have hKdvd : Nat.card ↥K ∣ 9 :=
        ⟨Nat.card (MulAction.orbit ↥E O), hKcard.symm⟩
      have hKle9 : Nat.card ↥K ≤ 9 := by
        obtain ⟨c, hc⟩ := hKdvd
        have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; omega)
        nlinarith
      have hK3 : 3 ∣ Nat.card ↥K := by
        interval_cases Nat.card ↥K <;> omega
      by_contra hcon
      have hfree : ∀ k : ↥K, k ≠ 1 → ∀ x : ↥O, k • x ≠ x :=
        fun k hk x hx => hcon ⟨k, hk, x, hx⟩
      have hdvd : Nat.card ↥K ∣ Nat.card ↥O := s16h_card_dvd_of_free hfree
      have h3O : 3 ∣ Nat.card ↥O := dvd_trans hK3 hdvd
      rw [Nat.card_coe_set_eq, hO] at h3O
      exact hO3 h3O
  obtain ⟨k, hkne, x, hkx⟩ := hkey
  have hkx' : (k.1 : MulAut α) x.1 = x.1 :=
    congrArg Subtype.val hkx
  exact ⟨k.1, fun h => hkne (Subtype.ext (Subtype.ext h)), x.1,
    by simpa only [hO] using x.2, hkx'⟩

public theorem s16h_twoNat_autSec_E_card [Finite W] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W}
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    (E : Subgroup (MulAut W)) (hEU : E ≤ stabSub U) (hEZ : E ≤ stabSub Z)
    (hEab : IsElemAbelian 3 E)
    (hEcard : 9 * Nat.card ↥(E ⊓ centSub U) ≤ Nat.card ↥E)
    (hErank : Nat.card ↥(autSub E U) ≤ 9) (hZcard : Nat.card ↥Z ≤ 2) :
    Nat.card ↥(autSec E U Z) = 9 := by
  classical
  have hcent : E ⊓ centSec U Z = E ⊓ centSub U := by
    refine le_antisymm ?_ (le_inf inf_le_left (inf_le_right.trans (centSub_le_centSec U Z)))
    intro e he
    rw [Subgroup.mem_inf] at he ⊢
    refine ⟨he.1, ?_⟩
    rw [mem_centSub]
    intro u hu
    have hzu : e u * u⁻¹ ∈ Z := (mem_centSec.mp he.2).2 u hu
    have hfixZ : ∀ z ∈ Z, e z = z :=
      s15_Core_map_eq_self_of_card_le_two Z e hZcard
        (fun z hz => (mem_stabSub.mp (hEZ he.1) z).mpr hz)
    have he3 : e ^ 3 = 1 := hEab.2 e he.1
    set z : W := e u * u⁻¹ with hzdef
    have hz : z ∈ Z := hzdef ▸ hzu
    have hz3 : z ^ 3 = 1 := by
      have h1 : e u = z * u := by rw [hzdef]; group
      have hiter : ∀ n : ℕ, e (z ^ n * u) = z ^ (n + 1) * u := by
        intro n
        rw [map_mul, hfixZ _ (Z.pow_mem hz n), h1]
        group
      have he1 : e u = z ^ 1 * u := by rw [pow_one]; exact h1
      have he2 : e (e u) = z ^ 2 * u := by
        rw [he1]
        exact hiter 1
      have he3' : e (e (e u)) = z ^ 3 * u := by
        rw [he2]
        exact hiter 2
      have h4 : e (e (e u)) = u := by
        have := congrArg (fun f : MulAut W => f u) he3
        simpa [pow_succ, MulAut.mul_apply] using this
      rw [he3'] at h4
      exact mul_right_cancel (by rw [one_mul]; exact h4)
    have hzZ : (⟨z, hz⟩ : ↥Z) = 1 := by
      have hord3 : orderOf (⟨z, hz⟩ : ↥Z) ∣ 3 :=
        orderOf_dvd_iff_pow_eq_one.mpr (Subtype.ext hz3)
      have hordZ : orderOf (⟨z, hz⟩ : ↥Z) ∣ Nat.card ↥Z :=
        orderOf_dvd_natCard _
      have hle : orderOf (⟨z, hz⟩ : ↥Z) ≤ 2 :=
        (Nat.le_of_dvd Nat.card_pos hordZ).trans hZcard
      rcases (Nat.dvd_prime Nat.prime_three).mp hord3 with h1 | h3
      · exact orderOf_eq_one_iff.mp h1
      · omega
    have hz1 : z = 1 := by
      simpa using congrArg Subtype.val hzZ
    rw [hzdef] at hz1
    exact mul_inv_eq_one.mp hz1
  have h1 := card_autSec_mul (A := E) (W := U) (U := Z) hEU hEZ
  have h2 := card_autSub_mul (A := E) (U := U) hEU
  rw [hcent] at h1
  have h9 : Nat.card ↥(autSub E U) = 9 := by
    have hle : 9 ≤ Nat.card ↥(autSub E U) := by
      rw [← h2] at hEcard
      exact Nat.le_of_mul_le_mul_right hEcard Nat.card_pos
    omega
  rw [h9] at h2
  have hEq : Nat.card ↥(autSec E U Z) * Nat.card ↥(E ⊓ centSub U) =
      9 * Nat.card ↥(E ⊓ centSub U) := by
    rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hEq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
