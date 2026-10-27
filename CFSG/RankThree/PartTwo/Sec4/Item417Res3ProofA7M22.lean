module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofInTools
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofSpor
import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofK

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open scoped Pointwise

namespace Res417Three

variable {G : Type} [Group G]

theorem mk_eq_of_conj_eq {L : Subgroup G} {l l' : L}
    (h : ∀ x ∈ L, (l : G) * x * (l : G)⁻¹ = (l' : G) * x * (l' : G)⁻¹) :
    (l : L ⧸ Subgroup.center L) = (l' : L ⧸ Subgroup.center L) := by
  rw [QuotientGroup.eq, Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have h1 := h y y.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc (y : G) * ((l : G)⁻¹ * l') = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * l' := by group
    _ = (l : G)⁻¹ * ((l' : G) * y * (l' : G)⁻¹) * l' := by rw [h1]
    _ = (l : G)⁻¹ * l' * y := by group

variable {L A : Subgroup G}

@[expose] noncomputable def innerRep (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹)
    (a : A) : L :=
  ⟨(hinner a a.2).choose, (hinner a a.2).choose_spec.1⟩

theorem innerRep_spec (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) (a : A) :
    ∀ x ∈ L, (a : G) * x * (a : G)⁻¹ =
      (innerRep hinner a : G) * x * (innerRep hinner a : G)⁻¹ :=
  (hinner a a.2).choose_spec.2

@[expose] noncomputable def innerHom
    (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) :
    A →* L ⧸ Subgroup.center L where
  toFun a := (innerRep hinner a : L ⧸ Subgroup.center L)
  map_one' := by
    change (innerRep hinner 1 : L ⧸ Subgroup.center L) = 1
    rw [← QuotientGroup.mk_one]
    refine mk_eq_of_conj_eq fun x hx => ?_
    rw [← innerRep_spec hinner 1 x hx]
    simp
  map_mul' a b := by
    change (innerRep hinner (a * b) : L ⧸ Subgroup.center L) =
      (innerRep hinner a : L ⧸ Subgroup.center L) * (innerRep hinner b : L ⧸ Subgroup.center L)
    rw [← QuotientGroup.mk_mul]
    refine mk_eq_of_conj_eq fun x hx => ?_
    rw [← innerRep_spec hinner (a * b) x hx]
    have hbx : (innerRep hinner b : G) * x * (innerRep hinner b : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (innerRep hinner b).2 hx) (L.inv_mem (innerRep hinner b).2)
    have h1 := innerRep_spec hinner b x hx
    have h2 := innerRep_spec hinner a _ hbx
    simp only [Subgroup.coe_mul]
    calc (a : G) * b * x * ((a : G) * b)⁻¹ = (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹ := by
          group
      _ = (a : G) * ((innerRep hinner b : G) * x * (innerRep hinner b : G)⁻¹) * (a : G)⁻¹ := by
          rw [h1]
      _ = (innerRep hinner a : G) * ((innerRep hinner b : G) * x * (innerRep hinner b : G)⁻¹) *
          (innerRep hinner a : G)⁻¹ := h2
      _ = (innerRep hinner a : G) * innerRep hinner b * x *
          ((innerRep hinner a : G) * innerRep hinner b)⁻¹ := by group

theorem innerHom_apply (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) (a : A) :
    innerHom hinner a = (innerRep hinner a : L ⧸ Subgroup.center L) := rfl

theorem innerHom_eq_one_iff (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹)
    (a : A) : innerHom hinner a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [innerHom_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := congrArg Subtype.val (h ⟨x, hx⟩)
    have h2 := innerRep_spec hinner a x hx
    simp only [Subgroup.coe_mul] at h1
    have h3 : (a : G) * x * (a : G)⁻¹ = x := by rw [h2, ← h1, mul_inv_cancel_right]
    calc x * a = (a : G) * x * (a : G)⁻¹ * a := by rw [h3]
      _ = a * x := by group
  · intro h y
    apply Subtype.ext
    have h1 := innerRep_spec hinner a y y.2
    have h2 := h y y.2
    simp only [Subgroup.coe_mul]
    have h3 : (innerRep hinner a : G) * y * (innerRep hinner a : G)⁻¹ = y := by
      rw [← h1, ← h2, mul_inv_cancel_right]
    calc (y : G) * (innerRep hinner a : G) =
        (innerRep hinner a : G) * y * (innerRep hinner a : G)⁻¹ * innerRep hinner a := by
          rw [h3]
      _ = (innerRep hinner a : G) * y := by group

theorem card_range_innerHom_mul (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) :
    Nat.card (innerHom hinner).range *
      Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) = Nat.card A := by
  have hker : (innerHom hinner).ker = (Subgroup.centralizer (L : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, innerHom_eq_one_iff, Subgroup.mem_subgroupOf]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (innerHom hinner)).toEquiv.symm,
    show Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) =
      Nat.card (innerHom hinner).ker by
        rw [hker, inf_comm]
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm.trans
          (by rw [Subgroup.inf_subgroupOf_right])]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

theorem pow_three_eq_one_of_inv {L : Subgroup G} (hZ : Nat.card (Subgroup.center L) = 3)
    {v g : L} (hv3 : v ^ 3 ∈ Subgroup.center L)
    (hg : ((g * v * g⁻¹ : L) : L ⧸ Subgroup.center L) = ((v⁻¹ : L) : L ⧸ Subgroup.center L)) :
    v ^ 3 = 1 := by
  rw [QuotientGroup.eq] at hg
  set w := g * v * g⁻¹ with hw
  have hz3 : (w⁻¹ * v⁻¹) ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨_, hg⟩)
    rw [hZ] at h1
    simpa using congrArg Subtype.val h1
  have hcomm : Commute w⁻¹ v⁻¹ := by
    have h1 : w⁻¹ = (w⁻¹ * v⁻¹) * v := by group
    rw [h1]
    exact Commute.mul_left (Subgroup.mem_center_iff.mp hg v⁻¹).symm
      (Commute.inv_right (Commute.refl v))
  have hw3 : w ^ 3 = v ^ 3 := by
    rw [hw, conj_pow, Subgroup.mem_center_iff.mp hv3 g, mul_inv_cancel_right]
  rw [hcomm.mul_pow, inv_pow, inv_pow, hw3] at hz3
  have h6 : v ^ 3 * v ^ 3 = 1 := by
    have := congrArg (fun t => (t * (v ^ 3) * (v ^ 3))) hz3
    simpa [mul_assoc] using this.symm
  have h9 : (v ^ 3) ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨_, hv3⟩)
    rw [hZ] at h1
    simpa using congrArg Subtype.val h1
  calc v ^ 3 = (v ^ 3) ^ 3 * (v ^ 3 * v ^ 3)⁻¹ := by group
    _ = 1 := by rw [h9, h6]; group

end Res417Three

open Res417Three

section Certs


variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerInConf417.isHeisCentral_of_inverting (h : IsInnerInConf417 L A E c m)
    (hZ : Nat.card (Subgroup.center L) = 3) (hm : m = 3)
    (hS27 : ¬ 27 ∣ Nat.card (L ⧸ Subgroup.center L))
    (hinv : ∀ P : Subgroup (L ⧸ Subgroup.center L), Nat.card P = 9 →
      ∃ g : L ⧸ Subgroup.center L, ∀ x ∈ P, g * x * g⁻¹ = x⁻¹) :
    IsHeisCentral ↥(A ⊔ L) ↥L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAmax, hcard, hAc, hc3, -, -, -⟩ := h.2.2.2.2.1
  have hAel := hAmax.prop
  have hA27 : Nat.card A = 27 := by rw [hcard, hm]; norm_num
  have hLq : IsQuasisimple L := h.2.2.1.1
  have : Group.IsPerfect L := hLq.1
  have hcL : c ∈ L := h.2.2.2.2.2.2.2.2.2
  have hcA : c ∈ A := h.mem_A
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := h.2.2.2.2.2.1
  have hcC := h.mem_centralizer
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hLC : L ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hcL, hcC⟩) ?_
    rw [CFSG.GroupTheory.inf_centralizer_eq_map_center,
      Subgroup.card_map_of_injective L.subtype_injective, hZ, Nat.card_zpowers, hc3]
  obtain ⟨v, hv1, hv2⟩ : ∃ v : A → L, (∀ a : A, ∀ x ∈ L,
      (a : G) * x * (a : G)⁻¹ = (v a : G) * x * (v a : G)⁻¹) ∧
      ∀ a, innerHom h.inner a = (v a : L ⧸ Subgroup.center L) :=
    ⟨innerRep h.inner, innerRep_spec h.inner, innerHom_apply h.inner⟩
  have hR9 : Nat.card (innerHom h.inner).range = 9 := by
    have h1 := card_range_innerHom_mul h.inner
    rw [hAc, Nat.card_zpowers, hc3, hA27] at h1
    omega
  set ρ := innerHom h.inner with hρ
  have hv3Z : ∀ a : A, v a ^ 3 ∈ Subgroup.center L := by
    intro a
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hAel.2 a a.2)
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hv2, ← map_pow, ha3, map_one]
  obtain ⟨g₀, hg₀⟩ := hinv ρ.range hR9
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g₀
  have hv3 : ∀ a : A, v a ^ 3 = 1 := by
    intro a
    refine pow_three_eq_one_of_inv hZ (hv3Z a) (g := g) ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      ← hv2]
    exact hg₀ _ ⟨a, rfl⟩
  have hdec : ∀ a ∈ A, ∃ w : L, (w : G) ^ 3 = 1 ∧ a * w = w * a ∧
      a * (w : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro a ha
    refine ⟨v ⟨a, ha⟩, by simpa using congrArg Subtype.val (hv3 ⟨a, ha⟩), ?_, ?_⟩
    · have h1 := hv1 ⟨a, ha⟩ _ (v ⟨a, ha⟩).2
      have h2 : a * (v ⟨a, ha⟩ : G) * a⁻¹ = v ⟨a, ha⟩ := by
        rw [h1, mul_inv_cancel_right]
      calc a * (v ⟨a, ha⟩ : G) = a * (v ⟨a, ha⟩ : G) * a⁻¹ * a := by group
        _ = (v ⟨a, ha⟩ : G) * a := by rw [h2]
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : (v ⟨a, ha⟩ : G)⁻¹ * x * v ⟨a, ha⟩ ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem (v ⟨a, ha⟩).2) hx) (v ⟨a, ha⟩).2
      have h1 := hv1 ⟨a, ha⟩ _ hx'
      have h2 : a * ((v ⟨a, ha⟩ : G)⁻¹ * x * v ⟨a, ha⟩) * a⁻¹ = x := by
        rw [h1]; group
      calc x * (a * (v ⟨a, ha⟩ : G)⁻¹) =
          a * ((v ⟨a, ha⟩ : G)⁻¹ * x * v ⟨a, ha⟩) * a⁻¹ * (a * (v ⟨a, ha⟩ : G)⁻¹) := by
            rw [h2]
        _ = a * (v ⟨a, ha⟩ : G)⁻¹ * x := by group
  have hnc : ∃ a b : A, (v a : G) * v b ≠ v b * v a := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    set f := QuotientGroup.mk' (Subgroup.center L) with hf
    set Pt := ρ.range.comap f with hPt
    have hR3 : IsPGroup 3 ρ.range := IsPGroup.of_card (n := 2) (by rw [hR9]; norm_num)
    have hK3 : IsPGroup 3 f.ker := by
      rw [hf, QuotientGroup.ker_mk']
      exact IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
    obtain ⟨P, hP⟩ := (hR3.comap_of_ker_isPGroup f hK3).exists_le_sylow
    have hle1 : ρ.range ≤ (P : Subgroup L).map f := by
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) ρ.range]
      exact Subgroup.map_mono hP
    have hcardle : Nat.card ((P : Subgroup L).map f) ≤ Nat.card ρ.range := by
      obtain ⟨k, hk⟩ := (P.isPGroup'.map f).exists_card_eq
      have hdvd := Subgroup.card_subgroup_dvd_card ((P : Subgroup L).map f)
      rw [hk] at hdvd ⊢
      rw [hR9]
      by_contra hlt
      have hk3 : 3 ≤ k := by
        by_contra hk3
        have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact hS27 ((Nat.pow_dvd_pow 3 hk3).trans hdvd)
    have heq := Subgroup.eq_of_le_of_card_ge hle1 hcardle
    have hPle : (P : Subgroup L) ≤ Pt := by
      rw [hPt, heq]
      exact Subgroup.le_comap_map f _
    have hrep : ∀ x ∈ (P : Subgroup L), ∃ a : A, ∃ z ∈ Subgroup.center L, x = v a * z := by
      intro x hx
      obtain ⟨a, ha⟩ := hPle hx
      refine ⟨a, (v a)⁻¹ * x, ?_, by group⟩
      rw [← QuotientGroup.eq]
      rw [hv2] at ha
      exact ha
    have hPc : ∀ x ∈ (P : Subgroup L), ∀ y ∈ (P : Subgroup L), x * y = y * x := by
      intro x hx y hy
      obtain ⟨a, z, hz, rfl⟩ := hrep x hx
      obtain ⟨b, z', hz', rfl⟩ := hrep y hy
      have hab : v a * v b = v b * v a := Subtype.ext (hall a b)
      have hz1 := Subgroup.mem_center_iff.mp hz
      have hz2 := Subgroup.mem_center_iff.mp hz'
      calc v a * z * (v b * z') = v a * (z * v b) * z' := by group
        _ = v a * (v b * z) * z' := by rw [hz1]
        _ = v a * v b * (z * z') := by group
        _ = v b * v a * (z' * z) := by rw [hab, hz1 z']
        _ = v b * (v a * z') * z := by group
        _ = v b * (z' * v a) * z := by rw [hz2]
        _ = v b * z' * (v a * z) := by group
    have hcP : (⟨c, hcL⟩ : L) ∈ (P : Subgroup L) := hP (by
      rw [Subgroup.mem_comap, hf, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).mpr h.mem_center]
      exact one_mem _)
    have hmem := CFSG.ShultStronglyClosedTI.central_element_mem_sylow_derived P
      ⟨⟨c, hcL⟩, hcP⟩ h.mem_center
    have hbot : commutator (P : Subgroup L) = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subtype.ext (hPc y y.2 x x.2)
    rw [hbot, Subgroup.mem_bot] at hmem
    have hc1 : c = 1 := congrArg Subtype.val (congrArg Subtype.val hmem)
    rw [hc1, orderOf_one] at hc3
    omega
  set U : Subgroup G := (A ⊔ L) ⊓ Subgroup.centralizer (L : Set G) with hU
  have hUL : U ⊔ L = A ⊔ L := by
    apply le_antisymm (sup_le inf_le_left le_sup_right)
    refine sup_le (fun a ha => ?_) le_sup_right
    obtain ⟨w, -, -, hwC⟩ := hdec a ha
    have haw : a * (w : G)⁻¹ ∈ U :=
      ⟨mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (inv_mem w.2)), hwC⟩
    have : a = a * (w : G)⁻¹ * w := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left haw) (Subgroup.mem_sup_right w.2)
  have hUinf : U ⊓ L = Subgroup.zpowers c := by
    rw [← hLC]
    ext x
    simp only [Subgroup.mem_inf, hU]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨⟨Subgroup.mem_sup_right h2, h1⟩, h2⟩
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    obtain ⟨huAL, huC⟩ := Subgroup.mem_inf.mp hu
    have hmul : u ∈ (A : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A L hAN]
      exact huAL
    obtain ⟨a, ha, l, hl, hu'⟩ := hmul
    have hu'' : u = a * l := hu'.symm
    subst hu''
    obtain ⟨w, hw3, hwa, hwC⟩ := hdec a ha
    have hwl : (w : G) * l ∈ Subgroup.zpowers c := by
      rw [← hLC]
      refine Subgroup.mem_inf.mpr ⟨mul_mem w.2 hl, ?_⟩
      have : (w : G) * l = (a * (w : G)⁻¹)⁻¹ * (a * l) := by group
      rw [this]
      exact mul_mem (inv_mem hwC) huC
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwl
    have hal : a * l = (a * (w : G)⁻¹) * c ^ k := by rw [hk]; group
    rw [hal]
    have hca : Commute c a := hAcomm c hcA a ha
    have hcw : Commute c (w : G) := (Subgroup.mem_centralizer_iff.mp hcC w w.2).symm
    have hc1 : Commute (a * (w : G)⁻¹) (c ^ k) :=
      ((hca.mul_right hcw.inv_right).symm).zpow_right k
    have hc2 : Commute a (w : G)⁻¹ := Commute.inv_right hwa
    rw [hc1.mul_pow, hc2.mul_pow, hAel.2 a ha, inv_pow, hw3, inv_one, one_mul, one_mul,
      ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hc3',
      _root_.one_zpow]
  have hUnc : ¬ ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := by
    intro hUc
    obtain ⟨a₁, a₂, hv12⟩ := hnc
    have hC : ∀ a : A, (a : G) * (v a : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      intro a
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : (v a : G)⁻¹ * x * v a ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem (v a).2) hx) (v a).2
      have h1 := hv1 a _ hx'
      have h2 : (a : G) * ((v a : G)⁻¹ * x * v a) * (a : G)⁻¹ = x := by rw [h1]; group
      calc x * ((a : G) * (v a : G)⁻¹) =
          (a : G) * ((v a : G)⁻¹ * x * v a) * (a : G)⁻¹ * ((a : G) * (v a : G)⁻¹) := by
            rw [h2]
        _ = (a : G) * (v a : G)⁻¹ * x := by group
    have hu₁ : (a₁ : G) * (v a₁ : G)⁻¹ ∈ U :=
      ⟨mul_mem (Subgroup.mem_sup_left a₁.2) (Subgroup.mem_sup_right (inv_mem (v a₁).2)), hC a₁⟩
    have hu₂ : (a₂ : G) * (v a₂ : G)⁻¹ ∈ U :=
      ⟨mul_mem (Subgroup.mem_sup_left a₂.2) (Subgroup.mem_sup_right (inv_mem (v a₂).2)), hC a₂⟩
    have hcu := hUc _ hu₁ _ hu₂
    obtain ⟨u₁, hu₁d⟩ : ∃ u, u = (a₁ : G) * (v a₁ : G)⁻¹ := ⟨_, rfl⟩
    obtain ⟨u₂, hu₂d⟩ : ∃ u, u = (a₂ : G) * (v a₂ : G)⁻¹ := ⟨_, rfl⟩
    rw [← hu₁d, ← hu₂d] at hcu
    have hu₂v₁ : u₂ * v a₁ = v a₁ * u₂ := by
      rw [hu₂d]
      exact (Subgroup.mem_centralizer_iff.mp (hC a₂) _ (v a₁).2).symm
    have hu₁v₂ : u₁ * v a₂ = v a₂ * u₁ := by
      rw [hu₁d]
      exact (Subgroup.mem_centralizer_iff.mp (hC a₁) _ (v a₂).2).symm
    have ha₁ : (a₁ : G) = u₁ * v a₁ := by rw [hu₁d]; group
    have ha₂ : (a₂ : G) = u₂ * v a₂ := by rw [hu₂d]; group
    apply hv12
    have h1 := hAcomm a₁ a₁.2 a₂ a₂.2
    rw [ha₁, ha₂] at h1
    have h' : u₁ * u₂ * ((v a₁ : G) * v a₂) = u₁ * u₂ * ((v a₂ : G) * v a₁) :=
      calc u₁ * u₂ * ((v a₁ : G) * v a₂) = u₁ * (u₂ * v a₁) * v a₂ := by group
        _ = u₁ * (v a₁ * u₂) * v a₂ := by rw [hu₂v₁]
        _ = u₁ * v a₁ * (u₂ * v a₂) := by group
        _ = u₂ * v a₂ * (u₁ * v a₁) := h1
        _ = u₂ * (v a₂ * u₁) * v a₁ := by group
        _ = u₂ * (u₁ * v a₂) * v a₁ := by rw [hu₁v₂]
        _ = u₂ * u₁ * ((v a₂ : G) * v a₁) := by group
        _ = u₁ * u₂ * ((v a₂ : G) * v a₁) := by rw [hcu]
    exact mul_left_cancel h'
  have hcommUL : ∀ x ∈ U, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hcardUL := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U L hcommUL).1
  rw [hUL, hUinf, Nat.card_zpowers, hc3] at hcardUL
  have hcardAL : Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) =
      Nat.card A * Nat.card L := by
    have : ((L.subgroupOf (A ⊔ L))).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
    have h1 := card_sup_mul_card_inf_of_normal (A.subgroupOf (A ⊔ L)) (L.subgroupOf (A ⊔ L))
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self,
      Subgroup.card_top, ← inf_subgroupOf,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans le_sup_left)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ L)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : L ≤ A ⊔ L)).toEquiv] at h1
    exact h1
  rw [hA27] at hcardAL
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have h81 : Nat.card U * Nat.card (A ⊓ L : Subgroup G) = 81 := by
    have h1 : Nat.card U * Nat.card (A ⊓ L : Subgroup G) * Nat.card L = 81 * Nat.card L := by
      calc Nat.card U * Nat.card (A ⊓ L : Subgroup G) * Nat.card L =
          Nat.card U * Nat.card L * Nat.card (A ⊓ L : Subgroup G) := by ring
        _ = Nat.card (A ⊔ L : Subgroup G) * 3 * Nat.card (A ⊓ L : Subgroup G) := by
            rw [hcardUL]
        _ = 3 * (Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G)) := by ring
        _ = 81 * Nat.card L := by rw [hcardAL]; ring
    exact Nat.eq_of_mul_eq_mul_right hLpos h1
  have hAL3 : 3 ∣ Nat.card (A ⊓ L : Subgroup G) := by
    have h1 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ⟨hcA, hcL⟩ :
      Subgroup.zpowers c ≤ A ⊓ L)
    rwa [Nat.card_zpowers, hc3] at h1
  have hU27 : Nat.card U = 27 := by
    have hdvd : Nat.card U ∣ 3 ^ 4 := ⟨_, h81.symm⟩
    obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have hk4' : k = 4 := by omega
      subst hk4'
      rw [hk] at h81
      have := Nat.le_of_dvd (by omega) hAL3
      omega
    have hcomm : k ≤ 2 → ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := by
      intro hk2 u hu u' hu'
      have hU : IsMulCommutative U := by
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
        · rw [pow_zero] at hk
          have : Subsingleton U := (Nat.card_eq_one_iff_unique.mp hk).1
          exact ⟨⟨fun x y => Subsingleton.elim _ _⟩⟩
        · rw [pow_one] at hk
          have := isCyclic_of_prime_card hk
          infer_instance
        · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
      exact congrArg Subtype.val (hU.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
    rcases (show k ≤ 2 ∨ k = 3 by omega) with hk2 | rfl
    · exact absurd (hcomm hk2) hUnc
    · rw [hk]; norm_num
  refine ⟨U.subgroupOf (A ⊔ L), L.subgroupOf (A ⊔ L), ?_, ?_, ?_,
    ⟨Subgroup.subgroupOfEquivOfLe le_sup_right⟩, ?_⟩
  · rw [← Subgroup.subgroupOf_sup inf_le_left le_sup_right, hUL, Subgroup.subgroupOf_self]
  · intro u hu w hw
    rw [Subgroup.mem_subgroupOf] at hu hw
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hu.2 _ hw).symm)
  · apply isHeisThree_of
    · rw [← hU27]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      have := hU3 _ (Subgroup.mem_subgroupOf.mp x.2)
      simpa using this
    · intro hcomm
      apply hUnc
      intro u hu u' hu'
      have h1 := hcomm.is_comm.comm ⟨⟨u, hu.1⟩, Subgroup.mem_subgroupOf.mpr hu⟩
        ⟨⟨u', hu'.1⟩, Subgroup.mem_subgroupOf.mpr hu'⟩
      exact congrArg (fun x : ↥(U.subgroupOf (A ⊔ L)) => ((x : ↥(A ⊔ L)) : G)) h1
  · rw [← inf_subgroupOf, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((inf_le_right : U ⊓ L ≤ L).trans le_sup_right)).toEquiv.symm, hUinf, Nat.card_zpowers,
      hc3]

end Certs

section CertsA7M22

theorem item417InA7M22_holds
    : Item417InA7M22 := by
  intro G _ _ L A E c m hconf hX
  have hLq := hconf.2.2.1.1
  have : Group.IsPerfect L := hLq.1
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hZ3 := hconf.isPGroup_center fun p hp hp3 =>
      CFSG.RankThree.PartOne.Mult.alternating_center_small_primes (by norm_num) e hp hp3
    have hZ := hconf.card_center_eq_three (Census.card_center_dvd_three_of_A7 hLq hZ3 e)
    have hm := hconf.eq_three_of_pRank_le_two e (pRank_le_two_of_not_dvd fun h27 => by
      have h1 := h27.trans (card_alternatingGroup_dvd 7)
      revert h1
      decide)
    have hS27 : ¬ 27 ∣ Nat.card (L ⧸ Subgroup.center L) := by
      rw [Nat.card_congr e.toEquiv]
      intro h27
      have h1 := h27.trans (card_alternatingGroup_dvd 7)
      revert h1
      decide
    have hH := hconf.isHeisCentral_of_inverting hZ hm hS27 fun P hP9 => by
      obtain ⟨g, -, hg⟩ := Sec17.Proof1721.ks1721Invert_alt7 ⟨e⟩ hP9
      exact ⟨g, hg⟩
    exact Or.inr (Or.inl ⟨hm, hH, Or.inl ⟨hZ, ⟨e⟩⟩⟩)
  · have hXc : Nonempty (NativeSporadic.M22 ≃* NativeSporadic.Carrier .M22) := ⟨MulEquiv.refl _⟩
    obtain ⟨eX⟩ := hXc
    have hZ3 := hconf.isPGroup_center fun p hp hp3 =>
      not_dvd_center_of_spor12 (s := .M22) (by simp [spor12]) (e.trans eX) hp hp3
    have hZ := hconf.card_center_eq_three (Census.card_center_dvd_three_of_M22 hLq hZ3 e)
    have ht := CFSG.RankThree.Asc83Table.M22.table (L := NativeSporadic.M22) ⟨eX⟩
    have hm := hconf.eq_three_of_pRank_le_two e ht.2.1.le
    have hS27 : ¬ 27 ∣ Nat.card (L ⧸ Subgroup.center L) := by
      rw [Nat.card_congr e.toEquiv, Census.card_m22_eq]
      decide
    have hH := hconf.isHeisCentral_of_inverting hZ hm hS27 fun P hP9 => by
      obtain ⟨g, -, hg⟩ := Sec17.Proof1721.ks1721Invert_m22 ⟨e⟩ hP9
      exact ⟨g, hg⟩
    exact Or.inr (Or.inl ⟨hm, hH, Or.inr ⟨hZ, ⟨e⟩⟩⟩)

end CertsA7M22

end CFSG.RankThree.PartTwo.Sec4
