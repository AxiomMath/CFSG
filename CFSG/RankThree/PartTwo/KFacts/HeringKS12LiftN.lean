module

import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.QTK.SectionLiftB
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts

private theorem ks12N_eq_one_of_sq_cube {X : Type} [Group X] {u : X} (h2 : u * u = 1)
    (h3 : u ^ 3 = 1) : u = 1 := by
  calc u = u * (u * u) := by rw [h2, mul_one]
    _ = u ^ 3 := (pow_three u).symm
    _ = 1 := h3

private theorem ks12N_exists_mem_eq_mul {X : Type} [Group X] {Z : Subgroup X} {a b : X}
    (h : (a : X ⧸ Z) = b) : ∃ z ∈ Z, b = a * z :=
  ⟨a⁻¹ * b, QuotientGroup.eq.mp h, (mul_inv_cancel_left a b).symm⟩

private theorem ks12N_commutator_eq_one {X : Type} [Group X] {a b c g z₁ z₂ : X}
    (hcen : ∀ h : X, h * c = c * h) (hz₁ : ∀ h : X, h * z₁ = z₁ * h)
    (hz₂ : ∀ h : X, h * z₂ = z₂ * h) (hc3 : c ^ 3 = 1) (hc : b * a = a * b * c)
    (ha : g * a * g⁻¹ = a⁻¹ * z₁) (hb : g * b * g⁻¹ = b * z₂) : c = 1 := by
  have hgc : g * c * g⁻¹ = c := by
    rw [hcen g, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (b * z₂) * (a⁻¹ * z₁) = (a⁻¹ * z₁) * (b * z₂) * c := by
    calc (b * z₂) * (a⁻¹ * z₁) = (g * b * g⁻¹) * (g * a * g⁻¹) := by rw [hb, ha]
      _ = g * (b * a) * g⁻¹ := by group
      _ = g * (a * b * c) * g⁻¹ := by rw [hc]
      _ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹) := by group
      _ = (a⁻¹ * z₁) * (b * z₂) * c := by rw [ha, hb, hgc]
  have hL : (b * z₂) * (a⁻¹ * z₁) = b * a⁻¹ * (z₁ * z₂) := by
    calc (b * z₂) * (a⁻¹ * z₁) = b * (z₂ * a⁻¹) * z₁ := by group
      _ = b * (a⁻¹ * z₂) * z₁ := by rw [← hz₂ a⁻¹]
      _ = b * a⁻¹ * (z₂ * z₁) := by group
      _ = b * a⁻¹ * (z₁ * z₂) := by rw [hz₁ z₂]
  have hR : (a⁻¹ * z₁) * (b * z₂) = a⁻¹ * b * (z₁ * z₂) := by
    calc (a⁻¹ * z₁) * (b * z₂) = a⁻¹ * (z₁ * b) * z₂ := by group
      _ = a⁻¹ * (b * z₁) * z₂ := by rw [hz₁ b]
      _ = a⁻¹ * b * (z₁ * z₂) := by group
  rw [hL, hR] at hconj
  have hcancel : b * a⁻¹ = a⁻¹ * b * c := by
    apply mul_right_cancel (b := z₁ * z₂)
    calc b * a⁻¹ * (z₁ * z₂) = a⁻¹ * b * (z₁ * z₂) * c := hconj
      _ = a⁻¹ * b * ((z₁ * z₂) * c) := by group
      _ = a⁻¹ * b * (c * (z₁ * z₂)) := by rw [hcen (z₁ * z₂)]
      _ = a⁻¹ * b * c * (z₁ * z₂) := by group
  have hW : c = b⁻¹ * a * b * a⁻¹ := by
    calc c = (a⁻¹ * b)⁻¹ * (a⁻¹ * b * c) := by group
      _ = (a⁻¹ * b)⁻¹ * (b * a⁻¹) := by rw [← hcancel]
      _ = b⁻¹ * a * b * a⁻¹ := by group
  have hcinv : c⁻¹ = c := by
    calc c⁻¹ = (b * a)⁻¹ * (a * b) := by rw [hc]; group
      _ = a⁻¹ * (b⁻¹ * a * b * a⁻¹) * a := by group
      _ = a⁻¹ * c * a := by rw [hW]
      _ = c := by rw [hcen a⁻¹]; group
  have hsq : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [hcinv]
      _ = 1 := mul_inv_cancel c
  exact ks12N_eq_one_of_sq_cube hsq hc3

private theorem ks12N_cube_eq_one {X : Type} [Group X] {a g z : X}
    (hcen : ∀ h : X, h * a ^ 3 = a ^ 3 * h) (hz : ∀ h : X, h * z = z * h) (hz3 : z ^ 3 = 1)
    (hA3 : (a ^ 3) ^ 3 = 1) (ha : g * a * g⁻¹ = a⁻¹ * z) : a ^ 3 = 1 := by
  have hc : Commute a⁻¹ z := hz a⁻¹
  have h1 : g * a ^ 3 * g⁻¹ = (a ^ 3)⁻¹ := by
    rw [← conj_pow, ha, hc.mul_pow, hz3, mul_one, inv_pow]
  have h2 : g * a ^ 3 * g⁻¹ = a ^ 3 := by
    rw [hcen g, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : a ^ 3 * a ^ 3 = 1 := by
    calc a ^ 3 * a ^ 3 = a ^ 3 * (g * a ^ 3 * g⁻¹) := by rw [h2]
      _ = a ^ 3 * (a ^ 3)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  exact ks12N_eq_one_of_sq_cube h3 hA3

private theorem ks12N_closure_props {X : Type} [Group X] {S : Set X}
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hSe : ∀ a ∈ S, a ^ 3 = 1) :
    IsMulCommutative (Subgroup.closure S) ∧ (∀ w ∈ Subgroup.closure S, w ^ 3 = 1) := by
  have hpair : S.Pairwise Commute := fun a ha b hb _ => hSc a ha b hb
  have hcomm : ∀ u ∈ Subgroup.closure S, ∀ v ∈ Subgroup.closure S, u * v = v * u := by
    intro u hu v hv
    exact congrArg Subtype.val
      ((Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  refine ⟨Subgroup.isMulCommutative_closure hpair, ?_⟩
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact hSe x hx
  | one => exact one_pow 3
  | mul x y hx hy hxe hye =>
    rw [(show Commute x y from hcomm x hx y hy).mul_pow, hxe, hye, one_mul]
  | inv x _ hxe => rw [inv_pow, hxe, inv_one]

private theorem ks12N_map_closure {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    {a b : X} :
    (Subgroup.closure (({a, b} : Set X) ∪ (Z : Set X))).map (QuotientGroup.mk' Z) =
      Subgroup.closure ({(a : X ⧸ Z), (b : X ⧸ Z)} : Set (X ⧸ Z)) := by
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rcases hs with hs | hs
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · have h1 : QuotientGroup.mk' Z s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
      rw [h1]
      exact Subgroup.one_mem _
  · apply Subgroup.closure_mono
    rintro _ (rfl | rfl)
    · exact ⟨a, Or.inl (Or.inl rfl), rfl⟩
    · exact ⟨b, Or.inl (Or.inr rfl), rfl⟩

private theorem ks12N_card_eq_three_mul {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    (hZ3 : Nat.card Z = 3) {E : Subgroup X} (hZE : Z ≤ E) {P : Subgroup (X ⧸ Z)}
    (hP : E.map (QuotientGroup.mk' Z) = P) : Nat.card E = 3 * Nat.card P := by
  obtain ⟨f, hf⟩ : ∃ f : E →* X ⧸ Z, f = (QuotientGroup.mk' Z).comp E.subtype := ⟨_, rfl⟩
  have hrange : f.range = P := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hP]
  have hker_map : f.ker.map E.subtype = Z := by
    ext w
    constructor
    · intro hw
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hw
      have he' : ((e : X) : X ⧸ Z) = 1 := by
        have h1 := MonoidHom.mem_ker.mp he
        rw [hf] at h1
        exact h1
      exact (QuotientGroup.eq_one_iff _).mp he'
    · intro hw
      refine Subgroup.mem_map.mpr ⟨⟨w, hZE hw⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      rw [hf]
      exact (QuotientGroup.eq_one_iff w).mpr hw
  have hker : Nat.card f.ker = 3 := by
    have h := Subgroup.card_map_of_injective (K := f.ker) (f := E.subtype)
      (Subgroup.subtype_injective E)
    rw [hker_map, hZ3] at h
    exact h.symm
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker, hrange] at h1
  exact h1.symm

public theorem exists_commuting_lifts {X : Type} [Group X] (Z : Subgroup X) [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3)
    {x y g h : X ⧸ Z} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (hgx : g * x * g⁻¹ = x⁻¹) (hgy : g * y * g⁻¹ = y) (hhy : h * y * h⁻¹ = y⁻¹) :
    ∃ x₀ y₀ : X, (QuotientGroup.mk x₀ : X ⧸ Z) = x ∧ (QuotientGroup.mk y₀ : X ⧸ Z) = y ∧
      x₀ * y₀ = y₀ * x₀ ∧ x₀ ^ 3 = 1 ∧ y₀ ^ 3 = 1 := by
  have hZcen : ∀ z ∈ Z, ∀ g : X, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (hZc hz) g
  have hZexp : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Z))
    rw [hZ3] at h
    simpa using congrArg Subtype.val h
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective h
  have hm_xy : ((x₀ * y₀ : X) : X ⧸ Z) = ((y₀ * x₀ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hxy
  obtain ⟨c, hcZ, hc⟩ := ks12N_exists_mem_eq_mul hm_xy
  have hm1 : ((g₀ * x₀ * g₀⁻¹ : X) : X ⧸ Z) = ((x₀⁻¹ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    exact hgx
  obtain ⟨z₁, hz₁, hgx'⟩ := ks12N_exists_mem_eq_mul hm1.symm
  have hm2 : ((g₀ * y₀ * g₀⁻¹ : X) : X ⧸ Z) = ((y₀ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hgy
  obtain ⟨z₂, hz₂, hgy'⟩ := ks12N_exists_mem_eq_mul hm2.symm
  have hm3 : ((h₀ * y₀ * h₀⁻¹ : X) : X ⧸ Z) = ((y₀⁻¹ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    exact hhy
  obtain ⟨z₃, hz₃, hhy'⟩ := ks12N_exists_mem_eq_mul hm3.symm
  have hc1 : c = 1 :=
    ks12N_commutator_eq_one (hZcen c hcZ) (hZcen z₁ hz₁) (hZcen z₂ hz₂) (hZexp c hcZ) hc
      hgx' hgy'
  have hcomm : x₀ * y₀ = y₀ * x₀ := by
    rw [hc1, mul_one] at hc
    exact hc.symm
  have hx3Z : x₀ ^ 3 ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp ((QuotientGroup.mk_pow Z x₀ 3).trans hx3)
  have hy3Z : y₀ ^ 3 ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp ((QuotientGroup.mk_pow Z y₀ 3).trans hy3)
  exact ⟨x₀, y₀, rfl, rfl, hcomm,
    ks12N_cube_eq_one (hZcen _ hx3Z) (hZcen z₁ hz₁) (hZexp z₁ hz₁) (hZexp _ hx3Z) hgx',
    ks12N_cube_eq_one (hZcen _ hy3Z) (hZcen z₃ hz₃) (hZexp z₃ hz₃) (hZexp _ hy3Z) hhy'⟩

private theorem ks12N_elementary27 {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    (hZcen : ∀ z ∈ Z, ∀ g : X, g * z = z * g) (hZexp : ∀ z ∈ Z, z ^ 3 = 1)
    (hZ3 : Nat.card Z = 3) {x₀ y₀ : X} (hcomm : x₀ * y₀ = y₀ * x₀) (hx3 : x₀ ^ 3 = 1)
    (hy3 : y₀ ^ 3 = 1)
    (h9 : Nat.card (Subgroup.closure ({(x₀ : X ⧸ Z), (y₀ : X ⧸ Z)} : Set (X ⧸ Z))) = 9) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure (({x₀, y₀} : Set X) ∪ (Z : Set X))) ∧
      Nat.card (Subgroup.closure (({x₀, y₀} : Set X) ∪ (Z : Set X))) = 27 := by
  have hZF : Z ≤ Subgroup.closure (({x₀, y₀} : Set X) ∪ (Z : Set X)) := fun w hw =>
    Subgroup.subset_closure (Or.inr hw)
  have hSc : ∀ u ∈ (({x₀, y₀} : Set X) ∪ (Z : Set X)), ∀ v ∈ (({x₀, y₀} : Set X) ∪ (Z : Set X)),
      u * v = v * u := by
    intro u hu v hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hcomm
      · exact hcomm.symm
      · rfl
    · exact hZcen v hv u
    · exact (hZcen u hu v).symm
    · exact (hZcen u hu v).symm
  have hSe : ∀ u ∈ (({x₀, y₀} : Set X) ∪ (Z : Set X)), u ^ 3 = 1 := by
    intro u hu
    rcases hu with hu | hu
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact hx3
      · exact hy3
    · exact hZexp u hu
  obtain ⟨hFc, hFp⟩ := ks12N_closure_props hSc hSe
  refine ⟨⟨hFc, hFp⟩, ?_⟩
  have hmap := ks12N_card_eq_three_mul hZ3 hZF (ks12N_map_closure (Z := Z) (a := x₀) (b := y₀))
  rw [h9] at hmap
  omega

public theorem three_le_localRank_of_quotient_normalizer {X : Type} [Group X] [Finite X]
    (hZ3 : Nat.card (Subgroup.center X) = 3)
    {x y g h : X ⧸ Subgroup.center X} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (h9 : Nat.card (Subgroup.closure ({x, y} : Set (X ⧸ Subgroup.center X))) = 9)
    (hgx : g * x * g⁻¹ = x⁻¹) (hgy : g * y * g⁻¹ = y) (hhy : h * y * h⁻¹ = y⁻¹)
    {T : Subgroup (X ⧸ Subgroup.center X)} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hxT : x ∈ Subgroup.normalizer (T : Set (X ⧸ Subgroup.center X)))
    (hyT : y ∈ Subgroup.normalizer (T : Set (X ⧸ Subgroup.center X))) :
    3 ≤ CFSG.Assembly.RankThreeEven.localRank 3 X := by
  have hZcen : ∀ z ∈ Subgroup.center X, ∀ g : X, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp hz g
  have hZexp : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center X))
    rw [hZ3] at h
    simpa using congrArg Subtype.val h
  obtain ⟨x₀, y₀, rfl, rfl, hcomm, hx₀3, hy₀3⟩ :=
    exists_commuting_lifts (Subgroup.center X) le_rfl hZ3 hx3 hy3 hxy hgx hgy hhy
  obtain ⟨hFel, hFcard⟩ := ks12N_elementary27 hZcen hZexp hZ3 hcomm hx₀3 hy₀3 h9
  obtain ⟨C, hCne, hC2, hCN⟩ := CFSG.SectionRank.QTK.exists_two_subgroup_normalized hT1 hT2
  have hFN : Subgroup.closure (({x₀, y₀} : Set X) ∪ (Subgroup.center X : Set X)) ≤
      Subgroup.normalizer (C : Set X) := by
    rw [Subgroup.closure_le]
    rintro w (hw | hw)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hCN _ hxT
      · exact hCN _ hyT
    · refine hCN w ?_
      rw [(QuotientGroup.eq_one_iff w).mpr hw]
      exact Subgroup.one_mem _
  have hbdd : BddAbove
      {k | ∃ H : Subgroup X, CFSG.Assembly.IsTwoLocal H ∧ CFSG.Assembly.pRank 3 H = k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro _ ⟨H, -, rfl⟩
    obtain ⟨F, -, -, hF⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) H
    have h1 : CFSG.Open.pRank 3 H < 3 ^ CFSG.Open.pRank 3 H := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card F ≤ Nat.card X := Subgroup.card_le_card_group F
    change CFSG.Open.pRank 3 H ≤ Nat.card X
    omega
  exact (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hFN hFel
    (k := 3) (hFcard.trans (by norm_num : (27 : ℕ) = 3 ^ 3))).trans
    (le_csSup hbdd ⟨_, ⟨C, hCne, hC2, rfl⟩, rfl⟩)

end CFSG.RankThree.PartTwo.KFacts
