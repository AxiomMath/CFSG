module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SNbr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VBase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WInt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem exists_three_cosets {X Y : Subgroup D} (hcard : 2 * Nat.card Y < Nat.card X) :
    ∃ u₁ ∈ X, u₁ ∉ Y ∧ ∃ u₂ ∈ X, u₂ ∉ Y ∧ u₁⁻¹ * u₂ ∉ Y := by
  have hne : ¬ X ≤ Y := fun hle => by
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨u₁, hu₁X, hu₁Y⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  refine ⟨u₁, hu₁X, hu₁Y, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsub : (X : Set D) ⊆ (Y : Set D) ∪ (fun x => u₁ * x) '' (Y : Set D) := by
    intro u₂ hu₂
    by_cases hY : u₂ ∈ Y
    · exact Or.inl hY
    · exact Or.inr ⟨u₁⁻¹ * u₂, hcon u₂ hu₂ hY, by group⟩
  have h1 : (X : Set D).ncard ≤ ((Y : Set D) ∪ (fun x => u₁ * x) '' (Y : Set D)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (Y : Set D) ((fun x => u₁ * x) '' (Y : Set D))
  have h3 : ((fun x => u₁ * x) '' (Y : Set D)).ncard = (Y : Set D).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective u₁)
  have h4 : (X : Set D).ncard = Nat.card X := (Nat.card_coe_set_eq (X : Set D)).symm
  have h5 : (Y : Set D).ncard = Nat.card Y := (Nat.card_coe_set_eq (Y : Set D)).symm
  omega

theorem three_mul_card_le {X Y : Subgroup D} (hYX : Y ≤ X) {u₁ u₂ : D} (hu₁ : u₁ ∈ X)
    (hu₂ : u₂ ∈ X) (h1 : u₁ ∉ Y) (h2 : u₂ ∉ Y) (h12 : u₁⁻¹ * u₂ ∉ Y) :
    3 * Nat.card Y ≤ Nat.card X := by
  have hd01 : Disjoint (Y : Set D) ((fun x => u₁ * x) '' (Y : Set D)) := by
    rw [Set.disjoint_left]
    rintro a ha ⟨b, hb, hab⟩
    apply h1
    have e : u₁ * b = a := hab
    have : u₁ = a * b⁻¹ := by rw [← e]; group
    rw [this]
    exact Y.mul_mem ha (Y.inv_mem hb)
  have hd02 : Disjoint (Y : Set D) ((fun x => u₂ * x) '' (Y : Set D)) := by
    rw [Set.disjoint_left]
    rintro a ha ⟨b, hb, hab⟩
    apply h2
    have e : u₂ * b = a := hab
    have : u₂ = a * b⁻¹ := by rw [← e]; group
    rw [this]
    exact Y.mul_mem ha (Y.inv_mem hb)
  have hd12 : Disjoint ((fun x => u₁ * x) '' (Y : Set D)) ((fun x => u₂ * x) '' (Y : Set D)) := by
    rw [Set.disjoint_left]
    rintro a ⟨b, hb, hab⟩ ⟨c, hc, hac⟩
    apply h12
    have e1 : u₁ * b = a := hab
    have e2 : u₂ * c = a := hac
    have : u₁⁻¹ * u₂ = b * c⁻¹ := by
      calc u₁⁻¹ * u₂ = u₁⁻¹ * (u₂ * c) * c⁻¹ := by group
        _ = u₁⁻¹ * (u₁ * b) * c⁻¹ := by rw [e2, ← e1]
        _ = b * c⁻¹ := by group
    rw [this]
    exact Y.mul_mem hb (Y.inv_mem hc)
  have hsub : (Y : Set D) ∪ (fun x => u₁ * x) '' (Y : Set D) ∪ (fun x => u₂ * x) '' (Y : Set D) ⊆
      (X : Set D) := by
    rintro a ((ha | ⟨b, hb, hab⟩) | ⟨b, hb, hab⟩)
    · exact hYX ha
    · rw [← hab]
      exact X.mul_mem hu₁ (hYX hb)
    · rw [← hab]
      exact X.mul_mem hu₂ (hYX hb)
  have hc1 : ((fun x => u₁ * x) '' (Y : Set D)).ncard = (Y : Set D).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective u₁)
  have hc2 : ((fun x => u₂ * x) '' (Y : Set D)).ncard = (Y : Set D).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective u₂)
  have hu : ((Y : Set D) ∪ (fun x => u₁ * x) '' (Y : Set D) ∪
      (fun x => u₂ * x) '' (Y : Set D)).ncard = 3 * (Y : Set D).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hd02, hd12⟩) (Set.toFinite _)
      (Set.toFinite _), Set.ncard_union_eq hd01 (Set.toFinite _) (Set.toFinite _), hc1, hc2]
    ring
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 : (X : Set D).ncard = Nat.card X := (Nat.card_coe_set_eq (X : Set D)).symm
  have h5 : (Y : Set D).ncard = Nat.card Y := (Nat.card_coe_set_eq (Y : Set D)).symm
  omega

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_other_nbrs {w u : CosetGeom (A ⊔ B) A B} (hu : (graph (A ⊔ B) A B).Adj w u) :
    ∃ a b, (graph (A ⊔ B) A B).Adj w a ∧ (graph (A ⊔ B) A B).Adj w b ∧ a ≠ u ∧ b ≠ u ∧
      a ≠ b := by
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Set.ncard_eq_three.mp (h.ncard_nbrs w)
  have hmem : ∀ y ∈ ({a, b, c} : Set (CosetGeom (A ⊔ B) A B)),
      (graph (A ⊔ B) A B).Adj w y := fun y hy => by
    have : y ∈ nbrs w := hset ▸ hy
    exact this
  have hu' : u ∈ ({a, b, c} : Set (CosetGeom (A ⊔ B) A B)) := by
    rw [← hset]
    exact hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu'
  rcases hu' with rfl | rfl | rfl
  · exact ⟨b, c, hmem b (by simp), hmem c (by simp), hab.symm, hac.symm, hbc⟩
  · exact ⟨a, c, hmem a (by simp), hmem c (by simp), hab, hbc.symm, hac⟩
  · exact ⟨a, b, hmem a (by simp), hmem b (by simp), hac, hbc, hab⟩

theorem smul_eq_of_not_mem_ballStab {w u a b : CosetGeom (A ⊔ B) A B}
    (hu : (graph (A ⊔ B) A B).Adj w u) (ha : (graph (A ⊔ B) A B).Adj w a)
    (hb : (graph (A ⊔ B) A B).Adj w b) (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b) {y : D}
    (hyw : y ∈ stab w) (hyu : y ∈ stab u) (hyQ : y ∉ ballStab 1 w) :
    (⟨y, stab_le w hyw⟩ : ↥(A ⊔ B)) • a = b := by
  set g : ↥(A ⊔ B) := ⟨y, stab_le w hyw⟩ with hg
  have hgw : g • w = w := smul_eq_of_mem_stab hyw
  have hgu : g • u = u := smul_eq_of_mem_stab hyu
  have hga : (graph (A ⊔ B) A B).Adj w (g • a) := by
    have := (smul_adj g).mpr ha
    rwa [hgw] at this
  have hne1 : g • a ≠ u := fun e => hau (smul_left_cancel g (e.trans hgu.symm))
  have hne2 : g • a ≠ a := fun e =>
    hyQ (h.mem_ballStab_one_of_fix_two' hu ha hau.symm hyw hyu (mem_stab_of_smul_eq e))
  by_contra hne
  exact h.nbr_four hu ha hb hga hau.symm hbu.symm hne1.symm hab hne2.symm (Ne.symm hne)

theorem exists_comm_triple (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    {x₀ x₁ : CosetGeom (A ⊔ B) A B} (hx₀ : vtype x₀ = false)
    (h01 : (graph (A ⊔ B) A B).Adj x₀ x₁)
    (hWab : Vn V 2 x₀ ≤ Subgroup.centralizer (Vn V 2 x₀ : Set D))
    {y : D} (hy : y ∈ stab x₀ ⊓ stab x₁) (hyQ : y ∉ ballStab 1 x₀) :
    ∃ w₁ ∈ Vn V 2 x₀, ∃ w₂ ∈ Vn V 2 x₀, ∃ w₃ ∈ Vn V 2 x₀,
      w₁ * y * w₁⁻¹ * y⁻¹ ∉ Vv V x₀ ∧ w₂ * y * w₂⁻¹ * y⁻¹ ∉ Vv V x₀ ∧
      w₃ * y * w₃⁻¹ * y⁻¹ ∉ Vv V x₀ ∧
      w₃ * y * w₃⁻¹ * y⁻¹ = (w₁ * y * w₁⁻¹ * y⁻¹)⁻¹ * (w₂ * y * w₂⁻¹ * y⁻¹) := by
  obtain ⟨β', β'', hβ', hβ'', n1, n2, n12⟩ := h.exists_other_nbrs h01
  have hβ't : vtype β' = true := vtype_eq_true_of_adj hβ' hx₀
  have hswap := h.smul_eq_of_not_mem_ballStab h01 hβ' hβ'' n1 n2 n12 hy.1 hy.2 hyQ
  have hUU : Vv V β'' = conjSub y (Vv V β') := by
    rw [← hswap]
    exact Vv_smul h.natural.reduced.2.1 _ β'
  have hUW : Vv V β' ≤ Vn V 2 x₀ := by
    refine (Vv_B_le_iff hβ't).mpr fun l hl => ?_
    have hlt : vtype l = false := vtype_eq_false_of_adj hl hβ't
    refine Vv_le_Vn hlt ?_
    have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl x₀ β' l
    have h2 : CosetGeom.dist x₀ β' = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hβ'
    have h3 : CosetGeom.dist β' l = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hl
    omega
  have hVU : Vv V x₀ ≤ Vv V β' := Vv_le_Vv_of_adj hβ' hx₀
  have hyW : y ∈ Subgroup.normalizer (Vn V 2 x₀ : Set D) := h.stab_le_normalizer_Vn 2 x₀ hy.1
  have hyV : y ∈ Subgroup.normalizer (Vv V x₀ : Set D) :=
    stab_le_normalizer_Vv h.natural.reduced.2.1 x₀ hy.1
  have hI : Vv V β' ⊓ Vv V β'' ≤ Vv V x₀ := hI1 x₀ β' β'' hx₀ hβ' hβ'' n12
  have key : ∀ u ∈ Vv V β', u * y * u⁻¹ * y⁻¹ ∈ Vv V x₀ → u ∈ Vv V x₀ := by
    intro u hu hd
    have e : y * u⁻¹ * y⁻¹ = u⁻¹ * (u * y * u⁻¹ * y⁻¹) := by group
    have h1 : y * u⁻¹ * y⁻¹ ∈ Vv V β' := by
      rw [e]
      exact (Vv V β').mul_mem ((Vv V β').inv_mem hu) (hVU hd)
    have h2 : y * u⁻¹ * y⁻¹ ∈ Vv V β'' := by
      rw [hUU]
      exact mul_mem_conjSub ((Vv V β').inv_mem hu)
    have h3 : y * u⁻¹ * y⁻¹ ∈ Vv V x₀ := hI ⟨h1, h2⟩
    have h4 : u⁻¹ ∈ Vv V x₀ := (Subgroup.mem_normalizer_iff.mp hyV u⁻¹).mpr h3
    simpa using (Vv V x₀).inv_mem h4
  have hab : ∀ a ∈ Vn V 2 x₀, ∀ b ∈ Vn V 2 x₀, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hWab ha) b hb).symm
  have hconj : ∀ a ∈ Vn V 2 x₀, y * a * y⁻¹ ∈ Vn V 2 x₀ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hyW a).mp ha
  have hhom : ∀ a ∈ Vv V β', ∀ b ∈ Vv V β',
      (a⁻¹ * b) * y * (a⁻¹ * b)⁻¹ * y⁻¹ =
        (a * y * a⁻¹ * y⁻¹)⁻¹ * (b * y * b⁻¹ * y⁻¹) := by
    intro a ha b hb
    have haW := hUW ha
    have hbW := hUW hb
    have hc : y * a * y⁻¹ ∈ Vn V 2 x₀ := hconj a haW
    have hd : y * b * y⁻¹ ∈ Vn V 2 x₀ := hconj b hbW
    have hcc : (y * a * y⁻¹) * (a⁻¹ * b * (y * b * y⁻¹)⁻¹) =
        (a⁻¹ * b * (y * b * y⁻¹)⁻¹) * (y * a * y⁻¹) :=
      hab _ hc _ ((Vn V 2 x₀).mul_mem ((Vn V 2 x₀).mul_mem ((Vn V 2 x₀).inv_mem haW) hbW)
        ((Vn V 2 x₀).inv_mem hd))
    calc (a⁻¹ * b) * y * (a⁻¹ * b)⁻¹ * y⁻¹
        = (a⁻¹ * b * (y * b * y⁻¹)⁻¹) * (y * a * y⁻¹) := by group
      _ = (y * a * y⁻¹) * (a⁻¹ * b * (y * b * y⁻¹)⁻¹) := hcc.symm
      _ = (a * y * a⁻¹ * y⁻¹)⁻¹ * (b * y * b⁻¹ * y⁻¹) := by group
  have hc4 : Nat.card (Vv V x₀) = 4 := h.card_Vv_A hx₀
  have hc16 : Nat.card (Vv V β') = 16 := h.card_Vv_B_of_card hU hβ't
  obtain ⟨u₁, hu₁, hu₁V, u₂, hu₂, hu₂V, hu₁₂⟩ :=
    exists_three_cosets (X := Vv V β') (Y := Vv V x₀) (by rw [hc4, hc16]; norm_num)
  refine ⟨u₁, hUW hu₁, u₂, hUW hu₂, u₁⁻¹ * u₂,
    hUW ((Vv V β').mul_mem ((Vv V β').inv_mem hu₁) hu₂), fun hd => hu₁V (key u₁ hu₁ hd),
    fun hd => hu₂V (key u₂ hu₂ hd),
    fun hd => hu₁₂ (key _ ((Vv V β').mul_mem ((Vv V β').inv_mem hu₁) hu₂) hd),
    hhom u₁ hu₁ u₂ hu₂⟩

theorem false_of_comm_mem_cosets (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    {x₀ x₁ : CosetGeom (A ⊔ B) A B} (hx₀ : vtype x₀ = false)
    (h01 : (graph (A ⊔ B) A B).Adj x₀ x₁)
    (hWab : Vn V 2 x₀ ≤ Subgroup.centralizer (Vn V 2 x₀ : Set D))
    {y : D} (hy : y ∈ stab x₀ ⊓ stab x₁) (hyQ : y ∉ ballStab 1 x₀) {f : D}
    (hcomm : ∀ w ∈ Vn V 2 x₀, w * y * w⁻¹ * y⁻¹ ∈ Vv V x₀ ∨
      f⁻¹ * (w * y * w⁻¹ * y⁻¹) ∈ Vv V x₀) : False := by
  obtain ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, h1, h2, h3, h123⟩ :=
    h.exists_comm_triple hU hI1 hx₀ h01 hWab hy hyQ
  have g1 := (hcomm w₁ hw₁).resolve_left h1
  have g2 := (hcomm w₂ hw₂).resolve_left h2
  apply h3
  rw [h123]
  have e : (w₁ * y * w₁⁻¹ * y⁻¹)⁻¹ * (w₂ * y * w₂⁻¹ * y⁻¹) =
      (f⁻¹ * (w₁ * y * w₁⁻¹ * y⁻¹))⁻¹ * (f⁻¹ * (w₂ * y * w₂⁻¹ * y⁻¹)) := by group
  rw [e]
  exact (Vv V x₀).mul_mem ((Vv V x₀).inv_mem g1) g2

theorem false_of_comm_mem_card_le (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    {x₀ x₁ : CosetGeom (A ⊔ B) A B} (hx₀ : vtype x₀ = false)
    (h01 : (graph (A ⊔ B) A B).Adj x₀ x₁)
    (hWab : Vn V 2 x₀ ≤ Subgroup.centralizer (Vn V 2 x₀ : Set D))
    {y : D} (hy : y ∈ stab x₀ ⊓ stab x₁) (hyQ : y ∉ ballStab 1 x₀) {P : Subgroup D}
    (hP : Nat.card P ≤ 4) {ζ : D} (hζP : ζ ∈ P) (hζV : ζ ∈ Vv V x₀) (hζ : ζ ≠ 1)
    (hcomm : ∀ w ∈ Vn V 2 x₀, w * y * w⁻¹ * y⁻¹ ∈ P) : False := by
  obtain ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, h1, h2, h3, h123⟩ :=
    h.exists_comm_triple hU hI1 hx₀ h01 hWab hy hyQ
  have hZP : Subgroup.zpowers ζ ≤ P := Subgroup.zpowers_le.mpr hζP
  have hZV : Subgroup.zpowers ζ ≤ Vv V x₀ := Subgroup.zpowers_le.mpr hζV
  have hcard : 2 ≤ Nat.card (Subgroup.zpowers ζ) := by
    rw [Nat.card_zpowers]
    have hpos : 0 < orderOf ζ := orderOf_pos ζ
    have : orderOf ζ ≠ 1 := fun e => hζ (orderOf_eq_one_iff.mp e)
    omega
  have h3' : (w₁ * y * w₁⁻¹ * y⁻¹)⁻¹ * (w₂ * y * w₂⁻¹ * y⁻¹) ∉ Vv V x₀ := by
    rw [← h123]
    exact h3
  have := three_mul_card_le hZP (hcomm w₁ hw₁) (hcomm w₂ hw₂) (fun hd => h1 (hZV hd))
    (fun hd => h2 (hZV hd)) (fun hd => h3' (hZV hd))
  omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
