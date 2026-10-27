module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SFano
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

@[expose] def Pair (A B : Subgroup D) (z : D) (V : Subgroup D)
    (s₀ s₁ s₂ s₃ s₄ : CosetGeom (A ⊔ B) A B) : Prop :=
  ∀ x ∈ Vv V s₀, x ∉ Vv V s₁ → ∀ y ∈ Vv V s₄, y ∉ Vv V s₃ →
    x * y * x⁻¹ * y⁻¹ ∈ Zv z s₂ ∧ x * y * x⁻¹ * y⁻¹ ≠ 1

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem pair_smul {s₀ s₁ s₂ s₃ s₄ : CosetGeom (A ⊔ B) A B}
    (hp : Pair A B z V s₀ s₁ s₂ s₃ s₄) (g : ↥(A ⊔ B)) :
    Pair A B z V (g • s₀) (g • s₁) (g • s₂) (g • s₃) (g • s₄) := by
  intro x hx hx' y hy hy'
  rw [Vv_smul h.natural.reduced.2.1, mem_conjSub] at hx hy hx' hy'
  obtain ⟨h1, h2⟩ := hp ((g : D)⁻¹ * x * g) hx hx' ((g : D)⁻¹ * y * g) hy hy'
  have e : (g : D)⁻¹ * (x * y * x⁻¹ * y⁻¹) * g = ((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * y * g) *
      ((g : D)⁻¹ * x * g)⁻¹ * ((g : D)⁻¹ * y * g)⁻¹ := by group
  constructor
  · rw [Zv_smul h.normalizes_zpowers, mem_conjSub, e]
    exact h1
  · intro e1
    apply h2
    rw [← e, e1]
    group

theorem relIndex_Vv_adj [Finite D] (hU : Nat.card (conjClosure V B) = 8)
    {u v : CosetGeom (A ⊔ B) A B} (huv : (graph (A ⊔ B) A B).Adj u v) (hu : vtype u = false)
    (hv : vtype v = true) : (Vv V u).relIndex (Vv V v) = 2 := by
  have h8 := Subgroup.relIndex_mul_card (Vv V u) (Vv V v)
  rw [inf_of_le_left (Vv_le_Vv_of_adj huv hu), h.card_Vv_A hu, h.card_Vv_B hU hv] at h8
  omega

theorem ballStab_one_le_centralizer [Finite D] {u : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    {y x : D} (hy : y ∈ ballStab 1 u) (hx : x ∈ Vv V u) : y * x * y⁻¹ = x := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hu
  rw [ballStab_smul, ballStab_one_γ₀_eq_pCoreOf h.gold, mem_conjSub] at hy
  rw [Vv_smul_γ₀ h.natural.reduced.2.1, mem_conjSub] at hx
  rw [← h.natural.centralizer_eq] at hy
  have hc := Subgroup.mem_centralizer_iff.mp hy.2 _ hx
  have hc' : ((g : D)⁻¹ * y * g) * ((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * y * g)⁻¹ =
      (g : D)⁻¹ * x * g := mul_inv_eq_iff_eq_mul.mpr hc.symm
  have e : y * x * y⁻¹ = (g : D) * (((g : D)⁻¹ * y * g) * ((g : D)⁻¹ * x * g) *
      ((g : D)⁻¹ * y * g)⁻¹) * (g : D)⁻¹ := by group
  rw [e, hc']
  group

theorem far_label [Finite D] {c α s₀ s₁ : CosetGeom (A ⊔ B) A B} (hc : vtype c = true)
    (h1 : (graph (A ⊔ B) A B).Adj c α) (h2 : (graph (A ⊔ B) A B).Adj α s₀)
    (h3 : (graph (A ⊔ B) A B).Adj s₀ s₁) (n02 : c ≠ s₀) (n13 : α ≠ s₁) {a : D}
    (ha : a ∈ Zv z c) (e : a ≠ 1) : a ∈ Vv V s₀ ∧ a ∉ Vv V s₁ := by
  have hα : vtype α = false := vtype_eq_false_of_adj h1 hc
  have hs₀ : vtype s₀ = true := vtype_eq_true_of_adj h2 hα
  exact ⟨Vv_le_Vv_of_adj h2 hα (h.Zv_le_Vv h1.symm hα ha),
    h.not_mem_Vv_of_mem_Zv hs₀ h2.symm h3 n13 h1.symm n02 ha e⟩

theorem pair_of_symConfigFive [Finite D] (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = 5) {p : ℕ → CosetGeom (A ⊔ B) A B}
    {γ : CosetGeom (A ⊔ B) A B} (hcfg : SymConfigFive A B V p γ) :
    Pair A B z V (p 1) (p 2) (p 3) (p 4) (p 5) := by
  have hb' : critDist (A ⊔ B) A B V = 4 + 1 := hb
  obtain ⟨x₀, hx₀, w₀, hw₀, hc0, -, -⟩ := h.symConfigFive_data hU hb hcfg
  obtain ⟨hp0, hp, -, hγ, -⟩ := hcfg
  have ht1 : vtype (p 1) = true := hp.vtype_true_of_odd rfl hp0 (by omega) (by decide)
  have ht2 : vtype (p 2) = false := hp.vtype_false_of_even rfl hp0 (by omega) (by decide)
  have ht3 : vtype (p 3) = true := hp.vtype_true_of_odd rfl hp0 (by omega) (by decide)
  have ht4 : vtype (p 4) = false := hp.vtype_false_of_even rfl hp0 (by omega) (by decide)
  have ht5 : vtype (p 5) = true := hp.vtype_true_of_odd rfl hp0 le_rfl (by decide)
  have a12 : (graph (A ⊔ B) A B).Adj (p 1) (p 2) := hp.adj (i := 1) (by omega)
  have a23 : (graph (A ⊔ B) A B).Adj (p 2) (p 3) := hp.adj (i := 2) (by omega)
  have a34 : (graph (A ⊔ B) A B).Adj (p 3) (p 4) := hp.adj (i := 3) (by omega)
  have a45 : (graph (A ⊔ B) A B).Adj (p 4) (p 5) := hp.adj (i := 4) (by omega)
  have hd : ∀ i j, i ≤ j → j ≤ 5 → CosetGeom.dist (p i) (p j) = j - i := hp
  have hdc : ∀ i j, i ≤ j → j ≤ 5 → CosetGeom.dist (p j) (p i) = j - i := fun i j hij hj => by
    rw [CosetGeom.dist_comm]; exact hd i j hij hj
  have hγt : vtype γ = false := vtype_eq_false_of_adj hγ ht5
  have hw₅ : w₀ ∈ Vv V (p 5) := Vv_le_Vv_of_adj hγ.symm hγt hw₀
  have hcomm : ∀ x ∈ Vv V (p 1), ∀ y ∈ Vv V (p 5), x * y * x⁻¹ * y⁻¹ ∈ Zv z (p 3) := by
    intro x hx y hy
    have := h.commutator_mem_Vv_inf hU hb' ht1 ht5 a12 a45.symm
      (by have := hd 1 5 (by omega) le_rfl; omega) (by have := hd 1 4 (by omega) (by omega); omega)
      (by have := hdc 1 5 (by omega) le_rfl; omega) (by have := hdc 2 5 (by omega) le_rfl; omega)
      hx hy
    exact h.mem_Zv_of_mem_Vv_of_mem_Vv ht3 a23.symm a34 (hp.ne (i := 2) (j := 4) (by omega)
      (by omega)) this.1 this.2
  have hstab₁ : ∀ x ∈ Vv V (p 1), x ∈ stab (p 3) := fun x hx =>
    ballStab_le_stab_of_dist_le (n := 4) (by have := hd 1 3 (by omega) (by omega); omega)
      (h.Vv_le_ballStab_B hb' ht1 hx)
  have hstab₅ : ∀ y ∈ Vv V (p 5), y ∈ stab (p 3) := fun y hy =>
    ballStab_le_stab_of_dist_le (n := 4) (by have := hdc 3 5 (by omega) le_rfl; omega)
      (h.Vv_le_ballStab_B hb' ht5 hy)
  have hV₂ : Vv V (p 2) ≤ Vv V (p 1) := Vv_le_Vv_of_adj a12.symm ht2
  have hV₄ : Vv V (p 4) ≤ Vv V (p 5) := Vv_le_Vv_of_adj a45 ht4
  have hker₂ : ∀ x ∈ Vv V (p 2), ∀ y ∈ Vv V (p 5), x * y = y * x := by
    intro x hx y hy
    have hy1 : y ∈ ballStab 1 (p 2) :=
      ballStab_le_ballStab_of_dist rfl (u := p 5) (v := p 2) (n := 4) (m := 1)
        (by have := hdc 2 5 (by omega) le_rfl; omega) (h.Vv_le_ballStab_B hb' ht5 hy)
    exact (mul_inv_eq_iff_eq_mul.mp (h.ballStab_one_le_centralizer ht2 hy1 hx)).symm
  have hker₄ : ∀ x ∈ Vv V (p 1), ∀ y ∈ Vv V (p 4), x * y = y * x := by
    intro x hx y hy
    have hx1 : x ∈ ballStab 1 (p 4) :=
      ballStab_le_ballStab_of_dist rfl (u := p 1) (v := p 4) (n := 4) (m := 1)
        (by have := hd 1 4 (by omega) (by omega); omega) (h.Vv_le_ballStab_B hb' ht1 hx)
    exact mul_inv_eq_iff_eq_mul.mp (h.ballStab_one_le_centralizer ht4 hx1 hy)
  have LA : ∀ k ∈ Vv V (p 2), ∀ x' ∈ Vv V (p 1), ∀ y ∈ Vv V (p 5),
      (k * x') * y * (k * x')⁻¹ * y⁻¹ = x' * y * x'⁻¹ * y⁻¹ := by
    intro k hk x' hx' y hy
    have hky : k * y = y * k := hker₂ k hk y hy
    have hky' : k⁻¹ * y⁻¹ = y⁻¹ * k⁻¹ :=
      calc k⁻¹ * y⁻¹ = (y * k)⁻¹ := (mul_inv_rev y k).symm
        _ = (k * y)⁻¹ := by rw [hky]
        _ = y⁻¹ * k⁻¹ := mul_inv_rev k y
    have hkc : k * (x' * y * x'⁻¹ * y⁻¹) * k⁻¹ = x' * y * x'⁻¹ * y⁻¹ :=
      h.conj_eq_of_mem_stab_Zv ht3 (hstab₁ k (hV₂ hk)) (hcomm x' hx' y hy)
    calc (k * x') * y * (k * x')⁻¹ * y⁻¹ = k * (x' * y * x'⁻¹) * (k⁻¹ * y⁻¹) := by group
      _ = k * (x' * y * x'⁻¹) * (y⁻¹ * k⁻¹) := by rw [hky']
      _ = k * (x' * y * x'⁻¹ * y⁻¹) * k⁻¹ := by group
      _ = x' * y * x'⁻¹ * y⁻¹ := hkc
  have LB : ∀ k ∈ Vv V (p 4), ∀ x' ∈ Vv V (p 1), ∀ y ∈ Vv V (p 5),
      x' * (k * y) * x'⁻¹ * (k * y)⁻¹ = x' * y * x'⁻¹ * y⁻¹ := by
    intro k hk x' hx' y hy
    have hxk : x' * k = k * x' := hker₄ x' hx' k hk
    have hkc : k * (x' * y * x'⁻¹ * y⁻¹) * k⁻¹ = x' * y * x'⁻¹ * y⁻¹ :=
      h.conj_eq_of_mem_stab_Zv ht3 (hstab₅ k (hV₄ hk)) (hcomm x' hx' y hy)
    calc x' * (k * y) * x'⁻¹ * (k * y)⁻¹ = (x' * k) * y * x'⁻¹ * y⁻¹ * k⁻¹ := by group
      _ = (k * x') * y * x'⁻¹ * y⁻¹ * k⁻¹ := by rw [hxk]
      _ = k * (x' * y * x'⁻¹ * y⁻¹) * k⁻¹ := by group
      _ = x' * y * x'⁻¹ * y⁻¹ := hkc
  have hx₀n : x₀ ∉ Vv V (p 2) := fun hx => hc0 (by
    have := hker₂ x₀ hx w₀ hw₅
    calc x₀ * w₀ * x₀⁻¹ * w₀⁻¹ = (w₀ * x₀) * x₀⁻¹ * w₀⁻¹ := by rw [this]
      _ = 1 := by group)
  have hw₀n : w₀ ∉ Vv V (p 4) := fun hw => hc0 (by
    have := hker₄ x₀ hx₀ w₀ hw
    calc x₀ * w₀ * x₀⁻¹ * w₀⁻¹ = (w₀ * x₀) * x₀⁻¹ * w₀⁻¹ := by rw [this]
      _ = 1 := by group)
  have hrel₂ := h.relIndex_Vv_adj hU a12.symm ht2 ht1
  have hrel₄ := h.relIndex_Vv_adj hU a45 ht4 ht5
  intro x hx hxn y hy hyn
  have hk : x * x₀⁻¹ ∈ Vv V (p 2) :=
    mul_inv_mem_of_relIndex_eq_two hrel₂ hx hx₀ hxn hx₀n
  have hk' : y * w₀⁻¹ ∈ Vv V (p 4) :=
    mul_inv_mem_of_relIndex_eq_two hrel₄ hy hw₅ hyn hw₀n
  have hxe : x = (x * x₀⁻¹) * x₀ := by group
  have hye : y = (y * w₀⁻¹) * w₀ := by group
  have key : x * y * x⁻¹ * y⁻¹ = x₀ * w₀ * x₀⁻¹ * w₀⁻¹ := by
    calc x * y * x⁻¹ * y⁻¹ = ((x * x₀⁻¹) * x₀) * y * ((x * x₀⁻¹) * x₀)⁻¹ * y⁻¹ := by
          rw [← hxe]
      _ = x₀ * y * x₀⁻¹ * y⁻¹ := LA _ hk x₀ hx₀ y hy
      _ = x₀ * ((y * w₀⁻¹) * w₀) * x₀⁻¹ * ((y * w₀⁻¹) * w₀)⁻¹ := by rw [← hye]
      _ = x₀ * w₀ * x₀⁻¹ * w₀⁻¹ := LB _ hk' x₀ hx₀ w₀ hw₅
  rw [key]
  exact ⟨by
    have := hcomm x₀ hx₀ w₀ hw₅
    exact this, hc0⟩

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
