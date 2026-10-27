module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VCrit
public import CFSG.Quasithin.Background.GoldschmidtAmalgamVBBall
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RCoinc
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RInj
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem mul_inv_mem_ballStab_one {x y : CosetGeom (A ⊔ B) A B}
    (hxy : (graph (A ⊔ B) A B).Adj x y) {a b : D} (ha : a ∈ stab x ⊓ stab y)
    (hb : b ∈ stab x ⊓ stab y) (haQ : a ∉ ballStab 1 x) (hbQ : b ∉ ballStab 1 x) :
    a * b⁻¹ ∈ ballStab 1 x := by
  cases hvx : vtype x
  · obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hxy hvx
    have hA : stab (g • γ₀ (A ⊔ B) A B) = conjSub (g : D) A := by
      rw [stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B)]
    have hB : stab (g • γ₁ (A ⊔ B) A B) = conjSub (g : D) B := by
      rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B)]
    rw [hA, hB] at ha hb
    rw [ballStab_smul, h.ballStab_one_γ₀_eq, mem_conjSub] at haQ hbQ ⊢
    have h1 := GoldAmL3.mul_inv_mem_of_relIndex_eq_two h.gold.vertex_left.relIndex_pCoreOf_T
      ⟨mem_conjSub.mp ha.1, mem_conjSub.mp ha.2⟩ ⟨mem_conjSub.mp hb.1, mem_conjSub.mp hb.2⟩
      haQ hbQ
    have e : (g : D)⁻¹ * (a * b⁻¹) * g = ((g : D)⁻¹ * a * g) * ((g : D)⁻¹ * b * g)⁻¹ := by group
    rw [e]
    exact h1
  · have hvy : vtype y = false := vtype_eq_false_of_adj hxy hvx
    obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hxy.symm hvy
    have hA : stab (g • γ₀ (A ⊔ B) A B) = conjSub (g : D) A := by
      rw [stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B)]
    have hB : stab (g • γ₁ (A ⊔ B) A B) = conjSub (g : D) B := by
      rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B)]
    rw [hA, hB] at ha hb
    rw [ballStab_smul, h.ballStab_one_γ₁_eq, mem_conjSub] at haQ hbQ ⊢
    have h1 := GoldAmL3.mul_inv_mem_of_relIndex_eq_two h.gold.vertex_right.relIndex_pCoreOf_T
      ⟨mem_conjSub.mp ha.2, mem_conjSub.mp ha.1⟩ ⟨mem_conjSub.mp hb.2, mem_conjSub.mp hb.1⟩
      haQ hbQ
    have e : (g : D)⁻¹ * (a * b⁻¹) * g = ((g : D)⁻¹ * a * g) * ((g : D)⁻¹ * b * g)⁻¹ := by group
    rw [e]
    exact h1

theorem commutator_mem_Zv_of_mem_ballStab_one {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    {x w : D} (hx : x ∈ ballStab 1 v) (hw : w ∈ Vv V v) : x * w * x⁻¹ * w⁻¹ ∈ Zv z v := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [ballStab_smul, h.ballStab_one_γ₁_eq, mem_conjSub] at hx
  rw [Vv_smul h.natural.reduced.2.1, Vv_γ₁ le_sup_right h.natural.reduced.2.1,
    mem_conjSub] at hw
  rw [Zv_smul_γ₁ h.normalizes_zpowers, mem_conjSub]
  have hc := (h.pCoreOf_eq_centralizerMod.le hx).2.2 _ hw
  have e : (g : D)⁻¹ * (x * w * x⁻¹ * w⁻¹) * g = ((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * w * g) *
      ((g : D)⁻¹ * x * g)⁻¹ * ((g : D)⁻¹ * w * g)⁻¹ := by group
  rw [e]
  exact hc

omit [Finite D] in
theorem stab_centralizes_Zv {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) {g : D}
    (hg : g ∈ stab v) {x : D} (hx : x ∈ Zv z v) : g * x * g⁻¹ = x := by
  obtain ⟨k, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B), mem_conjSub] at hg
  rw [Zv_smul_γ₁ h.normalizes_zpowers, mem_conjSub] at hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hxe : x = (k : D) * z ^ n * (k : D)⁻¹ := by
    rw [hn]
    group
  have hbc : ((k : D)⁻¹ * g * k) * z ^ n * ((k : D)⁻¹ * g * k)⁻¹ = z ^ n := by
    have hz : ((k : D)⁻¹ * g * k) * z = z * ((k : D)⁻¹ * g * k) :=
      mul_inv_eq_iff_eq_mul.mp (h.central _ hg)
    have := (Commute.zpow_right (show Commute ((k : D)⁻¹ * g * k) z from hz) n).eq
    rw [this]
    group
  calc g * x * g⁻¹ = (k : D) * (((k : D)⁻¹ * g * k) * z ^ n * ((k : D)⁻¹ * g * k)⁻¹) *
        (k : D)⁻¹ := by
        rw [hxe]
        group
    _ = (k : D) * z ^ n * (k : D)⁻¹ := by rw [hbc]
    _ = x := hxe.symm

theorem Vv_le_centralizer_of_two_labels {y u₁ u₂ : CosetGeom (A ⊔ B) A B} (hy : vtype y = false)
    (h₁ : (graph (A ⊔ B) A B).Adj y u₁) (h₂ : (graph (A ⊔ B) A B).Adj y u₂) (hne : u₁ ≠ u₂)
    {H : Subgroup D} (hc₁ : Zv z u₁ ≤ Subgroup.centralizer (H : Set D))
    (hc₂ : Zv z u₂ ≤ Subgroup.centralizer (H : Set D)) :
    Vv V y ≤ Subgroup.centralizer (H : Set D) := by
  have hu₁ : vtype u₁ = true := vtype_eq_true_of_adj h₁ hy
  have hu₂ : vtype u₂ = true := vtype_eq_true_of_adj h₂ hy
  obtain ⟨c₀, hc₀, hc₀1⟩ := h.exists_ne_one_mem_Zv hu₂
  refine le_of_card_four (h.card_Vv_A hy) (h.card_Zv hu₁) (h.Zv_le_Vv h₁ hy) hc₁
    (h.Zv_le_Vv h₂ hy hc₀) (hc₂ hc₀) fun hc₀₁ => hne ?_
  exact h.eq_of_Zv_eq hy h₁ h₂
    (eq_of_card_two_of_mem (h.card_Zv hu₁) (h.card_Zv hu₂) hc₀₁ hc₀ hc₀1)

end GoldHyp3

structure TypeIConfig {D : Type*} [Group D] {A B : Subgroup D} (V : Subgroup D) (m : ℕ)
    (p : ℕ → CosetGeom (A ⊔ B) A B) : Prop where
  card : Nat.card (conjClosure V B) = 8
  critDist_eq : critDist (A ⊔ B) A B V = m + 1
  six_le : 6 ≤ m
  even : Even m
  start : p 0 = γ₀ (A ⊔ B) A B
  geo : IsGeo p (m + 1)
  crit : ¬ V ≤ ballStab 1 (p (m + 1))
  good : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v → Vv V v ≤ ballStab 1 (p (m - 1))
  typeI : Vv V (p (m + 1)) ≤ ballStab 1 (p 1)

namespace TypeIConfig

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIConfig V m p)

include c

omit [Finite D] in
theorem vtype_zero : vtype (p 0) = false := by
  rw [c.start]
  exact vtype_γ₀

omit [Finite D] in
theorem vtype_even {i : ℕ} (hi : i ≤ m + 1) (he : Even i) : vtype (p i) = false :=
  c.geo.vtype_false_of_even_start rfl c.vtype_zero hi he

omit [Finite D] in
theorem vtype_odd {i : ℕ} (hi : i ≤ m + 1) (ho : Odd i) : vtype (p i) = true :=
  c.geo.vtype_true_of_odd_start rfl c.vtype_zero hi ho

omit [Finite D] in
theorem adj {i : ℕ} (hi : i ≤ m) : (graph (A ⊔ B) A B).Adj (p i) (p (i + 1)) :=
  c.geo.adj (by omega)

omit [Finite D] in
theorem Vv_zero (h : GoldHyp3 A B z V) : Vv V (p 0) = V := by
  rw [c.start]
  exact Vv_γ₀ h.natural.reduced.2.1

omit [Finite D] in
theorem crit' (h : GoldHyp3 A B z V) : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)) := by
  rw [c.Vv_zero h]
  exact c.crit

theorem exists_u (h : GoldHyp3 A B z V) :
    ∃ u : D, u ∈ Vv V (p (m + 1)) ∧ u ∈ stab (p 0) ⊓ stab (p 1) ∧ u ∉ ballStab 1 (p 0) := by
  have hp := c.geo
  have hb := c.critDist_eq
  have hbt : vtype (p (m + 1)) = true := c.vtype_odd le_rfl c.even.add_one
  obtain ⟨x₀, hx₀V, hx₀Q⟩ := IsConcreteLE.not_le_iff_exists.1 (c.crit' h)
  have hx₀b : x₀ ∈ stab (p (m + 1)) :=
    h.Vv_le_stab_A hb c.vtype_zero (by rw [hp 0 (m + 1) (Nat.zero_le _) le_rfl]; omega) hx₀V
  obtain ⟨u, hu, hnc⟩ : ∃ u ∈ Vv V (p (m + 1)), x₀ * u * x₀⁻¹ * u⁻¹ ∉ Zv z (p (m + 1)) := by
    by_contra hcon
    push Not at hcon
    exact hx₀Q (h.mem_ballStab_one_of_commutator hbt hx₀b hcon)
  have huI : u ∈ ballStab 1 (p 1) := c.typeI hu
  refine ⟨u, hu, ⟨?_, ballStab_le_stab 1 _ huI⟩, fun huQ => hnc ?_⟩
  · refine ballStab_le_stab_of_dist_le (n := 1) ?_ huI
    have := hp 0 1 (by omega) (by omega)
    rw [CosetGeom.dist_comm]
    omega
  · have e1 := h.ballStab_one_le_centralizer_Vv c.vtype_zero huQ hx₀V
    have e2 : u * x₀ = x₀ * u := mul_inv_eq_iff_eq_mul.mp e1
    have e3 : x₀ * u * x₀⁻¹ * u⁻¹ = 1 := by
      rw [← e2]
      group
    rw [e3]
    exact one_mem _

theorem Zv_one_le (h : GoldHyp3 A B z V) : Zv z (p 1) ≤ Vv V (p m) := by
  obtain ⟨c', hc1, hcZ, hcV⟩ := h.coincidence_odd_I c.card c.critDist_eq c.geo c.start c.crit
    (c.vtype_odd le_rfl c.even.add_one) c.typeI
  exact le_of_card_two_of_mem (h.card_Zv (c.vtype_odd (by have := c.six_le; omega) odd_one)) hcZ
    hcV hc1

omit [Finite D] in
theorem exists_adj_Vv_le {l : CosetGeom (A ⊔ B) A B} (hl : vtype l = false)
    (hd : CosetGeom.dist (p 0) l ≤ 2) :
    ∃ v, (graph (A ⊔ B) A B).Adj (p 0) v ∧ Vv V l ≤ Vv V v := by
  by_cases hl0 : l = p 0
  · obtain ⟨v, hv⟩ := exists_adj (p 0)
    exact ⟨v, hv, hl0 ▸ Vv_le_Vv_of_adj hv c.vtype_zero⟩
  · have heven : Even (CosetGeom.dist (p 0) l) :=
      (vtype_eq_iff_even_dist rfl (p 0) l).mp (by rw [c.vtype_zero, hl])
    have hpos : CosetGeom.dist (p 0) l ≠ 0 := fun e => hl0 ((dist_eq_zero_iff rfl).mp e).symm
    have h2 : CosetGeom.dist (p 0) l = 1 + 1 := by
      obtain ⟨k, hk⟩ := heven
      omega
    obtain ⟨β, hβ, hβd⟩ := exists_adj_dist_eq rfl h2
    exact ⟨β, dist_eq_one_iff_adj.mp hβd, Vv_le_Vv_of_adj hβ hl⟩

omit [Finite D] in
theorem Vn_two_le : Vn V 2 (p 0) ≤ ballStab 1 (p (m - 1)) := by
  refine Vn_le_iff.mpr fun l hl hd => ?_
  obtain ⟨v, hv, hlv⟩ := c.exists_adj_Vv_le hl hd
  exact hlv.trans (c.good v hv)

end TypeIConfig

end GoldAmL3

end F6

end CFSG.Quasithin
