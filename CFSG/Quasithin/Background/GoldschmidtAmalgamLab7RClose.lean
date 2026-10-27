module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Ball
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SPush

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmL3

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem conj_mem_inf_pCoreOf (h : TwoSys A B z V c V₂) (h3 : GoldHyp3 A B z V)
    (hb : 5 ≤ critDist (A ⊔ B) A B V) {a v : D} (ha : a ∈ A) (hv : v ∈ V₂) :
    a * v * a⁻¹ ∈ pCoreOf 2 A ⊓ pCoreOf 2 B := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  set g : ↥(A ⊔ B) := ⟨a, (le_sup_left : A ≤ A ⊔ B) ha⟩ with hg
  set u : CosetGeom (A ⊔ B) A B := g • γ₁ (A ⊔ B) A B with hu
  have hNu : a * v * a⁻¹ ∈ Nm A B V V₂ u := by
    rw [hu, GoldAmLab6.Nm_smul hA hB, Nm_γ₁ hB, mem_conjSub]
    have e : (g : D)⁻¹ * (a * v * a⁻¹) * g = v := by
      show a⁻¹ * (a * v * a⁻¹) * a = v
      group
    rw [e]
    exact hv
  have hg0 : g • γ₀ (A ⊔ B) A B = γ₀ (A ⊔ B) A B :=
    smul_eq_of_mem_stab (by rw [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)]; exact ha)
  have hadj : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) u := by
    have := (smul_adj g).mpr (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B))
    rwa [hg0] at this
  have hd0 : CosetGeom.dist u (γ₀ (A ⊔ B) A B) = 1 := by
    rw [CosetGeom.dist_comm]
    exact dist_eq_one_iff_adj.mpr hadj
  have hd1 : CosetGeom.dist u (γ₁ (A ⊔ B) A B) ≤ 2 := by
    have h1 := CosetGeom.dist_triangle (G₁ := A) (G₂ := B) rfl u (γ₀ (A ⊔ B) A B)
      (γ₁ (A ⊔ B) A B)
    have h2 : CosetGeom.dist (γ₀ (A ⊔ B) A B) (γ₁ (A ⊔ B) A B) = 1 :=
      dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
    omega
  refine ⟨?_, ?_⟩
  · rw [← GoldAmL3.ballStab_one_γ₀_eq_pCoreOf h.gold]
    exact GoldAmLab8.Nm_le_ballStab_of_dist h h3 (b := critDist (A ⊔ B) A B V) rfl u 1 _ hd0
      (by omega) hNu
  · rw [← GoldAmL3.ballStab_one_γ₁_eq_pCoreOf h.gold]
    exact GoldAmLab8.Nm_le_ballStab_of_dist h h3 (b := critDist (A ⊔ B) A B V) rfl u _ _ rfl
      (by omega) hNu

theorem exists_orderOf_eq_three (h : GoldHyp A B) : ∃ y ∈ B, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmul := Subgroup.relIndex_mul_card (A ⊓ B) B
  rw [inf_eq_left.mpr inf_le_right, h.relIndex_right] at hmul
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 ⟨_, hmul.symm⟩
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem le_sup_zpowers_of_orderOf_three (h : GoldHyp A B) {y : D} (hyB : y ∈ B)
    (hy3 : orderOf y = 3) : B ≤ (A ⊓ B) ⊔ Subgroup.zpowers y := by
  have hT2 : IsPGroup 2 ↥(A ⊓ B) := h.amalgam.toIsGoldschmidtVTriple.isPGroup_inf
  have hr : (A ⊓ B).relIndex B = 3 := h.relIndex_right
  have hTK : A ⊓ B ≤ (A ⊓ B) ⊔ Subgroup.zpowers y := le_sup_left
  have hKB : (A ⊓ B) ⊔ Subgroup.zpowers y ≤ B :=
    sup_le inf_le_right (Subgroup.zpowers_le.mpr hyB)
  have h1 := Subgroup.relIndex_mul_relIndex (A ⊓ B) ((A ⊓ B) ⊔ Subgroup.zpowers y) B hTK hKB
  rw [hr] at h1
  by_contra hBK
  have hne : ((A ⊓ B) ⊔ Subgroup.zpowers y).relIndex B ≠ 1 := fun h' =>
    hBK (Subgroup.relIndex_eq_one.mp h')
  have hdvd : ((A ⊓ B) ⊔ Subgroup.zpowers y).relIndex B ∣ 3 :=
    ⟨(A ⊓ B).relIndex ((A ⊓ B) ⊔ Subgroup.zpowers y), by rw [← h1, mul_comm]⟩
  have h3 : ((A ⊓ B) ⊔ Subgroup.zpowers y).relIndex B = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
  have h4 : (A ⊓ B).relIndex ((A ⊓ B) ⊔ Subgroup.zpowers y) = 1 := by
    rw [h3] at h1
    omega
  have hKT : (A ⊓ B) ⊔ Subgroup.zpowers y ≤ A ⊓ B := Subgroup.relIndex_eq_one.mp h4
  have hyT : y ∈ A ⊓ B :=
    hKT ((le_sup_right : Subgroup.zpowers y ≤ (A ⊓ B) ⊔ Subgroup.zpowers y)
      (Subgroup.mem_zpowers y))
  obtain ⟨k, hk⟩ := hT2 ⟨y, hyT⟩
  have hdy : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  rw [hy3] at hdy
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdy
  omega

theorem false_of_comm_mem (h : TwoSys A B z V c V₂) (h3 : GoldHyp3 A B z V)
    (hb : 5 ≤ critDist (A ⊔ B) A B V) {y : D} (hyB : y ∈ B) (hy3 : orderOf y = 3)
    (hRy : ∀ r ∈ pCoreOf 2 A ⊓ pCoreOf 2 B, y * r * y⁻¹ * r⁻¹ ∈ V₂) : False := by
  classical
  set W : Subgroup D := conjClosure V₂ A with hW
  have hWR : W ≤ pCoreOf 2 A ⊓ pCoreOf 2 B :=
    conjClosure_le fun a ha v hv => conj_mem_inf_pCoreOf h h3 hb ha hv
  have hV₂W : V₂ ≤ W := le_conjClosure V₂ A
  have hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro w hw
    have h1 : y * w * y⁻¹ * w⁻¹ ∈ W := hV₂W (hRy w (hWR hw))
    simpa [mul_assoc] using W.mul_mem h1 hw
  have hy2 : y * y = y⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    have : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
    calc y * (y * y) = y ^ 3 := (pow_three y).symm
      _ = 1 := this
  have hy'W : ∀ w ∈ W, y⁻¹ * w * y ∈ W := by
    intro w hw
    have e : y * (y * w * y⁻¹) * y⁻¹ = y⁻¹ * w * y := by
      calc y * (y * w * y⁻¹) * y⁻¹ = (y * y) * w * (y * y)⁻¹ := by group
        _ = y⁻¹ * w * (y⁻¹)⁻¹ := by rw [hy2]
        _ = y⁻¹ * w * y := by rw [inv_inv]
    rw [← e]
    exact hyW _ (hyW w hw)
  have hyN : y ∈ Subgroup.normalizer (W : Set D) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hyW w hw, fun hw => ?_⟩
    have := hy'W _ hw
    simpa [mul_assoc] using this
  have hAN : A ≤ Subgroup.normalizer (W : Set D) := le_normalizer_conjClosure V₂ A
  have hBN : B ≤ Subgroup.normalizer (W : Set D) :=
    (le_sup_zpowers_of_orderOf_three h.gold hyB hy3).trans
      (sup_le (inf_le_left.trans hAN) (Subgroup.zpowers_le.mpr hyN))
  have hWT : W ≤ A ⊓ B := hWR.trans (inf_le_left.trans h.gold.pCoreOf_left_le)
  have hbot : W = ⊥ := h.gold.eq_bot_of_normalizes hAN hBN hWT
  have hV₂ : V₂ = ⊥ := eq_bot_iff.mpr (hbot ▸ hV₂W)
  have h4 := h.nat₂.card_eq
  rw [hV₂, Subgroup.card_bot] at h4
  omega

end GoldAmLab7

end F6

end CFSG.Quasithin
