module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Chain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

section Geometry

variable {G : Type*} [Group G] {G₀ G₁ G₂ : Subgroup G}

theorem le_ballStab_succ_iff (hG : G₀ = G₁ ⊔ G₂) {α β : CosetGeom G₀ G₁ G₂}
    (hαβ : (graph G₀ G₁ G₂).Adj α β) {W : Subgroup G} (n : ℕ) :
    W ≤ ballStab (n + 1) α ↔ W ≤ stab α ∧ ∀ a ∈ stab α, conjSub a⁻¹ W ≤ ballStab n β := by
  constructor
  · intro hW
    refine ⟨hW.trans (ballStab_le_stab _ _), fun a ha => ?_⟩
    obtain ⟨ha0, ha1⟩ := mem_stab.mp ha
    have hadj : (graph G₀ G₁ G₂).Adj α ((⟨a, ha0⟩ : ↥G₀) • β) := by
      have := (smul_adj (⟨a, ha0⟩ : ↥G₀)).mpr hαβ
      rwa [ha1] at this
    have h1 := ballStab_succ_le_of_adj hadj n
    rw [ballStab_smul] at h1
    have h2 := hW.trans h1
    rwa [le_conjSub_iff] at h2
  · rintro ⟨hWα, hW⟩ x hx
    refine mem_ballStab.mpr fun δ hδ => ?_
    by_cases h0 : CosetGeom.dist α δ = 0
    · obtain rfl := (dist_eq_zero_iff hG).mp h0
      exact hWα hx
    · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero h0
      obtain ⟨β', hβ'adj, hβ'd⟩ := exists_adj_dist_eq hG (α := δ) (δ := α) (d := d)
        (by rw [CosetGeom.dist_comm]; exact hd)
      obtain ⟨g, hg, hgβ⟩ := stab_transitive_on_nbrs (show β ∈ nbrs α from hαβ)
        (show β' ∈ nbrs α from hβ'adj)
      have hx' : (g : G)⁻¹ * x * (g : G)⁻¹⁻¹ ∈ conjSub (g : G)⁻¹ W := mul_mem_conjSub hx
      have h3 := hW (g : G) hg hx'
      rw [inv_inv] at h3
      have h4 : x ∈ ballStab n β' := by
        rw [← hgβ, ballStab_smul, mem_conjSub]
        exact h3
      refine ballStab_le_stab_of_dist_le (n := n) ?_ h4
      rw [CosetGeom.dist_comm]
      omega

theorem forall_conjSub_inv_le_iff {H W X : Subgroup G} :
    (∀ a ∈ H, conjSub a⁻¹ W ≤ X) ↔ conjClosure W H ≤ X := by
  constructor
  · intro h
    refine conjClosure_le fun k hk z hz => ?_
    have := h k⁻¹ (H.inv_mem hk)
    rw [inv_inv] at this
    exact this (mul_mem_conjSub hz)
  · intro h a ha
    exact (HypF91.conjSub_le_conjClosure (H.inv_mem ha)).trans h

theorem conjClosure_eq_of_le_normalizer {H Z : Subgroup G}
    (hN : H ≤ Subgroup.normalizer (Z : Set G)) : conjClosure Z H = Z :=
  le_antisymm (conjClosure_le fun _ hk z hz => (Subgroup.mem_normalizer_iff.mp (hN hk) z).mp hz)
    (le_conjClosure Z H)

theorem ballStab_zero (hG : G₀ = G₁ ⊔ G₂) (γ : CosetGeom G₀ G₁ G₂) : ballStab 0 γ = stab γ := by
  refine le_antisymm (ballStab_le_stab 0 γ) fun x hx => mem_ballStab.mpr fun δ hδ => ?_
  have h0 : CosetGeom.dist γ δ = 0 := by omega
  obtain rfl := (dist_eq_zero_iff hG).mp h0
  exact hx

theorem le_ballStab_succ_γ₀_iff (hG : G₀ = G₁ ⊔ G₂) {W : Subgroup G} (n : ℕ) :
    W ≤ ballStab (n + 1) (γ₀ G₀ G₁ G₂) ↔
      W ≤ G₁ ∧ conjClosure W G₁ ≤ ballStab n (γ₁ G₀ G₁ G₂) := by
  have h₁ : G₁ ≤ G₀ := hG ▸ le_sup_left
  rw [le_ballStab_succ_iff hG (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)), stab_γ₀ h₁,
    forall_conjSub_inv_le_iff]

theorem le_ballStab_succ_γ₁_iff (hG : G₀ = G₁ ⊔ G₂) {W : Subgroup G} (n : ℕ) :
    W ≤ ballStab (n + 1) (γ₁ G₀ G₁ G₂) ↔
      W ≤ G₂ ∧ conjClosure W G₂ ≤ ballStab n (γ₀ G₀ G₁ G₂) := by
  have h₂ : G₂ ≤ G₀ := hG ▸ le_sup_right
  rw [le_ballStab_succ_iff hG (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).symm, stab_γ₁ h₂,
    forall_conjSub_inv_le_iff]

theorem le_ballStab_four_iff (hG : G₀ = G₁ ⊔ G₂) {V : Subgroup G}
    (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ ballStab 4 (γ₀ G₀ G₁ G₂) ↔ V ≤ G₁ ∧ V ≤ G₂ ∧ conjClosure V G₂ ≤ G₁ ∧
      conjClosure (conjClosure V G₂) G₁ ≤ G₂ ∧
      conjClosure (conjClosure (conjClosure V G₂) G₁) G₂ ≤ G₁ := by
  have h₁ : G₁ ≤ G₀ := hG ▸ le_sup_left
  rw [le_ballStab_succ_γ₀_iff hG 3, conjClosure_eq_of_le_normalizer hN,
    le_ballStab_succ_γ₁_iff hG 2, le_ballStab_succ_γ₀_iff hG 1, le_ballStab_succ_γ₁_iff hG 0,
    ballStab_zero hG, stab_γ₀ h₁]

theorem le_ballStab_five_iff (hG : G₀ = G₁ ⊔ G₂) {V : Subgroup G}
    (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ ballStab 5 (γ₀ G₀ G₁ G₂) ↔ V ≤ G₁ ∧ V ≤ G₂ ∧ conjClosure V G₂ ≤ G₁ ∧
      conjClosure (conjClosure V G₂) G₁ ≤ G₂ ∧
      conjClosure (conjClosure (conjClosure V G₂) G₁) G₂ ≤ G₁ ∧
      conjClosure (conjClosure (conjClosure (conjClosure V G₂) G₁) G₂) G₁ ≤ G₂ := by
  have h₂ : G₂ ≤ G₀ := hG ▸ le_sup_right
  rw [le_ballStab_succ_γ₀_iff hG 4, conjClosure_eq_of_le_normalizer hN,
    le_ballStab_succ_γ₁_iff hG 3, le_ballStab_succ_γ₀_iff hG 2, le_ballStab_succ_γ₁_iff hG 1,
    le_ballStab_succ_γ₀_iff hG 0, ballStab_zero hG, stab_γ₁ h₂]

variable [Finite G] {T V : Subgroup G}

theorem le_critDist_iff (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) {n : ℕ} (hn : 0 < n) :
    n ≤ critDist G₀ G₁ G₂ V ↔ V ≤ ballStab n (γ₀ G₀ G₁ G₂) :=
  ⟨fun h => (critDist_spec hyp hV).2.1.trans (ballStab_le_of_le h _), le_critDist hyp hV hn⟩

end Geometry

namespace GoldHyp3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}
  (h : GoldHyp3 A B z V)

include h

theorem four_le_critDist_iff_closure :
    4 ≤ critDist (A ⊔ B) A B V ↔ V ≤ A ∧ V ≤ B ∧ conjClosure V B ≤ A ∧
      conjClosure (conjClosure V B) A ≤ B ∧
      conjClosure (conjClosure (conjClosure V B) A) B ≤ A := by
  rw [le_critDist_iff (h.gold.amalgamHypV h.natural) h.natural.natural.ne_bot (by norm_num)]
  exact le_ballStab_four_iff rfl h.natural.reduced.2.1

theorem five_le_critDist_iff_closure :
    5 ≤ critDist (A ⊔ B) A B V ↔ V ≤ A ∧ V ≤ B ∧ conjClosure V B ≤ A ∧
      conjClosure (conjClosure V B) A ≤ B ∧
      conjClosure (conjClosure (conjClosure V B) A) B ≤ A ∧
      conjClosure (conjClosure (conjClosure (conjClosure V B) A) B) A ≤ B := by
  rw [le_critDist_iff (h.gold.amalgamHypV h.natural) h.natural.natural.ne_bot (by norm_num)]
  exact le_ballStab_five_iff rfl h.natural.reduced.2.1

theorem four_le_critDist_iff :
    4 ≤ critDist (A ⊔ B) A B V ↔ conjClosure (conjClosure V B) A ≤ pCoreOf 2 B := by
  rw [h.four_le_critDist_iff_closure]
  have hVQ : V ≤ pCoreOf 2 A := h.natural.le_pCoreOf
  have hVA : V ≤ A := hVQ.trans (pCoreOf_le 2 A)
  have hVB : V ≤ B := hVQ.trans (h.gold.pCoreOf_left_le.trans inf_le_right)
  have hUA : conjClosure V B ≤ A :=
    h.conjClosure_le_pCoreOf_left.trans (pCoreOf_le 2 A)
  have hW₂Q : conjClosure (conjClosure V B) A ≤ pCoreOf 2 A :=
    h.conjClosure_conjClosure_le_pCoreOf_left le_rfl
  have hW₂B : conjClosure (conjClosure V B) A ≤ B :=
    hW₂Q.trans (h.gold.pCoreOf_left_le.trans inf_le_right)
  simp only [hVA, hVB, hUA, hW₂B, true_and]
  constructor
  · intro h3 w hw
    have hcore : w ∈ coreIn (A ⊓ B) B := by
      refine ⟨hW₂B hw, fun k hk => ⟨?_, B.mul_mem (B.mul_mem (B.inv_mem hk) (hW₂B hw)) hk⟩⟩
      have hmem : k⁻¹ * w * k⁻¹⁻¹ ∈ conjSub k⁻¹ (conjClosure (conjClosure V B) A) :=
        mul_mem_conjSub hw
      rw [inv_inv] at hmem
      exact h3 (HypF91.conjSub_le_conjClosure (B.inv_mem hk) hmem)
    have hnorm : coreIn (A ⊓ B) B ≤ pCoreOf 2 B :=
      le_pCoreOf_of_le_normalizer 2 (coreIn_le_left _ _) (le_normalizer_coreIn _ _)
        (h.gold.isSylowTwoOf_right.2.1.to_le (coreIn_le_right _ _))
    exact hnorm hcore
  · intro hQ
    refine conjClosure_le fun k hk w hw => ?_
    have : k * w * k⁻¹ ∈ pCoreOf 2 B :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B hk) w).mp (hQ hw)
    exact (h.gold.pCoreOf_right_le this).1

theorem four_le_critDist_iff_le_coreIn :
    4 ≤ critDist (A ⊔ B) A B V ↔
      conjClosure (conjClosure V B) A ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B :=
  h.four_le_critDist_iff.trans ((h.conjClosure_conjClosure_tfae le_rfl).out 1 3)

theorem five_le_critDist_of_four_le (h4 : 4 ≤ critDist (A ⊔ B) A B V) :
    5 ≤ critDist (A ⊔ B) A B V := by
  have hW₂K : conjClosure (conjClosure V B) A ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B :=
    h.four_le_critDist_iff_le_coreIn.mp h4
  have hW₃K : conjClosure (conjClosure (conjClosure V B) A) B ≤
      coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B :=
    conjClosure_le fun k hk w hw =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ hk) w).mp (hW₂K hw)
  have hKQ : coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B ≤ pCoreOf 2 A :=
    (coreIn_le_right _ _).trans inf_le_left
  have hW₄ : conjClosure (conjClosure (conjClosure (conjClosure V B) A) B) A ≤ B :=
    (conjClosure_le fun k hk w hw =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A hk) w).mp
        (hKQ (hW₃K hw))).trans (h.gold.pCoreOf_left_le.trans inf_le_right)
  obtain ⟨c1, c2, c3, c4, c5⟩ := h.four_le_critDist_iff_closure.mp h4
  exact h.five_le_critDist_iff_closure.mpr ⟨c1, c2, c3, c4, c5, hW₄⟩

theorem critDist_ne_four : critDist (A ⊔ B) A B V ≠ 4 := fun h4 =>
  absurd (h.five_le_critDist_of_four_le h4.ge) (by omega)

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
