module

public import CFSG.Quasithin.EmptyFaithful.S152He9W
public import CFSG.Quasithin.Recognition.Kleidman.F204.GeoBase1
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPhi

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem kerβ_eq_Q2 (F : Frame L1 L2 S D X) :
    F112W.kerβ (P1 L1 L2 S) (P2 L1 L2 S) = Q2 L1 L2 S := by
  have hA := Amal.of_frame F
  apply le_antisymm _ (F112W.pCoreOf_le_kerβ hA.amalgam)
  set K := F112W.kerβ (P1 L1 L2 S) (P2 L1 L2 S) with hK
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_P2 F
  have hKB : K ≤ bigB L1 L2 S := by
    have := F112W.kerβ_le_inf (G₁ := P1 L1 L2 S) (G₂ := P2 L1 L2 S)
    rwa [F.P1_inf_P2] at this
  have hKP : K ≤ P2 L1 L2 S := F112W.kerβ_le_right
  have hnorm : (K.subgroupOf (P2 L1 L2 S)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (F112W.le_normalizer_kerβ (G₁ := P1 L1 L2 S)
      (G₂ := P2 L1 L2 S) g.2) n).mp hn
    exact this
  have hmapn : (Subgroup.map φ (K.subgroupOf (P2 L1 L2 S))).Normal := hnorm.map φ hφs
  have := hmapn
  intro k hk
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.map φ (K.subgroupOf (P2 L1 L2 S))) with h | h
  · have h2 : φ ⟨k, hKP hk⟩ ∈ Subgroup.map φ (K.subgroupOf (P2 L1 L2 S)) := ⟨_, hk, rfl⟩
    rw [h, Subgroup.mem_bot] at h2
    exact (hφk _).mp h2
  · exfalso
    have hBP : P2 L1 L2 S ≤ bigB L1 L2 S := by
      intro p hp
      have h2 : φ ⟨p, hp⟩ ∈ Subgroup.map φ (K.subgroupOf (P2 L1 L2 S)) := by rw [h]; trivial
      obtain ⟨c, hc, hcp⟩ := h2
      have hker : (c⁻¹ * ⟨p, hp⟩ : ↥(P2 L1 L2 S)) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcp, inv_mul_cancel]
      have hq : ((c⁻¹ * ⟨p, hp⟩ : ↥(P2 L1 L2 S)) : G) ∈ Q2 L1 L2 S := (hφk _).mp hker
      have hcB : (c : G) ∈ bigB L1 L2 S := hKB hc
      have hqB : ((c⁻¹ * ⟨p, hp⟩ : ↥(P2 L1 L2 S)) : G) ∈ bigB L1 L2 S :=
        F.mem_B_of_mem_S (F.Q2_le_S hq)
      have e : p = (c : G) * ((c⁻¹ * ⟨p, hp⟩ : ↥(P2 L1 L2 S)) : G) := by simp
      rw [e]
      exact (bigB L1 L2 S).mul_mem hcB hqB
    have h1 := F.pair.relIndex_bigB_right
    rw [(Subgroup.relIndex_eq_one).mpr hBP] at h1
    omega

theorem D_le_kerα (F : Frame L1 L2 S D X) : D ≤ F112W.kerα (P1 L1 L2 S) (P2 L1 L2 S) := by
  intro d hd
  have hdB : d ∈ bigB L1 L2 S := F.D_le_B hd
  have hdP : d ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hdB
  have hd3 : d ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥D) (x := ⟨d, hd⟩)
    rw [F.D_card] at this
    simpa using congrArg Subtype.val this
  refine ⟨hdP, fun p hp => ?_⟩
  rw [F.P1_inf_P2]
  exact three_conj_mem_B F hdP hd3 hp

theorem kerα_eq_Q1_sup_D (F : Frame L1 L2 S D X) :
    F112W.kerα (P1 L1 L2 S) (P2 L1 L2 S) = Q1 L1 L2 S ⊔ D := by
  have hA := Amal.of_frame F
  apply le_antisymm
  · intro k hk
    have hKB : k ∈ bigB L1 L2 S := by
      have := F112W.kerα_le_inf (G₁ := P1 L1 L2 S) (G₂ := P2 L1 L2 S)
      rw [F.P1_inf_P2] at this
      exact this hk
    have hDS : D ≤ Subgroup.normalizer (S : Set G) := F.D_le_B.trans F.B_le_normalizer_S
    rw [F.bigB_eq] at hKB
    obtain ⟨s, hs, d, hd, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hDS).mp hKB
    have hdK := D_le_kerα F hd
    have hsK : s ∈ F112W.kerα (P1 L1 L2 S) (P2 L1 L2 S) := by
      have := (F112W.kerα (P1 L1 L2 S) (P2 L1 L2 S)).mul_mem hk
        ((F112W.kerα (P1 L1 L2 S) (P2 L1 L2 S)).inv_mem hdK)
      simpa using this
    exact (Q1 L1 L2 S ⊔ D).mul_mem
      (le_sup_left (a := Q1 L1 L2 S) (b := D) (F.inf_kerα_le ⟨hs, hsK⟩))
      (le_sup_right (a := Q1 L1 L2 S) (b := D) hd)
  · exact sup_le (F112W.pCoreOf_le_kerα hA.amalgam) (D_le_kerα F)

theorem ballStab_one_true (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = true) : ballStab 1 δ = Qv δ := by
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hδ
  rw [ballStab_smul, Qv_smul]
  congr 1
  unfold Qv
  rw [stab_γ₁ h₂, F112W.kerβ_eq_ballStab rfl, kerβ_eq_Q2 F]

theorem ballStab_one_false (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) :
    ∃ E : Subgroup G, E ≤ stab δ ∧ Nat.card E = 3 ∧ E ⊓ Qv δ = ⊥ ∧
      ballStab 1 δ = Qv δ ⊔ E := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hδ
  have hQ : Qv (g • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) =
      conjSub (g : G) (Q1 L1 L2 S) := by
    rw [Qv_smul]; unfold Qv; rw [stab_γ₀ h₁]
  refine ⟨conjSub (g : G) D, ?_, ?_, ?_, ?_⟩
  · rw [stab_smul, stab_γ₀ h₁]
    exact conjSub_mono _ (F.D_le_B.trans le_sup_right)
  · rw [card_conjSub]; exact F.D_card
  · rw [hQ, ← conjSub_inf]
    have : D ⊓ Q1 L1 L2 S = ⊥ := by
      rw [eq_bot_iff, ← F.D_inf]
      exact inf_le_inf_left D F.Q1_le_S
    rw [this]
    exact (conjSub_eq_bot_iff _).mpr rfl
  · rw [ballStab_smul, F112W.kerα_eq_ballStab rfl, kerα_eq_Q1_sup_D F, conjSub_sup, hQ]

theorem relIndex_stab_inf_nbr (F : Frame L1 L2 S D X) {δ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hμ : μ ∈ nbrs δ) : (stab δ ⊓ stab μ).relIndex (stab δ) = 5 := by
  have hA := Amal.of_frame F
  obtain ⟨g, hg, he⟩ := hA.edge_conj hμ
  rw [he]
  rcases hg with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1, relIndex_conjSub]; exact hA.relIndex_left
  · rw [h1, relIndex_conjSub]; exact hA.relIndex_right

theorem stab_eq_sup_of_not_le (F : Frame L1 L2 S D X) {δ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hμ : μ ∈ nbrs δ) {N : Subgroup G} (hN : N ≤ stab δ) (hNμ : ¬ N ≤ stab μ) :
    N ⊔ (stab δ ⊓ stab μ) = stab δ := by
  have h5 := relIndex_stab_inf_nbr F hμ
  have hKS : stab δ ⊓ stab μ ≤ N ⊔ (stab δ ⊓ stab μ) := le_sup_right
  have hSL : N ⊔ (stab δ ⊓ stab μ) ≤ stab δ := sup_le hN inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hKS hSL
  rw [h5] at hmul
  have hd : (stab δ ⊓ stab μ).relIndex (N ⊔ (stab δ ⊓ stab μ)) ∣ 5 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h1 | h1
  · exfalso
    have : N ⊔ (stab δ ⊓ stab μ) ≤ stab δ ⊓ stab μ := Subgroup.relIndex_eq_one.mp h1
    exact hNμ ((le_sup_left.trans this).trans inf_le_right)
  · rw [h1] at hmul
    have : (N ⊔ (stab δ ⊓ stab μ)).relIndex (stab δ) = 1 := by omega
    exact le_antisymm hSL (Subgroup.relIndex_eq_one.mp this)

end CFSG.Quasithin.Kleidman.F204
