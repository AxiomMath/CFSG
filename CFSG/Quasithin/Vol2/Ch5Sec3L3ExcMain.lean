module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcRho
public import CFSG.Quasithin.Vol2.Ch5Sec3L3Facts

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Fischer
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem isElemAbelian_conjClosure {Z X : Subgroup G} (hZ : ∀ s ∈ Z, s * s = 1)
    (hab : ∀ a ∈ conjClosure Z X, ∀ b ∈ conjClosure Z X, a * b = b * a) :
    IsElemAbelian 2 (conjClosure Z X) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, fun y hy => ?_⟩
  rw [sq]
  have hy' := hy
  unfold conjClosure at hy'
  clear hy
  induction hy' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨h, hh, s, hs, rfl⟩ := hy
    calc h * s * h⁻¹ * (h * s * h⁻¹) = h * (s * s) * h⁻¹ := by group
      _ = 1 := by rw [hZ s hs, mul_one, mul_inv_cancel]
  | one => simp
  | mul a b ha hb iha ihb =>
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a _ iha =>
    rw [← mul_inv_rev, iha, inv_one]

variable [Finite G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}

theorem stmt5_3_7_exc_of (h527 : Stmt5_2_7)
    (h531 : Stmt5_3_1) : Stmt5_3_7_exc := by
  intro G _ _ T M L V H B D L₂ n f hyp hty hf _ hf2 z hz hzT hz2 hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨hM1, hM2⟩ := exc_centralizer_eq h527 h531 hyp hty hf2 hz hzT hz1 hO
  have hM12 := exc_inf_centralizer_eq h527 h531 hyp hty hf2 hz hzT hz1 hO
  have h535 := stmt5_3_5_of h531 (stmt5_3_L3_facts_of h527 h531) G T M L V H B D L₂ n f hyp hty
    hf
  obtain ⟨N, rfl⟩ := exists_excNF h527 h531 hyp hty hf2 hz hzT hz1 hO
  have hST : sec53S T L ≤ T := inf_le_left
  have hTz : T ≤ N.Gz := fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp
      ((inf_le_right : centerOf T ≤ Subgroup.centralizer (T : Set G)) hzT) t ht)
  have hTM12 : T ≤ sec53M12 L H := hM12 ▸ inf_le_left
  have hCT : CharTwo N.Gz :=
    charTwo_centralizer_of_conj_mem h.qtke h.sylow hz2 (g := 1) (by simpa using hzT)
  obtain ⟨hVT, hVN, hZV, hVcomm, hVsq⟩ := exc_Vz N hST h.sylow hTz hCT
  set W := conjClosure (sec53ZS T L) N.Gz with hW
  have hsZ : ∀ s ∈ sec53ZS T L, s * s = 1 := fun s hs => by
    obtain ⟨c, rfl⟩ := (N.mem_Z s).mp hs
    rw [N.sq_Φ, mul_zero, N.Φ_zero]
  have hZcase : N.Gz ≤ Subgroup.normalizer (sec53ZS T L : Set G) →
      N.Gz ≤ sec53M12 L H := fun hle => by rw [← h535]; exact hle
  by_cases hWS : W ≤ sec53S T L
  · by_cases hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
    ·
      have hE := isElemAbelian_conjClosure hsZ hab
      by_cases hWZ : W = sec53ZS T L
      · apply hZcase
        have h1 := hVN
        rw [hWZ] at h1
        exact h1
      have hZW : sec53ZS T L < W := lt_of_le_of_ne hZV (Ne.symm hWZ)
      rcases (l3facts_three h527 hyp hty hf).1 W hWS hE with hW1 | hW2
      · have h1 := le_M1_of_normalizes h527 h531 hyp hty hf hZW hW1 hTz hVN
        exact (le_inf h1 le_rfl).trans (hM1.le.trans hTM12)
      · have h1 := le_M2_of_normalizes h527 h531 hyp hty hf hZW hW2 hTz hVN
        exact (le_inf h1 le_rfl).trans (hM2.le.trans hTM12)
    ·
      push Not at hab
      obtain ⟨a, ha, b, hb, hne⟩ := hab
      have hcen := N.centerOf_eq hWS hZV ⟨a, ha, b, hb, hne⟩
      apply hZcase
      refine le_trans (H13.le_normalizer_inf_of_normalizes hVN
        (hVN.trans (H13.normalizer_le_normalizer_centralizer W))) (le_of_eq ?_)
      show Subgroup.normalizer ((centerOf W : Subgroup G) : Set G) = _
      rw [hcen]
  ·
    exfalso
    obtain ⟨v, hv, hvS⟩ : ∃ v ∈ W, v ∉ sec53S T L := by
      by_contra hcon
      push Not at hcon
      exact hWS fun v hv => hcon v hv
    have hvQ := N.mem_Q_of_sq hST (hVT hv) hvS (hVsq v hv)
    have hQW : N.Q ≤ W := N.Q_le_of hST (fun c => hZV ((N.mem_Z _).mpr ⟨c, rfl⟩))
      (fun t ht g hg => (Subgroup.mem_normalizer_iff.mp (hVN (hTz ht)) g).mp hg) hv hvS hvQ
    have hWQ : W ≤ N.Q := fun y hy =>
      N.mem_Q_of_comm_Q hST (hVT hy) fun q hq => hVcomm y hy q (hQW hq)
    have hWeq : W = N.Q := le_antisymm hWQ hQW
    have hQN : N.Gz ≤ Subgroup.normalizer (N.Q : Set G) := by
      have h1 := hVN
      rw [hWeq] at h1
      exact h1
    have hC : ∀ g ∈ N.Gz, (∀ y ∈ sec53ZS T L, y * g = g * y) → g ∈ T := by
      intro g hg hc
      have hgN : g ∈ Subgroup.normalizer (sec53ZS T L : Set G) :=
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hc)
      rw [h535] at hgN
      exact hM12.le (Subgroup.mem_inf.mpr ⟨hgN, hg⟩)
    have hA1 : N.Φ (0, 1, 0) ∈ pCoreOf 2 L ⊓ N.Q :=
      Subgroup.mem_inf.mpr ⟨(N.mem_V₁ _).mpr ⟨0, 1, rfl⟩, N.Φ_mem_Q (by norm_num) (by norm_num)⟩
    have hA1Z : N.Φ (0, 1, 0) ∉ sec53ZS T L := by
      intro h1
      obtain ⟨c, hc⟩ := (N.mem_Z _).mp h1
      exact zero_ne_one (N.Φ_inj hc).2.1
    have hZA : sec53ZS T L < pCoreOf 2 L ⊓ N.Q := by
      refine lt_of_le_of_ne (le_inf ?_ fun g hg => ?_) fun h1 => hA1Z (h1.ge hA1)
      · intro g hg
        obtain ⟨c, rfl⟩ := (N.mem_Z g).mp hg
        exact (N.mem_V₁ _).mpr ⟨c, 0, rfl⟩
      · obtain ⟨c, rfl⟩ := (N.mem_Z g).mp hg
        exact N.Φ_mem_Q (by norm_num) (by norm_num)
    have hTA : T ≤ Subgroup.normalizer ((pCoreOf 2 L ⊓ N.Q : Subgroup G) : Set G) :=
      H13.le_normalizer_inf_of_normalizes
        ((h.T_le.trans h.normal).trans (normalizer_le_normalizer_pCoreOf 2 L))
        (hTz.trans hQN)
    have hM1' : N.Gz ⊓ Subgroup.normalizer ((pCoreOf 2 L ⊓ N.Q : Subgroup G) : Set G) ≤ T := by
      have h1 := le_M1_of_normalizes h527 h531 hyp hty hf hZA inf_le_left (le_inf hTz hTA)
        inf_le_right
      exact (le_inf h1 inf_le_left).trans hM1.le
    exact N.false_of_normalizes_Q hQN hST h.sylow hTz hWeq hC hM1'

end CFSG.Quasithin.H13.Sec53L3
