module

public import CFSG.Quasithin.MS93.S33SpShape
public import CFSG.Quasithin.MS93.S33Conv
public import CFSG.Quasithin.MS93.S33Stmt

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

section Index

theorem relIndex_le_of_mul [Finite G] {D U K : Subgroup G} (hUK : U ≤ K)
    (hK : ∀ k ∈ K, ∃ u ∈ U, ∃ d ∈ D, k = u * d) : D.relIndex K ≤ D.relIndex U := by
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  let f : ↥U ⧸ D.subgroupOf U → ↥K ⧸ D.subgroupOf K :=
    Quotient.map' (Subgroup.inclusion hUK) fun a b hab => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
      exact hab
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u, hu, d, hd, hkud⟩ := hK k k.2
    refine ⟨QuotientGroup.mk ⟨u, hu⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hUK ⟨u, hu⟩) : ↥K ⧸ D.subgroupOf K) =
      QuotientGroup.mk k
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((Subgroup.inclusion hUK ⟨u, hu⟩)⁻¹ * k : ↥K).1 = d := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [hkud]
      group
    rw [this]
    exact hd
  exact Nat.card_le_card_of_surjective f hf

theorem exists_mul_of_mem_sup {U W : Subgroup G} (hcomm : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u)
    {x : G} (hx : x ∈ U ⊔ W) : ∃ u ∈ U, ∃ w ∈ W, x = u * w := by
  let S : Subgroup G :=
    { carrier := {x | ∃ u ∈ U, ∃ w ∈ W, x = u * w}
      mul_mem' := by
        rintro _ _ ⟨u, hu, w, hw, rfl⟩ ⟨u', hu', w', hw', rfl⟩
        refine ⟨u * u', mul_mem hu hu', w * w', mul_mem hw hw', ?_⟩
        calc u * w * (u' * w') = u * (w * u') * w' := by group
          _ = u * (u' * w) * w' := by rw [(hcomm u' hu' w hw).symm]
          _ = u * u' * (w * w') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨u, hu, w, hw, rfl⟩
        refine ⟨u⁻¹, inv_mem hu, w⁻¹, inv_mem hw, ?_⟩
        rw [mul_inv_rev]
        exact (hcomm u⁻¹ (inv_mem hu) w⁻¹ (inv_mem hw)).symm }
  have hle : U ⊔ W ≤ S := sup_le (fun u hu => ⟨u, hu, 1, one_mem _, by simp⟩)
    (fun w hw => ⟨1, one_mem _, w, hw, by simp⟩)
  exact hle hx

end Index

section Orders

variable [Finite G] {M T L : Subgroup G}

theorem exists_relIndex_zm_eq_pow (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    ∃ m : ℕ, 1 ≤ m ∧ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 (Z0q M T) :=
    h.isPGroup.to_le ((h.Z0q_le_Xq.trans (Xq_le_pCoreOf M)).trans h.pCore_le)
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hdvd : (pre h.le (Qv _ α')).relIndex (Z0q M T) ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card _
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hrel : (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ m := by
    rw [puAmalgam.zm_baseA, ← relIndex_pre h.le _ (Z0q_le M T)]
    exact hm
  refine ⟨m, ?_, hrel⟩
  by_contra h0
  have : m = 0 := by omega
  rw [this, pow_zero] at hrel
  exact relIndex_qv_zm_ne_one hc hrel

theorem sp4_cases (h : PUHyp M T L) {k : ℕ}
    (hk : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k ∨
      2 ^ (2 * k) ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) := by
  rcases hk with ⟨rfl, -⟩ | ⟨hk2, F, iF, fF, α, hcard, hα, hnat⟩
  · obtain ⟨m, hm1, hm⟩ := exists_relIndex_zm_eq_pow h hc
    rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    · exact Or.inl hm
    · refine Or.inr ?_
      rw [hm]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hF : 4 ≤ Fintype.card F := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    rcases shapes_of_sp h hcard hF hα hnat hc with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl (h1.trans hcard)
    · refine Or.inr ?_
      rw [hcard, ← pow_mul, mul_comm] at h1
      exact h1

end Orders

section Weak

variable [Finite G] {M T L : Subgroup G}

theorem s33iiW_of_parts (hLW : S33LW) (h : PUHyp M T L) (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) {k : ℕ}
    (hk : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k) {α' : Vtx (puAmalgam h.le)}
    {Y : Subgroup (puAmalgam h.le).Universal} (hyp : S33Hyp h α' Y) : S33iiW h α' := by
  rcases sp4_cases h hk hyp.1 with hP | hΛ
  · exact ⟨k, hk, Or.inr hP⟩
  · obtain ⟨hk1, t₁, ht₁, t₂, ht₂, hidx, h12, hsup⟩ := hLW G M T L h hXL k hk α' Y hyp hΛ
    exact ⟨k, hk, Or.inl ⟨hk1, t₁, ht₁, t₂, ht₂, hidx, h12, hsup⟩⟩

end Weak

theorem s33w_of (h32 : S32) (h38 : S38) (hBad : S33Bad) (hLW : S33LW) : S33w := by
  intro G _ _ M T L h α' hc Y hY hYR hn hXc
  have hyp : S33Hyp h α' Y := ⟨hc, hY, hYR, hn⟩
  obtain ⟨-, hXL, hcases⟩ := h32 G M T L h
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hn' : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤ critR (puAmalgam h.le) (baseA _) α' := by
    intro hle
    apply hn
    refine hle.trans (le_sup_of_le_left (Subgroup.commutator_mono ?_ ?_))
    · exact zm_le_xm _ h20 hb (PU.isMVtx_baseA _)
    · exact zm_le_xm _ h20 hb (hc.isMVtx_right _ h20)
  have hSL : IsSL3U M T L → S33i h α' Y ∨ S33iiW h α' := fun hU =>
    Or.inl (s33i_of_sl3 h hU hc hY hYR hn')
  have hSp : (∃ k, IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k) →
      S33i h α' Y ∨ S33iiW h α' := fun ⟨k, hk⟩ =>
    Or.inr (s33iiW_of_parts hLW h hXL hk hyp)
  have hBadCase : (IsHatA6U M T L ∨ IsDoubleSL3U M T L ∨ IsSL3TwoU M T L ∨ IsSL3TwoZ M T L ∨
      IsG2U h.le L) → S33i h α' Y ∨ S33iiW h α' := by
    intro hbad
    by_cases hU : IsSL3U M T L
    · exact hSL hU
    by_cases hS : ∃ k, IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k
    · exact hSp hS
    exfalso
    have hb2 := two_le_critDist _ h20 hb
    rcases (show critDist (puAmalgam h.le) = 2 ∨ 2 < critDist (puAmalgam h.le) by omega) with
      hb2' | hb2'
    · exact hBad G M T L h hb2' hXL hbad hU (fun k hk => hS ⟨k, hk⟩) α' hc Y hY hYR
        (hXc hb2' hU fun k hk => hS ⟨k, hk⟩) hn
    · rcases h38 G M T L h hb2' with hU' | hSp'
      · exact hU hU'
      · exact hS (isSp4DerSec_of_isSp4U h hSp')
  rcases hcases with hU | hA | hD2 | hT | hZ | hS | hG
  · exact hSL hU
  · exact hBadCase (Or.inl hA)
  · exact hBadCase (Or.inr (Or.inl hD2))
  · exact hBadCase (Or.inr (Or.inr (Or.inl hT)))
  · exact hBadCase (Or.inr (Or.inr (Or.inr (Or.inl hZ))))
  · exact hSp hS
  · exact hBadCase (Or.inr (Or.inr (Or.inr (Or.inr hG))))

end CFSG.Quasithin.MS93.S33
