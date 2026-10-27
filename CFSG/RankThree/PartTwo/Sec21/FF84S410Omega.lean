module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Core
public import CFSG.RankThree.PartTwo.Sec21.FF84S410Coord
public import CFSG.RankThree.PartTwo.Sec21.FF84S410NBCard
public import CFSG.RankThree.PartTwo.Sec21.FF84S4BCore
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP1

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

variable {G : Type} [Group G]

theorem comm_zpowers_le {S : Subgroup G} {c : G} (hc : c ∈ Nor S) :
    ⁅S, Subgroup.zpowers c⁆ ≤ S := by
  rw [Subgroup.commutator_le]
  intro g hg k hk
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hcm : c ^ m ∈ Nor S := zpow_mem hc m
  have h1 : g * (c ^ m * g⁻¹ * (c ^ m)⁻¹) ∈ S :=
    mul_mem hg ((Subgroup.mem_normalizer_iff.1 hcm g⁻¹).1 (inv_mem hg))
  rw [commutatorElement_def]
  simpa [mul_assoc] using h1

theorem plane_val : ∀ w : Fin 2 → ZMod 2,
    (w = 0 ∧ w 0 * w 0 + w 0 * w 1 + w 1 * w 1 = 0) ∨
      (w ≠ 0 ∧ w 0 * w 0 + w 0 * w 1 + w 1 * w 1 = 1) := by
  decide

theorem plane_cast (w : Fin 2 → ZMod 2) (P : Prop) [Decidable P] (hw : w = 0 ↔ P) :
    w 0 * w 0 + w 0 * w 1 + w 1 * w 1 = ((if P then 0 else 1 : ℕ) : ZMod 2) := by
  rcases plane_val w with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hP : P := hw.1 h1
    simp [hP, h2]
  · have hP : ¬ P := fun hp => h1 (hw.2 hp)
    simp [hP, h2]

theorem exists_e_ncomp [Finite G] {S : Subgroup G} {b b₁ b₂ : G} (hS : IsElemAb 2 6 S)
    (hb : b ∈ Nor S) (hb₁ : b₁ ∈ Nor S) (hb₂ : b₂ ∈ Nor S)
    (c0 : Nat.card ↥⁅S, Subgroup.zpowers b⁆ = 4) (c1 : Nat.card ↥⁅S, Subgroup.zpowers b₁⁆ = 4)
    (c2 : Nat.card ↥⁅S, Subgroup.zpowers b₂⁆ = 4)
    (hjoin : ⁅S, Subgroup.zpowers b⁆ ⊔ ⁅S, Subgroup.zpowers b₁⁆ ⊔ ⁅S, Subgroup.zpowers b₂⁆ = S) :
    ∃ e : ↥S ≃* Multiplicative F6,
      (∀ x : ↥S, qMinus (Multiplicative.toAdd (e x)) = (ncomp S b b₁ b₂ (x : G) : ZMod 2)) ∧
      (∀ x : ↥S, (x : G) ∈ ⁅S, Subgroup.zpowers b⁆ → x ≠ 1 → ncomp S b b₁ b₂ (x : G) = 1) ∧
      ∃ s t : ↥S, (s : G) ∈ ⁅S, Subgroup.zpowers b₁⁆ ⊔ ⁅S, Subgroup.zpowers b₂⁆ ∧
        (t : G) ∈ ⁅S, Subgroup.zpowers b₁⁆ ⊔ ⁅S, Subgroup.zpowers b₂⁆ ∧
        Multiplicative.toAdd (e s) = sig0 ∧ Multiplicative.toAdd (e t) = tau0 := by
  classical
  obtain ⟨E, h0, h1, h2⟩ := coord_exists hS (comm_zpowers_le hb) (comm_zpowers_le hb₁)
    (comm_zpowers_le hb₂) c0 c1 c2 hjoin
  obtain ⟨φ, hφ⟩ := Om_iso_qNorm3
  have hq : ∀ w : Fin 3 → Fin 2 → ZMod 2, qMinus (φ.symm w) = qNorm3 w := fun w => by
    have := hφ (φ.symm w)
    simpa using this.symm
  let ws : Fin 3 → Fin 2 → ZMod 2 := ![![0, 0], ![0, 0], ![1, 0]]
  let wt : Fin 3 → Fin 2 → ZMod 2 := ![![0, 0], ![1, 0], ![0, 1]]
  have hqs : qMinus (φ.symm ws) = 1 := by rw [hq]; decide
  have hqt : qMinus (φ.symm wt) = 0 := by rw [hq]; decide
  have hqst : qMinus (φ.symm ws + φ.symm wt) = 0 := by rw [← map_add, hq]; decide
  have hwt0 : φ.symm wt ≠ 0 := by
    intro h
    have h' : wt = 0 := by
      have := φ.symm.injective (h.trans (map_zero _).symm)
      exact this
    revert h'
    decide
  obtain ⟨g, hgs, hgt⟩ := om_pair_trans hqs hqt hqst hwt0
  let Φ : (Fin 3 → Fin 2 → ZMod 2) ≃ₗ[ZMod 2] F6 :=
    φ.symm.trans ((g⁻¹ : OmG) : F6 ≃ₗ[ZMod 2] F6)
  have hΦ : ∀ w, qMinus (Φ w) = qNorm3 w := fun w => by
    have : qMinus (((g⁻¹ : OmG) : F6 ≃ₗ[ZMod 2] F6) (φ.symm w)) = qMinus (φ.symm w) :=
      qMinus_apply_of_mem (g⁻¹).2 _
    exact this.trans (hq w)
  let e : ↥S ≃* Multiplicative F6 := E.trans (AddEquiv.toMultiplicative Φ.toAddEquiv)
  have hex : ∀ x : ↥S, Multiplicative.toAdd (e x) = Φ (Multiplicative.toAdd (E x)) :=
    fun x => rfl
  refine ⟨e, fun x => ?_, fun x hx0 hx1 => ?_, ?_⟩
  · rw [hex, hΦ]
    unfold qNorm3 ncomp
    rw [Fin.sum_univ_three, Nat.cast_add, Nat.cast_add,
      plane_cast _ _ (h0 x), plane_cast _ _ (h1 x), plane_cast _ _ (h2 x)]
  · have hxS : ((x : G)) ∈ ⁅S, Subgroup.zpowers b⁆ := hx0
    have hn1 : (x : G) ∈ ⁅S, Subgroup.zpowers b⁆ ⊔ ⁅S, Subgroup.zpowers b₂⁆ :=
      Subgroup.mem_sup_left hxS
    have hn2 : (x : G) ∈ ⁅S, Subgroup.zpowers b⁆ ⊔ ⁅S, Subgroup.zpowers b₁⁆ :=
      Subgroup.mem_sup_left hxS
    have hn0 : (x : G) ∉ ⁅S, Subgroup.zpowers b₁⁆ ⊔ ⁅S, Subgroup.zpowers b₂⁆ := by
      intro hm
      apply hx1
      have a0 := (h0 x).2 hm
      have a1 := (h1 x).2 hn1
      have a2 := (h2 x).2 hn2
      have : E x = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i
        · exact a0
        · exact a1
        · exact a2
      exact E.injective (this.trans (map_one E).symm)
    unfold ncomp
    simp [hn0, hn1, hn2]
  · refine ⟨E.symm (Multiplicative.ofAdd ws), E.symm (Multiplicative.ofAdd wt), ?_, ?_, ?_, ?_⟩
    · exact (h0 _).1 (by simp [ws])
    · exact (h0 _).1 (by simp [wt])
    · rw [hex]
      simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      show ((g⁻¹ : OmG) : F6 ≃ₗ[ZMod 2] F6) (φ.symm ws) = sig0
      have : φ.symm ws = g • sig0 := hgs.symm
      rw [this]
      exact inv_smul_smul g sig0
    · rw [hex]
      simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      show ((g⁻¹ : OmG) : F6 ≃ₗ[ZMod 2] F6) (φ.symm wt) = tau0
      have : φ.symm wt = g • tau0 := hgt.symm
      rw [this]
      exact inv_smul_smul g tau0

variable [Finite G]

theorem S410_omega_pair (h48 : FF84_4_8) (h47 : FF84_4_7) (hCSb : HypS48CSb) (hb2 : HypS48b2)
    (h49 : HypS49orbits) (h49S6 : HypS49S6) (hE27 : HypOmNormalizerE27)
    {b : G} {L B K : Subgroup G} {b₁ b₂ : G} (h : FF84Post b L B K b₁ b₂) {U : Subgroup G}
    (hU : U ∈ PiStar (Cen b) B 2) :
    ∃ e : ↥(Op 2 (Nor U)) ≃* Multiplicative F6, FF84OmegaDataFor (Op 2 (Nor U)) e ∧
      ∃ s t : ↥(Op 2 (Nor U)), (s : G) ∈ Cen b ∧ (t : G) ∈ Cen b ∧
        Multiplicative.toAdd (e s) = sig0 ∧ Multiplicative.toAdd (e t) = tau0 := by
  classical
  obtain ⟨-, hSE, -, hidx, -, -, -⟩ := h48 G b L B K b₁ b₂ h.sec U hU
  have hBE : IsElemAb 3 3 B := h.sec.mono.1
  have hgen : B = Subgroup.closure {b, b₁, b₂} := h.sec.mono.2.1
  have hBU : B ≤ Nor U := hU.2.2.1
  have hBS : B ≤ Nor (Op 2 (Nor U)) := hBU.trans (le_nor_op2 (Nor U))
  have hbB : b ∈ B := by rw [hgen]; exact Subgroup.subset_closure (by simp)
  have hb1B : b₁ ∈ B := by rw [hgen]; exact Subgroup.subset_closure (by simp)
  have hb2B : b₂ ∈ B := by rw [hgen]; exact Subgroup.subset_closure (by simp)
  obtain ⟨hc2, hc1, hCB⟩ := hb2 G b L B K b₁ b₂ h U hU
  have hc0 : Nat.card ↥(Op 2 (Nor U) ⊓ Cen b) = 16 := by
    rw [hCSb G b L B K b₁ b₂ h U hU]
    obtain ⟨U₁, U₂, -, -, -, hU47⟩ := h47 G b L B K b₁ b₂ h.sec
    exact (hU47 U hU).1.2
  obtain ⟨k0, k1, k2, hjoin, -, hf1, hf2⟩ := B_isotypic hSE hBE hBS hgen hc0 hc1 hc2 hCB
  obtain ⟨e, hqn, hS0, s, t, hs, ht, hes, het⟩ :=
    exists_e_ncomp hSE (hBS hbB) (hBS hb1B) (hBS hb2B) k0 k1 k2 hjoin
  have hUb : ∀ x : G, x ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆ ⊔
      ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆ → x ∈ Cen b := by
    intro x hx
    have hsup : ⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆ ⊔ ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆ ≤
        Cen b := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · have hb' : b ∈ Subgroup.closure ({b, b₂} : Set G) := Subgroup.subset_closure (by simp)
        exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hf1 hy) b hb').symm
      · have hb' : b ∈ Subgroup.closure ({b, b₁} : Set G) := Subgroup.subset_closure (by simp)
        exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hf2 hy) b hb').symm
    exact hsup hx
  obtain ⟨Δ₁, Δ₂, hU12, hdis, hc1', hc2', ht1, ht2, hinv1, hop1, hop2, hodd⟩ :=
    h49 G b L B K b₁ b₂ h U hU
  have hmemΔ : ∀ x : G, x ∈ Op 2 (Nor U) → x ≠ 1 → x ∈ Δ₁ ∨ x ∈ Δ₂ := fun x hx hx1 => by
    have : x ∈ ((Op 2 (Nor U) : Set G) \ {1}) := ⟨hx, hx1⟩
    rw [← hU12] at this
    exact this
  have hΔ1S : ∀ x ∈ Δ₁, x ∈ Op 2 (Nor U) ∧ x ≠ 1 := fun x hx => by
    have : x ∈ ((Op 2 (Nor U) : Set G) \ {1}) := by
      rw [← hU12]
      exact Or.inl hx
    exact ⟨this.1, this.2⟩
  have hcastodd : ∀ n : ℕ, (n : ZMod 2) = 1 ↔ n % 2 = 1 := fun n => by
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [hn, ← ZMod.natCast_mod n 2, hn]
      simp
    · rw [hn, ← ZMod.natCast_mod n 2, hn]
      simp
  have hq : ∀ x : ↥(Op 2 (Nor U)), (x : G) ≠ 1 →
      (qMinus (Multiplicative.toAdd (e x)) = 1 ↔ Op 2 (Cen (x : G)) = Op 2 (Nor U)) := by
    intro x hx1
    rw [hqn, hcastodd, ← hodd x x.2 hx1]
    constructor
    · exact hop1 x
    · intro hO
      rcases hmemΔ x x.2 hx1 with h1 | h2
      · exact h1
      · exact absurd hO (hop2 x h2)
  have htrans : ∀ x y : G, x ∈ Op 2 (Nor U) → y ∈ Op 2 (Nor U) → x ≠ 1 → y ≠ 1 →
      Op 2 (Cen x) = Op 2 (Nor U) → Op 2 (Cen y) = Op 2 (Nor U) →
        ∃ n ∈ Nor (Op 2 (Nor U)), n * x * n⁻¹ = y := by
    intro x y hx hy hx1 hy1 hxO hyO
    have hxΔ : x ∈ Δ₁ := by
      rcases hmemΔ x hx hx1 with h1 | h2
      · exact h1
      · exact absurd hxO (hop2 x h2)
    have hyΔ : y ∈ Δ₁ := by
      rcases hmemΔ y hy hy1 with h1 | h2
      · exact h1
      · exact absurd hyO (hop2 y h2)
    exact ht1 x hxΔ y hyΔ
  have hne : Δ₁.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hc1']; norm_num)
  obtain ⟨s₁, hs₁⟩ := hne
  obtain ⟨hs₁S, hs₁1⟩ := hΔ1S s₁ hs₁
  have hs₁2 : orderOf s₁ = 2 := by
    haveI := hSE.1
    have hsq : s₁ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := Op 2 (Nor U)) s₁ hs₁S
    exact orderOf_eq_prime hsq hs₁1
  have hker : Nor (Op 2 (Nor U)) ⊓ CenS (Op 2 (Nor U)) ≤ Op 2 (Nor U) := by
    intro x hx
    have hxc : x ∈ CenS (Op 2 (Cen s₁)) := by rw [hop1 s₁ hs₁]; exact hx.2
    have hxs : x ∈ Cen s₁ := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hx.2 s₁ hs₁S).symm
    have := B_charTwo_cen h.sec.hyp.char2 hs₁2 (Subgroup.mem_inf.2 ⟨hxs, hxc⟩)
    rwa [hop1 s₁ hs₁] at this
  have hex1 : ∃ s : G, s ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b⁆ ∧ s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : ⁅Op 2 (Nor U), Subgroup.zpowers b⁆ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      exact hcon
    rw [this, Subgroup.card_bot] at k0
    omega
  obtain ⟨s₀, hs₀0, hs₀1⟩ := hex1
  have hs₀S : s₀ ∈ Op 2 (Nor U) := comm_zpowers_le (hBS hbB) hs₀0
  have hs₀O : Op 2 (Cen s₀) = Op 2 (Nor U) := by
    have hc : ncomp (Op 2 (Nor U)) b b₁ b₂ s₀ = 1 := hS0 ⟨s₀, hs₀S⟩ hs₀0 (fun hh => hs₀1 (by
      have := congrArg Subtype.val hh
      simpa using this))
    have : s₀ ∈ Δ₁ := (hodd s₀ hs₀S hs₀1).2 (by rw [hc])
    exact hop1 s₀ this
  have hS6 : ∃ s₀ ∈ Op 2 (Nor U), s₀ ≠ 1 ∧ Op 2 (Cen s₀) = Op 2 (Nor U) ∧
      ∃ H : Subgroup G, H ≤ Cen s₀ ∧ Nonempty (↥H ≃* Equiv.Perm (Fin 6)) ∧
        H ⊓ Op 2 (Nor U) = ⊥ := by
    obtain ⟨H, hH1, hH2, hH3⟩ := h49S6 G b L B K b₁ b₂ h U hU s₀ hs₀0 hs₀1
    exact ⟨s₀, hs₀S, hs₀1, hs₀O, H, hH1, hH2, hH3⟩
  have hNB : Nat.card ↥(Nor B) ≤ 1296 := card_Nor_B_le h.sec h.cB
  have hcard : Nat.card ↥(Nor B ⊓ Nor (Op 2 (Nor U))) ≤ 648 := by
    rw [inf_comm]
    have h1 := Subgroup.card_mul_index ((Nor (Op 2 (Nor U)) ⊓ Nor B).subgroupOf (Nor B))
    have h2 : ((Nor (Op 2 (Nor U)) ⊓ Nor B).subgroupOf (Nor B)).index = 2 := hidx
    have h3 : Nat.card ↥((Nor (Op 2 (Nor U)) ⊓ Nor B).subgroupOf (Nor B)) =
        Nat.card ↥(Nor (Op 2 (Nor U)) ⊓ Nor B) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h2, h3] at h1
    omega
  exact ⟨e, omegaData_of_core e hSE hBE hBS hq htrans hker hS6 hcard hE27, s, t, hUb _ hs, hUb _ ht, hes, het⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
