module

public import CFSG.Quasithin.Vol2.Ch11SecBK6J

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_zero)
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative commutatorElement

namespace BK6

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem r2Line_sl3 (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSL3 L V n) {A : Subgroup G}
    (hAR : A ≤ pCoreOf 2 (LOf L V₂ ⊔ T)) (hA : autI hfl.elem A ∈ E3.aSet n (autI hfl.elem X)) :
    (⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₂ ∧
        V ⊓ Subgroup.centralizer (A : Set G) = V₂) ∨
      (E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = n ∧
        E3.mQuot V (V ⊓ Subgroup.centralizer (A : Set G)) = n ∧
        ∃ l ∈ LOf L V₂, ⁅V, conjSubgroup A l⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, K, _, _, _, hK, π, hπ⟩ := exists_real_sl3 hfl hk
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hn := hfl.two_le
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  have hV₁V : V₁ ≤ V := hfl.le₁₂.trans hfl.le₂
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hfl.sylow le_sup_left (sup_le Subgroup.le_normalizer hfl.T_le_L)
  have hP := SecA.isSylowTwoOf_autOn hfl.le_normalizer hTL'
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  have hF₁ := isFlagW_of_flag24 hfl hV₁V hfl.cV_le hfl.stable₁ (by rw [hfl.index₁, mul_one])
    hfl.T_le_V₁
  have hF₂ := isFlagW_of_flag24 hfl hfl.le₂ (hfl.cV_le.trans hfl.le₁₂) hfl.stable₂ hfl.index₂
    hfl.T_le_V₂
  have hU₁ := eq_U1_of_isFlagW hsq hf hg (by rw [hK]; exact hF₁)
  have hU₂ := eq_U2_of_isFlagW hsq hf hg (by rw [hK]; exact hF₂)
  have hlf := KGNat.factLineSL3_holds K n hn hK _ hsq _ _ π hπ
    (fun h hh z hz => SecA.autOn_fixes_cV h hh z hz) _ hP _ hF₂
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun a ha => K7.r2_le_normalizer hfl (hAR ha)
  choose b c hbc using fun a : ↥A => exists_rad2_of_mem_r2 hfl hK hf hU₂ (hAR a.2)
  obtain ⟨x, hx⟩ : ∃ x : ↥V → (Fin 3 → K), ∀ w, x w =
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w :=
    ⟨_, fun _ => rfl⟩
  have hmul : ∀ u u' : ↥V, x (u * u') = x u + x u' := fun u u' => by
    simp only [hx, hf.map_mul, Matrix.mulVec_add]
  have hker : ∀ u : ↥V, x u = 0 ↔ (u : G) ∈ Subgroup.centralizer (L : Set G) := fun u => by
    rw [← Subgroup.mem_subgroupOf, ← hf.ker, hx]
    constructor
    · intro h
      rw [← g_ginv_mulVec g (f u), h, Matrix.mulVec_zero]
    · intro h
      rw [h, Matrix.mulVec_zero]
  have hsurj : Function.Surjective x := fun y => by
    obtain ⟨u, hu⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ y)
    exact ⟨u, by rw [hx, hu, ginv_g_mulVec]⟩
  have hact : ∀ (a : ↥A) (w : ↥V),
      x (SecA.conjV V a (hAV a.2) w) = x w + x w 2 • ![b a, c a, 0] := fun a w => by
    rw [hx, hx, hbc a]
    exact sl3_act_formula hf g (b a) (c a) w
  have hV₂ : ∀ w : ↥V, (w : G) ∈ V₂ ↔ x w 2 = 0 := fun w => by
    change w ∈ V₂.subgroupOf V ↔ _
    rw [hU₂, hx]
    exact mem_pre_plane_iff hf g w
  have hV₁ : ∀ w : ↥V, (w : G) ∈ V₁ ↔ ∃ t : K, x w = t • ![1, 0, 0] := fun w => by
    change w ∈ V₁.subgroupOf V ↔ _
    rw [hU₁, mem_pre_line_iff hf g w]
    refine exists_congr fun t => ⟨fun h => ?_, fun h => ?_⟩
    · rw [hx, h, Matrix.mulVec_smul, ginv_g_mulVec]
    · rw [← g_ginv_mulVec g (f w), ← hx, h, Matrix.mulVec_smul]
  have hone' : ∀ a : ↥A, b a = 0 → c a = 0 → SecA.conjV V a (hAV a.2) = 1 := by
    intro a hb hc
    rw [hbc a, hb, hc, uSL_zero, mul_one, mul_inv_cancel, map_one, Subgroup.coe_one]
  have hone : ∀ a : ↥A, b a = 0 → c a = 0 → (a : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro a hb hc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg Subtype.val (DFunLike.congr_fun (hone' a hb hc) ⟨v, hv⟩)
    rw [SecA.conjV_apply_coe] at h1
    change (a : G) * v * (a : G)⁻¹ = v at h1
    calc v * (a : G) = a * v * (a : G)⁻¹ * a := by rw [h1]
      _ = a * v := by group
  have hV₂C : V₂ ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    intro v hv
    refine Subgroup.mem_inf.mpr ⟨hfl.le₂ hv, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have hO := mem_pCoreOf_of_rad2 hn hK hf g (b ⟨a, ha⟩) (c ⟨a, ha⟩)
    rw [← hU₂, ← show SecA.conjV V a (hAV ha) = _ from hbc ⟨a, ha⟩] at hO
    have h1 := congrArg Subtype.val (hlf.1 _ hO ⟨v, hfl.le₂ hv⟩ hv)
    rw [SecA.conjV_apply_coe] at h1
    change a * v * a⁻¹ = v at h1
    calc a * v = a * v * a⁻¹ * a := by group
      _ = v * a := by rw [h1]
  by_cases hsp : ∃ a₁ a₂ : ↥A, b a₁ * c a₂ - b a₂ * c a₁ ≠ 0
  · obtain ⟨a₁, a₂, hΔ⟩ := hsp
    have h₀ : (![b a₁, c a₁, 0] : Fin 3 → K) ≠ 0 := fun h => hΔ (by
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      simp at e0 e1
      rw [e0, e1, zero_mul, mul_zero, sub_zero])
    exact Or.inl ⟨sup_comm_eq_plane hmul hker hsurj hact hfl.le₂ hV₂ hΔ,
      inf_centralizer_eq_of_coord hact hV₂ hV₂C h₀⟩
  push Not at hsp
  have hA' : autOn A V ∈ E3.aSet n (autOn X V) := hA
  obtain ⟨a₀, h₀⟩ : ∃ a₀ : ↥A, b a₀ ≠ 0 ∨ c a₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hA'.2.1
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨a, ha, haV, rfl⟩ := SecA.mem_autOn_iff.mp hφ
    exact Subgroup.mem_bot.mpr (hone' ⟨a, ha⟩ (hcon ⟨a, ha⟩).1 (hcon ⟨a, ha⟩).2)
  have h₀' : (![b a₀, c a₀, 0] : Fin 3 → K) ≠ 0 := fun h => by
    rcases h₀ with h' | h'
    · exact h' (by simpa using congrFun h 0)
    · exact h' (by simpa using congrFun h 1)
  obtain ⟨r₁, r₂, hr⟩ : ∃ r₁ r₂ : K, r₁ * b a₀ + r₂ * c a₀ = 1 := by
    rcases h₀ with h | h
    · exact ⟨(b a₀)⁻¹, 0, by rw [zero_mul, add_zero, inv_mul_cancel₀ h]⟩
    · exact ⟨0, (c a₀)⁻¹, by rw [zero_mul, zero_add, inv_mul_cancel₀ h]⟩
  have hd : ∀ a : ↥A, ∃ t : K, (![b a, c a, 0] : Fin 3 → K) = t • ![b a₀, c a₀, 0] := by
    intro a
    have h := hsp a a₀
    refine ⟨r₁ * b a + r₂ * c a, funext fun i => ?_⟩
    fin_cases i <;> simp
    · linear_combination (-b a) * hr + r₂ * h
    · linear_combination (-c a) * hr - r₁ * h
  have hcen := inf_centralizer_eq_of_coord hact hV₂ hV₂C h₀'
  obtain ⟨P, hPV, hPm⟩ := exists_line_subgroup K hmul ![b a₀, c a₀, 0]
  have hsup := sup_comm_eq_line hmul hker hsurj hact hd hPV hPm
  refine Or.inr ⟨le_antisymm ?_ (le_mQuot_of_aSet hfl.elem hAV hA), ?_, ?_⟩
  · apply mQuot_le_of_relIndex_le
    rw [← hK]
    exact relIndex_le_of_line hsurj hact h₀ hd hone
  · rw [hcen]
    unfold E3.mQuot
    rw [relIndex_eq_card_of_hom (fun w => x w 2) (fun u u' => by simp only [hmul, Pi.add_apply])
      (fun t => (hsurj ![0, 0, t]).imp fun w hw => show x w 2 = t by rw [hw]; rfl) hV₂, hK,
      padicValNat.prime_pow]
  have hu : (![b a₀, c a₀] : Fin 2 → K) ≠ 0 := fun h => by
    rcases h₀ with h' | h'
    · exact h' (by simpa using congrFun h 0)
    · exact h' (by simpa using congrFun h 1)
  obtain ⟨B₂, hB₂⟩ := Ch10.SecC.C10KH.exists_sl2_mulVec_eq_single hu
  have hMe : (blockSL B₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![b a₀, c a₀, 0] := by
    have e0 := congrFun hB₂ 0
    have e1 := congrFun hB₂ 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
    rw [blockSL_mulVec]
    refine KGNat.vec3_eq ?_ ?_ (by simp) <;> simp [e0, e1]
  have hmem : ((rho3 π (g * blockSL B₂ * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) ∈
      autOn (LOf L V₂) V := by
    rw [SecA.autOn_lOf hfl.le_normalizer hfl.le₂, hU₂]
    exact (mem_perfectCore_HU2_iff hSL hf g _).mpr ⟨blockSL B₂, blockSL_mem B₂, rfl⟩
  obtain ⟨l, hl, hlV, hlM⟩ := SecA.mem_autOn_iff.mp hmem
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have hlx : ∀ w : ↥V, x (SecA.conjV V l hlV w) =
      (blockSL B₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ x w := fun w => by
    rw [← hlM, hx, hx, hf.act3, gconj_mulVec, ginv_g_mulVec]
  refine ⟨l, hl, ?_⟩
  rw [sup_commutator_conj (hL₂L hl) hlV, hsup]
  refine conjSubgroup_eq_of hV₁V hPV hlV fun w hw => (hV₁ ⟨w, hw⟩).trans ?_
  rw [show l * w * l⁻¹ = ((SecA.conjV V l hlV ⟨w, hw⟩ : ↥V) : G) by
    rw [SecA.conjV_apply_coe], hPm, hlx]
  refine exists_congr fun t => ⟨fun h => by rw [h, Matrix.mulVec_smul, hMe], fun h => ?_⟩
  rw [← hMe, ← Matrix.mulVec_smul] at h
  have h' := congrArg (fun y => (((blockSL B₂)⁻¹ : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ y) h
  simpa only [ginv_g_mulVec] using h'

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
