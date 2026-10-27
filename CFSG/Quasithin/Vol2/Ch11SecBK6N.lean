module

public import CFSG.Quasithin.Vol2.Ch11SecBK6K
public import CFSG.Quasithin.Vol2.Ch11SecBK6M

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spLevi_mem_perfectCore)
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative commutatorElement

namespace BK6

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem r2Line_sp4 (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSp4 L V n) {A : Subgroup G}
    (hAR : A ≤ pCoreOf 2 (LOf L V₂ ⊔ T)) (hA : autI hfl.elem A ∈ E3.aSet n (autI hfl.elem X)) :
    (⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₂ ∧
        V ⊓ Subgroup.centralizer (A : Set G) = V₂) ∨
      (E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = n ∧
        E3.mQuot V (V ⊓ Subgroup.centralizer (A : Set G)) = n ∧
        ∃ l ∈ LOf L V₂, ⁅V, conjSubgroup A l⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, K, _, _, _, hK, π, f, hf, g, -, hU₁, hU₂⟩ := K7.exists_coord_flag24 hfl hk
  have hn := hfl.two_le
  have hK4 : ∃ s : Finset K, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hZ : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, h z = z :=
    fun h hh z hz => SecA.autOn_fixes_cV h hh z hz
  have hV₁V : V₁ ≤ V := hfl.le₁₂.trans hfl.le₂
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun a ha => K7.r2_le_normalizer hfl (hAR ha)
  choose α β γ hq using fun a : ↥A => K7.exists_qSp_of_mem_r2 hfl hK hf hU₂ (hAR a.2)
  obtain ⟨x, hx⟩ : ∃ x : ↥V → (Fin 2 ⊕ Fin 2 → K), ∀ w, x w = mat 2 K g⁻¹ *ᵥ f w :=
    ⟨_, fun _ => rfl⟩
  have hmul : ∀ u u' : ↥V, x (u * u') = x u + x u' := fun u u' => by
    simp only [hx, hf.map_mul, Matrix.mulVec_add]
  have hker : ∀ u : ↥V, x u = 0 ↔ (u : G) ∈ Subgroup.centralizer (L : Set G) := fun u => by
    rw [← Subgroup.mem_subgroupOf, ← hf.ker, hx]
    constructor
    · intro h
      rw [← mat_mulVec_inv g (f u), h, Matrix.mulVec_zero]
    · intro h
      rw [h, Matrix.mulVec_zero]
  have hsurj : Function.Surjective x := fun y => by
    obtain ⟨u, hu⟩ := hf.surj (mat 2 K g *ᵥ y)
    exact ⟨u, by rw [hx, hu, mat_inv_mulVec]⟩
  have hact : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w +
      vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0 := fun a w => by
    rw [hx, hx, hq a, hf.act4, KA.gconj_mulVec_sp, mat_inv_mulVec, qSp_mulVec]
    refine vec4_eq ?_ ?_ ?_ ?_ <;>
      simp only [Pi.add_apply, vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
        vec4_apply_inr1, add_zero] <;> ring
  have hfix : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w →
      SecA.conjV V a (hAV a.2) w = w := fun a w h => by
    rw [hq a] at h ⊢
    apply KA.fix_of_mulVec_eq hK4 hf hZ
    rw [hx, hx] at h
    rw [← hf.act4]
    have h' := congrArg (fun y => mat 2 K g *ᵥ y) h
    simpa only [mat_mulVec_inv] using h'
  have hV₂ : ∀ w : ↥V, (w : G) ∈ V₂ ↔ x w (.inr 0) = 0 ∧ x w (.inr 1) = 0 := fun w => by
    change w ∈ V₂.subgroupOf V ↔ _
    rw [hU₂, hx]
    change f w ∈ gmapSp g (spPlane K) ↔ _
    rw [mem_gmapSp]
    rfl
  have hV₁ : ∀ w : ↥V, (w : G) ∈ V₁ ↔ ∃ t : K, x w = t • vec4 1 0 0 0 := fun w => by
    change w ∈ V₁.subgroupOf V ↔ _
    rw [hU₁]
    change f w ∈ gmapSp g (spLine K) ↔ _
    rw [mem_gmapSp_spLine_iff]
    refine exists_congr fun t => ⟨fun h => ?_, fun h => ?_⟩
    · rw [hx, h, Matrix.mulVec_smul, mat_inv_mulVec]
    · rw [← mat_mulVec_inv g (f w), ← hx, h, Matrix.mulVec_smul]
  by_cases hdet : ∃ a₀ : ↥A, α a₀ * γ a₀ - β a₀ ^ 2 ≠ 0
  · obtain ⟨a₀, hD⟩ := hdet
    exact Or.inl ⟨sup_comm_eq_plane_sp hmul hker hsurj hact hfl.le₂ hV₂ hD,
      inf_centralizer_eq_of_det_sp hact hfix hfl.le₂ hV₂ hD⟩
  push Not at hdet
  have hsing : ∀ a : ↥A, α a * γ a = β a ^ 2 := fun a => sub_eq_zero.mp (hdet a)
  have hA' : autOn A V ∈ E3.aSet n (autOn X V) := hA
  obtain ⟨a₀, h₀⟩ : ∃ a₀ : ↥A, ¬ (α a₀ = 0 ∧ β a₀ = 0 ∧ γ a₀ = 0) := by
    by_contra hcon
    push Not at hcon
    apply hA'.2.1
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨a, ha, haV, rfl⟩ := SecA.mem_autOn_iff.mp hφ
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun w => hfix ⟨a, ha⟩ w ?_
    obtain ⟨h1, h2, h3⟩ := hcon ⟨a, ha⟩
    rw [hact, h1, h2, h3]
    simp only [zero_mul, add_zero, vec4_zero]
  have hsum : ∀ a : ↥A, (α a + α a₀) * (γ a + γ a₀) = (β a + β a₀) ^ 2 := fun a => by
    obtain ⟨h1, h2, h3⟩ := add_params_sp hsurj hact a a₀
    rw [← h1, ← h2, ← h3]
    exact hsing (a * a₀)
  obtain ⟨r₀, r₁, ⟨u, v, huv⟩, hform⟩ := exists_root_form hsing a₀ hsum h₀
  choose t ht using hform
  have ht₀ : t a₀ ≠ 0 := fun h => h₀ ⟨by rw [(ht a₀).1, h, zero_mul],
    by rw [(ht a₀).2.1, h, zero_mul], by rw [(ht a₀).2.2, h, zero_mul]⟩
  obtain ⟨P, hPV, hPm⟩ := exists_line_subgroup K hmul (vec4 r₀ r₁ 0 0)
  have hsup := sup_comm_eq_line_sp hmul hker hsurj hact huv ht ht₀ hPV hPm
  refine Or.inr ⟨le_antisymm ?_ (le_mQuot_of_aSet hfl.elem hAV hA), ?_, ?_⟩
  · apply mQuot_le_of_relIndex_le
    rw [← hK]
    exact relIndex_le_of_line_sp hsurj hact hfix huv ht
  · unfold E3.mQuot
    rw [relIndex_inf_centralizer_sp hmul hsurj hact hfix huv ht ht₀, hK, padicValNat.prime_pow]
  have hr : (![r₀, r₁] : Fin 2 → K) ≠ 0 := fun h => by
    have e0 : r₀ = 0 := by simpa using congrFun h 0
    have e1 : r₁ = 0 := by simpa using congrFun h 1
    rw [e0, e1, mul_zero, mul_zero, add_zero] at huv
    exact zero_ne_one huv
  obtain ⟨B₂, hB₂⟩ := Ch10.SecC.C10KH.exists_sl2_mulVec_eq_single hr
  have hMe : mat 2 K (spLevi 1 B₂) *ᵥ vec4 1 0 0 0 = vec4 r₀ r₁ 0 0 := by
    have e0 := congrFun hB₂ 0
    have e1 := congrFun hB₂ 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
    rw [KA.spLevi1_mulVec_plane B₂ ⟨rfl, rfl⟩]
    refine vec4_eq ?_ ?_ rfl rfl <;> simp [vec4, e0, e1]
  have hmem : psiSp π g (spLevi 1 B₂) ∈ autOn (LOf L V₂) V := by
    rw [SecA.autOn_lOf hfl.le_normalizer hfl.le₂, hU₂, KA.gamma2_eq hf g]
    exact ⟨_, spLevi_mem_perfectCore hK4 1 B₂, rfl⟩
  obtain ⟨l, hl, hlV, hlM⟩ := SecA.mem_autOn_iff.mp hmem
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have hlx : ∀ w : ↥V, x (SecA.conjV V l hlV w) = mat 2 K (spLevi 1 B₂) *ᵥ x w := fun w => by
    rw [← hlM, hx, hx]
    exact KA.act_levi1 hf g B₂ w
  refine ⟨l, hl, ?_⟩
  rw [sup_commutator_conj (hL₂L hl) hlV, hsup]
  refine conjSubgroup_eq_of hV₁V hPV hlV fun w hw => (hV₁ ⟨w, hw⟩).trans ?_
  rw [show l * w * l⁻¹ = ((SecA.conjV V l hlV ⟨w, hw⟩ : ↥V) : G) by
    rw [SecA.conjV_apply_coe], hPm, hlx]
  refine exists_congr fun c => ⟨fun h => by rw [h, Matrix.mulVec_smul, hMe], fun h => ?_⟩
  rw [← hMe, ← Matrix.mulVec_smul] at h
  have h' := congrArg (fun y => mat 2 K (spLevi 1 B₂)⁻¹ *ᵥ y) h
  simpa only [mat_inv_mulVec] using h'

end BK6

theorem factR2Line_holds : FactR2Line := by
  intro G _ _ L V X T V₁ V₂ n h A hAR _ hA
  rcases h.kind with hk | hk
  · exact BK6.r2Line_sl3 h hk hAR hA
  · exact BK6.r2Line_sp4 h hk hAR hA

end CFSG.Quasithin.Vol2.Ch11.SecB
