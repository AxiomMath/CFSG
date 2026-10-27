module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2V2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2Z
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Main

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

theorem fin5_pair_det : ∀ a b i j : Fin 5, a ≠ b → i ≠ j →
    (i = midlab a b ∨ i = kstar a b ∨ i = kstar b a) →
    (j = midlab a b ∨ j = kstar a b ∨ j = kstar b a) →
    i ≠ midlab a b → j ≠ midlab a b →
    (a = kstar i j ∧ b = kstar j i) ∨ (a = kstar j i ∧ b = kstar i j) := by
  unfold midlab kstar
  decide

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem exists_vc (h7 : Fan7 F L) {v : G} (hv : v ∈ ballStab Γ G 2 α) :
    ∃ ζ ∈ L.zGroup 2 α, ∃ c ∈ D.calpha, v = ζ * c := by
  have h71c : Fan71c F L := h7.2.2.1
  have hcomm : ∀ ζ ∈ L.zGroup 2 α, ∀ c ∈ D.calpha, ζ * c = c * ζ := fun ζ hζ c hc =>
    (F87.ballStab_comm h71c (F87.calpha_le_ballStab h7 D hc) hζ).symm
  let S : Subgroup G :=
    { carrier := {x | ∃ ζ ∈ L.zGroup 2 α, ∃ c ∈ D.calpha, x = ζ * c}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (one_mul 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨ζ, hζ, c, hc, rfl⟩ ⟨ζ', hζ', c', hc', rfl⟩
        refine ⟨ζ * ζ', mul_mem hζ hζ', c * c', mul_mem hc hc', ?_⟩
        have := hcomm ζ' hζ' c hc
        calc ζ * c * (ζ' * c') = ζ * (c * ζ') * c' := by group
          _ = ζ * (ζ' * c) * c' := by rw [← this]
          _ = ζ * ζ' * (c * c') := by group
      inv_mem' := by
        rintro _ ⟨ζ, hζ, c, hc, rfl⟩
        refine ⟨ζ⁻¹, inv_mem hζ, c⁻¹, inv_mem hc, ?_⟩
        have h1 : c * ζ = ζ * c := (hcomm ζ hζ c hc).symm
        calc (ζ * c)⁻¹ = c⁻¹ * ζ⁻¹ := mul_inv_rev _ _
          _ = ζ⁻¹ * c⁻¹ := by
            have : (c * ζ)⁻¹ = (ζ * c)⁻¹ := by rw [h1]
            rwa [mul_inv_rev, mul_inv_rev, eq_comm] at this }
  have hle : ballStab Γ G 2 α ≤ S := by
    rw [(F87.fan73b_dset h7 D).1]
    exact sup_le (fun ζ hζ => ⟨ζ, hζ, 1, one_mem _, (mul_one ζ).symm⟩)
      (fun c hc => ⟨1, one_mem _, c, hc, (one_mul c).symm⟩)
  exact hle hv

theorem fcomm_y_mem_mul_calpha (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h82 : Fan82a F L) (h512 : Fan512 F L) {δ' : V} (hY : D.IsYPair δ') {i j : Fin 5}
    (hij : i ≠ j) : ∃ c ∈ D.calpha, fcomm (D.y δ' i) (D.y δ' j) =
      (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) * c := by
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨ζ, hζ, c, hc, hvζ⟩ := D.exists_vc h7 (D.fcomm_y_mem_ballStab F h7 h81 hY i j)
  have hact : ∀ (k : Fin 5) (n : ℕ), n ≤ 4 →
      fcomm (D.y δ' i) (D.y δ' j) • (D.P k).vert n = ζ • (D.P k).vert n := by
    intro k n hn
    rw [hvζ, mul_smul, D.fix_of_mem_calpha F h7.1 h71c hc k hn]
  have hξi : fcomm (D.y δ' i) (D.y δ' j) • (D.P i).vert 3 = (D.P i).vert 3 :=
    D.fcomm_y_fixes_ball_left F h71c h81 hY i j _ (D.dist_beta_xi F i).le
  have hξj : fcomm (D.y δ' i) (D.y δ' j) • (D.P j).vert 3 = (D.P j).vert 3 :=
    D.fcomm_y_fixes_ball_right F h71c h81 hY i j _ (D.dist_beta_xi F j).le
  have hδi := D.fcomm_y_moves_delta_left F h71c h81 hY hij
  have hδj := D.fcomm_y_moves_delta_right F h71c h81 hY hij
  have hzα : ∀ (k : Fin 5) (n : ℕ), n ≤ 4 → L.z α • (D.P k).vert n = (D.P k).vert n :=
    fun k n hn => (h71c.z_smul_eq_iff D.val _).2 (by rw [D.dist_vert F k hn]; exact hn)
  have hpow : ∀ (e : Bool) (k : Fin 5) (n : ℕ), n ≤ 4 →
      powB (L.z α) e • (D.P k).vert n = (D.P k).vert n := by
    intro e k n hn
    cases e <;> simp [powB, hzα k n hn]
  obtain ⟨e, hshape⟩ := D.zGroup_shapes h7 h82 h512 ζ hζ
  rcases hshape with h1 | ⟨l, h1⟩ | ⟨a, b, hab, h1⟩
  · exfalso
    apply hδi
    rw [show D.delta i = (D.P i).vert 4 from rfl, hact i 4 le_rfl, h1]
    exact hpow e i 4 le_rfl
  · exfalso
    have key : ∀ k : Fin 5, k ≠ l →
        fcomm (D.y δ' i) (D.y δ' j) • (D.P k).vert 3 ≠ (D.P k).vert 3 := by
      intro k hkl hfix
      rw [hact k 3 (by norm_num), h1, mul_smul] at hfix
      have hw := hpow e k 3 (by norm_num)
      have hz : L.z (D.alpha l) • (D.P k).vert 3 = (D.P k).vert 3 :=
        MulAction.injective (powB (L.z α) e) (hfix.trans hw.symm)
      have h5 := (h71c.z_smul_eq_iff (D.valence_alpha F l) _).1 hz
      have h6 := D.dist_vert_ne F h71c (Ne.symm hkl) (m := 2) (m' := 3) (by norm_num)
        (by norm_num)
      have h7' : Γ.dist (D.alpha l) ((D.P k).vert 3) = 2 + 3 := h6
      omega
    by_cases hil : i = l
    · exact key j (fun hjl => hij (hil.trans hjl.symm)) hξj
    · exact key i hil hξi
  · have hpowC : ∀ e : Bool, powB (L.z α) e ∈ D.calpha := by
      intro e
      cases e
      · exact one_mem _
      · exact D.z_mem_calpha F h71c h512
    have hcommz : ∀ (e : Bool) (s : Fin 5),
        powB (L.z α) e * L.z (D.alpha s) = L.z (D.alpha s) * powB (L.z α) e := by
      intro e s
      cases e
      · simp [powB]
      · exact h71c.z_comm_of_dist_le D.val (D.valence_alpha F s)
          (by rw [D.dist_start_alpha F s]; norm_num)
    have hcommzz : ∀ s t : Fin 5,
        L.z (D.alpha s) * L.z (D.alpha t) = L.z (D.alpha t) * L.z (D.alpha s) := by
      intro s t
      by_cases hst : s = t
      · rw [hst]
      · exact h71c.z_comm_of_dist_le (D.valence_alpha F s) (D.valence_alpha F t)
          (by rw [D.dist_alpha_alpha F h71c hst])
    have hcommP : ∀ (e : Bool) (s t : Fin 5), powB (L.z α) e * (L.z (D.alpha s) * L.z (D.alpha t)) =
        (L.z (D.alpha s) * L.z (D.alpha t)) * powB (L.z α) e := by
      intro e s t
      rw [← mul_assoc, hcommz e s, mul_assoc, hcommz e t, ← mul_assoc]
    have hiff : ∀ (k : Fin 5) (n : ℕ), n ≤ 4 →
        (fcomm (D.y δ' i) (D.y δ' j) • (D.P k).vert n = (D.P k).vert n ↔
          (L.z (D.alpha a) * L.z (D.alpha b)) • (D.P k).vert n = (D.P k).vert n) := by
      intro k n hn
      rw [hact k n hn, h1, mul_smul]
      have hw := hpow e k n hn
      constructor
      · intro hfix
        exact MulAction.injective (powB (L.z α) e) (hfix.trans hw.symm)
      · intro hfix
        rw [hfix, hw]
    have hclean : ∀ k : Fin 5, (L.z (D.alpha a) * L.z (D.alpha b)) • (D.P k).vert 3 =
        (D.P k).vert 3 → (k = midlab a b ∨ k = kstar a b ∨ k = kstar b a) := by
      intro k hk
      rcases (D.fixed_iff F h7 h512 hab k (n := 3) (by norm_num)).1 hk with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact absurd h (by norm_num)
      · exact Or.inr h
    have hmv : ∀ k : Fin 5, fcomm (D.y δ' i) (D.y δ' j) • (D.P k).vert 4 ≠ (D.P k).vert 4 →
        k ≠ midlab a b := by
      intro k hk e'
      exact hk ((hiff k 4 (by norm_num)).2
        ((D.fixed_iff F h7 h512 hab k (n := 4) (by norm_num)).2 (Or.inl e')))
    obtain hdet := fin5_pair_det a b i j hab hij (hclean i ((hiff i 3 (by norm_num)).1 hξi))
      (hclean j ((hiff j 3 (by norm_num)).1 hξj)) (hmv i hδi) (hmv j hδj)
    refine ⟨powB (L.z α) e * c, mul_mem (hpowC e) hc, ?_⟩
    rcases hdet with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hvζ, h1, hcommP e, mul_assoc]
    · rw [hvζ, h1, hcommP e, hcommzz (kstar j i) (kstar i j), mul_assoc]

end D10Set

end CFSG.Quasithin.Fan86
