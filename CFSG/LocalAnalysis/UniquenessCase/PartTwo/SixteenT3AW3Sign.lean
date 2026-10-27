module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Moves
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Single

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {T : Type} [CommGroup T] [Finite T] {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
  {X : Subgroup (MulAut T)}

private theorem s16t_w3_sign_logic {ι : Type} (P : ι → Prop) {i j k : ι} (hki : k ≠ i)
    (hkj : k ≠ j) (hcov : ∀ n, n = i ∨ n = j ∨ n = k)
    (aux : ∀ m, (∀ n, n ≠ m → (P n ↔ ¬ P m)) → False) : P i ↔ P j := by
  by_contra hne
  by_cases hk : P k ↔ P i
  · refine aux j fun n hn => ?_
    rcases hcov n with rfl | rfl | rfl
    · tauto
    · exact absurd rfl hn
    · tauto
  · refine aux i fun n hn => ?_
    rcases hcov n with rfl | rfl | rfl
    · exact absurd rfl hn
    · tauto
    · tauto

theorem s16t_w3_sign (h : S16tW3Hyp Y X) {S : Subgroup (MulAut T)}
    (hS : ∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1)
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {f : MulAut T} (hfX : f ∈ X) (hf3 : f ^ 3 = 1)
    (hfm : ∃ i, (Y i).map f.toMonoidHom ≠ Y i) {b : MulAut T} (hbX : b ∈ X)
    (hb : ∀ i, (Y i).map b.toMonoidHom = Y i) (i j : ι) :
    (∀ y ∈ Y i, (b ^ 3) y = y) ↔ ∀ y ∈ Y j, (b ^ 3) y = y := by
  have hmem : ∀ (g : MulAut T) n, (Y n).map g.toMonoidHom = Y n → ∀ y ∈ Y n, g y ∈ Y n :=
    fun g n hg y hy => hg.le (Subgroup.mem_map_of_mem g.toMonoidHom hy)
  have aux : ∀ m, (∀ n, n ≠ m →
      ((∀ y ∈ Y n, (b ^ 3) y = y) ↔ ¬ ∀ y ∈ Y m, (b ^ 3) y = y)) → False := by
    intro m hm
    obtain ⟨s, hs, y₀, hy₀, hmove⟩ := s16t_w3_S_moves h hS hSc hfX hf3 hfm m
    obtain ⟨-, hsY, hs3⟩ := (hS s).1 hs
    have hs3' : ∀ n, ∀ y ∈ Y n, (s ^ 3) y = y := fun n y _ => by
      rw [hs3]
      rfl
    have hbsb : b * s * b⁻¹ ∈ S := s16t_w3_conj_mem h hS hbX hs
    have hss : s (s y₀) = y₀ → False := fun h1 => hmove (by
      calc s y₀ = s (s (s y₀)) := by rw [h1]
        _ = (s ^ 3) y₀ := by rw [pow_three]; rfl
        _ = y₀ := hs3' m y₀ hy₀)
    by_cases hsm : ∀ y ∈ Y m, (b ^ 3) y = y
    · have hfixn : ∀ n, n ≠ m → ∀ y ∈ Y n, (b * s * b⁻¹ * s) y = y := by
        intro n hn y hy
        have hbn : ¬ ∀ y ∈ Y n, (b ^ 3) y = y := fun h' => (hm n hn).1 h' hsm
        have hc := (s16t_w3_conj (h.card_eq_four n) (hb n) (hsY n) (hs3' n)).2 hbn (s y)
          (hmem s n (hsY n) y hy)
        rw [MulAut.mul_apply, hc, MulAut.inv_apply_self]
      have h1 := s16t_w3_no_single h hS hSc hfX hf3 hfm (S.mul_mem hbsb hs) hfixn y₀ hy₀
      have hc := (s16t_w3_conj (h.card_eq_four m) (hb m) (hsY m) (hs3' m)).1 hsm (s y₀)
        (hmem s m (hsY m) y₀ hy₀)
      rw [MulAut.mul_apply, hc] at h1
      exact hss h1
    · have hfixn : ∀ n, n ≠ m → ∀ y ∈ Y n, (b * s * b⁻¹ * s⁻¹) y = y := by
        intro n hn y hy
        have hbn : ∀ y ∈ Y n, (b ^ 3) y = y := (hm n hn).2 hsm
        have hc := (s16t_w3_conj (h.card_eq_four n) (hb n) (hsY n) (hs3' n)).1 hbn (s⁻¹ y)
          (hmem s⁻¹ n (s16t_w3_map_inv (hsY n)) y hy)
        rw [MulAut.mul_apply, hc, MulAut.apply_inv_self]
      have h1 := s16t_w3_no_single h hS hSc hfX hf3 hfm (S.mul_mem hbsb (S.inv_mem hs)) hfixn
        y₀ hy₀
      have hc := (s16t_w3_conj (h.card_eq_four m) (hb m) (hsY m) (hs3' m)).2 hsm (s⁻¹ y₀)
        (hmem s⁻¹ m (s16t_w3_map_inv (hsY m)) y₀ hy₀)
      rw [MulAut.mul_apply, hc] at h1
      have e1 : s⁻¹ y₀ = s y₀ := by
        calc s⁻¹ y₀ = s (s⁻¹ (s⁻¹ y₀)) := (MulAut.apply_inv_self _ _ _).symm
          _ = s y₀ := by rw [h1]
      refine hss ?_
      calc s (s y₀) = s (s⁻¹ y₀) := by rw [e1]
        _ = y₀ := MulAut.apply_inv_self _ _ _
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨i₁, i₂, -, -, -, hi₁, hi₂, h12, hall⟩ := s16t_w3_cycle h hfX hf3 hfm i
  rcases hall j with hj | hj | hj
  · exact absurd hj.symm hij
  · refine s16t_w3_sign_logic (fun n => ∀ y ∈ Y n, (b ^ 3) y = y) (k := i₂) (Ne.symm hi₂)
      (hj ▸ Ne.symm h12) (fun n => ?_) aux
    rcases hall n with hn | hn | hn
    · exact Or.inl hn
    · exact Or.inr (Or.inl (hn.trans hj.symm))
    · exact Or.inr (Or.inr hn)
  · refine s16t_w3_sign_logic (fun n => ∀ y ∈ Y n, (b ^ 3) y = y) (k := i₁) (Ne.symm hi₁)
      (hj ▸ h12) (fun n => ?_) aux
    rcases hall n with hn | hn | hn
    · exact Or.inl hn
    · exact Or.inr (Or.inr hn)
    · exact Or.inr (Or.inl (hn.trans hj.symm))

theorem s16t_w3_comm_mem (h : S16tW3Hyp Y X) {S : Subgroup (MulAut T)}
    (hS : ∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1)
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {f : MulAut T} (hfX : f ∈ X) (hf3 : f ^ 3 = 1)
    (hfm : ∃ i, (Y i).map f.toMonoidHom ≠ Y i) {b : MulAut T} (hbX : b ∈ X)
    (hb : ∀ i, (Y i).map b.toMonoidHom = Y i) : b * f * b⁻¹ * f⁻¹ ∈ S := by
  have hd : ∀ i, (Y i).map (f * b⁻¹ * f⁻¹).toMonoidHom = Y i := by
    intro i
    obtain ⟨j, hj⟩ := h.perm f⁻¹ (X.inv_mem hfX) i
    rw [s16t_w3_map_mul, s16t_w3_map_mul, hj, s16t_w3_map_inv (hb j), ← hj, ← s16t_w3_map_mul,
      mul_inv_cancel, s16t_w3_map_one]
  have hc : b * f * b⁻¹ * f⁻¹ = b * (f * b⁻¹ * f⁻¹) := by group
  refine (hS _).2 ⟨X.mul_mem (X.mul_mem (X.mul_mem hbX hfX) (X.inv_mem hbX)) (X.inv_mem hfX),
    fun i => by rw [hc, s16t_w3_map_mul, hd i, hb i], ?_⟩
  rw [hc]
  refine s16t_w3_ext h.iSup_eq_top fun i y hy => ?_
  show ((b * (f * b⁻¹ * f⁻¹)) ^ 3) y = y
  refine (s16t_w3_cube_mul (h.card_eq_four i) (hb i) (hd i)).2 ?_ y hy
  obtain ⟨j, hj⟩ := h.perm f⁻¹ (X.inv_mem hfX) i
  have hji : (Y j).map f.toMonoidHom = Y i := by
    rw [← hj, ← s16t_w3_map_mul, mul_inv_cancel, s16t_w3_map_one]
  rw [s16t_w3_sign h hS hSc hfX hf3 hfm hbX hb i j, conj_pow]
  constructor
  · intro hbj u hu
    have hu' : f⁻¹ u ∈ Y j := hj ▸ Subgroup.mem_map_of_mem f⁻¹.toMonoidHom hu
    have h1 : (b ^ 3) (f⁻¹ u) = f⁻¹ u := hbj _ hu'
    have h2 : (b⁻¹ ^ 3) (f⁻¹ u) = f⁻¹ u := by
      rw [inv_pow]
      calc (b ^ 3)⁻¹ (f⁻¹ u) = (b ^ 3)⁻¹ ((b ^ 3) (f⁻¹ u)) := by rw [h1]
        _ = f⁻¹ u := MulAut.inv_apply_self _ _ _
    rw [MulAut.mul_apply, MulAut.mul_apply, h2, MulAut.apply_inv_self]
  · intro hfi z hz
    have hfz : f z ∈ Y i := hji ▸ Subgroup.mem_map_of_mem f.toMonoidHom hz
    have h1 := hfi (f z) hfz
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h1
    have h2 : (b⁻¹ ^ 3) z = z := f.injective h1
    rw [inv_pow] at h2
    calc (b ^ 3) z = (b ^ 3) ((b ^ 3)⁻¹ z) := by rw [h2]
      _ = z := MulAut.apply_inv_self _ _ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
