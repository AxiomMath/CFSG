module

public import CFSG.Quasithin.Vol2.Ch11G2Q8SiegelM
public import CFSG.Quasithin.Background.HTriPermute

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8

variable {K : Type} [Field K] [CharP K 2]

theorem ht_swap (k : Ix3) : ht (Sum.swap k) = 5 - ht k := by
  rcases k with k | k <;> fin_cases k <;> rfl

omit [CharP K 2] in
theorem polarQ_eq_sum (x y : Ix3 → K) : polarQ x y = ∑ k, x k * y (Sum.swap k) := by
  simp only [polarQ, Fintype.sum_sum_type, Fin.sum_univ_three, Sum.swap_inl, Sum.swap_inr]
  ring

omit [CharP K 2] in
theorem perp_iff {h : ℕ} (hh : h ≤ 6) (x : Ix3 → K) :
    (∀ y ∈ stdF K h, polarQ x y = 0) ↔ x ∈ stdF K (6 - h) := by
  constructor
  · intro H
    refine mem_stdF.mpr fun k hk => ?_
    have hy : (Pi.single (Sum.swap k) 1 : Ix3 → K) ∈ stdF K h := by
      refine mem_stdF.mpr fun k' hk' => ?_
      rw [Pi.single_apply, ite_eq_right]
      rintro rfl
      rw [ht_swap] at hk'
      have := ht_lt_six k
      omega
    have h1 := H _ hy
    rw [polarQ_eq_sum, Finset.sum_eq_single k] at h1
    · simpa using h1
    · intro k' _ hk'
      have hne : Sum.swap k' ≠ Sum.swap k := fun h' => hk' (by simpa using congrArg Sum.swap h')
      rw [Pi.single_apply, ite_eq_right hne, mul_zero]
    · simp
  · intro hx y hy
    rw [polarQ_eq_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases Nat.lt_or_ge (ht k) (6 - h) with hlt | hge
    · rw [hy (Sum.swap k) (by rw [ht_swap]; omega), mul_zero]
    · rw [hx k hge, zero_mul]

theorem polarQ_maps {S : Submodule K (Ix3 → K)} {g : ↥(cayleyGroup K)} (hg : g ∈ stabQ S)
    {x : Ix3 → K} (hx : ∀ y ∈ S, polarQ x y = 0) : ∀ y ∈ S, polarQ (g2Act g x) y = 0 := by
  intro y hy
  have h1 : g2Act g⁻¹ y ∈ S := by
    rw [mem_stabQ.mp hg, g2Act_apply_inv]
    exact hy
  rw [← g2Act_apply_inv g y, polarQ_g2Act]
  exact hx _ h1

theorem stabQ_le_perp {h : ℕ} (hh : h ≤ 6) : stabQ (stdF K h) ≤ stabQ (stdF K (6 - h)) := by
  intro g hg
  have hg' := (stabQ (stdF K h)).inv_mem hg
  refine mem_stabQ.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · exact (perp_iff hh _).mp (polarQ_maps hg ((perp_iff hh w).mpr hw))
  · have := (perp_iff hh _).mp (polarQ_maps hg' ((perp_iff hh _).mpr hw))
    rwa [g2Act_inv_apply] at this

theorem stabQ_le_one_or_two {h : ℕ} (h1 : 1 ≤ h) (h5 : h ≤ 5) :
    stabQ (stdF K h) ≤ stabQ (stdF K 1) ∨ stabQ (stdF K h) ≤ stabQ (stdF K 2) := by
  interval_cases h
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl
  · exact Or.inl stabQ_three_le_one
  · exact Or.inr (stabQ_le_perp (h := 4) (by norm_num))
  · exact Or.inl (stabQ_le_perp (h := 5) (by norm_num))

theorem U0_le_stabQ (h : ℕ) : U0 K ≤ stabQ (stdF K h) := by
  intro u hu
  refine mem_stabQ.mpr fun w => ⟨fun hw => FlagUni.mem hu hw, fun hw => ?_⟩
  have := FlagUni.mem ((U0 K).inv_mem hu) hw
  rwa [g2Act_inv_apply] at this

theorem g2Act_tL_sub' (s : K) (w : Ix3 → K) :
    g2Act (tL s) w - w = q6 (s * w (.inl 2)) 0 0 0 0 (s * w (.inr 0)) := by
  conv_lhs => rw [q6_eta w, g2Act_tL]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem tL_zero' : tL (0 : K) = 1 :=
  cayley_eq_one fun w => by
    have h := g2Act_tL_sub' (0 : K) w
    simp only [zero_mul] at h
    rw [← sub_eq_zero, h]
    funext k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem tL_mul_self' (s : K) : tL s * tL s = 1 := by
  rw [tL_mul, CharTwo.add_self_eq_zero, tL_zero']

theorem tL_injective : Function.Injective (tL (F := K)) := by
  intro s t h
  have h1 := g2Act_tL_sub' s (q6 0 0 1 0 0 0)
  rw [h, g2Act_tL_sub'] at h1
  have := congrFun h1 (.inl 0)
  simpa [q6] using this.symm

theorem tL_mem_U0' (s : K) : tL s ∈ U0 K := by
  intro h w hw
  rw [g2Act_tL_sub']
  refine inF_q6_iff.mpr ⟨fun hh => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun hh => ?_⟩
  · have h1 : h = 0 := by omega
    subst h1
    rw [hw (.inl 2) (by decide), mul_zero]
  · have h1 : w (.inr 0) = 0 := hw (.inr 0) (by
      have : ht (.inr 0) = 5 := rfl
      omega)
    rw [h1, mul_zero]

@[expose] def longRoot (K : Type) [Field K] [CharP K 2] : Subgroup ↥(cayleyGroup K) where
  carrier := {g | ∃ s : K, g = tL s}
  one_mem' := ⟨0, tL_zero'.symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, tL_mul s t⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨s, inv_eq_of_mul_eq_one_right (tL_mul_self' s)⟩

theorem longRoot_le_U0 : longRoot K ≤ U0 K := by
  rintro _ ⟨s, rfl⟩
  exact tL_mem_U0' s

theorem card_longRoot : Nat.card ↥(longRoot K) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective (fun s : K => (⟨tL s, s, rfl⟩ : ↥(longRoot K)))
    ⟨fun s t h => tL_injective (congrArg Subtype.val h), ?_⟩)).symm
  rintro ⟨_, s, rfl⟩
  exact ⟨s, rfl⟩

theorem longRoot_comm : ∀ a ∈ longRoot K, ∀ b ∈ longRoot K, a * b = b * a := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  rw [tL_mul, tL_mul, add_comm]

theorem longRoot_mul_self : ∀ e ∈ longRoot K, e * e = 1 := by
  rintro _ ⟨s, rfl⟩
  exact tL_mul_self' s

theorem mem_stabQ_two_of_comm_tL {s : K} (hs : s ≠ 0) {n : ↥(cayleyGroup K)}
    (hn : n * tL s = tL s * n) : n ∈ stabQ (stdF K 2) := by
  have key : ∀ m : ↥(cayleyGroup K), m * tL s = tL s * m →
      ∀ w ∈ stdF K 2, g2Act m w ∈ stdF K 2 := by
    intro m hm w hw
    obtain ⟨h1, h2, h3, h4⟩ := mem_stdF_two.mp hw
    set z : Ix3 → K := q6 0 0 (s⁻¹ * w (.inl 0)) (s⁻¹ * w (.inr 2)) 0 0 with hz
    have hwz : w = g2Act (tL s) z - z := by
      rw [g2Act_tL_sub', hz]
      conv_lhs => rw [q6_eta w]
      simp only [q6, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Matrix.cons_val_zero]
      rw [h1, h2, h3, h4, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hs, one_mul, one_mul]
    have e : g2Act m w = g2Act (tL s) (g2Act m z) - g2Act m z := by
      rw [hwz, map_sub, ← g2Act_mul_apply, hm, g2Act_mul_apply]
    rw [e]
    exact g2Act_tL_sub_mem s _
  have hn' : n⁻¹ * tL s = tL s * n⁻¹ := by
    calc n⁻¹ * tL s = n⁻¹ * (tL s * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * tL s) * n⁻¹ := by rw [hn]
      _ = tL s * n⁻¹ := by group
  refine mem_stabQ.mpr fun w => ⟨key n hn w, fun hw => ?_⟩
  have := key n⁻¹ hn' _ hw
  rwa [g2Act_inv_apply] at this

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
