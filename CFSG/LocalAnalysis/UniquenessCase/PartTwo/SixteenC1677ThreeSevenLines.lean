module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Kernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Helpers

variable {W : Type} [CommGroup W] [Finite W]

private theorem s168e3_seven_card_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card X = Nat.card (Multiplicative (Fin n → ZMod p)) := Nat.card_congr e.toEquiv
  rw [h1, show Nat.card (Multiplicative (Fin n → ZMod p)) = Nat.card (Fin n → ZMod p) from rfl,
    Nat.card_fun]
  simp [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]

private lemma s168e3_seven_stab_of_map_eq {U : Subgroup W} {φ : MulAut W}
    (h : U.map φ.toMonoidHom = U) : φ ∈ stabSub U := by
  intro u
  constructor
  · intro hu
    have hu' : φ u ∈ U.map φ.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := φ.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : φ u ∈ U.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [h] at hu'
    exact hu'

private lemma s168e3_seven_conj_mem_of_map_conj_eq {L : Subgroup (MulAut W)} {n : MulAut W}
    (h : L.map (MulAut.conj n).toMonoidHom = L) {l : MulAut W} (hl : l ∈ L) :
    n * l * n⁻¹ ∈ L := by
  have hm : (MulAut.conj n).toMonoidHom l ∈ L.map (MulAut.conj n).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hl
  rw [h] at hm
  simpa [MulAut.conj_apply] using hm

end Helpers

section General

variable {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)} {r : ℕ}
  {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}

theorem s168e3_seven_card_line (h : s16e_d3_Ctx A L r Δ σ) (i : Fin (r + 1)) :
    Nat.card ↥(L ⊓ centSub (Δ i)) = 7 ^ (r - 1) := by
  have hL : L ≤ stabSub (Δ i) :=
    (s16e_d3_le_ker h).trans (le_trans inf_le_right (iInf_le _ i))
  have hcm := card_autSub_mul hL
  rw [s16e_d3_card_autSub h i, s168e3_seven_card_of_elem h.elem] at hcm
  have hr : r = (r - 1) + 1 := by
    have := h.two_le
    omega
  rw [hr, pow_succ, mul_comm (7 ^ (r - 1)) 7] at hcm
  exact Nat.mul_left_cancel (by norm_num) hcm

theorem s168e3_seven_conj_line (h : s16e_d3_Ctx A L r Δ σ) (g : ↥A) {i : Fin (r + 1)}
    {l : MulAut W} (hl : l ∈ L ⊓ centSub (Δ i)) :
    (g : MulAut W) * l * (g : MulAut W)⁻¹ ∈ L ⊓ centSub (Δ (σ g i)) := by
  obtain ⟨hlL, hlC⟩ := Subgroup.mem_inf.mp hl
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact s168e3_seven_conj_mem_of_map_conj_eq (h.normal (g : MulAut W) g.2) hlL
  · intro x hx
    rw [← h.cfg.map_eq g i] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    simp [MulAut.mul_apply, MulAut.inv_apply_self, mem_centSub.mp hlC y hy]

theorem s168e3_seven_fix_of_sq (h : s16e_d3_Ctx A L r Δ σ) {s : ↥A} (hs : s ^ 2 = 1)
    {k : Fin (r + 1)} (hk : σ s k = k) : ∀ x ∈ Δ k, (s : MulAut W) x = x := by
  have hstab : (s : MulAut W) ∈ stabSub (Δ k) :=
    s168e3_seven_stab_of_map_eq (by rw [h.cfg.map_eq s k, hk])
  let N : Subgroup (MulAut W) := Subgroup.zpowers (s : MulAut W)
  have hN : N ≤ stabSub (Δ k) := Subgroup.zpowers_le.mpr hstab
  have hL : L ≤ stabSub (Δ k) :=
    (s16e_d3_le_ker h).trans (le_trans inf_le_right (iInf_le _ k))
  have hNL : ∀ n ∈ N, L.map (MulAut.conj n).toMonoidHom = L := by
    intro n hn
    exact h.normal n (Subgroup.zpowers_le.mpr s.2 hn)
  have hdvd21 := s16e_d3_card_autSub_dvd h.sq_eq_one (s16e_d3_card_block h k) hN hL hNL
    (s16e_d3_card_autSub h k)
  let ρ : MulAut ↥(Δ k) := resHom (Δ k) ⟨(s : MulAut W), hstab⟩
  have hρmem : ρ ∈ autSub N (Δ k) :=
    mem_autSub.mpr ⟨⟨(s : MulAut W), hstab⟩, Subgroup.mem_zpowers _, rfl⟩
  have hρ2 : ρ ^ 2 = 1 := by
    have hsval : (s : MulAut W) ^ 2 = 1 := by
      simpa using congrArg (fun t : ↥A => (t : MulAut W)) hs
    show resHom (Δ k) ⟨(s : MulAut W), hstab⟩ ^ 2 = 1
    rw [← map_pow,
      show (⟨(s : MulAut W), hstab⟩ : stabSub (Δ k)) ^ 2 = 1 from
        Subtype.ext (by simpa using hsval),
      map_one]
  have h21 : orderOf ρ ∣ 21 := by
    have h1 : orderOf (⟨ρ, hρmem⟩ : ↥(autSub N (Δ k))) ∣ Nat.card ↥(autSub N (Δ k)) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk ρ hρmem] at h1
    exact h1.trans hdvd21
  have h2 : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one hρ2
  have horder1 : orderOf ρ = 1 := by
    have hgcd : orderOf ρ ∣ Nat.gcd 21 2 := Nat.dvd_gcd h21 h2
    have hgcd21 : Nat.gcd 21 2 = 1 := by norm_num
    rw [hgcd21] at hgcd
    exact Nat.dvd_one.mp hgcd
  have hρ1 : ρ = 1 := orderOf_eq_one_iff.mp horder1
  intro x hx
  have hcon := congrArg (fun φ : MulAut ↥(Δ k) => ((φ ⟨x, hx⟩ : ↥(Δ k)) : W)) hρ1
  simp only [MulAut.one_apply] at hcon
  rw [resHom_apply] at hcon
  simpa using hcon

end General

section Two

variable {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
  {Δ : Fin (2 + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (2 + 1))}

private lemma s168e3_seven_third {i j : Fin (2 + 1)} (hij : i ≠ j) :
    ∃ k : Fin (2 + 1), k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

private lemma s168e3_seven_fin_three {i j k k' : Fin (2 + 1)} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (hkk' : k' ≠ k) : k' = i ∨ k' = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases k' <;> simp_all

theorem s168e3_seven_line_inf (h : s16e_d3_Ctx A L 2 Δ σ) {i j : Fin (2 + 1)} (hij : i ≠ j)
    {l : MulAut W} (hli : l ∈ L ⊓ centSub (Δ i)) (hlj : l ∈ centSub (Δ j)) : l = 1 := by
  obtain ⟨hlL, hlC⟩ := Subgroup.mem_inf.mp hli
  obtain ⟨k, hki, hkj⟩ := s168e3_seven_third hij
  refine s16e_d3_eq_one_of_supp_single h k hlL ?_
  intro k' hk' x hx
  rcases s168e3_seven_fin_three hij hki hkj hk' with rfl | rfl
  · exact (mem_centSub.mp hlC) x hx
  · exact (mem_centSub.mp hlj) x hx

theorem s168e3_seven_exists_sq (h : s16e_d3_Ctx A L 2 Δ σ) (i j : Fin (2 + 1)) :
    ∃ s : ↥A, s ^ 2 = 1 ∧ σ s = Equiv.swap i j := by
  by_cases hij : i = j
  · have hswap : Equiv.swap i j = 1 := by rw [hij, Equiv.swap_self]; rfl
    exact ⟨1, by simp, by simp [map_one, hswap]⟩
  · obtain ⟨g, hg⟩ := h.cfg.surj (Equiv.swap i j)
    have hcard : 7 ^ (2 + 1) * 3 * Nat.factorial (2 + 1) = 6174 := by
      norm_num [Nat.factorial]
    have hdvd : Nat.card ↥A ∣ 6174 := by
      rw [← hcard]
      exact s16e_d3_card_dvd_seven_pow_mul_three_mul_factorial h
    have hg6174 : g ^ 6174 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard g).trans hdvd)
    have hswap2 : Equiv.swap i j ^ 2 = 1 := by
      rw [pow_two, Equiv.swap_mul_self]
    have hswap3087 : Equiv.swap i j ^ 3087 = Equiv.swap i j := by
      have h : (3087 : ℕ) = 2 * 1543 + 1 := by norm_num
      rw [h, pow_add, pow_one, pow_mul, hswap2, one_pow, one_mul]
    have hs2 : (g ^ 3087) ^ 2 = 1 := by
      rw [← pow_mul, show 3087 * 2 = 6174 from by norm_num, hg6174]
    refine ⟨g ^ 3087, hs2, ?_⟩
    rw [map_pow, hg, hswap3087]

end Two

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
