module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsPerm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

private theorem s16t_a_card_elemAbelianOfRank {X : Type} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem s16t_a_rank_comm_pow {p n : ℕ} {P : Type} [Group P]
    (h : IsElemAbelianOfRank p n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

private theorem s16t_a_fix_iff {T : Type} [CommGroup T] {ι : Type} {Y : ι → Subgroup T}
    (hinj : Function.Injective Y) {Λ : Subgroup (MulAut T)} {ρ : ↥Λ →* Equiv.Perm ι}
    (hρ : ∀ (g : ↥Λ) (i : ι), (Y i).map (g : MulAut T).toMonoidHom = Y (ρ g i))
    (g : ↥Λ) (i : ι) :
    (Y i).map (g : MulAut T).toMonoidHom = Y i ↔ ρ g i = i := by
  constructor
  · intro h
    exact hinj ((hρ g i).symm.trans h)
  · intro h
    rw [hρ g i, h]

theorem s16t_a_card_stab_all {T : Type} [CommGroup T] {ι : Type} [Fintype ι]
    (hι : Fintype.card ι = 3) {Y : ι → Subgroup T} (hinj : Function.Injective Y)
    {Λ Λ₀ : Subgroup (MulAut T)} (hΛ : IsElemAbelianOfRank 3 2 ↥Λ)
    (hΛperm : ∀ f ∈ Λ, ∀ i, ∃ j, (Y i).map f.toMonoidHom = Y j)
    (hmove : ∃ f ∈ Λ, ∃ i, (Y i).map f.toMonoidHom ≠ Y i)
    (hΛ₀ : ∀ f, f ∈ Λ₀ ↔ f ∈ Λ ∧ ∀ i, (Y i).map f.toMonoidHom = Y i) :
    Nat.card Λ₀ = 3 ∧ ∀ f ∈ Λ, f ∉ Λ₀ → ∀ i, (Y i).map f.toMonoidHom ≠ Y i := by
  classical
  obtain ⟨ρ, hρ⟩ := s16t_a_exists_perm_hom hinj hΛperm
  have hcardΛ : Nat.card ↥Λ = 9 := by
    rw [s16t_a_card_elemAbelianOfRank hΛ]
    norm_num
  have hpow : ∀ a : ↥Λ, a ^ 3 = 1 := (s16t_a_rank_comm_pow hΛ).2
  have hΛ₀ker : Λ₀ = ρ.ker.map Λ.subtype := by
    ext f
    rw [hΛ₀, Subgroup.mem_map]
    constructor
    · rintro ⟨hfΛ, hfix⟩
      refine ⟨⟨f, hfΛ⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      ext i
      simpa using (s16t_a_fix_iff hinj hρ ⟨f, hfΛ⟩ i).1 (hfix i)
    · rintro ⟨x, hx, hxf⟩
      rw [← hxf]
      refine ⟨x.2, fun i => ?_⟩
      have hx1 : ρ x = 1 := MonoidHom.mem_ker.1 hx
      exact (s16t_a_fix_iff hinj hρ x i).2 (by rw [hx1]; rfl)
  have hcardΛ₀ : Nat.card Λ₀ = Nat.card ρ.ker := by
    rw [hΛ₀ker]
    exact Subgroup.card_map_of_injective (K := ρ.ker) (f := Λ.subtype) Λ.subtype_injective
  have hpermcard : Nat.card (Equiv.Perm ι) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hι]
    norm_num
  have hrange9 : Nat.card ρ.range ∣ 9 := by
    have h := Subgroup.card_range_dvd ρ
    rwa [hcardΛ] at h
  have hrange6 : Nat.card ρ.range ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card ρ.range
    rwa [hpermcard] at h
  have hrange3 : Nat.card ρ.range ∣ 3 := by
    have h := Nat.dvd_gcd hrange9 hrange6
    have hg : Nat.gcd 9 6 = 3 := by norm_num
    rwa [hg] at h
  have hrange_gt1 : 1 < Nat.card ρ.range := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    obtain ⟨f, hfΛ, i, hfi⟩ := hmove
    have hmem : ρ ⟨f, hfΛ⟩ ∈ ρ.range := ⟨⟨f, hfΛ⟩, rfl⟩
    rw [hbot] at hmem
    have hone : ρ ⟨f, hfΛ⟩ = 1 := Subgroup.mem_bot.1 hmem
    exact hfi ((s16t_a_fix_iff hinj hρ ⟨f, hfΛ⟩ i).2 (by rw [hone]; rfl))
  have hrange_eq : Nat.card ρ.range = 3 := by
    rcases (show Nat.Prime 3 by norm_num).eq_one_or_self_of_dvd (Nat.card ρ.range)
      hrange3 with h | h
    · omega
    · exact h
  have hker3 : Nat.card ρ.ker = 3 := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hrange_eq, hcardΛ] at h
    omega
  have hcardΛ₀eq : Nat.card Λ₀ = 3 := by
    rw [hcardΛ₀, hker3]
  refine ⟨hcardΛ₀eq, fun f hfΛ hfΛ₀ i hfix => ?_⟩
  let g : ↥Λ := ⟨f, hfΛ⟩
  have hg_ne : ρ g ≠ 1 := by
    intro h1
    apply hfΛ₀
    rw [hΛ₀]
    exact ⟨hfΛ, fun j => (s16t_a_fix_iff hinj hρ g j).2 (by rw [h1]; rfl)⟩
  have hpow3 : (ρ g) ^ 3 = 1 := by
    rw [← map_pow, hpow g, map_one]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hmod : (ρ g).supportᶜ.card ≡ 3 [MOD 3] := by
    have h := Equiv.Perm.card_compl_support_modEq (σ := ρ g) (p := 3) (n := 1)
      (by simpa using hpow3)
    rwa [hι] at h
  have hsupp_dvd : 3 ∣ (ρ g).supportᶜ.card := by
    have hzero : (ρ g).supportᶜ.card ≡ 0 [MOD 3] :=
      hmod.trans (Nat.modEq_zero_iff_dvd.2 (dvd_refl 3))
    exact Nat.modEq_zero_iff_dvd.1 hzero
  have hsupp_le : (ρ g).supportᶜ.card ≤ 3 := by
    calc (ρ g).supportᶜ.card ≤ Fintype.card ι := Finset.card_le_univ _
      _ = 3 := hι
  have hsupp_zero : (ρ g).supportᶜ.card = 0 := by
    by_contra hc0
    have hle : 3 ≤ (ρ g).supportᶜ.card := by
      obtain ⟨k, hk⟩ := hsupp_dvd
      omega
    have hc3 : (ρ g).supportᶜ.card = 3 := by omega
    have huniv : (ρ g).supportᶜ = Finset.univ :=
      Finset.eq_univ_of_card _ (hc3.trans hι.symm)
    have hσone : ρ g = 1 := by
      apply Equiv.ext
      intro j
      have hj : j ∈ (ρ g).supportᶜ := by
        rw [huniv]
        exact Finset.mem_univ j
      have hnj : j ∉ (ρ g).support := Finset.mem_compl.1 hj
      simpa using Equiv.Perm.notMem_support.1 hnj
    exact hg_ne hσone
  have hfixi : ρ g i = i := (s16t_a_fix_iff hinj hρ g i).1 hfix
  have hmem : i ∈ (ρ g).supportᶜ := by
    rw [Finset.mem_compl, Equiv.Perm.notMem_support]
    exact hfixi
  have hpos : 0 < (ρ g).supportᶜ.card := Finset.card_pos.2 ⟨i, hmem⟩
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
