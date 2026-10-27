module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13.K1262Two

open Subgroup

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem isSimpleGroup_alt6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

private def rA : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def sA : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private theorem rA_mul_sA_ne : rA * sA ≠ sA * rA := by
  intro h
  have h1 : (rA : Equiv.Perm (Fin 6)) * (sA : Equiv.Perm (Fin 6)) =
      (sA : Equiv.Perm (Fin 6)) * (rA : Equiv.Perm (Fin 6)) := congrArg Subtype.val h
  have h2 := congrArg (fun g : Equiv.Perm (Fin 6) => g 0) h1
  exact absurd h2 (by decide)

theorem exists_noncomm_alt6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a :=
  ⟨rA, sA, rA_mul_sA_ne⟩

theorem not_isPGroup_top_alt6 : ¬ IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 6))) := by
  intro h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h
  rw [Subgroup.card_top, card_alt6] at hn
  have h3 : 3 ∣ 2 ^ n := ⟨120, by omega⟩
  have h2 := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at h2

theorem eq_bot_of_normal_isPGroup_alt6 (N : Subgroup (alternatingGroup (Fin 6))) [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  haveI := isSimpleGroup_alt6
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · subst h
    exact (not_isPGroup_top_alt6 hN).elim

theorem eq_bot_of_normal_comm_alt6 (N : Subgroup (alternatingGroup (Fin 6))) [N.Normal]
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : N = ⊥ := by
  haveI := isSimpleGroup_alt6
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · subst h
    obtain ⟨a, b, hab⟩ := exists_noncomm_alt6
    exact (hab (hN a (Subgroup.mem_top a) b (Subgroup.mem_top b))).elim

private def dihT : Finset (alternatingGroup (Fin 6)) :=
  {1, rA, rA ^ 2, rA ^ 3, sA, sA * rA, sA * rA ^ 2, sA * rA ^ 3}

private theorem dihT_mul : ∀ x ∈ dihT, ∀ y ∈ dihT, x * y ∈ dihT := by decide +kernel

private theorem dihT_inv : ∀ x ∈ dihT, x⁻¹ ∈ dihT := by decide +kernel

private theorem dihT_one : (1 : alternatingGroup (Fin 6)) ∈ dihT := by decide

private def dihR : Subgroup (alternatingGroup (Fin 6)) where
  carrier := ↑dihT
  mul_mem' := fun {x y} hx hy => dihT_mul x hx y hy
  one_mem' := dihT_one
  inv_mem' := fun {x} hx => dihT_inv x hx

private theorem card_dihR : Nat.card dihR = 8 := by
  have h : Nat.card dihR = Nat.card dihT :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  rw [h, Nat.card_eq_finsetCard]
  decide

private theorem rA_mem : rA ∈ dihR := by
  show rA ∈ dihT
  decide

private theorem sA_mem : sA ∈ dihR := by
  show sA ∈ dihT
  decide

private theorem dihR_not_comm : ∃ x ∈ dihR, ∃ y ∈ dihR, x * y ≠ y * x :=
  ⟨rA, rA_mem, sA, sA_mem, rA_mul_sA_ne⟩

theorem false_of_two_subgroups_comm_alt6 {H : Type} [Group H] [Finite H]
    (φ : H →* alternatingGroup (Fin 6)) (hφ : Function.Surjective φ)
    (hcomm : ∀ P : Subgroup H, IsPGroup 2 P → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : False := by
  set M : Subgroup H := dihR.comap φ with hM
  set N : Subgroup H := φ.ker with hN
  have hMN : Nat.card M = 8 * Nat.card N := by
    have h1 : Nat.card M * M.index = Nat.card H := Subgroup.card_mul_index M
    have h2 : Nat.card N * N.index = Nat.card H := Subgroup.card_mul_index N
    have h3 : M.index = dihR.index := Subgroup.index_comap_of_surjective (H := dihR) hφ
    have h4 : Nat.card dihR * dihR.index = Nat.card (alternatingGroup (Fin 6)) :=
      Subgroup.card_mul_index dihR
    have h5 : N.index = 360 := by
      rw [hN, Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ, Subgroup.card_top, card_alt6]
    rw [card_dihR, card_alt6] at h4
    have h6 : dihR.index = 45 := by omega
    rw [h3, h6] at h1
    rw [h5] at h2
    omega
  have hMpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
  obtain ⟨P⟩ : Nonempty (Sylow 2 M) := Sylow.nonempty
  have hPcard : Nat.card (P : Subgroup M) = 2 ^ (Nat.card M).factorization 2 :=
    Sylow.card_eq_multiplicity P
  have hiM : Function.Injective M.subtype := Subtype.val_injective
  set P' : Subgroup H := (P : Subgroup M).map M.subtype with hP'
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map M.subtype
  have hP'M : P' ≤ M := Subgroup.map_subtype_le _
  have hP'card : Nat.card P' = 2 ^ (Nat.card M).factorization 2 := by
    rw [hP', Subgroup.card_map_of_injective hiM]
    exact hPcard
  set f : P' →* alternatingGroup (Fin 6) := φ.comp P'.subtype with hf
  have hiP' : Function.Injective P'.subtype := Subtype.val_injective
  have hfK : Nat.card f.ker * Nat.card f.range = 2 ^ (Nat.card M).factorization 2 := by
    rw [← hP'card]
    exact Subgroup.card_ker_mul_card_range f
  have hKN : Nat.card f.ker ∣ Nat.card N := by
    have e : Nat.card (f.ker.map P'.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective hiP'
    rw [← e]
    apply Subgroup.card_dvd_of_le
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hy' : φ (y : H) = 1 := MonoidHom.mem_ker.1 hy
    exact MonoidHom.mem_ker.2 hy'
  obtain ⟨j, hjv, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (⟨_, hfK.symm⟩ :
    Nat.card f.ker ∣ 2 ^ (Nat.card M).factorization 2)
  have hjN : 2 ^ j ∣ Nat.card N := by
    rw [← hj]
    exact hKN
  have hj3 : 2 ^ (j + 3) ∣ Nat.card M := by
    have e : 2 ^ (j + 3) = 8 * 2 ^ j := by ring
    rw [e, hMN]
    exact mul_dvd_mul_left 8 hjN
  have hjv' : j + 3 ≤ (Nat.card M).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hMpos).1 hj3
  have h8 : 8 ∣ Nat.card f.range := by
    have h1 : 2 ^ j * Nat.card f.range = 2 ^ (Nat.card M).factorization 2 := by
      rw [← hj]
      exact hfK
    have h2 : 2 ^ (j + 3) ∣ 2 ^ (Nat.card M).factorization 2 := pow_dvd_pow 2 hjv'
    rw [← h1, pow_add] at h2
    have h3 : 2 ^ 3 ∣ Nat.card f.range :=
      (mul_dvd_mul_iff_left (pow_ne_zero j two_ne_zero)).1 h2
    exact h3
  have hQle : f.range ≤ dihR := by
    intro x hx
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hx
    exact Subgroup.mem_comap.1 (hP'M g.2)
  have hQcomm : ∀ x ∈ f.range, ∀ y ∈ f.range, x * y = y * x := by
    intro x hx y hy
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hx
    obtain ⟨g', rfl⟩ := MonoidHom.mem_range.1 hy
    have hc : (g : H) * (g' : H) = (g' : H) * (g : H) :=
      hcomm P' hP'2 (g : H) g.2 (g' : H) g'.2
    show φ (g : H) * φ (g' : H) = φ (g' : H) * φ (g : H)
    rw [← map_mul, ← map_mul, hc]
  have hQ8 : Nat.card f.range = 8 := by
    have hle : Nat.card f.range ≤ 8 := by
      have := Subgroup.card_le_of_le hQle
      rwa [card_dihR] at this
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    obtain ⟨k, hk⟩ := h8
    omega
  have hQeq : f.range = dihR :=
    Subgroup.eq_of_le_of_card_ge hQle (le_of_eq (by rw [card_dihR, hQ8]))
  obtain ⟨x, hx, y, hy, hxy⟩ := dihR_not_comm
  apply hxy
  rw [← hQeq] at hx hy
  exact hQcomm x hx y hy

theorem false_of_sylow_comm_alt6 {X : Type} [Group X] [Finite X]
    (hS : ∀ S : Sylow 2 X, ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x)
    (Y : Subgroup X) (φ : ↥Y →* alternatingGroup (Fin 6)) (hφ : Function.Surjective φ) : False := by
  refine false_of_two_subgroups_comm_alt6 φ hφ ?_
  intro P hP x hx y hy
  obtain ⟨S, hPS⟩ := IsPGroup.exists_le_sylow (hP.map Y.subtype)
  have hx' : (x : X) ∈ (S : Subgroup X) := hPS (Subgroup.mem_map_of_mem Y.subtype hx)
  have hy' : (y : X) ∈ (S : Subgroup X) := hPS (Subgroup.mem_map_of_mem Y.subtype hy)
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact hS S x hx' y hy'

end CFSG.Quasithin.H13.K1262Two
