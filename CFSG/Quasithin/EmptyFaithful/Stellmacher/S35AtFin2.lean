module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.At

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem mp_zpowers_vp' (g : Perm (Fin 5)) (p : Fin 5) :
    mp g (Subgroup.zpowers (vp p)) = Subgroup.zpowers (vp (g p)) := by
  rw [mp, MonoidHom.map_zpowers]
  congr 1
  exact act_vp g p

theorem swap_mem_std : swap (0 : Fin 5) 2 ∈ S5Syl ∧ swap (1 : Fin 5) 3 ∈ S5Syl := by
  rw [mem_S5Syl_iff, mem_S5Syl_iff]; decide +kernel

theorem act_ep_swap (g : Perm (Fin 5)) {a b : Fin 5} (hab : a ≠ b) (hs : swap a b ∈ S5Syl) :
    ∃ x y : Fin 5, x ≠ y ∧ orth.act g (ep a b) = ep x y ∧ swap x y ∈ cj g S5Syl := by
  refine ⟨g a, g b, g.injective.ne hab, act_ep g a b, ?_⟩
  rw [swap_apply_apply]
  exact mem_cj_conj.mpr hs

theorem exists_ep_of_mem_commW {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {w : orth.W} (hw : w ∈ commW orth (Subgroup.zpowers (zc D)) ⊤)
    (hv : w ∉ Subgroup.zpowers (vp (fixPt D))) :
    ∃ x y : Fin 5, x ≠ y ∧ w = ep x y ∧ swap x y ∈ D := by
  obtain ⟨g, rfl, -, hz, hf⟩ := std_data hD
  rw [hz, ← cj_zpowers, commW_cj_top, mem_mp, mem_commW_zStd] at hw
  rw [hf, ← mp_zpowers_vp', mem_mp] at hv
  have hw' : w = orth.act g (orth.act g⁻¹ w) := (act_act_inv orth g w).symm
  rcases hw with h | h | h | h
  · exact absurd (h ▸ one_mem _) hv
  · obtain ⟨x, y, hxy, he, hs⟩ := act_ep_swap g (a := 0) (b := 2) (by decide) swap_mem_std.1
    exact ⟨x, y, hxy, by rw [hw', h, he], hs⟩
  · obtain ⟨x, y, hxy, he, hs⟩ := act_ep_swap g (a := 1) (b := 3) (by decide) swap_mem_std.2
    exact ⟨x, y, hxy, by rw [hw', h, he], hs⟩
  · exact absurd (h ▸ Subgroup.mem_zpowers _) hv

theorem exists_sylow_ge {A : Subgroup (Perm (Fin 5))} (hA : IsPGroup 2 A) :
    ∃ D : Subgroup (Perm (Fin 5)), Nat.card D = 8 ∧ A ≤ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hA.exists_le_sylow
  refine ⟨P, ?_, hP⟩
  have hG : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  rw [Sylow.card_eq_multiplicity, hG]
  have : (120 : ℕ).factorization 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two]; decide +kernel
  rw [this]; norm_num

end CFSG.Quasithin.F53.Stellmacher.S35.At
