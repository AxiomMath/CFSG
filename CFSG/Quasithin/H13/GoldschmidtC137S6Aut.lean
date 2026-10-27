module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin1
import CFSG.Quasithin.H13.GoldschmidtC137S6Fin2
import CFSG.Quasithin.H13.GoldschmidtC137S6Fin3
import CFSG.LargeExtraspecial.AS35YFSymAut

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin.B3

theorem eq_H1_or_eq_H2_of_lt {Q : Subgroup (Equiv.Perm (Fin 6))} (hTQ : T6 < Q) (hQ : Q < ⊤) :
    Q = H1 ∨ Q = H2 := by
  rcases overgroups hTQ.le with h | h | h | h
  · exact absurd h hTQ.ne'
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hQ.ne

theorem H1_ne_H2 : H1 ≠ H2 := by
  intro h
  have hT : H1 = T6 := by
    have h' := H1_inf_H2
    rw [← h, inf_idem] at h'
    exact h'
  have hc : Nat.card H1 = Nat.card T6 := by rw [hT]
  rw [card_H1, card_T6] at hc
  exact absurd hc (by norm_num)

theorem map_H1_eq_or_of_map_T6_eq (α : MulAut (Equiv.Perm (Fin 6)))
    (hα : T6.map α.toMonoidHom = T6) : H1.map α.toMonoidHom = H1 ∨ H1.map α.toMonoidHom = H2 := by
  have hT6H1 : T6 < H1 := by
    refine lt_of_le_of_ne T6_le_H1 ?_
    intro h
    have hc : Nat.card T6 = Nat.card H1 := by rw [h]
    rw [card_T6, card_H1] at hc
    exact absurd hc (by norm_num)
  have hH1top : H1 < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro h
    have hc : Nat.card H1 = 720 := by
      rw [h, Subgroup.card_top, Nat.card_perm, Nat.card_fin]
      norm_num
    rw [card_H1] at hc
    norm_num at hc
  have h1 : T6 < H1.map α.toMonoidHom := by
    have h := hT6H1
    rw [← Subgroup.map_lt_map_iff_of_injective (f := α.toMonoidHom) α.injective] at h
    rwa [hα] at h
  have h2 : H1.map α.toMonoidHom < ⊤ := by
    have htop : (⊤ : Subgroup (Gp 6)).map α.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective α.toMonoidHom α.surjective
    have h := hH1top
    rw [← Subgroup.map_lt_map_iff_of_injective (f := α.toMonoidHom) α.injective] at h
    rwa [htop] at h
  exact eq_H1_or_eq_H2_of_lt h1 h2

theorem swap_mem_H1 : Equiv.swap (4 : Fin 6) 5 ∈ H1 :=
  T6_le_H1 (R1_le_T6 swap45_mem_R1)

private theorem mulT_tauL_comm_H1l :
    ∀ t ∈ H1l, mulT tauL t = mulT t tauL := by
  decide +kernel

theorem swap_mul_eq_mul_swap_of_mem_H1 {h : Equiv.Perm (Fin 6)} (hh : h ∈ H1) :
    Equiv.swap (4 : Fin 6) 5 * h = h * Equiv.swap (4 : Fin 6) 5 := by
  apply tab_injective
  rw [tab_mul, tab_mul, tab_swap45]
  exact mulT_tauL_comm_H1l (tab h) (mem_H1.1 hh)

private theorem H1l_central :
    ∀ t ∈ H1l, (∀ u ∈ H1l, mulT t u = mulT u t) → t = idT 6 ∨ t = tauL := by
  decide +kernel

theorem eq_one_or_eq_swap_of_mem_H1 {z : Equiv.Perm (Fin 6)} (hz : z ∈ H1)
    (hc : ∀ h ∈ H1, z * h = h * z) : z = 1 ∨ z = Equiv.swap (4 : Fin 6) 5 := by
  have hcomm : ∀ u ∈ H1l, mulT (tab z) u = mulT u (tab z) := by
    intro u hu
    obtain ⟨σ, rfl⟩ := exists_tab_eq ((subOK_spec subOK_lists.2.1).1 u hu)
    have hσ : σ ∈ H1 := (mem_H1).2 hu
    have h := congrArg tab (hc σ hσ)
    rwa [tab_mul, tab_mul] at h
  rcases H1l_central (tab z) (mem_H1.1 hz) hcomm with h | h
  · left
    apply tab_injective
    rw [h, tab_one]
  · right
    apply tab_injective
    rw [h, tab_swap45]

theorem exists_conj_of_map_H1_eq (α : MulAut (Equiv.Perm (Fin 6)))
    (hα : H1.map α.toMonoidHom = H1) :
    ∃ π : Equiv.Perm (Fin 6), ∀ σ, α σ = π * σ * π⁻¹ := by
  have hαH1 : ∀ h : Equiv.Perm (Fin 6), h ∈ H1 → α h ∈ H1 := by
    intro h hh
    rw [← hα]
    exact ⟨h, hh, rfl⟩
  have hcent : ∀ h ∈ H1,
      α.toMonoidHom (Equiv.swap (4 : Fin 6) 5) * h =
        h * α.toMonoidHom (Equiv.swap (4 : Fin 6) 5) := by
    intro h hh
    have hh' : h ∈ H1.map α.toMonoidHom := by rw [hα]; exact hh
    obtain ⟨h', hh'H1, rfl⟩ := Subgroup.mem_map.1 hh'
    rw [← map_mul, ← map_mul, swap_mul_eq_mul_swap_of_mem_H1 hh'H1]
  have hz_ne : Equiv.swap (4 : Fin 6) 5 ≠ 1 := by
    intro h
    have h4 : (Equiv.swap (4 : Fin 6) 5) 4 = (1 : Equiv.Perm (Fin 6)) 4 :=
      congrArg (fun e : Equiv.Perm (Fin 6) => e 4) h
    rw [Equiv.swap_apply_left] at h4
    simp at h4
  have hαz : α (Equiv.swap (4 : Fin 6) 5) = Equiv.swap (4 : Fin 6) 5 := by
    have hzH1 : α (Equiv.swap (4 : Fin 6) 5) ∈ H1 := hαH1 _ swap_mem_H1
    rcases eq_one_or_eq_swap_of_mem_H1 hzH1 hcent with h1 | h1
    · exfalso
      apply hz_ne
      apply α.injective
      rw [h1, map_one]
    · exact h1
  have hpres : ∀ σ : Equiv.Perm (Fin 6), σ.IsSwap → (α σ).IsSwap := by
    intro σ hσ
    obtain ⟨i, j, hij, rfl⟩ := hσ
    have hconj : IsConj (Equiv.swap (4 : Fin 6) 5) (Equiv.swap i j) :=
      Equiv.Perm.isConj_swap (by decide : (4 : Fin 6) ≠ 5) hij
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    refine ⟨α c 4, α c 5, ?_, ?_⟩
    · exact (α c).injective.ne (by decide : (4 : Fin 6) ≠ 5)
    · rw [Equiv.swap_apply_apply, ← hαz, ← map_mul, ← map_inv, ← map_mul, hc]
  exact CFSG.LargeExtraspecial.AS35YF.perm_aut_eq_conj_of_isSwap α hpres (by norm_num)

theorem exists_conj_of_map_T6_eq (α : MulAut (Equiv.Perm (Fin 6)))
    (hα : T6.map α.toMonoidHom = T6) {Q : Subgroup (Equiv.Perm (Fin 6))} (hTQ : T6 < Q)
    (hQ : Q < ⊤) (hαQ : Q.map α.toMonoidHom = Q) :
    ∃ π : Equiv.Perm (Fin 6), ∀ σ, α σ = π * σ * π⁻¹ := by
  rcases eq_H1_or_eq_H2_of_lt hTQ hQ with rfl | rfl
  · exact exists_conj_of_map_H1_eq α hαQ
  · rcases map_H1_eq_or_of_map_T6_eq α hα with h1 | h1
    · exact exists_conj_of_map_H1_eq α h1
    · exfalso
      have h2 : H1.map α.toMonoidHom = H2.map α.toMonoidHom := by rw [h1, hαQ]
      exact H1_ne_H2 (Subgroup.map_injective (f := α.toMonoidHom) α.injective h2)

end CFSG.Quasithin.H13.U3.GC137
