module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Klein
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Chart
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Dich
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E8

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem pow_eight_of_pow_two_pow (g : Perm (Fin 5)) (e : ℕ) (h : g ^ 2 ^ e = 1) :
    g ^ 8 = 1 := by
  have h1 : orderOf g ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf g ∣ 120 := by
    have := orderOf_dvd_card (G := Perm (Fin 5)) (x := g)
    rwa [Fintype.card_perm, Fintype.card_fin, show Nat.factorial 5 = 120 by decide] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hk3 : k ≤ 3 := by
    by_contra hcon
    have h4 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    rw [hk] at h2
    have := h4.trans h2
    omega
  rw [← orderOf_dvd_iff_pow_eq_one, hk]
  exact (pow_dvd_pow 2 hk3).trans (by norm_num)

theorem claim8a (hS : Sit H M S)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ)) :
    Claim8a H M := by
  intro β α' hp ht
  obtain ⟨v, hvV, hvs, hidx⟩ := ht
  have hβ := hp.vδ
  have hα' := hp.vδ'
  obtain ⟨c0⟩ := Ch.nonempty_chart (Std.Zv_le_Vn_S5 hS hα') (hZ α' hα')
  have hsw : (c0.θ ⟨v, hvs⟩).IsSwap := by
    rw [← S35.Fin.idx_orth_eq_two_iff, ← c0.secIdx_eq_idx hvs]
    exact hidx
  obtain ⟨σ, hσ⟩ := exists_conj_swap hsw
  set c := twist c0 σ with hc
  have htv : th c v = swap 0 1 := by
    rw [th_of_mem c hvs]
    exact hσ
  have hVs : Vn β ≤ stab α' := (Std.PD_Vn_le_stab hS hp).1
  have hVY : Vn β ≤ Wb β ⊓ stab α' := le_inf (Std.Vn_le_Wb_self hS hβ) hVs
  have hYs : Wb β ⊓ stab α' ≤ stab α' := inf_le_right
  have hcomm : ∀ y ∈ Wb β ⊓ stab α', ∀ w ∈ Vn β, y * w = w * y := by
    intro y hy w hw
    have h1 : ⁅w, y⁆ ∈ (⊥ : Subgroup G) :=
      Std.comm_Vn_Wb hS β ▸ Subgroup.commutator_mem_commutator hw hy.1
    exact ((commutatorElement_eq_one_iff_mul_comm).mp (Subgroup.mem_bot.mp h1)).symm
  have h8 : ∀ y ∈ Wb β ⊓ stab α', th c y ^ 8 = 1 := by
    intro y hy
    obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 (stab β)) ⟨y, Std.Wb_le_Qv hS β hy.1⟩
    have hye : y ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    refine pow_eight_of_pow_two_pow _ e ?_
    rw [th_of_mem c hy.2, ← map_pow]
    have : (⟨y, hy.2⟩ : ↥(stab α')) ^ 2 ^ e = 1 := Subtype.ext (by simpa using hye)
    rw [this, map_one]
  have key : Goal α' (Wb β ⊓ stab α') (Vn β) := by
    rcases dichotomy c hVY hYs hcomm h8 hvV htv with h | ⟨s, hs, hVb, hYb⟩
    · exact goal_of_image hS hα' c hYs hVs h
    · exact goal_of_klein hS hα' c hYs hVs hvV htv hs hVb hYb
  obtain ⟨A, B, hA, hB, hAB, h1, h2, h3⟩ := key
  exact ⟨A, B, hA, hB, hAB, h1, h2, fun l hl hlQ => h3 _ (Std.Zv_le_Vn hl) hlQ⟩

end S35.E8

end F53.Stellmacher

end CFSG.Quasithin
