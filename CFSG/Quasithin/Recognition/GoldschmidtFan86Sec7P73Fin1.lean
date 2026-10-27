module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Coord

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace P73

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem add_self_vec : ∀ a : Fin 5 → ZMod 2, a + a = 0 := by decide

theorem add_eq_zero_vec : ∀ a b : Fin 5 → ZMod 2, a + b = 0 → b = a := by decide

theorem comm_vec : ∀ a b : Fin 5 → ZMod 2, a + b + a + b = 0 := by decide

theorem sig_inv (F : FanTree Γ G) {g : G} (hg : g ∈ nbrStab Γ G α) : sig D g⁻¹ = sig D g := by
  have h := sig_mul D F hg (inv_mem hg)
  rw [mul_inv_cancel, sig_one] at h
  exact add_eq_zero_vec _ _ h.symm

include D in
theorem sq_mem (F : FanTree Γ G) (h71c : Fan71c F L) {g : G} (hg : g ∈ nbrStab Γ G α) :
    g * g ∈ ballStab Γ G 2 α :=
  (sig_eq_zero_iff D F h71c (mul_mem hg hg)).1 (by rw [sig_mul D F hg hg]; exact add_self_vec _)

include D in
theorem comm_mem (F : FanTree Γ G) (h71c : Fan71c F L) {g h : G} (hg : g ∈ nbrStab Γ G α)
    (hh : h ∈ nbrStab Γ G α) : g * h * g⁻¹ * h⁻¹ ∈ ballStab Γ G 2 α := by
  have h1 : g * h ∈ nbrStab Γ G α := mul_mem hg hh
  have h2 : g * h * g⁻¹ ∈ nbrStab Γ G α := mul_mem h1 (inv_mem hg)
  refine (sig_eq_zero_iff D F h71c (mul_mem h2 (inv_mem hh))).1 ?_
  rw [sig_mul D F h2 (inv_mem hh), sig_mul D F h1 (inv_mem hg), sig_mul D F hg hh,
    sig_inv D F hg, sig_inv D F hh]
  exact comm_vec _ _

theorem minimal_of (hW : ∀ w, SigSet D w ↔ Wev w) (F : FanTree Γ G) (h71c : Fan71c F L)
    {N : Subgroup G} (hBN : ballStab Γ G 2 α ≤ N) (hNA : N ≤ nbrStab Γ G α)
    (hinv : ∀ g ∈ MulAction.stabilizer G α, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    N = ballStab Γ G 2 α ∨ N = nbrStab Γ G α := by
  by_cases hz : ∀ n ∈ N, sig D n = 0
  · exact Or.inl (le_antisymm (fun n hn => (sig_eq_zero_iff D F h71c (hNA hn)).1 (hz n hn)) hBN)
  · right
    push Not at hz
    obtain ⟨n0, hn0, hne0⟩ := hz
    let Q : (Fin 5 → ZMod 2) → Prop := fun v => ∃ n ∈ N, sig D n = v
    have hQ0 : Q 0 := ⟨1, N.one_mem, sig_one D⟩
    have hQadd : ∀ a b, Q a → Q b → Q (a + b) := by
      rintro a b ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
      exact ⟨n * m, N.mul_mem hn hm, sig_mul D F (hNA hn) (hNA hm)⟩
    have hQsh : ∀ a, Q a → Q (sh a) := by
      rintro a ⟨n, hn, rfl⟩
      have hx : D.x⁻¹ ∈ MulAction.stabilizer G α := inv_mem (D.x_mem_stabilizer F h71c)
      have := hinv _ hx n hn
      rw [inv_inv] at this
      exact ⟨_, this, sig_conj D F h71c n⟩
    have hv0 : Wev (sig D n0) := (hW _).1 ⟨n0, hNA hn0, rfl⟩
    have hnc := ev_nonconst _ hv0 hne0
    have hWQ : ∀ w, Wev w → Q w := fun w hw => W_le Q hQ0 hQadd hQsh ⟨n0, hn0, rfl⟩ hnc hw
    refine le_antisymm hNA fun g hg => ?_
    obtain ⟨n, hn, hng⟩ := hWQ (sig D g) ((hW _).1 ⟨g, hg, rfl⟩)
    have hgn : g * n⁻¹ ∈ ballStab Γ G 2 α := by
      refine (sig_eq_zero_iff D F h71c (mul_mem hg (inv_mem (hNA hn)))).1 ?_
      rw [sig_mul D F hg (inv_mem (hNA hn)), sig_inv D F (hNA hn), hng]
      exact add_self_vec _
    have : g = (g * n⁻¹) * n := by group
    rw [this]
    exact N.mul_mem (hBN hgn) hn

theorem noncentral_of (hW : ∀ w, SigSet D w ↔ Wev w) (F : FanTree Γ G) (h71c : Fan71c F L) :
    ¬ (∀ g ∈ MulAction.stabilizer G α, ∀ k ∈ nbrStab Γ G α,
      g * k * g⁻¹ * k⁻¹ ∈ ballStab Γ G 2 α) := by
  intro hcon
  have hv : Wev (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) := by decide
  obtain ⟨k, hk, hkv⟩ := (hW _).2 hv
  have hx : D.x⁻¹ ∈ MulAction.stabilizer G α := inv_mem (D.x_mem_stabilizer F h71c)
  have h1 := hcon _ hx k hk
  rw [inv_inv] at h1
  have hconj : D.x⁻¹ * k * D.x ∈ nbrStab Γ G α := by
    have := F.conj_mem_nbrStab_of_stab hx hk
    simpa using this
  have h2 := (sig_eq_zero_iff D F h71c (mul_mem hconj (inv_mem hk))).2 h1
  rw [sig_mul D F hconj (inv_mem hk), sig_conj D F h71c, sig_inv D F hk, hkv] at h2
  exact sh_ne _ hv (by decide) (add_eq_zero_vec _ _ h2).symm

end P73

end CFSG.Quasithin.Fan86
