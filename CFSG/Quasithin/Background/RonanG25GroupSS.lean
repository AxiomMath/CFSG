module

public import CFSG.Quasithin.Background.RonanG25GroupV

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

section Preimages

variable {G : Type} [Group G] {E : Type} [AddCommGroup E]

theorem pre_top_eq {B : Subgroup G} (φ : ↥B →* Multiplicative E) :
    pre B φ (⊤ : AddSubgroup E) = B := by
  ext y
  rw [mem_pre]
  exact ⟨fun ⟨hy, _⟩ => hy, fun hy => ⟨hy, AddSubgroup.mem_top _⟩⟩

theorem pre_bot_eq {B N' : Subgroup G} (φ : ↥B →* Multiplicative E) (hN' : N' ≤ B)
    (hker : ∀ y : ↥B, φ y = 1 ↔ (y : G) ∈ N') :
    pre B φ (⊥ : AddSubgroup E) = N' := by
  ext y
  rw [mem_pre]
  constructor
  · rintro ⟨hy, h⟩
    exact (hker ⟨y, hy⟩).mp (toAdd_eq_zero.mp (AddSubgroup.mem_bot.mp h))
  · intro hy
    have hyB : y ∈ B := hN' hy
    exact ⟨hyB, AddSubgroup.mem_bot.mpr (toAdd_eq_zero.mpr ((hker ⟨y, hyB⟩).mpr hy))⟩

theorem range_top_iff {B : Subgroup G} {φ : ↥B →* Multiplicative E}
    (hφ : Function.Surjective φ) (e : E) :
    e ∈ (⊤ : AddSubgroup E) ↔ ∃ y, φ y = Multiplicative.ofAdd e :=
  ⟨fun _ => hφ (Multiplicative.ofAdd e), fun _ => AddSubgroup.mem_top _⟩

end Preimages

section GroupSS

variable {G : Type} [Group G] [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G}

theorem chain_S₂_S₃_group (St : L3Setting n V V₁ L T H) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) {ord : Bool} :
    ChainCounts (GaloisField 2 n) (lOne L V₁) ord (gS₂ V H g h) (gS₃ V H L g h) s
      (if 2 < Nat.card (GaloisField 2 n) then s else 0) := by
  have hmod := (chain_piVd_ann (l1Rep St) s).trans (chain_piVd_up (l1Rep St) s)
  have hE : Equivariant (lOne L V₁) (gS₃ V H L g h) φ₆ (piAct s (actVd (rho St.D))) := by
    refine ⟨fun x hx y hy => ?_, fun x y y' hxy => ?_⟩
    · have hxN : x ∈ Subgroup.normalizer ((gS₃ V H L g h : Subgroup G) : Set G) :=
        hsub.I_S₃ ((le_sup_left : L ≤ L ⊔ conjClosure V H) (lOne_le_L hx))
      exact (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
    · have h6 := hsum.six.2.2 ⟨(x : G), lOne_le_L x.2⟩ y y' hxy.symm
      exact h6.trans (congrArg (fun v => Multiplicative.ofAdd v) (funext fun l => rfl))
  have key := ModChain.transport (ord := ord) (range_top_iff hsum.six.1) hE hmod le_top
  rw [pre_bot_eq φ₆ hsub.S₂_le_S₃ hsum.six.2.1, pre_top_eq φ₆, Nat.add_zero, Nat.zero_add] at key
  exact key

theorem chain_S₃_S_group (St : L3Setting n V V₁ L T H) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) {ord : Bool} :
    ChainCounts (GaloisField 2 n) (lOne L V₁) ord (gS₃ V H L g h) (gS V H L) r
      (if 2 < Nat.card (GaloisField 2 n) then r else 0) := by
  have hmod := (chain_piV_lines (l1Rep St) r).trans (chain_piV_up (l1Rep St) r)
  have hE : Equivariant (lOne L V₁) (gS V H L) φ₇ (piAct r (actV (rho St.D))) := by
    refine ⟨fun x hx y hy => ?_, fun x y y' hxy => ?_⟩
    · have hxN : x ∈ Subgroup.normalizer ((gS V H L : Subgroup G) : Set G) :=
        hsub.I_S ((le_sup_left : L ≤ L ⊔ conjClosure V H) (lOne_le_L hx))
      exact (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
    · have h7 := hsum.seven.2.2 ⟨(x : G), lOne_le_L x.2⟩ y y' hxy.symm
      exact h7.trans (congrArg (fun v => Multiplicative.ofAdd v) (funext fun l => rfl))
  have key := ModChain.transport (ord := ord) (range_top_iff hsum.seven.1) hE hmod le_top
  rw [pre_bot_eq φ₇ hsub.S₃_le_S hsum.seven.2.1, pre_top_eq φ₇, Nat.zero_add, Nat.add_zero] at key
  exact key

end GroupSS

end CFSG.Quasithin.RonanG25
