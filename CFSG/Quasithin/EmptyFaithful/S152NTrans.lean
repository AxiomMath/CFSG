module

public import CFSG.Quasithin.EmptyFaithful.S152NDelta

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace S152N

omit [Finite G] in
theorem cjSub_eq_bot_iff (g : G) {X : Subgroup G} : cjSub g X = ⊥ ↔ X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective X (MulAut.conj g).injective

variable {T H : Subgroup G} {V A : Subgroup G}

theorem exists_conj_isMinOffender (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V)
    (hord : (A ⊓ pCoreOf 2 H).relIndex A = 2) :
    ∃ h ∈ H, IsMinOffender T H V (cjSub h A) := by
  obtain ⟨h, hh, hAT⟩ := exists_conj_isMaxElemAbelian hT hA.1
  exact ⟨h, hh, isMinOffender_cjSub hT hA hord hh hAT⟩

omit [Finite G] in
theorem delta_quadratic (hA : A ∈ deltaSet H V) : ⁅⁅conjClosure V H, A⁆, A⁆ = ⊥ :=
  hA.2.2.2

theorem delta_fixed_eq {M : Subgroup G} (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V)
    (hord : (A ⊓ pCoreOf 2 H).relIndex A = 2) (hc : Concl319 T M V H True) :
    conjClosure V H ⊓ Subgroup.centralizer (A : Set G) =
      conjClosure V H ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
  obtain ⟨h, hh, hmin⟩ := exists_conj_isMinOffender hT hA hord
  have key : conjClosure V H ⊓ Subgroup.centralizer (cjSub h A : Set G) =
      conjClosure V H ⊓ Subgroup.centralizer ((cjSub h A ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
    hc.fixed_eq _ hmin
  have h1 := congrArg (cjSub h⁻¹) key
  rw [B2F.cjSub_inf, B2F.cjSub_inf, B2F.cjSub_centralizer, B2F.cjSub_centralizer,
    cjSub_conjClosure (H.inv_mem hh), cjSub_inv_cjSub, B2F.cjSub_inf, cjSub_inv_cjSub,
    cjSub_pCoreOf (H.inv_mem hh)] at h1
  exact h1

theorem delta_count {M : Subgroup G} (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V)
    (hord : (A ⊓ pCoreOf 2 H).relIndex A = 2) (hc : Concl319 T M V H True)
    (hne : ⁅V, A ⊓ pCoreOf 2 H⁆ ≠ ⊥) :
    Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 *
        Nat.card ↥(V ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) =
      Nat.card ↥(A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)) ^ 2 * Nat.card V := by
  obtain ⟨h, hh, hmin⟩ := exists_conj_isMinOffender hT hA hord
  have hQ := cjSub_pCoreOf hh
  have hB : cjSub h A ⊓ pCoreOf 2 H = cjSub h (A ⊓ pCoreOf 2 H) := by
    rw [B2F.cjSub_inf, hQ]
  have hV : conjSubgroup V h⁻¹ = cjSub h V := by
    unfold conjSubgroup cjSub
    rw [inv_inv]
  have hne' : ⁅cjSub h A ⊓ pCoreOf 2 H, conjSubgroup V h⁻¹⁆ ≠ ⊥ := by
    rw [hB, hV, ← cjSub_commutator]
    intro hbot
    apply hne
    rw [Subgroup.commutator_comm]
    exact (cjSub_eq_bot_iff h).mp hbot
  have h1 : Nat.card ↥(cjSub h A ⊓ pCoreOf 2 H) ^ 2 *
        Nat.card ↥(conjSubgroup V h⁻¹ ⊓
          Subgroup.centralizer ((cjSub h A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) =
      Nat.card ↥(cjSub h A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V h⁻¹ : Set G)) ^ 2 *
        Nat.card ↥(conjSubgroup V h⁻¹) :=
    hc.count_three _ hmin h⁻¹ (H.inv_mem hh) hne'
  have e1 : cjSub h V ⊓ Subgroup.centralizer ((cjSub h (A ⊓ pCoreOf 2 H) : Subgroup G) : Set G) =
      cjSub h (V ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) := by
    rw [B2F.cjSub_inf h V, B2F.cjSub_centralizer h]
  have e2 : cjSub h (A ⊓ pCoreOf 2 H) ⊓ Subgroup.centralizer ((cjSub h V : Subgroup G) : Set G) =
      cjSub h (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [B2F.cjSub_inf h (A ⊓ pCoreOf 2 H), B2F.cjSub_centralizer h]
  rw [hB, hV, e1, e2, card_cjSub, card_cjSub, card_cjSub, card_cjSub] at h1
  exact h1

@[expose] def Input15209Order : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ A ∈ deltaSet H (V154 T Mc M),
      (A ⊓ pCoreOf 2 H).relIndex A = 2

end S152N

end CFSG.Quasithin
