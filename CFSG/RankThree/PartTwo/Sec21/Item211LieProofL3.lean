module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofStar
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

open Item211Res2Proof
open scoped commutatorElement

@[expose] def IsL3Model211 (X : Type) [Group X] : Prop :=
  ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧ ∃ e : ℕ, 1 ≤ e ∧
    (Sec4.IsSLThreePiAt X (p ^ e) ∨ Sec4.IsoLThreePi X p e)

@[expose] def KS211L3Inner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsL3Model211 X →
    Odd (Nat.card (Subgroup.center X)) ∧
    ∀ τ ∈ Subgroup.closure {σ : MulAut X | σ ^ 3 = 1}, (∃ k : ℕ, τ ^ (2 ^ k) = 1) →
      τ ∈ (MulAut.conj : X →* MulAut X).range

@[expose] def KS211L3Minus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsL3Model211 X →
    ∀ T : Subgroup (MulAut X), T ≤ (MulAut.conj : X →* MulAut X).range → IsElemAbelian 2 T →
      Nat.card T = 4 → ∀ b : MulAut X, b ^ 3 = 1 → b ∈ Subgroup.centralizer (T : Set (MulAut X)) →
        ∀ W : Subgroup (MulAut X), IsPGroup 2 W →
          W ≤ (MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (T : Set (MulAut X)) →
          W ≤ Subgroup.centralizer ({b} : Set (MulAut X))

@[expose] def KS211L3Plus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsL3Model211 X →
    ∀ D T V W : Subgroup (MulAut X), IsElemAbelian 3 D → Nat.card D = 9 → IsPGroup 2 T →
      T ≠ ⊥ → T ≤ Subgroup.centralizer (D : Set (MulAut X)) →
      V ≤ (MulAut.conj : X →* MulAut X).range → IsPGroup 2 V →
      D ≤ Subgroup.normalizer (V : Set (MulAut X)) → ⁅V, D⁆ = V →
      V ≤ Subgroup.centralizer (T : Set (MulAut X)) → IsPGroup 2 W → V ≤ W →
      W ≤ Subgroup.centralizer (T : Set (MulAut X)) →
      (∀ τ ∈ (MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (T : Set (MulAut X)),
        τ ^ 3 = 1 → τ ∈ Subgroup.normalizer (W : Set (MulAut X))) →
      V = ⊥

namespace Item211LieProof

variable {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}

theorem commutator_le_closure_three {M : Type*} [Group M] (T D : Subgroup M)
    (hD : D ≤ Subgroup.closure {σ : M | σ ^ 3 = 1}) (hD3 : ∀ d ∈ D, d ^ 3 = 1) :
    ⁅T, D⁆ ≤ Subgroup.closure {σ : M | σ ^ 3 = 1} := by
  rw [Subgroup.commutator_le]
  intro t _ d hd
  rw [commutatorElement_def]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.inv_mem _ (hD hd))
  change (t * d * t⁻¹) ^ 3 = 1
  rw [conj_pow, hD3 d hd, mul_one, mul_inv_cancel]

theorem barImage_V_le_range_conj_of_L3 (hA : KS211L3Inner) (h : PairFacts A E U c L)
    (hX : IsL3Model211 (lBar L)) :
    barImage L (lThreeV E U c) ≤ (MulAut.conj : lBar L →* MulAut (lBar L)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinn := (hA (lBar L) h.q hX).2
  have hES : barImage L (E ⊓ Subgroup.centralizer (U : Set G)) ≤
      Subgroup.closure {σ : MulAut (lBar L) | σ ^ 3 = 1} := fun τ hτ =>
    Subgroup.subset_closure ((isElemAbelian_barImage_E h).2 τ (barImage_B_le_E hτ))
  have hVS : barImage L (lThreeV E U c) ≤ Subgroup.closure {σ : MulAut (lBar L) | σ ^ 3 = 1} := by
    rw [← barImage_V_comm_B h]
    exact commutator_le_closure_three _ _ hES fun d hd =>
      (isElemAbelian_barImage_E h).2 d (barImage_B_le_E hd)
  intro v hv
  obtain ⟨k, hk⟩ := (isPGroup_barImage_V h) ⟨v, hv⟩
  exact hinn v (hVS hv) ⟨k, by simpa using congrArg Subtype.val hk⟩

end Item211LieProof

open Item211LieProof

section Certs


theorem item211LieMinusL3_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hA : KS211L3Inner) (hB : KS211L3Minus) : Item211LieMinusL3 := by
  intro G _ _ A E U c L hpair _ hM hcase
  obtain ⟨-, p, hp, hp3, e, he, hmodel⟩ := hcase
  have h := pairFacts h45 h66 hpair
  have hX : IsL3Model211 (lBar L) := ⟨p, hp, hp3, e, he, hmodel⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinn := (hA (lBar L) h.q hX).2
  set Inn := (MulAut.conj : lBar L →* MulAut (lBar L)).range with hInn
  have hES : barImage L E ≤ Subgroup.closure {σ : MulAut (lBar L) | σ ^ 3 = 1} := fun τ hτ =>
    Subgroup.subset_closure ((isElemAbelian_barImage_E h).2 τ hτ)
  have hUeq := barImage_U_eq_comm_of_minus h hM
  have hUi : barImage L U ≤ Inn := by
    have hUS : barImage L U ≤ Subgroup.closure {σ : MulAut (lBar L) | σ ^ 3 = 1} := by
      rw [hUeq]
      exact commutator_le_closure_three _ _ hES (isElemAbelian_barImage_E h).2
    intro u hu
    obtain ⟨k, hk⟩ := (isPGroup_barImage_U h) ⟨u, hu⟩
    exact hinn u (hUS hu) ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hVi := barImage_V_le_range_conj_of_L3 hA h hX
  have hVeq := barImage_V_comm_B h
  apply barImage_V_ne_bot h
  rw [← hVeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbU : b ∈ Subgroup.centralizer (barImage L U : Set (MulAut (lBar L))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact barImage_U_comm_B u hu b hb
  have hW : barImage L (lThreeV E U c) ≤
      Inn ⊓ Subgroup.centralizer (barImage L U : Set (MulAut (lBar L))) := fun w hw =>
    Subgroup.mem_inf.mpr ⟨hVi hw, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      barImage_U_comm_V h u hu w hw⟩
  have h1 := hB (lBar L) h.q hX (barImage L U) hUi (isElemAbelian_barImage_U h)
    (card_barImage_U_of_minus h hM) b ((isElemAbelian_barImage_E h).2 b (barImage_B_le_E hb))
    hbU _ (isPGroup_barImage_V h) hW hv
  exact (Subgroup.mem_centralizer_singleton_iff.mp h1).symm

theorem item211LiePlusL3_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hA : KS211L3Inner) (hK : KS211L3Plus) : Item211LiePlusL3 := by
  intro G _ _ A E U c L hpair _ hP hcase
  obtain ⟨-, p, hp, hp3, e, he, hmodel⟩ := hcase
  have h := pairFacts h45 h66 hpair
  have hX : IsL3Model211 (lBar L) := ⟨p, hp, hp3, e, he, hmodel⟩
  have hZodd := (hA (lBar L) h.q hX).1
  set Inn := (MulAut.conj : lBar L →* MulAut (lBar L)).range with hInn
  have hBE : E ⊓ Subgroup.centralizer (U : Set G) = E :=
    inf_eq_left.mpr (mem_fourGroupsPlus_iff.mp hP).2
  have hVeq : ⁅barImage L (lThreeV E U c), barImage L E⁆ = barImage L (lThreeV E U c) := by
    have := barImage_V_comm_B h
    rwa [hBE] at this
  have hVi := barImage_V_le_range_conj_of_L3 hA h hX
  obtain ⟨R, hR2, hVR, hRU, -, hRτ⟩ := star hpair.mem_S h hZodd
  have hInnL : Inn ≤ barImage L L := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    exact mem_barImage_iff.mpr ⟨l, Subgroup.le_normalizer l.2, l.2, barAct_of_mem l.2⟩
  have hUC : barImage L U ≤ Subgroup.centralizer (barImage L E : Set (MulAut (lBar L))) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (barImage_U_comm_E_of_plus hP a ha x hx).symm
  have hVU : barImage L (lThreeV E U c) ≤
      Subgroup.centralizer (barImage L U : Set (MulAut (lBar L))) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact barImage_U_comm_V h u hu v hv
  have hRT : R ≤ Subgroup.centralizer (barImage L U : Set (MulAut (lBar L))) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hRU r hr u hu).symm
  refine barImage_V_ne_bot h (hK (lBar L) h.q hX (barImage L E) (barImage L U)
    (barImage L (lThreeV E U c)) R (isElemAbelian_barImage_E h) (card_barImage_E h)
    (isPGroup_barImage_U h) (barImage_U_ne_bot h) hUC hVi (isPGroup_barImage_V h)
    (barImage_E_le_normalizer_V h) hVeq hVU hR2 hVR hRT fun τ hτ hτ3 => ?_)
  exact hRτ τ (hInnL (Subgroup.mem_inf.mp hτ).1) (fun u hu =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hτ).2 u hu).symm) hτ3

end Certs

end CFSG.RankThree.PartTwo.Sec21
