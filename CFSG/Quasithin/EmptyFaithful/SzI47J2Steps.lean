module

public import CFSG.GH74.ThompsonOrderFormula
public import CFSG.Quasithin.Recognition.J2RecFiveQuot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.ShultStronglyClosedTI.InvolutionCounting

structure IsKernelComplement {G : Type} [Group G] [Finite G] {z : G} (F : J2Frame G z)
    (hcount : involutionClassCount G = 2) (R : Subgroup G) : Prop where
  t_mem : F.t ∈ R
  card : Nat.card R = 4
  mul_self : ∀ r ∈ R, r * r = 1
  le_T : R ≤ F.T
  comm_M : ∀ r ∈ R, ∀ m ∈ F.M hcount, r * m = m * r
  inf_W : R ⊓ F.W = ⊥
  X_eq : ∀ g ∈ F.X, ∃ m ∈ F.M hcount, ∃ r ∈ R, g = m * r

@[expose] def J2KernelAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (hcount : involutionClassCount G = 2)
    (F : J2Frame G z),
    Nonempty (↥(F.M hcount) ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (↥(F.M hcount) ≃* alternatingGroup (Fin 5))

@[expose] def J2KernelComplementExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (hcount : involutionClassCount G = 2)
    (F : J2Frame G z), ∃ R : Subgroup G, IsKernelComplement F hcount R

@[expose] def J2PairCountZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), involutionClassCount G = 2 →
    ∀ F : J2Frame G z, thompsonPairCount F.t z z = 960

@[expose] def J2PairCountT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (hcount : involutionClassCount G = 2)
    (F : J2Frame G z) (R : Subgroup G), IsKernelComplement F hcount R →
    Nonempty (↥(F.M hcount) ≃* alternatingGroup (Fin 4)) →
      thompsonPairCount F.t z F.t = 3 ∧ Nat.card (Subgroup.centralizer ({F.t} : Set G)) = 48

@[expose] def J2CardAlt4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (hcount : involutionClassCount G = 2)
    (F : J2Frame G z) (R : Subgroup G), IsKernelComplement F hcount R →
    Nonempty (↥(F.M hcount) ≃* alternatingGroup (Fin 4)) → Nat.card G = 51840

@[expose] def J2CardNe51840 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ z : G, IsTypeH2 G z →
    involutionClassCount G = 2 → Nat.card G ≠ 51840

@[expose] def J2ConfigOfAlt5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (hcount : involutionClassCount G = 2)
    (F : J2Frame G z) (R : Subgroup G), IsKernelComplement F hcount R →
    Nonempty (↥(F.M hcount) ≃* alternatingGroup (Fin 5)) →
      ∃ y : G, J2A5Config z (F.M hcount) R y

theorem j2CardAlt4_of_counts (hz : J2PairCountZ) (ht : J2PairCountT) : J2CardAlt4 := by
  intro G _ _ z hcount F R hR h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hr, hX⟩ := ht G z hcount F R hR h4
  have hz2 : orderOf z = 2 := orderOf_eq_prime F.isTypeH2.sq F.isTypeH2.ne_one
  have ht2 : orderOf F.t = 2 := orderOf_eq_prime (by rw [pow_two]; exact F.t_mul_t) F.t_ne_one
  have hnc : ¬ IsConj F.t z := fun h => F.not_isConj_t hcount h.symm
  have hcl : ∀ x : G, orderOf x = 2 → IsConj F.t x ∨ IsConj z x := by
    intro x hx
    have hx2 : x * x = 1 := by
      rw [← pow_two, ← hx]
      exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      rintro rfl
      simp at hx
    exact (F.isConj_z_or_t hcount hx2 hx1).symm
  rw [(CFSG.GH74.thompson_two_involution_class_order_formula ht2 hz2 hnc hcl).1,
    hz G z hcount F, hr, hX, F.isTypeH2.card_centralizer]

theorem j2Recognition_of_five
    (h1 : J2KernelAlt) (h1' : J2KernelComplementExists) (h2 : J2CardAlt4)
    (h3 : J2CardNe51840) (h4 : J2ConfigOfAlt5) : J2Recognition := by
  intro G _ _ hs hna z hz hcount
  obtain ⟨t, htC, ht2, htQ⟩ := hz.exists_involution_not_mem hcount
  obtain ⟨L, hLC, hLQ, hL⟩ := hz.exists_complement_of_involution htC ht2 htQ
  obtain ⟨F, -⟩ := J2Frame.exists_frame hz hLC hLQ hL
  obtain ⟨R, hR⟩ := h1' G z hcount F
  rcases h1 G z hcount F with h5 | h6
  · exact absurd (h2 G z hcount F R hR h5) (h3 G hs z hz hcount)
  · obtain ⟨y, hc⟩ := h4 G z hcount F R hR h6
    exact hc.nonempty_mulEquiv_J2 hz hcount

end CFSG.Quasithin
