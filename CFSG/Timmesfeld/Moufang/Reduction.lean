module

public import CFSG.Timmesfeld.Moufang.Criterion
public import CFSG.Timmesfeld.Skeleton

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def CommLambda (D : Set G) : Prop :=
  ∀ y ∈ D, ∀ x₁ ∈ D, ∀ x₂ ∈ D, Commute y x₁ → y * x₁ ∈ D → Commute y x₂ → y * x₂ ∈ D →
    orderOf (x₁ * x₂) = 4 → (x₁ * x₂) ^ 2 ∈ rootSet D y

@[expose] def ExistsLine (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
    ∃ y ∈ D, (∀ a ∈ rootSet D d, Commute a y ∧ a * y ∈ D) ∧ orderOf (y * c) = 4

theorem commutatorInput_of (h : Hyp G D) (hQ : CommLambda D) (hE : ExistsLine D) :
    CommutatorInput D := by
  have hD := h.root
  intro d hd c hcD hdc hodd
  obtain ⟨y, hy, hline, hyc⟩ := hE d hd c hcD hdc hodd
  obtain ⟨hdy, hdyD⟩ := hline d (mem_rootSet_self hd)
  refine ⟨y, hy, hdy, hdyD, hyc, fun a ha => ?_⟩
  obtain ⟨hay, hayD⟩ := hline a ha
  obtain ⟨hwD, hyw, -, hcyc⟩ := sq_mem_of_orderOf_eq_four hD hy hcD hyc
  have hywD : y * (y * c) ^ 2 ∈ D := by
    rw [← hcyc]
    have := conj_mem_of_isClass h.isClass c hy
    rwa [hD.inv_eq hcD] at this
  have h4 : orderOf (d * (y * c) ^ 2) = 4 :=
    orderOf_mul_sq_eq_four h.isClass hD hd hcD hdc hodd hy hdy hdyD hyc
  have h4a : orderOf (a * (y * c) ^ 2) = 4 :=
    (orderOf_mul_eq_four_iff_of_mem_rootSet hD hd ha hwD).2 h4
  have h4wa : orderOf ((y * c) ^ 2 * a) = 4 := by rwa [orderOf_mul_comm_eq]
  exact hQ y hy _ hwD a ha.1 hyw hywD hay.symm (by rw [← hay.eq]; exact hayD) h4wa

theorem moufangInput_of (hR : RootSetInput)
    (hQ : ∀ (G : Type) [Group G] (D : Set G), Hyp G D → CommLambda D)
    (hE : ∀ (G : Type) [Group G] (D : Set G), Hyp G D →
      ExistsLine D ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
        Blueprint.NativeSporadic.IsSporadic G .J2) :
    MoufangInput := by
  intro G _ D h
  obtain ⟨hc, hs⟩ := hR G D h
  rcases hE G D h with hl | he | hj
  · exact .inl (rootMoufang_of_commutatorInput h hc hs (commutatorInput_of h (hQ G D h) hl))
  · exact .inr (.inl he)
  · exact .inr (.inr hj)

end CFSG.Timmesfeld.Moufang
