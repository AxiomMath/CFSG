module

public import CFSG.Quasithin.EmptyFaithful.SzN28X0Core
public import CFSG.Quasithin.EmptyFaithful.SzN28Solv
public import CFSG.Quasithin.Background.P4InspOrthBasic
public import CFSG.Quasithin.EmptyFaithful.SzN28X0Syl
public import CFSG.Quasithin.EmptyFaithful.SzN28X0Zero

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN28

open CFSG.Quasithin.G11 CFSG.Quasithin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem x0_ne_bot (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)) (h : G111Hyp B Γ v₁ W X X₀)
    (h8 : G112Concl8S8 B Γ X) : X₀ ≠ ⊥ := by
  intro hX0
  subst hX0
  obtain ⟨e⟩ : Nonempty (↥Γ ≃* Equiv.Perm (Fin 8)) := h8.2.1
  have hV8 : Module.finrank (ZMod 2) V = 8 := h8.1
  obtain ⟨A, I, I', x₀, hd, -, hIiso⟩ := s8Data_iso_of_concl8 h.X_le h.X_sq h8
  have hc : F8Form B Γ A I I' x₀ := ⟨hd, h.alt, h.nondegenerate, h.isometry, hIiso⟩
  obtain ⟨e₀, he, f₀, hf, hv₁, he0, hf0⟩ := hc.exists_decomp h.point h.odd_index
  have hB0 := hc.B_e_f_zero hv₁ he hf h.odd_index
  obtain ⟨t, htA, ht⟩ := hc.exists_t he hf hB0
  have ht2 := hc.t_sq hB0 ht
  have htfix := hc.t_fix hB0 ht
  have ht1 := hc.t_ne_one he hf he0 hf0 ht
  have htΓ : t ∈ Γ := hd.A_le htA
  obtain ⟨n, hn⟩ := h.toG101Hyp.exists_card_X
  have hn3 : 3 ≤ n := by
    have hrank := h.rank
    rw [Subgroup.relIndex_bot_left, hn, Nat.log_pow Nat.one_lt_two, hV8] at hrank
    have := h.toG101Hyp.finrank_isotropic_le
    omega
  have hXbot : X ≠ ⊥ := by
    intro hb
    have h1 : Nat.card X = 1 := (Subgroup.eq_bot_iff_card X).1 hb
    rw [hn] at h1
    have h2 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨S, hS, hXS, hSN⟩ := h.four
  have hSΓ := h.toG101Hyp.isSylowTwoOf_of_stabilizer hS
  have hstab : ∀ g ∈ Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁, g (e₀ + f₀) = e₀ + f₀ := by
    intro g hg
    have h1 : g v₁ = v₁ := hg.2
    rwa [hv₁] at h1
  have htC : t ∈ Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁ :=
    ⟨htΓ, by
      show t v₁ = v₁
      rw [hv₁]
      exact htfix⟩
  have htcC : ∀ g ∈ Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁, g * t = t * g :=
    fun g hg => hc.t_comm he hf ht hg.1 (hstab g hg)
  have htS : t ∈ S := central_mem_sylow_two hS.2.1 hS.2.2 htC ht2 htcC
  have htX : t ∈ X :=
    t_mem_X e hSΓ.1 hSΓ.2.1 hSΓ.2.2 hXS hSN hXbot htS ht1 (fun s hs => htcC s (hS.1 hs))
  exact false_of_t_mem h.toG101Hyp hc he hf he0 hf0 hB0 hv₁ ht htX ht1

end CFSG.Quasithin.SzN28

namespace CFSG.Quasithin

theorem s8NoTrivialX0 : S8NoTrivialX0 := fun _ _ _ _ B Γ v₁ W X X₀ h h8 =>
  SzN28.x0_ne_bot B Γ v₁ W X X₀ h h8

namespace SzN28

theorem lemma14315Solvable_of_hP (h11 : StageLemma14111)
    (h113 : StageLemma14113) (hP : Lemma14315SolvableS8) : Lemma14315Solvable :=
  lemma14315Solvable_of_s8 h11 h113 hP s8NoTrivialX0

end SzN28

end CFSG.Quasithin
