module

public import CFSG.Quasithin.Vol2.Ch11SecO10W
public import CFSG.Quasithin.H13.A7Offender
public import CFSG.Quasithin.Background.B2Thompson

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
  CFSG.Quasithin.H13.A7

variable {G : Type} [Group G]

theorem offender_coord [Finite G] {V S A N : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (hNV : N ≤ normalizer (V : Set G)) (hN : ∀ n ∈ N, ∃ σ, IsCoordAct ψ n σ)
    (hVe : IsElemAbelian 2 V) (hVS : V ≤ S) (hA : IsMaxElemAbelian S A) (hAN : A ≤ N)
    (hAP : ∀ a ∈ A, ∃ σ ∈ sevenP, IsCoordAct ψ a σ) (hAC : ¬ A ≤ centralizer (V : Set G)) :
    (∀ a ∈ A, ∀ σ, IsCoordAct ψ a σ → InT3 σ) ∧ ∃ a ∈ A, ∃ σ, IsCoordAct ψ a σ ∧ IsTP σ := by
  classical
  set lamN : N →* Perm (Fin 7) := coordRep ψ hNV hN with hlamN
  set f : A →* Perm (Fin 7) := lamN.comp (inclusion hAN) with hfdef
  have hf_spec : ∀ a : A, IsCoordAct ψ a (f a) := fun a =>
    coordRep_spec ψ hNV hN ⟨a, hAN a.2⟩
  have hf_eq : ∀ (a : A) {σ : Perm (Fin 7)}, IsCoordAct ψ a σ → f a = σ := fun a σ hσ =>
    IsCoordAct.unique ψ (hNV (hAN a.2)) (hf_spec a) hσ
  have hfP : f.range ≤ sevenP := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨σ, hσP, hσ⟩ := hAP a a.2
    rw [hf_eq a hσ]
    exact hσP
  have hf2 : ∀ σ ∈ f.range, σ * σ = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have ha2 : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact hA.2.1.2 a a.2)
    rw [ha2, map_one]
  have hker : f.ker = (centralizer (V : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact coordRep_eq_one_iff ψ hNV hN ⟨a, hAN a.2⟩
  have hcardA : (A ⊓ centralizer (V : Set G)).relIndex A = Nat.card f.range := by
    rw [inf_relIndex_left, relIndex, ← hker, index_ker]
  have hcardV : Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) =
      Nat.card (fixE (f.range : Set (Perm (Fin 7)))) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨vec ψ ⟨(x : G), (mem_inf.1 x.2).1⟩,
      ?_, ?_⟩) ⟨?_, ?_⟩)
    · exact (mem_evenWeight).1 (vec_mem ψ _)
    · rintro _ ⟨a, rfl⟩
      have h1 := hf_spec a ⟨(x : G), (mem_inf.1 x.2).1⟩ ⟨(x : G), (mem_inf.1 x.2).1⟩ (by
        show (x : G) = a * x * (a : G)⁻¹
        rw [mem_centralizer_iff.1 (mem_inf.1 x.2).2 a a.2, mul_inv_cancel_right])
      exact h1.symm
    · intro x y hxy
      have h1 : vec ψ ⟨(x : G), (mem_inf.1 x.2).1⟩ = vec ψ ⟨(y : G), (mem_inf.1 y.2).1⟩ :=
        congrArg (fun z : fixE (f.range : Set (Perm (Fin 7))) => (z : Fin 7 → ZMod 2)) hxy
      have h2 : (x : G) = y := congrArg (fun z : V => (z : G)) (vec_injective ψ h1)
      exact Subtype.ext h2
    · rintro ⟨v, hv1, hv2⟩
      obtain ⟨x, hx⟩ := exists_vec_eq ψ (mem_evenWeight.2 hv1)
      refine ⟨⟨x, mem_inf.2 ⟨x.2, ?_⟩⟩, Subtype.ext hx⟩
      rw [mem_centralizer_iff]
      intro a ha
      let y : V := ⟨a * x * a⁻¹, (mem_normalizer_iff.1 (hNV (hAN ha)) x).1 x.2⟩
      have h1 := hf_spec ⟨a, ha⟩ x y rfl
      rw [hx, hv2 _ ⟨⟨a, ha⟩, rfl⟩, ← hx] at h1
      have h2 : a * (x : G) * a⁻¹ = x := congrArg Subtype.val (vec_injective ψ h1)
      calc a * (x : G) = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h2]
  have hoff : 64 ≤ Nat.card f.range * Nat.card (fixE (f.range : Set (Perm (Fin 7)))) := by
    have h1 := card_le_relIndex_mul_card hVe hVS hA
    rw [nat_card_of_vec ψ, hcardA, hcardV] at h1
    exact h1
  obtain ⟨hT3, hTP3⟩ := offender_spec hfP hf2 hoff
  have hne : f.range ≠ ⊥ := by
    intro hbot
    apply hAC
    intro a ha
    have h1 : f ⟨a, ha⟩ = 1 := by
      have : f ⟨a, ha⟩ ∈ f.range := ⟨⟨a, ha⟩, rfl⟩
      rw [hbot, mem_bot] at this
      exact this
    exact (coordRep_eq_one_iff ψ hNV hN ⟨a, hAN ha⟩).1 h1
  obtain ⟨σ, ⟨a, rfl⟩, hσ⟩ := hTP3 hne
  refine ⟨fun b hb τ hτ => ?_, a, a.2, f a, hf_spec a, hσ⟩
  rw [← hf_eq ⟨b, hb⟩ hτ]
  exact hT3 _ ⟨⟨b, hb⟩, rfl⟩

end CFSG.Quasithin.Vol2.Ch11.O10
