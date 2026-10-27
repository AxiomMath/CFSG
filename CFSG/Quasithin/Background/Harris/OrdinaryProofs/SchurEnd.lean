module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

lemma endCommutant_apply_comm {H : Subgroup (GLV V)} {f : V →ₗ[ZMod 2] V}
    (hf : f ∈ endCommutant H) {h : GLV V} (hh : h ∈ H) (v : V) :
    f (h v) = h (f v) := by
  have key := (Subalgebra.mem_centralizer_iff (ZMod 2)).mp hf (h : V →ₗ[ZMod 2] V) ⟨h, hh, rfl⟩
  have := congrArg (fun g : Module.End (ZMod 2) V => g v) key
  simpa [Module.End.mul_apply] using this.symm

lemma injective_of_mem_endCommutant {H : Subgroup (GLV V)} (hH : IsIrr H ⊤)
    {f : V →ₗ[ZMod 2] V} (hf : f ∈ endCommutant H) (hne : f ≠ 0) :
    Function.Injective f := by
  have hinv : Invariant H (LinearMap.ker f) := by
    intro k hk u hu
    rw [LinearMap.mem_ker] at hu ⊢
    rw [endCommutant_apply_comm hf hk, hu, map_zero]
  rcases hH.2.2 (LinearMap.ker f) hinv bot_le le_top with hbot | htop
  · exact LinearMap.ker_eq_bot.mp hbot
  · exfalso
    apply hne
    ext v
    have : v ∈ LinearMap.ker f := by rw [htop]; exact Submodule.mem_top
    simpa using this

lemma endCommutant_noZeroDivisors {H : Subgroup (GLV V)} (hH : IsIrr H ⊤) :
    NoZeroDivisors (endCommutant H) := by
  refine ⟨fun {a b} hab => ?_⟩
  by_cases ha : (a : Module.End (ZMod 2) V) = 0
  · exact Or.inl (Subtype.ext ha)
  · right
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have hinj := injective_of_mem_endCommutant hH a.2 ha
    apply hinj
    have h := congrArg (fun g : Module.End (ZMod 2) V => g v) (congrArg Subtype.val hab)
    simpa [Module.End.mul_apply] using h

lemma endCommutant_nontrivial {H : Subgroup (GLV V)} (hH : IsIrr H ⊤) :
    Nontrivial (endCommutant H) := by
  have hVnt : Nontrivial V := by
    obtain ⟨v, -, hv⟩ := (Submodule.ne_bot_iff _).mp (ne_of_lt hH.2.1).symm
    exact ⟨v, 0, hv⟩
  exact ⟨⟨1, Subalgebra.one_mem _⟩, ⟨0, Subalgebra.zero_mem _⟩,
    fun h => one_ne_zero (congrArg Subtype.val h)⟩

lemma exists_galoisField_of_finite_domain (K : Type) [Ring K] [IsDomain K] [Finite K]
    [alg : Algebra (ZMod 2) K] :
    ∃ e : ℕ, Nonempty (K ≃ₐ[ZMod 2] GaloisField 2 e) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2)]
    simp
  refine ⟨Module.finrank (ZMod 2) K, ⟨?_⟩⟩
  letI : Field K := (Finite.isDomain_to_isField K).toField
  letI : Algebra (ZMod 2) K := alg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact GaloisField.algEquivGaloisField 2 _ hcard

lemma exists_endIsField {H : Subgroup (GLV V)} (hH : IsIrr H ⊤) [Finite V] :
    ∃ e : ℕ, EndIsField H e := by
  have := endCommutant_nontrivial hH
  have := endCommutant_noZeroDivisors hH
  have : IsDomain (endCommutant H) := NoZeroDivisors.to_isDomain _
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have : Finite (endCommutant H) := Subtype.finite
  exact exists_galoisField_of_finite_domain (endCommutant H)

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
