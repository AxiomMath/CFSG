module

public import CFSG.Sporadic.SuzOddCore.GraphPerms
public import CFSG.Certificates.NativeRefine

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2

theorem suzGamma_adj_map {g : Equiv.Perm (Fin 22880)} (hg : g ∈ suzP) (x y : Fin 22880) :
    suzGamma.Adj (g x) (g y) ↔ suzGamma.Adj x y := by
  have key : ∀ {g : Equiv.Perm (Fin 22880)}, g ∈ suzP → ∀ x y : Fin 22880,
      suzGamma.Adj x y → suzGamma.Adj (g x) (g y) := by
    intro g hg x y h
    rw [suzGamma_adj] at h ⊢
    obtain ⟨h', hh', i, hi, H⟩ := h
    refine ⟨g * h', suzP.mul_mem hg hh', i, hi, ?_⟩
    rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  refine ⟨fun h => ?_, key hg x y⟩
  have := key (suzP.inv_mem hg) _ _ h
  simpa using this

@[expose] def gammaBasePt (s : ℕ) : Fin 22880 := pt 22880 s

@[expose] def gammaStab (s : ℕ) : Subgroup (suzGamma ≃g suzGamma) := stabChain gammaBasePt s

theorem mem_gammaStab {s : ℕ} {σ : suzGamma ≃g suzGamma} :
    σ ∈ gammaStab s ↔ ∀ j < s, σ (gammaBasePt j) = gammaBasePt j := by
  rw [gammaStab, mem_stabChain]
  rfl

theorem gammaBasePt_val {s : ℕ} (hs : s < 22880) : ((gammaBasePt s : Fin 22880) : ℕ) = s :=
  pt_val hs

instance : Finite (suzGamma ≃g suzGamma) :=
  Finite.of_injective (fun σ : suzGamma ≃g suzGamma => σ.toEquiv) fun _ _ h =>
    RelIso.ext fun x => congrArg (fun e : Equiv.Perm (Fin 22880) => e x) h

@[expose] def gammaBounds (s : ℕ) : ℕ := [22880, 8505, 1152, 4].getD s 0

end CFSG.Sporadic.SuzOddCore
