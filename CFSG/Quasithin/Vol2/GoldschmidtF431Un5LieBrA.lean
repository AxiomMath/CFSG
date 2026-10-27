module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5System
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNYam
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.Sec53F
  CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.Sec53F.Yam

section Bridge

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 2) ^ 2)

include hF in
omit [Finite F] [CharP F 2] in
theorem un5FD : UnitaryFieldData 2 2 F :=
  ⟨Nat.prime_two, by norm_num, by rw [hF, ← pow_mul]⟩

noncomputable def un5R : Matrix (Fin (2 * 2 + 1)) (HypIndex 2 1) F :=
  Classical.choose (exists_isHypTransport (r := 2) (ε := 1) (un5FD hF))

omit [Finite F] [CharP F 2] in
theorem un5R_spec : IsHypTransport (un5FD hF) (un5R hF) :=
  Classical.choose_spec (exists_isHypTransport (r := 2) (ε := 1) (un5FD hF))

noncomputable def un5Abs : SU (unitaryInvolution F 2 2) 5 ⧸
    Subgroup.center (SU (unitaryInvolution F 2 2) 5) ≃* hypPSU (un5FD hF) 2 1 :=
  (un5Equiv hF).trans (hypPSUEquivStatedProj (un5FD hF) (un5R_spec hF) (by norm_num)).symm

variable (ζ : traceZero (unitaryInvolution F 2 2)) [Fact ((ζ : F) ≠ 0)]

theorem map_map_symm {G H : Type*} [Group G] [Group H] (e : G ≃* H) (M : Subgroup G) :
    (M.map e.toMonoidHom).map e.symm.toMonoidHom = M := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩

theorem exists_un5Eps :
    ∃ ε : hypPSU (un5FD hF) 2 1 ≃* SU (unitaryInvolution F 2 2) 5 ⧸
        Subgroup.center (SU (unitaryInvolution F 2 2) 5),
      (hypProjUnitriangular (un5FD hF) 2 1).map ε.toMonoidHom = (un5System hF ζ).U ∧
      (((u5PtP (un5FD hF)).map ε.toMonoidHom = (un5System hF ζ).P₁ ∧
          (u5LnP (un5FD hF)).map ε.toMonoidHom = (un5System hF ζ).P₂) ∨
        ((u5PtP (un5FD hF)).map ε.toMonoidHom = (un5System hF ζ).P₂ ∧
          (u5LnP (un5FD hF)).map ε.toMonoidHom = (un5System hF ζ).P₁)) := by
  have := isSimpleGroup_un5 hF
  have hU0 := isSylowTwoOf_un5System hF ζ
  have : Finite (hypPSU (un5FD hF) 2 1) := finite_hypPSU_five (un5FD hF)
  obtain ⟨c, hcU, hcP⟩ := (u5_yamStd (h := un5FD hF)).pair (un5Abs hF)
    (BN.isYAmalgamPair (un5System hF ζ) hU0)
  let ε := (MulAut.conj c).trans (un5Abs hF).symm
  have key : ∀ (M : Subgroup (hypPSU (un5FD hF) 2 1))
      (X : Subgroup (SU (unitaryInvolution F 2 2) 5 ⧸
        Subgroup.center (SU (unitaryInvolution F 2 2) 5))),
      X.map (un5Abs hF).toMonoidHom = M.map (MulAut.conj c).toMonoidHom →
        M.map ε.toMonoidHom = X := by
    intro M X hX
    have : M.map ε.toMonoidHom = (M.map (MulAut.conj c).toMonoidHom).map
        (un5Abs hF).symm.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [this, ← hX]
    exact map_map_symm (un5Abs hF) X
  refine ⟨ε, key _ _ hcU, ?_⟩
  rcases hcP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨key _ _ h1, key _ _ h2⟩
  · exact Or.inr ⟨key _ _ h2, key _ _ h1⟩

noncomputable def un5Eps : hypPSU (un5FD hF) 2 1 ≃* SU (unitaryInvolution F 2 2) 5 ⧸
    Subgroup.center (SU (unitaryInvolution F 2 2) 5) :=
  Classical.choose (exists_un5Eps hF ζ)

theorem un5Eps_map_U :
    (hypProjUnitriangular (un5FD hF) 2 1).map (un5Eps hF ζ).toMonoidHom = (un5System hF ζ).U :=
  (Classical.choose_spec (exists_un5Eps hF ζ)).1

theorem un5Eps_map_P :
    (((u5PtP (un5FD hF)).map (un5Eps hF ζ).toMonoidHom = (un5System hF ζ).P₁ ∧
        (u5LnP (un5FD hF)).map (un5Eps hF ζ).toMonoidHom = (un5System hF ζ).P₂) ∨
      ((u5PtP (un5FD hF)).map (un5Eps hF ζ).toMonoidHom = (un5System hF ζ).P₂ ∧
        (u5LnP (un5FD hF)).map (un5Eps hF ζ).toMonoidHom = (un5System hF ζ).P₁)) :=
  (Classical.choose_spec (exists_un5Eps hF ζ)).2

end Bridge

end CFSG.Quasithin.H13.F431.Un
