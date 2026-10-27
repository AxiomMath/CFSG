module

public import CFSG.RankThree.GF2n.Smith81.S81BGeom
public import CFSG.RankThree.GF2n.Smith81.S81E7Bruhat
public import CFSG.RankThree.GF2n.Smith81.S81CCases

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

variable (K : Type) [Field K]

@[expose] def vAut : (Module.End K (V K))ˣ ≃* (V K ≃ₗ[K] V K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K (V K)

theorem vAut_apply (g : (Module.End K (V K))ˣ) (x : V K) :
    vAut K g x = (g : Module.End K (V K)) x := rfl

@[expose] def EAut : Subgroup (V K ≃ₗ[K] V K) := (EGrp K).map (vAut K).toMonoidHom

@[expose] def rootSet7 : Set (V K ≃ₗ[K] V K) :=
  {g | ∃ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ ∧ pr ⟨0, by decide⟩ γ = 1 ∧
    ∃ c : K, g = vAut K (e7Data_valid.xu K γ c)}

@[expose] def rootRad7 : Subgroup (V K ≃ₗ[K] V K) := Subgroup.closure (rootSet7 K)

variable {K}

theorem rootRad7_le_EAut : rootRad7 K ≤ EAut K := by
  rw [rootRad7, Subgroup.closure_le]
  rintro g ⟨γ, -, -, c, rfl⟩
  exact Subgroup.mem_map.mpr ⟨_, e7Data_valid.xu_mem K γ c, rfl⟩

theorem mem_EAut_iff {g : V K ≃ₗ[K] V K} : g ∈ EAut K ↔ (vAut K).symm g ∈ EGrp K := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro h
    exact ⟨_, h, by simp⟩

end CFSG.RankThree.GF2n.Smith81.E7Model

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model

section ToUniform

variable
  {G : Type} [Group G] {K : Type} [Field K] [Finite K]
  {M Q Z B : Subgroup G} {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  [(Z.subgroupOf Q).Normal]
  {φ₀ : Lgen M (LB M Q B) →* (Module.End K (Fin e7Data.d →₀ K))ˣ}
  {ψ₀ : ↥Q ⧸ Z.subgroupOf Q ≃* Multiplicative (Fin e7Data.d →₀ K)}

@[expose] def E5WeightHyp (φ₀ : Lgen M (LB M Q B) →* (Module.End K (Fin e7Data.d →₀ K))ˣ)
    (ψ : M₀.E ≃ₗ[K] V K) : Prop :=
  ∀ A : Subgroup G, IsZConjugate Z A → A ≤ Q → A ≠ Z → ∃ g ∈ EAut K,
    (fun a : G => ψ (M₀.π a)) '' (A : Set G) = (Submodule.span K {g (w0 : V K)} : Set (V K)) ∧
    ∀ u ∈ conjSub g (rootRad7 K), ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A ∧
      ((vAut K).toMonoidHom.comp φ₀) t = u

end ToUniform

@[expose] def Smith24E5UniformStatement :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE5 M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∃ (ψ : M₀.E ≃ₗ[K] V K) (φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)),
            EUniData M Q Z B M₀ ψ φ (EAut K) (w0 : V K) (rootRad7 K)

end CFSG.RankThree.GF2n.Smith81
