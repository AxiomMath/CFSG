module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushNatCount
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G]

@[expose] def IsNatSecA5 (F L N : Subgroup G) : Prop :=
  ∃ _ : (L.subgroupOf N).Normal,
    ∃ (θ : ↥F →* ↥(alternatingGroup (Fin 5))) (β : nat.W →* ↥N ⧸ L.subgroupOf N),
      Function.Surjective θ ∧ θ.ker = (cSecIn F L N).subgroupOf F ∧
      SecData nat F L N ((alternatingGroup (Fin 5)).subtype.comp θ) β

theorem exists_hom_of_quot {X : Subgroup G} {K : Type*} [Group K] (e : OTwoQuot X ≃* K) :
    ∃ φ : ↥X →* K, Function.Surjective φ ∧ ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 X := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  show e (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy

theorem mem_cSecIn_iff_of_ker_hom {F L X : Subgroup G} {H : Type*} [Group H] {θ : ↥F →* H}
    (hk : θ.ker = (cSecIn F L X).subgroupOf F) {d : G} (hd : d ∈ F) :
    θ ⟨d, hd⟩ = 1 ↔ d ∈ cSecIn F L X := by
  rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf]

theorem ker_le_of_surjective {K H : Type*} [Group K] [Group H] [Finite H] {φ θ : K →* H}
    (hφ : Function.Surjective φ) (hθ : Function.Surjective θ) (h : φ.ker ≤ θ.ker) :
    θ.ker ≤ φ.ker := by
  have hidx : ∀ f : K →* H, Function.Surjective f → f.ker.index = Nat.card H := fun f hf => by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
  have h1 := Subgroup.relIndex_mul_index h
  rw [hidx φ hφ, hidx θ hθ] at h1
  have hpos : 0 < Nat.card H := Nat.card_pos
  have : φ.ker.relIndex θ.ker = 1 := by
    have h2 : φ.ker.relIndex θ.ker * Nat.card H = 1 * Nat.card H := by rw [h1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  exact Subgroup.relIndex_eq_one.mp this

theorem sign_eq_one_of_mem_pResidualOf [Finite G] {X : Subgroup G} {n : ℕ}
    (ψ : ↥X →* Perm (Fin n)) {x : G} (hx : x ∈ pResidualOf 2 X) :
    ∃ hX : x ∈ X, Perm.sign (ψ ⟨x, hX⟩) = 1 := by
  rw [← oTwoUpper_eq_pResidualOf] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine ⟨hx.1, ?_⟩
    set σ := ψ ⟨x, hx.1⟩ with hσ
    have h1 : σ ^ orderOf x = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨x, hx.1⟩ : ↥X) ^ orderOf x = 1 := Subtype.ext (by simp)
      rw [this, map_one]
    have h2 : Perm.sign σ ^ orderOf x = 1 := by
      rw [← map_pow, h1, map_one]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h
    · exact h
    · exfalso
      rw [h, Odd.neg_one_pow hx.2] at h2
      exact absurd h2 (by decide)
  | one =>
    refine ⟨X.one_mem, ?_⟩
    have : (⟨1, X.one_mem⟩ : ↥X) = 1 := rfl
    rw [this, map_one, map_one]
  | mul x y _ _ hx hy =>
    obtain ⟨hxX, hx⟩ := hx
    obtain ⟨hyX, hy⟩ := hy
    refine ⟨X.mul_mem hxX hyX, ?_⟩
    have : (⟨x * y, X.mul_mem hxX hyX⟩ : ↥X) = ⟨x, hxX⟩ * ⟨y, hyX⟩ := rfl
    rw [this, map_mul, map_mul, hx, hy, mul_one]
  | inv x _ hx =>
    obtain ⟨hxX, hx⟩ := hx
    refine ⟨X.inv_mem hxX, ?_⟩
    have : (⟨x⁻¹, X.inv_mem hxX⟩ : ↥X) = (⟨x, hxX⟩)⁻¹ := rfl
    rw [this, map_inv, map_inv, hx, inv_one]

theorem core_le_cSecIn {X S Z : Subgroup G} [Finite G] (h : PushHyp X S Z) (L : Subgroup G)
    {q : G} (hq : q ∈ pCoreOf 2 X) : q ∈ cSecIn X L Z := by
  refine Subgroup.subset_closure ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 X hq, fun y hy => ?_⟩
  have h1 : y * q = q * y := Subgroup.mem_centralizer_iff.mp (h.core_le_centralizer hq) y hy
  have : q * y * q⁻¹ * y⁻¹ = 1 := by rw [← h1]; group
  rw [this]
  exact L.one_mem

variable [Finite G] {X S Z : Subgroup G}

theorem pu1_s5_natural (h : PushHyp X S Z) (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)))
    (hnat : IsNatSec X (zZero X Z) Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    pResidualOf 2 X ⊓ S ≤ baum S ∧ IsSylowTwoOf (baum S) (conjClosure (baum S) X) ∧
      (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z = 16 := by
  obtain ⟨e⟩ := he
  obtain ⟨hnorm, θ, β, hθs, hθk, hsd⟩ := hnat
  obtain ⟨φ, hφs, hφk⟩ := exists_hom_of_quot e
  have hle : φ.ker ≤ θ.ker := fun x hx =>
    (mem_cSecIn_iff_of_ker_hom hθk x.2).mpr (core_le_cSecIn h _ ((hφk x).mp hx))
  have hker : ∀ x : ↥X, θ x = 1 → (x : G) ∈ pCoreOf 2 X := fun x hx =>
    (hφk x).mp (ker_le_of_surjective hφs hθs hle hx)
  have hev : ∀ x : ↥X, (x : G) ∈ pResidualOf 2 X → Perm.sign (θ x) = 1 := fun x hx => by
    obtain ⟨hX, hs⟩ := sign_eq_one_of_mem_pResidualOf θ hx
    exact hs
  have hcnt := natCounts_of_secData h hJ hsd hker hev (fun τ _ => hθs τ)
  simpa using pu1_of_counts h hJ hcnt

end CFSG.Quasithin.F53Push
