module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresLinear
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresFamily
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresComm

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix

@[expose] def HermCoreInput : Prop :=
  ∀ (D : Type) [Field D] [Finite D] [CharP D 2] (d : ℕ)
    (T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D) (hT : IsInvol T),
    (∃ c : D, T (Matrix.scalar (Fin d) c) ≠ Matrix.scalar (Fin d) c) → HasCore (matUnitary hT)

@[expose] def AltCoreInput : Prop :=
  ∀ (D : Type) [Field D] [Finite D] [CharP D 2] (d : ℕ)
    (T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D) (hT : IsInvol T),
    (∀ c : D, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) c) → (∃ y, y + T y = 1) →
      HasCore (matUnitary hT)

theorem exists_coreFamily_unitaryOf (hHerm : HermCoreInput) (hAlt : AltCoreInput) {r : ℕ}
    {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Finite (D i)] [∀ i, CharP (D i) 2]
    {d : Fin r → ℕ} [∀ i, NeZero (d i)] {τ : PiMat D d → PiMat D d} (hτ : IsInvol τ)
    (hy : ∃ y, y + τ y = 1) :
    ∃ (β : Type) (S : β → Subgroup (PiMat D d)ˣ), IsCoreFamily (unitaryOf hτ) S := by
  obtain ⟨π, hπ⟩ := hτ.exists_perm
  have hfix : ∀ b (hb : π b = b), HasCore (matUnitary (isInvol_tauFix hτ hπ hb)) := by
    intro b hb
    by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
        Matrix.scalar (Fin (d b)) c
    · obtain ⟨Y, hY⟩ := hy
      refine hAlt (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk ⟨Y b, ?_⟩
      have h1 := congrFun hY b
      rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
    · push Not at hk
      exact hHerm (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk
  obtain ⟨β, S, h1, h2, h3, h4, h5⟩ :=
    exists_core_of_factors hτ hπ hfix (fun b _ => hasCore_top_GL (d b))
  exact ⟨β, S, h1, h2, h3, h4, h5⟩

section Adj

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def adjCent (A : Subgroup (GL ι K)) {adj : Matrix ι ι K → Matrix ι ι K}
    (hadj : IsInvol adj) : Subgroup (GL ι K) :=
  Subgroup.centralizer (A : Set (GL ι K)) ⊓ unitaryOf hadj

variable {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Algebra K (D i)] {d : Fin r → ℕ}

theorem exists_tau_of_adj (Φ : PiMat D d →ₐ[K] Matrix ι ι K) (hΦ : Function.Injective Φ)
    {A : Subgroup (GL ι K)}
    (hR : ∀ X : Matrix ι ι K, X ∈ Set.range Φ ↔ ∀ g ∈ A, X * (g : Matrix ι ι K) =
      (g : Matrix ι ι K) * X)
    {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)
    (hstab : ∀ X ∈ Set.range Φ, adj X ∈ Set.range Φ) :
    ∃ (τ : PiMat D d → PiMat D d) (hτ : IsInvol τ), (∀ y, Φ (τ y) = adj (Φ y)) ∧
      (unitaryOf hτ).map (Units.map Φ.toMonoidHom) = adjCent A hadj := by
  classical
  let τ : PiMat D d → PiMat D d := fun y => Function.invFun Φ (adj (Φ y))
  have hτΦ : ∀ y, Φ (τ y) = adj (Φ y) := fun y =>
    Function.invFun_eq (hstab _ ⟨y, rfl⟩)
  have hτ : IsInvol τ := by
    refine ⟨fun x y => hΦ ?_, fun x y => hΦ ?_, hΦ ?_, fun x => hΦ ?_⟩
    · rw [map_add, hτΦ, hτΦ, hτΦ, map_add, hadj.map_add]
    · rw [map_mul, hτΦ, hτΦ, hτΦ, map_mul, hadj.map_mul]
    · rw [hτΦ, map_one, hadj.map_one]
    · rw [hτΦ, hτΦ, hadj.invol]
  refine ⟨τ, hτ, hτΦ, le_antisymm ?_ fun g hg => ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun a ha => Units.ext ?_, ?_⟩
    · exact ((hR _).mp ⟨_, rfl⟩ a ha).symm
    · rw [mem_unitaryOf]
      show adj (Φ (u : PiMat D d)) * Φ (u : PiMat D d) = 1
      rw [← hτΦ, ← map_mul, mem_unitaryOf.mp hu, map_one]
  · obtain ⟨hgc, hgu⟩ := Subgroup.mem_inf.mp hg
    have hcomm : ∀ (h : GL ι K), h ∈ Subgroup.centralizer (A : Set (GL ι K)) →
        (h : Matrix ι ι K) ∈ Set.range Φ := fun h hh => (hR _).mpr fun a ha =>
      (congrArg Units.val (Subgroup.mem_centralizer_iff.mp hh a ha)).symm
    obtain ⟨y, hy⟩ := hcomm g hgc
    obtain ⟨y', hy'⟩ := hcomm g⁻¹ (Subgroup.inv_mem _ hgc)
    have h1 : y * y' = 1 := hΦ (by rw [map_mul, hy, hy', Units.mul_inv, map_one])
    have h2 : y' * y = 1 := hΦ (by rw [map_mul, hy, hy', Units.inv_mul, map_one])
    refine ⟨⟨y, y', h1, h2⟩, mem_unitaryOf.mpr ?_, Units.ext hy⟩
    apply hΦ
    show Φ (τ y * y) = Φ 1
    rw [map_mul, hτΦ, hy, map_one]
    exact mem_unitaryOf.mp hgu


theorem exists_coreFamily_adjCent (hHerm : HermCoreInput) (hAlt : AltCoreInput) {K : Type}
    [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Subgroup (GL ι K)} (hA : (Nat.card A : K) ≠ 0) {adj : Matrix ι ι K → Matrix ι ι K}
    (hadj : IsInvol adj)
    (hstab : ∀ X : Matrix ι ι K, (∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) →
      ∀ g ∈ A, adj X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * adj X)
    (hsymd : ∃ Y : Matrix ι ι K, (∀ g ∈ A, Y * (g : Matrix ι ι K) = (g : Matrix ι ι K) * Y) ∧
      Y + adj Y = 1) :
    ∃ (β : Type) (S : β → Subgroup (GL ι K)), IsCoreFamily (adjCent A hadj) S := by
  obtain ⟨r, D, d, _, _, _, _, Φ, hΦ, hR⟩ := exists_algHom_pi_matrix_commutant A hA
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap K (D i)).injective 2
  obtain ⟨τ, hτ, hτΦ, himg⟩ := exists_tau_of_adj Φ hΦ hR hadj fun X hX =>
    (hR _).mpr (hstab X ((hR X).mp hX))
  have hy : ∃ y, y + τ y = 1 := by
    obtain ⟨Y, hYc, hY⟩ := hsymd
    obtain ⟨y, rfl⟩ := (hR Y).mpr hYc
    exact ⟨y, hΦ (by rw [map_add, hτΦ, hY, map_one])⟩
  obtain ⟨β, S, hS⟩ := exists_coreFamily_unitaryOf hHerm hAlt hτ hy
  refine ⟨β, fun c => (S c).map (Units.map Φ.toMonoidHom), ?_⟩
  rw [← himg]
  exact hS.map _ (Units.map_injective (f := Φ.toMonoidHom) hΦ)

end Adj

end LayerCores

end CFSG.StandardType
