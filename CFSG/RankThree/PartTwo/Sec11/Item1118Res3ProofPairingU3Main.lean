module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Lin
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Rot

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Main

open Subgroup
open scoped Matrix MatrixGroups
open CFSG.RankThree.Classical2 (unitarySet)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem conj_commutator_mem {G : Type} [Group G] (A : Subgroup G) (g : G) {x : G}
    (hx : x ∈ ⁅A, A⁆) :
    g * x * g⁻¹ ∈ ⁅A.map (MulAut.conj g).toMonoidHom, A.map (MulAut.conj g).toMonoidHom⁆ := by
  have hmem : (MulAut.conj g).toMonoidHom x ∈ ⁅A, A⁆.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [Subgroup.map_commutator] at hmem
  exact hmem

theorem conj_or_powers_of_model {Ω : Type} [Field Ω] [IsAlgClosed Ω] {ℓ f : ℕ}
    [hℓ : Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 2)
    {R : Type} [Group R] {U : Subgroup (GL (Fin 3) Ω)}
    (hU : (U : Set (GL (Fin 3) Ω)) = unitarySet (ℓ ^ f) 3) (e : R ≃* U)
    (hZ : ∀ X : R, X ∈ Subgroup.center R → ∃ μ : Ω,
      (((e X : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) μ)
    {yR cR : R} (hy : ∀ x : R, yR * x = x * yR) (hy3 : yR ^ 3 = 1) (hy1 : yR ≠ 1)
    (hc3 : cR ^ 3 = 1) (hc1 : cR ≠ 1) :
    (∃ h : R, h * cR * h⁻¹ = cR * yR ∧ h * yR * h⁻¹ = yR) ∨ (cR = yR ∨ cR = yR ^ 2) := by
  have hpow : ∀ x : R, x ^ 3 = 1 →
      (((e x : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) ^ 3 = 1 := by
    intro x hx
    have h1 : (e x : U) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
    have h2 := congrArg (fun u : U => ((u : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω)) h1
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using h2
  have hyZ : yR ∈ Subgroup.center R := Subgroup.mem_center_iff.2 fun g => (hy g).symm
  obtain ⟨μ, hμ⟩ := hZ yR hyZ
  have hμ3 : μ ^ 3 = 1 := by
    apply Item1118Res3ProofU3Lin.scalar_pow_three_eq_one
    rw [← hμ]
    exact hpow yR hy3
  have hμ1 : μ ≠ 1 := by
    intro h1
    apply hy1
    apply Item1118Res3ProofU3Lin.eq_of_mat_eq e
    simp [hμ, h1]
  by_cases hs : ∃ ν : Ω, (((e cR : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      Matrix.scalar (Fin 3) ν
  · rcases Item1118Res3ProofU3Lin.central_mem_powers (c := cR) (d := yR) e hμ3 hμ1 hμ hs hc3 with
        h | h | h
    · exact absurd h hc1
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · push Not at hs
    have hXS : ((e cR : U) : GL (Fin 3) Ω) ∈ unitarySet (ℓ ^ f) 3 := by
      rw [← hU]
      exact (e cR).2
    have hX3 : ((e cR : U) : GL (Fin 3) Ω) ^ 3 = 1 := by
      have h1 : (e cR : U) ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
      have h2 := congrArg Subtype.val h1
      simpa using h2
    obtain ⟨G₁, hG₁U, l, hl3, hl1, hGX⟩ :=
      CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3.exists_rot_unitarySet hf hℓ3 hq1 hXS hX3 hs
    have hGU : G₁ ∈ U := by
      have : G₁ ∈ (U : Set (GL (Fin 3) Ω)) := by rw [hU]; exact hG₁U
      exact this
    obtain ⟨h, h1, h2⟩ := Item1118Res3ProofU3Lin.exists_conj_of_rot e (c := cR) (d := yR) hμ3 hμ1
      hμ hy ⟨G₁, hGU, l, hl3, hl1, hGX⟩
    exact Or.inl ⟨h, h1, h2⟩

theorem conj_mem_of_comm {G : Type} [Group G] {d c₀ c : G} {R : Subgroup G}
    (hcomm : ∀ a ∈ Subgroup.centralizer ({c₀ * d * c₀⁻¹} : Set G),
      ∀ b ∈ Subgroup.centralizer ({c₀ * d * c₀⁻¹} : Set G), a * b * a⁻¹ * b⁻¹ ∈ R)
    (hc : c ∈ ⁅Subgroup.centralizer ({d} : Set G), Subgroup.centralizer ({d} : Set G)⁆) :
    c₀ * c * c₀⁻¹ ∈ R := by
  have hsub : (Subgroup.centralizer ({d} : Set G)).map (MulAut.conj c₀).toMonoidHom ≤
      Subgroup.centralizer ({c₀ * d * c₀⁻¹} : Set G) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have had : d * a = a * d := Subgroup.mem_centralizer_iff.1 ha d (Set.mem_singleton d)
    show c₀ * d * c₀⁻¹ * (c₀ * a * c₀⁻¹) = c₀ * a * c₀⁻¹ * (c₀ * d * c₀⁻¹)
    calc c₀ * d * c₀⁻¹ * (c₀ * a * c₀⁻¹) = c₀ * (d * a) * c₀⁻¹ := by group
      _ = c₀ * (a * d) * c₀⁻¹ := by rw [had]
      _ = c₀ * a * c₀⁻¹ * (c₀ * d * c₀⁻¹) := by group
  have h1 := conj_commutator_mem (Subgroup.centralizer ({d} : Set G)) c₀ hc
  have h2 := Subgroup.commutator_mono hsub hsub
  have h3 : ⁅Subgroup.centralizer ({c₀ * d * c₀⁻¹} : Set G),
      Subgroup.centralizer ({c₀ * d * c₀⁻¹} : Set G)⁆ ≤ R :=
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact hcomm a ha b hb
  exact h3 (h2 h1)

theorem conj_pow_eq_conj {G : Type} [Group G] (a b : G) (n : ℕ) :
    (a * b * a⁻¹) ^ n = a * b ^ n * a⁻¹ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (a * b * a⁻¹) k, ih, pow_succ b k]
    simp only [mul_assoc, inv_mul_cancel_left]

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Main

end
