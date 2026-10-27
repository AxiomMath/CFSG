module

public import CFSG.LieType.Universal.RootData
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem

open scoped Matrix

section Lattice

variable {N : ℕ}

@[expose] def latChar (p : ℕ) (f : Fin N → ZMod p) (α : Fin N → ℤ) : ZMod p :=
  ∑ i, (α i : ZMod p) * f i

@[expose] def latPhi (R : Set (Fin N → ℤ)) (p : ℕ) (f : Fin N → ZMod p) : Set (Fin N → ℤ) :=
  {α | α ∈ R ∧ latChar p f α = 0}

@[expose] def latGram (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) : ℤ :=
  ∑ i, ∑ j, α i * S i j * β j

@[expose] def latLinked (S : Matrix (Fin N) (Fin N) ℤ) (Φ : Set (Fin N → ℤ)) :
    (Fin N → ℤ) → (Fin N → ℤ) → Prop :=
  Relation.EqvGen fun α β => α ∈ Φ ∧ β ∈ Φ ∧ latGram S α β ≠ 0

@[expose] def latPerm (π : Equiv.Perm (Fin N)) (α : Fin N → ℤ) : Fin N → ℤ := fun i => α (π.symm i)

@[expose] def IsCompOrbit (S : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N)) (Φ O : Set (Fin N → ℤ)) :
    Prop :=
  ∃ α ∈ Φ, O = {β | ∃ k : ℕ, latLinked S Φ ((latPerm π)^[k] α) β}

@[expose] def IsSingleComp (S : Matrix (Fin N) (Fin N) ℤ) (Φ O : Set (Fin N → ℤ)) : Prop :=
  ∃ α ∈ O, ∀ β ∈ O, latLinked S Φ α β

@[expose] def LatSolv (q2 : Prop) (π : Equiv.Perm (Fin N)) (O : Set (Fin N → ℤ)) : Prop :=
  q2 ∧ ((∃ α, O = {α, -α}) ∨ (O.ncard = 6 ∧ ∀ α ∈ O, latPerm π α = α))

@[expose] def corootCoord (p : ℕ) (S : Matrix (Fin N) (Fin N) ℤ) (α : Fin N → ℤ) : Fin N → ZMod p :=
  fun i => ((2 * latGram S (Pi.single i 1) α / latGram S α α : ℤ) : ZMod p)

@[expose] def perp (R : Set (Fin N → ℤ)) (S : Matrix (Fin N) (Fin N) ℤ) (α : Fin N → ℤ) :
    Set (Fin N → ℤ) :=
  {β | β ∈ R ∧ latGram S α β = 0}

variable {U' : Type} [Group U']

@[expose] def NodesConnected (Δ : UniversalRootDatum U') (T : Set (Fin Δ.rank)) : Prop :=
  ((SimpleGraph.fromRel fun i j : Fin Δ.rank => Δ.cartan i j ≠ 0).induce T).Connected

@[expose] def IsRootGram (Δ : UniversalRootDatum U') (S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ) : Prop :=
  (∀ i j, S i j = S j i) ∧ (∀ i j, 2 * S i j = Δ.cartan i j * S i i) ∧ ∀ i, 0 < S i i

@[expose] def IsDiagAut (Δ : UniversalRootDatum U') (π : Equiv.Perm (Fin Δ.rank)) : Prop :=
  ∀ i j, Δ.cartan (π i) (π j) = Δ.cartan i j

@[expose] def LatCorootSpan (Δ : UniversalRootDatum U') (p : ℕ) : Set (Fin Δ.rank → ZMod p) :=
  {f | ∃ c : Fin Δ.rank → ℤ, ∀ i, f i = ∑ j, (c j : ZMod p) * (Δ.cartan j i : ZMod p)}

@[expose] def LatPlane (Δ : UniversalRootDatum U') (π : Equiv.Perm (Fin Δ.rank)) : Prop :=
  ∃ i j k : Fin Δ.rank, ¬ π.SameCycle i j ∧ π k = k ∧ ¬ π.SameCycle i k ∧ ¬ π.SameCycle j k ∧
    NodesConnected Δ {m | ¬ π.SameCycle i m ∧ ¬ π.SameCycle j m} ∧
    (3 ≤ Set.ncard {m : Fin Δ.rank | ¬ π.SameCycle i m ∧ ¬ π.SameCycle j m} ∨
      ∃ m m' : Fin Δ.rank, m ≠ m' ∧ (¬ π.SameCycle i m ∧ ¬ π.SameCycle j m) ∧
        (¬ π.SameCycle i m' ∧ ¬ π.SameCycle j m') ∧ 2 ≤ Δ.cartan m m' * Δ.cartan m' m)

@[expose] def LatAdmPlane (Δ : UniversalRootDatum U') (S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ) (p : ℕ)
    (q2 : Prop) (π : Equiv.Perm (Fin Δ.rank)) : Prop :=
  ∃ f₁ f₂ : Fin Δ.rank → ZMod p,
    (∀ i, f₁ (π i) = f₁ i) ∧ (∀ i, f₂ (π i) = f₂ i) ∧ f₁ ∈ LatCorootSpan Δ p ∧
    f₂ ∈ LatCorootSpan Δ p ∧ (∀ a b : ZMod p, a • f₁ + b • f₂ = 0 → a = 0 ∧ b = 0) ∧
    (∃ α ∈ Δ.roots, latPerm π α = α ∧ latChar p f₁ α = 0 ∧ latChar p f₂ α = 0) ∧
    ∀ a b : ZMod p, (a ≠ 0 ∨ b ≠ 0) →
      ∃ O, IsCompOrbit S π (latPhi Δ.roots p (a • f₁ + b • f₂)) O ∧ ¬ LatSolv q2 π O ∧
        Nat.card {g : Fin Δ.rank → ZMod p // (∀ i, g (π i) = g i) ∧ ∀ β ∈ O, latChar p g β = 0} ≤ p ^ 2

@[expose] def LatPerp (Δ : UniversalRootDatum U') : Prop :=
  ∀ S, IsRootGram Δ S → ∀ α ∈ Δ.roots, ∀ p : ℕ, p.Prime → p ≠ 2 →
    latPhi Δ.roots p (corootCoord p S α) = perp Δ.roots S α ∧
    (∀ β ∈ perp Δ.roots S α, ∀ γ ∈ perp Δ.roots S α, latLinked S (perp Δ.roots S α) β γ) ∧
    Nat.card {f : Fin Δ.rank → ZMod p // ∀ β ∈ perp Δ.roots S α, latChar p f β = 0} = p ∧
    7 ≤ (perp Δ.roots S α).ncard

@[expose] def latRefl (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) : Fin N → ℤ :=
  β - (2 * latGram S α β / latGram S α α) • α

@[expose] def StronglyOrth (Δ : UniversalRootDatum U') (α β : Fin Δ.rank → ℤ) : Prop :=
  α ≠ β ∧ α ≠ -β ∧ α + β ∉ Δ.roots ∧ α - β ∉ Δ.roots

theorem latGram_latPerm (Δ : UniversalRootDatum U') (S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ)
    (hS : IsRootGram Δ S) (π : Equiv.Perm (Fin Δ.rank)) (hπ : IsDiagAut Δ π)
    (hconn : NodesConnected Δ Set.univ) (α β : Fin Δ.rank → ℤ) :
    latGram S (latPerm π α) (latPerm π β) = latGram S α β := by
  classical
  have hsym : ∀ i j, S i j = S j i := hS.1
  have hdiag : ∀ i j, 2 * S i j = Δ.cartan i j * S i i := hS.2.1
  have hpos : ∀ i, 0 < S i i := hS.2.2
  have key : ∀ i j, Δ.cartan i j * S i i = Δ.cartan j i * S j j := by
    intro i j
    calc Δ.cartan i j * S i i = 2 * S i j := (hdiag i j).symm
      _ = 2 * S j i := by rw [hsym i j]
      _ = Δ.cartan j i * S j j := hdiag j i
  have keyπ : ∀ i j, Δ.cartan i j * S (π i) (π i) = Δ.cartan j i * S (π j) (π j) := by
    intro i j
    have h := key (π i) (π j)
    rwa [hπ i j, hπ j i] at h
  have cross : ∀ i j, Δ.cartan i j ≠ 0 → S i i * S (π j) (π j) = S (π i) (π i) * S j j := by
    intro i j hij
    have h1 := key i j
    have h2 := keyπ i j
    have hmul : Δ.cartan i j * (S i i * S (π j) (π j)) =
        Δ.cartan i j * (S (π i) (π i) * S j j) := by
      calc Δ.cartan i j * (S i i * S (π j) (π j))
          = (Δ.cartan i j * S i i) * S (π j) (π j) := by ring
        _ = (Δ.cartan j i * S j j) * S (π j) (π j) := by rw [h1]
        _ = Δ.cartan j i * (S j j * S (π j) (π j)) := by ring
        _ = Δ.cartan j i * (S (π j) (π j) * S j j) := by ring
        _ = (Δ.cartan j i * S (π j) (π j)) * S j j := by ring
        _ = (Δ.cartan i j * S (π i) (π i)) * S j j := by rw [← h2]
        _ = Δ.cartan i j * (S (π i) (π i) * S j j) := by ring
    exact mul_left_cancel₀ hij hmul
  let G : SimpleGraph (Fin Δ.rank) := SimpleGraph.fromRel fun i j => Δ.cartan i j ≠ 0
  have hconnG : G.Connected :=
    (SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso G)).mp hconn
  haveI : Nonempty (Fin Δ.rank) := ⟨hconn.nonempty.some.1⟩
  obtain ⟨i0, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun i => S i i) Finset.univ_nonempty
  have crossAdj : ∀ i j, G.Adj i j → S i i * S (π j) (π j) = S (π i) (π i) * S j j := by
    intro i j hij
    rcases hij with ⟨-, h | h⟩
    · exact cross i j h
    · have h' := cross j i h
      calc S i i * S (π j) (π j) = S (π j) (π j) * S i i := by ring
        _ = S j j * S (π i) (π i) := h'.symm
        _ = S (π i) (π i) * S j j := by ring
  let P : Fin Δ.rank → Prop := fun i => S (π i) (π i) * S i0 i0 = S i i * S (π i0) (π i0)
  have hstep : ∀ b c, G.Adj b c → P b → P c := by
    intro b c hbc hPb
    simp only [P] at hPb
    have hrel := crossAdj b c hbc
    have hkey : S b b * (S (π c) (π c) * S i0 i0) =
        S b b * (S c c * S (π i0) (π i0)) := by
      calc S b b * (S (π c) (π c) * S i0 i0)
          = (S b b * S (π c) (π c)) * S i0 i0 := by ring
        _ = (S (π b) (π b) * S c c) * S i0 i0 := by rw [hrel]
        _ = S (π b) (π b) * (S c c * S i0 i0) := by ring
        _ = S (π b) (π b) * (S i0 i0 * S c c) := by ring
        _ = (S (π b) (π b) * S i0 i0) * S c c := by ring
        _ = (S b b * S (π i0) (π i0)) * S c c := by rw [hPb]
        _ = S b b * (S (π i0) (π i0) * S c c) := by ring
        _ = S b b * (S c c * S (π i0) (π i0)) := by ring
    exact mul_left_cancel₀ (hpos b).ne' hkey
  have hPall : ∀ i, P i := by
    intro i
    have hrt := (SimpleGraph.reachable_iff_reflTransGen i0 i).mp (hconnG.preconnected i0 i)
    induction hrt with
    | refl => exact mul_comm _ _
    | tail _ hbc ih => exact hstep _ _ hbc ih
  have hdiagπ : ∀ i, S (π i) (π i) = S i i := by
    intro i
    have hA : S (π i0) (π i0) ≤ S i0 i0 := hmax _ (Finset.mem_univ _)
    have hB : S i0 i0 ≤ S (π i0) (π i0) := by
      have hp := hPall (π.symm i0)
      simp only [P] at hp
      have hπi : π (π.symm i0) = i0 := Equiv.apply_symm_apply π i0
      rw [hπi] at hp
      have hd' : S (π.symm i0) (π.symm i0) ≤ S i0 i0 := hmax _ (Finset.mem_univ _)
      have hApos : 0 < S (π i0) (π i0) := hpos _
      have hBpos : 0 < S i0 i0 := hpos _
      have hle : S i0 i0 * S i0 i0 ≤ S i0 i0 * S (π i0) (π i0) := by
        rw [hp]
        exact mul_le_mul_of_nonneg_right hd' hApos.le
      exact (mul_le_mul_iff_right₀ hBpos).mp hle
    have hAB : S (π i0) (π i0) = S i0 i0 := le_antisymm hA hB
    have hp := hPall i
    simp only [P] at hp
    rw [hAB] at hp
    exact mul_right_cancel₀ (hpos i0).ne' hp
  have hSπ : ∀ i j, S (π i) (π j) = S i j := by
    intro i j
    have h1 := hdiag (π i) (π j)
    have h2 := hdiag i j
    rw [hπ i j, hdiagπ i] at h1
    have : (2 : ℤ) * S (π i) (π j) = 2 * S i j := by rw [h1, h2]
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) this
  simp only [latGram, latPerm]
  have hreindex : (∑ i, ∑ j, α (π.symm i) * S i j * β (π.symm j))
      = ∑ i, ∑ j, α i * S (π i) (π j) * β j := by
    rw [← Equiv.sum_comp π (fun i => ∑ j, α (π.symm i) * S i j * β (π.symm j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Equiv.symm_apply_apply]
    rw [← Equiv.sum_comp π (fun j => α i * S (π i) j * β (π.symm j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Equiv.symm_apply_apply]
  rw [hreindex]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hSπ i j]

theorem latCorootSpan_eq_top (Δ : UniversalRootDatum U') (p : ℕ) (hp : p.Prime)
    (hdet : ¬ (p : ℤ) ∣ Δ.cartan.det) (f : Fin Δ.rank → ZMod p) : f ∈ LatCorootSpan Δ p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let A : Matrix (Fin Δ.rank) (Fin Δ.rank) (ZMod p) := Δ.cartan.map fun x => (x : ZMod p)
  have hAdet : A.det = ((Δ.cartan.det : ℤ) : ZMod p) := (Int.cast_det Δ.cartan).symm
  have hAne : A.det ≠ 0 := by
    rw [hAdet]
    exact fun h => hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hAne
  let c' : Fin Δ.rank → ZMod p := (Aᵀ)⁻¹ *ᵥ f
  let c : Fin Δ.rank → ℤ := fun j => (ZMod.intCast_surjective (c' j)).choose
  have hc : ∀ j, (c j : ZMod p) = c' j := fun j => (ZMod.intCast_surjective (c' j)).choose_spec
  have hmul : Aᵀ *ᵥ c' = f := by
    show Aᵀ *ᵥ ((Aᵀ)⁻¹ *ᵥ f) = f
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Aᵀ (by rwa [Matrix.det_transpose]),
      Matrix.one_mulVec]
  refine ⟨c, fun i => ?_⟩
  have hfi : f i = ∑ j, A j i * c' j := by
    rw [← congrFun hmul i, Matrix.mulVec_apply_eq_sum]
    simp only [Matrix.transpose_apply]
  rw [hfi]
  change (∑ j, A j i * c' j) = ∑ j, (c j : ZMod p) * A j i
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hc j]
  ring

private theorem neg_mem_roots {U' : Type} [Group U'] (Δ : UniversalRootDatum U')
    {α : Fin Δ.rank → ℤ} (hα : α ∈ Δ.roots) : -α ∈ Δ.roots := by
  rcases hα with h | h
  · rcases h with ⟨w, i, rfl⟩
    refine Or.inl ⟨w * (coxeterMatrix Δ.isFiniteType).toCoxeterSystem.simple i, i, ?_⟩
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg]
  · rcases h with ⟨w, i, hi, rfl⟩
    refine Or.inr ⟨w * (coxeterMatrix Δ.isFiniteType).toCoxeterSystem.simple i, i, hi, ?_⟩
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg, smul_neg]

theorem stronglyOrth_neg (Δ : UniversalRootDatum U') {α β : Fin Δ.rank → ℤ}
    (h : StronglyOrth Δ α β) : StronglyOrth Δ (-α) β := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hh; exact h2 (by simpa using congrArg Neg.neg hh)
  · intro hh; exact h1 (neg_inj.mp hh)
  · intro hh
    have := neg_mem_roots Δ hh
    rw [show -(-α + β) = α - β by abel] at this
    exact h4 this
  · intro hh
    have := neg_mem_roots Δ hh
    rw [show -(-α - β) = α + β by abel] at this
    exact h3 this

theorem latPhi_smul (R : Set (Fin N → ℤ)) (p : ℕ) [Fact p.Prime] (k : ZMod p) (hk : k ≠ 0)
    (f : Fin N → ZMod p) : latPhi R p (k • f) = latPhi R p f := by
  ext α
  simp only [latPhi, Set.mem_setOf_eq]
  have hchar : latChar p (k • f) α = k * latChar p f α := by
    simp only [latChar, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hchar]
  constructor
  · rintro ⟨hR, h0⟩; exact ⟨hR, (mul_eq_zero.mp h0).resolve_left hk⟩
  · rintro ⟨hR, h0⟩; exact ⟨hR, by rw [h0, mul_zero]⟩

end Lattice

end CFSG.StandardType
