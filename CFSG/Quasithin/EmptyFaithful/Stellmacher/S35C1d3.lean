module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1d2
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolBase
public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem perm3_sq_eq_one_of_pow {σ : Equiv.Perm (Fin 3)} {k : ℕ} (h : σ ^ 2 ^ k = 1) :
    σ * σ = 1 := by
  have h4 : ∀ σ : Equiv.Perm (Fin 3), σ ^ 4 = 1 → σ * σ = 1 := by decide
  induction k generalizing σ with
  | zero =>
    have : σ = 1 := by simpa using h
    rw [this, mul_one]
  | succ k ih =>
    have h2 : (σ ^ 2) ^ 2 ^ k = 1 := by rw [← pow_mul, ← pow_succ']; exact h
    have := ih h2
    apply h4
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_two σ, pow_two (σ * σ)]
    simpa [pow_two] using this

theorem perm3_eq_of_two_group {σ τ : Equiv.Perm (Fin 3)} (hτ : τ ≠ 1) (hτ2 : τ * τ = 1)
    (hσ : σ * σ = 1) (hστ : (σ * τ) * (σ * τ) = 1) : σ = 1 ∨ σ = τ := by
  revert σ τ; decide

theorem exists_sylow_centralizes {L : Subgroup G} (π : ↥L →* Equiv.Perm (Fin 3))
    (hker : ∀ g : ↥L, π g = 1 ↔ (g : G) ∈ pCoreOf 2 L) {u : G} {τ : Equiv.Perm (Fin 3)}
    (hτ : τ ≠ 1) (hτ2 : τ * τ = 1) (hu : Good (pCoreOf 2 L) π u τ) :
    ∃ T : Subgroup G, IsSylowTwoOf T L ∧ u ∈ quasithinOmegaOneCenter T := by
  obtain ⟨huY, t, ht, hc⟩ := hu
  have htQ : ((t * t : ↥L) : G) ∈ pCoreOf 2 L := (hker _).mp (by rw [map_mul, ht, hτ2])
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 L ⟨(t : G) * t, htQ⟩
  have hm' : ((t : G) * t) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have htm : (t : G) ^ 2 ^ (m + 1) = 1 := by
    rw [pow_succ', pow_mul, pow_two]; exact hm'
  have hP : IsPGroup 2 (Subgroup.zpowers (t : G)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one htm)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨T, hT, hzT⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge
    ((Subgroup.zpowers_le (g := (t : G)) (H := L)).mpr t.2) hP
  have hQT : pCoreOf 2 L ≤ T :=
    CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hT
  have htT : (t : G) ∈ T := hzT (Subgroup.mem_zpowers _)
  have hπT : ∀ x : ↥L, (x : G) ∈ T → π x * π x = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hT.2.1 ⟨x, hx⟩
    have hk' := congrArg (fun z : T => (z : G)) hk
    have : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    exact perm3_sq_eq_one_of_pow (by rw [← map_pow, this, map_one])
  refine ⟨T, hT, mem_quasithinOmegaOneCenter_iff.mpr ⟨hQT huY.1, ?_, huY.2.1⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hpL : p ∈ L := hT.1 hp
  have h1 := hπT ⟨p, hpL⟩ hp
  have h2 := hπT (⟨p, hpL⟩ * t) (T.mul_mem hp htT)
  rw [map_mul, ht] at h2
  rcases perm3_eq_of_two_group hτ hτ2 h1 h2 with h | h
  · exact huY.2.2 p ((hker ⟨p, hpL⟩).mp h)
  · have hq : (t : G)⁻¹ * p ∈ pCoreOf 2 L := by
      refine (hker (t⁻¹ * ⟨p, hpL⟩)).mp ?_
      rw [map_mul, map_inv, ht, h, inv_mul_cancel]
    have hqu := huY.2.2 _ hq
    calc p * u = t * ((t : G)⁻¹ * p * u) := by group
      _ = t * (u * ((t : G)⁻¹ * p)) := by rw [hqu]
      _ = (t * u) * ((t : G)⁻¹ * p) := by group
      _ = u * p := by rw [hc]; group

theorem mem_Zv_of_good {l : Geo H M} (π : ↥(stab l) →* Equiv.Perm (Fin 3))
    (hker : ∀ g : ↥(stab l), π g = 1 ↔ (g : G) ∈ Qv l) {u : G} {τ : Equiv.Perm (Fin 3)}
    (hτ : τ ≠ 1) (hτ2 : τ * τ = 1) (hu : Good (Qv l) π u τ) : u ∈ Zv l := by
  obtain ⟨T, hT, huT⟩ := exists_sylow_centralizes π hker hτ hτ2 hu
  have h : quasithinOmegaOneCenter T ≤ Zv l :=
    le_iSup₂_of_le (f := fun (T : Subgroup G) (_ : IsSylowTwoOf T (stab l)) =>
      quasithinOmegaOneCenter T) T hT le_rfl
  exact h huT

end S35.C1

end F53.Stellmacher

end CFSG.Quasithin
