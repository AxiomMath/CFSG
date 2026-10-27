module

public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclBasic
import CFSG.LieType.SteinbergBRAutGL32
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

open Matrix CFSG.RepresentationTheory

private theorem false_of_diagonal_of_centralizes_r3 {r : ℕ} [Fact r.Prime]
    {K : Subgroup (GL (Fin 3) (ZMod r))} (hK : IsIrreducibleMatrixRep K.subtype)
    {y : GL (Fin 3) (ZMod r)} {α : Fin 3 → ZMod r}
    (hyd : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α) (hyns : ∃ i j, α i ≠ α j)
    (hc : ∀ x ∈ K, y * x = x * y) : False := by
  obtain ⟨i, j, hij⟩ := hyns
  refine hij (diagonal_apply_eq_of_commute_irreducible hK (fun k hk => ?_) i j)
  have h := congrArg (fun x : GL (Fin 3) (ZMod r) => (x : Matrix (Fin 3) (Fin 3) (ZMod r)))
    (hc k hk)
  simp only [Units.val_mul, hyd] at h
  exact h.symm

private theorem map_eq_one_of_pow_r3 {W Q : Type*} [Group W] [Group Q] (θ : W →* Q) {p : ℕ}
    (hp : p.Prime) (hpQ : ¬ p ∣ Nat.card Q) {g : W} (hg : g ^ p = 1) : θ g = 1 := by
  have hpow : θ g ^ p = 1 := by rw [← map_pow, hg, map_one]
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow) with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ orderOf_dvd_natCard (θ g)) hpQ

private theorem exists_hom_mulAut_of_perfect_r3 {G Q : Type*} [Group G] [Group Q]
    {K W : Subgroup G} [Group.IsPerfect K] (hWN : W ≤ Subgroup.normalizer (K : Set G))
    (e : (K ⧸ Subgroup.center K) ≃* Q) :
    ∃ θ : W →* MulAut Q, ∀ g : W, θ g = 1 → ∀ x ∈ K, (g : G) * x = x * g := by
  refine ⟨(MulAut.congr e).toMonoidHom.comp
    ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K).comp
      (K.normalizerMonoidHom.comp (Subgroup.inclusion hWN))), fun g hg x hx => ?_⟩
  have h1 : Subgroup.inclusion hWN g ∈ K.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
    apply (MulAut.congr e).injective
    rw [map_one, map_one]
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hg
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff] at h1
  exact (h1 x hx).symm

private theorem le_normalizer_r3 {r : ℕ} {W K : Subgroup (GL (Fin 3) (ZMod r))}
    (hnorm : ∀ g ∈ W, ∀ x ∈ K, g * x * g⁻¹ ∈ K) :
    W ≤ Subgroup.normalizer (K : Set (GL (Fin 3) (ZMod r))) := fun g hg =>
  Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hnorm g hg x hx, fun hx => by
    have h := hnorm g⁻¹ (W.inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h⟩

theorem false_of_alternating_five_of_coprime {r p : ℕ} [Fact r.Prime] (hp : p.Prime)
    (hp60 : ¬ p ∣ 60) {W K : Subgroup (GL (Fin 3) (ZMod r))} (hKW : K ≤ W)
    (hK : IsIrreducibleMatrixRep K.subtype) (e : Nonempty (K ≃* alternatingGroup (Fin 5)))
    (hprod : ∀ g ∈ W, ∃ h ∈ K, ∃ z ∈ W, (∀ x ∈ W, z * x = x * z) ∧ g = h * z)
    {y : GL (Fin 3) (ZMod r)} (hy : y ∈ W) (hyp : y ^ p = 1) {α : Fin 3 → ZMod r}
    (hyd : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α) (hyns : ∃ i j, α i ≠ α j) :
    False := by
  obtain ⟨e⟩ := e
  obtain ⟨h, hh, z, -, hzc, hyz⟩ := hprod y hy
  have hK60 : Nat.card K = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hh60 : h ^ 60 = 1 := by
    have h1 := pow_card_eq_one' (x := (⟨h, hh⟩ : K))
    rw [hK60] at h1
    simpa using congrArg Subtype.val h1
  have hy60 : ∀ x ∈ K, y ^ 60 * x = x * y ^ 60 := by
    intro x hx
    rw [hyz, (show Commute h z from (hzc h (hKW hh)).symm).mul_pow, hh60, one_mul]
    exact ((show Commute z x from hzc x (hKW hx)).pow_left 60).eq
  obtain ⟨u, -, hu⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hp60).symm
      hp.one_lt
  have hyu : y = (y ^ 60) ^ u := by
    rw [← pow_mul, pow_eq_pow_mod (60 * u) hyp, hu, pow_one]
  refine false_of_diagonal_of_centralizes_r3 hK hyd hyns fun x hx => ?_
  rw [hyu]
  exact ((show Commute (y ^ 60) x from hy60 x hx).pow_left u).eq

theorem false_of_gl_three_two_of_coprime {r p : ℕ} [Fact r.Prime] (hp : p.Prime)
    (hp336 : ¬ p ∣ 336) {W K : Subgroup (GL (Fin 3) (ZMod r))}
    (hnorm : ∀ g ∈ W, ∀ x ∈ K, g * x * g⁻¹ ∈ K) (hK : IsIrreducibleMatrixRep K.subtype)
    (e : Nonempty (K ≃* GL (Fin 3) (ZMod 2))) {y : GL (Fin 3) (ZMod r)} (hy : y ∈ W)
    (hyp : y ^ p = 1) {α : Fin 3 → ZMod r}
    (hyd : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α) (hyns : ∃ i j, α i ≠ α j) :
    False := by
  obtain ⟨e⟩ := e
  have hWN := le_normalizer_r3 hnorm
  have hcard : Nat.card (MulAut K) = 336 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32
  have h1 := map_eq_one_of_pow_r3 (K.normalizerMonoidHom.comp (Subgroup.inclusion hWN)) hp
    (by rwa [hcard]) (g := ⟨y, hy⟩) (Subtype.ext (by simpa using hyp))
  have hker : Subgroup.inclusion hWN ⟨y, hy⟩ ∈ K.normalizerMonoidHom.ker := MonoidHom.mem_ker.2 h1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff] at hker
  exact false_of_diagonal_of_centralizes_r3 hK hyd hyns fun x hx => (hker x hx).symm

theorem false_of_three_alt_six_of_coprime {r p : ℕ} [Fact r.Prime] (hp : p.Prime)
    (hp1440 : ¬ p ∣ 1440) {W K : Subgroup (GL (Fin 3) (ZMod r))}
    (hnorm : ∀ g ∈ W, ∀ x ∈ K, g * x * g⁻¹ ∈ K) (hK : IsIrreducibleMatrixRep K.subtype)
    (hperf : Group.IsPerfect K)
    (e : Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 6)))
    {y : GL (Fin 3) (ZMod r)} (hy : y ∈ W) (hyp : y ^ p = 1) {α : Fin 3 → ZMod r}
    (hyd : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α) (hyns : ∃ i j, α i ≠ α j) :
    False := by
  obtain ⟨e⟩ := e
  obtain ⟨θ, hθ⟩ := exists_hom_mulAut_of_perfect_r3 (le_normalizer_r3 hnorm) e
  have h1 := map_eq_one_of_pow_r3 θ hp
    (by rwa [CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]) (g := ⟨y, hy⟩)
    (Subtype.ext (by simpa using hyp))
  exact false_of_diagonal_of_centralizes_r3 hK hyd hyns (hθ ⟨y, hy⟩ h1)

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
