module

public import CFSG.Permutation.FiveTransitive.SolvableOrbitGoursat

public section

namespace CFSG

namespace FiveTransitive.PrimeCyclicFixedAction

open Subgroup MulAction SubMulAction

@[expose] abbrev cyclicSubgroup
    {X : Type*} (P : Subgroup (Equiv.Perm X)) (r : P) :
    Subgroup P :=
  Subgroup.zpowers r

@[expose] abbrev cyclicNormalizer
    {X : Type*} (P : Subgroup (Equiv.Perm X)) (r : P) :
    Subgroup P :=
  Subgroup.normalizer (cyclicSubgroup P r : Set P)

@[expose] abbrev cyclicInNormalizer
    {X : Type*} (P : Subgroup (Equiv.Perm X)) (r : P) :
    Subgroup (cyclicNormalizer P r) :=
  (cyclicSubgroup P r).subgroupOf (cyclicNormalizer P r)

@[expose] abbrev cyclicFixedPoints
    (X : Type*) (P : Subgroup (Equiv.Perm X)) (r : P) :
    SubMulAction (cyclicNormalizer P r) X :=
  fixedPointsSubMulOfNormal
    (G := cyclicNormalizer P r) (α := X)
    (H := cyclicInNormalizer P r)

@[expose] abbrev cyclicComplement
    (X : Type*) (P : Subgroup (Equiv.Perm X)) (r : P) :
    SubMulAction (cyclicNormalizer P r) X :=
  (cyclicFixedPoints X P r)ᶜ

@[expose] def generatorInNormalizer
    {X : Type*} (P : Subgroup (Equiv.Perm X)) (r : P) :
    cyclicNormalizer P r :=
  ⟨r, (cyclicSubgroup P r).le_normalizer
    (Subgroup.mem_zpowers r)⟩

def complementPerm
    (X : Type*) (P : Subgroup (Equiv.Perm X)) (r : P) :
    Equiv.Perm (cyclicComplement X P r) :=
  MulAction.toPermHom (cyclicNormalizer P r)
    (cyclicComplement X P r) (generatorInNormalizer P r)

theorem fixedPoints_eq_fixedPoints_generator
    (X : Type*) (P : Subgroup (Equiv.Perm X)) (r : P) :
    (cyclicFixedPoints X P r : Set X) =
      Function.fixedPoints ((r : P) : Equiv.Perm X) := by
  ext x
  change
    x ∈ MulAction.fixedPoints (cyclicInNormalizer P r) X ↔
      x ∈ Function.fixedPoints ((r : P) : Equiv.Perm X)
  rw [MulAction.mem_fixedPoints,
    Function.mem_fixedPoints_iff]
  constructor
  · intro hx
    let rN : cyclicNormalizer P r :=
      generatorInNormalizer P r
    let rSN : cyclicInNormalizer P r :=
      ⟨rN, Subgroup.mem_zpowers r⟩
    have hrFix := hx rSN
    simpa [rSN, rN, generatorInNormalizer,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hrFix
  · intro hx z
    have hrStab :
        r ∈ MulAction.stabilizer P x := by
      rw [MulAction.mem_stabilizer_iff]
      simpa [Subgroup.smul_def,
        Equiv.Perm.smul_def] using hx
    have hzStab :
        ((z : cyclicNormalizer P r) : P) ∈
          MulAction.stabilizer P x :=
      (Subgroup.zpowers_le.mpr hrStab) z.prop
    have hzFix := MulAction.mem_stabilizer_iff.mp hzStab
    simpa [Subgroup.smul_def,
      Equiv.Perm.smul_def] using hzFix

theorem complementPerm_fixedPointFree
    (X : Type*) (P : Subgroup (Equiv.Perm X)) (r : P) :
    ∀ x : cyclicComplement X P r,
      complementPerm X P r x ≠ x := by
  intro x hx
  have hxval := congrArg Subtype.val hx
  have hrFix :
      ((r : P) : Equiv.Perm X) x.1 = x.1 := by
    simpa [complementPerm, generatorInNormalizer,
      MulAction.toPermHom_apply, MulAction.toPerm_apply,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hxval
  have hxF : x.1 ∈ cyclicFixedPoints X P r := by
    change x.1 ∈ (cyclicFixedPoints X P r : Set X)
    rw [fixedPoints_eq_fixedPoints_generator]
    exact hrFix
  exact x.2 hxF

theorem orderOf_complementPerm
    (X : Type*) (P : Subgroup (Equiv.Perm X))
    (r : P) {p : ℕ}
    (hp : p.Prime) (horder : orderOf r = p) :
    orderOf (complementPerm X P r) = p := by
  letI : Fact p.Prime := ⟨hp⟩
  let N := cyclicNormalizer P r
  let FC := cyclicComplement X P r
  let rN : N := generatorInNormalizer P r
  let τ : N →* Equiv.Perm FC :=
    MulAction.toPermHom N FC
  let g : Equiv.Perm FC := complementPerm X P r
  have hrpow : r ^ p = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one r
  have hrNpow : rN ^ p = 1 := by
    apply Subtype.ext
    exact hrpow
  have hgpow : g ^ p = 1 := by
    change τ rN ^ p = 1
    rw [← map_pow, hrNpow, map_one]
  have hrNe : r ≠ 1 := by
    intro hr
    rw [hr, orderOf_one] at horder
    exact hp.ne_one horder.symm
  have hrPermNe : ((r : P) : Equiv.Perm X) ≠ 1 := by
    intro hr
    apply hrNe
    apply Subtype.ext
    exact hr
  obtain ⟨x, hx⟩ :
      ∃ x : X, ((r : P) : Equiv.Perm X) x ≠ x := by
    exact Classical.byContradiction fun h ↦
      hrPermNe (Equiv.ext fun x ↦
        not_ne_iff.mp ((not_exists.mp h) x))
  have hxFC : x ∈ cyclicComplement X P r := by
    change x ∉ (cyclicFixedPoints X P r : Set X)
    rw [fixedPoints_eq_fixedPoints_generator]
    exact hx
  let y : FC := ⟨x, hxFC⟩
  have hgNe : g ≠ 1 := by
    intro hg
    have hy := complementPerm_fixedPointFree X P r y
    apply hy
    change g y = y
    rw [hg]
    rfl
  exact orderOf_eq_prime hgpow hgNe

theorem cyclicInNormalizer_eq_zpowers_generator
    {X : Type*} (P : Subgroup (Equiv.Perm X)) (r : P) :
    cyclicInNormalizer P r =
      Subgroup.zpowers (generatorInNormalizer P r) := by
  ext z
  constructor
  · intro hz
    obtain ⟨m, hm⟩ :=
      Subgroup.mem_zpowers_iff.mp hz
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    apply Subtype.ext
    exact hm
  · intro hz
    obtain ⟨m, hm⟩ :=
      Subgroup.mem_zpowers_iff.mp hz
    change ((z : cyclicNormalizer P r) : P) ∈
      Subgroup.zpowers r
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    have hmP := congrArg
      (fun q : cyclicNormalizer P r ↦ (q : P)) hm
    exact hmP

private theorem complement_range_le_normalizer_zpowers
    (X : Type*) (P : Subgroup (Equiv.Perm X)) (r : P) :
    (MulAction.toPermHom (cyclicNormalizer P r)
        (cyclicComplement X P r)).range ≤
      Subgroup.normalizer
        (Subgroup.zpowers (complementPerm X P r) :
          Set (Equiv.Perm (cyclicComplement X P r))) := by
  let N := cyclicNormalizer P r
  let SN : Subgroup N := cyclicInNormalizer P r
  let FC := cyclicComplement X P r
  let rN : N := generatorInNormalizer P r
  let τ : N →* Equiv.Perm FC :=
    MulAction.toPermHom N FC
  let g : Equiv.Perm FC := complementPerm X P r
  have hSN : SN = Subgroup.zpowers rN := by
    simpa only [N, SN, rN] using
      cyclicInNormalizer_eq_zpowers_generator P r
  have hmap : SN.map τ = Subgroup.zpowers g := by
    calc
      SN.map τ = (Subgroup.zpowers rN).map τ := by
        rw [hSN]
      _ = Subgroup.zpowers (τ rN) :=
        MonoidHom.map_zpowers τ rN
      _ = Subgroup.zpowers g := by rfl
  apply Subgroup.le_normalizer_iff.mpr
  intro q hq z hz
  obtain ⟨n, rfl⟩ := hq
  rw [← hmap] at hz ⊢
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨n * s * n⁻¹, ?_, ?_⟩
  · exact
      (inferInstance : SN.Normal).conj_mem s hs n
  · change τ (n * s * n⁻¹) = τ n * τ s * (τ n)⁻¹
    simp

theorem alternatingGroup_le_of_prime_cyclic_fixed_action_cycle_count
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (r : P) {p : ℕ}
    [Fintype (cyclicFixedPoints X P r)]
    [Fintype (cyclicComplement X P r)]
    (hp : p.Prime) (horder : orderOf r = p)
    (hfive :
      5 ≤ Fintype.card (cyclicFixedPoints X P r))
    (hAlt :
      alternatingGroup (cyclicFixedPoints X P r) ≤
        (MulAction.toPermHom (cyclicNormalizer P r)
          (cyclicFixedPoints X P r)).range)
    (hcycles :
      (complementPerm X P r).cycleType.card <
        Fintype.card (cyclicFixedPoints X P r)) :
    alternatingGroup X ≤ P := by
  exact
    FiveTransitive.SolvableOrbitGoursat.alternatingGroup_le_of_prime_cyclic_complement_cycle_count
        X P hdegree h5
        (cyclicNormalizer P r)
        (cyclicFixedPoints X P r)
        (cyclicComplement X P r)
        rfl hfive hp
        (orderOf_complementPerm X P r hp horder)
        (complementPerm_fixedPointFree X P r)
        (complement_range_le_normalizer_zpowers X P r)
        hAlt hcycles

end FiveTransitive.PrimeCyclicFixedAction

end CFSG
