module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.I.theorem_18_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Schur–Zassenhaus complement conjugacy support

The complement-conjugacy machinery used by Statement 1.1 (Thompson lemma,
Bender [1] p. 164) and its T1 invariant-coset-lifting step (KS 8.2.1).

The unrestricted theorem `complements_conjugate_of_coprime` (Gorenstein
6.2.4 / KS 6.2.1) wraps the axiom-free validation oracle
`BenderSuzuki.External.huppert_I_18_3_complements_conjugate` (Huppert I.18.3,
itself the classical minimal-normal proof closed by Feit–Thompson on the odd
side).  The classical-route helpers from the sz-conjugacy verdict
(`map_complement_quotient`, `quotient_coprime_of_coprime`,
`map_mk'_map_conj_eq`, `lift_conj_eq_of_map_eq`, `complements_of_M_inside_join`)
are NOT needed: the oracle route avoids the solvable-normal/solvable-quotient
induction entirely.  `exists_mem_normal_conjugator` (the ambient-to-`N`
adjustment) is proved locally and is the piece that upgrades the oracle's
ambient conjugator to the normal-complement conjugator used by the
semidirect-product argument of T1.  `invariant_right_coset_has_fixed_representative_of_pgroup`
is the KS 8.2.1 invariant-coset-lifting lemma in the p-group-operator case
(the case used by Statement 1.1, where the operator is the `p`-group `P`):
the invariant coset `U·g` carries a fixed representative, by the p-group
fixed-point theorem on the invariant set `U·g` (order coprime to `p`).
-/


open scoped Pointwise

namespace CFSG.GorensteinWalter

namespace SchurZassenhaus

/-- Any ambient conjugator can be adjusted into the normal complement `N`. -/
public theorem exists_mem_normal_conjugator
    {G : Type*} [Group G] [Finite G]
    {N H K : Subgroup G} [N.Normal]
    (hH : N.IsComplement' H)
    {g : G} (hg : K = H.map (MulAut.conj g).toMonoidHom) :
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  have hgmem : g ∈ (N : Set G) * (H : Set G) := by
    have : g ∈ (N ⊔ H : Subgroup G) := by
      rw [hH.sup_eq_top]
      trivial
    change g ∈ (↑(N ⊔ H) : Set G) at this
    rwa [Subgroup.normal_mul N H] at this
  rcases (Set.mem_mul.mp hgmem) with ⟨n, hn, h, hh, hnmh⟩
  refine ⟨⟨n, hn⟩, ?_⟩
  rw [hg, ← hnmh]
  exact map_conj_mul_right_eq_of_mem_normalizer n ⟨h, Subgroup.le_normalizer hh⟩

/-- Schur–Zassenhaus complement conjugacy: all complements of a normal Hall
subgroup are conjugate (Gorenstein 6.2.4 / KS 6.2.1, unrestricted via
Feit–Thompson). -/
public theorem complements_conjugate_of_coprime
    {G : Type*} [Group G] [Finite G]
    (N H K : Subgroup G) :
    N.Normal → N.IsComplement' H → N.IsComplement' K →
      Nat.Coprime (Nat.card N) N.index →
      ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  intro hN hH hK hcop
  let : N.Normal := hN
  have hcopQ : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)) := by
    simpa [Subgroup.index_eq_card] using hcop
  exact BenderSuzuki.External.huppert_I_18_3_complements_conjugate N H K hcopQ hH hK

/-- The stronger form: the conjugator can be chosen inside the normal
complement `N`. -/
public theorem exists_mem_normal_conjugator_of_coprime
    {G : Type*} [Group G] [Finite G]
    (N H K : Subgroup G) :
    N.Normal → N.IsComplement' H → N.IsComplement' K →
      Nat.Coprime (Nat.card N) N.index →
      ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  intro hN hH hK hcop
  let : N.Normal := hN
  rcases (complements_conjugate_of_coprime N H K hN hH hK hcop) with ⟨g, hg⟩
  exact exists_mem_normal_conjugator hH hg

private lemma mem_coset_of_mul {G : Type*} [Group G] (U : Subgroup G) (g : G) (u : U) :
    (u : G) * g ∈ (U : Set G) * ({g} : Set G) := by
  rw [Set.mem_mul]
  exact ⟨u, u.2, g, rfl, rfl⟩

-- p-group special case of T1 (KS 8.2.1): the invariant coset U·g contains a
-- fixed representative.
theorem invariant_right_coset_has_fixed_representative_of_pgroup
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    {p : ℕ} [Fact (Nat.Prime p)] (hA : IsPGroup p A)
    (hcop : Nat.Coprime p (Nat.card G))
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) (g : G)
    (hcoset : ∀ a : A,
      a • ((U : Set G) * ({g} : Set G)) = (U : Set G) * ({g} : Set G)) :
    ∃ c : G, c ∈ MulAction.fixedPoints A G ∧
      (U : Set G) * ({g} : Set G) = (U : Set G) * ({c} : Set G) := by
  let s : SubMulAction A G := {
    carrier := (U : Set G) * ({g} : Set G),
    smul_mem' := by
      intro a x hx
      rw [← hcoset a]
      exact (Set.mem_smul_set.mpr ⟨x, hx, rfl⟩) }
  have hcard : Nat.card s = Nat.card U := by
    refine Nat.card_congr ((Equiv.ofBijective
      (fun u : U => ⟨(u : G) * g, mem_coset_of_mul U g u⟩) ?_).symm)
    constructor
    · intro u v huv
      apply Subtype.ext
      exact mul_right_cancel (Subtype.ext_iff.mp huv)
    · intro x
      rcases (Set.mem_mul.mp x.2) with ⟨u, hu, h, hh, hx⟩
      have hhg : h = g := hh
      refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
      rw [← hx, hhg]
  have hpc : ¬ p ∣ Nat.card s := by
    rw [hcard]
    intro hpU
    have hdvd : Nat.card U ∣ Nat.card G := by
      simpa [Subgroup.card_top] using (Subgroup.card_dvd_of_le (le_top : U ≤ ⊤))
    have hcopU : Nat.Coprime p (Nat.card U) :=
      (Nat.Coprime.of_dvd_left (a₁ := Nat.card U) (a₂ := Nat.card G) (b := p) hdvd hcop.symm).symm
    have hp' : Nat.Prime p := Fact.out
    exact (Nat.Prime.ne_one hp') (Nat.Coprime.eq_one_of_dvd hcopU hpU)
  rcases (IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hA s hpc) with ⟨c, hc⟩
  refine ⟨c.1, ?_, ?_⟩
  · rw [MulAction.mem_fixedPoints]
    intro a
    have hc' : a • c = c := MulAction.mem_fixedPoints.mp hc a
    exact Subtype.ext_iff.mp hc'
  · -- (U : Set G) * ({g} : Set G) = (U : Set G) * ({c.1} : Set G) — c.1 = u·g
    rcases (Set.mem_mul.mp c.2) with ⟨u, hu, h, hh, hx⟩
    have hhg : h = g := hh
    ext x
    rw [Set.mem_mul, Set.mem_mul, ← hx, hhg]
    constructor
    · rintro ⟨u', hu', h2, hh2, hx2⟩
      -- x = u' * h2 with h2 ∈ {g} — h2 = g — so x = u'·g = (u'·u⁻¹)·(u·g)
      refine ⟨u' * u⁻¹, Subgroup.mul_mem U hu' (Subgroup.inv_mem U hu), u * g, ?_, ?_⟩
      · exact rfl
      · rw [← hx2, ← hh2]
        group
    · rintro ⟨u', hu', h2, hh2, hx2⟩
      -- x = u' * h2 with h2 ∈ {u·g} — h2 = u·g — so x = u'·u·g
      refine ⟨u' * u, Subgroup.mul_mem U hu' hu, g, rfl, ?_⟩
      rw [← hx2, hh2]
      group
private lemma semidirect_conj_inl_by_inr_coords {G A : Type*} [Group G] [Group A]
    (φ : A →* MulAut G) (g : G) (a : A) :
    (SemidirectProduct.inl (φ := φ) g * SemidirectProduct.inr (φ := φ) a *
      (SemidirectProduct.inl (φ := φ) g)⁻¹) =
    SemidirectProduct.inl (φ := φ) (g * φ a g⁻¹) * SemidirectProduct.inr (φ := φ) a := by
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.inv_right,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    SemidirectProduct.left_inr, SemidirectProduct.right_inr]

-- the coset condition gives g * φ a g⁻¹ ∈ U
private lemma coset_condition_mem {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (U : Subgroup G) (g : G)
    (hcoset : ∀ a : A,
      a • ((U : Set G) * ({g} : Set G)) = (U : Set G) * ({g} : Set G))
    (a : A) : g * (MulDistribMulAction.toMulAut A G a) g⁻¹ ∈ U := by
  -- a • g ∈ U·g — from hcoset
  have hag : a • g ∈ (U : Set G) * ({g} : Set G) := by
    rw [← hcoset a]
    exact (Set.mem_smul_set.mpr ⟨g, by
      rw [Set.mem_mul]
      exact ⟨1, U.one_mem, g, rfl, one_mul g⟩, rfl⟩)
  rcases (Set.mem_mul.mp hag) with ⟨u, hu, h, hh, hx⟩
  -- a • g = u * g — h = g
  have hhg : h = g := hh
  -- g * (a • g)⁻¹ = u⁻¹ ∈ U
  have hginv : g * (a • g)⁻¹ = u⁻¹ := by
    rw [← hx, ← hhg]
    group
  -- φ a g⁻¹ = (a • g)⁻¹
  have hphi : MulDistribMulAction.toMulAut A G a g⁻¹ = (a • g)⁻¹ := by
    exact (MulDistribMulAction.toMulAut A G a).map_inv g
  rw [hphi, hginv]
  exact Subgroup.inv_mem U hu
private lemma acopy_le_normalizer_ucopy {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
    Acopy ≤ Subgroup.normalizer (Ucopy : Set (G ⋊[φ] A)) := by
  intro φ Ucopy Acopy x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rcases (Subgroup.mem_map.mp hx) with ⟨a, ha, rfl⟩
    rcases (Subgroup.mem_map.mp hy) with ⟨u, hu, rfl⟩
    rw [← map_inv (SemidirectProduct.inr (φ := φ))]
    rw [← SemidirectProduct.inl_aut]
    rw [Subgroup.mem_map]
    exact ⟨φ a u, hU a ⟨u, hu⟩, rfl⟩
  · intro hxy
    rcases (Subgroup.mem_map.mp hx) with ⟨a, ha, rfl⟩
    rcases (Subgroup.mem_map.mp hxy) with ⟨u, hu, hul⟩
    have hyeq : y = (SemidirectProduct.inr (φ := φ) a)⁻¹ * SemidirectProduct.inl (φ := φ) u *
        SemidirectProduct.inr (φ := φ) a := by
      rw [hul]
      group
    rw [hyeq]
    rw [← map_inv (SemidirectProduct.inr (φ := φ))]
    rw [← SemidirectProduct.inl_aut_inv]
    rw [Subgroup.mem_map]
    exact ⟨φ a⁻¹ u, hU a⁻¹ ⟨u, hu⟩, rfl⟩

-- sub-goal 2: the U-copy is normal in AU
private lemma ucopy_normal_in_AU {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
    (Ucopy.subgroupOf (Ucopy ⊔ Acopy)).Normal := by
  intro φ Ucopy Acopy
  rw [Subgroup.normal_subgroupOf_iff le_sup_left]
  intro h k hh hk
  have hk' : k ∈ Subgroup.normalizer (Ucopy : Set (G ⋊[φ] A)) := by
    exact (sup_le_iff.mpr ⟨Subgroup.le_normalizer, acopy_le_normalizer_ucopy U hU⟩) hk
  exact (Subgroup.mem_normalizer_iff.mp hk') h |>.1 hh
private lemma conjugated_Acopy_le_AU {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (U : Subgroup G) (g : G)
    (hcoset : ∀ a : A,
      a • ((U : Set G) * ({g} : Set G)) = (U : Set G) * ({g} : Set G)) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
    (Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom) ≤ Ucopy ⊔ Acopy := by
  intro φ Ucopy Acopy x hx
  rcases (Subgroup.mem_map.mp hx) with ⟨y, hy, hxy⟩
  rcases (Subgroup.mem_map.mp hy) with ⟨a, ha, rfl⟩
  -- hxy : (MulAut.conj (inl g)) (inr a) = x — the element: (inl g) * (inr a) * (inl g)⁻¹
  -- the coords: = inl (g * φ a g⁻¹) * inr a
  rw [← hxy]
  -- the goal: conj (inl g) (inr a) ∈ Ucopy ⊔ Acopy
  -- = inl (g φ a g⁻¹) * inr a — via the coords lemma
  have hcoords : MulAut.conj (SemidirectProduct.inl (φ := φ) g) (SemidirectProduct.inr (φ := φ) a) =
      SemidirectProduct.inl (φ := φ) (g * φ a g⁻¹) * SemidirectProduct.inr (φ := φ) a := by
    ext <;> simp [MulAut.conj, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr]
  change (MulAut.conj (SemidirectProduct.inl (φ := φ) g)) (SemidirectProduct.inr (φ := φ) a) ∈ Ucopy ⊔ Acopy
  rw [hcoords]
  -- the product ∈ AU — inl (g φ a g⁻¹) ∈ Ucopy ≤ AU, inr a ∈ Acopy ≤ AU
  have hmem1 : SemidirectProduct.inl (φ := φ) (g * φ a g⁻¹) ∈ Ucopy := by
    rw [Subgroup.mem_map]
    -- coset_condition_mem (inlined): hcoset ⇒ g * φ a g⁻¹ ∈ U
    have hag : a • g ∈ (U : Set G) * ({g} : Set G) := by
      rw [← hcoset a]
      exact (Set.mem_smul_set.mpr ⟨g, by
        rw [Set.mem_mul]
        exact ⟨1, U.one_mem, g, rfl, one_mul g⟩, rfl⟩)
    rcases (Set.mem_mul.mp hag) with ⟨u, hu, h, hh, hx⟩
    have hhg : h = g := hh
    have hginv : g * (a • g)⁻¹ = u⁻¹ := by
      rw [← hx, ← hhg]
      group
    have hphi : φ a g⁻¹ = (a • g)⁻¹ := by
      exact (MulDistribMulAction.toMulAut A G a).map_inv g
    rw [hphi, hginv]
    exact ⟨u⁻¹, Subgroup.inv_mem U hu, rfl⟩
  have hmem2 : SemidirectProduct.inr (φ := φ) a ∈ Acopy := by
    rw [Subgroup.mem_map]
    exact ⟨a, trivial, rfl⟩
  exact (Subgroup.mul_mem (Ucopy ⊔ Acopy)
    ((le_sup_left : Ucopy ≤ Ucopy ⊔ Acopy) hmem1)
    ((le_sup_right : Acopy ≤ Ucopy ⊔ Acopy) hmem2))
-- the action of A on U, restricted from the action on G
private def restrictedAction {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) : A →* MulAut (↥U) where
  toFun a :=
    { toFun := fun u => ⟨a • (u : G), hU a u⟩
      invFun := fun u => ⟨a⁻¹ • (u : G), hU a⁻¹ u⟩
      left_inv := by
        intro u
        apply Subtype.ext
        change a⁻¹ • (a • (u : G)) = (u : G)
        rw [← mul_smul, show a⁻¹ * a = 1 by group]
        simp
      right_inv := by
        intro u
        apply Subtype.ext
        change a • (a⁻¹ • (u : G)) = (u : G)
        rw [← mul_smul, show a * a⁻¹ = 1 by group]
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact MulDistribMulAction.smul_mul a (x : G) (y : G) }
  map_one' := by
    ext u
    change (1 : A) • (u : G) = (u : G)
    simp
  map_mul' := by
    intro a b
    ext u
    change (a * b) • (u : G) = a • (b • (u : G))
    exact mul_smul a b (u : G)


-- the compatibility: the restricted action commutes with the inclusion
private lemma restrictedAction_compat {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    ∀ a : A, (U.subtype.comp (MulEquiv.toMonoidHom (restrictedAction U hU a))) =
      (MulEquiv.toMonoidHom (MulDistribMulAction.toMulAut A G a)).comp U.subtype := by
  intro a
  ext u
  rfl

-- the embedding of U ⋊ A into S
private def embedSemidirectU {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    (↥U ⋊[restrictedAction U hU] A) →* (G ⋊[MulDistribMulAction.toMulAut A G] A) :=
  SemidirectProduct.map U.subtype (MonoidHom.id A) (restrictedAction_compat U hU)


-- the normal form: the left coordinate of every AU element lies in U
private lemma AU_left_mem_U {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
    ∀ x : ↥AU, x.1.left ∈ U := by
  intro φ AU x
  rcases (MonoidHom.mem_range.mp x.2) with ⟨y, hy⟩
  have : (embedSemidirectU U hU y).left ∈ U := by
    change (SemidirectProduct.map U.subtype (MonoidHom.id A) (restrictedAction_compat U hU) y).left ∈ U
    rw [SemidirectProduct.map_left]
    exact y.left.2
  simpa [← hy] using this

-- every element of AU is inl u · inr a with u ∈ U (the decomposition)
private lemma AU_mem_decomp {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
    ∀ x : ↥AU,
      x.1 = SemidirectProduct.inl (φ := φ) (x.1.left) * SemidirectProduct.inr (φ := φ) (x.1.right) ∧
      x.1.left ∈ U := by
  intro φ AU x
  constructor
  · exact (SemidirectProduct.inl_left_mul_inr_right x.1).symm
  · exact AU_left_mem_U U hU x


-- the U-copy and the A-copy are disjoint in S
private lemma disjoint_Ucopy_Acopy {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G]
    (U : Subgroup G) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
    Disjoint Ucopy Acopy := by
  intro φ Ucopy Acopy
  rw [Subgroup.disjoint_def]
  intro x hxU hxA
  rcases ((Subgroup.mem_map (K := U) (f := SemidirectProduct.inl (φ := φ))).mp hxU) with ⟨u, hu, rfl⟩
  rcases ((Subgroup.mem_map (K := ⊤) (f := SemidirectProduct.inr (φ := φ))).mp hxA) with ⟨a, ha, hx⟩
  have hu1 : u = 1 := by
    have : (SemidirectProduct.inl (φ := φ) u).left = (SemidirectProduct.inr (φ := φ) a).left := by
      rw [hx]
    simpa [SemidirectProduct.left_inl, SemidirectProduct.left_inr] using this
  rw [hu1]
  simp


-- the complement structure in ↥AU: the U-copy and the A-copy
private lemma complement_structure {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
    let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
    (Ucopy.subgroupOf AU).IsComplement' (Acopy.subgroupOf AU) := by
  intro φ Ucopy Acopy AU
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxU hxA
    apply Subtype.ext
    change x.1 = 1
    have hxU' : x.1 ∈ Ucopy := Subgroup.mem_subgroupOf.mp hxU
    have hxA' : x.1 ∈ Acopy := Subgroup.mem_subgroupOf.mp hxA
    rcases ((Subgroup.mem_map (K := U) (f := SemidirectProduct.inl (φ := φ))).mp hxU') with ⟨u, hu, hux⟩
    rcases ((Subgroup.mem_map (K := ⊤) (f := SemidirectProduct.inr (φ := φ))).mp hxA') with ⟨a, ha, hx⟩
    have hu1 : u = 1 := by
      have : (SemidirectProduct.inl (φ := φ) u).left = (SemidirectProduct.inr (φ := φ) a).left := by
        rw [hux, hx]
      simpa [SemidirectProduct.left_inl, SemidirectProduct.left_inr] using this
    rw [← hux, hu1]
    simp
  · ext x
    constructor
    · intro hx
      trivial
    · intro hx
      rw [Set.mem_mul]
      rcases (AU_mem_decomp U hU x) with ⟨hdecomp, hleft⟩
      have hinlAU : SemidirectProduct.inl (φ := φ) (x.1.left : G) ∈ AU := by
        exact (MonoidHom.mem_range.mpr
          ⟨SemidirectProduct.inl (φ := restrictedAction U hU) ⟨x.1.left, hleft⟩, by
            simp [embedSemidirectU, SemidirectProduct.map_inl]⟩)
      have hinrAU : SemidirectProduct.inr (φ := φ) (x.1.right : A) ∈ AU := by
        exact (MonoidHom.mem_range.mpr
          ⟨SemidirectProduct.inr (φ := restrictedAction U hU) x.1.right, by
            simp [embedSemidirectU, SemidirectProduct.map_inr]⟩)
      refine ⟨⟨SemidirectProduct.inl (φ := φ) (x.1.left : G), hinlAU⟩, ?_,
        ⟨SemidirectProduct.inr (φ := φ) (x.1.right : A), hinrAU⟩, ?_, ?_⟩
      · change ⟨SemidirectProduct.inl (φ := φ) (x.1.left : G), hinlAU⟩ ∈ Ucopy.subgroupOf AU
        rw [Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_map (K := U) (f := SemidirectProduct.inl (φ := φ))).mpr
          ⟨x.1.left, hleft, rfl⟩
      · change ⟨SemidirectProduct.inr (φ := φ) (x.1.right : A), hinrAU⟩ ∈ Acopy.subgroupOf AU
        rw [Subgroup.mem_subgroupOf]
        change (SemidirectProduct.inr (φ := φ) (x.1.right : A) : G ⋊[φ] A) ∈ Acopy
        rw [Subgroup.mem_map]
        exact ⟨x.1.right, trivial, rfl⟩
      · apply Subtype.ext
        exact hdecomp.symm

-- the U-copy is contained in AU
private lemma ucopy_le_AU {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
    Ucopy ≤ AU := by
  intro φ Ucopy AU x hx
  rcases (Subgroup.mem_map.mp hx) with ⟨u, hu, rfl⟩
  exact (MonoidHom.mem_range.mpr ⟨SemidirectProduct.inl (φ := restrictedAction U hU) ⟨u, hu⟩, by
    simp [embedSemidirectU, SemidirectProduct.map_inl]⟩)

-- the A-copy is contained in AU
private lemma acopy_le_AU {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
    let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
    Acopy ≤ AU := by
  intro φ Acopy AU x hx
  rcases (Subgroup.mem_map.mp hx) with ⟨a, ha, rfl⟩
  exact (MonoidHom.mem_range.mpr ⟨SemidirectProduct.inr (φ := restrictedAction U hU) a, by
    simp [embedSemidirectU, SemidirectProduct.map_inr]⟩)

-- AU is the join of the U-copy and the A-copy
private lemma ucopy_sup_acopy_eq_AU {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
    let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
    Ucopy ⊔ Acopy = AU := by
  intro φ Ucopy Acopy AU
  apply le_antisymm
  · exact sup_le (ucopy_le_AU U hU) (acopy_le_AU U hU)
  · intro x hx
    rcases (AU_mem_decomp U hU ⟨x, hx⟩) with ⟨hdecomp, hleft⟩
    have h1 : SemidirectProduct.inl (φ := φ) x.left ∈ Ucopy := by
      rw [Subgroup.mem_map]
      exact ⟨x.left, hleft, rfl⟩
    have h2 : SemidirectProduct.inr (φ := φ) x.right ∈ Acopy := by
      rw [Subgroup.mem_map]
      exact ⟨x.right, trivial, rfl⟩
    change (⟨x, hx⟩ : ↥AU).1 ∈ Ucopy ⊔ Acopy
    rw [hdecomp]
    exact Subgroup.mul_mem (Ucopy ⊔ Acopy)
      ((le_sup_left : Ucopy ≤ Ucopy ⊔ Acopy) h1)
      ((le_sup_right : Acopy ≤ Ucopy ⊔ Acopy) h2)

-- the image of `H.subgroupOf K` under the inclusion of K is H (when H ≤ K)
private lemma map_subtype_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) (hHK : H ≤ K) :
    (H.subgroupOf K).map K.subtype = H := by
  apply le_antisymm
  · intro x hx
    rcases (Subgroup.mem_map.mp hx) with ⟨y, hy, hyx⟩
    rw [← hyx]
    exact Subgroup.mem_subgroupOf.mp hy
  · intro x hx
    rw [Subgroup.mem_map]
    exact ⟨⟨x, hHK hx⟩, by
      rw [Subgroup.mem_subgroupOf]
      exact hx, rfl⟩

-- sub-goal 5: the index of the U-copy in AU is |A|, via the right projection
private lemma ucopy_index_eq_card_A {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
    (Ucopy.subgroupOf AU).index = Nat.card A := by
  intro φ Ucopy AU
  let ψ : ↥AU →* A := SemidirectProduct.rightHom.comp (AU.subtype)
  have hker : ψ.ker = Ucopy.subgroupOf AU := by
    apply le_antisymm
    · intro x hx
      simp [ψ] at hx
      rcases (AU_mem_decomp U hU x) with ⟨hdecomp, hleft⟩
      rw [hdecomp] at hx
      have ha1 : x.1.right = 1 := by
        simpa [SemidirectProduct.rightHom_inl, SemidirectProduct.rightHom_inr] using hx
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_map]
      refine ⟨x.1.left, hleft, ?_⟩
      rw [hdecomp, ha1]
      simp
    · intro x hx
      rw [MonoidHom.mem_ker]
      rw [Subgroup.mem_subgroupOf] at hx
      rcases ((Subgroup.mem_map (K := U) (f := SemidirectProduct.inl (φ := φ))).mp hx) with ⟨u, hu, hux⟩
      simp [ψ, ← hux]
  have hsurj : Function.Surjective ψ := by
    intro a
    refine ⟨⟨SemidirectProduct.inr (φ := φ) a, ?_⟩, ?_⟩
    · exact (MonoidHom.mem_range.mpr ⟨SemidirectProduct.inr (φ := restrictedAction U hU) a, by
        simp [embedSemidirectU, SemidirectProduct.map_inr]⟩)
    · simp [ψ]
  have hcard : Nat.card ((↥AU) ⧸ (Ucopy.subgroupOf AU)) = Nat.card A := by
    rw [← hker]
    have hq : (↥AU) ⧸ ψ.ker ≃* ψ.range := QuotientGroup.quotientKerEquivRange ψ
    have hrange : ψ.range = (⊤ : Subgroup A) := MonoidHom.range_eq_top_of_surjective ψ hsurj
    have htop : Nat.card (↥ψ.range) = Nat.card A := by
      rw [hrange]
      exact Nat.card_congr (Subgroup.topEquiv.toEquiv)
    exact (Nat.card_congr hq.toEquiv).trans htop
  rw [Subgroup.index_eq_card]
  exact hcard

-- the cardinality of the U-copy inside AU is |U|
private lemma card_ucopy_subgroupOf_eq_card_U {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
    Nat.card (↥(Ucopy.subgroupOf AU)) = Nat.card U := by
  intro φ Ucopy AU
  have hbiject : U ≃ ↥(Ucopy.subgroupOf AU) := by
    refine Equiv.ofBijective
      (fun u : U => ⟨⟨SemidirectProduct.inl (φ := φ) (u : G), ucopy_le_AU U hU (by
        rw [Subgroup.mem_map]
        exact ⟨u, u.2, rfl⟩)⟩, by
          rw [Subgroup.mem_subgroupOf]
          rw [Subgroup.mem_map]
          exact ⟨u, u.2, rfl⟩⟩) ?_
    constructor
    · intro u v huv
      apply Subtype.ext
      have hval : SemidirectProduct.inl (φ := φ) (u : G) = SemidirectProduct.inl (φ := φ) (v : G) :=
        Subtype.ext_iff.mp (Subtype.ext_iff.mp huv)
      have hleft : (u : G) = (v : G) := by
        have : (SemidirectProduct.inl (φ := φ) (u : G)).left =
            (SemidirectProduct.inl (φ := φ) (v : G)).left := by rw [hval]
        simpa [SemidirectProduct.left_inl] using this
      exact hleft
    · intro x
      rcases ((Subgroup.mem_map (K := U) (f := SemidirectProduct.inl (φ := φ))).mp
        (Subgroup.mem_subgroupOf.mp x.2)) with ⟨u, hu, hux⟩
      refine ⟨⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hux
  exact (Nat.card_congr hbiject).symm

-- sub-goal 4b: the conjugated A-copy is a complement of the U-copy in AU
private lemma conjugated_Acopy_is_complement {G A : Type*} [Group G] [Finite G]
    [Group A] [Finite A] [MulDistribMulAction A G]
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) (g : G)
    (hcoset : ∀ a : A,
      a • ((U : Set G) * ({g} : Set G)) = (U : Set G) * ({g} : Set G)) :
    let φ := MulDistribMulAction.toMulAut A G
    let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
    let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
    let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
    let A₁ : Subgroup (↥AU) :=
      (Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom).subgroupOf AU
    (Ucopy.subgroupOf AU).IsComplement' A₁ := by
  intro φ Ucopy Acopy AU A₁
  have hAU : Ucopy ⊔ Acopy = AU := ucopy_sup_acopy_eq_AU U hU
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxU hxA
    apply Subtype.ext
    change x.1 = 1
    have hxU' : x.1 ∈ Ucopy := Subgroup.mem_subgroupOf.mp hxU
    have hxA' : x.1 ∈ Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom :=
      Subgroup.mem_subgroupOf.mp hxA
    rcases ((Subgroup.mem_map (K := U) (f := SemidirectProduct.inl (φ := φ))).mp hxU')
      with ⟨u, hu, hux⟩
    rcases ((Subgroup.mem_map (K := Acopy)
      (f := (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom)).mp hxA')
      with ⟨y, hy, hxy⟩
    rcases ((Subgroup.mem_map (K := ⊤) (f := SemidirectProduct.inr (φ := φ))).mp hy)
      with ⟨a, ha, hya⟩
    have hright : (SemidirectProduct.inl (φ := φ) u).right =
        (MulAut.conj (SemidirectProduct.inl (φ := φ) g) (SemidirectProduct.inr (φ := φ) a)).right := by
      rw [hux, ← hxy, ← hya]
      simp
    have ha1 : a = 1 := by
      simpa [MulAut.conj, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
        SemidirectProduct.right_inl, SemidirectProduct.right_inr] using hright.symm
    rw [← hxy, ← hya, ha1]
    simp
  · rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_mul]
    rcases (AU_mem_decomp U hU x) with ⟨hdecomp, hleft⟩
    let a : A := x.1.right
    have hcos : g * φ a g⁻¹ ∈ U := coset_condition_mem U g hcoset a
    have hinl_uu' : SemidirectProduct.inl (φ := φ) (x.1.left * (g * φ a g⁻¹)⁻¹) ∈ AU := by
      exact (ucopy_le_AU U hU) (by
        rw [Subgroup.mem_map]
        exact ⟨x.1.left * (g * φ a g⁻¹)⁻¹,
          Subgroup.mul_mem U hleft (Subgroup.inv_mem U hcos), rfl⟩)
    have hconj : MulAut.conj (SemidirectProduct.inl (φ := φ) g) (SemidirectProduct.inr (φ := φ) a) ∈ AU := by
      have hmem2 : MulAut.conj (SemidirectProduct.inl (φ := φ) g) (SemidirectProduct.inr (φ := φ) a) ∈
          Ucopy ⊔ Acopy := (conjugated_Acopy_le_AU U g hcoset) (by
            rw [Subgroup.mem_map]
            exact ⟨SemidirectProduct.inr (φ := φ) a, by
              rw [Subgroup.mem_map]
              exact ⟨a, trivial, rfl⟩, rfl⟩)
      rw [hAU] at hmem2
      exact hmem2
    refine ⟨⟨SemidirectProduct.inl (φ := φ) (x.1.left * (g * φ a g⁻¹)⁻¹), hinl_uu'⟩, ?_,
      ⟨MulAut.conj (SemidirectProduct.inl (φ := φ) g) (SemidirectProduct.inr (φ := φ) a), hconj⟩, ?_, ?_⟩
    · change ⟨SemidirectProduct.inl (φ := φ) (x.1.left * (g * φ a g⁻¹)⁻¹), hinl_uu'⟩ ∈ Ucopy.subgroupOf AU
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_map]
      exact ⟨x.1.left * (g * φ a g⁻¹)⁻¹,
        Subgroup.mul_mem U hleft (Subgroup.inv_mem U hcos), rfl⟩
    · change ⟨MulAut.conj (SemidirectProduct.inl (φ := φ) g) (SemidirectProduct.inr (φ := φ) a), hconj⟩ ∈ A₁
      rw [Subgroup.mem_subgroupOf]
      change MulAut.conj (SemidirectProduct.inl (φ := φ) g) (SemidirectProduct.inr (φ := φ) a) ∈
        Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom
      rw [Subgroup.mem_map]
      exact ⟨SemidirectProduct.inr (φ := φ) a, by
        rw [Subgroup.mem_map]
        exact ⟨a, trivial, rfl⟩, rfl⟩
    · apply Subtype.ext
      have hcoords : MulAut.conj (SemidirectProduct.inl (φ := φ) g) (SemidirectProduct.inr (φ := φ) a) =
          SemidirectProduct.inl (φ := φ) (g * φ a g⁻¹) * SemidirectProduct.inr (φ := φ) a := by
        ext <;> simp [MulAut.conj, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
          SemidirectProduct.inv_left, SemidirectProduct.inv_right,
          SemidirectProduct.left_inl, SemidirectProduct.right_inl,
          SemidirectProduct.left_inr, SemidirectProduct.right_inr]
      simp only [Subgroup.coe_mul]
      rw [hdecomp, hcoords]
      simp [a, mul_assoc]

-- a conjugate of the A-copy equal to the A-copy means the conjugating element is fixed
private lemma fixed_of_conj_acopy {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (x : G) :
    let φ := MulDistribMulAction.toMulAut A G
    let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
    Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) x)).toMonoidHom = Acopy →
      x ∈ MulAction.fixedPoints A G := by
  intro φ Acopy hmap
  rw [MulAction.mem_fixedPoints]
  intro a
  have hmem : MulAut.conj (SemidirectProduct.inl (φ := φ) x) (SemidirectProduct.inr (φ := φ) a) ∈ Acopy := by
    rw [← hmap]
    rw [Subgroup.mem_map]
    exact ⟨SemidirectProduct.inr (φ := φ) a, by
      rw [Subgroup.mem_map]
      exact ⟨a, trivial, rfl⟩, rfl⟩
  have hcoords : MulAut.conj (SemidirectProduct.inl (φ := φ) x) (SemidirectProduct.inr (φ := φ) a) =
      SemidirectProduct.inl (φ := φ) (x * φ a x⁻¹) * SemidirectProduct.inr (φ := φ) a := by
    ext <;> simp [MulAut.conj, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr]
  rw [hcoords] at hmem
  rcases (Subgroup.mem_map.mp hmem) with ⟨b, hb, hb₂⟩
  have hleft : x * φ a x⁻¹ = 1 := by
    have hlb : (SemidirectProduct.inl (φ := φ) (x * φ a x⁻¹) * SemidirectProduct.inr (φ := φ) a).left =
        (SemidirectProduct.inr (φ := φ) b).left := by rw [hb₂]
    simpa [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr] using hlb
  have hphix : φ a x = x := by
    have h₂ : x * (φ a x)⁻¹ = x * x⁻¹ := by
      rw [(φ a).map_inv x] at hleft
      rw [hleft]
      simp
    exact inv_injective (mul_left_cancel h₂)
  change a • x = x
  simpa [φ, MulDistribMulAction.toMulAut_apply] using hphix

-- sub-goal 6 + assembly: T1 in the general coprime case (KS 8.2.1 via
-- Schur–Zassenhaus complement conjugacy in the semidirect-product subgroup AU)
theorem invariant_right_coset_has_fixed_representative
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G))
    (U : Subgroup G) (hU : ∀ a : A, ∀ u : U, a • (u : G) ∈ U) (g : G)
    (hcoset : ∀ a : A,
      a • ((U : Set G) * ({g} : Set G)) = (U : Set G) * ({g} : Set G)) :
    ∃ c : G, c ∈ MulAction.fixedPoints A G ∧
      (U : Set G) * ({g} : Set G) = (U : Set G) * ({c} : Set G) := by
  let φ := MulDistribMulAction.toMulAut A G
  let Ucopy : Subgroup (G ⋊[φ] A) := U.map (SemidirectProduct.inl (φ := φ))
  let Acopy : Subgroup (G ⋊[φ] A) := (⊤ : Subgroup A).map (SemidirectProduct.inr (φ := φ))
  let AU : Subgroup (G ⋊[φ] A) := (embedSemidirectU U hU).range
  let : Finite (G ⋊[φ] A) := Finite.of_injective
    (fun x : G ⋊[φ] A => (x.left, x.right)) (by
      intro x y h
      have h₁ : x.left = y.left := congrArg Prod.fst h
      have h₂ : x.right = y.right := congrArg Prod.snd h
      exact SemidirectProduct.ext h₁ h₂)
  let N : Subgroup (↥AU) := Ucopy.subgroupOf AU
  let H : Subgroup (↥AU) := Acopy.subgroupOf AU
  let A₁ : Subgroup (↥AU) :=
    (Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom).subgroupOf AU
  have hAU : Ucopy ⊔ Acopy = AU := ucopy_sup_acopy_eq_AU U hU
  have hN : N.Normal := by
    change (Ucopy.subgroupOf AU).Normal
    rw [← hAU]
    exact ucopy_normal_in_AU U hU
  have hH : N.IsComplement' H := by
    simpa [N, H] using (complement_structure U hU)
  have hA₁ : N.IsComplement' A₁ := by
    simpa [N, A₁] using (conjugated_Acopy_is_complement U hU g hcoset)
  have hcopU : Nat.Coprime (Nat.card U) (Nat.card A) := by
    have hdvd : Nat.card U ∣ Nat.card G := by
      simpa [Subgroup.card_top] using (Subgroup.card_dvd_of_le (le_top : U ≤ ⊤))
    exact Nat.Coprime.of_dvd_left (a₁ := Nat.card U) (a₂ := Nat.card G) (b := Nat.card A)
      hdvd hcop.symm
  have hcopN : Nat.Coprime (Nat.card (↥N)) N.index := by
    rw [ucopy_index_eq_card_A U hU, card_ucopy_subgroupOf_eq_card_U U hU]
    exact hcopU
  rcases (exists_mem_normal_conjugator_of_coprime N H A₁ hN hH hA₁ hcopN) with ⟨n, hn⟩
  have hnU : (n.1 : G ⋊[φ] A) ∈ Ucopy := Subgroup.mem_subgroupOf.mp n.2
  rcases ((Subgroup.mem_map (K := U) (f := SemidirectProduct.inl (φ := φ))).mp hnU)
    with ⟨v, hv, hnv⟩
  let c : G := v⁻¹ * g
  have hfixc : c ∈ MulAction.fixedPoints A G := by
    have hcompAU : AU.subtype.comp (MulAut.conj (n : ↥AU)).toMonoidHom =
        (MulAut.conj (SemidirectProduct.inl (φ := φ) v)).toMonoidHom.comp AU.subtype := by
      apply MonoidHom.ext
      intro z
      simp [MulAut.conj, ← hnv, Subgroup.coe_mul, mul_assoc]
    have hconj_eq : Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) v)).toMonoidHom =
        Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom := by
      have hlhs : A₁.map AU.subtype =
          Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom := by
        exact map_subtype_subgroupOf
          (Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom) AU (by
            intro x hx
            rw [← hAU]
            exact (conjugated_Acopy_le_AU U g hcoset) hx)
      have hrhs : (H.map (MulAut.conj (n : ↥AU)).toMonoidHom).map AU.subtype =
          Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) v)).toMonoidHom := by
        rw [Subgroup.map_map]
        rw [hcompAU]
        rw [← Subgroup.map_map]
        rw [map_subtype_subgroupOf Acopy AU (acopy_le_AU U hU)]
      rw [← hlhs, ← hrhs]
      exact congrArg (Subgroup.map AU.subtype) hn.symm
    have hconj_vg : Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) (v⁻¹ * g))).toMonoidHom =
        Acopy := by
      have hmap : (MulAut.conj (SemidirectProduct.inl (φ := φ) (v⁻¹ * g))).toMonoidHom =
          (MulAut.conj (SemidirectProduct.inl (φ := φ) v)).symm.toMonoidHom.comp
            (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom := by
        apply MonoidHom.ext
        intro x
        simp [MulAut.conj, map_inv, map_mul, mul_assoc]
      have hmap' : Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) (v⁻¹ * g))).toMonoidHom =
          (Acopy.map (MulAut.conj (SemidirectProduct.inl (φ := φ) g)).toMonoidHom).map
            (MulAut.conj (SemidirectProduct.inl (φ := φ) v)).symm.toMonoidHom := by
        rw [hmap]
        rw [← Subgroup.map_map]
      rw [hmap', ← hconj_eq]
      rw [Subgroup.map_map]
      rw [show (MulAut.conj (SemidirectProduct.inl (φ := φ) v)).symm.toMonoidHom.comp
          (MulAut.conj (SemidirectProduct.inl (φ := φ) v)).toMonoidHom = MonoidHom.id _ from by
        apply MonoidHom.ext
        intro x
        simp]
      rw [Subgroup.map_id]
    exact fixed_of_conj_acopy (v⁻¹ * g) hconj_vg
  have hcoset_eq : (U : Set G) * ({g} : Set G) = (U : Set G) * ({c} : Set G) := by
    ext x
    rw [Set.mem_mul, Set.mem_mul]
    constructor
    · rintro ⟨u', hu', h2, hh2, hx2⟩
      refine ⟨u' * v, Subgroup.mul_mem U hu' hv, c, rfl, ?_⟩
      rw [← hx2, hh2]
      simp [c, mul_assoc]
    · rintro ⟨u', hu', h2, hh2, hx2⟩
      refine ⟨u' * v⁻¹, Subgroup.mul_mem U hu' (Subgroup.inv_mem U hv), g, rfl, ?_⟩
      rw [← hx2, hh2]
      simp [c, mul_assoc]
  exact ⟨c, hfixc, hcoset_eq⟩

/-! ## Coprime-action and p-group commutator consequences -/

/-- The two coprime-action identities used repeatedly in the Thompson lemma.
This is the operator-action form of KS 8.2.7; ambient subgroup commutators are
obtained with the bridges in `FeitThompson.SubgroupConj`. -/
public theorem coprime_action_decomposition
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [MulDistribMulAction A B]
    (hsolv : IsSolvable B) (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    fixedPointSubgroup A B ⊔ commutatorAction (A := A) (G := B) = ⊤ ∧
      commutatorAction₂ (A := A) (G := B) = commutatorAction (A := A) (G := B) := by
  exact ⟨fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := B) (A := A) hsolv hcop,
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      (G := B) (A := A) hsolv hcop⟩

/-- KS 8.1.4(b), in the ambient-subgroup form used by the Thompson lemma:
if two `p`-subgroups normalize as indicated and `B` is nontrivial, then
commutation with `P` cannot generate all of `B`. -/
public theorem commutator_lt_of_pGroups
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B P : Subgroup G) (hBp : IsPGroup p B) (hPp : IsPGroup p P)
    (hPB : P ≤ Subgroup.normalizer (B : Set G)) (hBne : B ≠ ⊥) :
    ⁅B, P⁆ < B := by
  have hle : ⁅B, P⁆ ≤ B :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hPB
  refine lt_of_le_of_ne hle ?_
  intro heq
  let S : Subgroup G := B ⊔ P
  have hBnormS : (B.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (H := B) (K := S) le_sup_left).2
    exact sup_le Subgroup.le_normalizer hPB
  let : (B.subgroupOf S).Normal := hBnormS
  have hBPp : IsPGroup p S :=
    IsPGroup.to_sup_of_normal_left' hBp hPp hPB
  have hnil : Group.IsNilpotent ↑S :=
    IsPGroup.isNilpotent (p := p) hBPp
  obtain ⟨n, hn⟩ :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↑S)).mp hnil
  have hB_le_lcs :
      ∀ n : ℕ, B.subgroupOf S ≤
        (⊤ : Subgroup ↑S).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simp [Subgroup.lowerCentralSeries_zero]
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        have hcomm_sub :
            ⁅B.subgroupOf S, P.subgroupOf S⁆ = B.subgroupOf S := by
          apply (Subgroup.map_subtype_inj (H := S)).mp
          calc
            (⁅B.subgroupOf S, P.subgroupOf S⁆).map S.subtype = B := by
              rw [Subgroup.map_commutator,
                Subgroup.map_subgroupOf_eq_of_le le_sup_left,
                Subgroup.map_subgroupOf_eq_of_le le_sup_right, heq]
            _ = (B.subgroupOf S).map S.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le le_sup_left).symm
        rw [← hcomm_sub]
        exact Subgroup.commutator_mono ih le_top
  have hBsub_bot : B.subgroupOf S = ⊥ := by
    apply bot_unique
    exact (hB_le_lcs n).trans_eq hn
  apply hBne
  calc
    B = (B.subgroupOf S).map S.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le le_sup_left).symm
    _ = ⊥ := by rw [hBsub_bot]; simp

end SchurZassenhaus

end CFSG.GorensteinWalter
