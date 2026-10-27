module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RootGroups
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

@[expose, instance_reducible] def localAction (Γ : SimpleGraph V) [GraphAction H Γ] (z : V) :
    MulAction ↥(MulAction.stabilizer H z) {w : V // Γ.Adj z w} where
  smul g w := ⟨(g : H) • w.1, by
    have h := (GraphAction.adj_smul (Γ := Γ) (g : H) z w.1).mpr w.2
    rwa [MulAction.mem_stabilizer_iff.mp g.2] at h⟩
  one_smul w := Subtype.ext (one_smul H w.1)
  mul_smul g h w := Subtype.ext (mul_smul (g : H) (h : H) w.1)

@[expose] noncomputable def localPermHom (Γ : SimpleGraph V) [GraphAction H Γ] (z : V) :
    ↥(MulAction.stabilizer H z) →* Equiv.Perm {w : V // Γ.Adj z w} :=
  letI := localAction (H := H) Γ z
  MulAction.toPermHom ↥(MulAction.stabilizer H z) {w : V // Γ.Adj z w}

variable (H) in
@[expose] def socleAt (Γ : SimpleGraph V) (z : V) : Subgroup H :=
  CFSG.inSubgroup CFSG.perfectResidual (MulAction.stabilizer H z) ⊔
    fixingSubgroup H (Γ.neighborSet z)

variable (H) in
@[expose] def socTorus (Γ : SimpleGraph V) (z w y : V) : Subgroup H :=
  socleAt H Γ z ⊓ MulAction.stabilizer H w ⊓ MulAction.stabilizer H y

theorem socleAt_le_stabilizer {z : V}
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) :
    socleAt H Γ z ≤ MulAction.stabilizer H z := by
  unfold socleAt CFSG.inSubgroup
  exact sup_le (Subgroup.map_subtype_le _) hK

theorem neighborSet_smul (g : H) (x : V) :
    g • Γ.neighborSet x = Γ.neighborSet (g • x) := by
  ext w
  rw [Set.mem_smul_set_iff_inv_smul_mem, SimpleGraph.mem_neighborSet,
    SimpleGraph.mem_neighborSet]
  constructor
  · intro hw
    simpa using (GraphAction.adj_smul g x (g⁻¹ • w)).mpr hw
  · intro hw
    exact (GraphAction.adj_smul g x (g⁻¹ • w)).mp (by simpa using hw)

theorem fixingSubgroup_neighborSet_smul (g : H) (z : V) :
    fixingSubgroup H (Γ.neighborSet (g • z)) =
      (fixingSubgroup H (Γ.neighborSet z)).map (MulAut.conj g).toMonoidHom := by
  rw [← SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj
    (g := g) (s := Γ.neighborSet z), neighborSet_smul]

theorem socleAt_smul (g : H) (z : V) :
    socleAt H Γ (g • z) = (socleAt H Γ z).map (MulAut.conj g).toMonoidHom := by
  have hP : (CFSG.perfectResidual ↥(MulAction.stabilizer H z)).map
      (MulAction.stabilizerEquivStabilizer (rfl : g • z = g • z)).toMonoidHom =
      CFSG.perfectResidual ↥(MulAction.stabilizer H (g • z)) :=
    CFSG.LieType.SteinbergBR.perfectResidual_map_equiv _
  have hper : (CFSG.inSubgroup CFSG.perfectResidual (MulAction.stabilizer H z)).map
      (MulAut.conj g).toMonoidHom =
      CFSG.inSubgroup CFSG.perfectResidual (MulAction.stabilizer H (g • z)) := by
    unfold CFSG.inSubgroup
    rw [Subgroup.map_map]
    have hcomp : ((MulAut.conj g).toMonoidHom.comp
        (MulAction.stabilizer H z).subtype) =
        ((MulAction.stabilizer H (g • z)).subtype.comp
          (MulAction.stabilizerEquivStabilizer (rfl : g • z = g • z)).toMonoidHom) := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hP]
  have hfix := fixingSubgroup_neighborSet_smul (Γ := Γ) g z
  unfold socleAt
  rw [Subgroup.map_sup, ← hper, ← hfix]

theorem socTorus_smul (g : H) (z w y : V) :
    socTorus H Γ (g • z) (g • w) (g • y) =
      (socTorus H Γ z w y).map (MulAut.conj g).toMonoidHom := by
  unfold socTorus
  rw [socleAt_smul, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

theorem socTorus_comm (z w y : V) : socTorus H Γ z w y = socTorus H Γ z y w := by
  unfold socTorus
  ac_rfl

theorem exists_odd_pow_map_eq {G K : Type*} [Group G] [Group K] [Finite G] (φ : G →* K) (g : G)
    (hg : Odd (orderOf (φ g))) : ∃ k : ℕ, Odd (orderOf (g ^ k)) ∧ φ (g ^ k) = φ g := by
  have hn0 : orderOf g ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite g)
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hn0 hab
  have hcop : Nat.Coprime (2 ^ a) b := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hb)
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop hb0
  refine ⟨2 ^ a * c, ?_, ?_⟩
  · have h1 : (g ^ (2 ^ a * c)) ^ b = 1 := by
      rw [← pow_mul, show 2 ^ a * c * b = 2 ^ a * b * c by ring, pow_mul, ← hab,
        pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat hb (orderOf_dvd_of_pow_eq_one h1)
  · have hdvd : orderOf (φ g) ∣ 2 ^ a * b := hab ▸ orderOf_map_dvd φ g
    have hcop' : Nat.Coprime (orderOf (φ g)) (2 ^ a) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hg)
    have hdb : orderOf (φ g) ∣ b := hcop'.dvd_of_dvd_mul_left hdvd
    have hmod : 2 ^ a * c ≡ 1 [MOD orderOf (φ g)] :=
      Nat.ModEq.of_dvd hdb (show 2 ^ a * c ≡ 1 [MOD b] from hc)
    rw [map_pow]
    exact (pow_eq_pow_of_modEq hmod (pow_orderOf_eq_one _)).trans (pow_one _)

theorem twinFree_of_egirth (hg : (4 : ℕ∞) < Γ.egirth)
    (h2 : ∀ v : V, ∃ w w' : V, Γ.Adj v w ∧ Γ.Adj v w' ∧ w ≠ w') :
    ∀ x y : V, (∀ z : V, Γ.Adj x z ↔ Γ.Adj y z) → x = y := by
  intro x y hxy
  by_contra hne
  have hne' : y ≠ x := fun h => hne h.symm
  by_cases hadj : Γ.Adj x y
  · obtain ⟨w, hxw, hwy⟩ : ∃ w, Γ.Adj x w ∧ w ≠ y := by
      obtain ⟨a, b, ha, hb, hab⟩ := h2 x
      by_cases hay : a = y
      · exact ⟨b, hb, fun h => hab (hay.trans h.symm)⟩
      · exact ⟨a, ha, hay⟩
    have hwy' : Γ.Adj w y := ((hxy w).mp hxw).symm
    let p : Γ.Walk x x :=
      SimpleGraph.Walk.cons hxw (SimpleGraph.Walk.cons hwy'
        (SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil))
    have hp : p.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      refine ⟨?_, by simp [p]⟩
      rw [SimpleGraph.Walk.isPath_def]
      simp [p, SimpleGraph.Walk.support_cons, hne, hne', hwy, hwy', hwy'.ne, hxw.ne',
        hadj.ne']
    have hle : Γ.egirth ≤ (3 : ℕ∞) := by
      simpa [p] using hp.egirth_le_length
    have : (4 : ℕ∞) < (3 : ℕ∞) := lt_of_lt_of_le hg hle
    norm_num at this
  · obtain ⟨w, w', hxw, hxw', hww'⟩ := h2 x
    have hwy : w ≠ y := fun h => hadj (h ▸ hxw)
    have hw'y : w' ≠ y := fun h => hadj (h ▸ hxw')
    have hwy' : Γ.Adj w y := ((hxy w).mp hxw).symm
    have hw'y' : Γ.Adj w' y := ((hxy w').mp hxw').symm
    let p : Γ.Walk x x :=
      SimpleGraph.Walk.cons hxw (SimpleGraph.Walk.cons hwy'
        (SimpleGraph.Walk.cons hw'y'.symm
          (SimpleGraph.Walk.cons hxw'.symm SimpleGraph.Walk.nil)))
    have hp : p.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      refine ⟨?_, by simp [p]⟩
      rw [SimpleGraph.Walk.isPath_def]
      simp [p, SimpleGraph.Walk.support_cons, hne, hne', hwy, hw'y, hwy', hw'y', hww',
        hxw.ne', hxw'.ne', hwy'.ne', hw'y'.ne',
        Ne.symm hww', Ne.symm hwy, Ne.symm hw'y]
    have hle : Γ.egirth ≤ (4 : ℕ∞) := by
      simpa [p] using hp.egirth_le_length
    have : (4 : ℕ∞) < (4 : ℕ∞) := lt_of_lt_of_le hg hle
    norm_num at this

structure LocalFacts (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V) [GraphAction H Γ]
    (z : V) : Prop where
  kernel_le : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z
  oddFix : ∀ w, Γ.Adj z w → ∀ K : Subgroup H,
    K ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H w →
    Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex K) →
      ∃ y, Γ.Adj z y ∧ y ≠ w ∧ ∀ k ∈ K, k • y = y
  torusOdd : ∀ w y, Γ.Adj z w → Γ.Adj z y → w ≠ y →
    Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex (socTorus H Γ z w y))
  torusFix : ∀ w y u, Γ.Adj z w → Γ.Adj z y → w ≠ y → Γ.Adj z u →
    (∀ t ∈ socTorus H Γ z w y, t • u = u) → u = w ∨ u = y
  oddClosure : ∀ w y, Γ.Adj z w → Γ.Adj z y → w ≠ y → ∀ S : Set H,
    S ⊆ ↑(MulAction.stabilizer H z ⊓ MulAction.stabilizer H w ⊓ MulAction.stabilizer H y) →
    (∀ s ∈ S, Odd (orderOf s)) →
      Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex (Subgroup.closure S))
  torusGen : ∀ w y, Γ.Adj z w → Γ.Adj z y → w ≠ y → ∀ A : Subgroup H,
    A ≤ socTorus H Γ z w y →
    socTorus H Γ z w y ≤ A ⊔ fixingSubgroup H (Γ.neighborSet z) →
      ∃ b ∈ A, Odd (orderOf b) ∧
        socTorus H Γ z w y ≤ Subgroup.closure {b} ⊔ fixingSubgroup H (Γ.neighborSet z)
  oddConj : ∀ w y, Γ.Adj z w → Γ.Adj z y → w ≠ y → ∀ A B : Subgroup H,
    A ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H w →
    B ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H w →
    Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex A) →
    Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex B) →
    socTorus H Γ z w y ≤ A ⊔ fixingSubgroup H (Γ.neighborSet z) →
      ∃ c ∈ A ⊔ B, ∀ b ∈ B, (c * b * c⁻¹) • y = y

structure ZassenhausFacts (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (z : V) : Prop where
  dichotomy : ∀ w y, Γ.Adj z w → Γ.Adj z y → w ≠ y → ∀ M : Subgroup H,
    M ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H w ⊓ MulAction.stabilizer H y →
    (∀ t ∈ socTorus H Γ z w y, ∀ m ∈ M,
      t * m * t⁻¹ ∈ M ⊔ fixingSubgroup H (Γ.neighborSet z)) →
      M ≤ fixingSubgroup H (Γ.neighborSet z) ∨
        ∀ u, Γ.Adj z u → (∀ m ∈ M, m • u = u) → u = w ∨ u = y
  centralizer_le : ∀ w y, Γ.Adj z w → Γ.Adj z y → w ≠ y →
    ∀ g ∈ MulAction.stabilizer H z ⊓ MulAction.stabilizer H w ⊓ MulAction.stabilizer H y,
      (∀ t ∈ socTorus H Γ z w y, g * t * g⁻¹ * t⁻¹ ∈ fixingSubgroup H (Γ.neighborSet z)) →
        g ∈ socleAt H Γ z

end CFSG.Quasithin.Stroth.WeissDelta

end
