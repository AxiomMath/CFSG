module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.ClosedGoodPath
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RootGroupsIndex

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

theorem commute_of_mem_fixingSubgroup_inf_stabPath {n : ℕ} (hn : 2 ≤ n) (hW : WeissFree H Γ n)
    {p : GPath Γ n} (hp : p.NoBack) {g u : H}
    (hg : g ∈ fixingSubgroup H (Γ.neighborSet (p 0)) ⊓ GPath.stabPath (H := H) p)
    (hu : u ∈ pathRootGroup H Γ p) : g * u = u * g := by
  obtain ⟨hg0, hgp⟩ := Subgroup.mem_inf.mp hg
  have hgp' : g • p = p := by
    rw [GPath.smul_eq_iff]
    exact GPath.mem_stabPath_iff.mp hgp
  have hup0 : u • p 0 = p 0 := by
    have hv : Γ.Adj (p 1) (p 0) := (p.adj 0 (by omega)).symm
    exact (mem_pathRootGroup.mp hu) 1 (by omega) (by omega) (p 0) hv
  have hgu : g * u * g⁻¹ ∈ pathRootGroup H Γ p := by
    have hmap := pathRootGroup_smul_eq (H := H) (Γ := Γ) p g
    rw [hgp'] at hmap
    rw [hmap]
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hu
  have hug : u * g⁻¹ * u⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 0)) := by
    have hfix := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) u (p 0)
    rw [hup0] at hfix
    rw [hfix]
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom (Subgroup.inv_mem _ hg0)
  have hmemU : g * (u * g⁻¹ * u⁻¹) ∈ pathRootGroup H Γ p := by
    rw [show g * (u * g⁻¹ * u⁻¹) = (g * u * g⁻¹) * u⁻¹ by group]
    exact Subgroup.mul_mem _ hgu (Subgroup.inv_mem _ hu)
  have hcomm : g * u * g⁻¹ * u⁻¹ = 1 := by
    have hmem : g * (u * g⁻¹ * u⁻¹) ∈
        fixingSubgroup H (Γ.neighborSet (p 0)) ⊓ pathRootGroup H Γ p :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hg0 hug, hmemU⟩
    have hbot := fixingSubgroup_inf_pathRootGroup_eq_bot (H := H) (Γ := Γ) hn hW hp
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [show g * u * g⁻¹ * u⁻¹ = g * (u * g⁻¹ * u⁻¹) by group]
    exact hmem
  have h2 : g * u * (u * g)⁻¹ = 1 := by
    rw [mul_inv_rev]
    simpa only [mul_assoc] using hcomm
  exact mul_inv_eq_one.mp h2

theorem ClosedGoodPath.not_isPGroup_kernelAt [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ, Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hL : ∀ z, LocalFacts H Γ z) (W : ClosedGoodPath H Γ) (k : ℤ)
    (h2 : ¬ IsPGroup 2 ↥(fixingSubgroup H (Γ.neighborSet (W.x k)))) :
    ¬ IsPGroup 2 ↥(W.kernelAt k) := by
  classical
  let p : GPath Γ (n + 1) := W.window k (n + 1)
  have hp : p.NoBack := ClosedGoodPath.window_noBack W k (n + 1)
  have hp0 : p 0 = W.x k := by
    show W.window k (n + 1) 0 = W.x k
    rw [ClosedGoodPath.window_apply W k (Nat.zero_le (n + 1))]
    simp
  have hK0 : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) (p 0) := by
    rw [hp0]
    exact (hL (W.x k)).kernel_le
  obtain ⟨e, he⟩ := two_pow_relIndex_stabPath (H := H) (Γ := Γ) hn hM hne hval hp hK0
  have hpstab : GPath.stabPath (H := H) p = W.stab :=
    ClosedGoodPath.stabPath_window (H := H) hn hW hL W k
  have he' : (W.kernelAt k).relIndex
      (fixingSubgroup H (Γ.neighborSet (W.x k))) = 2 ^ e := by
    rw [hp0, hpstab] at he
    simpa only [ClosedGoodPath.kernelAt] using he
  intro hK
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, hKcard⟩ := hK.exists_card_eq
  have hKle : W.kernelAt k ≤ fixingSubgroup H (Γ.neighborSet (W.x k)) := inf_le_left
  have hcardG : Nat.card ↥(fixingSubgroup H (Γ.neighborSet (W.x k))) = 2 ^ (e + a) := by
    have hmul := Subgroup.relIndex_mul_card (W.kernelAt k)
      (fixingSubgroup H (Γ.neighborSet (W.x k)))
    rw [inf_eq_left.mpr hKle, he', hKcard, ← pow_add] at hmul
    exact hmul.symm
  exact h2 (IsPGroup.of_card (p := 2) (n := e + a) hcardG)

theorem ClosedGoodPath.socTorus_conj_mem [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hW : WeissFree H Γ n) (hL : ∀ z, LocalFacts H Γ z) (W : ClosedGoodPath H Γ) (k i : ℤ) :
    ∀ t ∈ socTorus H Γ (W.x i) (W.x (i - 1)) (W.x (i + 1)), ∀ m ∈ W.kernelAt k,
      t * m * t⁻¹ ∈ W.kernelAt k ⊔ fixingSubgroup H (Γ.neighborSet (W.x i)) := by
  intro t ht m hm
  let p : GPath Γ (n + 1) := W.window (i - (n : ℤ)) (n + 1)
  have hp : ∀ j : ℕ, j ≤ n + 1 → p j = W.x (i - (n : ℤ) + (j : ℤ)) := by
    intro j hj
    show W.window (i - (n : ℤ)) (n + 1) j = W.x (i - (n : ℤ) + (j : ℤ))
    rw [ClosedGoodPath.window_apply W (i - (n : ℤ)) hj]
  have hgood := (W.good (i - (n : ℤ)) (n + 1) p hp).2 n (by omega) (by omega)
  have hpn : p n = W.x i := by
    rw [hp n (by omega)]
    congr 1
    ring
  have hpm1 : p (n - 1) = W.x (i - 1) := by
    rw [hp (n - 1) (by omega),
      show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num]
    congr 1
    ring
  have hpp1 : p (n + 1) = W.x (i + 1) := by
    rw [hp (n + 1) le_rfl]
    congr 1
    push_cast
    ring
  have hpstab : GPath.stabPath (H := H) p = W.stab :=
    ClosedGoodPath.stabPath_window (H := H) hn hW hL W (i - (n : ℤ))
  have htsup : t ∈ (W.stab ⊓ socleAt H Γ (W.x i)) ⊔
      fixingSubgroup H (Γ.neighborSet (W.x i)) := by
    rw [hpn, hpm1, hpp1, hpstab] at hgood
    exact hgood ht
  have hnorm : (W.stab ⊓ socleAt H Γ (W.x i)) ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (W.x i)) : Set H) := by
    intro a ha
    exact stabilizer_le_normalizer_fixingSubgroup
      (socleAt_le_stabilizer (hL (W.x i)).kernel_le ha.2)
  have htsup' : t ∈ (↑((W.stab ⊓ socleAt H Γ (W.x i)) ⊔
      fixingSubgroup H (Γ.neighborSet (W.x i))) : Set H) := htsup
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (W.stab ⊓ socleAt H Γ (W.x i))
    (fixingSubgroup H (Γ.neighborSet (W.x i))) hnorm] at htsup'
  rcases htsup' with ⟨a, ha, r, hr, har⟩
  have haStab : a ∈ W.stab := ha.1
  have haFix : ∀ j : ℤ, a • W.x j = W.x j := ClosedGoodPath.mem_stab_iff.mp haStab
  have hmStab : m ∈ W.stab := hm.2
  have hmFix : ∀ j : ℤ, m • W.x j = W.x j := ClosedGoodPath.mem_stab_iff.mp hmStab
  have haK : a ∈ Subgroup.normalizer (W.kernelAt k : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (ClosedGoodPath.kernelAt_eq_map_conj W W haFix k).symm
  have haG : a ∈ Subgroup.normalizer
      (fixingSubgroup H (Γ.neighborSet (W.x i)) : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) a (W.x i)
    rw [haFix i] at h
    exact h.symm
  have haKmap : (W.kernelAt k).map (MulAut.conj a).toMonoidHom = W.kernelAt k :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp haK
  have haGmap : (fixingSubgroup H (Γ.neighborSet (W.x i))).map
      (MulAut.conj a).toMonoidHom = fixingSubgroup H (Γ.neighborSet (W.x i)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp haG
  have hsupmap : (W.kernelAt k ⊔ fixingSubgroup H (Γ.neighborSet (W.x i))).map
      (MulAut.conj a).toMonoidHom =
      W.kernelAt k ⊔ fixingSubgroup H (Γ.neighborSet (W.x i)) := by
    rw [Subgroup.map_sup, haKmap, haGmap]
  have haConj : ∀ x ∈ W.kernelAt k ⊔ fixingSubgroup H (Γ.neighborSet (W.x i)),
      a * x * a⁻¹ ∈ W.kernelAt k ⊔ fixingSubgroup H (Γ.neighborSet (W.x i)) := by
    intro x hx
    have h : (MulAut.conj a).toMonoidHom x ∈
        (W.kernelAt k ⊔ fixingSubgroup H (Γ.neighborSet (W.x i))).map
          (MulAut.conj a).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hsupmap] at h
    simpa [MulAut.conj_apply] using h
  have hrG : m⁻¹ * r * m ∈ fixingSubgroup H (Γ.neighborSet (W.x i)) := by
    have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) m⁻¹ (W.x i)
    rw [ClosedGoodPath.mem_stab_iff.mp (Subgroup.inv_mem _ hmStab) i] at h
    rw [h]
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj m⁻¹).toMonoidHom hr
  have hrm : r * m * r⁻¹ ∈
      W.kernelAt k ⊔ fixingSubgroup H (Γ.neighborSet (W.x i)) := by
    have hc : (m⁻¹ * r * m) * r⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x i)) :=
      Subgroup.mul_mem _ hrG (Subgroup.inv_mem _ hr)
    have heq : r * m * r⁻¹ = m * ((m⁻¹ * r * m) * r⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hc)
  have ht_eq : t * m * t⁻¹ = a * (r * m * r⁻¹) * a⁻¹ := by
    rw [← har]
    group
  rw [ht_eq]
  exact haConj _ hrm

theorem ClosedGoodPath.hasThirdFix_iff_le [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hW : WeissFree H Γ n) (hL : ∀ z, LocalFacts H Γ z)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (W : ClosedGoodPath H Γ) (k i : ℤ) (hZ : ZassenhausFacts H Γ (W.x i)) :
    W.HasThirdFix (W.kernelAt k) i ↔
      W.kernelAt k ≤ fixingSubgroup H (Γ.neighborSet (W.x i)) := by
  have hadj1 : Γ.Adj (W.x i) (W.x (i - 1)) := by
    have h := W.adj (i - 1)
    rw [show i - 1 + 1 = i by ring] at h
    exact h.symm
  have hadj2 : Γ.Adj (W.x i) (W.x (i + 1)) := W.adj i
  have hne : W.x (i - 1) ≠ W.x (i + 1) := by
    have h := W.ne_add_two (i - 1)
    rwa [show i - 1 + 2 = i + 1 by ring] at h
  have hKle : W.kernelAt k ≤ MulAction.stabilizer H (W.x i) ⊓
      MulAction.stabilizer H (W.x (i - 1)) ⊓ MulAction.stabilizer H (W.x (i + 1)) := by
    intro m hm
    have hmFix := ClosedGoodPath.mem_stab_iff.mp hm.2
    exact ⟨⟨MulAction.mem_stabilizer_iff.mpr (hmFix i),
      MulAction.mem_stabilizer_iff.mpr (hmFix (i - 1))⟩,
      MulAction.mem_stabilizer_iff.mpr (hmFix (i + 1))⟩
  have hnorm := ClosedGoodPath.socTorus_conj_mem (H := H) hn hW hL W k i
  have hdich := hZ.dichotomy (W.x (i - 1)) (W.x (i + 1)) hadj1 hadj2 hne
    (W.kernelAt k) hKle hnorm
  constructor
  · intro hthird
    obtain ⟨z, hzadj, hz1, hz2, hzfix⟩ := hthird
    rcases hdich with hKG | htwo
    · exact hKG
    · exfalso
      rcases htwo z hzadj hzfix with h | h
      · exact hz1 h
      · exact hz2 h
  · intro hKG
    obtain ⟨z, hzadj, hz1, hz2⟩ := h3 (W.x i) (W.x (i - 1)) (W.x (i + 1)) hadj1 hadj2
    exact ⟨z, hzadj, hz1, hz2, fun m hm => (mem_fixingSubgroup_iff H).mp (hKG hm) z hzadj⟩

end CFSG.Quasithin.Stroth.WeissDelta

end
