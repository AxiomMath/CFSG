module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxSmear
public import CFSG.Assembly.LowTwoRankDefs

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53B

open Thm52Aux

variable {G : Type u} [Group G] [Finite G]

structure FixData (p : ℕ) (X Q : Subgroup G) (b : G) : Prop where
  prime : p.Prime
  sol_eq : sol X = ⊥
  coprime : Nat.Coprime p (Nat.card X)
  Q_le : Q ≤ Subgroup.normalizer (X : Set G)
  trans : ∀ J ∈ lcal X, ∀ J' ∈ lcal X, ∃ g ∈ Q, J' = J.map (MulAut.conj g).toMonoidHom
  b_mem : b ∈ Subgroup.normalizer (X : Set G)
  b_pow : b ^ p = 1
  b_comm : ∀ g ∈ Q, g * b = b * g
  hfix : ∀ J ∈ lcal X, b ∈ Subgroup.normalizer (J : Set G) →
    ¬ J ≤ Subgroup.centralizer {b} → Group.IsSolvable ↥(J ⊓ Subgroup.centralizer {b})

namespace FixData

variable {p : ℕ} {X Q : Subgroup G} {b : G} (H : FixData p X Q b)

include H

omit [Finite G] in
theorem mem_normalizer_map_conj_iff {g : G} (hg : g ∈ Q) {J : Subgroup G} :
    b ∈ Subgroup.normalizer ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ↔
      b ∈ Subgroup.normalizer (J : Set G) := by
  have key : ∀ N : Subgroup G, b ∈ Subgroup.normalizer (N : Set G) ↔
      N.map (MulAut.conj b).toMonoidHom = N := fun N => Subgroup.mem_normalizer_iff_map_conj_eq
  rw [key, key]
  have h1 : (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [map_conj_map_conj, map_conj_map_conj, H.b_comm g hg]
  have h2 : Function.Injective (Subgroup.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj g).injective
  rw [h1]
  exact ⟨fun h => h2 h, fun h => by rw [h]⟩

omit [Finite G] in
theorem commute_conj_iff {g : G} (hg : g ∈ Q) (x : G) :
    (g * x * g⁻¹) * b = b * (g * x * g⁻¹) ↔ x * b = b * x := by
  have hcomm : g * b = b * g := H.b_comm g hg
  have hcomm' : g⁻¹ * b = b * g⁻¹ := by
    have := congrArg (fun y => g⁻¹ * y * g⁻¹) hcomm
    simpa [mul_assoc] using this.symm
  constructor
  · intro h
    have : g * (x * b) = g * (b * x) := by
      calc g * (x * b) = (g * x * g⁻¹) * (g * b) := by group
        _ = (g * x * g⁻¹) * (b * g) := by rw [hcomm]
        _ = ((g * x * g⁻¹) * b) * g := by group
        _ = (b * (g * x * g⁻¹)) * g := by rw [h]
        _ = b * g * x := by group
        _ = g * b * x := by rw [hcomm]
        _ = g * (b * x) := by group
    exact mul_left_cancel this
  · intro h
    calc (g * x * g⁻¹) * b = g * x * (g⁻¹ * b) := by group
      _ = g * x * (b * g⁻¹) := by rw [hcomm']
      _ = g * (x * b) * g⁻¹ := by group
      _ = g * (b * x) * g⁻¹ := by rw [h]
      _ = (g * b) * x * g⁻¹ := by group
      _ = (b * g) * x * g⁻¹ := by rw [hcomm]
      _ = b * (g * x * g⁻¹) := by group

omit [Finite G] in
theorem le_centralizer_map_conj_iff {g : G} (hg : g ∈ Q) {J : Subgroup G} :
    J.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer {b} ↔
      J ≤ Subgroup.centralizer {b} := by
  constructor
  · intro h x hx
    have h1 := h ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    have h2 : (g * x * g⁻¹) * b = b * (g * x * g⁻¹) := h1
    exact (H.commute_conj_iff hg x).mp h2
  · rintro h _ ⟨x, hx, rfl⟩
    have h1 := h hx
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    exact (H.commute_conj_iff hg x).mpr h1


omit [Finite G] in
theorem normalizes_of_normalizes {J J' : Subgroup G} (hJ : J ∈ lcal X) (hJ' : J' ∈ lcal X)
    (hbJ : b ∈ Subgroup.normalizer (J : Set G)) : b ∈ Subgroup.normalizer (J' : Set G) := by
  obtain ⟨g, hg, rfl⟩ := H.trans J hJ J' hJ'
  exact (H.mem_normalizer_map_conj_iff hg).mpr hbJ

omit [Finite G] in
theorem centralizes_of_centralizes {J J' : Subgroup G} (hJ : J ∈ lcal X) (hJ' : J' ∈ lcal X)
    (hbJ : J ≤ Subgroup.centralizer {b}) : J' ≤ Subgroup.centralizer {b} := by
  obtain ⟨g, hg, rfl⟩ := H.trans J hJ J' hJ'
  exact (H.le_centralizer_map_conj_iff hg).mpr hbJ

omit H [Finite G] in
theorem smear_eq_of_mem_normalizer {J : Subgroup G} (hbJ : b ∈ Subgroup.normalizer (J : Set G)) :
    smear J (Subgroup.zpowers b) = J ⊓ Subgroup.centralizer {b} := by
  have hAJ : Subgroup.zpowers b ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.zpowers_le.mpr hbJ
  have hL : orbitClosure J (Subgroup.zpowers b) = J := by
    refine le_antisymm (orbitClosure_le fun a ha => ?_) (le_orbitClosure J _)
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAJ ha)).le
  rw [smear, hL, centralizer_zpowers_eq]

theorem kOf_inf_centralizer_eq_iSup_smear :
    kOf X ⊓ Subgroup.centralizer {b} = ⨆ J ∈ lcal X, smear J (Subgroup.zpowers b) := by
  refine le_antisymm (kOf_inf_centralizer_le_iSup_smear H.prime H.sol_eq H.b_mem H.b_pow
    H.coprime) (iSup₂_le fun J hJ => le_inf ?_ ?_)
  · have hAZ : Subgroup.zpowers b ≤ Subgroup.normalizer (X : Set G) :=
      Subgroup.zpowers_le.mpr H.b_mem
    exact (smear_le_orbitClosure J _).trans (orbitClosure_le_kOf H.sol_eq hAZ hJ)
  · rw [← centralizer_zpowers_eq]
    exact smear_le_centralizer J _

theorem isSolvable_of_normalizes (hN : ∀ J ∈ lcal X, b ∈ Subgroup.normalizer (J : Set G))
    (hC : ∀ J ∈ lcal X, ¬ J ≤ Subgroup.centralizer {b}) :
    Group.IsSolvable ↥(kOf X ⊓ Subgroup.centralizer {b}) := by
  have hsol := H.sol_eq
  have h2 : ⨆ J ∈ lcal X, smear J (Subgroup.zpowers b) ≤
      sol (X ⊓ Subgroup.centralizer {b}) := by
    refine iSup₂_le fun J hJ => ?_
    have hsub := isSubnormal_smear hsol H.b_mem hJ
    have hle := smear_le_inf_centralizer hsol H.b_mem hJ
    have hs : Group.IsSolvable ↥(smear J (Subgroup.zpowers b)) := by
      rw [smear_eq_of_mem_normalizer (hN J hJ)]
      exact H.hfix J hJ (hN J hJ) (hC J hJ)
    exact le_sol_of_isSubnormal hle hsub hs
  have h3 : kOf X ⊓ Subgroup.centralizer {b} ≤ sol (X ⊓ Subgroup.centralizer {b}) :=
    H.kOf_inf_centralizer_eq_iSup_smear.le.trans h2
  have : Group.IsSolvable ↥(sol (X ⊓ Subgroup.centralizer {b})) :=
    isSolvable_sol (X ⊓ Subgroup.centralizer {b})
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h3)


theorem isDirectProduct : IsDirectProduct (lcal X) (kOf X) := isDirectProduct_lcal_kOf H.sol_eq

omit [Finite G] in
theorem zpowers_le_normalizer : Subgroup.zpowers b ≤ Subgroup.normalizer (X : Set G) :=
  Subgroup.zpowers_le.mpr H.b_mem

omit [Finite G] in
theorem map_conj_mem_lcal_of_mem_zpowers {a : G} (ha : a ∈ Subgroup.zpowers b)
    {J : Subgroup G} (hJ : J ∈ lcal X) : J.map (MulAut.conj a).toMonoidHom ∈ lcal X :=
  map_conj_mem_lcal hJ (H.zpowers_le_normalizer ha)

omit [Finite G] in
theorem map_conj_mem_lcal_of_mem {g : G} (hg : g ∈ Q) {J : Subgroup G} (hJ : J ∈ lcal X) :
    J.map (MulAut.conj g).toMonoidHom ∈ lcal X :=
  map_conj_mem_lcal hJ (H.Q_le hg)


omit [Finite G] in
theorem commute_of_mem_zpowers {g : G} (hg : g ∈ Q) {a : G} (ha : a ∈ Subgroup.zpowers b) :
    g * a = a * g := by
  have : g ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rw [centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
    exact H.b_comm g hg
  exact (Subgroup.mem_centralizer_iff.mp this a ha).symm

omit [Finite G] in
theorem smear_map_conj_le {g : G} (hg : g ∈ Q) (J : Subgroup G) :
    smear (J.map (MulAut.conj g).toMonoidHom) (Subgroup.zpowers b) ≤
      (smear J (Subgroup.zpowers b)).map (MulAut.conj g).toMonoidHom := by
  have h1 : orbitClosure (J.map (MulAut.conj g).toMonoidHom) (Subgroup.zpowers b) ≤
      (orbitClosure J (Subgroup.zpowers b)).map (MulAut.conj g).toMonoidHom := by
    refine orbitClosure_le fun a ha => ?_
    have h2 : (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [map_conj_map_conj, map_conj_map_conj, H.commute_of_mem_zpowers hg ha]
    rw [h2]
    exact Subgroup.map_mono (map_conj_le_orbitClosure J ha)
  intro x hx
  obtain ⟨hxo, hxc⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, hy, hyx⟩ := h1 hxo
  refine ⟨y, Subgroup.mem_inf.mpr ⟨hy, ?_⟩, hyx⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hxa := Subgroup.mem_centralizer_iff.mp hxc a ha
  have hga := H.commute_of_mem_zpowers hg ha
  have hyx' : g * y * g⁻¹ = x := hyx
  have hy' : y = g⁻¹ * x * g := by rw [← hyx']; group
  rw [hy']
  have hag : a * g⁻¹ = g⁻¹ * a := by
    have := congrArg (fun z => g⁻¹ * z * g⁻¹) hga
    simpa [mul_assoc] using this
  calc a * (g⁻¹ * x * g) = (a * g⁻¹) * x * g := by group
    _ = (g⁻¹ * a) * x * g := by rw [hag]
    _ = g⁻¹ * (a * x) * g := by group
    _ = g⁻¹ * (x * a) * g := by rw [← hxa]
    _ = g⁻¹ * x * (a * g) := by group
    _ = g⁻¹ * x * (g * a) := by rw [hga]
    _ = (g⁻¹ * x * g) * a := by group

section Free

variable (hfree : ∀ J ∈ lcal X, b ∉ Subgroup.normalizer (J : Set G))

include hfree

theorem map_conj_ne {a : G} (ha : a ∈ Subgroup.zpowers b) (ha1 : a ≠ 1) {J : Subgroup G}
    (hJ : J ∈ lcal X) : J.map (MulAut.conj a).toMonoidHom ≠ J := by
  intro h
  have haN : a ∈ Subgroup.normalizer (J : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  have hbot := zpowers_inf_normalizer_eq_bot H.prime H.b_pow (hfree J hJ)
  have : a ∈ Subgroup.zpowers b ⊓ Subgroup.normalizer (J : Set G) := ⟨ha, haN⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact ha1 this

omit hfree in
theorem smear_le_U {J : Subgroup G} (hJ : J ∈ lcal X) :
    smear J (Subgroup.zpowers b) ≤ kOf X ⊓ Subgroup.centralizer {b} := by
  rw [H.kOf_inf_centralizer_eq_iSup_smear]
  exact le_iSup₂ (f := fun J (_ : J ∈ lcal X) => smear J (Subgroup.zpowers b)) J hJ

theorem smear_isSimpleGroup {J : Subgroup G} (hJ : J ∈ lcal X) :
    IsSimpleGroup ↥(smear J (Subgroup.zpowers b)) ∧
      ¬ IsMulCommutative ↥(smear J (Subgroup.zpowers b)) := by
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  obtain ⟨e⟩ := nonempty_mulEquiv_smear H.prime H.b_mem H.b_pow hJ (hfree J hJ)
  exact ⟨e.isSimpleGroup, fun hc => hnc ((isMulCommutative_congr e).mp hc)⟩

theorem smear_coord_surj {J : Subgroup G} (hJ : J ∈ lcal X) {j : G} (hj : j ∈ J) :
    ∃ y : ↥(kOf X), (y : G) ∈ smear J (Subgroup.zpowers b) ∧
      ((H.isDirectProduct.coord hJ y : J) : G) = j := by
  have hA : ∀ a ∈ Subgroup.zpowers b, ∀ J ∈ lcal X, J.map (MulAut.conj a).toMonoidHom ∈ lcal X :=
    fun a ha J hJ => H.map_conj_mem_lcal_of_mem_zpowers ha hJ
  have hfreeA : ∀ a ∈ Subgroup.zpowers b, a ≠ 1 → ∀ J ∈ lcal X,
      J.map (MulAut.conj a).toMonoidHom ≠ J := fun a ha ha1 J hJ =>
    H.map_conj_ne hfree ha ha1 hJ
  have hW : smear J (Subgroup.zpowers b) ≤
      kOf X ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]
    exact H.smear_le_U hJ
  have h := le_projIn_of_smear_le H.isDirectProduct hA hfreeA hW hJ le_rfl le_rfl hj
  exact ((H.isDirectProduct).mem_projIn_iff hJ).mp h


theorem minimal_of_free {N : Subgroup G} (hNU : N ≤ kOf X ⊓ Subgroup.centralizer {b})
    (hNn : (N.subgroupOf (kOf X ⊓ Subgroup.centralizer {b})).Normal) (hNQ : Admits Q N) :
    N = ⊥ ∨ N = kOf X ⊓ Subgroup.centralizer {b} := by
  by_cases hN1 : N = ⊥
  · exact Or.inl hN1
  right
  have hdp := H.isDirectProduct
  have hNconj : ∀ n ∈ N, ∀ k ∈ kOf X ⊓ Subgroup.centralizer {b}, k * n * k⁻¹ ∈ N :=
    fun n hn k hk => (Subgroup.normal_subgroupOf_iff hNU).mp hNn n k hn hk
  obtain ⟨m, hmN, hm1⟩ : ∃ m ∈ N, m ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hN1 ((Subgroup.eq_bot_iff_forall N).mpr hcon)
  have hmK : m ∈ kOf X := (hNU hmN).1
  have hmC : m ∈ Subgroup.centralizer {b} := (hNU hmN).2
  obtain ⟨J, hJ, hcoord⟩ : ∃ J, ∃ hJ : J ∈ lcal X, hdp.coord hJ ⟨m, hmK⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hm1
    have : (⟨m, hmK⟩ : ↥(kOf X)) = 1 := hdp.ext_coord fun J hJ => by
      rw [hcon J hJ, map_one]
    exact congrArg Subtype.val this
  obtain ⟨-, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
  obtain ⟨y, huy⟩ : ∃ y : ↥J, hdp.coord hJ ⟨m, hmK⟩ * y ≠ y * hdp.coord hJ ⟨m, hmK⟩ := by
    by_contra hcon
    push Not at hcon
    have hnc' : ∃ a b : ↥J, a * b ≠ b * a := by
      by_contra h2
      push Not at h2
      exact hJnc (isMulCommutative_iff.mpr h2)
    have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc').2
    have : hdp.coord hJ ⟨m, hmK⟩ ∈ Subgroup.center ↥J :=
      Subgroup.mem_center_iff.mpr fun t => (hcon t).symm
    rw [hZ, Subgroup.mem_bot] at this
    exact hcoord this
  obtain ⟨y', hy'Δ, hy'c⟩ := H.smear_coord_surj hfree hJ y.2
  have hy'U : (y' : G) ∈ kOf X ⊓ Subgroup.centralizer {b} := H.smear_le_U hJ hy'Δ
  have hy'y : hdp.coord hJ y' = y := Subtype.ext hy'c
  have hKL : kOf X ≤ Subgroup.normalizer
      ((orbitClosure J (Subgroup.zpowers b) : Subgroup G) : Set G) :=
    kOf_le_normalizer_orbitClosure H.sol_eq H.zpowers_le_normalizer hJ
  have hy'L : (y' : G) ∈ orbitClosure J (Subgroup.zpowers b) := smear_le_orbitClosure J _ hy'Δ
  set y₀ : G := (y' : G) with hy₀
  set z : G := m * y₀ * m⁻¹ * y₀⁻¹ with hz
  have hzN : z ∈ N := by
    have := hNconj m⁻¹ (inv_mem hmN) y₀ hy'U
    have e : z = m * (y₀ * m⁻¹ * y₀⁻¹) := by rw [hz]; group
    rw [e]
    exact mul_mem hmN this
  have hzΔ : z ∈ smear J (Subgroup.zpowers b) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hKL hmK) y₀).mp hy'L
      exact mul_mem h1 (inv_mem hy'L)
    · rw [centralizer_zpowers_eq]
      exact mul_mem (mul_mem (mul_mem hmC hy'U.2) (inv_mem hmC)) (inv_mem hy'U.2)
  have hz1 : z ≠ 1 := by
    intro h1
    have hcomm : m * y₀ = y₀ * m := by
      calc m * y₀ = (m * y₀ * m⁻¹ * y₀⁻¹) * (y₀ * m) := by group
        _ = y₀ * m := by rw [← hz, h1, one_mul]
    have hcomm' : (⟨m, hmK⟩ : ↥(kOf X)) * y' = y' * ⟨m, hmK⟩ := Subtype.ext hcomm
    have := congrArg (hdp.coord hJ) hcomm'
    rw [map_mul, map_mul, hy'y] at this
    exact huy this
  have hΔsimple := (H.smear_isSimpleGroup hfree hJ).1
  have hΔN : smear J (Subgroup.zpowers b) ≤ N := by
    have hnormal : ((N ⊓ smear J (Subgroup.zpowers b)).subgroupOf
        (smear J (Subgroup.zpowers b))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro h k hh hk
      obtain ⟨hhN, hhΔ⟩ := Subgroup.mem_inf.mp hh
      exact Subgroup.mem_inf.mpr ⟨hNconj h hhN k (H.smear_le_U hJ hk),
        mul_mem (mul_mem hk hhΔ) (inv_mem hk)⟩
    have := hnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N ⊓ smear J (Subgroup.zpowers b)).subgroupOf (smear J (Subgroup.zpowers b))) with h0 | h1
    · exfalso
      have hmem : (⟨z, hzΔ⟩ : ↥(smear J (Subgroup.zpowers b))) ∈
          (N ⊓ smear J (Subgroup.zpowers b)).subgroupOf (smear J (Subgroup.zpowers b)) :=
        Subgroup.mem_inf.mpr ⟨hzN, hzΔ⟩
      rw [h0, Subgroup.mem_bot] at hmem
      exact hz1 (congrArg Subtype.val hmem)
    · intro x hx
      have hmem : (⟨x, hx⟩ : ↥(smear J (Subgroup.zpowers b))) ∈
          (N ⊓ smear J (Subgroup.zpowers b)).subgroupOf (smear J (Subgroup.zpowers b)) := by
        rw [h1]
        trivial
      exact (Subgroup.mem_inf.mp hmem).1
  refine le_antisymm hNU ?_
  rw [H.kOf_inf_centralizer_eq_iSup_smear]
  refine iSup₂_le fun J' hJ' => ?_
  obtain ⟨g, hg, hJ'g⟩ := H.trans J hJ J' hJ'
  rw [hJ'g]
  intro x hx
  obtain ⟨w, hwΔ, rfl⟩ := H.smear_map_conj_le hg J hx
  exact (Subgroup.mem_normalizer_iff.mp (hNQ hg) w).mp (hΔN hwΔ)


omit hfree in
theorem coord_conj_fixed {c : G} (hc : ∀ J ∈ lcal X, J.map (MulAut.conj c).toMonoidHom ∈ lcal X)
    {J : Subgroup G} (hJ : J ∈ lcal X) {y : ↥(kOf X)} (hcy : c * (y : G) * c⁻¹ = y) :
    ((H.isDirectProduct.coord (hc J hJ) y : J.map (MulAut.conj c).toMonoidHom) : G) =
      c * ((H.isDirectProduct.coord hJ y : J) : G) * c⁻¹ := by
  have h := H.isDirectProduct.coord_conj hc hJ y.2
  have e : (⟨c * (y : G) * c⁻¹, H.isDirectProduct.conj_mem hc y.2⟩ : ↥(kOf X)) = y :=
    Subtype.ext hcy
  rw [e] at h
  exact h

theorem centralizes_of_free {g : G} (hg : g ∈ Q) (hgp : Nat.Coprime p (orderOf g))
    (hgU : ∀ y ∈ kOf X ⊓ Subgroup.centralizer {b}, g * y = y * g) :
    ∀ x ∈ kOf X, g * x = x * g := by
  have hdp := H.isDirectProduct
  have hmapg : ∀ J ∈ lcal X, J.map (MulAut.conj g).toMonoidHom ∈ lcal X :=
    fun J hJ => H.map_conj_mem_lcal_of_mem hg hJ
  have hgy : ∀ y : ↥(kOf X), (y : G) ∈ kOf X ⊓ Subgroup.centralizer {b} →
      g * (y : G) * g⁻¹ = y := fun y hy => by
    rw [mul_inv_eq_iff_eq_mul]
    exact hgU y hy
  have hcomp : ∀ J ∈ lcal X, ∀ j ∈ J, g * j = j * g := by
    intro J hJ
    obtain ⟨-, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
    have hJg : J.map (MulAut.conj g).toMonoidHom = J := by
      by_contra hne
      obtain ⟨j₀, hj₀, hj₀1⟩ : ∃ j ∈ J, j ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hbot : J = ⊥ := (Subgroup.eq_bot_iff_forall J).mpr hcon
        rw [hbot] at hJnc
        exact hJnc inferInstance
      obtain ⟨y₀, hy₀Δ, hy₀c⟩ := H.smear_coord_surj hfree hJ hj₀
      have hy₀U : (y₀ : G) ∈ kOf X ⊓ Subgroup.centralizer {b} := H.smear_le_U hJ hy₀Δ
      have hy₀L : (y₀ : G) ∈ orbitClosure J (Subgroup.zpowers b) :=
        smear_le_orbitClosure J _ hy₀Δ
      have hc1 := H.coord_conj_fixed hmapg hJ (hgy y₀ hy₀U)
      rw [hy₀c] at hc1
      have hnot1 : hdp.coord (hmapg J hJ) y₀ ≠ 1 := by
        intro h1
        have : g * j₀ * g⁻¹ = 1 := by
          rw [← hc1, h1]
          rfl
        have : j₀ = 1 := by
          have h2 := congrArg (fun z => g⁻¹ * z * g) this
          simpa [mul_assoc] using h2
        exact hj₀1 this
      have hex : ∃ a ∈ Subgroup.zpowers b, J.map (MulAut.conj a).toMonoidHom =
          J.map (MulAut.conj g).toMonoidHom := by
        by_contra hno
        push Not at hno
        have hle : orbitClosure J (Subgroup.zpowers b) ≤
            sSup (lcal X \ {J.map (MulAut.conj g).toMonoidHom}) :=
          orbitClosure_le fun a ha => le_sSup
            ⟨H.map_conj_mem_lcal_of_mem_zpowers ha hJ,
              fun h => hno a ha (Set.mem_singleton_iff.mp h)⟩
        exact hnot1 ((hdp.coord_eq_one_iff (hmapg J hJ) y₀).mpr (hle hy₀L))
      obtain ⟨a, haA, haJ⟩ := hex
      have ha1 : a ≠ 1 := by
        rintro rfl
        apply hne
        rw [← haJ]
        ext x
        simp
      have hmapa : ∀ J ∈ lcal X, J.map (MulAut.conj a).toMonoidHom ∈ lcal X :=
        fun J hJ => H.map_conj_mem_lcal_of_mem_zpowers haA hJ
      have hgj : ∀ j ∈ J, g * j * g⁻¹ = a * j * a⁻¹ := by
        intro j hj
        obtain ⟨y, hyΔ, hyc⟩ := H.smear_coord_surj hfree hJ hj
        have hyU : (y : G) ∈ kOf X ⊓ Subgroup.centralizer {b} := H.smear_le_U hJ hyΔ
        have hay : a * (y : G) * a⁻¹ = y := by
          have : (y : G) ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
            rw [centralizer_zpowers_eq]
            exact hyU.2
          rw [mul_inv_eq_iff_eq_mul]
          exact (Subgroup.mem_centralizer_iff.mp this a haA)
        have h1 := H.coord_conj_fixed hmapg hJ (hgy y hyU)
        have h2 := H.coord_conj_fixed hmapa hJ hay
        rw [hyc] at h1 h2
        have h3 := hdp.coord_val_congr (hmapg J hJ) (hmapa J hJ) haJ.symm y
        rw [← h1, ← h2]
        exact h3
      have hcent : ∀ j ∈ J, (a⁻¹ * g) * j = j * (a⁻¹ * g) := by
        intro j hj
        have h1 := hgj j hj
        calc (a⁻¹ * g) * j = a⁻¹ * (g * j * g⁻¹) * g := by group
          _ = a⁻¹ * (a * j * a⁻¹) * g := by rw [h1]
          _ = j * (a⁻¹ * g) := by group
      have hcomm : Commute (a⁻¹) g :=
        (show Commute g a from H.commute_of_mem_zpowers hg haA).inv_right.symm
      have hpow : (a⁻¹ * g) ^ (orderOf g) = (a⁻¹) ^ (orderOf g) := by
        rw [hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
      have hcentpow : ∀ j ∈ J, (a⁻¹) ^ (orderOf g) * j = j * (a⁻¹) ^ (orderOf g) := by
        intro j hj
        rw [← hpow]
        exact (Commute.pow_left (show Commute (a⁻¹ * g) j from hcent j hj) _).eq
      have hmemN : (a⁻¹) ^ (orderOf g) ∈ Subgroup.normalizer (J : Set G) := by
        apply Subgroup.centralizer_le_normalizer (J : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact (hcentpow j hj).symm
      have hmemA : (a⁻¹) ^ (orderOf g) ∈ Subgroup.zpowers b := pow_mem (inv_mem haA) _
      have hbot := zpowers_inf_normalizer_eq_bot H.prime H.b_pow (hfree J hJ)
      have hmem : (a⁻¹) ^ (orderOf g) ∈ Subgroup.zpowers b ⊓ Subgroup.normalizer (J : Set G) :=
        ⟨hmemA, hmemN⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have hap : a ^ p = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp haA
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, H.b_pow, one_zpow]
      have : Fact p.Prime := ⟨H.prime⟩
      have hordA : orderOf a = p := orderOf_eq_prime hap ha1
      have h1' : a ^ (orderOf g) = 1 := by
        have h2 := congrArg (fun z => z⁻¹) hmem
        simpa [inv_pow] using h2
      have hdvd : p ∣ orderOf g := hordA ▸ orderOf_dvd_of_pow_eq_one h1'
      exact H.prime.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hgp hdvd)
    intro j hj
    obtain ⟨y, hyΔ, hyc⟩ := H.smear_coord_surj hfree hJ hj
    have hyU : (y : G) ∈ kOf X ⊓ Subgroup.centralizer {b} := H.smear_le_U hJ hyΔ
    have h1 := H.coord_conj_fixed hmapg hJ (hgy y hyU)
    rw [hyc] at h1
    have h3 := hdp.coord_val_congr (hmapg J hJ) hJ hJg y
    rw [h1, hyc] at h3
    calc g * j = (g * j * g⁻¹) * g := by group
      _ = j * g := by rw [h3]
  intro x hx
  have hK : kOf X ≤ Subgroup.centralizer {g} := by
    rw [← hdp.sSup_eq]
    refine sSup_le fun J hJ j hj => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomp J hJ j hj).symm
  have hx' := hK hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx'
  exact hx'.symm

end Free


theorem dichotomy
    (hmin : ∀ N : Subgroup G, N ≤ kOf X → (N.subgroupOf (kOf X)).Normal → Admits Q N →
      N = ⊥ ∨ N = kOf X) :
    Group.IsSolvable ↥(kOf X ⊓ Subgroup.centralizer {b}) ∨
      (¬ Group.IsSolvable ↥(kOf X ⊓ Subgroup.centralizer {b}) ∧
        (∀ N : Subgroup G, N ≤ kOf X ⊓ Subgroup.centralizer {b} →
          (N.subgroupOf (kOf X ⊓ Subgroup.centralizer {b})).Normal → Admits Q N →
            N = ⊥ ∨ N = kOf X ⊓ Subgroup.centralizer {b}) ∧
        (∀ g ∈ Q, Nat.Coprime p (orderOf g) →
          (∀ y ∈ kOf X ⊓ Subgroup.centralizer {b}, g * y = y * g) →
            ∀ x ∈ kOf X, g * x = x * g)) := by
  by_cases hΩ : ∃ J, J ∈ lcal X
  · obtain ⟨J₀, hJ₀⟩ := hΩ
    by_cases hN : b ∈ Subgroup.normalizer (J₀ : Set G)
    · have hNall : ∀ J ∈ lcal X, b ∈ Subgroup.normalizer (J : Set G) := fun J hJ =>
        H.normalizes_of_normalizes hJ₀ hJ hN
      by_cases hC : J₀ ≤ Subgroup.centralizer {b}
      · have hCall : ∀ J ∈ lcal X, J ≤ Subgroup.centralizer {b} := fun J hJ =>
          H.centralizes_of_centralizes hJ₀ hJ hC
        have hKC : kOf X ≤ Subgroup.centralizer {b} := by
          rw [← H.isDirectProduct.sSup_eq]
          exact sSup_le hCall
        rw [inf_eq_left.mpr hKC]
        by_cases hs : Group.IsSolvable ↥(kOf X)
        · exact Or.inl hs
        · exact Or.inr ⟨hs, hmin, fun g _ _ hgU x hx => hgU x hx⟩
      · have hC' : ∀ J ∈ lcal X, ¬ J ≤ Subgroup.centralizer {b} := fun J hJ hJC =>
          hC (H.centralizes_of_centralizes hJ hJ₀ hJC)
        exact Or.inl (H.isSolvable_of_normalizes hNall hC')
    · have hfree : ∀ J ∈ lcal X, b ∉ Subgroup.normalizer (J : Set G) := fun J hJ hbJ =>
        hN (H.normalizes_of_normalizes hJ hJ₀ hbJ)
      by_cases hs : Group.IsSolvable ↥(kOf X ⊓ Subgroup.centralizer {b})
      · exact Or.inl hs
      · exact Or.inr ⟨hs, fun N hNU hNn hNQ => H.minimal_of_free hfree hNU hNn hNQ,
          fun g hg hgp hgU => H.centralizes_of_free hfree hg hgp hgU⟩
  · left
    have hΩ' : lcal X = ∅ := by
      by_contra hne
      exact hΩ (Set.nonempty_iff_ne_empty.mpr hne)
    have hK : kOf X = ⊥ := by
      rw [← H.isDirectProduct.sSup_eq, hΩ', sSup_empty]
    rw [hK, bot_inf_eq]
    infer_instance

end FixData

end Thm53B

end CFSG.SignalizerFunctorTheorem.McBride.Near
