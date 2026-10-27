module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.K1320.L4Cls
public import CFSG.RankThree.PartOne.K1320.Members
public import CFSG.RankThree.PartOne.S13K.Pair134Embed
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.Sec1322Fin CFSG.RankThree.PartOne.Sec1322
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 100000

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_vprod1 : ∀ a : Gp, (isT a ∨ isV' a) → ∀ b : Gp, (isT b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → ∀ s : Gp, (isT s ∨ isV' s) → a * s = s * a → b * s = s * b → s ≠ a →
    s ≠ b → s ≠ a * b * a⁻¹ → s ≠ b * a * b⁻¹ → (∃ g : Gp, g * b * g⁻¹ = s) →
    s * b * (a * b * a⁻¹) = z0 ∧ b * (a * b * a⁻¹) = (a * b * a⁻¹) * b := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_vprod2 : ∀ a : Gp, (isT' a ∨ isV' a) → ∀ b : Gp, (isT' b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → ∀ s : Gp, (isT' s ∨ isV' s) → a * s = s * a → b * s = s * b → s ≠ a →
    s ≠ b → s ≠ a * b * a⁻¹ → s ≠ b * a * b⁻¹ → (∃ g : Gp, g * b * g⁻¹ = s) →
    s * b * (a * b * a⁻¹) = z0 ∧ b * (a * b * a⁻¹) = (a * b * a⁻¹) * b := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem vprod {p : ℕ} {E : Subgroup G} (Bd : Bridge p E) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hcard : Nat.card E = p ^ 3) {a b s : MulAut E}
    (ha : a ∈ reflectionSet p E) (hb : b ∈ reflectionSet p E) (hs : s ∈ reflectionSet p E)
    (hab : orderOf (a * b) = 4) (cas : a * s = s * a) (cbs : b * s = s * b) (hsa : s ≠ a)
    (hsb : s ≠ b) (hsaba : s ≠ a * b * a⁻¹) (hsbab : s ≠ b * a * b⁻¹)
    (hsconj : ∃ g ∈ reflectionGroup p E, g * b * g⁻¹ = s) :
    (∀ e : E, (s * b * (a * b * a⁻¹)) e = e⁻¹) ∧ b * (a * b * a⁻¹) = (a * b * a⁻¹) * b := by
  obtain ⟨a', rfl, -, -, -⟩ := Bd.refl_data h hcard ha
  obtain ⟨b', rfl, -, -, -⟩ := Bd.refl_data h hcard hb
  obtain ⟨s', rfl, -, -, -⟩ := Bd.refl_data h hcard hs
  have hinv : ∀ g : Gp, Bd.φ g⁻¹ = (Bd.φ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have ho : orderOf (a' * b') = 4 := by
    rw [← orderOf_injective Bd.φ Bd.inj, map_mul]; exact hab
  have h4 : (a' * b') ^ 4 = 1 := by
    have := pow_orderOf_eq_one (a' * b')
    rwa [ho] at this
  have h2 : (a' * b') ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at this
    omega
  have c1 : a' * s' = s' * a' := Bd.inj (by rw [map_mul, map_mul]; exact cas)
  have c2 : b' * s' = s' * b' := Bd.inj (by rw [map_mul, map_mul]; exact cbs)
  have n1 : s' ≠ a' := fun h1 => hsa (by rw [h1])
  have n2 : s' ≠ b' := fun h1 => hsb (by rw [h1])
  have n3 : s' ≠ a' * b' * a'⁻¹ := fun h1 => hsaba (by rw [h1, map_mul, map_mul, hinv])
  have n4 : s' ≠ b' * a' * b'⁻¹ := fun h1 => hsbab (by rw [h1, map_mul, map_mul, hinv])
  have hconj' : ∃ g : Gp, g * b' * g⁻¹ = s' := by
    obtain ⟨g, hg, hgs⟩ := hsconj
    obtain ⟨g', rfl⟩ := Bd.surj g hg
    exact ⟨g', Bd.inj (by rw [map_mul, map_mul, hinv]; exact hgs)⟩
  have key : s' * b' * (a' * b' * a'⁻¹) = z0 ∧ b' * (a' * b' * a'⁻¹) = (a' * b' * a'⁻¹) * b' := by
    rcases Bd.shape with hshape | hshape
    · exact gp_vprod1 a' ((hshape a').1 ha) b' ((hshape b').1 hb) h4 h2 s' ((hshape s').1 hs)
        c1 c2 n1 n2 n3 n4 hconj'
    · exact gp_vprod2 a' ((hshape a').1 ha) b' ((hshape b').1 hb) h4 h2 s' ((hshape s').1 hs)
        c1 c2 n1 n2 n3 n4 hconj'
  refine ⟨fun e => ?_, ?_⟩
  · have h5 : Bd.φ (s' * b' * (a' * b' * a'⁻¹)) = Bd.φ z0 := congrArg Bd.φ key.1
    rw [map_mul, map_mul, map_mul, map_mul, hinv] at h5
    rw [h5]
    exact Bd.inv e
  · have h5 := congrArg Bd.φ key.2
    simp only [map_mul, hinv] at h5
    exact h5


omit [Finite G] in
theorem mem_autMovedInG_of_inv {p : ℕ} {E : Subgroup G} (hE : IsElementaryAbelian p ↥E)
    (hp : p.Prime) (hp2 : p ≠ 2) {d : MulAut E} {b : G} (hbE : b ∈ E)
    (hd : d ⟨b, hbE⟩ = (⟨b, hbE⟩ : ↥E)⁻¹) : b ∈ autMovedInG E d := by
  have hdat := RefFacts.ElemData.of_isElementaryAbelian hp hp2 hE
  set β : ↥E := ⟨b, hbE⟩ with hβ
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := hp.eq_two_or_odd'.resolve_left hp2
  have hpow : β ^ p = 1 := hdat.pow β
  have hβ2 : β ^ (2 * k) * β = 1 := by
    rw [← pow_succ]
    rw [← hk]
    exact hpow
  have hm : d (β ^ k) * (β ^ k)⁻¹ = β := by
    rw [map_pow, hd, inv_pow]
    have h1 : (β ^ k)⁻¹ * (β ^ k)⁻¹ = (β ^ (2 * k))⁻¹ := by
      rw [two_mul, pow_add, mul_inv_rev]
    rw [h1]
    exact (eq_inv_of_mul_eq_one_right hβ2).symm
  have hmem : d (β ^ k) * (β ^ k)⁻¹ ∈ autMoved E d := Subgroup.subset_closure ⟨β ^ k, rfl⟩
  rw [hm] at hmem
  exact ⟨β, hmem, rfl⟩

omit [Finite G] in
theorem apply_eq_of_mem_torusImage {E I : Subgroup G} {b : G} (hbE : b ∈ E)
    (hI : I ≤ Subgroup.centralizer ({b} : Set G)) {g : MulAut E} (hg : g ∈ torusImage E I) :
    g ⟨b, hbE⟩ = ⟨b, hbE⟩ := by
  obtain ⟨w, hwI, hwN, rfl⟩ := Sec12Three.mem_torusImage_iff.1 hg
  apply Subtype.ext
  show ((conjAut E w hwN ⟨b, hbE⟩ : E) : G) = b
  rw [Equivariance.coe_conjAut hwN]
  have hc : b * w = w * b := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hI hwI)
    exact this.symm
  show w * b * w⁻¹ = b
  rw [← hc]
  group


theorem exists_third {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hcard : Nat.card E = p ^ 3)
    {z : MulAut E} (hz : Inverter p E z) (Bd : Bridge p E)
    {r₀ r₁ zs : MulAut E} (h₀ : r₀ ∈ reflectionSet p E) (h₁ : r₁ ∈ reflectionSet p E)
    (hs : zs ∈ reflectionSet p E) (hab : orderOf (r₀ * r₁) = 4)
    (h₀L : r₀ ∈ torusImage E L) (h₁L : r₁ ∈ torusImage E L)
    (hcomm : ∀ g ∈ torusImage E L, g * zs = zs * g) (hnotL : zs ∉ torusImage E L)
    (hconj : ∃ g ∈ reflectionGroup p E, g * r₁ * g⁻¹ = zs)
    {b : G} (hbE : b ∈ E) (hbz : zs ⟨b, hbE⟩ = ⟨b, hbE⟩)
    {I : Subgroup G} (hI : I ≤ Subgroup.centralizer ({b} : Set G))
    (hiii : I ∈ thetaCompZeroStarE p E) (hzsI : zs ∈ torusImage E I) :
    ∃ d'' : MulAut E, (d'' = r₁ ∨ d'' = r₀ * r₁ * r₀⁻¹) ∧ b ∈ autMovedInG E d'' := by
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  obtain ⟨B'', c'', h'', hF'', hc''E, hc''1, -, -⟩ := member_package hF13 hcard hz hiii
  have hnc : ¬ ∀ g ∈ torusImage E I, g * zs = zs * g := fun hc =>
    no_central_reflection hF13 h'' hF'' hcard hc''E hs hzsI hc
  push Not at hnc
  obtain ⟨g, hgI, hg⟩ := hnc
  have hgX : g ∈ reflectionGroup p E := torusImage_le_reflectionGroup hF'' hgI
  obtain ⟨g₀, hg₀X, hg₀⟩ := hconj
  have hr₀₁ : r₀ * r₁ * r₀⁻¹ ∈ torusImage E L :=
    (torusImage E L).mul_mem ((torusImage E L).mul_mem h₀L h₁L) ((torusImage E L).inv_mem h₀L)
  have hr₁₀ : r₁ * r₀ * r₁⁻¹ ∈ torusImage E L :=
    (torusImage E L).mul_mem ((torusImage E L).mul_mem h₁L h₀L) ((torusImage E L).inv_mem h₁L)
  have hsa : zs ≠ r₀ := fun e => hnotL (e ▸ h₀L)
  have hsb : zs ≠ r₁ := fun e => hnotL (e ▸ h₁L)
  have hsaba : zs ≠ r₀ * r₁ * r₀⁻¹ := fun e => hnotL (e ▸ hr₀₁)
  have hsbab : zs ≠ r₁ * r₀ * r₁⁻¹ := fun e => hnotL (e ▸ hr₁₀)
  have cas : r₀ * zs = zs * r₀ := hcomm r₀ h₀L
  have cbs : r₁ * zs = zs * r₁ := hcomm r₁ h₁L
  have hcl := Bd.vclass h hcard h₀ h₁ hs hab cas cbs hsa hsb hsaba hsbab ⟨g₀, hg₀X, hg₀⟩
    (g * g₀) ((reflectionGroup p E).mul_mem hgX hg₀X)
  have hd : g * g₀ * r₁ * (g * g₀)⁻¹ = g * zs * g⁻¹ := by
    calc g * g₀ * r₁ * (g * g₀)⁻¹ = g * (g₀ * r₁ * g₀⁻¹) * g⁻¹ := by group
      _ = g * zs * g⁻¹ := by rw [hg₀]
  have hdne : g * zs * g⁻¹ ≠ zs := fun e => hg (mul_inv_eq_iff_eq_mul.1 e)
  rw [hd] at hcl
  have hprod := vprod Bd h hcard h₀ h₁ hs hab cas cbs hsa hsb hsaba hsbab ⟨g₀, hg₀X, hg₀⟩
  set β : ↥E := ⟨b, hbE⟩ with hβ
  have hgb : g β = β := apply_eq_of_mem_torusImage hbE hI hgI
  have hgib : g⁻¹ β = β := by
    have h1 : g⁻¹ (g β) = β := by
      show (g⁻¹ * g) β = β
      rw [inv_mul_cancel]
      rfl
    rwa [hgb] at h1
  have hdb : (g * zs * g⁻¹) β = β := by
    show g (zs (g⁻¹ β)) = β
    rw [hgib, hbz, hgb]
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  rcases hcl with h1 | h2 | h3
  ·
    refine ⟨r₀ * r₁ * r₀⁻¹, Or.inr rfl, ?_⟩
    rw [h1] at hdb
    have hc' : r₀ * r₁ * r₀⁻¹ * zs = zs * (r₀ * r₁ * r₀⁻¹) := hcomm _ hr₀₁
    have e1 : zs * r₁ * (r₀ * r₁ * r₀⁻¹) = (r₀ * r₁ * r₀⁻¹) * zs * r₁ := by
      calc zs * r₁ * (r₀ * r₁ * r₀⁻¹) = zs * (r₁ * (r₀ * r₁ * r₀⁻¹)) := by group
        _ = zs * ((r₀ * r₁ * r₀⁻¹) * r₁) := by rw [hprod.2]
        _ = (zs * (r₀ * r₁ * r₀⁻¹)) * r₁ := by group
        _ = ((r₀ * r₁ * r₀⁻¹) * zs) * r₁ := by rw [hc']
        _ = (r₀ * r₁ * r₀⁻¹) * zs * r₁ := by group
    have h5 := hprod.1 β
    rw [e1] at h5
    have h6 : (r₀ * r₁ * r₀⁻¹) β = β⁻¹ := by
      have : ((r₀ * r₁ * r₀⁻¹) * zs * r₁) β = (r₀ * r₁ * r₀⁻¹) (zs (r₁ β)) := rfl
      rw [this, hdb, hbz] at h5
      exact h5
    exact mem_autMovedInG_of_inv hE hp hp2 hbE h6
  ·
    refine ⟨r₁, Or.inl rfl, ?_⟩
    rw [h2] at hdb
    have e1 : zs * r₁ * (r₀ * r₁ * r₀⁻¹) = r₁ * zs * (r₀ * r₁ * r₀⁻¹) := by
      rw [← cbs]
    have h5 := hprod.1 β
    rw [e1] at h5
    have h6 : r₁ β = β⁻¹ := by
      have : (r₁ * zs * (r₀ * r₁ * r₀⁻¹)) β = r₁ (zs ((r₀ * r₁ * r₀⁻¹) β)) := rfl
      rw [this, hdb, hbz] at h5
      exact h5
    exact mem_autMovedInG_of_inv hE hp hp2 hbE h6
  · exact absurd h3 hdne

end CFSG.RankThree.PartOne.K1327
