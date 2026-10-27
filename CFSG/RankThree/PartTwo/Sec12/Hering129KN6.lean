module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KM5
public import CFSG.RankThree.PartTwo.Sec12.Hering129KN4
public import CFSG.RankThree.PartTwo.Sec12.Hering129KN5
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH1
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH2
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH2b
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH3
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH3b

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open Matrix (ProjGenLinGroup)

namespace Hering129KN6

theorem mem_normalizer_of_map {P : Type} [Group P] {Yh : Subgroup P} {G' : Type*}
    [Group G'] {φ : ↥Yh →* G'} (hφ : Function.Injective φ) {Vh : Subgroup P} (hVY : Vh ≤ Yh)
    {n : ↥Yh} (hn : φ n ∈ Subgroup.normalizer (((Vh.subgroupOf Yh).map φ : Subgroup G') : Set G')) :
    (n : P) ∈ Subgroup.normalizer (Vh : Set P) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro v
  by_cases hv : v ∈ Yh
  · have h1 := hn (φ ⟨v, hv⟩)
    rw [← map_inv φ, ← map_mul φ, ← map_mul φ, Subgroup.mem_map_iff_mem hφ,
      Subgroup.mem_map_iff_mem hφ, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h1
    exact h1
  · have h1 : (n : P) * v * (n : P)⁻¹ ∉ Yh := fun h => hv (by
      have h2 := Yh.mul_mem (Yh.mul_mem (Yh.inv_mem n.2) h) n.2
      simpa [mul_assoc] using h2)
    exact ⟨fun h => absurd (hVY h) hv, fun h => absurd (hVY h) h1⟩

end Hering129KN6


namespace Hering129KN6

theorem move_of_frame {P : Type} [Group P] {Yh : Subgroup P} {K : Type} [Field K]
    {p f : ℕ} {π : Bool} (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {φ : ↥Yh →* ProjGenLinGroup (Fin 3) K}
    (hφ : Function.Injective φ) (hφL : ∀ x, φ x ∈ projImage (Sec4.slPi π 3 (p ^ f) K))
    (hφs : ∀ m ∈ projImage (Sec4.slPi π 3 (p ^ f) K), ∃ x, φ x = m)
    {ch : P} (hc : ch ∈ Yh) (hφc : φ ⟨ch, hc⟩ = ProjGenLinGroup.mk (Sec4.diagTau hτ))
    {Vh : Subgroup P} (hVY : Vh ≤ Yh) (hV : CFSG.Assembly.IsElemAbelian 3 Vh)
    (hV9 : Nat.card Vh = 9) (hcV : ch ∈ Vh) {s : P} (hs : s ∈ Yh)
    (hsV : ∀ v ∈ Vh, s * v * s⁻¹ = v⁻¹) :
    ∃ n ∈ Yh ⊓ Subgroup.normalizer (Vh : Set P), n * ch * n⁻¹ ∉ Subgroup.zpowers ch := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := hK.finite
  haveI : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  set W : Subgroup (ProjGenLinGroup (Fin 3) K) := (Vh.subgroupOf Yh).map φ with hW
  have hWL : W ≤ projImage (Sec4.slPi π 3 (p ^ f) K) := by
    rintro _ ⟨x, -, rfl⟩
    exact hφL x
  have hWe : CFSG.Assembly.IsElemAbelian 3 W := (hV.subgroupOf Yh).map φ
  have hW9 : Nat.card W = 9 := by
    rw [hW, Subgroup.card_map_of_injective hφ, ← hV9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv
  have hdW : ProjGenLinGroup.mk (Sec4.diagTau hτ) ∈ W :=
    ⟨⟨ch, hc⟩, Subgroup.mem_subgroupOf.mpr hcV, hφc⟩
  have htW : ∀ w ∈ W, φ ⟨s, hs⟩ * w * (φ ⟨s, hs⟩)⁻¹ = w⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (⟨s, hs⟩ : ↥Yh) * x * (⟨s, hs⟩ : ↥Yh)⁻¹ = x⁻¹ :=
      Subtype.ext (hsV x (Subgroup.mem_subgroupOf.mp hx))
    rw [← map_inv φ, ← map_mul φ, ← map_mul φ, hx', map_inv]
  have hd1 : ProjGenLinGroup.mk (Sec4.diagTau hτ) ≠ 1 := fun h =>
    Sec4.diagTau_not_mem_statedScalars hτ hτ1 (Sec4.mk_eq_one_iff_mem_statedScalars.mp h)
  have hord : orderOf (ProjGenLinGroup.mk (Sec4.diagTau hτ)) = 3 :=
    orderOf_eq_prime (hWe.2 _ hdW) hd1
  obtain ⟨w, hwW, hwd⟩ :
      ∃ w ∈ W, w ∉ Subgroup.zpowers (ProjGenLinGroup.mk (Sec4.diagTau hτ)) := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show W ≤ Subgroup.zpowers _ from fun x hx => hall x hx)
    rw [hW9, Nat.card_zpowers, hord] at this
    omega
  have hw1 : w ≠ 1 := fun h => hwd (h ▸ Subgroup.one_mem _)
  obtain ⟨n, hn, hnw⟩ := transitive_of_inverted hK hq hτ hτ1 hWL hWe hW9 hdW htW _ hdW hd1 w
    hwW hw1
  obtain ⟨x, rfl⟩ := hφs n (Subgroup.mem_inf.mp hn).1
  refine ⟨x, Subgroup.mem_inf.mpr ⟨x.2, mem_normalizer_of_map hφ hVY
    (Subgroup.mem_inf.mp hn).2⟩, fun hmem => hwd ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : (⟨ch, hc⟩ : ↥Yh) ^ k = x * ⟨ch, hc⟩ * x⁻¹ := Subtype.ext (by simpa using hk)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← hφc, ← map_zpow φ, hk', map_mul φ, map_mul φ, map_inv φ, hφc, hnw]

end Hering129KN6

theorem hess_t_move (hDeg : Gap129HessL3Deg) {P : Type} [Group P] [Finite P]
    {Yh Bh : Subgroup P} {xh bh ch : P} (hD : HessData Yh Bh xh bh ch)
    (hex : ∃ (p e : ℕ) (_ : Fact p.Prime), Sec4.IsoLThreePi ↥Yh p e) :
    ∃ th ∈ Yh, th ^ 2 = 1 ∧ bh * th = th * bh ∧ th * ch * th⁻¹ = ch⁻¹ ∧
      ∀ Vh : Subgroup P, Vh ≤ Yh → CFSG.Assembly.IsElemAbelian 3 Vh → Nat.card Vh = 9 →
        ch ∈ Vh → (∃ s ∈ Yh, ∀ v ∈ Vh, s * v * s⁻¹ = v⁻¹) →
        ∃ n ∈ Yh ⊓ Subgroup.normalizer (Vh : Set P), n * ch * n⁻¹ ∉ Subgroup.zpowers ch := by
  obtain ⟨p, e, hp, hiso⟩ := hex
  haveI := hD.normal
  obtain ⟨p, e, hp, he, hiso⟩ : ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
      Sec4.IsoLThreePi ↥Yh p e := by
    by_cases he : 1 ≤ e
    · exact ⟨p, e, hp, he, hiso⟩
    · obtain rfl : e = 0 := by omega
      by_cases h3 : p % 3 = 1
      · exact ⟨p, 1, hp, le_rfl, Hering129KH2b.isoLThreePi_zero hiso h3⟩
      · exfalso
        rcases hiso with ⟨-, hf⟩ | ⟨h2, -⟩
        · exact hDeg P Yh Bh xh bh ch hD p h3 hf
        · simp at h2
  obtain ⟨π, K, _, hK, hq, ⟨e'⟩⟩ := Hering129KH2.hess_model hD he hiso
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p e K :=
    fun h => by subst h; exact hK.unitary
  have hact := Hering129KH3.hess_actions hD hK hq e'
  obtain ⟨y, hy⟩ := hact bh (Subgroup.mem_sup_right (by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers bh))))
  obtain ⟨hyZ, hy3, hm1, hm3, -, Xm, hXL, hXC, hXp, hXs, hmX⟩ :=
    Hering129KH3b.hess_to_pgl hD hK hq e' hy
  obtain ⟨τ, hτ, hτ1, g, hg, hm₀g, ε, a, b, c, -, -, hshape, hyg⟩ :=
    exists_frame hK hq hy.1 hyZ hy3 (e' ⟨ch, hD.cY⟩).2 hm1 hm3 hXL hXC hXp hXs hmX
  obtain ⟨t, htS, htt, htD, l, htd⟩ := exists_negPerm hK hq hτ hτ1 hshape
  let φ : ↥Yh →* ProjGenLinGroup (Fin 3) K :=
    (MulAut.conj (ProjGenLinGroup.mk g)⁻¹).toMonoidHom.comp
      ((projImage (Sec4.slPi π 3 (p ^ e) K)).subtype.comp e'.toMonoidHom)
  have hφ : ∀ x, φ x = (ProjGenLinGroup.mk g)⁻¹ * (e' x : ProjGenLinGroup (Fin 3) K) *
      ProjGenLinGroup.mk g := fun x => by
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, inv_inv]
  have hφi : Function.Injective φ :=
    (MulAut.conj _).injective.comp ((Subgroup.subtype_injective _).comp e'.injective)
  have hφL : ∀ x, φ x ∈ projImage (Sec4.slPi π 3 (p ^ e) K) := by
    intro x
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp (e' x).2
    rw [hφ, ← hux]
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * u * g, ?_, by
      rw [map_mul ProjGenLinGroup.mk, map_mul ProjGenLinGroup.mk, map_inv ProjGenLinGroup.mk]⟩
    simpa using Sec4.conj_mem_slPi hπ (inv_mem hg) hu
  have hφs : ∀ m ∈ projImage (Sec4.slPi π 3 (p ^ e) K), ∃ x, φ x = m := by
    intro m hm
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hm
    have hu' : ProjGenLinGroup.mk (g * u * g⁻¹) ∈ projImage (Sec4.slPi π 3 (p ^ e) K) :=
      Subgroup.mem_map_of_mem _ (Sec4.conj_mem_slPi hπ hg hu)
    refine ⟨e'.symm ⟨_, hu'⟩, ?_⟩
    rw [hφ, MulEquiv.apply_symm_apply]
    show (ProjGenLinGroup.mk g)⁻¹ * ProjGenLinGroup.mk (g * u * g⁻¹) * ProjGenLinGroup.mk g = _
    rw [map_mul ProjGenLinGroup.mk, map_mul ProjGenLinGroup.mk, map_inv ProjGenLinGroup.mk]
    group
  have hφc : φ ⟨ch, hD.cY⟩ = ProjGenLinGroup.mk (Sec4.diagTau hτ) := by
    rw [hφ, hm₀g, map_mul ProjGenLinGroup.mk, map_mul ProjGenLinGroup.mk,
      map_inv ProjGenLinGroup.mk]
    group
  have hφb : ∀ (x : P) (hx : x ∈ Yh), φ ⟨bh * x * bh⁻¹, hD.normal.conj_mem x hx bh⟩ =
      ProjGenLinGroup.mk (Sec4.diagUnits a b c) * φ ⟨x, hx⟩ *
        (ProjGenLinGroup.mk (Sec4.diagUnits a b c))⁻¹ := by
    intro x hx
    rw [hφ, hφ, Hering129KH3.conj_compat e' hy hx, hyg, map_mul ProjGenLinGroup.mk,
      map_mul ProjGenLinGroup.mk, map_inv ProjGenLinGroup.mk]
    group
  obtain ⟨th, hφt⟩ : ∃ th : ↥Yh, φ th = ProjGenLinGroup.mk t := by
    have hT : ProjGenLinGroup.mk (g * t * g⁻¹) ∈ projImage (Sec4.slPi π 3 (p ^ e) K) :=
      Subgroup.mem_map_of_mem _ (Sec4.conj_mem_slPi hπ hg htS)
    refine ⟨e'.symm ⟨_, hT⟩, ?_⟩
    rw [hφ, MulEquiv.apply_symm_apply]
    show (ProjGenLinGroup.mk g)⁻¹ * ProjGenLinGroup.mk (g * t * g⁻¹) * ProjGenLinGroup.mk g = _
    rw [map_mul ProjGenLinGroup.mk, map_mul ProjGenLinGroup.mk, map_inv ProjGenLinGroup.mk]
    group
  refine ⟨th, th.2, ?_, ?_, ?_, fun Vh hVY hV hV9 hcV ⟨s, hs, hsV⟩ =>
    Hering129KN6.move_of_frame hK hq hτ hτ1 hφi hφL hφs hD.cY hφc hVY hV hV9 hcV hs hsV⟩
  ·
    have h : th ^ 2 = 1 := hφi (by
      rw [map_pow φ, hφt, map_one φ, ← map_pow ProjGenLinGroup.mk, sq, htt, map_one])
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  ·
    have h : (⟨bh * th * bh⁻¹, hD.normal.conj_mem _ th.2 bh⟩ : ↥Yh) = th := by
      apply hφi
      rw [hφb _ th.2, hφt, ← map_inv ProjGenLinGroup.mk, ← map_mul ProjGenLinGroup.mk,
        ← map_mul ProjGenLinGroup.mk, ← htD, mul_inv_cancel_right]
    have h' : bh * (th : P) * bh⁻¹ = th := congrArg Subtype.val h
    calc bh * (th : P) = bh * th * bh⁻¹ * bh := by group
      _ = th * bh := by rw [h']
  ·
    have h : th * ⟨ch, hD.cY⟩ * th⁻¹ = (⟨ch, hD.cY⟩ : ↥Yh)⁻¹ := by
      apply hφi
      rw [map_mul φ, map_mul φ, map_inv φ, map_inv φ, hφt, hφc, ← map_inv ProjGenLinGroup.mk,
        ← map_mul ProjGenLinGroup.mk, ← map_mul ProjGenLinGroup.mk, htd,
        map_mul ProjGenLinGroup.mk, ProjGenLinGroup.mk_scalar, one_mul, map_inv]
    exact congrArg Subtype.val h

end CFSG.RankThree.PartTwo.Sec12
