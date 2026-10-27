module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKL3OutA
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Sub
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Subgroup
open CFSG.Quasithin.H13.L829NK.L3OutA
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.L3Aut

theorem nk_l3odd_out :
    ∀ (p : ℕ), p.Prime → 7 ≤ p → p % 4 = 3 → ∀ (X : Type) [Group X], IsPSL 3 p 1 X →
      ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
        UOut X (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X)) := by
  intro p hp h7 hp4 X _ hX S hS
  unfold UOut
  intro y hy hfix
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hX
  let φ : X ≃* projectiveSL 3 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  haveI : Finite X := Finite.of_equiv _ φ.symm.toEquiv
  haveI : Fact p.Prime := ⟨hp⟩
  have hcharK : CharP K p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hp3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h2 : (2 : K) ≠ 0 := fun h => hp2 ((CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h))
  have h3 : (3 : K) ≠ 0 := fun h => hp3 ((CharP.cast_eq_zero_iff K p 3).mp (by exact_mod_cast h))
  have hσ : ∀ σ : K ≃+* K, σ = 1 := by
    intro σ
    have hcard1 : Nat.card (K ≃+* K) = 1 :=
      CFSG.ComponentClassification.AutL2Facts.card_ringAut (F := K) hp hK
    exact (Nat.card_eq_one_iff_unique.mp hcard1).1.elim σ 1
  let HX : Subgroup X := (HP (K := K)).comap φ.toMonoidHom
  have hHX : IsPGroup 2 HX := by
    intro g
    have hg : φ g.1 ∈ HP (K := K) := g.2
    obtain ⟨k, hk⟩ := isPGroup_HP (K := K) ⟨φ g.1, hg⟩
    refine ⟨k, ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at hk'
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    apply φ.injective
    rw [map_pow, map_one]
    exact hk'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hHX
  have hQS : IsSylowTwoOf (Q : Subgroup X) ⊤ := by
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [show ((Q : Subgroup X).subgroupOf ⊤).index = (Q : Subgroup X).index from
      Subgroup.relIndex_top_right _]
    exact Sylow.not_dvd_index Q
  obtain ⟨g, hgS⟩ := exists_conj_of_isSylowTwoOf_top_cs5 hQS hS
  have hconj : ∀ h ∈ HX, g * h * g⁻¹ ∈ S := by
    intro h hh
    rw [hgS]
    exact Subgroup.mem_map.mpr ⟨h, hQ hh, by simp [MulAut.conj_apply]⟩
  have hkey : ∀ b : X, (∀ s ∈ S, s * b = b * s) →
      ∀ u ∈ HX, u * (g⁻¹ * b * g) = (g⁻¹ * b * g) * u := by
    intro b hb u hu
    have h1 := hb (g * u * g⁻¹) (hconj u hu)
    calc u * (g⁻¹ * b * g) = g⁻¹ * ((g * u * g⁻¹) * b) * g := by group
      _ = g⁻¹ * (b * (g * u * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * b * g) * u := by group
  have hmHP : ∀ b : X, (∀ s ∈ S, s * b = b * s) →
      ∀ h ∈ HP (K := K), φ (g⁻¹ * b * g) * h = h * φ (g⁻¹ * b * g) := by
    intro b hb h hh
    have hu : φ.symm h ∈ HX := by
      show φ (φ.symm h) ∈ HP (K := K)
      rw [φ.apply_symm_apply]
      exact hh
    have hc := hkey b hb (φ.symm h) hu
    obtain ⟨m', hm'⟩ : ∃ m' : X, g⁻¹ * b * g = m' := ⟨_, rfl⟩
    rw [hm'] at hc ⊢
    have hc2 : φ (φ.symm h * m') = φ (m' * φ.symm h) := by rw [hc]
    simp only [map_mul, φ.apply_symm_apply] at hc2
    exact hc2.symm
  have hd0 : proj 3 K (d0SL (K := K)) ∈ HP (K := K) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hw0 : proj 3 K (wSL (K := K)) ∈ HP (K := K) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hconjlem : ∀ (b m' t : X), g⁻¹ * b * g = m' → m' * t = t * m' →
      b * (g * t * g⁻¹) = (g * t * g⁻¹) * b := by
    intro b m' t hm' hmt
    rw [← hm'] at hmt
    calc b * (g * t * g⁻¹) = g * ((g⁻¹ * b * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * b * g)) * g⁻¹ := by rw [hmt]
      _ = (g * t * g⁻¹) * b := by group
  have hwt_all : ∀ b : X, (∀ s ∈ S, s * b = b * s) →
      (∀ a b' : Kˣ, b * (g * φ.symm (proj 3 K (diagSL (K := K) a b')) * g⁻¹) =
          (g * φ.symm (proj 3 K (diagSL (K := K) a b')) * g⁻¹) * b) ∧
        b * (g * φ.symm (proj 3 K (x12 (1 : K))) * g⁻¹) =
          (g * φ.symm (proj 3 K (x12 (1 : K))) * g⁻¹) * b := by
    intro b hb
    obtain ⟨hd', hw'⟩ := commute_tests h2 (φ (g⁻¹ * b * g)) (hmHP b hb _ hd0) (hmHP b hb _ hw0)
    refine ⟨fun a b' => ?_, ?_⟩
    · apply hconjlem b (g⁻¹ * b * g) (φ.symm (proj 3 K (diagSL (K := K) a b'))) rfl
      apply φ.injective
      have hm := hd' a b'
      simp only [map_mul, φ.apply_symm_apply]
      simp only [map_mul, φ.apply_symm_apply] at hm
      exact hm
    · apply hconjlem b (g⁻¹ * b * g) (φ.symm (proj 3 K (x12 (1 : K)))) rfl
      apply φ.injective
      simp only [map_mul, φ.apply_symm_apply]
      simp only [map_mul, φ.apply_symm_apply] at hw'
      exact hw'
  have hyfix : ∀ w : X, (∀ h ∈ S ⊓ centralizer (S : Set X), h * w = w * h) → y w = w := by
    intro w hw
    apply hfix w
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hw h hh
  have hbS : ∀ h ∈ S ⊓ centralizer (S : Set X), ∀ s ∈ S, s * h = h * s := fun h hh s hs =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2 s hs
  have hyT : ∀ a b' : Kˣ, y (g * φ.symm (proj 3 K (diagSL (K := K) a b')) * g⁻¹) =
      g * φ.symm (proj 3 K (diagSL (K := K) a b')) * g⁻¹ := fun a b' =>
    hyfix _ (fun h hh => (hwt_all h (hbS h hh)).1 a b')
  have hyX : y (g * φ.symm (proj 3 K (x12 (1 : K))) * g⁻¹) =
      g * φ.symm (proj 3 K (x12 (1 : K))) * g⁻¹ :=
    hyfix _ (fun h hh => (hwt_all h (hbS h hh)).2)
  set y' : MulAut X := (MulAut.conj g)⁻¹ * y * MulAut.conj g with hy'def
  have hinv_apply : ∀ z : X, (MulAut.conj g)⁻¹ z = g⁻¹ * z * g := fun z => by
    rw [← map_inv, MulAut.conj_apply, inv_inv]
  have hy'T : ∀ a b' : Kˣ, y' (φ.symm (proj 3 K (diagSL (K := K) a b'))) =
      φ.symm (proj 3 K (diagSL (K := K) a b')) := by
    intro a b'
    rw [hy'def, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hyT a b', hinv_apply]
    group
  have hy'X : y' (φ.symm (proj 3 K (x12 (1 : K)))) = φ.symm (proj 3 K (x12 (1 : K))) := by
    rw [hy'def, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hyX, hinv_apply]
    group
  have hy'2 : y' * y' = 1 := by
    rw [hy'def]
    calc (MulAut.conj g)⁻¹ * y * MulAut.conj g * ((MulAut.conj g)⁻¹ * y * MulAut.conj g)
        = (MulAut.conj g)⁻¹ * (y * y) * MulAut.conj g := by group
      _ = 1 := by rw [hy, mul_one, inv_mul_cancel]
  set ψ : MulAut (projectiveSL 3 K) := MulAut.congr φ y' with hψdef
  have hψ2 : ψ * ψ = 1 := by
    rw [hψdef, ← map_mul, hy'2, map_one]
  have hψapp : ∀ t : projectiveSL 3 K, ψ t = φ (y' (φ.symm t)) := fun t => rfl
  have hψt : ∀ t : projectiveSL 3 K, y' (φ.symm t) = φ.symm t → ψ t = t := by
    intro t ht
    rw [hψapp, ht, φ.apply_symm_apply]
  have hψd : ∀ a b' : Kˣ, ψ (proj 3 K (diagSL (K := K) a b')) = proj 3 K (diagSL (K := K) a b') :=
    fun a b' => hψt _ (hy'T a b')
  have hψx : ψ (proj 3 K (x12 (1 : K))) = proj 3 K (x12 (1 : K)) := hψt _ hy'X
  obtain ⟨xP, hxP⟩ := torus_inner h2 h3 hσ ψ hψ2 hψd hψx
  have hy'conj : y' = MulAut.conj (φ.symm xP) := by
    apply MulEquiv.ext
    intro z
    have h1 : ψ (φ z) = φ (y' z) := by
      rw [hψapp, φ.symm_apply_apply]
    have h2' : ψ (φ z) = xP * φ z * xP⁻¹ := by
      rw [hxP, MulAut.conj_apply]
    apply φ.injective
    rw [← h1, h2', MulAut.conj_apply, map_mul, map_mul, map_inv, φ.apply_symm_apply]
  refine ⟨g * φ.symm xP * g⁻¹, ?_⟩
  have hy_eq : y = (MulAut.conj g) * y' * (MulAut.conj g)⁻¹ := by
    rw [hy'def]
    group
  rw [hy_eq, hy'conj, ← map_inv, ← map_mul, ← map_mul]

end CFSG.Quasithin.H13.L829NK
