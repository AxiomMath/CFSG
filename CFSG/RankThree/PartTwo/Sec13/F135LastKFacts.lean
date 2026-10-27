module

public import CFSG.RankThree.PartTwo.Sec13.F135LastLemmaF
public import CFSG.RankThree.PartTwo.Sec13.F135LastKDefs
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

theorem kf_hasTwoSix_of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : HasTwoSix S) : HasTwoSix S' := by
  obtain ⟨T, hT, hcard⟩ := h
  refine ⟨T.map e.toMonoidHom, ?_, ?_⟩
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := Subgroup.mem_map.mp ht
    rw [← map_mul, hT t0 ht0, map_one]
  · rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]

theorem kf_sq_iff_equivMap {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') (A : Subgroup S)
    (a : A) :
    a ^ 2 = 1 ↔ (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective a) ^ 2 = 1 := by
  have h1 : ((Subgroup.equivMapOfInjective A e.toMonoidHom e.injective a :
      ↥(A.map e.toMonoidHom)) : S') ^ 2 = e ((a : S) ^ 2) := by
    rw [map_pow]; rfl
  simp only [← Subtype.coe_inj, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [h1]
  exact e.map_eq_one_iff.symm

theorem kf_fourCubeSeven_map {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') {A : Subgroup S}
    {x : S} (h : FourCubeSeven A x) : FourCubeSeven (A.map e.toMonoidHom) (e x) := by
  obtain ⟨hcomm, hcard, hexp, hinv, hord, hnorm, hfix⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a' ha' b' hb'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]
  · intro a' ha'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [← map_pow, hexp a ha, map_one]
  · rw [← hinv]
    refine Nat.card_congr (Equiv.subtypeEquiv
      (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).toEquiv
      (fun a => kf_sq_iff_equivMap e A a)).symm
  · exact (orderOf_injective e.toMonoidHom e.injective x).trans hord
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have hx := (Subgroup.mem_normalizer_iff.mp hnorm) (e.symm h)
    have hconj : e.symm (e x * h * (e x)⁻¹) = x * e.symm h * x⁻¹ := by
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [hconj]
    exact hx
  · intro a' ha' h2 h3
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    have h2' : a ^ 2 = 1 := by
      rw [← map_pow] at h2
      exact e.injective (h2.trans (map_one e).symm)
    have h3' : x * a * x⁻¹ = a := by
      apply e.injective
      rw [map_mul, map_mul, map_inv]
      exact h3
    rw [hfix a ha h2' h3', map_one]

theorem hasTwoSix_or_fourCubeSeven_of_identification (h26 : KFactTwoSix) (h437 : KFactFourCubeSeven)
    {p : ℕ} {S : Type} [Group S] (hid : Identified p S) :
    HasTwoSix S ∨ ∃ (A : Subgroup S) (x : S), FourCubeSeven A x ∧ p = 7 := by
  rcases hid with ⟨hp, hHe | hON⟩ | ⟨_, hJ4⟩
  · obtain ⟨e⟩ := hHe
    exact Or.inl (@kf_hasTwoSix_of_mulEquiv He S Units.instGroup _ e.symm h26.1)
  · obtain ⟨e⟩ := hON
    obtain ⟨A, x, hA⟩ := h437
    exact Or.inr ⟨_, _, @kf_fourCubeSeven_map ON S Units.instGroup _ e.symm _ _ hA, hp⟩
  · obtain ⟨e⟩ := hJ4
    exact Or.inl (@kf_hasTwoSix_of_mulEquiv J4 S Units.instGroup _ e.symm h26.2)

theorem coprime_center_of_identification (hmult : KFactMultiplier) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {H : Type} [Group H] [Finite H] (J : Subgroup H) (hJ : CFSG.IsQuasisimple J)
    (hid : Identified p (↥J ⧸ Subgroup.center ↥J)) :
    Nat.Coprime (Nat.card (Subgroup.center J)) (2 * p) := by
  have hdisj : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* He) ∨
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ON) ∨ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* J4) := by
    rcases hid with ⟨_, h | h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have h3 : Nat.card (Subgroup.center ↥J) ∣ 3 := hmult ↥J hJ hdisj
  have h32 : Nat.Coprime 3 2 := by norm_num
  have h3p : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
  exact Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.mul_right h32 h3p)

@[expose] noncomputable def kf_act {H : Type*} [Group H] (J : Subgroup H) :
    ↥(normalizer (J : Set H)) →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
  (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (Subgroup.center ↥J)).comp
    J.normalizerMonoidHom

theorem kf_act_one_quot {H : Type*} [Group H] (J : Subgroup H)
    (n : ↥(normalizer (J : Set H))) (h : kf_act J n = 1) (s : ↥J) :
    QuotientGroup.mk' (Subgroup.center ↥J) (J.normalizerMonoidHom n s) =
      QuotientGroup.mk' (Subgroup.center ↥J) s := by
  have h2 : kf_act J n (QuotientGroup.mk' (Subgroup.center ↥J) s) =
      QuotientGroup.mk' (Subgroup.center ↥J) s := by
    rw [h]; rfl
  have h3 := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply
    (Subgroup.center ↥J) (J.normalizerMonoidHom n) s
  exact h3.symm.trans h2

theorem kf_comm_of_quot {H : Type*} [Group H] (J : Subgroup H) (g : H)
    (hg : g ∈ normalizer (J : Set H))
    (h : ∀ s : ↥J, QuotientGroup.mk' (Subgroup.center ↥J) (J.normalizerMonoidHom ⟨g, hg⟩ s) =
      QuotientGroup.mk' (Subgroup.center ↥J) s) :
    ∀ j ∈ J, ∀ k ∈ J, ⁅⁅j, g⁆, k⁆ = 1 := by
  intro j hj k hk
  have hs := QuotientGroup.eq.mp (h ⟨j⁻¹, J.inv_mem hj⟩)
  have hzk : k * ((g * j⁻¹ * g⁻¹)⁻¹ * j⁻¹) = ((g * j⁻¹ * g⁻¹)⁻¹ * j⁻¹) * k :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hs ⟨k, hk⟩)
  have hw : (g * j⁻¹ * g⁻¹)⁻¹ * j⁻¹ = ⁅g, j⁆ := by
    rw [commutatorElement_def]; group
  rw [hw] at hzk
  have hc : Commute ⁅g, j⁆ k := hzk.symm
  have hc' : Commute ⁅j, g⁆ k := by
    rw [← commutatorElement_inv]
    exact hc.inv_left
  exact commutatorElement_eq_one_iff_mul_comm.mpr hc'

theorem kf_mem_centralizer_of_act_one {H : Type*} [Group H] (J : Subgroup H)
    (hJ : CFSG.IsQuasisimple J) (e : H) (he : e ∈ normalizer (J : Set H))
    (h : kf_act J ⟨e, he⟩ = 1) : e ∈ centralizer (J : Set H) := by
  have hz := commute_of_trivial_mod_center J (Subgroup.isPerfect_iff.mp hJ.1) e he
    (kf_comm_of_quot J e he (kf_act_one_quot J ⟨e, he⟩ h))
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  exact commutatorElement_eq_one_iff_mul_comm.mp (hz j hj)

theorem kf_ker_le {H : Type*} [Group H] (J E : Subgroup H) (hJ : CFSG.IsQuasisimple J)
    (hEN : E ≤ normalizer (J : Set H)) :
    ((kf_act J).comp (Subgroup.inclusion hEN)).ker ≤ (centralizer (J : Set H) ⊓ E).subgroupOf E := by
  intro x hx
  have hx' : kf_act J (Subgroup.inclusion hEN x) = 1 := hx
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.mem_inf.mpr ⟨kf_mem_centralizer_of_act_one J hJ _ (hEN x.2) hx', x.2⟩

theorem kf_relIndex_le_card {H : Type*} [Group H] [Finite H] (J E : Subgroup H)
    (hJ : CFSG.IsQuasisimple J) (hEN : E ≤ normalizer (J : Set H)) :
    (centralizer (J : Set H) ⊓ E).relIndex E ≤
      Nat.card (((kf_act J).comp (Subgroup.inclusion hEN)).range) := by
  have h1 : Nat.card (((kf_act J).comp (Subgroup.inclusion hEN)).range) =
      ((kf_act J).comp (Subgroup.inclusion hEN)).ker.index :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv.symm
  rw [h1]
  haveI : ((kf_act J).comp (Subgroup.inclusion hEN)).ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.index_antitone (kf_ker_le J E hJ hEN)

theorem hK3_of_kfact (hK3 : KFactK3) {H : Type} [Group H] [Finite H] (J : Subgroup H)
    (hJ : CFSG.IsQuasisimple J) (E : Subgroup H) (p : ℕ) (hE : IsPGroup p E)
    (hEJ : ∀ e ∈ E, e ∈ normalizer (J : Set H))
    (hid : Identified p (↥J ⧸ Subgroup.center ↥J))
    (hcard : p ^ 3 ≤ (centralizer (J : Set H) ⊓ E).relIndex E) :
    ∀ g ∈ normalizer (J : Set H), g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) →
      ∀ j ∈ J, ∀ k ∈ J, ⁅⁅j, g⁆, k⁆ = 1 := by
  intro g hg hg3 hcomm
  have hEN : E ≤ normalizer (J : Set H) := fun e he => hEJ e he
  have hP : IsPGroup p ((kf_act J).comp (Subgroup.inclusion hEN)).range := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨k, hk⟩ := hE x
    refine ⟨k, Subtype.ext ?_⟩
    show ((kf_act J).comp (Subgroup.inclusion hEN) x) ^ p ^ k = 1
    rw [← map_pow, hk, map_one]
  have hPcard : p ^ 3 ≤ Nat.card ((kf_act J).comp (Subgroup.inclusion hEN)).range :=
    le_trans hcard (kf_relIndex_le_card J E hJ hEN)
  have hgg : (⟨g, hg⟩ : ↥(normalizer (J : Set H))) ^ 3 = 1 := Subtype.ext hg3
  have hα3 : kf_act J ⟨g, hg⟩ ^ 3 = 1 := by
    rw [← map_pow, hgg, map_one]
  have hcomm' : ∀ π ∈ ((kf_act J).comp (Subgroup.inclusion hEN)).range,
      kf_act J ⟨g, hg⟩ * π = π * kf_act J ⟨g, hg⟩ := by
    intro π hπ
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hπ
    change kf_act J ⟨g, hg⟩ * kf_act J (Subgroup.inclusion hEN x) =
      kf_act J (Subgroup.inclusion hEN x) * kf_act J ⟨g, hg⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm x x.2)
  have h1 : kf_act J ⟨g, hg⟩ = 1 :=
    hK3 (↥J ⧸ Subgroup.center ↥J) p hid _ hP hPcard _ hα3 hcomm'
  exact kf_comm_of_quot J g hg (kf_act_one_quot J ⟨g, hg⟩ h1)

end CFSG.RankThree.PartTwo.Sec13.F135Last
