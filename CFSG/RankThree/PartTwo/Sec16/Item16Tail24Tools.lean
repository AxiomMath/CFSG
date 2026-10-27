module

import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1624

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof (exists_isSylowOf_le
  exists_conj_of_isSylowOf)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def conjEnd {Q : Subgroup G} {x : G}
    (hxQ : x ∈ Subgroup.normalizer (Q : Set G)) : Q →* Q where
  toFun q := ⟨x * q * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxQ q).mp q.2⟩
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul]
    group

omit [Finite G] in
theorem coe_conjEnd_iterate {Q : Subgroup G} {x : G}
    (hxQ : x ∈ Subgroup.normalizer (Q : Set G)) (k : ℕ) (q : Q) :
    (((conjEnd hxQ)^[k] q : Q) : G) = x ^ k * q * (x ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change x * (((conjEnd hxQ)^[k] q : Q) : G) * x⁻¹ = _
    rw [ih, pow_succ']
    group

omit [Finite G] in
theorem map_commutator_subtype (Q : Subgroup G) :
    (_root_.commutator Q).map Q.subtype = ⁅Q, Q⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem inf_centralizer_le_commutator {Q : Subgroup G} {x : G}
    (hxQ : x ∈ Subgroup.normalizer (Q : Set G)) (hQ : Q = ⁅Q, Subgroup.zpowers x⁆) :
    Q ⊓ Subgroup.centralizer ({x} : Set G) ≤ ⁅Q, Q⁆ := by
  set σ := conjEnd hxQ with hσ
  set σb : Abelianization Q →* Abelianization Q := Abelianization.map σ with hσb
  set ψ : Abelianization Q →* Abelianization Q := σb / MonoidHom.id _ with hψ
  have hψa : ∀ a, ψ a = σb a / a := fun a => rfl
  have hiter : ∀ (k : ℕ) (q : Q),
      (σb^[k]) (Abelianization.of q) = Abelianization.of (σ^[k] q) := by
    intro k
    induction k with
    | zero => intro q; rfl
    | succ k ih =>
      intro q
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl
  have hrange : ∀ (k : ℕ) (a : Abelianization Q), (σb^[k]) a / a ∈ ψ.range := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      have h1 : (σb^[k + 1]) a / a = ψ ((σb^[k]) a) * ((σb^[k]) a / a) := by
        rw [hψa, Function.iterate_succ_apply', div_mul_div_cancel]
      rw [h1]
      exact mul_mem ⟨_, rfl⟩ (ih a)
  set R : Subgroup G := (ψ.range.comap (Abelianization.of)).map Q.subtype with hR
  have hQR : Q ≤ R := by
    refine hQ.le.trans ?_
    rw [Subgroup.commutator_le]
    intro g hg y hy
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
    refine ⟨⟨g, hg⟩ * ((σ^[k]) ⟨g, hg⟩)⁻¹, ?_, ?_⟩
    · change Abelianization.of (⟨g, hg⟩ * ((σ^[k]) ⟨g, hg⟩)⁻¹) ∈ ψ.range
      rw [map_mul, map_inv, ← hiter]
      have := inv_mem (hrange k (Abelianization.of ⟨g, hg⟩))
      rwa [inv_div, div_eq_mul_inv] at this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hσ,
        coe_conjEnd_iterate]
      rw [commutatorElement_def]
      group
  have hof : Function.Surjective (Abelianization.of (G := Q)) := fun a =>
    QuotientGroup.mk_surjective a
  have : Finite (Abelianization Q) := Finite.of_surjective _ hof
  have hsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨q, rfl⟩ := hof a
    obtain ⟨q', hq', hqq'⟩ := hQR q.2
    have : q' = q := Subtype.ext hqq'
    subst this
    exact hq'
  have hinj : Function.Injective ψ := Finite.injective_iff_surjective.mpr hsurj
  rintro g ⟨hgQ, hgC⟩
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hfix : σ ⟨g, hgQ⟩ = ⟨g, hgQ⟩ := by
    apply Subtype.ext
    change x * g * x⁻¹ = g
    rw [← hgx]
    group
  have hψ1 : ψ (Abelianization.of ⟨g, hgQ⟩) = ψ 1 := by
    rw [hψa, hψa, hσb, Abelianization.map_of, hfix, div_self', map_one, div_one]
  have hof1 := hinj hψ1
  have hker : (⟨g, hgQ⟩ : Q) ∈ _root_.commutator Q := by
    rw [← Abelianization.ker_of]
    exact hof1
  rw [← map_commutator_subtype]
  exact ⟨_, hker, rfl⟩

omit [Finite G] in
theorem zpowers_eq_of_card_eq_three {D : Subgroup G} (hD : Nat.card D = 3) {d : G}
    (hd : d ∈ D) (hd1 : d ≠ 1) : Subgroup.zpowers d = D := by
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; norm_num)
  have hle : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hd
  have hdvd : Nat.card (Subgroup.zpowers d) ∣ 3 := hD ▸ Subgroup.card_dvd_of_le hle
  have hne : Nat.card (Subgroup.zpowers d) ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one]
    intro hbot
    exact hd1 (by simpa [hbot] using Subgroup.mem_zpowers d)
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exact absurd h1 hne
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hD, h3])

theorem le_sup_commutator_of_forall_not_mem {Q E : Subgroup G} {c : G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : 9 ≤ Nat.card E)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G)) (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hc : Nat.card (Subgroup.zpowers c) = 3)
    (hcent : ∀ d ∈ E, d ∉ Subgroup.zpowers c →
      Q ⊓ Subgroup.centralizer ({d} : Set G) ≤ ⁅Q, Q⁆) :
    Q ≤ (Q ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ ⁅Q, Q⁆ := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E Q ⟨hE.1, hE.2⟩ (by norm_num; exact hE9) hEQ
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3)
  conv_lhs => rw [← hgen]
  refine iSup_le fun D => iSup_le fun hD => ?_
  obtain ⟨hDE, hD3⟩ := hD
  have hD3' : Nat.card D = 3 := by simpa using hD3
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hD3'
    norm_num at hD3'
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  have hDd := zpowers_eq_of_card_eq_three hD3' hdD hd1'
  by_cases hdc : d ∈ Subgroup.zpowers c
  · have hcD : c ∈ D := by
      rw [← hDd, Proof169.zpowers_eq_of_mem_of_ne_one hc hdc hd1']
      exact Subgroup.mem_zpowers c
    exact le_sup_of_le_left
      (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcD)))
  · exact le_sup_of_le_right
      ((inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdD))).trans
        (hcent d (hDE hdD) hdc))

theorem le_of_le_sup_commutator {Q H : Subgroup G} {p : ℕ} [Fact p.Prime] (hQ : IsPGroup p Q)
    (hHQ : H ≤ Q) (hle : Q ≤ H ⊔ ⁅Q, Q⁆) : Q ≤ H := by
  have : Fact (IsPGroup p Q) := ⟨hQ⟩
  have hQQ : ⁅Q, Q⁆ ≤ Q := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hcomm : (⁅Q, Q⁆).subgroupOf Q = _root_.commutator Q := by
    rw [← map_commutator_subtype, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective Q.subtype_injective]
  have hsup : H.subgroupOf Q ⊔ frattini Q = ⊤ := by
    rw [eq_top_iff]
    have h1 : (⊤ : Subgroup Q) ≤ (H ⊔ ⁅Q, Q⁆).subgroupOf Q := by
      intro q _
      exact Subgroup.mem_subgroupOf.mpr (hle q.2)
    rw [Subgroup.subgroupOf_sup hHQ hQQ, hcomm] at h1
    exact h1.trans (sup_le_sup_left (CFSG.commutator_le_frattini_of_isPGroup (p := p)) _)
  have htop := CFSG.lemma_1_7_a (p := p) _ hsup
  intro q hq
  have hq' : (⟨q, hq⟩ : Q) ∈ H.subgroupOf Q := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hq'

theorem le_centralizer_of_coprime {Q E : Subgroup G} {x c : G} (hQ : IsPGroup 2 Q)
    (hxQ : x ∈ Subgroup.normalizer (Q : Set G)) (hQX : Q = ⁅Q, Subgroup.zpowers x⁆)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : 9 ≤ Nat.card E)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G)) (hc : Nat.card (Subgroup.zpowers c) = 3)
    (hcent : ∀ d ∈ E, d ∉ Subgroup.zpowers c →
      Q ⊓ Subgroup.centralizer ({d} : Set G) ≤ Subgroup.centralizer ({x} : Set G)) :
    Q ≤ Subgroup.centralizer ({c} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := inf_centralizer_le_commutator hxQ hQX
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    rw [hk]
    intro h3
    have := (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have h2 := le_sup_commutator_of_forall_not_mem hE hE9 hEQ hQ3 hc fun d hd hdc => by
    intro q hq
    exact h1 ⟨hq.1, hcent d hd hdc hq⟩
  exact (le_of_le_sup_commutator hQ inf_le_left h2).trans inf_le_right

theorem le_of_isPerfect_of_le_sup {K O J : Subgroup G}
    (hOK : O ≤ Subgroup.normalizer (K : Set G)) (hO : IsPGroup 2 O) (hJ : Group.IsPerfect J)
    (hJKO : J ≤ K ⊔ O) : J ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := K ⊔ O with hY
  have hKY : K ≤ Y := le_sup_left
  have hOY : O ≤ Y := le_sup_right
  have hKn : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mpr (sup_le Subgroup.le_normalizer hOK)
  have hsolv : Group.IsSolvable (↥Y ⧸ K.subgroupOf Y) := by
    let f : ↥O →* ↥Y ⧸ K.subgroupOf Y :=
      (QuotientGroup.mk' (K.subgroupOf Y)).comp (Subgroup.inclusion hOY)
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf Y) z
      have hy : (y : G) ∈ ((K : Set G) * (O : Set G)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left K O hOK]
        exact y.2
      obtain ⟨k, hk, o, ho, hko⟩ := hy
      refine ⟨⟨o, ho⟩, ?_⟩
      change QuotientGroup.mk' (K.subgroupOf Y) (Subgroup.inclusion hOY ⟨o, ho⟩) =
        QuotientGroup.mk' (K.subgroupOf Y) y
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have hyk : (y : G) = k * o := hko.symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hyk]
      have hk' : o⁻¹ * k * o⁻¹⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (inv_mem (hOK ho)) k).mp hk
      simpa [mul_assoc] using hk'
    have : Group.IsNilpotent ↥O := hO.isNilpotent
    exact Group.isSolvable_of_surjective hf
  have hJ' : Group.IsPerfect (J.subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJKO).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have h1 := (CFSG.perfect_residual_transport (MonoidHom.id ↥Y)).2.2 (J.subgroupOf Y) hJ'
  have h2 := ((CFSG.perfect_residual_characterization (G := ↥Y)).2.2.2.2.1 (K.subgroupOf Y)).mp
    hsolv
  intro j hj
  have := h2 (h1 (show (⟨j, hJKO hj⟩ : Y) ∈ J.subgroupOf Y from hj))
  exact this

theorem le_normalizer_of_frattini {M D K : Subgroup G} {c : G} (hcD : c ∈ D) (hDM : D ≤ M)
    (hMD : M ≤ Subgroup.normalizer (D : Set G)) (hc : orderOf c = 3)
    (hcyc : ∀ S : Sylow 3 ↥D, IsCyclic ↥(S : Subgroup ↥D))
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hHK : M ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (K : Set G)) :
    M ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcP : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨S, hS, hcS⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr hcD) hcP
  have hScyc : IsCyclic ↥S := by
    obtain ⟨S₀, hS₀⟩ := hS
    have := hcyc S₀
    rw [← hS₀]
    exact isCyclic_of_surjective ((S₀ : Subgroup D).equivMapOfInjective D.subtype
      D.subtype_injective).toMonoidHom (MulEquiv.surjective _)
  intro m hm
  set S' := S.map (MulAut.conj m).toMonoidHom with hS'
  have hS'D : S' ≤ D := by
    calc S' ≤ D.map (MulAut.conj m).toMonoidHom := Subgroup.map_mono hS.le
      _ = D := Late.map_conj_eq_of_mem_normalizer (hMD hm)
  have hS'syl : IsSylowOf 3 S' D := isSylowOf_of_card hS'D (by
    rw [hS', Subgroup.card_map_of_injective (MulAut.conj m).injective]
    exact hS.card_eq)
  obtain ⟨d, hdD, hdS⟩ := exists_conj_of_isSylowOf hS hS'syl
  set n := d⁻¹ * m with hn
  have hnS : S.map (MulAut.conj n).toMonoidHom = S := by
    have h1 : (S.map (MulAut.conj m).toMonoidHom).map (MulAut.conj d⁻¹).toMonoidHom =
        (S.map (MulAut.conj d).toMonoidHom).map (MulAut.conj d⁻¹).toMonoidHom := by
      rw [← hS', hdS]
    rwa [Late.map_conj_map_conj, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
      at h1
  have hncS : n * c * n⁻¹ ∈ S := by
    rw [← hnS]
    exact ⟨c, hcS (Subgroup.mem_zpowers c), rfl⟩
  have hncord : orderOf (n * c * n⁻¹) = 3 := by
    rw [show n * c * n⁻¹ = (MulAut.conj n) c from rfl, MulEquiv.orderOf_eq, hc]
  have heq : Subgroup.zpowers (n * c * n⁻¹) = Subgroup.zpowers c := by
    have h1 : (Subgroup.zpowers (n * c * n⁻¹)).subgroupOf S =
        (Subgroup.zpowers c).subgroupOf S := by
      rw [IsCyclic.subgroup_eq_iff_card_eq,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hncS)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcS).toEquiv, Nat.card_zpowers,
        Nat.card_zpowers, hncord, hc]
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (Subgroup.zpowers_le.mpr hncS),
      inf_of_le_left hcS] at h1
    exact h1
  have hnc : n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    exact heq
  have hnM : n ∈ M := mul_mem (inv_mem (hDM hdD)) hm
  have hm' : m = d * n := by rw [hn, mul_inv_cancel_left]
  rw [hm']
  exact mul_mem (hDK hdD) (hHK ⟨hnM, hnc⟩)

end CFSG.RankThree.PartTwo.Sec16.Proof1624
