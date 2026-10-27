module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxLang
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxRational
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxSL2
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxTorus
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.E6

open scoped Matrix

section Count


theorem natCard_eq_torsion {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K L : Type} [Field K] [Finite K]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E)
    (w : WeylGroup τ) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL τ L)
    (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w)
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K L) ((x : adjointGroup τ K) : ModGL τ K) ∈
      (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr).map (MulAut.conj g0).toMonoidHom) :
    Nat.card E = Nat.card {x : ModGL τ L //
      x ∈ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr ∧ x ^ p = 1} := by
  classical
  have hι_inj : ∀ a b : ModGL τ K, baseChangeGL (algebraMap K L) a =
      baseChangeGL (algebraMap K L) b → a = b := fun a b h => baseChangeGL_injective _ h
  have hT : ∀ x : E, ∃ t ∈ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr,
      g0 * t * g0⁻¹ = baseChangeGL (algebraMap K L) ((x : adjointGroup τ K) : ModGL τ K) :=
    fun x => Subgroup.mem_map.1 (hEin x x.2)
  have hmem : ∀ x : E, g0⁻¹ * baseChangeGL (algebraMap K L) ((x : adjointGroup τ K) : ModGL τ K) *
      g0 ∈ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr := by
    intro x
    obtain ⟨t, ht, htx⟩ := hT x
    rw [← htx]
    have : g0⁻¹ * (g0 * t * g0⁻¹) * g0 = t := by group
    rw [this]
    exact ht
  have hpow : ∀ x : E, (g0⁻¹ * baseChangeGL (algebraMap K L)
      ((x : adjointGroup τ K) : ModGL τ K) * g0) ^ p = 1 := by
    intro x
    have h1 : ((x : adjointGroup τ K) : ModGL τ K) ^ p = 1 := congrArg Subtype.val (hE.2 x x.2)
    have := conj_pow (a := g0⁻¹) (b := baseChangeGL (algebraMap K L)
      ((x : adjointGroup τ K) : ModGL τ K)) (i := p)
    rw [inv_inv] at this
    rw [this, ← map_pow, h1, map_one]
    group
  let f : E → {x : ModGL τ L //
      x ∈ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr ∧ x ^ p = 1} :=
    fun x => ⟨_, hmem x, hpow x⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : g0⁻¹ * baseChangeGL (algebraMap K L) ((x : adjointGroup τ K) : ModGL τ K) * g0 =
        g0⁻¹ * baseChangeGL (algebraMap K L) ((y : adjointGroup τ K) : ModGL τ K) * g0 :=
      congrArg Subtype.val hxy
    have h2 : baseChangeGL (algebraMap K L) ((x : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K L) ((y : adjointGroup τ K) : ModGL τ K) := by
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    exact Subtype.ext (Subtype.ext (hι_inj _ _ h2))
  have hsurj : Function.Surjective f := by
    rintro ⟨t, ht, htp⟩
    have htC : t ∈ adjointGroup τ L := twistedTorusOf_le_adjointGroup _ _ ht
    have hyC : g0 * t * g0⁻¹ ∈ adjointGroup τ L := mul_mem (mul_mem hg0C htC) (inv_mem hg0C)
    have hyp : (g0 * t * g0⁻¹) ^ p = 1 := by
      rw [conj_pow, htp]
      group
    have hyΦ : Units.map (entrywiseHom Fr) (g0 * t * g0⁻¹) = g0 * t * g0⁻¹ := by
      have ht2 : canonicalRep (coxeterSystem τ) L w * Units.map (entrywiseHom Fr) t *
          (canonicalRep (coxeterSystem τ) L w)⁻¹ = t := (mem_twistedTorus.1 ht).2
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * canonicalRep (coxeterSystem τ) L w * Units.map (entrywiseHom Fr) t *
            (g0 * canonicalRep (coxeterSystem τ) L w)⁻¹
          = g0 * (canonicalRep (coxeterSystem τ) L w * Units.map (entrywiseHom Fr) t *
              (canonicalRep (coxeterSystem τ) L w)⁻¹) * g0⁻¹ := by group
        _ = g0 * t * g0⁻¹ := by rw [ht2]
    obtain ⟨c, hc⟩ := exists_rational_of_fixed_pTorsion hτ hp hp2 Fr hFr hyC hyΦ hyp
    have hcE : c ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨s, hs, hsx⟩ := hT ⟨x, hx⟩
      have hts : s * t = t * s := by
        have := (isMulCommutative_twistedTorus (L := L) w Fr).is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩
        exact congrArg Subtype.val this
      have h3 : baseChangeGL (algebraMap K L) (x : ModGL τ K) *
          baseChangeGL (algebraMap K L) (c : ModGL τ K) =
          baseChangeGL (algebraMap K L) (c : ModGL τ K) *
            baseChangeGL (algebraMap K L) (x : ModGL τ K) := by
        rw [hc, ← hsx]
        calc g0 * s * g0⁻¹ * (g0 * t * g0⁻¹) = g0 * (s * t) * g0⁻¹ := by group
          _ = g0 * (t * s) * g0⁻¹ := by rw [hts]
          _ = g0 * t * g0⁻¹ * (g0 * s * g0⁻¹) := by group
      have h4 : (x : ModGL τ K) * (c : ModGL τ K) = (c : ModGL τ K) * (x : ModGL τ K) := by
        apply hι_inj
        rw [map_mul, map_mul]
        exact h3
      exact Subtype.ext h4
    have hcp : c ^ p = 1 := by
      apply Subtype.ext
      apply hι_inj
      rw [Subgroup.coe_pow, map_pow, hc, hyp, Subgroup.coe_one, map_one]
    have hcEmem : c ∈ E := hSC c hcE hcp
    refine ⟨⟨c, hcEmem⟩, Subtype.ext ?_⟩
    change g0⁻¹ * baseChangeGL (algebraMap K L) ((c : adjointGroup τ K) : ModGL τ K) * g0 = t
    rw [hc]
    group
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

theorem card_ge_of_toral {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hbar : BigElemAbelianToralBar τ p) (hroot : HalfMaxFixedRoot τ p) (K : Type)
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E)
    (hcard : p ^ (τ.rank - 1) ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E) :
    p ^ τ.rank ≤ Nat.card E := by
  classical
  have hpK : ¬ p ∣ Nat.card K := by
    intro h
    have h1 : p ∣ 1 := (Nat.dvd_add_right h).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hEin⟩ :=
    exists_langTorus_of_toral_bar hp hbar K hpK E hE hcard
  have hcount := natCard_eq_torsion hτ hp hp2 E hE hSC w Fr hFr g0 hg0C hg0 hEin
  have hCharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hcard2 := natCard_twistedTorus_pTorsion (L := AlgebraicClosure K) (τ := τ) (ℓ := 2)
    Nat.prime_two Fr hFr hp hp2 w
  have hq : ((Nat.card K : ℕ) : ZMod p) = -1 := by
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  rw [hq] at hcard2
  have hE' := hcount.trans hcard2
  by_contra hlt
  push Not at hlt
  obtain ⟨β, hβ, hwβ⟩ := hroot w (hE' ▸ hcard) (hE' ▸ hlt)
  exact false_of_fixed_root hτ hp hp2 hpq E hE hSC w Fr hFr g0 hg0C hg0 hEin hβ hwβ

end Count

end ExcFramesHalf

end CFSG.StandardType
