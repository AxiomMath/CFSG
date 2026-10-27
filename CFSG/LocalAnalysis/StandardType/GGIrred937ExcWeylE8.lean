module

public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcLang
public import CFSG.LieType.Chevalley.OrdinaryEAlgebraicTorusCartanIndex
public import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly

section Weyl

theorem exists_realization_E8
    {p : ℕ} [Fact p.Prime] (K : Type) [Field K] [Finite K] [CharP K 2]
    (E : Subgroup (adjointGroup .E8 K)) (hF : LangFrameData .E8 p K E) :
    ∃ (ι₀ : Multiplicative (Fin Tag.E8.rank → ZMod p) →* adjointGroup .E8 K)
      (m : Fin Tag.E8.rank → adjointGroup .E8 K), Function.Injective ι₀ ∧ ι₀.range = E ∧
      ∀ (i : Fin Tag.E8.rank) (s : Fin Tag.E8.rank → ZMod p),
        m i * ι₀ (Multiplicative.ofAdd s) * (m i)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct Tag.E8 p (simple Tag.E8 i) s)) := by
  classical
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hcent, _hζo, hι₀, hrange, hbase⟩ := hF
  haveI hCharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr_bij : Function.Bijective Fr :=
    frobenius_bijective (k := K) (L := AlgebraicClosure K) Fr hFr
  set σ : AlgebraicClosure K ≃+* AlgebraicClosure K := RingEquiv.ofBijective Fr hFr_bij with hσdef
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hmul : ∀ a b : WeylGroup Tag.E8,
      canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) (a * b) =
        canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) a *
          canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) b :=
    fun a b => RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (τ := Tag.E8)
      (R := AlgebraicClosure K) a b
  have hFr_canon : ∀ v : WeylGroup Tag.E8,
      Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v) =
        canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v :=
    fun v => by
      simpa only [hσ] using entrywise_canonicalRep (τ := Tag.E8) σ v
  have hinv : ∀ a : WeylGroup Tag.E8,
      canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) a⁻¹ =
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) a)⁻¹ := by
    intro a
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, inv_mul_cancel, canonicalRep_one]
  have hconj_fixed : ∀ v : WeylGroup Tag.E8,
      Units.map (entrywiseHom Fr)
          (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹) =
        g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹ := by
    intro v
    have hwv : (w * v) * w⁻¹ = v := by
      rw [← hcent v]; group
    have hkey : canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w *
        canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v *
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w)⁻¹ =
        canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v := by
      rw [← hinv, ← hmul, ← hmul, hwv]
    calc Units.map (entrywiseHom Fr)
          (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹)
        = (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w) *
            canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v *
            (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg0, hFr_canon v]
      _ = g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹ := by
          rw [show (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w) *
                canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v *
                (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w)⁻¹ =
              g0 * (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w *
                canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v *
                (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ by group,
            hkey]
  have hex : ∀ i : Fin Tag.E8.rank,
      ∃ c : adjointGroup Tag.E8 K,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.E8 K) =
          g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) (simple Tag.E8 i) *
            g0⁻¹ := by
    intro i
    set v : WeylGroup Tag.E8 := simple Tag.E8 i with hv
    have hvv : v * v = 1 := by
      rw [hv]; exact (coxeterSystem Tag.E8).simple_mul_simple_self i
    have hn2 : canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v ^ 2 = 1 := by
      rw [sq, ← hmul, hvv, canonicalRep_one]
    have hx2 : (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹) ^ 2 = 1 := by
      rw [sq, show (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹) *
            (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹) =
          g0 * (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v *
            canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v) * g0⁻¹ by group,
        ← sq, hn2, mul_one, mul_inv_cancel]
    haveI : Finite (Subgroup.zpowers
        (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹)) :=
      finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, hx2⟩)
    have hxC : g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹ ∈
        adjointGroup Tag.E8 (AlgebraicClosure K) :=
      mul_mem (mul_mem hg0C
        (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E8) (AlgebraicClosure K) v)) (inv_mem hg0C)
    have hXC : Subgroup.zpowers
        (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹) ≤
        adjointGroup Tag.E8 (AlgebraicClosure K) := (Subgroup.zpowers_le).2 hxC
    have hXF : ∀ y ∈ Subgroup.zpowers
          (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹),
        Units.map (entrywiseHom Fr) y = y := by
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [map_zpow, hconj_fixed v]
    have hrel := (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect
      (τ := Tag.E8) (K := K) (L := AlgebraicClosure K) 1
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr
      (Subgroup.zpowers (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹))
      hXC hXF).1
    have hle := Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1 hrel)
    obtain ⟨c, hc, hcx⟩ :=
      hle (Subgroup.mem_zpowers
        (g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) v * g0⁻¹))
    exact ⟨⟨c, hc⟩, by simpa [hv] using hcx⟩
  choose m hm using hex
  refine ⟨ι₀, m, hι₀, hrange, ?_⟩
  intro i s
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  have hcomp : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((m i * ι₀ (Multiplicative.ofAdd s) * (m i)⁻¹ :
            adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
      g0 * (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) (simple Tag.E8 i) *
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s *
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) (simple Tag.E8 i))⁻¹) * g0⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hm i, hbase s]
    group
  rw [hcomp, ExcFrames.canonicalRep_conj_frameDiag]
  exact (hbase (TableBExc.torusAct Tag.E8 p (simple Tag.E8 i) s)).symm

end Weyl

end Irred937

end CFSG.StandardType
