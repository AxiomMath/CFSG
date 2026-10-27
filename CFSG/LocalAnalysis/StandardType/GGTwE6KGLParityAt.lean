module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
import TauCeti.GroupTheory.DerivedCentralQuotient

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem largeEvenLabelAll_rawDatum_self (lab : LargeEvenLabel) :
    LargeEvenLabelAll lab fun R _ I F =>
      ∀ Φ : LargeEvenRawCont, Φ R I F → LargeEvenRawDatum lab Φ := by
  intro Q h
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact ⟨K, i1, i2, hK, b, c, hbc, hq, fun Φ hΦ => ⟨K, i1, i2, hK, b, c, hbc, hΦ⟩⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact ⟨K, i1, i2, hK, hq, fun Φ hΦ => ⟨K, i1, i2, hK, hΦ⟩⟩)

private theorem canonical_rawDatum_of_two_le {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hn : 2 ≤ lab.n) {Φ : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab Φ) : CFSG.Assembly.LargeEvenRawDatum lab Φ := by
  obtain ⟨tag, r, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  dsimp only at hn
  cases tag
  all_goals dsimp only [LargeEvenRawDatum, CFSG.Assembly.LargeEvenRawDatum] at h hl ⊢
  case G2der => exact absurd hl.2 (by omega)
  case twF4der => exact absurd hl.2 (by omega)
  case twF4 =>
    have h3 := hl.2.2
    obtain ⟨K, i1, i2, hK, hq⟩ := h
    exact ⟨K, i1, i2, hK, by rwa [if_neg (by omega)]⟩
  all_goals exact h

private theorem mulAut_mul_conj_mul_inv {R : Type} [Group R] (a : MulAut R) (r : R) :
    a * MulAut.conj r * a⁻¹ = MulAut.conj (a r) := by
  ext x
  simp [MulAut.conj_apply]


theorem largeEvenLabelAll_n_dvd_of_isComponentOf_ggFix {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      Finite R → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ s ∈ I, s ^ p = 1 → s ≠ 1 →
        ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) → ∀ lab' : LargeEvenLabel,
          (lab'.tag = .twD → 3 ≤ lab'.rank) →
          LargeEvenMarking ↥J₁ (fun l _ _ _ _ _ => l = lab') → lab.n ∣ lab'.n := by
  refine (largeEvenLabelAll_rawDatum_self lab).mono
    fun R _ I _ hself hR hna hfin p hp hp2 s hsI hsp hs1 J₁ hJ₁ lab' htwD hmark => ?_
  rcases Nat.lt_or_ge lab.n 2 with hn | hn
  · rw [show lab.n = 1 by have := hlab.1; omega]
    exact one_dvd _
  haveI := hR
  haveI := hfin
  haveI : Finite (MulAut R) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut R))
  have hnc : ¬ IsMulCommutative R := fun h => by
    obtain ⟨a, b, hab⟩ := hna
    exact hab (h.is_comm.comm a b)
  have hcen := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [← hcen, Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun β : MulAut R => β x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  let L := (MulAut.conj : R →* MulAut R).range
  let e : R ≃* ↥L := MonoidHom.ofInjective hinj
  have he : ∀ r : R, ((e r : ↥L) : MulAut R) = MulAut.conj r := fun _ => rfl
  have hfixc : ∀ r : R, MulAut.conj r * s⁻¹ = s⁻¹ * MulAut.conj r ↔ s r = r := by
    intro r
    rw [← hinj.eq_iff, ← mulAut_mul_conj_mul_inv]
    constructor
    · intro h
      rw [mul_assoc, h, ← mul_assoc, mul_inv_cancel, one_mul]
    · intro h
      calc MulAut.conj r * s⁻¹ = s⁻¹ * (s * MulAut.conj r * s⁻¹) := by group
        _ = s⁻¹ * MulAut.conj r := by rw [h]
  haveI : Group.IsPerfect R := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
  have hZL : Subgroup.center ↥L = ⊥ := CFSG.StandardType.center_eq_bot_of_mulEquiv e.symm hcen
  let θ : ↥L ⧸ Subgroup.center ↥L ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hZL).trans (QuotientGroup.quotientBot.trans e.symm)
  have hind : LargeEvenInduces θ (fun l l' : ↥L => (l' : MulAut R) = s⁻¹⁻¹ * l * s⁻¹) s := by
    intro l l' h
    obtain ⟨r, rfl⟩ := e.surjective l
    obtain ⟨r', rfl⟩ := e.surjective l'
    change s (e.symm (e r)) = e.symm (e r')
    rw [e.symm_apply_apply, e.symm_apply_apply]
    rw [he, he, inv_inv, mulAut_mul_conj_mul_inv] at h
    exact (hinj h).symm
  have hM : CFSG.LocalAnalysis.GLTheoremA.MarkedInnDiag L s⁻¹ lab :=
    ⟨(Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective).commutator_eq_top, lab,
      hlab, canonical_rawDatum_of_two_le hlab hn (hself _ ⟨hR, hna, θ, rfl, s, hsI, hind⟩)⟩
  have hyN : s⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut R)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨s⁻¹ r, (mulAut_mul_conj_mul_inv s⁻¹ r).symm⟩
    · rintro ⟨r, hr⟩
      refine ⟨s r, ?_⟩
      rw [← mulAut_mul_conj_mul_inv, hr]
      group
  have hyC : s⁻¹ ∉ Subgroup.centralizer (L : Set (MulAut R)) := fun h => hs1 <| by
    ext r
    simpa using (hfixc r).1 (Subgroup.mem_centralizer_iff.1 h (MulAut.conj r) ⟨r, rfl⟩)
  have hC : (ggFix s).map (MulAut.conj : R →* MulAut R) =
      L ⊓ Subgroup.centralizer ({s⁻¹} : Set (MulAut R)) := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ((hfixc r).2 (mem_ggFix.1 hr))⟩
    · rintro ⟨⟨r, rfl⟩, hc⟩
      exact ⟨r, mem_ggFix.2 ((hfixc r).1 (Subgroup.mem_centralizer_singleton_iff.1 hc)), rfl⟩
  have hK : CFSG.Open.IsComponentOf (J₁.map (MulAut.conj : R →* MulAut R))
      (L ⊓ Subgroup.centralizer ({s⁻¹} : Set (MulAut R))) := by
    rw [← hC]
    exact CFSG.Assembly.isComponentOf_iff_open.1 ⟨Subgroup.map_mono hJ₁.1,
      hJ₁.2.1.map (MulAut.conj : R →* MulAut R),
      CFSG.Assembly.IsQuasisimple.of_mulEquiv (J₁.equivMapOfInjective _ hinj).symm hJ₁.2.2⟩
  have hKlab : CFSG.LocalAnalysis.GLTheoremA.LabelOf (J₁.map (MulAut.conj : R →* MulAut R))
      lab' :=
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_congr (J₁.equivMapOfInjective _ hinj).symm
      (· = lab')).2 (largeEvenMarkingLegacy_to_canonical_carrier
        (P := fun l _ _ _ => l = lab') hmark)
  exact CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.subcompField_holds (MulAut R) L _ s⁻¹ lab
    lab' p hp hp2 (by rw [inv_pow, hsp, inv_one]) hyN hyC hM hK hKlab htwD

end CFSG.StandardType.SCFourCover

end
