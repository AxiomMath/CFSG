module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Inner
public import Certificates.Certificate14971
public import Certificates.Certificate14979
import CFSG.RankThree.PartOne.A6N.Final
import CFSG.RankThree.PartOne.N1322.CaseA6
import CFSG.RankThree.PartOne.NF7H.StabSwap
import CFSG.RankThree.PartOne.NF7H.SwapFin

public section

namespace CFSG.StandardType.ZS.DimThree

open Subgroup CFSG.RankThree.PartOne CFSG.RepresentationTheory
open CFSG.RankThree.PartOne.LIT (autGL)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem center_pow_three_z6 {p : ℕ} [Fact p.Prime]
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hZ3 : Nat.card (Subgroup.center H) = 3)
    {z : H} (hz : z ∈ Subgroup.center H) : z ^ 3 = 1 := by
  have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center H)
  rw [hZ3] at h1
  have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
  simpa using congrArg (fun w : Subgroup.center H => (w : H)) h2

private theorem a6_orderOf_mul_le_five_z6 (a b : alternatingGroup (Fin 6)) :
    orderOf (a * b) ≤ 5 := by
  rcases N1322.A6_orders (a * b) with h2 | h3 | h4 | h5
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)).trans (by norm_num)
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)).trans (by norm_num)
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h4)).trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h5)

private theorem a6_hatt_z6 :
    ∃ a b : alternatingGroup (Fin 6), a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧
      orderOf (a * b) = 5 := by
  obtain ⟨x, y, hx2, hx1, hy2, hy1, hxy5, hxy1⟩ := N1322.A6_ord5
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨x, y, hx2, hx1, hy2, hy1, orderOf_eq_prime hxy5 hxy1⟩

private theorem a6_hone_z6 :
    ∀ a b : alternatingGroup (Fin 6), a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
      IsConj a b :=
  fun a b ha ha1 hb hb1 => isConj_iff.mpr (N1322.A6_conj a b ha ha1 hb hb1)


private theorem dec_z6 {p : ℕ} [Fact p.Prime]
    {H : Subgroup (GL (Fin 3) (ZMod p))} [Group.IsPerfect H]
    {G : Subgroup (GL (Fin 3) (ZMod p))} (hp5 : 5 ≤ p)
    (hn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) (hZ3 : Nat.card (Subgroup.center H) = 3)
    (e6 : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) :
    ∀ t ∈ G, ∃ h₀ ∈ H, ∃ z : GL (Fin 3) (ZMod p),
      (∀ x ∈ H, z * x = x * z) ∧ t = h₀ * z := by
  intro t htG
  obtain ⟨h₀, hh₀, z, hzc, htz⟩ :=
    CFSG.RankThree.PartOne.A6N.kf1322ThreeA6Norm_holds p hp5 H hirr ‹Group.IsPerfect H› hZ3
      ⟨e6⟩ t (hn t htG)
  exact ⟨h₀, hh₀, z, fun x _ => hzc x, htz⟩

theorem excData_of_threeAlternatingSix (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hn : ∀ g ∈ A.map (autGL e).toMonoidHom, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) [Group.IsPerfect H]
    (hZ3 : Nat.card (center H) = 3) (e6 : (H ⧸ center H) ≃* alternatingGroup (Fin 6))
    (hp30 : p % 30 = 1 ∨ p % 30 = 19) : ExcData p .J35 A := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    norm_num at hp30
  have hp5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three Fact.out hp hp3
  let f : H →* alternatingGroup (Fin 6) :=
    e6.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hfker : f.ker = Subgroup.center H := by
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center H)) e6.toMonoidHom
      e6.injective, QuotientGroup.ker_mk']
  have hf : Function.Surjective f :=
    e6.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center H))
  have hker : f.ker ≤ Subgroup.center H := by rw [hfker]
  have hker3 : ∀ z ∈ f.ker, z ^ 3 = 1 := by
    intro z hz
    rw [hfker] at hz
    exact center_pow_three_z6 hZ3 hz
  have hcard : 2 * Nat.card f.ker * Nat.card (alternatingGroup (Fin 6)) = ExcRow.J35.ord := by
    rw [hfker, hZ3, nat_card_alternatingGroup]
    norm_num [ExcRow.ord]
  have hcen : 2 * Nat.card f.ker = ExcRow.J35.cen := by
    rw [hfker, hZ3]
    norm_num [ExcRow.cen]
  have hZK : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  exact excData_of_inner_of_hom hp e hR hI hHG hirr
    (fun t ht _ => dec_z6 hp5 hn hirr hZ3 e6 t ht)
    f hf hker hker3 ExcRow.J35 (by simpa [ExcRow.admissible] using hp3) rfl
    hcard hZK hcen N1322.A6_noncomm
    (fun a b _ _ _ _ => a6_orderOf_mul_le_five_z6 a b) a6_hatt_z6 a6_hone_z6

private lemma exists_central_order_three_z6 {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hZ3 : Nat.card (Subgroup.center H) = 3) :
    ∃ z : H, z ∈ Subgroup.center H ∧ z ≠ 1 := by
  have hfin : Finite ↥(Subgroup.center H) :=
    (Nat.card_ne_zero.mp (by rw [hZ3]; norm_num)).2
  obtain ⟨z₀, hz₀ord⟩ := @exists_prime_orderOf_dvd_card' ↥(Subgroup.center H) _ hfin 3
    ⟨by norm_num⟩ (by rw [hZ3])
  refine ⟨(z₀ : H), z₀.2, ?_⟩
  intro h1
  have h2 : z₀ = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hz₀ord
  exact absurd hz₀ord (by norm_num)

private lemma noncomm_of_threeAlternatingSix_z6 {H : Subgroup (GL (Fin 3) (ZMod p))}
    (e6 : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) :
    ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  let f : H →* alternatingGroup (Fin 6) :=
    e6.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hf : Function.Surjective f :=
    e6.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center H))
  obtain ⟨x, y, hxy⟩ := N1322.A6_noncomm
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  refine ⟨(a : GL (Fin 3) (ZMod p)), a.2, (b : GL (Fin 3) (ZMod p)), b.2, ?_⟩
  intro h
  apply hxy
  have h' : a * b = b * a := Subtype.ext (by simpa using h)
  calc f a * f b = f (a * b) := (map_mul f a b).symm
    _ = f (b * a) := by rw [h']
    _ = f b * f a := map_mul f b a

private lemma exists_scalar_cube_z6 {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hZ3 : Nat.card (Subgroup.center H) = 3)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) {z : H}
    (hzmem : z ∈ Subgroup.center H) (hz1 : z ≠ 1) :
    ∃ c : ZMod p, ((z : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.scalar (Fin 3) c ∧ c ^ 3 = 1 ∧ c ≠ 1 := by
  have hcomm : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      ((z : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((z : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) * g := by
    intro g hg
    have h := congrArg (fun w : H => ((w : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)))
      (Subgroup.mem_center_iff.mp hzmem (⟨g, hg⟩ : H))
    simpa only [Subgroup.coe_mul, Units.val_mul] using h
  obtain ⟨c, hc⟩ := N1322.scalar_commutant_of_noncomm hirr hnc _ hcomm
  have hz3mat : (((z : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) ^ 3) = 1 := by
    simpa using congrArg (fun w : H => ((w : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p))) (center_pow_three_z6 hZ3 hzmem)
  have hc3 : c ^ 3 = 1 := by
    have h2 : (Matrix.scalar (Fin 3) c) ^ 3 = 1 := by
      rw [← hc]
      exact hz3mat
    rw [← map_pow, ← map_one (Matrix.scalar (Fin 3))] at h2
    exact (Matrix.scalar_inj (n := Fin 3)).mp h2
  have hc1 : c ≠ 1 := by
    intro h1
    apply hz1
    apply Subtype.ext
    apply Units.ext
    rw [hc, h1]
    simp
  exact ⟨c, hc, hc3, hc1⟩

theorem exists_smul_of_threeAlternatingSix (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hirr : IsIrreducibleMatrixRep H.subtype)
    (hZ3 : Nat.card (center H) = 3) (e6 : (H ⧸ center H) ≃* alternatingGroup (Fin 6)) :
    ∃ g ∈ A, ∃ ζ : ZMod p, ζ * ζ ≠ 1 ∧ ∀ v, g v = ζ • v := by
  obtain ⟨z, hzmem, hz1⟩ := exists_central_order_three_z6 hZ3
  obtain ⟨c, hcz, hc3, hc1⟩ :=
    exists_scalar_cube_z6 hirr hZ3 (noncomm_of_threeAlternatingSix_z6 e6) hzmem hz1
  have hcc : c * c ≠ 1 := by
    intro h2
    exact hc1 (by rw [← hc3, pow_succ, pow_two, h2, one_mul])
  obtain ⟨g, hgA, hgmap⟩ := Subgroup.mem_map.mp (hHG z.2)
  have hgz : (autGL e) g = (z : GL (Fin 3) (ZMod p)) := hgmap
  refine ⟨g, hgA, c, hcc, fun v => ?_⟩
  apply e.injective
  calc e (g v) = Matrix.mulVec (((autGL e) g : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)) (e v) := by
        rw [CFSG.RankThree.PartOne.LIT.autGL_mulVec]
        simp
    _ = Matrix.mulVec ((z : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)) (e v) := by
        rw [hgz]
    _ = c • e v := by
        rw [hcz, Matrix.scalar_apply, Matrix.diagonal_const_mulVec]
    _ = e (c • v) := (map_smul e c v).symm

end CFSG.StandardType.ZS.DimThree
