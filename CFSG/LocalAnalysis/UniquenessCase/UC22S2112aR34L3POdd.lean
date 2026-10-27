module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Ident
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63General
import CFSG.Adapters.LieModelL3U3Torus
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OddL3Inputs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125Cop
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125W
import CFSG.GH74.GLS.Stage2.OddAut.SL2OddNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.RankThree.PartTwo.Sec15.Sylow155R1 CFSG.RankThree.PartTwo.Sec15.Sylow155R3
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def R149L3P (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    (LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) →
    ∃ r : ℕ, r.Prime ∧ r ∣ p * (p ^ 2 - 1) ∧ IsStronglyPEmbedded r D.M

theorem uc22s2112l3p_conj (hGA : GriessAllModelsStatement) {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) {p : ℕ} (hp2 : p ≠ 2)
    (hX : LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) {b : G}
    (hb : b ∈ normalizer (L : Set G)) (hbT : b ∈ normalizer (D.T : Set G))
    (hbp : (orderOf b).Prime) (hb5 : 5 ≤ orderOf b) (hθ : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1) :
    ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L) ∧
      (∀ τ : G, ∀ hτ : τ ∈ normalizer (L : Set G), τ ∈ D.T →
        inducedBarInfAutHom L ⟨b, hb⟩ * inducedBarInfAutHom L ⟨τ, hτ⟩ =
          inducedBarInfAutHom L ⟨τ, hτ⟩ * inducedBarInfAutHom L ⟨b, hb⟩) ∧
      ∃ x : BarInf L, inducedBarInfAutHom L ⟨b, hb⟩ = MulAut.conj x ∧
        ∃ S : Sylow 2 (BarInf L), x ∈ centralizer (S : Set (BarInf L)) := by
  classical
  have : Fact (orderOf b).Prime := ⟨hbp⟩
  have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
  have hZ3 : Nat.card (center (Bar2 L)) ∣ 3 := by
    rcases hX with h | h
    · exact uc22s213_card_center_bar2_dvd_three hGA hL (Or.inl rfl) h
    · exact uc22s213_card_center_bar2_dvd_three hGA hL (Or.inr rfl) h
  have hsN : ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hbp (by omega) fun h => by
      have := (Nat.prime_dvd_prime_iff_eq hbp Nat.prime_three).1 (h.trans hZ3)
      omega
  set θ := inducedBarInfAutHom L ⟨b, hb⟩ with hθdef
  have hθo : orderOf θ = orderOf b := by
    have hd := orderOf_map_dvd (inducedBarInfAutHom L) ⟨b, hb⟩
    rw [Subgroup.orderOf_mk] at hd
    rcases (Nat.dvd_prime hbp).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hθ
    · exact h1
  have hOut : ¬ orderOf b ∣ Nat.card (Outer (BarInf L)) := by
    have h1 : ¬ orderOf b ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
    rcases hX with h | h
    · exact h.not_dvd_card_outer_psl3 hbp hb5 h1
    · exact h.not_dvd_card_outer_psu3 hbp hb5 h1
  obtain ⟨x, hx⟩ := PartOne.Section8.mem_inner_of_isPGroup_of_not_dvd_card_outer (r := orderOf b)
    (φ := θ) (IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, hθo, pow_one])) hOut
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hzc
  have hS : StatedClassicalModel (BarInf L) .PSL 3 p 1 ∨
      StatedClassicalModel (BarInf L) .PSU 3 p 1 :=
    hX.imp (·.statedClassicalModel_of_ne_zero (by norm_num))
      (·.statedClassicalModel_of_ne_zero (by norm_num))
  let V : Subgroup (MulAut (BarInf L)) :=
    (D.T.subgroupOf (normalizer (L : Set G))).map (inducedBarInfAutHom L)
  have hV : IsPGroup 2 V := (D.sylowG.isPGroup.comap_subtype).map _
  have hθV : θ ∈ normalizer (V : Set (MulAut (BarInf L))) := by
    rw [mem_normalizer_iff]
    intro v
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨⟨b, hb⟩ * τ * (⟨b, hb⟩)⁻¹, ?_, by rw [hθdef, map_mul, map_mul, map_inv]⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hτ ⊢
      exact (mem_normalizer_iff.1 hbT _).1 hτ
    · rintro ⟨τ, hτ, hτv⟩
      refine ⟨(⟨b, hb⟩)⁻¹ * τ * ⟨b, hb⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf] at hτ ⊢
        refine (mem_normalizer_iff.1 hbT _).2 ?_
        simpa [mul_assoc] using hτ
      · rw [map_mul, map_mul, map_inv, hτv, ← hθdef]
        group
  have hcop : Nat.Coprime (orderOf θ) 6 := by
    rw [hθo, show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hbp Nat.prime_two).2 (by omega))
      ((Nat.coprime_primes hbp Nat.prime_three).2 (by omega))
  have hcomm := res3L125_centralizes_of_normalizes hZ (res1OddL3_odd_commutator_outer hS)
    (res1OddL3_abelian_index_le_two hp2 hS) (res1OddL3_card_elemAbelian_le_four hp2 hS)
    (fun _ _ _ hR _ hA hidx hE _ hβ => res3L125_eq_one_of_coprime_six hR hA hidx hE hβ)
    hV hθV hcop
  have hcommT : ∀ τ : G, ∀ hτ : τ ∈ normalizer (L : Set G), τ ∈ D.T →
      θ * inducedBarInfAutHom L ⟨τ, hτ⟩ = inducedBarInfAutHom L ⟨τ, hτ⟩ * θ :=
    fun τ hτ hτT => hcomm _ (mem_map_of_mem _ (mem_subgroupOf.2 hτT))
  refine ⟨hsN, hcommT, x, hx.symm, ?_⟩
  obtain ⟨P, hP⟩ := uc22s2112r34_exists_sylow_barInf hL
  refine ⟨P, mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : y ∈ (P : Subgroup (BarInf L)) := hy
  rw [hP] at hy'
  obtain ⟨⟨τ, hτL⟩, hτ, rfl⟩ := hy'
  have h1 := hcommT τ (le_normalizer hτL) (mem_inf.1 (mem_subgroupOf.1 hτ)).1
  rw [uc22s2113_inducedBarInfAutHom_of_mem hτL, ← hx, ← map_mul, ← map_mul] at h1
  exact (hinj h1).symm

theorem uc22s2112l3p_lift {L : Subgroup G} {b : G} (hb : b ∈ normalizer (L : Set G))
    (hbp : (orderOf b).Prime) (hbN : ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {Y : Subgroup (BarInf L)}
    (hY : Y ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩))
    (eY : ↥Y ≃* SL(2, ZMod p)) :
    (∀ r : ℕ, r ∣ p * (p ^ 2 - 1) → r ∣ Nat.card ↥(L ⊓ centralizer ({b} : Set G))) ∧
      ∃ D0 : Subgroup G, D0 ≤ L ⊓ centralizer ({b} : Set G) ∧ ⁅D0, D0⁆ = D0 ∧
        ∃ f0 : ↥D0 →* PSL(2, GaloisField p 1), Function.Surjective f0 := by
  classical
  obtain ⟨φ, hφ, -⟩ := uc22s2112r34_exists_fixHom hb hbp hbN
  refine ⟨fun r hr => ?_, ?_⟩
  · have hY' : Nat.card Y = p * (p ^ 2 - 1) := by
      rw [Nat.card_congr eY.toEquiv, CFSG.GH74.GLS.Stage2.OddAut.SL2Odd.card_sl2, Nat.card_zmod]
    exact (hr.trans (hY' ▸ Subgroup.card_dvd_of_le hY)).trans (Subgroup.card_dvd_of_surjective hφ)
  let ε : ZMod p ≃+* GaloisField p 1 := (GaloisField.equivZmodP p).symm.toRingEquiv
  let π : SL(2, ZMod p) →* PSL(2, GaloisField p 1) :=
    (QuotientGroup.mk' _).comp (Matrix.SpecialLinearGroup.map ε.toRingHom)
  have hπ : Function.Surjective π := by
    refine (QuotientGroup.mk'_surjective _).comp fun A =>
      ⟨Matrix.SpecialLinearGroup.map ε.symm.toRingHom A, ?_⟩
    ext i j
    simp
  have : Group.IsPerfect PSL(2, GaloisField p 1) :=
    (uc22s2112r2_psl2_facts (by omega) le_rfl (by rw [pow_one]; omega)).2.2.1
  let Y' : Subgroup ↥(signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)) := Y.subgroupOf _
  let A : Subgroup ↥(L ⊓ centralizer ({b} : Set G)) := Y'.comap φ
  let eA := A.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let g' : ↥(A.map (Subgroup.subtype _)) →* PSL(2, GaloisField p 1) :=
    (((π.comp eY.toMonoidHom).comp (Subgroup.subgroupOfEquivOfLe hY).toMonoidHom).comp
      (φ.subgroupComap Y')).comp eA.symm.toMonoidHom
  have hg' : Function.Surjective g' :=
    ((((hπ.comp eY.surjective).comp (Subgroup.subgroupOfEquivOfLe hY).surjective).comp
      (φ.subgroupComap_surjective Y' hφ))).comp eA.symm.surjective
  obtain ⟨D0, hD0A, hD0perf, f0, hf0⟩ := uc22s2112r2_exists_perfect g' hg'
  exact ⟨D0, hD0A.trans (Subgroup.map_subtype_le A), hD0perf, f0, hf0⟩

theorem uc22s2112l3p_exists_inv {D : Data G} {Ch : Choice2011 G} (h149 : R149L3P D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (hX : LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) {b : G}
    (hbB : b ∈ c.B0) (hb : b ∈ normalizer (L : Set G)) (hbp : (orderOf b).Prime)
    (hbN : ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) {Y : Subgroup (BarInf L)}
    (hY : Y ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩))
    (eY : ↥Y ≃* SL(2, ZMod p)) :
    ∃ t ∈ D.M, (∃ k : ℕ, t ^ 2 ^ k = 1) ∧ t * b * t⁻¹ = b⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr, hrd, hrM⟩ := h149 L hL p hp hp2 hX
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' r ((uc22s2112l3p_lift hb hbp hbN hp5 hY eY).1 r hrd)
  have hyo : orderOf (y : G) = r := by rw [Subgroup.orderOf_coe, hy]
  have hyL := mem_inf.1 y.2
  have hX0 : zpowers (y : G) ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hyo
    exact hr.one_lt.ne hyo
  have hX0p : IsPGroup r (zpowers (y : G)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hX0U := mem_uniqueSet_of_isStronglyPEmbedded hr hrM (zpowers_le.2 (hL.1.le hyL.1)) hX0 hX0p
  obtain ⟨-, -, hCN, -⟩ := uc22s2112r2_normalizer hH c hL.1.le hbB hbp
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hb0 : zpowers b ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hbp
    exact Nat.not_prime_one hbp
  obtain ⟨m, hmM, hm⟩ := s21_10 D Ch hH c₀ (zpowers b) hb0 (zpowers_le.2 hbB) (zpowers (y : G))
    hX0 ⟨r, hr, hX0p⟩ (zpowers_le.2 (hCN hyL.2)) hX0U
  have hmb : m * b * m⁻¹ = b⁻¹ := hm b (mem_zpowers b)
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  refine ⟨m ^ o, pow_mem hmM o, ⟨k, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hko, pow_orderOf_eq_one]
  obtain ⟨j, rfl⟩ := ho
  have h1 : m * b = b⁻¹ * m := by
    calc m * b = m * b * m⁻¹ * m := by group
      _ = b⁻¹ * m := by rw [hmb]
  have h1' : m * b⁻¹ = b * m := by
    calc m * b⁻¹ = (m * b * m⁻¹)⁻¹ * m := by group
      _ = b * m := by rw [hmb, inv_inv]
  have hc : Commute (m ^ 2) b := by
    show m ^ 2 * b = b * m ^ 2
    rw [pow_two, mul_assoc, h1, ← mul_assoc, h1', mul_assoc]
  calc m ^ (2 * j + 1) * b * (m ^ (2 * j + 1))⁻¹
        = (m ^ 2) ^ j * (m * b * m⁻¹) * ((m ^ 2) ^ j)⁻¹ := by
        rw [pow_succ, pow_mul]
        group
    _ = b⁻¹ := by rw [hmb, ((hc.pow_left j).inv_right).eq, mul_inv_cancel_right]

end CFSG.LocalAnalysis.UniquenessCase.UC22
