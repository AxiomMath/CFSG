module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixComp
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixCmp
public import CFSG.LieType.SeitzGeneration.HyperCoverUnitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.RankThree.Classical.OrthogonalOrderThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6QTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

namespace GGQ2S08RoSix

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

omit [Finite G]
  in
theorem su5_scalars_eq_bot (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    (CFSG.Open.StatedScalars (Fin 5) K).subgroupOf (CFSG.Open.StatedSU 5 (2 ^ 1) K) = ⊥ := by
  have hKc : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨c, hc⟩ := hg
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 5) c ∈ CFSG.Open.StatedSU 5 (2 ^ 1) K := by
      rw [hc]
      exact g.2
    have h := (CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := 1) Nat.prime_two hKc
      (n := 5) (by norm_num) c).mp hmem
    have hc3 : c ^ 3 = 1 := by simpa using h.2
    have hdvd : orderOf c ∣ Nat.gcd 3 5 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one h.1)
    rw [show Nat.gcd 3 5 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_one, ← hc, hdvd, map_one]
  · intro hg
    rw [Subgroup.mem_bot] at hg
    rw [hg]
    exact Subgroup.one_mem _

theorem piL_mem_stabImg (c : GGQ2S08RoSix Bs L x) (w : Fin 6) (q : ↥(c.compL w)) :
    c.piL q ∈ c.stabImg w :=
  c.compL_le_stabPre w q.2

theorem eq_one_of_piL_eq_one (c : GGQ2S08RoSix Bs L x) (w : Fin 6) {q : ↥L}
    (hq : q ∈ c.compL w) (h1 : c.piL q = 1) : q = 1 := by
  have hKc : Nat.card c.K = (2 ^ 1) ^ 2 := by rw [c.hK]; norm_num
  have hU := USixTwo.fieldDataFour c.hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP c.K 2 := hU.charP
  haveI : Group.IsPerfect ↥(c.compL w) := Group.isPerfect_def.mpr (c.compL_quasisimple w).1
  let ρ₀ : ↥(c.compL w) →* ↥(c.stabImg w) :=
    (c.piL.comp (c.compL w).subtype).codRestrict (c.stabImg w) (c.piL_mem_stabImg w)
  let e : ↥(c.stabImg w) ≃* ↥(CFSG.Open.StatedSU 5 (2 ^ 1) c.K) :=
    (c.stabEquiv w).symm.trans (ggQ2s08r6_stabSUEquiv c.hK w)
  let mk := QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin 5) c.K).subgroupOf
    (CFSG.Open.StatedSU 5 (2 ^ 1) c.K))
  have hmk : Function.Injective mk := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact su5_scalars_eq_bot c.K c.hK
  let ρ : ↥(c.compL w) →* CFSG.Open.StatedProj (CFSG.Open.StatedSU 5 (2 ^ 1) c.K) :=
    mk.comp (e.toMonoidHom.comp ρ₀)
  have hρ₀ : Function.Surjective ρ₀ := by
    rintro ⟨r, hr⟩
    have hmap := ggQ2s08r6_map_comm_comap c.piL_surjective (c.stabImg w) (c.stabImg_perfect w)
    rw [← hmap] at hr
    obtain ⟨q', hq', hq'r⟩ := hr
    exact ⟨⟨q', hq'⟩, Subtype.ext hq'r⟩
  have hρ : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp hρ₀)
  have hρker : ∀ q' : ↥(c.compL w), ρ q' = 1 ↔ c.piL q' = 1 := by
    intro q'
    constructor
    · intro h
      have h2 : e (ρ₀ q') = 1 := hmk (by rw [map_one]; exact h)
      have h3 : ρ₀ q' = 1 := e.injective (by rw [h2, map_one])
      exact congrArg Subtype.val h3
    · intro h
      have h3 : ρ₀ q' = 1 := Subtype.ext h
      change mk (e (ρ₀ q')) = 1
      rw [h3, map_one, map_one]
  have hker : ρ.ker ≤ Subgroup.center ↥(c.compL w) := by
    intro q' hq'
    rw [MonoidHom.mem_ker, hρker] at hq'
    exact (ggQ2s08r6_mem_center_comm_comap c.piL_surjective c.piL_ker_le (c.stabImg w)
      (c.stabImg_perfect w) (c.stabImg_simple w) q').mpr hq'
  obtain ⟨φ, hφ, hφρ⟩ := CFSG.LieType.SeitzGeneration.exists_su_cover_hom hKc le_rfl
    (by norm_num : 4 ≤ 5) ρ hρ hker (fun h5 => absurd h5 (by decide))
  obtain ⟨g, hg⟩ := hφ ⟨q, hq⟩
  have hρq : ρ ⟨q, hq⟩ = 1 := (hρker _).mpr h1
  rw [← hg, hφρ] at hρq
  have hg1 : g = 1 := hmk (by rw [map_one]; exact hρq)
  rw [hg1, map_one] at hg
  exact congrArg Subtype.val hg.symm


theorem conjB_mem_center (c : GGQ2S08RoSix Bs L x) (b : Bs) {y : ↥L}
    (hy : y ∈ Subgroup.center ↥L) : c.conjB b y ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff] at hy ⊢
  intro l
  have h := hy ((c.conjB b).symm l)
  have h2 := congrArg (c.conjB b) h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem conj_mem_of_mem_compL (c : GGQ2S08RoSix Bs L x) (w : Fin 6) {q : ↥L}
    (hq : q ∈ c.compL w) (b : Bs) {b' : G} (hb' : b' ∈ Bs) (y : ↥L)
    (hy : y ∈ Subgroup.center ↥L) (h : (q : G) * b * (q : G)⁻¹ = b' * y) :
    (q : G) * b * (q : G)⁻¹ ∈ Bs := by
  have hu : q * c.conjB b q⁻¹ ∈ c.compL w :=
    (c.compL w).mul_mem hq (c.conjB_mem_compL w b ((c.compL w).inv_mem hq))
  set u := q * c.conjB b q⁻¹ with hudef
  set y' := c.conjB b y with hy'def
  have hy'c : y' ∈ Subgroup.center ↥L := c.conjB_mem_center b hy
  have hy'G : (y' : G) = (b : G) * y * (b : G)⁻¹ := e6QTwoBstarConjAction_apply c.hNL b y
  have huG : (u : G) = (q : G) * b * (q : G)⁻¹ * (b : G)⁻¹ := by
    rw [hudef, Subgroup.coe_mul, e6QTwoBstarConjAction_apply, Subgroup.coe_inv]
    group
  have hc'eq : (u : G) = (b' * (b : G)⁻¹) * y' := by
    rw [huG, h, hy'G]
    group
  have hc'Bs : b' * (b : G)⁻¹ ∈ Bs := Bs.mul_mem hb' (Bs.inv_mem b.2)
  have hc'L : b' * (b : G)⁻¹ ∈ L := by
    have : b' * (b : G)⁻¹ = (u : G) * (y' : G)⁻¹ := by rw [hc'eq]; group
    rw [this]
    exact L.mul_mem u.2 (L.inv_mem y'.2)
  set c' : ↥L := ⟨b' * (b : G)⁻¹, hc'L⟩ with hc'def
  have huL : u = c' * y' := Subtype.ext hc'eq
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact c.hBs.2 _ hc'Bs)
  have hu3 : u ^ 3 = y' ^ 3 := by
    have hcomm : Commute c' y' := Subgroup.mem_center_iff.mp hy'c c'
    rw [huL, hcomm.mul_pow, hc'3, one_mul]
  have hpi : c.piL (u ^ 3) = 1 := by
    rw [hu3, map_pow]
    have : c.piL y' = 1 := by rw [← MonoidHom.mem_ker, c.piL_ker]; exact hy'c
    rw [this, one_pow]
  have hu31 : u ^ 3 = 1 := c.eq_one_of_piL_eq_one w ((c.compL w).pow_mem hu 3) hpi
  have hy'3 : (y' : G) ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← Subgroup.coe_pow, ← hu3, hu31, Subgroup.coe_one]
  have hy'x : (y' : G) ∈ Subgroup.zpowers x :=
    mem_zpowers_of_mem_center c.hK c.θ c.hperf c.hBs c.hBL c.hstar c.hNL y'.2
      (fun l hl => congrArg Subtype.val (Subgroup.mem_center_iff.mp hy'c ⟨l, hl⟩).symm) hy'3
  have hy'Bs : (y' : G) ∈ Bs := (Subgroup.zpowers_le.mpr c.hx) hy'x
  have huBs : (u : G) ∈ Bs := by
    rw [hc'eq]
    exact Bs.mul_mem hc'Bs hy'Bs
  have : (q : G) * b * (q : G)⁻¹ = (u : G) * b := by rw [huG]; group
  rw [this]
  exact Bs.mul_mem huBs b.2


omit [Finite G]
  in
theorem exists_perm_four (w : Fin 6) :
    ∃ τ : Equiv.Perm (Fin 6), τ w = w ∧ ¬ τ ^ 2 ^ 1 = 1 ∧ τ ^ 2 ^ (1 + 1) = 1 := by
  fin_cases w
  · exact ⟨Equiv.swap 1 2 * Equiv.swap 1 3 * Equiv.swap 1 4, by decide, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 2 * Equiv.swap 0 3 * Equiv.swap 0 4, by decide, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 0 3 * Equiv.swap 0 4, by decide, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 0 2 * Equiv.swap 0 4, by decide, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 0 2 * Equiv.swap 0 3, by decide, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 0 2 * Equiv.swap 0 3, by decide, by decide, by decide⟩

theorem four_dvd_card_automizer (c : GGQ2S08RoSix Bs L x) (w : Fin 6) :
    4 ∣ Nat.card ↥(ggAutomizer (c.comp w) Bs) := by
  classical
  obtain ⟨τ, hτw, hτ2, hτ4⟩ := exists_perm_four w
  have hτord : orderOf τ = 2 ^ (1 + 1) := orderOf_eq_prime_pow hτ2 hτ4
  obtain ⟨n', hn'L, hn'N, hn'act⟩ := exists_mem_normalizer_frameAct_perm c.hK c.θ c.hNL c.hfull
    c.hrange5 c.hperf c.hBs c.hcard c.hx c.hx1 c.hBL c.hstar c.hI c.hLx τ
  have hconjBs : ∀ b : Bs, n' * (b : G) * n'⁻¹ ∈ Bs := fun b =>
    (Subgroup.mem_normalizer_iff.mp hn'N (b : G)).mp b.2
  have hrel : ∀ b : Bs, ∃ μ : c.Kˣ, ∀ k,
      c.diag ⟨n' * (b : G) * n'⁻¹, hconjBs b⟩ k = μ * c.diag b (τ.symm k) := by
    intro b
    have h := hn'act b (c.diag b) (fun k => c.cube _) (c.frameDiag_diag b)
    obtain ⟨μ, hμ⟩ := c.exists_eq_smul_diag h
    refine ⟨μ⁻¹, fun k => ?_⟩
    have := hμ k
    simp only [Function.comp_apply] at this
    rw [this, inv_mul_cancel_left]
  obtain ⟨g, τ', u, hgfr, hgmat, hrel'⟩ := c.exists_monomial_of_mem_normalizer hn'L hn'N
  have hττ' : τ = τ' := by
    refine ggQ2s08r6_perm_eq_of_forall c.card_units fun σ => ?_
    obtain ⟨b, hb⟩ := c.exists_diag_eq (fun k => (σ (0 : Fin 6))⁻¹ * σ k) (by simp)
    obtain ⟨μ₁, h1⟩ := hrel b
    obtain ⟨μ₂, h2⟩ := hrel' b (hconjBs b)
    have hσ : ∀ k, σ k = σ (0 : Fin 6) * c.diag b k := fun k => by rw [hb, mul_inv_cancel_left]
    refine ⟨μ₁⁻¹ * μ₂, fun i => ?_⟩
    have hD1 : c.diag b (τ.symm i) = μ₁⁻¹ * c.diag ⟨_, hconjBs b⟩ i := by
      rw [h1 i, inv_mul_cancel_left]
    have hD2 : c.diag b (τ'.symm i) = μ₂⁻¹ * c.diag ⟨_, hconjBs b⟩ i := by
      rw [h2 i, inv_mul_cancel_left]
    rw [hσ (τ.symm i), hσ (τ'.symm i), hD1, hD2, mul_left_comm (μ₁⁻¹ * μ₂) (σ (0 : Fin 6)),
      ← mul_assoc (μ₁⁻¹ * μ₂) μ₂⁻¹, mul_assoc μ₁⁻¹ μ₂ μ₂⁻¹, mul_inv_cancel, mul_one]
  subst hττ'
  have hcol : ∀ i, ((g : GL (Fin 6) c.K) : Matrix (Fin 6) (Fin 6) c.K) i w =
      if i = w then ((u w : c.Kˣ) : c.K) else 0 := by
    intro i
    rw [hgmat, Units.val_mul, CFSG.SectionRank.OddCover.coe_diagHom, Matrix.mul_diagonal,
      MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [Option.mem_def, Option.some.injEq]
    have hiff : (τ⁻¹ i = w) ↔ i = w := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, hτw]
    by_cases hi : i = w
    · rw [if_pos (hiff.mpr hi), if_pos hi, one_mul]
    · rw [if_neg (fun h => hi (hiff.mp h)), if_neg hi, zero_mul]
  have hgSU : (g : GL (Fin 6) c.K) ∈ LargeEvenSUGroup (Fin 6) c.K 2 :=
    (SetLike.ext_iff.mp (su6_eq c.K) _).mpr g.2
  have hsSU := ggQ2s08r6_scalar_mem c.hK (u w)⁻¹
  set s₀ : ↥(LargeEvenSUGroup (Fin 6) c.K 2) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) (u w)⁻¹, hsSU⟩ with hs₀
  set g₀ : ↥(LargeEvenSUGroup (Fin 6) c.K 2) := ⟨g, hgSU⟩ with hg₀
  have hg₁stab : s₀ * g₀ ∈ ggQ2s08r6Stab c.K w := by
    intro i
    change ((Matrix.GeneralLinearGroup.scalar (Fin 6) (u w)⁻¹ * (g : GL (Fin 6) c.K) :
      GL (Fin 6) c.K) : Matrix (Fin 6) (Fin 6) c.K) i w = _
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_mul, hcol i]
    by_cases hi : i = w
    · rw [if_pos hi, if_pos hi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    · rw [if_neg hi, if_neg hi, mul_zero]
  have hfrs : c.fr s₀ = 1 := by
    rw [fr_apply, InndiagSU.frameMk_apply]
    apply (QuotientGroup.eq_one_iff _).mpr
    change (((TableBUE.conjSU (USixTwo.fieldDataFour c.hK) c.Q c.hQ).symm (suCongr c.K s₀) :
      ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 c.K 6)) : GL (Fin 6) c.K) ∈
        LargeEvenScalars (Fin 6) c.K
    rw [InndiagSU.coe_conjSU_symm]
    refine ⟨(u w)⁻¹, ?_⟩
    change Matrix.GeneralLinearGroup.scalar (Fin 6) (u w)⁻¹ =
      c.Q * Matrix.GeneralLinearGroup.scalar (Fin 6) (u w)⁻¹ * c.Q⁻¹
    rw [← TypeA.PGLTor.scalar_mul_comm, mul_assoc, mul_inv_cancel, mul_one]
  have hfrg : c.fr g₀ = c.piL ⟨n', hn'L⟩ := by
    rw [fr_apply]
    exact hgfr
  have hn'P : (⟨n', hn'L⟩ : ↥L) ∈ c.stabPre w := by
    change c.piL ⟨n', hn'L⟩ ∈ c.stabImg w
    refine ⟨s₀ * g₀, hg₁stab, ?_⟩
    rw [map_mul, hfrs, one_mul, hfrg]
  have hsup := ggQ2s08r6_comap_eq_sup c.piL_surjective (c.stabImg w) (c.stabImg_perfect w)
  have hn'P' : (⟨n', hn'L⟩ : ↥L) ∈ c.compL w ⊔ c.piL.ker := by
    have h : (⟨n', hn'L⟩ : ↥L) ∈ Subgroup.comap c.piL (c.stabImg w) := hn'P
    rw [hsup] at h
    exact h
  haveI : (c.piL.ker).Normal := MonoidHom.normal_ker _
  obtain ⟨q, hq, z, hz, hqz⟩ := Subgroup.mem_sup_of_normal_right.mp hn'P'
  have hzc : z ∈ Subgroup.center ↥L := by rw [← c.piL_ker]; exact hz
  have hqG : (q : G) = n' * (z : G)⁻¹ := by
    have h : (q : G) * z = n' := congrArg Subtype.val hqz
    rw [← h]
    group
  have hk : ∀ b : Bs, ∃ k : ↥L, k ∈ Subgroup.center ↥L ∧
      (q : G) * b * (q : G)⁻¹ = (n' * (b : G) * n'⁻¹) * k := by
    intro b
    have hkc : c.conjB b⁻¹ z⁻¹ * z ∈ Subgroup.center ↥L := (Subgroup.center ↥L).mul_mem
      (c.conjB_mem_center b⁻¹ ((Subgroup.center ↥L).inv_mem hzc)) hzc
    refine ⟨c.conjB b⁻¹ z⁻¹ * z, hkc, ?_⟩
    have hkG : ((c.conjB b⁻¹ z⁻¹ * z : ↥L) : G) = (b : G)⁻¹ * (z : G)⁻¹ * b * z := by
      rw [Subgroup.coe_mul, e6QTwoBstarConjAction_apply]
      simp only [Subgroup.coe_inv, inv_inv]
    have hcomm : n'⁻¹ * ((c.conjB b⁻¹ z⁻¹ * z : ↥L) : G) =
        ((c.conjB b⁻¹ z⁻¹ * z : ↥L) : G) * n'⁻¹ :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hkc ⟨n'⁻¹, L.inv_mem hn'L⟩)
    rw [mul_assoc (n' * (b : G)), hcomm, hkG, hqG]
    group
  have hqconj : ∀ b : Bs, (q : G) * b * (q : G)⁻¹ ∈ Bs := by
    intro b
    obtain ⟨k, hkc, hkeq⟩ := hk b
    exact c.conj_mem_of_mem_compL w hq b (hconjBs b) k hkc hkeq
  have hqN : (q : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    have hmap : Bs.map (MulAut.conj (q : G)).toMonoidHom ≤ Bs := by
      rintro _ ⟨b, hb, rfl⟩
      exact hqconj ⟨b, hb⟩
    have hcard : Nat.card ↥(Bs.map (MulAut.conj (q : G)).toMonoidHom) = Nat.card ↥Bs :=
      Subgroup.card_map_of_injective (MulAut.conj (q : G)).injective
    exact mem_normalizer_iff_map_conj.mpr (Subgroup.eq_of_le_of_card_ge hmap hcard.ge)
  have hrelq : ∀ b : Bs, ∃ μ : c.Kˣ, ∀ k,
      c.diag ⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩ k = μ * c.diag b (τ.symm k) := by
    intro b
    obtain ⟨k₁, hk₁c, hk₁eq⟩ := hk b
    have hk₁Bs : (k₁ : G) ∈ Bs := by
      have : (k₁ : G) = (n' * (b : G) * n'⁻¹)⁻¹ * ((q : G) * b * (q : G)⁻¹) := by
        rw [hk₁eq]
        group
      rw [this]
      exact Bs.mul_mem (Bs.inv_mem (hconjBs b)) (hqconj b)
    have hk₁x : (k₁ : G) ∈ Subgroup.zpowers x := by
      rw [← c.hBL]
      refine ⟨hk₁Bs, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hk₁c ⟨l, hl⟩)
    have hsplit : (⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩ : ↥Bs) =
        ⟨n' * (b : G) * n'⁻¹, hconjBs b⟩ * ⟨(k₁ : G), hk₁Bs⟩ := Subtype.ext hk₁eq
    have hdk : c.diag ⟨(k₁ : G), hk₁Bs⟩ = 1 := (c.diag_eq_one_iff _).mpr hk₁x
    obtain ⟨μ, hμ⟩ := hrel b
    refine ⟨μ, fun k => ?_⟩
    rw [hsplit, c.diag_mul, hdk, mul_one]
    exact hμ k
  set α : MulAut ↥Bs := Bs.normalizerMonoidHom ⟨(q : G), hqN⟩ with hαdef
  have hαapply : ∀ b : Bs, α b = ⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩ := fun b =>
    Subtype.ext (Bs.normalizerMonoidHom_apply_apply_coe ⟨(q : G), hqN⟩ b)
  have hαmem : α ∈ ggAutomizer (c.comp w) Bs := by
    refine Subgroup.subset_closure (show α ∈ ggInduced (c.comp w) Bs from
      ⟨(q : G), ⟨q, hq, rfl⟩, hqN, fun b => ?_⟩)
    rw [hαapply]
  have hαpow : ∀ (m : ℕ) (b : Bs), ∃ μ : c.Kˣ, ∀ k,
      c.diag ((α ^ m) b) k = μ * c.diag b ((τ ^ m).symm k) := by
    intro m
    induction m with
    | zero =>
      intro b
      refine ⟨1, fun k => ?_⟩
      rw [pow_zero, pow_zero, one_mul]
      rfl
    | succ m ih =>
      intro b
      obtain ⟨μ, hμ⟩ := ih b
      obtain ⟨μ', hμ'⟩ := hrelq ((α ^ m) b)
      refine ⟨μ' * μ, fun k => ?_⟩
      rw [pow_succ', MulAut.mul_apply, hαapply, hμ' k, hμ, pow_succ', Equiv.Perm.mul_def,
        Equiv.symm_trans_apply, mul_assoc]
  have h4 : 4 ∣ orderOf α := by
    have hτm : τ ^ orderOf α = 1 := by
      apply ggQ2s08r6_perm_eq_of_forall c.card_units
      intro σ
      obtain ⟨b, hb⟩ := c.exists_diag_eq (fun k => (σ (0 : Fin 6))⁻¹ * σ k) (by simp)
      obtain ⟨μ, hμ⟩ := hαpow (orderOf α) b
      rw [pow_orderOf_eq_one, MulAut.one_apply] at hμ
      have hσ : ∀ k, σ k = σ (0 : Fin 6) * c.diag b k := fun k => by rw [hb, mul_inv_cancel_left]
      refine ⟨μ⁻¹, fun i => ?_⟩
      rw [Equiv.Perm.one_symm, Equiv.Perm.coe_one, id, hσ ((τ ^ orderOf α).symm i), hσ i,
        hμ i, mul_left_comm μ⁻¹, inv_mul_cancel_left]
    have h := orderOf_dvd_of_pow_eq_one hτm
    rw [hτord] at h
    exact h
  exact h4.trans (Subgroup.orderOf_dvd_natCard _ hαmem)

end GGQ2S08RoSix

end CFSG.StandardType

end
