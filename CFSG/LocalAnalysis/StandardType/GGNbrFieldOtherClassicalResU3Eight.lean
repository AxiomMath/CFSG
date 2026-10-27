module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3EightProj

public section

namespace CFSG.StandardType

namespace ResU3Eight

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.LocalAnalysis.GLTheoremA.T156.Uni
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)
open CFSG.RankThree.Classical (permGL permGL_not_mem_statedScalars)
open CFSG.RankThree.Classical2 (permGL_mul_diagHom_mul_inv diagHom_commute)
open ResU3Three

theorem exists_eq_conj_field_U3Eight {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hconj : GGRawFieldConj p R I F) (hnorm : GGRawFieldNorm R I F)
    (hcyc : GGRawFieldCycW p R I F) (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    {x : MulAut R} (hx : x ∈ Subgroup.closure (I ∪ F)) (hxI : x ∉ I) (hxp : x ^ p = 1) :
    ∃ f' ∈ F, ∃ u' ∈ I, orderOf f' = p ∧ x = u' * f' * u'⁻¹ := by
  obtain ⟨J, -, hJ, -, -, -, -⟩ := hcyc hs hna
  subst I
  obtain ⟨u, hu, f, hf, rfl⟩ := ggClosure_union_eq_mul hnorm x hx
  exact hconj hs hna u hu f hf hxI hxp

theorem pow_three_eq_one_of_ker_U3Eight {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} (hK3 : Nat.card ψ.ker ∣ 3) {z : L'} (hz : ψ z = 1) : z ^ 3 = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : ψ.ker) ∣ 3 := (orderOf_dvd_natCard _).trans hK3
  have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
  simpa using congrArg Subtype.val h2

theorem eq_of_sq_eq_one_U3Eight {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hker : ψ.ker ≤ Subgroup.center L') (hK3 : Nat.card ψ.ker ∣ 3) {n n' : L'}
    (hn : n ^ 2 = 1) (hn' : n' ^ 2 = 1) (hψn : ψ n' = ψ n) : n' = n := by
  set z := n' * n⁻¹ with hzdef
  have hz : ψ z = 1 := by rw [hzdef, map_mul, map_inv, hψn, mul_inv_cancel]
  have hzc : z ∈ Subgroup.center L' := hker hz
  have hz3 : z ^ 3 = 1 := pow_three_eq_one_of_ker_U3Eight hK3 hz
  have hn'z : n' = z * n := by rw [hzdef, inv_mul_cancel_right]
  have hcomm : Commute z n := (Subgroup.mem_center_iff.mp hzc n).symm
  have hz2 : z ^ 2 = 1 := by
    have h1 : (z * n) ^ 2 = z ^ 2 * n ^ 2 := hcomm.mul_pow 2
    rw [← hn'z, hn', hn, mul_one] at h1
    exact h1.symm
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2, inv_one, mul_one]
  rw [hn'z, hz1, one_mul]

section Eight

variable {K : Type} [Field K] [Finite K]

local notation "H₈" => LargeEvenSUGroup (Fin 3) K (2 ^ 3)
local notation "N₈" => Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ 3) : Set (GL (Fin 3) K))
local notation "ρ₈" => TableB.projConj (LargeEvenSUGroup (Fin 3) K (2 ^ 3))
local notation "π₈" => LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ 3))
local notation "R₈" => LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ 3))
local notation "I₈" => LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ 3)))
  (LargeEvenGUSet (Fin 3) K (2 ^ 3))
local notation "F₈" => LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ 3)))

theorem ggTorusLiftFix_U3Eight
    (hK : Nat.card K = (2 ^ 3) ^ 2)
    (hcyc : GGRawFieldCycW 3 R₈ I₈ F₈) (hconj : GGRawFieldConj 3 R₈ I₈ F₈)
    (hnorm : GGRawFieldNorm R₈ I₈ F₈) (hs : IsSimpleGroup R₈)
    (hna : ∃ a b : R₈, a * b ≠ b * a) : GGTorusLiftFix 3 0 R₈ I₈ F₈ := by
  classical
  intro L' _ _ ψ hψ hker hperf f hfp hind hnot
  obtain ⟨x, hx, hxψ⟩ := hind
  have hxI : x ∉ I₈ := fun h => hnot ⟨x, h, hxψ⟩
  have hxp : x ^ 3 = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [ggInduced_pow ψ hxψ 3 l, hfp]
    rfl
  have h₀K : UnitaryFieldData 2 3 K := TableBU.unitaryFieldData_of_card hK (by norm_num)
  haveI : CharP K 2 := h₀K.charP
  have hNK := TableBUE.gu_subset_normalizer (d := 3) h₀K
  have hK3 := ggCenterKp_u3Three hK (by norm_num) L' ψ hψ hker hperf
  obtain ⟨f', hf', u', hu', -, hxe⟩ :=
    exists_eq_conj_field_U3Eight hconj hnorm hcyc hs hna hx hxI hxp
  obtain ⟨U, hU, rfl⟩ := TableB.exists_eq_projConj hNK hu'
  obtain ⟨σ, hσf⟩ := exists_induced hf'
  set τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hτ
  have hτ2 : τ ^ 2 = 1 := by rw [sq, hτ, Equiv.swap_mul_self]
  have hτmem : (permGL τ : GL (Fin 3) K) ∈ H₈ := permGL_mem_su τ
  have ht₁ : U * permGL τ * U⁻¹ ∈ H₈ := conj_mem_su hU hτmem
  set t₀ : H₈ := ⟨permGL τ, hτmem⟩ with ht₀def
  set t₁ : H₈ := ⟨_, ht₁⟩ with ht₁def
  have hxt : x (π₈ t₁) = π₈ t₁ := by
    have h1 : (ρ₈ ⟨U, hNK hU⟩)⁻¹ (π₈ t₁) = π₈ t₀ := by
      rw [← map_inv]
      change ρ₈ ⟨U, hNK hU⟩⁻¹ (t₁ : R₈) = (t₀ : R₈)
      rw [TableB.projConj_mk]
      congr 1
      apply Subtype.ext
      change U⁻¹ * (U * permGL τ * U⁻¹) * U⁻¹⁻¹ = (permGL τ : GL (Fin 3) K)
      group
    have h2 : f' (π₈ t₀) = π₈ t₀ := by
      change f' (QuotientGroup.mk t₀) = QuotientGroup.mk t₀
      rw [hσf t₀]
      congr 1
      apply Subtype.ext
      rw [matAct_coe]
      exact map_permGL σ.toRingHom τ
    have h3 : ρ₈ ⟨U, hNK hU⟩ (π₈ t₀) = π₈ t₁ := by
      change ρ₈ ⟨U, hNK hU⟩ (t₀ : R₈) = (t₁ : R₈)
      rw [TableB.projConj_mk]
      congr 1
    rw [hxe, MulAut.mul_apply, MulAut.mul_apply, h1, h2, h3]
  have ht1 : π₈ t₁ ≠ 1 := by
    intro h
    have hmem : (t₁ : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff t₁).mp h)
    have h2 : (permGL τ : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K := by
      have h3 := (LargeEvenScalars.normal (ι := Fin 3) (K := K)).conj_mem _ hmem U⁻¹
      have e : U⁻¹ * (t₁ : GL (Fin 3) K) * U⁻¹⁻¹ = permGL τ := by
        change U⁻¹ * (U * permGL τ * U⁻¹) * U⁻¹⁻¹ = permGL τ
        group
      rwa [e] at h3
    exact permGL_not_mem_statedScalars (by rw [hτ]; decide) h2
  have ht2 : t₁ ^ 2 = 1 := by
    apply Subtype.ext
    change (U * permGL τ * U⁻¹) ^ 2 = 1
    rw [conj_pow, ← map_pow, hτ2, map_one, mul_one, mul_inv_cancel]
  obtain ⟨l, hl⟩ := hψ (π₈ t₁)
  have hl2 : ψ (l ^ 2) = 1 := by rw [map_pow, hl, ← map_pow, ht2, map_one]
  have hn2 : (l ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul]
    exact pow_three_eq_one_of_ker_U3Eight hK3 hl2
  have hψn : ψ (l ^ 3) = π₈ t₁ := by
    rw [map_pow, hl, pow_succ (π₈ t₁) 2, ← map_pow, ht2, map_one, one_mul]
  have hn1 : l ^ 3 ≠ 1 := by
    intro h
    apply ht1
    rw [← hψn, h, map_one]
  have hfn : f (l ^ 3) = l ^ 3 := by
    refine eq_of_sq_eq_one_U3Eight hker hK3 hn2 (by rw [← map_pow, hn2, map_one]) ?_
    rw [← hxψ, hψn, hxt]
  refine ⟨Subgroup.zpowers (l ^ 3), ⊥, ?_, ?_, bot_le, TypeA.isElemAbelian_bot (p := 3), ?_,
    bot_inf_eq _, ?_, ?_⟩
  · intro h
    apply hn1
    have : l ^ 3 ∈ (⊥ : Subgroup L') := h ▸ Subgroup.mem_zpowers (l ^ 3)
    exact Subgroup.mem_bot.mp this
  · have hord : orderOf (l ^ 3) = 2 := orderOf_eq_prime hn2 hn1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  · rw [Subgroup.card_bot, pow_zero]
  · intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [map_zpow, hfn]
  · intro y hy
    rw [Subgroup.mem_bot.mp hy, map_one]

theorem ggTorusNoLineFieldComp_U3Eight
    (hK : Nat.card K = (2 ^ 3) ^ 2)
    (hcyc : GGRawFieldCycW 3 R₈ I₈ F₈) (hconj : GGRawFieldConj 3 R₈ I₈ F₈)
    (hnorm : GGRawFieldNorm R₈ I₈ F₈) (hs : IsSimpleGroup R₈)
    (hna : ∃ a b : R₈, a * b ≠ b * a) : GGTorusNoLineFieldComp 3 0 R₈ I₈ F₈ := by
  classical
  intro L' _ _ ψ hψ hker hperf A hAe hAind _ hcard3 _
  have h₀K : UnitaryFieldData 2 3 K := TableBU.unitaryFieldData_of_card hK (by norm_num)
  haveI : CharP K 2 := h₀K.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNK := TableBUE.gu_subset_normalizer (d := 3) h₀K
  have hK3 := ggCenterKp_u3Three hK (by norm_num) L' ψ hψ hker hperf
  obtain ⟨J, S, hJI, -, hNJ, hgen, hSall⟩ := hcyc hs hna
  have hIJ : ∀ φ : MulAut R₈, φ ∈ I₈ ↔ φ ∈ J := fun φ => by rw [← hJI]; rfl
  obtain ⟨Ind, hInd⟩ := ggInducedHom_exists ψ hψ A (fun a ha => by
    obtain ⟨φ, -, h⟩ := hAind a ha
    exact ⟨φ, h⟩)
  have hIndcl : ∀ a : A, Ind a ∈ Subgroup.closure (I₈ ∪ F₈) := by
    intro a
    obtain ⟨φ, hφ, h⟩ := hAind a a.2
    rw [ggInduced_unique hψ (hInd a) h]
    exact hφ
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hIndp : ∀ a : A, Ind a ^ 3 = 1 := by
    intro a
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hexp a a.2)
    rw [this, map_one]
  have hIndS : ∀ a : A, Ind a ∈ S := fun a => hSall _ (hIndcl a) ⟨1, by simpa using hIndp a⟩
  let A₀ : Subgroup (MulAut L') := (J.comap Ind).map A.subtype
  have hA₀A : A₀ ≤ A := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hmem : ∀ a : A, (a : MulAut L') ∈ A₀ ↔ Ind a ∈ J := by
    intro a
    constructor
    · rintro ⟨a', ha', h⟩
      have : a' = a := Subtype.ext h
      subst this
      exact ha'
    · intro h
      exact ⟨a, h, rfl⟩
  obtain ⟨-, hgenA⟩ := ggCyclicSplit Nat.prime_three hA₀A hexp Ind hNJ hgen hIndS hmem
  have hA₀e : IsElemAbelian 3 A₀ := TableB.isElemAbelian_mono hAe hA₀A
  have hA₀I : ∀ a ∈ A₀, ∃ φ ∈ I₈, ∀ l, φ (ψ l) = ψ (a l) := fun a ha =>
    ⟨Ind ⟨a, hA₀A ha⟩, (hIJ _).mpr ((hmem ⟨a, hA₀A ha⟩).mp ha), hInd ⟨a, hA₀A ha⟩⟩
  have hA₀lt : Nat.card A₀ < 3 ^ 3 := TableBUE.card_lt_unitary_three h₀K hK (by norm_num)
    Nat.prime_three (by norm_num) hψ hker hperf hA₀e hA₀I
  have hAA₀ : ¬ A ≤ A₀ := fun hle =>
    absurd hcard3 (not_le.mpr (lt_of_le_of_lt (Subgroup.card_le_of_le hle) hA₀lt))
  obtain ⟨b, hbA, hbA₀⟩ := SetLike.not_le_iff_exists.mp hAA₀
  have hxI : Ind ⟨b, hbA⟩ ∉ I₈ := fun h => hbA₀ ((hmem ⟨b, hbA⟩).mpr ((hIJ _).mp h))
  obtain ⟨f', hf', u', hu', hf'3, hxe⟩ :=
    exists_eq_conj_field_U3Eight hconj hnorm hcyc hs hna (hIndcl _) hxI (hIndp _)
  obtain ⟨U, hU, rfl⟩ := TableB.exists_eq_projConj hNK hu'
  obtain ⟨σ, hσf⟩ := exists_induced hf'
  have hσ3 : orderOf σ = 3 :=
    (orderOf_eq_of_induced (d := 3) (by norm_num) (by norm_num) hK hσf).trans hf'3
  haveI : Finite H₈ := Finite.of_injective
    (fun x : H₈ => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  obtain ⟨α, -, hα⟩ := exists_cover_of_sections π₈ (QuotientGroup.mk'_surjective _)
    (fun E _ _ π hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := 3) hK (by norm_num) le_rfl (by decide)
        (dq_ne_U3Three (by norm_num)) hπ hcen)
    ψ hψ hker hperf
  set Ab : Subgroup (MulAut R₈) := TypeA.inducedSub ψ A₀ with hAbdef
  have hAb : IsElemAbelian 3 Ab := TypeA.isElemAbelian_inducedSub hψ hA₀e
  have hAbI : ∀ φ ∈ Ab, φ ∈ I₈ := by
    intro φ hφ
    obtain ⟨a, ha, h⟩ := TypeA.mem_inducedSub.mp hφ
    rw [ggInduced_unique hψ h (hInd ⟨a, hA₀A ha⟩)]
    exact (hIJ _).mpr ((hmem ⟨a, hA₀A ha⟩).mp ha)
  have hAbx : ∀ φ ∈ Ab, φ * (ρ₈ ⟨U, hNK hU⟩ * f' * (ρ₈ ⟨U, hNK hU⟩)⁻¹) =
      (ρ₈ ⟨U, hNK hU⟩ * f' * (ρ₈ ⟨U, hNK hU⟩)⁻¹) * φ := by
    intro φ hφ
    obtain ⟨a, ha, h⟩ := TypeA.mem_inducedSub.mp hφ
    rw [ggInduced_unique hψ h (hInd ⟨a, hA₀A ha⟩), ← hxe, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (TableB.IsElemAbelian.comm hAe (hA₀A ha) hbA)
  refine ⟨{n | ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹},
    fun n hn => hn, fun _ a₀ ha₀ hne hind hcl => ?_⟩
  have ha₀A₀ : a₀ ∈ A₀ := by
    obtain ⟨φ, hφ, h⟩ := hind
    have e := ggInduced_unique hψ (hInd ⟨a₀, ha₀⟩) h
    exact (hmem ⟨a₀, ha₀⟩).mpr (by rw [e]; exact (hIJ _).mp hφ)
  have hφ₀ : Ind ⟨a₀, ha₀⟩ ∈ Ab := TypeA.mem_inducedSub.mpr ⟨a₀, ha₀A₀, hInd ⟨a₀, ha₀⟩⟩
  have hφ₀1 : Ind ⟨a₀, ha₀⟩ ≠ 1 := by
    intro h
    apply hne
    refine ggAut_eq_one_of_induced_one ψ hker hperf a₀ fun l => ?_
    rw [← hInd ⟨a₀, ha₀⟩ l, h]
    rfl
  rcases reg_or_frame_proj_U3Eight hK hσ3 hσf ⟨U, hNK hU⟩ hU hAb hAbI hAbx hφ₀ hφ₀1 with
    hsolv | ⟨Q, u, v, hw, hwx, hdiag, B₀, σ₀, hB₀, hσ₀, hninj, huv⟩
  · exact absurd hcl (not_ggFixCompCyclic_of_noComp hψ hker (hInd ⟨a₀, ha₀⟩)
      (fun J hJ => not_isComponentOf_of_isSolvable hsolv hJ))
  set τ : Equiv.Perm (Fin 3) := Equiv.swap u v with hτ
  have hτ2 : τ ^ 2 = 1 := by rw [sq, hτ, Equiv.swap_mul_self]
  set w : H₈ := ⟨_, hw⟩ with hwdef
  have hw' : (w : GL (Fin 3) K) = Q * permGL τ * Q⁻¹ := rfl
  set cQ : MulAut (GL (Fin 3) K) := MulAut.conj Q⁻¹ with hcQdef
  have hcQ : ∀ X, cQ X = Q⁻¹ * X * Q := fun X => by rw [hcQdef, MulAut.conj_apply, inv_inv]
  have hcQs : ∀ c : Kˣ, cQ (Matrix.GeneralLinearGroup.scalar (Fin 3) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := fun c => by rw [hcQ, conj_scalar_U3Three]
  have hcQw : cQ (w : GL (Fin 3) K) = permGL τ := by rw [hcQ, hw']; group
  have hn2 : (α w) ^ 2 = 1 := by
    have hw2 : w ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hw', conj_pow, ← map_pow, hτ2, map_one, mul_one,
        mul_inv_cancel]
    rw [← map_pow, hw2, map_one]
  have hbn : b (α w) = α w := by
    refine eq_of_sq_eq_one_U3Eight hker hK3 hn2 (by rw [← map_pow, hn2, map_one]) ?_
    rw [← hInd ⟨b, hbA⟩ (α w), hxe, hα w]
    exact hwx
  have hact : ∀ a₁ ∈ A₀, ∃ (B : N₈) (D : Fin 3 → Kˣ), cQ (B : GL (Fin 3) K) = diagHom 3 D ∧
      (∃ s : Kˣ, ∀ i, D i ^ 3 = s) ∧
      ∀ g : H₈, a₁ (α g) = α ((LargeEvenSUGroup (Fin 3) K (2 ^ 3)).normalizerMonoidHom B g) := by
    intro a₁ ha₁
    obtain ⟨B, -, hBe, D, hD⟩ :=
      hdiag _ (TypeA.mem_inducedSub.mpr ⟨a₁, ha₁, hInd ⟨a₁, hA₀A ha₁⟩⟩)
    have hBind : ∀ l, ρ₈ B (ψ l) = ψ (a₁ l) := fun l => by
      rw [← hBe]
      exact hInd ⟨a₁, hA₀A ha₁⟩ l
    have hD' : cQ (B : GL (Fin 3) K) = diagHom 3 D := by rw [hcQ]; exact hD
    obtain ⟨s, hs⟩ := exists_cube_scalar_U3Three hK (by norm_num) (by norm_num) (M := B)
      (by rw [← hBe, hIndp])
    have hs' : (B : GL (Fin 3) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) s := hs
    refine ⟨B, D, hD', ⟨s, fun i => ?_⟩, fun g => act_of_lift_U3Three hK (by norm_num) hker hα B
      hBind g⟩
    have h1 : diagHom 3 (D ^ 3) = diagHom 3 (fun _ => s) := by
      rw [map_pow, ← hD', ← map_pow, hs', hcQs, scalar_eq_diagHom_U3Three]
    exact congrFun (diagHom_injective 3 h1) i
  have hdec := ggTransfer_decomp (A := A) (A₀ := A₀) (H := ggFixSub b)
    (fun l hl => mem_ggFixSub.mp hl) (hgenA b hbA hbA₀)
  refine ⟨α w, fun a ha => ?_, ?_⟩
  ·
    obtain ⟨a₁, ha₁, ha₁eq⟩ := hdec a ha
    have han : a (α w) = a₁ (α w) := ha₁eq (α w) (mem_ggFixSub.mpr hbn)
    obtain ⟨B₁, D₁, hD₁, ⟨s₁, hs₁⟩, hB₁act⟩ := hact a₁ ha₁
    have hfixb : b (α w * (a₁ (α w))⁻¹) = α w * (a₁ (α w))⁻¹ := by
      have hcomm : b (a₁ (α w)) = a₁ (b (α w)) := by
        have e := TableB.IsElemAbelian.comm hAe hbA (hA₀A ha₁)
        change (b * a₁) (α w) = (a₁ * b) (α w)
        rw [e]
      rw [map_mul, map_inv, hcomm, hbn]
    rw [han, hB₁act w, ← map_inv, ← map_mul]
    rw [hB₁act w, ← map_inv, ← map_mul] at hfixb
    set y : H₈ := w * ((LargeEvenSUGroup (Fin 3) K (2 ^ 3)).normalizerMonoidHom B₁ w)⁻¹ with hydef
    have hy : (y : GL (Fin 3) K) = (w : GL (Fin 3) K) * B₁ * (w : GL (Fin 3) K)⁻¹ *
        (B₁ : GL (Fin 3) K)⁻¹ := by
      rw [hydef, Subgroup.coe_mul, Subgroup.coe_inv]
      change (w : GL (Fin 3) K) * ((B₁ : GL (Fin 3) K) * (w : GL (Fin 3) K) *
        (B₁ : GL (Fin 3) K)⁻¹)⁻¹ = _
      group
    have hcQy : cQ (y : GL (Fin 3) K) = diagHom 3 (D₁ ∘ τ.symm * D₁⁻¹) := by
      rw [hy, map_mul, map_mul, map_mul, map_inv, map_inv, hcQw, hD₁,
        permGL_mul_diagHom_mul_inv, ← map_inv, ← map_mul]
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [← map_pow]
      have hy3 : y ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        apply cQ.injective
        rw [map_pow, hcQy, ← map_pow, map_one]
        have h1 : (D₁ ∘ τ.symm * D₁⁻¹) ^ 3 = 1 := by
          funext t
          simp only [Pi.pow_apply, Pi.mul_apply, Pi.inv_apply, Function.comp_apply,
            Pi.one_apply, mul_pow, inv_pow, hs₁, mul_inv_cancel]
        rw [h1, map_one]
      rw [hy3, map_one]
    · obtain ⟨a₁', ha₁', ha₁'eq⟩ := hdec a' ha'
      rw [ha₁'eq _ (mem_ggFixSub.mpr hfixb)]
      obtain ⟨B₁', D₁', hD₁', -, hB₁'act⟩ := hact a₁' ha₁'
      rw [hB₁'act y]
      congr 1
      apply Subtype.ext
      change (B₁' : GL (Fin 3) K) * (y : GL (Fin 3) K) * (B₁' : GL (Fin 3) K)⁻¹ = y
      have hc : (B₁' : GL (Fin 3) K) * (y : GL (Fin 3) K) = (y : GL (Fin 3) K) * B₁' := by
        apply cQ.injective
        rw [map_mul, map_mul, hD₁', hcQy]
        exact (diagHom_commute _ _).eq
      rw [hc, mul_inv_cancel_right]
  ·
    intro hmem'
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hmem'
    have hind₀ : ∀ l, ρ₈ B₀ (ψ l) = ψ (a₀ l) := fun l => by
      rw [← hB₀]
      exact hInd ⟨a₀, ha₀⟩ l
    have h1 : ρ₈ B₀ ^ t = MulAut.conj (ψ (α w)) * ρ₈ B₀ * (MulAut.conj (ψ (α w)))⁻¹ := by
      apply ggInduced_unique hψ (a := a₀ ^ t)
      · exact TableBUD.induced_zpow hind₀ t
      · intro l
        rw [ht]
        exact ggInduced_conj_mul_conj_inv ψ (α w) hind₀ l
    have hwN : (w : GL (Fin 3) K) ∈ N₈ := Subgroup.le_normalizer w.2
    have hcw : MulAut.conj (ψ (α w)) = ρ₈ ⟨w, hwN⟩ := by
      rw [hα w]
      exact (TableB.projConj_of_mem _ (w : GL (Fin 3) K) w.2).symm
    rw [hcw] at h1
    have h2 : ρ₈ (B₀ ^ t) = ρ₈ (⟨w, hwN⟩ * B₀ * (⟨w, hwN⟩ : N₈)⁻¹) := by
      rw [map_zpow, map_mul, map_mul, map_inv, h1]
    obtain ⟨z, hz⟩ := eq_scalar_mul_of_projConj_eq_U3Three hK (by norm_num) (by norm_num) h2
    have hz' : (B₀ : GL (Fin 3) K) ^ t = Matrix.GeneralLinearGroup.scalar (Fin 3) z *
        ((w : GL (Fin 3) K) * B₀ * (w : GL (Fin 3) K)⁻¹) := by
      simpa only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] using hz
    have hσ₀' : cQ (B₀ : GL (Fin 3) K) = diagHom 3 σ₀ := by rw [hcQ]; exact hσ₀
    have h3' : diagHom 3 (σ₀ ^ t) = diagHom 3 ((fun _ => z) * (σ₀ ∘ τ.symm)) := by
      have h4 := congrArg cQ hz'
      rw [map_zpow, hσ₀', map_mul, hcQs, map_mul, map_mul, map_inv, hcQw, hσ₀',
        permGL_mul_diagHom_mul_inv, scalar_eq_diagHom_U3Three, ← map_zpow, ← map_mul] at h4
      exact h4
    apply not_forall_swap_U3Three hninj huv z⁻¹ t
    intro i
    have h5 := congrFun (diagHom_injective 3 h3') i
    simp only [Pi.pow_apply, Pi.mul_apply, Function.comp_apply, hτ, Equiv.symm_swap] at h5
    rw [h5, inv_mul_cancel_left]

theorem fieldKLevel_U3Eight
    (hK : Nat.card K = (2 ^ 3) ^ 2)
    (hcy : GGRawFieldCycW 3 R₈ I₈ F₈) (hc : GGRawFieldConj 3 R₈ I₈ F₈)
    (hce : GGRawFieldCentral R₈ I₈ F₈) (hin : GGRawInnField 3 R₈ I₈ F₈) :
    GGNbrWeylFieldKLevelComp 3 R₈ I₈ F₈ := by
  intro hs hna
  have hnorm := ggRawFieldNorm_of_central hce hin hs hna
  have h₀K : UnitaryFieldData 2 3 K := TableBU.unitaryFieldData_of_card hK (by norm_num)
  haveI : CharP K 2 := h₀K.charP
  refine ⟨(hin hs hna).2.2.1, 0, ?_, ggTorusLiftFix_U3Eight hK hcy hc hnorm hs hna, ?_,
    ggTorusNoLineFieldComp_U3Eight hK hcy hc hnorm hs hna⟩
  · exact TypeA.ggTorusLift_zero
      (two_dvd_card_statedProj_statedSU (d := 3) (f := 3) (K := K) (by norm_num))
  · intro L' _ _ ψ hψ hker hperf A hA hAI _ h27 _
    exact absurd h27 (not_le.mpr (TableBUE.card_lt_unitary_three h₀K hK (by norm_num)
      Nat.prime_three (by norm_num) hψ hker hperf hA hAI))

end Eight

end ResU3Eight

open CFSG.Assembly

theorem largeEvenLabelAll_fieldKLevel_u3Eight
    {lab : LargeEvenLabel}
    (h : lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3)
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW 3))
    (hconj : LargeEvenLabelAll lab (GGRawFieldConj 3))
    (hcen : LargeEvenLabelAll lab GGRawFieldCentral)
    (hinn : LargeEvenLabelAll lab (GGRawInnField 3)) :
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp 3) := by
  have hrow : LargeEvenLabelAll lab fun R _ I F => GGRawFieldCycW 3 R I F →
      GGRawFieldConj 3 R I F → GGRawFieldCentral R I F → GGRawInnField 3 R I F →
        GGNbrWeylFieldKLevelComp 3 R I F := by
    obtain ⟨ht, hl, hn⟩ := h
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hl hn
    subst ht hl hn
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', fun hcy hc hce hin =>
      ResU3Eight.fieldKLevel_U3Eight hK hcy hc hce hin⟩
  refine (largeEvenLabelAll_and hrow (largeEvenLabelAll_and hcyc (largeEvenLabelAll_and hconj
    (largeEvenLabelAll_and hcen hinn)))).mono ?_
  rintro R _ I F ⟨h1, h2, h3, h4, h5⟩
  exact h1 h2 h3 h4 h5

end CFSG.StandardType

end
