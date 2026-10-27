module

public import CFSG.RankThree.PartOne.S11d.PSpField
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneFixed
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.PSpComponent

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OddIso CFSG.RankThree.PartOne.KCSpFull
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCPrimary Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (scalars_eq_center projectiveSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (projectiveSpecialLinearEquivProjectiveSL)
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlockEquivOne)
open scoped MatrixGroups

variable {r p : ℕ} {K : Type} [Field K]

theorem proj_injective_sp [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r) :
    Function.Injective (proj r K) := by
  have hker : (proj r K).ker = ⊥ := by
    rw [SymplecticHigher.ker_proj, ← Subgroup.card_eq_one, card_spScalars_eq_gcd K hr]
    have hK2 : 2 ∣ Nat.card K := hK ▸ dvd_pow_self 2 (by omega)
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h2' : ¬ 2 ∣ Nat.card K - 1 := by omega
    exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2')
  exact (MonoidHom.ker_eq_bot_iff _).mp hker

theorem sp_fix_ne_bot [Finite K] [CharP K 2] {a S : StatedSp r K} (hodd : Odd p) (hap : a ^ p = 1)
    (hcyc : IsCyclicOn (spEnd a) (LinearMap.range (spEnd a - 1)))
    (hS : S ∈ Subgroup.centralizer ({a} : Set (StatedSp r K))) (hS2 : S ^ 2 = 1) (hS1 : S ≠ 1) :
    LinearMap.ker (spEnd a - 1) ≠ ⊥ := by
  intro hbot
  apply hS1
  apply spEnd_injective
  refine LinearMap.ext fun v => ?_
  have hÂp : spEnd a ^ p = 1 := by rw [← spEnd_pow', hap, spEnd_one]
  have hSa : S * a = a * S := Subgroup.mem_centralizer_singleton_iff.mp hS
  have hcomm : spEnd S * spEnd a = spEnd a * spEnd S := spEnd_comm_iff.mp hSa
  have hS2' : spEnd S ^ (2 ^ 1) = 1 := by rw [← spEnd_pow', pow_one, hS2, spEnd_one]
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_fix_add_range hodd hÂp v
  rw [hbot, Submodule.mem_bot] at hv₁
  subst hv₁
  rw [zero_add, eq_id_on_range_of_two_pow hodd hÂp hcyc hcomm hS2' w hw, spEnd_one]
  rfl

theorem sp_fixedFactor_equiv [Finite K] {f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r) {a : StatedSp r K}
    (hap : orderOf a = p) (hxo : orderOf (proj r K a) = p)
    (hker : LinearMap.ker (spEnd a - 1) ≠ ⊥) :
    ∃ s : ℕ, 1 ≤ s ∧ Nonempty (↥(spFixedFactor a) ≃* StatedSp s K) := by
  obtain ⟨-, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hK hp
    hp2 (by omega : p ≠ 2) hr (proj r K a) hxo
  have blocks := hblocks a rfl hap
  have hfix := blocks.fixed_eq
  have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd a) := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hev : (spEnd a).HasEigenvalue 1 := by
      refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
      rw [Module.End.mem_eigenspace_iff, one_smul]
      exact mem_ker_sub_one_iff.mp hv
    refine mem_primaryFactors.mpr ⟨?_, ?_, ?_⟩
    · simpa using irreducible_X_sub_C (1 : K)
    · simpa using monic_X_sub_C (1 : K)
    · simpa using dvd_iff_isRoot.mpr (Module.End.hasEigenvalue_iff_isRoot.mp hev)
  obtain ⟨φ, hφ⟩ := blocks.fixedFactor hmem
  have hnd := blocks.fixed_nondegenerate
  have hBalt : ((spForm r K).restrict (primaryComponent (spEnd a) (X - 1))).IsAlt :=
    fun z => spForm_isAlt z.1
  obtain ⟨s, hs, ⟨e⟩⟩ := KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hBalt hnd
  have hpos : 0 < Module.finrank K (primaryComponent (spEnd a) (X - 1)) := by
    have : Nontrivial (primaryComponent (spEnd a) (X - 1)) := by
      rw [Submodule.nontrivial_iff_ne_bot, hfix]
      exact hker
    exact Module.finrank_pos
  exact ⟨s, by omega, ⟨φ.trans e⟩⟩

theorem sp_fixedFactor_quasisimple [Finite K] {f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r) {a : StatedSp r K}
    (hap : orderOf a = p) (hxo : orderOf (proj r K a) = p)
    (hker : LinearMap.ker (spEnd a - 1) ≠ ⊥) (hq4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple ↥(spFixedFactor a) := by
  obtain ⟨s, hs, ⟨e⟩⟩ := sp_fixedFactor_equiv hp hp2 hK hf hr hap hxo hker
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs (Or.inl (Or.inr hq4))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq

theorem sp_isComponent [Finite K] {f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r) {a : StatedSp r K}
    (hap : orderOf a = p) (hxo : orderOf (proj r K a) = p)
    (hker : LinearMap.ker (spEnd a - 1) ≠ ⊥) (hq4 : 4 ≤ Nat.card K) :
    IsComponentOf (Subgroup.centralizer ({a} : Set (StatedSp r K))) (spFixedFactor a) := by
  have hq := sp_fixedFactor_quasisimple hp hp2 hK hf hr hap hxo hker hq4
  have := isComponentOf_map_block (MonoidHom.id (StatedSp r K)) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) a (spFixedFactor a) hq (spFixedFactor_le_centralizer a)
    (fun g hg f hf => spFixedFactor_conj hg hf)
  simpa using this

theorem sp_commute_of_centralizes [Finite K] [CharP K 2] {a g g' : StatedSp r K} (hodd : Odd p)
    (hap : a ^ p = 1) (hcyc : IsCyclicOn (spEnd a) (LinearMap.range (spEnd a - 1)))
    (hg : g ∈ Subgroup.centralizer ({a} : Set (StatedSp r K)))
    (hg' : g' ∈ Subgroup.centralizer ({a} : Set (StatedSp r K)))
    (hgD : g ∈ Subgroup.centralizer (spFixedFactor a : Set (StatedSp r K))) :
    g * g' = g' * g := by
  have hÂp : spEnd a ^ p = 1 := by rw [← spEnd_pow', hap, spEnd_one]
  have hga : spEnd g * spEnd a = spEnd a * spEnd g :=
    spEnd_comm_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hga' : spEnd g' * spEnd a = spEnd a * spEnd g' :=
    spEnd_comm_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hg')
  obtain ⟨l, hl⟩ := scalar_on_fix_of_centralizes hgD
  apply spEnd_injective
  refine LinearMap.ext fun v => ?_
  rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply]
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_fix_add_range hodd hÂp v
  have hv₁' : spEnd g' v₁ ∈ LinearMap.ker (spEnd a - 1) := by
    rw [LinearMap.mem_ker]
    have := congrArg (fun f : Module.End K _ => f v₁) hga'
    simp only [Module.End.mul_apply] at this
    have h0 : (spEnd a - 1) v₁ = 0 := LinearMap.mem_ker.mp hv₁
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← this, h0]
  rw [map_add, map_add, map_add, map_add, hl _ hv₁', hl _ hv₁, map_smul]
  congr 1
  exact commute_on_range hcyc hga hga' w hw

theorem sp_solvable [Finite K] [CharP K 2] {a : StatedSp r K} (hodd : Odd p) (hap : a ^ p = 1)
    (hcyc : IsCyclicOn (spEnd a) (LinearMap.range (spEnd a - 1))) :
    Group.IsSolvable ↥(Subgroup.centralizer ({a} : Set (StatedSp r K)) ⊓
      Subgroup.centralizer ((⨆ _ : Unit, spFixedFactor a : Subgroup (StatedSp r K)) :
        Set (StatedSp r K))) := by
  rw [iSup_const]
  refine Group.isSolvable_of_comm fun u v => Subtype.ext ?_
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp u.2
  exact sp_commute_of_centralizes hodd hap hcyc hu1 (Subgroup.mem_inf.mp v.2).1 hu2

section Transvections

variable [CharP K 2]

theorem spForm_comm' (u w : Fin r ⊕ Fin r → K) : spForm r K u w = spForm r K w u :=
  alt_comm spForm_isAlt u w

theorem spTransvection_sq (u : Fin r ⊕ Fin r → K) :
    spTransvection u (1 : K) ^ 2 = 1 := by
  apply spEnd_injective
  refine LinearMap.ext fun y => ?_
  rw [pow_two, spEnd_mul, Module.End.mul_apply, spEnd_one, Module.End.one_apply,
    spEnd_spTransvection, spEnd_spTransvection]
  have h0 : spForm r K u u = 0 := spForm_isAlt u
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h0,
    mul_zero, add_zero, one_mul]
  rw [add_assoc, ← add_smul, ← two_smul K, show (2 : K) = 0 from CharP.cast_eq_zero K 2]
  simp

theorem spTransvection_ne_one {v v' : Fin r ⊕ Fin r → K} (hB : spForm r K v v' ≠ 0) :
    spTransvection v (1 : K) ≠ 1 := by
  intro h
  have hv : v ≠ 0 := fun h0 => hB (by rw [h0, map_zero, LinearMap.zero_apply])
  have h1 := congrArg (fun g : StatedSp r K => spEnd g v') h
  simp only [spEnd_one, Module.End.one_apply, spEnd_spTransvection] at h1
  have h2 : (1 * spForm r K v' v) • v = 0 := by
    have := h1
    rw [add_eq_left] at this
    exact this
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact hB (by rw [spForm_comm']; simpa using h3)
  · exact hv h3

theorem spTransvection_noncomm {v v' : Fin r ⊕ Fin r → K} (hB : spForm r K v v' ≠ 0) :
    spTransvection v (1 : K) * spTransvection v' 1 ≠ spTransvection v' 1 * spTransvection v 1 := by
  intro h
  have hv' : v' ≠ 0 := fun h0 => hB (by rw [h0, map_zero])
  have h1 := congrArg (fun g : StatedSp r K => spEnd g v') h
  simp only [spEnd_mul, Module.End.mul_apply, spEnd_spTransvection] at h1
  have h0 : spForm r K v' v' = 0 := spForm_isAlt v'
  simp only [h0, mul_zero, zero_smul, add_zero, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, one_mul] at h1
  have h2 : ((0 + spForm r K v' v * spForm r K v v') • v' : Fin r ⊕ Fin r → K) = 0 := by
    simpa using h1
  rw [zero_add] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hB (by rw [spForm_comm']; exact h4)
    · exact hB h4
  · exact hv' h3

theorem sp_pair [Finite K] {σ : K ≃+* K} {a : StatedSp r K} (hodd : Odd p) (hap : a ^ p = 1)
    (ha : fieldSp r K σ a = a) (hker : LinearMap.ker (spEnd a - 1) ≠ ⊥) :
    ∃ t₁ ∈ spFixedFactor a, fieldSp r K σ t₁ = t₁ ∧ ∃ t₂ ∈ spFixedFactor a,
      fieldSp r K σ t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧
        t₁ * t₂ ≠ t₂ * t₁ := by
  obtain ⟨v, v', hv, hv', hσv, hσv', hB⟩ := exists_rational_pair hodd hap ha hker
  have hB' : spForm r K v' v ≠ 0 := by rw [spForm_comm']; exact hB
  have hv1 : spEnd a v = v := mem_ker_sub_one_iff.mp hv
  have hv1' : spEnd a v' = v' := mem_ker_sub_one_iff.mp hv'
  refine ⟨spTransvection v 1, spTransvection_mem_spFixedFactor hv1 1,
    fieldSp_spTransvection σ hσv 1 (map_one σ), spTransvection v' 1,
    spTransvection_mem_spFixedFactor hv1' 1, fieldSp_spTransvection σ hσv' 1 (map_one σ),
    ⟨1, ?_⟩, ⟨1, ?_⟩, spTransvection_noncomm hB⟩
  · rw [pow_one]
    exact orderOf_eq_prime (spTransvection_sq v) (spTransvection_ne_one hB)
  · rw [pow_one]
    exact orderOf_eq_prime (spTransvection_sq v') (spTransvection_ne_one hB')

theorem sp_fix_nondegenerate [Finite K] {a : StatedSp r K} (hodd : Odd p) (hap : a ^ p = 1) :
    ((spForm r K).restrict (LinearMap.ker (spEnd a - 1))).Nondegenerate := by
  have hÂp : spEnd a ^ p = 1 := by rw [← spEnd_pow', hap, spEnd_one]
  have hBn : ∀ v, (∀ w, spForm r K v w = 0) → v = 0 := fun v hv =>
    (spForm_nondegenerate (r := r) (K := K)).1 v hv
  have hsep := fix_sep hBn (spEnd_isom a) hodd hÂp
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · apply Subtype.ext
    exact hsep x.1 x.2 (fun v' hv' => hx ⟨v', hv'⟩)
  · apply Subtype.ext
    exact hsep y.1 y.2 (fun v' hv' => by rw [spForm_comm']; exact hy ⟨v', hv'⟩)

end Transvections

section Outer

theorem sp_outer [NeZero r] {σ : K ≃+* K} (hσ1 : σ ≠ 1) {a : StatedSp r K}
    (hker : LinearMap.ker (spEnd a - 1) ≠ ⊥)
    (hnd : ((spForm r K).restrict (LinearMap.ker (spEnd a - 1))).Nondegenerate) :
    ∀ e ∈ spFixedFactor a, ¬ ∀ g ∈ spFixedFactor a, fieldSp r K σ g = e * g * e⁻¹ := by
  intro e _ H
  let A' : gsp r K := ⟨((e⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp (e⁻¹).2⟩
  have hfix : ∀ g ∈ spFixedFactor a, semiConj A' σ g = g := by
    intro g hg
    rw [semiConj_apply, H g hg]
    apply Subtype.ext
    rw [coe_conjSp]
    simp [A']
    group
  obtain ⟨hσ, -⟩ := line_scalar_of_fixedFactor A' σ hfix hnd hker
  exact hσ1 hσ

end Outer

theorem sp_model [Finite K] {f₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ (p * f₀)) (hf₀ : 1 ≤ f₀) (hr : 1 ≤ r) {a : StatedSp r K}
    (hap : orderOf a = p) (hxo : orderOf (proj r K a) = p)
    (hker : LinearMap.ker (spEnd a - 1) ≠ ⊥) :
    ∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
      LieModel (↥(spFixedFactor a) ⧸ Subgroup.center ↥(spFixedFactor a)) t' n' 2 (p * f') := by
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  obtain ⟨s, hs, ⟨e⟩⟩ := sp_fixedFactor_equiv hp hp2 hK hf hr hap hxo hker
  have hq : 4 ≤ 2 ^ (p * f₀) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [hp.two_le])
  let e3 : ↥(spFixedFactor a) ⧸ Subgroup.center ↥(spFixedFactor a) ≃*
      StatedSp s K ⧸ Subgroup.center (StatedSp s K) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  rcases Nat.lt_or_ge s 2 with hs1 | hs2
  · obtain rfl : s = 1 := by omega
    let eSL : StatedSp 1 K ⧸ Subgroup.center (StatedSp 1 K) ≃*
        SL(2, K) ⧸ Subgroup.center SL(2, K) :=
      QuotientGroup.congr _ _ (longBlockEquivOne K).symm
        (Subgroup.map_center_eq (longBlockEquivOne K).symm)
    let eP : SL(2, K) ⧸ Subgroup.center SL(2, K) ≃* projectiveSL 2 K :=
      QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 2 K).symm
    have hmodel : LieModel (↥(spFixedFactor a) ⧸ Subgroup.center ↥(spFixedFactor a)) .PSL 2 2
        (p * f₀) :=
      (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, hf, le_rfl,
        fun hc => by have := (Prod.mk.inj hc).2; omega,
        fun hc => by have := (Prod.mk.inj hc).2; omega⟩, K, inferInstance, inferInstance, hK,
        ⟨(e3.trans (eSL.trans eP)).trans
          ((projectiveSpecialLinearEquivProjectiveSL 2 K).symm.trans
            (projectiveSpecialLinearGroupEquivStatedProj 2 K))⟩⟩
    exact ⟨.PSL, 2, f₀, hf₀, hmodel⟩
  · have hadm : StatedLieAdmissible .PSp s 2 (p * f₀) :=
      ⟨Nat.prime_two, hf, hs2, fun hc => by have := (Prod.mk.inj hc).2; omega⟩
    have hmodel : LieModel (StatedSp s K ⧸ Subgroup.center (StatedSp s K)) .PSp s 2 (p * f₀) :=
      (lieModel_classical_iff (by decide)).mpr
        (CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient s K hadm hK)
    exact ⟨.PSp, s, f₀, hf₀, lieModel_of_mulEquiv e3.symm hmodel⟩

theorem sp_good_conclusion [Finite K] [CharP K 2] [NeZero r] {f₀ : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀))
    (hrank : CFSG.pRank p (StatedSp r K) ≤ 1) {σ : K ≃+* K} (hσ1 : σ ≠ 1) {a S : StatedSp r K}
    (hap : a ^ p = 1) (ha1 : a ≠ 1) (hxo : orderOf (proj r K a) = p)
    (hσa : fieldSp r K σ a = a) (hS2 : S ^ 2 = 1) (hS1 : S ≠ 1) (hSa : S * a = a * S) :
    GoodConclusion p (StatedSp r K) (fieldSp r K σ) a := by
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have : Fact p.Prime := ⟨hp⟩
  have hao : orderOf a = p := orderOf_eq_prime hap ha1
  have hcyc := sp_cyclic_of_rank hp hodd hap ha1 hrank
  have hS : S ∈ Subgroup.centralizer ({a} : Set (StatedSp r K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hSa
  have hker := sp_fix_ne_bot hodd hap hcyc hS hS2 hS1
  have hnd := sp_fix_nondegenerate hodd hap
  have hcomp := sp_isComponent hp hp2 hK hf hr hao hxo hker hq4
  have hsolv := sp_solvable hodd hap hcyc
  have hQ : ∀ _ : Unit, IsComponentOf (Subgroup.centralizer ({a} : Set (StatedSp r K)))
      (spFixedFactor a) := fun _ => hcomp
  have hlayer := inSubgroup_layer_eq_of_decomposition (fun _ : Unit => spFixedFactor a) hQ hsolv
  rw [iSup_const] at hlayer
  refine ⟨⟨_, hcomp⟩, fun E hE _ => ?_, fun g hg _ hg2 => ?_⟩
  · obtain ⟨_, rfl⟩ :=
      isComponentOf_eq_of_decomposition (fun _ : Unit => spFixedFactor a) hQ hsolv hE
    exact ⟨sp_outer hσ1 hker hnd, sp_model hp hp2 hK hf₀ hr hao hxo hker,
      sp_pair hodd hap hσa hker⟩
  · rw [hlayer]
    obtain ⟨k, hk⟩ := hg2
    exact two_mem_spFixedFactor hodd hap hcyc hg (k := k) (by rw [← hk]; exact pow_orderOf_eq_one g)

end CFSG.RankThree.PartOne
