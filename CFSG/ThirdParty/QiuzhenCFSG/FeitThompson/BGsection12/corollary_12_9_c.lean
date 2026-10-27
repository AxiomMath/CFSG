module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_8_e

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# corollary_12_9_c
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 12.9(c). -/
public theorem CFSG.corollary_12_9_c
    {M E E₁₂ E₁ E₂ E₃ A Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hq : q ∈ section12Tau1Primes M)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hCQ : subgroupCentralizerIn (section10Msigma M) Q = ⊥)
    (hcomm : ⁅A, Q⁆ ≠ ⊥) :
    subgroupCentralizerIn A Q ∈ section10PrimeOrderSubgroupsIn p A ∧
      ¬ Subgroup.centralizer (subgroupCentralizerIn A Q : Set G) ≤ M := by
  classical
  -- Get corollary_12_9_a
  have h_a := corollary_12_9_a hM hE hp hA hq hQ hCQ hcomm
  rcases h_a with ⟨hAQ_prime, hAQ_eq_CMsigma, hAQ_norm_M⟩
  have hAQ_card : Nat.card (↥⁅A, Q⁆) = p.val := by rcases hAQ_prime with ⟨_, h⟩; exact h
  have hAQ_le_A : ⁅A, Q⁆ ≤ A := by rcases hAQ_prime with ⟨h, _⟩; exact h
  rcases hAQ_norm_M with ⟨hAQ_M, hAQ_norm⟩
  have : Fact p.val.Prime := ⟨p.2⟩; have : Fact q.val.Prime := ⟨q.2⟩
  have hAE : A ≤ E := section12_rankTwo_le hA
  rcases section12_rankTwo_elementary hA with ⟨hAcard, hAelem⟩
  have : IsElementaryAbelian p.val A := hAelem
  have hAcomm : IsMulCommutative A := inferInstance
  have hAnormE : section10NormalIn A E := (corollary_12_6_a hM hE hp hA).1
  rcases hAnormE with ⟨hAE', hAnorm⟩
  have hE_normA : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE').1 hAnorm
  have hQE : Q ≤ E := hQ.1
  have hQcard : Nat.card Q = q.val := hQ.2
  have hQcyc : IsCyclic Q := isCyclic_of_prime_card hQcard
  have hQ_normA : Q ≤ Subgroup.normalizer (A : Set G) := hQE.trans hE_normA
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := Q)
  have htQ : (t : G) ∈ Q := t.property
  -- ===== PART 1: |C_A(Q)| = p =====
  have h_mem (a : G) (ha : a ∈ A) : ⁅a, (t : G)⁆ ∈ A := by
    have hconj : (t : G) * a⁻¹ * (t : G)⁻¹ ∈ A := by
      have hnorm := (Subgroup.mem_normalizer_iff (H := A)).mp (hQ_normA htQ)
      exact (hnorm a⁻¹).mp (Subgroup.inv_mem A ha)
    have hcalc : ⁅a, (t : G)⁆ = a * ((t : G) * a⁻¹ * (t : G)⁻¹) := by group
    rw [hcalc]; exact Subgroup.mul_mem A ha hconj
  have h_comm_mul (a b : G) (ha : a ∈ A) (hb : b ∈ A) :
      ⁅a * b, (t : G)⁆ = ⁅a, (t : G)⁆ * ⁅b, (t : G)⁆ := by
    have h_ax : a * ⁅b, (t : G)⁆ = ⁅b, (t : G)⁆ * a :=
      setLike_mul_comm (s := A) ha (h_mem b hb)
    have h_xy : ⁅a, (t : G)⁆ * ⁅b, (t : G)⁆ = ⁅b, (t : G)⁆ * ⁅a, (t : G)⁆ :=
      setLike_mul_comm (s := A) (h_mem a ha) (h_mem b hb)
    calc
      ⁅a * b, (t : G)⁆ = (a * b) * (t : G) * (a * b)⁻¹ * (t : G)⁻¹ := rfl
      _ = a * b * (t : G) * b⁻¹ * a⁻¹ * (t : G)⁻¹ := by simp [mul_assoc]
      _ = a * (b * (t : G) * b⁻¹ * (t : G)⁻¹) * (t : G) * a⁻¹ * (t : G)⁻¹ := by simp [mul_assoc]
      _ = a * ⁅b, (t : G)⁆ * (t : G) * a⁻¹ * (t : G)⁻¹ := rfl
      _ = (a * ⁅b, (t : G)⁆ * a⁻¹) * (a * (t : G) * a⁻¹ * (t : G)⁻¹) := by
        calc
          a * ⁅b, (t : G)⁆ * (t : G) * a⁻¹ * (t : G)⁻¹ =
            ((a * ⁅b, (t : G)⁆) * (t : G)) * a⁻¹ * (t : G)⁻¹ := by simp [mul_assoc]
          _ = (a * ⁅b, (t : G)⁆ * a⁻¹) * a * (t : G) * a⁻¹ * (t : G)⁻¹ := by simp [mul_assoc]
          _ = (a * ⁅b, (t : G)⁆ * a⁻¹) * (a * (t : G) * a⁻¹ * (t : G)⁻¹) := by simp [mul_assoc]
      _ = (a * ⁅b, (t : G)⁆ * a⁻¹) * ⁅a, (t : G)⁆ := rfl
      _ = ⁅b, (t : G)⁆ * ⁅a, (t : G)⁆ := by
        calc
          (a * ⁅b, (t : G)⁆ * a⁻¹) * ⁅a, (t : G)⁆ =
            ((a * ⁅b, (t : G)⁆) * a⁻¹) * ⁅a, (t : G)⁆ := rfl
          _ = ((⁅b, (t : G)⁆ * a) * a⁻¹) * ⁅a, (t : G)⁆ := by rw [h_ax]
          _ = (⁅b, (t : G)⁆ * (a * a⁻¹)) * ⁅a, (t : G)⁆ := by simp [mul_assoc]
          _ = (⁅b, (t : G)⁆ * 1) * ⁅a, (t : G)⁆ := by simp
          _ = ⁅b, (t : G)⁆ * ⁅a, (t : G)⁆ := by simp
      _ = ⁅a, (t : G)⁆ * ⁅b, (t : G)⁆ := by rw [h_xy]
  let φ : A →* A :=
    { toFun := fun a => ⟨⁅(a : G), (t : G)⁆, h_mem a a.property⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; exact h_comm_mul (a : G) (b : G) a.property b.property }
  let imG : Subgroup G := (MonoidHom.range φ).map A.subtype
  have h_imG_le_AQ : imG ≤ ⁅A, Q⁆ := by
    intro x hx; rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
    simpa [φ, imG] using Subgroup.commutator_mem_commutator a.property htQ
  have h_imG_nontriv : imG ≠ ⊥ := by
    intro hbot; apply hcomm
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha; rw [Subgroup.mem_centralizer_iff]; intro q hq
    have hmem_zp := ht ⟨q, hq⟩
    rcases Subgroup.mem_zpowers_iff.mp hmem_zp with ⟨n, hn⟩
    have hq_eq : q = ((t : G) ^ n) := by
      calc q = ((⟨q, hq⟩ : Q) : G) := rfl
        _ = ((t ^ n : Q) : G) := by rw [hn]
        _ = (t : G) ^ n := rfl
    rw [hq_eq]
    have ha_comm_t : (a : G) * (t : G) = (t : G) * (a : G) := by
      have hmem_range : φ ⟨a, ha⟩ ∈ MonoidHom.range φ :=
        MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
      have hmem_im : ((φ ⟨a, ha⟩ : G) : G) ∈ imG := by
        apply Subgroup.mem_map.mpr; exact ⟨φ ⟨a, ha⟩, hmem_range, rfl⟩
      have h_one : (φ ⟨a, ha⟩ : G) = 1 := by
        have := Subgroup.mem_bot.mp (by simpa [hbot] using hmem_im); simpa using this
      have hcomm_eq_one : ⁅(a : G), (t : G)⁆ = 1 := by simpa [φ] using h_one
      exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := a) (g₂ := (t : G))).mp hcomm_eq_one)
    have h_comm : Commute (a : G) (t : G) := ha_comm_t
    exact (h_comm.zpow_right n).symm
  have h_imG_card : Nat.card imG = p.val := by
    have h_dvd : Nat.card imG ∣ p.val := by
      have h := Subgroup.card_dvd_of_le h_imG_le_AQ; rwa [hAQ_card] at h
    have h_ne_one : Nat.card imG ≠ 1 := by
      intro hone; have h_eq_bot : imG = ⊥ := Subgroup.card_eq_one.mp hone
      exact h_imG_nontriv h_eq_bot
    rcases (Nat.Prime.eq_one_or_self_of_dvd p.2 _ h_dvd) with (h1 | hp_eq)
    · exact absurd h1 h_ne_one
    · exact hp_eq
  have h_range_card : Nat.card (MonoidHom.range φ) = p.val := by
    have h_equiv : MonoidHom.range φ ≃* imG :=
      Subgroup.equivMapOfInjective (MonoidHom.range φ) A.subtype (Subgroup.subtype_injective A)
    have h_card_eq : Nat.card (MonoidHom.range φ) = Nat.card imG :=
      Nat.card_congr h_equiv.toEquiv
    rw [h_card_eq, h_imG_card]
  have h_ker_card : Nat.card (MonoidHom.ker φ) = p.val := by
    have h_card_A_eq : Nat.card A = Nat.card (MonoidHom.ker φ) * Nat.card (MonoidHom.range φ) := by
      calc
        Nat.card A = Nat.card (A ⧸ MonoidHom.ker φ) * Nat.card (MonoidHom.ker φ) := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup]
        _ = Nat.card (MonoidHom.range φ) * Nat.card (MonoidHom.ker φ) := by
          rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
        _ = Nat.card (MonoidHom.ker φ) * Nat.card (MonoidHom.range φ) := mul_comm _ _
    rw [hAcard, h_range_card] at h_card_A_eq
    have hp_pos : p.val > 0 := Nat.Prime.pos p.2
    have h_mul : p.val * p.val = Nat.card (MonoidHom.ker φ) * p.val := by
      simpa [pow_two] using h_card_A_eq
    have h_mul' : p.val * p.val = p.val * Nat.card (MonoidHom.ker φ) := by
      calc p.val * p.val = Nat.card (MonoidHom.ker φ) * p.val := h_mul
        _ = p.val * Nat.card (MonoidHom.ker φ) := mul_comm _ _
    exact (Nat.eq_of_mul_eq_mul_left hp_pos h_mul').symm
  have h_ker_map_eq : (MonoidHom.ker φ).map A.subtype = subgroupCentralizerIn A Q := by
    ext x; constructor
    · intro hx; rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy_ker : φ y = 1 := hy
      have hx_in_A : (y : G) ∈ A := y.property
      refine ⟨hx_in_A, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr; intro q hq
      have hmem_zp := ht ⟨q, hq⟩
      rcases Subgroup.mem_zpowers_iff.mp hmem_zp with ⟨n, hn⟩
      have hq_eq : q = ((t : G) ^ n) := by
        calc q = ((⟨q, hq⟩ : Q) : G) := rfl
          _ = ((t ^ n : Q) : G) := by rw [hn]
          _ = (t : G) ^ n := rfl
      rw [hq_eq]
      have hy_comm_t : (y : G) * (t : G) = (t : G) * (y : G) := by
        have hcomm_eq_one : ⁅(y : G), (t : G)⁆ = 1 := by
          simpa [φ] using congrArg Subtype.val hy_ker
        exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := (y : G)) (g₂ := (t : G))).mp hcomm_eq_one)
      have h_comm : Commute (y : G) (t : G) := hy_comm_t
      exact (h_comm.zpow_right n).symm.eq
    · intro hx; rcases hx with ⟨hxA, hxC⟩
      let y : A := ⟨x, hxA⟩
      have hy_ker : φ y = 1 := by
        ext
        have hx_comm_t : x * (t : G) = (t : G) * x := by
          have hmem := (Subgroup.mem_centralizer_iff.mp hxC) (t : G) htQ; exact hmem.symm
        have h_comm : ⁅x, (t : G)⁆ = 1 := by
          exact (commutatorElement_eq_one_iff_mul_comm (g₁ := x) (g₂ := (t : G))).mpr hx_comm_t
        simpa [φ] using h_comm
      apply Subgroup.mem_map.mpr; exact ⟨y, hy_ker, rfl⟩
  have h_CAQ_card : Nat.card (subgroupCentralizerIn A Q) = p.val := by
    calc
      Nat.card (subgroupCentralizerIn A Q) = Nat.card ((MonoidHom.ker φ).map A.subtype) := by
        rw [h_ker_map_eq]
      _ = Nat.card (MonoidHom.ker φ) := by
        refine (Nat.card_congr ?_).symm
        exact (Subgroup.equivMapOfInjective (MonoidHom.ker φ) A.subtype
          (Subgroup.subtype_injective A)).toEquiv
      _ = p.val := h_ker_card
  have h_part1 : subgroupCentralizerIn A Q ∈ section10PrimeOrderSubgroupsIn p A := by
    rw [section10PrimeOrderSubgroupsIn]
    refine ⟨by simp [subgroupCentralizerIn, inf_le_left], h_CAQ_card⟩
  -- ===== PART 2: C_G(C_A(Q)) ≰ M =====
  have h_CAQ_ne_CMsigma : subgroupCentralizerIn A Q ≠
      subgroupCentralizerIn A (section10Msigma M) := by
    intro h_eq
    have h_not_conj : section12NotConjugate ⁅A, Q⁆ (subgroupCentralizerIn A Q) :=
      corollary_12_9_b hM hE hp hA hq hQ hCQ hcomm
    have hAQ_eq_CAQ : ⁅A, Q⁆ = subgroupCentralizerIn A Q := by rw [hAQ_eq_CMsigma, h_eq]
    have h_contra : ¬ section12NotConjugate ⁅A, Q⁆ (subgroupCentralizerIn A Q) := by
      intro hnc
      have h_conj_one : (⁅A, Q⁆).conjBy (1 : G) = ⁅A, Q⁆ := by
        rw [Subgroup.conjBy]
        have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
        rw [h, Subgroup.map_id]
      have h_eq : (⁅A, Q⁆).conjBy (1 : G) = subgroupCentralizerIn A Q := by
        rw [h_conj_one, hAQ_eq_CAQ]
      exact hnc 1 h_eq
    exact h_contra h_not_conj
  by_cases h_nonab : section12HasNonabelianSylowSubgroup p G
  · -- Case 1: nonabelian Sylow p-subgroup → Theorem 12.7(c)
    have h_CAQ_in_S_p_E : subgroupCentralizerIn A Q ∈ section10PrimeOrderSubgroupsIn p E := by
      rw [section10PrimeOrderSubgroupsIn]
      refine ⟨(by simp [subgroupCentralizerIn, inf_le_left] : _ ≤ A).trans hAE, h_CAQ_card⟩
    have h_thm := theorem_12_7_c hM hE hp hA h_nonab
      (subgroupCentralizerIn A Q) h_CAQ_in_S_p_E h_CAQ_ne_CMsigma
    rcases h_thm with ⟨_, h_cent_not_le_M⟩
    exact ⟨h_part1, h_cent_not_le_M⟩
  · -- Case 2: all Sylow p-subgroups abelian → Hall embedding → contradiction
    exfalso
    have h_abel_all : ∀ (P : Sylow p.val G), IsMulCommutative (P : Subgroup G) := by
      intro P; by_contra hPnonab; apply h_nonab; exact ⟨P, hPnonab⟩
    have hAp : IsPGroup p.val A := by
      have : IsElementaryAbelian p.val A := hAelem
      exact IsElementaryAbelian.isPGroup p.val A
    obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
    have hScomm : IsMulCommutative (S : Subgroup G) := h_abel_all S
    -- Destructure hE for Hall data
    rcases hE with ⟨hcomp, hE12data_tuple, hE1data_tuple, hE2data, hE3data⟩
    rcases hE12data_tuple with ⟨hE12E, hHallE12⟩
    rcases hE1data_tuple with ⟨hE1E12, hHallE1⟩
    -- Keep the original tuples for later reconstruction
    have hE12data : section12HallSubgroupIn (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E :=
      ⟨hE12E, hHallE12⟩
    have hE1data : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂ :=
      ⟨hE1E12, hHallE1⟩
    -- E is solvable (proper subgroup of minimal counterexample)
    have hE_solv : Group.IsSolvable E := by
      have hEproper : E ≠ ⊤ := by
        intro hEtop
        have htop_le_M : (⊤ : Subgroup G) ≤ M := by
          simpa [hEtop] using hcomp.2.1
        exact hM.1 (top_le_iff.mp htop_le_M)
      exact IsMinCE.proper_subgroups_solvable E (lt_top_iff_ne_top.2 hEproper)
    have : Group.IsSolvable E := hE_solv
    have hE12_solv : Group.IsSolvable E₁₂ :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hE12E)
    have : Group.IsSolvable E₁₂ := hE12_solv
    -- π₁₂ = τ₁ ∪ τ₂, π₁ = τ₁
    let π12 : Set Nat.Primes := section12Tau1Primes M ∪ section12Tau2Primes M
    let π1 : Set Nat.Primes := section12Tau1Primes M
    -- Q is a π₁₂-subgroup (|Q| = q and q ∈ τ₁ ⊆ π₁₂)
    have hQ_pi12 : IsPiSubgroup (G := G) π12 Q := by
      intro r hr
      rw [hQcard] at hr
      have hr_dvd_q : r.val ∣ q.val := hr
      have hr_eq_q_val : r.val = q.val := (Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hr_dvd_q
      have hr_eq_q : r = q := Subtype.ext hr_eq_q_val
      subst hr_eq_q
      exact Set.mem_union_left (section12Tau2Primes M) hq
    -- Trivial PUnit action for Hall theory
    let : MulDistribMulAction PUnit.{1} E := {
      smul := fun _ x => x
      one_smul := by intro x; rfl
      mul_smul := by intro a b x; rfl
      smul_mul := by intro a x y; rfl
      smul_one := by intro a; rfl }
    have hcopE : Nat.Coprime (Nat.card PUnit.{1}) (Nat.card E) := by simp
    have hQ_E_pi12 : IsPiSubgroup (G := E) π12 (Q.subgroupOf E) := by
      intro r hr
      have hcard_eq : Nat.card (Q.subgroupOf E) = Nat.card Q :=
        section12_card_subgroupOf_eq hQE
      rw [hcard_eq] at hr
      exact hQ_pi12 r hr
    have hQ_E_inv : IsInvariant PUnit.{1} E (Q.subgroupOf E) :=
      ⟨fun _ _ => ⟨id, id⟩⟩
    -- Embed Q.subgroupOf E into a Hall π₁₂-subgroup of ↥E, then conjugate to E₁₂.subgroupOf E
    rcases proposition_1_5_b hE_solv hcopE π12 (Q.subgroupOf E) hQ_E_pi12 hQ_E_inv with
      ⟨H_E, hH_E_hall, _, hQ_E_le_H⟩
    rcases exists_conj_eq_of_isHallSubgroup_of_solvable hE_solv hH_E_hall hHallE12 with
      ⟨e : E, he⟩
    -- he : E₁₂.subgroupOf E = H_E.map (MulAut.conj e).toMonoidHom
    have hQ_E_conj_le : (Q.subgroupOf E).map (MulAut.conj e).toMonoidHom ≤ E₁₂.subgroupOf E := by
      calc
        (Q.subgroupOf E).map (MulAut.conj e).toMonoidHom ≤
            H_E.map (MulAut.conj e).toMonoidHom := Subgroup.map_mono hQ_E_le_H
        _ = E₁₂.subgroupOf E := by rw [← he]
    -- Translate to G: Q^(e:G) ≤ E₁₂
    let eG : G := (e : E)
    have heG_E : eG ∈ E := (e : E).property
    have hQe_le_E12 : Q.map (MulAut.conj eG).toMonoidHom ≤ E₁₂ := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨q, hq, rfl⟩
      have hqE : q ∈ E := hQE hq
      have hq_E_mem : (⟨q, hqE⟩ : E) ∈ Q.subgroupOf E := by
        simpa [Subgroup.mem_subgroupOf] using hq
      have hconj_mem : (MulAut.conj e) (⟨q, hqE⟩ : E) ∈ E₁₂.subgroupOf E :=
        hQ_E_conj_le (Subgroup.mem_map.mpr ⟨⟨q, hqE⟩, hq_E_mem, rfl⟩)
      have hconj_mem' : ((MulAut.conj e) (⟨q, hqE⟩ : E) : G) ∈ E₁₂ := hconj_mem
      simpa [eG, MulAut.conj_apply] using hconj_mem'
    -- Conjugate Q^eG further into E₁ using Hall theory in ↥E₁₂
    have hQe_card : Nat.card (Q.map (MulAut.conj eG).toMonoidHom) = q.val := by
      apply (Nat.card_congr ?_).trans hQcard
      exact (Subgroup.equivMapOfInjective
        (f := (MulAut.conj eG).toMonoidHom) Q (MulAut.conj eG).injective).symm.toEquiv
    have hQe_pi1 : IsPiSubgroup (G := G) π1 (Q.map (MulAut.conj eG).toMonoidHom) := by
      intro r hr
      rw [hQe_card] at hr
      have hr_dvd_q : r.val ∣ q.val := hr
      have hr_eq_q_val : r.val = q.val :=
        (Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hr_dvd_q
      have hr_eq_q : r = q := Subtype.ext hr_eq_q_val
      subst hr_eq_q
      exact hq
    let : MulDistribMulAction PUnit.{1} E₁₂ := {
      smul := fun _ x => x
      one_smul := by intro x; rfl
      mul_smul := by intro a b x; rfl
      smul_mul := by intro a x y; rfl
      smul_one := by intro a; rfl }
    have hcopE12 : Nat.Coprime (Nat.card PUnit.{1}) (Nat.card E₁₂) := by simp
    have hQe_E12_pi1 : IsPiSubgroup (G := E₁₂) π1
        ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂) := by
      intro r hr
      have hcard_eq : Nat.card ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂) =
          Nat.card (Q.map (MulAut.conj eG).toMonoidHom) :=
        section12_card_subgroupOf_eq hQe_le_E12
      rw [hcard_eq] at hr
      exact hQe_pi1 r hr
    have hQe_E12_inv : IsInvariant PUnit.{1} E₁₂
        ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂) :=
      ⟨fun _ _ => ⟨id, id⟩⟩
    rcases proposition_1_5_b hE12_solv hcopE12 π1
      ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂) hQe_E12_pi1 hQe_E12_inv with
      ⟨H_E12, hH_E12_hall, _, hQe_E12_le_H⟩
    rcases exists_conj_eq_of_isHallSubgroup_of_solvable hE12_solv hH_E12_hall hHallE1 with
      ⟨f : E₁₂, hf⟩
    -- hf : E₁.subgroupOf E₁₂ = H_E12.map (MulAut.conj f).toMonoidHom
    have hQe_E12_conj_le :
        ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂).map
          (MulAut.conj f).toMonoidHom ≤ E₁.subgroupOf E₁₂ := by
      calc
        _ ≤ H_E12.map (MulAut.conj f).toMonoidHom := Subgroup.map_mono hQe_E12_le_H
        _ = E₁.subgroupOf E₁₂ := by rw [← hf]
    -- Translate to G: (Q^eG)^fG ≤ E₁
    let fG : G := (f : E₁₂)
    have hfG_E12 : fG ∈ E₁₂ := (f : E₁₂).property
    have hfG_E : fG ∈ E := hE12E hfG_E12
    have hQef_le_E1 : (Q.map (MulAut.conj eG).toMonoidHom).map
        (MulAut.conj fG).toMonoidHom ≤ E₁ := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨q, hq, rfl⟩
      have hq_E12 : q ∈ E₁₂ := hQe_le_E12 hq
      have hq_E12_mem : (⟨q, hq_E12⟩ : E₁₂) ∈
          (Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂ := by
        simpa [Subgroup.mem_subgroupOf] using hq
      have hconj_mem : (MulAut.conj f) (⟨q, hq_E12⟩ : E₁₂) ∈ E₁.subgroupOf E₁₂ :=
        hQe_E12_conj_le (Subgroup.mem_map.mpr ⟨⟨q, hq_E12⟩, hq_E12_mem, rfl⟩)
      have hconj_mem' : ((MulAut.conj f) (⟨q, hq_E12⟩ : E₁₂) : G) ∈ E₁ := hconj_mem
      simpa [fG, MulAut.conj_apply] using hconj_mem'
    -- Now Q^g ≤ E₁ where g = fG * eG
    let g : G := fG * eG
    have hg_E : g ∈ E := Subgroup.mul_mem E hfG_E heG_E
    have h_mulAut_comp : ((MulAut.conj fG) * (MulAut.conj eG)).toMonoidHom =
        (MulAut.conj fG).toMonoidHom.comp (MulAut.conj eG).toMonoidHom := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    have hQg_le_E1 : Q.map (MulAut.conj g).toMonoidHom ≤ E₁ := by
      calc
        Q.map (MulAut.conj g).toMonoidHom =
            Q.map (MulAut.conj (fG * eG)).toMonoidHom := rfl
        _ = Q.map ((MulAut.conj fG * MulAut.conj eG).toMonoidHom) := by
          rw [map_mul (MulAut.conj) fG eG]
        _ = Q.map ((MulAut.conj fG).toMonoidHom.comp (MulAut.conj eG).toMonoidHom) := by
          rw [h_mulAut_comp]
        _ = (Q.map (MulAut.conj eG).toMonoidHom).map
            (MulAut.conj fG).toMonoidHom := by rw [Subgroup.map_map]
        _ ≤ E₁ := hQef_le_E1
    -- X := Q^g is in section12PrimeOrderSubgroups E₁
    have hX_in_E1 : Q.map (MulAut.conj g).toMonoidHom ∈
        section12PrimeOrderSubgroups E₁ := by
      rw [section12PrimeOrderSubgroups]
      refine ⟨hQg_le_E1, ?_⟩
      refine ⟨q, ?_⟩
      apply (Nat.card_congr ?_).trans hQcard
      exact (Subgroup.equivMapOfInjective
        (f := (MulAut.conj g).toMonoidHom) Q (MulAut.conj g).injective).symm.toEquiv
    -- C_{M_σ}(Q^g) = ⊥
    have hg_M : g ∈ M := hcomp.2.1 hg_E
    have hMσ_conj (m : G) (hm : m ∈ M) (x : G) (hx : x ∈ section10Msigma M) :
        m * x * m⁻¹ ∈ section10Msigma M := by
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have h_conj_sub : (⟨m, hm⟩ * y * ⟨m⁻¹, Subgroup.inv_mem M hm⟩) ∈
          section10MsigmaSubgroup M :=
        (section10MsigmaSubgroup_normal M).conj_mem y hy ⟨m, hm⟩
      exact Subgroup.mem_map.mpr
        ⟨⟨m, hm⟩ * y * ⟨m⁻¹, Subgroup.inv_mem M hm⟩, h_conj_sub, by simp⟩
    have hCQ_Qg : subgroupCentralizerIn (section10Msigma M)
        (Q.map (MulAut.conj g).toMonoidHom) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rcases Subgroup.mem_inf.mp hx with ⟨hxMσ, hxC⟩
      have hx_conj_Mσ : g⁻¹ * x * g ∈ section10Msigma M := by
        have := hMσ_conj g⁻¹ (Subgroup.inv_mem M hg_M) x hxMσ
        simpa [inv_inv] using this
      have hx_conj_cent_Q : g⁻¹ * x * g ∈ Subgroup.centralizer (Q : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have hmem : g * q * g⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨q, hq, by simp [MulAut.conj_apply, mul_assoc]⟩
        have hxC_comm := (Subgroup.mem_centralizer_iff.mp hxC) (g * q * g⁻¹) hmem
        calc
          q * (g⁻¹ * x * g) = g⁻¹ * (g * q * g⁻¹ * x) * g := by simp [mul_assoc]
          _ = g⁻¹ * ((g * q * g⁻¹) * x) * g := by simp [mul_assoc]
          _ = g⁻¹ * (x * (g * q * g⁻¹)) * g := by rw [hxC_comm]
          _ = (g⁻¹ * x * g) * q := by simp [mul_assoc]
      have h_bot : g⁻¹ * x * g ∈
          section10Msigma M ⊓ Subgroup.centralizer (Q : Set G) :=
        Subgroup.mem_inf.mpr ⟨hx_conj_Mσ, hx_conj_cent_Q⟩
      have hCQ_expanded : section10Msigma M ⊓ Subgroup.centralizer (Q : Set G) = ⊥ :=
        calc
          section10Msigma M ⊓ Subgroup.centralizer (Q : Set G) =
              subgroupCentralizerIn (section10Msigma M) Q := rfl
          _ = ⊥ := hCQ
      rw [hCQ_expanded] at h_bot
      have h_one : g⁻¹ * x * g = 1 := Subgroup.mem_bot.mp h_bot
      calc
        x = 1 * x * 1 := by simp
        _ = (g * g⁻¹) * x * (g * g⁻¹) := by simp
        _ = g * (g⁻¹ * x * g) * g⁻¹ := by simp [mul_assoc]
        _ = g * 1 * g⁻¹ := by rw [h_one]
        _ = g * g⁻¹ := by simp
        _ = 1 := by simp
    -- Apply lemma_12_8_e: Q^g ≤ Z(E)
    have h_8e := lemma_12_8_e hM ⟨hcomp, hE12data, hE1data, hE2data, hE3data⟩ hp hA hAS hScomm
      (Q.map (MulAut.conj g).toMonoidHom) hX_in_E1 hCQ_Qg
    -- [A, Q^g] = ⊥ (since Q^g ≤ Z(E))
    have h_A_Qg_bot : ⁅A, Q.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      rcases Subgroup.mem_map.mp hq with ⟨q', hq', rfl⟩
      have hq_center : MulAut.conj g q' ∈ centerIn (G := G) E :=
        h_8e (Subgroup.mem_map.mpr ⟨q', hq', rfl⟩)
      rcases hq_center with ⟨hq_E, hq_cent⟩
      have h_comm_a := hq_cent a (hAE ha)
      exact h_comm_a.symm
    -- Relate [A, Q^g] to [A, Q]
    -- First, A^g = A since A ⊲ E and g ∈ E
    have : (A.subgroupOf E).Normal := hAnorm
    have hAg_eq_A : A.map (MulAut.conj g).toMonoidHom = A := by
      ext x; constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
        have haE : a ∈ E := hAE' ha
        let aE : E := ⟨a, haE⟩
        have ha_sub : aE ∈ A.subgroupOf E := by
          simpa [aE, Subgroup.mem_subgroupOf] using ha
        have h_conj : (⟨g, hg_E⟩ * aE * ⟨g, hg_E⟩⁻¹) ∈ A.subgroupOf E :=
          hAnorm.conj_mem aE ha_sub ⟨g, hg_E⟩
        have h_conj' : ((⟨g, hg_E⟩ * aE * ⟨g, hg_E⟩⁻¹ : E) : G) ∈ A := h_conj
        simpa [aE] using h_conj'
      · intro hx
        have hxE : x ∈ E := hAE' hx
        let xE : E := ⟨x, hxE⟩
        have hx_sub : xE ∈ A.subgroupOf E := by
          simpa [xE, Subgroup.mem_subgroupOf] using hx
        have h_conj : (⟨g⁻¹, Subgroup.inv_mem E hg_E⟩ * xE * ⟨g⁻¹, Subgroup.inv_mem E hg_E⟩⁻¹) ∈
            A.subgroupOf E :=
          hAnorm.conj_mem xE hx_sub ⟨g⁻¹, Subgroup.inv_mem E hg_E⟩
        let a' : G := g⁻¹ * x * g
        have ha'_A : a' ∈ A := by
          -- h_conj gives membership in A.subgroupOf E, which implies membership in A
          simpa [a', Subgroup.mem_subgroupOf] using h_conj
        refine Subgroup.mem_map.mpr ⟨a', ha'_A, ?_⟩
        dsimp [MulAut.conj_apply, a']
        simp [mul_assoc]
    -- [A, Q^g] = [A^g, Q^g] = [A, Q]^g via Subgroup.map_commutator
    have h_comm_conj : ⁅A, Q.map (MulAut.conj g).toMonoidHom⁆ =
        (⁅A, Q⁆).map (MulAut.conj g).toMonoidHom := by
      calc
        ⁅A, Q.map (MulAut.conj g).toMonoidHom⁆ =
            ⁅A.map (MulAut.conj g).toMonoidHom,
              Q.map (MulAut.conj g).toMonoidHom⁆ := by rw [hAg_eq_A]
        _ = (⁅A, Q⁆).map (MulAut.conj g).toMonoidHom := by
          rw [← Subgroup.map_commutator (f := (MulAut.conj g).toMonoidHom) (H₁ := A) (H₂ := Q)]
    -- [A, Q]^g = [A, Q] since g ∈ M and [A, Q] ⊲ M
    have h_AQ_conj_eq : (⁅A, Q⁆).map (MulAut.conj g).toMonoidHom = ⁅A, Q⁆ := by
      ext x; constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        let yM : M := ⟨y, hAQ_M hy⟩
        have hy_sub : yM ∈ (⁅A, Q⁆.subgroupOf M) := by
          simpa [yM, Subgroup.mem_subgroupOf] using hy
        have h_conj : (⟨g, hg_M⟩ * yM * ⟨g, hg_M⟩⁻¹) ∈ (⁅A, Q⁆.subgroupOf M) :=
          hAQ_norm.conj_mem yM hy_sub ⟨g, hg_M⟩
        have h_conj' : ((⟨g, hg_M⟩ * yM * ⟨g, hg_M⟩⁻¹ : M) : G) ∈ ⁅A, Q⁆ := h_conj
        simpa [yM] using h_conj'
      · intro hx
        have hxM : x ∈ M := hAQ_M hx
        let xM : M := ⟨x, hxM⟩
        have hx_sub : xM ∈ (⁅A, Q⁆.subgroupOf M) := by
          simpa [xM, Subgroup.mem_subgroupOf] using hx
        have h_conj : (⟨g⁻¹, Subgroup.inv_mem M hg_M⟩ * xM *
            ⟨g⁻¹, Subgroup.inv_mem M hg_M⟩⁻¹) ∈ (⁅A, Q⁆.subgroupOf M) :=
          hAQ_norm.conj_mem xM hx_sub ⟨g⁻¹, Subgroup.inv_mem M hg_M⟩
        let y' : G := g⁻¹ * x * g
        have hy'_AQ : y' ∈ ⁅A, Q⁆ := by
          -- h_conj gives membership in (⁅A, Q⁆).subgroupOf M
          simpa [y', Subgroup.mem_subgroupOf] using h_conj
        refine Subgroup.mem_map.mpr ⟨y', hy'_AQ, ?_⟩
        dsimp [MulAut.conj_apply, y']
        simp [mul_assoc]
    -- Combine: [A,Q] = ⊥, contradiction
    rw [h_comm_conj, h_AQ_conj_eq] at h_A_Qg_bot
    exact hcomm h_A_Qg_bot

end Section12
