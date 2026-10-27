module

public import CFSG.LocalAnalysis.StandardType.ExcPos.StrictNeighbour
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ExcPosFinite
import CFSG.Milestones.ASVolI.A3OddFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Perf
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusAltEight
import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
import Mathlib.GroupTheory.IsPerfect
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import CFSG.Walter.W67.Statements

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

theorem false_of_mulEquiv_alt5 {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B D J : Subgroup X} (hBcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (hBexp : ∀ b ∈ B, b ^ p = 1) (hDB : D ≤ B) (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hBC : B ⊓ Subgroup.centralizer (J : Set X) ≤ D) (hcard : p * Nat.card D < Nat.card B)
    (e : J ≃* alternatingGroup (Fin 5)) : False := by
  classical
  set f : B →* MulAut J := (Subgroup.normalizerMonoidHom J).comp (Subgroup.inclusion hBJ)
  set H : Subgroup (MulAut (alternatingGroup (Fin 5))) := f.range.map (MulAut.congr e).toMonoidHom
  have hHcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩ _ ⟨_, ⟨c, rfl⟩, rfl⟩
    have hbc : b * c = c * b := Subtype.ext (hBcomm _ b.2 _ c.2)
    simp only [← map_mul, hbc]
  have hHexp : ∀ x ∈ H, x ^ p = 1 := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    have hbp : b ^ p = 1 := Subtype.ext (by simpa using hBexp _ b.2)
    simp only [← map_pow, hbp, map_one]
  have hHle : Nat.card H ≤ p := exc_A5_aut_elementaryAbelian_card_le p hp hp2 H hHcomm hHexp
  have hHcard : Nat.card H = Nat.card f.range :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hker : f.ker ≤ D.subgroupOf B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_subgroupOf]
    refine hBC ⟨b.2, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
    have h1 : (((f b) ⟨j, hj⟩ : J) : X) = (b : X) * j * (b : X)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
    rw [hb, MulAut.one_apply] at h1
    calc j * b = ((b : X) * j * (b : X)⁻¹) * b := by rw [← h1]
      _ = b * j := by group
  have hkercard : Nat.card f.ker ≤ Nat.card D :=
    (Subgroup.card_le_of_le hker).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv).le
  have hle : Nat.card B ≤ Nat.card D * p := by
    rw [← Subgroup.card_ker_mul_card_range f]
    exact Nat.mul_le_mul hkercard (by rw [← hHcard]; exact hHle)
  exact lt_irrefl _ (hcard.trans_le (hle.trans_eq (mul_comm _ _)))

theorem exists_orderOf_eq_centralizer_of_mulEquiv_alt {X : Type} [Group X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {J K : Subgroup X} {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (φ : K ≃* alternatingGroup (Fin n)) {d : X} (hdN : d ∈ Subgroup.normalizer (K : Set X))
    (hdK : d ∉ Subgroup.centralizer (K : Set X)) (hdJ : d ∈ Subgroup.centralizer (J : Set X))
    (hdp : d ^ p = 1) :
    ∃ σ : alternatingGroup (Fin n), orderOf (σ : Equiv.Perm (Fin n)) = p ∧
      (J.subgroupOf K).map φ.toMonoidHom ≤ Subgroup.centralizer {σ} := by
  haveI := Fact.mk hp
  set α : MulAut K := Subgroup.normalizerMonoidHom K ⟨d, hdN⟩ with hα
  have hαk : ∀ k : K, ((α k : K) : X) = d * k * d⁻¹ := fun k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hα1 : α ≠ 1 := by
    intro h
    refine hdK (Subgroup.mem_centralizer_iff.2 fun k hk => ?_)
    have h1 : ((α ⟨k, hk⟩ : K) : X) = d * k * d⁻¹ := hαk ⟨k, hk⟩
    rw [h, MulAut.one_apply] at h1
    calc k * d = (d * k * d⁻¹) * d := by rw [← h1]
      _ = d * k := by group
  have hαp : α ^ p = 1 := by
    rw [hα, ← map_pow, show (⟨d, hdN⟩ : Subgroup.normalizer (K : Set X)) ^ p = 1 from
      Subtype.ext (by simpa using hdp), map_one]
  have hordα : orderOf α = p := orderOf_eq_prime hαp hα1
  obtain ⟨l, hl⟩ := CFSG.ASVolI.burnsideA315x_out_alt hn5 hn8 φ α
    (by rw [hordα]; exact hp.odd_of_ne_two hp2)
  have hcenter : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hl1 : l ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [hl, map_one])
  have hlp : l ^ p = 1 := by
    have hc : MulAut.conj (l ^ p) = 1 := by rw [map_pow, ← hl, hαp]
    have hz : φ (l ^ p) ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := φ.surjective g
      rw [← map_mul, ← map_mul]
      have h1 : l ^ p * k * (l ^ p)⁻¹ = k := by
        have := congrArg (fun a : MulAut K => a k) hc
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      congr 1
      calc k * l ^ p = (l ^ p * k * (l ^ p)⁻¹) * l ^ p := by rw [h1]
        _ = l ^ p * k := by group
    rw [hcenter, Subgroup.mem_bot] at hz
    exact φ.injective (hz.trans (map_one φ).symm)
  refine ⟨φ l, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_eq_prime hlp hl1]
  · rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hjX : (j : X) ∈ J := hj
    have hdj : (j : X) * d = d * j := Subgroup.mem_centralizer_iff.1 hdJ _ hjX
    have h1 : α j = j := by
      apply Subtype.ext
      rw [hαk]
      calc d * (j : X) * d⁻¹ = (j * d) * d⁻¹ := by rw [hdj]
        _ = j := by group
    rw [hl, MulAut.conj_apply] at h1
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul]
    congr 1
    calc j * l = (l * j * l⁻¹) * l := by rw [h1]
      _ = l * j := by group

private noncomputable def imageEquiv {X A : Type*} [Group X] [Group A] {J K : Subgroup X}
    (hJK : J ≤ K) (φ : K ≃* A) : J ≃* (J.subgroupOf K).map φ.toMonoidHom :=
  (Subgroup.subgroupOfEquivOfLe hJK).symm.trans
    ((J.subgroupOf K).equivMapOfInjective φ.toMonoidHom φ.injective)

private theorem not_le_solvable_image {X A : Type*} [Group X] [Group A] {J K : Subgroup X}
    [Group.IsPerfect J] [Nontrivial J] (hJK : J ≤ K) (φ : K ≃* A) {C : Subgroup A}
    (hC : Group.IsSolvable C) (hJC : (J.subgroupOf K).map φ.toMonoidHom ≤ C) : False := by
  haveI := hC
  exact Group.IsPerfect.not_isSolvable J
    (solvable_of_solvable_injective
      (f := (Subgroup.inclusion hJC).comp (imageEquiv hJK φ).toMonoidHom)
      ((Subgroup.inclusion_injective hJC).comp (imageEquiv hJK φ).injective))

theorem false_of_mulEquiv_alt8 {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B D J K : Subgroup X} (hBcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (hBexp : ∀ b ∈ B, b ^ p = 1) (hDB : D ≤ B) (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hBC : B ⊓ Subgroup.centralizer (J : Set X) = D) (hcard : p * Nat.card D < Nat.card B)
    [Group.IsPerfect J] [Nontrivial J] (hJK : J ≤ K)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hDK : ¬ D ≤ Subgroup.centralizer (K : Set X))
    (φ : K ≃* alternatingGroup (Fin 8)) : False := by
  classical
  obtain ⟨d, hdD, hdK⟩ := SetLike.not_le_iff_exists.1 hDK
  have hdC : d ∈ Subgroup.centralizer (J : Set X) := by
    have h := hdD
    rw [← hBC] at h
    exact h.2
  obtain ⟨σ, hσp, hσJ⟩ := exists_orderOf_eq_centralizer_of_mulEquiv_alt hp hp2
    (by norm_num) le_rfl φ (hBK (hDB hdD)) hdK hdC (hBexp d (hDB hdD))
  haveI : Group.IsPerfect ((J.subgroupOf K).map φ.toMonoidHom) :=
    Group.IsPerfect.ofSurjective (f := (imageEquiv hJK φ).toMonoidHom)
      (imageEquiv hJK φ).surjective
  haveI := Fact.mk hp
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := (σ : Equiv.Perm (Fin 8)))
    (by rw [hσp]; exact hp)
  rw [hσp] at hm
  have hsum := Equiv.Perm.sum_cycleType_le (σ : Equiv.Perm (Fin 8))
  rw [hm, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp8 : p ≤ 8 := (Nat.le_mul_of_pos_left p (Nat.succ_pos m)).trans hsum
  have key : Group.IsSolvable (Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 8)))) ∨
      Nat.card ((J.subgroupOf K).map φ.toMonoidHom) = 60 := by
    interval_cases p
    · obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
      · right
        rcases exc_A8_three_cycle_perfect σ.1 σ.2 (by rw [hm]; rfl) _ hσJ
          Subgroup.commutator_eq_self with h | h
        · exact absurd ((Nat.card_congr (imageEquiv hJK φ).toEquiv).trans h)
            Finite.one_lt_card.ne'
        · exact h
      · exact Or.inl (exc_A8_centralizer_solvable σ.1 σ.2
          (Or.inr (Or.inr ⟨hσp, by rw [hm]; rfl⟩)))
    · exact absurd hp (by norm_num)
    · exact Or.inl (exc_A8_centralizer_solvable σ.1 σ.2 (Or.inl hσp))
    · exact absurd hp (by norm_num)
    · exact Or.inl (exc_A8_centralizer_solvable σ.1 σ.2 (Or.inr (Or.inl hσp)))
    · exact absurd hp (by norm_num)
  rcases key with hsolv | h60
  · exact not_le_solvable_image hJK φ hsolv hσJ
  · obtain ⟨e⟩ := CFSG.Quasithin.A312J2.nonempty_mulEquiv_alt5_of_perfect (G := J) inferInstance
      ((Nat.card_congr (imageEquiv hJK φ).toEquiv).trans h60)
    exact false_of_mulEquiv_alt5 hp hp2 hBcomm hBexp hDB hBJ hBC.le hcard e

private theorem perfect_nontrivial_of_isQuasisimple {G : Type*} [Group G]
    (hG : CFSG.Assembly.IsQuasisimple G) : Group.IsPerfect G ∧ Nontrivial G := by
  haveI := hG.2
  exact ⟨⟨hG.1⟩, (QuotientGroup.mk'_surjective (Subgroup.center G)).nontrivial⟩

theorem strictNeighbour_isEmpty_mulEquiv_alt8
    {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X}
    {p : ℕ} {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) {e : X} (heD : e ∈ D) {K : Subgroup X}
    (hKG₀ : K ≤ G₀) (hKcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}))
    (hJK : J ≤ K) (hKne : K ≠ J) : IsEmpty (K ≃* alternatingGroup (Fin 8)) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨hBK, hDK⟩ := strictNeighbour_has_nontrivial_D_action hH heD hKG₀ hKcomp hJK hKne
  obtain ⟨-, -, -, -, hp, hp2, -, -, hEA, hB4, hDB, hD2, hBJ, hBC, hJcomp, -⟩ := hH
  have hBcomm : ∀ b ∈ B₁, ∀ c ∈ B₁, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (hEA.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  obtain ⟨hJp, hJn⟩ := perfect_nontrivial_of_isQuasisimple hJcomp.2.2
  have hcard : p * Nat.card D < Nat.card B₁ := by
    rw [hD2]
    calc p * p ^ 2 = p ^ 3 := by ring
      _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      _ ≤ Nat.card B₁ := hB4
  exact false_of_mulEquiv_alt8 hp hp2 hBcomm hEA.2 hDB hBJ hBC hcard hJK hBK hDK φ

theorem strictNeighbour_not_a3Case
    {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X}
    {p : ℕ} {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) {e : X} (heD : e ∈ D) {K : Subgroup X}
    (hKG₀ : K ≤ G₀) (hKcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}))
    (hJK : J ≤ K) (hKne : K ≠ J) (hKodd : Odd (Nat.card (Subgroup.center ↥K))) :
    ¬ GGSixLSevenA3Case K := by
  intro hA3
  obtain ⟨φ⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).1 hA3
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.AGLEmbedding.ToralCensus.center_eq_bot_of_mulEquiv_alt_eight hKcomp.2.2 hKodd φ
  exact (strictNeighbour_isEmpty_mulEquiv_alt8 hH heD hKG₀ hKcomp hJK hKne).false
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ)

end CFSG.StandardType.LieKnownR2.ExcPos
