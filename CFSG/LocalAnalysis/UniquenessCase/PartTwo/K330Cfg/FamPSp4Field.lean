module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherOuterQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven (fixedBy mem_fixedBy fixedBy_map_congr)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.RankThree.PartOne.KCSpComm
open CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.CASymplecticSubfield

private theorem k330c_mem_fixedBy_zpowers_iff {T : Type*} [Group T] (f : MulAut T) (x : T) :
    x ∈ fixedBy (Subgroup.zpowers f) ↔ f x = x := by
  rw [mem_fixedBy]
  refine ⟨fun h => h f (Subgroup.mem_zpowers f), fun h w hw => ?_⟩
  have h1 : w • x = x :=
    smul_eq_self_of_mem_zpowers hw (by simpa [MulAut.smul_def] using h)
  simpa [MulAut.smul_def] using h1

private theorem k330c_congr_conj_apply {J T : Type} [Group J] [Group T] (e : J ≃* T)
    (g x : MulAut J) :
    MulAut.congr e (MulAut.conj g x) = MulAut.conj (MulAut.congr e g) (MulAut.congr e x) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem k330c_congr_congr_symm {J T : Type} [Group J] [Group T] (e : J ≃* T)
    (x : MulAut T) : MulAut.congr e (MulAut.congr e.symm x) = x := by
  ext y
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply]

private theorem k330c_fixedBy_conj_map {J T : Type} [Group J] [Group T] (e : J ≃* T)
    (φ : MulAut J) (n : J) :
    ((fixedBy (Subgroup.zpowers φ)).map (MulAut.conj n).toMonoidHom).map e.toMonoidHom =
      (fixedBy (Subgroup.zpowers (MulAut.congr e φ))).map
        (MulAut.conj (e n)).toMonoidHom := by
  have hcomp : e.toMonoidHom.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj (e n)).toMonoidHom.comp e.toMonoidHom := by
    ext x
    change e (MulAut.conj n x) = MulAut.conj (e n) (e x)
    simp only [MulAut.conj_apply, map_mul, map_inv]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, fixedBy_map_congr e (Subgroup.zpowers φ),
    MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom]

private theorem k330c_hasFieldRP_of_mulEquiv {J T : Type} [Group J] [Finite J] [Group T]
    [Finite T] (e : J ≃* T) {Q : ℕ} {B : ℕ → ℕ} (h : HasFieldRP T Q B) :
    HasFieldRP J Q B := by
  intro W hW h7J
  have h7T : ¬ 7 ∣ Nat.card T := by
    rw [← Nat.card_congr e.toEquiv]
    exact h7J
  have hW' : Nat.card (W.map (MulAut.congr e).toMonoidHom) = 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hW]
  obtain ⟨g', φ', hφ', hWg', hrig', hpair', k, hk, hbound'⟩ :=
    h (W.map (MulAut.congr e).toMonoidHom) hW' h7T
  let g : MulAut J := MulAut.congr e.symm g'
  let φ : MulAut J := MulAut.congr e.symm φ'
  have hge : MulAut.congr e g = g' := k330c_congr_congr_symm e g'
  have hφe : MulAut.congr e φ = φ' := k330c_congr_congr_symm e φ'
  have hfixmap : (fixedBy (Subgroup.zpowers φ)).map e.toMonoidHom =
      fixedBy (Subgroup.zpowers φ') := by
    rw [fixedBy_map_congr e (Subgroup.zpowers φ), MonoidHom.map_zpowers,
      MulEquiv.coe_toMonoidHom, hφe]
  have hzpow : Subgroup.zpowers φ' = (Subgroup.zpowers φ).map (MulAut.congr e).toMonoidHom := by
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hφe]
  refine ⟨g, φ, ?_, ?_, ?_, ?_, k, hk, ?_⟩
  · change orderOf ((MulAut.congr e.symm).toMonoidHom φ') = 7
    rw [orderOf_injective (MulAut.congr e.symm).toMonoidHom (MulAut.congr e.symm).injective φ']
    exact hφ'
  · have hmapconj : ((Subgroup.zpowers φ).map (MulAut.conj g).toMonoidHom).map
        (MulAut.congr e).toMonoidHom =
        (Subgroup.zpowers φ').map (MulAut.conj g').toMonoidHom := by
      rw [Subgroup.map_map]
      have hcomp : (MulAut.congr e).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj g').toMonoidHom.comp (MulAut.congr e).toMonoidHom := by
        refine MonoidHom.ext fun x => ?_
        change MulAut.congr e (MulAut.conj g x) = MulAut.conj g' (MulAut.congr e x)
        rw [k330c_congr_conj_apply e g x, hge]
      rw [hcomp, ← Subgroup.map_map, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hφe]
    exact Subgroup.map_injective (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective
      (by rw [hmapconj, hWg'])
  · intro α hα
    have hα' : ∀ x ∈ fixedBy (Subgroup.zpowers φ'), MulAut.congr e α x = x := by
      intro x hx
      rw [← hfixmap, Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [← hyx, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hα y hy]
    have hmem := hrig' (MulAut.congr e α) hα'
    rw [hzpow, Subgroup.mem_map] at hmem
    obtain ⟨β, hβ, hβeq⟩ := hmem
    exact ((MulAut.congr e).injective (by simpa only [MulEquiv.coe_toMonoidHom] using hβeq)) ▸ hβ
  · intro n hn
    have hne' : (fixedBy (Subgroup.zpowers φ')).map (MulAut.conj (e n)).toMonoidHom ≠
        fixedBy (Subgroup.zpowers φ') := by
      intro h
      apply hn
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [k330c_fixedBy_conj_map e φ n, hφe, h, ← hfixmap]
    have hsup := hpair' (e n) hne'
    have hfixsym : (fixedBy (Subgroup.zpowers φ')).map e.symm.toMonoidHom =
        fixedBy (Subgroup.zpowers φ) := by
      rw [fixedBy_map_congr e.symm (Subgroup.zpowers φ'), MonoidHom.map_zpowers,
        MulEquiv.coe_toMonoidHom]
    have hconjsym : ((fixedBy (Subgroup.zpowers φ')).map (MulAut.conj (e n)).toMonoidHom).map
        e.symm.toMonoidHom = (fixedBy (Subgroup.zpowers φ)).map (MulAut.conj n).toMonoidHom := by
      rw [k330c_fixedBy_conj_map e.symm φ' (e n), e.symm_apply_apply]
    have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) hsup
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
      hfixsym, hconjsym] at hmap
    exact hmap
  · have hcard : Nat.card (fixedBy (Subgroup.zpowers φ)) =
        Nat.card (fixedBy (Subgroup.zpowers φ')) := by
      rw [← Subgroup.card_map_of_injective (K := fixedBy (Subgroup.zpowers φ))
          (f := e.toMonoidHom) e.injective,
        fixedBy_map_congr e (Subgroup.zpowers φ), MonoidHom.map_zpowers,
        MulEquiv.coe_toMonoidHom, hφe]
    rw [hcard]
    exact hbound'

private theorem k330c_hasFieldRP_projectiveSp {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    HasFieldRP (StatedProj (StatedSp 2 K)) (p ^ f) spBound := by
  intro W hW h7T
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hcyc : IsCyclic ↥W := isCyclic_of_prime_card hW
  obtain ⟨a, ha⟩ := hcyc.exists_generator
  have hordg : orderOf a = 7 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, hW]
  set A : MulAut (StatedProj (StatedSp 2 K)) := (a : MulAut (StatedProj (StatedSp 2 K))) with hA
  have hAord : orderOf A = 7 := by rw [hA, Subgroup.orderOf_coe, hordg]
  have hA7 : A ^ 7 = 1 := by rw [← hAord]; exact pow_orderOf_eq_one A
  have hWz : W = Subgroup.zpowers A := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le, hA]; exact a.2
    · rw [hW, Nat.card_zpowers, hAord]
  have hp7 : p ≠ 7 := by
    intro hp7
    apply h7T
    have hq7 : 7 ∣ Nat.card K := by
      rw [hK, hp7]
      exact dvd_pow_self 7 (by omega : f ≠ 0)
    have hSp7 : 7 ∣ Nat.card (StatedSp 2 K) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two]
      exact dvd_mul_of_dvd_left
        (hq7.trans (dvd_pow_self (Nat.card K) (by norm_num : 4 ≠ 0))) _
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (spScalars 2 K)
    rw [hcard] at hSp7
    have hZ7 : ¬ 7 ∣ Nat.card (spScalars 2 K) := by
      intro hd
      have hdvd : 7 ∣ Nat.card K - 1 :=
        hd.trans (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_scalars_dvd (r := 2)
          (by norm_num))
      have h1 : 1 ≤ Nat.card K := Nat.card_pos
      have hsub : 7 ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hq7 hdvd
      rw [Nat.sub_sub_self h1] at hsub
      exact Nat.prime_seven.one_lt.ne' (Nat.dvd_one.mp hsub)
    rcases Nat.prime_seven.dvd_mul.mp hSp7 with h | h
    · exact h
    · exact absurd h hZ7
  have h7ne : (7 : ℕ) ≠ p := fun h => hp7 h.symm
  have O : SpOuter p f 2 K := spOuter hp hf (by norm_num) hK
  have hAodd : Odd (orderOf A) := by rw [hAord]; exact ⟨3, by norm_num⟩
  have hAE : A ∈ spSemilinearAutGroup 2 K :=
    mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd hAodd
  have hAD : A ∉ spLinearAutGroup 2 K := by
    intro hD
    have hinner := mem_of_pow_eq_one_of_relIndex_dvd_two
      (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) Nat.prime_seven (by norm_num) hD hA7
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hinner
    have hdvd : orderOf A ∣ Nat.card (StatedProj (StatedSp 2 K)) := by
      rw [← hg]
      exact (orderOf_map_dvd (MulAut.conj :
        StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))) g).trans
        (orderOf_dvd_natCard g)
    rw [hAord] at hdvd
    exact h7T hdvd
  obtain ⟨h7f, σ, hσord, h, -, hAeq⟩ := O.descent 7 Nat.prime_seven A hAE hAD hAord
  obtain ⟨-, hkcard, -, -, hinj, hfixpts, -, -, -, hfixing, hfield, -, -, -⟩ :=
    CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      hp Nat.prime_seven (by norm_num) h7ne hf (by norm_num : 2 ≤ 2) hK σ hσord
  have hφord : orderOf (fieldAut 2 K σ) = 7 := by
    rw [orderOf_injective (fieldAut 2 K) O.fieldAut_injective σ, hσord]
  have hfixeq : fixedBy (Subgroup.zpowers (fieldAut 2 K σ)) =
      subfieldFixedGroup K 2 σ := by
    ext x
    rw [k330c_mem_fixedBy_zpowers_iff]
    exact (hfixpts x).symm
  have hfixsub : fixedBy (Subgroup.zpowers (fieldAut 2 K σ)) =
      fixedSubgroup (fieldAut 2 K σ) := by
    ext x
    rw [k330c_mem_fixedBy_zpowers_iff, mem_fixedSubgroup]
  have hφconj : h * fieldAut 2 K σ * h⁻¹ = MulAut.conj h (fieldAut 2 K σ) := by
    rw [MulAut.conj_apply]
  refine ⟨h, fieldAut 2 K σ, hφord, ?_, ?_, ?_, Nat.card (descentField σ), ?_, ?_⟩
  · rw [hWz, hAeq, hφconj, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom]
  · intro α hα
    rw [hfixeq] at hα
    have hmem : α ∈ fixingSubgroup (MulAut (StatedProj (StatedSp 2 K)))
        (subfieldFixedGroup K 2 σ : Set (StatedProj (StatedSp 2 K))) :=
      (mem_fixingSubgroup_iff (MulAut (StatedProj (StatedSp 2 K)))).mpr fun x hx => by
        rw [MulAut.smul_def]
        exact hα x hx
    rw [hfixing, hfield] at hmem
    exact hmem
  · intro x hx
    obtain ⟨u, rfl⟩ := proj_surjective x
    set B : gsp 2 K := ⟨u, statedSp_le_gsp u.2⟩ with hB
    have hconj : MulAut.conj (proj 2 K u) = conjAut 2 K B := (conjAut_statedSp u).symm
    have hσp : σ ^ 7 = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
    have hne' : (spSub 2 (descentField σ)).map (conjSp 2 K B).toMonoidHom ≠
        spSub 2 (descentField σ) := by
      intro h
      apply hx
      rw [hfixsub, fixedSubgroup_fieldAut_eq_range_sp (p := 7) (by norm_num) hσp,
        range_subfieldProj_eq_map, hconj, map_conjAut_map_proj, h]
    have hcardK : Nat.card K = Nat.card (descentField σ) ^ 7 := by
      rw [hK, hkcard, ← pow_mul, Nat.div_mul_cancel h7f]
    have hgen := (CFSG.LieType.SeitzGeneration.subfieldPairSpOdd
      CFSG.LieType.SeitzGeneration.subfieldPairSpF2_holds) K (descentField σ) 7
      Nat.prime_seven (by norm_num) hcardK 2 (by norm_num) B hne'
    rw [← Subgroup.sup_eq_closure] at hgen
    have h4 := congrArg (Subgroup.map (proj 2 K)) hgen
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ proj_surjective] at h4
    rw [hfixsub, fixedSubgroup_fieldAut_eq_range_sp (p := 7) (by norm_num) hσp,
      range_subfieldProj_eq_map, hconj, map_conjAut_map_proj]
    exact h4
  · rw [hkcard, ← pow_mul, Nat.div_mul_cancel h7f]
  ·
    have hfixinj : fixedBy (Subgroup.zpowers (fieldAut 2 K σ)) =
        (subfieldSpProj 2 (descentField σ)).range := by
      ext x
      rw [k330c_mem_fixedBy_zpowers_iff]
      exact (hfixpts x).symm
    rw [hfixinj]
    have h1 : Nat.card ((subfieldSpProj 2 (descentField σ)).range) =
        Nat.card (StatedProj (StatedSp 2 (descentField σ))) := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj]
      simp
    rw [h1, spBound]
    calc Nat.card (StatedProj (StatedSp 2 (descentField σ)))
        ≤ Nat.card (StatedSp 2 (descentField σ)) :=
          Nat.card_le_card_of_surjective (proj 2 (descentField σ)) proj_surjective
      _ = Nat.card (descentField σ) ^ 4 *
            ((Nat.card (descentField σ) ^ 2 - 1) * (Nat.card (descentField σ) ^ 4 - 1)) :=
          CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two (descentField σ)
      _ ≤ Nat.card (descentField σ) ^ 10 := by
          have h2 : Nat.card (descentField σ) ^ 2 - 1 ≤ Nat.card (descentField σ) ^ 2 :=
            Nat.sub_le _ _
          have h4 : Nat.card (descentField σ) ^ 4 - 1 ≤ Nat.card (descentField σ) ^ 4 :=
            Nat.sub_le _ _
          calc Nat.card (descentField σ) ^ 4 *
                ((Nat.card (descentField σ) ^ 2 - 1) * (Nat.card (descentField σ) ^ 4 - 1))
              ≤ Nat.card (descentField σ) ^ 4 *
                  (Nat.card (descentField σ) ^ 2 * Nat.card (descentField σ) ^ 4) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h4)
            _ = Nat.card (descentField σ) ^ 10 := by ring

theorem hasFieldRP_PSp4 {J : Type} [Group J] [Finite J] {p f : ℕ}
    (e : LieModel J .PSp 2 p f) : HasFieldRP J (p ^ f) spBound := by
  have hC : StatedClassicalModel J .PSp 2 p f :=
    LieModel.statedClassicalModel e (by decide)
  obtain ⟨hadm, K, _, _, hKcard, ⟨eK⟩⟩ := hC
  exact k330c_hasFieldRP_of_mulEquiv eK (k330c_hasFieldRP_projectiveSp hadm.1 hadm.2.1 hKcard)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
