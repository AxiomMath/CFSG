module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepToral
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepWit
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepBlock
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUMono
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallALinearBlock
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSU
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.CharacterTheory.Burnside
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace WitSU

variable {K : Type} [Field K]

theorem isSolvable_unitarySU_two_one (h : UnitaryFieldData 2 1 K) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ 3) : Group.IsSolvable ↥(unitarySU 2 1 K k) := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hc := CFSG.RankThree.PartOne.KFU.card_statedSU_eq h hk1
  have hc' : ∃ a b : ℕ, Nat.card ↥(unitarySU 2 1 K k) = 2 ^ a * 3 ^ b := by
    have e : Nat.card ↥(unitarySU 2 1 K k) = Nat.card (StatedSU k (2 ^ 1) K) := rfl
    interval_cases k
    · refine ⟨0, 0, ?_⟩
      have h2 : Finset.Icc 2 1 = (∅ : Finset ℕ) := by decide
      rw [h2, Finset.prod_empty] at hc
      have hc1 : (Nat.card (StatedSU 1 (2 ^ 1) K) : ℤ) = 1 := by rw [hc]; norm_num
      have hc2 : Nat.card (StatedSU 1 (2 ^ 1) K) = 1 := by exact_mod_cast hc1
      rw [e, hc2]
      norm_num
    · refine ⟨1, 1, ?_⟩
      have h2 : Finset.Icc 2 2 = ({2} : Finset ℕ) := by decide
      rw [h2, Finset.prod_singleton] at hc
      have hc1 : (Nat.card (StatedSU 2 (2 ^ 1) K) : ℤ) = 6 := by rw [hc]; norm_num
      have hc2 : Nat.card (StatedSU 2 (2 ^ 1) K) = 6 := by exact_mod_cast hc1
      rw [e, hc2]
      norm_num
    · refine ⟨3, 3, ?_⟩
      have h2 : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
      rw [h2, Finset.prod_pair (by norm_num)] at hc
      have hc1 : (Nat.card (StatedSU 3 (2 ^ 1) K) : ℤ) = 216 := by rw [hc]; norm_num
      have hc2 : Nat.card (StatedSU 3 (2 ^ 1) K) = 216 := by exact_mod_cast hc1
      rw [e, hc2]
      norm_num
  obtain ⟨a, b, hab⟩ := hc'
  have : Fintype ↥(unitarySU 2 1 K k) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hab)

theorem isSolvable_map_blockSU_two_one (h : UnitaryFieldData 2 1 K) {G : Type} [Group G] {n : ℕ}
    (φ : ↥(unitarySU 2 1 K n) →* G) {S : Finset (Fin n)} (hS1 : 1 ≤ S.card) (hS : S.card ≤ 3) :
    Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1) S).map φ) := by
  have : Group.IsSolvable ↥(unitarySU 2 1 K S.card) := isSolvable_unitarySU_two_one h hS1 hS
  have : Group.IsSolvable ↥(TableBUE.blockSU (K := K) (n := 1) S) :=
    Group.isSolvable_of_surjective (f := (TableBUE.blockSUEquiv S h).toMonoidHom)
      (TableBUE.blockSUEquiv S h).surjective
  have hS' : Group.IsSolvable (φ.comp (TableBUE.blockSU (K := K) (n := 1) S).subtype).range :=
    Group.isSolvable_of_surjective
      (φ.comp (TableBUE.blockSU (K := K) (n := 1) S).subtype).rangeRestrict_surjective
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at hS'

@[expose] noncomputable def rootDiagU {n : ℕ} (j₁ j₂ : Fin n) (ζ : Kˣ) : Fin n → Kˣ :=
  Function.update (Function.update (fun _ => (1 : Kˣ)) j₁ ζ) j₂ ζ⁻¹

theorem rootDiagU_apply_left {n : ℕ} {j₁ j₂ : Fin n} (h : j₁ ≠ j₂) (ζ : Kˣ) :
    rootDiagU j₁ j₂ ζ j₁ = ζ := by
  rw [rootDiagU, Function.update_of_ne h, Function.update_self]

theorem rootDiagU_apply_right {n : ℕ} (j₁ j₂ : Fin n) (ζ : Kˣ) : rootDiagU j₁ j₂ ζ j₂ = ζ⁻¹ := by
  rw [rootDiagU, Function.update_self]

theorem rootDiagU_apply_of_ne {n : ℕ} {j₁ j₂ k : Fin n} (h₁ : k ≠ j₁) (h₂ : k ≠ j₂) (ζ : Kˣ) :
    rootDiagU j₁ j₂ ζ k = 1 := by
  rw [rootDiagU, Function.update_of_ne h₂, Function.update_of_ne h₁]

theorem prod_rootDiagU {n : ℕ} {j₁ j₂ : Fin n} (h : j₁ ≠ j₂) (ζ : Kˣ) :
    ∏ i, rootDiagU j₁ j₂ ζ i = 1 := by
  rw [rootDiagU, SLRep.prod_update_update_const h, one_pow, mul_one, inv_mul_cancel]

theorem rootDiagU_pow {n : ℕ} {j₁ j₂ : Fin n} {N : ℕ} {ζ : Kˣ} (hζ : ζ ^ N = 1) (k : Fin n) :
    rootDiagU j₁ j₂ ζ k ^ N = 1 := by
  by_cases h₂ : k = j₂
  · subst h₂
    rw [rootDiagU_apply_right, inv_pow, hζ, inv_one]
  by_cases h₁ : k = j₁
  · subst h₁
    rw [rootDiagU_apply_left h₂, hζ]
  · rw [rootDiagU_apply_of_ne h₁ h₂, one_pow]

theorem mem_blockSU_of_diag {f n : ℕ} {d : ↥(unitarySU 2 f K n)} {δ : Fin n → Kˣ}
    (hd : (d : GL (Fin n) K) = diagHom n δ) {I : Finset (Fin n)} (hI : ∀ k ∉ I, δ k = 1) :
    d ∈ TableBUE.blockSU (K := K) (n := f) I := by
  intro a c hac
  rw [hd, coe_diagHom]
  by_cases hac' : a = c
  · subst hac'
    rw [diagonal_apply_eq, one_apply_eq, hI a (by tauto), Units.val_one]
  · rw [diagonal_apply_ne _ hac', one_apply_ne hac']

end WitSU

section Inputs

open CFSG.LieType.Universal.Unitary (SU antidiag conjTr) in
open CFSG.LieType.BorelTits (unitaryInvolution) in
theorem ggSixSeventeenWitnessOn_PSUSplit : GGSixSeventeenWitnessOn GGPSUSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair
  obtain ⟨rfl, hpq⟩ := hP
  have hadm := hctx.2.2.2.1.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by have := hadm.2.1; omega⟩
  obtain ⟨P, hP, hframe⟩ := ggSUBstarFrameInput_holds G p B Bs x L D J n f ψ hctx s1 hpq
  set hK := card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f) with hKdef
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hdata : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hnq : (n, 2 ^ (f + 1)) ≠ (3, 2) := hadm.2.2.2
  set φ := SURep.ggFrameU hK ψ P hP with hφ
  have hrangeφ : φ.range = ggG0 p B x L D J := (SURep.range_ggFrameU hK ψ P hP).trans hrange
  have hcentφ : Subgroup.centralizer (φ.range : Set G) = ⊥ := by rw [hrangeφ]; exact s1.1
  have hFk : SURep.GGFrameKer φ := SURep.ggFrameKer_ggFrameU hK ψ P hP hn3 hnq hker
  have hkerφ := SURep.ker_ggFrameU_le hK ψ P hP hker
  have hpF : p ∣ Nat.card (GaloisField 2 (2 * (f + 1))) - 1 := by
    rw [hK, show (1 : ℕ) = 1 ^ 2 from rfl, Nat.sq_sub_sq]
    exact Dvd.dvd.mul_right hpq _
  have hBs : GGBstar p B Bs := hctx.2.1
  have hBsge : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
    exact (Nat.pow_le_pow_right hp.pos h4r).trans (hBcard ▸ hBle)
  have hn5 : 5 ≤ n := by
    have hBs' := SURep.card_le_of_frameU hp hpF hdata hn3 hFk hcentφ (X := Bs)
      (fun c hc => hBs.2.1.2 c hc) hframe (S := {⟨0, by omega⟩}) (i₀ := ⟨0, by omega⟩)
      (fun c _ τ _ i hi => congrArg τ (Finset.mem_singleton.mp hi))
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton] at hBs'
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans hBs')
    omega
  obtain ⟨τb, hτb⟩ := hframe b hpair.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hδb : ∀ e ∈ ({b} : Set G),
      (e, diagHom (m + 1) ((fun _ : G => τb) e)) ∈ SUTorus.suPairs φ := by
    intro e he
    rw [Set.mem_singleton_iff.mp he]
    exact SUModel.mem_suPairs_of_frameActs hdata hτb
  have hL : IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [hrangeφ]
    exact hpair.2.2.1
  obtain ⟨i, hLI⟩ := SUTorus.exists_le_map_blockSU hdata hp hpq hkerφ hδb hL
  set I := LinTorus.diagClass ({b} : Set G) (fun _ : G => τb) i with hIdef
  have hI2 : 2 ≤ I.card := by
    by_contra hlt
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
      (show I.card = 1 by
        have h1 : 1 ≤ I.card :=
          Finset.card_pos.mpr ⟨i, LinTorus.self_mem_diagClass _ _ i⟩
        omega)
    rw [ha, SUTorus.blockSU_singleton hdata, Subgroup.map_bot] at hLI
    apply commutator_ne_bot_of_isQuasisimple hL.2.2
    rw [le_bot_iff.mp hLI]
    exact Subgroup.commutator_bot_left _
  have hI4 : f = 0 → 4 ≤ I.card := by
    rintro rfl
    by_contra hlt
    have := WitSU.isSolvable_map_blockSU_two_one hdata φ (S := I) (by omega) (by omega)
    exact LinSemisimple.false_of_isQuasisimple_of_le_isSolvable hL.2.2 hLI
  have hIq : (I.card, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have h1 : I.card = 3 := congrArg Prod.fst h'
    have h2 : 2 ^ (f + 1) = 2 := congrArg Prod.snd h'
    have hf0 : f = 0 := by
      by_contra hf0
      have : 2 ^ 2 ≤ 2 ^ (f + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := hI4 hf0
    omega
  have hI3 : 3 ≤ I.card := by
    by_contra hlt
    have hI2' : I.card = 2 := by omega
    have hf1 : 1 ≤ f := by
      by_contra hf0
      have := hI4 (by omega)
      omega
    have hKq := SURepair.isQuasisimple_map_blockSU_of_two_le hdata (by omega) hkerφ hI2
    have hsub := SUTorus.isSubnormal_map_blockSU hkerφ hδb i
    have hLeq := LinTypeAk.eq_of_isComponentOf_of_le hL hLI (isSubnormal_le_of_assembly hsub) hKq
    apply hpair.2.2.2
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hpq, ?_⟩)))
    rw [hLeq]
    exact LinTypeAk.lieModel_map_blockSU_of_card_two hdata (by omega) hkerφ hI2'
  have hKq : CFSG.Assembly.IsQuasisimple
      ↥((TableBUE.blockSU (K := GaloisField 2 (2 * (f + 1))) (n := f + 1) I).map φ) :=
    SURepair.isQuasisimple_map_of_isQuasisimple hkerφ
      (TableBUE.isQuasisimple_blockSU I hdata hK hI3 hIq)
  have hsub := SUTorus.isSubnormal_map_blockSU hkerφ hδb i
  have hLeq := LinTypeAk.eq_of_isComponentOf_of_le hL hLI (isSubnormal_le_of_assembly hsub) hKq
  have hI5 : f = 0 → 5 ≤ I.card := by
    rintro rfl
    by_contra hlt
    have hI4' : I.card = 4 := by have := hI4 rfl; omega
    have hp3 : p = 3 := by
      have h3 : p ∣ 3 := by simpa using hpq
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · exact absurd h hp.one_lt.ne'
      · exact h
    apply hpair.2.2.2
    refine Or.inl ⟨hp3, Or.inl ?_⟩
    rw [hLeq]
    have hM := SUTorus.lieModel_map_blockSU hdata hkerφ hI3 hIq
    rwa [hI4'] at hM
  obtain ⟨k₁, hk₁⟩ : ∃ k, k ∉ I := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hpair.2.1
    refine SURep.eq_of_act_eqU hcentφ fun s => ?_
    have hr : ∀ a c, τb a * (τb c)⁻¹ =
        (1 : Fin (m + 1) → (GaloisField 2 (2 * (f + 1)))ˣ) a *
          ((1 : Fin (m + 1) → (GaloisField 2 (2 * (f + 1)))ˣ) c)⁻¹ := by
      intro a c
      have ha : τb a = τb i := LinTorus.mem_diagClass.mp (hall a) b (Set.mem_singleton b)
      have hc : τb c = τb i := LinTorus.mem_diagClass.mp (hall c) b (Set.mem_singleton b)
      rw [ha, hc, mul_inv_cancel]
      simp
    have hconj := SURep.conjU_eq_of_ratio hdata hτb.1 (fun _ => by simp) hr s
    rw [hτb.apply hdata s, hconj, SURep.conjU_one, one_mul, inv_one, mul_one]
  have hIlt : I.card ≤ m := by
    have h := Finset.card_le_card (s := I) (t := Finset.univ.erase k₁)
      (fun j hj => Finset.mem_erase.mpr ⟨fun h => hk₁ (h ▸ hj), Finset.mem_univ _⟩)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := Finset.one_lt_card.mp (show 1 < I.card by omega)
  obtain ⟨ζ, hζp, hζn⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hdata hp hpq
  have hζpow : ζ ^ p = 1 := hζp ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζp
    exact hp.one_lt.ne hζp
  have hζi1 : ζ⁻¹ ≠ 1 := fun h => hζ1 (inv_eq_one.mp h)
  set δ := WitSU.rootDiagU j₁ j₂ ζ with hδdef
  have hprod : ∏ k, δ k = 1 := WitSU.prod_rootDiagU hj ζ
  have hnorm : ∀ k, (δ k : GaloisField 2 (2 * (f + 1))) ^ (2 ^ (f + 1) + 1) = 1 := fun k => by
    rw [← Units.val_pow_eq_pow_val, WitSU.rootDiagU_pow hζn k, Units.val_one]
  set d : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) (m + 1)) :=
    ⟨diagHom (m + 1) δ, SURep.diagHom_mem_unitarySU' hdata hnorm hprod⟩ with hd
  have hdδ : (d : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1)))) = diagHom (m + 1) δ := rfl
  have hdp : d ^ p = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hdδ, ← map_pow]
    have : δ ^ p = 1 := funext fun k => WitSU.rootDiagU_pow hζpow k
    rw [this, map_one, Subgroup.coe_one]
  have heBs : φ d ∈ Bs := SURep.mem_of_frame_inner hBs hdata hframe hdδ hdp
  have hb := SURep.frameActs_map φ hdδ hnorm
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin (m + 1), k₀ ∉ ({j₁, j₂} : Finset (Fin (m + 1))) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have h := Finset.card_le_card (fun k _ => hall k : (Finset.univ : Finset (Fin (m + 1))) ⊆ _)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h2 := Finset.card_le_two (a := j₁) (b := j₂)
    omega
  have hk₀1 : k₀ ≠ j₁ := fun h => hk₀ (by simp [h])
  have hk₀2 : k₀ ≠ j₂ := fun h => hk₀ (by simp [h])
  have hδk₀ : δ k₀ = 1 := WitSU.rootDiagU_apply_of_ne hk₀1 hk₀2 ζ
  have hδj₁ : δ j₁ = ζ := WitSU.rootDiagU_apply_left hj ζ
  have hδj₂ : δ j₂ = ζ⁻¹ := WitSU.rootDiagU_apply_right j₁ j₂ ζ
  have he1 : φ d ≠ 1 :=
    SURep.ne_one_of_frameActs hFk hdata (by omega) hb (i := j₁) (j := k₀)
      (by rw [hδj₁, hδk₀]; exact hζ1)
  have heL : φ d ∈ L₁ := by
    rw [hLeq]
    refine ⟨d, WitSU.mem_blockSU_of_diag hdδ fun k hk => ?_, rfl⟩
    exact WitSU.rootDiagU_apply_of_ne (fun h : k = j₁ => hk (h ▸ hj₁))
      (fun h : k = j₂ => hk (h ▸ hj₂)) ζ
  set S : Finset (Fin (m + 1)) := ({j₁, j₂} : Finset (Fin (m + 1)))ᶜ with hSdef
  have hSc2 : Sᶜ.card = 2 := by rw [hSdef, compl_compl, Finset.card_pair hj]
  have hScard : S.card = m - 1 := by
    rw [hSdef, Finset.card_compl, Fintype.card_fin, Finset.card_pair hj]
    omega
  have hS3 : 3 ≤ S.card := by omega
  have hSq : (S.card, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have h1 : S.card = 3 := congrArg Prod.fst h'
    have h2 : 2 ^ (f + 1) = 2 := congrArg Prod.snd h'
    have hf0 : f = 0 := by
      by_contra hf0
      have : 2 ^ 2 ≤ 2 ^ (f + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := hI5 hf0
    omega
  have hS : ∀ k ∈ S, δ k = 1 := fun k hk => by
    rw [hSdef, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact WitSU.rootDiagU_apply_of_ne hk.1 hk.2 ζ
  have hSc : ∀ k ∉ S, δ k ≠ 1 := fun k hk => by
    rw [hSdef, Finset.mem_compl, not_not, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · rw [hδj₁]; exact hζ1
    · rw [hδj₂]; exact hζi1
  have hj₁S : j₁ ∉ S := by simp [hSdef]
  have hk₀S : k₀ ∈ S := by rw [hSdef, Finset.mem_compl]; exact hk₀
  have hcomp := SURep.isComponentOf_map_blockSU hK hdata hFk hb hS hSc (by omega) hS3 hSq hj₁S
  have hcard : Nat.card (Bs ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := GaloisField 2 (2 * (f + 1))) (n := f + 1) S).map φ :
        Subgroup G) : Set G) : Subgroup G) ≤ p ^ 2 := by
    have h := SURep.card_le_of_frameU hp hpF hdata (by omega) hFk hcentφ
      (X := Bs ⊓ Subgroup.centralizer
        (((TableBUE.blockSU (K := GaloisField 2 (2 * (f + 1))) (n := f + 1) S).map φ :
          Subgroup G) : Set G))
      (fun c hc => hBs.2.1.2 c hc.1) (fun c hc => hframe c hc.1) (S := S) (i₀ := k₀)
      (fun c hc τ' hτ' k hk =>
        SURep.const_of_mem_centralizer_blockSU hFk hdata (by omega) hc.2 hτ' hk₀S k hk)
    rwa [hSc2] at h
  rw [hrangeφ] at hcomp
  exact Or.inr ⟨φ d, heL, Or.inl ⟨heBs, he1, Or.inr ⟨_, hcomp, hcard⟩⟩⟩

end Inputs

end CFSG.StandardType
