module

public import Certificates.Certificate8058
public import Certificates.Certificate8059
public import CFSG.RankThree.PartTwo.KFacts.K426Cover
public import CFSG.RankThree.PartTwo.KFacts.K426A6
public import CFSG.Sporadic.Schreier.PairJ3Order

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.CosetTable
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open scoped commutatorElement


theorem j3t_lines_check :
    linesOK3 3 243 13 6156 j3tCBGens j3tKeys j3tCBCert j3tLines = true ∧
      allLt 2 (fun c => validA 6156 j3tReps[c]! &&
        eqA 6156 (powArr 6156 j3tReps[c]! 3) (idA 6156)) = true ∧
      transOK2 13 6156 j3tTrans j3tReps j3tLines j3tRec PairJ3.levels PairJ3.baseArr = true ∧
      allLt 13 (fun j => decide (j3tRec.getD j 0 < 2)) = true :=
  Certificates.certificate8058.1

theorem j3t_cases_check :
    centOKP 3 6156 j3StrongArrs PairJ3.baseArr j3tReps[0]! j3tRelsA j3tCAGens j3tKeys
        j3tCACert 1080 = true ∧
      centOKP 3 6156 j3StrongArrs PairJ3.baseArr j3tReps[1]! j3tRelsB j3tCBGens j3tKeys
        j3tCBCert 243 = true :=
  Certificates.certificate8058.2.1

theorem j3t_derived_check :
    derivedLeOK 6156 j3tCAGens j3tDGens j3tKeys j3tDCert 360 = true ∧
      wordsOneOK 6156 j3tDGens j3tA6Rels = true ∧
      allLt 2 (fun l => siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tDGens[l]!) = true ∧
      siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tG = true ∧
      detOK 6156 j3tDGens j3tG j3tWu j3tWv 1 = true :=
  Certificates.certificate8058.2.2

theorem j3t_lift_check : cyclicCheckC j3tLiftRels [2] 4 2000 90 = true :=
  Certificates.certificate8059

theorem j3tKeys_lt : ∀ q ∈ j3tKeys, q < 6156 := by decide

theorem mem_j3P_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 6156)} (hG : Rep 6156 g G)
    (h : siftA 6156 PairJ3.levels PairJ3.baseArr 0 g = true) : G ∈ j3P := by
  rw [j3P_eq_original]
  exact (siftA_iff_mem_originalSubgroup j3ChainArrays (by norm_num) PairJ3.chain_check.1
    hG).1 h

theorem factorization_card_j3P_three : (Nat.card j3P).factorization 3 = 5 := by
  rw [card_j3P, show (50232960 : ℕ) = 3 ^ 5 * 206720 by norm_num]
  exact factorization_pow_mulG Nat.prime_three (by norm_num)

@[expose] noncomputable def j3tXA : Equiv.Perm (Fin 6156) := permOfArr 6156 j3tReps[0]!

@[expose] noncomputable def j3tXB : Equiv.Perm (Fin 6156) := permOfArr 6156 j3tReps[1]!

theorem j3tReps_spec {c : ℕ} (hc : c < 2) :
    validA 6156 j3tReps[c]! = true ∧ permOfArr 6156 j3tReps[c]! ^ 3 = 1 := by
  have h := allLt_spec j3t_lines_check.2.1 hc
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, (eqA_iff (rep_powArr (rep_of_validA h.1) 3) rep_idA).1 h.2⟩

theorem j3t_caseA :
    closure (permsA 6156 j3tCAGens) = centralizer {j3tXA} ⊓ j3P ∧
      Nat.card (closure (permsA 6156 j3tCAGens)) = 1080 := by
  rw [j3P_eq_original]
  exact centralizer_eq_of_ptailOK' j3ChainArrays (by norm_num) PairJ3.chain_check.1
    (rep_of_validA (j3tReps_spec (by norm_num)).1) j3tKeys_lt j3t_cases_check.1

theorem j3t_caseB :
    closure (permsA 6156 j3tCBGens) = centralizer {j3tXB} ⊓ j3P ∧
      Nat.card (closure (permsA 6156 j3tCBGens)) = 243 := by
  rw [j3P_eq_original]
  exact centralizer_eq_of_ptailOK' j3ChainArrays (by norm_num) PairJ3.chain_check.1
    (rep_of_validA (j3tReps_spec (by norm_num)).1) j3tKeys_lt j3t_cases_check.2

set_option maxRecDepth 20000 in
theorem j3t_fusion {x : Equiv.Perm (Fin 6156)} (hx : x ∈ j3P) (hxo : orderOf x = 3) :
    ∃ k ∈ j3P, ∃ c, (c = j3tXA ∨ c = j3tXB) ∧ ∃ e, (e = 1 ∨ e = 2) ∧ x = k * c ^ e * k⁻¹ := by
  have hQ : closure (permsA 6156 j3tCBGens) ≤ j3P := by
    rw [j3t_caseB.1]
    exact inf_le_right
  have hQcard :
      Nat.card (closure (permsA 6156 j3tCBGens)) = 3 ^ (Nat.card j3P).factorization 3 := by
    rw [factorization_card_j3P_three, linesOK3_card j3tKeys_lt j3t_lines_check.1]
    norm_num
  have hrec : ∀ j < 13, j3tRec.getD j 0 < 2 := fun j hj =>
    of_decide_eq_true (allLt_spec j3t_lines_check.2.2.2 hj)
  obtain ⟨k, hk, j, hj, e, he, rfl⟩ := exists_conj_rep hQ hQcard
    (fun j => permOfArr 6156 j3tLines[j]!) (fun c => permOfArr 6156 j3tReps[c]!)
    (fun j => permOfArr 6156 j3tTrans[j]!) (fun j => j3tRec.getD j 0) (r := 13)
    (fun g hg hg3 => linesOK3_spec j3tKeys_lt j3t_lines_check.1 hg hg3)
    (fun j hj => transOK2_spec mem_j3P_of_sift
      (fun j hj => (j3tReps_spec (hrec j hj)).1)
      (fun j hj => (linesOK3_line j3t_lines_check.1 hj).1) j3t_lines_check.2.2.1 hj) hx hxo
  refine ⟨k, hk, _, ?_, e, he, rfl⟩
  rcases (by have := hrec j hj; omega : j3tRec.getD j 0 = 0 ∨ j3tRec.getD j 0 = 1) with h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

@[expose] noncomputable def j3tD (i : Fin 2) : Equiv.Perm (Fin 6156) :=
  permOfArr 6156 j3tDGens[i.val]!

theorem range_j3tD : Set.range j3tD = permsA 6156 j3tDGens := by
  ext σ
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, by simpa [j3tDGens] using i.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by simpa [j3tDGens] using hk
    exact ⟨⟨k, hk2⟩, rfl⟩

theorem j3tDGens_valid : ∀ k < j3tDGens.size, validA 6156 j3tDGens[k]! = true := by
  have h := j3t_derived_check.2.1
  simp only [wordsOneOK, Bool.and_eq_true] at h
  exact fun k hk => allLt_spec h.1 hk

theorem rep_evalWA_j3tD (w : List (Fin 2 × Bool)) :
    Rep 6156 (evalWA 6156 j3tDGens w) (evalW j3tD w) :=
  rep_evalWA j3tDGens_valid (by simp [j3tDGens]) w

theorem j3tD_rels : ∀ w ∈ j3tA6Rels, evalW j3tD w = 1 := by
  have h := j3t_derived_check.2.1
  simp only [wordsOneOK, Bool.and_eq_true, List.all_eq_true] at h
  intro w hw
  exact (eqA_iff (rep_evalWA_j3tD w) rep_idA).1 (h.2 w hw)

@[expose] noncomputable def j3tGPerm : Equiv.Perm (Fin 6156) := permOfArr 6156 j3tG

theorem j3t_det :
    j3tGPerm * evalW j3tD j3tWu * j3tGPerm⁻¹ = evalW j3tD j3tWv ∧
      j3tGPerm * evalW j3tD j3tWv * j3tGPerm⁻¹ = evalW j3tD j3tWu * evalW j3tD j3tWv ^ 1 ∧
      evalW j3tD j3tWu * evalW j3tD j3tWv = evalW j3tD j3tWv * evalW j3tD j3tWu := by
  have h := j3t_derived_check.2.2.2.2
  simp only [detOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hv, h1⟩, h2⟩, h3⟩ := h
  have hu := rep_evalWA_j3tD j3tWu
  have hw := rep_evalWA_j3tD j3tWv
  refine ⟨eq_of_eqA (rep_conjA hv hu) hw h1, eq_of_eqA (rep_conjA hv hw)
    (rep_compA hu (rep_powArr hw 1)) h2, eq_of_eqA (rep_compA hu hw) (rep_compA hw hu) h3⟩

theorem j3tD_mem (i : Fin 2) : j3tD i ∈ j3P :=
  mem_j3P_of_sift (rep_of_validA (j3tDGens_valid i.val (by simpa [j3tDGens] using i.2)))
    (allLt_spec j3t_derived_check.2.2.1 i.2)

theorem j3tGPerm_mem : j3tGPerm ∈ j3P := by
  have h := j3t_derived_check.2.2.2.2
  simp only [detOK, Bool.and_eq_true] at h
  exact mem_j3P_of_sift (rep_of_validA h.1.1.1) j3t_derived_check.2.2.2.1

theorem j3t_derived :
    ⁅(centralizer {j3tXA} ⊓ j3P : Subgroup (Equiv.Perm (Fin 6156))), centralizer {j3tXA} ⊓ j3P⁆ ≤
      closure (Set.range j3tD) ∧ Nat.card (closure (Set.range j3tD)) = 360 := by
  rw [← j3t_caseA.1, range_j3tD]
  exact commutator_le_of_derivedLeOK j3tKeys_lt
    (fun k hk => enumOK_gens_valid (centOKP_enum j3t_cases_check.1) hk) j3t_derived_check.1

theorem evalW_wordPow {m : ℕ} {G : Type*} [Group G] (g : Fin m → G) (w : List (Fin m × Bool))
    (k : ℕ) : evalW g (wordPow w k) = evalW g w ^ k := by
  induction k with
  | zero => simp [wordPow, evalW]
  | succ k ih =>
    rw [pow_succ', ← ih, wordPow, wordPow, List.replicate_succ, List.flatten_cons, evalW_append]

theorem evalW_single {m : ℕ} {G : Type*} [Group G] (g : Fin m → G) (i : Fin m) :
    evalW g [(i, true)] = g i := by
  simp [evalW]

theorem exists_lift_A6 {X G : Type*} [Group X] [Finite X] [Group G] (ρ : X →* G)
    (hker : ρ.ker ≤ center X) (hp : IsPGroup 3 ρ.ker) (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1)
    (d : Fin 2 → G) (hd : ∀ i, ∃ x, ρ x = d i) {g : G} (hg : ∃ x, ρ x = g)
    (hrel : ∀ w ∈ j3tA6Rels, evalW d w = 1)
    (hgu : g * evalW d j3tWu * g⁻¹ = evalW d j3tWv)
    (hgv : g * evalW d j3tWv * g⁻¹ = evalW d j3tWu * evalW d j3tWv ^ 1)
    (huv : evalW d j3tWu * evalW d j3tWv = evalW d j3tWv * evalW d j3tWu)
    (hΓ : Finite (PG 2 j3tLiftRels) ∧ Nat.card (PG 2 j3tLiftRels) ≤ 90 * 4) :
    ∃ D₀ : Subgroup X, D₀.map ρ = closure (Set.range d) ∧ Nat.card D₀ ≤ 360 := by
  classical
  choose x hx using hd
  obtain ⟨gg, hgg⟩ := hg
  have hrel' : ∀ w ∈ j3tA6Rels, evalW (fun i => ρ (x i)) w = 1 := by
    intro w hw
    rw [show (fun i => ρ (x i)) = d from funext hx]
    exact hrel w hw
  have hmem : ∀ {w : List (Fin 2 × Bool)}, w ∈ j3tA6Rels → ∀ ℓ : Fin 2 → X,
      (∀ i, ρ (ℓ i) = d i) → evalW ℓ w ∈ ρ.ker := by
    intro w hw ℓ hℓ
    rw [MonoidHom.mem_ker, map_evalW, show (fun i => ρ (ℓ i)) = d from funext hℓ]
    exact hrel w hw
  have ho0 : ρ (x 0) ^ 2 = 1 := by
    rw [hx 0, ← evalW_single d 0, ← evalW_wordPow]
    exact hrel _ (by simp [j3tA6Rels])
  have ho1 : ρ (x 1) ^ 4 = 1 := by
    rw [hx 1, ← evalW_single d 1, ← evalW_wordPow]
    exact hrel _ (by simp [j3tA6Rels])
  obtain ⟨z0, hz0, hz0'⟩ := exists_mul_pow_eq_one hker hp (x 0) ho0 (by norm_num)
  obtain ⟨z1, hz1, hz1'⟩ := exists_mul_pow_eq_one hker hp (x 1) ho1 (by norm_num)
  let ℓ : Fin 2 → X := fun i => if i = 0 then x 0 * z0 else x 1 * z1
  have hℓ0 : ℓ 0 = x 0 * z0 := rfl
  have hℓ1 : ℓ 1 = x 1 * z1 := rfl
  have hℓ : ∀ i, ρ (ℓ i) = d i := by
    intro i
    fin_cases i
    · show ρ (x 0 * z0) = d 0
      rw [map_mul, MonoidHom.mem_ker.1 hz0, mul_one, hx 0]
    · show ρ (x 1 * z1) = d 1
      rw [map_mul, MonoidHom.mem_ker.1 hz1, mul_one, hx 1]
  have hcent : ∀ {w : List (Fin 2 × Bool)}, w ∈ j3tA6Rels → evalW ℓ w ∈ center X :=
    fun hw => hker (hmem hw ℓ hℓ)
  have hrels : ∀ w ∈ j3tLiftRels, evalW ℓ w = 1 := by
    intro w hw
    simp only [j3tLiftRels, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [evalW_wordPow, evalW_single, hℓ0]; exact hz0'
    · rw [evalW_wordPow, evalW_single, hℓ1]; exact hz1'
    · rw [evalW_wordPow, show 15 = 5 * 3 by norm_num, pow_mul, ← evalW_wordPow]
      exact h3 _ (hmem (by simp [j3tA6Rels]) ℓ hℓ)
    · rw [evalW_wordPow, show 15 = 5 * 3 by norm_num, pow_mul, ← evalW_wordPow]
      exact h3 _ (hmem (by simp [j3tA6Rels]) ℓ hℓ)
    · rw [evalW_commW, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp (hcent (by simp [j3tA6Rels])) _).symm
    · rw [evalW_commW, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp (hcent (by simp [j3tA6Rels])) _).symm
    · rw [evalW_commW, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp (hcent (by simp [j3tA6Rels])) _).symm
    · rw [evalW_commW, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp (hcent (by simp [j3tA6Rels])) _).symm
    ·
      rw [evalW_commW]
      set u := evalW ℓ j3tWu
      set v := evalW ℓ j3tWv
      have hρu : ρ u = evalW d j3tWu := by
        rw [map_evalW, show (fun i => ρ (ℓ i)) = d from funext hℓ]
      have hρv : ρ v = evalW d j3tWv := by
        rw [map_evalW, show (fun i => ρ (ℓ i)) = d from funext hℓ]
      have hck : ⁅u, v⁆ ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_commutatorElement, hρu, hρv,
          commutatorElement_eq_one_iff_mul_comm]
        exact huv
      have hc₁ : v⁻¹ * (gg * u * gg⁻¹) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hgg, hρu, hρv, hgu,
          inv_mul_cancel]
      have hc₂ : (u * v)⁻¹ * (gg * v * gg⁻¹) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, hgg, hρu,
          hρv, hgv, pow_one, inv_mul_cancel]
      exact commutator_eq_one_of_det (g := gg) (hker hck) (h3 _ hck) (hker hc₁) (hker hc₂)
        (by group) (by group)
  refine ⟨closure (Set.range ℓ), ?_, ?_⟩
  · rw [MonoidHom.map_closure, ← Set.range_comp]
    congr 2
    exact funext hℓ
  · exact (card_closure_le_of_rels ℓ j3tLiftRels hrels hΓ.1).trans hΓ.2


theorem isPGroup_j3t_caseB :
    IsPGroup 3 (centralizer {j3tXB} ⊓ j3P : Subgroup (Equiv.Perm (Fin 6156))) := by
  rw [← j3t_caseB.1]
  exact IsPGroup.of_card (n := 5) (by rw [j3t_caseB.2]; norm_num)

set_option maxRecDepth 20000 in
theorem j3Cover_of_mulEquiv {G : Type*} [Mul G] (φ : G ≃* j3P) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nat.card (center X) = 3 →
      Nonempty (X ⧸ center X ≃* G) → ∀ y : X, y ∉ center X → y ^ 3 ∈ center X →
        ∀ P : Subgroup X, P ≤ centralizer {y} → Group.IsPerfect P → P ⊓ center X = ⊥ := by
  intro X _ _ _ hZ ⟨e⟩ y hy hy3 P hP hperf
  let ψ : X ⧸ center X ≃* j3P := e.trans φ
  let ρ : X →* Equiv.Perm (Fin 6156) :=
    j3P.subtype.comp (ψ.toMonoidHom.comp (QuotientGroup.mk' (center X)))
  have hρ : ∀ w : X, ρ w = (ψ (w : X ⧸ center X) : Equiv.Perm (Fin 6156)) := fun w => rfl
  have hρker : ρ.ker = center X := by
    ext w
    rw [MonoidHom.mem_ker, hρ]
    constructor
    · intro h
      have h1 : ψ (w : X ⧸ center X) = 1 := Subtype.ext h
      rwa [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff] at h1
    · intro h
      rw [(QuotientGroup.eq_one_iff w).2 h, map_one]
      rfl
  have hρR : ρ.range = j3P := by
    ext r
    constructor
    · rintro ⟨w, rfl⟩
      rw [hρ]
      exact (ψ _).2
    · intro hr
      obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (ψ.symm ⟨r, hr⟩)
      refine ⟨w, ?_⟩
      rw [hρ, hw, MulEquiv.apply_symm_apply]
  have hZ3 : IsPGroup 3 ρ.ker := hρker ▸ IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1 := by
    intro z hz
    rw [hρker] at hz
    have h := pow_card_eq_one' (G := center X) (x := ⟨z, hz⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hpre : ∀ r ∈ j3P, ∃ w, ρ w = r := fun r hr => by
    rw [← hρR] at hr
    exact hr
  obtain ⟨D₀, hD₀, hD₀card⟩ := exists_lift_A6 ρ hρker.le hZ3 h3 j3tD
    (fun i => hpre _ (j3tD_mem i)) (hpre _ j3tGPerm_mem) j3tD_rels j3t_det.1 j3t_det.2.1
    j3t_det.2.2 (card_le_of_cyclicCheckC j3tLiftRels [2] (by norm_num) j3t_lift_check)
  have hD₀Z : D₀ ⊓ center X = ⊥ := by
    rw [← hρker]
    apply inf_ker_eq_bot_of_card_le
    rw [hD₀, j3t_derived.2]
    exact hD₀card
  exact perfect_inf_center_eq_bot (hperf := hperf) ρ hρker hZ hρR
    (j3tReps_spec (by norm_num)).2 (j3tReps_spec (by norm_num)).2
    (fun x hx hxo => j3t_fusion hx hxo) isPGroup_j3t_caseB j3t_derived.1 hD₀ hD₀Z hy hy3 hP

theorem j3CoverCentralizer : J3CoverCentralizer :=
  j3Cover_of_mulEquiv j3PermEquiv

end CFSG.RankThree.PartTwo.KFacts.K426
