module

public import CFSG.RankThree.Native.SuzFiveCheck
public import CFSG.Sporadic.SuzOddCore.InvGraphBound
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.Monster.B.Mathieu.SylowSound
public import CFSG.Sporadic.SuzOddCore.Restrict

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Fischer CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Mathieu (powArr rep_powArr)

theorem suzFive_getElem!_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    {i : ℕ} (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]


theorem suzFiveKeys_lt : ∀ p ∈ suzFiveKeys, p < 1782 := by decide

theorem suzFive_mem_M {g : Array ℕ} {G : Equiv.Perm (Fin 1782)} (hG : Rep 1782 g G)
    (h : suzFiveInM g = true) : G ∈ suzM :=
  (mem_suzM_iff_siftA hG).1 h

theorem suzFive_mem_T {g : Array ℕ} {G : Equiv.Perm (Fin 1782)} (hG : Rep 1782 g G)
    (h : suzFiveInT g = true) : G ∈ suzT := by
  rw [mem_suzT_iff]
  rw [suzFiveInT, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (suzFive_mem_M hG h)
  · exact Or.inr (suzFive_mem_M (rep_compA rep_v hG) h)

theorem suzFive_comm_closure {G : Type*} [Group G] {S : Set G}
    (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {x : G} (hx : x ∈ Subgroup.closure S) :
    ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).2 fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => h b hb a ha
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set G) :=
    (Subgroup.closure_le _).2 fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb =>
      (Subgroup.mem_centralizer_iff.1 (h1 hb) a ha).symm
  intro y hy
  exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y hy).symm

theorem suzFive_mem_centralizer_closure {G : Type*} [Group G] {S : Set G} {g : G}
    (h : ∀ s ∈ S, s * g = g * s) : g ∈ Subgroup.centralizer (Subgroup.closure S : Set G) := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer {g} :=
    (Subgroup.closure_le _).2 fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (h s hs)
  exact Subgroup.mem_centralizer_iff.2 fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hd)

theorem suzFive_enum_inj {gs : Array (Array ℕ)} {c : ArrCert}
    (hc : enumOK 1782 gs suzFiveKeys c = true) {i j : ℕ} (hi : i < c.pts.size)
    (hj : j < c.pts.size) (h : permOfArr 1782 c.pts[i]! = permOfArr 1782 c.pts[j]!) : i = j := by
  obtain ⟨hmem, hcard, -⟩ := enumOK_spec suzFiveKeys_lt hc
  set H := Subgroup.closure (permsA 1782 gs)
  let φ : Fin c.pts.size → H := fun k => ⟨permOfArr 1782 c.pts[k.val]!, (hmem _).2 ⟨k, k.2, rfl⟩⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk, rfl⟩ := (hmem x).1 hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hbij := hsurj.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card,
    Fintype.card_fin, hcard])
  have := hbij.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Subtype.ext h)
  exact congrArg Fin.val this

structure SuzFiveQFacts : Prop where
  enum : enumOK 1782 suzFiveQArrs suzFiveKeys suzFiveQCert = true
  size : suzFiveQCert.pts.size = 25
  comm : commA 1782 suzFiveQArrs[0]! suzFiveQArrs[1]! = true
  two : suzFiveQArrs.size = 2
  inM0 : suzFiveInM suzFiveQArrs[0]! = true
  inM1 : suzFiveInM suzFiveQArrs[1]! = true
  pow : allLt 25 (fun k => eqA 1782 (powArr 1782 suzFiveQCert.pts[k]! 5) (idA 1782)) = true
  cover : allLt 25 (fun k => eqA 1782 suzFiveQCert.pts[k]! (idA 1782) ||
    (List.range 6).any fun j => (List.range 5).any fun e =>
      eqA 1782 suzFiveQCert.pts[k]! (powArr 1782 suzFiveLines[j]! e)) = true
  dist : allLt 6 (fun j => allLt 6 fun j' => j == j' ||
    allLt 5 fun e => !(eqA 1782 suzFiveLines[j]! (powArr 1782 suzFiveLines[j']! e))) = true
  lines : allLt 6 (fun j => validA 1782 suzFiveLines[j]! &&
    eqA 1782 (powArr 1782 suzFiveLines[j]! 5) (idA 1782) &&
    !(eqA 1782 suzFiveLines[j]! (idA 1782)) &&
    suzFiveQCert.pts.toList.any (eqA 1782 suzFiveLines[j]!)) = true

theorem suzFive_Q_facts : SuzFiveQFacts := by
  have h := suzFive_Q_check
  simp only [suzFiveQCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem suzFiveLines_get {j : ℕ} (hj : j < 6) : suzFiveLines[j]! = suzFiveLineArr j := by
  rw [suzFiveLines, getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn]

theorem suzFiveLine_facts (j : Fin 6) :
    validA 1782 (suzFiveLineArr j) = true ∧
    eqA 1782 (powArr 1782 (suzFiveLineArr j) 5) (idA 1782) = true ∧
    eqA 1782 (suzFiveLineArr j) (idA 1782) = false ∧
    suzFiveQCert.pts.toList.any (eqA 1782 (suzFiveLineArr j)) = true := by
  have h := allLt_spec suzFive_Q_facts.lines j.2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [suzFiveLines_get j.2] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rep_suzFiveLine (j : Fin 6) : Rep 1782 (suzFiveLineArr j) (suzFiveLine j) :=
  rep_of_validA (suzFiveLine_facts j).1

theorem suzFiveQ_spec :
    (∀ x, x ∈ suzFiveQ ↔ ∃ k < suzFiveQCert.pts.size, permOfArr 1782 suzFiveQCert.pts[k]! = x) ∧
    Nat.card suzFiveQ = 25 ∧ ∀ k < suzFiveQCert.pts.size,
      validA 1782 suzFiveQCert.pts[k]! = true := by
  obtain ⟨h1, h2, h3⟩ := enumOK_spec suzFiveKeys_lt suzFive_Q_facts.enum
  exact ⟨h1, h2.trans suzFive_Q_facts.size, h3⟩

theorem suzFiveQ_elem {x : Equiv.Perm (Fin 1782)} (hx : x ∈ suzFiveQ) :
    ∃ k < 25, Rep 1782 suzFiveQCert.pts[k]! x := by
  obtain ⟨k, hk, rfl⟩ := (suzFiveQ_spec.1 x).1 hx
  exact ⟨k, suzFive_Q_facts.size ▸ hk, rep_of_validA (suzFiveQ_spec.2.2 k hk)⟩

theorem rep_suzFiveQGen {k : ℕ} (hk : k < 2) :
    Rep 1782 suzFiveQArrs[k]! (permOfArr 1782 suzFiveQArrs[k]!) :=
  rep_of_validA (enumOK_gens_valid suzFive_Q_facts.enum (by rw [suzFive_Q_facts.two]; exact hk))

theorem suzFiveQ_le_M : suzFiveQ ≤ suzM := by
  rw [suzFiveQ, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := by have := suzFive_Q_facts.two; simp only [Set.mem_ofPred_eq] at hk; omega
  interval_cases k
  · exact suzFive_mem_M (rep_suzFiveQGen (by norm_num)) suzFive_Q_facts.inM0
  · exact suzFive_mem_M (rep_suzFiveQGen (by norm_num)) suzFive_Q_facts.inM1

theorem suzFiveQ_comm : ∀ g ∈ suzFiveQ, ∀ h ∈ suzFiveQ, g * h = h * g := by
  intro g hg h hh
  refine suzFive_comm_closure ?_ hg h hh
  rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
  have hk2 : k < 2 := by have := suzFive_Q_facts.two; simp only [Set.mem_ofPred_eq] at hk; omega
  have hl2 : l < 2 := by have := suzFive_Q_facts.two; simp only [Set.mem_ofPred_eq] at hl; omega
  have hab := (commA_iff (rep_suzFiveQGen (k := 0) (by norm_num))
    (rep_suzFiveQGen (k := 1) (by norm_num))).1 suzFive_Q_facts.comm
  interval_cases k <;> interval_cases l
  · rfl
  · exact hab
  · exact hab.symm
  · rfl

theorem suzFiveLine_mem_Q (j : Fin 6) : suzFiveLine j ∈ suzFiveQ :=
  enumOK_mem_of_any suzFiveKeys_lt suzFive_Q_facts.enum (rep_suzFiveLine j)
    (suzFiveLine_facts j).2.2.2

theorem suzFiveLine_ne_one (j : Fin 6) : suzFiveLine j ≠ 1 := fun h => by
  have := (eqA_iff (rep_suzFiveLine j) rep_idA).2 h
  rw [(suzFiveLine_facts j).2.2.1] at this
  exact Bool.false_ne_true this

theorem suzFiveLine_pow_five (j : Fin 6) : suzFiveLine j ^ 5 = 1 :=
  (eqA_iff (rep_powArr (rep_suzFiveLine j) 5) rep_idA).1 (suzFiveLine_facts j).2.1

theorem orderOf_suzFiveLine (j : Fin 6) : orderOf (suzFiveLine j) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (suzFiveLine_pow_five j) (suzFiveLine_ne_one j)

theorem suzFiveQ_pow_five {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzFiveQ) : g ^ 5 = 1 := by
  obtain ⟨k, hk, hkg⟩ := suzFiveQ_elem hg
  exact (eqA_iff (rep_powArr hkg 5) rep_idA).1 (allLt_spec suzFive_Q_facts.pow hk)

theorem exponent_suzFiveQ : Monoid.exponent suzFiveQ = 5 := by
  have hdvd : Monoid.exponent suzFiveQ ∣ 5 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (suzFiveQ_pow_five g.2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h | h
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 h
    have := congrArg Subtype.val
      (hs.elim (⟨suzFiveLine 0, suzFiveLine_mem_Q 0⟩ : suzFiveQ) 1)
    exact suzFiveLine_ne_one 0 this
  · exact h

theorem factorization_card_suzM_five : (Nat.card suzM).factorization 5 = 2 := by
  rw [suzM_card_chain, show (448345497600 : ℕ) = 5 ^ 2 * 17933819904 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem suzFiveQ_sylow : ∃ S : Sylow 5 suzM, (S : Subgroup suzM) = suzFiveQ.subgroupOf suzM := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (suzFiveQ.subgroupOf suzM) = 5 ^ (Nat.card suzM).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzFiveQ_le_M).toEquiv, suzFiveQ_spec.2.1,
      factorization_card_suzM_five]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem suzFiveQ_lines :
    {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => Subgroup.zpowers (suzFiveLine i)) ∧
      Function.Injective (fun i : Fin 6 => Subgroup.zpowers (suzFiveLine i)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply prime_subgroups_eq_range suzFiveLine suzFiveLine_mem_Q suzFiveLine_ne_one
    suzFiveLine_pow_five
  · intro g hg hg1
    obtain ⟨k, hk, hkg⟩ := suzFiveQ_elem hg
    have h := allLt_spec suzFive_Q_facts.cover hk
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
    rcases h with h | ⟨j, hj, e, he, hje⟩
    · exact absurd ((eqA_iff hkg rep_idA).1 h) hg1
    · rw [suzFiveLines_get hj] at hje
      exact ⟨⟨j, hj⟩, e, (eqA_iff hkg (rep_powArr (rep_suzFiveLine ⟨j, hj⟩) e)).1 hje⟩
  · intro j j' k hk hjj'
    have h := allLt_spec (allLt_spec suzFive_Q_facts.dist j.2) j'.2
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact Fin.ext h
    · have h' := allLt_spec h hk
      rw [suzFiveLines_get j.2, suzFiveLines_get j'.2, Bool.not_eq_true'] at h'
      have := (eqA_iff (rep_suzFiveLine j) (rep_powArr (rep_suzFiveLine j') k)).2 hjj'
      rw [h'] at this
      exact absurd this Bool.false_ne_true

theorem suzFiveStage_size (tt : Array ℕ) (init : ℕ) (steps : List (ℕ × ℕ × ℕ)) :
    ∀ s, (suzFiveStage tt init steps s).size = 1782
  | 0 => by
    rw [suzFiveStage]
    rcases refineIterT_size tt (initColour "fixed" tt) init with h | h
    · rw [h]; simp [initColour]
    · exact h
  | s + 1 => by
    rw [suzFiveStage]
    rcases refineIterT_size tt (indivPoint (suzFiveStage tt init steps s)
      (steps.getD s (0, 0, 0)).1 s) (steps.getD s (0, 0, 0)).2.2 with h | h
    · rw [h, indivPoint, Array.size_set!, suzFiveStage_size tt init steps s]
    · exact h

@[expose] def suzFiveBasePt (steps : List (ℕ × ℕ × ℕ)) (s : ℕ) : Fin 1782 :=
  pt 1782 (steps.getD s (0, 0, 0)).1

theorem suzFiveStage_inv {tt : Array ℕ} {t σ : Equiv.Perm (Fin 1782)} (ht : Rep 1782 tt t)
    (hσ : NbrInv invNbr σ) (hcomm : ∀ x, σ (t x) = t (σ x)) {init : ℕ}
    {steps : List (ℕ × ℕ × ℕ)} (hpts : ∀ s < steps.length, (steps.getD s (0, 0, 0)).1 < 1782) :
    ∀ s ≤ steps.length, (∀ r < s, σ (suzFiveBasePt steps r) = suzFiveBasePt steps r) →
      ColInv 1782 (suzFiveStage tt init steps s) σ
  | 0, _, _ => by
    rw [suzFiveStage]
    exact refineIterT_inv ht hσ hcomm (initColour_inv ht hσ hcomm _) _
  | s + 1, hs, hfix => by
    rw [suzFiveStage]
    refine refineIterT_inv ht hσ hcomm ?_ _
    have hp := hpts s (by omega)
    refine indivPoint_inv (suzFiveStage_size tt init steps s) hp ?_
      (suzFiveStage_inv ht hσ hcomm hpts s (by omega) fun r hr => hfix r (by omega))
    have := hfix s (by omega)
    have e : suzFiveBasePt steps s = ⟨(steps.getD s (0, 0, 0)).1, hp⟩ := Fin.ext (pt_val hp)
    rwa [e] at this

@[expose] def suzFiveCentStab (t : Equiv.Perm (Fin 1782)) (steps : List (ℕ × ℕ × ℕ)) (s : ℕ) :
    Subgroup (autCent t) :=
  stabChain (suzFiveBasePt steps) s

section Bound

variable {tt : Array ℕ} {t : Equiv.Perm (Fin 1782)} (ht : Rep 1782 tt t) {init : ℕ}
  {steps : List (ℕ × ℕ × ℕ)} (hg : suzFiveGraphCheck tt init steps = true)
include ht hg

omit ht in
theorem suzFiveGraphCheck_spec :
    (∀ s < steps.length, (steps.getD s (0, 0, 0)).1 < 1782) ∧
    (∀ s < steps.length, classCount (suzFiveStage tt init steps s) (steps.getD s (0, 0, 0)).1 ≤
      (steps.getD s (0, 0, 0)).2.1) ∧
    ((suzFiveStage tt init steps steps.length).toList.take 1782).Nodup := by
  have h := hg
  rw [suzFiveGraphCheck] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := h
  refine ⟨fun s hs => ?_, fun s hs => of_decide_eq_true (allLt_spec h2 hs), of_decide_eq_true h3⟩
  rw [List.all_eq_true] at h1
  rw [List.getD_eq_getElem _ _ hs]
  exact of_decide_eq_true (h1 _ (List.getElem_mem hs))

theorem colInv_of_suzFiveCentStab {s : ℕ} (hs : s ≤ steps.length) {σ : autCent t}
    (hσ : σ ∈ suzFiveCentStab t steps s) :
    ColInv 1782 (suzFiveStage tt init steps s) (σ : invGraph ≃g invGraph).toEquiv :=
  suzFiveStage_inv ht (nbrInv_of_aut _) (mem_autCent.1 σ.2) (suzFiveGraphCheck_spec hg).1
    s hs ((mem_stabChain (G := autCent t)).1 hσ)

theorem suzFiveCentStab_orbit {s : ℕ} (hs : s < steps.length) :
    (MulAction.orbit (suzFiveCentStab t steps s) (suzFiveBasePt steps s)).ncard ≤
      (steps.getD s (0, 0, 0)).2.1 := by
  refine le_trans ?_ ((suzFiveGraphCheck_spec hg).2.1 s hs)
  rw [classCount, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨⟨σ, hσ⟩, rfl⟩
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  have hp := (suzFiveGraphCheck_spec hg).1 s hs
  rw [← pt_val hp]
  exact colInv_of_suzFiveCentStab ht hg hs.le hσ (suzFiveBasePt steps s)

theorem suzFiveCentStab_last : suzFiveCentStab t steps steps.length = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have hc := colInv_of_suzFiveCentStab ht hg le_rfl hσ
  have hnd := (suzFiveGraphCheck_spec hg).2.2
  have hsize := suzFiveStage_size tt init steps steps.length
  apply Subtype.ext
  refine RelIso.ext fun v => Fin.ext ?_
  have h := hc v
  rw [List.take_of_length_le (by simp [hsize])] at hnd
  rw [getElem!_pos _ _ (by rw [hsize]; exact ((σ : invGraph ≃g invGraph) v).2),
    getElem!_pos _ _ (by rw [hsize]; exact v.2), ← Array.getElem_toList,
    ← Array.getElem_toList] at h
  exact (hnd.getElem_inj_iff).1 h

theorem card_centralizer_suzT_le :
    Nat.card (Subgroup.centralizer {t} ⊓ suzT : Subgroup (Equiv.Perm (Fin 1782))) ≤
      ∏ s ∈ Finset.range steps.length, (steps.getD s (0, 0, 0)).2.1 := by
  have hA : Nat.card (autCent t) ≤ ∏ s ∈ Finset.range steps.length,
      (steps.getD s (0, 0, 0)).2.1 :=
    card_le_prod_of_stabChain (G := autCent t) (suzFiveBasePt steps)
      (fun s => (steps.getD s (0, 0, 0)).2.1) _
      (fun _ hs => suzFiveCentStab_orbit ht hg hs) (suzFiveCentStab_last ht hg)
  refine le_trans ?_ hA
  refine Nat.card_le_card_of_injective
    (fun g => ⟨toAut g.2.2, mem_autCent.2 fun x => ?_⟩) ?_
  · have := congrArg (fun h : Equiv.Perm (Fin 1782) => h x)
      (Subgroup.mem_centralizer_singleton_iff.1 g.2.1)
    simp only [Equiv.Perm.mul_apply] at this
    rw [toAut_apply, toAut_apply]
    exact this
  · intro g h hgh
    apply Subtype.ext
    have := congrArg (fun σ : autCent t => (σ : invGraph ≃g invGraph).toEquiv) hgh
    exact this

end Bound

theorem suzFiveCCheck_spec {cs : Array (Array ℕ)} {x : Array ℕ} {c : ArrCert} {sz : ℕ}
    (h : suzFiveCCheck cs x c sz = true) :
    enumOK 1782 cs suzFiveKeys c = true ∧ c.pts.size = sz ∧
      (∀ k < cs.size, commA 1782 cs[k]! x = true ∧ suzFiveInT cs[k]! = true) ∧
      validA 1782 x = true ∧ c.pts.toList.any (eqA 1782 x) = true := by
  simp only [suzFiveCCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun k hk => ?_, h4, h5⟩
  have := allLt_spec h3 hk
  simpa only [Bool.and_eq_true] using this

theorem suzFiveC_check_spec {i : ℕ} (hi : i < 6) :
    enumOK 1782 (suzFiveCArrs i) suzFiveKeys (suzFiveCCert i) = true ∧
      (suzFiveCCert i).pts.size = suzFiveCentOrders[i]! ∧
      (∀ k < (suzFiveCArrs i).size, commA 1782 (suzFiveCArrs i)[k]! (suzFiveLineArr i) = true ∧
        suzFiveInT (suzFiveCArrs i)[k]! = true) ∧
      validA 1782 (suzFiveLineArr i) = true ∧
      (suzFiveCCert i).pts.toList.any (eqA 1782 (suzFiveLineArr i)) = true :=
  suzFiveCCheck_spec (suzFive_C_check i hi)

theorem rep_suzFiveCGen {i : ℕ} (hi : i < 6) {k : ℕ} (hk : k < (suzFiveCArrs i).size) :
    Rep 1782 (suzFiveCArrs i)[k]! (permOfArr 1782 (suzFiveCArrs i)[k]!) :=
  rep_of_validA (enumOK_gens_valid (suzFiveC_check_spec hi).1 hk)

theorem suzFiveC_le {i : ℕ} (hi : i < 6) :
    suzFiveC ⟨i, hi⟩ ≤ Subgroup.centralizer {suzFiveLine ⟨i, hi⟩} ⊓ suzT := by
  rw [suzFiveC, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨hc, hT⟩ := (suzFiveC_check_spec hi).2.2.1 k hk
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
    ((commA_iff (rep_suzFiveCGen hi hk) (rep_suzFiveLine ⟨i, hi⟩)).1 hc),
    suzFive_mem_T (rep_suzFiveCGen hi hk) hT⟩

theorem card_suzFiveC {i : ℕ} (hi : i < 6) : Nat.card (suzFiveC ⟨i, hi⟩) = suzFiveCentOrders[i]! :=
  (enumOK_spec suzFiveKeys_lt (suzFiveC_check_spec hi).1).2.1.trans (suzFiveC_check_spec hi).2.1

theorem suzFiveLine_mem_C {i : ℕ} (hi : i < 6) : suzFiveLine ⟨i, hi⟩ ∈ suzFiveC ⟨i, hi⟩ :=
  enumOK_mem_of_any suzFiveKeys_lt (suzFiveC_check_spec hi).1 (rep_suzFiveLine ⟨i, hi⟩)
    (suzFiveC_check_spec hi).2.2.2.2

theorem suzFive_steps_prod {i : ℕ} (hi : i < 6) :
    ∏ s ∈ Finset.range suzFiveSteps[i]!.length, (suzFiveSteps[i]!.getD s (0, 0, 0)).2.1 =
      suzFiveCentOrders[i]! := by
  interval_cases i <;> decide

theorem suzFiveC_eq {i : ℕ} (hi : i < 6) :
    suzFiveC ⟨i, hi⟩ = Subgroup.centralizer {suzFiveLine ⟨i, hi⟩} ⊓ suzT := by
  refine Subgroup.eq_of_le_of_card_ge (suzFiveC_le hi) ?_
  rw [card_suzFiveC hi, ← suzFive_steps_prod hi]
  exact card_centralizer_suzT_le (rep_suzFiveLine ⟨i, hi⟩) (suzFive_graph_check i hi)

theorem suzFiveDCheck_spec {cs : Array (Array ℕ)} {cC : ArrCert} {ds : Array (Array ℕ)}
    {cD : ArrCert} {dsz : ℕ} {x : Array ℕ} {cnt : ℕ}
    (h : suzFiveDCheck cs cC ds cD dsz x cnt = true) :
    enumOK 1782 ds suzFiveKeys cD = true ∧ cD.pts.size = dsz ∧ 2 ≤ ds.size ∧
      (∀ k < cs.size, ∀ l < ds.size,
        cD.pts.toList.any (eqA 1782 (conjA 1782 cs[k]! ds[l]!)) = true) ∧
      (∀ k < cs.size, ∀ l < cs.size,
        cD.pts.toList.any (eqA 1782 (commutatorA 1782 cs[k]! cs[l]!)) = true) ∧
      (∀ l < ds.size, suzFiveInM ds[l]! = true) ∧ commA 1782 ds[0]! ds[1]! = false ∧
      suzFiveCentCount cC ds = cnt ∧
      (cnt = 5 → ∀ k < cC.pts.size, (allLt ds.size fun l => commA 1782 cC.pts[k]! ds[l]!) = true →
        ∃ e < 5, eqA 1782 cC.pts[k]! (powArr 1782 x e) = true) := by
  simp only [suzFiveDCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h9⟩, h10⟩ := h
  refine ⟨h1, h2, h3, fun k hk l hl => allLt_spec (allLt_spec h4 hk) hl,
    fun k hk l hl => allLt_spec (allLt_spec h5 hk) hl, fun l hl => allLt_spec h6 hl, h7, h9,
    fun h5' k hk hcomm => ?_⟩
  rw [Bool.or_eq_true, bne_iff_ne] at h10
  rcases h10 with h10 | h10
  · exact absurd h5' h10
  · have := allLt_spec h10 hk
    rw [hcomm, Bool.not_true, Bool.false_or, List.any_eq_true] at this
    obtain ⟨e, he, hx⟩ := this
    exact ⟨e, List.mem_range.1 he, hx⟩

theorem suzFive_pair_facts {i : ℕ} (hi : i < 6) {l : ℕ} (hl : l < suzFiveDerivedPairs[i]!.size) :
    (suzFiveDerivedPairs[i]!)[l]!.1 < (suzFiveCArrs i).size ∧
      validA 1782 (suzFiveBfs i)[(suzFiveDerivedPairs[i]!)[l]!.2]! = true ∧
      permOfArr 1782 (suzFiveBfs i)[(suzFiveDerivedPairs[i]!)[l]!.2]! ∈ suzFiveC ⟨i, hi⟩ := by
  have h := suzFive_pairs_check i hi
  simp only [suzFivePairsCheck] at h
  have h' := allLt_spec h hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  exact ⟨h1, h2, enumOK_mem_of_any suzFiveKeys_lt (suzFiveC_check_spec hi).1 (rep_of_validA h2) h3⟩

theorem suzFiveD_eq_closure {i : ℕ} (hi : i < 6) {dsz cnt : ℕ} {xa : Array ℕ}
    (hD : suzFiveDCheck (suzFiveCArrs i) (suzFiveCCert i) (suzFiveDArrs i) (suzFiveDCert i) dsz
      xa cnt = true) :
    suzFiveD ⟨i, hi⟩ = Subgroup.closure (permsA 1782 (suzFiveDArrs i)) := by
  obtain ⟨hDe, -, -, hnorm, hcomm, -⟩ := suzFiveDCheck_spec hD
  have hdsz : (suzFiveDArrs i).size = suzFiveDerivedPairs[i]!.size := by simp [suzFiveDArrs]
  rw [suzFiveD, suzFiveC]
  apply commutator_closure_eq_closure
  · rintro _ ⟨k, hk, rfl⟩
    have hk' : k < suzFiveDerivedPairs[i]!.size := by rw [← hdsz]; exact hk
    obtain ⟨hj, hv, hmem⟩ := suzFive_pair_facts hi hk'
    have hg := enumOK_gens_valid (suzFiveC_check_spec hi).1 hj
    show permOfArr 1782 (suzFiveDArrs i)[k]! ∈ _
    rw [show (suzFiveDArrs i)[k]! = commutatorA 1782
        (suzFiveCArrs i)[(suzFiveDerivedPairs[i]!)[k]!.1]!
        (suzFiveBfs i)[(suzFiveDerivedPairs[i]!)[k]!.2]! from suzFive_getElem!_map _ _ hk',
      permOfArr_eq_of_rep (rep_commutatorA hg hv)]
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure (mem_permsA hj)) hmem
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any suzFiveKeys_lt hDe
      (rep_conjA (enumOK_gens_valid (suzFiveC_check_spec hi).1 hk)
        (rep_of_validA (enumOK_gens_valid hDe hl))) (hnorm k hk l hl)
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any suzFiveKeys_lt hDe
      (rep_commutatorA (enumOK_gens_valid (suzFiveC_check_spec hi).1 hk)
        (enumOK_gens_valid (suzFiveC_check_spec hi).1 hl)) (hcomm k hk l hl)

theorem isSimpleGroup_of_orbit {ds : Array (Array ℕ)} {L : List ℕ} {m dsz : ℕ} {c : ArrCert}
    (hval : ∀ l < ds.size, validA 1782 ds[l]! = true) (hL : PointsList 1782 m L)
    (hpres : ∀ l < ds.size, ∀ x ∈ L, (ds[l]!)[x]! ∈ L)
    (hc : enumOK m (ds.map (restrictArr L)) (suzFivePosKeys m) c = true) (hsz : c.pts.size = dsz)
    (hD : Nat.card (Subgroup.closure (permsA 1782 ds)) = dsz) (hdsz : dsz * 2 = m.factorial)
    (hm5 : 5 ≤ m) : IsSimpleGroup (Subgroup.closure (permsA 1782 ds)) := by
  set H := Subgroup.closure (permsA 1782 ds)
  have hrep : ∀ l < ds.size, Rep 1782 ds[l]! (permOfArr 1782 ds[l]!) :=
    fun l hl => rep_of_validA (hval l hl)
  have hH : ∀ g ∈ H, ∀ x : Fin 1782, (x : ℕ) ∈ L → (g x : ℕ) ∈ L := by
    intro g hg x hx
    have := CFSG.Perm.smul_mem_of_finite_of_mem_closure (F := {y : Fin 1782 | (y : ℕ) ∈ L})
      (Set.toFinite _) (fun s hs y hy => by
        obtain ⟨l, hl, rfl⟩ := hs
        show ((permOfArr 1782 ds[l]! y : Fin 1782) : ℕ) ∈ L
        rw [← (hrep l hl) y]
        exact hpres l hl _ hy) hg hx
    exact this
  set ρ := hL.restrHom H hH
  let gen : ℕ → H := fun l => if h : l < ds.size then
    ⟨permOfArr 1782 ds[l]!, Subgroup.subset_closure (mem_permsA h)⟩ else 1
  have hgen : ∀ l < ds.size, ((gen l : H) : Equiv.Perm (Fin 1782)) = permOfArr 1782 ds[l]! :=
    fun l hl => by simp [gen, hl]
  have htop : (⊤ : Subgroup H) = Subgroup.closure (gen '' {l | l < ds.size}) := by
    symm
    rw [eq_top_iff]
    rintro ⟨g, hg⟩ -
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨l, hl, Subtype.ext (hgen l hl)⟩
    | one => exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx => exact Subgroup.inv_mem _ ihx
  have htab : ∀ l < ds.size, Rep m (ds.map (restrictArr L))[l]! (ρ (gen l)) := by
    intro l hl
    rw [suzFive_getElem!_map _ _ hl]
    have := hL.tabRep_restrHom H hH (gen l) (t := ds[l]!) (by rw [hgen l hl]; exact hrep l hl)
    exact fun i => this.apply i
  have hrange : ρ.range = Subgroup.closure (permsA m (ds.map (restrictArr L))) := by
    rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure, ← Set.image_comp]
    congr 1
    unfold permsA
    rw [Array.size_map]
    apply Set.image_congr
    intro l hl
    exact (permOfArr_eq_of_rep (htab l hl)).symm
  have hkeys : ∀ p ∈ suzFivePosKeys m, p < m := by
    intro p hp
    simpa [suzFivePosKeys] using hp
  have hcardR : Nat.card ρ.range = dsz := by
    rw [hrange, (enumOK_spec hkeys hc).2.1, hsz]
  have hinj : Function.Injective ρ := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hcardR, hD] at h
    have hpos : 0 < dsz := by
      have := Nat.factorial_pos m
      omega
    have hk : Nat.card ρ.ker = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact h.symm)
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hindex : ρ.range.index = 2 := by
    have h := ρ.range.index_mul_card
    rw [hcardR, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin, ← hdsz] at h
    have hpos : 0 < dsz := by
      have := Nat.factorial_pos m
      omega
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  have hA : ρ.range = alternatingGroup (Fin m) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  have hsimple : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm5)
  have e : H ≃* alternatingGroup (Fin m) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hA)
  exact (MulEquiv.isSimpleGroup_congr e).2 hsimple

theorem suzFiveD_facts {i : ℕ} (hi : i < 6) {dsz cnt m : ℕ}
    (hD : suzFiveDCheck (suzFiveCArrs i) (suzFiveCCert i) (suzFiveDArrs i) (suzFiveDCert i) dsz
      (suzFiveLineArr i) cnt = true) (hdo : suzFiveDerivedOrders[i]! = dsz)
    (hm : suzFiveOrbits[i]!.length = m) (hL : PointsList 1782 m suzFiveOrbits[i]!)
    (hdsz : dsz * 2 = m.factorial) (hm5 : 5 ≤ m) :
    Nat.card (suzFiveD ⟨i, hi⟩) = dsz ∧ suzFiveD ⟨i, hi⟩ ≤ suzM ∧
      IsSimpleGroup (suzFiveD ⟨i, hi⟩) ∧
      (∃ g ∈ suzFiveD ⟨i, hi⟩, ∃ h ∈ suzFiveD ⟨i, hi⟩, g * h ≠ h * g) := by
  obtain ⟨hDe, hsize, htwo, -, -, hinM, hnonab, -⟩ := suzFiveDCheck_spec hD
  have heq := suzFiveD_eq_closure hi hD
  have hrep : ∀ l < (suzFiveDArrs i).size,
      Rep 1782 (suzFiveDArrs i)[l]! (permOfArr 1782 (suzFiveDArrs i)[l]!) :=
    fun l hl => rep_of_validA (enumOK_gens_valid hDe hl)
  have hcard : Nat.card (Subgroup.closure (permsA 1782 (suzFiveDArrs i))) = dsz := by
    rw [(enumOK_spec suzFiveKeys_lt hDe).2.1, hsize]
  have ho := suzFive_orbit_check i hi
  rw [hm, hdo] at ho
  simp only [suzFiveOrbitCheck, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true,
    List.all_eq_true, List.contains_iff_mem] at ho
  obtain ⟨⟨⟨-, hpres⟩, hoc⟩, hosz⟩ := ho
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq, hcard]
  · rw [heq, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact suzFive_mem_M (hrep l hl) (hinM l hl)
  · rw [heq]
    refine isSimpleGroup_of_orbit (fun l hl => enumOK_gens_valid hDe hl) hL
      (fun l hl x hx => ?_) hoc hosz hcard hdsz hm5
    rw [getElem!_pos _ l hl]
    exact hpres l hl x hx
  · rw [heq]
    refine ⟨permOfArr 1782 (suzFiveDArrs i)[0]!, Subgroup.subset_closure (mem_permsA (by omega)),
      permOfArr 1782 (suzFiveDArrs i)[1]!, Subgroup.subset_closure (mem_permsA (by omega)),
      fun he => ?_⟩
    have := (commA_iff (hrep 0 (by omega)) (hrep 1 (by omega))).2 he
    rw [hnonab] at this
    exact Bool.false_ne_true this

theorem suzFive_points (i : Fin 6) :
    PointsList 1782 suzFiveOrbits[i.val]!.length suzFiveOrbits[i.val]! := by
  refine ⟨rfl, ?_, ?_⟩ <;> fin_cases i <;> decide

theorem mem_cent_suzFiveD_iff {i : ℕ} (hi : i < 6) {dsz cnt : ℕ}
    (hD : suzFiveDCheck (suzFiveCArrs i) (suzFiveCCert i) (suzFiveDArrs i) (suzFiveDCert i) dsz
      (suzFiveLineArr i) cnt = true) {k : ℕ} (hk : k < (suzFiveCCert i).pts.size) :
    permOfArr 1782 (suzFiveCCert i).pts[k]! ∈
        Subgroup.centralizer (suzFiveD ⟨i, hi⟩ : Set (Equiv.Perm (Fin 1782))) ↔
      (allLt (suzFiveDArrs i).size fun l =>
        commA 1782 (suzFiveCCert i).pts[k]! (suzFiveDArrs i)[l]!) = true := by
  obtain ⟨hDe, -⟩ := suzFiveDCheck_spec hD
  have hval := (enumOK_spec suzFiveKeys_lt (suzFiveC_check_spec hi).1).2.2 k hk
  rw [suzFiveD_eq_closure hi hD, CFSG.Monster.B.Co2.allLt_iff]
  constructor
  · intro hc l hl
    have hd : permOfArr 1782 (suzFiveDArrs i)[l]! ∈
        Subgroup.closure (permsA 1782 (suzFiveDArrs i)) :=
      Subgroup.subset_closure (mem_permsA hl)
    exact (commA_iff (rep_of_validA hval) (rep_of_validA (enumOK_gens_valid hDe hl))).2
      (Subgroup.mem_centralizer_iff.1 hc _ hd).symm
  · intro hc
    apply suzFive_mem_centralizer_closure
    rintro _ ⟨l, hl, rfl⟩
    exact ((commA_iff (rep_of_validA hval) (rep_of_validA (enumOK_gens_valid hDe hl))).1
      (hc l hl)).symm

theorem card_cent_suzFiveD {i : ℕ} (hi : i < 6) {dsz cnt : ℕ}
    (hD : suzFiveDCheck (suzFiveCArrs i) (suzFiveCCert i) (suzFiveDArrs i) (suzFiveDCert i) dsz
      (suzFiveLineArr i) cnt = true) :
    Nat.card (Subgroup.centralizer (suzFiveD ⟨i, hi⟩ : Set (Equiv.Perm (Fin 1782))) ⊓
      suzFiveC ⟨i, hi⟩ : Subgroup (Equiv.Perm (Fin 1782))) = cnt := by
  obtain ⟨-, -, -, -, -, -, -, hcnt, -⟩ := suzFiveDCheck_spec hD
  have hC := (suzFiveC_check_spec hi).1
  obtain ⟨hmem, -, -⟩ := enumOK_spec suzFiveKeys_lt hC
  set S := (Finset.range (suzFiveCCert i).pts.size).filter fun k =>
    (allLt (suzFiveDArrs i).size fun l =>
      commA 1782 (suzFiveCCert i).pts[k]! (suzFiveDArrs i)[l]!) = true
  have hS : S.card = cnt := by
    rw [← hcnt, suzFiveCentCount, ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
    congr 1
    ext k
    simp [S]
  rw [← hS, ← Nat.card_eq_finsetCard]
  symm
  refine Nat.card_eq_of_bijective (fun k => ⟨permOfArr 1782 (suzFiveCCert i).pts[k.1]!, ?_⟩)
    ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := k
    simp only [S, Finset.mem_filter, Finset.mem_range] at hk
    exact Subgroup.mem_inf.2 ⟨(mem_cent_suzFiveD_iff hi hD hk.1).2 hk.2, (hmem _).2 ⟨k, hk.1, rfl⟩⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [S, Finset.mem_filter, Finset.mem_range] at ha hb
    exact Subtype.ext (suzFive_enum_inj hC ha.1 hb.1 (congrArg Subtype.val hab))
  · rintro ⟨g, hg⟩
    obtain ⟨hgc, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, rfl⟩ := (hmem g).1 hgC
    refine ⟨⟨k, ?_⟩, rfl⟩
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, (mem_cent_suzFiveD_iff hi hD hk).1 hgc⟩

theorem cent_suzFiveD_eq {i : ℕ} (hi : i < 6) {dsz : ℕ}
    (hD : suzFiveDCheck (suzFiveCArrs i) (suzFiveCCert i) (suzFiveDArrs i) (suzFiveDCert i) dsz
      (suzFiveLineArr i) 5 = true) :
    Subgroup.centralizer (suzFiveD ⟨i, hi⟩ : Set (Equiv.Perm (Fin 1782))) ⊓ suzFiveC ⟨i, hi⟩ =
      Subgroup.zpowers (suzFiveLine ⟨i, hi⟩) := by
  obtain ⟨-, -, -, -, -, -, -, -, hpow⟩ := suzFiveDCheck_spec hD
  have hC := (suzFiveC_check_spec hi).1
  obtain ⟨hmem, -, hval⟩ := enumOK_spec suzFiveKeys_lt hC
  apply le_antisymm
  · intro g hg
    obtain ⟨hgc, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, rfl⟩ := (hmem g).1 hgC
    obtain ⟨e, -, he⟩ := hpow rfl k hk ((mem_cent_suzFiveD_iff hi hD hk).1 hgc)
    rw [(eqA_iff (rep_of_validA (hval k hk)) (rep_powArr (rep_suzFiveLine ⟨i, hi⟩) e)).1 he]
    exact Subgroup.npow_mem_zpowers _ e
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun d hd => ?_, suzFiveLine_mem_C hi⟩
    have hdC : d ∈ suzFiveC ⟨i, hi⟩ := by
      rw [suzFiveD] at hd
      refine (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) hd
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
        (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
    rw [suzFiveC_eq hi] at hdC
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hdC).1

theorem R3E_Suz_full_five_centralizer_structures :
    (suzFiveQ ≤ suzM ∧ (∀ g ∈ suzFiveQ, ∀ h ∈ suzFiveQ, g * h = h * g) ∧
      Monoid.exponent suzFiveQ = 5 ∧ Nat.card suzFiveQ = 25 ∧
      ∃ S : Sylow 5 suzM, (S : Subgroup suzM) = suzFiveQ.subgroupOf suzM) ∧
    ({H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => Subgroup.zpowers (suzFiveLine i)) ∧
      Function.Injective (fun i : Fin 6 => Subgroup.zpowers (suzFiveLine i))) ∧
    (∀ i : Fin 6, suzFiveC i = Subgroup.centralizer {suzFiveLine i} ⊓ suzT ∧
      IsSimpleGroup (suzFiveD i) ∧ (∃ g ∈ suzFiveD i, ∃ h ∈ suzFiveD i, g * h ≠ h * g) ∧
      suzFiveD i ≤ suzM) ∧
    (∀ i : Fin 6, i.val = 0 ∨ i.val = 3 ∨ i.val = 4 →
      Nat.card (suzFiveC i) = 3600 ∧ Nat.card (suzFiveD i) = 360 ∧
      Subgroup.centralizer (suzFiveD i : Set (Equiv.Perm (Fin 1782))) ⊓ suzFiveC i =
        Subgroup.zpowers (suzFiveLine i) ∧ Nat.card (Subgroup.zpowers (suzFiveLine i)) = 5) ∧
    (∀ i : Fin 6, i.val = 1 ∨ i.val = 2 ∨ i.val = 5 →
      Nat.card (suzFiveC i) = 600 ∧ Nat.card (suzFiveD i) = 60 ∧
      Nat.card (Subgroup.centralizer (suzFiveD i : Set (Equiv.Perm (Fin 1782))) ⊓ suzFiveC i :
        Subgroup (Equiv.Perm (Fin 1782))) = 10) := by
  have F0 := suzFiveD_facts (i := 0) (by norm_num) suzFive_D_check_0 (by decide) (by decide)
    (suzFive_points 0) (by decide) (by decide)
  have F1 := suzFiveD_facts (i := 1) (by norm_num) suzFive_D_check_1 (by decide) (by decide)
    (suzFive_points 1) (by decide) (by decide)
  have F2 := suzFiveD_facts (i := 2) (by norm_num) suzFive_D_check_2 (by decide) (by decide)
    (suzFive_points 2) (by decide) (by decide)
  have F3 := suzFiveD_facts (i := 3) (by norm_num) suzFive_D_check_3 (by decide) (by decide)
    (suzFive_points 3) (by decide) (by decide)
  have F4 := suzFiveD_facts (i := 4) (by norm_num) suzFive_D_check_4 (by decide) (by decide)
    (suzFive_points 4) (by decide) (by decide)
  have F5 := suzFiveD_facts (i := 5) (by norm_num) suzFive_D_check_5 (by decide) (by decide)
    (suzFive_points 5) (by decide) (by decide)
  refine ⟨⟨suzFiveQ_le_M, suzFiveQ_comm, exponent_suzFiveQ, suzFiveQ_spec.2.1, suzFiveQ_sylow⟩,
    suzFiveQ_lines, fun i => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨v, hv⟩ := i
    interval_cases v
    · exact ⟨suzFiveC_eq hv, F0.2.2.1, F0.2.2.2, F0.2.1⟩
    · exact ⟨suzFiveC_eq hv, F1.2.2.1, F1.2.2.2, F1.2.1⟩
    · exact ⟨suzFiveC_eq hv, F2.2.2.1, F2.2.2.2, F2.2.1⟩
    · exact ⟨suzFiveC_eq hv, F3.2.2.1, F3.2.2.2, F3.2.1⟩
    · exact ⟨suzFiveC_eq hv, F4.2.2.1, F4.2.2.2, F4.2.1⟩
    · exact ⟨suzFiveC_eq hv, F5.2.2.1, F5.2.2.2, F5.2.1⟩
  · obtain ⟨v, hv⟩ := i
    simp only at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨card_suzFiveC hv, F0.1, cent_suzFiveD_eq hv suzFive_D_check_0,
        by rw [Nat.card_zpowers, orderOf_suzFiveLine]⟩
    · exact ⟨card_suzFiveC hv, F3.1, cent_suzFiveD_eq hv suzFive_D_check_3,
        by rw [Nat.card_zpowers, orderOf_suzFiveLine]⟩
    · exact ⟨card_suzFiveC hv, F4.1, cent_suzFiveD_eq hv suzFive_D_check_4,
        by rw [Nat.card_zpowers, orderOf_suzFiveLine]⟩
  · obtain ⟨v, hv⟩ := i
    simp only at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨card_suzFiveC hv, F1.1, card_cent_suzFiveD hv suzFive_D_check_1⟩
    · exact ⟨card_suzFiveC hv, F2.1, card_cent_suzFiveD hv suzFive_D_check_2⟩
    · exact ⟨card_suzFiveC hv, F5.1, card_cent_suzFiveD hv suzFive_D_check_5⟩

end CFSG.RankThree.Native
