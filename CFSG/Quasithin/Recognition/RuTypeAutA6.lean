module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK

public section

namespace CFSG.Quasithin.RuType.AutA6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

@[expose] def inM10L (c : List ℕ) : Bool :=
  [Core.cid, [0, 8, 4, 5, 1, 6, 7, 3, 2, 9]].any fun rinv => Core.pslLit.contains (Core.cmul c rinv)

@[expose] def conjC (m c t : List ℕ) : Bool := Core.cmul m c == Core.cmul t m

@[expose] def tFrobL : List ℕ := [0, 1, 2, 6, 7, 8, 3, 4, 5, 9]

@[expose] def tMulFrobL : List ℕ := [0, 4, 8, 7, 2, 3, 5, 6, 1, 9]

@[expose] def dL : List ℕ := [3, 7, 9, 0, 8, 6, 5, 1, 4, 2]

@[expose] def centCheck (C : List (List ℕ)) : Bool :=
  C.all fun a => Core.cmul a a != Core.cid || inM10L a || Core.inS6 a ||
    C.all fun b => Core.cmul b b != Core.cid || inM10L b || Core.inS6 b ||
      C.any fun p => conjC p a b

section Packed

open CFSG.Permutation.FinPack CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK

private theorem inM10L_pk {a : List ℕ} (ha : IsC a) : inM10L a = inM10K (pk a) := by
  unfold inM10L inM10K
  exact in2_pk ha isC_m10Rep pk_m10Rep

private theorem centCheck_pk {C : List (List ℕ)} (hC : ∀ c ∈ C, IsC c) :
    centCheck C = centCK (C.map pk) := by
  unfold centCheck centCK
  refine all_pk fun a ha => ?_
  beta_reduce
  rw [bne, sq_pk (hC a ha), inM10L_pk (hC a ha), inS6_pk (hC a ha)]
  congr 1
  refine all_pk fun b hb => ?_
  beta_reduce
  rw [bne, sq_pk (hC b hb), inM10L_pk (hC b hb), inS6_pk (hC b hb)]
  congr 1
  refine any_pk fun p hp => ?_
  beta_reduce
  unfold conjC
  rw [peq_pk (hC p hp) (hC a ha) (hC b hb) (hC p hp)]

theorem cent_classes : Core.pslLit.all (fun t => Core.cmul t t != Core.cid || t == Core.cid ||
    centCheck (Core.autL.filter fun x => Core.cmul x t == Core.cmul t x)) = true := by
  refine (all_pk (q := fun t => !Nat.beq (mulK 10 t t) idK || Nat.beq t idK ||
    centCK (autK.filter fun x => commLaneK 10 x t)) fun t ht => ?_).trans ?_
  · have ht' := isC_of_psl ht
    have hF : ∀ c ∈ Core.autL.filter (fun x => Core.cmul x t == Core.cmul t x), IsC c :=
      fun c hc => isC_of_autL (List.mem_filter.1 hc).1
    beta_reduce
    rw [bne, sq_pk ht', beq_pk ht' isC_cid, pk_cid, centCheck_pk hF,
      map_filter_pk (q := fun x => commLaneK 10 x (pk t)) fun x hx => comm_pk (isC_of_autL hx) ht',
      autK_pin]
  · rw [beq_iff_eq.1 pslK_pin]
    exact centK_true

theorem out_classes_s6_check : Core.autL.all (fun c => Core.cmul c c != Core.cid || inM10L c ||
    !Core.inS6 c || Core.pslLit.any fun y =>
      conjC y c tFrobL || conjC (Core.cmul y tMulFrobL) c tFrobL) = true := by
  refine (all_pk (q := fun c => !Nat.beq (mulK 10 c c) idK || inM10K c || !inS6K c ||
    (anyK (fun y => peqK y c 641083073040 y) pslK ||
      anyK (fun y => peqK y c 641083073040 y) m10tK)) fun c hc => ?_).trans ?_
  · have hc' := isC_of_autL hc
    beta_reduce
    unfold conjC tFrobL tMulFrobL
    rw [bne, sq_pk hc', inM10L_pk hc', inS6_pk hc', out_any_pk hc' isC_tFrob pk_tFrob]
  · rw [autK_pin]
    exact outS6K_true

theorem out_classes_d_check : Core.autL.all (fun c => Core.cmul c c != Core.cid || inM10L c ||
    Core.inS6 c || Core.pslLit.any fun y => conjC y c dL || conjC (Core.cmul y tMulFrobL) c dL) =
      true := by
  refine (all_pk (q := fun c => !Nat.beq (mulK 10 c c) idK || inM10K c || inS6K c ||
    (anyK (fun y => peqK y c 154977962355 y) pslK ||
      anyK (fun y => peqK y c 154977962355 y) m10tK)) fun c hc => ?_).trans ?_
  · have hc' := isC_of_autL hc
    beta_reduce
    unfold conjC dL tMulFrobL
    rw [bne, sq_pk hc', inM10L_pk hc', inS6_pk hc', out_any_pk hc' isC_dL pk_dL]
  · rw [autK_pin]
    exact outDK_true

end Packed

theorem inM10L_eq (c : List ℕ) : inM10L c = Out21.A6.inM10C c := by
  have h : Out21.A6.m10RepsInvC = [Core.cid, [0, 8, 4, 5, 1, 6, 7, 3, 2, 9]] := by decide +kernel
  rw [inM10L, Out21.A6.inM10C, h]

theorem mem_m10_iff (x : P10) : x ∈ A6Models.m10 ↔ inM10L (code x) = true := by
  rw [Out21.A6.mem_m10_iff_code, inM10L_eq]

theorem code_tFrob : code A6Models.tFrob = tFrobL := by decide +kernel

theorem code_tMulFrob : code A6Models.tMulFrob = tMulFrobL := by decide +kernel

@[expose] def dInv : P10 := A6Models.perm10 [[0, 3], [1, 7], [2, 9], [4, 8], [5, 6]]

theorem code_dInv : code dInv = dL := by decide +kernel

theorem dInv_mul_self : dInv * dInv = 1 := by decide +kernel

theorem dInv_comm : dInv * (A6Models.tAdd * A6Models.tSq * A6Models.tInv) =
    A6Models.tAdd * A6Models.tSq * A6Models.tInv * dInv := by decide +kernel

theorem dInv_mem_pgl29 : dInv ∈ A6Models.pgl29 := by
  rw [Out21.A6.mem_pgl29_iff_code, code_dInv]
  decide +kernel

theorem dInv_not_mem_m10 : dInv ∉ A6Models.m10 := by
  rw [mem_m10_iff, code_dInv]
  decide +kernel

theorem dInv_not_mem_s6 : dInv ∉ s6 := by
  rw [mem_s6_iff, code_dInv]
  decide +kernel

theorem dInv_not_mem_psl29 : dInv ∉ A6Models.psl29 :=
  fun h => dInv_not_mem_m10 (Out21.A6.psl29_le_m10 h)

theorem dInv_mem_autA6 : dInv ∈ A6Models.autA6 := Out21.A6.pgl29_le_autA6 dInv_mem_pgl29

theorem tFrob_mul_self : A6Models.tFrob * A6Models.tFrob = 1 := by decide +kernel

theorem tFrob_not_mem_m10 : A6Models.tFrob ∉ A6Models.m10 := by
  rw [mem_m10_iff, code_tFrob]
  decide +kernel

theorem tFrob_mem_s6 : A6Models.tFrob ∈ s6 := by
  rw [mem_s6_iff, code_tFrob]
  decide +kernel

theorem tFrob_not_mem_psl29 : A6Models.tFrob ∉ A6Models.psl29 :=
  fun h => tFrob_not_mem_m10 (Out21.A6.psl29_le_m10 h)

theorem exists_of_mem_autL {c : List ℕ} (hc : c ∈ Core.autL) :
    ∃ x ∈ A6Models.autA6, code x = c := by
  unfold Core.autL at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨y, hy, hc⟩ := hc
  rw [List.mem_map] at hc
  obtain ⟨r, hr, rfl⟩ := hc
  obtain ⟨y', hy', rfl⟩ := exists_psl29_of_code hy
  rw [← autRepsP_code, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  refine ⟨y' * r', mul_mem (psl29_le_autA6 hy') ?_, code_mul _ _⟩
  rw [autA6_eq]
  exact autReps_mem_closure r' hr'

theorem eq_of_code {x y : P10} (h : code x = code y) : x = y := code_injective h

theorem exists_m10_of_check {c t : List ℕ} {σ τ : P10} (hσ : code σ = c) (hτ : code τ = t)
    (h : (Core.pslLit.any fun y => conjC y c t || conjC (Core.cmul y tMulFrobL) c t) = true) :
    ∃ m ∈ A6Models.m10, m * σ * m⁻¹ = τ := by
  rw [List.any_eq_true] at h
  obtain ⟨y, hy, h⟩ := h
  obtain ⟨y', hy', rfl⟩ := exists_psl29_of_code hy
  have key : ∀ m : P10, conjC (code m) c t = true → m * σ * m⁻¹ = τ := by
    intro m hm
    rw [conjC, beq_iff_eq, ← hσ, ← hτ, ← code_mul, ← code_mul] at hm
    rw [eq_of_code hm, mul_inv_cancel_right]
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact ⟨y', Out21.A6.psl29_le_m10 hy', key y' h⟩
  · refine ⟨y' * A6Models.tMulFrob, mul_mem (Out21.A6.psl29_le_m10 hy')
      Out21.A6.tMulFrob_mem_m10, key _ ?_⟩
    rw [code_mul, code_tMulFrob]
    exact h

theorem out_classes_s6 {σ : P10} (hσ : σ ∈ A6Models.autA6) (h2 : σ * σ = 1)
    (hm : σ ∉ A6Models.m10) (hs : σ ∈ s6) : ∃ m ∈ A6Models.m10, m * σ * m⁻¹ = A6Models.tFrob := by
  have h := out_classes_s6_check
  rw [List.all_eq_true] at h
  have h1 := h _ (code_mem_autL hσ)
  have hc2 : Core.cmul (code σ) (code σ) = Core.cid := by rw [← code_mul, h2, code_one]
  have hm' : inM10L (code σ) = false := by
    rw [← Bool.not_eq_true, ← mem_m10_iff]
    exact hm
  have hs' : Core.inS6 (code σ) = true := (mem_s6_iff σ).mp hs
  simp only [hc2, hm', hs', bne_self_eq_false, Bool.false_or, Bool.not_true] at h1
  exact exists_m10_of_check rfl code_tFrob h1

theorem out_classes_d {σ : P10} (hσ : σ ∈ A6Models.autA6) (h2 : σ * σ = 1)
    (hm : σ ∉ A6Models.m10) (hs : σ ∉ s6) : ∃ m ∈ A6Models.m10, m * σ * m⁻¹ = dInv := by
  have h := out_classes_d_check
  rw [List.all_eq_true] at h
  have h1 := h _ (code_mem_autL hσ)
  have hc2 : Core.cmul (code σ) (code σ) = Core.cid := by rw [← code_mul, h2, code_one]
  have hm' : inM10L (code σ) = false := by
    rw [← Bool.not_eq_true, ← mem_m10_iff]
    exact hm
  have hs' : Core.inS6 (code σ) = false := by
    rw [← Bool.not_eq_true, ← mem_s6_iff]
    exact hs
  simp only [hc2, hm', hs', bne_self_eq_false, Bool.false_or] at h1
  exact exists_m10_of_check rfl code_dInv h1

theorem cent_trans {τ : P10} (hτ : τ ∈ A6Models.psl29) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1)
    {σ₁ σ₂ : P10} (h₁ : σ₁ ∈ A6Models.autA6) (h₂ : σ₂ ∈ A6Models.autA6)
    (hc₁ : σ₁ * τ = τ * σ₁) (hc₂ : σ₂ * τ = τ * σ₂) (h₁2 : σ₁ * σ₁ = 1) (h₂2 : σ₂ * σ₂ = 1)
    (hm₁ : σ₁ ∉ A6Models.m10) (hm₂ : σ₂ ∉ A6Models.m10) (hs₁ : σ₁ ∉ s6) (hs₂ : σ₂ ∉ s6) :
    ∃ p ∈ A6Models.autA6, p * τ = τ * p ∧ p * σ₁ * p⁻¹ = σ₂ := by
  have h := cent_classes
  rw [List.all_eq_true] at h
  have h1 := h _ ((mem_psl29_iff τ).mp hτ)
  have ht2 : Core.cmul (code τ) (code τ) = Core.cid := by rw [← code_mul, hτ2, code_one]
  have ht1 : (code τ == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, ← code_one]
    exact fun h => hτ1 (code_injective h)
  simp only [ht2, ht1, bne_self_eq_false, Bool.false_or] at h1
  rw [centCheck, List.all_eq_true] at h1
  have hmem : ∀ {σ : P10}, σ ∈ A6Models.autA6 → σ * τ = τ * σ →
      code σ ∈ Core.autL.filter fun x => Core.cmul x (code τ) == Core.cmul (code τ) x := by
    intro σ hσ hc
    rw [List.mem_filter]
    refine ⟨code_mem_autL hσ, ?_⟩
    rw [beq_iff_eq, ← code_mul, ← code_mul, hc]
  have hprops : ∀ {σ : P10}, σ * σ = 1 → σ ∉ A6Models.m10 → σ ∉ s6 →
      Core.cmul (code σ) (code σ) = Core.cid ∧ inM10L (code σ) = false ∧
        Core.inS6 (code σ) = false := by
    intro σ h2 hm hs
    refine ⟨by rw [← code_mul, h2, code_one], ?_, ?_⟩
    · rw [← Bool.not_eq_true, ← mem_m10_iff]; exact hm
    · rw [← Bool.not_eq_true, ← mem_s6_iff]; exact hs
  have ha := h1 _ (hmem h₁ hc₁)
  obtain ⟨a1, a2, a3⟩ := hprops h₁2 hm₁ hs₁
  simp only [a1, a2, a3, bne_self_eq_false, Bool.false_or] at ha
  rw [List.all_eq_true] at ha
  have hb := ha _ (hmem h₂ hc₂)
  obtain ⟨b1, b2, b3⟩ := hprops h₂2 hm₂ hs₂
  simp only [b1, b2, b3, bne_self_eq_false, Bool.false_or] at hb
  rw [List.any_eq_true] at hb
  obtain ⟨pc, hpc, hp⟩ := hb
  rw [List.mem_filter] at hpc
  obtain ⟨hpA, hpτ⟩ := hpc
  obtain ⟨p, hp', rfl⟩ := exists_of_mem_autL hpA
  refine ⟨p, hp', ?_, ?_⟩
  · rw [beq_iff_eq, ← code_mul, ← code_mul] at hpτ
    exact code_injective hpτ
  · rw [conjC, beq_iff_eq, ← code_mul, ← code_mul] at hp
    rw [code_injective hp, mul_inv_cancel_right]

end CFSG.Quasithin.RuType.AutA6
