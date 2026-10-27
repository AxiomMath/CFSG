module

public import CFSG.GH74.GLS.C3.Layer1.P34RealL2C
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutBridge
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.A6Facts.Core

@[expose] def w183fin_comm (a b : List Nat) : Bool := cmul a b == cmul b a

@[expose] def w183fin_isInvC (c : List Nat) : Bool := cmul c c == cid && c != cid

@[expose] def w183fin_normE (a b g : List Nat) : Bool :=
  [a, b].all fun y => [a, b, cmul a b].any fun e => cmul g y == cmul e g

@[expose] def w183fin_violates (l : List (List Nat)) (a b : List Nat) : Bool :=
  [a, b, cmul a b].any fun t => l.any fun g => w183fin_comm g t && !w183fin_normE a b g

@[expose] def w183fin_noTI (l : List (List Nat)) : Bool :=
  let iv := l.filter w183fin_isInvC
  iv.all fun a => iv.all fun b => a == b || !w183fin_comm a b || w183fin_violates l a b

private theorem w183fin_code_comm (x y : P10) :
    w183fin_comm (code x) (code y) = true ↔ x * y = y * x := by
  unfold w183fin_comm
  rw [← code_mul, ← code_mul, beq_iff_eq]
  exact ⟨fun h => code_injective h, fun h => by rw [h]⟩

private theorem w183fin_code_isInv (x : P10) :
    w183fin_isInvC (code x) = true ↔ x * x = 1 ∧ x ≠ 1 := by
  unfold w183fin_isInvC
  rw [← code_mul, ← code_one, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  exact ⟨fun ⟨h1, h2⟩ => ⟨code_injective h1, fun h => h2 (by rw [h])⟩,
    fun ⟨h1, h2⟩ => ⟨by rw [h1], fun h => h2 (code_injective h)⟩⟩

private theorem w183fin_normE_true_of (a b g : P10) (hya : ∃ e ∈ [a, b, a * b], g * a = e * g)
    (hyb : ∃ e ∈ [a, b, a * b], g * b = e * g) :
    w183fin_normE (code a) (code b) (code g) = true := by
  have key : ∀ y : P10, (∃ e ∈ [a, b, a * b], g * y = e * g) →
      ([code a, code b, cmul (code a) (code b)].any fun e =>
        cmul (code g) (code y) == cmul e (code g)) = true := by
    rintro y ⟨e, he, hge⟩
    rw [List.any_eq_true]
    refine ⟨code e, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
      rcases he with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (code_mul _ _))
    · rw [← code_mul, ← code_mul, beq_iff_eq]
      exact congrArg code hge
  unfold w183fin_normE
  rw [List.all_eq_true]
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact key a hya
  · exact key b hyb

theorem w183fin_noTI_sound (B : Subgroup P10) (l : List (List Nat))
    (hl : ∀ x : P10, x ∈ B ↔ code x ∈ l) (hs : ∀ c ∈ l, ∃ x ∈ B, code x = c)
    (h : w183fin_noTI l = true) :
    ∀ A : Subgroup P10, A ≤ B → Nat.card A = 4 → (∀ x ∈ A, x * x = 1) →
      ∃ t ∈ A, t ≠ 1 ∧ ∃ g ∈ B, g * t = t * g ∧ g ∉ Subgroup.normalizer (A : Set P10) := by
  intro A hAB hcard hsq
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ :=
    CFSG.GH74.GLS.C3.Layer1.P34Real.exists_two_ne_one_of_four hcard
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  have hab_mem : a * b ∈ A := A.mul_mem ha hb
  have hcomm : a * b = b * a := by
    have h1 := hsq (a * b) hab_mem
    have h2 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    rw [mul_inv_rev, hbinv, hainv] at h2
    exact h2.symm
  have hab1 : a * b ≠ 1 := by
    intro h1
    apply hab
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this, hbinv]
  have haba : a * b ≠ a := by
    intro h1
    apply hb1
    simpa using h1
  have habb : a * b ≠ b := by
    intro h1
    apply ha1
    simpa using h1
  have hcases : ∀ w ∈ A, w = 1 ∨ w = a ∨ w = b ∨ w = a * b := fun w hw =>
    CFSG.RankTwoShapes.eq_of_mem_card_four hcard ha hb ha1 hb1 hab hab1 haba habb hw
  have hla : code a ∈ l := (hl a).1 (hAB ha)
  have hlb : code b ∈ l := (hl b).1 (hAB hb)
  have hia : w183fin_isInvC (code a) = true := (w183fin_code_isInv a).2 ⟨hsq a ha, ha1⟩
  have hib : w183fin_isInvC (code b) = true := (w183fin_code_isInv b).2 ⟨hsq b hb, hb1⟩
  have hna : code a ≠ code b := fun h => hab (code_injective h)
  have hcab : w183fin_comm (code a) (code b) = true := (w183fin_code_comm a b).2 hcomm
  unfold w183fin_noTI at h
  rw [List.all_eq_true] at h
  have h0 := h (code a) (List.mem_filter.2 ⟨hla, hia⟩)
  rw [List.all_eq_true] at h0
  have h1 := h0 (code b) (List.mem_filter.2 ⟨hlb, hib⟩)
  have hv : w183fin_violates l (code a) (code b) = true := by
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with (h3 | h3) | h3
    · exact absurd h3 hna
    · simp [hcab] at h3
    · exact h3
  unfold w183fin_violates at hv
  rw [List.any_eq_true] at hv
  obtain ⟨tc, htc, hv2⟩ := hv
  rw [List.any_eq_true] at hv2
  obtain ⟨gc, hgc, hv3⟩ := hv2
  rw [Bool.and_eq_true] at hv3
  obtain ⟨hcg, hnorm⟩ := hv3
  obtain ⟨g, hgB, rfl⟩ := hs gc hgc
  have hnotnorm : g ∉ Subgroup.normalizer (A : Set P10) := by
    intro hg
    have hn : w183fin_normE (code a) (code b) (code g) = false := by simpa using hnorm
    have hconj : ∀ y ∈ A, y ≠ 1 → ∃ e ∈ [a, b, a * b], g * y = e * g := by
      intro y hy hy1
      have h1 : g * y * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hg y).1 hy
      refine ⟨g * y * g⁻¹, ?_, by group⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hcases _ h1 with h2 | h2 | h2 | h2
      · exfalso
        apply hy1
        have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [this, h2]; group
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
    have := w183fin_normE_true_of a b g (hconj a ha ha1) (hconj b hb hb1)
    rw [hn] at this
    exact Bool.false_ne_true this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htc
  rcases htc with rfl | rfl | rfl
  · exact ⟨a, ha, ha1, g, hgB, ((w183fin_code_comm g a).1 hcg), hnotnorm⟩
  · exact ⟨b, hb, hb1, g, hgB, ((w183fin_code_comm g b).1 hcg), hnotnorm⟩
  · have hc : w183fin_comm (code g) (code (a * b)) = true := by rwa [code_mul]
    exact ⟨a * b, hab_mem, hab1, g, hgB, ((w183fin_code_comm g (a * b)).1 hc), hnotnorm⟩

@[expose] def w183fin_tMulC : List Nat := [0, 4, 8, 5, 6, 1, 7, 2, 3, 9]

@[expose] def w183fin_tMulFrobC : List Nat := [0, 4, 8, 7, 2, 3, 5, 6, 1, 9]

@[expose] def w183fin_cosetL (t : List Nat) : List (List Nat) :=
  pslLit ++ pslLit.map fun c => cmul c t

@[expose] def w183fin_lPGL : List (List Nat) := w183fin_cosetL w183fin_tMulC

@[expose] def w183fin_lM10 : List (List Nat) := w183fin_cosetL w183fin_tMulFrobC

section Packed

open CFSG.Permutation.FinPack CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK

private theorem w183fin_comm_pk {a b : List Nat} (ha : IsC a) (hb : IsC b) :
    w183fin_comm a b = commLaneK 10 (pk a) (pk b) := by
  unfold w183fin_comm
  exact comm_pk ha hb

private theorem w183fin_isInv_pk {a : List Nat} (ha : IsC a) :
    w183fin_isInvC a = invTK (pk a) := by
  unfold w183fin_isInvC
  exact invT_pk ha

private theorem w183fin_normE_pk {a b g : List Nat} (ha : IsC a) (hb : IsC b) (hg : IsC g) :
    w183fin_normE a b g = normEK (pk a) (pk b) (pk (cmul a b)) (pk g) := by
  have hab := isC_cmul ha hb
  unfold w183fin_normE normEK
  simp only [List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true,
    Bool.or_false]
  rw [peq_pk hg ha ha hg, peq_pk hg ha hb hg, peq_pk hg ha hab hg, peq_pk hg hb ha hg,
    peq_pk hg hb hb hg, peq_pk hg hb hab hg]

private theorem w183fin_vt_pk {L : List (List Nat)} (hL : ∀ c ∈ L, IsC c) {a b t : List Nat}
    (ha : IsC a) (hb : IsC b) (ht : IsC t) :
    (L.any fun g => w183fin_comm g t && !w183fin_normE a b g) =
      vtK (L.map pk) (pk a) (pk b) (pk (cmul a b)) (pk t) := by
  unfold vtK
  refine any_pk fun g hg => ?_
  beta_reduce
  rw [w183fin_comm_pk (hL g hg) ht, w183fin_normE_pk ha hb (hL g hg)]

private theorem w183fin_viol_pk {L : List (List Nat)} (hL : ∀ c ∈ L, IsC c) {a b : List Nat}
    (ha : IsC a) (hb : IsC b) :
    w183fin_violates L a b = violK (L.map pk) (pk a) (pk b) (pk (cmul a b)) := by
  unfold w183fin_violates violK
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [w183fin_vt_pk hL ha hb ha, w183fin_vt_pk hL ha hb hb,
    w183fin_vt_pk hL ha hb (isC_cmul ha hb)]

private theorem w183fin_noTI_pk {L : List (List Nat)} (hL : ∀ c ∈ L, IsC c) {IV : List ℕ}
    (hIV : (L.map pk).filter invTK = IV) : w183fin_noTI L = noTIK (L.map pk) IV := by
  simp only [w183fin_noTI, all_filter]
  unfold noTIK
  simp only [allK_sub hIV]
  refine all_pk fun a ha => ?_
  beta_reduce
  rw [w183fin_isInv_pk (hL a ha)]
  congr 1
  refine all_pk fun b hb => ?_
  beta_reduce
  rw [w183fin_isInv_pk (hL b hb), beq_pk (hL a ha) (hL b hb), w183fin_comm_pk (hL a ha) (hL b hb),
    w183fin_viol_pk hL (hL a ha) (hL b hb), pk_cmul (hL a ha) (hL b hb)]

theorem w183fin_ti_m10 : w183fin_noTI w183fin_lM10 = true := by
  obtain ⟨hL, hM⟩ := coset_codes isC_tMulFrob m10t_pin
  unfold w183fin_lM10 w183fin_cosetL w183fin_tMulFrobC
  rw [w183fin_noTI_pk hL (IV := ivM10K) (by rw [hM]; exact beq_iff_eq.1 ivM10K_pin), hM]
  exact noTI_m10K

theorem w183fin_ti_pgl : w183fin_noTI w183fin_lPGL = true := by
  obtain ⟨hL, hM⟩ := coset_codes isC_tMul pglt_pin
  unfold w183fin_lPGL w183fin_cosetL w183fin_tMulC
  rw [w183fin_noTI_pk hL (IV := ivPGLK) (by rw [hM]; exact beq_iff_eq.1 ivPGLK_pin), hM]
  exact noTI_pglK

theorem w183fin_ti_aut : w183fin_noTI autL = true := by
  rw [w183fin_noTI_pk (fun c hc => isC_of_autL hc)
    (IV := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K.invK)
    (by rw [autK_pin]; exact beq_iff_eq.1 invK_pin), autK_pin]
  exact noTI_autK

end Packed

theorem w183fin_cosetL_spec {B : Subgroup P10} {t : P10} {tC : List Nat} (htC : code t = tC)
    (hB : ∀ x : P10, x ∈ B ↔ ∃ r ∈ [(1 : P10), t], x * r⁻¹ ∈ A6Models.psl29) :
    (∀ x : P10, x ∈ B ↔ code x ∈ w183fin_cosetL tC) ∧
      (∀ c ∈ w183fin_cosetL tC, ∃ x ∈ B, code x = c) := by
  have hpsl : A6Models.psl29 ≤ B := fun x hx => (hB x).2 ⟨1, by simp, by simpa using hx⟩
  have htB : t ∈ B := (hB t).2 ⟨t, by simp, by simpa using Subgroup.one_mem _⟩
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun c hc => ?_⟩
  · obtain ⟨r, hr, hxr⟩ := (hB x).1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [inv_one, mul_one] at hxr
      exact List.mem_append_left _ ((mem_psl29_iff x).1 hxr)
    · refine List.mem_append_right _ (List.mem_map.2 ⟨code (x * r⁻¹), (mem_psl29_iff _).1 hxr, ?_⟩)
      rw [← htC, ← code_mul]
      congr 1
      group
  · rcases List.mem_append.1 hx with h | h
    · exact hpsl ((mem_psl29_iff x).2 h)
    · obtain ⟨c, hc, hcx⟩ := List.mem_map.1 h
      obtain ⟨y, hy, rfl⟩ := exists_psl29_of_code hc
      have : x = y * t := code_injective (by rw [code_mul, htC, hcx])
      rw [this]
      exact B.mul_mem (hpsl hy) htB
  · rcases List.mem_append.1 hc with h | h
    · obtain ⟨y, hy, rfl⟩ := exists_psl29_of_code h
      exact ⟨y, hpsl hy, rfl⟩
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 h
      obtain ⟨y, hy, rfl⟩ := exists_psl29_of_code hc'
      exact ⟨y * t, B.mul_mem (hpsl hy) htB, by rw [code_mul, htC]⟩

theorem w183fin_autL_spec : (∀ x : P10, x ∈ A6Models.autA6 ↔ code x ∈ autL) ∧
    (∀ c ∈ autL, ∃ x ∈ A6Models.autA6, code x = c) := by
  have hs : ∀ c ∈ autL, ∃ x ∈ A6Models.autA6, code x = c := by
    intro c hc
    unfold autL at hc
    obtain ⟨y, hy, hc2⟩ := List.mem_flatMap.1 hc
    obtain ⟨rc, hrc, rfl⟩ := List.mem_map.1 hc2
    obtain ⟨y', hy', rfl⟩ := exists_psl29_of_code hy
    rw [← autRepsP_code] at hrc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hrc
    refine ⟨y' * r, (mem_autA6_iff_exists _).2 ⟨r, hr, by simpa using hy'⟩, by rw [code_mul]⟩
  refine ⟨fun x => ⟨code_mem_autL, fun hx => ?_⟩, hs⟩
  obtain ⟨x', hx', hxx'⟩ := hs _ hx
  rw [← code_injective hxx']
  exact hx'

theorem w183fin_map_normalizer {Y : Type} [Group Y] (f : Y →* P10) (A : Subgroup Y) {g : Y}
    (hg : g ∈ Subgroup.normalizer (A : Set Y)) :
    f g ∈ Subgroup.normalizer ((A.map f : Subgroup P10) : Set P10) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro p
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨g * a * g⁻¹, (hg a).1 ha, by simp⟩
  · rintro ⟨a, ha, hap⟩
    refine ⟨g⁻¹ * a * g, (hg (g⁻¹ * a * g)).2 (by simpa [mul_assoc] using ha), ?_⟩
    have : p = (f g)⁻¹ * f a * f g := by rw [hap]; group
    rw [this]
    simp

@[expose] def w183fin_g3viol (a b : List Nat) : Bool :=
  [a, b, cmul a b].any fun t => pslLit.any fun g =>
    w183fin_comm g t && !(w183fin_comm g a && w183fin_comm g b)

@[expose] def w183fin_g3 : Bool :=
  let iv := autL.filter w183fin_isInvC
  iv.all fun a => iv.all fun b => a == b || !w183fin_comm a b || w183fin_g3viol a b

section Packed

open CFSG.Permutation.FinPack CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK

private theorem w183fin_g3t_pk {a b t : List Nat} (ha : IsC a) (hb : IsC b) (ht : IsC t) :
    (pslLit.any fun g => w183fin_comm g t && !(w183fin_comm g a && w183fin_comm g b)) =
      g3tK (pk a) (pk b) (pk t) := by
  unfold g3tK
  rw [← beq_iff_eq.1 pslK_pin]
  refine any_pk fun g hg => ?_
  beta_reduce
  have hg' := isC_of_psl hg
  rw [w183fin_comm_pk hg' ht, w183fin_comm_pk hg' ha, w183fin_comm_pk hg' hb]

private theorem w183fin_g3_true : w183fin_g3 = true := by
  have hIV : autK.filter invTK = CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K.invK :=
    beq_iff_eq.1 invK_pin
  have hL : ∀ c ∈ autL, IsC c := fun c hc => isC_of_autL hc
  have e : w183fin_g3 = g3K := by
    simp only [w183fin_g3, all_filter]
    unfold g3K
    simp only [allK_sub hIV]
    rw [← autK_pin]
    refine all_pk fun a ha => ?_
    beta_reduce
    rw [w183fin_isInv_pk (hL a ha)]
    refine congrArg (fun x => !invTK (pk a) || x) (all_pk fun b hb => ?_)
    beta_reduce
    unfold w183fin_g3viol
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    rw [w183fin_isInv_pk (hL b hb), beq_pk (hL a ha) (hL b hb),
      w183fin_comm_pk (hL a ha) (hL b hb), w183fin_g3t_pk (hL a ha) (hL b hb) (hL a ha),
      w183fin_g3t_pk (hL a ha) (hL b hb) (hL b hb),
      w183fin_g3t_pk (hL a ha) (hL b hb) (isC_cmul (hL a ha) (hL b hb)),
      pk_cmul (hL a ha) (hL b hb)]
  rw [e]
  exact g3K_true

end Packed

theorem w183fin_g3_sound :
    ∀ A : Subgroup P10, A ≤ A6Models.autA6 → Nat.card A = 4 → (∀ x ∈ A, x * x = 1) →
      ∃ t ∈ A, t ≠ 1 ∧ ∃ g ∈ A6Models.psl29, g * t = t * g ∧ ∃ a ∈ A, g * a ≠ a * g := by
  intro A hAB hcard hsq
  obtain ⟨hl, hs⟩ := w183fin_autL_spec
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ :=
    CFSG.GH74.GLS.C3.Layer1.P34Real.exists_two_ne_one_of_four hcard
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  have hab_mem : a * b ∈ A := A.mul_mem ha hb
  have hcomm : a * b = b * a := by
    have h1 := hsq (a * b) hab_mem
    have h2 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    rw [mul_inv_rev, hbinv, hainv] at h2
    exact h2.symm
  have hab1 : a * b ≠ 1 := by
    intro h1
    apply hab
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this, hbinv]
  have hla : code a ∈ autL := (hl a).1 (hAB ha)
  have hlb : code b ∈ autL := (hl b).1 (hAB hb)
  have hia : w183fin_isInvC (code a) = true := (w183fin_code_isInv a).2 ⟨hsq a ha, ha1⟩
  have hib : w183fin_isInvC (code b) = true := (w183fin_code_isInv b).2 ⟨hsq b hb, hb1⟩
  have hna : code a ≠ code b := fun h => hab (code_injective h)
  have hcab : w183fin_comm (code a) (code b) = true := (w183fin_code_comm a b).2 hcomm
  have h := w183fin_g3_true
  unfold w183fin_g3 at h
  rw [List.all_eq_true] at h
  have h0 := h (code a) (List.mem_filter.2 ⟨hla, hia⟩)
  rw [List.all_eq_true] at h0
  have h1 := h0 (code b) (List.mem_filter.2 ⟨hlb, hib⟩)
  have hv : w183fin_g3viol (code a) (code b) = true := by
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with (h3 | h3) | h3
    · exact absurd h3 hna
    · simp [hcab] at h3
    · exact h3
  unfold w183fin_g3viol at hv
  rw [List.any_eq_true] at hv
  obtain ⟨tc, htc, hv2⟩ := hv
  rw [List.any_eq_true] at hv2
  obtain ⟨gc, hgc, hv3⟩ := hv2
  rw [Bool.and_eq_true] at hv3
  obtain ⟨hcg, hnorm⟩ := hv3
  obtain ⟨g, hgP, rfl⟩ := exists_psl29_of_code hgc
  have hnc : ¬ (g * a = a * g ∧ g * b = b * g) := by
    intro ⟨h1, h2⟩
    have : (w183fin_comm (code g) (code a) && w183fin_comm (code g) (code b)) = true := by
      rw [Bool.and_eq_true]
      exact ⟨(w183fin_code_comm g a).2 h1, (w183fin_code_comm g b).2 h2⟩
    simp [this] at hnorm
  have hex : ∃ a' ∈ A, g * a' ≠ a' * g := by
    by_contra hcon
    push Not at hcon
    exact hnc ⟨hcon a ha, hcon b hb⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htc
  rcases htc with rfl | rfl | rfl
  · exact ⟨a, ha, ha1, g, hgP, (w183fin_code_comm g a).1 hcg, hex⟩
  · exact ⟨b, hb, hb1, g, hgP, (w183fin_code_comm g b).1 hcg, hex⟩
  · have hc : w183fin_comm (code g) (code (a * b)) = true := by rwa [code_mul]
    exact ⟨a * b, hab_mem, hab1, g, hgP, (w183fin_code_comm g (a * b)).1 hc, hex⟩

open CFSG.QuasithinUnique.Setup.X3Aut (invC) in
@[expose] def w183fin_order4 (c : List Nat) : Bool :=
  cmul c c != cid && cmul (cmul c c) (cmul c c) == cid

open CFSG.QuasithinUnique.Setup.X3Aut (invC) in
@[expose] def w183fin_conjC (g a : List Nat) : List Nat := cmul (cmul g a) (invC g)

@[expose] def w183fin_oddT (l : List (List Nat)) : Bool :=
  (l.filter w183fin_isInvC).all fun a => l.any fun g => w183fin_order4 (cmul a (w183fin_conjC g a))

section Packed

open CFSG.Permutation.FinPack CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK

private theorem w183fin_ord4_pk {c : List Nat} (hc : IsC c) : w183fin_order4 c = ord4K (pk c) := by
  have hcc := isC_cmul hc hc
  unfold w183fin_order4 ord4K ord4sK
  rw [bne, beq_pk hcc isC_cid, beq_pk (isC_cmul hcc hcc) isC_cid, pk_cmul hcc hcc, pk_cmul hc hc,
    pk_cid]

private theorem w183fin_oddT_pk {L : List (List Nat)} (hL : ∀ c ∈ L, IsC c) {IV : List ℕ}
    (hIV : (L.map pk).filter invTK = IV) : w183fin_oddT L = oddK (L.map pk) IV := by
  unfold w183fin_oddT oddK
  rw [all_filter, allK_sub hIV]
  refine all_pk fun a ha => ?_
  beta_reduce
  rw [w183fin_isInv_pk (hL a ha)]
  congr 1
  refine any_pk fun g hg => ?_
  beta_reduce
  have ha' := hL a ha
  have hg' := hL g hg
  have hga := isC_cmul hg' ha'
  have hi := isC_invC hg'
  unfold w183fin_conjC
  rw [w183fin_ord4_pk (isC_cmul ha' (isC_cmul hga hi)), pk_cmul ha' (isC_cmul hga hi),
    pk_cmul hga hi, pk_cmul hg' ha', pk_invC hg']

theorem w183fin_odd_m10 : w183fin_oddT w183fin_lM10 = true := by
  obtain ⟨hL, hM⟩ := coset_codes isC_tMulFrob m10t_pin
  unfold w183fin_lM10 w183fin_cosetL w183fin_tMulFrobC
  rw [w183fin_oddT_pk hL (IV := ivM10K) (by rw [hM]; exact beq_iff_eq.1 ivM10K_pin), hM]
  exact odd_m10K

theorem w183fin_odd_pgl : w183fin_oddT w183fin_lPGL = true := by
  obtain ⟨hL, hM⟩ := coset_codes isC_tMul pglt_pin
  unfold w183fin_lPGL w183fin_cosetL w183fin_tMulC
  rw [w183fin_oddT_pk hL (IV := ivPGLK) (by rw [hM]; exact beq_iff_eq.1 ivPGLK_pin), hM]
  exact odd_pglK

theorem w183fin_odd_aut : w183fin_oddT autL = true := by
  rw [w183fin_oddT_pk (fun c hc => isC_of_autL hc)
    (IV := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K.invK)
    (by rw [autK_pin]; exact beq_iff_eq.1 invK_pin), autK_pin]
  exact odd_autK

end Packed

theorem w183fin_oddT_sound (B : Subgroup P10) (l : List (List Nat))
    (hl : ∀ x : P10, x ∈ B ↔ code x ∈ l) (hs : ∀ c ∈ l, ∃ x ∈ B, code x = c)
    (h : w183fin_oddT l = true) :
    ∀ a ∈ B, a * a = 1 → a ≠ 1 →
      ∃ g ∈ B, (a * (g * a * g⁻¹)) ^ 2 ≠ 1 ∧ (a * (g * a * g⁻¹)) ^ 4 = 1 := by
  intro a haB ha2 ha1
  have hla : code a ∈ l := (hl a).1 haB
  have hia := (w183fin_code_isInv a).2 ⟨ha2, ha1⟩
  unfold w183fin_oddT at h
  rw [List.all_eq_true] at h
  have h1 := h (code a) (List.mem_filter.2 ⟨hla, hia⟩)
  rw [List.any_eq_true] at h1
  obtain ⟨gc, hgc, ho⟩ := h1
  obtain ⟨g, hgB, rfl⟩ := hs gc hgc
  refine ⟨g, hgB, ?_⟩
  have hc : cmul (code a) (w183fin_conjC (code g) (code a)) = code (a * (g * a * g⁻¹)) := by
    unfold w183fin_conjC
    rw [← CFSG.QuasithinUnique.Setup.X3Aut.code_inv g, ← code_mul, ← code_mul, ← code_mul]
  rw [hc] at ho
  unfold w183fin_order4 at ho
  rw [Bool.and_eq_true] at ho
  obtain ⟨h2, h4⟩ := ho
  generalize a * (g * a * g⁻¹) = x at h2 h4 ⊢
  rw [← code_mul, ← code_one, bne_iff_ne] at h2
  rw [← code_mul, ← code_mul, ← code_one, beq_iff_eq] at h4
  refine ⟨fun h => h2 (by rw [← pow_two, h]), ?_⟩
  have := code_injective h4
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  exact this

end CFSG.LocalAnalysis.WeakClosure81

end
