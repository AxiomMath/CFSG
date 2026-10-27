module

public import CFSG.Quasithin.Background.SmithB42Disp
public import CFSG.Sporadic.Schreier.TitsAutD
public import Certificates.Certificate260140
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

@[expose] def B42TypeTits (X : Type) [Group X] : Prop :=
  ReeTitsModel (X ⧸ Subgroup.center X) .Tits 2 1

namespace B42Tits

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native B42Disp

theorem titsDisp_check :
    titsOrderCheck = true ∧ titsColourCheck = true ∧ titsColourACheck = true :=
  Certificates.certificate260140

theorem rep_titsPowArr {x : Array ℕ} {σ : Equiv.Perm (Fin 1755)} (hx : Rep 1755 x σ) (k : ℕ) :
    Rep 1755 (titsPowArr x k) (σ ^ k) := by
  induction k with
  | zero => simpa [titsPowArr] using (rep_idA (n := 1755))
  | succ k ih => rw [pow_succ']; exact rep_compA hx ih

@[expose] noncomputable def titsW₁ : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsWordT

@[expose] noncomputable def titsW₂ : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsWordZ₂

@[expose] noncomputable def titsW₃ : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsWordZ₃

@[expose] noncomputable def titsCt : Equiv.Perm (Fin 1755) :=
  titsTInv * (titsW₁ * titsTInv * titsW₁⁻¹)

@[expose] noncomputable def titsCz : Equiv.Perm (Fin 1755) :=
  titsZ * (titsW₂ * titsZ * titsW₂⁻¹) * (titsW₃ * titsZ * titsW₃⁻¹)

theorem titsOrder_facts :
    titsCt ^ 13 = 1 ∧ titsCt ≠ 1 ∧ titsCz ^ 13 = 1 ∧ titsCz ≠ 1 := by
  have h := titsDisp_check.1
  simp only [titsOrderCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl1, hl2⟩, hl3⟩, hi1⟩, hi2⟩, hi3⟩, hct1⟩, hct13⟩, hcz1⟩, hcz13⟩ := h
  have rct : Rep 1755 titsCtArr titsCt :=
    rep_compA titsTInv_rep (rep_conjArr (rep_wordArr_titsT hl1) hi1 titsTInv_rep)
  have rcz : Rep 1755 titsCzArr titsCz :=
    rep_compA (rep_compA titsZ_rep (rep_conjArr (rep_wordArr_titsT hl2) hi2 titsZ_rep))
      (rep_conjArr (rep_wordArr_titsT hl3) hi3 titsZ_rep)
  refine ⟨eq_of_eqA (rep_titsPowArr rct 13) rep_idA hct13, fun h1 => ?_,
    eq_of_eqA (rep_titsPowArr rcz 13) rep_idA hcz13, fun h1 => ?_⟩
  · have := (eqA_iff rct rep_idA).2 h1
    rw [hct1] at this
    exact Bool.false_ne_true this
  · have := (eqA_iff rcz rep_idA).2 h1
    rw [hcz1] at this
    exact Bool.false_ne_true this

theorem orderOf_titsCt :
    orderOf titsCt = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact orderOf_eq_prime titsOrder_facts.1 titsOrder_facts.2.1

theorem orderOf_titsCz :
    orderOf titsCz = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact orderOf_eq_prime titsOrder_facts.2.2.1 titsOrder_facts.2.2.2

theorem orderOf_two_zmod_thirteen : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

@[expose] noncomputable def titsInvPerm (i : ℕ) : Equiv.Perm (Fin 1755) :=
  wordIn 13 titsT (titsInvCert[i]!).2 * (if (titsInvCert[i]!).1 then titsZ else titsTInv) *
    (wordIn 13 titsT (titsInvCert[i]!).2)⁻¹

theorem titsInvCert_length : titsInvCert.length = 143 := by
  rfl

theorem titsInvConj_length : titsInvConj.length = 143 := by
  rw [titsInvConj, List.length_map, titsInvCert_length]

theorem titsInvConj_getElem {i : ℕ} (hi : i < 143) :
    titsInvConj[i]! = conjArr (wordArr 1755 titsDerivedArrs (titsInvCert[i]!).2)
      (if (titsInvCert[i]!).1 then titsZArr else titsTArr) := by
  rw [getElem!_pos titsInvConj i (titsInvConj_length ▸ hi),
    getElem!_pos titsInvCert i (titsInvCert_length ▸ hi)]
  simp only [titsInvConj, List.getElem_map]

theorem rep_titsInvConj
    {i : ℕ} (hi : i < 143) :
    Rep 1755 titsInvConj[i]! (titsInvPerm i) := by
  have hmem : titsInvCert[i]! ∈ titsInvCert := by
    rw [getElem!_pos titsInvCert i (titsInvCert_length ▸ hi)]
    exact List.getElem_mem _
  obtain ⟨hl, hinv⟩ := titsInvCert_facts hmem
  rw [titsInvConj_getElem hi, titsInvPerm]
  split_ifs
  · exact rep_conjArr (rep_wordArr_titsT hl) hinv titsZ_rep
  · exact rep_conjArr (rep_wordArr_titsT hl) hinv titsTInv_rep

theorem titsInvPerm_mem (i : ℕ) : titsInvPerm i ∈ titsD := by
  have hw := wordIn_titsT_mem_titsD (titsInvCert[i]!).2
  refine titsD.mul_mem (titsD.mul_mem hw ?_) (titsD.inv_mem hw)
  split_ifs
  · exact titsZ_mem_titsD
  · exact titsTInv_mem_titsD

theorem isConj_titsInvPerm_of_flag {i : ℕ}
    (hf : (titsInvCert[i]!).1 = false) : IsConj titsTD ⟨titsInvPerm i, titsInvPerm_mem i⟩ := by
  refine isConj_iff.2 ⟨⟨_, wordIn_titsT_mem_titsD (titsInvCert[i]!).2⟩, Subtype.ext ?_⟩
  simp only [titsInvPerm, hf, Bool.false_eq_true, ↓reduceIte, Subgroup.coe_mul, Subgroup.coe_inv]
  rfl

theorem exists_titsInvPerm_eq
    {s : Equiv.Perm (Fin 1755)} (hs : s ∈ titsS) (h2 : s * s = 1) (h1 : s ≠ 1) :
    ∃ i < 143, titsInvPerm i = s := by
  have hsQ : s ∈ titsQS.originalSubgroup := by rw [titsQS_facts.2.2.1]; exact hs
  obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.2.1 (by show (finList 1755 titsSBase).length = 5; simp [finList,
      titsCentral_check.1]) titsClass_check.2 hsQ
  rw [(eqA_iff (rep_compA ha ha) rep_idA).2 h2,
    (show eqA 1755 a (idA 1755) = false from Bool.eq_false_iff.2 fun e =>
      h1 (eq_of_eqA ha rep_idA e))] at hp
  simp only [Bool.not_true, Bool.false_or, anyEq, List.any_eq_true] at hp
  obtain ⟨c, hc, hac⟩ := hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  have hi' : i < 143 := titsInvConj_length ▸ hi
  refine ⟨i, hi', ?_⟩
  have hr := rep_titsInvConj hi'
  rw [getElem!_pos titsInvConj i hi] at hr
  exact (eq_of_eqA ha hr hac).symm

theorem titsInvColour_lt {i : ℕ} (hi : i < 143) :
    titsInvColour[i]! < 31 := by
  have h := titsDisp_check.2.1
  simp only [titsColourCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, hlen⟩, hall⟩, -⟩ := h
  rw [getElem!_pos titsInvColour i (hlen ▸ hi)]
  exact hall _ (List.getElem_mem _)

theorem titsInvColourA_lt {i : ℕ} (hi : i < 143) :
    titsInvColourA[i]! < 3 := by
  have h := titsDisp_check.2.2
  simp only [titsColourACheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hall⟩, -⟩ := h
  rw [getElem!_pos titsInvColourA i (hlen ▸ hi)]
  exact hall _ (List.getElem_mem _)

theorem titsInvColour_ne
    {i j : ℕ} (hi : i < 143)
    (hj : j < 143) (hne : titsInvPerm i ≠ titsInvPerm j)
    (hc : titsInvPerm i * titsInvPerm j = titsInvPerm j * titsInvPerm i) :
    titsInvColour[i]! ≠ titsInvColour[j]! := by
  have h := titsDisp_check.2.1
  simp only [titsColourCheck, Bool.and_eq_true] at h
  have h2 := allLt_spec (allLt_spec h.2 hi) hj
  have hij : i ≠ j := fun e => hne (by rw [e])
  have hcomm : commA titsInvConj[i]! titsInvConj[j]! = true :=
    (commA_iff (rep_titsInvConj hi) (rep_titsInvConj hj)).2 hc
  simp only [hcomm, Bool.not_true, Bool.or_false, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 hij
  · exact h2

theorem titsInvColourA_ne
    {i j k : ℕ} (hi : i < 143)
    (hj : j < 143) (hk : k < 143) (hfi : (titsInvCert[i]!).1 = true)
    (hfj : (titsInvCert[j]!).1 = true) (hne : titsInvPerm i ≠ titsInvPerm j)
    (hc : titsInvPerm i * titsInvPerm j = titsInvPerm j * titsInvPerm i)
    (hp : titsInvPerm i * titsInvPerm j = titsInvPerm k) (hcol : titsInvColourA[i]! =
      titsInvColourA[j]!) : (titsInvCert[k]!).1 = false := by
  have h := titsDisp_check.2.2
  simp only [titsColourACheck, Bool.and_eq_true] at h
  have h2 := allLt_spec (allLt_spec h.2 hi) hj
  have hij : i ≠ j := fun e => hne (by rw [e])
  have hcomm : commA titsInvConj[i]! titsInvConj[j]! = true :=
    (commA_iff (rep_titsInvConj hi) (rep_titsInvConj hj)).2 hc
  simp only [hfi, hfj, hcomm, hcol, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.or_false, Bool.or_eq_true, beq_iff_eq, bne_self_eq_false] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 hij
  · have h3 := allLt_spec h2 hk
    have heq : eqA 1755 (compA 1755 titsInvConj[i]! titsInvConj[j]!) titsInvConj[k]! = true :=
      (eqA_iff (rep_compA (rep_titsInvConj hi) (rep_titsInvConj hj)) (rep_titsInvConj hk)).2 hp
    simp only [heq, Bool.not_true, Bool.or_false, Bool.not_eq_true'] at h3
    exact h3

theorem exists_conj_mem_titsS
    (E : Subgroup titsD) (hE : ∀ x ∈ E, x ^ 2 = 1) :
    ∃ g : titsD, ∀ x ∈ E, ((g⁻¹ * x * g : titsD) : Equiv.Perm (Fin 1755)) ∈ titsS := by
  have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE x x.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsD titsSylow P
  refine ⟨g, fun x hx => ?_⟩
  have h1 : x ∈ ((g • titsSylow : Sylow 2 titsD) : Subgroup titsD) := hg ▸ hP hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : g⁻¹ * x * g ∈ (titsSylow : Subgroup titsD) := by
    convert h1 using 1
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [coe_titsSylow, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem conj_facts {x g : titsD} (h2 : x ^ 2 = 1) (h1 : x ≠ 1) :
    ((g⁻¹ * x * g : titsD) : Equiv.Perm (Fin 1755)) * ((g⁻¹ * x * g : titsD) :
      Equiv.Perm (Fin 1755)) = 1 ∧ ((g⁻¹ * x * g : titsD) : Equiv.Perm (Fin 1755)) ≠ 1 := by
  refine ⟨?_, fun h => h1 ?_⟩
  · rw [← Subgroup.coe_mul]
    have : g⁻¹ * x * g * (g⁻¹ * x * g) = 1 := by
      calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [← sq, h2, mul_one, inv_mul_cancel]
    rw [this, Subgroup.coe_one]
  · have h' : g⁻¹ * x * g = 1 := Subtype.ext h
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h', mul_one, mul_inv_cancel]

theorem card_le_of_isElem2
    (E : Subgroup titsD) (hE : IsElem2 E) :
    Nat.card E ≤ 2 ^ 5 := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_mem_titsS E hE.2
  have hidx : ∀ x : E, x ≠ 1 → ∃ i < 143,
      titsInvPerm i = ((g⁻¹ * x * g : titsD) : Equiv.Perm (Fin 1755)) := by
    intro x hx1
    have hx1' : (x : titsD) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨h2, h1⟩ := conj_facts (g := g) (hE.2 x x.2) hx1'
    exact exists_titsInvPerm_eq (hg x x.2) h2 h1
  choose idx hidx_lt hidx_eq using hidx
  let f : E → Option (Fin 31) := fun x =>
    if h : x = 1 then none else some ⟨titsInvColour[idx x h]!, titsInvColour_lt (hidx_lt x h)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = 1 <;> by_cases hy : y = 1
    · rw [hx, hy]
    · simp [f, hx, hy] at hxy
    · simp [f, hx, hy] at hxy
    · simp only [f, hx, hy, dite_false, Option.some.injEq, Fin.mk.injEq] at hxy
      by_contra hne
      have hne' : titsInvPerm (idx x hx) ≠ titsInvPerm (idx y hy) := by
        rw [hidx_eq, hidx_eq]
        intro h
        apply hne
        have h' : g⁻¹ * (x : titsD) * g = g⁻¹ * (y : titsD) * g := Subtype.ext h
        exact Subtype.ext (by simpa using h')
      have hc : titsInvPerm (idx x hx) * titsInvPerm (idx y hy) =
          titsInvPerm (idx y hy) * titsInvPerm (idx x hx) := by
        rw [hidx_eq, hidx_eq, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
        congr 1
        have hxy' := hE.1 x x.2 y y.2
        calc g⁻¹ * (x : titsD) * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
          _ = g⁻¹ * (y * x) * g := by rw [hxy']
          _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
      exact titsInvColour_ne (hidx_lt x hx) (hidx_lt y hy) hne' hc hxy
  calc Nat.card E ≤ Nat.card (Option (Fin 31)) := Nat.card_le_card_of_injective f hf
    _ = 2 ^ 5 := by simp

theorem card_le_of_pure
    (E : Subgroup titsD) (hE : IsElem2 E)
    (hpure : ∀ ξ ∈ E, ξ ≠ 1 → ¬ IsConj titsTD ξ) : Nat.card E ≤ 2 ^ 2 := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_mem_titsS E hE.2
  have hflag : ∀ x : E, x ≠ 1 → ∀ i,
      titsInvPerm i = ((g⁻¹ * x * g : titsD) : Equiv.Perm (Fin 1755)) →
        (titsInvCert[i]!).1 = true := by
    intro x hx1 i hi
    by_contra hf
    rw [Bool.not_eq_true] at hf
    apply hpure x x.2 (fun h => hx1 (Subtype.ext h))
    have h1 := isConj_titsInvPerm_of_flag hf
    have h2 : (⟨titsInvPerm i, titsInvPerm_mem i⟩ : titsD) = g⁻¹ * x * g := Subtype.ext hi
    rw [h2] at h1
    exact h1.trans (isConj_iff.2 ⟨g, by group⟩)
  have hidx : ∀ x : E, x ≠ 1 → ∃ i < 143,
      titsInvPerm i = ((g⁻¹ * x * g : titsD) : Equiv.Perm (Fin 1755)) := by
    intro x hx1
    have hx1' : (x : titsD) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨h2, h1⟩ := conj_facts (g := g) (hE.2 x x.2) hx1'
    exact exists_titsInvPerm_eq (hg x x.2) h2 h1
  choose idx hidx_lt hidx_eq using hidx
  let f : E → Option (Fin 3) := fun x =>
    if h : x = 1 then none else some ⟨titsInvColourA[idx x h]!, titsInvColourA_lt (hidx_lt x h)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = 1 <;> by_cases hy : y = 1
    · rw [hx, hy]
    · simp [f, hx, hy] at hxy
    · simp [f, hx, hy] at hxy
    · simp only [f, hx, hy, dite_false, Option.some.injEq, Fin.mk.injEq] at hxy
      by_contra hne
      have hne' : titsInvPerm (idx x hx) ≠ titsInvPerm (idx y hy) := by
        rw [hidx_eq, hidx_eq]
        intro h
        apply hne
        have h' : g⁻¹ * (x : titsD) * g = g⁻¹ * (y : titsD) * g := Subtype.ext h
        exact Subtype.ext (by simpa using h')
      have hxy' := hE.1 x x.2 y y.2
      have hc : titsInvPerm (idx x hx) * titsInvPerm (idx y hy) =
          titsInvPerm (idx y hy) * titsInvPerm (idx x hx) := by
        rw [hidx_eq, hidx_eq, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
        congr 1
        calc g⁻¹ * (x : titsD) * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
          _ = g⁻¹ * (y * x) * g := by rw [hxy']
          _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
      have hxyE : x * y ≠ 1 := by
        intro h
        apply hne
        have hy2 : (y : titsD) * y = 1 := by rw [← sq]; exact hE.2 y y.2
        have h' : (x : titsD) * y = 1 := congrArg Subtype.val h
        exact Subtype.ext (by
          calc (x : titsD) = x * y * y := by rw [mul_assoc, hy2, mul_one]
            _ = y := by rw [h', one_mul])
      obtain ⟨k, hk, hkeq⟩ := exists_titsInvPerm_eq (hg _ (x * y).2)
        (conj_facts (g := g) (hE.2 _ (x * y).2) (fun h => hxyE (Subtype.ext h))).1
        (conj_facts (g := g) (hE.2 _ (x * y).2) (fun h => hxyE (Subtype.ext h))).2
      have hp : titsInvPerm (idx x hx) * titsInvPerm (idx y hy) = titsInvPerm k := by
        rw [hidx_eq, hidx_eq, hkeq, ← Subgroup.coe_mul]
        congr 1
        simp only [Subgroup.coe_mul]
        group
      have h1 := titsInvColourA_ne (hidx_lt x hx) (hidx_lt y hy) hk
        (hflag x hx _ (hidx_eq x hx)) (hflag y hy _ (hidx_eq y hy)) hne' hc hp hxy
      have h2 := hflag (x * y) hxyE k hkeq
      rw [h1] at h2
      exact Bool.false_ne_true h2
  calc Nat.card E ≤ Nat.card (Option (Fin 3)) := Nat.card_le_card_of_injective f hf
    _ = 2 ^ 2 := by simp

theorem mem_range_conj_of_mul_self
    (α : MulAut titsD) (hα : α * α = 1) :
    α ∈ (MulAut.conj : titsD →* MulAut titsD).range := by
  obtain ⟨a, rfl⟩ := titsConj_surjective α
  have ha2 : a * a = 1 :=
    titsConj_injective (by rw [map_mul, hα, map_one] : titsConj (a * a) = titsConj 1)
  by_cases h1 : (a : Equiv.Perm (Fin 1755)) = 1
  · refine ⟨1, ?_⟩
    rw [show a = 1 from Subtype.ext h1, map_one, map_one]
  · have hord : orderOf (a : Equiv.Perm (Fin 1755)) = 2 := by
      refine orderOf_eq_prime ?_ h1
      rw [sq, ← Subgroup.coe_mul, ha2, Subgroup.coe_one]
    have haD := titsA_involution_mem_D a.2 hord
    refine ⟨⟨a, haD⟩, MulEquiv.ext fun d => Subtype.ext ?_⟩
    rw [coe_titsConj_apply]
    rfl

theorem dispAt_of_isConj_t
    {ξ : titsD} (hξ : IsConj titsTD ξ) : DispAt titsD (MulAut.conj ξ) (2 ^ 5) := by
  obtain ⟨h, rfl⟩ := isConj_iff.1 hξ
  set w : titsD := ⟨titsW₁, wordIn_titsT_mem_titsD _⟩ with hw
  refine dispAt_conj titsD_center (ℓ := 13) (by norm_num) (by norm_num) [1, h * w * h⁻¹] ?_ ?_
  · have hprod : ([1, h * w * h⁻¹].map fun m => m * (h * titsTD * h⁻¹) * m⁻¹).prod =
        MulAut.conj h (titsTD * (w * titsTD * w⁻¹)) := by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, MulAut.conj_apply]
      group
    have hc : orderOf (titsTD * (w * titsTD * w⁻¹)) = 13 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_titsCt
    rw [hprod, MulEquiv.orderOf_eq, hc]
  · rw [orderOf_two_zmod_thirteen]
    norm_num

theorem dispAt_of_isConj_z
    {ξ : titsD} (hξ : IsConj titsZD ξ) : DispAt titsD (MulAut.conj ξ) (2 ^ 2) := by
  obtain ⟨h, rfl⟩ := isConj_iff.1 hξ
  set w₂ : titsD := ⟨titsW₂, wordIn_titsT_mem_titsD _⟩ with hw₂
  set w₃ : titsD := ⟨titsW₃, wordIn_titsT_mem_titsD _⟩ with hw₃
  refine dispAt_conj titsD_center (ℓ := 13) (by norm_num) (by norm_num)
    [1, h * w₂ * h⁻¹, h * w₃ * h⁻¹] ?_ ?_
  · have hprod : ([1, h * w₂ * h⁻¹, h * w₃ * h⁻¹].map
        fun m => m * (h * titsZD * h⁻¹) * m⁻¹).prod =
        MulAut.conj h (titsZD * (w₂ * titsZD * w₂⁻¹) * (w₃ * titsZD * w₃⁻¹)) := by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, MulAut.conj_apply]
      group
    have hc : orderOf (titsZD * (w₂ * titsZD * w₂⁻¹) * (w₃ * titsZD * w₃⁻¹)) = 13 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_titsCz
    rw [hprod, MulEquiv.orderOf_eq, hc]
  · rw [orderOf_two_zmod_thirteen]
    norm_num

theorem titsD_dispCriterion :
    DispCriterion titsD := by
  refine dispCriterion_of_classes titsD_center (fun ξ => IsConj titsTD ξ) 5 2 0
    (fun E hE => card_le_of_isElem2 E hE) (fun E hE hpure => card_le_of_pure E hE hpure)
    ?_ ?_ ?_ ?_
  · intro F hF
    have hle : F ≤ (MulAut.conj : titsD →* MulAut titsD).range := fun α hα =>
      mem_range_conj_of_mul_self α (by rw [← sq]; exact hF.2 α hα)
    rw [inf_of_le_left hle, pow_zero, one_mul]
  · intro ξ _ _ hB
    exact Or.inl (dispAt_of_isConj_t hB)
  · intro α hα hout
    exact absurd (mem_range_conj_of_mul_self α hα) hout
  · intro E hE1 hE hpure
    left
    obtain ⟨⟨ξ, hξE⟩, hξ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
    have hξ1' : ξ ≠ 1 := fun h => hξ1 (Subtype.ext h)
    have h2 : orderOf ξ = 2 := orderOf_eq_prime (hE.2 ξ hξE) hξ1'
    rcases titsD_involution_conj ξ h2 with hz | ht
    · exact ⟨ξ, hξE, hξ1', Or.inl (dispAt_of_isConj_z hz)⟩
    · exact absurd ht (hpure ξ hξE hξ1')

end B42Tits

open B42Tits CFSG.Sporadic.Schreier.Tits in
theorem asB42Tits_holds :
    AsB42NoOffenderFor B42TypeTits :=
  B42Disp.asB42NoOffenderFor_of_dispCriterion fun X _ h =>
    ⟨titsD, inferInstance, titsModelEquiv (X ⧸ Subgroup.center X) 2 1 h, titsD_dispCriterion⟩

theorem asB42ReeF4_of_large
    (hF : AsB42ReeF4Large) : AsB42ReeF4 :=
  AsB42NoOffenderFor.or hF asB42Tits_holds

end CFSG.Quasithin
