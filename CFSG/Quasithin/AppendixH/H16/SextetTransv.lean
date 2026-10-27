module

public import CFSG.Quasithin.AppendixH.H16.TranspAxis
public import CFSG.Quasithin.AppendixH.H16.SextetV10
public import CFSG.Quasithin.AppendixH.H16.SextetData2

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Open

@[expose] noncomputable def ksRho (i : ℕ) : MulAut W11 := rhoCd (ks6_autPerm i)

@[expose] noncomputable def gJ (J : ℕ) : MulAut W11 :=
  (List.range 6).foldl (fun a j => if J.testBit j then a * ksRho j else a) 1

set_option backward.isDefEq.respectTransparency false

private noncomputable def gJAut (J : ℕ) (l : List ℕ) (a : @MulAut W11 Multiplicative.mul) :
    @MulAut W11 Multiplicative.mul :=
  l.foldl (fun a j => if J.testBit j then a * ksRho j else a) a

private def gJCtr (J : ℕ) (l : List ℕ) (c : ℕ) : ℕ :=
  l.foldl (fun c j => if J.testBit j then c ^^^ ctr j else c) c

theorem ksRho_mem {i : ℕ} (hi : i < 6) : ksRho i ∈ imgCd sxKS :=
  rhoCd_mem_imgCd (ks6_autPerm i) (ks6_mem_KS ⟨i, hi⟩)

private theorem fold_mem (J : ℕ) (l : List ℕ) (hl : ∀ j ∈ l, j < 6) (a : MulAut W11)
    (ha : a ∈ imgCd sxKS) : gJAut J l a ∈ imgCd sxKS := by
  induction l generalizing a with
  | nil => exact ha
  | cons j l ih =>
    change gJAut J l (if J.testBit j then a * ksRho j else a) ∈ imgCd sxKS
    split_ifs with hJ
    · exact ih (fun k hk => hl k (List.mem_cons_of_mem j hk)) (a * ksRho j)
        (Subgroup.mul_mem _ ha (ksRho_mem (hl j (List.mem_cons_self ..))))
    · exact ih (fun k hk => hl k (List.mem_cons_of_mem j hk)) a ha

theorem gJ_mem (J : ℕ) : gJ J ∈ imgCd sxKS := by
  simpa [gJ, gJAut] using
    fold_mem J (List.range 6) (fun j hj => List.mem_range.1 hj) 1 (Subgroup.one_mem _)

private theorem foldl_const {M : Type*} (l : List ℕ) (a : M) :
    l.foldl (fun a _ => a) a = a := by
  induction l generalizing a with
  | nil => rfl
  | cons j l ih => simp [List.foldl_cons, ih]

theorem gJ_zero : gJ 0 = 1 := by
  simp only [gJ, Nat.zero_testBit, if_false]
  exact foldl_const (List.range 6) (1 : MulAut W11)

theorem isTranspAxis_ksRho {i : ℕ} (hi : i < 6) :
    IsTranspAxis (ksRho i) US V10 (toW 11 (ctr i)) := by
  constructor
  · intro x hx
    obtain ⟨m, hm, hpar, rfl⟩ := (mem_V10_iff x).1 hx
    change rhoCd (ks6_autPerm i) (toW 11 m) * (toW 11 m)⁻¹ ∈ US
    rw [actsBy_ks6 hi m, CFSG.Quasithin.H.Coc.toW_inv_self, ← toW_xor]
    exact (toW_mem_US_iff (Nat.xor_lt_two_pow (actM_lt (ksC6_lt i hi) m) hm)).2
      ((ks6_transv i hi m hm).1 hpar)
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
    have hpar : popPar 11 (m &&& 1192) = true := by
      cases h : popPar 11 (m &&& 1192)
      · exact absurd ((toW_mem_V10_iff hm).2 h) hx
      · rfl
    have hb : actM (ksC6 i) m ^^^ m ^^^ ctr i < 2 ^ 11 :=
      Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (actM_lt (ksC6_lt i hi) m) hm) (ctr_lt i hi)
    have hmem : actM (ksC6 i) m ^^^ m ^^^ ctr i ∈ uSMasks := (ks6_transv i hi m hm).2 hpar
    have hgoal : toW 11 (actM (ksC6 i) m ^^^ m ^^^ ctr i) ∈ US := (toW_mem_US_iff hb).2 hmem
    simpa [ksRho, actsBy_ks6 hi m, CFSG.Quasithin.H.Coc.toW_inv_self, toW_xor] using hgoal

private theorem fold_isTranspAxis (J : ℕ) :
    ∀ (l : List ℕ), (∀ j ∈ l, j < 6) → ∀ (a : @MulAut W11 Multiplicative.mul) (c : ℕ),
      IsTranspAxis a US V10 (toW 11 c) → toW 11 c ∈ V10 →
      IsTranspAxis (gJAut J l a) US V10 (toW 11 (gJCtr J l c)) ∧
      toW 11 (gJCtr J l c) ∈ V10 := by
  intro l
  induction l with
  | nil => intro _ a c ha hc; exact ⟨ha, hc⟩
  | cons j l ih =>
    intro hl a c ha hc
    change IsTranspAxis (gJAut J l (if J.testBit j then a * ksRho j else a)) US V10
        (toW 11 (gJCtr J l (if J.testBit j then c ^^^ ctr j else c))) ∧
      toW 11 (gJCtr J l (if J.testBit j then c ^^^ ctr j else c)) ∈ V10
    split_ifs with hJ
    · have hj : j < 6 := hl j (List.mem_cons_self ..)
      have hctrj : toW 11 (ctr j) ∈ V10 :=
        (toW_mem_V10_iff (ctr_lt j hj)).2 (ctr_par j hj)
      have hmul : IsTranspAxis (a * ksRho j) US V10 (toW 11 c * toW 11 (ctr j)) :=
        isTranspAxis_mul US_le_V10 hctrj ha (isTranspAxis_ksRho hj)
      rw [← toW_xor] at hmul
      have hmem : toW 11 (c ^^^ ctr j) ∈ V10 := by
        rw [toW_xor]; exact V10.mul_mem hc hctrj
      exact ih (fun k hk => hl k (List.mem_cons_of_mem j hk)) (a * ksRho j) (c ^^^ ctr j)
        hmul hmem
    · exact ih (fun k hk => hl k (List.mem_cons_of_mem j hk)) a c ha hc

theorem isTranspAxis_gJ (J : ℕ) : IsTranspAxis (gJ J) US V10 (toW 11 (xorCtr J)) := by
  have h := (fold_isTranspAxis J (List.range 6) (fun j hj => List.mem_range.1 hj) 1 0
    (by simpa [toW_zero] using isTranspAxis_one US V10)
    (by simpa [toW_zero] using V10.one_mem)).1
  simpa [gJ, xorCtr, gJAut, gJCtr] using h

theorem gJ_injOn : ∀ J < 64, ∀ J' < 64, gJ J = gJ J' → J = J' := by
  intro J hJ J' hJ' h
  have hx : (toW 11 8 : W11) ∉ V10 := by
    rw [toW_mem_V10_iff (by norm_num : 8 < 2 ^ 11), par_eight]
    simp
  have h1 : IsTranspAxis (gJ J) US V10 (toW 11 (xorCtr J)) := isTranspAxis_gJ J
  have h2 : IsTranspAxis (gJ J) US V10 (toW 11 (xorCtr J')) := by
    rw [h]; exact isTranspAxis_gJ J'
  have hc := isTranspAxis_center_unique hx h1 h2
  have hbound : xorCtr J ^^^ xorCtr J' < 2 ^ 11 :=
    Nat.xor_lt_two_pow (xorCtr_lt J hJ) (xorCtr_lt J' hJ')
  have hmem : xorCtr J ^^^ xorCtr J' ∈ uSMasks :=
    (toW_mem_US_iff hbound).1
      (by simpa [toW_xor, CFSG.Quasithin.H.Coc.toW_inv_self] using hc)
  exact xorCtr_inj J hJ J' hJ' hmem

theorem exists_gJ_eq :
    ∀ g ∈ imgCd sxKS, ∃ J < 64, g = gJ J := by
  haveI : Finite (MulAut W11) := CFSG.Quasithin.H.ZTrans.finite_mulAut_z (V := W11)
  let f : Fin 64 → ↥(imgCd sxKS) := fun J => ⟨gJ J, gJ_mem J⟩
  have hf : Function.Injective f := by
    intro J J' h
    exact Fin.ext (gJ_injOn J.1 J.2 J'.1 J'.2 (congrArg Subtype.val h))
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le
      (le_of_eq (by rw [Nat.card_fin, card_imgCd_sxKS]))
  intro g hg
  obtain ⟨J, hJ⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨J.1, J.2, (congrArg Subtype.val hJ).symm⟩

theorem fullTranspAxis_imgCd_sxGen :
    FullTranspAxis (imgCd sxGen) (imgCd sxKS) US V10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨J, hJ, rfl⟩ := exists_gJ_eq g hg
    exact ⟨toW 11 (xorCtr J), (toW_mem_V10_iff (xorCtr_lt J hJ)).2 (xorCtr_par J hJ),
      isTranspAxis_gJ J⟩
  · intro c hc
    obtain ⟨m, hm, hpar, rfl⟩ := (mem_V10_iff c).1 hc
    obtain ⟨J, hJ, hJmem⟩ := ctr_span m hm hpar
    refine ⟨gJ J, gJ_mem J, ?_⟩
    refine isTranspAxis_congr_center (isTranspAxis_gJ J) ?_
    have hb : m ^^^ xorCtr J < 2 ^ 11 := Nat.xor_lt_two_pow hm (xorCtr_lt J hJ)
    have h : toW 11 (m ^^^ xorCtr J) ∈ US := (toW_mem_US_iff hb).2 hJmem
    simpa [toW_xor, CFSG.Quasithin.H.Coc.toW_inv_self] using h
  · intro g hg hgtriv
    obtain ⟨J, hJ, rfl⟩ := exists_gJ_eq g hg
    have hx : (toW 11 8 : W11) ∉ V10 := by
      rw [toW_mem_V10_iff (by norm_num : 8 < 2 ^ 11), par_eight]
      simp
    set a : W11 := gJ J (toW 11 8) * (toW 11 8)⁻¹ with ha
    have h1 : a ∈ US := hgtriv _
    have h2 : a * (toW 11 (xorCtr J))⁻¹ ∈ US := (isTranspAxis_gJ J).2 _ hx
    have hc : (toW 11 (xorCtr J))⁻¹ ∈ US := by
      have h := US.mul_mem (US.inv_mem h1) h2
      have heq : a⁻¹ * (a * (toW 11 (xorCtr J))⁻¹) = (toW 11 (xorCtr J))⁻¹ := by
        rw [← mul_assoc, inv_mul_cancel, one_mul]
      rwa [heq] at h
    have hcmem : toW 11 (xorCtr J) ∈ US := by simpa [inv_inv] using US.inv_mem hc
    have hJm : xorCtr J ∈ uSMasks := (toW_mem_US_iff (xorCtr_lt J hJ)).1 hcmem
    have hJ0 : J = 0 :=
      xorCtr_inj J hJ 0 (by norm_num) (by rwa [xorCtr_zero, Nat.xor_zero])
    rw [hJ0, gJ_zero]
  · intro h hh g hg c hgtrans
    refine isTranspAxis_conj (fun u hu => ?_) (fun x => ?_) hgtrans
    · exact isActsInv_US (fun v => h v) ⟨h, hh, rfl⟩ u hu
    · constructor
      · intro hx
        exact isActsInv_V10 (fun v => h v) ⟨h, hh, rfl⟩ x hx
      · intro hx
        have hhinv : h⁻¹ ∈ imgCd sxGen := Subgroup.inv_mem _ hh
        have h' := isActsInv_V10 (fun v => h⁻¹ v) ⟨h⁻¹, hhinv, rfl⟩ (h x) hx
        simpa using h'

end CFSG.ASVolI.H16
