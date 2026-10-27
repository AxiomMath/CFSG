module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6OverMax
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFSp8

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.Quasithin.H13.MatNCert Matrix

abbrev GL7 : Type := GL (Fin 7) (ZMod 2)

@[expose] def stab7 : Subgroup GL7 where
  carrier := {g | (g : M7) *ᵥ Pi.single 0 1 = Pi.single 0 1}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_setOf_eq, Units.val_mul, ← Matrix.mulVec_mulVec] at hg hh ⊢
    rw [hh, hg]
  one_mem' := by
    show ((1 : GL7) : M7) *ᵥ _ = _
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    conv_lhs => rw [← hg]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_stab7 {g : GL7} : g ∈ stab7 ↔ (g : M7) *ᵥ Pi.single 0 1 = Pi.single 0 1 := Iff.rfl

@[expose] def piM (A : M7) : M6 := Matrix.of fun i j => A i.succ j.succ

theorem col_zero_of_fix {A : M7} (hA : A *ᵥ Pi.single 0 1 = Pi.single 0 1) (i : Fin 6) :
    A i.succ 0 = 0 := by
  have h := congrFun hA i.succ
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

theorem piM_mul {A : M7} (hA : A *ᵥ Pi.single 0 1 = Pi.single 0 1) (B : M7) :
    piM (A * B) = piM A * piM B := by
  ext i j
  simp only [piM, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_succ (n := 6)]
  rw [col_zero_of_fix hA i, zero_mul, zero_add]

theorem piM_one : piM 1 = 1 := by
  ext i j
  simp [piM, Matrix.one_apply]

@[expose] noncomputable def piHom : ↥stab7 →* GL6 :=
  MonoidHom.toHomUnits
    { toFun := fun g => piM ((g : GL7) : M7)
      map_one' := by simp [piM_one]
      map_mul' := fun g h => by
        simp only [Subgroup.coe_mul, Units.val_mul]
        exact piM_mul g.2 _ }

theorem coe_piHom (g : ↥stab7) : ((piHom g : GL6) : M6) = piM ((g : GL7) : M7) := rfl

theorem getD_piC (x : List ℕ) (j : ℕ) : (piC x).getD j 0 = x.getD (j + 1) 0 / 2 := by
  rw [piC, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_drop, add_comm 1 j]
  cases x[j + 1]? <;> rfl

theorem piM_decN (x : List ℕ) : piM (decN 7 x) = decN 6 (piC x) := by
  ext i j
  simp only [piM, decN, Matrix.of_apply, vecN, Fin.val_succ, getD_piC, Nat.testBit_succ]

theorem validN_piC {x : List ℕ} (hx : ValidN 7 x) : ValidN 6 (piC x) := by
  refine ⟨by simp [piC, hx.1], fun c hc => ?_⟩
  simp only [piC, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  have := hx.2 c' (List.mem_of_mem_drop hc')
  simp only [Nat.reducePow] at this ⊢
  omega

theorem colsN_piHom (g : ↥stab7) :
    colsN ((piHom g : GL6) : M6) = piC (colsN ((g : GL7) : M7)) := by
  rw [coe_piHom, ← decN_colsN ((g : GL7) : M7), piM_decN, decN_colsN,
    colsN_decN (validN_piC (validN_colsN _))]

theorem exists_kC {g : ↥stab7} (h : piHom g = 1) : ∃ m < 64,
    colsN ((g : GL7) : M7) = kC m := by
  have hv := validN_colsN ((g : GL7) : M7)
  have hp : piC (colsN ((g : GL7) : M7)) = oneN 6 := by
    rw [← colsN_piHom, h, Units.val_one, colsN_one]
  have h0 : (colsN ((g : GL7) : M7)).getD 0 0 = 1 := by
    have e := g.2
    rw [mem_stab7, ← decN_colsN ((g : GL7) : M7), ← vecN_one, decN_mulVec hv.1] at e
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, hx⟩ := list_eq_seven hv.1
    rw [hx] at e ⊢
    have l0 : x0 < 128 := hv.2 x0 (by rw [hx]; simp)
    have e' : vecN 7 x0 = vecN 7 1 := by simpa [mvN] using e
    exact vecN_inj (n := 7) (by simpa using l0) (by norm_num) e'
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, hx⟩ := list_eq_seven hv.1
  have hlt : ∀ c ∈ colsN ((g : GL7) : M7), c < 128 := hv.2
  rw [hx] at hp h0 hlt
  simp only [piC, List.drop_succ_cons, List.drop_zero, List.map_cons, List.map_nil, oneN,
    List.range_succ, List.range_zero, List.map_append, List.map_cons, List.nil_append,
    List.cons_append, List.cons.injEq] at hp
  simp only [List.getD_cons_zero] at h0
  obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := hp
  have l : ∀ c ∈ [x0, x1, x2, x3, x4, x5, x6], c < 128 := hlt
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at l
  obtain ⟨-, l1, l2, l3, l4, l5, l6⟩ := l
  refine ⟨x1 % 2 + 2 * (x2 % 2) + 4 * (x3 % 2) + 8 * (x4 % 2) + 16 * (x5 % 2) + 32 * (x6 % 2),
    by omega, ?_⟩
  rw [hx, kC]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq]
  norm_num at e1 e2 e3 e4 e5 e6 ⊢
  omega

section Case


theorem case_parts {x : List ℕ} (hx : x = xSc ∨ x = xIc) :
    (∀ m, 0 < m → m < 64 → ∃ s ∈ genSubN 7 [nGc, nHc, x],
      decN 7 (kC m) = ((s : GL7) : M7) * decN 7 (kC 1) * ((s⁻¹ : GL7) : M7)) ∧
    ((List.range 128).filter fun v => mvN (bbarC x) v == v).length = 32 ∧
    (∀ g ∈ rGens x, mulN g (bbarC x) = mulN (bbarC x) g) ∧
    (∀ m ∈ [6, 8, 17, 33], mulN (kC m) (kC m) = oneN 7) ∧
    Nat.card (genSubN 7 (rGens x)) = 32 :=
  cert899108_parts.2.2.1 x hx

theorem genSubN_le_range {σ : H6 →* GL7} (hg : ((σ gamH : GL7) : M7) = decN 7 nGc)
    (hh : ((σ hH : GL7) : M7) = decN 7 nHc) {x : List ℕ}
    (hc : ((σ cH : GL7) : M7) = decN 7 x) : genSubN 7 [nGc, nHc, x] ≤ σ.range := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  have hu' : colsN (u : M7) ∈ [nGc, nHc, x] := hu
  have hdec : (u : M7) = decN 7 (colsN (u : M7)) := (decN_colsN _).symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
  rcases hu' with e | e | e
  · rw [e, ← hg] at hdec
    rw [SetLike.mem_coe, Units.ext hdec]
    exact ⟨gamH, rfl⟩
  · rw [e, ← hh] at hdec
    rw [SetLike.mem_coe, Units.ext hdec]
    exact ⟨hH, rfl⟩
  · rw [e, ← hc] at hdec
    rw [SetLike.mem_coe, Units.ext hdec]
    exact ⟨cH, rfl⟩

theorem mem_of_K {σ : H6 →* GL7} (hg : ((σ gamH : GL7) : M7) = decN 7 nGc)
    (hh : ((σ hH : GL7) : M7) = decN 7 nHc) {x : List ℕ} (hx : x = xSc ∨ x = xIc)
    (hc : ((σ cH : GL7) : M7) = decN 7 x) {Y : Subgroup GL7} (hSY : σ.range ≤ Y)
    {y₀ : GL7} (hy₀ : y₀ ∈ Y) {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀' : m₀ < 64)
    (hy₀m : colsN (y₀ : M7) = kC m₀) {m : ℕ} (hm : 0 < m) (hm' : m < 64) :
    ∃ u ∈ Y, (u : M7) = decN 7 (kC m) := by
  have hle := genSubN_le_range hg hh hc
  obtain ⟨s₀, hs₀', e₀⟩ := (case_parts hx).1 m₀ hm₀ hm₀'
  obtain ⟨s, hs', e⟩ := (case_parts hx).1 m hm hm'
  have hs₀ := hle hs₀'
  have hs := hle hs'
  rw [← hy₀m, decN_colsN] at e₀
  refine ⟨(s * s₀⁻¹) * y₀ * (s * s₀⁻¹)⁻¹, mul_mem (mul_mem (mul_mem (hSY hs) (inv_mem (hSY hs₀)))
    hy₀) (inv_mem (mul_mem (hSY hs) (inv_mem (hSY hs₀)))), ?_⟩
  have h1 : ((s₀⁻¹ : GL7) : M7) * (s₀ : M7) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ (A B C D K : M7), B * A = 1 → C * B * (A * K * B) * (A * D) = C * K * D := by
    intro A B C D K hBA
    calc C * B * (A * K * B) * (A * D) = C * (B * A) * K * (B * A) * D := by
          simp only [Matrix.mul_assoc]
      _ = C * K * D := by rw [hBA, Matrix.mul_one, Matrix.mul_one]
  rw [e]
  simp only [Units.val_mul, _root_.mul_inv_rev, inv_inv, e₀]
  exact key _ _ _ _ _ h1

end Case

section Over


theorem validN_of_case {x : List ℕ} (hx : x = xSc ∨ x = xIc) : ValidN 7 x := by
  rcases hx with rfl | rfl
  exacts [validN_xSc, validN_xIc]

theorem dvd_of_K {σ : H6 →* GL7} (hg : ((σ gamH : GL7) : M7) = decN 7 nGc)
    (hh : ((σ hH : GL7) : M7) = decN 7 nHc) {x : List ℕ} (hx : x = xSc ∨ x = xIc)
    (hc : ((σ cH : GL7) : M7) = decN 7 x) {Y : Subgroup GL7} (hSY : σ.range ≤ Y)
    {y₀ : GL7} (hy₀ : y₀ ∈ Y) {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀' : m₀ < 64)
    (hy₀m : colsN (y₀ : M7) = kC m₀) :
    32 ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer {σ (wordH wZ1)}) := by
  have hxv := validN_of_case hx
  obtain ⟨-, -, hcomm, -, hcard⟩ := case_parts hx
  have hb : colsN ((σ (wordH wZ1) : GL7) : M7) = bbarC x :=
    colsN_wordH σ validN_nGc validN_nHc hxv hg hh hc wZ1
  have hp : colsN ((σ (wordH wP1) : GL7) : M7) = evalW 7 [nGc, nHc, x] wP1 :=
    colsN_wordH σ validN_nGc validN_nHc hxv hg hh hc wP1
  have hkm : ∀ m ∈ [6, 8, 17, 33], ∃ u ∈ Y, (u : M7) = decN 7 (kC m) := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact mem_of_K hg hh hx hc hSY hy₀ hm₀ hm₀' hy₀m (by omega) (by omega)
  have hgen : ∀ g ∈ rGens x, ∃ u ∈ Y, (u : M7) = decN 7 g := by
    intro g hg'
    simp only [rGens, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl | rfl
    · exact hkm 6 (by simp)
    · exact hkm 8 (by simp)
    · exact hkm 17 (by simp)
    · exact hkm 33 (by simp)
    · exact ⟨σ (wordH wP1), hSY ⟨_, rfl⟩, by rw [← hp, decN_colsN]⟩
  have hRY : genSubN 7 (rGens x) ≤ Y := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    have hu' : colsN (u : M7) ∈ rGens x := hu
    obtain ⟨v, hv, hv'⟩ := hgen _ hu'
    have : u = v := Units.ext ((decN_colsN (u : M7)).symm.trans hv'.symm)
    rw [SetLike.mem_coe, this]
    exact hv
  have hRC : genSubN 7 (rGens x) ≤ Subgroup.centralizer {σ (wordH wZ1)} := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    have hu' : colsN (u : M7) ∈ rGens x := hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    refine eq_of_colsN_eq ?_
    rw [Units.val_mul, Units.val_mul, colsN_mul, colsN_mul, hb]
    exact hcomm _ hu'
  rw [← hcard]
  exact Subgroup.card_dvd_of_le (le_inf hRY hRC)

theorem uChk_parts : piC xIc = piC xSc ∧
    (∀ u ∈ uGens, mulN u u = oneN 6 ∧ mulN u pibbarC = mulN pibbarC u) ∧
    Nat.card (genSubN 6 uGens) = 32 :=
  cert899108_parts.2.2.2.1

theorem card_U : Nat.card (genSubN 6 uGens) = 32 := uChk_parts.2.2

theorem U_le_centralizer {pb : GL6} (hpb : colsN (pb : M6) = pibbarC) :
    genSubN 6 uGens ≤ Subgroup.centralizer {pb} := by
  obtain ⟨-, hinv, -⟩ := uChk_parts
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  have hu' : colsN (u : M6) ∈ uGens := hu
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  refine eq_of_colsN_eq ?_
  rw [Units.val_mul, Units.val_mul, colsN_mul, colsN_mul, hpb]
  exact (hinv _ hu').2


theorem injective_of_ne {G : Type*} [Group G] (f : H6 →* G) (hf : f gamH ≠ 1) :
    Function.Injective f := by
  haveI : IsSimpleGroup H6 := CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8.isSimpleGroup_H6
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact h
  · exact absurd (h ▸ Subgroup.mem_top gamH : gamH ∈ f.ker) hf

theorem dvd_or_eq_of_inj {σ : H6 →* GL7} (hg : ((σ gamH : GL7) : M7) = decN 7 nGc)
    (hh : ((σ hH : GL7) : M7) = decN 7 nHc) {x : List ℕ} (hx : x = xSc ∨ x = xIc)
    (hc : ((σ cH : GL7) : M7) = decN 7 x) {Y : Subgroup GL7} (hSY : σ.range ≤ Y)
    (hY : Y ≤ stab7) (hinj : ∀ y : ↥stab7, (y : GL7) ∈ Y → piHom y = 1 → y = 1) :
    Y = σ.range ∨ 32 ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer {σ (wordH wZ1)}) := by
  have hxv := validN_of_case hx
  obtain ⟨hpx, -, -⟩ := uChk_parts
  set σ₁ : H6 →* ↥stab7 := σ.codRestrict stab7 fun g => hY (hSY ⟨g, rfl⟩)
  have hσ₁v : ∀ g, ((σ₁ g : ↥stab7) : GL7) = σ g := fun _ => rfl
  set τ : H6 →* GL6 := piHom.comp σ₁ with hτ
  have hτc : ∀ (g : H6) (c : List ℕ), ((σ g : GL7) : M7) = decN 7 c → ValidN 7 c →
      ((τ g : GL6) : M6) = decN 6 (piC c) := by
    intro g c hgc hcv
    rw [← decN_colsN ((τ g : GL6) : M6)]
    congr 1
    rw [hτ, MonoidHom.comp_apply, colsN_piHom, hσ₁v, hgc, colsN_decN hcv]
  have hτg := hτc gamH nGc hg validN_nGc
  have hτh := hτc hH nHc hh validN_nHc
  have hτx : ((τ cH : GL6) : M6) = decN 6 (piC xSc) := by
    rw [hτc cH x hc hxv]
    rcases hx with rfl | rfl
    · rfl
    · rw [hpx]
  have hsbv : ∀ g ∈ sbGens, ValidN 6 g := validN_sbGens
  have hv1 : ValidN 6 (piC nGc) := hsbv _ (by simp [sbGens])
  have hv2 : ValidN 6 (piC nHc) := hsbv _ (by simp [sbGens])
  have hv3 : ValidN 6 (piC xSc) := hsbv _ (by simp [sbGens])
  have hτS : τ.range ≤ Sbar := by
    rw [MonoidHom.range_eq_map, ← closure_gens_eq_top, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg', rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
    refine Subgroup.subset_closure ?_
    show colsN ((τ g : GL6) : M6) ∈ sbGens
    rcases hg' with rfl | rfl | rfl
    · rw [hτg, colsN_decN hv1]; simp [sbGens]
    · rw [hτh, colsN_decN hv2]; simp [sbGens]
    · rw [hτx, colsN_decN hv3]; simp [sbGens]
  have hτinj : Function.Injective τ := by
    refine injective_of_ne τ fun e => ?_
    have e' := congrArg (fun u : GL6 => colsN (u : M6)) e
    simp only [hτg, colsN_decN hv1, Units.val_one, colsN_one] at e'
    exact absurd e' (by decide)
  have hσinj : Function.Injective σ := by
    refine injective_of_ne σ fun e => ?_
    have e' := congrArg (fun u : GL7 => colsN (u : M7)) e
    simp only [hg, colsN_decN validN_nGc, Units.val_one, colsN_one] at e'
    exact absurd e' (by decide)
  have hcardS : 1451520 ≤ Nat.card Sbar := by
    rw [← card_H6]
    exact Nat.card_le_card_of_injective (fun g => (⟨τ g, hτS ⟨g, rfl⟩⟩ : Sbar))
      fun a b e => hτinj (congrArg Subtype.val e)
  obtain ⟨hSbar, -, -⟩ := stabilizer_eq hcardS
  have hcardσ : Nat.card σ.range = 1451520 := by
    rw [← card_H6, ← Nat.card_congr (MonoidHom.ofInjective hσinj).toEquiv]
  set Y₁ := Y.subgroupOf stab7 with hY₁
  have hinj₁ : ∀ a ∈ Y₁, ∀ b ∈ Y₁, piHom a = piHom b → a = b := by
    intro a ha b hb e
    have h1 := hinj (a * b⁻¹) (Y.mul_mem ha (Y.inv_mem hb)) (by rw [map_mul, map_inv, e,
      mul_inv_cancel])
    rwa [mul_inv_eq_one] at h1
  set Z := Y₁.map piHom with hZ
  have hSZ : Sbar ≤ Z := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    have hu' : colsN (u : M6) ∈ sbGens := hu
    have hmem : ∀ g : H6, τ g ∈ Z := fun g => ⟨σ₁ g, (hSY ⟨g, rfl⟩ : σ g ∈ Y), rfl⟩
    simp only [sbGens, List.mem_cons, List.not_mem_nil, or_false] at hu'
    rcases hu' with hu' | hu' | hu'
    · rw [eq_of_colsN_eq (by rw [hu', hτg, colsN_decN hv1] : colsN (u : M6) =
        colsN ((τ gamH : GL6) : M6))]
      exact hmem _
    · rw [eq_of_colsN_eq (by rw [hu', hτh, colsN_decN hv2] : colsN (u : M6) =
        colsN ((τ hH : GL6) : M6))]
      exact hmem _
    · rw [eq_of_colsN_eq (by rw [hu', hτx, colsN_decN hv3] : colsN (u : M6) =
        colsN ((τ cH : GL6) : M6))]
      exact hmem _
  have hcardY : Nat.card Y = Nat.card Z := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv, hZ]
    refine (Nat.card_image_of_injOn fun a ha b hb e => hinj₁ a ha b hb e).symm
  rcases sbar_max hcardS hSZ with hZS | hZT
  ·
    left
    refine (Subgroup.eq_of_le_of_card_ge hSY ?_).symm
    rw [hcardY, hZS, hSbar, hcardσ]
  ·
    right
    set β₁ := σ₁ (wordH wZ1)
    have hpb : colsN ((piHom β₁ : GL6) : M6) = pibbarC :=
      colsN_wordH τ hv1 hv2 hv3 hτg hτh hτx wZ1
    have hβY : β₁ ∈ Y₁ := (hSY ⟨_, rfl⟩ : σ (wordH wZ1) ∈ Y)
    set U' : Subgroup ↥stab7 := (genSubN 6 uGens).comap piHom ⊓ Y₁ with hU'
    have hU'card : Nat.card U' = 32 := by
      rw [← card_U]
      refine Nat.card_eq_of_bijective (fun y : U' => (⟨piHom y, y.2.1⟩ : genSubN 6 uGens))
        ⟨fun a b e => Subtype.ext (hinj₁ _ a.2.2 _ b.2.2 (congrArg Subtype.val e)), ?_⟩
      intro u
      have hu : (u : GL6) ∈ Z := hZT ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyu⟩ := hu
      refine ⟨⟨y, Subgroup.mem_inf.mpr ⟨?_, hy⟩⟩, Subtype.ext hyu⟩
      show piHom y ∈ genSubN 6 uGens
      rw [hyu]
      exact u.2
    have hle : U'.map stab7.subtype ≤ Y ⊓ Subgroup.centralizer {σ (wordH wZ1)} := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ U' := hy
      have hyU : piHom y ∈ genSubN 6 uGens := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hy').1
      have hyY : y ∈ Y₁ := (Subgroup.mem_inf.mp hy').2
      refine Subgroup.mem_inf.mpr ⟨hyY, ?_⟩
      show (y : GL7) ∈ Subgroup.centralizer {σ (wordH wZ1)}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc' : piHom y * piHom β₁ = piHom β₁ * piHom y :=
        Subgroup.mem_centralizer_singleton_iff.mp (U_le_centralizer hpb hyU)
      have := hinj₁ (y * β₁) (Y₁.mul_mem hyY hβY) (β₁ * y) (Y₁.mul_mem hβY hyY)
        (by rw [map_mul, map_mul, hc'])
      have e := congrArg (fun z : ↥stab7 => (z : GL7)) this
      simpa [β₁, hσ₁v] using e
    rw [← hU'card, ← Subgroup.card_map_of_injective stab7.subtype_injective]
    exact Subgroup.card_dvd_of_le hle

theorem overgroup {σ : H6 →* GL7} (hg : ((σ gamH : GL7) : M7) = decN 7 nGc)
    (hh : ((σ hH : GL7) : M7) = decN 7 nHc)
    (hc : ((σ cH : GL7) : M7) = decN 7 xSc ∨ ((σ cH : GL7) : M7) = decN 7 xIc)
    {Y : Subgroup GL7} (hSY : σ.range ≤ Y) (hY : Y ≤ stab7) :
    Y = σ.range ∨ 32 ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer {σ (wordH wZ1)}) := by
  obtain ⟨x, hx, hcx⟩ : ∃ x, (x = xSc ∨ x = xIc) ∧ ((σ cH : GL7) : M7) = decN 7 x := by
    rcases hc with h | h
    exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr rfl, h⟩]
  by_cases hK : ∃ y : ↥stab7, (y : GL7) ∈ Y ∧ piHom y = 1 ∧ y ≠ 1
  · obtain ⟨y, hyY, hy1, hy⟩ := hK
    obtain ⟨m, hm, hym⟩ := exists_kC hy1
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · exfalso
        apply hy
        apply Subtype.ext
        refine eq_of_colsN_eq ?_
        rw [hym, Subgroup.coe_one, Units.val_one, colsN_one]
        decide
      · exact h
    exact Or.inr (dvd_of_K hg hh hx hcx hSY hyY hm0 hm hym)
  · push Not at hK
    exact dvd_or_eq_of_inj hg hh hx hcx hSY hY fun y hy h1 => by
      by_contra hne
      exact hne (hK y hy h1)

end Over

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over
