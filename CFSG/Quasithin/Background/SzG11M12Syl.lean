module

public import CFSG.Quasithin.Background.SzG11M12Data
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.Quasithin.G11.SzG11S

namespace M12Syl

open CFSG.Blueprint CFSG.Sporadic.Mathieu M12Data
open scoped IsMulCommutative

@[expose] def tbl (σ : Equiv.Perm (Fin 12)) : List ℕ := List.ofFn fun i : Fin 12 => (σ i : ℕ)

theorem tbl_length (σ : Equiv.Perm (Fin 12)) : (tbl σ).length = 12 := by simp [tbl]

theorem tbl_lt (σ : Equiv.Perm (Fin 12)) : ∀ x ∈ tbl σ, x < 12 := by
  intro x hx
  simp only [tbl, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact (σ i).isLt

theorem tbl_getD (σ : Equiv.Perm (Fin 12)) (i : Fin 12) : (tbl σ).getD i 0 = (σ i : ℕ) := by
  have h : (i : ℕ) < (tbl σ).length := by rw [tbl_length]; exact i.isLt
  rw [List.getD_eq_getElem _ _ h]
  simp only [tbl, List.getElem_ofFn]

theorem tbl_mul (σ τ : Equiv.Perm (Fin 12)) : tbl (σ * τ) = tmul (tbl σ) (tbl τ) := by
  have h : tbl τ = List.ofFn fun i : Fin 12 => (τ i : ℕ) := rfl
  simp only [tmul]
  rw [h, List.map_ofFn]
  show List.ofFn _ = List.ofFn _
  congr 1
  funext i
  simp only [Function.comp, Equiv.Perm.mul_apply]
  exact (tbl_getD σ (τ i)).symm

theorem tbl_one : tbl (1 : Equiv.Perm (Fin 12)) = tid := by decide +kernel

theorem tbl_inj {σ τ : Equiv.Perm (Fin 12)} (h : tbl σ = tbl τ) : σ = τ := by
  ext i
  have := congrArg (fun l => l.getD (i : ℕ) 0) h
  simp only [tbl_getD] at this
  exact this

theorem tbl_gA : tbl m12gA = tA := by decide +kernel

theorem tbl_gB : tbl m12gB = tB := by decide +kernel

theorem tbl_gBi : tbl m12gB⁻¹ = tBi := by decide +kernel

@[expose] def letterM (d : ℕ) : ↥NativeSporadic.M12 :=
  if d = 1 then m12a else if d = 2 then m12b else if d = 3 then m12b⁻¹ else 1

@[expose] def evalM : ℕ → ℕ → ↥NativeSporadic.M12
  | 0, _ => 1
  | n + 1, w => if w = 0 then 1 else letterM (w % 4) * evalM n (w / 4)

theorem tbl_letterM (d : ℕ) :
    tbl ((letterM d : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = letterT tB tBi d := by
  unfold letterM letterT
  split_ifs
  · exact tbl_gA
  · exact tbl_gB
  · exact tbl_gBi
  · exact tbl_one

theorem tbl_evalM : ∀ n w : ℕ,
    tbl ((evalM n w : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = evalN tB tBi n w
  | 0, w => by simp [evalM, evalN, tbl_one]
  | n + 1, w => by
    by_cases hw : w = 0
    · simp [evalM, evalN, hw, tbl_one]
    · simp only [evalM, evalN, hw, ite_false]
      rw [Subgroup.coe_mul, tbl_mul, tbl_letterM, tbl_evalM n]

theorem mem_TL_of_enc {t : Tab} (h1 : t.length = 12) (h2 : ∀ x ∈ t, x < 12)
    (h : enc t ∈ TLc) : t ∈ TL := by
  rw [← TLc_eq] at h
  obtain ⟨s, hs, hst⟩ := List.mem_map.1 h
  obtain ⟨hs1, hs2⟩ := TL_valid s hs
  exact enc_inj s t (by omega) hs2 h2 hst ▸ hs

theorem tbl_mul_mem {σ τ : Equiv.Perm (Fin 12)} (hσ : tbl σ ∈ TL) (hτ : tbl τ ∈ TL) :
    tbl (σ * τ) ∈ TL :=
  mem_TL_of_enc (tbl_length _) (tbl_lt _) (by rw [tbl_mul]; exact TL_closed _ hσ _ hτ)

theorem tbl_pow_mem {σ : Equiv.Perm (Fin 12)} (hσ : tbl σ ∈ TL) (k : ℕ) : tbl (σ ^ k) ∈ TL := by
  induction k with
  | zero => rw [pow_zero, tbl_one]; exact TL_one
  | succ k ih => rw [pow_succ]; exact tbl_mul_mem ih hσ

@[expose] def TS : Subgroup (Equiv.Perm (Fin 12)) where
  carrier := {σ | tbl σ ∈ TL}
  mul_mem' := fun hσ hτ => tbl_mul_mem hσ hτ
  one_mem' := by show tbl (1 : Equiv.Perm (Fin 12)) ∈ TL; rw [tbl_one]; exact TL_one
  inv_mem' := by
    intro σ hσ
    have hpos := orderOf_pos σ
    have h1 : σ * σ ^ (orderOf σ - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    have h2 : σ⁻¹ = σ ^ (orderOf σ - 1) := inv_eq_of_mul_eq_one_right h1
    show tbl σ⁻¹ ∈ TL
    rw [h2]
    exact tbl_pow_mem hσ _

theorem mem_TS {σ : Equiv.Perm (Fin 12)} : σ ∈ TS ↔ tbl σ ∈ TL := Iff.rfl

theorem exists_mem_TS_of_mem {t : Tab} (ht : t ∈ TL) :
    ∃ w ∈ thWords, tbl ((evalM fuel w : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = t := by
  rw [← TL_words] at ht
  obtain ⟨w, hw, hwt⟩ := List.mem_map.1 ht
  exact ⟨w, hw, by rw [tbl_evalM, hwt]⟩

theorem TS_le : TS ≤ NativeSporadic.M12 := by
  intro σ hσ
  obtain ⟨w, -, hw⟩ := exists_mem_TS_of_mem (mem_TS.1 hσ)
  have : σ = ((evalM fuel w : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) := tbl_inj (hw.symm)
  rw [this]
  exact (evalM fuel w).2

theorem TS_card : Nat.card TS = 64 := by
  have hbij : Function.Bijective
      (fun σ : TS => (⟨tbl σ.1, List.mem_toFinset.2 σ.2⟩ : TL.toFinset)) := by
    constructor
    · intro σ τ h
      exact Subtype.ext (tbl_inj (congrArg Subtype.val h))
    · rintro ⟨t, ht⟩
      obtain ⟨w, -, hw⟩ := exists_mem_TS_of_mem (List.mem_toFinset.1 ht)
      refine ⟨⟨((evalM fuel w : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)), ?_⟩, ?_⟩
      · rw [mem_TS, hw]; exact List.mem_toFinset.1 ht
      · exact Subtype.ext hw
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup TL_nodup, TL_length]

@[expose] def sylSub : Subgroup ↥NativeSporadic.M12 := TS.subgroupOf NativeSporadic.M12

theorem sylSub_card : Nat.card sylSub = 64 := by
  rw [← TS_card]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe TS_le).toEquiv

noncomputable def sylow : Sylow 2 ↥NativeSporadic.M12 :=
  (IsPGroup.of_card (p := 2) (n := 6) (by rw [sylSub_card]; norm_num)).toSylow (by
    have h := Subgroup.card_mul_index sylSub
    rw [sylSub_card, card_M12] at h
    have : sylSub.index = 1485 := by omega
    rw [this]
    decide)

theorem exists_conj_mem_sylSub (Q : Subgroup ↥NativeSporadic.M12)
    (hQ : IsPGroup 2 Q) : ∃ g : ↥NativeSporadic.M12, ∀ q ∈ Q, g⁻¹ * q * g ∈ sylSub := by
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M12 sylow P
  refine ⟨g, fun q hq => ?_⟩
  have hq' : q ∈ ((g • sylow : Sylow 2 ↥NativeSporadic.M12) : Subgroup _) := by
    rw [hg]; exact hP hq
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq'
  exact hq'

@[expose] def vecN (u : List ℕ) (j : ℕ) : ZMod 2 := (u.getD j 0 : ℕ)

theorem e8_even : ∀ E ∈ e8Data, ∀ k < 3, ∑ j : Fin 12, vecN (E.2.getD k []) j = 0 := by
  decide +kernel

theorem e8_fix : ∀ E ∈ e8Data, ∀ t ∈ E.1, ∀ k < 3, ∃ c : ZMod 2, ∀ j : Fin 12,
    vecN (E.2.getD k []) j + vecN (E.2.getD k []) (t.getD j 0) = c := by decide +kernel

theorem e8_indep : ∀ E ∈ e8Data, ∀ c : Fin 3 → ZMod 2, (∃ c' : ZMod 2, ∀ j : Fin 12,
    c 0 * vecN (E.2.getD 0 []) j + c 1 * vecN (E.2.getD 1 []) j +
      c 2 * vecN (E.2.getD 2 []) j = c') → c = 0 := by decide +kernel

@[expose] def fixSub (w : ℕ → ZMod 2) : Subgroup (Equiv.Perm (Fin 12)) where
  carrier := {σ | ∃ c : ZMod 2, ∀ j : Fin 12, w j + w (σ j : ℕ) = c}
  mul_mem' := by
    rintro σ τ ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨d + c, fun j => ?_⟩
    have key : ∀ a b c : ZMod 2, a + b = (a + c) + (c + b) := by decide
    rw [Equiv.Perm.mul_apply, key (w j) (w (σ (τ j) : ℕ)) (w (τ j : ℕ)), hd j, hc (τ j)]
  one_mem' := ⟨0, fun j => by
    have : ∀ a : ZMod 2, a + a = 0 := by decide
    exact this _⟩
  inv_mem' := by
    rintro σ ⟨c, hc⟩
    refine ⟨c, fun j => ?_⟩
    have h2 : σ (σ⁻¹ j) = j := by simp
    have := hc (σ⁻¹ j)
    rw [h2] at this
    rw [add_comm]
    exact this

@[expose] def cj (g x : ↥NativeSporadic.M12) : ↥NativeSporadic.M12 := g⁻¹ * x * g

theorem cj_mul (g x y : ↥NativeSporadic.M12) : cj g (x * y) = cj g x * cj g y := by
  simp [cj, mul_assoc]

theorem cj_one (g : ↥NativeSporadic.M12) : cj g 1 = 1 := by simp [cj]

theorem cj_inj (g : ↥NativeSporadic.M12) {x y : ↥NativeSporadic.M12} (h : cj g x = cj g y) :
    x = y := by
  simpa [cj] using h

theorem cj_eq_one_iff (g x : ↥NativeSporadic.M12) : cj g x = 1 ↔ x = 1 := by
  constructor
  · intro h; exact cj_inj g (h.trans (cj_one g).symm)
  · rintro rfl; exact cj_one g

theorem tbl_mem_invs (g : ↥NativeSporadic.M12) {x : ↥NativeSporadic.M12}
    (hT : cj g x ∈ sylSub) (h1 : x ≠ 1) (h2 : x * x = 1) :
    tbl ((cj g x : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ invs := by
  simp only [invs, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨hT, fun h => h1 ?_, ?_⟩
  · have h3 : ((cj g x : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = 1 := by
      apply tbl_inj; rw [h, tbl_one]
    exact (cj_eq_one_iff g x).1 (Subtype.ext h3)
  · rw [← tbl_mul, ← Subgroup.coe_mul, ← cj_mul, h2, cj_one]
    exact tbl_one

theorem e8_vectors (E : Subgroup ↥NativeSporadic.M12)
    (hcard : Nat.card E = 8) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) :
    ∃ u : Fin 3 → Fin 12 → ZMod 2, (∀ k, ∑ j, u k j = 0) ∧
      (∀ k, ∀ e ∈ E, ∃ c : ZMod 2, ∀ j, u k j + u k ((e : Equiv.Perm (Fin 12)) j) = c) ∧
      (∀ c : Fin 3 → ZMod 2, (∃ c' : ZMod 2, ∀ j, ∑ k, c k * u k j = c') → c = 0) := by
  classical
  have hP : IsPGroup 2 E := IsPGroup.of_card (p := 2) (n := 3) (by rw [hcard]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_sylSub E hP
  have hcommE : IsMulCommutative ↥E := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have hEA : CFSG.IsElementaryAbelian 2 ↥E :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => by
        rw [pow_two]; exact Subtype.ext (hsq x x.2) }
  have hrank : Module.finrank (ZMod 2) (Additive ↥E) = 3 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥E)
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive ↥E) = 8 := by rw [← hcard]; exact Nat.card_congr Additive.toMul
    rw [h2] at h1
    exact Nat.pow_right_injective (le_refl 2)
      (by simpa using h1.symm : 2 ^ Module.finrank (ZMod 2) (Additive ↥E) = 2 ^ 3)
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive ↥E) hrank
  let X : Fin 3 → ↥E := fun k => Additive.toMul (b k)
  let Y : Fin 3 → ↥NativeSporadic.M12 := fun k => cj g (X k : ↥NativeSporadic.M12)
  have hY1 : ∀ k, Y k ∈ sylSub := fun k => hg _ (X k).2
  have hXne : ∀ k, (X k : ↥NativeSporadic.M12) ≠ 1 := by
    intro k h
    have h1 : X k = 1 := Subtype.ext h
    exact b.ne_zero k (toMul_eq_one.1 h1)
  have hYne : ∀ k, Y k ≠ 1 := fun k h => hXne k ((cj_eq_one_iff g _).1 h)
  have hXsq : ∀ k, (X k : ↥NativeSporadic.M12) * X k = 1 := fun k => hsq _ (X k).2
  have hYsq : ∀ k, Y k * Y k = 1 := fun k => by
    show cj g _ * cj g _ = 1
    rw [← cj_mul, hXsq, cj_one]
  have hYcomm : ∀ j k, Y j * Y k = Y k * Y j := fun j k => by
    show cj g _ * cj g _ = cj g _ * cj g _
    rw [← cj_mul, ← cj_mul, hcomm _ (X j).2 _ (X k).2]
  have hYinj : ∀ j k, j ≠ k → Y j ≠ Y k := by
    intro j k hjk h
    have h1 : (X j : ↥NativeSporadic.M12) = X k := cj_inj g h
    have h2 : X j = X k := Subtype.ext h1
    exact hjk (b.injective (Additive.toMul.injective h2))
  have hYz : Y 2 ≠ Y 0 * Y 1 := by
    intro h
    have h1 : (X 2 : ↥NativeSporadic.M12) = (X 0 : ↥NativeSporadic.M12) * X 1 :=
      cj_inj g (h.trans (cj_mul g _ _).symm)
    have h2 : X 2 = X 0 * X 1 := Subtype.ext h1
    have h3 : b 2 = b 0 + b 1 := by
      have := congrArg Additive.ofMul h2
      simpa [X] using this
    have h4 := congrArg (fun v => b.repr v 2) h3
    simp [Module.Basis.repr_self] at h4
  have hYtbl : ∀ k, tbl ((Y k : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ invs :=
    fun k => tbl_mem_invs g (hY1 k) (hXne k) (hXsq k)
  have hcommT : ∀ j k, tmul (tbl ((Y j : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)))
      (tbl ((Y k : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))) =
      tmul (tbl ((Y k : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)))
        (tbl ((Y j : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))) := fun j k => by
    rw [← tbl_mul, ← tbl_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hYcomm j k]
  have hneT : ∀ j k, j ≠ k → tbl ((Y j : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ≠
      tbl ((Y k : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) :=
    fun j k hjk h => hYinj j k hjk (Subtype.ext (tbl_inj h))
  have hzT : tbl ((Y 2 : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ≠
      tmul (tbl ((Y 0 : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)))
        (tbl ((Y 1 : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))) := by
    rw [← tbl_mul, ← Subgroup.coe_mul]
    intro h
    exact hYz (Subtype.ext (tbl_inj h))
  obtain ⟨E₀, hE₀, hm0, hm1, hm2⟩ := e8_cover _ (hYtbl 0) _ (hYtbl 1) (hcommT 0 1)
    (hneT 1 0 (by decide)) _ (hYtbl 2) (hcommT 0 2) (hcommT 1 2) (hneT 2 0 (by decide))
    (hneT 2 1 (by decide)) hzT
  have hmem : ∀ i : Fin 3, tbl ((Y i : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ E₀.1 := by
    intro i
    fin_cases i
    · exact hm0
    · exact hm1
    · exact hm2
  have hfix1 : ∀ i k : Fin 3, ((Y i : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈
      fixSub (vecN (E₀.2.getD k [])) := by
    intro i k
    obtain ⟨c, hc⟩ := e8_fix E₀ hE₀ _ (hmem i) k k.2
    refine ⟨c, fun j => ?_⟩
    have := hc j
    rwa [tbl_getD] at this
  have hall : ∀ k : Fin 3, ∀ e ∈ E,
      ((cj g e : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈
        fixSub (vecN (E₀.2.getD k [])) := by
    intro k e he
    let Pw : Submodule (ZMod 2) (Additive ↥E) :=
      { carrier := {v | ((cj g ((Additive.toMul v : ↥E) : ↥NativeSporadic.M12) :
          ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ fixSub (vecN (E₀.2.getD k []))}
        add_mem' := by
          intro v v' hv hv'
          show ((cj g ((Additive.toMul (v + v') : ↥E) : ↥NativeSporadic.M12) :
            ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈
            fixSub (vecN (E₀.2.getD k []))
          rw [toMul_add, Subgroup.coe_mul, cj_mul, Subgroup.coe_mul]
          exact (fixSub _).mul_mem hv hv'
        zero_mem' := by
          show ((cj g ((Additive.toMul (0 : Additive ↥E) : ↥E) : ↥NativeSporadic.M12) :
            ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈
            fixSub (vecN (E₀.2.getD k []))
          rw [toMul_zero, Subgroup.coe_one, cj_one, Subgroup.coe_one]
          exact (fixSub _).one_mem
        smul_mem' := by
          intro c v hv
          rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
          · rw [zero_smul]
            show ((cj g ((Additive.toMul (0 : Additive ↥E) : ↥E) : ↥NativeSporadic.M12) :
              ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈
              fixSub (vecN (E₀.2.getD k []))
            rw [toMul_zero, Subgroup.coe_one, cj_one, Subgroup.coe_one]
            exact (fixSub _).one_mem
          · rw [one_smul]
            exact hv }
    have hb : ∀ i, b i ∈ Pw := fun i => hfix1 i k
    have htop : Pw = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb i
    have : Additive.ofMul (⟨e, he⟩ : ↥E) ∈ Pw := htop ▸ Submodule.mem_top
    exact this
  refine ⟨fun k j => vecN (E₀.2.getD k [])
    ((((g⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) j : Fin 12) : ℕ), ?_, ?_, ?_⟩
  · intro k
    have h := e8_even E₀ hE₀ k k.2
    rw [← h]
    exact Equiv.sum_comp ((g⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))
      (fun i : Fin 12 => vecN (E₀.2.getD k []) i)
  · intro k e he
    obtain ⟨c, hc⟩ := hall k e he
    refine ⟨c, fun j => ?_⟩
    have h1 := hc (((g⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) j)
    have h2 : ((cj g e : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))
        (((g⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) j) =
        ((g⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) ((e : Equiv.Perm (Fin 12)) j) := by
      simp [cj, Equiv.Perm.mul_apply]
    rw [h2] at h1
    exact h1
  · rintro c ⟨c', hc'⟩
    apply e8_indep E₀ hE₀ c
    refine ⟨c', fun i => ?_⟩
    have := hc' (((g : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) i)
    simpa [Fin.sum_univ_three] using this

theorem invol_cycles (π : ↥NativeSporadic.M12) (h1 : π ≠ 1)
    (h2 : π * π = 1) :
    ∃ a b : Fin 4 → Fin 12,
      (∀ k, (π : Equiv.Perm (Fin 12)) (a k) = b k ∧ (π : Equiv.Perm (Fin 12)) (b k) = a k) ∧
      (∀ k, a k ≠ b k) ∧ (∀ k l, k ≠ l → a k ≠ a l ∧ a k ≠ b l ∧ b k ≠ b l) := by
  classical
  have hord : orderOf π = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  have hP : IsPGroup 2 (Subgroup.zpowers π) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_sylSub _ hP
  have hT : cj g π ∈ sylSub := hg π (Subgroup.mem_zpowers π)
  have hinv := tbl_mem_invs g hT h1 h2
  have hlen := inv_cycles _ hinv
  set t : Equiv.Perm (Fin 12) := ((cj g π : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) with ht
  have htt : ∀ x, t (t x) = x := by
    intro x
    have : (cj g π * cj g π : ↥NativeSporadic.M12) = 1 := by rw [← cj_mul, h2, cj_one]
    have h3 : t * t = 1 := by
      have := congrArg (fun m : ↥NativeSporadic.M12 => (m : Equiv.Perm (Fin 12))) this
      simpa [ht] using this
    simpa using congrArg (fun s : Equiv.Perm (Fin 12) => s x) h3
  have hπ : ∀ x, (π : Equiv.Perm (Fin 12)) ((g : Equiv.Perm (Fin 12)) x) =
      (g : Equiv.Perm (Fin 12)) (t x) := by
    intro x
    simp [ht, cj, Equiv.Perm.mul_apply]
  obtain ⟨L, hL⟩ : ∃ L, L = twoCycles (tbl t) := ⟨_, rfl⟩
  rw [← hL] at hlen
  have hnd : L.Nodup := by rw [hL]; exact (List.nodup_range).filter _
  have hmemL' : ∀ y ∈ L, y < 12 ∧ y < (tbl t).getD y 0 := by
    intro y hy
    rw [hL, twoCycles, List.mem_filter, List.mem_range] at hy
    obtain ⟨hlt, hlt2⟩ := hy
    exact ⟨hlt, by simpa using hlt2⟩
  have hmemL : ∀ k : Fin 4, ∃ x : Fin 12, (L[(k : ℕ)]'(by omega) : ℕ) = x ∧
      (x : ℕ) < (t x : ℕ) := by
    intro k
    obtain ⟨hlt, hlt2⟩ := hmemL' _ (List.getElem_mem (by omega : (k : ℕ) < L.length))
    refine ⟨⟨_, hlt⟩, rfl, ?_⟩
    rw [← tbl_getD t ⟨_, hlt⟩]
    exact hlt2
  choose x hx hxlt using hmemL
  have hxinj : ∀ k l, x k = x l → k = l := by
    intro k l h
    have h' : L[(k : ℕ)]'(by omega) = L[(l : ℕ)]'(by omega) := by rw [hx, hx, h]
    exact Fin.ext ((hnd.getElem_inj_iff).1 h')
  refine ⟨fun k => (g : Equiv.Perm (Fin 12)) (x k), fun k => (g : Equiv.Perm (Fin 12)) (t (x k)),
    fun k => ⟨hπ _, ?_⟩, fun k h => ?_, fun k l hkl => ⟨?_, ?_, ?_⟩⟩
  · rw [hπ, htt]
  · have h' : (g : Equiv.Perm (Fin 12)) (x k) = (g : Equiv.Perm (Fin 12)) (t (x k)) := h
    have h'' := congrArg (fun y : Fin 12 => (y : ℕ)) ((g : Equiv.Perm (Fin 12)).injective h')
    have h3 := hxlt k
    omega
  · intro h
    exact hkl (hxinj k l ((g : Equiv.Perm (Fin 12)).injective h))
  · intro h
    have h3 : x k = t (x l) := (g : Equiv.Perm (Fin 12)).injective h
    have h4 : t (x k) = x l := by rw [h3, htt]
    have h5 : (x k : ℕ) < (x l : ℕ) := by
      have := hxlt k
      rwa [h4] at this
    have h6 : (x l : ℕ) < (x k : ℕ) := by
      have := hxlt l
      rwa [← h3] at this
    omega
  · intro h
    exact hkl (hxinj k l (t.injective ((g : Equiv.Perm (Fin 12)).injective h)))

end M12Syl

end CFSG.Quasithin.G11.SzG11S
