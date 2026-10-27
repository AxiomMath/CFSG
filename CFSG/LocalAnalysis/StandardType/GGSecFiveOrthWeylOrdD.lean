module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflTypeD
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrd
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA

public section

namespace CFSG.StandardType.OrthF3

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin CFSG.Timmesfeld.ARS.CaseOA

private abbrev ct_od2_Rep (m : ℕ)
    (w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group)
    (π : Equiv.Perm (Fin (m + 1))) (s : Fin (m + 1) → ℤ) : Prop :=
  ∀ v, toStdD (m + 1) (weylAction (isFiniteType_cartanD (m + 1)) w v) =
    fun c => s c * toStdD (m + 1) v (π c)

private theorem ct_od2_coxeterMatrixD_eq (r : ℕ) :
    ggCoxeterMatrixD r = coxeterMatrix (isFiniteType_cartanD r) := by
  ext i j
  rw [ggCoxeterMatrixD_apply, ← cartanD_eq r]
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    simp [cartanD, TauCeti.coxeterOrder_four]
  · rw [if_neg hij]
    have hsymm : cartanD r j i = cartanD r i j := by
      rw [cartanD_eq]
      exact (CartanMatrix.D_isSymm r).apply i j
    rw [hsymm]
    have h01 : cartanD r i j = -1 ∨ cartanD r i j = 0 := by
      rw [cartanD_eq]
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rcases h01 with h | h
    · rw [h]
      simp [TauCeti.coxeterOrder_one]
    · rw [h]
      simp [TauCeti.coxeterOrder_zero]

private theorem ct_od2_rep_mul (m : ℕ)
    {w₁ w₂ : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group}
    {π₁ π₂ : Equiv.Perm (Fin (m + 1))} {s₁ s₂ : Fin (m + 1) → ℤ}
    (h₁ : ct_od2_Rep m w₁ π₁ s₁) (h₂ : ct_od2_Rep m w₂ π₂ s₂) :
    ct_od2_Rep m (w₂ * w₁) (π₁ * π₂) (fun c => s₂ c * s₁ (π₂ c)) := by
  intro v
  rw [weylAction_mul_apply, h₂]
  funext c
  rw [h₁]
  simp only [Function.comp_apply, Equiv.Perm.coe_mul]
  ring

private theorem ct_od2_realizes_perm (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group,
      ct_od2_Rep m w σ (fun _ => 1) := by
  have hgen : σ ∈ Submonoid.closure
      (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ m]
    exact Submonoid.mem_top σ
  refine Submonoid.closure_induction (motive := fun σ _ =>
      ∃ w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group,
        ct_od2_Rep m w σ (fun _ => 1)) ?_ ?_ ?_ hgen
  · rintro x ⟨i, rfl⟩
    refine ⟨(coxeterMatrix (isFiniteType_cartanD (m + 1))).toCoxeterSystem.simple
      i.castSucc, ?_⟩
    intro v
    rw [weylAction_simple,
      toStdD_reflection_of_lt (m + 1) (by simp only [Fin.val_castSucc]; omega)]
    have hval : (⟨i.castSucc.val + 1, by simp only [Fin.val_castSucc]; omega⟩ :
        Fin (m + 1)) = i.succ := Fin.ext (by simp)
    rw [hval]
    funext c
    simp
  · refine ⟨1, ?_⟩
    intro v
    simp
  · rintro x y hx hy ⟨wx, hxrep⟩ ⟨wy, hyrep⟩
    refine ⟨wy * wx, ?_⟩
    intro v
    rw [weylAction_mul_apply, hyrep, hxrep]
    funext c
    simp [Equiv.Perm.coe_mul]

private theorem ct_od2_simple_last_rep (m : ℕ) (hm : 1 ≤ m) :
    ct_od2_Rep m ((coxeterMatrix (isFiniteType_cartanD (m + 1))).toCoxeterSystem.simple
        (Fin.last m))
      (Equiv.swap ⟨m - 1, by omega⟩ (Fin.last m))
      (fun c => if c = ⟨m - 1, by omega⟩ ∨ c = Fin.last m then (-1 : ℤ) else 1) := by
  intro v
  rw [weylAction_simple, toStdD_reflection,
    stdReflD_of_not_lt (m + 1) (by simp only [Fin.last]; omega)]
  have hp : (⟨(Fin.last m).val - 1, by omega⟩ : Fin (m + 1)) =
      ⟨m - 1, by omega⟩ := Fin.ext (by simp [Fin.last])
  rw [hp]
  funext c
  have hcond : (c.val + 2 = m + 1 ∨ c.val + 1 = m + 1) ↔
      (c = ⟨m - 1, by omega⟩ ∨ c = Fin.last m) := by
    constructor
    · rintro (h | h)
      · left
        apply Fin.ext
        simp only
        omega
      · right
        apply Fin.ext
        simp only [Fin.val_last]
        omega
    · rintro (h | h)
      · subst h
        left
        change m - 1 + 2 = m + 1
        omega
      · subst h
        right
        simp only [Fin.val_last]
  simp only [hcond]

private theorem ct_od2_realizes_pure_double_last (m : ℕ) (hm : 1 ≤ m) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group,
      ct_od2_Rep m w 1
        (fun c => if c = ⟨m - 1, by omega⟩ ∨ c = Fin.last m then (-1 : ℤ) else 1) := by
  obtain ⟨ws, hws⟩ := ct_od2_realizes_perm m
    (Equiv.swap ⟨m - 1, by omega⟩ (Fin.last m))
  have hd := ct_od2_simple_last_rep m hm
  have hmul := ct_od2_rep_mul m hws hd
  refine ⟨(coxeterMatrix (isFiniteType_cartanD (m + 1))).toCoxeterSystem.simple
    (Fin.last m) * ws, ?_⟩
  convert hmul using 2
  · ext c
    simp
  · ring

private theorem ct_od2_realizes_pure_double (m : ℕ) (hm : 1 ≤ m)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group,
      ct_od2_Rep m w 1 (fun c => if c = i ∨ c = j then (-1 : ℤ) else 1) := by
  let p : Fin (m + 1) := ⟨m - 1, by omega⟩
  let k : Fin (m + 1) := Fin.last m
  have hpk : p ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    simp only [p, k, Fin.val_last] at hv
    omega
  obtain ⟨μ, hμi, hμj⟩ := (MulAction.is_two_pretransitive_iff.mp
    (Equiv.Perm.isMultiplyPretransitive (Fin (m + 1)) 2)) hij hpk
  have hμi' : μ i = p := hμi
  have hμj' : μ j = k := hμj
  obtain ⟨wμ, hwμ⟩ := ct_od2_realizes_perm m μ
  obtain ⟨wν, hwν⟩ := ct_od2_realizes_perm m μ⁻¹
  obtain ⟨wd, hwd⟩ := ct_od2_realizes_pure_double_last m hm
  have h1 : ct_od2_Rep m (wd * wν) (μ⁻¹)
      (fun c => if c = p ∨ c = k then (-1 : ℤ) else 1) := by
    have h := ct_od2_rep_mul m hwν hwd
    convert h using 2
    · ext c
      simp
    · ring
  have h2 := ct_od2_rep_mul m h1 hwμ
  refine ⟨wμ * (wd * wν), ?_⟩
  convert h2 using 2
  · ext c
    simp
  · have hpi : p = μ i := hμi'.symm
    have hkj : k = μ j := hμj'.symm
    rw [hpi, hkj]
    simp only [μ.injective.eq_iff]
    ring

private theorem ct_od2_realizes_delta_prod (m : ℕ) (hm : 1 ≤ m) (b : Fin (m + 1))
    (T : Finset (Fin (m + 1))) (hb : b ∉ T) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group,
      ct_od2_Rep m w 1
        (fun c => ∏ i ∈ T, (if c = i ∨ c = b then (-1 : ℤ) else 1)) := by
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_⟩
      intro v
      simp
  | insert a T ha ih =>
      have hbT : b ∉ T := fun h => hb (Finset.mem_insert_of_mem h)
      have hba : b ≠ a := by
        intro h
        apply hb
        rw [h]
        exact Finset.mem_insert_self a T
      obtain ⟨w, hw⟩ := ih hbT
      obtain ⟨wd, hwd⟩ := ct_od2_realizes_pure_double m hm (Ne.symm hba)
      refine ⟨wd * w, ?_⟩
      have h := ct_od2_rep_mul m hw hwd
      convert h using 2
      · ext c
        simp
      · rw [Finset.prod_insert ha]
        rfl

private theorem ct_od2_even_card_filter_neg (m : ℕ) (t : Fin (m + 1) → ℤ)
    (ht : ∀ c, t c = 1 ∨ t c = -1) (hprod : ∏ c, t c = 1) :
    Even (Finset.univ.filter (fun c => t c = -1)).card := by
  set S := Finset.univ.filter (fun c => t c = -1) with hS
  have hcomp : (∏ c ∈ S, (-1 : ℤ)) = 1 := by
    have h := Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset (Fin (m + 1))))
      (p := fun c => t c = -1) (f := fun c => t c)
    have h1 : (∏ c ∈ S, t c) = ∏ c ∈ S, (-1 : ℤ) :=
      Finset.prod_congr rfl fun c hc => by
        rw [hS, Finset.mem_filter] at hc
        exact hc.2
    have h2 : (∏ c ∈ Finset.univ.filter (fun c => ¬ t c = -1), t c) = 1 := by
      apply Finset.prod_eq_one
      intro c hc
      rw [Finset.mem_filter] at hc
      rcases ht c with hc1 | hc1
      · exact hc1
      · exact absurd hc1 hc.2
    rw [← hS, h1, h2, hprod] at h
    simpa using h
  have hpow : (-1 : ℤ) ^ S.card = 1 := by
    simpa [Finset.prod_const] using hcomp
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hpow

private theorem ct_od2_realizes_pure_sign (m : ℕ) (hm : 1 ≤ m) (t : Fin (m + 1) → ℤ)
    (ht : ∀ c, t c = 1 ∨ t c = -1) (hprod : ∏ c, t c = 1) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group,
      ct_od2_Rep m w 1 t := by
  classical
  set S : Finset (Fin (m + 1)) := Finset.univ.filter (fun c => t c = -1) with hSdef
  have heven : Even S.card := by
    simpa [hSdef] using ct_od2_even_card_filter_neg m t ht hprod
  have htS : t = fun c => if c ∈ S then (-1 : ℤ) else 1 := by
    funext c
    by_cases hc : c ∈ S
    · rw [if_pos hc]
      rw [hSdef, Finset.mem_filter] at hc
      exact hc.2
    · rw [if_neg hc]
      rw [hSdef, Finset.mem_filter] at hc
      push Not at hc
      have hc' : t c ≠ -1 := by simpa using hc
      rcases ht c with h1 | h1
      · exact h1
      · exact absurd h1 hc'
  by_cases hS : S = ∅
  · refine ⟨1, ?_⟩
    rw [htS]
    intro v
    simp [hS]
  · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    have hpos : 0 < S.card := Finset.card_pos.mpr hne
    obtain ⟨b, hbS⟩ := hne
    set T : Finset (Fin (m + 1)) := S.erase b with hTdef
    have hbT : b ∉ T := by simp [hTdef]
    have hcardT : T.card + 1 = S.card := by
      simpa [hTdef] using Finset.card_erase_add_one hbS
    have hodd : Odd T.card := by
      rcases heven with ⟨k, hk⟩
      refine ⟨k - 1, by omega⟩
    have hdelta : (fun c => ∏ i ∈ T, (if c = i ∨ c = b then (-1 : ℤ) else 1)) =
        fun c => if c ∈ S then (-1 : ℤ) else 1 := by
      funext c
      by_cases hcb : c = b
      · rw [hcb]
        have hprod : (∏ i ∈ T, (if b = i ∨ b = b then (-1 : ℤ) else 1)) =
            (-1 : ℤ) ^ T.card := by
          simp [Finset.prod_const]
        rw [hprod, hodd.neg_one_pow]
        simp [hbS]
      · by_cases hcT : c ∈ T
        · have hcS : c ∈ S := Finset.mem_of_mem_erase hcT
          have hprod : (∏ i ∈ T, (if c = i ∨ c = b then (-1 : ℤ) else 1)) =
              (if c = c ∨ c = b then (-1 : ℤ) else 1) := by
            refine Finset.prod_eq_single_of_mem c hcT ?_
            intro i hi hic
            simp [hic.symm, hcb]
          rw [hprod]
          simp [hcS]
        · have hcS : c ∉ S := by
            intro hcS
            have : c ∈ T := by
              rw [hTdef, Finset.mem_erase]
              exact ⟨hcb, hcS⟩
            exact hcT this
          have hprod : (∏ i ∈ T, (if c = i ∨ c = b then (-1 : ℤ) else 1)) = 1 := by
            apply Finset.prod_eq_one
            intro i hi
            have hic : c ≠ i := by
              intro h
              exact hcS (h ▸ Finset.mem_of_mem_erase hi)
            simp [hic, hcb]
          rw [hprod]
          simp [hcS]
    obtain ⟨w, hw⟩ := ct_od2_realizes_delta_prod m hm b T hbT
    refine ⟨w, ?_⟩
    rw [hdelta] at hw
    rw [htS]
    exact hw

private noncomputable def ct_od2_toStdDAddHom (n : ℕ) :
    (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun := toStdD n
  map_zero' := toStdD_zero n
  map_add' := fun v w => toStdD_add n v w

private theorem ct_od2_telescope (m : ℕ) :
    ∀ d : ℕ, ∀ i : Fin (m + 1), (hi : i.val + d ≤ m) →
      (∑ t : Fin d,
          toStdD (m + 1) (Pi.single ⟨i.val + t.val, by
            have ht : t.val < d := t.isLt
            omega⟩ 1)) =
        Pi.single i 1 - Pi.single ⟨i.val + d, by omega⟩ 1 := by
  intro d
  induction d with
  | zero =>
      intro i hi
      simp
  | succ d ih =>
      intro i hi
      rw [Fin.sum_univ_castSucc]
      have hcast : (∑ t : Fin d,
          toStdD (m + 1) (Pi.single ⟨i.val + (Fin.castSucc t).val, by omega⟩ 1)) =
          ∑ t : Fin d,
            toStdD (m + 1) (Pi.single ⟨i.val + t.val, by omega⟩ 1) := by
        apply Finset.sum_congr rfl
        intro t ht
        congr 2
      rw [hcast, ih i (by omega)]
      have hlt : (⟨i.val + (Fin.last d).val, by omega⟩ : Fin (m + 1)).val + 1 < m + 1 := by
        simp only [Fin.val_last]
        omega
      rw [toStdD_single_of_lt (m + 1) hlt]
      simp only [Fin.val_last]
      abel

private lemma ct_od2_prod_pm {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (∏ i ∈ s, f i) = 1 ∨ (∏ i ∈ s, f i) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases hf a with ha1 | ha1 <;> rcases ih with hs | hs <;> simp [ha1, hs]

private lemma ct_od2_prod_pm_sq {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (∏ i ∈ s, f i) * (∏ i ∈ s, f i) = 1 := by
  rcases ct_od2_prod_pm s f hf with h | h <;> rw [h] <;> norm_num

private def ct_od2_signOf (m : ℕ) (bits : Fin m → Bool) : Fin (m + 1) → ℤ :=
  Fin.lastCases (∏ j : Fin m, (if bits j then (-1 : ℤ) else 1))
    (fun j => if bits j then (-1 : ℤ) else 1)

private lemma ct_od2_signOf_pm (m : ℕ) (bits : Fin m → Bool) (c : Fin (m + 1)) :
    ct_od2_signOf m bits c = 1 ∨ ct_od2_signOf m bits c = -1 := by
  cases c using Fin.lastCases with
  | last =>
      dsimp [ct_od2_signOf]
      rcases ct_od2_prod_pm Finset.univ (fun j : Fin m =>
        (if bits j then (-1 : ℤ) else 1)) (fun j => by
          by_cases hb : bits j <;> simp [hb]) with h | h <;> simp [h]
  | cast j =>
      dsimp [ct_od2_signOf]
      by_cases hb : bits j <;> simp [hb]

private lemma ct_od2_signOf_prod (m : ℕ) (bits : Fin m → Bool) :
    (∏ c : Fin (m + 1), ct_od2_signOf m bits c) = 1 := by
  rw [Fin.prod_univ_castSucc]
  have hcast : (∏ j : Fin m, ct_od2_signOf m bits j.castSucc) =
      ∏ j : Fin m, (if bits j then (-1 : ℤ) else 1) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [ct_od2_signOf]
  rw [hcast]
  have hlast : ct_od2_signOf m bits (Fin.last m) =
      ∏ j : Fin m, (if bits j then (-1 : ℤ) else 1) := by
    simp [ct_od2_signOf]
  rw [hlast]
  exact ct_od2_prod_pm_sq Finset.univ (fun j : Fin m =>
    (if bits j then (-1 : ℤ) else 1)) (fun j => by
      by_cases hb : bits j <;> simp [hb])

private lemma ct_od2_signOf_inj (m : ℕ) {bits bits' : Fin m → Bool}
    (h : ct_od2_signOf m bits = ct_od2_signOf m bits') : bits = bits' := by
  funext j
  have hj := congrFun h j.castSucc
  simp only [ct_od2_signOf, Fin.lastCases_castSucc] at hj
  cases hb : bits j <;> cases hb' : bits' j <;> simp_all

private theorem ct_od2_toStdD_two_single (m : ℕ) (hm : 1 ≤ m) (i : Fin (m + 1)) :
    ∃ v : Fin (m + 1) → ℤ, toStdD (m + 1) v = (2 : ℤ) • Pi.single i 1 := by
  let d := m - i.val
  let v : Fin (m + 1) → ℤ :=
    (2 : ℤ) • (∑ t : Fin d,
      Pi.single ⟨i.val + t.val, by omega⟩ (1 : ℤ)) +
      Pi.single (Fin.last m) (1 : ℤ) - Pi.single ⟨m - 1, by omega⟩ (1 : ℤ)
  refine ⟨v, ?_⟩
  have hsum : toStdD (m + 1) (∑ t : Fin d,
      Pi.single ⟨i.val + t.val, by omega⟩ (1 : ℤ)) =
      ∑ t : Fin d,
        toStdD (m + 1) (Pi.single ⟨i.val + t.val, by omega⟩ (1 : ℤ)) := by
    change (ct_od2_toStdDAddHom (m + 1)) (∑ t : Fin d,
        Pi.single ⟨i.val + t.val, by omega⟩ (1 : ℤ)) =
      ∑ t : Fin d, (ct_od2_toStdDAddHom (m + 1))
        (Pi.single ⟨i.val + t.val, by omega⟩ (1 : ℤ))
    exact map_sum _ _ _
  have htelescope := ct_od2_telescope m d i (by
    dsimp [d]
    omega)
  have hlast : toStdD (m + 1) (Pi.single (Fin.last m) (1 : ℤ)) =
      Pi.single ⟨m - 1, by omega⟩ 1 + Pi.single (Fin.last m) 1 := by
    simpa using toStdD_single_of_not_lt (m + 1) (k := Fin.last m) (by
      simp only [Fin.val_last]
      omega) (by omega)
  have hprev : toStdD (m + 1) (Pi.single ⟨m - 1, by omega⟩ (1 : ℤ)) =
      Pi.single ⟨m - 1, by omega⟩ 1 - Pi.single (Fin.last m) 1 := by
    have hlt : (⟨m - 1, by omega⟩ : Fin (m + 1)).val + 1 < m + 1 := by
      simp only
      omega
    have h := toStdD_single_of_lt (m + 1) (k := ⟨m - 1, by omega⟩) hlt
    have he : (⟨(⟨m - 1, by omega⟩ : Fin (m + 1)).val + 1, hlt⟩ : Fin (m + 1)) =
        Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    simpa [he] using h
  change toStdD (m + 1) ((2 : ℤ) • (∑ t : Fin d,
      Pi.single ⟨i.val + t.val, by omega⟩ (1 : ℤ)) +
      Pi.single (Fin.last m) (1 : ℤ) - Pi.single ⟨m - 1, by omega⟩ (1 : ℤ)) =
    (2 : ℤ) • Pi.single i 1
  rw [sub_eq_add_neg, toStdD_add, toStdD_add, toStdD_neg, toStdD_smul,
    hsum, htelescope, hlast, hprev]
  have hd : i.val + d = m := by dsimp [d]; omega
  have hi : (⟨i.val + d, by omega⟩ : Fin (m + 1)) = Fin.last m :=
    Fin.ext (by simp only [Fin.val_last]; omega)
  rw [hi]
  module

private theorem ct_od2_rep_unique (m : ℕ) (hm : 1 ≤ m)
    {w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group}
    {π π' : Equiv.Perm (Fin (m + 1))} {s s' : Fin (m + 1) → ℤ}
    (hs : ∀ c, s c = 1 ∨ s c = -1) (hs' : ∀ c, s' c = 1 ∨ s' c = -1)
    (h : ct_od2_Rep m w π s) (h' : ct_od2_Rep m w π' s') :
    π = π' ∧ s = s' := by
  have hkey : ∀ i : Fin (m + 1), ∀ c : Fin (m + 1), (π c = i ↔ π' c = i) := by
    intro i c
    obtain ⟨v, hv⟩ := ct_od2_toStdD_two_single m hm i
    have H := congrFun ((h v).symm.trans (h' v)) c
    rw [hv] at H
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul] at H
    constructor
    · intro h1
      by_contra h2
      rw [if_pos h1, if_neg h2] at H
      rcases hs c with hs1 | hs1 <;> rcases hs' c with hs2 | hs2 <;>
        rw [hs1, hs2] at H <;> norm_num at H
    · intro h2
      by_contra h1
      rw [if_neg h1, if_pos h2] at H
      rcases hs c with hs1 | hs1 <;> rcases hs' c with hs2 | hs2 <;>
        rw [hs1, hs2] at H <;> norm_num at H
  have hπ : π = π' := by
    apply Equiv.ext
    intro c
    have := (hkey (π c) c).mp rfl
    exact this.symm
  refine ⟨hπ, ?_⟩
  rw [← hπ] at h'
  funext c
  obtain ⟨v, hv⟩ := ct_od2_toStdD_two_single m hm (π c)
  have H := congrFun ((h v).symm.trans (h' v)) c
  rw [hv] at H
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul] at H
  simp only [if_true] at H
  have h2 : s c * 2 = s' c * 2 := by simpa using H
  exact mul_right_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

theorem card_coxeterD_eq (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (ggCoxeterMatrixD n).Group = 2 ^ (n - 1) * n.factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  rw [Nat.add_sub_cancel]
  have hupper : Nat.card (ggCoxeterMatrixD (m + 1)).Group ≤
      2 ^ m * (m + 1).factorial := by
    simpa using CFSG.StandardType.SpJoinRefl.card_coxeterD_le (m + 1) (by omega)
  rw [ct_od2_coxeterMatrixD_eq] at hupper
  rw [ct_od2_coxeterMatrixD_eq]
  classical
  let X := Equiv.Perm (Fin (m + 1)) × (Fin m → Bool)
  have hcardX : Nat.card X = 2 ^ m * (m + 1).factorial := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
    ring
  have hex : ∀ q : X, ∃ w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group,
      ct_od2_Rep m w q.1 (ct_od2_signOf m q.2) := by
    rintro ⟨σ, bits⟩
    obtain ⟨ws, hws⟩ := ct_od2_realizes_pure_sign m hm (ct_od2_signOf m bits)
      (ct_od2_signOf_pm m bits) (ct_od2_signOf_prod m bits)
    obtain ⟨wσ, hwσ⟩ := ct_od2_realizes_perm m σ
    refine ⟨ws * wσ, ?_⟩
    have h := ct_od2_rep_mul m hwσ hws
    convert h using 2
    · ext c
      simp
    · ring
  choose F hF using hex
  have hfin : Finite (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group := by
    classical
    have key : ∀ w : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group,
        ∃ q : Equiv.Perm (Fin (m + 1)) × (Fin (m + 1) → ℤ),
          (∀ c, q.2 c = 1 ∨ q.2 c = -1) ∧ (∏ c, q.2 c = 1) ∧
            ct_od2_Rep m w q.1 q.2 := by
      intro w
      obtain ⟨π, s, hs, hprod, hrep⟩ :=
        exists_signedPerm_toStdD_weylAction (m := m + 1) (by omega) w
      exact ⟨(π, s), hs, hprod, hrep⟩
    choose q hq using key
    let g : (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group →
        Equiv.Perm (Fin (m + 1)) × (Fin m → Bool) :=
      fun w => ((q w).1, fun j => decide ((q w).2 j.castSucc = 1))
    have hg : Function.Injective g := by
      intro w w' hww
      have hπ : (q w).1 = (q w').1 := (Prod.ext_iff.mp hww).1
      have hbits : (fun j : Fin m => decide ((q w).2 j.castSucc = 1)) =
          (fun j : Fin m => decide ((q w').2 j.castSucc = 1)) := (Prod.ext_iff.mp hww).2
      have hcast : ∀ j : Fin m, (q w).2 j.castSucc = (q w').2 j.castSucc := by
        intro j
        have h := congrFun hbits j
        simp only [decide_eq_decide] at h
        rcases (hq w).1 j.castSucc with h1 | h1 <;>
          rcases (hq w').1 j.castSucc with h2 | h2
        · rw [h1, h2]
        · rw [h1] at h
          rw [h2] at h
          exact absurd h (by norm_num)
        · rw [h1] at h
          rw [h2] at h
          exact absurd h (by norm_num)
        · rw [h1, h2]
      have hs : (q w).2 = (q w').2 := by
        funext c
        refine Fin.lastCases ?_ (fun j => hcast j) c
        have hprodw : (∏ j : Fin m, (q w).2 j.castSucc) * (q w).2 (Fin.last m) = 1 := by
          rw [← Fin.prod_univ_castSucc]
          exact (hq w).2.1
        have hprodw' : (∏ j : Fin m, (q w).2 j.castSucc) * (q w').2 (Fin.last m) = 1 := by
          rw [Finset.prod_congr rfl (fun j _ => hcast j)]
          rw [← Fin.prod_univ_castSucc]
          exact (hq w').2.1
        have hP : (∏ j : Fin m, (q w).2 j.castSucc) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro j _
          rcases (hq w).1 j.castSucc with h | h <;> rw [h] <;> norm_num
        exact mul_left_cancel₀ hP (by rw [hprodw, hprodw'])
      apply weylAction_injective (isFiniteType_cartanD (m + 1))
      refine LinearMap.ext fun v => toStdD_injective (m + 1) ?_
      rw [(hq w).2.2 v, (hq w').2.2 v, hs, hπ]
    exact Finite.of_injective g hg
  have hF_inj : Function.Injective F := by
    rintro ⟨σ, bits⟩ ⟨σ', bits'⟩ hFF
    have h1 := hF (σ, bits)
    have h2 := hF (σ', bits')
    rw [← hFF] at h2
    have hsig := ct_od2_rep_unique m hm (ct_od2_signOf_pm m bits)
      (ct_od2_signOf_pm m bits') h1 h2
    have hσ : σ = σ' := hsig.1
    have ht : ct_od2_signOf m bits = ct_od2_signOf m bits' := hsig.2
    have hb : bits = bits' := ct_od2_signOf_inj m ht
    rw [hσ, hb]
  have hlower : 2 ^ m * (m + 1).factorial ≤
      Nat.card (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group := by
    rw [← hcardX]
    exact @Nat.card_le_card_of_injective X
      (coxeterMatrix (isFiniteType_cartanD (m + 1))).Group hfin F hF_inj
  exact le_antisymm hupper hlower

private theorem ct_od2_fact_ne_twelve (k : ℕ) (hk : 2 ≤ k) : k.factorial ≠ 12 := by
  by_cases hk4 : k ≤ 4
  · interval_cases k <;> norm_num
  · have h5 : 5 ≤ k := by omega
    have hfac : Nat.factorial 5 ≤ k.factorial := Nat.factorial_le h5
    norm_num at hfac
    omega

private theorem ct_od2_two_pow_fact_ne_twelve (k : ℕ) (hk : 2 ≤ k) :
    2 ^ k * k.factorial ≠ 12 := by
  by_cases hk3 : k ≤ 3
  · interval_cases k <;> norm_num
  · have h4 : 4 ≤ k := by omega
    have hpow : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h4
    have hfac : Nat.factorial 4 ≤ k.factorial := Nat.factorial_le h4
    have hbig : 2 ^ 4 * Nat.factorial 4 ≤ 2 ^ k * k.factorial :=
      Nat.mul_le_mul hpow hfac
    norm_num at hbig
    omega

private theorem ct_od2_card_coxeterE6 :
    Nat.card (CoxeterMatrix.E₆).Group = 51840 := by
  have hC : GGIntCartan CoxeterMatrix.E₆ (CFSG.Blueprint.Chevalley.Tag.cartan .E6) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) = CoxeterMatrix.E₆ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) hC
  have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E6) = 51840 :=
    CFSG.StandardType.NoOffExc.card_weyl_E6
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (CFSG.LieType.Chevalley.isFiniteType_cartan .E6)).Group) = 51840 at h
  rw [hM] at h
  exact h

private theorem ct_od2_card_coxeterE7 :
    Nat.card (CoxeterMatrix.E₇).Group = 2903040 := by
  have hC : GGIntCartan CoxeterMatrix.E₇ (CFSG.Blueprint.Chevalley.Tag.cartan .E7) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) = CoxeterMatrix.E₇ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) hC
  have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E7) = 2903040 :=
    CFSG.StandardType.NoOffExc.card_weyl_E7
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (CFSG.LieType.Chevalley.isFiniteType_cartan .E7)).Group) = 2903040 at h
  rw [hM] at h
  exact h

private theorem ct_od2_card_coxeterE8 :
    Nat.card (CoxeterMatrix.E₈).Group = 696729600 := by
  have hC : GGIntCartan CoxeterMatrix.E₈ (CFSG.Blueprint.Chevalley.Tag.cartan .E8) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) = CoxeterMatrix.E₈ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) hC
  have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E8) = 696729600 :=
    CFSG.StandardType.NoOffExc.card_weyl_E8
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (CFSG.LieType.Chevalley.isFiniteType_cartan .E8)).Group) = 696729600 at h
  rw [hM] at h
  exact h

private theorem ct_od2_card_coxeterF4 :
    Nat.card (CoxeterMatrix.F₄).Group = 1152 := by
  have hC : GGIntCartan CoxeterMatrix.F₄ (CFSG.Blueprint.Chevalley.Tag.cartan .F4) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) hC
  have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .F4) = 1152 :=
    CFSG.Monster.B.Geometry.card_f4WeylGroup
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).Group) = 1152 at h
  rw [hM] at h
  exact h

theorem card_ne_twelve_of_weyl
    {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (h : GGWeylReflectionGroup p A) (hG2 : ¬ GGWeylOfType p CoxeterMatrix.G₂ A) : Nat.card ↥A ≠ 12 := by
  intro h12
  rcases ggWeylReflectionGroup_cases h with ⟨k, hk, hT⟩ | ⟨k, hk, hT⟩ | ⟨k, hk, hT⟩ |
    hT | hT | hT | hT | hT
  · have hcard := CFSG.StandardType.ggWeylOfType_A_card hT
    rw [hcard] at h12
    exact ct_od2_fact_ne_twelve (k + 1) (by omega) h12
  · obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 2 ^ k * k.factorial := by
      rw [← Nat.card_congr e.toEquiv]
      exact le_antisymm (card_coxeterB_le k) (CFSG.StandardType.SpFrame.card_coxeterB_ge k hk)
    rw [hcard] at h12
    exact ct_od2_two_pow_fact_ne_twelve k hk h12
  · obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 2 ^ (k - 1) * k.factorial := by
      rw [← Nat.card_congr e.toEquiv]
      exact card_coxeterD_eq k hk
    rw [hcard] at h12
    have hbig : 192 ≤ 2 ^ (k - 1) * k.factorial := by
      have hp : 2 ^ 3 ≤ 2 ^ (k - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hf : Nat.factorial 4 ≤ k.factorial := Nat.factorial_le hk
      have h := Nat.mul_le_mul hp hf
      norm_num at h ⊢
      exact h
    omega
  · obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 51840 := by
      rw [← Nat.card_congr e.toEquiv, ct_od2_card_coxeterE6]
    rw [hcard] at h12
    norm_num at h12
  · obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 2903040 := by
      rw [← Nat.card_congr e.toEquiv, ct_od2_card_coxeterE7]
    rw [hcard] at h12
    norm_num at h12
  · obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 696729600 := by
      rw [← Nat.card_congr e.toEquiv, ct_od2_card_coxeterE8]
    rw [hcard] at h12
    norm_num at h12
  · obtain ⟨e, -⟩ := hT
    have hcard : Nat.card ↥A = 1152 := by
      rw [← Nat.card_congr e.toEquiv, ct_od2_card_coxeterF4]
    rw [hcard] at h12
    norm_num at h12
  · exact absurd hT hG2

end CFSG.StandardType.OrthF3

end
