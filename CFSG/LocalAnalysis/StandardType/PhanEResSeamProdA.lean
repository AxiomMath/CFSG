module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeam

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.AGLEmbeddingD2.ParabLevi
open scoped commutatorElement

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

section Generation

variable {F : Type} [Field F] {m : ℕ}

private theorem hmbSP_hchain_mem {T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)}
    {a b : SpecialLinearGroup (Fin (m + 1)) F} (ha : a ∈ T) (hb : b ∈ T) :
    ⁅a, b⁆ ∈ T := by
  rw [commutatorElement_def]
  exact T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb)

private theorem hmbSP_tv_mem_closure_upper (T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F))
    (hgen : ∀ k : Fin m, ∀ c : F,
      tv F k.castSucc k.succ c ∈ T ∧ tv F k.succ k.castSucc c ∈ T) :
    ∀ (i j : Fin (m + 1)), i < j → ∀ c : F, tv F i j c ∈ T := by
  have H : ∀ d : ℕ, ∀ (i j : Fin (m + 1)), i < j → j.val - i.val = d →
      ∀ c : F, tv F i j c ∈ T := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i j hij hd c
      by_cases hstep : j.val = i.val + 1
      · have hm : i.val < m := by omega
        have hk : (⟨i.val, hm⟩ : Fin m).castSucc = i := by ext; simp
        have hk' : (⟨i.val, hm⟩ : Fin m).succ = j := by
          ext; simp [Fin.val_succ]; omega
        rw [← hk, ← hk']
        exact (hgen ⟨i.val, hm⟩ c).1
      · have hlt : (i.val + 1) < m + 1 := by omega
        let p : Fin (m + 1) := ⟨i.val + 1, hlt⟩
        have hip : i < p := by simp [p, Fin.lt_def]
        have hpj : p < j := by simp [p, Fin.lt_def]; omega
        have hpm : i.val < m := by omega
        have hkp : (⟨i.val, hpm⟩ : Fin m).castSucc = i := by ext; simp
        have hkp' : (⟨i.val, hpm⟩ : Fin m).succ = p := by
          ext; simp [Fin.val_succ, p]
        have h1 : tv F i p c ∈ T := by
          rw [← hkp, ← hkp']; exact (hgen ⟨i.val, hpm⟩ c).1
        have h2 : tv F p j 1 ∈ T :=
          ih (j.val - p.val) (by simp [p] at hd ⊢; omega) p j hpj rfl 1
        have hchain := tv_chain (F := F) (i := i) (j := p) (l := j)
          (ne_of_lt hip) (ne_of_lt hpj) (ne_of_lt (lt_trans hip hpj)) c 1
        rw [mul_one] at hchain
        rw [← hchain]
        exact hmbSP_hchain_mem h1 h2
  intro i j hij c
  exact H (j.val - i.val) i j hij rfl c

private theorem hmbSP_tv_mem_closure_lower (T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F))
    (hgen : ∀ k : Fin m, ∀ c : F,
      tv F k.castSucc k.succ c ∈ T ∧ tv F k.succ k.castSucc c ∈ T) :
    ∀ (i j : Fin (m + 1)), j < i → ∀ c : F, tv F i j c ∈ T := by
  have H : ∀ d : ℕ, ∀ (i j : Fin (m + 1)), j < i → i.val - j.val = d →
      ∀ c : F, tv F i j c ∈ T := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i j hji hd c
      by_cases hstep : i.val = j.val + 1
      · have hm : j.val < m := by omega
        have hk : (⟨j.val, hm⟩ : Fin m).castSucc = j := by ext; simp
        have hk' : (⟨j.val, hm⟩ : Fin m).succ = i := by
          ext; simp [Fin.val_succ]; omega
        rw [← hk, ← hk']
        exact (hgen ⟨j.val, hm⟩ c).2
      · have hlt : (j.val + 1) < m + 1 := by omega
        let p : Fin (m + 1) := ⟨j.val + 1, hlt⟩
        have hjp : j < p := by simp [p, Fin.lt_def]
        have hpi : p < i := by simp [p, Fin.lt_def]; omega
        have hpm : j.val < m := by omega
        have hkp : (⟨j.val, hpm⟩ : Fin m).castSucc = j := by ext; simp
        have hkp' : (⟨j.val, hpm⟩ : Fin m).succ = p := by
          ext; simp [Fin.val_succ, p]
        have h1 : tv F p j 1 ∈ T := by
          rw [← hkp, ← hkp']; exact (hgen ⟨j.val, hpm⟩ 1).2
        have h2 : tv F i p c ∈ T :=
          ih (i.val - p.val) (by simp [p] at hd ⊢; omega) i p hpi rfl c
        have hchain := tv_chain (F := F) (i := i) (j := p) (l := j)
          (ne_of_gt hpi) (ne_of_gt hjp) (ne_of_lt (lt_trans hjp hpi)).symm c 1
        rw [mul_one] at hchain
        rw [← hchain]
        exact hmbSP_hchain_mem h2 h1
  intro i j hji c
  exact H (i.val - j.val) i j hji rfl c

private theorem hmbSP_tv_mem_closure (T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F))
    (hgen : ∀ k : Fin m, ∀ c : F,
      tv F k.castSucc k.succ c ∈ T ∧ tv F k.succ k.castSucc c ∈ T) :
    ∀ (i j : Fin (m + 1)), i ≠ j → ∀ c : F, tv F i j c ∈ T := by
  intro i j hij c
  rcases lt_or_gt_of_ne hij with h | h
  · exact hmbSP_tv_mem_closure_upper T hgen i j h c
  · exact hmbSP_tv_mem_closure_lower T hgen i j h c

theorem hmbSP_closure_simple_eq_top :
    Subgroup.closure {A : SpecialLinearGroup (Fin (m + 1)) F | ∃ k : Fin m, ∃ c : F,
      A = tv F k.castSucc k.succ c ∨ A = tv F k.succ k.castSucc c} = ⊤ := by
  let T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    Subgroup.closure {A | ∃ k : Fin m, ∃ c : F,
      A = tv F k.castSucc k.succ c ∨ A = tv F k.succ k.castSucc c}
  have hgen : ∀ k : Fin m, ∀ c : F,
      tv F k.castSucc k.succ c ∈ T ∧ tv F k.succ k.castSucc c ∈ T := by
    intro k c
    exact ⟨Subgroup.subset_closure ⟨k, c, Or.inl rfl⟩,
      Subgroup.subset_closure ⟨k, c, Or.inr rfl⟩⟩
  have htv : ∀ (i j : Fin (m + 1)), i ≠ j → ∀ c : F, tv F i j c ∈ T :=
    hmbSP_tv_mem_closure T hgen
  rw [eq_top_iff]
  intro A _
  by_cases hm : m = 0
  · subst hm
    haveI : Subsingleton (SpecialLinearGroup (Fin (0 + 1)) F) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : (a : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F) = 1 := by
        ext i j
        fin_cases i; fin_cases j
        have h := a.2
        rw [Matrix.det_fin_one] at h
        simpa using h
      have hb : (b : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F) = 1 := by
        ext i j
        fin_cases i; fin_cases j
        have h := b.2
        rw [Matrix.det_fin_one] at h
        simpa using h
      rw [ha, hb]
    rw [Subsingleton.elim A 1]
    exact T.one_mem
  · haveI : Nontrivial (Fin (m + 1)) := by
      rw [Fin.nontrivial_iff_two_le]; omega
    refine SpecialLinearGroup.diagonal_transvection_induction' (fun x => x ∈ T) A ?_ ?_ ?_
    · intro i j hij c hc
      rw [SpecialLinearGroup.diag2n_decompose hij c hc]
      refine T.mul_mem (T.mul_mem (T.mul_mem (T.mul_mem (T.mul_mem ?_ ?_) ?_) ?_) ?_) ?_
      · simpa [tv_of_ne hij] using htv i j hij c
      · simpa [tv_of_ne hij.symm] using htv j i hij.symm (-c⁻¹)
      · simpa [tv_of_ne hij] using htv i j hij c
      · simpa [tv_of_ne hij] using htv i j hij (-1)
      · simpa [tv_of_ne hij.symm] using htv j i hij.symm 1
      · simpa [tv_of_ne hij] using htv i j hij (-1)
    · intro i j hij c
      simpa [tv_of_ne hij] using htv i j hij c
    · intro a b ha hb
      exact T.mul_mem ha hb

end Generation

section Commute

variable {i j : Fin D.rank}

private theorem hmbSP_root_apply_mul_apply_nonneg {ε : Fin D.rank → ℤ} (hε : ε ∈ D.roots)
    (i j : Fin D.rank) : 0 ≤ ε i * ε j := by
  rcases (RootSystem.ofCartan D.isFiniteType D.divisible).sign ε hε with h | h
  · exact mul_nonneg (h i) (h j)
  · nlinarith [h i, h j]

private theorem hmbSP_pair_apply_left (hij : i ≠ j) (z : ℤ × ℤ) :
    pair i j z i = z.1 := by
  simp [pair_apply, hij]

private theorem hmbSP_pair_apply_right (hij : i ≠ j) (z : ℤ × ℤ) :
    pair i j z j = z.2 := by
  simp [pair_apply, hij.symm]

private theorem hmbSP_pair_reflection_mem_roots {i j : Fin D.rank} {z : ℤ × ℤ}
    (hz : pair i j z ∈ D.roots) :
    pair i j (-z.1 - D.cartan i j * z.2, z.2) ∈ D.roots := by
  have := (RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem i _ hz
  rwa [RootSystem.ofCartan_refl_apply,
    reflection_pair_left j (D.isFiniteType.apply_self i)] at this

private theorem hmbSP_nsmul_add_nsmul_eq_pair (i j : Fin D.rank) (σ τ : ℤ) (a b : ℕ) :
    a • (σ • (Pi.single i 1 : Fin D.rank → ℤ)) + b • (τ • (Pi.single j 1 : Fin D.rank → ℤ)) =
      pair i j ((a : ℤ) * σ, (b : ℤ) * τ) := by
  rw [pair_apply, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]

private theorem hmbSP_openCone_eq_empty_of_cartan_eq_zero {i j : Fin D.rank} (hij : i ≠ j)
    (hA : D.cartan i j = 0) {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    openCone D.roots (σ • Pi.single i 1) (τ • Pi.single j 1) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  rw [hmbSP_nsmul_add_nsmul_eq_pair] at hε
  have h1 := hmbSP_root_apply_mul_apply_nonneg hε i j
  have h2 := hmbSP_root_apply_mul_apply_nonneg (hmbSP_pair_reflection_mem_roots hε) i j
  rw [hmbSP_pair_apply_left hij, hmbSP_pair_apply_right hij] at h1 h2
  simp only [hA, zero_mul, sub_zero] at h2
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> nlinarith

private theorem hmbSP_linIndepPair_single {i j : Fin D.rank} (hij : i ≠ j) {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    LinIndepPair (σ • (Pi.single i 1 : Fin D.rank → ℤ))
      (τ • (Pi.single j 1 : Fin D.rank → ℤ)) := by
  intro a b h
  have h1 := congrFun h i
  have h2 := congrFun h j
  simp [hij, hij.symm] at h1 h2
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp_all

private theorem hmbSP_commutes_rootGroup_of_cartan_eq_zero (hext : SteinbergExtras D n H)
    {i j : Fin D.rank} (hij : i ≠ j) (hA : D.cartan i j = 0) {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    ∀ x ∈ D.rootGroup (σ • Pi.single i 1), ∀ y ∈ D.rootGroup (τ • Pi.single j 1),
      x * y = y * x := by
  have hroot : ∀ (k : Fin D.rank) (s : ℤ), (s = 1 ∨ s = -1) →
      s • (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := by
    intro k s hs
    have h1 : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
    rcases hs with rfl | rfl
    · simpa using h1
    · simpa using (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ h1
  intro x hx y hy
  have h := hext.commutator_mem _ (hroot i σ hσ) _ (hroot j τ hτ)
    (hmbSP_linIndepPair_single hij hσ hτ) x hx y hy
  rw [hmbSP_openCone_eq_empty_of_cartan_eq_zero hij hA hσ hτ] at h
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

private theorem hmbSP_commutes_sup_left {A A' B : Subgroup K}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (h' : ∀ x ∈ A', ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ A', ∀ y ∈ B, x * y = y * x := by
  have hA : A ≤ Subgroup.centralizer (B : Set K) := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (h z hz w hw).symm
  have hA' : A' ≤ Subgroup.centralizer (B : Set K) := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (h' z hz w hw).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 ((sup_le hA hA') hx) y hy).symm

private theorem hmbSP_commutes_sup_right {A B B' : Subgroup K}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (h' : ∀ x ∈ A, ∀ y ∈ B', x * y = y * x) :
    ∀ x ∈ A, ∀ y ∈ B ⊔ B', x * y = y * x := by
  intro x hx
  have hB : B ≤ Subgroup.centralizer ({x} : Set K) := fun y hy => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact h x hx y hy
  have hB' : B' ≤ Subgroup.centralizer ({x} : Set K) := fun y hy => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact h' x hx y hy
  intro y hy
  exact Subgroup.mem_centralizer_iff.1 ((sup_le hB hB') hy) x (Set.mem_singleton x)

theorem hmbSP_commutes_rankOne_of_cartan (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hij : i ≠ j) (hA : D.cartan i j = 0) :
    ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup j, x * y = y * x := by
  have hroot : ∀ σ τ : ℤ, (σ = 1 ∨ σ = -1) → (τ = 1 ∨ τ = -1) →
      ∀ x ∈ D.rootGroup (σ • Pi.single i 1), ∀ y ∈ D.rootGroup (τ • Pi.single j 1),
        x * y = y * x :=
    fun σ τ hσ hτ => hmbSP_commutes_rootGroup_of_cartan_eq_zero hext hij hA hσ hτ
  have h1 : ∀ σ : ℤ, (σ = 1 ∨ σ = -1) →
      ∀ x ∈ D.rootGroup (σ • Pi.single i 1), ∀ y ∈ rankOne D.rootGroup j, x * y = y * x :=
    fun σ hσ => hmbSP_commutes_sup_right (by simpa using hroot σ 1 hσ (Or.inl rfl))
      (by simpa using hroot σ (-1) hσ (Or.inr rfl))
  exact hmbSP_commutes_sup_left (by simpa using h1 1 (Or.inl rfl))
    (by simpa using h1 (-1) (Or.inr rfl))

end Commute

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
