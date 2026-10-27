module

public import CFSG.Quasithin.Background.G92Lin

public section

namespace CFSG.Quasithin.G92

open CFSG.Quasithin.SzN31 CFSG.Quasithin.SzN31.CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ι : Type}

@[expose] def Rsp (F : Frame V ι) (i : ι) : Submodule (ZMod 2) V := commSp V (F.x i) ⊤

@[expose] def Wsp (F : Frame V ι) (i : ι) : Submodule (ZMod 2) V :=
  fixSp V (F.a i) (commSp V (F.x i) ⊤)

@[expose] def Nb (F : Frame V ι) (i j : ι) : Prop := ∃ w ∈ Rsp F i, F.x j w ≠ w

@[expose] def Nw (F : Frame V ι) (i j : ι) : Prop := ∃ w ∈ Wsp F i, F.x j w ≠ w

section Basic

variable (F : Frame V ι)

theorem Rsp_x_inv (i j : ι) : ∀ v ∈ Rsp F i, F.x j v ∈ Rsp F i := by
  by_cases hji : j = i
  · subst hji
    exact peel_T_x F j (fun s _ => Submodule.mem_top)
  · exact commSp_invariant (F.xx j i hji) (fun s _ => Submodule.mem_top)

theorem Rsp_a_inv (i j : ι) : ∀ v ∈ Rsp F i, F.a j v ∈ Rsp F i := by
  by_cases hji : j = i
  · subst hji
    exact peel_T_a F j (fun s _ => Submodule.mem_top) (fun s _ => Submodule.mem_top)
  · exact commSp_invariant (F.xa i j (Ne.symm hji)).symm (fun s _ => Submodule.mem_top)

theorem Rsp_fpf (i : ι) : ∀ v ∈ Rsp F i, F.x i v = v → v = 0 := by
  intro v hv hxv
  have h := peel_fix_T F i (S := ⊤) (fun s _ => Submodule.mem_top)
  have hmem : v ∈ fixSp V (F.x i) (commSp V (F.x i) ⊤) := mem_fixSp.2 ⟨hv, hxv⟩
  rw [h] at hmem
  exact (Submodule.mem_bot (ZMod 2)).1 hmem

theorem Rsp_ne_bot {i : ι} (h : F.x i ≠ 1) : Rsp F i ≠ ⊥ := by
  refine commSp_ne_bot ?_
  by_contra hcon
  push Not at hcon
  exact h (LinearEquiv.ext fun v => hcon v Submodule.mem_top)

theorem Wsp_le_Rsp (i : ι) : Wsp F i ≤ Rsp F i := fun w hw => (mem_fixSp.1 hw).1

theorem fix_Rsp_of_fix_Wsp {i j : ι} (hji : j ≠ i) (hW : ∀ w ∈ Wsp F i, F.x j w = w) :
    ∀ t ∈ Rsp F i, F.x j t = t := by
  obtain ⟨-, hsupT⟩ := peel_split F i (S := ⊤) (fun s _ => Submodule.mem_top)
    (fun s _ => Submodule.mem_top)
  intro t ht
  have ht' : t ∈ Wsp F i ⊔ (Wsp F i).map (F.x i : V →ₗ[ZMod 2] V) := by
    have : t ∈ commSp V (F.x i) ⊤ := ht
    rw [← hsupT] at this
    exact this
  exact fix_sup hW (fix_map (F.xx j i hji) hW) t ht'

theorem Nb_symm {i j : ι} (hij : i ≠ j) (h : Nb F i j) : Nb F j i := by
  by_contra hcon
  unfold Nb at hcon h
  push Not at hcon
  obtain ⟨w, hw, hne⟩ := h
  apply hne
  obtain ⟨v, -, rfl⟩ := mem_commSp.1 hw
  obtain ⟨-, hsup⟩ := decomp_fix_comm (F.x j) (frame_odd F j) (F.xpow j) ⊤
    (fun s _ => Submodule.mem_top)
  have hv : v ∈ fixSp V (F.x j) ⊤ ⊔ commSp V (F.x j) ⊤ := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨c, hc, r, hr, rfl⟩ := Submodule.mem_sup.1 hv
  have hxr : F.x i r = r := hcon r hr
  have hxc : F.x j c = c := (mem_fixSp.1 hc).2
  have hrew : F.x i (c + r) - (c + r) = F.x i c - c := by
    rw [map_add, hxr]
    abel
  rw [hrew, map_sub, comm_apply (F.xx j i hij.symm) c, hxc]

theorem Nb_of_Nw {i j : ι} (h : Nw F i j) : Nb F i j := by
  obtain ⟨w, hw, hne⟩ := h
  exact ⟨w, Wsp_le_Rsp F i hw, hne⟩

theorem Nw_of_Nb {i j : ι} (hji : j ≠ i) (h : Nb F i j) : Nw F i j := by
  by_contra hcon
  unfold Nw at hcon
  push Not at hcon
  obtain ⟨w, hw, hne⟩ := h
  exact hne (fix_Rsp_of_fix_Wsp F hji hcon w hw)

end Basic

section StepA

variable [Fintype ι] [DecidableEq ι] (F : Frame V ι)

open Classical in
@[expose] noncomputable def JW (i : ι) : Finset ι :=
  (Finset.univ.erase i).filter (fun j => Nw F i j)

theorem mem_JW {i j : ι} : j ∈ JW F i ↔ j ≠ i ∧ Nw F i j := by
  classical
  simp [JW]

theorem not_mem_JW_self (i : ι) : i ∉ JW F i := by
  simp [mem_JW]

theorem stepA (hx1 : ∀ i, F.x i ≠ 1)
    (hdim : Module.finrank (ZMod 2) V = ∑ j, gFun (F.p j)) (i : ι) :
    Module.finrank (ZMod 2) (Rsp F i) = gFun (F.p i) + ∑ j ∈ JW F i, gFun (F.p j) ∧
      ∑ j ∈ JW F i, gFun (F.p j) ≤ gFun (F.p i) := by
  classical
  have hadm : Adm F ⊤ Finset.univ := adm_top F Finset.univ (fun i _ => hx1 i)
  have hxS : ∀ s ∈ (⊤ : Submodule (ZMod 2) V), F.x i s ∈ (⊤ : Submodule (ZMod 2) V) :=
    fun s _ => Submodule.mem_top
  have haS : ∀ s ∈ (⊤ : Submodule (ZMod 2) V), F.a i s ∈ (⊤ : Submodule (ZMod 2) V) :=
    fun s _ => Submodule.mem_top
  set JU : Finset ι := (Finset.univ.erase i).filter (fun j => ¬ Nw F i j) with hJU
  have hAU : Adm F (fixSp V (F.x i) ⊤) JU := by
    intro j hj
    obtain ⟨hjE, hjW⟩ := Finset.mem_filter.1 hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hjE
    refine ⟨(peel_U_invariant F Finset.univ ⊤ hadm (Finset.mem_univ j) hji).1,
      (peel_U_invariant F Finset.univ ⊤ hadm (Finset.mem_univ j) hji).2, ?_⟩
    refine peel_U_nontrivial F Finset.univ ⊤ hadm (Finset.mem_univ i) (Finset.mem_univ j) hji ?_
    intro w hw
    by_contra hne
    exact hjW ⟨w, hw, hne⟩
  have hAW : Adm F (Wsp F i) (JW F i) := by
    intro j hj
    obtain ⟨hji, hNw⟩ := (mem_JW F).1 hj
    exact ⟨(peel_W_invariant F Finset.univ ⊤ hadm (Finset.mem_univ j) hji).1,
      (peel_W_invariant F Finset.univ ⊤ hadm (Finset.mem_univ j) hji).2, hNw⟩
  have h1 : ∑ j ∈ JU, gFun (F.p j) ≤ Module.finrank (ZMod 2) (fixSp V (F.x i) ⊤) :=
    dim_lemma F JU _ hAU
  have h2 : ∑ j ∈ JW F i, gFun (F.p j) ≤ Module.finrank (ZMod 2) (Wsp F i) :=
    dim_lemma F (JW F i) _ hAW
  have h3 : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (fixSp V (F.x i) ⊤) +
      2 * Module.finrank (ZMod 2) (Wsp F i) := by
    have := finrank_peel F i hxS haS
    rw [finrank_top] at this
    exact this
  have hT : Module.finrank (ZMod 2) (Rsp F i) =
      2 * Module.finrank (ZMod 2) (Wsp F i) :=
    dihedral_finrank (F.x i) (F.a i) (F.xpow i) (frame_odd F i) (F.asq i) (F.conj i)
      (commSp V (F.x i) ⊤) (peel_T_x F i hxS) (peel_T_a F i hxS haS) (peel_fix_T F i hxS)
  have hRne := Rsp_ne_bot F (hx1 i)
  have hAR : Adm F (Rsp F i) (insert i (JW F i)) := by
    intro j hj
    refine ⟨Rsp_x_inv F i j, Rsp_a_inv F i j, ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj'
    · by_contra hcon
      push Not at hcon
      apply hRne
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_bot]
      exact Rsp_fpf F j v hv (hcon v hv)
    · obtain ⟨-, w, hw, hne⟩ := (mem_JW F).1 hj'
      exact ⟨w, Wsp_le_Rsp F i hw, hne⟩
  have h4 : ∑ j ∈ insert i (JW F i), gFun (F.p j) ≤ Module.finrank (ZMod 2) (Rsp F i) :=
    dim_lemma F (insert i (JW F i)) (Rsp F i) hAR
  rw [Finset.sum_insert (not_mem_JW_self F i)] at h4
  have hsum : ∑ j, gFun (F.p j) =
      gFun (F.p i) + ∑ j ∈ JU, gFun (F.p j) + ∑ j ∈ JW F i, gFun (F.p j) := by
    have e1 := Finset.add_sum_erase Finset.univ (fun j => gFun (F.p j)) (Finset.mem_univ i)
    have e2 := Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (fun j => Nw F i j)
      (fun j => gFun (F.p j))
    have : ∑ j ∈ JW F i, gFun (F.p j) = ∑ j ∈ (Finset.univ.erase i).filter (fun j => Nw F i j),
        gFun (F.p j) := rfl
    rw [← e1, this, ← e2]
    ring
  rw [hsum] at hdim
  constructor <;> omega

end StepA

section Blocks

variable [Fintype ι] [DecidableEq ι] (F : Frame V ι)

theorem gFun_three : gFun 3 = 2 := by simp [gFun]

theorem gFun_five : gFun 5 = 4 := by simp [gFun]

structure PrimeShape (F : Frame V ι) (i₁ : ι) : Prop where
  three : ∀ j, j ≠ i₁ → F.p j = 3
  mem : F.p i₁ = 3 ∨ F.p i₁ = 5

variable {F}

theorem PrimeShape.p_cases {i₁ : ι} (h : PrimeShape F i₁) (j : ι) :
    F.p j = 3 ∨ (j = i₁ ∧ F.p j = 5) := by
  by_cases hj : j = i₁
  · subst hj
    rcases h.mem with h3 | h5
    · exact Or.inl h3
    · exact Or.inr ⟨rfl, h5⟩
  · exact Or.inl (h.three j hj)

theorem PrimeShape.p_cases' {i₁ : ι} (h : PrimeShape F i₁) (j : ι) : F.p j = 3 ∨ F.p j = 5 := by
  rcases h.p_cases j with h3 | ⟨-, h5⟩
  · exact Or.inl h3
  · exact Or.inr h5

theorem PrimeShape.p_eq_three_of_g_eq_two {i₁ : ι} (h : PrimeShape F i₁) {j : ι}
    (hg : gFun (F.p j) = 2) : F.p j = 3 := by
  rcases h.p_cases j with h3 | ⟨-, h5⟩
  · exact h3
  · rw [h5, gFun_five] at hg
    omega

variable (F)

theorem partner_pair (hx1 : ∀ i, F.x i ≠ 1)
    (hdim : Module.finrank (ZMod 2) V = ∑ j, gFun (F.p j)) {i₁ : ι} (hP : PrimeShape F i₁)
    {i j : ι} (hj : j ∈ JW F i) :
    JW F i = {j} ∧ JW F j = {i} ∧ F.p i = 3 ∧ F.p j = 3 := by
  classical
  obtain ⟨hji, hNw⟩ := (mem_JW F).1 hj
  have hNb : Nb F i j := Nb_of_Nw F hNw
  have hNb' : Nb F j i := Nb_symm F hji.symm hNb
  have hi : i ∈ JW F j := (mem_JW F).2 ⟨hji.symm, Nw_of_Nb F hji.symm hNb'⟩
  obtain ⟨-, hBi⟩ := stepA F hx1 hdim i
  obtain ⟨-, hBj⟩ := stepA F hx1 hdim j
  have hg2 : ∀ k, 2 ≤ gFun (F.p k) := fun k => gFun_ge_two (F.prime k) (F.odd k)
  have h1 : gFun (F.p j) ≤ ∑ k ∈ JW F i, gFun (F.p k) :=
    Finset.single_le_sum (f := fun k => gFun (F.p k)) (fun _ _ => Nat.zero_le _) hj
  have h2 : gFun (F.p i) ≤ ∑ k ∈ JW F j, gFun (F.p k) :=
    Finset.single_le_sum (f := fun k => gFun (F.p k)) (fun _ _ => Nat.zero_le _) hi
  have heq : gFun (F.p i) = gFun (F.p j) := by omega
  have huniq : ∀ {a b : ι}, b ∈ JW F a → gFun (F.p a) = gFun (F.p b) →
      ∑ k ∈ JW F a, gFun (F.p k) ≤ gFun (F.p a) → JW F a = {b} := by
    intro a b hb hg hle
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨hb, fun x hx => ?_⟩
    by_contra hxb
    have hsub : ({x, b} : Finset ι) ⊆ JW F a := by
      intro y hy
      rcases Finset.mem_insert.1 hy with hy' | hy'
      · rw [hy']
        exact hx
      · rw [Finset.mem_singleton] at hy'
        rw [hy']
        exact hb
    have hle2 := Finset.sum_le_sum_of_subset (f := fun k => gFun (F.p k)) hsub
    rw [Finset.sum_pair hxb] at hle2
    have := hg2 x
    omega
  have hpi : F.p i = 3 := by
    rcases hP.p_cases i with h3 | ⟨hi1, h5⟩
    · exact h3
    · exfalso
      have hj1 : j ≠ i₁ := fun h => hji (h.trans hi1.symm)
      have h3 := hP.three j hj1
      rw [h5, h3, gFun_five, gFun_three] at heq
      omega
  have hpj : F.p j = 3 := hP.p_eq_three_of_g_eq_two (by rw [← heq, hpi, gFun_three])
  exact ⟨huniq hj heq hBi, huniq hi heq.symm hBj, hpi, hpj⟩

variable {F}

@[expose] noncomputable def Bf (F : Frame V ι) (i : ι) : Finset ι := insert i (JW F i)

theorem mem_Bf_self (i : ι) : i ∈ Bf F i := Finset.mem_insert_self _ _

theorem Bf_of_mem_JW {i j : ι} (h : j ∈ JW F i) : j ∈ Bf F i := Finset.mem_insert_of_mem h

theorem sum_Bf (i : ι) : ∑ j ∈ Bf F i, gFun (F.p j) = gFun (F.p i) + ∑ j ∈ JW F i, gFun (F.p j) :=
  Finset.sum_insert (not_mem_JW_self F i)

variable (F)

theorem Rsp_eq_of_partner (hx1 : ∀ i, F.x i ≠ 1)
    (hdim : Module.finrank (ZMod 2) V = ∑ j, gFun (F.p j)) {i₁ : ι} (hP : PrimeShape F i₁)
    {i j : ι} (hj : j ∈ JW F i) : Rsp F j = Rsp F i := by
  classical
  obtain ⟨hJi, hJj, hpi, hpj⟩ := partner_pair F hx1 hdim hP hj
  have hji : j ≠ i := ((mem_JW F).1 hj).1
  have hNb : Nb F i j := Nb_of_Nw F ((mem_JW F).1 hj).2
  have hdi : Module.finrank (ZMod 2) (Rsp F i) = 4 := by
    have := (stepA F hx1 hdim i).1
    rw [hJi, Finset.sum_singleton, hpi, hpj, gFun_three] at this
    omega
  have hdj : Module.finrank (ZMod 2) (Rsp F j) = 4 := by
    have := (stepA F hx1 hdim j).1
    rw [hJj, Finset.sum_singleton, hpi, hpj, gFun_three] at this
    omega
  obtain ⟨w, hw, hne⟩ := hNb
  have hy : F.x j w - w ∈ Rsp F i ⊓ Rsp F j :=
    ⟨sub_mem (Rsp_x_inv F i j w hw) hw, mem_commSp.2 ⟨w, Submodule.mem_top, rfl⟩⟩
  have hy0 : F.x j w - w ≠ 0 := sub_ne_zero.2 hne
  have hAdm : Adm F (Rsp F i ⊓ Rsp F j) {i, j} := by
    intro k hk
    refine ⟨fun s hs => ⟨Rsp_x_inv F i k s hs.1, Rsp_x_inv F j k s hs.2⟩,
      fun s hs => ⟨Rsp_a_inv F i k s hs.1, Rsp_a_inv F j k s hs.2⟩, F.x j w - w, hy, ?_⟩
    rcases Finset.mem_insert.1 hk with hk' | hk'
    · rw [hk']
      intro hfix
      exact hy0 (Rsp_fpf F i _ hy.1 hfix)
    · rw [Finset.mem_singleton] at hk'
      rw [hk']
      intro hfix
      exact hy0 (Rsp_fpf F j _ hy.2 hfix)
  have hdl : ∑ k ∈ ({i, j} : Finset ι), gFun (F.p k) ≤
      Module.finrank (ZMod 2) (Rsp F i ⊓ Rsp F j : Submodule (ZMod 2) V) :=
    dim_lemma F {i, j} _ hAdm
  rw [Finset.sum_pair hji.symm, hpi, hpj, gFun_three] at hdl
  have hYi : Rsp F i ⊓ Rsp F j = Rsp F i :=
    Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  have hYj : Rsp F i ⊓ Rsp F j = Rsp F j :=
    Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
  rw [← hYj, hYi]

theorem x_trivial_off {i j : ι} (hj : j ∉ Bf F i) : ∀ w ∈ Rsp F i, F.x j w = w := by
  have hji : j ≠ i := by
    rintro rfl
    exact hj (mem_Bf_self _)
  have hjJW : j ∉ JW F i := fun h => hj (Bf_of_mem_JW h)
  refine fix_Rsp_of_fix_Wsp F hji ?_
  intro w hw
  by_contra hne
  exact hjJW ((mem_JW F).2 ⟨hji, w, hw, hne⟩)

theorem a_trivial_off (hx1 : ∀ i, F.x i ≠ 1)
    (hdim : Module.finrank (ZMod 2) V = ∑ j, gFun (F.p j)) {i₁ : ι} (hP : PrimeShape F i₁)
    {i j : ι} (hj : j ∉ Bf F i) : ∀ w ∈ Rsp F i, F.a j w = w := by
  classical
  have hji : j ≠ i := by
    rintro rfl
    exact hj (mem_Bf_self _)
  have hjJW : j ∉ JW F i := fun h => hj (Bf_of_mem_JW h)
  have hxS : ∀ s ∈ (⊤ : Submodule (ZMod 2) V), F.x i s ∈ (⊤ : Submodule (ZMod 2) V) :=
    fun s _ => Submodule.mem_top
  have haS : ∀ s ∈ (⊤ : Submodule (ZMod 2) V), F.a i s ∈ (⊤ : Submodule (ZMod 2) V) :=
    fun s _ => Submodule.mem_top
  have hT : Module.finrank (ZMod 2) (Rsp F i) = 2 * Module.finrank (ZMod 2) (Wsp F i) :=
    dihedral_finrank (F.x i) (F.a i) (F.xpow i) (frame_odd F i) (F.asq i) (F.conj i)
      (commSp V (F.x i) ⊤) (peel_T_x F i hxS) (peel_T_a F i hxS haS) (peel_fix_T F i hxS)
  by_cases hJ : JW F i = ∅
  · have hdimR : Module.finrank (ZMod 2) (Rsp F i) = gFun (F.p i) := by
      have := (stepA F hx1 hdim i).1
      rw [hJ, Finset.sum_empty] at this
      omega
    refine invol_trivial (F.prime i) (F.xpow i) (F.asq j) (F.xa i j hji.symm).symm (Rsp F i)
      (Rsp_x_inv F i i) (Rsp_a_inv F i j) (Rsp_fpf F i) ?_
    rcases hP.p_cases' i with h3 | h5
    · rw [h3]
      exact no_dvd_three (by rw [hdimR, h3, gFun_three]; omega)
    · rw [h5]
      exact no_dvd_five (by rw [hdimR, h5, gFun_five]; omega)
  · obtain ⟨i', hi'⟩ := Finset.nonempty_iff_ne_empty.2 hJ
    obtain ⟨hJi, -, hpi, hpi'⟩ := partner_pair F hx1 hdim hP hi'
    have hii' : i' ≠ i := ((mem_JW F).1 hi').1
    have hji' : j ≠ i' := by
      rintro rfl
      exact hjJW hi'
    have hdR : Module.finrank (ZMod 2) (Rsp F i) = 4 := by
      have := (stepA F hx1 hdim i).1
      rw [hJi, Finset.sum_singleton, hpi, hpi', gFun_three] at this
      omega
    have hdW : Module.finrank (ZMod 2) (Wsp F i) = 2 := by omega
    have hReq : Rsp F i' = Rsp F i := Rsp_eq_of_partner F hx1 hdim hP hi'
    have hWfix : ∀ w ∈ Wsp F i, F.a j w = w := by
      refine invol_trivial (F.prime i') (F.xpow i') (F.asq j) (F.xa i' j hji'.symm).symm
        (Wsp F i) ?_ ?_ ?_ ?_
      · exact peel_W_invariant_of_comm (F.xx i' i hii') (F.xa i' i hii') (S := ⊤)
          (fun s _ => Submodule.mem_top)
      · exact peel_W_invariant_of_comm (F.xa i j hji.symm).symm (F.aa j i hji) (S := ⊤)
          (fun s _ => Submodule.mem_top)
      · intro t ht hxt
        exact Rsp_fpf F i' t (hReq ▸ Wsp_le_Rsp F i ht) hxt
      · rw [hpi']
        exact no_dvd_three (by omega)
    obtain ⟨-, hsupT⟩ := peel_split F i (S := ⊤) hxS haS
    intro t ht
    have ht' : t ∈ Wsp F i ⊔ (Wsp F i).map (F.x i : V →ₗ[ZMod 2] V) := by
      have : t ∈ commSp V (F.x i) ⊤ := ht
      rw [← hsupT] at this
      exact this
    exact fix_sup hWfix (fix_map (F.xa i j hji.symm).symm hWfix) t ht'

end Blocks

theorem finrank_sup_of_supIndep {κ : Type*} [DecidableEq κ] (s : Finset κ)
    (U : κ → Submodule (ZMod 2) V) (h : s.SupIndep U) :
    Module.finrank (ZMod 2) (s.sup U : Submodule (ZMod 2) V) =
      ∑ k ∈ s, Module.finrank (ZMod 2) (U k) := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : s.SupIndep U := h.subset (Finset.subset_insert a s)
    have hdisj : Disjoint (U a) (s.sup U) :=
      h (Finset.subset_insert a s) (Finset.mem_insert_self a s) ha
    rw [Finset.sup_insert, Finset.sum_insert ha, ← ih hs]
    have := Submodule.finrank_sup_add_finrank_inf_eq (U a) (s.sup U)
    rw [hdisj.eq_bot, finrank_bot, add_zero] at this
    exact this

section Main

variable [Fintype ι] [DecidableEq ι]

structure BlockData (F : Frame V ι) (B : ι → Finset ι) : Prop where
  self_mem : ∀ i, i ∈ B i
  block_eq : ∀ i, ∀ j ∈ B i, B j = B i
  card_cases : ∀ i, (B i).card = 1 ∨ ((B i).card = 2 ∧ ∀ j ∈ B i, F.p j = 3)
  R_eq : ∀ i, ∀ j ∈ B i, Rsp F j = Rsp F i
  trivial_off : ∀ i j, j ∉ B i → ∀ w ∈ Rsp F i, F.x j w = w ∧ F.a j w = w
  sup_eq_top : ⨆ i, Rsp F i = ⊤
  indep : ∀ i, Disjoint (Rsp F i) (⨆ j ∈ {j | j ∉ B i}, Rsp F j)
  finrank_eq : ∀ i, Module.finrank (ZMod 2) (Rsp F i) = ∑ j ∈ B i, gFun (F.p j)

variable (F : Frame V ι)

theorem blockData (hx1 : ∀ i, F.x i ≠ 1)
    (hdim : Module.finrank (ZMod 2) V = ∑ j, gFun (F.p j)) {i₁ : ι} (hP : PrimeShape F i₁) :
    BlockData F (Bf F) := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hblock_eq : ∀ i, ∀ j ∈ Bf F i, Bf F j = Bf F i := by
    intro i j hj
    rcases Finset.mem_insert.1 hj with h | hj'
    · rw [h]
    · obtain ⟨hJi, hJj, -, -⟩ := partner_pair F hx1 hdim hP hj'
      simp only [Bf, hJi, hJj]
      exact Finset.pair_comm _ _
  have hcard : ∀ i, (Bf F i).card = 1 ∨ ((Bf F i).card = 2 ∧ ∀ j ∈ Bf F i, F.p j = 3) := by
    intro i
    by_cases hJ : JW F i = ∅
    · left
      simp [Bf, hJ]
    · right
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hJ
      obtain ⟨hJi, -, hpi, hpj⟩ := partner_pair F hx1 hdim hP hj
      have hji : j ≠ i := ((mem_JW F).1 hj).1
      have hB : Bf F i = {i, j} := by simp [Bf, hJi]
      rw [hB]
      refine ⟨Finset.card_pair hji.symm, ?_⟩
      intro k hk
      rcases Finset.mem_insert.1 hk with h | hk'
      · rw [h]
        exact hpi
      · rw [Finset.mem_singleton.1 hk']
        exact hpj
  have hReq : ∀ i, ∀ j ∈ Bf F i, Rsp F j = Rsp F i := by
    intro i j hj
    rcases Finset.mem_insert.1 hj with h | hj'
    · rw [h]
    · exact Rsp_eq_of_partner F hx1 hdim hP hj'
  have htriv : ∀ i j, j ∉ Bf F i → ∀ w ∈ Rsp F i, F.x j w = w ∧ F.a j w = w :=
    fun i j hj w hw => ⟨x_trivial_off F hj w hw, a_trivial_off F hx1 hdim hP hj w hw⟩
  have hsymm : ∀ i j, j ∉ Bf F i → i ∉ Bf F j := by
    intro i j hj hi
    apply hj
    have := hblock_eq j i hi
    rw [this]
    exact mem_Bf_self j
  have hindep : ∀ i, Disjoint (Rsp F i) (⨆ j ∈ {j | j ∉ Bf F i}, Rsp F j) := by
    intro i
    have hle : (⨆ j ∈ {j | j ∉ Bf F i}, Rsp F j) ≤ fixSp V (F.x i) ⊤ := by
      refine iSup₂_le fun j hj => ?_
      intro w hw
      exact mem_fixSp.2
        ⟨Submodule.mem_top, (htriv j i (hsymm i j (show j ∉ Bf F i from hj)) w hw).1⟩
    rw [Submodule.disjoint_def]
    intro v hv hv'
    exact Rsp_fpf F i v hv (mem_fixSp.1 (hle hv')).2
  let blocks : Finset (Finset ι) := Finset.univ.image (Bf F)
  let U : Finset ι → Submodule (ZMod 2) V := fun b => ⨆ k ∈ b, Rsp F k
  have hUB : ∀ i, U (Bf F i) = Rsp F i := by
    intro i
    refine le_antisymm (iSup₂_le fun k hk => (hReq i k hk).le) ?_
    exact le_iSup₂ (f := fun k (_ : k ∈ Bf F i) => Rsp F k) i (mem_Bf_self i)
  have hSup : blocks.SupIndep U := by
    intro t ht b hb hbt
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    rw [hUB]
    have hle : t.sup U ≤ fixSp V (F.x i) ⊤ := by
      refine Finset.sup_le fun b' hb' => ?_
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 (ht hb')
      rw [hUB]
      have hi : i ∉ Bf F i' := by
        intro hmem
        apply hbt
        have := hblock_eq i' i hmem
        rw [this]
        exact hb'
      intro w hw
      exact mem_fixSp.2 ⟨Submodule.mem_top, (htriv i' i hi w hw).1⟩
    rw [Submodule.disjoint_def]
    intro v hv hv'
    exact Rsp_fpf F i v hv (mem_fixSp.1 (hle hv')).2
  have hfr : ∀ i, Module.finrank (ZMod 2) (Rsp F i) = ∑ j ∈ Bf F i, gFun (F.p j) := by
    intro i
    rw [sum_Bf]
    exact (stepA F hx1 hdim i).1
  have hpd : (blocks : Set (Finset ι)).PairwiseDisjoint id := by
    intro b hb b' hb' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hb'
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro k hk hk'
    apply hne
    rw [← hblock_eq i k hk, ← hblock_eq i' k hk']
  have hsum : ∑ b ∈ blocks, Module.finrank (ZMod 2) (U b) = ∑ j, gFun (F.p j) := by
    have h1 : ∑ b ∈ blocks, Module.finrank (ZMod 2) (U b) =
        ∑ b ∈ blocks, ∑ j ∈ b, gFun (F.p j) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
      rw [hUB, hfr]
    have h2 : ∑ x ∈ blocks.biUnion id, gFun (F.p x) =
        ∑ b ∈ blocks, ∑ j ∈ b, gFun (F.p j) :=
      Finset.sum_biUnion (f := fun j => gFun (F.p j)) hpd
    have hcov : blocks.biUnion id = Finset.univ :=
      Finset.eq_univ_iff_forall.2 fun k => Finset.mem_biUnion.2
        ⟨Bf F k, Finset.mem_image_of_mem _ (Finset.mem_univ k), mem_Bf_self k⟩
    rw [h1, ← h2, hcov]
  have hdimsup : Module.finrank (ZMod 2) (blocks.sup U : Submodule (ZMod 2) V) =
      Module.finrank (ZMod 2) V := by
    rw [finrank_sup_of_supIndep blocks U hSup, hsum, hdim]
  have htop : blocks.sup U = ⊤ := Submodule.eq_top_of_finrank_eq hdimsup
  have hsup_le : blocks.sup U ≤ ⨆ i, Rsp F i := by
    refine Finset.sup_le fun b hb => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    rw [hUB]
    exact le_iSup (fun i => Rsp F i) i
  exact { self_mem := mem_Bf_self
          block_eq := hblock_eq
          card_cases := hcard
          R_eq := hReq
          trivial_off := htriv
          sup_eq_top := eq_top_iff.2 (by rw [← htop]; exact hsup_le)
          indep := hindep
          finrank_eq := hfr }

end Main

end CFSG.Quasithin.G92
