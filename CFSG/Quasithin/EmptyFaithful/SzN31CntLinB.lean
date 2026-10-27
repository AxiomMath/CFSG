module

public import CFSG.Quasithin.EmptyFaithful.SzN31CntLinA

public section

namespace CFSG.Quasithin.SzN31

namespace CntLin

section Invariance

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem comm_apply {c t : V ≃ₗ[ZMod 2] V} (h : c * t = t * c) (v : V) : c (t v) = t (c v) := by
  have := DFunLike.congr_fun h v
  rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this

theorem fixSp_invariant {c t : V ≃ₗ[ZMod 2] V} (h : c * t = t * c) {S : Submodule (ZMod 2) V}
    (hc : ∀ s ∈ S, c s ∈ S) : ∀ v ∈ fixSp V t S, c v ∈ fixSp V t S := by
  intro v hv
  obtain ⟨hvS, hvt⟩ := mem_fixSp.1 hv
  exact mem_fixSp.2 ⟨hc v hvS, by rw [← comm_apply h v, hvt]⟩

theorem commSp_invariant {c t : V ≃ₗ[ZMod 2] V} (h : c * t = t * c) {S : Submodule (ZMod 2) V}
    (hc : ∀ s ∈ S, c s ∈ S) : ∀ v ∈ commSp V t S, c v ∈ commSp V t S := by
  intro v hv
  obtain ⟨s, hs, rfl⟩ := mem_commSp.1 hv
  exact mem_commSp.2 ⟨c s, hc s hs, by rw [map_sub, comm_apply h]⟩

theorem commSp_le {t : V ≃ₗ[ZMod 2] V} {S : Submodule (ZMod 2) V} (h : ∀ s ∈ S, t s ∈ S) :
    commSp V t S ≤ S := by
  intro v hv
  obtain ⟨s, hs, rfl⟩ := mem_commSp.1 hv
  exact sub_mem (h s hs) hs

theorem fix_sup {c : V ≃ₗ[ZMod 2] V} {A B : Submodule (ZMod 2) V} (hA : ∀ v ∈ A, c v = v)
    (hB : ∀ v ∈ B, c v = v) : ∀ v ∈ A ⊔ B, c v = v := by
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hA a ha, hB b hb]

theorem fix_map {c x : V ≃ₗ[ZMod 2] V} (h : c * x = x * c) {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, c w = w) : ∀ v ∈ W.map (x : V →ₗ[ZMod 2] V), c v = v := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
  show c (x w) = x w
  rw [comm_apply h, hW w hw]

theorem commSp_invariant_a {x a : V ≃ₗ[ZMod 2] V} {p : ℕ} (hp : 0 < p) (hx : x ^ p = 1)
    (hax : a * x * a⁻¹ = x⁻¹) {S : Submodule (ZMod 2) V} (hxS : ∀ s ∈ S, x s ∈ S)
    (haS : ∀ s ∈ S, a s ∈ S) : ∀ v ∈ commSp V x S, a v ∈ commSp V x S := by
  intro v hv
  obtain ⟨s, hs, rfl⟩ := mem_commSp.1 hv
  have hu : -(x⁻¹ (a s)) ∈ S := S.neg_mem (inv_apply_mem hp hx hxS (haS s hs))
  refine mem_commSp.2 ⟨-(x⁻¹ (a s)), hu, ?_⟩
  rw [map_sub, dihedral_apply_x hax, map_neg, apply_inv_apply]
  abel

theorem fixSp_commSp_eq_bot {x : V ≃ₗ[ZMod 2] V} {p : ℕ} (hp : Odd p) (hx : x ^ p = 1)
    {S : Submodule (ZMod 2) V} (hxS : ∀ s ∈ S, x s ∈ S) :
    fixSp V x (commSp V x S) = ⊥ := by
  have hd := (decomp_fix_comm x hp hx S hxS).1
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvT, hvx⟩ := mem_fixSp.1 hv
  have hvS : v ∈ fixSp V x S := mem_fixSp.2 ⟨commSp_le hxS hvT, hvx⟩
  rw [Submodule.mem_bot]
  exact Submodule.disjoint_def.1 hd v hvS hvT

theorem commSp_ne_bot {x : V ≃ₗ[ZMod 2] V} {S : Submodule (ZMod 2) V} (h : ∃ s ∈ S, x s ≠ s) :
    commSp V x S ≠ ⊥ := by
  obtain ⟨s, hs, hne⟩ := h
  intro hbot
  have hmem : x s - s ∈ commSp V x S := mem_commSp.2 ⟨s, hs, rfl⟩
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hne hmem

theorem frame_odd {ι : Type} (F : Frame V ι) (i : ι) : Odd (F.p i) :=
  (F.prime i).odd_of_ne_two (F.odd i)

end Invariance

end CntLin

open CntLin

section Peel

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type}

theorem adm_top (F : Frame V ι) (J : Finset ι) (h : ∀ i ∈ J, F.x i ≠ 1) : Adm F ⊤ J := by
  intro i hi
  refine ⟨fun s _ => Submodule.mem_top, fun s _ => Submodule.mem_top, ?_⟩
  by_contra hcon
  push Not at hcon
  exact h i hi (LinearEquiv.ext fun v => hcon v Submodule.mem_top)

theorem peel_T_x (F : Frame V ι) (i : ι) {S : Submodule (ZMod 2) V}
    (hxS : ∀ s ∈ S, F.x i s ∈ S) :
    ∀ t ∈ commSp V (F.x i) S, F.x i t ∈ commSp V (F.x i) S :=
  commSp_invariant rfl hxS

theorem peel_T_a (F : Frame V ι) (i : ι) {S : Submodule (ZMod 2) V}
    (hxS : ∀ s ∈ S, F.x i s ∈ S) (haS : ∀ s ∈ S, F.a i s ∈ S) :
    ∀ t ∈ commSp V (F.x i) S, F.a i t ∈ commSp V (F.x i) S :=
  commSp_invariant_a (F.prime i).pos (F.xpow i) (F.conj i) hxS haS

theorem peel_fix_T (F : Frame V ι) (i : ι) {S : Submodule (ZMod 2) V}
    (hxS : ∀ s ∈ S, F.x i s ∈ S) : fixSp V (F.x i) (commSp V (F.x i) S) = ⊥ :=
  fixSp_commSp_eq_bot (frame_odd F i) (F.xpow i) hxS

theorem peel_decomp (F : Frame V ι) (i : ι) {S : Submodule (ZMod 2) V}
    (hxS : ∀ s ∈ S, F.x i s ∈ S) :
    Disjoint (fixSp V (F.x i) S) (commSp V (F.x i) S) ∧
      fixSp V (F.x i) S ⊔ commSp V (F.x i) S = S :=
  decomp_fix_comm (F.x i) (frame_odd F i) (F.xpow i) S hxS

theorem peel_split [Finite V] (F : Frame V ι) (i : ι) {S : Submodule (ZMod 2) V}
    (hxS : ∀ s ∈ S, F.x i s ∈ S) (haS : ∀ s ∈ S, F.a i s ∈ S) :
    Disjoint (fixSp V (F.a i) (commSp V (F.x i) S))
        ((fixSp V (F.a i) (commSp V (F.x i) S)).map (F.x i : V →ₗ[ZMod 2] V)) ∧
      fixSp V (F.a i) (commSp V (F.x i) S) ⊔
          (fixSp V (F.a i) (commSp V (F.x i) S)).map (F.x i : V →ₗ[ZMod 2] V) =
        commSp V (F.x i) S :=
  dihedral_split (F.x i) (F.a i) (F.xpow i) (frame_odd F i) (F.asq i) (F.conj i) _
    (peel_T_x F i hxS) (peel_T_a F i hxS haS) (peel_fix_T F i hxS)

theorem peel_W_invariant_of_comm {c x a : V ≃ₗ[ZMod 2] V} (hcx : c * x = x * c)
    (hca : c * a = a * c) {S : Submodule (ZMod 2) V} (hc : ∀ s ∈ S, c s ∈ S) :
    ∀ w ∈ fixSp V a (commSp V x S), c w ∈ fixSp V a (commSp V x S) :=
  fixSp_invariant hca (commSp_invariant hcx hc)

theorem finrank_peel [Finite V] (F : Frame V ι) (i : ι) {S : Submodule (ZMod 2) V}
    (hxS : ∀ s ∈ S, F.x i s ∈ S) (haS : ∀ s ∈ S, F.a i s ∈ S) :
    Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) (fixSp V (F.x i) S) +
      2 * Module.finrank (ZMod 2) (fixSp V (F.a i) (commSp V (F.x i) S)) := by
  obtain ⟨hd, hsup⟩ := peel_decomp F i hxS
  have h1 : Module.Finite (ZMod 2) (fixSp V (F.x i) S) := Module.Finite.of_finite
  have h2 : Module.Finite (ZMod 2) (commSp V (F.x i) S) := Module.Finite.of_finite
  have := Submodule.finrank_sup_add_finrank_inf_eq (fixSp V (F.x i) S) (commSp V (F.x i) S)
  rw [hsup, hd.eq_bot, finrank_bot, add_zero] at this
  have h3 := dihedral_finrank (F.x i) (F.a i) (F.xpow i) (frame_odd F i) (F.asq i) (F.conj i)
    (commSp V (F.x i) S) (peel_T_x F i hxS) (peel_T_a F i hxS haS) (peel_fix_T F i hxS)
  omega

theorem gFun_le_peel [Finite V] (F : Frame V ι) (i : ι) {S : Submodule (ZMod 2) V}
    (hxS : ∀ s ∈ S, F.x i s ∈ S) (haS : ∀ s ∈ S, F.a i s ∈ S) (hnt : ∃ s ∈ S, F.x i s ≠ s) :
    gFun (F.p i) ≤ 2 * Module.finrank (ZMod 2) (fixSp V (F.a i) (commSp V (F.x i) S)) := by
  have hbot := peel_fix_T F i hxS
  have hTfin := dihedral_finrank (F.x i) (F.a i) (F.xpow i) (frame_odd F i) (F.asq i) (F.conj i)
    (commSp V (F.x i) S) (peel_T_x F i hxS) (peel_T_a F i hxS haS) hbot
  have hdvd := cyclic_dvd_two_pow (F.prime i) (F.x i) (F.xpow i) (commSp V (F.x i) S)
    (peel_T_x F i hxS) (fun t ht hfix => by
      have : t ∈ fixSp V (F.x i) (commSp V (F.x i) S) := mem_fixSp.2 ⟨ht, hfix⟩
      rw [hbot] at this
      exact (Submodule.mem_bot (ZMod 2)).1 this)
  have hpos : 0 < Module.finrank (ZMod 2) (commSp V (F.x i) S) := by
    have : Module.Finite (ZMod 2) (commSp V (F.x i) S) := Module.Finite.of_finite
    exact Submodule.one_le_finrank_iff.2 (commSp_ne_bot hnt)
  rw [hTfin] at hdvd hpos
  exact gFun_le_of_dvd (F.prime i) (F.odd i) hpos ⟨_, two_mul _⟩ hdvd

theorem peel_W_ne_bot [Finite V] (F : Frame V ι) (J : Finset ι) (S : Submodule (ZMod 2) V)
    (h : Adm F S J) {i₀ : ι} (hi : i₀ ∈ J) :
    fixSp V (F.a i₀) (commSp V (F.x i₀) S) ≠ ⊥ := by
  obtain ⟨hxS, haS, hnt⟩ := h i₀ hi
  intro hW
  have h1 := gFun_le_peel F i₀ hxS haS hnt
  have h2 := gFun_ge_two (F.prime i₀) (F.odd i₀)
  rw [hW, finrank_bot] at h1
  omega

theorem peel_U_invariant (F : Frame V ι) (J : Finset ι) (S : Submodule (ZMod 2) V)
    (h : Adm F S J) {i₀ j : ι} (hj : j ∈ J) (hji : j ≠ i₀) :
    (∀ u ∈ fixSp V (F.x i₀) S, F.x j u ∈ fixSp V (F.x i₀) S) ∧
      ∀ u ∈ fixSp V (F.x i₀) S, F.a j u ∈ fixSp V (F.x i₀) S := by
  obtain ⟨hxS, haS, -⟩ := h j hj
  exact ⟨fixSp_invariant (F.xx j i₀ hji) hxS, fixSp_invariant (F.xa i₀ j hji.symm).symm haS⟩

theorem peel_W_invariant (F : Frame V ι) (J : Finset ι) (S : Submodule (ZMod 2) V)
    (h : Adm F S J) {i₀ j : ι} (hj : j ∈ J) (hji : j ≠ i₀) :
    (∀ w ∈ fixSp V (F.a i₀) (commSp V (F.x i₀) S),
        F.x j w ∈ fixSp V (F.a i₀) (commSp V (F.x i₀) S)) ∧
      ∀ w ∈ fixSp V (F.a i₀) (commSp V (F.x i₀) S),
        F.a j w ∈ fixSp V (F.a i₀) (commSp V (F.x i₀) S) := by
  obtain ⟨hxS, haS, -⟩ := h j hj
  exact ⟨peel_W_invariant_of_comm (F.xx j i₀ hji) (F.xa j i₀ hji) hxS,
    peel_W_invariant_of_comm (F.xa i₀ j hji.symm).symm (F.aa j i₀ hji) haS⟩

theorem peel_U_nontrivial [Finite V] (F : Frame V ι) (J : Finset ι) (S : Submodule (ZMod 2) V)
    (h : Adm F S J) {i₀ : ι} (hi : i₀ ∈ J) {j : ι} (hj : j ∈ J) (hji : j ≠ i₀)
    (hW : ∀ w ∈ fixSp V (F.a i₀) (commSp V (F.x i₀) S), F.x j w = w) :
    ∃ u ∈ fixSp V (F.x i₀) S, F.x j u ≠ u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hxS, haS, -⟩ := h i₀ hi
  obtain ⟨-, hsupS⟩ := peel_decomp F i₀ hxS
  obtain ⟨-, hsupT⟩ := peel_split F i₀ hxS haS
  have hT : ∀ t ∈ commSp V (F.x i₀) S, F.x j t = t := by
    intro t ht
    have ht' : t ∈ fixSp V (F.a i₀) (commSp V (F.x i₀) S) ⊔
        (fixSp V (F.a i₀) (commSp V (F.x i₀) S)).map (F.x i₀ : V →ₗ[ZMod 2] V) := by
      rw [hsupT]
      exact ht
    exact fix_sup hW (fix_map (F.xx j i₀ hji) hW) t ht'
  have hS : ∀ s ∈ S, F.x j s = s := by
    intro s hs
    have hs' : s ∈ fixSp V (F.x i₀) S ⊔ commSp V (F.x i₀) S := by
      rw [hsupS]
      exact hs
    exact fix_sup hcon hT s hs'
  obtain ⟨-, -, s, hs, hne⟩ := h j hj
  exact hne (hS s hs)

theorem peel_adm [Finite V] [DecidableEq ι] (F : Frame V ι) (J : Finset ι)
    (S : Submodule (ZMod 2) V) (h : Adm F S J) {i₀ : ι} (hi : i₀ ∈ J) :
    ∃ JU JW : Finset ι, Disjoint JU JW ∧ JU ∪ JW = J.erase i₀ ∧
      Adm F (fixSp V (F.x i₀) S) JU ∧
      Adm F (fixSp V (F.a i₀) (commSp V (F.x i₀) S)) JW := by
  classical
  refine ⟨(J.erase i₀).filter
      (fun j => ∀ w ∈ fixSp V (F.a i₀) (commSp V (F.x i₀) S), F.x j w = w),
    (J.erase i₀).filter
      (fun j => ¬ ∀ w ∈ fixSp V (F.a i₀) (commSp V (F.x i₀) S), F.x j w = w),
    Finset.disjoint_filter_filter_not _ _ _, Finset.filter_union_filter_not_eq _ _, ?_, ?_⟩
  · intro j hj
    obtain ⟨hjJ', hjW⟩ := Finset.mem_filter.1 hj
    have hji : j ≠ i₀ := Finset.ne_of_mem_erase hjJ'
    have hjJ : j ∈ J := Finset.mem_of_mem_erase hjJ'
    exact ⟨(peel_U_invariant F J S h hjJ hji).1, (peel_U_invariant F J S h hjJ hji).2,
      peel_U_nontrivial F J S h hi hjJ hji hjW⟩
  · intro j hj
    obtain ⟨hjJ', hjW⟩ := Finset.mem_filter.1 hj
    have hji : j ≠ i₀ := Finset.ne_of_mem_erase hjJ'
    have hjJ : j ∈ J := Finset.mem_of_mem_erase hjJ'
    refine ⟨(peel_W_invariant F J S h hjJ hji).1, (peel_W_invariant F J S h hjJ hji).2, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hjW hcon

theorem dim_lemma [Finite V] (F : Frame V ι) (J : Finset ι) (S : Submodule (ZMod 2) V)
    (h : Adm F S J) : ∑ j ∈ J, gFun (F.p j) ≤ Module.finrank (ZMod 2) S := by
  classical
  suffices H : ∀ n : ℕ, ∀ (J : Finset ι) (S : Submodule (ZMod 2) V), J.card = n → Adm F S J →
      ∑ j ∈ J, gFun (F.p j) ≤ Module.finrank (ZMod 2) S from H _ J S rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro J S hJ hAdm
    rcases J.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨i₀, hi₀, hmin⟩ := J.exists_min_image (fun j => gFun (F.p j)) hne
      obtain ⟨JU, JW, hdisj, hunion, hAU, hAW⟩ := peel_adm F J S hAdm hi₀
      have hlt : (J.erase i₀).card < n := hJ ▸ Finset.card_erase_lt_of_mem hi₀
      have hsubU : JU ⊆ J.erase i₀ := by
        rw [← hunion]
        exact Finset.subset_union_left
      have hsubW : JW ⊆ J.erase i₀ := by
        rw [← hunion]
        exact Finset.subset_union_right
      have ihU := ih _ (lt_of_le_of_lt (Finset.card_le_card hsubU) hlt) JU _ rfl hAU
      have ihW := ih _ (lt_of_le_of_lt (Finset.card_le_card hsubW) hlt) JW _ rfl hAW
      have hsum : ∑ j ∈ J.erase i₀, gFun (F.p j) =
          ∑ j ∈ JU, gFun (F.p j) + ∑ j ∈ JW, gFun (F.p j) := by
        rw [← hunion]
        exact Finset.sum_union hdisj
      have hJsum : ∑ j ∈ J, gFun (F.p j) = gFun (F.p i₀) + ∑ j ∈ J.erase i₀, gFun (F.p j) :=
        (Finset.add_sum_erase J (fun j => gFun (F.p j)) hi₀).symm
      obtain ⟨hxS, haS, hnt⟩ := hAdm i₀ hi₀
      have hfin := finrank_peel F i₀ hxS haS
      have hg := gFun_le_peel F i₀ hxS haS hnt
      rcases JW.eq_empty_or_nonempty with hJW | ⟨j₀, hj₀⟩
      · rw [hJW, Finset.sum_empty] at hsum
        omega
      · have hj₀J : j₀ ∈ J := Finset.mem_of_mem_erase (hsubW hj₀)
        have hle : gFun (F.p i₀) ≤ gFun (F.p j₀) := hmin j₀ hj₀J
        have hsingle : gFun (F.p j₀) ≤ ∑ j ∈ JW, gFun (F.p j) :=
          Finset.single_le_sum (f := fun j => gFun (F.p j)) (fun _ _ => Nat.zero_le _) hj₀
        omega

theorem peel_bound [Finite V] [DecidableEq ι] (F : Frame V ι) (J : Finset ι)
    (S : Submodule (ZMod 2) V) (h : Adm F S J) {i₀ : ι} (hi : i₀ ∈ J) :
    ∑ j ∈ J.erase i₀, gFun (F.p j) +
        Module.finrank (ZMod 2) (fixSp V (F.a i₀) (commSp V (F.x i₀) S)) ≤
      Module.finrank (ZMod 2) S := by
  obtain ⟨JU, JW, hdisj, hunion, hAU, hAW⟩ := peel_adm F J S h hi
  have h1 := dim_lemma F JU _ hAU
  have h2 := dim_lemma F JW _ hAW
  have hsum : ∑ j ∈ J.erase i₀, gFun (F.p j) =
      ∑ j ∈ JU, gFun (F.p j) + ∑ j ∈ JW, gFun (F.p j) := by
    rw [← hunion]
    exact Finset.sum_union hdisj
  obtain ⟨hxS, haS, -⟩ := h i₀ hi
  have hfin := finrank_peel F i₀ hxS haS
  omega

end Peel

end CFSG.Quasithin.SzN31
