module

public import CFSG.Quasithin.Background.HZL34B

public section

namespace CFSG.Quasithin.H13.VzL34

open CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.L34Z
  CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Monster.Code CFSG.QuasithinUnique
  CFSG.QuasithinUnique.A5.Delta5 CFSG.Quasithin.H.ZTrans Equiv

@[expose] def bcVz : List ℕ := [0, 29, 27, 0, 0, 0, 0, 24, 9]

theorem bcVz_length : bcVz.length = 9 := rfl

theorem bcVz_lt : ∀ c ∈ bcVz, c < 2 ^ 5 := by decide

@[expose] def vzL34Add : (Fin 9 → ZMod 2) →+ (Fin 5 → ZMod 2) where
  toFun v := ∑ j : Fin 9, v j • bvec 5 (bcVz.getD j.val 0)
  map_zero' := by simp
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem vzL34_cols_even : ∀ j : Fin 9, ∑ i : Fin 5, bvec 5 (bcVz.getD j.val 0) i = 0 := by
  decide +kernel

theorem vzL34Add_mem (v : Fin 9 → ZMod 2) : vzL34Add v ∈ evenWeight 5 := by
  show ∑ i, vzL34Add v i = 0
  calc ∑ i, vzL34Add v i = ∑ i, ∑ j : Fin 9, v j • bvec 5 (bcVz.getD j.val 0) i := by
        simp [vzL34Add, Finset.sum_apply]
    _ = ∑ j : Fin 9, ∑ i, v j • bvec 5 (bcVz.getD j.val 0) i := Finset.sum_comm
    _ = ∑ j : Fin 9, v j • ∑ i, bvec 5 (bcVz.getD j.val 0) i :=
        Finset.sum_congr rfl fun j _ => Finset.smul_sum.symm
    _ = 0 := Finset.sum_eq_zero fun j _ => by rw [vzL34_cols_even j, smul_zero]

@[expose] def vzL34AddΔ : (Fin 9 → ZMod 2) →+ evenWeight 5 :=
  AddMonoidHom.codRestrict vzL34Add (evenWeight 5) vzL34Add_mem

@[expose] def vzL34Hom : W9 →* Multiplicative (evenWeight 5) :=
  AddMonoidHom.toMultiplicative vzL34AddΔ

@[expose] def vzL34Val (w : W9) : Fin 5 → ZMod 2 :=
  ((Multiplicative.toAdd (vzL34Hom w) : evenWeight 5) : Fin 5 → ZMod 2)

theorem vzL34Add_bvec (m : ℕ) : vzL34Add (bvec 9 m) = bvec 5 (actM bcVz m) := by
  refine addHom_bvec vzL34Add bcVz bcVz_length (fun j hj => ?_) m
  have h : ∀ j < 9, vzL34Add (bvec 9 (2 ^ j)) = bvec 5 (bcVz.getD j 0) := by decide +kernel
  exact h j hj

theorem vzL34Val_toW (m : ℕ) : vzL34Val (toW 9 m) = bvec 5 (actM bcVz m) := by
  rw [← vzL34Add_bvec]
  rfl

theorem vzL34_surj : ∀ k < 2 ^ 5, (∑ i : Fin 5, bvec 5 k i = 0) →
    ∃ m < 2 ^ 9, actM bcVz m = k := by
  decide +kernel

theorem vzL34_ker : ∀ m < 2 ^ 9, (actM bcVz m = 0 ↔ m ∈ combos w0Basis) := by
  decide +kernel

theorem vzL34Val_surj (x : Fin 5 → ZMod 2) (hx : x ∈ evenWeight 5) :
    ∃ w : W9, vzL34Val w = x := by
  obtain ⟨k, hk, hkx⟩ := toW_surj 5 (Multiplicative.ofAdd x)
  have hb : bvec 5 k = x := by
    have := congrArg Multiplicative.toAdd hkx
    simpa [toAdd_toW] using this
  have hev : ∑ i : Fin 5, bvec 5 k i = 0 := by
    rw [hb]; exact hx
  obtain ⟨m, hm, hmk⟩ := vzL34_surj k hk hev
  refine ⟨toW 9 m, ?_⟩
  rw [vzL34Val_toW, hmk, hb]

theorem vzL34Hom_surj : Function.Surjective vzL34Hom := by
  intro y
  obtain ⟨w, hw⟩ := vzL34Val_surj ((Multiplicative.toAdd y : evenWeight 5) : Fin 5 → ZMod 2)
    (Multiplicative.toAdd y).2
  refine ⟨w, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact hw

theorem vzL34Hom_eq_one_iff (w : W9) : vzL34Hom w = 1 ↔ w ∈ W0 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 w
  have hm' : m < 2 ^ 9 := hm
  have hone : vzL34Hom (toW 9 m) = 1 ↔ bvec 5 (actM bcVz m) = 0 := by
    rw [← vzL34Val_toW]
    constructor
    · intro h
      have h2 := congrArg (fun y => ((Multiplicative.toAdd y : evenWeight 5) : Fin 5 → ZMod 2)) h
      simpa [vzL34Val] using h2
    · intro h
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      simpa [vzL34Val] using h
  rw [hone, ← bvec_zero 5]
  constructor
  · intro h
    have hlt : actM bcVz m < 2 ^ 5 := actM_lt bcVz_lt m
    have := bvec_inj hlt (by positivity) h
    rw [mem_maskSub]
    have hz := (vzL34_ker m hm').1 this
    exact ⟨m, hz, rfl⟩
  · intro h
    rw [mem_maskSub] at h
    obtain ⟨m', hm'c, hm'eq⟩ := h
    have hlt' : m' < 2 ^ 9 := combos_lt (n := 9) (by decide) m' hm'c
    have hmm : m' = m := toW_inj hlt' hm' hm'eq
    subst hmm
    rw [(vzL34_ker m' hlt').2 hm'c]

@[expose] def sigX : Perm (Fin 5) := ⟨![0, 2, 1, 4, 3], ![0, 2, 1, 4, 3], by decide, by decide⟩

@[expose] def sigY : Perm (Fin 5) := ⟨![1, 3, 4, 2, 0], ![4, 0, 3, 1, 2], by decide, by decide⟩

theorem sigX_alt : sigX ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem sigY_alt : sigY ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem vzL34_eqX : ∀ m < 2 ^ 9, ∀ i : Fin 5,
    bvec 5 (actM bcVz (actM colsX m)) i = pact sigX (bvec 5 (actM bcVz m)) i := by
  decide +kernel

theorem vzL34_eqY : ∀ m < 2 ^ 9, ∀ i : Fin 5,
    bvec 5 (actM bcVz (actM colsY m)) i = pact sigY (bvec 5 (actM bcVz m)) i := by
  decide +kernel

@[expose] def VzActs (φ : MulAut W9) (σ : Perm (Fin 5)) : Prop :=
  ∀ w : W9, vzL34Val (φ w) = pact σ (vzL34Val w)

theorem VzActs.eq_of {φ : MulAut W9} {σ τ : Perm (Fin 5)} (h₁ : VzActs φ σ)
    (h₂ : VzActs φ τ) : σ = τ := by
  have h : ∀ x : Fin 5 → ZMod 2, x ∈ evenWeight 5 → pact σ x = pact τ x := by
    intro x hx
    obtain ⟨w, rfl⟩ := vzL34Val_surj x hx
    rw [← h₁ w, ← h₂ w]
  have key : ∀ x : Fin 5 → ZMod 2, isEven x → pact (σ⁻¹ * τ) x = x := by
    intro x hx
    rw [pact_mul, ← h x hx, ← pact_mul, inv_mul_cancel, pact_one]
  exact inv_mul_eq_one.1 (pact_faithful _ key)

theorem rho9X_acts : VzActs (rho9 xG) sigX := by
  intro w
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 w
  have hm' : m < 2 ^ 9 := hm
  rw [rho9_toW_cols xG cols_x hm', vzL34Val_toW, vzL34Val_toW]
  funext i
  exact vzL34_eqX m hm' i

theorem rho9Y_acts : VzActs (rho9 yG) sigY := by
  intro w
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 w
  have hm' : m < 2 ^ 9 := hm
  rw [rho9_toW_cols yG cols_y hm', vzL34Val_toW, vzL34Val_toW]
  funext i
  exact vzL34_eqY m hm' i

@[expose] def vzL34Stab : Subgroup (MulAut W9) where
  carrier := {φ | ∃ σ : Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ VzActs φ σ}
  one_mem' := ⟨1, one_mem _, fun _ => rfl⟩
  mul_mem' := by
    rintro φ ψ ⟨σ, hσ, hφ⟩ ⟨τ, hτ, hψ⟩
    refine ⟨σ * τ, mul_mem hσ hτ, fun w => ?_⟩
    rw [MulAut.mul_apply, hφ (ψ w), hψ w, pact_mul]
  inv_mem' := by
    rintro φ ⟨σ, hσ, hφ⟩
    refine ⟨σ⁻¹, inv_mem hσ, fun w => ?_⟩
    have h := hφ (φ⁻¹ w)
    have hw : φ (φ⁻¹ w) = w := by simp
    rw [hw] at h
    rw [h, ← pact_mul, inv_mul_cancel, pact_one]

open Classical in
noncomputable def vzL34Sig (φ : MulAut W9) : Perm (Fin 5) :=
  if h : ∃ σ : Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ VzActs φ σ then h.choose else 1

theorem vzL34Sig_spec {φ : MulAut W9} (hφ : φ ∈ vzL34Stab) :
    vzL34Sig φ ∈ alternatingGroup (Fin 5) ∧ VzActs φ (vzL34Sig φ) := by
  have h : ∃ σ : Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ VzActs φ σ := hφ
  unfold vzL34Sig
  rw [dif_pos h]
  exact h.choose_spec

theorem vzL34Sig_eq {φ : MulAut W9} (hφ : φ ∈ vzL34Stab) {σ : Perm (Fin 5)}
    (hσ : VzActs φ σ) : vzL34Sig φ = σ :=
  (vzL34Sig_spec hφ).2.eq_of hσ

noncomputable def vzL34AltHom : vzL34Stab →* Alt5 where
  toFun φ := ⟨vzL34Sig φ, (vzL34Sig_spec φ.2).1⟩
  map_one' := by
    apply Subtype.ext
    show vzL34Sig 1 = 1
    exact vzL34Sig_eq (one_mem _) (σ := 1) (fun _ => rfl)
  map_mul' φ ψ := by
    apply Subtype.ext
    show vzL34Sig ((φ : MulAut W9) * ψ) = vzL34Sig φ * vzL34Sig ψ
    refine vzL34Sig_eq (mul_mem φ.2 ψ.2) (σ := vzL34Sig φ * vzL34Sig ψ) ?_
    intro w
    show vzL34Val ((φ : MulAut W9) ((ψ : MulAut W9) w)) =
      pact (vzL34Sig φ * vzL34Sig ψ) (vzL34Val w)
    rw [(vzL34Sig_spec φ.2).2 ((ψ : MulAut W9) w), (vzL34Sig_spec ψ.2).2 w, pact_mul]

theorem L34_le_vzL34Stab : L34 ≤ vzL34Stab := by
  refine (Subgroup.closure_le vzL34Stab).2 ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact (show ∃ σ : Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ VzActs (rho9 xG) σ from
      ⟨sigX, sigX_alt, rho9X_acts⟩)
  · exact (show ∃ σ : Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ VzActs (rho9 yG) σ from
      ⟨sigY, sigY_alt, rho9Y_acts⟩)

noncomputable def vzL34Alpha : L34 →* Alt5 :=
  vzL34AltHom.comp (Subgroup.inclusion L34_le_vzL34Stab)

theorem vzL34Alpha_acts (φ : L34) (w : W9) :
    vzL34Val ((φ : MulAut W9) w) = pact (vzL34Alpha φ : Perm (Fin 5)) (vzL34Val w) :=
  (vzL34Sig_spec (L34_le_vzL34Stab φ.2)).2 w

theorem alt5_gen (a b : Alt5) (ha : orderOf a = 2) (hb : orderOf b = 5)
    (hab : orderOf (a * b * b) = 3) : Subgroup.closure ({a, b} : Set Alt5) = ⊤ := by
  set N : Subgroup Alt5 := Subgroup.closure ({a, b} : Set Alt5) with hN
  have ha' : a ∈ N := Subgroup.subset_closure (by simp)
  have hb' : b ∈ N := Subgroup.subset_closure (by simp)
  have hc : a * b * b ∈ N := N.mul_mem (N.mul_mem ha' hb') hb'
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have d5 : 5 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hb'; rwa [hb] at this
  have d3 : 3 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hc; rwa [hab] at this
  have d2 : 2 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N ha'; rwa [ha] at this
  have h30 : 30 ∣ Nat.card N := by omega
  have hdvd : Nat.card N ∣ 60 := by
    rw [← a5_card]; exact Subgroup.card_subgroup_dvd_card N
  have hle : Nat.card N ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hcases : Nat.card N = 30 ∨ Nat.card N = 60 := by
    obtain ⟨k, hk⟩ := h30
    omega
  have hsimple : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup (by simp)
  rcases hcases with h | h
  · exfalso
    have hidx : N.index = 2 := by
      have := N.card_mul_index
      rw [a5_card, h] at this; omega
    have hnorm : N.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · rw [h1] at h; simp at h
    · rw [h1] at hidx; simp at hidx
  · exact (Subgroup.card_eq_iff_eq_top N).mp (by rw [h, a5_card])

theorem sigX_order : orderOf (⟨sigX, sigX_alt⟩ : Alt5) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · apply Subtype.ext; show sigX ^ 2 = 1; decide +kernel
  · intro h; have := congrArg Subtype.val h; revert this; show ¬ (sigX = 1); decide +kernel

theorem sigY_order : orderOf (⟨sigY, sigY_alt⟩ : Alt5) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Subtype.ext; show sigY ^ 5 = 1; decide +kernel
  · intro h; have := congrArg Subtype.val h; revert this; show ¬ (sigY = 1); decide +kernel

theorem sigXYY_order :
    orderOf ((⟨sigX, sigX_alt⟩ : Alt5) * ⟨sigY, sigY_alt⟩ * ⟨sigY, sigY_alt⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Subtype.ext; show (sigX * sigY * sigY) ^ 3 = 1; decide +kernel
  · intro h; have := congrArg Subtype.val h; revert this; show ¬ (sigX * sigY * sigY = 1)
    decide +kernel

theorem vzL34Alpha_rhoX : vzL34Alpha ⟨rho9 xG, x_mem_L34⟩ = ⟨sigX, sigX_alt⟩ :=
  Subtype.ext (vzL34Sig_eq (L34_le_vzL34Stab x_mem_L34) rho9X_acts)

theorem vzL34Alpha_rhoY : vzL34Alpha ⟨rho9 yG, y_mem_L34⟩ = ⟨sigY, sigY_alt⟩ :=
  Subtype.ext (vzL34Sig_eq (L34_le_vzL34Stab y_mem_L34) rho9Y_acts)

theorem vzL34Alpha_surj : Function.Surjective vzL34Alpha := by
  rw [← MonoidHom.range_eq_top]
  have hgen := alt5_gen ⟨sigX, sigX_alt⟩ ⟨sigY, sigY_alt⟩ sigX_order sigY_order sigXYY_order
  have hsub : Subgroup.closure ({⟨sigX, sigX_alt⟩, ⟨sigY, sigY_alt⟩} : Set Alt5) ≤
      vzL34Alpha.range := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact MonoidHom.mem_range.2 ⟨⟨rho9 xG, x_mem_L34⟩, vzL34Alpha_rhoX⟩
    · exact MonoidHom.mem_range.2 ⟨⟨rho9 yG, y_mem_L34⟩, vzL34Alpha_rhoY⟩
  rw [hgen] at hsub
  exact top_le_iff.1 hsub

theorem vzL34_act_of_mem_Rbar {g : MulAut W9} (hg : g ∈ Rbar) (w : W9) :
    vzL34Val (g w) = vzL34Val w := by
  have h1 : g w * w⁻¹ ∈ commV Rbar := mem_commV hg w
  rw [commV_Rbar] at h1
  have h2 : vzL34Hom (g w * w⁻¹) = 1 := (vzL34Hom_eq_one_iff _).2 h1
  have h3 : vzL34Hom (g w) = vzL34Hom w := by
    have e : g w * w⁻¹ * w = g w := inv_mul_cancel_right (g w) w
    have h5 : vzL34Hom (g w) = vzL34Hom (g w * w⁻¹) * vzL34Hom w := by
      rw [← map_mul, e]
    rw [h5, h2, one_mul]
  simp only [vzL34Val, h3]

theorem vzL34Alpha_ker_card :
    Nat.card vzL34Alpha.ker = 16 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup vzL34Alpha.ker
  have h2 : Nat.card (L34 ⧸ vzL34Alpha.ker) = 60 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective vzL34Alpha
      vzL34Alpha_surj).toEquiv, a5_card]
  rw [card_L34, h2] at h1
  omega

theorem vzL34Alpha_eq_one_iff (φ : L34) :
    vzL34Alpha φ = 1 ↔ (φ : MulAut W9) ∈ Rbar := by
  have hle : Rbar.subgroupOf L34 ≤ vzL34Alpha.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have hsig : vzL34Sig (x : MulAut W9) = 1 :=
      vzL34Sig_eq (L34_le_vzL34Stab x.2) (σ := 1) (fun w => by
        rw [pact_one]; exact vzL34_act_of_mem_Rbar hx w)
    exact hsig
  have hcard : Nat.card (Rbar.subgroupOf L34) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Rbar_le_L34).toEquiv, card_Rbar]
  have heq : Rbar.subgroupOf L34 = vzL34Alpha.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, vzL34Alpha_ker_card])
  rw [← MonoidHom.mem_ker, ← heq, Subgroup.mem_subgroupOf]

end CFSG.Quasithin.H13.VzL34
