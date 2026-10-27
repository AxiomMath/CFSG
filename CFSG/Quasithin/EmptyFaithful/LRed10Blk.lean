module

public import CFSG.Quasithin.EmptyFaithful.LRed10Pair
public import CFSG.Quasithin.EmptyFaithful.LRed10Fin
public import CFSG.Quasithin.Vol2.Ch3n317A5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.Quasithin.Ch3n317A5

namespace LRed10

section Vec

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}

theorem mem_evenWeight' (f : Fin 5 → ZMod 2) : f ∈ evenWeight 5 ↔ Ev f := by
  simp [evenWeight, AddMonoidHom.mem_ker, Ev, Fin.sum_univ_five]

@[expose] def vec (β : ↥(commV L) ≃* Multiplicative ↥(evenWeight 5)) (u : ↥(commV L)) :
    Fin 5 → ZMod 2 :=
  ((Multiplicative.toAdd (β u) : ↥(evenWeight 5)) : Fin 5 → ZMod 2)

variable (β : ↥(commV L) ≃* Multiplicative ↥(evenWeight 5))

theorem ev_vec (u : ↥(commV L)) : Ev (vec β u) :=
  (mem_evenWeight' _).1 (Multiplicative.toAdd (β u)).2

theorem vec_inj {u v : ↥(commV L)} (h : vec β u = vec β v) : u = v := by
  apply β.injective
  apply Multiplicative.toAdd.injective
  exact Subtype.ext h

theorem vec_symm (f : Fin 5 → ZMod 2) (hf : Ev f) :
    vec β (β.symm (Multiplicative.ofAdd ⟨f, (mem_evenWeight' f).2 hf⟩)) = f := by
  unfold vec
  rw [MulEquiv.apply_symm_apply]
  rfl

noncomputable def evEquiv : ↥(commV L) ≃ {f : Fin 5 → ZMod 2 // Ev f} :=
  β.toEquiv.trans (Multiplicative.toAdd.trans (Equiv.subtypeEquivRight mem_evenWeight'))

theorem card_commV (β : ↥(commV L) ≃* Multiplicative ↥(evenWeight 5)) :
    Nat.card ↥(commV L) = 16 := by
  rw [Nat.card_congr (evEquiv β), card_ev]

end Vec

section Transfer

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} (θ : ↥L ≃* Perm (Fin 5))
  (β : ↥(commV L) ≃* Multiplicative ↥(evenWeight 5))

@[expose] def Compat : Prop :=
  ∀ (h : ↥L) (u : ↥(commV L)) (hu : (h : MulAut W) (u : W) ∈ commV L) (i : Fin 5),
    ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) ((θ h)⁻¹ i)

variable {θ β}

theorem vec_apply (hβ : Compat θ β) (x : ↥L) (u : ↥(commV L)) (i : Fin 5) :
    vec β ⟨(x : MulAut W) u, mem_commV_of_mem x.2 u.2⟩ i = vec β u ((θ x)⁻¹ i) :=
  hβ x u _ i

@[expose] noncomputable def eltHom (L : Subgroup (MulAut W)) (θ : ↥L ≃* Perm (Fin 5)) :
    Perm (Fin 5) →* MulAut W :=
  L.subtype.comp θ.symm.toMonoidHom

theorem eltHom_apply (σ : Perm (Fin 5)) : eltHom L θ σ = elt L θ σ := rfl

theorem eltHom_injective : Function.Injective (eltHom L θ) :=
  L.subtype_injective.comp θ.symm.injective

theorem range_eltHom : (eltHom L θ).range = L := by
  unfold eltHom
  rw [MonoidHom.range_comp]
  ext x
  constructor
  · rintro ⟨y, ⟨σ, rfl⟩, rfl⟩
    exact (θ.symm σ).2
  · intro hx
    exact ⟨⟨x, hx⟩, ⟨θ ⟨x, hx⟩, by simp⟩, rfl⟩

theorem card_fixV_inf_commV (hβ : Compat θ β) (B : Subgroup (MulAut W)) (hBL : B ≤ L) :
    Nat.card ↥(fixV B ⊓ commV L) =
      Nat.card (FixSet ((B.comap (eltHom L θ) : Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5)))) := by
  classical
  let F : ↥(fixV B ⊓ commV L) →
      FixSet ((B.comap (eltHom L θ) : Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5))) :=
    fun u => ⟨vec β ⟨u.1, u.2.2⟩, ev_vec β _, fun σ hσ i => by
      have hσB : (eltHom L θ σ) ∈ B := hσ
      have hfix : (eltHom L θ σ) u.1 = u.1 := u.2.1 _ hσB
      have h1 := vec_apply hβ (θ.symm σ) ⟨u.1, u.2.2⟩ i
      have h2 : vec β ⟨(θ.symm σ : MulAut W) u.1, mem_commV_of_mem (θ.symm σ).2 u.2.2⟩ =
          vec β ⟨u.1, u.2.2⟩ := by
        congr 1
        exact Subtype.ext hfix
      rw [h2, MulEquiv.apply_symm_apply] at h1
      exact h1.symm⟩
  refine Nat.card_eq_of_bijective F ⟨?_, ?_⟩
  · intro u v huv
    have h0 : (F u).1 = (F v).1 := Subtype.ext_iff.1 huv
    have h1 : vec β ⟨u.1, u.2.2⟩ = vec β ⟨v.1, v.2.2⟩ := h0
    have h := vec_inj β h1
    exact Subtype.ext (congrArg (fun x : ↥(commV L) => x.1) h)
  · rintro ⟨f, hf, hfix⟩
    set u₀ : ↥(commV L) := β.symm (Multiplicative.ofAdd ⟨f, (mem_evenWeight' f).2 hf⟩) with hu₀
    have hvec : vec β u₀ = f := vec_symm β f hf
    have hu₀fix : ∀ x ∈ B, (x : MulAut W) u₀.1 = u₀.1 := by
      intro x hx
      have hxL : x ∈ L := hBL hx
      have hσ : θ ⟨x, hxL⟩ ∈ ((B.comap (eltHom L θ) : Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5))) := by
        show eltHom L θ (θ ⟨x, hxL⟩) ∈ B
        rw [eltHom_apply, elt_theta]
        exact hx
      have h1 := vec_apply hβ ⟨x, hxL⟩ u₀
      have h2 : vec β ⟨x u₀.1, mem_commV_of_mem hxL u₀.2⟩ = vec β u₀ := by
        funext i
        rw [h1 i, hvec]
        exact hfix _ hσ i
      exact congrArg Subtype.val (vec_inj β h2)
    refine ⟨⟨u₀.1, hu₀fix, u₀.2⟩, ?_⟩
    apply Subtype.ext
    exact hvec

end Transfer

section Block

variable {W : Type*} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {θ : ↥L ≃* Perm (Fin 5)}
  {β : ↥(commV L) ≃* Multiplicative ↥(evenWeight 5)}

theorem padicValNat_add_le_four {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m * n ≤ 16) :
    padicValNat 2 m + padicValNat 2 n ≤ 4 := by
  rw [← padicValNat.mul hm hn]
  have h1 : 2 ^ padicValNat 2 (m * n) ∣ m * n := pow_padicValNat_dvd
  have h2 : 2 ^ padicValNat 2 (m * n) ≤ 2 ^ 4 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hm hn)) h1).trans (by simpa using h)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

omit [Finite W] in
theorem card_comap_eltHom (B : Subgroup (MulAut W)) (hB : B ≤ L) :
    Nat.card ↥(B.comap (eltHom L θ)) = Nat.card ↥B := by
  have h1 : (B.comap (eltHom L θ)).map (eltHom L θ) = B := by
    rw [Subgroup.map_comap_eq, range_eltHom]
    exact inf_eq_right.2 hB
  calc Nat.card ↥(B.comap (eltHom L θ)) = Nat.card ↥((B.comap (eltHom L θ)).map (eltHom L θ)) :=
        (Subgroup.card_map_of_injective eltHom_injective).symm
    _ = Nat.card ↥B := by rw [h1]

theorem blkProp_of_a5 (hβ : Compat θ β) {P : Subgroup (MulAut W)} {a b c d : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hPL : P ≤ L) (hP4 : Nat.card ↥P = 4)
    (h₁ : elt L θ (swap a b) ∈ P) (h₂ : elt L θ (swap c d) ∈ P) : BlkProp L P := by
  have hP'4 : Nat.card ↥(P.comap (eltHom L θ)) = 4 := by rw [card_comap_eltHom P hPL, hP4]
  have hmem := mem_four_iff hab hac had hbc hbd hcd (P.comap (eltHom L θ)) hP'4 h₁ h₂
  have e16 : padicValNat 2 16 = 4 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
  have e4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  refine ⟨hPL, fun B hBP => ?_, ?_⟩
  · have hBL : B ≤ L := hBP.trans hPL
    have hB'' : ∀ σ ∈ B.comap (eltHom L θ),
        σ = 1 ∨ σ = swap a b ∨ σ = swap c d ∨ σ = swap a b * swap c d :=
      fun σ hσ => (hmem σ).1 (Subgroup.comap_mono hBP hσ)
    have hcard : Nat.card ↥(B.comap (eltHom L θ)) = Nat.card ↥B := card_comap_eltHom B hBL
    have hdvd : Nat.card ↥(B.comap (eltHom L θ)) ∣ 4 := by
      rw [hcard, ← hP4]
      exact Subgroup.card_dvd_of_le hBP
    have h16 := card_mul_card_fixSet_le hab hac had hbc hbd hcd (B.comap (eltHom L θ)) hB'' hdvd
    rw [← card_fixV_inf_commV hβ B hBL, hcard] at h16
    have hpos1 : Nat.card ↥B ≠ 0 := Nat.card_pos.ne'
    have hpos2 : Nat.card ↥(fixV B ⊓ commV L) ≠ 0 := Nat.card_pos.ne'
    have := padicValNat_add_le_four hpos1 hpos2 h16
    unfold rk
    rw [card_commV β, e16]
    exact this
  · have h4 : Nat.card (FixSet ((P.comap (eltHom L θ) : Subgroup (Perm (Fin 5))) :
        Set (Perm (Fin 5)))) = 4 :=
      card_fixSet_eq_four hab hac had hbc hbd hcd (fun σ hσ => (hmem σ).1 hσ) h₁ h₂
    rw [← card_fixV_inf_commV hβ P hPL] at h4
    unfold rk
    rw [card_commV β, h4, e16, e4]

omit [Finite W] in
theorem fixV_inf_commV_eq_bot (hβ : Compat θ β) {K : Subgroup (MulAut W)} (hK : altOf L θ ≤ K) :
    fixV K ⊓ commV L = ⊥ := by
  refine eq_bot_iff.2 fun w hw => ?_
  have hvec : vec β ⟨w, hw.2⟩ = 0 := by
    refine eq_zero_of_fixed_alt (ev_vec β _) fun σ hσ i => ?_
    have hx : elt L θ σ ∈ altOf L θ := elt_mem_altOf hσ
    have hwK : (elt L θ σ) w = w := hw.1 _ (hK hx)
    have h1 := vec_apply hβ (θ.symm σ) ⟨w, hw.2⟩ i
    have h2 : vec β ⟨(θ.symm σ : MulAut W) w, mem_commV_of_mem (θ.symm σ).2 hw.2⟩ =
        vec β ⟨w, hw.2⟩ := by
      congr 1
      exact Subtype.ext hwK
    rw [h2, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have h1 : (⟨w, hw.2⟩ : ↥(commV L)) = 1 := by
    apply vec_inj β
    rw [hvec]
    unfold vec
    simp
  have := congrArg (fun x : ↥(commV L) => x.1) h1
  simpa using this

omit [Finite W] in
theorem le_sup_conj_of_a5 {P : Subgroup (MulAut W)} {a b c d : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h₁ : elt L θ (swap a b) ∈ P) (h₂ : elt L θ (swap c d) ∈ P) :
    ∃ g ∈ altOf L θ, L ≤ P ⊔ P.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨e, hae, hbe, hce, hde⟩ := exists_fifth a b c d hab hac had hbc hbd hcd
  have hρ : cyc5 a b c d e ∈ alternatingGroup (Fin 5) :=
    Perm.mem_alternatingGroup.2 (sign_cyc5 hab hbc hcd hde)
  refine ⟨elt L θ (cyc5 a b c d e), elt_mem_altOf hρ, ?_⟩
  obtain ⟨hc1, hc2⟩ := cyc5_conj a b c d e hab hac had hae hbc hbd hbe hcd hce hde
  have hconj : ∀ σ : Perm (Fin 5), elt L θ (cyc5 a b c d e * σ * (cyc5 a b c d e)⁻¹) =
      elt L θ (cyc5 a b c d e) * elt L θ σ * (elt L θ (cyc5 a b c d e))⁻¹ := fun σ => by
    rw [elt_mul, elt_mul, elt_inv]
  have m1 : elt L θ (swap b c) ∈ P.map (MulAut.conj (elt L θ (cyc5 a b c d e))).toMonoidHom :=
    ⟨elt L θ (swap a b), h₁, by rw [← hc1, hconj]; rfl⟩
  have m2 : elt L θ (swap d e) ∈ P.map (MulAut.conj (elt L θ (cyc5 a b c d e))).toMonoidHom :=
    ⟨elt L θ (swap c d), h₂, by rw [← hc2, hconj]; rfl⟩
  have hL : L = (⊤ : Subgroup (Perm (Fin 5))).map (eltHom L θ) := by
    rw [← MonoidHom.range_eq_map, range_eltHom]
  refine hL.le.trans ?_
  rw [← closure_path_four a b c d e hab hac had hae hbc hbd hbe hcd hce hde,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨σ, hσ, rfl⟩
  rcases hσ with rfl | rfl | rfl | rfl
  · exact Subgroup.mem_sup_left h₁
  · exact Subgroup.mem_sup_left h₂
  · exact Subgroup.mem_sup_right m1
  · exact Subgroup.mem_sup_right m2

theorem blk_facts (hβ : Compat θ β) {A P : Subgroup (MulAut W)} (θ' : ↥L ≃* Perm (Fin 5))
    (hPL : P ≤ L) (hP4 : Nat.card ↥P = 4)
    (hPcl : P = Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ A ∧ (θ' ⟨x, hx⟩).IsSwap}) :
    BlkProp L P ∧ ∃ g ∈ altOf L θ, L ≤ P ⊔ P.map (MulAut.conj g).toMonoidHom := by
  have key : ∀ (e₁ e₂ : ↥L ≃* Perm (Fin 5)) (x : ↥L), (e₁ x).IsSwap → (e₂ x).IsSwap := by
    intro e₁ e₂ x h
    have := isSwap_of_mulEquiv (e₁.symm.trans e₂) h
    simpa using this
  have hset : {x | ∃ hx : x ∈ L, x ∈ A ∧ (θ' ⟨x, hx⟩).IsSwap} =
      {x | ∃ hx : x ∈ L, x ∈ A ∧ (θ ⟨x, hx⟩).IsSwap} := by
    ext x
    constructor
    · rintro ⟨hx, hxA, hsw⟩
      exact ⟨hx, hxA, key θ' θ ⟨x, hx⟩ hsw⟩
    · rintro ⟨hx, hxA, hsw⟩
      exact ⟨hx, hxA, key θ θ' ⟨x, hx⟩ hsw⟩
  rw [hset] at hPcl
  have hcl4 : Nat.card ↥(Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ A ∧ (θ ⟨x, hx⟩).IsSwap}) = 4 := by
    rw [← hPcl]
    exact hP4
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, h₁, h₂⟩ := exists_two_swaps hcl4
  rw [← hPcl] at h₁ h₂
  exact ⟨blkProp_of_a5 hβ hab hac had hbc hbd hcd hPL hP4 h₁ h₂,
    le_sup_conj_of_a5 hab hac had hbc hbd hcd h₁ h₂⟩

theorem block_data {Kst Jst Tst : Subgroup (MulAut W)} (hA5 : E2.IsA5Module L)
    (hL4 : Nat.card ↥(L ⊓ Jst) = 4 ∧ ∃ θ' : ↥L ≃* Perm (Fin 5), L ⊓ Jst =
      Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ Tst ∧ (θ' ⟨x, hx⟩).IsSwap})
    (hK : ∀ x ∈ L, Odd (orderOf x) → x ∈ Kst) :
    BlkProp L (L ⊓ Jst) ∧ fixV Kst ⊓ commV L = ⊥ ∧
      ∃ g ∈ L, g ∈ Kst ∧ L ≤ (L ⊓ Jst) ⊔ (L ⊓ Jst).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨θ, β, hβ⟩ := hA5
  obtain ⟨h4, θ', hcl⟩ := hL4
  obtain ⟨hblk, g, hgA, hg⟩ := blk_facts (θ := θ) (β := β) hβ θ' inf_le_left h4 hcl
  have hAK : altOf L θ ≤ Kst := altOf_le_of_odd fun x hx hodd => hK x hx hodd
  exact ⟨hblk, fixV_inf_commV_eq_bot hβ hAK, g, altOf_le hgA, hAK hgA, hg⟩

end Block

end LRed10

end CFSG.Quasithin
