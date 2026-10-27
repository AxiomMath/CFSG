module

public import CFSG.Quasithin.Vol2.Ch12Sec5Lemmas
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.EmptyFaithful.T1515C6Gl
public import CFSG.Quasithin.EmptyFaithful.SzN19Par
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.F1Weak
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithful.S152UGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 Matrix

namespace S125ZV

theorem wedgeRep_apply (g : SpecialLinearGroup (Fin 5) (ZMod 2)) (w : Fin 10 → ZMod 2) :
    JonesParshall.wedgeRep g w =
      JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w :=
  JonesParshall.muW_apply (ZMod 2) g w

theorem diag_eq_one {u : SpecialLinearGroup (Fin 5) (ZMod 2)} (hu : IsUpperTri u) (i : Fin 5) :
    (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) i i = 1 := by
  have hdet : ∏ j, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) j j = 1 := by
    rw [← Matrix.det_of_isUpperTriangular (fun a b hab => hu a b hab)]
    exact u.2
  have hne : (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) i i ≠ 0 := fun h => by
    rw [Finset.prod_eq_zero (f := fun j => (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) j j)
      (Finset.mem_univ i) h] at hdet
    exact zero_ne_one hdet
  revert hne
  generalize (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) i i = x
  fin_cases x
  · intro h
    exact absurd rfl h
  · intro _
    rfl

theorem wedgeMat_mulVec_single {u : SpecialLinearGroup (Fin 5) (ZMod 2)} (hu : IsUpperTri u)
    (c : ZMod 2) :
    JonesParshall.wedgeMat (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single 0 c =
      Pi.single 0 c := by
  have h00 := diag_eq_one hu 0
  have h11 := diag_eq_one hu 1
  have h10 := hu 1 0 (by decide)
  have h20 := hu 2 0 (by decide)
  have h30 := hu 3 0 (by decide)
  have h40 := hu 4 0 (by decide)
  have h21 := hu 2 1 (by decide)
  have h31 := hu 3 1 (by decide)
  have h41 := hu 4 1 (by decide)
  funext k
  rw [Matrix.mulVec_single]
  fin_cases k <;> simp [JonesParshall.wedgeMat, JonesParshall.pr5, h00, h11, h10, h20, h30, h40,
    h21, h31, h41]

theorem exists_pr5 : ∀ i j : Fin 5, i < j → ∃ k : Fin 10, JonesParshall.pr5 k = (i, j) := by
  decide

theorem card_upperTri_le :
    Nat.card {u : SpecialLinearGroup (Fin 5) (ZMod 2) // IsUpperTri u} ≤ 2 ^ 10 := by
  have hinj : Function.Injective
      (fun u : {u : SpecialLinearGroup (Fin 5) (ZMod 2) // IsUpperTri u} => fun k : Fin 10 =>
        (u.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) (JonesParshall.pr5 k).1
          (JonesParshall.pr5 k).2) := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · obtain ⟨k, hk⟩ := exists_pr5 i j hij
      have := congrFun h k
      simp only [hk] at this
      exact this
    · rw [diag_eq_one u.2, diag_eq_one v.2]
    · rw [u.2 i j hij, v.2 i j hij]
  calc Nat.card {u : SpecialLinearGroup (Fin 5) (ZMod 2) // IsUpperTri u}
      ≤ Nat.card (Fin 10 → ZMod 2) := Nat.card_le_card_of_injective _ hinj
    _ = 2 ^ 10 := by simp

@[expose] def tr0 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def tr1 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def tr2 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def tr3 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1]

theorem wedgeMat_tr0 : JonesParshall.wedgeMat tr0 =
    1 + Matrix.single 1 4 1 + Matrix.single 2 5 1 + Matrix.single 3 6 1 := by decide

theorem wedgeMat_tr1 : JonesParshall.wedgeMat tr1 =
    1 + Matrix.single 0 1 1 + Matrix.single 5 7 1 + Matrix.single 6 8 1 := by decide

theorem wedgeMat_tr2 : JonesParshall.wedgeMat tr2 =
    1 + Matrix.single 1 2 1 + Matrix.single 4 5 1 + Matrix.single 8 9 1 := by decide

theorem wedgeMat_tr3 : JonesParshall.wedgeMat tr3 =
    1 + Matrix.single 2 3 1 + Matrix.single 5 6 1 + Matrix.single 7 8 1 := by decide

theorem fix_aux {x : Fin 10 → ZMod 2} {a b c d e f : Fin 10}
    (h : (1 + Matrix.single a b 1 + Matrix.single c d 1 + Matrix.single e f 1 :
      Matrix (Fin 10) (Fin 10) (ZMod 2)) *ᵥ x = x) (hac : a ≠ c) (hae : a ≠ e) (hce : c ≠ e) :
    x b = 0 ∧ x d = 0 ∧ x f = 0 := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, one_mul] at h
  have ha := congrFun h a
  have hc := congrFun h c
  have he := congrFun h e
  simp [hac, hae, hce, hac.symm, hae.symm, hce.symm] at ha hc he
  exact ⟨ha, hc, he⟩

theorem fixed_tr (x : Fin 10 → ZMod 2) (h0 : JonesParshall.wedgeMat tr0 *ᵥ x = x)
    (h1 : JonesParshall.wedgeMat tr1 *ᵥ x = x) (h2 : JonesParshall.wedgeMat tr2 *ᵥ x = x)
    (h3 : JonesParshall.wedgeMat tr3 *ᵥ x = x) : ∀ k : Fin 10, k ≠ 0 → x k = 0 := by
  rw [wedgeMat_tr0] at h0
  rw [wedgeMat_tr1] at h1
  rw [wedgeMat_tr2] at h2
  rw [wedgeMat_tr3] at h3
  obtain ⟨x4, x5, x6⟩ := fix_aux h0 (by decide) (by decide) (by decide)
  obtain ⟨x1, x7, x8⟩ := fix_aux h1 (by decide) (by decide) (by decide)
  obtain ⟨x2, -, x9⟩ := fix_aux h2 (by decide) (by decide) (by decide)
  obtain ⟨x3, -, -⟩ := fix_aux h3 (by decide) (by decide) (by decide)
  intro k hk
  fin_cases k
  · exact absurd rfl hk
  all_goals assumption

theorem exists_tr (M : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hM : M = tr0 ∨ M = tr1 ∨ M = tr2 ∨ M = tr3) :
    ∃ u : SpecialLinearGroup (Fin 5) (ZMod 2), IsUpperTri u ∧
      (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) = M := by
  have hup : ∀ i j : Fin 5, j < i → M i j = 0 := by
    intro i j hij
    rcases hM with rfl | rfl | rfl | rfl <;>
      fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
  have hdiag : ∏ i, M i i = 1 := by
    rcases hM with rfl | rfl | rfl | rfl <;> simp [Fin.prod_univ_five, tr0, tr1, tr2, tr3]
  refine ⟨⟨M, ?_⟩, hup, rfl⟩
  rw [Matrix.det_of_isUpperTriangular (fun a b hab => hup a b hab), hdiag]

theorem sq_eq_one (x : Multiplicative (Fin 10 → ZMod 2)) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  funext k
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, two_nsmul]
  generalize Multiplicative.toAdd x k = y
  fin_cases y <;> rfl

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem coe_conjAct_apply (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    ((conjAct V g v : ↥V) : G) = g * v * (g : G)⁻¹ := rfl

theorem card_autOn_sylow (F : Frame125 T L V) {S : Subgroup G}
    (hS : QuasithinUnique.IsSylowTwoOf S L) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (autOn S V) = 2 ^ 10 := by
  have hA := isSylowTwoOf_autOn' hS hLV
  have hcard : Nat.card (autOn L V) = 2 ^ 10 * 9765 :=
    (Nat.card_congr F.γ.toEquiv).trans card_sl_five_zmod_two
  have h1 : (autOn S V).relIndex (autOn L V) * Nat.card (autOn S V) = Nat.card (autOn L V) := by
    have := Subgroup.relIndex_mul_card (autOn S V) (autOn L V)
    rwa [inf_of_le_left hA.1] at this
  obtain ⟨k, hk⟩ := hA.2.1.exists_card_eq
  have hodd : ¬ 2 ∣ (autOn S V).relIndex (autOn L V) := hA.2.2
  rw [hcard, hk] at h1
  rw [hk]
  generalize (autOn S V).relIndex (autOn L V) = i at h1 hodd
  have hk1 : k ≤ 10 := by
    have hd : 2 ^ k ∣ 2 ^ 10 * 9765 := Dvd.intro_left _ h1
    have hc : Nat.Coprime (2 ^ k) 9765 := Nat.Coprime.pow_left k (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc.dvd_of_dvd_mul_right hd)
  have hk2 : 10 ≤ k := by
    have hd : 2 ^ 10 ∣ i * 2 ^ k := ⟨9765, h1⟩
    have hc : Nat.Coprime (2 ^ 10) i :=
      Nat.Coprime.pow_left 10 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc.dvd_of_dvd_mul_left hd)
  rw [show k = 10 by omega]

theorem exists_act_of_upperTri (F : Frame125 T L V)
    (hS : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {u : SpecialLinearGroup (Fin 5) (ZMod 2)} (hu : IsUpperTri u) :
    ∃ (t : G) (ht : t ∈ Subgroup.normalizer (V : Set G)), t ∈ T ∧ ∀ v : ↥V,
      F.e (conjAct V ⟨t, ht⟩ v) =
        Multiplicative.ofAdd (JonesParshall.wedgeRep u (Multiplicative.toAdd (F.e v))) := by
  set A := autOn (T ⊓ L) V with hAdef
  have hA10 : Nat.card A = 2 ^ 10 := card_autOn_sylow F hS hLV
  let Φ : ↥A → (Fin 10 → ZMod 2) → (Fin 10 → ZMod 2) := fun a x =>
    Multiplicative.toAdd (F.e ((a : MulAut ↥V) (F.e.symm (Multiplicative.ofAdd x))))
  have hΦ : Function.Injective Φ := by
    intro a b hab
    apply Subtype.ext
    ext v
    have h := congrFun hab (Multiplicative.toAdd (F.e v))
    simp only [Φ, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h
    exact congrArg Subtype.val (F.e.injective (Multiplicative.toAdd.injective h))
  let W : Set ((Fin 10 → ZMod 2) → (Fin 10 → ZMod 2)) :=
    Set.range (fun u : {u : SpecialLinearGroup (Fin 5) (ZMod 2) // IsUpperTri u} =>
      ⇑(JonesParshall.wedgeRep u.1))
  have hsub : Set.range Φ ⊆ W := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨t, ht, htTL, hta⟩ := mem_autOn_iff_exists.mp a.2
    obtain ⟨u', hu', hact⟩ := F.borel t htTL.1
    refine ⟨⟨u', hu'⟩, funext fun x => ?_⟩
    have h := hact (F.e.symm (Multiplicative.ofAdd x)) (conjAct V ⟨t, ht⟩
      (F.e.symm (Multiplicative.ofAdd x))) rfl
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    simp only [Φ, ← hta, h, toAdd_ofAdd]
  have hW : W.ncard ≤ (Set.range Φ).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hΦ,
      hA10]
    exact (Finite.card_range_le _).trans card_upperTri_le
  have heq : Set.range Φ = W := Set.eq_of_subset_of_ncard_le hsub hW
  have hmem : ⇑(JonesParshall.wedgeRep u) ∈ Set.range Φ := heq ▸ ⟨⟨u, hu⟩, rfl⟩
  obtain ⟨a, ha⟩ := hmem
  obtain ⟨t, ht, htTL, hta⟩ := mem_autOn_iff_exists.mp a.2
  refine ⟨t, ht, htTL.1, fun v => ?_⟩
  have h := congrFun ha (Multiplicative.toAdd (F.e v))
  simp only [Φ, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h
  rw [hta, ← h, ofAdd_toAdd]

end S125ZV

open S125ZV

theorem frame125ZV_of (h1222 : Stmt12_2_2) : Frame125ZV := by
  intro G _ _ T L V F hH
  obtain ⟨hVT, hTV⟩ : V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) := by
    rcases h1222 G T hH.hyp.simple hH.hyp.nonabelian hH.hyp.qtke hH.hyp.sylow with hA | h3
    · exact absurd hA hH.hyp.notAlt
    obtain ⟨-, -, hall⟩ := h3 L hH.hyp.maximal hH.hyp.faithful hH.hyp.quasisimple
    obtain ⟨⟨hVT, hTV, -⟩, -⟩ := hall V hH.hyp.irrPlus
    exact ⟨hVT, hTV⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hS : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    SzN19.isSylowTwoOf_inf_of_normalizes
      (isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow le_sup_right) le_sup_left
      hH.hyp.normalizes le_rfl
  apply le_antisymm
  ·
    rintro g ⟨hgV, hgZ⟩
    have hgC : g ∈ Subgroup.centralizer (T : Set G) := by
      refine (Subgroup.closure_le _).2 ?_ hgZ
      rintro z ⟨⟨-, hz⟩, -⟩
      exact hz
    set v : ↥V := ⟨g, hgV⟩ with hv
    set x : Fin 10 → ZMod 2 := Multiplicative.toAdd (F.e v) with hx
    have hfix : ∀ M : Matrix (Fin 5) (Fin 5) (ZMod 2), (M = tr0 ∨ M = tr1 ∨ M = tr2 ∨ M = tr3) →
        JonesParshall.wedgeMat M *ᵥ x = x := by
      intro M hM
      obtain ⟨u, hu, rfl⟩ := exists_tr M hM
      obtain ⟨t, ht, htT, hact⟩ := exists_act_of_upperTri F hS hLV hu
      have hc : conjAct V ⟨t, ht⟩ v = v := by
        apply Subtype.ext
        rw [coe_conjAct_apply]
        change t * g * t⁻¹ = g
        rw [Subgroup.mem_centralizer_iff.1 hgC t htT, mul_inv_cancel_right]
      have h := hact v
      rw [hc] at h
      rw [← wedgeRep_apply, hx, ← toAdd_ofAdd (JonesParshall.wedgeRep u _), ← h]
    have h0 := fixed_tr x (hfix _ (Or.inl rfl)) (hfix _ (Or.inr (Or.inl rfl)))
      (hfix _ (Or.inr (Or.inr (Or.inl rfl)))) (hfix _ (Or.inr (Or.inr (Or.inr rfl))))
    refine ⟨v, ?_, rfl⟩
    intro k hk
    exact h0 k (by simpa using hk)
  ·
    rintro _ ⟨v, hv, rfl⟩
    have hv0 : ∀ k : Fin 10, k ≠ 0 → Multiplicative.toAdd (F.e v) k = 0 := fun k hk =>
      hv k (by simpa using hk)
    have hsingle : Multiplicative.toAdd (F.e v) =
        Pi.single 0 (Multiplicative.toAdd (F.e v) 0) := by
      funext k
      by_cases hk : k = 0
      · subst hk
        simp
      · rw [hv0 k hk, Pi.single_eq_of_ne hk]
    refine ⟨v.2, Subgroup.subset_closure ⟨⟨hVT v.2, ?_⟩, ?_⟩⟩
    · show (v : G) ∈ Subgroup.centralizer (T : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro t htT
      obtain ⟨u, hu, hact⟩ := F.borel t htT
      have ht : t ∈ Subgroup.normalizer (V : Set G) := hTV htT
      have h := hact v (conjAct V ⟨t, ht⟩ v) rfl
      rw [wedgeRep_apply, hsingle, wedgeMat_mulVec_single hu, ← hsingle, ofAdd_toAdd] at h
      have h2 : conjAct V ⟨t, ht⟩ v = v := F.e.injective h
      have h3 : t * (v : G) * t⁻¹ = v := congrArg Subtype.val h2
      calc t * (v : G) = t * (v : G) * t⁻¹ * t := by group
        _ = v * t := by rw [h3]
    · show (v : G) ^ 2 = 1
      have h := congrArg Subtype.val (F.e.injective
        ((map_pow F.e v 2).trans ((sq_eq_one (F.e v)).trans (map_one F.e).symm)))
      simpa using h

end CFSG.Quasithin.H13
