module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMStat

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

inductive VStat where
  | cover (j : ℕ) (w : List (List ℕ)) (e : List ℕ)
  | five (u n c a b : List ℕ)
  | direct (j : ℕ) (w : List (List ℕ)) (e : List ℕ) (cw : List (List ℕ × List ℕ))

@[expose] def VStat.isCover : VStat → Bool
  | .cover _ _ _ => true
  | _ => false

structure Rep where
  a : List ℕ
  b : List ℕ
  st : VStat
  red : List (List ℕ × List ℕ × List ℕ × List ℕ × ℕ)

@[expose] def Rep.dflt : Rep := ⟨[], [], .five [] [] [] [] [], []⟩

@[expose] def CentChk (tLit sLit : List (List ℕ)) (a b : List ℕ) : Bool :=
  tLit.all fun t => !(ccomm t a && ccomm t b) || sLit.contains t

@[expose] def CoreChk (tLit sLit V : List (List ℕ)) (cw : List (List ℕ × List ℕ)) : Bool :=
  tLit.length == cw.length &&
  (tLit.zip cw).all fun p => sLit.contains p.1 ||
    (tLit.contains p.2.1 && V.contains p.2.2 && !(ccomm (cconj (cinv p.2.1) p.1) p.2.2))

@[expose] def VStatChk (tLit t0Lit : List (List ℕ)) (Ks : List KData) (a b : List ℕ) :
    VStat → Bool
  | .cover j w e => decide (j < Ks.length) && (ce4 a b).all (Ks.getD j KData.dflt).sLit.contains &&
      CentChk tLit (Ks.getD j KData.dflt).sLit a b && (ce4 a b).contains e &&
      NonormChk tLit (Ks.getD j KData.dflt) w e
  | .five u n c a' b' => FiveChk tLit t0Lit (ce4 a b) u n c a' b'
  | .direct j w e cw => decide (j < Ks.length) &&
      (ce4 a b).all (Ks.getD j KData.dflt).sLit.contains && (ce4 a b).contains e &&
      NonormChk tLit (Ks.getD j KData.dflt) w e && CoreChk tLit (Ks.getD j KData.dflt).sLit (ce4 a b) cw

@[expose] def RepChk (tLit : List (List ℕ)) (a b : List ℕ) : Bool :=
  (ce4 a b).all tLit.contains && NFA6.Core.nodupB (ce4 a b) &&
  (ce4 a b).all fun x => (ce4 a b).all fun y => (ce4 a b).contains (Core.cmul x y)

@[expose] def ce8 (a b c : List ℕ) : List (List ℕ) := ce4 a b ++ (ce4 a b).map (Core.cmul c)

@[expose] def RedEntChk (tLit : List (List ℕ)) (reps : List Rep) (a b : List ℕ)
    (e : List ℕ × List ℕ × List ℕ × List ℕ × ℕ) : Bool :=
  (ce8 a b e.1).contains e.2.1 && (ce8 a b e.1).contains e.2.2.1 && tLit.contains e.2.2.2.1 &&
  decide (e.2.2.2.2 < reps.length) && (reps.getD e.2.2.2.2 Rep.dflt).st.isCover &&
  NFA6.Core.setEq ((ce4 e.2.1 e.2.2.1).map (cconj (cinv e.2.2.2.1)))
    (ce4 (reps.getD e.2.2.2.2 Rep.dflt).a (reps.getD e.2.2.2.2 Rep.dflt).b)

@[expose] def RedChk (tLit : List (List ℕ)) (reps : List Rep) (R : Rep) : Bool :=
  R.st.isCover || tLit.all fun c =>
    !(cinvol c && ccomm c R.a && ccomm c R.b && !((ce4 R.a R.b).contains c)) ||
      R.red.any fun e => e.1 == c && RedEntChk tLit reps R.a R.b e

@[expose] def RepsChk (tLit t0Lit : List (List ℕ)) (Ks : List KData) (reps : List Rep) : Bool :=
  reps.all fun R => RepChk tLit R.a R.b && VStatChk tLit t0Lit Ks R.a R.b R.st && RedChk tLit reps R

@[expose] def PairEntChk (tLit : List (List ℕ)) (reps : List Rep) (a0 : List ℕ)
    (e : List ℕ × List ℕ × ℕ) : Bool :=
  tLit.contains e.2.1 && decide (e.2.2 < reps.length) &&
  NFA6.Core.setEq ((ce4 a0 e.1).map (cconj (cinv e.2.1)))
    (ce4 (reps.getD e.2.2 Rep.dflt).a (reps.getD e.2.2 Rep.dflt).b)

@[expose] def PairsChk (tLit : List (List ℕ)) (reps : List Rep)
    (pairs : List (List ℕ × List (List ℕ × List ℕ × ℕ))) : Bool :=
  pairs.all fun pa => tLit.all fun b => !(cinvol b && ccomm b pa.1 && b != pa.1) ||
    pa.2.any fun e => e.1 == b && PairEntChk tLit reps pa.1 e

@[expose] def ConjRepChk (tLit : List (List ℕ))
    (pairs : List (List ℕ × List (List ℕ × List ℕ × ℕ))) (cw : List (List ℕ × ℕ)) : Bool :=
  tLit.length == cw.length &&
  (tLit.zip cw).all fun p => !(cinvol p.1) || (tLit.contains p.2.1 &&
    decide (p.2.2 < pairs.length) && cconj (cinv p.2.1) p.1 == (pairs.getD p.2.2 ([], [])).1)

variable {i : Fin 4} {tLit : List (List ℕ)}

abbrev TableDisj (i : Fin 4) (A : Subgroup ↥(GB i)) : Prop :=
  (∃ H R Lh : Subgroup ↥(GB i), FiveWit (L1b i) (L2b i) (Tb i) A H R Lh) ∨
    ∃ K Y : Subgroup ↥(GB i), SevenWit (L1b i) (L2b i) (Tb i) A K Y

abbrev Seeded (A : Subgroup ↥(GB i)) (L : List (List ℕ)) : Prop := ∀ c ∈ L, ∃ x ∈ A, code x.1 = c

theorem code_conj_inv (t x : P16) : code (t⁻¹ * x * t) = cconj (cinv (code t)) (code x) := by
  rw [← code_inv, ← code_conj, inv_inv]

theorem seeded_conj {A : Subgroup ↥(GB i)} {L L' : List (List ℕ)} (hA : Seeded A L) (t : ↥(GB i))
    (h : ∀ c, c ∈ L.map (cconj (cinv (code t.1))) ↔ c ∈ L') :
    Seeded (A.map (MulAut.conj t⁻¹).toMonoidHom) L' := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ((h c).2 hc)
  obtain ⟨x, hx, rfl⟩ := hA d hd
  refine ⟨t⁻¹ * x * t, ⟨x, hx, by simp⟩, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, code_conj_inv]

theorem seeded_ce4 {A : Subgroup ↥(GB i)} {x y : ↥(GB i)} (hx : x ∈ A) (hy : y ∈ A) :
    Seeded A (ce4 (code x.1) (code y.1)) := by
  intro c hc
  simp only [ce4, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem A, by rw [Subgroup.coe_one, code_one]⟩
  · exact ⟨x, hx, rfl⟩
  · exact ⟨y, hy, rfl⟩
  · exact ⟨x * y, mul_mem hx hy, by rw [Subgroup.coe_mul, code_mul]⟩

theorem seeded_ce4_of {A : Subgroup ↥(GB i)} {L : List (List ℕ)} (hA : Seeded A L) {p q : List ℕ}
    (hp : p ∈ L) (hq : q ∈ L) : Seeded A (ce4 p q) := by
  obtain ⟨x, hx, rfl⟩ := hA p hp
  obtain ⟨y, hy, rfl⟩ := hA q hq
  exact seeded_ce4 hx hy

theorem seeded_ce8 {A : Subgroup ↥(GB i)} {a b : List ℕ} (hA : Seeded A (ce4 a b)) {c : ↥(GB i)}
    (hc : c ∈ A) : Seeded A (ce8 a b (code c.1)) := by
  intro d hd
  rcases List.mem_append.1 hd with h | h
  · exact hA d h
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 h
    obtain ⟨x, hx, rfl⟩ := hA d' hd'
    exact ⟨c * x, mul_mem hc hx, by rw [Subgroup.coe_mul, code_mul]⟩

theorem repChk_parts {a b : List ℕ} (h : RepChk tLit a b = true) :
    (∀ c ∈ ce4 a b, c ∈ tLit) ∧ (ce4 a b).Nodup ∧
      ∀ c ∈ ce4 a b, ∀ d ∈ ce4 a b, Core.cmul c d ∈ ce4 a b := by
  simp only [RepChk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1.1, nodup_of_nodupB' h.1.2, h.2⟩

theorem xdesc_of_seeded (hT : LDesc (TB i) tLit) {A : Subgroup ↥(GB i)} {a b : List ℕ}
    (hrep : RepChk tLit a b = true) (hA : Seeded A (ce4 a b)) (hA4 : Nat.card A ≤ 4) :
    XDesc A (ce4 a b) := by
  obtain ⟨h2, hnd, hm⟩ := repChk_parts hrep
  have h1 : cid ∈ ce4 a b := by simp [ce4]
  have hTd : XDesc (Tb i) tLit := ⟨mem_Tb_iff i hT, fun c hc => exists_Tb i hT hc⟩
  have hW := xdesc_xsub hTd h1 h2 hm
  have hWA : xsub i (ce4 a b) h1 hm ≤ A := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hA _ ((hW.mem x).1 hx)
    rwa [show x = y from Subtype.ext (code_injective hyx.symm)]
  have hc : Nat.card (xsub i (ce4 a b) h1 hm) = 4 := (hW.card hnd).trans rfl
  have e := eq_of_le_of_card_ge hWA (by rw [hc]; exact hA4)
  rw [← e]
  exact hW

theorem exists_outside (hT : LDesc (TB i) tLit) {A : Subgroup ↥(GB i)} {a b : List ℕ}
    (hrep : RepChk tLit a b = true) (hA4 : ¬ Nat.card A ≤ 4) :
    ∃ c ∈ A, code c.1 ∉ ce4 a b := by
  obtain ⟨h2, hnd, hm⟩ := repChk_parts hrep
  have h1 : cid ∈ ce4 a b := by simp [ce4]
  have hTd : XDesc (Tb i) tLit := ⟨mem_Tb_iff i hT, fun c hc => exists_Tb i hT hc⟩
  have hW := xdesc_xsub hTd h1 h2 hm
  by_contra hc
  push Not at hc
  have hAW : A ≤ xsub i (ce4 a b) h1 hm := fun x hx => (hW.mem x).2 (hc x hx)
  have := card_le_of_le hAW
  rw [hW.card hnd] at this
  exact hA4 this

theorem map_conj_props {A : Subgroup ↥(GB i)} (hAT : A ≤ Tb i) (hAe : IsElemAbelian 2 A)
    {t : ↥(GB i)} (ht : t ∈ Tb i) :
    A.map (MulAut.conj t⁻¹).toMonoidHom ≤ Tb i ∧
      IsElemAbelian 2 (A.map (MulAut.conj t⁻¹).toMonoidHom) ∧
      Nat.card (A.map (MulAut.conj t⁻¹).toMonoidHom) = Nat.card A := by
  refine ⟨?_, hAe.map _, card_map_equiv _ A⟩
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact mul_mem (mul_mem (inv_mem ht) (hAT hx)) ht

theorem tableDisj_of_conj (hTP : TPermChk (([u1, v1, u2, v2] ++ bGens i).map code) = true)
    {t : ↥(GB i)} (ht : t ∈ Tb i) {A : Subgroup ↥(GB i)}
    (h : TableDisj i (A.map (MulAut.conj t⁻¹).toMonoidHom)) : TableDisj i A := by
  have e : (A.map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj t).toMonoidHom = A := by
    have := map_conj_inv_map_conj A t⁻¹
    rwa [inv_inv] at this
  rw [← e]
  exact table_conj i hTP ht h

theorem sevenWit_of_cover_rep (hT : LDesc (TB i) tLit) {D : KData} (hE : KEnum D)
    (hC : KChk tLit D = true) (hTp : IsPGroup 2 (Tb i)) {a b e : List ℕ} {w : List (List ℕ)}
    (hS : ∀ c ∈ ce4 a b, c ∈ D.sLit) (hcen : CentChk tLit D.sLit a b = true) (he : e ∈ ce4 a b)
    (hw : NonormChk tLit D w e = true) {A : Subgroup ↥(GB i)} (hAT : A ≤ Tb i)
    (hAe : IsElemAbelian 2 A) (hA : Seeded A (ce4 a b)) :
    SevenWit (L1b i) (L2b i) (Tb i) A (Kx i D) (Yx i D) := by
  obtain ⟨aX, haA, hac⟩ := hA a (by simp [ce4])
  obtain ⟨bX, hbA, hbc⟩ := hA b (by simp [ce4])
  have haV : aX ∈ closure ({aX, bX} : Set ↥(GB i)) := subset_closure (by simp)
  have hbV : bX ∈ closure ({aX, bX} : Set ↥(GB i)) := subset_closure (by simp)
  have hVA : closure ({aX, bX} : Set ↥(GB i)) ≤ A := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact haA
    · exact hbA
  have hVS : closure ({aX, bX} : Set ↥(GB i)) ≤ Sx i D := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact (hE.s.mem x.1).2 (by rw [hac]; exact hS a (by simp [ce4]))
    · exact (hE.s.mem x.1).2 (by rw [hbc]; exact hS b (by simp [ce4]))
  have hcent : Tb i ⊓ centralizer (closure ({aX, bX} : Set ↥(GB i)) : Set ↥(GB i)) ≤ Sx i D := by
    rintro x ⟨hxT, hxc⟩
    have hxa : x * aX = aX * x := ((mem_centralizer_iff.1 hxc) aX haV).symm
    have hxb : x * bX = bX * x := ((mem_centralizer_iff.1 hxc) bX hbV).symm
    simp only [CentChk, List.all_eq_true] at hcen
    have h1 := hcen _ ((mem_Tb_iff i hT x).1 hxT)
    rw [← hac, ← hbc, ccomm_iff.2 (congrArg Subtype.val hxa),
      ccomm_iff.2 (congrArg Subtype.val hxb)] at h1
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h1
    exact (hE.s.mem _).2 h1
  obtain ⟨eX, heV, hec⟩ : ∃ eX ∈ closure ({aX, bX} : Set ↥(GB i)), code eX.1 = e := by
    simp only [ce4, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, by rw [Subgroup.coe_one, code_one]⟩
    · exact ⟨aX, haV, hac⟩
    · exact ⟨bX, hbV, hbc⟩
    · exact ⟨aX * bX, mul_mem haV hbV, by rw [Subgroup.coe_mul, code_mul, hac, hbc]⟩
  rw [← hec] at hw
  exact sevenWit_of_cover hT hE hC hTp hVS hcent heV hw hAT hAe hVA

theorem sevenWit_of_direct_rep (hT : LDesc (TB i) tLit) {D : KData} (hE : KEnum D)
    (hC : KChk tLit D = true) (hTp : IsPGroup 2 (Tb i)) {a b e : List ℕ} {w : List (List ℕ)}
    {cw : List (List ℕ × List ℕ)} (hrep : RepChk tLit a b = true)
    (hS : ∀ c ∈ ce4 a b, c ∈ D.sLit) (he : e ∈ ce4 a b) (hw : NonormChk tLit D w e = true)
    (hcore : CoreChk tLit D.sLit (ce4 a b) cw = true) {A : Subgroup ↥(GB i)}
    (hA : Seeded A (ce4 a b)) (hA4 : Nat.card A ≤ 4) :
    SevenWit (L1b i) (L2b i) (Tb i) A (Kx i D) (Yx i D) := by
  have hX := xdesc_of_seeded hT hrep hA hA4
  obtain ⟨eX, heA, rfl⟩ := hA e he
  have hAS : A ≤ Sx i D := fun x hx => (hE.s.mem _).2 (hS _ ((hX.mem x).1 hx))
  refine
    { le := hAS.trans le_sup_right
      irr := twoPTwoIrred_Kx hT hE hC hTp
      core := ?_
      nonorm := nonorm_of_chk hT hE hC hTp heA hw
      good := exists_good_Kx hT hE hC }
  intro x hx
  have hxT : x ∈ Tb i := coreIn_le_left _ _ hx
  simp only [CoreChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem, Bool.not_eq_true'] at hcore
  obtain ⟨hlen, hall⟩ := hcore
  have hxc : code x.1 ∈ tLit := (mem_Tb_iff i hT x).1 hxT
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hxc
  have hk' : k < cw.length := hlen ▸ hk
  have hz : (code x.1, cw[k]) ∈ tLit.zip cw := by
    rw [← hkx]
    exact List.mem_iff_getElem.2 ⟨k, by simp [hk, hk'], by simp⟩
  have h3 := hall _ hz
  simp only at h3
  rcases h3 with h | ⟨⟨hh, hv⟩, hnc⟩
  · exact mem_sup_right ((hE.s.mem _).2 h)
  · exfalso
    obtain ⟨hX', hhT, hhc⟩ := exists_Tb i hT hh
    obtain ⟨vX, hvA, hvc⟩ := hA _ hv
    have hcm := (hx.2 hX' hhT).2
    have h1 : (hX'⁻¹ * x * hX') * vX = vX * (hX'⁻¹ * x * hX') :=
      ((mem_centralizer_iff.1 hcm) vX hvA).symm
    have h2 : ccomm (cconj (cinv (cw[k]).1) (code x.1)) (cw[k]).2 = true := by
      rw [← hhc, ← hvc, ← code_conj_inv, ccomm_iff]
      exact congrArg Subtype.val h1
    rw [h2] at hnc
    exact Bool.noConfusion hnc

variable {t0Gen t0Lit : List (List ℕ)} {Ks : List KData}

theorem tableDisj_of_cover (hT : LDesc (TB i) tLit) (hTp : IsPGroup 2 (Tb i))
    (hK : ∀ j < Ks.length, KEnum (Ks.getD j KData.dflt) ∧ KChk tLit (Ks.getD j KData.dflt) = true)
    {a b : List ℕ} {st : VStat} (hst : VStatChk tLit t0Lit Ks a b st = true)
    (hc : st.isCover = true) {A : Subgroup ↥(GB i)} (hAT : A ≤ Tb i) (hAe : IsElemAbelian 2 A)
    (hA : Seeded A (ce4 a b)) : TableDisj i A := by
  cases st with
  | cover j w e =>
    simp only [VStatChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.contains_iff_mem] at hst
    obtain ⟨⟨⟨⟨hj, hS⟩, hcen⟩, he⟩, hw⟩ := hst
    obtain ⟨hE, hC⟩ := hK j hj
    exact Or.inr ⟨_, _, sevenWit_of_cover_rep hT hE hC hTp hS hcen he hw hAT hAe hA⟩
  | five => exact absurd hc (by simp [VStat.isCover])
  | direct => exact absurd hc (by simp [VStat.isCover])

theorem tableDisj_of_small (hT : LDesc (TB i) tLit) (h0 : T0Data tLit t0Gen t0Lit)
    (hTp : IsPGroup 2 (Tb i))
    (hK : ∀ j < Ks.length, KEnum (Ks.getD j KData.dflt) ∧ KChk tLit (Ks.getD j KData.dflt) = true)
    {a b : List ℕ} (hrep : RepChk tLit a b = true) {st : VStat}
    (hst : VStatChk tLit t0Lit Ks a b st = true) (hc : st.isCover = false)
    {A : Subgroup ↥(GB i)} (hA : Seeded A (ce4 a b)) (hA4 : Nat.card A ≤ 4) : TableDisj i A := by
  cases st with
  | cover => exact absurd hc (by simp [VStat.isCover])
  | five u n c a' b' =>
    exact Or.inl ⟨_, _, _, fiveWit_of_chk hT h0 hTp (xdesc_of_seeded hT hrep hA hA4)
      (repChk_parts hrep).2.1 hst⟩
  | direct j w e cw =>
    simp only [VStatChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.contains_iff_mem] at hst
    obtain ⟨⟨⟨⟨hj, hS⟩, he⟩, hw⟩, hcore⟩ := hst
    obtain ⟨hE, hC⟩ := hK j hj
    exact Or.inr ⟨_, _, sevenWit_of_direct_rep hT hE hC hTp hrep hS he hw hcore hA hA4⟩

theorem tableDisj_of_red (hT : LDesc (TB i) tLit)
    (hTP : TPermChk (([u1, v1, u2, v2] ++ bGens i).map code) = true) {reps : List Rep} {R : Rep}
    (hrep : RepChk tLit R.a R.b = true) (hred : RedChk tLit reps R = true)
    (hc : R.st.isCover = false) {A : Subgroup ↥(GB i)} (hAT : A ≤ Tb i) (hAe : IsElemAbelian 2 A)
    (hA : Seeded A (ce4 R.a R.b)) (hA4 : ¬ Nat.card A ≤ 4)
    (hcov : ∀ r < reps.length, (reps.getD r Rep.dflt).st.isCover = true →
      ∀ A' : Subgroup ↥(GB i), A' ≤ Tb i → IsElemAbelian 2 A' →
        Seeded A' (ce4 (reps.getD r Rep.dflt).a (reps.getD r Rep.dflt).b) → TableDisj i A') :
    TableDisj i A := by
  obtain ⟨cX, hcA, hcc⟩ := exists_outside hT hrep hA4
  obtain ⟨aX, haA, hac⟩ := hA R.a (by simp [ce4])
  obtain ⟨bX, hbA, hbc⟩ := hA R.b (by simp [ce4])
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => by
    have := hAe.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hinv : cinvol (code cX.1) = true := by
    rw [cinvol_iff]
    refine ⟨fun h1 => hcc ?_, ?_⟩
    · rw [h1, code_one]
      simp [ce4]
    · rw [← Subgroup.coe_mul, ← pow_two, hAe.2 cX hcA]
      rfl
  have hca : ccomm (code cX.1) R.a = true := by
    rw [← hac, ccomm_iff]
    exact congrArg Subtype.val (hcomm _ hcA _ haA)
  have hcb : ccomm (code cX.1) R.b = true := by
    rw [← hbc, ccomm_iff]
    exact congrArg Subtype.val (hcomm _ hcA _ hbA)
  simp only [RedChk, hc, Bool.false_or, List.all_eq_true] at hred
  have h1 := hred _ ((mem_Tb_iff i hT cX).1 (hAT hcA))
  rw [hinv, hca, hcb, show (ce4 R.a R.b).contains (code cX.1) = false by
    simpa using hcc] at h1
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨e, -, he1, hent⟩ := h1
  simp only [RedEntChk, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hent
  obtain ⟨⟨⟨⟨⟨hp, hq⟩, hs⟩, hr⟩, hcov'⟩, hseq⟩ := hent
  rw [he1] at hp hq
  have hA8 := seeded_ce8 hA hcA
  obtain ⟨sX, hsT, hsc⟩ := exists_Tb i hT hs
  have hA' : Seeded (A.map (MulAut.conj sX⁻¹).toMonoidHom)
      (ce4 (reps.getD e.2.2.2.2 Rep.dflt).a (reps.getD e.2.2.2.2 Rep.dflt).b) := by
    refine seeded_conj (seeded_ce4_of hA8 hp hq) sX fun c => ?_
    rw [hsc]
    exact setEq_mem' hseq c
  obtain ⟨hAT', hAe', -⟩ := map_conj_props hAT hAe hsT
  exact tableDisj_of_conj hTP hsT (hcov _ hr hcov' _ hAT' hAe' hA')

theorem table_of_seeds (hT : LDesc (TB i) tLit) (h0 : T0Data tLit t0Gen t0Lit)
    (hTp : IsPGroup 2 (Tb i)) (hTP : TPermChk (([u1, v1, u2, v2] ++ bGens i).map code) = true)
    (hK : ∀ j < Ks.length, KEnum (Ks.getD j KData.dflt) ∧ KChk tLit (Ks.getD j KData.dflt) = true)
    {reps : List Rep} (hR : RepsChk tLit t0Lit Ks reps = true)
    {pairs : List (List ℕ × List (List ℕ × List ℕ × ℕ))} (hP : PairsChk tLit reps pairs = true)
    {cw : List (List ℕ × ℕ)} (hCR : ConjRepChk tLit pairs cw = true) :
    ∀ A : Subgroup ↥(GB i), A ≤ Tb i → IsElemAbelian 2 A → 4 ≤ Nat.card A → TableDisj i A := by
  have hRall : ∀ R ∈ reps, RepChk tLit R.a R.b = true ∧
      VStatChk tLit t0Lit Ks R.a R.b R.st = true ∧ RedChk tLit reps R = true := by
    simp only [RepsChk, List.all_eq_true, Bool.and_eq_true] at hR
    exact fun R hR' => ⟨(hR R hR').1.1, (hR R hR').1.2, (hR R hR').2⟩
  have hgetD : ∀ r < reps.length, reps.getD r Rep.dflt ∈ reps := fun r hr => by
    rw [List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr
  have key : ∀ r < reps.length, ∀ A' : Subgroup ↥(GB i), A' ≤ Tb i → IsElemAbelian 2 A' →
      Seeded A' (ce4 (reps.getD r Rep.dflt).a (reps.getD r Rep.dflt).b) → TableDisj i A' := by
    intro r hr A' hAT' hAe' hA'
    obtain ⟨hrep, hst, hred⟩ := hRall _ (hgetD r hr)
    cases hc : (reps.getD r Rep.dflt).st.isCover
    · by_cases h4 : Nat.card A' ≤ 4
      · exact tableDisj_of_small hT h0 hTp hK hrep hst hc hA' h4
      · exact tableDisj_of_red hT hTP hrep hred hc hAT' hAe' hA' h4
          fun r' hr' hc' A'' hAT'' hAe'' hA'' =>
            tableDisj_of_cover hT hTp hK (hRall _ (hgetD r' hr')).2.1 hc' hAT'' hAe'' hA''
    · exact tableDisj_of_cover hT hTp hK hst hc hAT' hAe' hA'
  intro A hAT hAe hA4
  obtain ⟨aX, haA, bX, hbA, ha1, hb1, hab⟩ := NFF7.exists_ne_one_ne_of_four_le hA4
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => by
    have := hAe.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hinvA : ∀ x ∈ A, x ≠ 1 → cinvol (code x.1) = true := fun x hx hx1 => by
    rw [cinvol_iff]
    refine ⟨fun h1 => hx1 (Subtype.ext h1), ?_⟩
    rw [← Subgroup.coe_mul, ← pow_two, hAe.2 x hx]
    rfl
  simp only [ConjRepChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.contains_iff_mem, decide_eq_true_eq] at hCR
  obtain ⟨hlen, hall⟩ := hCR
  have hac : code aX.1 ∈ tLit := (mem_Tb_iff i hT aX).1 (hAT haA)
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hac
  have hk' : k < cw.length := hlen ▸ hk
  have hz : (code aX.1, cw[k]) ∈ tLit.zip cw := by
    rw [← hkx]
    exact List.mem_iff_getElem.2 ⟨k, by simp [hk, hk'], by simp⟩
  have h3 := hall _ hz
  simp only at h3
  rw [hinvA aX haA ha1] at h3
  obtain ⟨⟨htc, hkk⟩, ha0⟩ := h3.resolve_left (by decide)
  obtain ⟨tX, htT, htc'⟩ := exists_Tb i hT htc
  set pa := pairs.getD (cw[k]).2 ([], []) with hpa
  obtain ⟨hAT1, hAe1, -⟩ := map_conj_props hAT hAe htT
  refine tableDisj_of_conj hTP htT ?_
  set A1 := A.map (MulAut.conj tX⁻¹).toMonoidHom with hA1
  have hm1 : ∀ x ∈ A, tX⁻¹ * x * tX ∈ A1 := fun x hx =>
    ⟨x, hx, by simp⟩
  have hcode : ∀ x : ↥(GB i), code (tX⁻¹ * x * tX).1 = cconj (cinv (code tX.1)) (code x.1) :=
    fun x => by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, code_conj_inv]
  have ha0' : code (tX⁻¹ * aX * tX).1 = pa.1 := by rw [hcode, htc', ha0]
  set b1 := tX⁻¹ * bX * tX with hb1def
  have hb1T : code b1.1 ∈ tLit := (mem_Tb_iff i hT b1).1 (hAT1 (hm1 bX hbA))
  have hb1ne : b1 ≠ 1 := fun h => hb1 (by
    have : bX = tX * b1 * tX⁻¹ := by rw [hb1def]; group
    rw [this, h]
    group)
  have hb1inv : cinvol (code b1.1) = true := by
    rw [cinvol_iff]
    refine ⟨fun h1 => hb1ne (Subtype.ext h1), ?_⟩
    rw [← Subgroup.coe_mul, ← pow_two, hAe1.2 b1 (hm1 bX hbA)]
    rfl
  have hb1c : ccomm (code b1.1) pa.1 = true := by
    rw [← ha0', ccomm_iff]
    have := hcomm _ hbA _ haA
    have e : b1 * (tX⁻¹ * aX * tX) = (tX⁻¹ * aX * tX) * b1 := by
      rw [hb1def]
      calc tX⁻¹ * bX * tX * (tX⁻¹ * aX * tX) = tX⁻¹ * (bX * aX) * tX := by group
        _ = tX⁻¹ * (aX * bX) * tX := by rw [this]
        _ = tX⁻¹ * aX * tX * (tX⁻¹ * bX * tX) := by group
    exact congrArg Subtype.val e
  have hb1a : code b1.1 ≠ pa.1 := by
    rw [← ha0']
    intro h
    apply hab
    have h' : b1 = tX⁻¹ * aX * tX := Subtype.ext (code_injective h)
    have e1 : aX = tX * (tX⁻¹ * aX * tX) * tX⁻¹ := by group
    have e2 : bX = tX * b1 * tX⁻¹ := by rw [hb1def]; group
    rw [e1, e2, h']
  have hpm : pa ∈ pairs := by
    rw [hpa, List.getD_eq_getElem _ _ hkk]
    exact List.getElem_mem hkk
  simp only [PairsChk, List.all_eq_true] at hP
  have h4 := hP pa hpm _ hb1T
  rw [hb1inv, hb1c, show (code b1.1 != pa.1) = true by simpa using hb1a] at h4
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h4
  obtain ⟨e, -, he1, hent⟩ := h4
  simp only [PairEntChk, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hent
  obtain ⟨⟨hs, hr⟩, hseq⟩ := hent
  obtain ⟨sX, hsT, hsc⟩ := exists_Tb i hT hs
  have hA1s : Seeded A1 (ce4 pa.1 e.1) := by
    rw [he1, ← ha0']
    exact seeded_ce4 (hm1 aX haA) (hm1 bX hbA)
  obtain ⟨hAT2, hAe2, -⟩ := map_conj_props hAT1 hAe1 hsT
  refine tableDisj_of_conj hTP hsT (key _ hr _ hAT2 hAe2 ?_)
  refine seeded_conj hA1s sX fun c => ?_
  rw [hsc]
  exact setEq_mem' hseq c

@[expose] def ZChk (tLit zL : List (List ℕ)) : Bool :=
  zL.contains cid && zL.all tLit.contains && NFA6.Core.nodupB zL && zL.length == 4 &&
  zL.all fun x => zL.all fun y => zL.contains (Core.cmul x y)

theorem close_of_z (hT : LDesc (TB i) tLit) (h0 : T0Data tLit t0Gen t0Lit)
    (hTp : IsPGroup 2 (Tb i)) {zL ws : List (List ℕ)} (hz : ZChk tLit zL = true)
    (hci : CloseInvChk tLit [zL] ws = true) {u n c a b : List ℕ}
    (h5 : FiveChk tLit t0Lit zL u n c a b = true) :
    ∀ U E : Subgroup ↥(GB i), U ≤ E → E ≤ Tb i → Tb i ≤ normalizer (E : Set ↥(GB i)) →
      IsElemAbelian 2 E → 4 ≤ Nat.card U → CloseDisj i U := by
  simp only [ZChk, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true, beq_iff_eq] at hz
  obtain ⟨⟨⟨⟨h1, h2⟩, hnd⟩, h4⟩, hm⟩ := hz
  have hTd : XDesc (Tb i) tLit := ⟨mem_Tb_iff i hT, fun c hc => exists_Tb i hT hc⟩
  have hZ := xdesc_xsub hTd h1 h2 hm
  intro U E hUE hET hTE hEe hU4
  have hEZ : E ≤ xsub i zL h1 hm := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    obtain ⟨L, hL, hxL⟩ := mem_of_normal_elab hT hci hET hTE hEe hx hx1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    subst hL
    exact (hZ.mem x).2 hxL
  have hUZ : U = xsub i zL h1 hm := eq_of_le_of_card_ge (hUE.trans hEZ)
    (by rw [hZ.card (nodup_of_nodupB' hnd), h4]; exact hU4)
  rw [hUZ]
  exact Or.inl ⟨_, _, _, fiveWit_of_chk hT h0 hTp hZ (nodup_of_nodupB' hnd) h5⟩

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
