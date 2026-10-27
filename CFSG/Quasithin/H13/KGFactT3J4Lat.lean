module

public import CFSG.Quasithin.H13.KGFactT3J4Inputs
public import Certificates.Certificate7171
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Check
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Lat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM3Orb
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeBasic
public import CFSG.Quasithin.H13.NQCatT513L24
public import Certificates.Certificate4068
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Coset
public import CFSG.Sporadic.J4.QT2LocProof

public section

namespace CFSG.Quasithin.H13.KGT3J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Rad
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open CFSG.Quasithin.A312M24

@[expose] def starLetter (ℓ : ℤ) : Equiv.Perm (Fin 24) :=
  if 0 < ℓ then tauOf (ℓ.toNat - 1) else (tauOf ((-ℓ).toNat - 1))⁻¹

theorem tab_perm_eq {σ : Equiv.Perm (Fin 24)} {t : List ℕ} (ht : t.length = 24)
    (h : ∀ i : Fin 24, (σ i : ℕ) = t.getD i 0) : tab 24 σ = t := by
  apply List.ext_getElem
  · simp [tab, ht]
  · intro i h1 h2
    have hi : i < 24 := by simpa [tab] using h1
    have e := h ⟨i, hi⟩
    rw [List.getD_eq_getElem _ _ h2] at e
    simpa [tab] using e

theorem tab_tauOf {k : ℕ} (hk : k < 3) :
    tab 24 (tauOf k) = starPermOf k :=
  tab_perm_eq (star_perm_facts k hk).1 (tau_facts k hk).1

theorem tab_tauOf_inv {k : ℕ}
    (hk : k < 3) : tab 24 (tauOf k)⁻¹ = invTab24 (starPermOf k) := by
  have h := CFSG.QuasithinUnique.Setup.X1.tab_inv_of_inv (n := 24) (tauOf k) (starPermOf k).toArray
    (invTab24 (starPermOf k)).toArray (by rw [tab_tauOf hk]) (by simp [invTab24])
    (fun q hq => by simpa using Certificates.certificate7171.1 k hk q hq)
  simpa using h

theorem tab_starLetter {ℓ : ℤ}
    (hℓ : ℓ ∈ letters) : tab 24 (starLetter ℓ) = starLetterTab ℓ := by
  simp only [letters, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact tab_tauOf (k := 0) (by norm_num)
  · exact tab_tauOf (k := 1) (by norm_num)
  · exact tab_tauOf (k := 2) (by norm_num)
  · exact tab_tauOf_inv (k := 0) (by norm_num)
  · exact tab_tauOf_inv (k := 1) (by norm_num)
  · exact tab_tauOf_inv (k := 2) (by norm_num)

theorem tab_starWord :
    ∀ w : List ℤ, (∀ ℓ ∈ w, ℓ ∈ letters) → tab 24 (w.map starLetter).prod = starWordTab w
  | [], _ => by
    apply List.ext_getElem
    · simp [tab, starWordTab]
    · intro i h1 h2
      simp [tab, starWordTab]
  | ℓ :: w, h => by
    rw [List.map_cons, List.prod_cons, tab_mul, tab_starLetter (h ℓ (List.mem_cons_self ..)),
      tab_starWord w fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

theorem starHom_XJ
    {ℓ : ℤ} (hℓ : ℓ ∈ letters) :
    starHom ⟨XJ ℓ, XJ_mem hℓ⟩ = starLetter ℓ := by
  have hpos : ∀ k (hk : k < 3), starHom ⟨xJ k, xJ_mem hk⟩ = tauOf k := fun k hk => starHom_xJ hk
  simp only [letters, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [XJ, starLetter] using hpos 0 (by norm_num)
  · simpa [XJ, starLetter] using hpos 1 (by norm_num)
  · simpa [XJ, starLetter] using hpos 2 (by norm_num)
  · have e : (⟨XJ (-1), XJ_mem (by simp [letters])⟩ : ↥Hj) = (⟨xJ 0, xJ_mem (by norm_num)⟩)⁻¹ :=
      Subtype.ext (by simp [XJ])
    rw [e, map_inv, hpos 0 (by norm_num)]
    simp [starLetter]
  · have e : (⟨XJ (-2), XJ_mem (by simp [letters])⟩ : ↥Hj) = (⟨xJ 1, xJ_mem (by norm_num)⟩)⁻¹ :=
      Subtype.ext (by simp [XJ])
    rw [e, map_inv, hpos 1 (by norm_num)]
    simp [starLetter]
  · have e : (⟨XJ (-3), XJ_mem (by simp [letters])⟩ : ↥Hj) = (⟨xJ 2, xJ_mem (by norm_num)⟩)⁻¹ :=
      Subtype.ext (by simp [XJ])
    rw [e, map_inv, hpos 2 (by norm_num)]
    simp [starLetter]

theorem starHom_wordProd :
    ∀ (w : List ℤ) (hw : ∀ ℓ ∈ w, ℓ ∈ letters),
    starHom ⟨wordProd xJ w, wordProd_mem_Hj hw⟩ = (w.map starLetter).prod
  | [], hw => by
    have e : (⟨wordProd xJ [], wordProd_mem_Hj hw⟩ : ↥Hj) = 1 := Subtype.ext rfl
    rw [e, map_one]
    rfl
  | ℓ :: w, hw => by
    have hℓ : ℓ ∈ letters := hw ℓ (List.mem_cons_self ..)
    have hw' : ∀ x ∈ w, x ∈ letters := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    have e : (⟨wordProd xJ (ℓ :: w), wordProd_mem_Hj hw⟩ : ↥Hj) =
        ⟨XJ ℓ, XJ_mem hℓ⟩ * ⟨wordProd xJ w, wordProd_mem_Hj hw'⟩ :=
      Subtype.ext (by simp [wordProd_xJ])
    rw [e, map_mul, starHom_XJ hℓ, starHom_wordProd w hw', List.map_cons, List.prod_cons]

@[expose] noncomputable def fH :
    ↥Hj →* G24 :=
  starHom.codRestrict CFSG.Blueprint.NativeSporadic.M24 fun g => by
    rw [← range_starHom_eq]
    exact ⟨g, rfl⟩

theorem coe_fH
    (g : ↥Hj) :
    (fH g : Equiv.Perm (Fin 24)) = starHom g := by
  simp [fH]

theorem tab_fH
    (g : ↥Hj) :
    tab 24 (fH g) = tab 24 (starHom g) := by
  simp only [tab, Subgroup.smul_def, coe_fH]

theorem ker_fH :
    fH.ker = (Eg uJ 11).subgroupOf Hj := by
  rw [← ker_starHom]
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Subtype.coe_inj, coe_fH]
  rfl

theorem tab_fH_wordProd
    (w : List ℤ) (hw : ∀ ℓ ∈ w, ℓ ∈ letters) :
    tab 24 (fH ⟨wordProd xJ w, wordProd_mem_Hj hw⟩) = starWordTab w := by
  rw [tab_fH, starHom_wordProd w hw]
  exact tab_starWord w hw

@[expose] noncomputable def yM [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    G24 :=
  wordElt m24CtxE.a m24CtxE.b t3yWord

theorem tab_yM [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    (tab 24 yM).toArray = t3yTab := by
  have hel : ∀ l < (#[m24CtxE.a, m24CtxE.b] : Array G24).size,
      (#[m24CtxE.ta, m24CtxE.tb] : Array (Array ℕ)).getD l #[] =
        (tab 24 ((#[m24CtxE.a, m24CtxE.b] : Array G24).getD l 1)).toArray := by
    intro l hl
    have hl' : l < 2 := by simpa using hl
    interval_cases l
    · exact m24CtxE.ha.symm
    · exact m24CtxE.hb.symm
  have hw : ∀ l ∈ t3yWord, l < 2 := by decide +kernel
  exact (wordTabA_eq (n := 24) #[m24CtxE.a, m24CtxE.b] #[m24CtxE.ta, m24CtxE.tb] hel t3yWord
    fun l hl => by simpa using hw l hl).symm

theorem lab_yM [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    lab 24 m24CtxE.A m24CtxE.Δ yM = t3yLab := by
  show m24CtxE.A.act (tab 24 yM).toArray m24CtxE.Δ = _
  rw [tab_yM]
  rfl

@[expose] noncomputable def kappa [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    G24 →* G24 :=
  (MulAut.conj yM⁻¹).toMonoidHom

theorem kappa_apply [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (x : G24) : kappa x = yM⁻¹ * x * yM := by
  simp [kappa]

theorem kappa_injective [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Function.Injective kappa :=
  (MulAut.conj yM⁻¹).injective

theorem kappa_surjective [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Function.Surjective kappa :=
  (MulAut.conj yM⁻¹).surjective

theorem card_map_fH
    {Z : Subgroup J}
    (hEZ : Eg uJ 11 ≤ Z) (hZH : Z ≤ Hj) :
    Nat.card ((Z.subgroupOf Hj).map fH) * 2 ^ 11 = Nat.card Z := by
  have hM := j4Facts.mat
  set g : ↥(Z.subgroupOf Hj) →* G24 := fH.comp (Z.subgroupOf Hj).subtype with hg
  have h1 := Subgroup.card_ker_mul_card_range g
  have hr : g.range = (Z.subgroupOf Hj).map fH := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : g.ker = fH.ker.subgroupOf (Z.subgroupOf Hj) := by
    rw [hg, ← MonoidHom.comap_ker]
    rfl
  have hkle : fH.ker ≤ Z.subgroupOf Hj := by
    rw [ker_fH]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hEZ (Subgroup.mem_subgroupOf.mp hx))
  have hkc : Nat.card g.ker = 2 ^ 11 := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkle).toEquiv, ker_fH,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Eg_le_Hj).toEquiv, card_Eg_uJ hM]
  have hZc : Nat.card ↥(Z.subgroupOf Hj) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
  rw [hr, hkc, hZc] at h1
  rw [← h1, mul_comm]

theorem kappa_fH_kJ_mem [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {i : ℕ} (hi : i < 4) : kappa (fH ⟨kJ i, kJ_mem hi⟩) ∈ m24CtxE.S := by
  rw [kappa_apply, m24CtxE.conj_mem_S_iff, lab_yM]
  have h := tab_fH_wordProd (kWords.getD i []) (kJ_letters hi)
  have e : (⟨kJ i, kJ_mem hi⟩ : ↥Hj) =
      ⟨wordProd xJ (kWords.getD i []), wordProd_mem_Hj (kJ_letters hi)⟩ := rfl
  rw [e, h]
  exact Certificates.certificate7171.2.1 i hi

theorem map_P0_eq_S [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    ((P0.subgroupOf Hj).map fH).map kappa = m24CtxE.S := by
  have hM := j4Facts.mat
  have hle : ((P0.subgroupOf Hj).map fH).map kappa ≤ m24CtxE.S := by
    rw [Subgroup.map_map, Subgroup.map_le_iff_le_comap]
    have key : P0 ≤ (m24CtxE.S.comap (kappa.comp fH)).map Hj.subtype := by
      rw [Subgroup.closure_le]
      rintro g (⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩)
      · refine ⟨⟨uJ j, uJ_mem hj⟩, ?_, rfl⟩
        have h1 : fH ⟨uJ j, uJ_mem hj⟩ = 1 := by
          rw [← MonoidHom.mem_ker, ker_fH]
          exact Subgroup.mem_subgroupOf.mpr (u_mem_Eg hj)
        show kappa (fH _) ∈ m24CtxE.S
        rw [h1, map_one]
        exact one_mem _
      · exact ⟨⟨kJ i, kJ_mem hi⟩, kappa_fH_kJ_mem hi, rfl⟩
    intro x hx
    obtain ⟨z, hz, hzx⟩ := key (Subgroup.mem_subgroupOf.mp hx)
    rw [show z = x from Subtype.ext hzx] at hz
    exact hz
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective kappa_injective, m24CtxE.S_card]
  have h := card_map_fH (Z := P0) Eg_le_P0 P0_le_Hj
  rw [card_P0 hM j4Facts] at h
  have hk : m24CtxE.k = 10 := rfl
  rw [hk]
  omega

theorem S_le_conj [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {Z : Subgroup J} (hPZ : P0 ≤ Z) : m24CtxE.S ≤ ((Z.subgroupOf Hj).map fH).map kappa := by
  rw [← map_P0_eq_S]
  exact Subgroup.map_mono (Subgroup.map_mono fun x hx => hPZ hx)

theorem P0_le_NV :
    P0 ≤ NV := by
  have hM := j4Facts.mat
  refine le_inf P0_le_Hj ?_
  rw [Subgroup.closure_le]
  rintro g (⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩)
  · refine CFSG.Quasithin.H13.NQCat.T513.mem_normalizer_of_conj_mem fun x hx => ?_
    have hc := Eg_comm (elem_uJ hM) (u_mem_Eg hj) (V0_le_Eg' hM hx)
    rw [hc, mul_inv_cancel_right]
    exact hx
  · refine CFSG.Quasithin.H13.NQCat.T513.mem_normalizer_of_conj_mem fun x hx => ?_
    have hA := Acts_kJ hM hi
    have hgen : ∀ v ∈ ({eta uJ 11 422, eta uJ 11 553, eta uJ 11 1131} : Set J),
        kJ i * v * (kJ i)⁻¹ ∈ V0 := by
      rintro v (rfl | rfl | rfl)
      · rw [hA.2 422 (by norm_num)]
        exact (mem_V0_iff hM).2 ⟨_, Certificates.certificate7171.2.2.1 i hi 422 (by simp),
          rfl⟩
      · rw [hA.2 553 (by norm_num)]
        exact (mem_V0_iff hM).2 ⟨_, Certificates.certificate7171.2.2.1 i hi 553 (by simp),
          rfl⟩
      · rw [hA.2 1131 (by norm_num)]
        exact (mem_V0_iff hM).2 ⟨_, Certificates.certificate7171.2.2.1 i hi 1131
          (by simp), rfl⟩
    have hmap : V0.map (MulAut.conj (kJ i)).toMonoidHom ≤ V0 := by
      rw [V0, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨v, hv, rfl⟩
      exact hgen v hv
    exact hmap ⟨x, hx, rfl⟩

@[expose] noncomputable def cJ : J := wordProd xJ t3cWord

theorem t3cWord_letters : ∀ ℓ ∈ t3cWord, ℓ ∈ letters := by decide

theorem cJ_mem_CV :
    cJ ∈ CV := by
  have hM := j4Facts.mat
  refine Subgroup.mem_inf.mpr ⟨wordProd_mem_Hj t3cWord_letters, ?_⟩
  have hA := Acts_wordProd hM t3cWord t3cWord_letters
  rw [V0, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  have hfix : ∀ v ∈ [422, 553, 1131], cJ * eta uJ 11 v * cJ⁻¹ = eta uJ 11 v := by
    intro v hv
    have hv' : v < 2 ^ 11 := by simp at hv; omega
    rw [show cJ = wordProd xJ t3cWord from rfl, hA.2 v hv',
      Certificates.certificate7171.2.2.2 v hv]
  rintro x (rfl | rfl | rfl)
  · have := hfix 422 (by simp)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · have := hfix 553 (by simp)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · have := hfix 1131 (by simp)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm

theorem card_NV :
    Nat.card NV = 63 * 2 ^ 21 := by
  have hF := j4Facts
  have h := Subgroup.card_mul_index (NV.subgroupOf Hj)
  rw [(idx_eq hF.mat).1, card_Hj hF,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe NV_le_Hj).toEquiv] at h
  have e : (501397585920 : ℕ) = 63 * 2 ^ 21 * 3795 := by norm_num
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem card_of_le_Hj [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {Z : Subgroup J} (hPZ : P0 ≤ Z) (hZH : Z ≤ Hj) :
    Z = Hj ∨ ∃ j < 13, Nat.card Z = memIdx[j]! * 2 ^ 21 := by
  have hc := card_map_fH (Eg_le_P0.trans hPZ) hZH
  by_cases htop : ((Z.subgroupOf Hj).map fH).map kappa = ⊤
  · left
    have h1 : (Z.subgroupOf Hj).map fH = ⊤ := by
      apply Subgroup.map_injective kappa_injective
      rw [htop, Subgroup.map_top_of_surjective _ kappa_surjective]
    have hkle : fH.ker ≤ Z.subgroupOf Hj := by
      rw [ker_fH]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr ((Eg_le_P0.trans hPZ) (Subgroup.mem_subgroupOf.mp hx))
    have h2 : Z.subgroupOf Hj = ⊤ := by
      have h3 := Subgroup.comap_map_eq fH (Z.subgroupOf Hj)
      rw [h1, Subgroup.comap_top, sup_eq_left.mpr hkle] at h3
      exact h3.symm
    refine le_antisymm hZH fun x hx => ?_
    have : (⟨x, hx⟩ : ↥Hj) ∈ Z.subgroupOf Hj := by
      rw [h2]
      exact Subgroup.mem_top _
    exact this
  · right
    obtain ⟨j, hj, -, hcard⟩ := overgroup_member (S_le_conj hPZ) htop
    refine ⟨j, hj, ?_⟩
    rw [Subgroup.card_map_of_injective kappa_injective] at hcard
    rw [← hc, hcard]
    ring

theorem le_NV_of_card_nine [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {Z : Subgroup J} (hPZ : P0 ≤ Z) (hZH : Z ≤ Hj) (hZ : Nat.card Z = 9 * 2 ^ 21)
    (hCV : CV ≤ Z) : Z ≤ NV := by
  have hc := card_map_fH (Eg_le_P0.trans hPZ) hZH
  have hWc : Nat.card (((Z.subgroupOf Hj).map fH).map kappa) = 9 * 2 ^ 10 := by
    rw [Subgroup.card_map_of_injective kappa_injective]
    omega
  have htop : ((Z.subgroupOf Hj).map fH).map kappa ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, show Nat.card G24 = 244823040 from CFSG.Sporadic.Mathieu.card_M24]
      at hWc
    norm_num at hWc
  obtain ⟨j, hj, hWj, -⟩ := overgroup_member (S_le_conj hPZ) htop
  set c : ↥Hj := ⟨cJ, wordProd_mem_Hj t3cWord_letters⟩ with hcdef
  have hcW : kappa (fH c) ∈ m24CtxE.Y j := by
    rw [← hWj]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (hCV cJ_mem_CV)))
  have hct : tab 24 (fH c) = starWordTab t3cWord := tab_fH_wordProd t3cWord t3cWord_letters
  rw [kappa_apply] at hcW
  have hYc : Nat.card (m24CtxE.Y j) = 9 * 2 ^ 10 := by rw [← hWj, hWc]
  have hY2 : m24CtxE.Y j ≤ m24CtxE.Y 2 :=
    Certificates.certificate4068.2.2.2.2.2.1 (fH c) hct j hj hYc hcW
  have hPNV := P0_le_NV
  have hcN := card_map_fH (Eg_le_P0.trans hPNV) NV_le_Hj
  have hWNc : Nat.card (((NV.subgroupOf Hj).map fH).map kappa) = 63 * 2 ^ 10 := by
    rw [Subgroup.card_map_of_injective kappa_injective]
    rw [card_NV] at hcN
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) (hcN.trans (by norm_num))
  have htopN : ((NV.subgroupOf Hj).map fH).map kappa ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, show Nat.card G24 = 244823040 from CFSG.Sporadic.Mathieu.card_M24]
      at hWNc
    norm_num at hWNc
  obtain ⟨j', hj', hWNj, hcard'⟩ := overgroup_member (S_le_conj hPNV) htopN
  have hj2 : j' = 2 := idx_63 j' hj' (by rw [hWNc] at hcard'; omega)
  subst hj2
  have hle : (Z.subgroupOf Hj).map fH ≤ (NV.subgroupOf Hj).map fH := by
    rw [← Subgroup.map_le_map_iff_of_injective kappa_injective, hWj, hWNj]
    exact hY2
  intro z hz
  obtain ⟨n, hn, hnz⟩ := hle ⟨⟨z, hZH hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  have hk : n⁻¹ * ⟨z, hZH hz⟩ ∈ fH.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnz, inv_mul_cancel]
  rw [ker_fH] at hk
  have hE : ((n⁻¹ * ⟨z, hZH hz⟩ : ↥Hj) : J) ∈ NV :=
    hPNV (Eg_le_P0 (Subgroup.mem_subgroupOf.mp hk))
  have hnNV : (n : J) ∈ NV := Subgroup.mem_subgroupOf.mp hn
  have e : z = (n : J) * ((n⁻¹ * ⟨z, hZH hz⟩ : ↥Hj) : J) := by simp
  rw [e]
  exact NV.mul_mem hnNV hE

end CFSG.Quasithin.H13.KGT3J4
