module

public import CFSG.Quasithin.H13.NQCatA314M22Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22
public import CFSG.Quasithin.EmptyFaithful.A38c14CentralLift
public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.Quasithin.Vol2.Ch10SecKITu
public import CFSG.Quasithin.H13.NQCatA314Gen
public import CFSG.Quasithin.H13.NQCatA314ShortMap

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat PermLat
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem eq_of_perfectCore_ext {G : Type} [Group G] [Finite G] {M L A : Subgroup G}
    {U B : Subgroup ↥M} (hB : B ∈ lFamily U) (hAL : A ≤ L) (hLM : L ≤ M) (hcomm : ⁅L, L⁆ ≤ A)
    (hperf : ⁅A, A⁆ = A) (hPL : B ⊔ U = L.subgroupOf M) {k : ℕ}
    [IsSimpleGroup (alternatingGroup (Fin k))]
    (hnab : ∃ a b : alternatingGroup (Fin k), a * b ≠ b * a) (V : Subgroup ↥A) [V.Normal]
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (e : ↥A ⧸ V ≃* alternatingGroup (Fin k)) :
    B = A.subgroupOf M := by
  have hAM : A ≤ M := hAL.trans hLM
  have hpc : perfectCore (B ⊔ U) = A.subgroupOf M := by
    rw [hPL]
    exact perfectCore_subgroupOf_eq hAL hLM hcomm hperf
  let eP : ↥(perfectCore (B ⊔ U)) ≃* ↥A :=
    (MulEquiv.subgroupCongr hpc).trans (Subgroup.subgroupOfEquivOfLe hAM)
  let g : ↥(perfectCore (B ⊔ U)) →* alternatingGroup (Fin k) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' V).comp eP.toMonoidHom)
  have hg : Function.Surjective g :=
    e.surjective.comp ((QuotientGroup.mk'_surjective V).comp eP.surjective)
  have hVsolv : Group.IsSolvable ↥V :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hVc a.1 a.2 b.1 b.2)
  have hsolv : Group.IsSolvable g.ker := by
    let φ : g.ker →* ↥V :=
      (eP.toMonoidHom.comp g.ker.subtype).codRestrict V fun x => by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx
        have : (QuotientGroup.mk' V) (eP (x : ↥(perfectCore (B ⊔ U)))) = 1 := by
          have := e.injective (hx.trans e.map_one.symm)
          exact this
        exact (QuotientGroup.eq_one_iff _).mp this
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : eP (x : ↥(perfectCore (B ⊔ U))) = eP (y : ↥(perfectCore (B ⊔ U))) :=
        congrArg Subtype.val hxy
      exact Subtype.ext (eP.injective h1)
    exact Group.isSolvable_of_isSolvable_injective hφ
  exact (lFamily_eq_perfectCore hB hnab g hg hsolv).trans hpc

theorem isSimpleGroup_Mgrp : IsSimpleGroup ↥Mgrp := by
  have := (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  exact (MulEquiv.subgroupCongr mGens_closure).isSimpleGroup

theorem isQuasisimple_Mgrp :
    CFSG.IsQuasisimple ↥Mgrp := by
  have := isSimpleGroup_Mgrp
  have hck := cert_check
  have hM : Nat.card Mgrp = 443520 :=
    cert.card_m (rawIsEnc 22) (LatCert.closedOK_of_check hck) (LatCert.sizesOK_of_check hck)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (nonabelian_of_simple_card (by rw [hM]; norm_num))).1

theorem m22_eq_B0
    {B : Subgroup ↥Mgrp} (hB : B ∈ lFamily Ugrp) (hc : Nat.card B = 960) :
    ∃ _ : Subgroup.closure {g | g ∈ p5Gens} ≤ Mgrp,
      B = (Subgroup.closure {g | g ∈ p5Gens}).subgroupOf Mgrp := by
  classical
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hB' : B ∈ cComp (B ⊔ Ugrp) := hB
  obtain ⟨j, hj, hLM, hPL, hcardj⟩ :=
    cert.overgroup_cases_idx (rawIsEnc 22) hck (B ⊔ Ugrp) le_sup_right
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  rw [hlen] at hj
  have hM : Nat.card Mgrp = 443520 := cert.card_m (rawIsEnc 22) hcl hsz
  have hdvd : 960 ∣ cert.sizes.getD j 0 := by
    have h1 : Nat.card B ∣ Nat.card ↥(B ⊔ Ugrp) := Subgroup.card_dvd_of_le le_sup_left
    rw [hPL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hc, hcardj] at h1
    exact h1
  interval_cases j
  · exact absurd hdvd (by decide)
  · exact absurd hdvd (by decide)
  ·
    have h1920 : cert.sizes.getD 2 0 = 1920 := rfl
    rw [h1920] at hcardj
    have ha := List.all_eq_true.mp incl5 2 (by simp)
    simp only [h1920, bne_self_eq_false, Bool.false_or] at ha
    have hlen2 : 2 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[2] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen2
    have hAL : Subgroup.closure {g | g ∈ p5Gens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen2] at this
      exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, V, hVn, hVc, -, -, ⟨e⟩⟩ := ext5
    have hcomm : ⁅Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]},
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]}⁆ ≤
          Subgroup.closure {g | g ∈ p5Gens} :=
      commutator_le_of_card_eq_two_mul hAL (by rw [hcardj, hAcard])
    have hperf : ⁅Subgroup.closure {g | g ∈ p5Gens}, Subgroup.closure {g | g ∈ p5Gens}⁆ =
        Subgroup.closure {g | g ∈ p5Gens} := perfect_of_perfOK (rawIsEnc 22) perf5_ok
    have := Seven.alt5_simple
    exact ⟨hAL.trans hLM, eq_of_perfectCore_ext hB hAL hLM hcomm hperf hPL
      Seven.alt5_nonabelian V hVc e⟩
  ·
    exfalso
    have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
    rw [h5760] at hcardj
    have ha := List.all_eq_true.mp incl6 3 (by simp)
    simp only [h5760, bne_self_eq_false, Bool.false_or] at ha
    have hlen3 : 3 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[3] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen3
    have hAL : Subgroup.closure {g | g ∈ l6Gens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen3] at this
      exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, V, hVn, hVc, -, -, ⟨e⟩⟩ := ext6
    have hLA := Subgroup.eq_of_le_of_card_ge hAL (by rw [hcardj, hAcard])
    have hcomm : ⁅Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]},
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]}⁆ ≤
          Subgroup.closure {g | g ∈ l6Gens} := by
      rw [← hLA]
      exact commutator_self_le _
    have hperf : ⁅Subgroup.closure {g | g ∈ l6Gens}, Subgroup.closure {g | g ∈ l6Gens}⁆ =
        Subgroup.closure {g | g ∈ l6Gens} := perfect_of_perfOK (rawIsEnc 22) perf6_ok
    have := Seven.alt6_simple
    have hBeq := eq_of_perfectCore_ext hB hAL hLM hcomm hperf hPL Seven.alt6_nonabelian V hVc e
    have h1 : Nat.card B = 5760 := by
      rw [hBeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAL.trans hLM)).toEquiv, hAcard]
    omega
  ·
    exfalso
    have h443520 : cert.sizes.getD 4 0 = 443520 := rfl
    rw [h443520] at hcardj
    have heq := Subgroup.eq_of_le_of_card_ge hLM (by rw [hM]; exact hcardj.symm.le)
    have htop : B ⊔ Ugrp = ⊤ := by
      rw [hPL]
      exact (congrArg (fun K => K.subgroupOf Mgrp) heq).trans (Subgroup.subgroupOf_self Mgrp)
    rw [htop] at hB'
    have h1 := A321.cComp_eq_top_of_quasisimple isQuasisimple_Mgrp hB'
    rw [h1, Subgroup.card_top, hM] at hc
    omega
  · exact absurd hdvd (by decide)

theorem m22_block_equiv
    {S B : Subgroup ↥Mgrp} (hS : IsSylowTwoOf S ⊤)
    (hB : B ∈ lFamily S) (hc : Nat.card B = 960) : Nonempty (↥K4 ≃* ↥B) := by
  have hck := cert_check
  have hU : IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 22) hck (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  obtain ⟨c, hcS⟩ := exists_conj_of_isSylowTwoOf hS hU
  set α : MulAut ↥Mgrp := MulAut.conj c with hα
  have hB' : B.map α.toMonoidHom ∈ lFamily Ugrp := by
    have h1 := cComp_map_mulEquiv α (show B ∈ cComp (B ⊔ S) from hB)
    rw [Subgroup.map_sup, hcS] at h1
    exact h1
  have hc' : Nat.card (B.map α.toMonoidHom) = 960 := by
    rw [Subgroup.card_map_of_injective α.injective, hc]
  obtain ⟨hle, hBeq⟩ := m22_eq_B0 hB' hc'
  obtain ⟨ψ⟩ := k4_equiv_B0
  exact ⟨ψ.trans (((Subgroup.subgroupOfEquivOfLe hle).symm.trans
    (MulEquiv.subgroupCongr hBeq.symm)).trans
      (B.equivMapOfInjective α.toMonoidHom α.injective).symm)⟩

theorem card_of_isExt_e16_a5 {X : Type} [Group X]
    (h : IsExt X (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) : Nat.card X = 960 := by
  obtain ⟨V, _, ⟨eV⟩, hA⟩ := h
  have hV : Nat.card V = 16 := by
    rw [Nat.card_congr (eV.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
    norm_num
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [A314.card_isAlt_five hA, hV] at h1
  exact h1

@[expose] noncomputable def m22EquivMgrp :
    CFSG.Blueprint.NativeSporadic.Carrier .M22 ≃* ↥Mgrp :=
  (MulEquiv.subgroupCongr mGens_closure).symm

theorem m22_block_equiv_of {X : Type} [Group X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) {T B : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hc : Nat.card B = 960) :
    Nonempty (↥K4 ≃* ↥B) := by
  let ψ : X ≃* ↥Mgrp := φ.trans m22EquivMgrp
  have : Finite X := Finite.of_equiv _ ψ.symm.toEquiv
  have hT' : IsSylowTwoOf (T.map ψ.toMonoidHom) ⊤ :=
    A312.isSylowTwoOf_top_map ψ.toMonoidHom ψ.surjective hT
  have hB' : B.map ψ.toMonoidHom ∈ lFamily (T.map ψ.toMonoidHom) := by
    have h1 := cComp_map_mulEquiv ψ (show B ∈ cComp (B ⊔ T) from hB)
    rwa [Subgroup.map_sup] at h1
  have hc' : Nat.card (B.map ψ.toMonoidHom) = 960 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hc]
  obtain ⟨θ⟩ := m22_block_equiv hT' hB' hc'
  exact ⟨θ.trans (B.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm⟩

theorem subgroupOf_mem_lFamily' {G : Type} [Group G] [Finite G] {L T B : Subgroup G}
    (hTL : T ≤ L) (hBL : B ≤ L) (hB : B ∈ lFamily T) :
    B.subgroupOf L ∈ lFamily (T.subgroupOf L) := by
  show B.subgroupOf L ∈ cComp (B.subgroupOf L ⊔ T.subgroupOf L)
  rw [← Subgroup.subgroupOf_sup hBL hTL]
  exact A312.mem_cComp_subgroupOf (sup_le hBL hTL) hB

theorem mathieu_m22
    {G : Type} [Group G] [Finite G] {L T B : Subgroup G}
    (hT : IsSylowTwoOf T L) (hB : B ∈ lFamily T) (hBL : B ≤ L) (hL : IsSporadic .M22 ↥L)
    (hext : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) :
    IsShort2 B ∧ IsLin2Type B 2 := by
  obtain ⟨φ⟩ := hL
  have hc : Nat.card (B.subgroupOf L) = 960 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv]
    exact card_of_isExt_e16_a5 hext
  obtain ⟨θ⟩ := m22_block_equiv_of φ (isSylowTwoOf_top_subgroupOf hT)
    (subgroupOf_mem_lFamily' hT.1 hBL hB) hc
  exact isShort2_isLin2Type_of_mulEquiv (θ.trans (Subgroup.subgroupOfEquivOfLe hBL))

theorem mathieu_hatM22
    {G : Type} [Group G] [Finite G] {L T B : Subgroup G}
    (hT : IsSylowTwoOf T L) (hB : B ∈ lFamily T) (hBL : B ≤ L)
    (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    (hext : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) :
    IsShort2 B ∧ IsLin2Type B 2 := by
  have hc := card_of_isExt_e16_a5 hext
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    Finite.of_equiv _ m22EquivMgrp.symm.toEquiv
  obtain ⟨-, hZ3, ⟨e⟩⟩ := hL
  let π : ↥L →* CFSG.Blueprint.NativeSporadic.Carrier .M22 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [e.map_eq_one_iff, QuotientGroup.eq_one_iff]
  obtain ⟨V, hVn, ⟨eV⟩, ⟨eA⟩⟩ := hext
  have hVc : Nat.card V = 16 := by
    rw [Nat.card_congr (eV.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
    norm_num
  set B₁ := B.subgroupOf L with hB₁e
  have hinf : B₁ ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxk⟩
    rw [hker] at hxk
    have h3 : orderOf x ∣ 3 := by
      have h1 := orderOf_dvd_natCard (⟨x, hxk⟩ : ↥(Subgroup.center ↥L))
      rw [hZ3, ← Subgroup.orderOf_coe] at h1
      exact h1
    set y : ↥B := ⟨(x : G), Subgroup.mem_subgroupOf.mp hxB⟩ with hy
    have hyc : y ∈ Subgroup.center ↥B := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hxk ⟨(b : G), hBL b.2⟩)
      exact h2
    have hyV : y ∈ V := by
      have hq : (QuotientGroup.mk y : ↥B ⧸ V) ∈ Subgroup.center (↥B ⧸ V) := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hyc b]
      have h1 : eA (QuotientGroup.mk y) ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [Subgroup.mem_center_iff]
        intro a
        obtain ⟨q, rfl⟩ := eA.surjective a
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hq q]
      rw [Vol2.Ch10.SecB.C10KH.center_alt5, Subgroup.mem_bot, map_eq_one_iff _ eA.injective,
        QuotientGroup.eq_one_iff] at h1
      exact h1
    have h16 : orderOf y ∣ 16 := by
      have h1 := orderOf_dvd_natCard (⟨y, hyV⟩ : ↥V)
      rw [hVc, ← Subgroup.orderOf_coe] at h1
      exact h1
    have hoy : orderOf y = orderOf x := by
      rw [← Subgroup.orderOf_coe y, ← Subgroup.orderOf_coe x]
    have h1 : orderOf x = 1 := by
      rw [← hoy] at h3
      have h4 := Nat.dvd_gcd h16 h3
      rw [show Nat.gcd 16 3 = 1 by norm_num, Nat.dvd_one] at h4
      rw [← hoy]
      exact h4
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.mp h1
  have hB₁ : B₁ ∈ lFamily (T.subgroupOf L) := subgroupOf_mem_lFamily' hT.1 hBL hB
  have hB' : B₁.map π ∈ lFamily ((T.subgroupOf L).map π) :=
    A38c14.map_mem_lFamily π (hker ▸ le_refl _) hB₁
  have hT' : IsSylowTwoOf ((T.subgroupOf L).map π) ⊤ :=
    A312.isSylowTwoOf_top_map π hπ (isSylowTwoOf_top_subgroupOf hT)
  have hc' : Nat.card (B₁.map π) = 960 := by
    rw [← A38c14.card_eq_of_inf_ker_eq_bot π hinf, hB₁e,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hc]
  obtain ⟨θ⟩ := m22_block_equiv_of (MulEquiv.refl _) hT' hB' hc'
  exact isShort2_isLin2Type_of_mulEquiv ((θ.trans (A38c14.mapEquivOfInfKerEqBot π hinf).symm).trans
    (Subgroup.subgroupOfEquivOfLe hBL))

end CFSG.Quasithin.H13.NQCat.A314D
