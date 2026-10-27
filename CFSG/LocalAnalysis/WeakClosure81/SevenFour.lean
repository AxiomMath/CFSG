module

public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem centralizer_iSub_le_normalizer {V H E U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hU : U ∈ omegaSet V H E) :
    kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) ≤
      Subgroup.normalizer (U : Set G) := by
  intro c hc
  obtain ⟨-, hcC⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨g, hUg, -, -⟩ := mem_omegaSet.mp hU
  have hne : U ⊓ iSub V H E ≠ ⊥ := by
    rw [inf_iSub_eq_inf_pCoreOf hU]
    exact inf_pCoreOf_ne_bot_of_mem_omegaSet hV hE hEH hEnorm hU
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hxU : (x : G) ∈ U := (Subgroup.mem_inf.mp x.2).1
  have hxI : (x : G) ∈ iSub V H E := (Subgroup.mem_inf.mp x.2).2
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxC : c ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp hcC (x : G) hxI
  have hxV : (x : G) ∈ conjSubgroup V g := hUg ▸ hxU
  have hcN : c ∈ Subgroup.normalizer (conjSubgroup V g : Set G) :=
    centralizer_le_normalizer_conj hTI g hxV hx1' hxC
  rw [hUg]
  exact hcN

theorem inf_centralizer_iSub_subgroupOf_normal {V H E : Subgroup G}
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) :
    ((kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G)).subgroupOf
      (kSub V H E)).Normal := by
  have hIH : iSub V H E ≤ H :=
    iSup_le fun _ => iSup_le fun _ =>
      inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  have hK_N_I : kSub V H E ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    hKleH.trans (le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal hEH hEnorm))
  rw [Subgroup.normal_subgroupOf_iff inf_le_left]
  intro c k hc hk
  obtain ⟨hcK, hcC⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (kSub V H E).mul_mem ((kSub V H E).mul_mem hk hcK) ((kSub V H E).inv_mem hk)
  · rw [Subgroup.mem_centralizer_iff] at hcC ⊢
    intro i hi
    have hi' : k⁻¹ * i * k ∈ iSub V H E := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (hK_N_I ((kSub V H E).inv_mem hk)) i).mp hi
    have h := hcC (k⁻¹ * i * k) hi'
    calc i * (k * c * k⁻¹) = k * ((k⁻¹ * i * k) * c) * k⁻¹ := by group
      _ = k * (c * (k⁻¹ * i * k)) * k⁻¹ := by rw [h]
      _ = (k * c * k⁻¹) * i := by group

theorem inf_centralizer_iSub_eq_inf_iSub {V H E U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hU : U ∈ omegaSet V H E) :
    U ⊓ Subgroup.centralizer (iSub V H E : Set G) = U ⊓ iSub V H E := by
  have hI : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond hV hTI hE hOmH
  refine le_antisymm ?_ ?_
  · intro a ha
    obtain ⟨haU, haC⟩ := Subgroup.mem_inf.mp ha
    by_contra haI
    have haO : a ∉ pCoreOf 2 H := fun haO =>
      haI ⟨haU, inf_pCoreOf_le_iSub hU ⟨haU, haO⟩⟩
    have haOK : a ∉ pCoreOf 2 (kSub V H E) := fun h =>
      haO (pCoreOf_kSub_le_pCoreOf hEH hEnorm hOmH h)
    have haK : a ∈ kSub V H E := le_kSub hU haU
    obtain ⟨k, hkK, hknot⟩ : ∃ k ∈ kSub V H E,
        ¬ IsPGroup 2 (Subgroup.closure ({a, k⁻¹ * a * k} : Set G)) := by
      by_contra h
      push Not at h
      exact haOK (mem_pCoreOf_of_forall_closure_isPGroup haK fun g hg => by
        have h' := h g⁻¹ ((kSub V H E).inv_mem hg)
        rwa [inv_inv] at h')
    have hkH : k ∈ H := kSub_le_of_forall_le hOmH hkK
    have hU' : conjSubgroup U k ∈ omegaSet V H E :=
      conjSubgroup_mem_omegaSet hEH hEnorm hU hkH
    have ha'U' : k⁻¹ * a * k ∈ conjSubgroup U k := by
      rw [mem_conjSubgroup_iff]
      rw [show k * (k⁻¹ * a * k) * k⁻¹ = a by group]
      exact haU
    have hU2 : IsPGroup 2 U :=
      CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
        (isElemAbelian_of_mem_omegaSet hV hU)
    have hU'2 : IsPGroup 2 (conjSubgroup U k) :=
      hU2.map (MulAut.conj k⁻¹).toMonoidHom
    have ha2 : a * a = 1 := by
      have := (isElemAbelian_of_mem_omegaSet hV hU).2 a haU
      simpa [pow_two] using this
    have hUne : conjSubgroup U k ≠ U := by
      intro heq
      apply hknot
      refine hU2.to_le ((Subgroup.closure_le U).mpr ?_)
      rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact haU
      · rw [← heq]; exact ha'U'
    have haU'notN : a ∉ nVSub U k := by
      intro haN
      have hzp : Subgroup.zpowers a ≤
          Subgroup.normalizer (conjSubgroup U k : Set G) :=
        Subgroup.zpowers_le.mpr haN.2
      have hz2 : IsPGroup 2 (Subgroup.zpowers a) := by
        apply IsPGroup.of_card_dvd_pow (n := 1)
        rw [Nat.card_zpowers, pow_one]
        exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
      have hsup2 : IsPGroup 2 (conjSubgroup U k ⊔ Subgroup.zpowers a : Subgroup G) :=
        hU'2.to_sup_of_normal_left' hz2 hzp
      have hcle : Subgroup.closure ({a, k⁻¹ * a * k} : Set G) ≤
          conjSubgroup U k ⊔ Subgroup.zpowers a :=
        (Subgroup.closure_le _).mpr (by
          rintro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with hx | hx
          · rw [hx]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
          · rw [hx]; exact Subgroup.mem_sup_left ha'U')
      exact hknot (hsup2.to_le hcle)
    have hTIU : IsTI U := by
      obtain ⟨g, hUg, -, -⟩ := mem_omegaSet.mp hU
      rw [hUg]
      exact isTI_conj hTI g
    have hbSub_bot : bSub U k ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ :=
      bSub_inf_centralizer_eq_bot hTIU hUne haU haU'notN
    have hne' : conjSubgroup U k ⊓ pCoreOf 2 H ≠ ⊥ :=
      inf_pCoreOf_ne_bot_of_mem_omegaSet hV hE hEH hEnorm hU'
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
    have hyU' : (y : G) ∈ conjSubgroup U k := (Subgroup.mem_inf.mp y.2).1
    have hyO : (y : G) ∈ pCoreOf 2 H := (Subgroup.mem_inf.mp y.2).2
    have hyI : (y : G) ∈ iSub V H E := inf_pCoreOf_le_iSub hU' ⟨hyU', hyO⟩
    have hy1' : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hyN : (y : G) ∈ Subgroup.normalizer (U : Set G) :=
      (sevenOneCore_holds hV hTI hE (conjSubgroup U k) hU' U hU
        (inf_pCoreOf_le_inf_pCoreOf_sup hOmH hU' hU ⟨hyU', hyO⟩)).2
    have hybSub : (y : G) ∈ bSub U k := Subgroup.mem_inf.mpr ⟨hyU', hyN⟩
    have hyC : (y : G) ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp haC (y : G) hyI).symm
    have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbSub_bot]
      exact ⟨hybSub, hyC⟩
    exact hy1' (Subgroup.mem_bot.mp hybot)
  · refine inf_le_inf le_rfl ?_
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hI.1

theorem commutator_centralizer_iSub_kSub_le {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) :
    ⁅kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G), kSub V H E⁆ ≤
      iSub V H E := by
  set C : Subgroup G := kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) with hCdef
  have hCK : C ≤ kSub V H E := by rw [hCdef]; exact inf_le_left
  have hC_le_CGI : C ≤ Subgroup.centralizer (iSub V H E : Set G) := by
    rw [hCdef]; exact inf_le_right
  have hC_normal : (C.subgroupOf (kSub V H E)).Normal :=
    inf_centralizer_iSub_subgroupOf_normal hEH hEnorm hOmH
  have hK_N_C : kSub V H E ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_of_subgroupOf_normal hCK hC_normal
  have hCK_le_C : ⁅C, kSub V H E⁆ ≤ C :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hK_N_C
  have hIH : iSub V H E ≤ H :=
    (iSup_le fun _ => iSup_le fun _ =>
      inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
  have hK_N_I : kSub V H E ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    (kSub_le_of_forall_le hOmH).trans
      (le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal hEH hEnorm))
  have hK_eq : kSub V H E =
      ⨆ U : {U : Subgroup G // U ∈ omegaSet V H E}, (U.1 : Subgroup G) := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun U => iSup_le fun hU =>
        le_iSup_of_le (⟨U, hU⟩ : {U // U ∈ omegaSet V H E}) le_rfl
    · refine iSup_le fun U => le_iSup₂_of_le U.1 U.2 le_rfl
  rw [Subgroup.commutator_le]
  intro c hc k hk
  rw [hK_eq] at hk
  exact Subgroup.iSup_induction'
    (S := fun U : {U // U ∈ omegaSet V H E} => (U.1 : Subgroup G))
    (C := fun x _ => ⁅c, x⁆ ∈ iSub V H E)
    (fun U u hu => by
      have hCU_le_U : ⁅C, U.1⁆ ≤ U.1 :=
        Subgroup.le_normalizer_iff_commutator_le_right.mp
          (centralizer_iSub_le_normalizer hV hTI hE hEH hEnorm hOmH U.2)
      have hU_mem : ⁅c, u⁆ ∈ U.1 := hCU_le_U (Subgroup.commutator_mem_commutator hc hu)
      have hmemC : ⁅c, u⁆ ∈ C :=
        hCK_le_C (Subgroup.commutator_mem_commutator hc (le_kSub U.2 hu))
      have hCGI : ⁅c, u⁆ ∈ Subgroup.centralizer (iSub V H E : Set G) := hC_le_CGI hmemC
      have hmem : ⁅c, u⁆ ∈ U.1 ⊓ Subgroup.centralizer (iSub V H E : Set G) :=
        ⟨hU_mem, hCGI⟩
      rw [inf_centralizer_iSub_eq_inf_iSub hV hTI hE hEH hEnorm hOmH U.2] at hmem
      exact hmem.2)
    (by simp)
    (fun x y hx hy ihx ihy => by
      have hxK : x ∈ kSub V H E := by rwa [hK_eq]
      have hmem : x * ⁅c, y⁆ * x⁻¹ ∈ iSub V H E :=
        (Subgroup.mem_normalizer_iff.mp (hK_N_I hxK) ⁅c, y⁆).mp ihy
      rw [commutatorElement_mul_right_eq_mul_conj]
      rw [show ⁅c, x⁆ * x * ⁅c, y⁆ * x⁻¹ = ⁅c, x⁆ * (x * ⁅c, y⁆ * x⁻¹) by group]
      exact (iSub V H E).mul_mem ihx hmem)
    hk

theorem isNilpotent_kSub_inf_centralizer_iSub {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) :
    Group.IsNilpotent ↥(kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G)) := by
  set C : Subgroup G := kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) with hCdef
  refine Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot (n := 2) ?_
  have hCK_le_I := commutator_centralizer_iSub_kSub_le hV hTI hE hEH hEnorm hOmH
  have hCK : C ≤ kSub V H E := by rw [hCdef]; exact inf_le_left
  have hCC_le_I : ⁅C, C⁆ ≤ iSub V H E :=
    (Subgroup.commutator_mono le_rfl hCK).trans hCK_le_I
  have hIC_bot : ⁅iSub V H E, C⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp (inf_le_right : C ≤ _)
  change ⁅⁅C, C⁆, C⁆ = ⊥
  exact le_bot_iff.mp ((Subgroup.commutator_mono hCC_le_I le_rfl).trans (le_of_eq hIC_bot))

theorem seven_four {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) :
    kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) ≤
      pCoreOf 2 (kSub V H E) ⊔ CFSG.QuasithinUnique.oddCoreIn (kSub V H E) := by
  set C : Subgroup G := kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) with hCdef
  have hCnil : Group.IsNilpotent ↥C :=
    isNilpotent_kSub_inf_centralizer_iSub hV hTI hE hEH hEnorm hOmH
  have hdecomp : (⊤ : Subgroup ↥C) ≤
      CFSG.pCore 2 ↥C ⊔ CFSG.pPrimeCore 2 ↥C :=
    CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥C) (p := 2) hCnil
  have hmap : C ≤
      (CFSG.pCore 2 ↥C).map C.subtype ⊔ (CFSG.pPrimeCore 2 ↥C).map C.subtype := by
    have h := Subgroup.map_mono (f := C.subtype) hdecomp
    rwa [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hCK : C ≤ kSub V H E := by rw [hCdef]; exact inf_le_left
  have hK_N_C : kSub V H E ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_of_subgroupOf_normal hCK
      (inf_centralizer_iSub_subgroupOf_normal hEH hEnorm hOmH)
  have hchar : Subgroup.normalizer (C : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 C : Set G) := by
    haveI : (CFSG.pCore 2 ↥C).Characteristic :=
      CFSG.LieType.BorelTits.pCore_characteristic 2
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 ↥C)
  refine hmap.trans (sup_le_sup ?_ ?_)
  · rw [← CFSG.openPCoreOf_eq_map_pCore 2 C]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 C).trans hCK)
      (hK_N_C.trans hchar)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C)
  · haveI : (CFSG.pPrimeCore 2 ↥C).Characteristic := CFSG.pPrimeCore_characteristic
    have hcharP : Subgroup.normalizer (C : Set G) ≤
        Subgroup.normalizer ((CFSG.pPrimeCore 2 ↥C).map C.subtype : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pPrimeCore 2 ↥C)
    have hPnorm : (((CFSG.pPrimeCore 2 ↥C).map C.subtype).subgroupOf
        (kSub V H E)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        ((Subgroup.map_subtype_le (CFSG.pPrimeCore 2 ↥C)).trans hCK)).mpr
        (hK_N_C.trans hcharP)
    have hPodd : Odd (Nat.card (((CFSG.pPrimeCore 2 ↥C).map C.subtype).subgroupOf
        (kSub V H E))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          ((Subgroup.map_subtype_le (CFSG.pPrimeCore 2 ↥C)).trans hCK)).toEquiv,
        Subgroup.card_map_of_injective C.subtype_injective]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥C))
    have hle : (((CFSG.pPrimeCore 2 ↥C).map C.subtype).subgroupOf (kSub V H E)) ≤
        fusionOddCore (kSub V H E) := le_sSup ⟨hPnorm, hPodd⟩
    have hmapP := Subgroup.map_mono (f := (kSub V H E).subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le
      ((Subgroup.map_subtype_le (CFSG.pPrimeCore 2 ↥C)).trans hCK)] at hmapP
    exact hmapP

end CFSG.LocalAnalysis.WeakClosure81
