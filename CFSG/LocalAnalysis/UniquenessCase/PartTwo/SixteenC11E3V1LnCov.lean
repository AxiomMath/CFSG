module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardRes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Ctx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


private theorem s1611e3_realizes_of_resHom_map {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U : Subgroup V} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    (hinj : Function.Injective (CFSG.Quasithin.H13.VolI.resHom L U hU)) {D : FFModel}
    {W : Subgroup ↥U} (h : D.Realizes (CFSG.Quasithin.H13.VolI.resHom L U hU).range ⊤ W) :
    D.Realizes L U (W.map U.subtype) := by
  obtain ⟨π, hπs, hZU, hkerle, hHU, hHZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  let f := CFSG.Quasithin.H13.VolI.resHom L U hU
  let ε : ↥L ≃* ↥f.range := MonoidHom.ofInjective hinj
  let π' : D.Gam →* ↥L := ε.symm.toMonoidHom.comp π
  let topIncl : ↥U →* ↥(⊤ : Subgroup ↥U) :=
    { toFun := fun u => ⟨u, Subgroup.mem_top u⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let β' : ↥U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec := β.comp topIncl
  have hcoe : ∀ (γ : D.Gam) (u : ↥U),
      ((π' γ : ↥L) : MulAut V) (u : V) =
        (((π γ : ↥f.range) : MulAut ↥U) u : V) := by
    intro γ u
    have h1 : f (π' γ) = (π γ : MulAut ↥U) :=
      congrArg Subtype.val (MulEquiv.apply_symm_apply ε (π γ))
    calc ((π' γ : ↥L) : MulAut V) (u : V)
        = (f (π' γ) u : V) := (CFSG.Quasithin.H13.VolI.coe_resHom_apply L U hU (π' γ) u).symm
      _ = (((π γ : ↥f.range) : MulAut ↥U) u : V) := by rw [h1]
  have htop : Function.Surjective topIncl := fun v => ⟨(v : ↥U), Subtype.ext rfl⟩
  refine ⟨π', ?_, ?_, hkerle, fun l u hu => hU l l.2 u hu, ?_, hsec, hkerinv,
    β', ?_, ?_, ?_⟩
  · intro l
    obtain ⟨γ, hγ⟩ := hπs (ε l)
    refine ⟨γ, ?_⟩
    show ε.symm (π γ) = l
    rw [hγ, MulEquiv.symm_apply_apply]
  · intro x hx
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact u.2
  · intro l z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr
      ⟨f l u, hHZ ⟨f l, MonoidHom.mem_range.mpr ⟨l, rfl⟩⟩ u hu, ?_⟩
    exact CFSG.Quasithin.H13.VolI.coe_resHom_apply L U hU l u
  · exact hβs.comp htop
  · intro u
    have h := hβk (topIncl u)
    change β (topIncl u) = 1 ↔ (u : ↥U) ∈ W at h
    change β (topIncl u) = 1 ↔ (u : V) ∈ W.map U.subtype
    rw [h]
    constructor
    · intro hu
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    · intro hu
      obtain ⟨u', hu', heq⟩ := Subgroup.mem_map.mp hu
      have : u' = u := Subtype.ext heq
      rwa [← this]
  · intro γ u m hu hm hum
    let u' : ↥(⊤ : Subgroup ↥U) := topIncl u
    have hcoe' : (u' : ↥U) = u := rfl
    have hhu' : ((π γ : ↥f.range) : MulAut ↥U) (u' : ↥U) ∈ (⊤ : Subgroup ↥U) :=
      Subgroup.mem_top _
    have hhum : β u' = QuotientGroup.mk m := by simpa [β', u'] using hum
    have hkey := hβe γ u' m hhu' hm hhum
    have hx : ((π' γ : ↥L) : MulAut V) (u : V) =
        (((π γ : ↥f.range) : MulAut ↥U) (u' : ↥U) : V) := by
      rw [hcoe γ u, ← hcoe']
    have hsub : topIncl ⟨((π' γ : ↥L) : MulAut V) (u : V), hu⟩ =
        ⟨((π γ : ↥f.range) : MulAut ↥U) (u' : ↥U), hhu'⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      exact hx
    simp only [β', MonoidHom.comp_apply]
    rw [hsub]
    exact hkey

theorem s1611e3_v1_ln3_cover {D : Data G} (h : S1611e3Std D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsLn ↥L₀ 3 1) (hL : IsLn ↥(lBar ⊥ V hV L) 3 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    ∃ Z : Subgroup (Vtil ⊥ V hV), BinaryNaturalSL L₀ J₀ Z 3 1 ∧ Z ≤ fixV L₀ ∧ Z ≠ ⊥ ∧
      commSub J₀ L₀ = J₀ ∧ ∀ x ∈ L₀, ∀ y ∈ J₀, x y ∈ J₀ := by
  classical
  have hin : In10 D := h.in10 hc.setting.hyp16.hyp125
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h.h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by rw [htop]; exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => BinaryNaturalSL H U Z 3 1) :=
    s16e_two_fam_ln D hV (le_refl 3) hL hsum'
  obtain ⟨φ, hφcoe, hcommφ, hfixφ, D', hQD', hRD'⟩ :=
    s16c11_v1_hard_nat_section D hin h.h1217 hc hs hF
      (Q := fun D' => ∃ (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = 2 ∧ D' = FFModel.nat (StatedSL 3 K))
      (by
        intro H U Z hBU
        obtain ⟨K, hKfield, hKfin, hKcard, hR⟩ := hBU
        exact ⟨FFModel.nat (StatedSL 3 K),
          ⟨K, hKfield, hKfin, by simpa using hKcard, rfl⟩, hR⟩)
      hV1 hM
  obtain ⟨K, hKfield, hKfin, hKcard, rfl⟩ := hQD'
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := s16e_two_lBar_le D hc.setting.hyp151 hV
  have hZcenter : ∀ k ∈ kBar D.M ⊥ V hV L,
      (∀ k' ∈ kBar D.M ⊥ V hV L, k * k' = k' * k) → k = 1 := by
    intro k hk hkc
    have h1 : (⟨k, hk⟩ : ↥(kBar D.M ⊥ V hV L)) = 1 :=
      s16c167_center_of_isSym_three hK ⟨k, hk⟩
        (fun y => Subtype.ext (hkc (y : MulAut (Vtil ⊥ V hV)) y.2).symm)
    exact congrArg Subtype.val h1
  have hle : lBar ⊥ V hV L ≤ L₀ := by
    refine s16c1614_le_right_of_centralizes hdir hLM ?_ hZcenter
    intro n hn k hk
    exact (Subgroup.mem_centralizer_iff.1 hk.2) n hn
  have hcardL : Nat.card ↥(lBar ⊥ V hV L) = Nat.card ↥L₀ := by
    rw [CFSG.Blueprint.LieModel.card_psl_three_two hL,
      CFSG.Blueprint.LieModel.card_psl_three_two hL₀]
  have heqL : lBar ⊥ V hV L = L₀ := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardL.symm)
  have hL₀Mbar : L₀ ≤ Mbar D.M ⊥ V hV := hdir.2.2 ▸ le_sup_right
  have hL₀K : ∀ l ∈ L₀, ∀ k ∈ kBar D.M ⊥ V hV L, l * k = k * l := by
    intro l hl k hk
    exact (s16c11_comm_of_isInternalDirect hdir k hk l hl).symm
  have hJ : ∀ l ∈ L₀, ∀ j ∈ J₀, l j ∈ J₀ := by
    intro l hl j hj
    exact s16c11_mem_of_model (s15_Infra_vtil_sq_eq_one ⊥ V hV) hM (hL₀Mbar hl) (hL₀K l hl) hj
  have hJ' : ∀ l ∈ lBar ⊥ V hV L, ∀ j ∈ J₀, l j ∈ J₀ := fun l hl => hJ l (hle hl)
  have hLK : ∀ l ∈ lBar ⊥ V hV L, ∀ k ∈ kBar D.M ⊥ V hV L, l * k = k * l := by
    intro l hl k hk
    exact (s16c11_comm_of_isInternalDirect hdir k hk l (hle hl)).symm
  have hinj' : Function.Injective
      (CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ') :=
    s16c11_v1_resHom_injective hM hLM hLK hJ'
  have hinj₀ : Function.Injective (CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ) :=
    s16c11_v1_resHom_injective hM hL₀Mbar hL₀K hJ
  have hφeq : φ = CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ' := by
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro j
    apply Subtype.ext
    rw [hφcoe x j, CFSG.Quasithin.H13.VolI.coe_resHom_apply]
  have hφinj : Function.Injective φ := by rw [hφeq]; exact hinj'
  have hφrange : φ.range = (CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ).range := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, rfl⟩
      refine MonoidHom.mem_range.mpr ⟨⟨x, hle x.2⟩, ?_⟩
      apply MulEquiv.ext
      intro j
      apply Subtype.ext
      rw [hφcoe x j, CFSG.Quasithin.H13.VolI.coe_resHom_apply]
    · have h1 : Nat.card ↥(CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ).range =
          Nat.card ↥L₀ := (Nat.card_congr (MonoidHom.ofInjective hinj₀).toEquiv).symm
      have h2 : Nat.card ↥φ.range = Nat.card ↥(lBar ⊥ V hV L) :=
        (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
      rw [h1, h2, hcardL]
  have hRD'' : (FFModel.nat (StatedSL 3 K)).Realizes
      (CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ).range ⊤
      (fixV (CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ).range) := by
    rw [hφrange] at hRD'
    exact hRD'
  let Z : Subgroup (Vtil ⊥ V hV) := (fixV φ.range).map J₀.subtype
  have hZeq : Z = (fixV (CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ).range).map J₀.subtype := by
    change (fixV φ.range).map J₀.subtype = _
    rw [hφrange]
  have hreal : (FFModel.nat (StatedSL 3 K)).Realizes L₀ J₀ Z := by
    rw [hZeq]
    exact s1611e3_realizes_of_resHom_map hJ hinj₀ hRD''
  refine ⟨Z, ?_, ?_, ?_, ?_, hJ⟩
  · exact ⟨K, hKfield, hKfin, by simpa using hKcard, hreal⟩
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    rw [mem_fixV] at hu ⊢
    intro l hl
    have h1 : ((CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ ⟨l, hl⟩) u : Vtil ⊥ V hV) =
        (u : Vtil ⊥ V hV) :=
      congrArg Subtype.val
        (hu _ (by rw [hφrange]; exact MonoidHom.mem_range.mpr ⟨⟨l, hl⟩, rfl⟩))
    rwa [CFSG.Quasithin.H13.VolI.coe_resHom_apply] at h1
  · intro hbot
    have h1 : fixV φ.range ≤ ⊥ := by
      intro u hu
      have h2 : J₀.subtype u ∈ Z := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h2
      rw [Subgroup.mem_bot]
      exact J₀.subtype_injective (by rw [h2, map_one])
    exact hfixφ (le_bot_iff.mp h1)
  · have hmapcomm : (commV φ.range).map J₀.subtype = commSub J₀ L₀ := by
      apply le_antisymm
      · rw [Subgroup.map_le_iff_le_comap]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨g, hg, u, rfl⟩
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
        change J₀.subtype ((φ x : MulAut ↥J₀) u * u⁻¹) ∈ commSub J₀ L₀
        rw [map_mul, map_inv]
        refine Subgroup.subset_closure
          ⟨(x : MulAut (Vtil ⊥ V hV)), hle x.2, (u : Vtil ⊥ V hV), u.2, ?_⟩
        rw [show J₀.subtype ((φ x : MulAut ↥J₀) u) =
            (x : MulAut (Vtil ⊥ V hV)) (u : Vtil ⊥ V hV) from hφcoe x u]
        simp only [Subgroup.subtype_apply]
      · rw [commSub, Subgroup.closure_le]
        rintro _ ⟨l, hl, j, hj, rfl⟩
        refine Subgroup.mem_map.mpr
          ⟨CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ ⟨l, hl⟩ ⟨j, hj⟩ * ⟨j, hj⟩⁻¹, ?_, ?_⟩
        · exact Subgroup.subset_closure
            ⟨CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ ⟨l, hl⟩,
              by rw [hφrange]
                 exact MonoidHom.mem_range.mpr ⟨⟨l, hl⟩, rfl⟩, ⟨j, hj⟩, rfl⟩
        · rw [map_mul, map_inv]
          rw [show J₀.subtype
              ((CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ ⟨l, hl⟩) ⟨j, hj⟩) =
            (l : MulAut (Vtil ⊥ V hV)) (j : Vtil ⊥ V hV)
            from CFSG.Quasithin.H13.VolI.coe_resHom_apply L₀ J₀ hJ ⟨l, hl⟩ ⟨j, hj⟩]
          simp only [Subgroup.subtype_apply]
    have htopJ : (⊤ : Subgroup ↥J₀).map J₀.subtype = J₀ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hmapcomm, hcommφ, htopJ]

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
