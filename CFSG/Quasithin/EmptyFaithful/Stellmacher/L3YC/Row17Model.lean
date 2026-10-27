module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row17Comp
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row17Basic

public section

namespace CFSG.Quasithin.Stellmacher.L3YC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam

theorem card_eq_of_modO2_psl32 {Γ : Type} [Group Γ] [Finite Γ] {B : Subgroup Γ}
    (h : IsPSL 3 2 1 (ModO2 B)) : ∃ a : ℕ, Nat.card ↥B = 2 ^ a * 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := ↥B) (p := 2)).exists_card_eq
  refine ⟨a, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), ha,
    CFSG.Quasithin.SBc11.card_of_isPSL_three_two h, mul_comm]

section Overgroups


theorem row17_overgroups [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup J} (hperf : ⁅B, B⁆ = B)
    (hN : P0 ≤ Subgroup.normalizer (B : Set J)) (hPSL : IsPSL 3 2 1 (ModO2 B)) :
    B ⊔ P0 ≤ Hj ∨ B ⊔ P0 ≤ Subgroup.normalizer (V0 : Set J) := by
  have hF : J4Facts := j4Facts
  have hs : IsSimpleGroup (ModO2 B) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hPSL).2
  have hBc : B ∈ cComp (B ⊔ P0) :=
    mem_cComp_of_modO2_simple le_sup_left
      (Stellmacher.PU.L3YC.M24.normal_subgroupOf_sup hN) hperf hs
  have hB : B ∈ lFamily P0 := hBc
  obtain ⟨a, ha⟩ := card_eq_of_modO2_psl32 hPSL
  obtain ⟨t, ht⟩ := Stellmacher.PU.L3YC.M24.card_sup_eq_two_pow (isSylowTwoOf_P0).2.1 hN
  have hY : Nat.card ↥(B ⊔ P0) = 2 ^ (a + t) * 168 := by
    rw [ht, ha, pow_add]; ring
  have hsupne : B ⊔ P0 ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, card_J hF] at hY
    have h5 : (5 : ℕ) ∣ 2 ^ (a + t) * 168 := by
      rw [← hY]; norm_num
    have h5' : (5 : ℕ) ∣ 2 ^ (a + t) := (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h5)
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5')
    omega
  have hns := A312S.not_isSolvable_sup hB
  rcases CFSG.Quasithin.J4Ov.j4OvergroupLocal_holds (B ⊔ P0) le_sup_right hsupne hns with h | h | h
  · exact Or.inl h
  · rcases J4M2.J4M2Lattice hF (le_sup_right : P0 ≤ B ⊔ P0) h with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exfalso
      have h11 : (11 : ℕ) ∣ Nat.card ↥(B ⊔ P0) := by
        rw [h', CFSG.Quasithin.J4M2.card_M2_two_part hF]; norm_num
      rw [hY] at h11
      have h11' : (11 : ℕ) ∣ 2 ^ (a + t) := (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h11)
      have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h11')
      omega
  · exact Or.inr h

end Overgroups

theorem card_isHat_alt6 {S : Type} [Group S] (h : IsHat S (alternatingGroup (Fin 6))) :
    Nat.card S = 1080 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [(Subgroup.center S).card_eq_card_quotient_mul_card_subgroup, h3, Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

section HjPart

open CFSG.Quasithin.A312M24


theorem mem_normalizer_of_map_mem {B : Subgroup J} (hperf : ⁅B, B⁆ = B) (hBle : B ≤ Hj)
    (hEB : Eg uJ 11 ≤ Subgroup.normalizer (B : Set J)) {ω₁ : ↥Hj}
    (hω : fHj ω₁ ∈ Subgroup.normalizer
      (((fHj.comp (Subgroup.inclusion hBle)).range : Subgroup G24) : Set G24)) :
    (ω₁ : J) ∈ Subgroup.normalizer (B : Set J) := by
  have hM := j4Facts.mat
  set θ : ↥B →* G24 := fHj.comp (Subgroup.inclusion hBle) with hθ
  set X' : Subgroup ↥Hj := θ.range.comap fHj with hX'
  have h1 : ω₁ ∈ Subgroup.normalizer (X' : Set ↥Hj) := Subgroup.le_normalizer_comap fHj hω
  set XJ' : Subgroup J := X'.map Hj.subtype with hXJ'
  have h2 : (ω₁ : J) ∈ Subgroup.normalizer (XJ' : Set J) :=
    Subgroup.le_normalizer_map Hj.subtype ⟨ω₁, h1, rfl⟩
  have hXeq : XJ' = B ⊔ Eg uJ 11 := by
    apply le_antisymm
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨b, hb⟩ : fHj h ∈ θ.range := hh
      have hker : fHj ((Subgroup.inclusion hBle b)⁻¹ * h) = 1 := by
        rw [map_mul, map_inv]
        have : fHj (Subgroup.inclusion hBle b) = fHj h := hb
        rw [this, inv_mul_cancel]
      have hE : ((Subgroup.inclusion hBle b)⁻¹ * h : ↥Hj) ∈ fHj.ker := hker
      rw [ker_fHj, Subgroup.mem_subgroupOf] at hE
      have hh' : (h : J) = (b : J) * (((b : J))⁻¹ * (h : J)) := by group
      rw [show (Hj.subtype h) = (h : J) from rfl, hh']
      exact Subgroup.mul_mem_sup b.2 hE
    · refine sup_le ?_ ?_
      · intro b hb
        exact ⟨⟨b, hBle hb⟩, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      · intro e he
        refine ⟨⟨e, Eg_le_Hj he⟩, ?_, rfl⟩
        show fHj ⟨e, Eg_le_Hj he⟩ ∈ θ.range
        have : fHj ⟨e, Eg_le_Hj he⟩ = 1 := by
          have : (⟨e, Eg_le_Hj he⟩ : ↥Hj) ∈ fHj.ker := by
            rw [ker_fHj, Subgroup.mem_subgroupOf]; exact he
          exact this
        rw [this]; exact Subgroup.one_mem _
  have hBN : (B.subgroupOf (B ⊔ Eg uJ 11)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le (fun x hx => Subgroup.le_normalizer hx) hEB)
  have hEsolv : Group.IsSolvable ↥(Eg uJ 11) :=
    (@IsNilpotent.to_isSolvable _ _ (isPGroup_Eg (elem_uJ hM)).isNilpotent)
  have hcore : perfectCore (B ⊔ Eg uJ 11) = B := by
    apply le_antisymm
    · exact perfectCore_le_of_sup_solvable le_sup_left hBN rfl hEsolv
    · exact le_perfectCore_of_perfect le_sup_left hperf
  have h3 := normalizer_le_normalizer_perfectCore (B ⊔ Eg uJ 11)
  rw [hXeq] at h2
  have := h3 h2
  rwa [hcore] at this

theorem isPGroup_ker_theta {B : Subgroup J} (hBle : B ≤ Hj) :
    IsPGroup 2 (fHj.comp (Subgroup.inclusion hBle)).ker := by
  intro x
  have hx : fHj (Subgroup.inclusion hBle x.1) = 1 := x.2
  have hxk : Subgroup.inclusion hBle x.1 ∈ fHj.ker := hx
  obtain ⟨k, hk⟩ := isPGroup_ker_fHj (⟨_, hxk⟩ : fHj.ker)
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun y : fHj.ker => ((y : ↥Hj) : J)) hk
  simpa using this


theorem row17_hj [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup J} (hperf : ⁅B, B⁆ = B)
    (hN : P0 ≤ Subgroup.normalizer (B : Set J)) (hPSL : IsPSL 3 2 1 (ModO2 B))
    (hBH : B ⊔ P0 ≤ Hj) :
    (∃ ω : J, Row17Conc B ω) ∨
      ∃ hBle : B ≤ Hj, IsExt ↥((fHj.comp (Subgroup.inclusion hBle)).range)
        (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have hs : IsSimpleGroup (ModO2 B) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hPSL).2
  have hBc : B ∈ cComp (B ⊔ P0) :=
    mem_cComp_of_modO2_simple le_sup_left
      (Stellmacher.PU.L3YC.M24.normal_subgroupOf_sup hN) hperf hs
  have hB : B ∈ lFamily P0 := hBc
  obtain ⟨a, ha⟩ := card_eq_of_modO2_psl32 hPSL
  have hBle : B ≤ Hj := le_sup_left.trans hBH
  have hP0H : P0 ≤ Hj := P0_le_Hj
  have hB' : B.subgroupOf Hj ∈ lFamily (P0.subgroupOf Hj) := by
    have h1 := A312.mem_cComp_subgroupOf hBH (show B ∈ cComp (B ⊔ P0) from hB)
    rw [Subgroup.subgroupOf_sup hBle hP0H] at h1
    exact h1
  have hT' : IsSylowTwoOf (P0.subgroupOf Hj) ⊤ :=
    isSylowTwoOf_subgroupOf_of_le isSylowTwoOf_P0 hP0H
  have hkernil : Group.IsNilpotent ↥fHj.ker := isPGroup_ker_fHj.isNilpotent
  have hkersolv : Group.IsSolvable ↥fHj.ker := inferInstance
  have hkersolv' : Group.IsSolvable ↥(fHj.ker ⊓ (B.subgroupOf Hj ⊔ P0.subgroupOf Hj)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  have hBb : (B.subgroupOf Hj).map fHj ∈ lFamily ((P0.subgroupOf Hj).map fHj) := by
    have h2 := A312.map_mem_cComp fHj hkersolv'
      (show B.subgroupOf Hj ∈ cComp (B.subgroupOf Hj ⊔ P0.subgroupOf Hj) from hB')
    rwa [Subgroup.map_sup] at h2
  have hTf : IsSylowTwoOf ((P0.subgroupOf Hj).map fHj) ⊤ :=
    A312.isSylowTwoOf_top_map fHj fHj_surjective hT'
  set g : ↥B →* G24 := fHj.comp (Subgroup.inclusion hBle) with hg
  have hrange : g.range = (B.subgroupOf Hj).map fHj := by
    show (fHj.comp (Subgroup.inclusion hBle)).range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hgker : IsPGroup 2 g.ker := isPGroup_ker_theta hBle
  have htop : (B.subgroupOf Hj).map fHj ≠ ⊤ := by
    intro htop
    have h1 : g.range = ⊤ := hrange.trans htop
    have h2 := Subgroup.card_ker_mul_card_range g
    rw [h1, Subgroup.card_top, show Nat.card G24 = 244823040 from CFSG.Sporadic.Mathieu.card_M24,
      ha] at h2
    have h5 : (5 : ℕ) ∣ 2 ^ a * 168 := by
      rw [← h2]
      exact Dvd.dvd.mul_left (by norm_num) _
    exact not_five_dvd a h5
  have h14 := a312C14_of_lFamily isQuasisimple_G24 hTf hBb htop
  have h14' := h14.1
  rw [← hrange] at h14'
  rcases h14' with h | h | h | h
  ·
    exfalso
    obtain ⟨S, _, hS, ⟨e⟩⟩ := exists_modO2_equiv_of_ext g hgker (fun _ _ => isPGroup_of_isE2)
      (fun S _ _ hS => pCore_eq_bot_of_isPSL42 hS) h
    have h1 := Nat.card_congr e.toEquiv
    rw [CFSG.Quasithin.card_of_isPSL_two1522 4 hS,
      CFSG.Quasithin.SBc11.card_of_isPSL_three_two hPSL] at h1
    revert h1
    decide
  ·
    left
    have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
    have hperfT : ⁅g.range, g.range⁆ = g.range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range g)
    have hS₀N : (P0.subgroupOf Hj).map fHj ≤ Subgroup.normalizer (g.range : Set G24) := by
      have h1 : P0.subgroupOf Hj ≤
          Subgroup.normalizer ((B.subgroupOf Hj : Subgroup ↥Hj) : Set ↥Hj) := by
        intro p hp
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have := Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_subgroupOf.mp hp)) (y : J)
        simpa [Subgroup.mem_subgroupOf] using this
      rw [hrange]
      exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map fHj)
    obtain ⟨x, -, hx⟩ := Stellmacher.PU.L3YC.M24.row14_M24 ⟨Subgroup.topEquiv⟩ le_top hTf hS₀N
      hperfT h
    obtain ⟨ω₁, hω₁3, hω₁x⟩ :=
      exists_pow_three_lift_of_surj fHj fHj_surjective isPGroup_ker_fHj hx.2.1
    refine ⟨(ω₁ : J), ?_, ?_, ?_⟩
    · exact mem_normalizer_of_map_mem hperf hBle (fun e he => hN (Eg_le_P0 he))
        (by rw [hω₁x]; exact hx.1)
    · have := congrArg Subtype.val hω₁3
      simpa using this
    · intro b hb
      by_contra hcon
      push Not at hcon
      obtain ⟨q', hq', hne⟩ := hx.2.2.1 (g ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
      obtain ⟨q'', hq'', rfl⟩ := hq'
      set π : ↥B →* ↥g.range := g.rangeRestrict with hπdef
      have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective g
      have hπk : IsPGroup 2 π.ker := by rw [hπdef, MonoidHom.ker_rangeRestrict]; exact hgker
      have h2 : q'' ∈ ⁅CFSG.pCore 2 ↥g.range, (⊤ : Subgroup ↥g.range)⁆ := by
        rw [hx.2.2.2]; exact hq''
      have h3 : ⁅CFSG.pCore 2 ↥g.range, (⊤ : Subgroup ↥g.range)⁆ ≤
          (⁅CFSG.pCore 2 ↥B, (⊤ : Subgroup ↥B)⁆).map π := by
        calc ⁅CFSG.pCore 2 ↥g.range, (⊤ : Subgroup ↥g.range)⁆
            ≤ ⁅(CFSG.pCore 2 ↥B).map π, (⊤ : Subgroup ↥g.range)⁆ :=
              Subgroup.commutator_mono (Stellmacher.PU.L3YC.pCore_le_map π hπ hπk) le_rfl
          _ = (⁅CFSG.pCore 2 ↥B, (⊤ : Subgroup ↥B)⁆).map π := by
              rw [Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπ]
      obtain ⟨r, hr, hrq⟩ := h3 h2
      have hrJ : (r : J) ∈ ⁅(CFSG.pCore 2 ↥B).map B.subtype, B⁆ := by
        rw [commutator_pCore_map_eq]; exact ⟨r, hr, rfl⟩
      have h4 := hcon _ hrJ
      apply hne
      have h5 : ω₁ * (⟨r, hBle r.2⟩ : ↥Hj) * ω₁⁻¹ =
          (⟨b, hBle hb⟩ : ↥Hj) * ⟨r, hBle r.2⟩ * (⟨b, hBle hb⟩ : ↥Hj)⁻¹ := Subtype.ext h4
      have h6 := congrArg fHj h5
      simp only [map_mul, map_inv] at h6
      rw [hω₁x] at h6
      have hgr : g r = (q'' : G24) := congrArg Subtype.val hrq
      have h7 : fHj ⟨r, hBle r.2⟩ = (q'' : G24) := hgr
      have h8 : fHj ⟨b, hBle hb⟩ = g ⟨b, hb⟩ := rfl
      rw [h7, h8] at h6
      exact h6
  ·
    right
    exact ⟨hBle, h⟩
  ·
    exfalso
    obtain ⟨S, _, hS, ⟨e⟩⟩ := exists_modO2_equiv_of_ext g hgker (fun _ _ => isPGroup_of_isE2)
      (fun S _ _ hS => pCore_eq_bot_of_isHat hS.1 hS.2.1) h
    have h1 := Nat.card_congr e.toEquiv
    rw [card_isHat_alt6 hS, CFSG.Quasithin.SBc11.card_of_isPSL_three_two hPSL] at h1
    revert h1
    decide

end HjPart

theorem pCore_of_isExt_extraspecial {X : Type} [Group X] [Finite X]
    (h : IsExt X (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y)) :
    CFSG.IsExtraspecial 2 ↥(CFSG.pCore 2 X) ∧ Nat.card (CFSG.pCore 2 X) = 2 ^ 7 := by
  obtain ⟨V, hVn, ⟨hVe, hVc⟩, hVq⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe' : CFSG.IsExtraspecial 2 ↥V := hVe
  have hVp : IsPGroup 2 V := CFSG.IsExtraspecial.isPGroup 2 V
  have hVle : V ≤ CFSG.pCore 2 X := Stellmacher.PU.L3YC.le_pCore_two' hVn hVp
  have hle : CFSG.pCore 2 X ≤ V := by
    have h1 : (CFSG.pCore 2 X).map (QuotientGroup.mk' V) ≤ CFSG.pCore 2 (X ⧸ V) :=
      Stellmacher.PU.L3YC.map_le_pCore (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V) _
        CFSG.pCore_isPGroup
    rw [pCore_eq_bot_of_isPSL32 hVq, le_bot_iff, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at h1
    exact h1
  have hEq : V = CFSG.pCore 2 X := le_antisymm hVle hle
  subst hEq
  exact ⟨hVe', hVc⟩

section Main


theorem row17_J [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (hM3 : ∀ B : Subgroup J, ⁅B, B⁆ = B → P0 ≤ Subgroup.normalizer (B : Set J) →
      B ⊔ P0 ≤ Subgroup.normalizer (V0 : Set J) → IsPSL 3 2 1 (ModO2 B) →
      ∃ ω : J, Stellmacher.PU.L3YC.M24.Row14Conc B ω)
    {B : Subgroup J} (hperf : ⁅B, B⁆ = B) (hN : P0 ≤ Subgroup.normalizer (B : Set J))
    (hPSL : IsPSL 3 2 1 (ModO2 B)) :
    (∃ ω : J, Row17Conc B ω) ∨
      ∃ hBle : B ≤ Hj, IsExt ↥((fHj.comp (Subgroup.inclusion hBle)).range)
        (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  rcases row17_overgroups hperf hN hPSL with h | h
  · exact row17_hj hperf hN hPSL h
  · left
    obtain ⟨ω, hω⟩ := hM3 B hperf hN h hPSL
    exact ⟨ω, Row17Conc.of_row14 hω⟩

end Main

end CFSG.Quasithin.Stellmacher.L3YC
