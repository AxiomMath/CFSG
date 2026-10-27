module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Cz
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsTransport

public section

namespace CFSG.Quasithin.H13.KGA314J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc
open CFSG.Quasithin.J4Fam (M3 rho3 isPGroup_ker_rho3_alpha3 Eg_le_D D_le_M3 OrbM3)

theorem charTwo_of_goodLocal {X : Type} [Group X] [Finite X] {Kx : Subgroup X}
    (h : CFSG.QuasithinUnique.Vol2Native.L239.GoodLocal Kx) : CharTwo Kx :=
  (h X Kx (MonoidHom.id _) Function.surjective_id (by
    rw [MonoidHom.ker_id]
    exact IsPGroup.of_bot)).1

section M3

theorem charTwo_M3 :
    CharTwo M3 := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup J := pCoreOf 2 M3 with hQ
  set K₀ : Subgroup ↥M3 := (rho3 hF).ker ⊓ V0.normalizerMonoidHom.ker with hK₀
  set K : Subgroup J := K₀.map M3.subtype with hK
  have hKQ : K ≤ Q := by
    have hnorm : M3 ≤ Subgroup.normalizer (K : Set J) := by
      have h1 := Subgroup.le_normalizer_map (H := K₀) M3.subtype
      have h2 : Subgroup.normalizer (K₀ : Set ↥M3) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr inferInstance
      rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      exact h1
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le K₀) hnorm
      ((isPGroup_ker_rho3_alpha3 hF).map _)
  have hVQ : V0 ≤ Q := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : V0 ≤ M3) le_rfl ?_
    exact IsPGroup.of_card (n := 3) (by rw [CFSG.Quasithin.J4Rad.card_V0 hM]; norm_num)
  have hEM : Eg uJ 11 ≤ M3 := (Eg_le_D hM).trans D_le_M3
  set ρE : ↥(Eg uJ 11) →* Equiv.Perm (Fin 5) := (rho3 hF).comp (Subgroup.inclusion hEM)
  set V : Subgroup J := ρE.ker.map (Eg uJ 11).subtype with hV
  have hVE : V ≤ Eg uJ 11 := Subgroup.map_subtype_le _
  have hVK : V ≤ K := by
    rintro _ ⟨e, he, rfl⟩
    refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion hEM e, Subgroup.mem_inf.mpr ⟨he, ?_⟩, rfl⟩
    rw [MonoidHom.mem_ker, CFSG.Quasithin.J4Rad.normalizerMonoidHom_eq_one_iff']
    exact Eg_le_D hM e.2
  have hVcard : 8 < Nat.card V := by
    have h1 := Subgroup.card_ker_mul_card_range ρE
    rw [CFSG.Sporadic.J4.QT.card_Eg_uJ hM] at h1
    have h2 : IsPGroup 2 ρE.range :=
      (isPGroup_Eg (elem_uJ hM)).of_surjective ρE.rangeRestrict ρE.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have h3 : 2 ^ k ∣ 120 := by
      rw [← hk]
      calc Nat.card ρE.range ∣ Nat.card (Equiv.Perm (Fin 5)) := Subgroup.card_subgroup_dvd_card _
        _ = 120 := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans h3
      omega
    have h4 : 2 ^ k ≤ 8 := by
      calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
        _ = 8 := by norm_num
    rw [hV, Subgroup.card_map_of_injective (Eg uJ 11).subtype_injective]
    rw [hk] at h1
    have h5 : 0 < 2 ^ k := Nat.two_pow_pos k
    nlinarith
  intro c hc
  obtain ⟨hcM, hcQ⟩ := Subgroup.mem_inf.mp hc
  have hconj : ∀ m ∈ M3, m⁻¹ * c * m ∈ Hj := by
    intro m hm
    refine CFSG.Sporadic.J4.QT2.mem_Hj_of_big_inter hF hVE (fun v hv => ?_) hVcard
    have hvQ : v ∈ Q := hKQ (hVK hv)
    have hmv : m * v * m⁻¹ ∈ Q := by
      have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M3 hm
      exact (Subgroup.mem_normalizer_iff.mp this v).mp hvQ
    have hcv : c * (m * v * m⁻¹) = (m * v * m⁻¹) * c :=
      (Subgroup.mem_centralizer_iff.mp hcQ _ hmv).symm
    have e : (m⁻¹ * c * m)⁻¹ * v * (m⁻¹ * c * m) = v := by
      calc (m⁻¹ * c * m)⁻¹ * v * (m⁻¹ * c * m)
          = m⁻¹ * c⁻¹ * ((m * v * m⁻¹) * c) * m := by group
        _ = m⁻¹ * c⁻¹ * (c * (m * v * m⁻¹)) * m := by rw [hcv]
        _ = v := by group
    rw [e]
    exact hVE hv
  have hfix : ∀ x : ↥OrbM3, (⟨c, hcM⟩ : ↥M3) • x = x := by
    intro x
    obtain ⟨m, hm⟩ := x.2
    apply Subtype.ext
    change (⟨c, hcM⟩ : ↥M3) • (x : J ⧸ Hj) = (x : J ⧸ Hj)
    rw [← hm, smul_smul]
    change ((c * m : J)) • CFSG.Quasithin.F134.J4E9.basePt =
      (m : J) • CFSG.Quasithin.F134.J4E9.basePt
    rw [CFSG.Quasithin.F134.J4E9.smul_basePt_eq_iff, ← mul_assoc]
    exact hconj m m.2
  have hρ : rho3 hF ⟨c, hcM⟩ = 1 := by
    ext i
    obtain ⟨x, rfl⟩ := (CFSG.Quasithin.J4Fam.eOrb hF).surjective i
    rw [CFSG.Quasithin.J4Fam.rho3_apply, hfix x]
    rfl
  have hα : V0.normalizerMonoidHom ⟨c, hcM⟩ = 1 := by
    rw [CFSG.Quasithin.J4Rad.normalizerMonoidHom_eq_one_iff']
    intro v hv
    exact Subgroup.mem_centralizer_iff.mp hcQ v (hVQ hv)
  exact hKQ (Subgroup.mem_map.mpr ⟨⟨c, hcM⟩,
    Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr hρ, MonoidHom.mem_ker.mpr hα⟩, rfl⟩)

end M3

theorem isSylowTwoOf_of_top {G : Type*} [Group G] {P M : Subgroup G} (hP : IsSylowTwoOf P ⊤)
    (hPM : P ≤ M) : IsSylowTwoOf P M := by
  refine ⟨hPM, hP.2.1, fun h => hP.2.2 ?_⟩
  change 2 ∣ P.relIndex ⊤
  change 2 ∣ P.relIndex M at h
  exact h.trans ⟨_, (Subgroup.relIndex_mul_relIndex P M ⊤ hPM le_top).symm⟩

theorem eq_bot_or_top_of_isSubnormal {S : Type*} [Group S] [IsSimpleGroup S] {H K : Subgroup S}
    (h : IsSubnormal H K) (hK : K = ⊥ ∨ K = ⊤) : H = ⊥ ∨ H = ⊤ :=
  by
    rcases hK with rfl | rfl
    · exact Or.inl (le_bot_iff.1 h.le)
    · exact h.eq_bot_or_top

theorem isSylowTwoOf_subgroupOf_top {G : Type*} [Group G] {T L : Subgroup G}
    (hT : IsSylowTwoOf T L) : IsSylowTwoOf (T.subgroupOf L) ⊤ := by
  refine ⟨le_top, hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm, ?_⟩
  change ¬ 2 ∣ (T.subgroupOf L).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact hT.2.2

theorem map_map_symm' {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (H : Subgroup G) :
    (H.map φ.toMonoidHom).map φ.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem charTwo_transport {Γ : Type} [Group Γ] [Finite Γ] {P : Subgroup Γ}
    (hP : IsSylowTwoOf P ⊤)
    (hΓ : ∀ Y : Subgroup Γ, P ≤ Y → Y ≠ ⊤ → ¬ Group.IsSolvable ↥Y → CharTwo Y)
    {X : Type} [Group X] [Finite X] (e : X ≃* Γ) {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (hTY : T ≤ Y) (hY : Y ≠ ⊤) (hns : ¬ Group.IsSolvable ↥Y) : CharTwo Y := by
  have hT₁ := CFSG.QuasithinUnique.Unc25K1.isSylowTwoOf_top_map e hT
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.L246C127.exists_conj_of_isSylowTwoOf' hT₁ hP
  set c : Γ ≃* Γ := MulAut.conj g
  set Y₂ : Subgroup Γ := (Y.map e.toMonoidHom).map c.toMonoidHom with hY₂
  have hPY : P ≤ Y₂ := by
    rw [← hg]
    exact Subgroup.map_mono (Subgroup.map_mono hTY)
  have hback : (Y₂.map c.symm.toMonoidHom).map e.symm.toMonoidHom = Y := by
    rw [hY₂, map_map_symm', map_map_symm']
  have hY₂ne : Y₂ ≠ ⊤ := by
    intro htop
    apply hY
    rw [← hback, htop, Subgroup.map_top_of_surjective _ c.symm.surjective,
      Subgroup.map_top_of_surjective _ e.symm.surjective]
  let eY : ↥Y ≃* ↥Y₂ := (Y.equivMapOfInjective e.toMonoidHom e.injective).trans
    ((Y.map e.toMonoidHom).equivMapOfInjective c.toMonoidHom c.injective)
  have hns₂ : ¬ Group.IsSolvable ↥Y₂ := fun hs =>
    hns (Group.isSolvable_of_surjective (f := eY.symm.toMonoidHom) eY.symm.surjective)
  have hc := hΓ Y₂ hPY hY₂ne hns₂
  have h1 := CFSG.QuasithinUnique.Ch1.charTwo_map_mulEquiv e.symm
    (CFSG.QuasithinUnique.Ch1.charTwo_map_mulEquiv c.symm hc)
  rwa [hback] at h1

section Main

theorem charTwo_of_overgroup [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {Y : Subgroup J} (hP : P0 ≤ Y) (hY : Y ≠ ⊤) (hns : ¬ Group.IsSolvable ↥Y) : CharTwo Y := by
  have hS : IsSylowTwoOf P0 ⊤ := CFSG.Quasithin.J4Loc.isSylowTwoOf_P0
  have key : ∀ M : Subgroup J, CharTwo M → Y ≤ M → CharTwo Y := fun M hM hYM =>
    charTwo_of_pCore_centralizer_le hM hYM (inf_le_left.trans
      ((CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
        (isSylowTwoOf_of_top hS (hP.trans hYM))).trans hP))
  rcases CFSG.Quasithin.J4Ov.j4OvergroupLocal_holds Y hP hY hns with h | h | h
  · exact key _ (charTwo_of_goodLocal
      CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs.goodLocal_Hj) h
  · exact key _ (charTwo_of_goodLocal
      CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs.goodLocal_centralizer_zJ) h
  · exact key _ charTwo_M3 h

theorem a314j4_holds [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G),
    IsSylowTwoOf T L → B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .J4 ↥L →
    IsAlt 5 (ModO2 B) → CFSG.generalizedFitting ↥B = CFSG.pCore 2 ↥B := by
  intro G _ _ L T B hT hB hBL hBne hL _
  have hF : J4Facts := j4Facts
  obtain ⟨e₀⟩ := hL
  obtain ⟨ψ⟩ : Nonempty (↥L ≃* J) := ⟨e₀.trans (seedEquiv hF.mat)⟩
  have hBc : B ∈ cComp (B ⊔ T) := hB
  obtain ⟨hB1, -, hBsub, -⟩ := hBc
  have hXL : B ⊔ T ≤ L := sup_le hBL hT.1
  have hXne : B ⊔ T ≠ L := by
    intro hXL'
    have hsub : IsSubnormal (B.subgroupOf L) ⊤ := by
      have := CFSG.Quasithin.A4.subnormal_subgroupOf L hBsub
      rwa [hXL', Subgroup.subgroupOf_self] at this
    have hJs : IsSimpleGroup J := CFSG.Sporadic.J4.isSimpleGroup_J hF
    have : IsSimpleGroup ↥L := @MulEquiv.isSimpleGroup _ _ _ _ hJs ψ
    rcases eq_bot_or_top_of_isSubnormal hsub (Or.inr rfl) with h | h
    · apply hB1
      rw [← Subgroup.map_subgroupOf_eq_of_le hBL, h, Subgroup.map_bot]
    · apply hBne
      refine le_antisymm hBL fun l hl => ?_
      have : (⟨l, hl⟩ : ↥L) ∈ B.subgroupOf L := by rw [h]; trivial
      exact this
  have hns : ¬ Group.IsSolvable ↥(B ⊔ T) := CFSG.Quasithin.A312S.not_isSolvable_sup hB
  set Y : Subgroup ↥L := (B ⊔ T).subgroupOf L with hYdef
  let eY : ↥Y ≃* ↥(B ⊔ T) := Subgroup.subgroupOfEquivOfLe hXL
  have hTY : T.subgroupOf L ≤ Y := fun x hx => (le_sup_right : T ≤ B ⊔ T) hx
  have hYne : Y ≠ ⊤ := by
    intro htop
    apply hXne
    refine le_antisymm hXL fun l hl => ?_
    have : (⟨l, hl⟩ : ↥L) ∈ Y := by rw [htop]; trivial
    exact this
  have hYns : ¬ Group.IsSolvable ↥Y := fun hs =>
    hns (Group.isSolvable_of_surjective (f := eY.toMonoidHom) eY.surjective)
  have hYc : CharTwo Y := charTwo_transport (Γ := J) (P := P0)
    (CFSG.Quasithin.J4Loc.isSylowTwoOf_P0 : IsSylowTwoOf P0 ⊤)
    (fun Y' hP hY' hns' => charTwo_of_overgroup hP hY' hns') ψ
    (isSylowTwoOf_subgroupOf_top hT) hTY hYne hYns
  have hXc : CharTwo (B ⊔ T) := charTwo_iff_internal.mpr
    (CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2 eY
      (charTwo_iff_internal.mp hYc))
  have hBc2 : CharTwo B := CFSG.Quasithin.A4.charTwo_of_subnormal hBsub hXc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore]
  have h := charTwo_iff_internal.mp hBc2
  exact h

end Main

end CFSG.Quasithin.H13.KGA314J4
