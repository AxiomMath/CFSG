module

public import CFSG.Milestones.ASVolI.F431.RA35Gen
public import CFSG.Milestones.ASVolI.F48.Small.U42
public import CFSG.Milestones.ASVolI.F431.BF436U4C
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocFinal2

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section U42

set_option linter.unusedSectionVars false

theorem burnsideF4r_mem_sylow_of_comm {G : Type} [Group G] [Finite G] {S H : Subgroup G}
    (hS : IsSylowTwoOf S H) {y : G} (hyH : y ∈ H) (hy2 : y * y = 1)
    (hyc : ∀ s ∈ S, s * y = y * s) : y ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyN : y ∈ Subgroup.normalizer (S : Set G) := by
    have e : ∀ s ∈ S, y * s * y⁻¹ = s := fun s hs => by
      rw [← hyc s hs, mul_assoc, mul_inv_cancel, mul_one]
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      rw [e s hs]
      exact hs
    · intro hs
      have h1 : s = y * (y * s * y⁻¹) * y⁻¹ := by
        rw [hyi]
        calc s = (y * y) * s * (y * y) := by rw [hy2, one_mul, mul_one]
          _ = y * (y * s * y) * y := by simp only [mul_assoc]
      rw [h1, e _ hs]
      exact hs
  have hX : IsPGroup 2 (Subgroup.zpowers y) :=
    CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow (k := 1) (by rw [pow_one, pow_two, hy2])
  have hXN : Subgroup.zpowers y ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.zpowers_le (H := Subgroup.normalizer (S : Set G))).mpr hyN
  have hP : IsPGroup 2 (S ⊔ Subgroup.zpowers y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hS.2.1 hX hXN
  have hPH : S ⊔ Subgroup.zpowers y ≤ H := sup_le hS.1 ((Subgroup.zpowers_le (H := H)).mpr hyH)
  have hPS := burnsideF4j_eq_of_sylow_le hS hP le_sup_left hPH
  rw [← hPS]
  exact (le_sup_right : Subgroup.zpowers y ≤ S ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)

theorem burnsideF4r_u42_T_sylow_P2 : IsSylowTwoOf U42.T U42.P2 := by
  have hTP2 : U42.T ≤ U42.P2 := U42.T_le_B0.trans U42.B0_le_P2
  refine ⟨hTP2, IsPGroup.of_card (n := 6) (by rw [U42.card_T]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index (U42.T.subgroupOf U42.P2)
  have h2 : Nat.card ↥(U42.T.subgroupOf U42.P2) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP2).toEquiv, U42.card_T]
  rw [h2, U42.card_P2] at h1
  have h3 : (U42.T.subgroupOf U42.P2).index = 15 := by omega
  rw [h3]
  decide

theorem burnsideF4r_u42_pCoreOf_B0 : pCoreOf 2 U42.B0 = U42.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 U42.T := IsPGroup.of_card (n := 6) (by rw [U42.card_T]; norm_num)
  have hTB : IsSylowTwoOf U42.T U42.B0 :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right burnsideF4r_u42_T_sylow_P2 U42.T_le_B0
      U42.B0_le_P2
  apply le_antisymm (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hTB)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 U42.T_le_B0 ?_ hTp
  rw [U42.normalizer_T]

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4r_u42_eps (hyp : HypF_4_4 .U4 2 1 Gp M₁ M₂) {x : E}
    (hx : x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ θ : U42.Y ≃* ↥Gp, burnsideF48_img θ U42.B0 = Gp ⊓ (M₁ ⊓ M₂) ∧
      burnsideF48_img θ U42.P1 = Gp ⊓ M₁ ∧ burnsideF48_img θ U42.P2 = Gp ⊓ M₂ := by
  haveI := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨θ₀⟩ := U42.nonempty_mulEquiv_Y (burnsideF48_lieModel_U4 hyp.model)
  obtain ⟨θ, hθB, hθ⟩ := burnsideF48_identify θ₀.symm burnsideF48s_u42_isLieParabolics hP
  refine ⟨θ, hθB, ?_⟩
  rcases hθ with h | ⟨-, h2⟩
  · exact h
  · exfalso
    set ι : U42.Y →* E := Gp.subtype.comp θ.toMonoidHom with hιdef
    have hι : Function.Injective ι := Gp.subtype_injective.comp θ.injective
    have himg : burnsideF48_img θ U42.P2 = U42.P2.map ι := by
      unfold burnsideF48_img
      rw [Subgroup.map_map]
    rw [himg] at h2
    rw [← h2, burnsideF4d_oPPrime_map ι hι, burnsideF4j_ctr_map ι hι] at hx
    obtain ⟨y, hyZ, rfl⟩ := hx
    have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy2 : y * y = 1 := hι (by rw [map_mul, hx2, map_one])
    have hTp : IsPGroup 2 U42.T := IsPGroup.of_card (n := 6) (by rw [U42.card_T]; norm_num)
    have hTP2 : U42.T ≤ U42.P2 := U42.T_le_B0.trans U42.B0_le_P2
    have hTO : U42.T ≤ oPPrime 2 U42.P2 := burnsideF4d_Z1_le_oPPrime hTp hTP2
    have hyc : ∀ s ∈ U42.T, s * y = y * s := fun s hs =>
      (Subgroup.mem_centralizer_iff.mp hyZ.2) s (hTO hs)
    have hyP2 : y ∈ U42.P2 := burnsideF4d_oPPrime_le _ hyZ.1
    have hyT := burnsideF4r_mem_sylow_of_comm burnsideF4r_u42_T_sylow_P2 hyP2 hy2 hyc
    have hyx : y = U42.xY := U42.center_T_eq hyT hyc hy1
    subst hyx
    obtain ⟨e, he, hee⟩ := U42.exists_P2_conj_sY U42.mem_L0S_fifteen
    have h15 : U42.sY 15 ∈ ctr (oPPrime 2 U42.P2) := by
      rw [← hee]
      exact burnsideF4j_conj_mem_ctr
        (burnsideF4d_Z1_normalizer_oPPrime (Subgroup.le_normalizer he)) hyZ
    have h15T := U42.sY_mem_T U42.mem_L0S_fifteen
    have h15c : ∀ s ∈ U42.T, s * U42.sY 15 = U42.sY 15 * s := fun s hs =>
      (Subgroup.mem_centralizer_iff.mp h15.2) s (hTO hs)
    have h151 : U42.sY 15 ≠ 1 := by
      rw [← hee]
      intro h0
      apply hy1
      calc U42.xY = e⁻¹ * (e * U42.xY * e⁻¹) * e := by group
        _ = 1 := by rw [h0]; group
    have h15x := U42.center_T_eq h15T h15c h151
    rw [← U42.sY_zero] at h15x
    exact absurd (U42.sY_inj h15x) (by decide)

variable {Yc : Type} [Group Yc] {β : Cpl M₁ M₂ Yc} {M : Type} [Group M] {ε : Yc →* M}
  {z : M}

theorem burnsideF4r_u42_ctx (hyp : HypF_4_31 .U4 1 Gp M₁ M₂ β ε z) (hGp : Gp = ⊤) :
    ∃ (ι : U42.Y →* E) (C : U42.Ctx M), Function.Injective ι ∧ Function.Surjective ι ∧
      (∀ g, g ∈ U42.P1 ↔ ι g ∈ M₁) ∧ (∀ g, g ∈ U42.P2 ↔ ι g ∈ M₂) ∧
      U42.T.map ι = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧ U42.Vsub.map ι = pCoreOf 2 (Gp ⊓ M₂) ∧
      C.z = z ∧ C.φ2.range ≤ MiTwo β ε ∧
      ∀ (g : U42.Y) (hg : g ∈ U42.P2) (hgM : ι g ∈ M₂),
        C.Φ2 g = burnsideF4d_bTwo β ε ⟨ι g, hgM⟩ := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz := hyp.z_mem.1 (by decide)
  rw [burnsideF4j_Z1_eq hyp] at hz
  obtain ⟨x, hxM1, hxZ, hxz⟩ := mem_subImg.mp hz
  have hb1i := burnsideF4j_bOne_injective hyp
  have hb2i := burnsideF4j_bTwo_injective hyp
  have hx1 : x ≠ 1 := by
    intro h
    apply hyp.z_inv.1
    rw [← hxz]
    have e : (⟨x, hxM1⟩ : ↥M₁) = 1 := Subtype.ext h
    rw [e, map_one]
  have hx2 : x * x = 1 := by
    have : burnsideF4d_bOne β ε (⟨x, hxM1⟩ * ⟨x, hxM1⟩) = burnsideF4d_bOne β ε 1 := by
      rw [map_mul, hxz, map_one]
      exact hyp.z_inv.2
    exact congrArg Subtype.val (hb1i this)
  obtain ⟨θ, hθB, hθ1, hθ2⟩ := burnsideF4r_u42_eps hyp.amalgam hxZ hx1 hx2
  set ι : U42.Y →* E := Gp.subtype.comp θ.toMonoidHom with hιdef
  have hι : Function.Injective ι := Gp.subtype_injective.comp θ.injective
  have hιs : Function.Surjective ι := by
    intro e
    have he : e ∈ Gp := by rw [hGp]; exact Subgroup.mem_top e
    obtain ⟨y, hy⟩ := θ.surjective ⟨e, he⟩
    exact ⟨y, by rw [hιdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hy]; rfl⟩
  have himg : ∀ Q : Subgroup U42.Y, burnsideF48_img θ Q = Q.map ι := fun Q => by
    unfold burnsideF48_img
    rw [Subgroup.map_map]
  have hle : ∀ X : Subgroup E, Gp ⊓ X = X := fun X => inf_eq_right.2 (hGp ▸ le_top)
  rw [himg, hle] at hθ1 hθ2
  rw [himg] at hθB
  have hm1 : ∀ g, g ∈ U42.P1 ↔ ι g ∈ M₁ := fun g => by
    rw [← hθ1, Subgroup.mem_map_iff_mem hι]
  have hm2 : ∀ g, g ∈ U42.P2 ↔ ι g ∈ M₂ := fun g => by
    rw [← hθ2, Subgroup.mem_map_iff_mem hι]
  have hTS : U42.T.map ι = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    rw [← hθB, burnsideF4j_pCoreOf_map ι hι, burnsideF4r_u42_pCoreOf_B0]
  have hVQ : U42.Vsub.map ι = pCoreOf 2 (Gp ⊓ M₂) := by
    rw [hle, ← hθ2, burnsideF4j_pCoreOf_map ι hι, U42.pCoreOf_P2]
  have hιx : ι U42.xY = x := by
    obtain ⟨w, hwZ, hwz, hw1, -⟩ := burnsideF4r_zbar hyp (by decide)
    have hwx : (w : E) = x := by
      rw [burnsideF4j_bM_eq_bOne, ← hxz] at hwz
      exact congrArg Subtype.val (hb1i hwz)
    rw [← hTS, burnsideF4j_ctr_map ι hι] at hwZ
    obtain ⟨y, hyZ, hyw⟩ := hwZ
    have hy1 : y ≠ 1 := fun h => hw1 (Subtype.ext (by rw [← hyw, h, map_one]; rfl))
    have hyx : y = U42.xY :=
      U42.center_T_eq hyZ.1 (fun s hs => (Subgroup.mem_centralizer_iff.mp hyZ.2) s hs) hy1
    rw [← hyx, hyw, hwx]
  let ρ1 : ↥U42.P1 →* ↥M₁ := (ι.comp U42.P1.subtype).codRestrict M₁ (fun p => (hm1 p).1 p.2)
  let ρ2 : ↥U42.P2 →* ↥M₂ := (ι.comp U42.P2.subtype).codRestrict M₂ (fun p => (hm2 p).1 p.2)
  have hρ1 : Function.Injective ρ1 := fun a b h => by
    have h' : ι a = ι b := congrArg (fun m : ↥M₁ => (m : E)) h
    exact Subtype.ext (hι h')
  have hρ2 : Function.Injective ρ2 := fun a b h => by
    have h' : ι a = ι b := congrArg (fun m : ↥M₂ => (m : E)) h
    exact Subtype.ext (hι h')
  have hφ1x : (burnsideF4d_bOne β ε).comp ρ1 ⟨U42.xY, U42.mem_P1_xY⟩ = z := by
    rw [← hxz]
    show burnsideF4d_bOne β ε ⟨ι U42.xY, _⟩ = _
    congr 1
    exact Subtype.ext hιx
  have hVab : ∀ a ∈ pCoreOf 2 (Gp ⊓ M₂), ∀ b ∈ pCoreOf 2 (Gp ⊓ M₂), a * b = b * a := by
    rw [← hVQ]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, U42.Vsub_comm ha hb]
  have hctrQ : ctr (pCoreOf 2 (Gp ⊓ M₂)) = pCoreOf 2 (Gp ⊓ M₂) := by
    apply le_antisymm inf_le_left
    intro a ha
    exact ⟨ha, Subgroup.mem_centralizer_iff.mpr fun b hb => hVab b hb a ha⟩
  have hQ2 : pCoreOf 2 (Gp ⊓ M₂) ≤ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hVimg : Subgroup.map ((burnsideF4d_bTwo β ε).comp ρ2) (U42.Vsub.subgroupOf U42.P2) =
      ctr (pCoreOf 2 (GiTwo Gp β ε)) := by
    rw [burnsideF4d_GiTwo_eq, subImg_pCoreOf hb2i inf_le_right,
      burnsideF4j_ctr_subImg _ hb2i hQ2, hctrQ]
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine mem_subImg.mpr ⟨ι p, (hm2 p).1 p.2, ?_, rfl⟩
      rw [← hVQ]
      exact ⟨p, hp, rfl⟩
    · intro hy
      obtain ⟨e, he2, heQ, rfl⟩ := mem_subImg.mp hy
      rw [← hVQ] at heQ
      obtain ⟨v, hv, rfl⟩ := heQ
      have hvP : v ∈ U42.P2 := U42.Vsub_le_P2 hv
      exact ⟨⟨v, hvP⟩, hv, rfl⟩
  let C : U42.Ctx M :=
    { φ1 := (burnsideF4d_bOne β ε).comp ρ1
      φ2 := (burnsideF4d_bTwo β ε).comp ρ2
      inj1 := hb1i.comp hρ1
      inj2 := hb2i.comp hρ2
      agree := fun b h1 h2 => burnsideF4j_bOne_eq_bTwo β ε (ι b) ((hm1 b).1 h1) ((hm2 b).1 h2)
      cent := fun g hg => by
        have hgz : g ∈ Subgroup.centralizer ({z} : Set M) := by
          rw [Subgroup.mem_centralizer_singleton_iff, ← hφ1x]
          exact hg
        have hgM := hyp.hb hgz
        rw [burnsideF4d_MiOne_eq, subImg_self] at hgM
        obtain ⟨m, rfl⟩ := hgM
        obtain ⟨p, hp⟩ := hιs (m : E)
        refine ⟨⟨p, (hm1 p).2 (hp ▸ m.2)⟩, ?_⟩
        show burnsideF4d_bOne β ε (ρ1 _) = _
        congr 1
        exact Subtype.ext hp
      norm := fun g hg => by
        rw [hVimg, (hyp.ha (Or.inr (Or.inl rfl))).2, burnsideF4d_MiTwo_eq, subImg_self] at hg
        obtain ⟨m, rfl⟩ := hg
        obtain ⟨p, hp⟩ := hιs (m : E)
        refine ⟨⟨p, (hm2 p).2 (hp ▸ m.2)⟩, ?_⟩
        show burnsideF4d_bTwo β ε (ρ2 _) = _
        congr 1
        exact Subtype.ext hp }
  refine ⟨ι, C, hι, hιs, hm1, hm2, hTS, hVQ, ?_, ?_, ?_⟩
  · rw [U42.Ctx.z_def, C.Φ1_of_mem U42.mem_P1_xY]
    exact hφ1x
  · rintro _ ⟨p, rfl⟩
    exact ⟨f2 (c := β) (ρ2 p), ⟨ρ2 p, rfl⟩, rfl⟩
  · intro g hg hgM
    rw [C.Φ2_of_mem hg]
    rfl

theorem burnsideF4r_top_of_odd_sq [Finite E] (hn : Gp.Normal) (hsq : ∀ e : E, e * e ∈ Gp)
    (hodd : Odd Gp.index) : Gp = ⊤ := by
  rw [eq_top_iff]
  intro e _
  set q : E ⧸ Gp := (e : E ⧸ Gp) with hq
  have hq2 : q ^ 2 = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
    exact hsq e
  have h1 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
  have h2 : orderOf q ∣ Gp.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard q
  have h3 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  rw [orderOf_eq_one_iff, hq, QuotientGroup.eq_one_iff] at h3
  exact h3

variable {f : ℕ}

theorem burnsideF4r_U4_top_nonfused (hyp : HypF_4_31 .U4 f Gp M₁ M₂ β ε z) (hf : f < 2)
    (hGp : Gp = ⊤) :
    ∃ v : ↥(M₁ ⊓ M₂), (v : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧ v ≠ 1 ∧ v * v = 1 ∧
      ¬ IsConj z (bM β ε v) := by
  haveI := hyp.finite_M
  have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
  obtain rfl : f = 1 := by omega
  obtain ⟨ι, C, hι, -, hm1, hm2, hTS, -, hCz, -, hΦ2⟩ := burnsideF4r_u42_ctx hyp hGp
  have htV := U42.tPrime_mem_Vsub
  have htT : U42.tPrime ∈ U42.T := U42.Vsub_le_T htV
  have htB : U42.tPrime ∈ U42.B0 := U42.T_le_B0 htT
  have ht1 : ι U42.tPrime ∈ M₁ := (hm1 _).1 (U42.B0_le_P1 htB)
  have ht2 : ι U42.tPrime ∈ M₂ := (hm2 _).1 (U42.B0_le_P2 htB)
  refine ⟨⟨ι U42.tPrime, ht1, ht2⟩, ?_, ?_, ?_, ?_⟩
  · rw [← hTS]
    exact ⟨_, htT, rfl⟩
  · intro h0
    apply U42.tPrime_ne_one
    apply hι
    rw [map_one]
    exact congrArg Subtype.val h0
  · apply Subtype.ext
    show ι U42.tPrime * ι U42.tPrime = 1
    rw [← map_mul, U42.tPrime_sq, map_one]
  · intro hc
    obtain ⟨c, hcz⟩ := isConj_iff.mp hc
    apply C.not_conj_z htV U42.not_isConj_tPrime c
    rw [hΦ2 _ (U42.B0_le_P2 htB) ht2, hCz, hcz, burnsideF4j_bM_eq_bOne]
    exact (burnsideF4j_bOne_eq_bTwo β ε _ ht1 ht2).symm

theorem burnsideF4r_A42_U4 (hyp : HypF_4_31 .U4 f Gp M₁ M₂ β ε z) (hf : f < 2)
    (hodd : Odd Gp.index) :
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .U4 Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε := by
  classical
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
  obtain rfl : f = 1 := by omega
  have hGp : Gp = ⊤ := burnsideF4r_top_of_odd_sq hyp.amalgam.normal
    (burnsideF4m_u4_sq_mem hyp.amalgam.toHypF_4_4g) hodd
  obtain ⟨ι, C, hι, hιs, hm1, hm2, hTS, hVQ, hCz, hrange, hΦ2⟩ := burnsideF4r_u42_ctx hyp hGp
  have htV := U42.tPrime_mem_Vsub
  have htT : U42.tPrime ∈ U42.T := U42.Vsub_le_T htV
  have htB : U42.tPrime ∈ U42.B0 := U42.T_le_B0 htT
  have ht2 : ι U42.tPrime ∈ M₂ := (hm2 _).1 (U42.B0_le_P2 htB)
  have ht1' : ι U42.tPrime ≠ 1 := by
    intro h0
    apply U42.tPrime_ne_one
    apply hι
    rw [map_one]
    exact h0
  have ht2' : ι U42.tPrime * ι U42.tPrime = 1 := by
    rw [← map_mul, U42.tPrime_sq, map_one]
  refine ⟨⟨ι U42.tPrime, ht2⟩, ?_, ?_, ?_⟩
  · rw [← hVQ]
    exact ⟨_, htV, rfl⟩
  ·
    have h27 := as_F_4_27 .U4 1 E Gp M₁ M₂ hyp.amalgam hGp
    dsimp only at h27
    obtain ⟨hχm, -, -, h3, -, -⟩ := h27
    obtain ⟨-, -, hls, hliff, -⟩ := h3 ⟨by decide, by decide, by decide⟩
    rcases hls _ ht1' ht2' with htL | htS
    · exfalso
      obtain ⟨c, -, hc⟩ := (hliff _ ht1' ht2').mp htL
      have hle : Gp ⊓ (M₁ ⊓ M₂) = M₁ ⊓ M₂ := inf_eq_right.2 (hGp ▸ le_top)
      rw [← hle, ← hTS, burnsideF4j_ctr_map ι hι] at hc
      obtain ⟨w, hwZ, hwc⟩ := hc
      have hw1 : w ≠ 1 := by
        intro h0
        apply ht1'
        have e1 : c * ι U42.tPrime * c⁻¹ = 1 := by rw [← hwc, h0, map_one]
        calc ι U42.tPrime = c⁻¹ * (c * ι U42.tPrime * c⁻¹) * c := by group
          _ = 1 := by rw [e1]; group
      have hwx : w = U42.xY :=
        U42.center_T_eq hwZ.1 (fun s hs => (Subgroup.mem_centralizer_iff.mp hwZ.2) s hs) hw1
      obtain ⟨c', rfl⟩ := hιs c
      apply U42.not_isConj_tPrime
      refine isConj_iff.mpr ⟨c'⁻¹, hι ?_⟩
      rw [map_mul, map_mul, map_inv, inv_inv, ← hwx, hwc]
      group
    · exact ⟨1, hyp.amalgam.toHypF_4_4g.chart, hχm, htS⟩
  ·
    have e1 : epsG β ε (f2 (c := β) ⟨ι U42.tPrime, ht2⟩) = C.tG := by
      rw [U42.Ctx.tG_def, hΦ2 _ (U42.B0_le_P2 htB) ht2]
      rfl
    rw [e1]
    exact (C.centralizer_tG_le_range).trans hrange

end U42

end CFSG.ASVolI
