module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType.GGQ2Frame.SpPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private theorem l02qspf_centerPrime_sp {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [NeZero m] (hp : p.Prime) (hp2 : p ≠ 2) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSpGroup K m)) := by
  have := Fact.mk hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* LargeEvenSpGroup K m),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSpGroup K m →* E, ∀ h, π (s h) = h :=
    fun E _ _ π hπ hcen hC =>
      CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_coprime (n := m) (K := K)
        (p := 2) E π hπ hcen hC
  have : Finite (LargeEvenSpGroup K m) := Finite.of_injective
    (fun x : LargeEvenSpGroup K m =>
      ((x : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  have hinj : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnp := StdSubRestU.noTorsion_ker_of_section
    (q := LargeEvenProjMk (LargeEvenSpGroup K m)) (QuotientGroup.mk'_surjective _) hsplit hp hp2
    (fun z hz _ => hinj ((MonoidHom.mem_ker.mp hz).trans (map_one _).symm)) hψ hker hperf
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    have h1 : ψ z ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 l]
    rw [TableBSymp.center_spProj_eq_bot, Subgroup.mem_bot] at h1
    exact h1
  have hzp : (z : L') ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 : z = 1 := Subtype.ext (hnp _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

private theorem l02qspf_torusSCRank_sp {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) :
    GGTorusSCRank p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq
  have hinj : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  set e₁ : ↥(LargeEvenSpGroup K m) ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  set e₂ : ↥(CFSG.Open.StatedSp m K) ≃*
      ↥(CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K)) :=
    (MonoidHom.ofInjective CFSG.RankThree.Classical.spLin_injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.Classical.range_spLin)
  have hLS : LargeEvenSpGroup K m = CFSG.Open.StatedSp m K := rfl
  have hfr : Module.finrank K (Fin m ⊕ Fin m → K) / 2 = m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine ggTorusSCRank_of_selfCent hp TableBSymp.sp_I_subset_inn TableBSymp.center_spProj_eq_bot
    (l02qspf_centerPrime_sp hp hp2)
    (selfCentPowLe_of_mulEquiv (e₁.symm.trans ((MulEquiv.subgroupCongr hLS).trans e₂))
      fun E hE hsc => ?_)
  have h := SpNS.pow_finrank_div_two_le_card_of_selfCent hp hpq
    CFSG.RankThree.Classical.spForm_isAlt CFSG.RankThree.Classical.spForm_nondegenerate E hE hsc
  rwa [hfr] at h

theorem piMat_surjective_holds :
    ∀ {G : Type} [Group G] [Finite G] {H : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
      [CharP K 2] [NeZero m] (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSpGroup K m)),
      Function.Surjective (piMat θ) := by
  intro G _ _ H m K _ _ _ _ θ
  unfold piMat
  exact (TableBSymp.spProjEquivSp (K := K) (m := m)).surjective.comp (ggQuotHom_surjective θ)

theorem ker_piMat_holds :
    ∀ {G : Type} [Group G] [Finite G] {H : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
      [CharP K 2] [NeZero m] (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSpGroup K m)),
      (piMat θ).ker = Subgroup.center ↥H := by
  intro G _ _ H m K _ _ _ _ θ
  ext h
  change (TableBSymp.spProjEquivSp (K := K) (m := m)) (ggQuotHom θ h) = 1 ↔
    h ∈ Subgroup.center ↥H
  rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_ggQuotHom]

theorem exists_rho_holds :
    ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
      [CharP K 2] [NeZero m] (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSpGroup K m))
      (hEN : E ≤ Subgroup.normalizer (H : Set G))
      (_ : ∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)),
      ∃ ρ : ↥E →* ↥(StatedSp m K), ∀ (b : ↥E) (h : ↥H),
        piMat θ (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h) = ρ b * piMat θ h * (ρ b)⁻¹ := by
  intro G _ _ H E m K _ _ _ _ θ hEN hI
  classical
  let R := LargeEvenProj (LargeEvenSpGroup K m)
  let e : R ≃* ↥(StatedSp m K) := TableBSymp.spProjEquivSp (K := K) (m := m)
  have hconjinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAutConj_injective_of_center_eq_bot (TableBSymp.center_spProj_eq_bot (K := K) (m := m))
  have hmem : ∀ b : ↥E, ∃ a : R, MulAut.conj a = ggBeta H θ hEN b := by
    intro b
    have hb : ggBeta H θ hEN b ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) := by
      rw [ggBeta_eq]
      exact hI b b.2
    exact TableBSymp.sp_I_subset_inn hb
  let aOf : ↥E → R := fun b => Classical.choose (hmem b)
  have haOf : ∀ b : ↥E, MulAut.conj (aOf b) = ggBeta H θ hEN b := fun b =>
    Classical.choose_spec (hmem b)
  let φ : ↥E →* R :=
    { toFun := aOf
      map_one' := by
        apply hconjinj
        rw [haOf 1, map_one, map_one]
      map_mul' := by
        intro b c
        apply hconjinj
        calc MulAut.conj (aOf (b * c))
            = ggBeta H θ hEN (b * c) := haOf (b * c)
          _ = ggBeta H θ hEN b * ggBeta H θ hEN c := map_mul _ _ _
          _ = MulAut.conj (aOf b) * MulAut.conj (aOf c) := by rw [haOf b, haOf c]
          _ = MulAut.conj (aOf b * aOf c) := (map_mul _ _ _).symm }
  let ρ : ↥E →* ↥(StatedSp m K) := e.toMonoidHom.comp φ
  refine ⟨ρ, ?_⟩
  intro b h
  have h1 : ggQuotHom θ (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h) =
      ggBeta H θ hEN b (ggQuotHom θ h) :=
    (ggBeta_ggQuotHom H hEN θ b h).symm
  calc
    piMat θ (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h)
        = e (ggQuotHom θ (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h)) := rfl
    _ = e (ggBeta H θ hEN b (ggQuotHom θ h)) := by rw [h1]
    _ = e (MulAut.conj (aOf b) (ggQuotHom θ h)) := by rw [← haOf b]
    _ = e (aOf b * ggQuotHom θ h * (aOf b)⁻¹) := by rw [MulAut.conj_apply]
    _ = e (aOf b) * e (ggQuotHom θ h) * (e (aOf b))⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = ρ b * piMat θ h * (ρ b)⁻¹ := rfl

theorem three_pow_le_card_E_holds :
    ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
      [CharP K 2] [NeZero m] (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSpGroup K m)),
      Nat.card K = 2 → commutator H = ⊤ → IsElemAbelian 3 E →
      ∀ (hEN : E ≤ Subgroup.normalizer (H : Set G)),
      (∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) →
      (∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E) →
      E ⊓ Subgroup.centralizer (H : Set G) = ⊥ → 3 ^ 3 ≤ Nat.card E → 3 ^ m ≤ Nat.card E := by
  intro G _ _ H E m K _ _ _ _ θ hcardK hperf hE hEN hI hSC hdisc h33
  classical
  have hker : (ggGamma H hEN).ker = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff] at hb
    have hb' : (b : G) ∈ E ⊓ Subgroup.centralizer (H : Set G) := ⟨b.2, hb⟩
    rw [hdisc] at hb'
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.mem_bot.mp hb')
  have hcardGamma : Nat.card (ggGamma H hEN).range = Nat.card ↥E := by
    let f : ↥E → (ggGamma H hEN).range := fun b => ⟨ggGamma H hEN b, ⟨b, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · intro b c hbc
        have h1 : ggGamma H hEN b = ggGamma H hEN c := congrArg Subtype.val hbc
        have h2 : ggGamma H hEN (b * c⁻¹) = 1 := by
          rw [map_mul, map_inv, h1, mul_inv_cancel]
        have h3 : b * c⁻¹ ∈ (ggGamma H hEN).ker := h2
        rw [hker] at h3
        have hbc1 : b * c⁻¹ = 1 := Subgroup.mem_bot.mp h3
        calc b = b * c⁻¹ * c := by group
          _ = c := by rw [hbc1, one_mul]
      · rintro ⟨y, b, rfl⟩
        exact ⟨b, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have hcard3 : 3 ^ 3 ≤ Nat.card (ggGamma H hEN).range := by
    rw [hcardGamma]
    exact h33
  have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 3) (by norm_num)
    (Bs := E) (X := H) hE hSC hperf θ hEN hI hcard3 hcard3
  obtain ⟨hψ, hkerψ, hperf', hA, hAI, hr, h3', hself⟩ := hTB
  have hSCR := l02qspf_torusSCRank_sp (K := K) (m := m) (p := 3)
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)) (by norm_num)
    (show 3 ∣ Nat.card K + 1 from by
      have h : Nat.card K + 1 = 3 := by omega
      rw [h])
  have hle : 3 ^ m ≤ Nat.card (ggGamma H hEN).range :=
    hSCR ↥H (ggQuotHom θ) hψ hkerψ hperf' (ggGamma H hEN).range hA hAI hself
  rwa [hcardGamma] at hle

theorem exists_spFrame_holds :
    ExistsSpFrame := by
  intro G _ _ H E m K _ _ _ _ θ hcardK hperf hE hEN hI hSC hdisc h33
  classical
  obtain ⟨ρ, hρ⟩ := exists_rho_holds θ hEN hI
  have hρinj : Function.Injective ρ := by
    intro b c hbc
    have hd : ρ (b * c⁻¹) = 1 := by
      rw [map_mul, map_inv, hbc, mul_inv_cancel]
    have hLA : ggLAut H θ ⟨(((b * c⁻¹ : ↥E) : G)), hEN (b * c⁻¹).2⟩ = 1 := by
      ext r
      obtain ⟨q, rfl⟩ := θ.surjective r
      induction q using QuotientGroup.induction_on with
      | H h =>
        rw [ggLAut_apply, MulAut.one_apply]
        have hp := hρ (b * c⁻¹) h
        rw [hd, one_mul, inv_one, mul_one] at hp
        have hp' : ggQuotHom θ (H.normalizerMonoidHom ⟨(((b * c⁻¹ : ↥E) : G)),
            hEN (b * c⁻¹).2⟩ h) = ggQuotHom θ h := by
          apply (TableBSymp.spProjEquivSp (K := K) (m := m)).injective
          simpa [piMat] using hp
        rwa [ggQuotHom_apply, ggQuotHom_apply] at hp'
    have hcent : (((b * c⁻¹ : ↥E) : G)) ∈ Subgroup.centralizer (H : Set G) :=
      mem_centralizer_of_ggLAut_eq_one H θ hperf hLA
    have hmem : ((b * c⁻¹ : ↥E) : G) ∈ E ⊓ Subgroup.centralizer (H : Set G) :=
      ⟨(b * c⁻¹).2, hcent⟩
    rw [hdisc] at hmem
    have hbc1 : b * c⁻¹ = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
    calc b = b * c⁻¹ * c := by group
      _ = c := by rw [hbc1, one_mul]
  have hcardEr : Nat.card (ρ.range) = Nat.card ↥E := by
    let f : ↥E → ρ.range := fun b => ⟨ρ b, ⟨b, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · intro b c hbc
        exact hρinj (congrArg Subtype.val hbc)
      · rintro ⟨y, b, rfl⟩
        exact ⟨b, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have h3le : 3 ^ m ≤ Nat.card ↥E :=
    three_pow_le_card_E_holds θ hcardK hperf hE hEN hI hSC hdisc h33
  have hEab : IsElemAbelian 3 (ρ.range) := by
    constructor
    · constructor
      constructor
      intro x y
      rcases x with ⟨x, hx⟩
      rcases y with ⟨y, hy⟩
      rcases hx with ⟨a, rfl⟩
      rcases hy with ⟨b, rfl⟩
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul]
      congr 1
      exact hE.1.is_comm.comm a b
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have ha : a ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hE.2 (a : G) a.2
      rw [ha, map_one]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨ζ, hζw, hζconj⟩ :=
    exists_spPlaneConj (F := K) (p := 3) h2 Nat.prime_three (by norm_num)
  obtain ⟨c, hc⟩ := hζconj m ρ.range hEab (by rwa [hcardEr])
  let T : Subgroup ↥(StatedSp m K) := (spPlaneTorus m ζ).range
  have hcT : ρ.range.map (MulAut.conj c).toMonoidHom = T := hc
  have hcardT : Nat.card T = Nat.card (ρ.range) := by
    rw [← hcT]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (ρ.range)
      (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).toEquiv).symm
  have hcardD : Nat.card (Fin m → Multiplicative (ZMod 3)) = 3 ^ m := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    simp
  have hTLle : Nat.card T ≤ 3 ^ m := by
    have hsurj : Function.Surjective (fun u : Fin m → Multiplicative (ZMod 3) =>
        (⟨spPlaneTorus m ζ u, ⟨u, rfl⟩⟩ : T)) := by
      rintro ⟨y, u, rfl⟩
      exact ⟨u, rfl⟩
    have hle := Nat.card_le_card_of_surjective
      (fun u : Fin m → Multiplicative (ZMod 3) =>
        (⟨spPlaneTorus m ζ u, ⟨u, rfl⟩⟩ : T)) hsurj
    rwa [hcardD] at hle
  have hEub : Nat.card ↥E ≤ 3 ^ m := by
    rw [← hcardEr, ← hcardT]
    exact hTLle
  have hcardE : Nat.card ↥E = 3 ^ m := le_antisymm hEub h3le
  have hcardTeq : Nat.card T = 3 ^ m := by
    rw [hcardT, hcardEr, hcardE]
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hζne : ζ ≠ 1 := by
    intro hζ1
    have hTbot : T = ⊥ := by
      rw [show T = (spPlaneTorus m ζ).range from rfl, hζ1]
      ext x
      constructor
      · rintro ⟨u, hu⟩
        have hcomp : spPlaneTorus m (1 : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) =
            1 := by
          apply MonoidHom.pi_ext
          intro i x
          rw [spPlaneTorus_mulSingle]
          simp
        rw [hcomp, MonoidHom.one_apply] at hu
        exact Subgroup.mem_bot.mpr hu.symm
      · intro hx
        exact ⟨1, by simpa using (Subgroup.mem_bot.mp hx).symm⟩
    have hT1 : Nat.card T = 1 := by rw [hTbot]; simp
    have h3m1 : 3 ^ m = 1 := by rw [← hcardTeq, hT1]
    have hge : 3 ≤ 3 ^ m := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    omega
  have hζinj : Function.Injective ζ := by
    have hprimeD : Nat.Prime (Nat.card (Multiplicative (ZMod 3))) := by
      simpa using Nat.prime_three
    haveI : Fact (Nat.Prime (Nat.card (Multiplicative (ZMod 3)))) := ⟨hprimeD⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (MonoidHom.ker ζ) with hbot | htop
    · rw [MonoidHom.ker_eq_bot_iff] at hbot
      exact hbot
    · exfalso
      have hζ1 : ζ = 1 := by
        apply MonoidHom.ext
        intro a
        have ha : a ∈ (MonoidHom.ker ζ) := by
          rw [htop]
          exact Subgroup.mem_top a
        simpa [MonoidHom.mem_ker] using ha
      exact hζne hζ1
  let fT : (Fin m → Multiplicative (ZMod 3)) →* T :=
    { toFun := fun u => ⟨spPlaneTorus m ζ u, ⟨u, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro u v; apply Subtype.ext; simp }
  have hsurjT : Function.Surjective fT := by
    rintro ⟨y, u, rfl⟩
    exact ⟨u, rfl⟩
  have hspInj : Function.Injective (spPlaneTorus m ζ) := by
    intro a b hab
    have hbij : Function.Bijective fT :=
      (Nat.bijective_iff_surjective_and_card fT).2
        ⟨hsurjT, by rw [hcardD, hcardTeq]⟩
    exact hbij.1 (Subtype.ext hab)
  have hfT : Function.Bijective fT :=
    ⟨fun u v huv => hspInj (congrArg Subtype.val huv), hsurjT⟩
  let eT : (Fin m → Multiplicative (ZMod 3)) ≃* T := MulEquiv.ofBijective fT hfT
  let eC' : ρ.range ≃* ρ.range.map (MulAut.conj c).toMonoidHom :=
    Subgroup.equivMapOfInjective (ρ.range) (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective
  let eC : ρ.range ≃* T := eC'.trans (MulEquiv.subgroupCongr hcT)
  let fE : ↥E →* ρ.range :=
    { toFun := fun b => ⟨ρ b, ⟨b, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp }
  have hfE : Function.Bijective fE := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact hρinj (congrArg Subtype.val hab)
    · rintro ⟨y, b, rfl⟩
      exact ⟨b, rfl⟩
  let eρ : ↥E ≃* ρ.range := MulEquiv.ofBijective fE hfE
  let τ : (Fin m → Multiplicative (ZMod 3)) ≃* ↥E :=
    eT.trans (eC.symm.trans eρ.symm)
  have heC_apply : ∀ x : ρ.range,
      (((eC x : T)) : ↥(StatedSp m K)) = (MulAut.conj c) x := by
    intro x
    rfl
  have htau : ∀ u : Fin m → Multiplicative (ZMod 3),
      (MulAut.conj c) (ρ (τ u)) = spPlaneTorus m ζ u := by
    intro u
    have h1 : (eρ (τ u) : ρ.range) = eC.symm (eT u) := by
      simp [τ]
    have h2 : ((eρ (τ u) : ρ.range) : ↥(StatedSp m K)) = ρ (τ u) := rfl
    have happ := heC_apply (eC.symm (eT u))
    rw [MulEquiv.apply_symm_apply] at happ
    calc (MulAut.conj c) (ρ (τ u))
        = (MulAut.conj c) ((eC.symm (eT u) : ρ.range) : ↥(StatedSp m K)) := by rw [← h2, h1]
      _ = spPlaneTorus m ζ u := happ.symm
  let π : ↥H →* ↥(StatedSp m K) := (MulAut.conj c).toMonoidHom.comp (piMat θ)
  have hπsurj : Function.Surjective π :=
    (MulAut.conj c).surjective.comp (piMat_surjective_holds θ)
  have hπker_eq : π.ker = Subgroup.center ↥H := by
    ext h
    change (MulAut.conj c) ((piMat θ) h) = 1 ↔ h ∈ Subgroup.center ↥H
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_piMat_holds θ]
  have hπker : π.ker ≤ Subgroup.center ↥H := le_of_eq hπker_eq
  refine ⟨ζ, hζinj, hcardE, ⟨{
    π := π
    surj := hπsurj
    ker_le := hπker
    τ := τ
    intertwine := ?_ }⟩⟩
  intro u h
  have hb : (MulAut.conj c) (ρ (τ u)) = spPlaneTorus m ζ u := htau u
  calc
    π (H.normalizerMonoidHom ⟨((τ u : ↥E) : G), hEN (τ u).2⟩ h)
        = (MulAut.conj c) (piMat θ (H.normalizerMonoidHom ⟨((τ u : ↥E) : G),
            hEN (τ u).2⟩ h)) := rfl
    _ = (MulAut.conj c) (ρ (τ u) * piMat θ h * (ρ (τ u))⁻¹) := by rw [hρ]
    _ = (MulAut.conj c) (ρ (τ u)) * (MulAut.conj c) (piMat θ h) *
          ((MulAut.conj c) (ρ (τ u)))⁻¹ := by simp only [map_mul, map_inv]
    _ = spPlaneTorus m ζ u * π h * (spPlaneTorus m ζ u)⁻¹ := by rw [hb]; rfl

end

end CFSG.StandardType.GGQ2Frame.SpPlacement
