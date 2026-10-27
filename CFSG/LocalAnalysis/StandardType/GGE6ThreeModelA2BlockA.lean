module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelA2BlockB
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelA2BlockC

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.E6 CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.Quasithin.F134.LieOdd
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three
open scoped MatrixGroups
open Matrix


section Helpers

private theorem frobE6_rootDiagUnit {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}
    (b : Fin Tag.E6.rank → Ωˣ) :
    frobE6 Fr (rootDiagUnit Tag.E6 b) =
      rootDiagUnit Tag.E6 (fun i => Units.map Fr.toMonoidHom (b i)) := by
  refine Units.ext ?_
  change entrywise Fr (rootDiag b) =
    rootDiag (fun i => Units.map Fr.toMonoidHom (b i))
  rw [CFSG.LieType.Chevalley.entrywise_rootDiag]

private theorem frobE6_eq_of_mem_torusGroup_pow_three {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}
    {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q - 1)
    {u : ModGL Tag.E6 Ω} (hu : u ∈ torusGroup Tag.E6 Ω) (hu3 : u ^ 3 = 1) :
    frobE6 Fr u = u := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  have hb3 : b ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 1 := by
      rw [← rootDiagUnit_pow, hu3, rootDiagUnit_one]
    exact DiagTorus.rootDiagUnit_injective h1
  rw [frobE6_rootDiagUnit]
  congr 1
  funext i
  refine Units.ext ?_
  rw [Units.coe_map]
  change Fr ↑(b i) = ↑(b i)
  rw [hFr]
  have hbi : (b i : Ω) ^ 3 = 1 := by
    have h' : (b i) ^ 3 = 1 := by simpa using congrFun hb3 i
    rw [← Units.val_pow_eq_pow_val, h', Units.val_one]
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : (0 : Ω) = 0 ^ q := (map_zero Fr).symm.trans (hFr 0)
    rw [h, pow_zero] at h1
    exact zero_ne_one h1
  obtain ⟨m, hm⟩ := h3
  have hqeq : q = 3 * m + 1 := by omega
  calc (b i : Ω) ^ q = (b i) ^ (3 * m + 1) := by rw [hqeq]
    _ = (b i) ^ (3 * m) * (b i) := by rw [pow_succ]
    _ = ((b i) ^ 3) ^ m * (b i) := by rw [pow_mul]
    _ = (1 : Ω) ^ m * (b i) := by rw [hbi]
    _ = (b i : Ω) := by rw [one_pow, one_mul]

private theorem diagSL3_pow {Ω : Type} [Field Ω] (d : Fin 3 → Ωˣ)
    (hd : (d 0 : Ω) * d 1 * d 2 = 1) (n : ℕ) :
    diagSL3 d hd ^ n = diagSL3 (d ^ n)
      (by
        simp only [Pi.pow_apply, Units.val_pow_eq_pow_val]
        rw [← mul_pow, ← mul_pow, hd, one_pow]) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL3, coe_diagSL3, Matrix.diagonal_pow]
  congr 1

private theorem frobE6_pinnedX {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}
    (γ : Fin Tag.E6.rank → ℤ) (c : Ω) :
    frobE6 Fr (pinnedX Tag.E6 Ω γ c) = pinnedX Tag.E6 Ω γ (Fr c) := by
  refine Units.ext ?_
  change entrywiseHom Fr (pinnedX Tag.E6 Ω γ c : Module.End Ω (RootModule Tag.E6 Ω)) =
    (pinnedX Tag.E6 Ω γ (Fr c) : Module.End Ω (RootModule Tag.E6 Ω))
  exact entrywise_pinnedX Fr γ c

private theorem frobE6_mem_rootSpan {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}
    {S : Set (Fin Tag.E6.rank → ℤ)} {u : ModGL Tag.E6 Ω}
    (hu : u ∈ rootSpan Tag.E6 Ω S) :
    frobE6 Fr u ∈ rootSpan Tag.E6 Ω S := by
  rw [rootSpan_eq_closure] at hu ⊢
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨γ, hγ, c, rfl⟩ := hx
      rw [frobE6_pinnedX]
      exact Subgroup.subset_closure ⟨γ, hγ, Fr c, rfl⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

end Helpers

theorem a2BlockSplitInput_holds :
    ∀ {Ω : Type} [Field Ω] [IsAlgClosed Ω] {Fr : Ω →+* Ω} {q : ℕ}
      (_hFr : ∀ c, Fr c = c ^ q) (_hq : (q : Ω) = 0) (_h3 : 3 ∣ q - 1)
      {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (_hζo : orderOf ζ = 3)
      {E : Subgroup (ModGL Tag.E6 Ω)} (_hE : CFSG.Open.IsElemAbelian 3 E)
      (_hEF : ∀ e ∈ E, frobE6 Fr e = e)
      (_hEX : E ≤ xHat Tag.E6 Ω (Subgroup.zpowers (gE6 2))),
      ∃ z ∈ rootSpan Tag.E6 Ω (a2Roots (a2PairE6 2).1 (a2PairE6 2).2), frobE6 Fr z = z ∧
        ∀ e ∈ E, ∃ v, z * e * z⁻¹ = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
  intro Ω _ _ Fr q hFr hq h3 ζ hζ hζo E hE hEF hEX
  classical
  obtain ⟨ρ, σ, hfr, h01, h12⟩ := exists_frame_a2PairE6 Ω 2
  have hroots : a2Roots (σ 0 1) (σ 1 2) =
      a2Roots (a2PairE6 2).1 (a2PairE6 2).2 := by rw [h01, h12]
  have hpair : pairRefl ((σ 0 1), (σ 1 2)) = gE6 2 := by
    rw [h01, h12]
    exact pairRefl_a2PairE6 2
  have hEM : E ≤ monoHat Tag.E6 Ω := hEX.trans (xHat_le_monoHat _)
  set ψE : E →* WeylGroup Tag.E6 := (psiHat Tag.E6 Ω).comp (Subgroup.inclusion hEM) with hψE
  have hψS : ∀ e : E, ψE e ∈ Subgroup.zpowers (gE6 2) := fun e =>
    (mem_xHat.1 (hEX e.2)).2
  by_cases hbot : ψE.range = ⊥
  ·
    refine ⟨1, Subgroup.one_mem _, map_one (frobE6 Fr), ?_⟩
    intro e he
    have hmem : ψE ⟨e, he⟩ ∈ ψE.range := ⟨⟨e, he⟩, rfl⟩
    rw [hbot] at hmem
    have h1 : psiHat Tag.E6 Ω ⟨e, hEM he⟩ = 1 := Subgroup.mem_bot.1 hmem
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one h1
    have hb' : e = rootDiagUnit Tag.E6 b := hb
    have hb3 : b ^ 3 = 1 := by
      have hb1 : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 1 := by
        rw [← rootDiagUnit_pow, ← hb', hE.2 e he, rootDiagUnit_one]
      exact DiagTorus.rootDiagUnit_injective hb1
    obtain ⟨v, hv⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ hb3
    have hvb : b = zetaVec ζ hζ v := hv.symm
    exact ⟨v, by rw [hb', hvb, one_mul, inv_one, mul_one]⟩
  ·
    have hg2o : orderOf (gE6 2) = 3 :=
      orderOf_eq_prime (gE6_pow_three 2) (by
        intro h
        have := (testE6_move 2).1
        rw [h] at this
        exact this rfl)
    have hcard3 : Nat.card (Subgroup.zpowers (gE6 2)) = 3 := by
      rw [Nat.card_zpowers, hg2o]
    have hle : ψE.range ≤ Subgroup.zpowers (gE6 2) := by
      rintro _ ⟨e, rfl⟩
      exact hψS e
    have hdvd : Nat.card ψE.range ∣ 3 := by
      rw [← hcard3]
      exact Subgroup.card_dvd_of_le hle
    have hcardne : Nat.card ψE.range ≠ 1 := by
      intro h1
      apply hbot
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxle : Subgroup.zpowers x ≤ ψE.range := Subgroup.zpowers_le.mpr hx
      have hdvd1 : Nat.card (Subgroup.zpowers x) ∣ 1 := by
        rw [← h1]
        exact Subgroup.card_dvd_of_le hxle
      have hx1 : Nat.card (Subgroup.zpowers x) = 1 := Nat.dvd_one.1 hdvd1
      rw [Nat.card_zpowers] at hx1
      exact orderOf_eq_one_iff.1 hx1
    have hcard : Nat.card ψE.range = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd h hcardne
      · exact h
    have heq : ψE.range = Subgroup.zpowers (gE6 2) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcard3])
    have hg2 : gE6 2 ∈ ψE.range := heq ▸ Subgroup.mem_zpowers _
    obtain ⟨⟨x, hxE⟩, hxψ⟩ := hg2
    set m : ModGL Tag.E6 Ω := ρ coxSL3 with hm
    have hmMon : m ∈ monomialSubgroup Tag.E6 Ω := by
      rw [hm, show coxSL3 = wSL3 0 1 (by decide) * wSL3 1 2 (by decide) from rfl, map_mul]
      exact mul_mem (frame_wSL3 hfr 0 1 (by decide)).1
        (frame_wSL3 hfr 1 2 (by decide)).1
    have hmHat : m ∈ monoHat Tag.E6 Ω := monomial_le_monoHat hmMon
    have hmaps : MapsRootLines (m : (Module.End Ω (RootModule Tag.E6 Ω))ˣ)
        (pairRefl ((σ 0 1), (σ 1 2))) := by
      rw [hm, show coxSL3 = wSL3 0 1 (by decide) * wSL3 1 2 (by decide) from rfl, map_mul]
      have h0 : MapsRootLines (ρ (wSL3 0 1 (by decide))) (rootReflection (σ 0 1)) := by
        obtain ⟨hm0, hq0⟩ := frame_wSL3 hfr 0 1 (by decide)
        rw [← hq0]
        exact mapsRootLines_weylQuotientHom (τ := Tag.E6) (R := Ω) ⟨_, hm0⟩
      have h1 : MapsRootLines (ρ (wSL3 1 2 (by decide))) (rootReflection (σ 1 2)) := by
        obtain ⟨hm1, hq1⟩ := frame_wSL3 hfr 1 2 (by decide)
        rw [← hq1]
        exact mapsRootLines_weylQuotientHom (τ := Tag.E6) (R := Ω) ⟨_, hm1⟩
      exact h0.mul h1
    have hmψ : psiHat Tag.E6 Ω ⟨m, hmHat⟩ = gE6 2 := by
      rw [psiHat_eq hmaps, hpair]
    have hxHat : x ∈ monoHat Tag.E6 Ω := hEM hxE
    have hxψ' : psiHat Tag.E6 Ω ⟨x, hxHat⟩ = gE6 2 := hxψ
    have hker : psiHat Tag.E6 Ω ⟨x * m⁻¹,
        mul_mem hxHat (inv_mem hmHat)⟩ = 1 := by
      have hsub : (⟨x * m⁻¹, mul_mem hxHat (inv_mem hmHat)⟩ : monoHat Tag.E6 Ω) =
          ⟨x, hxHat⟩ * (⟨m, hmHat⟩ : monoHat Tag.E6 Ω)⁻¹ := Subtype.ext rfl
      rw [hsub, map_mul, map_inv, hxψ', hmψ, mul_inv_cancel]
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one hker
    set t : ModGL Tag.E6 Ω := m⁻¹ * rootDiagUnit Tag.E6 b * m with htdef
    have htT : t ∈ torusGroup Tag.E6 Ω := by
      rw [htdef]
      have hmapsinv : MapsRootLines
          ((m⁻¹ : ModGL Tag.E6 Ω) : (Module.End Ω (RootModule Tag.E6 Ω))ˣ)
          (gE6 2)⁻¹ := by
        simpa [hpair] using hmaps.inv
      have h := monomial_conj_rootDiagUnit_weylTuple (x := m⁻¹) (inv_mem hmMon) hmapsinv
      rw [show (m⁻¹)⁻¹ = m by rw [inv_inv]] at h
      rw [h]
      exact rootDiagUnit_mem_torusGroup _
    have hxt : x = m * t := by
      rw [htdef]
      have hb' : x * m⁻¹ = rootDiagUnit Tag.E6 b := hb
      calc x = x * m⁻¹ * m := by group
        _ = rootDiagUnit Tag.E6 b * m := by rw [hb']
        _ = m * (m⁻¹ * rootDiagUnit Tag.E6 b * m) := by group
    have hq0 : q ≠ 0 := by
      intro h
      have h1 : (0 : Ω) = 0 ^ q := (map_zero Fr).symm.trans (hFr 0)
      rw [h, pow_zero] at h1
      exact zero_ne_one h1
    have h3ne : (3 : Ω) ≠ 0 := by
      intro h30
      have hchar : ringChar Ω = 3 := by
        have hdvd : ringChar Ω ∣ 3 :=
          (CharP.cast_eq_zero_iff Ω (ringChar Ω) 3).mp (by exact_mod_cast h30)
        rcases CharP.char_is_prime_or_zero Ω (ringChar Ω) with hp | hp
        · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
        · rw [hp] at hdvd
          exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by norm_num)
      have h3q : 3 ∣ q := by
        rw [← hchar]
        exact (CharP.cast_eq_zero_iff Ω (ringChar Ω) q).mp hq
      obtain ⟨m', hm'⟩ := h3
      obtain ⟨k, hk⟩ := h3q
      omega
    obtain ⟨d, hddet, hddist, y, t₁, hyQ, ht₁T, ht₁c, hblock⟩ :=
      exists_block_conj_diag (Ω := Ω) h3ne hfr (t := t) htT
    set h : ModGL Tag.E6 Ω := ρ (diagSL3 d hddet) with hh
    have hT : h ∈ torusGroup Tag.E6 Ω := hfr.diag _ (fun i j hij => by
      simp [coe_diagSL3, hij])
    have hxy : y * x * y⁻¹ = h * t₁ := by
      rw [hxt, hh]
      exact hblock
    have hhtT : h * t₁ ∈ torusGroup Tag.E6 Ω := mul_mem hT ht₁T
    have hht3 : (h * t₁) ^ 3 = 1 := by
      rw [← hxy]
      have h := conj_pow (a := y) (b := x) (i := 3)
      rw [h, hE.2 x hxE]
      group
    have hFh : frobE6 Fr (h * t₁) = h * t₁ :=
      frobE6_eq_of_mem_torusGroup_pow_three hFr h3 hhtT hht3
    have hcent : ∀ (e : ModGL Tag.E6 Ω) (he : e ∈ E),
        psiHat Tag.E6 Ω ⟨e, hEM he⟩ = 1 → y * e * y⁻¹ = e := by
      intro e he he1
      have heM : e ∈ monoHat Tag.E6 Ω := hEM he
      have h1 : psiHat Tag.E6 Ω ⟨e, heM⟩ = 1 := he1
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one h1
      have hb' : e = rootDiagUnit Tag.E6 b := hb
      have hb3 : b ^ 3 = 1 := by
        have hb1 : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 1 := by
          rw [← rootDiagUnit_pow, ← hb', hE.2 e he, rootDiagUnit_one]
        exact DiagTorus.rootDiagUnit_injective hb1
      have hcomm : x * rootDiagUnit Tag.E6 b * x⁻¹ = rootDiagUnit Tag.E6 b := by
        have hc := TableB.IsElemAbelian.comm hE hxE he
        have hc' : x * e = e * x := hc
        rw [hb'] at hc'
        rw [hc', mul_inv_cancel_right]
      have hweyl : weylTuple (gE6 2) b = b := by
        have hc := conj_rootDiagUnit_of_mem_monoHat (⟨x, hxHat⟩ : monoHat Tag.E6 Ω) b
        rw [hxψ'] at hc
        exact DiagTorus.rootDiagUnit_injective (hc.symm.trans hcomm)
      obtain ⟨v, hv⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ hb3
      have hvb : b = zetaVec ζ hζ v := hv.symm
      have hweyl' : weylTuple (gE6 2) (zetaVec ζ hζ v) = zetaVec ζ hζ v := by
        rw [← hvb]
        exact hweyl
      have hvad : adAct .E6 3 (gE6 2) v = v := by
        apply TableBExc.E6Three.zetaVec_injective hζo hζ
        rw [← TableBExc.E6Three.weylTuple_zetaVec]
        exact hweyl'
      have hyc := blockGroup_comm_rootDiagUnit_zetaVec hζo hζ 2 v hvad y (hroots ▸ hyQ)
      rw [hb', hvb]
      rw [hyc]
      group
    have hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ torusGroup Tag.E6 Ω := by
      intro e he
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hψS ⟨e, he⟩)
      have hψk : ψE ⟨e, he⟩ = (gE6 2) ^ k := hk.symm
      have hxψE : ψE ⟨x, hxE⟩ = gE6 2 := hxψ
      have hker0 : ψE (⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k)) = 1 := by
        rw [map_mul, map_zpow, hψk, hxψE]
        group
      let eH : monoHat Tag.E6 Ω :=
        ⟨((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω),
          hEM (⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E).2⟩
      have hker : psiHat Tag.E6 Ω eH = 1 := by
        change ψE (⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k)) = 1
        exact hker0
      have heH : ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) ∈
          torusGroup Tag.E6 Ω := by
        obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one hker
        rw [show ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) =
            (eH : ModGL Tag.E6 Ω) from rfl]
        rw [hb]
        exact rootDiagUnit_mem_torusGroup _
      have hcentE : y * ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) * y⁻¹ =
          ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) :=
        hcent _ ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E)).2 hker
      have heq : e = ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) * x ^ k := by
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
        group
      rw [heq]
      have hxpow : y * x ^ k * y⁻¹ = (h * t₁) ^ k := by
        rw [show y * x ^ k * y⁻¹ = (MulAut.conj y) (x ^ k) from rfl, map_zpow]
        change (y * x * y⁻¹) ^ k = (h * t₁) ^ k
        rw [hxy]
      have hEq : y * (((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) * x ^ k) * y⁻¹ =
          ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) * ((h * t₁) ^ k) := by
        calc y * (((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) * x ^ k) * y⁻¹
            = (y * ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) * y⁻¹) *
                (y * x ^ k * y⁻¹) := by group
          _ = ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) * ((h * t₁) ^ k) := by
                rw [hcentE, hxpow]
      rw [hEq]
      exact mul_mem heH (zpow_mem hhtT k)
    set u : ModGL Tag.E6 Ω := frobE6 Fr y * y⁻¹ with hu
    have huQ : u ∈ rootSpan Tag.E6 Ω (a2Roots (σ 0 1) (σ 1 2)) :=
      mul_mem (frobE6_mem_rootSpan hyQ) (inv_mem hyQ)
    have hucommH : u * (h * t₁) = (h * t₁) * u := by
      have h1 : u * (h * t₁) * u⁻¹ = h * t₁ := by
        rw [hu]
        calc frobE6 Fr y * y⁻¹ * (h * t₁) * (frobE6 Fr y * y⁻¹)⁻¹
            = frobE6 Fr y * (y⁻¹ * (h * t₁) * y) * (frobE6 Fr y)⁻¹ := by group
          _ = frobE6 Fr y * x * (frobE6 Fr y)⁻¹ := by
                rw [← hxy]; group
          _ = frobE6 Fr (y * x * y⁻¹) := by
                conv_rhs => rw [map_mul, map_mul, map_inv]
                rw [hEF x hxE]
          _ = frobE6 Fr (h * t₁) := by rw [hxy]
          _ = h * t₁ := hFh
      calc u * (h * t₁) = (u * (h * t₁) * u⁻¹) * u := by group
        _ = (h * t₁) * u := by rw [h1]
    have hucomm : u * h = h * u := by
      obtain ⟨A, hA⟩ := (rootSpan_a2Roots_eq_range hfr) ▸ huQ
      rw [← hA]
      have hucommH' : ρ A * (h * t₁) = (h * t₁) * ρ A := by
        rw [hA]; exact hucommH
      have ht₁u : t₁ * ρ A = ρ A * t₁ := ht₁c A
      calc ρ A * h = ρ A * (h * t₁) * t₁⁻¹ := by group
        _ = (h * t₁) * ρ A * t₁⁻¹ := by rw [hucommH']
        _ = h * (t₁ * ρ A) * t₁⁻¹ := by group
        _ = h * (ρ A * t₁) * t₁⁻¹ := by rw [ht₁u]
        _ = h * ρ A := by group
    obtain ⟨d', hd'det, hu_eq⟩ :=
      commute_diagSL3_mem_range (ρ := ρ) (σ := σ) hfr hddet hddist huQ
        (by simpa only [hh] using hucomm)
    have hq1 : q ≠ 1 := by
      intro h
      have hcast : (1 : Ω) = (q : Ω) := by simp [h]
      exact one_ne_zero (hcast.trans hq)
    have hm : q - 1 ≠ 0 := by omega
    have hqeq : q = (q - 1) + 1 := by omega
    have hd'prod : ((fun i => (d' i)⁻¹) 0 : Ω) * (fun i => (d' i)⁻¹) 1 *
        (fun i => (d' i)⁻¹) 2 = 1 := by
      simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
      calc ((d' 0 : Ω))⁻¹ * ((d' 1 : Ω))⁻¹ * ((d' 2 : Ω))⁻¹ =
          (((d' 0 : Ω) * d' 1 * d' 2))⁻¹ := by rw [mul_inv, mul_inv]
        _ = 1 := by rw [hd'det, inv_one]
    obtain ⟨s, hs, hspow⟩ :=
      exists_diagSL3_pow (fun i => (d' i)⁻¹) hd'prod (m := q - 1) hm
    set sρ : ModGL Tag.E6 Ω := ρ (diagSL3 s hs) with hsρdef
    have hsρT : sρ ∈ torusGroup Tag.E6 Ω := by
      rw [hsρdef]
      exact hfr.diag _ (fun i j hij => by simp [coe_diagSL3, hij])
    have hmat : (diagSL3 s hs) ^ (q - 1) = (diagSL3 d' hd'det)⁻¹ := by
      rw [diagSL3_pow, diagSL3_inv]
      refine Subtype.ext ?_
      rw [coe_diagSL3, coe_diagSL3]
      simp only [Pi.pow_apply]
      congr 1
      funext i
      rw [hspow i]
    have hsu : sρ ^ (q - 1) = u⁻¹ := by
      rw [hsρdef, ← map_pow, hmat, hu_eq, ← map_inv]
    have hFy : frobE6 Fr y = u * y := by rw [hu]; group
    have h1 : frobE6 Fr sρ = sρ * u⁻¹ := by
      have hFq : frobE6 Fr sρ = sρ ^ q := by
        rw [hsρdef]
        exact frobE6_rho_diagSL3 hfr hFr hs
      rw [hFq, hqeq, pow_succ', hsu]
    refine ⟨sρ * y, ?_, ?_, ?_⟩
    · rw [← hroots]
      exact mul_mem ((rootSpan_a2Roots_eq_range hfr).symm ▸ ⟨diagSL3 s hs, rfl⟩) hyQ
    · rw [map_mul, h1, hFy]
      group
    · intro e he
      have hmemH : sρ * (y * e * y⁻¹) * sρ⁻¹ ∈ torusGroup Tag.E6 Ω :=
        mul_mem (mul_mem hsρT (hyE e he)) (inv_mem hsρT)
      have hze : sρ * y * e * (sρ * y)⁻¹ = sρ * (y * e * y⁻¹) * sρ⁻¹ := by group
      rw [hze]
      have h3' : (sρ * (y * e * y⁻¹) * sρ⁻¹) ^ 3 = 1 := by
        have h1 : (sρ * (y * e * y⁻¹) * sρ⁻¹) ^ 3 =
            sρ * (y * e * y⁻¹) ^ 3 * sρ⁻¹ := conj_pow (a := sρ) (b := y * e * y⁻¹) (i := 3)
        rw [h1]
        have h2 : (y * e * y⁻¹) ^ 3 = 1 := by
          rw [conj_pow (a := y) (b := e) (i := 3), hE.2 e he]
          group
        rw [h2, mul_one, mul_inv_cancel]
      exact exists_zetaVec_eq_of_mem_torusGroup_pow_three hζ hζo hmemH h3'

end CFSG.StandardType.E6ThreeModel
