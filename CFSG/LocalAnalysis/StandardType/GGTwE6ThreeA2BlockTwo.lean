module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockTwoCore

public noncomputable section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.E6 CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.Quasithin.F134.LieOdd
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2
open scoped MatrixGroups
open Matrix


theorem a2BlockTwoInput_holds : A2BlockTwoInput := by
  intro Ω _ _ Fr q hFr hq h3 ζ hζ hζo E hE hEθ hEX
  classical
  obtain ⟨ρ, σ, hfr, h01, h12⟩ := exists_frame_a2PairE6 Ω 2
  have hpair : pairRefl ((σ 0 1), (σ 1 2)) = gE6 2 := by
    rw [h01, h12]
    exact pairRefl_a2PairE6 2
  have hEM : E ≤ monoHat Tag.E6 Ω := hEX.trans (xHat_le_monoHat _)
  set ψE : E →* WeylGroup Tag.E6 := (psiHat Tag.E6 Ω).comp (Subgroup.inclusion hEM) with hψE
  have hψS : ∀ e : E, ψE e ∈ Subgroup.zpowers (gE6 2) := fun e =>
    (mem_xHat.1 (hEX e.2)).2
  by_cases hbot : ψE.range = ⊥
  · refine exists_thetaFixed_conj_of_kernel hFr hq h3 hζ hζo 2 hE hEθ hEX ?_
    intro e he _
    have hmem : ψE ⟨e, he⟩ ∈ ψE.range := ⟨⟨e, he⟩, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
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
    have hθh : TwistedDiag.theta Fr (h * t₁) = h * t₁ :=
      theta_eq_of_mem_torusGroup_pow_three hFr h3 hhtT hht3
    have hcent : ∀ (e : ModGL Tag.E6 Ω) (he : e ∈ E),
        psiHat Tag.E6 Ω ⟨e, hEM he⟩ = 1 → y * e * y⁻¹ = e := by
      intro e he he1
      have heM : e ∈ monoHat Tag.E6 Ω := hEM he
      have h1 : psiHat Tag.E6 Ω ⟨e, heM⟩ = 1 := he1
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one h1
      have hb3 : b ^ 3 = 1 := by
        have hb1 : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 1 := by
          rw [← rootDiagUnit_pow, ← hb, hE.2 e he, rootDiagUnit_one]
        exact DiagTorus.rootDiagUnit_injective hb1
      have hcomm : x * rootDiagUnit Tag.E6 b * x⁻¹ = rootDiagUnit Tag.E6 b := by
        have hc := TableB.IsElemAbelian.comm hE hxE he
        have hc' : x * ((⟨e, heM⟩ : monoHat Tag.E6 Ω) : ModGL Tag.E6 Ω) =
            ((⟨e, heM⟩ : monoHat Tag.E6 Ω) : ModGL Tag.E6 Ω) * x := hc
        rw [hb] at hc'
        rw [hc', mul_inv_cancel_right]
      have hweyl : weylTuple (gE6 2) b = b := by
        have hc := conj_rootDiagUnit_of_mem_monoHat (⟨x, hxHat⟩ : monoHat Tag.E6 Ω) b
        rw [hxψ'] at hc
        exact DiagTorus.rootDiagUnit_injective (hc.symm.trans hcomm)
      obtain ⟨v, rfl⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ hb3
      have hv : adAct .E6 3 (gE6 2) v = v := by
        have h2 : TableBExc.E6Three.zetaVec ζ hζ (adAct .E6 3 (gE6 2) v) =
            TableBExc.E6Three.zetaVec ζ hζ v := by
          rw [← TableBExc.E6Three.weylTuple_zetaVec]
          exact hweyl
        exact TableBExc.E6Three.zetaVec_injective hζo hζ h2
      have hform := (adAct_gE6_eq_iff 2 v).1 hv
      have hα : rootChar (TableBExc.E6Three.zetaVec ζ hζ v) (a2PairE6 2).1 = 1 :=
        (rootChar_zetaVec_eq_one_iff hζo hζ v _).2 hform.1
      have hβ : rootChar (TableBExc.E6Three.zetaVec ζ hζ v) (a2PairE6 2).2 = 1 :=
        (rootChar_zetaVec_eq_one_iff hζo hζ v _).2 hform.2
      have hα' : rootChar (TableBExc.E6Three.zetaVec ζ hζ v) (σ 0 1) = 1 := by
        rw [h01]; exact hα
      have hβ' : rootChar (TableBExc.E6Three.zetaVec ζ hζ v) (σ 1 2) = 1 := by
        rw [h12]; exact hβ
      have h0 : σ 0 0 = 0 := by
        have h := hfr.eq_sub 0 0
        rw [sub_self] at h
        exact h
      have h1 : σ 1 0 = -σ 0 1 := by
        have h := hfr.neg 1 0
        rw [h, neg_neg]
      have h2 : σ 2 0 = -(σ 0 1 + σ 1 2) := by
        have h := hfr.add 2 1 0
        have h21 : σ 2 1 = -σ 1 2 := by
          have h := hfr.neg 2 1
          rw [h, neg_neg]
        rw [h21, h1] at h
        calc σ 2 0 = -σ 1 2 + -σ 0 1 := h.symm
          _ = -(σ 0 1 + σ 1 2) := by abel
      have hdd : (fun i => rootChar (TableBExc.E6Three.zetaVec ζ hζ v) (σ i 0)) = 1 := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
        rcases hi with rfl | rfl | rfl
        · simp only [h0, rootChar_zero, Pi.one_apply]
        · simp only [h1, rootChar_neg' (b := TableBExc.E6Three.zetaVec ζ hζ v) (x := σ 0 1), hα', inv_one, Pi.one_apply]
        · simp only [h2, rootChar_neg' (b := TableBExc.E6Three.zetaVec ζ hζ v) (x := σ 0 1 + σ 1 2), rootChar_add, hα', hβ', one_mul, inv_one, Pi.one_apply]
      obtain ⟨A, rfl⟩ := (rootSpan_a2Roots_eq_range hfr) ▸ hyQ
      have hconj := hfr.torus (TableBExc.E6Three.zetaVec ζ hζ v) A
      rw [hdd] at hconj
      have hconj1 : conjDiag3 (1 : Fin 3 → Ωˣ) A = A := by
        apply Subtype.ext
        rw [coe_conjDiag3]
        simp [diagGL3]
      rw [hconj1] at hconj
      change ρ A * ((⟨e, heM⟩ : monoHat Tag.E6 Ω) : ModGL Tag.E6 Ω) * (ρ A)⁻¹ =
        ((⟨e, heM⟩ : monoHat Tag.E6 Ω) : ModGL Tag.E6 Ω)
      rw [hb]
      have hcomm' : ρ A * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) =
          rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * ρ A := by
        calc ρ A * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) =
            (rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * ρ A *
              (rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v))⁻¹) *
                rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) := by rw [hconj]
          _ = rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * ρ A := by group
      calc ρ A * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * (ρ A)⁻¹ =
          rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * ρ A * (ρ A)⁻¹ := by
            rw [hcomm']
        _ = rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) := by group
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
        rw [show ((⟨e, he⟩ * ⟨x, hxE⟩ ^ (-k) : E) : ModGL Tag.E6 Ω) = (eH : ModGL Tag.E6 Ω) from rfl]
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
    set u : ModGL Tag.E6 Ω := TwistedDiag.theta Fr y * y⁻¹ with hu
    have huQ : u ∈ rootSpan Tag.E6 Ω (a2Roots (σ 0 1) (σ 1 2)) := by
      have hqpos : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · subst h; obtain ⟨m, hm⟩ := h3; omega
        · exact h
      have hmap := theta_rootSpan_a2PairE6_two hFr (by
        intro c
        obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hqpos
        exact ⟨d, by rw [hFr, hd]⟩)
      have hset : a2Roots (a2PairE6 2).1 (a2PairE6 2).2 =
          a2Roots (σ 0 1) (σ 1 2) := by rw [h01, h12]
      rw [hset] at hmap
      have hy' : TwistedDiag.theta Fr y ∈ rootSpan Tag.E6 Ω
          (a2Roots (σ 0 1) (σ 1 2)) := hmap ▸ ⟨y, hyQ, rfl⟩
      exact mul_mem hy' (inv_mem hyQ)
    have hucommH : u * (h * t₁) = (h * t₁) * u := by
      have h1 : u * (h * t₁) * u⁻¹ = h * t₁ := by
        rw [hu]
        calc TwistedDiag.theta Fr y * y⁻¹ * (h * t₁) *
              (TwistedDiag.theta Fr y * y⁻¹)⁻¹
            = TwistedDiag.theta Fr y * (y⁻¹ * (h * t₁) * y) *
                (TwistedDiag.theta Fr y)⁻¹ := by group
          _ = TwistedDiag.theta Fr y * x * (TwistedDiag.theta Fr y)⁻¹ := by
                rw [← hxy]; group
          _ = TwistedDiag.theta Fr (y * x * y⁻¹) := by
                conv_rhs => rw [map_mul, map_mul, map_inv]
                rw [(hEθ hxE).2]
                rfl
          _ = TwistedDiag.theta Fr (h * t₁) := by rw [hxy]
          _ = h * t₁ := hθh
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
    have huT : u ∈ torusGroup Tag.E6 Ω :=
      mem_torusGroup_of_mem_rootSpan_commute_diag hfr hddet hddist huQ hucomm
    obtain ⟨s, hsT, hs⟩ := exists_torus_lang hFr huT
    refine ⟨s * y, ?_, ?_⟩
    · rw [TwistedDiag.mem_thetaFixed]
      refine ⟨?_, ?_⟩
      · exact mul_mem (torusGroup_le_adjointGroup hsT) ((rootSpan_le_adjointGroup Ω _) hyQ)
      · rw [map_mul]
        have h1 : TwistedDiag.theta Fr s = s * u⁻¹ := by
          have h2 := hs
          change ((TwistedDiag.theta Fr) s)⁻¹ * s = u at h2
          calc TwistedDiag.theta Fr s =
              s * ((TwistedDiag.theta Fr s)⁻¹ * s)⁻¹ := by group
            _ = s * u⁻¹ := by rw [h2]
        rw [h1, hu]
        group
    · intro e he
      have hmemH : s * (y * e * y⁻¹) * s⁻¹ ∈ torusGroup Tag.E6 Ω :=
        mul_mem (mul_mem hsT (hyE e he)) (inv_mem hsT)
      have hze : s * y * e * (s * y)⁻¹ = s * (y * e * y⁻¹) * s⁻¹ := by group
      rw [hze]
      have h3' : (s * (y * e * y⁻¹) * s⁻¹) ^ 3 = 1 := by
        have h1 : (s * (y * e * y⁻¹) * s⁻¹) ^ 3 =
            s * (y * e * y⁻¹) ^ 3 * s⁻¹ := conj_pow (a := s) (b := y * e * y⁻¹) (i := 3)
        rw [h1]
        have h2 : (y * e * y⁻¹) ^ 3 = 1 := by
          rw [conj_pow (a := y) (b := e) (i := 3), hE.2 e he]
          group
        rw [h2, mul_one, mul_inv_cancel]
      exact exists_zetaVec_eq_of_mem_torusGroup_pow_three hζ hζo hmemH h3'

end CFSG.StandardType.NoOffTwE6Three
