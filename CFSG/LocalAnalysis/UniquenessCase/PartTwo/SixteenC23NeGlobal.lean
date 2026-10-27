module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Order
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Sylow
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_conj_eq_self_of_card_le {V₀ : Subgroup G} {y : G}
    (hy : y ∈ normalizer (V₀ : Set G)) (hy7 : orderOf y = 7) (hcard : Nat.card V₀ ≤ 4) :
    ∀ e ∈ V₀, y * e * y⁻¹ = e := by
  have hy7' : y ^ 7 = 1 := by rw [← hy7]; exact pow_orderOf_eq_one y
  have hzpow : (⟨y, hy⟩ : normalizer (V₀ : Set G)) ^ 7 = 1 := by
    ext
    simpa using hy7'
  set ψ : MulAut ↥V₀ := V₀.normalizerMonoidHom ⟨y, hy⟩ with hψdef
  have hψ7 : ψ ^ 7 = 1 := by
    rw [hψdef, ← map_pow, hzpow, map_one]
  have hdvd7 : orderOf ψ ∣ 7 := orderOf_dvd_iff_pow_eq_one.2 hψ7
  have hdvd24 : orderOf ψ ∣ 24 := by
    have h1 : orderOf ψ ∣ Nat.card (MulAut ↥V₀) := orderOf_dvd_natCard ψ
    have h2 : Nat.card (MulAut ↥V₀) ∣ Nat.card (Equiv.Perm ↥V₀) := by
      let f : MulAut ↥V₀ →* Equiv.Perm ↥V₀ := MulAut.toPerm (M := ↥V₀)
      have hf : Function.Injective f := MulEquiv.toEquiv_injective
      have hcard' : Nat.card (MulAut ↥V₀) = Nat.card f.range := by
        rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hf, Subgroup.card_top]
      rw [hcard']
      simpa using Subgroup.card_dvd_of_le (le_top : f.range ≤ ⊤)
    have h3 : Nat.card (Equiv.Perm ↥V₀) = Nat.factorial (Nat.card ↥V₀) := Nat.card_perm
    have h4 : Nat.factorial (Nat.card ↥V₀) ∣ 24 := by
      simpa [show Nat.factorial 4 = 24 by decide] using Nat.factorial_dvd_factorial hcard
    have hperm : Nat.card (Equiv.Perm ↥V₀) ∣ 24 := by
      rw [h3]
      exact h4
    exact h1.trans (h2.trans hperm)
  have hone : orderOf ψ = 1 := by
    have hg : orderOf ψ ∣ Nat.gcd 7 24 := Nat.dvd_gcd hdvd7 hdvd24
    rw [show Nat.gcd 7 24 = 1 by decide, Nat.dvd_one] at hg
    exact hg
  have hψ1 : ψ = 1 := orderOf_eq_one_iff.1 hone
  intro e he
  have h := congrArg (fun (f : MulAut ↥V₀) => ((f ⟨e, he⟩ : ↥V₀) : G)) hψ1
  simp only [MulAut.one_apply] at h
  rwa [hψdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h

theorem c23ne_exists_y0 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_2 D V₀ V hV L) :
    ∃ y ∈ D.M, orderOf y = 7 ∧ ∀ v ∈ V, y * v = v * y := by
  have h151 := hS.setting.hyp151
  have hP := h151.hyp125.pairFacts
  have hsmall : mSub V₀ ≤ 2 := hS.setting.hyp16.small
  have hsig : 7 ∈ D.sig := by
    rw [hc.2.2.2]
    exact Set.mem_singleton 7
  obtain ⟨E, hEM, hEab, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := 7) (M := D.M) (k := 3) (by norm_num) (by
      rw [UC6.groupPRank_eq_pRank]
      exact hSg.three_le 7 hsig)
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hEstab : E ≤ stabTil V₀ V := hEM.trans hMs
  let φ : ↥E →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hEstab)
  have hφrange : φ.range ≤ Mbar D.M V₀ V hV := by
    rintro _ ⟨x, rfl⟩
    exact actTil_mem_barSub V₀ V hV (X := D.M) (g := (x : G)) (hEM x.2) (hEstab x.2)
  have hker : φ.ker ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hbot
    have hcard : Nat.card φ.range = Nat.card ↥E := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
    have hdvd : 7 ^ 3 ∣ Nat.card (Mbar D.M V₀ V hV) := by
      have h := Subgroup.card_dvd_of_le hφrange
      rwa [hcard, hEcard] at h
    exact c23_not_dvd_card_mbar_case2 D h1217 hS hc hdvd
  obtain ⟨yE, hyker, hyne⟩ : ∃ yE : ↥E, yE ∈ φ.ker ∧ yE ≠ 1 := by
    by_contra h
    exact hker ((Subgroup.eq_bot_iff_forall φ.ker).2 (fun x hx => by
      by_contra hx1
      exact h ⟨x, hx, hx1⟩))
  have hyE : (yE : G) ∈ E := yE.2
  have hyM : (yE : G) ∈ D.M := hEM hyE
  have hyne' : (yE : G) ≠ 1 := by
    intro h1
    exact hyne (Subtype.ext (by simpa using h1))
  have hpow7 : (yE : G) ^ 7 = 1 := hEab.2 (yE : G) hyE
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have horder : orderOf (yE : G) = 7 := orderOf_eq_prime hpow7 hyne'
  have hcardV₀ : Nat.card ↥V₀ ≤ 4 := by
    have h0 : Nat.card ↥V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub (U := V₀) hP.elemAbelian₀.isPGroup
    calc Nat.card ↥V₀ = 2 ^ mSub V₀ := h0
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hsmall
      _ = 4 := by norm_num
  have hy_norm : (yE : G) ∈ normalizer (V₀ : Set G) := hP.le_normalizer₀ hyM
  have hcent₀ : ∀ e ∈ V₀, (yE : G) * e * (yE : G)⁻¹ = e :=
    c23ne_conj_eq_self_of_card_le hy_norm horder hcardV₀
  have hδ : ∀ v ∈ V, (yE : G) * v * (yE : G)⁻¹ * v⁻¹ ∈ V₀ := by
    intro v hv
    have h1 : actTil V₀ V hV (Subgroup.inclusion hEstab yE) = 1 := hyker
    exact (actTil_eq_one_iff V₀ V hV (Subgroup.inclusion hEstab yE)).1 h1 v hv
  have hyV : ∀ v ∈ V, (yE : G) * v = v * (yE : G) := by
    intro v hv
    haveI : IsMulCommutative ↥V := hV.1
    set d : G := (yE : G) * v * (yE : G)⁻¹ * v⁻¹ with hddef
    have hd₀ : d ∈ V₀ := hδ v hv
    have hdV : d ∈ V := hP.le hd₀
    have hyd : (yE : G) * d * (yE : G)⁻¹ = d := hcent₀ d hd₀
    have hdcomm : d * v = v * d := by
      exact congrArg Subtype.val (mul_comm' (⟨d, hdV⟩ : V) (⟨v, hv⟩ : V))
    have h1 : (yE : G) * v * (yE : G)⁻¹ = v * d := by
      rw [← hdcomm]
      simp only [hddef]
      group
    have h3 : d * d = 1 := by
      rw [← pow_two]
      exact hV.2 d hdV
    have hy2v : (yE : G) ^ 2 * v * ((yE : G) ^ 2)⁻¹ = v := by
      rw [pow_two]
      calc ((yE : G) * (yE : G)) * v * (((yE : G) * (yE : G)))⁻¹
          = (yE : G) * ((yE : G) * v * (yE : G)⁻¹) * (yE : G)⁻¹ := by group
        _ = (yE : G) * (v * d) * (yE : G)⁻¹ := by rw [h1]
        _ = ((yE : G) * v * (yE : G)⁻¹) * ((yE : G) * d * (yE : G)⁻¹) := by group
        _ = (v * d) * d := by rw [h1, hyd]
        _ = v * (d * d) := by group
        _ = v := by rw [h3, mul_one]
    have hy2comm : (yE : G) ^ 2 * v = v * (yE : G) ^ 2 := by
      calc (yE : G) ^ 2 * v = ((yE : G) ^ 2 * v * ((yE : G) ^ 2)⁻¹) * (yE : G) ^ 2 := by
            group
        _ = v * (yE : G) ^ 2 := by rw [hy2v]
    have hcent_y2 : (yE : G) ^ 2 ∈ Subgroup.centralizer ({v} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hy2comm
    have hy_eq : (yE : G) = ((yE : G) ^ 2) ^ 4 := by
      rw [← pow_mul]
      show (yE : G) = (yE : G) ^ (2 * 4)
      rw [show 2 * 4 = 8 by norm_num, show (8 : ℕ) = 7 + 1 by norm_num, pow_add,
        hpow7, one_mul, pow_one]
    have hcent_y : (yE : G) ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [hy_eq]
      exact pow_mem hcent_y2 4
    exact Subgroup.mem_centralizer_singleton_iff.1 hcent_y
  exact ⟨(yE : G), hyM, horder, hyV⟩

theorem c23ne_sp_seven (D : Data G) (hSg : UC6S846.SigmaStd D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Case167_2 D V₀ V hV L) {K : Subgroup G}
    (hK : K ∈ calC D.M) : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M :=
  UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hK) (by
    rw [hc.2.2.2]
    exact Set.mem_singleton 7)

theorem c23ne_isTI_of_centralizers {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G))
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 M) {y : G} (hyM : y ∈ M)
    (hy7 : orderOf y = 7) (hyV : ∀ v ∈ V, y * v = v * y)
    (hcent : ∀ v ∈ V, v ≠ 1 → centralizer ({v} : Set G) ≤ M) :
    CFSG.CGT.Timmesfeld75.IsTI V := by
  intro g
  by_cases hbot : V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    obtain ⟨v, hv, hvne⟩ : ∃ v ∈ V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V, v ≠ 1 := by
      by_contra h
      exact hbot ((Subgroup.eq_bot_iff_forall _).2 (fun x hx => by
        by_contra hx1
        exact h ⟨x, hx, hx1⟩))
    have hvV : v ∈ V := hv.1
    have hvconj : v ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g V := hv.2
    set w : G := g⁻¹ * v * g with hwdef
    have hwV : w ∈ V := by
      rw [hwdef]
      exact (CFSG.CGT.Timmesfeld75.mem_conjSubgroup).1 hvconj
    have hv_eq : v = g * w * g⁻¹ := by rw [hwdef]; group
    have hwne : w ≠ 1 := by
      intro h1
      exact hvne (by rw [hv_eq, h1]; group)
    have hyw : y * w = w * y := hyV w hwV
    have hgygv : g * y * g⁻¹ ∈ centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g * y * g⁻¹) * v
          = g * (y * w) * g⁻¹ := by rw [hv_eq]; group
        _ = g * (w * y) * g⁻¹ := by rw [hyw]
        _ = v * (g * y * g⁻¹) := by rw [hv_eq]; group
    have hgygM : g * y * g⁻¹ ∈ M := hcent v hvV hvne hgygv
    have hYmem : y ∈ M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom := by
      refine ⟨hyM, ?_⟩
      exact Subgroup.mem_map.2 ⟨g * y * g⁻¹, hgygM, by
        simp [MulAut.conj_apply, mul_assoc]⟩
    have hdvd : 7 ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom) := by
      have hle : Subgroup.zpowers y ≤ M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [Subgroup.zpowers_le]
        exact hYmem
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hy7] at h
    have hgM : g ∈ M := by
      by_contra hgnM
      exact hsp.2.2 g⁻¹ (fun hginv => hgnM (by simpa using M.inv_mem hginv)) hdvd
    have hmap : V.map (MulAut.conj g) = V :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := V) (g := g)).1 (hM hgM)
    have hconj : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V := by
      simpa [CFSG.CGT.Timmesfeld75.conjSubgroup] using hmap
    rw [hconj]
    simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
