module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Triple
public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleCore2

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open Triple

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section MainThm


theorem triple_of_free (hKF10 : H1TensorStatement) (hKF11a : Sp4InvolutionStatement)
    (hNK : E1NaturalKStatement) (hLine : NtLineStatement)
    (hCt : CtStructureStatement) (hSplit : RtSplitStatement) (_hLC : LemmaCStatement)
    (hS1 : Step1Statement) : TripleStatement := by
  intro G _ _ M Q Z B t hH AM g hg hplus Fb Fc Y hFF hN' hY
  classical
  have hc := hH.ctx
  have ht : t ∈ LB M Q B := hH.mem
  obtain ⟨n, -, hqn, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hKZ : Nat.card AM.K = Nat.card Z := AM.glob.card
  have hK4 : 4 ≤ Nat.card AM.K := by omega
  obtain ⟨hNL, hNX, hNR, hXR⟩ := b2_nt_facts hSplit hH
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc ht
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hXR' : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := by rw [← hNR]; exact le_sup_right
  have hNR' : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M (LB M Q B) t
  have hXH0 : E1Xpre M Q B t ≤ H0 M Z := hXR'.trans hRH0
  have hNH0 : Nt M (LB M Q B) t ≤ H0 M Z := hNR'.trans hRH0
  haveI : (Q.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hc.hyp.Q_normal.2 hx
  have hQH0 : Q ≤ H0 M Z := hc.Q_le_H0
  obtain ⟨hQFb, hQFc, hFbX, hFcX, hsupF, hintF, hcommF, hSb, hSc⟩ := hFF
  obtain ⟨hQY, hQFc', hYX, hFcX', hsupY, hintY, hcommY, hSy, hSc'⟩ := hY
  have hgM : g ∈ M := Lgen_le_M hc hg.1
  have hgH0 : g ∈ H0 M Z := Lgen_le_H0 hc hg.1
  have hgQ : conjSubgroup g Q = Q := hc.conj_Q_eq hgM
  have hconjH0 : ∀ S : Subgroup G, S ≤ H0 M Z → conjSubgroup g S ≤ H0 M Z := by
    intro S hS x hx
    have h1 : g⁻¹ * x * g ∈ S := mem_conjSubgroup.mp hx
    have h2 := mul_mem (mul_mem hgH0 (hS h1)) (inv_mem hgH0)
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h2
  have hXgH0 := hconjH0 _ hXH0
  have hNgH0 := hconjH0 _ hNH0
  have hFbH0 : Fb ≤ H0 M Z := hFbX.trans hXH0
  have hFcH0 : Fc ≤ H0 M Z := hFcX.trans hXH0
  have hYH0 : Y ≤ H0 M Z := hYX.trans hXgH0
  have hQX : Q ≤ E1Xpre M Q B t := le_sup_right
  have hQXg : Q ≤ conjSubgroup g (E1Xpre M Q B t) :=
    calc Q = conjSubgroup g Q := hgQ.symm
      _ ≤ conjSubgroup g (E1Xpre M Q B t) := Subgroup.map_mono hQX
  have hQNg : Q ≤ conjSubgroup g (Nt M (LB M Q B) t) :=
    calc Q = conjSubgroup g Q := hgQ.symm
      _ ≤ conjSubgroup g (Nt M (LB M Q B) t) := Subgroup.map_mono hQN
  obtain ⟨h8, hhyp, hTS, h4V⟩ := hS1 G M Q Z B t hH AM
  obtain ⟨c, hact⟩ := (hNK G M Q Z B t hH AM).1 hplus
  have hXO : AM.actImage (E1Xpre M Q B t) ≤ AM.S.O := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hg
    exact fun e => AM.φ_Qf y e
  obtain ⟨D, hpf⟩ := lcData_std AM.S (AM.Vsp hc t) (AM.actImage (E1Xpre M Q B t)) hXO hTS
    (parabolic_holds AM.K hK4 AM.S h8 hhyp _ hTS h4V).1 h4V h8 c
    (natIrred_holds AM.K hK4).1.1 hact
  have hBC : AM.actImage Fb ⊔ AM.actImage Fc = AM.actImage (E1Xpre M Q B t) := by
    change Img AM.φ Fb ⊔ Img AM.φ Fc = Img AM.φ (E1Xpre M Q B t)
    rw [← Img_sup AM.φ hFbH0 hFcH0, hsupF]
  have hcomm : ∀ b ∈ AM.actImage Fb, ∀ x ∈ AM.actImage Fc, b * x = x * b :=
    Img_comm AM.φ AM.φ_ker hcommF
  have hinf : AM.actImage Fb ⊓ AM.actImage Fc = ⊥ := by
    change Img AM.φ Fb ⊓ Img AM.φ Fc = ⊥
    rw [← Img_inf AM.φ AM.φ_ker hQFb, hintF]
    exact Img_bot_of_le AM.φ AM.φ_ker le_rfl
  obtain ⟨hSimpB, hBn, hBcard⟩ := Img_sl_facts AM.φ AM.φ_ker hQFb hFbH0 hSb hqn hq4
  obtain ⟨hSimpC, hCn, hCcard⟩ := Img_sl_facts AM.φ AM.φ_ker hQFc hFcH0 hSc hqn hq4
  haveI : IsSimpleGroup ↥(AM.actImage Fb) := hSimpB
  haveI : IsSimpleGroup ↥(AM.actImage Fc) := hSimpC
  obtain ⟨θ, κ, hθ, hBθ, hCθ, hunip⟩ := exists_frame hKF10 hK4 D c hact hpf
    (AM.actImage Fb) (AM.actImage Fc) hBC hcomm hinf hBn hCn
  have hTFb : Img (PhiT AM θ) Fb = rowG := (TI_eq_map AM θ Fb).trans hBθ
  have hTFc : Img (PhiT AM θ) Fc = colG := (TI_eq_map AM θ Fc).trans hCθ
  have hTN : Img (PhiT AM θ) (Nt M (LB M Q B) t) = lineG := by
    obtain ⟨hl1, hl2⟩ := line_facts hH AM D hXR' (hLine G M Q Z B t hH AM)
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := (mem_Img (PhiT AM θ)).mp hy
      obtain ⟨r, hr⟩ := hl1 x hx
      rw [mem_lineG_iff]
      refine ⟨r, ?_⟩
      change conjE θ (AM.φ x) = _
      rw [hr, hunip r]
    · intro hy
      obtain ⟨r, rfl⟩ := mem_lineG_iff.mp hy
      obtain ⟨x, hx, hxr⟩ := hl2 r
      refine (mem_Img (PhiT AM θ)).mpr ⟨x, hx, ?_⟩
      change conjE θ (AM.φ x) = _
      rw [hxr, hunip r]
  have hTX : Img (PhiT AM θ) (E1Xpre M Q B t) = rowG ⊔ colG := by
    rw [← hsupF, Img_sup _ hFbH0 hFcH0, hTFb, hTFc]
  set γ : T3E AM.K := PhiT AM θ ⟨g, hgH0⟩ with hγdef
  have hcjconj : ∀ S : Subgroup G, S ≤ H0 M Z →
      Img (PhiT AM θ) (conjSubgroup g S) = (Img (PhiT AM θ) S).map (cjH γ) := fun S hS =>
    Img_conj (PhiT AM θ) ⟨g, hgH0⟩ hS
  have hγOk : γ ∈ Ok κ :=
    TI_le_Ok AM θ hθ (Subgroup.zpowers g)
      ((mem_Img _).mpr ⟨⟨g, hgH0⟩, Subgroup.mem_zpowers g, rfl⟩)
  have hAO : Img (PhiT AM θ) Y ≤ Ok κ := TI_le_Ok AM θ hθ Y
  have hAc : ∀ a ∈ Img (PhiT AM θ) Y, ∀ x ∈ (colG : Subgroup (T3E AM.K)), a * x = x * a := by
    intro a ha x hx
    rw [← hTFc] at hx
    exact Img_comm (PhiT AM θ) (PhiT_ker AM θ) hcommY a ha x hx
  have hAinf : Img (PhiT AM θ) Y ⊓ colG = ⊥ := by
    rw [← hTFc, ← Img_inf (PhiT AM θ) (PhiT_ker AM θ) hQY, hintY]
    exact Img_bot_of_le _ (PhiT_ker AM θ) le_rfl
  have hAsup : Img (PhiT AM θ) Y ⊔ colG = (rowG ⊔ colG).map (cjH γ) :=
    calc Img (PhiT AM θ) Y ⊔ colG = Img (PhiT AM θ) Y ⊔ Img (PhiT AM θ) Fc := by rw [hTFc]
      _ = Img (PhiT AM θ) (Y ⊔ Fc) := (Img_sup _ hYH0 hFcH0).symm
      _ = Img (PhiT AM θ) (conjSubgroup g (E1Xpre M Q B t)) := by rw [hsupY]
      _ = (Img (PhiT AM θ) (E1Xpre M Q B t)).map (cjH γ) := hcjconj _ hXH0
      _ = (rowG ⊔ colG).map (cjH γ) := by rw [hTX]
  obtain ⟨hSimpY, hYn, hYcard⟩ :=
    Img_sl_facts (PhiT AM θ) (PhiT_ker AM θ) hQY hYH0 hSy hqn hq4
  have hAcard : Nat.card ↥(Img (PhiT AM θ) Y) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) AM.K) := by
    rw [hYcard, card_SL2_eq, hKZ]
  have hAy : ∃ y ∈ Img (PhiT AM θ) Y, NotTwoPow y :=
    notTwoPow_of_not_pgroup_sub (not_pgroup_of_card hYcard hqn hq4)
  have hN'T : (lineG : Subgroup (T3E AM.K)).map (cjH γ) ≤ lineG ⊔ rowG := by
    have h1 : Img (PhiT AM θ) (conjSubgroup g (Nt M (LB M Q B) t)) ≤
        Img (PhiT AM θ) (Nt M (LB M Q B) t) ⊔ Img (PhiT AM θ) Fb := by
      rw [← Img_sup _ hNH0 hFbH0]
      exact Img_mono _ hN'
    rw [hcjconj _ hNH0, hTN, hTFb] at h1
    exact h1
  have hneT : (lineG : Subgroup (T3E AM.K)).map (cjH γ) ≠ lineG := by
    intro h
    apply hg.2.2.2
    apply Img_inj (PhiT AM θ) (PhiT_ker AM θ) hQNg hQN hNgH0 hNH0
    rw [hcjconj _ hNH0, hTN]
    exact h
  have hNNG : Nt M (LB M Q B) t ≤
      conjSubgroup g (Nt M (LB M Q B) t) ⊔ conjSubgroup g (E1Xpre M Q B t) := by
    intro n hn
    have hnL : n ∈ LB M Q B := hNL hn
    have hgL : g⁻¹ * n * g ∈ LB M Q B := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg.2.1) n).mp hnL
      simpa using this
    have h1 : n ∈ conjSubgroup g (Rt M (LB M Q B) t) :=
      mem_conjSubgroup.mpr (le_Rt (LB M Q B) ht hgL)
    have hcs : conjSubgroup g (Nt M (LB M Q B) t ⊔ E1Xpre M Q B t) =
        conjSubgroup g (Nt M (LB M Q B) t) ⊔ conjSubgroup g (E1Xpre M Q B t) :=
      Subgroup.map_sup _ _ _
    rw [← hNR, hcs] at h1
    exact h1
  have hNNT : (lineG : Subgroup (T3E AM.K)) ≤
      lineG.map (cjH γ) ⊔ (rowG ⊔ colG).map (cjH γ) := by
    have h1 : Img (PhiT AM θ) (Nt M (LB M Q B) t) ≤
        Img (PhiT AM θ) (conjSubgroup g (Nt M (LB M Q B) t)) ⊔
          Img (PhiT AM θ) (conjSubgroup g (E1Xpre M Q B t)) := by
      rw [← Img_sup _ hNgH0 hXgH0]
      exact Img_mono _ hNNG
    rw [hcjconj _ hNH0, hcjconj _ hXH0, hTN, hTX] at h1
    exact h1
  have hCore : CoreData κ γ (Img (PhiT AM θ) Y) :=
    ⟨hγOk, hAO, hAc, hAinf, hAsup, hSimpY, hYn, hAcard, hAy, hN'T, hneT, hNNT⟩
  have hbound : ∀ 𝒰 : Subgroup (T3E AM.K), 𝒰 ≤ Ok κ →
      (∀ u ∈ 𝒰, ∀ x ∈ (colG : Subgroup (T3E AM.K)), u * x = x * u) →
      (∀ u ∈ 𝒰, ∀ l ∈ (lineG : Subgroup (T3E AM.K)), u * l = l * u) →
      𝒰 ≤ Subgroup.closure ((Img (PhiT AM θ) Y : Set (T3E AM.K)) ∪
        ((rowG (K := AM.K) : Subgroup (T3E AM.K)) : Set (T3E AM.K))) →
      (∀ u ∈ 𝒰, u * u = 1) → Nat.card 𝒰 ≤ 2 * Nat.card AM.K ^ 2 := by
    intro 𝒰 hOk hcol hlin hcl hsq
    have hrange : 𝒰 ≤ (PhiT AM θ).range := by
      refine hcl.trans ((Subgroup.closure_le _).mpr (Set.union_subset ?_ ?_))
      · intro y hy
        obtain ⟨x, -, rfl⟩ := (mem_Img (PhiT AM θ)).mp hy
        exact ⟨x, rfl⟩
      · intro y hy
        have hy' : y ∈ Img (PhiT AM θ) Fb := by rw [hTFb]; exact hy
        obtain ⟨x, -, rfl⟩ := (mem_Img (PhiT AM θ)).mp hy'
        exact ⟨x, rfl⟩
    set 𝒱 : Subgroup G := (𝒰.comap (PhiT AM θ)).map (H0 M Z).subtype with h𝒱
    have h𝒱H0 : 𝒱 ≤ H0 M Z := Subgroup.map_subtype_le _
    have hmem𝒱 : ∀ x : ↥(H0 M Z), (x : G) ∈ 𝒱 ↔ PhiT AM θ x ∈ 𝒰 := by
      intro x
      constructor
      · rintro ⟨x', hx', hxx⟩
        have : x' = x := Subtype.ext hxx
        subst this
        exact hx'
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hQ𝒱 : Q ≤ 𝒱 := fun x hx => (hmem𝒱 ⟨x, hQH0 hx⟩).mpr (by
      have : PhiT AM θ ⟨x, hQH0 hx⟩ = 1 := (PhiT_ker AM θ _).mpr hx
      rw [this]
      exact 𝒰.one_mem)
    have hImg𝒱 : Img (PhiT AM θ) 𝒱 = 𝒰 := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := (mem_Img (PhiT AM θ)).mp hy
        exact (hmem𝒱 x).mp hx
      · intro hy
        obtain ⟨x, rfl⟩ := hrange hy
        exact (mem_Img (PhiT AM θ)).mpr ⟨x, (hmem𝒱 x).mpr hy, rfl⟩
    have htH0 : t ∈ H0 M Z := hRH0 (le_Rt (LB M Q B) ht ht)
    have hΦt : PhiT AM θ ⟨t, htH0⟩ ∈ (lineG : Subgroup (T3E AM.K)) := by
      rw [← hTN]
      exact (mem_Img _).mpr ⟨⟨t, htH0⟩, tMemNt_aux hH, rfl⟩
    have h𝒱E : 𝒱 ≤ E1Ct hc t := by
      intro x hx
      have hxH0 : x ∈ H0 M Z := h𝒱H0 hx
      have hxU : PhiT AM θ ⟨x, hxH0⟩ ∈ 𝒰 := (hmem𝒱 ⟨x, hxH0⟩).mp hx
      have hcm := hlin _ hxU _ hΦt
      have h1 : PhiT AM θ ⁅(⟨x, hxH0⟩ : ↥(H0 M Z)), ⟨t, htH0⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcm
      have h2 : ⁅x, t⁆ ∈ Q := by
        have := (PhiT_ker AM θ _).mp h1
        simpa [commutatorElement_def] using this
      exact Subgroup.mem_inf.mpr ⟨mem_CommQ.mpr ⟨(Subgroup.mem_inf.mp hxH0).1, h2⟩, hxH0⟩
    obtain ⟨hRE, hidx, -⟩ := hCt G M Q Z B t hH
    haveI : (Rt M (LB M Q B) t).IsFiniteRelIndex (E1Ct hc t) :=
      ⟨Subgroup.index_ne_zero_of_finite⟩
    have hrel : (Rt M (LB M Q B) t).relIndex 𝒱 ≤ 2 :=
      (Subgroup.relIndex_le_of_le_right h𝒱E Subgroup.relIndex_ne_zero).trans hidx
    have hcard1 := Subgroup.relIndex_mul_card (H := Rt M (LB M Q B) t) (K := 𝒱)
    have hle2 : Nat.card ↥𝒱 ≤ 2 * Nat.card ↥(Rt M (LB M Q B) t ⊓ 𝒱) := by
      rw [← hcard1]
      exact Nat.mul_le_mul_right _ hrel
    have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
    have hc𝒱 := card_Img (PhiT AM θ) (PhiT_ker AM θ) hQ𝒱 h𝒱H0
    have hc𝒱' := card_Img (PhiT AM θ) (PhiT_ker AM θ) (le_inf hQR hQ𝒱)
      (inf_le_left.trans hRH0)
    rw [Img_inf (PhiT AM θ) (PhiT_ker AM θ) hQR, hImg𝒱] at hc𝒱'
    rw [hImg𝒱] at hc𝒱
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have hle3 : Nat.card ↥𝒰 ≤ 2 * Nat.card ↥(Img (PhiT AM θ) (Rt M (LB M Q B) t) ⊓ 𝒰) := by
      rw [hc𝒱, hc𝒱'] at hle2
      have : Nat.card Q * Nat.card ↥𝒰 ≤ Nat.card Q * (2 * Nat.card ↥(Img (PhiT AM θ)
          (Rt M (LB M Q B) t) ⊓ 𝒰)) := by linarith
      exact Nat.le_of_mul_le_mul_left this hQpos
    have hR : Img (PhiT AM θ) (Rt M (LB M Q B) t) = lineG ⊔ (rowG ⊔ colG) := by
      rw [← hNR, Img_sup _ hNH0 hXH0, hTN, hTX]
    haveI := simple_colG (K := AM.K) hK4
    have h𝒰₀ : Img (PhiT AM θ) (Rt M (LB M Q B) t) ⊓ 𝒰 ≤ lineG ⊔ rowG := by
      intro u hu
      obtain ⟨huR, hu𝒰⟩ := Subgroup.mem_inf.mp hu
      rw [hR] at huR
      obtain ⟨l, hl, z, hz, rfl⟩ := fu_mem_sup lineG_comm_rowG_colG huR
      obtain ⟨f, hf, x, hx, rfl⟩ := fu_mem_sup rowG_comm_colG hz
      have hx1 : x = 1 := by
        apply fu_eq_one_of_central not_comm_colG hx
        intro y hy
        have h1 := hcol _ hu𝒰 y hy
        have e1 : l * (f * x) * y = l * f * (x * y) := by simp only [mul_assoc]
        have e2 : y * (l * (f * x)) = l * f * (y * x) := by
          calc y * (l * (f * x)) = (y * l) * (f * x) := by rw [mul_assoc]
            _ = (l * y) * (f * x) := by rw [(lineG_comm_colG l hl y hy).symm]
            _ = l * (y * f) * x := by simp only [mul_assoc]
            _ = l * (f * y) * x := by rw [(rowG_comm_colG f hf y hy).symm]
            _ = l * f * (y * x) := by simp only [mul_assoc]
        rw [e1, e2] at h1
        exact mul_left_cancel h1
      subst hx1
      rw [mul_one]
      exact Subgroup.mul_mem_sup hl hf
    have hcard𝒰₀ := two_group_bound (K := AM.K) (n := n) (by rw [hKZ, hqn]) hK4 _ h𝒰₀
      (fun u hu => hsq u (Subgroup.mem_inf.mp hu).2)
    calc Nat.card ↥𝒰 ≤ 2 * Nat.card ↥(Img (PhiT AM θ) (Rt M (LB M Q B) t) ⊓ 𝒰) := hle3
      _ ≤ 2 * Nat.card AM.K ^ 2 := Nat.mul_le_mul_left _ hcard𝒰₀
  obtain ⟨hκ0, hN'row, hlineA, hAeq⟩ := triple_core_free hKF11a hK4 hCore hbound
  subst hκ0
  have hTY : Img (PhiT AM θ) Y = slotG := hAeq
  refine ⟨⟨θ, fun e => (hθ e).trans (by simp [Qk]),
    factorAct_of_img AM θ Y tensor3Act0 act0E (fun A T => act0E_apply A T) hTY,
    factorAct_of_img AM θ Fb tensor3Act1 act1E (fun A T => act1E_apply A T) hTFb,
    factorAct_of_img AM θ Fc tensor3Act2 act2E (fun A T => act2E_apply A T) hTFc⟩,
    ?_, ?_, ?_, ?_⟩
  ·
    refine (Img_le_iff (PhiT AM θ) (PhiT_ker AM θ) hQY hNH0).mp ?_
    rw [hTN, hTY]
    exact lineG_le_slotG
  ·
    refine (Img_le_iff (PhiT AM θ) (PhiT_ker AM θ) hQFb hNgH0).mp ?_
    rw [hcjconj _ hNH0, hTN, hTFb]
    exact hN'row
  ·
    apply le_antisymm _ (le_inf hQY hQFb)
    intro x hx
    have hxH0 : x ∈ H0 M Z := hYH0 hx.1
    have h1 : PhiT AM θ ⟨x, hxH0⟩ ∈ Img (PhiT AM θ) (Y ⊓ Fb) :=
      (mem_Img _).mpr ⟨⟨x, hxH0⟩, hx, rfl⟩
    rw [Img_inf (PhiT AM θ) (PhiT_ker AM θ) hQY, hTY, hTFb, slotG_inf_rowG] at h1
    exact (PhiT_ker AM θ _).mp (Subgroup.mem_bot.mp h1)
  ·
    intro a ha b hb
    have hcm : ∀ u ∈ Img (PhiT AM θ) Y, ∀ v ∈ Img (PhiT AM θ) Fb, u * v = v * u := by
      intro u hu v hv
      rw [hTY] at hu
      rw [hTFb] at hv
      obtain ⟨A, rfl⟩ := hu
      obtain ⟨B', rfl⟩ := hv
      exact act0E_comm_act1E A B'
    have h1 : PhiT AM θ ⁅(⟨a, hYH0 ha⟩ : ↥(H0 M Z)), ⟨b, hFbH0 hb⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcm _ ((mem_Img _).mpr ⟨_, ha, rfl⟩) _ ((mem_Img _).mpr ⟨_, hb, rfl⟩)
    have := (PhiT_ker AM θ _).mp h1
    simpa [commutatorElement_def] using this

end MainThm

end CFSG.RankThree.GF2n.Smith81.Smith23E1
