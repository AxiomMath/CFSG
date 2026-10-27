module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsConj
public import CFSG.RankThree.GF2n.Stroth80.Sec10Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

section Aux

@[expose] def centMod (M Q Y : Subgroup G) (hQ : M ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup G where
  carrier := {x | x ∈ M ∧ ∀ y ∈ Y, ⁅x, y⁆ ∈ Q}
  mul_mem' := by
    rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
    refine ⟨M.mul_mem haM hbM, fun y hy => ?_⟩
    have e : ⁅a * b, y⁆ = (a * ⁅b, y⁆ * a⁻¹) * ⁅a, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQ haM) _).mp (hb y hy)) (ha y hy)
  one_mem' := ⟨M.one_mem, fun y _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro a ⟨haM, ha⟩
    refine ⟨M.inv_mem haM, fun y hy => ?_⟩
    have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (hQ (M.inv_mem haM)) _).mp (Q.inv_mem (ha y hy))
    simpa using this

omit [Finite G] in
theorem conj_normalizer (g : G) (Y : Subgroup G) :
    conjSubgroup g (Subgroup.normalizer (Y : Set G)) =
      Subgroup.normalizer (conjSubgroup g Y : Set G) :=
  Subgroup.map_normalizer_eq_of_bijective (f := (MulAut.conj g).toMonoidHom) Y
    (MulAut.conj g).bijective

theorem mem_of_comm_mem_Q {Y Q : Subgroup G} {q : ℕ} (h4 : 4 ≤ q) (hq2 : ∃ s : ℕ, q = 2 ^ s)
    (h : QuotSat Y Q (IsSLModel 2 q)) {c : G} (hcY : c ∈ Y) (hc : ∀ y ∈ Y, ⁅c, y⁆ ∈ Q) :
    c ∈ Q := by
  obtain ⟨hn, hmod⟩ := h
  haveI := hn
  obtain ⟨hcard, hsimple⟩ := isSLModel_two_data h4 hq2 hmod
  haveI := hsimple
  let cbar : ↥Y ⧸ Q.subgroupOf Y := QuotientGroup.mk ⟨c, hcY⟩
  have hcent : cbar ∈ Subgroup.center (↥Y ⧸ Q.subgroupOf Y) := by
    rw [Subgroup.mem_center_iff]
    intro z
    induction z using QuotientGroup.induction_on with
    | H y =>
      have h1 : ⁅(QuotientGroup.mk y : ↥Y ⧸ Q.subgroupOf Y), cbar⁆ = 1 := by
        change ⁅(QuotientGroup.mk' (Q.subgroupOf Y)) y, (QuotientGroup.mk' (Q.subgroupOf Y))
          ⟨c, hcY⟩⁆ = 1
        rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf]
        show ⁅(y : G), c⁆ ∈ Q
        rw [← commutatorElement_inv]
        exact Q.inv_mem (hc y y.2)
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
  by_contra hcQ
  have hne : cbar ≠ 1 := by
    intro h1
    apply hcQ
    have := (QuotientGroup.eq_one_iff (⟨c, hcY⟩ : ↥Y)).mp h1
    exact Subgroup.mem_subgroupOf.mp this
  have hctop : Subgroup.center (↥Y ⧸ Q.subgroupOf Y) = ⊤ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥Y ⧸ Q.subgroupOf Y))).resolve_left ?_
    intro hbot
    rw [hbot] at hcent
    exact hne (Subgroup.mem_bot.mp hcent)
  letI : CommGroup (↥Y ⧸ Q.subgroupOf Y) := Group.commGroupOfCenterEqTop hctop
  have hp := IsSimpleGroup.prime_card (α := ↥Y ⧸ Q.subgroupOf Y)
  rw [hcard] at hp
  have hq1 : q ≠ 1 := by omega
  have hq2' : q ^ 2 - 1 ≠ 1 := by
    have : 16 ≤ q ^ 2 := by nlinarith
    omega
  exact Nat.not_prime_mul hq1 hq2' hp

theorem normalizer_centMod {hQ : M ≤ Subgroup.normalizer (Q : Set G)} {Y : Subgroup G} {g : G}
    (hgM : g ∈ M) (hgY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer (centMod M Q Y hQ : Set G) := by
  have key : ∀ g : G, g ∈ M → g ∈ Subgroup.normalizer (Y : Set G) →
      ∀ z ∈ centMod M Q Y hQ, g * z * g⁻¹ ∈ centMod M Q Y hQ := by
    intro g hgM hgY z hz
    refine ⟨M.mul_mem (M.mul_mem hgM hz.1) (M.inv_mem hgM), fun y' hy' => ?_⟩
    have hy'' : g⁻¹ * y' * g ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Y : Set G)).inv_mem hgY)
        y').mp hy'
      simpa using this
    have e : ⁅g * z * g⁻¹, y'⁆ = g * ⁅z, g⁻¹ * y' * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hQ hgM) _).mp (hz.2 _ hy'')
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => key g hgM hgY z hz, fun hz => ?_⟩
  have := key g⁻¹ (M.inv_mem hgM) ((Subgroup.normalizer (Y : Set G)).inv_mem hgY) _ hz
  simpa [mul_assoc] using this

theorem centMod_le_normalizer {hQ : M ≤ Subgroup.normalizer (Q : Set G)} {Y K : Subgroup G}
    (hQK : Q ≤ K) (hKY : K ≤ Y) :
    centMod M Q Y hQ ≤ Subgroup.normalizer (K : Set G) :=
  normalizer_of_commutator_le (X := K) (Y := centMod M Q Y hQ) hQK fun a ha c hc => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hc.2 a (hKY ha))

@[expose] def DY (M Q B Y : Subgroup G) (y : G) : Subgroup G :=
  ⨆ (g : G) (_ : g ∈ M) (_ : conjSubgroup g Y = Y) (_ : y ∈ conjSubgroup g (LB M Q B)),
    conjSubgroup g (LB M Q B ⊓ Y)

theorem DY_le_Y (M Q B Y : Subgroup G) (y : G) : DY M Q B Y y ≤ Y := by
  refine iSup_le fun g => iSup_le fun hg => iSup_le fun hgY => iSup_le fun hy => ?_
  exact (Subgroup.map_mono inf_le_right).trans hgY.le

theorem DY_le_Lgen (M Q B Y : Subgroup G) (y : G) : DY M Q B Y y ≤ Lgen M (LB M Q B) := by
  refine iSup_le fun g => iSup_le fun hg => iSup_le fun hgY => iSup_le fun hy => ?_
  exact (Subgroup.map_mono inf_le_left).trans (le_iSup₂_of_le g hg le_rfl)

theorem LB_inf_Y_le_DY (M Q B Y : Subgroup G) {y : G} (hy : y ∈ LB M Q B) :
    LB M Q B ⊓ Y ≤ DY M Q B Y y := by
  have h1 : y ∈ conjSubgroup (1 : G) (LB M Q B) := by rw [conjSubgroup_one]; exact hy
  refine le_trans (le_of_eq (conjSubgroup_one _).symm) ?_
  exact le_iSup_of_le (1 : G) (le_iSup_of_le M.one_mem
    (le_iSup_of_le (conjSubgroup_one Y) (le_iSup_of_le h1 le_rfl)))

theorem isPGroup_CN (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {y : G} (hyL : y ∈ LB M Q B)
    (hyQ : y ∉ Q) : IsPGroup 2 ↥(hc.CN y) := by
  have hs5 := hs.toSec5
  have hsy : Sec5Hyp hc n y := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hyL, hyQ⟩
  by_cases hR : Rt M (LB M Q B) y = LB M Q B
  · have hle : hc.CN y ≤ LB M Q B := fun x hx => hR ▸ (Ctx.mem_CN.mp hx).1
    exact (hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen).of_injective
      (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
  · exact hc.isPGroup_CN_of_311 h34 hsy
      (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen y hyL hyQ hR)

theorem conj_CN_eq (hc : Ctx M Q Z B) {y c : G} (hy : y ∈ M) (hcM : c ∈ M)
    (hcy : ⁅c, y⁆ ∈ Q) : conjSubgroup c (hc.CN y) = hc.CN y := by
  rw [← Ctx.CN_conjM hc hcM y]
  have hyQ : y⁻¹ * ⁅c, y⁆ * y ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hy)) _).mp hcy
    simpa using this
  have e : c * y * c⁻¹ = y * (y⁻¹ * ⁅c, y⁆ * y) := by
    simp only [commutatorElement_def]; group
  rw [e, Ctx.CN_mul_of_mem_Q hc hyQ]

end Aux

open CFSG.RankThreeEvenClassification.Helpers in
theorem CN_le_Y (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (hall : GoodAll M Q B Y)
    {y : G} (hyLY : y ∈ LB M Q B ⊓ Y) (hyQ : y ∉ Q) : hc.CN y ≤ Y := by
  classical
  have hyL : y ∈ LB M Q B := (Subgroup.mem_inf.mp hyLY).1
  have hyY : y ∈ Y := (Subgroup.mem_inf.mp hyLY).2
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hYM : Y ≤ M := hYR.trans (hc.Rt_le_M t)
  have hXM : X ≤ M := hXR.trans (hc.Rt_le_M t)
  have hyM : y ∈ M := hYM hyY
  have hXY' : X ≤ Subgroup.normalizer (Y : Set G) :=
    normalizer_of_commutator_le (X := Y) (Y := X) hQY (fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this)
  have hRY : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Y : Set G) :=
    calc Rt M (LB M Q B) t = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le hXY' Subgroup.le_normalizer
  have hLY : LB M Q B ≤ Subgroup.normalizer (Y : Set G) := (le_Rt (LB M Q B) ht).trans hRY
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQ2 : IsPGroup 2 ↥Q := by
    have := pCoreOf_isPGroup 2 M
    have hQeq : pCoreOf 2 M = Q := hc.hyp.hQ.symm
    rwa [hQeq] at this
  set L := LB M Q B with hL
  set M₀ := Lgen M L with hM₀
  let Y₁ := centMod M Q Y hQn
  have hY₁Y : Y₁ ⊓ Y ≤ Q := fun c hc' => mem_of_comm_mem_Q hq4 hq2 hYsl hc'.2 hc'.1.2
  have hY₁N : Y₁ ≤ Subgroup.normalizer (Y : Set G) := centMod_le_normalizer hQY le_rfl
  have hQY₁ : Q ≤ Y₁ := fun q hq => ⟨hQM hq, fun y' hy' => by
    have e : ⁅q, y'⁆ = q * (y' * q⁻¹ * y'⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hQn (hYM hy')) _).mp (Q.inv_mem hq))⟩
  have hM₀M : M₀ ≤ M := iSup₂_le fun m hm r hr => hc.conj_LB_le_M hm hr
  have hM₀Y : M₀ ≤ Subgroup.normalizer (Y : Set G) := by
    refine iSup₂_le fun m hm => ?_
    obtain ⟨g, hgM, hgY, hgL⟩ := hall m hm
    have hgL' : conjSubgroup g L = conjSubgroup m L := by rw [hgL, hc.LB_conj hm]
    rw [← hgL']
    have h1 : conjSubgroup g L ≤ conjSubgroup g (Subgroup.normalizer (Y : Set G)) :=
      Subgroup.map_mono hLY
    rw [conj_normalizer, hgY] at h1
    exact h1
  have hM₀Y₁ : M₀ ≤ Subgroup.normalizer (Y₁ : Set G) := fun g hg =>
    normalizer_centMod (hM₀M hg) (hM₀Y hg)
  have hRyM₀ : Rt M L y ≤ M₀ :=
    iSup_le fun m => iSup_le fun hm => iSup_le fun _ => le_iSup₂_of_le m hm le_rfl
  have hRyY : Rt M L y ≤ Subgroup.normalizer (Y : Set G) := hRyM₀.trans hM₀Y
  have hRsup : Rt M L y ≤ Y₁ ⊔ DY M Q B Y y := by
    refine iSup_le fun m => iSup_le fun hm => iSup_le fun hmy => ?_
    obtain ⟨g, hgM, hgY, hgL⟩ := hall m hm
    have hgL' : conjSubgroup g L = conjSubgroup m L := by rw [hgL, hc.LB_conj hm]
    have hygL : y ∈ conjSubgroup g L := hgL' ▸ hmy
    rw [← hgL']
    have hLeq : L = (L ⊓ X) ⊔ (L ⊓ Y) := h4.2.2
    conv_lhs => rw [hLeq]
    rw [conjSubgroup_sup']
    refine sup_le_sup ?_ ?_
    · intro z hz
      have he : g⁻¹ * z * g ∈ X := (Subgroup.mem_inf.mp (mem_conjSubgroup.mp hz)).2
      have hzeq : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      refine ⟨?_, fun y' hy' => ?_⟩
      · rw [hzeq]
        exact M.mul_mem (M.mul_mem hgM (hXM he)) (M.inv_mem hgM)
      · have hy'' : g⁻¹ * y' * g ∈ Y := by
          have : y' ∈ conjSubgroup g Y := by rw [hgY]; exact hy'
          exact mem_conjSubgroup.mp this
        have e' : ⁅z, y'⁆ = g * ⁅g⁻¹ * z * g, g⁻¹ * y' * g⁆ * g⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e']
        exact (Subgroup.mem_normalizer_iff.mp (hQn hgM) _).mp (hcomm _ he _ hy'')
    · exact le_iSup_of_le g (le_iSup_of_le hgM (le_iSup_of_le hgY (le_iSup_of_le hygL le_rfl)))
  set N := hc.CN y with hN
  have hN2 : IsPGroup 2 ↥N := isPGroup_CN h34 h311a hs hyL hyQ
  have hNR : N ≤ Rt M L y := fun x hx => (Ctx.mem_CN.mp hx).1
  have hNM₀ : N ≤ M₀ := hNR.trans hRyM₀
  have hNnY : N ≤ Subgroup.normalizer (Y : Set G) := hNR.trans hRyY
  have hY₁N' : ∀ c ∈ Y₁, conjSubgroup c N = N := fun c hcY₁ =>
    conj_CN_eq hc hyM hcY₁.1 (hcY₁.2 y hyY)
  let P : Subgroup G := ((N ⊔ Y) ⊓ Y₁) ⊓ M₀
  have hQP : Q ≤ P := fun q hq =>
    ⟨⟨(le_sup_right : Y ≤ N ⊔ Y) (hQY hq), hQY₁ hq⟩, le_Lgen_self M L (hQL hq)⟩
  have hPY : P ⊓ Y = Q := le_antisymm (fun x hx => hY₁Y ⟨hx.1.1.2, hx.2⟩) (le_inf hQP hQY)
  have hPY₁ : P ≤ Y₁ := fun x hx => hx.1.2
  have hPNY : P ≤ N ⊔ Y := fun x hx => hx.1.1
  have hPnorm : P ≤ Subgroup.normalizer (Y : Set G) := hPY₁.trans hY₁N
  have hP2 : IsPGroup 2 ↥P := by
    have h1 : Y.relIndex (P ⊔ Y) = Y.relIndex P := relIndex_sup_right_of_le_normalizer hPnorm
    have h2 : Y.relIndex (N ⊔ Y) = Y.relIndex N := relIndex_sup_right_of_le_normalizer hNnY
    have h3 : Y.relIndex (P ⊔ Y) ∣ Y.relIndex (N ⊔ Y) :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex Y (P ⊔ Y) (N ⊔ Y) le_sup_right
        (sup_le hPNY le_sup_right))
    obtain ⟨k, hk⟩ := relIndex_two_pow_of_isPGroup Y hN2
    have h4' : Y.relIndex P = Q.relIndex P := by
      unfold Subgroup.relIndex
      congr 1
      ext x
      simp only [Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have : (x : G) ∈ P ⊓ Y := ⟨x.2, hx⟩
        rw [hPY] at this
        exact this
      · intro hx
        exact hQY hx
    rw [h1, h2, hk, h4'] at h3
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    have h5 := Subgroup.relIndex_mul_card (H := Q) (K := P)
    rw [inf_eq_left.mpr hQP] at h5
    obtain ⟨a, ha⟩ := hQ2.exists_card_eq
    exact IsPGroup.of_card (n := j + a) (by rw [← h5, hj, ha, pow_add])
  set T : Subgroup G := Y₁ ⊓ M₀ with hT
  have hPT : P ≤ T := fun x hx => ⟨hx.1.2, hx.2⟩
  have hTM₀ : T ≤ M₀ := inf_le_right
  have hPfwd : ∀ c ∈ T, ∀ x ∈ P, c * x * c⁻¹ ∈ P := by
    intro c hc' x hx
    have hcY₁ : c ∈ Y₁ := hc'.1
    have hcM₀ : c ∈ M₀ := hc'.2
    have hcNY : c ∈ Subgroup.normalizer (Y : Set G) := hY₁N hcY₁
    have hconj : conjSubgroup c (N ⊔ Y) = N ⊔ Y := by
      rw [conjSubgroup_sup', hY₁N' c hcY₁, conjSubgroup_eq_self_iff.mpr hcNY]
    refine ⟨⟨?_, Y₁.mul_mem (Y₁.mul_mem hcY₁ hx.1.2) (Y₁.inv_mem hcY₁)⟩,
      M₀.mul_mem (M₀.mul_mem hcM₀ hx.2) (M₀.inv_mem hcM₀)⟩
    rw [← hconj]
    refine mem_conjSubgroup.mpr ?_
    have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rw [e]
    exact hx.1.1
  have hPnormT : (P.subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPT]
    intro c hc'
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hPfwd c hc' z hz, fun hz => ?_⟩
    have := hPfwd c⁻¹ (T.inv_mem hc') _ hz
    have e : c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z := by group
    rwa [e] at this
  have hTnorm : (T.subgroupOf M₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTM₀]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ M₀, ∀ z ∈ T, g * z * g⁻¹ ∈ T := fun g hg z hz =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hM₀Y₁ hg) z).mp hz.1,
        M₀.mul_mem (M₀.mul_mem hg hz.2) (M₀.inv_mem hg)⟩
    intro z
    refine ⟨fun hz => key g hg z hz, fun hz => ?_⟩
    have := key g⁻¹ (M₀.inv_mem hg) _ hz
    have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rwa [e] at this
  have hM₀norm : (M₀.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hM₀M]
    exact Lgen_normalizes M L
  have hsub : CFSG.Open.IsSubnormal P M :=
    CFSG.Open.IsSubnormal.step hPT hPnormT
      (CFSG.Open.IsSubnormal.step hTM₀ hTnorm
        (CFSG.Open.IsSubnormal.step hM₀M hM₀norm (CFSG.Open.IsSubnormal.refl M)))
  have hPQ : P ≤ Q := by
    have := subnormal_pSubgroup_le_pCoreOf 2 hsub hP2
    have hQeq : pCoreOf 2 M = Q := hc.hyp.hQ.symm
    rwa [hQeq] at this
  have hQDY : Q ≤ DY M Q B Y y := (le_inf hQL hQY).trans (LB_inf_Y_le_DY M Q B Y hyL)
  intro x hx
  have hxR : x ∈ Rt M L y := hNR hx
  obtain ⟨a, haY₁, b, hbD, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (centMod_le_normalizer hQDY (DY_le_Y M Q B Y y)) (hRsup hxR)
  have hbY : b ∈ Y := DY_le_Y M Q B Y y hbD
  have hbM₀ : b ∈ M₀ := DY_le_Lgen M Q B Y y hbD
  have ha : a ∈ P := by
    have e : a = x * b⁻¹ := by rw [← hab]; group
    refine ⟨⟨?_, haY₁⟩, ?_⟩
    · rw [e]
      exact (N ⊔ Y).mul_mem ((le_sup_left : N ≤ N ⊔ Y) hx)
        ((N ⊔ Y).inv_mem ((le_sup_right : Y ≤ N ⊔ Y) hbY))
    · rw [e]
      exact M₀.mul_mem (hNM₀ hx) (M₀.inv_mem hbM₀)
  have haQ : a ∈ Q := hPQ ha
  rw [← hab]
  exact Y.mul_mem (hQY haQ) hbY

end HS9

theorem sec98End_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement) :
    Sec98EndStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 hall y hy hyQ
  exact HS9.CN_le_Y h34 h311a hs hsplit h4 hall hy hyQ

end CFSG.RankThree.GF2n.Stroth80
