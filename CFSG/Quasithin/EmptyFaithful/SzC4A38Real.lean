module

public import CFSG.Quasithin.EmptyFaithful.SzC4NdG
public import CFSG.Quasithin.EmptyFaithful.SzC4Chir4
public import CFSG.Quasithin.EmptyFaithful.SzC4ChiInst
public import CFSG.Quasithin.Background.C134L32CorrM
public import CFSG.Quasithin.EmptyFaithful.A38c10Cases
public import CFSG.Quasithin.EmptyFaithful.A38c10Ctx
public import CFSG.Quasithin.EmptyFaithful.A38c10MSc
public import CFSG.Quasithin.EmptyFaithful.A38c10Main
public import CFSG.Quasithin.EmptyFaithful.T1531In62

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.FLc CFSG.Quasithin CFSG.Quasithin.A38c10
open scoped commutatorElement Pointwise

theorem hyp6_of_msgat {G : Type} [Group G] [Finite G] {L S Vp Yp Y₁ Y₂ : Subgroup G}
    {α : ↥L →* SLt 4} (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hS2 : IsPGroup 2 ↥S) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {k : ℕ}
    {ψ : ↥(Pof L α k) →* SLt 3} {q : G} (hm : MSGat L S Vp Yp Y₁ Y₂ (Pof L α k) ψ q) :
    Hyp6 L S α (QI 4 {k}) ∧ IsLnTwoQuot (perfectCore (PP L α (QI 4 {k}))) 3 := by
  obtain ⟨-, hSLP, -, hSP, -, -, hψs, hψk, -⟩ := hm
  have hPsi : MS.PsiData (Pof L α k) S ψ := ⟨hS2, hψs, fun x hx => (hψk x hx).1⟩
  have hSN : S ≤ Subgroup.normalizer (Pof L α k : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hSP s hs p hp, fun hp => ?_⟩
    have h1 := hSP s⁻¹ (S.inv_mem hs) _ hp
    have e : s⁻¹ * (s * p * s⁻¹) * s⁻¹⁻¹ = p := by group
    rwa [e] at h1
  refine ⟨⟨hαs, hαk, hS2, hSL, hSN, hSLP, MS.le_perfectCore_sup hPsi,
    fun x hx ho => MS.mem_perfectCore_of_odd hPsi hx ho⟩, ?_⟩
  obtain ⟨α₀, hα₀⟩ := MS.exists_isModO2Surj hPsi
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hα₀.2.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α₀ hα₀.1)⟩

variable {G : Type} [Group G] [Finite G]

theorem chiC_c134Q_eq_zero_corrM (A : ChiAPI) {H S K : Subgroup G} (hq : IsLnTwoQuot K 3)
    (hcase : C134Case4Min H S K) (hQ2 : IsPGroup 2 ↥(c134Q H K)) {g : G} (hg : g ∈ K)
    (hg7 : g ^ 7 = 1) : chiC A (c134Q H K) g = 0 := by
  obtain ⟨⟨n, F, iF, iFin, α, hcard, hα, hcen, hdisj, h1, ⟨A₃, A₄, h2, h3, h4⟩, -⟩, -⟩ := hcase
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hcard hα
  set Q := c134Q H K with hQ
  set Zq := centerOf Q with hZq
  set C := c134CQ H K with hC
  set U : Subgroup G := ⁅centerOf Q, K⁆ with hU
  have hZQ : Zq ≤ Q := inf_le_left
  have hCZ : C ≤ Zq := hcen ▸ le_sup_left
  have hUZ : U ≤ Zq := hcen ▸ le_sup_right
  have hA4Q : A₄ ≤ Q := h4.2.1
  have hA3Q : A₃ ≤ Q := h3.2.1.trans hA4Q
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := h4.1 hg
  have hgU : g ∈ Subgroup.normalizer (U : Set G) := h1.1 hg
  have hgA3 : g ∈ Subgroup.normalizer (A₃ : Set G) := h2.1 hg
  have hgZ : g ∈ Subgroup.normalizer (Zq : Set G) := normalizes_of_isSum h2 hg
  have hgA4 : g ∈ Subgroup.normalizer (A₄ : Set G) := h3.1 hg
  have hCcent : ∀ c ∈ C, g * c * g⁻¹ = c := by
    intro c hc
    have := Subgroup.mem_centralizer_iff.1 hc.2 g hg
    calc g * c * g⁻¹ = c * g * g⁻¹ := by rw [this]
      _ = c := by group
  have hgC : g ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [hCcent c hc]
      exact hc
    · intro hc
      have h := hCcent _ hc
      have h' : g * c * g⁻¹ = c := by
        calc g * c * g⁻¹ = g⁻¹ * (g * (g * c * g⁻¹) * g⁻¹) * g := by group
          _ = g⁻¹ * (g * c * g⁻¹) * g := by rw [h]
          _ = c := by group
      rw [h'] at hc
      exact hc
  have hcomm : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c := by
    intro c hc u hu
    have hcZ : c ∈ Subgroup.centralizer (Q : Set G) := (hCZ hc).2
    have huQ : u ∈ Q := hZQ (hUZ hu)
    exact (Subgroup.mem_centralizer_iff.1 hcZ u huQ).symm
  have e4 := chiC_layer A hF h4 hQ2 hg hg7
  have e3 := chiC_layer A hF h3 (hQ2.to_le hA4Q) hg hg7
  have e2 := chiC_layer A hF h2 (hQ2.to_le hA3Q) hg hg7
  have e1 := chiC_layer A hF h1 (hQ2.to_le (hUZ.trans hZQ)) hg hg7
  have hsplit := chiC_split A (hQ2.to_le hZQ) hCZ hUZ hcomm hdisj hcen.symm hgZ hgC hgU hg7
  rw [chiC_bot A g] at e1
  rw [chiC_of_centralizes A C hgC hCcent] at hsplit
  have hg7' : α ⟨g, hg⟩ ^ 7 = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥K) ^ 7 = 1 := Subtype.ext (by simpa using hg7)
    rw [this, map_one]
  have hd := chiMat_dual A hF (α ⟨g, hg⟩ : Matrix.GeneralLinearGroup (Fin 3) F)
    (by simpa using congrArg Subtype.val hg7')
  rw [hd] at e3 e2
  push_cast at e4 e3 e2 e1
  linarith

theorem chiC_X_corrM (A : ChiAPI) {L S : Subgroup G} {α : ↥L →* SLt 4} {Pbar Rbar : Subgroup (SLt 4)}
    {gb : SLt 4} (h : Hyp6 L S α Pbar) (hpb : (1 : SLt 4) ∈ Pbar) (hPD : ParabData Pbar Rbar gb)
    (hq : IsLnTwoQuot (perfectCore (PP L α Pbar)) 3)
    (hcase : C134Case4Min (perfectCore (PP L α Pbar) ⊔ S) S (perfectCore (PP L α Pbar)))
    {g : G} (hgK : g ∈ perfectCore (PP L α Pbar)) (hgL : g ∈ L) (hg : α ⟨g, hgL⟩ = gb)
    (hg7 : g ^ 7 = 1) :
    chiC A (pCoreOf 2 L) g = - A.chi ↥Rbar (conjOn Rbar gb hPD.gb_normalizes) := by
  set P := PP L α Pbar with hP
  set K := perfectCore P with hK
  set X := pCoreOf 2 L with hX
  set Q := c134Q (K ⊔ S) K with hQ
  have hKP : K ≤ P := perfectCore_le P
  have hKL : K ≤ L := hKP.trans PP_le
  have hQle := Q_le h
  have hQL : Q ≤ L := fun q hq => (hQle hq).2
  have hQ2 : IsPGroup 2 ↥Q := (pCoreOf_isPGroup 2 (K ⊔ S)).to_le (fun q hq => (hQle hq).1)
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_left hl)
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) :=
    SBd5.mem_normalizer_commutator_of (hKO hgK) (Subgroup.le_normalizer hgK)
  have hgX : g ∈ Subgroup.normalizer (X : Set G) := le_normalizer_pCoreOf 2 L (hKL hgK)
  have hgQ0 : g ∈ Subgroup.normalizer ((Q ⊓ X : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hgQ, hgX⟩
  have hQ0Q : Q ⊓ X ≤ Q := inf_le_left
  have hQ0X : Q ⊓ X ≤ X := inf_le_right
  have e0 : chiC A Q g = 0 := chiC_c134Q_eq_zero_corrM A hq hcase hQ2 hgK hg7
  have hαQ := alphaQ_le h hPD
  have hlift := exists_lift h hPD hgK hgL hg
  let π0 : ↥Q →* SLt 4 := α.comp (Subgroup.inclusion hQL)
  have hπ0 : ∀ q : ↥Q, π0 q ∈ Rbar := fun q => (hαQ q q.2).choose_spec
  let π : ↥Q →* ↥Rbar := π0.codRestrict Rbar hπ0
  have hπs : Function.Surjective π := by
    intro r
    obtain ⟨q, hqQ, hqL, hqr⟩ := hlift r r.2
    exact ⟨⟨q, hqQ⟩, Subtype.ext hqr⟩
  have hker : ∀ y : ↥Q, π y = 1 ↔ (y : G) ∈ Q ⊓ X := by
    intro y
    have h1 : π y = 1 ↔ α ⟨y, hQL y.2⟩ = 1 := by
      constructor
      · intro hy
        have := congrArg Subtype.val hy
        exact this
      · intro hy
        exact Subtype.ext hy
    rw [h1, alpha_eq_one_iff h.ker]
    exact ⟨fun hyX => ⟨y.2, hyX⟩, fun hy => hy.2⟩
  have hφ : ∀ y : ↥Q, π (conjOn Q g hgQ y) =
      conjOn Rbar gb hPD.gb_normalizes (π y) := by
    intro y
    apply Subtype.ext
    show α ⟨g * y * g⁻¹, _⟩ = gb * α ⟨y, hQL y.2⟩ * gb⁻¹
    rw [← hg]
    have : (⟨g * y * g⁻¹, _⟩ : ↥L) = ⟨g, hgL⟩ * ⟨y, hQL y.2⟩ * ⟨g, hgL⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have e1 := chiC_exact A hQ2 hQ0Q hgQ hgQ0 hg7 π hπs hker
    (conjOn Rbar gb hPD.gb_normalizes) hφ
  have hQnorm : ((Q ⊓ X).subgroupOf X).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    ·
      have hxH : (x : G) ∈ K ⊔ S := (X_le_PP h.ker hpb |>.trans h.PKS) x.2
      have hQN : K ⊔ S ≤ Subgroup.normalizer (Q : Set G) := by
        refine sup_le (fun k hk => ?_) (fun s hs => ?_)
        · exact SBd5.mem_normalizer_commutator_of (hKO hk) (Subgroup.le_normalizer hk)
        · have hSO : s ∈ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) :=
            le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_right hs)
          have hSK : s ∈ Subgroup.normalizer (K : Set G) :=
            normalizer_le_normalizer_perfectCore P (h.SP hs)
          exact SBd5.mem_normalizer_commutator_of hSO hSK
      exact (Subgroup.mem_normalizer_iff.mp (hQN hxH) n).mp hn.1
    · exact X.mul_mem (X.mul_mem x.2 hn.2) (X.inv_mem x.2)
  let π' : ↥X →* ↥X ⧸ (Q ⊓ X).subgroupOf X := QuotientGroup.mk' ((Q ⊓ X).subgroupOf X)
  have hπ's : Function.Surjective π' := QuotientGroup.mk'_surjective _
  have hker' : ∀ y : ↥X, π' y = 1 ↔ (y : G) ∈ Q ⊓ X := by
    intro y
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hφ' : ∀ y : ↥X, π' (conjOn X g hgX y) = (1 : MulAut (↥X ⧸ (Q ⊓ X).subgroupOf X)) (π' y) := by
    intro y
    show π' (conjOn X g hgX y) = π' y
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have := comm_X_K h hpb (x := (y : G)⁻¹) (k := g) (X.inv_mem y.2) hgK
    have e : ((conjOn X g hgX y)⁻¹ * y : ↥X) = ⟨g * (y : G)⁻¹ * g⁻¹ * ((y : G)⁻¹)⁻¹, by
      have h2 : g * (y : G)⁻¹ * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hgX _).mp (X.inv_mem y.2)
      exact X.mul_mem h2 (by simp)⟩ := by
      apply Subtype.ext
      simp [conjOn_apply, mul_assoc]
    rw [e]
    exact this
  have e2 := chiC_exact A (pCoreOf_isPGroup 2 L) hQ0X hgX hgQ0 hg7 π' hπ's hker' 1 hφ'
  rw [A.chi_one] at e2
  linarith

theorem chirality4_corrM (A : ChiAPI) {L S : Subgroup G} {α : ↥L →* SLt 4}
    (h1 : Hyp6 L S α (QI 4 {1})) (h3 : Hyp6 L S α (QI 4 {3}))
    (hq1 : IsLnTwoQuot (perfectCore (PP L α (QI 4 {1}))) 3)
    (hq3 : IsLnTwoQuot (perfectCore (PP L α (QI 4 {3}))) 3)
    (hc1 : C134Case4Min (perfectCore (PP L α (QI 4 {1})) ⊔ S) S
      (perfectCore (PP L α (QI 4 {1}))))
    (hc3 : C134Case4Min (perfectCore (PP L α (QI 4 {3})) ⊔ S) S
      (perfectCore (PP L α (QI 4 {3})))) : False := by
  obtain ⟨l, hlg, hl7⟩ := exists_lift_order_seven h1.ker h1.surj gb1_pow
  have hlP1 : (l : G) ∈ PP L α (QI 4 {1}) := mem_PP.2 ⟨l.2, by
    have : (⟨(l : G), l.2⟩ : ↥L) = l := rfl
    rw [this, hlg]
    exact gb1_mem⟩
  have hg7 : (l : G) ^ 7 = 1 := by
    have := congrArg Subtype.val hl7
    simpa using this
  have hord : Odd (orderOf (l : G)) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hg7)
  have hgK1 : (l : G) ∈ perfectCore (PP L α (QI 4 {1})) := h1.odd _ hlP1 hord
  obtain ⟨w, hw⟩ := h1.surj wb
  have hα' : α (w * l * w⁻¹) = gb3 := by
    rw [map_mul, map_mul, map_inv, hw, hlg, gb3_eq]
  have hg'7 : ((w * l * w⁻¹ : ↥L) : G) ^ 7 = 1 := by
    have : (w * l * w⁻¹) ^ 7 = 1 := by
      rw [conj_pow, hl7]
      group
    simpa using congrArg Subtype.val this
  have hg'P3 : ((w * l * w⁻¹ : ↥L) : G) ∈ PP L α (QI 4 {3}) := mem_PP.2 ⟨(w * l * w⁻¹).2, by
    rw [hα']
    exact gb3_mem⟩
  have hord' : Odd (orderOf ((w * l * w⁻¹ : ↥L) : G)) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hg'7)
  have hgK3 : ((w * l * w⁻¹ : ↥L) : G) ∈ perfectCore (PP L α (QI 4 {3})) :=
    h3.odd _ hg'P3 hord'
  have e1 := chiC_X_corrM A h1 (one_mem _) parabData1 hq1 hc1 hgK1 l.2 hlg hg7
  have e3 := chiC_X_corrM A h3 (one_mem _) parabData3 hq3 hc3 hgK3 (w * l * w⁻¹).2 hα' hg'7
  rw [chi_Rrad1] at e1
  rw [chi_Rrad3] at e3
  have hF : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  have hdual := A.chiMat_inv_transpose hF Cm Cm_pow
  have hne := A.chiMat_ne_zero hF Cm Cm_pow Cm_ne
  have hwN : (w : G) ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L w.2
  have hlN : (l : G) ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L l.2
  have e4 := chiC_conj A (pCoreOf 2 L) hwN hlN
  have e5 : ((w * l * w⁻¹ : ↥L) : G) = (w : G) * (l : G) * (w : G)⁻¹ := rfl
  rw [e5, e4] at e3
  unfold CmT at e1
  have h0 : A.chiMat Cm = 0 := by linarith
  exact hne h0

theorem case4_of_msgat_corrM (hC34 : C134L32CorrM) {G : Type} [Group G] [Finite G]
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hYY : Yp = Y153 Mc M) (hYpL : Yp ≤ L)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    (hodd1 : ∀ y ∈ Yp, Odd (orderOf y) → (∀ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ = z) → y = 1)
    {Vp Y₁ Y₂ : Subgroup G} (hVp2 : IsPGroup 2 ↥Vp) (hVpS : Vp ≤ Sgp153 T V₁)
    (hVL : L ≤ Subgroup.normalizer (Vp : Set G)) (hVS : Sgp153 T V₁ ≤ Subgroup.normalizer (Vp : Set G))
    (hY₁ : Y₁ ≤ Yp) (hY₂ : Y₂ ≤ Yp) (hY₁c : ∃ a, Nat.card ↥Y₁ = 2 ^ a * 3)
    (hY₂c : ∃ a, Nat.card ↥Y₂ = 2 ^ a * 3)
    (P : Subgroup G) (ψ : ↥P →* SLt 3) (q : G) (hPL : P ≤ L) (hSLP : Sgp153 T V₁ ⊓ L ≤ P)
    (hSP : ∀ s ∈ Sgp153 T V₁, ∀ p ∈ P, s * p * s⁻¹ ∈ P)
    (hmin : ∀ X : Subgroup G, Sgp153 T V₁ ⊓ L ≤ X → X ≤ L → X ≠ L → Yp ≤ X → ¬ P ≤ X)
    (hYP : Y₁ ≤ P ∨ Y₂ ≤ P) (hψs : Function.Surjective ψ)
    (hψk : ∀ x : ↥P, ψ x = 1 → (x : G) ∈ Sgp153 T V₁ ⊓ L) (hq1 : q ≠ 1)
    (hqP : ∀ a ∈ P, a * q * a⁻¹ = q) (hqK : q ∈ ⁅Vp, oTwoUpper P⁆) :
    C134Case4Min (perfectCore P ⊔ Sgp153 T V₁) (Sgp153 T V₁) (perfectCore P) := by
  classical
  set S : Subgroup G := Sgp153 T V₁ with hSdef
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  obtain ⟨hLc, hLn, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSI : S ≤ I := c.facts.sylow.1
  have hS2 : IsPGroup 2 ↥S := hyp.qtfe.sylow.1.to_le inf_le_left
  have hST : S ≤ T := inf_le_left
  have hTM : T ≤ M := hyp.T_le
  have hcharL : CharTwo L :=
    charTwo_of_isSubnormal_of_charTwo c.ctx.charTwo (subnormal_of_mem_cComp hLI)
  have hPsi : MS.PsiData P S ψ := ⟨hS2, hψs, fun x hx => (hψk x hx).1⟩
  set K : Subgroup G := perfectCore P with hKdef
  have hKP : K ≤ P := perfectCore_le P
  have hKL : K ≤ L := hKP.trans hPL
  have hKI : K ≤ I := hKL.trans hLle
  have hSN : S ≤ Subgroup.normalizer (P : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hSP s hs p hp, fun hp => ?_⟩
    have h1 := hSP s⁻¹ (S.inv_mem hs) _ hp
    have e : s⁻¹ * (s * p * s⁻¹) * s⁻¹⁻¹ = p := by group
    rwa [e] at h1
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := fun s hs =>
    normalizer_le_normalizer_perfectCore P (hSN hs)
  have hsupeq : K ⊔ S = P ⊔ S := MS.perfectCore_sup_eq hPsi
  have hPKS : P ≤ K ⊔ S := MS.le_perfectCore_sup hPsi
  have hoT : oTwoUpper P ≤ K := MS.oTwoUpper_le_perfectCore hPsi
  have hset : ((K ⊔ S : Subgroup G) : Set G) = (K : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K S hSK
  obtain ⟨α, hα⟩ := MS.exists_isModO2Surj hPsi
  have hq3 : IsLnTwoQuot K 3 :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα.1)⟩
  have hLie := SBd7.isRankTwoLie2Derived_of_modO2 α hα.1 hα.2
  have hcomp : K ∈ cComp (K ⊔ S) := SBd5.mem_cComp_sup' (MS.perfectCore_mem_cComp_self hPsi) hSK
  have hLSN : L ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer hx) hSL
  have hsylLS : IsSylowTwoOf S (L ⊔ S) :=
    SBd7.isSylowTwoOf_of_le_of_le' c.facts.sylow le_sup_right (sup_le hLle hSI)
  have hOLS : pCoreOf 2 L ≤ S := by
    have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
        (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hLSN hg)) (pCoreOf_isPGroup 2 L)
    exact hOL.trans (pCoreOf_le_of_isSylowTwoOf hsylLS)
  have hOP : pCoreOf 2 L ≤ P := fun x hx => hSLP ⟨hOLS hx, pCoreOf_le 2 L hx⟩
  have hchar : CharTwo (K ⊔ S) := by
    rw [hsupeq]
    exact MS.charTwo_sup_of_le hcharL hS2 hSL hPL (hOP.trans le_sup_left)
  obtain ⟨y, hyYp, hyP, hy3⟩ := MS.exists_order_three hY₁ hY₂ hY₁c hY₂c hYP
  have hyodd : Odd (orderOf y) := by rw [hy3]; decide
  have hyK : y ∈ K := MS.mem_perfectCore_of_odd hPsi hyP hyodd
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy3; omega
  have hmove : ∃ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ ≠ z := by
    by_contra hcon
    push Not at hcon
    exact hy1 (hodd1 y hyYp hyodd hcon)
  have hV' : ⁅VZ T M, oTwoUpper (Y153 Mc M ⊓ K)⁆ ≠ ⊥ := by
    obtain ⟨z, hzZ, hzy⟩ := hmove
    have hzV : z ∈ VZ T M := hyp.Z_le_VZ hzZ
    have hyO : y ∈ oTwoUpper (Y153 Mc M ⊓ K) :=
      mem_oTwoUpper_of_odd ⟨by rw [← hYY]; exact hyYp, hyK⟩ hyodd
    intro hb
    have hc' : ⁅z, y⁆ ∈ ⁅VZ T M, oTwoUpper (Y153 Mc M ⊓ K)⁆ :=
      Subgroup.commutator_mem_commutator hzV hyO
    rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc'
    apply hzy
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [← hc']
      _ = z := by group
  have hKM : ¬ K ≤ M := by
    intro hKM
    have hSM : S ≤ M := hST.trans hTM
    have hPM : P ≤ M := hPKS.trans (sup_le hKM hSM)
    have hLM : ¬ L ≤ M := fun h => hLn (le_inf h hLle)
    refine hmin (M ⊓ L) (fun x hx => ⟨hSM hx.1, hx.2⟩) inf_le_right
      (fun h => hLM (h.symm.le.trans inf_le_left)) ?_ (le_inf hPM hPL)
    exact le_inf (by rw [hYY]; exact Y153_le Mc M) hYpL
  have hMSp : IsMSPair (K ⊔ S) S :=
    MS.isMSPair_sup_S_of_K c hKI hSK hchar hcomp hLie hKM hV'
  have hKSI : K ⊔ S ≤ I := sup_le hKI hSI
  have hsyl : IsSylowTwoOf S (K ⊔ S) :=
    SBd7.isSylowTwoOf_of_le_of_le' c.facts.sylow le_sup_right hKSI
  obtain ⟨i, hi⟩ := hC34 G (K ⊔ S) S K hMSp hcomp hset
    ⟨ZMod 2, inferInstance, inferInstance, α, ZMod.card 2, hα⟩
  have hVpH : Vp ≤ pCoreOf 2 (K ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 (hVpS.trans le_sup_right) (sup_le (hKL.trans hVL) hVS) hVp2
  have hqQ : q ∈ c134Q (K ⊔ S) K := Subgroup.commutator_mono hVpH hoT hqK
  have hqfix : ∀ a ∈ K, a * q * a⁻¹ = q := fun a ha => hqP a (hKP ha)
  have hOSyl : pCoreOf 2 (K ⊔ S) ≤ S := pCoreOf_le_of_isSylowTwoOf hsyl
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_left hl)
  have hSO : S ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) := fun s hs =>
    le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_right hs)
  have hQO : c134Q (K ⊔ S) K ≤ pCoreOf 2 (K ⊔ S) := by
    refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (K ⊔ S) :=
      (Subgroup.mem_normalizer_iff.mp (hKO hl) _).mp ((pCoreOf 2 (K ⊔ S)).inv_mem hx)
    have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [commutatorElement_def, e]
    exact (pCoreOf 2 (K ⊔ S)).mul_mem hx h1
  have hQS : c134Q (K ⊔ S) K ≤ S := hQO.trans hOSyl
  have hKQ : K ≤ Subgroup.normalizer (c134Q (K ⊔ S) K : Set G) := fun l hl =>
    SBd5.mem_normalizer_commutator_of (hKO hl) (Subgroup.le_normalizer hl)
  have hSQ : S ≤ Subgroup.normalizer (c134Q (K ⊔ S) K : Set G) := fun s hs =>
    SBd5.mem_normalizer_commutator_of (hSO hs) (hSK hs)
  match i, hi with
  | 0, hi => exact hi.elim
  | 1, hi =>
    exact (MS.false_of_case_one_two_three (show IsC134Case 1 (K ⊔ S) S K from hi) (Or.inl rfl) hqQ
      hq1 hqfix).elim
  | 2, hi =>
    exact (MS.false_of_case_one_two_three (show IsC134Case 2 (K ⊔ S) S K from hi)
      (Or.inr (Or.inl rfl)) hqQ hq1 hqfix).elim
  | 3, hi =>
    exact (MS.false_of_case_one_two_three (show IsC134Case 3 (K ⊔ S) S K from hi)
      (Or.inr (Or.inr rfl)) hqQ hq1 hqfix).elim
  | 4, hi => exact hi
  | 5, hi =>
    exfalso
    obtain ⟨-, h5⟩ := hi
    obtain ⟨hΩ, -⟩ := h5 S hsyl le_rfl
    have hV₁T : V₁ ≤ T := hh.decomp.le₁.trans hyp.VZ_le_T
    have hZΩ : quasithinOmegaOneCenter T ≤ omegaOneCenterOf S := by
      refine Subgroup.closure_mono ?_
      rintro z ⟨⟨hzT, hzC⟩, hz2⟩
      have hzS : z ∈ S := ⟨hzT, Subgroup.centralizer_le_normalizer (V₁ : Set G)
        (Subgroup.centralizer_le hV₁T hzC)⟩
      exact ⟨⟨hzS, Subgroup.centralizer_le hST hzC⟩, hz2⟩
    refine hy1 (hodd1 y hyYp hyodd fun z hz => ?_)
    have hzC := (hΩ (hZΩ hz)).2
    have h1 := Subgroup.mem_centralizer_iff.mp hzC y (Subgroup.mem_sup_left hyK)
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [h1]
      _ = z := by group
  | n + 6, hi => exact hi.elim

theorem ms_false_corr2M (hC34 : C134L32CorrM) {G : Type} [Group G] [Finite G]
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hYY : Yp = Y153 Mc M) (hYpL : Yp ≤ L)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    (hodd1 : ∀ y ∈ Yp, Odd (orderOf y) → (∀ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ = z) → y = 1)
    {Vp Y₁ Y₂ : Subgroup G} (hVp2 : IsPGroup 2 ↥Vp) (hVpS : Vp ≤ Sgp153 T V₁)
    (hVL : L ≤ Subgroup.normalizer (Vp : Set G))
    (hVS : Sgp153 T V₁ ≤ Subgroup.normalizer (Vp : Set G))
    (hY₁ : Y₁ ≤ Yp) (hY₂ : Y₂ ≤ Yp) (hY₁c : ∃ a, Nat.card ↥Y₁ = 2 ^ a * 3)
    (hY₂c : ∃ a, Nat.card ↥Y₂ = 2 ^ a * 3)
    (hV : MSG2 L (Sgp153 T V₁) Vp Yp Y₁ Y₂) : False := by
  obtain ⟨α, hαs, hαk, -, ⟨ψ₁, q₁, hm₁⟩, ⟨ψ₃, q₃, hm₃⟩⟩ := hV
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hh.hyp.qtfe.sylow.1.to_le inf_le_left
  obtain ⟨h₁, hq₁⟩ := hyp6_of_msgat hαs hαk hS2 hSL hm₁
  obtain ⟨h₃, hq₃⟩ := hyp6_of_msgat hαs hαk hS2 hSL hm₃
  obtain ⟨hPL₁, hSLP₁, -, hSP₁, hmin₁, hYP₁, hψs₁, hψk₁, -, hq1₁, hqP₁, hqK₁⟩ := hm₁
  obtain ⟨hPL₃, hSLP₃, -, hSP₃, hmin₃, hYP₃, hψs₃, hψk₃, -, hq1₃, hqP₃, hqK₃⟩ := hm₃
  have hc₁ := case4_of_msgat_corrM hC34 c hYY hYpL hSL hodd1 hVp2 hVpS hVL hVS hY₁ hY₂ hY₁c hY₂c
    (Pof L α 1) ψ₁ q₁ hPL₁ hSLP₁ hSP₁ hmin₁ hYP₁ hψs₁ hψk₁ hq1₁ hqP₁ hqK₁
  have hc₃ := case4_of_msgat_corrM hC34 c hYY hYpL hSL hodd1 hVp2 hVpS hVL hVS hY₁ hY₂ hY₁c hY₂c
    (Pof L α 3) ψ₃ q₃ hPL₃ hSLP₃ hSP₃ hmin₃ hYP₃ hψs₃ hψk₃ hq1₃ hqP₃ hqK₃
  exact chirality4_corrM chiAPI h₁ h₃ hq₁ hq₃ hc₁ hc₃

theorem l4Four_holds_corr2M (h113 : StageLemma14113) (h36 : Input15336One) (h51 : AsB51)
    (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) (hC34 : C134L32CorrM) : L4Four := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c17 hq
  obtain ⟨Y₁, Y₂, E⟩ := env4_of_ctx h113 h36 c c17 hq
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hF : Facts15311 T M V₁ Yp I := c.facts
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLIc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
    S153D.pCoreOf_sup_R153_le hF hLIc hLq hRN
  have hVZ : VZ T M ≤ VL153 T V₁ Yp L := S153D.VZ_le_VL153 hh c.ctx hF hLIc hO
  obtain ⟨y₀, hy₀, z, hzZ, hy₀z⟩ := exists_moves_Z h113 hh
  have hzVp : z ∈ VL153 T V₁ Yp L := hVZ (hh.hyp.Z_le_VZ hzZ)
  have hzB : ∀ b ∈ Sgp153 T V₁ ⊓ L, b * z * b⁻¹ = z := by
    intro b hb
    have hbT : b ∈ T := (inf_le_left : Sgp153 T V₁ ≤ T) hb.1
    have := Subgroup.mem_centralizer_iff.mp (hh.hyp.T_le_centralizer_Z hbT) z hzZ
    calc b * z * b⁻¹ = z * b * b⁻¹ := by rw [← this]
      _ = z := by group
  have hzY : ∃ y ∈ Y₁ ⊔ Y₂, y * z * y⁻¹ ≠ z := ⟨y₀, E.Yp_Y hy₀, hy₀z⟩
  obtain ⟨hsplit, -, hkey, htri⟩ := vmain_G2 h51 hI16 hA8 E hzVp hzB hzY
  rcases hh.cases with hY | ⟨hU, hY⟩
  ·
    exfalso
    have hE : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) := by
      rcases hF.struct_Yp with h | h
      · exact h
      · exfalso
        have h27 : Nat.card (OTwoQuot Yp) = 3 ^ 3 := h.2.1
        apply not_dvd_27_card_of_quot4 hq
        have h1 : Nat.card (OTwoQuot Yp) ∣ Nat.card Yp := Subgroup.card_quotient_dvd_card _
        have h2 : Nat.card Yp ∣ Nat.card L := Subgroup.card_dvd_of_le E.Yp_L
        rw [h27] at h1
        exact (by norm_num : (27 : ℕ) = 3 ^ 3) ▸ h1.trans h2
    have hodd1 : ∀ y ∈ Yp, Odd (orderOf y) →
        (∀ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ = z) → y = 1 := fun y hy hodd hz =>
      odd_centralizes_Z_trivial h113 hh hY hE hy hodd hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      exact hy₀z (by group)
    have hZ := Z_eq_zpowers hh.hyp hzZ hz1
    have hfixZ : ∀ y : G, (y * z * y⁻¹ = z) →
        ∀ z' ∈ quasithinOmegaOneCenter T, y * z' * y⁻¹ = z' := by
      intro y hy z' hz'
      rw [hZ] at hz'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
      calc y * z ^ k * y⁻¹ = (y * z * y⁻¹) ^ k := by rw [conj_zpow]
        _ = z ^ k := by rw [hy]
    rcases htri with h1 | h2 | hms
    · obtain ⟨y, hy, hord⟩ := exists_order_three_of_card E.Y₁_card
      have := hodd1 y (E.Y₁_Yp hy) (by rw [hord]; decide) (hfixZ y (h1 y hy))
      rw [this, orderOf_one] at hord
      omega
    · obtain ⟨y, hy, hord⟩ := exists_order_three_of_card E.Y₂_card
      have := hodd1 y (E.Y₂_Yp hy) (by rw [hord]; decide) (hfixZ y (h2 y hy))
      rw [this, orderOf_one] at hord
      omega
    · have hRS : R153 T V₁ Yp ≤ Sgp153 T V₁ := by
        intro r hr
        have hr' := hF.R_eq ▸ hr
        refine ⟨hr'.1, ?_⟩
        have h1 : r ∈ Subgroup.centralizer (V₁ : Set G) :=
          Subgroup.centralizer_le hh.decomp.le₁ hr'.2
        exact Subgroup.centralizer_le_normalizer (V₁ : Set G) h1
      have hVpR : VL153 T V₁ Yp L ≤ R153 T V₁ Yp :=
        ((Subgroup.closure_le _).2 fun x hx => hx.1.1).trans hO
      have hVp2 : IsPGroup 2 ↥(VL153 T V₁ Yp L) := fun x =>
        ⟨1, Subtype.ext (by simpa using E.Vp_elem.2 x x.2)⟩
      exact ms_false_corr2M hC34 c hY E.Yp_L E.S_L hodd1 hVp2 (hVpR.trans hRS) E.L_N E.S_N E.Y₁_Yp
        E.Y₂_Yp E.Y₁_card E.Y₂_card hms
  ·
    refine ⟨⟨hU, hY⟩, ?_⟩
    have hV₁Vp : V₁ ≤ VL153 T V₁ Yp L := hh.decomp.le₁.trans hVZ
    have hYV₁ : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
      rw [hY]
      exact (oTwoUpper_le _).trans inf_le_right
    have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hh.hyp.qtfe.sylow.1.to_le inf_le_left
    have hVc : V₁ ≤ Subgroup.centralizer (L : Set G) :=
      closeV (fun a ha b hb => congrArg Subtype.val (E.Vp_elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
        E.Vp_elem.2 E.L_N hS2 hsplit hkey hV₁Vp inf_le_right hYV₁ (sup_le E.Y₁_Yp E.Y₂_Yp) E.Yp_L
    exact Subgroup.le_centralizer_iff.mp hVc

end CFSG.Quasithin.SzC4
