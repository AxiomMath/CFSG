module

public import CFSG.Quasithin.EmptyFaithful.S153D14
public import CFSG.Quasithin.EmptyFaithful.S153D15
public import CFSG.Quasithin.EmptyFaithful.S153DGen3
public import CFSG.Quasithin.EmptyFaithful.S153DIn16
public import CFSG.Quasithin.Background.C2PushThree
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

section Generic

omit [Finite G] in
theorem conj_mem_centerOf {P : Subgroup G} {g z : G} (hg : g ∈ Subgroup.normalizer (P : Set G))
    (hz : z ∈ centerOf P) : g * z * g⁻¹ ∈ centerOf P := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hy' : g⁻¹ * y * g ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
    simpa using this
  have hc : (g⁻¹ * y * g) * z = z * (g⁻¹ * y * g) := Subgroup.mem_centralizer_iff.mp hz.2 _ hy'
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * y := by group

omit [Finite G] in
theorem le_normalizer_of_conj_mem {S D : Subgroup G} (h : ∀ g ∈ S, ∀ x ∈ D, g * x * g⁻¹ ∈ D) :
    S ≤ Subgroup.normalizer (D : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have h1 := h g⁻¹ (S.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem forall_commutator_mem_of_comm_ne {L J : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hJL : J ≤ Subgroup.normalizer (L : Set G))
    (hJN : J ≤ Subgroup.normalizer (pCoreOf 2 L : Set G)) (hne : ⁅L, J⁆ ≠ L) :
    ∀ j ∈ J, ∀ l ∈ L, ⁅j, l⁆ ∈ pCoreOf 2 L := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKL : ⁅L, J⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hJL
  have hKn : (⁅L, J⁆.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr
      (Subgroup.normalizer_commutator_ge_left L J)
  have hNn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  let πL : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hKbar : ((⁅L, J⁆.subgroupOf L).map πL).Normal :=
    hKn.map πL (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hKbar with htop | hcen
  · exfalso
    apply hne
    refine le_antisymm hKL ?_
    have hperfL : Group.IsPerfect ↥L := isPerfect_of_commutator_eq hperf
    have hQp : IsPGroup 2 (↥L ⧸ ⁅L, J⁆.subgroupOf L) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H l =>
        have hl : πL l ∈ (⁅L, J⁆.subgroupOf L).map πL := htop ▸ Subgroup.mem_top _
        obtain ⟨k, hk, hkl⟩ := hl
        have hn : k⁻¹ * l ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.mp hkl
        obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (G := ↥L) (p := 2) ⟨k⁻¹ * l, hn⟩
        refine ⟨a, ?_⟩
        have hmk : (QuotientGroup.mk l : ↥L ⧸ ⁅L, J⁆.subgroupOf L) =
            QuotientGroup.mk (k⁻¹ * l) := by
          have hl' : l = k * (k⁻¹ * l) := by group
          conv_lhs => rw [hl']
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).mpr hk, one_mul]
        rw [hmk, ← QuotientGroup.mk_pow]
        have hpow : (k⁻¹ * l) ^ 2 ^ a = 1 := by
          have := congrArg Subtype.val ha
          simpa using this
        rw [hpow, QuotientGroup.mk_one]
    have hnil : Group.IsNilpotent (↥L ⧸ ⁅L, J⁆.subgroupOf L) := hQp.isNilpotent
    have : Group.IsSolvable (↥L ⧸ ⁅L, J⁆.subgroupOf L) := inferInstance
    intro l hl
    have h1 : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : ↥L ⧸ ⁅L, J⁆.subgroupOf L) = 1 :=
      eq_one_of_isPerfect_of_isSolvable _
    have h2 : (⟨l, hl⟩ : ↥L) ∈ ⁅L, J⁆.subgroupOf L :=
      (QuotientGroup.eq_one_iff (N := ⁅L, J⁆.subgroupOf L) _).mp h1
    exact h2
  · have hKN : ⁅⁅L, J⁆, L⁆ ≤ pCoreOf 2 L := by
      rw [Subgroup.commutator_le]
      intro k hk l hl
      have hkL : k ∈ L := hKL hk
      have hcent : πL ⟨k, hkL⟩ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
        hcen ⟨⟨k, hkL⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      have h1 : πL ⁅(⟨k, hkL⟩ : ↥L), (⟨l, hl⟩ : ↥L)⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hcent (πL ⟨l, hl⟩)).symm
      exact (mem_pCore_iff _).mp ((QuotientGroup.eq_one_iff _).mp h1)
    have hcomm : ⁅⁅J, L⁆, L⁆ ≤ pCoreOf 2 L := by
      rw [Subgroup.commutator_comm J L]
      exact hKN
    have hLN : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
    have h3 := commutator_commutator_le_of_rotate hLN hLN hJN hKN hcomm
    rw [hperf] at h3
    intro j hj l hl
    have h4 : ⁅l, j⁆ ∈ pCoreOf 2 L := h3 (Subgroup.commutator_mem_commutator hl hj)
    rw [← commutatorElement_inv l j]
    exact (pCoreOf 2 L).inv_mem h4

theorem le_pCoreOf_sup_of_centralizes {R J L : Subgroup G} (hRp : IsPGroup 2 R)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hO : pCoreOf 2 (L ⊔ R) ≤ R) (hJR : J ≤ R)
    (hJ : ∀ j ∈ J, ∀ l ∈ L, ⁅j, l⁆ ∈ pCoreOf 2 L) : J ≤ pCoreOf 2 (L ⊔ R) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := pCoreOf 2 L with hN
  have hRN : R ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 L (hRL hg)
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pCoreOf 2 L
  have hNO : N ≤ R := (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
    (sup_le hLN hRN) (pCoreOf_isPGroup 2 L)).trans hO
  have hconj : ∀ {g : G}, g ∈ Subgroup.normalizer (N : Set G) → ∀ {x : G}, x ∈ N →
      g * x * g⁻¹ ∈ N := fun hg x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  let D : Subgroup G :=
    { carrier := {x | x ∈ R ∧ ∀ l ∈ L, ⁅x, l⁆ ∈ N}
      mul_mem' := by
        rintro x y ⟨hxR, hx⟩ ⟨hyR, hy⟩
        refine ⟨R.mul_mem hxR hyR, fun l hl => ?_⟩
        have : ⁅x * y, l⁆ = x * ⁅y, l⁆ * x⁻¹ * ⁅x, l⁆ := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact N.mul_mem (hconj (hRN hxR) (hy l hl)) (hx l hl)
      one_mem' := ⟨R.one_mem, fun l _ => by simp⟩
      inv_mem' := by
        rintro x ⟨hxR, hx⟩
        refine ⟨R.inv_mem hxR, fun l hl => ?_⟩
        have : ⁅x⁻¹, l⁆ = x⁻¹ * ⁅x, l⁆⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [this]
        have h1 := hconj (hRN (R.inv_mem hxR)) (N.inv_mem (hx l hl))
        simpa using h1 }
  have hDR : D ≤ R := fun x hx => hx.1
  have hDnorm : L ⊔ R ≤ Subgroup.normalizer (D : Set G) := by
    refine sup_le (le_normalizer_of_conj_mem fun g hg x hx => ?_)
      (le_normalizer_of_conj_mem fun g hg x hx => ?_)
    ·
      have hgN : g ∈ Subgroup.normalizer (N : Set G) := hLN hg
      have hc : ⁅g, x⁆ ∈ N := by
        have := N.inv_mem (hx.2 g hg)
        rwa [commutatorElement_inv] at this
      have hcR : ⁅g, x⁆ ∈ R := hNO hc
      refine ⟨?_, fun l hl => ?_⟩
      · have : g * x * g⁻¹ = ⁅g, x⁆ * x := by simp only [commutatorElement_def]; group
        rw [this]
        exact R.mul_mem hcR hx.1
      · have hgl : g⁻¹ * l * g ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hg) hl) hg
        have : ⁅g * x * g⁻¹, l⁆ = g * ⁅x, g⁻¹ * l * g⁆ * g⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact hconj hgN (hx.2 _ hgl)
    ·
      have hgN : g ∈ Subgroup.normalizer (N : Set G) := hRN hg
      refine ⟨R.mul_mem (R.mul_mem hg hx.1) (R.inv_mem hg), fun l hl => ?_⟩
      have hgl : g⁻¹ * l * g ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hRL (R.inv_mem hg)) l).mp hl
        simpa using this
      have : ⁅g * x * g⁻¹, l⁆ = g * ⁅x, g⁻¹ * l * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact hconj hgN (hx.2 _ hgl)
  have hDp : IsPGroup 2 D := hRp.to_le hDR
  have hDle : D ≤ pCoreOf 2 (L ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 (hDR.trans le_sup_right) hDnorm hDp
  exact fun j hj => hDle ⟨hJR hj, hJ j hj⟩

theorem comm_thompsonJ_eq {R L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hRp : IsPGroup 2 R)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hO : pCoreOf 2 (L ⊔ R) ≤ R)
    (hJ : ¬ thompsonJ R ≤ thompsonJ (pCoreOf 2 (L ⊔ R))) : ⁅L, thompsonJ R⁆ = L := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hJR : thompsonJ R ≤ R := thompsonJ_le_self R
  have hJL : thompsonJ R ≤ Subgroup.normalizer (L : Set G) := hJR.trans hRL
  have hJN : thompsonJ R ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 L (hJL hg)
  have hc := forall_commutator_mem_of_comm_ne hperf hq hJL hJN hne
  have hle := le_pCoreOf_sup_of_centralizes hRp hRL hO hJR hc
  exact hJ (GammaExtra.thompsonJ_eq_of_le hle hO).ge

end Generic

section Setting

omit [Finite G] in
theorem sup_R153_le {L : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hL : L ∈ cComp I) :
    L ⊔ R153 T V₁ Yp ≤ I :=
  sup_le (le_of_mem_cComp hL) ((pCoreOf_le 2 _).trans hI.1.1)

theorem pCoreOf_le_R153 (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hF : Facts15311 T M V₁ Yp I) :
    pCoreOf 2 I ≤ R153 T V₁ Yp := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_Sgp153 hF).trans le_sup_right)
    (fun g hg => le_normalizer_pCoreOf 2 I (hI.1.1 hg)) (pCoreOf_isPGroup 2 I)

theorem charTwo_sup_R153 (c : Ctx15313 T Mc M V₁ V₂ Yp I t) (hF : Facts15311 T M V₁ Yp I)
    {L : Subgroup G} (hL : L ∈ cComp I) : CharTwo (L ⊔ R153 T V₁ Yp) :=
  charTwo_of_le c.charTwo (sup_R153_le c.inH hL)
    ((pCoreOf_le_R153 c.inH hF).trans le_sup_right)

theorem pCoreOf_sup_R153_le (hF : Facts15311 T M V₁ Yp I) {L : Subgroup G} (hL : L ∈ cComp I)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hRL : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
  c2_1_pCore_le (C2Push.isTwoRadicalIn_sup_of_le_normalizer hF.radical hL hLq hRL)

theorem pCoreOf_le_pCoreOf_sup {R L : Subgroup G} (hRL : R ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ R) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (fun g hg => le_normalizer_pCoreOf 2 L hg)
      (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hRL hg)))
    (pCoreOf_isPGroup 2 L)

theorem VZ_le_centerOf (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (c : Ctx15313 T Mc M V₁ V₂ Yp I t)
    (hF : Facts15311 T M V₁ Yp I) {L : Subgroup G} (hL : L ∈ cComp I)
    (hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp) :
    VZ T M ≤ centerOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharLR := charTwo_sup_R153 c hF hL
  intro v hv
  have hvR : v ∈ centerOf (R153 T V₁ Yp) := lemma_15_3_14_one h hF hv
  have hvLR : v ∈ L ⊔ R153 T V₁ Yp := Subgroup.mem_sup_right hvR.1
  have hvC : v ∈ Subgroup.centralizer (pCoreOf 2 (L ⊔ R153 T V₁ Yp) : Set G) :=
    Subgroup.centralizer_le hO hvR.2
  exact ⟨hcharLR ⟨hvLR, hvC⟩, hvC⟩

theorem WL_le_centerOf (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (c : Ctx15313 T Mc M V₁ V₂ Yp I t)
    (hF : Facts15311 T M V₁ Yp I) {L : Subgroup G} (hL : L ∈ cComp I)
    (hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp) :
    WL153 T M L ≤ centerOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine conjClosure_le fun l hl z hz => conj_mem_centerOf ?_ (VZ_le_centerOf h c hF hL hO hz)
  exact le_normalizer_pCoreOf 2 (L ⊔ R153 T V₁ Yp) (Subgroup.mem_sup_left hl)

theorem not_le_centralizer_VZ (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {L : Subgroup G}
    (hLI : L ≤ I) (hLn : ¬ L ≤ M ⊓ I) : ¬ L ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro h1
  have hM : M = Subgroup.normalizer (VZ T M : Set G) := h.hyp.isHv_of_inM' h.hyp.inM
  have h2 : L ≤ M := hM ▸ h1.trans (Subgroup.centralizer_le_normalizer _)
  exact hLn (le_inf h2 hLI)

theorem not_le_centralizer_WL (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {L : Subgroup G}
    (hLI : L ≤ I) (hLn : ¬ L ≤ M ⊓ I) :
    ¬ L ≤ Subgroup.centralizer (WL153 T M L : Set G) := fun hc =>
  not_le_centralizer_VZ h hLI hLn (hc.trans (Subgroup.centralizer_le (le_conjClosure _ _)))

theorem isQuasisimple_autOn_WL (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (c : Ctx15313 T Mc M V₁ V₂ Yp I t) (hF : Facts15311 T M V₁ Yp I) {L : Subgroup G}
    (hL : L ∈ cComp I) (hLn : ¬ L ≤ M ⊓ I) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hRL : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G))
    (hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp) :
    CFSG.IsQuasisimple ↥(autOn L (WL153 T M L)) := by
  have hker : pCoreOf 2 L ≤ Subgroup.centralizer (WL153 T M L : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hxP : x ∈ pCoreOf 2 (L ⊔ R153 T V₁ Yp) := pCoreOf_le_pCoreOf_sup hRL hx
    exact ((Subgroup.mem_centralizer_iff.mp (WL_le_centerOf h c hF hL hO hw).2) x hxP).symm
  exact isQuasisimple_autOn (le_normalizer_conjClosure _ L) hLq hker
    (not_le_centralizer_WL h (le_of_mem_cComp hL) hLn)

theorem lemma_15_3_16
    (hC27 : ASC27Statement G) (hin : Input15316One) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (c : Ctx15313L T Mc M V₁ V₂ Yp I L t) : Concl15316 T M V₁ Yp I L := by
  obtain ⟨hLc, hLn, hL3, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  obtain ⟨hYL, hRL, -⟩ :=
    lemma_15_3_12_one h37 h38 c.ctx.hyp c.ctx.inH c.facts c.ctx.rank hLI hL3
  have hO := pCoreOf_sup_R153_le c.facts hLI hLq hRL
  have hcharL : CharTwo L :=
    charTwo_of_isSubnormal_of_charTwo c.ctx.charTwo (subnormal_of_mem_cComp hLI)
  have hdesc := c27Concl_of_statement hC27 (lemma_15_3_15_one c.ctx.hyp c.ctx.inH c.facts) hLI hLq
    hcharL hLn hRL rfl
  have hRp : IsPGroup 2 (R153 T V₁ Yp) := pCoreOf_isPGroup 2 _
  have hLeq := comm_thompsonJ_eq hLI.2.1 hLq hRp hRL hO hdesc.2.1.1
  obtain ⟨hR1, hR2⟩ := hin G T Mc M V₁ V₂ Yp I L t c hRL hO hdesc
  exact ⟨hR1, hR2, isQuasisimple_autOn_WL c.ctx.hyp c.ctx c.facts hLI hLn hLq hRL hO, hYL, hRL,
    hLeq, hdesc⟩

end Setting

end S153D

end CFSG.Quasithin
