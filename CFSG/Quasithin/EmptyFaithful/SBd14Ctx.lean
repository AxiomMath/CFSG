module

public import CFSG.Quasithin.EmptyFaithful.SBd14Grp
public import CFSG.Quasithin.EmptyFaithful.SBd7Gen
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.SBd4Close
public import CFSG.Quasithin.EmptyFaithful.SBd9Borel
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

structure RestHyp {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) : Prop where
  ctx : CtxComp2 T Mc M V₁ V₂ Yp I L t
  hL0 : L = conjClosure L (Sgp153 T V₁)
  hn2 : IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L)
  hYL : oTwoUpper (Yp ⊓ L) ≠ ⊥
  hy : ∃ y ∈ Yp, orderOf y = 3 ∧ y ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
    Yp = oTwoUpper (Yp ⊓ L) ⊔ Subgroup.zpowers y ⊔ pCoreOf 2 Yp
  hY : ¬ Yp ≤ L
  hNL : I ≤ Subgroup.normalizer (L : Set G)
  hYY : Yp = Y153 Mc M
  hB : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G)
  hBM : L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I
  hQV : Sgp153 T V₁ ⊓ L ≤ Subgroup.centralizer (VZ T M : Set G)
  h1 : V₁ ≤ Subgroup.centralizer (L : Set G)
  h2 : ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y
  h3 : V₂ ≤ oTwoUpper (Yp ⊓ L)
  h4 : ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem le_Q_of_two {Q X : Subgroup G} (hQ : IsSylowTwoOf Q L) (hXL : X ≤ L)
    (hXN : X ≤ Subgroup.normalizer (Q : Set G)) (hX2 : IsPGroup 2 ↥X) : X ≤ Q := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 ↥(X ⊔ Q) := hX2.to_sup_of_normal_right' hQ.2.1 hXN
  have h := (A4.isSylowTwoOf_iff_maximal.mp hQ).2.2 (X ⊔ Q) (sup_le hXL hQ.1) hsup le_sup_right
  exact le_sup_left.trans h

theorem exists_swap (hyp : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    ∃ t' ∈ T, t' ∉ Sgp153 T V₁ ∧ B6.conjSub t' V₁ = V₂ ∧ B6.conjSub t' V₂ = V₁ ∧
      t' * t' ∈ Sgp153 T V₁ := by
  have hidx : (Sgp153 T V₁).relIndex T = 2 := D.relIndex_nS hyp
  obtain ⟨τ, hτT, hτS⟩ : ∃ τ ∈ T, τ ∉ Sgp153 T V₁ := by
    by_contra hcon
    push Not at hcon
    have : Sgp153 T V₁ = T := le_antisymm inf_le_left hcon
    rw [this, Subgroup.relIndex_self] at hidx
    omega
  have hSn : ((Sgp153 T V₁).subgroupOf T).index = 2 := hidx
  have hττS : τ * τ ∈ Sgp153 T V₁ := by
    have := Subgroup.mul_self_mem_of_index_two hSn (⟨τ, hτT⟩ : ↥T)
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨h1, h2⟩ := szN3_conj_V_swap hyp D hτT hτS
  exact ⟨τ, hτT, hτS, h1, h2, hττS⟩

section Facts

theorem RestHyp.S_le_L (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) :=
  SBd9.Sgp_le_normalizer_L r.hL0

theorem RestHyp.Yp_le_L (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    Yp ≤ Subgroup.normalizer (L : Set G) :=
  (le_sup_left.trans r.ctx.inH.1.1).trans r.hNL

theorem RestHyp.S_le_Yp (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := by
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  intro s hs
  have : s ∈ M := hyp.T_le ((inf_le_left : Sgp153 T V₁ ≤ T) hs)
  rw [r.hYY]
  exact le_normalizer_Y153 Mc M this

theorem RestHyp.T_le_Yp (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    T ≤ Subgroup.normalizer (Yp : Set G) := by
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  intro s hs
  rw [r.hYY]
  exact le_normalizer_Y153 Mc M (hyp.T_le hs)

theorem RestHyp.Yp_le_V (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    Yp ≤ Subgroup.normalizer (V₁ : Set G) ∧ Yp ≤ Subgroup.normalizer (V₂ : Set G) := by
  rw [r.hYY]
  exact Hyp153.Y153_le_normalizer_V h113 r.ctx.hyp.hyp r.ctx.hyp.decomp

theorem RestHyp.S_le_YL (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (oTwoUpper (Yp ⊓ L) : Set G) := fun _ hs =>
  normalizer_le_normalizer_oTwoUpper (Yp ⊓ L)
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨r.S_le_Yp hs, r.S_le_L hs⟩)

theorem RestHyp.Yp_le_Q (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    Yp ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
  le_sup_left.trans r.hB

theorem RestHyp.sylow (r : RestHyp T Mc M V₁ V₂ Yp I L t) : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
  SBd9.sylow_inf_Sgp r.ctx r.hL0

theorem RestHyp.YL_le_B (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    oTwoUpper (Yp ⊓ L) ≤ L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
  le_inf ((oTwoUpper_le _).trans inf_le_right) (fun _ hy => r.Yp_le_Q ((oTwoUpper_le _ hy).1))

theorem RestHyp.le_Q_of_two (r : RestHyp T Mc M V₁ V₂ Yp I L t) {X : Subgroup G}
    (hXB : X ≤ L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G))
    (hX2 : IsPGroup 2 ↥X) : X ≤ Sgp153 T V₁ ⊓ L :=
  CFSG.Quasithin.SBd14.le_Q_of_two r.sylow (hXB.trans inf_le_left) (hXB.trans inf_le_right) hX2

end Facts

section V2

theorem RestHyp.V_sq (r : RestHyp T Mc M V₁ V₂ Yp I L t) : ∀ a ∈ VZ T M, a * a = 1 := fun a ha => by
  have := (r.ctx.hyp.hyp.elemAbelian).2 a ha
  rw [pow_two] at this
  exact this

theorem RestHyp.V₂_two (r : RestHyp T Mc M V₁ V₂ Yp I L t) : IsPGroup 2 ↥V₂ :=
  IsPGroup.of_card (n := 2) (by rw [r.ctx.hyp.decomp.card₂]; norm_num)

theorem RestHyp.V₂_le_Q (r : RestHyp T Mc M V₁ V₂ Yp I L t) : V₂ ≤ Sgp153 T V₁ ⊓ L :=
  r.le_Q_of_two (r.h3.trans r.YL_le_B) r.V₂_two

theorem RestHyp.V₂_cQ (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    ∀ v ∈ V₂, ∀ q ∈ Sgp153 T V₁ ⊓ L, v * q = q * v := fun v hv _ hq =>
  Subgroup.mem_centralizer_iff.mp (r.hQV hq) v (r.ctx.hyp.decomp.le₂ hv)

theorem RestHyp.exists_y₂ (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    ∃ y ∈ oTwoUpper (Yp ⊓ L), Odd (orderOf y) ∧ ¬ ∀ v ∈ V₂, y * v = v * y := by
  by_contra hno
  push Not at hno
  apply r.h4
  have hle : oTwoUpper (Yp ⊓ L) ≤ Subgroup.centralizer (V₂ : Set G) := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact (hno y (mem_oTwoUpper_of_odd hy.1 hy.2) hy.2 v hv).symm
  intro y hy v hv
  exact (Subgroup.mem_centralizer_iff.mp (hle hy) v hv).symm

end V2

section Fpf

theorem RestHyp.fpf₂ (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) {y : G}
    (hy : y ∈ oTwoUpper (Yp ⊓ L)) (hodd : Odd (orderOf y))
    (hact : ¬ ∀ v ∈ V₂, y * v = v * y) : ∀ v ∈ V₂, y * v * y⁻¹ = v → v = 1 := by
  intro v hv hfix
  by_contra hv1
  apply hact
  have hyN : y ∈ Subgroup.normalizer (V₂ : Set G) := (r.Yp_le_V h113).2 ((oTwoUpper_le _ hy).1)
  have hall := SBd7.odd_fixes_of_card_four r.ctx.hyp.decomp.card₂
    (fun a ha => r.V_sq a (r.ctx.hyp.decomp.le₂ ha)) hyN hodd hv hv1 hfix
  intro w hw
  calc y * w = (y * w * y⁻¹) * y := by group
    _ = w * y := by rw [hall w hw]

theorem RestHyp.V₂_inf_Z (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    ∀ v ∈ V₂, v ∈ centerOf L → v = 1 := by
  obtain ⟨y, hy, hodd, hact⟩ := r.exists_y₂
  intro v hv hZ
  refine r.fpf₂ h113 hy hodd hact v hv ?_
  have hyL : y ∈ L := (oTwoUpper_le _ hy).2
  have h1 := Subgroup.mem_centralizer_iff.mp hZ.2 y hyL
  calc y * v * y⁻¹ = v * y * y⁻¹ := by rw [h1]
    _ = v := by group

end Fpf

section D

variable {t' : G}

theorem RestHyp.D_le_Yp (r : RestHyp T Mc M V₁ V₂ Yp I L t) (ht'T : t' ∈ T) :
    B6.conjSub t' (oTwoUpper (Yp ⊓ L)) ≤ Yp := by
  intro x hx
  have h1 : t'⁻¹ * x * t' ∈ oTwoUpper (Yp ⊓ L) := B6.mem_conjSub.mp hx
  have h2 : t'⁻¹ * x * t' ∈ Yp := (oTwoUpper_le _ h1).1
  have h3 : x ∈ B6.conjSub t' Yp := B6.mem_conjSub.mpr h2
  rwa [B6.conjSub_eq_self (r.T_le_Yp ht'T)] at h3

theorem RestHyp.D_cV₂ (r : RestHyp T Mc M V₁ V₂ Yp I L t) (hc1 : B6.conjSub t' V₁ = V₂) :
    ∀ x ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)), ∀ v ∈ V₂, x * v = v * x := by
  intro x hx v hv
  have h1 : t'⁻¹ * x * t' ∈ oTwoUpper (Yp ⊓ L) := B6.mem_conjSub.mp hx
  have h2 : t'⁻¹ * v * t' ∈ V₁ := B6.mem_conjSub.mp (hc1 ▸ hv)
  have h3 := r.h2 _ h1 _ h2
  calc x * v = t' * ((t'⁻¹ * x * t') * (t'⁻¹ * v * t')) * t'⁻¹ := by group
    _ = t' * ((t'⁻¹ * v * t') * (t'⁻¹ * x * t')) * t'⁻¹ := by rw [h3]
    _ = v * x := by group

theorem RestHyp.S_le_D (r : RestHyp T Mc M V₁ V₂ Yp I L t) (ht'T : t' ∈ T) :
    Sgp153 T V₁ ≤ Subgroup.normalizer ((B6.conjSub t' (oTwoUpper (Yp ⊓ L)) : Subgroup G) : Set G) := by
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have hTS := Hyp153.T_le_normalizer_Sgp153 hyp r.ctx.hyp.decomp
  intro s hs
  refine SBd4.mem_normalizer_conjSub (r.S_le_YL ?_)
  have := (Subgroup.mem_normalizer_iff.mp (hTS (inv_mem ht'T)) s).mp hs
  simpa using this

end D

section Case

theorem RestHyp.Yp_le_YL (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    Yp ≤ Subgroup.normalizer (oTwoUpper (Yp ⊓ L) : Set G) := fun _ hy =>
  normalizer_le_normalizer_oTwoUpper (Yp ⊓ L)
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, r.Yp_le_L hy⟩)

theorem RestHyp.case1 (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    pCoreOf 2 Yp = Yp ⊓ Subgroup.centralizer (VZ T M : Set G) ∧
      IsElemAbelianOfRank 3 2 (OTwoQuot Yp) := by
  have hcases := Hyp153.lemma_15_3_7_cases h113 r.ctx.hyp.hyp
  rw [← r.hYY] at hcases
  rcases hcases with h | ⟨hP, hO2Z⟩
  · exact h
  · exfalso
    have hZL : centerOf L = pCoreOf 2 L := r.ctx.c33.center_eq
    have hq : CFSG.IsQuasisimple ↥L := r.ctx.c33.quasisimple
    let π : ↥Yp →* OTwoQuot Yp := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Yp)
    have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
    obtain ⟨hext, -, hexp⟩ := hP
    have hab : ∀ a b : OTwoQuot Yp, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center (OTwoQuot Yp) := by
      have := hext
      have := CFSG.IsExtraspecial.quotient_elementary_abelian 3 (OTwoQuot Yp)
      intro a b
      rw [← QuotientGroup.eq_one_iff]
      have hc := (inferInstance : IsMulCommutative
        (OTwoQuot Yp ⧸ Subgroup.center (OTwoQuot Yp))).is_comm.comm (QuotientGroup.mk a)
        (QuotientGroup.mk b)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hc]
      group
    set YLY : Subgroup ↥Yp := (oTwoUpper (Yp ⊓ L)).subgroupOf Yp with hYLY
    have hYLn : YLY.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer ((oTwoUpper_le _).trans inf_le_left)).mpr
        r.Yp_le_YL
    set N : Subgroup (OTwoQuot Yp) := YLY.map π with hN
    have hNn : N.Normal := hYLn.map π hπsurj
    obtain ⟨y₂, hy₂, hodd₂, hact₂⟩ := r.exists_y₂
    have hy₂Yp : y₂ ∈ Yp := (oTwoUpper_le _ hy₂).1
    have hcV : ∀ y : ↥Yp, π y ∈ Subgroup.center (OTwoQuot Yp) →
        ∀ v ∈ V₂, (y : G) * v = v * y := by
      intro y hy v hv
      have : (y : G) ∈ O2Z Yp := mem_O2Z_iff.mpr ⟨y.2, by simpa [π] using hy⟩
      rw [hO2Z] at this
      exact (Subgroup.mem_centralizer_iff.mp this.2 v (r.ctx.hyp.decomp.le₂ hv)).symm
    have hNZ : ¬ N ≤ Subgroup.center (OTwoQuot Yp) := by
      intro hle
      have hmem : π ⟨y₂, hy₂Yp⟩ ∈ N := ⟨⟨y₂, hy₂Yp⟩, Subgroup.mem_subgroupOf.mpr hy₂, rfl⟩
      exact hact₂ (hcV ⟨y₂, hy₂Yp⟩ (hle hmem))
    obtain ⟨w, hwN, hw1, hwZ⟩ := normal_meets_center hab hNn hNZ
    obtain ⟨y, hyYLY, rfl⟩ := hwN
    have hyYL : (y : G) ∈ oTwoUpper (Yp ⊓ L) := Subgroup.mem_subgroupOf.mp hyYLY
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (π y) = 3 := orderOf_eq_prime (hexp (π y)) hw1
    have hdvd : 3 ∣ orderOf (y : G) := by
      rw [Subgroup.orderOf_coe]
      exact hord ▸ orderOf_map_dvd π y
    have hne : orderOf (y : G) ≠ 0 := by
      rw [Subgroup.orderOf_coe]
      exact (orderOf_pos y).ne'
    set y₃ : G := (y : G) ^ (orderOf (y : G) / 3) with hy₃
    have hy₃ord : orderOf y₃ = 3 := orderOf_pow_orderOf_div hne hdvd
    have hy₃YL : y₃ ∈ oTwoUpper (Yp ⊓ L) := Subgroup.pow_mem _ hyYL _
    have hy₃c : ∀ v ∈ V₂, y₃ * v = v * y₃ := by
      intro v hv
      have hc := hcV y hwZ v hv
      have : Commute (y : G) v := hc
      exact (this.pow_left _).eq
    have hLie := SBd9.lieL3_of_psl (n := 2) (by norm_num) hq hZL r.sylow r.hn2
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V₂, v ≠ 1 := by
      by_contra hno
      push Not at hno
      have h4 := r.ctx.hyp.decomp.card₂
      have : Nat.card ↥V₂ = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => Subtype.ext ((hno a a.2).trans (hno b b.2).symm)⟩, ⟨1⟩⟩
      omega
    have hvL : v ∈ L := (r.V₂_le_Q.trans inf_le_right) hv
    have hvc : v ∈ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq' => (r.V₂_cQ v hv q hq').symm
    have hvZ := hLie.reg4 (by norm_num) y₃ (r.YL_le_B hy₃YL) hy₃ord v ⟨hvL, hvc⟩
      (hy₃c v hv).symm
    exact hv1 (r.V₂_inf_Z h113 v hv hvZ)

end Case

section Outer

theorem RestHyp.exists_outer (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) {t' : G}
    (ht'T : t' ∈ T) (hc2 : B6.conjSub t' V₂ = V₁) :
    ∃ d ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)), d ^ 3 = 1 ∧
      d ∉ L ⊔ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hO2, hE9⟩ := r.case1 h113
  obtain ⟨e⟩ := hE9
  let π : ↥Yp →* OTwoQuot Yp := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Yp)
  let ψ : ↥Yp →* Multiplicative (Fin 2 → ZMod 3) := e.toMonoidHom.comp π
  have hpC : ∀ w : ↥Yp, (w : G) ∈ pCoreOf 2 Yp ↔ w ∈ CFSG.Open.pCore 2 ↥Yp := by
    intro w
    constructor
    · rintro ⟨u, hu, hue⟩
      have : u = w := Subtype.ext hue
      exact this ▸ hu
    · intro h
      exact ⟨w, h, rfl⟩
  have hker : ∀ w : ↥Yp, ψ w = 1 ↔ (w : G) ∈ pCoreOf 2 Yp := by
    intro w
    show e (π w) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, hpC]
    exact QuotientGroup.eq_one_iff w
  have hkerV : ∀ w : ↥Yp, ψ w = 1 → ∀ v ∈ VZ T M, v * (w : G) = (w : G) * v := by
    intro w hw
    have h1 : (w : G) ∈ pCoreOf 2 Yp := (hker w).mp hw
    rw [hO2] at h1
    exact fun v hv => Subgroup.mem_centralizer_iff.mp h1.2 v hv
  have hVle₁ := r.ctx.hyp.decomp.le₁
  have hVle₂ := r.ctx.hyp.decomp.le₂
  obtain ⟨y₂, hy₂, hodd₂, hact₂⟩ := r.exists_y₂
  have hy₂Yp : y₂ ∈ Yp := (oTwoUpper_le _ hy₂).1
  set y₁ : G := t' * y₂ * t'⁻¹ with hy₁def
  have hy₁D : y₁ ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) := by
    rw [B6.mem_conjSub]
    have : t'⁻¹ * y₁ * t' = y₂ := by simp [hy₁def, mul_assoc]
    rw [this]
    exact hy₂
  have hy₁Yp : y₁ ∈ Yp := r.D_le_Yp ht'T hy₁D
  have hact₁ : ¬ ∀ v ∈ V₁, y₁ * v = v * y₁ := by
    intro hall
    apply hact₂
    intro v₂ hv₂
    have hv₁ : t' * v₂ * t'⁻¹ ∈ V₁ := by
      rw [← hc2, B6.mem_conjSub]
      simpa [mul_assoc] using hv₂
    have h1 := hall _ hv₁
    calc y₂ * v₂ = t'⁻¹ * (y₁ * (t' * v₂ * t'⁻¹)) * t' := by simp [hy₁def, mul_assoc]
      _ = t'⁻¹ * ((t' * v₂ * t'⁻¹) * y₁) * t' := by rw [h1]
      _ = v₂ * y₂ := by simp [hy₁def, mul_assoc]
  have hy₂c₁ : ∀ v ∈ V₁, y₂ * v = v * y₂ := fun v hv => r.h2 y₂ hy₂ v hv
  let w₂ : ↥Yp := ⟨y₂, hy₂Yp⟩
  let w₁ : ↥Yp := ⟨y₁, hy₁Yp⟩
  have ha : ψ w₂ ≠ 1 := by
    intro h
    exact hact₂ fun v hv => (hkerV w₂ h v (hVle₂ hv)).symm
  have hb : ψ w₁ ≠ 1 := by
    intro h
    exact hact₁ fun v hv => (hkerV w₁ h v (hVle₁ hv)).symm
  have hbz : ψ w₁ ∉ Subgroup.zpowers (ψ w₂) := by
    rintro ⟨m, hm⟩
    have hm' : ψ w₂ ^ m = ψ w₁ := hm
    have h1 : ψ (w₂ ^ m * w₁⁻¹) = 1 := by
      rw [map_mul, map_zpow, map_inv, hm', mul_inv_cancel]
    apply hact₁
    intro v hv
    have h2 := hkerV _ h1 v (hVle₁ hv)
    have hc : Commute y₂ v := hy₂c₁ v hv
    have h3 : Commute (y₂ ^ m) v := hc.zpow_left m
    have h4 : (((w₂ ^ m * w₁⁻¹ : ↥Yp)) : G) = y₂ ^ m * y₁⁻¹ := by simp [w₂, w₁]
    rw [h4] at h2
    have h5 : y₁⁻¹ * v = v * y₁⁻¹ := by
      have e1 : v * (y₂ ^ m * y₁⁻¹) = y₂ ^ m * (v * y₁⁻¹) := by
        rw [← mul_assoc, ← h3.eq, mul_assoc]
      rw [e1, mul_assoc] at h2
      exact (mul_left_cancel h2).symm
    have h6 : Commute y₁⁻¹ v := h5
    simpa using h6.inv_left.eq
  have hA9 : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 9 := by
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_multiplicative, ZMod.card]
  have hA3 : ∀ x : Multiplicative (Fin 2 → ZMod 3), x ^ 3 = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    ext i
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    generalize (Multiplicative.toAdd x) i = a
    revert a
    decide
  obtain ⟨y, hyYp, hy3, hyN0, hyY⟩ := r.hy
  obtain ⟨m, n, hmn⟩ := exists_pow_mul_eq hA9 hA3 ha hbz (ψ ⟨y, hyYp⟩)
  have hn₀Yp : y₂ ^ m * y₁ ^ n ∈ Yp :=
    Yp.mul_mem (Subgroup.zpow_mem _ hy₂Yp m) (Subgroup.zpow_mem _ hy₁Yp n)
  have hcker : ψ ⟨(y₂ ^ m * y₁ ^ n)⁻¹ * y, Yp.mul_mem (Yp.inv_mem hn₀Yp) hyYp⟩ = 1 := by
    have e1 : (⟨(y₂ ^ m * y₁ ^ n)⁻¹ * y, Yp.mul_mem (Yp.inv_mem hn₀Yp) hyYp⟩ : ↥Yp) =
        (w₂ ^ m * w₁ ^ n)⁻¹ * ⟨y, hyYp⟩ := Subtype.ext (by simp [w₂, w₁])
    rw [e1, map_mul, map_inv, map_mul, map_zpow, map_zpow, hmn, inv_mul_cancel]
  have hcmem : (y₂ ^ m * y₁ ^ n)⁻¹ * y ∈ pCoreOf 2 Yp := (hker _).mp hcker
  have hcube : y₂ ^ 3 = 1 := by
    have h1 : ψ (w₂ ^ 3) = 1 := by rw [map_pow]; exact hA3 _
    have h2 : y₂ ^ 3 ∈ pCoreOf 2 Yp := by
      have := (hker (w₂ ^ 3)).mp h1
      simpa [w₂] using this
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 Yp ⟨y₂ ^ 3, h2⟩
    have hj' : (y₂ ^ 3) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hodv1 : orderOf (y₂ ^ 3) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have hodv2 : orderOf (y₂ ^ 3) ∣ orderOf y₂ := orderOf_pow_dvd 3
    have hcop : Nat.Coprime (2 ^ j) (orderOf y₂) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd₂)
    have h3 : orderOf (y₂ ^ 3) ∣ Nat.gcd (2 ^ j) (orderOf y₂) := Nat.dvd_gcd hodv1 hodv2
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  refine ⟨y₁, hy₁D, ?_, ?_⟩
  · have : y₁ ^ 3 = t' * y₂ ^ 3 * t'⁻¹ := by simp [hy₁def, conj_pow]
    rw [this, hcube]
    group
  · intro hy₁N0
    apply hyN0
    have hy₂L : y₂ ∈ L := (oTwoUpper_le _ hy₂).2
    have hn₀N0 : y₂ ^ m * y₁ ^ n ∈ L ⊔ Subgroup.centralizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_sup_left hy₂L) m)
        (Subgroup.zpow_mem _ hy₁N0 n)
    have hcN : (y₂ ^ m * y₁ ^ n)⁻¹ * y ∈
        Subgroup.normalizer ((L ⊔ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      have hcL : (y₂ ^ m * y₁ ^ n)⁻¹ * y ∈ Subgroup.normalizer (L : Set G) :=
        r.Yp_le_L (Yp.mul_mem (Yp.inv_mem hn₀Yp) hyYp)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => conj_mem_N0 hcL hx, fun hx => ?_⟩
      have := conj_mem_N0 (inv_mem hcL) hx
      simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Yp ⟨(y₂ ^ m * y₁ ^ n)⁻¹ * y, hcmem⟩
    have hck : ((y₂ ^ m * y₁ ^ n)⁻¹ * y) ^ (2 ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    obtain ⟨nn, hnn, hpow⟩ := pow_mul_form hn₀N0 hcN (2 ^ k)
    have hyc : y = (y₂ ^ m * y₁ ^ n) * ((y₂ ^ m * y₁ ^ n)⁻¹ * y) := by group
    have hy2k : y ^ (2 ^ k) = nn := by
      calc y ^ (2 ^ k) = ((y₂ ^ m * y₁ ^ n) * ((y₂ ^ m * y₁ ^ n)⁻¹ * y)) ^ (2 ^ k) := by
            rw [← hyc]
        _ = nn := by rw [hpow, hck, mul_one]
    have hcop : Nat.Coprime (2 ^ k) (orderOf y) := by
      rw [hy3]
      exact Nat.Coprime.pow_left k (by norm_num)
    have hz := A4.mem_zpowers_pow_of_coprime hcop
    rw [hy2k] at hz
    exact (Subgroup.zpowers_le.mpr hnn) hz

end Outer

section Main

omit [Finite G] in
theorem card_conjSub' (g : G) (H : Subgroup G) : Nat.card ↥(B6.conjSub g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem RestHyp.exists_pair (r : RestHyp T Mc M V₁ V₂ Yp I L t) {t' : G}
    (hc2 : B6.conjSub t' V₂ = V₁) :
    ∃ y₂ ∈ oTwoUpper (Yp ⊓ L), ∃ y₁ ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)),
      (∃ v ∈ V₂, y₂ * v ≠ v * y₂) ∧ (∃ v ∈ V₁, y₁ * v ≠ v * y₁) := by
  obtain ⟨y₂, hy₂, -, hact₂⟩ := r.exists_y₂
  push Not at hact₂
  obtain ⟨v₂, hv₂, hne₂⟩ := hact₂
  refine ⟨y₂, hy₂, t' * y₂ * t'⁻¹, ?_, ⟨v₂, hv₂, hne₂⟩, t' * v₂ * t'⁻¹, ?_, ?_⟩
  · rw [B6.mem_conjSub]
    simpa [mul_assoc] using hy₂
  · rw [← hc2, B6.mem_conjSub]
    simpa [mul_assoc] using hv₂
  · intro h
    apply hne₂
    have h2 : t'⁻¹ * ((t' * y₂ * t'⁻¹) * (t' * v₂ * t'⁻¹)) * t' =
        t'⁻¹ * ((t' * v₂ * t'⁻¹) * (t' * y₂ * t'⁻¹)) * t' := by rw [h]
    simpa [mul_assoc] using h2

omit [Finite G] in
theorem RestHyp.D_gen (t' : G) :
    ∀ K : Subgroup G, (∀ y ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)), Odd (orderOf y) → y ∈ K) →
      B6.conjSub t' (oTwoUpper (Yp ⊓ L)) ≤ K := by
  intro K hK
  have h1 : oTwoUpper (Yp ⊓ L) ≤ B6.conjSub t'⁻¹ K := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    show y ∈ B6.conjSub t'⁻¹ K
    rw [B6.mem_conjSub]
    have hyY : y ∈ oTwoUpper (Yp ⊓ L) := mem_oTwoUpper_of_odd hy.1 hy.2
    have hD : t' * y * t'⁻¹ ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) := by
      rw [B6.mem_conjSub]
      simpa [mul_assoc] using hyY
    have hodd : Odd (orderOf (t' * y * t'⁻¹)) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hy.2
    simpa using hK _ hD hodd
  intro x hx
  have h2 : t'⁻¹ * x * t' ∈ oTwoUpper (Yp ⊓ L) := B6.mem_conjSub.mp hx
  have h3 := (B6.mem_conjSub.mp (h1 h2))
  simpa [mul_assoc] using h3

end Main

end CFSG.Quasithin.SBd14
