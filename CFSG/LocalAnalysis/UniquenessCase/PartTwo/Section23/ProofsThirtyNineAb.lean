module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CentralizerTV
public import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.SteinbergCBFTFactorization

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

def centLModV : Subgroup G where
  carrier := {s : G | s ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) ∧
    ∀ l ∈ c.L, ⁅s, l⁆ ∈ c.V}
  one_mem' := by
    refine ⟨Subgroup.mem_inf.mpr ⟨(c.L ⊔ D.T).one_mem,
      (Subgroup.centralizer (c.V : Set G)).one_mem⟩, ?_⟩
    intro l _
    simp
  mul_mem' := by
    rintro s₁ s₂ ⟨hs₁S, hs₁⟩ ⟨hs₂S, hs₂⟩
    refine ⟨Subgroup.mem_inf.mpr
      ⟨(c.L ⊔ D.T).mul_mem (Subgroup.mem_inf.mp hs₁S).1 (Subgroup.mem_inf.mp hs₂S).1,
       (Subgroup.centralizer (c.V : Set G)).mul_mem
        (Subgroup.mem_inf.mp hs₁S).2 (Subgroup.mem_inf.mp hs₂S).2⟩, ?_⟩
    intro l hl
    have hs₁H : s₁ ∈ c.L ⊔ D.T := (Subgroup.mem_inf.mp hs₁S).1
    have hconj : s₁ * ⁅s₂, l⁆ * s₁⁻¹ ∈ c.V :=
      (Subgroup.mem_normalizer_iff.mp (Ctx23L.sup_le_normalizer_V D Ch c hs₁H)
        ⁅s₂, l⁆).1 (hs₂ l hl)
    rw [CFSG.commutator_mul_left (s₁) (s₂) (l)]
    exact c.V.mul_mem hconj (hs₁ l hl)
  inv_mem' := by
    rintro s ⟨hsS, hs⟩
    refine ⟨Subgroup.mem_inf.mpr
      ⟨(c.L ⊔ D.T).inv_mem (Subgroup.mem_inf.mp hsS).1,
       (Subgroup.centralizer (c.V : Set G)).inv_mem (Subgroup.mem_inf.mp hsS).2⟩, ?_⟩
    intro l hl
    have hsH : s ∈ c.L ⊔ D.T := (Subgroup.mem_inf.mp hsS).1
    have hconj : s⁻¹ * ⁅s, l⁆ * s ∈ c.V := by
      have h := (Subgroup.mem_normalizer_iff.mp
        (Ctx23L.sup_le_normalizer_V D Ch c ((c.L ⊔ D.T).inv_mem hsH)) ⁅s, l⁆).1
        (hs l hl)
      simpa only [inv_inv] using h
    have hEq : ⁅s⁻¹, l⁆ = (s⁻¹ * ⁅s, l⁆ * s)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hEq]
    exact c.V.inv_mem hconj

theorem mem_centLModV {x : G} :
    x ∈ c.centLModV ↔ x ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) ∧
      ∀ l ∈ c.L, ⁅x, l⁆ ∈ c.V :=
  Iff.rfl

include c in
theorem sup_inf_centralizer_V_le_pCoreOf (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) :
    (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) ≤
      CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
  uc22main1_le_pCoreOf inf_le_left
    (Ctx23L.isPGroup_sup_inf_centralizer_V D Ch h4 h23 h1930 c)
    (fun n hn x hx =>
      Ctx23L.conj_mem_sup_inf_centralizer_V D Ch c n hn x hx)

include c in
private theorem conj_mem_centLModV {g : G}
    (hg : g ∈ c.L ⊔ D.T) {s : G} (hs : s ∈ c.centLModV) :
    g * s * g⁻¹ ∈ c.centLModV := by
  refine ⟨Ctx23L.conj_mem_sup_inf_centralizer_V D Ch c g hg s hs.1, ?_⟩
  intro l hl
  have hLTnormL : c.L ⊔ D.T ≤ Subgroup.normalizer (c.L : Set G) :=
    sup_le Subgroup.le_normalizer c.hL.1.1
  have hg' : g⁻¹ ∈ c.L ⊔ D.T := (c.L ⊔ D.T).inv_mem hg
  have hgl : g⁻¹ * l * g ∈ c.L := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (hLTnormL hg') l).1 hl
  have hcomm : ⁅g * s * g⁻¹, l⁆ = g * ⁅s, g⁻¹ * l * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hcomm]
  exact (Subgroup.mem_normalizer_iff.mp
    (Ctx23L.sup_le_normalizer_V D Ch c hg) _).1 (hs.2 _ hgl)

include c in
theorem sup_le_normalizer_centLModV :
    c.L ⊔ D.T ≤ Subgroup.normalizer (c.centLModV : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    exact conj_mem_centLModV (D := D) (Ch := Ch) (c := c) hg hs
  · intro hs
    have h := conj_mem_centLModV (D := D) (Ch := Ch) (c := c)
      ((c.L ⊔ D.T).inv_mem hg) hs
    rwa [show g⁻¹ * (g * s * g⁻¹) * (g⁻¹)⁻¹ = s by group] at h

include c in
theorem V_le_centLModV (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    c.V ≤ c.centLModV := by
  intro v hv
  have hVab := c.isElemAbelian_V h4 h1930
  have hVT : v ∈ D.T := c.V_le_T h4 h1930 hv
  refine ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hVT, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val ((hVab.1).is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  · intro l hl
    have hconj : l * v⁻¹ * l⁻¹ ∈ c.V :=
      (Subgroup.mem_normalizer_iff.mp
        (Ctx23L.sup_le_normalizer_V D Ch c (Subgroup.mem_sup_left hl)) v⁻¹).1
        (c.V.inv_mem hv)
    have hEq : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hEq]
    exact c.V.mul_mem hv hconj

include c in
theorem le_centLModV_of_forall {X : Subgroup G}
    (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hXS : X ≤ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G))
    (hX : ∀ x ∈ X, ∀ l ∈ c.L, ⁅x, l⁆ ∈ c.centLModV) :
    X ≤ c.centLModV := by
  intro x hx
  refine ⟨hXS hx, ?_⟩
  intro l hl
  have hXL_C : ⁅X, c.L⁆ ≤ c.centLModV := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact hX a ha b hb
  have hXL_V : ⁅⁅X, c.L⁆, c.L⁆ ≤ c.V := by
    rw [Subgroup.commutator_le]
    intro s hs l hl'
    exact (hXL_C hs).2 l hl'
  have hLX_V : ⁅⁅c.L, X⁆, c.L⁆ ≤ c.V := by
    simpa only [Subgroup.commutator_comm c.L X] using hXL_V
  have hLL_X : ⁅⁅c.L, c.L⁆, X⁆ ≤ c.V :=
    CFSG.GroupTheory.commutator_commutator_le_of_rotate_normal
      (M := c.L ⊔ D.T) (A := c.L) (B := X) (N := c.V)
      le_sup_left (hXS.trans inf_le_left) ((c.V_le_T h4 h1930).trans le_sup_right)
      (Ctx23L.sup_le_normalizer_V D Ch c) hLX_V hXL_V
  rw [c.hL.1.2.1] at hLL_X
  have hXL_V' : ⁅X, c.L⁆ ≤ c.V := by
    simpa only [Subgroup.commutator_comm X c.L] using hLL_X
  exact hXL_V' (Subgroup.commutator_mem_commutator hx hl)

include c in
theorem exists_conjSubgroup_Z_le_E_not_le_centralizer
    (hE : ¬ IsMulCommutative c.E) :
    ∃ k : G, CFSG.Quasithin.conjSubgroup D.Z k ≤ c.E ∧
      ¬ CFSG.Quasithin.conjSubgroup D.Z k ≤ Subgroup.centralizer (c.V : Set G) := by
  classical
  by_contra h
  push Not at h
  have hME : D.M ≤ Subgroup.normalizer (c.E : Set G) := by
    rw [Ctx23L.E]
    exact uc22p22v_le_normalizer_conjClosure D.M c.V
  let gen : ↥D.M × ↥c.N → Subgroup G := fun p =>
    CFSG.Quasithin.conjSubgroup D.Z (((p.1 : G) * (p.2 : G))⁻¹)
  have hEspan : c.E = ⨆ p, gen p := by
    rw [c.E_span]
  have hgen_le_E : ∀ p : ↥D.M × ↥c.N, gen p ≤ c.E := by
    intro p
    rw [c.E_span]
    exact le_iSup (fun q : ↥D.M × ↥c.N =>
      CFSG.Quasithin.conjSubgroup D.Z (((q.1 : G) * (q.2 : G))⁻¹)) p
  have hEcent : c.E ≤ Subgroup.centralizer (c.V : Set G) := by
    rw [hEspan]
    exact iSup_le (f := gen) fun p =>
      h ((p.1 : G) * (p.2 : G))⁻¹ (hgen_le_E p)
  have hEcentE : c.E ≤ Subgroup.centralizer (c.E : Set G) := by
    conv_lhs => rw [hEspan]
    refine iSup_le (f := gen) fun p => ?_
    set m : G := (p.1 : G) with hm
    set n : G := (p.2 : G) with hn
    have hZnV : CFSG.Quasithin.conjSubgroup D.Z (n⁻¹) ≤ c.V := by
      rw [Ctx23L.V]
      have hEq : CFSG.Quasithin.conjSubgroup D.Z (n⁻¹) =
          D.Z.map (MulAut.conj n).toMonoidHom := by
        change D.Z.map (MulAut.conj ((n⁻¹)⁻¹)).toMonoidHom =
          D.Z.map (MulAut.conj n).toMonoidHom
        rw [inv_inv]
      rw [hEq]
      exact le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf c.N D.Z) => K)
        (D.Z.map (MulAut.conj n).toMonoidHom) ⟨n, p.2.2, rfl⟩ le_rfl
    have hgen : CFSG.Quasithin.conjSubgroup D.Z ((m * n)⁻¹) ≤
        CFSG.Quasithin.conjSubgroup c.V (m⁻¹) := by
      have h' := CFSG.Quasithin.E3.conjSubgroup_mono_left (m⁻¹) hZnV
      rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup, ← mul_inv_rev] at h'
    have hmN : m⁻¹ ∈ Subgroup.normalizer (c.E : Set G) :=
      (Subgroup.normalizer (c.E : Set G)).inv_mem (hME (p.1).2)
    have hEVm : c.E ≤ Subgroup.centralizer
        (CFSG.Quasithin.conjSubgroup c.V (m⁻¹) : Set G) := by
      have h' := CFSG.Quasithin.E3.conjSubgroup_mono_left (m⁻¹) hEcent
      rw [CFSG.Quasithin.E3.conjSubgroup_centralizer,
        CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hmN] at h'
      exact h'
    exact hgen.trans (Subgroup.le_centralizer_iff.mp hEVm)
  exact hE ⟨⟨fun a b =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEcentE a.2) b.1 b.2).symm⟩⟩

include c in
theorem conjSubgroup_Z_inf_centralizer_V_eq_bot (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {k : G} (hk : ¬ CFSG.Quasithin.conjSubgroup D.Z k ≤
      Subgroup.centralizer (c.V : Set G)) :
    CFSG.Quasithin.conjSubgroup D.Z k ⊓ Subgroup.centralizer (c.V : Set G) = ⊥ := by
  classical
  set A : Subgroup G := CFSG.Quasithin.conjSubgroup D.Z k
  by_contra hne
  apply hk
  intro y hy
  obtain ⟨zsub, hzsub1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let z : G := zsub.1
  have hz : z ∈ A ⊓ Subgroup.centralizer (c.V : Set G) := zsub.2
  have hz1 : z ≠ 1 := fun h => hzsub1 (Subtype.ext h)
  have hzA : z ∈ A := (Subgroup.mem_inf.mp hz).1
  have hzC : z ∈ Subgroup.centralizer (c.V : Set G) := (Subgroup.mem_inf.mp hz).2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hzv : z * v = v * z := (Subgroup.mem_centralizer_iff.mp hzC v hv).symm
  have hz_conj : z ∈ CFSG.Quasithin.conjSubgroup A v⁻¹ := by
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    have h' : v⁻¹ * z * v = z := by
      calc v⁻¹ * z * v = v⁻¹ * (z * v) := by group
        _ = v⁻¹ * (v * z) := by rw [hzv]
        _ = z := by group
    have h'' : v⁻¹ * z * v⁻¹⁻¹ = z := by
      simpa only [inv_inv] using h'
    rw [h'']
    exact hzA
  have hne_inf : A ⊓ CFSG.Quasithin.conjSubgroup A v⁻¹ ≠ ⊥ := by
    intro hbot
    have hzbot : z ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hzA, hz_conj⟩
    exact hz1 (Subgroup.mem_bot.mp hzbot)
  have hEq : CFSG.Quasithin.conjSubgroup A v⁻¹ = A :=
    c.conjSubgroup_TI h4 h1930 k v⁻¹ hne_inf
  have hvN : v ∈ Subgroup.normalizer (A : Set G) := by
    have hvN' : v⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer).mp hEq
    simpa only [inv_inv] using (Subgroup.normalizer (A : Set G)).inv_mem hvN'
  have hvT : v ∈ D.T := c.V_le_T h4 h1930 hv
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp D.sylowG.isPGroup) ⟨v, hvT⟩
  have hv2 : ∃ j : ℕ, orderOf v = 2 ^ j :=
    ⟨j, (Subgroup.orderOf_mk v hvT).symm.trans hj⟩
  have hcent := c.conjSubgroup_twoElement_centralizes h4 h1930 k hvN hv2
  exact mul_inv_eq_iff_eq_mul.mp (hcent y hy)

include c in
theorem exists_mem_conjSubgroup_Z_inv_mul_mem (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {k : G} (hkT : CFSG.Quasithin.conjSubgroup D.Z k ≤ D.T)
    (hk : ¬ CFSG.Quasithin.conjSubgroup D.Z k ≤
      Subgroup.centralizer (c.V : Set G))
    (hidx : (D.T ⊓ Subgroup.centralizer (c.V : Set G)).relIndex D.T =
      2 ^ CFSG.Open.pRank 2 D.Z) :
    ∀ t ∈ D.T, ∃ z ∈ CFSG.Quasithin.conjSubgroup D.Z k,
      z⁻¹ * t ∈ Subgroup.centralizer (c.V : Set G) := by
  classical
  let A : Subgroup G := CFSG.Quasithin.conjSubgroup D.Z k
  let B : Subgroup G := D.T ⊓ Subgroup.centralizer (c.V : Set G)
  have hAT : A ≤ D.T := hkT
  have hAB : A ⊓ B = ⊥ := by
    have h := conjSubgroup_Z_inf_centralizer_V_eq_bot (D := D) (Ch := Ch) (c := c)
      h4 h1930 (k := k) hk
    change A ⊓ (D.T ⊓ Subgroup.centralizer (c.V : Set G)) = ⊥
    rw [← inf_assoc, inf_eq_left.mpr hAT]
    exact h
  have hcardA : Nat.card A = 2 ^ CFSG.Open.pRank 2 D.Z := by
    change Nat.card (CFSG.Quasithin.conjSubgroup D.Z k) = 2 ^ CFSG.Open.pRank 2 D.Z
    rw [CFSG.Quasithin.E3.card_conjSubgroup,
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
        (c.isElemAbelian_Z h4 h1930)]
  have hcardB : 2 ^ CFSG.Open.pRank 2 D.Z * Nat.card B = Nat.card D.T := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := D.T)
    have hBT : B ≤ D.T := inf_le_left
    rw [inf_eq_left.mpr hBT] at h
    rwa [show B.relIndex D.T = 2 ^ CFSG.Open.pRank 2 D.Z from hidx] at h
  have hcardT : Nat.card D.T = Nat.card A * Nat.card B := by
    rw [← hcardB, hcardA]
  have hprod : Nat.card ↥((A : Set G) * (B : Set G)) = Nat.card D.T := by
    have h := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf (A := A) (B := B)
    rw [hAB] at h
    have h' : Nat.card ↥((A : Set G) * (B : Set G)) = Nat.card A * Nat.card B := by
      simpa [Subgroup.card_bot] using h
    rwa [← hcardT] at h'
  have hsubset : ((A : Set G) * (B : Set G)) ⊆ (D.T : Set G) := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact D.T.mul_mem (hAT ha) (Subgroup.mem_inf.mp hb).1
  have hset_eq : ((A : Set G) * (B : Set G)) = (D.T : Set G) := by
    have hncardT : ((D.T : Set G)).ncard = Nat.card D.T :=
      (Nat.card_coe_set_eq (D.T : Set G)).symm
    have hncardProd : (((A : Set G) * (B : Set G))).ncard = Nat.card D.T := by
      rw [← Nat.card_coe_set_eq]
      exact hprod
    refine Set.eq_of_subset_of_ncard_le hsubset ?_ (Set.toFinite _)
    rw [hncardT, hncardProd]
  intro t ht
  have htprod : t ∈ ((A : Set G) * (B : Set G)) := by
    rw [hset_eq]
    exact ht
  obtain ⟨z, hz, w, hw, rfl⟩ := Set.mem_mul.mp htprod
  refine ⟨z, hz, ?_⟩
  have hwC : w ∈ Subgroup.centralizer (c.V : Set G) := (Subgroup.mem_inf.mp hw).2
  convert hwC using 1
  group

include c in
theorem commutator_commutator_mem_centLModV (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hEQ : c.E ≤ CFSG.Open.pCoreOf 2 D.M)
    (hEZ : ⁅c.E, CFSG.Open.pCoreOf 2 D.M⁆ ≤ D.Z)
    {k : G} (hkE : CFSG.Quasithin.conjSubgroup D.Z k ≤ c.E)
    (hT : ∀ t ∈ D.T, ∃ z ∈ CFSG.Quasithin.conjSubgroup D.Z k,
      z⁻¹ * t ∈ Subgroup.centralizer (c.V : Set G))
    {X : Subgroup G}
    (hXS : X ≤ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G))
    (hLX : c.L ⊔ D.T ≤ Subgroup.normalizer (X : Set G))
    (hSX : ∀ s ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G),
      ∀ x ∈ X, ⁅s, x⁆ ∈ c.centLModV) :
    ∀ q ∈ D.T, ∀ q' ∈ D.T, ∀ x ∈ X, ⁅q', ⁅q, x⁆⁆ ∈ c.centLModV := by
  classical
  have hQT : CFSG.Open.pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM)
  have hET : c.E ≤ D.T := hEQ.trans hQT
  have hCVleM : Subgroup.centralizer (c.V : Set G) ≤ D.M := by
    have hUZ : D.U = D.Z := (h4 h1930 c).1
    have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
      rw [← hUZ]
      exact D.normalizer_U_eq
    have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
    exact (Subgroup.centralizer_le hZleV).trans
      ((Subgroup.centralizer_le_normalizer (D.Z : Set G)).trans (le_of_eq hNZ))
  have hME : D.M ≤ Subgroup.normalizer (c.E : Set G) := by
    rw [Ctx23L.E]
    exact uc22p22v_le_normalizer_conjClosure D.M c.V
  have hZC : D.Z ≤ c.centLModV :=
    (uc22p22v_le_conjClosure c.N D.Z).trans (c.V_le_centLModV h4 h1930)
  have hconj_mem : ∀ h ∈ c.L ⊔ D.T, ∀ c' ∈ c.centLModV,
      h * c' * h⁻¹ ∈ c.centLModV := by
    intro h hh c' hc'
    exact (Subgroup.mem_normalizer_iff.mp
      (c.sup_le_normalizer_centLModV hh) c').1 hc'
  have hcomm_mem : ∀ h ∈ c.L ⊔ D.T, ∀ c' ∈ c.centLModV,
      ⁅h, c'⁆ ∈ c.centLModV := by
    intro h hh c' hc'
    have h1 := hconj_mem h hh c' hc'
    have h2 : c'⁻¹ ∈ c.centLModV := c.centLModV.inv_mem hc'
    simpa [commutatorElement_def] using c.centLModV.mul_mem h1 h2
  intro q hq q' hq' x hx
  obtain ⟨z, hzZk, hsz⟩ := hT q hq
  obtain ⟨z', hz'Zk, hs'z⟩ := hT q' hq'
  have hzE : z ∈ c.E := hkE hzZk
  have hz'E : z' ∈ c.E := hkE hz'Zk
  have hzT : z ∈ D.T := hET hzE
  have hz'T : z' ∈ D.T := hET hz'E
  have hzLT : z ∈ c.L ⊔ D.T := Subgroup.mem_sup_right hzT
  have hz'LT : z' ∈ c.L ⊔ D.T := Subgroup.mem_sup_right hz'T
  have hqLT : q ∈ c.L ⊔ D.T := Subgroup.mem_sup_right hq
  have hq'LT : q' ∈ c.L ⊔ D.T := Subgroup.mem_sup_right hq'
  have hxS : x ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) := hXS hx
  have hxLT : x ∈ c.L ⊔ D.T := (Subgroup.mem_inf.mp hxS).1
  have hxM : x ∈ D.M := hCVleM (Subgroup.mem_inf.mp hxS).2
  have hzM : z ∈ D.M := (uc22main1_pCoreOf_le D.M) (hEQ hzE)
  have hsS : z⁻¹ * q ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, hsz⟩
    exact (c.L ⊔ D.T).mul_mem ((c.L ⊔ D.T).inv_mem hzLT) hqLT
  have hs'S : z'⁻¹ * q' ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, hs'z⟩
    exact (c.L ⊔ D.T).mul_mem ((c.L ⊔ D.T).inv_mem hz'LT) hq'LT
  have hyX : ⁅q, x⁆ ∈ X := by
    have h1 : q * x * q⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hLX hqLT) x).1 hx
    simpa [commutatorElement_def] using X.mul_mem h1 (X.inv_mem hx)
  have hxzE : ⁅x, z⁆ ∈ c.E := by
    have hxzx : x * z * x⁻¹ ∈ c.E :=
      (Subgroup.mem_normalizer_iff.mp (hME hxM) z).1 hzE
    simpa [commutatorElement_def] using c.E.mul_mem hxzx (c.E.inv_mem hzE)
  have hzxE : ⁅z, x⁆ ∈ c.E := by
    rw [← commutatorElement_inv x z]
    exact c.E.inv_mem hxzE
  have hzzxC : ⁅z', ⁅z, x⁆⁆ ∈ c.centLModV :=
    hZC (hEZ (Subgroup.commutator_mem_commutator hz'E (hEQ hzxE)))
  have hc1 : z * ⁅z⁻¹ * q, x⁆ * z⁻¹ ∈ c.centLModV :=
    hconj_mem z hzLT _ (hSX (z⁻¹ * q) hsS x hx)
  have hqx_eq : ⁅q, x⁆ = (z * ⁅z⁻¹ * q, x⁆ * z⁻¹) * ⁅z, x⁆ := by
    calc ⁅q, x⁆ = ⁅z * (z⁻¹ * q), x⁆ :=
          congrArg (fun a => ⁅a, x⁆) (by group : q = z * (z⁻¹ * q))
      _ = (z * ⁅z⁻¹ * q, x⁆ * z⁻¹) * ⁅z, x⁆ := by
          rw [CFSG.commutator_mul_left]
  have hzy : ⁅z', ⁅q, x⁆⁆ ∈ c.centLModV := by
    rw [hqx_eq, CFSG.commutator_mul_right]
    have h1 : ⁅z', z * ⁅z⁻¹ * q, x⁆ * z⁻¹⁆ * (z * ⁅z⁻¹ * q, x⁆ * z⁻¹) ∈
        c.centLModV :=
      c.centLModV.mul_mem
        (hcomm_mem z' hz'LT (z * ⁅z⁻¹ * q, x⁆ * z⁻¹) hc1) hc1
    have h2 : ⁅z', ⁅z, x⁆⁆ * (z * ⁅z⁻¹ * q, x⁆ * z⁻¹)⁻¹ ∈ c.centLModV :=
      c.centLModV.mul_mem hzzxC (c.centLModV.inv_mem hc1)
    simpa only [mul_assoc] using c.centLModV.mul_mem h1 h2
  have hc2 : z' * ⁅z'⁻¹ * q', ⁅q, x⁆⁆ * z'⁻¹ ∈ c.centLModV :=
    hconj_mem z' hz'LT _ (hSX (z'⁻¹ * q') hs'S _ hyX)
  have hq'x_eq : ⁅q', ⁅q, x⁆⁆ =
      (z' * ⁅z'⁻¹ * q', ⁅q, x⁆⁆ * z'⁻¹) * ⁅z', ⁅q, x⁆⁆ := by
    calc ⁅q', ⁅q, x⁆⁆ = ⁅z' * (z'⁻¹ * q'), ⁅q, x⁆⁆ :=
          congrArg (fun a => ⁅a, ⁅q, x⁆⁆) (by group : q' = z' * (z'⁻¹ * q'))
      _ = (z' * ⁅z'⁻¹ * q', ⁅q, x⁆⁆ * z'⁻¹) * ⁅z', ⁅q, x⁆⁆ := by
          rw [CFSG.commutator_mul_left]
  rw [hq'x_eq]
  exact c.centLModV.mul_mem hc2 hzy

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
