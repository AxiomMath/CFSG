module

public import CFSG.Quasithin.Recognition.F112Crit.Lemma61
public import CFSG.Quasithin.Recognition.F112Crit.Lemma63
public import CFSG.Quasithin.Recognition.F112Crit.Lemma65
public import CFSG.Quasithin.Recognition.F112Crit.Transvection
public import CFSG.Quasithin.Recognition.F112Crit.FrattiniAction
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph
public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

section Generic

variable {G : Type*} [Group G]

theorem mem_pCore_iff_mem_pCoreOf {H : Subgroup G} (h : ↥H) :
    h ∈ CFSG.pCore 2 ↥H ↔ (h : G) ∈ pCoreOf 2 H := by
  constructor
  · intro hh
    exact ⟨h, hh, rfl⟩
  · rintro ⟨n, hn, hnh⟩
    have : n = h := Subtype.ext hnh
    exact this ▸ hn

theorem centralizer_pCore_le_of_charTwo {H : Subgroup G} (h : CharTwo H) :
    Subgroup.centralizer ((CFSG.pCore 2 ↥H : Subgroup ↥H) : Set ↥H) ≤ CFSG.pCore 2 ↥H := by
  intro c hc
  have h1 : (c : G) ∈ H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp (SetLike.mem_coe.mp hy)
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hc) n hn)
  exact (mem_pCore_iff_mem_pCoreOf c).2 (h h1)

theorem exists_mem_zpowers_sup_pCoreOf {K R : Subgroup G} (hRK : R ≤ K) (hR : IsPGroup 2 R)
    (hcyc : ∀ X : Subgroup (oTwoQuot ↥K), IsPGroup 2 X → IsCyclic ↥X) :
    ∃ c ∈ R, R ≤ Subgroup.zpowers c ⊔ pCoreOf 2 K := by
  classical
  let f : ↥R →* oTwoQuot ↥K :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hRK)
  have hX : IsPGroup 2 ↥f.range := hR.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  haveI := hcyc f.range hX
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥f.range)
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ↥R, f r₀ = (g : oTwoQuot ↥K) := g.2
  refine ⟨(r₀ : G), r₀.2, fun r hr => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨f ⟨r, hr⟩, ⟨_, rfl⟩⟩)
  have hfk : f (r₀ ^ k) = f ⟨r, hr⟩ := by
    rw [map_zpow, hr₀]
    exact congrArg Subtype.val hk
  have hker : f ((r₀ ^ k)⁻¹ * ⟨r, hr⟩) = 1 := by
    rw [map_mul, map_inv, hfk, inv_mul_cancel]
  have h1 : Subgroup.inclusion hRK ((r₀ ^ k)⁻¹ * ⟨r, hr⟩) ∈ CFSG.pCore 2 ↥K :=
    (QuotientGroup.eq_one_iff _).1 hker
  have h2 := (mem_pCore_iff_mem_pCoreOf _).1 h1
  have e : (((r₀ ^ k)⁻¹ * ⟨r, hr⟩ : ↥R) : G) = ((r₀ : G) ^ k)⁻¹ * r := by
    simp [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
  have h3 : ((r₀ : G) ^ k)⁻¹ * r ∈ pCoreOf 2 K := by
    rw [← e]; exact h2
  have h4 : r = (r₀ : G) ^ k * (((r₀ : G) ^ k)⁻¹ * r) := by group
  rw [h4]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ _))
    (Subgroup.mem_sup_right h3)

end Generic

section Frattini

theorem frattini_add_apply {N : Type*} [Group N] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (π : Additive N →+ V) (α : MulAut N) (g : V →ₗ[ZMod 2] V)
    (hg : ∀ n : N, g (π (Additive.ofMul n)) = π (Additive.ofMul (α n)))
    {c q m : N} {k : ℤ} (hm : m = c ^ k * q) (hq : α q = q) :
    π (Additive.ofMul m) + g (π (Additive.ofMul m)) =
      (k : ZMod 2) • (π (Additive.ofMul c) + g (π (Additive.ofMul c))) := by
  subst hm
  have h1 : α (c ^ k * q) = α c ^ k * q := by rw [map_mul α, map_zpow α, hq]
  rw [hg (c ^ k * q), hg c, h1, ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, map_add, map_add,
    map_zsmul, map_zsmul, Int.cast_smul_eq_zsmul (ZMod 2), smul_add, add_add_add_comm,
    CFSG.ComponentClassification.OutcomeLocal.zmod2_add_self (π (Additive.ofMul q)), add_zero]

end Frattini

section Amalgam

variable {G : Type u} [Group G] [Finite G] {G₀ G₁ G₂ T Z : Subgroup G}

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

namespace CritAmalgam

theorem ballStab_one_eq (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    ballStab 1 (γ₀ G₀ G₁ G₂) = CFSG.Quasithin.coreIn (G₁ ⊓ G₂) G₁ :=
  (CosetGeom.ballStab_one_γ₀ hc.amalgam.gen).1

theorem pCoreOf_left_le_ballStab (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    pCoreOf 2 G₁ ≤ ballStab 1 (γ₀ G₀ G₁ G₂) := by
  have := CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam (γ₀ G₀ G₁ G₂)
  rwa [hc.stab_γ₀_eq] at this

theorem pCoreOf_left_le (hc : CritAmalgam G₀ G₁ G₂ T Z) : pCoreOf 2 G₁ ≤ G₁ ⊓ G₂ :=
  hc.pCoreOf_left_le_ballStab.trans (hc.ballStab_one_eq ▸ CFSG.Quasithin.coreIn_le_right _ _)

theorem conjClosure_le_T (hc : CritAmalgam G₀ G₁ G₂ T Z) : conjClosure Z G₂ ≤ T :=
  hc.conjClosure_le_center.trans
    (inf_le_left.trans (F7.isSylowTwoOf_pCoreOf_le hc.amalgam.sylow₂))

end CritAmalgam

end Amalgam

section Main

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T Z : Subgroup G}

theorem comm_mem_pCoreOf (hc : CritAmalgam G₀ G₁ G₂ T Z) {L : Subgroup G} (hL₁ : L ≤ G₁)
    (hLn : G₁ ≤ Subgroup.normalizer (L : Set G))
    (hq : CFSG.IsQuasisimple (oTwoQuot ↥L)) (hno : NoMcLaughlinCover (oTwoQuot ↥L))
    (hcyc : ∃ c ∈ pCoreOf 2 G₁, pCoreOf 2 G₁ ≤ Subgroup.zpowers c ⊔ pCoreOf 2 G₂)
    {a : G} (haA : a ∈ conjClosure Z G₂) (haR : a ∉ pCoreOf 2 G₁) :
    ∀ l ∈ L, l * a * l⁻¹ * a⁻¹ ∈ pCoreOf 2 G₁ := by
  classical
  have haQ₂ : a ∈ pCoreOf 2 G₂ := (hc.conjClosure_le_center haA).1
  have haC : a ∈ Subgroup.centralizer (pCoreOf 2 G₂ : Set G) := (hc.conjClosure_le_center haA).2
  have haG₁ : a ∈ G₁ := (hc.amalgam.T_le (hc.conjClosure_le_T haA)).1
  obtain ⟨V, _, _, _, π, ρ, hπs, hπρ, hρk⟩ := exists_frattini_action (H := ↥G₁)
    (centralizer_pCore_le_of_charTwo hc.amalgam.charTwo)
  set a₁ : ↥G₁ := ⟨a, haG₁⟩ with ha₁
  have hρa : ρ a₁ ≠ 1 := fun h => haR ((mem_pCore_iff_mem_pCoreOf a₁).1 ((hρk a₁).1 h))
  have ht : CFSG.ComponentClassification.OutcomeLocal.IsF2Transvection (ρ a₁) := by
    obtain ⟨c, hcR, hcyc'⟩ := hcyc
    obtain ⟨cN, hcN, hcNc⟩ := Subgroup.mem_map.mp hcR
    refine isF2Transvection_of_fixes (ρ a₁) hρa (π (Additive.ofMul ⟨cN, hcN⟩)) fun v => ?_
    obtain ⟨n, rfl⟩ := hπs v
    obtain ⟨m, hnm⟩ : ∃ m : ↥(CFSG.pCore 2 ↥G₁), n = Additive.ofMul m :=
      ⟨Additive.toMul n, rfl⟩
    rw [hnm]
    have hmR : ((m : ↥G₁) : G) ∈ pCoreOf 2 G₁ := ⟨m.1, m.2, rfl⟩
    have hcG₂ : c ∈ G₂ := (hc.pCoreOf_left_le hcR).2
    have hnorm : Subgroup.zpowers c ≤ Subgroup.normalizer (pCoreOf 2 G₂ : Set G) :=
      (Subgroup.zpowers_le).2 (le_normalizer_pCoreOf 2 G₂ hcG₂)
    have hmem := hcyc' hmR
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hmem
    obtain ⟨y, hy, q, hq₂, hyq⟩ := Set.mem_mul.mp hmem
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hqR : q ∈ pCoreOf 2 G₁ := by
      have : q = (c ^ k)⁻¹ * ((m : ↥G₁) : G) := by rw [← hyq]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hcR k)) hmR
    obtain ⟨qN, hqN, hqNq⟩ := Subgroup.mem_map.mp hqR
    have hm : m = (⟨cN, hcN⟩ : ↥(CFSG.pCore 2 ↥G₁)) ^ k * ⟨qN, hqN⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      have h1 : ((c ^ k * q : G)) = ((m : ↥G₁) : G) := hyq
      rw [← h1, ← hcNc, ← hqNq]
      simp [Subgroup.coe_mul, Subgroup.coe_zpow]
    have hα : MulAut.conjNormal a₁ (⟨qN, hqN⟩ : ↥(CFSG.pCore 2 ↥G₁)) = ⟨qN, hqN⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      have h1 : q * a = a * q := (Subgroup.mem_centralizer_iff.mp haC) q hq₂
      have h2 : a * q * a⁻¹ = q := by rw [← h1]; group
      rw [MulAut.conjNormal_apply]
      show a * (qN : G) * a⁻¹ = (qN : G)
      rw [show (qN : G) = q from hqNq]
      exact h2
    exact ⟨(k : ZMod 2), frattini_add_apply π (MulAut.conjNormal a₁) (ρ a₁ : V →ₗ[ZMod 2] V)
      (hπρ a₁) hm hα⟩
  let κ₀ : ↥L →* LinearMap.GeneralLinearGroup (ZMod 2) V := ρ.comp (Subgroup.inclusion hL₁)
  have hker : ∀ l : ↥L, κ₀ l = 1 ↔ l ∈ CFSG.pCore 2 ↥L := by
    intro l
    have h1 : κ₀ l = 1 ↔ (l : G) ∈ pCoreOf 2 G₁ :=
      (hρk (Subgroup.inclusion hL₁ l)).trans
        (mem_pCore_iff_mem_pCoreOf (Subgroup.inclusion hL₁ l))
    rw [h1, mem_pCore_iff_mem_pCoreOf l]
    exact ⟨fun h => pCoreOf_inf_le hL₁ ⟨h, l.2⟩,
      fun h => pCoreOf_mono_of_le_normalizer hL₁ hLn h⟩
  let κ : oTwoQuot ↥L →* LinearMap.GeneralLinearGroup (ZMod 2) V :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) κ₀ fun l hl => (hker l).2 hl
  have hκ : ∀ l : ↥L, κ (l : oTwoQuot ↥L) = κ₀ l := fun l => rfl
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [hκ] at hx
      exact (QuotientGroup.eq_one_iff l).2 ((hker l).1 hx)
  have hnorm : ∀ x : oTwoQuot ↥L, ρ a₁ * κ x * (ρ a₁)⁻¹ ∈ κ.range := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H l =>
      have hl' : a * (l : G) * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hLn haG₁) l).1 l.2
      refine ⟨((⟨a * l * a⁻¹, hl'⟩ : ↥L) : oTwoQuot ↥L), ?_⟩
      rw [hκ, hκ]
      show ρ (Subgroup.inclusion hL₁ ⟨a * l * a⁻¹, hl'⟩) =
        ρ a₁ * ρ (Subgroup.inclusion hL₁ l) * (ρ a₁)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
  have hcomm := commute_of_normalizing_transvection hq hno κ hκinj ht hnorm
  intro l hl
  have h1 := hcomm ((⟨l, hl⟩ : ↥L) : oTwoQuot ↥L)
  rw [hκ] at h1
  have h2 : ρ (⟨l, hL₁ hl⟩ * a₁ * ⟨l, hL₁ hl⟩⁻¹ * a₁⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1' : ρ ⟨l, hL₁ hl⟩ * ρ a₁ = ρ a₁ * ρ ⟨l, hL₁ hl⟩ := h1
    rw [h1']
    group
  exact (mem_pCore_iff_mem_pCoreOf _).1 ((hρk _).1 h2)

theorem conjClosure_le_ballStab_one (hc : CritAmalgam G₀ G₁ G₂ T Z) {L : Subgroup G}
    (hL₁ : L ≤ G₁) (hLn : G₁ ≤ Subgroup.normalizer (L : Set G)) (hLG : G₁ = L ⊔ (G₁ ⊓ G₂))
    (hq : CFSG.IsQuasisimple (oTwoQuot ↥L)) (hno : NoMcLaughlinCover (oTwoQuot ↥L))
    (hcyc : ∃ c ∈ pCoreOf 2 G₁, pCoreOf 2 G₁ ≤ Subgroup.zpowers c ⊔ pCoreOf 2 G₂) :
    conjClosure Z G₂ ≤ CosetGeom.ballStab 1 (CosetGeom.γ₀ G₀ G₁ G₂) := by
  by_contra hcon
  obtain ⟨a, haA, haN⟩ := SetLike.not_le_iff_exists.mp hcon
  apply haN
  rw [hc.ballStab_one_eq]
  refine CFSG.Quasithin.mem_coreIn.2
    ⟨(hc.amalgam.T_le (hc.conjClosure_le_T haA)).1, fun h hh => ?_⟩
  have hmul : (↑(L ⊔ (G₁ ⊓ G₂)) : Set G) = (L : Set G) * ((G₁ ⊓ G₂ : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L (G₁ ⊓ G₂) (inf_le_left.trans hLn)
  have hh' : h⁻¹ ∈ (L : Set G) * ((G₁ ⊓ G₂ : Subgroup G) : Set G) := by
    rw [← hmul, SetLike.mem_coe, ← hLG]
    exact G₁.inv_mem hh
  obtain ⟨l, hl, b, hb, hlb⟩ := Set.mem_mul.mp hh'
  have hbA : b * a * b⁻¹ ∈ conjClosure Z G₂ :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Z G₂ hb.2) a).mp haA
  have hbR : b * a * b⁻¹ ∉ pCoreOf 2 G₁ := by
    intro hR
    have hbN := le_normalizer_pCoreOf 2 G₁ hb.1
    have : a ∈ pCoreOf 2 G₁ := (Subgroup.mem_normalizer_iff.mp hbN a).mpr hR
    exact haN (hc.pCoreOf_left_le_ballStab this)
  have hcomm := comm_mem_pCoreOf hc hL₁ hLn hq hno hcyc hbA hbR l hl
  have hbab : b * a * b⁻¹ ∈ G₁ ⊓ G₂ := hc.amalgam.T_le (hc.conjClosure_le_T hbA)
  have h3 : l * (b * a * b⁻¹) * l⁻¹ ∈ G₁ ⊓ G₂ := by
    have := (G₁ ⊓ G₂).mul_mem (hc.pCoreOf_left_le hcomm) hbab
    simpa [mul_assoc] using this
  have e : h⁻¹ * a * h = l * (b * a * b⁻¹) * l⁻¹ := by
    have : h = (l * b)⁻¹ := by rw [hlb, inv_inv]
    rw [this]
    group
  rw [e]
  exact h3

theorem three_le_critB_of_le (hc : CritAmalgam G₀ G₁ G₂ T Z)
    (h : conjClosure Z G₂ ≤ CosetGeom.ballStab 1 (CosetGeom.γ₀ G₀ G₁ G₂)) :
    3 ≤ critB G₀ G₁ G₂ Z := by
  rw [le_critB_iff hc]
  intro μ hμ
  by_cases hμ2 : CosetGeom.dist (CosetGeom.γ₀ G₀ G₁ G₂) μ < 2
  · exact lt_critB_imp hc (lt_of_lt_of_le hμ2 (two_le_critB hc))
  · have hd : CosetGeom.dist (CosetGeom.γ₀ G₀ G₁ G₂) μ = 1 + 1 := by omega
    obtain ⟨δ, hμδ, hδ⟩ := CosetGeom.exists_adj_dist_eq hc.amalgam.gen hd
    have hγδ : δ ∈ CosetGeom.nbrs (CosetGeom.γ₀ G₀ G₁ G₂) := CosetGeom.dist_eq_one_iff_adj.mp hδ
    have hδt : CosetGeom.vtype δ = true := vtype_eq_true_of_mem_nbrs CosetGeom.vtype_γ₀ hγδ
    have hμt : CosetGeom.vtype μ = false :=
      vtype_eq_false_of_mem_nbrs hδt (show μ ∈ CosetGeom.nbrs δ from hμδ.symm)
    obtain ⟨g, rfl, rfl⟩ := exists_edge_conj hμt (show δ ∈ CosetGeom.nbrs μ from hμδ)
    have h1 : CosetGeom.Vv Z (CosetGeom.γ₀ G₀ G₁ G₂) ≤
        CosetGeom.Vv Z (g • CosetGeom.γ₁ G₀ G₁ G₂) :=
      Vv_le_Vv_of_mem_nbrs hδt (CosetGeom.mem_nbrs_symm hγδ)
    rw [CosetGeom.Vv_γ₀ hc.normalizes, CosetGeom.Vv_smul hc.normalizes,
      CosetGeom.Vv_γ₁ hc.amalgam.le₂ hc.normalizes] at h1
    rw [CosetGeom.ballStab_smul]
    exact h1.trans (conjSub_mono _ h)

end Main

section SettingLevel

namespace Setting

variable {G : Type} [Group G] [Finite G] {L₁ L₂ S Z : Subgroup G}

theorem exists_mem_zpowers_sup (hs : Setting L₁ L₂ S Z) :
    ∃ c ∈ pCoreOf 2 (P₂ L₁ L₂ S),
      pCoreOf 2 (P₂ L₁ L₂ S) ≤ Subgroup.zpowers c ⊔ pCoreOf 2 (P₁ L₁ L₂ S) := by
  have hc := hs.toCritAmalgam
  have hRle : pCoreOf 2 (P₂ L₁ L₂ S) ≤ P₁ L₁ L₂ S := hc.pCoreOf_left_le.trans inf_le_right
  obtain ⟨x, hxP, hx⟩ :=
    isSylowTwoOf_exists_conj_le (lemma61_sylow hs.hyp) hRle (pCoreOf_isPGroup 2 _)
  have hRL₁ : pCoreOf 2 (P₂ L₁ L₂ S) ≤ L₁ := by
    refine hx.trans ?_
    have : conjSub x S ≤ conjSub x L₁ := conjSub_mono x hs.S_le
    rwa [conjSub_eq_of_mem_normalizer (P₁_le_normalizer hs.hyp hxP)] at this
  have := exists_mem_zpowers_sup_pCoreOf hRL₁ (pCoreOf_isPGroup 2 _) hs.cyclic
  rwa [← pCoreOf_P₁ hs.hyp hs.S_le] at this

theorem three_le_critB (hs : Setting L₁ L₂ S Z) (hq : CFSG.IsQuasisimple (oTwoQuot ↥L₂))
    (hno : NoMcLaughlinCover (oTwoQuot ↥L₂)) :
    3 ≤ critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z := by
  have hc := hs.toCritAmalgam
  refine three_le_critB_of_le hc
    (conjClosure_le_ballStab_one hc (L := L₂) le_sup_left ?_ ?_ hq hno hs.exists_mem_zpowers_sup)
  · exact sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hs.hyp).2
  · rw [F112W.inf_alpha_beta hs.hyp]

end Setting

end SettingLevel

end CFSG.Quasithin.F112Crit
