module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4FF
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Insp

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436
open scoped commutatorElement IsMulCommutative

namespace L436

theorem pRank_le_one_of_surjective' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M N : Type*}
    [Group M] [Group N] [Finite M] [Finite N] (ψ : M →* N) (hψ : Function.Surjective ψ)
    (hM : CFSG.pRank p M ≤ 1) : CFSG.pRank p N ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow p M) := inferInstance
  have hP₀ : CFSG.pRank p (P₀ : Subgroup M) ≤ 1 := (CFSG.SectionRank.pRank_sylow P₀).2 ▸ hM
  have hcyc : IsCyclic (P₀ : Subgroup M) :=
    ((CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hp P₀.isPGroup').1
      hP₀).resolve_right fun h => hp2 h.1
  have hQ : IsCyclic ((P₀.mapSurjective hψ : Sylow p N) : Subgroup N) := by
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective (ψ.subgroupMap _) (ψ.subgroupMap_surjective _)
  rw [← (CFSG.SectionRank.pRank_sylow (P₀.mapSurjective hψ)).2]
  exact (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hp
    (P₀.mapSurjective hψ).isPGroup').2 (Or.inl hQ)

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem le_of_perfect_of_le_sup_of_isPGroup' {p : ℕ} [Fact p.Prime] {X A P : Subgroup Ω}
    (hn : A ⊔ P ≤ Subgroup.normalizer (A : Set Ω)) (hP : IsPGroup p P) (hX : ⁅X, X⁆ = X)
    (hXle : X ≤ A ⊔ P) : X ≤ A := by
  set Y : Subgroup Ω := A ⊔ P with hY
  have hAY : A ≤ Y := le_sup_left
  have hPY : P ≤ Y := le_sup_right
  have : (A.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAY).mpr hn
  set π := QuotientGroup.mk' (A.subgroupOf Y) with hπ
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion hPY)) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf Y) z
    have hPn : P ≤ Subgroup.normalizer (A : Set Ω) := hPY.trans hn
    have hx : (x : Ω) ∈ (↑(P ⊔ A) : Set Ω) := by rw [sup_comm]; exact x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P A hPn] at hx
    obtain ⟨q, hq, l, hl, hql⟩ := hx
    refine ⟨⟨q, hq⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((Subgroup.inclusion hPY ⟨q, hq⟩)⁻¹ * x : ↥Y) = (l : Ω) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hql]
      group
    rw [this]
    exact hl
  have hpq : IsPGroup p (↥Y ⧸ A.subgroupOf Y) := hP.of_surjective _ hsurj
  have : Group.IsNilpotent (↥Y ⧸ A.subgroupOf Y) := hpq.isNilpotent
  have : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
  have : Group.IsPerfect ↥(X.subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXle).symm.surjective
  have hbot : (X.subgroupOf Y).map π = ⊥ := by
    by_contra hne
    have : Nontrivial ↥((X.subgroupOf Y).map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hperf : Group.IsPerfect ↥((X.subgroupOf Y).map π) :=
      Group.IsPerfect.ofSurjective (π.subgroupMap_surjective (X.subgroupOf Y))
    have hsol : Group.IsSolvable ↥((X.subgroupOf Y).map π) :=
      Group.isSolvable_of_isSolvable_injective ((X.subgroupOf Y).map π).subtype_injective
    exact Group.IsPerfect.not_isSolvable ↥((X.subgroupOf Y).map π) hsol
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro k hk
  have : (⟨k, hXle hk⟩ : ↥Y) ∈ A.subgroupOf Y := hbot hk
  exact this

end L436

variable {G : Type} [Group G] [Finite G]

namespace Setting436Sp4

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (s : Setting436Sp4 G T M L n I H K t)
include s

theorem pCoreOf_GZ_le_normalizer_K₂ :
    pCoreOf 2 (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) ≤
      Subgroup.normalizer (sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) := by
  set V := v432 T M L with hV
  set K₂ := sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hK₂
  set Q₁ := sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hQ₁
  set GZ := Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) with hGZ
  set QZ := pCoreOf 2 GZ with hQZ
  have hK₂GZ : K₂ ≤ GZ := s.concl.K₂_le.trans (Subgroup.centralizer_le_normalizer _)
  have hQ₁V : Q₁ ≤ Subgroup.normalizer (V : Set G) := by
    have hSV : T ⊓ H ⊓ K ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
      s.T_le_normalizer_V hg.1.1
    exact (le_sup_right.trans s.concl.S_eq.symm.le).trans hSV
  have key : ∀ x ∈ QZ, ∀ k ∈ K₂, ∀ v ∈ V, x * (k * v * k⁻¹) * x⁻¹ ∈ K₂ := by
    intro x hx k hk v hv
    have hx' : k⁻¹ * x * k ∈ QZ := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 GZ
        (inv_mem (hK₂GZ hk))) x).mp hx
      simpa using this
    obtain ⟨q, hq, hqV⟩ := s.starstar hx'
    have hqv : q⁻¹ * v * q ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hQ₁V (inv_mem hq)) v).mp hv
      simpa using this
    have h1 := hqV _ hqv
    have e : x * (k * v * k⁻¹) * x⁻¹ =
        k * ((k⁻¹ * x * k * q) * (q⁻¹ * v * q) * (k⁻¹ * x * k * q)⁻¹) * k⁻¹ := by group
    rw [e, h1]
    have hqK : q ∈ K₂ := pCoreOf_le 2 K₂ hq
    exact mul_mem (mul_mem hk (mul_mem (mul_mem (inv_mem hqK) (s.concl.V_le_K₂ hv)) hqK))
      (inv_mem hk)
  have hle : ∀ x ∈ QZ, ∀ g ∈ K₂, x * g * x⁻¹ ∈ K₂ := by
    intro x hx
    have h1 : conjClosure V K₂ ≤ K₂.comap (MulAut.conj x).toMonoidHom :=
      conjClosure_le fun k hk v hv => by
        simpa [MulAut.conj_apply] using key x hx k hk v hv
    intro g hg
    have hcl : conjClosure V K₂ = K₂ := s.concl.K₂_closure
    rw [← hcl] at hg
    simpa [MulAut.conj_apply] using h1 hg
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => hle x hx g hg, fun hg => ?_⟩
  have := hle x⁻¹ (inv_mem hx) _ hg
  simpa [mul_assoc] using this

theorem T_le_normalizer_K₂ (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : Lemma122A) (hF : A318Facts) (h56 : AsB56) (hInsp : InspFF436) {KZ : Subgroup G}
    (hKZ : KZ ∈ cComp (Subgroup.centralizer
      (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)))
    (hK₂ : sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ KZ) :
    T ≤ Subgroup.normalizer (sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) := by
  classical
  set V := v432 T M L with hV
  set K₂ := sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hK₂def
  set Q₁ := sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hQ₁
  set GZ := Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) with hGZ
  set U := conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L)) GZ with hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKZn := s.KZ_normal h37 h38 h122 hKZ hK₂
  have hq := s.KZ_quasisimple h36 hKZ hK₂
  have hKZ' := cComp_normalizer hKZ
  have hKZGZ : KZ ≤ GZ := le_of_mem_cComp hKZ'
  have hGZKZ : GZ ≤ Subgroup.normalizer (KZ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKZGZ).1 hKZn
  have hVKZ : V ≤ KZ := s.concl.V_le_K₂.trans hK₂
  have hred := s.isTwoReducedIn_U
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hU2 : ∀ w ∈ U, w ^ 2 = 1 := hred.2.2.1.2
  have hGZU : GZ ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKZU : KZ ≤ Subgroup.normalizer (U : Set G) := hKZGZ.trans hGZU
  have hO2 : pCoreOf 2 (autOn GZ U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hKle : autOn KZ U ≤ autOn GZ U := InternalSec.autOn_le_autOn_of_le hKZGZ
  have hKn : ((autOn KZ U).subgroupOf (autOn GZ U)).Normal :=
    (Subgroup.normal_subgroupOf_iff hKle).2 fun k j hk hj =>
      InternalSec.autOn_normal_of hGZKZ j hj k hk
  have hO2K : pCoreOf 2 (autOn KZ U) = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ hKle hKn
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hO₂QZ : pCoreOf 2 KZ ≤ pCoreOf 2 GZ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 KZ).trans hKZGZ)
      (hGZKZ.trans (normalizer_le_normalizer_pCoreOf 2 KZ)) (pCoreOf_isPGroup 2 KZ)
  have hO₂C : pCoreOf 2 KZ ≤ Subgroup.centralizer (U : Set G) :=
    hO₂QZ.trans s.pCoreOf_GZ_le_centralizer_U
  have hnt : ¬ KZ ≤ Subgroup.centralizer (U : Set G) := fun h =>
    s.not_V_le_centralizer_U (hVKZ.trans h)
  have hKq : CFSG.IsQuasisimple ↥(autOn KZ U) :=
    InternalSec.isQuasisimple_autOn hKZU hq hO2K hnt
  set Vs := autOn V U with hVs
  have hVsK : Vs ≤ autOn KZ U := InternalSec.autOn_le_autOn_of_le hVKZ
  have hcardVs : Nat.card ↥Vs = 2 ^ n := s.card_autOn_V
  have hfixeq : fixV Vs = (Subgroup.centralizer (V : Set G)).subgroupOf U := by
    ext w
    rw [mem_fixV, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hw v hv
      have h1 := hw _ (InternalSec.conjAct_mem_autOn s.V_le_normalizer_U hv)
      have h2 := congrArg Subtype.val h1
      rw [InternalSec.coe_conjAct_apply] at h2
      calc v * (w : G) = (v * w * v⁻¹) * v := by group
        _ = w * v := by rw [h2]
    · intro hw x hx
      obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hx
      apply Subtype.ext
      rw [InternalSec.coe_conjAct_apply, hw g hg, mul_inv_cancel_right]
  have hcardfix : Nat.card ↥(fixV Vs) = Nat.card ↥(U ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [hfixeq]
    exact Nat.card_congr
      { toFun := fun w => ⟨(w : ↥U), (w : ↥U).2, w.2⟩
        invFun := fun w => ⟨⟨w, w.2.1⟩, w.2.2⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  have hoff : Nat.card ↥U ≤ Nat.card ↥Vs * Nat.card ↥(fixV Vs) := by
    rw [hcardVs, hcardfix]
    exact s.card_U_le
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := mul_comm_of_exp_two s.concl.V_sq
  have hVsne : Vs ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardVs
    have := s.four_le_two_pow
    omega
  have hVsel : IsElemAbelian2 Vs := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 ha
      obtain ⟨g', hg', rfl⟩ := Setup.mem_autOn_iff.1 hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hVab g hg g' hg')
    · obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 ha
      rw [← map_pow]
      have : g ^ 2 = 1 := Subtype.ext (by simpa using s.concl.V_sq g hg)
      rw [this, map_one]
  obtain ⟨B, hBVs, hB, hBc⟩ := B1.exists_offender_below (X := autOn KZ U) (A := Vs)
    ⟨hVsK, hVsne, hVsel⟩ 0 (by simpa using hoff)
  have hLA : ⁅autOn KZ U, B⁆ = autOn KZ U := by
    rcases L436.commutator_eq_or_eq_bot_of_quasisimple hKq
        ((hBVs.trans hVsK).trans Subgroup.le_normalizer) with h | h
    · exact h
    · exfalso
      obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB.2.1
      obtain ⟨g, hgV, hgb⟩ := Setup.mem_autOn_iff.1 (hBVs hbB)
      have hcomm : ∀ k ∈ autOn KZ U, k * b = b * k := by
        intro k hk
        have hk' : ⁅k, b⁆ ∈ ⁅autOn KZ U, B⁆ := Subgroup.commutator_mem_commutator hk hbB
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hk'
        exact hk'
      apply hb1
      apply Subtype.ext
      show b = 1
      rw [← hgb]
      have hgK : (g : G) ∈ K₂ := s.concl.V_le_K₂ hgV
      have hgQ : (g : G) ∈ Q₁ := s.mem_Q₁_of_commutator_mem hgK fun k hk => by
        have hk' : k ∈ Subgroup.normalizer (U : Set G) := hKZU (hK₂ hk)
        have h1 := hcomm _ (InternalSec.conjAct_mem_autOn hKZU (hK₂ hk))
        have h2 : conjAct U (g * ⟨k, hk'⟩ * g⁻¹ * ⟨k, hk'⟩⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hgb, ← h1]
          group
        have h3 := mem_centralizer_of_conjAct_eq_one _ h2
        have h3' : (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
          simpa using h3
        exact s.K₂_inf_centralizer_U_le (Subgroup.mem_inf.mpr
          ⟨mul_mem (mul_mem (mul_mem hgK hk) (inv_mem hgK)) (inv_mem hk), h3'⟩)
      exact InternalSec.conjAct_eq_one_of_mem_centralizer g (s.Q₁_le_centralizer_U hgQ)
  have hSY : SQTKGroup ↥KZ := InternalSec.sqtkGroup_mono s.sqtkGroup_GZ hKZGZ
  obtain ⟨hKJ, -, -, -, hcases⟩ := InternalSec.b56Cases_ffJ_autOn h56 hU2 hKZU le_rfl
    Subgroup.le_normalizer hSY hO2K hB hLA
  have hJ : ffJ (autOn KZ U) = autOn KZ U := le_antisymm (B6.ffJ_le _) hKJ
  rw [hJ] at hcases
  have h1 := L436.b56Case1_of_isQuasisimple hKq hcases
  have hFst : quasithinGenFitting (autOn KZ U) = autOn KZ U :=
    InternalSec.eq_of_le_quasisimple le_rfl (fun x hx k hk =>
      mul_mem (mul_mem hx hk) (inv_mem hx)) hKq h1.1
  have hlist : B56QuasisimpleList ↥(autOn KZ U) := by
    have := h1.2.2
    rwa [hFst] at this
  have hK₂U : K₂ ≤ Subgroup.normalizer (U : Set G) := hK₂.trans hKZU
  have hK₂le : autOn K₂ U ≤ autOn KZ U := InternalSec.autOn_le_autOn_of_le hK₂
  have hker₂ : (InternalSec.autOnHom hK₂U).ker = CFSG.pCore 2 ↥K₂ := by
    ext k
    rw [InternalSec.mem_ker_autOnHom]
    constructor
    · intro hk
      have hkQ : (k : G) ∈ Q₁ := s.K₂_inf_centralizer_U_le ⟨k.2, hk⟩
      obtain ⟨y, hy, hyk⟩ := hkQ
      have : y = k := Subtype.ext hyk
      rw [← this]
      exact hy
    · intro hk
      exact s.Q₁_le_centralizer_U ⟨k, hk, rfl⟩
  have hpsl : IsPSL 2 2 n ↥(autOn K₂ U) := by
    obtain ⟨hadm, F, hF', hFf, hcard, ⟨e⟩⟩ := s.concl.psl
    have e₁ := (QuotientGroup.quotientKerEquivOfSurjective (InternalSec.autOnHom hK₂U)
      (InternalSec.autOnHom_surjective hK₂U)).symm
    have e₂ := QuotientGroup.quotientMulEquivOfEq hker₂
    exact ⟨hadm, F, hF', hFf, hcard, ⟨(e₁.trans e₂).trans e⟩⟩
  obtain ⟨p, hp, hp2, hpn⟩ := s.exists_odd_prime_dvd
  have : Fact p.Prime := ⟨hp⟩
  have hBn : Nat.card ↥B ≤ 2 ^ n := hcardVs ▸ Subgroup.card_le_of_le hBVs
  have hNcomm : ∀ c ∈ KZ ⊓ Subgroup.centralizer (U : Set G), ∀ k ∈ KZ,
      c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 KZ := by
    refine L436.commutator_mem_pCoreOf_of_quasisimple hq inf_le_left (fun k hk =>
      mem_normalizer_inf (Subgroup.le_normalizer hk)
        (InternalSec.le_normalizer_centralizer hKZU hk)) fun hle => ?_
    exact hnt (hle.trans (sup_le inf_le_right hO₂C))
  have hcond : CFSG.Open.pRank p (autOn KZ U) ≤ 1 ∨
      (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥(autOn KZ U) →* S), Function.Surjective φ ∧
        (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
        ∃ (s' : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s' then 1 else -1) ∧
          IsPSLEps3q s' q S) := by
    rcases s.pRank_KZ_le_one hF h36 h38 hKZ hK₂ hKZn hp hp2 hpn with hr | ⟨hp3, h2⟩
    · left
      have hM : CFSG.pRank p ↥KZ ≤ 1 := by
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype]
        exact hr
      have h' := L436.pRank_le_one_of_surjective' hp hp2
        (InternalSec.autOnHom hKZU) (InternalSec.autOnHom_surjective hKZU) hM
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype] at h'
      exact h'
    · right
      subst hp3
      obtain ⟨s', q, hcong, hpslq, -⟩ := h2
      set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥GZ) with hπ
      set SK := starImage 3 (KZ.subgroupOf GZ) with hSK
      have := L436.isSimpleGroup_of_isPSLEps3q hpslq
      let ψ₀ : ↥KZ →* PStar 3 ↥GZ := π.comp (Subgroup.inclusion hKZGZ)
      have hrange : ψ₀.range = SK := by
        rw [MonoidHom.range_comp, Subgroup.inclusion_range]
      let ψ : ↥KZ →* ↥SK := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ₀.rangeRestrict
      have hψ : Function.Surjective ψ :=
        (MulEquiv.subgroupCongr hrange).surjective.comp ψ₀.rangeRestrict_surjective
      have hψv : ∀ k : ↥KZ, ((ψ k : ↥SK) : PStar 3 ↥GZ) = π ⟨k, hKZGZ k.2⟩ := fun k => rfl
      have hperf : Group.IsPerfect ↥SK := by
        have : Group.IsPerfect ↥KZ := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hKZ)
        exact Group.IsPerfect.ofSurjective hψ
      have hO₂3 : ∀ k : ↥KZ, (k : G) ∈ pCoreOf 2 KZ → π ⟨k, hKZGZ k.2⟩ = 1 := by
        intro k hk
        exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥GZ)
          (⟨k, hKZGZ k.2⟩ : ↥GZ)).mpr
          (pCoreOf_subgroupOf_le_pPrimeCore (x := ⟨k, hKZGZ k.2⟩) hKZGZ hGZKZ hk)
      have hker : (InternalSec.autOnHom hKZU).ker ≤ ψ.ker := by
        intro c hc
        rw [InternalSec.mem_ker_autOnHom] at hc
        rw [MonoidHom.mem_ker]
        apply L436.eq_one_of_forall_commute hperf
        intro y
        obtain ⟨k, rfl⟩ := hψ y
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hψv, hψv, ← map_mul, ← map_mul]
        have hck := hNcomm c ⟨c.2, hc⟩ k k.2
        have h1 : π ⟨(c : G) * k * (c : G)⁻¹ * (k : G)⁻¹, hKZGZ (mul_mem (mul_mem (mul_mem c.2 k.2)
            (inv_mem c.2)) (inv_mem k.2))⟩ = 1 :=
          hO₂3 ⟨_, mul_mem (mul_mem (mul_mem c.2 k.2) (inv_mem c.2)) (inv_mem k.2)⟩ hck
        have e : (⟨(c : G), hKZGZ c.2⟩ * ⟨(k : G), hKZGZ k.2⟩ : ↥GZ) =
            ⟨(c : G) * k * (c : G)⁻¹ * (k : G)⁻¹, hKZGZ (mul_mem (mul_mem (mul_mem c.2 k.2)
              (inv_mem c.2)) (inv_mem k.2))⟩ * (⟨(k : G), hKZGZ k.2⟩ * ⟨(c : G), hKZGZ c.2⟩) := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group
        rw [e, map_mul, h1, one_mul, map_mul]
      let e₀ := QuotientGroup.quotientKerEquivOfSurjective (InternalSec.autOnHom hKZU)
        (InternalSec.autOnHom_surjective hKZU)
      let φ : ↥(autOn KZ U) →* ↥SK :=
        (QuotientGroup.lift _ ψ hker).comp e₀.symm.toMonoidHom
      have hφ : ∀ k : ↥KZ, φ (InternalSec.autOnHom hKZU k) = ψ k := by
        intro k
        show QuotientGroup.lift _ ψ hker (e₀.symm (InternalSec.autOnHom hKZU k)) = ψ k
        have : e₀.symm (InternalSec.autOnHom hKZU k) = (QuotientGroup.mk k : ↥KZ ⧸ _) := by
          apply e₀.injective
          rw [MulEquiv.apply_symm_apply]
          rfl
        rw [this, QuotientGroup.lift_mk]
      refine ⟨rfl, ↥SK, inferInstance, φ, ?_, ?_, s', q, hcong, hpslq⟩
      · intro y
        obtain ⟨k, rfl⟩ := hψ y
        exact ⟨InternalSec.autOnHom hKZU k, hφ k⟩
      · intro x hx
        obtain ⟨k, rfl⟩ := InternalSec.autOnHom_surjective hKZU x
        rw [MonoidHom.mem_ker, hφ] at hx
        have hk3 : (⟨k, hKZGZ k.2⟩ : ↥GZ) ∈ CFSG.pPrimeCore 3 ↥GZ := by
          rw [← QuotientGroup.eq_one_iff]
          have := congrArg Subtype.val hx
          rw [hψv] at this
          exact this
        have hcop : Nat.Coprime 3 (orderOf (⟨k, hKZGZ k.2⟩ : ↥GZ)) :=
          Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hk3)
            CFSG.pPrimeCore_coprime_card
        have hdvd : orderOf (InternalSec.autOnHom hKZU k) ∣ orderOf k := orderOf_map_dvd _ k
        have hk' : orderOf k = orderOf (⟨k, hKZGZ k.2⟩ : ↥GZ) := by
          rw [← Subgroup.orderOf_coe k, ← Subgroup.orderOf_coe (⟨k, hKZGZ k.2⟩ : ↥GZ)]
        intro h3
        have := (Nat.Coprime.coprime_dvd_right (hk' ▸ hdvd) hcop)
        exact absurd (Nat.Coprime.eq_one_of_dvd this h3) (by norm_num)
  have hU2' : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hU2 u u.2)
  have hEq : autOn KZ U = autOn K₂ U := hInsp ↥U hU2' (autOn KZ U) (autOn K₂ U) B n p
    s.sk.base.hyp.two_le hKq hlist hK₂le hpsl
    (hBVs.trans (InternalSec.autOn_le_autOn_of_le s.concl.V_le_K₂)) hB.2.1 hB.2.2.1 hBn
    (by simpa using hBc) hp hp2 hpn hcond
  have hfac : ∀ x ∈ KZ, ∃ a ∈ K₂, ∀ k ∈ KZ,
      (a⁻¹ * x) * k * (a⁻¹ * x)⁻¹ * k⁻¹ ∈ pCoreOf 2 KZ := by
    intro x hx
    have hxs : conjAct U ⟨x, hKZU hx⟩ ∈ autOn K₂ U :=
      hEq ▸ InternalSec.conjAct_mem_autOn hKZU hx
    obtain ⟨g, hg, hgx⟩ := Setup.mem_autOn_iff.1 hxs
    refine ⟨g, hg, fun k hk => hNcomm _ (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hK₂ hg)) hx, ?_⟩)
      k hk⟩
    have h1 : conjAct U (g⁻¹ * ⟨x, hKZU hx⟩) = 1 := by
      rw [map_mul, map_inv, hgx, inv_mul_cancel]
    have := mem_centralizer_of_conjAct_eq_one _ h1
    simpa using this
  have hKZle : KZ ≤ K₂ ⊔ pCoreOf 2 KZ := L436.le_sup_pCoreOf_of_quasisimple hq hK₂ hfac
  have hO₂K₂ : pCoreOf 2 KZ ≤ Subgroup.normalizer (K₂ : Set G) :=
    hO₂QZ.trans s.pCoreOf_GZ_le_normalizer_K₂
  have hKZK₂ : KZ ≤ K₂ := L436.le_of_perfect_of_le_sup_of_isPGroup'
    (sup_le Subgroup.le_normalizer hO₂K₂) (pCoreOf_isPGroup 2 KZ) (perfect_of_mem_cComp hKZ)
    hKZle
  have hKZeq : KZ = K₂ := le_antisymm hKZK₂ hK₂
  rw [← hKZeq]
  exact s.T_le_normalizer_Z.trans hGZKZ

end Setting436Sp4

theorem step436Sp4_of (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : Lemma122A) (hF : A318Facts) (h56 : AsB56) (hInsp : InspFF436)
    (hKZ : Step436KZ) : Step436Sp4 := by
  intro G _ _ T M L n I H K t s
  obtain ⟨KZ, hKZ', hK₂⟩ := hKZ G T M L n I H K t s
  exact s.T_le_normalizer_K₂ h36 h37 h38 h122 hF h56 hInsp hKZ' hK₂

end CFSG.Quasithin.H13.Ch4
