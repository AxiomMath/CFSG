module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4A318
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.Background.InternalSecB56M

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436
open scoped commutatorElement

namespace L436

theorem nontrivial_statedSL_two {F : Type} [Field F] : Nontrivial ↥(StatedSL 2 F) := by
  refine ⟨⟨uT F 1, 1, fun h => ?_⟩⟩
  have := congrArg
    (fun g : ↥(StatedSL 2 F) => ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [uT] at this

theorem nontrivial_statedSL_three {F : Type} [Field F] [Finite F] (h2 : 2 ≤ Nat.card F) :
    Nontrivial ↥(StatedSL 3 F) := by
  rw [← Finite.one_lt_card_iff_nontrivial, CFSG.SectionRank.OddCover.card_statedSL_three]
  have h8 : 8 ≤ Nat.card F ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left h2 3
  have h4 : 4 ≤ Nat.card F ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h2 2
  have h3 : 3 ≤ Nat.card F ^ 2 - 1 := by omega
  have h7 : 7 ≤ Nat.card F ^ 3 - 1 := by omega
  calc 1 < 8 * 3 * 7 := by norm_num
    _ ≤ Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h8 h3) h7

theorem nontrivial_of_b56FactorList {X : Type} [Group X] (h : B56FactorList X) : Nontrivial X := by
  rcases h with ⟨n, K, _, _, hn, -, ⟨e⟩⟩ | he | ⟨m, K, _, _, hm, -, hcard, ⟨e⟩⟩
  · have := nontrivial_statedSL_two (F := K)
    exact e.toEquiv.nontrivial
  · obtain ⟨e⟩ := he
    exact e.toEquiv.nontrivial
  · have h2 : 2 ≤ Nat.card K := by
      rw [hcard]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have := nontrivial_statedSL_three h2
    exact e.toEquiv.nontrivial

theorem nontrivial_statedSL_three_two : Nontrivial ↥(StatedSL 3 (ZMod 2)) :=
  nontrivial_statedSL_three (by rw [Nat.card_zmod])

section B56

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem eq_bot_of_sup_le {G₁ G₂ : Subgroup (MulAut V)} (hle : G₁ ⊔ G₂ ≤ G₁)
    (hinf : G₁ ⊓ G₂ = ⊥) : G₂ = ⊥ := by
  rw [eq_bot_iff, ← hinf]
  exact le_inf (le_sup_right.trans hle) le_rfl

omit [Finite V] in
theorem not_b56FactorList_bot : ¬ B56FactorList ↥(⊥ : Subgroup (MulAut V)) := fun h => by
  have := nontrivial_of_b56FactorList h
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(⊥ : Subgroup (MulAut V))
  exact hab (Subsingleton.elim a b)

omit [Finite V] in
theorem not_mulEquiv_sl3_bot :
    ¬ Nonempty (↥(⊥ : Subgroup (MulAut V)) ≃* ↥(StatedSL 3 (ZMod 2))) := fun ⟨e⟩ => by
  have := nontrivial_statedSL_three_two
  have : Nontrivial ↥(⊥ : Subgroup (MulAut V)) := e.toEquiv.nontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(⊥ : Subgroup (MulAut V))
  exact hab (Subsingleton.elim a b)

theorem b56Case1_of_isQuasisimple {J : Subgroup (MulAut V)} (hJ : CFSG.IsQuasisimple ↥J)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) : B56Case1 J := by
  have hn : ∀ x ∈ J, ∀ k ∈ J, x * k * x⁻¹ ∈ J := fun x hx k hk =>
    J.mul_mem (J.mul_mem hx hk) (J.inv_mem hx)
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, hout, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hc, -, he₁, -, -, h₂⟩
  · exact h1
  · exact (InternalSec.not_le_perm_three hJ le_rfl e).elim
  · exfalso
    rcases InternalSec.le_or_le_of_sup_eq hsup hc le_rfl hn hJ with h | h
    · have hG₂ := eq_bot_of_sup_le (hsup.le.trans h) hinf
      subst hG₂
      exact not_b56FactorList_bot hf₂
    · have hinf' : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hinf
      have hG₁ := eq_bot_of_sup_le (sup_comm G₂ G₁ ▸ hsup.le.trans h) hinf'
      subst hG₁
      exact not_b56FactorList_bot hf₁
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases InternalSec.le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ le_rfl hn hJ with h | h
    · have htJ : t ∈ J := by
        rw [hJt]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
      exact hout ⟨t, h htJ, fun x _ => rfl⟩
    · exact InternalSec.not_le_of_card_prime hJ h hc₂
  · exfalso
    rcases InternalSec.le_or_le_of_sup_eq hsup hc le_rfl hn hJ with h | h
    · have hG₂ := eq_bot_of_sup_le (hsup.le.trans h) hinf
      subst hG₂
      rcases h₂ with ⟨he₂, -⟩ | ⟨_, _, _, _, -, _, hR⟩
      · exact not_mulEquiv_sl3_bot he₂
      · refine InternalSec.false_of_realizesVia_nat hR ?_
        have hc0 : commV (⊥ : Subgroup (MulAut V)) = ⊥ := by
          rw [eq_bot_iff, commV, Subgroup.closure_le]
          rintro _ ⟨x, hx, v, rfl⟩
          rw [Subgroup.mem_bot.mp hx]
          simp
        rw [hc0]
        exact bot_le
    · have hinf' : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hinf
      have hG₁ := eq_bot_of_sup_le (sup_comm G₂ G₁ ▸ hsup.le.trans h) hinf'
      subst hG₁
      exact not_mulEquiv_sl3_bot he₁

end B56

variable {Ω : Type} [Group Ω]

theorem commutator_eq_or_eq_bot_of_quasisimple {K A : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K)
    (hA : A ≤ Subgroup.normalizer (K : Set Ω)) : ⁅K, A⁆ = K ∨ ⁅K, A⁆ = ⊥ := by
  have hle : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hA
  have hN : ((⁅K, A⁆ : Subgroup Ω).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left K A)
  have hKo := B1Red.isQuasisimple_to_open hK
  have hKK : ⁅K, K⁆ = K := by
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ K.subtype
    rw [← commutator_def, hKo.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact h2.symm
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hKo
      ((⁅K, A⁆ : Subgroup Ω).subgroupOf K) with h | h
  · right
    have hc : ⁅⁅K, A⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hx' : (⟨x, hle hx⟩ : ↥K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := hx
      have := Subgroup.mem_center_iff.mp (h hx') ⟨k, hk⟩
      exact congrArg Subtype.val this
    have hc' : ⁅⁅A, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm A K]; exact hc
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate hc hc'
    rwa [hKK] at h3
  · left
    refine le_antisymm hle fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := by rw [h]; trivial
    exact this

theorem le_sup_pCoreOf_of_quasisimple {X A : Subgroup Ω}
    (hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)) (hAX : A ≤ X)
    (h : ∀ x ∈ X, ∃ a ∈ A, ∀ k ∈ X,
      (a⁻¹ * x) * k * (a⁻¹ * x)⁻¹ * k⁻¹ ∈ pCoreOf 2 X) :
    X ≤ A ⊔ pCoreOf 2 X := by
  classical
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  set Abar := (A.subgroupOf X).map π with hAbar
  have hmem : ∀ x : ↥X, (x : Ω) ∈ pCoreOf 2 X → x ∈ CFSG.pCore 2 ↥X := by
    rintro x ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hcen : ∀ x : ↥X, ∃ a : ↥X, (a : Ω) ∈ A ∧ ∀ y : ↥X ⧸ CFSG.pCore 2 ↥X,
      π (a⁻¹ * x) * y = y * π (a⁻¹ * x) := by
    intro x
    obtain ⟨a, ha, hc⟩ := h x x.2
    refine ⟨⟨a, hAX ha⟩, ha, fun y => ?_⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) y
    have hk : (⟨a, hAX ha⟩ : ↥X)⁻¹ * x * k * ((⟨a, hAX ha⟩ : ↥X)⁻¹ * x)⁻¹ * k⁻¹ ∈
        CFSG.pCore 2 ↥X := hmem _ (hc k k.2)
    have h2 : π ((⟨a, hAX ha⟩ : ↥X)⁻¹ * x * k * ((⟨a, hAX ha⟩ : ↥X)⁻¹ * x)⁻¹ * k⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hk
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc π ((⟨a, hAX ha⟩ : ↥X)⁻¹ * x) * π k
        = (π ((⟨a, hAX ha⟩ : ↥X)⁻¹ * x) * π k * (π ((⟨a, hAX ha⟩ : ↥X)⁻¹ * x))⁻¹ * (π k)⁻¹) *
            (π k * π ((⟨a, hAX ha⟩ : ↥X)⁻¹ * x)) := by group
      _ = π k * π ((⟨a, hAX ha⟩ : ↥X)⁻¹ * x) := by rw [h2, one_mul]
  have htop : (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) ≤ Abar := by
    rw [← Group.isPerfect_def.mp hq.1, commutator_def, Subgroup.commutator_le]
    intro u _ v _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) v
    obtain ⟨a, ha, hca⟩ := hcen x
    obtain ⟨b, hb, hcb⟩ := hcen y
    have ex : π x = π a * π (a⁻¹ * x) := by rw [← map_mul, mul_inv_cancel_left]
    have ey : π y = π b * π (b⁻¹ * y) := by rw [← map_mul, mul_inv_cancel_left]
    have hc : ⁅π x, π y⁆ = ⁅π a, π b⁆ := by
      rw [commutatorElement_def, commutatorElement_def, ex, ey]
      set c := π (a⁻¹ * x)
      set d := π (b⁻¹ * y)
      calc π a * c * (π b * d) * (π a * c)⁻¹ * (π b * d)⁻¹
          = π a * (c * (π b * d) * c⁻¹) * (π a)⁻¹ * d⁻¹ * (π b)⁻¹ := by group
        _ = π a * (π b * d) * (π a)⁻¹ * d⁻¹ * (π b)⁻¹ := by
            rw [hca (π b * d), mul_inv_cancel_right]
        _ = π a * π b * (d * (π a)⁻¹ * d⁻¹) * (π b)⁻¹ := by group
        _ = π a * π b * (π a)⁻¹ * (π b)⁻¹ := by rw [hcb (π a)⁻¹, mul_inv_cancel_right]
    rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) x = π x from rfl,
      show (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) y = π y from rfl, hc]
    have ha' : π a ∈ Abar := ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hb' : π b ∈ Abar := ⟨b, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    rw [commutatorElement_def]
    exact Abar.mul_mem (Abar.mul_mem (Abar.mul_mem ha' hb') (Abar.inv_mem ha')) (Abar.inv_mem hb')
  intro x hx
  obtain ⟨a, ha, hax⟩ := htop (Subgroup.mem_top (π ⟨x, hx⟩))
  have hk : a⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥X := by
    rw [← QuotientGroup.eq]
    exact hax
  have hx' : x = (a : Ω) * ((a⁻¹ * ⟨x, hx⟩ : ↥X) : Ω) := by simp
  rw [hx']
  refine mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha)) (Subgroup.mem_sup_right ?_)
  exact ⟨_, hk, rfl⟩

end L436

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_of_conjAct_eq_one {U : Subgroup G} (g : Subgroup.normalizer (U : Set G))
    (hg : conjAct U g = 1) : (g : G) ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : G)) hg
  simp only [InternalSec.coe_conjAct_apply, MulAut.one_apply] at h
  calc u * g = (g * u * (g : G)⁻¹) * g := by rw [h]
    _ = g * u := by group

namespace Setting436Sp4

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (s : Setting436Sp4 G T M L n I H K t)
include s

theorem conjClosure_C_eq :
    conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
        (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) =
      conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L) ⊓ Subgroup.centralizer (T : Set G))
        (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) := by
  set GZ := Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) with hGZ
  refine le_antisymm ?_ (conjClosure_mono inf_le_left le_rfl)
  obtain ⟨Y₁, Y₂, hY₁N, -, -, -, -, -, -, hY₂K, -, -, -, -, htrans⟩ := s.concl.torus
  have hYGZ : Y₁ ⊔ Y₂ ≤ GZ := _root_.sup_le (hY₁N.trans inf_le_right)
    (hY₂K.trans (s.concl.K₂_le.trans (Subgroup.centralizer_le_normalizer _)))
  obtain ⟨c₀, hc₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp s.C_inf_centralizer_T_ne_bot
  refine conjClosure_le fun g hg c hc => ?_
  by_cases hc1 : c = 1
  · rw [hc1, mul_one, mul_inv_cancel]
    exact one_mem _
  obtain ⟨y, hy, hyc⟩ := htrans (c₀ : G) c₀.2.1 c hc (fun h => hc₀1 (Subtype.ext h)) hc1
  rw [← hyc]
  have h1 := mem_conjClosure (mul_mem hg (hYGZ hy)) c₀.2
  have e : g * (y * (c₀ : G) * y⁻¹) * g⁻¹ = (g * y) * (c₀ : G) * (g * y)⁻¹ := by group
  rw [e]
  exact h1

theorem isTwoReducedIn_U :
    IsTwoReducedIn (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))
      (conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
        (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))) := by
  rw [s.conjClosure_C_eq]
  refine isTwoReducedIn_conjClosure _ (s.sk.base.hyp.sylow.1.toSylow s.sk.base.hyp.sylow.2)
    s.T_le_normalizer_Z s.charTwo_GZ ?_
  intro c hc
  exact Subgroup.subset_closure ⟨⟨s.V_le_T hc.1.1, hc.2⟩, s.concl.V_sq c hc.1.1⟩

theorem pCoreOf_GZ_le_centralizer_U :
    pCoreOf 2 (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) ≤
      Subgroup.centralizer (conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
        (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' := A4.omegaOneCenterOf_le_centerOf _ (s.star.2 hu)
  exact (Subgroup.mem_centralizer_iff.mp hu'.2 x hx).symm

theorem Q₁_le_centralizer_U :
    sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤
      Subgroup.centralizer (conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
        (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) : Set G) :=
  (s.star.1.trans (s.star.2.trans (A4.omegaOneCenterOf_le _))).trans
    s.pCoreOf_GZ_le_centralizer_U

theorem V_inf_centralizer_U :
    v432 T M L ⊓ Subgroup.centralizer (conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
        (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) : Set G) =
      v432 T M L ⊓ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) := by
  apply le_antisymm
  · intro v hv
    have hv' : v ∈ v432 T M L ⊓
        Subgroup.centralizer (sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) :=
      ⟨hv.1, Subgroup.centralizer_le s.star.1 hv.2⟩
    rw [s.concl.V_cent_Q₁] at hv'
    exact hv'
  · exact fun v hv => ⟨hv.1, s.Q₁_le_centralizer_U hv.2⟩

theorem not_V_le_centralizer_U :
    ¬ v432 T M L ≤ Subgroup.centralizer (conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
        (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) : Set G) := by
  intro h
  have hle : v432 T M L ≤ v432 T M L ⊓ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) := by
    rw [← s.V_inf_centralizer_U]
    exact le_inf le_rfl h
  have h1 := Subgroup.relIndex_eq_one.mpr hle
  have h4 := s.four_le_two_pow
  rw [s.concl.index_V] at h1
  omega

theorem V_le_normalizer_U :
    v432 T M L ≤ Subgroup.normalizer (conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
      (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) : Set G) :=
  s.concl.V_le_K₂.trans ((s.concl.K₂_le.trans (Subgroup.centralizer_le_normalizer _)).trans
    (le_normalizer_conjClosure _ _))

theorem card_autOn_V :
    Nat.card ↥(autOn (v432 T M L) (conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
      (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)))) = 2 ^ n := by
  set U := conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
    (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) with hU
  set V := v432 T M L with hV
  have hVU := s.V_le_normalizer_U
  set f := InternalSec.autOnHom hVU with hf
  have hker : f.ker = (Subgroup.centralizer (U : Set G)).subgroupOf V := by
    ext v
    rw [InternalSec.mem_ker_autOnHom, Subgroup.mem_subgroupOf]
  have e := QuotientGroup.quotientKerEquivOfSurjective f (InternalSec.autOnHom_surjective hVU)
  rw [← Nat.card_congr e.toEquiv]
  show f.ker.index = 2 ^ n
  rw [hker, ← Subgroup.relIndex, ← Subgroup.inf_relIndex_right, inf_comm, s.V_inf_centralizer_U,
    s.concl.index_V]

theorem card_U_le :
    Nat.card ↥(conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
        (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))) ≤
      2 ^ n * Nat.card ↥(conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
        (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) ⊓
          Subgroup.centralizer (v432 T M L : Set G)) := by
  classical
  set U := conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
    (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) with hU
  set V := v432 T M L with hV
  set Q₁ := sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hQ₁
  have hQ₁U : Q₁ ≤ U := s.star.1
  set N₁ : Subgroup ↥Q₁ := (Subgroup.centralizer (V : Set G)).subgroupOf Q₁ with hN₁
  let f : ↥(U ⊓ Subgroup.centralizer (V : Set G)) × (↥Q₁ ⧸ N₁) → ↥U := fun x =>
    ⟨(x.1 : G) * ((x.2.out : ↥Q₁) : G)⁻¹, mul_mem x.1.2.1 (inv_mem (hQ₁U x.2.out.2))⟩
  have hsurj : Function.Surjective f := by
    intro u
    have huQ : (u : G) ∈ pCoreOf 2 (Subgroup.normalizer
        (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) :=
      (s.star.2.trans (A4.omegaOneCenterOf_le _)) u.2
    obtain ⟨q, hq, hqV⟩ := s.starstar huQ
    set x : ↥Q₁ ⧸ N₁ := QuotientGroup.mk ⟨q, hq⟩ with hx
    have hout : (x.out)⁻¹ * ⟨q, hq⟩ ∈ N₁ := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have hn : ((x.out : G))⁻¹ * q ∈ Subgroup.centralizer (V : Set G) := by
      have := Subgroup.mem_subgroupOf.mp hout
      simpa using this
    have huq : (u : G) * q ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h := hqV v hv
      calc v * ((u : G) * q) = ((u : G) * q) * v * ((u : G) * q)⁻¹ * ((u : G) * q) := by
            rw [h]
        _ = (u : G) * q * v := by group
    have hd : (u : G) * (x.out : G) ∈ U ⊓ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem u.2 (hQ₁U x.out.2), ?_⟩
      have e : (u : G) * (x.out : G) = ((u : G) * q) * (((x.out : G))⁻¹ * q)⁻¹ := by group
      rw [e]
      exact mul_mem huq (inv_mem hn)
    refine ⟨(⟨_, hd⟩, x), Subtype.ext ?_⟩
    show (u : G) * (x.out : G) * ((x.out : G))⁻¹ = u
    group
  have h1 := Nat.card_le_card_of_surjective f hsurj
  rw [Nat.card_prod] at h1
  have h2 : Nat.card (↥Q₁ ⧸ N₁) = 2 ^ n := by
    show N₁.index = 2 ^ n
    rw [hN₁, ← Subgroup.relIndex, ← Subgroup.inf_relIndex_right, inf_comm, s.concl.Q₁_cent_V,
      s.concl.index_Q₁]
  rw [h2] at h1
  linarith

theorem K₂_inf_centralizer_U_le :
    sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ⊓
        Subgroup.centralizer (conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
          (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) : Set G) ≤
      sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) := by
  classical
  set U := conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
    (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) with hU
  set K₂ := sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hK₂
  set Q₁ := sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hQ₁
  have := s.isSimpleGroup_modO2_K₂
  have hK₂U : K₂ ≤ Subgroup.normalizer (U : Set G) :=
    (s.concl.K₂_le.trans (Subgroup.centralizer_le_normalizer _)).trans
      (le_normalizer_conjClosure _ _)
  set N := (Subgroup.centralizer (U : Set G)).subgroupOf K₂ with hN
  have hNn : N.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (InternalSec.le_normalizer_centralizer hK₂U)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K₂) with hπ
  have hMn : (N.map π).Normal := Subgroup.Normal.map hNn π (QuotientGroup.mk'_surjective _)
  have hQ₁C : Q₁ ≤ Subgroup.centralizer (U : Set G) := s.Q₁_le_centralizer_U
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥K₂) ∈ N := Subgroup.mem_subgroupOf.mpr hx.2
    have h1 : π ⟨x, hx.1⟩ = 1 := by
      have : π ⟨x, hx.1⟩ ∈ N.map π := Subgroup.mem_map_of_mem π hxN
      rw [h] at this
      exact this
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨_, h2, rfl⟩
  · exfalso
    apply s.not_V_le_centralizer_U
    intro v hv
    have hvK : v ∈ K₂ := s.concl.V_le_K₂ hv
    have hmem : π ⟨v, hvK⟩ ∈ N.map π := h ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hcv⟩ := hmem
    have hk : c⁻¹ * ⟨v, hvK⟩ ∈ CFSG.pCore 2 ↥K₂ := by
      rw [← QuotientGroup.eq]
      exact hcv
    have hkQ : ((c⁻¹ * ⟨v, hvK⟩ : ↥K₂) : G) ∈ Q₁ := by
      exact ⟨_, hk, rfl⟩
    have e : v = (c : G) * ((c⁻¹ * ⟨v, hvK⟩ : ↥K₂) : G) := by simp
    rw [e]
    exact mul_mem (Subgroup.mem_subgroupOf.mp hc) (hQ₁C hkQ)

end Setting436Sp4

end CFSG.Quasithin.H13.Ch4
