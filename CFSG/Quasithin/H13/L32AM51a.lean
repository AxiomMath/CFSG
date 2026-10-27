module

public import CFSG.Quasithin.H13.L32AM50l
public import CFSG.Quasithin.H13.L32AC51h
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyPrimeSquare
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeWrap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.G64SymCase
public import CFSG.Quasithin.Background.S1567Z4
public import CFSG.Quasithin.Background.SmithB42Alt7Model
public import CFSG.Quasithin.Background.SmithB45M22HatMain
public import CFSG.Quasithin.EmptyFaithful.Insp11Irr
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
public import CFSG.Quasithin.EmptyFaithful.S153E58A
public import CFSG.Quasithin.EmptyFaithful.S153E58B
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.L32AC36i
public import CFSG.Quasithin.H13.L32AC36m
public import CFSG.Quasithin.H13.L32AC50g
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open Equiv Equiv.Perm
open scoped IsMulCommutative commutatorElement

theorem Alt8.card_alt8 : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem Alt8.card_perm8 : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem Alt8.isSimpleGroup : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

theorem Alt8.eq_bot_or_le {X : Subgroup (Perm (Fin 8))}
    (hX : ∀ a ∈ alternatingGroup (Fin 8), ∀ x ∈ X, a * x * a⁻¹ ∈ X) :
    X = ⊥ ∨ alternatingGroup (Fin 8) ≤ X := by
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := Alt8.isSimpleGroup
  have hA : (alternatingGroup (Fin 8)).Normal := inferInstance
  have hn : ((X ⊓ alternatingGroup (Fin 8)).subgroupOf (alternatingGroup (Fin 8))).Normal := by
    refine ⟨fun y hy a => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact ⟨hX a a.2 y hy.1, (a * y * a⁻¹).2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((X ⊓ alternatingGroup (Fin 8)).subgroupOf (alternatingGroup (Fin 8))) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxa : ∀ a ∈ alternatingGroup (Fin 8), x * a * x⁻¹ * a⁻¹ = 1 := by
      intro a ha
      have hc1 : x * a * x⁻¹ * a⁻¹ ∈ X := by
        have := X.mul_mem hx (hX a ha x⁻¹ (X.inv_mem hx))
        simpa [mul_assoc] using this
      have hc2 : x * a * x⁻¹ * a⁻¹ ∈ alternatingGroup (Fin 8) :=
        (alternatingGroup (Fin 8)).mul_mem (hA.conj_mem a ha x)
          ((alternatingGroup (Fin 8)).inv_mem ha)
      have hm : (⟨_, hc2⟩ : ↥(alternatingGroup (Fin 8))) ∈
          (X ⊓ alternatingGroup (Fin 8)).subgroupOf (alternatingGroup (Fin 8)) :=
        Subgroup.mem_subgroupOf.mpr ⟨hc1, hc2⟩
      rw [h, Subgroup.mem_bot] at hm
      exact congrArg Subtype.val hm
    apply Lin.conjNormal_injective8
    rw [map_one]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    have := hxa a a.2
    rw [mul_inv_eq_one] at this
    exact this
  · right
    intro a ha
    have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin 8))) ∈
        (X ⊓ alternatingGroup (Fin 8)).subgroupOf (alternatingGroup (Fin 8)) := by
      rw [h]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1

theorem isQuasisimple_of_alt8 {X : Type*} [Group X] (ε : X ≃* alternatingGroup (Fin 8)) :
    CFSG.Open.IsQuasisimple X := by
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := Alt8.isSimpleGroup
  have : IsSimpleGroup X := ε.isSimpleGroup
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    refine ⟨ε.symm ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.mpr (by decide)⟩,
      ε.symm ⟨swap 1 2 * swap 2 3, mem_alternatingGroup.mpr (by decide)⟩, fun h => ?_⟩
    have h1 := congrArg (fun x => ((ε x : alternatingGroup (Fin 8)) : Perm (Fin 8))) h
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
    revert h1
    decide
  have hc : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : b ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.mp this a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h1 : ⁅a, b⁆ ∈ commutator X := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab h1
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

structure Top51 (T L V H W K : Subgroup G) (π : ↥H →* Perm (Fin 8)) : Prop
    extends TopW T L V H W where
  hK : K ∈ cComp H
  hKn : H ≤ Subgroup.normalizer (K : Set G)
  hUK : conjClosure V H = ⁅conjClosure V H, K⁆
  hP : IsPSL 4 2 1 (L32A.cStar K)
  hker : π.ker = CFSG.Open.pCore 2 ↥H
  hsurj : Function.Surjective π

namespace Top51

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 8)} (C : Top51 T L V H W K π)
include C

theorem hKH : K ≤ H := le_of_mem_cComp C.hK

theorem pi_eq_one_iff (h : ↥H) : π h = 1 ↔ (h : G) ∈ pCoreOf 2 H := by
  rw [← MonoidHom.mem_ker, C.hker, ← pCoreOf_subgroupOf',
    Subgroup.mem_subgroupOf]

theorem card_cStar : Nat.card (L32A.cStar K) = 20160 := by
  obtain ⟨ε⟩ := Lin.nonempty_mulEquiv_sl_of_isPSL C.hP
  rw [Nat.card_congr (ε.trans Lin.slFourEquivAlt8).toEquiv, Alt8.card_alt8]

theorem range_piK : (π.comp (Subgroup.inclusion C.hKH)).range = alternatingGroup (Fin 8) := by
  classical
  set φ := π.comp (Subgroup.inclusion C.hKH) with hφ
  have hker : φ.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, C.pi_eq_one_iff, ← pCoreOf_subgroupOf' K,
      Subgroup.mem_subgroupOf]
    exact mem_pCoreOf_iff_of_mem_cComp C.hK k.2
  have hcard : Nat.card φ.range = 20160 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
      ← Nat.card_congr (cStarEquiv K).toEquiv, C.card_cStar]
  have hnorm : ∀ a ∈ alternatingGroup (Fin 8), ∀ x ∈ φ.range, a * x * a⁻¹ ∈ φ.range := by
    rintro a - _ ⟨k, rfl⟩
    obtain ⟨h, rfl⟩ := C.hsurj a
    have hk' : (h : G) * k * (h : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (C.hKn h.2) k).mp k.2
    refine ⟨⟨_, hk'⟩, ?_⟩
    show π (Subgroup.inclusion C.hKH ⟨_, hk'⟩) = π h * π (Subgroup.inclusion C.hKH k) * (π h)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext rfl)
  rcases Alt8.eq_bot_or_le hnorm with h | h
  · rw [h, Subgroup.card_bot] at hcard
    omega
  · exact (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, Alt8.card_alt8])).symm

theorem pi_mem_alt {k : G} (hk : k ∈ K) : π ⟨k, C.hKH hk⟩ ∈ alternatingGroup (Fin 8) := by
  rw [← C.range_piK]
  exact ⟨⟨k, hk⟩, rfl⟩

theorem exists_pi_eq {γ : Perm (Fin 8)} (hγ : γ ∈ alternatingGroup (Fin 8)) :
    ∃ k : G, ∃ hk : k ∈ K, π ⟨k, C.hKH hk⟩ = γ := by
  rw [← C.range_piK] at hγ
  obtain ⟨k, rfl⟩ := hγ
  exact ⟨k, k.2, rfl⟩

variable [IsMulCommutative ↥(conjClosure V H)]

theorem exists_act_ne_one : ∃ k : G, ∃ hk : k ∈ K, C.act ⟨k, C.hKH hk⟩ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply C.hWU.not_ge
  rw [C.hUK, Subgroup.commutator_le]
  intro u hu k hk
  have h1 := (C.act_eq_one_iff_comm ⟨k, C.hKH hk⟩).mp (hcon k hk) u⁻¹ (inv_mem hu)
  have hkU : k * u⁻¹ * k⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H (C.hKH hk)) _).mp (inv_mem hu)
  have hc : u * (k * u⁻¹ * k⁻¹) = (k * u⁻¹ * k⁻¹) * u :=
    congrArg Subtype.val (mul_comm (⟨u, hu⟩ : ↥(conjClosure V H)) ⟨_, hkU⟩)
  rw [commutatorElement_def,
    show u * k * u⁻¹ * k⁻¹ = k * u⁻¹ * k⁻¹ * (u⁻¹)⁻¹ by rw [inv_inv, ← hc]; group]
  exact h1

theorem act_eq_one_iff (h : ↥H) : C.act h = 1 ↔ π h = 1 := by
  refine ⟨fun hh => ?_, fun hh => C.act_eq_one_of_mem ((C.pi_eq_one_iff h).mp hh)⟩
  have hnorm : ∀ a ∈ alternatingGroup (Fin 8), ∀ x ∈ C.act.ker.map π,
      a * x * a⁻¹ ∈ C.act.ker.map π := by
    rintro a - _ ⟨n, hn, rfl⟩
    obtain ⟨g, rfl⟩ := C.hsurj a
    exact ⟨g * n * g⁻¹, (C.act.normal_ker).conj_mem n hn g, by rw [map_mul, map_mul, map_inv]⟩
  rcases Alt8.eq_bot_or_le hnorm with h0 | h0
  · have : π h ∈ C.act.ker.map π := ⟨h, hh, rfl⟩
    rwa [h0, Subgroup.mem_bot] at this
  · exfalso
    obtain ⟨k, hkK, hk⟩ := C.exists_act_ne_one
    obtain ⟨n, hn, hnk⟩ := h0 (C.pi_mem_alt hkK)
    apply hk
    have h1 : π (n⁻¹ * ⟨k, C.hKH hkK⟩) = 1 := by rw [map_mul, map_inv, hnk, inv_mul_cancel]
    have h2 := C.act_eq_one_of_mem ((C.pi_eq_one_iff _).mp h1)
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul] at h2
    exact h2

theorem ker_act : C.act.ker = π.ker := by
  ext h
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact C.act_eq_one_iff h

@[expose] noncomputable def emb : ↥C.act.range →* Perm (Fin 8) :=
  (QuotientGroup.kerLift π).comp (((QuotientGroup.quotientMulEquivOfEq C.ker_act).toMonoidHom).comp
    (QuotientGroup.quotientKerEquivRange C.act).symm.toMonoidHom)

theorem emb_act (h : ↥H) : C.emb ⟨C.act h, h, rfl⟩ = π h := by
  have : (QuotientGroup.quotientKerEquivRange C.act).symm ⟨C.act h, h, rfl⟩ =
      (h : ↥H ⧸ C.act.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show QuotientGroup.kerLift π (QuotientGroup.quotientMulEquivOfEq C.ker_act
    ((QuotientGroup.quotientKerEquivRange C.act).symm ⟨C.act h, h, rfl⟩)) = π h
  rw [this]
  rfl

theorem emb_injective : Function.Injective C.emb := by
  rintro ⟨_, h, rfl⟩ ⟨_, h', rfl⟩ hh
  rw [C.emb_act, C.emb_act] at hh
  have h1 : π (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, hh, inv_mul_cancel]
  rw [← C.act_eq_one_iff, map_mul, map_inv, inv_mul_eq_one] at h1
  exact Subtype.ext h1

theorem emb_surjective : Function.Surjective C.emb := by
  intro γ
  obtain ⟨h, rfl⟩ := C.hsurj γ
  exact ⟨⟨C.act h, h, rfl⟩, C.emb_act h⟩

@[expose] noncomputable def embEquiv : ↥C.act.range ≃* Perm (Fin 8) :=
  MulEquiv.ofBijective C.emb ⟨C.emb_injective, C.emb_surjective⟩

@[expose] noncomputable def autK : Subgroup (MulAut (Hat V H W)) := (K.subgroupOf H).map C.act

theorem autK_le : C.autK ≤ C.act.range := Subgroup.map_le_range _ _

theorem autK_normal : ∀ y ∈ C.act.range, ∀ l ∈ C.autK, y * l * y⁻¹ ∈ C.autK := by
  rintro _ ⟨h, rfl⟩ _ ⟨k, hk, rfl⟩
  refine ⟨h * k * h⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp (C.hKn h.2) k).mp (Subgroup.mem_subgroupOf.mp hk)

theorem act_mem_autK_iff (h : ↥H) : C.act h ∈ C.autK ↔ π h ∈ alternatingGroup (Fin 8) := by
  constructor
  · rintro ⟨k, hk, hkh⟩
    have h1 : C.act (k⁻¹ * h) = 1 := by rw [map_mul, map_inv, hkh, inv_mul_cancel]
    rw [C.act_eq_one_iff, map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1]
    exact C.pi_mem_alt (Subgroup.mem_subgroupOf.mp hk)
  · intro hh
    obtain ⟨k, hk, hkh⟩ := C.exists_pi_eq hh
    refine ⟨⟨k, C.hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
    have h1 : π (⟨k, C.hKH hk⟩⁻¹ * h) = 1 := by rw [map_mul, map_inv, hkh, inv_mul_cancel]
    rw [← C.act_eq_one_iff, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1

theorem sq_mem : ∀ y ∈ C.act.range, y ^ 2 ∈ C.autK := by
  rintro _ ⟨h, rfl⟩
  rw [← map_pow, C.act_mem_autK_iff, map_pow, mem_alternatingGroup, map_pow, Int.units_sq]

theorem emb_mem_alt (l : ↥C.autK) :
    C.emb (Subgroup.inclusion C.autK_le l) ∈ alternatingGroup (Fin 8) := by
  obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp l.2
  have : Subgroup.inclusion C.autK_le l = ⟨C.act k, k, rfl⟩ := Subtype.ext hkl.symm
  rw [this, C.emb_act]
  exact C.pi_mem_alt (Subgroup.mem_subgroupOf.mp hk)

@[expose] noncomputable def iotaHom : ↥C.autK →* alternatingGroup (Fin 8) :=
  (C.emb.comp (Subgroup.inclusion C.autK_le)).codRestrict _ C.emb_mem_alt

theorem iotaHom_bijective : Function.Bijective C.iotaHom := by
  refine ⟨fun a b hab => ?_, fun γ => ?_⟩
  · have h1 : C.emb (Subgroup.inclusion C.autK_le a) = C.emb (Subgroup.inclusion C.autK_le b) :=
      congrArg Subtype.val hab
    exact Subgroup.inclusion_injective C.autK_le (C.emb_injective h1)
  · obtain ⟨k, hk, hkγ⟩ := C.exists_pi_eq γ.2
    refine ⟨⟨C.act ⟨k, C.hKH hk⟩, ⟨k, C.hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, ?_⟩
    apply Subtype.ext
    show C.emb ⟨C.act ⟨k, C.hKH hk⟩, _, rfl⟩ = γ
    rw [C.emb_act, hkγ]

@[expose] noncomputable def iota : ↥C.autK ≃* alternatingGroup (Fin 8) :=
  MulEquiv.ofBijective C.iotaHom C.iotaHom_bijective

theorem emb_eq_iota (l : ↥C.autK) :
    C.emb ⟨(l : MulAut (Hat V H W)), C.autK_le l.2⟩ = (C.iota l : Perm (Fin 8)) := rfl

theorem pCoreOf_range : pCoreOf 2 C.act.range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 C.act.range with hR
  have hRG : R ≤ C.act.range := pCoreOf_le 2 _
  set X := (R.subgroupOf C.act.range).map C.emb with hX
  have hnorm : ∀ a ∈ alternatingGroup (Fin 8), ∀ x ∈ X, a * x * a⁻¹ ∈ X := by
    rintro a ha _ ⟨r, hr, rfl⟩
    obtain ⟨k, hk, rfl⟩ := C.exists_pi_eq ha
    set g : ↥C.act.range := ⟨C.act ⟨k, C.hKH hk⟩, _, rfl⟩ with hg
    have hgr : (g : MulAut (Hat V H W)) * r * (g : MulAut (Hat V H W))⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ g.2) r).mp
        (Subgroup.mem_subgroupOf.mp hr)
    refine ⟨g * r * g⁻¹, Subgroup.mem_subgroupOf.mpr hgr, ?_⟩
    rw [map_mul, map_mul, map_inv, hg, C.emb_act]
  rcases Alt8.eq_bot_or_le hnorm with h | h
  · rw [eq_bot_iff]
    intro r hr
    have h1 : C.emb ⟨r, hRG hr⟩ ∈ X := ⟨⟨r, hRG hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one C.emb] at h1
    exact congrArg Subtype.val (C.emb_injective h1)
  · exfalso
    have hc : swap (0 : Fin 8) 1 * swap 0 2 ∈ alternatingGroup (Fin 8) :=
      mem_alternatingGroup.mpr (by decide)
    obtain ⟨r, hr, hrc⟩ := h hc
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 C.act.range) ⟨_, Subgroup.mem_subgroupOf.mp hr⟩
    have h1 : (swap (0 : Fin 8) 1 * swap 0 2) ^ 2 ^ n = 1 := by
      rw [← hrc, ← map_pow]
      have h0 : (r : MulAut (Hat V H W)) ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      have : r ^ 2 ^ n = 1 := Subtype.ext (by simpa using h0)
      rw [this, map_one]
    have h3 : orderOf (swap (0 : Fin 8) 1 * swap 0 2) = 3 :=
      orderOf_eq_prime (by decide) (by decide)
    have h4 := orderOf_dvd_of_pow_eq_one h1
    rw [h3] at h4
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
    omega

theorem genFitting_eq : quasithinGenFitting C.act.range = C.autK :=
  B1Red.quasithinGenFitting_eq_of_two_quot C.autK_le C.autK_normal
    (isQuasisimple_of_alt8 C.iota) C.sq_mem C.pCoreOf_range

end Top51

end CFSG.Quasithin.H13.L32A.C
