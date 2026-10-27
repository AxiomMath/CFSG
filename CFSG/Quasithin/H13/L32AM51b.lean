module

public import CFSG.Quasithin.H13.L32AM51a
public import CFSG.Quasithin.Background.SmithB45LnL4Main
public import CFSG.Quasithin.Background.SmithB42LnL42
public import CFSG.Quasithin.Background.B69Red

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open Equiv Equiv.Perm
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top51

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 8)} (C : Top51 T L V H W K π)
  [IsMulCommutative ↥(conjClosure V H)]
include C

@[expose] def IrrK : Prop :=
  ∀ J : Subgroup (Hat V H W), (∀ l ∈ C.autK, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤

@[expose] noncomputable def autE (B : Subgroup G) : Subgroup (MulAut (Hat V H W)) :=
  (B.subgroupOf H).map C.act

theorem mem_pCoreOf_iff_comm {f : G} (hf : f ∈ H) :
    f ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure V H, f * u * f⁻¹ * u⁻¹ ∈ W := by
  rw [← C.act_eq_one_iff_comm ⟨f, hf⟩, C.act_eq_one_iff, C.pi_eq_one_iff]

theorem card_autE {B : Subgroup G} (hBH : B ≤ H) :
    Nat.card (C.autE B) = (B ⊓ pCoreOf 2 H).relIndex B := by
  have hE : C.autE B = autSec (autOn B (conjClosure V H)) ⊤
      (W.subgroupOf (conjClosure V H)) := by
    ext ψ
    rw [A6.A6Mod.mem_autSec_iff (le_normalizer_conjClosure V H) C.hHUW hBH]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, Subgroup.mem_subgroupOf.mp hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  rw [hE]
  exact A6.A6Mod.card_autSec_eq (le_normalizer_conjClosure V H) C.hHUW hBH
    fun f hf => C.mem_pCoreOf_iff_comm (hBH hf)

theorem isA2_autE {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) :
    IsA2 C.act.range (C.autE B) := by
  obtain ⟨hBH, hBe, hBQ, -, -⟩ := hB
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp hBQ
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨C.act ⟨b, hBH hb⟩, ⟨b, hBH hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩, ?_⟩
    intro h1
    apply hbQ
    have h2 : C.act ⟨b, hBH hb⟩ = 1 := congrArg Subtype.val h1
    rw [C.act_eq_one_iff, C.pi_eq_one_iff] at h2
    exact h2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have := hBe.1
    have h1 : (x : G) * y = y * x := congrArg Subtype.val
      (mul_comm (⟨x, Subgroup.mem_subgroupOf.mp hx⟩ : ↥B) ⟨y, Subgroup.mem_subgroupOf.mp hy⟩)
    exact Subtype.ext h1
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h2 : x ^ 2 = 1 := Subtype.ext (hBe.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [h2, map_one]

theorem index_fixV_autE_le {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) :
    (fixV (C.autE B)).index ≤ Nat.card (C.autE B) ^ 2 := by
  obtain ⟨hBH, -, -, -, hidx⟩ := hB
  set U := conjClosure V H with hU
  set q := InternalSec.secMk (W.subgroupOf U) with hq
  set Z := (centralizerMod (fsuV1 T V) U B).subgroupOf U with hZ
  have hZf : Z.map q ≤ fixV (C.autE B) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨f, hf, rfl⟩
    have hz' : (z : G) ∈ centralizerMod (fsuV1 T V) U B := hz
    have hf' : (f : G) ∈ B := hf
    have hc := (mem_centralizerMod.mp hz').2.2 (f : G) hf'
    rw [C.act_secMk]
    have h1 : (f : G) * z * (f : G)⁻¹ * (z : G)⁻¹ ∈ W := by
      apply C.hV₁W
      have := inv_mem hc
      rwa [show ((z : G) * f * (z : G)⁻¹ * (f : G)⁻¹)⁻¹ = (f : G) * z * (f : G)⁻¹ * (z : G)⁻¹ by
        group] at this
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    exact h1
  have hpos : ∀ X : Subgroup (Hat V H W), 0 < X.index := fun X =>
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hposU : 0 < Z.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 : (fixV (C.autE B)).index ≤ (Z.map q).index :=
    Nat.le_of_dvd (hpos _) (Subgroup.index_dvd_of_le hZf)
  have h2 : (Z.map q).index ≤ Z.index :=
    Nat.le_of_dvd hposU (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))
  calc (fixV (C.autE B)).index ≤ Z.index := h1.trans h2
    _ = (centralizerMod (fsuV1 T V) U B).relIndex U := rfl
    _ ≤ ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := hidx
    _ = Nat.card (C.autE B) ^ 2 := by rw [C.card_autE hBH]

theorem sq_eq_one (v : Hat V H W) : v ^ 2 = 1 := by
  rw [pow_two]
  exact C.sec_sq v

theorem isQuasisimple_autK : CFSG.IsQuasisimple ↥C.autK :=
  B1Red.isQuasisimple_of_open (isQuasisimple_of_alt8 C.iota)

theorem center_autK : Subgroup.center ↥C.autK = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := Alt8.isSimpleGroup
  have : IsSimpleGroup ↥C.autK := C.iota.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥C.autK) with h | h
  · exact h
  · exfalso
    have hc1 : swap (0 : Fin 8) 1 * swap 1 2 ∈ alternatingGroup (Fin 8) :=
      mem_alternatingGroup.mpr (by decide)
    have hc2 : swap (1 : Fin 8) 2 * swap 2 3 ∈ alternatingGroup (Fin 8) :=
      mem_alternatingGroup.mpr (by decide)
    have hz : C.iota.symm ⟨_, hc1⟩ ∈ Subgroup.center ↥C.autK := by rw [h]; trivial
    have h1 := congrArg (fun x => ((C.iota x : alternatingGroup (Fin 8)) : Perm (Fin 8)))
      (Subgroup.mem_center_iff.mp hz (C.iota.symm ⟨_, hc2⟩))
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
    revert h1
    decide

theorem sqtkGroup_range (hA21 : AsA21SQTKSection) : SQTKGroup ↥C.act.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := sqtkGroup_of_setting C.S
  set Λ : Subgroup ↥C.act.range := C.autK.subgroupOf C.act.range with hΛ
  have hΛn : Λ.Normal := ⟨fun l hl y => by
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact C.autK_normal y y.2 l hl⟩
  have hΛq : CFSG.IsQuasisimple ↥Λ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe C.autK_le).symm
      C.isQuasisimple_autK
  refine hA21 ↥H hH ⊤ ↥C.act.range (C.act.rangeRestrict.comp Subgroup.topEquiv.toMonoidHom)
    (fun y => by
      obtain ⟨x, hx⟩ := MonoidHom.rangeRestrict_surjective C.act y
      exact ⟨⟨x, trivial⟩, hx⟩) Λ
    (B5.layer_eq_top_of_quasisimple hΛq) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hΛ, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow]
  exact C.sq_mem _ y.2

theorem b4Hyp (hA21 : AsA21SQTKSection) (hirr : C.IrrK) : B4Hyp C.act.range C.autK := by
  refine ⟨C.sqtkGroup_range hA21, C.genFitting_eq.symm, C.isQuasisimple_autK, ?_⟩
  refine ⟨bot_lt_iff_ne_bot.mpr C.top_ne_bot, fun J hJ _ _ => hirr J fun l hl v hv => ?_⟩
  exact hJ ⟨l, hl⟩ v hv

theorem exists_act_not_mem : ∃ h : ↥H, C.act h ∉ C.autK := by
  obtain ⟨h, hh⟩ := C.hsurj (swap 0 1)
  refine ⟨h, fun hm => ?_⟩
  have := (C.act_mem_autK_iff h).mp hm
  rw [hh, mem_alternatingGroup, sign_swap (by decide)] at this
  exact absurd this (by decide)

theorem exists_wedge [Module (ZMod 2) (Additive (Hat V H W))] (hA21 : AsA21SQTKSection)
    (hirr : C.IrrK) {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B)
    (e : ↥C.autK ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) :
    ∃ β : Additive (Hat V H W) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2),
      ∀ g w, β (B42Ln.repOf4 (B42Ln.phiOf4 e) g w) = B42Ln.wedgeRep4' g (β w) := by
  classical
  have hb4 := C.b4Hyp hA21 hirr
  have hZ := C.center_autK
  have hA := C.isA2_autE hB
  have h2F := C.index_fixV_autE_le hB
  have : Finite (Additive (Hat V H W)) := inferInstanceAs (Finite (Hat V H W))
  have : Nontrivial (Hat V H W) := B42Ln.nontrivial_of_equiv4 e
  have hρ : SmithCurtis.IsSimpleRep (B42Ln.repOf4 (B42Ln.phiOf4 e)) :=
    B42Ln.isSimpleRep_repOf4 (B42Ln.phiOf4 e) (B42Ln.irr_of_isIrrSec hb4.2.2.2)
  have hmodel : B42Ln.L4Model (B42Ln.repOf4 (B42Ln.phiOf4 e)) := by
    rcases B45Ln.card_le_or_l4Model hb4 hZ e hA h2F with hV18 | hm
    · have hV18' : Nat.card (Hat V H W) ≤ 2 ^ 18 := hV18
      have hcard20 : ∀ β : Additive (Hat V H W) ≃ₗ[ZMod 2] (Fin 20 → ZMod 2), False := fun β => by
        have h1 : Nat.card (Hat V H W) = 2 ^ 20 := by
          rw [show Nat.card (Hat V H W) = Nat.card (Additive (Hat V H W)) from rfl,
            Nat.card_congr β.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
          rfl
        omega
      rcases B45Ln.type_cases hρ with hm | h24 | ⟨β, -⟩ | ⟨β, -⟩ | ⟨β, hβ⟩
      · exact hm
      · exfalso
        have h1 : 2 ^ 24 ≤ Nat.card (Hat V H W) := by
          rw [B42Ln.card_eq_two_pow_finrank]
          exact Nat.pow_le_pow_right (by norm_num) h24
        omega
      · exact (hcard20 β).elim
      · exact (hcard20 β).elim
      · exact (B45Ln.false_of_rep14 hb4 hZ e hβ hA h2F).elim
    · exact hm
  rcases hmodel with htriv | ⟨κ, β, hβ⟩ | ⟨β, hβ⟩
  · exact (B42Ln.not_trivial4 e htriv).elim
  · exfalso
    have htop := G64.BinaryNaturalSL.eq_top (B42Ln.binaryNaturalSL_of_nat4 e hβ)
    obtain ⟨h, hh⟩ := C.exists_act_not_mem
    exact hh (htop ▸ Subgroup.mem_top _)
  · exact ⟨β, hβ⟩

end Top51

end CFSG.Quasithin.H13.L32A.C
