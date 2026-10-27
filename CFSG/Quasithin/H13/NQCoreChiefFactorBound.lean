module

public import CFSG.Quasithin.SteinbergCFMinimalParabolicFixedSpaceRank
public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.Quasithin.Background.D15Chief
public import CFSG.Quasithin.H13.NQCoreRadicalCentralizerProof

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup Module CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ABGLocalTools (chiefRep chiefRep_apply_mk chiefRep_eq_one_iff chiefRep_irreducible
  IsChiefFactorUnder exists_ofMul_mk chiefConj_apply_coe)
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem eq_top_of_map_subtype_eq {H : Subgroup G} {b : Subgroup ↥H} (hb : b.map H.subtype = H) :
    b = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ : (x : G) ∈ b.map H.subtype := by
    rw [hb]
    exact x.2
  rwa [← H.subtype_injective hyx]

theorem isCoatom_subgroupOf_of_max {H M : Subgroup G} (hMH : M < H)
    (hMmax : ∀ Y : Subgroup G, M < Y → Y ≤ H → Y = H) : IsCoatom (M.subgroupOf H) := by
  refine ⟨fun h => hMH.not_ge fun x hx => ?_, fun b hb => ?_⟩
  · have h1 : (⟨x, hx⟩ : ↥H) ∈ M.subgroupOf H := h ▸ mem_top _
    exact h1
  · refine eq_top_of_map_subtype_eq (hMmax _ (lt_of_le_of_ne ?_ fun heq => hb.ne ?_)
      (map_subtype_le b))
    · intro x hx
      exact ⟨⟨x, hMH.le hx⟩, hb.le hx, rfl⟩
    · ext y
      constructor
      · intro hy
        exact hb.le hy
      · intro hy
        have h1 : (y : G) ∈ M := heq ▸ (⟨y, hy, rfl⟩ : (y : G) ∈ b.map H.subtype)
        exact h1

theorem eq_subgroupOf_of_isCoatom {H M T : Subgroup G} (hTH : T ≤ H)
    (hMu : ∀ Y : Subgroup G, Y < H → (∀ Z : Subgroup G, Y < Z → Z ≤ H → Z = H) → T ≤ Y →
      Y = M)
    {Y : Subgroup ↥H} (hY : IsCoatom Y) (hTY : T.subgroupOf H ≤ Y) : Y = M.subgroupOf H := by
  have hYlt : Y.map H.subtype < H :=
    lt_of_le_of_ne (map_subtype_le Y) fun h => hY.1 (eq_top_of_map_subtype_eq h)
  have hYmax : ∀ Z : Subgroup G, Y.map H.subtype < Z → Z ≤ H → Z = H := by
    intro Z hZ hZH
    have hYZ : Y < Z.subgroupOf H := by
      refine lt_of_le_of_ne (fun y hy => hZ.le ⟨y, hy, rfl⟩) fun heq => hZ.ne ?_
      rw [heq, subgroupOf_map_subtype, inf_eq_left.mpr hZH]
    have h1 := hY.2 _ hYZ
    refine le_antisymm hZH fun x hx => ?_
    have h2 : (⟨x, hx⟩ : ↥H) ∈ Z.subgroupOf H := h1 ▸ mem_top _
    exact h2
  have h1 := hMu _ hYlt hYmax fun t ht => ⟨⟨t, hTH ht⟩, hTY ht, rfl⟩
  rw [← h1]
  exact (comap_map_eq_self_of_injective H.subtype_injective Y).symm

variable [Finite G]

theorem noncentral_chief_factor_bound {H T M U L N : Subgroup G} (hHs : Group.IsSolvable ↥H)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hMH : M < H)
    (hMmax : ∀ Y : Subgroup G, M < Y → Y ≤ H → Y = H) (hTM : T ≤ M)
    (hMu : ∀ Y : Subgroup G, Y < H → (∀ Z : Subgroup G, Y < Z → Z ≤ H → Z = H) → T ≤ Y →
      Y = M)
    (hU : IsElemAbelian 2 U) (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) :
    (∀ t ∈ T, (∀ x ∈ N, t * x * t⁻¹ * x⁻¹ ∈ L) → t ∈ (CFSG.pCore 2 ↥H).map H.subtype) ∧
    ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      ((CFSG.pCore 2 ↥H).map H.subtype).relIndex A ≤ (centralizerMod L N A).relIndex N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hT.1
  have hNU : N ≤ U := hstep.1.1
  have hLN : L < N := hstep.2.2.1
  have hN₁ : H ≤ normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hN₂ : H ≤ normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => by
    have := hU.1
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥U) ⟨y, hy⟩)
  have hchief : IsChiefFactorUnder 2 H N L := by
    refine ⟨hLN, hN₁, hN₂, fun x hx y hy => ?_, fun x hx y hy => ?_, fun x hx => ?_,
      fun X hLX hXN hHX => ?_⟩
    · rw [hcomm x (hNU hx) y (hNU (hLN.le hy)), mul_inv_cancel_right]
      exact hy
    · rw [commutatorElement_def, hcomm x (hNU hx) y (hNU hy), mul_assoc, mul_assoc,
        mul_inv_cancel_left, mul_inv_cancel]
      exact one_mem L
    · rw [hU.2 x (hNU hx)]
      exact one_mem L
    · exact hstep.2.2.2 X ⟨hXN.trans hNU, fun g hg x hx =>
        (mem_normalizer_iff.mp (hHX hg) x).mp hx⟩ hLX hXN
  have := hchief.normal
  have := hchief.isElementaryAbelian
  set W := Additive (↥N ⧸ L.subgroupOf N) with hW
  have : Finite W := inferInstanceAs (Finite (↥N ⧸ L.subgroupOf N))
  have : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  set ρ0 := chiefRep (p := 2) hN₁ hN₂ with hρ0
  set ρ : Representation (ZMod 2) ↥H W := (Units.coeHom _).comp ρ0 with hρ
  have hρapply : ∀ (h : ↥H) (x : ↥N), ρ h (Additive.ofMul (x : ↥N ⧸ L.subgroupOf N)) =
      Additive.ofMul ((⟨(h : G) * x * (h : G)⁻¹,
        (mem_normalizer_iff.mp (hN₁ h.2) x).mp x.2⟩ : ↥N) : ↥N ⧸ L.subgroupOf N) := by
    intro h x
    change ((ρ0 h : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) _ = _
    rw [hρ0, chiefRep_apply_mk]
    congr 2
  have hirr : ρ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W' => ?_ }
    · obtain ⟨x, hxN, hxL⟩ := IsConcreteLE.exists_of_lt hLN
      have h1 : Additive.ofMul ((⟨x, hxN⟩ : ↥N) : ↥N ⧸ L.subgroupOf N) ∈
          (⊥ : Subrepresentation ρ).toSubmodule := by
        rw [h]
        exact Submodule.mem_top
      have h2 : ((⟨x, hxN⟩ : ↥N) : ↥N ⧸ L.subgroupOf N) = 1 := h1
      exact hxL (mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2))
    · rcases chiefRep_irreducible hchief W'.toSubmodule
        (fun n v hv => W'.apply_mem_toSubmodule n hv) with h | h
      · left
        exact Subrepresentation.ext (by rw [h]; rfl)
      · right
        exact Subrepresentation.ext (by rw [h]; rfl)
  have hρnt : ∃ g, ρ g ≠ 1 := by
    by_contra hall
    push Not at hall
    refine hnc fun g hg x hx => ?_
    have h1 : ρ0 ⟨g, hg⟩ = 1 := Units.ext (hall ⟨g, hg⟩)
    rw [hρ0, chiefRep_eq_one_iff] at h1
    have h2 := L.inv_mem (h1 x hx)
    rwa [commutatorElement_def, show (x * g * x⁻¹ * g⁻¹)⁻¹ = g * x * g⁻¹ * x⁻¹ by group] at h2
  have hT2H : IsPGroup 2 ↥(T.subgroupOf H) := hT.2.1.of_equiv (subgroupOfEquivOfLe hTH).symm
  set Ts : Sylow 2 ↥H := hT2H.toSylow hT.2.2 with hTs
  have hM' := isCoatom_subgroupOf_of_max hMH hMmax
  have hTsM' : (Ts : Subgroup ↥H) ≤ M.subgroupOf H := fun t ht => hTM ht
  have huniq : ∀ Y : Subgroup ↥H, IsCoatom Y → (Ts : Subgroup ↥H) ≤ Y → Y = M.subgroupOf H :=
    fun Y hY hTsY => eq_subgroupOf_of_isCoatom hTH hMu hY hTsY
  obtain ⟨hker, -, hbound⟩ :=
    SteinbergCF.solvable_minimal_parabolic_irreducible_factor_fixed_space_rank hHs Ts hTn hM'
      hTsM' huniq ρ hρnt
  refine ⟨fun t ht htriv => ?_, fun A hAT hAe => ?_⟩
  ·
    have h1 : (⟨t, hTH ht⟩ : ↥H) ∈ ρ.ker ⊓ (Ts : Subgroup ↥H) := by
      refine ⟨MonoidHom.mem_ker.mpr ?_, ht⟩
      have h2 : ρ0 ⟨t, hTH ht⟩ = 1 := by
        rw [hρ0, chiefRep_eq_one_iff]
        intro w hw
        have h3 := L.inv_mem (htriv w hw)
        rw [show (t * w * t⁻¹ * w⁻¹)⁻¹ = w * t * w⁻¹ * t⁻¹ by group] at h3
        rw [commutatorElement_def]
        exact h3
      change ((ρ0 ⟨t, hTH ht⟩ : LinearMap.GeneralLinearGroup (ZMod 2) W) :
        W →ₗ[ZMod 2] W) = 1
      rw [h2]
      rfl
    rw [hker] at h1
    exact ⟨_, h1, rfl⟩
  ·
    set C := centralizerMod L N A with hC
    have hAH : A ≤ H := hAT.trans hTH
    have hLC : L ≤ C := by
      intro l hl
      refine ⟨hLN.le hl, le_normalizer hl, fun a ha => ?_⟩
      have h1 : a * l⁻¹ * a⁻¹ ∈ L :=
        (mem_normalizer_iff.mp (hN₂ (hAH ha)) _).mp (L.inv_mem hl)
      rw [show l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) by group]
      exact L.mul_mem hl h1
    have hCN : C ≤ N := fun x hx => hx.1
    set A' : Subgroup ↥H := A.subgroupOf H with hA'
    have hA'e : IsElementaryAbelian 2 ↥A' := by
      have e : ↥A' ≃* ↥A := subgroupOfEquivOfLe hAH
      refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
      · have := hAe.1
        exact e.symm.surjective.isMulCommutative inferInstance
      · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (Subtype.ext ?_)
        simpa using hAe.2 _ a.2
    have h1 := hbound A' (fun a ha => hAT ha) hA'e
    have hinvC : ∀ x : ↥N, Additive.ofMul (x : ↥N ⧸ L.subgroupOf N) ∈
        Representation.invariants (ρ.comp A'.subtype) ↔ (x : G) ∈ C := by
      intro x
      have key : ∀ a (ha : a ∈ A), ρ ⟨a, hAH ha⟩ (Additive.ofMul (x : ↥N ⧸ L.subgroupOf N)) =
          Additive.ofMul (x : ↥N ⧸ L.subgroupOf N) ↔ (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ L := by
        intro a ha
        rw [hρapply, Additive.ofMul.injective.eq_iff, QuotientGroup.eq, mem_subgroupOf,
          Subgroup.coe_mul, Subgroup.coe_inv]
        have hy : a * (x : G) * a⁻¹ ∈ U :=
          hNU ((mem_normalizer_iff.mp (hN₁ (hAH ha)) x).mp x.2)
        change (a * (x : G) * a⁻¹)⁻¹ * x ∈ L ↔ _
        rw [hcomm _ (U.inv_mem hy) x (hNU x.2),
          show (x : G) * (a * (x : G) * a⁻¹)⁻¹ = (x : G) * a * (x : G)⁻¹ * a⁻¹ by group]
      rw [Representation.mem_invariants]
      constructor
      · intro h
        refine ⟨x.2, mem_normalizer_iff.mpr fun l => ⟨fun hl => ?_, fun hl => ?_⟩,
          fun a ha => (key a ha).mp (h ⟨⟨a, hAH ha⟩, ha⟩)⟩
        · rw [hcomm x (hNU x.2) l (hNU (hLN.le hl)), mul_inv_cancel_right]
          exact hl
        · have hlU : (x : G) * l * (x : G)⁻¹ ∈ U := hNU (hLN.le hl)
          have h2 := hcomm _ (U.inv_mem (hNU x.2)) _ hlU
          rw [show (x : G)⁻¹ * ((x : G) * l * (x : G)⁻¹) = l * (x : G)⁻¹ by group] at h2
          rw [show l = (l * (x : G)⁻¹) * (x : G) by group, h2,
            show (x : G) * l * (x : G)⁻¹ * (x : G)⁻¹ * (x : G) = (x : G) * l * (x : G)⁻¹ by
              group]
          exact hl
      · rintro ⟨-, -, h⟩ ⟨g, hg⟩
        exact (key (g : G) hg).mpr (h _ hg)
    have hcardW : Nat.card W = L.relIndex N := by
      rw [hW]
      exact (index_eq_card _).symm
    have hcardInv : Nat.card (Representation.invariants (ρ.comp A'.subtype)) = L.relIndex C := by
      have hmem : ∀ w : W, w ∈ Representation.invariants (ρ.comp A'.subtype) ↔
          Additive.toMul w ∈ (C.subgroupOf N).map (QuotientGroup.mk' (L.subgroupOf N)) := by
        intro w
        obtain ⟨x, rfl⟩ := exists_ofMul_mk w
        rw [hinvC]
        constructor
        · intro hx
          exact ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, hyx⟩
          have h2 : y⁻¹ * x ∈ L.subgroupOf N := QuotientGroup.eq.mp hyx
          have h3 : (x : G) = y * ((y⁻¹ * x : ↥N) : G) := by simp
          rw [h3]
          exact mul_mem hy (hLC h2)
      rw [Nat.card_congr (Additive.toMul.subtypeEquiv hmem), ← relIndex_eq_card_map_mk,
        relIndex_subgroupOf hCN]
    have hquot : Nat.card (W ⧸ Representation.invariants (ρ.comp A'.subtype)) = C.relIndex N := by
      have h2 := Submodule.card_eq_card_quotient_mul_card
        (Representation.invariants (ρ.comp A'.subtype))
      rw [hcardW, hcardInv, ← relIndex_mul_relIndex L C N hLC hCN] at h2
      exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _))
        h2).symm
    have hfin : Nat.card (W ⧸ Representation.invariants (ρ.comp A'.subtype)) =
        2 ^ finrank (ZMod 2) (W ⧸ Representation.invariants (ρ.comp A'.subtype)) := by
      have : Finite (W ⧸ Representation.invariants (ρ.comp A'.subtype)) :=
        Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
      have : Module.Finite (ZMod 2) (W ⧸ Representation.invariants (ρ.comp A'.subtype)) :=
        Module.Finite.of_finite
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have hA'map : A'.map H.subtype = A := by
      rw [hA', subgroupOf_map_subtype, inf_eq_left.mpr hAH]
    have hrel : ((CFSG.pCore 2 ↥H).map H.subtype).relIndex A =
        (CFSG.pCore 2 ↥H).relIndex A' := by
      rw [← relIndex_map_map_of_injective _ _ H.subtype_injective, hA'map]
    obtain ⟨s, hs⟩ : ∃ s, (CFSG.pCore 2 ↥H).relIndex A' = 2 ^ s := by
      have hdvd : (CFSG.pCore 2 ↥H).relIndex A' ∣ Nat.card A' := index_dvd_card _
      obtain ⟨a, ha⟩ := (IsElementaryAbelian.isPGroup 2 ↥A').exists_card_eq
      rw [ha] at hdvd
      obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨s, hs⟩
    rw [hs, Nat.log_pow (by norm_num)] at h1
    rw [hrel, hs, ← hquot, hfin]
    exact Nat.pow_le_pow_right (by norm_num) h1

end CFSG.Quasithin.H13.NQCore
