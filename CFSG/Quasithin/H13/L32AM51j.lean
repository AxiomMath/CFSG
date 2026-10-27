module

public import CFSG.Quasithin.H13.L32AM51f

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Equiv Equiv.Perm
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem not_le_normalizer_map {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) {P U : Subgroup A}
    (h : ¬ P ≤ Subgroup.normalizer (U : Set A)) :
    ¬ P.map f ≤ Subgroup.normalizer ((U.map f : Subgroup B) : Set B) := by
  intro hle
  apply h
  intro g hg
  have hN := Subgroup.mem_normalizer_iff.mp (hle ⟨g, hg, rfl⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    obtain ⟨u', hu', he⟩ := (hN (f u)).mp ⟨u, hu, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at he
    rwa [← hf he]
  · intro hu
    obtain ⟨u', hu', he⟩ := (hN (f u)).mpr ⟨g * u * g⁻¹, hu, by rw [map_mul, map_mul, map_inv]⟩
    rwa [← hf he]

theorem s3_preimG {P : Type*} [Group P] {ψ : ↥H →* P} {T₀ : Subgroup G} (hT₀H : T₀ ≤ H)
    (hT₀2 : IsPGroup 2 T₀) (hkerT : ψ.ker ≤ T₀.subgroupOf H) {R : Subgroup P}
    (hTR : (T₀.subgroupOf H).map ψ ≤ R) (hRr : R ≤ ψ.range)
    (h3 : ((T₀.subgroupOf H).map ψ).relIndex R = 3)
    (hn : ¬ R ≤ Subgroup.normalizer (((T₀.subgroupOf H).map ψ : Subgroup P) : Set P)) :
    T₀ ≤ preimG ψ R ∧ IsSylowTwoOf T₀ (preimG ψ R) ∧ oTwoUpper (preimG ψ R) ⊔ T₀ = preimG ψ R ∧
      quasithinO2QuotientIso (preimG ψ R) (Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := preimG ψ R with hXdef
  have hTX : T₀ ≤ X := fun t ht => mem_preimG.mpr ⟨hT₀H ht, hTR ⟨⟨t, hT₀H ht⟩, ht, rfl⟩⟩
  have hXH : X ≤ H := preimG_le ψ R
  have hX3 : T₀.relIndex X = 3 := by
    have e1 : (T₀.subgroupOf H).relIndex (X.subgroupOf H) = T₀.relIndex X :=
      Subgroup.relIndex_subgroupOf hXH
    have e2 : X.subgroupOf H = R.comap ψ :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have e3 : ((T₀.subgroupOf H).map ψ).comap ψ = T₀.subgroupOf H :=
      Subgroup.comap_map_eq_self hkerT
    have e4 : (R.comap ψ).map ψ = R := by
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr hRr]
    rw [← e1, e2, ← e3, Subgroup.relIndex_comap, e4, h3]
  have hsyl : IsSylowTwoOf T₀ X := ⟨hTX, hT₀2, by
    show ¬ 2 ∣ T₀.relIndex X
    rw [hX3]
    decide⟩
  refine ⟨hTX, hsyl, oTwoUpper_sup_of_sylow hsyl, ?_⟩
  have hnX : ¬ X ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro hXN
    apply hn
    intro r hr
    obtain ⟨h, rfl⟩ := hRr hr
    have hhX : (h : G) ∈ X := mem_preimG.mpr ⟨h.2, hr⟩
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ s : ↥H, s ∈ T₀.subgroupOf H → h * s * h⁻¹ ∈ T₀.subgroupOf H := fun s hs => by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hXN hhX) s).mp hs
    have key' : ∀ s : ↥H, s ∈ T₀.subgroupOf H → h⁻¹ * s * h ∈ T₀.subgroupOf H := fun s hs => by
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXN hhX)) s).mp hs
      simpa using this
    intro p
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨h * s * h⁻¹, key s hs, by simp [map_mul, map_inv]⟩
    · rintro ⟨s, hs, hsp⟩
      refine ⟨h⁻¹ * s * h, key' s hs, ?_⟩
      rw [map_mul, map_mul, map_inv, hsp]
      group
  obtain ⟨e⟩ := L32A.nonempty_quotient_perm_three hTX hT₀2 hX3 hnX
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

namespace Top51

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 8)} (C : Top51 T L V H W K π)
  [IsMulCommutative ↥(conjClosure V H)]
  {πK : ↥K →* Lin.SLn 4} (hπs : Function.Surjective πK)
  (hkerK : ∀ k : ↥K, πK k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
include C

@[expose] noncomputable def theta : Lin.SLn 4 →* Perm (Fin 8) :=
  (alternatingGroup (Fin 8)).subtype.comp ((C.psi hπs hkerK).symm.trans C.iota).toMonoidHom

theorem theta_injective : Function.Injective (C.theta hπs hkerK) :=
  (alternatingGroup (Fin 8)).subtype_injective.comp ((C.psi hπs hkerK).symm.trans C.iota).injective

theorem theta_piK (k : ↥K) : C.theta hπs hkerK (πK k) = π (Subgroup.inclusion C.hKH k) := by
  have h1 : (C.psi hπs hkerK).symm (πK k) = C.thetaK k := by
    rw [MulEquiv.symm_apply_eq, C.psi_thetaK]
  simp only [theta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, h1,
    Subgroup.coe_subtype]
  rw [← C.emb_eq_iota]
  exact C.emb_act (Subgroup.inclusion C.hKH k)

theorem act_eq_of_pi_eq {h h' : ↥H} (he : π h = π h') : C.act h = C.act h' := by
  have h1 : C.act (h⁻¹ * h') = 1 := by
    rw [C.act_eq_one_iff, map_mul, map_inv, he, inv_mul_cancel]
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

omit [IsMulCommutative ↥(conjClosure V H)] in
theorem oTwoUpper_le_K {X : Subgroup G} (hXH : X ≤ H)
    (hXA : ∀ x (hx : x ∈ X), π ⟨x, hXH hx⟩ ∈ alternatingGroup (Fin 8)) : oTwoUpper X ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer C.hKH).mpr C.hKn
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hxH : x ∈ H := hXH hx
  obtain ⟨k, hkK, hk⟩ := C.exists_pi_eq (hXA x hx)
  have hkH : k ∈ H := C.hKH hkK
  set o : ↥H := ⟨k⁻¹ * x, H.mul_mem (H.inv_mem hkH) hxH⟩ with ho_def
  have ho : (o : G) ∈ pCoreOf 2 H := by
    have h1 : π o = 1 := by
      have e : o = (⟨k, hkH⟩ : ↥H)⁻¹ * ⟨x, hxH⟩ := rfl
      rw [e, map_mul, map_inv, hk, inv_mul_cancel]
    exact (C.pi_eq_one_iff _).mp h1
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, ho⟩
  refine ⟨m, ?_⟩
  have ho1 : o ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
  have hxo : (⟨x, hxH⟩ : ↥H) = ⟨k, hkH⟩ * o := Subtype.ext (by simp [ho_def])
  have hk1 : (QuotientGroup.mk (⟨k, hkH⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hkK)
  have h2 : (QuotientGroup.mk ((⟨x, hxH⟩ : ↥H) ^ 2 ^ m) : ↥H ⧸ K.subgroupOf H) = 1 := by
    rw [QuotientGroup.mk_pow, hxo, QuotientGroup.mk_mul, hk1, one_mul, ← QuotientGroup.mk_pow,
      ho1, QuotientGroup.mk_one]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h2
  exact h2

end Top51

end CFSG.Quasithin.H13.L32A.C
