module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Hat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Red
import CFSG.Quasithin.Background.A3Structure312Quotient
import CFSG.Monster.B.Short.Extraspecial

public section

namespace CFSG.Quasithin.J4M2

open scoped commutatorElement

theorem commutator_eq_top_of_commutator_eq_self {G : Type*} [Group G] {B : Subgroup G}
    (h : ⁅B, B⁆ = B) : commutator ↥B = ⊤ := by
  refine Subgroup.map_injective B.subtype_injective ?_
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, h]

theorem commutator_quotient_eq_top {X : Type*} [Group X] (V : Subgroup X) [V.Normal]
    (h : commutator X = ⊤) : commutator (X ⧸ V) = ⊤ := by
  have hsurj : Function.Surjective (QuotientGroup.mk' V) := QuotientGroup.mk'_surjective V
  have h1 : ⁅(⊤ : Subgroup (X ⧸ V)), ⊤⁆ =
      Subgroup.map (QuotientGroup.mk' V) ⁅(⊤ : Subgroup X), ⊤⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj]
  rw [commutator_def, h1, ← commutator_def, h, Subgroup.map_top_of_surjective _ hsurj]

theorem isHat_quotient_of_surjective {X A S : Type} [Group X] [Finite X] [Group A] [Group S]
    (ψ : X →* A) (hψ : Function.Surjective ψ) (V : Subgroup X) [V.Normal] (hVψ : V ≤ ψ.ker)
    (hperf : commutator X = ⊤) (hcard : Nat.card ψ.ker = 3 * Nat.card V) (e : A ≃* S)
    (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) : IsHat (X ⧸ V) S := by
  have : Finite A := Finite.of_surjective ψ hψ
  let ψ' : X ⧸ V →* A := QuotientGroup.lift V ψ hVψ
  have hψ' : Function.Surjective ψ' := fun a => by
    obtain ⟨x, rfl⟩ := hψ a
    exact ⟨(x : X ⧸ V), rfl⟩
  have h1 : Nat.card X = Nat.card A * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
  have h2 : Nat.card (X ⧸ V) = Nat.card A * Nat.card ψ'.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ'.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ').toEquiv]
  have h3 : Nat.card X = Nat.card (X ⧸ V) * Nat.card V :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup V
  have hpos : 0 < Nat.card A * Nat.card V := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hW : Nat.card ψ'.ker = 3 := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Nat.card A * Nat.card V * Nat.card ψ'.ker = Nat.card X := by rw [h3, h2]; ring
      _ = Nat.card A * (3 * Nat.card V) := by rw [h1, hcard]
      _ = Nat.card A * Nat.card V * 3 := by ring
  exact isHat_of_quotient_of_normal_order_three (commutator_quotient_eq_top V hperf) ψ'.ker hW
    ((QuotientGroup.quotientKerEquivOfSurjective ψ' hψ').trans e) hS hnab

theorem eq_of_mem_cComp_of_map {G S : Type*} [Group G] [Finite G] [Group S] [Finite S]
    {M K B0 : Subgroup G} (ρ : ↥M →* S) {A : Subgroup S} (hAs : IsSimpleGroup ↥A)
    (hAle : A ≤ ρ.range) (hidx : Nat.card ρ.range = 2 * Nat.card A) (hKM : K ≤ M)
    (hKρ : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ K) (hKsolv : Group.IsSolvable ↥K) (hB0M : B0 ≤ M)
    (hKB0 : K ≤ B0) (hB0 : ∀ m : ↥M, (m : G) ∈ B0 ↔ ρ m ∈ A) (hB0perf : ⁅B0, B0⁆ = B0)
    {B : Subgroup G} (hB : B ∈ cComp M) : B = B0 := by
  have hBM : B ≤ M := le_of_mem_cComp hB
  have hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K := fun m hm k hk =>
    (hKρ (⟨m, hm⟩ * ⟨k, hKM hk⟩ * ⟨m, hm⟩⁻¹)).1 (by
      rw [map_mul, map_mul, (hKρ ⟨k, hKM hk⟩).2 hk, mul_one, map_inv, mul_inv_cancel])
  have hkerSolv : Group.IsSolvable ↥(ρ.ker ⊓ (⊤ : Subgroup ↥M)) := by
    have := hKsolv
    refine Group.isSolvable_of_isSolvable_injective (G' := ↥K)
      (f := { toFun := fun m => ⟨((m : ↥M) : G), (hKρ m.1).1 m.2.1⟩
              map_one' := rfl
              map_mul' := fun _ _ => rfl }) fun a b h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hBtop : B.subgroupOf M ∈ cComp (⊤ : Subgroup ↥M) := by
    simpa only [Subgroup.subgroupOf_self] using A312.mem_cComp_subgroupOf (le_refl M) hB
  have himg : (B.subgroupOf M).map ρ ∈ cComp ρ.range := by
    rw [MonoidHom.range_eq_map]
    exact A312.map_mem_cComp ρ hkerSolv hBtop
  obtain ⟨hnorm, hcomm, -⟩ := card_eq_two_mul_facts hAle hidx
  have hBA : (B.subgroupOf M).map ρ = A := eq_of_mem_cComp_of_simple hAle hnorm hAs hcomm himg
  have hBB0 : B ≤ B0 := fun b hb => (hB0 ⟨b, hBM hb⟩).2 (by
    rw [← hBA]
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 hb))
  have hB0le : B0 ≤ B ⊔ K := by
    intro x hx
    have hxM : x ∈ M := hB0M hx
    have hxA : ρ ⟨x, hxM⟩ ∈ A := (hB0 ⟨x, hxM⟩).1 hx
    rw [← hBA] at hxA
    obtain ⟨y, hy, hyx⟩ := hxA
    have hk : (y : G)⁻¹ * x ∈ K := by
      refine (hKρ (y⁻¹ * ⟨x, hxM⟩)).1 ?_
      rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have hx' : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [hx']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hy) hk
  have hBsup : B ⊔ K = B0 := le_antisymm (sup_le hBB0 hKB0) hB0le
  have hBnorm : B ≤ Subgroup.normalizer (K : Set G) := fun b hb =>
    Subgroup.mem_normalizer_iff.2 fun x => ⟨hKn b (hBM hb) x, fun hx => by
      have h := hKn b⁻¹ (M.inv_mem (hBM hb)) _ hx
      have h' : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
      rwa [h'] at h⟩
  have hcore : perfectCore (B ⊔ K) = B := (cComp_commutator_perfectCore hB hKM hKsolv hBnorm).2
  rw [hBsup, perfectCore_eq_self_of_perfect hB0perf] at hcore
  exact hcore.symm

theorem isExt_extraspecial_hat_of_surjective {G A S' : Type} [Group G] [Finite G] [Group A]
    [Group S'] {B0 K Q : Subgroup G} (ψ : ↥B0 →* A) (hψ : Function.Surjective ψ)
    (hker : ∀ b : ↥B0, ψ b = 1 ↔ (b : G) ∈ K) (hperf : ⁅B0, B0⁆ = B0) (hKB0 : K ≤ B0)
    (hQK : Q ≤ K) (hKcard : Nat.card K = 3 * 2 ^ 13) (hQcard : Nat.card Q = 2 ^ 13)
    (hQext : CFSG.IsExtraspecialPGroup 2 ↥Q) (hQn : ∀ b ∈ B0, ∀ x ∈ Q, b * x * b⁻¹ ∈ Q)
    (e : A ≃* S') (hS' : IsSimpleGroup S') (hnab : ∃ a b : S', a * b ≠ b * a) :
    IsExt ↥B0 (fun V _ => IsExtraspecial2 6 V) (fun Y _ => IsHat Y S') := by
  have hQB0 : Q ≤ B0 := hQK.trans hKB0
  have hVn : (Q.subgroupOf B0).Normal := ⟨fun x hx b => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hQn b b.2 x hx⟩
  have hkerEq : ψ.ker = K.subgroupOf B0 := by
    ext b
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hVψ : Q.subgroupOf B0 ≤ ψ.ker := by
    rw [hkerEq]
    exact fun b hb => Subgroup.mem_subgroupOf.2 (hQK (Subgroup.mem_subgroupOf.1 hb))
  have hcard : Nat.card ψ.ker = 3 * Nat.card (Q.subgroupOf B0) := by
    rw [hkerEq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKB0).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQB0).toEquiv, hKcard, hQcard]
  refine ⟨Q.subgroupOf B0, hVn, ?_, ?_⟩
  · have hQ2 : IsExtraspecial2 6 ↥Q := ⟨hQext.isExtraspecial, by rw [hQcard]⟩
    exact IsExtraspecial2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQB0).symm hQ2
  · exact isHat_quotient_of_surjective ψ hψ (Q.subgroupOf B0) hVψ
      (commutator_eq_top_of_commutator_eq_self hperf) hcard e hS' hnab

theorem shape_of_mem_cComp {G S S' : Type} [Group G] [Finite G] [Group S] [Finite S] [Group S']
    (M : Subgroup G) (ρ : ↥M →* S) (A : Subgroup S) (e : ↥A ≃* S')
    (hS' : IsSimpleGroup S') (hnab : ∃ a b : S', a * b ≠ b * a)
    (hAle : A ≤ ρ.range) (hidx : Nat.card ρ.range = 2 * Nat.card A)
    (K Q B0 : Subgroup G) (hKM : K ≤ M) (hKρ : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ K)
    (hKsolv : Group.IsSolvable ↥K) (hKcard : Nat.card K = 3 * 2 ^ 13)
    (hQK : Q ≤ K) (hQcard : Nat.card Q = 2 ^ 13) (hQext : CFSG.IsExtraspecialPGroup 2 ↥Q)
    (hQn : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q)
    (hB0M : B0 ≤ M) (hKB0 : K ≤ B0) (hB0 : ∀ m : ↥M, (m : G) ∈ B0 ↔ ρ m ∈ A)
    (hB0perf : ⁅B0, B0⁆ = B0) :
    ∀ B ∈ cComp M, B = B0 ∧
      IsExt ↥B (fun V _ => IsExtraspecial2 6 V) (fun Y _ => IsHat Y S') := by
  intro B hB
  have := hS'
  have hBB0 : B = B0 :=
    eq_of_mem_cComp_of_map ρ e.isSimpleGroup hAle hidx hKM hKρ hKsolv hB0M hKB0 hB0 hB0perf hB
  refine ⟨hBB0, ?_⟩
  rw [hBB0]
  let ψ : ↥B0 →* ↥A :=
    (ρ.comp (Subgroup.inclusion hB0M)).codRestrict A fun b => (hB0 ⟨b, hB0M b.2⟩).1 b.2
  have hψ : Function.Surjective ψ := by
    intro a
    obtain ⟨m, hm⟩ := hAle a.2
    exact ⟨⟨(m : G), (hB0 m).2 (hm ▸ a.2)⟩, Subtype.ext hm⟩
  have hker : ∀ b : ↥B0, ψ b = 1 ↔ (b : G) ∈ K := fun b =>
    Iff.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩ (hKρ ⟨b, hB0M b.2⟩)
  exact isExt_extraspecial_hat_of_surjective ψ hψ hker hB0perf hKB0 hQK hKcard hQcard hQext
    (fun b hb x hx => hQn b (hB0M hb) x hx) e hS' hnab

theorem j4Shape_of_mem_cComp {G S : Type} [Group G] [Finite G] [Group S] [Finite S]
    (M : Subgroup G) (ρ : ↥M →* S) (A : Subgroup S)
    (e : ↥A ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22)
    (hS' : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    (hnab : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .M22, a * b ≠ b * a)
    (hAle : A ≤ ρ.range) (hidx : Nat.card ρ.range = 2 * Nat.card A)
    (K Q B0 : Subgroup G) (hKM : K ≤ M) (hKρ : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ K)
    (hKsolv : Group.IsSolvable ↥K) (hKcard : Nat.card K = 3 * 2 ^ 13)
    (hQK : Q ≤ K) (hQcard : Nat.card Q = 2 ^ 13) (hQext : CFSG.IsExtraspecialPGroup 2 ↥Q)
    (hQn : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q)
    (hB0M : B0 ≤ M) (hKB0 : K ≤ B0) (hB0 : ∀ m : ↥M, (m : G) ∈ B0 ↔ ρ m ∈ A)
    (hB0perf : ⁅B0, B0⁆ = B0) :
    ∀ B ∈ cComp M, B = B0 ∧ J4Fam.J4Shape ↥B := fun B hB =>
  have h := shape_of_mem_cComp M ρ A e hS' hnab hAle hidx K Q B0 hKM hKρ hKsolv hKcard hQK hQcard
    hQext hQn hB0M hKB0 hB0 hB0perf B hB
  ⟨h.1, Or.inl h.2⟩

end CFSG.Quasithin.J4M2
