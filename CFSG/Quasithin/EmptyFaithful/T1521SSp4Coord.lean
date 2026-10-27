module

public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Act
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.Sp4

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.QuasithinUnique CFSG.Quasithin

theorem exists_equiv_projUnipotent {G : Type} [Group G] [Finite G] {L R : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hL : IsPSp4 2 n ↥L) (hR : IsSylowTwoOf R L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : ↥L ≃* StatedProj (StatedSp 2 K)),
      Nat.card K = 2 ^ n ∧ ∀ x : ↥L, (x : G) ∈ R ↔ φ x ∈ projUnipotent 2 K := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨φ0⟩⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  let Q : Sylow 2 (StatedProj (StatedSp 2 K)) :=
    (A4.toSylow hR).mapSurjective (f := φ0.toMonoidHom) φ0.surjective
  have hQ : (Q : Subgroup (StatedProj (StatedSp 2 K))) = (R.subgroupOf L).map φ0.toMonoidHom :=
    rfl
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnipotent (K := K) (r := 2) 2 (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 K)) U₀ Q
  have hmem : ∀ x, x ∈ (Q : Subgroup (StatedProj (StatedSp 2 K))) ↔
      g⁻¹ * x * g ∈ projUnipotent 2 K := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, hU₀]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g⁻¹ * (g * y * g⁻¹) * g ∈ _
      simpa [mul_assoc] using hy
    · intro h
      refine ⟨g⁻¹ * x * g, h, ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  refine ⟨K, hKf, hKfin, φ0.trans (MulAut.conj g⁻¹), hK, fun x => ?_⟩
  have h1 : (x : G) ∈ R ↔ φ0 x ∈ (Q : Subgroup (StatedProj (StatedSp 2 K))) := by
    rw [hQ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  rw [h1, hmem]
  change _ ↔ g⁻¹ * φ0 x * g⁻¹⁻¹ ∈ projUnipotent 2 K
  rw [inv_inv]

section Coord

variable {G : Type} [Group G] {K : Type} [Field K] {L R : Subgroup G}
  (φ : ↥L ≃* StatedProj (StatedSp 2 K))

@[expose] noncomputable def vHom : Multiplicative (K × K) →* G where
  toFun x := ((φ.symm (vP (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2) : ↥L) : G)
  map_one' := by simp [vP_zero]
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ← vP_mul, map_mul, Subgroup.coe_mul]

@[expose] noncomputable def vW (x : K × K) : G := vHom φ (Multiplicative.ofAdd x)

@[expose] noncomputable def vSub : Subgroup G := (vHom φ).range

theorem vW_apply (x : K × K) : vW φ x = ((φ.symm (vP x.1 x.2) : ↥L) : G) := rfl

theorem vW_mul (x y : K × K) : vW φ x * vW φ y = vW φ (x + y) := by
  rw [vW, vW, vW, ← map_mul]
  rfl

theorem vW_zero : vW φ (0 : K × K) = 1 := by
  rw [vW]
  exact map_one _

theorem vW_mem (x : K × K) : vW φ x ∈ vSub φ := ⟨_, rfl⟩

theorem exists_vW_of_mem {y : G} (hy : y ∈ vSub φ) : ∃ x : K × K, vW φ x = y := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨Multiplicative.toAdd x, rfl⟩

variable [CharP K 2]

theorem vW_injective : Function.Injective (vW φ) := by
  intro x y h
  have h1 : φ.symm (vP x.1 x.2) = φ.symm (vP y.1 y.2) := Subtype.ext h
  obtain ⟨h2, h3⟩ := vP_injective (φ.symm.injective h1)
  exact Prod.ext h2 h3

omit [CharP K 2] in
theorem vSub_le_L : vSub φ ≤ L := by
  rintro _ ⟨x, rfl⟩
  exact (φ.symm _).2

variable {φ}

omit [CharP K 2] in
theorem vW_mem_R (hφ : ∀ x : ↥L, (x : G) ∈ R ↔ φ x ∈ projUnipotent 2 K) (x : K × K) :
    vW φ x ∈ R := by
  rw [vW_apply, hφ, MulEquiv.apply_symm_apply]
  exact vP_mem_projUnipotent _ _

omit [CharP K 2] in
theorem vSub_le_R (hφ : ∀ x : ↥L, (x : G) ∈ R ↔ φ x ∈ projUnipotent 2 K) : vSub φ ≤ R := by
  rintro _ ⟨x, rfl⟩
  exact vW_mem_R hφ _

theorem vW_commute_R (hφ : ∀ x : ↥L, (x : G) ∈ R ↔ φ x ∈ projUnipotent 2 K) (hRL : R ≤ L)
    {r : G} (hr : r ∈ R) (x : K × K) : r * vW φ x = vW φ x * r := by
  have hr' := (hφ ⟨r, hRL hr⟩).mp hr
  obtain ⟨u, hu, hur⟩ := hr'
  have h1 : (⟨r, hRL hr⟩ : ↥L) * φ.symm (vP x.1 x.2) = φ.symm (vP x.1 x.2) * ⟨r, hRL hr⟩ := by
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hur, vP, ← map_mul, ← map_mul,
      tauS_zero_mul_comm hu]
  have h2 := congrArg (fun z : ↥L => (z : G)) h1
  simpa [vW_apply] using h2

theorem isElemAbelian_vSub : CFSG.Open.IsElemAbelian 2 (vSub φ) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨xa, hxa⟩ := exists_vW_of_mem φ a.2
    obtain ⟨xb, hxb⟩ := exists_vW_of_mem φ b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hxa, ← hxb, vW_mul, vW_mul, add_comm]
  · obtain ⟨xx, rfl⟩ := exists_vW_of_mem φ hx
    rw [sq, vW_mul, ← two_nsmul, two_nsmul]
    have : xx + xx = 0 := by
      ext <;> simp [CharTwo.add_self_eq_zero]
    rw [this, vW_zero]

theorem card_vSub : Nat.card (vSub φ) = Nat.card K ^ 2 := by
  have hbij : Function.Bijective (fun x : K × K => (⟨vW φ x, vW_mem φ x⟩ : vSub φ)) := by
    refine ⟨fun x y h => vW_injective φ (Subtype.mk.inj h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := exists_vW_of_mem φ y.2
    exact ⟨x, Subtype.ext hx⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, sq]

variable [Finite K]

theorem exists_vAct_conj {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hφ : ∀ x : ↥L, (x : G) ∈ R ↔ φ x ∈ projUnipotent 2 K) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (haR : ∀ y ∈ L, (y ∈ R ↔ a * y * a⁻¹ ∈ R)) :
    ∃ (l₁ l₂ : K) (σ : K ≃+* K) (ε : Bool), l₁ ≠ 0 ∧ l₂ ≠ 0 ∧
      (∀ x : K × K, a * vW φ x * a⁻¹ = vW φ (vAct l₁ l₂ σ ε x)) ∧
      ((∀ x : K × K, vAct l₁ l₂ σ ε x = x) →
        ∃ l ∈ R, (l : G)⁻¹ * a ∈ Subgroup.centralizer (L : Set G)) := by
  let α : MulAut ↥L := conjAct L ⟨a, ha⟩
  let β : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr φ α
  have hα : ∀ y : ↥L, ((α y : ↥L) : G) = a * (y : G) * a⁻¹ := fun y => rfl
  have hβz : ∀ z, β z = φ (α (φ.symm z)) := fun z => rfl
  have hβ : ∀ x, β x ∈ projUnipotent 2 K ↔ x ∈ projUnipotent 2 K := by
    intro x
    have hx : φ (φ.symm x) = x := by simp
    have h1 := hφ (α (φ.symm x))
    have h2 := hφ (φ.symm x)
    rw [hx] at h2
    rw [hβz, ← h1, ← h2, hα]
    exact (haR _ (φ.symm x).2).symm
  obtain ⟨l₁, l₂, σ, ε, h1, h2, hact, hid⟩ := exists_vAct hn hK hβ
  refine ⟨l₁, l₂, σ, ε, h1, h2, fun x => ?_, fun hx => ?_⟩
  · have e : α (φ.symm (vP x.1 x.2)) = φ.symm (β (vP x.1 x.2)) := by
      rw [hβz, MulEquiv.symm_apply_apply]
    have e2 := congrArg (fun z : ↥L => (z : G)) e
    simp only [hα] at e2
    rw [vW_apply, vW_apply]
    change _ = ((φ.symm (vP _ _) : ↥L) : G)
    rw [← hact x, ← e2]
  · obtain ⟨u, hu, hβu⟩ := hid hx
    set l : ↥L := φ.symm (proj 2 K u) with hl
    have hlR : (l : G) ∈ R := by
      rw [hφ, hl, MulEquiv.apply_symm_apply]
      exact ⟨u, hu, rfl⟩
    refine ⟨l, hlR, ?_⟩
    have hconj : ∀ y : ↥L, α y = l * y * l⁻¹ := by
      intro y
      have h1 : β (φ y) = proj 2 K u * φ y * (proj 2 K u)⁻¹ := by
        rw [hβu, MulAut.conj_apply]
      have h2 : α y = φ.symm (β (φ y)) := by
        rw [hβz, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      rw [h2, h1, hl, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun z : ↥L => (z : G)) (hconj ⟨y, hy⟩)
    simp only [hα] at h1
    have h1' : a * y * a⁻¹ = (l : G) * y * (l : G)⁻¹ := h1
    calc y * ((l : G)⁻¹ * a) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * a := by group
      _ = (l : G)⁻¹ * (a * y * a⁻¹) * a := by rw [h1']
      _ = (l : G)⁻¹ * a * y := by group

end Coord

end CFSG.Quasithin.Sp4
