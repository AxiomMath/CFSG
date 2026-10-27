module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3ERed
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMain

public section

namespace CFSG.Quasithin.L31521E

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Fin257
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

theorem exists_equiv_projUnitriangular {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    {n : ℕ} (hn : 2 ≤ n) (hL : IsPSL 3 2 n ↥L) (hP : IsSylowTwoOf P L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : ↥L ≃* projectiveSL 3 F), Nat.card F = 2 ^ n ∧
      ∀ x : ↥L, (x : G) ∈ P ↔ φ x ∈ projUnitriangular 3 F := by
  obtain ⟨-, F, hFf, hFfin, hF, ⟨e⟩⟩ := hL
  let φ0 : ↥L ≃* projectiveSL 3 F := e.trans (statedSLEquiv F)
  have hchar : CharP F 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 (projectiveSL 3 F) :=
    (A4.toSylow hP).mapSurjective (f := φ0.toMonoidHom) φ0.surjective
  have hQ : (Q : Subgroup (projectiveSL 3 F)) = (P.subgroupOf L).map φ0.toMonoidHom := rfl
  obtain ⟨U₀, hU₀⟩ := LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
    (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 F) U₀ Q
  have hmem : ∀ x, x ∈ (Q : Subgroup (projectiveSL 3 F)) ↔
      g⁻¹ * x * g ∈ projUnitriangular 3 F := by
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
  refine ⟨F, hFf, hFfin, φ0.trans (MulAut.conj g⁻¹), hF, fun x => ?_⟩
  have h1 : (x : G) ∈ P ↔ φ0 x ∈ (Q : Subgroup (projectiveSL 3 F)) := by
    rw [hQ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  rw [h1, hmem]
  change _ ↔ g⁻¹ * φ0 x * g⁻¹⁻¹ ∈ projUnitriangular 3 F
  rw [inv_inv]

variable {G : Type} [Group G] [Finite G]

theorem rankBound1521_l3 {S L : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hL : IsPSL 3 2 n ↥L)
    (hq : CFSG.IsQuasisimple ↥L) (hSyl : IsSylowTwoOf (S ⊓ L) L) :
    ∃ V V' : Subgroup G, RankBound1521 S L V V' := by
  obtain ⟨F, hFf, hFfin, φ, hF, hφ⟩ := exists_equiv_projUnitriangular hn hL hSyl
  have hchar : CharP F 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have hdata := L3.modelData_L3 (F := F) hn hF
  let π : ↥L →* projectiveSL 3 F := φ.toMonoidHom
  have hπ : ∀ x : ↥L, π x = φ x := fun _ => rfl
  have hinj : Function.Injective π := φ.injective
  have hZ : ∀ x : ↥L, (∀ y : ↥L, x * y = y * x) → x = 1 := by
    intro x hx
    apply φ.injective
    rw [map_one]
    refine hdata.center_trivial _ fun y => ?_
    obtain ⟨y', rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hx y']
  have hred : Red257 L (S ⊓ L)
      (pre π (Subgroup.normalizer ((L3.V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))))
      (pre π (Subgroup.normalizer ((L3.V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))))
      (pre π L3.V1) (pre π L3.V2) π (projUnitriangular 3 F) L3.V1 L3.V2 :=
    { surj := φ.surjective
      ker_central := fun x hx y => by
        have : x = 1 := hinj (by rw [hx, map_one])
        rw [this, one_mul, mul_one]
      ker_two := fun x => ⟨0, by
        have h1 : (x : ↥L) = 1 := hinj (by rw [map_one]; exact MonoidHom.mem_ker.mp x.2)
        rw [pow_zero, pow_one]
        exact Subtype.ext h1⟩
      center_le := fun x hx => by rw [hZ x hx, map_one]
      hP := by
        ext x
        rw [mem_pre]
        constructor
        · intro hx
          exact ⟨hSyl.1 hx, (hφ ⟨x, hSyl.1 hx⟩).mp hx⟩
        · rintro ⟨hxL, hxU⟩
          exact (hφ ⟨x, hxL⟩).mpr hxU
      hK₁ := rfl
      hK₂ := rfl
      hV := rfl
      hV' := rfl }
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard : 2 < Nat.card (L3.V1 : Subgroup (projectiveSL 3 F)) := by
    rw [L3.card_V1]
    nlinarith
  exact ⟨_, _, rankBound1521_of_red hq hred (L3.maxRankModel_L3 hn hF)
    (isElemAbelian_pre1521 hinj hdata.elem₁) hdata.le₁ hdata.le₂ hcard⟩

end CFSG.Quasithin.L31521E
