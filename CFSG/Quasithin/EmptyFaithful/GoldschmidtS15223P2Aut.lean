module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2SL2Rig
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Block

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem exists_conj_le_of_odd_index {K : Type*} [Group K] [Finite K] {P Q : Subgroup K}
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) :
    ∃ g : K, ∀ x ∈ P, g * x * g⁻¹ ∈ Q := by
  obtain ⟨R, hR⟩ := hP.exists_le_sylow
  let S : Sylow 2 K := hQ.toSylow hQi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K R S
  refine ⟨g, fun x hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ ((g • R : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hR hx, by simp [MulAut.conj_apply]⟩
  rw [hg] at h1
  exact h1

section Unitriangular

variable {F : Type*} [Field F]

@[expose] def sl2UHom (F : Type*) [Field F] :
    Multiplicative F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun a := sl2U (Multiplicative.toAdd a)
  map_one' := sl2U_zero
  map_mul' a b := by simp [sl2U_mul]

@[expose] def sl2UGroup (F : Type*) [Field F] : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
  (sl2UHom F).range

theorem sl2U_mem_sl2UGroup (a : F) : sl2U a ∈ sl2UGroup F :=
  ⟨Multiplicative.ofAdd a, rfl⟩

theorem isPGroup_sl2UGroup [CharP F 2] : IsPGroup 2 (sl2UGroup F) := by
  intro g
  obtain ⟨a, ha⟩ := g.2
  refine ⟨1, Subtype.ext ?_⟩
  have h : (g : Matrix.SpecialLinearGroup (Fin 2) F) = sl2U (Multiplicative.toAdd a) := ha.symm
  simp only [pow_one, Subgroup.coe_pow, h, Subgroup.coe_one]
  rw [pow_two, sl2U_mul_self]

end Unitriangular

variable {G : Type} [Group G]

theorem commutator_mem_blockQ_of_lin2 [Finite G] {X U₂ : Subgroup G} {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type X n) {z : G} (hzN : z ∈ Subgroup.normalizer (X : Set G))
    (hU₂2 : IsPGroup 2 U₂) (hUz : ∀ u ∈ U₂, u * z = z * u)
    (hodd : ¬ 2 ∣ (U₂.subgroupOf X).index)
    {k : G} (hk : k ∈ X) (hk3 : k ^ 3 = 1) (hkQ : k ∉ blockQ X) (hkz : k * z = z * k) :
    ∀ l ∈ X, z * l * z⁻¹ * l⁻¹ ∈ blockQ X := by
  obtain ⟨F, hFf, hFfin, hcard, α, hαs, hαk, -⟩ := hlin
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hn.le hq
  set H : Subgroup ↥X := U₂.subgroupOf X with hH
  have hH2 : IsPGroup 2 H := hU₂2.comap_subtype
  have hUb2 : IsPGroup 2 (H.map α) := hH2.map α
  have hUbi : ¬ 2 ∣ (H.map α).index := fun h => hodd (h.trans (H.index_map_dvd hαs))
  obtain ⟨g, hg⟩ := exists_conj_le_of_odd_index isPGroup_sl2UGroup hUb2 hUbi
  set α' : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MulAut.conj g⁻¹).toMonoidHom.comp α with hα'
  have hα'x : ∀ x : ↥X, α' x = g⁻¹ * α x * g := fun x => by simp [hα']
  have hα's : Function.Surjective α' := by
    intro y
    obtain ⟨x, hx⟩ := hαs (g * y * g⁻¹)
    exact ⟨x, by rw [hα'x, hx]; group⟩
  have hα'ker : ∀ x : ↥X, α' x = 1 ↔ x ∈ CFSG.pCore 2 ↥X := by
    intro x
    rw [← hαk, MonoidHom.mem_ker, hα'x]
    constructor
    · intro h
      have : α x = g * 1 * g⁻¹ := by rw [← h]; group
      simpa using this
    · intro h
      rw [h]
      group
  let σ : MulAut ↥X := X.normalizerMonoidHom ⟨z, hzN⟩
  have hσ : ∀ x : ↥X, ((σ x : ↥X) : G) = z * x * z⁻¹ := fun x => by simp [σ]
  have hσN : ∀ x : ↥X, σ x ∈ CFSG.pCore 2 ↥X ↔ x ∈ CFSG.pCore 2 ↥X := by
    intro x
    have hc := Subgroup.characteristic_iff_map_eq.mp
      (CFSG.pCore_characteristic (p := 2) (G := ↥X)) σ
    constructor
    · intro h
      rw [← hc] at h
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
      have : y = x := σ.injective hyx
      exact this ▸ hy
    · intro h
      rw [← hc]
      exact Subgroup.mem_map.mpr ⟨x, h, rfl⟩
  have hker_le : α'.ker ≤ (α'.comp σ.toMonoidHom).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (hα'ker _).mpr ((hσN x).mpr ((hα'ker x).mp hx))
  let φ : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F :=
    α'.liftOfRightInverse (Function.surjInv hα's) (Function.rightInverse_surjInv hα's)
      ⟨α'.comp σ.toMonoidHom, hker_le⟩
  have hφ : ∀ x : ↥X, φ (α' x) = α' (σ x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply α' _ _ ⟨α'.comp σ.toMonoidHom, hker_le⟩ x
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := hα's y
    rw [hφ, hα'ker] at hy
    rw [(hα'ker x).mpr ((hσN x).mp hy)]
  have hσfix : ∀ x : ↥X, (x : G) * z = z * (x : G) → σ x = x := by
    intro x hx
    apply Subtype.ext
    rw [hσ]
    calc z * (x : G) * z⁻¹ = (x : G) * z * z⁻¹ := by rw [hx]
      _ = x := by group
  have hu : ∀ a : F, φ (sl2U a) = sl2U a := by
    intro a
    obtain ⟨x, hxH, hxa⟩ := Subgroup.mem_map.mp (hg _ (sl2U_mem_sl2UGroup a))
    have hx' : α' x = sl2U a := by
      rw [hα'x, hxa]
      group
    rw [← hx', hφ, hσfix x (hUz _ (Subgroup.mem_subgroupOf.mp hxH))]
  have hκ3 : α' ⟨k, hk⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨k, hk⟩ : ↥X) ^ 3 = 1 := Subtype.ext hk3
    rw [this, map_one]
  have hκ1 : α' ⟨k, hk⟩ ≠ 1 := fun h =>
    hkQ ((mem_blockQ_iff_pCore ⟨k, hk⟩).mpr ((hα'ker _).mp h))
  have hκ : φ (α' ⟨k, hk⟩) = α' ⟨k, hk⟩ := by
    rw [hφ, hσfix ⟨k, hk⟩ hkz]
  have hall := eq_id_of_fixes_sl2U φ hφinj hu hκ3 hκ1 hκ
  intro l hl
  have h1 : α' (σ ⟨l, hl⟩) = α' ⟨l, hl⟩ := by rw [← hφ]; exact hall _
  have h2 : σ ⟨l, hl⟩ * ⟨l, hl⟩⁻¹ ∈ CFSG.pCore 2 ↥X := by
    rw [← hα'ker, map_mul, map_inv, h1]
    group
  have h3 := (mem_blockQ_iff_pCore (σ ⟨l, hl⟩ * ⟨l, hl⟩⁻¹)).mpr h2
  simpa [hσ] using h3

end CFSG.Quasithin.S15223
