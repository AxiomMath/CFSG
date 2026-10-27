module

public import CFSG.Quasithin.H13.QRCBenderAmbient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylowUnique
public import CFSG.Quasithin.Background.B1MoreNineC

public section

namespace CFSG.Quasithin.H13.BenL2

open Subgroup CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.GorensteinWalter
  CFSG.Glauberman.Dickson CFSG.Quasithin.H13.QRC
open scoped MatrixGroups

theorem cube_root {F : Type} [Field F] {ω a : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (ha : a ^ 3 = 1) : a = 1 ∨ a = ω ∨ a = ω ^ 2 := by
  have h3 : 1 + ω + ω ^ 2 = 0 := by
    have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  have h : (a - 1) * (a - ω) * (a - ω ^ 2) = 0 := by
    linear_combination ha - hω3 + (-a ^ 2 + a * ω) * h3
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem pow_three_mem_of_mul {G : Type*} [Group G] {U : Subgroup G} {u d : G} (hu : u ∈ U)
    (hd : d ∈ normalizer (U : Set G)) (h : (u * d) ^ 3 ∈ U) : d ^ 3 ∈ U := by
  have h1 : d * u * d⁻¹ ∈ U := (mem_normalizer_iff.mp hd u).mp hu
  have h2 : d * (d * u * d⁻¹) * d⁻¹ ∈ U := (mem_normalizer_iff.mp hd _).mp h1
  have e : d ^ 3 = (u * (d * u * d⁻¹) * (d * (d * u * d⁻¹) * d⁻¹))⁻¹ * (u * d) ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
    simp [pow_succ, mul_assoc]
  rw [e]
  exact U.mul_mem (U.inv_mem (U.mul_mem (U.mul_mem hu h1) h2)) h

section SL2

variable {F : Type} [Field F] [CharP F 2]

theorem borel_cube {ω : Fˣ} (hω : orderOf ω = 3) {x : SL(2, F)} (hx : x ∈ sl2Borel F)
    (hx3 : x ^ 3 ∈ sl2UpperUnipotentSubgroup F) :
    ∃ k < 3, x * (splitTorusSLHom F ω ^ k)⁻¹ ∈ sl2UpperUnipotentSubgroup F := by
  set U := sl2UpperUnipotentSubgroup F with hU
  have hDN : (splitTorusSLHom F).range ≤ normalizer (U : Set SL(2, F)) := by
    rw [hU, sl2_normalizer_upperUnipotent, ← sl2_upperUnipotent_sup_torus]
    exact le_sup_right
  rw [← sl2_upperUnipotent_sup_torus] at hx
  obtain ⟨u, hu, d, ⟨a, rfl⟩, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hDN).mp hx
  have hd3 : splitTorusSLHom F a ^ 3 ∈ U := pow_three_mem_of_mul hu (hDN ⟨a, rfl⟩) hx3
  have hd1 : splitTorusSLHom F (a ^ 3) = 1 := by
    have hmem : splitTorusSLHom F (a ^ 3) ∈ U ⊓ (splitTorusSLHom F).range :=
      ⟨by rw [map_pow]; exact hd3, ⟨a ^ 3, rfl⟩⟩
    rw [hU, sl2_upperUnipotent_inf_torus] at hmem
    exact hmem
  have ha3 : a ^ 3 = 1 := splitTorusSLHom_injective (hd1.trans (map_one _).symm)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  have hω3' : (ω : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hω1' : (ω : F) ≠ 1 := fun h => hω1 (Units.ext h)
  have ha3' : (a : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ha3, Units.val_one]
  have hk : ∃ k < 3, a = ω ^ k := by
    rcases cube_root hω3' hω1' ha3' with h | h | h
    · exact ⟨0, by norm_num, Units.ext (by simpa using h)⟩
    · exact ⟨1, by norm_num, Units.ext (by simpa using h)⟩
    · exact ⟨2, by norm_num, Units.ext (by simpa using h)⟩
  obtain ⟨k, hk3, rfl⟩ := hk
  refine ⟨k, hk3, ?_⟩
  rw [← map_pow, mul_inv_cancel_right]
  exact hu

end SL2

structure L2Facts (X : Type*) [Group X] (q : ℕ) : Prop where
  ti : ∀ S S' : Sylow 2 X, ∀ g ∈ (S : Subgroup X), g ≠ 1 → g ∈ (S' : Subgroup X) → S = S'
  card : ∀ S : Sylow 2 X, Nat.card (S : Subgroup X) = q
  cube : ∀ S : Sylow 2 X, ∃ c ∈ normalizer ((S : Subgroup X) : Set X),
    ∀ x ∈ normalizer ((S : Subgroup X) : Set X), x ^ 3 ∈ (S : Subgroup X) →
      ∃ k < 3, x * (c ^ k)⁻¹ ∈ (S : Subgroup X)

theorem L2Facts.of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] {q : ℕ}
    (e : X ≃* Y) (h : L2Facts Y q) : L2Facts X q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Se : Sylow 2 X → Sylow 2 Y := fun S => S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : ∀ (S : Sylow 2 X) (x : X), x ∈ (S : Subgroup X) ↔
      e x ∈ ((Se S : Sylow 2 Y) : Subgroup Y) := by
    intro S x
    show x ∈ (S : Subgroup X) ↔ e x ∈ (S : Subgroup X).map e.toMonoidHom
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [e.injective hyx] at hy
  have hnorm : ∀ (S : Sylow 2 X) (x : X), x ∈ normalizer ((S : Subgroup X) : Set X) ↔
      e x ∈ normalizer (((Se S : Sylow 2 Y) : Subgroup Y) : Set Y) := by
    intro S x
    rw [mem_normalizer_iff, mem_normalizer_iff]
    constructor
    · intro hx y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← hmap, ← map_inv, ← map_mul, ← map_mul, ← hmap]
      exact hx z
    · intro hx z
      rw [hmap, hmap, map_mul, map_mul, map_inv]
      exact hx (e z)
  refine ⟨fun S S' g hg hg1 hg' => ?_, fun S => ?_, fun S => ?_⟩
  · have h1 := h.ti _ _ (e g) ((hmap S g).mp hg) (fun h1 => hg1 (e.injective
      (h1.trans (map_one e).symm))) ((hmap S' g).mp hg')
    ext x
    rw [hmap S x, hmap S' x, h1]
  · rw [← h.card (Se S)]
    exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
  · obtain ⟨c, hc, hcx⟩ := h.cube (Se S)
    refine ⟨e.symm c, (hnorm S _).mpr (by rwa [MulEquiv.apply_symm_apply]), fun x hx hx3 => ?_⟩
    obtain ⟨k, hk, hxk⟩ := hcx (e x) ((hnorm S x).mp hx)
      (by rw [← map_pow]; exact (hmap S _).mp hx3)
    refine ⟨k, hk, (hmap S _).mpr ?_⟩
    rwa [map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply]

section PSL2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem exists_orderOf_eq_three {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Even n) :
    ∃ ω : Fˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_units]
  obtain ⟨m, rfl⟩ := hn
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h3 : 3 ∣ Nat.card Fˣ := by
    rw [hcard, hF, ← two_mul, pow_mul]
    norm_num
    omega
  exact exists_prime_orderOf_dvd_card' 3 h3

theorem l2Facts_psl2 {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Even n) :
    L2Facts (PSL2 F) (2 ^ n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₀ : Sylow 2 (PSL2 F) := psl2UpperUnipotentSylow F hF with hU₀
  have hU₀c : (U₀ : Subgroup (PSL2 F)) = psl2UpperUnipotentSubgroup F :=
    psl2UpperUnipotentSylow_coe F hF
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_three hF hn
  set c₀ : PSL2 F := sl2EquivPSL2 (splitTorusSLHom F ω) with hc₀
  have hB : psl2Borel F = (sl2Borel F).map (sl2EquivPSL2 (F := F)).toMonoidHom :=
    sl2EquivPSL2_borel.symm
  have hUm : psl2UpperUnipotentSubgroup F =
      (sl2UpperUnipotentSubgroup F).map (sl2EquivPSL2 (F := F)).toMonoidHom :=
    sl2EquivPSL2_upperUnipotent.symm
  have hN₀ : normalizer ((U₀ : Subgroup (PSL2 F)) : Set (PSL2 F)) = psl2Borel F := by
    rw [hU₀c]
    exact psl2UpperUnipotent_normalizer_eq_borel F
  have hcube₀ : ∀ x ∈ normalizer ((U₀ : Subgroup (PSL2 F)) : Set (PSL2 F)),
      x ^ 3 ∈ (U₀ : Subgroup (PSL2 F)) → ∃ k < 3, x * (c₀ ^ k)⁻¹ ∈ (U₀ : Subgroup (PSL2 F)) := by
    intro x hx hx3
    rw [hN₀, hB] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [hU₀c, hUm] at hx3 ⊢
    have hx'3 : x' ^ 3 ∈ sl2UpperUnipotentSubgroup F := by
      obtain ⟨y, hy, hyx⟩ := hx3
      rw [← map_pow] at hyx
      rwa [(sl2EquivPSL2 (F := F)).injective hyx] at hy
    obtain ⟨k, hk, hxk⟩ := borel_cube hω hx' hx'3
    refine ⟨k, hk, ⟨_, hxk, ?_⟩⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, map_pow, hc₀]
  have hc₀N : c₀ ∈ normalizer ((U₀ : Subgroup (PSL2 F)) : Set (PSL2 F)) := by
    rw [hN₀, hB]
    refine ⟨splitTorusSLHom F ω, ?_, rfl⟩
    rw [← sl2_upperUnipotent_sup_torus]
    exact mem_sup_right ⟨ω, rfl⟩
  refine ⟨fun S S' g hg hg1 hg' => psl2_sylow_eq_of_mem_nontrivial F hF S S' g hg hg1 hg',
    fun S => ?_, fun S => ?_⟩
  · obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (PSL2 F) U₀ S
    rw [← ha, ← Nat.card_congr (Sylow.equivSMul U₀ a).toEquiv, hU₀c,
      psl2UpperUnipotentSubgroup_card, hF]
  · obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (PSL2 F) U₀ S
    have hmem : ∀ y : PSL2 F, y ∈ (S : Subgroup (PSL2 F)) ↔
        a⁻¹ * y * a ∈ (U₀ : Subgroup (PSL2 F)) := by
      intro y
      rw [← ha, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [MulAut.smul_def]
    have hnorm : ∀ y : PSL2 F, y ∈ normalizer ((S : Subgroup (PSL2 F)) : Set (PSL2 F)) ↔
        a⁻¹ * y * a ∈ normalizer ((U₀ : Subgroup (PSL2 F)) : Set (PSL2 F)) := by
      intro y
      rw [mem_normalizer_iff, mem_normalizer_iff]
      constructor
      · intro hy z
        have h1 := hy (a * z * a⁻¹)
        rw [hmem, hmem] at h1
        simpa [mul_assoc] using h1
      · intro hy z
        have h1 := hy (a⁻¹ * z * a)
        rw [hmem, hmem]
        simpa [mul_assoc] using h1
    refine ⟨a * c₀ * a⁻¹, (hnorm _).mpr (by simpa [mul_assoc] using hc₀N), fun x hx hx3 => ?_⟩
    obtain ⟨k, hk, hxk⟩ := hcube₀ (a⁻¹ * x * a) ((hnorm x).mp hx)
      (by
        have h1 := (hmem (x ^ 3)).mp hx3
        have e : a⁻¹ * x ^ 3 * a = (a⁻¹ * x * a) ^ 3 := by
          rw [pow_three', pow_three']
          group
        rwa [e] at h1)
    refine ⟨k, hk, (hmem _).mpr ?_⟩
    have e : a⁻¹ * (x * ((a * c₀ * a⁻¹) ^ k)⁻¹) * a = a⁻¹ * x * a * (c₀ ^ k)⁻¹ := by
      rw [conj_pow]
      group
    rw [e]
    exact hxk

end PSL2

section Ambient

variable {Γ : Type*} [Group Γ]

open CFSG.QuasithinUnique (IsSylowTwoOf)

structure BorelL2 (K : Subgroup Γ) (q : ℕ) : Prop where
  ti : ∀ U U' : Subgroup Γ, IsSylowTwoOf U K → IsSylowTwoOf U' K → U ⊓ U' ≠ ⊥ → U = U'
  card : ∀ U : Subgroup Γ, IsSylowTwoOf U K → Nat.card U = q
  cube : ∀ U : Subgroup Γ, IsSylowTwoOf U K → ∃ c ∈ K, c ∈ normalizer (U : Set Γ) ∧
    ∀ x ∈ K, x ∈ normalizer (U : Set Γ) → x ^ 3 ∈ U → ∃ k < 3, x * (c ^ k)⁻¹ ∈ U

noncomputable def toSylow [Fact (Nat.Prime 2)] {K U : Subgroup Γ} (hU : IsSylowTwoOf U K) :
    Sylow 2 ↥K :=
  IsPGroup.toSylow (hU.2.1.comap_of_injective K.subtype K.subtype_injective) hU.2.2

theorem mem_toSylow [Fact (Nat.Prime 2)] {K U : Subgroup Γ} (hU : IsSylowTwoOf U K) (x : ↥K) :
    x ∈ (toSylow hU : Subgroup ↥K) ↔ (x : Γ) ∈ U :=
  Iff.rfl

theorem borelL2_of_l2Facts {K : Subgroup Γ} {q : ℕ} (h : L2Facts ↥K q) : BorelL2 K q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ∀ {U : Subgroup Γ} (hU : IsSylowTwoOf U K) (x : ↥K),
      x ∈ normalizer (((toSylow hU : Sylow 2 ↥K) : Subgroup ↥K) : Set ↥K) ↔
        (x : Γ) ∈ normalizer (U : Set Γ) := by
    intro U hU x
    rw [mem_normalizer_iff, mem_normalizer_iff]
    constructor
    · intro hx y
      by_cases hyK : y ∈ K
      · have h1 := hx ⟨y, hyK⟩
        rw [mem_toSylow, mem_toSylow] at h1
        exact h1
      · constructor
        · intro hy
          exact absurd (hU.1 hy) hyK
        · intro hy
          have h2 : (x : Γ) * y * (x : Γ)⁻¹ ∈ K := hU.1 hy
          have h3 : y ∈ K := by
            have := K.mul_mem (K.mul_mem (K.inv_mem x.2) h2) x.2
            simpa [mul_assoc] using this
          exact absurd h3 hyK
    · intro hx y
      rw [mem_toSylow, mem_toSylow]
      exact hx y
  refine ⟨fun U U' hU hU' hne => ?_, fun U hU => ?_, fun U hU => ?_⟩
  · obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hgK : (g : Γ) ∈ K := hU.1 (g.2.1)
    have h1 := h.ti (toSylow hU) (toSylow hU') ⟨g, hgK⟩ ((mem_toSylow hU _).mpr g.2.1)
      (fun h2 => hg1 (Subtype.ext (show (g : Γ) = 1 from
        congrArg (fun y : ↥K => (y : Γ)) h2))) ((mem_toSylow hU' _).mpr g.2.2)
    ext x
    constructor
    · intro hx
      have h2 := (mem_toSylow hU ⟨x, hU.1 hx⟩).mpr hx
      rw [h1] at h2
      exact (mem_toSylow hU' _).mp h2
    · intro hx
      have h2 := (mem_toSylow hU' ⟨x, hU'.1 hx⟩).mpr hx
      rw [← h1] at h2
      exact (mem_toSylow hU _).mp h2
  · rw [← h.card (toSylow hU)]
    refine Nat.card_congr ⟨fun x => ⟨⟨x, hU.1 x.2⟩, (mem_toSylow hU _).mpr x.2⟩,
      fun x => ⟨x.1, (mem_toSylow hU _).mp x.2⟩, fun _ => rfl, fun _ => rfl⟩
  · obtain ⟨c, hc, hcx⟩ := h.cube (toSylow hU)
    refine ⟨c, c.2, (hnorm hU c).mp hc, fun x hxK hxN hx3 => ?_⟩
    obtain ⟨k, hk, hxk⟩ := hcx ⟨x, hxK⟩ ((hnorm hU _).mpr hxN)
      ((mem_toSylow hU _).mpr (by simpa using hx3))
    refine ⟨k, hk, ?_⟩
    have h1 := (mem_toSylow hU _).mp hxk
    simpa using h1

end Ambient

end CFSG.Quasithin.H13.BenL2
