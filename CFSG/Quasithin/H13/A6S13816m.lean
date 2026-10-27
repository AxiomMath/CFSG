module

public import CFSG.Quasithin.H13.A6S13816l
public import CFSG.Quasithin.H13.A6S13816f
public import CFSG.Quasithin.H13.A6S13813f
public import CFSG.Quasithin.Background.C126RFCases
public import CFSG.Quasithin.H13.A6Set14
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

namespace S14.PlusData

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}
  {Lp : Subgroup G} (P : PlusData S Lp)
include P

theorem exists_c012_cube : ∃ c : ↥(Subgroup.normalizer (V : Set G)), (c : G) ∈ Lp ∧
    S.frame.ρ c = swap 0 1 * swap 1 2 ∧ (c : G) ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcL, hc⟩ := P.three (swap 0 1 * swap 1 2) (by decide +kernel)
  have h3 : ((c ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 Lp :=
    P.mem_pCoreOf_of_K4 (by simpa using Lp.pow_mem hcL 3)
      (by rw [map_pow, hc, c012_facts.2.2]; decide)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Lp ⟨_, h3⟩
  have hk' : ((c : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨c ^ 4 ^ k, by simpa using Lp.pow_mem hcL (4 ^ k), ?_, ?_⟩
  · rw [map_pow, hc, pow_four_pow_of_cube c012_facts.2.2]
  · have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    simp only [SubgroupClass.coe_pow]
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hk', one_pow]

theorem decomp {c : ↥(Subgroup.normalizer (V : Set G))} (hc : (c : G) ∈ Lp)
    (hρ : S.frame.ρ c = swap 0 1 * swap 1 2) {x : G} (hx : x ∈ Lp) :
    x ∈ pCoreOf 2 Lp ∨ (c : G) * c * x ∈ pCoreOf 2 Lp ∨ (c : G) * x ∈ pCoreOf 2 Lp := by
  obtain ⟨xn, rfl⟩ : ∃ xn : ↥(Subgroup.normalizer (V : Set G)), (xn : G) = x :=
    ⟨⟨x, P.le_NV hx⟩, rfl⟩
  obtain ⟨h4, h5, hs⟩ := P.rho hx
  rcases (a4At_all _ h4 h5 hs).1 with h | h | h
  · exact Or.inl (P.mem_pCoreOf_of_K4 hx h)
  · exact Or.inr (Or.inl (P.mem_pCoreOf_of_K4 (x := c * c * xn) (Lp.mul_mem (Lp.mul_mem hc hc) hx)
      (by rw [map_mul, map_mul, hρ]; exact h)))
  · exact Or.inr (Or.inr (P.mem_pCoreOf_of_K4 (x := c * xn) (Lp.mul_mem hc hx)
      (by rw [map_mul, hρ]; exact h)))

omit P in
theorem not_mem {c : ↥(Subgroup.normalizer (V : Set G))}
    (hρ : S.frame.ρ c = swap 0 1 * swap 1 2) (hc3 : (c : G) ^ 3 = 1) : (c : G) ∉ pCoreOf 2 Lp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Lp ⟨_, h⟩
  have hk' : (c : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : c = 1 := Subtype.ext (L32Comm.eq_one_of_pow_of_cube hk' hc3)
  rw [h1, map_one] at hρ
  exact absurd hρ.symm (by decide)

end S14.PlusData

namespace L2Hat

variable {Q : Type} [Group Q]

theorem exists_comm_eq [Finite Q] {U : Subgroup Q} {c : Q} (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U)
    (hfix : ∀ u ∈ U, c * u * c⁻¹ = u → u = 1) {u : Q} (hu : u ∈ U) :
    ∃ s ∈ U, c * s * c⁻¹ * s⁻¹ = u := by
  let f : ↥U → ↥U := fun s => ⟨c * s * c⁻¹ * (s : Q)⁻¹, U.mul_mem (hcU s s.2) (U.inv_mem s.2)⟩
  have hf : Function.Injective f := by
    intro s s' h
    have h1 : c * (s : Q) * c⁻¹ * (s : Q)⁻¹ = c * s' * c⁻¹ * (s' : Q)⁻¹ := congrArg Subtype.val h
    have h2 : c * ((s' : Q)⁻¹ * s) * c⁻¹ = (s' : Q)⁻¹ * s :=
      calc c * ((s' : Q)⁻¹ * s) * c⁻¹ = (c * (s' : Q)⁻¹ * c⁻¹) * (c * s * c⁻¹ * (s : Q)⁻¹) * s := by
            group
        _ = (c * (s' : Q)⁻¹ * c⁻¹) * (c * s' * c⁻¹ * (s' : Q)⁻¹) * s := by rw [h1]
        _ = (s' : Q)⁻¹ * s := by group
    have h3 := hfix _ (U.mul_mem (U.inv_mem s'.2) s.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3).symm
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
  exact ⟨s, s.2, congrArg Subtype.val hs⟩

theorem le_of_fpf [Finite Q] {U L₀ : Subgroup Q} {c : Q} (hc : c ∈ L₀)
    (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U) (hfix : ∀ u ∈ U, c * u * c⁻¹ = u → u = 1)
    (hUL : U ≤ Subgroup.normalizer (L₀ : Set Q)) : U ≤ L₀ := by
  intro u hu
  obtain ⟨s, hs, rfl⟩ := exists_comm_eq hcU hfix hu
  have h1 : s * c⁻¹ * s⁻¹ ∈ L₀ := (Subgroup.mem_normalizer_iff.mp (hUL hs) c⁻¹).mp (L₀.inv_mem hc)
  have e : c * s * c⁻¹ * s⁻¹ = c * (s * c⁻¹ * s⁻¹) := by group
  rw [e]
  exact L₀.mul_mem hc h1

theorem exists_pow_mul {U : Subgroup Q} {x x' : Q} (hxN : x ∈ Subgroup.normalizer (U : Set Q))
    (hx3 : x ^ 3 = 1) (h : x' * x⁻¹ ∈ U ∨ x' * x ∈ U) : ∃ e : ℕ, ∃ q ∈ U, x' = x ^ e * q := by
  rcases h with h | h
  · refine ⟨1, x⁻¹ * (x' * x⁻¹) * x, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp h
    simpa using this
  · refine ⟨2, x * (x' * x) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN _).mp h, ?_⟩
    calc x' = x ^ 3 * x' := by rw [hx3, one_mul]
      _ = x ^ 2 * (x * (x' * x) * x⁻¹) := by group

theorem map_conj_map_conj (A : Subgroup Q) (y y' : Q) :
    (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y').toMonoidHom =
      A.map (MulAut.conj (y' * y)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_inv_map_conj (A : Subgroup Q) (y : Q) :
    (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y⁻¹).toMonoidHom = A := by
  rw [map_conj_map_conj, inv_mul_cancel]
  ext x
  simp

@[expose] def pairStab (A B : Subgroup Q) : Subgroup Q where
  carrier := {y | (A.map (MulAut.conj y).toMonoidHom = A ∧ B.map (MulAut.conj y).toMonoidHom = B) ∨
    (A.map (MulAut.conj y).toMonoidHom = B ∧ B.map (MulAut.conj y).toMonoidHom = A)}
  one_mem' := by
    left
    constructor <;> (ext x; simp)
  mul_mem' := by
    rintro y y' (⟨h1, h2⟩ | ⟨h1, h2⟩) (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
    · left
      rw [← map_conj_map_conj, ← map_conj_map_conj, h1', h2', h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← map_conj_map_conj, ← map_conj_map_conj, h1', h2', h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← map_conj_map_conj, ← map_conj_map_conj, h1', h2', h1, h2]
      exact ⟨rfl, rfl⟩
    · left
      rw [← map_conj_map_conj, ← map_conj_map_conj, h1', h2', h1, h2]
      exact ⟨rfl, rfl⟩
  inv_mem' := by
    rintro y (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      constructor
      · conv_lhs => rw [← h1]
        exact map_conj_inv_map_conj A y
      · conv_lhs => rw [← h2]
        exact map_conj_inv_map_conj B y
    · right
      constructor
      · conv_lhs => rw [← h2]
        exact map_conj_inv_map_conj B y
      · conv_lhs => rw [← h1]
        exact map_conj_inv_map_conj A y

theorem map_map_conj {R : Type} [Group R] (ψ : Q →* R) (A : Subgroup Q) (y : Q) :
    (A.map ψ).map (MulAut.conj (ψ y)).toMonoidHom = (A.map (MulAut.conj y).toMonoidHom).map ψ := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem split_of [Finite Q] {K₁ X N U₁ U₂ : Subgroup Q} {t c : Q}
    (hcomm' : ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hinf : K₁ ⊓ K₁.map (MulAut.conj t).toMonoidHom = ⊥)
    (hX' : X ≤ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom)
    (htX : t ∈ Subgroup.normalizer (X : Set Q))
    (hXN : X ≤ Subgroup.normalizer (N : Set Q)) (hN : IsPGroup 2 N)
    (hc : c ∈ X) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hdec : ∀ x ∈ X, x ∈ N ∨ c * c * x ∈ N ∨ c * x ∈ N) (hU₁ : IsSylowTwoOf U₁ K₁)
    (hU₂ : IsSylowTwoOf U₂ (K₁.map (MulAut.conj t).toMonoidHom))
    (hU₁X : U₁ ≤ Subgroup.normalizer (X : Set Q)) (hU₂X : U₂ ≤ Subgroup.normalizer (X : Set Q)) :
    ∃ a ∈ K₁, ∃ b ∈ K₁.map (MulAut.conj t).toMonoidHom, c = a * b ∧ a ^ 3 = 1 ∧ a ≠ 1 ∧
      b ^ 3 = 1 ∧ b ≠ 1 ∧ a ∈ Subgroup.normalizer (U₁ : Set Q) ∧
      b ∈ Subgroup.normalizer (U₂ : Set Q) := by
  obtain ⟨htwo, htwo', a, haK, b, hbK, hcab, ha3, ha1, hb3, hb1⟩ :=
    L2Comm.pair_split hcomm' hinf hX' htX hXN hN hc hc3 hc1 hdec
  have hcomm := L32Comm.mul_comm_of_commutator_eq_bot hcomm'
  have hcomm2 : ∀ x ∈ K₁.map (MulAut.conj t).toMonoidHom, ∀ y ∈ K₁, x * y = y * x :=
    fun x hx y hy => (hcomm y hy x hx).symm
  have haN := L2Comm.mem_normalizer_of_pair hcomm htwo hU₁ hU₁X hc haK hbK hcab ha3
  have hcba : c = b * a := by rw [hcab]; exact hcomm a haK b hbK
  have hbN := L2Comm.mem_normalizer_of_pair hcomm2 htwo' hU₂ hU₂X hc hbK haK hcba hb3
  exact ⟨a, haK, b, hbK, hcab, ha3, ha1, hb3, hb1, haN, hbN⟩

theorem mem_normalizer_subgroupOf {K U : Subgroup Q} {x : Q} (hxK : x ∈ K)
    (hxN : x ∈ Subgroup.normalizer (U : Set Q)) :
    (⟨x, hxK⟩ : ↥K) ∈ Subgroup.normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hxN h

end L2Hat

namespace L2Hat

variable {G : Type} [Group G] [Finite G]

theorem bar_data {Q : Type} [Group Q] {H ℓ : Subgroup G} (π : ↥H →* Q)
    (hπ : ∀ x : ↥H, π x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) (hℓH : ℓ ≤ H) {c : G} (hc : c ∈ ℓ)
    (hc3 : c ^ 3 = 1) (hcO : c ∉ pCoreOf 2 ℓ)
    (hdec : ∀ x ∈ ℓ, x ∈ pCoreOf 2 ℓ ∨ c * c * x ∈ pCoreOf 2 ℓ ∨ c * x ∈ pCoreOf 2 ℓ) :
    π ⟨c, hℓH hc⟩ ^ 3 = 1 ∧ π ⟨c, hℓH hc⟩ ≠ 1 ∧
      IsPGroup 2 (((pCoreOf 2 ℓ).subgroupOf H).map π) ∧
      ∀ x ∈ (ℓ.subgroupOf H).map π, x ∈ ((pCoreOf 2 ℓ).subgroupOf H).map π ∨
        π ⟨c, hℓH hc⟩ * π ⟨c, hℓH hc⟩ * x ∈ ((pCoreOf 2 ℓ).subgroupOf H).map π ∨
        π ⟨c, hℓH hc⟩ * x ∈ ((pCoreOf 2 ℓ).subgroupOf H).map π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcH3 : (⟨c, hℓH hc⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simp [hc3])
  refine ⟨by rw [← map_pow, hcH3, map_one], fun h => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hπ _ h
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hcO (by rw [L32Comm.eq_one_of_pow_of_cube hk' hc3]; exact Subgroup.one_mem _)
  · have h1 : IsPGroup 2 ((pCoreOf 2 ℓ).subgroupOf H) :=
      (pCoreOf_isPGroup 2 ℓ).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((pCoreOf_le 2 ℓ).trans hℓH)).symm
    exact h1.map π
  · rintro _ ⟨y, hy, rfl⟩
    rcases hdec y (Subgroup.mem_subgroupOf.mp hy) with h | h | h
    · exact Or.inl ⟨y, Subgroup.mem_subgroupOf.mpr h, rfl⟩
    · refine Or.inr (Or.inl ⟨⟨c, hℓH hc⟩ * ⟨c, hℓH hc⟩ * y, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩)
      · simpa using h
      · rw [map_mul, map_mul]
    · refine Or.inr (Or.inr ⟨⟨c, hℓH hc⟩ * y, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩)
      · simpa using h
      · rw [map_mul]

end L2Hat

namespace L2Hat

variable {Q : Type} [Group Q]

theorem conj_mul_of_comm {a b u : Q} (hbu : b * u = u * b) :
    (a * b) * u * (a * b)⁻¹ = a * u * a⁻¹ :=
  calc (a * b) * u * (a * b)⁻¹ = a * (b * u) * b⁻¹ * a⁻¹ := by group
    _ = a * (u * b) * b⁻¹ * a⁻¹ := by rw [hbu]
    _ = a * u * a⁻¹ := by group

theorem eq_one_of_conj_eq_in {K U : Subgroup Q} {n : ℕ} (hK : IsPSL 2 2 n ↥K)
    (hU : IsSylowTwoOf U K) {x : Q} (hxK : x ∈ K) (hxN : x ∈ Subgroup.normalizer (U : Set Q))
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {u : Q} (hu : u ∈ U) (hxu : x * u * x⁻¹ = u) : u = 1 := by
  have h := L2Borel.eq_one_of_conj_eq hK (isSylowTwoOf_top_subgroupOf hU)
    (mem_normalizer_subgroupOf hxK hxN) (x := ⟨x, hxK⟩) (Subtype.ext (by simpa using hx3))
    (fun h => hx1 (congrArg Subtype.val h)) (u := ⟨u, hU.1 hu⟩) (Subgroup.mem_subgroupOf.mpr hu)
    (Subtype.ext (by simpa using hxu))
  exact congrArg Subtype.val h

theorem mul_mem_or_in {K U : Subgroup Q} {n : ℕ} (hK : IsPSL 2 2 n ↥K) (hU : IsSylowTwoOf U K)
    {x x' : Q} (hxK : x ∈ K) (hx'K : x' ∈ K) (hxN : x ∈ Subgroup.normalizer (U : Set Q))
    (hx'N : x' ∈ Subgroup.normalizer (U : Set Q)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hx'3 : x' ^ 3 = 1) (hx'1 : x' ≠ 1) : x' * x⁻¹ ∈ U ∨ x' * x ∈ U := by
  rcases L2Borel.mul_mem_or hK (isSylowTwoOf_top_subgroupOf hU) (mem_normalizer_subgroupOf hxK hxN)
    (mem_normalizer_subgroupOf hx'K hx'N) (Subtype.ext (by simpa using hx3))
    (fun h => hx1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hx'3))
    (fun h => hx'1 (congrArg Subtype.val h)) with h | h
  · exact Or.inl (Subgroup.mem_subgroupOf.mp h)
  · exact Or.inr (Subgroup.mem_subgroupOf.mp h)

end L2Hat

@[expose] def Case13816L2HatTensor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    IsHatA6 L → ∀ H ∈ S.Hz, ∀ K ∈ cComp H, conjClosure K T ≠ K → H = (K ⊔ T) ⊔ S.L1 →
      ((∃ n, IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) ∨ IsAlt 5 (↥K ⧸ CFSG.pCore 2 ↥K)) →
      ∀ Wm : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)), Wm ≠ ⊤ →
        (∀ h ∈ S.KSt H H, ∀ w ∈ Wm, h w ∈ Wm) →
        (∀ Y : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)), Wm ≤ Y →
          (∀ h ∈ S.KSt H H, ∀ y ∈ Y, h y ∈ Y) → Y = Wm ∨ Y = ⊤) →
        (∀ w, (∀ k ∈ S.KSt H K, k w * w⁻¹ ∈ Wm) → w ∈ Wm) → False

theorem case13816L2Hat_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h122 : CFSG.Quasithin.Lemma122A)
    (hTen : Case13816L2HatTensor) : Case13816L2Hat := by
  intro G _ _ T L V S hS hhat H hH K hK hne hHeq hL2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hℓK : S.L1 ≤ conjClosure K T :=
    S.L1_le_conjClosure' h37 h38 h122 hH hK hne (L2Case.three_dvd_card hL2)
  have hℓH : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hF := (hS.hF H hH).toHypF91
  have hFU : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure _ _
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hN₀ : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπ2 : ∀ x : ↥H, π x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    have hmem := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hmem⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  set Kb := (K.subgroupOf H).map π with hKb
  set Tb := (T.subgroupOf H).map π with hTb
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := modO2Image_mem_cComp hK
  have hTbs : IsSylowTwoOf Tb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTsyl) π hπs
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  obtain ⟨-, hL2'⟩ := h38 _ hQ Kb hKbc
  rcases hL2' Tb hTbs with ⟨hnorm, -, -⟩ | ⟨t, htT, -, hconj, -, hcomm', hinf, hTN, -⟩
  · exact hne (L32Case.conjClosure_eq_of_normal hKH hTH (normal_of_normal_map_of_mem_cComp
      (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H) (subgroupOf_mem_cComp hK) hnorm))
  set K₂ := Kb.map (MulAut.conj t).toMonoidHom with hK₂
  set X := (S.L1.subgroupOf H).map π with hX
  have hXle : X ≤ Kb ⊔ K₂ := by
    have hcc : (conjClosure (K.subgroupOf H) (T.subgroupOf H)).map H.subtype =
        conjClosure K T := by
      rw [A3.map_conjClosure, Subgroup.map_subgroupOf_eq_of_le hKH,
        Subgroup.map_subgroupOf_eq_of_le hTH]
    have hcl : conjClosure (K.subgroupOf H) (T.subgroupOf H) ≤ (Kb ⊔ K₂).comap π := by
      refine conjClosure_le fun s hs k hk => ?_
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      have hs' : π s ∈ Tb := Subgroup.mem_map_of_mem π hs
      have hk' : π k ∈ Kb := Subgroup.mem_map_of_mem π hk
      have hmem : Kb.map (MulAut.conj (π s)).toMonoidHom ∈ conjSubgroupsBy Tb Kb :=
        ⟨π s, hs', rfl⟩
      rw [hconj] at hmem
      have hsk : π s * π k * (π s)⁻¹ ∈ Kb.map (MulAut.conj (π s)).toMonoidHom :=
        ⟨π k, hk', by simp [MulAut.conj_apply]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · rw [h] at hsk
        exact Subgroup.mem_sup_left hsk
      · rw [h] at hsk
        exact Subgroup.mem_sup_right hsk
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ conjClosure K T := hℓK (Subgroup.mem_subgroupOf.mp hy)
    rw [← hcc] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hcl hz
  have hcomm : ∀ x ∈ Kb, ∀ y ∈ K₂, x * y = y * x :=
    L32Comm.mul_comm_of_commutator_eq_bot hcomm'
  have hcomm2 : ∀ x ∈ K₂, ∀ y ∈ Kb, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hK₂c : K₂ ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := A38.cComp_conj hKbc
  have hU₁ : IsSylowTwoOf (Tb ⊓ Kb) Kb :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKbc) hTbs
  have hU₂ : IsSylowTwoOf (Tb ⊓ K₂) K₂ :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₂c) hTbs
  have hK0N1 : Kb ⊔ K₂ ≤ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le Subgroup.le_normalizer fun x hx => L2Comm.mem_normalizer_of_comm hcomm le_rfl hx
  have hK0N2 : Kb ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le (fun x hx => L2Comm.mem_normalizer_of_comm hcomm2 le_rfl hx) Subgroup.le_normalizer
  have hP := S14.plusData_l1plus S (S.hatL1Plus hhat)
  obtain ⟨c₀, hc₀, hc₀3, hc₀O, hdec₀⟩ := l0_decomp hhat
  obtain ⟨c₁, hc₁, hρc₁, hc₁3⟩ := hP.exists_c012_cube
  have hL0H : l0 L ≤ H := S.l0_le_L1.trans hℓH
  have hLpH : l1plus T L V ≤ H := hP.le_L1.trans hℓH
  have hTl0 : T ≤ Subgroup.normalizer (l0 L : Set G) :=
    A5.le_normalizer_oTwoRes_of_le_normalizer (S.T_le_NL.trans normalizer_L_le_o2Z)
  set X₀ := ((l0 L).subgroupOf H).map π with hX₀
  set X₁ := ((l1plus T L V).subgroupOf H).map π with hX₁
  have hX₀le : X₀ ≤ Kb ⊔ K₂ := (Subgroup.map_mono (f := π)
    (show (l0 L).subgroupOf H ≤ S.L1.subgroupOf H from fun x hx => S.l0_le_L1 hx)).trans hXle
  have hX₁le : X₁ ≤ Kb ⊔ K₂ := (Subgroup.map_mono (f := π)
    (show (l1plus T L V).subgroupOf H ≤ S.L1.subgroupOf H from fun x hx => hP.le_L1 hx)).trans
      hXle
  have hTX₀ : Tb ≤ Subgroup.normalizer (X₀ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map hTl0 π
  have hTX₁ : Tb ≤ Subgroup.normalizer (X₁ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map hP.T_le π
  obtain ⟨hcb₀3, hcb₀1, hNp₀, hdecb₀⟩ := L2Hat.bar_data π hπ2 hL0H hc₀ hc₀3 hc₀O hdec₀
  obtain ⟨hcb₁3, hcb₁1, hNp₁, hdecb₁⟩ := L2Hat.bar_data π hπ2 hLpH hc₁ hc₁3
    (S14.PlusData.not_mem hρc₁ hc₁3) (fun x hx => hP.decomp hc₁ hρc₁ hx)
  obtain ⟨a, haK, b, hbK, hcab, ha3, ha1, hb3, hb1, haN, hbN⟩ := L2Hat.split_of hcomm' hinf
    hX₀le (hTX₀ htT) (L32Case.map_le_normalizer_map (le_normalizer_pCoreOf 2 (l0 L)) π) hNp₀
    ⟨⟨c₀, hL0H hc₀⟩, Subgroup.mem_subgroupOf.mpr hc₀, rfl⟩ hcb₀3 hcb₀1 hdecb₀ hU₁ hU₂
    (inf_le_left.trans hTX₀) (inf_le_left.trans hTX₀)
  obtain ⟨a', ha'K, b', hb'K, hcab', ha'3, ha'1, hb'3, hb'1, ha'N, hb'N⟩ := L2Hat.split_of hcomm'
    hinf hX₁le (hTX₁ htT) (L32Case.map_le_normalizer_map (le_normalizer_pCoreOf 2 _) π) hNp₁
    ⟨⟨c₁, hLpH hc₁⟩, Subgroup.mem_subgroupOf.mpr hc₁, rfl⟩ hcb₁3 hcb₁1 hdecb₁ hU₁ hU₂
    (inf_le_left.trans hTX₁) (inf_le_left.trans hTX₁)
  obtain ⟨e₁⟩ := modO2_mulEquiv hK
  obtain ⟨n, hKbP⟩ : ∃ n, IsPSL 2 2 n ↥Kb := by
    rcases hL2 with ⟨n, h⟩ | h
    · exact ⟨n, isPSL_congr e₁ h⟩
    · exact ⟨2, isPSL_congr e₁ (C126.isPSL_two_two_two_of_alternating_five _ h)⟩
  have hK₂P : IsPSL 2 2 n ↥K₂ := isPSL_congr (A38.conjEquiv t Kb) hKbP
  obtain ⟨e, q, hq, ha'eq⟩ := L2Hat.exists_pow_mul haN ha3
    (L2Hat.mul_mem_or_in hKbP hU₁ haK ha'K haN ha'N ha3 ha1 ha'3 ha'1)
  obtain ⟨f, q', hq', hb'eq⟩ := L2Hat.exists_pow_mul hbN hb3
    (L2Hat.mul_mem_or_in hK₂P hU₂ hbK hb'K hbN hb'N hb3 hb1 hb'3 hb'1)
  have hc₀X : π ⟨c₀, hL0H hc₀⟩ ∈ X₀ := ⟨⟨c₀, hL0H hc₀⟩, Subgroup.mem_subgroupOf.mpr hc₀, rfl⟩
  have hU₁L : Tb ⊓ Kb ≤ X₀ := by
    refine L2Hat.le_of_fpf hc₀X (fun u hu => ?_) (fun u hu h => ?_) (inf_le_left.trans hTX₀)
    · rw [hcab, L2Hat.conj_mul_of_comm (hcomm u (hU₁.1 hu) b hbK).symm]
      exact (Subgroup.mem_normalizer_iff.mp haN u).mp hu
    · rw [hcab, L2Hat.conj_mul_of_comm (hcomm u (hU₁.1 hu) b hbK).symm] at h
      exact L2Hat.eq_one_of_conj_eq_in hKbP hU₁ haK haN ha3 ha1 hu h
  have hU₂L : Tb ⊓ K₂ ≤ X₀ := by
    have hcba : π ⟨c₀, hL0H hc₀⟩ = b * a := by rw [hcab]; exact hcomm a haK b hbK
    refine L2Hat.le_of_fpf hc₀X (fun u hu => ?_) (fun u hu h => ?_) (inf_le_left.trans hTX₀)
    · rw [hcba, L2Hat.conj_mul_of_comm (hcomm2 u (hU₂.1 hu) a haK).symm]
      exact (Subgroup.mem_normalizer_iff.mp hbN u).mp hu
    · rw [hcba, L2Hat.conj_mul_of_comm (hcomm2 u (hU₂.1 hu) a haK).symm] at h
      exact L2Hat.eq_one_of_conj_eq_in hK₂P hU₂ hbK hbN hb3 hb1 hu h
  have hker : CFSG.pCore 2 ↥H ≤ (actH hV₁ hIH).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, A6Tv.actH_eq_one_iff hV₁ hIHN hIH x]
    intro u hu
    have hx' : (x : G) ∈ pCoreOf 2 H := (mem_pCore_iff x).1 hx
    have h1 := (fsuV1 T V).inv_mem (hF.commutator_conjClosure_le u hu x hx')
    have e : (u * (x : G) * u⁻¹ * (x : G)⁻¹)⁻¹ = (x : G) * u * (x : G)⁻¹ * u⁻¹ := by group
    rwa [e] at h1
  set ψ := QuotientGroup.lift (CFSG.pCore 2 ↥H) (actH hV₁ hIH) hker with hψ
  have hψπ : ∀ x : ↥H, ψ (π x) = actH hV₁ hIH x := fun x => rfl
  have hHs' : S.KSt H H = (H.subgroupOf H).map (actH hV₁ hIH) :=
    autOn_tilde_eq_map_actH hV₁ hIH le_rfl
  have hψHs : ∀ y, ψ y ∈ S.KSt H H := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    rw [hHs', hψπ]
    exact ⟨x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hHsψ : ∀ h ∈ S.KSt H H, ∃ y, ψ y = h := by
    intro h hh
    rw [hHs'] at hh
    obtain ⟨x, -, rfl⟩ := hh
    exact ⟨π x, rfl⟩
  have hKSt : S.KSt H K = Kb.map ψ := by
    show autOn _ _ = _
    rw [autOn_tilde_eq_map_actH hV₁ hIH hKH, hKb, Subgroup.map_map]
    rfl
  have hfixZ : ∀ x : ↥H, (x : G) ∈ Subgroup.centralizer (V : Set G) →
      ∀ z ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3, actH hV₁ hIH x z = z := by
    intro x hx z hz
    obtain ⟨⟨g, hgN⟩, hgU, hgz⟩ := exists_mk_of_mem_tilde z
    have hgU' : g ∈ conjClosure S.V3 H := hgU
    have hz' : z = modMk hIHN g hgU' := Subtype.ext hgz.symm
    have hg3 : g ∈ S.V3 := by
      rw [← modMk_mem_subM_iff hIHN hF.V₁_le_Vp hgU', ← hz']
      exact hz
    have hxg : (x : G) * g * (x : G)⁻¹ = g := by
      have := Subgroup.mem_centralizer_iff.mp hx g (S.V3_le_V hg3)
      rw [← this, mul_inv_cancel_right]
    rw [hz', actH_modMk hV₁ hIHN hIH x hgU']
    exact A6Tv.modMk_congr hIHN _ _ hxg
  have hX₀fix : ∀ y ∈ X₀, ∀ z ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3, ψ y z = z := by
    rintro _ ⟨x, hx, rfl⟩ z hz
    rw [hψπ]
    exact hfixZ x (S.o2Z_le_centralizer (oTwoRes_le _ (Subgroup.mem_subgroupOf.mp hx))) z hz
  have hZ4 := S.card_tilde_V3 hS hH
  have hbot : (⊥ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) ≠ ⊤ := by
    intro h
    have h1 : subM (fsuV1 T V) (conjClosure S.V3 H) S.V3 ≤ ⊥ := h ▸ le_top
    rw [le_bot_iff] at h1
    rw [h1, Subgroup.card_bot] at hZ4
    exact absurd hZ4 (by norm_num)
  have hfin : Finite (Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    Finite.of_injective (fun W : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)) =>
      (W : Set ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))) SetLike.coe_injective
  obtain ⟨Wm, ⟨hWmne, hWmi⟩, hWmmax⟩ := Set.exists_max_image
    {W : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)) | W ≠ ⊤ ∧
      ∀ h ∈ S.KSt H H, ∀ w ∈ W, h w ∈ W}
    (fun W => Nat.card W) (Set.toFinite _) ⟨⊥, hbot, fun h _ w hw => by
      rw [Subgroup.mem_bot] at hw ⊢
      rw [hw, map_one]⟩
  have hmax : ∀ Y : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)), Wm ≤ Y →
      (∀ h ∈ S.KSt H H, ∀ y ∈ Y, h y ∈ Y) → Y = Wm ∨ Y = ⊤ := by
    intro Y hWY hY
    by_cases hYt : Y = ⊤
    · exact Or.inr hYt
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hWY (hWmmax Y ⟨hYt, hY⟩)).symm
  by_cases hcases : ∀ w, (∀ k ∈ S.KSt H K, k w * w⁻¹ ∈ Wm) → w ∈ Wm
  · exact hTen G T L V S hS hhat H hH K hK hne hHeq hL2 Wm hWmne hWmi hmax hcases
  push Not at hcases
  obtain ⟨w₀, hw₀, hw₀'⟩ := hcases
  have hKbne : Kb ≠ K₂ := fun h => ha1 (by
    have : a ∈ Kb ⊓ K₂ := ⟨haK, h ▸ haK⟩
    rw [hinf] at this
    exact this)
  have hTstab : ∀ s ∈ Tb, s ∈ L2Hat.pairStab Kb K₂ := by
    intro s hs
    have hA : Kb.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy Tb Kb := ⟨s, hs, rfl⟩
    have hB : K₂.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy Tb Kb :=
      ⟨s * t, Tb.mul_mem hs htT, L2Hat.map_conj_map_conj Kb t s⟩
    rw [hconj] at hA hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
    have hinj : Kb.map (MulAut.conj s).toMonoidHom ≠ K₂.map (MulAut.conj s).toMonoidHom := by
      intro h
      apply hKbne
      calc Kb = (Kb.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom :=
            (L2Hat.map_conj_inv_map_conj Kb s).symm
        _ = (K₂.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by rw [h]
        _ = K₂ := L2Hat.map_conj_inv_map_conj K₂ s
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact absurd (hA.trans hB.symm) hinj
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hB⟩
    · exact absurd (hA.trans hB.symm) hinj
  have hstab : ∀ y : ↥H ⧸ CFSG.pCore 2 ↥H, y ∈ L2Hat.pairStab Kb K₂ := by
    have hK0stab : ∀ y ∈ Kb ⊔ K₂, y ∈ L2Hat.pairStab Kb K₂ := fun y hy =>
      Or.inl ⟨A38.map_conj_eq_iff.mpr (hK0N1 hy), A38.map_conj_eq_iff.mpr (hK0N2 hy)⟩
    have hle : (K ⊔ T) ⊔ S.L1 ≤ ((L2Hat.pairStab Kb K₂).comap π).map H.subtype := by
      refine sup_le (sup_le (fun x hx => ?_) (fun x hx => ?_)) (fun x hx => ?_)
      · exact ⟨⟨x, hKH hx⟩, hK0stab _ (Subgroup.mem_sup_left ⟨⟨x, hKH hx⟩, hx, rfl⟩), rfl⟩
      · exact ⟨⟨x, hTH hx⟩, hTstab _ ⟨⟨x, hTH hx⟩, hx, rfl⟩, rfl⟩
      · exact ⟨⟨x, hℓH hx⟩, hK0stab _ (hXle ⟨⟨x, hℓH hx⟩, hx, rfl⟩), rfl⟩
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    have hx : (x : G) ∈ (K ⊔ T) ⊔ S.L1 := by
      rw [← hHeq]
      exact x.2
    obtain ⟨x', hx', hxx'⟩ := hle hx
    have : x' = x := Subtype.ext hxx'
    rw [← this]
    exact hx'
  have hperm : ∀ h ∈ S.KSt H H, ((K₂.map ψ).map (MulAut.conj h).toMonoidHom = K₂.map ψ ∧
      (Kb.map ψ).map (MulAut.conj h).toMonoidHom = Kb.map ψ) ∨
      ((K₂.map ψ).map (MulAut.conj h).toMonoidHom = Kb.map ψ ∧
        (Kb.map ψ).map (MulAut.conj h).toMonoidHom = K₂.map ψ) := by
    intro h hh
    obtain ⟨y, rfl⟩ := hHsψ h hh
    rw [L2Hat.map_map_conj, L2Hat.map_map_conj]
    rcases hstab y with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [h1, h2]
      exact ⟨rfl, rfl⟩
  have hZ : ¬ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3 ≤ Wm := by
    intro hle
    apply hWmne
    rw [eq_top_iff, ← iSup_actH_subM_eq_top hV₁ hIHN hIH hF.V₁_le_Vp]
    refine iSup₂_le fun m hm => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hWmi m (by rw [hHs']; exact hm) w (hle hw)
  have hZWm : ∀ z ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3, z ∈ Wm → z = 1 := by
    let W : Subgroup G :=
      { carrier := {g | g ∈ S.V3 ∧ ∃ hg : g ∈ conjClosure S.V3 H, modMk hIHN g hg ∈ Wm}
        one_mem' := ⟨S.V3.one_mem, (conjClosure S.V3 H).one_mem, by
          rw [modMk_one]
          exact Wm.one_mem⟩
        mul_mem' := fun {x y} ⟨hx3, hx, hxW⟩ ⟨hy3, hy, hyW⟩ => ⟨S.V3.mul_mem hx3 hy3,
          (conjClosure S.V3 H).mul_mem hx hy, by
            rw [modMk_mul hIHN hx hy]
            exact Wm.mul_mem hxW hyW⟩
        inv_mem' := fun {x} ⟨hx3, hx, hxW⟩ => ⟨S.V3.inv_mem hx3, (conjClosure S.V3 H).inv_mem hx,
          by
            rw [modMk_inv hIHN hx]
            exact Wm.inv_mem hxW⟩ }
    have hV1W : fsuV1 T V ≤ W := fun v hv => ⟨hF.V₁_le_Vp hv,
      le_conjClosure _ _ (hF.V₁_le_Vp hv), by
        rw [(A6Tv.modMk_eq_one_iff' hIHN _).2 hv]
        exact Wm.one_mem⟩
    have hW3 : W ≤ S.V3 := fun g hg => hg.1
    have hWN : l1plus T L V ⊔ T ≤ Subgroup.normalizer (W : Set G) := by
      refine A5.le_normalizer_of_forall_conj_mem fun x hx g hg => ?_
      obtain ⟨hg3, hgU, hgW⟩ := hg
      have hxH : x ∈ H := sup_le hLpH hTH hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp (sup_le hP.le_NV3 S.T_le_normalizer_V3 hx) g).mp
        hg3, (Subgroup.mem_normalizer_iff.mp (hIH hxH) g).mp hgU, ?_⟩
      have h1 := hWmi _ (hψHs (π ⟨x, hxH⟩)) _ hgW
      rw [hψπ, actH_modMk hV₁ hIHN hIH ⟨x, hxH⟩ hgU] at h1
      exact h1
    have hmk : ∀ z ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3, ∃ g,
        ∃ hgU : g ∈ conjClosure S.V3 H, g ∈ S.V3 ∧ z = modMk hIHN g hgU := by
      intro z hz
      obtain ⟨⟨g, hgN⟩, hgU, hgz⟩ := exists_mk_of_mem_tilde z
      have hgU' : g ∈ conjClosure S.V3 H := hgU
      have hz' : z = modMk hIHN g hgU' := Subtype.ext hgz.symm
      refine ⟨g, hgU', ?_, hz'⟩
      rw [← modMk_mem_subM_iff hIHN hF.V₁_le_Vp hgU', ← hz']
      exact hz
    rcases hP.irred.2.2.2 W hV1W hW3 hWN with h | h
    · intro z hz hzW
      obtain ⟨g, hgU, hg3, rfl⟩ := hmk z hz
      have hgW : g ∈ W := ⟨hg3, hgU, hzW⟩
      rw [h] at hgW
      exact (A6Tv.modMk_eq_one_iff' hIHN hgU).2 hgW
    · exfalso
      apply hZ
      intro z hz
      obtain ⟨g, hgU, hg3, rfl⟩ := hmk z hz
      rw [← h] at hg3
      obtain ⟨-, hgU'', hgW⟩ := hg3
      exact hgW
  have hc₁H : (c₁ : G) ∈ H := hLpH hc₁
  have hcψ : ((ψ b) ^ f * ψ q') * ((ψ a) ^ e * ψ q) = actH hV₁ hIH ⟨c₁, hc₁H⟩ := by
    rw [← hψπ, hcab', ha'eq, hb'eq, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact hcomm2 _ (K₂.mul_mem (K₂.pow_mem hbK f) (hU₂.1 hq')) _
      (Kb.mul_mem (Kb.pow_mem haK e) (hU₁.1 hq))
  have hab : ∀ z ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3, (ψ b * ψ a) z = z := by
    intro z hz
    rw [← map_mul, ← hcomm a haK b hbK, ← hcab]
    exact hX₀fix _ hc₀X z hz
  refine L2Wt.false_of_sum (X₁ := K₂.map ψ) (X₂ := Kb.map ψ) (Hs := S.KSt H H) ?_ ?_ ?_ hperm
    hWmi hmax hZ hZWm (a := ψ b) (b := ψ a) (u := ψ q') (u' := ψ q) ⟨b, hbK, rfl⟩
    ⟨a, haK, rfl⟩ ⟨q', hU₂.1 hq', rfl⟩ ⟨q, hU₁.1 hq, rfl⟩ hab
    (fun z hz => hX₀fix _ (hU₂L hq') z hz) (fun z hz => hX₀fix _ (hU₁L hq) z hz) f e
    (fun z hz h => S.fix_tilde_V3_c012 hS hH hV₁ hIH hρc₁ hc₁H hz (hcψ ▸ h))
    (fun z hz => hcψ ▸ (S.stab_tilde_V3 hS hH hV₁ hIH (x := ⟨c₁, hc₁H⟩)
      (Subgroup.mem_sup_left (hP.le_L1 hc₁)) z).2 hz)
    (w₀ := w₀) (fun k hk => hw₀ k (by rw [hKSt]; exact hk)) hw₀'
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm2 x hx y hy]
  · rintro _ ⟨y, -, rfl⟩
    exact hψHs y
  · rintro _ ⟨y, -, rfl⟩
    exact hψHs y

end CFSG.Quasithin.H13.A6
