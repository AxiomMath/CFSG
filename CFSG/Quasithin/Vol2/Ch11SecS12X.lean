module

public import CFSG.Quasithin.Vol2.Ch11SecS12P
public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open hiding StatedSL
open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem sixteen_le_card_of_pow_five {A : Type} [Group A] [Finite A] (hA : IsPGroup 2 A)
    {σ : MulAut A} (h5 : σ ^ 5 = 1) (h1 : σ ≠ 1) : 16 ≤ Nat.card A := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 5 ↥(Subgroup.zpowers σ) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime h5 h1
  have hcong := hP.card_modEq_card_fixedPoints A
  let Fx : Subgroup A :=
    { carrier := {a | σ a = a}
      mul_mem' := fun {a b} (ha : σ a = a) (hb : σ b = b) => by
        show σ (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one σ
      inv_mem' := fun {a} (ha : σ a = a) => by
        show σ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hfix : MulAction.fixedPoints ↥(Subgroup.zpowers σ) A = (Fx : Set A) := by
    ext a
    constructor
    · intro h
      exact h ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro (ha : σ a = a) g
      have hs : σ ∈ MulAction.stabilizer (MulAut A) a := ha
      have hg : (g : MulAut A) ∈ MulAction.stabilizer (MulAut A) a :=
        Subgroup.zpowers_le.mpr hs g.2
      exact hg
  have hcF : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers σ) A) = Nat.card Fx := by
    rw [hfix]
    rfl
  rw [hcF] at hcong
  obtain ⟨m, hm⟩ := hA.exists_card_eq
  obtain ⟨c, hc⟩ := (hA.to_subgroup Fx).exists_card_eq
  have hlt : Nat.card Fx < Nat.card A := by
    have hne : Fx ≠ ⊤ := by
      intro htop
      apply h1
      ext a
      have : a ∈ Fx := htop ▸ Subgroup.mem_top a
      exact this
    have h := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
    rwa [Subgroup.card_top] at h
  rw [hm, hc] at hlt hcong
  have hcm : c < m := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  rw [hm]
  by_contra hlt16
  have hm4 : m < 4 := by
    by_contra h4
    exact hlt16 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (not_lt.mp h4)))
  interval_cases m <;> interval_cases c <;> simp_all [Nat.ModEq]

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_centralizer {L₁ X₁ : Subgroup G} (hX₁ : IsPGroup 3 X₁)
    (hXL : X₁ ≤ Subgroup.normalizer (L₁ : Set G))
    (hcomm : ∀ x ∈ X₁, ∀ l ∈ L₁, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁) {l : G} (hl : l ∈ L₁) :
    ∃ b ∈ pCoreOf 2 L₁, l * b ∈ Subgroup.centralizer (X₁ : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 L₁) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁).exists_card_eq
    rw [hk]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hXB : X₁ ≤ Subgroup.normalizer (pCoreOf 2 L₁ : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁ (hXL hx)
  have hO : (pCoreOf 2 L₁).subgroupOf L₁ |>.Normal := normal_pCoreOf_subgroupOf L₁
  obtain ⟨b, hb, hfix⟩ := H13.Ch4.exists_mul_fixed_of_isPGroup hX₁ hB hXB (a := l) fun x hx => by
    have h1 := hcomm x hx l hl
    have hlO : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ ∈ pCoreOf 2 L₁ := by
      have := hO.conj_mem ⟨_, CFSG.LieType.BorelTits.pCoreOf_le 2 L₁ h1⟩
        (Subgroup.mem_subgroupOf.mpr h1) ⟨l, hl⟩⁻¹
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have e : l⁻¹ * (x * l * x⁻¹) = l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ := by group
    rw [e]
    exact hlO
  refine ⟨b, hb, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have := hfix x hx
  calc x * (l * b) = x * (l * b) * x⁻¹ * x := by group
    _ = l * b * x := by rw [this]

theorem exists_pow_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    {L₁ H E : Subgroup G} (α₀ : ↥L₁ →* ↥(StatedSL 2 F)) (hα₀ : Function.Surjective α₀)
    (hker : α₀.ker = (pCoreOf 2 L₁).subgroupOf L₁) (hHL : H ≤ L₁)
    (hcov : ∀ l : ↥L₁, ∃ h : ↥H, α₀ (Subgroup.inclusion hHL h) = α₀ l)
    (hHE : H ≤ Subgroup.normalizer (E : Set G)) {y : G} (hyH : y ∈ H) (hy3 : y ^ 3 = 1)
    (hyE : ∃ e ∈ E, y * e * y⁻¹ ≠ e) :
    ∃ σ : MulAut ↥E, σ ^ 5 = 1 ∧ σ ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥H →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hHE)
  have hρ : ∀ (h : ↥H) (e : ↥E), ((ρ h e : ↥E) : G) = (h : G) * e * (h : G)⁻¹ := fun _ _ => rfl
  let f : ↥H →* ↥(StatedSL 2 F) := α₀.comp (Subgroup.inclusion hHL)
  have hf : Function.Surjective f := fun s => by
    obtain ⟨l, rfl⟩ := hα₀ s
    obtain ⟨h, hh⟩ := hcov l
    exact ⟨h, hh⟩
  have hsimp := isSimpleGroup_statedSL hF
  have hN : (ρ.ker.map f).Normal := Subgroup.Normal.map ρ.normal_ker f hf
  have hk : ρ.ker ≤ f.ker := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map f) with hb | ht
    · intro n hn
      have : f n ∈ ρ.ker.map f := ⟨n, hn, rfl⟩
      rwa [hb, Subgroup.mem_bot] at this
    · exfalso
      obtain ⟨n, hn, hny⟩ : f ⟨y, hyH⟩ ∈ ρ.ker.map f := ht ▸ Subgroup.mem_top _
      have ho : n⁻¹ * ⟨y, hyH⟩ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hny, inv_mul_cancel]
      have ho' : ((n⁻¹ * ⟨y, hyH⟩ : ↥H) : G) ∈ pCoreOf 2 L₁ := by
        have : Subgroup.inclusion hHL (n⁻¹ * ⟨y, hyH⟩) ∈ α₀.ker := ho
        rw [hker, Subgroup.mem_subgroupOf] at this
        exact this
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁) ⟨_, ho'⟩
      have hk' : (n⁻¹ * ⟨y, hyH⟩ : ↥H) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        simpa using congrArg Subtype.val hk
      have hρy : ρ ⟨y, hyH⟩ = ρ (n⁻¹ * ⟨y, hyH⟩) := by
        rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul]
      have h2 : ρ ⟨y, hyH⟩ ^ 2 ^ k = 1 := by rw [hρy, ← map_pow, hk', map_one]
      have h3 : ρ ⟨y, hyH⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨y, hyH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
        rw [this, map_one]
      have hone : ρ ⟨y, hyH⟩ = 1 := by
        have h1 := orderOf_dvd_of_pow_eq_one h2
        have h1' := orderOf_dvd_of_pow_eq_one h3
        have : orderOf (ρ ⟨y, hyH⟩) = 1 := Nat.eq_one_of_dvd_coprimes
          (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) h1 h1'
        exact orderOf_eq_one_iff.mp this
      obtain ⟨e, he, hye⟩ := hyE
      apply hye
      have := congrArg (fun σ : MulAut ↥E => ((σ ⟨e, he⟩ : ↥E) : G)) hone
      simpa [hρ] using this
  let φ : ↥ρ.range →* ↥(StatedSL 2 F) :=
    ρ.rangeRestrict.liftOfRightInverseAux (Function.surjInv ρ.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _) f (by rwa [MonoidHom.ker_rangeRestrict])
  have hφ : Function.Surjective φ := by
    intro s
    obtain ⟨h, rfl⟩ := hf s
    exact ⟨ρ.rangeRestrict h, MonoidHom.liftOfRightInverseAux_comp_apply _ _ _ _ _ h⟩
  have h60 : Nat.card ↥(StatedSL 2 F) ∣ Nat.card ↥ρ.range := Subgroup.card_dvd_of_surjective hφ
  rw [Nat.card_congr (SecD.statedSLEquiv' 2 F).toEquiv, C11P9A.card_SL2_four hF] at h60
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := ↥ρ.range) 5 (dvd_trans (by norm_num) h60)
  refine ⟨(σ : MulAut ↥E), ?_, ?_⟩
  · have h := pow_orderOf_eq_one σ
    rw [hσ] at h
    simpa using congrArg Subtype.val h
  · intro h1
    have : σ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hσ
    norm_num at hσ

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
