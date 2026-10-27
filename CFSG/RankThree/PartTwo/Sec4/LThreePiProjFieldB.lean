module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjFieldTwo
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjCaseI
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjField

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.KFacts
open Matrix

section Commuting

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem diagUnits_pow (a b c : Kˣ) (n : ℕ) :
    diagUnits a b c ^ n = diagUnits (a ^ n) (b ^ n) (c ^ n) := by
  induction n with
  | zero => simp [diagUnits_one]
  | succ n ih => rw [pow_succ, ih, diagUnits_mul, ← pow_succ, ← pow_succ, ← pow_succ]

theorem exists_commuting_mod_of_order_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) (hyZ : y ∉ zPi π 3 (p ^ f) K)
    (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K) :
    ∃ x ∈ slPi π 3 (p ^ f) K, x ^ 3 = 1 ∧ y * x * y⁻¹ * x⁻¹ ∈ StatedScalars (Fin 3) K ∧
      ∀ k : ℕ, (y ^ k)⁻¹ * x ∉ StatedScalars (Fin 3) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨y', ⟨z, hz, rfl⟩, h⟩ := rank3II_4_10_one hK hq hτ hτ1 hyH hyZ hy3
  have hzs := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  have hzc := commute_of_mem_statedScalars hzs
  have hpow : ∀ (x : GL (Fin 3) K) (k : ℕ), (y ^ k)⁻¹ * x ∈ StatedScalars (Fin 3) K →
      (y * z) * x = x * (y * z) := by
    intro x k hk
    obtain ⟨w, hw⟩ := hk
    have hx : x = y ^ k * GeneralLinearGroup.scalar (Fin 3) w := by rw [hw]; group
    have c1 : Commute (y * z) (y ^ k) :=
      Commute.mul_left (Commute.self_pow y k) (show Commute z (y ^ k) from (hzc (y ^ k)).symm)
    have c2 : Commute (y * z) (GeneralLinearGroup.scalar (Fin 3) w) :=
      CFSG.ClassicalGroups.UnitaryFlag.commute_scalar w (y * z)
    rw [hx]
    exact (Commute.mul_right c1 c2).eq
  have hyz : ∀ x : GL (Fin 3) K, y * x * y⁻¹ = (y * z) * x * (y * z)⁻¹ := by
    intro x
    calc y * x * y⁻¹ = y * (z * x * z⁻¹) * y⁻¹ := by rw [← hzc x]; group
      _ = (y * z) * x * (y * z)⁻¹ := by group
  rcases h with ⟨⟨g, hg, hD⟩, -, -⟩ | ⟨⟨g, hg, e₀, he₀, hD⟩, -, -⟩ |
    ⟨-, -, -, -, -, w, hwS, hwo, hwC, hwcent, -⟩
  ·
    have hyzD : y * z = g * diagTau hτ * g⁻¹ := eq_conj_of_inv_conj hD
    refine ⟨g * cycThree * g⁻¹, conj_mem_slPi hπ hg (cycThree_mem_slPi hπ), ?_, ?_, ?_⟩
    · rw [conj_pow, cycThree_pow_three, mul_one, mul_inv_cancel]
    ·
      have hcd := cycThree_pow_conj_diagTau hτ hτ0 1
      rw [pow_one, mul_one] at hcd
      have hdc : diagTau hτ * cycThree * (diagTau hτ)⁻¹ * cycThree⁻¹ ∈
          StatedScalars (Fin 3) K := by
        have h1 : diagTau hτ * cycThree * (diagTau hτ)⁻¹ * cycThree⁻¹ =
            (cycThree * diagTau hτ * cycThree⁻¹ * (diagTau hτ)⁻¹)⁻¹ := by group
        rw [h1, hcd, mul_inv_cancel_right]
        exact inv_mem ⟨_, rfl⟩
      rw [hyz, hyzD]
      have h2 : g * diagTau hτ * g⁻¹ * (g * cycThree * g⁻¹) * (g * diagTau hτ * g⁻¹)⁻¹ *
          (g * cycThree * g⁻¹)⁻¹ =
          g * (diagTau hτ * cycThree * (diagTau hτ)⁻¹ * cycThree⁻¹) * g⁻¹ := by group
      rw [h2]
      obtain ⟨u, hu⟩ := hdc
      rw [← hu, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u g).eq, mul_inv_cancel_right]
      exact ⟨u, rfl⟩
    · intro k hk
      have h1 := hpow _ k hk
      rw [hyzD] at h1
      have h2 : diagTau hτ * cycThree = cycThree * diagTau hτ := by
        have := congrArg (fun x => g⁻¹ * x * g) h1
        calc diagTau hτ * cycThree = g⁻¹ * (g * diagTau hτ * g⁻¹ * (g * cycThree * g⁻¹)) * g :=
              by group
          _ = g⁻¹ * (g * cycThree * g⁻¹ * (g * diagTau hτ * g⁻¹)) * g := this
          _ = cycThree * diagTau hτ := by group
      have hcd := cycThree_pow_conj_diagTau hτ hτ0 1
      rw [pow_one, mul_one] at hcd
      have h3 : cycThree * diagTau hτ * cycThree⁻¹ = diagTau hτ := by
        rw [← h2, mul_inv_cancel_right]
      rw [h3] at hcd
      have h4 := eq_one_of_scalar_mul_eq hcd.symm
      apply hτ1
      have h5 : (Units.mk0 τ hτ0) ^ 2 = 1 := h4
      have h6 : (Units.mk0 τ hτ0) ^ 3 = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one])
      have h7 : Units.mk0 τ hτ0 = 1 := by
        calc Units.mk0 τ hτ0 = (Units.mk0 τ hτ0) ^ 3 * ((Units.mk0 τ hτ0) ^ 2)⁻¹ := by group
          _ = 1 := by rw [h6, h5, inv_one, one_mul]
      rw [← Units.val_mk0 hτ0, h7, Units.val_one]
  ·
    have hyzD : y * z = g * diagE e₀ * g⁻¹ := eq_conj_of_inv_conj hD
    refine ⟨g * diagTau hτ * g⁻¹, conj_mem_slPi hπ hg (diagTau_mem_slPi hπ
      (fun h => by subst h; exact hq) hτ), ?_, ?_, ?_⟩
    · rw [conj_pow, diagTau_pow_three hτ, mul_one, mul_inv_cancel]
    · rw [hyz, hyzD]
      have h2 : g * diagE e₀ * g⁻¹ * (g * diagTau hτ * g⁻¹) * (g * diagE e₀ * g⁻¹)⁻¹ *
          (g * diagTau hτ * g⁻¹)⁻¹ =
          g * (diagE e₀ * diagTau hτ * (diagE e₀)⁻¹ * (diagTau hτ)⁻¹) * g⁻¹ := by group
      rw [h2, ← diagTau_mul_diagE hτ e₀]
      have : diagTau hτ * diagE e₀ * (diagE e₀)⁻¹ * (diagTau hτ)⁻¹ = 1 := by group
      rw [this, mul_one, mul_inv_cancel]
      exact one_mem _
    · intro k hk
      obtain ⟨u, hu⟩ := hk
      obtain ⟨v, hv⟩ := hzs
      have hy : y = g * diagE e₀ * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) v⁻¹ := by
        rw [← hyzD, ← hv, map_inv]
        group
      have hsc : ∀ (a : Kˣ) (A : GL (Fin 3) K),
          A * GeneralLinearGroup.scalar (Fin 3) a = GeneralLinearGroup.scalar (Fin 3) a * A :=
        fun a A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar a A).eq
      have hyk : y ^ k = g * diagE e₀ ^ k * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) (v⁻¹ ^ k) := by
        rw [hy, (Commute.mul_pow (hsc v⁻¹ (g * diagE e₀ * g⁻¹)) k), conj_pow, map_pow]
      have hx : g * diagTau hτ * g⁻¹ = y ^ k * GeneralLinearGroup.scalar (Fin 3) u := by
        rw [hu]; group
      rw [hyk] at hx
      have hx' : diagTau hτ = diagE e₀ ^ k * GeneralLinearGroup.scalar (Fin 3) (v⁻¹ ^ k * u) := by
        have := congrArg (fun x => g⁻¹ * x * g) hx
        rw [map_mul]
        calc diagTau hτ = g⁻¹ * (g * diagTau hτ * g⁻¹) * g := by group
          _ = g⁻¹ * (g * diagE e₀ ^ k * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) (v⁻¹ ^ k) *
              GeneralLinearGroup.scalar (Fin 3) u) * g := this
          _ = diagE e₀ ^ k * (g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) (v⁻¹ ^ k) *
              GeneralLinearGroup.scalar (Fin 3) u) * g) := by group
          _ = diagE e₀ ^ k * (GeneralLinearGroup.scalar (Fin 3) (v⁻¹ ^ k) *
              GeneralLinearGroup.scalar (Fin 3) u) := by
              rw [← map_mul, hsc _ g⁻¹, inv_mul_cancel_right]
      have h11 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 1 1) hx'
      have h22 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 2 2) hx'
      simp only [diagE, diagUnits_pow, Units.val_mul, coe_diagUnits, coe_diagTau_eq_diagonal,
        GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_mul_diagonal,
        diagonal_apply_eq] at h11 h22
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, one_pow, Units.val_one, one_mul] at h11 h22
      have h2 : τ ^ 2 = 1 := h11.trans h22.symm
      apply hτ1
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, h2, div_one]
  ·
    have hwcm : w ∈ centMod (slPi π 3 (p ^ f) K) (y * z) := by
      rw [hwcent]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    obtain ⟨-, s, hs, hws⟩ := mem_centMod_iff_scalar.mp hwcm
    refine ⟨w, hwS, ?_, ?_, ?_⟩
    · have := pow_orderOf_eq_one w
      rwa [hwo] at this
    ·
      rw [hyz]
      have h1 : (y * z) * w * (y * z)⁻¹ * w⁻¹ = (w * (y * z) * w⁻¹ * (y * z)⁻¹)⁻¹ := by group
      rw [h1, hws, mul_inv_cancel_right]
      exact inv_mem hs
    · intro k hk
      apply hwC
      refine Subgroup.mem_inf.mpr ⟨hwS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact (hpow w k hk).symm

end Commuting

section FieldThree

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem false_of_field_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {A : Subgroup G} (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {c : G} (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) {σ : G}
    (hσψ : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (frobGL ψ s))
    (hAeq : A = A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers σ)
    (hfixB : ∀ b ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)),
      ∃ y, IsPGLAtP e b y ∧ frobGL ψ y = y)
    (hAL3 : Nat.card (A ⊓ L : Subgroup G) = 3) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  obtain ⟨⟨b, hb⟩, hb1⟩ : ∃ x : (A ⊓ L : Subgroup G), x ≠ 1 := by
    have : Nontrivial (A ⊓ L : Subgroup G) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hAL3]; norm_num)
    exact exists_ne 1
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbA := (Subgroup.mem_inf.mp hb).1
  have hbL := (Subgroup.mem_inf.mp hb).2
  have hbo : orderOf b = 3 := orderOf_eq_prime (hA.1.2 b hbA) hb1'
  have hALb : A ⊓ L = Subgroup.zpowers b := by
    symm
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb)
      (by rw [hAL3, Nat.card_zpowers, hbo])
  have hBeq := inf_sup_centralizer_eq hA hLC hAc
  rw [hALb] at hBeq
  have hbB : b ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) :=
    Subgroup.mem_inf.mpr ⟨hbA, Subgroup.mem_sup_left hbL⟩
  obtain ⟨y, hy, hyψ⟩ := hfixB b hbB
  obtain ⟨S, hS, hScard⟩ := exists_fixedField hK hf hφ3
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  have hS₀ : PiField π p f₀ S := ⟨hK.prime, hf₀, hScard⟩
  have hq₀ : ModThree π (p ^ f₀) := modThree_of_cube (by rw [← pow_mul, mul_comm, ← hf]; exact hq)
  have hπ₀ : π = false → UnitaryFieldData p f₀ S := fun h => by subst h; exact hS₀.unitary
  have hq₀' : π = false → ModThree false (p ^ f₀) := fun h => by subst h; exact hq₀
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hS₀ hq₀
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hSψ : ∀ c, c ∈ S ↔ ψ c = c := fun c => (hS c).trans (fixed_iff_of_sq hφ3 hψ c).symm
  have hbC : b ∉ Subgroup.centralizer (L : Set G) := fun h =>
    hb1' (Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨hbL, h⟩))
  have hyZ : y ∉ zPi π 3 (p ^ f) K := not_mem_zPi_of_isPGLAtP hK hq hbC hy
  have hy3 := pow_three_mem_zPiP hK hq (hA.1.2 b hbA) hy
  have hyφ : frobGL φ y = y := by
    apply Units.ext
    have := congrArg Units.val hyψ
    rw [coe_frobGL] at this ⊢
    ext i k
    have h := congrFun (congrFun this i) k
    simp only [Matrix.map_apply] at h ⊢
    exact (fixed_iff_of_sq hφ3 hψ _).mp h
  obtain ⟨y₀, rfl⟩ := exists_subGL_eq hS hyφ
  have hy₀H : y₀ ∈ glPi π 3 (p ^ f₀) S := (subGL_mem_glPi_iff hK hf hφ hS hS₀ y₀).mp hy.1
  have hy₀Z : y₀ ∉ zPi π 3 (p ^ f₀) S := fun h => hyZ (subGL_mem_zPi hK hq hf hφ hS hS₀ hq₀ h)
  have hy₀3 : y₀ ^ 3 ∈ zPi π 3 (p ^ f₀) S := by
    rw [zPi_eq hπ₀ hq₀' hτ₀ hτ₀1]
    refine Subgroup.mem_inf.mpr ⟨pow_mem hy₀H 3, mem_statedScalars_of_subGL S ?_⟩
    rw [map_pow]
    exact mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hy3
  obtain ⟨x₀, hx₀S, hx₀3, hx₀c, hx₀n⟩ := exists_commuting_mod_of_order_three hS₀ hq₀ hy₀H hy₀Z hy₀3
  have hXS : subGL S x₀ ∈ slPi π 3 (p ^ f) K := (subGL_mem_slPi_iff hK hf hφ hS hS₀ x₀).mpr hx₀S
  set x : L := e.symm (projOf _ ⟨subGL S x₀, hXS⟩) with hx
  have hex : e x = projOf _ ⟨subGL S x₀, hXS⟩ := by rw [hx, MulEquiv.apply_symm_apply]
  have hxσ : σ * (x : G) = x * σ := by
    apply commute_of_slAct_eqP (e := e)
    rw [hex]
    apply Subtype.ext
    rw [hσψ, coe_projOf, frobGL_subGL hSψ x₀]
  have hxb : b * (x : G) = x * b := by
    apply commute_of_slAct_eqP (e := e)
    rw [hex, slAct_projOf_of_isPGLAtP hπ hy]
    apply Subtype.ext
    rw [coe_projOf, coe_projOf]
    change ProjGenLinGroup.mk (subGL S y₀ * subGL S x₀ * (subGL S y₀)⁻¹) =
      ProjGenLinGroup.mk (subGL S x₀)
    obtain ⟨u, hu⟩ := hx₀c
    have h1 : subGL S y₀ * subGL S x₀ * (subGL S y₀)⁻¹ =
        subGL S (GeneralLinearGroup.scalar (Fin 3) u) * subGL S x₀ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, hu]
      group
    rw [h1, map_mul, subGL_scalar, mk_eq_one_iff_mem_statedScalars.mpr ⟨_, rfl⟩, one_mul]
  have hxc : c * (x : G) = x * c := by
    have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
      have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
      exact this.2
    exact (Subgroup.mem_centralizer_iff.mp hcC x x.2).symm
  have hx3 : (x : G) ^ 3 = 1 := by
    have : x ^ 3 = 1 := by
      rw [hx, ← map_pow]
      have : (projOf _ ⟨subGL S x₀, hXS⟩ : projImage (slPi π 3 (p ^ f) K)) ^ 3 = 1 := by
        rw [← map_pow]
        have h1 : (⟨subGL S x₀, hXS⟩ : slPi π 3 (p ^ f) K) ^ 3 = 1 :=
          Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hx₀3, map_one, Subgroup.coe_one])
        rw [h1, map_one]
      rw [this, map_one]
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hxA : (x : G) ∈ A := by
    refine mem_of_maximal_of_commute hA hx3 fun a ha => ?_
    rw [hAeq, hBeq] at ha
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers σ ≤
        Subgroup.centralizer {(x : G)} := by
      refine sup_le (sup_le ?_ ?_) ?_ <;>
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      · exact hxb
      · exact hxc
      · exact hxσ
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hxb' : (x : G) ∈ Subgroup.zpowers b := hALb ▸ Subgroup.mem_inf.mpr ⟨hxA, x.2⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxb'
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  rw [zpow_emod_three hb3 k, ← Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num)),
    zpow_natCast] at hk
  set n := (k % 3).toNat
  apply hx₀n n
  have heb := coe_e_eq_mk_of_isPGLAtP hK hq hbL hy
  have hmk : ProjGenLinGroup.mk (subGL S x₀) = ProjGenLinGroup.mk (subGL S y₀ ^ n) := by
    have h1 : x = (⟨b, hbL⟩ : L) ^ n := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk.symm)
    have h2 := congrArg (fun l : L => ((e l : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K)) h1
    simp only [map_pow, Subgroup.coe_pow] at h2
    rw [heb, hex, coe_projOf] at h2
    rw [map_pow]
    exact h2
  have h3 : subGL S ((y₀ ^ n)⁻¹ * x₀) ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, map_pow, map_mul, map_inv, hmk,
      map_pow, inv_mul_cancel]
  exact mem_statedScalars_of_subGL S h3

end FieldThree

section FieldFour

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem alt412_field_four (hK : PiField π p f K) (hq : ModThree π (p ^ f)) [Fact p.Prime]
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] (hθ : aschbacherSolvableCore 3 L = ⊥)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) {σ : G} (hσA : σ ∈ A)
    (hσkind : InducesStdKind L σ .field) (hL : IsoLThreePi L p f) (hp2 : p = 2)
    (hπ1 : π = false) (hA81 : Nat.card A = 81) (hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Alt412 L A c := by
  classical
  subst hp2
  subst hπ1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : false = false → UnitaryFieldData 2 f K := fun _ => hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3K := hK.three_ne_zero hq
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hBeq := inf_sup_centralizer_eq hA hLC hAc
  have hcardB := card_inf_sup_centralizer hA hLC hc3 hAc
  set E' := Subgroup.zpowers c ⊔ (A ⊓ L) with hE'
  have hE'eq : E' = A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) := by rw [hBeq, sup_comm]
  have hE'27 : Nat.card E' = 27 := by rw [hE'eq, hcardB, hAL9]
  have hE'A : E' ≤ A := by rw [hE'eq]; exact inf_le_left
  have hE'LC : E' ≤ L ⊔ Subgroup.centralizer (L : Set G) := by rw [hE'eq]; exact inf_le_right
  have hE : ∀ a ∈ E', ∃ y, IsPGLAtP e a y := by
    intro a ha
    obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hE'LC ha)
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
    exact ⟨_, isPGLAtP_mul e (isPGLAtP_of_mem e hπ hl hs hse.symm)
      (isPGLAtP_of_mem_centralizer e hu)⟩
  have hEL : ∀ a ∈ A ⊓ L, ∃ y, IsPGLAtP e a y := fun a ha =>
    hE a (Subgroup.mem_sup_right ha)
  have hRcomm := range_pglHomP_comm (hK := hK) (hq := hq) (hA' := hE)
    (fun a ha b hb => hAcomm a (hE'A ha) b (hE'A hb))
  have hRexp := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hE) (fun a ha => hA3 a (hE'A ha))
  have hcardE := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (hA' := hE)
  have hE'C : E' ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c := by
    rw [hE'eq, inf_assoc, inf_eq_right.mpr (le_sup_right : Subgroup.centralizer (L : Set G) ≤
      L ⊔ Subgroup.centralizer (L : Set G)), hAc]
  rw [hE'C, Nat.card_zpowers, hc3, hE'27] at hcardE
  have hR9 : Nat.card (pglHomP hK hq E' hE).range = 9 := by omega
  have hbot : ∀ x ∈ A ⊓ L, x ≠ 1 → x ∉ Subgroup.centralizer (L : Set G) := fun x hx hx1 hxC =>
    hx1 (Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hxC⟩))
  have hn : 1 ≤ f := hK.one_le
  refine Or.inr (Or.inr (Or.inr ⟨hA81, σ, hσA, hσkind, f, hn, hL, hE'27, ?_⟩))
  rcases frame_or_heis h3K hτ hτ1 _ hRcomm hRexp (by omega) with ⟨b, hb, hd, -⟩ |
    ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  ·
    refine Or.inr ⟨isTypeCOn_of_frameP hK hq hθ hE (fun a ha => hA3 a (hE'A ha)) hR9 hb hd, ?_⟩
    exact hq
  ·
    have h1 : ∀ x ∈ A ⊓ L, x ≠ 1 → ∀ y, IsPGLAtP e x y → Type123 false (2 ^ f) K y 1 := by
      intro x hx hx1 y hy
      have hxE' : x ∈ E' := Subgroup.mem_sup_right hx
      rcases type13_of_heisP hK hq hRcomm hy₁ hy₂ hζ1 hζ hy.1
        (not_mem_zPi_of_isPGLAtP hK hq (hbot x hx hx1) hy)
        (pow_three_mem_zPiP hK hq (hA3 x (Subgroup.mem_inf.mp hx).1) hy)
        (mk_mem_range_pglHomP hxE' hy) with h | h
      · exact h
      · exact absurd (exists_inner_of_mem_supP hK hq
          (Subgroup.mem_sup_left (Subgroup.mem_inf.mp hx).2) hy) (not_inner_of_type3 hK hq hy.1 h)
    refine Or.inl ⟨fun x hx hx1 => ?_, ?_⟩
    · obtain ⟨y, hy⟩ := hEL x hx
      exact inducesTypeOn_of_isPGLAtP hK hq hθ hy (h1 x hx hx1 y hy)
    · have hrange : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
          (pglHomP hK hq E' hE).range →
            (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHomP hK hq (A ⊓ L) hEL).range := by
        intro y hy
        obtain ⟨⟨a, ha⟩, hay⟩ := hy
        obtain ⟨z, hz⟩ := hE a ha
        rw [pglHomP_apply ⟨a, ha⟩ hz] at hay
        rw [← hay]
        exact mem_range_inf_of_mem_sup hK hq hA hLC hEL (hE'A ha) (hE'LC ha) hz
      exact transitive_of_range_heis hK hq inf_le_right hAL9
        (fun a ha b hb => hAcomm a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1)
        (fun a ha => hA3 a (Subgroup.mem_inf.mp ha).1) hEL (hrange _ hy₁) (hrange _ hy₂) hζ1
        hζ h1

end FieldFour

end CFSG.RankThree.PartTwo.Sec4
