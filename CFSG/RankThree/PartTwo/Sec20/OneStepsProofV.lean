module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.Quasithin.EmptyFaithful.SBc8Transfer
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open Matrix CFSG.LocalAnalysis.ComponentInitial

theorem sl3_eq_one_of_sub_mulVec_mem_line {F : Type*} [Field F] [CharP F 2]
    (A : SpecialLinearGroup (Fin 3) F) (hA3 : A ^ 3 = 1)
    (h : ∀ x : Fin 3 → F, (x - (A : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 1 = 0 ∧
      (x - (A : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = 0) : A = 1 := by
  set B : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hB
  have hrow : ∀ i j : Fin 3, i ≠ 0 → B i j = if i = j then 1 else 0 := by
    intro i j hi
    have hx := h (Pi.single j 1)
    rw [mulVec_single_one] at hx
    have hi' : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
    rcases hi' with rfl | rfl
    · have := hx.1
      rw [Pi.sub_apply, col_apply, sub_eq_zero] at this
      rw [← this, Pi.single_apply]
    · have := hx.2
      rw [Pi.sub_apply, col_apply, sub_eq_zero] at this
      rw [← this, Pi.single_apply]
  have h10 := hrow 1 0 (by decide)
  have h11 := hrow 1 1 (by decide)
  have h12 := hrow 1 2 (by decide)
  have h20 := hrow 2 0 (by decide)
  have h21 := hrow 2 1 (by decide)
  have h22 := hrow 2 2 (by decide)
  simp only [show ((1 : Fin 3) = 0) = False by decide, show ((1 : Fin 3) = 2) = False by decide,
    show ((2 : Fin 3) = 0) = False by decide, show ((2 : Fin 3) = 1) = False by decide,
    ite_true, ite_false] at h10 h11 h12 h20 h21 h22
  have hdet : B.det = 1 := A.2
  rw [det_fin_three, h10, h11, h12, h20, h21, h22] at hdet
  have h00 : B 0 0 = 1 := by simpa using hdet
  have hsq : B * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h11, h12, h20, h21, h22,
        CharTwo.add_self_eq_zero]
  have hA2 : A ^ 2 = 1 := by
    apply Subtype.ext
    rw [pow_two]
    exact hsq
  calc A = A ^ 3 * (A ^ 2)⁻¹ := by group
    _ = 1 := by rw [hA3, hA2]; group

theorem addSubgroup_eq_top_of_vectorStabilizer_invariant {F : Type*} [Field F]
    (Y : AddSubgroup (Fin 3 → F))
    (hY : ∀ h : SpecialLinearGroup (Fin 3) F,
      (h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
        ∀ y ∈ Y, (h : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ Y)
    {u : Fin 3 → F} (hu : u ∈ Y) (hu' : u 1 ≠ 0 ∨ u 2 ≠ 0) : Y = ⊤ := by
  have key : ∀ (i j : Fin 3) (hij : i ≠ j), j ≠ 0 → ∀ (d : F), ∀ y ∈ Y,
      (Pi.single i (d * y j) : Fin 3 → F) ∈ Y := by
    intro i j hij hj d y hy
    have hfix : ((SpecialLinearGroup.transvection hij d : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      rw [SpecialLinearGroup.transvection_coe, ← transvection,
        LinearFlag.transvection_mulVec, Pi.single_apply,
        ite_eq_right_iff.mpr (fun h => absurd h hj), mul_zero, Pi.single_zero, add_zero]
    have h1 := hY _ hfix y hy
    rw [SpecialLinearGroup.transvection_coe, ← transvection,
      LinearFlag.transvection_mulVec] at h1
    have := Y.sub_mem h1 hy
    rwa [add_sub_cancel_left] at this
  have hall : ∀ (i : Fin 3) (d : F), (Pi.single i d : Fin 3 → F) ∈ Y := by
    rcases hu' with h1 | h2
    · have hs0 : ∀ d : F, (Pi.single 0 d : Fin 3 → F) ∈ Y := fun d => by
        have := key 0 1 (by decide) (by decide) (d / u 1) u hu
        rwa [div_mul_cancel₀ d h1] at this
      have hs2 : ∀ d : F, (Pi.single 2 d : Fin 3 → F) ∈ Y := fun d => by
        have := key 2 1 (by decide) (by decide) (d / u 1) u hu
        rwa [div_mul_cancel₀ d h1] at this
      have hs1 : ∀ d : F, (Pi.single 1 d : Fin 3 → F) ∈ Y := fun d => by
        have := key 1 2 (by decide) (by decide) d _ (hs2 1)
        rwa [Pi.single_eq_same, mul_one] at this
      intro i d
      fin_cases i
      · exact hs0 d
      · exact hs1 d
      · exact hs2 d
    · have hs0 : ∀ d : F, (Pi.single 0 d : Fin 3 → F) ∈ Y := fun d => by
        have := key 0 2 (by decide) (by decide) (d / u 2) u hu
        rwa [div_mul_cancel₀ d h2] at this
      have hs1 : ∀ d : F, (Pi.single 1 d : Fin 3 → F) ∈ Y := fun d => by
        have := key 1 2 (by decide) (by decide) (d / u 2) u hu
        rwa [div_mul_cancel₀ d h2] at this
      have hs2 : ∀ d : F, (Pi.single 2 d : Fin 3 → F) ∈ Y := fun d => by
        have := key 2 1 (by decide) (by decide) d _ (hs1 1)
        rwa [Pi.single_eq_same, mul_one] at this
      intro i d
      fin_cases i
      · exact hs0 d
      · exact hs1 d
      · exact hs2 d
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  exact AddSubgroup.sum_mem _ fun i _ => hall i (x i)

theorem exists_conj_unitriangular_le_sylow {F : Type*} [Field F] [Finite F] [CharP F 2]
    (Q : Sylow 2 (SpecialLinearGroup (Fin 3) F)) :
    ∃ g : SpecialLinearGroup (Fin 3) F, ∀ u ∈ LinearFlag.unitriangular 3 F,
      g * u * g⁻¹ ∈ (Q : Subgroup (SpecialLinearGroup (Fin 3) F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F) U Q
  refine ⟨g, fun u hu => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rw [← hU] at hu
  exact ⟨u, hu, rfl⟩

theorem coords_eq_zero_of_unitriangular_fixed {F : Type*} [Field F] {v : Fin 3 → F}
    (hv : ∀ u ∈ LinearFlag.unitriangular 3 F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    v 1 = 0 ∧ v 2 = 0 := by
  have h := (LinearFlag.unitriangular_invariant_subspaces (K := F) (n := 3)).2.1
  have hv' : v ∈ (LinearFlag.flagSpace 3 F 1 : Set (Fin 3 → F)) := by
    rw [← h]
    exact hv
  rw [SetLike.mem_coe, LinearFlag.mem_flagSpace] at hv'
  exact ⟨hv' 1 (by decide), hv' 2 (by decide)⟩

variable {G : Type} [Group G] [Finite G]

theorem le_normalClosureIn_of_naturalModule {K V P D : Subgroup G} {c : G} {Z : Set G}
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (hα : Function.Surjective α)
    (β : ↥V ≃* Multiplicative (Fin 3 → F))
    (hβ : ∀ (k : ↥K) (v w : ↥V), (w : G) = k * v * (k : G)⁻¹ →
      Multiplicative.toAdd (β w) =
        (α k : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v))
    (hVK : V ≤ K) (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P K)
    (hZV : ∀ z ∈ Z, ∀ v ∈ V, z * v * z⁻¹ = v)
    (hZP : ∀ z ∈ Z, ∀ p ∈ P, p * z * p⁻¹ * z⁻¹ = 1)
    (hZK : ∀ z ∈ Z, ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ V)
    (hVD : V ≤ D) (hCZ : ∀ k ∈ K, (∀ z ∈ Z, k * z * k⁻¹ = z) → k ∈ D)
    (hcK : c ∈ K) (hc3 : c ^ 3 = 1) (hcα : α ⟨c, hcK⟩ ≠ 1) :
    V ≤ normalClosureIn (K ⊓ D) c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have h : β (⟨x, hx⟩ * ⟨y, hy⟩) = β (⟨y, hy⟩ * ⟨x, hx⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (β.injective h)
  have hV2 : IsPGroup 2 V := by
    refine IsPGroup.of_card (n := n * 3) ?_
    rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.ofAdd.symm,
      Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hF, pow_mul]
  have hodd : ¬ 2 ∣ P.relIndex K := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.2
  have htr : ∀ z ∈ Z, ∃ m ∈ V, ∀ k ∈ K, k * (z * m⁻¹) * k⁻¹ = z * m⁻¹ := fun z hz =>
    CFSG.Quasithin.SBc8.exists_mul_centralizer_of_cocycle hKV hVc hV2 hP.le hodd (hZV z hz)
      (hZK z hz) (hZP z hz)
  choose! m hmV hmC using htr
  have hmP : ∀ z ∈ Z, ∀ p ∈ P, p * m z * p⁻¹ = m z := by
    intro z hz p hp
    have h1 := hmC z hz p (hP.le hp)
    have h2 : p * z * p⁻¹ = z := mul_inv_eq_one.mp (hZP z hz p hp)
    calc p * m z * p⁻¹ = (p * (z * (m z)⁻¹) * p⁻¹)⁻¹ * (p * z * p⁻¹) := by group
      _ = (z * (m z)⁻¹)⁻¹ * z := by rw [h1, h2]
      _ = m z := by group
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_le_sylow (Q.mapSurjective hα)
  have hU : ∀ u ∈ LinearFlag.unitriangular 3 F,
      ∃ p : ↥K, (p : G) ∈ P ∧ g⁻¹ * α p * g = u := by
    intro u hu
    have h := hg u hu
    rw [Sylow.coe_mapSurjective, hQ] at h
    obtain ⟨p, hp, hpu⟩ := h
    exact ⟨p, Subgroup.mem_subgroupOf.mp hp, by rw [hpu]; group⟩
  have hgig : ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  have hggi : (g : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
    congrArg Subtype.val (mul_inv_cancel g)
  let b : ↥V → Fin 3 → F := fun v =>
    ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Multiplicative.toAdd (β v)
  have hb_mul : ∀ v w : ↥V, b (v * w) = b v + b w := by
    intro v w
    simp only [b, map_mul, toAdd_mul, mulVec_add]
  have hb_one : b 1 = 0 := by simp [b]
  have hb_inv : ∀ v : ↥V, b v⁻¹ = - b v := by
    intro v
    have := hb_mul v⁻¹ v
    rw [inv_mul_cancel, hb_one] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hb_inj : Function.Injective b := by
    intro v w hvw
    have h : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ b v = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ b w := by
      rw [hvw]
    simp only [b, mulVec_mulVec, hggi, one_mulVec] at h
    exact β.injective (Multiplicative.toAdd.injective h)
  have hb_surj : Function.Surjective b := by
    intro x
    refine ⟨β.symm (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x)), ?_⟩
    simp only [b, MulEquiv.apply_symm_apply, toAdd_ofAdd, mulVec_mulVec, hgig, one_mulVec]
  let Am : ↥K → Matrix (Fin 3) (Fin 3) F := fun k =>
    ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (α k : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)
  have hAm : ∀ k : ↥K, Am k =
      ((g⁻¹ * α k * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    fun k => rfl
  have hb_eq : ∀ (k : ↥K) (v w : ↥V), (w : G) = k * v * (k : G)⁻¹ → b w = Am k *ᵥ b v := by
    intro k v w hw
    simp only [b, Am, hβ k v w hw, mulVec_mulVec]
    rw [mul_assoc _ (g : Matrix (Fin 3) (Fin 3) F), hggi, mul_one]
  have hmline : ∀ z (hz : z ∈ Z), b ⟨m z, hmV z hz⟩ 1 = 0 ∧ b ⟨m z, hmV z hz⟩ 2 = 0 := by
    intro z hz
    apply coords_eq_zero_of_unitriangular_fixed
    intro u hu
    obtain ⟨p, hp, rfl⟩ := hU u hu
    rw [← hAm]
    exact (hb_eq p ⟨m z, hmV z hz⟩ ⟨m z, hmV z hz⟩ (hmP z hz p hp).symm).symm
  have hstab : ∀ k : ↥K, Am k *ᵥ Pi.single 0 1 = Pi.single 0 1 → (k : G) ∈ D := by
    intro k hk
    refine hCZ k k.2 fun z hz => ?_
    obtain ⟨h1, h2⟩ := hmline z hz
    have hkv : (k : G) * m z * (k : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hKV k.2) (m z)).mp (hmV z hz)
    have hline : b ⟨m z, hmV z hz⟩ =
        b ⟨m z, hmV z hz⟩ 0 • (Pi.single 0 1 : Fin 3 → F) := by
      ext i
      fin_cases i <;> simp [h1, h2]
    have hfix : b ⟨_, hkv⟩ = b ⟨m z, hmV z hz⟩ := by
      rw [hb_eq k ⟨m z, hmV z hz⟩ ⟨_, hkv⟩ rfl, hline, mulVec_smul, hk]
    have hkm : (k : G) * m z * (k : G)⁻¹ = m z := congrArg Subtype.val (hb_inj hfix)
    calc (k : G) * z * (k : G)⁻¹
        = ((k : G) * (z * (m z)⁻¹) * (k : G)⁻¹) * ((k : G) * m z * (k : G)⁻¹) := by group
      _ = z * (m z)⁻¹ * m z := by rw [hmC z hz k k.2, hkm]
      _ = z := by group
  have hXn : K ⊓ D ≤ Subgroup.normalizer (normalClosureIn (K ⊓ D) c : Set G) :=
    le_normalizer_normalClosureIn (K ⊓ D) c
  let Y : AddSubgroup (Fin 3 → F) :=
    { carrier := {x | ∃ v : ↥V, (v : G) ∈ normalClosureIn (K ⊓ D) c ∧ b v = x}
      zero_mem' := ⟨1, Subgroup.one_mem _, hb_one⟩
      add_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨v * w, Subgroup.mul_mem _ hv hw, hb_mul v w⟩
      neg_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨v⁻¹, Subgroup.inv_mem _ hv, hb_inv v⟩ }
  have hYmem : ∀ x, x ∈ Y ↔ ∃ v : ↥V, (v : G) ∈ normalClosureIn (K ⊓ D) c ∧ b v = x :=
    fun x => Iff.rfl
  have hYinv : ∀ h : SpecialLinearGroup (Fin 3) F,
      (h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
        ∀ y ∈ Y, (h : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ Y := by
    intro h hh y hy
    obtain ⟨v, hvX, rfl⟩ := (hYmem y).mp hy
    obtain ⟨k, hk⟩ := hα (g * h * g⁻¹)
    have hk' : g⁻¹ * α k * g = h := by rw [hk]; group
    have hkD : (k : G) ∈ D := hstab k (by rw [hAm, hk']; exact hh)
    have hkv : (k : G) * v * (k : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hKV k.2) v).mp v.2
    refine (hYmem _).mpr ⟨⟨_, hkv⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hXn ⟨k.2, hkD⟩) v).mp hvX
    · rw [hb_eq k v ⟨_, hkv⟩ rfl, hAm, hk']
  have hcX : c ∈ normalClosureIn (K ⊓ D) c := self_mem_normalClosureIn (K ⊓ D) c
  have hsub : ∀ x : Fin 3 → F, x - Am ⟨c, hcK⟩ *ᵥ x ∈ Y := by
    intro x
    obtain ⟨v, rfl⟩ := hb_surj x
    have hw : c * (v : G)⁻¹ * c⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hKV hcK) _).mp (V.inv_mem v.2)
    have hvX : (v : G) * c * (v : G)⁻¹ ∈ normalClosureIn (K ⊓ D) c :=
      Subgroup.subset_closure ⟨v, ⟨hVK v.2, hVD v.2⟩, rfl⟩
    refine (hYmem _).mpr ⟨v * ⟨_, hw⟩, ?_, ?_⟩
    · have : ((v * ⟨_, hw⟩ : ↥V) : G) = ((v : G) * c * (v : G)⁻¹) * c⁻¹ := by
        simp only [Subgroup.coe_mul]
        group
      rw [this]
      exact Subgroup.mul_mem _ hvX (Subgroup.inv_mem _ hcX)
    · rw [hb_mul, hb_eq ⟨c, hcK⟩ v⁻¹ ⟨_, hw⟩ rfl, hb_inv, mulVec_neg, sub_eq_add_neg]
  have hoff : ∃ u ∈ Y, u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hcα
    have hc' : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simp [hc3])
    have hA3 : (g⁻¹ * α ⟨c, hcK⟩ * g) ^ 3 = 1 := by
      rw [show (g⁻¹ * α ⟨c, hcK⟩ * g) ^ 3 = g⁻¹ * (α ⟨c, hcK⟩) ^ 3 * g by
        simp only [pow_succ, pow_zero, one_mul]; group, ← map_pow, hc', map_one]
      group
    have hA := sl3_eq_one_of_sub_mulVec_mem_line _ hA3 fun x => by
      rw [← hAm]
      exact hcon _ (hsub x)
    calc α ⟨c, hcK⟩ = g * (g⁻¹ * α ⟨c, hcK⟩ * g) * g⁻¹ := by group
      _ = 1 := by rw [hA]; group
  obtain ⟨u, hu, hu'⟩ := hoff
  have hYtop := addSubgroup_eq_top_of_vectorStabilizer_invariant Y hYinv hu hu'
  intro v hv
  have hvY : b ⟨v, hv⟩ ∈ Y := hYtop ▸ AddSubgroup.mem_top _
  obtain ⟨w, hwX, hw⟩ := (hYmem _).mp hvY
  have hwv : (w : G) = v := congrArg Subtype.val (hb_inj hw)
  rw [← hwv]
  exact hwX

omit [Finite G] in
theorem mem_and_commute_of_mem_zTwenty {T : Subgroup G} {z : G} (hz : z ∈ zTwenty T) :
    z ∈ T ∧ ∀ t ∈ T, t * z = z * t := by
  obtain ⟨z, hz, rfl⟩ := hz
  rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff] at hz
  exact ⟨z.2, fun t ht => congrArg Subtype.val (Subgroup.mem_center_iff.mp hz.1 ⟨t, ht⟩)⟩

theorem step209V_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (h7 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (h8 : IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n) :
    vTwenty M c T ≤ normalClosureIn (kTwenty M c ⊓ N) c := by
  obtain ⟨-, hVO, n, -, hVK, F, _, _, hF, α, hαs, hαk, β, hβ⟩ := h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hMV : M ≤ Subgroup.normalizer (vTwenty M c T : Set G) := by
    rw [hVO]
    exact hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hV2 : IsPGroup 2 (vTwenty M c T) :=
    hVO ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c)
  have hVT : vTwenty M c T ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVK.trans hKM) hMV hV2).trans
      (pCoreOf_le_of_isSylowOf hT.sylow)
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hcK : c ∈ kTwenty M c := self_mem_normalClosureIn M c
  refine le_normalClosureIn_of_naturalModule (P := T ⊓ kTwenty M c)
    (Z := (zTwenty T : Set G)) hF α hαs β hβ hVK ?_ ?_ ?_ ?_ ?_ (hVT.trans hTN) ?_ hcK hc3 ?_
  · rw [hVO]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  · exact hT.sylow.inf_of_le_normalizer hKM hMK
  · intro z hz v hv
    rw [← (mem_and_commute_of_mem_zTwenty hz).2 v (hVT hv)]
    group
  · intro z hz p hp
    rw [(mem_and_commute_of_mem_zTwenty hz).2 p hp.1]
    group
  · intro z hz k hk
    have h1 : z * k * z⁻¹ * k⁻¹ ∈ vTwenty M c T := Subgroup.commutator_mem_commutator hz hk
    rw [show k * z * k⁻¹ * z⁻¹ = (z * k * z⁻¹ * k⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ h1
  · intro k hk hkz
    refine h7 ⟨hk, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have := hkz z hz
    calc z * k = k * z * k⁻¹ * k := by rw [this]
      _ = k * z := by group
  ·
    intro h1
    have hcV : c ∈ vTwenty M c T := by
      have : (⟨c, hcK⟩ : ↥(kTwenty M c)) ∈ (vTwenty M c T).subgroupOf (kTwenty M c) := by
        rw [← hαk, MonoidHom.mem_ker]
        exact h1
      exact Subgroup.mem_subgroupOf.mp this
    have hKV : kTwenty M c ≤ vTwenty M c T := by
      rw [kTwenty, normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMV hx) c).mp hcV
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    obtain ⟨k, hk⟩ := hαs (Matrix.SpecialLinearGroup.transvection h01 (1 : F))
    have hk1 : α k = 1 := by
      rw [← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
      exact hKV k.2
    rw [hk1] at hk
    have h2 := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 3) F =>
      (B : Matrix (Fin 3) (Fin 3) F) 0 1) hk
    simp [Matrix.SpecialLinearGroup.transvection_coe] at h2

theorem step209V_proof : Step209V := fun _ _ _ _ _ _ _ _ _ hT hTN h7 h8 =>
  step209V_core hT.toCtx20 hTN h7 h8

end CFSG.RankThree.PartTwo.Sec20
