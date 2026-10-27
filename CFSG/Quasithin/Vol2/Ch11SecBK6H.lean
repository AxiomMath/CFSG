module

public import CFSG.Quasithin.Vol2.Ch11SecBK6G
public import CFSG.Quasithin.Vol2.Ch11SecBK7K
public import CFSG.Quasithin.Vol2.Ch11SecBK7H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp qSp_mul qSp_injective)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative

namespace BK6

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem relIndex_le_of_hom {A B : Subgroup G} {M : Type*} [AddCommGroup M] [Finite M]
    (φ : ↥A → M) (hφ : ∀ a b, φ (a * b) = φ a + φ b) (hker : ∀ a, φ a = 0 → (a : G) ∈ B) :
    B.relIndex A ≤ Nat.card M := by
  have h1 : φ 1 = 0 := by
    have := hφ 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  let χ : ↥A →* Multiplicative M :=
    { toFun := fun a => Multiplicative.ofAdd (φ a)
      map_one' := by rw [h1]; rfl
      map_mul' := fun a b => by rw [hφ]; rfl }
  have hle : χ.ker ≤ B.subgroupOf A := fun a ha => by
    rw [Subgroup.mem_subgroupOf]
    exact hker a (by simpa [χ] using ha)
  calc B.relIndex A = (B.subgroupOf A).index := rfl
    _ ≤ χ.ker.index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
          (Subgroup.index_dvd_of_le hle)
    _ = Nat.card χ.range := Subgroup.index_ker χ
    _ ≤ Nat.card (Multiplicative M) := Subgroup.card_le_card_group _
    _ = Nat.card M := rfl

theorem r2Gen_sp4 (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSp4 L V n) {A : Subgroup G}
    (hAR : A ≤ pCoreOf 2 (LOf L V₂ ⊔ T)) :
    V ≤ ⨆ (B : Subgroup G) (_ : B ≤ A ∧ E3.mQuot A B ≤ 2 * n),
      V ⊓ Subgroup.centralizer (B : Set G) := by
  obtain ⟨_, K, _, _, _, hK, π, f, hf, g, -, -, hV₂⟩ := K7.exists_coord_flag24 hfl hk
  have hZ : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, h z = z :=
    fun h hh z hz => SecA.autOn_fixes_cV h hh z hz
  choose x y z hxyz using fun a : ↥A => K7.exists_qSp_of_mem_r2 hfl hK hf hV₂ (hAR a.2)
  have huniq : ∀ a b c a' b' c' : K,
      ((π (g * qSp a b c * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) =
        ((π (g * qSp a' b' c' * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) →
      a = a' ∧ b = b' ∧ c = c' := by
    intro a b c a' b' c' h
    have h1 := hf.injective_nat (Subtype.ext h)
    exact qSp_injective (mul_left_cancel (mul_right_cancel h1))
  have hadd : ∀ a b : ↥A, x (a * b) = x a + x b ∧ y (a * b) = y a + y b ∧
      z (a * b) = z a + z b := by
    intro a b
    refine huniq _ _ _ _ _ _ ?_
    rw [← hxyz, show SecA.conjV V ((a * b : ↥A) : G) (K7.r2_le_normalizer hfl (hAR (a * b).2)) =
      SecA.conjV V a (K7.r2_le_normalizer hfl (hAR a.2)) *
        SecA.conjV V b (K7.r2_le_normalizer hfl (hAR b.2)) from SecA.conjV_mul V _ _, hxyz,
      hxyz, ← Subgroup.coe_mul, ← map_mul, ← qSp_mul]
    congr 2
    group
  set y₀ := mat 2 K g *ᵥ vec4 1 0 0 0 with hy₀
  set y₁ := mat 2 K g *ᵥ vec4 0 1 0 0 with hy₁
  have hy₀ne : y₀ ≠ 0 := v0_ne_zero g
  have hy₁ne : y₁ ≠ 0 := fun h => by
    have := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h
    simp only [hy₁, mat_inv_mulVec, Matrix.mulVec_zero] at this
    exact one_ne_zero (congrFun this (.inl 1))
  let P (u : Fin 2 ⊕ Fin 2 → K) : Subgroup G :=
    (hf.pre (LinearMap.ker ((Matrix.toBilin' (spJ K)).flip u)).toAddSubgroup).map V.subtype
  have hP : ∀ u (v : G), v ∈ P u ↔ ∃ hv : v ∈ V, Matrix.toBilin' (spJ K) (f ⟨v, hv⟩) u = 0 := by
    intro u v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hv, h⟩
      exact ⟨⟨v, hv⟩, h, rfl⟩
  have hcentP : ∀ (u : Fin 2 ⊕ Fin 2 → K), u ≠ 0 → ∀ (a : ↥A) (c : K),
      SecA.conjV V a (K7.r2_le_normalizer hfl (hAR a.2)) =
        ((π (K7.trv u c) : ↥(autOn L V)) : MulAut ↥V) →
      (a : G) ∈ Subgroup.centralizer (P u : Set G) := by
    intro u hu a c he
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨hvV, hvu⟩ := (hP u v).mp hv
    have h1 := congrArg Subtype.val (K7.trv_fix hf hZ hu c hvu)
    rw [← he, SecA.conjV_apply_coe] at h1
    change (a : G) * v * (a : G)⁻¹ = v at h1
    calc v * (a : G) = (a : G) * v * (a : G)⁻¹ * (a : G) := by rw [h1]
      _ = (a : G) * v := by group
  have hidx : ∀ u : Fin 2 ⊕ Fin 2 → K, u ≠ 0 → ∀ φ : ↥A → K × K,
      (∀ a b, φ (a * b) = φ a + φ b) →
      (∀ a, φ a = 0 → ∃ c : K, SecA.conjV V a (K7.r2_le_normalizer hfl (hAR a.2)) =
        ((π (K7.trv u c) : ↥(autOn L V)) : MulAut ↥V)) →
      E3.mQuot A (A ⊓ Subgroup.centralizer (P u : Set G)) ≤ 2 * n := by
    intro u hu φ hφ hker
    refine mQuot_le_of_relIndex_le ((relIndex_le_of_hom φ hφ fun a ha => ?_).trans ?_)
    · obtain ⟨c, hc⟩ := hker a ha
      exact ⟨a.2, hcentP u hu a c hc⟩
    · rw [Nat.card_prod, hK, ← pow_add, two_mul]
  have h₀ := hidx y₀ hy₀ne (fun a => (y a, z a))
    (fun a b => by rw [(hadd a b).2.1, (hadd a b).2.2]; rfl) fun a ha => by
      obtain ⟨hy0, hz0⟩ := Prod.mk.inj ha
      refine ⟨-x a, ?_⟩
      rw [hxyz, hy0, hz0, hy₀, ← K7.trv_conj, K7.trv_e0, neg_neg]
  have h₁ := hidx y₁ hy₁ne (fun a => (x a, y a))
    (fun a b => by rw [(hadd a b).1, (hadd a b).2.1]; rfl) fun a ha => by
      obtain ⟨hx0, hy0⟩ := Prod.mk.inj ha
      refine ⟨-z a, ?_⟩
      rw [hxyz, hx0, hy0, hy₁, ← K7.trv_conj, K7.trv_e1, neg_neg]
  have hPle : ∀ u, E3.mQuot A (A ⊓ Subgroup.centralizer (P u : Set G)) ≤ 2 * n →
      P u ≤ ⨆ (B : Subgroup G) (_ : B ≤ A ∧ E3.mQuot A B ≤ 2 * n),
        V ⊓ Subgroup.centralizer (B : Set G) := by
    intro u hu v hv
    have hmem : v ∈ V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (P u : Set G) : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨((hP u v).mp hv).1, Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 v hv).symm⟩
    exact (le_iSup₂ (f := fun (B : Subgroup G) (_ : B ≤ A ∧ E3.mQuot A B ≤ 2 * n) =>
      V ⊓ Subgroup.centralizer (B : Set G)) (A ⊓ Subgroup.centralizer (P u : Set G))
      ⟨inf_le_left, hu⟩) hmem
  intro v hv
  set xv := mat 2 K g⁻¹ *ᵥ f ⟨v, hv⟩ with hxv
  obtain ⟨w₀, hw₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 (xv (.inl 0)) (xv (.inl 1)) 0 (xv (.inr 1)))
  obtain ⟨w₁, hw₁⟩ := hf.surj (mat 2 K g *ᵥ vec4 0 0 (xv (.inr 0)) 0)
  have hsum : f ⟨v, hv⟩ = f (w₀ * w₁) := by
    rw [hf.map_mul, hw₀, hw₁, ← Matrix.mulVec_add, ← mat_mulVec_inv g (f ⟨v, hv⟩), ← hxv]
    congr 1
    exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])
  have hz := (hf.eq_iff _ _).mp hsum
  set z : ↥V := ⟨v, hv⟩ * (w₀ * w₁)⁻¹ with hzdef
  have hv' : v = ((z * w₀ : ↥V) : G) * (w₁ : G) := by
    rw [← Subgroup.coe_mul, hzdef, show (⟨v, hv⟩ : ↥V) * (w₀ * w₁)⁻¹ * w₀ * w₁ = ⟨v, hv⟩ by group]
  have hzw₀ : ((z * w₀ : ↥V) : G) ∈ P y₀ := by
    refine (hP y₀ _).mpr ⟨(z * w₀).2, ?_⟩
    rw [show (⟨((z * w₀ : ↥V) : G), (z * w₀).2⟩ : ↥V) = z * w₀ from rfl, hf.map_mul,
      (hf.ker z).mpr hz, zero_add, hw₀, hy₀, spB_mat, toBilin'_spJ_apply]
    simp [vec4, Fin.sum_univ_two]
  have hw₁P : (w₁ : G) ∈ P y₁ := by
    refine (hP y₁ _).mpr ⟨w₁.2, ?_⟩
    rw [show (⟨(w₁ : G), w₁.2⟩ : ↥V) = w₁ from rfl, hw₁, hy₁, spB_mat, toBilin'_spJ_apply]
    simp [vec4, Fin.sum_univ_two]
  rw [hv']
  exact Subgroup.mul_mem _ (hPle y₀ h₀ hzw₀) (hPle y₁ h₁ hw₁P)

end BK6

theorem factR2Gen_holds : FactR2Gen := by
  intro G _ _ L V X T V₁ V₂ n hfl A hA
  rcases hfl.kind with hk | hk
  · exact BK6.r2Gen_sl3 hfl hk hA
  · exact BK6.r2Gen_sp4 hfl hk hA

end CFSG.Quasithin.Vol2.Ch11.SecB
