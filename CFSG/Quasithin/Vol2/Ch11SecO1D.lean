module

public import CFSG.Quasithin.Vol2.Ch11SecO1B
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartF
public import CFSG.Quasithin.Vol2.Ch11SecDFacts6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA SecS SecS.C11P9A
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom coe_torusHom torus)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped IsMulCommutative

section Torus

variable {K : Type} [Field K]

theorem eq_zero_of_mul_eq {a b : K} (ha : a ≠ 1) (h : a * b = b) : b = 0 := by
  have h1 : (a - 1) * b = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr ha)

theorem eq_zero_of_forall_tSL {c : Kˣ} (hc : c ≠ 1) {y : Fin 3 → K}
    (h : ∀ t : Kˣ × Kˣ, ((tSL t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y =
      y) : y = 0 := by
  have hc' : (c : K) ≠ 1 := fun h1 => hc (Units.ext h1)
  have h1 := h (c, 1)
  have h2 := h (1, c)
  have h3 := h (c⁻¹, 1)
  rw [tSL_mulVec] at h1 h2 h3
  funext i
  fin_cases i
  · exact eq_zero_of_mul_eq hc' (by simpa using congrFun h1 0)
  · exact eq_zero_of_mul_eq hc' (by simpa using congrFun h2 1)
  · exact eq_zero_of_mul_eq hc' (by simpa using congrFun h3 2)

theorem exists_units_ne_one [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ c : Kˣ, c ≠ 1 := by
  obtain ⟨c, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  exact ⟨Units.mk0 c hc0, fun h => hc1 (by simpa using congrArg Units.val h)⟩

end Torus

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem fix_of_mem_autOn {X V : Subgroup G} {v : G} (hv : v ∈ V)
    (hvX : v ∈ Subgroup.centralizer (X : Set G)) {d : MulAut ↥V} (hd : d ∈ autOn X V) :
    d ⟨v, hv⟩ = ⟨v, hv⟩ := by
  obtain ⟨x, hx, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hd
  apply Subtype.ext
  rw [conjV_apply_coe, Subgroup.mem_centralizer_iff.mp hvX x hx, mul_inv_cancel_right]

theorem cartan_fix_eq_bot_sl3 (hS : SecD.NatSetting11 G T L I n) (hk : KindSL3 L (fsuV T I) n)
    {X : Subgroup G} (hX : IsCartanX T L X) :
    fsuV T I ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  have := isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, hK, π, f, -, hf⟩ := exists_coord_sl3 hS hk
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨c, hc⟩ := exists_units_ne_one hn hK
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf (isSylowTwoOf_P hS)
  have hD := isHall_autOn_cartan hS hX
  rw [eq_map_psiW_of_sylow hg, inf_normalizer_eq hf g] at hD
  obtain ⟨x, -, hDx⟩ := exists_eq_map_torus3 hf g hD
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvX⟩
  have hfix : ∀ t : Kˣ × Kˣ, ((tSL t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((((g * x)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f ⟨v, hvV⟩) =
        (((g * x)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          f ⟨v, hvV⟩ := by
    intro t
    have hmem : psiW π (g * x) (tSL t) ∈ autOn X (fsuV T I) := by
      rw [hDx]
      exact ⟨tSL t, ⟨t, rfl⟩, rfl⟩
    have h1 := congrArg f (fix_of_mem_autOn hvV hvX hmem)
    rw [psiW_apply, hf.act3] at h1
    rw [← conj_mulVec, h1]
  have h0 := eq_zero_of_forall_tSL hc hfix
  have h2 : f ⟨v, hvV⟩ = 0 := by
    rw [← g_ginv_mulVec (g * x) (f ⟨v, hvV⟩), h0, Matrix.mulVec_zero]
  rw [hf.ker, Subgroup.mem_bot] at h2
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)

theorem _root_.CFSG.Quasithin.Vol2.Ch11.SecD.torusFixSL3Fact_holds : SecD.TorusFixSL3Fact :=
  fun _ _ _ _ _ _ _ _ hS hk hX => cartan_fix_eq_bot_sl3 hS hk hX

end CFSG.Quasithin.Vol2.Ch11.SecO1
