module

public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.H13.U3CodimTwo
public import CFSG.Quasithin.SteinbergCBU3Frame
public import CFSG.Quasithin.SteinbergBQCoreGeneratedConfinement

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Quasithin.SteinbergCB CFSG.Blueprint
open scoped IsMulCommutative

@[expose] def U3InternalFrameProducer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L →
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
    ∃ (V : Subgroup G) (z : G), QTU3InternalFrame T L V z

@[expose] def U3SixActionProfileProducer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G) [IsElementaryAbelian 2 V],
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    (∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 → ∃ l ∈ L, l⁻¹ * x * l = y) ∧
      ∃ b : LinearMap.BilinForm (ZMod 2) (Additive V), b.Nondegenerate ∧ b.IsAlt ∧
        (∀ n : normalizer (V : Set G), ∀ x y : Additive V,
          b (u3ConjLin V _ le_rfl n x) (u3ConjLin V _ le_rfl n y) = b x y) ∧
        QTBinarySixProfile b (u3ConjLin V (normalizer (V : Set G)) le_rfl).range

@[expose] def U3LocalUniquenessEscapeProducer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G),
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    normalizer (L : Set G) < ⊤ ∧ normalizer (V : Set G) ≤ normalizer (L : Set G) ∧
      (∀ m ∈ normalizer (L : Set G), CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) ∧
      ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)

@[expose] def U3CodimThreeCentralizerControl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G),
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    ∀ F : Subgroup G, F ≤ V → F.relIndex V ≤ 8 →
      centralizer (F : Set G) ≤ normalizer (V : Set G)

@[expose] def U3AbelianCentralizerHull : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G),
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    IsMulCommutative ↥(⨆ h ∈ centralizer ({z} : Set G), CFSG.conjugate V h)

@[expose] def U3EscapingLocalGenerationWitness : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G),
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    (∀ (g : G) (B : Subgroup G), B ≤ T ⊓ CFSG.conjugate V g →
      B.relIndex (CFSG.conjugate V g) ≤ 4 → ⁅B, V⁆ = ⊥) →
    ∃ (H D : Subgroup G) (P : Finset (Subgroup G × Subgroup G)),
      T ≤ H ∧ H ≤ centralizer ({z} : Set G) ∧ ¬ H ≤ normalizer (L : Set G) ∧
        D ≤ H ⊓ normalizer (L : Set G) ∧ (∀ AK ∈ P, AK.1 ≤ H ∧ AK.2 ≤ H) ∧
        H = D ⊔ ⨆ AK ∈ P, AK.2 ∧
        ∀ AK ∈ P, (∃ g : G, AK.1 = CFSG.conjugate V g) ∧ AK.1 ≤ AK.2 ∧
          QuasithinUnique.IsSylowTwoOf (T ⊓ AK.2) AK.2 ∧
          (AK.1 ⊓ CFSG.Open.pCoreOf 2 AK.2).relIndex AK.1 ≤ 4 ∧
          SteinbergBQ.twoResidualOf AK.2 ≤
            closure (⋃ k ∈ AK.2, (SteinbergBQ.conjSub k AK.1 : Set G))

variable {G : Type*} [Group G]

theorem conjSub_eq_conjugate (g : G) (V : Subgroup G) :
    SteinbergBQ.conjSub g V = CFSG.conjugate V g⁻¹ := by
  ext x
  rw [SteinbergBQ.mem_conjSub, mem_conjugate_iff', inv_inv]

theorem stmt13_3_16_of_producers (h1 : U3InternalFrameProducer)
    (h2 : U3SixActionProfileProducer) (h3 : U3LocalUniquenessEscapeProducer)
    (h4 : U3CodimThreeCentralizerControl) (h5 : U3AbelianCentralizerHull)
    (h6 : U3EscapingLocalGenerationWitness) : Stmt13_3_16 := by
  intro G _ _ T L hH hU3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, z, hF⟩ := h1 G T L hH hU3
  obtain ⟨-, hVT, hVe, hV64, -, -, hLV, hTV, -, -, -, hVz, hz2⟩ := id hF
  have : IsElementaryAbelian 2 V := hVe
  set M := normalizer (L : Set G) with hM
  obtain ⟨hLtrans, b, -, -, -, hprof⟩ := h2 G T L V z hH hU3 hF
  obtain ⟨-, hVM, -, -⟩ := h3 G T L V z hH hU3 hF
  have hcent := h4 G T L V z hH hU3 hF
  have hJ := h5 G T L V z hH hU3 hF
  let TS : Sylow 2 G := hH.sylow.1.toSylow hH.sylow.2
  have hzV : z ∈ V := by
    have h : z ∈ V ⊓ centralizer (T : Set G) := by
      rw [hVz]
      exact mem_zpowers z
    exact h.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have htrans : ∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 →
      ∃ n ∈ normalizer (V : Set G), n⁻¹ * x * n = y := by
    intro x hx hx1 y hy hy1
    obtain ⟨l, hl, hly⟩ := hLtrans x hx hx1 y hy hy1
    exact ⟨l, hLV hl, hly⟩
  have hJ' : ∀ x ∈ ⨆ h ∈ centralizer ({z} : Set G), CFSG.conjugate V h,
      ∀ y ∈ ⨆ h ∈ centralizer ({z} : Set G), CFSG.conjugate V h, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(⨆ h ∈ centralizer
      ({z} : Set G), CFSG.conjugate V h)) ⟨y, hy⟩)
  obtain ⟨hcodim, -⟩ := six_profile_conjugate_codimension_two_centralization TS hV64
    hTV b hprof htrans hzV hz1 hJ' hcent
  obtain ⟨H, D, P, hTH, -, hHM, hD, hPH, hgen, hP⟩ :=
    h6 G T L V z hH hU3 hF fun g B hB hBidx => hcodim g B hB hBidx
  apply hHM
  refine SteinbergBQ.conjugate_core_generated_subgroup_confinement TS hVT
    (hV64.trans (by norm_num : (64 : ℕ) = 2 ^ 6)) hTV hVM (by norm_num : 2 < 4)
    (by norm_num : 4 ≤ 6) ?_ ?_ hTH hD P hPH hgen ?_
  · intro F hFV hF
    obtain ⟨k, -, hk⟩ := exists_relIndex_eq_two_pow hFV (hV64.trans (by norm_num :
      (64 : ℕ) = 2 ^ 6))
    refine hcent F hFV ?_
    rw [hk] at hF ⊢
    by_contra h
    push Not at h
    have h3 : 2 ^ 4 ≤ 2 ^ k := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      by_contra h4
      push Not at h4
      have h5 : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h5
      omega
    omega
  · intro g B hB hBidx
    rw [conjSub_eq_conjugate] at hB hBidx
    have h7 := hcodim g⁻¹ B hB (by simpa using hBidx)
    rw [commutator_eq_bot_iff_le_centralizer] at h7
    exact h7
  · intro AK hAK
    obtain ⟨⟨g, hg⟩, hAKle, hSyl, hcore, hres⟩ := hP AK hAK
    refine ⟨⟨g⁻¹, by rw [conjSub_eq_conjugate, inv_inv]; exact hg⟩, hAKle, hSyl,
      by simpa using hcore, hres⟩

end CFSG.Quasithin.H13.U3
