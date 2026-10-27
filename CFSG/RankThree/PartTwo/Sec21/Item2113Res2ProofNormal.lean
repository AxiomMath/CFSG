module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofTwelve

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item2112Rank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G)
    (E' U' : Subgroup G) (b : G) (K : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → Sec21Pair G A E' U' b K → IsList218 K →
      ∀ d ∈ A, d ≠ 1 → IsCentral218 K d →
      (d ∈ iOf218 K d ∧
        ((Nonempty (K ≃* NativeSporadic.He) ∧
            Sec4.IsTripleCover (iOf218 K d) (alternatingGroup (Fin 7))) ∨
          ((Nonempty (lBar K ≃* NativeSporadic.M24) ∨ Nonempty (lBar K ≃* NativeSporadic.J2) ∨
              Nonempty (lBar K ≃* NativeSporadic.Ru)) ∧
            Sec4.IsTripleCover (lBar (iOf218 K d)) (alternatingGroup (Fin 6))) ∨
          (Nonempty (K ≃* NativeSporadic.J4) ∧
            Nat.card (Subgroup.center (iOf218 K d)) = 6 ∧
            Nonempty (iOf218 K d ⧸ Subgroup.center (iOf218 K d) ≃* NativeSporadic.M22)) ∨
          (∃ n : ℕ, 0 < n ∧ Even n ∧
            (ChevalleyExceptionalModel (lBar K) .G2 2 n ∨
              ChevalleyExceptionalModel (lBar K) .trialityD4 2 n) ∧
            Nonempty (lBar (iOf218 K d) ≃* SL3 n)))) →
      Subgroup.centralizer ({d} : Set G) ≤
        Subgroup.normalizer ((iOf218 K d ⊔
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) :
            Subgroup G) : Set G) →
      ∀ x : G, x * c * x⁻¹ ≠ d

namespace Item2113Res2Proof

open Subgroup
open Item2113Proof (commGroupOf map_subtype_zpowers map_subtype_closure_pair
  map_eq_iff_mem_normalizer normalizer_le_of_forall transvection_data data_of_choice
  inv_apply_mem_of_map_eq apply_mem_of_map_eq fixSub_eq_closure apply_eq_mul_of_ne
  conj_comm_mem ofCoords ofCoords_apply coords_smul)

theorem item2112NoFusion_of (h219 : Item219) (h2101 : Item2110One) (hR : Item2112Rank) :
    Item2112NoFusion := by
  intro G _ _ A E U c L E' U' b K hpair hL hpair' hK d hdA hd1 hdcen x
  exact hR G A E U c L E' U' b K hpair hL hpair' hK d hdA hd1 hdcen
    (h219 G A E' U' b K hpair' hK d hdA hd1 hdcen)
    (h2101 G A E' U' b K hpair' hK d hdA hd1 hdcen) x

variable {G : Type} [Group G]

theorem exists_mem_mapping {A : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Multiplicative V ≃* A)
    (hSL : ∀ σ : MulAut A, LinearMap.det (Sec12.coordHom f σ : V →ₗ[ZMod 3] V) = 1 →
      σ ∈ wStar A) {cA dA : A} (hc1 : cA ≠ 1) (hdc : dA ∉ zpowers cA) :
    ∃ σ ∈ wStar A, σ cA = dA := by
  set uc : V := Multiplicative.toAdd (f.symm cA) with huc
  set ud : V := Multiplicative.toAdd (f.symm dA) with hud
  have hfuc : f (Multiplicative.ofAdd uc) = cA := by simp [huc]
  have hfud : f (Multiplicative.ofAdd ud) = dA := by simp [hud]
  have hnot : uc ∉ Submodule.span (ZMod 3) {uc - ud} := by
    intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    by_cases ha0 : a = 0
    · apply hc1
      rw [← hfuc, ← ha, ha0, zero_smul, ofAdd_zero, map_one]
    · apply hdc
      have h1 : a • ud = (a - 1) • uc := by
        have h2 := ha
        rw [smul_sub] at h2
        rw [sub_smul, one_smul]
        calc a • ud = a • uc - (a • uc - a • ud) := by abel
          _ = a • uc - uc := by rw [h2]
      have h3' : ud = (a⁻¹ * (a - 1)) • uc := by
        rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [← hfud, h3', coords_smul, hfuc]
      exact pow_mem (mem_zpowers cA) _
  obtain ⟨φ, hφc, hφd⟩ := Submodule.exists_le_ker_of_notMem hnot
  have hφw : φ (uc - ud) = 0 := hφd (Submodule.mem_span_singleton_self _)
  have hφud : φ ud = φ uc := by
    have h := hφw
    rw [map_sub] at h
    exact (sub_eq_zero.mp h).symm
  set v : V := (φ uc)⁻¹ • (ud - uc) with hv
  have hφv : φ v = 0 := by
    have h0 : φ (ud - uc) = 0 := by
      rw [← neg_sub, map_neg, hφw]
      exact neg_zero
    rw [hv, map_smul, h0, smul_zero]
  set τ := LinearEquiv.transvection (f := φ) (v := v) hφv with hτ
  refine ⟨ofCoords f τ, hSL _ ?_, ?_⟩
  · rw [Item2113Proof.coordHom_ofCoords, ← LinearEquiv.coe_det,
      LinearEquiv.transvection.det_eq_one]
    rfl
  · rw [ofCoords_apply, ← huc, LinearEquiv.transvection.apply, hv, smul_smul,
      mul_inv_cancel₀ hφc, one_smul, add_sub_cancel, hfud]

section Normal

theorem item2111_of_noFusion (h211 : Item211) (hch : Item2113Choice)
    (hNF : Item2112NoFusion) : Item2111 := by
  intro G _ _ A E U c L hpair hL hirr
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe := hpair.mem_S.1.1
  have hLc : L ≤ centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  obtain ⟨d, hdA, hd1, hdcen, t, htL, ht, htd⟩ := hch G A E U c L hpair hL
  obtain ⟨h27, hc1, hcA, hdc⟩ := data_of_choice h211 hpair hL hdA hd1 hdcen
  obtain ⟨htS, -, -, -, -⟩ := transvection_data hcA hdA hLc htL ht htd
  have hc1' : (⟨c, hcA⟩ : A) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  obtain ⟨f⟩ := Sec12.exists_coords hAe (n := 3) (by rw [h27]; norm_num)
  have hSL := @rank3II_21_11_core G _ A hAe h27 (Fin 3 → ZMod 3) Pi.addCommGroup
    (Pi.module _ _ _) f (wStar A) hirr t htS ht
  obtain ⟨σ, ⟨w, rfl⟩, hσ⟩ := @exists_mem_mapping G _ A (Fin 3 → ZMod 3) Pi.addCommGroup
    (Pi.module _ _ _) f hSL _ _ hc1' hdc
  have hwc : (w : G) * c * (w : G)⁻¹ = d := by
    have h := congrArg Subtype.val hσ
    rwa [normalizerMonoidHom_apply_apply_coe] at h
  exact hNF G A E U c L E U c L hpair hL hpair hL d hdA hd1 hdcen w hwc

end Normal

end Item2113Res2Proof

end CFSG.RankThree.PartTwo.Sec21
