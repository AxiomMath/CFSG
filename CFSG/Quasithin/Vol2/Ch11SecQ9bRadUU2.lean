module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUU1
public import CFSG.Quasithin.Vol2.Ch11SecQ9bI2a

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₂ K : Subgroup G} {n : ℕ}

namespace C11P9B

theorem isMulCommutative_of_le_fsuV (h : Hyp11 G T L I n) {W : Subgroup G}
    (hWV : W ≤ fsuV T I) : IsMulCommutative ↥W := by
  obtain ⟨hc, -⟩ := isElemAbelian_fsuV h
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h2 := hc.is_comm.comm (⟨a, hWV a.2⟩ : ↥(fsuV T I)) ⟨b, hWV b.2⟩
  have h3 : ((⟨a, hWV a.2⟩ * ⟨b, hWV b.2⟩ : ↥(fsuV T I)) : G) =
      ((⟨b, hWV b.2⟩ * ⟨a, hWV a.2⟩ : ↥(fsuV T I)) : G) :=
    congrArg Subtype.val h2
  exact h3

omit [Finite G] in
theorem mem_centralizer_sup {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.centralizer (A : Set G)) (hB : x ∈ Subgroup.centralizer (B : Set G)) :
    x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hz : Subgroup.zpowers x ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      exact hA
    · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      exact hB
  exact hz (Subgroup.mem_zpowers x)

theorem modules3n_U (hFc : Facts12c) (hN : NatFacts) (hL3 : FactLineSL3) (hLp : FactLineSp4)
    (hLg : FactLineG2) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n)
    (hV₂ : IsVi T L I n 2 V₂) {U : Subgroup G}
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂)
    (hTU : T ≤ Subgroup.normalizer (U : Set G))
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G)))
    (hNK : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₂ ≤ K) (hc : Concl1111 (↥K ⧸ CFSG.pCore 2 ↥K) n) :
    (n = 2 ∧ (IsAlt 7 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
        IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (alternatingGroup (Fin 7))) ∧
      ∀ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
        Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) → Odd (orderOf y) →
        (y : G) ∈ Subgroup.centralizer (U : Set G)) ∨
    (n = 2 ∧ ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      ∀ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
        CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K) → Odd (orderOf y) →
        (y : G) ∈ Subgroup.centralizer (U : Set G)) := by
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := le_of_mem_cComp hK
  have hU₂ : U ≤ V₂ := le_V2_of_sup_eq hUV
  have := isMulCommutative_of_le_fsuV h (hU₂.trans (IsVi.le_fsuV hV₂))
  set ρ : ↥K →* MulAut ↥U := (conjAct U).comp (Subgroup.inclusion hKN) with hρdef
  have hρ : ∀ y : ↥K, ρ y = 1 → (y : G) ∈ Subgroup.centralizer (U : Set G) := by
    intro y hy
    have hy' : conjV U y (hKN y.2) = 1 := hy
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h2 := congrArg (fun φ : MulAut ↥U => ((φ ⟨v, hv⟩ : ↥U) : G)) hy'
    simp only [conjV_apply_coe, MulAut.one_apply] at h2
    calc v * y = y * v * (y : G)⁻¹ * y := by rw [h2]
      _ = y * v := by group
  have hsq : ∀ w : ↥U, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w (IsVi.le_fsuV hV₂ (hU₂ w.2)))
  have hρ1 : ρ ≠ 1 := by
    intro h1
    apply not_lOf_le_centralizer hL3 hLp hLg h1102 h hV₂
    intro l hl
    rw [← hUV]
    exact mem_centralizer_sup (hρ ⟨l, hLK hl⟩ (by rw [h1]; rfl))
      (Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (Subgroup.mem_centralizer_iff.mp hz.2 l ((perfectCore_le _).trans inf_le_left hl)).symm)
  rcases hFc.modules ↥K ↥U hsq ρ n h.one_lt ((Subgroup.card_le_of_le hU₂).trans
      (card_V2_le h1103 h hV₂))
      (perfect_top_of_mem_cComp hK) hc hρ1 with hB | ⟨hn, hA7, hZ⟩ | ⟨hn, hnq, hF⟩
  · exfalso
    have hSyl := isSylowTwoOf_top_subgroupOf (A4.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTU) hKN hNK)
    have hmap : ((LOf L V₂).subgroupOf K).map K.subtype = LOf L V₂ :=
      Subgroup.map_subgroupOf_eq_of_le hLK
    have hperf : ⁅(LOf L V₂).subgroupOf K, (LOf L V₂).subgroupOf K⁆ = (LOf L V₂).subgroupOf K := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, hmap]
      exact perfectCore_perfect _
    have hSB : (T ⊓ K).subgroupOf K ≤
        Subgroup.normalizer ((LOf L V₂).subgroupOf K : Set ↥K) := by
      intro s hs
      rw [Subgroup.mem_normalizer_iff]
      intro b
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp (T_le_normalizer_lOf h.normal
        (IsVi.le_normalizer hV₂) (Subgroup.mem_subgroupOf.mp hs).1) b
    have hB4 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥((LOf L V₂).subgroupOf K) ⧸ CFSG.pCore 2 ↥((LOf L V₂).subgroupOf K) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F) := by
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inr rfl) hV₂
      exact ⟨F, inferInstance, inferInstance, hF, ⟨(quotPCoreSubgroupOfEquiv hLK).trans e⟩⟩
    obtain ⟨r, hr, hρr⟩ := hB _ _ hSyl hSB hperf hB4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP : (pCoreOf 2 ((LOf L V₂).subgroupOf K)).map K.subtype ≤ pCoreOf 2 (LOf L V₂) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans hmap.le) ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map _)
      calc LOf L V₂ = ((LOf L V₂).subgroupOf K).map K.subtype := hmap.symm
        _ ≤ _ := (Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)).trans
          (Subgroup.le_normalizer_map _)
    have hrC := Subgroup.centralizer_le hU₂
      (pCoreOf_lOf_le_centralizer hL3 hLp hLg h1102 h hV₂ (hP ⟨r, hr, rfl⟩))
    apply hρr
    ext v
    change ((conjV U r (hKN r.2) v : ↥U) : G) = v
    have hcomm : (v : G) * r = r * v := Subgroup.mem_centralizer_iff.mp hrC v v.2
    rw [conjV_apply_coe, ← hcomm, mul_inv_cancel_right]
  · exact Or.inl ⟨hn, hA7, fun y hy hodd => hρ y (hZ y hy hodd)⟩
  · exact Or.inr ⟨hn, hnq, fun y hy hodd => hρ y (hF y hy hodd)⟩

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
