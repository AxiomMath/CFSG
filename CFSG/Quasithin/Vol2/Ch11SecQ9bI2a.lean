module

public import CFSG.Quasithin.Vol2.Ch11SecA13Line2
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12c
public import CFSG.Quasithin.Vol2.Ch11SecA12Out

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₂ K : Subgroup G} {n : ℕ}

namespace C11P9B

theorem isMulCommutative_V2 (h : Hyp11 G T L I n) (hV₂ : IsVi T L I n 2 V₂) :
    IsMulCommutative ↥V₂ := by
  obtain ⟨hc, -⟩ := isElemAbelian_fsuV h
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h2 := hc.is_comm.comm (⟨a, IsVi.le_fsuV hV₂ a.2⟩ : ↥(fsuV T I)) ⟨b, IsVi.le_fsuV hV₂ b.2⟩
  have h3 : ((⟨a, IsVi.le_fsuV hV₂ a.2⟩ * ⟨b, IsVi.le_fsuV hV₂ b.2⟩ : ↥(fsuV T I)) : G) =
      ((⟨b, IsVi.le_fsuV hV₂ b.2⟩ * ⟨a, IsVi.le_fsuV hV₂ a.2⟩ : ↥(fsuV T I)) : G) :=
    congrArg Subtype.val h2
  exact h3

theorem card_V2_le (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n) (hV₂ : IsVi T L I n 2 V₂) :
    Nat.card ↥V₂ ≤ 2 ^ (3 * n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := Subgroup.relIndex_mul_card (H := fsuV T I ⊓ Subgroup.centralizer (L : Set G))
    (K := V₂)
  rw [inf_of_le_left (IsVi.cV_le hV₂), IsVi.relIndex_eq hV₂] at hmul
  have hA : Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 ^ n := by
    obtain ⟨-, -, h3, -, -⟩ := h1103 G T L I n h
    rcases h3 with ⟨hbot, -⟩ | ⟨-, -, hm, -⟩
    · rw [hbot, Subgroup.card_bot]
      exact Nat.one_le_two_pow
    · unfold E3.mQuot at hm
      rw [Subgroup.relIndex_bot_left] at hm
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((isPGroup_fsuV h).to_le
        (inf_le_left : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤ fsuV T I))
      rw [hk, padicValNat.prime_pow] at hm
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) hm
  calc Nat.card ↥V₂ = 2 ^ (n * 2) * Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer (L : Set G)) :=
        hmul.symm
    _ ≤ 2 ^ (n * 2) * 2 ^ n := Nat.mul_le_mul_left _ hA
    _ = 2 ^ (3 * n) := by ring

omit [Finite G] in
theorem perfect_top_of_mem_cComp {Y : Subgroup G} (hK : K ∈ cComp Y) :
    ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact perfect_of_mem_cComp hK

theorem modules3n_V2 (hFc : Facts12c) (hN : NatFacts) (hL3 : FactLineSL3) (hLp : FactLineSp4)
    (hLg : FactLineG2) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n)
    (hV₂ : IsVi T L I n 2 V₂) (hK : K ∈ cComp (Subgroup.normalizer (V₂ : Set G)))
    (hNK : Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₂ ≤ K) (hc : Concl1111 (↥K ⧸ CFSG.pCore 2 ↥K) n) :
    (n = 2 ∧ (IsAlt 7 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
        IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (alternatingGroup (Fin 7))) ∧
      ∀ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
        Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) → Odd (orderOf y) →
        (y : G) ∈ Subgroup.centralizer (V₂ : Set G)) ∨
    (n = 2 ∧ ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      ∀ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
        CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K) → Odd (orderOf y) →
        (y : G) ∈ Subgroup.centralizer (V₂ : Set G)) := by
  have hKN : K ≤ Subgroup.normalizer (V₂ : Set G) := le_of_mem_cComp hK
  have := isMulCommutative_V2 h hV₂
  set ρ : ↥K →* MulAut ↥V₂ := (conjAct V₂).comp (Subgroup.inclusion hKN) with hρdef
  have hρ : ∀ y : ↥K, ρ y = 1 → (y : G) ∈ Subgroup.centralizer (V₂ : Set G) := by
    intro y hy
    have hy' : conjV V₂ y (hKN y.2) = 1 := hy
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h2 := congrArg (fun φ : MulAut ↥V₂ => ((φ ⟨v, hv⟩ : ↥V₂) : G)) hy'
    simp only [conjV_apply_coe, MulAut.one_apply] at h2
    calc v * y = y * v * (y : G)⁻¹ * y := by rw [h2]
      _ = y * v := by group
  have hsq : ∀ w : ↥V₂, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w (IsVi.le_fsuV hV₂ w.2))
  have hρ1 : ρ ≠ 1 := by
    intro h1
    apply not_lOf_le_centralizer hL3 hLp hLg h1102 h hV₂
    intro l hl
    exact hρ ⟨l, hLK hl⟩ (by rw [h1]; rfl)
  rcases hFc.modules ↥K ↥V₂ hsq ρ n h.one_lt (card_V2_le h1103 h hV₂)
      (perfect_top_of_mem_cComp hK) hc hρ1 with hB | ⟨hn, hA7, hZ⟩ | ⟨hn, hnq, hF⟩
  · exfalso
    have hSyl := isSylowTwoOf_top_subgroupOf (isSylowTwoOf_inf_K h hV₂ hK hNK)
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
    have hrC := pCoreOf_lOf_le_centralizer hL3 hLp hLg h1102 h hV₂ (hP ⟨r, hr, rfl⟩)
    apply hρr
    ext v
    change ((conjV V₂ r (hKN r.2) v : ↥V₂) : G) = v
    have hcomm : (v : G) * r = r * v := Subgroup.mem_centralizer_iff.mp hrC v v.2
    rw [conjV_apply_coe, ← hcomm, mul_inv_cancel_right]
  · exact Or.inl ⟨hn, hA7, fun y hy hodd => hρ y (hZ y hy hodd)⟩
  · exact Or.inr ⟨hn, hnq, fun y hy hodd => hρ y (hF y hy hodd)⟩

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
