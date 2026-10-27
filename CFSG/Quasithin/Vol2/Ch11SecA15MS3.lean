module

public import CFSG.Quasithin.Vol2.Ch11SecA15MS2
public import CFSG.Quasithin.Vol2.Ch11SecA15MS
public import CFSG.Quasithin.Vol2.Ch11SecAVi2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

omit [Finite G] in
theorem lOf_le_L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left

theorem inf_L_le_lOf_sup_ROf (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) : T ⊓ L ≤ LOf L V₁ ⊔ ROf T L V₁ := by
  have hLV := L_le_normalizer_fsuV h
  have hUV := IsVi.le_fsuV hU
  have hflag := isFlagW_of_isVi h hU
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  have hP : autOn (T ⊓ L) (fsuV T I) ≤
      perfectCore (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I))) := by
    rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
      ⟨-, -, -, -, -, hG2⟩
    · exact hF.sylowSL3 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
    · exact hF.sylowSp4 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
    · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
      exact hF.sylowG2 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
  intro t ht
  have htV : t ∈ Subgroup.normalizer (fsuV T I : Set G) := hLV ht.2
  have hg := hP (conjV_mem_autOn ht htV)
  rw [← autOn_inf_normalizer hUV, ← autOn_perfectCore (inf_le_left.trans hLV)] at hg
  obtain ⟨l, hl, hlV, hlt⟩ := mem_autOn_iff.mp hg
  have hc : l⁻¹ * t ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem (lOf_le_L hl)) ht.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) hlt
    simp only [conjV_apply_coe] at h1
    calc v * (l⁻¹ * t) = l⁻¹ * (l * v * l⁻¹) * t := by group
      _ = l⁻¹ * (t * v * t⁻¹) * t := by rw [h1]
      _ = l⁻¹ * t * v := by group
  rw [centralizer_eq_pCoreOf h1102 h] at hc
  have := Subgroup.mul_mem_sup hl (pCoreOf_le_ROf (V₁ := V₁) h hc)
  simpa using this

theorem lOf_sup_ROf_lt (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) : LOf L V₁ ⊔ ROf T L V₁ < L ⊔ ROf T L V₁ := by
  refine lt_of_le_of_ne (sup_le_sup_right lOf_le_L _) fun heq => ?_
  have hLM := mem_cComp_of_le h le_rfl (sup_le Subgroup.le_normalizer h.normal)
  have hRL₁ : ROf T L V₁ ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    (ROf_le_T h).trans (T_le_normalizer_lOf h.normal (IsVi.le_normalizer hU))
  have hLL : L = LOf L V₁ := eq_of_le_sup_of_perfect lOf_le_L (perfect_of_mem_cComp hLM)
    isPGroup_ROf hRL₁ (heq ▸ le_sup_left)
  have hLV₁ : L ≤ Subgroup.normalizer (V₁ : Set G) := by
    rw [hLL]
    exact (perfectCore_le _).trans inf_le_right
  obtain ⟨_, hirr, -, -, -⟩ := h1102 G T L I n h
  have hn : 1 ≤ n := by have := h.one_lt; omega
  rcases hirr.2.2.2.2.2 V₁ (IsVi.cV_le hU) (IsVi.le_fsuV hU) hLV₁ with h1 | h1
  · have h2 := IsVi.relIndex_eq hU
    rw [h1, Subgroup.relIndex_self, mul_one] at h2
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  · obtain ⟨-, -, V₃, -, -, h3, -, -, -, -, -⟩ := exists_isVi hN h1102 h
    have hle : V₃ ≤ V₁ := h1 ▸ IsVi.le_fsuV h3
    have hd := Subgroup.relIndex_mul_relIndex _ _ _ (IsVi.cV_le h3) hle
    rw [IsVi.relIndex_eq h3, IsVi.relIndex_eq hU] at hd
    have hdvd : 2 ^ (n * 3) ∣ 2 ^ (n * 1) := ⟨_, hd.symm⟩
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    omega

theorem ms2 (hF : Facts15) (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) :
    ∃ H' : Subgroup G, H' < L ⊔ ROf T L V₁ ∧ ¬ 2 ∣ H'.relIndex (L ⊔ ROf T L V₁) ∧
      ROf T L V₁ = pCoreOf 2 H' := by
  refine ⟨LOf L V₁ ⊔ ROf T L V₁, lOf_sup_ROf_lt hN h1102 h hU, ?_,
    (pCoreOf_lOf_sup_ROf h hU).symm⟩
  have hS := isSylowTwoOf_inf_msG0 (V₁ := V₁) h
  have hle1 : T ⊓ (L ⊔ ROf T L V₁) ≤ LOf L V₁ ⊔ ROf T L V₁ :=
    (inf_msG0_le h).trans (sup_le (inf_L_le_lOf_sup_ROf hF h1102 h hU) le_sup_right)
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle1 (lOf_sup_ROf_lt hN h1102 h hU).le
  intro h2
  apply hS.2.2
  change 2 ∣ (T ⊓ (L ⊔ ROf T L V₁)).relIndex (L ⊔ ROf T L V₁)
  rw [← hmul]
  exact dvd_mul_of_dvd_right h2 _

theorem isMSPair (h331 : Stmt3_3_1) (hF : Facts15) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hNot : ¬ Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    IsMSPair (L ⊔ ROf T L V₁) (ROf T L V₁) :=
  ⟨⟨sqtkGroup_of_le_normalizer h331 h (sup_le Subgroup.le_normalizer (ROf_le_normalizer_L h)),
    charTwo_msG0 h, L, L_mem_cComp_msG0 h, coe_msG0 h, rankTwo_L hF h1102 h⟩,
    Or.inl (ms2 hF hN h1102 h hU), ms3_of_not_le h331 h hNot⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
