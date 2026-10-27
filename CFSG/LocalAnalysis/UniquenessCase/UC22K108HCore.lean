module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108HLe
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rq
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rS207
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rp
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]


theorem uc22p22r_hall_core_H207 (D : Data G) (hK : F10.K108H207) (h201 : S20_1_124 D) (h207 : S20_7 D)
    (h1930 : H1930 D) {H : Subgroup G} (hH : H ∈ hSet D.T D.M) {L K B X : Subgroup G}
    (hL : L ∈ calLOf D.T D.M H) (hKc : K ∈ calC L) (hKM : ¬ K ≤ D.M) (hBM : B ≤ D.M)
    (hBK : B ≤ normalizer (K : Set G)) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBo : Odd (Nat.card B))
    (hBT : Permutes B D.T) (hBr : ∀ r : ℕ, r.Prime → r ∣ Nat.card B → CFSG.Open.pRank r B ≤ 2)
    (hXB : X ≤ B) (hXp : (Nat.card X).Prime) (hX2 : Nat.card X ≠ 2) (hU : X ∈ uniqueSet D.M) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.card X).Prime := ⟨hXp⟩
  haveI hcyc : IsCyclic ↥X := isCyclic_of_prime_card rfl
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  set x : G := (g : G) with hxdef
  have hX : X = Subgroup.zpowers x := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨i, by simpa using congrArg Subtype.val hi⟩
    · intro hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact X.zpow_mem g.2 i
  have hxo : orderOf x = Nat.card X := by
    rw [← Nat.card_zpowers, ← hX]
  have hxB : x ∈ B := hXB g.2
  have hU' : Subgroup.zpowers x ∈ uniqueSet D.M := hX ▸ hU
  obtain ⟨hKsub, -⟩ := uc22p22r_K_subnormal hL hKc
  have hOinf : OInf H ≤ D.M := (h201 h1930 H hH).2.2
  have hTH : D.T ≤ H := hH.1
  have hshape := uc22p22r_shape207 D h207 h1930 hL.1 hKc
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    uc22p22r_fo_sylow_inf (D.sylowG.of_le hTH le_top) hKsub
  have hBm : ∀ u ∈ B, u ^ Nat.card B = 1 := fun u hu => by
    have h1 : (⟨u, hu⟩ : ↥B) ^ Nat.card ↥B = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow] at h2
    exact h2
  have hperm : Permutes B (D.T ⊓ K) := uc22p22r_permutes_inf_odd hBo hBm hBK D.sylowM.isPGroup hBT
  have hO2 : pCoreOf 2 K ≤ D.M := (uc22p22r_pCoreOf_le_oinf hKsub).trans hOinf
  have hZ : ∀ k : ↥K, uc22p22rPsi K k = 1 → (k : G) ∈ D.M := by
    intro k hk
    have hkZ : k ∈ uc22p22rZK K := by
      rw [uc22p22rZK_eq_ker]
      exact MonoidHom.mem_ker.2 hk
    exact hOinf (uc22p22rZK_le_oinf hKsub ⟨k, hkZ, rfl⟩)
  have h0 : ∀ Y : Subgroup G, Subgroup.zpowers x ≤ Y → Y ≤ D.M → ∀ n ∈ K ⊔ B,
      n ∈ normalizer (Y : Set G) → n ∈ D.M := by
    intro Y hXY hYM n _ hnY
    apply uc22p22r_mem_of_conj_mem_of_unique D hU'
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnY) x).1 (hXY (Subgroup.mem_zpowers x))
    exact hYM (by simpa using h1)
  have hstar : ∀ g ∈ K ⊔ B, (∀ y ∈ Subgroup.zpowers x, g⁻¹ * y * g ∈ D.M) → g ∈ D.M :=
    fun g _ hy => uc22p22r_mem_of_conj_le_of_unique D hU' hy
  exact hKM (uc22p22r_le_of_k108H207_hall hK hXp hX2 hxo hxB hBK hBc hBo hBr hKc.2.2 hshape hSyl hperm
    (inf_le_left.trans D.sylowM.le) hBM hO2 hZ h0 hstar)

theorem uc22p22r_core211L_of_count_H207 (D : Data G) (Ch : Choice2011 G) (hK : F10.K108H207) (h201 : S20_1_124 D)
    (h207 : S20_7 D) (hcount : H1930 D → ∀ L ∈ calL D.T D.M, ∀ K₁ ∈ calC L, ∀ K₂ ∈ calC L, ∀ K₃ ∈ calC L,
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃) : Core211L D Ch := by
  intro h1930 _ X hX H hH hXTH L hL
  obtain ⟨hp, hp2, -, ⟨A, ⟨hAY, hAo, k, hk⟩, hAc⟩, hrank, hU⟩ := hX
  by_contra hLM
  haveI : Fact (Nat.card X).Prime := ⟨hp⟩
  haveI hcyc : IsCyclic ↥X := isCyclic_of_prime_card rfl
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  set x : G := (g : G) with hxdef
  have hX : X = Subgroup.zpowers x := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨i, by simpa using congrArg Subtype.val hi⟩
    · intro hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact X.zpow_mem g.2 i
  have hxo : orderOf x = Nat.card X := by
    rw [← Nat.card_zpowers, ← hX]
  have hXM : X ≤ D.M := hU.1
  have hxX : x ∈ X := g.2
  have hxH : x ∈ H := hXTH (Subgroup.mem_sup_left hxX)
  have hUx : ∀ h ∈ H, h⁻¹ * x * h ∈ D.M → h ∈ D.M := fun h _ hh =>
    uc22p22r_mem_of_conj_mem_of_unique D (hX ▸ hU) hh
  have hxL := uc22p22r_normalizes_calL D h201 h1930 hH hL hLM hp hxo hxH (hXM hxX) hUx
  have hXL : X ≤ normalizer (L : Set G) := by
    rw [hX]
    exact Subgroup.zpowers_le.2 hxL
  have hYL : X ⊔ D.T ≤ normalizer (L : Set G) := sup_le hXL hL.1.1
  have hXp : IsPGroup (Nat.card X) X := IsPGroup.of_card (n := 1) (by rw [pow_one])
  obtain ⟨y, hyY, hy⟩ := uc22p22r_exists_conj_le hp hp2 hXp le_sup_left hk
  set A' : Subgroup G := A.map (MulAut.conj y).toMonoidHom with hA'def
  have hXA' : X ≤ A' := fun z hz => ⟨y⁻¹ * z * y, hy z hz, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hA'Y : A' ≤ X ⊔ D.T := by
    rintro _ ⟨a, ha, rfl⟩
    show y * a * y⁻¹ ∈ X ⊔ D.T
    exact (X ⊔ D.T).mul_mem ((X ⊔ D.T).mul_mem hyY (hAY ha)) ((X ⊔ D.T).inv_mem hyY)
  have hA'card : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hA'o : Odd (Nat.card A') := hA'card ▸ hAo
  have hYcard : Nat.card ↥(X ⊔ D.T) = Nat.card A' * 2 ^ k := by
    rw [hA'card, ← hk]
    exact uc22p22r_card_eq_mul_index hAY
  have hTY : CFSG.ABGLocalTools.IsSylowOf 2 D.T (X ⊔ D.T) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact D.sylowG.of_le le_sup_right le_top
  have hA'T : Permutes A' D.T := uc22p22r_permutes_of_hall hA'Y hA'o hYcard hTY
  have hA'c : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hab : a * b = b * a := congrArg Subtype.val (hAc.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, hab]
  have hA'r : ∀ r : ℕ, r.Prime → r ∣ Nat.card A' → CFSG.Open.pRank r A' ≤ 2 := by
    intro r hr hrd
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hA'o) (even_iff_two_dvd.2 hrd)
    have hrY : r ∈ piSet (X ⊔ D.T) := ⟨hr, hrd.trans (Subgroup.card_dvd_of_le hA'Y)⟩
    exact (CFSG.SectionRank.pRank_mono hr.one_lt hA'Y).trans (hrank r hrY hr2)
  have hA'M : A' ≤ D.M := hA'Y.trans (sup_le hXM D.sylowM.le)
  obtain ⟨K, hKc, -, hKM⟩ := uc22p22r_exists_calC_not_le D hL.1 hLM
  have hA'K := uc22p22r_le_normalizer_calC_of_odd (hA'Y.trans hYL) hA'o (hcount h1930 L hL.1) hKc
  exact uc22p22r_hall_core_H207 D hK h201 h207 h1930 hH hL hKc hKM hA'M hA'K hA'c hA'o hA'T hA'r hXA' hp hp2 hU

theorem uc22p22r_core211L_of_k108H207 (D : Data G) (Ch : Choice2011 G) (hK : F10.K108H207)
    (h201 : S20_1_124 D) (h207 : S20_7 D) : Core211L D Ch :=
  uc22p22r_core211L_of_count_H207 D Ch hK h201 h207 fun h1930 L hL K₁ h₁ K₂ h₂ K₃ h₃ =>
    uc22p22r_calC_card_le_two D h207 h1930 hL h₁ h₂ h₃

theorem uc22p22r_s21_1_of_k108H207 (D : Data G) (Ch : Choice2011 G) (hK : F10.K108H207)
    (h201 : S20_1_124 D) (h204 : S20_4 D) (h207 : S20_7 D) (h640 : UC6.R6_40_2 D) : S21_1 D Ch :=
  uc22p21e_s21_1_of D Ch h204 h640 (uc22p22r_core211L_of_k108H207 D Ch hK h201 h207)

end CFSG.LocalAnalysis.UniquenessCase.UC22
