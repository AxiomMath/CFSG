module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs
public import CFSG.Quasithin.Vol2.Ch4Sec2NoSum2

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}

theorem exists_mem_normalizer_not_mem {P R : Subgroup G} (hP : IsPGroup 2 ↥P) (hRP : R < P) :
    ∃ s ∈ P, s ∈ Subgroup.normalizer (R : Set G) ∧ s ∉ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : R.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have hPR : P ≤ R := fun x hx =>
      Subgroup.mem_subgroupOf.mp (h ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥P))
    exact absurd hRP (not_lt_of_ge hPR)
  have hN := normalizerCondition_of_isNilpotent (G := ↥P) (R.subgroupOf P) hlt
  obtain ⟨x, hxN, hxR⟩ := SetLike.exists_of_lt hN
  refine ⟨x, x.2, ?_, fun h => hxR (Subgroup.mem_subgroupOf.mpr h)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ P
  · have := Subgroup.mem_normalizer_iff.mp hxN ⟨y, hy⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hyR
      exact absurd (hRP.le hyR) hy
    · intro hxy
      have hxyP : (x : G) * y * (x : G)⁻¹ ∈ P := hRP.le hxy
      have : y ∈ P := by
        have h1 := P.mul_mem (P.mul_mem (P.inv_mem x.2) hxyP) x.2
        simpa [mul_assoc] using h1
      exact absurd this hy

theorem I_le_normalizer_sup (hIH : I ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    I ≤ Subgroup.normalizer ((K ⊔ pCoreOf 2 I : Subgroup G) : Set G) := by
  intro i hi
  exact mem_normalizer_sup (hHK (hIH hi)) (le_normalizer_pCoreOf 2 I hi)

theorem zAt_alphaV_ne_bot (A B Z : Subgroup G) (hZ : Z ≠ ⊥) :
    zAt A B Z (alphaV A B) ≠ ⊥ := by
  intro h
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
  have hmem : (Quotient.out ((1 : G) : G ⧸ A)) * (a : G) * (Quotient.out ((1 : G) : G ⧸ A))⁻¹ ∈
      zAt A B Z (alphaV A B) := ⟨a, a.2, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  apply ha1
  apply Subtype.ext
  simpa using hmem

theorem notLeKernelAt_of_parts (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h31 : Lemma31) (h32 : Lemma32) (hU : UZeroNeBot) (hL37 : Lemma37) (hAm : AmalgamData) :
    NotLeKernelAt := by
  intro G _ _ T M L Mm I H K m k hch hIV hb
  have hd : NoSumBigData G T M L Mm I H K m k := hch.1
  have hy : Hyp4_2_3 G T M L Mm I := hd.1
  have hIH : InM I H := hd.2.1
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  obtain ⟨hAB, -, hIB, -⟩ := hAm G T M L Mm I H K m k hch hIV
  obtain ⟨hHK, -⟩ := h32 G T M L Mm I H K m k hd
  obtain ⟨hRlt, hRC⟩ := h31 G T M L Mm I H K m k hd
  have hIN : I ≤ Subgroup.normalizer ((K ⊔ pCoreOf 2 I : Subgroup G) : Set G) :=
    I_le_normalizer_sup hIH.2 hHK
  have hNα : typeOne T M L I K (alphaV (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) :=
    ⟨rfl, SimpleGraph.Reachable.refl _⟩
  have hU₀ : uZero I K ≠ ⊥ := hU G T M L Mm I H K m k hd
  have hZ₁ := zAt_alphaV_ne_bot (K ⊔ pCoreOf 2 I) (gammaZero T M L I) _ hU₀
  have hZcore : zAt (K ⊔ pCoreOf 2 I) (gammaZero T M L I) (uZero I K)
      (alphaV (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) ≤
      coreInf (K ⊔ pCoreOf 2 I) (gammaZero T M L I) :=
    le_coreInf_of_forall_reachable_le_kernelAt (fun ε hε => hb _ ε hNα hε)
  have hN₀R : coreInf (K ⊔ pCoreOf 2 I) (gammaZero T M L I) ≤ pCoreOf 2 I := by
    have := coreInf_le (K ⊔ pCoreOf 2 I) (gammaZero T M L I)
    rwa [hAB] at this
  have hN₀2 : IsPGroup 2 ↥(coreInf (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) :=
    (pCoreOf_isPGroup 2 I).to_le hN₀R
  have hN₀ne : coreInf (K ⊔ pCoreOf 2 I) (gammaZero T M L I) ≠ ⊥ := fun h =>
    hZ₁ (le_bot_iff.mp (h ▸ hZcore))
  have hSX := sup_le_normalizer_coreInf (K ⊔ pCoreOf 2 I) (gammaZero T M L I)
  have hIX : I ≤ Subgroup.normalizer
      (coreInf (K ⊔ pCoreOf 2 I) (gammaZero T M L I) : Set G) :=
    fun i hi => mem_normalizer_coreInf_of_mem (hIN hi) (hIB hi)
  have hKX : K ≤ Subgroup.normalizer
      (coreInf (K ⊔ pCoreOf 2 I) (gammaZero T M L I) : Set G) :=
    le_sup_left.trans (le_sup_left.trans hSX)
  have hBX : gammaZero T M L I ≤ Subgroup.normalizer
      (coreInf (K ⊔ pCoreOf 2 I) (gammaZero T M L I) : Set G) :=
    le_sup_right.trans hSX
  have hX2 : pCoreOf 2 (Subgroup.normalizer
      (coreInf (K ⊔ pCoreOf 2 I) (gammaZero T M L I) : Set G)) ≠ ⊥ := fun h =>
    hN₀ne (le_bot_iff.mp (h ▸ le_pCoreOf_of_le_normalizer Subgroup.le_normalizer le_rfl hN₀2))
  have hXH := hL37 G T M L Mm I H K m k hch _ hIX hKX hX2
  have hrP : rPlus T M L = pCoreOf 2 (L ⊔ T) := by
    rw [hy.pCoreOf_sup_eq_inf, hc.conjClosure_eq]
  obtain ⟨s, hsP, hsN, hsR⟩ := exists_mem_normalizer_not_mem (P := rPlus T M L)
    (hrP ▸ pCoreOf_isPGroup 2 (L ⊔ T)) hRlt
  have hsB : s ∈ gammaZero T M L I := ⟨⟨hsP.2, hsN⟩, hRC hsP⟩
  have hsH : s ∈ H := hXH (hBX hsB)
  have hsO : s ∈ pCoreOf 2 (L ⊔ T) := hrP ▸ hsP
  exact hsR (hc.inf_le_pCoreOf_I hy h37 h38 h39 ⟨hsO, hsH⟩)

end CFSG.Quasithin.H13.Ch4.NSB
