module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinFrameStatements
import CFSG.Assembly.GL83StatedBridge
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.StandardType.GGTableBLinear
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalDefs
import CFSG.LocalAnalysis.StandardType.GGTwAutBasic
import CFSG.LocalAnalysis.StandardType.GGTwSLRank
import CFSG.LocalAnalysis.StandardType.GGK1ScLin
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Res
import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsLinBound

public section

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l02lfr_center_eq_bot {K : Type} [Field K] [CharP K 2] (d : ℕ) :
    Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply (TypeA.recipeEquiv d K).injective
  rw [map_one]
  have hz' : TypeA.recipeEquiv d K z ∈ Subgroup.center (projectiveSL d K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := (TypeA.recipeEquiv d K).surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
  rw [SlNsRootGen.center_projectiveSL_eq_bot_charTwo, Subgroup.mem_bot] at hz'
  exact hz'

private theorem l02lfr_linConjAut_injective {K : Type} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (hK : Nat.card K = 2) : Function.Injective (TableB.linConjAut (Fin d) K) := by
  have hunits : Subsingleton Kˣ := by
    have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    exact (Nat.card_eq_one_iff_unique.mp hcard).1
  have hcenter : Subgroup.center (GL (Fin d) K) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rw [eq_bot_iff]
    rintro _ ⟨u, rfl⟩
    rw [@Subsingleton.elim Kˣ hunits u 1, map_one]
    exact Subgroup.mem_bot.mpr rfl
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have hAc : A ∈ Subgroup.center (GL (Fin d) K) :=
    linConjAut_ker_le_center (K := K) hd hA
  rw [hcenter] at hAc
  exact Subgroup.mem_bot.mp hAc

private theorem l02lfr_sl_one_subsingleton {K : Type} [Field K] :
    Subsingleton (LargeEvenSLGroup (Fin 1) K) := by
  refine ⟨fun A B => Subtype.ext ?_⟩
  have hmem : ∀ A : LargeEvenSLGroup (Fin 1) K, (A : GL (Fin 1) K) = 1 := by
    intro A
    have hdet : ((A : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K).det = 1 :=
      CFSG.Open.StatedAPI.det_of_mem_statedSL (by
        rw [← largeEvenSLGroup_eq_statedSL]
        exact A.2)
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.det_fin_one] using hdet
  rw [hmem A, hmem B]

theorem linCardEEq_holds :
    LinCardEEq := by
  intro G _ _ H E r t ε K _ _ _ θ hdt hK hperf hE hEN hI hSC hdisc h33
  classical
  have hεlt : ε.val < 2 := ε.isLt
  have hbot : E ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (H : Set G) := hx.2
    have hx3 : x ^ 3 = 1 := hE.2 x hx.1
    have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.centralizer (H : Set G))) :=
      (Nat.prime_three.coprime_iff_not_dvd).mpr hdisc
    have hdvdC : orderOf x ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hxC
    have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hord1 : orderOf x = 1 :=
      (Nat.coprime_comm.mp (hcop.coprime_dvd_right hdvdC)).eq_one_of_dvd hdvd3
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hord1)
  have hunits : Subsingleton Kˣ := by
    have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    exact (Nat.card_eq_one_iff_unique.mp hcard).1
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      exact congrArg Units.val (@Subsingleton.elim Kˣ hunits (Units.mk0 c hc) 1)
  have hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0 := by
    intro c hc
    rcases h01 c with rfl | rfl
    · norm_num at hc
    · exact ggTw_cast_three_ne_zero (K := K) (by linear_combination hc)
  have hSLmem : ∀ A : GL (Fin (r + 1)) K, A ∈ LargeEvenSLGroup (Fin (r + 1)) K := by
    intro A
    rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.mem_statedSL_iff]
    simpa using congrArg Units.val
      (@Subsingleton.elim Kˣ hunits (Matrix.GeneralLinearGroup.det A) 1)
  have hlow : 3 ^ t ≤ Nat.card ↥E := by
    by_cases ht3 : t ≤ 3
    · exact le_trans (Nat.pow_le_pow_right (by norm_num) ht3) h33
    · have ht4 : 4 ≤ t := by omega
      have hkerGamma : (ggGamma H hEN).ker = ⊥ := by
        rw [eq_bot_iff]
        intro b hb
        rw [MonoidHom.mem_ker, ggGamma_eq_one_iff] at hb
        have hb' : (b : G) ∈ E ⊓ Subgroup.centralizer (H : Set G) := ⟨b.2, hb⟩
        rw [hbot] at hb'
        rw [Subgroup.mem_bot]
        exact Subtype.ext (Subgroup.mem_bot.mp hb')
      have hcardGamma : Nat.card (ggGamma H hEN).range = Nat.card ↥E := by
        have h := Subgroup.card_ker_mul_card_range (ggGamma H hEN)
        rw [hkerGamma] at h
        simpa using h
      have hcard3 : 3 ^ 3 ≤ Nat.card (ggGamma H hEN).range := by
        rw [hcardGamma]
        exact h33
      have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 3) (by norm_num)
        (Bs := E) (X := H) hE hSC hperf θ hEN hI hcard3 hcard3
      have hZ : Subgroup.center
          (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)) = ⊥ :=
        l02lfr_center_eq_bot (K := K) (r + 1)
      have hIinner : ∀ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) Set.univ,
          φ ^ 3 = 1 → φ ∈ Set.range (MulAut.conj :
            LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K) →*
              MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K))) := by
        intro φ hφ _
        obtain ⟨A, rfl⟩ := TableB.exists_eq_linConjAut hφ
        exact ⟨((⟨A, hSLmem A⟩ : LargeEvenSLGroup (Fin (r + 1)) K) :
          LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)),
          (TableB.linConjAut_of_mem A (hSLmem A)).symm⟩
      have hcp : GGCenterPrime 3
          (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)) :=
        ggCenterPrime_linear_gcd (K := K) (d := r + 1) (p := 3)
          (by omega) (by norm_num) (by norm_num) (by
            rintro ⟨-, h3⟩
            rw [hK] at h3
            norm_num at h3)
      have hrank : GGSelfCentRankGE 3 t
          (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)) := by
        refine ggTwSL_scRank_rec (K := K) (d := r + 1) (r := t) (by omega) ?_ ?_
        · constructor <;> omega
        · simp [hK]
      have hSCR := ggTorusSCRank_of_selfCentRankGE (p := 3) (r := t) Nat.prime_three
        hZ hIinner hcp hrank
      obtain ⟨hψ, hkerψ, hperfH, hA, hAI, -, -, hself⟩ := hTB
      have hle : 3 ^ t ≤ Nat.card (ggGamma H hEN).range :=
        hSCR ↥H (ggQuotHom θ) hψ hkerψ hperfH (ggGamma H hEN).range hA hAI hself
      rwa [hcardGamma] at hle
  have hupper : Nat.card ↥E ≤ 3 ^ t := by
    let R := LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)
    let κ : GL (Fin (r + 1)) K →* MulAut R := TableB.linConjAut (Fin (r + 1)) K
    let g : ↥E →* MulAut R := (ggLAut H θ).comp (Subgroup.inclusion hEN)
    have hgker : g.ker = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      rw [MonoidHom.mem_ker] at hb
      change ggLAut H θ ⟨(b : G), hEN b.2⟩ = 1 at hb
      have hcent : (b : G) ∈ Subgroup.centralizer (H : Set G) :=
        mem_centralizer_of_ggLAut_eq_one H θ hperf hb
      have hmem : (b : G) ∈ E ⊓ Subgroup.centralizer (H : Set G) := ⟨b.2, hcent⟩
      rw [hbot] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    by_cases h2 : 2 ≤ r + 1
    · have hκinj : Function.Injective κ :=
        l02lfr_linConjAut_injective (K := K) h2 hK
      have hle : g.range ≤ κ.range := by
        rintro _ ⟨b, rfl⟩
        obtain ⟨A, hA⟩ := TableB.exists_eq_linConjAut (hI (b : G) b.2)
        exact ⟨A, hA.symm⟩
      have hgcard : Nat.card ↥E = Nat.card g.range := by
        have h := Subgroup.card_ker_mul_card_range g
        rw [hgker] at h
        simpa using h.symm
      let P : Subgroup (GL (Fin (r + 1)) K) := g.range.comap κ
      have hPmap : P.map κ = g.range := Subgroup.map_comap_eq_self hle
      have hPcard : Nat.card P = Nat.card ↥E := by
        have h1 : Nat.card (P.map κ) = Nat.card P :=
          Subgroup.card_map_of_injective hκinj
        rw [hPmap] at h1
        exact h1.symm.trans hgcard.symm
      have hcommg : ∀ u ∈ g.range, ∀ v ∈ g.range, u * v = v * u := by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg g (hE.1.is_comm.comm x y)
      have hpowg : ∀ u ∈ g.range, u ^ 3 = 1 := by
        rintro _ ⟨x, rfl⟩
        have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hE.2 (x : G) x.2)
        rw [← map_pow, hx3, map_one]
      have hPcomm : IsMulCommutative ↥P := by
        refine ⟨⟨fun A B => ?_⟩⟩
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        apply hκinj
        rw [map_mul, map_mul]
        exact hcommg (κ (A : GL (Fin (r + 1)) K)) A.2
          (κ (B : GL (Fin (r + 1)) K)) B.2
      have hPexp : ∀ A ∈ P, A ^ 3 = 1 := by
        intro A hA
        apply hκinj
        rw [map_pow, map_one]
        exact hpowg (κ A) hA
      have hP : IsElemAbelian 3 P := ⟨hPcomm, hPexp⟩
      have hcommP : ∀ g ∈ P, ∀ h ∈ P, g * h = h * g := by
        intro g hg h hh
        exact congrArg Subtype.val (hPcomm.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
      have hbound : Nat.card P ≤ 3 ^ (Fintype.card (Fin (r + 1)) / 2) :=
        card_le_pow_half_gl (K := K) (ι := Fin (r + 1))
          (ggTw_cast_three_ne_zero (K := K)) hω P hcommP hPexp
      rw [Fintype.card_fin] at hbound
      have hdt' : (r + 1) / 2 = t := by
        have hε : ε.val = 0 ∨ ε.val = 1 := by omega
        rcases hε with h0 | h1 <;> omega
      rw [hdt'] at hbound
      rwa [hPcard] at hbound
    · have hr0 : r + 1 = 1 := by omega
      have hSL1 : Subsingleton (LargeEvenSLGroup (Fin 1) K) :=
        l02lfr_sl_one_subsingleton (K := K)
      have hRsub : Subsingleton R := by
        dsimp only [R]
        rw [hr0]
        exact @Quotient.instSubsingletonQuotient _ _ hSL1
      have hMulAutSub : Subsingleton (MulAut R) := by
        refine ⟨fun f g => MulEquiv.ext fun x => ?_⟩
        exact @Subsingleton.elim R hRsub (f x) (g x)
      have htop : g.ker = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [MonoidHom.mem_ker]
        exact @Subsingleton.elim (MulAut R) hMulAutSub (g x) 1
      have hbotE : (⊥ : Subgroup ↥E) = ⊤ := by rw [← hgker, htop]
      have hEsingle : Subsingleton ↥E := by
        refine ⟨fun x y => ?_⟩
        have hx : x = 1 := by
          have hmem : x ∈ (⊥ : Subgroup ↥E) := by
            rw [hbotE]
            exact Subgroup.mem_top x
          exact Subgroup.mem_bot.mp hmem
        have hy : y = 1 := by
          have hmem : y ∈ (⊥ : Subgroup ↥E) := by
            rw [hbotE]
            exact Subgroup.mem_top y
          exact Subgroup.mem_bot.mp hmem
        rw [hx, hy]
      have hcardE1 : Nat.card ↥E = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨hEsingle, ⟨1⟩⟩
      have ht0 : t = 0 := by omega
      rw [hcardE1, ht0, pow_zero]
  exact le_antisymm hupper hlow

end CFSG.StandardType.GGQ2Frame.LinPlacement
