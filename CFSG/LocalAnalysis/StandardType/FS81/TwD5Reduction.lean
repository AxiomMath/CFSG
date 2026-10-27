module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Pieces
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Local
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Fus
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5OddCore
public import CFSG.LocalAnalysis.StandardType.FS81.ThmENineFour
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoBridgeDefs
import CFSG.LocalAnalysis.StandardType.FS81.MonoN0

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

theorem not_isCharTwoType_of_nineFourData {G : Type} [Group G] [Finite G]
    {B : Basis3 G (5 + 1)} {t : G} (h : NineFourData B t) : ¬ IsCharTwoType G := by
  obtain ⟨ht, -, -, hct, hO2, hconj0⟩ := h
  set s : Set G := Set.range (fun i : Fin 4 => B.b i.succ.succ) with hs
  have hgen : ∀ i : Fin 4, B.b i.succ.succ ∈ Subgroup.closure s := by
    intro i
    rw [hs]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (B.comm _ _).eq
  have hpow : ∀ a ∈ s, a ^ 3 = 1 := by
    rintro _ ⟨i, rfl⟩
    have h3 := pow_orderOf_eq_one (B.b i.succ.succ)
    rwa [B.ord] at h3
  have hE : IsElemAbelian 3 (Subgroup.closure s) :=
    IsElemAbelian.closure_of_commute hcomm hpow
  have hE1 : Subgroup.closure s ≠ ⊥ := by
    intro hbot
    have hmem := hgen ⟨0, by decide⟩
    rw [hbot] at hmem
    have h1 : B.b (Fin.succ (Fin.succ (0 : Fin 4))) = 1 := Subgroup.mem_bot.mp hmem
    have h3 := B.ord (Fin.succ (Fin.succ (0 : Fin 4)))
    rw [h1, orderOf_one] at h3
    omega
  have hEt : Subgroup.closure s ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have h2i : 2 ≤ (Fin.succ (Fin.succ i)).val := by
      simp only [Fin.val_succ]
      omega
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hct i.succ.succ h2i).symm
  have hconj : ∀ H ∈ Coprime.hyperplanes 3 (Subgroup.closure s),
      ∃ c ∈ Subgroup.centralizer ({t} : Set G), c * B.b 2 * c⁻¹ ∈ H := by
    rw [hs]
    exact hconj0
  exact not_isCharTwoType_of_hyperplane_conj ht hE hE1 hEt hO2 hconj

theorem t5NotMono_holds :
    ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
      ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → Fus42 B b₀ → OddCoreTrivial E →
        LocalOrthI B b₀ → False := by
  intro G _ _ b₀ K E hstd B hB hfus hodd hI
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbig⟩ := hstd.2.1
  obtain ⟨hspan, hb0, -⟩ := hB
  subst hspan
  exact false_of_normalizer_mono (by norm_num) B hb0 hfus hodd hbig hI.2

theorem ggSecFiveE6QTwoFS81Input_of_pieces (h2 : T5Fus42) (h5 : T5ThmA) (h9 : T5Nine) :
    GGSecFiveE6QTwoFS81Input := by
  have h0 := t5Canon_holds
  have h1 := t5Local_holds
  have h3 := t5OddCore_holds
  intro X _ _ hsimple hK b₀ K E hord hKle hKnorm hKcenter hKmark hKcyc hrank hconj
    hmax hb₀ hcard hbig
  have hyp : HypTwD5 b₀ K E :=
    ⟨hord, hKle, hKnorm, hKcenter, hKmark, hKcyc, hrank, hconj, hmax, hb₀, hcard, hbig⟩
  have hcanon : CanonTwD5 b₀ K E := h0 X b₀ K E hyp
  have hstd : StdTwD5 b₀ K E := ⟨hsimple, hyp, hcanon⟩
  obtain ⟨B, hB, hloc⟩ := h1 X b₀ K E hstd
  have hfus : Fus42 B b₀ := h2 X b₀ K E hstd B hB hloc
  have hodd : OddCoreTrivial E := h3 X b₀ K E hstd B hB hloc hfus
  rcases hloc with hI | hII
  · exact (t5NotMono_holds X b₀ K E hstd B hB hfus hodd hI).elim
  obtain ⟨B', hB', hrec⟩ := h5 X b₀ K E hstd B hB hII hfus hodd
  have hfus' : Fus42 B' b₀ := by
    unfold Fus42 at hfus ⊢
    rw [hB'.1]
    rw [hB.1] at hfus
    exact hfus
  intro hchar
  obtain ⟨t, ht⟩ := h9 X b₀ K E hstd hK hchar B' hB' hrec hfus'
  exact not_isCharTwoType_of_nineFourData ht hchar

theorem ggSecFiveE6QTwoFS81Input_of_open (h5 : T5ThmA) (h9 : T5Nine) :
    GGSecFiveE6QTwoFS81Input :=
  ggSecFiveE6QTwoFS81Input_of_pieces t5Fus42_holds
    h5 h9

end CFSG.StandardType.FrameRoute.FS81

end
