module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteenSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteenFour
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.ABGLocalTools Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace ElevenFourteen

theorem normal_inf_subgroupOf_of_le_normalizer {P C M : Subgroup G} (hPM : P ≤ M)
    (hMC : M ≤ normalizer (C : Set G)) : ((P ⊓ C).subgroupOf P).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hyC := hMC (hPM hy)
  constructor
  · rintro ⟨hz1, hz2⟩
    exact ⟨P.mul_mem (P.mul_mem hy hz1) (P.inv_mem hy), (mem_normalizer_iff.1 hyC z).1 hz2⟩
  · rintro ⟨hz1, hz2⟩
    refine ⟨?_, (mem_normalizer_iff.1 hyC z).2 hz2⟩
    have := P.mul_mem (P.mul_mem (P.inv_mem hy) hz1) hy
    simpa [mul_assoc] using this

theorem le_normalizer_ctilde {M V₀ V : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (hV₀ : M ≤ normalizer (V₀ : Set G)) : M ≤ normalizer (F11.CTilde M V₀ V : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact uc22p22q_ctilde_conj_mem hV hV₀ hm
  · intro hc
    have := uc22p22q_ctilde_conj_mem hV hV₀ (M.inv_mem hm) hc
    simpa [mul_assoc] using this

theorem one_lt_pRank_inf_centralizer (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup G}
    (hP : IsSylowOf p P D.M) :
    1 < CFSG.Open.pRank p (P ⊓ centralizer (V₀ : Set G)) := by
  obtain ⟨-, -, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hpP⟩
  have hPM : P ≤ D.M := hP.le
  have h3 : 3 ≤ CFSG.Open.pRank p P := (hx.three_le p hp).trans (uc22p22q_pRank_le_sylow hP)
  haveI hSn : ((P ⊓ centralizer (V₀ : Set G)).subgroupOf P).Normal :=
    normal_inf_centralizer_subgroupOf (hPM.trans hMV₀)
  have hcyc := eleven_four_one_of_sig D h61 hH hp hPM hP.isPGroup
  haveI hPn : (P.subgroupOf P).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact UCK.k31 (Q := P) (S := P ⊓ centralizer (V₀ : Set G)) (X := P ⊓ centralizer (V₀ : Set G))
    hpP hp2 hP.isPGroup h3 le_rfl inf_le_left hcyc inf_le_left inf_le_right
    (sup_eq_left.2 inf_le_left).symm

theorem eleven_fourteen_one (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) :
    ¬ D.M ⊓ centralizer (V₀ : Set G) ≤ F11.CTilde D.M V₀ V := by
  intro hle
  obtain ⟨hV, hV₀V, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hpP⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf p D.M
  have h1 := one_lt_pRank_inf_centralizer D hx h61 hH hp hP
  have hV₀exp : ∀ d ∈ V₀, d ^ 2 = 1 := fun d hd => hV.2.2.2.2 d (hV₀V hd)
  have hSV : P ⊓ centralizer (V₀ : Set G) ≤ D.M ⊓ centralizer (V : Set G) := fun e he =>
    ⟨hP.le he.1, inf_ctilde_inf_centralizer_le hpP hp2 hP.isPGroup hV₀exp
      ⟨⟨he.1, hle ⟨hP.le he.1, he.2⟩⟩, he.2⟩⟩
  have h2 := uc22p22n_pRank_centralizer_le_one D h61 hV hH.2.1 p hp
  have h3 := CFSG.SectionRank.pRank_mono hpP.one_lt hSV
  omega

theorem eleven_fourteen_two (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) {X : Subgroup G} (hXM : X ≤ D.M)
    (hCX : D.M ⊓ centralizer (V : Set G) ≤ X)
    (hMX : (X : Set G) * (F11.CTilde D.M V₀ V : Set G) = (D.M : Set G)) :
    UniqueMax D.M X := by
  obtain ⟨hV, hV₀V, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hpP⟩
  obtain ⟨P, hP, hPX⟩ := exists_isSylowOf_inf (p := p) hXM
  have hPM : P ≤ D.M := hP.le
  have h3 : 3 ≤ CFSG.Open.pRank p P := (hx.three_le p hp).trans (uc22p22q_pRank_le_sylow hP)
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := uc22p22q_ctilde_le
  have hMC := le_normalizer_ctilde hV.2.2.1 hMV₀
  have hPeq := eq_sup_inf_of_mul_eq hXM hCM hMC hMX hP hPX
  haveI hQn : ((P ⊓ F11.CTilde D.M V₀ V).subgroupOf P).Normal :=
    normal_inf_subgroupOf_of_le_normalizer hPM hMC
  haveI hSn : ((P ⊓ centralizer (V₀ : Set G)).subgroupOf P).Normal :=
    normal_inf_centralizer_subgroupOf (hPM.trans hMV₀)
  have hcyc := eleven_four_one_of_sig D h61 hH hp hPM hP.isPGroup
  have hV₀exp : ∀ d ∈ V₀, d ^ 2 = 1 := fun d hd => hV.2.2.2.2 d (hV₀V hd)
  have hRY : (P ⊓ F11.CTilde D.M V₀ V) ⊓ (P ⊓ centralizer (V₀ : Set G)) ≤ P ⊓ X := by
    intro e he
    have hR : e ∈ centralizer (V : Set G) :=
      inf_ctilde_inf_centralizer_le hpP hp2 hP.isPGroup hV₀exp ⟨⟨he.1.1, he.1.2⟩, he.2.2⟩
    exact ⟨he.1.1, hCX ⟨hPM he.1.1, hR⟩⟩
  have hY : 1 < CFSG.Open.pRank p (P ⊓ X) :=
    UCK.k31 hpP hp2 hP.isPGroup h3 inf_le_left inf_le_left hcyc inf_le_left hRY hPeq
  have hYnc : ¬ IsCyclic (P ⊓ X : Subgroup G) := fun hc => by
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic hpP hc
    omega
  exact uniqueMax_of_le D.maxLocal
    (h61 p hp (P ⊓ X) (inf_le_left.trans hPM) hP.isPGroup.to_inf_left hYnc) inf_le_right hXM

end ElevenFourteen

theorem r1114_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) : R1114 D :=
  fun _ _ hH => ⟨ElevenFourteen.eleven_fourteen_one D hx h61 hH,
    fun _ hXM hCX hMX => ElevenFourteen.eleven_fourteen_two D hx h61 hH hXM hCX hMX⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
