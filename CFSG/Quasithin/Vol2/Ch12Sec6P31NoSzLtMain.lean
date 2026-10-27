module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzLtE
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzLtMod
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzEq
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport

public section

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.F126 S126 S126P31
open CFSG.QuasithinUnique
open scoped IsMulCommutative

section Setting

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

attribute [local instance] commGroupOfFact

theorem map_rhoQ_star [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {X : Subgroup G} (hXH : X ≤ H) :
    (star H X).map (rhoQ h hIU) = autIH V₁ I H X := by
  rw [autIH_eq_map h hXH]
  unfold S126.star
  rw [Subgroup.map_map]
  rfl

theorem isSz_autIH_lt [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hKH : K ≤ H) {n : ℕ}
    (hSzN : IsSz n ↥(star H K)) (hs : IsSimpleGroup ↥(star H K))
    (hne : autIH V₁ I H K ≠ ⊥) : IsSz n ↥(autIH V₁ I H K) := by
  let π : ↥(star H K) →* MulAut ↥(tildeOf V₁ (conjClosure I H)) :=
    (rhoQ h hIU).comp (star H K).subtype
  have hrange : π.range = autIH V₁ I H K := by
    rw [← map_rhoQ_star h hIU hKH]
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hinj : Function.Injective π := by
    apply injective_of_isSimpleGroup
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ autIH V₁ I H K, y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hne ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    rw [← hrange] at hy
    obtain ⟨s, rfl⟩ := hy
    exact ⟨s, hy1⟩
  exact isSz_congr ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)) hSzN

end Setting

section Main

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

attribute [local instance] commGroupOfFact

theorem false_of_isSz_lt_w31
    (hSzE : A6.SzEnd) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1222 : Stmt12_2_2)
    {F : Frame126 T L V} (hH : Hyp126 G T L V) {H K : Subgroup G} (hIs : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (hne : conjClosure K T ≠ K) {n : ℕ}
    (hSz : IsSz n (starMod_w31 H K)) : False := by
  have h91 := h918.toHypF98.toHypF91
  have hHq : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian (pCoreOf_ne_bot h91)
  have hKc : K ∈ cComp H := h918.K_cComp
  have hKH : K ≤ H := le_of_mem_cComp hKc
  obtain ⟨E, -, hEodd, -, hES, hEC, hfpf⟩ :=
    exists_odd_normal_fpf_lt h1222 hH hIs h918 hne hHq h37 h38 hSz
  have hE3 : ∀ e ∈ E, ∃ k : ℕ, e ^ 3 ^ k = 1 :=
    isThreeGroup_of_odd_le_star h1222 F hH h918.T_le_H (le_sup_left.trans h918.L₁T_le_H)
      hH.hyp.sylow.1 hES hEodd
  have hSzN : IsSz n ↥(star H K) := isSz_star_lt h918 hSz
  have hs : IsSimpleGroup ↥(star H K) := isSimpleGroup_of_psl2_or_sz (Or.inr hSzN)
  obtain ⟨I, hV₁I, hIU, Wa, hWa, hirr⟩ := exists_isIrrPlusTildeU h918
  haveI hFI := factElem h918 hIU
  have hIT := isIrrPlusTildeT_of_ambient h918 hIU Wa hWa hirr
  have hirr' : subM F.V1 (conjClosure I H) I ∈
      IrrPlusOn (autIH F.V1 I H (conjClosure K T))
        (orbSup (autIH F.V1 I H T) (subM F.V1 (conjClosure I H) I)) (autIH F.V1 I H T) := hIT
  have hnt := hnt_of_irrSec h918 hIU hirr'.1.2.2.2.1
  have hneL : autIH F.V1 I H K ≠ ⊥ := by
    rw [autIH_eq_map h918 hKH]
    exact map_K_ne_bot h918 hIU hnt
  have hLSz : IsSz n ↥(autIH F.V1 I H K) := isSz_autIH_lt h918 hIU hKH hSzN hs hneL
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply le_antisymm
    · exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
    · exact le_conjClosure K T
  obtain ⟨-, hFive⟩ := F918_5' h918 hHq hne hV₁I hIU Wa hWa hirr hD36 hD37 hD321 hI5 h37 h38
  have h5 := hFive t htT htK
  obtain ⟨-, -, hprelim⟩ := five_prelim h918 hHq hne hIU hnt h37 h38
  obtain ⟨htT', -, hMp, -⟩ := hprelim t htT htK
  have htMp := autIH_T_le_normalizer h918 I htT'
  have hW2 : ∀ w : ↥(tildeOf F.V1 (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hFI.out.2 w.1 w.2)
  have hE3' : ∀ e ∈ E, ∃ k : ℕ, rhoQ h918 hIU e ^ 3 ^ k = 1 := by
    intro e he
    obtain ⟨k, hk⟩ := hE3 e he
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hfpf' : ∀ w : ↥(tildeOf F.V1 (conjClosure I H)), (∀ e ∈ E, rhoQ h918 hIU e w = w) →
      w = 1 := by
    intro w hw
    have hfix := hfpf (iotaQ h918 hIU w) (fun e he => by
      rw [psiH_iotaQ h918 hIU, hw e he])
    exact iotaQ_injective h918 hIU (hfix.trans (iotaQ_one h918 hIU).symm)
  have hEMp : ∀ e ∈ E, ∀ m ∈ autIH F.V1 I H (conjClosure K T),
      rhoQ h918 hIU e * m = m * rhoQ h918 hIU e := by
    intro e he m hm
    rw [← map_rhoQ_star h918 hIU h918.K₀_le_H] at hm
    obtain ⟨n', hn', rfl⟩ := hm
    have hcn := Subgroup.mem_centralizer_iff.1 (hEC he) n' hn'
    rw [← map_mul, ← map_mul, hcn]
  haveI : Finite ↥E := Subgroup.instFiniteSubtypeMem E
  exact A6.SzMod.false_of_modFive_grp hW2 hSzE (rhoQ h918 hIU) E hEodd hE3' hfpf' hEMp hLSz hMp
    htMp h5

theorem noSzLtF_w31_of
    (hSzE : A6.SzEnd) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1222 : Stmt12_2_2) : NoSzLtF_w31 := by
  intro _ G _ _ T L V _ F hH _ H K hIs h918 hne n _ hSz
  exact false_of_isSz_lt_w31 hSzE hD36 hD37 hD321 hI5 h37 h38 h1222 hH hIs h918 hne hSz

end Main

end CFSG.Quasithin.H13.P31Sz
