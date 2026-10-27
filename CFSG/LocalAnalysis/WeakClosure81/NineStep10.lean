module

public import CFSG.LocalAnalysis.WeakClosure81.NineLemmaD
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X A : Subgroup G} {p : ℕ}

private def nineStep10_normalClosure (Y K : Subgroup G) : Subgroup G :=
  ⨆ k : ↥K, conjSubgroup Y (k : G)

private theorem nineStep10_le_normalClosure (Y K : Subgroup G) :
    Y ≤ nineStep10_normalClosure Y K := by
  have h := le_iSup (fun k : ↥K => conjSubgroup Y (k : G)) ⟨1, K.one_mem⟩
  simpa [nineStep10_normalClosure, CFSG.Quasithin.conjSubgroup_one] using h

private theorem nineStep10_normalClosure_le {Y K : Subgroup G} (hYK : Y ≤ K) :
    nineStep10_normalClosure Y K ≤ K := by
  rw [nineStep10_normalClosure]
  refine iSup_le fun k => ?_
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hxK : (k : G) * x * (k : G)⁻¹ ∈ K := hYK hx
  have hx' : x = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G) := by group
  rw [hx']
  exact K.mul_mem (K.mul_mem (K.inv_mem k.2) hxK) k.2

private theorem nineStep10_conj_mem_normalClosure {Y K : Subgroup G} {k₀ : G} (hk₀ : k₀ ∈ K)
    {x : G} (hx : x ∈ nineStep10_normalClosure Y K) :
    k₀ * x * k₀⁻¹ ∈ nineStep10_normalClosure Y K := by
  refine Subgroup.iSup_induction (fun k : ↥K => conjSubgroup Y (k : G))
    (C := fun x => k₀ * x * k₀⁻¹ ∈ nineStep10_normalClosure Y K) hx ?_ ?_ ?_
  · intro k y hy
    have hy' : k₀ * y * k₀⁻¹ ∈ conjSubgroup Y ((k : G) * k₀⁻¹) := by
      rw [mem_conjSubgroup_iff] at hy ⊢
      have heq : ((k : G) * k₀⁻¹) * (k₀ * y * k₀⁻¹) * ((k : G) * k₀⁻¹)⁻¹
          = (k : G) * y * (k : G)⁻¹ := by group
      rw [heq]
      exact hy
    exact le_iSup (fun k' : ↥K => conjSubgroup Y (k' : G))
      ⟨(k : G) * k₀⁻¹, K.mul_mem k.2 (K.inv_mem hk₀)⟩ hy'
  · simpa using (nineStep10_normalClosure Y K).one_mem
  · intro x y hx hy
    have hmul := (nineStep10_normalClosure Y K).mul_mem hx hy
    have heq : k₀ * (x * y) * k₀⁻¹
        = (k₀ * x * k₀⁻¹) * (k₀ * y * k₀⁻¹) := by group
    rw [heq]
    exact hmul

private theorem nineStep10_subgroupOf_normal {Y K : Subgroup G} (hYK : Y ≤ K) :
    ((nineStep10_normalClosure Y K).subgroupOf K).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (nineStep10_normalClosure_le hYK)).mpr ?_
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => nineStep10_conj_mem_normalClosure hk hx, fun hx => by
    have h := nineStep10_conj_mem_normalClosure (K.inv_mem hk) hx
    have heq : k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x := by group
    rwa [heq] at h⟩

theorem commutator_cClos_ne_bot (h : TwoPTwoIrred K S X p) (hAS : A ≤ S)
    (hAR : ¬ A ≤ pCoreOf 2 K)
    (h9 : ⁅twoResidual K, E3.cClos V 1 (pCoreOf 2 K)⁆ ≠ ⊥) :
    ⁅A, E3.cClos V 1 (pCoreOf 2 K)⁆ ≠ ⊥ := by
  intro hbot
  have hAK : A ≤ K := hAS.trans h.sylowTwo.le
  have hA2 : IsPGroup 2 A := h.sylowTwo.isPGroup.to_le hAS
  let R : Subgroup G := pCoreOf 2 K
  let C : Subgroup G := E3.cClos V 1 R
  have hNK : nineStep10_normalClosure A K ≤ K := nineStep10_normalClosure_le hAK
  have hNnorm : ((nineStep10_normalClosure A K).subgroupOf K).Normal :=
    nineStep10_subgroupOf_normal hAK
  have hnot : ¬ nineStep10_normalClosure A K ≤ nineFrattiniR K X := fun hle =>
    TwoPTwo.not_le_frattiniR_of_isPGroup h.toTwoPTwo hAK hA2 hAR
      ((nineStep10_le_normalClosure A K).trans hle)
  have hres : twoResidual K ≤ nineStep10_normalClosure A K :=
    TwoPTwoIrred.twoResidual_le_of_not_le_frattiniR h hNK hNnorm hnot
  have hAC : A ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by simpa [C, R] using hbot)
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hKC : K ≤ Subgroup.normalizer (C : Set G) :=
    hKR.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := 1) R)
  have hcent : nineStep10_normalClosure A K ≤ Subgroup.centralizer (C : Set G) := by
    rw [nineStep10_normalClosure]
    refine iSup_le fun k => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    rw [mem_conjSubgroup_iff] at hy
    have hkc : (k : G) * c * (k : G)⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hKC k.2) c).mp hc
    have hcomm :=
      (Subgroup.mem_centralizer_iff.mp (hAC hy)) ((k : G) * c * (k : G)⁻¹) hkc
    have h1 : MulAut.conj (k : G) (c * y) = MulAut.conj (k : G) (y * c) := by
      rw [map_mul, map_mul]
      simpa only [MulAut.conj_apply] using hcomm
    exact (MulAut.conj (k : G)).injective h1
  have h2 : twoResidual K ≤ Subgroup.centralizer (C : Set G) := hres.trans hcent
  exact h9 (by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    simpa [C, R] using h2)

theorem mem_omegaSet_of_commutator_cClos_ne_bot (hV : Hyp7 V) (hA : IsGConj V A) (hAK : A ≤ K)
    (hAR : ¬ A ≤ pCoreOf 2 K)
    (hΓ : A ⊓ pCoreOf 2 K ∈ E3.gammaSet V 1 (pCoreOf 2 K)) (hne : A ⊓ pCoreOf 2 K ≠ ⊥)
    (h10 : ⁅A, E3.cClos V 1 (pCoreOf 2 K)⁆ ≠ ⊥) :
    A ∈ omegaSet V K (nineE V K) := by
  obtain ⟨g, hg⟩ := hA
  let R : Subgroup G := pCoreOf 2 K
  let W : Subgroup G := E3.wClos V 1 R
  let C : Subgroup G := E3.cClos V 1 R
  have hW1R : A ⊓ R ≤ W := E3.le_wClos hΓ
  have hCW : C ≤ Subgroup.centralizer (W : Set G) := inf_le_right
  obtain ⟨x₀, hx₀ne⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one (H := A ⊓ R)).mp (by simpa [R] using hne)
  have hx₀mem : (x₀ : G) ∈ A ⊓ R := x₀.2
  have hx₀1 : (x₀ : G) ≠ 1 := fun h => hx₀ne (Subtype.ext h)
  have hCnormA : C ≤ Subgroup.normalizer (A : Set G) := by
    have hcent1 : Subgroup.centralizer (W : Set G) ≤
        Subgroup.centralizer ((A ⊓ R : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (show ((A ⊓ R : Subgroup G) : Set G) ⊆ (W : Set G) from hW1R)
    have hcent2 : Subgroup.centralizer ((A ⊓ R : Subgroup G) : Set G) ≤
        Subgroup.centralizer ({(x₀ : G)} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx₀mem)
    have hcent3 : Subgroup.centralizer ({(x₀ : G)} : Set G) ≤
        Subgroup.normalizer (A : Set G) := by
      have hv : (x₀ : G) ∈ conjSubgroup V g := by rw [← hg]; exact hx₀mem.1
      have h := centralizer_le_normalizer_conj (V := V) hV.2.2 g hv hx₀1
      rwa [← hg] at h
    exact hCW.trans (hcent1.trans (hcent2.trans hcent3))
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hKC : K ≤ Subgroup.normalizer (C : Set G) :=
    hKR.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := 1) R)
  obtain ⟨a, ha, c, hc, haz⟩ : ∃ a ∈ A, ∃ c ∈ C, ⁅a, c⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : ⁅A, C⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcomm1 : ⁅a, c⁆ = 1 := hcon a ha c hc
      exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm1).symm
    exact h10 (by simpa [C, R] using hbot)
  set z : G := ⁅a, c⁆ with hzdef
  have hz1 : z ≠ 1 := haz
  have hzA : z ∈ A := by
    have h' : c * a⁻¹ * c⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hCnormA hc) a⁻¹).mp (A.inv_mem ha)
    rw [hzdef, commutatorElement_def]
    simpa [mul_assoc] using A.mul_mem ha h'
  have hzC : z ∈ C := by
    have haca : a * c * a⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hKC (hAK ha)) c).mp hc
    rw [hzdef, commutatorElement_def]
    exact C.mul_mem haca (C.inv_mem hc)
  have hzR : z ∈ R := (show C ≤ R from inf_le_left) hzC
  have hzW : z ∈ W := hW1R ⟨hzA, hzR⟩
  have hzcentW : z ∈ Subgroup.centralizer (W : Set G) := hCW hzC
  have hzcenter : z ∈ centerOf W := ⟨hzW, hzcentW⟩
  have hz2 : z ^ 2 = 1 :=
    (isElemAbelian_conjSubgroup' (V := V) hV.1 g).2 z (by rw [← hg]; exact hzA)
  have hzE : z ∈ nineE V K := by
    show z ∈ omegaOneOf (centerOf W)
    exact Subgroup.subset_closure ⟨hzcenter, hz2⟩
  refine ⟨g, hg, fun hbot => hz1 ?_, hAR⟩
  have hzbot : z ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hzE, hzA⟩
  exact mem_bot.mp hzbot

end CFSG.LocalAnalysis.WeakClosure81
