module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveEightA
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIa
public import CFSG.LocalAnalysis.WeakClosure81.FiveTen
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem IsMinFam16.exists_hyp167 (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hH : IsMinFam16 M U S H) : ∃ (g : G) (X T : Subgroup G), Hyp167 M V₀ V U S H g X T := by
  classical
  have hHfam : Fam16 M U S H := hH.1
  have hSylH : IsSylowIn 2 S H := h.isSylowIn_of_fam h1 hS hHfam
  let Ω : Set (Subgroup G) := E3.gammaSet V 0 H
  have hinv : E1.IsInvColl H Ω := E3.isInvColl_gammaSet h.hyp.h6.elemAbelian 0 H
  have hweak : E1.weakClosure S Ω = E3.wClos V 0 S := E3.weakClosure_gammaSet hHfam.1
  have hN : H ⊓ normalizer (E1.weakClosure S Ω : Set G) ≤ M := by
    rw [hweak]
    exact inf_le_right.trans (h.normalizer_wClos_le h1 hS)
  have hhyp : FiveTenHyp H M S Ω := ⟨hinv, hSylH, hN, hHfam.2.2⟩
  obtain ⟨A, hA, hAT, H', hH'H, hAH', hker, hnot, hmax⟩ :=
    FiveTenConc.exists_le_sylow hinv hSylH h.S_le_M (fiveTenAt_all H M S Ω hhyp)
  obtain ⟨-, g, hAg, hq⟩ := hA
  have hAg' : A = conjSubgroup V g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup h.hyp.h6.elemAbelian.isPGroup g) hAg).1 hq
  subst hAg'
  have hpairH' : IsPairAt M H' (conjSubgroup V g) :=
    ⟨hAH', hAT.trans h.S_le_M, hnot, hmax⟩
  have hkerSyl : ∃ P : Subgroup G, IsSylowIn 2 P (kerMOf M H) ∧ P ≤ kerMOf M H' := by
    obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 2 (bot_le : (⊥ : Subgroup G) ≤ kerMOf M H)
      (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    exact ⟨P, hP, hP.le.trans hker⟩
  have hFmem : H' ∈ DFam16 M H (conjSubgroup V g) := ⟨hH'H, hkerSyl, hpairH'⟩
  let F : Set (Subgroup G) := DFam16 M H (conjSubgroup V g)
  have hFne : ∃ n : ℕ, ∃ Y : Subgroup G, Y ∈ F ∧ Nat.card Y = n := ⟨_, H', hFmem, rfl⟩
  obtain ⟨X, hXF, hXcard⟩ := Nat.find_spec hFne
  have hXmin_card : ∀ Y : Subgroup G, Y ∈ F → Nat.card X ≤ Nat.card Y := by
    intro Y hY
    rw [hXcard]
    exact Nat.find_min' hFne ⟨Y, hY, rfl⟩
  have hXmin : ∀ X' ∈ F, X' ≤ X → X' = X := by
    intro X' hX'F hX'X
    exact Subgroup.eq_of_le_of_card_ge hX'X (hXmin_card X' hX'F)
  have hpairX : IsPairAt M X (conjSubgroup V g) := hXF.2.2
  have hA2 : IsPGroup 2 (conjSubgroup V g) :=
    E3.isPGroup_conjSubgroup h.hyp.h6.elemAbelian.isPGroup g
  obtain ⟨T, hT, hAT'⟩ :=
    exists_isSylowIn_ge 2 (le_inf hpairX.A_le hpairX.A_le_M) hA2
  exact ⟨g, X, T, ⟨h, hH, hAT, hXF, hXmin, hT, hAT'⟩⟩

theorem Hyp167.inf_centralizer_eSub_le_kerMOf (hX : Hyp167 M V₀ V U S H g X T) :
    X ⊓ centralizer (eSub V₀ X T : Set G) ≤ kerMOf M X := by
  have hTM : T ≤ M := hX.sylow.le.trans inf_le_right
  have hZ : V₀ ⊓ centralizer (T : Set G) ≠ ⊥ :=
    CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
      hX.sylow.isPGroup hX.cex.hyp.elemAbelian₀.isPGroup hX.cex.hyp.ne_bot
      (by rwa [hX.cex.hyp.normalizer₀])
  have hXn : X ≤ normalizer (eSub V₀ X T : Set G) := le_normalizer_conjClosure _ _
  have hNn : ((X ⊓ centralizer (eSub V₀ X T : Set G)).subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro n x hn hx
    refine ⟨X.mul_mem (X.mul_mem hx hn.1) (X.inv_mem hx),
      Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    have he' : x⁻¹ * e * x ∈ eSub V₀ X T := by
      have := (Subgroup.mem_normalizer_iff.1 (hXn (X.inv_mem hx)) e).1 he
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hn.2 _ he'
    calc e * (x * n * x⁻¹) = x * ((x⁻¹ * e * x) * n) * x⁻¹ := by group
      _ = x * (n * (x⁻¹ * e * x)) * x⁻¹ := by rw [hc]
      _ = x * n * x⁻¹ * e := by group
  refine le_kerMOf_of_normal inf_le_left hNn ?_
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ
  have hzE : (z : G) ∈ eSub V₀ X T := le_conjClosure _ _ z.2
  have hz1 : (z : G) ≠ 1 := fun e => hz (Subtype.ext e)
  intro n hn
  exact hX.cex.hyp.centralizer_le z.2.1 hz1
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzE) hn.2)

private theorem hyp167_exists_sylow_le_inf (hX : Hyp167 M V₀ V U S H g X T)
    (hQ : IsSylowIn 2 (T ⊓ kerMOf M X) (kerMOf M X)) :
    ∃ P : Subgroup G, IsSylowIn 2 P (kerMOf M H) ∧ P ≤ T ⊓ kerMOf M X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀syl, hP₀K⟩ := hX.mem.2.1
  obtain ⟨k, hkK, hkQ⟩ :=
    exists_conj_le_of_isSylowTwoOf (A := P₀) hQ hP₀K hP₀syl.isPGroup
  have hkH : k ∈ H := hX.mem.1 (kerMOf_le_group M X hkK)
  have hHnorm : H ≤ Subgroup.normalizer (kerMOf M H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (kerMOf_le_group M H)).1
      (normal_subgroupOf_kerMOf M H)
  have hconj : (kerMOf M H).map (MulAut.conj k).toMonoidHom = kerMOf M H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hHnorm hkH)
  refine ⟨CFSG.Quasithin.cjSub k P₀, ?_, hkQ⟩
  show IsSylowIn 2 (P₀.map (MulAut.conj k).toMonoidHom) (kerMOf M H)
  refine ⟨?_, hP₀syl.isPGroup.map _, ?_⟩
  · rw [← hconj]
    exact Subgroup.map_mono hP₀syl.le
  · rw [← hconj,
      Subgroup.relIndex_map_map_of_injective P₀ (kerMOf M H) (MulAut.conj k).injective]
    exact hP₀syl.not_dvd_relIndex

private theorem hyp167_inf_kerMOf_normal (hX : Hyp167 M V₀ V U S H g X T) :
    IsSylowIn 2 (T ⊓ kerMOf M X) (kerMOf M X) ∧
      ((T ⊓ kerMOf M X).subgroupOf X).Normal := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  have hKM : kerMOf M X ≤ M := kerMOf_le_left M X
  have hKn : ((kerMOf M X).subgroupOf X).Normal := normal_subgroupOf_kerMOf M X
  have hKXM : kerMOf M X ≤ X ⊓ M := le_inf hKX hKM
  have hXn : X ≤ Subgroup.normalizer (kerMOf M X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 hKn
  have hKnXM : ((kerMOf M X).subgroupOf (X ⊓ M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKXM).2 (inf_le_left.trans hXn)
  have hQsyl : IsSylowIn 2 (T ⊓ kerMOf M X) (kerMOf M X) :=
    hX.sylow.inf_normal hKXM hKnXM
  have hfr := frattini_isSylowIn hKX hKn hQsyl
  have hTX : T ≤ X := hX.sylow.le.trans inf_le_left
  let Q : Subgroup G := T ⊓ kerMOf M X
  let Y : Subgroup G := X ⊓ Subgroup.normalizer (Q : Set G)
  have hQK : Q ≤ kerMOf M X := inf_le_right
  have hQX : Q ≤ X := hQK.trans hKX
  have hTnormQ : T ≤ Subgroup.normalizer (Q : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxK⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht),
        conj_mem_kerMOf (hTX ht) hxK⟩
    · rintro ⟨hxT, hxK⟩
      refine ⟨?_, ?_⟩
      · have h := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
        simpa [mul_assoc] using h
      · have h := conj_mem_kerMOf (hTX (T.inv_mem ht)) hxK
        simpa [mul_assoc] using h
  have hYX : Y ≤ X := inf_le_left
  have hAY : conjSubgroup V g ≤ Y :=
    le_inf hX.mem.2.2.A_le (hX.A_le_T.trans hTnormQ)
  have hYK : Y ⊔ kerMOf M X = X := by
    refine le_antisymm (sup_le hYX hKX) fun x hx => ?_
    obtain ⟨y, hy, n, hnX, hnN, hyn⟩ := hfr x hx
    rw [← hyn]
    exact (Y ⊔ kerMOf M X).mul_mem (Subgroup.mem_sup_right hy)
      (Subgroup.mem_sup_left ⟨hnX, hnN⟩)
  obtain ⟨hkerY, hpY⟩ := hX.mem.2.2.restrict hYX hAY hYK
  obtain ⟨P, hPsyl, hPQ⟩ := hyp167_exists_sylow_le_inf hX hQsyl
  have hQY : Q ≤ Y := le_inf hQX Subgroup.le_normalizer
  have hPY : P ≤ Y := hPQ.trans hQY
  have hPK : P ≤ kerMOf M X := hPQ.trans inf_le_right
  have hYF : Y ∈ DFam16 M H (conjSubgroup V g) :=
    ⟨hYX.trans hX.mem.1, ⟨P, hPsyl, by rw [hkerY]; exact le_inf hPY hPK⟩, hpY⟩
  have hYXeq : Y = X := hX.min_X Y hYF hYX
  have hYnorm : Y ≤ Subgroup.normalizer (Q : Set G) := inf_le_right
  have hXnorm : X ≤ Subgroup.normalizer (Q : Set G) := hYXeq.symm.le.trans hYnorm
  exact ⟨hQsyl, (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).2 hXnorm⟩

theorem Hyp167.inf_kerMOf_eq_pCoreOf (hX : Hyp167 M V₀ V U S H g X T) :
    T ⊓ kerMOf M X = pCoreOf 2 (kerMOf M X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  obtain ⟨hQsyl, hQnormX⟩ := hyp167_inf_kerMOf_normal hX
  refine le_antisymm ?_ ?_
  · have hQX : T ⊓ kerMOf M X ≤ X := inf_le_right.trans hKX
    have hQnormK : ((T ⊓ kerMOf M X).subgroupOf (kerMOf M X)).Normal := by
      have hXN : X ≤ Subgroup.normalizer ((T ⊓ kerMOf M X : Subgroup G) : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).1 hQnormX
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 (hKX.trans hXN)
    exact le_pCoreOf_of_isPGroup_of_normal inf_le_right hQnormK hQsyl.isPGroup
  · exact pCoreOf_le_of_isSylowIn hQsyl

theorem Hyp167.eq_conjClosure_sup_pCoreOf (hX : Hyp167 M V₀ V U S H g X T) :
    X = conjClosure (conjSubgroup V g) X ⊔ pCoreOf 2 (kerMOf M X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  obtain ⟨hQsyl, -⟩ := hyp167_inf_kerMOf_normal hX
  obtain ⟨P, hPsyl, hPQ⟩ := hyp167_exists_sylow_le_inf hX hQsyl
  have hleaf1 : T ⊓ kerMOf M X = pCoreOf 2 (kerMOf M X) :=
    Hyp167.inf_kerMOf_eq_pCoreOf hX
  have hPpc : P ≤ pCoreOf 2 (kerMOf M X) := hleaf1 ▸ hPQ
  have hPK : P ≤ kerMOf M X := hPQ.trans inf_le_right
  have hp : IsPairAt M X (conjSubgroup V g) := hX.mem.2.2
  have hAK : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hgen : conjClosure (conjSubgroup V g) X ⊔ kerMOf M X = X :=
    IsPairAt.conjClosure_sup_kerMOf_eq hp hAK
  have hCX : conjClosure (conjSubgroup V g) X ≤ X :=
    conjClosure_le fun h hh z hz => X.mul_mem (X.mul_mem hh (hp.A_le hz)) (X.inv_mem hh)
  have hPcKX : pCoreOf 2 (kerMOf M X) ≤ X :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (kerMOf M X)).trans hKX
  have hX'X : conjClosure (conjSubgroup V g) X ⊔ pCoreOf 2 (kerMOf M X) ≤ X :=
    sup_le hCX hPcKX
  have hAX' : conjSubgroup V g ≤
      conjClosure (conjSubgroup V g) X ⊔ pCoreOf 2 (kerMOf M X) :=
    (le_conjClosure _ _).trans le_sup_left
  have hX'K : (conjClosure (conjSubgroup V g) X ⊔ pCoreOf 2 (kerMOf M X)) ⊔
      kerMOf M X = X := by
    rw [sup_assoc]
    rw [sup_eq_right.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 (kerMOf M X))]
    exact hgen
  obtain ⟨hkerX', hpX'⟩ := hp.restrict hX'X hAX' hX'K
  have hX'F : conjClosure (conjSubgroup V g) X ⊔ pCoreOf 2 (kerMOf M X) ∈
      DFam16 M H (conjSubgroup V g) := by
    refine ⟨hX'X.trans hX.mem.1, ⟨P, hPsyl, ?_⟩, hpX'⟩
    rw [hkerX']
    exact le_inf (hPpc.trans le_sup_right) hPK
  exact (hX.min_X _ hX'F hX'X).symm

theorem Hyp167.isElemAbelian_eSub (h1 : W16One G) (hS : Std15 G) (hV₀ : V₀ ≤ pCoreOf 2 H)
    (hX : Hyp167 M V₀ V U S H g X T) : IsElemAbelian 2 (eSub V₀ X T) :=
  CFSG.Open.IsElemAbelian.mono (Cex16.isElemAbelian_iSub16 h1 hS hX.cex hX.min.1)
    (conjClosure_mono (inf_le_left.trans (le_inf hX.cex.hyp.h6.le hV₀)) hX.mem.1)

end CFSG.LocalAnalysis.WeakClosure81

end
