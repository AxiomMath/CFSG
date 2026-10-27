module

public import CFSG.LocalAnalysis.WeakClosure81.W16Four
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSix
public import CFSG.LocalAnalysis.WeakClosure81.FiveTen
import CFSG.Quasithin.Background.F9Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem conjSub_eq_conjSubgroup (g : G) (A : Subgroup G) :
    A1b.conjSub g A = conjSubgroup A g⁻¹ := by
  ext x
  rw [A1b.mem_conjSub_iff, mem_conjSubgroup_iff]
  simp

theorem IsMinFam16.fam16 (hH : IsMinFam16 M U S H) : Fam16 M U S H :=
  hH.1

theorem Cex16.exists_isMinFam16 (h : Cex16 M V₀ V U S) :
    ∃ H : Subgroup G, IsMinFam16 M U S H := by
  classical
  have hC : Fam16 M U S (centralizer (U : Set G)) :=
    ⟨h.S_le_centralizer, le_rfl, h.not_le⟩
  have hP : ∃ n : ℕ, ∃ H : Subgroup G, Fam16 M U S H ∧ Nat.card H = n :=
    ⟨Nat.card (centralizer (U : Set G)), centralizer (U : Set G), hC, rfl⟩
  obtain ⟨H, hHF, hHcard⟩ := Nat.find_spec hP
  refine ⟨H, hHF, ?_⟩
  intro H' hH'H hH'F
  have hle : Nat.card H ≤ Nat.card H' := by
    rw [hHcard]
    exact Nat.find_min' hP ⟨H', hH'F, rfl⟩
  have hle' : Nat.card H' ≤ Nat.card H := Subgroup.card_le_of_le hH'H
  by_contra hne
  exact absurd (Subgroup.card_lt_of_lt (lt_of_le_of_ne hH'H hne)) (not_lt.2 hle)

theorem IsMinFam16.sup_conjClosure_eq (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) : S ⊔ conjClosure V H = H := by
  have hHfam : Fam16 M U S H := hH.1
  have hSH : S ≤ H := hHfam.1
  have hHC : H ≤ centralizer (U : Set G) := hHfam.2.1
  have hHM : ¬ H ≤ M := hHfam.2.2
  have hVH : V ≤ H := h.V_le_S.trans hSH
  have hVC : V ≤ centralizer (U : Set G) := h.V_le_S.trans h.S_le_centralizer
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun g hg z hz => H.mul_mem (H.mul_mem hg (hVH hz)) (H.inv_mem hg)
  have hgen : ∀ g ∈ H, ∀ z ∈ V, g * z * g⁻¹ ∈ centralizer (U : Set G) := by
    intro g hg z hz
    have hgC : g ∈ centralizer (U : Set G) := hHC hg
    have hconj : conjSubgroup V g⁻¹ ≤ centralizer (U : Set G) := by
      calc conjSubgroup V g⁻¹ ≤ conjSubgroup (centralizer (U : Set G)) g⁻¹ :=
            conjSubgroup_mono hVC g⁻¹
        _ = centralizer (conjSubgroup U g⁻¹ : Set G) := E3.conjSubgroup_centralizer U g⁻¹
        _ = centralizer (U : Set G) := by
            rw [conjSubgroup_eq_iff_mem_normalizer.mpr]
            exact Subgroup.centralizer_le_normalizer (U : Set G)
              ((centralizer (U : Set G)).inv_mem hgC)
    exact hconj (by
      rw [mem_conjSubgroup_iff]
      have hz' : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
      rwa [hz'])
  have hKC : conjClosure V H ≤ centralizer (U : Set G) :=
    conjClosure_le fun g hg z hz => hgen g hg z hz
  have hFam : Fam16 M U S (S ⊔ conjClosure V H) := by
    refine ⟨le_sup_left, sup_le h.S_le_centralizer hKC, ?_⟩
    intro hLM
    have hKM : conjClosure V H ≤ M := le_sup_right.trans hLM
    have hKleW : conjClosure V H ≤ E3.wClos V 0 (M ⊓ centralizer (U : Set G)) := by
      refine conjClosure_le fun g hg z hz => ?_
      have hconj : conjSubgroup V g⁻¹ ≤ centralizer (U : Set G) := by
        have hgC : g ∈ centralizer (U : Set G) := hHC hg
        calc conjSubgroup V g⁻¹ ≤ conjSubgroup (centralizer (U : Set G)) g⁻¹ :=
              conjSubgroup_mono hVC g⁻¹
          _ = centralizer (conjSubgroup U g⁻¹ : Set G) := E3.conjSubgroup_centralizer U g⁻¹
          _ = centralizer (U : Set G) := by
              rw [conjSubgroup_eq_iff_mem_normalizer.mpr]
              exact Subgroup.centralizer_le_normalizer (U : Set G)
                ((centralizer (U : Set G)).inv_mem hgC)
      have hA : conjSubgroup V g⁻¹ ∈ E3.gammaSet V 0 (M ⊓ centralizer (U : Set G)) := by
        refine ⟨le_inf ?_ hconj, g⁻¹, le_rfl, by rw [E3.mQuot_self]⟩
        intro x hx
        have hx' : g⁻¹ * x * g ∈ V := by
          have h := (mem_conjSubgroup_iff (A := V) (g := g⁻¹)).1 hx
          simpa using h
        have hx'' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        rw [hx'']
        exact hKM (mem_conjClosure hg hx')
      exact E3.le_wClos hA (by
        rw [mem_conjSubgroup_iff]
        have hz' : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
        rwa [hz'])
    have hKleC : conjClosure V H ≤ centralizer (V : Set G) :=
      hKleW.trans (h1 hS h.hyp h.mbar h.le h.n_lt_mBar)
    have hKab : IsElemAbelian 2 (conjClosure V H) :=
      CFSG.Quasithin.HypF91.isElemAbelian_conjClosure_of_forall h.hyp.h6.elemAbelian
        (fun k hk => by
          intro v hv
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          have hxK : x ∈ conjClosure V H :=
            CFSG.Quasithin.HypF91.conjSub_le_conjClosure hk hx
          exact (Subgroup.mem_centralizer_iff.mp (hKleC hxK) v hv).symm)
    have hKp : IsPGroup 2 (conjClosure V H) :=
      CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hKab
    have hKNorm : ((conjClosure V H).subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
      exact le_normalizer_conjClosure V H
    have hKpCore : conjClosure V H ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 hKH hKNorm hKp
    exact hV ((le_conjClosure V H).trans hKpCore)
  exact hH.2 (S ⊔ conjClosure V H) (sup_le hSH hKH) hFam

theorem IsMinFam16.exists_conj_le_S_not_le_kerMOf (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) {x : G} (hxH : conjSubgroup V x ≤ H)
    (hx : ¬ conjSubgroup V x ≤ pCoreOf 2 H) :
    ∃ k ∈ H, conjSubgroup V (x * k) ≤ S ∧ ¬ conjSubgroup V (x * k) ≤ kerMOf M H := by
  have hHfam : Fam16 M U S H := hH.1
  have hSylH : IsSylowIn 2 S H := h.isSylowIn_of_fam h1 hS hHfam
  have hA0e : IsElemAbelian 2 (conjSubgroup V x) :=
    isElemAbelian_conjSubgroup' h.hyp.h6.elemAbelian x
  have hA0p : IsPGroup 2 (conjSubgroup V x) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hA0e
  let Ω : Set (Subgroup G) := {A | ∃ k ∈ H, A = conjSubgroup (conjSubgroup V x) k}
  have hΩ : E1.IsInvColl H Ω := by
    refine ⟨?_, ?_, ?_⟩
    · intro A hA
      obtain ⟨k, hk, rfl⟩ := hA
      intro a ha
      rw [mem_conjSubgroup_iff] at ha
      have ha' : a = k⁻¹ * (k * a * k⁻¹) * k := by group
      rw [ha']
      exact H.mul_mem (H.mul_mem (H.inv_mem hk) (hxH ha)) hk
    · intro A hA
      obtain ⟨k, hk, rfl⟩ := hA
      exact isElemAbelian_conjSubgroup' hA0e k
    · intro A hA g hg
      obtain ⟨k, hk, rfl⟩ := hA
      refine ⟨k * g⁻¹, H.mul_mem hk (H.inv_mem hg), ?_⟩
      rw [conjSub_eq_conjSubgroup, conjSubgroup_conjSubgroup]
  have hS_le_NW : S ≤ Subgroup.normalizer (E1.weakClosure S Ω : Set G) := by
    intro s hs
    apply E1.mem_normalizer_of_conj_mem
    have hle : E1.weakClosure S Ω ≤ (E1.weakClosure S Ω).comap (MulAut.conj s).toMonoidHom := by
      refine iSup₂_le fun A hA => iSup_le fun hAS => ?_
      intro a ha
      rw [Subgroup.mem_comap]
      have hconjΩ : A1b.conjSub s A ∈ Ω := hΩ.conj A hA s (hHfam.1 hs)
      have hconjS : A1b.conjSub s A ≤ S := by
        intro y hy
        rw [A1b.mem_conjSub_iff] at hy
        have hy' : s * (s⁻¹ * y * s) * s⁻¹ ∈ S :=
          S.mul_mem (S.mul_mem hs (hAS hy)) (S.inv_mem hs)
        rwa [show s * (s⁻¹ * y * s) * s⁻¹ = y by group] at hy'
      exact E1.le_weakClosure hconjΩ hconjS (A1b.mem_conjSub_of_mem ha)
    intro w hw
    exact hle hw
  have hNW_le_M : H ⊓ Subgroup.normalizer (E1.weakClosure S Ω : Set G) ≤ M := by
    by_contra hnot
    have hNfam : Fam16 M U S (H ⊓ Subgroup.normalizer (E1.weakClosure S Ω : Set G)) :=
      ⟨le_inf hHfam.1 hS_le_NW, inf_le_left.trans hHfam.2.1, hnot⟩
    have hNeq : H ⊓ Subgroup.normalizer (E1.weakClosure S Ω : Set G) = H :=
      hH.2 _ inf_le_left hNfam
    have hH_le_NW : H ≤ Subgroup.normalizer (E1.weakClosure S Ω : Set G) := by
      rw [← hNeq]
      exact inf_le_right
    have hW_le_S : E1.weakClosure S Ω ≤ S := E1.weakClosure_le
    have hW_le_H : E1.weakClosure S Ω ≤ H := hW_le_S.trans hHfam.1
    have hWp : IsPGroup 2 (E1.weakClosure S Ω) := hSylH.isPGroup.to_le hW_le_S
    have hWnorm : ((E1.weakClosure S Ω).subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hW_le_H]
      exact hH_le_NW
    have hWpCore : E1.weakClosure S Ω ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 hW_le_H hWnorm hWp
    obtain ⟨m, hm, hmS⟩ :=
      exists_conjSub_le_of_isSylowIn (H := H) (T := S) (M := H)
        (S := conjSubgroup V x) hSylH hHfam.1 hA0p hxH hxH
    have hmH : m ∈ H := hm.1
    have hmS' : conjSubgroup (conjSubgroup V x) m⁻¹ ≤ S := by
      rw [conjSub_eq_conjSubgroup] at hmS
      exact hmS
    have hgen : conjSubgroup (conjSubgroup V x) m⁻¹ ≤ E1.weakClosure S Ω :=
      E1.le_weakClosure ⟨m⁻¹, H.inv_mem hmH, rfl⟩ hmS'
    have hA0_le : conjSubgroup V x ≤ pCoreOf 2 H := by
      have hmNorm : conjSubgroup (pCoreOf 2 H) m = pCoreOf 2 H :=
        conjSubgroup_eq_iff_mem_normalizer.mpr
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H hmH)
      have hstep : conjSubgroup (conjSubgroup (conjSubgroup V x) m⁻¹) m ≤ pCoreOf 2 H :=
        (conjSubgroup_mono (hgen.trans hWpCore) m).trans (le_of_eq hmNorm)
      have hEq : conjSubgroup (conjSubgroup (conjSubgroup V x) m⁻¹) m = conjSubgroup V x := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      rwa [hEq] at hstep
    exact hx hA0_le
  obtain ⟨A, hA, hAS, H', hH'H, hAH', hker, hnot, hmax⟩ :=
    five_ten hΩ hSylH hNW_le_M hHfam.2.2
  obtain ⟨k, hk, hAk⟩ := hA
  have hAk' : A = conjSubgroup V (x * k) := by rw [hAk, conjSubgroup_conjSubgroup]
  refine ⟨k, hk, ?_, ?_⟩
  · rw [← hAk']
    exact hAS
  · rw [← hAk']
    exact fun hle => hnot (hle.trans hker)

end CFSG.LocalAnalysis.WeakClosure81

end
