module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNine
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveKGp
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineGen
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem le_sup_pCoreOf_of_barSub_eq {K A B : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : SevenK.IsBarMap K (pCoreOf 2 K) φ) (hAK : A ≤ K)
    (hbar : SevenK.barSub K φ A = SevenK.barSub K φ B) :
    A ≤ B ⊔ pCoreOf 2 K := by
  intro a ha
  have haK : a ∈ K := hAK ha
  have hφa : φ ⟨a, haK⟩ ∈ SevenK.barSub K φ B := by
    rw [← hbar]
    exact SevenK.mem_barSub.mpr ⟨⟨a, haK⟩, ha, rfl⟩
  obtain ⟨b, hbB, hφb⟩ := SevenK.mem_barSub.mp hφa
  have hker : ((b⁻¹ * ⟨a, haK⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
    apply (hφ.ker_iff _).mp
    rw [map_mul, map_inv, hφb]
    simp
  have heq : a = (b : G) * ((b⁻¹ * ⟨a, haK⟩ : ↥K) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [heq]
  exact Subgroup.mul_mem_sup hbB hker

theorem IsMinFam16.conj_eq_of_mem_of_le_S
    (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) n) {y : G} (hy : y ∈ H)
    (hle : conjSubgroup V y ≤ S) : conjSubgroup V y = V := by
  classical
  let K : Subgroup G := conjClosure V H
  let Y : Subgroup X := SevenK.barSub K φ V
  haveI : Finite X := Finite.of_surjective (φ : ↥K → X) hφ.surjective
  have hsup : S ⊔ K = H := by
    change S ⊔ conjClosure V H = H
    exact IsMinFam16.sup_conjClosure_eq h1 hS h hH hV
  have hKH : K ≤ H := le_sup_right.trans hsup.le
  have hSnorm : S ≤ normalizer (K : Set G) := by
    change S ≤ normalizer (conjClosure V H : Set G)
    exact hH.1.1.trans (le_normalizer_conjClosure V H)
  obtain ⟨s, hsS, k, hkK, hsk⟩ : ∃ s ∈ S, ∃ k ∈ K, s * k = y := by
    have hyset : y ∈ ((S : Set G) * (K : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S K hSnorm, hsup]
      exact hy
    simpa only [Set.mem_mul, SetLike.mem_coe] using hyset
  have hVyeq : conjSubgroup V y = conjSubgroup V k := by
    rw [← hsk, ← conjSubgroup_conjSubgroup V s k]
    have hsmem : s ∈ normalizer (V : Set G) := by
      rw [h.hyp.h6.normalizer_eq]
      exact Cex16.S_le_M h hsS
    rw [conjSubgroup_eq_iff_mem_normalizer.mpr hsmem]
  have hVk_cent : conjSubgroup V k ≤ centralizer (V : Set G) := by
    have hc := Cex16.conj_le_centralizer_of_le_S h1 hS h hle
    rwa [hVyeq] at hc
  have hcardY : Nat.card Y = 2 ^ n := hX.1
  have hn1 : 1 ≤ n := by
    rcases hX.2 with ⟨hn, _⟩ | ⟨hn, _⟩
    · exact le_of_lt hn
    · exact le_of_eq hn.symm
  have hcard_ge : 2 ≤ Nat.card Y := by
    rw [hcardY]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card Y = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hYab : IsElemAbelian 2 Y :=
    isElemAbelian_barSub (K := K) (A := V) h.hyp.h6.elemAbelian φ
  have hX' : Shape166 X Y n := hX
  have hYgen : normalClosure (Y : Set X) = ⊤ :=
    IsMinFam16.normalClosure_barSub_eq_top h1 hS h hH hV hφ
  let kK : ↥K := ⟨k, hkK⟩
  have hC : conjSubgroup Y (φ kK) ≤ centralizer (Y : Set X) := by
    have hbc : SevenK.barSub K φ (conjSubgroup V k) = conjSubgroup Y (φ kK) :=
      barSub_conjSubgroup (K := K) φ V kK
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← hbc] at hx
    obtain ⟨a, ha_conj, haφ⟩ := SevenK.mem_barSub.mp hx
    obtain ⟨v, hvV, hvφ⟩ := SevenK.mem_barSub.mp hz
    have hcomm : (a : G) * (v : G) = (v : G) * (a : G) :=
      (Subgroup.mem_centralizer_iff.mp (hVk_cent ha_conj) (v : G) hvV).symm
    have hav : a * v = v * a := Subtype.ext (by simpa using hcomm)
    rw [← hvφ, ← haφ]
    calc φ v * φ a = φ (v * a) := (map_mul φ v a).symm
      _ = φ (a * v) := by rw [hav]
      _ = φ a * φ v := map_mul φ a v
  have hYeq : conjSubgroup Y (φ kK) = Y := by
    by_contra hne
    have hbot : conjSubgroup Y (φ kK) ⊓ normalizer (Y : Set X) = ⊥ :=
      Shape166.conj_inf_normalizer_eq_bot hYab hYgen hX' le_rfl hYne hne
    have hsub : conjSubgroup Y (φ kK) ≤ normalizer (Y : Set X) :=
      hC.trans (Subgroup.centralizer_le_normalizer (Y : Set X))
    have hthis : conjSubgroup Y (φ kK) ≤ conjSubgroup Y (φ kK) ⊓ normalizer (Y : Set X) :=
      le_inf le_rfl hsub
    rw [hbot] at hthis
    have hbot' : conjSubgroup Y (φ kK) = ⊥ := le_bot_iff.mp hthis
    have h1 : Nat.card Y = 1 := by
      rw [← E3.card_conjSubgroup Y (φ kK), hbot', Subgroup.card_bot]
    omega
  have hk_normK : k ∈ normalizer (K : Set G) := by
    change k ∈ normalizer (conjClosure V H : Set G)
    exact le_normalizer_conjClosure V H (hKH hkK)
  have hconjK : conjSubgroup V k ≤ K := by
    calc conjSubgroup V k ≤ conjSubgroup K k := conjSubgroup_mono (le_conjClosure V H) k
      _ = K := conjSubgroup_eq_iff_mem_normalizer.mpr hk_normK
  have hbar : SevenK.barSub K φ (conjSubgroup V k) = SevenK.barSub K φ V := by
    rw [barSub_conjSubgroup (K := K) φ V kK, hYeq]
  have hVk_le : conjSubgroup V k ≤ V ⊔ pCoreOf 2 K :=
    le_sup_pCoreOf_of_barSub_eq hφ hconjK hbar
  have hkV : ∀ v ∈ V, k⁻¹ * v * (k⁻¹)⁻¹ ∈ V ⊔ pCoreOf 2 (conjClosure V H) := by
    intro v hv
    have hmem : k⁻¹ * v * k ∈ conjSubgroup V k := by
      rw [mem_conjSubgroup_iff]
      have hv' : k * (k⁻¹ * v * k) * k⁻¹ = v := by group
      rw [hv']
      exact hv
    have hfin := hVk_le hmem
    simpa using hfin
  have hkM' : k⁻¹ ∈ M :=
    Cex16.mem_of_conj_le_sup h1 h5 hS h (show Fam16 M U S H from hH.1) hV hQ
      (hKH (K.inv_mem hkK)) hkV
  have hkM : k ∈ M := by simpa using M.inv_mem hkM'
  have hyM : y ∈ M := by
    rw [← hsk]
    exact M.mul_mem (Cex16.S_le_M h hsS) hkM
  have hyN : y ∈ normalizer (V : Set G) := by
    rw [h.hyp.h6.normalizer_eq]
    exact hyM
  exact conjSubgroup_eq_iff_mem_normalizer.mpr hyN

end CFSG.LocalAnalysis.WeakClosure81

end
