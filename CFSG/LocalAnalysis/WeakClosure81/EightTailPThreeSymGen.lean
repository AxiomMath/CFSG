module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymDefs
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymMatching
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymNorm
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymSwaps
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymHyper
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymA
import CFSG.LocalAnalysis.WeakClosure81.ThreeOneMatching

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm CFSG.Open CFSG.Timmesfeld.Bridge.Asc72

theorem exists_mem_setNormalizer_conj_eq {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P)
    {s : Y} (hs : s ∈ symT t (P : Subgroup Y)) :
    ∃ x ∈ Subgroup.setNormalizer (symT t (P : Subgroup Y)), x * t * x⁻¹ = s := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hst : s = t
  · exact ⟨1, Subgroup.one_mem _, by simp [hst]⟩
  · have hmatch := symT_matching h
    have htT : t ∈ symT t (P : Subgroup Y) := ⟨IsConj.refl t, h.mem⟩
    have hsurj : Function.Surjective (symPi e) := w85g_symPi_surjective e
    let P' : Sylow 2 (Perm (Fin m)) := P.mapSurjective (f := symPi e) hsurj
    have hP'coe : (P' : Subgroup (Perm (Fin m))) = (P : Subgroup Y).map (symPi e) :=
      Sylow.coe_mapSurjective (f := symPi e) hsurj P
    obtain ⟨a, b, hab, htab⟩ := h.swap
    obtain ⟨c, d, hcd, hscd⟩ := hmatch.2.2.1 s hs
    have hne : symPi e s ≠ symPi e t := by
      intro heq
      exact hst (hmatch.1 hs htT heq)
    have hneqab : swap c d ≠ swap a b := by
      intro heq
      exact hne (hscd.trans (heq.trans htab.symm))
    have htabP' : swap a b ∈ (P' : Subgroup (Perm (Fin m))) := by
      rw [hP'coe, ← htab]
      exact Subgroup.mem_map_of_mem (symPi e) h.mem
    have hscdP' : swap c d ∈ (P' : Subgroup (Perm (Fin m))) := by
      rw [hP'coe, ← hscd]
      exact Subgroup.mem_map_of_mem (symPi e) hs.2
    have hPsyl : CFSG.Quasithin.IsSylowIn 2 (P' : Subgroup (Perm (Fin m))) ⊤ :=
      CFSG.Quasithin.isSylowIn_of_card_eq le_top (by
        rw [Subgroup.card_top]
        exact Sylow.card_eq_multiplicity P')
    obtain ⟨σ, hσ, hTσ, hfix⟩ := ThreeOne.exists_matching hPsyl
    have hσa : σ a = b := (hTσ a b hab).mp htabP'
    have hσc : σ c = d := (hTσ c d hcd).mp hscdP'
    have hac : a ≠ c := by
      intro h'
      apply hneqab
      have hbd : b = d := by rw [← hσa, h']; exact hσc
      rw [hbd, ← h']
    have had : a ≠ d := by
      intro h'
      apply hneqab
      have hcb : c = b := by
        calc c = σ (σ c) := (hσ c).symm
          _ = σ a := by rw [hσc, h']
          _ = b := hσa
      rw [← h', hcb]
      exact Equiv.swap_comm b a
    have hbc : b ≠ c := by
      intro h'
      apply hneqab
      have had' : a = d := by
        calc a = σ (σ a) := (hσ a).symm
          _ = σ c := by rw [hσa, h']
          _ = d := hσc
      rw [← h', had']
      exact Equiv.swap_comm b d
    have hbd : b ≠ d := by
      intro h'
      apply hneqab
      have hac' : a = c := σ.injective (by rw [hσa, h', hσc])
      rw [← hac', ← h']
    obtain ⟨hcomm, hconj⟩ :=
      exchange_two_cycles_mem_centralizer hσ hσa hσc hab hac had hbc hbd hcd
    set ρ : Perm (Fin m) := swap a c * swap b d with hρdef
    have hρC : ρ ∈ Subgroup.centralizer ({σ} : Set (Perm (Fin m))) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hN : Subgroup.setNormalizer
          {u : Perm (Fin m) | u.IsSwap ∧ u ∈ (P' : Subgroup (Perm (Fin m)))} =
        Subgroup.centralizer ({σ} : Set (Perm (Fin m))) := by
      have hset : {u : Perm (Fin m) | u.IsSwap ∧ u ∈ (P' : Subgroup (Perm (Fin m)))} =
          {u : Perm (Fin m) | u ∈ (P' : Subgroup (Perm (Fin m))) ∧ u.IsSwap} := by
        ext u
        exact and_comm
      rw [hset, ThreeOne.setNormalizer_eq_centralizer hσ hTσ]
    have himage : symPi e '' symT t (P : Subgroup Y) =
        {u : Perm (Fin m) | u.IsSwap ∧ u ∈ (P' : Subgroup (Perm (Fin m)))} := by
      rw [hP'coe]
      exact symT_image_eq_swaps h
    have hρN : ρ ∈ Subgroup.setNormalizer (symPi e '' symT t (P : Subgroup Y)) := by
      rw [himage, hN]
      exact hρC
    have hρmap : ρ ∈ (Subgroup.setNormalizer (symT t (P : Subgroup Y))).map (symPi e) := by
      rw [map_setNormalizer_eq h]
      exact hρN
    obtain ⟨x, hxN, hxπ⟩ := Subgroup.mem_map.mp hρmap
    have hxtT : x * t * x⁻¹ ∈ symT t (P : Subgroup Y) :=
      (Subgroup.mem_set_normalizer_iff.mp hxN t).mp htT
    refine ⟨x, hxN, ?_⟩
    apply hmatch.1 hxtT hs
    rw [map_mul, map_mul, map_inv, hxπ, htab, hscd]
    simpa [hρdef] using hconj

theorem fusionOddCore_le_closure {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P) :
    fusionOddCore Y ≤
      Subgroup.closure ((Subgroup.centralizer ({t} : Set Y) : Set Y) ∪
        (Subgroup.setNormalizer (symT t (P : Subgroup Y)) : Set Y)) := by
  let Q : Subgroup Y := Subgroup.closure (symT t (P : Subgroup Y))
  let R : Subgroup Y := Subgroup.closure ((Subgroup.centralizer ({t} : Set Y) : Set Y) ∪
        (Subgroup.setNormalizer (symT t (P : Subgroup Y)) : Set Y))
  change fusionOddCore Y ≤ R
  have hgen := le_iSup_inf_centralizer_of_index_two (O := fusionOddCore Y) (Q := Q)
    (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore Y)
    (isElemAbelian_closure_symT h) (closure_symT_ne_bot h)
  refine hgen.trans ?_
  refine iSup_le fun B => ?_
  refine iSup_le fun hBQ => ?_
  refine iSup_le fun hBi => ?_
  by_cases hcase : ∃ s ∈ symT t (P : Subgroup Y), s ∈ B
  · obtain ⟨s, hs, hsB⟩ := hcase
    have hCsR : Subgroup.centralizer ({s} : Set Y) ≤ R := by
      intro z hz
      obtain ⟨x, hxN, hxt⟩ := exists_mem_setNormalizer_conj_eq h hs
      have hxR : x ∈ R := Subgroup.subset_closure (Or.inr hxN)
      have hzxR : x⁻¹ * z * x ∈ R := by
        apply Subgroup.subset_closure
        apply Or.inl
        change x⁻¹ * z * x ∈ Subgroup.centralizer ({t} : Set Y)
        rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
        have hxinv : x⁻¹ * s * x = t := by rw [← hxt]; group
        calc (x⁻¹ * z * x) * t = (x⁻¹ * z * x) * (x⁻¹ * s * x) := by rw [hxinv]
          _ = x⁻¹ * (z * s) * x := by group
          _ = x⁻¹ * (s * z) * x := by rw [hz]
          _ = (x⁻¹ * s * x) * (x⁻¹ * z * x) := by group
          _ = t * (x⁻¹ * z * x) := by rw [hxinv]
      have hzxeq : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
      rw [← hzxeq]
      exact R.mul_mem (R.mul_mem hxR hzxR) (R.inv_mem hxR)
    exact (inf_le_right.trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsB))).trans hCsR
  · have hno : ∀ s ∈ symT t (P : Subgroup Y), s ∉ B := by
      intro s hs hsB
      exact hcase ⟨s, hs, hsB⟩
    have hle := fusionOddCore_inf_centralizer_le_centralizer h hBQ hBi hno
    exact hle.trans (fun z hz => Subgroup.subset_closure (Or.inl hz))

end CFSG.LocalAnalysis.WeakClosure81

end
