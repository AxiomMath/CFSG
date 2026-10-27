module

public import CFSG.RankThree.SubgroupLists.MitchellDegenerate
public import CFSG.RankThree.SubgroupLists.MitchellQOne
public import Certificates.Certificate113

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem exists_ne_zero_orth_four (h2 : (2 : K) ≠ 0) {v₁ v₂ v₃ v₄ : Matrix V₄ V₄ K}
    (h₁ : v₁ ∈ (cliffSpace : Submodule K _)) (h₂ : v₂ ∈ (cliffSpace : Submodule K _))
    (h₃ : v₃ ∈ (cliffSpace : Submodule K _)) (h₄ : v₄ ∈ (cliffSpace : Submodule K _)) :
    ∃ w ∈ (cliffSpace : Submodule K _), w ≠ 0 ∧ cliffB w v₁ = 0 ∧ cliffB w v₂ = 0 ∧
      cliffB w v₃ = 0 ∧ cliffB w v₄ = 0 := by
  classical
  set M := (cliffSpace : Submodule K (Matrix V₄ V₄ K))
  set S : Submodule K M := Submodule.span K {⟨v₁, h₁⟩, ⟨v₂, h₂⟩, ⟨v₃, h₃⟩, ⟨v₄, h₄⟩}
  have hS : finrank K S ≤ 4 := by
    have := finrank_span_le_card (R := K)
      ({⟨v₁, h₁⟩, ⟨v₂, h₂⟩, ⟨v₃, h₃⟩, ⟨v₄, h₄⟩} : Set M)
    refine this.trans ?_
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  have hnd := cliffBil_nondegenerate h2
  have hO : finrank K ((cliffBil K).orthogonal S) = 5 - finrank K S := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, finrank_cliffSpace h2]
  have hpos : 0 < finrank K ((cliffBil K).orthogonal S) := by omega
  haveI : Nontrivial ((cliffBil K).orthogonal S) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨w, hw⟩ := exists_ne (0 : (cliffBil K).orthogonal S)
  have hw0 : ((w : M) : Matrix V₄ V₄ K) ≠ 0 := by
    intro h
    apply hw
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have horth : ∀ (v : Matrix V₄ V₄ K) (hv : v ∈ M), (⟨v, hv⟩ : M) ∈ S →
      cliffB ((w : M) : Matrix V₄ V₄ K) v = 0 := by
    intro v hv hvS
    have h := w.2 _ hvS
    have h' : cliffBil K ⟨v, hv⟩ (w : M) = 0 := h
    rw [cliffBil_apply, cliffB_comm] at h'
    exact h'
  refine ⟨(w : M), (w : M).2, hw0, horth _ h₁ ?_, horth _ h₂ ?_, horth _ h₃ ?_, horth _ h₄ ?_⟩ <;>
    exact Submodule.subset_span (by simp)

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem commute_of_isotropic_orth (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)}
    (hGS : G ≤ StatedSp 2 K) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) {u r : Matrix V₄ V₄ K}
    (huM : u ∈ (cliffSpace : Submodule K _)) (hQu : cliffB u u ≠ 0)
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hur : cliffB u r = 0) (hrr : cliffB r r = 0)
    (hr0 : r ≠ 0) {x y : GL V₄ K} (hxG : x ∈ G) (hyG : y ∈ G)
    (hxu : (x : Matrix V₄ V₄ K) * u = u * (x : Matrix V₄ V₄ K))
    (hyu : (y : Matrix V₄ V₄ K) * u = u * (y : Matrix V₄ V₄ K))
    (hxr : (x : Matrix V₄ V₄ K) * r = r * (x : Matrix V₄ V₄ K))
    (hyr : (y : Matrix V₄ V₄ K) * r = r * (y : Matrix V₄ V₄ K)) : x * y = y * x := by
  obtain ⟨K', iF, iFin, iCh, φ, u', hu', s, hs, hu's⟩ := exists_isNCInv_smul_map hp2 huM hQu
  have h2' : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
  obtain ⟨h, hhS, hh⟩ := exists_conj_eq_tStd h2' hu'
  set k : GL V₄ K' := h⁻¹ with hk
  have hkS : k ∈ StatedSp 2 K' := inv_mem hhS
  have hki : k⁻¹ = h := by rw [hk, inv_inv]
  set G'' := (G.map (mapGL φ)).map (MulAut.conj k).toMonoidHom
  have hU0'' : ∀ z ∈ G'', IsSqZero z → z = 1 := by
    intro z hz hsq
    rw [mem_map_conj] at hz
    obtain ⟨z₀, hz₀, hz₀e⟩ := hz
    have hsq' : IsSqZero (mapGL φ z₀) := by
      rw [hz₀e]
      have := isSqZero_conj hsq k⁻¹
      simpa [mul_assoc] using this
    have h1 := hU0 z₀ hz₀ ((isSqZero_map_iff φ).mp hsq')
    rw [h1, map_one] at hz₀e
    calc z = k * (k⁻¹ * z * k) * k⁻¹ := by group
      _ = 1 := by rw [← hz₀e]; group
  set R : Matrix V₄ V₄ K' := (k : Matrix V₄ V₄ K') * r.map φ * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K')
  have htk' : (tStd : GL V₄ K') = k * u' * k⁻¹ := by
    rw [← hh, hk]
    group
  have htk : (tStdMat : Matrix V₄ V₄ K') =
      (k : Matrix V₄ V₄ K') * (u' : Matrix V₄ V₄ K') * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') := by
    rw [← coe_tStd, htk', Units.val_mul, Units.val_mul]
  have hrM' : r.map φ ∈ (cliffSpace : Submodule K' _) := map_mem_cliffSpace φ hrM
  have huM' : (u' : Matrix V₄ V₄ K') ∈ (cliffSpace : Submodule K' _) := by
    rw [hu's]
    exact Submodule.smul_mem _ _ (map_mem_cliffSpace φ huM)
  have hRM : R ∈ (cliffSpace : Submodule K' _) := conj_mem_cliffSpace hkS hrM'
  have hRt : cliffB tStdMat R = 0 := by
    rw [htk, cliffB_conj h2' k huM' hrM', hu's, cliffB_smul_left, cliffB_map, hur, map_zero,
      mul_zero]
  have hRR : cliffB R R = 0 := by
    rw [cliffB_conj h2' k hrM' hrM', cliffB_map, hrr, map_zero]
  have hR0 : R ≠ 0 := by
    intro h0
    apply hr0
    have hm : r.map φ = 0 := by
      have e : r.map φ = ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') * R * (k : Matrix V₄ V₄ K') := by
        simp only [R, ← Matrix.mul_assoc]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
          ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [e, h0, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    have := congrFun (congrFun hm i) j
    simpa using φ.injective (by simpa using this)
  have hconj : ∀ z : GL V₄ K, ((k * mapGL φ z * k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') =
      (k : Matrix V₄ V₄ K') * (z : Matrix V₄ V₄ K).map φ * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') :=
          by
    intro z
    rw [Units.val_mul, Units.val_mul, coe_mapGL]
  have hkk : ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') * (k : Matrix V₄ V₄ K') = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm_conj : ∀ (z : GL V₄ K) (Y : Matrix V₄ V₄ K),
      (z : Matrix V₄ V₄ K) * Y = Y * (z : Matrix V₄ V₄ K) →
      ((k * mapGL φ z * k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') *
          ((k : Matrix V₄ V₄ K') * Y.map φ * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K')) =
        ((k : Matrix V₄ V₄ K') * Y.map φ * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K')) *
          ((k * mapGL φ z * k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') := by
    intro z Y hzY
    rw [hconj]
    have e : (z : Matrix V₄ V₄ K).map φ * Y.map φ = Y.map φ * (z : Matrix V₄ V₄ K).map φ := by
      rw [← Matrix.map_mul, hzY, Matrix.map_mul]
    calc (k : Matrix V₄ V₄ K') * (z : Matrix V₄ V₄ K).map φ * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') *
          ((k : Matrix V₄ V₄ K') * Y.map φ * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K'))
        = (k : Matrix V₄ V₄ K') * ((z : Matrix V₄ V₄ K).map φ * Y.map φ) *
            ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') (k : Matrix V₄ V₄ K'), hkk,
            Matrix.one_mul]
      _ = (k : Matrix V₄ V₄ K') * (Y.map φ * (z : Matrix V₄ V₄ K).map φ) *
            ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') := by rw [e]
      _ = ((k : Matrix V₄ V₄ K') * Y.map φ * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K')) *
          ((k : Matrix V₄ V₄ K') * (z : Matrix V₄ V₄ K).map φ *
            ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K')) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') (k : Matrix V₄ V₄ K'), hkk,
            Matrix.one_mul]
  have hut : ∀ z : GL V₄ K, (z : Matrix V₄ V₄ K) * u = u * (z : Matrix V₄ V₄ K) →
      ((k * mapGL φ z * k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') * tStdMat =
        tStdMat * ((k * mapGL φ z * k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') := by
    intro z hz
    have h := hcomm_conj z u hz
    rw [htk, hu's]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [h]
  have hmemG : ∀ z ∈ G, k * mapGL φ z * k⁻¹ ∈ G'' := fun z hz =>
    conj_mem_map_conj (Subgroup.mem_map_of_mem _ hz)
  have hres := commute_of_isotropic_tStd h2' hU0'' hRM hRt hRR hR0 (hmemG x hxG) (hmemG y hyG)
    (hut x hxu) (hut y hyu) (hcomm_conj x r hxr) (hcomm_conj y r hyr)
  apply mapGL_injective φ
  have e : k * mapGL φ x * k⁻¹ * (k * mapGL φ y * k⁻¹) = k * (mapGL φ x * mapGL φ y) * k⁻¹ := by
    group
  have e' : k * mapGL φ y * k⁻¹ * (k * mapGL φ x * k⁻¹) = k * (mapGL φ y * mapGL φ x) * k⁻¹ := by
    group
  rw [e, e'] at hres
  have := mul_left_cancel (mul_right_cancel hres)
  rw [map_mul, map_mul, this]

theorem exists_orth_pair_of_three (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)}
    (hGS : G ≤ StatedSp 2 K) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ K) ∈ G)
    {d e f : GL V₄ K} (hdG : d ∈ G) (heG : e ∈ G) (hfG : f ∈ G) (hd : IsNCInv d)
    (he : IsNCInv e) (hf : IsNCInv f)
    (hβ : cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) *
      cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) ≠ 1)
    (hfP : ∀ a b : K, (f : Matrix V₄ V₄ K) ≠ a • (d : Matrix V₄ V₄ K) + b • (e : Matrix V₄ V₄ K)) :
    ∃ u w : Matrix V₄ V₄ K, u ∈ (cliffSpace : Submodule K _) ∧ w ∈ (cliffSpace : Submodule K _) ∧
      cliffB u d = 0 ∧ cliffB u e = 0 ∧ cliffB u f = 0 ∧ cliffB w d = 0 ∧ cliffB w e = 0 ∧
      cliffB w f = 0 ∧ cliffB u w = 0 ∧ cliffB u u ≠ 0 ∧ cliffB w w ≠ 0 := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  have hdM := (mem_cliffSpace_of_involution h2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).1
  have heM := (mem_cliffSpace_of_involution h2 he.1 he.2.1 he.2.2.1 he.2.2.2).1
  have hfM := (mem_cliffSpace_of_involution h2 hf.1 hf.2.1 hf.2.2.1 hf.2.2.2).1
  have hdd : (d : Matrix V₄ V₄ K) * d = 1 := by rw [← Units.val_mul, hd.2.1, Units.val_one]
  have hee : (e : Matrix V₄ V₄ K) * e = 1 := by rw [← Units.val_mul, he.2.1, Units.val_one]
  have hff : (f : Matrix V₄ V₄ K) * f = 1 := by rw [← Units.val_mul, hf.2.1, Units.val_one]
  obtain ⟨u, huM, hud, hue, huf, hQu⟩ := exists_orth_cliffQ_ne_zero h2 hdM heM hfM
    (cliffB_eq_one_of_mul_self h2 hdd) (cliffB_eq_one_of_mul_self h2 hee) hβ hfP
  obtain ⟨w, hwM, hw0, hwd, hwe, hwf, hwu⟩ := exists_ne_zero_orth_four h2 hdM heM hfM huM
  refine ⟨u, w, huM, hwM, hud, hue, huf, hwd, hwe, hwf, by rw [cliffB_comm]; exact hwu, hQu, ?_⟩
  intro hQw
  have hanti : ∀ (a z : Matrix V₄ V₄ K), a ∈ (cliffSpace : Submodule K _) →
      z ∈ (cliffSpace : Submodule K _) → cliffB z a = 0 → a * z = -(z * a) := by
    intro a z ha hz h0
    exact (mul_eq_neg_mul_iff h2 ha hz).mpr (by rw [cliffB_comm]; exact h0)
  have hprod : ∀ (a b z : Matrix V₄ V₄ K), a ∈ (cliffSpace : Submodule K _) →
      b ∈ (cliffSpace : Submodule K _) → z ∈ (cliffSpace : Submodule K _) →
      cliffB z a = 0 → cliffB z b = 0 → a * b * z = z * (a * b) := by
    intro a b z ha hb hz hza hzb
    rw [Matrix.mul_assoc, hanti b z hb hz hzb, Matrix.mul_neg, ← Matrix.mul_assoc,
      hanti a z ha hz hza, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have hcomm := commute_of_isotropic_orth hp2 hGS hU0 huM hQu hwM
    (by rw [cliffB_comm]; exact hwu) hQw hw0 (G.mul_mem hdG heG) (G.mul_mem hdG hfG)
    (by rw [Units.val_mul]; exact hprod _ _ _ hdM heM huM hud hue)
    (by rw [Units.val_mul]; exact hprod _ _ _ hdM hfM huM hud huf)
    (by rw [Units.val_mul]; exact hprod _ _ _ hdM heM hwM hwd hwe)
    (by rw [Units.val_mul]; exact hprod _ _ _ hdM hfM hwM hwd hwf)
  have hcm := congrArg (fun z : GL V₄ K => (z : Matrix V₄ V₄ K)) hcomm
  simp only [Units.val_mul] at hcm
  have hγ := cliffB_sq_eq_one_of_commute h2 hdM heM hfM hdd hee hff
    (lin_indep_of_not_mem_span h2 (cliffB_eq_one_of_mul_self h2 hdd)
      (cliffB_eq_one_of_mul_self h2 hee) hβ hfP) hcm
  have h' : cliffB (d : Matrix V₄ V₄ K) (f : Matrix V₄ V₄ K) = 1 ∨
      cliffB (d : Matrix V₄ V₄ K) (f : Matrix V₄ V₄ K) = -1 := by
    have : (cliffB (d : Matrix V₄ V₄ K) (f : Matrix V₄ V₄ K) - 1) *
        (cliffB (d : Matrix V₄ V₄ K) (f : Matrix V₄ V₄ K) + 1) = 0 := by linear_combination hγ
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases eq_or_eq_neg_of_cliffB_eq_one h2 hU0 hneg hdG hfG hd hf h' with h | h
  · exact hfP 1 0 (by rw [h]; simp)
  · exact hfP (-1) 0 (by rw [h]; simp)

end CFSG.RankThree.SubgroupLists
