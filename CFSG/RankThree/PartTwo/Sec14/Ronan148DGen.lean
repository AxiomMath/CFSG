module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148DTwoDefs
public import Certificates.Certificate148002
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCore

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree.Native.ONTriple CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup

theorem le_of_isPerfect_of_le_sup {X : Type} [Group X] {u : X} {K J : Subgroup X}
    (hKu : K ≤ centralizer ({u} : Set X)) (hJ : J ≤ zpowers u ⊔ K) [Group.IsPerfect J] :
    J ≤ K := by
  have huK : u ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hKu hk)
  have hcu : ∀ {m : X}, m ∈ K → Commute u m := fun hm =>
    (mem_centralizer_iff.mp huK _ hm).symm
  have hcomm : ⁅zpowers u ⊔ K, zpowers u ⊔ K⁆ ≤ K := by
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨a, k, hk, rfl⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup huK hx
    obtain ⟨b, k', hk', rfl⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup huK hy
    rw [CFSG.ComponentClassification.RankTwoSporadic.commutatorElement_mul_left_central
      ((hcu hk).zpow_left a) ((hcu hk').zpow_left a) ((hcu hk).zpow_left b)
      ((hcu hk').zpow_left b) ((Commute.refl u).zpow_zpow a b), commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
  calc J = ⁅J, J⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅zpowers u ⊔ K, zpowers u ⊔ K⁆ := Subgroup.commutator_mono hJ hJ
    _ ≤ K := hcomm

section Model


theorem wordG_e27 {j : ℕ} (hj : j < 2) {k : ℕ} (hk : k < 7) :
    wordG (e27InitG j) (e27Word j k) = gM ⟨k, by omega⟩ :=
  Certificates.certificate148002 j hj ⟨k, hk⟩

abbrev KL (j l : ℕ) : Subgroup GM := K0G.map (MulAut.conj (nL j l)⁻¹).toMonoidHom

theorem iSup_K_eq_top {j : ℕ} (hj : j < 2) : ⨆ l : Fin 4, KL j l = ⊤ := by
  set S := ⨆ l : Fin 4, KL j l with hS
  set Kp : Subgroup Mat45ˣ := S.map M.subtype with hKp
  have hnL : ∀ i : ℕ, i < 8 → eM (e27NReg j i) = (nL j (i / 2)).1 := fun i hi =>
    eM_rL hj (by omega)
  have hinit : ∀ k, (e27InitG j).getD k 1 ∈ Kp := by
    intro k
    by_cases hk : k < 9
    · rw [e27InitG_getD j hk]
      by_cases hk8 : k < 8
      · simp only [hk8, ↓reduceIte]
        rw [hnL k hk8]
        have hkK : ((nL j (k / 2))⁻¹ * (⟨eM (e27KReg k), eM_mem _⟩ : GM) * nL j (k / 2)) ∈
            KL j (k / 2) := by
          refine ⟨⟨eM (e27KReg k), eM_mem _⟩, ?_, ?_⟩
          · unfold e27KReg
            split_ifs
            · exact k1_mem
            · exact k2_mem
          · simp [MulAut.conj_apply]
        have hS' : KL j (k / 2) ≤ S := le_iSup (fun l : Fin 4 => KL j l) ⟨k / 2, by omega⟩
        exact ⟨_, hS' hkK, rfl⟩
      · simp only [hk8, ↓reduceIte]
        have hz : (zG : GM) ∈ KL j 0 := ⟨zG, zG_mem_K0, conj_zG _⟩
        have hS' : KL j 0 ≤ S := le_iSup (fun l : Fin 4 => KL j l) ⟨0, by omega⟩
        rw [zM_eq]
        exact ⟨zG, hS' hz, rfl⟩
    · rw [e27InitG_getD_of_ge j (by omega)]
      exact one_mem _
  have hgen : ∀ k : Fin 8, gM k ∈ Kp := by
    intro k
    by_cases hk : k.val < 7
    · have e : gM k = gM ⟨k.val, by omega⟩ := rfl
      rw [e, ← wordG_e27 hj hk]
      unfold wordG
      refine Kp.list_prod_mem fun x hx => ?_
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
      split
      · exact hinit _
      · exact Kp.inv_mem (hinit _)
    · have e7 : k = 7 := Fin.ext (by have := k.isLt; omega)
      have h8 := hinit 8
      rw [e27InitG_getD j (by norm_num), if_neg (by norm_num), zM_eq] at h8
      rw [e7]
      exact h8
  have hM : M ≤ Kp := by
    rw [M_eq_closure, closure_le]
    rintro _ ⟨k, rfl⟩
    exact hgen k
  rw [eq_top_iff]
  intro g _
  obtain ⟨h, hh, he⟩ := hM g.2
  have : h = g := Subtype.ext he
  rw [← this]
  exact hh

end Model

section Abstract


theorem mL_not_mem_zpowers (j l : ℕ) : mL j l ∉ zpowers zG := by
  have hx0 : xG 0 ∉ zpowers zG := by
    intro h
    have h0 := (relG.coord_eq_zero_iff ⟨xG 0, ThreeQRel.v_mem 0⟩).2 h
    rw [coord_xG0] at h0
    have := congrFun h0 0
    simp at this
  have h := conj_not_mem_zpowers hx0 (nL j l)⁻¹
  have e : (MulAut.conj (nL j l)⁻¹).toMonoidHom (xG 0) = mL j l := by
    simp [mL, MulAut.conj_apply]
  rwa [e] at h

theorem eq_K_of_le_centralizer (j l : ℕ) {J : Subgroup GM}
    (hJC : J ≤ centralizer ({mL j l} : Set GM)) [Group.IsPerfect J] (hJ : 1080 ≤ Nat.card J) :
    J = KL j l := by
  obtain ⟨h1, -⟩ := centralizer_conj (nL j l)⁻¹ (α := 1) (by norm_num) 0
  have e : (nL j l)⁻¹ * (xG 0 ^ 1 * zG ^ 0) * (nL j l)⁻¹⁻¹ = mL j l := by
    simp [mL]
  rw [e] at h1
  have hKC : KL j l ≤ centralizer ({mL j l} : Set GM) := by
    rw [h1]
    exact le_sup_right
  have hle : J ≤ KL j l := le_of_isPerfect_of_le_sup hKC (h1 ▸ hJC)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj (nL j l)⁻¹).injective,
    centralizer_x0_eq.2]
  exact hJ

theorem onTripleGenE27 : ONTripleGenE27 := by
  intro X _ _ hperf hT E hE 𝒦 h𝒦
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hperf hT
  have hE' := Sec13.ON134.isE27_map hE ψ.toMonoidHom ψ.injective
  obtain ⟨g, j, hj, hEg⟩ := exists_conj_AG hE'
  set φ : X ≃* GM := ψ.trans (MulAut.conj g) with hφ
  have hφmap : ∀ S : Subgroup X, S.map φ.toMonoidHom =
      (S.map ψ.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    intro S
    rw [Subgroup.map_map]
    rfl
  have hEφ : E.map φ.toMonoidHom = AG j := by rw [hφmap, hEg]
  have hKL : ∀ l : Fin 4, KL j l ≤ (sSup 𝒦).map φ.toMonoidHom := by
    intro l
    have hu : mL j l ∈ E.map φ.toMonoidHom := hEφ ▸ mL_mem_AG hj l.isLt
    obtain ⟨v, hvE, hvu⟩ := hu
    have hvu' : φ v = mL j l := hvu
    have hvZ : v ∉ Subgroup.center X := by
      intro hvZ
      exact mL_not_mem_zpowers j l (hvu' ▸ (Sec13.ON134.mem_center_iff_model φ).1 hvZ)
    obtain ⟨K, hK𝒦, hKC, hKperf, hK1080, -⟩ := h𝒦 v hvE hvZ
    have hKφC : K.map φ.toMonoidHom ≤ centralizer ({mL j l} : Set GM) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [mem_centralizer_singleton_iff, ← hvu']
      have h1 := mem_centralizer_singleton_iff.mp (hKC hk)
      show φ k * φ v = φ v * φ k
      rw [← map_mul, ← map_mul, h1]
    have : Group.IsPerfect ↥(K.map φ.toMonoidHom) := by
      haveI := hKperf
      exact Group.IsPerfect.map φ.toMonoidHom
    have hcard : 1080 ≤ Nat.card ↥(K.map φ.toMonoidHom) := by
      rw [Subgroup.card_map_of_injective φ.injective]
      exact hK1080
    rw [← eq_K_of_le_centralizer j l hKφC hcard]
    exact Subgroup.map_mono (le_sSup hK𝒦)
  have htop : (sSup 𝒦).map φ.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← iSup_K_eq_top hj]
    exact iSup_le hKL
  apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
  rw [htop, Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective]

end Abstract

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
