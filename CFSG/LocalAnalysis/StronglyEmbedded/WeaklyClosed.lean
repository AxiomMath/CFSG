module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.StronglyEmbedded

open Subgroup
open CFSG.RankThree.PartOne.StrongP

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

private theorem exists_isSylowOf_ge {R H : Subgroup G} [Fact p.Prime]
    (hR : IsPGroup p R) (hRH : R ≤ H) :
    ∃ T : Subgroup G, R ≤ T ∧ CFSG.ABGLocalTools.IsSylowOf p T H := by
  obtain ⟨Q, hQ⟩ := (hR.comap_subtype (K := H)).exists_le_sylow
  exact ⟨(Q : Subgroup H).map H.subtype, fun x hx => ⟨⟨x, hRH hx⟩, hQ hx, rfl⟩, Q, rfl⟩

private theorem exists_pGroup_lt_le_normalizer {P R : Subgroup G} [Fact p.Prime]
    (hR : IsPGroup p R) (hPR : P < R) :
    ∃ Q : Subgroup G, IsPGroup p Q ∧ P < Q ∧ Q ≤ R ⊓ normalizer (P : Set G) := by
  let : Group.IsNilpotent R := hR.isNilpotent
  have hlt : P.subgroupOf R < ⊤ := by
    exact lt_top_iff_ne_top.mpr (fun htop =>
      hPR.not_ge (Subgroup.subgroupOf_eq_top.mp htop))
  set N : Subgroup R := normalizer ((P.subgroupOf R : Subgroup R) : Set R)
  have hPN : P.subgroupOf R < N := Group.normalizerCondition_of_isNilpotent _ hlt
  refine ⟨N.map R.subtype, hR.to_le (Subgroup.map_subtype_le N), ?_, ?_⟩
  · have h := (Subgroup.map_subtype_lt_map_subtype).2 hPN
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPR.le] at h
  · intro y hy
    obtain ⟨z, hzN, rfl⟩ := hy
    refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have hzq : (⟨q, hPR.le hq⟩ : R) ∈ P.subgroupOf R := hq
      have := (Subgroup.mem_normalizer_iff.mp hzN ⟨q, hPR.le hq⟩).mp hzq
      exact Subgroup.mem_subgroupOf.mp this
    · intro hconj
      have hqR : q ∈ R := by
        have hmem : (z : G)⁻¹ * ((z : G) * q * (z : G)⁻¹) * (z : G) ∈ R := by
          simpa using R.mul_mem (R.mul_mem (R.inv_mem z.2) (hPR.le hconj)) z.2
        have hEq : (z : G)⁻¹ * ((z : G) * q * (z : G)⁻¹) * (z : G) = q := by group
        rwa [hEq] at hmem
      have hzq : z * (⟨q, hqR⟩ : R) * z⁻¹ ∈ P.subgroupOf R := hconj
      exact (Subgroup.mem_normalizer_iff.mp hzN ⟨q, hqR⟩).mpr hzq

theorem exists_mem_normalizer_mul_conj_eq_of_weaklyClosed [Fact p.Prime] {P : Sylow p G}
    {W : Subgroup G} (hWP : W ≤ (P : Subgroup G))
    (hW : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      W.map (MulAut.conj g).toMonoidHom = W)
    {x y g : G} (hx : x ∈ Subgroup.centralizer (W : Set G))
    (hy : y ∈ Subgroup.centralizer (W : Set G)) (hg : g * x * g⁻¹ = y) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n * x * n⁻¹ = y := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hWC : W ≤ C := by
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hy w hw)
  have hgWC : W.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro z ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g * w * g⁻¹) * y = g * (w * x) * g⁻¹ := by rw [← hg]; group
      _ = g * (x * w) * g⁻¹ := by rw [Subgroup.mem_centralizer_iff.mp hx w hw]
      _ = y * (g * w * g⁻¹) := by rw [← hg]; group
  have hWp : IsPGroup p W := P.isPGroup'.to_le hWP
  have hgWp : IsPGroup p (W.map (MulAut.conj g).toMonoidHom) := hWp.map _
  obtain ⟨S, hWS, hS⟩ := exists_isSylowOf_ge (H := C) hWp hWC
  obtain ⟨R, hgWR, hR⟩ := exists_isSylowOf_ge (H := C) hgWp hgWC
  obtain ⟨c, hcC, hconj⟩ := hR.exists_mem_conj hS
  have hc_eq : conjSub c R = S := by
    ext z
    exact (mem_conjSub_iff).trans (hconj z).symm
  obtain ⟨Pstar, hSPstar⟩ := hS.isPGroup.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P Pstar
  have hPstar : (Pstar : Subgroup G) = conjSub h (P : Subgroup G) := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hSP : S ≤ conjSub h (P : Subgroup G) := hPstar ▸ hSPstar
  have hS_hP : conjSub h⁻¹ S ≤ (P : Subgroup G) := by
    calc conjSub h⁻¹ S ≤ conjSub h⁻¹ (conjSub h (P : Subgroup G)) := Subgroup.map_mono hSP
      _ = P := by rw [conjSub_mul, inv_mul_cancel, conjSub_one]
  have hWhP : conjSub h⁻¹ W ≤ (P : Subgroup G) := (Subgroup.map_mono hWS).trans hS_hP
  have hhW : conjSub h⁻¹ W = W := hW h⁻¹ hWhP
  have hcgS : conjSub (c * g) W ≤ S := by
    calc conjSub (c * g) W = conjSub c (conjSub g W) := (conjSub_mul).symm
      _ ≤ conjSub c R := Subgroup.map_mono hgWR
      _ = S := hc_eq
  have hcgP : conjSub (h⁻¹ * (c * g)) W ≤ (P : Subgroup G) := by
    rw [← conjSub_mul]
    exact (Subgroup.map_mono hcgS).trans hS_hP
  have hhcgW : conjSub (h⁻¹ * (c * g)) W = W := hW _ hcgP
  have hhN : h ∈ Subgroup.normalizer (W : Set G) := by
    have hhinv : h⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hhW
    simpa using (Subgroup.normalizer (W : Set G)).inv_mem hhinv
  have hhcgN : h⁻¹ * (c * g) ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hhcgW
  have hcgN : c * g ∈ Subgroup.normalizer (W : Set G) := by
    have := (Subgroup.normalizer (W : Set G)).mul_mem hhN hhcgN
    have hEq : h * (h⁻¹ * (c * g)) = c * g := by group
    rwa [hEq] at this
  refine ⟨c * g, hcgN, ?_⟩
  have hcY : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  calc (c * g) * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ := by group
    _ = c * y * c⁻¹ := by rw [hg]
    _ = y := by rw [hcY]; group

theorem isStronglyPEmbedded_of_weaklyClosed {M P A : Subgroup G} [Fact p.Prime]
    (hM : M ≠ ⊤) (hPM : CFSG.ABGLocalTools.IsSylowOf p P M)
    (hAP : A ≤ P) (hA : A ≠ ⊥) (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hweak : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ P →
      A.map (MulAut.conj g).toMonoidHom = A)
    (hcover : ∀ x ∈ M, orderOf x = p → ∃ m ∈ M, m * x * m⁻¹ ∈ A)
    (hcent : ∀ a ∈ A, orderOf a = p → Subgroup.centralizer ({a} : Set G) ≤ M)
    (hN : Subgroup.normalizer (A : Set G) ≤ M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p M := by
  classical
  have hNP : Subgroup.normalizer (P : Set G) ≤ M := by
    intro g hg
    have hgP : P.map (MulAut.conj g).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hgA : A.map (MulAut.conj g).toMonoidHom ≤ P := by
      rw [← hgP]
      exact Subgroup.map_mono hAP
    exact hN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hweak g hgA))
  have hPindex : ¬ p ∣ P.index := by
    obtain ⟨Pstar, hPPstar⟩ := hPM.isPGroup.exists_le_sylow
    by_cases heq : P = (Pstar : Subgroup G)
    · rw [heq]
      exact Pstar.not_dvd_index
    · have hlt : P < (Pstar : Subgroup G) := lt_of_le_of_ne hPPstar heq
      obtain ⟨Q, hQp, hPQ, hQle⟩ :=
        exists_pGroup_lt_le_normalizer (p := p) (P := P) (R := (Pstar : Subgroup G))
          Pstar.isPGroup' hlt
      have hQM : Q ≤ M := (hQle.trans inf_le_right).trans hNP
      exfalso
      exact hPQ.ne (hPM.eq_of_le hPQ.le hQM hQp).symm
  obtain ⟨P', hP'coe⟩ : ∃ P' : Sylow p G, (P' : Subgroup G) = P :=
    ⟨hPM.isPGroup.toSylow hPindex, IsPGroup.toSylow_coe _ _⟩
  have hpM : p ∣ Nat.card M := by
    have hAM : A ≤ M := hAP.trans hPM.le
    have hpA : p ∣ Nat.card A := by
      rcases (hPM.isPGroup.to_le hAP).card_eq_or_dvd with h1 | h
      · exact absurd (Subgroup.card_eq_one.mp h1) hA
      · exact h
    exact hpA.trans (Subgroup.card_dvd_of_le hAM)
  have hweak' : ∀ t : G, A.map (MulAut.conj t).toMonoidHom ≤ (P' : Subgroup G) →
      A.map (MulAut.conj t).toMonoidHom = A := by
    intro t ht
    exact hweak t (by simpa [hP'coe] using ht)
  have hAP' : A ≤ (P' : Subgroup G) := by simpa [hP'coe] using hAP
  refine ⟨hM, hpM, ?_⟩
  intro g hg hdvd
  obtain ⟨xS, hxSord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom)) p hdvd
  have hxS : (xS : G) ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom := xS.2
  have hxM : (xS : G) ∈ M := (Subgroup.mem_inf.mp hxS).1
  have hxMg : (xS : G) ∈ M.map (MulAut.conj g).toMonoidHom := (Subgroup.mem_inf.mp hxS).2
  have hxord : orderOf (xS : G) = p := by
    rw [Subgroup.orderOf_coe, hxSord]
  let y : G := g⁻¹ * (xS : G) * g
  have hyM : y ∈ M := by
    have h := hxMg
    rw [Subgroup.mem_map_equiv] at h
    have h' : (MulAut.conj g).symm (xS : G) ∈ M := h
    simpa [y, MulAut.conj_symm_apply] using h'
  have hyord : orderOf y = p := by
    have hyeq : y = (MulAut.conj g⁻¹) (xS : G) := by
      simp [y, MulAut.conj_apply]
    rw [hyeq, MulEquiv.orderOf_eq, hxord]
  obtain ⟨m₁, hm₁M, haA⟩ := hcover (xS : G) hxM hxord
  set a : G := m₁ * (xS : G) * m₁⁻¹ with ha_def
  obtain ⟨m₂, hm₂M, hbA⟩ := hcover y hyM hyord
  set b : G := m₂ * y * m₂⁻¹ with hb_def
  have haord : orderOf a = p := by
    have h : a = (MulAut.conj m₁) (xS : G) := by simp [ha_def, MulAut.conj_apply]
    rw [h, MulEquiv.orderOf_eq, hxord]
  have hbord : orderOf b = p := by
    have h : b = (MulAut.conj m₂) y := by simp [hb_def, MulAut.conj_apply]
    rw [h, MulEquiv.orderOf_eq, hyord]
  have haCent : a ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hAcomm a haA z hz).symm
  have hbCent : b ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hAcomm b hbA z hz).symm
  set k : G := m₁ * g * m₂⁻¹ with hk_def
  have hk : k * b * k⁻¹ = a := by
    rw [hk_def, ha_def, hb_def]
    simp only [y]
    group
  obtain ⟨n, hnN, hn⟩ := exists_mem_normalizer_mul_conj_eq_of_weaklyClosed
    (p := p) (P := P') (W := A) hAP' hweak' hbCent haCent hk
  have hnM : n ∈ M := hN hnN
  have hnkCent : n⁻¹ * k ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : (n⁻¹ * k) * b * (n⁻¹ * k)⁻¹ = b := by
      calc (n⁻¹ * k) * b * (n⁻¹ * k)⁻¹ = n⁻¹ * (k * b * k⁻¹) * n := by group
        _ = n⁻¹ * a * n := by rw [hk]
        _ = b := by
            have h := congrArg (fun t => n⁻¹ * t * n) hn
            simpa [mul_assoc] using h.symm
    have hEq : (n⁻¹ * k) * b = b * (n⁻¹ * k) := by
      calc (n⁻¹ * k) * b = (n⁻¹ * k) * b * (n⁻¹ * k)⁻¹ * (n⁻¹ * k) := by group
        _ = b * (n⁻¹ * k) := by rw [hfix]
    exact hEq
  have hnkM : n⁻¹ * k ∈ M := hcent b hbA hbord hnkCent
  have hkM : k ∈ M := by
    have := M.mul_mem hnM hnkM
    have hEq : n * (n⁻¹ * k) = k := by group
    rwa [hEq] at this
  have hgM : g ∈ M := by
    have := M.mul_mem (M.mul_mem (M.inv_mem hm₁M) hkM) hm₂M
    have hEq : m₁⁻¹ * k * m₂ = g := by
      rw [hk_def]
      group
    rwa [hEq] at this
  exact hg hgM

end CFSG.LocalAnalysis.StronglyEmbedded
