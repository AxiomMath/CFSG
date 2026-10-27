module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136S
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136U
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrNDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem step1 (h133N : R4_133N) (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    {t : MulAut W} (S : Std136 Y t) {p : ℕ} (hp : p.Prime)
    (hne : ⁅pCoreOf p Y, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ L : Subgroup (MulAut W), Conc4_136W Y t L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hw2' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hw2 w
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hleP2 : pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hpCore2 : pCoreOf 2 Y = ⊥ :=
    S.o2 (pCoreOf 2 Y) hleP2
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hleP2).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have ht2ord : orderOf t = 2 := S.t2
  have ht2 : t ^ 2 = 1 := by simpa [ht2ord] using pow_orderOf_eq_one t
  have htne : t ≠ 1 := by
    rintro rfl
    simp at ht2ord
  obtain ⟨L, N, hLN, hNP, hNnorm, hU1, hU3, h133⟩ :=
    h133N W hw2' Y t S.tY ht2 htne S.cost hpCore2 S.basic.1 p hp hne
  obtain ⟨p', hp', hLp', hcomm133, hind, hcases⟩ := h133
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hpCore2] at hne
    exact hne (Subgroup.commutator_bot_left (Subgroup.zpowers t))
  have hLne : L ≠ ⊥ := by
    rintro rfl
    exact hcomm133 (Subgroup.commutator_bot_left (Subgroup.zpowers t))
  have hLP : L ≤ pCoreOf p Y := hLN.trans hNP
  have hLY : L ≤ Y := hLP.trans (CFSG.LieType.BorelTits.pCoreOf_le p Y)
  let H : Subgroup (MulAut W) := ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom
  have hHP : H ≤ pCoreOf p Y := by
    refine iSup₂_le fun φ hφ => ?_
    have hnorm : φ ∈ Subgroup.normalizer (pCoreOf p Y : Set (MulAut W)) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := p) Y hφ
    have hmap : (pCoreOf p Y).map (MulAut.conj φ).toMonoidHom = pCoreOf p Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm
    exact (Subgroup.map_mono hLP).trans (le_of_eq hmap)
  have hHY : H ≤ Y := hHP.trans (CFSG.LieType.BorelTits.pCoreOf_le p Y)
  have hHn : (H.subgroupOf Y).Normal := by
    let Hsub : Subgroup (MulAut W) :=
      ⨆ φ : Y, L.map (MulAut.conj (φ : MulAut W)).toMonoidHom
    have hHsub : H = Hsub :=
      (iSup_subtype'' (Y : Set (MulAut W))
        fun φ => L.map (MulAut.conj φ).toMonoidHom).symm
    rw [Subgroup.normal_subgroupOf_iff hHY]
    intro h k hh hk
    rw [hHsub] at hh ⊢
    refine Subgroup.iSup_induction (C := fun x => k * x * k⁻¹ ∈ Hsub)
      (fun φ : Y => L.map (MulAut.conj (φ : MulAut W)).toMonoidHom) hh ?_ ?_ ?_
    · intro φ z hz
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_iSup_of_mem (⟨k * (φ : MulAut W), Y.mul_mem hk φ.2⟩ : Y) ?_
      refine Subgroup.mem_map.mpr ⟨l, hl, ?_⟩
      show (MulAut.conj (k * (φ : MulAut W))).toMonoidHom l =
        k * (MulAut.conj (φ : MulAut W)).toMonoidHom l * k⁻¹
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · intro x z hx hz
      have heq : k * (x * z) * k⁻¹ = (k * x * k⁻¹) * (k * z * k⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ hx hz
  have hPp : IsPGroup p (pCoreOf p Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup p Y
  have hHp : IsPGroup p H := hPp.to_le hHP
  have hodd : Odd (Nat.card H) := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hLH : L ≤ H := by
    have h1 : L.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L := by
      ext x; simp [MulAut.conj]
    rw [← h1]
    exact le_iSup₂_of_le (1 : MulAut W) Y.one_mem le_rfl
  have hH1 : H ≠ ⊥ := by
    intro hbot
    exact hLne (le_bot_iff.mp (hbot ▸ hLH))
  have hcommH : commSub ⊤ H = ⊤ :=
    comm_top_of_odd S hw2 hHY hHn hodd hH1
  have hspan : (⨆ X ∈ conjSubs Y (commSub ⊤ L), X) = ⊤ :=
    lemmaS hLY hcommH
  have hU := lemmaU hw2' hLN (hNP.trans (CFSG.LieType.BorelTits.pCoreOf_le p Y))
    hNnorm hU1 hind hspan hU3
  exact ⟨L, hspan, hU, Or.inl ⟨p', hp', hLp', hcomm133, hind, hcases⟩⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
