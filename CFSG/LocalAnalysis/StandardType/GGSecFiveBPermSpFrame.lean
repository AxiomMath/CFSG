module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpEquiv
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open scoped MatrixGroups

theorem ggSecFiveBSp_fin_val_zero {n : ℕ} [NeZero n] : (0 : Fin n).val = 0 := by
  change 0 % n = 0
  exact Nat.zero_mod n

theorem ggSecFiveBSp_fin_val_one {n : ℕ} [NeZero n] (hn : 1 < n) :
    (1 : Fin n).val = 1 := by
  change 1 % n = 1
  exact Nat.mod_eq_of_lt hn

private theorem ggSecFiveBSp_fin_val_two {n : ℕ} [NeZero n] (hn : 2 < n) :
    (2 : Fin n).val = 2 := by
  change 2 % n = 2
  exact Nat.mod_eq_of_lt hn

theorem ggSecFiveBSp_fin_one_ne_zero {n : ℕ} [NeZero n] (hn : 1 < n) :
    (1 : Fin n) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  rw [ggSecFiveBSp_fin_val_one hn, ggSecFiveBSp_fin_val_zero] at h'
  omega

theorem ggSecFiveBSp_fin_one_ne_two {n : ℕ} [NeZero n] (hn : 2 < n) :
    (1 : Fin n) ≠ 2 := by
  intro h
  have h' := congrArg Fin.val h
  rw [ggSecFiveBSp_fin_val_one (by omega), ggSecFiveBSp_fin_val_two hn] at h'
  omega

private theorem ggSecFiveBSp_fin_zero_ne_two {n : ℕ} [NeZero n] (hn : 2 < n) :
    (0 : Fin n) ≠ 2 := by
  intro h
  have h' := congrArg Fin.val h
  rw [ggSecFiveBSp_fin_val_zero, ggSecFiveBSp_fin_val_two hn] at h'
  omega

theorem ggSecFiveBSp_fin_castSucc_zero {r : ℕ} :
    ((0 : Fin (r + 1)).castSucc : Fin (r + 2)) = 0 := by
  ext
  rw [Fin.val_castSucc, ggSecFiveBSp_fin_val_zero (n := r + 1),
    ggSecFiveBSp_fin_val_zero (n := r + 2)]

theorem ggSecFiveBSp_fin_succ_zero {r : ℕ} :
    ((0 : Fin (r + 1)).succ : Fin (r + 2)) = 1 := by
  ext
  rw [Fin.val_succ, ggSecFiveBSp_fin_val_zero (n := r + 1),
    ggSecFiveBSp_fin_val_one (n := r + 2) (by omega)]

theorem ggSecFiveBSp_fin_succ_one {r : ℕ} (hr : 2 ≤ r) :
    ((1 : Fin (r + 1)).succ : Fin (r + 2)) = 2 := by
  ext
  rw [Fin.val_succ, ggSecFiveBSp_fin_val_one (n := r + 1) (by omega),
    ggSecFiveBSp_fin_val_two (n := r + 2) (by omega)]

private theorem ggSecFiveBSp_fin_succ_last {r : ℕ} :
    (Fin.last r).succ = (Fin.last (r + 1) : Fin (r + 2)) := by
  ext
  rw [Fin.val_succ, Fin.val_last, Fin.val_last]

theorem ggSecFiveBSp_fin_last_succ_ne_two {r : ℕ} (hr : 2 ≤ r) :
    (Fin.last (r + 1) : Fin (r + 2)) ≠ 2 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_last, ggSecFiveBSp_fin_val_two (n := r + 2) (by omega)] at h'
  omega

private theorem ggSecFiveBSp_fin_last_ne_one {r : ℕ} (hr : 2 ≤ r) :
    (Fin.last r : Fin (r + 1)) ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_last, ggSecFiveBSp_fin_val_one (n := r + 1) (by omega)] at h'
  omega

theorem ggSecFiveBSp_fin_last_ne_zero {r : ℕ} (hr : 2 ≤ r) :
    (Fin.last r : Fin (r + 1)) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_last, ggSecFiveBSp_fin_val_zero (n := r + 1)] at h'
  omega

private theorem ggSecFiveBSp_rangeAgreement {G : Type} [Group G] [Finite G]
    {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 2 ≤ f) (hr : 2 ≤ r)
    {Bs L K : Subgroup G} {x y : G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hxBs : x ∈ Bs) (hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hyBs : y ∈ Bs)
    (hKcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ' : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hKF : GGSecFiveBPermSpKFrame Bs K eta π κ χ') :
    ∀ k : Fin r, (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) k.succ)).range =
      (κ.comp (shortBlock (GaloisField 2 f) (Fin.castSucc_lt_succ (i := k)).ne)).range := by
  intro k
  have hLk := ggSecFiveBPermSp_reflComm_L hp2 hr hBc hBsmax hxBs hLcomp hLF (k.succ)
  have hKk := ggSecFiveBPermSp_reflComm_K hp2 hf hr hBc hBsmax hyBs hKcomp hKF
    (i := k.castSucc) (j := k.succ) (hij := (Fin.castSucc_lt_succ (i := k)).ne)
  rw [Fin.castSucc_succ] at hLk
  exact hLk.symm.trans hKk

theorem ggSecFiveBSp_conjData {G : Type} [Group G] [Finite G]
    {p n r : ℕ} [Fact p.Prime] (hr : 2 ≤ r) {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    (hAfull : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    ∃ (w : Equiv.Perm (Fin n)) (φ : MulAut ↥Bs) (g : G),
      w = Equiv.swap (π 0) (π 2) ∧
      (∀ (b : ↥Bs) (i : Fin n), eta (φ b) (w i) = eta b i) ∧
      (∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹) := by
  let w : Equiv.Perm (Fin n) := Equiv.swap (π 0) (π 2)
  have hπ02 : (π 0 : Fin n) ≠ π 2 :=
    π.injective.ne (ggSecFiveBSp_fin_zero_ne_two (n := r + 2) (by omega))
  have hwmem : SpCoord.permAut w ∈ aPermutationFull n p :=
    Subgroup.subset_closure ⟨π 0, π 2, hπ02, rfl⟩
  have hmem : SpCoord.permAut w ∈
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hAfull]
    exact hwmem
  obtain ⟨φ, hφL, hφcongr⟩ := Subgroup.mem_map.mp hmem
  have hφcongr' : MulAut.congr eta φ = SpCoord.permAut w := hφcongr
  obtain ⟨g, -, -, hgconj⟩ := mem_ggAutomizer_iff.mp hφL
  refine ⟨w, φ, g, rfl, ?_, hgconj⟩
  intro b i
  have h1 : eta (φ b) = SpCoord.permAut w (eta b) := by
    rw [show eta (φ b) = MulAut.congr eta φ (eta b) by
      rw [MulAut.congr_apply]
      simp, hφcongr']
  rw [h1, SpCoord.permAut_apply]
  simp

private theorem ggSecFiveBSp_firstMap {G : Type} [Group G] [Finite G]
    {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 2 ≤ f) (hr : 2 ≤ r)
    {Bs L K : Subgroup G} {x y : G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hxBs : x ∈ Bs) (hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hyBs : y ∈ Bs)
    (hKcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ' : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hKF : GGSecFiveBPermSpKFrame Bs K eta π κ χ')
    (h10 : (1 : Fin (r + 1)) ≠ 0)
    {w : Equiv.Perm (Fin n)} {φ : MulAut ↥Bs} {g : G}
    (hw0 : w (π 0) = π 2) (hw1 : w (π 1) = π 1)
    (hwcoord : ∀ (b : ↥Bs) (i : Fin n), eta (φ b) (w i) = eta b i)
    (hgconj : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹) :
    (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range.map
        (MulAut.conj g).toMonoidHom =
      (κ.comp (shortBlock (GaloisField 2 f) h10)).range := by
  have hC1 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 0) (π 1) : Set G), Bs⁆ =
      (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range := by
    have h := ggSecFiveBPermSp_reflComm_L hp2 hr hBc hBsmax hxBs hLcomp hLF
      (0 : Fin (r + 1))
    simpa only [ggSecFiveBSp_fin_castSucc_zero, ggSecFiveBSp_fin_succ_zero] using h
  have hK10 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 2) (π 1) : Set G), Bs⁆ =
      (κ.comp (shortBlock (GaloisField 2 f) h10)).range := by
    have h := ggSecFiveBPermSp_reflComm_K hp2 hf hr hBc hBsmax hyBs hKcomp hKF
      (i := (1 : Fin (r + 1))) (j := (0 : Fin (r + 1))) (hij := h10)
    simpa only [ggSecFiveBSp_fin_succ_one (r := r) hr, ggSecFiveBSp_fin_succ_zero] using h
  calc (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range.map
        (MulAut.conj g).toMonoidHom
      = (⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 0) (π 1) : Set G), Bs⁆).map
          (MulAut.conj g).toMonoidHom := by rw [hC1]
    _ = ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (w (π 0)) (w (π 1)) : Set G), Bs⁆ :=
        ggReflComm_map_conj hgconj hwcoord (π 0) (π 1)
    _ = ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 2) (π 1) : Set G), Bs⁆ := by
        rw [hw0, hw1]
    _ = (κ.comp (shortBlock (GaloisField 2 f) h10)).range := hK10

private theorem ggSecFiveBSp_longMap {G : Type} [Group G] [Finite G]
    {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 2 ≤ f) (hr : 2 ≤ r)
    {Bs K : Subgroup G} {y : G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyBs : y ∈ Bs)
    (hKcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ' : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hKF : GGSecFiveBPermSpKFrame Bs K eta π κ χ')
    {w : Equiv.Perm (Fin n)} {φ : MulAut ↥Bs} {g : G}
    (hwlast : w (π (Fin.last (r + 1))) = π (Fin.last (r + 1)))
    (hwcoord : ∀ (b : ↥Bs) (i : Fin n), eta (φ b) (w i) = eta b i)
    (hgconj : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹) :
    (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range.map
        (MulAut.conj g).toMonoidHom =
      (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range := by
  have hM : ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G),
        Bs⁆ =
      (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range := by
    have h := ggSecFiveBPermSp_singletonComm_K hp2 hf hr hBc hBsmax hyBs hKcomp hKF
      (Fin.last r)
    simpa only [ggSecFiveBSp_fin_succ_last] using h
  calc (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range.map
        (MulAut.conj g).toMonoidHom
      = (⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G),
          Bs⁆).map (MulAut.conj g).toMonoidHom := by rw [hM]
    _ = ⁅Subgroup.centralizer
          (ggBsCoordZero Bs eta (w (π (Fin.last (r + 1)))) : Set G), Bs⁆ :=
        ggSingletonComm_map_conj hgconj hwcoord (π (Fin.last (r + 1)))
    _ = ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G), Bs⁆ := by
        rw [hwlast]
    _ = (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range := hM

private theorem ggSecFiveBSp_commute_image {G : Type} [Group G]
    {r f : ℕ} (hr : 2 ≤ r) {κ : StatedSp (r + 1) (GaloisField 2 f) →* G} {g : G}
    {C : Subgroup G} (h10 : (1 : Fin (r + 1)) ≠ 0)
    (hCmap : C.map (MulAut.conj g).toMonoidHom =
      (κ.comp (shortBlock (GaloisField 2 f) h10)).range)
    (hMmap : (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range.map
        (MulAut.conj g).toMonoidHom =
      (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range) :
    ∀ a ∈ C,
      ∀ b ∈ (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range,
        a * b = b * a := by
  intro a ha b hb
  have hca : (MulAut.conj g) a ∈
      (κ.comp (shortBlock (GaloisField 2 f) h10)).range := by
    rw [← hCmap]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha
  have hcb : (MulAut.conj g) b ∈
      (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range := by
    rw [← hMmap]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hb
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hca
  obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp hcb
  have hcomm : Commute ((MulAut.conj g) a) ((MulAut.conj g) b) := by
    rw [← hA, ← hB]
    exact (CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_shortBlock_longBlock
      (K := GaloisField 2 f) h10 (ggSecFiveBSp_fin_last_ne_one (r := r) hr)
      (ggSecFiveBSp_fin_last_ne_zero (r := r) hr) A B).map κ
  exact (commute_map_iff (MulAut.conj g).injective).mp hcomm

theorem ggSecFiveBPermSp_agreement_crossing_of_frames {G : Type} [Group G] [Finite G]
    {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 2 ≤ f) (hr : 2 ≤ r)
    {Bs X₁ X₂ : Subgroup G} {x y : G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hxBs : x ∈ Bs) (hX₁ : IsComponentOf X₁ (Subgroup.centralizer ({x} : Set G)))
    (hyBs : y ∈ Bs) (hX₂ : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) X₂)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    (hA : (ggAutomizer X₁ Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hσ : GGSecFiveBPermSpLFrame Bs X₁ eta π σ χ)
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ' : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hκ : GGSecFiveBPermSpKFrame Bs X₂ eta π κ χ') :
    (∀ k : Fin r, (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) k.succ)).range =
      (κ.comp (shortBlock (GaloisField 2 f) (Fin.castSucc_lt_succ (i := k)).ne)).range) ∧
    ∀ a ∈ (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range,
      ∀ b ∈ (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range,
        a * b = b * a := by
  refine ⟨ggSecFiveBSp_rangeAgreement hp2 hf hr hBc hBsmax hxBs hX₁ hyBs hX₂ hσ hκ, ?_⟩
  obtain ⟨w, φ, g, hw_eq, hwcoord, hgconj⟩ :=
    ggSecFiveBSp_conjData (r := r) (n := n) (p := p) (L := X₁) (Bs := Bs) (π := π) hr hA
  have h10 : (1 : Fin (r + 1)) ≠ 0 := ggSecFiveBSp_fin_one_ne_zero (by omega)
  have hw0 : w (π 0) = π 2 := by
    rw [hw_eq]
    exact Equiv.swap_apply_left _ _
  have hw1 : w (π 1) = π 1 := by
    rw [hw_eq]
    exact Equiv.swap_apply_of_ne_of_ne
      (π.injective.ne (ggSecFiveBSp_fin_one_ne_zero (n := r + 2) (by omega)))
      (π.injective.ne (ggSecFiveBSp_fin_one_ne_two (n := r + 2) (by omega)))
  have hwlast : w (π (Fin.last (r + 1))) = π (Fin.last (r + 1)) := by
    rw [hw_eq]
    exact Equiv.swap_apply_of_ne_of_ne
      (π.injective.ne (ggSecFiveBSp_fin_last_ne_zero (r := r + 1) (by omega)))
      (π.injective.ne (ggSecFiveBSp_fin_last_succ_ne_two (r := r) hr))
  exact ggSecFiveBSp_commute_image hr h10
    (ggSecFiveBSp_firstMap hp2 hf hr hBc hBsmax hxBs hX₁ hyBs hX₂ hσ hκ
      h10 hw0 hw1 hwcoord hgconj)
    (ggSecFiveBSp_longMap hp2 hf hr hBc hBsmax hyBs hX₂ hκ hwlast hwcoord hgconj)


theorem ggSecFiveBPermSpChartInput_of_frames (hL : GGSecFiveBPermSpLFrameInput)
    (hK : GGSecFiveBPermSpKFrameInput) : GGSecFiveBPermSpChartInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta hBfull hAfull hnbr hG0 f K i0 hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, π, -, κ, χ', hKF⟩ :=
    hK G p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta hBfull hAfull hnbr hG0 f K i0 hcell
  have hn : n = r + 2 := by
    have h := Fintype.card_congr π
    simpa using h.symm
  have hr : 2 ≤ r := by
    have h4' : 4 ≤ r + 2 := hn ▸ h4
    omega
  obtain ⟨σ, χ, hLF⟩ :=
    hL G p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta hBfull hAfull hnbr hG0 f K i0 hcell r π
  obtain ⟨hf, hK𝒦, -, -, -⟩ := hcell
  obtain ⟨-, hBs, hxBs, -, -⟩ := hR.1.1.tableB_facts
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  have hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    (hR.1.1.1.2.2.2.2.2.2.1 : LargeEvenSStar p B x L).2.2.2.1
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hyB : y ∈ B := hNy.1.2.1
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hyB
  have hKcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hNy.1.2.2.2.2.1
  exact ⟨r, hn, σ, κ, hLF.1, hLF.2.1, hKF.1, hKF.2.1,
    ggSecFiveBPermSp_agreement_crossing_of_frames hp2 hf hr hBc hBsmax hxBs hLcomp hyBs hKcomp
      hAfull hLF hKF⟩

end CFSG.StandardType

end
