module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iInvol
public import CFSG.RankThree.PartTwo.Sec21.Hering233iE16Groups
public import CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64
import CFSG.RankThree.PartTwo.Sec6.Item63
public import CFSG.RankThree.PartTwo.Sec21.Hering233iE16Transport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSp)

namespace Hering233i

open Matrix hiding ext
open scoped Matrix
open CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesSp64
open CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.LowTwoRank

@[expose] noncomputable def sigN (p : Fin 3) : Mat6 :=
  Matrix.single (Sum.inl p) (Sum.inr p) (1 : F4)

@[expose] noncomputable def levN (p q : Fin 3) : Mat6 :=
  Matrix.single (Sum.inl p) (Sum.inl q) (1 : F4) + Matrix.single (Sum.inr q) (Sum.inr p) (1 : F4)

theorem sigN_mul_sigN (p q : Fin 3) : sigN p * sigN q = 0 :=
  Matrix.single_mul_single_of_ne (1 : F4) (Sum.inl p) (Sum.inr p) (Sum.inl q)
    (fun h => nomatch h) 1

theorem levN_mul_levN {p q p' q' : Fin 3} (h1 : q ≠ p') (h2 : p ≠ q') :
    levN p q * levN p' q' = 0 := by
  have e1 : (Matrix.single (Sum.inl p) (Sum.inl q) (1 : F4) : Mat6) *
      Matrix.single (Sum.inl p') (Sum.inl q') (1 : F4) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F4) (Sum.inl p) (Sum.inl q) (Sum.inl p')
      (fun h => h1 (Sum.inl.inj h)) 1
  have e2 : (Matrix.single (Sum.inl p) (Sum.inl q) (1 : F4) : Mat6) *
      Matrix.single (Sum.inr q') (Sum.inr p') (1 : F4) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F4) (Sum.inl p) (Sum.inl q) (Sum.inr q')
      (fun h => nomatch h) 1
  have e3 : (Matrix.single (Sum.inr q) (Sum.inr p) (1 : F4) : Mat6) *
      Matrix.single (Sum.inl p') (Sum.inl q') (1 : F4) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F4) (Sum.inr q) (Sum.inr p) (Sum.inl p')
      (fun h => nomatch h) 1
  have e4 : (Matrix.single (Sum.inr q) (Sum.inr p) (1 : F4) : Mat6) *
      Matrix.single (Sum.inr q') (Sum.inr p') (1 : F4) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F4) (Sum.inr q) (Sum.inr p) (Sum.inr q')
      (fun h => h2 (Sum.inr.inj h)) 1
  simp only [levN, add_mul, mul_add, e1, e2, e3, e4, add_zero]

theorem sigN_mul_levN {p p' q' : Fin 3} (h : p ≠ q') : sigN p * levN p' q' = 0 := by
  have e1 : (Matrix.single (Sum.inl p) (Sum.inr p) (1 : F4) : Mat6) *
      Matrix.single (Sum.inl p') (Sum.inl q') (1 : F4) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F4) (Sum.inl p) (Sum.inr p) (Sum.inl p')
      (fun h => nomatch h) 1
  have e2 : (Matrix.single (Sum.inl p) (Sum.inr p) (1 : F4) : Mat6) *
      Matrix.single (Sum.inr q') (Sum.inr p') (1 : F4) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F4) (Sum.inl p) (Sum.inr p) (Sum.inr q')
      (fun h' => h (Sum.inr.inj h')) 1
  simp only [sigN, levN, mul_add, e1, e2, add_zero]

theorem levN_mul_sigN {p q p' : Fin 3} (h : q ≠ p') : levN p q * sigN p' = 0 := by
  have e1 : (Matrix.single (Sum.inl p) (Sum.inl q) (1 : F4) : Mat6) *
      Matrix.single (Sum.inl p') (Sum.inr p') (1 : F4) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F4) (Sum.inl p) (Sum.inl q) (Sum.inl p')
      (fun h' => h (Sum.inl.inj h')) 1
  have e2 : (Matrix.single (Sum.inr q) (Sum.inr p) (1 : F4) : Mat6) *
      Matrix.single (Sum.inl p') (Sum.inr p') (1 : F4) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F4) (Sum.inr q) (Sum.inr p) (Sum.inl p')
      (fun h' => nomatch h') 1
  simp only [sigN, levN, add_mul, e1, e2, add_zero]

theorem Jm_symm_transpose : (Jm : Mat6)ᵀ = Jm := by
  ext x y
  rw [Matrix.transpose_apply, Jm_apply, Jm_apply]
  by_cases h : x = y.swap
  · rw [if_pos h, if_pos (by rw [h, Sum.swap_swap])]
  · rw [if_neg h, if_neg (fun h' => h (by rw [h', Sum.swap_swap]))]

theorem Jm_mul_single (a b : Fin 3 ⊕ Fin 3) (c : F4) :
    (Jm : Mat6) * Matrix.single a b c = Matrix.single a.swap b c := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single x.swap]
  · rw [Jm_apply, if_pos rfl, Matrix.single_apply, Matrix.single_apply, one_mul]
    by_cases h : a = x.swap
    · have h' : a.swap = x := by rw [h, Sum.swap_swap]
      simp [h, h']
    · have h' : ¬ a.swap = x := fun h'' => h (by rw [← h'', Sum.swap_swap])
      simp [h, h']
  · intro z _ hz
    rw [Jm_apply, if_neg hz, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Jm_sigN_symm (p : Fin 3) : ((Jm : Mat6) * sigN p)ᵀ = Jm * sigN p := by
  rw [sigN, Jm_mul_single, Matrix.transpose_single]
  rfl

theorem Jm_levN_symm (p q : Fin 3) : ((Jm : Mat6) * levN p q)ᵀ = Jm * levN p q := by
  rw [levN, Matrix.mul_add, Jm_mul_single, Jm_mul_single, Matrix.transpose_add,
    Matrix.transpose_single, Matrix.transpose_single]
  simp only [Sum.swap_inl, Sum.swap_inr]
  exact add_comm _ _

theorem single_apply_eq_zero {v : Fin 3 → ZMod 3} {a b x y : Fin 3 ⊕ Fin 3}
    (hab : ext v a = ext v b) (hxy : ext v x ≠ ext v y) :
    (Matrix.single a b (1 : F4) : Mat6) x y = 0 := by
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hxy hab

theorem sigN_block {v : Fin 3 → ZMod 3} {p : Fin 3} (hp : v p = 0) {x y : Fin 3 ⊕ Fin 3}
    (hxy : ext v x ≠ ext v y) : sigN p x y = 0 :=
  single_apply_eq_zero (by
    simp only [ext, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, hp]
    try rfl) hxy

theorem levN_block {v : Fin 3 → ZMod 3} {p q : Fin 3} (hpq : v p = v q) {x y : Fin 3 ⊕ Fin 3}
    (hxy : ext v x ≠ ext v y) : levN p q x y = 0 := by
  rw [levN, Matrix.add_apply, single_apply_eq_zero (by simp [ext, hpq]) hxy,
    single_apply_eq_zero (by simp [ext, hpq]) hxy, add_zero]

theorem nilPair0 : NilPair (sigN 1) (sigN 2) :=
  ⟨sigN_mul_sigN _ _, sigN_mul_sigN _ _, sigN_mul_sigN _ _, sigN_mul_sigN _ _⟩

theorem nilPair1 : NilPair (sigN 2) (levN 0 1) :=
  ⟨sigN_mul_sigN _ _, sigN_mul_levN (by decide), levN_mul_sigN (by decide),
    levN_mul_levN (by decide) (by decide)⟩

theorem nilPair2 : NilPair (levN 0 1) (levN 0 2) :=
  ⟨levN_mul_levN (by decide) (by decide), levN_mul_levN (by decide) (by decide),
    levN_mul_levN (by decide) (by decide), levN_mul_levN (by decide) (by decide)⟩

theorem hind0 : ∀ s t : F4, s • sigN 1 + t • sigN 2 = 0 → s = 0 ∧ t = 0 := by
  intro s t h
  have h1 := congrFun₂ h (Sum.inl 1) (Sum.inr 1)
  have h2 := congrFun₂ h (Sum.inl 2) (Sum.inr 2)
  simp [sigN, Matrix.single_apply] at h1 h2
  exact ⟨h1, h2⟩

theorem hind1 : ∀ s t : F4, s • sigN 2 + t • levN 0 1 = 0 → s = 0 ∧ t = 0 := by
  intro s t h
  have h1 := congrFun₂ h (Sum.inl 2) (Sum.inr 2)
  have h2 := congrFun₂ h (Sum.inl 0) (Sum.inl 1)
  simp [sigN, levN, Matrix.single_apply] at h1 h2
  exact ⟨h1, h2⟩

theorem hind2 : ∀ s t : F4, s • levN 0 1 + t • levN 0 2 = 0 → s = 0 ∧ t = 0 := by
  intro s t h
  have h1 := congrFun₂ h (Sum.inl 0) (Sum.inl 1)
  have h2 := congrFun₂ h (Sum.inl 0) (Sum.inl 2)
  simp [levN, Matrix.single_apply] at h1 h2
  exact ⟨h1, h2⟩

theorem sp_E16_of_pair {v : Fin 3 → ZMod 3} {N₁ N₂ : Mat6} (h : NilPair N₁ N₂)
    (hJ1 : ((Jm : Mat6) * N₁)ᵀ = Jm * N₁) (hJ2 : ((Jm : Mat6) * N₂)ᵀ = Jm * N₂)
    (hind : ∀ s t : F4, s • N₁ + t • N₂ = 0 → s = 0 ∧ t = 0)
    (hb₁ : ∀ x y, ext v x ≠ ext v y → N₁ x y = 0)
    (hb₂ : ∀ x y, ext v x ≠ ext v y → N₂ x y = 0) :
    ∃ E₀ : Subgroup Sp, IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 2 ^ 4 ∧
      E₀ ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set Sp) := by
  obtain ⟨E, hEab, hEcard, hEel⟩ := exists_E16_gfam (⊤ : AddSubgroup F4) (⊤ : AddSubgroup F4)
    (by rw [AddSubgroup.card_top, card_F4]) h two_eq_zero hind
  have hle : E ≤ StatedSp 3 F4 := fun g hg => by
    obtain ⟨s, -, t, -, hgst⟩ := hEel g hg
    rw [mem_statedSp_iff, hgst]
    exact gMat_symp h two_eq_zero Jm_symm_transpose hJ1 hJ2 s t
  refine ⟨E.subgroupOf (StatedSp 3 F4), isElemAbelian_subgroupOf hEab _, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hEcard
  · intro g hg
    obtain ⟨s, -, t, -, hgst⟩ := hEel (g : GL (Fin 3 ⊕ Fin 3) F4) (Subgroup.mem_subgroupOf.mp hg)
    apply mem_centralizer_of_isBlockDiag
    change IsBlockDiag (ext v) ((g : GL (Fin 3 ⊕ Fin 3) F4) : Mat6)
    rw [hgst]
    intro x y hxy
    have hne : x ≠ y := fun e => hxy (by rw [e])
    simp only [gMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hb₁ x y hxy, hb₂ x y hxy,
      mul_zero, add_zero, Matrix.one_apply_ne hne]

theorem normal_comp0 {Y : Subgroup (Subgroup.centralizer
    ({δ (Multiplicative.ofAdd (std 0))} : Set Sp))} (hY : CFSG.IsComponent Y) : Y.Normal := by
  have h := components_std0 hY
  have hY' : Y = S4.subgroupOf (Subgroup.centralizer
      ({δ (Multiplicative.ofAdd (std 0))} : Set Sp)) := by
    rw [← h, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  rw [hY']
  exact normal_subgroupOf_of_iff (κ := 0) mem_S4_iff

theorem normal_comp1 {Y : Subgroup C1} (hY : CFSG.IsComponent Y) : Y.Normal := by
  have hinj : Function.Injective C1.subtype := C1.subtype_injective
  rcases components_std1 hY with h | h
  · have hY' : Y = S2.subgroupOf C1 := by
      rw [← h, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective hinj]
    rw [hY']
    exact normal_subgroupOf_of_iff (κ := 0) mem_S2_iff
  · have hY' : Y = Levi2.subgroupOf C1 := by
      rw [← h, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective hinj]
    rw [hY']
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer Levi2_le_C1).mpr C1_le_normalizer_Levi2

theorem normal_comp2 {Y : Subgroup C3} (hY : CFSG.IsComponent Y) : Y.Normal := by
  have h := components_std2 hY
  have hY' : Y = leviSL3.range.subgroupOf C3 := by
    rw [← h, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C3.subtype_injective]
  rw [hY', subgroupOf_S3]
  exact MonoidHom.normal_ker _

theorem sp_model (i : Fin 3) {c : Sp} (hc : c = δ (Multiplicative.ofAdd (std i))) :
    ∃ E₀ : Subgroup Sp, IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 2 ^ 4 ∧
      E₀ ≤ Subgroup.centralizer ({c} : Set Sp) ∧
      ∀ Y : Subgroup (Subgroup.centralizer ({c} : Set Sp)), CFSG.IsComponent Y → Y.Normal := by
  subst hc
  rcases fin3_cases i with rfl | rfl | rfl
  · obtain ⟨E₀, h1, h2, h3⟩ := sp_E16_of_pair (v := std 0) nilPair0 (Jm_sigN_symm 1)
      (Jm_sigN_symm 2) hind0 (fun x y hxy => sigN_block (by decide) hxy)
      (fun x y hxy => sigN_block (by decide) hxy)
    exact ⟨E₀, h1, h2, h3, fun Y hY => normal_comp0 hY⟩
  · obtain ⟨E₀, h1, h2, h3⟩ := sp_E16_of_pair (v := std 1) nilPair1 (Jm_sigN_symm 2)
      (Jm_levN_symm 0 1) hind1 (fun x y hxy => sigN_block (by decide) hxy)
      (fun x y hxy => levN_block (by decide) hxy)
    exact ⟨E₀, h1, h2, h3, fun Y hY => normal_comp1 hY⟩
  · obtain ⟨E₀, h1, h2, h3⟩ := sp_E16_of_pair (v := std 2) nilPair2 (Jm_levN_symm 0 1)
      (Jm_levN_symm 0 2) hind2 (fun x y hxy => levN_block (by decide) hxy)
      (fun x y hxy => levN_block (by decide) hxy)
    exact ⟨E₀, h1, h2, h3, fun Y hY => normal_comp2 hY⟩

theorem exists_std_pos_Sp {G : Type} [Group G] {I A : Subgroup G} (hAI : A ≤ I)
    (Φ₁ : I ≃* Sp) (hΦ₁A : (A.subgroupOf I).map Φ₁.toMonoidHom = A0) {b : G} (hbA : b ∈ A)
    (hb1 : b ≠ 1) :
    ∃ (Φ : I ≃* Sp) (i : Fin 3) (hbI : b ∈ I), Φ ⟨b, hbI⟩ = δ (Multiplicative.ofAdd (std i)) := by
  have hbI : b ∈ I := hAI hbA
  have hmem : Φ₁ ⟨b, hbI⟩ ∈ A0 := by
    rw [← hΦ₁A]
    exact Subgroup.mem_map.mpr ⟨⟨b, hbI⟩, Subgroup.mem_subgroupOf.mpr hbA, rfl⟩
  obtain ⟨y, hy⟩ : Φ₁ ⟨b, hbI⟩ ∈ δ.range := hmem
  have hv : Multiplicative.toAdd y ≠ 0 := by
    intro h0
    apply hb1
    have hy1 : y = 1 := Multiplicative.toAdd.injective h0
    rw [hy1, map_one] at hy
    have h1 : Φ₁ ⟨b, hbI⟩ = Φ₁ 1 := by rw [map_one]; exact hy.symm
    have := congrArg Subtype.val (Φ₁.injective h1)
    simpa using this
  obtain ⟨σ, s, i, hσ⟩ := exists_flip_perm_std _ hv
  refine ⟨Φ₁.trans ((reindexSp (permE σ) (Jm_permE σ)).trans
    (reindexSp (flipE s) (Jm_flipE s))), i, hbI, ?_⟩
  rw [MulEquiv.trans_apply, ← hy]
  change reindexSp (flipE s) (Jm_flipE s) (reindexSp (permE σ) (Jm_permE σ)
    (δ (Multiplicative.ofAdd (Multiplicative.toAdd y)))) = _
  rw [reindexSp_δ _ (ext_comp_permE σ _), reindexSp_δ _ (ext_comp_flipE s _), hσ]

end Hering233i

open Hering233i CFSG.RankThree.PartTwo.KFacts.KS21.Sp64 CFSG.RankThree.PartTwo.Sec21.TablesSp64 in
theorem terminalE16Sp64 : TerminalE16Sp64 := by
  intro G _ _ I A hAI hAe hT B hBA hB3 X hX
  obtain ⟨⟨e⟩, hA⟩ := hT
  obtain ⟨Φ₁, hΦ₁A⟩ := HeringRootsSp64.exists_Phi_Sp hAI hAe e hA
  obtain ⟨b, hbB, hb1, hBb⟩ := exists_gen_of_card_three hB3
  have hbA : b ∈ A := hBA hbB
  obtain ⟨Φ, i, hbI, hΦb⟩ := exists_std_pos_Sp hAI Φ₁ hΦ₁A hbA hb1
  subst hBb
  have hΦH := map_inf_centralizer_zpowers Φ hbI
  have hHI : I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ≤ I :=
    inf_le_left
  have hY := CFSG.LocalCores.isComponent_map_mulEquiv (thetaK hHI Φ hΦH) hX
  obtain ⟨E₀, hab, hcard, hE₀C, hYn⟩ := sp_model i hΦb
  haveI : (X.map (thetaK hHI Φ hΦH).toMonoidHom).Normal := hYn _ hY
  have hB : E₀ ≤ Subgroup.normalizer
      ((Subgroup.zpowers (Φ ⟨b, hbI⟩) : Subgroup Sp) : Set Sp) := by
    have h1 : Subgroup.centralizer ((Subgroup.zpowers (Φ ⟨b, hbI⟩) : Subgroup Sp) : Set Sp) =
        Subgroup.centralizer ({Φ ⟨b, hbI⟩} : Set Sp) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [h1]
    exact hE₀C hg
  exact transport_E16 Φ hbI X hab hcard hB
    (hE₀C.trans (Sec6.le_normalizer_map_subtype (X.map (thetaK hHI Φ hΦH).toMonoidHom)))

end CFSG.RankThree.PartTwo.Sec21
