module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpEquiv
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotNeighbourStandard
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpFour
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.ClassicalGroups.Symplectic.Sp4PlaneGeneration
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSwap
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpAut
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs

public section

namespace CFSG.StandardType.SpFourOpposite

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner solvable_of_equiv)
open scoped MatrixGroups

section Group

variable {G : Type} [Group G]

private theorem map_le_centralizer_map {M N : Subgroup G} (f : G →* G)
    (h : M ≤ Subgroup.centralizer (N : Set G)) :
    M.map f ≤ Subgroup.centralizer ((N.map f : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (h hx) y hy]

private theorem le_centralizer_of_map_conj {M N : Subgroup G} (w : G)
    (h : M.map (MulAut.conj w).toMonoidHom ≤
      Subgroup.centralizer (N.map (MulAut.conj w).toMonoidHom : Set G)) :
    M ≤ Subgroup.centralizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hxz := Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_map_of_mem _ hx)) _
    (Subgroup.mem_map_of_mem _ hz)
  apply (MulAut.conj w).injective
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hxz

theorem le_centralizer_of_isComponentOf [Finite G] {H J Q₁ Q₂ R : Subgroup G}
    (hJH : CFSG.Assembly.IsComponentOf J H) (hQ₁ : Q₁ ≤ J) (hQ₂ : Q₂ ≤ J)
    {r : G} (hrQ : r ∈ Q₁) (hr : r ∉ Subgroup.centralizer (J : Set G))
    (hC : ∀ g ∈ J, g ∈ Subgroup.centralizer (Q₁ : Set G) →
      g ∈ Subgroup.centralizer (Q₂ : Set G) → g = 1)
    [Group.IsSolvable (Outer ↥J)] [Group.IsPerfect ↥R]
    (hRH : R ≤ H) (hRQ₁ : R ≤ Subgroup.centralizer (Q₁ : Set G))
    (hRQ₂ : R ≤ Subgroup.centralizer (Q₂ : Set G)) :
    R ≤ Subgroup.centralizer (J : Set G) := by
  classical
  have hN : R ≤ Subgroup.normalizer (J : Set G) := fun g hg =>
    CFSG.StandardType.ggMem_normalizer_of_component hJH (hQ₁ hrQ) hr
      (Subgroup.le_normalizer (hRH hg))
      (Subgroup.mem_centralizer_iff.mp (hRQ₁ hg) r hrQ).symm
  let φ : ↥R →* MulAut ↥J := (Subgroup.normalizerMonoidHom J).comp (Subgroup.inclusion hN)
  have hφ : ((QuotientGroup.mk' (inner ↥J)).comp φ) = 1 :=
    CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one _
  intro g hg
  have hinner : φ ⟨g, hg⟩ ∈ inner ↥J := by
    rw [← QuotientGroup.ker_mk' (inner ↥J), MonoidHom.mem_ker]
    exact DFunLike.congr_fun hφ ⟨g, hg⟩
  obtain ⟨j, hj⟩ := hinner
  have hfix : ∀ x (hx : x ∈ J), x ∈ Q₁ ∨ x ∈ Q₂ → (j : G) * x = x * j := by
    intro x hx hxQ
    have h1 : ((φ ⟨g, hg⟩ ⟨x, hx⟩ : ↥J) : G) = g * x * g⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe J _ _
    have hgx : g * x = x * g := by
      rcases hxQ with hxQ | hxQ
      · exact (Subgroup.mem_centralizer_iff.mp (hRQ₁ hg) x hxQ).symm
      · exact (Subgroup.mem_centralizer_iff.mp (hRQ₂ hg) x hxQ).symm
    have h2 : ((MulAut.conj j ⟨x, hx⟩ : ↥J) : G) = (j : G) * x * (j : G)⁻¹ := rfl
    rw [hj] at h2
    have h3 : (j : G) * x * (j : G)⁻¹ = x := by
      rw [← h2, h1, hgx, mul_inv_cancel_right]
    calc (j : G) * x = (j : G) * x * (j : G)⁻¹ * j := by group
      _ = x * j := by rw [h3]
  have hj1 : (j : G) = 1 := hC j j.2
    (Subgroup.mem_centralizer_iff.mpr fun x hx => (hfix x (hQ₁ hx) (Or.inl hx)).symm)
    (Subgroup.mem_centralizer_iff.mpr fun x hx => (hfix x (hQ₂ hx) (Or.inr hx)).symm)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : ((φ ⟨g, hg⟩ ⟨y, hy⟩ : ↥J) : G) = g * y * g⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe J _ _
  have h2 : ((MulAut.conj j ⟨y, hy⟩ : ↥J) : G) = (j : G) * y * (j : G)⁻¹ := rfl
  rw [hj, h1, hj1, one_mul, inv_one, mul_one] at h2
  calc y * g = g * y * g⁻¹ * g := by rw [h2]
    _ = g * y := by group

end Group

section Native

variable {F : Type} [Field F]

theorem eq_one_of_commute_longBlock [CharP F 2] {s : StatedSp 2 F}
    (h₀ : ∀ A : SL(2, F), s * longBlock F 2 0 A = longBlock F 2 0 A * s)
    (h₁ : ∀ A : SL(2, F), s * longBlock F 2 1 A = longBlock F 2 1 A * s) : s = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let X : SL(2, F) := ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two]⟩
  have hX : ((X : Matrix (Fin 2) (Fin 2) F) - 1).det ≠ 0 := by
    have h3 : (X : Matrix (Fin 2) (Fin 2) F) - 1 = !![-1, 1; -1, -1 - 1] := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [X]
    rw [h3, Matrix.det_fin_two_of]
    have h4 : -1 * (-1 - 1) - 1 * -1 = (1 : F) := by linear_combination h2
    rw [h4]
    exact one_ne_zero
  obtain ⟨a, b, hs, -⟩ := CFSG.ComponentClassification.RankTwoClassical.exists_longBlock_mul_longBlock
    hX (h₀ X)
  have hs' : s = longBlock F 2 0 a * longBlock F 2 1 b := hs
  have hcomm : ∀ Y Z : SL(2, F),
      longBlock F 2 1 Y * longBlock F 2 0 Z = longBlock F 2 0 Z * longBlock F 2 1 Y :=
    fun Y Z => (commute_longBlock_longBlock (by decide) Y Z).eq
  have hcen : ∀ c : SL(2, F), (∀ A : SL(2, F), c * A = A * c) → c = 1 := by
    intro c hc
    have hc' : c ∈ Subgroup.center SL(2, F) := Subgroup.mem_center_iff.mpr fun A => (hc A).symm
    obtain ⟨e, he, hec⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc'
    have he1 : e = 1 := CharTwo.sq_injective (by simpa using he)
    apply Subtype.ext
    rw [← hec, he1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have ha : a = 1 := hcen a fun A => by
    have h := h₀ A
    have e1 : longBlock F 2 0 a * longBlock F 2 1 b * longBlock F 2 0 A =
        longBlock F 2 0 (a * A) * longBlock F 2 1 b := by
      rw [mul_assoc, hcomm, ← mul_assoc, ← map_mul]
    have e2 : longBlock F 2 0 A * (longBlock F 2 0 a * longBlock F 2 1 b) =
        longBlock F 2 0 (A * a) * longBlock F 2 1 b := by
      rw [← mul_assoc, ← map_mul]
    rw [hs', e1, e2] at h
    exact longBlock_injective _ (mul_right_cancel h)
  have hb : b = 1 := hcen b fun A => by
    have h := h₁ A
    have e1 : longBlock F 2 0 a * longBlock F 2 1 b * longBlock F 2 1 A =
        longBlock F 2 0 a * longBlock F 2 1 (b * A) := by
      rw [mul_assoc, ← map_mul]
    have e2 : longBlock F 2 1 A * (longBlock F 2 0 a * longBlock F 2 1 b) =
        longBlock F 2 0 a * longBlock F 2 1 (A * b) := by
      rw [← mul_assoc, hcomm, mul_assoc, ← map_mul]
    rw [hs', e1, e2] at h
    exact longBlock_injective _ (mul_left_cancel h)
  rw [hs', ha, hb, map_one, map_one, mul_one]

variable {G : Type} [Group G]

theorem le_centralizer_of_isComponentOf_statedSp [Finite G] [Finite F] [CharP F 2]
    {H J R : Subgroup G} (ψ : StatedSp 2 F →* G) (hψ : Function.Injective ψ)
    (hψJ : ψ.range = J) (hJH : CFSG.Assembly.IsComponentOf J H) [Group.IsPerfect ↥R]
    (hRH : R ≤ H)
    (hRQ : ∀ k : Fin 2, R ≤ Subgroup.centralizer ((ψ.comp (longBlock F 2 k)).range : Set G)) :
    R ≤ Subgroup.centralizer (J : Set G) := by
  classical
  let e : StatedSp 2 F ≃* ↥J := (MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hψJ)
  have : Group.IsSolvable (Outer (StatedSp 2 F)) :=
    CFSG.SeitzReduction.SymplecticPilot.isSolvable_outer_statedSp (n := 2) le_rfl
  have : Group.IsSolvable (Outer ↥J) := solvable_of_equiv e
  have hC : ∀ s : StatedSp 2 F,
      ψ s ∈ Subgroup.centralizer ((ψ.comp (longBlock F 2 0)).range : Set G) →
      ψ s ∈ Subgroup.centralizer ((ψ.comp (longBlock F 2 1)).range : Set G) → s = 1 := by
    intro s h₀ h₁
    refine eq_one_of_commute_longBlock (fun A => hψ ?_) (fun A => hψ ?_)
    · rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp h₀ _ ⟨A, rfl⟩).symm
    · rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp h₁ _ ⟨A, rfl⟩).symm
  let X : SL(2, F) := ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two]⟩
  have hX1 : X ≠ 1 := by
    intro h
    have h00 := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [X] at h00
  have hr : ψ (longBlock F 2 0 X) ∉ Subgroup.centralizer (J : Set G) := by
    intro h
    have hcen : ∀ s : StatedSp 2 F, s * longBlock F 2 0 X = longBlock F 2 0 X * s := by
      intro s
      apply hψ
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp h (ψ s) (hψJ ▸ ⟨s, rfl⟩)
    have h1 : longBlock F 2 0 X = 1 :=
      eq_one_of_commute_longBlock (fun A => (hcen _).symm) (fun A => (hcen _).symm)
    exact hX1 (longBlock_injective 0 (h1.trans (map_one _).symm))
  refine le_centralizer_of_isComponentOf hJH (Q₁ := (ψ.comp (longBlock F 2 0)).range)
    (Q₂ := (ψ.comp (longBlock F 2 1)).range) ?_ ?_ ⟨X, rfl⟩ hr ?_ hRH (hRQ 0) (hRQ 1)
  · rw [← hψJ, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  · rw [← hψJ, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  · intro g hg h₀ h₁
    rw [← hψJ] at hg
    obtain ⟨s, rfl⟩ := hg
    rw [hC s h₀ h₁, map_one]

theorem range_le_centralizer_of_isComponentOf_statedSp [Finite G] [Finite F] [CharP F 2]
    {H J : Subgroup G} (ψ : StatedSp 2 F →* G) (hψ : Function.Injective ψ)
    (hψJ : ψ.range = J) (hJH : CFSG.Assembly.IsComponentOf J H) (ψ' : StatedSp 2 F →* G)
    {S : Subgroup (StatedSp 2 F)} (hS : ⁅S, S⁆ = S)
    (hSle : ¬ S ≤ (longBlock F 2 0).range ⊔ (longBlock F 2 1).range) (hSH : S.map ψ' ≤ H)
    (hSQ : ∀ k : Fin 2,
      S.map ψ' ≤ Subgroup.centralizer ((ψ.comp (longBlock F 2 k)).range : Set G))
    (hJQ : ∀ k : Fin 2, J ≤ Subgroup.centralizer ((ψ'.comp (longBlock F 2 k)).range : Set G)) :
    ψ'.range ≤ Subgroup.centralizer (J : Set G) := by
  have : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.mpr hS
  have : Group.IsPerfect ↥(S.map ψ') := Group.IsPerfect.map ψ'
  have hR := le_centralizer_of_isComponentOf_statedSp ψ hψ hψJ hJH (R := S.map ψ') hSH hSQ
  rw [MonoidHom.range_eq_map,
    ← CFSG.ClassicalGroups.Symplectic.Sp4.longBlock_sup_longBlock_sup_eq_top_of_perfect hS hSle,
    Subgroup.map_sup, Subgroup.map_sup, ← MonoidHom.range_comp, ← MonoidHom.range_comp]
  exact sup_le (sup_le (Subgroup.le_centralizer_iff.mp (hJQ 0))
    (Subgroup.le_centralizer_iff.mp (hJQ 1))) hR

end Native

section Crossing

variable {G : Type} [Group G]

private theorem exists_lift_swap {p n : ℕ} {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {j a c : Fin n}
    (hX : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j)
    (hac : a ≠ c) (ha : a ≠ j) (hc : c ≠ j) :
    ∃ g, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap a c) := by
  have hmem : SpCoord.permAut (p := p) (Equiv.swap a c) ∈
      (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hX]
    exact Subgroup.subset_closure (Or.inr ⟨a, c, hac, ha, hc, rfl⟩)
  obtain ⟨g, hg, -, hgτ⟩ := exists_mem_of_mem_map_congr eta hmem
  exact ⟨g, hg, hgτ⟩

private theorem exists_succ_eq {n : ℕ} {π : Fin (n + 1) ≃ Fin (n + 1)} {i0 x : Fin (n + 1)}
    (hπ : π 0 = i0) (hx : x ≠ i0) : ∃ a : Fin n, π a.succ = x := by
  have h0 : π.symm x ≠ 0 := fun h => hx (by rw [← hπ, ← h, Equiv.apply_symm_apply])
  obtain ⟨a, ha⟩ := Fin.exists_succ_eq.mpr h0
  exact ⟨a, by rw [ha, Equiv.apply_symm_apply]⟩

private theorem shortBlock_range_le_centralizer {F : Type} [Field F] {n : ℕ}
    (κ : StatedSp n F →* G) {a b c : Fin n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (κ.comp (shortBlock F hab)).range ≤
      Subgroup.centralizer ((κ.comp (longBlock F n c)).range : Set G) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨B, rfl⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, (commute_shortBlock_longBlock hab hca hcb A B).eq]

theorem ggSecFiveBCoordBSpFour_cross_of_isComponentOf [Finite G] {p f : ℕ} (hf : 2 ≤ f)
    {Bs L K J : Subgroup G} {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))}
    {i0 j u v : Fin 4} (hji0 : j ≠ i0) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hui0 : u ≠ i0) (hvi0 : v ≠ i0)
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hKeta : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p j)
    (πL : Fin 4 ≃ Fin 4) (κL : StatedSp 3 (GaloisField 2 f) →* G) (hπL : πL 0 = i0)
    (hLs : ∀ (a b : Fin 3) (hab : a ≠ b),
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (πL a.succ) (πL b.succ) : Set G), Bs⁆ =
        (κL.comp (shortBlock (GaloisField 2 f) hab)).range)
    (hLl : ∀ a : Fin 3,
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (πL a.succ) : Set G), Bs⁆ =
        (κL.comp (longBlock (GaloisField 2 f) 3 a)).range)
    (hJX : J = ggBlockComm Bs eta {u, v})
    (ψ : StatedSp 2 (GaloisField 2 f) →* G) (hψ : Function.Injective ψ) (hψJ : ψ.range = J)
    (hψu : (ψ.comp (longBlock (GaloisField 2 f) 2 0)).range =
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta u : Set G), Bs⁆)
    (hψv : (ψ.comp (longBlock (GaloisField 2 f) 2 1)).range =
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta v : Set G), Bs⁆)
    {d : G} (hd : d ∈ ggBsCoordEq Bs eta j i0)
    (hJd : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({d} : Set G))) :
    ∀ a ∈ ⁅Subgroup.centralizer (ggBsCoordEq Bs eta j u : Set G), Bs⁆,
      ∀ b ∈ ⁅Subgroup.centralizer (ggBsCoordEq Bs eta v i0 : Set G), Bs⁆, a * b = b * a := by
  classical
  have hF4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨g₁, hg₁, hτ₁⟩ := exists_lift_swap hKeta hvi0.symm hji0.symm hjv.symm
  obtain ⟨g₂, hg₂, hτ₂⟩ := exists_lift_swap hKeta hui0.symm hji0.symm hju.symm
  obtain ⟨g₃, hg₃, hτ₃⟩ := exists_lift_swap hLeta hjv.symm hvi0 hji0
  obtain ⟨aj, haj⟩ := exists_succ_eq hπL hji0
  obtain ⟨au, hau⟩ := exists_succ_eq hπL hui0
  obtain ⟨av, hav⟩ := exists_succ_eq hπL hvi0
  have hne : ∀ {a b : Fin 3} {x y : Fin 4}, πL a.succ = x → πL b.succ = y → x ≠ y → a ≠ b :=
    fun ha hb hxy hab => hxy (by rw [← ha, ← hb, hab])
  have hajav : aj ≠ av := hne haj hav hjv
  have hajau : aj ≠ au := hne haj hau hju
  have hauav : au ≠ av := hne hau hav huv
  have hR1 : (⁅Subgroup.centralizer (ggBsCoordEq Bs eta j i0 : Set G), Bs⁆).map
      (MulAut.conj g₁).toMonoidHom = (κL.comp (shortBlock (GaloisField 2 f) hajav)).range := by
    rw [ggReflComm_map_conj (g := g₁) (φ := ggConjAut Bs hg₁) (fun _ => rfl)
      (eta_ggConjAut_apply_of_permAut hg₁ hτ₁), Equiv.swap_apply_of_ne_of_ne hji0 hjv,
      Equiv.swap_apply_left, ← haj, ← hav, hLs aj av hajav]
  have hR2 : (⁅Subgroup.centralizer (ggBsCoordEq Bs eta j i0 : Set G), Bs⁆).map
      (MulAut.conj g₂).toMonoidHom = (κL.comp (shortBlock (GaloisField 2 f) hajau)).range := by
    rw [ggReflComm_map_conj (g := g₂) (φ := ggConjAut Bs hg₂) (fun _ => rfl)
      (eta_ggConjAut_apply_of_permAut hg₂ hτ₂), Equiv.swap_apply_of_ne_of_ne hji0 hju,
      Equiv.swap_apply_left, ← haj, ← hau, hLs aj au hajau]
  have : Group.IsPerfect SL(2, GaloisField 2 f) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ hF4
  have hP : Group.IsPerfect ↥(κL.comp (shortBlock (GaloisField 2 f) hajav)).range :=
    Group.IsPerfect.range _
  have : Group.IsPerfect ↥(⁅Subgroup.centralizer (ggBsCoordEq Bs eta j i0 : Set G), Bs⁆) := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective
    rw [Subgroup.map_commutator, hR1]
    exact Subgroup.isPerfect_iff.mp hP
  have hdB : d ∈ Bs := ggBsCoordEq_le j i0 hd
  have hRd : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta j i0 : Set G), Bs⁆ ≤
      Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxd : x ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact Subgroup.mem_centralizer_iff.mp hx d hd
    have hyd : y ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hBc d hdB y hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxd hyd) (inv_mem hxd)) (inv_mem hyd)
  have hRQu : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta j i0 : Set G), Bs⁆ ≤
      Subgroup.centralizer
        ((⁅Subgroup.centralizer (ggBsCoordZero Bs eta u : Set G), Bs⁆ : Subgroup G) : Set G) := by
    apply le_centralizer_of_map_conj g₁
    rw [hR1, ggSingletonComm_map_conj (g := g₁) (φ := ggConjAut Bs hg₁) (fun _ => rfl)
      (eta_ggConjAut_apply_of_permAut hg₁ hτ₁), Equiv.swap_apply_of_ne_of_ne hui0 huv, ← hau,
      hLl au]
    exact shortBlock_range_le_centralizer κL hajav hajau.symm hauav
  have hRQv : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta j i0 : Set G), Bs⁆ ≤
      Subgroup.centralizer
        ((⁅Subgroup.centralizer (ggBsCoordZero Bs eta v : Set G), Bs⁆ : Subgroup G) : Set G) := by
    apply le_centralizer_of_map_conj g₂
    rw [hR2, ggSingletonComm_map_conj (g := g₂) (φ := ggConjAut Bs hg₂) (fun _ => rfl)
      (eta_ggConjAut_apply_of_permAut hg₂ hτ₂), Equiv.swap_apply_of_ne_of_ne hvi0 huv.symm,
      ← hav, hLl av]
    exact shortBlock_range_le_centralizer κL hajau hajav.symm hauav.symm
  have hRJ := le_centralizer_of_isComponentOf_statedSp ψ hψ hψJ hJd hRd
    (Fin.forall_fin_two.mpr ⟨by rw [hψu]; exact hRQu, by rw [hψv]; exact hRQv⟩)
  have hR3 : (⁅Subgroup.centralizer (ggBsCoordEq Bs eta j i0 : Set G), Bs⁆).map
      (MulAut.conj g₃).toMonoidHom = ⁅Subgroup.centralizer (ggBsCoordEq Bs eta v i0 : Set G), Bs⁆ := by
    rw [ggReflComm_map_conj (g := g₃) (φ := ggConjAut Bs hg₃) (fun _ => rfl)
      (eta_ggConjAut_apply_of_permAut hg₃ hτ₃), Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hvi0.symm hji0.symm]
  have hJ3 : J.map (MulAut.conj g₃).toMonoidHom = ggBlockComm Bs eta {u, j} := by
    rw [hJX, ggBlockComm_map_conj hg₃ hτ₃, Set.image_insert_eq, Set.image_singleton,
      Equiv.swap_apply_of_ne_of_ne huv hju.symm, Equiv.swap_apply_left]
  have hX : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta v i0 : Set G), Bs⁆ ≤
      Subgroup.centralizer (ggBlockComm Bs eta {u, j} : Set G) := by
    rw [← hR3, ← hJ3]
    exact map_le_centralizer_map _ hRJ
  have hRju : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta j u : Set G), Bs⁆ ≤
      ggBlockComm Bs eta {u, j} := by
    rw [ggBlockComm]
    refine Subgroup.commutator_mono (Subgroup.centralizer_le ?_) le_rfl
    intro b hb
    obtain ⟨hbB, hb1⟩ := mem_ggBsCoordZeroOn.mp hb
    exact mem_ggBsCoordEq.mpr ⟨hbB, by rw [hb1 j (by simp), hb1 u (by simp)]⟩
  intro a ha b hb
  exact Subgroup.mem_centralizer_iff.mp (hX hb) a (hRju ha)

end Crossing

end CFSG.StandardType.SpFourOpposite

end
