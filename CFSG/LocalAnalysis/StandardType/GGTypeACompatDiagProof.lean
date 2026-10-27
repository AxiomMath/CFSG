module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLin
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagRoot
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagCompat
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagCoord
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagBlock
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagCard
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagTorus
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLift
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix

section Cfg

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}

private theorem GGTypeANbrCfg.ne_two (hN : GGTypeANbrCfg p B Bs x L D J n f y K) : p ≠ 2 :=
  hN.1.1.2.2.2.2.2.1.2.1

private theorem GGTypeANbrCfg.nbr (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    GGNbr p B x D J y K :=
  hN.2.2.2.2.2.2.2.2.1

private theorem GGTypeANbrCfg.isElemAbelian (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    IsElemAbelian p Bs :=
  hN.1.2.1.2.1

private theorem GGTypeANbrCfg.two_eq_zero (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    (2 : GaloisField 2 f) = 0 :=
  two_eq_zero_of_card (GaloisField.card 2 f (by have := hN.one_le_f; omega)) hN.one_le_f

section Certs

theorem GGTypeANbrCfg.exists_diagLift_L (hMp : GGInnerDiagMpInput)
    (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ∃ φ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ.range = L ∧
      φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      ∀ b ∈ Bs, GGActsDiag φ b := by
  have hn := hN.three_le
  obtain ⟨hf, φ₀, hrange, hker⟩ := GGTypeANbr.exists_lift hN.1 hN.2.2.2.2
  have hA := exists_mem_ggInducedPairs_of_innerDiagOn hMp (n := n) (f := f) (by omega)
    hN.2.2.2.2.1.1 hN.2.2.1.1 hker hrange
  exact exists_lift_actsDiag_of_bstar hN.prime hN.ne_two hf hN.dvd_two_pow_sub_one hN.isElemAbelian
    hN.1.bstar_inf_centralizer_L hN.card_bstar_ge.1 hker hrange hA

theorem GGTypeANbrCfg.bstar_inf_centralizer_J_le (hMp : GGInnerDiagMpInput)
    (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  obtain ⟨φ, hrange, hker, hdiag⟩ := hN.exists_diagLift_L hMp
  have hxB : x ∈ Bs := hN.x_mem
  have hyB : y ∈ Bs := hN.y_mem
  obtain ⟨dx, hdx⟩ := hdiag x hxB
  obtain ⟨dy, hdy⟩ := hdiag y hyB
  have hb : ∀ k : Fin 2, (![x, y] k, InnerDiagA.diagGL (![dx, dy] k)) ∈
      LinFusion.ggInducedPairs φ := by
    intro k
    fin_cases k
    · exact ggActsVec_iff_mem_ggInducedPairs.1 hdx
    · exact ggActsVec_iff_mem_ggInducedPairs.1 hdy
  have hrng : Set.range ![x, y] = {x, y} := by
    ext g
    simp [Fin.exists_fin_two, eq_comm]
    tauto
  have hDc : Subgroup.centralizer (D : Set G) = Subgroup.centralizer (Set.range ![x, y]) := by
    rw [hN.nbr.2.1, Subgroup.centralizer_closure, hrng]
  have hJc : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (Set.range ![x, y])) := by
    rw [hrange, ← hDc]
    exact hN.1.2.2.1.2.2.2.2.2.1
  obtain ⟨i, hI, -, hJi⟩ := (LinSemisimple.isComponentOf_iff_exists_eq_map_blockSpecialLinear
    hker hb).1 hJc
  obtain ⟨T, hT1, hT2, hTJ, hBT⟩ := exists_twoSubgroup_le_map_blockSpecialLinear hker
    (fun b hb' => hdiag b (hN.1.2.1.1 hb')) hI
  exact ggStdSubBstarCentralizer_of_twoSubgroup hN.1 ⟨T, hT1, hT2, hJi ▸ hTJ, hBT⟩

theorem GGTypeANbrCfg.exists_lift_L_lowerBlock (hMp : GGInnerDiagMpInput)
    (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ∃ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (∀ b ∈ Bs, GGActsDiag φ₁ b) ∧
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J := by
  obtain ⟨φ, hrange, hker, hdiag⟩ := hN.exists_diagLift_L hMp
  have hCJ := hN.bstar_inf_centralizer_J_le hMp
  have hD : ∀ r, ∃ g ∈ Bs, ∃ τ : (GaloisField 2 f)ˣ, τ ≠ 1 ∧ GGActsVec φ g (diagAt r τ) :=
    fun r => exists_actsVec_diagAt_of_bstar hN.two_eq_zero hN.prime hN.dvd_natCard_units
      hN.isElemAbelian hN.bs_centralizer hker hdiag
      (by rw [hrange]; exact (hN.1.card_bstar_inf_centralizer_L).le) hN.card_bstar_ge.2 r
  have hJc : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hrange]
    exact hN.1.2.2.1.2.2.2.2.2.1
  obtain ⟨r, hr⟩ := exists_eq_map_blockSpecialLinear_erase hN.prime hN.isElemAbelian hker hdiag hD
    hN.x_mem hN.y_mem (fun s => hN.x_comm_of_mem_L (φ s) (hrange ▸ ⟨s, rfl⟩))
    (fun h => hN.not_y_comm_L fun l hl => by
      rw [← hrange] at hl
      obtain ⟨s, rfl⟩ := hl
      exact h s)
    hN.nbr.2.1 hJc hCJ
  obtain ⟨φ', hr', hk', hd', hJ'⟩ := exists_lift_lowerBlock_eq hN.two_eq_zero hker hdiag r
  exact ⟨φ', hr'.trans hrange, hk', hd', hJ'.trans hr.symm⟩

theorem GGTypeANbrCfg.exists_diagLift_K (hMp : GGInnerDiagMpInput)
    (hN : GGTypeANbrCfg p B Bs x L D J n f y K)
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K) :
    ∃ φ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ.range = K ∧
      φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      ∀ b ∈ Bs, GGActsDiag φ b := by
  have hn := hN.three_le
  obtain ⟨φ₀, hrange, hker⟩ := hN.exists_lift_K
  have hA := exists_mem_ggInducedPairs_of_innerDiagOn hMp (n := n) (f := f) (by omega)
    hN.2.2.2.2.1.1 (hN.2.2.1.2 y K hN.nbr) hker hrange
  exact exists_lift_actsDiag_of_bstar hN.prime hN.ne_two hN.one_le_f hN.dvd_two_pow_sub_one
    hN.isElemAbelian (GGNbr.bstar_inf_centralizer_eq_zpowers hN.1 hN.nbr hCJ hJK)
    hN.card_bstar_ge.1 hker hrange hA

theorem GGTypeANbrCfg.exists_lift_K_upperBlock (hMp : GGInnerDiagMpInput)
    (hN : GGTypeANbrCfg p B Bs x L D J n f y K)
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K) :
    ∃ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₂.comp (slUpperBlockHom n (GaloisField 2 f))).range = J := by
  obtain ⟨φ, hrange, hker, hdiag⟩ := hN.exists_diagLift_K hMp hCJ hJK
  have hnbr : GGNbr p B x D J y K := hN.nbr
  have hD : ∀ r, ∃ g ∈ Bs, ∃ τ : (GaloisField 2 f)ˣ, τ ≠ 1 ∧ GGActsVec φ g (diagAt r τ) :=
    fun r => exists_actsVec_diagAt_of_bstar hN.two_eq_zero hN.prime hN.dvd_natCard_units
      hN.isElemAbelian hN.bs_centralizer hker hdiag
      (by rw [hrange]; exact (GGNbr.card_bstar_inf_centralizer hN.1 hnbr hCJ hJK).le)
      hN.card_bstar_ge.2 r
  have hDD : D = Subgroup.closure {y, x} := by rw [hnbr.2.1, Set.pair_comm]
  have hJL : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hN.1.2.2.1.2.2.2.2.2.1
  have hJxy : IsComponentOf J
      (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_stdSub hN.1.1.2.2.2.2.2.2.1 hN.1.2.2.1 hnbr.2.1
  have hCD : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (by
      rw [Set.singleton_subset_iff, hnbr.2.1]
      exact Subgroup.subset_closure (Set.mem_insert _ _))
  have hJle : J ≤ K ⊓ Subgroup.centralizer (D : Set G) := le_inf hJK (hJL.1.trans inf_le_right)
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hN.y_comm_of_mem_K k hk).symm
  have hJc : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hrange]
    exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hJxy hJle
      (inf_le_inf hKy hCD)
  obtain ⟨r, hr⟩ := exists_eq_map_blockSpecialLinear_erase hN.prime hN.isElemAbelian hker hdiag hD
    hN.y_mem hN.x_mem (fun s => hN.y_comm_of_mem_K (φ s) (hrange ▸ ⟨s, rfl⟩))
    (fun h => hN.not_x_comm_K fun k hk => by
      rw [← hrange] at hk
      obtain ⟨s, rfl⟩ := hk
      exact h s)
    hDD hJc hCJ
  obtain ⟨φ', hr', hk', hd', hJ'⟩ := exists_lift_upperBlock_eq hN.two_eq_zero hker hdiag r
  exact ⟨φ', hr'.trans hrange, hk', hJ'.trans hr.symm⟩

end Certs

end Cfg

section Target

theorem ggTypeACompatDiagBInput_of_known (hMp : GGInnerDiagMpInput) (hL : GGLBalanceInput) :
    GGTypeACompatDiagBInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  have hn3 := hN.three_le
  obtain ⟨φ₁, hφ₁L, hk₁, hdiag₁, hφ₁J⟩ := hN.exists_lift_L_lowerBlock hMp
  have hCJ := hN.bstar_inf_centralizer_J_le hMp
  have hpJ : p ∣ Nat.card J := hφ₁J ▸ prime_dvd_card_range_comp_slLowerBlockHom hN.prime
    hN.dvd_natCard_units (by omega) hk₁
  have hJK : J ≤ K := le_of_ggNbr hL hN.1.1 hN.1.2.2 hpJ hN.nbr
  obtain ⟨φ₂₀, hφ₂L, hk₂₀, hφ₂J⟩ := hN.exists_lift_K_upperBlock hMp hCJ hJK
  obtain ⟨φ₂, hr₂, hk₂, hc⟩ := exists_slCompat_lift hn3 hk₁ hk₂₀ (hφ₁J.trans hφ₂J.symm)
  have hA₂ := exists_mem_ggInducedPairs_of_innerDiagOn hMp (n := n) (f := f) (by omega)
    hN.2.2.2.2.1.1 (hN.2.2.1.2 y K hN.nbr) hk₂ (hr₂.trans hφ₂L)
  exact ⟨φ₁, φ₂, hφ₁L, hk₁, hr₂.trans hφ₂L, hk₂, hφ₁J, hc, fun b hb =>
    ⟨hdiag₁ b hb, ggActsDiag_of_compat hn3 hk₂ hc (hdiag₁ b hb) (hA₂ b hb)⟩⟩

end Target

end CFSG.StandardType

end
