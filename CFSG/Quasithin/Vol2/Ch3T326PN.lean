module

public import CFSG.Quasithin.Vol2.Ch3T326H
public import CFSG.Quasithin.Vol2.Ch3T326S
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem two_lt_rk_of_dsum {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {n : ℕ} {K : Type} [Field K] [Finite K] {H : Subgroup (MulAut V)} {U Z : Subgroup V} {k : ℕ}
    (h : DirectSumOfCopies H U Z (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)) (k + 1))
    (h8 : 8 ≤ Nat.card K ^ n) : 2 < rk ↥U := by
  obtain ⟨I, π, -, -, hU, hR⟩ := h
  obtain ⟨-, -, -, -, -, -, -, β, hβs, -, -⟩ := hR 0
  have hIU : I 0 ≤ U := hU ▸ le_sup_of_le_right (le_iSup I 0)
  have e2 : Nat.card (↥(FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)).sec ⧸
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)).ker.subgroupOf
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)).sec) = Nat.card K ^ n := by
    change Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin n → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin n → K))).subgroupOf ⊤) = Nat.card K ^ n
    rw [← Subgroup.index_eq_card, Subgroup.bot_subgroupOf, Subgroup.index_bot, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n),
      Fintype.card_fin]
  have h1 := Nat.card_le_card_of_surjective β hβs
  have h2 := Subgroup.card_le_of_le hIU
  rw [e2] at h1
  have h3 : 8 ≤ 2 ^ rk ↥U := by
    rw [← card_eq_two_pow hV U]
    omega
  by_contra hcon
  push Not at hcon
  have : 2 ^ rk ↥U ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hcon
  omega

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem le_centralizer_of_fixV [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] {s : G} (hs : s ∈ T)
    (h : commV (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))) ≤
      fixV (conjAutSub (conjAct (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩)
        (autOn L (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))))) :
    ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
      Subgroup.centralizer (CFSG.conjugate L s : Set G) := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  have hLs : CFSG.conjugate L s ≤ Subgroup.normalizer (VM : Set G) :=
    (Vol2.Ch10.SecA.conjugate_le_fsuL0 hs).trans c.L₀_le_NVM
  have hconj : autOn (CFSG.conjugate L s) VM =
      conjAutSub (conjAct VM ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩) (autOn L VM) :=
    autOn_conjugate c.L_le_NVM (c.T_le_NVM (T.inv_mem hs))
  rw [← hconj, Vol2.Ch11.SecC.B51.commV_autOn c.L_le_NVM,
    Vol2.Ch11.SecC.B51.fixV_autOn hLs] at h
  have hUVM : ⁅VM, L⁆ ≤ VM := Subgroup.le_normalizer_iff_commutator_le_left.mp c.L_le_NVM
  intro x hx
  have h1 : (⟨x, hUVM hx⟩ : ↥VM) ∈ (⁅VM, L⁆).subgroupOf VM := Subgroup.mem_subgroupOf.2 hx
  exact Subgroup.mem_subgroupOf.1 (h h1)

theorem case_iii_of_d321Two [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (h2 : D321Two (autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))))
    (hO2 : IsPSL 3 2 1 ↥(autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))) →
      Nat.card ↥(oTwoUpper
          (autOn (Subgroup.normalizer (conjClosure L T : Set G))
              (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
            Subgroup.centralizer ((autOn (conjClosure L T)
              (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :
                Subgroup _) : Set _))) = 5 ∨
        (Nat.card ↥(oTwoUpper
            (autOn (Subgroup.normalizer (conjClosure L T : Set G))
                (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
              Subgroup.centralizer ((autOn (conjClosure L T)
                (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :
                  Subgroup _) : Set _))) = 25 ∧
          ∀ x ∈ oTwoUpper
            (autOn (Subgroup.normalizer (conjClosure L T : Set G))
                (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
              Subgroup.centralizer ((autOn (conjClosure L T)
                (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :
                  Subgroup _) : Set _)), x ^ 5 = 1)) :
    Case3_2_6_iii T L V₀ ∧ 2 < rk ↥((⁅conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) := by
  obtain ⟨hpsl, hds⟩ := h2
  rw [Vol2.Ch11.SecC.B51.commV_autOn c.L_le_NVM] at hds
  have hexp : ∀ w : ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))), w ^ 2 = 1 :=
    fun w => Subtype.ext (by simpa using c.elemVM.2 w w.2)
  refine ⟨⟨inferInstance, lieModel_of_isPSL hpsl, hds, hO2 hpsl⟩,
    two_lt_rk_of_dsum hexp hds ?_⟩
  rw [Nat.card_zmod]
  norm_num

theorem case_iv_of_d321Three [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (h3 : D321Three (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
      (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))) :
    Case3_2_6_iv T L V₀ ∧
      2 < rk ↥((⁅conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) := by
  obtain ⟨n, hpsl, K, hK, hKfin, hcard, hds⟩ := h3
  have e1 : commV (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))) ⊓
      fixV (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))) =
      (⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊓
        Subgroup.centralizer (conjClosure L T : Set G)).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) := by
    rw [Vol2.Ch11.SecC.B51.commV_autOn c.L_le_NVM, Vol2.Ch11.SecC.B51.fixV_autOn c.L₀_le_NVM]
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [e1, Vol2.Ch11.SecC.B51.commV_autOn c.L_le_NVM] at hds
  have hexp : ∀ w : ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))), w ^ 2 = 1 :=
    fun w => Subtype.ext (by simpa using c.elemVM.2 w w.2)
  have hn2 : 2 ≤ n := by
    obtain ⟨⟨-, hn1, -, hne, -⟩, -⟩ := hpsl
    by_contra hlt
    have hn : n = 1 := by omega
    subst hn
    exact hne rfl
  refine ⟨⟨n, K, hK, hKfin, hcard, lieModel_of_isPSL hpsl, hds⟩, two_lt_rk_of_dsum hexp hds ?_⟩
  rw [hcard, ← pow_mul]
  calc 8 ≤ 2 ^ 4 := by norm_num
    _ ≤ 2 ^ (n * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Ctx

end CFSG.Quasithin.H13.T326
