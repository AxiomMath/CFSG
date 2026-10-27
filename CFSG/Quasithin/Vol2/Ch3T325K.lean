module

public import CFSG.Quasithin.Vol2.Ch3T325I
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.Background.InternalSecB56M

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

theorem commutator_eq_or_eq_bot {Ω : Type*} [Group Ω] {K A : Subgroup Ω}
    (hK : CFSG.IsQuasisimple ↥K) (hA : A ≤ Subgroup.normalizer (K : Set Ω)) :
    ⁅K, A⁆ = K ∨ ⁅K, A⁆ = ⊥ := by
  have hle : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hA
  have hN : ((⁅K, A⁆ : Subgroup Ω).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left K A)
  have hKo := B1Red.isQuasisimple_to_open hK
  have hKK : ⁅K, K⁆ = K := by
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ K.subtype
    rw [← commutator_def, hKo.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact h2.symm
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hKo
      ((⁅K, A⁆ : Subgroup Ω).subgroupOf K) with h | h
  · right
    have hc : ⁅⁅K, A⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hx' : (⟨x, hle hx⟩ : ↥K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := hx
      have := Subgroup.mem_center_iff.mp (h hx') ⟨k, hk⟩
      exact congrArg Subtype.val this
    have hc' : ⁅⁅A, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm A K]; exact hc
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate hc hc'
    rwa [hKK] at h3
  · left
    refine le_antisymm hle fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := by rw [h]; trivial
    exact this

section B56

variable {V : Type} [CommGroup V] [Finite V]

theorem b56Case1_of_commV {J K : Subgroup (MulAut V)} (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hcomm : commV K = ⊤)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    B56Case1 J := by
  have htop : ∀ {X : Subgroup (MulAut V)}, K ≤ X → commV X = ⊤ := fun h =>
    top_le_iff.1 (by rw [← hcomm]; exact commV_le_commV h)
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, -, W₁, W₂, -, -, -, -, -, hWinf, hp₁, hp₂⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, -, hc₂, -, -, ⟨-, hV12⟩, -, hcV₂, ht₁, ht₂, -⟩ |
      ⟨_, _, -, -, -, -, -, -, hidx, -⟩
  · exact h1
  · exact (not_le_perm_three hK hKJ e).elim
  · exfalso
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · have hW₁ : W₁ = ⊤ := top_le_iff.1 ((htop h).symm.le.trans (commV_le_of_b56Piece hp₁))
      rw [hW₁, top_inf_eq] at hWinf
      rw [hWinf] at hp₂
      exact not_b56Piece_self hp₂
    · have hW₂ : W₂ = ⊤ := top_le_iff.1 ((htop h).symm.le.trans (commV_le_of_b56Piece hp₂))
      rw [hW₂, inf_top_eq] at hWinf
      rw [hWinf] at hp₁
      exact not_b56Piece_self hp₁
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hK with h | h
    · rw [htop h, top_inf_eq] at hV12
      rw [hV12, Subgroup.card_bot] at hcV₂
      norm_num at hcV₂
    · exact not_le_of_card_prime hK h hc₂
  · exfalso
    rw [htop hKJ, top_sup_eq, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)

end B56

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem exists_offender
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))]
    (hJ : L = ⁅L, thompsonJ T⁆) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      IsFFStarOffender (autOn (Subgroup.normalizer (L : Set G))
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
        (autOn A (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))) ∧
      ⁅autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))),
        autOn A (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))⁆ =
        autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set VM := conjClosure (conjClosure V₀ T) M with hVMdef
  have hWe := c.elemVM
  have hTW : T ≤ Subgroup.normalizer (VM : Set G) := c.T_le_M.trans (M_le_NVM T L V₀)
  have hLW : L ≤ Subgroup.normalizer (VM : Set G) :=
    Subgroup.le_normalizer.trans (M_le_NVM T L V₀)
  have hq := c.quasi_LVM
  have hnorm : ∀ A : Subgroup G, A ≤ T →
      autOn A VM ≤ Subgroup.normalizer (autOn L VM : Set (MulAut ↥VM)) := by
    intro A hAT x hx
    have hc := autOn_normal_of (U := VM) (hAT.trans c.T_le_M)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hc x hx k hk, fun hk => ?_⟩
    have := hc x⁻¹ ((autOn A VM).inv_mem hx) _ hk
    simpa [mul_assoc] using this
  by_cases hex : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ⁅autOn L VM, autOn A VM⁆ = autOn L VM
  · obtain ⟨A, hA, hLA⟩ := hex
    have hAC : ¬ A ≤ Subgroup.centralizer (VM : Set G) := by
      intro hAC
      have h0 : autOn A VM = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0, Subgroup.commutator_bot_right] at hLA
      refine not_commute_of_isQuasisimple hq fun a ha b hb => ?_
      rw [← hLA, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have hoff : IsFFOffender M VM A := ⟨isMaxElemAbelian_of_isSylowTwoOf c.sylowM hA, hAC⟩
    exact ⟨A, hA, offenderImages_isFFStarOffender hWe c.redVM.1 (M_le_NVM T L V₀)
      ⟨A, hoff, rfl⟩, hLA⟩
  · exfalso
    push Not at hex
    have hbot : ∀ A : Subgroup G, IsMaxElemAbelian T A →
        autOn A VM ≤ Subgroup.centralizer (autOn L VM : Set (MulAut ↥VM)) := by
      intro A hA
      rcases commutator_eq_or_eq_bot hq (hnorm A hA.1) with h1 | h1
      · exact absurd h1 (hex A hA)
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (Subgroup.mem_centralizer_iff.mp (h1 hk) x hx).symm
    set S : Subgroup G :=
      ((Subgroup.centralizer (autOn L VM : Set (MulAut ↥VM))).comap (conjAct VM)).map
        (Subgroup.normalizer (VM : Set G)).subtype with hS
    have hJS : thompsonJ T ≤ S := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      have haN : a ∈ Subgroup.normalizer (VM : Set G) := hTW (hA.1 ha)
      exact ⟨⟨a, haN⟩, hbot A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
    apply c.not_le_centralizer_VM
    have key : ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VM : Set G) := by
      rw [Subgroup.commutator_le]
      intro l hl j hj
      obtain ⟨g, hg, rfl⟩ := hJS hj
      set lN : ↥(Subgroup.normalizer (VM : Set G)) := ⟨l, hLW hl⟩
      have hlK : conjAct VM lN ∈ autOn L VM := conjAct_mem_autOn hLW hl
      have hcomm : conjAct VM ⁅lN, g⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp hg _ hlK)
      exact (convI_eq_one_iff hWe ⁅lN, g⁆).1 hcomm
    rwa [← hJ] at key

end Ctx

end CFSG.Quasithin.H13.T325
