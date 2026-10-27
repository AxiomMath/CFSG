module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenPair
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenFPF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup CFSG.ASVolI.ChIJK
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V A : Subgroup G}

theorem isL2Gp_quotient_of_ker {K L N : Subgroup G} (hLK : L ≤ K) (hNL : N ≤ L)
    [(N.subgroupOf L).Normal] {P : Type} [Group P] (ψ : ↥K →* P)
    (hker : ∀ l : ↥K, (l : G) ∈ L → (ψ l = 1 ↔ (l : G) ∈ N)) {n : ℕ}
    (hS : IsL2Gp ↥(barSub K ψ L) n) : IsL2Gp (↥L ⧸ N.subgroupOf L) n := by
  let f : ↥L →* P := ψ.comp (Subgroup.inclusion hLK)
  have hker' : f.ker = N.subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker (Subgroup.inclusion hLK l) l.2
  have hrange : f.range = barSub K ψ L := by
    ext x
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLK l, l.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  let e : ↥L ⧸ N.subgroupOf L ≃* ↥(barSub K ψ L) :=
    ((QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)
  exact isL2Gp_of_mulEquiv hS e.symm


theorem pair_kernel_eq {K : Subgroup G} (hP : PairHyp V A) (hVK : V ≤ K) (hAK : A ≤ K)
    {P : Type} [Group P] (ψ : ↥K →* P) {n : ℕ} (hn : 2 ≤ n)
    (hS : IsL2Gp ↥(barSub K ψ (V ⊔ A)) n) :
    ∀ l : ↥K, (l : G) ∈ V ⊔ A → (ψ l = 1 ↔ (l : G) ∈ pairY V A) := by
  have hLK : V ⊔ A ≤ K := sup_le hVK hAK
  have hYL : pairY V A ≤ V ⊔ A := sup_le_sup inf_le_left inf_le_left
  haveI hYn : ((pairY V A).subgroupOf (V ⊔ A)).Normal := pairY_normal hP
  have hback : ∀ l : ↥K, (l : G) ∈ pairY V A → ψ l = 1 := by
    intro l hl
    let f : ↥(V ⊔ A) →* P := ψ.comp (Subgroup.inclusion hLK)
    let g : ↥(V ⊔ A) →* ↥(barSub K ψ (V ⊔ A)) :=
      f.codRestrict _ (fun x => ⟨Subgroup.inclusion hLK x, x.2, rfl⟩)
    have hg : Function.Surjective g := by
      intro x
      obtain ⟨k, hk, hkx⟩ := mem_barSub.mp x.2
      exact ⟨⟨k, hk⟩, Subtype.ext hkx⟩
    have hN : (((pairY V A).subgroupOf (V ⊔ A)).map g).Normal := Subgroup.Normal.map hYn g hg
    have hYp : IsPGroup 2 ↥((pairY V A).subgroupOf (V ⊔ A)) :=
      (pairY_isPGroup hP).of_surjective (Subgroup.subgroupOfEquivOfLe hYL).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hYL).symm.surjective
    have hbot := eq_bot_of_normal_isPGroup_of_isL2Gp hn hS hN (hYp.map g)
    have hmem : g ⟨l, hYL hl⟩ ∈ ((pairY V A).subgroupOf (V ⊔ A)).map g :=
      Subgroup.mem_map_of_mem g (Subgroup.mem_subgroupOf.mpr hl)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  let N : Subgroup G := (V ⊔ A) ⊓ ψ.ker.map K.subtype
  have hNL : N ≤ V ⊔ A := inf_le_left
  have hkerN : ∀ l : ↥K, (l : G) ∈ V ⊔ A → (ψ l = 1 ↔ (l : G) ∈ N) := by
    intro l hl
    constructor
    · intro h1
      exact ⟨hl, l, h1, rfl⟩
    · rintro ⟨-, k, hk, hkl⟩
      have hkl' : k = l := Subtype.ext hkl
      subst hkl'
      exact hk
  have hNn : (N.subgroupOf (V ⊔ A)).Normal := by
    have : N.subgroupOf (V ⊔ A) = (ψ.comp (Subgroup.inclusion hLK)).ker := by
      ext l
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact (hkerN (Subgroup.inclusion hLK l) l.2).symm
    rw [this]
    exact MonoidHom.normal_ker _
  have hYN : pairY V A ≤ N := by
    intro y hy
    exact ⟨hYL hy, ⟨⟨y, hLK (hYL hy)⟩, hback ⟨y, hLK (hYL hy)⟩ hy, rfl⟩⟩
  have hS' : IsL2Gp (↥(V ⊔ A) ⧸ N.subgroupOf (V ⊔ A)) n :=
    isL2Gp_quotient_of_ker hLK hNL ψ hkerN hS
  have hEq : N = pairY V A :=
    eq_of_quotient_dihedral_l2_sz (pairHyp_quotient hP) hYN hNL hn hS'
  intro l hl
  constructor
  · intro h1
    exact hEq ▸ (hkerN l hl).mp h1
  · exact hback l

theorem pairY_inf_centralizer_eq_bot {K : Subgroup G} (hP : PairHyp V A) (hVK : V ≤ K)
    (hAK : A ≤ K) {P : Type} [Group P] (ψ : ↥K →* P) {n : ℕ} (hn : 2 ≤ n)
    (hS : IsL2Gp ↥(barSub K ψ (V ⊔ A)) n) {l : G} (hl : l ∈ V ⊔ A) (hlY : l ∉ pairY V A)
    {m : ℕ} (hm : Odd m) (hlm : l ^ m ∈ pairY V A) :
    pairY V A ⊓ Subgroup.centralizer ({l} : Set G) = ⊥ := by
  haveI hYn : ((pairY V A).subgroupOf (V ⊔ A)).Normal := pairY_normal hP
  have hLK : V ⊔ A ≤ K := sup_le hVK hAK
  have hYL : pairY V A ≤ V ⊔ A := sup_le_sup inf_le_left inf_le_left
  have hX : IsL2Gp (↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A)) n :=
    isL2Gp_quotient_of_ker hLK hYL ψ (pair_kernel_eq hP hVK hAK ψ hn hS) hS
  exact inf_centralizer_eq_bot_of_natural hYL hn hX (pairHyp_chief_natural hP) hl hlY hm hlm

end CFSG.LocalAnalysis.WeakClosure81
