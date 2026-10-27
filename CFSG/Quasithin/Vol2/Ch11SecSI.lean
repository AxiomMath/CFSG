module

public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.Quasithin.Vol2.Ch11SecSQuot

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_pCoreOf_of_solvable {B N : Subgroup G} {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : ↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) K) (hNB : N ≤ B)
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) (hNs : Group.IsSolvable ↥N) :
    N ≤ pCoreOf 2 B := by
  have hnorm : CFSG.pCore 2 ↥B |>.Normal := CFSG.pCore_normal
  set φ := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥B)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hNn : (N.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNB).mpr hBN
  have hs : Group.IsSolvable ↥(N.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNB).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNB).injective
  have hs' : Group.IsSolvable ↥((N.subgroupOf B).map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective (N.subgroupOf B))
  have := isSimpleGroup_SL2 hn hK
  have := hNn.map φ hφs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf B).map φ) with hbot | htop
  · intro x hx
    have hx' : (⟨x, hNB hx⟩ : ↥B) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have : φ ⟨x, hNB hx⟩ ∈ (N.subgroupOf B).map φ := ⟨⟨x, hNB hx⟩, hx, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    have hker : φ.ker = CFSG.pCore 2 ↥B := by
      ext y
      simp [hφ]
    rw [hker] at hx'
    rw [pCoreOf_two_eq_map]
    exact ⟨⟨x, hNB hx⟩, hx', rfl⟩
  · exfalso
    rw [htop] at hs'
    have hsl : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv (G := Matrix.SpecialLinearGroup (Fin 2) K)).toMonoidHom)
        (Subgroup.topEquiv (G := Matrix.SpecialLinearGroup (Fin 2) K)).surjective
    have hcomm := (IsSimpleGroup.comm_iff_isSolvable).mpr hsl
    obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_SL2 (exists_finset_card_four hn hK)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm x y]

end CFSG.Quasithin.Vol2.Ch11.SecS
