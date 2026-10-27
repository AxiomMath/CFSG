module

public import CFSG.Quasithin.Vol2.E2NineTI2bRank
public import CFSG.Quasithin.Vol2.E2NineTIProof
public import CFSG.Quasithin.Vol2.Ch3E213MP5F
public import CFSG.Quasithin.Vol2.E2SevenSp4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

namespace TI2b

theorem diag_of_star_top {A : Type} [Group A] [Finite A] {Ts Ms K : Subgroup A}
    (hJ : kerIn Ms ⊤ = ⊥)
    (hD : IsDiagramNontrivial (star Ms ⊤ Ts) (star Ms ⊤ K) (star Ms ⊤ (Ts ⊓ K))) :
    ∀ P : Subgroup A, IsMaxParabolic2 K P →
      K ⊓ Subgroup.normalizer ((Ts ⊓ K : Subgroup A) : Set A) ≤ P →
        ¬ Ts ≤ Subgroup.normalizer (P : Set A) := by
  intro P hP hle hTsP
  let e₀ : A ≃* StarQuot Ms ⊤ := MulEquiv.ofBijective
    ((E2P.starMap Ms ⊤).comp (Subgroup.topEquiv (G := A)).symm.toMonoidHom)
    ⟨(starMap_injective_of_kerIn_eq_bot hJ).comp (Subgroup.topEquiv (G := A)).symm.injective,
      (E2P.starMap_surjective Ms ⊤).comp (Subgroup.topEquiv (G := A)).symm.surjective⟩
  have hstar : ∀ X : Subgroup A, star Ms ⊤ X = X.map e₀.toMonoidHom := by
    intro X
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, hxX, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mp hxX, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_top x⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  refine hD (P.map e₀.toMonoidHom) ?_ ?_ ?_
  · rw [hstar K]
    exact Ch3E213M.P5.isMaxParabolic2_map_equiv e₀ hP
  · rw [hstar K, hstar (Ts ⊓ K), ← Ch3E213M.P5.map_inf_normalizer e₀]
    exact Subgroup.map_mono hle
  · rw [hstar Ts]
    exact Ch3E213M.P5.map_le_normalizer e₀ hTsP

theorem as_E_2_9_nStarTI_2b_of_leaves (hL3 : L3Leaf) (hSp4 : Sp4Leaf) :
    ASInputs.AS_E_2_9_nStarTI_2b := by
  intro G _ _ H T M V h hTI hsq K n hKc hHK hTK hn1 hty hD hBor
  have := E2P.finite_starQuot M H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with hlt | hn2
  · obtain rfl : n = 1 := by omega
    exact_mod_cast h.one_le_nParam
  have hKH : K ≤ (⊤ : Subgroup (StarQuot M H)) := le_top
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  have hmpY := E2P.minParabolic_star h.minParabolic
  have hJY : kerIn (star M H M) ⊤ = ⊥ := E2P.kerIn_star M H
  set E := tiClosure M V with hEdef
  have hEel := h.isElemAbelian_tiClosure hTI
  have hEO := h.tiClosure_le_pCoreOf
  have hET : E ≤ T := hEO.trans h.pCoreOf_M_le_T
  have hE28 : Hyp28 H T M E := ⟨h.minParabolic, h.sqtk, hET,
    fun t ht => le_normalizer_tiClosure (h.minParabolic.le ht), hEel, hEO,
    fun hle => h.not_le_kerIn (le_tiClosure.trans hle)⟩
  have hEY28 := hE28.star hsq
  have hY28 := h.star hsq
  have hEsel := isElemAbelian_star (M := M) (H := H) hEel
  have hEsN : star M H M ≤ Subgroup.normalizer (star M H E : Set (StarQuot M H)) := by
    rintro _ ⟨⟨m, hmH⟩, hm, rfl⟩
    exact starMap_mem_normalizer hmH (le_normalizer_tiClosure (Subgroup.mem_subgroupOf.1 hm))
  have hEs1 : star M H E ≠ ⊥ := fun hb =>
    hY28.ne_bot (le_bot_iff.mp (hb ▸ star_mono (le_tiClosure : V ≤ E)))
  have hKN : (⊤ : Subgroup (StarQuot M H)) ≤ Subgroup.normalizer (K : Set (StarQuot M H)) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hKn : K.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hKN)
  have hLT : K ⊔ star M H T = ⊤ := hHK.symm
  have eK := equivStarOfKerInEqBot hJY hKH
  have hty' : IsPSL 3 2 n ↥K ∨ IsSp4Prime n ↥K :=
    hty.imp (isPSL_of_mulEquiv_gen eK) (fun hs => isSp4Prime_of_mulEquiv eK hs)
  have hs : IsSimpleGroup ↥K := by
    rcases hty' with hP | hP
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 n hP).2
    · exact isSimpleGroup_of_isSp4Prime hP
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    haveI : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
    haveI : Nontrivial ↥K := hs.toNontrivial
    haveI hsol : Group.IsSolvable ↥K := Group.isSolvable_of_comm fun a b => hab a b
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  have hcent := centralizer_eq_bot_of_simple hmpY hJY hKn hs hnab hLT
  have hMK := inf_eq_of_isBorelIn_star hmpY hJY (subnormal_of_mem_cComp hKc) hKH hBor
  rcases hty' with hP | hP
  ·
    obtain ⟨hEK, hcard, hdich⟩ := hL3 _ (star M H T) (star M H M) K (star M H E) n hn2
      hmpY.isSylow hLT
      (fun a ha => by
        have : a ∈ Subgroup.centralizer (K : Set (StarQuot M H)) :=
          Subgroup.mem_centralizer_iff.mpr fun x hx => (ha x hx).symm
        rw [hcent] at this
        exact this)
      hP (diag_of_star_top hJY hD) hMK hmpY.le (star_mono hET)
      (fun x hx => by rw [← pow_two]; exact hEsel.2 x hx)
      (hmpY.le.trans hEsN) hEsN hEs1
    exact le_nParam_of_starDich h hTI hKn le_rfl hEK hcard hdich
  ·
    obtain ⟨R₀, hR₀E, hR₀K, hcard, hdich⟩ := hSp4 _ (star M H T) (star M H M) K (star M H E) n
      hn2 hEY28 hJY hcent hLT hP hMK hEsN
    exact le_nParam_of_starDich h hTI hKn hR₀E hR₀K hcard hdich

end TI2b

end E2

end CFSG.Quasithin
