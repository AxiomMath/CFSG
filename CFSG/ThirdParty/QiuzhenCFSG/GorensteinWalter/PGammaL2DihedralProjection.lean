module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalDihedralIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral Sylow constraints on subgroups of `PΓL₂`

For `|K| > 3`, the canonical PSL₂ layer is the derived subgroup of the
normal PGL₂ layer, hence is itself normal in `PΓL₂(K)`.  If a subgroup
`A ≤ PΓL₂(K)` contains this layer and has dihedral Sylow `2`-subgroups, the
canonical PSL₂ subgroup has index in `A` not divisible by four.

This is the source-independent first reduction toward proving that the field
automorphism image of `A` has odd order.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped MatrixGroups

universe u

/-- For `|K| > 3`, the canonical PSL₂ layer is normal in `PΓL₂(K)`. -/
public theorem pGammaL2PSLRange_normal
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    (pGammaL2PSLRange K).Normal := by
  let N : Subgroup (PGammaL2 K) := pGammaL2PGLRange K
  let C : Subgroup N := commutator N
  let L : Subgroup (PGammaL2 K) := C.map N.subtype
  let : C.Characteristic := by
    dsimp [C]
    infer_instance
  let : N.Normal := by
    exact pGammaL2PGLRange_normal K
  have hLnormal : L.Normal := by
    dsimp [L]
    exact ConjAct.normal_of_characteristic_of_normal
  have hL : L = pGammaL2PSLRange K := by
    let e : PGL2 K ≃* N := pGammaL2PGLRangeEquiv K
    let t : PSL2 K →* PGL2 K :=
      Matrix.ProjectiveSpecialLinearGroup.toPGL
    let i : PGL2 K →* PGammaL2 K := SemidirectProduct.inl
    have hcomm : commutator (PGL2 K) = t.range := by
      simpa [t] using
        pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
    have hmapComm :
        (commutator (PGL2 K)).map e.toMonoidHom = commutator N := by
      have heRange : e.toMonoidHom.range = ⊤ :=
        MonoidHom.range_eq_top.mpr e.surjective
      rw [map_commutator_eq, heRange]
      rfl
    change (commutator N).map N.subtype = pGammaL2PSLRange K
    rw [← hmapComm]
    rw [hcomm]
    rw [Subgroup.map_map]
    have hei : N.subtype.comp e.toMonoidHom = i := by
      apply MonoidHom.ext
      intro g
      exact pGammaL2PGLRangeEquiv_coe K g
    rw [hei]
    change t.range.map i = (i.comp t).range
    exact MonoidHom.map_range i t
  rw [← hL]
  exact hLnormal

/-- The canonical PSL₂ layer has dihedral Sylow `2`-subgroups. -/
public theorem pGammaL2PSLRange_hasDihedralSylowTwo
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    HasDihedralSylowTwo (pGammaL2PSLRange K) := by
  let : Finite (pGammaL2PSLRange K) :=
    Finite.of_surjective (pGammaL2PSLRangeEquiv K)
      (pGammaL2PSLRangeEquiv K).surjective
  exact hasDihedralSylowTwo_of_mulEquiv
    (pGammaL2PSLRangeEquiv K).symm
    (psl2_odd_hasDihedralSylowTwo_model K hK)

/-- If `A ≤ PΓL₂(K)` contains the canonical PSL₂ layer and has dihedral
Sylow `2`-subgroups, the index of that layer in `A` is not divisible by
four. -/
public theorem pGammaL2_psl_subgroupOf_index_not_dvd_four_of_dihedral
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hAd : HasDihedralSylowTwo A) :
    ¬ 4 ∣ ((pGammaL2PSLRange K).subgroupOf A).index := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fintype K := Fintype.ofFinite K
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let : Finite A := inferInstance
  let H : Subgroup A := (pGammaL2PSLRange K).subgroupOf A
  let : Finite H := inferInstance
  have hHnormal : H.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hPSL).2
    intro h a hh ha
    exact (pGammaL2PSLRange_normal K hK hcard).conj_mem h hh a
  let eH : H ≃* pGammaL2PSLRange K :=
    Subgroup.subgroupOfEquivOfLe hPSL
  have hHd : HasDihedralSylowTwo H := by
    let : Finite (pGammaL2PSLRange K) :=
      Finite.of_surjective (pGammaL2PSLRangeEquiv K)
        (pGammaL2PSLRangeEquiv K).surjective
    exact hasDihedralSylowTwo_of_mulEquiv eH
      (pGammaL2PSLRange_hasDihedralSylowTwo K hK)
  exact normal_subgroup_index_not_dvd_four_of_dihedral_sylow
    hAd H hHnormal hHd

/-- If the restricted field-automorphism image is even, then the
projective-linear kernel of a dihedral-Sylow subgroup containing the canonical
PSL₂ layer is exactly that PSL₂ layer.  Thus the remaining even-image case is
the pure semilinear extension of PSL₂, not an extension of PGL₂. -/
public theorem pGammaL2_even_field_projection_linearKernel_eq_psl
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hAd : HasDihedralSylowTwo A)
    (heven : 2 ∣ Nat.card (pGammaL2FieldProjection K A).range) :
    pGammaL2LinearKernel K A =
      (pGammaL2PSLRange K).subgroupOf A := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fintype K := Fintype.ofFinite K
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let : Finite A := inferInstance
  let H : Subgroup A := (pGammaL2PSLRange K).subgroupOf A
  let L : Subgroup A := pGammaL2LinearKernel K A
  let M : Subgroup (PGammaL2 K) := L.map A.subtype
  have hHL : H ≤ L := by
    intro x hx
    rw [mem_pGammaL2LinearKernel_iff]
    change SemidirectProduct.rightHom (x : PGammaL2 K) = 1
    have hxPSL : (x : PGammaL2 K) ∈ pGammaL2PSLRange K := hx
    rcases (mem_pGammaL2PSLRange_iff K (x : PGammaL2 K)).mp hxPSL with
      ⟨y, hy⟩
    rw [← hy]
    simp
  have hPSLM : pGammaL2PSLRange K ≤ M := by
    intro x hx
    have hxA : x ∈ A := hPSL hx
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    exact hHL hx
  have hMPGL : M ≤ pGammaL2PGLRange K := by
    rintro _x ⟨a, ha, rfl⟩
    change (a : PGammaL2 K) ∈ pGammaL2PGLRange K
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
    change SemidirectProduct.rightHom (a : PGammaL2 K) = 1
    exact (mem_pGammaL2LinearKernel_iff K A a).mp ha
  have hHmap : H.map A.subtype = pGammaL2PSLRange K := by
    simpa [H] using
      (Subgroup.map_subgroupOf_eq_of_le hPSL)
  have hrelMap : H.relIndex L =
      (pGammaL2PSLRange K).relIndex M := by
    rw [← hHmap]
    exact (Subgroup.relIndex_map_map_of_injective H L
      A.subtype_injective).symm
  have hrelPGL :
      (pGammaL2PSLRange K).relIndex (pGammaL2PGLRange K) = 2 :=
    pGammaL2_psl_range_relIndex_pgl_eq_two K hK
  have hrelMul := Subgroup.relIndex_mul_relIndex
    (pGammaL2PSLRange K) M (pGammaL2PGLRange K) hPSLM hMPGL
  rw [hrelPGL] at hrelMul
  have hrelDvd : H.relIndex L ∣ 2 := by
    refine ⟨M.relIndex (pGammaL2PGLRange K), ?_⟩
    rw [hrelMap]
    exact hrelMul.symm
  have hLindex : L.index =
      Nat.card (pGammaL2FieldProjection K A).range := by
    exact pGammaL2LinearKernel_index_eq_card_range K A
  have hLeven : 2 ∣ L.index := by
    rwa [hLindex]
  have hnotFour : ¬ 4 ∣ H.index := by
    exact pGammaL2_psl_subgroupOf_index_not_dvd_four_of_dihedral
      K hK hcard A hPSL hAd
  have hrelOne : H.relIndex L = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hrelDvd with hrel | hrel
    · exact hrel
    · exfalso
      apply hnotFour
      rcases hLeven with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hmul := Subgroup.relIndex_mul_index hHL
      rw [hrel, hn] at hmul
      omega
  apply le_antisymm
  · exact Subgroup.relIndex_eq_one.mp hrelOne
  · exact hHL

/-- For a faithful embedding of a group with dihedral Sylow `2`-subgroups
into `PΓL₂(K)` whose range contains the canonical PSL₂ layer, either the
field image is odd or the linear kernel is exactly PSL₂. -/
public theorem pGammaL2_embedding_field_projection_odd_or_linearKernel_eq_psl
    {R : Type u} [Group R] [Finite R]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (hSylow : HasDihedralSylowTwo R)
    (f : R →* PGammaL2 K) (hf : Function.Injective f)
    (hPSL : pGammaL2PSLRange K ≤ f.range) :
    Odd (Nat.card (pGammaL2FieldProjection K f.range).range) ∨
      pGammaL2LinearKernel K f.range =
        (pGammaL2PSLRange K).subgroupOf f.range := by
  let eR : R ≃* f.range :=
    MulEquiv.ofBijective f.rangeRestrict
      ⟨fun a b hab => hf (congrArg Subtype.val hab),
        f.rangeRestrict_surjective⟩
  let : Finite f.range := Finite.of_surjective eR eR.surjective
  have hRange : HasDihedralSylowTwo f.range :=
    hasDihedralSylowTwo_of_mulEquiv eR.symm hSylow
  rcases Nat.even_or_odd
      (Nat.card (pGammaL2FieldProjection K f.range).range) with
    heven | hodd
  · right
    exact pGammaL2_even_field_projection_linearKernel_eq_psl
      K hK hcard f.range hPSL hRange heven.two_dvd
  · exact Or.inl hodd

end CFSG.GorensteinWalter
