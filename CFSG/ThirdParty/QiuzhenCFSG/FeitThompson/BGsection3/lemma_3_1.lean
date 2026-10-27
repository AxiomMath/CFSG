module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

namespace CFSG
end CFSG
open CFSG

public theorem CFSG.lemma_3_1 {G : Type*} [Group G] [Finite G] (K R : Subgroup G)
    (hK_ne : K ≠ ⊥) (hR_ne : R ≠ ⊥) (hK_normal : K.Normal) (hKR : K.IsComplement' R) :
    IsFrobeniusGroupWithKernelComplement K R ↔
      ∀ x : R, x ≠ 1 → elementCentralizerIn K (x : G) = ⊥ := by
  let _ := (inferInstance : Finite G)
  let _ := hK_ne
  let _ := hR_ne
  constructor
  · intro hfrob x hx_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rcases hy with ⟨hyK, hyC⟩
    by_contra hy_ne
    have hy_not_mem_R : y ∉ R := by
      intro hyR
      exact hy_ne ((Subgroup.disjoint_def.mp hKR.disjoint) hyK hyR)
    have hy_comm : y * (x : G) = (x : G) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hx_conj : (x : G) ∈ R.conjBy y := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨(x : G), x.property, ?_⟩
      calc
        y * (x : G) * y⁻¹ = ((x : G) * y) * y⁻¹ := by rw [hy_comm]
        _ = (x : G) * (y * y⁻¹) := by rw [mul_assoc]
        _ = (x : G) := by simp
    exact hx_ne <|
      Subtype.ext <|
        (Subgroup.disjoint_def.mp (hfrob.disjoint_conjBy y hy_not_mem_R)) x.property hx_conj
  · intro hcent
    refine ⟨hK_normal, hKR, ?_, hK_ne, hR_ne⟩
    intro g hg_not_mem_R
    rw [Subgroup.disjoint_def]
    intro x hxR hxRg
    by_cases hx_eq_one : x = 1
    · exact hx_eq_one
    rcases hKR.2 g with ⟨⟨⟨k, hkK⟩, ⟨r, hrR⟩⟩, hgr⟩
    have hgr' : (k : G) * r = g := by
      simpa using hgr
    rw [Subgroup.conjBy, Subgroup.mem_map] at hxRg
    rcases hxRg with ⟨y, hyR, hyEq⟩
    let z : G := r * y * r⁻¹
    have hzR : z ∈ R := by
      dsimp [z]
      exact R.mul_mem (R.mul_mem hrR hyR) (R.inv_mem hrR)
    have hxEq : x = k * z * k⁻¹ := by
      calc
        x = g * y * g⁻¹ := by simpa [MulAut.conj_apply] using hyEq.symm
        _ = (k * r) * y * (k * r)⁻¹ := by rw [← hgr']
        _ = k * z * k⁻¹ := by
          dsimp [z]
          simp [mul_assoc]
    have hxzK : x * z⁻¹ ∈ K := by
      have hzkinvK : z * k⁻¹ * z⁻¹ ∈ K :=
        hK_normal.conj_mem (k⁻¹) (K.inv_mem hkK) z
      have hk_mul : k * (z * k⁻¹ * z⁻¹) ∈ K := K.mul_mem hkK hzkinvK
      simpa [hxEq, mul_assoc] using hk_mul
    have hxzR : x * z⁻¹ ∈ R := R.mul_mem hxR (R.inv_mem hzR)
    have hxz_eq_one : x * z⁻¹ = 1 := (Subgroup.disjoint_def.mp hKR.disjoint) hxzK hxzR
    have hx_eq_z : x = z := by
      simpa [mul_assoc] using congrArg (fun t : G => t * z) hxz_eq_one
    have hx_fix : x = k * x * k⁻¹ := by
      simpa [hx_eq_z] using hxEq
    have hk_comm : k * x = x * k := by
      have hx_mul_k : x * k = k * x := by
        simpa [mul_assoc] using congrArg (fun t : G => t * k) hx_fix
      exact hx_mul_k.symm
    have hk_cent : k ∈ elementCentralizerIn K x := by
      exact ⟨hkK, Subgroup.mem_centralizer_singleton_iff.mpr hk_comm⟩
    have hx_sub_ne_one : (⟨x, hxR⟩ : R) ≠ 1 := by
      intro hx_sub_eq_one
      exact hx_eq_one (congrArg Subtype.val hx_sub_eq_one)
    have hk_eq_one : k = 1 := by
      have hk_bot : k ∈ (⊥ : Subgroup G) := by
        rw [hcent ⟨x, hxR⟩ hx_sub_ne_one] at hk_cent
        simpa using hk_cent
      simpa using hk_bot
    have hg_mem_R : g ∈ R := by
      have hg_eq_r : g = r := by
        calc
          g = (k : G) * r := hgr'.symm
          _ = r := by simp [hk_eq_one]
      rw [hg_eq_r]
      exact hrR
    exact False.elim (hg_not_mem_R hg_mem_R)
