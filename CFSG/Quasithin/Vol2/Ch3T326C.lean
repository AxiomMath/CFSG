module

public import CFSG.Quasithin.Vol2.Ch3T325C
public import CFSG.Quasithin.Vol2.Ch3T326A

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open T325 (V₀_le_V V_le_VM M_le_NVM isSylowTwoOf_of_le autOn_eq_of_factor)

variable {G : Type} [Group G]

namespace Ctx

variable [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem T_le_M₀ : T ≤ Subgroup.normalizer (conjClosure L T : Set G) ⊓ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) : Subgroup G) : Set G) :=
  le_inf c.T_le_M (le_normalizer_inf_centralizer' Subgroup.le_normalizer
    (c.T_le_M.trans (M_le_NVM T (conjClosure L T) V₀)))

theorem autOn_M₀ : autOn (Subgroup.normalizer (conjClosure L T : Set G))
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) =
    autOn (Subgroup.normalizer (conjClosure L T : Set G) ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) : Subgroup G) : Set G))
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) := by
  set M := Subgroup.normalizer (conjClosure L T : Set G) with hM
  set VM := conjClosure (conjClosure V₀ T) M with hVM
  set C := M ⊓ Subgroup.centralizer (VM : Set G) with hC
  have hCM : C ≤ M := inf_le_left
  have hMC : M ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf_centralizer' Subgroup.le_normalizer (M_le_NVM T (conjClosure L T) V₀)
  have hsyl : IsSylowTwoOf (T ⊓ C) C := B6.isSylowTwoOf_inf_normal c.sylowM hCM hMC
  have hTC : T ⊓ C = T ⊓ Subgroup.centralizer (VM : Set G) := by
    rw [hC, ← inf_assoc, inf_eq_left.mpr c.T_le_M]
  rw [hTC] at hsyl
  have hfac := exists_mul_of_sylow hCM hMC hsyl.1 hsyl.2.1 hsyl.2.2
  refine autOn_eq_of_factor inf_le_left (M_le_NVM T (conjClosure L T) V₀) fun m hm => ?_
  obtain ⟨n, hn, c', hc', rfl⟩ := hfac m hm
  exact ⟨n, hn, c', hc', rfl⟩

theorem VM_le_M₀ :
    conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ≤
      Subgroup.normalizer (conjClosure L T : Set G) ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) : Subgroup G) : Set G) := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  have hVT : VM ≤ T := (A4.le_pCoreOf_of_isTwoReducedIn c.redVM).trans
    (pCoreOf_two_le_of_isSylowTwoOf c.sylowM)
  have : IsMulCommutative ↥VM := c.elemVM.1
  have hVC : VM ≤ Subgroup.centralizer (VM : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      setLike_mul_comm (s := VM) hw hv
  refine le_inf c.VM_le_M ((le_inf hVT hVC).trans Subgroup.le_normalizer)

theorem red₀ : IsTwoReducedIn (Subgroup.normalizer (conjClosure L T : Set G) ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) : Subgroup G) : Set G))
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) := by
  refine A4.isTwoReducedIn_of_pCoreOf_autOn_eq_bot c.VM_le_M₀
    (inf_le_left.trans (M_le_NVM T (conjClosure L T) V₀)) c.elemVM ?_
  rw [← c.autOn_M₀]
  exact Setup.pCoreOf_autOn_eq_bot c.redVM

theorem pCoreOf_M₀ : pCoreOf 2 (Subgroup.normalizer (conjClosure L T : Set G) ⊓
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) : Subgroup G) : Set G)) =
    T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) := by
  refine le_antisymm (le_inf (pCoreOf_two_le_of_isSylowTwoOf
    (isSylowTwoOf_of_le c.fsu.sylow c.T_le_M₀))
    (A4.pCoreOf_le_centralizer_of_isTwoReducedIn c.red₀)) ?_
  exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans c.T_le_M₀) inf_le_right
    (c.fsu.sylow.1.to_le inf_le_left)

theorem sup_le_normalizer_R : conjClosure L T ⊔ T ≤ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) : Subgroup G) : Set G) := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  have hR : T ⊓ Subgroup.centralizer (VM : Set G) =
      pCoreOf 2 (conjClosure L T ⊔ T) ⊓ Subgroup.centralizer (VM : Set G) := by
    rw [c.o2, inf_assoc,
      inf_eq_right.mpr (Subgroup.centralizer_le (V_le_VM T (conjClosure L T) V₀))]
  rw [hR]
  exact le_normalizer_inf_centralizer' (le_normalizer_pCoreOf 2 _)
    (c.sup_le_M.trans (M_le_NVM T (conjClosure L T) V₀))

theorem isUniqueM_M₀ : IsUniqueM (Subgroup.normalizer (conjClosure L T : Set G) ⊓
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) : Subgroup G) : Set G))
    (Subgroup.normalizer (conjClosure L T : Set G)) := by
  set M := Subgroup.normalizer (conjClosure L T : Set G) with hM
  set R := T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T) M : Set G) with hRdef
  have hLTR : L ⊔ T ≤ Subgroup.normalizer (R : Set G) := by
    rw [← sup_eq T L]
    exact c.sup_le_normalizer_R
  refine ⟨⟨c.maxM, inf_le_left⟩, fun M' hM' => ?_⟩
  by_cases hR : R = ⊥
  · have hMM₀ : M ≤ M ⊓ Subgroup.normalizer (R : Set G) := by
      refine le_inf le_rfl fun m _ => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hR, Subgroup.mem_bot, Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro h
        have := congrArg (fun y => m⁻¹ * y * m) h
        simpa [mul_assoc] using this
    exact c.maxM.2 M' hM'.1.1 (hMM₀.trans hM'.2)
  · have hR2 : IsPGroup 2 R := c.fsu.sylow.1.to_le inf_le_left
    obtain ⟨K, hK, hNK⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (R : Set G))
      ⟨R, hR, hR2, rfl⟩
    have hKM : K = M := c.uniq.2 K ⟨hK, hLTR.trans hNK⟩
    have hLTM₀ : L ⊔ T ≤ M ⊓ Subgroup.normalizer (R : Set G) :=
      le_inf (sup_le (c.L_le_L₀.trans Subgroup.le_normalizer) c.T_le_M) hLTR
    exact c.uniq.2 M' ⟨hM'.1, hLTM₀.trans hM'.2⟩

theorem hyp315 {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H) :
    Hyp315 T (Subgroup.normalizer (conjClosure L T : Set G))
      (Subgroup.normalizer (conjClosure L T : Set G) ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) : Subgroup G) : Set G)) H
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :=
  { toHyp315Base := ⟨c.T_le_M₀, inf_le_left, hH, c.red₀, c.pCoreOf_M₀⟩
    «case» := Or.inr (inf_le_right.trans (M_le_NVM T (conjClosure L T) V₀)) }

end Ctx

end CFSG.Quasithin.H13.T326
