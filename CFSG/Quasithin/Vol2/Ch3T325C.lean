module

public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Vol2.Ch3T325A

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem autOn_eq_of_factor {M N V : Subgroup G} (hNM : N ≤ M)
    (hMn : M ≤ Subgroup.normalizer (V : Set G))
    (hfac : ∀ m ∈ M, ∃ n ∈ N, ∃ c ∈ M ⊓ Subgroup.centralizer (V : Set G), m = n * c) :
    autOn M V = autOn N V := by
  apply le_antisymm
  · rintro φ ⟨g, hg, rfl⟩
    obtain ⟨n, hn, c, hc, hm⟩ := hfac (g : G) (Subgroup.mem_subgroupOf.mp hg)
    have hnn : n ∈ Subgroup.normalizer (V : Set G) := hMn (hNM hn)
    have hcn : c ∈ Subgroup.normalizer (V : Set G) := hMn hc.1
    have hg' : g = ⟨n, hnn⟩ * ⟨c, hcn⟩ := Subtype.ext hm
    rw [hg', map_mul, InternalSec.conjAct_eq_one_of_mem_centralizer
      (⟨c, hcn⟩ : ↥(Subgroup.normalizer (V : Set G))) hc.2, mul_one]
    exact Subgroup.mem_map.mpr ⟨⟨n, hnn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hNM)

namespace Ctx

variable [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem T_le_M₀ : T ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :
        Subgroup G) : Set G) :=
  le_inf c.T_le_M (le_normalizer_inf_centralizer' Subgroup.le_normalizer
    (c.T_le_M.trans (M_le_NVM T L V₀)))

theorem autOn_M₀ : autOn (Subgroup.normalizer (L : Set G))
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) =
    autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :
          Subgroup G) : Set G))
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) := by
  set M := Subgroup.normalizer (L : Set G) with hM
  set VM := conjClosure (conjClosure V₀ T) M with hVM
  set C := M ⊓ Subgroup.centralizer (VM : Set G) with hC
  have hCM : C ≤ M := inf_le_left
  have hMC : M ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf_centralizer' Subgroup.le_normalizer (M_le_NVM T L V₀)
  have hsyl : IsSylowTwoOf (T ⊓ C) C := B6.isSylowTwoOf_inf_normal c.sylowM hCM hMC
  have hTC : T ⊓ C = T ⊓ Subgroup.centralizer (VM : Set G) := by
    rw [hC, ← inf_assoc, inf_eq_left.mpr c.T_le_M]
  rw [hTC] at hsyl
  have hfac := exists_mul_of_sylow hCM hMC hsyl.1 hsyl.2.1 hsyl.2.2
  refine autOn_eq_of_factor inf_le_left (M_le_NVM T L V₀) fun m hm => ?_
  obtain ⟨n, hn, c', hc', rfl⟩ := hfac m hm
  exact ⟨n, hn, c', hc', rfl⟩

theorem VM_le_M₀ : conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) ≤
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :
          Subgroup G) : Set G) := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) with hVM
  have hVT : VM ≤ T := (A4.le_pCoreOf_of_isTwoReducedIn c.redVM).trans
    (pCoreOf_two_le_of_isSylowTwoOf c.sylowM)
  have : IsMulCommutative ↥VM := c.elemVM.1
  have hVC : VM ≤ Subgroup.centralizer (VM : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      setLike_mul_comm (s := VM) hw hv
  refine le_inf c.VM_le_M ((le_inf hVT hVC).trans Subgroup.le_normalizer)

theorem red₀ : IsTwoReducedIn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :
          Subgroup G) : Set G))
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) := by
  refine A4.isTwoReducedIn_of_pCoreOf_autOn_eq_bot c.VM_le_M₀
    (inf_le_left.trans (M_le_NVM T L V₀)) c.elemVM ?_
  rw [← c.autOn_M₀]
  exact Setup.pCoreOf_autOn_eq_bot c.redVM

theorem pCoreOf_M₀ : pCoreOf 2 (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :
          Subgroup G) : Set G)) =
    T ⊓ Subgroup.centralizer
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) := by
  refine le_antisymm (le_inf (pCoreOf_two_le_of_isSylowTwoOf
    (isSylowTwoOf_of_le c.fsu.sylow c.T_le_M₀))
    (A4.pCoreOf_le_centralizer_of_isTwoReducedIn c.red₀)) ?_
  exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans c.T_le_M₀) inf_le_right
    (c.fsu.sylow.1.to_le inf_le_left)

theorem sup_le_normalizer_R : L ⊔ T ≤ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :
        Subgroup G) : Set G) := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) with hVM
  have hR : T ⊓ Subgroup.centralizer (VM : Set G) =
      pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer (VM : Set G) := by
    rw [c.o2, inf_assoc, inf_eq_right.mpr (Subgroup.centralizer_le (V_le_VM T L V₀))]
  rw [hR]
  have hLTM : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer c.T_le_M
  exact le_normalizer_inf_centralizer' (le_normalizer_pCoreOf 2 _)
    (hLTM.trans (M_le_NVM T L V₀))

theorem isUniqueM_M₀ : IsUniqueM (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :
          Subgroup G) : Set G))
    (Subgroup.normalizer (L : Set G)) := by
  set M := Subgroup.normalizer (L : Set G) with hM
  set R := T ⊓ Subgroup.centralizer (conjClosure (conjClosure V₀ T) M : Set G) with hRdef
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
    have hKM : K = M := c.uniq.2 K ⟨hK, c.sup_le_normalizer_R.trans hNK⟩
    have hLTM₀ : L ⊔ T ≤ M ⊓ Subgroup.normalizer (R : Set G) :=
      le_inf (sup_le Subgroup.le_normalizer c.T_le_M) c.sup_le_normalizer_R
    exact c.uniq.2 M' ⟨hM'.1, hLTM₀.trans hM'.2⟩

theorem hyp315 {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    Hyp315 T (Subgroup.normalizer (L : Set G)) (Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :
          Subgroup G) : Set G)) H
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) :=
  { toHyp315Base := ⟨c.T_le_M₀, inf_le_left, hH, c.red₀, c.pCoreOf_M₀⟩
    «case» := Or.inr (inf_le_right.trans (M_le_NVM T L V₀)) }

end Ctx

end CFSG.Quasithin.H13.T325
