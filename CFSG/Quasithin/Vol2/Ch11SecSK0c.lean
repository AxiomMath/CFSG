module

public import CFSG.Quasithin.Vol2.Ch11SecSK0b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSolvable_of_le {A B : Subgroup G} (hAB : A ≤ B) (hB : Group.IsSolvable ↥B) :
    Group.IsSolvable ↥A :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAB)
    (Subgroup.inclusion_injective hAB)

theorem eq_of_subnormal_of_cSimple {Q : Type*} [Group Q] {P J : Subgroup Q}
    (hP : quasithinIsCComponent P P) (hJP : J ≤ P) (hJ : J ≠ ⊥) (hJp : ⁅J, J⁆ = J)
    (hJs : IsSubnormal J P) : J = P := by
  by_contra hne
  exact hP.2.2.2 J (lt_of_le_of_ne hJP hne) hJ hJp hJs

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem cComp_k0Of (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    k0Of K P₂ ∈ cComp (k0Of K P₂ ⊔ T) := by
  have hK0K := k0Of_le K P₂
  have hK0p := k0Of_perfect K P₂
  have hK0n : ((k0Of K P₂).subgroupOf (k0Of K P₂ ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (h.T_le_normalizer_k0Of hP))
  refine ⟨hP.k0Of_ne_bot, hK0p, IsSubnormal.step le_sup_left hK0n (IsSubnormal.refl _),
    fun J hJlt hJne hJp hJs => ?_⟩
  obtain ⟨J₀, hJ₀⟩ := (Set.toFinite {J' : Subgroup G | J' < k0Of K P₂ ∧ J' ≠ ⊥ ∧
      ⁅J', J'⁆ = J' ∧ IsSubnormal J' (k0Of K P₂ ⊔ T)}).exists_minimal ⟨J, hJlt, hJne, hJp, hJs⟩
  obtain ⟨hJ₀lt, hJ₀ne, hJ₀p, hJ₀s⟩ := hJ₀.prop
  have hJ₀c : J₀ ∈ cComp (k0Of K P₂ ⊔ T) := by
    refine ⟨hJ₀ne, hJ₀p, hJ₀s, fun J' hJ'lt hJ'ne hJ'p hJ's => ?_⟩
    exact hJ'lt.ne (hJ₀.eq_of_le ⟨hJ'lt.trans hJ₀lt, hJ'ne, hJ'p, hJ's⟩ hJ'lt.le)
  have hJ₀K : J₀ ≤ K := hJ₀lt.le.trans hK0K
  have hJ₀sub : IsSubnormal J₀ (k0Of K P₂) := A3.subnormal_of_le_of_le hJ₀s hJ₀lt.le le_sup_left
  have hbar : modO2Image K J₀ = P₂ := by
    rw [← modO2Image_k0Of K hP.c₂.2.1]
    refine eq_of_subnormal_of_cSimple ?_ (Subgroup.map_mono fun x hx => hJ₀lt.le hx)
      (modO2Image_ne_bot hJ₀K hJ₀p hJ₀ne) (modO2Image_perfect hJ₀K hJ₀p)
      (modO2Image_subnormal hJ₀sub)
    rw [modO2Image_k0Of K hP.c₂.2.1]
    exact hP.c₂
  have hsup := sup_eq_of_modO2Image_eq hJ₀K hK0K (hbar.trans (modO2Image_k0Of K hP.c₂.2.1).symm)
  have hJ₀Q : J₀ ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hJ₀K.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hK0eq : k0Of K P₂ = J₀ ⊔ (k0Of K P₂ ⊓ pCoreOf 2 K) :=
    A3.eq_sup_inf_of_le_sup hJ₀Q hJ₀lt.le (hsup ▸ le_sup_left)
  have hNs : Group.IsSolvable ↥(k0Of K P₂ ⊓ pCoreOf 2 K) :=
    isSolvable_of_le inf_le_right (isSolvable_pCoreOf_two K)
  have hJ₀N : J₀ ≤ Subgroup.normalizer ((k0Of K P₂ ⊓ pCoreOf 2 K : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hJ₀lt.le hx), hJ₀Q hx⟩
  have hcore := (cComp_commutator_perfectCore hJ₀c (inf_le_left.trans le_sup_left) hNs hJ₀N).2
  rw [← hK0eq, perfectCore_eq_self_of_perfect hK0p] at hcore
  exact hJ₀lt.ne hcore.symm

theorem isLocal_k0Of (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    quasithinIsLocal T (k0Of K P₂) := by
  refine ⟨h.sylow.1, h.cComp_k0Of hP,
    (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right).2.2, fun hbot => ?_⟩
  have hle : V₁ ≤ pCoreOf 2 (k0Of K P₂ ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.V₁_le_T.trans le_sup_right)
      (sup_le ((k0Of_le K P₂).trans h.K_le_normalizer_V₁) h.T_le_normalizer_V₁) h.isPGroup_V₁
  exact h.V₁_ne_bot (eq_bot_iff.mpr (hbot ▸ hle))

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
