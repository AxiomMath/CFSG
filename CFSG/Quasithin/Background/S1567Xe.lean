module

public import CFSG.Quasithin.Background.S1567Cm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section Xe

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem normalizer_eq_sup (k : Ctx67 G T Mc M V₁ V₂ E t) :
    Subgroup.normalizer (E : Set G) =
      (M ⊓ Subgroup.normalizer (E : Set G)) ⊔ Subgroup.centralizer (E : Set G) := by
  apply le_antisymm
  · calc Subgroup.normalizer (E : Set G)
        = (YE153 Mc M E ⊔ TE153 T E) ⊔ Subgroup.centralizer (E : Set G) := k.r66.GE_eq
      _ ≤ (M ⊓ Subgroup.normalizer (E : Set G)) ⊔ Subgroup.centralizer (E : Set G) :=
        sup_le_sup_right (YE_TE_le_ME k.c) _
  · exact sup_le inf_le_right (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
theorem normalizer_le_normalizer_CE (E : Subgroup G) :
    Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (E : Set G) : Set G) :=
  B2F.le_normalizer_centralizer le_rfl

theorem isSylowTwoOf_SE (k : Ctx67 G T Mc M V₁ V₂ E t) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer (E : Set G)) (Subgroup.centralizer (E : Set G)) := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have h := A4.isSylowTwoOf_inf_normal k.r2.sylow_GE hCN (normalizer_le_normalizer_CE E)
  have e : TE153 T E ⊓ Subgroup.centralizer (E : Set G) = T ⊓ Subgroup.centralizer (E : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨⟨a, _⟩, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨⟨a, hCN c⟩, c⟩⟩
  rwa [e] at h

theorem not_three_dvd_card_M_inf_CE (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ¬ 3 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E : Set G)) := by
  intro hd
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ Subgroup.centralizer (E : Set G))) 3 hd
  have hxM : (x : G) ∈ M := x.2.1
  have hxC : (x : G) ∈ Subgroup.centralizer (E : Set G) := x.2.2
  have hord : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hY : (x : G) ∈ Y153 Mc M := by
    rw [k.r49.eq_oPrime]
    exact Subgroup.subset_closure ⟨hxM, 1, by rw [hord]; norm_num⟩
  have hZ : (x : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le k.r66.Z_le_E hxC
  have hP : (x : G) ∈ pCoreOf 2 (Y153 Mc M) := by
    rw [k.r49.pCore_eq_centralizer_Z]
    exact ⟨hY, hZ⟩
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 (Y153 Mc M) ⟨(x : G), hP⟩
  have hj' : (x : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hdvd : 3 ∣ 2 ^ j := hord ▸ orderOf_dvd_of_pow_eq_one hj'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem M_inf_CE_eq (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    M ⊓ Subgroup.centralizer (E : Set G) = T ⊓ Subgroup.centralizer (E : Set G) := by
  have hsyl := isSylowTwoOf_SE k
  have hle : T ⊓ Subgroup.centralizer (E : Set G) ≤ M ⊓ Subgroup.centralizer (E : Set G) :=
    inf_le_inf_right _ k.c.hyp.T_le
  have h23 : C1Pack153.TwoThree (M ⊓ Subgroup.centralizer (E : Set G)) :=
    (twoThree_M k hidx).mono inf_le_left
  have hp2 : IsPGroup 2 ↥(M ⊓ Subgroup.centralizer (E : Set G)) :=
    isPGroup_two_of_twoThree h23 (not_three_dvd_card_M_inf_CE k)
  have := (A4.isSylowTwoOf_iff_maximal.mp hsyl).2.2 (M ⊓ Subgroup.centralizer (E : Set G))
    inf_le_right hp2 hle
  exact le_antisymm this hle

theorem relIndex_SE_CE (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    (T ⊓ Subgroup.centralizer (E : Set G)).relIndex (Subgroup.centralizer (E : Set G)) = 3 := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have e1 : (M ⊓ Subgroup.normalizer (E : Set G)) ⊓ Subgroup.centralizer (E : Set G) =
      M ⊓ Subgroup.centralizer (E : Set G) := by
    rw [inf_assoc, inf_eq_right.mpr hCN]
  have e2 : (T ⊓ Subgroup.centralizer (E : Set G)).relIndex (Subgroup.centralizer (E : Set G)) =
      ((M ⊓ Subgroup.normalizer (E : Set G)) ⊓ Subgroup.centralizer (E : Set G)).relIndex
        (Subgroup.centralizer (E : Set G)) := by
    rw [e1, M_inf_CE_eq k hidx]
  rw [e2, relIndex_inf_eq_relIndex_sup (inf_le_right.trans (normalizer_le_normalizer_CE E)),
    ← normalizer_eq_sup k]
  exact hidx

theorem CE_eq_XE_sup_SE (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    XE153 E ⊔ (T ⊓ Subgroup.centralizer (E : Set G)) = Subgroup.centralizer (E : Set G) :=
  sup_eq_of_relIndex_two_pow_of_odd (oTwoUpper_le _) inf_le_right
    (relIndex_oTwoUpper_eq_two_pow _) (by rw [relIndex_SE_CE k hidx]; decide)

omit [Finite G] in
theorem XE_normal_153 (E : Subgroup G) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (XE153 E : Set G) :=
  (normalizer_le_normalizer_CE E).trans (normalizer_le_normalizer_oTwoUpper _)

theorem GE_eq_153 (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    Subgroup.normalizer (E : Set G) = (YE153 Mc M E ⊔ XE153 E) ⊔ TE153 T E := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hYE : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hSE : T ⊓ Subgroup.centralizer (E : Set G) ≤ TE153 T E := inf_le_inf_left T hCN
  apply le_antisymm
  · rw [k.r66.GE_eq, ← CE_eq_XE_sup_SE k hidx]
    refine sup_le (sup_le ((le_sup_left : YE153 Mc M E ≤ _).trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) (hSE.trans le_sup_right))
  · exact sup_le (sup_le hYE ((oTwoUpper_le _).trans hCN)) inf_le_right

theorem XE_not_le_153 (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    ¬ XE153 E ≤ M := by
  intro hXM
  have hCM : Subgroup.centralizer (E : Set G) ≤ M := by
    rw [← CE_eq_XE_sup_SE k hidx]
    exact sup_le hXM (inf_le_left.trans k.c.hyp.T_le)
  apply k.L.not_le_M
  rw [normalizer_eq_sup k]
  exact sup_le inf_le_left hCM

omit [Finite G] in
theorem SE_le_normalizer_XE (E : Subgroup G) :
    T ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (XE153 E : Set G) :=
  inf_le_right.trans (le_normalizer_oTwoUpper _)

theorem isSylowTwoOf_SE_inf_XE (k : Ctx67 G T Mc M V₁ V₂ E t) :
    IsSylowTwoOf ((T ⊓ Subgroup.centralizer (E : Set G)) ⊓ XE153 E) (XE153 E) :=
  A4.isSylowTwoOf_inf_normal (isSylowTwoOf_SE k) (oTwoUpper_le _) (le_normalizer_oTwoUpper _)

theorem relIndex_SE_inf_XE (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    ((T ⊓ Subgroup.centralizer (E : Set G)) ⊓ XE153 E).relIndex (XE153 E) = 3 := by
  rw [relIndex_inf_eq_relIndex_sup (SE_le_normalizer_XE E), sup_comm,
    CE_eq_XE_sup_SE k hidx]
  exact relIndex_SE_CE k hidx

theorem XE_quot_153 (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    Nonempty (OTwoQuot (XE153 E) ≃* Multiplicative (ZMod 3)) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl := isSylowTwoOf_SE_inf_XE k
  have hidx3 := relIndex_SE_inf_XE k hidx
  by_cases hN : XE153 E ≤ Subgroup.normalizer
      (((T ⊓ Subgroup.centralizer (E : Set G)) ⊓ XE153 E : Subgroup G) : Set G)
  · have hP : pCoreOf 2 (XE153 E) = (T ⊓ Subgroup.centralizer (E : Set G)) ⊓ XE153 E := by
      apply le_antisymm
      · exact A4.le_of_normal_of_isSylowTwoOf hsyl (pCoreOf_le 2 _)
          ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
            (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
      · exact le_pCoreOf_of_le_normalizer 2 inf_le_right hN hsyl.2.1
    have hcard : Nat.card (OTwoQuot (XE153 E)) = 3 := by
      rw [← C1Pack153.relIndex_pCoreOf_eq_card_quot, hP]
      exact hidx3
    refine ⟨mulEquivOfPrimeCardEq (p := 3) hcard ?_⟩
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  · exfalso
    exact not_nonempty_oTwoQuot_equiv_perm_three (oTwoUpper_oTwoUpper _).symm
      (nonempty_quotient_pCore_of_relIndex_eq_three' hsyl hidx3 hN)

end Xe

end S1567

end CFSG.Quasithin
