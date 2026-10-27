module

public import CFSG.Quasithin.H13.NQS13410W

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

@[expose] def Stmt13_2_2_9L1Perm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → IsHatA6 L →
      V ⊓ centralizer (L : Set G) ≠ ⊥ →
        normalizer (L₁Of L (fsuV1 T V) : Set G) ≤ normalizer (L : Set G)

@[expose] def Stmt13_2_2_9L1Nat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → IsHatA6 L →
      V ⊓ centralizer (L : Set G) = ⊥ →
        normalizer (L₁Of L (fsuV1 T V) : Set G) ≤ normalizer (L : Set G)

theorem stmt13_2_2_9L1_of_cases (hN : Stmt13_2_2_9L1Nat) (hP : Stmt13_2_2_9L1Perm) :
    Stmt13_2_2_9L1 := by
  intro G _ _ T L V hH hV hA6 hhat
  by_cases hZV : V ⊓ centralizer (L : Set G) = ⊥
  · exact hN G T L V hH hV hA6 hhat hZV
  · exact hP G T L V hH hV hA6 hhat hZV

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_normalizer_of_isSylowTwoOf {C R : Subgroup G} (hR : IsSylowTwoOf R C) {n : G}
    (hn : n ∈ normalizer (C : Set G)) :
    ∃ c ∈ C, ∃ m ∈ normalizer (R : Set G), n = c * m := by
  have hmapC : C.map (MulAut.conj n).toMonoidHom = C := by
    ext x
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hn y).mp hy
    · intro hx
      refine ⟨n⁻¹ * x * n, ?_, by group⟩
      have := (mem_normalizer_iff.mp (inv_mem hn) x).mp hx
      simpa using this
  have hS' : IsSylowTwoOf (R.map (MulAut.conj n).toMonoidHom) C := by
    have := IsSylowTwoOf.map_equiv (MulAut.conj n) hR
    rw [show C.map (MulAut.conj n).toMonoidHom = C from hmapC] at this
    exact this
  obtain ⟨h, hhC, hh⟩ := A4.exists_conj_of_isSylowTwoOf hR hS'
  refine ⟨h, hhC, h⁻¹ * n, ?_, by group⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := (hh (n * x * n⁻¹)).mp ⟨x, hx, rfl⟩
    have e : h⁻¹ * (n * x * n⁻¹) * h = (h⁻¹ * n) * x * (h⁻¹ * n)⁻¹ := by group
    rwa [e] at h1
  · intro hx
    have h1 : n * x * n⁻¹ ∈ R.map (MulAut.conj n).toMonoidHom := by
      rw [hh]
      have e : h⁻¹ * (n * x * n⁻¹) * h = (h⁻¹ * n) * x * (h⁻¹ * n)⁻¹ := by group
      rw [e]
      exact hx
    obtain ⟨y, hy, hyx⟩ := mem_map.mp h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have hyx' : y = x := by simpa using hyx
    exact hyx' ▸ hy

theorem mem_normalizer_l0_of_mem_centralizerSection {L X : Subgroup G} (hL0X : l0 L ≤ X)
    (hXL : X ≤ L) {n : G}
    (hn : n ∈ centralizerSection (normalizer (X : Set G)) X (pCoreOf 2 X)) :
    n ∈ normalizer (l0 L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnX : n ∈ normalizer (X : Set G) := hn.2.1
  have hcomm : ∀ x ∈ X, x * n * x⁻¹ * n⁻¹ ∈ pCoreOf 2 X :=
    ((mem_centralizerSection_iff_of_le (LieType.BorelTits.pCoreOf_le 2 X)).mp hn).2
  set W := l0 L ⊔ pCoreOf 2 X with hW
  have hnW : n ∈ normalizer (W : Set G) := by
    refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
    have hmap : W.map (MulAut.conj n).toMonoidHom ≤ W := by
      rw [hW, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        have h1 := hcomm a (hL0X ha)
        have e : (MulAut.conj n).toMonoidHom a = (a * n * a⁻¹ * n⁻¹)⁻¹ * a := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact W.mul_mem (W.inv_mem (mem_sup_right h1)) (mem_sup_left ha)
      · rintro _ ⟨b, hb, rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp
          (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hnX) b).mp hb)
    have := hmap (Subgroup.mem_map_of_mem _ hw)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
  have hO2L : pCoreOf 2 X ≤ normalizer (l0 L : Set G) :=
    (LieType.BorelTits.pCoreOf_le 2 X).trans (hXL.trans L_le_normalizer_l0)
  have hWeq : oTwoRes W = l0 L := by
    refine le_antisymm (oTwoRes_le_of_le_sup le_rfl
      (LieType.BorelTits.pCoreOf_isPGroup 2 X) hO2L) ?_
    exact (oTwoRes_le_oTwoRes (o2Z L)).trans (A6.oTwoRes_mono le_sup_left)
  have h1 : Subgroup.zpowers n ≤ normalizer (oTwoRes W : Set G) :=
    A5.le_normalizer_oTwoRes_of_le_normalizer (zpowers_le.mpr hnW)
  rw [hWeq] at h1
  exact h1 (mem_zpowers n)

theorem stmt13_2_2_9L1_of_setting134 {T L V : Subgroup G}
    (S : A6.Setting134 G T L V) (hhat : IsHatA6 L) :
    normalizer (L₁Of L (fsuV1 T V) : Set G) ≤ normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hR
  set N := normalizer (L₁ : Set G) with hN
  set C := centralizerSection N L₁ (pCoreOf 2 L₁) with hC
  have hTL : T ≤ normalizer (L : Set G) := S.T_le_NL
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hTN : T ≤ N := A5.le_normalizer_oTwoRes_of_le_normalizer fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hTL ht, Subgroup.le_normalizer (T_le_normalizer_fsuV1 T V ht)⟩
  have hNR : normalizer (R : Set G) ≤ normalizer (L : Set G) := by
    by_contra hK
    exact NQS134.false_of_thompsonJ_le S hhat hK (iSup₂_le fun A hA => hA.1) le_rfl le_rfl
  have hX : L₁ = oTwoUpper L₁ := by
    have h1 : L₁ ≤ oTwoRes L₁ := oTwoRes_le_oTwoRes _
    rw [oTwoRes_eq_oTwoUpper] at h1
    exact le_antisymm h1 (oTwoUpper_le _)
  have hsub : IsSubnormal L₁ N :=
    A4.subnormal_of_normal Subgroup.le_normalizer (normal_subgroupOf_of_le_normalizer le_rfl)
  have hTsyl : IsSylowTwoOf T (N ⊓ normalizer (L₁ : Set G)) := by
    rw [inf_idem]
    exact A5.isSylowTwoOf_of_le S.h13.sylow hTN
  have hRsyl : IsSylowTwoOf R C := (a4_2_4 hX hsub R).1 (a4_2_5 hX hsub hTsyl)
  have hCnorm : N ≤ normalizer (C : Set G) := fun n hn =>
    A4.mem_normalizer_of_conj_mem fun m hm =>
      conj_mem_centralizerSection (Subgroup.le_normalizer hn) hn
        (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁ hn) hm
  have hL : CharTwo L := A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful
  have hCM : C ≤ normalizer (L : Set G) := fun c hc =>
    normalizer_l0_le hhat hL hTL S.uniqueM
      (mem_normalizer_l0_of_mem_centralizerSection (s134_l0_le_L1 S) hL1L hc)
  intro n hn
  obtain ⟨c, hc, m, hm, rfl⟩ := exists_mul_normalizer_of_isSylowTwoOf hRsyl (hCnorm hn)
  exact mul_mem (hCM hc) (hNR hm)

theorem stmt13_2_2_9L1Perm_holds (h1332 : Stmt13_3_2) :
    Stmt13_2_2_9L1Perm := by
  intro G _ _ T L V hH hV _ hhat hZV
  obtain ⟨S⟩ := exists_setting134 h1332 hH hV hZV
  exact stmt13_2_2_9L1_of_setting134 S hhat

end CFSG.Quasithin.H13.U3
