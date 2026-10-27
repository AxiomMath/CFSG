module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A6S1372SixteenTilde

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace A6L76A

theorem rad_eq_bot_of_surjective {Γ Q : Type*} [Group Γ] [Group Q] [IsSimpleGroup Γ]
    (hΓ : ¬ Group.IsSolvable Γ) [Nontrivial Q] (π : Γ →* Q) (hπ : Function.Surjective π) :
    ∀ N : Subgroup Q, N.Normal → Group.IsSolvable ↥N → N = ⊥ := by
  have hinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      obtain ⟨q, hq⟩ := exists_ne (1 : Q)
      obtain ⟨g, rfl⟩ := hπ q
      exact hq ((MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top g))
  intro N hN hNs
  have hc : (N.comap π).Normal := hN.comap π
  have hcs : Group.IsSolvable ↥(N.comap π) :=
    Group.isSolvable_of_isSolvable_injective (f := π.subgroupComap N) fun x y hxy =>
      Subtype.ext (hinj (congrArg Subtype.val hxy))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap π) with h | h
  · rw [← Subgroup.map_comap_eq_self_of_surjective hπ N, h, Subgroup.map_bot]
  · exfalso
    rw [h] at hcs
    exact hΓ (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := Γ)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := Γ)).symm.injective)

theorem not_isSolvable_alt {n : ℕ} (hn : 5 ≤ n) :
    ¬ Group.IsSolvable ↥(alternatingGroup (Fin n)) := by
  intro h
  have : IsMulCommutative (Equiv.Perm (Fin n) ⧸ alternatingGroup (Fin n)) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr alternatingGroup.commutator_perm_le
  have := Group.isSolvable_of_subgroup_quotient (alternatingGroup (Fin n))
  refine Equiv.Perm.not_isSolvable (Fin n) ?_ this
  rw [Cardinal.mk_fin]
  exact_mod_cast hn

theorem isSimpleGroup_alt {n : ℕ} (hn : 5 ≤ n) : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
  alternatingGroup.isSimpleGroup (by simpa using hn)

theorem center_sl_eq_bot {n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) = ⊥ := by
  have := Fintype.ofFinite F
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow hn.ne'] at hr
    exact zero_ne_one hr
  have h1 : r = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [← Nat.card_eq_fintype_card, hF, pow_one] at this
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, h1]
  simp

theorem isSimpleGroup_sl {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) F) := by
  have e : Matrix.ProjectiveSpecialLinearGroup (Fin n) F ≃* Matrix.SpecialLinearGroup (Fin n) F :=
    (QuotientGroup.quotientMulEquivOfEq (center_sl_eq_bot hF)).trans QuotientGroup.quotientBot
  have h : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :=
    (CFSG.LinearGroups.linear_projective_simple (by omega) (Or.inl hn)).2.1
  exact e.symm.isSimpleGroup

theorem isSimpleGroup_statedSL {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL n F) := by
  have := isSimpleGroup_sl hn hF
  exact (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F).symm.isSimpleGroup

theorem not_isSolvable_statedSL {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] :
    ¬ Group.IsSolvable ↥(CFSG.Assembly.LowTwoRank.StatedSL n F) := by
  intro h
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hn)
  have : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :=
    CFSG.LinearGroups.linear_projective_nontrivial (by omega)
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin n) F) :=
    (QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))).nontrivial
  refine Group.IsPerfect.not_isSolvable (Matrix.SpecialLinearGroup (Fin n) F) ?_
  exact Group.isSolvable_of_isSolvable_injective
    (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F).toMonoidHom)
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F).injective

end A6L76A

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem not_comm_V3_le_V1 {X : Subgroup G} (hX : S.L1 ≤ X)
    (h : ∀ x ∈ X, ∀ v ∈ S.V3, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V) : False := by
  have h1 : ⁅S.V3, S.L1⁆ ≤ fsuV1 T V := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have e : ⁅v, l⁆ = (l * v * l⁻¹ * v⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact (fsuV1 T V).inv_mem (h l (hX hl) v hv)
  have h2 := Subgroup.card_le_of_le (S.V3_le_commutator_V3_L1.trans h1)
  rw [S.card_V3, S.card_V1] at h2
  omega

variable {S}

section Tilde

variable {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
include hH

theorem nontrivial_tilde_of_L1_le {K : Subgroup G} (hKH : K ≤ H) (hL1K : S.L1 ≤ K) :
    Nontrivial ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  refine S.not_comm_V3_le_V1 hL1K fun k hk v hv => ?_
  have h1 : (⟨A6Mod.secAct hHU hHV ⟨k, hKH hk⟩, (A6Mod.mem_autSec_iff hHU hHV hKH).2
      ⟨⟨k, hKH hk⟩, hk, rfl⟩⟩ : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) = 1 := Subsingleton.elim _ _
  exact (A6Mod.secAct_eq_one_iff hHU hHV _).1 (congrArg Subtype.val h1) v (le_conjClosure _ _ hv)

theorem secAct_solvRad_eq_one {K : Subgroup G} (hKH : K ≤ H)
    (hrad : ∀ N : Subgroup ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))), N.Normal → Group.IsSolvable ↥N → N = ⊥)
    {x : G} (hx : x ∈ solvRad K) :
    ∀ u ∈ conjClosure S.V3 H, x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set κ : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict _
      (fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩) with hκ
  have hκs : Function.Surjective κ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hψ
    exact ⟨⟨f, hfK⟩, rfl⟩
  have hRK : solvRad K ≤ K := solvRad_le K
  have hRs : Group.IsSolvable ↥((solvRad K).subgroupOf K) := by
    have := solvRad_isSolvable K
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hRK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRK).injective
  have hNn : (((solvRad K).subgroupOf K).map κ).Normal := (solvRad_normal K).map κ hκs
  have hNs : Group.IsSolvable ↥(((solvRad K).subgroupOf K).map κ) :=
    Group.isSolvable_of_surjective (κ.subgroupMap_surjective ((solvRad K).subgroupOf K))
  have hN := hrad _ hNn hNs
  have h1 : κ ⟨x, hRK hx⟩ ∈ ((solvRad K).subgroupOf K).map κ := ⟨⟨x, hRK hx⟩, hx, rfl⟩
  rw [hN, Subgroup.mem_bot] at h1
  exact (A6Mod.secAct_eq_one_iff hHU hHV _).1 (congrArg Subtype.val h1)

theorem T_le_normalizer_of_L1_le {K : Subgroup G} (hK : K ∈ cComp H) (hL1K : S.L1 ≤ K)
    (hrad : ∀ N : Subgroup ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))), N.Normal → Group.IsSolvable ↥N → N = ⊥) :
    T ≤ Subgroup.normalizer (K : Set G) := by
  intro t ht
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  by_contra hn
  have hne : K.map (MulAut.conj t).toMonoidHom ≠ K := fun he =>
    hn (LocDbl.map_conj_eq_iff.mp he)
  have hK' : K.map (MulAut.conj t).toMonoidHom ∈ cComp H :=
    LocDbl.map_conj_mem_cComp hK (Subgroup.le_normalizer (hTH ht))
  have hsub : IsSubnormal (K.map (MulAut.conj t).toMonoidHom ⊓ K) K :=
    A3.subnormal_inf_right (subnormal_of_mem_cComp hK') (le_of_mem_cComp hK)
  have hlt : K.map (MulAut.conj t).toMonoidHom ⊓ K < K := by
    refine lt_of_le_of_ne inf_le_right fun he => hne ?_
    have hle : K ≤ K.map (MulAut.conj t).toMonoidHom := he.ge.trans inf_le_left
    exact (LocDbl.eq_of_mem_cComp_of_le hK hK' hle).symm
  have hR := le_solvRad_of_subnormal_lt hK hsub hlt
  have hL1K' : S.L1 ≤ K.map (MulAut.conj t).toMonoidHom := by
    intro l hl
    have h1 : t⁻¹ * l * t⁻¹⁻¹ ∈ S.L1 :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 (T.inv_mem ht)) l).mp hl
    refine ⟨t⁻¹ * l * t, by simpa using hL1K h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine S.not_comm_V3_le_V1 ((le_inf hL1K' hL1K).trans hR) fun x hx v hv => ?_
  exact secAct_solvRad_eq_one hH (le_of_mem_cComp hK) hrad hx v (le_conjClosure _ _ hv)

theorem le_normalizer_of_L1_le (h37 : A37ForSQTK) (h38 : A38ForSQTK) {K : Subgroup G}
    (hK : K ∈ cComp H) (hL1K : S.L1 ≤ K)
    (hrad : ∀ N : Subgroup ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))), N.Normal → Group.IsSolvable ↥N → N = ⊥) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hN := normal_conjClosure_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
    hH.1.2 hTs hK
  have hT := T_le_normalizer_of_L1_le hH hK hL1K hrad
  have he : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk => (Subgroup.mem_normalizer_iff.mp (hT ht) k).mp hk)
      (le_conjClosure K T)
  rwa [he] at hN

end Tilde

theorem commutator_UH_eq_of_L1_le {H K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hL1K : S.L1 ≤ K) :
    ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H := by
  have hHU := le_normalizer_conjClosure S.V3 H
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro u hu k hk
    have hku : k * u⁻¹ * k⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hKH hk)) _).mp ((conjClosure S.V3 H).inv_mem hu)
    rw [commutatorElement_def, show u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) by group]
    exact (conjClosure S.V3 H).mul_mem hu hku
  · refine conjClosure_le fun h hh v hv => ?_
    have hv' : v ∈ ⁅conjClosure S.V3 H, K⁆ :=
      Subgroup.commutator_mono (le_conjClosure _ _) hL1K (S.V3_le_commutator_V3_L1 hv)
    have hN : h ∈ Subgroup.normalizer ((⁅conjClosure S.V3 H, K⁆ : Subgroup G) : Set G) := by
      refine LocDbl.map_conj_eq_iff.mp ?_
      rw [Subgroup.map_commutator, LocDbl.map_conj_eq_iff.mpr (hHU hh),
        LocDbl.map_conj_eq_iff.mpr (hHK hh)]
    exact (Subgroup.mem_normalizer_iff.mp hN v).mp hv'

end Setting4

end CFSG.Quasithin.H13.A6
