
module

public import CFSG.Monster.B.TwoA.Base.RankThreeBase
public import CFSG.Monster.B.TwoA.Base.SymFiveAut
public import CFSG.Monster.B.TwoA.Base.DirProd

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

@[expose] def beta3 :
    C3 →* Equiv.Perm (Fin 5) := betaCU.comp c3Proj

theorem beta3_surjective :
    Function.Surjective beta3 :=
  betaCU_surjective.comp c3Proj_surjective

@[expose] def R3C :
    Subgroup C3 := (CFSG.pCore 2 CU).comap c3Proj

@[expose] def R3 :
    Subgroup Dfull := R3C.map C3.subtype

theorem ker_beta3 :
    beta3.ker = R3C := by
  rw [beta3, ← MonoidHom.comap_ker, ker_betaCU]
  rfl

theorem natCard_R3C :
    Nat.card R3C = 2 ^ 35 := by
  rw [R3C, natCard_comap_of_surjective c3Proj_surjective, ker_c3Proj,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Ehat ⊓ C3 ≤ C3)).toEquiv,
    natCard_Ehat_inf_C3, natCard_pCore_CU]
  norm_num

theorem natCard_R3 :
    Nat.card R3 = 2 ^ 35 := by
  rw [R3, ← Nat.card_congr (R3C.equivMapOfInjective C3.subtype Subtype.coe_injective).toEquiv,
    natCard_R3C]

theorem R3C_eq_pCore :
    R3C = CFSG.pCore 2 C3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← ker_beta3]
  exact ker_eq_pCore_of_surjective beta3_surjective
    (IsPGroup.of_card (n := 35) (by rw [ker_beta3, natCard_R3C])) pCore_perm_five

theorem R3_eq_pCore_C3 :

    R3 = (CFSG.pCore 2 C3).map C3.subtype := by rw [R3, R3C_eq_pCore]

theorem E3_le_C3 :

    E3 ≤ C3 := fun _ ha => Subgroup.mem_centralizer_iff.2 fun _ hb =>
  EU_comm qV_Uplane (E3_eq_EU ▸ hb) (E3_eq_EU ▸ ha)

theorem E3_le_R3 :
    E3 ≤ R3 := by
  intro a ha
  have haC : a ∈ C3 := E3_le_C3 ha
  refine ⟨⟨a, haC⟩, ?_, rfl⟩
  have h1 : c3Proj ⟨a, haC⟩ = 1 := by
    rw [← MonoidHom.mem_ker, ker_c3Proj, Subgroup.mem_subgroupOf]
    exact ⟨EU_le_Ehat (E3_eq_EU ▸ ha), haC⟩
  change c3Proj ⟨a, haC⟩ ∈ CFSG.pCore 2 CU
  rw [h1]
  exact Subgroup.one_mem _

theorem index_E3_R3 :
    (E3.subgroupOf R3).index = 2 ^ 32 := by
  have h := (E3.subgroupOf R3).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe E3_le_R3).toEquiv, natCard_E3,
    natCard_R3] at h
  omega

abbrev C3K : Subgroup K3 := C3.subgroupOf K3

@[expose] def B3 :
    C3K →* Equiv.Perm (Fin 5) :=
  beta3.comp (Subgroup.subgroupOfEquivOfLe C3_le_K3).toMonoidHom

theorem B3_apply
    (c : C3K) :
    B3 c = beta3 ⟨(c : Dfull), (Subgroup.mem_subgroupOf.1 c.2)⟩ := rfl

theorem B3_surjective :
    Function.Surjective B3 :=
  beta3_surjective.comp (MulEquiv.surjective _)

theorem natCard_ker_B3 :
    Nat.card B3.ker = 2 ^ 35 := by
  rw [B3, natCard_ker_comp_of_surjective (MulEquiv.surjective _) beta3_surjective, ker_beta3,
    natCard_R3C]
  have hk : (Subgroup.subgroupOfEquivOfLe C3_le_K3).toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 (MulEquiv.injective _)
  rw [hk, Subgroup.card_bot, one_mul]

theorem ker_B3_eq_pCore :
    B3.ker = CFSG.pCore 2 C3K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ker_eq_pCore_of_surjective B3_surjective (IsPGroup.of_card natCard_ker_B3)
    pCore_perm_five

theorem ker_B3_characteristic :
    B3.ker.Characteristic := by
  rw [ker_B3_eq_pCore]
  infer_instance

abbrev R3K :
    Subgroup K3 := secKer B3

instance R3K_normal :
    R3K.Normal := secKer_normal B3 ker_B3_characteristic

theorem map_R3K :
    R3K.map K3.subtype = R3 := by
  ext d
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have hc' : beta3 ⟨(c : Dfull), Subgroup.mem_subgroupOf.1 c.2⟩ = 1 := hc
    rw [← MonoidHom.mem_ker, ker_beta3] at hc'
    exact ⟨_, hc', rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hcK : (⟨(c : Dfull), C3_le_K3 c.2⟩ : K3) ∈ C3K := c.2
    refine ⟨⟨(c : Dfull), C3_le_K3 c.2⟩, ⟨⟨_, hcK⟩, ?_, rfl⟩, rfl⟩
    change beta3 ⟨(c : Dfull), c.2⟩ = 1
    rw [← MonoidHom.mem_ker, ker_beta3]
    exact hc

theorem R3_subgroupOf_eq :
    R3.subgroupOf K3 = R3K := by
  rw [← map_R3K]
  exact Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective R3K

instance R3_subgroupOf_normal :
    (R3.subgroupOf K3).Normal := by
  rw [R3_subgroupOf_eq]
  infer_instance

theorem natCard_R3K :
    Nat.card R3K = 2 ^ 35 := by
  rw [← natCard_R3, ← map_R3K]
  exact Nat.card_congr (R3K.equivMapOfInjective K3.subtype Subtype.coe_injective).toEquiv

attribute [local instance] sharpAction

theorem mem_R3_iff
    (g : C3) : (g : Dfull) ∈ R3 ↔ c3Proj g ∈ CFSG.pCore 2 CU := by
  constructor
  · rintro ⟨c, hc, hcg⟩
    rw [← Subtype.ext hcg]
    exact hc
  · intro h
    exact ⟨g, h, rfl⟩

@[expose] def sigma3 :
    K3 →* Equiv.Perm (Fin 5) :=
  sigmaSec B3 B3_surjective ker_B3_characteristic sym5_conj_bijective

theorem sigma3_coe
    (g : C3) : sigma3 ⟨g, C3_le_K3 g.2⟩ = betaCU (c3Proj g) :=
  sigmaSec_coe B3 B3_surjective ker_B3_characteristic sym5_conj_bijective
    ⟨⟨g, C3_le_K3 g.2⟩, g.2⟩

end CFSG.Monster.B.TwoA
