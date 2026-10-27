module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2Transfer
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.GroupTheory.PCore.InfPCoreOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem permutes_subgroupOf {A B N : Subgroup G} (hA : A ≤ N) (hB : B ≤ N)
    (h : Permutes A B) : Permutes (A.subgroupOf N) (B.subgroupOf N) := by
  unfold Permutes at h ⊢
  ext x
  rw [Set.mem_mul, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have ha' : (a : G) ∈ A := ha
    have hb' : (b : G) ∈ B := hb
    have hx : (x : G) ∈ (B : Set G) * (A : Set G) := by
      rw [← h]
      exact ⟨(a : G), ha', (b : G), hb', by simpa using congrArg Subtype.val hab⟩
    obtain ⟨b', hb', a', ha', hbax⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr
      ⟨⟨b', hB hb'⟩, Subgroup.mem_subgroupOf.mpr hb', ⟨a', hA ha'⟩,
        Subgroup.mem_subgroupOf.mpr ha', Subtype.ext hbax⟩
  · rintro ⟨b, hb, a, ha, hba⟩
    have ha' : (a : G) ∈ A := ha
    have hb' : (b : G) ∈ B := hb
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [h]
      exact ⟨(b : G), hb', (a : G), ha', by simpa using congrArg Subtype.val hba⟩
    obtain ⟨a', ha', b', hb', habx⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr
      ⟨⟨a', hA ha'⟩, Subgroup.mem_subgroupOf.mpr ha', ⟨b', hB hb'⟩,
        Subgroup.mem_subgroupOf.mpr hb', Subtype.ext habx⟩

theorem piSet_congr {H H' : Type} [Group H] [Finite H] [Group H'] [Finite H']
    {X : Subgroup H} {Y : Subgroup H'} (h : Nat.card ↥X = Nat.card ↥Y) :
    piSet X = piSet Y := by
  ext p
  simp only [piSet, Set.mem_setOf_eq, h]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

@[expose] noncomputable def Y0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup ↥(c.H hV) :=
  (c.L0.subgroupOf c.L).map (c.phiL hV)

@[expose] noncomputable def f0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ↥c.L0 →* ↥(c.Y0 hV) :=
  ((c.phiL hV).comp (Subgroup.inclusion c.hL0L)).codRestrict (c.Y0 hV) fun x =>
    Subgroup.mem_map.mpr ⟨⟨(x : G), c.hL0L x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩

@[simp] theorem f0_apply_coe (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (x : ↥c.L0) :
    ((c.f0 hV x : ↥(c.Y0 hV)) : ↥(c.H hV)) = c.phiL hV ⟨(x : G), c.hL0L x.2⟩ := rfl

theorem f0_surjective (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Function.Surjective (c.f0 hV) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
  refine ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext ?_⟩
  show c.phiL hV ⟨(x : G), c.hL0L (Subgroup.mem_subgroupOf.mp hx)⟩ = (y : ↥(c.H hV))
  rw [show (⟨(x : G), c.hL0L (Subgroup.mem_subgroupOf.mp hx)⟩ : ↥c.L) = x from
    Subtype.ext rfl]
  exact hxy

theorem commutator_L0_eq_top (c : Ctx23L D Ch) :
    ⁅(⊤ : Subgroup ↥c.L0), (⊤ : Subgroup ↥c.L0)⁆ = ⊤ := by
  have hcomm : commutator ↥c.L0 = ⊤ :=
    (Subgroup.map_injective c.L0.subtype_injective) (by
      rw [Subgroup.map_subtype_commutator, c.hL0.prop.2.1]
      simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := c.L0)).symm)
  rw [← commutator_def]
  exact hcomm

theorem f0_ker_commutator_mem_pCore (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    ∀ x ∈ (c.f0 hV).ker, ∀ y : ↥c.L0,
      x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥c.L0 := by
  intro x hx y
  have hx1 : c.phiL hV ⟨(x : G), c.hL0L x.2⟩ = 1 := by
    have h := congrArg (fun z : ↥(c.Y0 hV) => (z : ↥(c.H hV))) (MonoidHom.mem_ker.mp hx)
    simpa only [f0_apply_coe, Subgroup.coe_one] using h
  have hxV : (x : G) ∈ Subgroup.centralizer (c.V : Set G) :=
    (c.phiL_eq_one_iff hV ⟨(x : G), c.hL0L x.2⟩).1 hx1
  have hcomm := c.commutator_mem_pCoreOf hV hK hnat (x : G)
    (Subgroup.mem_inf.mpr ⟨c.hL0L x.2, hxV⟩) (y : G) (c.hL0L y.2)
  have hmemL0 : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ c.L0 :=
    c.L0.mul_mem (c.L0.mul_mem (c.L0.mul_mem x.2 y.2) (c.L0.inv_mem x.2)) (c.L0.inv_mem y.2)
  have hmem : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L0 :=
    CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 c.hL0L ⟨hmemL0, hcomm⟩
  obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp
    (show (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈
      (CFSG.pCore 2 ↥c.L0).map c.L0.subtype from hmem)
  rw [show (x * y * x⁻¹ * y⁻¹ : ↥c.L0) = z from Subtype.ext hzval.symm]
  exact hz

theorem isL2_bar2_L0_of (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) (hS : KSchurL2) {j : ℕ}
    (h : IsL2 (Bar2 (c.Y0 hV)) j) : IsL2 (Bar2 c.L0) j :=
  isL2_quotientPCore_of_surjective (c.f0 hV) (c.f0_surjective hV) (c.commutator_L0_eq_top)
    (c.f0_ker_commutator_mem_pCore hV hK hnat) hS h

theorem isL2Square_bar2_L0_of (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) (hS : KSchurL2) {j : ℕ}
    (h : IsL2Square (Bar2 (c.Y0 hV)) j) : IsL2Square (Bar2 c.L0) j :=
  isL2Square_quotientPCore_of_surjective (c.f0 hV) (c.f0_surjective hV)
    (c.commutator_L0_eq_top) (c.f0_ker_commutator_mem_pCore hV hK hnat) hS h

theorem inf_centralizer_V_le_pCoreOf_L0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) (hS : KSchurL2)
    {j : ℕ} (hshape : IsL2 (Bar2 (c.Y0 hV)) j ∨ IsL2Square (Bar2 (c.Y0 hV)) j) :
    c.L0 ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L0 := by
  intro x hx
  obtain ⟨hxL0, hxV⟩ := Subgroup.mem_inf.mp hx
  have h1 : c.phiL hV ⟨x, c.hL0L hxL0⟩ = 1 :=
    (c.phiL_eq_one_iff hV ⟨x, c.hL0L hxL0⟩).2 hxV
  have hker : (⟨x, hxL0⟩ : ↥c.L0) ∈ (CFSG.pCore 2 ↥(c.Y0 hV)).comap (c.f0 hV) := by
    rw [Subgroup.mem_comap]
    have h2 : (c.f0 hV) ⟨x, hxL0⟩ = 1 := Subtype.ext h1
    rw [h2]
    exact (CFSG.pCore 2 ↥(c.Y0 hV)).one_mem
  rw [comap_pCore_eq_of_surjective (c.f0 hV) (c.f0_surjective hV) (c.commutator_L0_eq_top)
    (c.f0_ker_commutator_mem_pCore hV hK hnat) hS hshape] at hker
  exact Subgroup.mem_map.mpr ⟨⟨x, hxL0⟩, hker, rfl⟩

theorem inf_centralizer_V_eq_bot_of_le (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) (hS : KSchurL2)
    {j : ℕ} (hshape : IsL2 (Bar2 (c.Y0 hV)) j ∨ IsL2Square (Bar2 (c.Y0 hV)) j)
    {A : Subgroup G} (hA0 : A ≤ c.L0) (hAodd : Odd (Nat.card A)) :
    A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥ := by
  have hp : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 c.L0) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L0)).map c.L0.subtype
  have hbot : A ⊓ CFSG.Open.pCoreOf 2 c.L0 = ⊥ :=
    uc22p2214_inf_eq_bot_of_odd hAodd hp
  have hle : A ⊓ Subgroup.centralizer (c.V : Set G) ≤ A ⊓ CFSG.Open.pCoreOf 2 c.L0 := by
    intro x hx
    obtain ⟨hxA, hxV⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxA, c.inf_centralizer_V_le_pCoreOf_L0 hV hK hnat hS hshape
      (Subgroup.mem_inf.mpr ⟨hA0 hxA, hxV⟩)⟩
  exact le_bot_iff.mp (hle.trans (le_of_eq hbot))

theorem inf_centralizer_V_eq_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) (hS : KSchurL2) {j : ℕ}
    (hshape : IsL2 (Bar2 (c.Y0 hV)) j ∨ IsL2Square (Bar2 (c.Y0 hV)) j) :
    c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥ :=
  c.inf_centralizer_V_eq_bot_of_le hV hK hnat hS hshape c.hB.1
    (uc22p22f_odd_card_B c.toCtx21)

@[expose] noncomputable def Astar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (A : Subgroup G) :
    Subgroup ↥(c.H hV) :=
  (A.subgroupOf c.L).map (c.phiL hV)

@[expose] noncomputable def Bstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup ↥(c.H hV) :=
  (c.B.subgroupOf c.L).map (c.phiL hV)

theorem Bstar_eq_Astar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    c.Bstar hV = c.Astar hV c.B := rfl

theorem Astar_le_Y0 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {A : Subgroup G}
    (hA0 : A ≤ c.L0) : c.Astar hV A ≤ c.Y0 hV :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono c.L hA0)

@[expose] noncomputable def CH (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) : Subgroup ↥(c.H hV) :=
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
  fixingSubgroupOf ↥(c.H hV) (c.W hV) ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))

theorem phiL_mem_CH_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (x : ↥c.L) :
    c.phiL hV x ∈ c.CH hV ↔ (x : G) ∈ Subgroup.centralizer (D.Z : Set G) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
  exact c.phiL_mem_fixingSubgroup_Ztil_iff hV x

theorem phiL_eq_one_of_mem_of_le (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {A : Subgroup G} (hinj : A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥)
    {K : Subgroup ↥c.L} (hK : K ≤ A.subgroupOf c.L) {x : ↥c.L} (hx : x ∈ K)
    (h1 : c.phiL hV x = 1) : x = 1 := by
  have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp (hK hx)
  have hxV : (x : G) ∈ Subgroup.centralizer (c.V : Set G) := (c.phiL_eq_one_iff hV x).1 h1
  have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
    rw [← hinj]
    exact Subgroup.mem_inf.mpr ⟨hxA, hxV⟩
  exact Subtype.ext (Subgroup.mem_bot.mp hbot)

theorem phiL_eq_one_of_mem_of_le_B (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) {K : Subgroup ↥c.L}
    (hK : K ≤ c.B.subgroupOf c.L) {x : ↥c.L} (hx : x ∈ K) (h1 : c.phiL hV x = 1) :
    x = 1 :=
  c.phiL_eq_one_of_mem_of_le hV hinj hK hx h1

@[expose] noncomputable def phiLOn (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (K : Subgroup ↥c.L) :
    ↥K →* ↥(K.map (c.phiL hV)) :=
  ((c.phiL hV).comp K.subtype).codRestrict (K.map (c.phiL hV)) fun x =>
    Subgroup.mem_map.mpr ⟨(x : ↥c.L), x.2, rfl⟩

@[simp] theorem phiLOn_apply_coe (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (K : Subgroup ↥c.L) (x : ↥K) :
    ((c.phiLOn hV K x : ↥(K.map (c.phiL hV))) : ↥(c.H hV)) = c.phiL hV (x : ↥c.L) := rfl

theorem phiLOn_surjective (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (K : Subgroup ↥c.L) : Function.Surjective (c.phiLOn hV K) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[expose] noncomputable def equivMapPhiL (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (K : Subgroup ↥c.L) (hinj : ∀ x ∈ K, c.phiL hV x = 1 → x = 1) :
    ↥K ≃* ↥(K.map (c.phiL hV)) :=
  MulEquiv.ofBijective (c.phiLOn hV K) ⟨fun x y hxy => by
    have h1 : c.phiLOn hV K (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : ((x * y⁻¹ : ↥K) : ↥c.L) = 1 :=
      hinj _ (x * y⁻¹).2 (by simpa using congrArg Subtype.val h1)
    exact mul_inv_eq_one.mp (Subtype.ext h2), c.phiLOn_surjective hV K⟩

theorem card_Astar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {A : Subgroup G}
    (hA0 : A ≤ c.L0) (hinj : A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) :
    Nat.card ↥(c.Astar hV A) = Nat.card ↥A := by
  have hK : ∀ x ∈ A.subgroupOf c.L, c.phiL hV x = 1 → x = 1 :=
    fun x hx => c.phiL_eq_one_of_mem_of_le hV hinj le_rfl hx
  calc Nat.card ↥(c.Astar hV A) = Nat.card ↥(A.subgroupOf c.L) :=
        (Nat.card_congr (c.equivMapPhiL hV (A.subgroupOf c.L) hK).toEquiv).symm
    _ = Nat.card ↥A := Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (hA0.trans c.hL0L)).toEquiv

theorem isMulCommutative_Astar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {A : Subgroup G} (hAab : IsMulCommutative A) :
    IsMulCommutative ↥(c.Astar hV A) := by
  have hcomm : ∀ a b : ↥(A.subgroupOf c.L), a * b = b * a := by
    intro a b
    have hA := hAab.is_comm.comm
      (⟨(a : G), Subgroup.mem_subgroupOf.mp a.2⟩ : ↥A)
      ⟨(b : G), Subgroup.mem_subgroupOf.mp b.2⟩
    have hG : (a : G) * (b : G) = (b : G) * (a : G) := congrArg Subtype.val hA
    exact Subtype.ext (Subtype.ext hG)
  haveI : IsMulCommutative ↥(A.subgroupOf c.L) := ⟨⟨hcomm⟩⟩
  exact Subgroup.map_isMulCommutative (H := A.subgroupOf c.L) (c.phiL hV)

theorem odd_card_Astar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {A : Subgroup G}
    (hA0 : A ≤ c.L0) (hAodd : Odd (Nat.card A))
    (hinj : A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) : Odd (Nat.card ↥(c.Astar hV A)) := by
  rw [c.card_Astar hV hA0 hinj]
  exact hAodd

theorem isMulCommutative_Bstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    IsMulCommutative ↥(c.Bstar hV) := by
  rw [c.Bstar_eq_Astar hV]
  exact c.isMulCommutative_Astar hV c.hB.2.1

theorem odd_card_Bstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) : Odd (Nat.card ↥(c.Bstar hV)) := by
  rw [c.Bstar_eq_Astar hV]
  exact c.odd_card_Astar hV c.hB.1 (uc22p22f_odd_card_B c.toCtx21) hinj

theorem card_sup_sylowStar_Astar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {A : Subgroup G}
    (hA0 : A ≤ c.L0) (hAodd : Odd (Nat.card A)) (hAT : Permutes A D.T)
    (hinj : A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) :
    Nat.card ↥((c.sylowStar hV : Subgroup ↥(c.H hV)) ⊔ c.Astar hV A) =
      Nat.card (c.sylowStar hV : Subgroup ↥(c.H hV)) * Nat.card ↥(c.Astar hV A) := by
  have hpermL : Permutes A (D.T ⊓ c.L) :=
    CFSG.GroupTheory.permutes_inf_of_le (hA0.trans c.hL0L) hAT
  have hDT : (D.T ⊓ c.L).subgroupOf c.L = D.T.subgroupOf c.L := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have hpermSub : Permutes (A.subgroupOf c.L) (D.T.subgroupOf c.L) := by
    rw [← hDT]
    exact permutes_subgroupOf (hA0.trans c.hL0L) inf_le_right hpermL
  have hpermH : Permutes (c.Astar hV A) (c.sylowStar hV : Subgroup ↥(c.H hV)) := by
    have h := CFSG.GroupTheory.map_permutes_map (c.phiL hV) hpermSub
    rwa [← c.sylowStar_coe hV] at h
  have hdisj : c.Astar hV A ⊓ (c.sylowStar hV : Subgroup ↥(c.H hV)) = ⊥ :=
    uc22p2214_inf_eq_bot_of_odd (c.odd_card_Astar hV hA0 hAodd hinj)
      (c.sylowStar hV).isPGroup'
  have h := uc22p2214_card_sup_of_permutes hpermH hdisj
  rwa [sup_comm, mul_comm] at h

theorem card_sup_sylowStar_Bstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) :
    Nat.card ↥((c.sylowStar hV : Subgroup ↥(c.H hV)) ⊔ c.Bstar hV) =
      Nat.card (c.sylowStar hV : Subgroup ↥(c.H hV)) * Nat.card ↥(c.Bstar hV) := by
  obtain ⟨-, -, -, -, -, -, -, hperm, -, -⟩ := c.hB.2.2
  rw [c.Bstar_eq_Astar hV]
  exact c.card_sup_sylowStar_Astar hV c.hB.1 (uc22p22f_odd_card_B c.toCtx21) hperm hinj

theorem inf_map_phiL_CH (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (K : Subgroup ↥c.L) :
    K.map (c.phiL hV) ⊓ c.CH hV =
      (K ⊓ (Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L).map (c.phiL hV) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxK, hxCH⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, hyK, rfl⟩ := Subgroup.mem_map.mp hxK
    exact Subgroup.mem_map.mpr
      ⟨y, Subgroup.mem_inf.mpr ⟨hyK, (c.phiL_mem_CH_iff hV y).1 hxCH⟩, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_map.mpr ⟨y, (Subgroup.mem_inf.mp hy).1, rfl⟩,
        (c.phiL_mem_CH_iff hV y).2 (Subgroup.mem_inf.mp hy).2⟩

theorem inf_Astar_CH (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {A : Subgroup G}
    (hA0 : A ≤ c.L0) :
    c.Astar hV A ⊓ c.CH hV =
      ((A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L).map (c.phiL hV) := by
  have hzero : A.subgroupOf c.L ⊓ (Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L =
      (A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L := by
    rw [← Subgroup.comap_subtype A c.L,
      ← Subgroup.comap_subtype (Subgroup.centralizer (D.Z : Set G)) c.L,
      ← Subgroup.comap_subtype (A ⊓ Subgroup.centralizer (D.Z : Set G)) c.L,
      Subgroup.comap_inf]
  rw [Astar, inf_map_phiL_CH, hzero]

theorem piSet_inf_Astar_CH (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {A : Subgroup G}
    (hA0 : A ≤ c.L0) (hinj : A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) :
    piSet (c.Astar hV A ⊓ c.CH hV) =
      piSet (A ⊓ Subgroup.centralizer (D.Z : Set G)) := by
  have hK : ∀ x ∈ (A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L,
      c.phiL hV x = 1 → x = 1 :=
    fun x hx => c.phiL_eq_one_of_mem_of_le hV hinj
      (K := (A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L)
      (Subgroup.subgroupOf_mono c.L inf_le_left) hx
  refine piSet_congr ?_
  rw [c.inf_Astar_CH hV hA0,
    (Nat.card_congr (c.equivMapPhiL hV
      ((A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L) hK).toEquiv).symm]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left.trans (hA0.trans c.hL0L))).toEquiv

theorem piSet_inf_Bstar_CH (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) :
    piSet (c.Bstar hV ⊓ c.CH hV) =
      piSet (c.B ⊓ Subgroup.centralizer (D.Z : Set G)) := by
  rw [c.Bstar_eq_Astar hV]
  exact c.piSet_inf_Astar_CH hV c.hB.1 hinj

theorem piSet_Astar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {A : Subgroup G}
    (hA0 : A ≤ c.L0) (hinj : A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) :
    piSet (c.Astar hV A) = piSet A :=
  piSet_congr (c.card_Astar hV hA0 hinj)

theorem piSet_Bstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) :
    piSet (c.Bstar hV) = piSet c.B := by
  rw [c.Bstar_eq_Astar hV]
  exact c.piSet_Astar hV c.hB.1 hinj

theorem isCyclic_inf_centralizer_Z_of_le (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {A : Subgroup G} (hA0 : A ≤ c.L0)
    (hinj : A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥)
    (h : IsCyclic ↥(c.Astar hV A ⊓ c.CH hV)) :
    IsCyclic ↥(A ⊓ Subgroup.centralizer (D.Z : Set G)) := by
  have hK : ∀ x ∈ (A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L,
      c.phiL hV x = 1 → x = 1 :=
    fun x hx => c.phiL_eq_one_of_mem_of_le hV hinj
      (K := (A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L)
      (Subgroup.subgroupOf_mono c.L inf_le_left) hx
  have h' : IsCyclic ↥(((A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L).map
      (c.phiL hV)) := by
    rwa [← c.inf_Astar_CH hV hA0]
  exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe
    (inf_le_left.trans (hA0.trans c.hL0L)))).mp
    ((MulEquiv.isCyclic (c.equivMapPhiL hV
      ((A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L) hK)).mpr h')

theorem isCyclic_inf_centralizer_Z_of (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥)
    (h : IsCyclic ↥(c.Bstar hV ⊓ c.CH hV)) :
    IsCyclic ↥(c.B ⊓ Subgroup.centralizer (D.Z : Set G)) := by
  rw [c.Bstar_eq_Astar hV] at h
  exact c.isCyclic_inf_centralizer_Z_of_le hV c.hB.1 hinj h

theorem inf_centralizer_Z_eq_bot_of_le (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {A : Subgroup G} (hA0 : A ≤ c.L0)
    (hinj : A ⊓ Subgroup.centralizer (c.V : Set G) = ⊥)
    (h : c.Astar hV A ⊓ c.CH hV = ⊥) : A ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ := by
  have hmap :
      ((A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L).map (c.phiL hV) = ⊥ := by
    rw [← c.inf_Astar_CH hV hA0]
    exact h
  have hker : (A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L ≤ (c.phiL hV).ker :=
    (Subgroup.map_eq_bot_iff _).mp hmap
  have hbot : (A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : x = 1 :=
      c.phiL_eq_one_of_mem_of_le hV hinj
        (K := (A ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L)
        (Subgroup.subgroupOf_mono c.L inf_le_left) hx (MonoidHom.mem_ker.mp (hker hx))
    rw [hx1]
    exact (⊥ : Subgroup ↥c.L).one_mem
  have hdisj : Disjoint (A ⊓ Subgroup.centralizer (D.Z : Set G)) c.L :=
    Subgroup.subgroupOf_eq_bot.mp hbot
  have hle : A ⊓ Subgroup.centralizer (D.Z : Set G) ≤ c.L :=
    inf_le_left.trans (hA0.trans c.hL0L)
  rw [eq_bot_iff]
  intro x hx
  have hx1 : x = 1 := (Subgroup.disjoint_def.mp hdisj) hx (hle hx)
  rw [hx1]
  exact (⊥ : Subgroup G).one_mem

theorem inf_centralizer_Z_eq_bot_of (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥)
    (h : c.Bstar hV ⊓ c.CH hV = ⊥) :
    c.B ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ := by
  rw [c.Bstar_eq_Astar hV] at h
  exact c.inf_centralizer_Z_eq_bot_of_le hV c.hB.1 hinj h

theorem map_subgroupOf_le_Bstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {E : Subgroup G}
    (hE : E ≤ c.B) : (E.subgroupOf c.L).map (c.phiL hV) ≤ c.Bstar hV :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono c.L hE)

theorem inf_map_subgroupOf_CH_eq_bot (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {E : Subgroup G} (hE : E ≤ c.B)
    (hEdisj : E ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥) :
    (E.subgroupOf c.L).map (c.phiL hV) ⊓ c.CH hV = ⊥ := by
  have hzero : E.subgroupOf c.L ⊓ (Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L = ⊥ := by
    rw [← Subgroup.comap_subtype E c.L,
      ← Subgroup.comap_subtype (Subgroup.centralizer (D.Z : Set G)) c.L,
      ← Subgroup.comap_inf, hEdisj, Subgroup.comap_subtype (⊥ : Subgroup G) c.L,
      Subgroup.bot_subgroupOf]
  rw [c.inf_map_phiL_CH hV (E.subgroupOf c.L), hzero, Subgroup.map_bot]

theorem isCyclic_of_isCyclic_map_subgroupOf (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hinj : c.B ⊓ Subgroup.centralizer (c.V : Set G) = ⊥) {E : Subgroup G} (hE : E ≤ c.B)
    (h : IsCyclic ↥((E.subgroupOf c.L).map (c.phiL hV))) : IsCyclic ↥E := by
  have hK : ∀ x ∈ E.subgroupOf c.L, c.phiL hV x = 1 → x = 1 :=
    fun x hx => c.phiL_eq_one_of_mem_of_le_B hV hinj (K := E.subgroupOf c.L)
      (Subgroup.subgroupOf_mono c.L hE) hx
  have hEcyc : IsCyclic ↥(E.subgroupOf c.L) :=
    (MulEquiv.isCyclic (c.equivMapPhiL hV (E.subgroupOf c.L) hK)).mpr h
  exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe
    (hE.trans (c.hB.1.trans c.hL0L)))).mp hEcyc

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
