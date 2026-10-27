module

public import CFSG.RankThree.GF2n.Tim81.Sec5.HBarAut
public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
public import CFSG.RankThree.GF2n.Tim81.Sec2.NatSumCocycle

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin CFSG.GroupTheory
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V H Hh : Subgroup G} {h₀ k₀ : G}

namespace Sec45Shape

@[reducible] private noncomputable def commCocycle
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    (u : G) (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H) : ↥H → SecMod hs :=
  fun z => SecMod.mk hs ⟨⁅u, (z : G)⁆, hHu (z : G) z.2⟩

@[simp] private theorem commCocycle_apply
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    (u : G) (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H) (z : ↥H) :
    commCocycle hs u hHu z = SecMod.mk hs ⟨⁅u, (z : G)⁆, hHu (z : G) z.2⟩ := rfl

private theorem commCocycle_mul_of_mem_kOf
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    (u : G) (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H)
    (hKu : ∀ k ∈ kOf V H, ⁅k, u⁆ ∈ Tim79a.xOf V H)
    (hWK : Tim79a.xOf V H ≤ kOf V H) {a k : ↥H} (hkK : (k : G) ∈ kOf V H) :
    commCocycle hs u hHu (a * k) = commCocycle hs u hHu a := by
  have huKW : ⁅u, (k : G)⁆ ∈ Tim79a.xOf V H := by
    rw [← commutatorElement_inv (k : G) u]
    exact (Tim79a.xOf V H).inv_mem (hKu (k : G) hkK)
  have hconjW : (a : G) * ⁅u, (k : G)⁆ * (a : G)⁻¹ ∈ Tim79a.xOf V H :=
    (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H a.2) _).mp huKW
  have hcomm : (⟨⁅u, ((a * k : ↥H) : G)⁆, hHu ((a * k : ↥H) : G) (a * k).2⟩ :
      ↥(kOf V H)) =
      (⟨⁅u, (a : G)⁆, hHu (a : G) a.2⟩ : ↥(kOf V H)) *
        ⟨(a : G) * ⁅u, (k : G)⁆ * (a : G)⁻¹, hWK hconjW⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk, Subgroup.coe_inv]
    rw [commutatorElement_def, commutatorElement_def]
    group
  calc commCocycle hs u hHu (a * k)
      = SecMod.mk hs (⟨⁅u, (a : G)⁆, hHu (a : G) a.2⟩ : ↥(kOf V H)) +
          SecMod.mk hs (⟨(a : G) * ⁅u, (k : G)⁆ * (a : G)⁻¹, hWK hconjW⟩ :
            ↥(kOf V H)) := by
        rw [show commCocycle hs u hHu (a * k) = SecMod.mk hs
            (⟨⁅u, ((a * k : ↥H) : G)⁆, hHu ((a * k : ↥H) : G) (a * k).2⟩ :
              ↥(kOf V H)) from rfl, ← SecMod.mk_mul hs, hcomm]
    _ = commCocycle hs u hHu a := by
        have hzero : SecMod.mk hs (⟨(a : G) * ⁅u, (k : G)⁆ * (a : G)⁻¹,
            hWK hconjW⟩ : ↥(kOf V H)) = 0 :=
          (SecMod.mk_eq_zero_iff hs _).mpr hconjW
        rw [show commCocycle hs u hHu a = SecMod.mk hs (⟨⁅u, (a : G)⁆, hHu (a : G) a.2⟩ :
          ↥(kOf V H)) from rfl, hzero, add_zero]

private noncomputable def commCocycleBar
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    (u : G) (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H)
    (hKu : ∀ k ∈ kOf V H, ⁅k, u⁆ ∈ Tim79a.xOf V H)
    (hWK : Tim79a.xOf V H ≤ kOf V H) : HBar V H → SecMod hs :=
  Quotient.lift (commCocycle hs u hHu) (by
    intro a b hab
    have hk : a⁻¹ * b ∈ (kOf V H).subgroupOf H := QuotientGroup.leftRel_apply.1 hab
    have hkK : (((a⁻¹ * b : ↥H) : G)) ∈ kOf V H := Subgroup.mem_subgroupOf.mp hk
    rw [show b = a * (a⁻¹ * b) from (mul_inv_cancel_left a b).symm]
    exact (commCocycle_mul_of_mem_kOf hs u hHu hKu hWK hkK).symm)

@[simp] private theorem commCocycleBar_piK
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    (u : G) (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H)
    (hKu : ∀ k ∈ kOf V H, ⁅k, u⁆ ∈ Tim79a.xOf V H)
    (hWK : Tim79a.xOf V H ≤ kOf V H) (a : ↥H) :
    commCocycleBar hs u hHu hKu hWK (piK V H a) = commCocycle hs u hHu a := rfl

private theorem commCocycle_mul
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    (u : G) (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H)
    [Module (ZMod 2) (SecMod hs)]
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) (a b : ↥H) :
    commCocycle hs u hHu (a * b) =
      commCocycle hs u hHu a +
        repSec hs hs.comm SL(2, F) ψ (ψ (piK V H a)) (commCocycle hs u hHu b) := by
  have hact : repSec hs hs.comm SL(2, F) ψ (ψ (piK V H a)) (commCocycle hs u hHu b) =
      SecMod.mk hs (⟨(a : G) * ⁅u, (b : G)⁆ * (a : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H a.2) _).mp
          (hHu (b : G) b.2)⟩ : ↥(kOf V H)) := by
    exact repSec_apply_piK_mk hs hs.comm SL(2, F) ψ a
      ⟨⁅u, (b : G)⁆, hHu (b : G) b.2⟩
  have hcomm : (⟨⁅u, ((a * b : ↥H) : G)⁆, hHu ((a * b : ↥H) : G) (a * b).2⟩ :
      ↥(kOf V H)) =
      (⟨⁅u, (a : G)⁆, hHu (a : G) a.2⟩ : ↥(kOf V H)) *
        ⟨(a : G) * ⁅u, (b : G)⁆ * (a : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H a.2) _).mp
            (hHu (b : G) b.2)⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk, Subgroup.coe_inv]
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [hact]
  calc commCocycle hs u hHu (a * b)
      = SecMod.mk hs (⟨⁅u, (a : G)⁆, hHu (a : G) a.2⟩ : ↥(kOf V H)) +
          SecMod.mk hs (⟨(a : G) * ⁅u, (b : G)⁆ * (a : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H a.2) _).mp
              (hHu (b : G) b.2)⟩ : ↥(kOf V H)) := by
        rw [show commCocycle hs u hHu (a * b) = SecMod.mk hs
            (⟨⁅u, ((a * b : ↥H) : G)⁆, hHu ((a * b : ↥H) : G) (a * b).2⟩ :
              ↥(kOf V H)) from rfl, ← SecMod.mk_mul hs, hcomm]
    _ = commCocycle hs u hHu a + _ := by
        rw [show commCocycle hs u hHu a = SecMod.mk hs (⟨⁅u, (a : G)⁆, hHu (a : G) a.2⟩ :
          ↥(kOf V H)) from rfl]

private theorem commCocycleBar_mul
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    (u : G) (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H)
    (hKu : ∀ k ∈ kOf V H, ⁅k, u⁆ ∈ Tim79a.xOf V H)
    (hWK : Tim79a.xOf V H ≤ kOf V H)
    [Module (ZMod 2) (SecMod hs)]
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) (x y : HBar V H) :
    commCocycleBar hs u hHu hKu hWK (x * y) =
      commCocycleBar hs u hHu hKu hWK x +
        repSec hs hs.comm SL(2, F) ψ (ψ x) (commCocycleBar hs u hHu hKu hWK y) := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
      change commCocycleBar hs u hHu hKu hWK (piK V H a * piK V H b) =
        commCocycleBar hs u hHu hKu hWK (piK V H a) +
          repSec hs hs.comm SL(2, F) ψ (ψ (piK V H a))
            (commCocycleBar hs u hHu hKu hWK (piK V H b))
      rw [← map_mul, commCocycleBar_piK, commCocycleBar_piK, commCocycleBar_piK]
      exact commCocycle_mul hs u hHu ψ a b

private theorem commCocycle_eq_zero_of_mem_imgK
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    (u : G) (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H)
    (hKu : ∀ k ∈ kOf V H, ⁅k, u⁆ ∈ Tim79a.xOf V H)
    (hWK : Tim79a.xOf V H ≤ kOf V H)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) {X : Subgroup G}
    (hXu : ∀ c ∈ X, ⁅c, u⁆ ∈ Tim79a.xOf V H) :
    ∀ x ∈ (imgK V H X).map ψ.toMonoidHom,
      commCocycleBar hs u hHu hKu hWK (ψ.symm x) = 0 := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨c, hcX, hcpi⟩ := (mem_imgK_iff).mp hy
  have hxW : ⁅(c : G), u⁆ ∈ Tim79a.xOf V H := hXu (c : G) hcX
  have huW : ⁅u, (c : G)⁆ ∈ Tim79a.xOf V H := by
    rw [← commutatorElement_inv (c : G) u]
    exact (Tim79a.xOf V H).inv_mem hxW
  have hzero : commCocycle hs u hHu c = 0 :=
    (SecMod.mk_eq_zero_iff hs _).mpr huW
  have hsymm : ψ.symm (ψ y) = y := by simp
  have hfin : commCocycleBar hs u hHu hKu hWK (ψ.symm (ψ y)) =
      commCocycle hs u hHu c := by
    rw [hsymm, ← hcpi, commCocycleBar_piK]
  exact hfin.trans hzero

theorem commutator_Pc_mem_xOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {u : G}
    (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H) (hKu : ∀ k ∈ kOf V H, ⁅k, u⁆ ∈ Tim79a.xOf V H)
    {X : Subgroup G} (hXP : X ≤ Pc M V) (hX : 2 < Nat.card (imgK V H X))
    (hXu : ∀ c ∈ X, ⁅c, u⁆ ∈ Tim79a.xOf V H) : ∀ p ∈ Pc M V, ⁅p, u⁆ ∈ Tim79a.xOf V H := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hWK : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  have hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H) := hS.quotModHyp h
  haveI hnorm : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hs.normal
  have hmod : Module (ZMod 2) (SecMod hs) := SecMod.module hs hw.sq_mem
  letI := hmod
  let coc : HBar V H → SecMod hs := commCocycleBar hs u hHu hKu hWK
  have hcoc_piK : ∀ a : ↥H, coc (piK V H a) = commCocycle hs u hHu a :=
    commCocycleBar_piK hs u hHu hKu hWK
  have hcoc_mul : ∀ x y : HBar V H, coc (x * y) =
      coc x + repSec hs hs.comm SL(2, F) ψ (ψ x) (coc y) :=
    commCocycleBar_mul hs u hHu hKu hWK ψ
  let f : SL(2, F) → SecMod hs := fun s => coc (ψ.symm s)
  have hf_apply : ∀ s : SL(2, F), f s = coc (ψ.symm s) := fun s => rfl
  have hf : ∀ g h : SL(2, F), f (g * h) =
      f g + repSec hs hs.comm SL(2, F) ψ g (f h) := by
    intro g h
    have h1 : ψ.symm (g * h) = ψ.symm g * ψ.symm h := map_mul ψ.symm g h
    rw [hf_apply, h1, hcoc_mul, MulEquiv.apply_symm_apply, hf_apply, hf_apply]
  let A : Subgroup SL(2, F) := (imgK V H (Pc M V)).map ψ.toMonoidHom
  let A₁ : Subgroup SL(2, F) := (imgK V H X).map ψ.toMonoidHom
  have hP : (∀ a ∈ A, a * a = 1) ∧ Nat.card A = Fintype.card F := by
    have h1 := hS.map_imgK_conj_sylow h ψ (x := 1) H.one_mem
    simpa only [A, conjSubgroup_one] using h1
  have hA₁A : A₁ ≤ A := by
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, imgK_mono hXP hy, rfl⟩
  have hA₁card : 2 < Nat.card A₁ := by
    rw [show Nat.card A₁ = Nat.card (imgK V H X) from
      Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]
    exact hX
  have hf₁ : ∀ x ∈ A₁, f x = 0 := by
    intro x hx
    exact commCocycle_eq_zero_of_mem_imgK hs u hHu hKu hWK ψ hXu x hx
  have hl1 : 1 ≤ l := hw.one_le
  have hmain : ∀ x ∈ A, f x = 0 :=
    Sec2.IsNatSumModule.cocycle_eq_zero_of_le (hσ := hw.natSum hs hmod)
      (hF := hl) (ha := by omega) (hf := hf) (hA2 := hP.1) (hA := hP.2)
      (hA₁A := hA₁A) (hA₁ := hA₁card) (hf₁ := hf₁)
  intro p hp
  have hpA : ψ (piK V H ⟨p, hS.Pc_le hp⟩) ∈ A :=
    Subgroup.mem_map.mpr ⟨piK V H ⟨p, hS.Pc_le hp⟩,
      Subgroup.mem_map.mpr ⟨⟨p, hS.Pc_le hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩, rfl⟩
  have hzero : SecMod.mk hs (⟨⁅u, p⁆, hHu p (hS.Pc_le hp)⟩ : ↥(kOf V H)) = 0 := by
    have h := hmain _ hpA
    rwa [show f (ψ (piK V H ⟨p, hS.Pc_le hp⟩)) =
      SecMod.mk hs (⟨⁅u, p⁆, hHu p (hS.Pc_le hp)⟩ : ↥(kOf V H)) from by
      rw [hf_apply, MulEquiv.symm_apply_apply, hcoc_piK]] at h
  have huW : ⁅u, p⁆ ∈ Tim79a.xOf V H := (SecMod.mk_eq_zero_iff hs _).mp hzero
  rw [show ⁅p, u⁆ = ⁅u, p⁆⁻¹ from (commutatorElement_inv u p).symm]
  exact (Tim79a.xOf V H).inv_mem huW


end Sec45Shape

namespace Sec5Hyp

private theorem commutator_mem_inf_of_mem_centralizer (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {F₀ : Subgroup G} (hF₀E : F₀ ≤ ⁅Pc M V, U⁆)
    (hF₀card : Nat.card F₀ = Nat.card V ^ 2) {c u : G} (hcP : c ∈ Pc M V) (huU : u ∈ U)
    (hcF₀ : F₀ ≤ Subgroup.centralizer ({c} : Set G)) : ⁅c, u⁆ ∈ F₀ := by
  classical
  have h := hS.toRootHyp
  obtain ⟨g, y, hSg, hyH, hUeq, hVy, -, hE, -, -⟩ := hS.exists_sigma_data hU
  have huW : u ∈ Tim79a.xOf V (hOf M V g) := by
    have hu' : u ∈ conjSubgroup g V := hUeq ▸ huU
    rw [hVy] at hu'
    exact Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hyH) hu'
  have hcH : c ∈ hOf M V g := hSg.Pc_le hcP
  have hcuW : ⁅c, u⁆ ∈ Tim79a.xOf V (hOf M V g) :=
    mem_commutator_xOf (z := ⟨c, hcH⟩) (w := ⟨u, huW⟩)
  have hcuc : ⁅⁅u, c⁆, c⁆ = 1 :=
    Sec45Shape.commutator_commutator_eq_one h hSg hcP huW
  have hcuC : ⁅c, u⁆ ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hcomm : c * ⁅u, c⁆ = ⁅u, c⁆ * c := by
      have h2 := commutatorElement_eq_one_iff_mul_comm.mp hcuc
      first | exact h2 | exact h2.symm
    have hcommute : Commute c ⁅u, c⁆ := hcomm
    have h1 : ⁅c, u⁆ = ⁅u, c⁆⁻¹ := (commutatorElement_inv u c).symm
    rw [h1]
    exact hcommute.inv_right.eq
  by_cases hcK : c ∈ kOf V (hOf M V g)
  · have hcu1 : ⁅c, u⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hcK).2 u huW).symm
    rw [hcu1]
    exact F₀.one_mem
  · have hplane := Sec45Shape.xOf_inf_centralizer_le_and_card h hSg hcP hcK
    have hF₀W : F₀ ≤ Tim79a.xOf V (hOf M V g) :=
      hF₀E.trans (le_of_eq hE) |>.trans inf_le_right
    have hF₀le : F₀ ≤ Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({c} : Set G) :=
      le_inf hF₀W hcF₀
    have hcardeq : Nat.card ↥(Tim79a.xOf V (hOf M V g) ⊓
        Subgroup.centralizer ({c} : Set G)) = Nat.card F₀ := by
      rw [hplane.2, hF₀card]
    have heq : F₀ = Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hF₀le (le_of_eq hcardeq)
    rw [heq]
    exact Subgroup.mem_inf.mpr ⟨hcuW, hcuC⟩

private theorem commutator_conj_mem_xOf (h : RootHyp M V) (hS : Sec45Shape M V Hh k₀)
    {u z k : G} (huH : ∀ w ∈ Hh, ⁅u, w⁆ ∈ kOf V Hh)
    (huW : u ∈ Subgroup.centralizer (Tim79a.xOf V Hh : Set G))
    (hzH : z ∈ Hh) (hkK : k ∈ kOf V Hh) (hkuW : ⁅k, u⁆ ∈ Tim79a.xOf V Hh) :
    ⁅z * k * z⁻¹, u⁆ ∈ Tim79a.xOf V Hh := by
  classical
  have hW_le_K : Tim79a.xOf V Hh ≤ kOf V Hh := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  have hs := hS.quotModHyp h
  have hconjK_le : conjSubgroup u (kOf V Hh) ≤ kOf V Hh := by
    intro y hy
    have hyx : u⁻¹ * y * u ∈ kOf V Hh := mem_conjSubgroup.mp hy
    have hcomm : ⁅u, u⁻¹ * y * u⁆ ∈ kOf V Hh := huH _ ((kOf_le V Hh) hyx)
    have hyform : y = ⁅u, u⁻¹ * y * u⁆ * (u⁻¹ * y * u) := by
      rw [commutatorElement_def]; group
    rw [hyform]
    exact (kOf V Hh).mul_mem hcomm hyx
  have huN : u ∈ Subgroup.normalizer (kOf V Hh : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hconjK_le
        (le_of_eq (by rw [card_conjSubgroup])))
  have hk''K : ⁅u⁻¹, z⁻¹⁆ ∈ kOf V Hh := by
    have hzK : z⁻¹ * ⁅u, z⁆ * z ∈ kOf V Hh := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_kOf V Hh (Hh.inv_mem hzH)) _).mp (huH z hzH)
    have hzu : z⁻¹ * u * z = (z⁻¹ * ⁅u, z⁆ * z) * u := by
      rw [commutatorElement_def]; group
    have hcoe : ⁅u⁻¹, z⁻¹⁆ = u⁻¹ * (z⁻¹ * u * z) := by
      rw [commutatorElement_def]; group
    rw [hcoe, hzu]
    simpa only [mul_assoc, inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huN) _).mp hzK
  have hkey : ⁅z * k * z⁻¹, u⁆ = z * ⁅k, u * ⁅u⁻¹, z⁻¹⁆⁆ * z⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    group
  have huWnorm : ∀ w ∈ Tim79a.xOf V Hh, u * w * u⁻¹ ∈ Tim79a.xOf V Hh := by
    intro w hw
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.centralizer_le_normalizer _ huW) w).mp hw
  have hstep : ⁅k, u * ⁅u⁻¹, z⁻¹⁆⁆ =
      ⁅k, u⁆ * (u * ⁅k, ⁅u⁻¹, z⁻¹⁆⁆ * u⁻¹) := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    group
  have hkk''W : ⁅k, ⁅u⁻¹, z⁻¹⁆⁆ ∈ Tim79a.xOf V Hh := hs.comm k hkK _ hk''K
  have hinner : ⁅k, u * ⁅u⁻¹, z⁻¹⁆⁆ ∈ Tim79a.xOf V Hh := by
    rw [hstep]
    exact (Tim79a.xOf V Hh).mul_mem hkuW (huWnorm _ hkk''W)
  rw [hkey]
  exact (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V Hh hzH) _).mp hinner

private theorem commutator_kOf_le_xOf (h : RootHyp M V) (hS : Sec45Shape M V Hh k₀)
    {y : G} (hyH : y ∈ Hh) (hPy : conjSubgroup k₀ (Pc M V) = conjSubgroup y (Pc M V))
    {u : G} (huH : ∀ z ∈ Hh, ⁅u, z⁆ ∈ kOf V Hh)
    (huW : u ∈ Subgroup.centralizer (Tim79a.xOf V Hh : Set G))
    (hPK : ∀ c ∈ Pc M V ⊓ kOf V Hh, ⁅c, u⁆ ∈ Tim79a.xOf V Hh) :
    ∀ k ∈ kOf V Hh, ⁅k, u⁆ ∈ Tim79a.xOf V Hh := by
  classical
  have hKnorm : conjSubgroup y (kOf V Hh) = kOf V Hh :=
    conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V Hh hyH)
  have hWnorm : kOf V Hh ≤ Subgroup.normalizer (Tim79a.xOf V Hh : Set G) :=
    (kOf_le V Hh).trans (Tim79a.H_le_normalizer_xOf V Hh)
  let T : Subgroup G := commMemSubgroup (kOf V Hh) (Tim79a.xOf V Hh) hWnorm u
  have hmemT : ∀ x : G, x ∈ T ↔ x ∈ kOf V Hh ∧ ⁅x, u⁆ ∈ Tim79a.xOf V Hh :=
    fun x => mem_commMemSubgroup hWnorm u x
  have hT_le : T ≤ kOf V Hh := commMemSubgroup_le _ _ hWnorm u
  have hPK_le : Pc M V ⊓ kOf V Hh ≤ T := by
    intro c hc
    exact (hmemT c).mpr ⟨hc.2, hPK c hc⟩
  have hHconj_le : ∀ z ∈ Hh, conjSubgroup z T ≤ T := by
    intro z hz x hx
    have hx' : z⁻¹ * x * z ∈ T := mem_conjSubgroup.mp hx
    obtain ⟨hxK, hxuW⟩ := (hmemT _).mp hx'
    have hxK' : x ∈ kOf V Hh :=
      (Subgroup.mem_normalizer_iff''.mp (le_normalizer_kOf V Hh hz) x).mpr hxK
    refine (hmemT x).mpr ⟨hxK', ?_⟩
    have hcomm := commutator_conj_mem_xOf h hS huH huW hz hxK hxuW
    rwa [show z * (z⁻¹ * x * z) * z⁻¹ = x by group] at hcomm
  have hHnorm : Hh ≤ Subgroup.normalizer (T : Set G) := by
    intro z hz
    refine mem_normalizer_iff_conjSubgroup_eq.mpr
      (Subgroup.eq_of_le_of_card_ge (hHconj_le z hz) (le_of_eq ?_))
    rw [card_conjSubgroup]
  have hPhK_le : conjSubgroup y (Pc M V ⊓ kOf V Hh) ≤ T := by
    intro x hx
    have hx' : y⁻¹ * x * y ∈ Pc M V ⊓ kOf V Hh := by
      simpa only [inv_inv] using mem_conjSubgroup.mp hx
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hHnorm hyH)) x).mpr
      (by simpa only [inv_inv] using hPK_le hx')
  have hkfact : kOf V Hh = (Pc M V ⊓ kOf V Hh) ⊔ conjSubgroup y (Pc M V ⊓ kOf V Hh) := by
    conv_lhs => rw [hS.kFact]
    rw [hPy]
    congr 1
    conv_lhs => rw [← hKnorm]
    rw [← conjSubgroup_inf]
  have hK_le_T : kOf V Hh ≤ T := hkfact ▸ sup_le hPK_le hPhK_le
  intro k hk
  exact ((hmemT k).mp (hK_le_T hk)).2

private theorem card_imgK_inf_centralizer (hS : Sec5Hyp M V) (h51d : Sec5.Stmt51d M V)
    {h : G} (hh : conjSubgroup h V ∈ sigmaSet M V) {F₀ : Subgroup G} (hF : F₀ ∈ fSet M V)
    (hF₀W : F₀ ≤ Tim79a.xOf V (hOf M V h)) :
    Nat.card ↥(imgK V (hOf M V h) (Pc M V ⊓ Subgroup.centralizer (F₀ : Set G))) =
      Nat.card V := by
  classical
  have hroot := hS.toRootHyp
  have hSh := hS.shape hh
  have hXH : Pc M V ⊓ Subgroup.centralizer (F₀ : Set G) ≤ hOf M V h :=
    inf_le_left.trans hSh.Pc_le
  have hKcent : kOf V (hOf M V h) ≤ Subgroup.centralizer (F₀ : Set G) := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk).2 x (hF₀W hx)
  have hXinf : (Pc M V ⊓ Subgroup.centralizer (F₀ : Set G)) ⊓ kOf V (hOf M V h) =
      Pc M V ⊓ kOf V (hOf M V h) := by
    refine le_antisymm ?_ (le_inf (le_inf inf_le_left (inf_le_right.trans hKcent)) inf_le_right)
    intro x hx
    obtain ⟨⟨hxP, -⟩, hxK⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxP, hxK⟩
  have hsplit := RootHyp.card_imgK_mul_card_inf (V := V) (H := hOf M V h)
    (X := Pc M V ⊓ Subgroup.centralizer (F₀ : Set G)) hXH
  rw [hXinf] at hsplit
  have h2 : Nat.card ↥(Pc M V ⊓ kOf V (hOf M V h)) * Nat.card V ^ 2 = Nat.card ↥(Pc M V) :=
    hSh.card_Pc_inf_kOf hroot
  have h3 : Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (F₀ : Set G)) * Nat.card V =
      Nat.card ↥(Pc M V) := h51d F₀ hF
  have hPKpos : 0 < Nat.card ↥(Pc M V ⊓ kOf V (hOf M V h)) := Nat.card_pos
  have hqpos : 0 < Nat.card V := Nat.card_pos
  have hmain : Nat.card ↥(imgK V (hOf M V h) (Pc M V ⊓
        Subgroup.centralizer (F₀ : Set G))) *
        (Nat.card ↥(Pc M V ⊓ kOf V (hOf M V h)) * Nat.card V) =
      Nat.card V * (Nat.card ↥(Pc M V ⊓ kOf V (hOf M V h)) * Nat.card V) := by
    calc Nat.card ↥(imgK V (hOf M V h) (Pc M V ⊓
          Subgroup.centralizer (F₀ : Set G))) *
          (Nat.card ↥(Pc M V ⊓ kOf V (hOf M V h)) * Nat.card V)
        = (Nat.card ↥(imgK V (hOf M V h) (Pc M V ⊓
            Subgroup.centralizer (F₀ : Set G))) *
            Nat.card ↥(Pc M V ⊓ kOf V (hOf M V h))) * Nat.card V := by ring
      _ = Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (F₀ : Set G)) * Nat.card V := by
          rw [hsplit]
      _ = Nat.card ↥(Pc M V) := h3
      _ = Nat.card ↥(Pc M V ⊓ kOf V (hOf M V h)) * Nat.card V ^ 2 := h2.symm
      _ = Nat.card V * (Nat.card ↥(Pc M V ⊓ kOf V (hOf M V h)) * Nat.card V) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hPKpos hqpos) hmain

private theorem commutator_Pc_le_xOf_of_fSet (hS : Sec5Hyp M V) (h51d : Sec5.Stmt51d M V)
    {g h : G} (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hKF : ∀ u ∈ conjSubgroup g V,
      (∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h)) ∧
        u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G))
    (hF : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) ∈ fSet M V) :
    ⁅Pc M V, conjSubgroup g V⁆ ≤ Tim79a.xOf V (hOf M V h) := by
  classical
  have hroot := hS.toRootHyp
  have hSh := hS.shape hh
  obtain ⟨gh, yh, hSh', hyhH, hUeqh, hVyh, hyhV, hEh, hCh, hCEh⟩ := hS.exists_sigma_data hh
  have hPgh : conjSubgroup gh (Pc M V) = conjSubgroup h (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqh.symm
  have hhhOf : hOf M V gh = hOf M V h := by
    unfold hOf
    rw [hPgh]
  have hVyh' : conjSubgroup h V = conjSubgroup yh V := hUeqh.trans hVyh
  have hyhH' : yh ∈ hOf M V h := hhhOf ▸ hyhH
  have hEh' : ⁅Pc M V, conjSubgroup h V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V h) := by
    rw [hEh, hhhOf]
  have hF₀W : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) ≤
      Tim79a.xOf V (hOf M V h) :=
    (inf_le_right.trans (le_of_eq hEh')).trans inf_le_right
  have hPK : ∀ u ∈ conjSubgroup g V, ∀ c ∈ Pc M V ⊓ kOf V (hOf M V h),
      ⁅c, u⁆ ∈ Tim79a.xOf V (hOf M V h) := by
    intro u hu c hc
    have hcF₀ : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) ≤
        Subgroup.centralizer ({c} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hc.2).2 x (hF₀W hx)).symm
    exact hF₀W (commutator_mem_inf_of_mem_centralizer hS hg inf_le_left hF.2.1
      hc.1 hu hcF₀)
  rw [Subgroup.commutator_le]
  intro p hp u hu
  have huH := (hKF u hu).1
  have huW := (hKF u hu).2
  have hKu : ∀ k ∈ kOf V (hOf M V h), ⁅k, u⁆ ∈ Tim79a.xOf V (hOf M V h) :=
    commutator_kOf_le_xOf hroot hSh hyhH'
      (hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hVyh') huH huW (hPK u hu)
  have hXcard : 2 < Nat.card ↥(imgK V (hOf M V h)
      (Pc M V ⊓ Subgroup.centralizer
        ((⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆ : Subgroup G) : Set G))) := by
    rw [card_imgK_inf_centralizer hS h51d hh hF hF₀W]
    have h4 := hroot.four_le_card
    omega
  have hXu : ∀ c ∈ Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆ : Subgroup G) : Set G),
      ⁅c, u⁆ ∈ Tim79a.xOf V (hOf M V h) := by
    intro c hc
    have hcF₀ : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) ≤
        Subgroup.centralizer ({c} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (Subgroup.mem_centralizer_iff.mp hc.2 x hx).symm
    exact hF₀W (commutator_mem_inf_of_mem_centralizer hS hg inf_le_left hF.2.1
      hc.1 hu hcF₀)
  exact Sec45Shape.commutator_Pc_mem_xOf hroot hSh huH hKu inf_le_left hXcard hXu p hp

theorem fSet_inf_eq_V_impossible (hS : Sec5Hyp M V) (h51d : Sec5.Stmt51d M V)
    {g h : G} (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hKF : ∀ u ∈ conjSubgroup g V,
      (∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h)) ∧
        u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G))
    (hF : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) ∈ fSet M V) :
    False := by
  classical
  have hroot := hS.toRootHyp
  have hSh := hS.shape hh
  have hEgW := commutator_Pc_le_xOf_of_fSet hS h51d hg hh hKF hF
  obtain ⟨gh, yh, hSh', hyhH, hUeqh, hVyh, hyhV, hEh, hCh, hCEh⟩ := hS.exists_sigma_data hh
  have hPgh : conjSubgroup gh (Pc M V) = conjSubgroup h (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqh.symm
  have hhOf : hOf M V gh = hOf M V h := by
    unfold hOf
    rw [hPgh]
  have hEh' : ⁅Pc M V, conjSubgroup h V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V h) := by
    rw [hEh, hhOf]
  have hEgEh : ⁅Pc M V, conjSubgroup g V⁆ ≤ ⁅Pc M V, conjSubgroup h V⁆ := by
    rw [hEh']
    exact le_inf (hS.commutator_le_Pc hg) hEgW
  have hF₀eq : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) =
      ⁅Pc M V, conjSubgroup g V⁆ := inf_eq_left.mpr hEgEh
  have hcard : Nat.card V ^ 2 = Nat.card V ^ 3 := by
    rw [← hF.2.1, hF₀eq, hS.card_commutator_Pc hg]
  have hq : 1 < Nat.card V := by
    have h4 := hroot.four_le_card
    omega
  have h23 : 2 = 3 := Nat.pow_right_injective hq hcard
  omega


private theorem piK_conj_eq_of_commutator_mem {V H : Subgroup G} {u z : G}
    (huz : ⁅u, z⁆ ∈ kOf V H) (hzH : z ∈ H) (huzH : u * z * u⁻¹ ∈ H) :
    piK V H ⟨u * z * u⁻¹, huzH⟩ = piK V H ⟨z, hzH⟩ := by
  refine (QuotientGroup.eq_iff_div_mem).mpr ?_
  have hdiv : (⟨u * z * u⁻¹, huzH⟩ / ⟨z, hzH⟩ : ↥H) =
      ⟨⁅u, z⁆, kOf_le V H huz⟩ := by
    apply Subtype.ext
    simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    rw [commutatorElement_def]
  rw [hdiv]
  exact Subgroup.mem_subgroupOf.mpr huz

section SectionConjugation

variable {M V : Subgroup G} {g h : G}
variable (hroot : RootHyp M V) (hSh : Sec45Shape M V (hOf M V h) h)
variable {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
variable {hl : Fintype.card F = 2 ^ (2 * l)} {ψ : HBar V (hOf M V h) ≃* SL(2, F)}
variable (hw : Sec45ShapeWith M V (hOf M V h) F l hl ψ)
variable (hs : QuotMod.Hyp (hOf M V h) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h)))
variable [((Tim79a.xOf V (hOf M V h)).subgroupOf (kOf V (hOf M V h))).Normal]
variable [Module (ZMod 2) (SecMod hs)]

private theorem repSec_comp_conj {u : G} (hHu : ∀ z ∈ (hOf M V h), ⁅u, z⁆ ∈ kOf V (hOf M V h))
    (huNK : ∀ n ∈ kOf V (hOf M V h), u * n * u⁻¹ ∈ kOf V (hOf M V h))
    {φ : SecMod hs →ₗ[ZMod 2] SecMod hs}
    (hφmk : ∀ n : ↥(kOf V (hOf M V h)), φ (SecMod.mk hs n) =
      SecMod.mk hs ⟨u * (n : G) * u⁻¹, huNK n n.2⟩) :
    ∀ (s : SL(2, F)) (v : SecMod hs),
      φ (repSec hs hs.comm SL(2, F) ψ s v) =
        repSec hs hs.comm SL(2, F) ψ s (φ v) := by
  have huzH : ∀ z : ↥(hOf M V h), u * (z : G) * u⁻¹ ∈ (hOf M V h) := by
    intro z
    have hcomm : ⁅u, (z : G)⁆ ∈ kOf V (hOf M V h) := hHu z z.2
    rw [show u * (z : G) * u⁻¹ = ⁅u, (z : G)⁆ * (z : G) by
      rw [commutatorElement_def]; group]
    exact (hOf M V h).mul_mem (kOf_le V (hOf M V h) hcomm) z.2
  have hpi : ∀ z : ↥(hOf M V h),
      piK V (hOf M V h) ⟨u * (z : G) * u⁻¹, huzH z⟩ = piK V (hOf M V h) z :=
    fun z => piK_conj_eq_of_commutator_mem (hHu z z.2) z.2 (huzH z)
  have hpoint : ∀ (z : ↥(hOf M V h)) (v : SecMod hs),
      φ (repSec hs hs.comm SL(2, F) ψ (ψ (piK V (hOf M V h) z)) v) =
        repSec hs hs.comm SL(2, F) ψ (ψ (piK V (hOf M V h) z)) (φ v) := by
    intro z v
    obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs v
    let wz : ↥(hOf M V h) := ⟨u * (z : G) * u⁻¹, huzH z⟩
    calc φ (repSec hs hs.comm SL(2, F) ψ (ψ (piK V (hOf M V h) z)) (SecMod.mk hs n))
        = SecMod.mk hs ⟨u * ((z : G) * (n : G) * (z : G)⁻¹) * u⁻¹,
            huNK _ (hs.conj z z.2 n n.2)⟩ := by
          rw [repSec_apply_piK_mk, hφmk]
      _ = repSec hs hs.comm SL(2, F) ψ (ψ (piK V (hOf M V h) wz))
            (SecMod.mk hs ⟨u * (n : G) * u⁻¹, huNK n n.2⟩) := by
          rw [repSec_apply_piK_mk]
          congr 1
          apply Subtype.ext
          simp only [wz]
          group
      _ = repSec hs hs.comm SL(2, F) ψ (ψ (piK V (hOf M V h) z))
            (SecMod.mk hs ⟨u * (n : G) * u⁻¹, huNK n n.2⟩) := by rw [hpi z]
      _ = repSec hs hs.comm SL(2, F) ψ (ψ (piK V (hOf M V h) z)) (φ (SecMod.mk hs n)) := by
          rw [hφmk]
  intro s v
  obtain ⟨z, hz⟩ := piK_surjective V (hOf M V h) (ψ.symm s)
  have hseq : ψ (piK V (hOf M V h) z) = s := by rw [hz, MulEquiv.apply_symm_apply]
  rw [← hseq]
  exact hpoint z v

private theorem commutator_mem_xOf_of_fixedSub_le_ker
    (hroot : RootHyp M V) (hSh : Sec45Shape M V (hOf M V h) h)
    (hw : Sec45ShapeWith M V (hOf M V h) F l hl ψ) {u : G}
    (huNK : ∀ n ∈ kOf V (hOf M V h), u * n * u⁻¹ ∈ kOf V (hOf M V h))
    {φ : SecMod hs →ₗ[ZMod 2] SecMod hs}
    (hφmk : ∀ n : ↥(kOf V (hOf M V h)), φ (SecMod.mk hs n) =
      SecMod.mk hs ⟨u * (n : G) * u⁻¹, huNK n n.2⟩)
    (hfix : fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ≤
      LinearMap.ker (φ - LinearMap.id)) :
    ∀ k ∈ Pc M V ⊓ kOf V (hOf M V h), ⁅u, k⁆ ∈ Tim79a.xOf V (hOf M V h) := by
  intro k hk
  have hkK : k ∈ kOf V (hOf M V h) := hk.2
  have hsub : SecMod.mk hs ⟨k, hkK⟩ ∈
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) := by
    rw [Sec45Shape.fixedSub_repSec_Pc hroot hSh hw hs]
    exact (mk_mem_subSec_iff hs le_sup_right).mpr (Subgroup.mem_sup_left hk)
  have hker := hfix hsub
  have heq : φ (SecMod.mk hs ⟨k, hkK⟩) = SecMod.mk hs ⟨k, hkK⟩ := by
    rw [LinearMap.mem_ker] at hker
    exact sub_eq_zero.mp (by simpa [LinearMap.sub_apply] using hker)
  have hmkeq : SecMod.mk hs ⟨u * k * u⁻¹, huNK k hkK⟩ = SecMod.mk hs ⟨k, hkK⟩ :=
    (hφmk ⟨k, hkK⟩).symm.trans heq
  have hmemW : (u * k * u⁻¹)⁻¹ * k ∈ Tim79a.xOf V (hOf M V h) :=
    (QuotMod.mk_eq_mk_iff (N := kOf V (hOf M V h)) (N₀ := Tim79a.xOf V (hOf M V h)) _ _).mp hmkeq
  have hnorm : k * ((u * k * u⁻¹)⁻¹ * k) * k⁻¹ ∈ Tim79a.xOf V (hOf M V h) :=
    (Subgroup.mem_normalizer_iff.mp
      (Tim79a.H_le_normalizer_xOf V (hOf M V h) (kOf_le V (hOf M V h) hkK)) _).mp hmemW
  have hconj : k * ((u * k * u⁻¹)⁻¹ * k) * k⁻¹ = ⁅u, k⁆⁻¹ := by
    rw [commutatorElement_def]; group
  rw [hconj] at hnorm
  simpa using (Tim79a.xOf V (hOf M V h)).inv_mem hnorm

private theorem subSec_sup_le_fixedSub_inf_ker (hS : Sec5Hyp M V)
    (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hroot : RootHyp M V) (hSh : Sec45Shape M V (hOf M V h) h)
    (hw : Sec45ShapeWith M V (hOf M V h) F l hl ψ) {u : G}
    {u : G} (huU : u ∈ conjSubgroup g V)
    (huW : u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G))
    (huNK : ∀ n ∈ kOf V (hOf M V h), u * n * u⁻¹ ∈ kOf V (hOf M V h))
    {φ : SecMod hs →ₗ[ZMod 2] SecMod hs}
    (hφmk : ∀ n : ↥(kOf V (hOf M V h)), φ (SecMod.mk hs n) =
      SecMod.mk hs ⟨u * (n : G) * u⁻¹, huNK n n.2⟩) :
    subSec hs (((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊔ Tim79a.xOf V (hOf M V h)) ≤
      fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓
        LinearMap.ker (φ - LinearMap.id) := by
  classical
  obtain ⟨gh, yh, hShg, hyhH, hUeqh, hVyh, hyhV, hEh, hChK, hChCE⟩ := hS.exists_sigma_data hh
  have hPgh : conjSubgroup gh (Pc M V) = conjSubgroup h (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqh.symm
  have hhOf : hOf M V gh = (hOf M V h) := by
    unfold hOf
    rw [hPgh]
  have hCh_eq : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h) := by
    change Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) = Pc M V ⊓ kOf V (hOf M V h)
    rw [hChK, hhOf]
  have hEh' : ⁅Pc M V, conjSubgroup h V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V h) := by
    rw [hEh, hhOf]
  let C : Subgroup G := (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
    (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))
  let X : Subgroup G := C ⊔ Tim79a.xOf V (hOf M V h)
  have hC_le_Ch : C ≤ Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) := inf_le_right
  have hC_le_K : C ≤ kOf V (hOf M V h) := fun c hc => (hCh_eq ▸ hC_le_Ch hc).2
  have hC_le_P : C ≤ Pc M V := fun c hc => (hC_le_Ch hc).1
  have hC_le_PK : C ≤ Pc M V ⊓ kOf V (hOf M V h) := fun c hc =>
    Subgroup.mem_inf.mpr ⟨hC_le_P hc, hC_le_K hc⟩
  have hW_le_X : Tim79a.xOf V (hOf M V h) ≤ X := le_sup_right
  have hX_le_K : X ≤ kOf V (hOf M V h) := sup_le hC_le_K (hroot.xOf_le_kOf hSh.Pc_le hSh.le_pCore)
  have hX_sup : X ≤ (Pc M V ⊓ kOf V (hOf M V h)) ⊔ Tim79a.xOf V (hOf M V h) :=
    sup_le (hC_le_PK.trans le_sup_left) le_sup_right
  have hC_le_cent : C ≤ Subgroup.centralizer ({u} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact Subgroup.mem_centralizer_iff.mp hc.1.2 u huU
  have hW_cent : Tim79a.xOf V (hOf M V h) ≤ Subgroup.centralizer ({u} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp huW w hw).symm
  have hX_cent : X ≤ Subgroup.centralizer ({u} : Set G) := sup_le hC_le_cent hW_cent
  intro v hv
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hv
  have hnX : (n : G) ∈ X := n.2.1
  have hnK : (n : G) ∈ kOf V (hOf M V h) := n.2.2
  have hcent : u * (n : G) * u⁻¹ = (n : G) := by
    have h := Subgroup.mem_centralizer_iff.mp (hX_cent hnX) u
      (by simp : u ∈ ({u} : Set G))
    rw [h]; group
  have hφn : φ (SecMod.mk hs ⟨(n : G), hnK⟩) = SecMod.mk hs ⟨(n : G), hnK⟩ := by
    rw [hφmk]
    congr 1
    exact Subtype.ext hcent
  have hfix : SecMod.mk hs ⟨(n : G), hnK⟩ ∈
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) := by
    rw [Sec45Shape.fixedSub_repSec_Pc hroot hSh hw hs]
    exact (mk_mem_subSec_iff hs le_sup_right).mpr (hX_sup hnX)
  have hker : SecMod.mk hs ⟨(n : G), hnK⟩ ∈ LinearMap.ker (φ - LinearMap.id) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hφn]
    simp
  rw [← hn]
  rw [show Subgroup.inclusion inf_le_right n = (⟨(n : G), hnK⟩ : ↥(kOf V (hOf M V h))) from
    Subtype.ext rfl]
  exact ⟨hfix, hker⟩

end SectionConjugation

private theorem section_intersection_and_card (hS : Sec5Hyp M V)
    {g h : G} (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hroot : RootHyp M V) (hSh : Sec45Shape M V (hOf M V h) h)
    (hs : QuotMod.Hyp (hOf M V h) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h)))
    [((Tim79a.xOf V (hOf M V h)).subgroupOf (kOf V (hOf M V h))).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hleh : ⁅Pc M V, conjSubgroup h V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    ((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊓
          Tim79a.xOf V (hOf M V h) = Pc M V ⊓ Tim79a.xOf V (hOf M V h) ∧
      Nat.card ↥(((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
          (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊔
            Tim79a.xOf V (hOf M V h)) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) =
      Nat.card (Tim79a.xOf V (hOf M V h)) *
        Nat.card ↥((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
          (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) := by
  classical
  obtain ⟨gh, yh, hShg, hyhH, hUeqh, hVyh, hyhV, hEh, hChK, hChCE⟩ := hS.exists_sigma_data hh
  have hPgh : conjSubgroup gh (Pc M V) = conjSubgroup h (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqh.symm
  have hhOf : hOf M V gh = hOf M V h := by
    unfold hOf
    rw [hPgh]
  have hCh_eq : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h) := by
    change Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h)
    rw [hChK, hhOf]
  have hEh' : ⁅Pc M V, conjSubgroup h V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V h) := by
    rw [hEh, hhOf]
  let C : Subgroup G := (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
    (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))
  let X : Subgroup G := C ⊔ Tim79a.xOf V (hOf M V h)
  have hC_le_Ch : C ≤ Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) := inf_le_right
  have hC_le_K : C ≤ kOf V (hOf M V h) := fun c hc => (hCh_eq ▸ hC_le_Ch hc).2
  have hC_le_P : C ≤ Pc M V := fun c hc => (hC_le_Ch hc).1
  have hCinf : C ⊓ Tim79a.xOf V (hOf M V h) = Pc M V ⊓ Tim79a.xOf V (hOf M V h) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hC_le_P hx.1, hx.2⟩
    · intro x hx
      obtain ⟨hxP, hxW⟩ := Subgroup.mem_inf.mp hx
      have hxEh : x ∈ ⁅Pc M V, conjSubgroup h V⁆ := by
        rw [hEh']
        exact Subgroup.mem_inf.mpr ⟨hxP, hxW⟩
      have hxK : x ∈ kOf V (hOf M V h) := (hroot.xOf_le_kOf hSh.Pc_le hSh.le_pCore) hxW
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_inf.mpr ⟨hleh hxEh, hCh_eq ▸ Subgroup.mem_inf.mpr ⟨hxP, hxK⟩⟩, hxW⟩
  have hX_CW : Nat.card ↥X * Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) =
      Nat.card (Tim79a.xOf V (hOf M V h)) * Nat.card ↥C := by
    have hcard := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (A := C) (B := Tim79a.xOf V (hOf M V h))
      (hC_le_K.trans ((kOf_le V (hOf M V h)).trans (Tim79a.H_le_normalizer_xOf V (hOf M V h))))
    rw [hCinf, Nat.mul_comm (Nat.card ↥C)] at hcard
    exact hcard
  exact ⟨hCinf, hX_CW⟩

private theorem card_subSec_mul_eq {g h : G}
    (hs : QuotMod.Hyp (hOf M V h) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h)))
    [((Tim79a.xOf V (hOf M V h)).subgroupOf (kOf V (hOf M V h))).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hX_le_K : ((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊔
          Tim79a.xOf V (hOf M V h) ≤ kOf V (hOf M V h))
    (hsec : ((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊓
          Tim79a.xOf V (hOf M V h) = Pc M V ⊓ Tim79a.xOf V (hOf M V h) ∧
      Nat.card ↥(((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
          (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊔
            Tim79a.xOf V (hOf M V h)) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) =
      Nat.card (Tim79a.xOf V (hOf M V h)) *
        Nat.card ↥((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
          (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)))) :
    Nat.card ↥(subSec hs (((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊔
          Tim79a.xOf V (hOf M V h))) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) =
      Nat.card ↥((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) := by
  have hXcard : Nat.card ↥(subSec hs (((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊔
          Tim79a.xOf V (hOf M V h))) * Nat.card (Tim79a.xOf V (hOf M V h)) =
      Nat.card ↥(((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊔
          Tim79a.xOf V (hOf M V h)) :=
    natCard_subSec hs le_sup_right hX_le_K
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(Tim79a.xOf V (hOf M V h)))) ?_
  calc Nat.card ↥(subSec hs (((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊔
          Tim79a.xOf V (hOf M V h))) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) *
      Nat.card (Tim79a.xOf V (hOf M V h))
      = Nat.card ↥(subSec hs (((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
          (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) ⊔
            Tim79a.xOf V (hOf M V h))) * Nat.card (Tim79a.xOf V (hOf M V h)) *
          Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) := by ring
    _ = Nat.card (Tim79a.xOf V (hOf M V h)) *
          Nat.card ↥((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
            (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) := by
        rw [hXcard, hsec.2]
    _ = Nat.card ↥((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
          (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) *
        Nat.card (Tim79a.xOf V (hOf M V h)) := by ring

private theorem card_fixedSub_mul_eq (hS : Sec5Hyp M V)
    {h : G} (hh : conjSubgroup h V ∈ sigmaSet M V)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    {hl : Fintype.card F = 2 ^ (2 * l)} {ψ : HBar V (hOf M V h) ≃* SL(2, F)}
    (hroot : RootHyp M V) (hSh : Sec45Shape M V (hOf M V h) h)
    (hw : Sec45ShapeWith M V (hOf M V h) F l hl ψ)
    (hs : QuotMod.Hyp (hOf M V h) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h)))
    [((Tim79a.xOf V (hOf M V h)).subgroupOf (kOf V (hOf M V h))).Normal]
    [Module (ZMod 2) (SecMod hs)] :
    Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) =
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) := by
  classical
  obtain ⟨gh, yh, hShg, hyhH, hUeqh, hVyh, hyhV, hEh, hChK, hChCE⟩ := hS.exists_sigma_data hh
  have hPgh : conjSubgroup gh (Pc M V) = conjSubgroup h (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqh.symm
  have hhOf : hOf M V gh = hOf M V h := by
    unfold hOf
    rw [hPgh]
  have hCh_eq : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h) := by
    change Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h)
    rw [hChK, hhOf]
  have hfixcard : Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) *
        Nat.card (Tim79a.xOf V (hOf M V h)) =
      Nat.card ↥((Pc M V ⊓ kOf V (hOf M V h)) ⊔ Tim79a.xOf V (hOf M V h)) := by
    rw [Sec45Shape.fixedSub_repSec_Pc hroot hSh hw hs]
    exact natCard_subSec hs le_sup_right
      (sup_le inf_le_right (hroot.xOf_le_kOf hSh.Pc_le hSh.le_pCore))
  have hChW : Nat.card ↥((Pc M V ⊓ kOf V (hOf M V h)) ⊔ Tim79a.xOf V (hOf M V h)) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) =
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) *
        Nat.card (Tim79a.xOf V (hOf M V h)) := by
    have hcard := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (A := Pc M V ⊓ kOf V (hOf M V h)) (B := Tim79a.xOf V (hOf M V h))
      ((inf_le_right : Pc M V ⊓ kOf V (hOf M V h) ≤ kOf V (hOf M V h)).trans
        ((kOf_le V (hOf M V h)).trans (Tim79a.H_le_normalizer_xOf V (hOf M V h))))
    rw [show (Pc M V ⊓ kOf V (hOf M V h)) ⊓ Tim79a.xOf V (hOf M V h) =
      Pc M V ⊓ Tim79a.xOf V (hOf M V h) from by
      rw [inf_assoc, inf_eq_right.mpr (hroot.xOf_le_kOf hSh.Pc_le hSh.le_pCore)]] at hcard
    simpa [hCh_eq] using hcard
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(Tim79a.xOf V (hOf M V h)))) ?_
  calc Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) * Nat.card (Tim79a.xOf V (hOf M V h))
      = Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
          ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) *
          Nat.card (Tim79a.xOf V (hOf M V h)) *
          Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) := by ring
    _ = Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) *
          Nat.card (Tim79a.xOf V (hOf M V h)) := by rw [hfixcard, hChW]
    _ = Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) *
          Nat.card (Tim79a.xOf V (hOf M V h)) := rfl

private theorem card_mul_pow_le_of_subSec_le {g h : G} {r : ℕ}
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {ψ : HBar V (hOf M V h) ≃* SL(2, F)}
    {hs : QuotMod.Hyp (hOf M V h) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h))}
    [((Tim79a.xOf V (hOf M V h)).subgroupOf (kOf V (hOf M V h))).Normal]
    [Module (ZMod 2) (SecMod hs)]
    {φ : SecMod hs →ₗ[ZMod 2] SecMod hs} {C : Subgroup G}
    (hA : Nat.card ↥(subSec hs (C ⊔ Tim79a.xOf V (hOf M V h))) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) = Nat.card ↥C)
    (hC : Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) =
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)))
    (hB : Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) =
      Nat.card V ^ (2 * r) * Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓ LinearMap.ker (φ - LinearMap.id)))
    (hmono : Nat.card ↥(subSec hs (C ⊔ Tim79a.xOf V (hOf M V h))) ≤
      Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓ LinearMap.ker (φ - LinearMap.id))) :
    Nat.card ↥C * Nat.card V ^ (2 * r) ≤
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) := by
  calc Nat.card ↥C * Nat.card V ^ (2 * r)
      = (Nat.card ↥(subSec hs (C ⊔ Tim79a.xOf V (hOf M V h))) *
          Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h))) * Nat.card V ^ (2 * r) := by rw [hA]
    _ = (Nat.card ↥(subSec hs (C ⊔ Tim79a.xOf V (hOf M V h))) * Nat.card V ^ (2 * r)) *
          Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) := by ring
    _ ≤ (Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
          ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓ LinearMap.ker (φ - LinearMap.id)) *
          Nat.card V ^ (2 * r)) * Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmono)
    _ = (Nat.card V ^ (2 * r) * Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
          ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓ LinearMap.ker (φ - LinearMap.id))) *
          Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) := by ring
    _ = Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
          ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) *
          Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) := by rw [← hB]
    _ = Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) := hC

private theorem card_inf_le_of_one_le (hS : Sec5Hyp M V)
    {g h : G} (hh : conjSubgroup h V ∈ sigmaSet M V)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    {hl : Fintype.card F = 2 ^ (2 * l)} {ψ : HBar V (hOf M V h) ≃* SL(2, F)}
    (hroot : RootHyp M V) (hSh : Sec45Shape M V (hOf M V h) h)
    (hw : Sec45ShapeWith M V (hOf M V h) F l hl ψ)
    (hs : QuotMod.Hyp (hOf M V h) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h)))
    [((Tim79a.xOf V (hOf M V h)).subgroupOf (kOf V (hOf M V h))).Normal]
    [Module (ZMod 2) (SecMod hs)]
    {u : G} (huU : u ∈ conjSubgroup g V)
    (huW : u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G))
    (huNK : ∀ n ∈ kOf V (hOf M V h), u * n * u⁻¹ ∈ kOf V (hOf M V h))
    {φ : SecMod hs →ₗ[ZMod 2] SecMod hs}
    (hφmk : ∀ n : ↥(kOf V (hOf M V h)), φ (SecMod.mk hs n) =
      SecMod.mk hs ⟨u * (n : G) * u⁻¹, huNK n n.2⟩)
    (hleh : ⁅Pc M V, conjSubgroup h V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    {r : ℕ}
    (hr : Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) =
      Fintype.card F ^ r * Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓ LinearMap.ker (φ - LinearMap.id)))
    (hFpow : Fintype.card F ^ r = Nat.card V ^ (2 * r)) (hr1 : 1 ≤ r) :
    Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) * Nat.card V ^ 2 ≤
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) := by
  classical
  obtain ⟨hsec, hX_CW⟩ := section_intersection_and_card hS hh hroot hSh hs hleh
  have hCinf := hsec
  let C : Subgroup G := (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊓
    (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))
  let X : Subgroup G := C ⊔ Tim79a.xOf V (hOf M V h)
  have hC_le_Ch : C ≤ Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) := inf_le_right
  have hCh_eq : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h) := by
    obtain ⟨gh, yh, hShg, hyhH, hUeqh, hVyh, hyhV, hEh, hChK, hChCE⟩ := hS.exists_sigma_data hh
    have hPgh : conjSubgroup gh (Pc M V) = conjSubgroup h (Pc M V) :=
      hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqh.symm
    have hhOf : hOf M V gh = hOf M V h := by
      unfold hOf
      rw [hPgh]
    change Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h)
    rw [hChK, hhOf]
  have hC_le_P : C ≤ Pc M V := fun c hc => (hC_le_Ch hc).1
  have hC_le_K : C ≤ kOf V (hOf M V h) := fun c hc => (hCh_eq ▸ hC_le_Ch hc).2
  have hW_le_X : Tim79a.xOf V (hOf M V h) ≤ X := le_sup_right
  have hX_le_K : X ≤ kOf V (hOf M V h) := sup_le hC_le_K (hroot.xOf_le_kOf hSh.Pc_le hSh.le_pCore)
  have hsub : subSec hs X ≤ fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓
      LinearMap.ker (φ - LinearMap.id) :=
    subSec_sup_le_fixedSub_inf_ker (hS := hS) (hh := hh)
      (hroot := hroot) (hSh := hSh) (hw := hw) (hs := hs) (u := u) (huU := huU)
      (huW := huW) (huNK := huNK) (hφmk := hφmk)
  have hA : Nat.card ↥(subSec hs X) * Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) =
      Nat.card ↥C := card_subSec_mul_eq (g := g) (h := h) hs hX_le_K ⟨hCinf, hX_CW⟩
  have hC : Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) *
        Nat.card ↥(Pc M V ⊓ Tim79a.xOf V (hOf M V h)) =
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) :=
    card_fixedSub_mul_eq hS hh hroot hSh hw hs
  have hB : Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) =
      Nat.card V ^ (2 * r) * Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓ LinearMap.ker (φ - LinearMap.id)) := by
    simpa only [hFpow] using hr
  have hmono : Nat.card ↥(subSec hs X) ≤
      Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓ LinearMap.ker (φ - LinearMap.id)) :=
    Nat.card_le_card_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective _)
  have hmain := card_mul_pow_le_of_subSec_le (g := g) (h := h) (r := r)
    (C := C) (hs := hs) (φ := φ) hA hC hB hmono
  have hq2 : Nat.card V ^ 2 ≤ Nat.card V ^ (2 * r) :=
    Nat.pow_le_pow_right (Nat.card_pos (α := ↥V)) (by omega)
  calc Nat.card ↥C * Nat.card V ^ 2
      ≤ Nat.card ↥C * Nat.card V ^ (2 * r) := Nat.mul_le_mul_left _ hq2
    _ ≤ Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) := hmain

private theorem normalizer_kOf_xOf_of_commutator_mem
    {H : Subgroup G} {u : G} (hHu : ∀ z ∈ H, ⁅u, z⁆ ∈ kOf V H)
    (huW : u ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G)) :
    u ∈ Subgroup.normalizer (kOf V H : Set G) ∧
      u ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) := by
  constructor
  · have hconjK_le : conjSubgroup u (kOf V H) ≤ kOf V H := by
      intro y hy
      have hyx : u⁻¹ * y * u ∈ kOf V H := mem_conjSubgroup.mp hy
      have hcomm : ⁅u, u⁻¹ * y * u⁆ ∈ kOf V H := hHu _ ((kOf_le V H) hyx)
      have hyform : y = ⁅u, u⁻¹ * y * u⁆ * (u⁻¹ * y * u) := by
        rw [commutatorElement_def]; group
      rw [hyform]
      exact (kOf V H).mul_mem hcomm hyx
    exact mem_normalizer_iff_conjSubgroup_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hconjK_le (le_of_eq (by rw [card_conjSubgroup])))
  · exact Subgroup.centralizer_le_normalizer _ huW

private noncomputable def zpowersQuotModHyp {H K W : Subgroup G} (hs : QuotMod.Hyp H K W)
    {u : G} (huN_K : u ∈ Subgroup.normalizer (K : Set G))
    (huN_W : u ∈ Subgroup.normalizer (W : Set G)) :
    QuotMod.Hyp (Subgroup.zpowers u) K W :=
  { le := hs.le
    comm := hs.comm
    conj := fun x hx n hn =>
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr huN_K) hx) n).mp hn
    conj₀ := fun x hx n hn =>
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr huN_W) hx) n).mp hn }

private noncomputable def conjQLinearMap {H K W : Subgroup G} (hs : QuotMod.Hyp H K W)
    [((W).subgroupOf K).Normal] [Module (ZMod 2) (SecMod hs)] {u : G}
    (hsu : QuotMod.Hyp (Subgroup.zpowers u) K W) : SecMod hs →ₗ[ZMod 2] SecMod hs :=
  (QuotMod.conjQ hsu u (Subgroup.mem_zpowers u)).toAdditive.toZModLinearMap 2

private theorem conjQLinearMap_mk {H K W : Subgroup G} (hs : QuotMod.Hyp H K W)
    [((W).subgroupOf K).Normal] [Module (ZMod 2) (SecMod hs)] {u : G}
    (hsu : QuotMod.Hyp (Subgroup.zpowers u) K W)
    (huNK : ∀ n ∈ K, u * n * u⁻¹ ∈ K) (n : ↥K) :
    conjQLinearMap hs hsu (SecMod.mk hs n) =
      SecMod.mk hs ⟨u * (n : G) * u⁻¹, huNK n n.2⟩ := by
  change (QuotMod.conjQ hsu u (Subgroup.mem_zpowers u)).toAdditive
    (QuotMod.mk W n) = QuotMod.mk W ⟨u * (n : G) * u⁻¹, huNK n n.2⟩
  rfl

private theorem exists_card_fixedSub_eq_of_fixed {h : G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    {hl : Fintype.card F = 2 ^ (2 * l)} {ψ : HBar V (hOf M V h) ≃* SL(2, F)}
    (hroot : RootHyp M V) (hSh : Sec45Shape M V (hOf M V h) h)
    (hw : Sec45ShapeWith M V (hOf M V h) F l hl ψ)
    (hs : QuotMod.Hyp (hOf M V h) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h)))
    [((Tim79a.xOf V (hOf M V h)).subgroupOf (kOf V (hOf M V h))).Normal]
    [hmod : Module (ZMod 2) (SecMod hs)] {φ : SecMod hs →ₗ[ZMod 2] SecMod hs}
    (hφ_equiv : ∀ (s : SL(2, F)) (v : SecMod hs),
      φ (repSec hs hs.comm SL(2, F) ψ s v) = repSec hs hs.comm SL(2, F) ψ s (φ v)) :
    ∃ r : ℕ,
      Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
          ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) =
        Fintype.card F ^ r * Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
          ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓
            LinearMap.ker (φ - LinearMap.id)) ∧
      Fintype.card F ^ r = Nat.card V ^ (2 * r) := by
  let A : Subgroup SL(2, F) := (imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom
  have hP2 : (∀ a ∈ A, a * a = 1) ∧ Nat.card A = Fintype.card F := by
    have h1 := hSh.map_imgK_conj_sylow hroot ψ (x := 1) (hOf M V h).one_mem
    simpa only [A, conjSubgroup_one] using h1
  have hFcard : Fintype.card F = Nat.card V ^ 2 := by
    rw [hl, hw.card_V, ← pow_mul]
    congr 1
    omega
  obtain ⟨r, hr⟩ := Sec2.IsNatSumModule.exists_card_fixedSub_eq
    (hσ := hw.natSum hs hmod) hP2.1 hP2.2 φ hφ_equiv
  exact ⟨r, hr, by rw [hFcard, ← pow_mul]⟩

private theorem fixedSub_le_ker_of_card_eq {h : G}
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {ψ : HBar V (hOf M V h) ≃* SL(2, F)}
    (hs : QuotMod.Hyp (hOf M V h) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h)))
    [((Tim79a.xOf V (hOf M V h)).subgroupOf (kOf V (hOf M V h))).Normal]
    [Module (ZMod 2) (SecMod hs)] {φ : SecMod hs →ₗ[ZMod 2] SecMod hs} {r : ℕ}
    (hr : Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) =
      Fintype.card F ^ r * Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓ LinearMap.ker (φ - LinearMap.id)))
    (hFpow : Fintype.card F ^ r = Nat.card V ^ (2 * r)) (hr0 : r = 0) :
    fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ≤
      LinearMap.ker (φ - LinearMap.id) := by
  have hcard : Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓
          LinearMap.ker (φ - LinearMap.id)) =
      Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) := by
    have h : Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
          ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom)) =
        Nat.card ↥(fixedSub (repSec hs hs.comm SL(2, F) ψ)
          ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓
            LinearMap.ker (φ - LinearMap.id)) := by
      simpa only [hr0, hFpow, Nat.mul_zero, pow_zero, one_mul] using hr
    exact h.symm
  have hker_eq : fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓
          LinearMap.ker (φ - LinearMap.id) =
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) := by
    apply SetLike.coe_injective
    exact Set.Finite.eq_of_subset_of_card_le
      (s := ((fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) ⊓ LinearMap.ker (φ - LinearMap.id) :
          Submodule (ZMod 2) (SecMod hs)) : Set (SecMod hs)))
      (t := ((fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V (hOf M V h) (Pc M V)).map ψ.toMonoidHom) :
          Submodule (ZMod 2) (SecMod hs)) : Set (SecMod hs)))
      (Set.toFinite _) (fun x hx => hx.1) (le_of_eq hcard.symm)
  rw [← hker_eq]
  exact inf_le_right

private theorem exists_nontrivial_mem_trivial_or_card_inf_le (hS : Sec5Hyp M V)
    {g h : G} (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hleh : ⁅Pc M V, conjSubgroup h V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    (hKF : ∀ u ∈ conjSubgroup g V,
      (∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h)) ∧
        u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G)) :
    ∃ u ∈ conjSubgroup g V, u ≠ 1 ∧
      ((∀ k ∈ Pc M V ⊓ kOf V (hOf M V h), ⁅u, k⁆ ∈ Tim79a.xOf V (hOf M V h)) ∨
        (Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ⊓
            (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) * Nat.card V ^ 2 ≤
          Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)))) := by
  classical
  have hroot := hS.toRootHyp
  have hSh := hS.shape hh
  have hne : conjSubgroup g V ≠ ⊥ := by
    intro hbot
    apply hroot.toHyp.ne_bot
    have h := congrArg (conjSubgroup g⁻¹) hbot
    simpa [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, conjSubgroup_one,
      conjSubgroup_bot] using h
  obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hHu : ∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h) := (hKF u huU).1
  have huW : u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G) := (hKF u huU).2
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hSh.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW_le_K : Tim79a.xOf V (hOf M V h) ≤ kOf V (hOf M V h) :=
    hroot.xOf_le_kOf hSh.Pc_le hSh.le_pCore
  have hs : QuotMod.Hyp (hOf M V h) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h)) :=
    hSh.quotModHyp hroot
  obtain ⟨huN_K, huN_W⟩ := normalizer_kOf_xOf_of_commutator_mem hHu huW
  have huNK : ∀ n ∈ kOf V (hOf M V h), u * n * u⁻¹ ∈ kOf V (hOf M V h) := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp huN_K n).mp hn
  have huNW : ∀ n ∈ Tim79a.xOf V (hOf M V h), u * n * u⁻¹ ∈ Tim79a.xOf V (hOf M V h) :=
    fun n hn => (Subgroup.mem_normalizer_iff.mp huN_W n).mp hn
  let hsu : QuotMod.Hyp (Subgroup.zpowers u) (kOf V (hOf M V h)) (Tim79a.xOf V (hOf M V h)) :=
    zpowersQuotModHyp hs huN_K huN_W
  haveI hnorm : ((Tim79a.xOf V (hOf M V h)).subgroupOf (kOf V (hOf M V h))).Normal := hs.normal
  have hmod : Module (ZMod 2) (SecMod hs) := SecMod.module hs hw.sq_mem
  letI := hmod
  let φ : SecMod hs →ₗ[ZMod 2] SecMod hs := conjQLinearMap hs hsu
  have hφmk : ∀ n : ↥(kOf V (hOf M V h)), φ (SecMod.mk hs n) =
      SecMod.mk hs ⟨u * (n : G) * u⁻¹, huNK n n.2⟩ :=
    conjQLinearMap_mk hs hsu huNK
  have hφ_equiv := repSec_comp_conj (F := F) (ψ := ψ) (hs := hs) (hHu := hHu)
    (huNK := huNK) (hφmk := hφmk)
  obtain ⟨r, hr, hFpow⟩ :=
    exists_card_fixedSub_eq_of_fixed (h := h) hroot hSh hw hs hφ_equiv
  by_cases hr0 : r = 0
  · refine ⟨u, huU, hu1', Or.inl ?_⟩
    exact commutator_mem_xOf_of_fixedSub_le_ker (hroot := hroot) (hSh := hSh) (hw := hw)
      (hs := hs) (huNK := huNK) (hφmk := hφmk)
      (hfix := fixedSub_le_ker_of_card_eq (h := h) hs hr hFpow hr0)
  · refine ⟨u, huU, hu1', Or.inr ?_⟩
    exact card_inf_le_of_one_le (hS := hS) (hh := hh) (hroot := hroot)
      (hSh := hSh) (hw := hw) (hs := hs) (huU := huU) (huW := huW)
      (huNK := huNK) (hφmk := hφmk) (hleh := hleh) (hr := hr) (hFpow := hFpow)
      (hr1 := Nat.pos_of_ne_zero hr0)

private theorem centralizer_le_of_commutator_mem_xOf (hS : Sec5Hyp M V)
    {g h : G} (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hF₀ : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) = V)
    {u : G} (huU : u ∈ conjSubgroup g V) (hu1 : u ≠ 1)
    (hcase : ∀ k ∈ Pc M V ⊓ kOf V (hOf M V h), ⁅u, k⁆ ∈ Tim79a.xOf V (hOf M V h)) :
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) := by
  classical
  have hroot := hS.toRootHyp
  let P : Subgroup G := Pc M V
  let Cg : Subgroup G := P ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)
  let Ch : Subgroup G := P ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)
  let Eg : Subgroup G := ⁅P, conjSubgroup g V⁆
  let Eh : Subgroup G := ⁅P, conjSubgroup h V⁆
  have hSh := hS.shape hh
  obtain ⟨gh, yh, hShg, hyhH, hUeqh, hVyh, hyhV, hEh, hChK, hChCE⟩ := hS.exists_sigma_data hh
  have hPgh : conjSubgroup gh (Pc M V) = conjSubgroup h (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqh.symm
  have hhOf : hOf M V gh = hOf M V h := by
    unfold hOf
    rw [hPgh]
  have hCh_eq : Ch = P ⊓ kOf V (hOf M V h) := by
    change Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h)
    rw [hChK, hhOf]
  obtain ⟨gg, yg, hShg', hygH, hUeqg, hVyg, hygV, hEgg, hCgg, hCggCE⟩ := hS.exists_sigma_data hg
  have hPgg : conjSubgroup gg (Pc M V) = conjSubgroup g (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqg.symm
  have hggOf : hOf M V gg = hOf M V g := by
    unfold hOf
    rw [hPgg]
  have hCg_eq : Cg = P ⊓ kOf V (hOf M V g) := by
    change Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
      Pc M V ⊓ kOf V (hOf M V g)
    rw [hCgg, hggOf]
  have hEg_eq : Eg = Pc M V ⊓ Tim79a.xOf V (hOf M V g) := by
    change ⁅Pc M V, conjSubgroup g V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V g)
    rw [hEgg, hggOf]
  have hEh_eq : Eh = Pc M V ⊓ Tim79a.xOf V (hOf M V h) := by
    change ⁅Pc M V, conjSubgroup h V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V h)
    rw [hEh, hhOf]
  have hEgW : ⁅Pc M V, conjSubgroup g V⁆ ⊓ Tim79a.xOf V (hOf M V h) = V := by
    have h1 : Eg ⊓ Tim79a.xOf V (hOf M V h) = Eg ⊓ Eh := by
      rw [hEg_eq, hEh_eq]
      rw [← inf_assoc,
        inf_eq_left.mpr (inf_le_left : Pc M V ⊓ Tim79a.xOf V (hOf M V g) ≤ Pc M V)]
    rw [h1, hF₀]
  intro c hc
  have hc' : c ∈ Pc M V ⊓ kOf V (hOf M V h) := hCh_eq ▸ hc
  have hcP : c ∈ Pc M V := hc'.1
  have hucW : ⁅u, c⁆ ∈ Tim79a.xOf V (hOf M V h) := hcase c hc'
  have hcuW : ⁅c, u⁆ ∈ Tim79a.xOf V (hOf M V h) := by
    rw [show ⁅c, u⁆ = ⁅u, c⁆⁻¹ from (commutatorElement_inv u c).symm]
    exact (Tim79a.xOf V (hOf M V h)).inv_mem hucW
  have hcuE : ⁅c, u⁆ ∈ ⁅Pc M V, conjSubgroup g V⁆ :=
    Subgroup.commutator_mem_commutator hcP huU
  have hcuV : ⁅c, u⁆ ∈ V := hEgW ▸ Subgroup.mem_inf.mpr ⟨hcuE, hcuW⟩
  have huUyg : u ∈ conjSubgroup yg V := hVyg ▸ (hUeqg ▸ huU)
  have hcK' : c ∈ kOf V (hOf M V gg) :=
    Sec45Shape.mem_kOf_of_commutator_mem hroot hShg' hygH hygV huUyg hu1 hcP hcuV
  rw [hggOf] at hcK'
  change c ∈ Cg
  rw [hCg_eq]
  exact Subgroup.mem_inf.mpr ⟨hcP, hcK'⟩

private theorem Pc_eq_sup_of_trivial (hS : Sec5Hyp M V)
    {g h : G} (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hF₀ : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) = V)
    {u : G} (huU : u ∈ conjSubgroup g V) (hu1 : u ≠ 1)
    (hcase : ∀ k ∈ Pc M V ⊓ kOf V (hOf M V h), ⁅u, k⁆ ∈ Tim79a.xOf V (hOf M V h)) :
    Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) := by
  classical
  have hroot := hS.toRootHyp
  let P : Subgroup G := Pc M V
  let Cg : Subgroup G := P ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)
  let Ch : Subgroup G := P ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)
  let Eg : Subgroup G := ⁅P, conjSubgroup g V⁆
  let Eh : Subgroup G := ⁅P, conjSubgroup h V⁆
  have hCgcard : Nat.card ↥Cg * Nat.card V ^ 2 = Nat.card ↥P := by
    simpa only [Cg, P] using hS.card_Pc_inf_centralizer hg
  have hChcard : Nat.card ↥Ch * Nat.card V ^ 2 = Nat.card ↥P := by
    simpa only [Ch, P] using hS.card_Pc_inf_centralizer hh
  have hSh := hS.shape hh
  obtain ⟨gh, yh, hShg, hyhH, hUeqh, hVyh, hyhV, hEh, hChK, hChCE⟩ := hS.exists_sigma_data hh
  have hPgh : conjSubgroup gh (Pc M V) = conjSubgroup h (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqh.symm
  have hhOf : hOf M V gh = hOf M V h := by
    unfold hOf
    rw [hPgh]
  have hCh_eq : Ch = P ⊓ kOf V (hOf M V h) := by
    change Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h)
    rw [hChK, hhOf]
  have hCh_le_Cg : Ch ≤ Cg :=
    centralizer_le_of_commutator_mem_xOf hS hg hh hF₀ huU hu1 hcase
  have hCh_eq_Cg : Ch = Cg := by
    refine Subgroup.eq_of_le_of_card_ge hCh_le_Cg ?_
    have hq2 : 0 < Nat.card V ^ 2 := pow_pos Nat.card_pos 2
    refine Nat.le_of_mul_le_mul_right ?_ hq2
    rw [hCgcard, hChcard]
  obtain ⟨gg, yg, hShg', hygH, hUeqg, hVyg, hygV, hEgg, hCgg, hCggCE⟩ := hS.exists_sigma_data hg
  have hPgg : conjSubgroup gg (Pc M V) = conjSubgroup g (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqg.symm
  have hggOf : hOf M V gg = hOf M V g := by
    unfold hOf
    rw [hPgg]
  have hCg_eq : Cg = P ⊓ kOf V (hOf M V g) := by
    change Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
      Pc M V ⊓ kOf V (hOf M V g)
    rw [hCgg, hggOf]
  have hEg_eq : Eg = Pc M V ⊓ Tim79a.xOf V (hOf M V g) := by
    change ⁅Pc M V, conjSubgroup g V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V g)
    rw [hEgg, hggOf]
  have hEh_eq : Eh = Pc M V ⊓ Tim79a.xOf V (hOf M V h) := by
    change ⁅Pc M V, conjSubgroup h V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V h)
    rw [hEh, hhOf]
  obtain ⟨Fg, hFg, hFg2, hFg3, lg, hlg, ψg, hwg⟩ := hShg'.shape
  obtain ⟨Fh, hFh, hFh2, hFh3, lh, hlh, ψh, hwh⟩ := hSh.shape
  have hcenter_g := hwg.center_PK
  rw [hggOf] at hcenter_g
  have hcenter_h := hwh.center_PK
  have hcenter_g' : Cg ⊓ Subgroup.centralizer (Cg : Set G) = Eg := by
    rw [hCg_eq, hEg_eq]
    exact hcenter_g
  have hcenter_h' : Ch ⊓ Subgroup.centralizer (Ch : Set G) = Eh := by
    rw [hCh_eq, hEh_eq]
    exact hcenter_h
  have hEg_eq_Eh : Eg = Eh := by
    calc Eg = Cg ⊓ Subgroup.centralizer (Cg : Set G) := hcenter_g'.symm
      _ = Ch ⊓ Subgroup.centralizer (Ch : Set G) := by rw [hCh_eq_Cg]
      _ = Eh := hcenter_h'
  have hEgV : Eg = V := by
    have h : Eg ⊓ Eh = V := hF₀
    rw [hEg_eq_Eh, inf_idem] at h
    exact hEg_eq_Eh.trans h
  have hEgV' : ⁅Pc M V, conjSubgroup g V⁆ = V := hEgV
  have hcard : Nat.card V ^ 3 = Nat.card V ^ 1 := by
    rw [pow_one, ← hS.card_commutator_Pc hg, hEgV']
  have hq : 1 < Nat.card V := by
    have h4 := hroot.four_le_card
    omega
  have h31 : 3 = 1 := Nat.pow_right_injective hq hcard
  omega

private theorem Pc_eq_sup_of_card_inf (hS : Sec5Hyp M V)
    {g h : G} (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hcase : Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ⊓
        (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) * Nat.card V ^ 2 ≤
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) :
    Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) := by
  classical
  have hroot := hS.toRootHyp
  let P : Subgroup G := Pc M V
  let Cg : Subgroup G := P ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)
  let Ch : Subgroup G := P ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)
  have hCgP : Cg ≤ P := inf_le_left
  have hChP : Ch ≤ P := inf_le_left
  have hCgcard : Nat.card ↥Cg * Nat.card V ^ 2 = Nat.card ↥P := by
    simpa only [Cg, P] using hS.card_Pc_inf_centralizer hg
  have hChcard : Nat.card ↥Ch * Nat.card V ^ 2 = Nat.card ↥P := by
    simpa only [Ch, P] using hS.card_Pc_inf_centralizer hh
  have hSh := hS.shape hh
  obtain ⟨gh, yh, hShg, hyhH, hUeqh, hVyh, hyhV, hEh, hChK, hChCE⟩ := hS.exists_sigma_data hh
  have hPgh : conjSubgroup gh (Pc M V) = conjSubgroup h (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hUeqh.symm
  have hhOf : hOf M V gh = hOf M V h := by
    unfold hOf
    rw [hPgh]
  have hCh_eq : Ch = P ⊓ kOf V (hOf M V h) := by
    change Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h)
    rw [hChK, hhOf]
  have hforward : ∀ x ∈ Cg, ∀ y ∈ Ch, x * y * x⁻¹ ∈ Ch := by
    intro x hx y hy
    rw [hCh_eq] at hy ⊢
    exact Subgroup.mem_inf.mpr
      ⟨P.mul_mem (P.mul_mem (hCgP hx) hy.1) (P.inv_mem (hCgP hx)),
        (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_kOf V (hOf M V h) (hSh.Pc_le (hCgP hx))) y).mp hy.2⟩
  have hnorm : Cg ≤ Subgroup.normalizer (Ch : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨hforward x hx y, fun hy => by
      have h := hforward x⁻¹ (Cg.inv_mem hx) (x * y * x⁻¹) hy
      simpa [mul_assoc] using h⟩
  have hcase' : Nat.card ↥(Cg ⊓ Ch) * Nat.card V ^ 2 ≤ Nat.card ↥Ch := by
    simpa only [Cg, Ch, P] using hcase
  have hcard_sup' : Nat.card ↥(Cg ⊔ Ch) * Nat.card ↥(Cg ⊓ Ch) =
      Nat.card ↥Cg * Nat.card ↥Ch :=
    CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hnorm
  have hcard_sup : Nat.card ↥(Ch ⊔ Cg) * Nat.card ↥(Ch ⊓ Cg) =
      Nat.card ↥Ch * Nat.card ↥Cg := by
    rw [sup_comm, inf_comm, hcard_sup', Nat.mul_comm]
  have hP_le : Nat.card ↥P ≤ Nat.card ↥(Ch ⊔ Cg) := by
    have h1 : Nat.card ↥(Ch ⊔ Cg) * (Nat.card ↥(Cg ⊓ Ch) * Nat.card V ^ 2) =
        Nat.card ↥Ch * Nat.card ↥P := by
      calc Nat.card ↥(Ch ⊔ Cg) * (Nat.card ↥(Cg ⊓ Ch) * Nat.card V ^ 2)
          = (Nat.card ↥(Ch ⊔ Cg) * Nat.card ↥(Ch ⊓ Cg)) * Nat.card V ^ 2 := by
              rw [inf_comm]
              ring
        _ = (Nat.card ↥Ch * Nat.card ↥Cg) * Nat.card V ^ 2 := by rw [hcard_sup]
        _ = Nat.card ↥Ch * (Nat.card ↥Cg * Nat.card V ^ 2) := by ring
        _ = Nat.card ↥Ch * Nat.card ↥P := by rw [hCgcard]
    have h2 : Nat.card ↥(Ch ⊔ Cg) * (Nat.card ↥(Cg ⊓ Ch) * Nat.card V ^ 2) ≤
        Nat.card ↥(Ch ⊔ Cg) * Nat.card ↥Ch := Nat.mul_le_mul_left _ hcase'
    rw [h1, mul_comm (Nat.card ↥(Ch ⊔ Cg)) (Nat.card ↥Ch)] at h2
    exact Nat.le_of_mul_le_mul_left h2 Nat.card_pos
  have hle : Ch ⊔ Cg ≤ P := sup_le hChP hCgP
  have heq : Ch ⊔ Cg = P := Subgroup.eq_of_le_of_card_ge hle hP_le
  change P = Cg ⊔ Ch
  rw [← heq, sup_comm]

private theorem Pc_eq_sup_of_trivial_or_card (hS : Sec5Hyp M V)
    {g h : G} (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hF₀ : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) = V)
    {u : G} (huU : u ∈ conjSubgroup g V) (hu1 : u ≠ 1)
    (hcase : (∀ k ∈ Pc M V ⊓ kOf V (hOf M V h), ⁅u, k⁆ ∈ Tim79a.xOf V (hOf M V h)) ∨
      (Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ⊓
          (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))) * Nat.card V ^ 2 ≤
        Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)))) :
    Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) := by
  rcases hcase with hcase | hcase
  · exact Pc_eq_sup_of_trivial hS hg hh hF₀ huU hu1 hcase
  · exact Pc_eq_sup_of_card_inf hS hg hh hcase

theorem Pc_eq_sup_centralizer_of_inf_eq_V (hS : Sec5Hyp M V)
    {g h : G} (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hleh : ⁅Pc M V, conjSubgroup h V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    (hKF : ∀ u ∈ conjSubgroup g V,
      (∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h)) ∧
        u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G))
    (hF₀ : (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) = V) :
    Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) := by
  obtain ⟨u, huU, hu1, hcase⟩ :=
    exists_nontrivial_mem_trivial_or_card_inf_le hS hh hleh hKF
  exact Pc_eq_sup_of_trivial_or_card hS hg hh hF₀ huU hu1 hcase

end Sec5Hyp

end CFSG.RankThree.GF2n.Tim81

end
