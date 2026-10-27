module

public import CFSG.Quasithin.Background.C1PackSL2
public import CFSG.Quasithin.Background.E2SolvStruct
public import CFSG.Quasithin.Background.G6PGroup
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.Quasithin.Background.C1GNDefs
import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
open scoped commutatorElement
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem exists_single_block {P S MP V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : MinParabolic P S MP) (hsolv : Group.IsSolvable ↥P)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p P ≤ 2) (hred : IsTwoReducedIn P V)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (V : Set G)) (hS : baum S = S) :
    ∃ L : Subgroup (MulAut (IntMod V hV)), autI hV P = L ∧ ActsAsNaturalL2 L (commV L) := by
  classical
  obtain ⟨hKJ, I, hcard, hJeq, hcomm, hind, htrans, hnat, -, -, -⟩ :=
    E2_3_one_of_isSolvable hV h hsolv hSQT hred hJ
  obtain ⟨hSb, -⟩ := E2_3_two_sylow_of_isSolvable hV h hsolv hSQT hred hJ
  rw [hS] at hSb
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hSP : S ≤ P := h.isSylow.1
  have hSJ : autI hV S ≤ ⨆ L ∈ I, L :=
    hSb ▸ ((autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans hJeq.le)
  have hLne : ∀ L ∈ I, L ≠ ⊥ := by
    intro L hL hL0
    obtain ⟨e, -, -⟩ := hnat L hL
    have h1 : Nat.card ↥L = Nat.card SL2F2 := Nat.card_congr e.toEquiv
    rw [hL0, Subgroup.card_bot, card_sl2F2] at h1
    omega
  have hI : ∃ L, I = {L} := by
    rcases hcard with h1 | h2
    · exact Finset.card_eq_one.1 h1
    · exfalso
      obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.1 h2
      have hm₁ : L₁ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))) := by simp
      have hm₂ : L₂ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))) := by simp
      obtain ⟨t, ht1, ht2⟩ := htrans L₁ hm₁ L₂ hm₂
      have hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := hcomm L₁ hm₁ L₂ hm₂ hne
      have hsup2 : (⨆ L ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))), L) = L₁ ⊔ L₂ := by
        apply le_antisymm
        · refine iSup₂_le fun L hL => ?_
          rcases Finset.mem_insert.1 hL with rfl | hL
          · exact le_sup_left
          · rw [Finset.mem_singleton.1 hL]
            exact le_sup_right
        · exact sup_le (le_iSup₂_of_le L₁ hm₁ le_rfl) (le_iSup₂_of_le L₂ hm₂ le_rfl)
      have htsup : t ∈ L₁ ⊔ L₂ := hsup2 ▸ hSJ ht1
      have hxfix : ∀ a ∈ L₁, ∀ y ∈ L₂, a * y * a⁻¹ = y := fun a ha y hy => by
        rw [hc a ha y hy, mul_inv_cancel_right]
      have hnormL₂ : L₁ ≤ Subgroup.normalizer (L₂ : Set (MulAut (IntMod V hV))) := fun a ha => by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hxL
          rwa [hxfix a ha x hxL]
        · intro hxL
          have h1 := hxfix a⁻¹ (L₁.inv_mem ha) _ hxL
          have h2 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
          rw [h2] at h1
          rw [h1]
          exact hxL
      obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hnormL₂).1 htsup
      have hinf : L₁ ⊓ L₂ = ⊥ := by
        refine le_bot_iff.1 ((inf_le_inf_left L₁ ?_).trans (hind L₁ hm₁).le)
        exact le_iSup₂_of_le L₂ hm₂ (le_iSup (fun _ : L₂ ≠ L₁ => L₂) hne.symm)
      apply hLne L₂ hm₂
      rw [eq_bot_iff]
      intro x hx
      have h1 : x ∈ B1.conjAut (a * b) L₁ := ht2 ▸ hx
      rw [B1.mem_conjAut] at h1
      have h2 : (a * b)⁻¹ * x * (a * b) ∈ L₂ := by
        have h3 : (a * b)⁻¹ * x * (a * b) = b⁻¹ * x * b := by
          have h4 := hxfix a⁻¹ (L₁.inv_mem ha) x hx
          calc (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
            _ = b⁻¹ * x * b := by
              have : a⁻¹ * x * a = x := by simpa using h4
              rw [this]
        rw [h3]
        exact L₂.mul_mem (L₂.mul_mem (L₂.inv_mem hb) hx) hb
      have h5 : (a * b)⁻¹ * x * (a * b) ∈ L₁ ⊓ L₂ := ⟨h1, h2⟩
      rw [hinf, Subgroup.mem_bot] at h5
      have : x = 1 := by
        have h6 : x = (a * b) * ((a * b)⁻¹ * x * (a * b)) * (a * b)⁻¹ := by group
        rw [h6, h5]
        group
      exact (Subgroup.mem_bot).2 this
  obtain ⟨L, rfl⟩ := hI
  refine ⟨L, ?_, hnat L (Finset.mem_singleton_self L)⟩
  have hJL : autI hV (thompsonJ P) = L := by simpa using hJeq
  apply le_antisymm
  · rw [← sup_twoResidual_eq h.isSylow,
      autI_sup hV (hSP.trans hPN) ((twoResidual_le P).trans hPN)]
    refine sup_le ?_ ?_
    · rw [hSb]
      exact (autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans hJL.le
    · exact (autI_mono hV hKJ).trans hJL.le
  · rw [← hJL]
    exact autI_mono hV (B6.thompsonJ_le P)

theorem fittingSubgroup_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.fittingSubgroup A).map e.toMonoidHom = CFSG.fittingSubgroup B :=
  CFSG.WholeGroup.fittingSubgroup_map_mulEquiv e

theorem generalizedFitting_eq_fittingSubgroup_of_isSolvable {A : Type*} [Group A]
    [Group.IsSolvable A] : CFSG.generalizedFitting A = CFSG.fittingSubgroup A :=
  CFSG.WholeGroup.generalizedFitting_eq_fittingSubgroup_of_isSolvable

theorem generalizedFitting_map_sl2 {A : Type*} [Group A] (ι : A ≃* SL2F2) :
    (CFSG.generalizedFitting A).map ι.toMonoidHom = commutator SL2F2 := by
  have : Group.IsSolvable A := Group.isSolvable_of_surjective (f := ι.symm.toMonoidHom) ι.symm.surjective
  rw [generalizedFitting_eq_fittingSubgroup_of_isSolvable, fittingSubgroup_map_mulEquiv,
    ← generalizedFitting_eq_fittingSubgroup_of_isSolvable, generalizedFitting_sl2]

omit [Finite G] in
theorem mem_fstarPre_iff {P V : Subgroup G} (hPN : P ≤ Subgroup.normalizer (V : Set G))
    (ι : ↥(autOn P V) ≃* SL2F2) {g : G} (hg : g ∈ P) :
    g ∈ fstarPre P V ↔
      ι ⟨conjAct V ⟨g, hPN hg⟩, ⟨⟨g, hPN hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩⟩ ∈
        commutator SL2F2 := by
  have hF := generalizedFitting_map_sl2 ι
  have hiff : ∀ y : ↥(autOn P V),
      y ∈ CFSG.generalizedFitting ↥(autOn P V) ↔ ι y ∈ commutator SL2F2 := fun y => by
    rw [← hF]
    exact (Subgroup.mem_map_iff_mem (f := ι.toMonoidHom) ι.injective).symm
  unfold fstarPre
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨-, n, hn, hng⟩
    obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.1 hn
    have hn' : n = ⟨g, hPN hg⟩ := Subtype.ext hng
    subst hn'
    have : y = ⟨conjAct V ⟨g, hPN hg⟩, ⟨⟨g, hPN hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩⟩ :=
      Subtype.ext hyn
    rw [← this]
    exact (hiff y).1 hy
  · intro h
    refine ⟨hg, ⟨g, hPN hg⟩, ?_, rfl⟩
    refine Subgroup.mem_map.2 ⟨⟨conjAct V ⟨g, hPN hg⟩,
      ⟨⟨g, hPN hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩⟩, (hiff _).2 h, rfl⟩

omit [Finite G] in
theorem isNatL2Section_fstarPre {P V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hPN : P ≤ Subgroup.normalizer (V : Set G))
    {L : Subgroup (MulAut (IntMod V hV))} (hL : autI hV P = L)
    (hnat : ActsAsNaturalL2 L (commV L)) :
    IsNatL2Section (fstarPre P V) (Subgroup.centralizer (V : Set G)) ⁅V, fstarPre P V⁆
      (⁅V, fstarPre P V⁆ ⊓ Subgroup.centralizer (fstarPre P V : Set G)) 1 ∧
    twoResidual P ≤ fstarPre P V ∧
    ∀ K J : Subgroup G, K ≤ fstarPre P V → J ≤ P → ¬ K ≤ Subgroup.centralizer (V : Set G) →
      (∃ a ∈ J, a ^ 2 = 1 ∧ a ∉ Subgroup.centralizer (V : Set G)) →
      ¬ ⁅K, J⁆ ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨e, φ, hφ⟩ := hnat
  let ι' : ↥(autI hV P) ≃* SL2F2 := (MulEquiv.subgroupCongr hL).trans e
  let ι : ↥(autOn P V) ≃* SL2F2 := ι'
  let ε₀ : ↥P →* ↥(autOn P V) :=
    ((conjAct V).comp (Subgroup.inclusion hPN)).codRestrict (autOn P V)
      (fun g => ⟨⟨g, hPN g.2⟩, Subgroup.mem_subgroupOf.2 g.2, rfl⟩)
  let ε : ↥P →* SL2F2 := ι.toMonoidHom.comp ε₀
  let hP : ↥P → ↥L := fun g => ⟨convI hV ⟨g, hPN g.2⟩, by
    rw [← hL]
    exact convI_mem_autI hV g.2 (hPN g.2)⟩
  have hεmat : ∀ g : ↥P, ε g = e (hP g) := fun g => rfl
  have hεker : ∀ g : ↥P, ε g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro g
    rw [hεmat, MulEquiv.map_eq_one_iff]
    have h1 : hP g = 1 ↔ convI hV ⟨g, hPN g.2⟩ = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1]
    exact convI_eq_one_iff hV ⟨g, hPN g.2⟩
  have hεsurj : Function.Surjective ε := by
    intro s
    have hx : (e.symm s : MulAut (IntMod V hV)) ∈ autI hV P := by
      rw [hL]
      exact (e.symm s).2
    obtain ⟨g, hgP, hg⟩ := (mem_autI hV).1 hx
    refine ⟨⟨g, hgP⟩, ?_⟩
    rw [hεmat]
    have : hP ⟨g, hgP⟩ = e.symm s := Subtype.ext hg
    rw [this]
    exact e.apply_symm_apply s
  have hKP : fstarPre P V ≤ P := inf_le_left
  have hKiff : ∀ g : ↥P, (g : G) ∈ fstarPre P V ↔ ε g ∈ commutator SL2F2 := fun g =>
    mem_fstarPre_iff hPN ι g.2
  let α : ↥(fstarPre P V) →* SL2F2 := ε.comp (Subgroup.inclusion hKP)
  have hker : α.ker = (Subgroup.centralizer (V : Set G)).subgroupOf (fstarPre P V) := by
    ext k
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hεker ⟨k, hKP k.2⟩
  have hrange : α.range = commutator SL2F2 := by
    ext s
    constructor
    · rintro ⟨k, rfl⟩
      exact (hKiff ⟨k, hKP k.2⟩).1 k.2
    · intro hs
      obtain ⟨g, rfl⟩ := hεsurj s
      exact ⟨⟨g, (hKiff g).2 hs⟩, rfl⟩
  obtain ⟨s, hs3, hs1⟩ : ∃ s : SL2F2, s ^ 3 = 1 ∧ s ≠ 1 := by decide
  have hscomm : s ∈ commutator SL2F2 := by
    rw [commutator_sl2_eq]
    exact mem_sl2A3.2 hs3
  obtain ⟨k₀, hk₀⟩ : s ∈ α.range := hrange ▸ hscomm
  have hKN : fstarPre P V ≤ Subgroup.normalizer (V : Set G) := hKP.trans hPN
  have hW1V : ⁅V, fstarPre P V⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hKN
  have hW1sub : ∀ x ∈ ⁅V, fstarPre P V⁆, ∃ hxV : x ∈ V, IntMod.mk hV ⟨x, hxV⟩ ∈ commV L := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v, hv, k, hk, rfl⟩ := hx
      have hxV : ⁅v, k⁆ ∈ V := hW1V (Subgroup.commutator_mem_commutator hv hk)
      refine ⟨hxV, ?_⟩
      have hσ : (hP ⟨k, hKP hk⟩ : MulAut (IntMod V hV)) ∈ L := (hP ⟨k, hKP hk⟩).2
      have h2 := (commV L).inv_mem (G6.mem_commV_of_mem hσ (IntMod.mk hV ⟨v, hv⟩))
      have heq : IntMod.mk hV ⟨⁅v, k⁆, hxV⟩ =
          ((hP ⟨k, hKP hk⟩ : MulAut (IntMod V hV)) (IntMod.mk hV ⟨v, hv⟩) *
            (IntMod.mk hV ⟨v, hv⟩)⁻¹)⁻¹ := by
        apply IntMod.val_injective
        show ⁅v, k⁆ = _
        rw [IntMod.val_inv, IntMod.val_mul, IntMod.val_inv]
        show _ = ((k * v * k⁻¹) * v⁻¹)⁻¹
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact h2
    | one =>
      refine ⟨V.one_mem, ?_⟩
      have : IntMod.mk hV ⟨(1 : G), V.one_mem⟩ = 1 := IntMod.val_injective rfl
      rw [this]
      exact (commV L).one_mem
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxV, hx⟩ := ihx
      obtain ⟨hyV, hy⟩ := ihy
      refine ⟨V.mul_mem hxV hyV, ?_⟩
      have : IntMod.mk hV ⟨x * y, V.mul_mem hxV hyV⟩ =
          IntMod.mk hV ⟨x, hxV⟩ * IntMod.mk hV ⟨y, hyV⟩ := IntMod.val_injective rfl
      rw [this]
      exact (commV L).mul_mem hx hy
    | inv x _ ih =>
      obtain ⟨hxV, hx⟩ := ih
      refine ⟨V.inv_mem hxV, ?_⟩
      have : IntMod.mk hV ⟨x⁻¹, V.inv_mem hxV⟩ = (IntMod.mk hV ⟨x, hxV⟩)⁻¹ :=
        IntMod.val_injective rfl
      rw [this]
      exact (commV L).inv_mem hx
  let incl : ↥⁅V, fstarPre P V⁆ →* ↥(commV L) :=
    { toFun := fun w => ⟨IntMod.mk hV ⟨w.1, (hW1sub w.1 w.2).1⟩, (hW1sub w.1 w.2).2⟩
      map_one' := Subtype.ext (IntMod.val_injective rfl)
      map_mul' := fun a b => Subtype.ext (IntMod.val_injective rfl) }
  have hincl_val : ∀ w : ↥⁅V, fstarPre P V⁆, (incl w : IntMod V hV).val = (w : G) := fun w => rfl
  have hincl_inj : Function.Injective incl := fun a b h =>
    Subtype.ext (by
      have := congrArg (fun x : ↥(commV L) => (x : IntMod V hV).val) h
      simpa [hincl_val] using this)
  let β : ↥⁅V, fstarPre P V⁆ →* Multiplicative (Fin 2 → ZMod 2) := φ.toMonoidHom.comp incl
  have hβinj : Function.Injective β := φ.injective.comp hincl_inj
  have hnormL : ∀ x : ↥L, ∀ y : MulAut (IntMod V hV), y ∈ L → (x : MulAut (IntMod V hV)) * y *
      (x : MulAut (IntMod V hV))⁻¹ ∈ L := fun x y hy => L.mul_mem (L.mul_mem x.2 hy) (L.inv_mem x.2)
  have hEQ : ∀ (k : ↥(fstarPre P V)) (u v : ↥⁅V, fstarPre P V⁆),
      (v : G) = (k : G) * (u : G) * (k : G)⁻¹ →
      Multiplicative.toAdd (β v) =
        (α k : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u) := by
    intro k u v hv
    have hu : ((hP ⟨k, hKP k.2⟩ : ↥L) : MulAut (IntMod V hV)) (incl u : IntMod V hV) ∈ commV L :=
      G6.apply_mem_commV (hnormL _) (incl u).2
    have hv' : incl v = ⟨((hP ⟨k, hKP k.2⟩ : ↥L) : MulAut (IntMod V hV)) (incl u : IntMod V hV), hu⟩ := by
      apply Subtype.ext
      apply IntMod.val_injective
      show (v : G) = _
      rw [hv]
      show _ = ((convI hV ⟨(k : G), hKN k.2⟩) (incl u : IntMod V hV)).val
      rw [convI_apply_val]
      rfl
    show Multiplicative.toAdd (φ (incl v)) = _
    rw [hv', hφ (hP ⟨k, hKP k.2⟩) (incl u) hu]
    rfl
  have hβsurj : Function.Surjective β := by
    intro x
    obtain ⟨y, hy⟩ := sl2_exists_sub_eq s hs3 hs1 (Multiplicative.toAdd x)
    set u₀ : ↥(commV L) := φ.symm (Multiplicative.ofAdd y) with hu₀
    have hu : ((hP ⟨k₀, hKP k₀.2⟩ : ↥L) : MulAut (IntMod V hV)) (u₀ : IntMod V hV) ∈ commV L :=
      G6.apply_mem_commV (hnormL _) u₀.2
    have hu₀V : (u₀ : IntMod V hV).val ∈ V := (u₀ : IntMod V hV).val_mem
    have hw : ⁅(k₀ : G), (u₀ : IntMod V hV).val⁆ ∈ ⁅V, fstarPre P V⁆ := by
      have := Subgroup.commutator_mem_commutator k₀.2 hu₀V
      rwa [Subgroup.commutator_comm] at this
    refine ⟨⟨⁅(k₀ : G), (u₀ : IntMod V hV).val⁆, hw⟩, ?_⟩
    have hinclw : incl ⟨⁅(k₀ : G), (u₀ : IntMod V hV).val⁆, hw⟩ =
        ⟨((hP ⟨k₀, hKP k₀.2⟩ : ↥L) : MulAut (IntMod V hV)) (u₀ : IntMod V hV), hu⟩ * u₀⁻¹ := by
      apply Subtype.ext
      apply IntMod.val_injective
      show ⁅(k₀ : G), (u₀ : IntMod V hV).val⁆ = _
      rw [Subgroup.coe_mul, IntMod.val_mul, Subgroup.coe_inv, IntMod.val_inv]
      show _ = ((convI hV ⟨(k₀ : G), hKN k₀.2⟩) (u₀ : IntMod V hV)).val * _
      rw [convI_apply_val]
      simp only [commutatorElement_def]
    show φ (incl ⟨⁅(k₀ : G), (u₀ : IntMod V hV).val⁆, hw⟩) = x
    rw [hinclw, map_mul, hφ (hP ⟨k₀, hKP k₀.2⟩) u₀ hu, map_inv]
    have hφu : φ u₀ = Multiplicative.ofAdd y := φ.apply_symm_apply _
    have hes : ((e (hP ⟨k₀, hKP k₀.2⟩) : SL2F2) : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
        (s : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
      have : e (hP ⟨k₀, hKP k₀.2⟩) = s := hk₀
      rw [this]
    rw [hφu, hes]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    rw [sub_eq_add_neg] at hy
    exact hy
  have hβker : β.ker = (⁅V, fstarPre P V⁆ ⊓ Subgroup.centralizer (fstarPre P V : Set G)).subgroupOf
      ⁅V, fstarPre P V⁆ := by
    rw [(MonoidHom.ker_eq_bot_iff β).2 hβinj]
    symm
    rw [eq_bot_iff]
    intro w hw
    have hwC : (w : G) ∈ Subgroup.centralizer (fstarPre P V : Set G) :=
      (Subgroup.mem_subgroupOf.1 hw).2
    have hcomm : (w : G) = (k₀ : G) * (w : G) * (k₀ : G)⁻¹ := by
      have h1 := Subgroup.mem_centralizer_iff.1 hwC (k₀ : G) k₀.2
      calc (w : G) = (w : G) * (k₀ : G) * (k₀ : G)⁻¹ := by group
        _ = (k₀ : G) * (w : G) * (k₀ : G)⁻¹ := by rw [← h1]
    have hfix := hEQ k₀ w w hcomm
    rw [hk₀] at hfix
    have h0 := sl2_eq_zero_of_fixed s hs3 hs1 _ hfix.symm
    have h1 : β w = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using h0
    exact (Subgroup.mem_bot).2 (hβinj (by rw [h1, map_one]))
  refine ⟨⟨ZMod 2, inferInstance, inferInstance, by simp, α, hker, hrange, β, hβsurj, hβker, hEQ⟩,
    ?_, ?_⟩
  ·
    have key : ∀ x ∈ P, ∀ y ∈ fstarPre P V, x * y * x⁻¹ ∈ fstarPre P V := by
      intro x hx y hy
      have hxyP : x * y * x⁻¹ ∈ P := P.mul_mem (P.mul_mem hx (hKP hy)) (P.inv_mem hx)
      have h1 := (hKiff ⟨y, hKP hy⟩).1 hy
      refine (hKiff ⟨x * y * x⁻¹, hxyP⟩).2 ?_
      have h2 : ε ⟨x * y * x⁻¹, hxyP⟩ = ε ⟨x, hx⟩ * ε ⟨y, hKP hy⟩ * (ε ⟨x, hx⟩)⁻¹ := by
        rw [show (⟨x * y * x⁻¹, hxyP⟩ : ↥P) = ⟨x, hx⟩ * ⟨y, hKP hy⟩ * (⟨x, hx⟩ : ↥P)⁻¹ from rfl,
          map_mul, map_mul, map_inv]
      rw [h2]
      exact (inferInstance : (commutator SL2F2).Normal).conj_mem _ h1 _
    have hnormK : P ≤ Subgroup.normalizer (fstarPre P V : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => key x hx y hy, fun hy => ?_⟩
      have := key x⁻¹ (P.inv_mem hx) _ hy
      simpa [mul_assoc] using this
    refine twoResidual_le_of_isTwoQuotient hKP hnormK fun y hy => ⟨1, ?_⟩
    rw [pow_one]
    refine (hKiff ⟨y ^ 2, P.pow_mem hy 2⟩).2 ?_
    rw [show (⟨y ^ 2, P.pow_mem hy 2⟩ : ↥P) = (⟨y, hy⟩ : ↥P) ^ 2 from rfl, map_pow,
      commutator_sl2_eq]
    exact mem_sl2A3.2 (sl2_sq_pow_three _)
  · intro K J hKf hJP hK hJ hcomm
    obtain ⟨k, hkK, hkC⟩ := IsConcreteLE.not_le_iff_exists.1 hK
    obtain ⟨a, haJ, ha2, haC⟩ := hJ
    have hkP : k ∈ P := hKP (hKf hkK)
    have haP : a ∈ P := hJP haJ
    have h1 : ε ⟨k, hkP⟩ ≠ 1 := fun h => hkC ((hεker _).1 h)
    have h3 : (ε ⟨k, hkP⟩) ^ 3 = 1 := by
      have := (hKiff ⟨k, hkP⟩).1 (hKf hkK)
      rw [commutator_sl2_eq] at this
      exact mem_sl2A3.1 this
    have h4 : ε ⟨a, haP⟩ ≠ 1 := fun h => haC ((hεker _).1 h)
    have h5 : (ε ⟨a, haP⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨a, haP⟩ : ↥P) ^ 2 = 1 := Subtype.ext ha2
      rw [this, map_one]
    have h6 := sl2_not_commute _ h5 h4 _ h3 h1
    apply h6
    have hc : ⁅k, a⁆ ∈ Subgroup.centralizer (V : Set G) :=
      hcomm (Subgroup.commutator_mem_commutator hkK haJ)
    have h7 : ε ⁅(⟨k, hkP⟩ : ↥P), ⟨a, haP⟩⁆ = 1 := (hεker _).2 hc
    rwa [map_commutatorElement] at h7

end CFSG.Quasithin.C1Pack
