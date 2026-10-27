module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FS

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open scoped commutatorElement IsMulCommutative

theorem closure_eq_top_of_wedge {S : Set (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)))}
    (h : ∀ k : Fin 6, ∃ x ∈ Subgroup.closure S,
      B5FinWedge.wedgeCoord4 (Multiplicative.toAdd x) = Pi.single k (1 : ZMod 2)) :
    Subgroup.closure S = ⊤ := by
  set H := Subgroup.closure S with hH
  let f : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) →* Multiplicative (Fin 6 → ZMod 2) :=
    (B5FinWedge.wedgeCoord4 (K := ZMod 2)).toAddMonoidHom.toMultiplicative
  have hfb : Function.Bijective f := B5FinWedge.wedgeCoord4_bijective
  have key : ∀ v : Fin 6 → ZMod 2, Multiplicative.ofAdd v =
      (if v 0 = 1 then Multiplicative.ofAdd (Pi.single 0 1) else 1) *
        (if v 1 = 1 then Multiplicative.ofAdd (Pi.single 1 1) else 1) *
          (if v 2 = 1 then Multiplicative.ofAdd (Pi.single 2 1) else 1) *
            (if v 3 = 1 then Multiplicative.ofAdd (Pi.single 3 1) else 1) *
              (if v 4 = 1 then Multiplicative.ofAdd (Pi.single 4 1) else 1) *
                (if v 5 = 1 then Multiplicative.ofAdd (Pi.single 5 1) else 1) := by
    decide +kernel
  have hsingle : ∀ k : Fin 6, Multiplicative.ofAdd (Pi.single k (1 : ZMod 2)) ∈ H.map f := by
    intro k
    obtain ⟨x, hx, hxe⟩ := h k
    exact ⟨x, hx, by rw [← hxe]; rfl⟩
  have hite : ∀ (p : Prop) [Decidable p] (k : Fin 6),
      (if p then Multiplicative.ofAdd (Pi.single k (1 : ZMod 2)) else 1) ∈ H.map f := by
    intro p _ k
    split_ifs
    · exact hsingle k
    · exact Subgroup.one_mem _
  have htop : ∀ w : Multiplicative (Fin 6 → ZMod 2), w ∈ H.map f := by
    intro w
    rw [show w = Multiplicative.ofAdd (Multiplicative.toAdd w) from rfl, key]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hite _ 0) (hite _ 1)) (hite _ 2)) (hite _ 3)) (hite _ 4)) (hite _ 5)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := htop (f x)
  rw [← hfb.1 hyx]
  exact hy

theorem fix_wedge_one : ∀ x : Fin 6 → ZMod 2,
    B5FinWedge.wedgeMat4 (1 + single 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    B5FinWedge.wedgeMat4 (1 + single 2 3 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    B5FinWedge.wedgeMat4 (1 + single 3 1 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    x = 0 := by
  decide +kernel

theorem fix_wedge_three : ∀ x : Fin 6 → ZMod 2,
    B5FinWedge.wedgeMat4 (1 + single 0 1 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    B5FinWedge.wedgeMat4 (1 + single 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    B5FinWedge.wedgeMat4 (1 + single 2 0 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    x = 0 := by
  decide +kernel

theorem coord_actW_tr {a b : Fin 4} (h : a ≠ b)
    (x : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :
    B5FinWedge.wedgeCoord4 (Multiplicative.toAdd
        (FLc.actW (SpecialLinearGroup.transvection h (1 : ZMod 2)) x)) =
      B5FinWedge.wedgeMat4 (1 + single a b 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        B5FinWedge.wedgeCoord4 (Multiplicative.toAdd x) := by
  rw [FLc.coord4_actW]
  rfl

theorem hfix_wedge_one : ∀ b : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)),
    (∀ g ∈ (perfectCore (FLc.QI 4 {1}) : Set SL4), FLc.actW g b = b) → b = 1 := by
  intro b hb
  have e1 := congrArg (fun y => B5FinWedge.wedgeCoord4 (Multiplicative.toAdd y))
    (hb _ (tr_mem_one_levi (a := 1) (c := 2) (by decide) (by decide) (by decide)))
  have e2 := congrArg (fun y => B5FinWedge.wedgeCoord4 (Multiplicative.toAdd y))
    (hb _ (tr_mem_one_levi (a := 2) (c := 3) (by decide) (by decide) (by decide)))
  have e3 := congrArg (fun y => B5FinWedge.wedgeCoord4 (Multiplicative.toAdd y))
    (hb _ (tr_mem_one_levi (a := 3) (c := 1) (by decide) (by decide) (by decide)))
  simp only [coord_actW_tr] at e1 e2 e3
  have h0 := fix_wedge_one _ e1 e2 e3
  apply Multiplicative.toAdd.injective
  apply (B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)).1
  rw [h0, toAdd_one, map_zero]

theorem hfix_wedge_three : ∀ b : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)),
    (∀ g ∈ (perfectCore (FLc.QI 4 {3}) : Set SL4), FLc.actW g b = b) → b = 1 := by
  intro b hb
  have e1 := congrArg (fun y => B5FinWedge.wedgeCoord4 (Multiplicative.toAdd y))
    (hb _ (tr_mem_three_levi (a := 0) (c := 1) (by decide) (by decide) (by decide)))
  have e2 := congrArg (fun y => B5FinWedge.wedgeCoord4 (Multiplicative.toAdd y))
    (hb _ (tr_mem_three_levi (a := 1) (c := 2) (by decide) (by decide) (by decide)))
  have e3 := congrArg (fun y => B5FinWedge.wedgeCoord4 (Multiplicative.toAdd y))
    (hb _ (tr_mem_three_levi (a := 2) (c := 0) (by decide) (by decide) (by decide)))
  simp only [coord_actW_tr] at e1 e2 e3
  have h0 := fix_wedge_three _ e1 e2 e3
  apply Multiplicative.toAdd.injective
  apply (B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)).1
  rw [h0, toAdd_one, map_zero]

theorem exists_wedge_comm {P : Set SL4} {a b : Fin 4} (hab : a ≠ b)
    (hmem : SpecialLinearGroup.transvection hab (1 : ZMod 2) ∈ P) (k' k : Fin 6)
    (he : B5FinWedge.wedgeMat4 (1 + single a b 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      Pi.single k' 1 + -Pi.single k' 1 = Pi.single k 1) :
    ∃ x ∈ Subgroup.closure {x | ∃ g ∈ P, ∃ c : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)),
      x = FLc.actW g c * c⁻¹},
      B5FinWedge.wedgeCoord4 (Multiplicative.toAdd x) = Pi.single k (1 : ZMod 2) := by
  obtain ⟨w, hw⟩ := (B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)).2 (Pi.single k' 1)
  refine ⟨FLc.actW (SpecialLinearGroup.transvection hab 1) (Multiplicative.ofAdd w) *
    (Multiplicative.ofAdd w)⁻¹, Subgroup.subset_closure ⟨_, hmem, _, rfl⟩, ?_⟩
  rw [toAdd_mul, toAdd_inv, map_add, map_neg, coord_actW_tr, toAdd_ofAdd, hw]
  exact he

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G} {α : ↥L →* SL4}
  {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)} [IsMulCommutative ↥(vPlus L T)]

theorem card_comm_ge_ext_one (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U' Z' : Subgroup ↥(vPlus L T)}
    (D₀ : FLc.VModel 4 ρ U' Z' (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) :
    64 ≤ Nat.card ↥⁅vPlus L T, liftCore α (FLc.QI 4 {1})⁆ := by
  have : Finite (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :=
    Nat.finite_of_card_ne_zero (by rw [FLc.card_X_ext4]; norm_num)
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← FLc.card_X_ext4]
  refine card_le_comm D₀ (P := (perfectCore (FLc.QI 4 {1}) : Set SL4))
    (fun g hg => exists_mem_Y h hαs hαv hg) (closure_eq_top_of_wedge fun k => ?_)
  fin_cases k
  · exact exists_wedge_comm (b := 2) (by decide) (tr_mem_one_rad (by decide) _) 3 _ (by decide)
  · exact exists_wedge_comm (b := 1) (by decide) (tr_mem_one_rad (by decide) _) 3 _ (by decide)
  · exact exists_wedge_comm (b := 1) (by decide) (tr_mem_one_rad (by decide) _) 4 _ (by decide)
  · exact exists_wedge_comm (a := 1) (b := 3) (by decide)
      (tr_mem_one_levi (by decide) (by decide) _) 5 _ (by decide)
  · exact exists_wedge_comm (a := 1) (b := 2) (by decide)
      (tr_mem_one_levi (by decide) (by decide) _) 5 _ (by decide)
  · exact exists_wedge_comm (a := 2) (b := 1) (by decide)
      (tr_mem_one_levi (by decide) (by decide) _) 4 _ (by decide)

theorem card_comm_ge_ext_three (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U' Z' : Subgroup ↥(vPlus L T)}
    (D₀ : FLc.VModel 4 ρ U' Z' (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) :
    64 ≤ Nat.card ↥⁅vPlus L T, liftCore α (FLc.QI 4 {3})⁆ := by
  have : Finite (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :=
    Nat.finite_of_card_ne_zero (by rw [FLc.card_X_ext4]; norm_num)
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← FLc.card_X_ext4]
  refine card_le_comm D₀ (P := (perfectCore (FLc.QI 4 {3}) : Set SL4))
    (fun g hg => exists_mem_Y h hαs hαv hg) (closure_eq_top_of_wedge fun k => ?_)
  fin_cases k
  · exact exists_wedge_comm (a := 0) (b := 2) (by decide)
      (tr_mem_three_levi (by decide) (by decide) _) 3 _ (by decide)
  · exact exists_wedge_comm (a := 0) (b := 1) (by decide)
      (tr_mem_three_levi (by decide) (by decide) _) 3 _ (by decide)
  · exact exists_wedge_comm (a := 0) (b := 1) (by decide)
      (tr_mem_three_levi (by decide) (by decide) _) 4 _ (by decide)
  · exact exists_wedge_comm (a := 1) (b := 0) (by decide)
      (tr_mem_three_levi (by decide) (by decide) _) 1 _ (by decide)
  · exact exists_wedge_comm (a := 1) (b := 0) (by decide)
      (tr_mem_three_levi (by decide) (by decide) _) 2 _ (by decide)
  · exact exists_wedge_comm (a := 2) (b := 0) (by decide)
      (tr_mem_three_levi (by decide) (by decide) _) 2 _ (by decide)

omit [IsMulCommutative ↥(vPlus L T)] in
theorem comm_pCoreOf_le_of {V Y : Subgroup G} (hαs : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) (hLperf : ⁅L, L⁆ = L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hYL : Y ≤ L)
    (hY1 : ∃ y : ↥L, (y : G) ∈ Y ∧ α y ≠ 1) (hcomm : ⁅pCoreOf 2 L, Y⁆ ≤ V) :
    ⁅pCoreOf 2 L, L⁆ ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  let K : Subgroup G :=
    { carrier := {x | x ∈ L ∧ ∀ q ∈ pCoreOf 2 L, x * q * x⁻¹ * q⁻¹ ∈ V}
      one_mem' := by
        refine ⟨L.one_mem, fun q _ => ?_⟩
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact V.one_mem
      mul_mem' := fun {x y} hx hy => ⟨L.mul_mem hx.1 hy.1, fun q hq => by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hLV hx.1) _).mp (hy.2 q hq)
        have e : x * y * q * (x * y)⁻¹ * q⁻¹ =
            (x * (y * q * y⁻¹ * q⁻¹) * x⁻¹) * (x * q * x⁻¹ * q⁻¹) := by group
        rw [e]
        exact V.mul_mem h1 (hx.2 q hq)⟩
      inv_mem' := fun {x} hx => ⟨L.inv_mem hx.1, fun q hq => by
        have hq' : x⁻¹ * q * x ∈ pCoreOf 2 L := by
          have := (Subgroup.mem_normalizer_iff.mp (hLO (L.inv_mem hx.1)) q).mp hq
          simpa using this
        have h1 := V.inv_mem (hx.2 _ hq')
        have e : x⁻¹ * q * x⁻¹⁻¹ * q⁻¹ =
            (x * (x⁻¹ * q * x) * x⁻¹ * (x⁻¹ * q * x)⁻¹)⁻¹ := by group
        rw [e]
        exact h1⟩ }
  have hKL : K ≤ L := fun x hx => hx.1
  have hKn : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K := by
    intro l hl k hk
    refine ⟨L.mul_mem (L.mul_mem hl hk.1) (L.inv_mem hl), fun q hq => ?_⟩
    have hq' : l⁻¹ * q * l ∈ pCoreOf 2 L := by
      have := (Subgroup.mem_normalizer_iff.mp (hLO (L.inv_mem hl)) q).mp hq
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp (hk.2 _ hq')
    have e : l * k * l⁻¹ * q * (l * k * l⁻¹)⁻¹ * q⁻¹ =
        l * (k * (l⁻¹ * q * l) * k⁻¹ * (l⁻¹ * q * l)⁻¹) * l⁻¹ := by group
    rw [e]
    exact h1
  have hYK : Y ≤ K := by
    intro y hy
    refine ⟨hYL hy, fun q hq => ?_⟩
    have h1 : ⁅y, q⁆ ∈ ⁅pCoreOf 2 L, Y⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hy hq
    rw [commutatorElement_def] at h1
    exact hcomm h1
  have hNorm : (K.subgroupOf L).Normal :=
    ⟨fun k hk l => Subgroup.mem_subgroupOf.2 (hKn l l.2 k (Subgroup.mem_subgroupOf.1 hk))⟩
  have hsimple : IsSimpleGroup SL4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) (by norm_num)
  have hαK : (K.subgroupOf L).map α = ⊤ := by
    have := hNorm.map α hαs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K.subgroupOf L).map α) with h1 | h1
    · obtain ⟨y, hyY, hy1⟩ := hY1
      have : α y ∈ (K.subgroupOf L).map α := ⟨y, Subgroup.mem_subgroupOf.2 (hYK hyY), rfl⟩
      rw [h1, Subgroup.mem_bot] at this
      exact absurd this hy1
    · exact h1
  have h2 : IsPGroup 2 (↥L ⧸ K.subgroupOf L) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H l =>
      obtain ⟨k, hk, hkl⟩ : α l ∈ (K.subgroupOf L).map α := by rw [hαK]; exact Subgroup.mem_top _
      have hq : k⁻¹ * l ∈ CFSG.pCore 2 ↥L := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hkl, inv_mul_cancel]
      obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hq⟩
      refine ⟨m, ?_⟩
      have hm' : (k⁻¹ * l) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have hkK : (QuotientGroup.mk k : ↥L ⧸ K.subgroupOf L) = 1 :=
        (QuotientGroup.eq_one_iff k).2 hk
      have e : (QuotientGroup.mk l : ↥L ⧸ K.subgroupOf L) = QuotientGroup.mk (k⁻¹ * l) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hkK, inv_one, one_mul]
      rw [e, ← QuotientGroup.mk_pow, hm', QuotientGroup.mk_one]
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hLperf
  have hsub : Subsingleton (↥L ⧸ K.subgroupOf L) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent _ h2.isNilpotent
  have hLK : L ≤ K := by
    intro l hl
    have : (QuotientGroup.mk ⟨l, hl⟩ : ↥L ⧸ K.subgroupOf L) = 1 := Subsingleton.elim _ _
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 this)
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have h1 := V.inv_mem ((hLK hl).2 q hq)
  have e : ⁅q, l⁆ = (l * q * l⁻¹ * q⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact h1

end CFSG.Quasithin.H13.L3321
