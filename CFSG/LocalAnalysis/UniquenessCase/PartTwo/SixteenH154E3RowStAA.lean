module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SecBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3ExtClassify
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Family CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

variable {W : Type} [CommGroup W]

private theorem s16h_e3A_finite_mulAut {X : Type*} [Mul X] [Finite X] : Finite (MulAut X) := by
  classical
  exact Finite.of_injective (fun f : MulAut X => (f : X → X))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_e3A_le_stabSub_commSub (L : Subgroup (MulAut W)) :
    L ≤ stabSub (commSub ⊤ L) := by
  intro l hl
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have hmem : l⁻¹ (l u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b (fun x hx => L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl) (l u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b (fun x hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)) u hu

private theorem s16h_e3A_le_stabSub_fixV (L : Subgroup (MulAut W)) :
    L ≤ stabSub (fixV L) := by
  intro l hl
  rw [mem_stabSub]
  intro z
  constructor
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
    have h1 : (l * x * l⁻¹) (l z) = l z := hz _ hx'
    have h2 : (l * x * l⁻¹) (l z) = l (x z) := by simp [MulAut.mul_apply]
    exact l.injective (by rw [← h2, h1])
  · intro hz
    rw [mem_fixV] at hz
    rwa [hz l hl]

private noncomputable def s16h_mulAutLinearHom (Q : Type*) [CommGroup Q]
    [Module (ZMod 2) (Additive Q)] : MulAut Q →* (Additive Q ≃ₗ[ZMod 2] Additive Q) where
  toFun g := (MulEquiv.toAdditive g).toLinearEquiv (fun c x => by
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 from by decide) c with rfl | rfl <;> simp)
  map_one' := LinearEquiv.ext fun x => rfl
  map_mul' f g := LinearEquiv.ext fun x => rfl

private theorem s16h_mulAutLinearHom_apply (Q : Type*) [CommGroup Q]
    [Module (ZMod 2) (Additive Q)] (g : MulAut Q) (q : Q) :
    s16h_mulAutLinearHom Q g (Additive.ofMul q) = Additive.ofMul (g q) := rfl

private def s16h_submoduleOfSubgroup (Q : Type*) [CommGroup Q]
    [Module (ZMod 2) (Additive Q)] (S : Subgroup Q) : Submodule (ZMod 2) (Additive Q) where
  carrier := {x | Additive.toMul x ∈ S}
  add_mem' := fun {x y} hx hy => by
    show Additive.toMul (x + y) ∈ S
    rw [toMul_add]
    exact S.mul_mem hx hy
  zero_mem' := by
    show Additive.toMul (0 : Additive Q) ∈ S
    rw [show Additive.toMul (0 : Additive Q) = 1 from rfl]
    exact S.one_mem
  smul_mem' := fun c {x} hx => by
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 from by decide) c with rfl | rfl
    · show Additive.toMul ((0 : ZMod 2) • x) ∈ S
      rw [zero_smul]
      exact S.one_mem
    · show Additive.toMul ((1 : ZMod 2) • x) ∈ S
      rw [one_smul]
      exact hx

private def s16h_subgroupOfSubmodule (Q : Type*) [CommGroup Q]
    [Module (ZMod 2) (Additive Q)] (N : Submodule (ZMod 2) (Additive Q)) : Subgroup Q where
  carrier := {q | Additive.ofMul q ∈ N}
  one_mem' := by
    show Additive.ofMul (1 : Q) ∈ N
    rw [show Additive.ofMul (1 : Q) = 0 from rfl]
    exact N.zero_mem
  mul_mem' := fun {x y} hx hy => by
    show Additive.ofMul (x * y) ∈ N
    rw [ofMul_mul]
    exact N.add_mem hx hy
  inv_mem' := fun {x} hx => by
    show Additive.ofMul x⁻¹ ∈ N
    rw [ofMul_inv]
    exact N.neg_mem hx

private theorem s16h_submoduleOfSubgroup_subgroupOfSubmodule (Q : Type*) [CommGroup Q]
    [Module (ZMod 2) (Additive Q)] (N : Submodule (ZMod 2) (Additive Q)) :
    s16h_submoduleOfSubgroup Q (s16h_subgroupOfSubmodule Q N) = N := by
  ext x
  exact Iff.rfl

private theorem s16h_isInvAct_iff (Q : Type*) [CommGroup Q] [Module (ZMod 2) (Additive Q)]
    {G : Type*} [Group G] (act : G →* MulAut Q) (N : Submodule (ZMod 2) (Additive Q)) :
    IsInvAct (fun g x => s16h_mulAutLinearHom Q (act g) x) N ↔
      ∀ g : G, ∀ q ∈ s16h_subgroupOfSubmodule Q N,
        act g q ∈ s16h_subgroupOfSubmodule Q N := by
  constructor
  · intro hN g q hq
    exact hN g (Additive.ofMul q) hq
  · intro hN g x hx
    have hx' : Additive.toMul x ∈ s16h_subgroupOfSubmodule Q N := by
      show Additive.ofMul (Additive.toMul x) ∈ N
      rwa [ofMul_toMul]
    have h := hN g (Additive.toMul x) hx'
    show s16h_mulAutLinearHom Q (act g) x ∈ N
    rw [← ofMul_toMul x, s16h_mulAutLinearHom_apply]
    exact h

theorem s16h_H5_rowSt8_sec_centralizer_eq_bot [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
    (hirr : commSub ⊤ L ∈ irrSet L) :
    Subgroup.centralizer (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) :
      Set (MulAut (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))) = ⊥ := by
  classical
  haveI : Finite (MulAut W) := s16h_e3A_finite_mulAut (X := W)
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := U ⊓ fixV L with hZ
  have hLU : L ≤ stabSub U := by rw [hU]; exact s16h_e3A_le_stabSub_commSub L
  have hLfix : L ≤ stabSub (fixV L) := s16h_e3A_le_stabSub_fixV L
  have hLZ : L ≤ stabSub Z := by
    rw [hZ]
    intro l hl
    rw [mem_stabSub]
    intro x
    exact ⟨fun hx => ⟨(hLU hl x).1 hx.1, (hLfix hl x).1 hx.2⟩,
      fun hx => ⟨(hLU hl x).2 hx.1, (hLfix hl x).2 hx.2⟩⟩
  have hcenter : Subgroup.center ↥L = ⊥ := center_eq_bot_of_isL3 h.1
  have hfaith : L ⊓ centSec U Z = ⊥ := by
    rw [hU, hZ]
    exact s16h_H5_faithful_on_quotient hc hcenter
  have hQ2 : ∀ q : Sec U Z, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : (w ^ 2 : ↥U) = 1 := Subtype.ext (by simpa using hc.elem (w : W))
      rw [h2]
      rfl
  letI : Module (ZMod 2) (Additive (Sec U Z)) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      show Additive.ofMul ((Additive.toMul x) ^ 2) = 0
      rw [hQ2]; rfl
  let actL : ↥L →* MulAut (Sec U Z) :=
    (Subgroup.subtype (autSec L U Z)).comp (B5.secEquiv L hLU hLZ hfaith).toMonoidHom
  have hactL_range : actL.range = autSec L U Z := by
    change ((Subgroup.subtype (autSec L U Z)).comp
      (B5.secEquiv L hLU hLZ hfaith).toMonoidHom).range = autSec L U Z
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      (B5.secEquiv L hLU hLZ hfaith).surjective, ← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype _
  obtain ⟨eL⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 h.1
  let act : GL32 →* MulAut (Sec U Z) := actL.comp eL.symm.toMonoidHom
  have hact_range : act.range = autSec L U Z := by
    change (actL.comp eL.symm.toMonoidHom).range = autSec L U Z
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eL.symm.surjective,
      ← MonoidHom.range_eq_map]
    exact hactL_range
  have hact_range' : ∀ a ∈ autSec L U Z, ∃ g : GL32, act g = a := by
    intro a ha
    rw [← hact_range] at ha
    exact ha
  let ρ : GL32 →* (Additive (Sec U Z) ≃ₗ[ZMod 2] Additive (Sec U Z)) :=
    (s16h_mulAutLinearHom (Sec U Z)).comp act
  have hirrsec : XMod.IsIrrSec ↥(autSec L U Z) (⊥ : Subgroup (Sec U Z)) ⊤ := by
    rw [irrSet, Set.mem_setOf_eq] at hirr
    obtain ⟨-, hIrr⟩ := hirr
    rw [IsIrrOn] at hIrr
    obtain ⟨hZU, -, -, hirrCond⟩ := hIrr
    exact B5.isIrrSec_autSec (V := W) (W := U) (C := Z) (L := L) hZU hirrCond hLU hLZ
  have hρ : IsIrrRep ρ := by
    refine ⟨?_, fun g => map_zero _, fun N hN => ?_⟩
    · have hlt : (⊥ : Subgroup (Sec U Z)) < ⊤ := hirrsec.1
      have hne : (⊥ : Subgroup (Sec U Z)) ≠ ⊤ := hlt.ne
      have hex : ∃ q : Sec U Z, q ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hne (by ext q; simp [hcon q])
      exact ⟨Additive.ofMul hex.choose, 0, fun h =>
        hex.choose_spec (Additive.ofMul.injective h)⟩
    · set J : Subgroup (Sec U Z) := s16h_subgroupOfSubmodule (Sec U Z) N with hJ
      have hJinv : XMod.IsInv ↥(autSec L U Z) J := by
        intro a q hq
        obtain ⟨g, hg⟩ := hact_range' (a : MulAut (Sec U Z)) a.2
        have h2 : (a : MulAut (Sec U Z)) q ∈ J := by
          rw [← hg]
          exact (s16h_isInvAct_iff (Sec U Z) act N).1 hN g q hq
        change (a : MulAut (Sec U Z)) q ∈ J
        exact h2
      rcases hirrsec.2 J hJinv bot_le le_top with hbot | htop
      · left
        have hNbot : N = s16h_submoduleOfSubgroup (Sec U Z) J := by
          rw [← s16h_submoduleOfSubgroup_subgroupOfSubmodule (Sec U Z) N, ← hJ]
        rw [hNbot, hbot]
        ext x
        simp [s16h_submoduleOfSubgroup]
      · right
        have hNtop : N = s16h_submoduleOfSubgroup (Sec U Z) J := by
          rw [← s16h_submoduleOfSubgroup_subgroupOfSubmodule (Sec U Z) N, ← hJ]
        rw [hNtop, htop]
        ext x
        simp [s16h_submoduleOfSubgroup]
  have hcard : 2 ^ 8 ∣ Nat.card (Additive (Sec U Z)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmq : E3.mQuot U Z = 8 := h.2
    unfold E3.mQuot at hmq
    have h1 : Nat.card (Additive (Sec U Z)) = Z.relIndex U := by
      rw [← Nat.card_congr (Additive.ofMul (α := Sec U Z))]
      rfl
    rw [h1]
    have hpos : Z.relIndex U ≠ 0 := by
      intro h0
      rw [h0] at hmq
      simp at hmq
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos,
      Nat.factorization_def _ Nat.prime_two]
    exact le_of_eq hmq.symm
  have hcard_ne : Nat.card (Additive (Sec U Z)) ≠ 2 ∧
      Nat.card (Additive (Sec U Z)) ≠ 8 := by
    constructor <;> intro hc'
    · have h2 : (2 : ℕ) ^ 8 ∣ Nat.card (Additive (Sec U Z)) := hcard
      rw [hc'] at h2
      norm_num at h2
    · have h2 : (2 : ℕ) ^ 8 ∣ Nat.card (Additive (Sec U Z)) := hcard
      rw [hc'] at h2
      norm_num at h2
  have hmodel : ModIso repA ρ := by
    rcases irreducible_binary_GL3_classification ρ hρ with h1 | h1 | h1 | h1
    · exact absurd ((card_eq_of_modIso h1).symm.trans (by rw [Nat.card_zmod])) hcard_ne.1
    · exact absurd ((card_eq_of_modIso h1).symm.trans natCard_Vec3) hcard_ne.2
    · exact absurd ((card_eq_of_modIso h1).symm.trans natCard_Vec3) hcard_ne.2
    · exact h1
  rw [Subgroup.eq_bot_iff_forall]
  intro φ hφ
  have hcomm : ∀ g : GL32, φ * act g = act g * φ := by
    intro g
    have hg : act g ∈ autSec L U Z := by rw [← hact_range]; exact ⟨g, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp hφ (act g) hg).symm
  obtain ⟨f, hf⟩ := hmodel
  let Φ : Additive (Sec U Z) ≃ₗ[ZMod 2] Additive (Sec U Z) := s16h_mulAutLinearHom (Sec U Z) φ
  have hΦ : ∀ g, Φ * (ρ g) = (ρ g) * Φ := by
    intro g
    have h2 := congrArg (s16h_mulAutLinearHom (Sec U Z)) (hcomm g)
    simpa [Φ, ρ, map_mul] using h2
  let N : traceZero ≃ₗ[ZMod 2] traceZero := f.trans (Φ.trans f.symm)
  have hkey : ∀ g Z, f.symm (ρ g Z) = repA g (f.symm Z) := by
    intro g Z
    apply f.injective
    rw [hf g (f.symm Z)]
    simp
  have hN : ∀ g X, N (repA g X) = repA g (N X) := by
    intro g X
    have h1 := hf g X
    have h2 := LinearEquiv.congr_fun (hΦ g) (f X)
    simp only [LinearEquiv.mul_apply] at h2
    show f.symm (Φ (f (repA g X))) = repA g (f.symm (Φ (f X)))
    rw [h1, h2, hkey g (Φ (f X))]
  have hN1 : N = 1 := endS_traceZero N hN
  have hΦ1 : Φ = 1 := by
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := f.surjective x
    have h2 : N y = y := by rw [hN1]; rfl
    have h3 : f.symm (Φ (f y)) = y := h2
    have h4 := congrArg f h3
    simpa using h4
  have hφ1 : φ = 1 := by
    refine MulEquiv.ext fun q => ?_
    have h2 := LinearEquiv.congr_fun hΦ1 (Additive.ofMul q)
    have h3 : Additive.ofMul (φ q) = Additive.ofMul q := by
      rw [← s16h_mulAutLinearHom_apply (Sec U Z) φ q]
      exact h2
    exact Additive.ofMul.injective h3
  exact hφ1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
