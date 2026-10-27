module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

namespace P22x

open CFSG.Open Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped Pointwise commutatorElement

section Dictionary

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {Vmod : Type} [AddCommGroup Vmod]
  [Module (ZMod 2) Vmod]

@[expose] def iota (e : ↥V ≃* Multiplicative Vmod) (x : Vmod) : G :=
  ((e.symm (Multiplicative.ofAdd x) : ↥V) : G)

theorem iota_mem (e : ↥V ≃* Multiplicative Vmod) (x : Vmod) : iota e x ∈ V := (e.symm _).2

theorem iota_add (e : ↥V ≃* Multiplicative Vmod) (x y : Vmod) :
    iota e (x + y) = iota e x * iota e y := by
  unfold iota
  rw [ofAdd_add, map_mul]
  rfl

theorem iota_zero (e : ↥V ≃* Multiplicative Vmod) : iota e 0 = 1 := by
  unfold iota
  rw [ofAdd_zero, map_one]
  rfl

theorem iota_neg (e : ↥V ≃* Multiplicative Vmod) (x : Vmod) : iota e (-x) = (iota e x)⁻¹ := by
  unfold iota
  rw [ofAdd_neg, map_inv]
  rfl

theorem iota_sub (e : ↥V ≃* Multiplicative Vmod) (x y : Vmod) :
    iota e (x - y) = iota e x * (iota e y)⁻¹ := by
  rw [sub_eq_add_neg, iota_add, iota_neg]

theorem iota_injective (e : ↥V ≃* Multiplicative Vmod) : Function.Injective (iota e) := by
  intro x y h
  have h1 : e.symm (Multiplicative.ofAdd x) = e.symm (Multiplicative.ofAdd y) := Subtype.ext h
  exact Multiplicative.ofAdd.injective (e.symm.injective h1)

theorem exists_iota (e : ↥V ≃* Multiplicative Vmod) {g : G} (hg : g ∈ V) :
    ∃ x : Vmod, iota e x = g :=
  ⟨Multiplicative.toAdd (e ⟨g, hg⟩), by simp [iota]⟩

theorem iota_rho (hV : M ≤ normalizer (V : Set G)) (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ) (m : ↥M) (x : Vmod) :
    iota e (ρ (QuotientGroup.mk m) x) = (m : G) * iota e x * (m : G)⁻¹ :=
  uc22br4_symm_rho hV e ρ hc m x

@[expose] def bsub (e : ↥V ≃* Multiplicative Vmod) (W : Subgroup G) : Submodule (ZMod 2) Vmod :=
  AddSubgroup.toZModSubmodule 2 (uc22br4_addSub e W)

theorem mem_bsub {e : ↥V ≃* Multiplicative Vmod} {W : Subgroup G} {x : Vmod} :
    x ∈ bsub e W ↔ iota e x ∈ W := Iff.rfl

theorem bsub_le_iff (e : ↥V ≃* Multiplicative Vmod) {W W' : Subgroup G} (hW : W ≤ V) :
    bsub e W ≤ bsub e W' ↔ W ≤ W' := by
  constructor
  · intro h g hg
    obtain ⟨x, rfl⟩ := exists_iota e (hW hg)
    exact h (mem_bsub.2 hg)
  · intro h x hx
    exact h hx

theorem bsub_inf (e : ↥V ≃* Multiplicative Vmod) (W W' : Subgroup G) :
    bsub e (W ⊓ W') = bsub e W ⊓ bsub e W' := rfl

theorem bsub_V (e : ↥V ≃* Multiplicative Vmod) : bsub e V = ⊤ :=
  eq_top_iff.2 fun x _ => iota_mem e x

theorem bsub_eq_bot_iff (e : ↥V ≃* Multiplicative Vmod) {W : Subgroup G} (hW : W ≤ V) :
    bsub e W = ⊥ ↔ W = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨x, rfl⟩ := exists_iota e (hW hg)
    have : x ∈ bsub e W := mem_bsub.2 hg
    rw [h, Submodule.mem_bot] at this
    rw [this, iota_zero]
    exact Subgroup.one_mem _
  · intro h
    rw [eq_bot_iff]
    intro x hx
    have : iota e x = 1 := Subgroup.mem_bot.1 (h ▸ mem_bsub.1 hx)
    rw [← iota_zero e] at this
    exact (Submodule.mem_bot _).2 (iota_injective e this)

theorem card_bsub (e : ↥V ≃* Multiplicative Vmod) {W : Subgroup G} (hW : W ≤ V) :
    Nat.card (bsub e W) = Nat.card W := by
  refine Nat.card_congr
    { toFun := fun x => ⟨iota e x.1, mem_bsub.1 x.2⟩
      invFun := fun w => ⟨Multiplicative.toAdd (e ⟨w.1, hW w.2⟩), mem_bsub.2 (by simpa [iota] using w.2)⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp [iota]
      right_inv := fun w => by
        apply Subtype.ext
        simp [iota] }

theorem fixSub_mbarImage (hV : M ≤ normalizer (V : Set G)) (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ) {X : Subgroup G}
    (hX : X ≤ M) : fixSub ρ (mbarImage M V X) = bsub e (centralizer (X : Set G)) := by
  ext x
  constructor
  · intro hx
    refine mem_bsub.2 (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    have h1 := hx (QuotientGroup.mk ⟨y, hX hy⟩) ⟨⟨y, hX hy⟩, hy, rfl⟩
    have h2 := congrArg (iota e) h1
    rw [iota_rho hV e ρ hc] at h2
    calc y * iota e x = y * iota e x * y⁻¹ * y := by group
      _ = iota e x * y := by rw [h2]
  · intro hx a ha
    obtain ⟨m, hm, rfl⟩ := ha
    apply iota_injective e
    rw [show (QuotientGroup.mk' (kerAct M V).normalCore) m = QuotientGroup.mk m from rfl,
      iota_rho hV e ρ hc]
    have h1 := Subgroup.mem_centralizer_iff.1 (mem_bsub.1 hx) (m : G) hm
    rw [h1]
    group

@[expose] def bsup (e : ↥V ≃* Multiplicative Vmod) (S : Submodule (ZMod 2) Vmod) : Subgroup G :=
  (((AddSubgroup.toSubgroup S.toAddSubgroup).comap e.toMonoidHom).map V.subtype)

theorem iota_mem_bsup {e : ↥V ≃* Multiplicative Vmod} {S : Submodule (ZMod 2) Vmod} {x : Vmod} :
    iota e x ∈ bsup e S ↔ x ∈ S := by
  constructor
  · rintro ⟨v, hv, hvx⟩
    have : v = e.symm (Multiplicative.ofAdd x) := Subtype.ext hvx
    subst this
    simpa using hv
  · intro hx
    exact ⟨e.symm (Multiplicative.ofAdd x), by simpa using hx, rfl⟩

theorem bsup_le_V (e : ↥V ≃* Multiplicative Vmod) (S : Submodule (ZMod 2) Vmod) :
    bsup e S ≤ V := by
  rintro _ ⟨v, _, rfl⟩
  exact v.2

theorem bsub_commutator (hV : M ≤ normalizer (V : Set G)) (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ) {W X : Subgroup G}
    (hW : W ≤ V) (hX : X ≤ M) :
    ⁅W, X⁆ ≤ V ∧ bsub e ⁅W, X⁆ = commOn ρ (mbarImage M V X) (bsub e W) := by
  have hcomm : ∀ (w y : G) (hyX : y ∈ X) (u : Vmod), iota e u = w →
      iota e (u - ρ (QuotientGroup.mk ⟨y, hX hyX⟩) u) = w * y * w⁻¹ * y⁻¹ := by
    intro w y hyX u hu
    rw [iota_sub, iota_rho hV e ρ hc ⟨y, hX hyX⟩, hu]
    simp only
    group
  have hle : ⁅W, X⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro w hw y hy
    rw [commutatorElement_def]
    have h1 : y * w⁻¹ * y⁻¹ ∈ V := uc22br_gt_conj_mem hV (hX hy) (V.inv_mem (hW hw))
    have := V.mul_mem (hW hw) h1
    simpa [mul_assoc] using this
  refine ⟨hle, le_antisymm ?_ ?_⟩
  · have hsub : ⁅W, X⁆ ≤ bsup e (commOn ρ (mbarImage M V X) (bsub e W)) := by
      rw [Subgroup.commutator_le]
      intro w hw y hy
      obtain ⟨u, hu⟩ := exists_iota e (hW hw)
      rw [commutatorElement_def, ← hcomm w y hy u hu, iota_mem_bsup]
      have := Submodule.neg_mem _ (sub_mem_commOn (ρ := ρ) (A := mbarImage M V X)
        (U := bsub e W) (a := QuotientGroup.mk ⟨y, hX hy⟩) ⟨⟨y, hX hy⟩, hy, rfl⟩
        (mem_bsub.2 (hu ▸ hw)))
      simpa using this
    intro x hx
    exact iota_mem_bsup.1 (hsub (mem_bsub.1 hx))
  · rw [commOn_le_iff]
    intro a ha u hu
    obtain ⟨m, hm, rfl⟩ := ha
    rw [mem_bsub]
    have hy : (m : G) ∈ X := hm
    have h1 := hcomm (iota e u) (m : G) hy u rfl
    have h2 : iota e (ρ (QuotientGroup.mk m) u - u) =
        (iota e u * (m : G) * (iota e u)⁻¹ * (m : G)⁻¹)⁻¹ := by
      rw [← h1, ← iota_neg, neg_sub]
    show iota e (ρ (QuotientGroup.mk m) u - u) ∈ ⁅W, X⁆
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator (mem_bsub.1 hu) hy)

end Dictionary

end P22x

end CFSG.LocalAnalysis.UniquenessCase.UC22
