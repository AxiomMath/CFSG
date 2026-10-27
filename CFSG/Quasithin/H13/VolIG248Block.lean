module

public import CFSG.Quasithin.H13.VolIG248Module
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.Quasithin.A5Model Subgroup
open scoped commutatorElement

theorem isQuasisimple_of_mulEquiv_alt5 {Q : Type*} [Group Q]
    (e : Q ≃* alternatingGroup (Fin 5)) : CFSG.IsQuasisimple Q := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimp : IsSimpleGroup Q := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ : ∃ a b : Q, a * b ≠ b * a := by
    obtain ⟨a', b', h⟩ : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by decide
    refine ⟨e.symm a', e.symm b', fun h' => h ?_⟩
    have := congrArg e h'
    simpa using this
  have hcenter : center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
    · exact h
    · exfalso
      apply hab
      have hc : a ∈ center Q := h ▸ mem_top a
      exact (mem_center_iff.mp hc b).symm
  let e' : Q ⧸ center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  refine ⟨⟨?_⟩, e'.isSimpleGroup, e'.symm a, e'.symm b, fun h => hab ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator Q := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  · have := congrArg e' h
    simpa using this

variable {G : Type} [Group G]

namespace G248

namespace Setting

variable [Finite G] {V V₁ L T H : Subgroup G} {g : G} (X : Setting V V₁ L T H g)
include X

theorem blockQ_eq : blockQ L = conjClosure V₁ L := X.pCoreOf_L_eq

theorem blockU_eq : blockU L = conjClosure V₁ L := by
  show ⁅blockQ L, L⁆ = conjClosure V₁ L
  rw [X.blockQ_eq, X.commutator_VL_eq]

omit [Finite G] in
theorem VL_comm {x y : G} (hx : x ∈ conjClosure V₁ L) (hy : y ∈ conjClosure V₁ L) :
    x * y = y * x := by
  have h : (⟨x, hx⟩ * ⟨y, hy⟩ : ↥(conjClosure V₁ L)) = ⟨y, hy⟩ * ⟨x, hx⟩ :=
    X.St.D.ψ.injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val h

omit [Finite G] in
theorem VL_sq {x : G} (hx : x ∈ conjClosure V₁ L) : x ^ 2 = 1 := by
  have h : X.St.D.ψ ⟨x, hx⟩ ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, two_nsmul]
    exact Ev_add_self _
  have h2 : (⟨x, hx⟩ : ↥(conjClosure V₁ L)) ^ 2 = 1 :=
    X.St.D.ψ.injective (by rw [map_pow, h, map_one])
  have := congrArg Subtype.val h2
  simpa using this

theorem blockZ_eq : blockZ L = ⊥ := by
  have hZ : blockZ L = conjClosure V₁ L ⊓ centralizer (L : Set G) := by
    show blockU L ⊓ centralizer (L : Set G) = _
    rw [X.blockU_eq]
  rw [hZ]
  have hZL : L ≤ normalizer ((conjClosure V₁ L ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun l hl => inf_normalizer_le_normalizer_inf ⟨X.St.D.hnorm hl,
      normalizer_le_normalizer_centralizer'' L (le_normalizer hl)⟩
  rcases X.St.irreducible_L inf_le_left hZL with h | h
  · exact h
  · exfalso
    obtain ⟨l, hl, v, hv, hne⟩ := X.exists_not_comm
    have hvZ : v ∈ conjClosure V₁ L ⊓ centralizer (L : Set G) := by rw [h]; exact hv
    apply hne
    rw [mem_centralizer_iff.mp hvZ.2 l hl]
    group

theorem mem_pCore_iff (x : ↥L) : x ∈ CFSG.pCore 2 ↥L ↔ X.St.D.θ x = 1 := by
  rw [AppC.mem_pCore_iff_mem_blockQ, X.theta_eq_one_iff]
  rfl

theorem ker_theta : X.St.D.θ.ker = CFSG.pCore 2 ↥L := by
  ext x
  rw [MonoidHom.mem_ker, X.mem_pCore_iff]

theorem isShort2 : IsShort2 L := by
  have hb := X.St.hyp.base
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N _ hp
    have hle : oTwoUpper L ≤ N.map L.subtype := oTwoUpper_le_of_pow_mem fun x hx => by
      obtain ⟨k, hk⟩ := hp (QuotientGroup.mk ⟨x, hx⟩)
      exact ⟨k, ⟨⟨x, hx⟩ ^ 2 ^ k, (QuotientGroup.eq_one_iff _).1 (by
        rw [QuotientGroup.mk_pow]; exact hk), rfl⟩⟩
    rw [← hb.oTwo_eq] at hle
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'
  · rintro x ⟨hxL, hxC⟩
    rw [X.pCoreOf_L_eq] at hxC
    have h1 : X.St.D.alpha ⟨x, X.St.D.hnorm hxL⟩ = 1 := by
      rw [RawData5.alpha_eq_one_iff]
      intro v
      have := mem_centralizer_iff.mp hxC v v.2
      rw [← this]
      group
    have h1' : X.St.D.alpha ⟨(⟨x, hxL⟩ : ↥L), X.St.D.hnorm (⟨x, hxL⟩ : ↥L).2⟩ = 1 := h1
    rw [X.St.D.alpha_of_mem] at h1'
    have h2 : X.St.D.θ ⟨x, hxL⟩ = 1 := Subtype.ext (pact_injective (h1'.trans (map_one pact).symm))
    exact (X.theta_eq_one_iff _).1 h2
  · rw [X.blockU_eq, X.blockQ_eq]
    exact ⟨fun x hx => ⟨hx, mem_centralizer_iff.2 fun y hy => X.VL_comm hy hx⟩,
      fun x hx => X.VL_sq hx⟩
  · left
    exact isQuasisimple_of_mulEquiv_alt5
      ((QuotientGroup.quotientMulEquivOfEq X.ker_theta.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ X.St.D.surj))
  · rw [X.blockZ_eq, X.blockU_eq]
    refine ⟨bot_lt_iff_ne_bot.2 X.St.VL_ne_bot, fun W _ hW hWL => ?_⟩
    exact X.St.irreducible_L hW hWL

theorem isAltType : IsAltType L 5 := by
  let e : ↥(blockU L) ≃* ↥(conjClosure V₁ L) := MulEquiv.subgroupCongr X.blockU_eq
  refine ⟨X.St.D.θ, X.St.D.surj, X.ker_theta, X.St.D.ψ.toMonoidHom.comp e.toMonoidHom,
    X.St.D.ψ.surjective.comp e.surjective, ?_, ?_⟩
  · rw [X.blockZ_eq, bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff _).2 (X.St.D.ψ.injective.comp e.injective)
  · intro ℓ u v huv i
    have h1 : X.St.D.ψ (e v) = pact (X.St.D.θ ℓ : Equiv.Perm (Fin 5)) (X.St.D.ψ (e u)) := by
      rw [← X.St.D.equiv]
      congr 1
      apply Subtype.ext
      rw [conjAct_coe_apply]
      exact huv
    show ((Multiplicative.toAdd (X.St.D.ψ (e v)) : ↥Ev) : Fin 5 → ZMod 2) i = _
    rw [h1, toAdd_pact, pw_coe]
    rfl

end Setting

end G248

end CFSG.Quasithin.H13.VolI
