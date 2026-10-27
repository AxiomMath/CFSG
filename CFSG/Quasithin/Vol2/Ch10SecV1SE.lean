module

public import CFSG.Quasithin.Vol2.Ch10SecV1SC
public import CFSG.Quasithin.Vol2.Ch10SecV1SB
public import CFSG.Quasithin.Vol2.Ch10SecV1SD

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {H : Type} [Group H] {L : Subgroup H} {K : Type} [Field K]

theorem le_normalizer_of_conj_mem {J : Subgroup H} (h : ∀ l ∈ L, ∀ x ∈ J, l * x * l⁻¹ ∈ J) :
    L ≤ Subgroup.normalizer (J : Set H) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h l hl x, fun hx => ?_⟩
  have := h l⁻¹ (L.inv_mem hl) _ hx
  rwa [inv_inv, show l⁻¹ * (l * x * l⁻¹) * l = x by group] at this

namespace SumTwo

variable {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} {V W₀ W₁ : Subgroup H}

@[expose] def conjW (S : SumTwo φ V W₀ W₁) (l : ↥L) (w : ↥W₀) : ↥W₀ :=
  S.c₀.θ.symm (Multiplicative.ofAdd (mat φ l *ᵥ Multiplicative.toAdd (S.c₀.θ w)))

theorem coe_conjW (S : SumTwo φ V W₀ W₁) (l : ↥L) (w : ↥W₀) :
    (S.conjW l w : H) = l * (w : H) * (l : H)⁻¹ := by
  rw [conjW, NatCoord.symm_mat, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem coe_gr_conjW (S : SumTwo φ V W₀ W₁) (a : K) (l : ↥L) (w : ↥W₀) :
    (S.gr a (S.conjW l w) : H) = l * (S.gr a w : H) * (l : H)⁻¹ := by
  have e : S.gr a (S.conjW l w) =
      S.c₁.θ.symm (Multiplicative.ofAdd (mat φ l *ᵥ (a • Multiplicative.toAdd (S.c₀.θ w)))) := by
    apply S.c₁.θ.injective
    rw [gr_apply, conjW, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd,
      Matrix.mulVec_smul]
  rw [e, NatCoord.symm_mat]
  rfl

theorem conj_grHom (S : SumTwo φ V W₀ W₁) (a : K) (l : ↥L) (w : ↥W₀) :
    (l : H) * S.grHom a w * (l : H)⁻¹ = S.grHom a (S.conjW l w) := by
  show (l : H) * ((w : H) * S.gr a w) * (l : H)⁻¹ = S.conjW l w * (S.gr a (S.conjW l w) : H)
  rw [coe_conjW, coe_gr_conjW]
  group

theorem le_normalizer_graph (S : SumTwo φ V W₀ W₁) (a : K) :
    L ≤ Subgroup.normalizer (S.graph a : Set H) := by
  refine le_normalizer_of_conj_mem fun l hl x hx => ?_
  obtain ⟨w, rfl⟩ := hx
  exact ⟨_, (S.conj_grHom a ⟨l, hl⟩ w).symm⟩

@[expose] def graphCoord (S : SumTwo φ V W₀ W₁) (a : K) : NatCoord φ (S.graph a) where
  θ := (MonoidHom.ofInjective (S.grHom_injective a)).symm.trans S.c₀.θ
  act l v := by
    obtain ⟨w, hw⟩ := (MonoidHom.ofInjective (S.grHom_injective a)).surjective v
    refine ⟨MonoidHom.ofInjective (S.grHom_injective a) (S.conjW l w), ?_, ?_⟩
    · rw [← hw, MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply, ← conj_grHom]
    · show S.c₀.θ ((MonoidHom.ofInjective (S.grHom_injective a)).symm
          (MonoidHom.ofInjective (S.grHom_injective a) (S.conjW l w))) =
        Multiplicative.ofAdd (mat φ l *ᵥ Multiplicative.toAdd (S.c₀.θ
          ((MonoidHom.ofInjective (S.grHom_injective a)).symm v)))
      rw [← hw, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, conjW,
        MulEquiv.apply_symm_apply]

theorem exists_graph [Finite H] (S : SumTwo φ V W₀ W₁) {J : Subgroup H} (hJV : J ≤ V)
    (hLJ : L ≤ Subgroup.normalizer (J : Set H)) (hcard : Nat.card J = Nat.card W₀)
    (h : J ⊓ W₁ = ⊥) : ∃ a : K, J = S.graph a := by
  have hJ1 : ∀ x ∈ J, x ∈ W₁ → x = 1 := fun x hx hx1 => by
    have : x ∈ J ⊓ W₁ := ⟨hx, hx1⟩
    rwa [h, Subgroup.mem_bot] at this
  have hd : ∀ j : ↥J, ∃ a : ↥W₀, ∃ b : ↥W₁, (a : H) * b = j := fun j => by
    obtain ⟨a, ha, b, hb, hab⟩ := S.decomp (hJV j.2)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  choose p₀ p₁ hp using hd
  have hinj : Function.Injective p₀ := by
    intro j j' hjj
    have h1 : (j' : H)⁻¹ * j = (p₁ j' : H)⁻¹ * p₁ j := by
      rw [← hp j, ← hp j', hjj]
      group
    have h2 : (j' : H)⁻¹ * j = 1 := hJ1 _ (J.mul_mem (J.inv_mem j'.2) j.2)
      (by rw [h1]; exact W₁.mul_mem (W₁.inv_mem (p₁ j').2) (p₁ j).2)
    exact Subtype.ext (inv_mul_eq_one.mp h2).symm
  have hbij : Function.Bijective p₀ := hinj.bijective_of_nat_card_le hcard.symm.le
  set e := Equiv.ofBijective p₀ hbij with he
  have hmem : ∀ w : ↥W₀, (w : H) * (p₁ (e.symm w) : H) ∈ J := fun w => by
    have h1 := hp (e.symm w)
    have h2 : p₀ (e.symm w) = w := e.apply_symm_apply w
    rw [h2] at h1
    rw [h1]
    exact (e.symm w).2
  have huniq : ∀ (w : ↥W₀) (b : H), b ∈ W₁ → (w : H) * b ∈ J → b = p₁ (e.symm w) := by
    intro w b hb hwb
    have h3 : b⁻¹ * (p₁ (e.symm w) : H) = ((w : H) * b)⁻¹ * ((w : H) * p₁ (e.symm w)) := by
      group
    have h4 : b⁻¹ * (p₁ (e.symm w) : H) = 1 := hJ1 _
      (by rw [h3]; exact J.mul_mem (J.inv_mem hwb) (hmem w))
      (W₁.mul_mem (W₁.inv_mem hb) (p₁ _).2)
    exact inv_mul_eq_one.mp h4
  set Fw : ↥W₀ → ↥W₁ := fun w => p₁ (e.symm w) with hFw
  have hFmul : ∀ w w' : ↥W₀, Fw (w * w') = Fw w * Fw w' := by
    intro w w'
    have hc := S.comm _ (S.le₁ (Fw w).2) _ (S.le₀ w'.2)
    refine Subtype.ext (huniq (w * w') _ (W₁.mul_mem (Fw w).2 (Fw w').2) ?_).symm
    have e1 : ((w * w' : ↥W₀) : H) * ((Fw w : H) * Fw w') =
        ((w : H) * Fw w) * ((w' : H) * Fw w') := by
      calc ((w * w' : ↥W₀) : H) * ((Fw w : H) * Fw w') =
            w * ((w' : H) * Fw w) * Fw w' := by simp only [Subgroup.coe_mul]; group
        _ = w * ((Fw w : H) * w') * Fw w' := by rw [hc]
        _ = ((w : H) * Fw w) * ((w' : H) * Fw w') := by group
    rw [e1]
    exact J.mul_mem (hmem w) (hmem w')
  have hFconj : ∀ (l : ↥L) (w : ↥W₀), (Fw (S.conjW l w) : H) = l * (Fw w : H) * (l : H)⁻¹ := by
    intro l w
    refine (huniq _ _ ((Subgroup.mem_normalizer_iff.mp (S.c₁.le_normalizer l.2) _).mp
      (Fw w).2) ?_).symm
    rw [coe_conjW, show (l : H) * w * (l : H)⁻¹ * ((l : H) * Fw w * (l : H)⁻¹) =
      l * ((w : H) * Fw w) * (l : H)⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp (hLJ l.2) _).mp (hmem w)
  let F : (Fin 3 → K) →+ (Fin 3 → K) := AddMonoidHom.mk'
    (fun x => Multiplicative.toAdd (S.c₁.θ (Fw (S.c₀.θ.symm (Multiplicative.ofAdd x)))))
    (fun x y => by
      show Multiplicative.toAdd (S.c₁.θ (Fw (S.c₀.θ.symm (Multiplicative.ofAdd (x + y))))) =
        Multiplicative.toAdd (S.c₁.θ (Fw (S.c₀.θ.symm (Multiplicative.ofAdd x)))) +
          Multiplicative.toAdd (S.c₁.θ (Fw (S.c₀.θ.symm (Multiplicative.ofAdd y))))
      rw [ofAdd_add, map_mul, hFmul, map_mul, toAdd_mul])
  obtain ⟨a, ha⟩ := commutant_SL3 F fun γ x => by
    obtain ⟨l, hl⟩ := exists_mat φ γ
    rw [← hl]
    show Multiplicative.toAdd (S.c₁.θ (Fw (S.c₀.θ.symm (Multiplicative.ofAdd (mat φ l *ᵥ x))))) =
      mat φ l *ᵥ Multiplicative.toAdd (S.c₁.θ (Fw (S.c₀.θ.symm (Multiplicative.ofAdd x))))
    set w := S.c₀.θ.symm (Multiplicative.ofAdd x) with hw
    have hx : S.c₀.θ.symm (Multiplicative.ofAdd (mat φ l *ᵥ x)) = S.conjW l w := by
      rw [conjW, hw, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hF : Fw (S.conjW l w) = S.c₁.θ.symm (Multiplicative.ofAdd
        (mat φ l *ᵥ Multiplicative.toAdd (S.c₁.θ (Fw w)))) := by
      apply Subtype.ext
      rw [hFconj, NatCoord.symm_mat, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    rw [hx, hF, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  refine ⟨a, ?_⟩
  have hle : J ≤ S.graph a := by
    intro j hj
    set w := p₀ ⟨j, hj⟩ with hw
    have hj' : e.symm w = ⟨j, hj⟩ := e.symm_apply_apply _
    have hFa : Fw w = S.gr a w := by
      apply S.c₁.θ.injective
      have := ha (Multiplicative.toAdd (S.c₀.θ w))
      simp only [F, AddMonoidHom.mk'_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply] at this
      rw [gr_apply, ← this, ofAdd_toAdd]
    refine ⟨w, ?_⟩
    show (w : H) * S.gr a w = j
    rw [← hFa]
    show (w : H) * (p₁ (e.symm w) : H) = j
    rw [hj', hp ⟨j, hj⟩]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [S.card_graph, hcard])

theorem eq_or_eq_graph [Finite H] (S : SumTwo φ V W₀ W₁) {J : Subgroup H} (hJV : J ≤ V)
    (hLJ : L ≤ Subgroup.normalizer (J : Set H)) (hcard : Nat.card J = Nat.card W₀) :
    J = W₁ ∨ ∃ a : K, J = S.graph a := by
  have hLJ1 : L ≤ Subgroup.normalizer ((J ⊓ W₁ : Subgroup H) : Set H) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLJ hl, S.c₁.le_normalizer hl⟩
  rcases S.c₁.eq_bot_or_eq inf_le_right hLJ1 with h | h
  · right
    exact S.exists_graph hJV hLJ hcard h
  · left
    have hW : W₁ ≤ J := by
      rw [← h]
      exact inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hW (by rw [hcard, S.card_eq])).symm

end SumTwo

end CFSG.Quasithin.Vol2.Ch10.V1C.A319
