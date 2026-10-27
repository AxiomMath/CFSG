module

public import CFSG.Quasithin.EmptyFaithful.S152SFam

public section

namespace CFSG.Quasithin

namespace S152S

section CentralProduct

variable {J : Type} [Group J]

@[expose] def mulHom (A B : Subgroup J) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A × B →* J where
  toFun p := (p.1 : J) * (p.2 : J)
  map_one' := by simp
  map_mul' p q := by
    have h := hc (q.1 : J) q.1.2 (p.2 : J) p.2.2
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    calc (p.1 : J) * (q.1 : J) * ((p.2 : J) * (q.2 : J))
        = (p.1 : J) * ((q.1 : J) * (p.2 : J)) * (q.2 : J) := by group
      _ = (p.1 : J) * ((p.2 : J) * (q.1 : J)) * (q.2 : J) := by rw [h]
      _ = (p.1 : J) * (p.2 : J) * ((q.1 : J) * (q.2 : J)) := by group

theorem mulHom_apply (A B : Subgroup J) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (a : A) (b : B) :
    mulHom A B hc (a, b) = (a : J) * (b : J) := rfl

theorem mulHom_surjective (A B : Subgroup J) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (htop : A ⊔ B = ⊤) : Function.Surjective (mulHom A B hc) := by
  have hA : A ≤ (mulHom A B hc).range := fun a ha => ⟨(⟨a, ha⟩, 1), by simp [mulHom_apply]⟩
  have hB : B ≤ (mulHom A B hc).range := fun b hb => ⟨(1, ⟨b, hb⟩), by simp [mulHom_apply]⟩
  have : (mulHom A B hc).range = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact sup_le hA hB
  exact MonoidHom.range_eq_top.1 this

theorem ker_mulHom_center (A B : Subgroup J) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (htop : A ⊔ B = ⊤) :
    ((QuotientGroup.mk' (Subgroup.center J)).comp (mulHom A B hc)).ker =
      (Subgroup.center A).prod (Subgroup.center B) := by
  have hsurj := mulHom_surjective A B hc htop
  ext ⟨a, b⟩
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_prod, mulHom_apply]
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h
    constructor
    · rw [Subgroup.mem_center_iff]
      intro a'
      have h1 := h (a' : J)
      have h2 : (b : J) * (a' : J) = (a' : J) * (b : J) := (hc a' a'.2 b b.2).symm
      apply Subtype.ext
      show (a' : J) * (a : J) = (a : J) * (a' : J)
      apply mul_right_cancel (b := (b : J))
      calc (a' : J) * (a : J) * (b : J) = (a' : J) * ((a : J) * (b : J)) := by group
        _ = (a : J) * (b : J) * (a' : J) := h1
        _ = (a : J) * ((b : J) * (a' : J)) := by group
        _ = (a : J) * ((a' : J) * (b : J)) := by rw [h2]
        _ = (a : J) * (a' : J) * (b : J) := by group
    · rw [Subgroup.mem_center_iff]
      intro b'
      have h1 := h (b' : J)
      have h2 : (a : J) * (b' : J) = (b' : J) * (a : J) := hc a a.2 b' b'.2
      apply Subtype.ext
      show (b' : J) * (b : J) = (b : J) * (b' : J)
      apply mul_left_cancel (a := (a : J))
      calc (a : J) * ((b' : J) * (b : J)) = ((a : J) * (b' : J)) * (b : J) := by group
        _ = ((b' : J) * (a : J)) * (b : J) := by rw [h2]
        _ = (b' : J) * ((a : J) * (b : J)) := by group
        _ = (a : J) * (b : J) * (b' : J) := h1
        _ = (a : J) * ((b : J) * (b' : J)) := by group
  · rintro ⟨ha, hb⟩
    rw [Subgroup.mem_center_iff] at ha hb ⊢
    intro j
    obtain ⟨⟨a', b'⟩, rfl⟩ := hsurj j
    rw [mulHom_apply]
    have e1 : (a' : J) * (a : J) = (a : J) * (a' : J) := congrArg Subtype.val (ha a')
    have e2 : (b' : J) * (b : J) = (b : J) * (b' : J) := congrArg Subtype.val (hb b')
    have e3 : (a : J) * (b' : J) = (b' : J) * (a : J) := hc a a.2 b' b'.2
    have e4 : (b : J) * (a' : J) = (a' : J) * (b : J) := (hc a' a'.2 b b.2).symm
    calc (a' : J) * (b' : J) * ((a : J) * (b : J))
        = (a' : J) * ((b' : J) * (a : J)) * (b : J) := by group
      _ = (a' : J) * ((a : J) * (b' : J)) * (b : J) := by rw [e3]
      _ = ((a' : J) * (a : J)) * ((b' : J) * (b : J)) := by group
      _ = ((a : J) * (a' : J)) * ((b : J) * (b' : J)) := by rw [e1, e2]
      _ = (a : J) * ((a' : J) * (b : J)) * (b' : J) := by group
      _ = (a : J) * ((b : J) * (a' : J)) * (b' : J) := by rw [e4]
      _ = (a : J) * (b : J) * ((a' : J) * (b' : J)) := by group

noncomputable def centralProductQuotEquiv (A B : Subgroup J) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (htop : A ⊔ B = ⊤) :
    (J ⧸ Subgroup.center J) ≃* (A ⧸ Subgroup.center A) × (B ⧸ Subgroup.center B) :=
  let ψ : A × B →* J ⧸ Subgroup.center J := (QuotientGroup.mk' (Subgroup.center J)).comp (mulHom A B hc)
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (mulHom_surjective A B hc htop)
  ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_mulHom_center A B hc htop))).trans
    (QuotientGroup.prodMulEquiv (Subgroup.center A) (Subgroup.center B))

private theorem quotientKerEquivOfSurjective_symm_apply
    {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f)
    (g : G) :
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f g) =
      QuotientGroup.mk' (MonoidHom.ker f) g := by
  rw [MulEquiv.symm_apply_eq]
  change f g = QuotientGroup.kerLift f (QuotientGroup.mk g)
  rw [QuotientGroup.kerLift_mk]

@[simp] theorem centralProductQuotEquiv_mk (A B : Subgroup J)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (htop : A ⊔ B = ⊤)
    (a : A) (b : B) :
    centralProductQuotEquiv A B hc htop
      (QuotientGroup.mk' (Subgroup.center J) ((a : J) * (b : J))) =
      (QuotientGroup.mk' (Subgroup.center A) a,
        QuotientGroup.mk' (Subgroup.center B) b) := by
  classical
  unfold centralProductQuotEquiv
  dsimp only
  set f : A × B →* J ⧸ Subgroup.center J :=
    (QuotientGroup.mk' (Subgroup.center J)).comp (mulHom A B hc) with hf_def
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (mulHom_surjective A B hc htop)
  change (QuotientGroup.prodMulEquiv (Subgroup.center A) (Subgroup.center B))
    ((QuotientGroup.quotientMulEquivOfEq (ker_mulHom_center A B hc htop))
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm
        (QuotientGroup.mk' (Subgroup.center J) ((a : J) * (b : J))))) =
      (QuotientGroup.mk' (Subgroup.center A) a,
        QuotientGroup.mk' (Subgroup.center B) b)
  rw [show QuotientGroup.mk' (Subgroup.center J) ((a : J) * (b : J)) = f (a, b) from rfl]
  rw [quotientKerEquivOfSurjective_symm_apply]
  change (QuotientGroup.prodMulEquiv (Subgroup.center A) (Subgroup.center B))
      ((QuotientGroup.quotientMulEquivOfEq (ker_mulHom_center A B hc htop))
        (QuotientGroup.mk ((a, b) : A × B))) =
    ((QuotientGroup.mk' (Subgroup.center A)) a, (QuotientGroup.mk' (Subgroup.center B)) b)
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rw [QuotientGroup.prodMulEquiv_apply]
  rfl

end CentralProduct

section CenterEquiv

noncomputable def quotCenterEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩ g
      have := hx (e.symm g)
      have h2 := congrArg e this
      simpa using h2
    · intro hy
      refine ⟨e.symm y, fun g => ?_, by simp⟩
      have := hy (e g)
      have h2 := congrArg e.symm this
      simpa using h2)

@[simp] theorem quotCenterEquiv_mk {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (a : A) :
    quotCenterEquiv e (QuotientGroup.mk' (Subgroup.center A) a) =
      QuotientGroup.mk' (Subgroup.center B) (e a) := by
  rw [quotCenterEquiv]
  exact QuotientGroup.congr_mk (G' := Subgroup.center A) (H' := Subgroup.center B) e _ a

end CenterEquiv

end S152S

open S152S

theorem BTProps.of_central_product {J : Type} [Group J] [Finite J] (A B : Subgroup J)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (htop : A ⊔ B = ⊤)
    (hA : BTProps (A ⧸ Subgroup.center A)) (hB : BTProps (B ⧸ Subgroup.center B)) :
    BTProps (J ⧸ Subgroup.center J) :=
  BTProps.of_mulEquiv (centralProductQuotEquiv A B hc htop).symm (BTProps.prod hA hB)

end CFSG.Quasithin
