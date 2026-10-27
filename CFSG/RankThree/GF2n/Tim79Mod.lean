module

import CFSG.RankThree.GF2n.NaturalDecomp
import CFSG.RankThree.GF2n.Tim79Hom
public import CFSG.Timmesfeld.RankOne.Defs

public section

namespace CFSG.RankThree.GF2n.Tim79

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS

open scoped commutatorElement

theorem eq_zero_of_equivariant_biadditive {K V : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) [AddCommGroup V] [Finite V]
    [DistribMulAction (SpecialLinearGroup (Fin 2) K) V]
    (hfix : ∀ v : V, (∀ x : SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0)
    (hquad : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : V,
      a' • (a • v - v) = a • v - v)
    {L : AddSubgroup V} (hL : ∀ w ∈ L, ∀ a ∈ upperUnipotent K, a • w = w)
    (hgen : ∀ U : AddSubgroup V, (∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) →
      L ≤ U → U = ⊤)
    (b : V →+ V →+ (Fin 2 → K))
    (hb : ∀ (g : SpecialLinearGroup (Fin 2) K) (x y : V),
      b (g • x) (g • y) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ b x y) : b = 0 := by
  obtain ⟨s, -, hsup, hs⟩ := exists_supIndep_natural hfix hquad hL hgen
  have h2 : ∀ W₁ ∈ s, ∀ W₂ ∈ s, ∀ x ∈ W₁, ∀ y ∈ W₂, b x y = 0 := by
    intro W₁ hW₁ W₂ hW₂ x hx y hy
    obtain ⟨-, -, -, θ₁, -, hr₁, hθ₁⟩ := hs W₁ hW₁
    obtain ⟨-, -, -, θ₂, -, hr₂, hθ₂⟩ := hs W₂ hW₂
    let f : (Fin 2 → K) →+ (Fin 2 → K) →+ (Fin 2 → K) :=
      AddMonoidHom.mk' (fun v => (b (θ₁ v)).comp θ₂) (fun v v' => by
        ext w i
        simp [map_add])
    have hf : ∀ (g : SpecialLinearGroup (Fin 2) K) (v w : Fin 2 → K),
        f ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) =
          (g : Matrix (Fin 2) (Fin 2) K) *ᵥ f v w := by
      intro g v w
      show b (θ₁ _) (θ₂ _) = _
      rw [hθ₁, hθ₂, hb]
      rfl
    have h0 := equivariant_biadditive_eq_zero hK f hf
    rw [← hr₁] at hx
    rw [← hr₂] at hy
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    have := congrArg (fun F : (Fin 2 → K) →+ (Fin 2 → K) →+ (Fin 2 → K) => F v w) h0
    simpa [f] using this
  have h1 : ∀ W₁ ∈ s, ∀ x ∈ W₁, b x = 0 := by
    intro W₁ hW₁ x hx
    have hle : s.sup id ≤ (b x).ker := Finset.sup_le fun W₂ hW₂ y hy =>
      AddMonoidHom.mem_ker.mpr (h2 W₁ hW₁ W₂ hW₂ x hx y hy)
    rw [hsup] at hle
    ext y i
    have := AddMonoidHom.mem_ker.mp (hle (AddSubgroup.mem_top y))
    simp [this]
  have hle : s.sup id ≤ b.ker := Finset.sup_le fun W₁ hW₁ x hx =>
    AddMonoidHom.mem_ker.mpr (h1 W₁ hW₁ x hx)
  rw [hsup] at hle
  ext x y i
  have := AddMonoidHom.mem_ker.mp (hle (AddSubgroup.mem_top x))
  simp [this]


section Quotient

variable {Γ : Type*} [Group Γ] {K : Type*} [Field K]

private structure ModData (φ : Γ →* SpecialLinearGroup (Fin 2) K) (C Lγ : Subgroup Γ) : Prop where
  surj : Function.Surjective φ
  le : Lγ ≤ C
  cn : ∀ z : Γ, ∀ c ∈ C, z * c * z⁻¹ ∈ C
  ln : ∀ z : Γ, ∀ l ∈ Lγ, z * l * z⁻¹ ∈ Lγ
  comm : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ Lγ
  ker : ∀ z : Γ, φ z = 1 → ∀ c ∈ C, ⁅z, c⁆ ∈ Lγ

variable {φ : Γ →* SpecialLinearGroup (Fin 2) K} {C Lγ : Subgroup Γ}

private theorem ModData.normal (h : ModData φ C Lγ) : (Lγ.subgroupOf C).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.ln g n hn

private def Qmod (_h : ModData φ C Lγ) : Type _ := Additive (↥C ⧸ Lγ.subgroupOf C)

private noncomputable instance (h : ModData φ C Lγ) : AddCommGroup (Qmod h) :=
  letI : (Lγ.subgroupOf C).Normal := h.normal
  letI : CommGroup (↥C ⧸ Lγ.subgroupOf C) :=
    { (inferInstance : Group (↥C ⧸ Lγ.subgroupOf C)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have := h.comm (b⁻¹ : ↥C) (b⁻¹).2 (a⁻¹ : ↥C) (a⁻¹).2
        convert this using 1
        simp [commutatorElement_def, mul_assoc] }
  inferInstanceAs (AddCommGroup (Additive (↥C ⧸ Lγ.subgroupOf C)))

private instance [Finite Γ] (h : ModData φ C Lγ) : Finite (Qmod h) :=
  inferInstanceAs (Finite (Additive (↥C ⧸ Lγ.subgroupOf C)))

private def Qmod.mk (h : ModData φ C Lγ) (c : ↥C) : Qmod h :=
  Additive.ofMul (QuotientGroup.mk c : ↥C ⧸ Lγ.subgroupOf C)


private theorem Qmod.mk_mul (h : ModData φ C Lγ) (a b : ↥C) :
    Qmod.mk h (a * b) = Qmod.mk h a + Qmod.mk h b := rfl

private theorem Qmod.mk_one (h : ModData φ C Lγ) : Qmod.mk h 1 = 0 := rfl

private theorem Qmod.mk_surjective (h : ModData φ C Lγ) :
    Function.Surjective (Qmod.mk h) := fun v =>
  let ⟨c, hc⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  ⟨c, by simp only [Qmod.mk, hc]; rfl⟩

private theorem Qmod.mk_eq_mk_iff (h : ModData φ C Lγ) (a b : ↥C) :
    Qmod.mk h a = Qmod.mk h b ↔ (a : Γ)⁻¹ * b ∈ Lγ := by
  letI : (Lγ.subgroupOf C).Normal := h.normal
  have e : Qmod.mk h a = Qmod.mk h b ↔
      (QuotientGroup.mk a : ↥C ⧸ Lγ.subgroupOf C) = QuotientGroup.mk b :=
    ⟨fun hab => Additive.ofMul.injective hab, fun hab => congrArg Additive.ofMul hab⟩
  rw [e, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

private theorem Qmod.mk_eq_zero_iff (h : ModData φ C Lγ) (c : ↥C) :
    Qmod.mk h c = 0 ↔ (c : Γ) ∈ Lγ := by
  rw [← Qmod.mk_one h, Qmod.mk_eq_mk_iff]
  simp

private def cjC (h : ModData φ C Lγ) (z : Γ) : ↥C →* ↥C where
  toFun c := ⟨z * c * z⁻¹, h.cn z c c.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

private noncomputable def actM [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ) (z : Γ) :
    (↥C ⧸ Lγ.subgroupOf C) →* (↥C ⧸ Lγ.subgroupOf C) :=
  QuotientGroup.map _ _ (cjC h z) (fun n hn => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    simpa [cjC] using h.ln z n hn)

private theorem actM_mk [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ) (z : Γ) (c : ↥C) :
    actM h z (QuotientGroup.mk c) = QuotientGroup.mk (cjC h z c) := rfl

private theorem actM_mul [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ) (z z' : Γ)
    (x : ↥C ⧸ Lγ.subgroupOf C) : actM h (z * z') x = actM h z (actM h z' x) := by
  induction x using QuotientGroup.induction_on with | H c => ?_
  rw [actM_mk, actM_mk, actM_mk]
  congr 1
  ext
  simp [cjC, mul_assoc]

private theorem actM_one [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ)
    (x : ↥C ⧸ Lγ.subgroupOf C) :
    actM h 1 x = x := by
  induction x using QuotientGroup.induction_on with | H c => ?_
  rw [actM_mk]
  congr 1
  ext
  simp [cjC]

private theorem actM_eq [(Lγ.subgroupOf C).Normal] (h : ModData φ C Lγ) {z z' : Γ} (hz : φ z = φ z')
    (x : ↥C ⧸ Lγ.subgroupOf C) : actM h z x = actM h z' x := by
  induction x using QuotientGroup.induction_on with | H c => ?_
  rw [actM_mk, actM_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hw : φ (z⁻¹ * z') = 1 := by rw [map_mul, map_inv, hz, inv_mul_cancel]
  have h1 := h.ker (z⁻¹ * z') hw ((c : Γ)⁻¹) (inv_mem c.2)
  have h2 := h.ln z _ (inv_mem h1)
  convert h2 using 1
  simp only [cjC, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
    commutatorElement_def]
  group

private noncomputable def Qmod.smul' (h : ModData φ C Lγ) (g : SpecialLinearGroup (Fin 2) K)
    (v : Qmod h) : Qmod h :=
  letI : (Lγ.subgroupOf C).Normal := h.normal
  Additive.ofMul (actM h (Classical.choose (h.surj g)) (Additive.toMul v))

private noncomputable instance (h : ModData φ C Lγ) :
    DistribMulAction (SpecialLinearGroup (Fin 2) K) (Qmod h) where
  smul := Qmod.smul' h
  one_smul v := by
    letI : (Lγ.subgroupOf C).Normal := h.normal
    show Additive.ofMul (actM h (Classical.choose (h.surj 1)) (Additive.toMul v)) = v
    rw [actM_eq h (z' := 1) (by rw [Classical.choose_spec (h.surj 1), map_one]), actM_one]
    rfl
  mul_smul g₁ g₂ v := by
    letI : (Lγ.subgroupOf C).Normal := h.normal
    show Additive.ofMul (actM h (Classical.choose (h.surj (g₁ * g₂))) (Additive.toMul v)) =
      Additive.ofMul (actM h (Classical.choose (h.surj g₁))
        (actM h (Classical.choose (h.surj g₂)) (Additive.toMul v)))
    rw [actM_eq h (z' := Classical.choose (h.surj g₁) * Classical.choose (h.surj g₂)) (by
      rw [map_mul, Classical.choose_spec (h.surj g₁), Classical.choose_spec (h.surj g₂),
        Classical.choose_spec (h.surj (g₁ * g₂))]), actM_mul]
  smul_zero g := by
    letI : (Lγ.subgroupOf C).Normal := h.normal
    show Additive.ofMul (actM h _ (Additive.toMul (0 : Qmod h))) = 0
    rw [show Additive.toMul (0 : Qmod h) = 1 from rfl, map_one]
    rfl
  smul_add g v w := by
    letI : (Lγ.subgroupOf C).Normal := h.normal
    show Additive.ofMul (actM h _ (Additive.toMul (v + w))) = _
    rw [show Additive.toMul (v + w) = Additive.toMul v * Additive.toMul w from rfl, map_mul]
    rfl

private theorem Qmod.smul_mk (h : ModData φ C Lγ) (z : Γ) (c : ↥C) :
    φ z • Qmod.mk h c = Qmod.mk h (cjC h z c) := by
  letI : (Lγ.subgroupOf C).Normal := h.normal
  show Additive.ofMul (actM h (Classical.choose (h.surj (φ z))) (QuotientGroup.mk c)) = _
  rw [actM_eq h (z' := z) (Classical.choose_spec (h.surj (φ z))), actM_mk]
  rfl

private theorem Qmod.mk_inv (h : ModData φ C Lγ) (a : ↥C) : Qmod.mk h a⁻¹ = - Qmod.mk h a := by
  have := Qmod.mk_mul h a a⁻¹
  rw [mul_inv_cancel, Qmod.mk_one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

private theorem Qmod.mk_cjC_eq_iff (h : ModData φ C Lγ) (z : Γ) (c : ↥C) :
    Qmod.mk h (cjC h z c) = Qmod.mk h c ↔ ⁅z, (c : Γ)⁆ ∈ Lγ := by
  have e : ((cjC h z c * c⁻¹ : ↥C) : Γ) = ⁅z, (c : Γ)⁆ := by
    simp [cjC, commutatorElement_def]
  rw [← e, ← Qmod.mk_eq_zero_iff h, Qmod.mk_mul, Qmod.mk_inv, add_neg_eq_zero]

end Quotient

section Main

variable {Γ : Type*} [Group Γ] [Finite Γ] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_zero_of_equivariant_pairing
    (hK : 4 ≤ Nat.card K) (φ : Γ →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφ : Function.Surjective φ) (C Lγ C₁ : Subgroup Γ) (hLC₁ : Lγ ≤ C₁) (hC₁C : C₁ ≤ C)
    (hCn : ∀ z : Γ, ∀ c ∈ C, z * c * z⁻¹ ∈ C) (hLn : ∀ z : Γ, ∀ l ∈ Lγ, z * l * z⁻¹ ∈ Lγ)
    (hcomm : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ Lγ)
    (hker : ∀ z : Γ, φ z = 1 → ∀ c ∈ C, ⁅z, c⁆ ∈ Lγ)
    (hfix : ∀ c ∈ C, (∀ z : Γ, ⁅z, c⁆ ∈ Lγ) → c ∈ Lγ)
    (hquad : ∀ x x' : Γ, φ x ∈ upperUnipotent K → φ x' ∈ upperUnipotent K →
      ∀ c ∈ C, ⁅x', ⁅x, c⁆⁆ ∈ Lγ)
    (hL : ∀ c ∈ C₁, ∀ x : Γ, φ x ∈ upperUnipotent K → ⁅x, c⁆ ∈ Lγ)
    (hgen : ∀ S : Subgroup Γ, Lγ ≤ S → S ≤ C → (∀ z : Γ, ∀ s ∈ S, z * s * z⁻¹ ∈ S) →
      C₁ ≤ S → S = C)
    (β : Γ → Γ → (Fin 2 → K))
    (hβ₁ : ∀ a ∈ C, ∀ a' ∈ C, ∀ b ∈ C, β (a * a') b = β a b + β a' b)
    (hβ₂ : ∀ a ∈ C, ∀ b ∈ C, ∀ b' ∈ C, β a (b * b') = β a b + β a b')
    (hβL₁ : ∀ l ∈ Lγ, ∀ b ∈ C, β l b = 0) (hβL₂ : ∀ a ∈ C, ∀ l ∈ Lγ, β a l = 0)
    (hβeq : ∀ z : Γ, ∀ a ∈ C, ∀ b ∈ C,
      β (z * a * z⁻¹) (z * b * z⁻¹) = (φ z : Matrix (Fin 2) (Fin 2) K) *ᵥ β a b) :
    ∀ a ∈ C, ∀ b ∈ C, β a b = 0 := by
  have hd : ModData φ C Lγ := ⟨hφ, hLC₁.trans hC₁C, hCn, hLn, hcomm, hker⟩
  let Lt : AddSubgroup (Qmod hd) :=
    { carrier := {v | ∃ c : ↥C, (c : Γ) ∈ C₁ ∧ Qmod.mk hd c = v}
      zero_mem' := ⟨1, C₁.one_mem, Qmod.mk_one hd⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, C₁.mul_mem ha hb, Qmod.mk_mul hd a b⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, C₁.inv_mem ha, Qmod.mk_inv hd a⟩ }
  have hfix' : ∀ v : Qmod hd, (∀ x : Matrix.SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0 := by
    intro v hv
    obtain ⟨c, rfl⟩ := Qmod.mk_surjective hd v
    rw [Qmod.mk_eq_zero_iff]
    refine hfix c c.2 (fun z => ?_)
    exact (Qmod.mk_cjC_eq_iff hd z c).mp (by rw [← Qmod.smul_mk]; exact hv (φ z))
  have hquad' : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : Qmod hd,
      a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨x', rfl⟩ := hφ a'
    obtain ⟨c, rfl⟩ := Qmod.mk_surjective hd v
    have e : φ x • Qmod.mk hd c - Qmod.mk hd c = Qmod.mk hd (cjC hd x c * c⁻¹) := by
      rw [Qmod.smul_mk, Qmod.mk_mul, Qmod.mk_inv, sub_eq_add_neg]
    rw [e, Qmod.smul_mk]
    refine (Qmod.mk_cjC_eq_iff hd x' (cjC hd x c * c⁻¹)).mpr ?_
    have := hquad x x' ha ha' c c.2
    simpa [cjC, commutatorElement_def, mul_assoc] using this
  have hL' : ∀ w ∈ Lt, ∀ a ∈ upperUnipotent K, a • w = w := by
    rintro _ ⟨c, hc, rfl⟩ a ha
    obtain ⟨x, rfl⟩ := hφ a
    rw [Qmod.smul_mk]
    exact (Qmod.mk_cjC_eq_iff hd x c).mpr (hL c hc x ha)
  have hgen' : ∀ U : AddSubgroup (Qmod hd),
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) → Lt ≤ U → U = ⊤ := by
    intro U hU hLU
    let S : Subgroup Γ :=
      { carrier := {z | ∃ hz : z ∈ C, Qmod.mk hd ⟨z, hz⟩ ∈ U}
        one_mem' := ⟨C.one_mem, by
          have e : (⟨1, C.one_mem⟩ : ↥C) = 1 := rfl
          rw [e, Qmod.mk_one hd]
          exact U.zero_mem⟩
        mul_mem' := by
          rintro a b ⟨ha, haU⟩ ⟨hb, hbU⟩
          exact ⟨C.mul_mem ha hb, by
            have := U.add_mem haU hbU
            rwa [← Qmod.mk_mul hd ⟨a, ha⟩ ⟨b, hb⟩] at this⟩
        inv_mem' := by
          rintro a ⟨ha, haU⟩
          exact ⟨C.inv_mem ha, by
            have := U.neg_mem haU
            rwa [← Qmod.mk_inv hd ⟨a, ha⟩] at this⟩ }
    have hS : S = C := by
      refine hgen S (fun l hl => ⟨hd.le hl, ?_⟩) (fun z hz => hz.1) (fun z s hs => ?_)
        (fun c hc => ⟨hC₁C hc, hLU ⟨⟨c, hC₁C hc⟩, hc, rfl⟩⟩)
      · have : Qmod.mk hd ⟨l, hd.le hl⟩ = 0 := (Qmod.mk_eq_zero_iff hd _).mpr hl
        rw [this]
        exact U.zero_mem
      · obtain ⟨hsC, hsU⟩ := hs
        refine ⟨hCn z s hsC, ?_⟩
        have := hU (φ z) _ hsU
        rwa [Qmod.smul_mk] at this
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, rfl⟩ := Qmod.mk_surjective hd v
    have hc : (c : Γ) ∈ S := by
      rw [hS]
      exact c.2
    obtain ⟨hcC, hcU⟩ := hc
    exact hcU
  choose rep hrep using Qmod.mk_surjective hd
  have hcongr₁ : ∀ a a' b : ↥C, Qmod.mk hd a = Qmod.mk hd a' → β a b = β a' b := by
    intro a a' b hab
    have hl : (a : Γ)⁻¹ * a' ∈ Lγ := (Qmod.mk_eq_mk_iff hd a a').mp hab
    have e : (a' : Γ) = a * ((a : Γ)⁻¹ * a') := by group
    rw [e, hβ₁ a a.2 _ (hd.le hl |> fun h => C.mul_mem (C.inv_mem a.2) a'.2) b b.2,
      hβL₁ _ hl b b.2, add_zero]
  have hcongr₂ : ∀ a b b' : ↥C, Qmod.mk hd b = Qmod.mk hd b' → β a b = β a b' := by
    intro a b b' hbb
    have hl : (b : Γ)⁻¹ * b' ∈ Lγ := (Qmod.mk_eq_mk_iff hd b b').mp hbb
    have e : (b' : Γ) = b * ((b : Γ)⁻¹ * b') := by group
    rw [e, hβ₂ a a.2 b b.2 _ (C.mul_mem (C.inv_mem b.2) b'.2), hβL₂ a a.2 _ hl, add_zero]
  have hb₂ : ∀ v w w' : Qmod hd,
      β (rep v) (rep (w + w')) = β (rep v) (rep w) + β (rep v) (rep w') := by
    intro v w w'
    have h1 : Qmod.mk hd (rep (w + w')) = Qmod.mk hd (rep w * rep w') := by
      rw [Qmod.mk_mul, hrep, hrep, hrep]
    rw [hcongr₂ _ _ _ h1]
    exact hβ₂ _ (rep v).2 _ (rep w).2 _ (rep w').2
  have hb₁ : ∀ v v' w : Qmod hd,
      β (rep (v + v')) (rep w) = β (rep v) (rep w) + β (rep v') (rep w) := by
    intro v v' w
    have h1 : Qmod.mk hd (rep (v + v')) = Qmod.mk hd (rep v * rep v') := by
      rw [Qmod.mk_mul, hrep, hrep, hrep]
    rw [hcongr₁ _ _ _ h1]
    exact hβ₁ _ (rep v).2 _ (rep v').2 _ (rep w).2
  let b : Qmod hd →+ Qmod hd →+ (Fin 2 → K) :=
    AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun w => β (rep v) (rep w)) (hb₂ v))
      (fun v v' => AddMonoidHom.ext fun w => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
        exact hb₁ v v' w)
  have hbeq : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (x y : Qmod hd),
      b (g • x) (g • y) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ b x y := by
    intro g x y
    obtain ⟨z, rfl⟩ := hφ g
    have hx : φ z • x = Qmod.mk hd (cjC hd z (rep x)) := by
      conv_lhs => rw [← hrep x]
      exact Qmod.smul_mk hd z (rep x)
    have hy : φ z • y = Qmod.mk hd (cjC hd z (rep y)) := by
      conv_lhs => rw [← hrep y]
      exact Qmod.smul_mk hd z (rep y)
    show β (rep (φ z • x)) (rep (φ z • y)) = _
    rw [hcongr₁ (rep (φ z • x)) (cjC hd z (rep x)) _ (by rw [hrep, hx]),
      hcongr₂ (cjC hd z (rep x)) (rep (φ z • y)) (cjC hd z (rep y)) (by rw [hrep, hy])]
    exact hβeq z _ (rep x).2 _ (rep y).2
  have h0 := eq_zero_of_equivariant_biadditive hK (V := Qmod hd) hfix' hquad' (L := Lt) hL' hgen'
    b hbeq
  intro a ha a' ha'
  have e : β a a' = b (Qmod.mk hd ⟨a, ha⟩) (Qmod.mk hd ⟨a', ha'⟩) := by
    show β a a' = β (rep (Qmod.mk hd ⟨a, ha⟩)) (rep (Qmod.mk hd ⟨a', ha'⟩))
    rw [hcongr₁ (rep (Qmod.mk hd ⟨a, ha⟩)) ⟨a, ha⟩ _ (hrep _),
      hcongr₂ ⟨a, ha⟩ (rep (Qmod.mk hd ⟨a', ha'⟩)) ⟨a', ha'⟩ (hrep _)]
  rw [e, h0]
  rfl

end Main


end CFSG.RankThree.GF2n.Tim79
