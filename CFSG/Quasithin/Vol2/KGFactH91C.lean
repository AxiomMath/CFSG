module

public import CFSG.Quasithin.Vol2.KGFactH91B
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.KGH91

open Matrix CFSG.Quasithin.SLnTwo CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm
open scoped Pointwise

variable {G : Type} [Group G] {n : ℕ}

theorem mem_map_conj {W : Subgroup G} {m x : G} :
    x ∈ W.map (MulAut.conj m).toMonoidHom ↔ m⁻¹ * x * m ∈ W := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : m⁻¹ * ((MulAut.conj m).toMonoidHom y) * m = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro h
    refine ⟨m⁻¹ * x * m, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_eq_iff {W W' : Subgroup G} {m : G} :
    W.map (MulAut.conj m).toMonoidHom = W' ↔ ∀ a, a ∈ W ↔ m * a * m⁻¹ ∈ W' := by
  constructor
  · intro h a
    rw [← h, mem_map_conj]
    have : m⁻¹ * (m * a * m⁻¹) * m = a := by group
    rw [this]
  · intro h
    ext x
    rw [mem_map_conj, h]
    have : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rw [this]

@[expose] noncomputable def conjHom {L : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) : ↥L →* ↥L where
  toFun l := ⟨m⁻¹ * l * m, by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hm) l).1 l.2
    rwa [inv_inv] at this⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjHom_coe {L : Subgroup G} {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (l : ↥L) : ((conjHom hm l : ↥L) : G) = m⁻¹ * l * m := rfl

theorem conjHom_surjective {L : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) : Function.Surjective (conjHom hm) := fun l =>
  ⟨⟨m * l * m⁻¹, (Subgroup.mem_normalizer_iff.1 hm l).1 l.2⟩,
    Subtype.ext (by rw [conjHom_coe]; group)⟩

namespace NatCoord

variable {L W : Subgroup G}

@[expose] noncomputable def conjugate (C : NatCoord L W n) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    NatCoord L (W.map (MulAut.conj m).toMonoidHom) n where
  E g := C.E (m⁻¹ * g * m)
  ρ := C.ρ.comp (conjHom hm)
  le l hl := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_map_conj, mem_map_conj]
    have h1 : m⁻¹ * (l * x * l⁻¹) * m = ((conjHom hm ⟨l, hl⟩ : ↥L) : G) * (m⁻¹ * x * m) *
        ((conjHom hm ⟨l, hl⟩ : ↥L) : G)⁻¹ := by
      rw [conjHom_coe]
      group
    rw [h1]
    exact Subgroup.mem_normalizer_iff.1 (C.le (conjHom hm ⟨l, hl⟩).2) _
  map_mul a ha b hb := by
    rw [mem_map_conj] at ha hb
    have : m⁻¹ * (a * b) * m = (m⁻¹ * a * m) * (m⁻¹ * b * m) := by group
    rw [this, C.map_mul _ ha _ hb]
  inj a ha b hb h := by
    rw [mem_map_conj] at ha hb
    have := C.inj _ ha _ hb h
    calc a = m * (m⁻¹ * a * m) * m⁻¹ := by group
      _ = m * (m⁻¹ * b * m) * m⁻¹ := by rw [this]
      _ = b := by group
  surj x := by
    have h : m⁻¹ * (m * C.inv x * m⁻¹) * m = C.inv x := by group
    refine ⟨m * C.inv x * m⁻¹, ?_, ?_⟩
    · rw [mem_map_conj, h]
      exact C.inv_mem x
    · show C.E (m⁻¹ * (m * C.inv x * m⁻¹) * m) = x
      rw [h, C.E_inv]
  conj l a ha := by
    rw [mem_map_conj] at ha
    show C.E (m⁻¹ * ((l : G) * a * (l : G)⁻¹) * m) =
      (C.ρ (conjHom hm l) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ C.E (m⁻¹ * a * m)
    have h1 : m⁻¹ * ((l : G) * a * (l : G)⁻¹) * m = ((conjHom hm l : ↥L) : G) *
        (m⁻¹ * a * m) * ((conjHom hm l : ↥L) : G)⁻¹ := by
      rw [conjHom_coe]
      group
    rw [h1, C.conj _ _ ha]
  ρ_surj := C.ρ_surj.comp (conjHom_surjective hm)

theorem card_eq (C : NatCoord L W n) : Nat.card ↥W = Nat.card (Fin n → ZMod 2) :=
  Nat.card_congr
    { toFun := fun a => C.E a
      invFun := fun x => ⟨C.inv x, C.inv_mem x⟩
      left_inv := fun a => Subtype.ext (C.inv_E a.2)
      right_inv := fun x => C.E_inv x }

theorem conj_eq_of_ρ_eq_one (C : NatCoord L W n) {l : ↥L} (hl : C.ρ l = 1) {a : G}
    (ha : a ∈ W) : (l : G) * a * (l : G)⁻¹ = a :=
  C.inj _ (C.conj_mem l ha) a ha (by
    rw [C.conj l a ha, hl, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec])

end NatCoord

noncomputable def proj (A B : Subgroup G) (v : G) : G :=
  open Classical in
  if h : ∃ b ∈ B, v * b⁻¹ ∈ A then h.choose else 1

theorem proj_mul_eq {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    proj A B (a * b) = b := by
  have h : ∃ b' ∈ B, a * b * b'⁻¹ ∈ A := ⟨b, hb, by rw [mul_inv_cancel_right]; exact ha⟩
  rw [proj, dite_eq_left h]
  obtain ⟨hb', ha'⟩ := h.choose_spec
  have h1 : b * h.choose⁻¹ ∈ A := by
    have := A.mul_mem (A.inv_mem ha) ha'
    rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul] at this
  have h2 : b * h.choose⁻¹ ∈ A ⊓ B := ⟨h1, B.mul_mem hb (B.inv_mem hb')⟩
  rw [hAB, Subgroup.mem_bot, mul_inv_eq_one] at h2
  exact h2.symm

theorem card_lt_card_mulAut (hn : 3 ≤ n) :
    Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) <
      Nat.card (MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) := by
  classical
  have : Finite (MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) :=
    Finite.of_injective (fun f : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) => (f : _ → _))
      DFunLike.coe_injective
  have := Fintype.ofFinite (MulAut (SpecialLinearGroup (Fin n) (ZMod 2)))
  have hinj : Function.Injective
      (MulAut.conj : SpecialLinearGroup (Fin n) (ZMod 2) →*
        MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    refine eq_one_of_forall_commute_SL fun g => ?_
    have hg := congrArg (fun f : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) => f g) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    calc z * g = (z * g * z⁻¹) * z := by group
      _ = g * z := by rw [hg]
  have hns : ¬ Function.Surjective
      (MulAut.conj : SpecialLinearGroup (Fin n) (ZMod 2) →*
        MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) := by
    intro hs
    obtain ⟨z, hz⟩ := hs (slGraphAut n (ZMod 2))
    obtain ⟨g, hg⟩ := graph_ne_conj hn (Matrix.SpecialLinearGroup.toGL z)
    apply hg
    rw [← hz]
    apply Subtype.ext
    rw [coe_slConjugation, MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ← _root_.map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective _ hinj hns

structure Setting (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) where
  hyp : Hyp121 G T L V V₁ V₂ n
  C₁ : NatCoord L V₁ n
  C₂ : NatCoord L V₂ n
  dual : ∀ l, C₂.ρ l = slGraphAut n (ZMod 2) (C₁.ρ l)

theorem Setting.nonempty [Finite G] {T L V V₁ V₂ : Subgroup G}
    (hyp : Hyp121 G T L V V₁ V₂ n) : Nonempty (Setting G T L V V₁ V₂ n) := by
  obtain ⟨C₁, C₂, h⟩ := exists_dualCoord hyp
  exact ⟨⟨hyp, C₁, C₂, h⟩⟩

namespace Setting

variable [Finite G] {T L V V₁ V₂ : Subgroup G} (S : Setting G T L V V₁ V₂ n)
include S

theorem hn : 3 ≤ n := by rcases S.hyp.rank with h | h <;> omega

theorem le₁ : V₁ ≤ V := S.hyp.sup ▸ le_sup_left

theorem le₂ : V₂ ≤ V := S.hyp.sup ▸ le_sup_right

theorem comm {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a := by
  obtain ⟨_, hE, -⟩ := S.hyp.reduced
  have h := hE.toIsMulCommutative.is_comm.comm
    (⟨⟨a, S.hyp.le ha⟩, Subgroup.mem_subgroupOf.mpr ha⟩ :
      ↥(V.subgroupOf (Subgroup.normalizer (L : Set G))))
    ⟨⟨b, S.hyp.le hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩
  exact congrArg (fun z : ↥(V.subgroupOf (Subgroup.normalizer (L : Set G))) =>
    ((z : ↥(Subgroup.normalizer (L : Set G))) : G)) h

theorem conj_mem {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) {v : G} (hv : v ∈ V) :
    m * v * m⁻¹ ∈ V := by
  obtain ⟨hN, -, -⟩ := S.hyp.reduced
  have := hN.conj_mem ⟨v, S.hyp.le hv⟩ (Subgroup.mem_subgroupOf.mpr hv) ⟨m, hm⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem le_normalizer : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => S.conj_mem hm hv, fun hv => ?_⟩
  have := S.conj_mem (Subgroup.inv_mem _ hm) hv
  have e : m⁻¹ * (m * v * m⁻¹) * m⁻¹⁻¹ = v := by group
  rwa [e] at this

theorem exists_decomp {v : G} (hv : v ∈ V) : ∃ a ∈ V₁, ∃ c ∈ V₂, v = a * c := by
  have hle : V₁ ≤ Subgroup.normalizer (V₂ : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have haV := S.le₁ ha
    constructor
    · intro hx
      rwa [S.comm haV (S.le₂ hx), mul_inv_cancel_right]
    · intro hx
      have hxV : x ∈ V := by
        have := V.mul_mem (V.mul_mem (V.inv_mem haV) (S.le₂ hx)) haV
        have e : a⁻¹ * (a * x * a⁻¹) * a = x := by group
        rwa [e] at this
      rwa [S.comm haV hxV, mul_inv_cancel_right] at hx
  have h := Subgroup.coe_mul_of_left_le_normalizer_right V₁ V₂ hle
  rw [S.hyp.sup] at h
  have hv' : v ∈ (V₁ : Set G) * (V₂ : Set G) := by
    rw [← h]
    exact hv
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.1 hv'
  exact ⟨a, ha, c, hc, rfl⟩

theorem exists_decomp' {v : G} (hv : v ∈ V) : ∃ c ∈ V₂, ∃ a ∈ V₁, v = c * a := by
  obtain ⟨a, ha, c, hc, rfl⟩ := S.exists_decomp hv
  exact ⟨c, hc, a, ha, S.comm (S.le₁ ha) (S.le₂ hc)⟩

theorem decomp_unique {a a' c c' : G} (ha : a ∈ V₁) (ha' : a' ∈ V₁) (hc : c ∈ V₂)
    (hc' : c' ∈ V₂) (h : a * c = a' * c') : a = a' ∧ c = c' := by
  have e : a'⁻¹ * a = c' * c⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * c) * c⁻¹ := by group
      _ = a'⁻¹ * (a' * c') * c⁻¹ := by rw [h]
      _ = c' * c⁻¹ := by group
  have hm : a'⁻¹ * a ∈ V₁ ⊓ V₂ :=
    ⟨V₁.mul_mem (V₁.inv_mem ha') ha, e ▸ V₂.mul_mem hc' (V₂.inv_mem hc)⟩
  rw [S.hyp.inf, Subgroup.mem_bot, inv_mul_eq_one] at hm
  subst hm
  refine ⟨rfl, ?_⟩
  exact (mul_left_cancel h)

theorem proj_props {A B : Subgroup G} (hAB : (A = V₁ ∧ B = V₂) ∨ (A = V₂ ∧ B = V₁)) :
    (∀ v ∈ V, proj A B v ∈ B) ∧
    (∀ v ∈ V, ∀ w ∈ V, proj A B (v * w) = proj A B v * proj A B w) ∧
    (∀ (l : ↥L), ∀ v ∈ V, proj A B ((l : G) * v * (l : G)⁻¹) = (l : G) * proj A B v * (l : G)⁻¹) ∧
    (∀ v ∈ V, proj A B v = 1 → v ∈ A) := by
  have hinf : A ⊓ B = ⊥ := by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.hyp.inf
    · rw [inf_comm]
      exact S.hyp.inf
  have hdec : ∀ v ∈ V, ∃ a ∈ A, ∃ b ∈ B, v = a * b := by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun v hv => S.exists_decomp hv
    · exact fun v hv => S.exists_decomp' hv
  have hAV : A ≤ V := by rcases hAB with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [S.le₁, S.le₂]
  have hBV : B ≤ V := by rcases hAB with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [S.le₂, S.le₁]
  have hLA : L ≤ Subgroup.normalizer (A : Set G) := by
    rcases hAB with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [S.hyp.norm₁, S.hyp.norm₂]
  have hLB : L ≤ Subgroup.normalizer (B : Set G) := by
    rcases hAB with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [S.hyp.norm₂, S.hyp.norm₁]
  refine ⟨fun v hv => ?_, fun v hv w hw => ?_, fun l v hv => ?_, fun v hv h1 => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec v hv
    rw [proj_mul_eq hinf ha hb]
    exact hb
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec v hv
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec w hw
    have e : a * b * (a' * b') = (a * a') * (b * b') := by
      rw [mul_assoc, ← mul_assoc b, S.comm (hBV hb) (hAV ha'), mul_assoc, mul_assoc]
    rw [e, proj_mul_eq hinf (A.mul_mem ha ha') (B.mul_mem hb hb'), proj_mul_eq hinf ha hb,
      proj_mul_eq hinf ha' hb']
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec v hv
    have e : (l : G) * (a * b) * (l : G)⁻¹ =
        ((l : G) * a * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹) := by group
    rw [e, proj_mul_eq hinf ((Subgroup.mem_normalizer_iff.1 (hLA l.2) a).1 ha)
      ((Subgroup.mem_normalizer_iff.1 (hLB l.2) b).1 hb), proj_mul_eq hinf ha hb]
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec v hv
    rw [proj_mul_eq hinf ha hb] at h1
    rw [h1, mul_one]
    exact ha

theorem le_or_le {W : Subgroup G} (C : NatCoord L W n) (hWV : W ≤ V) : W ≤ V₁ ∨ W ≤ V₂ := by
  obtain ⟨ι⟩ := S.hyp.iso
  have proj_le : ∀ {A B : Subgroup G}, ((A = V₁ ∧ B = V₂) ∨ (A = V₂ ∧ B = V₁)) →
      ∀ C' : NatCoord L B n, (∀ l, C'.ρ l = slGraphAut n (ZMod 2) (C.ρ l)) → W ≤ A := by
    intro A B hAB C' hd w hw
    obtain ⟨h1, h2, h3, h4⟩ := S.proj_props hAB
    have := C.eq_one_of_dual S.hn hd (f := proj A B) (fun a ha => h1 a (hWV ha))
      (fun a ha b hb => h2 a (hWV ha) b (hWV hb)) (fun l a ha => h3 l a (hWV ha)) w hw
    exact h4 w (hWV hw) this
  obtain ⟨C₂', h | h⟩ := C.exists_adapted S.hn ι S.C₂
  · obtain ⟨C₁', h' | h'⟩ := C.exists_adapted S.hn ι S.C₁
    · exact absurd (C₁'.isXSectionIso (C' := C₂') fun l => (h l).trans (h' l).symm) S.hyp.dual
    · exact Or.inr (proj_le (Or.inr ⟨rfl, rfl⟩) C₁' h')
  · exact Or.inl (proj_le (Or.inl ⟨rfl, rfl⟩) C₂' h)

theorem card₁ : Nat.card ↥V₁ = Nat.card (Fin n → ZMod 2) := S.C₁.card_eq

theorem card₂ : Nat.card ↥V₂ = Nat.card (Fin n → ZMod 2) := S.C₂.card_eq

theorem exists_ne_one₁ : ∃ a ∈ V₁, a ≠ 1 := by
  have hn := S.hn
  refine ⟨S.C₁.inv (Pi.single ⟨0, by omega⟩ 1), S.C₁.inv_mem _, fun h => ?_⟩
  have := S.C₁.E_inv (Pi.single ⟨0, by omega⟩ 1)
  rw [h, S.C₁.E_one] at this
  have h2 := congrFun this ⟨0, by omega⟩
  simp at h2

theorem map_conj_eq_or_eq {W : Subgroup G} (C : NatCoord L W n) (hWV : W ≤ V)
    {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    W.map (MulAut.conj m).toMonoidHom = V₁ ∨ W.map (MulAut.conj m).toMonoidHom = V₂ := by
  have hle : W.map (MulAut.conj m).toMonoidHom ≤ V := by
    intro x hx
    rw [mem_map_conj] at hx
    have := S.conj_mem hm (hWV hx)
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [e] at this
  have hcard : Nat.card ↥(W.map (MulAut.conj m).toMonoidHom) = Nat.card (Fin n → ZMod 2) :=
    (C.conjugate hm).card_eq
  rcases S.le_or_le (C.conjugate hm) hle with h | h
  · left
    exact Subgroup.eq_of_le_of_card_ge h (by rw [S.card₁, hcard])
  · right
    exact Subgroup.eq_of_le_of_card_ge h (by rw [S.card₂, hcard])

theorem fix_or_swap {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    (m ∈ Subgroup.normalizer (V₁ : Set G) ∧ m ∈ Subgroup.normalizer (V₂ : Set G)) ∨
      ((∀ a, a ∈ V₁ ↔ m * a * m⁻¹ ∈ V₂) ∧ ∀ c, c ∈ V₂ ↔ m * c * m⁻¹ ∈ V₁) := by
  have hnorm : ∀ {W : Subgroup G}, W.map (MulAut.conj m).toMonoidHom = W →
      m ∈ Subgroup.normalizer (W : Set G) := by
    intro W h
    rw [Subgroup.mem_normalizer_iff]
    exact map_conj_eq_iff.1 h
  have hne : V₁ ≠ V₂ := by
    intro h
    obtain ⟨a, ha, ha1⟩ := S.exists_ne_one₁
    have : a ∈ V₁ ⊓ V₂ := ⟨ha, h ▸ ha⟩
    rw [S.hyp.inf, Subgroup.mem_bot] at this
    exact ha1 this
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  rcases S.map_conj_eq_or_eq S.C₁ S.le₁ hm with h₁ | h₁ <;>
    rcases S.map_conj_eq_or_eq S.C₂ S.le₂ hm with h₂ | h₂
  · exact absurd (Subgroup.map_injective hinj (h₁.trans h₂.symm)) hne
  · exact Or.inl ⟨hnorm h₁, hnorm h₂⟩
  · exact Or.inr ⟨map_conj_eq_iff.1 h₁, map_conj_eq_iff.1 h₂⟩
  · exact absurd (Subgroup.map_injective hinj (h₁.trans h₂.symm)) hne

theorem pairing_conj {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (h₁ : m ∈ Subgroup.normalizer (V₁ : Set G)) (h₂ : m ∈ Subgroup.normalizer (V₂ : Set G)) :
    ∀ a ∈ V₁, ∀ c ∈ V₂, pairing S.C₁ S.C₂ (m * a * m⁻¹) (m * c * m⁻¹) =
      pairing S.C₁ S.C₂ a c := by
  have hβ := isDualPairing S.C₁ S.C₂ S.dual
  have m₁ : ∀ a ∈ V₁, m * a * m⁻¹ ∈ V₁ := fun a ha => (Subgroup.mem_normalizer_iff.1 h₁ a).1 ha
  have m₂ : ∀ c ∈ V₂, m * c * m⁻¹ ∈ V₂ := fun c hc => (Subgroup.mem_normalizer_iff.1 h₂ c).1 hc
  refine eq_pairing S.hn S.C₁ S.C₂ S.dual (fun a ha b hb c hc => ?_) (fun a ha c hc d hd => ?_)
    (fun l hl a ha c hc => ?_) ?_
  · have e : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
    rw [e, hβ.1 _ (m₁ a ha) _ (m₁ b hb) _ (m₂ c hc)]
  · have e : m * (c * d) * m⁻¹ = (m * c * m⁻¹) * (m * d * m⁻¹) := by group
    rw [e, hβ.2.1 _ (m₁ a ha) _ (m₂ c hc) _ (m₂ d hd)]
  · have hl' : m * l * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hm l).1 hl
    have e : ∀ x, m * (l * x * l⁻¹) * m⁻¹ = (m * l * m⁻¹) * (m * x * m⁻¹) * (m * l * m⁻¹)⁻¹ :=
      fun x => by group
    rw [e, e]
    exact hβ.2.2.2.2 _ hl' _ (m₁ a ha) _ (m₂ c hc)
  · obtain ⟨a', ha', ha'1⟩ := S.exists_ne_one₁
    obtain ⟨c', hc', hac'⟩ := hβ.2.2.1 a' ha' ha'1
    refine ⟨m⁻¹ * a' * m, ?_, m⁻¹ * c' * m, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h₁) a').1 ha'
      rwa [inv_inv] at this
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h₂) c').1 hc'
      rwa [inv_inv] at this
    · have e : ∀ x, m * (m⁻¹ * x * m) * m⁻¹ = x := fun x => by group
      rw [e, e, hac']
      exact one_ne_zero

theorem pairing_conj_swap {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (h₁ : ∀ a, a ∈ V₁ ↔ m * a * m⁻¹ ∈ V₂) (h₂ : ∀ c, c ∈ V₂ ↔ m * c * m⁻¹ ∈ V₁) :
    ∀ a ∈ V₁, ∀ c ∈ V₂, pairing S.C₁ S.C₂ (m * c * m⁻¹) (m * a * m⁻¹) =
      pairing S.C₁ S.C₂ a c := by
  have hβ := isDualPairing S.C₁ S.C₂ S.dual
  refine eq_pairing (P := fun a c => pairing S.C₁ S.C₂ (m * c * m⁻¹) (m * a * m⁻¹)) S.hn S.C₁
    S.C₂ S.dual (fun a ha b hb c hc => ?_) (fun a ha c hc d hd => ?_)
    (fun l hl a ha c hc => ?_) ?_
  · have e : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
    rw [e, hβ.2.1 _ ((h₂ c).1 hc) _ ((h₁ a).1 ha) _ ((h₁ b).1 hb)]
  · have e : m * (c * d) * m⁻¹ = (m * c * m⁻¹) * (m * d * m⁻¹) := by group
    rw [e, hβ.1 _ ((h₂ c).1 hc) _ ((h₂ d).1 hd) _ ((h₁ a).1 ha)]
  · have hl' : m * l * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hm l).1 hl
    have e : ∀ x, m * (l * x * l⁻¹) * m⁻¹ = (m * l * m⁻¹) * (m * x * m⁻¹) * (m * l * m⁻¹)⁻¹ :=
      fun x => by group
    rw [e, e]
    exact hβ.2.2.2.2 _ hl' _ ((h₂ c).1 hc) _ ((h₁ a).1 ha)
  · obtain ⟨a', ha', ha'1⟩ := S.exists_ne_one₁
    obtain ⟨c', hc', hac'⟩ := hβ.2.2.1 a' ha' ha'1
    have e : ∀ x, m * (m⁻¹ * x * m) * m⁻¹ = x := fun x => by group
    refine ⟨m⁻¹ * c' * m, ?_, m⁻¹ * a' * m, ?_, ?_⟩
    · rw [h₁, e]
      exact hc'
    · rw [h₂, e]
      exact ha'
    · rw [e, e, hac']
      exact one_ne_zero

theorem exists_eq_conj {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (h₁ : m ∈ Subgroup.normalizer (V₁ : Set G)) (h₂ : m ∈ Subgroup.normalizer (V₂ : Set G)) :
    ∃ l ∈ L, ∀ v ∈ V, m * v * m⁻¹ = l * v * l⁻¹ := by
  have m₁ : ∀ a ∈ V₁, m * a * m⁻¹ ∈ V₁ := fun a ha => (Subgroup.mem_normalizer_iff.1 h₁ a).1 ha
  let φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
    AddMonoidHom.mk' (fun x => S.C₁.E (m * S.C₁.inv x * m⁻¹)) fun x y => by
      have e : m * (S.C₁.inv x * S.C₁.inv y) * m⁻¹ =
          (m * S.C₁.inv x * m⁻¹) * (m * S.C₁.inv y * m⁻¹) := by group
      rw [S.C₁.inv_add, e, S.C₁.map_mul _ (m₁ _ (S.C₁.inv_mem x)) _ (m₁ _ (S.C₁.inv_mem y))]
  have hφ : ∀ x, matOf φ *ᵥ x = S.C₁.E (m * S.C₁.inv x * m⁻¹) := fun x => matOf_mulVec φ x
  have hdet : (matOf φ).det = 1 := by
    rcases zmod_two_cases (matOf φ).det with h0 | h1
    · exfalso
      obtain ⟨x, hx, hx0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      rw [hφ] at hx0
      have h1 := S.C₁.eq_one_of_E (m₁ _ (S.C₁.inv_mem x)) hx0
      have h2 : S.C₁.inv x = 1 := by
        calc S.C₁.inv x = m⁻¹ * (m * S.C₁.inv x * m⁻¹) * m := by group
          _ = 1 := by rw [h1]; group
      apply hx
      rw [← S.C₁.E_inv x, h2, S.C₁.E_one]
    · exact h1
  obtain ⟨l, hl⟩ := S.C₁.ρ_surj ⟨matOf φ, hdet⟩
  set m' := (l : G)⁻¹ * m with hm'
  have hm'M : m' ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer l.2)) hm
  have hm'₁ : m' ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (S.hyp.norm₁ l.2)) h₁
  have hm'₂ : m' ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (S.hyp.norm₂ l.2)) h₂
  have hc₁ : ∀ a ∈ V₁, m' * a * m'⁻¹ = a := by
    intro a ha
    have e : m' * a * m'⁻¹ = ((l⁻¹ : ↥L) : G) * (m * a * m⁻¹) * ((l⁻¹ : ↥L) : G)⁻¹ := by
      rw [hm']
      simp only [Subgroup.coe_inv]
      group
    refine S.C₁.inj _ ((Subgroup.mem_normalizer_iff.1 hm'₁ a).1 ha) a ha ?_
    rw [e, S.C₁.conj _ _ (m₁ a ha), _root_.map_inv, hl]
    have h3 : S.C₁.E (m * a * m⁻¹) = matOf φ *ᵥ S.C₁.E a := by rw [hφ, S.C₁.inv_E ha]
    rw [h3, Matrix.mulVec_mulVec]
    have h4 := coe_inv_mul (⟨matOf φ, hdet⟩ : SpecialLinearGroup (Fin n) (ZMod 2))
    simp only at h4
    rw [h4, Matrix.one_mulVec]
  have hc₂ : ∀ c ∈ V₂, m' * c * m'⁻¹ = c := by
    intro c hc
    have hcm : m' * c * m'⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 hm'₂ c).1 hc
    have hp := S.pairing_conj hm'M hm'₁ hm'₂
    refine S.C₂.inj _ hcm c hc (vec_ext_dot fun x => ?_)
    have := hp (S.C₁.inv x) (S.C₁.inv_mem x) c hc
    rw [hc₁ _ (S.C₁.inv_mem x)] at this
    simp only [pairing, S.C₁.E_inv] at this
    rw [dotProduct_comm, this, dotProduct_comm]
  refine ⟨l, l.2, fun v hv => ?_⟩
  obtain ⟨a, ha, c, hc, rfl⟩ := S.exists_decomp hv
  have e : m * (a * c) * m⁻¹ = (l : G) * ((m' * a * m'⁻¹) * (m' * c * m'⁻¹)) * (l : G)⁻¹ := by
    rw [hm']
    group
  rw [e, hc₁ a ha, hc₂ c hc]

theorem exists_swap : ∃ m ∈ Subgroup.normalizer (L : Set G),
    (∀ a, a ∈ V₁ ↔ m * a * m⁻¹ ∈ V₂) ∧ ∀ c, c ∈ V₂ ↔ m * c * m⁻¹ ∈ V₁ := by
  by_contra hno
  have hall : ∀ m ∈ Subgroup.normalizer (L : Set G), ∃ l ∈ L, ∀ v ∈ V,
      m * v * m⁻¹ = l * v * l⁻¹ := by
    intro m hm
    rcases S.fix_or_swap hm with ⟨h₁, h₂⟩ | hsw
    · exact S.exists_eq_conj hm h₁ h₂
    · exact absurd ⟨m, hm, hsw⟩ hno
  obtain ⟨ι⟩ := S.hyp.iso
  obtain ⟨eA⟩ := S.hyp.aut
  have hLV : L ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer.trans S.le_normalizer
  let ρV := Setup.rho V L hLV
  have hle : autOn (Subgroup.normalizer (L : Set G)) V ≤ ρV.range := by
    intro φ hφ
    obtain ⟨g, hgM, rfl⟩ := Setup.mem_autOn_iff.1 hφ
    obtain ⟨l, hl, hgl⟩ := hall g hgM
    refine ⟨⟨l, hl⟩, ?_⟩
    ext v
    rw [Setup.rho_apply_coe, Setup.coe_conjAct_apply]
    exact (hgl v v.2).symm
  have hker : CFSG.pCore 2 ↥L ≤ ρV.ker := by
    intro l hl
    have h1 : S.C₁.ρ l = 1 := by
      rw [← MonoidHom.mem_ker, S.C₁.ker_eq S.hn ι]
      exact hl
    have h2 : S.C₂.ρ l = 1 := by
      rw [← MonoidHom.mem_ker, S.C₂.ker_eq S.hn ι]
      exact hl
    rw [MonoidHom.mem_ker]
    ext v
    rw [Setup.rho_apply_coe, MulAut.one_apply]
    obtain ⟨a, ha, c, hc, hv⟩ := S.exists_decomp v.2
    rw [hv]
    have e : (l : G) * (a * c) * (l : G)⁻¹ =
        ((l : G) * a * (l : G)⁻¹) * ((l : G) * c * (l : G)⁻¹) := by group
    rw [e, S.C₁.conj_eq_of_ρ_eq_one h1 ha, S.C₂.conj_eq_of_ρ_eq_one h2 hc]
  have h1 : Nat.card ↥(autOn (Subgroup.normalizer (L : Set G)) V) ≤
      Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) := by
    calc Nat.card ↥(autOn (Subgroup.normalizer (L : Set G)) V) ≤ Nat.card ↥ρV.range :=
          Subgroup.card_le_of_le hle
      _ = ρV.ker.index := by
          rw [Subgroup.index_eq_card]
          exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρV).toEquiv).symm
      _ ≤ (CFSG.pCore 2 ↥L).index :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
            (Subgroup.index_dvd_of_le hker)
      _ = Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) := by
          rw [Subgroup.index_eq_card]
          exact Nat.card_congr ι.toEquiv
  have h2 : Nat.card ↥(autOn (Subgroup.normalizer (L : Set G)) V) =
      Nat.card (MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) :=
    Nat.card_congr (eA.trans (MulAut.congr ι)).toEquiv
  have h3 := card_lt_card_mulAut S.hn
  omega

end Setting

end CFSG.Quasithin.H13.KGH91
