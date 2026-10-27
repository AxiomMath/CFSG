module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {Γ : Type*} [Group Γ]

structure HalfPair (P R : Subgroup Γ) : Prop where
  commP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x
  sqP : ∀ x ∈ P, x * x = 1
  commR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
  sqR : ∀ x ∈ R, x * x = 1
  disj : P ⊓ R = ⊥
  halfPR : ∀ t ∈ R, t ≠ 1 → t ∈ Subgroup.normalizer (P : Set Γ) →
    ∀ s ∈ P, s * t = t * s → s ∈ Subgroup.normalizer (R : Set Γ)
  halfRP : ∀ s ∈ P, s ≠ 1 → s ∈ Subgroup.normalizer (R : Set Γ) →
    ∀ t ∈ R, t * s = s * t → t ∈ Subgroup.normalizer (P : Set Γ)

variable {P R : Subgroup Γ}

theorem HalfPair.symm (h : HalfPair P R) : HalfPair R P :=
  ⟨h.commR, h.sqR, h.commP, h.sqP, by rw [inf_comm]; exact h.disj, h.halfRP, h.halfPR⟩

private theorem finite_inf [Finite P] (S : Subgroup Γ) : Finite ↥(P ⊓ S) :=
  Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : P ⊓ S ≤ P))

theorem HalfPair.comm_mem_inf (h : HalfPair P R) {f l : Γ}
    (hf : f ∈ R ⊓ Subgroup.normalizer (P : Set Γ)) (hl : l ∈ P) :
    f * l * f⁻¹ * l⁻¹ ∈ P ⊓ Subgroup.normalizer (R : Set Γ) := by
  have hm : f * l * f⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hf.2 l).mp hl
  have hk : f * l * f⁻¹ * l⁻¹ ∈ P := P.mul_mem hm (P.inv_mem hl)
  refine ⟨hk, ?_⟩
  by_cases hf1 : f = 1
  · subst hf1
    simpa using (Subgroup.normalizer (R : Set Γ)).one_mem
  refine h.halfPR f hf.1 hf1 hf.2 _ hk ?_
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right (h.sqR f hf.1)
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right (h.sqP l hl)
  have hff : f * f = 1 := h.sqR f hf.1
  have hc := h.commP _ hm l hl
  rw [hfi] at hc
  rw [hfi, hli]
  calc f * l * f * l * f = l * (f * l * f) * f := by rw [hc]
    _ = l * f * l * (f * f) := by group
    _ = l * f * l := by rw [hff, mul_one]
    _ = (f * f) * l * f * l := by rw [hff, one_mul]
    _ = f * (f * l * f * l) := by group

theorem HalfPair.comm_inj (h : HalfPair P R) {l : Γ} (hl : l ∈ P)
    (hlN : l ∉ Subgroup.normalizer (R : Set Γ)) {f f' : Γ}
    (hf : f ∈ R ⊓ Subgroup.normalizer (P : Set Γ)) (hf' : f' ∈ R ⊓ Subgroup.normalizer (P : Set Γ))
    (e : f * l * f⁻¹ * l⁻¹ = f' * l * f'⁻¹ * l⁻¹) : f = f' := by
  by_contra hne
  have hg : f'⁻¹ * f ∈ R ⊓ Subgroup.normalizer (P : Set Γ) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hf') hf
  have hg1 : f'⁻¹ * f ≠ 1 := fun h1 => hne (inv_mul_eq_one.mp h1).symm
  have e2 : f * l * f⁻¹ = f' * l * f'⁻¹ := mul_right_cancel e
  have hcomm : l * (f'⁻¹ * f) = (f'⁻¹ * f) * l := by
    calc l * (f'⁻¹ * f) = f'⁻¹ * (f' * l * f'⁻¹) * f := by group
      _ = f'⁻¹ * (f * l * f⁻¹) * f := by rw [e2]
      _ = (f'⁻¹ * f) * l := by group
  exact hlN (h.halfPR _ hg.1 hg1 hg.2 l hl hcomm)

private def HalfPair.commHom (h : HalfPair P R) {f : Γ}
    (hf : f ∈ R ⊓ Subgroup.normalizer (P : Set Γ)) : ↥P →* ↥P :=
  { toFun := fun l => ⟨f * l * f⁻¹ * l⁻¹,
      P.mul_mem ((Subgroup.mem_normalizer_iff.mp hf.2 l).mp l.2) (P.inv_mem l.2)⟩
    map_one' := by ext; simp
    map_mul' := fun a b => by
      apply Subtype.ext
      show f * ((a : Γ) * b) * f⁻¹ * ((a : Γ) * b)⁻¹ =
        (f * a * f⁻¹ * (a : Γ)⁻¹) * (f * b * f⁻¹ * (b : Γ)⁻¹)
      have hb : f * (b : Γ) * f⁻¹ * (b : Γ)⁻¹ ∈ P :=
        P.mul_mem ((Subgroup.mem_normalizer_iff.mp hf.2 b).mp b.2) (P.inv_mem b.2)
      have hc := h.commP _ (P.inv_mem a.2) _ hb
      calc f * ((a : Γ) * b) * f⁻¹ * ((a : Γ) * b)⁻¹ =
            (f * a * f⁻¹) * ((f * b * f⁻¹ * (b : Γ)⁻¹) * (a : Γ)⁻¹) := by group
        _ = (f * a * f⁻¹) * ((a : Γ)⁻¹ * (f * b * f⁻¹ * (b : Γ)⁻¹)) := by rw [hc]
        _ = _ := by group }

private theorem HalfPair.card_ker_le [Finite P] (h : HalfPair P R) {f : Γ}
    (hf : f ∈ R ⊓ Subgroup.normalizer (P : Set Γ)) (hf1 : f ≠ 1) :
    Nat.card (h.commHom hf).ker ≤
      Nat.card ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) := by
  haveI := finite_inf (P := P) (Subgroup.normalizer (R : Set Γ))
  refine Nat.card_le_card_of_injective
    (fun x : (h.commHom hf).ker =>
      (⟨((x : ↥P) : Γ), (x : ↥P).2, ?_⟩ :
        ↥(P ⊓ Subgroup.normalizer (R : Set Γ))))
    fun x y hxy => ?_
  · have hx : f * ((x : ↥P) : Γ) * f⁻¹ * ((x : ↥P) : Γ)⁻¹ = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    refine h.halfPR f hf.1 hf1 hf.2 _ (x : ↥P).2 ?_
    calc ((x : ↥P) : Γ) * f =
          (f * ((x : ↥P) : Γ) * f⁻¹ * ((x : ↥P) : Γ)⁻¹)⁻¹ * (f * x) := by group
      _ = f * x := by rw [hx, inv_one, one_mul]
  · have hv := congrArg (fun z : ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) => (z : Γ)) hxy
    exact Subtype.ext (Subtype.ext hv)

private theorem HalfPair.card_range_le [Finite P] (h : HalfPair P R) {f : Γ}
    (hf : f ∈ R ⊓ Subgroup.normalizer (P : Set Γ)) :
    Nat.card (h.commHom hf).range ≤
      Nat.card ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) := by
  haveI := finite_inf (P := P) (Subgroup.normalizer (R : Set Γ))
  refine Nat.card_le_card_of_injective
    (fun x : (h.commHom hf).range =>
      (⟨((x : ↥P) : Γ), (x : ↥P).2, ?_⟩ :
        ↥(P ⊓ Subgroup.normalizer (R : Set Γ))))
    fun x y hxy => ?_
  · obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp x.2
    rw [← hl]
    exact (h.comm_mem_inf hf l.2).2
  · have hv := congrArg (fun z : ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) => (z : Γ)) hxy
    exact Subtype.ext (Subtype.ext hv)

theorem HalfPair.card_le_sq [Finite P] (h : HalfPair P R) {f : Γ}
    (hf : f ∈ R ⊓ Subgroup.normalizer (P : Set Γ)) (hf1 : f ≠ 1) :
    Nat.card P ≤ Nat.card ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) ^ 2 := by
  haveI := finite_inf (P := P) (Subgroup.normalizer (R : Set Γ))
  have hcard : Nat.card P =
      Nat.card (h.commHom hf).ker * Nat.card (h.commHom hf).range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard, sq]
  exact Nat.mul_le_mul (h.card_ker_le hf hf1) (h.card_range_le hf)

theorem HalfPair.card_le [Finite P] (h : HalfPair P R) {l : Γ} (hl : l ∈ P)
    (hlN : l ∉ Subgroup.normalizer (R : Set Γ)) :
    Nat.card ↥(R ⊓ Subgroup.normalizer (P : Set Γ)) ≤
      Nat.card ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) := by
  haveI := finite_inf (P := P) (Subgroup.normalizer (R : Set Γ))
  exact Nat.card_le_card_of_injective
    (fun f : ↥(R ⊓ Subgroup.normalizer (P : Set Γ)) =>
      (⟨f * l * (f : Γ)⁻¹ * l⁻¹, h.comm_mem_inf f.2 hl⟩ : ↥(P ⊓ Subgroup.normalizer (R : Set Γ))))
    fun f f' hff' => Subtype.ext (h.comm_inj hl hlN f.2 f'.2 (congrArg Subtype.val hff'))

theorem HalfPair.card_eq [Finite P] [Finite R] (h : HalfPair P R) {l r : Γ} (hl : l ∈ P)
    (hlN : l ∉ Subgroup.normalizer (R : Set Γ)) (hr : r ∈ R)
    (hrN : r ∉ Subgroup.normalizer (P : Set Γ)) :
    Nat.card ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) =
      Nat.card ↥(R ⊓ Subgroup.normalizer (P : Set Γ)) :=
  le_antisymm (h.symm.card_le hr hrN) (h.card_le hl hlN)

theorem HalfPair.exists_comm_eq [Finite P] [Finite R] (h : HalfPair P R) {r : Γ} (hr : r ∈ R)
    (hrN : r ∉ Subgroup.normalizer (P : Set Γ)) {l : Γ} (hl : l ∈ P)
    (hlN : l ∉ Subgroup.normalizer (R : Set Γ)) {e : Γ}
    (he : e ∈ P ⊓ Subgroup.normalizer (R : Set Γ)) :
    ∃ g ∈ R ⊓ Subgroup.normalizer (P : Set Γ), e = l * g * l⁻¹ * g⁻¹ := by
  haveI := finite_inf (P := P) (Subgroup.normalizer (R : Set Γ))
  let ψ : ↥(R ⊓ Subgroup.normalizer (P : Set Γ)) → ↥(P ⊓ Subgroup.normalizer (R : Set Γ)) :=
    fun f => ⟨f * l * (f : Γ)⁻¹ * l⁻¹, h.comm_mem_inf f.2 hl⟩
  have hinj : Function.Injective ψ := fun f f' hff' =>
    Subtype.ext (h.comm_inj hl hlN f.2 f'.2 (congrArg Subtype.val hff'))
  obtain ⟨g, hg⟩ := (hinj.bijective_of_nat_card_le (h.card_eq hl hlN hr hrN).le).2
    ⟨e⁻¹, Subgroup.inv_mem _ he⟩
  refine ⟨g, g.2, ?_⟩
  have e1 : (g : Γ) * l * (g : Γ)⁻¹ * l⁻¹ = e⁻¹ := congrArg Subtype.val hg
  rw [← inv_inv e, ← e1]
  group

end CFSG.RankThree.GF2n.Stroth80
