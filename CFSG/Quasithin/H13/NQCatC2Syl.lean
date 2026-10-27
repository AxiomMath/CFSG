module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Quasithin.H13.NQCatC2Prod

public section

namespace CFSG.Quasithin.H13.NQCat.C2

open CFSG.QuasithinUnique

variable {A : Type} [Group A] {Q₁ Q₂ : Subgroup A}

theorem le_normalizer_of_forall_comm {X Y : Subgroup A}
    (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) : Y ≤ Subgroup.normalizer (X : Set A) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [← hc a ha b hb, mul_inv_cancel_right]
    exact ha
  · intro ha
    have := hc _ ha b hb
    have e : a = b * a * b⁻¹ := by
      calc a = b⁻¹ * (b * a * b⁻¹ * b) := by group
        _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [this]
        _ = b * a * b⁻¹ := by group
    rw [e]
    exact ha

theorem mem_normalizer_of_conj_mem' [Finite A] {H : Subgroup A} {g : A}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set A) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hg x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hye⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hye
  have : y = x := by simpa using hye
  rwa [← this]

theorem CommPair.mono (h : CommPair Q₁ Q₂) {Y₁ Y₂ : Subgroup A} (h₁ : Y₁ ≤ Q₁) (h₂ : Y₂ ≤ Q₂) :
    CommPair Y₁ Y₂ :=
  ⟨fun a ha b hb => h.comm a (h₁ ha) b (h₂ hb),
    le_bot_iff.mp ((inf_le_inf h₁ h₂).trans h.inf_eq.le)⟩

theorem CommPair.card_sup (h : CommPair Q₁ Q₂) :
    Nat.card ↥(Q₁ ⊔ Q₂) = Nat.card Q₁ * Nat.card Q₂ := by
  rw [← Nat.card_congr h.prodEquiv.toEquiv, Nat.card_prod]

@[expose] noncomputable def CommPair.img₁ (h : CommPair Q₁ Q₂) (X : Subgroup A) : Subgroup A :=
  (X.subgroupOf (Q₁ ⊔ Q₂)).map h.pr1

@[expose] noncomputable def CommPair.img₂ (h : CommPair Q₁ Q₂) (X : Subgroup A) : Subgroup A :=
  (X.subgroupOf (Q₁ ⊔ Q₂)).map h.pr2

variable (h : CommPair Q₁ Q₂)
include h

theorem CommPair.img₁_le (X : Subgroup A) : h.img₁ X ≤ Q₁ := by
  rintro _ ⟨x, -, rfl⟩
  exact h.pr1_mem x

theorem CommPair.img₂_le (X : Subgroup A) : h.img₂ X ≤ Q₂ := by
  rintro _ ⟨x, -, rfl⟩
  exact h.pr2_mem x

theorem CommPair.mem_img₁ {X : Subgroup A} {a b : A} (ha : a ∈ Q₁) (hb : b ∈ Q₂)
    (hab : a * b ∈ X) : a ∈ h.img₁ X :=
  ⟨⟨a * b, Subgroup.mul_mem_sup ha hb⟩, hab, (h.pr_eq ha hb rfl).1⟩

theorem CommPair.mem_img₂ {X : Subgroup A} {a b : A} (ha : a ∈ Q₁) (hb : b ∈ Q₂)
    (hab : a * b ∈ X) : b ∈ h.img₂ X :=
  ⟨⟨a * b, Subgroup.mul_mem_sup ha hb⟩, hab, (h.pr_eq ha hb rfl).2⟩

theorem CommPair.exists_of_mem_img₁ {X : Subgroup A} {a : A} (ha : a ∈ h.img₁ X) :
    ∃ b ∈ Q₂, a * b ∈ X := by
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨h.pr2 x, h.pr2_mem x, by rw [h.pr1_mul_pr2]; exact hx⟩

theorem CommPair.exists_of_mem_img₂ {X : Subgroup A} {b : A} (hb : b ∈ h.img₂ X) :
    ∃ a ∈ Q₁, a * b ∈ X := by
  obtain ⟨x, hx, rfl⟩ := hb
  exact ⟨h.pr1 x, h.pr1_mem x, by rw [h.pr1_mul_pr2]; exact hx⟩

theorem CommPair.exists_mul_img {X : Subgroup A} (hX : X ≤ Q₁ ⊔ Q₂) {x : A} (hx : x ∈ X) :
    ∃ a ∈ h.img₁ X, ∃ b ∈ h.img₂ X, x = a * b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul (hX hx)
  exact ⟨a, h.mem_img₁ ha hb hx, b, h.mem_img₂ ha hb hx, rfl⟩

theorem CommPair.img₁_le_of_le {Y₁ Y₂ : Subgroup A} (h₁ : Y₁ ≤ Q₁) (h₂ : Y₂ ≤ Q₂)
    {X : Subgroup A} (hX : X ≤ Y₁ ⊔ Y₂) : h.img₁ X ≤ Y₁ := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := h.exists_of_mem_img₁ ha
  obtain ⟨a', ha', b', hb', he⟩ := (h.mono h₁ h₂).exists_mul (hX hab)
  rw [(h.eq_of_mul_eq_mul (h.img₁_le X ha) (h₁ ha') hb (h₂ hb') he).1]
  exact ha'

theorem CommPair.img₂_le_of_le {Y₁ Y₂ : Subgroup A} (h₁ : Y₁ ≤ Q₁) (h₂ : Y₂ ≤ Q₂)
    {X : Subgroup A} (hX : X ≤ Y₁ ⊔ Y₂) : h.img₂ X ≤ Y₂ := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := h.exists_of_mem_img₂ hb
  obtain ⟨a', ha', b', hb', he⟩ := (h.mono h₁ h₂).exists_mul (hX hab)
  rw [(h.eq_of_mul_eq_mul ha (h₁ ha') (h.img₂_le X hb) (h₂ hb') he).2]
  exact hb'

theorem CommPair.card_img₁_dvd {X : Subgroup A} (hX : X ≤ Q₁ ⊔ Q₂) :
    Nat.card (h.img₁ X) ∣ Nat.card X := by
  have := Subgroup.card_map_dvd (X.subgroupOf (Q₁ ⊔ Q₂)) h.pr1
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv] at this

theorem CommPair.card_img₂_dvd {X : Subgroup A} (hX : X ≤ Q₁ ⊔ Q₂) :
    Nat.card (h.img₂ X) ∣ Nat.card X := by
  have := Subgroup.card_map_dvd (X.subgroupOf (Q₁ ⊔ Q₂)) h.pr2
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv] at this

theorem CommPair.card_le_mul [Finite A] {X : Subgroup A} (hX : X ≤ Q₁ ⊔ Q₂) :
    Nat.card X ≤ Nat.card (h.img₁ X) * Nat.card (h.img₂ X) := by
  let f : ↥X → ↥(h.img₁ X) × ↥(h.img₂ X) := fun x =>
    (⟨h.pr1 ⟨x, hX x.2⟩, ⟨⟨x, hX x.2⟩, x.2, rfl⟩⟩, ⟨h.pr2 ⟨x, hX x.2⟩, ⟨⟨x, hX x.2⟩, x.2, rfl⟩⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 := congrArg (fun p : ↥(h.img₁ X) × ↥(h.img₂ X) => (p.1 : A) * p.2) hxy
    simp only [f] at h1
    rw [h.pr1_mul_pr2, h.pr1_mul_pr2] at h1
    exact Subtype.ext h1
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective f hf

theorem CommPair.isCyclic_img₁ {X : Subgroup A} (hX : X ≤ Q₁ ⊔ Q₂) (hc : IsCyclic ↥X) :
    IsCyclic ↥(h.img₁ X) := by
  have : IsCyclic ↥(X.subgroupOf (Q₁ ⊔ Q₂)) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hX).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hX).symm.surjective
  exact isCyclic_of_surjective (h.pr1.subgroupMap _) (h.pr1.subgroupMap_surjective _)

theorem CommPair.isCyclic_img₂ {X : Subgroup A} (hX : X ≤ Q₁ ⊔ Q₂) (hc : IsCyclic ↥X) :
    IsCyclic ↥(h.img₂ X) := by
  have : IsCyclic ↥(X.subgroupOf (Q₁ ⊔ Q₂)) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hX).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hX).symm.surjective
  exact isCyclic_of_surjective (h.pr2.subgroupMap _) (h.pr2.subgroupMap_surjective _)

theorem CommPair.perm_img₁ {T D : Subgroup A} (hTQ : T ≤ Q₁ ⊔ Q₂) (hDQ : D ≤ Q₁ ⊔ Q₂)
    (hT₁ : h.img₁ T ≤ T) (hperm : ∀ t ∈ T, ∀ x ∈ D, ∃ x' ∈ D, ∃ t' ∈ T, t * x = x' * t') :
    ∀ t ∈ T ⊓ Q₁, ∀ y ∈ h.img₁ D, ∃ y' ∈ h.img₁ D, ∃ t' ∈ T ⊓ Q₁, t * y = y' * t' := by
  intro t ht y hy
  obtain ⟨b, hb, hyb⟩ := h.exists_of_mem_img₁ hy
  obtain ⟨x', hx', t', ht', he⟩ := hperm t (Subgroup.mem_inf.mp ht).1 _ hyb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := h.exists_mul_img hDQ hx'
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h.exists_mul_img hTQ ht'
  have hc : c₁ * a₂ = a₂ * c₁ := h.comm c₁ (h.img₁_le T hc₁) a₂ (h.img₂_le D ha₂)
  have e : t * y * b = (a₁ * c₁) * (a₂ * c₂) := by
    calc t * y * b = t * (y * b) := by group
      _ = a₁ * a₂ * (c₁ * c₂) := he
      _ = a₁ * (a₂ * c₁) * c₂ := by group
      _ = a₁ * (c₁ * a₂) * c₂ := by rw [hc]
      _ = (a₁ * c₁) * (a₂ * c₂) := by group
  have := h.eq_of_mul_eq_mul (mul_mem (Subgroup.mem_inf.mp ht).2 (h.img₁_le D hy))
    (mul_mem (h.img₁_le D ha₁) (h.img₁_le T hc₁)) hb
    (mul_mem (h.img₂_le D ha₂) (h.img₂_le T hc₂)) e
  exact ⟨a₁, ha₁, c₁, Subgroup.mem_inf.mpr ⟨hT₁ hc₁, h.img₁_le T hc₁⟩, this.1⟩

theorem CommPair.perm_img₂ {T D : Subgroup A} (hTQ : T ≤ Q₁ ⊔ Q₂) (hDQ : D ≤ Q₁ ⊔ Q₂)
    (hT₂ : h.img₂ T ≤ T) (hperm : ∀ t ∈ T, ∀ x ∈ D, ∃ x' ∈ D, ∃ t' ∈ T, t * x = x' * t') :
    ∀ t ∈ T ⊓ Q₂, ∀ y ∈ h.img₂ D, ∃ y' ∈ h.img₂ D, ∃ t' ∈ T ⊓ Q₂, t * y = y' * t' := by
  intro t ht y hy
  obtain ⟨a, ha, hay⟩ := h.exists_of_mem_img₂ hy
  obtain ⟨x', hx', t', ht', he⟩ := hperm t (Subgroup.mem_inf.mp ht).1 _ hay
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := h.exists_mul_img hDQ hx'
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h.exists_mul_img hTQ ht'
  have hc : c₁ * a₂ = a₂ * c₁ := h.comm c₁ (h.img₁_le T hc₁) a₂ (h.img₂_le D ha₂)
  have hat : a * t = t * a := h.comm a ha t (Subgroup.mem_inf.mp ht).2
  have e : a * (t * y) = (a₁ * c₁) * (a₂ * c₂) := by
    calc a * (t * y) = a * t * y := by group
      _ = t * a * y := by rw [hat]
      _ = t * (a * y) := by group
      _ = a₁ * a₂ * (c₁ * c₂) := he
      _ = a₁ * (a₂ * c₁) * c₂ := by group
      _ = a₁ * (c₁ * a₂) * c₂ := by rw [hc]
      _ = (a₁ * c₁) * (a₂ * c₂) := by group
  have := h.eq_of_mul_eq_mul ha (mul_mem (h.img₁_le D ha₁) (h.img₁_le T hc₁))
    (mul_mem (Subgroup.mem_inf.mp ht).2 (h.img₂_le D hy))
    (mul_mem (h.img₂_le D ha₂) (h.img₂_le T hc₂)) e
  exact ⟨a₂, ha₂, c₂, Subgroup.mem_inf.mpr ⟨hT₂ hc₂, h.img₂_le T hc₂⟩, this.2⟩

theorem CommPair.mem_normalizer_img₁ [Finite A] {X : Subgroup A} {c₁ c₂ : A} (hc₁ : c₁ ∈ Q₁)
    (hc₂ : c₂ ∈ Q₂) (hcX : c₁ * c₂ ∈ Subgroup.normalizer (X : Set A)) :
    c₁ ∈ Subgroup.normalizer (h.img₁ X : Set A) := by
  apply mem_normalizer_of_conj_mem'
  intro a ha
  obtain ⟨b, hb, hab⟩ := h.exists_of_mem_img₁ ha
  have haQ : a ∈ Q₁ := h.img₁_le X ha
  have hw : c₂ * b * c₂⁻¹ ∈ Q₂ := mul_mem (mul_mem hc₂ hb) (inv_mem hc₂)
  have h1 : c₁ * c₂ * (a * b) * (c₁ * c₂)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hcX _).mp hab
  have e1 : c₂ * a = a * c₂ := (h.comm a haQ c₂ hc₂).symm
  have e2 : c₁ * (c₂ * b * c₂⁻¹) = (c₂ * b * c₂⁻¹) * c₁ := h.comm c₁ hc₁ _ hw
  have h2 : c₁ * c₂ * (a * b) * (c₁ * c₂)⁻¹ = (c₁ * a * c₁⁻¹) * (c₂ * b * c₂⁻¹) := by
    calc c₁ * c₂ * (a * b) * (c₁ * c₂)⁻¹ = c₁ * (c₂ * a) * b * c₂⁻¹ * c₁⁻¹ := by group
      _ = c₁ * (a * c₂) * b * c₂⁻¹ * c₁⁻¹ := by rw [e1]
      _ = c₁ * a * c₁⁻¹ * (c₁ * (c₂ * b * c₂⁻¹)) * c₁⁻¹ := by group
      _ = c₁ * a * c₁⁻¹ * ((c₂ * b * c₂⁻¹) * c₁) * c₁⁻¹ := by rw [e2]
      _ = (c₁ * a * c₁⁻¹) * (c₂ * b * c₂⁻¹) := by group
  rw [h2] at h1
  exact h.mem_img₁ (mul_mem (mul_mem hc₁ haQ) (inv_mem hc₁)) hw h1

theorem CommPair.mem_normalizer_img₂ [Finite A] {X : Subgroup A} {c₁ c₂ : A} (hc₁ : c₁ ∈ Q₁)
    (hc₂ : c₂ ∈ Q₂) (hcX : c₁ * c₂ ∈ Subgroup.normalizer (X : Set A)) :
    c₂ ∈ Subgroup.normalizer (h.img₂ X : Set A) := by
  apply mem_normalizer_of_conj_mem'
  intro b hb
  obtain ⟨a, ha, hab⟩ := h.exists_of_mem_img₂ hb
  have hbQ : b ∈ Q₂ := h.img₂_le X hb
  have hw : c₁ * a * c₁⁻¹ ∈ Q₁ := mul_mem (mul_mem hc₁ ha) (inv_mem hc₁)
  have h1 : c₁ * c₂ * (a * b) * (c₁ * c₂)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hcX _).mp hab
  have e1 : c₂ * a = a * c₂ := (h.comm a ha c₂ hc₂).symm
  have e2 : c₁ * (c₂ * b * c₂⁻¹) = (c₂ * b * c₂⁻¹) * c₁ :=
    h.comm c₁ hc₁ _ (mul_mem (mul_mem hc₂ hbQ) (inv_mem hc₂))
  have h2 : c₁ * c₂ * (a * b) * (c₁ * c₂)⁻¹ = (c₁ * a * c₁⁻¹) * (c₂ * b * c₂⁻¹) := by
    calc c₁ * c₂ * (a * b) * (c₁ * c₂)⁻¹ = c₁ * (c₂ * a) * b * c₂⁻¹ * c₁⁻¹ := by group
      _ = c₁ * (a * c₂) * b * c₂⁻¹ * c₁⁻¹ := by rw [e1]
      _ = c₁ * a * c₁⁻¹ * (c₁ * (c₂ * b * c₂⁻¹)) * c₁⁻¹ := by group
      _ = c₁ * a * c₁⁻¹ * ((c₂ * b * c₂⁻¹) * c₁) * c₁⁻¹ := by rw [e2]
      _ = (c₁ * a * c₁⁻¹) * (c₂ * b * c₂⁻¹) := by group
  rw [h2] at h1
  exact h.mem_img₂ hw (mul_mem (mul_mem hc₂ hbQ) (inv_mem hc₂)) h1

variable [Finite A] {Y₁ Y₂ : Subgroup A} (h₁ : Y₁ ≤ Q₁) (h₂ : Y₂ ≤ Q₂)
include h₁ h₂

theorem CommPair.img_le_of_sylow {P : Subgroup A} (hP : IsSylowTwoOf P (Y₁ ⊔ Y₂)) :
    h.img₁ P ≤ P ∧ h.img₂ P ≤ P := by
  have hPQ : P ≤ Q₁ ⊔ Q₂ := hP.1.trans (sup_le_sup h₁ h₂)
  have hP2 : IsPGroup 2 ↥(P.subgroupOf (Q₁ ⊔ Q₂)) := hP.2.1.comap_subtype
  have hX2 : IsPGroup 2 ↥(h.img₁ P ⊔ h.img₂ P) :=
    (hP2.map h.pr1).to_sup_of_normal_left' (hP2.map h.pr2)
      (le_normalizer_of_forall_comm fun a ha b hb => h.comm a (h.img₁_le P ha) b (h.img₂_le P hb))
  have hXY : h.img₁ P ⊔ h.img₂ P ≤ Y₁ ⊔ Y₂ :=
    sup_le_sup (h.img₁_le_of_le h₁ h₂ hP.1) (h.img₂_le_of_le h₁ h₂ hP.1)
  have hPX : P ≤ h.img₁ P ⊔ h.img₂ P := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_img hPQ hx
    exact Subgroup.mul_mem_sup ha hb
  have heq := hP.eq_of_le hPX hXY hX2
  exact ⟨le_sup_left.trans heq.le, le_sup_right.trans heq.le⟩

theorem CommPair.img₁_eq_of_sylow {P : Subgroup A} (hP : IsSylowTwoOf P (Y₁ ⊔ Y₂)) :
    h.img₁ P = P ⊓ Y₁ := by
  refine le_antisymm (le_inf (h.img_le_of_sylow h₁ h₂ hP).1 (h.img₁_le_of_le h₁ h₂ hP.1)) ?_
  intro a ha
  exact h.mem_img₁ (h₁ ha.2) (one_mem Q₂) (by rw [mul_one]; exact ha.1)

theorem CommPair.img₂_eq_of_sylow {P : Subgroup A} (hP : IsSylowTwoOf P (Y₁ ⊔ Y₂)) :
    h.img₂ P = P ⊓ Y₂ := by
  refine le_antisymm (le_inf (h.img_le_of_sylow h₁ h₂ hP).2 (h.img₂_le_of_le h₁ h₂ hP.1)) ?_
  intro b hb
  exact h.mem_img₂ (one_mem Q₁) (h₂ hb.2) (by rw [one_mul]; exact hb.1)

theorem CommPair.eq_sup_of_sylow {P : Subgroup A} (hP : IsSylowTwoOf P (Y₁ ⊔ Y₂)) :
    P = (P ⊓ Y₁) ⊔ (P ⊓ Y₂) := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_img (hP.1.trans (sup_le_sup h₁ h₂)) hx
  rw [h.img₁_eq_of_sylow h₁ h₂ hP] at ha
  rw [h.img₂_eq_of_sylow h₁ h₂ hP] at hb
  exact Subgroup.mul_mem_sup ha hb

theorem CommPair.isSylowTwoOf_inf₁ {P : Subgroup A} (hP : IsSylowTwoOf P (Y₁ ⊔ Y₂)) :
    IsSylowTwoOf (P ⊓ Y₁) Y₁ := by
  obtain ⟨S₁, hS₁le, hS₁⟩ := exists_isSylowTwoOf_of_le (inf_le_right : P ⊓ Y₁ ≤ Y₁)
    (hP.2.1.to_le inf_le_left)
  have hX2 : IsPGroup 2 ↥(S₁ ⊔ (P ⊓ Y₂)) :=
    hS₁.2.1.to_sup_of_normal_left' (hP.2.1.to_le inf_le_left)
      (le_normalizer_of_forall_comm fun a ha b hb => h.comm a (h₁ (hS₁.1 ha)) b (h₂ hb.2))
  have hXY : S₁ ⊔ (P ⊓ Y₂) ≤ Y₁ ⊔ Y₂ := sup_le_sup hS₁.1 inf_le_right
  have hPX : P ≤ S₁ ⊔ (P ⊓ Y₂) :=
    (h.eq_sup_of_sylow h₁ h₂ hP).le.trans (sup_le_sup_right hS₁le _)
  have heq := hP.eq_of_le hPX hXY hX2
  have hS : S₁ ≤ P ⊓ Y₁ := le_inf (le_sup_left.trans heq.le) hS₁.1
  rwa [le_antisymm hS hS₁le] at hS₁

theorem CommPair.isSylowTwoOf_inf₂ {P : Subgroup A} (hP : IsSylowTwoOf P (Y₁ ⊔ Y₂)) :
    IsSylowTwoOf (P ⊓ Y₂) Y₂ := by
  obtain ⟨S₂, hS₂le, hS₂⟩ := exists_isSylowTwoOf_of_le (inf_le_right : P ⊓ Y₂ ≤ Y₂)
    (hP.2.1.to_le inf_le_left)
  have hX2 : IsPGroup 2 ↥((P ⊓ Y₁) ⊔ S₂) :=
    (hP.2.1.to_le inf_le_left).to_sup_of_normal_left' hS₂.2.1
      (le_normalizer_of_forall_comm fun a ha b hb => h.comm a (h₁ ha.2) b (h₂ (hS₂.1 hb)))
  have hXY : (P ⊓ Y₁) ⊔ S₂ ≤ Y₁ ⊔ Y₂ := sup_le_sup inf_le_right hS₂.1
  have hPX : P ≤ (P ⊓ Y₁) ⊔ S₂ :=
    (h.eq_sup_of_sylow h₁ h₂ hP).le.trans (sup_le_sup_left hS₂le _)
  have heq := hP.eq_of_le hPX hXY hX2
  have hS : S₂ ≤ P ⊓ Y₂ := le_inf (le_sup_right.trans heq.le) hS₂.1
  rwa [le_antisymm hS hS₂le] at hS₂

end CFSG.Quasithin.H13.NQCat.C2

namespace CFSG.Quasithin.H13.NQCat.C2

open CFSG.QuasithinUnique

variable {A : Type} [Group A]

theorem le_of_isHallTwoPrimeOf [Finite A] {B M X : Subgroup A} (hB : Lin2.IsHallTwoPrimeOf B M)
    (hXM : X ≤ M) (hX : Odd (Nat.card X)) (hBX : B ≤ Subgroup.normalizer (X : Set A)) : X ≤ B := by
  obtain ⟨hBM, hBo, k, hk⟩ := hB
  have hM : Nat.card M = 2 ^ k * Nat.card B := by
    rw [← hk, ← Subgroup.relIndex_mul_card B _, inf_eq_left.mpr hBM]
  have hsup := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hBX
  have hodd : Odd (Nat.card ↥(X ⊔ B)) := by
    have h1 : Nat.card ↥(X ⊔ B) ∣ Nat.card X * Nat.card B := ⟨_, hsup.symm⟩
    exact Odd.of_dvd_nat (hX.mul hBo) h1
  have hdvd : Nat.card ↥(X ⊔ B) ∣ 2 ^ k * Nat.card B :=
    hM ▸ Subgroup.card_dvd_of_le (sup_le hXM hBM)
  have hdvd' : Nat.card ↥(X ⊔ B) ∣ Nat.card B :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_left hdvd
  have heq : B = X ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right
    (Nat.le_of_dvd Nat.card_pos hdvd')
  exact le_sup_left.trans heq.symm.le

end CFSG.Quasithin.H13.NQCat.C2
