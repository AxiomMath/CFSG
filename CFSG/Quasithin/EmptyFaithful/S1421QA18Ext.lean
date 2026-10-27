module

public import CFSG.Quasithin.EmptyFaithful.S1421QA18D
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421QA18

variable {G D : Type} [Group G] [Group D]

section Iso

variable {A₁ A₂ : Subgroup G} {P₁ P₂ : Subgroup D}
  (φ : (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups P₁ P₂))

@[expose] def iso1 : ↥A₁ ≃* ↥P₁ := φ.φ1

@[expose] def iso2 : ↥A₂ ≃* ↥P₂ := φ.φ2

@[expose] def iso12 : ↥(A₁ ⊓ A₂) ≃* ↥(P₁ ⊓ P₂) := φ.φ12

theorem iso12_eq1 (b : ↥(A₁ ⊓ A₂)) :
    ((iso12 φ b : ↥(P₁ ⊓ P₂)) : D) = ((iso1 φ ⟨b.1, b.2.1⟩ : ↥P₁) : D) :=
  congrArg Subtype.val (φ.comm1 b)

theorem iso12_eq2 (b : ↥(A₁ ⊓ A₂)) :
    ((iso12 φ b : ↥(P₁ ⊓ P₂)) : D) = ((iso2 φ ⟨b.1, b.2.2⟩ : ↥P₂) : D) :=
  congrArg Subtype.val (φ.comm2 b)

@[expose] noncomputable def f1 (g : G) : D :=
  open Classical in if h : g ∈ A₁ then ((iso1 φ ⟨g, h⟩ : ↥P₁) : D) else 1

@[expose] noncomputable def f2 (g : G) : D :=
  open Classical in if h : g ∈ A₂ then ((iso2 φ ⟨g, h⟩ : ↥P₂) : D) else 1

theorem f1_apply {g : G} (h : g ∈ A₁) : f1 φ g = ((iso1 φ ⟨g, h⟩ : ↥P₁) : D) := by
  classical
  simp [f1, h]

theorem f2_apply {g : G} (h : g ∈ A₂) : f2 φ g = ((iso2 φ ⟨g, h⟩ : ↥P₂) : D) := by
  classical
  simp [f2, h]

theorem f1_mem {g : G} (h : g ∈ A₁) : f1 φ g ∈ P₁ := by
  rw [f1_apply φ h]; exact (iso1 φ ⟨g, h⟩).2

theorem f2_mem {g : G} (h : g ∈ A₂) : f2 φ g ∈ P₂ := by
  rw [f2_apply φ h]; exact (iso2 φ ⟨g, h⟩).2

theorem f1_mul {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₁) : f1 φ (a * b) = f1 φ a * f1 φ b := by
  rw [f1_apply φ (A₁.mul_mem ha hb), f1_apply φ ha, f1_apply φ hb]
  have : (⟨a * b, A₁.mul_mem ha hb⟩ : ↥A₁) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [this, map_mul]
  rfl

theorem f2_mul {a b : G} (ha : a ∈ A₂) (hb : b ∈ A₂) : f2 φ (a * b) = f2 φ a * f2 φ b := by
  rw [f2_apply φ (A₂.mul_mem ha hb), f2_apply φ ha, f2_apply φ hb]
  have : (⟨a * b, A₂.mul_mem ha hb⟩ : ↥A₂) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [this, map_mul]
  rfl

theorem f1_one : f1 φ 1 = 1 := by
  have h := f1_mul φ A₁.one_mem A₁.one_mem
  rw [mul_one] at h
  exact left_eq_mul.mp h

theorem f2_one : f2 φ 1 = 1 := by
  have h := f2_mul φ A₂.one_mem A₂.one_mem
  rw [mul_one] at h
  exact left_eq_mul.mp h

theorem f1_inv {a : G} (ha : a ∈ A₁) : f1 φ a⁻¹ = (f1 φ a)⁻¹ := by
  have h := f1_mul φ (A₁.inv_mem ha) ha
  rw [inv_mul_cancel, f1_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem f2_inv {a : G} (ha : a ∈ A₂) : f2 φ a⁻¹ = (f2 φ a)⁻¹ := by
  have h := f2_mul φ (A₂.inv_mem ha) ha
  rw [inv_mul_cancel, f2_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem f1_inj {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₁) (h : f1 φ a = f1 φ b) : a = b := by
  rw [f1_apply φ ha, f1_apply φ hb] at h
  have := (iso1 φ).injective (Subtype.ext h)
  exact congrArg Subtype.val this

theorem f2_inj {a b : G} (ha : a ∈ A₂) (hb : b ∈ A₂) (h : f2 φ a = f2 φ b) : a = b := by
  rw [f2_apply φ ha, f2_apply φ hb] at h
  have := (iso2 φ).injective (Subtype.ext h)
  exact congrArg Subtype.val this

theorem exists_f1 {p : D} (hp : p ∈ P₁) : ∃ a ∈ A₁, f1 φ a = p := by
  obtain ⟨a, ha⟩ := (iso1 φ).surjective ⟨p, hp⟩
  exact ⟨a.1, a.2, by rw [f1_apply φ a.2]; exact congrArg Subtype.val ha⟩

theorem exists_f2 {p : D} (hp : p ∈ P₂) : ∃ a ∈ A₂, f2 φ a = p := by
  obtain ⟨a, ha⟩ := (iso2 φ).surjective ⟨p, hp⟩
  exact ⟨a.1, a.2, by rw [f2_apply φ a.2]; exact congrArg Subtype.val ha⟩

theorem f1_eq_f2 {a : G} (h1 : a ∈ A₁) (h2 : a ∈ A₂) : f1 φ a = f2 φ a := by
  rw [f1_apply φ h1, f2_apply φ h2]
  exact (iso12_eq1 φ ⟨a, h1, h2⟩).symm.trans (iso12_eq2 φ ⟨a, h1, h2⟩)

theorem mem_A₂_of_f1_mem {a : G} (ha : a ∈ A₁) (h : f1 φ a ∈ P₂) : a ∈ A₂ := by
  have hp : f1 φ a ∈ P₁ ⊓ P₂ := ⟨f1_mem φ ha, h⟩
  obtain ⟨b, hb⟩ := (iso12 φ).surjective ⟨f1 φ a, hp⟩
  have h1 : f1 φ b.1 = f1 φ a := by
    rw [f1_apply φ b.2.1, ← iso12_eq1 φ b]
    exact congrArg Subtype.val hb
  have : b.1 = a := f1_inj φ b.2.1 ha h1
  exact this ▸ b.2.2

theorem mem_A₁_of_f2_mem {a : G} (ha : a ∈ A₂) (h : f2 φ a ∈ P₁) : a ∈ A₁ := by
  have hp : f2 φ a ∈ P₁ ⊓ P₂ := ⟨h, f2_mem φ ha⟩
  obtain ⟨b, hb⟩ := (iso12 φ).surjective ⟨f2 φ a, hp⟩
  have h1 : f2 φ b.1 = f2 φ a := by
    rw [f2_apply φ b.2.2, ← iso12_eq2 φ b]
    exact congrArg Subtype.val hb
  have : b.1 = a := f2_inj φ b.2.2 ha h1
  exact this ▸ b.2.1

theorem centralizes_of_conj_eq_one {b : G} (hb₁ : b ∈ A₁) (hb₂ : b ∈ A₂)
    (h : MulAut.conj (f1 φ b) = 1) :
    (∀ a ∈ A₁, b * a * b⁻¹ = a) ∧ (∀ a ∈ A₂, b * a * b⁻¹ = a) := by
  have hc : ∀ x : D, f1 φ b * x * (f1 φ b)⁻¹ = x := fun x => by
    have := congrArg (fun ρ : MulAut D => ρ x) h
    simpa [MulAut.conj_apply] using this
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine f1_inj φ (A₁.mul_mem (A₁.mul_mem hb₁ ha) (A₁.inv_mem hb₁)) ha ?_
    rw [f1_mul φ (A₁.mul_mem hb₁ ha) (A₁.inv_mem hb₁), f1_mul φ hb₁ ha, f1_inv φ hb₁, hc]
  · have hc2 : ∀ x : D, f2 φ b * x * (f2 φ b)⁻¹ = x := fun x => by
      rw [← f1_eq_f2 φ hb₁ hb₂]; exact hc x
    refine f2_inj φ (A₂.mul_mem (A₂.mul_mem hb₂ ha) (A₂.inv_mem hb₂)) ha ?_
    rw [f2_mul φ (A₂.mul_mem hb₂ ha) (A₂.inv_mem hb₂), f2_mul φ hb₂ ha, f2_inv φ hb₂, hc2]

end Iso

section Ext

theorem mulAut_conj_eq (ρ : MulAut D) (d : D) :
    ρ * MulAut.conj d * ρ⁻¹ = MulAut.conj (ρ d) := by
  ext x
  simp [MulAut.conj_apply]

theorem normal_conj_range : ((MulAut.conj : D →* MulAut D).range).Normal := by
  refine ⟨fun n hn ρ => ?_⟩
  obtain ⟨d, rfl⟩ := hn
  exact ⟨ρ d, (mulAut_conj_eq ρ d).symm⟩

theorem conj_mem_autStab_iff {P : Subgroup D} {d : D} :
    MulAut.conj d ∈ autStab P ↔ d ∈ Subgroup.normalizer (P : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h x
    simpa [MulAut.conj_apply] using this
  · intro h x
    have := h x
    simpa [MulAut.conj_apply] using this

theorem normalizer_of_forall {A M : Subgroup G}
    (hn : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) {m : G} (hm : m ∈ M) :
    m ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hn m hm h, fun hh => ?_⟩
  have := hn m⁻¹ (M.inv_mem hm) _ hh
  simpa [mul_assoc] using this

theorem exists_mul_of_le_sup {A M N : Subgroup G} (hNM : N ≤ M)
    (hn : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hM : M ≤ A ⊔ N) {m : G} (hm : m ∈ M) :
    ∃ a ∈ A, ∃ x ∈ N, a * x = m := by
  have hNn : N ≤ Subgroup.normalizer (A : Set G) := fun x hx =>
    normalizer_of_forall hn (hNM hx)
  have h1 : m ∈ ((A ⊔ N : Subgroup G) : Set G) := hM hm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A N hNn, Set.mem_mul] at h1
  obtain ⟨a, ha, x, hx, rfl⟩ := h1
  exact ⟨a, ha, x, hx, rfl⟩

theorem exists_theta {A M N : Subgroup G}
    (f : G → D) (ψ : ↥N →* MulAut D) (hNM : N ≤ M) (hAM : A ≤ M)
    (hn : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hM : M ≤ A ⊔ N)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b)
    (hψ : ∀ (x : G) (hx : x ∈ N) (a : G), a ∈ A → ψ ⟨x, hx⟩ (f a) = f (x * a * x⁻¹))
    (hinn : ∀ (b : G) (hbN : b ∈ N), b ∈ A → ψ ⟨b, hbN⟩ = MulAut.conj (f b)) :
    ∃ Θ : ↥M →* MulAut D, ∀ (a x : G) (ha : a ∈ A) (hx : x ∈ N),
      Θ ⟨a * x, M.mul_mem (hAM ha) (hNM hx)⟩ = MulAut.conj (f a) * ψ ⟨x, hx⟩ := by
  classical
  have hdec := fun m (hm : m ∈ M) => exists_mul_of_le_sup hNM hn hM hm
  have hdec' := hdec
  choose! a ha x hx hax using hdec
  have hf1 : f 1 = 1 := by
    have := hmul 1 A.one_mem 1 A.one_mem
    simpa using this
  let θ : G → MulAut D := fun m =>
    if h : m ∈ M then MulAut.conj (f (a m)) * ψ ⟨x m, hx m h⟩ else 1
  have hspec : ∀ (a' x' : G) (ha' : a' ∈ A) (hx' : x' ∈ N),
      θ (a' * x') = MulAut.conj (f a') * ψ ⟨x', hx'⟩ := by
    intro a' x' ha' hx'
    have hm : a' * x' ∈ M := M.mul_mem (hAM ha') (hNM hx')
    simp only [θ, hm, dite_true]
    set m := a' * x' with hmdef
    have e : a m * x m = a' * x' := by rw [hax m hm]
    set y : G := a'⁻¹ * a m with hy
    have hyA : y ∈ A := A.mul_mem (A.inv_mem ha') (ha m hm)
    have hyx : y = x' * (x m)⁻¹ := by
      rw [hy]
      calc a'⁻¹ * a m = a'⁻¹ * (a m * x m) * (x m)⁻¹ := by group
        _ = a'⁻¹ * (a' * x') * (x m)⁻¹ := by rw [e]
        _ = x' * (x m)⁻¹ := by group
    have hyN : y ∈ N := hyx ▸ N.mul_mem hx' (N.inv_mem (hx m hm))
    have h1 := hinn y hyN hyA
    have h2 : a m = a' * y := by rw [hy]; group
    have h3 : x m = y⁻¹ * x' := by rw [hyx]; group
    have h4 : (⟨x m, hx m hm⟩ : ↥N) = ⟨y, hyN⟩⁻¹ * ⟨x', hx'⟩ :=
      Subtype.ext (by simpa using h3)
    rw [h4, map_mul, map_inv, h1, h2, hmul a' ha' y hyA, map_mul]
    group
  have hf1' : θ 1 = 1 := by
    have := hspec 1 1 A.one_mem N.one_mem
    rw [one_mul] at this
    rw [this, hf1]
    have h1 : (⟨1, N.one_mem⟩ : ↥N) = 1 := rfl
    rw [h1]
    simp
  refine ⟨
    { toFun := fun m => θ m.1
      map_one' := hf1'
      map_mul' := ?_ }, ?_⟩
  · intro m m'
    obtain ⟨a₀, ha₀, x₀, hx₀, hm⟩ := hdec' m.1 m.2
    obtain ⟨a₁, ha₁, x₁, hx₁, hm'⟩ := hdec' m'.1 m'.2
    show θ (m.1 * m'.1) = θ m.1 * θ m'.1
    have hb : x₀ * a₁ * x₀⁻¹ ∈ A := hn x₀ (hNM hx₀) a₁ ha₁
    have e : m.1 * m'.1 = (a₀ * (x₀ * a₁ * x₀⁻¹)) * (x₀ * x₁) := by
      rw [← hm, ← hm']; group
    have hθm : θ m.1 = MulAut.conj (f a₀) * ψ ⟨x₀, hx₀⟩ := by
      rw [← hm]; exact hspec _ _ ha₀ hx₀
    have hθm' : θ m'.1 = MulAut.conj (f a₁) * ψ ⟨x₁, hx₁⟩ := by
      rw [← hm']; exact hspec _ _ ha₁ hx₁
    rw [e, hspec _ _ (A.mul_mem ha₀ hb) (N.mul_mem hx₀ hx₁), hθm, hθm',
      hmul _ ha₀ _ hb]
    have key : MulAut.conj (f (x₀ * a₁ * x₀⁻¹)) * ψ ⟨x₀, hx₀⟩ =
        ψ ⟨x₀, hx₀⟩ * MulAut.conj (f a₁) := by
      rw [← hψ x₀ hx₀ a₁ ha₁, ← mulAut_conj_eq]
      group
    have hx01 : (⟨x₀ * x₁, N.mul_mem hx₀ hx₁⟩ : ↥N) = ⟨x₀, hx₀⟩ * ⟨x₁, hx₁⟩ := rfl
    rw [hx01]
    simp only [map_mul]
    calc MulAut.conj (f a₀) * MulAut.conj (f (x₀ * a₁ * x₀⁻¹)) *
          (ψ ⟨x₀, hx₀⟩ * ψ ⟨x₁, hx₁⟩)
        = MulAut.conj (f a₀) * (MulAut.conj (f (x₀ * a₁ * x₀⁻¹)) * ψ ⟨x₀, hx₀⟩) *
            ψ ⟨x₁, hx₁⟩ := by group
      _ = _ := by rw [key]; group
  · intro a' x' ha' hx'
    exact hspec a' x' ha' hx'

end Ext

section Vertex

theorem vertex_bijective {A M N : Subgroup G} {P P' : Subgroup D}
    (f : G → D) (ψ : ↥N →* MulAut D)
    (hNM : N ≤ M) (hAM : A ≤ M)
    (hn : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hM : M ≤ A ⊔ N)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b)
    (hfP : ∀ a ∈ A, f a ∈ P) (hfsurj : ∀ p ∈ P, ∃ a ∈ A, f a = p)
    (hψ : ∀ (x : G) (hx : x ∈ N) (a : G), a ∈ A → ψ ⟨x, hx⟩ (f a) = f (x * a * x⁻¹))
    (hinn : ∀ (b : G) (hbN : b ∈ N), b ∈ A → ψ ⟨b, hbN⟩ = MulAut.conj (f b))
    (hψinj : Function.Injective ψ)
    (hψP : ∀ x : ↥N, ψ x ∈ autStab P) (hψP' : ∀ x : ↥N, ψ x ∈ autStab P')
    (hP : Subgroup.normalizer (P : Set D) = P) (hP' : Subgroup.normalizer (P' : Set D) = P')
    (hfN : ∀ a ∈ A, f a ∈ P' → a ∈ N) :
    ∃ Θ : ↥M →* MulAut D,
      (∀ (x : G) (hx : x ∈ N), Θ ⟨x, hNM hx⟩ = ψ ⟨x, hx⟩) ∧
      (∀ m, Θ m ∈ ((MulAut.conj : D →* MulAut D).range ⊔ ψ.range) ⊓ autStab P) ∧
      Function.Injective Θ ∧
      (∀ ρ ∈ ((MulAut.conj : D →* MulAut D).range ⊔ ψ.range) ⊓ autStab P, ∃ m, Θ m = ρ) ∧
      (∀ ρ ∈ ((MulAut.conj : D →* MulAut D).range ⊔ ψ.range) ⊓ autStab P, ρ ∈ autStab P' →
        ∃ x : ↥N, ψ x = ρ) := by
  obtain ⟨Θ, hΘ⟩ := exists_theta f ψ hNM hAM hn hM hmul hψ hinn
  have hf1 : f 1 = 1 := by
    have := hmul 1 A.one_mem 1 A.one_mem
    simpa using this
  have hMbarmem : ∀ (d : D) (x : ↥N), MulAut.conj d * ψ x ∈
      (MulAut.conj : D →* MulAut D).range ⊔ ψ.range := fun d x =>
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨d, rfl⟩) (Subgroup.mem_sup_right ⟨x, rfl⟩)
  have hNcompat : ∀ (x : G) (hx : x ∈ N), Θ ⟨x, hNM hx⟩ = ψ ⟨x, hx⟩ := by
    intro x hx
    have := hΘ 1 x A.one_mem hx
    have e : (⟨1 * x, M.mul_mem (hAM A.one_mem) (hNM hx)⟩ : ↥M) = ⟨x, hNM hx⟩ :=
      Subtype.ext (one_mul x)
    rw [e, hf1] at this
    simpa using this
  have hmem : ∀ m, Θ m ∈ ((MulAut.conj : D →* MulAut D).range ⊔ ψ.range) ⊓ autStab P := by
    intro m
    obtain ⟨a, ha, x, hx, hax⟩ := exists_mul_of_le_sup hNM hn hM m.2
    have e : m = ⟨a * x, M.mul_mem (hAM ha) (hNM hx)⟩ := Subtype.ext hax.symm
    rw [e, hΘ a x ha hx]
    refine ⟨hMbarmem _ _, ?_⟩
    exact Subgroup.mul_mem _
      (conj_mem_autStab_iff.mpr (by rw [hP]; exact hfP a ha)) (hψP ⟨x, hx⟩)
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    obtain ⟨a, ha, x, hx, hax⟩ := exists_mul_of_le_sup hNM hn hM m.2
    have e : m = ⟨a * x, M.mul_mem (hAM ha) (hNM hx)⟩ := Subtype.ext hax.symm
    rw [e, hΘ a x ha hx] at hm
    have h1 : ψ ⟨x, hx⟩ = (MulAut.conj (f a))⁻¹ := eq_inv_of_mul_eq_one_right hm
    have h2 : MulAut.conj (f a)⁻¹ ∈ autStab P' := by
      rw [map_inv, ← h1]; exact hψP' _
    have h3 : (f a)⁻¹ ∈ P' := by rw [← hP']; exact conj_mem_autStab_iff.mp h2
    have h4 : a ∈ N := hfN a ha (by simpa using P'.inv_mem h3)
    have h5 := hinn a h4 ha
    have h6 : ψ (⟨a, h4⟩ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, h5, h1]; simp
    have h7 : (⟨a, h4⟩ * ⟨x, hx⟩ : ↥N) = 1 := hψinj (h6.trans (map_one ψ).symm)
    have h8 : a * x = 1 := congrArg Subtype.val h7
    exact Subtype.ext (by rw [e]; exact h8)
  have hdecomp : ∀ ρ ∈ ((MulAut.conj : D →* MulAut D).range ⊔ ψ.range) ⊓ autStab P,
      ∃ (a : G) (ha : a ∈ A) (x : ↥N), ρ = MulAut.conj (f a) * ψ x := by
    intro ρ hρ
    obtain ⟨hρ1, hρ2⟩ := Subgroup.mem_inf.mp hρ
    have := normal_conj_range (D := D)
    rw [Subgroup.mem_sup_of_normal_left] at hρ1
    obtain ⟨_, ⟨d, rfl⟩, _, ⟨x, rfl⟩, hρe⟩ := hρ1
    have hcd : MulAut.conj d ∈ autStab P := by
      have h1 : MulAut.conj d = ρ * (ψ x)⁻¹ := by rw [← hρe]; group
      rw [h1]
      exact Subgroup.mul_mem _ hρ2 (Subgroup.inv_mem _ (hψP x))
    have hdP : d ∈ P := by rw [← hP]; exact conj_mem_autStab_iff.mp hcd
    obtain ⟨a, ha, hfa⟩ := hfsurj d hdP
    exact ⟨a, ha, x, by rw [hfa, ← hρe]⟩
  refine ⟨Θ, hNcompat, hmem, hinj, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨a, ha, x, hρe⟩ := hdecomp ρ hρ
    refine ⟨⟨a * x, M.mul_mem (hAM ha) (hNM x.2)⟩, ?_⟩
    rw [hΘ a x ha x.2, hρe]
  · intro ρ hρ hρ'
    obtain ⟨a, ha, x, hρe⟩ := hdecomp ρ hρ
    have hca : MulAut.conj (f a) ∈ autStab P' := by
      have h1 : MulAut.conj (f a) = ρ * (ψ x)⁻¹ := by rw [hρe]; group
      rw [h1]
      exact Subgroup.mul_mem _ hρ' (Subgroup.inv_mem _ (hψP' x))
    have hfaP' : f a ∈ P' := by rw [← hP']; exact conj_mem_autStab_iff.mp hca
    have haN : a ∈ N := hfN a ha hfaP'
    refine ⟨⟨a, haN⟩ * x, ?_⟩
    rw [map_mul, hinn a haN ha, hρe]

end Vertex

section Main

structure ExtData (G D : Type) [Group G] [Group D] where
  A₁ : Subgroup G
  A₂ : Subgroup G
  M₁ : Subgroup G
  M₂ : Subgroup G
  TD : Subgroup D
  P₁ : Subgroup D
  P₂ : Subgroup D
  φ : (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups P₁ P₂)
  ψ : ↥(M₁ ⊓ M₂) →* MulAut D
  yam : IsYAmalgamPair TD P₁ P₂
  hA₁ : A₁ ≤ M₁
  hA₂ : A₂ ≤ M₂
  hn₁ : ∀ m ∈ M₁, ∀ a ∈ A₁, m * a * m⁻¹ ∈ A₁
  hn₂ : ∀ m ∈ M₂, ∀ a ∈ A₂, m * a * m⁻¹ ∈ A₂
  hM₁ : M₁ ≤ A₁ ⊔ (M₁ ⊓ M₂)
  hM₂ : M₂ ≤ A₂ ⊔ (M₁ ⊓ M₂)
  hi₁ : A₁ ⊓ M₂ ≤ A₂
  hi₂ : A₂ ⊓ M₁ ≤ A₁
  hψ₁ : ∀ (x : G) (hx : x ∈ M₁ ⊓ M₂) (a : G), a ∈ A₁ →
    ψ ⟨x, hx⟩ (f1 φ a) = f1 φ (x * a * x⁻¹)
  hψ₂ : ∀ (x : G) (hx : x ∈ M₁ ⊓ M₂) (a : G), a ∈ A₂ →
    ψ ⟨x, hx⟩ (f2 φ a) = f2 φ (x * a * x⁻¹)
  hψinj : Function.Injective ψ
  hψinn : ∀ (b : G) (hb : b ∈ M₁ ⊓ M₂), b ∈ A₁ → b ∈ A₂ →
    ψ ⟨b, hb⟩ = MulAut.conj (f1 φ b)

namespace ExtData

variable {G D : Type} [Group G] [Group D] (E : ExtData G D)

theorem psi_mem_autStab₁ (x : ↥(E.M₁ ⊓ E.M₂)) : E.ψ x ∈ autStab E.P₁ := by
  obtain ⟨x, hx⟩ := x
  show ∀ y : D, y ∈ E.P₁ ↔ E.ψ ⟨x, hx⟩ y ∈ E.P₁
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := exists_f1 E.φ hy
    rw [E.hψ₁ x hx a ha]
    exact f1_mem E.φ (E.hn₁ x hx.1 a ha)
  · intro h
    obtain ⟨a', ha', hfa'⟩ := exists_f1 E.φ h
    have ha : x⁻¹ * a' * x ∈ E.A₁ := by
      simpa using E.hn₁ x⁻¹ (E.M₁.inv_mem hx.1) a' ha'
    have h1 := E.hψ₁ x hx (x⁻¹ * a' * x) ha
    rw [show x * (x⁻¹ * a' * x) * x⁻¹ = a' by group, hfa'] at h1
    have h2 : f1 E.φ (x⁻¹ * a' * x) = y := (E.ψ ⟨x, hx⟩).injective h1
    rw [← h2]
    exact f1_mem E.φ ha

theorem psi_mem_autStab₂ (x : ↥(E.M₁ ⊓ E.M₂)) : E.ψ x ∈ autStab E.P₂ := by
  obtain ⟨x, hx⟩ := x
  show ∀ y : D, y ∈ E.P₂ ↔ E.ψ ⟨x, hx⟩ y ∈ E.P₂
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := exists_f2 E.φ hy
    rw [E.hψ₂ x hx a ha]
    exact f2_mem E.φ (E.hn₂ x hx.2 a ha)
  · intro h
    obtain ⟨a', ha', hfa'⟩ := exists_f2 E.φ h
    have ha : x⁻¹ * a' * x ∈ E.A₂ := by
      simpa using E.hn₂ x⁻¹ (E.M₂.inv_mem hx.2) a' ha'
    have h1 := E.hψ₂ x hx (x⁻¹ * a' * x) ha
    rw [show x * (x⁻¹ * a' * x) * x⁻¹ = a' by group, hfa'] at h1
    have h2 : f2 E.φ (x⁻¹ * a' * x) = y := (E.ψ ⟨x, hx⟩).injective h1
    rw [← h2]
    exact f2_mem E.φ ha

theorem isExtension [Finite G] : IsExtensionOfLieAmalgam D E.M₁ E.M₂ := by
  classical
  have hfinP₁ : Finite ↥E.P₁ := Finite.of_equiv _ (iso1 E.φ).toEquiv
  have hfinP₂ : Finite ↥E.P₂ := Finite.of_equiv _ (iso2 E.φ).toEquiv
  have hfinB : Finite ↥(E.P₁ ⊓ E.P₂) := Finite.of_equiv _ (iso12 E.φ).toEquiv
  have hN1 := normalizer_eq_of_isMaximalTwoLocal (yamPair_left E.yam)
  have hN2 := normalizer_eq_of_isMaximalTwoLocal (yamPair_right E.yam)
  have hNB := normalizer_inf_eq E.yam
  obtain ⟨Θ₁, hΘ₁N, hΘ₁mem, hΘ₁inj, hΘ₁surj, hΘ₁mid⟩ :=
    vertex_bijective (A := E.A₁) (M := E.M₁) (N := E.M₁ ⊓ E.M₂) (P := E.P₁) (P' := E.P₂)
      (f1 E.φ) E.ψ inf_le_left E.hA₁ E.hn₁ E.hM₁ (fun a ha b hb => f1_mul E.φ ha hb)
      (fun a ha => f1_mem E.φ ha) (fun p hp => exists_f1 E.φ hp) E.hψ₁
      (fun b hbN hbA => E.hψinn b hbN hbA (E.hi₁ ⟨hbA, hbN.2⟩)) E.hψinj
      E.psi_mem_autStab₁ E.psi_mem_autStab₂ hN1 hN2
      (fun a ha h => ⟨E.hA₁ ha, E.hA₂ (mem_A₂_of_f1_mem E.φ ha h)⟩)
  obtain ⟨Θ₂, hΘ₂N, hΘ₂mem, hΘ₂inj, hΘ₂surj, -⟩ :=
    vertex_bijective (A := E.A₂) (M := E.M₂) (N := E.M₁ ⊓ E.M₂) (P := E.P₂) (P' := E.P₁)
      (f2 E.φ) E.ψ inf_le_right E.hA₂ E.hn₂ E.hM₂ (fun a ha b hb => f2_mul E.φ ha hb)
      (fun a ha => f2_mem E.φ ha) (fun p hp => exists_f2 E.φ hp) E.hψ₂
      (fun b hbN hbA => by
        have hbA₁ : b ∈ E.A₁ := E.hi₂ ⟨hbA, hbN.1⟩
        rw [E.hψinn b hbN hbA₁ hbA, f1_eq_f2 E.φ hbA₁ hbA]) E.hψinj
      E.psi_mem_autStab₂ E.psi_mem_autStab₁ hN2 hN1
      (fun a ha h => ⟨E.hA₁ (mem_A₁_of_f2_mem E.φ ha h), E.hA₂ ha⟩)
  refine ⟨(MulAut.conj : D →* MulAut D).range ⊔ E.ψ.range, E.TD, E.P₁, E.P₂, le_sup_left,
    E.yam, ?_, ?_⟩
  · intro ρ hρ hρ'
    have := normal_conj_range (D := D)
    rw [Subgroup.mem_sup_of_normal_left] at hρ
    obtain ⟨_, ⟨d, rfl⟩, _, ⟨x, rfl⟩, hρe⟩ := hρ
    have hψB : E.ψ x ∈ autStab (E.P₁ ⊓ E.P₂) := by
      intro y
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(E.psi_mem_autStab₁ x y).mp h1, (E.psi_mem_autStab₂ x y).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(E.psi_mem_autStab₁ x y).mpr h1, (E.psi_mem_autStab₂ x y).mpr h2⟩
    have hcd : MulAut.conj d ∈ autStab (E.P₁ ⊓ E.P₂) := by
      have h1 : MulAut.conj d = ρ * (E.ψ x)⁻¹ := by rw [← hρe]; group
      rw [h1]
      exact Subgroup.mul_mem _ hρ' (Subgroup.inv_mem _ hψB)
    have hdB : d ∈ E.P₁ ⊓ E.P₂ := by rw [← hNB]; exact conj_mem_autStab_iff.mp hcd
    rw [← hρe]
    exact Subgroup.mul_mem _ (conj_mem_autStab_iff.mpr (by rw [hN1]; exact hdB.1))
      (E.psi_mem_autStab₁ x)
  · have hψmem : ∀ x : ↥(E.M₁ ⊓ E.M₂), E.ψ x ∈
        (((MulAut.conj : D →* MulAut D).range ⊔ E.ψ.range) ⊓ autStab E.P₁) ⊓
        (((MulAut.conj : D →* MulAut D).range ⊔ E.ψ.range) ⊓ autStab E.P₂) := fun x =>
      ⟨⟨Subgroup.mem_sup_right ⟨x, rfl⟩, E.psi_mem_autStab₁ x⟩,
        ⟨Subgroup.mem_sup_right ⟨x, rfl⟩, E.psi_mem_autStab₂ x⟩⟩
    refine ⟨
      { φ1 := MulEquiv.ofBijective (Θ₁.codRestrict _ hΘ₁mem)
          ⟨fun a b h => hΘ₁inj (congrArg Subtype.val h), fun ρ => by
            obtain ⟨m, hm⟩ := hΘ₁surj ρ.1 ρ.2
            exact ⟨m, Subtype.ext hm⟩⟩
        φ12 := MulEquiv.ofBijective (E.ψ.codRestrict _ hψmem)
          ⟨fun a b h => E.hψinj (congrArg Subtype.val h), fun ρ => by
            obtain ⟨x, hx⟩ := hΘ₁mid ρ.1 ρ.2.1 ρ.2.2.2
            exact ⟨x, Subtype.ext hx⟩⟩
        φ2 := MulEquiv.ofBijective (Θ₂.codRestrict _ hΘ₂mem)
          ⟨fun a b h => hΘ₂inj (congrArg Subtype.val h), fun ρ => by
            obtain ⟨m, hm⟩ := hΘ₂surj ρ.1 ρ.2
            exact ⟨m, Subtype.ext hm⟩⟩
        comm1 := fun g => Subtype.ext ((hΘ₁N g.1 g.2).symm)
        comm2 := fun g => Subtype.ext ((hΘ₂N g.1 g.2).symm) }⟩

end ExtData

end Main

section CaseA

@[expose] noncomputable def innPsi {A₁ A₂ : Subgroup G} {P₁ P₂ : Subgroup D}
    (φ : (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups P₁ P₂)) :
    ↥(A₁ ⊓ A₂) →* MulAut D :=
  (MulAut.conj : D →* MulAut D).comp ((P₁ ⊓ P₂).subtype.comp (iso12 φ).toMonoidHom)

theorem innPsi_apply {A₁ A₂ : Subgroup G} {P₁ P₂ : Subgroup D}
    (φ : (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups P₁ P₂))
    (b : ↥(A₁ ⊓ A₂)) : innPsi φ b = MulAut.conj (f1 φ b.1) := by
  show MulAut.conj ((iso12 φ b : ↥(P₁ ⊓ P₂)) : D) = _
  rw [iso12_eq1 φ b, f1_apply φ b.2.1]

theorem innPsi_apply₂ {A₁ A₂ : Subgroup G} {P₁ P₂ : Subgroup D}
    (φ : (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups P₁ P₂))
    (b : ↥(A₁ ⊓ A₂)) : innPsi φ b = MulAut.conj (f2 φ b.1) := by
  rw [innPsi_apply, f1_eq_f2 φ b.2.1 b.2.2]

theorem isExtension_of_iso [Finite G] {A₁ A₂ : Subgroup G} {TD P₁ P₂ : Subgroup D}
    (φ : (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups P₁ P₂))
    (yam : IsYAmalgamPair TD P₁ P₂)
    (hcent : ∀ b : G, b ∈ A₁ → b ∈ A₂ → MulAut.conj (f1 φ b) = 1 → b = 1) :
    IsExtensionOfLieAmalgam D A₁ A₂ := by
  have hinj : Function.Injective (innPsi φ) := by
    rw [injective_iff_map_eq_one]
    intro b hb
    rw [innPsi_apply] at hb
    exact Subtype.ext (hcent b.1 b.2.1 b.2.2 hb)
  refine (ExtData.mk A₁ A₂ A₁ A₂ TD P₁ P₂ φ (innPsi φ) yam le_rfl le_rfl
    (fun m hm a ha => A₁.mul_mem (A₁.mul_mem hm ha) (A₁.inv_mem hm))
    (fun m hm a ha => A₂.mul_mem (A₂.mul_mem hm ha) (A₂.inv_mem hm))
    le_sup_left le_sup_left inf_le_right inf_le_right ?_ ?_ hinj ?_).isExtension
  · intro x hx a ha
    have := innPsi_apply φ ⟨x, hx⟩
    rw [this]
    simp only [MulAut.conj_apply]
    rw [f1_mul φ (A₁.mul_mem hx.1 ha) (A₁.inv_mem hx.1), f1_mul φ hx.1 ha, f1_inv φ hx.1]
  · intro x hx a ha
    have := innPsi_apply₂ φ ⟨x, hx⟩
    rw [this]
    simp only [MulAut.conj_apply]
    rw [f2_mul φ (A₂.mul_mem hx.2 ha) (A₂.inv_mem hx.2), f2_mul φ hx.2 ha, f2_inv φ hx.2]
  · intro b hb _ _
    exact innPsi_apply φ ⟨b, hb⟩

end CaseA

end S1421QA18

end CFSG.Quasithin
