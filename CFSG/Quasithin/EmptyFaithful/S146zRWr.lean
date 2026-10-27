module

public import Mathlib.GroupTheory.RegularWreathProduct

public section

namespace CFSG.Quasithin

namespace QWr

section Conj

variable {X : Type} [Group X]

theorem mem_map_conj {K : Subgroup X} {x z : X} :
    z ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * z * x ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_mul (x y : X) (K : Subgroup X) :
    K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  ext z
  simp only [mem_map_conj]
  have h : (x * y)⁻¹ * z * (x * y) = y⁻¹ * (x⁻¹ * z * x) * y := by group
  rw [h]

theorem map_conj_injective (x : X) {K L : Subgroup X}
    (h : K.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj x).toMonoidHom) : K = L :=
  Subgroup.map_injective (MulAut.conj x).injective h

end Conj

section Z2

theorem Z2_cases (z : Multiplicative (ZMod 2)) : z = 1 ∨ z = Multiplicative.ofAdd 1 := by
  revert z
  decide

theorem Z2_gen_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

theorem Z2_gen_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide

end Z2

section Sign

variable {X : Type} [Group X]

open Classical in
noncomputable def sgnFun (N₁ : Subgroup X) (x : X) : Multiplicative (ZMod 2) :=
  if N₁.map (MulAut.conj x).toMonoidHom = N₁ then 1 else Multiplicative.ofAdd 1

theorem sgnFun_of_eq {N₁ : Subgroup X} {x : X} (h : N₁.map (MulAut.conj x).toMonoidHom = N₁) :
    sgnFun N₁ x = 1 := by
  unfold sgnFun
  rw [ite_eq_left h]

theorem sgnFun_of_ne {N₁ : Subgroup X} {x : X} (h : N₁.map (MulAut.conj x).toMonoidHom ≠ N₁) :
    sgnFun N₁ x = Multiplicative.ofAdd 1 := by
  unfold sgnFun
  rw [ite_eq_right h]

theorem sgnFun_eq_one_iff {N₁ : Subgroup X} {x : X} :
    sgnFun N₁ x = 1 ↔ N₁.map (MulAut.conj x).toMonoidHom = N₁ := by
  by_cases h : N₁.map (MulAut.conj x).toMonoidHom = N₁
  · rw [sgnFun_of_eq h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [sgnFun_of_ne h]
    exact ⟨fun h' => absurd h' Z2_gen_ne_one, fun h' => absurd h' h⟩

variable {N₁ N₂ : Subgroup X} {s : X}

theorem conj_N₂_cases (hs : N₂ = N₁.map (MulAut.conj s).toMonoidHom)
    (hperm : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ ∨
      N₁.map (MulAut.conj x).toMonoidHom = N₂) (x : X) :
    N₂.map (MulAut.conj x).toMonoidHom = N₁ ∨ N₂.map (MulAut.conj x).toMonoidHom = N₂ := by
  have h : N₂.map (MulAut.conj x).toMonoidHom = N₁.map (MulAut.conj (x * s)).toMonoidHom := by
    rw [map_conj_mul, ← hs]
  rw [h]
  exact hperm (x * s)

theorem sgnFun_mul (hs : N₂ = N₁.map (MulAut.conj s).toMonoidHom) (hne : N₁ ≠ N₂)
    (hperm : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ ∨
      N₁.map (MulAut.conj x).toMonoidHom = N₂) (x y : X) :
    sgnFun N₁ (x * y) = sgnFun N₁ x * sgnFun N₁ y := by
  have hfix : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ →
      N₂.map (MulAut.conj x).toMonoidHom = N₂ := by
    intro x hx
    rcases conj_N₂_cases hs hperm x with h | h
    · exact absurd (map_conj_injective x (hx.trans h.symm)) hne
    · exact h
  have hswap : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₂ →
      N₂.map (MulAut.conj x).toMonoidHom = N₁ := by
    intro x hx
    rcases conj_N₂_cases hs hperm x with h | h
    · exact h
    · exact absurd (map_conj_injective x (hx.trans h.symm)) hne
  by_cases hx : N₁.map (MulAut.conj x).toMonoidHom = N₁
  · by_cases hy : N₁.map (MulAut.conj y).toMonoidHom = N₁
    · have hxy : N₁.map (MulAut.conj (x * y)).toMonoidHom = N₁ := by
        rw [map_conj_mul, hy, hx]
      rw [sgnFun_of_eq hxy, sgnFun_of_eq hx, sgnFun_of_eq hy, mul_one]
    · have hy2 : N₁.map (MulAut.conj y).toMonoidHom = N₂ := (hperm y).resolve_left hy
      have hxy : N₁.map (MulAut.conj (x * y)).toMonoidHom ≠ N₁ := by
        rw [map_conj_mul, hy2, hfix x hx]
        exact hne.symm
      rw [sgnFun_of_ne hxy, sgnFun_of_eq hx, sgnFun_of_ne hy, one_mul]
  · have hx2 : N₁.map (MulAut.conj x).toMonoidHom = N₂ := (hperm x).resolve_left hx
    by_cases hy : N₁.map (MulAut.conj y).toMonoidHom = N₁
    · have hxy : N₁.map (MulAut.conj (x * y)).toMonoidHom ≠ N₁ := by
        rw [map_conj_mul, hy, hx2]
        exact hne.symm
      rw [sgnFun_of_ne hxy, sgnFun_of_ne hx, sgnFun_of_eq hy, mul_one]
    · have hy2 : N₁.map (MulAut.conj y).toMonoidHom = N₂ := (hperm y).resolve_left hy
      have hxy : N₁.map (MulAut.conj (x * y)).toMonoidHom = N₁ := by
        rw [map_conj_mul, hy2, hswap x hx2]
      rw [sgnFun_of_eq hxy, sgnFun_of_ne hx, sgnFun_of_ne hy, Z2_gen_mul_self]

theorem exists_sigma (hs : N₂ = N₁.map (MulAut.conj s).toMonoidHom) (hne : N₁ ≠ N₂)
    (hperm : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ ∨
      N₁.map (MulAut.conj x).toMonoidHom = N₂) :
    ∃ σ : X →* Multiplicative (ZMod 2),
      σ s = Multiplicative.ofAdd 1 ∧ ∀ x, σ x = 1 ↔ N₁.map (MulAut.conj x).toMonoidHom = N₁ := by
  refine ⟨MonoidHom.mk' (sgnFun N₁) (sgnFun_mul hs hne hperm), ?_, fun x => sgnFun_eq_one_iff⟩
  refine sgnFun_of_ne ?_
  rw [← hs]
  exact hne.symm

end Sign

section Acts

variable {X : Type} [Group X] {D : Type} [Group D] {N₁ : Subgroup X}

def Acts (ρ : D →* MulAut ↥N₁) (x : X) (d : D) : Prop :=
  ∀ (n : X) (hn : n ∈ N₁), x * n * x⁻¹ = ((ρ d ⟨n, hn⟩ : ↥N₁) : X)

variable {ρ : D →* MulAut ↥N₁}

theorem Acts.mul {x y : X} {d e : D} (hx : Acts ρ x d) (hy : Acts ρ y e) :
    Acts ρ (x * y) (d * e) := by
  intro n hn
  have h1 : y * n * y⁻¹ = ((ρ e ⟨n, hn⟩ : ↥N₁) : X) := hy n hn
  have h2 := hx _ (ρ e ⟨n, hn⟩).2
  calc x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
    _ = x * ((ρ e ⟨n, hn⟩ : ↥N₁) : X) * x⁻¹ := by rw [h1]
    _ = ((ρ d ⟨_, (ρ e ⟨n, hn⟩).2⟩ : ↥N₁) : X) := h2
    _ = ((ρ (d * e) ⟨n, hn⟩ : ↥N₁) : X) := by rw [map_mul]; rfl

theorem Acts.unique (hρ : Function.Injective ρ) {x : X} {d e : D} (hd : Acts ρ x d)
    (he : Acts ρ x e) : d = e := by
  apply hρ
  ext n
  rw [← hd n.1 n.2, ← he n.1 n.2]

theorem Acts.one_iff {x : X} : Acts ρ x 1 ↔ ∀ n ∈ N₁, x * n * x⁻¹ = n := by
  constructor
  · intro h n hn
    simpa using h n hn
  · intro h n hn
    simpa using h n hn

end Acts

section Cocycle

variable {X : Type} [Group X]

def sp (s : X) (z : Multiplicative (ZMod 2)) : X := if z = 1 then 1 else s

theorem sp_one (s : X) : sp s 1 = 1 := by
  unfold sp
  rw [ite_eq_left rfl]

theorem sp_gen (s : X) : sp s (Multiplicative.ofAdd 1) = s := by
  unfold sp
  rw [ite_eq_right Z2_gen_ne_one]

variable (σ : X →* Multiplicative (ZMod 2)) (s : X)

theorem sigma_sp (hσs : σ s = Multiplicative.ofAdd 1) (z : Multiplicative (ZMod 2)) :
    σ (sp s z) = z := by
  rcases Z2_cases z with rfl | rfl
  · rw [sp_one, map_one]
  · rw [sp_gen, hσs]

def u (x : X) (z : Multiplicative (ZMod 2)) : X := (sp s z)⁻¹ * x * sp s ((σ x)⁻¹ * z)

theorem sigma_u (hσs : σ s = Multiplicative.ofAdd 1) (x : X) (z : Multiplicative (ZMod 2)) :
    σ (u σ s x z) = 1 := by
  rw [u, map_mul, map_mul, map_inv, sigma_sp σ s hσs, sigma_sp σ s hσs]
  group

theorem u_mul (x y : X) (z : Multiplicative (ZMod 2)) :
    u σ s (x * y) z = u σ s x z * u σ s y ((σ x)⁻¹ * z) := by
  have h : (σ (x * y))⁻¹ * z = (σ y)⁻¹ * ((σ x)⁻¹ * z) := by
    rw [map_mul, mul_inv_rev, mul_assoc]
  unfold u
  rw [h]
  group

end Cocycle

section Hom

variable {X : Type} [Group X] {D : Type} [Group D] {N₁ : Subgroup X} (ρ : D →* MulAut ↥N₁)
  (σ : X →* Multiplicative (ZMod 2)) (s : X)

theorem exists_hom_acts (hρ : Function.Injective ρ) (hσs : σ s = Multiplicative.ofAdd 1)
    (hσ : ∀ x, σ x = 1 ↔ N₁.map (MulAut.conj x).toMonoidHom = N₁)
    (hrange : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ → ∃ d : D, Acts ρ x d) :
    ∃ φ : X →* D ≀ᵣ Multiplicative (ZMod 2), (∀ x, (φ x).right = σ x) ∧
      ∀ x z, Acts ρ (u σ s x z) ((φ x).left z) := by
  choose left hleft using fun (x : X) (z : Multiplicative (ZMod 2)) =>
    hrange (u σ s x z) ((hσ _).mp (sigma_u σ s hσs x z))
  refine ⟨MonoidHom.mk' (fun x => (⟨left x, σ x⟩ : D ≀ᵣ Multiplicative (ZMod 2))) ?_,
    fun x => rfl, fun x z => hleft x z⟩
  intro x y
  refine RegularWreathProduct.ext ?_ (map_mul σ x y)
  funext z
  have h := (hleft x z).mul (hleft y ((σ x)⁻¹ * z))
  rw [← u_mul σ s x y z] at h
  exact Acts.unique hρ (hleft (x * y) z) h

end Hom

section Inj

variable {X : Type} [Group X] {D : Type} [Group D] {N₁ N₂ : Subgroup X} {ρ : D →* MulAut ↥N₁}
  {σ : X →* Multiplicative (ZMod 2)} {s : X}

theorem injective_of_acts (hs : N₂ = N₁.map (MulAut.conj s).toMonoidHom)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hcen : ∀ x : X, (∀ n ∈ N₁ ⊔ N₂, x * n = n * x) → x ∈ N₁ ⊔ N₂)
    (hZ : ∀ n ∈ N₁, (∀ m ∈ N₁, n * m = m * n) → n = 1)
    (φ : X →* D ≀ᵣ Multiplicative (ZMod 2)) (hφr : ∀ x, (φ x).right = σ x)
    (hφl : ∀ x z, Acts ρ (u σ s x z) ((φ x).left z)) : Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hr : σ x = 1 := by rw [← hφr x, hx]; rfl
  have hl : ∀ z, (φ x).left z = 1 := fun z => by rw [hx]; rfl
  have h1 : ∀ n ∈ N₁, x * n * x⁻¹ = n := by
    have h := hφl x 1
    rw [hl 1, Acts.one_iff] at h
    simpa [u, sp_one, hr] using h
  have h2 : ∀ n ∈ N₁, s⁻¹ * x * s * n * (s⁻¹ * x * s)⁻¹ = n := by
    have h := hφl x (Multiplicative.ofAdd 1)
    rw [hl, Acts.one_iff] at h
    simpa [u, sp_gen, hr] using h
  have h3 : ∀ m ∈ N₂, x * m = m * x := by
    intro m hm
    have hn : s⁻¹ * m * s ∈ N₁ := by
      rw [hs] at hm
      exact mem_map_conj.mp hm
    have h := h2 _ hn
    have h' : x * m * x⁻¹ = m := calc
      x * m * x⁻¹ = s * (s⁻¹ * x * s * (s⁻¹ * m * s) * (s⁻¹ * x * s)⁻¹) * s⁻¹ := by group
      _ = s * (s⁻¹ * m * s) * s⁻¹ := by rw [h]
      _ = m := by group
    exact mul_inv_eq_iff_eq_mul.mp h'
  have h4 : ∀ n ∈ N₁ ⊔ N₂, x * n = n * x := by
    intro n hn
    have hle : N₁ ⊔ N₂ ≤ Subgroup.centralizer {x} := sup_le
      (fun n hn => Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact mul_inv_eq_iff_eq_mul.mp (h1 n hn))
      (fun m hm => Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact h3 m hm)
    exact Subgroup.mem_centralizer_iff.mp (hle hn) x (Set.mem_singleton x)
  have h5 : x ∈ N₁ ⊔ N₂ := hcen x h4
  have hnorm : N₁ ≤ Subgroup.normalizer (N₂ : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h' : a * y * a⁻¹ = y := mul_inv_eq_iff_eq_mul.mpr (hcomm a ha y hy)
      rw [h']
      exact hy
    · intro hy
      have hc : a⁻¹ * (a * y * a⁻¹) = (a * y * a⁻¹) * a⁻¹ := hcomm a⁻¹ (N₁.inv_mem ha) _ hy
      have h' : y = a * y * a⁻¹ := calc
        y = a⁻¹ * (a * y * a⁻¹) * a := by group
        _ = (a * y * a⁻¹) * a⁻¹ * a := by rw [hc]
        _ = a * y * a⁻¹ := by group
      rw [h']
      exact hy
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ N₁, ∃ b ∈ N₂, a * b = x := by
    have h6 := Subgroup.coe_mul_of_left_le_normalizer_right N₁ N₂ hnorm
    have h7 : x ∈ ((N₁ ⊔ N₂ : Subgroup X) : Set X) := h5
    rw [h6] at h7
    exact Set.mem_mul.mp h7
  have ha1 : a = 1 := by
    refine hZ a ha fun m hm => ?_
    have hbm : m * b = b * m := hcomm m hm b hb
    have h' : (a * m) * b = (m * a) * b := calc
      a * m * b = a * (m * b) := mul_assoc _ _ _
      _ = a * (b * m) := by rw [hbm]
      _ = x * m := by rw [← hab, mul_assoc]
      _ = m * x := mul_inv_eq_iff_eq_mul.mp (h1 m hm)
      _ = m * (a * b) := by rw [hab]
      _ = m * a * b := (mul_assoc _ _ _).symm
    exact mul_right_cancel h'
  have hxb : x = b := by rw [← hab, ha1, one_mul]
  have hb' : s⁻¹ * x * s ∈ N₁ := by
    rw [hxb]
    rw [hs] at hb
    exact mem_map_conj.mp hb
  have hy1 : s⁻¹ * x * s = 1 :=
    hZ _ hb' fun m hm => mul_inv_eq_iff_eq_mul.mp (h2 m hm)
  calc x = s * (s⁻¹ * x * s) * s⁻¹ := by group
    _ = 1 := by rw [hy1]; group

end Inj

end QWr

set_option linter.unusedVariables false in
theorem q_exists_injective_hom_wreath
    {X : Type} [Group X] {D : Type} [Group D]
    (N₁ N₂ : Subgroup X) (s : X)
    (hs : N₂ = N₁.map (MulAut.conj s).toMonoidHom)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hdisj : N₁ ⊓ N₂ = ⊥)
    (hperm : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ ∨
      N₁.map (MulAut.conj x).toMonoidHom = N₂)
    (hnormal : (N₁ ⊔ N₂).Normal)
    (hcen : ∀ x : X, (∀ n ∈ N₁ ⊔ N₂, x * n = n * x) → x ∈ N₁ ⊔ N₂)
    (hZ : ∀ n ∈ N₁, (∀ m ∈ N₁, n * m = m * n) → n = 1)
    (ρ : D →* MulAut ↥N₁) (hρ : Function.Injective ρ)
    (hrange : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ →
      ∃ d : D, ∀ (n : X) (hn : n ∈ N₁), x * n * x⁻¹ = ((ρ d ⟨n, hn⟩ : ↥N₁) : X)) :
    ∃ φ : X →* D ≀ᵣ Multiplicative (ZMod 2), Function.Injective φ := by
  by_cases hne : N₁ = N₂
  · have h1 : N₁ = ⊥ := by
      have h := hdisj
      rwa [← hne, inf_idem] at h
    have hsup : N₁ ⊔ N₂ = ⊥ := by rw [← hne, sup_idem, h1]
    have hX : ∀ x : X, x = 1 := fun x => by
      have hx : x ∈ N₁ ⊔ N₂ := hcen x fun n hn => by
        rw [hsup, Subgroup.mem_bot] at hn
        rw [hn, mul_one, one_mul]
      rwa [hsup, Subgroup.mem_bot] at hx
    have : Subsingleton X := ⟨fun a b => (hX a).trans (hX b).symm⟩
    exact ⟨1, Function.injective_of_subsingleton _⟩
  · obtain ⟨σ, hσs, hσ⟩ := QWr.exists_sigma hs hne hperm
    obtain ⟨φ, hφr, hφl⟩ := QWr.exists_hom_acts ρ σ s hρ hσs hσ hrange
    exact ⟨φ, QWr.injective_of_acts hs hcomm hcen hZ φ hφr hφl⟩

theorem q_mulEquiv_wreath
    {X : Type} [Group X] [Finite X] {D : Type} [Group D] [Finite D]
    (N₁ N₂ : Subgroup X) (s : X)
    (hs : N₂ = N₁.map (MulAut.conj s).toMonoidHom)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hdisj : N₁ ⊓ N₂ = ⊥)
    (hperm : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ ∨
      N₁.map (MulAut.conj x).toMonoidHom = N₂)
    (hnormal : (N₁ ⊔ N₂).Normal)
    (hcen : ∀ x : X, (∀ n ∈ N₁ ⊔ N₂, x * n = n * x) → x ∈ N₁ ⊔ N₂)
    (hZ : ∀ n ∈ N₁, (∀ m ∈ N₁, n * m = m * n) → n = 1)
    (ρ : D →* MulAut ↥N₁) (hρ : Function.Injective ρ)
    (hrange : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ →
      ∃ d : D, ∀ (n : X) (hn : n ∈ N₁), x * n * x⁻¹ = ((ρ d ⟨n, hn⟩ : ↥N₁) : X))
    (hcard : 2 * Nat.card D ^ 2 ≤ Nat.card X) :
    Nonempty (X ≃* D ≀ᵣ Multiplicative (ZMod 2)) := by
  obtain ⟨φ, hφ⟩ := q_exists_injective_hom_wreath N₁ N₂ s hs hcomm hdisj hperm hnormal hcen hZ ρ
    hρ hrange
  have hc : Nat.card (D ≀ᵣ Multiplicative (ZMod 2)) = 2 * Nat.card D ^ 2 := by
    rw [RegularWreathProduct.card, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    ring
  exact ⟨MulEquiv.ofBijective φ (hφ.bijective_of_nat_card_le (by rw [hc]; exact hcard))⟩

theorem q_mulEquiv_wreath_mulAut
    {X : Type} [Group X] [Finite X] {L : Type} [Group L] [Finite L]
    (N₁ N₂ : Subgroup X) (s : X) (e : L ≃* ↥N₁)
    (hs : N₂ = N₁.map (MulAut.conj s).toMonoidHom)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hdisj : N₁ ⊓ N₂ = ⊥)
    (hperm : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ ∨
      N₁.map (MulAut.conj x).toMonoidHom = N₂)
    (hnormal : (N₁ ⊔ N₂).Normal)
    (hcen : ∀ x : X, (∀ n ∈ N₁ ⊔ N₂, x * n = n * x) → x ∈ N₁ ⊔ N₂)
    (hZ : ∀ n ∈ N₁, (∀ m ∈ N₁, n * m = m * n) → n = 1)
    (hcard : 2 * Nat.card (MulAut L) ^ 2 ≤ Nat.card X) :
    Nonempty (X ≃* MulAut L ≀ᵣ Multiplicative (ZMod 2)) := by
  refine q_mulEquiv_wreath N₁ N₂ s hs hcomm hdisj hperm hnormal hcen hZ
    (MulAut.congr e).toMonoidHom (fun a b h => (MulAut.congr e).injective h) ?_ hcard
  intro x hx
  have hx' : x ∈ Subgroup.normalizer (N₁ : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hx
  refine ⟨(MulAut.congr e).symm (N₁.normalizerMonoidHom ⟨x, hx'⟩), fun n hn => ?_⟩
  have h1 : (MulAut.congr e).toMonoidHom ((MulAut.congr e).symm
      (N₁.normalizerMonoidHom ⟨x, hx'⟩)) = N₁.normalizerMonoidHom ⟨x, hx'⟩ :=
    (MulAut.congr e).apply_symm_apply _
  rw [h1]
  exact (Subgroup.normalizerMonoidHom_apply_apply_coe N₁ ⟨x, hx'⟩ ⟨n, hn⟩).symm

theorem q_mulEquiv_wreath_inner
    {X : Type} [Group X] [Finite X] {L : Type} [Group L] [Finite L]
    (N₁ N₂ : Subgroup X) (s : X) (e : L ≃* ↥N₁)
    (hs : N₂ = N₁.map (MulAut.conj s).toMonoidHom)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hdisj : N₁ ⊓ N₂ = ⊥)
    (hperm : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ ∨
      N₁.map (MulAut.conj x).toMonoidHom = N₂)
    (hnormal : (N₁ ⊔ N₂).Normal)
    (hcen : ∀ x : X, (∀ n ∈ N₁ ⊔ N₂, x * n = n * x) → x ∈ N₁ ⊔ N₂)
    (hZ : ∀ n ∈ N₁, (∀ m ∈ N₁, n * m = m * n) → n = 1)
    (hinner : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ →
      ∃ d : L, ∀ n ∈ N₁, x * n * x⁻¹ = (e d : X) * n * (e d : X)⁻¹)
    (hcard : 2 * Nat.card L ^ 2 ≤ Nat.card X) :
    Nonempty (X ≃* L ≀ᵣ Multiplicative (ZMod 2)) := by
  have hρ : Function.Injective ((MulAut.conj : ↥N₁ →* MulAut ↥N₁).comp e.toMonoidHom) := by
    intro a b hab
    apply e.injective
    have hc : ∀ m : ↥N₁, (e a : X) * m * (e a : X)⁻¹ = (e b : X) * m * (e b : X)⁻¹ := fun m => by
      have := congrArg (fun f : MulAut ↥N₁ => ((f m : ↥N₁) : X)) hab
      simpa using this
    have h1 : (e a : X)⁻¹ * (e b : X) = 1 := by
      refine hZ _ (N₁.mul_mem (N₁.inv_mem (e a).2) (e b).2) fun m hm => ?_
      have h := hc ⟨m, hm⟩
      calc (e a : X)⁻¹ * (e b : X) * m
          = (e a : X)⁻¹ * ((e b : X) * m * (e b : X)⁻¹) * (e b : X) := by group
        _ = (e a : X)⁻¹ * ((e a : X) * m * (e a : X)⁻¹) * (e b : X) := by rw [← h]
        _ = m * ((e a : X)⁻¹ * (e b : X)) := by group
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  refine q_mulEquiv_wreath N₁ N₂ s hs hcomm hdisj hperm hnormal hcen hZ
    ((MulAut.conj : ↥N₁ →* MulAut ↥N₁).comp e.toMonoidHom) hρ ?_ hcard
  intro x hx
  obtain ⟨d, hd⟩ := hinner x hx
  refine ⟨d, fun n hn => ?_⟩
  rw [hd n hn]
  simp

end CFSG.Quasithin
