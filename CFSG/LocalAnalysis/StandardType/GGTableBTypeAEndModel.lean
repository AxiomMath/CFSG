module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly

section Induced

variable {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R)

theorem mulAut_eq_of_forall (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {a b : MulAut L'} (h : ∀ l, ψ (a l) = ψ (b l)) : a = b := by
  have h1 := eq_of_inv_mul_mem_center hperf (a : L' →* L') (b : L' →* L') (fun l => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (ψ (a l))⁻¹ * ψ (b l) = 1
    rw [h l, inv_mul_cancel]))
  ext l
  exact congrArg (fun f : L' →* L' => f l) h1

theorem induced_unique (hψ : Function.Surjective ψ) {a : MulAut L'} {φ₁ φ₂ : MulAut R}
    (h₁ : ∀ l, φ₁ (ψ l) = ψ (a l)) (h₂ : ∀ l, φ₂ (ψ l) = ψ (a l)) : φ₁ = φ₂ := by
  ext r
  obtain ⟨l, rfl⟩ := hψ r
  rw [h₁, h₂]

theorem induced_pow {a : MulAut L'} {φ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l)) (n : ℕ) :
    ∀ l, (φ ^ n) (ψ l) = ψ ((a ^ n) l) := by
  induction n with
  | zero => intro l; rfl
  | succ n ih =>
    intro l
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, h, ih]

@[expose] def inducedSub (A : Subgroup (MulAut L')) : Subgroup (MulAut R) where
  carrier := {φ | ∃ a ∈ A, ∀ l, φ (ψ l) = ψ (a l)}
  mul_mem' := by
    rintro φ₁ φ₂ ⟨a, ha, h1⟩ ⟨b, hb, h2⟩
    exact ⟨a * b, A.mul_mem ha hb, fun l => by
      rw [MulAut.mul_apply, MulAut.mul_apply, h2, h1]⟩
  one_mem' := ⟨1, A.one_mem, fun _ => rfl⟩
  inv_mem' := by
    rintro φ ⟨a, ha, h⟩
    refine ⟨a⁻¹, A.inv_mem ha, fun l => ?_⟩
    apply φ.injective
    rw [MulAut.apply_inv_self, h, MulAut.apply_inv_self]

variable {ψ}

theorem mem_inducedSub {A : Subgroup (MulAut L')} {φ : MulAut R} :
    φ ∈ inducedSub ψ A ↔ ∃ a ∈ A, ∀ l, φ (ψ l) = ψ (a l) :=
  Iff.rfl

theorem conj_induced_apply {G H : Type*} [Group G] [Group H] (f : G →* H)
    {a : MulAut G} {φ : MulAut H} (hφ : ∀ l, φ (f l) = f (a l)) (n l : G) :
    (MulAut.conj (f n) * φ * (MulAut.conj (f n))⁻¹) (f l) =
      f ((MulAut.conj n * a * (MulAut.conj n)⁻¹) l) := by
  have h1 : (MulAut.conj (f n))⁻¹ = MulAut.conj (f n)⁻¹ := (map_inv _ _).symm
  have h2 : (MulAut.conj n)⁻¹ = MulAut.conj n⁻¹ := (map_inv _ _).symm
  have harg : (MulAut.conj (f n))⁻¹ (f l) = f (n⁻¹ * l * n) := by
    rw [h1, MulAut.conj_apply]
    simp only [map_mul, map_inv, inv_inv]
  have hL : (MulAut.conj (f n) * φ * (MulAut.conj (f n))⁻¹) (f l) =
      f n * φ (f (n⁻¹ * l * n)) * (f n)⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, harg, MulAut.conj_apply]
  have h3 : (MulAut.conj n)⁻¹ l = n⁻¹ * l * n := by
    rw [h2, MulAut.conj_apply, inv_inv]
  have hR : f ((MulAut.conj n * a * (MulAut.conj n)⁻¹) l) =
      f n * φ (f (n⁻¹ * l * n)) * (f n)⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, h3, MulAut.conj_apply, map_mul, map_mul, map_inv,
      ← hφ]
  rw [hL, hR]

noncomputable def inducedSubEquiv (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')}
    (hA : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l)) :
    ↥A ≃* ↥(inducedSub ψ A) := by
  classical
  choose φa hφa using hA
  let f : ↥A → ↥(inducedSub ψ A) := fun a => ⟨φa a a.2, a, a.2, hφa a a.2⟩
  have hf : ∀ (a : ↥A) (l : L'), (f a).1 (ψ l) = ψ (a.1 l) :=
    fun a => hφa a a.2
  refine MulEquiv.ofBijective
    ({ toFun := f
       map_one' := ?_
       map_mul' := ?_ } : ↥A →* ↥(inducedSub ψ A)) ⟨?_, ?_⟩
  · apply Subtype.ext
    exact induced_unique ψ hψ (a := (1 : MulAut L')) (hf 1) (fun _ => rfl)
  · intro a b
    apply Subtype.ext
    refine induced_unique ψ hψ (a := (a * b).1) (hf (a * b)) ?_
    intro l
    rw [Subgroup.coe_mul, MulAut.mul_apply, hf, hf, Subgroup.coe_mul, MulAut.mul_apply]
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h1 : φa a ha = φa b hb := congrArg Subtype.val hab
    apply Subtype.ext
    apply mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← hφa a ha, ← hφa b hb, h1]
  · rintro ⟨φ, a, ha, h⟩
    exact ⟨⟨a, ha⟩, Subtype.ext (induced_unique ψ hψ (hφa a ha) h)⟩

theorem inducedSubEquiv_apply (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')}
    (hA : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l)) (a : ↥A) (l : L') :
    (inducedSubEquiv hψ hker hperf hA a).1 (ψ l) = ψ (a.1 l) := by
  exact Classical.choose_spec (hA a a.2) l

theorem card_inducedSub (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (hA : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l)) :
    Nat.card (inducedSub ψ A) = Nat.card A :=
  (Nat.card_congr (inducedSubEquiv hψ hker hperf hA).toEquiv).symm

theorem isElemAbelian_inducedSub (hψ : Function.Surjective ψ) {p : ℕ} {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) : IsElemAbelian p (inducedSub ψ A) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨φ₁, a, ha, h1⟩ ⟨φ₂, b, hb, h2⟩
    apply Subtype.ext
    change φ₁ * φ₂ = φ₂ * φ₁
    have hab : a * b = b * a := TableB.IsElemAbelian.comm hA ha hb
    apply induced_unique ψ hψ (a := a * b)
    · intro l
      rw [MulAut.mul_apply, MulAut.mul_apply, h2, h1]
    · intro l
      rw [hab, MulAut.mul_apply, MulAut.mul_apply, h1, h2]
  · rintro φ ⟨a, ha, h⟩
    have h1 := induced_pow ψ h p
    rw [hA.2 a ha] at h1
    exact induced_unique ψ hψ h1 (fun _ => rfl)

end Induced

section Model

variable {d p : ℕ} {K : Type} [Field K]

theorem act_of_lift (hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤) {L' : Type}
    [Group L'] {ψ : L' →* projectiveSL d K} (hker : ψ.ker ≤ Subgroup.center L')
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hφ : ∀ g, ψ (φ g) = proj d K g) {a : MulAut L'}
    {g : SpecialLinearGroup (Fin d) K}
    (hind : ∀ l, conjAut d K (SpecialLinearGroup.toGL g) (ψ l) = ψ (a l)) :
    ∀ s, a (φ s) = φ (g * s * g⁻¹) := by
  have h1 := eq_of_inv_mul_mem_center hperfSL ((a : L' →* L').comp φ)
    (φ.comp (MulAut.conj g).toMonoidHom) (fun s => hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change (ψ (a (φ s)))⁻¹ * ψ (φ (g * s * g⁻¹)) = 1
      rw [← hind, hφ, hφ, conjAut_toGL, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul,
        inv_mul_cancel]))
  intro s
  exact congrArg (fun f : SpecialLinearGroup (Fin d) K →* L' => f s) h1

theorem slConjugation_inv_apply (A₀ : GL (Fin d) K) (s : SpecialLinearGroup (Fin d) K) :
    CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹
        (CatalogueBHigherLinearAction.slConjugation d K A₀ s) = s := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem mem_scalars_of_slConjugation_mem (A₀ : GL (Fin d) K) {s : SpecialLinearGroup (Fin d) K}
    (hs : CatalogueBHigherLinearAction.slConjugation d K A₀ s ∈ scalars d K) : s ∈ scalars d K := by
  have h1 := (scalars_le_center d K) hs
  have h2 : s = CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹
      (CatalogueBHigherLinearAction.slConjugation d K A₀ s) := (slConjugation_inv_apply A₀ s).symm
  rw [scalars_eq_center]
  rw [h2]
  exact (Subgroup.map_center_eq (CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹)) ▸
    ⟨_, h1, rfl⟩

theorem exists_diagonal_model [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hpd : Nat.Coprime p d) (hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤)
    {L' : Type} [Group L'] {ψ : L' →* projectiveSL d K} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ)
    (hφ : ∀ g, ψ (φ g) = proj d K g) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φa ∈ Set.range (conjAut d K), ∀ l, φa (ψ l) = ψ (a l)) :
    ∃ φ' : SpecialLinearGroup (Fin d) K →* L', Function.Surjective φ' ∧
      (∀ g, φ' g = 1 → g ∈ scalars d K) ∧
      (∀ a ∈ A, ∃ D : SpecialLinearGroup (Fin d) K,
        (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) ∧ D ^ p = 1 ∧
        ∀ s, a (φ' s) = φ' (D * s * D⁻¹)) ∧
      Nat.card A ≤ p ^ (d - 1) ∧
      (Nat.card A = p ^ (d - 1) → ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
        ∃ a ∈ A, ∃ D : SpecialLinearGroup (Fin d) K,
          (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧ ∀ s, a (φ' s) = φ' (D * s * D⁻¹)) := by
  set X := inducedSub ψ A with hX
  have hXA : IsElemAbelian p X := isElemAbelian_inducedSub hψ hA
  have hXI : ∀ x ∈ X, ∃ B : GL (Fin d) K, conjAut d K B = x := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    exact ⟨B, induced_unique ψ hψ hφa hxa⟩
  have hcardX : Nat.card X = Nat.card A := card_inducedSub hψ hker hperf (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    TableB.IsElemAbelian.comm hXA hx hy
  obtain ⟨A₀, hdiag, hle, hfull⟩ := exists_diagonalizing_slLift hp hpK hd hpd X hXc hXA.2 hXI
  set c₀ := CatalogueBHigherLinearAction.slConjugation d K A₀ with hc₀
  set c₀' := CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ with hc₀'
  set φ' := φ.comp c₀'.toMonoidHom with hφ'
  have hlift : ∀ x ∈ X, ∃ g ∈ slLift hd hpd X hXc,
      conjAut d K (SpecialLinearGroup.toGL g) = x := by
    intro x hx
    obtain ⟨B, rfl⟩ := hXI x hx
    obtain ⟨g, hgp, hg⟩ := exists_slLift hd hpd (hXA.2 _ hx)
    exact ⟨g, ⟨hgp, hg ▸ hx⟩, hg⟩
  have hact : ∀ a : MulAut L', ∀ g : SpecialLinearGroup (Fin d) K,
      (∀ l, conjAut d K (SpecialLinearGroup.toGL g) (ψ l) = ψ (a l)) →
      ∀ s, a (φ' s) = φ' (c₀ g * s * (c₀ g)⁻¹) := by
    intro a g hind s
    have h1 := act_of_lift hperfSL hker hφ hind (c₀' s)
    have h2 : c₀' (c₀ g * s * (c₀ g)⁻¹) = g * c₀' s * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, hc₀, hc₀', slConjugation_inv_apply]
    change a (φ (c₀' s)) = φ (c₀' (c₀ g * s * (c₀ g)⁻¹))
    rw [h1, h2]
  have hc₀mat : ∀ g, ((c₀ g : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      conjMat A₀ g := fun g => coe_slConjugation' A₀ g
  refine ⟨φ', hφs.comp c₀'.surjective, ?_, ?_, hcardX ▸ hle, ?_⟩
  · intro g hg
    have h1 : proj d K (c₀' g) = 1 := by
      rw [← hφ]
      change ψ (φ' g) = 1
      rw [hg, map_one]
    exact mem_scalars_of_slConjugation_mem A₀⁻¹ (proj_eq_one_iff.mp h1)
  · intro a ha
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    obtain ⟨g, hg, hgφ⟩ := hlift φa ⟨a, ha, hφa⟩
    refine ⟨c₀ g, ⟨_, (hc₀mat g).trans (conjMat_diag hg.1 (hdiag g hg)).1⟩, ?_,
      hact a g (fun l => by rw [hgφ, hφa])⟩
    rw [← map_pow, hg.1, map_one]
  · intro hcard t ht htp
    obtain ⟨g, hg, hgt⟩ := hfull (hcardX.trans hcard) t ht htp
    obtain ⟨a, ha, hind⟩ := hg.2
    exact ⟨a, ha, c₀ g, (hc₀mat g).trans hgt, hact a g hind⟩

end Model

end CFSG.StandardType.TypeA
