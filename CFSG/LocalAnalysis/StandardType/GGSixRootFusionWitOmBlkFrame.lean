module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFrame

public section

namespace CFSG.StandardType

namespace WitOmBlk

open QuadraticMap Module OrdPNsOm

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

omit [CharP K 2] in
theorem isHypFamily_comp {m m' : ℕ} {e f : Fin m' → V} (h : TableBOrth.IsHypFamily Q e f)
    {ι : Fin m → Fin m'} (hι : Function.Injective ι) :
    TableBOrth.IsHypFamily Q (e ∘ ι) (f ∘ ι) :=
  ⟨fun _ => h.map_e _, fun _ => h.map_f _, fun _ _ => h.polar_ee _ _,
    fun _ _ => h.polar_ff _ _, fun i j => by simp only [Function.comp, h.polar_ef, hι.eq_iff]⟩

omit [CharP K 2] in
theorem quad_add (x y : V) : Q (x + y) = Q x + Q y + polar Q x y := by
  rw [polar]
  ring

omit [CharP K 2] in
theorem quad_smul (c : K) (x : V) : Q (c • x) = c * c * Q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul]

theorem exists_frame_of_type {c₀ : K} {τ : Bool} {m m' : ℕ} (hm : m + 1 ≤ m')
    {e f : Fin m' → V} {a b : V} (hF : IsFrame Q c₀ τ e f a b) (τ₀ : Bool)
    {X : Submodule K V} (hX : ∀ x, fvec e f a b x ∈ X) :
    ∃ (e' f' : Fin m → V) (a' b' : V), IsFrame Q c₀ τ₀ e' f' a' b' ∧
      ∀ x, fvec e' f' a' b' x ∈ X := by
  set ι : Fin m → Fin m' := Fin.castLE (by omega) with hι
  have hιinj : Function.Injective ι := Fin.castLE_injective _
  set j₀ : Fin m' := ⟨m, by omega⟩ with hj₀
  have hne : ∀ i, ι i ≠ j₀ := fun i h => by
    have h1 := congrArg Fin.val h
    simp only [hι, hj₀, Fin.val_castLE] at h1
    omega
  have he : ∀ i, e i ∈ X := fun i => hX (.inl i)
  have hf : ∀ i, f i ∈ X := fun i => hX (.inr (.inl i))
  have ha : a ∈ X := hX (.inr (.inr 0))
  have hb : b ∈ X := hX (.inr (.inr 1))
  have hyp := isHypFamily_comp hF.hyp hιinj
  have key : ∀ a' b' : V, a' ∈ X → b' ∈ X → (∀ i, polar Q (e (ι i)) a' = 0) →
      (∀ i, polar Q (e (ι i)) b' = 0) → (∀ i, polar Q (f (ι i)) a' = 0) →
      (∀ i, polar Q (f (ι i)) b' = 0) → polar Q a' b' = 1 →
      Q a' = (if τ₀ then 1 else 0) → Q b' = (if τ₀ then c₀ else 0) →
      ∃ (e' f' : Fin m → V) (a'' b'' : V), IsFrame Q c₀ τ₀ e' f' a'' b'' ∧
        ∀ x, fvec e' f' a'' b'' x ∈ X := by
    intro a' b' ha' hb' h1 h2 h3 h4 h5 h6 h7
    refine ⟨e ∘ ι, f ∘ ι, a', b', ⟨hyp, h1, h2, h3, h4, h5, h6, h7⟩, ?_⟩
    rintro (i | i | j)
    · exact he _
    · exact hf _
    · fin_cases j
      · exact ha'
      · exact hb'
  have hee : ∀ i, polar Q (e (ι i)) (e j₀) = 0 := fun i => hF.hyp.polar_ee _ _
  have hef : ∀ i, polar Q (e (ι i)) (f j₀) = 0 := fun i => by
    rw [hF.hyp.polar_ef, ite_eq_right (hne i)]
  have hfe : ∀ i, polar Q (f (ι i)) (e j₀) = 0 := fun i => by
    rw [polar_comm, hF.hyp.polar_ef, ite_eq_right (hne i).symm]
  have hff : ∀ i, polar Q (f (ι i)) (f j₀) = 0 := fun i => hF.hyp.polar_ff _ _
  have hej : polar Q (e j₀) (f j₀) = 1 := by rw [hF.hyp.polar_ef, ite_eq_left rfl]
  cases τ <;> cases τ₀
  · exact key a b ha hb (fun _ => hF.pea _) (fun _ => hF.peb _) (fun _ => hF.pfa _)
      (fun _ => hF.pfb _) hF.pab hF.qa hF.qb
  ·
    have hqa : Q a = 0 := by simpa using hF.qa
    have hqb : Q b = 0 := by simpa using hF.qb
    refine key (e j₀ + f j₀) (f j₀ + (a + c₀ • b)) (X.add_mem (he _) (hf _))
      (X.add_mem (hf _) (X.add_mem ha (X.smul_mem _ hb))) (fun i => ?_) (fun i => ?_)
      (fun i => ?_) (fun i => ?_) ?_ ?_ ?_
    · rw [polar_add_right, hee, hef, add_zero]
    · rw [polar_add_right, polar_add_right, polar_smul_right, hef, hF.pea, hF.peb, smul_zero,
        add_zero, add_zero]
    · rw [polar_add_right, hfe, hff, add_zero]
    · rw [polar_add_right, polar_add_right, polar_smul_right, hff, hF.pfa, hF.pfb, smul_zero,
        add_zero, add_zero]
    · rw [polar_add_left, polar_add_right, polar_add_right, polar_add_right, polar_add_right,
        polar_smul_right, polar_smul_right, hej, hF.pea, hF.peb, polar_self_charTwo, hF.pfa,
        hF.pfb]
      simp
    · rw [quad_add, hF.hyp.map_e, hF.hyp.map_f, hej]
      simp
    · rw [quad_add, quad_add, quad_smul, hF.hyp.map_f, hqa, hqb, polar_smul_right, hF.pab,
        polar_add_right, polar_smul_right, hF.pfa, hF.pfb]
      simp
  ·
    exact key (e j₀) (f j₀) (he _) (hf _) hee hef hfe hff hej (by simpa using hF.hyp.map_e j₀)
      (by simpa using hF.hyp.map_f j₀)
  · exact key a b ha hb (fun _ => hF.pea _) (fun _ => hF.peb _) (fun _ => hF.pfa _)
      (fun _ => hF.pfb _) hF.pab hF.qa hF.qb

theorem exists_frame_of_type_add [Finite K] {c₀ : K} {τ : Bool} {m : ℕ} {e f : Fin m → V}
    {a b : V} (hF : IsFrame Q c₀ τ e f a b) {r : V} (hr : Q r ≠ 0)
    (hre : ∀ i, polar Q r (e i) = 0) (hrf : ∀ i, polar Q r (f i) = 0) (hra : polar Q r a = 0)
    (hrb : polar Q r b = 0) (τ₀ : Bool) {X : Submodule K V} (haX : a ∈ X) (hbX : b ∈ X)
    (hrX : r ∈ X) : ∃ a' b' : V, IsFrame Q c₀ τ₀ e f a' b' ∧ a' ∈ X ∧ b' ∈ X := by
  obtain ⟨t, ht⟩ := isSquare_of_charTwo' (Q r)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hr (by rw [ht, mul_zero])
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' c₀
  set r₁ := t⁻¹ • r with hr₁
  have hr₁X : r₁ ∈ X := X.smul_mem _ hrX
  have hQr₁ : Q r₁ = 1 := by
    rw [hr₁, quad_smul, ht]
    field_simp
  have hpol : ∀ x, polar Q r x = 0 → polar Q x r₁ = 0 := fun x hx => by
    rw [polar_comm, hr₁, polar_smul_left, hx, smul_zero]
  have her : ∀ i, polar Q (e i) r₁ = 0 := fun i => hpol _ (hre i)
  have hfr : ∀ i, polar Q (f i) r₁ = 0 := fun i => hpol _ (hrf i)
  have har : polar Q a r₁ = 0 := hpol _ hra
  have hbr : polar Q b r₁ = 0 := hpol _ hrb
  have hra' : polar Q r₁ a = 0 := by rw [polar_comm]; exact har
  have hrb' : polar Q r₁ b = 0 := by rw [polar_comm]; exact hbr
  clear_value r₁
  have key : ∀ a' b' : V, a' ∈ X → b' ∈ X → (∀ i, polar Q (e i) a' = 0) →
      (∀ i, polar Q (e i) b' = 0) → (∀ i, polar Q (f i) a' = 0) →
      (∀ i, polar Q (f i) b' = 0) → polar Q a' b' = 1 →
      Q a' = (if τ₀ then 1 else 0) → Q b' = (if τ₀ then c₀ else 0) →
      ∃ a'' b'' : V, IsFrame Q c₀ τ₀ e f a'' b'' ∧ a'' ∈ X ∧ b'' ∈ X :=
    fun a' b' ha' hb' h1 h2 h3 h4 h5 h6 h7 =>
      ⟨a', b', ⟨hF.hyp, h1, h2, h3, h4, h5, h6, h7⟩, ha', hb'⟩
  cases τ <;> cases τ₀
  · exact key a b haX hbX hF.pea hF.peb hF.pfa hF.pfb hF.pab hF.qa hF.qb
  ·
    have hqa : Q a = 0 := by simpa using hF.qa
    have hqb : Q b = 0 := by simpa using hF.qb
    refine key (a + r₁) (b + s • r₁) (X.add_mem haX hr₁X) (X.add_mem hbX (X.smul_mem _ hr₁X))
      (fun i => ?_) (fun i => ?_) (fun i => ?_) (fun i => ?_) ?_ ?_ ?_
    · rw [polar_add_right, hF.pea, her, add_zero]
    · rw [polar_add_right, polar_smul_right, hF.peb, her, smul_zero, add_zero]
    · rw [polar_add_right, hF.pfa, hfr, add_zero]
    · rw [polar_add_right, polar_smul_right, hF.pfb, hfr, smul_zero, add_zero]
    · rw [polar_add_left, polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
        hF.pab, har, hrb', polar_self_charTwo]
      simp
    · rw [quad_add, hqa, hQr₁, har]
      simp
    · rw [quad_add, quad_smul, hqb, hQr₁, polar_smul_right, hbr, hs]
      simp
  ·
    have hqa : Q a = 1 := by simpa using hF.qa
    have hqb : Q b = c₀ := by simpa using hF.qb
    have hb₁ : Q (b + s • r₁) = 0 := by
      rw [quad_add, quad_smul, hqb, hQr₁, polar_smul_right, hbr, hs, smul_zero, add_zero,
        mul_one, CharTwo.add_self_eq_zero]
    have hab₁ : polar Q a (b + s • r₁) = 1 := by
      rw [polar_add_right, polar_smul_right, hF.pab, har, smul_zero, add_zero]
    refine key (b + s • r₁) (a + (b + s • r₁)) (X.add_mem hbX (X.smul_mem _ hr₁X))
      (X.add_mem haX (X.add_mem hbX (X.smul_mem _ hr₁X))) (fun i => ?_) (fun i => ?_)
      (fun i => ?_) (fun i => ?_) ?_ ?_ ?_
    · rw [polar_add_right, polar_smul_right, hF.peb, her, smul_zero, add_zero]
    · rw [polar_add_right, polar_add_right, polar_smul_right, hF.pea, hF.peb, her, smul_zero,
        add_zero, add_zero]
    · rw [polar_add_right, polar_smul_right, hF.pfb, hfr, smul_zero, add_zero]
    · rw [polar_add_right, polar_add_right, polar_smul_right, hF.pfa, hF.pfb, hfr, smul_zero,
        add_zero, add_zero]
    · rw [polar_add_right, polar_self_charTwo, add_zero, polar_comm, hab₁]
    · simpa using hb₁
    · rw [quad_add, hqa, hb₁, hab₁]
      simp only [Bool.false_eq_true, ite_false, add_zero]
      exact CharTwo.add_self_eq_zero 1
  · exact key a b haX hbX hF.pea hF.peb hF.pfa hF.pfb hF.pab hF.qa hF.qb

end WitOmBlk

end CFSG.StandardType
