module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section OmegaOne

variable {X : Type} [Group X] [Finite X] {A : Subgroup X}

private theorem endgC_conj_one (T : Subgroup X) : conjSubgroup (1 : X) T = T := by
  ext x
  simp [mem_conjSubgroup]

private theorem endgC_conj_mul (g h : X) (T : Subgroup X) :
    conjSubgroup (g * h) T = conjSubgroup g (conjSubgroup h T) := by
  ext x
  simp only [mem_conjSubgroup]
  rw [show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group]

private theorem endgC_card (g : X) (T : Subgroup X) :
    Nat.card (conjSubgroup g T) = Nat.card T :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem endgC_sq_conj (hO : EndOmegaHyp A) {g y : X} (hy : y ∈ conjSubgroup g A) :
    y * y = 1 := by
  have h1 : g⁻¹ * y * g ∈ A := mem_conjSubgroup.1 hy
  have h2 : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := hO.sq _ h1
  calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

private theorem endgC_cond (A : Subgroup X) (g h : X) :
    (∀ z ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup (g * h) A, z * y = y * z) ↔
      (∀ z ∈ A, ∀ y ∈ conjSubgroup h A, z * y = y * z) := by
  constructor
  · intro H z hz y hy
    have hz' : g * z * g⁻¹ ∈ conjSubgroup g A := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
      exact hz
    have hy' : g * y * g⁻¹ ∈ conjSubgroup (g * h) A := by
      rw [mem_conjSubgroup, show (g * h)⁻¹ * (g * y * g⁻¹) * (g * h) = h⁻¹ * y * h by group]
      exact mem_conjSubgroup.1 hy
    have key := H (g * z * g⁻¹) hz' (g * y * g⁻¹) hy'
    calc z * y = g⁻¹ * (g * z * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * z * g⁻¹)) * g := by rw [key]
      _ = y * z := by group
  · intro H z hz y hy
    have hz' : g⁻¹ * z * g ∈ A := mem_conjSubgroup.1 hz
    have hy' : g⁻¹ * y * g ∈ conjSubgroup h A := by
      rw [mem_conjSubgroup, show h⁻¹ * (g⁻¹ * y * g) * h = (g * h)⁻¹ * y * (g * h) by group]
      exact mem_conjSubgroup.1 hy
    have key := H (g⁻¹ * z * g) hz' (g⁻¹ * y * g) hy'
    calc z * y = g * ((g⁻¹ * z * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [key]
      _ = y * z := by group

theorem endg_A_le_EgenX (hO : EndOmegaHyp A) : A ≤ EgenX A := by
  have h1 : ∀ z ∈ A, ∀ y ∈ conjSubgroup (1 : X) A, z * y = y * z := by
    intro z hz y hy
    rw [endgC_conj_one] at hy
    exact hO.comm z hz y hy
  exact le_iSup₂_of_le (1 : X) h1 (le_of_eq (endgC_conj_one A).symm)

theorem endg_EgenX_comm_A (A : Subgroup X) : ∀ x ∈ EgenX A, ∀ a ∈ A, x * a = a * x := by
  have hle : EgenX A ≤ Subgroup.centralizer (A : Set X) := by
    unfold EgenX
    refine iSup₂_le fun g hg => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hg z hz x hx
  intro x hx a ha
  exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) a ha).symm

private theorem endgC_comm_key (A : Subgroup X) {x a b : X} (ha : a ∈ EgenX A)
    (hc : ⁅b, x⁆ ∈ A) : ⁅a * b, x⁆ = ⁅b, x⁆ * ⁅a, x⁆ := by
  have hac : a * ⁅b, x⁆ = ⁅b, x⁆ * a := endg_EgenX_comm_A A a ha _ hc
  calc ⁅a * b, x⁆ = (a * ⁅b, x⁆) * x * a⁻¹ * x⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅b, x⁆ * ⁅a, x⁆ := by
        rw [hac]
        simp only [commutatorElement_def]
        group

theorem endg_EgenX_sq_mem (hO : EndOmegaHyp A) : ∀ x ∈ EgenX A, x * x ∈ A := by
  intro x hx
  refine Subgroup.iSup_induction' (fun g : X => ⨆ (_ : InOmegaA A g), conjSubgroup g A)
    (C := fun x _ => x * x ∈ A) ?_ ?_ ?_ hx
  · intro g y hy
    have hy' : y ∈ ⨆ (_ : InOmegaA A g), conjSubgroup g A := hy
    show y * y ∈ A
    by_cases hg : InOmegaA A g
    · rw [iSup_pos hg] at hy'
      rw [endgC_sq_conj hO hy']
      exact A.one_mem
    · rw [iSup_neg hg, Subgroup.mem_bot] at hy'
      rw [hy', mul_one]
      exact A.one_mem
  · show (1 : X) * 1 ∈ A
    rw [mul_one]
    exact A.one_mem
  · intro u v hu hv hcu hcv
    show (u * v) * (u * v) ∈ A
    have hcu' : u * u ∈ A := hcu
    have hcv' : v * v ∈ A := hcv
    have hu' : u ∈ EgenX A := hu
    have hv' : v ∈ EgenX A := hv
    have hc : ⁅u⁻¹, v⁆ ∈ A := hO.e (Subgroup.commutator_mem_commutator (inv_mem hu') hv')
    have hid : (u * v) * (u * v) = (u * u) * ⁅u⁻¹, v⁆ * (v * v) := by
      rw [commutatorElement_def]
      group
    rw [hid]
    exact mul_mem (mul_mem hcu' hc) hcv'

theorem endg_EgenX_pgroup (hO : EndOmegaHyp A) : IsPGroup 2 (EgenX A) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  have h2 : (g : X) * (g : X) ∈ A := endg_EgenX_sq_mem hO (g : X) g.2
  have h4 : ((g : X) * g) * ((g : X) * g) = 1 := hO.sq _ h2
  have e : (g : X) ^ (2 ^ 2) = ((g : X) * g) * ((g : X) * g) := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, pow_two]
  rw [Subgroup.coe_pow, Subgroup.coe_one, e, h4]

theorem endg_EgenX_class_two (hO : EndOmegaHyp A) :
    ∀ x ∈ EgenX A, ∀ y ∈ EgenX A, ∀ z ∈ EgenX A, ⁅⁅x, y⁆, z⁆ = 1 := by
  intro x hx y hy z hz
  have hw : ⁅x, y⁆ ∈ A := hO.e (Subgroup.commutator_mem_commutator hx hy)
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (endg_EgenX_comm_A A z hz _ hw).symm

private theorem endgC_commute_EgenX (A : Subgroup X)
    (hgen : ∀ g h : X, InOmegaA A g → InOmegaA A h →
      ∀ x ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup h A, x * y = y * x) :
    ∀ x ∈ EgenX A, ∀ y ∈ EgenX A, x * y = y * x := by
  have inner : ∀ g : X, InOmegaA A g → ∀ x ∈ conjSubgroup g A, ∀ y ∈ EgenX A,
      x * y = y * x := by
    intro g hg x hx y hy
    refine Subgroup.iSup_induction' (fun h : X => ⨆ (_ : InOmegaA A h), conjSubgroup h A)
      (C := fun y _ => x * y = y * x) ?_ ?_ ?_ hy
    · intro h y' hy'
      have hy'' : y' ∈ ⨆ (_ : InOmegaA A h), conjSubgroup h A := hy'
      show x * y' = y' * x
      by_cases hh : InOmegaA A h
      · rw [iSup_pos hh] at hy''
        exact hgen g h hg hh x hx y' hy''
      · rw [iSup_neg hh, Subgroup.mem_bot] at hy''
        rw [hy'', mul_one, one_mul]
    · show x * 1 = 1 * x
      rw [mul_one, one_mul]
    · intro u v hu hv huc hvc
      show x * (u * v) = u * v * x
      exact Commute.mul_right (show Commute x u from huc) (show Commute x v from hvc)
  intro x hx
  refine Subgroup.iSup_induction' (fun g : X => ⨆ (_ : InOmegaA A g), conjSubgroup g A)
    (C := fun x _ => ∀ y ∈ EgenX A, x * y = y * x) ?_ ?_ ?_ hx
  · intro g x' hx'
    have hx'' : x' ∈ ⨆ (_ : InOmegaA A g), conjSubgroup g A := hx'
    by_cases hg : InOmegaA A g
    · rw [iSup_pos hg] at hx''
      exact inner g hg x' hx''
    · rw [iSup_neg hg, Subgroup.mem_bot] at hx''
      intro y _
      rw [hx'', one_mul, mul_one]
  · intro y _
    rw [mul_one, one_mul]
  · intro u v _ _ huc hvc y hy
    exact (show Commute u y from huc y hy).mul_left (show Commute v y from hvc y hy)

theorem endg_six_three (hO : EndOmegaHyp A) (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥) :
    ⁅EgenX A, EgenX A⁆ = A := by
  refine le_antisymm hO.e ?_
  have hnc : ∃ g h : X, InOmegaA A g ∧ InOmegaA A h ∧
      ∃ x ∈ conjSubgroup g A, ∃ y ∈ conjSubgroup h A, x * y ≠ y * x := by
    by_contra hcon
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu v hv
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    refine endgC_commute_EgenX A (fun g h hg hh x hx y hy => ?_) u hu v hv
    by_contra hxy
    exact hcon ⟨g, h, hg, hh, x, hx, y, hy, hxy⟩
  obtain ⟨g, h, hg, hh, x, hx, y, hy, hxy⟩ := hnc
  have hgE : conjSubgroup g A ≤ EgenX A := le_iSup₂_of_le g hg le_rfl
  have hhE : conjSubgroup h A ≤ EgenX A := le_iSup₂_of_le h hh le_rfl
  have hxE : x ∈ EgenX A := hgE hx
  have hx1 : x ≠ 1 := by
    intro h1
    apply hxy
    rw [h1, one_mul, mul_one]
  have hcomm_mem : ∀ w ∈ conjSubgroup h A, ⁅w, x⁆ ∈ A := fun w hw =>
    hO.e (Subgroup.commutator_mem_commutator (hhE hw) hxE)
  let f : conjSubgroup h A → A := fun w => ⟨⁅(w : X), x⁆, hcomm_mem (w : X) w.2⟩
  have hf_mul : ∀ a b : conjSubgroup h A, f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    show ⁅((a * b : conjSubgroup h A) : X), x⁆ = ⁅(a : X), x⁆ * ⁅(b : X), x⁆
    rw [Subgroup.coe_mul, endgC_comm_key A (hhE a.2) (hcomm_mem (b : X) b.2)]
    exact hO.comm _ (hcomm_mem (b : X) b.2) _ (hcomm_mem (a : X) a.2)
  let ψ : conjSubgroup h A →* A := MonoidHom.mk' f hf_mul
  have hψ : ∀ w : conjSubgroup h A, ((ψ w : A) : X) = ⁅(w : X), x⁆ := fun w => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : ⁅(a : X), x⁆ = 1 := by
      have h0 := congrArg Subtype.val ha
      rw [hψ] at h0
      exact h0
    by_contra ha1
    have ha1' : (a : X) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
    have hcomm : x * (a : X) = (a : X) * x :=
      (commutatorElement_eq_one_iff_mul_comm.1 ha').symm
    exact hxy (hO.n1 g h x hx hx1 (a : X) a.2 ha1' hcomm x hx y hy)
  have hcard : Nat.card A ≤ Nat.card (conjSubgroup h A) := le_of_eq (endgC_card h A).symm
  have hbij : Function.Bijective ψ := hinj.bijective_of_nat_card_le hcard
  intro a ha
  obtain ⟨w, hw⟩ := hbij.2 ⟨a, ha⟩
  have hwa : ⁅(w : X), x⁆ = a := congrArg Subtype.val hw
  rw [← hwa]
  exact Subgroup.commutator_mem_commutator (hhE w.2) hxE

theorem endg_EgenX_conj (A : Subgroup X) (g : X) :
    conjSubgroup g (EgenX A) = ⨆ (h : X)
      (_ : ∀ z ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup h A, z * y = y * z), conjSubgroup h A := by
  apply le_antisymm
  · show (EgenX A).map (MulAut.conj g).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    unfold EgenX
    refine iSup₂_le fun h hh => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    show conjSubgroup g (conjSubgroup h A) ≤ _
    rw [← endgC_conj_mul]
    exact le_iSup₂_of_le (g * h) ((endgC_cond A g h).2 hh) le_rfl
  · refine iSup₂_le fun k hk => ?_
    have hk' := (endgC_cond A g (g⁻¹ * k)).1 (by rw [mul_inv_cancel_left]; exact hk)
    have e1 : conjSubgroup k A = conjSubgroup g (conjSubgroup (g⁻¹ * k) A) := by
      rw [← endgC_conj_mul, mul_inv_cancel_left]
    rw [e1]
    exact Subgroup.map_mono (le_iSup₂_of_le (g⁻¹ * k) hk' le_rfl)

end OmegaOne

section OmegaTwo

variable {X : Type} [Group X] [Finite X] {A : Subgroup X}

private theorem endgD_gen_le {g : X} (hg : InOmegaA A g) : conjSubgroup g A ≤ EgenX A := by
  unfold EgenX
  exact le_iSup₂_of_le g hg le_rfl

private theorem endgD_egen_comm {u : X} (hu : u ∈ EgenX A) {a : X} (ha : a ∈ A) :
    u * a = a * u := by
  have hc : EgenX A ≤ Subgroup.centralizer (A : Set X) := by
    unfold EgenX
    refine iSup₂_le fun g hg => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hg b hb y hy
  exact (Subgroup.mem_centralizer_iff.1 (hc hu) a ha).symm

private theorem endgD_comm_mul (hO : EndOmegaHyp A) {u v x : X} (hu : u ∈ EgenX A)
    (hv : v ∈ EgenX A) (hx : x ∈ EgenX A) : ⁅u * v, x⁆ = ⁅u, x⁆ * ⁅v, x⁆ := by
  have hvx : ⁅v, x⁆ ∈ A := hO.e (Subgroup.commutator_mem_commutator hv hx)
  have hux : ⁅u, x⁆ ∈ A := hO.e (Subgroup.commutator_mem_commutator hu hx)
  have hcomm : u * ⁅v, x⁆ = ⁅v, x⁆ * u := endgD_egen_comm hu hvx
  calc ⁅u * v, x⁆ = u * ⁅v, x⁆ * u⁻¹ * ⁅u, x⁆ := by
        simp only [commutatorElement_def]; group
    _ = ⁅v, x⁆ * ⁅u, x⁆ := by rw [hcomm, mul_inv_cancel_right]
    _ = ⁅u, x⁆ * ⁅v, x⁆ := hO.comm _ hvx _ hux

private theorem endgD_exists_ne_one (hA : A ≠ ⊥) (h : X) :
    ∃ y ∈ conjSubgroup h A, y ≠ 1 := by
  by_contra hall
  push Not at hall
  apply hA
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  have hm : h * a * h⁻¹ ∈ conjSubgroup h A := by
    rw [mem_conjSubgroup]
    have e : h⁻¹ * (h * a * h⁻¹) * h = a := by group
    rw [e]
    exact ha
  have h1 : h * a * h⁻¹ = 1 := hall _ hm
  calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
    _ = 1 := by rw [h1]; group

private theorem endgD_conj_commutator (g : X) (K L : Subgroup X) :
    conjSubgroup g ⁅K, L⁆ = ⁅conjSubgroup g K, conjSubgroup g L⁆ := by
  unfold conjSubgroup
  rw [Subgroup.map_commutator]

theorem endg_six_two (hO : EndOmegaHyp A) {g h : X} (hg : InOmegaA A g) (hh : InOmegaA A h)
    {x : X} (hx : x ∈ conjSubgroup g A) (hx1 : x ≠ 1) :
    (∀ y ∈ conjSubgroup h A, x * y = y * x) ∨
      (∀ a ∈ A, ∃ y ∈ conjSubgroup h A, y * x * y⁻¹ = a * x) := by
  by_cases hcase : ∃ y₀ ∈ conjSubgroup h A, y₀ ≠ 1 ∧ x * y₀ = y₀ * x
  · obtain ⟨y₀, hy₀, hy₀1, hc⟩ := hcase
    exact Or.inl fun y hy => hO.n1 g h x hx hx1 y₀ hy₀ hy₀1 hc x hx y hy
  right
  push Not at hcase
  have hxE : x ∈ EgenX A := endgD_gen_le hg hx
  have hmem : ∀ y ∈ conjSubgroup h A, ⁅y, x⁆ ∈ A := fun y hy =>
    hO.e (Subgroup.commutator_mem_commutator (endgD_gen_le hh hy) hxE)
  let f : ↥(conjSubgroup h A) →* ↥A :=
    MonoidHom.mk' (fun y => ⟨⁅(y : X), x⁆, hmem y y.2⟩)
      (fun u v => Subtype.ext (endgD_comm_mul hO (endgD_gen_le hh u.2) (endgD_gen_le hh v.2) hxE))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : ⁅(a : X), x⁆ = 1 := congrArg Subtype.val ha
    have h2 : (a : X) * x = x * a := commutatorElement_eq_one_iff_mul_comm.1 h1
    by_contra hne1
    exact hcase (a : X) a.2 (fun h3 => hne1 (Subtype.ext h3)) h2.symm
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, card_conjSubgroup h A⟩).2
  intro a ha
  obtain ⟨y, hy⟩ := hsurj ⟨a, ha⟩
  have hya : ⁅(y : X), x⁆ = a := congrArg Subtype.val hy
  refine ⟨(y : X), y.2, ?_⟩
  calc (y : X) * x * (y : X)⁻¹ = ⁅(y : X), x⁆ * x := by
        simp only [commutatorElement_def]; group
    _ = a * x := by rw [hya]

theorem endg_exists_noncomm (hO : EndOmegaHyp A) (F : OmegaPart1 A)
    (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥) {g : X} (hg : InOmegaA A g) (hgA : conjSubgroup g A ≠ A)
    {x : X} (hx : x ∈ conjSubgroup g A) (hx1 : x ≠ 1) :
    ∃ h : X, InOmegaA A h ∧ ∃ y ∈ conjSubgroup h A, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hP : ∀ h : X, InOmegaA A h → ∀ z ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup h A,
      z * y = y * z := by
    intro h hh
    obtain ⟨y₀, hy₀, hy₀1⟩ := endgD_exists_ne_one hO.ne_bot h
    exact fun z hz y hy => hO.n1 g h x hx hx1 y₀ hy₀ hy₀1 (hcon h hh y₀ hy₀) z hz y hy
  have hE : EgenX A ≤ conjSubgroup g (EgenX A) := by
    rw [F.conj g]
    unfold EgenX
    exact iSup₂_le fun h hh => le_iSup₂_of_le h (hP h hh) le_rfl
  have hEq : EgenX A = conjSubgroup g (EgenX A) :=
    Subgroup.eq_of_le_of_card_ge hE (card_conjSubgroup g (EgenX A)).le
  have hcomm : conjSubgroup g ⁅EgenX A, EgenX A⁆ = ⁅EgenX A, EgenX A⁆ := by
    rw [endgD_conj_commutator, ← hEq]
  rw [F.six_three hne] at hcomm
  exact hgA hcomm

theorem endg_six_four (hO : EndOmegaHyp A) (F : OmegaPart1 A) (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥)
    {g : X} (hg : InOmegaA A g) (hgA : conjSubgroup g A ≠ A) {x : X}
    (hx : x ∈ conjSubgroup g A) (hx1 : x ≠ 1) : ∀ a ∈ A, ∃ y : X, y * x * y⁻¹ = a * x := by
  obtain ⟨h, hh, y, hy, hxy⟩ := endg_exists_noncomm hO F hne hg hgA hx hx1
  rcases F.six_two hg hh hx hx1 with h1 | h2
  · exact absurd (h1 y hy) hxy
  · intro a ha
    obtain ⟨y', -, hy'⟩ := h2 a ha
    exact ⟨y', hy'⟩

theorem endg_six_four_gen (hO : EndOmegaHyp A) (F : OmegaPart1 A) (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥)
    {g h : X} (hgh : conjSubgroup g A ≠ conjSubgroup h A)
    (hc : ∀ z ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup h A, z * y = y * z) {y : X}
    (hy : y ∈ conjSubgroup h A) (hy1 : y ≠ 1) :
    ∀ u ∈ conjSubgroup g A, ∃ w : X, w * y * w⁻¹ = u * y := by
  have hg₀ : InOmegaA A (g⁻¹ * h) := by
    intro z hz y' hy'
    have hzg : g * z * g⁻¹ ∈ conjSubgroup g A := by
      rw [mem_conjSubgroup]
      have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rw [e]
      exact hz
    have hyh : g * y' * g⁻¹ ∈ conjSubgroup h A := by
      rw [mem_conjSubgroup]
      have e : h⁻¹ * (g * y' * g⁻¹) * h = (g⁻¹ * h)⁻¹ * y' * (g⁻¹ * h) := by group
      rw [e]
      exact (mem_conjSubgroup).1 hy'
    have key := hc _ hzg _ hyh
    calc z * y' = g⁻¹ * (g * z * g⁻¹ * (g * y' * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y' * g⁻¹ * (g * z * g⁻¹)) * g := by rw [key]
      _ = y' * z := by group
  have hgA₀ : conjSubgroup (g⁻¹ * h) A ≠ A := by
    intro heq
    have key : conjSubgroup g (conjSubgroup (g⁻¹ * h) A) = conjSubgroup h A := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left]
    rw [heq] at key
    exact hgh key
  have hx₀ : g⁻¹ * y * g ∈ conjSubgroup (g⁻¹ * h) A := by
    rw [mem_conjSubgroup]
    have e : (g⁻¹ * h)⁻¹ * (g⁻¹ * y * g) * (g⁻¹ * h) = h⁻¹ * y * h := by group
    rw [e]
    exact (mem_conjSubgroup).1 hy
  have hx₀1 : g⁻¹ * y * g ≠ 1 := by
    intro h1
    apply hy1
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  intro u hu
  obtain ⟨w₀, hw₀⟩ := endg_six_four hO F hne hg₀ hgA₀ hx₀ hx₀1 (g⁻¹ * u * g)
    ((mem_conjSubgroup).1 hu)
  refine ⟨g * w₀ * g⁻¹, ?_⟩
  calc g * w₀ * g⁻¹ * y * (g * w₀ * g⁻¹)⁻¹ = g * (w₀ * (g⁻¹ * y * g) * w₀⁻¹) * g⁻¹ := by
        group
    _ = g * (g⁻¹ * u * g * (g⁻¹ * y * g)) * g⁻¹ := by rw [hw₀]
    _ = u * y := by group

end OmegaTwo

section OmegaAssembly

variable {X : Type} [Group X] [Finite X] {A : Subgroup X}

theorem endg_omegaPart1 (hO : EndOmegaHyp A) : OmegaPart1 A where
  A_le := endg_A_le_EgenX hO
  comm_A := endg_EgenX_comm_A A
  pgroup := endg_EgenX_pgroup hO
  class_two := endg_EgenX_class_two hO
  six_two := fun {g h} hg hh {x} hx hx1 => endg_six_two hO hg hh hx hx1
  six_three := endg_six_three hO
  conj := endg_EgenX_conj A

theorem endg_omegaPart2 (hO : EndOmegaHyp A) : OmegaPart2 A :=
  have F := endg_omegaPart1 hO
  { exists_noncomm := fun hne {g} hg hgA {x} hx hx1 => endg_exists_noncomm hO F hne hg hgA hx hx1
    six_four := fun hne {g} hg hgA {x} hx hx1 => endg_six_four hO F hne hg hgA hx hx1
    six_four_gen := fun hne {g h} hgh hc {y} hy hy1 => endg_six_four_gen hO F hne hgh hc hy hy1 }

end OmegaAssembly

end CFSG.RankThree.GF2n.Stroth80
