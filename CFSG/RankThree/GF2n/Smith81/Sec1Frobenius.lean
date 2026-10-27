module

public import CFSG.RankThree.GF2n.Smith81.Sec1Fusion
public import CFSG.RankThree.GF2n.Stroth80.FrobClause

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section FieldAlg

theorem semilin_involution_eq {K : Type} [Field K] [Finite K] [CharP K 2] {a₁ a₂ : K}
    {σ₁ σ₂ : K ≃+* K} (h1 : ∀ s, a₁ * σ₁ (a₁ * σ₁ s) = s) (h2 : ∀ s, a₂ * σ₂ (a₂ * σ₂ s) = s)
    (hc : ∀ s, a₁ * σ₁ (a₂ * σ₂ s) = a₂ * σ₂ (a₁ * σ₁ s))
    (hne1 : ∃ s, a₁ * σ₁ s ≠ s) (hne2 : ∃ s, a₂ * σ₂ s ≠ s) :
    ∀ s, a₁ * σ₁ s = a₂ * σ₂ s := by
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have key : ∀ (a : K) (σ : K ≃+* K), (∀ s, a * σ (a * σ s) = s) → (∃ s, a * σ s ≠ s) →
      a * σ a = 1 ∧ (∀ s, σ (σ s) = s) ∧ ∃ s, σ s ≠ s := by
    intro a σ h hne
    have h1' : a * σ a = 1 := by simpa using h 1
    have hσσ : ∀ s, σ (σ s) = s := by
      intro s
      have := h s
      rw [map_mul, ← mul_assoc, h1', one_mul] at this
      exact this
    refine ⟨h1', hσσ, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs⟩ := hne
    have ha : a * a = 1 := by simpa [hcon] using h1'
    have ha1 : a = 1 := by
      have : (a - 1) ^ 2 = 0 := by linear_combination ha + (1 - a) * h2K
      exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp this)
    apply hs
    rw [hcon, ha1, one_mul]
  obtain ⟨hn1, hs1, hσ1⟩ := key a₁ σ₁ h1 hne1
  obtain ⟨hn2, hs2, hσ2⟩ := key a₂ σ₂ h2 hne2
  have hσ : σ₁ = σ₂ := by
    refine ringEquiv_eq_of_sq_eq_one σ₁ σ₂ (RingEquiv.ext hs1) (RingEquiv.ext hs2) ?_ ?_
    · rintro rfl
      obtain ⟨s, hs⟩ := hσ1
      exact hs rfl
    · rintro rfl
      obtain ⟨s, hs⟩ := hσ2
      exact hs rfl
  subst hσ
  have hcomm := hc 1
  simp only [mul_one, map_one] at hcomm
  have hsq : a₁ ^ 2 = a₂ ^ 2 := by
    linear_combination (a₁ * a₂) * hcomm - a₁ ^ 2 * hn2 + a₂ ^ 2 * hn1
  have ha : a₁ = a₂ := by
    have : (a₁ - a₂) ^ 2 = 0 := by linear_combination hsq + (a₂ ^ 2 - a₁ * a₂) * h2K
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  intro s
  rw [ha]

end FieldAlg

section SemilinAct

@[expose] def SemilinAct (N Y : Subgroup G) : Prop :=
  (∀ m ∈ N, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y) ∧
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : ↥Y ≃* Multiplicative K), ∀ m ∈ N,
    ∃ (a : Kˣ) (σ : K ≃+* K), ∀ z w : ↥Y, (w : G) = m * z * m⁻¹ →
      Multiplicative.toAdd (e w) = (a : K) * σ (Multiplicative.toAdd (e z))

theorem semilinAct_Z [Finite G] {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) : SemilinAct M Z := by
  refine ⟨fun m hm y hy => (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hm) y).mp hy, ?_⟩
  obtain ⟨K, hK, hfin, -, e, h⟩ := (stroth_frobClause H).1
  exact ⟨K, hK, hfin, e, h⟩

theorem SemilinAct.conj {N Y : Subgroup G} (h : SemilinAct N Y) (g : G) :
    SemilinAct (conjSubgroup g N) (conjSubgroup g Y) := by
  obtain ⟨hN, K, hK, hfin, e, hact⟩ := h
  refine ⟨?_, K, hK, hfin, ?_⟩
  · intro m' hm' y' hy'
    rw [mem_conjSubgroup] at hm' hy' ⊢
    have := hN _ hm' _ hy'
    have e1 : g⁻¹ * m' * g * (g⁻¹ * y' * g) * (g⁻¹ * m' * g)⁻¹ = g⁻¹ * (m' * y' * m'⁻¹) * g := by
      group
    rwa [e1] at this
  · let e₀ : ↥Y ≃* ↥(conjSubgroup g Y) := MulEquiv.subgroupMap (MulAut.conj g) Y
    refine ⟨e₀.symm.trans e, ?_⟩
    intro m' hm'
    rw [mem_conjSubgroup] at hm'
    obtain ⟨a, σ, hs⟩ := hact _ hm'
    refine ⟨a, σ, fun z' w' hw' => ?_⟩
    show Multiplicative.toAdd (e (e₀.symm w')) = a * σ (Multiplicative.toAdd (e (e₀.symm z')))
    apply hs
    have hz : (z' : G) = g * (e₀.symm z' : G) * g⁻¹ := by
      have := congrArg Subtype.val (e₀.apply_symm_apply z')
      exact this.symm
    have hw : (w' : G) = g * (e₀.symm w' : G) * g⁻¹ := by
      have := congrArg Subtype.val (e₀.apply_symm_apply w')
      exact this.symm
    rw [hz, hw] at hw'
    have : (e₀.symm w' : G) = g⁻¹ * (g * (e₀.symm w' : G) * g⁻¹) * g := by group
    rw [this, hw']
    group

end SemilinAct

section CardSq

theorem card_le_sq_card_centralizer [Finite G] {Z : Subgroup G} {x : G}
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ2 : ∀ z ∈ Z, z * z = 1) (hx2 : x * x = 1)
    (hxN : ∀ z ∈ Z, x * z * x⁻¹ ∈ Z) :
    Nat.card Z ≤ Nat.card ↥(Z ⊓ Subgroup.centralizer ({x} : Set G)) ^ 2 := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  let φ : G → G := fun z => x * z * x⁻¹ * z⁻¹
  have hφZ : ∀ a ∈ Z, φ a ∈ Z := fun a ha => Z.mul_mem (hxN a ha) (Z.inv_mem ha)
  have hφmul : ∀ a ∈ Z, ∀ b ∈ Z, φ (a * b) = φ a * φ b := by
    intro a ha b hb
    have h := hZc _ (Z.mul_mem (hxN b hb) (Z.inv_mem hb)) _ (Z.inv_mem ha)
    show x * (a * b) * x⁻¹ * (a * b)⁻¹ = (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹)
    calc x * (a * b) * x⁻¹ * (a * b)⁻¹
        = (x * a * x⁻¹) * (((x * b * x⁻¹) * b⁻¹) * a⁻¹) := by group
      _ = (x * a * x⁻¹) * (a⁻¹ * ((x * b * x⁻¹) * b⁻¹)) := by rw [h]
      _ = (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by group
  let f : ↥Z →* ↥Z := MonoidHom.mk' (fun z => ⟨φ z, hφZ z z.2⟩)
    (fun a b => Subtype.ext (hφmul a a.2 b b.2))
  have hcard : Nat.card ↥Z = Nat.card ↥f.ker * Nat.card ↥f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : ∀ z : ↥Z, z ∈ f.ker → (z : G) ∈ Z ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    refine ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : φ z = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
    have h2 : x * z * x⁻¹ = z := by
      have : x * z * x⁻¹ * z⁻¹ = 1 := h1
      exact mul_inv_eq_one.mp this
    have := mul_inv_eq_iff_eq_mul.mp h2
    exact this.symm
  have hrange : ∀ w : ↥Z, w ∈ f.range → (w : G) ∈ Z ⊓ Subgroup.centralizer ({x} : Set G) := by
    rintro w ⟨z, rfl⟩
    refine ⟨(f z).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hw2 : φ z * φ z = 1 := hZ2 _ (hφZ z z.2)
    have e : x * φ z * x⁻¹ = (φ z)⁻¹ := by
      simp only [φ]
      rw [hxinv]
      have e3 : (x * (z : G) * x * (z : G)⁻¹)⁻¹ = (z : G) * x⁻¹ * (z : G)⁻¹ * x⁻¹ := by group
      rw [e3, hxinv]
      calc x * (x * ↑z * x * (↑z)⁻¹) * x = (x * x) * ↑z * x * (↑z)⁻¹ * x := by group
        _ = (z : G) * x * (z : G)⁻¹ * x := by rw [hx2, one_mul]
    have e2 : (φ z)⁻¹ = φ z := inv_eq_of_mul_eq_one_right hw2
    rw [e2] at e
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  have h1 : Nat.card ↥f.ker ≤ Nat.card ↥(Z ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_le_card_of_injective (fun z => ⟨(z.1 : G), hker z.1 z.2⟩) ?_
    intro a b hab
    have h := congrArg Subtype.val hab
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have h2 : Nat.card ↥f.range ≤ Nat.card ↥(Z ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_le_card_of_injective (fun w => ⟨(w.1 : G), hrange w.1 w.2⟩) ?_
    intro a b hab
    have h := congrArg Subtype.val hab
    apply Subtype.ext
    apply Subtype.ext
    exact h
  rw [hcard, sq]
  exact Nat.mul_le_mul h1 h2

end CardSq

section Cover

theorem semilin_cover [Finite G] {N Y C : Subgroup G} (hS : SemilinAct N Y)
    (hY2 : ∀ y ∈ Y, y * y = 1) (hCN : C ≤ N) (hC2 : ∀ c ∈ C, c * c = 1)
    (hCc : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) :
    Nat.card C ≤ 2 * Nat.card ↥(C ⊓ Subgroup.centralizer (Y : Set G)) := by
  classical
  obtain ⟨hNY, K, hK, hfin, e, hact⟩ := hS
  have hK2 : (2 : K) = 0 := by
    obtain ⟨y, hy⟩ := e.surjective (Multiplicative.ofAdd (1 : K))
    have h1 : y * y = 1 := Subtype.ext (hY2 y y.2)
    have := congrArg e h1
    rw [map_mul, hy, map_one e] at this
    have h2 := congrArg Multiplicative.toAdd this
    simp only [toAdd_mul, toAdd_ofAdd, toAdd_one] at h2
    rw [one_add_one_eq_two] at h2
    exact h2
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hK2
  have hsame : ∀ c ∈ C, c ∉ Subgroup.centralizer (Y : Set G) → ∀ c' ∈ C,
      c' ∉ Subgroup.centralizer (Y : Set G) → ∀ y ∈ Y, c * y * c⁻¹ = c' * y * c'⁻¹ := by
    intro c hc hcn c' hc' hcn'
    obtain ⟨a, σ, hs⟩ := hact c (hCN hc)
    obtain ⟨a', σ', hs'⟩ := hact c' (hCN hc')
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hC2 c hc)
    have hc'inv : c'⁻¹ = c' := inv_eq_of_mul_eq_one_right (hC2 c' hc')
    have act1 : ∀ y : ↥Y, Multiplicative.toAdd (e ⟨c * y * c⁻¹, hNY c (hCN hc) y y.2⟩) =
        (a : K) * σ (Multiplicative.toAdd (e y)) := fun y => hs y _ rfl
    have act2 : ∀ y : ↥Y, Multiplicative.toAdd (e ⟨c' * y * c'⁻¹, hNY c' (hCN hc') y y.2⟩) =
        (a' : K) * σ' (Multiplicative.toAdd (e y)) := fun y => hs' y _ rfl
    have hsy : ∀ s : K, ∃ y : ↥Y, Multiplicative.toAdd (e y) = s := fun s =>
      ⟨e.symm (Multiplicative.ofAdd s), by simp⟩
    have h1 : ∀ s, (a : K) * σ ((a : K) * σ s) = s := by
      intro s
      obtain ⟨y, rfl⟩ := hsy s
      have := act1 ⟨c * y * c⁻¹, hNY c (hCN hc) y y.2⟩
      rw [act1 y] at this
      have e1 : (⟨c * (c * y * c⁻¹) * c⁻¹, hNY c (hCN hc) _ (hNY c (hCN hc) y y.2)⟩ : ↥Y) = y := by
        apply Subtype.ext
        show c * (c * y * c⁻¹) * c⁻¹ = y
        rw [hcinv]
        calc c * (c * (y : G) * c) * c = (c * c) * y * (c * c) := by group
          _ = y := by rw [hC2 c hc]; simp
      rw [e1] at this
      exact this.symm
    have h1' : ∀ s, (a' : K) * σ' ((a' : K) * σ' s) = s := by
      intro s
      obtain ⟨y, rfl⟩ := hsy s
      have := act2 ⟨c' * y * c'⁻¹, hNY c' (hCN hc') y y.2⟩
      rw [act2 y] at this
      have e1 : (⟨c' * (c' * y * c'⁻¹) * c'⁻¹,
          hNY c' (hCN hc') _ (hNY c' (hCN hc') y y.2)⟩ : ↥Y) = y := by
        apply Subtype.ext
        show c' * (c' * y * c'⁻¹) * c'⁻¹ = y
        rw [hc'inv]
        calc c' * (c' * (y : G) * c') * c' = (c' * c') * y * (c' * c') := by group
          _ = y := by rw [hC2 c' hc']; simp
      rw [e1] at this
      exact this.symm
    have hcomm : ∀ s, (a : K) * σ ((a' : K) * σ' s) = (a' : K) * σ' ((a : K) * σ s) := by
      intro s
      obtain ⟨y, rfl⟩ := hsy s
      have h3 := act1 ⟨c' * y * c'⁻¹, hNY c' (hCN hc') y y.2⟩
      rw [act2 y] at h3
      have h4 := act2 ⟨c * y * c⁻¹, hNY c (hCN hc) y y.2⟩
      rw [act1 y] at h4
      have e1 : (⟨c * (c' * y * c'⁻¹) * c⁻¹, hNY c (hCN hc) _ (hNY c' (hCN hc') y y.2)⟩ : ↥Y) =
          ⟨c' * (c * y * c⁻¹) * c'⁻¹, hNY c' (hCN hc') _ (hNY c (hCN hc) y y.2)⟩ := by
        apply Subtype.ext
        show c * (c' * (y : G) * c'⁻¹) * c⁻¹ = c' * (c * (y : G) * c⁻¹) * c'⁻¹
        have hcc := hCc c hc c' hc'
        calc c * (c' * (y : G) * c'⁻¹) * c⁻¹ = (c * c') * y * (c * c')⁻¹ := by group
          _ = (c' * c) * y * (c' * c)⁻¹ := by rw [hcc]
          _ = c' * (c * (y : G) * c⁻¹) * c'⁻¹ := by group
      rw [e1] at h3
      rw [← h3, ← h4]
    have hne : ∃ s, (a : K) * σ s ≠ s := by
      obtain ⟨y, hy, hyc⟩ : ∃ y ∈ Y, ¬ y * c = c * y := by
        by_contra hcon
        push Not at hcon
        exact hcn (Subgroup.mem_centralizer_iff.mpr hcon)
      refine ⟨Multiplicative.toAdd (e ⟨y, hy⟩), fun h => hyc ?_⟩
      rw [← act1 ⟨y, hy⟩] at h
      have h5 := e.injective (Multiplicative.toAdd.injective h)
      have h6 := congrArg Subtype.val h5
      simp only at h6
      rw [mul_inv_eq_iff_eq_mul] at h6
      exact h6.symm
    have hne' : ∃ s, (a' : K) * σ' s ≠ s := by
      obtain ⟨y, hy, hyc⟩ : ∃ y ∈ Y, ¬ y * c' = c' * y := by
        by_contra hcon
        push Not at hcon
        exact hcn' (Subgroup.mem_centralizer_iff.mpr hcon)
      refine ⟨Multiplicative.toAdd (e ⟨y, hy⟩), fun h => hyc ?_⟩
      rw [← act2 ⟨y, hy⟩] at h
      have h5 := e.injective (Multiplicative.toAdd.injective h)
      have h6 := congrArg Subtype.val h5
      simp only at h6
      rw [mul_inv_eq_iff_eq_mul] at h6
      exact h6.symm
    have hfin := semilin_involution_eq h1 h1' hcomm hne hne'
    intro y hy
    have h7 := hfin (Multiplicative.toAdd (e ⟨y, hy⟩))
    rw [← act1 ⟨y, hy⟩, ← act2 ⟨y, hy⟩] at h7
    have h8 := congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective h7))
    exact h8
  by_cases hall : C ≤ Subgroup.centralizer (Y : Set G)
  · rw [inf_eq_left.mpr hall]
    omega
  · obtain ⟨c₁, hc₁C, hc₁⟩ := SetLike.not_le_iff_exists.mp hall
    have hcov : ∀ c ∈ C, c ∉ Subgroup.centralizer (Y : Set G) →
        c₁⁻¹ * c ∈ Subgroup.centralizer (Y : Set G) := by
      intro c hc hcn
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have := hsame c₁ hc₁C hc₁ c hc hcn y hy
      calc y * (c₁⁻¹ * c) = c₁⁻¹ * (c₁ * y * c₁⁻¹) * c := by group
        _ = c₁⁻¹ * (c * y * c⁻¹) * c := by rw [this]
        _ = (c₁⁻¹ * c) * y := by group
    let ψ : ↥C → ↥(C ⊓ Subgroup.centralizer (Y : Set G)) × Bool := fun c =>
      if h : (c : G) ∈ Subgroup.centralizer (Y : Set G) then (⟨c, c.2, h⟩, false)
      else (⟨c₁⁻¹ * c, C.mul_mem (C.inv_mem hc₁C) c.2, hcov c c.2 h⟩, true)
    have hψ : Function.Injective ψ := by
      intro c c' h
      by_cases hc : (c : G) ∈ Subgroup.centralizer (Y : Set G) <;>
        by_cases hc' : (c' : G) ∈ Subgroup.centralizer (Y : Set G) <;>
        simp only [ψ, hc, hc', dite_true, dite_false, Prod.mk.injEq] at h
      · have h1' := congrArg Subtype.val h.1
        exact Subtype.ext h1'
      · exact absurd h.2 (by simp)
      · exact absurd h.2 (by simp)
      · have h1' := congrArg Subtype.val h.1
        simp only at h1'
        exact Subtype.ext (mul_left_cancel h1')
    have := Nat.card_le_card_of_injective ψ hψ
    rw [Nat.card_prod] at this
    simpa [mul_comm] using this

end Cover

section Smith112

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem Sit.X_inf_Q (hs : Sit M Q Z X x) : X ⊓ Q = ⊥ := by
  obtain ⟨g, hg, -, -⟩ := hs.QB_eq
  have H := hs.hyp
  have hZQ := H.Z_normal.1
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyX, hyQ⟩ := Subgroup.mem_inf.mp hy
  by_contra hy1
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [h]; exact Subgroup.one_mem _)
  have hyg : y ∈ conjSubgroup g Z := hg ▸ hyX
  have hyZ : y ∉ Z := by
    intro hyZ
    have : y ∈ Z ⊓ X := ⟨hyZ, hyX⟩
    rw [hs.Z_inf_X, Subgroup.mem_bot] at this
    exact hy1' this
  have hy' : ∃ (g' z : G), z ∈ Z ∧ y = g' * z * g'⁻¹ := by
    refine ⟨g, g⁻¹ * y * g, ?_, by group⟩
    exact mem_conjSubgroup.mp hyg
  obtain ⟨g', hg'Q, hyg'⟩ := stroth_2_6 H hyQ hyZ hy'
  have heq : conjSubgroup g Z = conjSubgroup g' Z :=
    conjSubgroup_eq_of_mem_ne_one H hy1' hyg hyg'
  apply hs.notQ
  apply hg'Q
  rw [← heq, ← hg]
  exact hs.mem


theorem Sit.X_le_M_of_centralizes (hs : Sit M Q Z X x) {z₀ : G} (hz₀Z : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (hz₀ : z₀ ∈ Subgroup.centralizer (X : Set G)) : ∀ w ∈ X, w ∈ M := by
  intro w hw
  have hcomm : w * z₀ = z₀ * w := Subgroup.mem_centralizer_iff.mp hz₀ w hw
  have := Tim77.mem_normalizer_of_commute_of_isTI hs.hyp.ti hz₀Z hz₀1 hcomm
  rwa [hs.hyp.normalizer_Z.1] at this

theorem Sit.X_le_M_of_Z_le_normalizer (hs : Sit M Q Z X x) (hq : 4 ≤ Nat.card Z)
    (hZN : ∀ z ∈ Z, z ∈ Subgroup.normalizer (X : Set G)) : ∀ w ∈ X, w ∈ M := by
  obtain ⟨g, hg, hQB, hN⟩ := hs.QB_eq
  have H := hs.hyp
  have hZQ := H.Z_normal.1
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => Z_central H ha (hZQ hb)
  have hZ2 : ∀ z ∈ Z, z * z = 1 := fun z hz => by rw [← pow_two]; exact Z_sq H hz
  have hSX : SemilinAct (Subgroup.normalizer (X : Set G)) X := by
    have := (semilinAct_Z H).conj g
    rw [← hN, ← hg] at this
    exact this
  have hcover := semilin_cover hSX hs.X_sq (C := Z) hZN hZ2 hZc
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ : ∃ z : ↥(Z ⊓ Subgroup.centralizer (X : Set G)), z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card ↥(Z ⊓ Subgroup.centralizer (X : Set G)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
    omega
  exact hs.X_le_M_of_centralizes (Subgroup.mem_inf.mp hz₀).1 (fun h => hz₀1 (Subtype.ext h))
    (Subgroup.mem_inf.mp hz₀).2

theorem Sit.post12_of_Z_le_normalizer (hs : Sit M Q Z X x) (hXQ : X ⊓ Q = ⊥)
    (hXM : ∀ w ∈ X, w ∈ M) (hZN : ∀ z ∈ Z, z ∈ Subgroup.normalizer (X : Set G)) :
    Post12 M Q Z X := by
  have H := hs.hyp
  refine ⟨?_, hXQ⟩
  intro w hw
  refine ⟨hXM w hw, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hwN := H.Z_normal.2 (hXM w hw)
  have h1 : ⁅z, w⁆ ∈ Z := by
    have e : ⁅z, w⁆ = z * (w * z⁻¹ * w⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem hz ((Subgroup.mem_normalizer_iff.mp hwN z⁻¹).mp (Z.inv_mem hz))
  have h2 : ⁅z, w⁆ ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (hZN z hz) w).mp hw
    rw [commutatorElement_def]
    exact X.mul_mem this (X.inv_mem hw)
  have h3 : ⁅z, w⁆ ∈ Z ⊓ X := ⟨h1, h2⟩
  rw [hs.Z_inf_X, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem smith_1_12_of_gt4 (hs : Sit M Q Z X x) (h4 : 4 < Nat.card Z) :
    Post12 M Q Z X := by
  obtain ⟨g, hg, hQB, hN⟩ := hs.QB_eq
  have H := hs.hyp
  have hZQ := H.Z_normal.1
  have hx2 := hs.x_sq
  have hXQ : X ⊓ Q = ⊥ := hs.X_inf_Q
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => Z_central H ha (hZQ hb)
  have hZ2 : ∀ z ∈ Z, z * z = 1 := fun z hz => by rw [← pow_two]; exact Z_sq H hz
  have hxN : ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hs.memM) z).mp hz
  set C : Subgroup G := Z ⊓ Subgroup.centralizer ({x} : Set G) with hC
  have hCZ : C ≤ Z := inf_le_left
  have hcard : Nat.card Z ≤ Nat.card C ^ 2 := card_le_sq_card_centralizer hZc hZ2 hx2 hxN
  have hC4 : 4 ≤ Nat.card C := by
    obtain ⟨n, k, hZn, -⟩ := H.cp
    have hdvd : Nat.card C ∣ 2 ^ n := hZn ▸ Subgroup.card_dvd_of_le hCZ
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · exfalso
      have hle : Nat.card C ≤ 2 := by
        rw [hj]
        calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      nlinarith
    · rw [hj]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
  have hCN : C ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    Tim77.mem_normalizer_of_commute_of_isTI hs.X_isTI hs.mem hs.ne_one
      (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
  have hSX : SemilinAct (Subgroup.normalizer (X : Set G)) X := by
    have := (semilinAct_Z H).conj g
    rw [← hN, ← hg] at this
    exact this
  have hcover := semilin_cover hSX hs.X_sq hCN (fun c hc => hZ2 c (hCZ hc))
    (fun c hc c' hc' => hZc c (hCZ hc) c' (hCZ hc'))
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ : ∃ z : ↥(C ⊓ Subgroup.centralizer (X : Set G)), z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card ↥(C ⊓ Subgroup.centralizer (X : Set G)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
    omega
  have hz₀' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  obtain ⟨hz₀C, hz₀X⟩ := Subgroup.mem_inf.mp hz₀
  have hXM : ∀ w ∈ X, w ∈ M := hs.X_le_M_of_centralizes (hCZ hz₀C) hz₀' hz₀X
  have hcover2 := semilin_cover (semilinAct_Z H) hZ2 (fun w hw => hXM w hw) hs.X_sq hs.X_comm
  have hXcard : Nat.card X = Nat.card Z := by
    rw [hg]; exact card_conjSubgroup g Z
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ : ∃ z : ↥(X ⊓ Subgroup.centralizer (Z : Set G)), z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card ↥(X ⊓ Subgroup.centralizer (Z : Set G)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
    omega
  have hx₀' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  obtain ⟨hx₀X, hx₀Z⟩ := Subgroup.mem_inf.mp hx₀
  have hZN : ∀ z ∈ Z, z ∈ Subgroup.normalizer (X : Set G) := by
    intro z hz
    have hcomm : z * x₀ = x₀ * z := Subgroup.mem_centralizer_iff.mp hx₀Z z hz
    exact Tim77.mem_normalizer_of_commute_of_isTI hs.X_isTI hx₀X hx₀' hcomm
  exact hs.post12_of_Z_le_normalizer hXQ hXM hZN

end Smith112

end CFSG.RankThree.GF2n.Smith81
