module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeAut

public section

namespace CFSG.StandardType.TwoThree

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.Assembly CFSG.StandardType.TypeA

variable {d : ℕ} {K : Type} [Field K]

section Two

variable [Finite K]

theorem det_eq_one_of_card (hK : Nat.card K = 2) (A : GL (Fin d) K) :
    (A : Matrix (Fin d) (Fin d) K).det = 1 := by
  have h := congrArg Units.val (units_eq_one hK (Matrix.GeneralLinearGroup.det A))
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h

@[expose] def toSLHom (hK : Nat.card K = 2) : GL (Fin d) K →* SpecialLinearGroup (Fin d) K where
  toFun A := ⟨A, det_eq_one_of_card hK A⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem coe_toSLHom (hK : Nat.card K = 2) (A : GL (Fin d) K) :
    ((toSLHom hK A : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = A :=
  rfl

theorem toGL_toSLHom (hK : Nat.card K = 2) (A : GL (Fin d) K) :
    SpecialLinearGroup.toGL (toSLHom hK A) = A :=
  Units.ext rfl

theorem eq_one_of_mem_scalars (hK : Nat.card K = 2) {g : SpecialLinearGroup (Fin d) K}
    (hg : g ∈ scalars d K) : g = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hg
  ext i j
  rw [hc, units_eq_one hK c, Units.val_one, map_one]
  rfl

end Two

section Act

variable {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}

theorem twist_act {a : MulAut L'} {h : SpecialLinearGroup (Fin d) K}
    (ha : ∀ s, a (φ s) = φ (h * s * h⁻¹)) (c : SpecialLinearGroup (Fin d) K) (s) :
    a ((φ.comp (MulAut.conj c⁻¹).toMonoidHom) s) =
      (φ.comp (MulAut.conj c⁻¹).toMonoidHom) (c * h * c⁻¹ * s * (c * h * c⁻¹)⁻¹) := by
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [ha]
  congr 1
  group

theorem ggFix_eq_map_centralizer (hφ : Function.Bijective φ) {a : MulAut L'}
    {h : SpecialLinearGroup (Fin d) K} (ha : ∀ s, a (φ s) = φ (h * s * h⁻¹)) :
    ggFix a = (Subgroup.centralizer {h}).map φ := by
  ext l
  obtain ⟨s, rfl⟩ := hφ.2 l
  rw [mem_ggFix, ha]
  constructor
  · intro h1
    refine ⟨s, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h2 := hφ.1 h1
    calc s * h = h * s * h⁻¹ * h := by rw [h2]
      _ = h * s := by group
  · rintro ⟨s', hs', hss'⟩
    have hs : s' = s := hφ.1 hss'
    subst hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hs'
    congr 1
    rw [← hs']
    group

end Act

@[expose] def fixSub {L' : Type} [Group L'] (S : Set L') : Subgroup (MulAut L') where
  carrier := {a | ∀ j ∈ S, a j = j}
  mul_mem' {a b} ha hb j hj := by rw [MulAut.mul_apply, hb j hj, ha j hj]
  one_mem' _ _ := rfl
  inv_mem' {a} ha j hj := by
    conv_lhs => rw [← ha j hj]
    exact MulAut.inv_apply_self _ _ _

theorem mem_fixSub {L' : Type} [Group L'] {S : Set L'} {a : MulAut L'} :
    a ∈ fixSub S ↔ ∀ j ∈ S, a j = j :=
  Iff.rfl

theorem induced_zpow {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R} {a : MulAut L'}
    {φ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l)) (k : ℤ) :
    ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
  rcases k with n | n
  · simpa using induced_pow ψ h n
  · intro l
    have h1 := induced_pow ψ h (n + 1) (((a ^ (n + 1))⁻¹ : MulAut L') l)
    rw [MulAut.apply_inv_self] at h1
    rw [zpow_negSucc, zpow_negSucc, ← h1, MulAut.inv_apply_self]

variable [Finite K] [CharP K 2]

theorem ggEndNode_two (hK : Nat.card K = 2) (hd : 6 ≤ d) :
    GGEndNode 3 (d / 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _
  have hsec : SLHasSections (m + 2) K := slHasSections_of_five_le (by omega)
  have hperfSL : commutator (SpecialLinearGroup (Fin (m + 2)) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := m + 2) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply eq_one_of_mem_scalars hK
    rw [← proj_eq_one_iff, ← hφ, hg, map_one]
  have hinj := conjAut_injective hK (d := m + 2) (by omega)
  set X := inducedSub ψ A with hX
  have hXA : IsElemAbelian 3 X := isElemAbelian_inducedSub hψ hA
  have hcardX : Nat.card X = Nat.card A := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ∀ x ∈ X, ∃ B : GL (Fin (m + 2)) K, conjAut (m + 2) K B = x := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    exact ⟨B, induced_unique ψ hψ hφa hxa⟩
  set Xt := X.comap (conjAut (m + 2) K) with hXt
  have hcardt : Nat.card Xt = Nat.card X := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun B : Xt => (⟨conjAut (m + 2) K B, B.2⟩ : X)) ⟨?_, ?_⟩)
    · intro B C hBC
      exact Subtype.ext (hinj (congrArg Subtype.val hBC))
    · rintro ⟨x, hx⟩
      obtain ⟨B, rfl⟩ := hXI x hx
      exact ⟨⟨B, hx⟩, rfl⟩
  have hcommt : ∀ B ∈ Xt, ∀ C ∈ Xt, B * C = C * B := fun B hB C hC =>
    hinj (by rw [map_mul, map_mul]; exact TableB.IsElemAbelian.comm hXA hB hC)
  have hexpt : ∀ B ∈ Xt, B ^ 3 = 1 := fun B hB =>
    hinj (by rw [map_pow, map_one]; exact hXA.2 _ hB)
  have hlift : ∀ a ∈ A, ∃ B ∈ Xt, ∀ l, conjAut (m + 2) K B (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    exact ⟨B, ⟨a, ha, hφa⟩, hφa⟩
  have hact : ∀ (a : MulAut L') (B : GL (Fin (m + 2)) K),
      (∀ l, conjAut (m + 2) K B (ψ l) = ψ (a l)) →
        ∀ s, a (φ s) = φ (toSLHom hK B * s * (toSLHom hK B)⁻¹) :=
    fun a B hB => act_of_lift hperfSL hker hφ (by rw [toGL_toSLHom]; exact hB)
  set e := (Matrix.GeneralLinearGroup.toLin : GL (Fin (m + 2)) K ≃* _) with he
  set Y : Subgroup (Module.End K (Fin (m + 2) → K))ˣ := Xt.map e.toMonoidHom with hY
  have hcardY : Nat.card Y = Nat.card Xt :=
    (Nat.card_congr (Xt.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hcommY : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩
    change e B * e C = e C * e B
    rw [← map_mul, ← map_mul, hcommt B hB C hC]
  have hexpY : ∀ x ∈ Y, x ^ 3 = 1 := by
    rintro _ ⟨B, hB, rfl⟩
    change e B ^ 3 = 1
    rw [← map_pow, hexpt B hB, map_one]
  have hcardA : 3 ^ ((m + 2) / 2) ≤ Nat.card Y := by
    rw [hcardY, hcardt, hcardX]
    exact hr
  have hYne : Y ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardA
    have : 1 < 3 ^ ((m + 2) / 2) := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hYcard : 3 ^ finrank K (Fin (m + 2) → K) ≤ 3 * Nat.card Y ^ 2 := by
    rw [Module.finrank_fin_fun]
    calc 3 ^ (m + 2) ≤ 3 ^ (2 * ((m + 2) / 2) + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 * (3 ^ ((m + 2) / 2)) ^ 2 := by ring
      _ ≤ 3 * Nat.card Y ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcardA 2)
  obtain ⟨g', hg'Y, hg'rank, hg'cent⟩ := exists_end_node hK Y hcommY hexpY hYne hYcard
  obtain ⟨B₀, hB₀, rfl⟩ := hg'Y
  have hB₀3 : (B₀ : Matrix (Fin (m + 2)) (Fin (m + 2)) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hexpt B₀ hB₀, Units.val_one]
  obtain ⟨P, hP⟩ := exists_conj_eq_g0 hK hB₀3 hg'rank
  obtain ⟨a₀, ha₀A, ha₀⟩ := hB₀
  set c := toSLHom hK P with hc
  set φ' := φ.comp (MulAut.conj c⁻¹).toMonoidHom with hφ'
  have hφ'bij : Function.Bijective φ' :=
    ⟨hφinj.comp (MulAut.conj c⁻¹).injective, hφs.comp (MulAut.conj c⁻¹).surjective⟩
  have hact' : ∀ (a : MulAut L') (B : GL (Fin (m + 2)) K),
      (∀ l, conjAut (m + 2) K B (ψ l) = ψ (a l)) → ∀ s,
        a (φ' s) = φ' (c * toSLHom hK B * c⁻¹ * s * (c * toSLHom hK B * c⁻¹)⁻¹) :=
    fun a B hB s => twist_act (hact a B hB) c s
  have hcmat : ∀ B : GL (Fin (m + 2)) K,
      ((c * toSLHom hK B * c⁻¹ : SpecialLinearGroup (Fin (m + 2)) K) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
        (P : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * (B : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
          ((P⁻¹ : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) := by
    intro B
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc, ← map_inv,
      coe_toSLHom, coe_toSLHom, coe_toSLHom]
  have hc0 : c * toSLHom hK B₀ * c⁻¹ = g0 m K := Subtype.ext ((hcmat B₀).trans hP)
  have hact₀ : ∀ s, a₀ (φ' s) = φ' (g0 m K * s * (g0 m K)⁻¹) := by
    intro s
    rw [hact' a₀ B₀ ha₀ s, hc0]
  have hfix₀ : ggFix a₀ = (Subgroup.centralizer {g0 m K}).map φ' :=
    ggFix_eq_map_centralizer hφ'bij hact₀
  obtain ⟨hlayer, hcomp⟩ := layer_centralizer_g0 hK (m := m) (by omega) (φ := φ')
    (fun j _ hj => hφ'bij.1 (by rw [hj, map_one]))
  rw [← hfix₀] at hlayer hcomp
  have hJfix : LargeEvenLayer (ggFix a₀) ≤ ggFix a₀ := sSup_le fun K hK => hK.1
  refine ⟨a₀, ha₀A, ?_, hlayer ▸ hcomp, ?_⟩
  · intro h1
    apply g0_ne_one (m := m) (K := K)
    have h2 : ∀ l, (1 : MulAut (projectiveSL (m + 2) K)) (ψ l) = ψ (a₀ l) := by
      intro l
      rw [h1]
      rfl
    have hB1 : conjAut (m + 2) K B₀ = 1 := induced_unique ψ hψ ha₀ h2
    have hB₀1 : B₀ = 1 := hinj (by rw [hB1, map_one])
    rw [← hc0, hB₀1, map_one, mul_one, mul_inv_cancel]
  · intro a' ha'
    constructor
    · intro hfix
      obtain ⟨B', hB', hB'ind⟩ := hlift a' ha'
      set h' := c * toSLHom hK B' * c⁻¹ with hh'
      have hact'' := hact' a' B' hB'ind
      have hcommJ : ∀ s ∈ coordBlockSL K (J01 m), s * h' = h' * s := by
        intro s hs
        have h1 := hfix (φ' s) (by rw [hlayer]; exact ⟨s, hs, rfl⟩)
        rw [hact''] at h1
        have h2 := hφ'bij.1 h1
        calc s * h' = h' * s * h'⁻¹ * h' := by rw [h2]
          _ = h' * s := by group
      have hcol := col_eq_of_commute_J0 hK (by omega) hcommJ
      have hfixW : ∀ w, (e B₀ : Module.End K (Fin (m + 2) → K)) w = w →
          (e B' : Module.End K (Fin (m + 2) → K)) w = w := by
        intro w hw
        change (B₀ : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ w = w at hw
        change (B' : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ w = w
        have hPw : (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ
            ((P : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ w) =
              (P : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ w := by
          rw [← hP, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one,
            ← Matrix.mulVec_mulVec, hw]
        have h3 := fixes_of_col_eq hcol hPw
        rw [hh', hcmat B', Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one, ← Matrix.mulVec_mulVec] at h3
        have h4 := congrArg
          (fun v => ((P⁻¹ : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ v) h3
        simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h4
        rwa [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h4
      have hmem := hg'cent (e B') ⟨B', hB', rfl⟩ hfixW
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hBk : B₀ ^ k = B' := e.injective (by rw [map_zpow]; exact hk)
      have ha'k : a' = a₀ ^ k := by
        apply mulAut_eq_of_forall ψ hker hperf
        intro l
        rw [← hB'ind, ← induced_zpow ha₀ k, ← hBk, map_zpow]
      rw [ha'k]
      exact Subgroup.zpow_mem_zpowers a₀ k
    · intro hmem j hj
      have hle : Subgroup.zpowers a₀ ≤ fixSub (ggFix a₀ : Set L') := by
        rw [Subgroup.zpowers_le]
        intro x hx
        exact hx
      exact hle hmem j (hJfix hj)

end CFSG.StandardType.TwoThree
