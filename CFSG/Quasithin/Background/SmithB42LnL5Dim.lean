module

public import CFSG.Quasithin.Background.SmithB42LnL5Out
public import CFSG.Quasithin.Background.SmithB42LnL5Rep
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Dim
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix
open CFSG.Assembly.LowTwoRank

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

noncomputable abbrev fL (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) : G5 →* MulAut V :=
  L.subtype.comp (phiOf e).symm.toMonoidHom

omit [Finite V] in
theorem fL_apply (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (g : G5) :
    fL e g = (((phiOf e).symm g : ↥L) : MulAut V) := rfl

omit [Finite V] in
theorem fL_injective (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) : Function.Injective (fL e) :=
  fun _ _ h => (phiOf e).symm.injective (Subtype.ext h)

omit [Finite V] in
theorem fL_mem (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (g : G5) : fL e g ∈ L :=
  ((phiOf e).symm g).2

omit [Finite V] in
theorem fL_phiOf (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {x : MulAut V} (hx : x ∈ L) :
    fL e (phiOf e ⟨x, hx⟩) = x := by
  rw [fL_apply, MulEquiv.symm_apply_apply]

omit [Finite V] in
theorem exists_fL_eq (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {x : MulAut V} (hx : x ∈ L) :
    ∃ g, fL e g = x :=
  ⟨phiOf e ⟨x, hx⟩, fL_phiOf e hx⟩

omit [Finite V] in
theorem card_comap_eq (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hAL : A ≤ L) :
    Nat.card (A.comap (fL e)) = Nat.card A := by
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨fL e g, g.2⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h' : fL e g = fL e g' := congrArg (fun z : ↥A => (z : MulAut V)) h
    exact Subtype.ext (fL_injective e h')
  · rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := exists_fL_eq e (hAL hx)
    exact ⟨⟨g, hx⟩, rfl⟩

theorem card_le_two_mul_comap (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hAG : A ≤ G) :
    Nat.card A ≤ 2 * Nat.card (A.comap (fL e)) := by
  classical
  by_cases hAL : A ≤ L
  · rw [card_comap_eq e hAL]
    omega
  · obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
    have ha₀L' : a₀⁻¹ ∉ L := fun h => ha₀L (by simpa using L.inv_mem h)
    have key : ∀ x : ↥A, (x : MulAut V) ∉ L → a₀⁻¹ * x ∈ L := fun x hx =>
      mul_mem_of_not_mem hHyp hZ e (G.inv_mem (hAG ha₀)) (hAG x.2) ha₀L' hx
    have hm1 : ∀ (x : ↥A) (hx : (x : MulAut V) ∈ L), phiOf e ⟨x, hx⟩ ∈ A.comap (fL e) :=
      fun x hx => by
        show fL e (phiOf e ⟨x, hx⟩) ∈ A
        rw [fL_phiOf]
        exact x.2
    have hm2 : ∀ (x : ↥A) (hx : (x : MulAut V) ∉ L),
        phiOf e ⟨a₀⁻¹ * x, key x hx⟩ ∈ A.comap (fL e) := fun x hx => by
      show fL e (phiOf e ⟨a₀⁻¹ * x, key x hx⟩) ∈ A
      rw [fL_phiOf]
      exact A.mul_mem (A.inv_mem ha₀) x.2
    let F : ↥A → ↥(A.comap (fL e)) × Bool := fun x =>
      if hx : (x : MulAut V) ∈ L then (⟨phiOf e ⟨x, hx⟩, hm1 x hx⟩, false)
      else (⟨phiOf e ⟨a₀⁻¹ * x, key x hx⟩, hm2 x hx⟩, true)
    have hF : Function.Injective F := by
      intro x y hxy
      by_cases hx : (x : MulAut V) ∈ L <;> by_cases hy : (y : MulAut V) ∈ L
      · simp only [F, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        have h1 := (phiOf e).injective
          (congrArg (fun z : ↥(A.comap (fL e)) => (z : G5)) hxy.1)
        exact Subtype.ext (congrArg (fun z : ↥L => (z : MulAut V)) h1)
      · simp [F, hx, hy] at hxy
      · simp [F, hx, hy] at hxy
      · simp only [F, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        have h1 := congrArg (fun z : ↥L => (z : MulAut V)) ((phiOf e).injective
          (congrArg (fun z : ↥(A.comap (fL e)) => (z : G5)) hxy.1))
        exact Subtype.ext (mul_left_cancel h1)
    have h := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
    linarith

theorem card_le_pow_of_gen (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hfixL : fixV L = ⊥) {k : ℕ}
    {y : G5} (gs : Fin k → G5)
    (hgen : Subgroup.closure (Set.range fun i => gs i * y * (gs i)⁻¹) = ⊤) {c : G5}
    {x : MulAut V} (hx : fL e (c⁻¹ * y * c) = x) :
    Nat.card V ≤ (fixV (Subgroup.zpowers x)).index ^ k := by
  set l : Fin k → MulAut V := fun i => fL e (gs i * c) with hl
  set B : Fin k → Subgroup (MulAut V) :=
    fun i => (Subgroup.zpowers x).map (MulAut.conj (l i)).toMonoidHom with hB
  have hconj : ∀ i, fL e (gs i * y * (gs i)⁻¹) = l i * x * (l i)⁻¹ := by
    intro i
    have e1 : gs i * y * (gs i)⁻¹ = (gs i * c) * (c⁻¹ * y * c) * (gs i * c)⁻¹ := by group
    rw [e1, map_mul, map_mul, map_inv, hx]
  have hle : Subgroup.closure (Set.range fun i => gs i * y * (gs i)⁻¹) ≤
      (⨆ i, B i).comap (fL e) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine Subgroup.mem_iSup_of_mem i ⟨x, Subgroup.mem_zpowers x, ?_⟩
    show (MulAut.conj (l i)) x = fL e (gs i * y * (gs i)⁻¹)
    rw [MulAut.conj_apply, hconj]
  rw [hgen] at hle
  have hX : L ≤ ⨆ i, B i := by
    intro z hz
    obtain ⟨g, rfl⟩ := exists_fL_eq e hz
    exact hle (Subgroup.mem_top g)
  have h := card_le_prod_index B hX hfixL
  have hidx : ∀ i, (fixV (B i)).index = (fixV (Subgroup.zpowers x)).index := fun i =>
    CFSG.QuasithinUnique.B42A57.index_fixV_conj _ _
  simp only [hidx, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem card_le_of_inv (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2)))
    (hfixL : fixV L = ⊥) {g : G5} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    Nat.card V ≤ (fixV (Subgroup.zpowers (fL e g))).index ^ 5 := by
  obtain ⟨c, hc | hc⟩ := exists_conj_t0_or_s0 hg2 hg1
  · have hx : fL e (c⁻¹ * t0 * c) = fL e g := by
      have : c⁻¹ * t0 * c = g := by rw [← hc]; group
      rw [this]
    exact card_le_pow_of_gen e hfixL gT closure_t0 hx
  · have hx : fL e (c⁻¹ * s0 * c) = fL e g := by
      have : c⁻¹ * s0 * c = g := by rw [← hc]; group
      rw [this]
    have h := card_le_pow_of_gen e hfixL gS closure_s0 hx
    have h1 : 1 ≤ (fixV (Subgroup.zpowers (fL e g))).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact h.trans (Nat.pow_le_pow_right h1 (by norm_num))

omit [Finite V] in
theorem fL_mem_of_mem {e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))} {b : G5} (hb : b ∈ A.comap (fL e)) :
    fL e b ∈ A := hb

theorem l5Model_of_center
    [Module (ZMod 2) (Additive V)]
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hρ : IsSimpleRep (repOf (phiOf e)))
    (hV20 : 2 ^ 20 ≤ Nat.card V) (hidx : (fixV A).index ≤ 16) {v : Fin 5 → ZMod 2}
    (hv0 : v ≠ 0) (hv : ∀ b ∈ A.comap (fL e), b ≠ 1 → ∃ ψ, IsTv b v ψ)
    (h16 : Nat.card (A.comap (fL e)) = 16) : L5Model (repOf (phiOf e)) := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  set gk : Fin 4 → G5 := fun k => (exists_conj_center hv0 k.castSucc).choose with hgk
  have hgkv : ∀ k, ((gk k : G5) : 𝕄) *ᵥ v = Pi.single k.castSucc 1 := fun k =>
    (exists_conj_center hv0 k.castSucc).choose_spec
  set B : Fin 4 → Subgroup (MulAut V) :=
    fun k => A.map (MulAut.conj (fL e (gk k))).toMonoidHom with hB
  have hX := index_fixV_le_prod B (le_refl (⨆ k, B k))
  have hidxB : ∀ k, (fixV (B k)).index = (fixV A).index := fun k =>
    CFSG.QuasithinUnique.B42A57.index_fixV_conj _ _
  simp only [hidxB, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hX
  have hX' : (fixV (⨆ k, B k)).index < Nat.card V := by
    calc (fixV (⨆ k, B k)).index ≤ (fixV A).index ^ 4 := hX
      _ ≤ 16 ^ 4 := Nat.pow_le_pow_left hidx 4
      _ < 2 ^ 20 := by norm_num
      _ ≤ Nat.card V := hV20
  have hne : fixV (⨆ k, B k) ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.index_bot] at hX'
    exact lt_irrefl _ hX'
  obtain ⟨⟨x, hxX⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  refine l5Model_of_fixed_point hρ (x := Additive.ofMul x) (fun h => hx1' (by simpa using h))
    fun i j hij hi4 => ?_
  obtain ⟨k, rfl⟩ : ∃ k : Fin 4, k.castSucc = i :=
    ⟨⟨i, by have := i.2; have : (i : ℕ) ≠ 4 := fun h => hi4 (Fin.ext h); omega⟩, rfl⟩
  obtain ⟨b, hb, hbk⟩ := eT_mem_conj_of_center hv0 hv h16 (hgkv k) hij
  have hmem : fL e (eT k.castSucc j hij) ∈ B k := by
    refine ⟨fL e b, fL_mem_of_mem hb, ?_⟩
    show (MulAut.conj (fL e (gk k))) (fL e b) = _
    rw [MulAut.conj_apply, ← hbk, map_mul, map_mul, map_inv]
  have hfix : (fL e (eT k.castSucc j hij)) x = x :=
    hxX _ (Subgroup.mem_iSup_of_mem k hmem)
  rw [repOf_apply, ← fL_apply, hfix]

theorem l5Model_of_axis
    [Module (ZMod 2) (Additive V)]
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hρ : IsSimpleRep (repOf (phiOf e)))
    (hV20 : 2 ^ 20 ≤ Nat.card V) (hidx : (fixV A).index ≤ 16) {ψ : Fin 5 → ZMod 2}
    (hψ0 : ψ ≠ 0) (hψ : ∀ b ∈ A.comap (fL e), b ≠ 1 → ∃ v, IsTv b v ψ)
    (h16 : Nat.card (A.comap (fL e)) = 16) : L5Model (repOf (phiOf e)) := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  set gk : Fin 4 → G5 := fun k => (exists_conj_axis hψ0 k.succ).choose with hgk
  have hgkψ : ∀ k, Pi.single k.succ 1 ᵥ* ((gk k : G5) : 𝕄) = ψ := fun k =>
    (exists_conj_axis hψ0 k.succ).choose_spec
  set B : Fin 4 → Subgroup (MulAut V) :=
    fun k => A.map (MulAut.conj (fL e (gk k))).toMonoidHom with hB
  have hX := index_fixV_le_prod B (le_refl (⨆ k, B k))
  have hidxB : ∀ k, (fixV (B k)).index = (fixV A).index := fun k =>
    CFSG.QuasithinUnique.B42A57.index_fixV_conj _ _
  simp only [hidxB, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hX
  have hX' : (fixV (⨆ k, B k)).index < Nat.card V := by
    calc (fixV (⨆ k, B k)).index ≤ (fixV A).index ^ 4 := hX
      _ ≤ 16 ^ 4 := Nat.pow_le_pow_left hidx 4
      _ < 2 ^ 20 := by norm_num
      _ ≤ Nat.card V := hV20
  have hne : fixV (⨆ k, B k) ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.index_bot] at hX'
    exact lt_irrefl _ hX'
  obtain ⟨⟨x, hxX⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  refine l5Model_of_fixed_axis hρ (x := Additive.ofMul x) (fun h => hx1' (by simpa using h))
    fun i j hij hj0 => ?_
  obtain ⟨k, rfl⟩ : ∃ k : Fin 4, k.succ = j := ⟨j.pred hj0, Fin.succ_pred j hj0⟩
  obtain ⟨b, hb, hbk⟩ := eT_mem_conj_of_axis hψ0 hψ h16 (hgkψ k) hij
  have hmem : fL e (eT i k.succ hij) ∈ B k := by
    refine ⟨fL e b, fL_mem_of_mem hb, ?_⟩
    show (MulAut.conj (fL e (gk k))) (fL e b) = _
    rw [MulAut.conj_apply, ← hbk, map_mul, map_mul, map_inv]
  have hfix : (fL e (eT i k.succ hij)) x = x :=
    hxX _ (Subgroup.mem_iSup_of_mem k hmem)
  rw [repOf_apply, ← fL_apply, hfix]

theorem eT01_mul_eT10_ne :
    eT 0 1 (by decide) * eT 1 0 (by decide) ≠ eT 1 0 (by decide) * eT 0 1 (by decide) := by
  intro h
  have h1 := congrArg (fun g : G5 => (g : 𝕄) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_eT] at h1
  revert h1
  decide

omit [Finite V] in
theorem exists_not_comm (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) : ∃ a b : ↥L, a * b ≠ b * a :=
  ⟨(phiOf e).symm (eT 0 1 (by decide)), (phiOf e).symm (eT 1 0 (by decide)), fun h =>
    eT01_mul_eT10_ne ((phiOf e).symm.injective (by rw [map_mul, map_mul, h]))⟩

omit [Finite V] in
theorem nontrivial_of_equiv (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  obtain ⟨a, b, hab⟩ := exists_not_comm e
  exact hab (Subtype.ext (MulEquiv.ext fun v => Subsingleton.elim _ _))

omit [Finite V] in
theorem comm_of_comap {e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))} (hA : IsElemAbelian2 A) :
    ∀ a ∈ A.comap (fL e), ∀ b ∈ A.comap (fL e), a * b = b * a := by
  intro a ha b hb
  apply fL_injective e
  rw [map_mul, map_mul]
  exact hA.1 _ ha _ hb

omit [Finite V] in
theorem sq_of_comap {e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))} (hA : IsElemAbelian2 A) :
    ∀ a ∈ A.comap (fL e), a * a = 1 := by
  intro a ha
  apply fL_injective e
  rw [map_mul, map_one, ← pow_two]
  exact hA.2 _ ha

theorem conjG5_fix (hHyp : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2)))
    (hA : IsElemAbelian2 A) {a : MulAut V} (haA : a ∈ A) (haG : a ∈ G) :
    ∀ b ∈ A.comap (fL e), conjG5 hHyp e haG b = b := by
  intro b hb
  apply (phiOf e).symm.injective
  apply Subtype.ext
  rw [conjG5_spec, ← fL_apply, hA.1 a haA _ hb, mul_inv_cancel_right]

theorem l5Model_of_offender
    [Module (ZMod 2) (Additive V)] (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (hA : IsFFStarOffender G A) :
    L5Model (repOf (phiOf e)) := by
  classical
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Nontrivial V := nontrivial_of_equiv e
  have hfixL : fixV L = ⊥ :=
    CFSG.QuasithinUnique.B42A57.fixV_eq_bot_of_irr hHyp.2.2.2 (exists_not_comm e)
  have hρ : IsSimpleRep (repOf (phiOf e)) :=
    isSimpleRep_repOf (phiOf e) (irr_of_isIrrSec hHyp.2.2.2)
  by_cases hd : Module.finrank (ZMod 2) (Additive V) ≤ 19
  · exact l5Model_of_finrank_le hρ hd
  push Not at hd
  have hV20 : 2 ^ 20 ≤ Nat.card V := by
    rw [card_eq_two_pow_finrank]
    exact Nat.pow_le_pow_right (by norm_num) hd
  have hidx : (fixV A).index ≤ Nat.card A := CFSG.QuasithinUnique.B42A57.index_fixV_le hA
  have hAG : A ≤ G := hA.1
  have hel : IsElemAbelian2 A := hA.2.2.1
  have hcS := comm_of_comap (e := e) hel
  have h2S := sq_of_comap (e := e) hel
  have hcardA := card_le_two_mul_comap hHyp hZ e hAG
  set S := A.comap (fL e) with hS
  have hidxx : ∀ s ∈ S, (fixV (Subgroup.zpowers (fL e s))).index ≤ Nat.card A := fun s hs =>
    (index_fixV_mono ((Subgroup.zpowers_le).2 (fL_mem_of_mem hs))).trans hidx
  have houter : ∀ a₀ ∈ A, a₀ ∉ L → ∃ P : GL (Fin 5) (ZMod 2), ∃ haG : a₀ ∈ G,
      (∀ x : G5, ((conjG5 hHyp e haG x : G5) : 𝕄) =
        (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)) ∧
      ∀ b ∈ S, conjG5 hHyp e haG b = b := by
    intro a₀ ha₀ ha₀L
    obtain ⟨P, hP⟩ := exists_conjG5_eq hHyp hZ e (hAG ha₀) ha₀L
    exact ⟨P, hAG ha₀, hP, conjG5_fix hHyp e hel ha₀ (hAG ha₀)⟩
  by_cases hJ2 : ∃ s ∈ S, ∃ c : G5, c * s * c⁻¹ = s0
  ·
    exfalso
    obtain ⟨s, hs, c, hc⟩ := hJ2
    have hA64 : Nat.card A ≤ 64 := by
      by_cases hAL : A ≤ L
      · rw [← card_comap_eq e hAL]
        exact card_le_of_elemAbelian hcS h2S
      · obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
        obtain ⟨P, haG, hP, hfix⟩ := houter a₀ ha₀ ha₀L
        have := card_le_32_of_fixed hP hcS h2S hfix
        omega
    have hx : fL e (c⁻¹ * s0 * c) = fL e s := by
      have : c⁻¹ * s0 * c = s := by rw [← hc]; group
      rw [this]
    have h := card_le_pow_of_gen e hfixL gS closure_s0 hx
    have h1 : (fixV (Subgroup.zpowers (fL e s))).index ^ 3 ≤ 64 ^ 3 :=
      Nat.pow_le_pow_left ((hidxx s hs).trans hA64) 3
    have : (64 : ℕ) ^ 3 < 2 ^ 20 := by norm_num
    omega
  have hT : ∀ s ∈ S, s ≠ 1 → ∃ v ψ, IsTv s v ψ := by
    intro s hs hs1
    obtain ⟨c, hc | hc⟩ := exists_conj_t0_or_s0 (h2S s hs) hs1
    · have h := isTv_conj_t0 c⁻¹
      have e1 : c⁻¹ * t0 * c⁻¹⁻¹ = s := by rw [← hc]; group
      rw [e1] at h
      exact ⟨_, _, h⟩
    · exact absurd ⟨s, hs, c, hc⟩ hJ2
  by_cases hAL : A ≤ L
  ·
    have hSA : Nat.card S = Nat.card A := card_comap_eq e hAL
    have hS1 : ∃ s ∈ S, s ≠ 1 := by
      obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA.2.1
      obtain ⟨g, rfl⟩ := exists_fL_eq e (hAL ha)
      refine ⟨g, ha, fun h => ha1 ?_⟩
      apply Subtype.ext
      show fL e g = (1 : MulAut V)
      rw [h, map_one]
    obtain ⟨s₁, hs₁, hs₁1⟩ := hS1
    have hsmall : Nat.card A ≤ 8 → False := by
      intro h8
      have h := card_le_of_inv e hfixL (h2S s₁ hs₁) hs₁1
      have h1 : (fixV (Subgroup.zpowers (fL e s₁))).index ^ 5 ≤ 8 ^ 5 :=
        Nat.pow_le_pow_left ((hidxx s₁ hs₁).trans h8) 5
      have : (8 : ℕ) ^ 5 < 2 ^ 20 := by norm_num
      omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq S h2S).exists_card_eq
    obtain hcen | hax := common_center_or_axis hcS h2S hT
    · obtain ⟨v, hv⟩ := hcen
      have hv0 : v ≠ 0 := by
        obtain ⟨ψ, hψ⟩ := hv s₁ hs₁ hs₁1
        exact hψ.2.1
      have h16 := (card_le_of_center hv0 hv).1
      by_cases h16' : Nat.card S = 16
      · exact l5Model_of_center e hρ hV20 (hidx.trans (by omega)) hv0 hv h16'
      · exfalso
        apply hsmall
        rw [← hSA, hk] at *
        have : k ≤ 3 := by
          by_contra hk3
          have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
          _ = 8 := by norm_num
    · obtain ⟨ψ, hψ⟩ := hax
      have hψ0 : ψ ≠ 0 := by
        obtain ⟨v, hv⟩ := hψ s₁ hs₁ hs₁1
        exact hv.2.2.1
      have h16 := (card_le_of_axis hψ0 hψ).1
      by_cases h16' : Nat.card S = 16
      · exact l5Model_of_axis e hρ hV20 (hidx.trans (by omega)) hψ0 hψ h16'
      · exfalso
        apply hsmall
        rw [← hSA, hk] at *
        have : k ≤ 3 := by
          by_contra hk3
          have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
          _ = 8 := by norm_num
  ·
    exfalso
    obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
    obtain ⟨P, haG, hP, hfix⟩ := houter a₀ ha₀ ha₀L
    by_cases hS1 : ∃ s ∈ S, s ≠ 1
    · obtain ⟨s₁, hs₁, hs₁1⟩ := hS1
      have hS2 : Nat.card S ≤ 2 := by
        obtain hcen | hax := common_center_or_axis hcS h2S hT
        · obtain ⟨v, hv⟩ := hcen
          exact card_le_two_of_center hP hfix hv
        · obtain ⟨ψ, hψ⟩ := hax
          exact card_le_two_of_axis hP hfix hψ
      have h := card_le_of_inv e hfixL (h2S s₁ hs₁) hs₁1
      have h1 : (fixV (Subgroup.zpowers (fL e s₁))).index ^ 5 ≤ 4 ^ 5 :=
        Nat.pow_le_pow_left ((hidxx s₁ hs₁).trans (by omega)) 5
      have : (4 : ℕ) ^ 5 < 2 ^ 20 := by norm_num
      omega
    ·
      push Not at hS1
      have hS1' : Nat.card S = 1 := by
        rw [Subgroup.card_eq_one, eq_bot_iff]
        intro s hs
        rw [Subgroup.mem_bot]
        exact hS1 s hs
      have hA2 : Nat.card A ≤ 2 := by omega
      have ha₀2 : a₀ * a₀ = 1 := by rw [← pow_two]; exact hel.2 a₀ ha₀
      have hPs := transpose_P hHyp e haG ha₀2 hP
      obtain ⟨γ, hγ2, hx1, hx2⟩ := exists_conj_mul_inv hPs hP
      set γ' := fL e γ with hγ'
      have hγ'inv : γ'⁻¹ = γ' := by
        rw [hγ', ← map_inv, inv_eq_of_mul_eq_one_right hγ2]
      have ha₀inv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀2
      have hxeq : fL e (conjG5 hHyp e haG γ * γ) = a₀ * (γ' * a₀ * γ'⁻¹) := by
        rw [map_mul, fL_apply, conjG5_spec, ← fL_apply, ← hγ', hγ'inv, ha₀inv]
        group
      set B : Fin 2 → Subgroup (MulAut V) :=
        ![Subgroup.zpowers a₀, (Subgroup.zpowers a₀).map (MulAut.conj γ').toMonoidHom] with hB
      have hle : Subgroup.zpowers (fL e (conjG5 hHyp e haG γ * γ)) ≤ ⨆ i, B i := by
        rw [Subgroup.zpowers_le, hxeq]
        refine Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem 0 (Subgroup.mem_zpowers a₀))
          (Subgroup.mem_iSup_of_mem 1 ⟨a₀, Subgroup.mem_zpowers a₀, ?_⟩)
        show (MulAut.conj γ') a₀ = _
        rw [MulAut.conj_apply]
      have h1 := index_fixV_le_prod B hle
      rw [Fin.prod_univ_two] at h1
      have hB0 : (fixV (B 0)).index ≤ 2 :=
        (index_fixV_mono ((Subgroup.zpowers_le).2 ha₀)).trans (hidx.trans hA2)
      have hB1 : (fixV (B 1)).index = (fixV (B 0)).index :=
        CFSG.QuasithinUnique.B42A57.index_fixV_conj _ _
      have h2 := card_le_of_inv e hfixL hx2 hx1
      have h3 : (fixV (Subgroup.zpowers (fL e (conjG5 hHyp e haG γ * γ)))).index ≤ 4 := by
        rw [hB1] at h1
        calc _ ≤ (fixV (B 0)).index * (fixV (B 0)).index := h1
          _ ≤ 2 * 2 := Nat.mul_le_mul hB0 hB0
          _ = 4 := by norm_num
      have h4 := Nat.pow_le_pow_left h3 5
      have : (4 : ℕ) ^ 5 < 2 ^ 20 := by norm_num
      omega

end CFSG.Quasithin.B42Ln
