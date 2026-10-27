module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoFrame

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace ChoiceTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_frame (hK : Nat.card K = 2) {g : K[X]} [Fact (Irreducible g)]
    (hgd : g ∣ cyclotomic 3 K) {E : Subgroup (StatedSp n K)} (hE3 : ∀ Y ∈ E, Y ^ 3 = 1)
    (hEc : ∀ Y ∈ E, ∀ Y' ∈ E, Y * Y' = Y' * Y)
    (hEsc : ∀ Z : StatedSp n K, (∀ Y ∈ E, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ E) :
    Nonempty (SpFrame K n (AdjoinRoot.root g) E) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  set ζ := AdjoinRoot.root g with hζdef
  have hζo : IsPrimitiveRoot ζ 3 := NSFrame.root_isPrimitiveRoot hp hpK hgd
  have hζ3 : ζ ^ 3 = 1 := hζo.pow_eq_one
  set S : Set (Module.End K (Fin n ⊕ Fin n → K)) := {M | ∃ Y ∈ E, spEnd Y = M} with hS
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨Y, hY, rfl⟩ _ ⟨Y', hY', rfl⟩
    change spEnd Y * spEnd Y' = spEnd Y' * spEnd Y
    rw [← spEnd_mul, ← spEnd_mul, hEc Y hY Y' hY']
  have hSp : ∀ x ∈ S, x ^ 3 = 1 := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [← spEnd_pow, hE3 Y hY, spEnd_one]
  have hSB : ∀ x ∈ S, ∀ u w, spForm n K (x u) (x w) = spForm n K u w := by
    rintro _ ⟨Y, -, rfl⟩ u w
    exact mem_sesqUnitaryGroup.mp (spLin_mem Y) u w
  obtain ⟨s, κ, _, Φ₀, β, hβ, hact, hdec⟩ := SpNS.exists_nframe hp hp2 hpK hgd
    (SpNS.rootPB_dim_eq_two hp hp2 hpK hgd hpq) (SpNS.aeval_root_pow_pred hp hpK hgd hpq)
    (spForm_isAlt (r := n) (K := K)) spForm_nondegenerate S hSc hSp hSB
  have hdim := SpNS.rootPB_dim_eq_two hp hp2 hpK hgd hpq
  set bL : Basis (Fin 2) K (AdjoinRoot g) := (CoordSL.rootPB g).basis.reindex (finCongr hdim)
  have hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v := fun u v => by
    have h1 := SpNS.bilin_apply_det bL hβ (Algebra.lmul K (AdjoinRoot g) ζ) u v
    rw [← Algebra.norm_apply, SpNS.norm_root_eq_one hp hp2 hpK hgd hpq, one_mul] at h1
    exact h1
  have hσβ : ∀ u v, β (SpNS.frobL K g u) (SpNS.frobL K g v) = β u v := fun u v => by
    have h1 := SpNS.bilin_apply_det bL hβ (SpNS.frobL K g : AdjoinRoot g →ₗ[K] AdjoinRoot g) u v
    rw [SpNS.det_frobL hp hp2 hpK hgd hpq, one_mul] at h1
    exact h1
  have hσζ : ∀ u, SpNS.frobL K g (ζ * u) = ζ ^ 2 * SpNS.frobL K g u := fun u => by
    rw [SpNS.frobL_root_mul hp hpK hgd hpq u]
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcardL : Fintype.card (AdjoinRoot g) = Fintype.card K ^ 2 := by
    rw [Module.card_fintype (CoordSL.rootPB g).basis, Fintype.card_fin, hdim]
  have hσσ : ∀ u, SpNS.frobL K g (SpNS.frobL K g u) = u := fun u => by
    rw [SpNS.frobL_apply, SpNS.frobL_apply, ← pow_mul, ← sq, ← hcardL, FiniteField.pow_card]
  have hactE : ∀ Y ∈ E, ∃ k : Fin s → ℕ, ∀ d w,
      spEnd Y (Φ₀ (d, w)) = Φ₀ (fun i => ζ ^ k i * d i, w) := fun Y hY => hact _ ⟨Y, hY, rfl⟩
  have hκ : IsEmpty κ := by
    by_contra hne
    rw [not_isEmpty_iff] at hne
    obtain ⟨k₀⟩ := hne
    set B₀ : LinearMap.BilinForm K (κ → K) :=
      (spForm n K).compl₁₂ (Φ₀.toLinearMap ∘ₗ LinearMap.inr K (Fin s → AdjoinRoot g) (κ → K))
        (Φ₀.toLinearMap ∘ₗ LinearMap.inr K (Fin s → AdjoinRoot g) (κ → K)) with hB₀
    have hB₀apply : ∀ w w', B₀ w w' = spForm n K (Φ₀ (0, w)) (Φ₀ (0, w')) := fun _ _ => rfl
    have hB₀alt : B₀.IsAlt := fun w => spForm_isAlt _
    set u : κ → K := Pi.single k₀ 1 with hu
    have hu0 : Φ₀ (0, u) ≠ 0 := by
      intro h0
      have h1 := Φ₀.injective (h0.trans (map_zero Φ₀).symm)
      have h2 := congrFun (congrArg Prod.snd h1) k₀
      simp [hu] at h2
    obtain ⟨y, hy⟩ : ∃ y, spForm n K (Φ₀ (0, u)) y ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu0 (spForm_nondegenerate.1 _ hall)
    obtain ⟨⟨d', w'⟩, rfl⟩ := Φ₀.surjective y
    rw [hdec] at hy
    simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply, Finset.sum_const_zero,
      zero_add] at hy
    have hc : B₀ u w' ≠ 0 := hy
    set v : κ → K := (B₀ u w')⁻¹ • w' with hv
    have huv : B₀ u v = 1 := by rw [hv, map_smul, smul_eq_mul, inv_mul_cancel₀ hc]
    set T : (κ → K) ≃ₗ[K] (κ → K) := LinearEquiv.ofLinearMap (cyc3 B₀ u v)
      (cyc3 B₀ u v ∘ₗ cyc3 B₀ u v) (LinearMap.ext fun w => cyc3_cube hB₀alt huv w)
      (LinearMap.ext fun w => cyc3_cube hB₀alt huv w) with hT
    set M := (LinearEquiv.refl K (Fin s → AdjoinRoot g)).prodCongr T with hM
    have hMapp : ∀ d w, M (d, w) = (d, cyc3 B₀ u v w) := fun _ _ => rfl
    have hMiso : ∀ x y, spForm n K (Φ₀ (M x)) (Φ₀ (M y)) = spForm n K (Φ₀ x) (Φ₀ y) := by
      rintro ⟨d, w⟩ ⟨d', w'⟩
      rw [hMapp, hMapp, hdec d d' (cyc3 B₀ u v w) (cyc3 B₀ u v w'), hdec d d' w w',
        ← hB₀apply, ← hB₀apply, cyc3_isom hB₀alt huv w w']
    obtain ⟨Y, hY⟩ := exists_actsAs (Φ := Φ₀) M hMiso
    have hYc : ∀ Z ∈ E, Y * Z = Z * Y := by
      intro Z hZ
      obtain ⟨k, hk⟩ := hactE Z hZ
      have hZa : ActsAs Φ₀ Z (fun x => (fun i => ζ ^ k i * x.1 i, x.2)) := fun x => hk x.1 x.2
      exact hY.commute hZa fun x => rfl
    have hY3 : Y ^ 3 = 1 := by
      refine (hY.pow 3).eq (ActsAs.one.congr fun x => ?_)
      obtain ⟨d, w⟩ := x
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, hMapp]
      rw [cyc3_cube hB₀alt huv]
    obtain ⟨k, hk⟩ := hactE Y (hEsc Y hYc hY3)
    have h1 := (hY (0, u)).symm.trans (hk 0 u)
    rw [hMapp] at h1
    have h2 := congrArg Prod.snd (Φ₀.injective h1)
    exact cyc3_ne hB₀alt huv h2
  have : Unique (κ → K) := Pi.uniqueOfIsEmpty _
  set e₀ : (Fin s → AdjoinRoot g) ≃ₗ[K] ((Fin s → AdjoinRoot g) × (κ → K)) :=
    LinearEquiv.ofLinearMap (LinearMap.inl K _ _) (LinearMap.fst K _ _)
      (LinearMap.ext fun x => Prod.ext rfl (Subsingleton.elim _ _)) (LinearMap.ext fun _ => rfl)
    with he₀
  set Φ := e₀.trans Φ₀ with hΦ
  have hΦapp : ∀ d, Φ d = Φ₀ (d, 0) := fun _ => rfl
  have hform : ∀ d d', spForm n K (Φ d) (Φ d') = ∑ i, β (d i) (d' i) := by
    intro d d'
    rw [hΦapp, hΦapp, hdec, Prod.mk_zero_zero, map_zero, map_zero, add_zero]
  have hiso : ∀ f : Fin s → ZMod 3, ∀ d d', spForm n K (Φ (torLE K hζ3 f d))
      (Φ (torLE K hζ3 f d')) = spForm n K (Φ d) (Φ d') := by
    intro f d d'
    rw [hform, hform]
    exact Finset.sum_congr rfl fun i _ => bilin_pow_mul hζβ _ _ _
  choose tor htor using fun f : Fin s → ZMod 3 => exists_actsAs (Φ := Φ) (torLE K hζ3 f) (hiso f)
  have htor' : ∀ f, ActsAs Φ (tor f) (torE ζ f) := htor
  have hactΦ : ∀ Y ∈ E, ∃ k : Fin s → ℕ, ActsAs Φ Y (fun d i => ζ ^ k i * d i) := by
    intro Y hY
    obtain ⟨k, hk⟩ := hactE Y hY
    exact ⟨k, fun d => (hk d 0)⟩
  have htorE : ∀ f, tor f ∈ E := by
    intro f
    refine hEsc _ (fun Z hZ => ?_) ?_
    · obtain ⟨k, hk⟩ := hactΦ Z hZ
      exact (htor' f).commute hk fun d => funext fun i => by
        simp only [torE_apply]
        ring
    · refine ((htor' f).pow 3).eq (ActsAs.one.congr fun d => ?_)
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      rw [← torE_add hζ3, ← torE_add hζ3]
      have h3 : f + f + f = 0 := funext fun i => by
        simp only [Pi.add_apply, Pi.zero_apply]
        calc f i + f i + f i = 3 * f i := by ring
          _ = 0 := by rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
      rw [h3, torE_zero]
  have hEtor : ∀ Y ∈ E, ∃ f, tor f = Y := by
    intro Y hY
    obtain ⟨k, hk⟩ := hactΦ Y hY
    refine ⟨fun i => (k i : ZMod 3), (htor' _).eq (hk.congr fun d => funext fun i => ?_)⟩
    rw [torE_apply, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ3]
  exact ⟨⟨s, Φ, β, SpNS.frobL K g, hform, hζβ, hσζ, hσσ, hσβ, tor, htor', htorE, hEtor⟩⟩

end ChoiceTwo

end CFSG.StandardType
