module

public import CFSG.Quasithin.Background.ONanE68LieCyc

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6
open scoped commutatorElement

section Regular

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_free_card {X W : Subgroup G}
    (hXW : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hfree : ∀ w ∈ W, w ≠ 1 → ∀ x ∈ X, x * w * x⁻¹ = w → x = 1)
    (hcard : Nat.card ↥X + 1 = Nat.card ↥W) :
    ∀ v ∈ W, v ≠ 1 → ∀ w ∈ W, w ≠ 1 → ∃ x ∈ X, x * v * x⁻¹ = w := by
  classical
  intro v hv hv1 w hw hw1
  let S : Set ↥W := {a | a ≠ 1}
  have hS : Nat.card ↥S = Nat.card ↥X := by
    have h1 : Nat.card ↥S = Nat.card ↥W - 1 := by
      have : S = ((Set.univ : Set ↥W) \ {1}) := by
        ext a; simp [S]
      rw [this, Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem (Set.mem_univ _),
        Set.ncard_univ]
    omega
  let f : ↥X → ↥S := fun x => ⟨⟨(x : G) * v * (x : G)⁻¹, hXW x x.2 v hv⟩, by
    intro h
    have h' : (x : G) * v * (x : G)⁻¹ = 1 := congrArg Subtype.val h
    apply hv1
    have := congrArg (fun t => (x : G)⁻¹ * t * (x : G)) h'
    simpa [mul_assoc] using this⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (x : G) * v * (x : G)⁻¹ = (y : G) * v * (y : G)⁻¹ :=
      congrArg (fun a : ↥S => ((a : ↥W) : G)) hxy
    have h2 : ((y : G)⁻¹ * x) * v * ((y : G)⁻¹ * x)⁻¹ = v := by
      have := congrArg (fun t => (y : G)⁻¹ * t * (y : G)) h1
      simp only [mul_assoc, mul_inv_rev] at this ⊢
      simpa [mul_assoc] using this
    have h3 : (y : G)⁻¹ * x = 1 := hfree v hv hv1 _ (X.mul_mem (X.inv_mem y.2) x.2) h2
    exact Subtype.ext (inv_mul_eq_one.1 h3).symm
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (le_of_eq hS)
  obtain ⟨x, hx⟩ := hbij.2 ⟨⟨w, hw⟩, fun h => hw1 (congrArg Subtype.val h)⟩
  refine ⟨x, x.2, ?_⟩
  exact congrArg (fun a : ↥S => ((a : ↥W) : G)) hx

end Regular


section Clause

variable {G : Type} [Group G] [Finite G] {T M V U L X : Subgroup G}

theorem commutator_le_of_normalizes (hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G))
    (hXL : X ≤ L) : ⁅V, X⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro v hv x hx
  rw [commutatorElement_def]
  exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hVN v hv) x).1 (hXL hx)) (L.inv_mem (hXL hx))

theorem clause_four (h : HypE61 T M V) (hsup : U ⊔ ⁅V, X⁆ = V)
    (hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G)) (hXL : X ≤ L) :
    Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (L : Set G) ≤
      M ⊓ Subgroup.centralizer (V : Set G) := by
  have hVXL := commutator_le_of_normalizes hVN hXL
  have h1 : Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.le_centralizer_iff, ← hsup]
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.1 inf_le_left
    · exact Subgroup.le_centralizer_iff.1 (inf_le_right.trans (Subgroup.centralizer_le hVXL))
  exact le_inf (h1.trans h.centralizer_le) h1


theorem clause_two (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) (hn : 1 < E3.mQuot V U)
    (hXLM : X ≤ L ⊓ M) (hLH : L ≤ Subgroup.centralizer (U : Set G))
    (hXcyc : IsCyclic ↥X) (hXcard : Nat.card ↥X = 2 ^ E3.mQuot V U - 1)
    (hautX : autI h.isElemAbelian X = autI h.isElemAbelian (L ⊓ M))
    (hcycLM : IsCyclic ↥(autI h.isElemAbelian (L ⊓ M)))
    (hcardLM : Nat.card ↥(autI h.isElemAbelian (L ⊓ M)) = 2 ^ E3.mQuot V U - 1)
    (hNL : ∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (U : Set G) →
      g ∈ Subgroup.normalizer (L : Set G)) :
    U ⊓ ⁅V, X⁆ = ⊥ ∧ U ⊔ ⁅V, X⁆ = V ∧ X ≤ L ⊓ M ∧ IsCyclic ↥X ∧
      Nat.card ↥X = 2 ^ E3.mQuot V U - 1 ∧ autI h.isElemAbelian X ≠ ⊥ ∧
      (∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ x ∈ X, x * v * x⁻¹ = v → x ∈ Subgroup.centralizer (V : Set G)) ∧
      (∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ w ∈ ⁅V, X⁆, w ≠ 1 → ∃ x ∈ X, x * v * x⁻¹ = w) ∧
      autI h.isElemAbelian (M ⊓ Subgroup.normalizer (U : Set G)) ≤
        Subgroup.normalizer (autI h.isElemAbelian X :
          Set (MulAut (IntMod V h.isElemAbelian))) ∧
      autI h.isElemAbelian X ≤ autI h.isElemAbelian (M ⊓ Subgroup.normalizer (U : Set G)) := by
  classical
  have hV := h.isElemAbelian
  have hUV : U ≤ V := hU.1
  have hXH : X ≤ Subgroup.centralizer (U : Set G) := fun x hx => hLH (hXLM hx).1
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    (e6_5_three h hU).2 ⟨hXH hx, (hXLM hx).2⟩
  have hcycX : IsCyclic ↥(autI hV X) := hautX ▸ hcycLM
  have hcardX : Nat.card ↥(autI hV X) = 2 ^ E3.mQuot V U - 1 := hautX ▸ hcardLM
  obtain ⟨hinf, hsup, hfree⟩ := singer_autI hV hUV hn hXH hXN hcycX hcardX
  have h4 : 4 ≤ 2 ^ E3.mQuot V U :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ E3.mQuot V U := Nat.pow_le_pow_right (by norm_num) hn
  have hXC : X ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
    have h1 := card_autI_mul_card_inf hV hXN
    rw [hcardX, hXcard] at h1
    have hpos : 0 < 2 ^ E3.mQuot V U - 1 := by omega
    have h2 : Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) = 1 := by
      have : (2 ^ E3.mQuot V U - 1) * Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) =
          (2 ^ E3.mQuot V U - 1) * 1 := by rw [mul_one]; exact h1
      exact Nat.eq_of_mul_eq_mul_left hpos this
    exact Subgroup.eq_bot_of_card_eq _ h2
  have hXW : ∀ x ∈ X, ∀ w ∈ ⁅V, X⁆, x * w * x⁻¹ ∈ ⁅V, X⁆ := by
    intro x hx w hw
    have hmap : (⁅V, X⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom ≤ ⁅V, X⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨v, hv, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 (hXN hx) v).1 hv
      · rintro _ ⟨y, hy, rfl⟩
        exact X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
    exact hmap ⟨w, hw, rfl⟩
  have hfree' : ∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ x ∈ X, x * v * x⁻¹ = v →
      x ∈ Subgroup.centralizer (V : Set G) := by
    intro v hv hv1 x hx hxv
    refine hfree v hv hv1 x hx ?_
    calc x * v = (x * v * x⁻¹) * x := by group
      _ = v * x := by rw [hxv]
  have hfree1 : ∀ w ∈ ⁅V, X⁆, w ≠ 1 → ∀ x ∈ X, x * w * x⁻¹ = w → x = 1 := by
    intro w hw hw1 x hx hxw
    have hxC := hfree' w hw hw1 x hx hxw
    have : x ∈ X ⊓ Subgroup.centralizer (V : Set G) := ⟨hx, hxC⟩
    rw [hXC, Subgroup.mem_bot] at this
    exact this
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV ha hb
  have hWV : ⁅V, X⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def]
    have h1 : x * v⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hXN hx) v⁻¹).1 (V.inv_mem hv)
    have : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
    rw [this]
    exact V.mul_mem hv h1
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hmW : E3.mQuot ⁅V, X⁆ ⊥ = E3.mQuot V U :=
    E68Proof.mQuot_bot_eq_of_decomp hV2 hUV hWV hVc hinf hsup rfl
  have hWcard : Nat.card ↥⁅V, X⁆ = 2 ^ E3.mQuot V U := by
    have := E3.relIndex_eq_two_pow (hV2.to_le hWV) (⊥ : Subgroup G)
    rw [Subgroup.relIndex_bot_left, hmW] at this
    exact this
  have htrans := exists_conj_of_free_card hXW hfree1 (by omega)
  refine ⟨hinf, hsup, hXLM, hXcyc, hXcard, ?_, hfree', htrans, ?_, ?_⟩
  · intro h0
    rw [h0, Subgroup.card_bot] at hcardX
    omega
  · intro φ hφ
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 hφ
    refine E68Proof.mem_normalizer_of_conj_le (fun ψ hψ => ?_)
    rw [hautX] at hψ ⊢
    obtain ⟨y, hyK, rfl⟩ := (mem_autI hV).1 hψ
    have hgL : (g : G) ∈ Subgroup.normalizer (L : Set G) := hNL g ⟨hgK.1, g.2⟩ hgK.2
    have hgy : (g : G) * y * (g : G)⁻¹ ∈ L ⊓ M :=
      ⟨(Subgroup.mem_normalizer_iff.1 hgL y).1 hyK.1,
        M.mul_mem (M.mul_mem hgK.1 hyK.2) (M.inv_mem hgK.1)⟩
    have hyN : (y : G) ∈ Subgroup.normalizer (V : Set G) := y.2
    have hgyN : (g : G) * y * (g : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hyN) (Subgroup.inv_mem _ g.2)
    have := convI_mem_autI hV hgy hgyN
    convert this using 1
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · exact autI_mono hV (fun x hx => ⟨(hXLM hx).2, Subgroup.centralizer_le_normalizer _ (hXH hx)⟩)

end Clause

end CFSG.Quasithin.RonanE611
