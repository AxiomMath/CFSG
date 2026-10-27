module

public import CFSG.Quasithin.Vol2.Ch5ModulesNat
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Lift
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Semi

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Offender
open scoped IsMulCommutative MatrixGroups Matrix Pointwise
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL)

variable {G : Type} [Group G]

namespace Setting516

variable {T L D R : Subgroup G}

theorem inf_centralizer_le_of_nat [Finite G] (hS : Setting516 T L D R) {W : Subgroup G} {n : ℕ}
    (hW : IsNatModCh5 L W n) :
    L ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (R : Set G) := by
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hW.1
  have hnorm : L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) :
      Set G) := fun _ hl => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hl, F7.normalizer_le_normalizer_centralizer _ (hLW hl)⟩
  rcases hS.simple _ inf_le_left hnorm with hle | heq
  · exact hle.trans hS.pCoreOf_le
  · exact absurd (heq.symm.le.trans inf_le_right) hW.not_le_centralizer

theorem exists_resIso [Finite G] (hS : Setting516 T L D R) {W : Subgroup G} {n : ℕ}
    (hWR : W ≤ R) (hW : IsNatModCh5 L W n) :
    ∃ r : ↥(autOn L R) ≃* ↥(autOn L W), ∀ (a : ↥(autOn L R)) (w : ↥W),
      ((((r a : ↥(autOn L W)) : MulAut ↥W) w : ↥W) : G) =
        (((a : MulAut ↥R) ⟨w, hWR w.2⟩ : ↥R) : G) := by
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hS.reduced.2.1
  obtain ⟨r, hrs, hr⟩ := exists_autOn_restrict hLR hW.1 hWR
  have hinj : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨l, hlL, hla⟩ := mem_autOn_iff.mp a.2
    have hlW : (l : G) ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := hr a ⟨w, hw⟩
      rw [ha, ← hla, conjAct_apply_coe] at h1
      have h2 : (w : G) = l * w * (l : G)⁻¹ := h1
      calc w * (l : G) = (l * w * (l : G)⁻¹) * l := by rw [← h2]
        _ = l * w := by group
    have hlR := hS.inf_centralizer_le_of_nat hW ⟨hlL, hlW⟩
    apply Subtype.ext
    rw [← hla]
    ext w
    rw [conjAct_apply_coe]
    show (l : G) * w * (l : G)⁻¹ = w
    rw [← Subgroup.mem_centralizer_iff.mp hlR w w.2, mul_inv_cancel_right]
  exact ⟨MulEquiv.ofBijective r ⟨hinj, hrs⟩, hr⟩

theorem resIso_autHom {W : Subgroup G} (hWR : W ≤ R)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    {r : ↥(autOn L R) ≃* ↥(autOn L W)}
    (hr : ∀ (a : ↥(autOn L R)) (w : ↥W), ((((r a : ↥(autOn L W)) : MulAut ↥W) w : ↥W) : G) =
      (((a : MulAut ↥R) ⟨w, hWR w.2⟩ : ↥R) : G)) (l : ↥L) :
    r (autHom hLR l) = autHom hLW l := by
  apply Subtype.ext
  ext w
  rw [hr, autHom_apply_coe, autHom_apply_coe]

theorem sylow_resIso [Finite G] (hS : Setting516 T L D R) {W S : Subgroup G} {n : ℕ}
    (hWR : W ≤ R) (hW : IsNatModCh5 L W n) (hSL : S ≤ L) {F : Type} [Field F]
    {r : ↥(autOn L R) ≃* ↥(autOn L W)}
    (hr : ∀ (a : ↥(autOn L R)) (w : ↥W), ((((r a : ↥(autOn L W)) : MulAut ↥W) w : ↥W) : G) =
      (((a : MulAut ↥R) ⟨w, hWR w.2⟩ : ↥R) : G))
    {ψ : ↥(autOn L W) ≃* SL(2, F)}
    (hP : ∀ x : ↥(autOn L W), (x : MulAut ↥W) ∈ autOn S W ↔ ∃ b : F, ψ x = unipSL b)
    (a : ↥(autOn L R)) :
    (a : MulAut ↥R) ∈ autOn S R ↔ ∃ b : F, (r.trans ψ) a = unipSL b := by
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hS.reduced.2.1
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hW.1
  rw [MulEquiv.trans_apply, ← hP]
  obtain ⟨l, hlL, hla⟩ := mem_autOn_iff.mp a.2
  have hra : r a = autHom hLW ⟨l, hlL⟩ := by
    have : a = autHom hLR ⟨l, hlL⟩ := Subtype.ext hla.symm
    rw [this, resIso_autHom hWR hLR hLW hr]
  constructor
  · intro ha
    obtain ⟨s, hs, hsa⟩ := mem_autOn_iff.mp ha
    refine mem_autOn_iff.mpr ⟨⟨s, hLW (hSL hs)⟩, hs, ?_⟩
    ext w
    rw [conjAct_apply_coe, hr, ← hsa, conjAct_apply_coe]
  · intro ha
    obtain ⟨s, hs, hsa⟩ := mem_autOn_iff.mp ha
    have hW' : (s : G)⁻¹ * l ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) hsa
      simp only [conjAct_apply_coe] at h1
      rw [hra, autHom_apply_coe] at h1
      have h2 : (l : G) * w = s * w * (s : G)⁻¹ * l := by
        rw [h1]
        group
      calc w * ((s : G)⁻¹ * l) = (s : G)⁻¹ * (s * w * (s : G)⁻¹ * l) := by group
        _ = (s : G)⁻¹ * l * w := by rw [← h2]; group
    have hsL : (s : G) ∈ L := hSL hs
    have hR' := hS.inf_centralizer_le_of_nat hW
      (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hsL) hlL, hW'⟩)
    refine mem_autOn_iff.mpr ⟨⟨s, hLR hsL⟩, hs, ?_⟩
    rw [← hla]
    ext w
    rw [conjAct_apply_coe, conjAct_apply_coe]
    have h3 := Subgroup.mem_centralizer_iff.mp hR' w w.2
    show (s : G) * w * (s : G)⁻¹ = l * w * (l : G)⁻¹
    calc (s : G) * w * (s : G)⁻¹ = s * (w * ((s : G)⁻¹ * l)) * (l : G)⁻¹ := by group
      _ = s * (((s : G)⁻¹ * l) * w) * (l : G)⁻¹ := by rw [h3]
      _ = l * w * (l : G)⁻¹ := by group

end Setting516

theorem IsNatModCh5.exists_qcoord [Finite G] {L W S : Subgroup G} {n : ℕ}
    (h : IsNatModCh5 L W n) (hS : IsSylowTwoOf S L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      ∃ (ψ : ↥(autOn L W) ≃* SL(2, F)) (Y : ↥W ≃* Multiplicative (Fin 2 → F)),
        QCoord L W S F ψ Y.toMonoidHom := by
  obtain ⟨F, _, _, _, hF, ψ, Y, hint, hP⟩ := h.exists_sylowCoord hS
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, ψ, Y,
    ⟨h.1, Y.surjective, fun x => ?_, hint, hP⟩⟩
  constructor
  · intro hx
    have : x = 1 := Y.injective (hx.trans (map_one Y).symm)
    rw [this]
    exact Subgroup.one_mem _
  · intro hx
    obtain ⟨l, hlL, hla⟩ := mem_autOn_iff.mp (ψ.symm (sl2Ord3 F)).2
    have hfix : ((ψ.symm (sl2Ord3 F) : ↥(autOn L W)) : MulAut ↥W) x = x := by
      apply Subtype.ext
      rw [← hla, conjAct_apply_coe, Subgroup.mem_centralizer_iff.mp hx l hlL,
        mul_inv_cancel_right]
    have h1 := hint (ψ.symm (sl2Ord3 F)) x
    rw [hfix, MulEquiv.apply_symm_apply, coe_sl2Ord3] at h1
    set v := Multiplicative.toAdd (Y x) with hv
    have e : !![(1 : F), 1; 1, 0] *ᵥ v = ![v 0 + v 1, v 0] := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [e] at h1
    have a := congrFun h1 0
    have b := congrFun h1 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a b
    have hv1 : v 1 = 0 := by linear_combination -a
    have hv0 : v 0 = 0 := b.symm.trans hv1
    show Y x = 1
    apply Multiplicative.toAdd.injective
    rw [← hv, toAdd_one]
    funext i
    fin_cases i
    · exact hv0
    · exact hv1

namespace QCoord

variable {L N S : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)}

theorem mem_centralizer_iff_of_nat (hc : QCoord L N S F ψ Y) (hSL : S ≤ L)
    (hbot : N ⊓ Subgroup.centralizer (L : Set G) = ⊥) (x : ↥N) :
    (x : G) ∈ Subgroup.centralizer (S : Set G) ↔ (Multiplicative.toAdd (Y x)) 1 = 0 := by
  rw [hc.snd_eq_zero_iff hSL]
  constructor
  · intro hx s hs
    rw [Subgroup.mem_centralizer_iff.mp hx s hs, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : s * (x : G) * s⁻¹ * (x : G)⁻¹ ∈ N ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨?_, h s hs⟩
      have hsN : s ∈ Subgroup.normalizer (N : Set G) := hc.le_normalizer (hSL hs)
      exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hsN _).mp x.2) (N.inv_mem x.2)
    rw [hbot, Subgroup.mem_bot] at h1
    calc s * (x : G) = s * x * s⁻¹ * (x : G)⁻¹ * x * s := by group
      _ = x * s := by rw [h1, one_mul]

theorem exists_beta (hc : QCoord L N S F ψ Y) (hSL : S ≤ L) :
    ∃ β : ↥S →* Multiplicative F, Function.Surjective β ∧
      (∀ s : ↥S, ψ (autHom hc.le_normalizer ⟨s, hSL s.2⟩) =
        unipSL (Multiplicative.toAdd (β s))) ∧
      (∀ s : ↥S, β s = 1 ↔ (s : G) ∈ Subgroup.centralizer (N : Set G)) := by
  have hLN := hc.le_normalizer
  have hmem : ∀ s : ↥S, ((autHom hLN ⟨s, hSL s.2⟩ : ↥(autOn L N)) : MulAut ↥N) ∈ autOn S N :=
    fun s => mem_autOn_iff.mpr ⟨⟨s, hLN (hSL s.2)⟩, s.2, rfl⟩
  choose b hb using fun s : ↥S => (hc.sylow _).mp (hmem s)
  have hinj : Function.Injective (unipSL : F → SL(2, F)) := by
    intro x y hxy
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hxy
    simpa [coe_unipSL] using this
  let β : ↥S →* Multiplicative F :=
    { toFun := fun s => Multiplicative.ofAdd (b s)
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply hinj
        rw [toAdd_ofAdd, ← hb 1, toAdd_one, Vol2.Ch10.SecA.unipSL_zero]
        rw [show (⟨((1 : ↥S) : G), hSL (1 : ↥S).2⟩ : ↥L) = 1 from rfl, map_one, map_one]
      map_mul' := fun s s' => by
        apply Multiplicative.toAdd.injective
        apply hinj
        rw [toAdd_ofAdd, ← hb, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
        rw [show (⟨((s * s' : ↥S) : G), hSL (s * s').2⟩ : ↥L) = ⟨s, hSL s.2⟩ * ⟨s', hSL s'.2⟩
          from rfl, map_mul, map_mul, hb, hb]
        have := (Vol2.Ch10.SecA.unipHom (F := F)).map_mul (Multiplicative.ofAdd (b s))
          (Multiplicative.ofAdd (b s'))
        simpa [Vol2.Ch10.SecA.unipHom_apply] using this.symm }
  refine ⟨β, ?_, fun s => hb s, fun s => ?_⟩
  · intro x
    have hx : ((ψ.symm (unipSL (Multiplicative.toAdd x)) : ↥(autOn L N)) : MulAut ↥N) ∈
        autOn S N := (hc.sylow _).mpr ⟨_, MulEquiv.apply_symm_apply _ _⟩
    obtain ⟨s, hs, hsx⟩ := mem_autOn_iff.mp hx
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    apply hinj
    show unipSL (b ⟨s, hs⟩) = _
    rw [← hb ⟨s, hs⟩]
    have : autHom hLN ⟨(s : G), hSL hs⟩ = ψ.symm (unipSL (Multiplicative.toAdd x)) :=
      Subtype.ext hsx
    rw [this, MulEquiv.apply_symm_apply]
  · constructor
    · intro h1
      have h2 : ψ (autHom hLN ⟨s, hSL s.2⟩) = 1 := by
        rw [hb s]
        have : b s = 0 := by
          have := congrArg Multiplicative.toAdd h1
          simpa [β] using this
        rw [this, Vol2.Ch10.SecA.unipSL_zero]
      have h3 : autHom hLN ⟨s, hSL s.2⟩ = 1 := ψ.injective (h2.trans (map_one ψ).symm)
      exact mem_centralizer_of_autHom_eq_one hLN h3
    · intro h1
      apply Multiplicative.toAdd.injective
      apply hinj
      show unipSL (b s) = unipSL (Multiplicative.toAdd 1)
      rw [← hb s, toAdd_one, Vol2.Ch10.SecA.unipSL_zero]
      have h3 : autHom hLN ⟨s, hSL s.2⟩ = 1 := by
        apply Subtype.ext
        ext w
        rw [autHom_apply_coe]
        show (s : G) * w * (s : G)⁻¹ = w
        rw [← Subgroup.mem_centralizer_iff.mp h1 w w.2, mul_inv_cancel_right]
      rw [h3, map_one]

end QCoord

theorem upper_conj_unipSL {F : Type} [Field F] {M : SL(2, F)}
    (hM : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (b : F) :
    M * unipSL b * M⁻¹ = unipSL ((M : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * b) := by
  have hdet := upper_det hM
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_unipSL,
    Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hM]
  · linear_combination hdet
  · ring
  · linear_combination hdet

theorem exists_ringEquiv_of_beta {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    [CharP F₁ 2] [CharP F₂ 2] (hcard : Nat.card F₁ = Nat.card F₂) {Sg X : Type*} [Group Sg]
    (β₁ : Sg →* Multiplicative F₁) (β₂ : Sg →* Multiplicative F₂)
    (hs₁ : Function.Surjective β₁) (hker : ∀ s, β₁ s = 1 ↔ β₂ s = 1) (act : X → Sg → Sg) (c₁ : X → F₁) (c₂ : X → F₂)
    (h₁ : ∀ x s, Multiplicative.toAdd (β₁ (act x s)) = c₁ x ^ 2 * Multiplicative.toAdd (β₁ s))
    (h₂ : ∀ x s, Multiplicative.toAdd (β₂ (act x s)) = c₂ x ^ 2 * Multiplicative.toAdd (β₂ s))
    (hc : ∀ c : F₁, c ≠ 0 → ∃ x, c₁ x = c) :
    ∃ φ : F₁ ≃+* F₂, ∀ x, c₂ x = φ (c₁ x) := by
  classical
  choose sec hsec using hs₁
  let φ₀ : F₁ → F₂ := fun a => Multiplicative.toAdd (β₂ (sec (Multiplicative.ofAdd a)))
  have hwd : ∀ s s', β₁ s = β₁ s' → β₂ s = β₂ s' := by
    intro s s' h
    have h1 : β₁ (s⁻¹ * s') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := (hker _).mp h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hφ₀ : ∀ s, φ₀ (Multiplicative.toAdd (β₁ s)) = Multiplicative.toAdd (β₂ s) := by
    intro s
    show Multiplicative.toAdd (β₂ (sec (Multiplicative.ofAdd (Multiplicative.toAdd (β₁ s))))) =
      _
    rw [hwd _ s (by rw [ofAdd_toAdd, hsec])]
  have hφ₀add : ∀ a a', φ₀ (a + a') = φ₀ a + φ₀ a' := by
    intro a a'
    obtain ⟨s, rfl⟩ : ∃ s, Multiplicative.toAdd (β₁ s) = a :=
      ⟨sec (Multiplicative.ofAdd a), by rw [hsec, toAdd_ofAdd]⟩
    obtain ⟨s', rfl⟩ : ∃ s', Multiplicative.toAdd (β₁ s') = a' :=
      ⟨sec (Multiplicative.ofAdd a'), by rw [hsec, toAdd_ofAdd]⟩
    rw [← toAdd_mul, ← map_mul, hφ₀, hφ₀, hφ₀, map_mul, toAdd_mul]
  have hφ₀0 : ∀ a, φ₀ a = 0 → a = 0 := by
    intro a ha
    obtain ⟨s, rfl⟩ : ∃ s, Multiplicative.toAdd (β₁ s) = a :=
      ⟨sec (Multiplicative.ofAdd a), by rw [hsec, toAdd_ofAdd]⟩
    rw [hφ₀] at ha
    have h1 : β₂ s = 1 := Multiplicative.toAdd.injective (by rw [ha]; rfl)
    rw [(hker s).mpr h1]
    rfl
  have hφ₀inj : Function.Injective φ₀ := by
    intro a a' h
    have h1 : φ₀ (a + a') = 0 := by rw [hφ₀add, h, CharTwo.add_self_eq_zero]
    have h2 := hφ₀0 _ h1
    have h3 := eq_neg_of_add_eq_zero_left h2
    rwa [CharTwo.neg_eq] at h3
  have hφ₀c : ∀ x a, φ₀ (c₁ x ^ 2 * a) = c₂ x ^ 2 * φ₀ a := by
    intro x a
    obtain ⟨s, rfl⟩ : ∃ s, Multiplicative.toAdd (β₁ s) = a :=
      ⟨sec (Multiplicative.ofAdd a), by rw [hsec, toAdd_ofAdd]⟩
    rw [← h₁, hφ₀, hφ₀, h₂]
  have := Fintype.ofFinite F₁
  have := Fintype.ofFinite F₂
  let ι : F₂ ≃+* F₁ := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard])
  have hpinj : Function.Injective (fun a => ι (φ₀ a)) := ι.injective.comp hφ₀inj
  let p : Equiv.Perm F₁ := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hpinj)
  have hp : ∀ a, p a = ι (φ₀ a) := fun _ => rfl
  have hpadd : ∀ a a', p (a + a') = p a + p a' := fun a a' => by
    rw [hp, hp, hp, hφ₀add, map_add]
  obtain ⟨σ, hσ⟩ := Semi516.exists_isSemilinearWith_of_conj_smul (F := F₁) p hpadd fun c => by
    by_cases hc0 : c = 0
    · refine ⟨0, fun y => ?_⟩
      rw [hc0, smul_eq_mul, smul_eq_mul, zero_mul, zero_mul]
      have := hpadd 0 0
      rw [add_zero] at this
      exact (add_eq_left.mp this.symm)
    · obtain ⟨r, hr⟩ := isSquare_of_charTwo' c
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact hc0 (by rw [hr, mul_zero])
      obtain ⟨x, hx⟩ := hc r hr0
      refine ⟨ι (c₂ x) ^ 2, fun y => ?_⟩
      have hc' : c = c₁ x ^ 2 := by rw [hr, hx, sq]
      rw [smul_eq_mul, smul_eq_mul, hc', hp, hφ₀c, map_mul, map_pow, ← hp, Semi516.perm_apply_inv]
  refine ⟨σ.trans ι.symm, fun x => ?_⟩
  have hkey : ∀ c a, φ₀ (c * a) = ι.symm (σ c) * φ₀ a := by
    intro c a
    have h1 := hσ c a
    rw [smul_eq_mul, smul_eq_mul, hp, hp] at h1
    apply ι.injective
    rw [h1, map_mul, RingEquiv.apply_symm_apply]
  have h1 := hφ₀c x 1
  rw [hkey] at h1
  have h10 : φ₀ 1 ≠ 0 := fun h => one_ne_zero (hφ₀0 1 h)
  have h2 := mul_right_cancel₀ h10 h1
  rw [map_pow, map_pow] at h2
  show c₂ x = ι.symm (σ (c₁ x))
  exact (CharTwo.sq_inj.mp h2).symm

end CFSG.Quasithin.H13
