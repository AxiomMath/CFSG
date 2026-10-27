module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBDefs
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBModule2
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.Quasithin.H13.L827X.LBModule

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.H13.L827X.LBDefs CFSG.Quasithin.H13.L827X.LBModule2
open scoped commutatorElement

theorem chief_rep_exists {G : Type} [Group G] [Finite G] {T X K U V X₁ W₀ W₁ : Subgroup G} {v : G}
    (h : XiHyp T X K U V X₁ W₀ W₁ v) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : FiniteDimensional (ZMod 2) W)
      (τ : (CFSG.Quasithin.conjClosure K T ⊔ T : Subgroup G) →* (W ≃ₗ[ZMod 2] W))
      (π : W₁ → W), ChiefRepProps (CFSG.Quasithin.conjClosure K T ⊔ T) (pCoreOf 2 X) W₀ W₁ τ π := by
  obtain ⟨hT, hX, -, -, hXK, hKX, -, -, -, hUV, hVT, -, -, -, -, -, -, -, hUW0, hW0W1, hW1O,
    hΛW0, hΛW1, hchief, -⟩ := h
  set Λ : Subgroup G := CFSG.Quasithin.conjClosure K T ⊔ T with hΛdef
  have hTN : T ≤ Subgroup.normalizer (X : Set G) := hX.2.1
  have hOT : pCoreOf 2 X ≤ T := pCoreOf_le_of_quasithinIsSylowTwo hT hTN
  have hW1T : W₁ ≤ T := hW1O.trans (sup_le hOT (hUV.trans hVT))
  have hP : IsPGroup 2 W₁ := IsPGroup.to_le hT.1 hW1T
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    (Subgroup.le_normalizer.trans hKX).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hTO : T ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hTN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hΛO : Λ ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    sup_le (CFSG.Quasithin.conjClosure_le fun t ht z hz =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTO ht) (hKO hz)) (Subgroup.inv_mem _ (hTO ht)))
      hTO
  haveI hN : (W₀.subgroupOf W₁).Normal := ch827_normal hW0W1 hP hΛW0 hΛW1 hchief
  have hcomm := ch827_comm_quot hW0W1 hP hΛW0 hΛW1 hchief
  have hexp := ch827_exp2_quot hW0W1 hP hΛW0 hΛW1 hchief hcomm
  haveI := ch827_nontrivial_quot hW0W1
  letI : CommGroup (ch827Quot W₀ W₁) :=
    { (inferInstance : Group (ch827Quot W₀ W₁)) with mul_comm := hcomm }
  have h2 : ∀ x : Additive (ch827Quot W₀ W₁), (2 : ℕ) • x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ : ∃ q : ch827Quot W₀ W₁, Additive.ofMul q = x := ⟨Additive.toMul x, rfl⟩
    rw [← ofMul_pow, hexp q, ofMul_one]
  letI : Module (ZMod 2) (Additive (ch827Quot W₀ W₁)) := AddCommGroup.zmodModule h2
  let π : ↥W₁ → Additive (ch827Quot W₀ W₁) := fun w => Additive.ofMul (QuotientGroup.mk w)
  have hπadd : ∀ a b : ↥W₁, π (a * b) = π a + π b := fun a b =>
    (congrArg Additive.ofMul (QuotientGroup.mk_mul (W₀.subgroupOf W₁) a b)).trans (ofMul_mul _ _)
  have hπker : ∀ w : ↥W₁, π w = 0 ↔ (w : G) ∈ W₀ := fun w => by
    show Additive.ofMul (QuotientGroup.mk w : ch827Quot W₀ W₁) = 0 ↔ _
    rw [ofMul_eq_zero, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    refine ⟨w, ?_⟩
    show Additive.ofMul (QuotientGroup.mk w : ch827Quot W₀ W₁) = y
    rw [hw]
    rfl
  let lin : Λ → (Additive (ch827Quot W₀ W₁) →ₗ[ZMod 2] Additive (ch827Quot W₀ W₁)) :=
    fun l => (MonoidHom.toAdditive (ch827CQ Λ W₀ W₁ hΛW1 hΛW0 l)).toZModLinearMap 2
  have lin_one : ∀ x, lin 1 x = x := fun x => by
    show Additive.ofMul (ch827CQ Λ W₀ W₁ hΛW1 hΛW0 1 (Additive.toMul x)) = x
    rw [ch827CQ_one]
    rfl
  have lin_mul : ∀ (l l' : Λ) (x : Additive (ch827Quot W₀ W₁)),
      lin (l * l') x = lin l (lin l' x) := fun l l' x => by
    show Additive.ofMul (ch827CQ Λ W₀ W₁ hΛW1 hΛW0 (l * l') (Additive.toMul x)) =
      Additive.ofMul (ch827CQ Λ W₀ W₁ hΛW1 hΛW0 l
        (ch827CQ Λ W₀ W₁ hΛW1 hΛW0 l' (Additive.toMul x)))
    rw [ch827CQ_mul]
  let τl : Λ → (Additive (ch827Quot W₀ W₁) ≃ₗ[ZMod 2] Additive (ch827Quot W₀ W₁)) :=
    fun l => LinearEquiv.ofLinear (lin l) (lin l⁻¹)
      (LinearMap.ext fun x => by
        rw [LinearMap.comp_apply, ← lin_mul, mul_inv_cancel, lin_one]
        rfl)
      (LinearMap.ext fun x => by
        rw [LinearMap.comp_apply, ← lin_mul, inv_mul_cancel, lin_one]
        rfl)
  let τ : Λ →* (Additive (ch827Quot W₀ W₁) ≃ₗ[ZMod 2] Additive (ch827Quot W₀ W₁)) :=
    { toFun := τl
      map_one' := LinearEquiv.ext fun x => lin_one x
      map_mul' := fun l l' => LinearEquiv.ext fun x => lin_mul l l' x }
  have hτ : ∀ (l : Λ) (x : Additive (ch827Quot W₀ W₁)), τ l x = lin l x := fun l x => rfl
  have hequiv : ∀ (l : Λ) (w w' : ↥W₁), (w' : G) = (l : G) * w * (l : G)⁻¹ →
      τ l (π w) = π w' := by
    intro l w w' hw'
    have hww : w' = ch827ConjSub W₁ (hΛW1 l.2) w := Subtype.ext hw'
    rw [hww, hτ]
    show Additive.ofMul (ch827CQ Λ W₀ W₁ hΛW1 hΛW0 l (QuotientGroup.mk w)) =
      Additive.ofMul (QuotientGroup.mk (ch827ConjSub W₁ (hΛW1 l.2) w))
    rw [ch827CQ_mk]
  have hirr : ∀ S : Submodule (ZMod 2) (Additive (ch827Quot W₀ W₁)),
      (∀ l : Λ, ∀ w ∈ S, τ l w ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hfwdB : ∀ l ∈ Λ, ∀ g ∈ ch827Preim W₁ π hπadd S,
        l * g * l⁻¹ ∈ ch827Preim W₁ π hπadd S := by
      rintro l hl g ⟨x, rfl, hx⟩
      refine ⟨ch827ConjSub W₁ (hΛW1 hl) x, rfl, ?_⟩
      rw [← hequiv ⟨l, hl⟩ x _ rfl]
      exact hS ⟨l, hl⟩ _ hx
    have hBΛ : Λ ≤ Subgroup.normalizer (ch827Preim W₁ π hπadd S : Set G) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · exact hfwdB l hl g
      · intro hg
        have h2' := hfwdB l⁻¹ (inv_mem hl) _ hg
        simpa [mul_assoc] using h2'
    have hB0 : W₀ ≤ ch827Preim W₁ π hπadd S := by
      intro g hg
      exact ⟨⟨g, hW0W1.le hg⟩, rfl, by rw [(hπker _).mpr hg]; exact S.zero_mem⟩
    have hB1 : ch827Preim W₁ π hπadd S ≤ W₁ := by
      rintro g ⟨x, rfl, -⟩
      exact x.2
    rcases hchief _ hB0 hB1 hBΛ with hB | hB
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨w, rfl⟩ := hπsurj x
      have hwB : (w : G) ∈ ch827Preim W₁ π hπadd S := ⟨w, rfl, hx⟩
      rw [hB] at hwB
      exact (hπker w).mpr hwB
    · right
      rw [Submodule.eq_top_iff']
      intro x
      obtain ⟨w, rfl⟩ := hπsurj x
      have hwB : (w : G) ∈ ch827Preim W₁ π hπadd S := by
        rw [hB]
        exact w.2
      obtain ⟨x', hx', hmem⟩ := hwB
      have : x' = w := Subtype.ext hx'
      rw [← this]
      exact hmem
  have hOp : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hPp : IsPGroup 2 ↥(pCoreOf 2 X ⊓ Λ) := IsPGroup.to_le hOp inf_le_left
  let ρ : ↥(pCoreOf 2 X ⊓ Λ) →* (Additive (ch827Quot W₀ W₁) ≃ₗ[ZMod 2] Additive (ch827Quot W₀ W₁)) :=
    τ.comp (Subgroup.inclusion inf_le_right)
  letI : MulAction ↥(pCoreOf 2 X ⊓ Λ) (Additive (ch827Quot W₀ W₁)) := MulAction.compHom _ ρ
  obtain ⟨w₁, hw₁0, hw₁⟩ := ch827_exists_fixed_ne_zero ↥(pCoreOf 2 X ⊓ Λ) hPp (fun g => by
    show τ (Subgroup.inclusion inf_le_right g) 0 = 0
    exact map_zero _)
  have hw₁fix : ∀ l : Λ, (l : G) ∈ pCoreOf 2 X → τ l w₁ = w₁ := by
    intro l hl
    have := hw₁ ⟨(l : G), hl, l.2⟩
    exact this
  let C : Submodule (ZMod 2) (Additive (ch827Quot W₀ W₁)) :=
    { carrier := {w | ∀ l : Λ, (l : G) ∈ pCoreOf 2 X → τ l w = w}
      add_mem' := fun {a b} ha hb l hl => by
        show τ l (a + b) = a + b
        rw [map_add, ha l hl, hb l hl]
      zero_mem' := fun l _ => map_zero _
      smul_mem' := fun c x hx l hl => by
        show τ l (c • x) = c • x
        rw [map_smul, hx l hl] }
  have hCinv : ∀ l : Λ, ∀ w ∈ C, τ l w ∈ C := by
    intro l w hw
    show ∀ l' : Λ, (l' : G) ∈ pCoreOf 2 X → τ l' (τ l w) = τ l w
    intro l' hl'
    have hconj : ((l⁻¹ * l' * l : Λ) : G) ∈ pCoreOf 2 X := by
      have h3 := (Subgroup.mem_normalizer_iff.mp (hΛO (inv_mem l.2)) (l' : G)).mp hl'
      simpa [mul_assoc] using h3
    calc τ l' (τ l w) = τ (l' * l) w := by rw [map_mul, LinearEquiv.mul_apply]
      _ = τ (l * (l⁻¹ * l' * l)) w := by rw [show l * (l⁻¹ * l' * l) = l' * l by group]
      _ = τ l (τ (l⁻¹ * l' * l) w) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = τ l w := by rw [hw _ hconj]
  have hCtop : C = ⊤ := by
    rcases hirr C hCinv with hC | hC
    · exfalso
      have hmem : w₁ ∈ C := fun l hl => hw₁fix l hl
      rw [hC, Submodule.mem_bot] at hmem
      exact hw₁0 hmem
    · exact hC
  have hOtriv : ∀ o : Λ, (o : G) ∈ pCoreOf 2 X → τ o = 1 := by
    intro o ho
    apply LinearEquiv.ext
    intro w
    have hw : w ∈ C := by
      rw [hCtop]
      exact Submodule.mem_top
    exact hw o ho
  refine ⟨Additive (ch827Quot W₀ W₁), inferInstance, inferInstance, inferInstance, τ, π, ?_⟩
  unfold ChiefRepProps
  exact ⟨inferInstance, hπsurj, hπadd, hπker, hequiv, hOtriv, hirr⟩

theorem mQuot_eq_finrank_range {G : Type} [Group G] [Finite G] {T X K U V X₁ W₀ W₁ : Subgroup G}
    {v : G} (h : XiHyp T X K U V X₁ W₀ W₁ v) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {τ : (CFSG.Quasithin.conjClosure K T ⊔ T : Subgroup G) →* (W ≃ₗ[ZMod 2] W)} {π : W₁ → W}
    (hR : ChiefRepProps (CFSG.Quasithin.conjClosure K T ⊔ T) (pCoreOf 2 X) W₀ W₁ τ π)
    (hvΛ : v ∈ CFSG.Quasithin.conjClosure K T ⊔ T) :
    mQuot (⁅W₁, Subgroup.zpowers v⁆ ⊔ W₀) W₀ =
      Module.finrank (ZMod 2) (LinearMap.range ((τ ⟨v, hvΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap - 1)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsq, -, -, -, hvV, -, -, hW0W1, -, -, hΛW1, -, -⟩ := h
  obtain ⟨-, hπsurj, hπadd, hπker, hequiv, -, -⟩ := hR
  have hv2 : v ^ 2 = 1 := hsq v hvV
  have h2z : v ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hv2]
  have hzp : ∀ k ∈ Subgroup.zpowers v, k = 1 ∨ k = v := by
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
    · left
      rw [zpow_mul, h2z, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, h2z, one_zpow, one_mul]
  have hvinv : ∀ w : G, w ∈ W₁ → v * w⁻¹ * v⁻¹ ∈ W₁ := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hΛW1 hvΛ) w⁻¹).mp (inv_mem hw)
  have hcommW : ∀ w : G, w ∈ W₁ → ⁅w, v⁆ ∈ W₁ := fun w hw => by
    rw [commutatorElement_def, show w * v * w⁻¹ * v⁻¹ = w * (v * w⁻¹ * v⁻¹) by group]
    exact W₁.mul_mem hw (hvinv w hw)
  set φ : W →ₗ[ZMod 2] W := (τ ⟨v, hvΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap - 1 with hφdef
  have hφ : ∀ y : W, φ y = τ ⟨v, hvΛ⟩ y - y := fun y => rfl
  set R : Submodule (ZMod 2) W := LinearMap.range φ with hRdef
  set A : Subgroup G := ⁅W₁, Subgroup.zpowers v⁆ ⊔ W₀ with hAdef
  have hcomm_le : ⁅W₁, Subgroup.zpowers v⁆ ≤ W₁ := by
    rw [Subgroup.commutator_le]
    intro w hw k hk
    rcases hzp k hk with hk1 | hk1
    · rw [hk1, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [hk1]
      exact hcommW w hw
  have hAW1 : A ≤ W₁ := sup_le hcomm_le hW0W1.le
  have hkey1 : ∀ w : ↥W₁, π ⟨⁅(w : G), v⁆, hcommW w w.2⟩ = -φ (π w) := by
    intro w
    have hx : v * (w : G)⁻¹ * v⁻¹ ∈ W₁ := hvinv w w.2
    have e1 : (⟨⁅(w : G), v⁆, hcommW w w.2⟩ : ↥W₁) = w * ⟨v * (w : G)⁻¹ * v⁻¹, hx⟩ :=
      Subtype.ext (show ⁅(w : G), v⁆ = (w : G) * (v * (w : G)⁻¹ * v⁻¹) by
        rw [commutatorElement_def]
        group)
    have e2 : π ⟨v * (w : G)⁻¹ * v⁻¹, hx⟩ = τ ⟨v, hvΛ⟩ (π w⁻¹) :=
      (hequiv ⟨v, hvΛ⟩ w⁻¹ ⟨v * (w : G)⁻¹ * v⁻¹, hx⟩ rfl).symm
    have e3 : π w⁻¹ = -π w := ch827_pi_inv W₁ π hπadd w
    rw [e1, hπadd, e2, e3, map_neg, hφ]
    abel
  have hB0 : W₀ ≤ ch827Preim W₁ π hπadd R := by
    intro g hg
    exact (mem_ch827Preim).mpr ⟨⟨g, hW0W1.le hg⟩, rfl, by
      rw [(hπker _).mpr hg]
      exact R.zero_mem⟩
  have hsubA : A ≤ ch827Preim W₁ π hπadd R := by
    refine sup_le ?_ hB0
    rw [Subgroup.commutator_le]
    intro w hw k hk
    rcases hzp k hk with hk1 | hk1
    · rw [hk1, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [hk1]
      refine (mem_ch827Preim).mpr ⟨⟨⁅w, v⁆, hcommW w hw⟩, rfl, ?_⟩
      have hk' : π ⟨⁅w, v⁆, hcommW w hw⟩ = -φ (π ⟨w, hw⟩) := hkey1 ⟨w, hw⟩
      rw [hk']
      exact R.neg_mem (LinearMap.mem_range_self φ _)
  have hsupA : ∀ r ∈ R, ∃ x : ↥A, π ⟨(x : G), hAW1 x.2⟩ = r := by
    intro r hr
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hr
    obtain ⟨w, rfl⟩ := hπsurj y
    have hmemA : ⁅(w : G), v⁆⁻¹ ∈ A :=
      inv_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator w.2 (Subgroup.mem_zpowers v)))
    refine ⟨⟨⁅(w : G), v⁆⁻¹, hmemA⟩, ?_⟩
    have hx' : ⁅(w : G), v⁆⁻¹ ∈ W₁ := inv_mem (hcommW w w.2)
    have e4 : (⟨⁅(w : G), v⁆⁻¹, hx'⟩ : ↥W₁) = (⟨⁅(w : G), v⁆, hcommW w w.2⟩ : ↥W₁)⁻¹ :=
      Subtype.ext rfl
    show π ⟨⁅(w : G), v⁆⁻¹, hx'⟩ = φ (π w)
    rw [e4, ch827_pi_inv W₁ π hπadd, hkey1 w, neg_neg]
  let ιA : ↥A → ↥W₁ := fun x => ⟨(x : G), hAW1 x.2⟩
  let F : ↥A →* Multiplicative W :=
    { toFun := fun x => Multiplicative.ofAdd (π (ιA x))
      map_one' := by
        show Multiplicative.ofAdd (π (1 : ↥W₁)) = 1
        rw [ch827_pi_one W₁ π hπadd, ofAdd_zero]
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (π (ιA x * ιA y)) = Multiplicative.ofAdd (π (ιA x)) *
          Multiplicative.ofAdd (π (ιA y))
        rw [hπadd, ofAdd_add] }
  have hker : F.ker = W₀.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (π (ιA x)) = 1 ↔ _
    rw [ofAdd_eq_one, hπker]
  have hF : ∀ y : Multiplicative W, y ∈ F.range ↔ Multiplicative.toAdd y ∈ R := by
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨h', hh', hmem⟩ := (mem_ch827Preim).mp (hsubA x.2)
      have hxh : h' = ιA x := Subtype.ext hh'
      show π (ιA x) ∈ R
      rw [← hxh]
      exact hmem
    · intro hy
      obtain ⟨x, hx⟩ := hsupA (Multiplicative.toAdd y) hy
      refine ⟨x, ?_⟩
      show Multiplicative.ofAdd (π (ιA x)) = y
      rw [hx]
      rfl
  have hrel : W₀.relIndex A = Nat.card R := by
    unfold Subgroup.relIndex
    rw [← hker, Subgroup.index_ker, Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd hF)]
  have hcardR : Nat.card R = 2 ^ Module.finrank (ZMod 2) R := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  unfold mQuot
  rw [hrel, hcardR, padicValNat.prime_pow]

end CFSG.Quasithin.H13.L827X.LBModule
