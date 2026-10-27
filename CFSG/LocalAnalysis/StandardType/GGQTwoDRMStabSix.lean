module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBridge
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabA
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMSel
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
import CFSG.LocalAnalysis.StandardType.GGQTwoPThree
import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutAlt8Perm
import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEvenOrbit
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUA
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabD

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def A6BoundaryStabAt {G : Type} [Group G] [Finite G]
    (Bs L : Subgroup G) (x : G) (hx : x ∈ Bs) : Prop :=
  Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} ≤ 720 ∧
    ∀ a ∈ ggInduced ⊤ Bs, a ⟨x, hx⟩ = ⟨x, hx⟩ → a ∈ ggAutomizer L Bs

theorem a6_boundary_to_old_at {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {x : G} (hx : x ∈ Bs) (β : Additive ↥Bs ≃+ DVec 6)
    (h : A6BoundaryStabAt Bs L x hx) :
    Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} ≤
        2 ^ (6 - 1) * (6 - 1).factorial ∧
      ∀ a ∈ ggInduced ⊤ Bs, GGIsReflection 3 a → a ⟨x, hx⟩ = ⟨x, hx⟩ →
        a ∈ ggAutomizer L Bs ∨
          ∃ i : Fin 6, ∀ b : ↥Bs,
            β (Additive.ofMul (a b)) = dNeg 6 i (β (Additive.ofMul b)) := by
  refine ⟨le_trans h.1 (by norm_num), ?_⟩
  intro a ha _ hfix
  exact Or.inl (h.2 a ha hfix)

section Perm

variable {m : ℕ}

private lemma p9uRS6_eq_of_smul_single_eq {c c' : ZMod 3} (hc : c ≠ 0) {j k : Fin m}
    (h : c • (Pi.single j 1 : DVec m) = c' • Pi.single k 1) : j = k := by
  by_contra hjk
  have h' := congrFun h j
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk, smul_zero,
    smul_eq_mul, mul_one] at h'
  exact hc h'

private lemma p9uRS6_ne_zero_of_sign {c : ZMod 3} (h : c = 1 ∨ c = -1) : c ≠ 0 := by
  rcases h with h | h <;> rw [h] <;> decide

@[expose] noncomputable def dEvenPerm (w : ↥(dEven m)) : Equiv.Perm (Fin m) :=
  Classical.choose (show ∃ σ : Equiv.Perm (Fin m), ∃ c : Fin m → ZMod 3,
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧
        ∀ i, (w : DVec m ≃ₗ[ZMod 3] DVec m) (dBasis m i) = c i • dBasis m (σ i) from w.2)

theorem dEvenPerm_spec (w : ↥(dEven m)) : ∃ c : Fin m → ZMod 3, (∀ i, c i = 1 ∨ c i = -1) ∧
    (∀ i, (w : DVec m ≃ₗ[ZMod 3] DVec m) (dBasis m i) = c i • dBasis m (dEvenPerm w i)) ∧
    ∀ (v : DVec m) (i : Fin m), (w : DVec m ≃ₗ[ZMod 3] DVec m) v (dEvenPerm w i) = c i * v i := by
  obtain ⟨c, hc, -, hact⟩ := Classical.choose_spec (show ∃ σ : Equiv.Perm (Fin m),
      ∃ c : Fin m → ZMod 3, (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧
        ∀ i, (w : DVec m ≃ₗ[ZMod 3] DVec m) (dBasis m i) = c i • dBasis m (σ i) from w.2)
  refine ⟨c, hc, hact, fun v i => ?_⟩
  have hwv : (w : DVec m ≃ₗ[ZMod 3] DVec m) v =
      ∑ k, v k • (c k • dBasis m (dEvenPerm w k)) := by
    conv_lhs => rw [← (dBasis m).sum_repr v]
    simp only [map_sum, map_smul, Pi.basisFun_repr]
    exact Finset.sum_congr rfl fun k _ => by rw [hact k]; rfl
  rw [hwv, Finset.sum_apply, Finset.sum_eq_single i]
  · simp only [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    ring
  · intro k _ hki
    simp [Pi.basisFun_apply, (dEvenPerm w).injective.ne hki.symm]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem dEvenPerm_eq (w : ↥(dEven m)) {σ : Equiv.Perm (Fin m)} {c : Fin m → ZMod 3}
    (h : ∀ i, (w : DVec m ≃ₗ[ZMod 3] DVec m) (dBasis m i) = c i • dBasis m (σ i)) :
    dEvenPerm w = σ := by
  obtain ⟨c', hc', h', -⟩ := dEvenPerm_spec w
  refine Equiv.ext fun i => ?_
  have hi := (h' i).symm.trans (h i)
  simp only [dBasis, Pi.basisFun_apply] at hi
  exact p9uRS6_eq_of_smul_single_eq (p9uRS6_ne_zero_of_sign (hc' i)) hi

@[expose] noncomputable def dEvenPermHom (m : ℕ) : ↥(dEven m) →* Equiv.Perm (Fin m) where
  toFun := dEvenPerm
  map_one' := dEvenPerm_eq 1 (c := fun _ => 1) (fun i => by simp)
  map_mul' w w' := by
    obtain ⟨c, -, h, -⟩ := dEvenPerm_spec w
    obtain ⟨c', -, h', -⟩ := dEvenPerm_spec w'
    refine dEvenPerm_eq (w * w') (c := fun i => c' i * c (dEvenPerm w' i)) (fun i => ?_)
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h', map_smul, h, smul_smul,
      Equiv.Perm.mul_apply]

theorem apply_dEvenPerm_ne_zero_of_fix (w : ↥(dEven m)) {v : DVec m}
    (hv : (w : DVec m ≃ₗ[ZMod 3] DVec m) v = v) {i : Fin m} (hi : v i ≠ 0) :
    v (dEvenPerm w i) ≠ 0 := by
  obtain ⟨c, hc, -, happ⟩ := dEvenPerm_spec w
  have h := happ v i
  rw [hv] at h
  rw [h]
  exact mul_ne_zero_iff.mpr ⟨p9uRS6_ne_zero_of_sign (hc i), hi⟩

theorem eq_of_dEvenPerm_eq_of_fix {w w' : ↥(dEven m)} {v : DVec m} (hv : ∀ i, v i ≠ 0)
    (hw : (w : DVec m ≃ₗ[ZMod 3] DVec m) v = v) (hw' : (w' : DVec m ≃ₗ[ZMod 3] DVec m) v = v)
    (h : dEvenPerm w = dEvenPerm w') : w = w' := by
  obtain ⟨c, -, hb, happ⟩ := dEvenPerm_spec w
  obtain ⟨c', -, hb', happ'⟩ := dEvenPerm_spec w'
  have hcc : ∀ i, c i = c' i := by
    intro i
    have h1 := happ v i
    have h2 := happ' v i
    rw [hw] at h1
    rw [hw', ← h] at h2
    exact (show ∀ a b y : ZMod 3, y ≠ 0 → a * y = b * y → a = b by decide) _ _ _ (hv i)
      (h1.symm.trans h2)
  apply Subtype.ext
  refine (dBasis m).ext' fun i => ?_
  rw [hb, hb', hcc, h]

theorem commute_of_dEvenPerm_eq_one {w w' : ↥(dEven m)} (hw : dEvenPerm w = 1)
    (hw' : dEvenPerm w' = 1) : w * w' = w' * w := by
  obtain ⟨c, -, hb, -⟩ := dEvenPerm_spec w
  obtain ⟨c', -, hb', -⟩ := dEvenPerm_spec w'
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  refine (dBasis m).ext' fun i => ?_
  simp only [LinearEquiv.mul_apply, map_smul, hb, hb', hw, hw', Equiv.Perm.one_apply, smul_smul]
  rw [mul_comm]

end Perm

theorem exists_native_of_weylA5 {G : Type} [Group G] {Bs : Subgroup G}
    (β : Additive ↥Bs ≃+ DVec 6) {A : Subgroup (MulAut ↥Bs)}
    (hA : ∀ a ∈ A, ggLin (p := 3) β a ∈ dEven 6) (hW5 : GGWeylOfType 3 (CoxeterMatrix.A 5) A)
    {v₀ : DVec 6} (hv₀ : v₀ ≠ 0) (hfix : ∀ a ∈ A, ggLin (p := 3) β a v₀ = v₀) :
    (∀ i, v₀ i = 1 ∨ v₀ i = -1) ∧ A.map (ggLin (p := 3) β) = dEvenStab 6 v₀ := by
  classical
  obtain ⟨E, -⟩ := exists_permEquiv_of_ggWeylOfType_A hW5
  let ψ : Equiv.Perm (Fin 6) →* ↥(dEven 6) :=
    MonoidHom.codRestrict ((ggLin (p := 3) β).comp (A.subtype.comp E.toMonoidHom)) (dEven 6)
      (fun τ => hA _ (E τ).2)
  have hψ : ∀ τ, ((ψ τ : ↥(dEven 6)) : DVec 6 ≃ₗ[ZMod 3] DVec 6) =
      ggLin (p := 3) β (E τ) := fun τ => rfl
  have hψinj : Function.Injective ψ := by
    intro τ τ' h
    apply E.injective
    apply Subtype.ext
    apply ggLin_injective (p := 3) β
    rw [← hψ, ← hψ, h]
  let h : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 6) := (dEvenPermHom 6).comp ψ
  have hh : ∀ τ, h τ = dEvenPerm (ψ τ) := fun τ => rfl
  have hker : h.ker = ⊥ := by
    rcases CFSG.EvenSporadicStandard.M22Std.perm_six_eq_bot_or_alt_le (N := h.ker)
        inferInstance with hb | hA6
    · exact hb
    · exfalso
      have h1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
          Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
        decide
      have h2 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 3) ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
          Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
        decide
      have hc1 : dEvenPerm (ψ (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2)) = 1 :=
        (hh _).symm.trans (MonoidHom.mem_ker.mp (hA6 h1))
      have hc2 : dEvenPerm (ψ (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 3)) = 1 :=
        (hh _).symm.trans (MonoidHom.mem_ker.mp (hA6 h2))
      have hcomm := commute_of_dEvenPerm_eq_one hc1 hc2
      have hτ : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 1 3) =
          (Equiv.swap 0 1 * Equiv.swap 1 3) * (Equiv.swap 0 1 * Equiv.swap 1 2) :=
        hψinj (by
          rw [map_mul ψ (Equiv.swap 0 1 * Equiv.swap 1 2) (Equiv.swap 0 1 * Equiv.swap 1 3),
            map_mul ψ (Equiv.swap 0 1 * Equiv.swap 1 3) (Equiv.swap 0 1 * Equiv.swap 1 2), hcomm])
      exact absurd hτ (by decide)
  have hinj : Function.Injective h := (MonoidHom.ker_eq_bot_iff h).mp hker
  have hsurj : Function.Surjective h := Finite.injective_iff_surjective.mp hinj
  have hψfix : ∀ τ, ((ψ τ : ↥(dEven 6)) : DVec 6 ≃ₗ[ZMod 3] DVec 6) v₀ = v₀ :=
    fun τ => hfix _ (E τ).2
  obtain ⟨i₀, hi₀⟩ : ∃ i, v₀ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv₀ (funext hcon)
  have hsupp : ∀ j, v₀ j ≠ 0 := by
    intro j
    obtain ⟨τ, hτ⟩ := hsurj (Equiv.swap i₀ j)
    have h' := apply_dEvenPerm_ne_zero_of_fix (ψ τ) (hψfix τ) hi₀
    rwa [← hh, hτ, Equiv.swap_apply_left] at h'
  have hsign : ∀ i, v₀ i = 1 ∨ v₀ i = -1 := fun i =>
    (show ∀ y : ZMod 3, y ≠ 0 → y = 1 ∨ y = -1 by decide) _ (hsupp i)
  refine ⟨hsign, le_antisymm ?_ ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨hA a ha, hfix a ha⟩
  · intro w hw
    obtain ⟨τ, hτ⟩ := hsurj (dEvenPerm ⟨w, hw.1⟩)
    have heq : ψ τ = ⟨w, hw.1⟩ :=
      eq_of_dEvenPerm_eq_of_fix hsupp (hψfix τ) hw.2 ((hh τ).symm.trans hτ)
    exact ⟨E τ, (E τ).2, by rw [← hψ, heq]⟩

theorem ggIsTransvection_of_ggLin {G : Type} [Group G] {Bs : Subgroup G}
    (β : Additive ↥Bs ≃+ DVec 6) {φ : MulAut ↥Bs} {ε : DVec 6} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    {q : ZMod 3} (hq : q ≠ 0) (hφ : ∀ v, ggLin (p := 3) β φ v = v + (q * (ε ⬝ᵥ v)) • ε) :
    GGIsTransvection 3 φ := by
  classical
  have hεε : ε ⬝ᵥ ε = 0 := by
    have h1 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> rw [h] <;> decide
    unfold dotProduct
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    decide
  have hβφ : ∀ b : ↥Bs, β (Additive.ofMul (φ b)) =
      β (Additive.ofMul b) + (q * (ε ⬝ᵥ β (Additive.ofMul b))) • ε := fun b => by
    rw [← ggLin_apply_ofMul (p := 3) β φ b, hφ]
  have hε0 : ε 0 ≠ 0 := p9uRS6_ne_zero_of_sign (hε 0)
  let f : DVec 6 →+ ZMod 3 :=
    { toFun := fun v => ε ⬝ᵥ v
      map_zero' := dotProduct_zero ε
      map_add' := dotProduct_add ε }
  have hfsurj : Function.Surjective f := fun t => ⟨Pi.single 0 (t * ε 0), by
    change ε ⬝ᵥ Pi.single 0 (t * ε 0) = t
    rw [dotProduct_single]
    rcases hε 0 with h | h <;> rw [h] <;> ring⟩
  let eB : ↥Bs ≃ DVec 6 := Additive.ofMul.trans β.toEquiv
  have hfix_iff : ∀ b : ↥Bs, φ b = b ↔ eB b ∈ f.ker := by
    intro b
    rw [AddMonoidHom.mem_ker]
    change φ b = b ↔ ε ⬝ᵥ β (Additive.ofMul b) = 0
    constructor
    · intro hb
      have h1 := hβφ b
      rw [hb, left_eq_add] at h1
      have h2 := congrFun h1 0
      rw [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h2
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact (mul_eq_zero.mp h3).resolve_left hq
      · exact absurd h3 hε0
    · intro h0
      apply Additive.ofMul.injective
      apply β.injective
      rw [hβφ b, h0, mul_zero, zero_smul, add_zero]
  have hcard : Nat.card {b : ↥Bs // φ b = b} * 3 = Nat.card ↥Bs := by
    have h1 : Nat.card {b : ↥Bs // φ b = b} = Nat.card f.ker :=
      Nat.card_congr (Equiv.subtypeEquiv eB hfix_iff)
    have h2 : Nat.card ↥Bs = Nat.card (DVec 6) := Nat.card_congr eB
    have h3 : Nat.card f.ker * f.ker.index = Nat.card (DVec 6) := AddSubgroup.card_mul_index _
    have h4 : f.ker.index = 3 := by
      rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hfsurj, AddSubgroup.card_top,
        Nat.card_zmod]
    rw [h1, h2, ← h3, h4]
  refine ⟨hcard, fun b => ?_⟩
  apply Additive.ofMul.injective
  apply β.injective
  have hsub : β (Additive.ofMul (b⁻¹ * φ b)) = (q * (ε ⬝ᵥ β (Additive.ofMul b))) • ε := by
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, hβφ b]
    abel
  rw [hβφ, hsub, dotProduct_smul, hεε, smul_zero, mul_zero, zero_smul, add_zero]

theorem a6BoundaryStabAt_of_native (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp : p = 3) (hx : x ∈ Bs)
    (β : Additive ↥Bs ≃+ DVec 6) {ε : DVec 6} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hxε : β (Additive.ofMul ⟨x, hx⟩) = ε)
    (hAε : (ggAutomizer L Bs).map (ggLin (p := 3) β) = dEvenStab 6 ε) :
    A6BoundaryStabAt Bs L x hx := by
  subst hp
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  have hsupp : ∀ i, ε i ≠ 0 := fun i => p9uRS6_ne_zero_of_sign (hε i)
  have hlin_mem : ∀ a ∈ ggAutomizer L Bs, ggLin (p := 3) β a ∈ dEvenStab 6 ε := fun a ha => by
    rw [← hAε]
    exact Subgroup.mem_map_of_mem _ ha
  have hkey : ∀ a ∈ ggInduced ⊤ Bs, a ⟨x, hx⟩ = ⟨x, hx⟩ → a ∈ ggAutomizer L Bs := by
    intro a ha hax
    have hAfix : ggLin (p := 3) β a ε = ε := by
      rw [← hxε, ggLin_apply_ofMul, hax]
    have hAnorm : ∀ w ∈ dEvenStab 6 ε,
        ggLin (p := 3) β a * w * (ggLin (p := 3) β a)⁻¹ ∈ dEvenStab 6 ε := by
      intro w hw
      rw [← hAε] at hw
      obtain ⟨a', ha', rfl⟩ := hw
      rw [← map_inv, ← map_mul, ← map_mul]
      exact hlin_mem _ (qtwoDRMStab_normalizes ha₀ hcfg hx ha hax ha')
    obtain ⟨w, hw, q, hform⟩ := qtwoDRMStab_six_form hε hAfix hAnorm
    rw [← hAε] at hw
    obtain ⟨a', ha', hwa'⟩ := hw
    by_cases hq : q = 0
    · have hAw : ggLin (p := 3) β a = w := LinearEquiv.ext fun v => by
        rw [hform, hq, zero_mul, zero_smul, add_zero]
      have haa' : a = a' := ggLin_injective (p := 3) β (hAw.trans hwa'.symm)
      rw [haa']
      exact ha'
    · exfalso
      have hLtop : ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs :=
        Subgroup.closure_mono fun φ ⟨g, _, hgN, hφ⟩ => ⟨g, Subgroup.mem_top g, hgN, hφ⟩
      have hφ : a'⁻¹ * a ∈ ggAutomizer ⊤ Bs :=
        mul_mem (inv_mem (hLtop ha')) (Subgroup.subset_closure ha)
      have hφind : a'⁻¹ * a ∈ ggInduced ⊤ Bs := mem_ggAutomizer_iff.mp hφ
      refine hNT _ hφind (ggIsTransvection_of_ggLin β hε hq fun v => ?_)
      rw [map_mul, map_inv, LinearEquiv.mul_apply, hform, ← hwa', ← LinearEquiv.mul_apply,
        inv_mul_cancel]
      rfl
  refine ⟨?_, hkey⟩
  let Φ : {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} → Equiv.Perm (Fin 6) :=
    fun a => dEvenPerm ⟨ggLin (p := 3) β a.1, (hlin_mem a.1 (hkey a.1 a.2.1 a.2.2)).1⟩
  have hΦ : Function.Injective Φ := by
    intro a b hab
    have h := eq_of_dEvenPerm_eq_of_fix hsupp (hlin_mem a.1 (hkey a.1 a.2.1 a.2.2)).2
      (hlin_mem b.1 (hkey b.1 b.2.1 b.2.2)).2 hab
    exact Subtype.ext (ggLin_injective (p := 3) β (congrArg Subtype.val h))
  calc Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩}
      ≤ Nat.card (Equiv.Perm (Fin 6)) := Nat.card_le_card_of_injective Φ hΦ
    _ = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl

theorem card_dEven_six : Nat.card ↥(dEven 6) = 23040 := by
  obtain ⟨e, -⟩ := dEven_equiv (m := 6) (by norm_num)
  rw [← Nat.card_congr e.toEquiv, OrthF3.card_coxeterD_eq 6 (by norm_num)]
  rfl

theorem exists_native_of_weylD5 {G : Type} [Group G] {Bs : Subgroup G}
    (β : Additive ↥Bs ≃+ DVec 6) {A : Subgroup (MulAut ↥Bs)}
    (hA : ∀ a ∈ A, ggLin (p := 3) β a ∈ dEven 6) (hW : GGWeylOfType 3 (ggCoxeterMatrixD 5) A)
    {v₀ : DVec 6} (hv₀ : v₀ ≠ 0) (hfix : ∀ a ∈ A, ggLin (p := 3) β a v₀ = v₀) :
    ∃ (i₀ : Fin 6) (c : ZMod 3), c ≠ 0 ∧ v₀ = c • Pi.single i₀ 1 ∧
      A.map (ggLin (p := 3) β) = dEvenStab 6 (Pi.single i₀ 1) := by
  classical
  obtain ⟨eW, -⟩ := hW
  have hcardA : Nat.card A = 1920 := by
    rw [← Nat.card_congr eW.toEquiv, OrthF3.card_coxeterD_eq 5 (by norm_num)]
    rfl
  have hcardA' : Nat.card (A.map (ggLin (p := 3) β)) = 1920 := by
    rw [← hcardA]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective A _
      (ggLin_injective (p := 3) β)).toEquiv).symm
  have hA'le : A.map (ggLin (p := 3) β) ≤ dEven 6 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA a ha
  have hA'S : (A.map (ggLin (p := 3) β)).subgroupOf (dEven 6) ≤
      MulAction.stabilizer (↥(dEven 6)) v₀ := by
    intro w hw
    rw [Subgroup.mem_subgroupOf] at hw
    obtain ⟨a, ha, haw⟩ := hw
    rw [MulAction.mem_stabilizer_iff]
    change (w : DVec 6 ≃ₗ[ZMod 3] DVec 6) v₀ = v₀
    rw [← haw]
    exact hfix a ha
  have hdvd : 1920 ∣ Nat.card (MulAction.stabilizer (↥(dEven 6)) v₀) := by
    have h1 : Nat.card ((A.map (ggLin (p := 3) β)).subgroupOf (dEven 6)) = 1920 := by
      rw [← hcardA']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'le).toEquiv
    rw [← h1]
    exact Subgroup.card_dvd_of_le hA'S
  have hos : Nat.card (MulAction.stabilizer (↥(dEven 6)) v₀) *
      Nat.card (MulAction.orbit (↥(dEven 6)) v₀) = 23040 := by
    rw [← card_dEven_six, ← Subgroup.card_mul_index (MulAction.stabilizer (↥(dEven 6)) v₀),
      MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have horb : Nat.card (MulAction.orbit (↥(dEven 6)) v₀) ≤ 12 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk] at hos
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hos
    have h12 : k * Nat.card (MulAction.orbit (↥(dEven 6)) v₀) = 12 :=
      Nat.eq_of_mul_eq_mul_left (show 0 < 1920 by norm_num) (by rw [← mul_assoc, hos])
    calc Nat.card (MulAction.orbit (↥(dEven 6)) v₀)
        ≤ k * Nat.card (MulAction.orbit (↥(dEven 6)) v₀) := Nat.le_mul_of_pos_left _ (by omega)
      _ = 12 := h12
  have hsupp1 : (dVecSupp v₀).card = 1 := by
    have hpos : 0 < (dVecSupp v₀).card := by
      refine Finset.card_pos.mpr ?_
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      apply hv₀
      funext j
      by_contra hj
      have hjmem : j ∈ dVecSupp v₀ := mem_dVecSupp.mpr hj
      rw [hcon] at hjmem
      exact Finset.notMem_empty j hjmem
    by_contra hne
    by_cases h6 : (dVecSupp v₀).card = 6
    · have hfull : ∀ i, v₀ i ≠ 0 := by
        intro i
        have hall : dVecSupp v₀ = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [h6, Fintype.card_fin])
        exact mem_dVecSupp.mp (hall ▸ Finset.mem_univ i)
      have h32 : 2 ^ (6 - 1) ≤ Nat.card (MulAction.orbit (↥(dEven 6)) v₀) :=
        two_pow_le_card_orbit_of_full (by norm_num) hfull
      have h32' : 32 ≤ Nat.card (MulAction.orbit (↥(dEven 6)) v₀) := le_trans (by norm_num) h32
      omega
    · have hle : (dVecSupp v₀).card ≤ 6 := by
        calc (dVecSupp v₀).card ≤ Finset.univ.card := Finset.card_le_univ _
          _ = 6 := by rw [Finset.card_univ, Fintype.card_fin]
      have h4 : 4 * Nat.choose 6 (dVecSupp v₀).card ≤
          Nat.card (MulAction.orbit (↥(dEven 6)) v₀) :=
        four_mul_choose_le_card_orbit (by omega) (by omega)
      have h6' := le_choose_of_pos_of_lt (d := 6) (k := (dVecSupp v₀).card) (by omega) (by omega)
      omega
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hsupp1
  have hvi₀ : v₀ i₀ ≠ 0 := mem_dVecSupp.mp (by rw [hi₀]; exact Finset.mem_singleton_self i₀)
  have hv₀eq : v₀ = v₀ i₀ • Pi.single i₀ 1 := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i₀
    · subst hj
      rw [Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne hj, mul_zero]
      by_contra hjv
      have hjmem : j ∈ dVecSupp v₀ := mem_dVecSupp.mpr hjv
      rw [hi₀, Finset.mem_singleton] at hjmem
      exact hj hjmem
  refine ⟨i₀, v₀ i₀, hvi₀, hv₀eq, ?_⟩
  have hle : A.map (ggLin (p := 3) β) ≤ dEvenStab 6 (Pi.single i₀ 1) := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨hA a ha, ?_⟩
    have h := hfix a ha
    rw [hv₀eq, map_smul] at h
    exact (show ∀ (c : ZMod 3) (u u' : DVec 6), c ≠ 0 → c • u = c • u' → u = u' from
      fun c u u' hc h => by simpa [smul_smul, inv_mul_cancel₀ hc] using congrArg (c⁻¹ • ·) h)
      _ _ _ hvi₀ h
  have hcardS : Nat.card (dEvenStab 6 (Pi.single i₀ 1)) = 1920 := by
    rw [qtwoDB36_card_dEvenStab (m := 6) (by norm_num) i₀]
    rfl
  have : Finite ↥(dEvenStab 6 (Pi.single i₀ 1)) := Nat.finite_of_card_ne_zero (by omega)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardS, hcardA'])

theorem ggQTwoDRMStab_six_orth (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hx : x ∈ Bs) (β : Additive ↥Bs ≃+ DVec 6)
    {i₀ : Fin 6} {c : ZMod 3} (hc : c ≠ 0) (hxc : β (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1)
    (hAe : (ggAutomizer L Bs).map (ggLin (p := 3) β) = dEvenStab 6 (Pi.single i₀ 1)) :
    Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} ≤
        2 ^ (6 - 1) * (6 - 1).factorial ∧
      ∀ a ∈ ggInduced ⊤ Bs, GGIsReflection 3 a → a ⟨x, hx⟩ = ⟨x, hx⟩ →
        a ∈ ggAutomizer L Bs ∨
          ∃ i : Fin 6, ∀ b : ↥Bs, β (Additive.ofMul (a b)) = dNeg 6 i (β (Additive.ofMul b)) := by
  have hlin_mem : ∀ a ∈ ggAutomizer L Bs, ggLin (p := 3) β a ∈ dEvenStab 6 (Pi.single i₀ 1) :=
    fun a ha => by
      rw [← hAe]
      exact Subgroup.mem_map_of_mem _ ha
  have hfix_of : ∀ a : MulAut ↥Bs, a ⟨x, hx⟩ = ⟨x, hx⟩ →
      ggLin (p := 3) β a (Pi.single i₀ 1) = Pi.single i₀ 1 := by
    intro a hax
    have h := ggLin_apply_ofMul (p := 3) β a ⟨x, hx⟩
    rw [hax, hxc, map_smul] at h
    simpa [smul_smul, inv_mul_cancel₀ hc] using congrArg (c⁻¹ • ·) h
  have hnorm_of : ∀ a : MulAut ↥Bs, a ∈ ggInduced ⊤ Bs → a ⟨x, hx⟩ = ⟨x, hx⟩ →
      ∀ w ∈ dEvenStab 6 (Pi.single i₀ 1),
        ggLin (p := 3) β a * w * (ggLin (p := 3) β a)⁻¹ ∈ dEvenStab 6 (Pi.single i₀ 1) := by
    intro a ha hax w hw
    rw [← hAe] at hw
    obtain ⟨a', ha', rfl⟩ := hw
    rw [← map_inv, ← map_mul, ← map_mul]
    exact hlin_mem _ (qtwoDRMStab_normalizes ha₀ hcfg hx ha hax ha')
  have hD := qtwoDRMStab_D (m := 6) (by norm_num) i₀
  let Φ : {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} →
      {A : DVec 6 ≃ₗ[ZMod 3] DVec 6 // A (Pi.single i₀ 1) = Pi.single i₀ 1 ∧
        ∀ w ∈ dEvenStab 6 (Pi.single i₀ 1), A * w * A⁻¹ ∈ dEvenStab 6 (Pi.single i₀ 1)} :=
    fun a => ⟨ggLin (p := 3) β a.1, hfix_of a.1 a.2.2, hnorm_of a.1 a.2.1 a.2.2⟩
  have hΦ : Function.Injective Φ := fun a b hab =>
    Subtype.ext (ggLin_injective (p := 3) β (congrArg Subtype.val hab))
  have : Finite {A : DVec 6 ≃ₗ[ZMod 3] DVec 6 // A (Pi.single i₀ 1) = Pi.single i₀ 1 ∧
      ∀ w ∈ dEvenStab 6 (Pi.single i₀ 1), A * w * A⁻¹ ∈ dEvenStab 6 (Pi.single i₀ 1)} :=
    Finite.of_injective (fun A => (A.1 : DVec 6 → DVec 6))
      (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  refine ⟨(Nat.card_le_card_of_injective Φ hΦ).trans hD.1, fun a ha hrefl hax => ?_⟩
  have hMrefl : dIsRefl (ggLin (p := 3) β a) := exists_of_ggIsReflection β hrefl
  rcases hD.2 (ggLin (p := 3) β a) (hfix_of a hax) (hnorm_of a ha hax) hMrefl with hmem | ⟨i, hi⟩
  · left
    rw [← hAe] at hmem
    obtain ⟨a', ha', heq⟩ := hmem
    rwa [ggLin_injective (p := 3) β heq] at ha'
  · exact Or.inr ⟨i, fun b => by rw [← ggLin_apply_ofMul (p := 3) β a b, hi]⟩

section Input

theorem a6BoundaryStabInput_holds (ha₀ : GGLNoncyclicInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
      (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
        ∀ (e' : Fin 6 ≃ ι), M = (ggCoxeterMatrixD 6).reindex e' →
          ∀ (hx : x ∈ Bs) (β : Additive ↥Bs ≃+ DVec 6),
            (∀ (t : Fin 6) (s : ↥Bs),
              β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) :
                  MulAut ↥Bs)) s)) =
                dTau 6 (decide (t.val + 1 = 6)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
                  (β (Additive.ofMul s))) →
            GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs) →
              A6BoundaryStabAt Bs L x hx := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg e' hM hx β hβ hW5
  obtain ⟨r, hrL, hrc, h6⟩ := hcfg.2.2.2.2
  have hp : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hrL hrc h6
  have himg := qtwoD_image_eq (m := 6) (by norm_num) hM β hβ
  have hA : ∀ a ∈ ggAutomizer L Bs, ggLin (p := 3) β a ∈ dEven 6 := fun a ha => by
    rw [← himg]
    exact Subgroup.mem_map_of_mem _ ((le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦) ha)
  have hfix : ∀ a ∈ ggAutomizer L Bs, ggLin (p := 3) β a (β (Additive.ofMul ⟨x, hx⟩)) =
      β (Additive.ofMul ⟨x, hx⟩) := fun a ha => by
    rw [ggLin_apply_ofMul, qtwoD_AL_fixes_x hcfg.1 hx a ha]
  have hx1 : x ≠ 1 := (hcfg.1.1.1.1.2.2.2.2.2.2.1).2.2.1
  have hv₀ : β (Additive.ofMul ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hx1
    have h1 : (⟨x, hx⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (β.injective (h0.trans (map_zero β).symm))
    exact congrArg Subtype.val h1
  obtain ⟨hsign, hmap⟩ := exists_native_of_weylA5 β hA hW5 hv₀ hfix
  exact a6BoundaryStabAt_of_native ha₀ hcfg.1 hp hx β hsign rfl hmap

theorem ggQTwoDRMStabInputOn_six_of_type (ha₀ : GGLNoncyclicInput)
    (hT : GGQTwoDRMBaseTypeInputOn (· = 6)) : GGQTwoDRMStabInputOn (· = 6) := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hx β hβ
  subst hm
  rcases hT G p B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM with hA5 | hD5
  · exact a6_boundary_to_old_at hx β
      (a6BoundaryStabInput_holds ha₀ G p B Bs x L D J 𝒦 ι M e hcfg e' hM hx β hβ hA5)
  · obtain ⟨r, hrL, hrc, h6⟩ := hcfg.2.2.2.2
    have hp : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hrL hrc h6
    subst hp
    have himg := qtwoD_image_eq (m := 6) (by norm_num) hM β hβ
    have hA : ∀ a ∈ ggAutomizer L Bs, ggLin (p := 3) β a ∈ dEven 6 := fun a ha => by
      rw [← himg]
      exact Subgroup.mem_map_of_mem _
        ((le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦) ha)
    have hfix : ∀ a ∈ ggAutomizer L Bs, ggLin (p := 3) β a (β (Additive.ofMul ⟨x, hx⟩)) =
        β (Additive.ofMul ⟨x, hx⟩) := fun a ha => by
      rw [ggLin_apply_ofMul, qtwoD_AL_fixes_x hcfg.1 hx a ha]
    have hx1 : x ≠ 1 := (hcfg.1.1.1.1.2.2.2.2.2.2.1).2.2.1
    have hv₀ : β (Additive.ofMul ⟨x, hx⟩) ≠ 0 := by
      intro h0
      apply hx1
      have h1 : (⟨x, hx⟩ : ↥Bs) = 1 :=
        Additive.ofMul.injective (β.injective (h0.trans (map_zero β).symm))
      exact congrArg Subtype.val h1
    obtain ⟨i₀, c, hc, hxc, hmap⟩ := exists_native_of_weylD5 β hA hD5 hv₀ hfix
    exact ggQTwoDRMStab_six_orth ha₀ hcfg.1 hx β hc hxc hmap

end Input

end CFSG.StandardType.QTwo

end
