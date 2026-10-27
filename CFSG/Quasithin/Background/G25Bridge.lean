module

public import CFSG.Quasithin.Background.G13Fam
public import CFSG.Quasithin.Background.G2SixCore

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.G1 CFSG.Quasithin.SL2Model
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G] {F : Type*} [Field F] [CharP F 2] {n : ℕ}

structure SectionFam (hn : 2 ≤ n) (I Sx N : Subgroup G) (β : ↥I →* SL(n, F))
    (σ : SL(n, F) →* SL(n, F)) (A : Fin n → Subgroup G) : Prop where
  N_le : ∀ k, N ≤ A k
  le_Sx : ∀ k, A k ≤ Sx
  swap : ∀ (k : Fin n) (h : idx0 hn ≠ k), ∃ x : ↥I, β x = σ (wS F h) ∧
    (∀ y ∈ A (idx0 hn), (x : G) * y * (x : G)⁻¹ ∈ A k) ∧
    (∀ z ∈ A k, (x : G)⁻¹ * z * (x : G) ∈ A (idx0 hn))
  torus : ∀ d : Fˣ, ∃ x : ↥I, β x = σ (embSL (idx0_ne_idx1 hn) (dgm d)) ∧
    ∀ y ∈ A (idx0 hn), (x : G) * y * (x : G)⁻¹ ∈ A (idx0 hn)
  root : ∀ (a b : Fin n) (hab : a ≠ b) (k : Fin n), k ≠ b → ∀ c : F, ∃ x : ↥I,
    β x = σ (Matrix.SpecialLinearGroup.transvection hab c) ∧
      ∀ y ∈ A k, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ N
  comm : ∀ c : F, ∃ x : ↥I,
    β x = σ (Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c) ∧
      ∀ y ∈ Sx, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ A (idx0 hn)
  disj : A (idx0 hn) ⊓ A (idx1 hn) ≤ N
  sup : ⨆ k, A k = Sx

namespace QuotSetting

variable {I Sx N : Subgroup G} (Q : QuotSetting I Sx N) [(N.subgroupOf Sx).Normal]

theorem convAct_eq_one_of_comm (x : ↥I) (hx : ∀ y ∈ Sx, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ N) :
    Q.convAct x = 1 := by
  apply MulEquiv.ext
  intro a
  refine QuotientGroup.induction_on a fun y => ?_
  show Q.convAct x (secMk Sx N y) = secMk Sx N y
  rw [convAct_mk, secMk_eq_secMk_iff]
  have := hx (y⁻¹ : G) (inv_mem y.2)
  simpa [mul_assoc] using this

@[expose] noncomputable def actOfHom' {K : Type*} [Group K] (β : ↥I →* K)
    (hβ : Function.Surjective β) (hker : ∀ x : ↥I, β x = 1 → Q.convAct x = 1) :
    K →* MulAut (SecQuot Sx N) :=
  β.liftOfRightInverse (Function.surjInv hβ) (Function.rightInverse_surjInv hβ)
    ⟨Q.convAct, fun x hx => hker x hx⟩

theorem actOfHom'_apply {K : Type*} [Group K] (β : ↥I →* K) (hβ : Function.Surjective β)
    (hker : ∀ x : ↥I, β x = 1 → Q.convAct x = 1) (x : ↥I) :
    Q.actOfHom' β hβ hker (β x) = Q.convAct x :=
  β.liftOfRightInverse_comp_apply (Function.surjInv hβ) (Function.rightInverse_surjInv hβ)
    ⟨Q.convAct, fun x hx => hker x hx⟩ x

end QuotSetting

theorem exists_phi_of_sectionFam [Finite G] [Finite F] {hn : 2 ≤ n} {I Sx N : Subgroup G}
    (Q : QuotSetting I Sx N) (β : ↥I →* SL(n, F)) (hβ : Function.Surjective β)
    (hker : ∀ x : ↥I, β x = 1 → ∀ y ∈ Sx, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ N)
    (σ : SL(n, F) →* SL(n, F)) {A : Fin n → Subgroup G} (hA : SectionFam hn I Sx N β σ A) :
    ∃ (s : ℕ) (φ : ↥Sx →* Multiplicative (Fin s → Fin n → F)),
      Function.Surjective φ ∧ (∀ x : ↥Sx, φ x = 1 ↔ (x : G) ∈ N) ∧
      (∀ (m : ↥I) (g : SL(n, F)) (x y : ↥Sx), σ g = β m →
        (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
          φ y = Multiplicative.ofAdd (fun l => g • Multiplicative.toAdd (φ x) l)) ∧
      (∀ (k : Fin n) (x : ↥Sx), (x : G) ∈ A k ↔
        ∀ (l : Fin s) (j : Fin n), j ≠ k → Multiplicative.toAdd (φ x) l j = 0) ∧
      Nat.card ↥(A (idx0 hn)) = Nat.card ↥N * Nat.card F ^ s := by
  have hNnormal := Q.normal
  let _ : CommGroup (SecQuot Sx N) := Q.quotCommGroup
  have hker' : ∀ x : ↥I, β x = 1 → Q.convAct x = 1 := fun x hx =>
    Q.convAct_eq_one_of_comm x (hker x hx)
  let ρ0 : SL(n, F) →* MulAut (SecQuot Sx N) := Q.actOfHom' β hβ hker'
  let ρ : SL(n, F) →* MulAut (SecQuot Sx N) := ρ0.comp σ
  let _ : DistribMulAction SL(n, F) (Additive (SecQuot Sx N)) := distribMulActionAdditive ρ
  have hconj : ∀ (i : ↥I) (x : ↥Sx), ρ0 (β i) (secMk Sx N x) =
      secMk Sx N ⟨(i : G) * x * (i : G)⁻¹, Q.nS i i.2 x x.2⟩ := fun i x => by
    rw [Q.actOfHom'_apply, Q.convAct_mk]
  have hact : ∀ (g : SL(n, F)) (i : ↥I) (x : ↥Sx), σ g = β i →
      g • Additive.ofMul (secMk Sx N x) =
        Additive.ofMul (secMk Sx N ⟨(i : G) * x * (i : G)⁻¹, Q.nS i i.2 x x.2⟩) := by
    intro g i x hg
    show Additive.ofMul (ρ0 (σ g) (secMk Sx N x)) = _
    rw [hg, hconj]
  let Y : Fin n → AddSubgroup (Additive (SecQuot Sx N)) := fun k =>
    Subgroup.toAddSubgroup (secImg Sx N (A k))
  have hY : ∀ k a, Additive.ofMul a ∈ Y k ↔ a ∈ secImg Sx N (A k) := fun k a => Iff.rfl
  have hmemY : ∀ (k : Fin n) (x : ↥Sx), Additive.ofMul (secMk Sx N x) ∈ Y k ↔ (x : G) ∈ A k :=
    fun k x => by
      rw [hY]
      exact secMk_mem_secImg_iff (hA.N_le k)
  have hsurj : ∀ u : Additive (SecQuot Sx N), ∃ x : ↥Sx, u = Additive.ofMul (secMk Sx N x) := by
    intro u
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective u
    obtain ⟨x, rfl⟩ := secMk_surjective (A := Sx) (B := N) a
    exact ⟨x, rfl⟩
  have hsq : ∀ u : Additive (SecQuot Sx N), u + u = 0 := fun u => by
    show Additive.ofMul (Additive.toMul u * Additive.toMul u) = Additive.ofMul 1
    exact congrArg Additive.ofMul (Q.quot_sq _)
  have hfam : G13Fam F hn Y :=
    { swap := fun k h => by
        obtain ⟨x, hx, hxA, hxA'⟩ := hA.swap k h
        ext u
        obtain ⟨y, rfl⟩ := hsurj u
        rw [hmemY k y]
        constructor
        · intro hy
          have hyS : (x : G)⁻¹ * y * (x : G) ∈ Sx := by
            have := Q.nS ((x : G)⁻¹) (inv_mem x.2) y y.2
            simpa using this
          refine ⟨Additive.ofMul (secMk Sx N ⟨(x : G)⁻¹ * y * x, hyS⟩),
            (hmemY _ _).2 (hxA' y hy), ?_⟩
          show wS F h • Additive.ofMul (secMk Sx N ⟨(x : G)⁻¹ * y * x, hyS⟩) = _
          rw [hact (wS F h) x _ hx.symm]
          congr 2
          apply Subtype.ext
          simp [mul_assoc]
        · rintro ⟨z, hz, hzy⟩
          obtain ⟨y', rfl⟩ := hsurj z
          have hy' := (hmemY _ _).1 hz
          have h1 : wS F h • Additive.ofMul (secMk Sx N y') =
              Additive.ofMul (secMk Sx N ⟨(x : G) * y' * (x : G)⁻¹, Q.nS x x.2 y' y'.2⟩) :=
            hact (wS F h) x y' hx.symm
          have h2 : Additive.ofMul (secMk Sx N ⟨(x : G) * y' * (x : G)⁻¹, Q.nS x x.2 y' y'.2⟩) =
              Additive.ofMul (secMk Sx N y) := h1.symm.trans hzy
          have h3 := Additive.ofMul.injective h2
          rw [secMk_eq_secMk_iff] at h3
          have h4 : (x : G) * y' * (x : G)⁻¹ ∈ A k := hxA y' hy'
          have e : (y : G) = (x : G) * y' * (x : G)⁻¹ *
              (((x : G) * y' * (x : G)⁻¹)⁻¹ * y) := by group
          rw [e]
          exact (A k).mul_mem h4 (hA.N_le k h3)
      torus := fun d y hy => by
        obtain ⟨x, hx, hxA⟩ := hA.torus d
        obtain ⟨y', rfl⟩ := hsurj y
        have hy' := (hmemY _ _).1 hy
        show embSL (idx0_ne_idx1 hn) (dgm d) • Additive.ofMul (secMk Sx N y') ∈ Y (idx0 hn)
        rw [hact _ x y' hx.symm]
        exact (hmemY _ _).2 (hxA y' hy')
      root_fix := fun a b hab k hkb c y hy => by
        obtain ⟨x, hx, hxN⟩ := hA.root a b hab k hkb c
        obtain ⟨y', rfl⟩ := hsurj y
        have hy' := (hmemY _ _).1 hy
        show Matrix.SpecialLinearGroup.transvection hab c • Additive.ofMul (secMk Sx N y') =
          Additive.ofMul (secMk Sx N y')
        rw [hact _ x y' hx.symm]
        congr 1
        rw [secMk_eq_secMk_iff]
        have := hxN ((y' : G)⁻¹) ((A k).inv_mem hy')
        have e : ((x : G) * y' * (x : G)⁻¹)⁻¹ * y' = (x : G) * (y' : G)⁻¹ * (x : G)⁻¹ *
            (y' : G)⁻¹⁻¹ := by group
        show ((x : G) * y' * (x : G)⁻¹)⁻¹ * y' ∈ N
        rw [e]
        exact this
      comm := fun c u => by
        obtain ⟨x, hx, hxA⟩ := hA.comm c
        obtain ⟨y, rfl⟩ := hsurj u
        show Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c •
          Additive.ofMul (secMk Sx N y) - Additive.ofMul (secMk Sx N y) ∈ Y (idx0 hn)
        rw [hact _ x y hx.symm]
        show Additive.ofMul (secMk Sx N ⟨(x : G) * y * (x : G)⁻¹, Q.nS x x.2 y y.2⟩ /
          secMk Sx N y) ∈ Y (idx0 hn)
        rw [div_eq_mul_inv, ← map_inv (secMk Sx N) y, ← map_mul]
        refine (hY _ _).2 (secMk_mem_secImg (A := Sx) (B := N) ?_)
        have := hxA y y.2
        simpa [mul_assoc] using this
      disj := by
        rw [eq_bot_iff]
        intro z hz
        obtain ⟨y, rfl⟩ := hsurj z
        have h0 := (hmemY _ _).1 (AddSubgroup.mem_inf.1 hz).1
        have h1 := (hmemY _ _).1 (AddSubgroup.mem_inf.1 hz).2
        have : (y : G) ∈ N := hA.disj ⟨h0, h1⟩
        exact AddSubgroup.mem_bot.2 (by rw [secMk_eq_one_iff.2 this]; rfl)
      sup := by
        rw [eq_top_iff]
        intro z _
        obtain ⟨y, rfl⟩ := hsurj z
        have hy : (y : G) ∈ ⨆ k, A k := by rw [hA.sup]; exact y.2
        have key : ∃ hx : (y : G) ∈ Sx, secMk Sx N ⟨y, hx⟩ ∈ ⨆ k, secImg Sx N (A k) := by
          refine Subgroup.iSup_induction (fun k => A k)
            (C := fun x => ∃ hx : x ∈ Sx, secMk Sx N ⟨x, hx⟩ ∈ ⨆ k, secImg Sx N (A k)) hy ?_ ?_ ?_
          · intro k x hx
            exact ⟨hA.le_Sx k hx, le_iSup (fun k => secImg Sx N (A k)) k
              (secMk_mem_secImg (A := Sx) (B := N) (x := ⟨x, hA.le_Sx k hx⟩) hx)⟩
          · exact ⟨Sx.one_mem, by
              have : secMk Sx N ⟨1, Sx.one_mem⟩ = 1 := map_one _
              rw [this]
              exact Subgroup.one_mem _⟩
          · rintro x z ⟨hx, hx'⟩ ⟨hz, hz'⟩
            refine ⟨Sx.mul_mem hx hz, ?_⟩
            have : secMk Sx N ⟨x * z, Sx.mul_mem hx hz⟩ =
                secMk Sx N ⟨x, hx⟩ * secMk Sx N ⟨z, hz⟩ := map_mul (secMk Sx N) ⟨x, hx⟩ ⟨z, hz⟩
            rw [this]
            exact Subgroup.mul_mem _ hx' hz'
        obtain ⟨hx, hx'⟩ := key
        have h1 : Additive.ofMul (secMk Sx N ⟨y, hx⟩) ∈
            Subgroup.toAddSubgroup (⨆ k, secImg Sx N (A k)) := hx'
        rw [OrderIso.map_iSup] at h1
        exact h1 }
  obtain ⟨s, Θ, hΘ, hcard, hmem⟩ := hfam.exists_equiv_fam hsq
  let ψ : Additive (SecQuot Sx N) →+ (Fin s → Fin n → F) := Θ.symm.toAddMonoidHom
  let φ : ↥Sx →* Multiplicative (Fin s → Fin n → F) :=
    (AddMonoidHom.toMultiplicativeRight ψ).comp (secMk Sx N)
  have hφ : ∀ x : ↥Sx, φ x =
      Multiplicative.ofAdd (Θ.symm (Additive.ofMul (secMk Sx N x))) := fun x => rfl
  have hΘsymm : ∀ (g : SL(n, F)) (u : Additive (SecQuot Sx N)),
      Θ.symm (g • u) = fun l => g • (Θ.symm u) l := by
    intro g u
    apply Θ.injective
    rw [AddEquiv.apply_symm_apply, hΘ g (Θ.symm u), AddEquiv.apply_symm_apply]
  refine ⟨s, φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨a, ha⟩ : ∃ a : SecQuot Sx N, Additive.ofMul a = Θ (Multiplicative.toAdd v) :=
      ⟨Additive.toMul (Θ (Multiplicative.toAdd v)), rfl⟩
    obtain ⟨x, rfl⟩ := secMk_surjective (A := Sx) (B := N) a
    refine ⟨x, ?_⟩
    rw [hφ, ha, AddEquiv.symm_apply_apply]
    rfl
  · intro x
    rw [hφ]
    constructor
    · intro hx
      have h1 : Θ.symm (Additive.ofMul (secMk Sx N x)) = 0 := hx
      have h2 : Additive.ofMul (secMk Sx N x) = 0 := by
        have := congrArg Θ h1
        rwa [AddEquiv.apply_symm_apply, map_zero] at this
      exact secMk_eq_one_iff.1 h2
    · intro hx
      have h1 : secMk Sx N x = 1 := secMk_eq_one_iff.2 hx
      rw [h1]
      show Multiplicative.ofAdd (Θ.symm (0 : Additive (SecQuot Sx N))) = 1
      rw [map_zero]
      rfl
  · intro m g x y hg hy
    have hyx : y = ⟨(m : G) * x * (m : G)⁻¹, Q.nS m m.2 x x.2⟩ := Subtype.ext hy
    have h1 : Additive.ofMul (secMk Sx N y) = g • Additive.ofMul (secMk Sx N x) := by
      rw [hact g m x hg, hyx]
    rw [hφ, hφ, h1, hΘsymm]
    rfl
  · intro k x
    rw [← hmemY k x, hmem k]
    constructor
    · rintro ⟨a, ha⟩ l j hj
      have h1 : Θ.symm (Additive.ofMul (secMk Sx N x)) = fun l => Pi.single k (a l) := by
        rw [ha, AddEquiv.symm_apply_apply]
      show (Θ.symm (Additive.ofMul (secMk Sx N x))) l j = 0
      rw [h1]
      simp [hj]
    · intro h0
      refine ⟨fun l => (Θ.symm (Additive.ofMul (secMk Sx N x))) l k, ?_⟩
      have h1 : (fun l => Pi.single k ((Θ.symm (Additive.ofMul (secMk Sx N x))) l k) :
          Fin s → Fin n → F) = Θ.symm (Additive.ofMul (secMk Sx N x)) := by
        funext l j
        by_cases hj : j = k
        · subst hj
          simp
        · rw [Pi.single_eq_of_ne hj]
          exact (h0 l j hj).symm
      rw [h1, AddEquiv.apply_symm_apply]
  · have h1 : Nat.card ↥(Y (idx0 hn)) = Nat.card ↥(secImg Sx N (A (idx0 hn))) :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun a => Iff.rfl))
    rw [h1] at hcard
    let f : ↥(A (idx0 hn)) →* SecQuot Sx N :=
      (secMk Sx N).comp (Subgroup.inclusion (hA.le_Sx (idx0 hn)))
    have hker0 : f.ker = N.subgroupOf (A (idx0 hn)) := by
      ext w
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact secMk_eq_one_iff
    have hrange : f.range = secImg Sx N (A (idx0 hn)) := by
      ext z
      rw [MonoidHom.mem_range, mem_secImg]
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨Subgroup.inclusion (hA.le_Sx _) w, w.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    have h2 := Subgroup.card_ker_mul_card_range f
    rw [hker0, hrange, hcard,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hA.N_le (idx0 hn))).toEquiv] at h2
    exact h2.symm

end CFSG.Quasithin
