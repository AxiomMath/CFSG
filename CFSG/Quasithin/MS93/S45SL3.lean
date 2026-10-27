module

public import CFSG.Quasithin.MS93.ML3Sec
public import CFSG.Quasithin.MS93.S4AEA

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Assembly.LowTwoRank
open scoped Matrix commutatorElement

section Transport

variable {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}

theorem isSumOfNaturalModulesVia_sup {K V V₁ B Z : Subgroup G} {ψ : ↥K →* ↥Γ} {dual : Bool}
    {k : ℕ} (h : IsSumOfNaturalModulesVia K V₁ Z ψ dual k)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hn : V₁ ≤ Subgroup.normalizer (B : Set G)) (hsup : V₁ ⊔ B = V) (hinf : V₁ ⊓ B = Z) :
    IsSumOfNaturalModulesVia K V B ψ dual k := by
  classical
  obtain ⟨hKV₁, hZV₁, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := h
  have hV₁V : V₁ ≤ V := hsup ▸ le_sup_left
  have hBV : B ≤ V := hsup ▸ le_sup_right
  have hZB : Z ≤ B := hinf ▸ inf_le_right
  have hdec : ∀ v : ↥V, ∃ x : ↥V₁, ∃ y : ↥B, (x : G) * y = v := by
    intro v
    have hv : (v : G) ∈ ((V₁ ⊔ B : Subgroup G) : Set G) := by rw [hsup]; exact v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V₁ B hn] at hv
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hv
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩
  choose a b hab using hdec
  have hker : ∀ x : ↥V₁, β₁ x = 1 ↔ (x : G) ∈ Z := fun x => by
    rw [← MonoidHom.mem_ker, hβ₁k, Subgroup.mem_subgroupOf]
  have hwd : ∀ (x x' : ↥V₁) (y y' : ↥B), (x : G) * y = x' * y' → β₁ x = β₁ x' := by
    intro x x' y y' hxy
    have hz : ((x'⁻¹ * x : ↥V₁) : G) ∈ Z := by
      rw [← hinf]
      refine ⟨(x'⁻¹ * x).2, ?_⟩
      have e : ((x'⁻¹ * x : ↥V₁) : G) = y' * (y : G)⁻¹ := by
        show (x' : G)⁻¹ * x = y' * (y : G)⁻¹
        calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * y) * (y : G)⁻¹ := by group
          _ = (x' : G)⁻¹ * (x' * y') * (y : G)⁻¹ := by rw [hxy]
          _ = y' * (y : G)⁻¹ := by group
      rw [e]
      exact B.mul_mem y'.2 (B.inv_mem y.2)
    have := (hker _).mpr hz
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  let β : ↥V →* Multiplicative (Fin k → ι → F) :=
    { toFun := fun v => β₁ (a v)
      map_one' := by
        have := hwd (a 1) 1 (b 1) 1 (by rw [hab]; simp)
        rw [this, map_one]
      map_mul' := fun v w => by
        have hy : (a w : G)⁻¹ * b v * a w ∈ B := by
          have := (Subgroup.mem_normalizer_iff.mp (hn (V₁.inv_mem (a w).2)) (b v)).mp (b v).2
          simpa using this
        have := hwd (a (v * w)) (a v * a w) (b (v * w)) (⟨_, hy⟩ * b w) (by
          rw [hab]
          show (v : G) * w = a v * a w * ((a w : G)⁻¹ * b v * a w * b w)
          rw [← hab v, ← hab w]
          group)
        rw [this, map_mul] }
  have hβ : ∀ v, β v = β₁ (a v) := fun _ => rfl
  refine ⟨hKV, hBV, β, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨x, rfl⟩ := hβ₁s t
    refine ⟨⟨x, hV₁V x.2⟩, ?_⟩
    rw [hβ]
    exact hwd _ x _ 1 (by rw [hab]; simp)
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hβ, hker]
    constructor
    · intro hz
      rw [← hab v]
      exact B.mul_mem (hZB hz) (b v).2
    · intro hv
      have := hwd (a v) 1 (b v) ⟨v, hv⟩ (by rw [hab]; simp)
      rw [map_one] at this
      exact (hker _).mp this
  · intro g u v huv i
    have hx : (g : G) * a u * (g : G)⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKV₁ g.2) _).mp (a u).2
    have hy : (g : G) * b u * (g : G)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hKB g.2) _).mp (b u).2
    have e := hwd (a v) ⟨_, hx⟩ (b v) ⟨_, hy⟩ (by
      rw [hab, huv]
      show (g : G) * u * (g : G)⁻¹ = (g : G) * a u * (g : G)⁻¹ * ((g : G) * b u * (g : G)⁻¹)
      rw [← hab u]
      group)
    rw [hβ, hβ, e]
    exact hβ₁e g (a u) ⟨_, hx⟩ rfl i

end Transport

section Faithful

variable {G : Type} [Group G] {F : Type} [Field F]

theorem eq_one_of_natAct_mulVec_eq_self (dual : Bool) {g : SL3 F}
    (hfix : ∀ y : Fin 3 → F, natAct dual g *ᵥ y = y) : g = 1 := by
  cases dual with
  | false =>
    exact eq_one_of_mulVec_eq_self fun y => by
      have := hfix y
      rwa [natAct_false] at this
  | true =>
    have hd : dualMat g = 1 := by
      apply Matrix.ext_of_mulVec_single
      intro i
      have := hfix (Pi.single i 1)
      rw [natAct_true] at this
      rw [this, Matrix.one_mulVec]
    have hinv : g⁻¹ = 1 := by
      apply Subtype.ext
      have : (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ = 1 := hd
      rw [← Matrix.transpose_transpose (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)),
        this, Matrix.transpose_one]
      rfl
    exact inv_eq_one.mp hinv

theorem toSL3_eq_one_of_conj {K V Z : Subgroup G}
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} {dual : Bool}
    (h : IsSumOfNaturalModulesVia K V Z α dual 1) (l : ↥K)
    (hl : ∀ v ∈ V, v⁻¹ * ((l : G) * v * (l : G)⁻¹) ∈ Z) : toSL3 α l = 1 := by
  set N := NatSec.ofIsSum h with hN
  have hfix : ∀ y : Fin 3 → F, natAct dual (toSL3 α l) *ᵥ y = y := by
    intro y
    obtain ⟨v, hv, rfl⟩ := N.exists_coord_eq y
    have h1 := (N.coord_eq_zero_iff (V.mul_mem (V.inv_mem hv) (N.conj_mem l hv))).mpr (hl v hv)
    rw [N.coord_mul (V.inv_mem hv) (N.conj_mem l hv), N.coord_inv hv, N.coord_conj l hv,
      neg_add_eq_zero] at h1
    exact h1.symm
  exact eq_one_of_natAct_mulVec_eq_self dual hfix

end Faithful

section Line

variable {F : Type} [Field F]

theorem rootElt01_conj_mem_qLn (c : F) {g : SL3 F} (hg : g ∈ (qLn : Subgroup (SL3 F))) :
    rootElt 0 1 c * g * (rootElt 0 1 c)⁻¹ ∈ (qLn : Subgroup (SL3 F)) := by
  obtain ⟨b, d, rfl⟩ := mem_qLn_iff_uniTri.mp hg
  refine mem_qLn_iff_uniTri.mpr ⟨b + c * d, d, ?_⟩
  rw [rootElt01_eq_uniTri, uniTri_inv, uniTri_mul, uniTri_mul]
  congr 1 <;> ring

theorem rootElt10_conj_mem_qLn (c : F) {g : SL3 F} (hg : g ∈ (qLn : Subgroup (SL3 F))) :
    rootElt 1 0 c * g * (rootElt 1 0 c)⁻¹ ∈ (qLn : Subgroup (SL3 F)) := by
  obtain ⟨b, d, rfl⟩ := mem_qLn_iff_uniTri.mp hg
  refine mem_qLn_iff_uniTri.mpr ⟨b, d + c * b, ?_⟩
  rw [← rootElt_neg]
  apply Subtype.ext
  rw [coe_mul_SL3, coe_mul_SL3, coe_rootElt (by decide), coe_rootElt (by decide), coe_uniTri,
    coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
  all_goals ring

theorem mem_of_ln01_invariant (S : AddSubgroup (Fin 3 → F)) (hS : ∀ y ∈ S, y ∈ ln01)
    (hne : ∃ y ∈ S, y ≠ 0)
    (h01 : ∀ c : F, ∀ y ∈ S, ((rootElt 0 1 c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ S)
    (h10 : ∀ c : F, ∀ y ∈ S, ((rootElt 1 0 c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ S) :
    ∀ y ∈ (ln01 : Submodule F (Fin 3 → F)), y ∈ S := by
  have hd : ∀ (i j : Fin 3), i ≠ j → (∀ c : F, ∀ y ∈ S,
      ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ S) →
      ∀ c : F, ∀ y ∈ S, Pi.single i (c * y j) ∈ S := by
    intro i j hij hS' c y hy
    have := S.sub_mem (hS' c y hy) hy
    rwa [rootElt_mulVec hij, add_sub_cancel_left] at this
  obtain ⟨s, hs, hs0⟩ := hne
  have hs2 : s 2 = 0 := hS s hs
  have he0 : ∀ t : F, Pi.single 0 t ∈ S := by
    by_cases h1 : s 1 = 0
    · have h0 : s 0 ≠ 0 := by
        intro h0
        apply hs0
        funext k
        fin_cases k <;> simp [h0, h1, hs2]
      intro t
      have e1 := hd 1 0 (by decide) h10 (1 / s 0) s hs
      rw [div_mul_cancel₀ _ h0] at e1
      have := hd 0 1 (by decide) h01 t _ e1
      simpa using this
    · intro t
      have := hd 0 1 (by decide) h01 (t / s 1) s hs
      rwa [div_mul_cancel₀ _ h1] at this
  have he1 : ∀ t : F, Pi.single 1 t ∈ S := by
    intro t
    have := hd 1 0 (by decide) h10 t _ (he0 1)
    simpa using this
  intro y hy
  have hy2 : y 2 = 0 := hy
  have e : y = Pi.single 0 (y 0) + Pi.single 1 (y 1) := by
    funext k
    fin_cases k <;> simp [hy2]
  rw [e]
  exact S.add_mem (he0 _) (he1 _)

theorem mem_of_normalizer_invariant [Finite F] [CharP F 2] {A : Subgroup (SL3 F)}
    (hA : IsPGroup 2 A) (hAc : Nat.card A = Nat.card F ^ 2) (hfc : fixN A = commN A)
    (h2 : Module.finrank F (commN A) = 2) (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ y ∈ S, y ∈ fixN A) (hne : ∃ y ∈ S, y ≠ 0)
    (hinv : ∀ g ∈ Subgroup.normalizer (A : Set (SL3 F)),
      ∀ y ∈ S, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ S) :
    ∀ y ∈ fixN A, y ∈ S := by
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hA
  set A' := A.map (MulAut.conj x).toMonoidHom with hA'
  have hC' : commN A' = ln01 := by
    apply Submodule.eq_of_le_of_finrank_eq (commN_le_ln01_of_le_sStar hx)
    rw [finrank_commN_map_conj, h2, finrank_ln01]
  have hF' : fixN A' = ln01 := by rw [hA', fixN_map_conj, hfc, ← commN_map_conj, ← hA', hC']
  have hA'q : A' = qLn := by
    have hle : A' ≤ qLn := by
      intro g hg
      obtain ⟨a, b, d, rfl⟩ := mem_sStar_iff.mp (hx hg)
      have he1 : ((uniTri a b d : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] = ![0, 1, 0] :=
        (show ![0, 1, 0] ∈ fixN A' by rw [hF']; rfl) _ hg
      have ha : a = 0 := by
        have := congrFun he1 0
        simpa [uniTri_mulVec] using this
      subst ha
      exact mem_qLn_iff_uniTri.mpr ⟨b, d, rfl⟩
    have hcard : Nat.card A' = Nat.card F ^ 2 := by
      rw [hA', ← hAc]
      exact Nat.card_congr (Subgroup.equivMapOfInjective A _
        (MulAut.conj x).injective).toEquiv.symm
    have : Finite (qLn : Subgroup (SL3 F)) := Nat.finite_of_card_ne_zero (by
      rw [card_qLn]; exact pow_ne_zero _ Nat.card_pos.ne')
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_qLn, hcard])
  set e := Matrix.SpecialLinearGroup.toLin' x with he
  set S' : AddSubgroup (Fin 3 → F) := S.map (e : (Fin 3 → F) →+ (Fin 3 → F)) with hS'
  have hxS : ∀ y, ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y = e y := fun y => by
    simp [he, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  have hconj : ∀ g : SL3 F, g ∈ Subgroup.normalizer (A' : Set (SL3 F)) → ∀ y ∈ S',
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ S' := by
    rintro g hg _ ⟨y, hy, rfl⟩
    have fwd : ∀ g ∈ Subgroup.normalizer (A' : Set (SL3 F)), ∀ a ∈ A,
        (x⁻¹ * g * x) * a * (x⁻¹ * g * x)⁻¹ ∈ A := by
      intro g hg a ha
      have h1 : x * a * x⁻¹ ∈ A' := ⟨a, ha, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hg _).mp h1
      obtain ⟨a', ha', ha'e⟩ := h2
      have : (x⁻¹ * g * x) * a * (x⁻¹ * g * x)⁻¹ = a' := by
        have e2 : x * a' * x⁻¹ = g * (x * a * x⁻¹) * g⁻¹ := ha'e
        calc (x⁻¹ * g * x) * a * (x⁻¹ * g * x)⁻¹ = x⁻¹ * (g * (x * a * x⁻¹) * g⁻¹) * x := by
              group
          _ = x⁻¹ * (x * a' * x⁻¹) * x := by rw [e2]
          _ = a' := by group
      rw [this]; exact ha'
    have hgA : x⁻¹ * g * x ∈ Subgroup.normalizer (A : Set (SL3 F)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      refine ⟨fwd g hg a, fun ha => ?_⟩
      have := fwd g⁻¹ (inv_mem hg) _ ha
      have e3 : (x⁻¹ * g⁻¹ * x) * ((x⁻¹ * g * x) * a * (x⁻¹ * g * x)⁻¹) *
          (x⁻¹ * g⁻¹ * x)⁻¹ = a := by group
      rwa [e3] at this
    have h3 := hinv _ hgA y hy
    refine ⟨_, h3, ?_⟩
    show e (((x⁻¹ * g * x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e y
    rw [← hxS, ← hxS, coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec (v := (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ _)),
      ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]
  have hS'ln : ∀ y ∈ S', y ∈ ln01 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hF', hA', fixN_map_conj]
    exact ⟨y, hS y hy, rfl⟩
  have hne' : ∃ y ∈ S', y ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := hne
    exact ⟨e y, ⟨y, hy, rfl⟩, fun h => hy0 (e.injective (by rw [h, map_zero]))⟩
  have hnorm : ∀ (i j : Fin 3), i ≠ j → (∀ c : F, ∀ g ∈ (qLn : Subgroup (SL3 F)),
      rootElt i j c * g * (rootElt i j c)⁻¹ ∈ (qLn : Subgroup (SL3 F))) →
      ∀ c : F, rootElt i j c ∈ Subgroup.normalizer (A' : Set (SL3 F)) := by
    intro i j _ hq c
    rw [Subgroup.mem_normalizer_iff, hA'q]
    intro g
    refine ⟨hq c g, fun hg => ?_⟩
    have := hq (-c) _ hg
    rw [rootElt_neg, inv_inv] at this
    have e : (rootElt i j c)⁻¹ * (rootElt i j c * g * (rootElt i j c)⁻¹) * rootElt i j c = g := by
      group
    rwa [e] at this
  have hall := mem_of_ln01_invariant S' hS'ln hne'
    (fun c => hconj _ (hnorm 0 1 (by decide) (fun c g hg => rootElt01_conj_mem_qLn c hg) c))
    (fun c => hconj _ (hnorm 1 0 (by decide) (fun c g hg => rootElt10_conj_mem_qLn c hg) c))
  intro y hy
  have hey : e y ∈ ln01 := by
    rw [← hF', hA', fixN_map_conj]
    exact ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hy'e⟩ := hall _ hey
  rw [show y = y' from e.injective hy'e.symm]
  exact hy'

end Line

section DualLine

variable {F : Type} [Field F]

omit [Field F] in
theorem conj_mem_normalizer {Γ : Type*} [Group Γ] {A : Subgroup Γ} (x : Γ) {g : Γ}
    (hg : g ∈ Subgroup.normalizer ((A.map (MulAut.conj x).toMonoidHom : Subgroup Γ) : Set Γ)) :
    x⁻¹ * g * x ∈ Subgroup.normalizer (A : Set Γ) := by
  have fwd : ∀ g ∈ Subgroup.normalizer ((A.map (MulAut.conj x).toMonoidHom : Subgroup Γ) :
      Set Γ), ∀ a ∈ A, (x⁻¹ * g * x) * a * (x⁻¹ * g * x)⁻¹ ∈ A := by
    intro g hg a ha
    have h1 : x * a * x⁻¹ ∈ A.map (MulAut.conj x).toMonoidHom := ⟨a, ha, rfl⟩
    obtain ⟨a', ha', ha'e⟩ := (Subgroup.mem_normalizer_iff.mp hg _).mp h1
    have e2 : x * a' * x⁻¹ = g * (x * a * x⁻¹) * g⁻¹ := ha'e
    have : (x⁻¹ * g * x) * a * (x⁻¹ * g * x)⁻¹ = a' := by
      calc (x⁻¹ * g * x) * a * (x⁻¹ * g * x)⁻¹ = x⁻¹ * (g * (x * a * x⁻¹) * g⁻¹) * x := by
            group
        _ = x⁻¹ * (x * a' * x⁻¹) * x := by rw [e2]
        _ = a' := by group
    rw [this]; exact ha'
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fwd g hg a, fun ha => ?_⟩
  have := fwd g⁻¹ (inv_mem hg) _ ha
  have e3 : (x⁻¹ * g⁻¹ * x) * ((x⁻¹ * g * x) * a * (x⁻¹ * g * x)⁻¹) * (x⁻¹ * g⁻¹ * x)⁻¹ = a := by
    group
  rwa [e3] at this

theorem exists_conj_eq_qLn [Finite F] [CharP F 2] {A : Subgroup (SL3 F)} (hA : IsPGroup 2 A)
    (hAc : Nat.card A = Nat.card F ^ 2) (hfc : fixN A = commN A)
    (h2 : Module.finrank F (commN A) = 2) :
    ∃ x : SL3 F, A.map (MulAut.conj x).toMonoidHom = qLn := by
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hA
  refine ⟨x, ?_⟩
  set A' := A.map (MulAut.conj x).toMonoidHom with hA'
  have hC' : commN A' = ln01 := by
    apply Submodule.eq_of_le_of_finrank_eq (commN_le_ln01_of_le_sStar hx)
    rw [finrank_commN_map_conj, h2, finrank_ln01]
  have hF' : fixN A' = ln01 := by rw [hA', fixN_map_conj, hfc, ← commN_map_conj, ← hA', hC']
  have hle : A' ≤ qLn := by
    intro g hg
    obtain ⟨a, b, d, rfl⟩ := mem_sStar_iff.mp (hx hg)
    have he1 : ((uniTri a b d : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] = ![0, 1, 0] :=
      (show ![0, 1, 0] ∈ fixN A' by rw [hF']; rfl) _ hg
    have ha : a = 0 := by
      have := congrFun he1 0
      simpa [uniTri_mulVec] using this
    subst ha
    exact mem_qLn_iff_uniTri.mpr ⟨b, d, rfl⟩
  have hcard : Nat.card A' = Nat.card F ^ 2 := by
    rw [hA', ← hAc]
    exact Nat.card_congr (Subgroup.equivMapOfInjective A _
      (MulAut.conj x).injective).toEquiv.symm
  have : Finite (qLn : Subgroup (SL3 F)) := Nat.finite_of_card_ne_zero (by
    rw [card_qLn]; exact pow_ne_zero _ Nat.card_pos.ne')
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_qLn, hcard])

theorem dualMat_qLn_fix_iff (y : Fin 3 → F) :
    (∀ g ∈ (qLn : Subgroup (SL3 F)), dualMat g *ᵥ y = y) ↔ y 0 = 0 ∧ y 1 = 0 := by
  constructor
  · intro h
    have h1 := h (rootElt 0 2 1) (rootGroup_le_qLn ⟨1, rfl⟩)
    have h2 := h (rootElt 1 2 1) (le_sup_right (a := rootGroup 0 2) ⟨1, rfl⟩)
    rw [dualMat_rootElt_mulVec (by decide)] at h1 h2
    have e1 := congrFun h1 2
    have e2 := congrFun h2 2
    simp at e1 e2
    exact ⟨e1, e2⟩
  · rintro ⟨h0, h1⟩ g hg
    obtain ⟨b, c, rfl⟩ := mem_qLn_iff_uniTri.mp hg
    rw [dualMat, uniTri_inv, coe_uniTri]
    funext k
    fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1]

@[expose] noncomputable def diagLn (l : F) (hl : l ≠ 0) : SL3 F :=
  Matrix.SpecialLinearGroup.diag2n (show (1 : Fin 3) ≠ 2 by decide) l hl

theorem dualMat_diagLn_mulVec (l : F) (hl : l ≠ 0) (y : Fin 3 → F) :
    dualMat (diagLn l hl) *ᵥ y = ![y 0, l⁻¹ * y 1, l * y 2] := by
  have hinv : (diagLn l hl)⁻¹ = diagLn l⁻¹ (inv_ne_zero hl) := by
    rw [inv_eq_iff_mul_eq_one]
    apply Subtype.ext
    rw [coe_mul_SL3, diagLn, diagLn, Matrix.SpecialLinearGroup.diag2n_coe,
      Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal, coe_one_SL3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hl]
  rw [dualMat, hinv, diagLn, Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_transpose]
  funext k
  fin_cases k <;> simp [Matrix.mulVec_diagonal]

theorem diagLn_mem_normalizer_qLn (l : F) (hl : l ≠ 0) :
    diagLn l hl ∈ Subgroup.normalizer ((qLn : Subgroup (SL3 F)) : Set (SL3 F)) := by
  have key : ∀ (l : F) (hl : l ≠ 0), ∀ g ∈ (qLn : Subgroup (SL3 F)),
      diagLn l hl * g * (diagLn l hl)⁻¹ ∈ (qLn : Subgroup (SL3 F)) := by
    intro l hl g hg
    obtain ⟨b, c, rfl⟩ := mem_qLn_iff_uniTri.mp hg
    refine mem_qLn_iff_uniTri.mpr ⟨b * l, l * c * l, ?_⟩
    have hinv : (diagLn l hl)⁻¹ = diagLn l⁻¹ (inv_ne_zero hl) := by
      rw [inv_eq_iff_mul_eq_one]
      apply Subtype.ext
      rw [coe_mul_SL3, diagLn, diagLn, Matrix.SpecialLinearGroup.diag2n_coe,
        Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal, coe_one_SL3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hl]
    rw [hinv]
    apply Subtype.ext
    rw [coe_mul_SL3, coe_mul_SL3, diagLn, diagLn, Matrix.SpecialLinearGroup.diag2n_coe,
      Matrix.SpecialLinearGroup.diag2n_coe, coe_uniTri, coe_uniTri]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal, hl]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key l hl g, fun hg => ?_⟩
  have h1 := key l⁻¹ (inv_ne_zero hl) _ hg
  have hinv : (diagLn l hl)⁻¹ = diagLn l⁻¹ (inv_ne_zero hl) := by
    rw [inv_eq_iff_mul_eq_one]
    apply Subtype.ext
    rw [coe_mul_SL3, diagLn, diagLn, Matrix.SpecialLinearGroup.diag2n_coe,
      Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal, coe_one_SL3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hl]
  rw [← hinv] at h1
  have e : (diagLn l hl)⁻¹ * (diagLn l hl * g * (diagLn l hl)⁻¹) * (diagLn l hl)⁻¹⁻¹ = g := by
    group
  rwa [e] at h1

theorem dual_fix_of_normalizer [Finite F] [CharP F 2] {A : Subgroup (SL3 F)}
    (hA : IsPGroup 2 A) (hAc : Nat.card A = Nat.card F ^ 2) (hfc : fixN A = commN A)
    (h2 : Module.finrank F (commN A) = 2) :
    (∀ S : AddSubgroup (Fin 3 → F), (∀ y ∈ S, ∀ a ∈ A, dualMat a *ᵥ y = y) →
      (∃ y ∈ S, y ≠ 0) →
      (∀ g ∈ Subgroup.normalizer (A : Set (SL3 F)), ∀ y ∈ S, dualMat g *ᵥ y ∈ S) →
      ∀ y : Fin 3 → F, (∀ a ∈ A, dualMat a *ᵥ y = y) → y ∈ S) ∧
    (∃ (e : F → (Fin 3 → F)), Function.Injective e ∧ ∀ t a, a ∈ A → dualMat a *ᵥ e t = e t) ∧
    (∀ l : F, l ≠ 0 → l ≠ 1 → ∃ g ∈ Subgroup.normalizer (A : Set (SL3 F)),
      ∀ y : Fin 3 → F, (∀ a ∈ A, dualMat a *ᵥ y = y) → dualMat g *ᵥ y = y → y = 0) := by
  obtain ⟨x, hx⟩ := exists_conj_eq_qLn hA hAc hfc h2
  set X := dualMat x with hX
  set Xi := dualMat x⁻¹ with hXi
  have hXXi : ∀ y, X *ᵥ (Xi *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hX, hXi, ← dualMat_mul, mul_inv_cancel, dualMat_one,
      Matrix.one_mulVec]
  have hXiX : ∀ y, Xi *ᵥ (X *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hX, hXi, ← dualMat_mul, inv_mul_cancel, dualMat_one,
      Matrix.one_mulVec]
  have hfixA : ∀ y, (∀ a ∈ A, dualMat a *ᵥ y = y) ↔ (X *ᵥ y) 0 = 0 ∧ (X *ᵥ y) 1 = 0 := by
    intro y
    rw [← dualMat_qLn_fix_iff, ← hx]
    constructor
    · rintro hy _ ⟨a, ha, rfl⟩
      show dualMat (x * a * x⁻¹) *ᵥ (X *ᵥ y) = X *ᵥ y
      rw [dualMat_mul, dualMat_mul, ← hX, ← hXi, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hXiX, hy a ha]
    · intro hy a ha
      have := hy _ ⟨a, ha, rfl⟩
      change dualMat (x * a * x⁻¹) *ᵥ (X *ᵥ y) = X *ᵥ y at this
      rw [dualMat_mul, dualMat_mul, ← hX, ← hXi, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hXiX] at this
      have := congrArg (Xi *ᵥ ·) this
      simpa only [hXiX] using this
  have hnorm : ∀ g ∈ Subgroup.normalizer ((qLn : Subgroup (SL3 F)) : Set (SL3 F)),
      x⁻¹ * g * x ∈ Subgroup.normalizer (A : Set (SL3 F)) := fun g hg =>
    conj_mem_normalizer x (by rw [hx]; exact hg)
  have hdl : ∀ (l : F) (hl : l ≠ 0) (y : Fin 3 → F),
      X *ᵥ (dualMat (x⁻¹ * diagLn l hl * x) *ᵥ y) = ![(X *ᵥ y) 0, l⁻¹ * (X *ᵥ y) 1,
        l * (X *ᵥ y) 2] := by
    intro l hl y
    rw [dualMat_mul, dualMat_mul, ← hX, ← hXi, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hXXi, dualMat_diagLn_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · intro S hS hne hinv y hy
    obtain ⟨s, hs, hs0⟩ := hne
    have hsA := (hfixA s).mp (hS s hs)
    have hs2 : (X *ᵥ s) 2 ≠ 0 := by
      intro h2'
      apply hs0
      have : X *ᵥ s = 0 := by
        funext k; fin_cases k
        · exact hsA.1
        · exact hsA.2
        · exact h2'
      have := congrArg (Xi *ᵥ ·) this
      simpa only [hXiX, Matrix.mulVec_zero] using this
    have hyA := (hfixA y).mp hy
    by_cases hy2 : (X *ᵥ y) 2 = 0
    · have : y = 0 := by
        have : X *ᵥ y = 0 := by
          funext k; fin_cases k
          · exact hyA.1
          · exact hyA.2
          · exact hy2
        have := congrArg (Xi *ᵥ ·) this
        simpa only [hXiX, Matrix.mulVec_zero] using this
      rw [this]; exact S.zero_mem
    · set l := (X *ᵥ y) 2 / (X *ᵥ s) 2 with hl
      have hl0 : l ≠ 0 := div_ne_zero hy2 hs2
      have h1 := hinv _ (hnorm _ (diagLn_mem_normalizer_qLn l hl0)) s hs
      have e : dualMat (x⁻¹ * diagLn l hl0 * x) *ᵥ s = y := by
        have h3 := hdl l hl0 s
        have h4 : X *ᵥ (dualMat (x⁻¹ * diagLn l hl0 * x) *ᵥ s) = X *ᵥ y := by
          rw [h3]
          funext k; fin_cases k
          · simp [hsA.1, hyA.1]
          · simp [hsA.2, hyA.2]
          · simp [hl, div_mul_cancel₀ _ hs2]
        have := congrArg (Xi *ᵥ ·) h4
        simpa only [hXiX] using this
      rw [← e]; exact h1
  · refine ⟨fun t => Xi *ᵥ ![0, 0, t], fun t t' htt => ?_, fun t a ha => ?_⟩
    · have := congrArg (X *ᵥ ·) htt
      simp only [hXXi] at this
      simpa using congrFun this 2
    · refine ((hfixA _).mpr ?_) a ha
      rw [hXXi]
      exact ⟨rfl, rfl⟩
  · intro l hl0 hl1
    refine ⟨x⁻¹ * diagLn l hl0 * x, hnorm _ (diagLn_mem_normalizer_qLn l hl0), fun y hy hfix => ?_⟩
    have hyA := (hfixA y).mp hy
    have h3 := hdl l hl0 y
    rw [hfix] at h3
    have h2' : (X *ᵥ y) 2 = 0 := by
      have := congrFun h3 2
      simp at this
      have : (l - 1) * (X *ᵥ y) 2 = 0 := by rw [sub_mul, one_mul, ← this, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hl1)
    have : X *ᵥ y = 0 := by
      funext k; fin_cases k
      · exact hyA.1
      · exact hyA.2
      · exact h2'
    have := congrArg (Xi *ᵥ ·) this
    simpa only [hXiX, Matrix.mulVec_zero] using this

end DualLine

end CFSG.Quasithin.MS93.S45
