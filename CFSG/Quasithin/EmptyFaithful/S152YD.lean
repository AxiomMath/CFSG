module

public import CFSG.Quasithin.EmptyFaithful.S152YC
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.S153DInputs

public section

namespace CFSG.Quasithin.S152Y

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Transport

variable {G : Type} [Group G]

@[expose] def coordHom {X : Type} [Group X] {k : ℕ} (β : X →* Multiplicative (Fin k → Vec3)) (i : Fin k) :
    X →* Multiplicative Vec3 :=
  (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin k => Vec3) i)).comp β

theorem normalize_via {K X Z : Subgroup G} {F : Type} [Field F] [Fintype F] {k : ℕ}
    (hF : Fintype.card F = 2) {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (h : IsSumOfNaturalModulesVia K X Z α false k) :
    ∃ (α' : ↥K →* SL3) (β' : ↥X →* Multiplicative (Fin k → Vec3)),
      Function.Surjective α' ∧ α'.ker = α.ker ∧ Function.Surjective β' ∧ β'.ker = Z.subgroupOf X ∧
      ∀ (a : ↥K) (u v : ↥X), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
        Multiplicative.toAdd (β' v) i = mulV (α' a) (Multiplicative.toAdd (β' u) i) := by
  classical
  obtain ⟨hKX, hZX, β, hβs, hβk, hβe⟩ := h
  let e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by rw [hF, ZMod.card])
  let Φ : ↥(StatedSL 3 F) →* SL3 :=
    (Matrix.SpecialLinearGroup.map (e : F →+* ZMod 2)).comp
      (specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom
  have hΦcoe : ∀ g : ↥(StatedSL 3 F), ((Φ g : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (e : F →+* ZMod 2).mapMatrix ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g
    have h1 := specialLinearGroupEquivStatedSL_coe 3 F ((specialLinearGroupEquivStatedSL 3 F).symm g)
    rw [MulEquiv.apply_symm_apply] at h1
    show ((Matrix.SpecialLinearGroup.map (e : F →+* ZMod 2)
      ((specialLinearGroupEquivStatedSL 3 F).symm g) : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
    rw [Matrix.SpecialLinearGroup.map_apply_coe, ← h1]
  have hΦinj : Function.Injective Φ := by
    intro g g' hgg
    have h1 := hΦcoe g
    have h2 := hΦcoe g'
    rw [hgg] at h1
    have h3 : (e : F →+* ZMod 2).mapMatrix ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (e : F →+* ZMod 2).mapMatrix ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
      h1.symm.trans h2
    have h4 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := Matrix.map_injective e.injective h3
    exact Subtype.ext (Units.ext h4)
  have hΦsurj : Function.Surjective Φ := by
    intro B
    refine ⟨specialLinearGroupEquivStatedSL 3 F
      (Matrix.SpecialLinearGroup.map (e.symm : ZMod 2 →+* F) B), ?_⟩
    show Matrix.SpecialLinearGroup.map (e : F →+* ZMod 2)
      ((specialLinearGroupEquivStatedSL 3 F).symm (specialLinearGroupEquivStatedSL 3 F
        (Matrix.SpecialLinearGroup.map (e.symm : ZMod 2 →+* F) B))) = B
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    simp
  let εa : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → ZMod 2) :=
    AddMonoidHom.mk' (fun v i j => e (v i j)) (fun a b => by ext i j; simp [map_add])
  let εm : Multiplicative (Fin k → Fin 3 → F) →* Multiplicative (Fin k → Vec3) :=
    AddMonoidHom.toMultiplicative εa
  have hεinj : Function.Injective εm := by
    intro a b hab
    have h1 : Multiplicative.toAdd (εm a) = Multiplicative.toAdd (εm b) := congrArg Multiplicative.toAdd hab
    have h2 : ∀ i j, e (Multiplicative.toAdd a i j) = e (Multiplicative.toAdd b i j) :=
      fun i j => congrFun (congrFun h1 i) j
    apply Multiplicative.toAdd.injective
    funext i j
    exact e.injective (h2 i j)
  have hεsurj : Function.Surjective εm := by
    intro w
    refine ⟨Multiplicative.ofAdd (fun i j => e.symm (Multiplicative.toAdd w i j)), ?_⟩
    apply Multiplicative.toAdd.injective
    funext i j
    show e (e.symm (Multiplicative.toAdd w i j)) = Multiplicative.toAdd w i j
    simp
  refine ⟨Φ.comp α, εm.comp β, hΦsurj.comp hα, MonoidHom.ker_comp_of_injective α Φ hΦinj,
    hεsurj.comp hβs, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective β εm hεinj, hβk]
  · intro a u v huv i
    have h1 := hβe a u v huv i
    have h2 : (moduleAct false (α a : Matrix.GeneralLinearGroup (Fin 3) F)) =
        ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      simp [moduleAct]
    rw [h2] at h1
    show (fun j => e (Multiplicative.toAdd (β v) i j)) =
      mulV (Φ (α a)) (fun j => e (Multiplicative.toAdd (β u) i j))
    funext j
    rw [h1]
    unfold mulV
    rw [hΦcoe (α a)]
    exact RingHom.map_mulVec (e : F →+* ZMod 2) _ (Multiplicative.toAdd (β u) i) j

end Transport

section Cases

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_mult_fun (F : Type) [Fintype F] (k : ℕ) :
    Nat.card (Multiplicative (Fin k → Fin 3 → F)) = (Fintype.card F ^ 3) ^ k := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_multiplicative]

omit [Finite G] in
theorem comm_of_sq {W : Subgroup G} (hsq : ∀ a ∈ W, a * a = 1) {a b : G} (ha : a ∈ W) (hb : b ∈ W) :
    a * b = b * a := by
  have h1 : a * b * (a * b) = 1 := hsq _ (W.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  have h2 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [h2, mul_inv_rev, ha', hb']

theorem three_of_card_two {C : Subgroup G} (h : Nat.card C = 2) {a b c : G} (ha : a ∈ C) (hb : b ∈ C)
    (hc : c ∈ C) : a = b ∨ a = c ∨ b = c := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hab, hac, hbc⟩ := hcon
  have : Fintype ↥C := Fintype.ofFinite _
  have h3 : (({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩} : Finset ↥C)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact hbc (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hab (congrArg Subtype.val h), fun h => hac (congrArg Subtype.val h)⟩
  have h4 := Finset.card_le_univ ({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩} : Finset ↥C)
  rw [h3, ← Nat.card_eq_fintype_card, h] at h4
  omega

structure L32Data (K R V W S : Subgroup G) (y : G) : Prop where
  hq : IsLnTwoQuot K 3
  vd : GVData K V S y
  hS : IsSylowTwoOf S K
  hVW : V ≤ W
  WQ : W ≤ c134Q (K ⊔ R) K
  Wsq : ∀ a ∈ W, a * a = 1
  Wnorm : K ≤ Subgroup.normalizer (W : Set G)
  Wtriv : ∀ k ∈ CFSG.Open.pCoreOf 2 K, ∀ x ∈ W, k * x * k⁻¹ = x
  Wcent : ∀ a ∈ W, ∀ q ∈ c134Q (K ⊔ R) K, a * q = q * a

omit [Finite G] in
theorem L32Data.closure_le {K R V W S : Subgroup G} {y : G} (d : L32Data K R V W S y) :
    Subgroup.closure {x : G | ∃ k ∈ K, ∃ z ∈ V, k * z * k⁻¹ = x} ≤ W := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, z, hz, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (d.Wnorm hk) z).mp (d.hVW hz)

omit [Finite G] in
theorem exists_commutator {K V S : Subgroup G} {y : G} (hV : GVData K V S y)
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) [Finite V] :
    ∀ v ∈ V, ∃ v' ∈ V, y * v' * y⁻¹ * v'⁻¹ = v := by
  classical
  have hyV : ∀ x : ↥V, y * (x : G) * y⁻¹ ∈ V := fun x =>
    (Subgroup.mem_normalizer_iff.mp hV.y_norm x).mp x.2
  let φ : ↥V → ↥V := fun x => ⟨y * (x : G) * y⁻¹ * (x : G)⁻¹, V.mul_mem (hyV x) (V.inv_mem x.2)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have hab' : y * (a : G) * y⁻¹ * (a : G)⁻¹ = y * (b : G) * y⁻¹ * (b : G)⁻¹ := congrArg Subtype.val hab
    have hq : y * (b : G) * y⁻¹ ∈ V := hyV b
    have hc : y * ((a : G) * (b : G)⁻¹) * y⁻¹ = (a : G) * (b : G)⁻¹ := by
      have hp : y * (a : G) * y⁻¹ = (y * (b : G) * y⁻¹ * (b : G)⁻¹) * (a : G) := by
        calc y * (a : G) * y⁻¹ = (y * (a : G) * y⁻¹ * (a : G)⁻¹) * (a : G) := by group
          _ = _ := by rw [hab']
      have hqc : (y * (b : G) * y⁻¹) * ((b : G)⁻¹ * (a : G)) = ((b : G)⁻¹ * (a : G)) * (y * (b : G) * y⁻¹) :=
        hcomm _ hq _ (V.mul_mem (V.inv_mem b.2) a.2)
      have hba : (b : G)⁻¹ * (a : G) = (a : G) * (b : G)⁻¹ := hcomm _ (V.inv_mem b.2) _ a.2
      calc y * ((a : G) * (b : G)⁻¹) * y⁻¹ = (y * (a : G) * y⁻¹) * (y * (b : G) * y⁻¹)⁻¹ := by group
        _ = ((y * (b : G) * y⁻¹) * ((b : G)⁻¹ * (a : G))) * (y * (b : G) * y⁻¹)⁻¹ := by
          rw [hp]; group
        _ = (((b : G)⁻¹ * (a : G)) * (y * (b : G) * y⁻¹)) * (y * (b : G) * y⁻¹)⁻¹ := by rw [hqc]
        _ = (b : G)⁻¹ * (a : G) := by group
        _ = (a : G) * (b : G)⁻¹ := hba
    have : (a : G) * (b : G)⁻¹ = 1 := hV.y_fpf _ (V.mul_mem a.2 (V.inv_mem b.2)) hc
    exact Subtype.ext (mul_inv_eq_one.mp this)
  intro v hv
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨v, hv⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

omit [Finite G] in
theorem card_mult_fin3 (F : Type) [Fintype F] :
    Nat.card (Multiplicative (Fin 3 → F)) = Fintype.card F ^ 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin]

end Cases

end CFSG.Quasithin.S152Y
