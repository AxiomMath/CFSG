module

public import CFSG.Quasithin.H13.NQBlockTerminalInputs
public import CFSG.Quasithin.H13.NQRigidBridge
public import CFSG.GroupTheory.SteinbergBKLinearPlaneSL2
public import CFSG.Quasithin.H13.NQSetupTwoStabilizer
public import CFSG.Quasithin.H13.NQBlockOriginalKSingleton
public import CFSG.Quasithin.H13.NQBlockStmt1317
public import CFSG.Quasithin.H13.NQTermTerminalFourWitness

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open scoped commutatorElement Pointwise

section Linear

open Matrix in
theorem exists_specialLinearGroup_apply_eq {k : Type*} [Field k] {V : Type*} [AddCommGroup V]
    [Module k V] (hV : Module.finrank k V = 2) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SpecialLinearGroup k V, g v = w := by
  classical
  have : Module.Finite k V := Module.finite_of_finrank_eq_succ hV
  let b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hV
  have hv' : b.equivFun v ≠ 0 := fun h0 => hv (b.equivFun.injective (h0.trans (map_zero _).symm))
  have hw' : b.equivFun w ≠ 0 := fun h0 => hw (b.equivFun.injective (h0.trans (map_zero _).symm))
  obtain ⟨s, hs⟩ := CFSG.GroupTheory.SteinbergBK.exists_sl2_mulVec_eq _ _ hv' hw'
  refine ⟨Matrix.SpecialLinearGroup.toLin_equiv b s, ?_⟩
  have h1 := LinearMap.congr_fun (Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq b s) v
  refine h1.trans ?_
  rw [Matrix.toLin_apply]
  have h2 : (s : Matrix (Fin 2) (Fin 2) k) *ᵥ ⇑(b.repr v) = b.equivFun w := hs
  rw [h2]
  exact b.sum_equivFun w

end Linear

section CommHom

variable {G : Type*} [Group G]

@[expose] def commHom (U : Subgroup G) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {b : G}
    (hb : b ∈ normalizer (U : Set G)) : U →* U where
  toFun u := ⟨b * u * b⁻¹ * (u : G)⁻¹,
    U.mul_mem ((mem_normalizer_iff.mp hb u).mp u.2) (U.inv_mem u.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hy : b * (y : G) * b⁻¹ ∈ U := (mem_normalizer_iff.mp hb y).mp y.2
    have h1 : (y : G)⁻¹ * (x : G)⁻¹ = (x : G)⁻¹ * (y : G)⁻¹ :=
      hUc _ (U.inv_mem y.2) _ (U.inv_mem x.2)
    have h3 : (b * y * b⁻¹) * (x : G)⁻¹ = (x : G)⁻¹ * (b * y * b⁻¹) :=
      hUc _ hy _ (U.inv_mem x.2)
    calc b * (x * y) * b⁻¹ * ((x : G) * y)⁻¹
        = (b * x * b⁻¹) * (b * y * b⁻¹) * ((y : G)⁻¹ * (x : G)⁻¹) := by group
      _ = (b * x * b⁻¹) * ((b * y * b⁻¹) * (x : G)⁻¹) * (y : G)⁻¹ := by rw [h1]; group
      _ = (b * x * b⁻¹) * ((x : G)⁻¹ * (b * y * b⁻¹)) * (y : G)⁻¹ := by rw [h3]
      _ = (b * x * b⁻¹ * (x : G)⁻¹) * (b * y * b⁻¹ * (y : G)⁻¹) := by group

theorem commHom_apply (U : Subgroup G) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {b : G}
    (hb : b ∈ normalizer (U : Set G)) (u : U) :
    ((commHom U hUc hb u : U) : G) = b * u * b⁻¹ * (u : G)⁻¹ :=
  rfl

theorem mem_ker_commHom (U : Subgroup G) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {b : G}
    (hb : b ∈ normalizer (U : Set G)) (u : U) :
    u ∈ (commHom U hUc hb).ker ↔ b * u = u * b := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, commHom_apply, Subgroup.coe_one]
  constructor
  · intro h1
    calc b * (u : G) = b * u * b⁻¹ * (u : G)⁻¹ * (u * b) := by group
      _ = u * b := by rw [h1, one_mul]
  · intro h1
    calc b * (u : G) * b⁻¹ * (u : G)⁻¹ = (b * u) * b⁻¹ * (u : G)⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem card_eq_card_centralizer_mul [Finite G] (U : Subgroup G)
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {b : G} (hb : b ∈ normalizer (U : Set G)) :
    Nat.card U =
      Nat.card ↥(U ⊓ centralizer ({b} : Set G)) * Nat.card (commHom U hUc hb).range := by
  have h1 : Nat.card (commHom U hUc hb).ker = Nat.card ↥(U ⊓ centralizer ({b} : Set G)) := by
    have e : (commHom U hUc hb).ker = (U ⊓ centralizer ({b} : Set G)).subgroupOf U := by
      ext u
      rw [mem_ker_commHom, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
      exact ⟨fun h => ⟨u.2, h.symm⟩, fun h => h.2.symm⟩
    rw [e]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h1, ← index_ker, card_mul_index]

end CommHom

section Modules

variable {G : Type} [Group G] [Finite G]

theorem card_evenWeight_of_card_eq_five {Ω : Type*} [Fintype Ω] (h5 : Fintype.card Ω = 5) :
    Nat.card (evenWeight Ω) = 16 := by
  classical
  let e : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq h5
  have h1 : Nat.card (evenWeight Ω) = Nat.card {x : Fin 5 → ZMod 2 // ∑ i, x i = 0} := by
    refine Nat.card_congr
      { toFun := fun x => ⟨fun i => (x : Ω → ZMod 2) (e.symm i), ?_⟩
        invFun := fun y => ⟨fun ω => (y : Fin 5 → ZMod 2) (e ω), ?_⟩
        left_inv := fun x => Subtype.ext (funext fun ω => by simp)
        right_inv := fun y => Subtype.ext (funext fun i => by simp) }
    · have hx : ∑ ω, (x : Ω → ZMod 2) ω = 0 := x.2
      rw [← hx]
      exact Equiv.sum_comp e.symm (x : Ω → ZMod 2)
    · show ∑ ω, (y : Fin 5 → ZMod 2) (e ω) = 0
      rw [Equiv.sum_comp e (y : Fin 5 → ZMod 2)]
      exact y.2
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

@[expose] def TerminalModulePositive (L M : Subgroup G) : Prop :=
  16 ≤ Nat.card (qtnqU L M) ∧ ∀ W : Subgroup G, W ≤ qtnqU L M →
    (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) → W = ⊥ ∨ W = qtnqU L M

@[expose] def TerminalModuleSmall (L M : Subgroup G) : Prop :=
  8 ≤ Nat.card (qtnqU L M) ∧ ∀ S : Subgroup G, S ≤ qtnqU L M →
    (∀ l ∈ L, ∀ s ∈ S, l * s * l⁻¹ ∈ S) → Nat.card S ≤ 4 → ∀ l ∈ L, ∀ s ∈ S, l * s * l⁻¹ = s

theorem conj_mem_qtnqU {T L M : Subgroup G} (h : QTNQ T L M) {l : G} (hl : l ∈ L) {u : G}
    (hu : u ∈ qtnqU L M) : l * u * l⁻¹ ∈ qtnqU L M :=
  (mem_normalizer_iff.mp (NQRigid.le_normalizer_qtnqU h (h.l_le hl)) u).mp hu

theorem forall_exists_of_transitive_equivariant {T L M : Subgroup G} (h : QTNQ T L M)
    {V : Type*} [Zero V] (ρ : L ⧸ CFSG.solvableRadical L → V → V)
    (htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ q, ρ q v = w)
    (π : qtnqU L M → V) (hπ1 : π 1 = 0)
    (hπ : ∀ (l : L) (x y : qtnqU L M), (y : G) = l * x * l⁻¹ →
      π y = ρ (l : L ⧸ CFSG.solvableRadical L) (π x))
    (S : Subgroup G) (hSL : ∀ l ∈ L, ∀ s ∈ S, l * s * l⁻¹ ∈ S)
    (s₀ : qtnqU L M) (hs₀ : (s₀ : G) ∈ S) (hπ0 : π s₀ ≠ 0) :
    ∀ v : V, ∃ s : qtnqU L M, (s : G) ∈ S ∧ π s = v := by
  intro v
  by_cases hv : v = 0
  · exact ⟨1, S.one_mem, by rw [hv, hπ1]⟩
  · obtain ⟨q, hq⟩ := htr _ v hπ0 hv
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨_, conj_mem_qtnqU h l.2 s₀.2⟩, hSL l l.2 s₀ hs₀, ?_⟩
    rw [hπ l s₀ ⟨_, conj_mem_qtnqU h l.2 s₀.2⟩ rfl, hq]

theorem card_le_card_of_forall_exists {S U : Subgroup G} (hSU : S ≤ U) {V : Type*}
    (π : U → V) (hπ : ∀ v : V, ∃ s : U, (s : G) ∈ S ∧ π s = v) :
    Nat.card V ≤ Nat.card S := by
  refine Nat.card_le_card_of_surjective (fun s : S => π ⟨s, hSU s.2⟩) fun v => ?_
  obtain ⟨s, hsS, hsv⟩ := hπ v
  exact ⟨⟨s, hsS⟩, hsv⟩

theorem naturalFour_cases {T L M : Subgroup G} (h : QTNQ T L M)
    (ha : NQSetup.QTNQNaturalFour L M) :
    TerminalModulePositive L M ∨ TerminalModuleSmall L M := by
  classical
  obtain ⟨k, _, _, hk4, V, _, _, hV2, β, φ, hφs, hφe, hφk⟩ := ha
  have : Module.Finite k V := Module.finite_of_finrank_eq_succ hV2
  have : Finite V := Module.finite_of_finite k
  have hV16 : Nat.card V = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := k), hV2, Nat.card_eq_fintype_card, hk4]
    norm_num
  have htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ q, β q v = w := by
    intro v w hv hw
    obtain ⟨g, hg⟩ := exists_specialLinearGroup_apply_eq hV2 hv hw
    exact ⟨β.symm g, by rw [MulEquiv.apply_symm_apply]; exact hg⟩
  have hsurj := forall_exists_of_transitive_equivariant h (V := V) (fun q v => β q v) htr
    (fun x => φ (Additive.ofMul x)) (by rw [ofMul_one, map_zero]) hφe
  have hU16 : 16 ≤ Nat.card (qtnqU L M) := by
    rw [← hV16]
    refine Nat.card_le_card_of_surjective (fun u : qtnqU L M => φ (Additive.ofMul u))
      fun v => ?_
    obtain ⟨x, hx⟩ := hφs v
    exact ⟨Additive.toMul x, hx⟩
  by_cases hinj : Function.Injective φ
  · left
    refine ⟨hU16, fun W hWU hWL => ?_⟩
    by_cases hW : W = ⊥
    · exact Or.inl hW
    · right
      obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW
      have hw1' : w ≠ 1 := fun e => hw1 (Subtype.ext e)
      have hφw : φ (Additive.ofMul ⟨w, hWU hw⟩) ≠ 0 := by
        intro h0
        apply hw1'
        have h1 : Additive.ofMul (⟨w, hWU hw⟩ : qtnqU L M) = Additive.ofMul 1 :=
          hinj (by rw [h0, ofMul_one, map_zero])
        exact congrArg Subtype.val (Additive.ofMul.injective h1)
      refine le_antisymm hWU fun x hx => ?_
      obtain ⟨s, hsW, hsx⟩ := hsurj W hWL ⟨w, hWU hw⟩ hw hφw (φ (Additive.ofMul ⟨x, hx⟩))
      have he : s = ⟨x, hx⟩ := Additive.ofMul.injective (hinj hsx)
      have hsx' : (s : G) = x := by rw [he]
      exact hsx' ▸ hsW
  · right
    refine ⟨by omega, fun S hSU hSL hS4 l hl s hs => ?_⟩
    by_contra hne
    have hφ0 : φ (Additive.ofMul ⟨s, hSU hs⟩) ≠ 0 := fun h0 => hne (hφk ⟨l, hl⟩ ⟨s, hSU hs⟩ h0)
    have h16 := card_le_card_of_forall_exists hSU _ (hsurj S hSL ⟨s, hSU hs⟩ hs hφ0)
    omega

theorem naturalThreeExtension_small {T L M : Subgroup G} (h : QTNQ T L M)
    (hc : NQSetup.QTNQNaturalThreeExtension L M) : TerminalModuleSmall L M := by
  classical
  obtain ⟨V, _, _, hV3, β, φ, hφs, hφe, hφk⟩ := hc
  have : Module.Finite (ZMod 2) V := Module.finite_of_finrank_eq_succ hV3
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hV8 : Nat.card V = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hV3, Nat.card_zmod]
    norm_num
  have htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ q, β q v = w := by
    intro v w hv hw
    obtain ⟨g, hg⟩ := SteinbergCB.exists_linearEquiv_apply_eq hv hw
    exact ⟨β.symm g, by rw [MulEquiv.apply_symm_apply]; exact hg⟩
  have hsurj := forall_exists_of_transitive_equivariant h (V := V) (fun q v => β q v) htr
    (fun x => φ (Additive.ofMul x)) (by rw [ofMul_one, map_zero]) hφe
  refine ⟨?_, fun S hSU hSL hS4 l hl s hs => ?_⟩
  · rw [← hV8]
    refine Nat.card_le_card_of_surjective (fun u : qtnqU L M => φ (Additive.ofMul u))
      fun v => ?_
    obtain ⟨x, hx⟩ := hφs v
    exact ⟨Additive.toMul x, hx⟩
  · by_contra hne
    have hφ0 : φ (Additive.ofMul ⟨s, hSU hs⟩) ≠ 0 := fun h0 => hne (hφk ⟨l, hl⟩ ⟨s, hSU hs⟩ h0)
    have h8 := card_le_card_of_forall_exists hSU _ (hsurj S hSL ⟨s, hSU hs⟩ hs hφ0)
    omega

theorem naturalThreeDouble_small {T L M : Subgroup G} (h : QTNQ T L M)
    (hc : NQSetup.QTNQNaturalThreeDouble L M) : TerminalModuleSmall L M := by
  classical
  obtain ⟨V, _, _, hV3, β, ψ, hψ⟩ := hc
  have : Module.Finite (ZMod 2) V := Module.finite_of_finrank_eq_succ hV3
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hV8 : Nat.card V = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hV3, Nat.card_zmod]
    norm_num
  have htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ q, β q v = w := by
    intro v w hv hw
    obtain ⟨g, hg⟩ := SteinbergCB.exists_linearEquiv_apply_eq hv hw
    exact ⟨β.symm g, by rw [MulEquiv.apply_symm_apply]; exact hg⟩
  have h1 := forall_exists_of_transitive_equivariant h (V := V) (fun q v => β q v) htr
    (fun x => (ψ (Additive.ofMul x)).1) (by rw [ofMul_one, map_zero]; rfl)
    (fun l x y hxy => by rw [hψ l x y hxy])
  have h2 := forall_exists_of_transitive_equivariant h (V := V) (fun q v => β q v) htr
    (fun x => (ψ (Additive.ofMul x)).2) (by rw [ofMul_one, map_zero]; rfl)
    (fun l x y hxy => by rw [hψ l x y hxy])
  refine ⟨?_, fun S hSU hSL hS4 l hl s hs => ?_⟩
  · have hVV : Nat.card (V × V) = 64 := by rw [Nat.card_prod, hV8]
    rw [Nat.card_congr (Additive.ofMul.trans ψ.toEquiv), hVV]
    norm_num
  · have hs1 : s = 1 := by
      have e1 : (ψ (Additive.ofMul ⟨s, hSU hs⟩)).1 = 0 := by
        by_contra hne
        have := card_le_card_of_forall_exists hSU _ (h1 S hSL ⟨s, hSU hs⟩ hs hne)
        omega
      have e2 : (ψ (Additive.ofMul ⟨s, hSU hs⟩)).2 = 0 := by
        by_contra hne
        have := card_le_card_of_forall_exists hSU _ (h2 S hSL ⟨s, hSU hs⟩ hs hne)
        omega
      have e : ψ (Additive.ofMul ⟨s, hSU hs⟩) = ψ 0 := by
        rw [map_zero]
        exact Prod.ext e1 e2
      have e' : (⟨s, hSU hs⟩ : qtnqU L M) = 1 := Additive.ofMul.injective (ψ.injective e)
      exact congrArg Subtype.val e'
    rw [hs1, mul_one, mul_inv_cancel]

theorem deletedFive_positive {T L M : Subgroup G} (h : QTNQ T L M)
    (hb : NQRigid.QTNQDeletedFive L M) : TerminalModulePositive L M := by
  classical
  obtain ⟨Ω, _, _, hΩ, β, θ, hθ⟩ := hb
  have hU16 : Nat.card (qtnqU L M) = 16 := by
    rw [← card_evenWeight_of_card_eq_five hΩ]
    exact Nat.card_congr (Additive.ofMul.trans θ.toEquiv)
  refine ⟨hU16.ge, fun W hWU hWL => ?_⟩
  let ψ : Additive (qtnqU L M) →+ (Ω → ZMod 2) :=
    { toFun := fun x => ((θ x : evenWeight Ω) : Ω → ZMod 2)
      map_zero' := by rw [map_zero, Submodule.coe_zero]
      map_add' := fun x y => by rw [map_add, Submodule.coe_add] }
  let A : AddSubgroup (Ω → ZMod 2) := (Subgroup.toAddSubgroup (W.subgroupOf (qtnqU L M))).map ψ
  let N : Submodule (ZMod 2) (Ω → ZMod 2) :=
    { carrier := A
      add_mem' := A.add_mem
      zero_mem' := A.zero_mem
      smul_mem' := fun c x hx => by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · rw [zero_smul]
          exact A.zero_mem
        · rw [one_smul]
          exact hx }
  have hmemN : ∀ x : Ω → ZMod 2, x ∈ N ↔ ∃ w : qtnqU L M, (w : G) ∈ W ∧
      ((θ (Additive.ofMul w) : evenWeight Ω) : Ω → ZMod 2) = x := by
    intro x
    show x ∈ (A : Set (Ω → ZMod 2)) ↔ _
    rw [SetLike.mem_coe, AddSubgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨Additive.toMul z, ?_, rfl⟩
      have hz' : Additive.toMul z ∈ W.subgroupOf (qtnqU L M) := hz
      exact mem_subgroupOf.mp hz'
    · rintro ⟨w, hw, rfl⟩
      exact ⟨Additive.ofMul w, mem_subgroupOf.mpr hw, rfl⟩
  have hNE : N ≤ evenWeight Ω := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := (hmemN x).mp hx
    exact (θ (Additive.ofMul w)).2
  have hperm : ∀ g : alternatingGroup Ω, MulAction.toPerm g = (g : Equiv.Perm Ω) :=
    fun g => Equiv.ext fun _ => rfl
  have hN : ∀ g : alternatingGroup Ω, ∀ x ∈ N, permAct (MulAction.toPerm g) x ∈ N := by
    intro g x hx
    obtain ⟨w, hwW, rfl⟩ := (hmemN x).mp hx
    obtain ⟨q, hq⟩ := β.surjective g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine (hmemN _).mpr ⟨⟨_, conj_mem_qtnqU h l.2 w.2⟩, hWL l l.2 w hwW, ?_⟩
    rw [hθ l w ⟨_, conj_mem_qtnqU h l.2 w.2⟩ rfl, hq, hperm]
  have h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : alternatingGroup Ω, g • a = c ∧ g • b = d := by
    intro a b c d hab hcd
    obtain ⟨σ, h1, h2⟩ := NQSetup.exists_alternatingGroup_apply_eq_apply_eq hΩ hab hcd
    exact ⟨σ, h1, h2⟩
  rcases CFSG.QuasithinUnique.Setup.SL2Modules.evenWeight_irreducible_five hΩ h2 N hNE hN with
    hN0 | hNE'
  · left
    refine eq_bot_iff.mpr fun w hw => ?_
    have hmem : ((θ (Additive.ofMul (⟨w, hWU hw⟩ : qtnqU L M)) : evenWeight Ω) :
        Ω → ZMod 2) ∈ N := (hmemN _).mpr ⟨⟨w, hWU hw⟩, hw, rfl⟩
    rw [hN0, Submodule.mem_bot] at hmem
    have h0 : θ (Additive.ofMul (⟨w, hWU hw⟩ : qtnqU L M)) = θ 0 := by
      rw [map_zero]
      exact Subtype.ext hmem
    have e' : (⟨w, hWU hw⟩ : qtnqU L M) = 1 := Additive.ofMul.injective (θ.injective h0)
    rw [mem_bot]
    exact congrArg Subtype.val e'
  · right
    refine le_antisymm hWU fun x hx => ?_
    have hmem : ((θ (Additive.ofMul (⟨x, hx⟩ : qtnqU L M)) : evenWeight Ω) :
        Ω → ZMod 2) ∈ N := by
      rw [hNE']
      exact (θ (Additive.ofMul ⟨x, hx⟩)).2
    obtain ⟨w, hwW, hwx⟩ := (hmemN _).mp hmem
    have e : θ (Additive.ofMul w) = θ (Additive.ofMul ⟨x, hx⟩) := Subtype.ext hwx
    have e' : w = ⟨x, hx⟩ := Additive.ofMul.injective (θ.injective e)
    have hwx' : (w : G) = x := by rw [e']
    exact hwx' ▸ hwW

theorem explicitModule_cases {T L M : Subgroup G} (h : QTNQ T L M)
    (hmod : NQRigid.QTNQExplicitModule L M) :
    TerminalModulePositive L M ∨ TerminalModuleSmall L M := by
  rcases hmod with ha | hb | hc | hc
  · exact naturalFour_cases h ha
  · exact Or.inl (deletedFive_positive h hb)
  · exact Or.inr (naturalThreeDouble_small h hc)
  · exact Or.inr (naturalThreeExtension_small h hc)

end Modules

section Terminal

variable {G : Type} [Group G] [Finite G]

theorem radical_commute_qtnqU {T L M : Subgroup G} (h : QTNQ T L M) :
    ∀ r ∈ (CFSG.solvableRadical ↥L).map L.subtype, ∀ u ∈ qtnqU L M, r * u = u * r := by
  intro r hr u hu
  rw [← h.centralizer_eq_radical] at hr
  exact (mem_centralizer_iff.mp hr.2 u (NQSetup.qtnqU_le_qtnqVc h hu)).symm

theorem conj_commute_of_trivial_on_quotient {T L M : Subgroup G} (h : QTNQ T L M) {b : G}
    (hbM : b ∈ M) (hbL : ∀ l ∈ L, ⁅l, b⁆ ∈ (CFSG.solvableRadical ↥L).map L.subtype)
    {l : G} (hl : l ∈ L) {u : G} (hu : u ∈ qtnqU L M) :
    b * (l * u * l⁻¹) * b⁻¹ = l * (b * u * b⁻¹) * l⁻¹ := by
  have hs := hbL l⁻¹ (L.inv_mem hl)
  set s := ⁅l⁻¹, b⁆ with hsdef
  have hbu : b * u * b⁻¹ ∈ qtnqU L M :=
    (mem_normalizer_iff.mp (NQRigid.le_normalizer_qtnqU h hbM) u).mp hu
  have hsc : s * (b * u * b⁻¹) = (b * u * b⁻¹) * s := radical_commute_qtnqU h s hs _ hbu
  have hbl : b * l = l * s * b := by
    rw [hsdef, commutatorElement_def]
    group
  calc b * (l * u * l⁻¹) * b⁻¹ = (b * l) * u * (b * l)⁻¹ := by group
    _ = (l * s * b) * u * (l * s * b)⁻¹ := by rw [hbl]
    _ = l * (s * (b * u * b⁻¹)) * s⁻¹ * l⁻¹ := by group
    _ = l * ((b * u * b⁻¹) * s) * s⁻¹ * l⁻¹ := by rw [hsc]
    _ = l * (b * u * b⁻¹) * l⁻¹ := by group

theorem terminal_small_module_false {T L M : Subgroup G} (h : QTNQ T L M)
    (hTI : ∀ x : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) x = ⊥ ∨
      CFSG.conjugate (qtnqU L M) x = qtnqU L M)
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M)
    {H Y : Subgroup G} (hTH : T ≤ H) (hYH : Y ≤ H) (hYn : (Y.subgroupOf H).Normal)
    (hYp : Group.IsPerfect Y) (hHY : IsPGroup 2 (H ⧸ Y.subgroupOf H))
    (hsimple : IsSimpleGroup (Y ⧸ CFSG.pCore 2 Y))
    (hnab : ∃ a b : Y ⧸ CFSG.pCore 2 Y, a * b ≠ b * a)
    (hYM : ¬ Y ≤ M) (hm2 : CFSG.pRank 2 (H ⧸ CFSG.pCore 2 H) ≤ 2)
    (hFour : ∀ B : Subgroup G, B ≤ M → CFSG.IsElementaryAbelian 2 B → Nat.card B = 4 →
      ∃ b ∈ B, b ≠ 1 ∧ ∀ l ∈ L, ⁅l, b⁆ ∈ (CFSG.solvableRadical ↥L).map L.subtype)
    (h8 : 8 ≤ Nat.card (qtnqU L M))
    (hsmall : ∀ S : Subgroup G, S ≤ qtnqU L M → (∀ l ∈ L, ∀ s ∈ S, l * s * l⁻¹ ∈ S) →
      Nat.card S ≤ 4 → ∀ l ∈ L, ∀ s ∈ S, l * s * l⁻¹ = s) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := qtnqU L M with hUdef
  obtain ⟨-, -, -, -, ⟨hU1, hUM, hUn, hUel⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hUp : IsPGroup 2 U := CFSG.IsElementaryAbelian.isPGroup 2 U
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := (isElementaryAbelian_iff.mp hUel).1
  have hMN : M ≤ normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mp hUn
  have hNU : normalizer (U : Set G) = M := h.max_two_local.2 _ ⟨U, hU1, hUp, rfl⟩ hMN
  have hTle : ∀ P : Subgroup G, IsPGroup 2 P → T ≤ normalizer (P : Set G) → P ≤ T := by
    intro P hP hTP
    have hsup := hP.to_sup_of_normal_left' h.sylow.1 hTP
    have heq := (h.sylow.1.toSylow h.sylow.2).is_maximal' hsup le_sup_right
    exact le_sup_left.trans heq.le
  set Q := (CFSG.pCore 2 H).map H.subtype with hQdef
  have hQp : IsPGroup 2 Q := (CFSG.pCore_isPGroup (p := 2) (G := H)).map H.subtype
  have hHQ : H ≤ normalizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · rintro ⟨q', hq', rfl⟩
      exact ⟨⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := H)).conj_mem _ hq' _, rfl⟩
    · rintro ⟨q', hq', hqq⟩
      refine ⟨⟨x, hx⟩⁻¹ * q' * ⟨x, hx⟩⁻¹⁻¹,
        (CFSG.pCore_normal (p := 2) (G := H)).conj_mem _ hq' _, ?_⟩
      change x⁻¹ * (q' : G) * x⁻¹⁻¹ = q
      rw [show (q' : G) = x * q * x⁻¹ from hqq]
      group
  have hQT : Q ≤ T := hTle Q hQp (hTH.trans hHQ)
  have hQM : Q ≤ M := hQT.trans h.t_le
  have hUT : U ≤ T := hTle U hUp (h.t_le.trans hMN)
  have hcard : ∀ x : G, Nat.card (CFSG.conjugate U x) = Nat.card U := fun x =>
    Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
  have hbig : ∀ x : G, CFSG.conjugate U x ≤ H →
      Nat.card U ≤ 4 * Nat.card ↥(CFSG.conjugate U x ⊓ Q) := by
    intro x hx
    have h1 := NQTerm.card_le_four_mul_card_inf_pCore hm2 hx (CFSG.IsElementaryAbelian.map _)
    rwa [hcard] at h1
  have hconjH : ∀ x ∈ H, CFSG.conjugate U x ≤ H := fun x hx =>
    CFSG.GroupTheory.conjugate_le_of_mem (hUT.trans hTH) hx
  obtain ⟨g, hgT, hgQ⟩ : ∃ g : G, CFSG.conjugate U g ≤ T ∧ ¬ CFSG.conjugate U g ≤ Q := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply hYM
    refine (hYH.trans ?_).trans hW
    set W := (sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate U g = X) ∧ X ≤ T} :
      Subgroup G)
    have hmapW : ∀ y ∈ H, W.map (MulAut.conj y).toMonoidHom ≤ W := by
      intro y hy
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun X hX => ?_
      obtain ⟨⟨x, rfl⟩, hXT⟩ := hX
      rw [← Subgroup.map_le_iff_le_comap]
      refine le_sSup ⟨⟨x * y⁻¹, ?_⟩, ?_⟩
      · show U.map (MulAut.conj (x * y⁻¹)⁻¹).toMonoidHom =
          (U.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom
        rw [Subgroup.map_map, mul_inv_rev, inv_inv, map_mul]
        rfl
      · calc (CFSG.conjugate U x).map (MulAut.conj y).toMonoidHom
            ≤ Q.map (MulAut.conj y).toMonoidHom := Subgroup.map_mono (hall x hXT)
          _ = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHQ hy)
          _ ≤ T := hQT
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hmapW y hy) fun w hw => ?_
    refine ⟨y⁻¹ * w * y, ?_, ?_⟩
    · have h1 : (MulAut.conj y⁻¹).toMonoidHom w ∈ W :=
        hmapW y⁻¹ (inv_mem hy) ⟨w, hw, rfl⟩
      simpa [MulAut.conj_apply] using h1
    · show y * (y⁻¹ * w * y) * y⁻¹ = w
      group
  have hUQ : ¬ U ≤ Q := by
    intro hUQ
    have hA₀H : CFSG.conjugate U g ≤ H := hgT.trans hTH
    have hA₀p : IsPGroup 2 (CFSG.conjugate U g) := hUp.map _
    obtain ⟨y, hyY, hyM⟩ := (SteinbergCC.perfect_two_extension_conjugate_escape hYH hYn hYp hHY
      hsimple hnab hA₀H hA₀p hgQ).2 hYM
    rw [CFSG.GroupTheory.conjugate_conjugate] at hyM
    have hA₁H : CFSG.conjugate U (g * y) ≤ H := by
      rw [← CFSG.GroupTheory.conjugate_conjugate]
      exact CFSG.GroupTheory.conjugate_le_of_mem hA₀H (hYH hyY)
    have hA₁p : IsPGroup 2 (CFSG.conjugate U (g * y)) := hUp.map _
    have hne : CFSG.conjugate U (g * y) ≠ U := fun he => hyM (by rw [he]; exact hUM)
    have hpg : IsPGroup 2 (U ⊔ CFSG.conjugate U (g * y) : Subgroup G) :=
      (hQp.to_sup_of_normal_left' hA₁p (hA₁H.trans hHQ)).to_le (sup_le_sup_right hUQ _)
    have hnorm : CFSG.conjugate U (g * y) ⊓ normalizer (U : Set G) ≠ ⊥ := by
      intro hbot
      have h4 := hbig _ hA₁H
      have hle : CFSG.conjugate U (g * y) ⊓ Q ≤ CFSG.conjugate U (g * y) ⊓
          normalizer (U : Set G) := inf_le_inf_left _ (hNU ▸ hQM)
      rw [hbot, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at h4
      omega
    have hcomm := (CFSG.Quasithin.SteinbergBM.nq_elementary_TI_pair_commutation hUel hTI hne).2
      hpg hnorm
    apply hyM
    rw [← hNU]
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨y, hyY, hyM⟩ := (SteinbergCC.perfect_two_extension_conjugate_escape hYH hYn hYp hHY
    hsimple hnab (hUT.trans hTH) hUp hUQ).2 hYM
  set A := CFSG.conjugate U y with hAdef
  have hAQ : Nat.card U ≤ 4 * Nat.card ↥(A ⊓ Q) := hbig y (hconjH y (hYH hyY))
  have hAU : A ≠ U := fun he => hyM (by rw [he]; exact hUM)
  have hUA : U ⊓ A = ⊥ := (hTI y).resolve_right hAU
  have hAel : CFSG.IsElementaryAbelian 2 A := CFSG.IsElementaryAbelian.map _
  have hATI := CFSG.Quasithin.SteinbergBM.conjugate_TI hTI y
  obtain ⟨n, hn⟩ := hUp.exists_card_eq
  have hAn : Nat.card A = 2 ^ n := (hcard y).trans hn
  set B := A ⊓ normalizer (U : Set G) with hBdef
  set U₀ := U ⊓ normalizer (A : Set G) with hU₀def
  have hBM : B ≤ M := hNU ▸ inf_le_right
  have hUB : Nat.card U ≤ 4 * Nat.card B :=
    hAQ.trans (Nat.mul_le_mul_left 4 (Subgroup.card_le_of_le (inf_le_inf_left A (hNU ▸ hQM))))
  have hB1 : B ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hUB
    omega
  have hrev := CFSG.Quasithin.SteinbergBM.equal_rank_elementary_TI_pair_mutual_normalizer_calculus
    hAel hUel hAn hn (by rw [inf_comm]; exact hUA) hATI hTI hB1
  have hU01 : U₀ ≠ ⊥ := hrev.1
  have hcal := CFSG.Quasithin.SteinbergBM.equal_rank_elementary_TI_pair_mutual_normalizer_calculus
    hUel hAel hn hAn hUA hTI hATI hU01
  obtain ⟨-, -, -, ⟨hYset, -, -⟩, -, -, hYnorm, hUeq, hlt⟩ := hcal
  have hU0lt : U₀ < U := by
    refine lt_of_le_of_ne inf_le_left fun he => hyM ?_
    have hBA : B = A := (hUeq he).1
    rw [← hNU, ← hBA]
    exact inf_le_right
  obtain ⟨-, hU0B, -, hCb, -⟩ := hlt hU0lt
  have hkey : ∀ b ∈ B, (∀ l ∈ L, ⁅l, b⁆ ∈ (CFSG.solvableRadical ↥L).map L.subtype) → b = 1 := by
    intro b hb hbL
    by_contra hb1
    have hbN : b ∈ normalizer (U : Set G) := hb.2
    have hbM : b ∈ M := hBM hb
    set f := commHom U hUc hbN with hf
    set S : Subgroup G := f.range.map U.subtype with hS
    have hSU : S ≤ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hdec : Nat.card U = Nat.card B * Nat.card f.range := by
      have h1 := card_eq_card_centralizer_mul U hUc hbN
      rw [hCb b hb hb1, hU0B] at h1
      exact h1
    have hS4 : Nat.card S ≤ 4 := by
      rw [hS, Subgroup.card_map_of_injective U.subtype_injective]
      have hBpos : 0 < Nat.card B := Nat.card_pos
      by_contra hgt
      have h5 : Nat.card B * 5 ≤ Nat.card B * Nat.card f.range :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hfL : ∀ l ∈ L, ∀ u : U, ∃ u' : U, (u' : G) = l * u * l⁻¹ ∧
        ((f u' : U) : G) = l * (f u : G) * l⁻¹ := by
      intro l hl u
      have hlu : l * (u : G) * l⁻¹ ∈ U := (mem_normalizer_iff.mp (hMN (h.l_le hl)) u).mp u.2
      refine ⟨⟨_, hlu⟩, rfl, ?_⟩
      rw [hf, commHom_apply, commHom_apply]
      have hc := conj_commute_of_trivial_on_quotient h hbM hbL hl u.2
      calc b * (l * u * l⁻¹) * b⁻¹ * (l * (u : G) * l⁻¹)⁻¹
          = (l * (b * u * b⁻¹) * l⁻¹) * (l * (u : G) * l⁻¹)⁻¹ := by rw [hc]
        _ = l * (b * u * b⁻¹ * (u : G)⁻¹) * l⁻¹ := by group
    have hSL : ∀ l ∈ L, ∀ s ∈ S, l * s * l⁻¹ ∈ S := by
      rintro l hl _ ⟨x, ⟨u, rfl⟩, rfl⟩
      obtain ⟨u', -, hu'⟩ := hfL l hl u
      exact ⟨f u', ⟨u', rfl⟩, hu'⟩
    have hfix := hsmall S hSU hSL hS4
    have hker : ⁅U, L⁆ ≤ f.ker.map U.subtype := by
      rw [Subgroup.commutator_le]
      intro u hu l hl
      have hlu : l * u⁻¹ * l⁻¹ ∈ U :=
        (mem_normalizer_iff.mp (hMN (h.l_le hl)) u⁻¹).mp (U.inv_mem hu)
      refine ⟨⟨u, hu⟩ * ⟨_, hlu⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul]
        obtain ⟨u', hu'1, hu'2⟩ := hfL l hl ⟨u⁻¹, U.inv_mem hu⟩
        have he : (⟨_, hlu⟩ : U) = u' := Subtype.ext hu'1.symm
        rw [he]
        apply Subtype.ext
        have hmem : ((f ⟨u⁻¹, U.inv_mem hu⟩ : U) : G) ∈ S := ⟨_, ⟨_, rfl⟩, rfl⟩
        rw [Subgroup.coe_mul, hu'2, hfix l hl _ hmem, ← Subgroup.coe_mul, ← map_mul]
        have : (⟨u, hu⟩ * ⟨u⁻¹, U.inv_mem hu⟩ : U) = 1 := Subtype.ext (mul_inv_cancel u)
        rw [this, map_one]
      · show u * (l * u⁻¹ * l⁻¹) = ⁅u, l⁆
        rw [commutatorElement_def]
        group
    have hall : ∀ u : U, f u = 1 := by
      intro u
      have hu : (u : G) ∈ f.ker.map U.subtype := by
        have hcomm : ⁅U, L⁆ = U := NQRigid.commutator_qtnqU_eq h
        refine hker ?_
        rw [hcomm]
        exact u.2
      obtain ⟨u', hu', huu⟩ := hu
      have he : u' = u := Subtype.ext huu
      rw [← he]
      exact hu'
    have hcen : U ⊓ centralizer ({b} : Set G) = U := by
      refine le_antisymm inf_le_left fun u hu => mem_inf.mpr ⟨hu, ?_⟩
      exact mem_centralizer_singleton_iff.mpr
        ((mem_ker_commHom U hUc hbN ⟨u, hu⟩).mp (hall ⟨u, hu⟩)).symm
    rw [hCb b hb hb1] at hcen
    exact (ne_of_lt hU0lt) hcen
  have hB2 : Nat.card B ≤ 2 := by
    by_contra hgt
    have hBp : IsPGroup 2 B := hAel.isPGroup.to_le inf_le_left
    obtain ⟨k, hk⟩ := hBp.exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : 2 ^ k ≤ 2 := by
        calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      omega
    obtain ⟨E, hE, -, hEB⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := G) Nat.prime_two
      (n := 2) (H := ⊥) (L := B) (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hk]; exact Nat.pow_dvd_pow 2 hk2) bot_le
    obtain ⟨b, hbE, hb1, hbL⟩ := hFour E (hEB.trans hBM)
      (CFSG.Quasithin.BlueprintB2.isElementaryAbelian_of_le (hEB.trans inf_le_left) hAel)
      (by rw [hE]; norm_num)
    exact hb1 (hkey b (hEB hbE) hbL)
  obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
  have hb1' : b ≠ 1 := fun e => hb1 (Subtype.ext e)
  have hbN : b ∈ normalizer (U : Set G) := hbB.2
  have hconjY : ∀ x ∈ U ⊔ A, ∀ z ∈ U₀ ⊔ B, x * z * x⁻¹ ∈ U₀ ⊔ B := by
    intro x hx z hz
    have hle : U₀ ⊔ B ≤ U ⊔ A := sup_le_sup (inf_le_left : U₀ ≤ U) (inf_le_left : B ≤ A)
    have hzUA : z ∈ U ⊔ A := hle hz
    have h1 := hYnorm.conj_mem ⟨z, hzUA⟩ (by rw [mem_subgroupOf]; exact hz) ⟨x, hx⟩
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hrange : ∀ u : U, ((commHom U hUc hbN u : U) : G) ∈ U₀ := by
    intro u
    rw [commHom_apply]
    have hbY : b ∈ U₀ ⊔ B := le_sup_right (a := U₀) hbB
    have h1 : (u : G) * b⁻¹ * (u : G)⁻¹ ∈ U₀ ⊔ B :=
      hconjY u (le_sup_left (a := U) u.2) b⁻¹ ((U₀ ⊔ B).inv_mem hbY)
    have h2 : b * u * b⁻¹ * (u : G)⁻¹ ∈ U₀ ⊔ B := by
      have := (U₀ ⊔ B).mul_mem hbY h1
      rwa [show b * ((u : G) * b⁻¹ * (u : G)⁻¹) = b * u * b⁻¹ * (u : G)⁻¹ by group] at this
    have h2' : b * u * b⁻¹ * (u : G)⁻¹ ∈ ((U₀ : Set G) * (B : Set G)) := by
      rw [← hYset]
      exact h2
    obtain ⟨x, hx, z, hz, hxz⟩ := Set.mem_mul.mp h2'
    have hfU : b * u * b⁻¹ * (u : G)⁻¹ ∈ U := (commHom U hUc hbN u).2
    have hzU : z ∈ U := by
      have := U.mul_mem (U.inv_mem (inf_le_left (a := U) hx)) hfU
      rwa [← hxz, show x⁻¹ * (x * z) = z by group] at this
    have hz1 : z = 1 := by
      have : z ∈ U ⊓ A := ⟨hzU, inf_le_left (a := A) hz⟩
      rw [hUA, mem_bot] at this
      exact this
    rw [← hxz, hz1, mul_one]
    exact hx
  have hdec : Nat.card U = Nat.card B * Nat.card (commHom U hUc hbN).range := by
    have h1 := card_eq_card_centralizer_mul U hUc hbN
    rw [hCb b hbB hb1', hU0B] at h1
    exact h1
  have hrle : Nat.card (commHom U hUc hbN).range ≤ Nat.card B := by
    rw [← hU0B, ← Subgroup.card_map_of_injective U.subtype_injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, ⟨u, rfl⟩, rfl⟩
    exact hrange u
  have hsq : Nat.card U ≤ Nat.card B * Nat.card B := by
    rw [hdec]
    exact Nat.mul_le_mul_left _ hrle
  have : Nat.card B * Nat.card B ≤ 2 * 2 := Nat.mul_le_mul hB2 hB2
  omega

end Terminal

@[expose] def OblTerminalWholeModuleResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    (∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M) →
    normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧ X ≤ T} :
      Subgroup G) : Set G) ≤ M →
    ∀ (H Y : Subgroup G) (_ : (Y.subgroupOf H).Normal), T ≤ H → Y ≤ H → Group.IsPerfect Y →
      IsPGroup 2 (H ⧸ Y.subgroupOf H) → IsSimpleGroup (Y ⧸ CFSG.pCore 2 Y) →
      (∃ a b : Y ⧸ CFSG.pCore 2 Y, a * b ≠ b * a) → ¬ Y ≤ M →
      CFSG.pRank 2 (H ⧸ CFSG.pCore 2 H) ≤ 2 →
      16 ≤ Nat.card (qtnqU L M) ∧
        ∀ V : Subgroup G, V ≤ qtnqU L M → (∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V) →
          V = ⊥ ∨ V = qtnqU L M

theorem nonquasisimpleTITerminalContradiction_of_residual
    (hS : OriginalKEscapingSourceY) (hE : OriginalNoNormalSourceYEscapes)
    (hEsc : NonquasisimpleTIEscapingResidual) (hMod : OblTerminalWholeModuleResidual)
    (hFour : ConfigurationFourGroupObstruction) : NonquasisimpleTITerminalContradiction := by
  intro G _ _ T L M h hTI
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
  have hW := ((original_radical_supplements_share_simple_residual_and_internal_module h
    hR).2.2.2.2.2.2.2.2.2.2 hTI _ rfl).2 (original_K_singleton_of_inputs hS hE h)
  obtain ⟨H, Y, hYn, hTH, hYH, hYp, hHY, hsimple, hnab, hYM, hm2⟩ := hEsc G T L M h hTI hW
  obtain ⟨h16, hirr⟩ := hMod G T L M h hTI hW H Y hYn hTH hYH hYp hHY hsimple hnab hYM hm2
  obtain ⟨_, _, B, hBle, -, hBe, hB4, hBf⟩ := NQTerm.nq_terminal_irreducible_four_witness h h16
    hirr hTI hW hTH hYH hYn hYp hHY hsimple hnab hYM hm2
  obtain ⟨b, hb, hb1, hbL⟩ := hFour G T L M h B (hBle.trans inf_le_right) hBe hB4
  exact hb1 (hBf b hb hbL)

theorem oblTerminalWholeModuleResidual_of_explicitModule
    (hmod : ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
      NQRigid.QTNQExplicitModule L M)
    (hFour : ConfigurationFourGroupObstruction) : OblTerminalWholeModuleResidual := by
  intro G _ _ T L M h hTI hW H Y hYn hTH hYH hYp hHY hsimple hnab hYM hm2
  rcases explicitModule_cases h (hmod G T L M h) with hpos | ⟨h8, hsmall⟩
  · exact hpos
  · exact (terminal_small_module_false h hTI hW hTH hYH hYn hYp hHY hsimple hnab hYM hm2
      (hFour G T L M h) h8 hsmall).elim

theorem nonquasisimpleTITerminalContradiction_of_explicitModule
    (hS : OriginalKEscapingSourceY) (hE : OriginalNoNormalSourceYEscapes)
    (hEsc : NonquasisimpleTIEscapingResidual)
    (hmod : ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
      NQRigid.QTNQExplicitModule L M)
    (hFour : ConfigurationFourGroupObstruction) : NonquasisimpleTITerminalContradiction :=
  nonquasisimpleTITerminalContradiction_of_residual hS hE hEsc
    (oblTerminalWholeModuleResidual_of_explicitModule hmod hFour) hFour

end CFSG.Quasithin.H13.NQBlock
