module

public import CFSG.RankThree.PartTwo.J2Residue.KJSplitHolds
public import CFSG.RankThree.PartTwo.J2Residue.C4725Intertwiner
public import CFSG.RankThree.PartTwo.J2Residue.H2SylowTransfer
public import CFSG.RankThree.PartTwo.J2Residue.ConjAction
public import CFSG.RankThree.PartTwo.J2Residue.KFacts
public import CFSG.RankThree.PartTwo.J2Residue.KFactsCommon

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.RankThree.PartTwo.J2Residue.C4725 CFSG.RankThree.PartTwo.J2Residue.H2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [local irreducible] eJP x0J

@[expose] noncomputable def eJPHom :
    ↥P →* J2 :=
  eJP.toMonoidHom

@[expose] noncomputable def eJPinvHom :
    J2 →* ↥P :=
  eJP.symm.toMonoidHom

theorem eJPHom_apply (g : ↥P) :
    eJPHom g = eJP g := rfl

theorem eJPinvHom_apply (x : J2) :
    eJPinvHom x = eJP.symm x := rfl

theorem exists_complement_of_coords
    {L : Type*} [Group L]
    {M : Subgroup L} [M.Normal] (π : L →* ↥P) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 1 ↔ x ∈ M) (ρ : ↥P →* Module.End (ZMod 2) V12) (hρ : IsMRep ρ)
    (e : ↥M ≃ V12) (he : ∀ a b : ↥M, e (a * b) = e a + e b)
    (hact : ∀ (ℓ : L) (m : ↥M),
      e ⟨ℓ * m * ℓ⁻¹, (inferInstance : M.Normal).conj_mem m m.2 ℓ⟩ = ρ (π ℓ) (e m)) :
    ∃ H : Subgroup L, Subgroup.IsComplement' H M := by
  classical
  have he1 : e 1 = 0 := by
    have := he 1 1
    rw [mul_one] at this
    exact left_eq_add.1 this
  let u : ↥P → L := fun g => if g = 1 then 1 else (hπ g).choose
  have hu : ∀ g, π (u g) = g := fun g => by
    by_cases hg : g = 1
    · simp [u, hg]
    · simp only [u, if_neg hg]
      exact (hπ g).choose_spec
  have hu1 : u 1 = 1 := by simp [u]
  have hmem : ∀ g h, u g * u h * (u (g * h))⁻¹ ∈ M := fun g h => (hker _).1 (by
    rw [map_mul, map_mul, map_inv, hu, hu, hu, mul_inv_cancel])
  let m : ↥P → ↥P → ↥M := fun g h => ⟨u g * u h * (u (g * h))⁻¹, hmem g h⟩
  let c : ↥P → ↥P → V12 := fun g h => e (m g h)
  have hc : IsNormCoc ρ c := by
    refine ⟨fun h => ?_, fun g => ?_, fun g h k => ?_⟩
    · have : m 1 h = 1 := Subtype.ext (by simp [m, hu1])
      simp only [c, this, he1]
    · have : m g 1 = 1 := Subtype.ext (by simp [m, hu1])
      simp only [c, this, he1]
    · have hconj := hact (u g) (m h k)
      rw [hu] at hconj
      have hid : (⟨u g * (m h k : L) * (u g)⁻¹, (inferInstance : M.Normal).conj_mem _ (m h k).2
          (u g)⟩ : ↥M) * m g (h * k) = m g h * m (g * h) k :=
        Subtype.ext (by simp only [m, Subgroup.coe_mul, mul_assoc]; group)
      have := congrArg e hid
      rw [he, he, hconj] at this
      simp only [c]
      rw [show ρ g (e (m h k)) - e (m (g * h) k) + e (m g (h * k)) - e (m g h) =
        (ρ g (e (m h k)) + e (m g (h * k))) - (e (m g h) + e (m (g * h) k)) by abel, this, sub_self]
  obtain ⟨β, hβ⟩ := exists_cob_of_isNormCoc hρ hc
  let n : ↥P → ↥M := fun g => e.symm (-β g)
  let u' : ↥P → L := fun g => (n g : L) * u g
  have hu'mul : ∀ g h, u' (g * h) = u' g * u' h := by
    intro g h
    have key : n (g * h) = n g * ⟨u g * (n h : L) * (u g)⁻¹,
        (inferInstance : M.Normal).conj_mem _ (n h).2 (u g)⟩ * m g h := by
      apply e.injective
      rw [he, he, hact, hu]
      simp only [n, c, Equiv.apply_symm_apply, map_neg]
      have := congrFun (congrFun hβ g) h
      simp only [c] at this
      rw [this, H2.cob]
      abel
    simp only [u']
    rw [key]
    simp only [m, Subgroup.coe_mul]
    group
  let φ : ↥P →* L := MonoidHom.mk' u' hu'mul
  have hφ : ∀ g, π (φ g) = g := fun g => by
    simp only [φ, MonoidHom.mk'_apply, u', map_mul, hu, (hker _).2 (n g).2, one_mul]
  refine ⟨φ.range, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_⟩
  · rw [Subgroup.disjoint_def]
    rintro x ⟨g, rfl⟩ hx
    have hg : g = 1 := by rw [← hφ g]; exact (hker _).2 hx
    rw [hg, map_one]
  · refine Set.eq_univ_of_forall fun ℓ => ?_
    refine ⟨φ (π ℓ), ⟨π ℓ, rfl⟩, (φ (π ℓ))⁻¹ * ℓ, (hker _).1 ?_, by group⟩
    rw [map_mul, map_inv, hφ, inv_mul_cancel]

@[expose] noncomputable def conjRep {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : G →* Module.End (ZMod 2) W) (θ : V12 ≃ₗ[ZMod 2] W) : G →* Module.End (ZMod 2) V12 where
  toFun g := (θ.symm : W →ₗ[ZMod 2] V12) ∘ₗ ρ g ∘ₗ (θ : V12 →ₗ[ZMod 2] W)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

theorem conjRep_apply {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : G →* Module.End (ZMod 2) W) (θ : V12 ≃ₗ[ZMod 2] W) (g : G) (v : V12) :
    conjRep ρ θ g v = θ.symm (ρ g (θ v)) :=
  rfl

theorem exists_linearEquiv_of_fixed_J2
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Nontrivial W] (ρ : J2 →* Module.End (ZMod 2) W)
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ x : J2, ∀ u ∈ U, ρ x u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : ∀ u : W, ρ x0J u = u → u = 0) :
    ∃ θ : V12 ≃ₗ[ZMod 2] W, ∀ j < 2, ∀ y,
      θ ((Mj j).mulVec y) = ρ.comp eJPHom (letterP j) (θ y) := by
  have hfix' : ∀ u : W, ρ.comp eJPHom x0P u = u → u = 0 := by
    intro u hu
    rw [MonoidHom.comp_apply, eJPHom_apply, show eJP x0P = x0J by unfold x0J; rfl]
      at hu
    exact hfix u hu
  refine exists_linearEquiv_of_fixed (ρ.comp eJPHom) (fun U hU => ?_) hfix'
  refine hirr U fun x u hu => ?_
  have := hU (eJP.symm x) u hu
  rwa [MonoidHom.comp_apply, eJPHom_apply, MulEquiv.apply_symm_apply] at this

theorem exists_coords_of_action
    {A : Type*} [CommGroup A] [Finite A] [Nontrivial A]
    [Module (ZMod 2) (Additive A)] (σ : J2 →* MulAut A)
    (hirr : ∀ K : Subgroup A, (∀ x : J2, ∀ a ∈ K, σ x a ∈ K) → K = ⊥ ∨ K = ⊤)
    (hfix : ∀ a : A, σ x0J a = a → a = 1) :
    ∃ (ρ : ↥P →* Module.End (ZMod 2) V12) (e : A ≃ V12), IsMRep ρ ∧
      (∀ a b : A, e (a * b) = e a + e b) ∧ ∀ (g : ↥P) (a : A), e (σ (eJP g) a) = ρ g (e a) := by
  haveI : Finite (Additive A) := Finite.of_equiv A Additive.ofMul
  haveI : Nontrivial (Additive A) := Additive.ofMul.symm.nontrivial
  have hirrJ := submodule_eq_bot_or_top σ hirr
  obtain ⟨θ, hθ⟩ := exists_linearEquiv_of_fixed_J2 ((mulAutToEnd A).comp σ) hirrJ fun u hu => by
    rw [← ofMul_toMul u, MonoidHom.comp_apply, mulAutToEnd_apply] at hu
    rw [← ofMul_toMul u, hfix _ (Additive.ofMul.injective hu), ofMul_one]
  refine ⟨conjRep (((mulAutToEnd A).comp σ).comp eJPHom) θ,
    Additive.ofMul.trans θ.symm.toEquiv, fun j v => ?_, fun a b => ?_, fun g a => ?_⟩
  · rcases Nat.lt_or_ge j 2 with hj | hj
    · rw [conjRep_apply, ← hθ j hj, LinearEquiv.symm_apply_apply]
    · have h1 : letterP j = letterP 1 :=
        Subtype.ext (by simp [letterP, letter, show j ≠ 0 by omega])
      have h2 : Mj j = Mj 1 := by simp [Mj, colsJ, show j ≠ 0 by omega]
      rw [h1, h2, conjRep_apply, ← hθ 1 (by norm_num), LinearEquiv.symm_apply_apply]
  · simp only [Equiv.trans_apply, ofMul_mul, LinearEquiv.coe_toEquiv, map_add]
  · simp only [Equiv.trans_apply, LinearEquiv.coe_toEquiv, conjRep_apply,
      LinearEquiv.apply_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eJPHom_apply,
      eJPinvHom_apply,
      mulAutToEnd_apply]

theorem exists_proj {L : Type*}
    [Group L] {M : Subgroup L} [M.Normal] (ψ : L ⧸ M ≃* J2) :
    ∃ π : L →* ↥P, Function.Surjective π ∧ (∀ x, π x = 1 ↔ x ∈ M) ∧
      ∀ ℓ : L, eJP (π ℓ) = ψ (ℓ : L ⧸ M) := by
  refine ⟨eJPinvHom.comp (ψ.toMonoidHom.comp (QuotientGroup.mk' M)), fun g => ?_,
    fun x => ?_, fun ℓ => ?_⟩
  · obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (ψ.symm (eJP g))
    refine ⟨q, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eJPHom_apply, eJPinvHom_apply,
      QuotientGroup.mk'_apply, hq,
      MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eJPHom_apply, eJPinvHom_apply,
      QuotientGroup.mk'_apply]
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eJPHom_apply, eJPinvHom_apply,
      QuotientGroup.mk'_apply,
      MulEquiv.apply_symm_apply]

theorem kJSplit_holds :
    KJSplit := by
  intro L _ _ M _ hM2 hM1 hmin hψ d hd3 hdS hCd
  obtain ⟨ψ⟩ := hψ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEA : IsElementaryAbelian 2 ↥M :=
    isElementaryAbelian_of_minimalNormal inferInstance hM2 hM1 hmin
  letI : CommGroup ↥M := IsMulCommutative.instCommGroup
  have hsq : ∀ m : ↥M, m ^ 2 = 1 := fun m =>
    Subtype.ext (by simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) (m : L) m.2)
  letI : Module (ZMod 2) (Additive ↥M) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hsq, ofMul_one]
  have hRM : ∀ r ∈ M, ∀ m ∈ M, r * m = m * r := fun r hr m hm =>
    congrArg Subtype.val (mul_comm (⟨r, hr⟩ : ↥M) ⟨m, hm⟩)
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).2 hM1
  have hσ : ∀ (ℓ : L) (m : ↥M), conjActionJ2 hRM ψ (ψ (ℓ : L ⧸ M)) m =
      ⟨ℓ * m * ℓ⁻¹, (inferInstance : M.Normal).conj_mem m m.2 ℓ⟩ :=
    fun ℓ m => Subtype.ext (conjActionJ2_mk hRM ψ ℓ m)
  have hirr : ∀ K : Subgroup ↥M, (∀ x : J2, ∀ a ∈ K, conjActionJ2 hRM ψ x a ∈ K) →
      K = ⊥ ∨ K = ⊤ := by
    intro K hK
    have hKn : (K.map M.subtype).Normal := ⟨fun n hn ℓ => by
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
      refine Subgroup.mem_map.2 ⟨⟨ℓ * m * ℓ⁻¹, (inferInstance : M.Normal).conj_mem m m.2 ℓ⟩,
        ?_, rfl⟩
      rw [← hσ]
      exact hK _ _ hm⟩
    rcases hmin _ hKn (Subgroup.map_subtype_le K) with hK' | hK'
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective K M.subtype_injective).1 hK'
    · right
      refine eq_top_iff.2 fun m _ => ?_
      have hm : (m : L) ∈ K.map M.subtype := by
        rw [hK']
        exact m.2
      obtain ⟨m', hm', he⟩ := Subgroup.mem_map.1 hm
      rwa [Subtype.ext he] at hm'
  have hfix : ∀ m : ↥M, conjActionJ2 hRM ψ x0J m = m → m = 1 := by
    intro m hm
    obtain ⟨g, hg⟩ := exists_conj_mk_eq_or_eq_inv hM2 ψ hd3 hdS x0J_ne_one threeCentral_x0J
    have key : ((g * d * g⁻¹) * (m : L) * (g * d * g⁻¹)⁻¹ = (m : L)) ∨
        ((g * d * g⁻¹)⁻¹ * (m : L) * (g * d * g⁻¹)⁻¹⁻¹ = (m : L)) := by
      rcases hg with hg | hg
      · left
        rw [← hg, hσ] at hm
        exact congrArg Subtype.val hm
      · right
        have hg' : x0J = ψ (((g * d * g⁻¹)⁻¹ : L) : L ⧸ M) := by
          rw [QuotientGroup.mk_inv, map_inv, hg, inv_inv]
        rw [hg', hσ] at hm
        exact congrArg Subtype.val hm
    exact Subtype.ext (eq_one_of_conj_fixes hCd m.2 key)
  obtain ⟨ρ, e, hρ, he, hact⟩ := exists_coords_of_action (conjActionJ2 hRM ψ) hirr hfix
  obtain ⟨π, hπ, hker, heπ⟩ := exists_proj ψ
  refine exists_complement_of_coords π hπ hker ρ hρ e he fun ℓ m => ?_
  rw [← hσ, ← heπ, hact]

end CFSG.RankThree.PartTwo.J2Residue
