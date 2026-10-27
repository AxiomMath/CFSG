module

public import CFSG.Quasithin.Vol2.Ch11SecD557NatA
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.SteinbergBSNoncentralHyperplane
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase
public import CFSG.Quasithin.Background.G2SL3Setting
public import CFSG.Quasithin.Vol2.Ch11SecD551C

public section

namespace CFSG.Quasithin.H13

open CFSG.Blueprint CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model CFSG.Quasithin.Vol2.Ch11 CFSG.Quasithin.Vol2.Ch11.SecD
open scoped MatrixGroups IsMulCommutative

namespace L128Four

variable {G : Type} [Group G] [Finite G] {L V V₁ P : Subgroup G}

theorem isSimpleGroup_of_binaryNaturalSL {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    (h : BinaryNaturalSL H ⊤ ⊥ 3 1) : IsSimpleGroup ↥H := by
  obtain ⟨K, hF, hfin, hK, π, hπ⟩ := h
  have hπb : Function.Bijective π := ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩
  have : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
    norm_num
  let σ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hFcard
  have : IsSimpleGroup SL(3, ZMod 2) := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  exact ((MulEquiv.ofBijective π hπb).symm.trans
    ((statedSLEquiv' 3 K).trans (slMapEquiv σ))).isSimpleGroup

theorem isNaturalSL3Module_of_realizes [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (π : ↥(StatedSL 3 K) →* ↥(autOn L V))
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥V) (autOn L V) ⊤ ⊥ π)
    (hP : ∀ a ∈ L, a ∈ Subgroup.centralizer (V : Set G) ↔ a ∈ P)
    (hV₁ : V₁ ≤ V) (hV₁2 : Nat.card V₁ = 2) : IsNaturalSL3Module 1 L P V V₁ := by
  have hπi : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful _)
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  have hπb : Function.Bijective π := ⟨hπi, hπs⟩
  let πe : ↥(StatedSL 3 K) ≃* ↥(autOn L V) := MulEquiv.ofBijective π hπb
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hFcard : Fintype.card K = Fintype.card (GaloisField 2 1) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 1 one_ne_zero, pow_one]
  let σ : K ≃+* GaloisField 2 1 := FiniteField.ringEquivOfCardEq hFcard
  let c : ↥L →* ↥(autOn L V) :=
    (MulEquiv.subgroupCongr (SecA.range_conjHomL V L hLV)).toMonoidHom.comp
      (SecA.conjHomL V L hLV).rangeRestrict
  have hc : ∀ a : ↥L, ((c a : ↥(autOn L V)) : MulAut ↥V) = SecA.conjV V a (hLV a.2) :=
    fun a => rfl
  have hcs : Function.Surjective c :=
    (MulEquiv.subgroupCongr (SecA.range_conjHomL V L hLV)).surjective.comp
      (MonoidHom.rangeRestrict_surjective _)
  let θ : ↥L →* SL(3, GaloisField 2 1) := (slMapEquiv σ).toMonoidHom.comp
    ((statedSLEquiv' 3 K).toMonoidHom.comp (πe.symm.toMonoidHom.comp c))
  have hθs : Function.Surjective θ :=
    (slMapEquiv σ).surjective.comp ((statedSLEquiv' 3 K).surjective.comp
      (πe.symm.surjective.comp hcs))
  have hθker : θ.ker = P.subgroupOf L := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : θ a = 1 ↔ c a = 1 := by
      simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    have h2 : c a = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) := by
      constructor
      · intro ha
        have := congrArg (fun x : ↥(autOn L V) => (x : MulAut ↥V)) ha
        simp only [hc, Subgroup.coe_one] at this
        exact mem_centralizer_of_conjV_eq_one _ this
      · intro haC
        apply Subtype.ext
        rw [hc]
        ext v
        rw [SecA.conjV_apply_coe]
        simp only [Subgroup.coe_one, MulAut.one_apply]
        rw [(Subgroup.mem_centralizer_iff.mp haC v v.2).symm, mul_inv_cancel_right]
    rw [h1, h2]
    exact hP (a : G) a.2
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' := (hβk u).mp hu
    rw [Subgroup.mem_bot] at hu'
    exact Subtype.ext hu'
  let βe := MulEquiv.ofBijective β ⟨hβi, hβs⟩
  let j : Multiplicative (Fin 3 → K) →* ↥(FFModel.nat (StatedSL 3 K)).sec :=
    { toFun := fun m => ⟨m, Subgroup.mem_top m⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ι : Multiplicative (Fin 3 → K) →* ↥(FFModel.nat (StatedSL 3 K)).sec ⧸
      (FFModel.nat (StatedSL 3 K)).ker.subgroupOf (FFModel.nat (StatedSL 3 K)).sec :=
    (QuotientGroup.mk' _).comp j
  have hιi : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hm' := (QuotientGroup.eq_one_iff _).mp hm
    rw [Subgroup.mem_subgroupOf] at hm'
    exact (Subgroup.mem_bot).mp hm'
  have hιs : Function.Surjective ι := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => exact ⟨x.1, rfl⟩
  let ιe := MulEquiv.ofBijective ι ⟨hιi, hιs⟩
  let ψ₀ : ↥V ≃* Multiplicative (Fin 3 → K) := Subgroup.topEquiv.symm.trans (βe.trans ιe.symm)
  have key : ∀ v : ↥V, β ⟨v, trivial⟩ = ι (ψ₀ v) := by
    intro v
    have h1 : ιe (ψ₀ v) = β ⟨v, trivial⟩ := by
      change ιe (ιe.symm (βe (Subgroup.topEquiv.symm v))) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    exact h1.symm
  let ψ : ↥V ≃* W3 (GaloisField 2 1) := ψ₀.trans (vecMapEquiv σ)
  have hequiv : ∀ (a : ↥L) (v : ↥V),
      ψ (conjAct V ⟨a, hLV a.2⟩ v) = natAct3 (θ a) (ψ v) := by
    intro a v
    have hγ : π (πe.symm (c a)) = c a := πe.apply_symm_apply (c a)
    have h1 := hβe (πe.symm (c a)) ⟨v, trivial⟩ ⟨ψ₀ v, trivial⟩ trivial trivial (key v)
    have h2 : ψ₀ ((π (πe.symm (c a)) : MulAut ↥V) v) =
        natAct (StatedSL 3 K) (πe.symm (c a)) (ψ₀ v) := by
      apply hιi
      rw [← key]
      exact h1
    rw [hγ, hc] at h2
    have h3 : conjAct V ⟨a, hLV a.2⟩ v = SecA.conjV V a (hLV a.2) v := rfl
    rw [h3]
    show vecMapEquiv σ (ψ₀ _) = natAct3 (θ a) (vecMapEquiv σ (ψ₀ v))
    rw [h2]
    have h4 := vecMapEquiv_mulVec σ (statedSLEquiv' 3 K (πe.symm (c a))) (ψ₀ v)
    rw [coe_statedSLEquiv'] at h4
    exact h4
  have h01 : ∀ x : GaloisField 2 1, x = 0 ∨ x = 1 := by
    classical
    intro x
    by_contra hx
    push Not at hx
    have hcard : Fintype.card (GaloisField 2 1) = 2 := by
      rw [← hFcard, ← Nat.card_eq_fintype_card, hK]
    have h3 : ({0, 1, x} : Finset (GaloisField 2 1)).card = 3 :=
      Finset.card_eq_three.mpr ⟨0, 1, x, zero_ne_one, hx.1.symm, hx.2.symm, rfl⟩
    have := Finset.card_le_univ ({0, 1, x} : Finset (GaloisField 2 1))
    omega
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ V₁, y ≠ 1 := by
    by_contra hall
    push Not at hall
    have : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall V₁).2 hall
    rw [this, Subgroup.card_bot] at hV₁2
    omega
  have hyV : y ∈ V := hV₁ hy
  have hV₁eq : ∀ x ∈ V₁, x = 1 ∨ x = y := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (SteinbergBS.eq_of_card_le_two hV₁2.le hx hy hx1 hy1)
  have hw0 : Multiplicative.toAdd (ψ ⟨y, hyV⟩) ≠ 0 := by
    intro h0
    have : ψ ⟨y, hyV⟩ = 1 := by rw [← ofAdd_toAdd (ψ ⟨y, hyV⟩), h0, ofAdd_zero]
    exact hy1 (congrArg Subtype.val (ψ.injective (this.trans (map_one ψ).symm)))
  refine ⟨hLV, θ, ψ, hθs, hθker, hequiv, Multiplicative.toAdd (ψ ⟨y, hyV⟩), hw0, fun v => ?_⟩
  constructor
  · intro hv
    rcases hV₁eq v hv with h | h
    · refine ⟨0, ?_⟩
      have : v = 1 := Subtype.ext h
      simp [this]
    · refine ⟨1, ?_⟩
      have : v = ⟨y, hyV⟩ := Subtype.ext h
      simp [this]
  · rintro ⟨x, hx⟩
    rcases h01 x with h | h
    · subst h
      have h1 : ψ v = 1 := by rw [← ofAdd_toAdd (ψ v), hx, zero_smul, ofAdd_zero]
      have : v = 1 := ψ.injective (h1.trans (map_one ψ).symm)
      rw [this]
      exact V₁.one_mem
    · subst h
      have h1 : ψ v = ψ ⟨y, hyV⟩ := by
        rw [← ofAdd_toAdd (ψ v), hx, one_smul, ofAdd_toAdd]
      have : v = ⟨y, hyV⟩ := ψ.injective h1
      rw [this]
      exact hy

end L128Four

end CFSG.Quasithin.H13
