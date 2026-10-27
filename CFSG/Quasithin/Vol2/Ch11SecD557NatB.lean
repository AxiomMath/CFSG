module

public import CFSG.Quasithin.Vol2.Ch11SecD557NatA
public import CFSG.Quasithin.Background.G2SL3Setting
public import CFSG.Quasithin.Vol2.Ch11SecD551A
public import CFSG.Quasithin.Vol2.Ch11SecD551C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem pCoreOf_eq_inf_pCoreOf_sup (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L = L ⊓ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) ?_) ?_
  · exact le_ROf' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
  · refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun l hl =>
        mem_normalizer_inf (Subgroup.le_normalizer hl)
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)

def scalHom {F : Type} [Field F] (c : F) : W3 F →* W3 F where
  toFun w := Multiplicative.ofAdd (c • Multiplicative.toAdd w)
  map_one' := by simp
  map_mul' a b := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add, toAdd_mul, smul_add]

theorem scalHom_natAct3 {F : Type} [Field F] (c : F) (A : SL(3, F)) (w : W3 F) :
    scalHom c (natAct3 A w) = natAct3 A (scalHom c w) := by
  rw [natAct3_apply, natAct3_apply]
  show Multiplicative.ofAdd (c • Multiplicative.toAdd (Multiplicative.ofAdd
      (A • Multiplicative.toAdd w))) =
    Multiplicative.ofAdd (A • Multiplicative.toAdd (Multiplicative.ofAdd
      (c • Multiplicative.toAdd w)))
  rw [toAdd_ofAdd, toAdd_ofAdd, Matrix.SpecialLinearGroup.smul_def,
    Matrix.SpecialLinearGroup.smul_def, smul_comm (A : Matrix (Fin 3) (Fin 3) F) c]

theorem isNaturalSL3Module_of (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) [IsMulCommutative ↥(fsuV T I)] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (he : Nonempty (↥(autOn L (fsuV T I)) ≃* SL(3, K)))
    (π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I)))
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π) :
    IsNaturalSL3Module n L (pCoreOf 2 (L ⊔ T)) (fsuV T I) V₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by have := h.one_lt; omega
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV h
  obtain ⟨X, hX⟩ := exists_isCartanX h
  have hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    (h1141 G T L I n V₁ X h hV₁ hX).1.1
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv' : (v : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨v.2, hv⟩
    rw [hCV, Subgroup.mem_bot] at hv'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hv')
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  obtain ⟨e⟩ := he
  have hπs' : Function.Surjective (π : ↥(StatedSL 3 K) → ↥(autOn L (fsuV T I))) := hπs
  have hπb : Function.Bijective (π : ↥(StatedSL 3 K) → ↥(autOn L (fsuV T I))) :=
    hπs'.bijective_of_nat_card_le (by
      rw [Nat.card_congr (statedSLEquiv' 3 K).toEquiv, Nat.card_congr e.toEquiv])
  let πe : ↥(StatedSL 3 K) ≃* ↥(autOn L (fsuV T I)) := MulEquiv.ofBijective π hπb
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hFcard : Fintype.card K = Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card 2 n hn0]
  let σ : K ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq hFcard
  let c : ↥L →* ↥(autOn L (fsuV T I)) :=
    (MulEquiv.subgroupCongr (SecA.range_conjHomL (fsuV T I) L hLV)).toMonoidHom.comp
      (SecA.conjHomL (fsuV T I) L hLV).rangeRestrict
  have hc : ∀ a : ↥L, ((c a : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) =
      SecA.conjV (fsuV T I) a (hLV a.2) := fun a => rfl
  have hcs : Function.Surjective c :=
    (MulEquiv.subgroupCongr (SecA.range_conjHomL (fsuV T I) L hLV)).surjective.comp
      (MonoidHom.rangeRestrict_surjective _)
  let θ : ↥L →* SL(3, GaloisField 2 n) := (slMapEquiv σ).toMonoidHom.comp
    ((statedSLEquiv' 3 K).toMonoidHom.comp (πe.symm.toMonoidHom.comp c))
  have hθs : Function.Surjective θ :=
    (slMapEquiv σ).surjective.comp ((statedSLEquiv' 3 K).surjective.comp
      (πe.symm.surjective.comp hcs))
  have hθker : θ.ker = (pCoreOf 2 (L ⊔ T)).subgroupOf L := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : θ a = 1 ↔ c a = 1 := by
      simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    rw [h1]
    have h2 : c a = 1 ↔ (a : G) ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
      constructor
      · intro ha
        have := congrArg (fun x : ↥(autOn L (fsuV T I)) => (x : MulAut ↥(fsuV T I))) ha
        simp only [hc, Subgroup.coe_one] at this
        exact ⟨a.2, mem_centralizer_of_conjV_eq_one _ this⟩
      · rintro ⟨-, haC⟩
        apply Subtype.ext
        rw [hc]
        ext v
        rw [SecA.conjV_apply_coe]
        simp only [Subgroup.coe_one, MulAut.one_apply]
        rw [(Subgroup.mem_centralizer_iff.mp haC v v.2).symm, mul_inv_cancel_right]
    rw [h2, SecA.centralizer_eq_pCoreOf h1102 h, pCoreOf_eq_inf_pCoreOf_sup h.normal]
    exact ⟨fun hx => hx.2, fun hx => ⟨a.2, hx⟩⟩
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' := (hβk u).mp hu
    rw [hZ, Subgroup.mem_bot] at hu'
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
  let ψ₀ : ↥(fsuV T I) ≃* Multiplicative (Fin 3 → K) :=
    Subgroup.topEquiv.symm.trans (βe.trans ιe.symm)
  have key : ∀ v : ↥(fsuV T I), β ⟨v, trivial⟩ = ι (ψ₀ v) := by
    intro v
    have h1 : ιe (ψ₀ v) = β ⟨v, trivial⟩ := by
      change ιe (ιe.symm (βe (Subgroup.topEquiv.symm v))) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    exact h1.symm
  let ψ : ↥(fsuV T I) ≃* W3 (GaloisField 2 n) := ψ₀.trans (vecMapEquiv σ)
  have hequiv : ∀ (a : ↥L) (v : ↥(fsuV T I)),
      ψ (CFSG.Quasithin.conjAct (fsuV T I) ⟨a, hLV a.2⟩ v) = natAct3 (θ a) (ψ v) := by
    intro a v
    have hγ : π (πe.symm (c a)) = c a := πe.apply_symm_apply (c a)
    have h1 := hβe (πe.symm (c a)) ⟨v, trivial⟩ ⟨ψ₀ v, trivial⟩ trivial trivial (key v)
    have h2 : ψ₀ ((π (πe.symm (c a)) : MulAut ↥(fsuV T I)) v) =
        natAct (StatedSL 3 K) (πe.symm (c a)) (ψ₀ v) := by
      apply hιi
      rw [← key]
      exact h1
    rw [hγ, hc] at h2
    have h3 : CFSG.Quasithin.conjAct (fsuV T I) ⟨a, hLV a.2⟩ v =
        SecA.conjV (fsuV T I) a (hLV a.2) v := rfl
    rw [h3]
    show vecMapEquiv σ (ψ₀ _) = natAct3 (θ a) (vecMapEquiv σ (ψ₀ v))
    rw [h2]
    have h4 := vecMapEquiv_mulVec σ (statedSLEquiv' 3 K (πe.symm (c a))) (ψ₀ v)
    rw [coe_statedSLEquiv'] at h4
    exact h4
  obtain ⟨-, hES, hidx, -⟩ := SecA.isFlagW_of_isVi h hV₁
  rw [hZ] at hES hidx
  have hcardU : Nat.card ↥(V₁.subgroupOf (fsuV T I)) = 2 ^ n := by
    rw [Subgroup.relIndex_bot_left] at hidx
    rw [hidx, pow_one]
  set A := (V₁.subgroupOf (fsuV T I)).map ψ.toMonoidHom with hAdef
  have hAcard : Nat.card A = Nat.card (GaloisField 2 n) := by
    rw [hAdef, Subgroup.card_map_of_injective ψ.injective, hcardU, GaloisField.card 2 n hn0]
  have hsmul : ∀ c' : GaloisField 2 n, ∀ a ∈ A,
      Multiplicative.ofAdd (c' • Multiplicative.toAdd a) ∈ A := by
    intro c' a ha
    obtain ⟨u, hu, rfl⟩ := ha
    let φ : ↥(fsuV T I) →* ↥(fsuV T I) :=
      ψ.symm.toMonoidHom.comp ((scalHom c').comp ψ.toMonoidHom)
    have hφZ : ∀ z ∈ (⊥ : Subgroup ↥(fsuV T I)), φ z ∈ (⊥ : Subgroup ↥(fsuV T I)) := by
      intro z hz
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one]
    have hφH : ∀ g ∈ autOn L (fsuV T I), ∀ w : ↥(fsuV T I),
        φ (g w) * (g (φ w))⁻¹ ∈ (⊥ : Subgroup ↥(fsuV T I)) := by
      intro g hg w
      obtain ⟨x, hxL, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hg
      rw [Subgroup.mem_bot, mul_inv_eq_one]
      apply ψ.injective
      have hx := hequiv ⟨x, hxL⟩
      change ∀ v, ψ (SecA.conjV (fsuV T I) x hxV v) = natAct3 (θ ⟨x, hxL⟩) (ψ v) at hx
      simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      rw [hx, hx, MulEquiv.apply_symm_apply, scalHom_natAct3]
    have hφu := hES φ hφZ hφH u hu
    refine ⟨φ u, hφu, ?_⟩
    simp [φ, scalHom]
  obtain ⟨w, hw0, hw⟩ := exists_eq_smul_of_card A hsmul hAcard
  refine ⟨hLV, θ, ψ, hθs, hθker, hequiv, w, hw0, fun v => ?_⟩
  rw [← hw]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨u, hu, huv⟩
    have huv' : u = v := ψ.injective huv
    rw [← huv']
    exact hu

end CFSG.Quasithin.Vol2.Ch11.SecD
