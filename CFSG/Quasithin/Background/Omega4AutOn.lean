module

public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 CFSG.QuasithinUnique CFSG.Open
open scoped Matrix IsMulCommutative

theorem binaryOrthogonalFour_autOn {G : Type} [Group G] {L V : Subgroup G} {m : ℕ}
    [IsMulCommutative ↥V] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ (2 * m))
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαV : ∀ ℓ : ↥L, α ℓ = 1 → ∀ v ∈ V, (ℓ : G) * v * (ℓ : G)⁻¹ = v)
    (β : ↥V →* Multiplicative (Matrix (Fin 2) (Fin 2) F)) (hβ : Function.Injective β)
    (hβim : ∀ X : Matrix (Fin 2) (Fin 2) F,
      (∃ v : ↥V, Multiplicative.toAdd (β v) = X) ↔ X.map (· ^ 2 ^ m) = X.transpose)
    (hβeq : ∀ (ℓ : ↥L) (v w : ↥V), (w : G) = ℓ * v * ℓ⁻¹ →
      Multiplicative.toAdd (β w) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *
        Multiplicative.toAdd (β v) *
          ((α ℓ : Matrix (Fin 2) (Fin 2) F).map (· ^ 2 ^ m)).transpose) :
    BinaryOrthogonalFour (V := ↥V) (autOn L V) ⊤ ⊥ m := by
  classical
  let eSL := specialLinearGroupEquivStatedSL 2 F
  let α' : ↥L →* ↥(StatedSL 2 F) := eSL.toMonoidHom.comp α
  have hα's : Function.Surjective α' := eSL.surjective.comp hα
  let ρ : ↥L →* ↥(autOn L V) := T4213N.rhoAut hLV
  have hker : α'.ker ≤ ρ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    have ha1 : α a = 1 := eSL.map_eq_one_iff.mp ha
    apply Subtype.ext
    refine InternalSec.conjAct_eq_one_of_mem_centralizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro v hv
    have hcomm : (a : G) * v = v * (a : G) := by
      calc (a : G) * v = ((a : G) * v * (a : G)⁻¹) * (a : G) := by group
        _ = v * (a : G) := by rw [hαV a ha1 v hv]
    exact hcomm.symm
  set e := QuotientGroup.quotientKerEquivOfSurjective α' hα's with he
  set π : ↥(StatedSL 2 F) →* ↥(autOn L V) :=
    (QuotientGroup.lift α'.ker ρ hker).comp e.symm.toMonoidHom with hπ
  have hπα : ∀ a : ↥L, π (α' a) = ρ a := by
    intro a
    have h1 : e.symm (α' a) = (a : ↥L ⧸ α'.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hπs : Function.Surjective π := by
    intro χ
    obtain ⟨a, rfl⟩ := T4213N.rhoAut_surjective hLV χ
    exact ⟨α' a, hπα a⟩
  let f : ↥V →* ↥(hermSub m (Fin 2) F) :=
    β.codRestrict (hermSub m (Fin 2) F) fun v => by
      rw [mem_hermSub]
      have h := (hβim (Multiplicative.toAdd (β v))).mp ⟨v, rfl⟩
      simpa [frobPow] using congrArg Matrix.transpose h
  have hfi : Function.Injective f := by
    intro v w hvw
    exact hβ (Subtype.ext_iff.mp hvw)
  have hfs : Function.Surjective f := by
    rintro ⟨X, hX⟩
    rw [mem_hermSub] at hX
    have hX' : (Multiplicative.toAdd X).map (· ^ 2 ^ m) =
        (Multiplicative.toAdd X).transpose := by
      have h := congrArg Matrix.transpose hX
      simpa [frobPow, Matrix.transpose_transpose] using h
    obtain ⟨v, hv⟩ := (hβim (Multiplicative.toAdd X)).mpr hX'
    refine ⟨v, Subtype.ext ?_⟩
    change β v = X
    exact Multiplicative.toAdd.injective hv
  let B : ↥(⊤ : Subgroup ↥V) →* ↥(hermSub m (Fin 2) F) ⧸
      ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf
        (hermSub m (Fin 2) F)) :=
    (QuotientGroup.mk' ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf
      (hermSub m (Fin 2) F))).comp (f.comp (⊤ : Subgroup ↥V).subtype)
  have hBapp : ∀ u : ↥(⊤ : Subgroup ↥V),
      B u = QuotientGroup.mk (f (u : ↥V)) := fun _ => rfl
  have hmk : ∀ x y : ↥(hermSub m (Fin 2) F),
      (QuotientGroup.mk x : ↥(hermSub m (Fin 2) F) ⧸
        ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf
          (hermSub m (Fin 2) F))) = QuotientGroup.mk y ↔ x = y := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.coe_mul,
      Subgroup.coe_inv, inv_mul_eq_one]
    exact Subtype.ext_iff.symm
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, π, ?_⟩
  refine ⟨hπs, bot_le, bot_le, fun _ _ _ => trivial, fun h z hz => ?_,
    fun γ x hx => twistAct_mem_hermSub m (StatedSL 2 F) hF γ hx, fun γ x hx => ?_,
    B, ?_, fun u => ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · have hx1 : x = 1 := hx
    show twistAct m (StatedSL 2 F) γ x ∈
      (⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))
    rw [Subgroup.mem_bot, hx1]
    exact act_map_one (twistAct m (StatedSL 2 F)) γ (twistAct_mul m (StatedSL 2 F) γ)
  · intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf
        (hermSub m (Fin 2) F)) q
    have hx2 : (frobPow m (Multiplicative.toAdd x.1))ᵀ = Multiplicative.toAdd x.1 :=
      (mem_hermSub m).mp x.2
    have hx2' : (Multiplicative.toAdd x.1).map (· ^ 2 ^ m) =
        (Multiplicative.toAdd x.1).transpose := by
      have h := congrArg Matrix.transpose hx2
      simpa [frobPow, Matrix.transpose_transpose] using h
    obtain ⟨v, hv⟩ := (hβim (Multiplicative.toAdd x.1)).mpr hx2'
    refine ⟨⟨v, trivial⟩, ?_⟩
    show QuotientGroup.mk (f v) = QuotientGroup.mk x
    rw [hmk]
    refine Subtype.ext ?_
    change β v = x.1
    exact Multiplicative.toAdd.injective hv
  · show (QuotientGroup.mk (f (u : ↥V)) : ↥(hermSub m (Fin 2) F) ⧸
      ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf
        (hermSub m (Fin 2) F))) = 1 ↔ (u : ↥V) ∈ ⊥
    rw [show (1 : ↥(hermSub m (Fin 2) F) ⧸
        ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf
          (hermSub m (Fin 2) F))) =
        QuotientGroup.mk (1 : ↥(hermSub m (Fin 2) F)) from rfl, hmk, Subgroup.mem_bot]
    exact map_eq_one_iff f hfi
  · intro γ u x hu hx hum
    let γ' : ↥(StatedSL 2 F) := γ
    obtain ⟨a, ha⟩ := hα's γ'
    have hum' : (QuotientGroup.mk (f (u : ↥V)) : ↥(hermSub m (Fin 2) F) ⧸
        ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf
          (hermSub m (Fin 2) F))) = QuotientGroup.mk x := by
      rw [← hBapp u]
      exact hum
    have hfu : f (u : ↥V) = x := (hmk _ _).mp hum'
    show QuotientGroup.mk (f (((π γ' : ↥(autOn L V)) : MulAut ↥V) (u : ↥V))) =
      QuotientGroup.mk (⟨twistAct m (StatedSL 2 F) γ' x.1, hx⟩ :
        ↥(hermSub m (Fin 2) F))
    rw [hmk]
    apply Subtype.ext
    change Multiplicative.toAdd (f ((((π γ' : ↥(autOn L V)) : MulAut ↥V) (u : ↥V)))).1 =
      Multiplicative.toAdd (twistAct m (StatedSL 2 F) γ' x.1)
    have hstep : Multiplicative.toAdd
        (f ((((π γ' : ↥(autOn L V)) : MulAut ↥V) (u : ↥V)))).1 =
        Multiplicative.toAdd (twistAct m (StatedSL 2 F) γ' (f (u : ↥V))) := by
      rw [← ha, hπα a]
      show Multiplicative.toAdd (β (((ρ a : ↥(autOn L V)) : MulAut ↥V) (u : ↥V))) =
        (α a : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (β (u : ↥V)) *
          ((α a : Matrix (Fin 2) (Fin 2) F).map (· ^ 2 ^ m)).transpose
      exact hβeq a (u : ↥V) (((ρ a : ↥(autOn L V)) : MulAut ↥V) (u : ↥V))
        (T4213N.rhoAut_apply hLV a (u : ↥V))
    have hfu' : (f (u : ↥V) : Multiplicative (Matrix (Fin 2) (Fin 2) F)) = x.1 :=
      congrArg Subtype.val hfu
    rw [hstep, hfu']

theorem IsOmega4MinusType.binaryOrthogonalFour_autOn {G : Type} [Group G] {L : Subgroup G}
    {m : ℕ} (hT : IsOmega4MinusType L m) (hZ : blockZ L = ⊥) [IsMulCommutative ↥(blockU L)]
    (hLU : L ≤ Subgroup.normalizer (blockU L : Set G))
    (hQU : CFSG.Open.pCoreOf 2 L ≤ Subgroup.centralizer (blockU L : Set G)) :
    BinaryOrthogonalFour (V := ↥(blockU L)) (autOn L (blockU L)) ⊤ ⊥ m := by
  obtain ⟨F, hFld, hFintype, hFcard, α, hα, hαker, β, hβim, hβker, hβeq⟩ := hT
  letI := hFld
  letI := hFintype
  have hFchar : CharP F 2 := charP_of_card_eq_prime_pow (by simpa using hFcard)
  letI := hFchar
  have hFnat : Nat.card F = 2 ^ (2 * m) := by rw [Nat.card_eq_fintype_card, hFcard]
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, hZ, Subgroup.bot_subgroupOf]
  refine CFSG.Quasithin.binaryOrthogonalFour_autOn hLU hFnat α hα ?_ β hβi hβim ?_
  · intro ℓ hℓ v hv
    have hmem : (ℓ : G) ∈ CFSG.Open.pCoreOf 2 L := by
      rw [CFSG.Open.pCoreOf]
      exact Subgroup.mem_map.mpr ⟨ℓ, hαker ▸ MonoidHom.mem_ker.mpr hℓ, rfl⟩
    have hcent := Subgroup.mem_centralizer_iff.mp (hQU hmem) v hv
    calc (ℓ : G) * v * (ℓ : G)⁻¹ = v * (ℓ : G) * (ℓ : G)⁻¹ := by rw [← hcent]
      _ = v := by group
  · intro ℓ v w hw
    exact hβeq ℓ v w hw

end CFSG.Quasithin

end
