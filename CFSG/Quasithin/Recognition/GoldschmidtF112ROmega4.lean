module

public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528EBlock

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13 (IsOmega4MinusBlock)
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem lieModel_of_isL2Quot {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (h : IsL2Quot n (oTwoQuot ↥L)) : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, GaloisField 2 n,
    inferInstance, inferInstance, hK, ⟨?_⟩⟩
  · intro h2
    have : 2 ^ n = 2 ^ 1 := by simpa using h2
    have := Nat.pow_right_injective le_rfl this
    omega
  · intro h2
    have h3 : 2 ^ n = 3 := by simpa using h2
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  exact ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥L)).trans e).trans
    (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL (GaloisField 2 n) 2 2 n (by omega)
      hK).symm

theorem mem_hermSub_iff {F : Type} [Field F] [CharP F 2] (a : ℕ) (X : Matrix (Fin 2) (Fin 2) F) :
    Multiplicative.ofAdd X ∈ hermSub a (Fin 2) F ↔ X.map (· ^ 2 ^ a) = X.transpose := by
  change (frobPow a X).transpose = X ↔ _
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    rw [Matrix.transpose_transpose] at this
    exact this
  · intro h
    change (X.map (· ^ 2 ^ a)).transpose = X
    rw [h, Matrix.transpose_transpose]

theorem isOmega4MinusBlock_of_type {L : Subgroup G} {m : ℕ} (hm : 1 ≤ m) (hB : IsBlock2 L L)
    (hq : IsL2Quot (2 * m) (oTwoQuot ↥L)) (hT : IsOmega4MinusType L m) :
    IsOmega4MinusBlock L m := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hB.1
  set U := blockU L with hU
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβim, hβk, hβe⟩ := hT
  have hLN : L ≤ Subgroup.normalizer (U : Set G) := H13.Omega4.le_normalizer_blockU L
  haveI hcomm : IsMulCommutative ↥U :=
    ⟨⟨fun a b => Subtype.ext (H13.Omega4.blockU_comm hS a.2 b.2)⟩⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hF
  refine ⟨hB, lieModel_of_isL2Quot (by omega) hq, hcomm, F, inferInstance, inferInstance,
    inferInstance, by rw [Nat.card_eq_fintype_card, hF], ?_⟩
  have hmemA : ∀ l : ↥L, conjAct U (Subgroup.inclusion hLN l) ∈ autOn L U := fun l =>
    ⟨Subgroup.inclusion hLN l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  let c : ↥L →* ↥(autOn L U) :=
    ((conjAct U).comp (Subgroup.inclusion hLN)).codRestrict (autOn L U) hmemA
  have hc : ∀ (l : ↥L) (u : ↥U), (((c l : MulAut ↥U) u : ↥U) : G) = l * u * l⁻¹ := by
    intro l u
    simp [c, conjAct]
  have hcs : Function.Surjective c := by
    rintro ⟨h, x, hx, rfl⟩
    exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, Subtype.ext rfl⟩
  have hker : α.ker ≤ c.ker := by
    intro l hl
    rw [hαk, CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore] at hl
    have hlQ : (l : G) ∈ blockQ L := ⟨l, hl, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rw [hc]
    have hu := (Subgroup.mem_inf.mp (hS.2.2.1.1 u.2)).2
    have := Subgroup.mem_centralizer_iff.mp hu l hlQ
    simp [this]
  set sE := specialLinearGroupEquivStatedSL 2 F with hsE
  set e := QuotientGroup.quotientKerEquivOfSurjective α hαs with he
  let π : (FFModel.twistTensor m (StatedSL 2 F)).Gam →* ↥(autOn L U) :=
    (QuotientGroup.lift α.ker c hker).comp (e.symm.toMonoidHom.comp sE.symm.toMonoidHom)
  have hπ : ∀ l : ↥L, π (sE (α l)) = c l := by
    intro l
    have h1 : e.symm (α l) = (QuotientGroup.mk l : ↥L ⧸ α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift α.ker c hker (e.symm (sE.symm (sE (α l)))) = c l
    rw [MulEquiv.symm_apply_apply, h1, QuotientGroup.lift_mk]
  have hγ : ∀ γ : ↥(StatedSL 2 F), ∃ l : ↥L, γ = sE (α l) := by
    intro γ
    obtain ⟨l, hl⟩ := hαs (sE.symm γ)
    exact ⟨l, by rw [hl, MulEquiv.apply_symm_apply]⟩
  have hπs : Function.Surjective π := by
    intro h
    obtain ⟨l, rfl⟩ := hcs h
    exact ⟨_, hπ l⟩
  have hconj : ∀ (l : ↥L) (u : ↥U), (l : G) * u * (l : G)⁻¹ ∈ U := fun l u =>
    (Subgroup.mem_normalizer_iff.mp (hLN l.2) u).mp u.2
  have hβmem : ∀ u : ↥U, β u ∈ hermSub m (Fin 2) F := fun u =>
    (mem_hermSub_iff m (Multiplicative.toAdd (β u))).2 ((hβim _).1 ⟨u, rfl⟩)
  let β₁ : ↥U →* ↥(FFModel.twistTensor m (StatedSL 2 F)).sec := β.codRestrict _ hβmem
  have hβ₁s : Function.Surjective β₁ := by
    rintro ⟨X, hX⟩
    obtain ⟨u, hu⟩ := (hβim (Multiplicative.toAdd X)).2
      ((mem_hermSub_iff m (Multiplicative.toAdd X)).1 hX)
    exact ⟨u, Subtype.ext hu⟩
  refine ⟨π, hπs, le_top, bot_le, fun _ _ _ => Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
  ·
    intro h z hz
    obtain ⟨l, rfl⟩ := hcs h
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have hzl : (l : G) * z = z * l :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 l l.2
    rw [hc, hzl, Subgroup.coe_inv, mul_inv_cancel_right]
    exact hz
  ·
    intro γ X hX
    obtain ⟨l, rfl⟩ := hγ γ
    obtain ⟨u, hu⟩ := (hβim (Multiplicative.toAdd X)).2
      ((mem_hermSub_iff m (Multiplicative.toAdd X)).1 hX)
    have h := hβe l u ⟨_, hconj l u⟩ rfl
    have : twistAct m (StatedSL 2 F) (sE (α l)) X = β ⟨_, hconj l u⟩ := by
      apply Multiplicative.toAdd.injective
      rw [h, hu]
      rfl
    change twistAct m (StatedSL 2 F) (sE (α l)) X ∈ hermSub m (Fin 2) F
    rw [this]
    exact hβmem _
  ·
    intro γ X hX
    have hX1 : X = 1 := Subgroup.mem_bot.mp hX
    subst hX1
    show twistAct m (StatedSL 2 F) γ 1 ∈ (⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))
    rw [Subgroup.mem_bot]
    apply Multiplicative.toAdd.injective
    simp [twistAct]
  · refine ⟨(QuotientGroup.mk' _).comp (β₁.comp (Subgroup.topEquiv).toMonoidHom), ?_, ?_, ?_⟩
    · exact (QuotientGroup.mk'_surjective _).comp (hβ₁s.comp Subgroup.topEquiv.surjective)
    · intro u
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      change β u = 1 ↔ _
      rw [← MonoidHom.mem_ker, hβk]
    · intro γ u X hu hX hβX
      obtain ⟨l, rfl⟩ := hγ γ
      have hXu : ((X : (FFModel.twistTensor m (StatedSL 2 F)).Amb) :
          Multiplicative (Matrix (Fin 2) (Fin 2) F)) = β (u : ↥U) := by
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          Subgroup.mem_subgroupOf] at hβX
        have h1 := Subgroup.mem_bot.mp
          (show _ ∈ (⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))) from hβX)
        have h2 := inv_mul_eq_one.mp h1
        exact h2.symm
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      congr 1
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      show Multiplicative.toAdd (β _) = Multiplicative.toAdd
        (twistAct m (StatedSL 2 F) (sE (α l)) X.1)
      rw [hXu]
      refine hβe l u _ ?_
      show ((((π (sE (α l)) : ↥(autOn L U)) : MulAut ↥U) (u : ↥U) : ↥U) : G) = _
      rw [hπ, hc]

end CFSG.Quasithin.F112R

