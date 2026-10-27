module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LieType.Simplicity.Classical
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace L34Br

theorem isPSL_two_two_two_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h60 : Nat.card X = 60) : IsPSL 2 2 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  obtain ⟨eX⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60
  obtain ⟨e4⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four (GaloisField 2 2)
      (by rw [hc4]; norm_num))
  refine ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hc4, ⟨?_⟩⟩
  exact eX.trans (e4.symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2)))

theorem isPSL_of_mulEquiv {X X' : Type} [Group X] [Group X'] {n p e : ℕ} (h : IsPSL n p e X)
    (f : X ≃* X') : IsPSL n p e X' := by
  obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hK, hKf, hcard, ⟨f.symm.trans e'⟩⟩

theorem isPSL_psl_two_galois :
    IsPSL 2 2 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  exact ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hc4,
    ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2)⟩⟩

variable {G : Type} [Group G]

theorem isSylowIn_map_conj {S H : Subgroup G} (hS : IsSylowIn 2 S H) (g : G) :
    IsSylowIn 2 (S.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨Subgroup.map_mono hS.1, hS.2.1.map _, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact hS.2.2

theorem isSylowIn_of_le {P Q H : Subgroup G} (hP : IsSylowIn 2 P H) (hPQ : P ≤ Q)
    (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) : IsSylowIn 2 Q H :=
  ⟨hQH, hQ, fun h2 => hP.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left H hPQ))⟩

variable [Finite G]

theorem exists_conj_le_of_isSylowIn {S H P : Subgroup G} (hS : IsSylowIn 2 S H) (hPH : P ≤ H)
    (hP : IsPGroup 2 P) : ∃ h ∈ H, P.map (MulAut.conj h).toMonoidHom ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPX : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hPX.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥H) Q hS.toSylow
  refine ⟨(c : G), c.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxQ : (⟨x, hPH hx⟩ : ↥H) ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_subgroupOf.mpr hx)
  have h2 : c * ⟨x, hPH hx⟩ * c⁻¹ ∈ ((c • Q : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hxQ, by simp [MulAut.conj_apply]⟩
  rw [hc, IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at h2
  simpa [MulAut.conj_apply] using h2

theorem card_le_of_isSylowIn {S H Q : Subgroup G} (hS : IsSylowIn 2 S H) (hQH : Q ≤ H)
    (hQ : IsPGroup 2 Q) : Nat.card Q ≤ Nat.card S := by
  obtain ⟨h, -, hle⟩ := exists_conj_le_of_isSylowIn hS hQH hQ
  calc Nat.card Q = Nat.card ↥(Q.map (MulAut.conj h).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj h).injective).symm
    _ ≤ Nat.card S := Subgroup.card_le_of_le hle

theorem isSylowIn_of_card_le {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (h : ∀ Q : Subgroup G, P ≤ Q → Q ≤ H → IsPGroup 2 Q → Nat.card Q ≤ Nat.card P) :
    IsSylowIn 2 P H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hPS⟩ := exists_isSylowIn_ge 2 hPH hP
  have hSP : S = P := (Subgroup.eq_of_le_of_card_ge hPS (h S hPS hS.1 hS.2.1)).symm
  rw [← hSP]
  exact hS

theorem card_of_isPSL_two {Y : Type} [Group Y] (h : IsPSL 2 2 2 Y) : Nat.card Y = 60 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four h

theorem isSimpleGroup_of_isPSL_two {X : Type} [Group X] (h : IsPSL 2 2 2 X) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 2 h).2

theorem eq_oTwoUpper_of_simple {Y : Type*} [Group Y] {A : Subgroup Y}
    (hs : IsSimpleGroup ↥A) {a : Y} (ha : a ∈ A) (ha1 : a ≠ 1) (hao : Odd (orderOf a)) :
    A = oTwoUpper A := by
  have hN : ((oTwoUpper A).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le A)).2 (le_normalizer_oTwoUpper A)
  have := hs
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((oTwoUpper A).subgroupOf A) with h | h
  · exfalso
    have hmem : (⟨a, ha⟩ : ↥A) ∈ (oTwoUpper A).subgroupOf A :=
      Subgroup.mem_subgroupOf.2 (mem_oTwoUpper_of_odd ha hao)
    rw [h, Subgroup.mem_bot] at hmem
    exact ha1 (congrArg Subtype.val hmem)
  · refine le_antisymm (fun x hx => ?_) (oTwoUpper_le A)
    have hmem : (⟨x, hx⟩ : ↥A) ∈ (oTwoUpper A).subgroupOf A := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem

theorem isPSL_oTwoUpper_quot {W P R : Subgroup G} (hPW : P ≤ W) (hRP : R ≤ P)
    (hWR : W ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R)
    (hpow : ∀ w ∈ W, ∃ n : ℕ, w ^ 2 ^ n ∈ P) [(R.subgroupOf P).Normal]
    (hPR : IsPSL 2 2 2 (↥P ⧸ R.subgroupOf P)) :
    IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥W ⧸ CFSG.pCore 2 ↥W))) ∧ P ⊓ pCoreOf 2 W ≤ R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 ↥W with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  set φ := QuotientGroup.mk' O with hφ
  set θ : ↥P →* ↥W ⧸ O := φ.comp (Subgroup.inclusion hPW) with hθ
  have hRW : R ≤ W := hRP.trans hPW
  have hRO : R.subgroupOf W ≤ O := by
    have hn : (R.subgroupOf W).Normal := ⟨fun n hn w => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 (hWR w.2) n).1 hn⟩
    have hp : IsPGroup 2 (R.subgroupOf W) := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRW).symm
    exact le_sSup ⟨hn, hp⟩
  have hs := isSimpleGroup_of_isPSL_two hPR
  have h60 := card_of_isPSL_two hPR
  have hker : θ.ker = R.subgroupOf P := by
    refine le_antisymm ?_ ?_
    · set ρ := QuotientGroup.mk' (R.subgroupOf P) with hρ
      have hkn : θ.ker.Normal := inferInstance
      have hk2 : IsPGroup 2 θ.ker := by
        intro x
        have hx : φ (Subgroup.inclusion hPW (x : ↥P)) = 1 := x.2
        rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
        obtain ⟨n, hn⟩ := hO2 ⟨_, hx⟩
        refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg (fun y : ↥O => ((y : ↥W) : G)) hn
        simpa using this
      have hmn : (θ.ker.map ρ).Normal := hkn.map ρ (QuotientGroup.mk'_surjective _)
      have := hs
      have := hmn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (θ.ker.map ρ) with h | h
      · intro x hx
        have : ρ x = 1 := by
          have hmem : ρ x ∈ θ.ker.map ρ := ⟨x, hx, rfl⟩
          rw [h, Subgroup.mem_bot] at hmem
          exact hmem
        rwa [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      · exfalso
        have h2 : IsPGroup 2 (θ.ker.map ρ) := hk2.map ρ
        rw [h] at h2
        have h2' : IsPGroup 2 (↥P ⧸ R.subgroupOf P) :=
          h2.of_equiv Subgroup.topEquiv
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2'
        rw [h60] at hn
        have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 60)
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        omega
    · intro x hx
      rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, hφ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hRO hx
  let e₁ : (↥P ⧸ R.subgroupOf P) ≃* ↥θ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange θ)
  have hsr : IsSimpleGroup ↥θ.range := MulEquiv.isSimpleGroup e₁.symm
  have hcr : Nat.card ↥θ.range = 60 := by rw [← Nat.card_congr e₁.toEquiv, h60]
  have h3 : 3 ∣ Nat.card ↥θ.range := hcr ▸ (by norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨a, ha⟩, ha3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  rw [Subgroup.orderOf_mk] at ha3
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha3
    norm_num at ha3
  have hro := eq_oTwoUpper_of_simple hsr ha ha1 (by rw [ha3]; decide)
  have htop : θ.range = oTwoUpper (⊤ : Subgroup (↥W ⧸ O)) := by
    refine eq_oTwoUpper_of_pow_mem le_top (fun x _ => ?_) hro
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := hpow (w : G) w.2
    refine ⟨n, ⟨⟨(w : G) ^ 2 ^ n, hn⟩, ?_⟩⟩
    rw [hθ, MonoidHom.comp_apply, hφ, QuotientGroup.mk'_apply]
    congr 1
  refine ⟨isPSL_of_mulEquiv hPR (e₁.trans (MulEquiv.subgroupCongr htop)), ?_⟩
  rintro x ⟨hxP, hxO⟩
  obtain ⟨w, hw, rfl⟩ := hxO
  have hwO : w ∈ O := by rw [hO]; exact hw
  have hk : (⟨(w : G), hxP⟩ : ↥P) ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, hφ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hwO
  rw [hker] at hk
  exact hk

@[expose] def fixSub {X : Type} [Group X] (α : MulAut X) : Subgroup X :=
  (α : X →* X).eqLocus (MonoidHom.id X)

theorem mem_fixSub {X : Type} [Group X] {α : MulAut X} {x : X} : x ∈ fixSub α ↔ α x = x :=
  Iff.rfl

@[expose] def L34ParData (X : Type) [Group X] (S₀ : Subgroup X) : Prop :=
  ∃ R₂ R₃ : Subgroup X, R₂ ≠ R₃ ∧
    (∀ R : Subgroup X, (R = R₂ ∨ R = R₃) →
      R ≤ S₀ ∧ Subgroup.normalizer (S₀ : Set X) ≤ Subgroup.normalizer (R : Set X) ∧
      IsElemAbelian 2 R ∧ Nat.card R = 16 ∧
      (∃ π : ↥(Subgroup.normalizer (R : Set X)) →*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
        Function.Surjective π ∧ π.ker = R.subgroupOf (Subgroup.normalizer (R : Set X))) ∧
      ∀ r ∈ R, ∀ s ∈ R, r ≠ 1 → s ≠ 1 →
        ∃ n ∈ Subgroup.normalizer (R : Set X), n * r * n⁻¹ = s) ∧
    ∀ E : Subgroup X, E ≤ S₀ → IsElemAbelian 2 E → E ≤ R₂ ∨ E ≤ R₃

@[expose] def L34OutData (X : Type) [Group X] (S₀ : Subgroup X) : Prop :=
  ∃ ψ : MulAut X →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2),
    (∀ x : X, ψ (MulAut.conj x) = 1) ∧
    (∀ α : MulAut X, α * α = 1 → ψ α = 1 → ∃ x : X, α = MulAut.conj x) ∧
    (∀ α : MulAut X, α * α = 1 → ψ α = (1, Multiplicative.ofAdd 1) → IsPSL 2 2 2 ↥(fixSub α)) ∧
    ∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ → (ψ α).1 = Multiplicative.ofAdd 1 →
      ∃ d ∈ Subgroup.normalizer (S₀ : Set X), α d * d⁻¹ ∉ S₀

end L34Br

end CFSG.Quasithin.H13
