module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Wreath
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22q
public import CFSG.LocalAnalysis.UniquenessCase.UC6K47d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

local notation "Z₃" => Multiplicative (ZMod 3)

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

omit [Finite G] in
theorem uc611_mem_map_conj_iff (H : Subgroup G) (c x : G) :
    x ∈ H.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

omit [Finite G] in
theorem uc611_map_conj_le {M : Subgroup G} {c : G} (hc : c ∈ M) :
    M.map (MulAut.conj c).toMonoidHom ≤ M := by
  rintro _ ⟨m, hm, rfl⟩
  exact M.mul_mem (M.mul_mem hc hm) (M.inv_mem hc)

omit [Finite G] in
theorem uc611_map_conj_eq_of_le_normalizer {M K : Subgroup G} (hMK : M ≤ normalizer (K : Set G))
    {c : G} (hc : c ∈ M) : K.map (MulAut.conj c).toMonoidHom = K :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMK hc)

omit [Finite G] in
theorem uc611_map_conj_centralizer (c : G) (Y : Subgroup G) :
    (centralizer (Y : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ((Y.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  rw [uc611_mem_map_conj_iff, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [SetLike.mem_coe, uc611_mem_map_conj_iff] at hy
    have := h _ hy
    calc y * x = c * (c⁻¹ * y * c * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = c * (c⁻¹ * x * c * (c⁻¹ * y * c)) * c⁻¹ := by rw [this]
      _ = x * y := by group
  · intro h y hy
    have := h (c * y * c⁻¹) ((uc611_mem_map_conj_iff Y c _).2 (by simpa [mul_assoc] using hy))
    calc y * (c⁻¹ * x * c) = c⁻¹ * (c * y * c⁻¹ * x) * c := by group
      _ = c⁻¹ * (x * (c * y * c⁻¹)) * c := by rw [this]
      _ = c⁻¹ * x * c * y := by group

theorem uc611_thompson_map_conj (P : Subgroup G) (c : G) :
    thompsonSubgroup (P.map (MulAut.conj c).toMonoidHom) =
      (thompsonSubgroup P).map (MulAut.conj c).toMonoidHom :=
  (CFSG.map_ambientMaxCardThompson_of_injective (MulAut.conj c).toMonoidHom P
    ((MulAut.conj c).injective.comp P.subtype_injective)).symm

theorem uc611_le_normalizer_primeCore (M : Subgroup G) :
    M ≤ normalizer ((rankThreePrimeCore 3 M : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le M)).1
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three M)

theorem uc611_gamma_map_conj_le {k p : ℕ} {M Q : Subgroup G} (hΓ : rankThreeGamma k p Q ≤ M)
    {c : G} (hc : c ∈ M) : rankThreeGamma k p (Q.map (MulAut.conj c).toMonoidHom) ≤ M := by
  unfold rankThreeGamma at hΓ ⊢
  rw [CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_conj]
  exact (Subgroup.map_mono hΓ).trans (uc611_map_conj_le hc)

theorem uc611_clauseC_conj {M Q : Subgroup G} (h : rankThreeClauseC M Q) {c : G} (hc : c ∈ M) :
    rankThreeClauseC M (Q.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨hsolv, ⟨e⟩, hΓ, hY⟩ := h
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hsurj : Function.Surjective (MulAut.conj c).toMonoidHom := (MulAut.conj c).surjective
  have hKf : (rankThreePrimeCore 3 M).map (MulAut.conj c).toMonoidHom = rankThreePrimeCore 3 M :=
    uc611_map_conj_eq_of_le_normalizer (uc611_le_normalizer_primeCore M) hc
  refine ⟨hsolv, ⟨(Subgroup.equivMapOfInjective Q _ hinj).symm.trans e⟩, ?_, ?_⟩
  · show rankThreeGamma 1 3 (thompsonSubgroup (Q.map (MulAut.conj c).toMonoidHom)) ≤ M
    rw [uc611_thompson_map_conj]
    exact uc611_gamma_map_conj_le hΓ hc
  · intro Y' hY'Q hY'3 hY'J
    have hYc : Y'.comap (MulAut.conj c).toMonoidHom ≤ Q := by
      intro y hy
      obtain ⟨q, hq, hqy⟩ := hY'Q hy
      exact (hinj hqy) ▸ hq
    have hY'eq : (Y'.comap (MulAut.conj c).toMonoidHom).map (MulAut.conj c).toMonoidHom = Y' :=
      Subgroup.map_comap_eq_self_of_surjective hsurj Y'
    have hYcard : Nat.card (Y'.comap (MulAut.conj c).toMonoidHom) = 3 := by
      rw [← hY'3, ← Subgroup.card_map_of_injective hinj, hY'eq]
    have hYJ : ¬ Y'.comap (MulAut.conj c).toMonoidHom ≤ thompsonSubgroup Q := fun hle =>
      hY'J (by
        show Y' ≤ thompsonSubgroup (Q.map (MulAut.conj c).toMonoidHom)
        rw [uc611_thompson_map_conj, ← hY'eq]
        exact Subgroup.map_mono hle)
    obtain ⟨R, hRK, hR2, hRidx, hQR, m, hm1, hRm⟩ := hY _ hYc hYcard hYJ
    refine ⟨R.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_, ?_, m, hm1, ?_⟩
    · rw [← hKf]
      exact Subgroup.map_mono hRK
    · exact hR2.of_equiv (Subgroup.equivMapOfInjective R _ hinj)
    · have h1 : (R.map (MulAut.conj c).toMonoidHom).relIndex (rankThreePrimeCore 3 M) =
          R.relIndex (rankThreePrimeCore 3 M) := by
        conv_lhs => rw [← hKf]
        exact Subgroup.relIndex_map_map_of_injective R _ hinj
      show ¬ 2 ∣ (R.map (MulAut.conj c).toMonoidHom).relIndex (rankThreePrimeCore 3 M)
      rw [h1]
      exact hRidx
    · rw [← Subgroup.map_normalizer_eq_of_bijective R ⟨hinj, hsurj⟩]
      exact Subgroup.map_mono hQR
    · have := CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsQ8CentralCyclic_map hRm (MulAut.conj c)
      rwa [Subgroup.map_inf_eq _ _ _ hinj, uc611_map_conj_centralizer, hY'eq] at this

theorem uc611_sylow_eq_map_conj {p : ℕ} [Fact p.Prime] {M Q P : Subgroup G}
    (hQ : IsSylowOf p Q M) (hP : IsSylowOf p P M) :
    ∃ c ∈ M, P = Q.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨c, hcM, hc⟩ := hQ.exists_mem_conj hP
  exact ⟨c, hcM, Subgroup.ext fun x => (hc x).trans (uc611_mem_map_conj_iff Q c x).symm⟩

theorem uc611_clauseC_of_sylow {M Q P : Subgroup G} (hQ : IsSylowOf 3 Q M) (hP : IsSylowOf 3 P M)
    (h : rankThreeClauseC M Q) : rankThreeClauseC M P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcM, rfl⟩ := uc611_sylow_eq_map_conj hQ hP
  exact uc611_clauseC_conj h hcM

local instance uc611_instDecEqWreath : DecidableEq W₃ := fun a b =>
  decidable_of_iff
    (RegularWreathProduct.equivProd Z₃ Z₃ a = RegularWreathProduct.equivProd Z₃ Z₃ b)
    ⟨fun h => (RegularWreathProduct.equivProd _ _).injective h, fun h => by rw [h]⟩

local instance uc611_instFintypeWreath : Fintype W₃ :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd Z₃ Z₃).symm

private theorem uc611_wreath_card_center :
    Fintype.card {c : W₃ // ∀ g : W₃, g * c = c * g} = 3 := by
  decide +kernel

private theorem uc611_wreath_center_char : ∀ c : W₃, (∀ g : W₃, g * c = c * g) ↔
    (c.right = 1 ∧ ∀ i j, c.left i = c.left j) := by
  decide +kernel

private theorem uc611_wreath_z2_char : ∀ w : W₃, (∀ y : W₃, (w * y * w⁻¹ * y⁻¹).right = 1 ∧
    ∀ i j, (w * y * w⁻¹ * y⁻¹).left i = (w * y * w⁻¹ * y⁻¹).left j) ↔
    (w.right = 1 ∧ ∏ i, w.left i = 1) := by
  decide +kernel

private theorem uc611_wreath_comm_surj : ∀ x : W₃, x.right ≠ 1 → ∀ w : W₃,
    (w.right = 1 ∧ ∏ i, w.left i = 1) → ∃ y : W₃, y.right = 1 ∧ x * y * x⁻¹ * y⁻¹ = w := by
  decide +kernel

private theorem uc611_wreath_ucs_two {w : W₃} (hw : w ∈ Subgroup.upperCentralSeries W₃ 2) :
    w.right = 1 ∧ ∏ i, w.left i = 1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff] at hw
  refine (uc611_wreath_z2_char w).1 fun y => ?_
  have hy := hw y
  rw [Subgroup.upperCentralSeries_one, commutatorElement_def, Subgroup.mem_center_iff] at hy
  exact (uc611_wreath_center_char _).1 hy

omit [Finite G] in
theorem uc611_emb_injective {P : Subgroup G} (e : ↥P ≃* W₃) :
    Function.Injective (P.subtype.comp e.symm.toMonoidHom) :=
  P.subtype_injective.comp e.symm.injective

omit [Finite G] in
theorem uc611_card_le_of_abelian {P : Subgroup G} (e : ↥P ≃* W₃) {B : Subgroup G}
    (hBP : B ≤ P) (hB : IsMulCommutative B) : Nat.card B ≤ 27 := by
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  have hιsurj : ∀ b ∈ P, ∃ w, ι w = b := fun b hb => ⟨e ⟨b, hb⟩, by simp [ι]⟩
  have hcomap : Nat.card (B.comap ι) = Nat.card B := by
    have hrange : B ≤ ι.range := fun b hb => hιsurj b (hBP hb)
    calc Nat.card (B.comap ι) = Nat.card ((B.comap ι).map ι) :=
          (Subgroup.card_map_of_injective hιinj).symm
      _ = Nat.card B := by rw [Subgroup.map_comap_eq_self hrange]
  have := Subgroup.comap_injective_isMulCommutative B hιinj
  rw [← hcomap]
  by_cases hle : B.comap ι ≤ (RegularWreathProduct.rightHom : W₃ →* Z₃).ker
  · rw [← CFSG.LocalAnalysis.RankThreeTheoremC.wreath_card_ker]
    exact Subgroup.card_le_of_le hle
  · have := CFSG.LocalAnalysis.RankThreeTheoremC.wreath_card_le_nine_of_not_le_ker
      (X := B.comap ι) inferInstance hle
    omega

theorem uc611_thompson_eq_map_ker {P : Subgroup G} (e : ↥P ≃* W₃) :
    thompsonSubgroup P = (RegularWreathProduct.rightHom : W₃ →* Z₃).ker.map
      (P.subtype.comp e.symm.toMonoidHom) := by
  refine le_antisymm (CFSG.LocalAnalysis.RankThreeTheoremC.thompsonSubgroup_le_map_ker e) ?_
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  have hA₀c : IsMulCommutative (RegularWreathProduct.rightHom : W₃ →* Z₃).ker :=
    CFSG.LocalAnalysis.RankThreeTheoremC.wreath_ker_isElemAbelian.1
  have hA₁P : (RegularWreathProduct.rightHom : W₃ →* Z₃).ker.map ι ≤ P := by
    rintro _ ⟨a, _, rfl⟩
    exact (e.symm a).2
  have hA₁c : IsMulCommutative ((RegularWreathProduct.rightHom : W₃ →* Z₃).ker.map ι) :=
    Subgroup.map_isMulCommutative _ ι
  have hA₁card : Nat.card ((RegularWreathProduct.rightHom : W₃ →* Z₃).ker.map ι) = 27 :=
    (Subgroup.card_map_of_injective hιinj).trans
      CFSG.LocalAnalysis.RankThreeTheoremC.wreath_card_ker
  exact CFSG.le_ambientMaxCardThompson ⟨hA₁P, hA₁c, fun B hBP hB =>
    (uc611_card_le_of_abelian e hBP hB).trans hA₁card.ge⟩

theorem uc611_thompson_exp3 {P : Subgroup G} (e : ↥P ≃* W₃) :
    ∀ a ∈ thompsonSubgroup P, a ^ 3 = 1 := by
  rw [uc611_thompson_eq_map_ker e]
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, CFSG.LocalAnalysis.RankThreeTheoremC.wreath_ker_isElemAbelian.2 a ha, map_one]

theorem uc611_thompson_isMulCommutative {P : Subgroup G} (e : ↥P ≃* W₃) :
    IsMulCommutative (thompsonSubgroup P) := by
  have hA₀c : IsMulCommutative (RegularWreathProduct.rightHom : W₃ →* Z₃).ker :=
    CFSG.LocalAnalysis.RankThreeTheoremC.wreath_ker_isElemAbelian.1
  rw [uc611_thompson_eq_map_ker e]
  exact Subgroup.map_isMulCommutative _ _

theorem uc611_card_thompson {P : Subgroup G} (e : ↥P ≃* W₃) :
    Nat.card (thompsonSubgroup P) = 27 := by
  rw [uc611_thompson_eq_map_ker e, Subgroup.card_map_of_injective (uc611_emb_injective e),
    CFSG.LocalAnalysis.RankThreeTheoremC.wreath_card_ker]

theorem uc611_eq_thompson_of_abelian_card {P : Subgroup G} (e : ↥P ≃* W₃) {B : Subgroup G}
    (hBP : B ≤ P) (hB : IsMulCommutative B) (hcard : Nat.card B = 27) :
    B = thompsonSubgroup P := by
  have hle : B ≤ thompsonSubgroup P := CFSG.le_ambientMaxCardThompson
    ⟨hBP, hB, fun B' hB'P hB'c => (uc611_card_le_of_abelian e hB'P hB'c).trans hcard.ge⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [uc611_card_thompson e, hcard])

theorem uc611_weaklyClosed {P : Subgroup G} (e : ↥P ≃* W₃) :
    ∀ g : G, (∀ x ∈ thompsonSubgroup P, g⁻¹ * x * g ∈ P) →
      ∀ x ∈ thompsonSubgroup P, g⁻¹ * x * g ∈ thompsonSubgroup P := by
  intro g hg x hx
  have hcomm := uc611_thompson_isMulCommutative e
  have hfinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hBP : (thompsonSubgroup P).map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hg y hy
  have hBeq : (thompsonSubgroup P).map (MulAut.conj g⁻¹).toMonoidHom = thompsonSubgroup P :=
    uc611_eq_thompson_of_abelian_card e hBP (Subgroup.map_isMulCommutative _ _)
      (by rw [Subgroup.card_map_of_injective hfinj, uc611_card_thompson e])
  have hmem : g⁻¹ * x * g ∈ (thompsonSubgroup P).map (MulAut.conj g⁻¹).toMonoidHom :=
    ⟨x, hx, by simp⟩
  rwa [hBeq] at hmem

theorem uc611_card_center {P : Subgroup G} (e : ↥P ≃* W₃) : Nat.card (Subgroup.center ↥P) = 3 := by
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
    Nat.card_congr (Equiv.subtypeEquivRight fun c => Subgroup.mem_center_iff),
    Nat.card_eq_fintype_card]
  exact uc611_wreath_card_center

theorem uc611_ucs_two_le_thompson {P : Subgroup G} (e : ↥P ≃* W₃) :
    (Subgroup.upperCentralSeries ↥P 2).map P.subtype ≤ thompsonSubgroup P := by
  rintro _ ⟨a, ha, rfl⟩
  have hea : e a ∈ Subgroup.upperCentralSeries W₃ 2 := by
    rw [← Subgroup.comap_upperCentralSeries e 2] at ha
    exact ha
  rw [uc611_thompson_eq_map_ker e]
  exact ⟨e a, (uc611_wreath_ucs_two hea).1, by simp⟩

theorem uc611_exists_comm_eq {P : Subgroup G} (e : ↥P ≃* W₃) {x : G} (hxP : x ∈ P)
    (hxJ : x ∉ thompsonSubgroup P) {w : G}
    (hw : w ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype) :
    ∃ y ∈ thompsonSubgroup P, x * y * x⁻¹ * y⁻¹ = w := by
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  have hew₀ : e w₀ ∈ Subgroup.upperCentralSeries W₃ 2 := by
    rw [← Subgroup.comap_upperCentralSeries e 2] at hw₀
    exact hw₀
  have hx₀ : (e ⟨x, hxP⟩).right ≠ 1 := fun h => hxJ (by
    rw [uc611_thompson_eq_map_ker e]
    exact ⟨e ⟨x, hxP⟩, h, by simp⟩)
  obtain ⟨y₀, hy₀, hcomm⟩ := uc611_wreath_comm_surj _ hx₀ (e w₀) (uc611_wreath_ucs_two hew₀)
  refine ⟨P.subtype (e.symm y₀), ?_, ?_⟩
  · rw [uc611_thompson_eq_map_ker e]
    exact ⟨y₀, hy₀, rfl⟩
  · have h := congrArg (fun z : W₃ => P.subtype (e.symm z)) hcomm
    simpa using h

theorem uc611_exists_gen_of_card_three {P : Subgroup G} {X : Subgroup G}
    (hXP : X ≤ P) (hX3 : Nat.card X = 3) (hXA : ¬ X ≤ thompsonSubgroup P) :
    ∃ x ∈ X, X = zpowers x ∧ x ^ 3 = 1 ∧ x ∉ thompsonSubgroup P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxX, hxJ⟩ := IsConcreteLE.not_le_iff_exists.mp hXA
  have _hxP : x ∈ P := hXP hxX
  have hx1 : x ≠ 1 := fun h => hxJ (h ▸ (thompsonSubgroup P).one_mem)
  have hx3 : x ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := X) (x := ⟨x, hxX⟩)
    rw [hX3] at h
    simpa using congrArg Subtype.val h
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hEq : zpowers x = X := Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxX)
    (by rw [Nat.card_zpowers, hord, hX3])
  exact ⟨x, hxX, hEq.symm, hx3, hxJ⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6
