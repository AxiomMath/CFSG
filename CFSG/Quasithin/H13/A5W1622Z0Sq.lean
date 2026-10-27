module

public import CFSG.Quasithin.H13.A5W1622F4P2
public import CFSG.Quasithin.H13.A5W1622v
public import CFSG.Quasithin.H13.A5W1622s
public import CFSG.Quasithin.H13.A5W1622Sq
public import CFSG.Quasithin.MS93.MResSqIncl
public import CFSG.Quasithin.H13.A5W1622o

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise commutatorElement

theorem c134Case4F_at {G : Type} [Group G] [Finite G] {G₀ R L : Subgroup G}
    (h4 : C134CorrLocal.IsC134Case4Corr G₀ R L)
    (hI : ∀ y ∈ c134Q G₀ L, (∀ x ∈ c134Q G₀ L, y * x * y⁻¹ * x⁻¹ ∈ c134CQ G₀ L) →
      y ∈ frattiniIn (c134Q G₀ L))
    {c : G} (hc : c ∈ c134CQ G₀ L) {y : G} (hy : y ∈ c134Q G₀ L)
    (hyc : ∀ x ∈ c134Q G₀ L, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.zpowers c) :
    y ∈ centerOf (c134Q G₀ L) := by
  have hyΦ := hI y hy fun x hx => (Subgroup.zpowers_le.mpr hc) (hyc x hx)
  obtain ⟨⟨n, F, _, _, α, hF, hα, hCE, hZ, -, -, hΦ, -, hQ⟩, -⟩ := h4
  set Q := c134Q G₀ L with hQdef
  set Φ := frattiniIn Q with hΦdef
  have hn : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    omega
  have h2 : (2 : F) = 0 := by
    have h1 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
    rw [hF, Nat.cast_pow, Nat.cast_ofNat] at h1
    exact pow_eq_zero_iff hn |>.mp h1
  have hcZ : c ∈ centerOf Q := hZ ▸ Subgroup.mem_sup_left hc
  have hcc : c * c = 1 := by
    obtain ⟨e⟩ := hCE
    have h1 : e (⟨c, hc⟩ * ⟨c, hc⟩) = e 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      funext i
      show Multiplicative.toAdd (e ⟨c, hc⟩) i + Multiplicative.toAdd (e ⟨c, hc⟩) i = 0
      generalize Multiplicative.toAdd (e ⟨c, hc⟩) i = a
      revert a
      decide
    exact congrArg Subtype.val (e.injective h1)
  have hcQ : ∀ x ∈ Q, x * c = c * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hcZ.2 x hx
  have hcL : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_iff.mp hc.2 l hl
  have hZc : ∀ z ∈ centerOf Q, ∀ x ∈ Q, z * x = x * z := fun z hz x hx =>
    (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm
  have hΦQ : Φ ≤ Q := Subgroup.map_subtype_le _
  have hcen : ∀ g ∈ Subgroup.zpowers c, ∀ x ∈ Q, g * x = x * g := by
    intro g hg x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (hcQ x hx).symm m)).eq
  let X : Subgroup G :=
    { carrier := {φ | φ ∈ Φ ∧ ∀ x ∈ Q, φ * x * φ⁻¹ * x⁻¹ ∈ Subgroup.zpowers c}
      one_mem' := ⟨Φ.one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro φ φ' ⟨hφ, h1⟩ ⟨hφ', h1'⟩
        refine ⟨Φ.mul_mem hφ hφ', fun x hx => ?_⟩
        have e : φ * φ' * x * (φ * φ')⁻¹ * x⁻¹ =
            (φ * (φ' * x * φ'⁻¹ * x⁻¹)) * φ⁻¹ * (φ * x * φ⁻¹ * x⁻¹) := by group
        rw [e, ← hcen _ (h1' x hx) φ (hΦQ hφ), mul_inv_cancel_right]
        exact Subgroup.mul_mem _ (h1' x hx) (h1 x hx)
      inv_mem' := by
        rintro φ ⟨hφ, h1⟩
        refine ⟨Φ.inv_mem hφ, fun x hx => ?_⟩
        have hk := hcen _ (h1 x hx) φ⁻¹ (Q.inv_mem (hΦQ hφ))
        have e : φ⁻¹ * x * φ⁻¹⁻¹ * x⁻¹ =
            φ⁻¹ * (φ * x * φ⁻¹ * x⁻¹)⁻¹ * φ := by group
        rw [e, ← hcen _ (Subgroup.inv_mem _ (h1 x hx)) φ⁻¹ (Q.inv_mem (hΦQ hφ)),
          inv_mul_cancel_right]
        exact Subgroup.inv_mem _ (h1 x hx) }
  have hyX : y ∈ X := ⟨hyΦ, hyc⟩
  have hZX : centerOf Q ≤ X := by
    intro z hz
    refine ⟨hΦ.2.1 hz, fun x hx => ?_⟩
    rw [hZc z hz x hx, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hXΦ : X ≤ Φ := fun _ hφ => hφ.1
  have hconj : ∀ l ∈ L, ∀ φ ∈ X, l * φ * l⁻¹ ∈ X := by
    rintro l hl φ ⟨hφ, h1⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hΦ.1 hl) φ).mp hφ, fun x hx => ?_⟩
    have hx' : l⁻¹ * x * l ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hQ.1 (L.inv_mem hl)) x).mp hx
      simpa using this
    have hk := h1 _ hx'
    have e : l * φ * l⁻¹ * x * (l * φ * l⁻¹)⁻¹ * x⁻¹ =
        l * (φ * (l⁻¹ * x * l) * φ⁻¹ * (l⁻¹ * x * l)⁻¹) * l⁻¹ := by group
    rw [e]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [← hm, ((Commute.zpow_right (hcL l hl) m)).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c m
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := fun l hl =>
    Subgroup.mem_normalizer_iff.mpr fun φ =>
      ⟨hconj l hl φ, fun hφ => by
        have := hconj l⁻¹ (L.inv_mem hl) _ hφ
        simpa [mul_assoc] using this⟩
  by_contra hyZ
  have hXeq : X = Φ := F4P.eq_of_not_le hα.1 hΦ hZX hXΦ hLX fun h => hyZ (h hyX)
  refine F4P.false_of_comm_mem h2 hΦ hQ hΦQ hZc (fun x hx hxφ => ⟨hx, ?_⟩) hcc hcQ
    fun φ hφ x hx => (hXeq ▸ hφ : φ ∈ X).2 x hx
  exact Subgroup.mem_centralizer_iff.mpr fun φ hφ => hxφ φ hφ

theorem lem13622Case4Z0_of_sq (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h45 : MS93.MRes.C134Case4Lemma45CorrSq) : Lem13622Case4Z0 := by
  intro G _ _ T L V S hH K₀ hK₀G hK₀ hTK₀ hz _ ⟨F, _, _, α, hF2, hα⟩ hi4 hvCQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  have hchar : CharTwo (K₀ ⊔ S.Tv) :=
    C1GN.charTwo_of_le hH.hF (S.isSylowTwoOf_Tv h1222 h517) le_sup_right (sup_le hK₀G S.Tv_le_Gv)
  have hcard2 : Fintype.card F = Fintype.card (ZMod 2) := by rw [hF2, ZMod.card]
  let ε : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard2
  let eK : (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα.1)
  have hl : IsPSL 3 2 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := Vol2Native.A312L.Seven.isPSL_three_two
    (eK.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.trans
      (slMulEquivOfRingEquiv ε 3)))
  have hlist : IsPSL 3 2 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ∨ IsAlt 6 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ∨
      IsPSU 3 3 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := Or.inl hl
  have hRk := SBc11.isRankTwoLie2Derived_of_list
    (isList_of_mulEquiv (quotCenterEquivOfEqBot (SBc11.center_eq_bot_of_list hlist)).symm hlist)
  have hMS := S.isMSPair_of h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 hK₀G hK₀ hTK₀ hz
    hchar hRk
  have hset : ((K₀ ⊔ S.Tv : Subgroup G) : Set G) = (K₀ : Set G) * (S.Tv : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K₀ S.Tv hTK₀
  have hI := h45 G (K₀ ⊔ S.Tv) S.Tv K₀ hMS hK₀ hset ⟨F, inferInstance, inferInstance, α, hF2, hα⟩
    (S.c134SqCond_Tv h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 hK₀G hK₀ hTK₀ hz) hi4
  have hZQ : ∀ y ∈ c134Q (K₀ ⊔ S.Tv) K₀,
      (∀ x ∈ c134Q (K₀ ⊔ S.Tv) K₀, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.zpowers S.v12) →
        y ∈ centerOf (c134Q (K₀ ⊔ S.Tv) K₀) := fun y hy hyc => c134Case4F_at hi4 hI hvCQ hy hyc
  set O := pCoreOf 2 K₀ with hOdef
  set Q := c134Q (K₀ ⊔ S.Tv) K₀ with hQdef
  set Z₀ := z0Of S.v12 K₀ with hZ₀def
  obtain ⟨hQO, -, hKQ, -⟩ := S.c134Q_facts h1222 h517 hK₀G hTK₀
  have hOK : O ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hKO : K₀ ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  have hnorm : (K₀.subgroupOf (K₀ ⊔ S.Tv)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hTK₀)
  have hOG : O ≤ pCoreOf 2 (K₀ ⊔ S.Tv) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K₀ (K₀ ⊔ S.Tv)
      le_sup_left hnorm
  have hvc : ∀ g ∈ K₀, g * S.v12 = S.v12 * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp (hK₀G hg)
  have hvz : ∀ g ∈ K₀, ∀ c ∈ Subgroup.zpowers S.v12, g * c = c * g := by
    intro g hg c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((Commute.zpow_right (hvc g hg) i)).eq
  have hZ₀prop : ∀ x ∈ Z₀, x ∈ O ∧ ∀ r ∈ O, x * r * x⁻¹ * r⁻¹ ∈ Subgroup.zpowers S.v12 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨O.one_mem, fun r _ => by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨O.mul_mem hx.1 hy.1, fun r hr => ?_⟩
      have h1 := hy.2 r hr
      have h2 := hx.2 r hr
      have e : x * y * r * (x * y)⁻¹ * r⁻¹ =
          x * (y * r * y⁻¹ * r⁻¹) * x⁻¹ * (x * r * x⁻¹ * r⁻¹) := by group
      rw [e, hvz x (hOK hx.1) _ h1, mul_inv_cancel_right]
      exact Subgroup.mul_mem _ h1 h2
    | inv x _ hx =>
      refine ⟨O.inv_mem hx.1, fun r hr => ?_⟩
      have h1 := hx.2 r hr
      have e : x⁻¹ * r * x⁻¹⁻¹ * r⁻¹ = x⁻¹ * (x * r * x⁻¹ * r⁻¹)⁻¹ * x := by group
      rw [e, hvz x⁻¹ (K₀.inv_mem (hOK hx.1)) _ (Subgroup.inv_mem _ h1), inv_mul_cancel_right]
      exact Subgroup.inv_mem _ h1
  have hZ₀conj : ∀ x ∈ Z₀, ∀ k ∈ K₀, k * x * k⁻¹ ∈ Z₀ := by
    intro x hx k hk
    obtain ⟨hxO, hxr⟩ := hZ₀prop x hx
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp (hKO hk) x).mp hxO, ?_⟩
    intro r hr
    have hr' : k⁻¹ * r * k ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hKO (K₀.inv_mem hk)) r).mp hr
      simpa using this
    have h1 := hxr _ hr'
    have e : k * x * k⁻¹ * r * (k * x * k⁻¹)⁻¹ * r⁻¹ =
        k * (x * (k⁻¹ * r * k) * x⁻¹ * (k⁻¹ * r * k)⁻¹) * k⁻¹ := by group
    rw [e, hvz k hk _ h1, mul_inv_cancel_right]
    exact h1
  have hcZQ : ∀ x ∈ Z₀, ∀ k ∈ K₀, k⁻¹ * x * k * x⁻¹ ∈ centerOf Q := by
    intro x hx k hk
    have hxQ : k⁻¹ * x * k * x⁻¹ ∈ Q := by
      have h1 : ⁅x, k⁻¹⁆ ∈ Q :=
        Subgroup.commutator_mem_commutator (hOG (hZ₀prop x hx).1) (K₀.inv_mem hk)
      have h2 : k⁻¹ * x * k * x⁻¹ = (⁅x, k⁻¹⁆)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact Q.inv_mem h1
    have hxZ : k⁻¹ * x * k * x⁻¹ ∈ Z₀ := by
      have := hZ₀conj x hx k⁻¹ (K₀.inv_mem hk)
      rw [inv_inv] at this
      exact Z₀.mul_mem this (Z₀.inv_mem hx)
    exact hZQ _ hxQ fun q hq => (hZ₀prop _ hxZ).2 q (hQO hq)
  obtain ⟨⟨n, F₄, _, _, α₄, -, hα₄, -, -, -, hU, -, -, -⟩, -⟩ := hi4
  obtain ⟨-, -, β, -, hβk, hβe⟩ := hU
  have hZQK : centerOf Q ≤ K₀ := inf_le_left.trans (hQO.trans hOK)
  have hKZQ : K₀ ≤ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) :=
    Setting.le_normalizer_centerOf hKQ
  have hUQ : ⁅centerOf Q, K₀⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro q hq k hk
    have hqQ : q ∈ Q := hq.1
    have h1 : k * q⁻¹ * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKQ hk) _).mp (Q.inv_mem hqQ)
    rw [commutatorElement_def, show q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) by group]
    exact Q.mul_mem hqQ h1
  have hUO : ⁅centerOf Q, K₀⁆ ≤ centerOf O := by
    intro u hu
    refine ⟨hQO (hUQ hu), Subgroup.mem_centralizer_iff.mpr fun o ho => ?_⟩
    have hoK := hOK ho
    have hoker : (⟨o, hoK⟩ : ↥K₀) ∈ α₄.ker := by
      rw [hα₄.2]
      rw [hOdef, pCoreOf] at ho
      obtain ⟨o', ho', ho'eq⟩ := ho
      have e : (⟨o, hoK⟩ : ↥K₀) = o' := Subtype.ext ho'eq.symm
      rw [e]
      exact ho'
    have hu' : o * u * o⁻¹ ∈ ⁅centerOf Q, K₀⁆ :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_commutator hKZQ Subgroup.le_normalizer hoK) u).mp hu
    have h1 := hβe ⟨o, hoK⟩ ⟨u, hu⟩ ⟨o * u * o⁻¹, hu'⟩ rfl
    have h2 : β ⟨o * u * o⁻¹, hu'⟩ = β ⟨u, hu⟩ := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [h1 i, MonoidHom.mem_ker.mp hoker]
      simp [moduleAct]
    have h4 : (⟨o * u * o⁻¹, hu'⟩ : ↥⁅centerOf Q, K₀⁆) * ⟨u, hu⟩⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h4
    have h5 : o * u * o⁻¹ = u := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
      exact mul_inv_eq_one.mp h4
    calc o * u = o * u * o⁻¹ * o := by group
      _ = u * o := by rw [h5]
  have hZOK : centerOf O ≤ K₀ := inf_le_left.trans hOK
  have hKZO : K₀ ≤ Subgroup.normalizer ((centerOf O : Subgroup G) : Set G) :=
    Setting.le_normalizer_centerOf hKO
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx k hk
    have hxN : x ∈ Subgroup.normalizer (K₀ : Set G) :=
      Subgroup.le_normalizer (hOK (hZ₀prop x hx).1)
    have hU1 := comm_mem_commutator_of_perfect hZQK hKZQ hK₀p hxN (hcZQ x hx)
    have hU2 := comm_mem_commutator_of_perfect hZOK hKZO hK₀p hxN fun k hk => hUO (hU1 k hk)
    have h1 := hU2 k⁻¹ (K₀.inv_mem hk)
    rw [inv_inv] at h1
    have h2 : ⁅x, k⁆ = (k * x * k⁻¹ * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact Subgroup.inv_mem _ h1
  · refine Subgroup.commutator_mono (fun c hc => Subgroup.subset_closure ⟨hc.1, fun r hr => ?_⟩)
      le_rfl
    rw [← Subgroup.mem_centralizer_iff.mp hc.2 r hr, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _

end CFSG.Quasithin.H13.A5
