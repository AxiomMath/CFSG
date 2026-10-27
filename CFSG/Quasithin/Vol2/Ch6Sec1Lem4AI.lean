module

public import CFSG.Quasithin.Vol2.Ch6OrthC27
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs
public import CFSG.Quasithin.Background.C1PackC129Case
public import CFSG.Quasithin.EmptyFaithful.T1515Der5Fit
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem3
public import CFSG.Quasithin.Background.E3Offender
public import CFSG.Quasithin.Background.HDefs

public section

namespace CFSG.Quasithin.H13

section CaseAi

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem relIndex_sup_eq_inf_ch6 {H K : Subgroup G} (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K := by
  have hKrel : K.relIndex (H ⊔ K) = K.relIndex H := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hK
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hK
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hK).toEquiv.symm
  have hmul : (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
      (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
    calc (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) :=
          Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
      _ = (H ⊓ K).relIndex K * K.relIndex (H ⊔ K) :=
          (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right).symm
      _ = (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
          rw [hKrel, Subgroup.inf_relIndex_left]
  have hpos : 0 < (H ⊓ K).relIndex H :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (H ⊓ K).subgroupOf H))
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [hmul, mul_comm])

theorem exists_isHStar_le_ch6 {M X : Subgroup G} (hX : InH T X) (hXM : ¬ X ≤ M) :
    ∃ H : Subgroup G, IsHStar T M H ∧ H ≤ X := by
  obtain ⟨H, ⟨hHH, hHM, hHX⟩, hmin⟩ :=
    (Set.toFinite {Y : Subgroup G | InH T Y ∧ ¬ Y ≤ M ∧ Y ≤ X}).exists_minimal
      ⟨X, hX, hXM, le_rfl⟩
  exact ⟨H, ⟨hHH, hHM, fun Y hY hYH hYM =>
    le_antisymm hYH (hmin ⟨hY, hYM, hYH.trans hHX⟩ hYH)⟩, hHX⟩

theorem mem_normalizer_of_prop121_ch6 (hP : CFSG.QuasithinUnique.Id2519.Prop121Three)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hq : CFSG.QuasithinUnique.QTKECore G) {H K : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥)
    (hK : K ∈ cComp H) {x : G} (hxH : x ∈ H) (hx5 : x ^ 5 = 1) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  rcases hP G hs hnab hq H hH K hK with hN | ⟨h2, -⟩
  · exact hN hxH
  set O := {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate K h} with hO
  have hmem : ∀ (A : Subgroup G) (a y : G), y ∈ CFSG.conjugate A a ↔ a * y * a⁻¹ ∈ A := by
    intro A a y
    unfold CFSG.conjugate
    rw [Subgroup.mem_map_equiv]
    simp
  have hconj : ∀ (a b : G) (A : Subgroup G),
      CFSG.conjugate (CFSG.conjugate A a) b = CFSG.conjugate A (a * b) := by
    intro a b A
    ext y
    rw [hmem, hmem, hmem]
    constructor <;> intro hy <;> convert hy using 1 <;> group
  have hK1 : CFSG.conjugate K 1 = K := by
    ext y
    rw [hmem]
    simp
  have hinj : ∀ (a : G) (A B : Subgroup G),
      CFSG.conjugate A a = CFSG.conjugate B a → A = B := by
    intro a A B hAB
    ext y
    have h1 := hmem A a (a⁻¹ * y * a)
    have h2 := hmem B a (a⁻¹ * y * a)
    rw [hAB] at h1
    have e : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
    rw [e] at h1 h2
    exact h1.symm.trans h2
  have hmemN : ∀ y : G, CFSG.conjugate K y = K → y ∈ Subgroup.normalizer (K : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have := hmem K y z
    rw [hy] at this
    exact this
  by_contra hxN
  have hx1 : CFSG.conjugate K x ≠ K := fun h => hxN (hmemN x h)
  obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.mp h2
  have hall : ∀ c : O, c = a ∨ c = b := by
    intro c
    have : c ∈ ({a, b} : Set O) := huniv ▸ Set.mem_univ c
    simpa using this
  set e0 : O := ⟨K, 1, H.one_mem, hK1.symm⟩
  set e1 : O := ⟨CFSG.conjugate K x, x, hxH, rfl⟩
  set e2 : O := ⟨CFSG.conjugate K (x * x), x * x, H.mul_mem hxH hxH, rfl⟩
  have h01 : e0 ≠ e1 := fun h => hx1 (congrArg Subtype.val h).symm
  have h2' : ∀ c : O, c = e0 ∨ c = e1 := by
    intro c
    rcases hall e0 with h0a | h0b <;> rcases hall e1 with h1a | h1b
    · exact absurd (h0a.trans h1a.symm) h01
    · rcases hall c with hc | hc
      · exact Or.inl (hc.trans h0a.symm)
      · exact Or.inr (hc.trans h1b.symm)
    · rcases hall c with hc | hc
      · exact Or.inr (hc.trans h1a.symm)
      · exact Or.inl (hc.trans h0b.symm)
    · exact absurd (h0b.trans h1b.symm) h01
  have hx2 : CFSG.conjugate K (x * x) = K := by
    rcases h2' e2 with h | h
    · exact congrArg Subtype.val h
    · exfalso
      have h3 : CFSG.conjugate K (x * x) = CFSG.conjugate K x := congrArg Subtype.val h
      rw [← hconj x x K] at h3
      have h4 : CFSG.conjugate (CFSG.conjugate K x) x = CFSG.conjugate K x := h3
      have h5 : CFSG.conjugate K x = K := by
        apply hinj x
        rw [h4]
      exact hx1 h5
  apply hxN
  have hxx : x * x ∈ Subgroup.normalizer (K : Set G) := hmemN _ hx2
  have : x = (x * x) ^ 3 := by
    rw [← pow_two, ← pow_mul]
    calc x = x ^ 5 * x := by rw [hx5, one_mul]
      _ = x ^ (2 * 3) := by rw [← pow_succ]
  rw [this]
  exact Subgroup.pow_mem _ hxx 3

omit [Finite G] in
theorem oTwoUpper_le_of_normal_sup_ch6 {H N S : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hS : IsPGroup 2 S) (hSH : S ≤ H) (hH : H ≤ N ⊔ S) :
    oTwoUpper H ≤ N := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hsup : N.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNH hSH]
    exact Subgroup.subgroupOf_eq_top.mpr hH
  have hx' : (⟨x, hx⟩ : ↥H) ∈ N.subgroupOf H ⊔ S.subgroupOf H := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, s, hs, hns⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  obtain ⟨k, hk⟩ := hS' ⟨s, hs⟩
  refine ⟨k, ?_⟩
  have hs1 : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) = QuotientGroup.mk s := by
    rw [← hns, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have h2 : (QuotientGroup.mk ((⟨x, hx⟩ : ↥H) ^ 2 ^ k) : ↥H ⧸ N.subgroupOf H) = 1 := by
    rw [QuotientGroup.mk_pow, h1, ← QuotientGroup.mk_pow, hs1, QuotientGroup.mk_one]
  rw [QuotientGroup.eq_one_iff] at h2
  simpa using Subgroup.mem_subgroupOf.mp h2

theorem le_normalizer_conjClosure_ch6 {X K T : Subgroup G}
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    X ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  intro x hx
  have key : ∀ y ∈ X, ∀ z ∈ conjClosure K T, y * z * y⁻¹ ∈ conjClosure K T := by
    intro y hy z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, k, hk, rfl⟩ := hz
      have hty : t⁻¹ * y * t ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (hTX (T.inv_mem ht)) y).mp hy
        simpa [mul_assoc] using this
      have hk' : (t⁻¹ * y * t) * k * (t⁻¹ * y * t)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hXK hty) k).mp hk
      have e : y * (t * k * t⁻¹) * y⁻¹ =
          t * ((t⁻¹ * y * t) * k * (t⁻¹ * y * t)⁻¹) * t⁻¹ := by group
      rw [e]
      exact mem_conjClosure ht hk'
    | one => simp
    | mul a b _ _ iha ihb =>
      have := (conjClosure K T).mul_mem iha ihb
      simpa [mul_assoc] using this
    | inv a _ iha =>
      have := (conjClosure K T).inv_mem iha
      simpa [mul_assoc] using this
  exact mem_normalizer_of_conj_mem (key x hx)

theorem le_of_not_le_normalizer_inf_ch6 {X K₀ : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (K₀ : Set G)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT2 : IsPGroup 2 T) (hX5 : (X ⊓ T).relIndex X = 5) (hX2 : X = oTwoUpper X)
    (hnot : ¬ X ≤ Subgroup.normalizer ((T ⊓ K₀ : Subgroup G) : Set G)) : X ≤ K₀ := by
  have h1 : ¬ X ⊓ K₀ ≤ T := by
    intro hle
    apply hnot
    intro x hx
    refine mem_normalizer_of_conj_mem fun p hp => ?_
    have hxp : x * p * x⁻¹ ∈ K₀ :=
      (Subgroup.mem_normalizer_iff.mp (hXN hx) p).mp hp.2
    have hpx : p * x⁻¹ * p⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hTX hp.1) x⁻¹).mp (X.inv_mem hx)
    have hc : x * p * x⁻¹ * p⁻¹ ∈ X ⊓ K₀ := by
      refine ⟨?_, K₀.mul_mem hxp (K₀.inv_mem hp.2)⟩
      have := X.mul_mem hx hpx
      simpa [mul_assoc] using this
    have hcT := hle hc
    refine ⟨?_, hxp⟩
    have := T.mul_mem hcT hp.1
    simpa [mul_assoc] using this
  obtain ⟨y, ⟨hyX, hyK⟩, hyT⟩ := Set.not_subset.mp h1
  have hXK : X ⊓ K₀ ≤ X := inf_le_left
  have hXKn : ((X ⊓ K₀).subgroupOf X).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr fun x hx => ?_
    exact mem_normalizer_inf_ch6 (Subgroup.le_normalizer hx) (hXN hx)
  have hsup : X ≤ (X ⊓ K₀) ⊔ (X ⊓ T) := by
    set R := (X ⊓ K₀) ⊔ (X ⊓ T) with hR
    have hPR : X ⊓ T ≤ R := le_sup_right
    have hRX : R ≤ X := sup_le inf_le_left inf_le_left
    have hmul := Subgroup.relIndex_mul_relIndex (X ⊓ T) R X hPR hRX
    rw [hX5] at hmul
    have hdvd : (X ⊓ T).relIndex R ∣ 5 := Dvd.intro _ hmul
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exfalso
      have hRP : R ≤ X ⊓ T := Subgroup.relIndex_eq_one.mp h1
      exact hyT (hRP ((le_sup_left : X ⊓ K₀ ≤ R) ⟨hyX, hyK⟩)).2
    · rw [h5] at hmul
      have : R.relIndex X = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp this
  have hP2 : IsPGroup 2 (X ⊓ T : Subgroup G) := hT2.to_le inf_le_right
  have hO := oTwoUpper_le_of_normal_sup_ch6 hXK hXKn hP2 inf_le_left hsup
  rw [← hX2] at hO
  exact hO.trans inf_le_right

namespace Hyp611

theorem le_centralizer_of_isHStar_ch6 (h5172 : Stmt5_1_7_two) (h : Hyp611 G T M L V 4)
    (hJN : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G)) {H : Subgroup G}
    (hH : IsHStar T M H) :
    H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  by_contra hZH
  obtain ⟨hLJ, -⟩ := h5172 G T M L V H 4 h.toHyp5_0_1 h.module hH hZH
  have hcJ : ⁅L, thompsonJ T⁆ ≤ thompsonJ T := by
    rw [Subgroup.commutator_le]
    intro l hl j hj
    rw [commutatorElement_def]
    exact (thompsonJ T).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hJN (Subgroup.mem_sup_left hl)) j).mp hj)
      ((thompsonJ T).inv_mem hj)
  have hLT : L ≤ T := hLJ ▸ hcJ.trans (thompsonJ_le_self T)
  have hL2 : IsPGroup 2 ↥L := h.sylow.1.to_le hLT
  have htop : CFSG.pCore 2 ↥L = ⊤ := by
    rw [eq_top_iff]
    exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance
      (hL2.of_equiv (Subgroup.topEquiv (G := ↥L)).symm)
  have hcard := h.card_quot_four_ch6
  rw [htop] at hcard
  rw [← Subgroup.index, Subgroup.index_top] at hcard
  exact absurd hcard (by norm_num)

theorem pCoreOf_xFive_props_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4) :
    ch6Q T V ≤ pCoreOf 2 (xFiveCh6 T L ⊔ T) ∧ pCoreOf 2 (xFiveCh6 T L ⊔ T) ≤ T ∧
      pCoreOf 2 (xFiveCh6 T L ⊔ T) ≤ (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXL : xFiveCh6 T L ≤ L := (xFiveCh6_le T L).trans inf_le_left
  have hQN : xFiveCh6 T L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [h.centralizer_eq]
    exact (sup_le_sup_right hXL T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
  have hST : pCoreOf 2 (xFiveCh6 T L ⊔ T) ≤ T :=
    F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf le_sup_right)
  refine ⟨CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_left.trans le_sup_right) hQN (h.sylow.1.to_le inf_le_left), hST, ?_⟩
  obtain ⟨x₀, hx₀, hx₀5⟩ := h.exists_orderOf_five_ch6 horth
  have hx₀X : x₀ ∈ xFiveCh6 T L := Subgroup.subset_closure ⟨hx₀, hx₀5⟩
  exact h.le_sup_of_orderOf_five_ch6 horth hx₀ hx₀5 hST
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hx₀X))

theorem thompsonJk_one_le_ch6 (hH11 : Ch6InH11) (h : Hyp611 G T M L V 4)
    (horth : IsOrthCh5 L V 4) {S : Subgroup G} (hVS : V ≤ S) (hST : S ≤ T)
    (hSL : S ≤ (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) :
    thompsonJk 1 S ≤ S ⊓ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.isElemAbelian
  obtain ⟨a, hna, -, hc, hB⟩ := id horth
  have ha : a = 2 := by omega
  have hB' : BinaryOrthogonalFour (V := IntMod V hV) (autI hV L) ⊤ ⊥ a := hB
  have hLM : autI hV L ≤ autI hV M := A4.autOn_mono h.L_le
  have hMN : autI hV M ≤ Subgroup.normalizer (autI hV L : Set (MulAut (IntMod V hV))) := by
    have key : ∀ k : Subgroup.normalizer (V : Set G), (k : G) ∈ M → ∀ ψ ∈ autI hV L,
        convI hV k * ψ * (convI hV k)⁻¹ ∈ autI hV L := by
      intro k hkM ψ hψ
      obtain ⟨ℓ, hℓL, rfl⟩ := (mem_autI hV).mp hψ
      rw [← map_inv, ← map_mul, ← map_mul]
      have hmem : ((k * ℓ * k⁻¹ : Subgroup.normalizer (V : Set G)) : G) ∈ L := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.mp (h.normal hkM) ℓ).mp hℓL
      exact convI_mem_autI hV hmem (k * ℓ * k⁻¹).2
    intro φ hφ
    obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).mp hφ
    rw [Subgroup.mem_normalizer_iff]
    intro ψ
    refine ⟨key g hgM ψ, fun hψ => ?_⟩
    have := key g⁻¹ (M.inv_mem hgM) _ hψ
    rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
      inv_mul_cancel, mul_one] at this
  have hH := fun (A : Subgroup (MulAut (IntMod V hV))) (hAM : A ≤ autI hV M) (hA1 : A ≠ ⊥)
      (hAe : IsElemAbelian2 A) =>
    hH11 (IntMod V hV) (autI hV L) (autI hV M) a IntMod.sq_eq_one (by omega) hLM hMN hB' A hAM
      hA1 hAe
  have hTLN : T ⊓ L ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro x hx
    exact mem_normalizer_inf_ch6 (Subgroup.le_normalizer hx.1)
      (F7.normalizer_le_normalizer_centralizer _ (h.T_le_normalizer hx.1))
  have hSL' : ∀ A : Subgroup G, A ≤ S → autI hV A ≤ autI hV L := by
    intro A hAS φ hφ
    obtain ⟨g, hgA, rfl⟩ := (mem_autI hV).mp hφ
    have hg : (g : G) ∈ ((T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) :=
      hSL (hAS hgA)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTLN] at hg
    obtain ⟨p, hp, c, hc, hpc⟩ := hg
    have hpN : p ∈ Subgroup.normalizer (V : Set G) := h.T_le_normalizer hp.1
    have hcN : c ∈ Subgroup.normalizer (V : Set G) := h.T_le_normalizer hc.1
    have hgeq : g = ⟨p, hpN⟩ * ⟨c, hcN⟩ := Subtype.ext hpc.symm
    have hc1 : convI hV ⟨c, hcN⟩ = 1 := (convI_eq_one_iff hV _).mpr hc.2
    rw [hgeq, map_mul, hc1, mul_one]
    exact convI_mem_autI hV hp.2 hpN
  unfold thompsonJk
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAS, hAe, hAmax⟩ := hA
  refine le_inf hAS ?_
  intro x hxA
  by_contra hxC
  obtain ⟨E, hES, hEe, hEc⟩ := H.exists_isElemAbelian_card_pRank S
  have hAE := hAmax E hES hEe
  have hAle := H.card_le_two_pow_pRank hAS hAe
  obtain ⟨k, hk⟩ := H.exists_card_eq_two_pow_of_isElemAbelian hAe
  set m := CFSG.Open.pRank 2 S with hm
  have hkm : k ≤ m := by
    rw [hk] at hAle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hAle
  have hmk : m ≤ k + 1 := by
    have h2 : 2 ^ m ≤ 2 ^ (k + 1) :=
      calc 2 ^ m ≤ 2 ^ 1 * 2 ^ k := by rw [← hEc, ← hk]; exact hAE
        _ = 2 ^ (k + 1) := by ring
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have hcor : IsElemAbelianCorank S (m - k) A :=
    ⟨hAS, hAe, by rw [hk, ← pow_add]; congr 1; omega⟩
  have hB24 := card_le_relIndex_mul_card_mul_two_pow hV hVS hcor
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAS.trans (hST.trans h.T_le_normalizer)
  have hĀM : autI hV A ≤ autI hV M := A4.autOn_mono (hAS.trans (hST.trans h.T_le))
  have hĀ1 : autI hV A ≠ ⊥ := by
    intro h0
    apply hxC
    have hmem := convI_mem_autI hV hxA (hAN hxA)
    rw [h0, Subgroup.mem_bot] at hmem
    exact (convI_eq_one_iff hV _).mp hmem
  have hĀe : IsElemAbelian2 (autI hV A) := isElemAbelian2_autI hV hAe hAN
  obtain ⟨-, -, h3⟩ := hH _ hĀM hĀ1 hĀe
  have h2 := h3 (hSL' A hAS)
  rw [E3.rk_autI_eq_mQuot hV hAN, E3.rkIdx_fixV_autI hV hAN] at h2
  have hA2 : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAe
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  rw [E3.relIndex_eq_two_pow hA2 (A ⊓ Subgroup.centralizer (V : Set G)),
    E3.card_eq_two_pow_mul hV2
      (inf_le_left : V ⊓ Subgroup.centralizer (A : Set G) ≤ V)] at hB24
  set x := mQuot A (A ⊓ Subgroup.centralizer (V : Set G))
  set y := mQuot V (V ⊓ Subgroup.centralizer (A : Set G))
  set c := Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))
  have hc : 0 < c := Nat.card_pos
  have hj : 2 ^ (m - k) ≤ 2 :=
    calc 2 ^ (m - k) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := by norm_num
  have h4 : 2 ^ y * c ≤ 2 ^ (x + 1) * c :=
    hB24.trans (calc 2 ^ x * c * 2 ^ (m - k) ≤ 2 ^ x * c * 2 := Nat.mul_le_mul_left _ hj
      _ = 2 ^ (x + 1) * c := by ring)
  have h5 : 2 ^ y ≤ 2 ^ (x + 1) := Nat.le_of_mul_le_mul_right h4 hc
  have h6 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
  omega

theorem normalizer_le_and_isUniqueM_ch6 (h432 : Stmt4_3_2) (h : Hyp611 G T M L V 4) :
    Subgroup.normalizer (V : Set G) ≤ M ∧
      IsUniqueM (Subgroup.normalizer (ch6Q T V : Set G)) M := by
  have hU := h.isUniqueM h432
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.isElemAbelian
  have hQ := h.centralizer_eq
  have hQ1 : ch6Q T V ≠ ⊥ := by rw [hQ]; exact h.maximal.1.2.2.2
  have hQ2 : IsPGroup 2 (ch6Q T V) := h.sylow.1.to_le inf_le_left
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  exact ⟨le_of_isUniqueM_of_le_twoLocal hU h.sup_le_normalizer ⟨V, h.ne_bot, hV2, rfl⟩,
    ⟨⟨h.maxTwoLocal, le_of_isUniqueM_of_le_twoLocal hU hLTQ ⟨_, hQ1, hQ2, rfl⟩⟩,
      fun M' hM' => hU.2 M' ⟨hM'.1, hLTQ.trans hM'.2⟩⟩⟩

theorem oTwoFIn_le_ch6 (h432 : Stmt4_3_2) (hH11 : Ch6InH11) (h : Hyp611 G T M L V 4)
    (horth : IsOrthCh5 L V 4) (hr : 1 < rParam V) {M₁ : Subgroup G}
    (hXT : xFiveCh6 T L ⊔ T ≤ M₁) : oTwoFIn M₁ ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQS, hST, hSL⟩ := h.pCoreOf_xFive_props_ch6 horth
  set S := pCoreOf 2 (xFiveCh6 T L ⊔ T) with hSdef
  have hV := h.isElemAbelian
  have hVQ : V ≤ ch6Q T V := fun v hv =>
    ⟨h.le_T hv, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (B2F.isElemAbelian_comm hV hw hv)⟩
  have hVS : V ≤ S := hVQ.trans hQS
  have hJ := h.thompsonJk_one_le_ch6 hH11 horth hVS hST hSL
  have hSM₁ : S ≤ M₁ := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hXT
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTM₁ : T ≤ M₁ := le_sup_right.trans hXT
  have hQ₁S : pCoreOf 2 M₁ ≤ S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf hTM₁)).trans le_sup_right)
      (hXT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁)
  set K := oTwoFIn M₁ with hKdef
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := hSM₁.trans C2Six.le_normalizer_oTwoFIn
  have hPK : pCoreOf 2 K ≤ S ⊓ K := by
    refine le_inf ?_ (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    refine le_trans ?_ hQ₁S
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans
        (Subgroup.map_subtype_le _ : oTwoFIn M₁ ≤ M₁))
      (C2Six.le_normalizer_oTwoFIn.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hodd : ¬ 2 ∣ (pCoreOf 2 K).relIndex K := by
    have h1 : Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) := odd_card_oTwoFIn_quotient M₁
    have e : (pCoreOf 2 K).relIndex K = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
      show (((CFSG.Open.pCore 2 ↥K).map K.subtype).comap K.subtype).index = _
      rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
      rfl
    rw [e]
    exact fun h2 => (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)
  have hSyl : IsSylowIn 2 S (S ⊔ K) := by
    refine ⟨le_sup_left, hS2, fun h2 => hodd ?_⟩
    rw [relIndex_sup_eq_inf_ch6 hSK] at h2
    exact h2.trans (Subgroup.relIndex_dvd_of_le_left K hPK)
  have hsolv : Group.IsSolvable ↥(S ⊔ K) := by
    rw [sup_comm]
    exact isSolvable_oTwoFIn_sup hSM₁ hS2
  obtain ⟨hNV, hNQ⟩ := h.normalizer_le_and_isUniqueM_ch6 h432
  have := ch6InE626_proved G T V M (S ⊔ K) S 1 h.sylow h.ne_bot hV h.le_T h.T_le_normalizer hNV
    hNQ one_pos (by exact_mod_cast E1.solvable_nParam_le_one hsolv) hSyl hQS hST
    (by exact_mod_cast hr) hJ
  exact le_sup_right.trans this.1

end Hyp611

@[expose] def Res614EndGame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V M₁ K₁ X : Subgroup G),
    Hyp611 G T M L V 4 → IsOrthCh5 L V 4 → quasithinIsMaxTwoLocal M₁ →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁ → M₁ ≠ M →
    K₁ ∈ cComp M₁ → CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) → ¬ K₁ ≤ M →
    X ≤ L → X ≤ M₁ → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 →
    ((X ⊓ T).subgroupOf X).Normal → T ≤ Subgroup.normalizer (X : Set G) →
    X ≤ Subgroup.normalizer (K₁ : Set G) → X ≤ conjClosure K₁ T →
    ¬ X ≤ Subgroup.normalizer ((T ⊓ conjClosure K₁ T : Subgroup G) : Set G) → False

end CaseAi

end CFSG.Quasithin.H13
