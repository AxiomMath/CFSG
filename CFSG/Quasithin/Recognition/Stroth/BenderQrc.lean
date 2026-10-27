module

public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15Proof
public import CFSG.Quasithin.Background.AutOnSylow
public import CFSG.Quasithin.Background.AutOnFixV
public import CFSG.Quasithin.Vol2.Ch3zCmp
public import CFSG.Quasithin.Vol2.Ch3yChain
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.B2F
open scoped commutatorElement

private theorem relIndex_conj_le_of_le {G : Type*} [Group G] {V R₂ : Subgroup G}
    (hq : ∀ E₀ : Subgroup G, E₀ ≤ R₂ → IsElemAbelian 2 E₀ →
      ¬ E₀ ≤ Subgroup.centralizer (V : Set G) →
      ((Subgroup.centralizer (V : Set G)).relIndex E₀) ^ 2 ≤
        (Subgroup.centralizer (E₀ : Set G)).relIndex V)
    {g : G} (hg : g ∈ Subgroup.normalizer (R₂ : Set G)) {E : Subgroup G}
    (hER₂ : E ≤ R₂) (hE : IsElemAbelian 2 E)
    (hnc : ¬ E ≤ Subgroup.centralizer (cjSub g V : Set G)) :
    ((Subgroup.centralizer (cjSub g V : Set G)).relIndex E) ^ 2 ≤
      (Subgroup.centralizer (E : Set G)).relIndex (cjSub g V) := by
  have hE₀R₂ : cjSub g⁻¹ E ≤ R₂ := cjSub_le (Subgroup.inv_mem _ hg) hER₂
  have hnc₀ : ¬ cjSub g⁻¹ E ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hnc
    have := cjSub_mono (g := g) hle
    rwa [cjSub_cjSub_inv, B2F.cjSub_centralizer] at this
  have h := hq _ hE₀R₂ (isElemAbelian_cjSub hE) hnc₀
  have r1 : (cjSub g (Subgroup.centralizer (V : Set G))).relIndex (cjSub g (cjSub g⁻¹ E)) =
      (Subgroup.centralizer (V : Set G)).relIndex (cjSub g⁻¹ E) :=
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have r2 : (cjSub g (Subgroup.centralizer (cjSub g⁻¹ E : Set G))).relIndex (cjSub g V) =
      (Subgroup.centralizer (cjSub g⁻¹ E : Set G)).relIndex V :=
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  rw [B2F.cjSub_centralizer, cjSub_cjSub_inv] at r1 r2
  rw [r1, r2]
  exact h

theorem false_of_d15Four {G : Type*} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}
    (h : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂) {q : ℕ} (hq : 2 ≤ q)
    (hJ : ¬ thompsonJ T ≤ pCoreOf 2 G₂)
    (hA : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      (A ⊓ pCoreOf 2 G₂).relIndex A ≤ q)
    (hsec : ∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N →
      ¬ IsCentralStep G₂ L N →
      ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 G₂ →
        q ^ 2 ≤ (centralizerMod L N A).relIndex N)
    (hV : ∀ E : Subgroup G, E ≤ pCoreOf 2 G₂ → IsElemAbelian 2 E →
      ¬ E ≤ Subgroup.centralizer (V : Set G) →
      ((Subgroup.centralizer (V : Set G)).relIndex E) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex V)
    {c : ℕ} (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV' := h.reduced.2.2.1
  have hmp := h.minParabolic hnff
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  have hTG₁ : T ≤ G₁ := h.sylow₁.1
  have hTG₂ : T ≤ G₂ := h.sylow₂.1
  have hR₂T : R₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hUT : U ≤ T := hUR₂.trans hR₂T
  have hUG₂ : U ≤ G₂ := hUT.trans hTG₂
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hUe : IsElemAbelian 2 U := D15Proof.isElemAbelian_conjClosure h hnff hVR₂
  have hUP : ⁅U, oTwoUpper G₂⁆ ≠ ⊥ := D15Proof.commutator_ne_bot h
  obtain ⟨A, hAmax, hAR₂⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ R₂ := by
    by_contra hall
    push Not at hall
    exact hJ (iSup₂_le fun A hA => hall A hA)
  have hAT : A ≤ T := hAmax.1
  have hAe : IsElemAbelian 2 A := hAmax.2.1
  have hCAU : A ⊓ Subgroup.centralizer (U : Set G) ≤ R₂ :=
    D15Proof.inf_centralizer_le_pCoreOf hmp hG₂U hUP hAT
  set B := R₂ ⊓ A with hBdef
  have hBA : B ≤ A := inf_le_right
  have ha0 : 0 < R₂.relIndex A := Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _)
  have hb0 : 0 < (Subgroup.centralizer (U : Set G)).relIndex B :=
    Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _)
  have hab : (Subgroup.centralizer (U : Set G)).relIndex A =
      (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A := by
    have := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (U : Set G)) R₂ A
    have e : (Subgroup.centralizer (U : Set G) ⊓ R₂).relIndex A =
        (Subgroup.centralizer (U : Set G)).relIndex A := by
      rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (U : Set G) ⊓ R₂),
        ← Subgroup.inf_relIndex_right (Subgroup.centralizer (U : Set G)) A]
      congr 1
      refine le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf (le_inf inf_le_left ?_)
        inf_le_right)
      rintro x ⟨hxC, hxA⟩
      exact hCAU ⟨hxA, hxC⟩
    rw [e] at this
    exact this.symm
  have hi : (Subgroup.centralizer (A : Set G)).relIndex U ≤
      (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A := by
    have hAoff := card_le_relIndex_mul_card hUe hUT hAmax
    have hoff' : Nat.card U ≤ (Subgroup.centralizer (U : Set G)).relIndex A *
        Nat.card (Subgroup.centralizer (A : Set G) ⊓ U : Subgroup G) := by
      rw [Subgroup.inf_relIndex_left, inf_comm] at hAoff
      exact hAoff
    have e2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set G)) U
    have hpos : 0 < Nat.card (Subgroup.centralizer (A : Set G) ⊓ U : Subgroup G) := Nat.card_pos
    rw [← hab]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [e2]
    exact hoff'
  have hii : q ^ 4 ≤ (Subgroup.centralizer (A : Set G)).relIndex U := by
    have hpow : q ^ 4 ≤ (q ^ 2) ^ c := by
      calc q ^ 4 = (q ^ 2) ^ 2 := by ring
        _ ≤ (q ^ 2) ^ c :=
          Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))) hc
    refine hpow.trans ?_
    refine D15Proof.pow_le_relIndex hUG₂ (hAT.trans hTG₂) (fun L' N' hstep hnc => ?_) hser
    exact hsec L' N' hstep hnc A hAT hAe hAR₂
  have hQ : ∀ k ∈ G₂, ∀ E : Subgroup G, E ≤ B →
      ¬ E ≤ Subgroup.centralizer (cjSub k V : Set G) →
      ((Subgroup.centralizer (cjSub k V : Set G)).relIndex E) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex (cjSub k V) := by
    intro k hk E hEB hnc
    have hEA : E ≤ A := hEB.trans hBA
    exact relIndex_conj_le_of_le (V := V) (R₂ := R₂)
      (fun E₀ hE₀R₂ hE₀e hnc₀ => hV E₀ hE₀R₂ hE₀e hnc₀)
      (hG₂R₂ hk) (hEB.trans inf_le_left) (isElemAbelian_mono hEA hAe) hnc
  have hiii := Ch3y.sq_relIndex_le_nonstrict (V := V) (H := G₂) (B := B) hQ B le_rfl
  have hiv : (Subgroup.centralizer (B : Set G)).relIndex U ≤
      (Subgroup.centralizer (A : Set G)).relIndex U :=
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le fun x hx => hBA hx)
      (D15Proof.relIndex_ne_zero _ _)
  have hb_le_a : (Subgroup.centralizer (U : Set G)).relIndex B ≤ R₂.relIndex A := by
    have h1 : (Subgroup.centralizer (U : Set G)).relIndex B ^ 2 ≤
        (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A :=
      (hiii.trans hiv).trans hi
    rw [pow_two] at h1
    exact Nat.le_of_mul_le_mul_left h1 hb0
  have haq : R₂.relIndex A ≤ q := by
    have := hA A hAT hAe
    rwa [Subgroup.inf_relIndex_left] at this
  have hu_le : (Subgroup.centralizer (A : Set G)).relIndex U ≤ q ^ 2 := by
    have hbq : (Subgroup.centralizer (U : Set G)).relIndex B ≤ q :=
      hb_le_a.trans haq
    have h1 : (Subgroup.centralizer (A : Set G)).relIndex U ≤ q * q :=
      hi.trans (Nat.mul_le_mul hbq haq)
    simpa [pow_two] using h1
  have hqq : q ^ 4 ≤ q ^ 2 := hii.trans hu_le
  have hq2pos : 0 < q ^ 2 := pow_pos (by omega) 2
  have hle1 : q ^ 2 ≤ 1 := by
    have h := Nat.le_of_mul_le_mul_right (show q ^ 2 * q ^ 2 ≤ 1 * q ^ 2 by
      calc q ^ 2 * q ^ 2 = q ^ 4 := by ring
        _ ≤ q ^ 2 := hqq
        _ = 1 * q ^ 2 := by ring) hq2pos
    simpa using h
  nlinarith [hq, hle1]

private theorem mem_centralizer_of_odd_of_centralizes_commutator {G : Type*} [Group G]
    {U P : Subgroup G} {x : G} (hU : IsElemAbelian 2 U)
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) (hxP : x ∈ P)
    (hxN : x ∈ Subgroup.normalizer (U : Set G))
    (hxCI : x ∈ Subgroup.centralizer ((⁅U, P⁆ : Subgroup G) : Set G)) (hxo : Odd (orderOf x)) :
    x ∈ Subgroup.centralizer (U : Set G) := by
  have hI_le_U : ⁅U, P⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hPU
  have hx2C : x ^ 2 ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    set c : G := x * v * x⁻¹ * v⁻¹ with hcdef
    have hcI : c ∈ ⁅U, P⁆ := by
      have h1 : ⁅x, v⁆ ∈ ⁅P, U⁆ := Subgroup.commutator_mem_commutator hxP hv
      rwa [Subgroup.commutator_comm] at h1
    have hcomm : c * x = x * c := Subgroup.mem_centralizer_iff.mp hxCI _ hcI
    have hc2 : c ^ 2 = 1 := hU.2 _ (hI_le_U hcI)
    have hc_conj : x * c * x⁻¹ = c := by rw [← hcomm]; group
    have hc_eq : x * v * x⁻¹ = c * v := by rw [hcdef]; group
    have h1 : (x * x) * v * (x * x)⁻¹ = v := by
      calc (x * x) * v * (x * x)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by group
        _ = x * (c * v) * x⁻¹ := by rw [hc_eq]
        _ = (x * c * x⁻¹) * (x * v * x⁻¹) := by group
        _ = c * (c * v) := by rw [hc_conj, hc_eq]
        _ = (c * c) * v := by group
        _ = v := by rw [← pow_two, hc2, one_mul]
    have h2 : (x * x) * v = v * (x * x) := by
      have := congrArg (fun z => z * (x * x)) h1
      simpa [mul_assoc] using this
    have h3 : v * x ^ 2 = x ^ 2 * v := by simpa [pow_two] using h2.symm
    exact h3
  set φ : MulAut U := conjAct U ⟨x, hxN⟩ with hφdef
  have hφ2 : φ ^ 2 = 1 := by
    ext v
    have hvcomm : (v : G) * (x * x) = (x * x) * (v : G) := by
      simpa [pow_two] using Subgroup.mem_centralizer_iff.mp hx2C v v.2
    rw [hφdef, pow_two, MulAut.mul_apply, AutOn.coe_conjAct_apply,
      AutOn.coe_conjAct_apply, MulAut.one_apply]
    calc x * (x * (v : G) * x⁻¹) * x⁻¹ = (x * x) * (v : G) * (x * x)⁻¹ := by group
      _ = (v : G) := by rw [← hvcomm]; group
  have hdvd : orderOf φ ∣ orderOf x := by
    have h1 := orderOf_map_dvd (conjAct U) ⟨x, hxN⟩
    simpa [hφdef, Subgroup.orderOf_mk x hxN] using h1
  have hord2 : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one hφ2
  have hoddφ : Odd (orderOf φ) := hxo.of_dvd_nat hdvd
  have hone : orderOf φ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · rw [h] at hoddφ
      obtain ⟨k, hk⟩ := hoddφ
      omega
  have hφ1 : φ = 1 := orderOf_eq_one_iff.mp hone
  rw [hφdef] at hφ1
  exact A4.conjAct_eq_one_iff.mp hφ1

theorem false_of_d15Five {G : Type*} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}
    (h : D11Hyp G₁ G₂ T V M₂) {q : ℕ} (hq : 2 ≤ q)
    (hJ : ¬ thompsonJ T ≤ pCoreOf 2 G₂)
    (hA : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      (A ⊓ pCoreOf 2 G₂).relIndex A ≤ q)
    (hsub : ∀ I : Subgroup G, G₂ ≤ Subgroup.normalizer (I : Set G) → IsElemAbelian 2 I →
      pCoreOf 2 G₂ ≤ Subgroup.centralizer (I : Set G) → ¬ G₂ ≤ Subgroup.centralizer (I : Set G) →
      ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 G₂ →
        q ^ 2 ≤ (Subgroup.centralizer (A : Set G) ⊓ I).relIndex I)
    (hU : IsElemAbelian 2 (conjClosure V G₂))
    (h5 : ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  set P := oTwoUpper G₂ with hPdef
  set I := ⁅U, P⁆ with hIdef
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hG₂P : G₂ ≤ Subgroup.normalizer (P : Set G) := le_normalizer_oTwoUpper G₂
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := (oTwoUpper_le G₂).trans hG₂U
  have hI_le_U : I ≤ U := by
    rw [hIdef]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hPU
  have hIe : IsElemAbelian 2 I := isElemAbelian_mono hI_le_U hU
  have hG₂I : G₂ ≤ Subgroup.normalizer (I : Set G) := by
    rw [hIdef]
    exact D14.le_normalizer_commutator hG₂U hG₂P
  have h5' : I ≤ centerOf R₂ := by
    rw [hIdef, hUdef, hPdef, ← F6.twoResidual_eq_oTwoUpper]
    exact h5
  have hI_le_R₂ : I ≤ R₂ := h5'.trans inf_le_left
  have hR₂_le_C : R₂ ≤ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact h5'.trans inf_le_right
  have hG₂nc : ¬ G₂ ≤ Subgroup.centralizer (I : Set G) := by
    intro hC
    have hPCU : P ≤ Subgroup.centralizer (U : Set G) := by
      rw [hPdef, oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hxG₂, hxo⟩
      exact mem_centralizer_of_odd_of_centralizes_commutator hU hPU
        (mem_oTwoUpper_of_odd hxG₂ hxo) (hG₂U hxG₂) (hC hxG₂) hxo
    have hIbot : ⁅U, P⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hPCU
    exact D15Proof.commutator_ne_bot h (by rw [← hUdef, ← hPdef]; exact hIbot)
  obtain ⟨A, hAmax, hAR₂⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ R₂ := by
    by_contra hall
    push Not at hall
    exact hJ (iSup₂_le fun A hA => hall A hA)
  have hAT : A ≤ T := hAmax.1
  have hAe : IsElemAbelian 2 A := hAmax.2.1
  have hkey := hsub I hG₂I hIe hR₂_le_C hG₂nc A hAT hAe hAR₂
  have hI_le_T : I ≤ T := hI_le_R₂.trans (B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂)
  have hmax := card_le_relIndex_mul_card hIe hI_le_T hAmax
  have hpos : 0 < Nat.card (I ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  have hrm : (I ⊓ Subgroup.centralizer (A : Set G)).relIndex I *
      Nat.card (I ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) = Nat.card I := by
    have := Subgroup.relIndex_mul_card (I ⊓ Subgroup.centralizer (A : Set G)) I
    rwa [inf_eq_left.mpr inf_le_left] at this
  have hle : (Subgroup.centralizer (A : Set G) ⊓ I).relIndex I ≤
      (A ⊓ Subgroup.centralizer (I : Set G)).relIndex A := by
    rw [inf_comm (Subgroup.centralizer (A : Set G)) I]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [hrm]
    exact hmax
  have hle2 : (A ⊓ Subgroup.centralizer (I : Set G)).relIndex A ≤ R₂.relIndex A := by
    have hsub' : A ⊓ R₂ ≤ A ⊓ Subgroup.centralizer (I : Set G) :=
      inf_le_inf_left A hR₂_le_C
    have h : (A ⊓ Subgroup.centralizer (I : Set G)).relIndex A ≤
        (A ⊓ R₂).relIndex A :=
      Subgroup.relIndex_le_of_le_left hsub' (D15Proof.relIndex_ne_zero _ _)
    calc (A ⊓ Subgroup.centralizer (I : Set G)).relIndex A
        ≤ (A ⊓ R₂).relIndex A := h
      _ = R₂.relIndex A := Subgroup.inf_relIndex_left A R₂
  have hle_q : R₂.relIndex A ≤ q := by
    have := hA A hAT hAe
    rwa [Subgroup.inf_relIndex_left] at this
  have hq_le : q ^ 2 ≤ q := hkey.trans (hle.trans hle2) |>.trans hle_q
  nlinarith [hq, hq_le]

private theorem index_fixV_zpowers_eq_card_commV {W : Type*} [CommGroup W] [Finite W]
    (a : MulAut W) :
    (fixV (Subgroup.zpowers a)).index = Nat.card (commV (Subgroup.zpowers a)) := by
  have h := Subgroup.index_ker (commHom a)
  rw [ker_commHom, MonoidHom.range_eq_map, ← commV_zpowers_eq_map a] at h
  exact h

private theorem not_ffInt_of_disp {G : Type*} [Group G] [Finite G] {G₁ V T : Subgroup G}
    (hV : IsElemAbelian 2 V) (hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G))
    (hT : IsSylowTwoOf T G₁) {q : ℕ} (hq : 2 ≤ q)
    (hdisp : ∀ t ∈ T, t * t ∈ Subgroup.centralizer (V : Set G) →
      t ∉ Subgroup.centralizer (V : Set G) →
      q ^ 2 ≤ (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V)
    (hab : ∀ A : Subgroup G, A ≤ T → (∀ a ∈ A, ∀ b ∈ A,
        a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
          a * a ∈ Subgroup.centralizer (V : Set G)) →
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ q) :
    ¬ IsFFInt G₁ V hV := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  intro hFF
  obtain ⟨Astar, hAstar_le, hAstar_ne, hAstar_el, hAstar_off⟩ := hFF
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hG₁V
  have hSyl : IsSylowTwoOf (autOn T V) (autOn G₁ V) := AutOn.isSylowTwoOf_autOn hT hG₁V
  have hAstarP : IsPGroup 2 Astar := hAstar_el.isPGroup
  obtain ⟨X, hX, hBX⟩ := exists_conj_le_of_isSylowTwoOf hSyl hAstar_le hAstarP
  set B : Subgroup (MulAut ↥V) := cjSub X Astar with hBdef
  have hB_el : IsElemAbelian2 B := B6.isElemAbelian2_conjSub hAstar_el X
  have hB_ne : B ≠ ⊥ := by
    intro hbot
    apply hAstar_ne
    have h1 : cjSub X⁻¹ (cjSub X Astar) = Astar := by
      simpa using cjSub_cjSub_inv X⁻¹ Astar
    have h2 : cjSub X⁻¹ (⊥ : Subgroup (MulAut ↥V)) = ⊥ := by
      rw [cjSub, Subgroup.map_bot]
    have := congrArg (cjSub X⁻¹) hbot
    rw [hBdef, h1, h2] at this
    exact this
  have hB_off : Nat.card ↥V ≤ Nat.card B * Nat.card (fixV B) := by
    rw [hBdef]
    change Nat.card ↥V ≤ Nat.card (Astar.map (MulAut.conj X).toMonoidHom) *
      Nat.card (fixV (Astar.map (MulAut.conj X).toMonoidHom))
    rw [Subgroup.card_map_of_injective (MulAut.conj X).injective,
      CFSG.Quasithin.ConjTransport.card_fixV_map_conj]
    exact hAstar_off
  let ψ : T →* MulAut ↥V := A4.actionOn V T hTN
  let C : Subgroup T := B.comap ψ
  let A : Subgroup G := C.map T.subtype
  have hAT : A ≤ T := Subgroup.map_subtype_le C
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hTN
  have haut : autOn A V = B := by
    ext b
    constructor
    · intro hb
      obtain ⟨x, hxN, hxA, rfl⟩ := AutOn.mem_autOn_iff_exists.mp hb
      obtain ⟨t, htC, htx⟩ := Subgroup.mem_map.mp hxA
      subst htx
      have hψ : ψ t ∈ B := htC
      have hsub : (⟨(t : G), hxN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨(t : G), hTN t.2⟩ := Subtype.ext rfl
      change (conjAct V) (⟨(t : G), hxN⟩ : Subgroup.normalizer (V : Set G)) ∈ B
      rw [hsub]
      exact hψ
    · intro hb
      obtain ⟨x, hxN, hxT, hxb⟩ := AutOn.mem_autOn_iff_exists.mp (hBX hb)
      refine AutOn.mem_autOn_iff_exists.mpr ⟨x, hxN, ?_, hxb⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxT⟩, ?_, rfl⟩
      show ψ ⟨x, hxT⟩ ∈ B
      have hsub : (⟨x, hTN hxT⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨x, hxN⟩ := Subtype.ext rfl
      have hψx : ψ ⟨x, hxT⟩ = conjAct V ⟨x, hTN hxT⟩ := rfl
      rw [hψx, hsub, hxb]
      exact hb
  have hA_quad : ∀ a ∈ A, ∀ b ∈ A,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
        a * a ∈ Subgroup.centralizer (V : Set G) := by
    intro a ha b hb
    have haN : a ∈ Subgroup.normalizer (V : Set G) := hAN ha
    have hbN : b ∈ Subgroup.normalizer (V : Set G) := hAN hb
    have hφa : conjAct V ⟨a, haN⟩ ∈ B := by
      rw [← haut]
      exact AutOn.conjAct_mem_autOn_of_mem haN ha
    have hφb : conjAct V ⟨b, hbN⟩ ∈ B := by
      rw [← haut]
      exact AutOn.conjAct_mem_autOn_of_mem hbN hb
    constructor
    · have hc : a * b * a⁻¹ * b⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
      have hN : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.normalizer (V : Set G) := hAN hc
      have hsub : (⟨a * b * a⁻¹ * b⁻¹, hN⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨a, haN⟩ * ⟨b, hbN⟩ * ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩⁻¹ :
            Subgroup.normalizer (V : Set G)) := Subtype.ext rfl
      have h1 : conjAct V ⟨a * b * a⁻¹ * b⁻¹, hN⟩ = 1 := by
        rw [hsub, map_mul, map_mul, map_mul, map_inv, map_inv]
        have hcomm := hB_el.1 _ hφa _ hφb
        calc (conjAct V ⟨a, haN⟩ * conjAct V ⟨b, hbN⟩) *
              (conjAct V ⟨a, haN⟩)⁻¹ * (conjAct V ⟨b, hbN⟩)⁻¹
            = ((conjAct V ⟨b, hbN⟩) * (conjAct V ⟨a, haN⟩)) *
              (conjAct V ⟨a, haN⟩)⁻¹ * (conjAct V ⟨b, hbN⟩)⁻¹ := by rw [hcomm]
          _ = 1 := by group
      exact A4.conjAct_eq_one_iff.mp h1
    · have hc : a * a ∈ A := A.mul_mem ha ha
      have hN : a * a ∈ Subgroup.normalizer (V : Set G) := hAN hc
      have hsub : (⟨a * a, hN⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨a, haN⟩ * ⟨a, haN⟩ : Subgroup.normalizer (V : Set G)) := Subtype.ext rfl
      have h1 : conjAct V ⟨a * a, hN⟩ = 1 := by
        rw [hsub, map_mul, ← pow_two, hB_el.2 _ hφa]
      exact A4.conjAct_eq_one_iff.mp h1
  have hAbound : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ q :=
    hab A hAT hA_quad
  have hcardB : Nat.card B = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    rw [← haut, AutOn.card_autOn_eq_relIndex hAN]
  have hBq : Nat.card B ≤ q := hcardB.trans_le hAbound
  have hB_exists : ∃ b : MulAut ↥V, b ∈ B ∧ b ≠ 1 := by
    by_contra h
    push Not at h
    apply hB_ne
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact h x hx
  obtain ⟨b, hbB, hbne⟩ := hB_exists
  have hbB' : b ∈ autOn A V := by rwa [haut]
  obtain ⟨t, htN, htA, htb⟩ := AutOn.mem_autOn_iff_exists.mp hbB'
  have ht2 : t * t ∈ Subgroup.centralizer (V : Set G) := by
    have hb2 : b * b = 1 := hB_el.2 b hbB
    have hsub : (⟨t * t, hAN (A.mul_mem htA htA)⟩ : Subgroup.normalizer (V : Set G)) =
        (⟨t, htN⟩ : Subgroup.normalizer (V : Set G)) * ⟨t, htN⟩ := Subtype.ext rfl
    have h1 : conjAct V ⟨t * t, hAN (A.mul_mem htA htA)⟩ = 1 := by
      rw [hsub, map_mul, htb, hb2]
    exact A4.conjAct_eq_one_iff.mp h1
  have htnc : t ∉ Subgroup.centralizer (V : Set G) := by
    intro hc
    apply hbne
    rw [← htb]
    exact A4.conjAct_eq_one_iff.mpr hc
  have hdisp_t : q ^ 2 ≤ (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V :=
    hdisp t (hAT htA) ht2 htnc
  have hz : Subgroup.zpowers (conjAct V ⟨t, htN⟩) = autOn (Subgroup.zpowers t) V := by
    have hLN : Subgroup.zpowers t ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.zpowers_le.mpr htN
    ext a
    rw [Subgroup.mem_zpowers_iff, AutOn.mem_autOn_iff_exists]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨t ^ n, hLN (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩), ⟨n, rfl⟩, ?_⟩
      have hsub : (⟨t ^ n, hLN (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)⟩ :
          Subgroup.normalizer (V : Set G)) = ⟨t, htN⟩ ^ n := Subtype.ext rfl
      rw [hsub, map_zpow]
    · rintro ⟨x, hxN, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      have hx : (⟨t ^ n, hxN⟩ : Subgroup.normalizer (V : Set G)) = ⟨t, htN⟩ ^ n :=
        Subtype.ext rfl
      rw [hx, map_zpow]
  have hfix_card : Nat.card (fixV (Subgroup.zpowers (conjAct V ⟨t, htN⟩))) =
      Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
    rw [hz, card_fixV_autOn_eq hV (Subgroup.zpowers_le.mpr htN),
      CFSG.centralizer_zpowers_eq_centralizer_singleton]
  have hindex : (fixV (Subgroup.zpowers (conjAct V ⟨t, htN⟩))).index =
      (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V := by
    have e1 := Subgroup.card_mul_index (fixV (Subgroup.zpowers (conjAct V ⟨t, htN⟩)))
    have e2 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer ({t} : Set G)) V
    rw [inf_of_le_left inf_le_left] at e2
    rw [hfix_card] at e1
    have e3 : Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
          (fixV (Subgroup.zpowers (conjAct V ⟨t, htN⟩))).index =
        Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
          (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V := by
      rw [e1, mul_comm, e2]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos e3
  have hfixidx : (fixV (Subgroup.zpowers b)).index =
      (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V := by
    rw [← htb, hindex]
  have hfix_le : fixV B ≤ fixV (Subgroup.zpowers b) := by
    intro w hw x hx
    exact hw x (Subgroup.zpowers_le.mpr hbB hx)
  have hcard_b : Nat.card (fixV (Subgroup.zpowers b)) *
      (fixV (Subgroup.zpowers b)).index = Nat.card ↥V :=
    Subgroup.card_mul_index (fixV (Subgroup.zpowers b))
  have hB_off' : Nat.card ↥V ≤ Nat.card B * Nat.card (fixV (Subgroup.zpowers b)) :=
    hB_off.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hfix_le))
  have hidx_le_card : (fixV (Subgroup.zpowers b)).index ≤ Nat.card B := by
    have hpos : 0 < Nat.card (fixV (Subgroup.zpowers b)) := Nat.card_pos
    have h1 : Nat.card (fixV (Subgroup.zpowers b)) * (fixV (Subgroup.zpowers b)).index
        ≤ Nat.card (fixV (Subgroup.zpowers b)) * Nat.card B := by
      rw [hcard_b, mul_comm]
      exact hB_off'
    exact Nat.le_of_mul_le_mul_left h1 hpos
  have h2 : q ^ 2 ≤ Nat.card B := hdisp_t.trans (hfixidx.ge.trans hidx_le_card)
  nlinarith [hq, h2, hBq]

private theorem not_dualFFInt_of_disp {G : Type*} [Group G] [Finite G] {G₁ V T : Subgroup G}
    (hV : IsElemAbelian 2 V) (hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G))
    (hT : IsSylowTwoOf T G₁) {q : ℕ} (hq : 2 ≤ q)
    (hdisp : ∀ t ∈ T, t * t ∈ Subgroup.centralizer (V : Set G) →
      t ∉ Subgroup.centralizer (V : Set G) →
      q ^ 2 ≤ (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V)
    (hab : ∀ A : Subgroup G, A ≤ T → (∀ a ∈ A, ∀ b ∈ A,
        a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
          a * a ∈ Subgroup.centralizer (V : Set G)) →
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ q) :
    ¬ IsDualFFInt G₁ V hV := by
  letI : IsMulCommutative ↥V := hV.1
  letI : CommGroup ↥V := IsMulCommutative.instCommGroup
  intro hFF
  obtain ⟨B, hB_le, hB_ne, hB_el, hB_off⟩ := hFF
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hG₁V
  let δ : MulAut ↥V →* MulAut (DualGrp ↥V) := dualAct ↥V
  have hδinj : Function.Injective δ :=
    dualAct_injective (V := ↥V) (fun v : ↥V => Subtype.ext (hV.2 v v.2))
  let C : Subgroup (MulAut ↥V) := B.comap δ
  have hB_range : B ≤ δ.range :=
    hB_le.trans (Subgroup.map_le_range δ (autOn G₁ V))
  have hB_eq : dualSub C = B := Subgroup.map_comap_eq_self hB_range
  have hC_le : C ≤ autOn G₁ V := by
    intro c hc
    obtain ⟨a, ha, hca⟩ := Subgroup.mem_map.mp (hB_le (show δ c ∈ B from hc))
    rw [← hδinj hca]
    exact ha
  have hC_el : IsElemAbelian2 C := by
    constructor
    · intro x hx y hy
      apply hδinj
      exact hB_el.1 _ hx _ hy
    · intro x hx
      apply hδinj
      exact hB_el.2 _ hx
  have hC_ne : C ≠ ⊥ := by
    intro hbot
    apply hB_ne
    rw [← hB_eq, hbot]
    exact Subgroup.map_bot δ
  have hSyl : IsSylowTwoOf (autOn T V) (autOn G₁ V) := AutOn.isSylowTwoOf_autOn hT hG₁V
  obtain ⟨X, hX, hCX⟩ := exists_conj_le_of_isSylowTwoOf hSyl hC_le hC_el.isPGroup
  set C' : Subgroup (MulAut ↥V) := cjSub X C with hC'def
  have hC'_le : C' ≤ autOn T V := hCX
  have hC'_el : IsElemAbelian2 C' := B6.isElemAbelian2_conjSub hC_el X
  let ψ : T →* MulAut ↥V := A4.actionOn V T hTN
  let C₀ : Subgroup T := C'.comap ψ
  let A : Subgroup G := C₀.map T.subtype
  have hAT : A ≤ T := Subgroup.map_subtype_le C₀
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hTN
  have haut : autOn A V = C' := by
    ext b
    constructor
    · intro hb
      obtain ⟨x, hxN, hxA, rfl⟩ := AutOn.mem_autOn_iff_exists.mp hb
      obtain ⟨t, htC, htx⟩ := Subgroup.mem_map.mp hxA
      subst htx
      have hψ : ψ t ∈ C' := htC
      have hsub : (⟨(t : G), hxN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨(t : G), hTN t.2⟩ := Subtype.ext rfl
      change (conjAct V) (⟨(t : G), hxN⟩ : Subgroup.normalizer (V : Set G)) ∈ C'
      rw [hsub]
      exact hψ
    · intro hb
      obtain ⟨x, hxN, hxT, hxb⟩ := AutOn.mem_autOn_iff_exists.mp (hC'_le hb)
      refine AutOn.mem_autOn_iff_exists.mpr ⟨x, hxN, ?_, hxb⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxT⟩, ?_, rfl⟩
      show ψ ⟨x, hxT⟩ ∈ C'
      have hsub : (⟨x, hTN hxT⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨x, hxN⟩ := Subtype.ext rfl
      have hψx : ψ ⟨x, hxT⟩ = conjAct V ⟨x, hTN hxT⟩ := rfl
      rw [hψx, hsub, hxb]
      exact hb
  have hA_quad : ∀ a ∈ A, ∀ b ∈ A,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
        a * a ∈ Subgroup.centralizer (V : Set G) := by
    intro a ha b hb
    have haN : a ∈ Subgroup.normalizer (V : Set G) := hAN ha
    have hbN : b ∈ Subgroup.normalizer (V : Set G) := hAN hb
    have hφa : conjAct V ⟨a, haN⟩ ∈ C' := by
      rw [← haut]
      exact AutOn.conjAct_mem_autOn_of_mem haN ha
    have hφb : conjAct V ⟨b, hbN⟩ ∈ C' := by
      rw [← haut]
      exact AutOn.conjAct_mem_autOn_of_mem hbN hb
    constructor
    · have hc : a * b * a⁻¹ * b⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
      have hN : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.normalizer (V : Set G) := hAN hc
      have hsub : (⟨a * b * a⁻¹ * b⁻¹, hN⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨a, haN⟩ * ⟨b, hbN⟩ * ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩⁻¹ :
            Subgroup.normalizer (V : Set G)) := Subtype.ext rfl
      have h1 : conjAct V ⟨a * b * a⁻¹ * b⁻¹, hN⟩ = 1 := by
        rw [hsub, map_mul, map_mul, map_mul, map_inv, map_inv]
        have hcomm := hC'_el.1 _ hφa _ hφb
        calc (conjAct V ⟨a, haN⟩ * conjAct V ⟨b, hbN⟩) *
              (conjAct V ⟨a, haN⟩)⁻¹ * (conjAct V ⟨b, hbN⟩)⁻¹
            = ((conjAct V ⟨b, hbN⟩) * (conjAct V ⟨a, haN⟩)) *
              (conjAct V ⟨a, haN⟩)⁻¹ * (conjAct V ⟨b, hbN⟩)⁻¹ := by rw [hcomm]
          _ = 1 := by group
      exact A4.conjAct_eq_one_iff.mp h1
    · have hc : a * a ∈ A := A.mul_mem ha ha
      have hN : a * a ∈ Subgroup.normalizer (V : Set G) := hAN hc
      have hsub : (⟨a * a, hN⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨a, haN⟩ * ⟨a, haN⟩ : Subgroup.normalizer (V : Set G)) := Subtype.ext rfl
      have h1 : conjAct V ⟨a * a, hN⟩ = 1 := by
        rw [hsub, map_mul, ← pow_two, hC'_el.2 _ hφa]
      exact A4.conjAct_eq_one_iff.mp h1
  have hAbound : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ q :=
    hab A hAT hA_quad
  have hcardC' : Nat.card C' = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    rw [← haut, AutOn.card_autOn_eq_relIndex hAN]
  have hcardB : Nat.card B = Nat.card C' := by
    rw [← hB_eq]
    change Nat.card (C.map δ) = Nat.card C'
    rw [Subgroup.card_map_of_injective hδinj, card_cjSub X C]
  have hBq : Nat.card B ≤ q := by
    rw [hcardB]
    exact hcardC'.trans_le hAbound
  have hC'_ne : C' ≠ ⊥ := by
    intro hbot
    have h1 : cjSub X⁻¹ C' = C := by
      rw [hC'def]
      simpa using cjSub_cjSub_inv X⁻¹ C
    have h2 : cjSub X⁻¹ (⊥ : Subgroup (MulAut ↥V)) = ⊥ := by
      rw [cjSub, Subgroup.map_bot]
    have := congrArg (cjSub X⁻¹) hbot
    rw [h1, h2] at this
    exact hC_ne this
  have hC'_exists : ∃ b : MulAut ↥V, b ∈ C' ∧ b ≠ 1 := by
    by_contra h
    push Not at h
    apply hC'_ne
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact h x hx
  obtain ⟨b, hbB, hbne⟩ := hC'_exists
  have hbB' : b ∈ autOn A V := by rwa [haut]
  obtain ⟨t, htN, htA, htb⟩ := AutOn.mem_autOn_iff_exists.mp hbB'
  have ht2 : t * t ∈ Subgroup.centralizer (V : Set G) := by
    have hb2 : b * b = 1 := hC'_el.2 b hbB
    have hsub : (⟨t * t, hAN (A.mul_mem htA htA)⟩ : Subgroup.normalizer (V : Set G)) =
        (⟨t, htN⟩ : Subgroup.normalizer (V : Set G)) * ⟨t, htN⟩ := Subtype.ext rfl
    have h1 : conjAct V ⟨t * t, hAN (A.mul_mem htA htA)⟩ = 1 := by
      rw [hsub, map_mul, htb, hb2]
    exact A4.conjAct_eq_one_iff.mp h1
  have htnc : t ∉ Subgroup.centralizer (V : Set G) := by
    intro hc
    apply hbne
    rw [← htb]
    exact A4.conjAct_eq_one_iff.mpr hc
  have hdisp_t : q ^ 2 ≤ (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V :=
    hdisp t (hAT htA) ht2 htnc
  have hz : Subgroup.zpowers (conjAct V ⟨t, htN⟩) = autOn (Subgroup.zpowers t) V := by
    have hLN : Subgroup.zpowers t ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.zpowers_le.mpr htN
    ext a
    rw [Subgroup.mem_zpowers_iff, AutOn.mem_autOn_iff_exists]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨t ^ n, hLN (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩), ⟨n, rfl⟩, ?_⟩
      have hsub : (⟨t ^ n, hLN (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)⟩ :
          Subgroup.normalizer (V : Set G)) = ⟨t, htN⟩ ^ n := Subtype.ext rfl
      rw [hsub, map_zpow]
    · rintro ⟨x, hxN, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      have hx : (⟨t ^ n, hxN⟩ : Subgroup.normalizer (V : Set G)) = ⟨t, htN⟩ ^ n :=
        Subtype.ext rfl
      rw [hx, map_zpow]
  have hfix_card : Nat.card (fixV (Subgroup.zpowers (conjAct V ⟨t, htN⟩))) =
      Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
    rw [hz, AutOn.card_fixV_autOn_eq (W := V) (Subgroup.zpowers_le.mpr htN),
      CFSG.centralizer_zpowers_eq_centralizer_singleton]
  have hindex : (fixV (Subgroup.zpowers (conjAct V ⟨t, htN⟩))).index =
      (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V := by
    have e1 := Subgroup.card_mul_index (fixV (Subgroup.zpowers (conjAct V ⟨t, htN⟩)))
    have e2 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer ({t} : Set G)) V
    rw [inf_of_le_left inf_le_left] at e2
    rw [hfix_card] at e1
    have e3 : Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
          (fixV (Subgroup.zpowers (conjAct V ⟨t, htN⟩))).index =
        Nat.card (V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
          (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V := by
      rw [e1, mul_comm, e2]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos e3
  have hcardcomm : Nat.card (commV (Subgroup.zpowers (conjAct V ⟨t, htN⟩))) =
      (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V := by
    rw [← index_fixV_zpowers_eq_card_commV (W := ↥V)
      (conjAct V ⟨t, htN⟩), hindex]
  have hdualidx : (fixV B).index = Nat.card (commV C') := by
    rw [← hB_eq, index_fixV_dualSub (V := ↥V) (fun v : ↥V => Subtype.ext (hV.2 v v.2)) C,
      hC'def]
    exact (CFSG.Quasithin.ConjTransport.card_commV_map_conj C X).symm
  have hcomm_le : commV (Subgroup.zpowers b) ≤ commV C' := by
    intro x hx
    exact Subgroup.closure_mono (by
      rintro _ ⟨a, ha, v, rfl⟩
      exact ⟨a, Subgroup.zpowers_le.mpr hbB ha, v, rfl⟩) hx
  have hcomm_card : Nat.card (commV (Subgroup.zpowers b)) ≤ Nat.card (commV C') :=
    Subgroup.card_le_of_le hcomm_le
  have hfixidx : Nat.card (commV (Subgroup.zpowers b)) =
      (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V := by
    rw [← htb, hcardcomm]
  have hlower : q ^ 2 ≤ (fixV B).index := by
    rw [hdualidx]
    exact hdisp_t.trans (hfixidx.ge.trans hcomm_card)
  have hB_off' : Nat.card (fixV B) * (fixV B).index ≤ Nat.card (fixV B) * Nat.card B := by
    have hcard : Nat.card (fixV B) * (fixV B).index = Nat.card (DualGrp ↥V) :=
      Subgroup.card_mul_index (fixV B)
    rw [hcard, mul_comm]
    exact hB_off
  have hidx_le_card : (fixV B).index ≤ Nat.card B :=
    Nat.le_of_mul_le_mul_left hB_off' Nat.card_pos
  have h2 : q ^ 2 ≤ Nat.card B := hlower.trans hidx_le_card
  nlinarith [hq, h2, hBq]

theorem not_isFFInt_of_disp {G : Type*} [Group G] [Finite G] {G₁ V T : Subgroup G}
    (hV : IsElemAbelian 2 V) (hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G))
    (hT : IsSylowTwoOf T G₁) {q : ℕ} (hq : 2 ≤ q)
    (hdisp : ∀ t ∈ T, t * t ∈ Subgroup.centralizer (V : Set G) →
      t ∉ Subgroup.centralizer (V : Set G) →
      q ^ 2 ≤ (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V)
    (hab : ∀ A : Subgroup G, A ≤ T → (∀ a ∈ A, ∀ b ∈ A,
        a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
          a * a ∈ Subgroup.centralizer (V : Set G)) →
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ q) :
    ¬ IsFFInt G₁ V hV ∧ ¬ IsDualFFInt G₁ V hV :=
  ⟨not_ffInt_of_disp hV hG₁V hT hq hdisp hab,
    not_dualFFInt_of_disp hV hG₁V hT hq hdisp hab⟩

theorem d15_false_or_not_le' {G : Type} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}
    (h : D11Hyp G₁ G₂ T V M₂) {q : ℕ} (hq : 2 ≤ q)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hndual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1)
    (hJ : ¬ thompsonJ T ≤ pCoreOf 2 G₂)
    (hA : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      (A ⊓ pCoreOf 2 G₂).relIndex A ≤ q)
    (hsec : ∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N →
      ¬ IsCentralStep G₂ L N →
      ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 G₂ →
        q ^ 2 ≤ (centralizerMod L N A).relIndex N)
    (hV : ∀ E : Subgroup G, E ≤ pCoreOf 2 G₂ → IsElemAbelian 2 E →
      ¬ E ≤ Subgroup.centralizer (V : Set G) →
      ((Subgroup.centralizer (V : Set G)).relIndex E) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex V)
    (hsub : ∀ I : Subgroup G, G₂ ≤ Subgroup.normalizer (I : Set G) → IsElemAbelian 2 I →
      pCoreOf 2 G₂ ≤ Subgroup.centralizer (I : Set G) → ¬ G₂ ≤ Subgroup.centralizer (I : Set G) →
      ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 G₂ →
        q ^ 2 ≤ (Subgroup.centralizer (A : Set G) ⊓ I).relIndex I) :
    ¬ V ≤ pCoreOf 2 G₂ := by
  intro hVR₂
  have hV' := h.reduced.2.2.1
  have hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G) := h.reduced.2.1
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  have hR₂G₂ : R₂ ≤ G₂ := pCoreOf_le 2 G₂
  have hUG₂ : U ≤ G₂ := conjClosure_le fun g hg v hv =>
    G₂.mul_mem (G₂.mul_mem hg (hR₂G₂ (hVR₂ hv))) (G₂.inv_mem hg)
  have hD125 : IsElemAbelian 2 U → D15Proof.D125 G₂ T U := by
    intro hUe
    intro L N hstep hnc A hAT hAe hquad
    haveI : (L.subgroupOf (Subgroup.normalizer (L : Set G))).Normal :=
      Subgroup.normal_in_normalizer
    have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) :=
      isElemAbelian_secImg (A := Subgroup.normalizer (L : Set G)) (K := L) (X := N)
        (B2F.isElemAbelian_mono hstep.1.1 hUe)
    have hR₂C : R₂ ≤ centralizerMod L G₂ N := Ch3z.pCoreOf_le_centralizerMod hUG₂ hstep hE
    by_cases hAR₂ : A ≤ R₂
    · have hA_le : A ≤ centralizerMod L A N := by
        intro x hx
        have hx' : x ∈ centralizerMod L G₂ N := hR₂C (hAR₂ hx)
        exact ⟨hx, hx'.2.1, hx'.2.2⟩
      rw [Subgroup.relIndex_eq_one.mpr hA_le]
      exact Nat.one_le_iff_ne_zero.mpr (D15Proof.relIndex_ne_zero _ _)
    · have hsecA := hsec L N hstep hnc A hAT hAe hAR₂
      have hleft : (centralizerMod L A N).relIndex A ≤ (A ⊓ R₂).relIndex A := by
        refine Subgroup.relIndex_le_of_le_left ?_ (D15Proof.relIndex_ne_zero _ _)
        intro x hx
        exact ⟨hx.1, (hR₂C hx.2).2.1, (hR₂C hx.2).2.2⟩
      have hAq : (A ⊓ R₂).relIndex A ≤ q := hA A hAT hAe
      have hqle : q ≤ q ^ 2 := by nlinarith [hq]
      exact (hleft.trans hAq).trans (hqle.trans hsecA)
  have hconcl := EmptyFaithfulMultiple.d15ConclAS_of_d125' h hD125
  rcases hconcl with h1 | ⟨hq1, hff⟩ | hdual | ⟨hq2, -, hcser⟩ | ⟨-, hUe, hchief, h5, -, -⟩
  · exact h1 hVR₂
  · exact hnff hff
  · exact hndual hdual
  · obtain ⟨c, hc, hser⟩ := hcser
    exact false_of_d15Four h hnff hVR₂ hq hJ hA hsec hV hc hser
  · exact false_of_d15Five h hq hJ hA hsub hUe h5

theorem d15_false_or_not_le {G : Type} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}
    (h : D11Hyp G₁ G₂ T V M₂) {q r : ℕ} (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hJ : ¬ thompsonJ T ≤ pCoreOf 2 G₂)
    (hA : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      (A ⊓ pCoreOf 2 G₂).relIndex A ≤ q)
    (hsec : ∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N →
      ¬ IsCentralStep G₂ L N →
      ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 G₂ →
        q ^ 2 ≤ (centralizerMod L N A).relIndex N)
    (hV : ∀ E : Subgroup G, E ≤ pCoreOf 2 G₂ → IsElemAbelian 2 E →
      ¬ E ≤ Subgroup.centralizer (V : Set G) →
      ((Subgroup.centralizer (V : Set G)).relIndex E) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex V)
    (hsub : ∀ I : Subgroup G, G₂ ≤ Subgroup.normalizer (I : Set G) → IsElemAbelian 2 I →
      pCoreOf 2 G₂ ≤ Subgroup.centralizer (I : Set G) → ¬ G₂ ≤ Subgroup.centralizer (I : Set G) →
      ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 G₂ →
        q ^ 2 ≤ (Subgroup.centralizer (A : Set G) ⊓ I).relIndex I)
    (hdisp : ∀ t ∈ T, t * t ∈ Subgroup.centralizer (V : Set G) →
      t ∉ Subgroup.centralizer (V : Set G) →
      r ^ 2 ≤ (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V)
    (hab : ∀ A : Subgroup G, A ≤ T → (∀ a ∈ A, ∀ b ∈ A,
        a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
          a * a ∈ Subgroup.centralizer (V : Set G)) →
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ r) :
    ¬ V ≤ pCoreOf 2 G₂ :=
  have hff := not_isFFInt_of_disp h.reduced.2.2.1 h.reduced.2.1 h.sylow₁ hr hdisp hab
  d15_false_or_not_le' h hq hff.1 hff.2 hJ hA hsec hV hsub

end CFSG.Quasithin.Stroth
