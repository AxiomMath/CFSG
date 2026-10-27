module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIWChoiceFixed

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_mem_of_sq_mem_of_odd_relIndex {N H : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hodd : Odd (N.relIndex H))
    {x : G} (hxH : x ∈ H) (hx2 : x * x ∈ N) : x ∈ N := by
  let NK : Subgroup H := N.subgroupOf H
  haveI : NK.Normal := hN
  let q : H ⧸ NK := QuotientGroup.mk' NK ⟨x, hxH⟩
  by_contra hxN
  have hq : q ≠ 1 := by
    intro hq1
    apply hxN
    have hmem : (⟨x, hxH⟩ : H) ∈ NK := (QuotientGroup.eq_one_iff (⟨x, hxH⟩ : H)).mp hq1
    exact Subgroup.mem_subgroupOf.mp hmem
  have hq2 : q ^ 2 = 1 := by
    have hval : q ^ 2 = QuotientGroup.mk' NK ((⟨x, hxH⟩ : H) ^ 2) := (map_pow (QuotientGroup.mk' NK) _ 2).symm
    rw [hval]
    exact (QuotientGroup.eq_one_iff ((⟨x, hxH⟩ : H) ^ 2)).mpr
      (Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using hx2))
  have hdvd2 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
  have hdvdH : orderOf q ∣ Nat.card (H ⧸ NK) := orderOf_dvd_natCard q
  have hoddq : Odd (Nat.card (H ⧸ NK)) := by
    change Odd NK.index
    rwa [show NK.index = N.relIndex H from rfl]
  have hcop : Nat.Coprime 2 (Nat.card (H ⧸ NK)) := Nat.coprime_two_left.mpr hoddq
  have h1 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdH
  exact hq (orderOf_eq_one_iff.mp h1)

theorem nine3_odd_relIndex_pCoreOf_sup_X (hc : Nine3Choice V T A K S X p g x) :
    Odd ((pCoreOf 2 K).relIndex (pCoreOf 2 K ⊔ X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨hc.core.hyp.base.prime⟩
  let R := pCoreOf 2 K
  have hRX : R ⊓ X = ⊥ := by
    exact (IsPGroup.disjoint_of_ne 2 p (Ne.symm hc.core.hyp.base.odd) R X
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
      hc.core.hyp.base.sylowP.isPGroup).eq_bot
  have hRXnorm : X ≤ Subgroup.normalizer (R : Set G) :=
    hc.core.hyp.base.sylowP.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hcard : Nat.card ↥(R ⊔ X) = Nat.card ↥R * Nat.card ↥X :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      R X hRXnorm (disjoint_iff.mpr hRX)
  have h := Subgroup.relIndex_mul_card (H := R) (K := R ⊔ X)
  rw [inf_eq_left.mpr le_sup_left, hcard, hc.core.card,
    mul_comm (Nat.card ↥R) p] at h
  have hrel : R.relIndex (R ⊔ X) = p :=
    Nat.mul_right_cancel (Nat.card_pos (α := ↥R)) h
  rw [hrel]
  exact hc.core.hyp.base.prime.odd_of_ne_two hc.core.hyp.base.odd

theorem nine3_commutator_map_injective (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) {a : G} (ha : a ∈ A) (haR : a ∉ pCoreOf 2 K) :
    ∀ α ∈ A ⊓ pCoreOf 2 K, α ≠ 1 → ⁅α, x⁻¹ * a * x⁆ ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨hc.core.hyp.base.prime⟩
  let R := pCoreOf 2 K
  let u : G := x⁻¹ * a * x
  have ha2 : a * a = 1 := by
    have h := (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1
      hc.core.A_mem_nineOmegaIn.1).2 a ha
    simpa [pow_two] using h
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have hxK : x ∈ K := hc.core.hyp.base.sylowP.le hc.x_mem
  have huK : u ∈ K := by
    rw [show u = x⁻¹ * a * x from rfl]
    exact K.mul_mem (K.mul_mem (K.inv_mem hxK) (hc.core.S_le_K (hc.core.A_mem_nineOmegaIn.2 ha))) hxK
  have hu2 : u * u = 1 := by
    rw [show u = x⁻¹ * a * x from rfl]
    calc (x⁻¹ * a * x) * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
      _ = 1 := by rw [ha2]; group
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  have hx1 : x ≠ 1 := by
    have hXcard : Nat.card X = p := hc.core.card
    have hxord : orderOf x = p := by
      rw [hc.x_gen, Nat.card_zpowers] at hXcard
      exact hXcard
    rintro rfl
    rw [orderOf_one] at hxord
    exact hc.core.hyp.base.prime.ne_one hxord.symm
  intro α hα hα1 hcomm
  have hαA : α ∈ A := hα.1
  have hαR : α ∈ R := hα.2
  have hcent : u ∈ Subgroup.centralizer ({α} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm
  have huN : u ∈ Subgroup.normalizer (A : Set G) := by
    have h := centralizer_le_normalizer_conj hc.core.hyp7.2.2 g (hc.V_g ▸ hαA) hα1 hcent
    rwa [hc.V_g] at h
  have hdA : u * a * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp huN a).mp ha
  have hdR : u * a * u⁻¹ ∉ R := by
    intro hdR
    have hmem : u⁻¹ * (u * a * u⁻¹) * u ∈ R := by
      simpa using (Nine3Core.mem_pCoreOf_conj_iff K (K.inv_mem huK)).mp hdR
    apply haR
    have h_eq : u⁻¹ * (u * a * u⁻¹) * u = a := by
      calc u⁻¹ * (u * a * u⁻¹) * u = (u⁻¹ * u) * a * (u⁻¹ * u) := by group
        _ = a := by rw [inv_mul_cancel, one_mul, mul_one]
    rwa [h_eq] at hmem
  have hrel : (A ⊓ R).relIndex A = 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact nine_two_relIndex hc.core.hyp7 hc.core.rk_gt hc.core.hyp hc.core.A_mem_nineOmegaIn
  have hdaR : (u * a * u⁻¹) * a ∈ R := by
    have hdA' : (⟨u * a * u⁻¹, hdA⟩ : ↥A) ∉ (A ⊓ R).subgroupOf A := by
      intro hmem
      exact hdR (Subgroup.mem_subgroupOf.mp hmem).2
    have haA' : (⟨a, ha⟩ : ↥A) ∉ (A ⊓ R).subgroupOf A := by
      intro hmem
      exact haR (Subgroup.mem_subgroupOf.mp hmem).2
    have hmemA : (⟨u * a * u⁻¹, hdA⟩ * ⟨a, ha⟩ : ↥A) ∈ (A ⊓ R).subgroupOf A := by
      rw [Subgroup.mul_mem_iff_of_index_two hrel]
      exact iff_of_false hdA' haA'
    exact (Subgroup.mem_subgroupOf.mp hmemA).2
  have hua_sq : (u * a) * (u * a) ∈ R := by
    have h_eq : (u * a) * (u * a) = (u * a * u⁻¹) * a := by
      rw [hu_inv]
      group
    rwa [h_eq]
  have haK : a ∈ K := hc.core.S_le_K (hc.core.A_mem_nineOmegaIn.2 ha)
  have hsupK : R ⊔ X ≤ K :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hc.core.hyp.base.sylowP.le
  have hKnormRX : K ≤ Subgroup.normalizer ((R ⊔ X : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsupK).mp
      (TwoPTwo.normal_pCoreOf_sup hc.core.hyp.base.toTwoPTwo)
  have hle : ⁅K, R ⊔ X⁆ ≤ R ⊔ X :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hKnormRX
  have hxinvRX : x⁻¹ ∈ R ⊔ X := Subgroup.mem_sup_right (X.inv_mem hc.x_mem)
  have hmem : ⁅a, x⁻¹⁆ ∈ R ⊔ X :=
    hle (Subgroup.commutator_mem_commutator haK hxinvRX)
  have hcomm_eq : ⁅a, x⁻¹⁆ = a * u := by
    rw [commutatorElement_def, show u = x⁻¹ * a * x from rfl]
    rw [inv_eq_of_mul_eq_one_left ha2]
    group
  have hua_RX : u * a ∈ R ⊔ X := by
    have h_eq : u * a = (⁅a, x⁻¹⁆)⁻¹ := by
      rw [hcomm_eq, mul_inv_rev, hu_inv, inv_eq_of_mul_eq_one_left ha2]
    rw [h_eq]
    exact Subgroup.inv_mem _ hmem
  have hRnormK : K ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  haveI : (R.subgroupOf (R ⊔ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (hsupK.trans hRnormK)
  have huaR : u * a ∈ R :=
    nine3_mem_of_sq_mem_of_odd_relIndex le_sup_left inferInstance
      (nine3_odd_relIndex_pCoreOf_sup_X hc) hua_RX hua_sq
  have hxaR : ⁅x, a⁆ ∈ R := by
    have h1 : x * (u * a) * x⁻¹ ∈ R :=
      (Nine3Core.mem_pCoreOf_conj_iff K hxK).mp huaR
    have h_eq : ⁅x, a⁆ = (x * (u * a) * x⁻¹)⁻¹ := by
      rw [commutatorElement_def, show u = x⁻¹ * a * x from rfl]
      simp [inv_eq_of_mul_eq_one_left ha2]
      group
    rw [h_eq]
    exact Subgroup.inv_mem _ h1
  have hcommA : ∀ b ∈ A, ⁅x, b⁆ ∈ R := by
    intro b hb
    by_cases hbR : b ∈ R
    · have hxb : x * b * x⁻¹ ∈ R :=
        (Nine3Core.mem_pCoreOf_conj_iff K hxK).mp hbR
      rw [commutatorElement_def]
      exact R.mul_mem hxb (R.inv_mem hbR)
    · have hbaR : b * a ∈ R := by
        have hbA' : (⟨b, hb⟩ : ↥A) ∉ (A ⊓ R).subgroupOf A := by
          intro hmem
          exact hbR (Subgroup.mem_subgroupOf.mp hmem).2
        have haA' : (⟨a, ha⟩ : ↥A) ∉ (A ⊓ R).subgroupOf A := by
          intro hmem
          exact haR (Subgroup.mem_subgroupOf.mp hmem).2
        have hmemA : (⟨b, hb⟩ * ⟨a, ha⟩ : ↥A) ∈ (A ⊓ R).subgroupOf A := by
          rw [Subgroup.mul_mem_iff_of_index_two hrel]
          exact iff_of_false hbA' haA'
        exact (Subgroup.mem_subgroupOf.mp hmemA).2
      have h1 : ⁅x, b * a⁆ ∈ R := by
        have hxba : x * (b * a) * x⁻¹ ∈ R :=
          (Nine3Core.mem_pCoreOf_conj_iff K hxK).mp hbaR
        rw [commutatorElement_def]
        exact R.mul_mem hxba (R.inv_mem hbaR)
      have h3 : (b * a) * ⁅x, a⁆ * (b * a)⁻¹ ∈ R :=
        R.mul_mem (R.mul_mem hbaR hxaR) (R.inv_mem hbaR)
      have hb_eq : b = (b * a) * a := by
        calc b = b * 1 := by simp
          _ = b * (a * a) := by rw [ha2]
          _ = (b * a) * a := by group
      rw [hb_eq, commutatorElement_mul_right_eq_mul_conj]
      simpa [mul_assoc] using R.mul_mem h1 h3
  have hxR : x ∈ R :=
    nine_two_centralizer hc.core.hyp7 hc.core.rk_gt hc.core.hyp
      hc.core.A_mem_nineOmegaIn (Subgroup.mem_sup_right hc.x_mem) hcommA
  have hxbot : x ∈ X ⊓ R := ⟨hc.x_mem, hxR⟩
  rw [TwoPTwo.sylowP_inf_pCoreOf hc.core.hyp.base.toTwoPTwo] at hxbot
  exact hx1 (Subgroup.mem_bot.mp hxbot)

theorem nine3_centralizer_A_eq_sup (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) :
    nineI V K ⊓ Subgroup.centralizer (A : Set G) =
      (A ⊓ pCoreOf 2 K) ⊔ (nineI V K ⊓ Subgroup.centralizer (A : Set G) ⊓
        Subgroup.centralizer (conjSubgroup A x : Set G)) := by
  classical
  haveI : IsMulCommutative ↥(nineI V K) := hI.abelian.1
  let R := pCoreOf 2 K
  let I := nineI V K
  let A₀ := A ⊓ R
  let U := conjSubgroup A x
  let U₀ := U ⊓ R
  have hxK : x ∈ K := hc.core.hyp.base.sylowP.le hc.x_mem
  have hAΩ : A ∈ omegaIn V K (nineE V K) := nine3_A_mem_omega hc
  have hUΩ : U ∈ omegaIn V K (nineE V K) := conjSubgroup_mem_omegaIn hAΩ hxK
  have hcommU : ⁅I, U⁆ = U₀ := nine3_comm_of_mem_omega hc hI hUΩ
  have hAab : ∀ x y : G, x ∈ A → y ∈ A → x * y = y * x :=
    fun x y hx hy => CFSG.Open.IsElemAbelian.comm
      (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1 hc.core.A_mem_nineOmegaIn.1) hx hy
  have hAexp : ∀ x : G, x ∈ A → x * x = 1 := by
    intro x hx
    have h := (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1
      hc.core.A_mem_nineOmegaIn.1).2 x hx
    simpa [pow_two] using h
  have hUexp : ∀ x : G, x ∈ U → x * x = 1 := by
    intro x hx
    have h := (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1 hUΩ.1).2 x hx
    simpa [pow_two] using h
  have hIexp : ∀ x : G, x ∈ I → x * x = 1 := by
    intro x hx
    have h := hI.abelian.2 x hx
    simpa [pow_two] using h
  obtain ⟨a, ha, haR⟩ := nine3_exists_a_not_mem_pCore hc
  have ha2 : a * a = 1 := hAexp a ha
  let u : G := x⁻¹ * a * x
  have huU : u ∈ U := by
    rw [show U = conjSubgroup A x from rfl, CFSG.Quasithin.mem_conjSubgroup_iff]
    rw [show u = x⁻¹ * a * x from rfl]
    have h : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
    rwa [h]
  have huK : u ∈ K := by
    rw [show u = x⁻¹ * a * x from rfl]
    exact K.mul_mem (K.mul_mem (K.inv_mem hxK)
      (hc.core.S_le_K (hc.core.A_mem_nineOmegaIn.2 ha))) hxK
  have huR : u ∉ R := by
    intro huR
    apply haR
    have hmem : x * u * x⁻¹ ∈ R := (Nine3Core.mem_pCoreOf_conj_iff K hxK).mp huR
    have h_eq : x * u * x⁻¹ = a := by
      rw [show u = x⁻¹ * a * x from rfl]
      group
    rwa [h_eq] at hmem
  have hU0I : U₀ ≤ I := le_iSup₂_of_le U hUΩ le_rfl
  have hA0I : A₀ ≤ I := by
    rw [show A₀ = A ⊓ R from rfl, ← Nine3Core.nineI_inf_eq hc.core hc.core.A_mem_nineOmegaIn]
    exact inf_le_right
  have hφ_mul : ∀ α β : ↥I, ⁅(α : G) * (β : G), u⁆ =
      ⁅(α : G), u⁆ * ⁅(β : G), u⁆ := by
    intro α β
    have hαmem : ⁅(α : G), u⁆ ∈ I := hU0I (by
      have h := Subgroup.commutator_mem_commutator α.2 huU
      rwa [hcommU] at h)
    have hβmem : ⁅(β : G), u⁆ ∈ I := hU0I (by
      have h := Subgroup.commutator_mem_commutator β.2 huU
      rwa [hcommU] at h)
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hconj : (α : G) * ⁅(β : G), u⁆ * (α : G)⁻¹ = ⁅(β : G), u⁆ := by
      calc (α : G) * ⁅(β : G), u⁆ * (α : G)⁻¹ =
          ⁅(β : G), u⁆ * (α : G) * (α : G)⁻¹ := by
            rw [CFSG.Open.IsElemAbelian.comm hI.abelian α.2 hβmem]
        _ = ⁅(β : G), u⁆ := by group
    rw [hconj]
    exact CFSG.Open.IsElemAbelian.comm hI.abelian hβmem hαmem
  have hφ_mem : ∀ α : ↥I, ⁅(α : G), u⁆ ∈ U₀ := by
    intro α
    have h := Subgroup.commutator_mem_commutator α.2 huU
    rwa [hcommU] at h
  let φ : ↥A₀ → ↥U₀ := fun α => ⟨⁅(α : G), u⁆, hφ_mem ⟨(α : G), hA0I α.2⟩⟩
  have hφ_inj : Function.Injective φ := by
    intro α β hEq
    by_contra hne
    have hval : ⁅(α : G), u⁆ = ⁅(β : G), u⁆ := congrArg Subtype.val hEq
    have hγ1 : (α : G) * (β : G)⁻¹ ≠ 1 := by
      intro h
      apply hne
      have h' : (α : G) = (β : G) := by
        calc (α : G) = (α : G) * (β : G)⁻¹ * (β : G) := by group
          _ = (β : G) := by rw [h, one_mul]
      exact Subtype.ext h'
    have hγA : (α : G) * (β : G)⁻¹ ∈ A₀ := A₀.mul_mem α.2 (A₀.inv_mem β.2)
    have hγcomm : ⁅(α : G) * (β : G)⁻¹, u⁆ = 1 := by
      have hβinv : (β : G)⁻¹ ∈ I := I.inv_mem (hA0I β.2)
      have hmul := hφ_mul ⟨(α : G), hA0I α.2⟩ ⟨(β : G)⁻¹, hβinv⟩
      have hβ2 : (β : G) * (β : G) = 1 := hAexp (β : G) β.2.1
      have hβinv_eq : (β : G)⁻¹ = (β : G) := inv_eq_of_mul_eq_one_left hβ2
      have hβu2 : ⁅(β : G), u⁆ * ⁅(β : G), u⁆ = 1 :=
        hUexp ⁅(β : G), u⁆ (hφ_mem ⟨(β : G), hA0I β.2⟩).1
      have h1 : ⁅(α : G), u⁆ * ⁅(β : G), u⁆ = 1 := by
        rw [hval]
        exact hβu2
      calc ⁅(α : G) * (β : G)⁻¹, u⁆ = ⁅(α : G), u⁆ * ⁅(β : G)⁻¹, u⁆ := hmul
        _ = ⁅(α : G), u⁆ * ⁅(β : G), u⁆ := by rw [hβinv_eq]
        _ = 1 := h1
    exact nine3_commutator_map_injective hc hI ha haR
      ((α : G) * (β : G)⁻¹) hγA hγ1 hγcomm
  have hU0_eq : U₀ = conjSubgroup A₀ x := by
    rw [show U₀ = U ⊓ R from rfl, show U = conjSubgroup A x from rfl,
      show R = conjSubgroup R x from (Nine3Core.conjSubgroup_pCoreOf K hxK).symm,
      ← E3.conjSubgroup_inf]
  have hcard : Nat.card ↥A₀ = Nat.card ↥U₀ := by
    rw [hU0_eq]
    exact (card_conjSubgroup' x A₀).symm
  have hφ_surj : Function.Surjective φ := by
    haveI : Fintype ↥A₀ := Fintype.ofFinite _
    haveI : Fintype ↥U₀ := Fintype.ofFinite _
    have hcardF : Fintype.card ↥A₀ = Fintype.card ↥U₀ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hcard
    exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcardF)).mp hφ_inj
  have hforward : I ⊓ Subgroup.centralizer (A : Set G) ≤
      A₀ ⊔ (I ⊓ Subgroup.centralizer (A : Set G) ⊓
        Subgroup.centralizer (U : Set G)) := by
    rintro y ⟨hyI, hyC⟩
    have hβ : ⁅y, u⁆ ∈ U₀ := hφ_mem ⟨y, hyI⟩
    obtain ⟨α, hφα⟩ := hφ_surj ⟨⁅y, u⁆, hβ⟩
    have hα2 : (α : G) * (α : G) = 1 := hAexp (α : G) α.2.1
    have hαinv : (α : G)⁻¹ = (α : G) := inv_eq_of_mul_eq_one_left hα2
    have hval : ⁅(α : G), u⁆ = ⁅y, u⁆ := congrArg Subtype.val hφα
    let c' : G := y * (α : G)⁻¹
    have hc'I : c' ∈ I := I.mul_mem hyI (I.inv_mem (hA0I α.2))
    have hc'C : c' ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hyb : b * y = y * b := (Subgroup.mem_centralizer_iff.mp hyC) b hb
      have hαb : b * (α : G) = (α : G) * b := (hAab (α : G) b α.2.1 hb).symm
      calc b * (y * (α : G)⁻¹) = b * (y * (α : G)) := by rw [hαinv]
        _ = (b * y) * (α : G) := by group
        _ = (y * b) * (α : G) := by rw [hyb]
        _ = y * (b * (α : G)) := by group
        _ = y * ((α : G) * b) := by rw [hαb]
        _ = (y * (α : G)) * b := by group
        _ = (y * (α : G)⁻¹) * b := by rw [hαinv]
    have hc'u : ⁅c', u⁆ = 1 := by
      have hαI : (α : G) ∈ I := hA0I α.2
      have hc'_eq : c' = y * (α : G) := by
        rw [show c' = y * (α : G)⁻¹ from rfl, hαinv]
      rw [hc'_eq, hφ_mul ⟨y, hyI⟩ ⟨(α : G), hαI⟩, hval]
      exact hUexp ⁅y, u⁆ (hβ).1
    have hc'2 : c' * c' = 1 := by
      have hc'_eq : c' = y * (α : G) := by
        rw [show c' = y * (α : G)⁻¹ from rfl, hαinv]
      rw [hc'_eq]
      have hy2 : y * y = 1 := hIexp y hyI
      have hαy : (α : G) * y = y * (α : G) :=
        CFSG.Open.IsElemAbelian.comm hI.abelian (hA0I α.2) hyI
      calc (y * (α : G)) * (y * (α : G)) = y * ((α : G) * y) * (α : G) := by group
        _ = y * (y * (α : G)) * (α : G) := by rw [hαy]
        _ = (y * y) * ((α : G) * (α : G)) := by group
        _ = 1 := by rw [hy2, hα2, mul_one]
    have hc'U : c' ∈ Subgroup.centralizer (U : Set G) := by
      have hUle : U ≤ Subgroup.centralizer ({c'} : Set G) := by
        rw [show U = U₀ ⊔ Subgroup.zpowers u from nine3_eq_sup_inf_zpowers hc hUΩ huU huR]
        apply sup_le
        · intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst hw
          exact CFSG.Open.IsElemAbelian.comm hI.abelian hc'I (hU0I hz)
        · refine Subgroup.zpowers_le.mpr ?_
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst hw
          exact commutatorElement_eq_one_iff_mul_comm.mp hc'u
      have hUle' : U ≤ Subgroup.centralizer ((Subgroup.zpowers c' : Subgroup G) : Set G) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rcases nine3_mem_zpowers_involution hc'2 hw with rfl | rfl
        · simp
        · exact Subgroup.mem_centralizer_iff.mp (hUle hz) c' (Set.mem_singleton c')
      exact (Subgroup.le_centralizer_iff.mp hUle') (Subgroup.mem_zpowers c')
    have hc'_mem : c' ∈ I ⊓ Subgroup.centralizer (A : Set G) ⊓
        Subgroup.centralizer (U : Set G) := ⟨⟨hc'I, hc'C⟩, hc'U⟩
    have hy_eq : y = c' * (α : G) := by
      rw [show c' = y * (α : G)⁻¹ from rfl, hαinv]
      rw [mul_assoc, hα2, mul_one]
    rw [hy_eq]
    have hsup : c' * (α : G) ∈ (I ⊓ Subgroup.centralizer (A : Set G) ⊓
        Subgroup.centralizer (U : Set G)) ⊔ A₀ := Subgroup.mul_mem_sup hc'_mem α.2
    rw [sup_comm] at hsup
    exact hsup
  apply le_antisymm hforward
  apply sup_le
  · intro z hz
    refine ⟨hA0I hz, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun b hb => (hAab z b hz.1 hb).symm)
  · rintro z ⟨⟨hzI, hzC⟩, hzU⟩
    exact ⟨hzI, hzC⟩

end CFSG.LocalAnalysis.WeakClosure81
