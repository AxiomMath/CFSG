module

public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofGen
import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofSz
import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.Blueprint CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_S szFieldAut_W)
open scoped Pointwise LinearAlgebra.Projectivization

namespace Steps166

section Model

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem false_of_fixed_S_W (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : ℙ K (Fin 4 → K)} (hx : x ∈ suzukiOmega a K)
    (h1 : suzukiSElt a K 1 0 • x = x) (h2 : suzukiWElt a K • x = x) : False := by
  rcases mem_suzukiOmega_iff.mp hx with rfl | ⟨u, v, rfl⟩
  · rw [(suzuki_ovoid_weyl_action a hK).1] at h2
    exact suzukiLine_ne_suzukiInfty 0 0 h2
  · rw [suzukiSElt_smul_suzukiLine hK, suzukiLine_eq_iff] at h1
    have h := h1.1
    exact one_ne_zero (by linear_combination h)

theorem card_suzukiU (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 := by
  have hinj : Function.Injective fun p : K × K => suzukiSElt a K p.1 p.2 := fun p q h =>
    Prod.ext (suzukiSElt_inj.mp h).1 (suzukiSElt_inj.mp h).2
  rw [← SetLike.coe_sort_coe, coe_suzukiU hK, Nat.card_range_of_injective hinj, Nat.card_prod, hK,
    sq]

theorem odd_cofactor (a : ℕ) :
    Odd ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) := by
  have h1 : Odd (2 ^ (2 * a + 1) - 1) := by
    rw [Nat.odd_iff]
    exact two_pow_odd_sub_one_mod_two a
  have h2 : Odd ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    refine Even.add_one ?_
    rw [← pow_mul]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  exact h1.mul h2

theorem card_le_of_isPGroup_two (hK : Nat.card K = 2 ^ (2 * a + 1))
    {Q : Subgroup (suzukiGroup a K)} (hQ : IsPGroup 2 Q) :
    Nat.card Q ≤ (2 ^ (2 * a + 1)) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hdvd : Nat.card Q ∣ (2 ^ (2 * a + 1)) ^ 2 *
      ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) := by
    rw [← mul_assoc, ← suzuki_order hK]
    exact Subgroup.card_subgroup_dvd_card Q
  have hcop : Nat.Coprime (Nat.card Q) ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_two_left).mpr (odd_cofactor a))
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

@[expose] noncomputable def suzukiUSylow
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : Sylow 2 (suzukiGroup a K) where
  toSubgroup := suzukiU a K
  isPGroup' := IsPGroup.of_card (n := 2 * (2 * a + 1)) (by rw [card_suzukiU hK, ← pow_mul,
    mul_comm])
  is_maximal' := fun {Q} hQ hUQ =>
    (Subgroup.eq_of_le_of_card_ge hUQ
      (by rw [card_suzukiU hK]; exact card_le_of_isPGroup_two hK hQ))
      |>.symm

theorem le_suzukiU_of_le_suzukiB (hK : Nat.card K = 2 ^ (2 * a + 1))
    {Q : Subgroup (suzukiGroup a K)} (hQ : IsPGroup 2 Q) (hQB : Q ≤ suzukiB a K) :
    Q ≤ suzukiU a K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hTcard, hTN, hUT, -, -, hBcard⟩ := suzuki_borel_structure hK
  have hBN : suzukiB a K ≤ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
    sup_le Subgroup.le_normalizer hTN
  set UB := (suzukiU a K).subgroupOf (suzukiB a K) with hUB
  have hUBn : UB.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (suzukiU_le_suzukiB a K)).mpr hBN
  have hcardq : Nat.card (↥(suzukiB a K) ⧸ UB) = 2 ^ (2 * a + 1) - 1 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup UB
    rw [hBcard, hUB, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suzukiU_le_suzukiB a K)).toEquiv,
      card_suzukiU hK, mul_comm] at h
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm
  have hodd : Odd (Nat.card (↥(suzukiB a K) ⧸ UB)) := by
    rw [hcardq, Nat.odd_iff]
    exact two_pow_odd_sub_one_mod_two a
  set QB := Q.subgroupOf (suzukiB a K) with hQBdef
  have hQB2 : IsPGroup 2 (QB.map (QuotientGroup.mk' UB)) :=
    (hQ.comap_of_injective _ (suzukiB a K).subtype_injective).map _
  have hbot : QB.map (QuotientGroup.mk' UB) = ⊥ := by
    rw [← Subgroup.card_eq_one]
    rcases hQB2.card_eq_or_dvd with h | h
    · exact h
    · exfalso
      have := h.trans (Subgroup.card_subgroup_dvd_card _)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  intro x hx
  have hxB : x ∈ suzukiB a K := hQB hx
  have h1 : QuotientGroup.mk' UB (⟨x, hxB⟩ : suzukiB a K) ∈ QB.map (QuotientGroup.mk' UB) :=
    ⟨⟨x, hxB⟩, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem eq_of_le_stabilizer (hK : Nat.card K = 2 ^ (2 * a + 1))
    (P : Sylow 2 (suzukiGroup a K)) (h : suzukiGroup a K)
    (hP : (P : Subgroup (suzukiGroup a K)) ≤
      MulAction.stabilizer (suzukiGroup a K) (h • suzukiInfty K)) :
    (P : Subgroup (suzukiGroup a K)) = (suzukiU a K).map (MulAut.conj h).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, (suzuki_ovoid_stabilizer hK).1] at hP
  set P' := (P : Subgroup (suzukiGroup a K)).map (MulAut.conj h⁻¹).toMonoidHom with hP'
  have hP'B : P' ≤ suzukiB a K := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hP hy
    simpa [MulAut.conj_apply, mul_assoc] using hb
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map _
  have hP'U : P' ≤ suzukiU a K := le_suzukiU_of_le_suzukiB hK hP'2 hP'B
  have hcard : Nat.card P' = Nat.card (suzukiU a K) := by
    rw [hP', Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective,
      Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (suzukiUSylow hK)]
    rfl
  have heq : P' = suzukiU a K := Subgroup.eq_of_le_of_card_ge hP'U hcard.ge
  rw [← heq, hP', Subgroup.map_map]
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem conj_smul_eq_map {G : Type*} [Group G] (h : G) (S : Subgroup G) :
    MulAut.conj h • S = S.map (MulAut.conj h).toMonoidHom := by
  ext y
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  rfl

theorem sup_fixedSubgroupOf_sylow_eq_top (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {α : MulAut (suzukiGroup a K)} (hα : α ^ 3 = 1)
    (P : Sylow 2 (suzukiGroup a K)) :
    fixedSubgroupOf α ⊔ (P : Subgroup (suzukiGroup a K)) = ⊤ := by
  classical
  have hsimple : IsSimpleGroup (suzukiGroup a K) := (suzuki_simple ha hK).2.2
  by_cases hinn : KFacts.IsInnerAut α
  ·
    obtain ⟨g, rfl⟩ := hinn
    have hg3 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow]; exact hα
    have hnp : ¬ (Nat.card (suzukiGroup a K)).Prime := by
      rw [suzuki_order hK]
      intro hp
      have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rcases Nat.prime_mul_iff.mp hp with ⟨-, h2⟩ | ⟨-, h2⟩
      · have : 0 < (2 ^ (2 * a + 1)) ^ 2 := by positivity
        omega
      · have h3 : 1 < 2 ^ (2 * a + 1) - 1 := by omega
        have h4 : 1 < (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
        nlinarith
    have hcen : Subgroup.center (suzukiGroup a K) = ⊥ :=
      (Sec13.isPerfect_center_of_isSimpleGroup hsimple hnp).2
    have hg3c : g ^ 3 ∈ Subgroup.center (suzukiGroup a K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun σ : MulAut (suzukiGroup a K) => σ y) hg3
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * g ^ 3 = (g ^ 3 * y * (g ^ 3)⁻¹) * g ^ 3 := by rw [h]
        _ = g ^ 3 * y := by group
    rw [hcen, Subgroup.mem_bot] at hg3c
    have hg1 : g = 1 := by
      have hord : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3c
      have hord2 : orderOf g ∣ Nat.card (suzukiGroup a K) := orderOf_dvd_natCard g
      rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd (h ▸ hord2) (KFacts.not_three_dvd_card_suzukiGroup hK)
    subst hg1
    rw [map_one]
    exact eq_top_iff.mpr fun x _ => Subgroup.mem_sup_left (show (1 : MulAut _) x = x from rfl)
  ·
    obtain ⟨φ, ⟨σ, rfl⟩, -, d, ⟨g, rfl⟩, hαeq⟩ :=
      KFacts.isField_sz_of_pow_three_eq_one ha hK hα hinn
    set H := fixedSubgroupOf α ⊔ (P : Subgroup (suzukiGroup a K)) with hH
    have hfix : ∀ y, szFieldAut a K σ y = y → g * y * g⁻¹ ∈ fixedSubgroupOf α := by
      intro y hy
      rw [mem_fixedSubgroupOf, hαeq]
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply,
        MulAut.conj_symm_apply]
      rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group, hy]
    have hS10 : szFieldAut a K σ (suzukiSElt a K 1 0) = suzukiSElt a K 1 0 := by
      rw [szFieldAut_S, map_one, map_zero]
    have hW : szFieldAut a K σ (suzukiWElt a K) = suzukiWElt a K := szFieldAut_W σ
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (suzukiGroup a K) (suzukiUSylow hK) P
    set x := h • suzukiInfty K with hx
    have hΩ : ∀ k : suzukiGroup a K, ∀ z ∈ suzukiOmega a K, k • z ∈ suzukiOmega a K :=
      fun k z hz => suzuki_smul_mem_suzukiOmega hK k hz
    have hxΩ : x ∈ suzukiOmega a K := hΩ h _ (suzukiInfty_mem_suzukiOmega a K)
    have hPmem : ∀ p, p ∈ (P : Subgroup (suzukiGroup a K)) ↔
        ∃ u ∈ suzukiU a K, h * u * h⁻¹ = p := by
      intro p
      rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      rfl
    have hPtrans : ∀ z ∈ suzukiOmega a K, z ≠ x → ∀ z' ∈ suzukiOmega a K, z' ≠ x →
        ∃ p ∈ (P : Subgroup (suzukiGroup a K)), p • z = z' := by
      intro z hz hzx z' hz' hz'x
      have hw : h⁻¹ • z ∈ suzukiOmega a K \ {suzukiInfty K} :=
        ⟨hΩ _ _ hz, fun he => hzx (by rw [hx, ← he, smul_inv_smul])⟩
      have hw' : h⁻¹ • z' ∈ suzukiOmega a K \ {suzukiInfty K} :=
        ⟨hΩ _ _ hz', fun he => hz'x (by rw [hx, ← he, smul_inv_smul])⟩
      obtain ⟨⟨u, hu⟩, hux, -⟩ := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1 _ hw _ hw'
      refine ⟨h * u * h⁻¹, (hPmem _).mpr ⟨u, hu, rfl⟩, ?_⟩
      change u • (h⁻¹ • z) = h⁻¹ • z' at hux
      rw [mul_smul, mul_smul, hux, smul_inv_smul]
    obtain ⟨y, hyC, hyx⟩ : ∃ y ∈ fixedSubgroupOf α, y • x ≠ x := by
      by_contra hcon
      push Not at hcon
      have h1 := hcon _ (hfix _ hS10)
      have h2 := hcon _ (hfix _ hW)
      have hconj : ∀ s : suzukiGroup a K, (g * s * g⁻¹) • x = x → s • g⁻¹ • x = g⁻¹ • x := by
        intro s hs
        have e : g⁻¹ * (g * s * g⁻¹) = s * g⁻¹ := by group
        calc s • g⁻¹ • x = (s * g⁻¹) • x := (mul_smul _ _ _).symm
          _ = (g⁻¹ * (g * s * g⁻¹)) • x := by rw [e]
          _ = g⁻¹ • (g * s * g⁻¹) • x := mul_smul _ _ _
          _ = g⁻¹ • x := by rw [hs]
      exact false_of_fixed_S_W hK (hΩ g⁻¹ x hxΩ) (hconj _ h1) (hconj _ h2)
    have hHtrans : ∀ z ∈ suzukiOmega a K, ∃ k ∈ H, k • x = z := by
      intro z hz
      by_cases hzx : z = x
      · exact ⟨1, one_mem _, by rw [one_smul, hzx]⟩
      · obtain ⟨p, hp, hpz⟩ := hPtrans (y • x) (hΩ _ _ hxΩ) hyx z hz hzx
        exact ⟨p * y, mul_mem (Subgroup.mem_sup_right hp) (Subgroup.mem_sup_left hyC),
          by rw [mul_smul, hpz]⟩
    have hsyl : ∀ Q : Sylow 2 (suzukiGroup a K), (Q : Subgroup (suzukiGroup a K)) ≤ H := by
      intro Q
      obtain ⟨h', hh'⟩ := MulAction.exists_smul_eq (suzukiGroup a K) (suzukiUSylow hK) Q
      obtain ⟨k, hkH, hkx⟩ :=
        hHtrans (h' • suzukiInfty K) (hΩ _ _ (suzukiInfty_mem_suzukiOmega a K))
      have hkP : ((k • P : Sylow 2 (suzukiGroup a K)) : Subgroup (suzukiGroup a K)) ≤
          MulAction.stabilizer (suzukiGroup a K) (h' • suzukiInfty K) := by
        intro z hz
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hz
        obtain ⟨p, hp, rfl⟩ := hz
        obtain ⟨u, hu, rfl⟩ := (hPmem p).mp hp
        rw [MulAction.mem_stabilizer_iff, ← hkx, hx]
        have hu8 : u • suzukiInfty K = suzukiInfty K :=
          suzukiB_le_stabilizer hK (suzukiU_le_suzukiB a K hu)
        have e : k * (h * u * h⁻¹) * k⁻¹ * (k * h) = k * h * u := by group
        calc (k * (h * u * h⁻¹) * k⁻¹) • k • h • suzukiInfty K
            = (k * (h * u * h⁻¹) * k⁻¹ * (k * h)) • suzukiInfty K := by
              rw [mul_smul (k * (h * u * h⁻¹) * k⁻¹) (k * h), mul_smul k h]
          _ = (k * h * u) • suzukiInfty K := by rw [e]
          _ = k • h • suzukiInfty K := by rw [mul_smul, hu8, mul_smul]
      have hQeq : (Q : Subgroup (suzukiGroup a K)) =
          ((k • P : Sylow 2 (suzukiGroup a K)) : Subgroup (suzukiGroup a K)) := by
        rw [eq_of_le_stabilizer hK _ h' hkP, ← hh', Sylow.coe_subgroup_smul, conj_smul_eq_map]
        rfl
      rw [hQeq, Sylow.coe_subgroup_smul]
      intro z hz
      rw [Subgroup.mem_smul_pointwise_iff_exists] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      change k * p * k⁻¹ ∈ H
      exact mul_mem (mul_mem hkH (Subgroup.mem_sup_right hp)) (inv_mem hkH)
    have hNC : Subgroup.normalClosure (suzukiU a K : Set (suzukiGroup a K)) ≤ H := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro z hz
      obtain ⟨u, hu, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
      obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
      refine hsyl (c • suzukiUSylow hK) ?_
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨u, hu, rfl⟩
    have hNn : (Subgroup.normalClosure (suzukiU a K : Set (suzukiGroup a K))).Normal :=
      Subgroup.normalClosure_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure (suzukiU a K : Set (suzukiGroup a K))) with h0 | h1
    · exfalso
      have hmem : suzukiSElt a K 1 0 ∈
          Subgroup.normalClosure (suzukiU a K : Set (suzukiGroup a K)) :=
        Subgroup.subset_normalClosure (suzukiSElt_mem_suzukiU a K 1 0)
      rw [h0, Subgroup.mem_bot, ← suzukiSElt_zero_zero hK, suzukiSElt_inj] at hmem
      exact one_ne_zero hmem.1
    · exact eq_top_iff.mpr (h1 ▸ hNC)

end Model

end Steps166

theorem kSzGen166 : KSzGen166 := by
  intro T _ n hSz α hα S
  obtain ⟨-, a, ha, F, _, _, hn, hF, ⟨e⟩⟩ := hSz
  rw [hn] at hF
  have : Finite T := Finite.of_equiv _ e.symm.toEquiv
  set α' := MulAut.congr e α with hα'def
  have hα' : α' ^ 3 = 1 := by rw [hα'def, ← map_pow, hα, map_one]
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  set S' : Sylow 2 (suzukiGroup a F) := Sylow.mapSurjective he S with hS'
  have h := Steps166.sup_fixedSubgroupOf_sylow_eq_top ha hF hα' S'
  have hfixmap : (fixedSubgroupOf α).map e.toMonoidHom = fixedSubgroupOf α' := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change α' (e z) = e z
      rw [hα'def, MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact congrArg e hz
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      change α (e.symm y) = e.symm y
      have hy' : α' y = y := hy
      rw [hα'def, MulAut.congr_apply] at hy'
      simp only [MulEquiv.trans_apply] at hy'
      have := congrArg e.symm hy'
      rwa [MulEquiv.symm_apply_apply] at this
  have hmap : (fixedSubgroupOf α ⊔ (S : Subgroup T)).map e.toMonoidHom =
      fixedSubgroupOf α' ⊔ (S' : Subgroup (suzukiGroup a F)) := by
    rw [Subgroup.map_sup, hfixmap, hS', Sylow.coe_mapSurjective]
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ fixedSubgroupOf α' ⊔ (S' : Subgroup (suzukiGroup a F)) :=
    h ▸ Subgroup.mem_top _
  rw [← hmap] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  rwa [e.injective hzx] at hz

theorem step166Gen_of' (h146 : Sec14.Item146S14)
    (hΔ : Step166DeltaSz) :
    Step166Gen :=
  step166Gen_of h146 hΔ kSzGen166

theorem step166GenHJ_of' (h146 : Sec14.Item146S14)
    (hΔ : Step166DeltaSzHJ) : Step166GenHJ :=
  step166GenHJ_of h146 hΔ kSzGen166

end CFSG.RankThree.PartTwo.Sec16
