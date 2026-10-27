module

public import CFSG.RankThree.PartOne.N143.SectionListConsumers
public import CFSG.RankThree.PartOne.N143.ExtSPEList
public import CFSG.RankThree.PartOne.N143.AutList
public import CFSG.RankThree.PartOne.S12.Sec1511Y4E
public import CFSG.RankThree.PartOne.S12.Sec1511Fam
public import CFSG.RankThree.PartOne.S12.Sec1511Model
public import CFSG.RankThree.PartOne.S12.Sec1511Tools
public import CFSG.RankThree.PartOne.S12.Sec1511Y2WPlane
public import CFSG.RankThree.PartOne.S12.Sec1511L225Psl

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.ABGLocalTools StrongP CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec1511

section Aux

variable {M : Type} [Group M] [Finite M] {p : ℕ}

theorem y2_aux_list (hSPE : ExtSPEList) (hAut : KF1511AutList) (hL : KFL225) {O : Subgroup M} [O.Normal]
    (hOcop : ¬ p ∣ Nat.card O) (hObot : pPrimeCore p (M ⧸ O) = ⊥) {M₀ P B : Subgroup M}
    (hOM₀ : O ≤ M₀) (hc : Y2Cfg p M₀ P B) (ha : Y2Aut p B) (hK : CFSG.IsKGroup M)
    (hl : IsStronglyPEmbedded p (M₀.map (QuotientGroup.mk' O)) →
      Census3.TheoremThreeList ↥(generalizedFitting (M ⧸ O))) : L225Out p M₀ P B O := by
  classical
  have hp : p.Prime := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  have hY₀ : IsStronglyPEmbedded p (M₀.map (QuotientGroup.mk' O)) :=
    spe_map_quotient hc.spe hOM₀ hOcop
  obtain ⟨hSsimple, hSnonab, hSnormal, hSC⟩ := spe_fstar hp hObot hY₀
  have hS3 : TheoremThreeListHyp ↥(generalizedFitting (M ⧸ O)) :=
    ⟨hSsimple, hSnonab, isKGroup_subgroup_quotient hK O _, hl hY₀⟩
  have hBp : IsPGroup p ↥B := by
    have := hc.Bel
    exact IsElementaryAbelian.isPGroup p ↥B
  have hPp : IsPGroup p ↥P := hc.syl.2.1
  have hPhat : IsSylowOf p (P.map (QuotientGroup.mk' O)) ⊤ := isSylowOf_map_mk' hc.syl
  have hΩ : omegaOne p (P.map (QuotientGroup.mk' O)) = B.map (QuotientGroup.mk' O) := by
    rw [omegaOne_map_mk' hPp hOcop, hc.omega]
  have hBel : IsElementaryAbelian p ↥(B.map (QuotientGroup.mk' O)) := by
    have := hc.Bel
    exact IsElementaryAbelian.map _
  have hBcard : Nat.card ↥(B.map (QuotientGroup.mk' O)) = Nat.card ↥B := card_map_mk' hBp hOcop
  have hΩel : IsElementaryAbelian p ↥(omegaOne p (P.map (QuotientGroup.mk' O))) := by
    rw [hΩ]; exact hBel
  have hΩcard : Nat.card ↥(omegaOne p (P.map (QuotientGroup.mk' O))) = p ^ 2 ∨
      Nat.card ↥(omegaOne p (P.map (QuotientGroup.mk' O))) = p ^ 3 := by
    rw [hΩ, hBcard]; exact hc.card
  have hspe := hSPE p hp hc.p5 (M ⧸ O) _ hSnormal hS3 hSC _ hY₀ _ hPhat hΩel hΩcard
  obtain ⟨hA2, hA3, hA10, hAT, hASz⟩ :=
    hAut p hp hc.p5 (M ⧸ O) _ hSnormal hS3 hSC _ hPhat hΩel hΩcard
  rw [hΩ] at hA2 hA3 hA10 hAT hASz
  have hfinal : p = 5 → (∃ q : TauCeti.PrimePower, q.p = 5 ∧ q.exponent = 2 ∧
      Census3.IsoLie ↥(generalizedFitting (M ⧸ O)) (.A 1 q)) → Nat.card ↥B = 25 →
      L225Out p M₀ P B O := by
    intro hp5 hq hB25
    subst hp5
    have hΩel' : IsElementaryAbelian 5 ↥(omegaOne 5 (P.map (QuotientGroup.mk' O))) := hΩel
    have hΩcard' : Nat.card ↥(omegaOne 5 (P.map (QuotientGroup.mk' O))) = 25 := by
      rw [hΩ, hBcard]; exact hB25
    obtain ⟨hP25, h1, h2, g, hg, hgo⟩ := hL (M ⧸ O) _ hSnormal hSC hq _ hY₀ _ hPhat hΩel' hΩcard'
    rw [hΩ] at h1 hg hgo
    have hP25' : Nat.card ↥P = 25 := by rw [← card_map_mk' hPp hOcop]; exact hP25
    have hBP : B ≤ P := by
      rw [← hc.omega]
      exact (Subgroup.closure_le _).2 fun x hx => hx.1
    refine ⟨rfl, hB25, (Subgroup.eq_of_le_of_card_ge hBP (by rw [hP25', hB25])).symm, ?_, ?_, ?_⟩
    · intro V hV hBV
      have hnorm : B.map (QuotientGroup.mk' O) ≤
          Subgroup.normalizer ((V.map (QuotientGroup.mk' O) : Subgroup (M ⧸ O)) : Set (M ⧸ O)) := by
        rintro _ ⟨b, hb, rfl⟩
        exact map_mem_normalizer _ (hBV hb)
      have hVbot := h1 (V.map (QuotientGroup.mk' O)) (hV.map _) hnorm
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hVbot
      exact hVbot
    · refine ⟨↥(M₀.map (QuotientGroup.mk' O)), inferInstance,
        (QuotientGroup.mk' O).subgroupMap M₀, h2, ?_⟩
      intro hdvd
      apply hOcop
      have hle : ((QuotientGroup.mk' O).subgroupMap M₀).ker.map M₀.subtype ≤ O := by
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : (QuotientGroup.mk' O).subgroupMap M₀ x = 1 := hx
        have hx2 : QuotientGroup.mk' O (x : M) = 1 := congrArg Subtype.val hx1
        exact (QuotientGroup.eq_one_iff _).1 hx2
      have := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective M₀.subtype_injective] at this
      exact hdvd.trans this
    · obtain ⟨n, hn, hnπ⟩ := exists_lift_normalizer hBp hOcop hg
      subst hnπ
      obtain ⟨h0, h3, hmin⟩ := hgo
      refine ⟨n, hn, h0, ?_, fun k hk0 hk3 hkc => hmin k hk0 hk3 ?_⟩
      · exact (pow_mem_centralizer_iff hBp hOcop hn 3).2 h3
      · exact (pow_mem_centralizer_iff hBp hOcop hn k).1 hkc
  rcases hspe with ⟨q, hqp, hq23, hq⟩ | ⟨hp5, hcase⟩
  · rcases hq23 with hq2 | hq3
    · obtain ⟨hcard2, g, hg, hgo⟩ := hA2 ⟨q, hqp, hq2, hq⟩
      have hBc : Nat.card ↥B = p ^ 2 := by rw [← hBcard]; exact hcard2
      obtain ⟨m, hm1, hm4, hdvd⟩ :=
        exists_dvd_lcm_of_orderModC hBp hOcop hg hgo (ha.ord4 hBc)
      have hp5 : p = 5 := arith_l2sq hp hc.p5 hm1 hm4 hdvd
      subst hp5
      exact hfinal rfl ⟨q, hqp, hq2, hq⟩ (by rw [hBc]; norm_num)
    · obtain ⟨hcard3, g, hg, hgo⟩ := hA3 ⟨q, hqp, hq3, hq⟩
      obtain ⟨m, hm1, hm6, hdvd⟩ := exists_dvd_lcm_of_orderModC hBp hOcop hg hgo ha.ord6
      exact (arith_l2cube hc.p5 hm1 hm6 hdvd).elim
  · subst hp5
    rcases hcase with hA | hT | hSz
    · obtain ⟨hc25, g, hg, hgo⟩ := hA10 rfl hA
      have hB25 : Nat.card ↥B = 5 ^ 2 := by rw [← hBcard]; exact hc25
      obtain ⟨m, hm1, hm4, hdvd⟩ := exists_dvd_lcm_of_orderModC hBp hOcop hg hgo (ha.ord4 hB25)
      exact (arith_eight hm1 (hm4.trans (by norm_num)) hdvd).elim
    · obtain ⟨hc25, F, hFc, hFN, hFne⟩ := hAT rfl hT
      have hB25 : Nat.card ↥B = 25 := by rw [← hBcard]; exact hc25
      have hlift : ∀ y ∈ F, ∃ n ∈ Subgroup.normalizer (B : Set M),
          QuotientGroup.mk' O n = y := fun y hy => exists_lift_normalizer hBp hOcop (hFN y hy)
      choose! f hf using hlift
      have hinj : Set.InjOn f ↑F := fun a ha' b hb hab => by
        rw [← (hf a ha').2, ← (hf b hb).2, hab]
      have hcard' : (F.image f).card = 48 := by rw [Finset.card_image_of_injOn hinj]; exact hFc
      have hle := ha.count hB25 (F.image f)
        (by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
          exact (hf y hy).1)
        (by
          intro x hx y hy hxy hxy'
          obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
          have hab : a ≠ b := fun h => hxy (by rw [h])
          apply hFne a ha' b hb hab
          have := map_mem_centralizer (O := O) hxy'
          simpa [map_mul, map_inv, (hf a ha').2, (hf b hb).2] using this)
      omega
    · obtain ⟨hc25, g, hg, hgo⟩ := hASz rfl hSz
      have hB25 : Nat.card ↥B = 5 ^ 2 := by rw [← hBcard]; exact hc25
      obtain ⟨m, hm1, hm4, hdvd⟩ := exists_dvd_lcm_of_orderModC hBp hOcop hg hgo (ha.ord4 hB25)
      exact (arith_five hm1 hm4 hdvd).elim

end Aux

section Gen

variable {G : Type} [Group G]

theorem lemmaY2_list [Finite G] (hSPE : ExtSPEList) (hAutK : KF1511AutList) (hL : KFL225) (hKW : KFW4Plane)
    {p : ℕ} {E N Y' P : Subgroup G} (hS : Setting p E N) (hp5 : 5 ≤ p) (hY1 : Y1Out p E N Y' P)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (hS4 : Nat.card ↥(P ⊓ E) = p ^ 2 →
      Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) ∧ Nat.card ↥E = p ^ 3)
    (hK : CFSG.IsKGroup ↥Y')
    (hrank : ∀ Y₀ : Subgroup (↥Y' ⧸ pPrimeCore p ↥Y'), IsStronglyPEmbedded p Y₀ →
      Census3.TheoremThreeList ↥(generalizedFitting (↥Y' ⧸ pPrimeCore p ↥Y'))) :
    Y2Out p N Y' P (P ⊓ E) ((pPrimeCore p ↥Y').map Y'.subtype) := by
  have hp := hS.prime
  have : Fact p.Prime := ⟨hp⟩
  have hPY : P ≤ Y' := hY1.syl.1
  have hBY : P ⊓ E ≤ Y' := inf_le_left.trans hPY
  have hcfg := y2Cfg_of_y1Out hS hp5 hY1
  have haut := y2Aut_of_weyl hKW hS hp5 hY1 hJ hW hS4
  have hOcop : ¬ p ∣ Nat.card (pPrimeCore p ↥Y') :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 pPrimeCore_coprime_card
  have hObot : pPrimeCore p (↥Y' ⧸ pPrimeCore p ↥Y') = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hOM₀ : pPrimeCore p ↥Y' ≤ (N ⊓ Y').subgroupOf Y' := hcfg.coprime _ inferInstance hOcop
  have hout := y2_aux_list hSPE hAutK hL hOcop hObot hOM₀ hcfg haut hK (fun hY₀ => hrank _ hY₀)
  have hO_le : (pPrimeCore p ↥Y').map Y'.subtype ≤ Y' := Subgroup.map_subtype_le _
  have hO_norm : ∀ y ∈ Y', ∀ o ∈ (pPrimeCore p ↥Y').map Y'.subtype,
      y * o * y⁻¹ ∈ (pPrimeCore p ↥Y').map Y'.subtype := by
    intro y hy o ho
    obtain ⟨o', ho', rfl⟩ := ho
    exact ⟨⟨y, hy⟩ * o' * ⟨y, hy⟩⁻¹, (inferInstance : (pPrimeCore p ↥Y').Normal).conj_mem o' ho' ⟨y, hy⟩, rfl⟩
  have hO_cop : ¬ p ∣ Nat.card ↥((pPrimeCore p ↥Y').map Y'.subtype) := by
    rwa [Subgroup.card_map_of_injective Y'.subtype_injective]
  have hO_N : (pPrimeCore p ↥Y').map Y'.subtype ≤ N := hY1.coprime _ hO_le hO_norm hO_cop
  have hcardB : Nat.card ↥((P ⊓ E).subgroupOf Y') = Nat.card ↥(P ⊓ E) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv
  refine ⟨hout.p5, by rw [← hcardB]; exact hout.card, ?_, hO_le, hO_norm, hO_cop, hO_N, ?_, ?_, ?_⟩
  ·
    have h := hout.PB
    rw [Subgroup.subgroupOf_inj] at h
    rw [inf_eq_left.2 hPY, inf_eq_left.2 hBY] at h
    exact h
  ·
    intro V hVY hV2 hBV
    have hV' : IsPGroup 2 ↥(V.subgroupOf Y') := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVY).symm
    have hnorm : (P ⊓ E).subgroupOf Y' ≤
        Subgroup.normalizer ((V.subgroupOf Y' : Subgroup ↥Y') : Set ↥Y') := by
      intro b hb
      have hb' : (b : G) ∈ P ⊓ E := Subgroup.mem_subgroupOf.1 hb
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact Subgroup.mem_normalizer_iff.1 (hBV hb') (x : G)
    have h := hout.two _ hV' hnorm
    intro v hv
    exact ⟨⟨v, hVY hv⟩, h (Subgroup.mem_subgroupOf.2 hv), rfl⟩
  ·
    obtain ⟨Q, _, f, hQ, hk⟩ := hout.simple5
    let e : ↥(N ⊓ Y') ≃* ↥((N ⊓ Y').subgroupOf Y') :=
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ Y' ≤ Y')).symm
    refine not_hasNonabSimpleSection (f.comp e.toMonoidHom) hQ ?_
    intro hdvd
    apply hk
    have hle : (f.comp e.toMonoidHom).ker.map e.toMonoidHom ≤ f.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have h4 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective e.injective] at h4
    exact hdvd.trans h4
  ·
    obtain ⟨n, hn, h0, h3, hmin⟩ := hout.three
    have hn' : (n : G) ∈ Subgroup.normalizer ((P ⊓ E : Subgroup G) : Set G) := by
      have := mem_normalizer_map_subtype hn
      rwa [Subgroup.map_subgroupOf_eq_of_le hBY] at this
    refine ⟨(n : G), n.2, hn', ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := Subgroup.mem_centralizer_iff.1 h3 ⟨b, hBY hb⟩ (Subgroup.mem_subgroupOf.2 hb)
      have h4 := congrArg Subtype.val this
      simpa using h4
    · intro hc
      apply hmin 1 (by norm_num) (by norm_num)
      rw [pow_one, Subgroup.mem_centralizer_iff]
      intro b hb
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hc (b : G) (Subgroup.mem_subgroupOf.1 hb)

end Gen

section Node

variable {G : Type} [Group G] [Finite G]

theorem y2_of_y1_list (hSPE : ExtSPEList) (hAut : KF1511AutList) (hL225 : KFL225) (hKW : KFW4Plane)
    (hRank : KF1511List) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152 p E A (lieGenerated p E)) {Y₀ P : Subgroup G} {n : G}
    (hnN : n ∈ lieNormalizer p E)
    (hY₀2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ Y₀ ≤ Subgroup.normalizer (S : Set G))
    (hY₀N : ¬ Y₀ ≤ lieNormalizer p E) (hS : Setting p E (lieNormalizer p E))
    (hp5 : 5 ≤ p) (hY1 : Y1Out p E (lieNormalizer p E) (conjSub n Y₀) P)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (hS4 : Nat.card ↥(P ⊓ E) = p ^ 2 →
      Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) ∧ Nat.card ↥E = p ^ 3) :
    Y2Out p (lieNormalizer p E) (conjSub n Y₀) P (P ⊓ E)
      ((pPrimeCore p ↥(conjSub n Y₀)).map (conjSub n Y₀).subtype) := by
  have h := h15.h12
  have hY'2 := two_local_conj hY₀2 n
  have hY'N : ¬ conjSub n Y₀ ≤ lieNormalizer p E := fun hle => hY₀N (le_of_conjSub_le hnN hle)
  have hKP : CFSG.IsKProper G := h.setup.2.2.1
  have : IsSimpleGroup G := h.setup.1
  have hK : CFSG.IsKGroup ↥(conjSub n Y₀) := hKP _ (ne_top_of_two_local h.setup.2.1 hY'2)
  exact lemmaY2_list hSPE hAut hL225 hKW hS hp5 hY1 hJ hW hS4 hK
    (fun Y₁ hY₁ => hRank G p A c L E h15 hF hout (conjSub n Y₀) hY'2 hY'N ⟨Y₁, hY₁⟩)

theorem node1511_of_inputsE_list
    (h154 : Node154) (h155 : Node155) (h1510 : Node1510)
    (hSPE : ExtSPEList) (hAut : KF1511AutList) (hRank : KF1511List)
    (hBTE : AUTSL.KF1511BTE) (hEI : KFEI) (hA : KF1511A) : Node1511 := by
  classical
  intro G _ _ p A c L E h15 hF hout B hBA hcases M hM
  by_contra hMN
  have h := h15.h12
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by norm_num)
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hAE : A ≤ E := h.A_le_E
  have hAcard : Nat.card ↥A = p ^ 3 := h.A_card
  have hBE : B ≤ E := hBA.trans hAE
  have hS : Setting p E (lieNormalizer p E) :=
    ⟨hp, hEel, torusNormalizer_le_lieNormalizer hp E,
      fun U hU hU1 => h1510 G p A c L E h15 hF hout U hU hU1, rank_le_three h⟩
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout hEQ hQW hQ
  have hBcard : p ^ 2 ≤ Nat.card ↥B := by
    rcases hcases with ⟨-, hle⟩ | ⟨-, hBA'⟩
    · rw [hAcard] at hle
      have h1 : p * p ^ 2 ≤ p * Nat.card ↥B := by
        calc p * p ^ 2 = p ^ 3 := by ring
          _ ≤ p * Nat.card ↥B := hle
      exact Nat.le_of_mul_le_mul_left h1 hp.pos
    · rw [hBA', hAcard]
      exact Nat.pow_le_pow_right hp.pos (by norm_num)
  have hBel : IsElementaryAbelian p ↥B := elemAbelian_of_le hEel hBE
  have hBnc : ¬ IsCyclic ↥B := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = Nat.card ↥B := orderOf_eq_card_of_forall_mem_zpowers hg
    have hexp : g ^ p = 1 := by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p ↥B) g
      exact this
    have hdvd : Nat.card ↥B ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hexp
    have hle : Nat.card ↥B ≤ p := Nat.le_of_dvd hp.pos hdvd
    have : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  have hM2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ M = Subgroup.normalizer (S : Set G) := hM.1.1
  have hMN' : ¬ M ≤ lieNormalizer p E := hMN
  have hBM : B ≤ M := fun b hb => hM.2 hb
  obtain ⟨W₀, hW⟩ := h154 G p A c L E h15 hF hout
  by_cases hEA : E = A
  ·
    have hnotfive : ¬ Outcome152Five p E A (lieGenerated p E) := by
      rintro ⟨-, -, -, -, -, -, hne, -⟩
      exact hne hEA
    have hout4 : Outcome152One p E A (lieGenerated p E) ∨ Outcome152Two p E A (lieGenerated p E) ∨
        Outcome152Three p E A (lieGenerated p E) ∨ Outcome152Four p E A (lieGenerated p E) := by
      rcases hout with h1 | h2 | h3 | h4 | h5
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr h4))
      · exact absurd h5 hnotfive
    have hEI' : E ≤ lieGenerated p E := hEI G p A c L E h15 hF hout hnotfive
    have hΩ : OmegaHyp p E := by
      intro Q hEQ hQW hQp
      have hQW' : Q ≤ torusNormalizer E := hQW
      obtain ⟨P, hP, hQP⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hQW' hQp
      have hΩP : omegaOne p P = E := by
        rcases h155 G p A c L E h15 hF hout P hP with hΩ | ⟨h5, -, -, -⟩
        · exact hΩ
        · exact absurd h5 hnotfive
      apply le_antisymm
      · calc omegaOne p Q ≤ omegaOne p P :=
              Subgroup.closure_mono (fun x hx => ⟨hQP hx.1, hx.2⟩)
          _ = E := hΩP
      · intro e he
        exact Subgroup.subset_closure ⟨hEQ he,
          elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he⟩
    obtain ⟨R₀, B₁, hR₀2, hR₀1, hY₀N, hB₁Y₀, hB₁E, hB₁nc, hfam⟩ :=
      exists_maximal_two_local hM2 hMN' hBM hBE hBnc
    have hY₀2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧
        Subgroup.normalizer (R₀ : Set G) ≤ Subgroup.normalizer (S : Set G) :=
      ⟨R₀, hR₀1, hR₀2, le_rfl⟩
    obtain ⟨n, hnN, P, hY1, -⟩ := lemmaY1 hS hJ hY₀2 hY₀N hB₁Y₀ hB₁E hB₁nc (Or.inl hΩ)
    have hS4 : Nat.card ↥(P ⊓ E) = p ^ 2 →
        Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) ∧ Nat.card ↥E = p ^ 3 :=
      fun _ => ⟨weyl154_perm_four hEA hout hW, hEA ▸ hAcard⟩
    have hY2 := y2_of_y1_list hSPE hAut L225.kfL225 kfW4Plane hRank h15 hF hout hnN hY₀2 hY₀N hS hp5 hY1 hJ hW hS4
    have hp55 : p = 5 := hY2.p5
    subst hp55
    have hY'eq : conjSub n (Subgroup.normalizer (R₀ : Set G)) =
        Subgroup.normalizer ((conjSub n R₀ : Subgroup G) : Set G) :=
      Subgroup.map_equiv_normalizer_eq R₀ (MulAut.conj n)
    have hR'2 : IsPGroup 2 ↥(conjSub n R₀) := hR₀2.map _
    have hcardR' : Nat.card ↥(conjSub n R₀) = Nat.card ↥R₀ := card_conjSub
    have hR'1 : conjSub n R₀ ≠ ⊥ := by
      intro hbot
      apply hR₀1
      have h1 : Nat.card ↥(conjSub n R₀) = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hcardR'] at h1
      exact Subgroup.card_eq_one.1 h1
    have hRn : ∀ y ∈ conjSub n (Subgroup.normalizer (R₀ : Set G)), ∀ r ∈ conjSub n R₀,
        y * r * y⁻¹ ∈ conjSub n R₀ := fun y hy r hr =>
      (Subgroup.mem_normalizer_iff.1 (hY'eq ▸ hy) r).1 hr
    have hNR : Subgroup.normalizer ((conjSub n R₀ : Subgroup G) : Set G) ≤
        conjSub n (Subgroup.normalizer (R₀ : Set G)) := hY'eq ▸ le_rfl
    have hRY : conjSub n R₀ ≤ conjSub n (Subgroup.normalizer (R₀ : Set G)) :=
      hY'eq ▸ Subgroup.le_normalizer
    have hY'N : ¬ conjSub n (Subgroup.normalizer (R₀ : Set G)) ≤ lieNormalizer 5 E :=
      fun hle => hY₀N (le_of_conjSub_le hnN hle)
    have hmax := hmax_of_family hfam inf_le_right hY1.noncyc hcardR'
    have hY3 := lemmaY3 Nat.prime_five hY1 hY'N hY2 hR'2 hRY hRn hNR hmax
    have hBY' : P ⊓ E ≤ conjSub n (Subgroup.normalizer (R₀ : Set G)) := inf_le_left.trans hY1.syl.1
    have hO2R : O2 (conjSub n (Subgroup.normalizer (R₀ : Set G))) = conjSub n R₀ :=
      hY3.maximal _ (O2_isPGroup _) (le_O2 hRY hR'2 hRn)
        (fun b hb => le_normalizer_O2 _ (hBY' hb))
    have hchar : ∀ y ∈ conjSub n (Subgroup.normalizer (R₀ : Set G)),
        (∀ r ∈ conjSub n R₀, y * r = r * y) → y ∈ conjSub n R₀ := by
      intro y hy hcomm
      have hloc : CFSG.IsPLocal 2 (conjSub n (Subgroup.normalizer (R₀ : Set G))) :=
        ⟨conjSub n R₀, hR'1, hR'2, hY'eq⟩
      have hchP := h.setup.2.2.2.1 _ hloc
      have hmem : (⟨y, hy⟩ : ↥(conjSub n (Subgroup.normalizer (R₀ : Set G)))) ∈
          Subgroup.centralizer
            ((CFSG.pCore 2 ↥(conjSub n (Subgroup.normalizer (R₀ : Set G))) : Subgroup _) : Set _) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        apply Subtype.ext
        have hzR : (z : G) ∈ conjSub n R₀ := hO2R ▸ ⟨z, hz, rfl⟩
        exact (hcomm _ hzR).symm
      have hyO2 : y ∈ O2 (conjSub n (Subgroup.normalizer (R₀ : Set G))) :=
        ⟨⟨y, hy⟩, hchP hmem, rfl⟩
      rwa [hO2R] at hyO2
    have hB1 : P ⊓ E ≠ ⊥ := fun hbot => hY1.noncyc (by rw [hbot]; infer_instance)
    have hBN : Subgroup.normalizer ((P ⊓ E : Subgroup G) : Set G) ≤ lieNormalizer 5 E :=
      hS.hN _ inf_le_right hB1
    obtain ⟨t, n', f, hmodel, ht, -⟩ := lieModel_of_outcome hout4
    have hE125 : Nat.card ↥E = 125 := by
      rw [hEA, hAcard]
      norm_num
    exact lemmaY4E hBTE rfl hS hY1 hY2 hY3 hEI' hE125 hR'2 hRn hNR hchar hBN hmodel ht
  ·
    have h5 : Outcome152Five p E A (lieGenerated p E) := Outcome152.five_of_ne hout hEA
    have hBA' : B = A := by
      rcases hcases with ⟨hEA', -⟩ | ⟨-, hBA'⟩
      · exact absurd hEA' hEA
      · exact hBA'
    have hBcard3 : Nat.card ↥B = p ^ 3 := hBA' ▸ hAcard
    have hM2' : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ M ≤ Subgroup.normalizer (S : Set G) := by
      obtain ⟨S, hS1, hS2, hMS⟩ := hM2
      exact ⟨S, hS1, hS2, hMS ▸ le_rfl⟩
    have hE1 : ∃ e ∈ E, e ≠ 1 := by
      obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (show B ≠ ⊥ from fun hbot =>
        hBnc (by rw [hbot]; infer_instance))
      exact ⟨b, hBE b.2, fun hh => hb1 (Subtype.ext hh)⟩
    have hEexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
      elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
    have hΩ : OmegaHyp p E ∨ (Nat.card ↥B = p ^ 3 ∧ KAHyp p E (lieNormalizer p E) B) := by
      by_cases hp5' : p = 5
      · exact Or.inr ⟨hBcard3, hBA' ▸ hA G p A c L E h15 hF h5 hp5'⟩
      · left
        have hp7 : 7 ≤ p := by
          by_contra hlt
          have : p = 6 := by omega
          exact absurd (this ▸ hp) (by norm_num)
        refine omegaHyp_of_centralizes hEel (fun F hF' hEF => h.E_max_global F hF' hEF) ?_
        intro g hg k hgk
        exact centralizes_of_pPower_gen hp hEexp hE1 hW (weyl154_hord6 hW) (by omega) hg hgk
    obtain ⟨n, hnN, P, hY1, hBle⟩ := lemmaY1 hS hJ hM2' hMN' hBM hBE hBnc hΩ
    have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    have hPE3 : Nat.card ↥(P ⊓ E) = p ^ 3 := by
      rcases hY1.card with h2 | h3
      · rw [hBcard3, h2] at hBle
        omega
      · exact h3
    have hS4 : Nat.card ↥(P ⊓ E) = p ^ 2 →
        Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) ∧ Nat.card ↥E = p ^ 3 := fun hh => by
      rw [hPE3] at hh
      omega
    have hY2 := y2_of_y1_list hSPE hAut L225.kfL225 kfW4Plane hRank h15 hF hout hnN hM2' hMN' hS hp5 hY1 hJ hW hS4
    have h25 := hY2.card
    have hp55 := hY2.p5
    rw [hPE3, hp55] at h25
    norm_num at h25

end Node

end CFSG.RankThree.PartOne.N143
