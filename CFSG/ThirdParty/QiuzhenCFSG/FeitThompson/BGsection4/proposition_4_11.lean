module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_10
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_9
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_b

namespace CFSG
end CFSG
open CFSG

open scoped FixedPoints IsMulCommutative commutatorElement

/-! # Infrastructure for Proposition 4.11 from BG Section 4 -/

universe u

section Main

open scoped FixedPoints

private theorem CFSG.natCard_quotient_zpowers_pow_eq_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p G)] [Nontrivial G] {g : G}
    (hg : Subgroup.zpowers g = ⊤) :
    Nat.card (G ⧸ Subgroup.zpowers (g ^ p)) = p := by
  have hg_order : orderOf g = Nat.card G := by
    simpa using orderOf_eq_card_of_zpowers_eq_top hg
  obtain ⟨n, hn_pos, hGcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := G) (hG := Fact.out)).mp inferInstance
  have hp_dvd_order : p ∣ orderOf g := by
    rw [hg_order, hGcard]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn_pos)
  have hgpow_order : orderOf (g ^ p) = orderOf g / p :=
    orderOf_pow_of_dvd (x := g) (n := p) (by exact (Fact.out : Nat.Prime p).ne_zero) hp_dvd_order
  have hcard_pow : Nat.card (Subgroup.zpowers (g ^ p)) = orderOf g / p := by
    rw [Nat.card_zpowers, hgpow_order]
  have hmul :
      Nat.card (G ⧸ Subgroup.zpowers (g ^ p)) * (orderOf g / p) = orderOf g := by
    calc
      Nat.card (G ⧸ Subgroup.zpowers (g ^ p)) * (orderOf g / p)
          = Nat.card (G ⧸ Subgroup.zpowers (g ^ p)) * Nat.card (Subgroup.zpowers (g ^ p)) := by
              rw [hcard_pow]
      _ = Nat.card G := by
            simpa using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G)
                (s := Subgroup.zpowers (g ^ p))).symm
      _ = orderOf g := hg_order.symm
  rcases hp_dvd_order with ⟨m, hm⟩
  have hm_ne_zero : m ≠ 0 := by
    intro hm_zero
    have hzero : orderOf g = 0 := by simp [hm, hm_zero]
    exact (Nat.ne_of_gt (orderOf_pos g)) hzero
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne_zero
  have hdiv_pos : 0 < orderOf g / p := by
    rw [hm]
    simpa [Nat.mul_comm] using
      (show 0 < m * p / p from by
        rw [Nat.mul_div_cancel m ((Fact.out : Nat.Prime p).pos)]
        exact hm_pos)
  apply Nat.eq_of_mul_eq_mul_right hdiv_pos
  calc
    Nat.card (G ⧸ Subgroup.zpowers (g ^ p)) * (orderOf g / p) = orderOf g := hmul
    _ = (orderOf g / p) * p := by
      rw [hm, Nat.mul_div_right m ((Fact.out : Nat.Prime p).pos), Nat.mul_comm]
    _ = p * (orderOf g / p) := by rw [Nat.mul_comm]

public theorem CFSG.normal_of_derivedSubgroup_le
    {G : Type*} [Group G] (N : Subgroup G) (hder : derivedSubgroup G ≤ N) :
    N.Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  have hcomm : ⁅g, n⁆ ∈ derivedSubgroup G := by
    simpa only [derivedSubgroup, derivedSeries_one, _root_.commutator_def] using
      (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
        (by simp) (by simp))
  have hconj_eq : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]
    group
  rw [hconj_eq]
  exact N.mul_mem (hder hcomm) hn

private theorem CFSG.exists_maximal_cyclic_subgroup_containing
    {G : Type*} [Group G] [Finite G] (E : Subgroup G) (hEcyc : IsCyclic E) :
    ∃ A : Subgroup G,
      E ≤ A ∧ IsCyclic A ∧
        ∀ B : Subgroup G, E ≤ B → IsCyclic B → A ≤ B → B = A := by
  classical
  let s : Set (Subgroup G) := {A | E ≤ A ∧ IsCyclic A}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := ⟨E, le_rfl, hEcyc⟩
  obtain ⟨A, hAmax⟩ := hsfin.exists_maximal hsne
  refine ⟨A, hAmax.1.1, hAmax.1.2, ?_⟩
  intro B hEB hBcyc hAB
  have hBmem : B ∈ s := ⟨hEB, hBcyc⟩
  exact le_antisymm (hAmax.2 hBmem hAB) hAB

private theorem CFSG.mho_one_le_frattini_local
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] :
    mho p 1 G ≤ frattini G := by
  rw [frattini_eq_closure_commutator_union_powers (R := G) (p := p), mho]
  refine (Subgroup.closure_le (K := Subgroup.closure (((_root_.commutator G : Subgroup G) : Set G) ∪
    Set.range fun x : G => x ^ p))).2 ?_
  rintro _ ⟨x, rfl⟩
  exact Subgroup.subset_closure (Or.inr ⟨x, by simp [pow_one]⟩)

private theorem CFSG.mho_one_map_subtype_mono
    {G : Type*} [Group G] {p : ℕ} {D H : Subgroup G} (hDH : D ≤ H) :
    (mho p 1 D).map D.subtype ≤ (mho p 1 H).map H.subtype := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  rw [mho] at hy
  change (y : G) ∈ (mho p 1 H).map H.subtype
  refine Subgroup.closure_induction (k := Set.range fun z : D => z ^ (p ^ 1)) (x := y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, rfl⟩
    have hzH : ((⟨(z : G), hDH z.2⟩ : H) ^ (p ^ 1)) ∈ mho p 1 H := by
      rw [mho]
      exact Subgroup.subset_closure ⟨⟨(z : G), hDH z.2⟩, rfl⟩
    simpa using Subgroup.mem_map_of_mem H.subtype hzH
  · simp
  · intro a b _ _ ha hb
    exact ((mho p 1 H).map H.subtype).mul_mem ha hb
  · intro a _ ha
    exact ((mho p 1 H).map H.subtype).inv_mem ha

private theorem CFSG.mho_one_map_subtype_normal_of_normal
    {G : Type*} [Group G] {p : ℕ} (N : Subgroup G) [N.Normal] :
    ((mho p 1 N).map N.subtype).Normal := by
  rw [mho, MonoidHom.map_closure]
  let S : Set G := N.subtype '' Set.range fun x : N => x ^ (p ^ 1)
  refine Subgroup.Normal.mk ?_
  intro x hx g
  change g * x * g⁻¹ ∈ Subgroup.closure S
  refine
    Subgroup.closure_induction (k := S) (x := x)
      (p := fun z _hz => g * z * g⁻¹ ∈ Subgroup.closure S)
      (mem := ?_) (one := by simp) (mul := ?_) (inv := ?_) hx
  · intro y hy
    rcases hy with ⟨u, ⟨z, rfl⟩, rfl⟩
    let z' : N := ⟨g * (z : G) * g⁻¹, (inferInstance : N.Normal).conj_mem (z : G) z.2 g⟩
    have hz' : z' ^ (p ^ 1) ∈ mho p 1 N := by
      rw [mho]
      exact Subgroup.subset_closure ⟨z', rfl⟩
    have hz'map' : (((z' ^ (p ^ 1) : N) : G)) ∈ (mho p 1 N).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hz'
    have hz'map : (((z' ^ (p ^ 1) : N) : G)) ∈ Subgroup.closure S := by
      simpa [mho, S, MonoidHom.map_closure] using hz'map'
    have hconj_pow :
        g * (((z ^ (p ^ 1) : N) : G)) * g⁻¹ = (((z' ^ (p ^ 1) : N) : G)) := by
      simp [z']
    change g * (((z ^ (p ^ 1) : N) : G)) * g⁻¹ ∈ Subgroup.closure S
    rw [hconj_pow]
    exact hz'map
  · intro a b _ _ ha hb
    simpa [mul_assoc] using (Subgroup.closure S).mul_mem ha hb
  · intro a _ ha
    simpa [mul_assoc] using (Subgroup.closure S).inv_mem ha

private theorem CFSG.exists_zpowers_sup_eq_comap_of_cyclic_subgroup_quotient
    {R : Type*} [Group R] {T : Subgroup R} [T.Normal]
    (Abar : Subgroup (R ⧸ T)) (hAbar_cyc : IsCyclic Abar) :
    ∃ a : R, Abar.comap (QuotientGroup.mk' T) = T ⊔ Subgroup.zpowers a := by
  let q : R →* R ⧸ T := QuotientGroup.mk' T
  obtain ⟨abar, habar_top⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := Abar)).1 hAbar_cyc
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective T (abar : R ⧸ T)
  let H : Subgroup R := T ⊔ Subgroup.zpowers a
  have hH_le : H ≤ Abar.comap q := by
    refine sup_le ?_ ?_
    · intro x hxT
      change q x ∈ Abar
      have hx_one : q x = 1 := (QuotientGroup.eq_one_iff (N := T) (x := x)).2 hxT
      simp [hx_one]
    · exact (Subgroup.zpowers_le).2 (by simp [q, ha])
  have hmap_le : H.map q ≤ Abar :=
    (Subgroup.map_le_iff_le_comap).2 hH_le
  have hAbar_le : Abar ≤ H.map q := by
    intro y hyA
    have hytop : (⟨y, hyA⟩ : Abar) ∈ (⊤ : Subgroup Abar) := by simp
    have hyzpow : (⟨y, hyA⟩ : Abar) ∈ Subgroup.zpowers abar := by
      simp [habar_top]
    rcases Subgroup.mem_zpowers_iff.mp hyzpow with ⟨n, hn⟩
    have hy_eq : q (a ^ n) = y := by
      calc
        q (a ^ n) = q a ^ n := by simp [q]
        _ = (abar : R ⧸ T) ^ n := by rw [ha]
        _ = y := by simpa using congrArg Subtype.val hn
    rw [← hy_eq]
    exact Subgroup.mem_map_of_mem q (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers a n))
  have hmap_eq : H.map q = Abar := le_antisymm hmap_le hAbar_le
  refine ⟨a, ?_⟩
  calc
    Abar.comap q = (H.map q).comap q := by rw [hmap_eq]
    _ = H ⊔ q.ker := Subgroup.comap_map_eq (f := q) (H := H)
    _ = H := by
      apply sup_eq_left.2
      simp [H, q, QuotientGroup.ker_mk']

private theorem CFSG.exists_zpowers_sup_eq_top_of_cyclic_quotient
    {R : Type*} [Group R] {N : Subgroup R} [N.Normal]
    (hcyc : IsCyclic (R ⧸ N)) :
    ∃ b : R, N ⊔ Subgroup.zpowers b = ⊤ := by
  let q : R →* R ⧸ N := QuotientGroup.mk' N
  obtain ⟨x, hx_top⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := R ⧸ N)).1 hcyc
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective N x
  let H : Subgroup R := N ⊔ Subgroup.zpowers b
  have hx_mem : x ∈ H.map q := by
    simpa [q, hb] using
      (Subgroup.mem_map_of_mem q (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) :
        q b ∈ H.map q)
  have hmap_top : H.map q = ⊤ := by
    apply eq_top_iff.2
    intro y hy
    have hyzpow : y ∈ Subgroup.zpowers x := by
      simp [hx_top]
    rcases Subgroup.mem_zpowers_iff.mp hyzpow with ⟨n, rfl⟩
    have hxpow_eq : q (b ^ n) = x ^ n := by
      calc
        q (b ^ n) = q b ^ n := by simp [q]
        _ = x ^ n := by rw [hb]
    rw [← hxpow_eq]
    exact Subgroup.mem_map_of_mem q (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers b n))
  refine ⟨b, ?_⟩
  calc
    H = H ⊔ q.ker := by
      symm
      apply sup_eq_left.2
      simp [H, q, QuotientGroup.ker_mk']
    _ = Subgroup.comap q (H.map q) := by
      simpa using (Subgroup.comap_map_eq (f := q) (H := H)).symm
    _ = ⊤ := by simp [hmap_top]

public theorem CFSG.proposition_4_11_aux
    {p : ℕ} [Fact p.Prime] (hpgt : 3 < p) :
    ∀ n : ℕ,
      ∀ (R : Type*) [Group R] [Finite R] [Fact (IsPGroup p R)],
        Nat.card R = n →
        Nat.card (omega₁ (G := R) (p := p)) ≤ p ^ 2 →
        IsMetacyclic R := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih R _ _ _ hcardR hOmega
  classical
  have hpodd : p ≠ 2 := by omega
  by_cases hRcomm : IsMulCommutative R
  · letI : IsMulCommutative R := hRcomm
    have hΩquot :
        Nat.card (omega₁ (G := R ⧸ frattini R) (p := p)) ≤ p ^ 2 :=
      lemma_4_9 (R := R) (p := p) hpgt hOmega (frattini R) inferInstance
    have hquot_elem : IsElementaryAbelian p (R ⧸ frattini R) :=
      isElementaryAbelian_quotient_frattini (R := R) (p := p)
    letI : IsElementaryAbelian p (R ⧸ frattini R) := hquot_elem
    have hΩquot_top : omega₁ (G := R ⧸ frattini R) (p := p) = ⊤ := by
      apply omega₁_eq_top_of_forall_pow_eq_one
      intro x
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p (R ⧸ frattini R)) x
    have hquot_card : Nat.card (R ⧸ frattini R) ≤ p ^ 2 := by
      calc
        Nat.card (R ⧸ frattini R) = Nat.card (⊤ : Subgroup (R ⧸ frattini R)) := by
          exact
            (Nat.card_congr
              (Subgroup.topEquiv : (⊤ : Subgroup (R ⧸ frattini R)) ≃* (R ⧸ frattini R))).symm
        _ = Nat.card (omega₁ (G := R ⧸ frattini R) (p := p)) := by
          rw [hΩquot_top]
        _ ≤ p ^ 2 := hΩquot
    have hcardQ :
        Nat.card (R ⧸ frattini R) =
          p ^ Module.finrank (ZMod p) (Additive (R ⧸ frattini R)) := by
      calc
        Nat.card (R ⧸ frattini R) = Nat.card (Additive (R ⧸ frattini R)) :=
          Nat.card_congr Additive.ofMul
        _ = p ^ Module.finrank (ZMod p) (Additive (R ⧸ frattini R)) := by
          simpa only [Nat.card_zmod] using
            (Module.natCard_eq_pow_finrank
              (K := ZMod p) (V := Additive (R ⧸ frattini R)))
    have hquot_finrank_le_two : Module.finrank (ZMod p) (Additive (R ⧸ frattini R)) ≤ 2 := by
      have hpow_le : p ^ Module.finrank (ZMod p) (Additive (R ⧸ frattini R)) ≤ p ^ 2 := by
        rw [← hcardQ]
        exact hquot_card
      exact (Nat.pow_le_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hpow_le
    have hgen_quot_le_two : generatorRank (R ⧸ frattini R) ≤ 2 := by
      exact
        (generatorRank_le_finrank_of_elementaryAbelian (p := p) (R ⧸ frattini R)).trans
          hquot_finrank_le_two
    have hgenR_le_two : generatorRank R ≤ 2 :=
      (generatorRank_le_generatorRank_quotient_frattini (p := p) R).trans hgen_quot_le_two
    exact isMetacyclic_of_generatorRank_le_two_of_commutative R hgenR_le_two
  · let D : Subgroup R := derivedSubgroup R
    have hD_ne_bot : D ≠ ⊥ := by
      intro hD_bot
      have hcomm_bot : _root_.commutator R = ⊥ := by
        simpa only [D, derivedSubgroup, derivedSeries_one] using hD_bot
      have hcent :
          (⊤ : Subgroup R) ≤ Subgroup.centralizer ((⊤ : Subgroup R) : Set R) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer
          (H₁ := (⊤ : Subgroup R)) (H₂ := (⊤ : Subgroup R))).1 hcomm_bot
      apply hRcomm
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha_cent : a ∈ Subgroup.centralizer ((⊤ : Subgroup R) : Set R) := hcent (by simp)
      simpa using ((Subgroup.mem_centralizer_iff.mp ha_cent) b (by simp)).symm
    let M : Subgroup R := (mho p 1 D).map D.subtype
    have hM_le_D : M ≤ D := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.2
    have hM_norm : M.Normal := mho_one_map_subtype_normal_of_normal (p := p) D
    letI : M.Normal := hM_norm
    by_cases hM_bot : M = ⊥
    · obtain ⟨T, hTnorm, hT_le_D, hT_card, hT_central⟩ :=
        exists_central_normal_subgroup_card_eq_prime_of_nontrivial_normal
          (G := R) (p := p) D hD_ne_bot
      letI : T.Normal := hTnorm
      have hquot_card : Nat.card R = Nat.card (R ⧸ T) * p := by
        calc
          Nat.card R = Nat.card (R ⧸ T) * Nat.card T := by
            simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := R) (s := T))
          _ = Nat.card (R ⧸ T) * p := by rw [hT_card]
      have hquot_lt : Nat.card (R ⧸ T) < n := by
        rw [← hcardR, hquot_card]
        simpa [one_mul] using
          (Nat.mul_lt_mul_of_pos_left ((Fact.out : Nat.Prime p).one_lt)
            (Nat.card_pos (α := R ⧸ T)))
      letI : Fact (IsPGroup p (R ⧸ T)) := ⟨(Fact.out : IsPGroup p R).to_quotient T⟩
      have hOmega_quot :
          Nat.card (omega₁ (G := R ⧸ T) (p := p)) ≤ p ^ 2 :=
        lemma_4_9 (R := R) (p := p) hpgt hOmega T hTnorm
      have hmeta_quot : IsMetacyclic (R ⧸ T) :=
        ih (Nat.card (R ⧸ T)) hquot_lt (R ⧸ T) rfl hOmega_quot
      have hquot_not_cyclic : ¬ IsCyclic (R ⧸ T) := by
        intro hquot_cyc
        apply hRcomm
        refine ⟨⟨fun a b => ?_⟩⟩
        have hker_le_center :
            (QuotientGroup.mk' T : R →* R ⧸ T).ker ≤ Subgroup.center R := by
          simpa [QuotientGroup.ker_mk'] using hT_central
        exact ((QuotientGroup.mk' T).isMulCommutative_of_isCyclic_of_ker_le_center
          hker_le_center).is_comm.comm a b
      obtain ⟨Abar, hAbar_norm, hAbar_cyc, hAquot_cyc⟩ := hmeta_quot
      letI : Abar.Normal := hAbar_norm
      obtain ⟨a, haH⟩ :=
        exists_zpowers_sup_eq_comap_of_cyclic_subgroup_quotient (T := T) Abar hAbar_cyc
      let H : Subgroup R := T ⊔ Subgroup.zpowers a
      have hH_eq : H = Abar.comap (QuotientGroup.mk' T) := by
        symm
        exact haH
      have hH_norm : H.Normal := by
        rw [hH_eq]
        exact hAbar_norm.comap (QuotientGroup.mk' T)
      letI : H.Normal := hH_norm
      have hT_le_H : T ≤ H := by
        exact le_sup_left
      have hRquotH_cyc : IsCyclic (R ⧸ H) := by
        let qT : R →* R ⧸ T := QuotientGroup.mk' T
        have hHmap_eq : H.map qT = Abar := by
          calc
            H.map qT = (Abar.comap qT).map qT := by rw [hH_eq]
            _ = Abar := by
              simpa using
                (Subgroup.map_comap_eq_self_of_surjective (f := qT)
                  (h := QuotientGroup.mk'_surjective T) Abar)
        let e0 : (R ⧸ T) ⧸ H.map qT ≃* R ⧸ H :=
          QuotientGroup.quotientQuotientEquivQuotient (N := T) (M := H) hT_le_H
        let e1 : (R ⧸ T) ⧸ Abar ≃* (R ⧸ T) ⧸ H.map qT :=
          (QuotientGroup.quotientMulEquivOfEq hHmap_eq).symm
        exact (e1.trans e0).isCyclic.1 hAquot_cyc
      obtain ⟨b, hH_sup_b⟩ := exists_zpowers_sup_eq_top_of_cyclic_quotient (N := H) hRquotH_cyc
      let Tsub : Subgroup H := T.subgroupOf H
      letI : Tsub.Normal := Subgroup.Normal.subgroupOf (G := R) (hH := hTnorm) H
      have hTsub_center : Tsub ≤ Subgroup.center H := by
        intro x hx
        have hxT : ((x : H) : R) ∈ T := by
          simpa [Tsub, Subgroup.mem_subgroupOf] using hx
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp (hT_central hxT)) y.1
      have hTsub_sup : Tsub ⊔ (Subgroup.zpowers a).subgroupOf H = ⊤ := by
        rw [← Subgroup.subgroupOf_sup (A := T) (A' := Subgroup.zpowers a) (B := H)
          le_sup_left le_sup_right]
        simp [H]
      have hza_sub_cyc : IsCyclic ((Subgroup.zpowers a).subgroupOf H) := by
        exact (Subgroup.subgroupOfEquivOfLe (H := Subgroup.zpowers a) (K := H) le_sup_right).isCyclic.2
          inferInstance
      have hHquotT_cyc : IsCyclic (H ⧸ Tsub) :=
        quotient_isCyclic_of_sup_cyclic_right (R := H) (R₁ := Tsub)
          (R₂ := (Subgroup.zpowers a).subgroupOf H) hTsub_sup hza_sub_cyc
      have hH_comm : IsMulCommutative H := by
        refine ⟨⟨fun x y => ?_⟩⟩
        have hkerTsub_le_center :
            (QuotientGroup.mk' Tsub : H →* H ⧸ Tsub).ker ≤ Subgroup.center H := by
          simpa [QuotientGroup.ker_mk'] using hTsub_center
        exact ((QuotientGroup.mk' Tsub).isMulCommutative_of_isCyclic_of_ker_le_center
          hkerTsub_le_center).is_comm.comm x y
      letI : IsMulCommutative H := hH_comm
      have hmhoD_bot : mho p 1 D = ⊥ := by
        exact
          (Subgroup.map_eq_bot_iff_of_injective (H := mho p 1 D) (f := D.subtype)
            D.subtype_injective).1 hM_bot
      have hD_pow : ∀ x : D, x ^ p = 1 := by
        intro x
        have hxpow_mem : x ^ p ∈ mho p 1 D := by
          rw [mho]
          exact Subgroup.subset_closure ⟨x, by simp [pow_one]⟩
        have hxpow_bot : x ^ p ∈ (⊥ : Subgroup D) := by
          simpa [hmhoD_bot] using hxpow_mem
        simpa using hxpow_bot
      have hD_le_omega : D ≤ omega₁ (G := R) (p := p) := by
        intro x hx
        change x ∈ Subgroup.closure {y : R | y ^ (p ^ 1) = 1}
        refine Subgroup.subset_closure ?_
        have hxpow : (⟨x, hx⟩ : D) ^ p = 1 := hD_pow ⟨x, hx⟩
        simpa [pow_one] using congrArg Subtype.val hxpow
      have hD_le_H : D ≤ H := by
        letI : IsMulCommutative (Subgroup.zpowers b) := inferInstance
        have hcomm_le : _root_.commutator R ≤ H :=
          Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
            (N := H) (H := Subgroup.zpowers b) hH_sup_b inferInstance
        simpa only [D, derivedSubgroup, derivedSeries_one] using hcomm_le
      let qT : R →* R ⧸ T := QuotientGroup.mk' T
      have hHmap_eq : H.map qT = Abar := by
        calc
          H.map qT = (Abar.comap qT).map qT := by rw [hH_eq]
          _ = Abar := by
            simpa using
              (Subgroup.map_comap_eq_self_of_surjective (f := qT)
                (h := QuotientGroup.mk'_surjective T) Abar)
      have hAbar_eq_zpow : Abar = Subgroup.zpowers (qT a) := by
        calc
          Abar = H.map qT := hHmap_eq.symm
          _ = (T ⊔ Subgroup.zpowers a).map qT := by rfl
          _ = T.map qT ⊔ (Subgroup.zpowers a).map qT := Subgroup.map_sup _ _ _
          _ = ⊥ ⊔ Subgroup.zpowers (qT a) := by
            simp [qT, MonoidHom.map_zpowers]
          _ = Subgroup.zpowers (qT a) := by simp
      have hAbar_ne_bot : Abar ≠ ⊥ := by
        intro hAbar_bot
        have hcyc_quot_bot : IsCyclic ((R ⧸ T) ⧸ (⊥ : Subgroup (R ⧸ T))) := by
          cases hAbar_bot
          simpa using hAquot_cyc
        have hcyc : IsCyclic (R ⧸ T) := by
          exact (QuotientGroup.quotientBot (G := R ⧸ T)).isCyclic.1 hcyc_quot_bot
        exact hquot_not_cyclic hcyc
      let A1 : Subgroup (R ⧸ T) := Subgroup.zpowers ((qT a) ^ p)
      have hA1_normal : A1.Normal := by
        refine Subgroup.Normal.mk ?_
        intro x hx g
        rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
        have hconj_gen_mem : g * ((qT a) ^ p) * g⁻¹ ∈ A1 := by
          have hconj_a_mem : g * qT a * g⁻¹ ∈ Subgroup.zpowers (qT a) := by
            rw [← hAbar_eq_zpow]
            exact hAbar_norm.conj_mem (qT a) (by rw [hAbar_eq_zpow]; exact Subgroup.mem_zpowers (qT a)) g
          rcases Subgroup.mem_zpowers_iff.mp hconj_a_mem with ⟨m, hm⟩
          rw [show g * ((qT a) ^ p) * g⁻¹ = (g * qT a * g⁻¹) ^ p by simp]
          rw [← hm]
          convert (Subgroup.zpow_mem_zpowers ((qT a) ^ p) m : ((qT a) ^ p) ^ m ∈ A1) using 1
          rw [show (qT a ^ m) ^ p = qT a ^ (m * p) by rw [← zpow_natCast, zpow_mul]]
          rw [show ((qT a) ^ p) ^ m = qT a ^ ((p : ℤ) * m) by simp [zpow_mul]]
          simp [mul_comm]
        rw [show g * ((((qT a) ^ p) ^ n)) * g⁻¹ = (g * ((qT a) ^ p) * g⁻¹) ^ n by simp]
        exact A1.zpow_mem hconj_gen_mem n
      letI : A1.Normal := hA1_normal
      let Acyc : Subgroup (R ⧸ T) := Subgroup.zpowers (qT a)
      have hAcyc_normal : Acyc.Normal := by
        change (Subgroup.zpowers (qT a)).Normal
        rw [← hAbar_eq_zpow]
        exact hAbar_norm
      letI : Acyc.Normal := hAcyc_normal
      letI : Nontrivial Acyc :=
        (Subgroup.nontrivial_iff_ne_bot Acyc).2 (by simpa [Acyc, hAbar_eq_zpow] using hAbar_ne_bot)
      let q1 : R ⧸ T →* (R ⧸ T) ⧸ A1 := QuotientGroup.mk' A1
      let qA : Acyc →* Acyc.map q1 := q1.subgroupMap Acyc
      have hqA_surj : Function.Surjective qA := MonoidHom.subgroupMap_surjective q1 Acyc
      have hqA_range_top : qA.range = ⊤ := by
        ext y
        constructor
        · intro _hy
          simp
        · intro _hy
          rcases hqA_surj y with ⟨x, rfl⟩
          exact ⟨x, rfl⟩
      have hqA_ker : qA.ker = A1.subgroupOf Acyc := by
        simpa [qA, q1, Acyc] using (Subgroup.ker_subgroupMap (f := q1) (H := Acyc))
      have hAcyc_quot_card :
          Nat.card (Acyc ⧸ qA.ker) = Nat.card (Acyc.map q1) := by
        have hcard := Nat.card_congr (QuotientGroup.quotientKerEquivRange qA).toEquiv
        simpa [hqA_range_top] using hcard
      let qa : Acyc := ⟨qT a, by simp [Acyc]⟩
      have hqa_top : Subgroup.zpowers qa = ⊤ := by
        apply (Subgroup.eq_top_iff' (H := Subgroup.zpowers qa)).2
        intro x
        rcases Subgroup.mem_zpowers_iff.mp x.2 with ⟨n, hn⟩
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa [qa] using hn)⟩
      letI : Fact (IsPGroup p Acyc) := ⟨(Fact.out : IsPGroup p (R ⧸ T)).to_subgroup Acyc⟩
      have hqA_ker_zpow : qA.ker = Subgroup.zpowers (qa ^ p) := by
        rw [hqA_ker]
        ext x
        constructor
        · intro hx
          change (x : R ⧸ T) ∈ A1 at hx
          change (x : R ⧸ T) ∈ Subgroup.zpowers ((qT a) ^ p) at hx
          rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, hn⟩
          exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa [qa] using hn)⟩
        · intro hx
          change (x : R ⧸ T) ∈ A1
          change (x : R ⧸ T) ∈ Subgroup.zpowers ((qT a) ^ p)
          rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, hn⟩
          exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
            simpa [qa] using congrArg Subtype.val hn⟩
      have hAcyc_quot_card_p : Nat.card (Acyc ⧸ qA.ker) = p := by
        rw [hqA_ker_zpow]
        exact natCard_quotient_zpowers_pow_eq_prime (G := Acyc) (p := p) (g := qa) hqa_top
      have hAcyc_map_card : Nat.card (Acyc.map q1) = p := by
        rw [← hAcyc_quot_card]
        exact hAcyc_quot_card_p
      letI : Fact (IsPGroup p ((R ⧸ T) ⧸ A1)) :=
        ⟨((Fact.out : IsPGroup p (R ⧸ T)).to_quotient A1)⟩
      letI : (Acyc.map q1).Normal := by infer_instance
      have hAcyc_map_center : Acyc.map q1 ≤ Subgroup.center ((R ⧸ T) ⧸ A1) :=
        normal_subgroup_card_eq_prime_le_center
          (G := (R ⧸ T) ⧸ A1) (p := p) (N := Acyc.map q1) hAcyc_map_card
      have hq1qa_center : q1 (qT a) ∈ Subgroup.center ((R ⧸ T) ⧸ A1) := by
        exact hAcyc_map_center (Subgroup.mem_map_of_mem q1 (by simp [Acyc]))
      have hq1comm : q1 (qT a) * q1 (qT b) = q1 (qT b) * q1 (qT a) :=
        ((Subgroup.mem_center_iff.mp hq1qa_center) (q1 (qT b))).symm
      let c : R := ⁅a, b⁆
      have hqc_mem_A1 : qT c ∈ A1 := by
        have hqc_eq : q1 (qT c) = ⁅q1 (qT a), q1 (qT b)⁆ := by
          simp [c, q1, qT, map_commutatorElement]
        have hqc_one : q1 (qT c) = 1 := by
          rw [hqc_eq]
          exact (commutatorElement_eq_one_iff_mul_comm).2 hq1comm
        exact (QuotientGroup.eq_one_iff (N := A1) (x := qT c)).1 hqc_one
      have hA1_eq_map : A1 = (Subgroup.zpowers (a ^ p)).map qT := by
        change Subgroup.zpowers ((qT a) ^ p) = (Subgroup.zpowers (a ^ p)).map qT
        have hqT_pow : qT (a ^ p) = (qT a) ^ p := by simp [qT]
        rw [← hqT_pow]
        exact (MonoidHom.map_zpowers qT (a ^ p)).symm
      have hc_in_Ap : c ∈ T ⊔ Subgroup.zpowers (a ^ p) := by
        have hc_comap : c ∈ ((Subgroup.zpowers (a ^ p)).map qT).comap qT := by
          rw [← hA1_eq_map]
          exact hqc_mem_A1
        have hcomap_eq :
            ((Subgroup.zpowers (a ^ p)).map qT).comap qT =
              Subgroup.zpowers (a ^ p) ⊔ qT.ker := by
          simpa using (Subgroup.comap_map_eq (f := qT) (H := Subgroup.zpowers (a ^ p)))
        have hc_mem : c ∈ Subgroup.zpowers (a ^ p) ⊔ qT.ker := by
          rw [← hcomap_eq]
          exact hc_comap
        simpa [qT, QuotientGroup.ker_mk', sup_comm] using hc_mem
      have hc_in_D : c ∈ D := by
        simpa [c, D, derivedSubgroup, derivedSeries_one] using
          (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup R)) (H₂ := (⊤ : Subgroup R))
            (by simp) (by simp))
      have hc_pow : c ^ p = 1 := by
        simpa using congrArg Subtype.val (hD_pow ⟨c, hc_in_D⟩)
      have ha_in_H : a ∈ H := by
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
      have hc_in_H : c ∈ H := hD_le_H hc_in_D
      have hac_comm : Commute a c := by
        show a * c = c * a
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := H)).comm ⟨a, ha_in_H⟩ ⟨c, hc_in_H⟩)
      have hconj_a : b * a * b⁻¹ = c⁻¹ * a := by
        calc
          b * a * b⁻¹ = ⁅a, b⁆⁻¹ * a := by
            rw [commutatorElement_def]
            group
          _ = c⁻¹ * a := by simp [c]
      have hap_comm_b : Commute (a ^ p) b := by
        have hconj_ap : b * (a ^ p) * b⁻¹ = a ^ p := by
          calc
            b * (a ^ p) * b⁻¹ = (b * a * b⁻¹) ^ p := by
              exact MonoidHom.map_pow (MulAut.conj b).toMonoidHom a p
            _ = (c⁻¹ * a) ^ p := by rw [hconj_a]
            _ = c⁻¹ ^ p * a ^ p := (hac_comm.symm.inv_left).mul_pow p
            _ = a ^ p := by simp [hc_pow]
        show a ^ p * b = b * (a ^ p)
        have hmul : b * (a ^ p) = a ^ p * b := by
          simpa [mul_assoc] using congrArg (fun x => x * b) hconj_ap
        exact hmul.symm
      have hcb_comm : Commute c b := by
        rcases (Subgroup.mem_sup_of_normal_left (x := c) (s := T)
          (t := Subgroup.zpowers (a ^ p))).1 hc_in_Ap with ⟨t, ht, u, hu, htu⟩
        have htb_comm : Commute t b := by
          exact ((Subgroup.mem_center_iff.mp (hT_central ht)) b).symm
        have hub_comm : Commute u b := by
          rcases Subgroup.mem_zpowers_iff.mp hu with ⟨n, rfl⟩
          exact hap_comm_b.zpow_left n
        have htu_comm : Commute (t * u) b := htb_comm.mul_left hub_comm
        rw [htu] at htu_comm
        exact htu_comm
      have hc_center : c ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro r
        have hr_sup : r ∈ H ⊔ Subgroup.zpowers b := by
          rw [hH_sup_b]
          simp
        rcases (Subgroup.mem_sup_of_normal_left (x := r) (s := H)
          (t := Subgroup.zpowers b)).1 hr_sup with ⟨y, hy, z, hz, hyz⟩
        have hcy_comm : Commute c y := by
          show c * y = y * c
          exact congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := H)).comm ⟨c, hc_in_H⟩ ⟨y, hy⟩)
        have hcz_comm : Commute c z := by
          rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
          exact hcb_comm.zpow_right n
        calc
          r * c = (y * z) * c := by rw [hyz]
          _ = y * (z * c) := by simp [mul_assoc]
          _ = y * (c * z) := by rw [← hcz_comm.eq]
          _ = (y * c) * z := by simp [mul_assoc]
          _ = (c * y) * z := by rw [← hcy_comm.eq]
          _ = c * (y * z) := by simp [mul_assoc]
          _ = c * r := by rw [hyz]
      let C : Subgroup R := Subgroup.zpowers c
      have hC_le_center : C ≤ Subgroup.center R := by
        intro x hx
        rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
        exact (Subgroup.center R).zpow_mem hc_center n
      have hC_le_D : C ≤ D := by
        intro x hx
        rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
        exact D.zpow_mem hc_in_D n
      have hC_normal : C.Normal := by
        refine Subgroup.Normal.mk ?_
        intro x hx g
        have hx_cent : x ∈ Subgroup.center R := hC_le_center hx
        have hconj_eq : g * x * g⁻¹ = x := by
          have hcomm : g * x = x * g := (Subgroup.mem_center_iff.mp hx_cent) g
          rw [hcomm]
          group
        rw [hconj_eq]
        exact hx
      letI : C.Normal := hC_normal
      have hC_le_H : C ≤ H := by
        intro x hx
        rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
        exact H.zpow_mem hc_in_H n
      let qC : R →* R ⧸ C := QuotientGroup.mk' C
      have hqCa_comm_b : qC a * qC b = qC b * qC a := by
        have hqc_one : qC c = 1 := by
          exact (QuotientGroup.eq_one_iff (N := C) (x := c)).2 (by simp [C])
        have hcomm_one : ⁅qC a, qC b⁆ = 1 := by
          simpa [qC, c, map_commutatorElement] using hqc_one
        exact (commutatorElement_eq_one_iff_mul_comm).1 hcomm_one
      have hqC_H_b :
          ∀ y : R, y ∈ H → qC y * qC b = qC b * qC y := by
        intro y hy
        have hy_sup : y ∈ T ⊔ Subgroup.zpowers a := by simpa [H] using hy
        rcases (Subgroup.mem_sup_of_normal_left (x := y) (s := T)
          (t := Subgroup.zpowers a)).1 hy_sup with ⟨t, ht, u, hu, htu⟩
        have hqt_comm : qC t * qC b = qC b * qC t := by
          exact (congrArg qC ((Subgroup.mem_center_iff.mp (hT_central ht)) b)).symm
        have hqu_comm : qC u * qC b = qC b * qC u := by
          rcases Subgroup.mem_zpowers_iff.mp hu with ⟨n, rfl⟩
          have hcomm : Commute (qC a) (qC b) := hqCa_comm_b
          exact hcomm.zpow_left n
        calc
          qC y * qC b = (qC t * qC u) * qC b := by rw [← htu]; simp [qC, map_mul]
          _ = qC t * (qC u * qC b) := by simp [mul_assoc]
          _ = qC t * (qC b * qC u) := by rw [hqu_comm]
          _ = (qC t * qC b) * qC u := by simp [mul_assoc]
          _ = (qC b * qC t) * qC u := by rw [hqt_comm]
          _ = qC b * (qC t * qC u) := by simp [mul_assoc]
          _ = qC b * qC y := by rw [← htu]; simp [qC, map_mul]
      let Hbar : Subgroup (R ⧸ C) := H.map qC
      have hHbar_center : Hbar ≤ Subgroup.center (R ⧸ C) := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro z
        rcases QuotientGroup.mk'_surjective C z with ⟨r, rfl⟩
        have hr_sup : r ∈ H ⊔ Subgroup.zpowers b := by
          rw [hH_sup_b]
          simp
        rcases (Subgroup.mem_sup_of_normal_left (x := r) (s := H)
          (t := Subgroup.zpowers b)).1 hr_sup with ⟨y', hy', z', hz', hyz'⟩
        have hyy'_comm : qC y * qC y' = qC y' * qC y := by
          have hcomm : Commute y y' := by
            show y * y' = y' * y
            exact congrArg Subtype.val
              ((IsMulCommutative.is_comm (M := H)).comm ⟨y, hy⟩ ⟨y', hy'⟩)
          simpa [qC, map_mul] using congrArg qC hcomm.eq
        have hyz'_comm : qC y * qC z' = qC z' * qC y := by
          rcases Subgroup.mem_zpowers_iff.mp hz' with ⟨n, rfl⟩
          have hcomm : Commute (qC y) (qC b) := hqC_H_b y hy
          exact hcomm.zpow_right n
        calc
          qC r * qC y = (qC y' * qC z') * qC y := by rw [← hyz']; simp [qC, map_mul]
          _ = qC y' * (qC z' * qC y) := by simp [mul_assoc]
          _ = qC y' * (qC y * qC z') := by rw [← hyz'_comm]
          _ = (qC y' * qC y) * qC z' := by simp [mul_assoc]
          _ = (qC y * qC y') * qC z' := by rw [hyy'_comm]
          _ = qC y * (qC y' * qC z') := by simp [mul_assoc]
          _ = qC y * qC r := by rw [← hyz']; simp [qC, map_mul]
      have hRquotHbar_cyc : IsCyclic ((R ⧸ C) ⧸ Hbar) := by
        let e : (R ⧸ C) ⧸ Hbar ≃* R ⧸ H :=
          QuotientGroup.quotientQuotientEquivQuotient (N := C) (M := H) hC_le_H
        simpa [Hbar] using e.isCyclic.2 hRquotH_cyc
      have hQcomm_C : IsMulCommutative (R ⧸ C) := by
        refine ⟨⟨fun x y => ?_⟩⟩
        have hker_le_center :
            (QuotientGroup.mk' Hbar : R ⧸ C →* (R ⧸ C) ⧸ Hbar).ker ≤ Subgroup.center (R ⧸ C) := by
          simpa [QuotientGroup.ker_mk'] using hHbar_center
        exact ((QuotientGroup.mk' Hbar).isMulCommutative_of_isCyclic_of_ker_le_center
          hker_le_center).is_comm.comm x y
      letI : IsMulCommutative (R ⧸ C) := hQcomm_C
      have hD_le_C : D ≤ C := by
        simpa only [D, derivedSubgroup, derivedSeries_one, qC, QuotientGroup.ker_mk'] using
          (Abelianization.commutator_subset_ker qC)
      have hD_eq_C : D = C := le_antisymm hD_le_C hC_le_D
      obtain ⟨S, hC_le_S, hS_cyc, hS_max⟩ :=
        exists_maximal_cyclic_subgroup_containing C inferInstance
      have hD_le_S : D ≤ S := by
        rw [hD_eq_C]
        exact hC_le_S
      have hS_normal : S.Normal := normal_of_derivedSubgroup_le S hD_le_S
      letI : S.Normal := hS_normal
      have hS_ne_top : S ≠ ⊤ := by
        intro hStop
        have htop_cyc : IsCyclic (⊤ : Subgroup R) := by
          cases hStop
          simpa using hS_cyc
        have hR_cyc : IsCyclic R :=
          (Subgroup.topEquiv : (⊤ : Subgroup R) ≃* R).isCyclic.1 htop_cyc
        exact hRcomm hR_cyc.isMulCommutative
      have hS1_eq :
          ∀ S1 : Subgroup R, S ≤ S1 →
            Nat.card (S1 ⧸ S.subgroupOf S1) = p →
            S1 = omega₁ (G := R) (p := p) ⊔ S := by
        intro S1 hS_le_S1 hS1quot
        have hC_le_S1 : C ≤ S1 := hC_le_S.trans hS_le_S1
        have hS1_not_cyc : ¬ IsCyclic S1 := by
          intro hS1cyc
          have hEq : S1 = S := hS_max S1 hC_le_S1 hS1cyc hS_le_S1
          have hquot_one : Nat.card (S1 ⧸ S.subgroupOf S1) = 1 := by
            subst hEq
            simp
          exact (Fact.out : Nat.Prime p).ne_one (hS1quot.symm.trans hquot_one)
        letI : Fact (IsPGroup p S1) := ⟨(Fact.out : IsPGroup p R).to_subgroup S1⟩
        have hindex1 : ∃ U : Subgroup S1, IsCyclic U ∧ Nat.card (S1 ⧸ U) = p := by
          refine ⟨S.subgroupOf S1, ?_, hS1quot⟩
          exact (Subgroup.subgroupOfEquivOfLe hS_le_S1).isCyclic.2 hS_cyc
        obtain ⟨hΩS1_card, hΩS1_elem⟩ :=
          lemma_4_5_b (R := S1) (p := p) hpodd hS1_not_cyc hindex1
        let Ω1R : Subgroup R := (omega₁ (G := S1) (p := p)).map S1.subtype
        have hΩ1R_le_ΩR : Ω1R ≤ omega₁ (G := R) (p := p) := by
          simpa [Ω1R] using omega₁_map_subtype_le (G := R) (p := p) S1
        have hΩ1R_card : Nat.card Ω1R = p ^ 2 := by
          calc
            Nat.card Ω1R = Nat.card (omega₁ (G := S1) (p := p)) :=
              Subgroup.card_map_of_injective
                (K := omega₁ (G := S1) (p := p)) (f := S1.subtype) S1.subtype_injective
            _ = p ^ 2 := hΩS1_card
        have hΩR_card_eq : Nat.card (omega₁ (G := R) (p := p)) = p ^ 2 := by
          apply le_antisymm hOmega
          rw [← hΩ1R_card]
          exact Subgroup.card_le_of_le hΩ1R_le_ΩR
        have hΩ1R_eq :
            Ω1R = omega₁ (G := R) (p := p) := by
          apply Subgroup.eq_of_le_of_card_ge hΩ1R_le_ΩR
          rw [hΩR_card_eq, hΩ1R_card]
        let S0 : Subgroup S1 := S.subgroupOf S1
        have hΩ_not_cyc : ¬ IsCyclic (omega₁ (G := S1) (p := p)) := by
          intro hcyc
          have hexp_dvd : Monoid.exponent (omega₁ (G := S1) (p := p)) ∣ p :=
            IsElementaryAbelian.exponent_dvd_p p (omega₁ (G := S1) (p := p))
          rw [hcyc.exponent_eq_card, hΩS1_card] at hexp_dvd
          have hp_lt_sq : p < p ^ 2 := pow_two_gt_prime
          exact (Nat.not_dvd_of_pos_of_lt (Fact.out : Nat.Prime p).pos hp_lt_sq) hexp_dvd
        have hΩ_not_le_S0 : ¬ omega₁ (G := S1) (p := p) ≤ S0 := by
          letI : IsCyclic S0 := (Subgroup.subgroupOfEquivOfLe hS_le_S1).isCyclic.2 hS_cyc
          intro hle
          exact hΩ_not_cyc (Subgroup.isCyclic_of_le hle)
        let q10 : S1 →* S1 ⧸ S0 := QuotientGroup.mk' S0
        have hΩmap_ne_bot : (omega₁ (G := S1) (p := p)).map q10 ≠ ⊥ := by
          intro hbot
          have hle :
              omega₁ (G := S1) (p := p) ≤ q10.ker :=
            (Subgroup.map_eq_bot_iff (H := omega₁ (G := S1) (p := p)) (f := q10)).mp hbot
          exact hΩ_not_le_S0 (by simpa [q10, QuotientGroup.ker_mk'] using hle)
        letI : Fact (Nat.card (S1 ⧸ S0)).Prime := ⟨by
          rw [show Nat.card (S1 ⧸ S0) = p by simpa [S0] using hS1quot]
          exact Fact.out
        ⟩
        have hΩmap_top : (omega₁ (G := S1) (p := p)).map q10 = ⊤ := by
          rcases Subgroup.eq_bot_or_eq_top_of_prime_card (H := (omega₁ (G := S1) (p := p)).map q10) with
            hbot | htop
          · exact False.elim (hΩmap_ne_bot hbot)
          · exact htop
        have hsup1 : omega₁ (G := S1) (p := p) ⊔ S0 = ⊤ := by
          calc
            omega₁ (G := S1) (p := p) ⊔ S0 = omega₁ (G := S1) (p := p) ⊔ q10.ker := by
              simp [q10, QuotientGroup.ker_mk']
            _ = ((omega₁ (G := S1) (p := p)).map q10).comap q10 := by
              symm
              simpa using
                (Subgroup.comap_map_eq (f := q10) (H := omega₁ (G := S1) (p := p)))
            _ = ⊤ := by simp [hΩmap_top]
        have hS1_eq_sup : S1 = Ω1R ⊔ S := by
          calc
            S1 = Subgroup.map S1.subtype (⊤ : Subgroup S1) := by
              symm
              simpa using (Subgroup.map_subgroupOf_eq_of_le (H := S1) (K := S1) le_rfl)
            _ = Subgroup.map S1.subtype (omega₁ (G := S1) (p := p) ⊔ S0) := by rw [hsup1]
            _ = Ω1R ⊔ S := by
              rw [Subgroup.map_sup]
              simp [Ω1R, S0, hS_le_S1]
        calc
          S1 = Ω1R ⊔ S := hS1_eq_sup
          _ = omega₁ (G := R) (p := p) ⊔ S := by rw [hΩ1R_eq]
      let qS : R →* R ⧸ S := QuotientGroup.mk' S
      letI : Fact (IsPGroup p (R ⧸ S)) := ⟨(Fact.out : IsPGroup p R).to_quotient S⟩
      have hQ_card_ne_one : Nat.card (R ⧸ S) ≠ 1 := by
        intro hQ1
        have hR_eq_S : Nat.card R = Nat.card S := by
          calc
            Nat.card R = Nat.card (R ⧸ S) * Nat.card S := by
              simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := R) (s := S))
            _ = Nat.card S := by rw [hQ1]; simp
        exact hS_ne_top ((Subgroup.card_eq_iff_eq_top S).1 hR_eq_S.symm)
      have hQ_one_lt : 1 < Nat.card (R ⧸ S) := by
        have hQ_pos : 0 < Nat.card (R ⧸ S) := Nat.card_pos (α := R ⧸ S)
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hQ_pos) (Ne.symm hQ_card_ne_one)
      have hQ_nontriv : Nontrivial (R ⧸ S) :=
        Finite.one_lt_card_iff_nontrivial.mp hQ_one_lt
      have hp_dvd_Q : p ∣ Nat.card (R ⧸ S) := by
        rcases IsPGroup.card_eq_or_dvd (p := p) (G := R ⧸ S) (Fact.out : IsPGroup p (R ⧸ S)) with
          h1 | hdvd
        · exact False.elim (hQ_card_ne_one h1)
        · exact hdvd
      obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' (G := R ⧸ S) p hp_dvd_Q
      let U0 : Subgroup (R ⧸ S) := Subgroup.zpowers x
      have hU0_card : Nat.card U0 = p := by
        rw [Nat.card_zpowers, hx_ord]
      have hQ_unique_p :
          ∀ U : Subgroup (R ⧸ S), Nat.card U = p →
            U = (omega₁ (G := R) (p := p) ⊔ S).map qS := by
        intro U hUcard
        let S1 : Subgroup R := U.comap qS
        have hS_le_S1 : S ≤ S1 := by
          intro s hs
          change qS s ∈ U
          have hs_one : qS s = 1 := (QuotientGroup.eq_one_iff (N := S) (x := s)).2 hs
          simp [hs_one]
        have hS1map_eq : S1.map qS = U := by
          simpa [S1] using
            (Subgroup.map_comap_eq_self_of_surjective (f := qS)
              (h := QuotientGroup.mk'_surjective S) U)
        let qU : S1 →* S1.map qS := qS.subgroupMap S1
        have hqU_surj : Function.Surjective qU := MonoidHom.subgroupMap_surjective qS S1
        have hqU_range_top : qU.range = ⊤ := by
          ext y
          constructor
          · intro _hy
            simp
          · intro _hy
            rcases hqU_surj y with ⟨u, rfl⟩
            exact ⟨u, rfl⟩
        have hqU_ker : qU.ker = S.subgroupOf S1 := by
          simpa [qU, qS, S1] using (Subgroup.ker_subgroupMap (f := qS) (H := S1))
        have hS1quot_card : Nat.card (S1 ⧸ S.subgroupOf S1) = p := by
          have hquot_card : Nat.card (S1 ⧸ qU.ker) = Nat.card (S1.map qS) := by
            have hcard := Nat.card_congr (QuotientGroup.quotientKerEquivRange qU).toEquiv
            simpa [hqU_range_top] using hcard
          calc
            Nat.card (S1 ⧸ S.subgroupOf S1) = Nat.card (S1 ⧸ qU.ker) := by rw [hqU_ker]
            _ = Nat.card (S1.map qS) := hquot_card
            _ = Nat.card U := by rw [hS1map_eq]
            _ = p := hUcard
        have hS1_eq_fixed : S1 = omega₁ (G := R) (p := p) ⊔ S :=
          hS1_eq S1 hS_le_S1 hS1quot_card
        calc
          U = S1.map qS := by rw [hS1map_eq]
          _ = (omega₁ (G := R) (p := p) ⊔ S).map qS := by rw [hS1_eq_fixed]
      have hU0_eq_fixed : U0 = (omega₁ (G := R) (p := p) ⊔ S).map qS :=
        hQ_unique_p U0 hU0_card
      have hQ_comm : IsMulCommutative (R ⧸ S) := by
        refine ⟨⟨fun x y => ?_⟩⟩
        rcases QuotientGroup.mk'_surjective S x with ⟨r, rfl⟩
        rcases QuotientGroup.mk'_surjective S y with ⟨s, rfl⟩
        have hrs_mem : ⁅r, s⁆ ∈ S := by
          exact hD_le_S (by
            simpa [D, derivedSubgroup, derivedSeries_one] using
              (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup R)) (H₂ := (⊤ : Subgroup R))
                (by simp) (by simp)))
        have hcomm_one : ⁅qS r, qS s⁆ = 1 := by
          rw [← map_commutatorElement]
          exact (QuotientGroup.eq_one_iff (N := S) (x := ⁅r, s⁆)).2 hrs_mem
        exact (commutatorElement_eq_one_iff_mul_comm).1 hcomm_one
      letI : IsMulCommutative (R ⧸ S) := hQ_comm
      let ΩQ : Subgroup (R ⧸ S) := omega₁ (G := R ⧸ S) (p := p)
      have hΩQ_pow : ∀ x : ΩQ, x ^ p = 1 := by
        intro x
        apply Subtype.ext
        change (x : R ⧸ S) ^ p = 1
        refine Subgroup.closure_induction (k := {z : R ⧸ S | z ^ (p ^ 1) = 1}) (x := x.1) ?_ ?_ ?_ ?_ x.2
        · intro z hz
          simpa [pow_one] using hz
        · simp
        · intro z₁ z₂ _ _ hz₁ hz₂
          simp [mul_pow, hz₁, hz₂]
        · intro z _ hz
          simpa [inv_pow] using congrArg Inv.inv hz
      have hU0_le_ΩQ : U0 ≤ ΩQ := by
        intro y hy
        change y ∈ Subgroup.closure {z : R ⧸ S | z ^ (p ^ 1) = 1}
        refine Subgroup.subset_closure ?_
        have hy_powU : (⟨y, hy⟩ : U0) ^ Nat.card U0 = 1 := by
          letI : Fintype U0 := Fintype.ofFinite U0
          convert (pow_card_eq_one (x := (⟨y, hy⟩ : U0))) using 1
          simp
        have hy_pow : y ^ p = 1 := by
          simpa [hU0_card] using congrArg Subtype.val hy_powU
        simpa [pow_one] using hy_pow
      have hΩQ_le_U0 : ΩQ ≤ U0 := by
        intro y hy
        by_cases hy1 : y = 1
        · simp [hy1]
        · have hy_pow : y ^ p = 1 := by
            simpa [ΩQ] using congrArg Subtype.val (hΩQ_pow ⟨y, hy⟩)
          have hy_ord : orderOf y = p := orderOf_eq_prime hy_pow hy1
          have hzy_card : Nat.card (Subgroup.zpowers y) = p := by
            rw [Nat.card_zpowers, hy_ord]
          have hzy_eq_fixed :
              Subgroup.zpowers y = (omega₁ (G := R) (p := p) ⊔ S).map qS :=
            hQ_unique_p (Subgroup.zpowers y) hzy_card
          have hzy_eq : Subgroup.zpowers y = U0 := hzy_eq_fixed.trans hU0_eq_fixed.symm
          simpa [hzy_eq] using Subgroup.mem_zpowers y
      have hΩQ_eq_U0 : ΩQ = U0 := le_antisymm hΩQ_le_U0 hU0_le_ΩQ
      have hΩQ_card : Nat.card ΩQ = p := by
        rw [hΩQ_eq_U0, hU0_card]
      have hquot_cyc : IsCyclic (R ⧸ S) := by
        by_contra hncyc
        obtain ⟨E, _hE_normal, hEcard, hEelem⟩ :=
          lemma_4_5_a (R := R ⧸ S) (p := p) hpodd hncyc
        have hE_le_ΩQ : E ≤ ΩQ := by
          intro z hz
          change z ∈ Subgroup.closure {w : R ⧸ S | w ^ (p ^ 1) = 1}
          refine Subgroup.subset_closure ?_
          simpa [pow_one] using elemPow_eq_one_of_isElementaryAbelian z hz
        have hcard_le : Nat.card E ≤ Nat.card ΩQ := Subgroup.card_le_of_le hE_le_ΩQ
        have hp_sq_le_p : p ^ 2 ≤ p := by
          simpa [hEcard, hΩQ_card] using hcard_le
        have hp_lt_sq : p < p ^ 2 := pow_two_gt_prime
        exact (not_le_of_gt hp_lt_sq) hp_sq_le_p
      exact ⟨S, hS_normal, hS_cyc, hquot_cyc⟩
    · obtain ⟨T, hTnorm, hT_le_M, hT_card, hT_central⟩ :=
        exists_central_normal_subgroup_card_eq_prime_of_nontrivial_normal
          (G := R) (p := p) M hM_bot
      letI : T.Normal := hTnorm
      have hT_le_D : T ≤ D := hT_le_M.trans hM_le_D
      have hquot_card : Nat.card R = Nat.card (R ⧸ T) * p := by
        calc
          Nat.card R = Nat.card (R ⧸ T) * Nat.card T := by
            simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := R) (s := T))
          _ = Nat.card (R ⧸ T) * p := by rw [hT_card]
      have hquot_lt : Nat.card (R ⧸ T) < n := by
        rw [← hcardR, hquot_card]
        simpa [one_mul] using
          (Nat.mul_lt_mul_of_pos_left ((Fact.out : Nat.Prime p).one_lt)
            (Nat.card_pos (α := R ⧸ T)))
      letI : Fact (IsPGroup p (R ⧸ T)) := ⟨(Fact.out : IsPGroup p R).to_quotient T⟩
      have hOmega_quot :
          Nat.card (omega₁ (G := R ⧸ T) (p := p)) ≤ p ^ 2 :=
        lemma_4_9 (R := R) (p := p) hpgt hOmega T hTnorm
      have hmeta_quot : IsMetacyclic (R ⧸ T) :=
        ih (Nat.card (R ⧸ T)) hquot_lt (R ⧸ T) rfl hOmega_quot
      have hquot_not_cyclic : ¬ IsCyclic (R ⧸ T) := by
        intro hquot_cyc
        apply hRcomm
        refine ⟨⟨fun a b => ?_⟩⟩
        have hker_le_center :
            (QuotientGroup.mk' T : R →* R ⧸ T).ker ≤ Subgroup.center R := by
          simpa [QuotientGroup.ker_mk'] using hT_central
        exact ((QuotientGroup.mk' T).isMulCommutative_of_isCyclic_of_ker_le_center
          hker_le_center).is_comm.comm a b
      obtain ⟨Abar, hAbar_norm, hAbar_cyc, hAquot_cyc⟩ := hmeta_quot
      letI : Abar.Normal := hAbar_norm
      obtain ⟨a, haH⟩ :=
        exists_zpowers_sup_eq_comap_of_cyclic_subgroup_quotient (T := T) Abar hAbar_cyc
      let H : Subgroup R := T ⊔ Subgroup.zpowers a
      have hH_eq : H = Abar.comap (QuotientGroup.mk' T) := by
        symm
        exact haH
      have hH_norm : H.Normal := by
        rw [hH_eq]
        exact hAbar_norm.comap (QuotientGroup.mk' T)
      letI : H.Normal := hH_norm
      have hT_le_H : T ≤ H := by
        exact le_sup_left
      have hRquotH_cyc : IsCyclic (R ⧸ H) := by
        let qT : R →* R ⧸ T := QuotientGroup.mk' T
        have hHmap_eq : H.map qT = Abar := by
          calc
            H.map qT = (Abar.comap qT).map qT := by rw [hH_eq]
            _ = Abar := by
              simpa using
                (Subgroup.map_comap_eq_self_of_surjective (f := qT)
                  (h := QuotientGroup.mk'_surjective T) Abar)
        let e0 : (R ⧸ T) ⧸ H.map qT ≃* R ⧸ H :=
          QuotientGroup.quotientQuotientEquivQuotient (N := T) (M := H) hT_le_H
        let e1 : (R ⧸ T) ⧸ Abar ≃* (R ⧸ T) ⧸ H.map qT :=
          (QuotientGroup.quotientMulEquivOfEq hHmap_eq).symm
        exact (e1.trans e0).isCyclic.1 hAquot_cyc
      obtain ⟨b, hH_sup_b⟩ := exists_zpowers_sup_eq_top_of_cyclic_quotient (N := H) hRquotH_cyc
      let Tsub : Subgroup H := T.subgroupOf H
      letI : Tsub.Normal := Subgroup.Normal.subgroupOf (G := R) (hH := hTnorm) H
      have hTsub_center : Tsub ≤ Subgroup.center H := by
        intro x hx
        have hxT : ((x : H) : R) ∈ T := by
          simpa [Tsub, Subgroup.mem_subgroupOf] using hx
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp (hT_central hxT)) y.1
      have hTsub_sup : Tsub ⊔ (Subgroup.zpowers a).subgroupOf H = ⊤ := by
        rw [← Subgroup.subgroupOf_sup (A := T) (A' := Subgroup.zpowers a) (B := H)
          le_sup_left le_sup_right]
        simp [H]
      have hza_sub_cyc : IsCyclic ((Subgroup.zpowers a).subgroupOf H) := by
        exact (Subgroup.subgroupOfEquivOfLe (H := Subgroup.zpowers a) (K := H) le_sup_right).isCyclic.2
          inferInstance
      have hHquotT_cyc : IsCyclic (H ⧸ Tsub) :=
        quotient_isCyclic_of_sup_cyclic_right (R := H) (R₁ := Tsub)
          (R₂ := (Subgroup.zpowers a).subgroupOf H) hTsub_sup hza_sub_cyc
      have hH_comm : IsMulCommutative H := by
        refine ⟨⟨fun x y => ?_⟩⟩
        have hkerTsub_le_center :
            (QuotientGroup.mk' Tsub : H →* H ⧸ Tsub).ker ≤ Subgroup.center H := by
          simpa [QuotientGroup.ker_mk'] using hTsub_center
        exact ((QuotientGroup.mk' Tsub).isMulCommutative_of_isCyclic_of_ker_le_center
          hkerTsub_le_center).is_comm.comm x y
      letI : IsMulCommutative H := hH_comm
      have hD_le_H : D ≤ H := by
        letI : IsMulCommutative (Subgroup.zpowers b) := inferInstance
        have hcomm_le : _root_.commutator R ≤ H :=
          Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
            (N := H) (H := Subgroup.zpowers b) hH_sup_b inferInstance
        simpa only [D, derivedSubgroup, derivedSeries_one] using hcomm_le
      have hM_le_mhoHmap : M ≤ (mho p 1 H).map H.subtype := by
        simpa [M, D] using (mho_one_map_subtype_mono (p := p) hD_le_H)
      have hT_le_mhoHmap : T ≤ (mho p 1 H).map H.subtype := hT_le_M.trans hM_le_mhoHmap
      have hTsub_le_mhoH : Tsub ≤ mho p 1 H := by
        intro x hx
        have hxT : ((x : H) : R) ∈ T := by
          simpa [Tsub, Subgroup.mem_subgroupOf] using hx
        have hxmap : ((x : H) : R) ∈ (mho p 1 H).map H.subtype := hT_le_mhoHmap hxT
        rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hy_eq⟩
        have hyx : y = x := by
          apply Subtype.ext
          simpa using hy_eq
        simpa [hyx] using hy
      letI : Fact (IsPGroup p H) := ⟨(Fact.out : IsPGroup p R).to_subgroup H⟩
      have hTsub_le_frattini : Tsub ≤ frattini H :=
        hTsub_le_mhoH.trans (mho_one_le_frattini_local (G := H) (p := p))
      have hza_sub_sup_frattini : (Subgroup.zpowers a).subgroupOf H ⊔ frattini H = ⊤ := by
        apply top_unique
        calc
          ⊤ = Tsub ⊔ (Subgroup.zpowers a).subgroupOf H := hTsub_sup.symm
          _ ≤ frattini H ⊔ (Subgroup.zpowers a).subgroupOf H :=
            sup_le_sup hTsub_le_frattini le_rfl
          _ = (Subgroup.zpowers a).subgroupOf H ⊔ frattini H := by rw [sup_comm]
      have hza_sub_top : (Subgroup.zpowers a).subgroupOf H = ⊤ :=
        frattini_nongenerating (G := H) hza_sub_sup_frattini
      have hH_cyc : IsCyclic H := by
        have htop_cyc : IsCyclic (⊤ : Subgroup H) := by
          rw [← hza_sub_top]
          exact hza_sub_cyc
        exact (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).isCyclic.1 htop_cyc
      exact ⟨H, hH_norm, hH_cyc, hRquotH_cyc⟩

/-! # Proposition 4.11 from BG Section 4 -/

section Main

open scoped FixedPoints
public theorem CFSG.proposition_4_11 {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hpgt : 3 < p)
    (hOmega : Nat.card (omega₁ (G := R) (p := p)) ≤ p ^ 2) :
    IsMetacyclic R := by
  exact proposition_4_11_aux (p := p) hpgt (Nat.card R) R rfl hOmega
