module

public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

/-!
# Frattini lemmas used in BG section 1
-/

/-- Lemma 1.7(a): if `H ⊔ Φ(R) = ⊤`, then `H = ⊤`. -/
public theorem CFSG.lemma_1_7_a {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] : ∀ H : Subgroup R, H ⊔ frattini R = ⊤ → H = ⊤ := by
  let _ := (inferInstance : Fact p.Prime)
  let _ := (inferInstance : Fact (IsPGroup p R))
  intro H hsup
  simpa using (frattini_nongenerating (G := R) hsup)

public lemma CFSG.coatom_normal_of_isPGroup {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] {K : Subgroup R} (hK : IsCoatom K) : K.Normal := by
  have hnil : Group.IsNilpotent R := IsPGroup.isNilpotent (p := p) (G := R) (h := Fact.out)
  have hnc : NormalizerCondition R := Group.normalizerCondition_of_isNilpotent (G := R)
  exact Subgroup.NormalizerCondition.normal_of_coatom K hnc hK

lemma CFSG.quotient_subgroup_eq_bot_or_top_of_coatom {R : Type*} [Group R]
    {K : Subgroup R} [K.Normal] (hK : IsCoatom K) :
    ∀ H : Subgroup (R ⧸ K), H = ⊥ ∨ H = ⊤ := by
  intro H
  have hK_le_comap : K ≤ H.comap (QuotientGroup.mk' K) := by
    intro x hx
    change QuotientGroup.mk' K x ∈ H
    have hx1 : QuotientGroup.mk' K x = 1 := (QuotientGroup.eq_one_iff (N := K) (x := x)).2 hx
    simp [hx1]
  by_cases hEq : H.comap (QuotientGroup.mk' K) = K
  · left
    have hmap : (H.comap (QuotientGroup.mk' K)).map (QuotientGroup.mk' K) = H := by
      simpa using (Subgroup.map_comap_eq_self_of_surjective (f := QuotientGroup.mk' K)
        (h := QuotientGroup.mk'_surjective K) H)
    calc
      H = (H.comap (QuotientGroup.mk' K)).map (QuotientGroup.mk' K) := hmap.symm
      _ = K.map (QuotientGroup.mk' K) := by simp [hEq]
      _ = ⊥ := by simp
  · right
    have hlt : K < H.comap (QuotientGroup.mk' K) := lt_of_le_of_ne hK_le_comap (by simpa [eq_comm] using hEq)
    have hcomap_top : H.comap (QuotientGroup.mk' K) = ⊤ := hK.right _ hlt
    have hmap : (H.comap (QuotientGroup.mk' K)).map (QuotientGroup.mk' K) = H := by
      simpa using (Subgroup.map_comap_eq_self_of_surjective (f := QuotientGroup.mk' K)
        (h := QuotientGroup.mk'_surjective K) H)
    calc
      H = (H.comap (QuotientGroup.mk' K)).map (QuotientGroup.mk' K) := hmap.symm
      _ = (⊤ : Subgroup R).map (QuotientGroup.mk' K) := by simp [hcomap_top]
      _ = ⊤ := by
            simpa using (Subgroup.map_top_of_surjective (f := QuotientGroup.mk' K)
              (QuotientGroup.mk'_surjective K))

lemma CFSG.card_quotient_coatom_eq_prime {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    {K : Subgroup R} (hK : IsCoatom K) : Nat.card (R ⧸ K) = p := by
  letI : K.Normal := coatom_normal_of_isPGroup (p := p) (K := K) hK
  have hq_pgroup : IsPGroup p (R ⧸ K) := (Fact.out : IsPGroup p R).to_quotient K
  rcases hq_pgroup.exists_card_eq with ⟨n, hn⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have hcard1 : Nat.card (R ⧸ K) = 1 := by simpa [hn0] using hn
    have hsub : Subsingleton (R ⧸ K) := (Nat.card_eq_one_iff_unique.mp hcard1).1
    have hK_top : K = ⊤ := (QuotientGroup.subsingleton_iff (N := K)).1 hsub
    exact hK.left hK_top
  have hn_le_one : n ≤ 1 := by
    by_contra hnot
    have hn_ge_two : 2 ≤ n := Nat.succ_le_of_lt (lt_of_not_ge hnot)
    have h1le : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn_ge_two
    have hp_le_cardQ : p ^ 1 ≤ Nat.card (R ⧸ K) := by
      rw [hn]
      exact Nat.pow_le_pow_right ((Fact.out : Nat.Prime p).pos) h1le
    obtain ⟨H, hHcard⟩ :=
      Sylow.exists_subgroup_card_pow_prime_of_le_card (G := (R ⧸ K)) (p := p) (n := 1)
        (hp := Fact.out) hq_pgroup hp_le_cardQ
    have hH_ne_bot : H ≠ ⊥ := by
      intro hbot
      have : Nat.card H = 1 := by simp [hbot]
      have hp_one : p = 1 := by simpa [hHcard] using this
      exact (Fact.out : Nat.Prime p).ne_one hp_one
    have hH_ne_top : H ≠ ⊤ := by
      intro htop
      have hcardH : Nat.card H = p := by simpa using hHcard
      have hpow_eq : p ^ n = p := by
        calc
          p ^ n = Nat.card (R ⧸ K) := hn.symm
          _ = Nat.card H := by simp [htop]
          _ = p := hcardH
      have hpow_eq' : p ^ n = p ^ 1 := by simpa using hpow_eq
      have hn_eq_one : n = 1 :=
        (Nat.pow_right_injective (show 2 ≤ p from (Fact.out : Nat.Prime p).two_le)) hpow_eq'
      exact Nat.not_succ_le_self 1 (by simp [hn_eq_one] at hn_ge_two)
    have hbot_or_top := quotient_subgroup_eq_bot_or_top_of_coatom (K := K) hK H
    exact (hbot_or_top.elim hH_ne_bot hH_ne_top)
  have hn_eq_one : n = 1 := Nat.le_antisymm hn_le_one (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero))
  simp [hn, hn_eq_one]

public lemma CFSG.commutator_le_frattini_of_isPGroup {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    _root_.commutator R ≤ frattini R := by
  intro x hx
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro M hM
  letI : M.Normal := coatom_normal_of_isPGroup (p := p) (K := M) hM
  have hcardQ : Nat.card (R ⧸ M) = p := card_quotient_coatom_eq_prime (p := p) (K := M) hM
  have hcyc : IsCyclic (R ⧸ M) := isCyclic_of_prime_card (α := (R ⧸ M)) hcardQ
  letI : CommGroup (R ⧸ M) := hcyc.commGroup
  have hcommQ : IsMulCommutative (R ⧸ M) := inferInstance
  have hcomm_le : _root_.commutator R ≤ M :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := M)).1 hcommQ
  exact hcomm_le hx

public lemma CFSG.pth_power_mem_frattini_of_isPGroup {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] (x : R) : x ^ p ∈ frattini R := by
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro M hM
  letI : M.Normal := coatom_normal_of_isPGroup (p := p) (K := M) hM
  letI : Fintype (R ⧸ M) := Fintype.ofFinite (R ⧸ M)
  have hcardQ : Nat.card (R ⧸ M) = p := card_quotient_coatom_eq_prime (p := p) (K := M) hM
  have hcardQf : Fintype.card (R ⧸ M) = p := by
    simpa [Nat.card_eq_fintype_card] using hcardQ
  have hpowQ : ((QuotientGroup.mk' M x) : R ⧸ M) ^ p = 1 := by
    have : ((QuotientGroup.mk' M x) : R ⧸ M) ^ Fintype.card (R ⧸ M) = 1 := by
      exact pow_card_eq_one (x := (QuotientGroup.mk' M x : R ⧸ M))
    simpa [hcardQf] using this
  exact (QuotientGroup.eq_one_iff (N := M) (x := x ^ p)).1 (by
    simpa [MonoidHom.map_pow] using hpowQ)

/-- Lemma 1.7(b): the Frattini quotient of a finite `p`-group is elementary abelian. -/
public theorem CFSG.isElementaryAbelian_quotient_frattini {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    IsElementaryAbelian p (R ⧸ frattini R) := by
  refine {
    toIsMulCommutative := ?_,
    exponent_dvd_p := ?_
  }
  · have hcomm_le : _root_.commutator R ≤ frattini R :=
      commutator_le_frattini_of_isPGroup (R := R) (p := p)
    have hcommQ : IsMulCommutative (R ⧸ frattini R) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini R)).2 hcomm_le
    exact hcommQ
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change ((QuotientGroup.mk' (frattini R) x : R ⧸ frattini R) ^ p = 1)
    have hxpow : x ^ p ∈ frattini R := pth_power_mem_frattini_of_isPGroup (R := R) (p := p) x
    exact (QuotientGroup.eq_one_iff (N := frattini R) (x := x ^ p)).2 hxpow

public theorem CFSG.frattini_eq_bot_of_isElementaryAbelian {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [IsElementaryAbelian p R] :
    frattini R = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · let B : Subgroup R := Subgroup.zpowers x
    have horder_dvd : orderOf x ∣ p := by
      have horder_dvd_exp : orderOf x ∣ Monoid.exponent R :=
        orderOf_dvd_of_pow_eq_one (Monoid.pow_exponent_eq_one x)
      exact horder_dvd_exp.trans (IsElementaryAbelian.exponent_dvd_p p R)
    have horder_eq_p : orderOf x = p := by
      rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).1 horder_dvd with h1 | hp
      · exact False.elim (hx1 (orderOf_eq_one_iff.mp h1))
      · exact hp
    have hB_card : Nat.card B = p := by
      have hB_card_order : Nat.card B = orderOf x := by
        dsimp [B]
        exact Nat.card_zpowers x
      exact hB_card_order.trans horder_eq_p
    obtain ⟨C, hcompl⟩ := IsElementaryAbelian.exists_isCompl (p := p) (A := R) B
    have hxB : x ∈ B := by
      dsimp [B]
      exact Subgroup.mem_zpowers x
    have hx_not_C : x ∉ C := by
      intro hxC
      have hx_inf : x ∈ B ⊓ C := ⟨hxB, hxC⟩
      have hx_bot : x ∈ (⊥ : Subgroup R) := by simpa [hcompl.inf_eq_bot] using hx_inf
      exact hx1 (by simpa using hx_bot)
    have hC_coatom : IsCoatom C := by
      refine ⟨?_, ?_⟩
      · intro hCtop
        exact hx_not_C (by simp [hCtop])
      · intro D hCD
        have hC_le_D : C ≤ D := le_of_lt hCD
        rcases SetLike.exists_of_lt hCD with ⟨d, hdD, hdnotC⟩
        have hsup : B ⊔ C = ⊤ := by simpa [sup_comm] using hcompl.sup_eq_top
        have hdBC : d ∈ B ⊔ C := by simp [hsup]
        rcases (Subgroup.mem_sup (s := B) (t := C) (x := d)).1 hdBC with
          ⟨b, hbB, c, hcC, hbc_eq⟩
        have hbcD : b * c ∈ D := by simpa [hbc_eq] using hdD
        have hcD : c ∈ D := hC_le_D hcC
        have hbD : b ∈ D := by
          have : (b * c) * c⁻¹ ∈ D := D.mul_mem hbcD (D.inv_mem hcD)
          simpa [mul_assoc] using this
        have hb_ne_one : b ≠ 1 := by
          intro hb1
          have hd_eq_c : d = c := by
            calc
              d = b * c := hbc_eq.symm
              _ = c := by simp [hb1]
          exact hdnotC (hd_eq_c ▸ hcC)
        let E : Subgroup B := (B ⊓ D).subgroupOf B
        have hbE : (⟨b, hbB⟩ : B) ∈ E := by
          change b ∈ B ⊓ D
          exact ⟨hbB, hbD⟩
        have hE_ne_bot : E ≠ ⊥ := by
          intro hEbot
          have hbE_bot : (⟨b, hbB⟩ : B) ∈ (⊥ : Subgroup B) := by simpa [hEbot] using hbE
          have : (⟨b, hbB⟩ : B) = 1 := by simpa using hbE_bot
          exact hb_ne_one (Subtype.ext_iff.mp this)
        haveI : Fact (Nat.card B).Prime := ⟨by simpa [hB_card] using (Fact.out : Nat.Prime p)⟩
        have hE_bot_or_top : E = ⊥ ∨ E = ⊤ :=
          Subgroup.eq_bot_or_eq_top_of_prime_card (G := B) E
        have hE_top : E = ⊤ := hE_bot_or_top.resolve_left hE_ne_bot
        have hB_le_BinfD : B ≤ B ⊓ D := (Subgroup.subgroupOf_eq_top).1 hE_top
        have hB_le_D : B ≤ D := fun y hy => (hB_le_BinfD hy).2
        have htop_le_D : (⊤ : Subgroup R) ≤ D := by
          rw [← hcompl.sup_eq_top]
          exact sup_le hB_le_D hC_le_D
        exact top_le_iff.mp htop_le_D
    have hxC : x ∈ C := (frattini_le_coatom hC_coatom) hx
    exact False.elim (hx_not_C hxC)

public noncomputable def CFSG.frattiniQuotientEquivOfIsElementaryAbelian
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [IsElementaryAbelian p R] :
    R ⧸ frattini R ≃* R :=
  (QuotientGroup.quotientMulEquivOfEq
    (frattini_eq_bot_of_isElementaryAbelian (R := R) (p := p))).trans
    (QuotientGroup.quotientBot (G := R))

public theorem CFSG.frattiniQuotientEquivOfIsElementaryAbelian_mk'
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [IsElementaryAbelian p R]
    (r : R) :
    frattiniQuotientEquivOfIsElementaryAbelian (R := R) (p := p)
      (QuotientGroup.mk' (frattini R) r) = r := by
  rfl

public theorem CFSG.frattiniQuotientEquivOfIsElementaryAbelian_coe
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [IsElementaryAbelian p R]
    (r : R) :
    frattiniQuotientEquivOfIsElementaryAbelian (R := R) (p := p)
      (r : R ⧸ frattini R) = r :=
  frattiniQuotientEquivOfIsElementaryAbelian_mk' (R := R) (p := p) r

/-- Lemma 1.7(c): `Φ(R) = 1` iff `R` is elementary abelian. -/
public theorem CFSG.frattini_eq_bot_iff_isElementaryAbelian {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    frattini R = ⊥ ↔ IsElementaryAbelian p R := by
  constructor
  · intro hphi
    refine {
      toIsMulCommutative := ?_,
      exponent_dvd_p := ?_
    }
    · have hcomm_le : _root_.commutator R ≤ frattini R :=
        commutator_le_frattini_of_isPGroup (R := R) (p := p)
      have hcomm_bot : _root_.commutator R = ⊥ := by
        refine le_antisymm ?_ bot_le
        simpa [hphi] using hcomm_le
      have htop_comm_bot : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊥ := by
        simpa [_root_.commutator_def] using hcomm_bot
      have htop_le_centralizer :
          (⊤ : Subgroup R) ≤ Subgroup.centralizer (((⊤ : Subgroup R) : Set R)) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).1 htop_comm_bot
      exact {
        is_comm := ⟨by
          intro a b
          have ha_centralizer : a ∈ Subgroup.centralizer (((⊤ : Subgroup R) : Set R)) :=
            htop_le_centralizer (by simp)
          exact ((Subgroup.mem_centralizer_iff (g := a) (s := ((⊤ : Subgroup R) : Set R))).1
            ha_centralizer b (by simp)).symm⟩
      }
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro x
      have hxpow_mem : x ^ p ∈ frattini R :=
        pth_power_mem_frattini_of_isPGroup (R := R) (p := p) x
      have hxpow_bot : x ^ p ∈ (⊥ : Subgroup R) := by
        simpa [hphi] using hxpow_mem
      simpa using hxpow_bot
  · intro hElem
    letI : IsElementaryAbelian p R := hElem
    exact frattini_eq_bot_of_isElementaryAbelian (R := R) (p := p)

/-- Lemma 1.7(d): for a finite `p`-group, `Φ(R)` is generated by commutators and `p`-th powers. -/
public theorem CFSG.frattini_eq_closure_commutator_union_powers {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    frattini R =
      Subgroup.closure (((_root_.commutator R : Subgroup R) : Set R) ∪
        Set.range (fun x : R => x ^ p)) := by
  let K : Subgroup R :=
    Subgroup.closure (((_root_.commutator R : Subgroup R) : Set R) ∪
      Set.range (fun x : R => x ^ p))
  have hK_normal : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine Subgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_)
      (fun x _ ihx => ?_) hn
    · rcases hx with hxcomm | ⟨y, rfl⟩
      · exact Subgroup.subset_closure
          (Or.inl (((inferInstance : (_root_.commutator R).Normal).conj_mem x hxcomm g)))
      · exact Subgroup.subset_closure
          (Or.inr ⟨g * y * g⁻¹, conj_pow (a := g) (b := y) (i := p)⟩)
    · simp
    · rw [← conj_mul]
      exact K.mul_mem ihx ihy
    · rw [← conj_inv]
      exact K.inv_mem ihx
  letI : K.Normal := hK_normal
  have hK_le_frattini : K ≤ frattini R := by
    refine (Subgroup.closure_le (K := frattini R)).2 ?_
    intro x hx
    rcases hx with hxcomm | ⟨y, rfl⟩
    · exact commutator_le_frattini_of_isPGroup (R := R) (p := p) hxcomm
    · exact pth_power_mem_frattini_of_isPGroup (R := R) (p := p) y
  have hcomm_le_K : _root_.commutator R ≤ K := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl hx)
  have hElem_quot : IsElementaryAbelian p (R ⧸ K) := by
    refine {
      toIsMulCommutative := ?_,
      exponent_dvd_p := ?_
    }
    · have hcommQ : IsMulCommutative (R ⧸ K) :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).2 hcomm_le_K
      exact hcommQ
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro q
      refine QuotientGroup.induction_on q ?_
      intro x
      change ((QuotientGroup.mk' K x : R ⧸ K) ^ p = 1)
      have hxpow_mem : x ^ p ∈ K := Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)
      exact (QuotientGroup.eq_one_iff (N := K) (x := x ^ p)).2 hxpow_mem
  haveI : Fact (IsPGroup p (R ⧸ K)) := ⟨(Fact.out : IsPGroup p R).to_quotient K⟩
  have hphi_quot : frattini (R ⧸ K) = ⊥ :=
    (frattini_eq_bot_iff_isElementaryAbelian (R := R ⧸ K) (p := p)).2 hElem_quot
  have hfrattini_le_comap :
      frattini R ≤ (frattini (R ⧸ K)).comap (QuotientGroup.mk' K) :=
    frattini_le_comap_frattini_of_surjective (G := R) (H := R ⧸ K) (φ := QuotientGroup.mk' K)
      (QuotientGroup.mk'_surjective K)
  have hfrattini_le_K : frattini R ≤ K := by
    simpa [hphi_quot, K] using hfrattini_le_comap
  exact le_antisymm hfrattini_le_K hK_le_frattini
