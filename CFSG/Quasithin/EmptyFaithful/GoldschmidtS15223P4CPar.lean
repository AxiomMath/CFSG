module

public import CFSG.Quasithin.Background.FLcLn
public import CFSG.Quasithin.EmptyFaithful.S151ZQ
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CVoc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.FLc CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace S15223P4

namespace C

theorem eq_of_forall_orderOf_three {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : 1 ≤ n)
    (e : Q ≃* SLt n) {B Pk P : Subgroup Q} (hB : IsSylowTwoOf B ⊤) (hBk : B ≤ Pk)
    (hkP : Pk ≤ P) (h3 : ∀ y ∈ P, orderOf y = 3 → y ∈ Pk) : P = Pk := by
  have eL : ↥(⊤ : Subgroup Q) ≃* SLt n := Subgroup.topEquiv.trans e
  obtain ⟨D⟩ := exists_borelIso hn hB eL
  have hBL : B ≤ ⊤ := le_top
  refine le_antisymm ?_ hkP
  rw [D.cutsOf_le_iff hBL (hBk.trans hkP) le_top hBk]
  intro j hjk
  by_contra hjP
  have hjn : IsNode n j := D.isNode_of_mem_cutsOf hjk
  obtain ⟨Pj, hBPj, hPjL, hPjc⟩ :=
    D.exists_cutsOf_eq hBL (I := nodeSet n \ {j}) (fun i hi => hi.1)
  have hPjP : Pj ≤ P := by
    rw [D.cutsOf_le_iff hBL hBPj le_top (hBk.trans hkP), hPjc]
    intro i hi
    refine ⟨D.isNode_of_mem_cutsOf hi, fun h => hjP ?_⟩
    rw [Set.mem_singleton_iff] at h
    rw [← h]
    exact hi
  have hUPj : Ut n ≤ D.model Pj := (D.Ut_le_model_iff hBL).2 hBPj
  have hmodel : D.model Pj = QI n (nodeSet n \ {j}) := by
    calc D.model Pj = QI n (cuts (D.model Pj)) := eq_QI_cuts hUPj
      _ = QI n (nodeSet n \ {j}) := by rw [← hPjc]; rfl
  have hidx := index_single hjn
  rw [← hmodel] at hidx
  have hcard : Nat.card Pj = 3 * Nat.card B := by
    have h1 := Subgroup.relIndex_mul_card (Ut n) (D.model Pj)
    rw [inf_of_le_left hUPj, hidx] at h1
    have h2 := D.card_model hPjL
    have h4 := D.card_model hBL
    rw [D.model_B] at h4
    omega
  have h3dvd : 3 ∣ Nat.card Pj := ⟨Nat.card B, hcard⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hy' : orderOf (y : Q) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyk : (y : Q) ∈ Pk := h3 y (hPjP y.2) hy'
  have hyB : (y : Q) ∉ B := by
    intro hyB
    obtain ⟨k, hk⟩ := hB.2.1 ⟨(y : Q), hyB⟩
    have hk' : (y : Q) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd : 3 ∣ 2 ^ k := by
      rw [← hy']
      exact orderOf_dvd_of_pow_eq_one hk'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  have hBK : B ≤ Pk ⊓ Pj := le_inf hBk hBPj
  have hKPj : Pk ⊓ Pj ≤ Pj := inf_le_right
  have hrel : B.relIndex Pj = 3 := by
    have h1 := Subgroup.relIndex_mul_card B Pj
    rw [inf_of_le_left hBPj] at h1
    have hpos : 0 < Nat.card B := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, hcard])
  have hmul := Subgroup.relIndex_mul_relIndex B (Pk ⊓ Pj) Pj hBK hKPj
  rw [hrel] at hmul
  have hdvd : B.relIndex (Pk ⊓ Pj) ∣ 3 := ⟨(Pk ⊓ Pj).relIndex Pj, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact hyB (Subgroup.relIndex_eq_one.1 h ⟨hyk, y.2⟩)
  · rw [h] at hmul
    have h1 : (Pk ⊓ Pj).relIndex Pj = 1 := by omega
    have hPjPk : Pj ≤ Pk := (Subgroup.relIndex_eq_one.1 h1).trans inf_le_left
    have h2 := (D.cutsOf_le_iff hBL hBPj hPjL hBk).1 hPjPk hjk
    rw [hPjc] at h2
    exact h2.2 rfl

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

@[expose] def star (X P : Subgroup G) : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
  (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))

omit [Finite G] in
theorem mem_star {X P : Subgroup G} {q : ↥X ⧸ CFSG.pCore 2 ↥X} :
    q ∈ star X P ↔ ∃ x : ↥X, (x : G) ∈ P ∧ (x : ↥X ⧸ CFSG.pCore 2 ↥X) = q := by
  unfold star
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem star_mono {X P P' : Subgroup G} (h : P ≤ P') : star X P ≤ star X P' := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := mem_star.1 hq
  exact mem_star.2 ⟨x, h hx, rfl⟩

omit [Finite G] in
theorem isSylowTwoOf_star {X A : Subgroup G} (hA : IsSylowTwoOf A X) :
    IsSylowTwoOf (star X A) ⊤ := by
  have h := CFSG.QuasithinUnique.Setup.Wreath.isSylowTwoOf_map_hom hA
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
  rwa [QuotientGroup.range_mk'] at h

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem inf_centralizer_le_kI_sup :
    X ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ≤
      kI T Mc M B₀ ⊔ (sOf152 T Mc M B₀ ⊓ X) := by
  obtain ⟨n, hn, ⟨e⟩⟩ : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) :=
    d.ln.elim (fun h => ⟨4, by norm_num, h⟩) (fun h => ⟨5, by norm_num, h⟩)
  let eq : (↥X ⧸ CFSG.pCore 2 ↥X) ≃* SLt n :=
    e.trans (specialLinearGroupEquivStatedSL n (ZMod 2)).symm
  set A := sOf152 T Mc M B₀ ⊓ X with hAdef
  have hB := isSylowTwoOf_star d.f.sylow
  have hAk : A ≤ kI T Mc M B₀ ⊔ A := le_sup_right
  have hkM : kI T Mc M B₀ ⊔ A ≤ X ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) :=
    sup_le (le_inf d.kI_le_X (kI_le_centralizer T Mc M B₀))
      (le_inf inf_le_right (inf_le_left.trans d.c.S_le_centralizer))
  have h3 : ∀ y ∈ star X (X ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)),
      orderOf y = 3 → y ∈ star X (kI T Mc M B₀ ⊔ A) := by
    intro y hy hy3
    obtain ⟨x, hxC, rfl⟩ := mem_star.1 hy
    have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    obtain ⟨a, c, hc3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hx0 3 (by norm_num)
    have hcdvd : c ∣ orderOf x := ⟨3 ^ a, by rw [hord]; ring⟩
    have hc0 : 0 < c := Nat.pos_of_ne_zero fun h => hx0 (by rw [hord, h, mul_zero])
    have hord' : orderOf (x ^ c) = 3 ^ a := by
      rw [orderOf_pow_of_dvd hc0.ne' hcdvd, hord, Nat.mul_div_cancel _ hc0]
    have hxG : orderOf (((x ^ c : ↥X)) : G) = 3 ^ a := by
      rw [Subgroup.orderOf_coe]
      exact hord'
    have hxk : (((x ^ c : ↥X)) : G) ∈ kI T Mc M B₀ :=
      Subgroup.subset_closure ⟨by simpa using pow_mem hxC.2 c, a, hxG⟩
    have hmem : ((x ^ c : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ star X (kI T Mc M B₀ ⊔ A) :=
      mem_star.2 ⟨x ^ c, Subgroup.mem_sup_left hxk, rfl⟩
    have hy3' : orderOf (x : ↥X ⧸ CFSG.pCore 2 ↥X) = 3 := hy3
    have hr : c % 3 = 1 ∨ c % 3 = 2 := by omega
    have hyy : (x : ↥X ⧸ CFSG.pCore 2 ↥X) =
        ((x ^ c : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ^ (c % 3) := by
      rw [QuotientGroup.mk_pow, ← pow_mul, ← pow_mod_orderOf, hy3']
      rcases hr with h | h <;> simp [Nat.mul_mod, h]
    rw [hyy]
    exact pow_mem hmem _
  have key := eq_of_forall_orderOf_three (by omega) eq hB (star_mono hAk) (star_mono hkM) h3
  intro x hx
  have hxq : ((⟨x, hx.1⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈
      star X (X ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) :=
    mem_star.2 ⟨⟨x, hx.1⟩, hx, rfl⟩
  rw [key] at hxq
  obtain ⟨x₁, hx₁, hq⟩ := mem_star.1 hxq
  have hz : x₁⁻¹ * ⟨x, hx.1⟩ ∈ CFSG.pCore 2 ↥X := QuotientGroup.eq.1 hq
  have hzA : ((x₁⁻¹ * ⟨x, hx.1⟩ : ↥X) : G) ∈ A := by
    apply d.f.sylow.pCoreOf_le
    rw [CFSG.Open.pCoreOf]
    exact ⟨_, by assumption, rfl⟩
  have hxx : x = (x₁ : G) * ((x₁⁻¹ * ⟨x, hx.1⟩ : ↥X) : G) := by simp
  rw [hxx]
  exact Subgroup.mul_mem _ hx₁ (Subgroup.mem_sup_right hzA)

end CData

end C

end S15223P4

end CFSG.Quasithin
