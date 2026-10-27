module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec11Torus
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec112
import CFSG.RankThree.GF2n.Stroth80.Sec119KU
import CFSG.RankThree.GF2n.Stroth80.Sec119Lift
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusLine

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem IsLBTorus.mk_mem_Ebar_of_eq_conj_pow {y : G} (hy : IsLBTorus M Q Z B y)
    (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {i : ℕ} {m : ↥M}
    (hm : (m : G) = y ^ i * a * (y ^ i)⁻¹) :
    (QuotientGroup.mk m : Mbar M Q) ∈ Ebar M Q Z B := by
  have hL : y ^ i * a * (y ^ i)⁻¹ ∈ LB M Q B :=
    hc.conj_mem_LB_of_mem_normalizer (M.pow_mem hy.mem_M i)
      (Subgroup.pow_mem _ hy.normalizes_B i) ha
  have hA' : IsA2 Q Z (y ^ i * a * (y ^ i)⁻¹) := by
    have h := hA.conj (y ^ i)
    rwa [hc.conj_Q_eq (M.pow_mem hy.mem_M i), hc.conj_Z_eq (M.pow_mem hy.mem_M i)] at h
  have e : m = ⟨y ^ i * a * (y ^ i)⁻¹, hc.LB_le_M hL⟩ := Subtype.ext hm
  rw [e]
  exact hc.mk_mem_Ebar hL hA'

theorem IsLBTorus.exists_line_Xbar {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {a : G} (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) :
    ∃ L : Subgroup ↥(Xbar M Q Z B), Nat.card L = Nat.card Z ∧
      (∀ u : ↥(Xbar M Q Z B),
        (u : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) → u ∈ L) ∧
      ∀ u ∈ L, u ≠ 1 → ∃ i < Nat.card Z - 1, ∃ m : ↥M, (m : G) = y ^ i * a * (y ^ i)⁻¹ ∧
        (u : Mbar M Q) = QuotientGroup.mk m := by
  obtain ⟨U, -, hUc, hUa, hUel⟩ := hy.exists_lbLine hc ha hA.2.1
  have hUX : U ≤ Xbar M Q Z B := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact (Xbar M Q Z B).one_mem
    obtain ⟨i, -, m, hm, rfl⟩ := hUel u hu hu1
    exact Subgroup.subset_closure (hy.mk_mem_Ebar_of_eq_conj_pow hc ha hA hm)
  refine ⟨U.subgroupOf (Xbar M Q Z B), ?_, fun u hu => ?_, fun u hu hu1 => ?_⟩
  · rw [← hUc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv
  · rw [Subgroup.mem_subgroupOf, hu]
    exact hUa ⟨a, hc.LB_le_M ha⟩ rfl
  · have hu1' : (u : Mbar M Q) ≠ 1 := fun h => hu1 (Subtype.ext h)
    obtain ⟨i, hi, m, hm, hum⟩ := hUel _ (Subgroup.mem_subgroupOf.mp hu) hu1'
    exact ⟨i, hi, m, hm, hum⟩

theorem IsLBTorus.exists_line_XbarMod {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {a : G} (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M)) :
    ∃ L : Subgroup (XbarMod M Q Z B), Nat.card L = Nat.card Z ∧ (t : XbarMod M Q Z B) ∈ L ∧
      ∀ u ∈ L, u ≠ 1 → ∃ i < Nat.card Z - 1, ∃ m : ↥M, (m : G) = y ^ i * a * (y ^ i)⁻¹ ∧
        ∃ v : ↥(Xbar M Q Z B), (v : Mbar M Q) = QuotientGroup.mk m ∧
          (v : XbarMod M Q Z B) = u := by
  obtain ⟨L, hLc, htL, hLel⟩ := hy.exists_line_Xbar hc ha hA
  obtain ⟨e, -, he, -⟩ := hc.hyp.cp
  set π := QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)) with hπ
  have hinj : Function.Injective (π.comp L.subtype) :=
    CFSG.RankThree.OddKernel.injective_restrict_of_odd π
      (by rw [hπ, QuotientGroup.ker_mk']; exact hc.odd_card_center_Xbar)
      (IsPGroup.of_card (hLc.trans he))
  refine ⟨L.map π, ?_, Subgroup.mem_map_of_mem _ (htL t ht), fun u hu hu1 => ?_⟩
  · have e1 : L.map π = (π.comp L.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e1, ← hLc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · obtain ⟨v, hvL, rfl⟩ := Subgroup.mem_map.mp hu
    have hv1 : v ≠ 1 := by
      rintro rfl
      exact hu1 (map_one _)
    obtain ⟨i, hi, m, hm, hvm⟩ := hLel v hvL hv1
    exact ⟨i, hi, m, hm, v, hvm, rfl⟩

theorem Ctx.isConj_mk_of_mem_Ebar (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {u v : ↥(Xbar M Q Z B)}
    (hu : (u : Mbar M Q) ∈ Ebar M Q Z B) (hv : (v : Mbar M Q) ∈ Ebar M Q Z B) :
    IsConj (u : XbarMod M Q Z B) (v : XbarMod M Q Z B) := by
  obtain ⟨⟨e₀, he₀, hE⟩, -⟩ := stroth112_holds G M Q Z B hc n hw hn ha2
  have hconj : ∀ w : ↥(Xbar M Q Z B), (w : Mbar M Q) ∈ Ebar M Q Z B →
      IsConj (⟨e₀, Subgroup.subset_closure he₀⟩ : ↥(Xbar M Q Z B)) w := by
    intro w hw'
    rw [hE] at hw'
    obtain ⟨x, hx, hxe⟩ := hw'
    exact isConj_iff.mpr ⟨⟨x, hx⟩, Subtype.ext hxe.symm⟩
  exact (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))).map_isConj
    ((hconj u hu).symm.trans (hconj v hv))

private theorem Ctx.exists_mem_fixA2Plane_of_mem_radical (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M))
    {S : Set (XbarMod M Q Z B)} {P R : Subgroup (XbarMod M Q Z B)}
    (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k = 1) (hPS : Subgroup.closure S = P)
    (hPt : P ≤ Subgroup.centralizer {(t : XbarMod M Q Z B)}) (hRP : R ≤ P)
    (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (hR : IsPGroup 2 R) (hRc : R ≤ ⁅P, P⁆)
    {r : XbarMod M Q Z B} (hr : r ∈ R) :
    ∃ c : ↥(Xbar M Q Z B), (c : Mbar M Q) ∈ fixA2Plane M Q Z a ∧ (c : XbarMod M Q Z B) = r := by
  have ht2 : t ^ 2 = 1 := by
    have h1 : orderOf t = 2 := by
      rw [← Subgroup.orderOf_coe, ht]
      exact Ctx.orderOf_eq_two_of_mem_Ebar (hc.mk_mem_Ebar ha hA)
    rw [← h1]
    exact pow_orderOf_eq_one t
  obtain ⟨S', P', R', hS', hP'S, hP'P, hR'R, hP't, hR'P, hR'n, hR'⟩ :=
    exists_lift_radical_of_odd_center hc.odd_card_center_Xbar ht2 hS hPS hPt hRP hRn hR
  rcases hc.forall_mem_fixA2Plane_or ha hA ht hS' hP'S hP't hR'P hR'n hR' with h | h
  · rw [← hR'R] at hr
    obtain ⟨c, hcR, rfl⟩ := Subgroup.mem_map.mp hr
    exact ⟨c, h c hcR, rfl⟩
  · have hr' := hRc hr
    rw [← hP'P, ← Subgroup.map_commutator] at hr'
    obtain ⟨c, hcP, rfl⟩ := Subgroup.mem_map.mp hr'
    exact ⟨c, h c hcP, rfl⟩

theorem IsLBTorus.commute_mk_of_radical {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {a : G} (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M))
    {S : Set (XbarMod M Q Z B)} {P R : Subgroup (XbarMod M Q Z B)}
    (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k = 1) (hPS : Subgroup.closure S = P)
    (hPt : P ≤ Subgroup.centralizer {(t : XbarMod M Q Z B)}) (hRP : R ≤ P)
    (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (hR : IsPGroup 2 R) (hRc : R ≤ ⁅P, P⁆)
    {i : ℕ} {m : ↥M} (hm : (m : G) = y ^ i * a * (y ^ i)⁻¹) {v : ↥(Xbar M Q Z B)}
    (hv : (v : Mbar M Q) = QuotientGroup.mk m) {r : XbarMod M Q Z B} (hr : r ∈ R) :
    (v : XbarMod M Q Z B) * r = r * v := by
  obtain ⟨c, hcK, rfl⟩ :=
    hc.exists_mem_fixA2Plane_of_mem_radical ha hA ht hS hPS hPt hRP hRn hR hRc hr
  have h1 := hy.commute_of_mem_fixA2Plane hc ha hA hcK hm
  rw [← hv] at h1
  have h2 : c * v = v * c := Subtype.ext h1
  have h3 := congrArg (fun g : ↥(Xbar M Q Z B) => (g : XbarMod M Q Z B)) h2
  simp only [QuotientGroup.mk_mul] at h3
  exact h3.symm

end CFSG.RankThree.GF2n.Stroth80
