module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16n9b_exists_pgroup_card_ge {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime)
    {A E : Subgroup Γ} (hA : IsPGroup p A) (hE : IsPGroup p E) (hAc : Nat.card A = p ^ 3)
    (hEc : p ^ 3 ≤ Nat.card E) (hAn : ∃ a b : A, a * b ≠ b * a)
    (hEa : ∀ a b : E, a * b = b * a) :
    ∃ P : Subgroup Γ, IsPGroup p P ∧ p ^ 4 ≤ Nat.card P := by
  haveI := Fact.mk hp
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  have hPQ : Nat.card P = Nat.card Q := by
    rw [P.card_eq_multiplicity, Q.card_eq_multiplicity]
  refine ⟨P, P.isPGroup', ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 : p ^ 3 ≤ Nat.card P := hAc ▸ Subgroup.card_le_of_le hAP
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hP3 : Nat.card P = p ^ 3 := by
    rw [hn] at h1 hlt ⊢
    have h3n : 3 ≤ n := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    have hn4 : n < 4 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
    have : n = 3 := by omega
    rw [this]
  have hEeq : E = (Q : Subgroup Γ) :=
    Subgroup.eq_of_le_of_card_ge hEQ (by rw [← hPQ, hP3]; exact hEc)
  have hQcomm : ∀ x y : (Q : Subgroup Γ), x * y = y * x := fun x y => by
    have h' : (x : Γ) * y = y * x :=
      congrArg Subtype.val (hEa ⟨x, hEeq ▸ x.2⟩ ⟨y, hEeq ▸ y.2⟩)
    exact Subtype.ext h'
  obtain ⟨a, b, hab⟩ := hAn
  let φ : (P : Subgroup Γ) ≃* (Q : Subgroup Γ) := Sylow.equiv P Q
  apply hab
  have h2 : φ ⟨a, hAP a.2⟩ * φ ⟨b, hAP b.2⟩ = φ ⟨b, hAP b.2⟩ * φ ⟨a, hAP a.2⟩ := hQcomm _ _
  rw [← map_mul, ← map_mul] at h2
  have h3 := φ.injective h2
  exact Subtype.ext (congrArg (fun x : (P : Subgroup Γ) => (x : Γ)) h3)

theorem s16n9b_exists_fix_of_card_gt {T : Type*} [CommGroup T] [Finite T] {p : ℕ} (hp : p.Prime)
    {P : Subgroup (MulAut T)} (hP : IsPGroup p P) (hcard : Nat.card T - 1 < Nat.card P)
    {z : T} (hz : z ≠ 1) : ∃ ψ ∈ P, orderOf ψ = p ∧ ψ z = z := by
  classical
  haveI := Fact.mk hp
  haveI : Finite (MulAut T) :=
    Finite.of_injective (fun f : MulAut T => (f : T → T)) DFunLike.coe_injective
  let S : Subgroup ↥P := MulAction.stabilizer ↥P z
  have hidx : S.index = Nat.card (MulAction.orbit ↥P z) := MulAction.index_stabilizer ↥P z
  have h1 : Nat.card S * S.index = Nat.card P := Subgroup.card_mul_index S
  have horb : Nat.card (MulAction.orbit ↥P z) ≤ Nat.card T - 1 := by
    have hsub : MulAction.orbit ↥P z ⊆ ({1}ᶜ : Set T) := by
      rintro _ ⟨g, rfl⟩ h
      apply hz
      have : (g : MulAut T) z = 1 := h
      have h2 := (g : MulAut T).injective (this.trans (map_one (g : MulAut T)).symm)
      exact h2
    calc Nat.card (MulAction.orbit ↥P z) = (MulAction.orbit ↥P z).ncard :=
        Nat.card_coe_set_eq _
      _ ≤ ({1}ᶜ : Set T).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card T - 1 := by rw [Set.ncard_compl, Set.ncard_singleton]
  have hS : 2 ≤ Nat.card S := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < Nat.card S := Nat.card_pos
    have h2 : Nat.card S = 1 := by omega
    rw [h2, one_mul, hidx] at h1
    omega
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hP.to_subgroup S)
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, pow_zero] at hj
      omega
    · exact h0
  have hdvd : p ∣ Nat.card S := by
    rw [hj]
    exact dvd_pow_self p (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨((x : ↥P) : MulAut T), (x : ↥P).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx
  · have := x.2
    exact MulAction.mem_stabilizer_iff.mp this

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case3_fix (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLM : L ≤ D.M) (h3 : Case168_3 D V₀ V hV L)
    (hge : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV)) :
    ∀ z : Vtil V₀ V hV, z ≠ 1 → ∃ ψ ∈ Mbar D.M V₀ V hV, orderOf ψ = 3 ∧ ψ z = z := by
  classical
  intro z hz
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hMb
  have hLb : lBar V₀ V hV L ≤ Mb := barSub_mono V₀ V hV hLM
  have hAc : Nat.card (lBar V₀ V hV L) = 3 ^ 3 := h3.1.2.1
  have hnc : ∃ a b : ↥(lBar V₀ V hV L), a * b ≠ b * a := by
    haveI := h3.1.1
    haveI := CFSG.IsExtraspecial.quotient_nontrivial 3 ↥(lBar V₀ V hV L)
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(lBar V₀ V hV L) ⧸ Subgroup.center ↥(lBar V₀ V hV L))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have ha : a ∉ Subgroup.center ↥(lBar V₀ V hV L) := fun h =>
      hx ((QuotientGroup.eq_one_iff a).2 h)
    rw [Subgroup.mem_center_iff] at ha
    push Not at ha
    obtain ⟨b, hb⟩ := ha
    exact ⟨a, b, fun h => hb h.symm⟩
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) Mb
  have h27 : 3 ^ 3 ≤ Nat.card (E.subgroupOf Mb) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hEcard]
    exact Nat.pow_le_pow_right (by norm_num) hge
  have hA₀c : Nat.card ((lBar V₀ V hV L).subgroupOf Mb) = 3 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLb).toEquiv]
    exact hAc
  have hA₀n : ∃ a b : ↥((lBar V₀ V hV L).subgroupOf Mb), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨(Subgroup.subgroupOfEquivOfLe hLb).symm a, (Subgroup.subgroupOfEquivOfLe hLb).symm b,
      fun h => hab ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact (Subgroup.subgroupOfEquivOfLe hLb).symm.injective h
  have hE' : IsElemAbelian 3 (E.subgroupOf Mb) := CFSG.Open.IsElemAbelian.subgroupOf hE Mb
  obtain ⟨P₀, hP₀p, hP₀c⟩ := s16n9b_exists_pgroup_card_ge Nat.prime_three
    (IsPGroup.of_card hA₀c) (CFSG.Open.IsElemAbelian.isPGroup hE') hA₀c h27 hA₀n
    (fun a b => hE'.1.is_comm.comm a b)
  have hPp : IsPGroup 3 (P₀.map Mb.subtype) := hP₀p.map Mb.subtype
  have hPc : 3 ^ 4 ≤ Nat.card (P₀.map Mb.subtype) := by
    rw [Subgroup.card_map_of_injective Mb.subtype_injective]
    exact hP₀c
  have hT : ∀ v : Vtil V₀ V hV, v ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hVc : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
    rw [← Subgroup.card_top (G := Vtil V₀ V hV), card_eq_two_pow hT ⊤, h3.2.1]
  have hcard : Nat.card (Vtil V₀ V hV) - 1 < Nat.card (P₀.map Mb.subtype) := by
    rw [hVc]
    calc 2 ^ 6 - 1 < 3 ^ 4 := by norm_num
      _ ≤ _ := hPc
  obtain ⟨ψ, hψP, hψo, hψz⟩ := s16n9b_exists_fix_of_card_gt Nat.prime_three hPp hcard hz
  exact ⟨ψ, Subgroup.map_subtype_le P₀ hψP, hψo, hψz⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
