module

public import CFSG.RankThree.PartOne.K159F.OuterFacts
import CFSG.RankThree.PartOne.S12.Sec159Node
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne Sec153

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAb_of_props' {p : ℕ} {F : Subgroup G} (hab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hexp : ∀ b ∈ F, b ^ p = 1) : IsElementaryAbelian p ↥F :=
  CFSG.IsElementaryAbelian.of_forall hab hexp

theorem le_E_of_elemAb3 {p : ℕ} (hp : p.Prime) {A E : Subgroup G} {c : G} {L : Subgroup G}
    (h155 : Node155) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {PW : Subgroup G}
    (hPW : IsSylowOf p PW (torusNormalizer E)) {R : Subgroup G} (hRPW : R ≤ PW)
    (hRexp : ∀ b ∈ R, b ^ p = 1) (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hRcard : p ^ 3 ≤ Nat.card R) : R ≤ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  rcases h155 G p A c L E h15 hF hout' PW hPW with hΩ | ⟨-, -, hF3, -⟩
  · intro x hx
    have : x ∈ omegaOne p PW := Subgroup.subset_closure ⟨hRPW hx, hRexp x hx⟩
    rwa [hΩ] at this
  · intro g hg
    have hRp : IsPGroup p ↥R := fun b => ⟨1, Subtype.ext (by simpa using hRexp b b.2)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hRp
    have hk3 : 3 ≤ k := by
      rw [hk] at hRcard
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hRcard
    have hdvdR : p ^ 3 ∣ Nat.card R := by
      rw [hk]; exact pow_dvd_pow p hk3
    have hzp : Nat.card ↥(Subgroup.zpowers g) ∣ p ^ 3 := by
      rw [Nat.card_zpowers]
      exact (orderOf_dvd_of_pow_eq_one (hRexp g hg)).trans (dvd_pow_self p (by norm_num))
    obtain ⟨F, hFcard, hgF, hFR⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp hzp hdvdR
      (Subgroup.zpowers_le.2 hg)
    have hFel : IsElementaryAbelian p ↥F :=
      isElemAb_of_props' (fun a ha b hb => hRab a (hFR ha) b (hFR hb))
        (fun b hb => hRexp b (hFR hb))
    exact hF3 F (hFR.trans hRPW) hFel hFcard (hgF (Subgroup.mem_zpowers g))

theorem thompsonElem_le_E {p : ℕ} (hp : p.Prime) {E PW Q : Subgroup G}
    (hEel : IsElementaryAbelian p ↥E)
    (hR : ∀ R : Subgroup G, R ≤ PW → IsElementaryAbelian p ↥R → p ^ 3 ≤ Nat.card ↥R → R ≤ E)
    (hQPW : Q ≤ PW) (hEQ : p ^ 3 ≤ Nat.card ↥(E ⊓ Q)) :
    thompsonElem p Q ≤ E ∧ ¬ IsCyclic ↥(thompsonElem p Q) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEQel : IsElementaryAbelian p ↥(E ⊓ Q) := Sec159.isElementaryAbelian_of_le hEel inf_le_left
  let S : Set (Subgroup G) := {F' | F' ≤ Q ∧ IsElementaryAbelian p ↥F' ∧ p ^ 3 ≤ Nat.card ↥F'}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨E ⊓ Q, inf_le_right, hEQel, hEQ⟩
  obtain ⟨F₀, ⟨hF₀Q, hF₀e, hF₀c⟩, hF₀max⟩ :=
    Set.exists_max_image S (fun F' => Nat.card ↥F') hSfin hSne
  have hmaxall : ∀ F' : Subgroup G, F' ≤ Q → IsElementaryAbelian p ↥F' →
      Nat.card ↥F' ≤ Nat.card ↥F₀ := by
    intro F' hF'Q hF'e
    by_cases h : p ^ 3 ≤ Nat.card ↥F'
    · exact hF₀max F' ⟨hF'Q, hF'e, h⟩
    · exact (Nat.lt_of_not_le h).le.trans hF₀c
  have hJE : thompsonElem p Q ≤ E := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨F, hFQ, hFe, hFmax, hxF⟩
    have hc : p ^ 3 ≤ Nat.card ↥F := hEQ.trans (hFmax (E ⊓ Q) inf_le_right hEQel)
    have hFE : F ≤ E := by
      have := hFe
      refine hR F (hFQ.trans hQPW) hFe hc
    exact hFE hxF
  refine ⟨hJE, fun hcyc => ?_⟩
  have hF₀J : F₀ ≤ thompsonElem p Q := fun x hx =>
    Subgroup.subset_closure ⟨F₀, hF₀Q, hF₀e, hmaxall, hx⟩
  have hexp : ∀ u ∈ thompsonElem p Q, u ^ p = 1 := fun u hu =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) u (hJE hu)
  have hdvd := Sec159Node.card_dvd_of_isCyclic_exp hcyc hexp
  have h1 : Nat.card ↥F₀ ≤ Nat.card ↥(thompsonElem p Q) := Subgroup.card_le_of_le hF₀J
  have h2 : Nat.card ↥(thompsonElem p Q) ≤ p := Nat.le_of_dvd hp.pos hdvd
  have h3 : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem card_inf_ge_of_moved {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G 5 A c L E)
    (M : ModData 5 E) (hEcard : Nat.card ↥E = 5 ^ 4) {Q : Subgroup G}
    (hQE : ∀ u ∈ E, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q) {y : G} (hyQ : y ∈ Q)
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) {a : ℕ} (hpow : conjAut E y hyN ^ (5 ^ a) = 1)
    (hne : conjAut E y hyN ≠ 1) : 5 ^ 3 ≤ Nat.card ↥(E ⊓ Q) := by
  classical
  have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  set φ : MulAut ↥E := conjAut E y hyN with hφ
  let f : ↥E →* ↥E := MonoidHom.mk' (fun u => φ u * u⁻¹) (by
    intro a b
    rw [map_mul]
    calc φ a * φ b * (a * b)⁻¹ = φ a * (φ b * b⁻¹) * a⁻¹ := by group
      _ = φ a * (a⁻¹ * (φ b * b⁻¹)) := by
        rw [mul_assoc, hEc (φ b * b⁻¹) a⁻¹]
      _ = φ a * a⁻¹ * (φ b * b⁻¹) := by group)
  have hker : Nat.card ↥f.ker ≤ 5 := by
    have h1 := K159F.outer_facts' h M hyN hpow hne
    have h2 : Nat.card ↥f.ker = Nat.card {u : ↥E // conjAut E y hyN u = u} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun u => by
        simp [MonoidHom.mem_ker, f, mul_inv_eq_one, hφ]))
    rw [h2]; exact h1
  have h1 := Subgroup.card_ker_mul_card_range f
  have hrange : Nat.card ↥f.range ≤ Nat.card ↥(E ⊓ Q) := by
    have hle : f.range.map E.subtype ≤ E ⊓ Q := by
      rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨(f u).2, ?_⟩
      have h2 : (((φ u * u⁻¹ : ↥E)) : G) = y * ((u : G) * y⁻¹ * (u : G)⁻¹) := by
        have := Equivariance.coe_conjAut hyN u
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hφ, this]; group
      have h3 : (u : G) * y⁻¹ * (u : G)⁻¹ ∈ Q := hQE u u.2 y⁻¹ (Q.inv_mem hyQ)
      show (((φ u * u⁻¹ : ↥E)) : G) ∈ Q
      rw [h2]
      exact Q.mul_mem hyQ h3
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective E.subtype_injective] at this
  rw [hEcard] at h1
  have h4 : 5 ^ 4 ≤ 5 * Nat.card ↥f.range := by
    rw [← h1]; exact Nat.mul_le_mul_right _ hker
  have h5 : 5 ^ 3 ≤ Nat.card ↥f.range := by
    have h6 : 5 * 5 ^ 3 ≤ 5 * Nat.card ↥f.range := by
      calc 5 * 5 ^ 3 = 5 ^ 4 := by norm_num
        _ ≤ _ := h4
    exact Nat.le_of_mul_le_mul_left h6 (by norm_num)
  exact h5.trans hrange

end CFSG.RankThree.PartOne.K1510R
