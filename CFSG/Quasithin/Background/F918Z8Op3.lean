module

public import CFSG.Quasithin.Background.F918Z8Op0
public import CFSG.Quasithin.Background.F918Z8Op1
public import CFSG.Quasithin.Background.F918Z8Op2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem opq_core {G : Type*} [Group G] [Finite G] {M : Subgroup G} (hS : IsQuotientOfSQTKTC ↥M)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L L' : Subgroup G} (hLM : L ≤ M) (hL'M : L' ≤ M)
    (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hLc : ∀ a ∈ L, (∀ b ∈ L, a * b = b * a) → a = 1)
    (hpL : p ∣ Nat.card L) (hpL' : p ∣ Nat.card L') (hL : InvSylAll L p) (hL' : InvSylAll L' p)
    {g : G} (hgM : g ∈ M) (hg : ∀ x ∈ L, g * x = x * g)
    (hgn : ∀ x ∈ L', g * x * g⁻¹ ∈ L') (hgp : ∃ k : ℕ, g ^ (p ^ k) = 1) : g ∈ L' := by
  by_contra hgL'
  have hp : p.Prime := Fact.out
  obtain ⟨P, hPL, hPp, m, hm, hpm⟩ : ∃ P : Subgroup G, P ≤ L ∧ IsPGroup p P ∧
      ∃ m : ℕ, Nat.card L = Nat.card P * m ∧ ¬ p ∣ m := by
    obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p ↥L))
    refine ⟨(P₀ : Subgroup ↥L).map L.subtype, Subgroup.map_subtype_le _,
      P₀.isPGroup'.map L.subtype, Nat.card L / p ^ ((Nat.card L).factorization p), ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective L.subtype_injective, Sylow.card_eq_multiplicity]
      exact (Nat.ordProj_mul_ordCompl_eq_self (Nat.card L) p).symm
    · exact Nat.not_dvd_ordCompl hp Nat.card_pos.ne'
  have hpP : p ∣ Nat.card P := by
    rw [hm] at hpL
    exact (hp.dvd_mul.mp hpL).resolve_right hpm
  obtain ⟨τ, hτL, hτ2, hτP⟩ := hL P hPL hPp ⟨m, hm, hpm⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) p hpP
  have hyP : (y : G) ∈ P := y.2
  have hyL : (y : G) ∈ L := hPL y.2
  have hyo : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe]; exact hy
  obtain ⟨Q, hQp, hgQ, hQle, m', hm', hpm'⟩ := opq_sylow_glue hgn hgp
  have hQc : ∀ r ∈ Q, ∀ a ∈ L, r * a = a * r := by
    intro r hr a ha
    have hcentral : L' ⊔ Subgroup.zpowers g ≤ Subgroup.centralizer (L : Set G) := by
      refine sup_le ?_ ?_
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hcomm a ha b hb
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro a ha
        exact (hg a ha).symm
    exact ((Subgroup.mem_centralizer_iff.mp (hcentral (hQle hr))) a ha).symm
  have hQM : Q ≤ M := by
    refine hQle.trans (sup_le hL'M ?_)
    rw [Subgroup.zpowers_le]
    exact hgM
  have hdisj : ∀ r ∈ Q, r ∈ Subgroup.zpowers (y : G) → r = 1 := by
    intro r hrQ hry
    have hrL : r ∈ L := (Subgroup.zpowers_le.mpr hyL) hry
    exact hLc r hrL (fun b hb => hQc r hrQ b hb)
  have hcyc : IsCyclic ↥Q :=
    opq_cyclic_of_inverting hS hp2 (hLM hyL) (hLM hτL) hyo hτ2 (hτP _ hyP) hQM hQp
      (fun r hr => hQc r hr _ hyL) (fun r hr => hQc r hr _ hτL) hdisj
  have hgnorm : g ∈ Subgroup.normalizer (L' : Set G) := Subgroup.mem_normalizer_fintype hgn
  have hnorm : L' ⊔ Subgroup.zpowers g ≤ Subgroup.normalizer (L' : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hgnorm)
  set Pt : Subgroup G := Q ⊓ L' with hPt
  have hPtQ : Pt ≤ Q := inf_le_left
  have hPtL' : Pt ≤ L' := inf_le_right
  have hPtp : IsPGroup p Pt := IsPGroup.to_le hQp hPtQ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hPtp
  have hpPt : p ∣ Nat.card Pt := by
    rw [hm'] at hpL'
    exact (hp.dvd_mul.mp hpL').resolve_right hpm'
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0] at he
      rw [he] at hpPt
      exact absurd (Nat.dvd_one.mp (by simpa using hpPt)) hp.ne_one
    · exact h0
  have hen : e < n := by
    have hle : Nat.card Pt ≤ Nat.card Q := Subgroup.card_le_of_le hPtQ
    rw [he, hn] at hle
    have hle' : e ≤ n := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    rcases Nat.lt_or_ge e n with h | h
    · exact h
    · exfalso
      have hen' : e = n := le_antisymm hle' h
      have hcard : Nat.card Q ≤ Nat.card Pt := by rw [he, hn, hen']
      have hQP : Q = Pt := (Subgroup.eq_of_le_of_card_ge hPtQ hcard).symm
      apply hgL'
      have : g ∈ Pt := by rw [← hQP]; exact hgQ
      exact this.2
  obtain ⟨s', hs'⟩ : ∃ s', n = e + (s' + 1) := ⟨n - e - 1, by omega⟩
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := ↥Q)
  have hqord : orderOf q = p ^ n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hq]
    exact hn
  set g₁ : G := ((q ^ (p ^ s') : ↥Q) : G) with hg₁
  set w : G := ((q ^ (p ^ (s' + 1)) : ↥Q) : G) with hw
  have hg₁Q : g₁ ∈ Q := (q ^ (p ^ s') : ↥Q).2
  have hg₁p : g₁ ^ p = w := by
    have : (q ^ (p ^ s')) ^ p = q ^ (p ^ (s' + 1)) := by
      rw [← pow_mul, ← pow_succ]
    rw [hg₁, hw, ← Subgroup.coe_pow, this]
  have hg₁n : ∀ x ∈ L', g₁ * x * g₁⁻¹ ∈ L' := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hnorm (hQle hg₁Q)) x).mp hx
  have hwordQ : orderOf (q ^ (p ^ (s' + 1))) = p ^ e := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero)
      (by rw [hqord]; exact pow_dvd_pow p (by omega)), hqord]
    rw [hs', pow_add, Nat.mul_div_cancel _ (pow_pos hp.pos _)]
  have hword : orderOf w = p ^ e := by
    rw [hw, Subgroup.orderOf_coe]
    exact hwordQ
  have hwPt : w ∈ Pt := by
    have hH : (Pt.subgroupOf Q) = Subgroup.zpowers (q ^ (p ^ (s' + 1))) := by
      have : Finite (Pt.subgroupOf Q) := inferInstance
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, hwordQ,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPtQ).toEquiv, he]
    have hmem : q ^ (p ^ (s' + 1)) ∈ Pt.subgroupOf Q := by
      rw [hH]; exact Subgroup.mem_zpowers _
    exact Subgroup.mem_subgroupOf.mp hmem
  have hsyl : ¬ p ^ (e + 1) ∣ Nat.card L' := by
    intro hd
    rw [hm', he, pow_succ] at hd
    exact hpm' (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos e) hd)
  obtain ⟨τt, hτtL, hτt2, hτtP⟩ := hL' Pt hPtL' hPtp ⟨m', hm', hpm'⟩
  exact opq_sylow_trick hp2 he1 hg₁n hg₁p (hPtL' hwPt) hword hsyl hτtL hτt2 (hτtP w hwPt)


end CFSG.Quasithin
