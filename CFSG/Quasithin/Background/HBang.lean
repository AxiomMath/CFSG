module

public import CFSG.Quasithin.Background.HDefs
public import CFSG.Quasithin.Background.A1cA131

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open

theorem mem_of_isPGroup_of_index_two {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {E : Subgroup Q} [E.Normal] (hidx : E.index = 2) {P : Subgroup Q}
    (hP : IsPGroup p P) : P ≤ E := by
  intro y hy
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  have hk' : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  by_contra hyE
  have hq : (QuotientGroup.mk y : Q ⧸ E) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have hcard : Nat.card (Q ⧸ E) = 2 := by rw [← Subgroup.index_eq_card, hidx]
  have h2 : orderOf (QuotientGroup.mk y : Q ⧸ E) = 2 := by
    have h1 : orderOf (QuotientGroup.mk y : Q ⧸ E) ∣ 2 := hcard ▸ orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hq
    · exact h
  have h3 : orderOf (QuotientGroup.mk y : Q ⧸ E) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  rw [h2] at h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).mp
    (Nat.prime_two.dvd_of_dvd_pow h3)
  exact hp2 this.symm

variable {V : Type*} [CommGroup V]

@[expose] def extInv (E : Subgroup (MulAut V)) (s : MulAut V) (hs2 : s ^ 2 = 1)
    (hsE : s ∈ Subgroup.normalizer (E : Set (MulAut V))) : Subgroup (MulAut V) where
  carrier := {g | g ∈ E ∨ g * s ∈ E}
  one_mem' := Or.inl E.one_mem
  mul_mem' := by
    have hss : s * s = 1 := by rw [← sq, hs2]
    have hconj : ∀ e ∈ E, s * e * s ∈ E := fun e he => by
      have := (Subgroup.mem_normalizer_iff.mp hsE e).mp he
      rwa [show s⁻¹ = s from inv_eq_of_mul_eq_one_right hss] at this
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (E.mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact E.mul_mem ha hb)
    · refine Or.inr ?_
      have : a * b * s = (a * s) * (s * b * s) := by
        rw [show (a * s) * (s * b * s) = a * (s * s) * b * s by group, hss, mul_one]
      rw [this]
      exact E.mul_mem ha (hconj b hb)
    · refine Or.inl ?_
      have : a * b = (a * s) * (s * (b * s) * s) := by
        rw [show (a * s) * (s * (b * s) * s) = a * (s * s) * b * (s * s) by group, hss, mul_one,
          mul_one]
      rw [this]
      exact E.mul_mem ha (hconj _ hb)
  inv_mem' := by
    have hss : s * s = 1 := by rw [← sq, hs2]
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    rintro a (ha | ha)
    · exact Or.inl (E.inv_mem ha)
    · refine Or.inr ?_
      have h1 : a⁻¹ * s = s * (a * s)⁻¹ * s := by
        rw [mul_inv_rev, hsinv, ← mul_assoc s s, hss, one_mul]
      rw [h1]
      have := (Subgroup.mem_normalizer_iff.mp hsE _).mp (E.inv_mem ha)
      rwa [hsinv] at this

theorem isCyclic_inf_centralizer_of_hypBang [Finite V] {M : Subgroup (MulAut V)}
    (hM : HypBang M) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E : Subgroup (MulAut V)}
    (hEM : E ≤ M) (hE : IsElemAbelian p E) {s : MulAut V} (hsM : s ∈ M) (hs2 : s ^ 2 = 1)
    (hsE : s ∈ Subgroup.normalizer (E : Set (MulAut V)))
    (hsc : s ∉ Subgroup.centralizer (E : Set (MulAut V))) :
    IsCyclic ↥(E ⊓ Subgroup.centralizer ({s} : Set (MulAut V))) := by
  classical
  have : Finite (MulAut V) := MulEquiv.finite_left
  obtain ⟨Y, _, _, hY, φ, hφ⟩ := hM
  have hss : s * s = 1 := by rw [← sq, hs2]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hconj : ∀ e ∈ E, s * e * s ∈ E := fun e he => by
    have := (Subgroup.mem_normalizer_iff.mp hsE e).mp he
    rwa [hsinv] at this
  set H := extInv E s hs2 hsE with hHdef
  have hEH : E ≤ H := fun e he => Or.inl he
  have hsH : s ∈ H := Or.inr (by rw [hss]; exact E.one_mem)
  have hHM : H ≤ M := by
    rintro g (hg | hg)
    · exact hEM hg
    · have : g = (g * s) * s := by rw [mul_assoc, hss, mul_one]
      rw [this]
      exact M.mul_mem (hEM hg) hsM
  have hsnE : s ∉ E := by
    intro hs
    apply hsc
    have hsp : s ^ p = 1 := hE.2 s hs
    have hs1 : s = 1 := by
      have h1 : orderOf s ∣ p := orderOf_dvd_of_pow_eq_one hsp
      have h2 : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one hs2
      have h3 : orderOf s ∣ Nat.gcd p 2 := Nat.dvd_gcd h1 h2
      rw [(Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2] at h3
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    rw [hs1]
    exact Subgroup.one_mem _
  have hpel : ∀ y ∈ H, ∀ k : ℕ, y ^ p ^ k = 1 → y ∈ E := by
    rintro y (hy | hy) k hk
    · exact hy
    · exfalso
      have hsy : s * y ∈ E := by
        have : s * y = s * (y * s) * s := by rw [mul_assoc, mul_assoc, hss, mul_one]
        rw [this]
        exact hconj _ hy
      have hpow : ∀ j : ℕ, y ^ (2 * j) ∈ E ∧ y ^ (2 * j + 1) * s ∈ E := by
        intro j
        induction j with
        | zero => exact ⟨by simp, by simpa using hy⟩
        | succ j ih =>
          have h1 : y ^ (2 * (j + 1)) = (y ^ (2 * j + 1) * s) * (s * y) := by
            rw [show (y ^ (2 * j + 1) * s) * (s * y) = y ^ (2 * j + 1) * (s * s) * y by group,
              hss, mul_one, ← pow_succ, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
          have h2 : y ^ (2 * (j + 1) + 1) * s = y ^ (2 * (j + 1)) * (y * s) := by
            rw [pow_succ, mul_assoc]
          refine ⟨?_, ?_⟩
          · rw [h1]
            exact E.mul_mem ih.2 hsy
          · rw [h2, h1]
            exact E.mul_mem (E.mul_mem ih.2 hsy) hy
      obtain ⟨j, hj⟩ : ∃ j, p ^ k = 2 * j + 1 := by
        have hodd : Odd (p ^ k) := ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
        exact hodd
      have := (hpow j).2
      rw [← hj, hk, one_mul] at this
      exact hsnE this
  set Q := ↥H
  have hEn : (E.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hEH]
    rintro g (hg | hg)
    · exact Subgroup.le_normalizer hg
    · have : g = (g * s) * s := by rw [mul_assoc, hss, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer hg) hsE
  have hEp : IsPGroup p ↥(E.subgroupOf H) := by
    intro x
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hE.2 _ x.2))⟩
  have hcore : CFSG.Open.pCore p Q = E.subgroupOf H := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup p (G := Q) ⟨y, hy⟩
      have hQ : y ^ p ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hk' : (y : MulAut V) ^ p ^ k = 1 := by
        rw [← Subgroup.coe_pow, hQ]
        rfl
      exact hpel y y.2 k hk'
    · exact CFSG.LieType.BorelTits.le_pCore p hEn hEp
  have hF : Subgroup.centralizer (CFSG.Open.pCore p Q : Set Q) ≤ CFSG.Open.pCore p Q := by
    rw [hcore]
    rintro ⟨y, hyH⟩ hy
    rcases hyH with hyE | hyE
    · exact hyE
    · exfalso
      apply hsc
      have hyc : y ∈ Subgroup.centralizer (E : Set (MulAut V)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have := Subgroup.mem_centralizer_iff.mp hy ⟨e, hEH he⟩ he
        exact congrArg Subtype.val this
      have hec : y * s ∈ Subgroup.centralizer (E : Set (MulAut V)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have := @mul_comm' (↥E) _ hE.1 ⟨e, he⟩ ⟨y * s, hyE⟩
        exact congrArg Subtype.val this
      have : s = y⁻¹ * (y * s) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyc) hec
  let ψ : Y →* MulAut V := M.subtype.comp φ
  let G : Subgroup Y := H.comap ψ
  let φ' : ↥G →* Q := (ψ.comp G.subtype).codRestrict H fun y => y.2
  have hφ' : Function.Surjective φ' := by
    rintro ⟨h, hh⟩
    obtain ⟨y, hy⟩ := hφ ⟨h, hHM hh⟩
    have hyG : y ∈ G := by
      change ψ y ∈ H
      change (M.subtype (φ y)) ∈ H
      rw [hy]
      exact hh
    exact ⟨⟨y, hyG⟩, Subtype.ext (by
      change M.subtype (φ y) = h
      rw [hy]
      rfl)⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥G) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp1 G.subtype G.subtype_injective).trans
      (hY.1 p (Fact.out : p.Prime) hp2)
  have hconcl := A1c.A131Concl_of_surjective hp2 hF (Nat.card ↥G) ↥G φ' hφ' rfl hrk
  let T : Subgroup Q := (Subgroup.zpowers s).subgroupOf H
  have hT : IsPGroup 2 T := by
    intro x
    obtain ⟨x, hx⟩ := x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    change (x : MulAut V) ^ 2 ^ 1 = 1
    have hk' : (x : MulAut V) = s ^ k := hk.symm
    rw [hk', pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs2,
      one_zpow]
  have hT1 : T ≠ ⊥ := by
    intro h
    have : (⟨s, hsH⟩ : Q) ∈ T := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers s)
    rw [h, Subgroup.mem_bot] at this
    apply hsnE
    rw [show s = 1 from congrArg Subtype.val this]
    exact E.one_mem
  have hcyc := hconcl.1 T hT hT1
  rw [hcore] at hcyc
  let ι : ↥(E ⊓ Subgroup.centralizer ({s} : Set (MulAut V))) →*
      ↥(E.subgroupOf H ⊓ Subgroup.centralizer (T : Set Q)) :=
    { toFun := fun x => ⟨⟨x.1, hEH (Subgroup.mem_inf.mp x.2).1⟩, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp x.2).1, by
          rw [Subgroup.mem_centralizer_iff]
          rintro ⟨t, htH⟩ ht
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp ht)
          apply Subtype.ext
          change t * x.1 = x.1 * t
          have hk' : t = s ^ k := hk.symm
          rw [hk']
          have hxs : x.1 * s = s * x.1 := by
            have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2 s
              (Set.mem_singleton s)
            exact this.symm
          exact Commute.zpow_left (show Commute s x.1 from hxs.symm) k⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b h => by
    apply Subtype.ext
    have := congrArg (fun z => ((z.1 : Q) : MulAut V)) h
    exact this
  exact isCyclic_of_injective ι hι

end H

end CFSG.Quasithin
