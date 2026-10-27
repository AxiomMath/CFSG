module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTwo
public import CFSG.Sporadic.Schreier.RuElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {T : Type*} [CommGroup T]

theorem s16n9b_map_conj_pow_fixed (X : Subgroup (MulAut T)) {x : MulAut T}
    (hx : X.map (MulAut.conj x).toMonoidHom = X) (k : ℕ) :
    X.map (MulAut.conj (x ^ k)).toMonoidHom = X := by
  induction k with
  | zero => rw [pow_zero]; exact s16n9b_map_conj_one X
  | succ k ih => rw [pow_succ', ← s16n9b_map_conj_map_conj X (x ^ k) x, ih, hx]

theorem s16n9b_two_normalizes_of_odd {M A : Subgroup (MulAut T)} {g : MulAut T}
    (h : S16n9bTwo M A g) {e : MulAut T} (he : e ∈ M) {n : ℕ} (hn : Odd n) (hen : e ^ n = 1) :
    A.map (MulAut.conj e).toMonoidHom = A := by
  by_contra hne
  obtain ⟨m, hm⟩ := hn
  have hAe : A.map (MulAut.conj e).toMonoidHom = A.map (MulAut.conj g).toMonoidHom :=
    (h.conj e he).resolve_left hne
  have hone : A.map (MulAut.conj (e ^ n)).toMonoidHom = A := by
    rw [hen]
    exact s16n9b_map_conj_one A
  have hBe : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj e).toMonoidHom =
      A.map (MulAut.conj (e * g)).toMonoidHom := s16n9b_map_conj_map_conj A g e
  rcases h.conj (e * g) (M.mul_mem he h.mem) with h1 | h1
  ·
    have h2 : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (e ^ 2)).toMonoidHom =
        A.map (MulAut.conj g).toMonoidHom := by
      rw [sq, ← s16n9b_map_conj_map_conj _ e e, hBe, h1, hAe]
    have h3 := s16n9b_map_conj_pow_fixed _ h2 m
    apply h.ne
    calc A.map (MulAut.conj g).toMonoidHom
        = (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj ((e ^ 2) ^ m)).toMonoidHom :=
          h3.symm
      _ = (A.map (MulAut.conj e).toMonoidHom).map (MulAut.conj ((e ^ 2) ^ m)).toMonoidHom := by
          rw [hAe]
      _ = A.map (MulAut.conj ((e ^ 2) ^ m * e)).toMonoidHom := s16n9b_map_conj_map_conj A e _
      _ = A.map (MulAut.conj (e ^ n)).toMonoidHom := by rw [hm, pow_succ e (2 * m), pow_mul]
      _ = A := hone
  ·
    have key : ∀ k : ℕ, A.map (MulAut.conj (e ^ (k + 1))).toMonoidHom =
        A.map (MulAut.conj g).toMonoidHom := by
      intro k
      induction k with
      | zero => rw [zero_add, pow_one]; exact hAe
      | succ k ih =>
        rw [pow_succ', ← s16n9b_map_conj_map_conj A (e ^ (k + 1)) e, ih, hBe]
        exact h1
    have h2 := key (2 * m)
    rw [← hm, hone] at h2
    exact h.ne h2.symm

theorem s16n9b_two_normalizes_conj {M A : Subgroup (MulAut T)} {g : MulAut T}
    (h : S16n9bTwo M A g) {φ : MulAut T} (hφM : φ ∈ M)
    (hA : A.map (MulAut.conj φ).toMonoidHom = A) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom := by
  rw [s16n9b_map_conj_map_conj]
  rcases h.conj (φ * g) (M.mul_mem hφM h.mem) with h1 | h1
  · exfalso
    apply h.ne
    have h2 : A.map (MulAut.conj φ⁻¹).toMonoidHom = A := by
      have := congrArg (fun X : Subgroup (MulAut T) => X.map (MulAut.conj φ⁻¹).toMonoidHom) hA
      simp only [s16n9b_map_conj_map_conj, inv_mul_cancel, s16n9b_map_conj_one] at this
      exact this.symm
    calc A.map (MulAut.conj g).toMonoidHom
        = (A.map (MulAut.conj (φ * g)).toMonoidHom).map (MulAut.conj φ⁻¹).toMonoidHom := by
          rw [s16n9b_map_conj_map_conj, inv_mul_cancel_left]
      _ = A.map (MulAut.conj φ⁻¹).toMonoidHom := by rw [h1]
      _ = A := h2
  · exact h1

theorem s16n9b_card_le_mul_card_inf_centSub [Finite T] {p : ℕ} (hp : p.Prime)
    {E : Subgroup (MulAut T)} {a : ℕ} (hE : Nat.card E = p ^ a) {W : Subgroup T}
    (hEW : E ≤ stabSub W) {m : ℕ} (hm : Nat.card (MulAut ↥W) = m) (hpm : ¬ p ^ 2 ∣ m) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ centSub W) := by
  haveI : Finite (MulAut ↥W) :=
    Finite.of_injective (fun f : MulAut ↥W => (f : ↥W → ↥W)) DFunLike.coe_injective
  have h := card_autSub_mul hEW
  have hd1 : Nat.card (autSub E W) ∣ p ^ a := hE ▸ Dvd.intro _ h
  have hd2 : Nat.card (autSub E W) ∣ m := hm ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, -, hiE⟩ := (Nat.dvd_prime_pow hp).1 hd1
  have hi1 : i ≤ 1 := by
    by_contra hlt
    push Not at hlt
    exact hpm ((Nat.pow_dvd_pow p hlt).trans (hiE ▸ hd2))
  have hle : Nat.card (autSub E W) ≤ p := by
    rw [hiE]
    calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hi1
      _ = p := pow_one p
  calc Nat.card E = Nat.card (autSub E W) * Nat.card ↥(E ⊓ centSub W) := h.symm
    _ ≤ p * Nat.card ↥(E ⊓ centSub W) := Nat.mul_le_mul_right _ hle

theorem s16n9b_card_mulAut_rank_three [Finite T] (hT : ∀ v : T, v ^ 2 = 1) {W : Subgroup T}
    (hW : rk ↥W = 3) : Nat.card (MulAut ↥W) = 168 := by
  have h8 : Nat.card ↥W = 8 := by
    rw [card_eq_two_pow hT W, hW]
    norm_num
  exact CFSG.Sporadic.RuSchreier.ru_card_mulAut_eight (fun a b => mul_comm a b)
    (fun a => Subtype.ext (by simpa using hT a)) h8

theorem s16n9b_card_le_forty_nine [Finite T] (hT : ∀ v : T, v ^ 2 = 1) {M A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo M A g) (hrk : rk ↥(commSub ⊤ A) = 3)
    {E : Subgroup (MulAut T)} (hEM : E ≤ M) (hE7 : ∀ e ∈ E, e ^ 7 = 1) {a : ℕ}
    (hEcard : Nat.card E = 7 ^ a) : Nat.card E ≤ 49 := by
  have hA : ∀ e ∈ E, A.map (MulAut.conj e).toMonoidHom = A := fun e he =>
    s16n9b_two_normalizes_of_odd h (hEM he) (n := 7) (by decide) (hE7 e he)
  have hstW : E ≤ stabSub (commSub ⊤ A) := by
    intro e he
    apply s16n9b_mem_stabSub_of_map_eq
    rw [← s15_Infra_commSub_top_map_conj A e, hA e he]
  have hgB : commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) = (commSub ⊤ A).map g.toMonoidHom :=
    s15_Infra_commSub_top_map_conj A g
  have hstW' : E ≤ stabSub ((commSub ⊤ A).map g.toMonoidHom) := by
    intro e he
    apply s16n9b_mem_stabSub_of_map_eq
    rw [← hgB, ← s15_Infra_commSub_top_map_conj _ e,
      s16n9b_two_normalizes_conj h (hEM he) (hA e he)]
  have hrk' : rk ↥((commSub ⊤ A).map g.toMonoidHom) = 3 := by
    rw [s16n9b_rk_map]
    exact hrk
  have h168 := s16n9b_card_mulAut_rank_three hT hrk
  have h168' := s16n9b_card_mulAut_rank_three hT hrk'
  have hn : ¬ 7 ^ 2 ∣ 168 := by norm_num
  have h1 := s16n9b_card_le_mul_card_inf_centSub (p := 7) (by norm_num) hEcard hstW h168 hn
  have hdvd : Nat.card ↥(E ⊓ centSub (commSub ⊤ A)) ∣ 7 ^ a :=
    hEcard ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 hdvd
  have h2 := s16n9b_card_le_mul_card_inf_centSub (p := 7) (by norm_num) hb
    (inf_le_left.trans hstW') h168' hn
  have h3 : E ⊓ centSub (commSub ⊤ A) ⊓ centSub ((commSub ⊤ A).map g.toMonoidHom) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨-, hx1⟩, hx2⟩ := hx
    rw [Subgroup.mem_bot]
    apply MulEquiv.ext
    intro t
    have ht : t ∈ commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom := by
      rw [h.sup]
      exact Subgroup.mem_top t
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 ht
    have e1 : x y = y := hx1 y hy
    have e2 : x z = z := hx2 z hz
    rw [map_mul, e1, e2]
    rfl
  rw [h3, Subgroup.card_bot] at h2
  omega

end Generic

section Construction

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case11_pRank_lt (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥)
    (h11 : Case168_11 D V₀ V hV L) : CFSG.Open.pRank 7 (Mbar D.M V₀ V hV) < 3 := by
  obtain ⟨g, hg⟩ := s16n9b_twoConj D h1217 hV hc hV0 h11.2.2.1
  by_contra hge
  push Not at hge
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 7) (by norm_num) (Mbar D.M V₀ V hV)
  have h49 := s16n9b_card_le_forty_nine (s15_Infra_vtil_sq_eq_one V₀ V hV) hg h11.2.1 hEM hE.2
    hEcard
  have h343 : 343 ≤ Nat.card E := by
    rw [hEcard]
    calc 343 = 7 ^ 3 := by norm_num
      _ ≤ 7 ^ CFSG.Open.pRank 7 (Mbar D.M V₀ V hV) := Nat.pow_le_pow_right (by norm_num) hge
  omega

end Construction

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
