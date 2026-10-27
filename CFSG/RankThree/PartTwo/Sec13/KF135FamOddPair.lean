module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddTools
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddCore

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

open CFSG Subgroup
open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
  {V : Subgroup (MulAut S)}

theorem false_of_commuting_pair (h : KF135Hyp S p P x u V) {H₁ H₂ : Subgroup S}
    (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) (hp1 : p ∣ Nat.card H₁)
    (hp2 : p ∣ Nat.card H₂) (hint : ∀ g ∈ H₁ ⊓ H₂, g ^ 2 = 1) {z : S}
    (hzc : ∀ a ∈ H₁, a * z = z * a) (hzc2 : ∀ b ∈ H₂, b * z = z * b) (hz2 : z ^ 2 = 1)
    (hz : z ≠ 1) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp2' : p ≠ 2 := by have := h.seven_le; omega
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := H₁) p hp1
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := H₂) p hp2
  have ha' : orderOf (a : S) = p := by rw [Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf (b : S) = p := by rw [Subgroup.orderOf_coe]; exact hb
  set C : Subgroup S := Subgroup.closure {(a : S), (b : S)}
  have hab : (a : S) * b = b * a := hcomm a a.2 b b.2
  have hC : CFSG.Open.IsElemAbelian p C := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · rintro y (rfl | rfl) w (rfl | rfl)
      · rfl
      · exact hab
      · exact hab.symm
      · rfl
    · rintro y (rfl | rfl)
      · rw [← ha']; exact pow_orderOf_eq_one _
      · rw [← hb']; exact pow_orderOf_eq_one _
  have hbna : (b : S) ∉ Subgroup.zpowers (a : S) := by
    intro hmem
    have hbH : (b : S) ∈ H₁ ⊓ H₂ := ⟨(Subgroup.zpowers_le.2 a.2) hmem, b.2⟩
    have h1 := orderOf_dvd_of_pow_eq_one (hint _ hbH)
    rw [hb'] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    have := h.seven_le
    omega
  have hCp : IsPGroup p C := hC.isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hCp
  have haC : Subgroup.zpowers (a : S) ≤ C :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _))
  have hbC : (b : S) ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hpk : p ∣ p ^ k := by
      rw [← hk, ← ha', ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le haC
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 1 with h0 | h1
      · have : k = 0 := by omega
        rw [this, pow_zero] at hpk
        exact absurd (Nat.le_of_dvd one_pos hpk) (by have := h.prime.two_le; omega)
      · omega
    have hle : Nat.card C ≤ Nat.card (Subgroup.zpowers (a : S)) := by
      rw [hk, hk1, pow_one, Nat.card_zpowers, ha']
    exact hbna ((Subgroup.eq_of_le_of_card_ge haC hle).symm ▸ hbC)
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) p (n := 2)
    (hk ▸ pow_dvd_pow p hk2)
  set F : Subgroup S := F₀.map C.subtype
  have hFC : F ≤ C := Subgroup.map_subtype_le F₀
  have hFc : Nat.card F = p ^ 2 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hF₀]
  have hCz : C ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup S) : Set S) := by
    have hcen : C ≤ Subgroup.centralizer ({z} : Set S) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hzc _ a.2)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hzc2 _ b.2)
    refine hcen.trans fun g hg => ?_
    have hgz : Commute g z := Subgroup.mem_centralizer_singleton_iff.1 hg
    have hgzn : ∀ n : ℤ, g * z ^ n * g⁻¹ = z ^ n := fun n => by
      rw [(hgz.zpow_right n).eq, mul_inv_cancel_right]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, (hgzn n).symm⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have h1 : g * y * g⁻¹ = g * z ^ n * g⁻¹ := by rw [← hn, hgzn]
      simpa using h1.symm
  refine false_of_h2a_witness h (hC.mono hFC) hFc (T := Subgroup.zpowers z) ?_ ?_ (hFC.trans hCz)
  · intro hbot
    apply hz
    have : z ∈ (⊥ : Subgroup S) := hbot ▸ Subgroup.mem_zpowers z
    exact (Subgroup.mem_bot).1 this
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (by
      rw [Nat.card_zpowers]
      have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h3 | h3
      · exact absurd (orderOf_eq_one_iff.1 h3) hz
      · exact h3.trans (pow_one 2).symm) (n := 1)

theorem exists_mulEquiv_lift_of_le_range_toPGL {n : ℕ} (K : Type) [Field K] [Finite K]
    {q : ℕ} [hq : Fact q.Prime] (hqn : ¬ q ∣ n) (G : Subgroup PGL(n, K))
    (hG : G ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin n) K →* PGL(n, K)).range) (Q : Subgroup G)
    (hQ : IsPGroup q Q) :
    ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin n) K), IsPGroup q T ∧ Nonempty (Q ≃* T) := by
  set Q' : Subgroup PGL(n, K) := Q.map G.subtype
  have hQ' : IsPGroup q Q' := hQ.map _
  obtain ⟨T, hT, hTQ⟩ := CFSG.RankThree.PartTwo.Sec4.L34Odd.exists_isPGroup_map_eq q
    (Matrix.SpecialLinearGroup.toPGL : Matrix.SpecialLinearGroup (Fin n) K →* PGL(n, K)) Q' hQ'
    ((Subgroup.map_subtype_le Q).trans hG)
  have hinjT : Function.Injective
      ((Matrix.SpecialLinearGroup.toPGL :
        Matrix.SpecialLinearGroup (Fin n) K →* PGL(n, K)).comp T.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Matrix.SpecialLinearGroup.toPGL_ker, Matrix.SpecialLinearGroup.mem_center_iff] at ht
    obtain ⟨r, hr, hrt⟩ := ht
    have hrt' : (Matrix.scalar (Fin n) r) =
        ((t : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := hrt
    rw [Fintype.card_fin] at hr
    have hn : (t : Matrix.SpecialLinearGroup (Fin n) K) ^ n = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hrt', ← map_pow, hr, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have hn' : t ^ n = 1 := Subtype.ext (by simpa using hn)
    obtain ⟨k, hk⟩ := hT t
    have hdvd : orderOf t ∣ Nat.gcd n (q ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn') (orderOf_dvd_of_pow_eq_one hk)
    have hcop : Nat.gcd n (q ^ k) = 1 :=
      Nat.Coprime.pow_right k (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hqn))
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    exact hdvd ▸ Subgroup.one_mem _
  have hrange : ((Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin n) K →* PGL(n, K)).comp T.subtype).range = Q' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hTQ]
  exact ⟨T, hT, ⟨(Q.equivMapOfInjective G.subtype G.subtype_injective).trans
    ((MonoidHom.ofInjective hinjT).trans (MulEquiv.subgroupCongr hrange)).symm⟩⟩

theorem false_of_two_blocks (h : KF135Hyp S p P x u V) {H : Type*} [Group H] [Finite H]
    (hHc : ∀ c ∈ Subgroup.center H, c ^ 2 = 1) (e₁ e₂ : H →* S) (he₁ : Function.Injective e₁)
    (he₂ : Function.Injective e₂) (hcomm : ∀ a b : H, e₁ a * e₂ b = e₂ b * e₁ a)
    (hp : p ∣ Nat.card H) {z : S} (hz1 : ∀ a : H, e₁ a * z = z * e₁ a)
    (hz2 : ∀ b : H, e₂ b * z = z * e₂ b) (hzsq : z ^ 2 = 1) (hz : z ≠ 1) : False := by
  have hcard : ∀ (e : H →* S), Function.Injective e → Nat.card e.range = Nat.card H := fun e he =>
    Nat.card_congr (MonoidHom.ofInjective he).toEquiv.symm
  refine false_of_commuting_pair h (H₁ := e₁.range) (H₂ := e₂.range) ?_
    (by rw [hcard e₁ he₁]; exact hp) (by rw [hcard e₂ he₂]; exact hp) ?_ (z := z) ?_ ?_ hzsq hz
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact hcomm a b
  · rintro g ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have hac : a ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply he₁
      rw [map_mul, map_mul, ← hb]
      exact hcomm c b
    rw [← map_pow, hHc a hac, map_one]
  · rintro _ ⟨a, rfl⟩
    exact hz1 a
  · rintro _ ⟨b, rfl⟩
    exact hz2 b

theorem dvd_card_range_of_ker {G H : Type*} [Group G] [Finite G] [Group H] (f : G →* H) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hG : q ∣ Nat.card G) (hker : ∀ g ∈ f.ker, g ^ 2 = 1) :
    q ∣ Nat.card f.range := by
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card G = Nat.card f.ker * Nat.card f.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  rw [hcard] at hG
  rcases (Nat.Prime.dvd_mul hq).1 hG with hk | hr
  · exfalso
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) q hk
    have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hker _ g.2))
    rw [hg] at h1
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h1)
  · exact hr

theorem card_le_of_isElemAbelian_of_isCyclic {G : Type*} [Group G] [Finite G] {q : ℕ}
    (hq : q.Prime) {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian q E) (hc : IsCyclic E) :
    Nat.card E ≤ q := by
  obtain ⟨g, hg⟩ := hc.exists_generator
  have h1 : Nat.card E = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have h2 : orderOf g ∣ q := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 _ g.2))
  rw [h1]
  exact Nat.le_of_dvd hq.pos h2

theorem false_of_cyclic (h : KF135Hyp S p P x u V) (hP : P ≤ inner S)
    (hc : ∀ E : Subgroup S, CFSG.Open.IsElemAbelian p E → IsCyclic E) : False :=
  false_of_rankLE1 h hP fun E hE => card_le_of_isElemAbelian_of_isCyclic h.prime hE (hc E hE)

end CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd
