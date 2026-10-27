module

public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Vol2.Ch10SecC9S3a

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

section Abstract

variable {Ω : Type*} [Group Ω]

theorem commutator_ne_self_of_isSolvable {N : Subgroup Ω} (hs : Group.IsSolvable ↥N)
    (hN : N ≠ ⊥) : ⁅N, N⁆ ≠ N := by
  intro h
  have htop : commutator ↥N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hall : ∀ n, derivedSeries ↥N n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih]; exact htop
  obtain ⟨n, hn⟩ := (Group.isSolvable_def _).mp hs
  rw [hall n] at hn
  apply hN
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : ↥N) ∈ (⊥ : Subgroup ↥N) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem commutator_eq_one_of_odd [Finite Ω] {K A : Subgroup Ω} (hK : IsPGroup 2 ↥K)
    (hA : Odd (Nat.card A)) (hAK : A ≤ Subgroup.centralizer (K : Set Ω)) {x : Ω}
    (hx : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ A) : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ = 1 := by
  let f : ↥K →* ↥A :=
    { toFun := fun k => ⟨x * k * x⁻¹ * k⁻¹, hx k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hc : (a : Ω) * (x * b * x⁻¹ * (b : Ω)⁻¹) * (a : Ω)⁻¹ =
            x * b * x⁻¹ * (b : Ω)⁻¹ := by
          have := Subgroup.mem_centralizer_iff.mp (hAK (hx b b.2)) a a.2
          rw [this, mul_inv_cancel_right]
        simp only [Subgroup.coe_mul]
        calc x * (a * b) * x⁻¹ * ((a : Ω) * b)⁻¹
            = (x * a * x⁻¹ * (a : Ω)⁻¹) *
                ((a : Ω) * (x * b * x⁻¹ * (b : Ω)⁻¹) * (a : Ω)⁻¹) := by group
          _ = (x * a * x⁻¹ * (a : Ω)⁻¹) * (x * b * x⁻¹ * (b : Ω)⁻¹) := by rw [hc] }
  intro k hk
  obtain ⟨m, hm⟩ := hK ⟨k, hk⟩
  have h1 : orderOf (f ⟨k, hk⟩) ∣ 2 ^ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hm, map_one])
  have h2 : orderOf (f ⟨k, hk⟩) ∣ Nat.card A := orderOf_dvd_natCard _
  have h3 : orderOf (f ⟨k, hk⟩) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · simpa using hj
    · exfalso
      rw [hj, pow_succ] at h2
      exact (Nat.not_even_iff_odd.mpr hA) (even_iff_two_dvd.mpr (dvd_of_mul_left_dvd h2))
  rw [orderOf_eq_one_iff] at h3
  exact congrArg Subtype.val h3

theorem isNilpotent_of_commutator_le_center {N : Subgroup Ω}
    (h : ∀ a ∈ N, ∀ b ∈ N, ∀ c ∈ N, a * b * a⁻¹ * b⁻¹ * c = c * (a * b * a⁻¹ * b⁻¹)) :
    Group.IsNilpotent ↥N := by
  let f := QuotientGroup.mk' (Subgroup.center ↥N)
  have : IsMulCommutative (↥N ⧸ Subgroup.center ↥N) := ⟨⟨fun x y => by
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        rw [Subgroup.mem_center_iff]
        intro c
        apply Subtype.ext
        have h2 := h _ (N.inv_mem b.2) _ (N.inv_mem a.2) c c.2
        simp only [inv_inv] at h2
        push_cast
        rw [mul_inv_rev]
        simp only [mul_assoc] at h2 ⊢
        exact h2.symm⟩⟩
  exact Subgroup.isNilpotent_of_ker_le_center f (by rw [QuotientGroup.ker_mk'])

theorem mem_pCoreOf_of_isNilpotent [Finite Ω] {N : Subgroup Ω} (hN : Group.IsNilpotent ↥N)
    {q : ℕ} [hq : Fact q.Prime] {x : Ω} (hx : x ∈ N) {k : ℕ} (hxk : x ^ q ^ k = 1) :
    x ∈ pCoreOf q N := by
  have hord : orderOf (⟨x, hx⟩ : ↥N) ∣ q ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext hxk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq.out).mp hord
  have hzp : IsPGroup q ↥(Subgroup.zpowers (⟨x, hx⟩ : ↥N)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have htf : Group.IsNilpotent ↥N ↔
      ∀ (p : ℕ), Fact (Nat.Prime p) → ∀ (P : Sylow p ↥N), (P : Subgroup ↥N).Normal :=
    (Group.isNilpotent_of_finite_tfae (G := ↥N)).out 1 4
  have hPn : (P : Subgroup ↥N).Normal := htf.mp hN q hq P
  have hle : (P : Subgroup ↥N).map N.subtype ≤ pCoreOf q N := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer q
      (fun y ⟨z, _, hz⟩ => hz ▸ z.2) (fun n hn => ?_) (P.isPGroup'.map N.subtype)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨n, hn⟩ * z * ⟨n, hn⟩⁻¹, hPn.conj_mem z hz _, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have hzy' : (z : Ω) = n * y * n⁻¹ := hzy
      have hyN : y ∈ N := by
        have : n⁻¹ * (n * y * n⁻¹) * n ∈ N :=
          N.mul_mem (N.mul_mem (N.inv_mem hn) (hzy' ▸ z.2)) hn
        simpa [mul_assoc] using this
      refine ⟨⟨y, hyN⟩, ?_, rfl⟩
      have : (⟨n, hn⟩ : ↥N)⁻¹ * z * ⟨n, hn⟩ = ⟨y, hyN⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzy']
        group
      rw [← this]
      have := hPn.conj_mem z hz (⟨n, hn⟩ : ↥N)⁻¹
      rwa [inv_inv] at this
  exact hle ⟨⟨x, hx⟩, hP (Subgroup.mem_zpowers _), rfl⟩

end Abstract

theorem le_centralizer_of_ffJ {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G₁ N₀ : Subgroup (MulAut V)} (hJ : G₁ = ffJ G₁) (hO2 : pCoreOf 2 G₁ = ⊥) (hN₀G : N₀ ≤ G₁)
    (hs : Group.IsSolvable ↥N₀) (h3 : ¬ 3 ∣ Nat.card N₀) (N : Subgroup (MulAut V))
    (hN : N ≤ N₀) (hNn : G₁ ≤ Subgroup.normalizer (N : Set (MulAut V))) :
    N ≤ Subgroup.centralizer (G₁ : Set (MulAut V)) := by
  suffices H : ∀ n : ℕ, ∀ N : Subgroup (MulAut V), N ≤ N₀ →
      G₁ ≤ Subgroup.normalizer (N : Set (MulAut V)) → Nat.card N = n →
      N ≤ Subgroup.centralizer (G₁ : Set (MulAut V)) from H _ N hN hNn rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hN hNn hcard
  by_cases hb : N = ⊥
  · rw [hb]; exact bot_le
  have hsN : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hN)
  have hMN : ⁅N, N⁆ ≤ N := Subgroup.commutator_le_self N
  have hMlt : Nat.card ↥(⁅N, N⁆ : Subgroup (MulAut V)) < Nat.card N :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hMN (commutator_ne_self_of_isSolvable hsN hb))
  have hMC := ih _ (hcard ▸ hMlt) ⁅N, N⁆ (hMN.trans hN)
    (SecA.le_normalizer_commutator hNn hNn) rfl
  have hnil : Group.IsNilpotent ↥N := isNilpotent_of_commutator_le_center fun a ha b hb c hc => by
    have hab : a * b * a⁻¹ * b⁻¹ ∈ ⁅N, N⁆ := by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator ha hb
    exact (Subgroup.mem_centralizer_iff.mp (hMC hab) c (hN.trans hN₀G hc)).symm
  have hcore : ∀ p : ℕ, p.Prime → p ∣ Nat.card N →
      pCoreOf p N ≤ Subgroup.centralizer (G₁ : Set (MulAut V)) := by
    intro p hp hpN
    have : Fact p.Prime := ⟨hp⟩
    have hle : pCoreOf p N ≤ pCoreOf p G₁ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
        ((CFSG.LieType.BorelTits.pCoreOf_le p N).trans (hN.trans hN₀G))
        (hNn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p N))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup p N)
    by_cases hp2 : p = 2
    · subst hp2
      rw [hO2] at hle
      exact hle.trans bot_le
    by_cases hp3 : p = 3
    · subst hp3
      exact absurd ((hpN.trans (Subgroup.card_dvd_of_le hN))) h3
    exact hle.trans (B55.pCoreOf_le_centralizer hV hJ hp2 hp3)
  intro x hx
  refine mem_of_forall_primePow (M := N) (N := Nat.card N)
    (fun p hp hpN y hy k hyk => ?_) x hx ?_
  · have : Fact p.Prime := ⟨hp⟩
    exact hcore p hp hpN (mem_pCoreOf_of_isNilpotent hnil hy hyk)
  · have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥N)
    rwa [Subgroup.orderOf_mk] at this

end CFSG.Quasithin.Vol2.Ch10.SecC
