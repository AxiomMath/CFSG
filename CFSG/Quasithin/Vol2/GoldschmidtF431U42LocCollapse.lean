module

public import CFSG.Adapters.Involutions
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocKlein

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG

theorem odd_card_oddCore (G : Type*) [Group G] [Finite G] : Odd (Nat.card (oddCore G)) := by
  have hle : oddCore G ≤ pPrimeCore 2 G :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  exact Nat.coprime_two_left.mp (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hle)
    (pPrimeCore_coprime_card (p := 2) (G := G)))

theorem mk_comm_iff {H : Type*} [Group H] (N : Subgroup H) [N.Normal] (x y : H) :
    (QuotientGroup.mk x : H ⧸ N) * QuotientGroup.mk y = QuotientGroup.mk y * QuotientGroup.mk x ↔
      x * y * x⁻¹ * y⁻¹ ∈ N := by
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc (QuotientGroup.mk x : H ⧸ N) * QuotientGroup.mk y
        = ((QuotientGroup.mk x : H ⧸ N) * QuotientGroup.mk y * (QuotientGroup.mk x)⁻¹ *
          (QuotientGroup.mk y)⁻¹) * (QuotientGroup.mk y * QuotientGroup.mk x) := by group
      _ = QuotientGroup.mk y * QuotientGroup.mk x := by rw [h, one_mul]

theorem collapse {H : Type} [Group H] [Finite H] (N X Q : Subgroup H)
    (hNc : N ≤ Subgroup.center H) (hN2 : Nat.card N = 2) (hNX : N ≤ X) (hNQ : N ≤ Q)
    (hQp : IsPGroup 2 Q) (hQm : ∀ Q' : Subgroup H, IsPGroup 2 Q' → Q ≤ Q' → Q' = Q)
    (u a b : H) (hu : u * u = 1) (huN : u ∉ N) (huQ : u ∈ Q)
    (huc : ∀ q ∈ Q, q * u * q⁻¹ * u⁻¹ ∈ N)
    (hU1 : ∀ h : H, h * u * h⁻¹ * u⁻¹ ∈ N → h ∈ X)
    (hU3 : ∀ h : H, h * u * h⁻¹ ∈ Q → h * u * h⁻¹ * u⁻¹ ∈ N)
    (ha : a * a = 1) (hb : b * b = 1)
    (hUa : ∀ h : H, h * a * h⁻¹ * a⁻¹ ∈ N → h ∈ X)
    (hUb : ∀ h : H, h * b * h⁻¹ * b⁻¹ ∈ N → h ∈ X)
    (hUab : ∀ h : H, h * (a * b) * h⁻¹ * (a * b)⁻¹ ∈ N → h ∈ X)
    (hX1 : ∀ K : Subgroup H, K ≤ X → (∀ e ∈ X, ∀ k ∈ K, e * k * e⁻¹ ∈ K) → N ≤ K →
      ¬ 4 ∣ Nat.card K → K = N) :
    ∀ h : H, h ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : N.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hNc hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  let mk : H →* H ⧸ N := QuotientGroup.mk' N
  have hmk : Function.Surjective mk := QuotientGroup.mk'_surjective N
  have : Finite (H ⧸ N) := Finite.of_surjective mk hmk
  have hmk1 : ∀ x : H, mk x = 1 ↔ x ∈ N := fun x => QuotientGroup.eq_one_iff x
  have hOX : ∀ x ∈ X, (mk x) ∈ oddCore (H ⧸ N) → mk x = 1 := by
    intro x hx hxO
    let Kd : Subgroup H := X ⊓ (oddCore (H ⧸ N)).comap mk
    have hNKd : N ≤ Kd := fun n hn => ⟨hNX hn, by simp [(hmk1 n).2 hn]⟩
    have hKd : Kd = N := by
      refine hX1 Kd inf_le_left ?_ hNKd ?_
      · intro e he k hk
        refine ⟨X.mul_mem (X.mul_mem he hk.1) (X.inv_mem he), ?_⟩
        have := (inferInstance : (oddCore (H ⧸ N)).Normal).conj_mem (mk k) hk.2 (mk e)
        simpa using this
      · have hodd := odd_card_oddCore (H ⧸ N)
        let f : ↥Kd →* H ⧸ N := mk.comp Kd.subtype
        have h1 := Subgroup.card_ker_mul_card_range f
        have hker : Nat.card f.ker = 2 := by
          have : f.ker = N.subgroupOf Kd := by
            ext k
            simp [f, hmk1, Subgroup.mem_subgroupOf]
          rw [this, ← hN2]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNKd).toEquiv
        have hrange : Nat.card f.range ∣ Nat.card (oddCore (H ⧸ N)) := by
          refine Subgroup.card_dvd_of_le ?_
          rintro _ ⟨k, rfl⟩
          exact k.2.2
        have hodd' : Odd (Nat.card f.range) := Odd.of_dvd_nat hodd hrange
        rw [hker] at h1
        obtain ⟨m, hm⟩ := hodd'
        omega
    have hxN : x ∈ N := hKd ▸ ⟨hx, hxO⟩
    exact (hmk1 x).2 hxN
  let Sq : Sylow 2 H := ⟨Q, hQp, fun {Q'} h1 h2 => hQm Q' h1 h2⟩
  let Sb : Sylow 2 (H ⧸ N) := Sq.mapSurjective hmk
  have hSb : ∀ g : H ⧸ N, g ∈ (Sb : Subgroup (H ⧸ N)) ↔ ∃ q ∈ Q, mk q = g := fun g => Iff.rfl
  have hcomm : ∀ x y : H, mk x * mk y = mk y * mk x ↔ x * y * x⁻¹ * y⁻¹ ∈ N :=
    fun x y => mk_comm_iff N x y
  have hmkuS : mk u ∈ (Sb : Subgroup (H ⧸ N)) := (hSb _).2 ⟨u, huQ, rfl⟩
  have hzZ : (⟨mk u, hmkuS⟩ : (Sb : Subgroup (H ⧸ N))) ∈
      Subgroup.center (Sb : Subgroup (H ⧸ N)) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨g, hg⟩
    obtain ⟨q, hq, rfl⟩ := (hSb g).1 hg
    refine Subtype.ext ?_
    exact ((hcomm q u).2 (huc q hq))
  have hord : orderOf (⟨mk u, hmkuS⟩ : (Sb : Subgroup (H ⧸ N))) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · refine Subtype.ext ?_
      change mk u ^ 2 = 1
      rw [pow_two, ← map_mul, hu, map_one]
    · intro h
      have : mk u = 1 := congrArg Subtype.val h
      exact huN ((hmk1 u).1 this)
  have hwc : ∀ g : H ⧸ N, g⁻¹ * mk u * g ∈ (Sb : Subgroup (H ⧸ N)) →
      g⁻¹ * mk u * g = mk u := by
    intro g hg
    obtain ⟨h, rfl⟩ := hmk g
    obtain ⟨q, hq, hqe⟩ := (hSb _).1 hg
    have h1 : mk (h⁻¹ * u * h) = mk q := by rw [hqe]; simp
    have h2 : q⁻¹ * (h⁻¹ * u * h) ∈ N := QuotientGroup.eq.1 h1.symm
    have h3 : h⁻¹ * u * h ∈ Q := by
      have := Q.mul_mem hq (hNQ h2)
      simpa using this
    have h4 := hU3 h⁻¹ (by simpa using h3)
    have h5 : mk (h⁻¹ * u * h * u⁻¹) = 1 := (hmk1 _).2 (by simpa using h4)
    have h6 : mk (h⁻¹ * u * h) = mk u := by
      simpa [mul_inv_eq_one] using h5
    simpa using h6
  obtain ⟨hfac, -⟩ := CFSG.Adapters.glauberman_zStar Sb ⟨mk u, hmkuS⟩ hzZ hord hwc
  have hO : oddCore (H ⧸ N) = ⊥ := by
    have : Finite (oddCore (H ⧸ N)) := inferInstance
    refine eq_bot_of_three_involutions (oddCore (H ⧸ N)) (mk a) (mk b)
      (by rw [← map_mul, ha, map_one]) (by rw [← map_mul, hb, map_one]) ?_ ?_ ?_
    · intro o ho hoa
      obtain ⟨x, rfl⟩ := hmk o
      exact hOX x (hUa x ((hcomm x a).1 hoa)) ho
    · intro o ho hob
      obtain ⟨x, rfl⟩ := hmk o
      exact hOX x (hUb x ((hcomm x b).1 hob)) ho
    · intro o ho hoab
      obtain ⟨x, rfl⟩ := hmk o
      rw [← map_mul] at hoab
      exact hOX x (hUab x ((hcomm x (a * b)).1 hoab)) ho
  intro h
  obtain ⟨c, hc, k, hk, hck⟩ := hfac (mk h)
  rw [hO, Subgroup.mem_bot] at hk
  rw [hk, mul_one] at hck
  have h1 : mk h * mk u = mk u * mk h := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [← hck] at this
    exact this
  exact hU1 h ((hcomm h u).1 h1)

end CFSG.Quasithin.H13.F431.U42
