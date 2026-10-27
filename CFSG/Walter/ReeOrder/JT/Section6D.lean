module

public import CFSG.Walter.ReeOrder.JT.Section6C
public import CFSG.Walter.ReeOrder.JT.Section4IF

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem exists_odd_normal_of_kleinFour {N V : Subgroup X} (hV : IsKleinFour V) (hVN : V ≤ N)
    (h8 : ¬ 8 ∣ Nat.card N) {u w : X} (hu : u ∈ V) (hw : w ∈ V) (hu1 : u ≠ 1) (hw1 : w ≠ 1)
    (huw : ∀ g ∈ N, g * u * g⁻¹ ≠ w) :
    ∃ M : Subgroup X, M ≤ N ∧ Odd (Nat.card M) ∧
      (∀ g ∈ N, g ∈ Subgroup.normalizer (M : Set X)) ∧
      (∀ y ∈ N, Odd (orderOf y) → y ∈ M) ∧ Nat.card N = 4 * Nat.card M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVcard : Nat.card (V.subgroupOf N) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv, hV.card_four]
  have hfacN : (Nat.card N).factorization 2 = 2 := by
    have h4 : 2 ^ 2 ∣ Nat.card N := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV.card_four]
      exact Subgroup.card_dvd_of_le hVN
    have h8' : ¬ 2 ^ 3 ∣ Nat.card N := by norm_num; exact h8
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne'] at h4 h8'
    omega
  let VS : Sylow 2 N := Sylow.ofCard (V.subgroupOf N) (by rw [hVcard, hfacN]; norm_num)
  have hVS : IsKleinFour (VS : Subgroup N) := by
    have e : (V.subgroupOf N) ≃* V := Subgroup.subgroupOfEquivOfLe hVN
    exact ⟨hVcard, by
      change Monoid.exponent (V.subgroupOf N) = 2
      rw [Monoid.exponent_eq_of_mulEquiv e, hV.exponent_two]⟩
  have hnc : ∀ g : N, g * ⟨u, hVN hu⟩ * g⁻¹ ≠ ⟨w, hVN hw⟩ := fun g hg =>
    huw g g.2 (congrArg Subtype.val hg)
  obtain ⟨M, hMn, hModd, hMcard⟩ := exists_normal_odd_of_kleinFour_sylow VS hVS
    (u := ⟨u, hVN hu⟩) (w := ⟨w, hVN hw⟩)
    (by change (⟨u, hVN hu⟩ : N) ∈ V.subgroupOf N; rw [Subgroup.mem_subgroupOf]; exact hu)
    (by change (⟨w, hVN hw⟩ : N) ∈ V.subgroupOf N; rw [Subgroup.mem_subgroupOf]; exact hw)
    (fun h0 => hu1 (congrArg Subtype.val h0)) (fun h0 => hw1 (congrArg Subtype.val h0)) hnc
  set MG := M.map N.subtype with hMGdef
  have hMGcard : Nat.card MG = Nat.card M := Subgroup.card_map_of_injective N.subtype_injective
  have hMidx : M.index = 4 := by
    have h1 := M.card_mul_index
    rw [hMcard] at h1
    have : 0 < Nat.card M := Nat.card_pos
    nlinarith
  refine ⟨MG, Subgroup.map_subtype_le _, hMGcard ▸ hModd, fun n hn => ?_, fun y hyN hyodd => ?_,
    by rw [hMcard, hMGcard]⟩
  · have hmem' : (⟨n, hn⟩ : N) ∈ Subgroup.normalizer (M : Set N) := by
      have := hMn
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact Subgroup.le_normalizer_map N.subtype ⟨⟨n, hn⟩, hmem', rfl⟩
  · have h4 : (⟨y, hyN⟩ : N) ^ 4 ∈ M := by
      have := Subgroup.pow_index_mem M (⟨y, hyN⟩ : N)
      rwa [hMidx] at this
    have h1 : (⟨y, hyN⟩ : N) ^ orderOf y ∈ M := by
      have : (⟨y, hyN⟩ : N) ^ orderOf y = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this]
      exact M.one_mem
    have hcop : Nat.Coprime 4 (orderOf y) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hyodd)
    exact ⟨⟨y, hyN⟩, mem_of_pow_mem_of_coprime h4 h1 hcop, rfl⟩

end General

namespace JTHyp

variable (h : JTHyp G) (hp : h.p ≠ 2)
include hp

theorem odd_card_of_isPGroup {X : Subgroup G} (hXp : IsPGroup h.p X) : Odd (Nat.card X) := by
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  rw [hn]
  exact ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow

theorem not_eight_dvd
    {X : Subgroup G} (hXp : IsPGroup h.p X) (hX1 : X ≠ ⊥) :
    ¬ 8 ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
  intro h8
  obtain ⟨s⟩ := h.nonempty_setup hp
  obtain ⟨g, hg⟩ := s.exists_conj_le_Q_of_eight_dvd hp (h.odd_card_of_isPGroup hp hXp) h8
  have hdvd : Nat.card X ∣ Nat.card s.Q := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    exact Subgroup.card_dvd_of_le hg
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hX1 hn
  rw [hn] at hdvd
  exact s.not_dvd_card_Q hp ((dvd_pow_self h.p hn0).trans hdvd)

end JTHyp

namespace BorelData

variable {h : JTHyp G} (b : BorelData h)

theorem T_le_normalizer {X : Subgroup G} (htX : h.t ∈ Subgroup.normalizer (X : Set G))
    (hτX : b.τ ∈ Subgroup.normalizer (X : Set G)) : b.T ≤ Subgroup.normalizer (X : Set G) := by
  intro x hx
  rcases b.mem_T_iff.mp hx with rfl | rfl | rfl | rfl
  · exact Subgroup.mul_mem _ htX hτX
  · exact htX
  · exact hτX
  · exact Subgroup.one_mem _

theorem card_inf_le_of_conj {X : Subgroup G} {g u w : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hgu : g * u * g⁻¹ = w) :
    Nat.card (X ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ≤
      Nat.card (X ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := by
  have hle : (X ⊓ Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom ≤
      X ⊓ Subgroup.centralizer ({w} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgu]
    have hxu := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    change g * x * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hxu]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  have := Subgroup.card_le_of_le hle
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at this

variable (hp : h.p ≠ 2) (hq5 : h.q % 8 = 5)
include hp hq5

theorem card_eq_prod
    {X : Subgroup G} (hXp : IsPGroup h.p X)
    (htX : h.t ∈ Subgroup.normalizer (X : Set G)) (hτX : b.τ ∈ Subgroup.normalizer (X : Set G)) :
    Nat.card X = Nat.card (X ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) *
      Nat.card (X ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) *
      Nat.card (X ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) : Subgroup G) := by
  have hBW := b.card_mul_sq X htX hτX (h.odd_card_of_isPGroup hp hXp)
  have hXT : X ⊓ Subgroup.centralizer ({h.t} : Set G) ⊓
      Subgroup.centralizer ({b.τ} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨n, hn⟩ := hXp ⟨y, hy.1.1⟩
    have hyn : y ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hyC : y ∈ b.C := b.mem_C_of_commute hp hq5
      (Subgroup.mem_centralizer_singleton_iff.mp hy.1.2)
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
      (Odd.of_dvd_nat ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow
        (orderOf_dvd_of_pow_eq_one hyn))
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left n b.coprime_card_C.symm) (orderOf_dvd_of_pow_eq_one hyn)
      (Subgroup.orderOf_dvd_natCard _ hyC)))
  rw [hXT, Subgroup.card_bot, one_pow, mul_one] at hBW
  exact hBW

variable (hp3 : h.p ≠ 3)
include hp3

theorem card_inf_eq
    {X : Subgroup G} (hXp : IsPGroup h.p X)
    (hCX : b.C ≤ Subgroup.normalizer (X : Set G)) {u : G}
    (hu : u = h.t ∨ u = b.τ ∨ u = h.t * b.τ) :
    Nat.card (X ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = 1 ∨
      Nat.card (X ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = h.q := by
  set Xu := X ⊓ Subgroup.centralizer ({u} : Set G) with hXudef
  have hCu := b.C_le_centralizer hu
  have hCXu : b.C ≤ Subgroup.normalizer (Xu : Set G) := fun x hx =>
    mem_normalizer_inf (hCX hx) (Subgroup.mem_centralizer_singleton_iff.mp (hCu hx))
  have hXup : IsPGroup h.p Xu := hXp.to_le inf_le_left
  have hdisj : Disjoint b.C Xu := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := hXup.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n b.coprime_card_C
  have hYcard := card_sup_eq_mul_of_disjoint hCXu hdisj
  have hYu : b.C ⊔ Xu ≤ Subgroup.centralizer ({u} : Set G) := sup_le hCu inf_le_right
  have hYodd : Odd (Nat.card (b.C ⊔ Xu : Subgroup G)) := by
    rw [hYcard]
    exact (b.odd_card_C hq5).mul (h.odd_card_of_isPGroup hp hXup)
  have hc0 : 0 < Nat.card b.C := Nat.card_pos
  rcases b.card_inf_centralizer hp hq5 hp3 (b.orderOf_eq_two hu) hYu hYodd le_sup_left with
    h1 | ⟨h1, -⟩
  · left
    rw [hYcard] at h1
    have : Nat.card b.C * Nat.card Xu = Nat.card b.C * 1 := by rw [h1, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hc0 this
  · right
    rw [hYcard] at h1
    have : Nat.card b.C * Nat.card Xu = Nat.card b.C * h.q := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hc0 this

theorem card_le_cube
    {X : Subgroup G} (hXp : IsPGroup h.p X)
    (htX : h.t ∈ Subgroup.normalizer (X : Set G)) (hτX : b.τ ∈ Subgroup.normalizer (X : Set G))
    (hCX : b.C ≤ Subgroup.normalizer (X : Set G)) : Nat.card X ≤ h.q ^ 3 := by
  rw [b.card_eq_prod hp hq5 hXp htX hτX, pow_three, ← mul_assoc]
  have hle : ∀ {u : G}, (u = h.t ∨ u = b.τ ∨ u = h.t * b.τ) →
      Nat.card (X ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ≤ h.q := by
    intro u hu
    have hq1 : 1 ≤ h.q := by rw [JTHyp.q_eq]; exact Nat.one_le_pow _ _ (Fact.out : h.p.Prime).pos
    rcases b.card_inf_eq hp hq5 hp3 hXp hCX hu with h1 | h1 <;> omega
  exact Nat.mul_le_mul (Nat.mul_le_mul (hle (Or.inl rfl)) (hle (Or.inr (Or.inl rfl))))
    (hle (Or.inr (Or.inr rfl)))

theorem exists_P
    {X : Subgroup G} (hXp : IsPGroup h.p X) (hX1 : X ≠ ⊥)
    (htX : h.t ∈ Subgroup.normalizer (X : Set G)) (hτX : b.τ ∈ Subgroup.normalizer (X : Set G))
    (hCX : b.C ≤ Subgroup.normalizer (X : Set G)) {u w : G} (hu : u ∈ b.T) (hw : w ∈ b.T)
    (hu1 : u ≠ 1) (hw1 : w ≠ 1)
    (hcard : Nat.card (X ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ≠
      Nat.card (X ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G)) :
    ∃ P : Subgroup G, X ≤ P ∧ P ≤ Subgroup.normalizer (X : Set G) ∧ IsPGroup h.p P ∧
      (∀ g ∈ Subgroup.normalizer (X : Set G), g ∈ Subgroup.normalizer (P : Set G)) ∧
      (∀ y ∈ Subgroup.normalizer (X : Set G), ∀ n : ℕ, y ^ h.p ^ n = 1 → y ∈ P) ∧
      ∃ k ≤ 3, Nat.card P = h.q ^ k := by
  have hTN := b.T_le_normalizer htX hτX
  have huw : ∀ g ∈ Subgroup.normalizer (X : Set G), g * u * g⁻¹ ≠ w := by
    intro g hg hgu
    apply hcard
    refine le_antisymm (card_inf_le_of_conj hg hgu) (card_inf_le_of_conj
      (Subgroup.inv_mem _ hg) ?_)
    rw [← hgu]
    group
  obtain ⟨M, hMN, hModd, hMn, hMmem, -⟩ := exists_odd_normal_of_kleinFour b.isKleinFour_T hTN
    (h.not_eight_dvd hp hXp hX1) hu hw hu1 hw1 huw
  have hCM : b.C ≤ M := fun x hx => hMmem x (hCX hx)
    (Odd.of_dvd_nat (b.odd_card_C hq5) (Subgroup.orderOf_dvd_natCard _ hx))
  obtain ⟨P, hPM, hPp, hPmem, -, k, hk, hPcard⟩ := b.exists_sylow_normal hp hq5 hp3 hModd
    (hMn _ htX) (hMn _ hτX) hCM
  have hpodd : ∀ {y : G} {n : ℕ}, y ^ h.p ^ n = 1 → Odd (orderOf y) := fun hy =>
    Odd.of_dvd_nat ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow (orderOf_dvd_of_pow_eq_one hy)
  have hmem : ∀ y ∈ Subgroup.normalizer (X : Set G), ∀ n : ℕ, y ^ h.p ^ n = 1 → y ∈ P :=
    fun y hy n hyn => hPmem y (hMmem y hy (hpodd hyn)) n hyn
  refine ⟨P, fun x hx => ?_, hPM.trans hMN, hPp, fun g hg => ?_, hmem, k, hk, hPcard⟩
  · obtain ⟨n, hn⟩ := hXp ⟨x, hx⟩
    exact hmem x (Subgroup.le_normalizer hx) n (by simpa using congrArg Subtype.val hn)
  · refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨n, hn⟩ := hPp ⟨y, hy⟩
    have hyn : y ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine hPmem _ ((Subgroup.mem_normalizer_iff.mp (hMn g hg) y).mp (hPM hy)) n ?_
    rw [conj_pow, hyn, mul_one, mul_inv_cancel]

omit hp hq5 hp3 in
theorem exists_pow_eq_one_not_mem {X : Subgroup G} (hXp : IsPGroup h.p X)
    (hlt : ∀ S : Sylow h.p G, Nat.card X < Nat.card S) :
    ∃ y ∈ Subgroup.normalizer (X : Set G), (∃ n : ℕ, y ^ h.p ^ n = 1) ∧ y ∉ X := by
  obtain ⟨S, hXS⟩ := hXp.exists_le_sylow
  have := (S.isPGroup').isNilpotent
  have hnc : NormalizerCondition S := Group.normalizerCondition_of_isNilpotent
  have hlt' : X.subgroupOf S < ⊤ := by
    refine lt_of_le_of_ne le_top fun h0 => ?_
    have : Nat.card (X.subgroupOf S) = Nat.card S := by rw [h0, Subgroup.card_top]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXS).toEquiv] at this
    exact (hlt S).ne this
  obtain ⟨y, hyN, hyX⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt')
  refine ⟨y, mem_normalizer_of_conj_mem fun x hx => ?_, ?_, fun h0 => hyX ?_⟩
  · have h1 := (Subgroup.mem_normalizer_iff.mp hyN ⟨x, hXS hx⟩).mp (by exact hx)
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · obtain ⟨n, hn⟩ := S.isPGroup' y
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  · exact h0

omit hp hq5 hp3 in
theorem cube_le_card_sylow (h51 : h.q ^ 3 ∣ Nat.card G) (S : Sylow h.p G) :
    h.q ^ 3 ≤ Nat.card S := by
  rw [S.card_eq_multiplicity]
  have hdvd : h.p ^ (3 * h.f) ∣ Nat.card G := by rw [pow_mul', ← JTHyp.q_eq]; exact h51
  rw [(Fact.out : h.p.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne'] at hdvd
  rw [JTHyp.q_eq, ← pow_mul, mul_comm]
  exact Nat.pow_le_pow_right (Fact.out : h.p.Prime).pos hdvd

theorem exists_cube
    (h51 : h.q ^ 3 ∣ Nat.card G) :
    ∃ X : Subgroup G, IsPGroup h.p X ∧ b.R ≤ X ∧ h.t ∈ Subgroup.normalizer (X : Set G) ∧
      b.τ ∈ Subgroup.normalizer (X : Set G) ∧ b.C ≤ Subgroup.normalizer (X : Set G) ∧
      Nat.card X = h.q ^ 3 := by
  classical
  set Sx : Set (Subgroup G) := {X | IsPGroup h.p X ∧ b.R ≤ X ∧
    h.t ∈ Subgroup.normalizer (X : Set G) ∧ b.τ ∈ Subgroup.normalizer (X : Set G) ∧
    b.C ≤ Subgroup.normalizer (X : Set G)} with hSxdef
  have hRp : IsPGroup h.p b.R := IsPGroup.of_card (by rw [b.card_R, JTHyp.q_eq])
  have hRS : b.R ∈ Sx := ⟨hRp, le_rfl, Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun x hx => (b.R_comm_t hx)), mem_normalizer_of_conj_mem
    fun x hx => by rw [b.τ_inv x hx]; exact Subgroup.inv_mem _ hx, b.C_le_normalizer⟩
  obtain ⟨X, hXS, hXmax⟩ := Set.exists_max_image Sx (fun X => Nat.card X) (Set.toFinite Sx)
    ⟨b.R, hRS⟩
  obtain ⟨hXp, hRX, htX, hτX, hCX⟩ := hXS
  refine ⟨X, hXp, hRX, htX, hτX, hCX, ?_⟩
  refine le_antisymm (b.card_le_cube hp hq5 hp3 hXp htX hτX hCX) ?_
  by_contra hlt
  push Not at hlt
  have hX1 : X ≠ ⊥ := fun h0 => by
    have := Subgroup.card_le_of_le hRX
    rw [h0, Subgroup.card_bot, b.card_R] at this
    have h5 := h.five_lt
    rw [← JTHyp.q_eq] at h5
    omega
  have hXt : Nat.card (X ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) = h.q := by
    rcases b.card_inf_eq hp hq5 hp3 hXp hCX (Or.inl rfl) with h1 | h1
    · exfalso
      have hle : b.R ≤ X ⊓ Subgroup.centralizer ({h.t} : Set G) := fun x hx =>
        ⟨hRX hx, Subgroup.mem_centralizer_singleton_iff.mpr (b.R_comm_t hx)⟩
      have := Subgroup.card_le_of_le hle
      rw [h1, b.card_R] at this
      have h5 := h.five_lt
      rw [← JTHyp.q_eq] at h5
      omega
    · exact h1
  have hprod := b.card_eq_prod hp hq5 hXp htX hτX
  obtain ⟨u, hu, hu1⟩ : ∃ u : G, (u = b.τ ∨ u = h.t * b.τ) ∧
      Nat.card (X ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = 1 := by
    rcases b.card_inf_eq hp hq5 hp3 hXp hCX (Or.inr (Or.inl rfl)) with h2 | h2
    · exact ⟨b.τ, Or.inl rfl, h2⟩
    rcases b.card_inf_eq hp hq5 hp3 hXp hCX (Or.inr (Or.inr rfl)) with h3 | h3
    · exact ⟨h.t * b.τ, Or.inr rfl, h3⟩
    exfalso
    rw [hXt, h2, h3, show h.q * h.q * h.q = h.q ^ 3 by ring] at hprod
    omega
  have huT : u ∈ b.T := by
    rcases hu with rfl | rfl
    · exact b.τ_mem_T
    · exact b.mem_T_iff.mpr (Or.inl rfl)
  have hune : u ≠ 1 := by
    have := b.orderOf_eq_two (Or.inr hu)
    intro h0
    rw [h0, orderOf_one] at this
    omega
  have hq1 : h.q ≠ 1 := by
    have h5 := h.five_lt
    rw [← JTHyp.q_eq] at h5
    omega
  obtain ⟨P, hXP, -, hPp, hPN, hPmem, -⟩ := b.exists_P hp hq5 hp3 hXp hX1 htX hτX hCX
    b.t_mem_T huT h.t_ne_one hune (by rw [hXt, hu1]; exact hq1)
  obtain ⟨y, hyN, ⟨n, hyn⟩, hyX⟩ := exists_pow_eq_one_not_mem hXp fun S =>
    lt_of_lt_of_le hlt (cube_le_card_sylow h51 S)
  have hPS : P ∈ Sx := ⟨hPp, hRX.trans hXP, hPN _ htX, hPN _ hτX, fun x hx => hPN _ (hCX hx)⟩
  have hlt' : Nat.card X < Nat.card P := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hXP) fun h0 => hyX ?_
    have : X = P := Subgroup.eq_of_le_of_card_ge hXP h0.ge
    rw [this]
    exact hPmem y hyN n hyn
  exact absurd (hXmax P hPS) (not_le.mpr hlt')

theorem exists_M₁
    (h51 : h.q ^ 3 ∣ Nat.card G) :
    ∃ P : Subgroup G, b.R ≤ P ∧ P ≤ Subgroup.normalizer (b.R : Set G) ∧ IsPGroup h.p P ∧
      (∀ g ∈ Subgroup.normalizer (b.R : Set G), g ∈ Subgroup.normalizer (P : Set G)) ∧
      (∀ y ∈ Subgroup.normalizer (b.R : Set G), ∀ n : ℕ, y ^ h.p ^ n = 1 → y ∈ P) ∧
      Nat.card P = h.q ^ 3 := by
  classical
  have hRp : IsPGroup h.p b.R := IsPGroup.of_card (by rw [b.card_R, JTHyp.q_eq])
  have hq1 : h.q ≠ 1 := by
    have h5 := h.five_lt
    rw [← JTHyp.q_eq] at h5
    omega
  have hR1 : b.R ≠ ⊥ := fun h0 => by
    have := b.card_R
    rw [h0, Subgroup.card_bot] at this
    exact hq1 this.symm
  have htR : h.t ∈ Subgroup.normalizer (b.R : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun x hx => (b.R_comm_t hx))
  have hτR : b.τ ∈ Subgroup.normalizer (b.R : Set G) :=
    mem_normalizer_of_conj_mem fun x hx => by rw [b.τ_inv x hx]; exact Subgroup.inv_mem _ hx
  have hRt : Nat.card (b.R ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) = h.q := by
    rw [inf_eq_left.mpr (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (b.R_comm_t hx)), b.card_R]
  have hRτ : Nat.card (b.R ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro x hx
    have h1 := b.τ_inv x hx.1
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    rw [← h2, mul_inv_cancel_right] at h1
    have hxx : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel x
    exact Subgroup.mem_bot.mpr (eq_one_of_mul_self_of_odd hxx (Odd.of_dvd_nat
      (h.odd_card_of_isPGroup hp hRp) (Subgroup.orderOf_dvd_natCard _ hx.1)))
  obtain ⟨P, hRP, hPN, hPp, hPn, hPmem, k, hk, hPcard⟩ := b.exists_P hp hq5 hp3 hRp hR1 htR hτR
    b.C_le_normalizer b.t_mem_T b.τ_mem_T h.t_ne_one b.τ_ne_one (by rw [hRt, hRτ]; exact hq1)
  refine ⟨P, hRP, hPN, hPp, hPn, hPmem, ?_⟩
  obtain ⟨X, hXp, -, htX, hτX, hCX, hXcard⟩ := b.exists_cube hp hq5 hp3 h51
  set Z := X ⊓ Subgroup.centralizer (X : Set G) with hZdef
  have hZp : IsPGroup h.p Z := hXp.to_le inf_le_left
  have hZN : ∀ {g : G}, g ∈ Subgroup.normalizer (X : Set G) →
      g ∈ Subgroup.normalizer (Z : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_mem fun z hz => ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1,
      Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have hzx := (Subgroup.mem_centralizer_iff.mp hz.2) _ hx'
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [hzx]
      _ = g * z * g⁻¹ * x := by group
  have hZ1 : Nat.card Z ≠ 1 := by
    have : Nontrivial X := by
      rw [← Finite.one_lt_card_iff_nontrivial, hXcard]
      exact Nat.one_lt_pow (by norm_num) (by omega)
    have hcen := (hXp.center_nontrivial)
    have hZeq : Z = (Subgroup.center X).map X.subtype := by
      ext z
      constructor
      · intro hz
        refine ⟨⟨z, hz.1⟩, Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_, rfl⟩
        exact ((Subgroup.mem_centralizer_iff.mp hz.2) x x.2)
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨x, hx⟩)
    rw [hZeq, Subgroup.card_map_of_injective X.subtype_injective]
    exact (Finite.one_lt_card_iff_nontrivial.mpr hcen).ne'
  have hZprod := b.card_eq_prod hp hq5 hZp (hZN htX) (hZN hτX)
  have hCZ : b.C ≤ Subgroup.normalizer (Z : Set G) := fun x hx => hZN (hCX hx)
  obtain ⟨u, hu, hZu⟩ : ∃ u : G, (u = h.t ∨ u = b.τ ∨ u = h.t * b.τ) ∧
      Nat.card (Z ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = h.q := by
    rcases b.card_inf_eq hp hq5 hp3 hZp hCZ (Or.inl rfl) with h1 | h1
    · rcases b.card_inf_eq hp hq5 hp3 hZp hCZ (Or.inr (Or.inl rfl)) with h2 | h2
      · rcases b.card_inf_eq hp hq5 hp3 hZp hCZ (Or.inr (Or.inr rfl)) with h3 | h3
        · exfalso
          rw [h1, h2, h3] at hZprod
          exact hZ1 hZprod
        · exact ⟨_, Or.inr (Or.inr rfl), h3⟩
      · exact ⟨_, Or.inr (Or.inl rfl), h2⟩
    · exact ⟨_, Or.inl rfl, h1⟩
  obtain ⟨g, hg⟩ := h.exists_conj_of_card_eq hp b.R_le_F b.card_R (b.orderOf_eq_two hu)
    (inf_le_right : Z ⊓ Subgroup.centralizer ({u} : Set G) ≤ _) hZu
  set X' := X.map (MulAut.conj g).toMonoidHom with hX'def
  have hX'N : X' ≤ Subgroup.normalizer (b.R : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg]
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := hy
    have hzx : z * x = x * z := ((Subgroup.mem_centralizer_iff.mp hz.1.2) x hx).symm
    refine ⟨z, hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hzx' : x * z * x⁻¹ = z := by rw [← hzx, mul_inv_cancel_right]
    calc g * z * g⁻¹ = g * (x * z * x⁻¹) * g⁻¹ := by rw [hzx']
      _ = g * x * g⁻¹ * (g * z * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
  have hX'P : X' ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := hXp ⟨x, hx⟩
    have hxn : x ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine hPmem _ (hX'N ⟨x, hx, rfl⟩) n ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hxn, mul_one, mul_inv_cancel]
  have hle := Subgroup.card_le_of_le hX'P
  rw [hX'def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hXcard, hPcard] at hle
  have hq2 : 2 ≤ h.q := by
    have h5 := h.five_lt
    rw [← JTHyp.q_eq] at h5
    omega
  have hk3 : 3 ≤ k := (Nat.pow_le_pow_iff_right hq2).mp hle
  rw [hPcard, show k = 3 by omega]

end BorelData

end CFSG.Walter.JT
