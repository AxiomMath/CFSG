module

public import CFSG.Walter.ReeOrder.JT.Section6B
public import CFSG.Walter.ReeOrder.JT.AuxGroup

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem mem_of_pow_eq_one_of_normal {p : ℕ} [Fact p.Prime] {H N : Subgroup X} (hNH : N ≤ H)
    (hNn : ∀ x ∈ H, x ∈ Subgroup.normalizer (N : Set X)) (hNp : IsPGroup p N) {m : ℕ}
    (hcard : Nat.card H = Nat.card N * m) (hm : Nat.Coprime m p) {y : X} (hy : y ∈ H) {n : ℕ}
    (hyn : y ^ p ^ n = 1) : y ∈ N := by
  have hyp : IsPGroup p (Subgroup.zpowers y) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one hyn)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hZ := hyp.to_sup_of_normal_right' hNp ((Subgroup.zpowers_le).mpr (hNn y hy))
  set Z := Subgroup.zpowers y ⊔ N with hZdef
  have hZH : Z ≤ H := sup_le ((Subgroup.zpowers_le).mpr hy) hNH
  obtain ⟨j, hj⟩ := hZ.exists_card_eq
  have h1 : Nat.card Z ∣ Nat.card N * m := hcard ▸ Subgroup.card_dvd_of_le hZH
  have h2 : Nat.card Z ∣ Nat.card N :=
    Nat.Coprime.dvd_of_dvd_mul_right (by rw [hj]; exact Nat.Coprime.pow_left j hm.symm) h1
  have heq : N = Z := Subgroup.eq_of_le_of_card_ge le_sup_right
    (Nat.le_of_dvd Nat.card_pos h2)
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

end General

namespace BorelData

variable {h : JTHyp G} (b : BorelData h)

theorem card_mul_sq (K : Subgroup G) (htK : h.t ∈ Subgroup.normalizer (K : Set G))
    (hτK : b.τ ∈ Subgroup.normalizer (K : Set G)) (hK : Odd (Nat.card K)) :
    Nat.card K * Nat.card (K ⊓ Subgroup.centralizer ({h.t} : Set G) ⊓
        Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) ^ 2 =
      Nat.card (K ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) *
        Nat.card (K ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) *
        Nat.card (K ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) : Subgroup G) :=
  card_mul_card_sq_eq_mul h.t_mul_t b.τ_mul_τ h.t_ne_one b.τ_ne_one (Ne.symm b.τ_ne_t)
    b.τ_comm_t.symm K htK hτK hK

theorem orderOf_eq_two {u : G} (hu : u = h.t ∨ u = b.τ ∨ u = h.t * b.τ) : orderOf u = 2 := by
  rcases hu with rfl | rfl | rfl
  · exact h.orderOf_t
  · exact b.orderOf_τ
  · refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      calc h.t * b.τ * (h.t * b.τ) = h.t * (b.τ * h.t) * b.τ := by group
        _ = h.t * (h.t * b.τ) * b.τ := by rw [b.τ_comm_t]
        _ = (h.t * h.t) * (b.τ * b.τ) := by group
        _ = 1 := by rw [h.t_mul_t, b.τ_mul_τ, one_mul]
    · intro h0
      apply b.τ_ne_t
      calc b.τ = h.t⁻¹ * (h.t * b.τ) := by group
        _ = h.t := by rw [h0, mul_one, inv_eq_of_mul_eq_one_right h.t_mul_t]

theorem C_le_centralizer {u : G} (hu : u = h.t ∨ u = b.τ ∨ u = h.t * b.τ) :
    b.C ≤ Subgroup.centralizer ({u} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hu with rfl | rfl | rfl
  · exact b.C_comm_t hx
  · exact b.C_comm x hx
  · calc x * (h.t * b.τ) = (x * h.t) * b.τ := by group
      _ = (h.t * x) * b.τ := by rw [b.C_comm_t hx]
      _ = h.t * (x * b.τ) := by group
      _ = h.t * (b.τ * x) := by rw [b.C_comm x hx]
      _ = h.t * b.τ * x := by group

theorem mem_normalizer_inf {K : Subgroup G} {u v : G}
    (huK : u ∈ Subgroup.normalizer (K : Set G)) (huv : u * v = v * u) :
    u ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun y hy => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp huK y).mp hy.1
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hyv := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have h1 : Commute v u := huv.symm
    have h2 : Commute v y := hyv.symm
    exact ((h1.mul_right h2).mul_right h1.inv_right).symm.eq

variable (hp : h.p ≠ 2) (hq5 : h.q % 8 = 5) (hp3 : h.p ≠ 3)
include hp hq5 hp3

theorem exists_sylow_normal
    {Y : Subgroup G} (hYodd : Odd (Nat.card Y))
    (htY : h.t ∈ Subgroup.normalizer (Y : Set G)) (hτY : b.τ ∈ Subgroup.normalizer (Y : Set G))
    (hCY : b.C ≤ Y) :
    ∃ P : Subgroup G, P ≤ Y ∧ IsPGroup h.p P ∧
      (∀ y ∈ Y, ∀ n : ℕ, y ^ h.p ^ n = 1 → y ∈ P) ∧
      Nat.card Y = Nat.card P * Nat.card b.C ∧ ∃ k ≤ 3, Nat.card P = h.q ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcp := b.coprime_card_C
  have hc0 : 0 < Nat.card b.C := Nat.card_pos
  have hYu : ∀ u : G, (u = h.t ∨ u = b.τ ∨ u = h.t * b.τ) →
      ∃ e ≤ 1, Nat.card (Y ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) =
        h.q ^ e * Nat.card b.C ∧ (e = 1 → ∃ N : Subgroup G,
          N ≤ Y ⊓ Subgroup.centralizer ({u} : Set G) ∧
          (∀ x ∈ Y ⊓ Subgroup.centralizer ({u} : Set G), x ∈ Subgroup.normalizer (N : Set G)) ∧
          IsPGroup h.p N ∧ Nat.card N = h.q) := by
    intro u hu
    rcases b.card_inf_centralizer hp hq5 hp3 (b.orderOf_eq_two hu) inf_le_right
        (Odd.of_dvd_nat hYodd (Subgroup.card_dvd_of_le inf_le_left))
        (le_inf hCY (b.C_le_centralizer hu)) with h1 | ⟨h1, N, hN⟩
    · exact ⟨0, by norm_num, by rw [h1, pow_zero, one_mul], fun h0 => absurd h0 (by norm_num)⟩
    · exact ⟨1, le_rfl, by rw [h1, pow_one], fun _ => ⟨N, hN⟩⟩
  obtain ⟨e₁, he₁, hc₁, hN₁⟩ := hYu h.t (Or.inl rfl)
  obtain ⟨e₂, he₂, hc₂, hN₂⟩ := hYu b.τ (Or.inr (Or.inl rfl))
  obtain ⟨e₃, he₃, hc₃, hN₃⟩ := hYu (h.t * b.τ) (Or.inr (Or.inr rfl))
  have hYT : Y ⊓ Subgroup.centralizer ({h.t} : Set G) ⊓ Subgroup.centralizer ({b.τ} : Set G) =
      b.C := by
    refine le_antisymm (fun y hy => ?_) (le_inf (le_inf hCY (b.C_le_centralizer (Or.inl rfl)))
      (b.C_le_centralizer (Or.inr (Or.inl rfl))))
    exact b.mem_C_of_commute hp hq5 (Subgroup.mem_centralizer_singleton_iff.mp hy.1.2)
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
      (Odd.of_dvd_nat hYodd (Subgroup.orderOf_dvd_natCard _ hy.1.1))
  set k := e₁ + e₂ + e₃ with hkdef
  have hYcard : Nat.card Y = h.q ^ k * Nat.card b.C := by
    have hBW := b.card_mul_sq Y htY hτY hYodd
    rw [hYT, hc₁, hc₂, hc₃] at hBW
    have : Nat.card Y * Nat.card b.C ^ 2 = (h.q ^ k * Nat.card b.C) * Nat.card b.C ^ 2 := by
      rw [hBW, hkdef, pow_add, pow_add]
      ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hc0 2) this
  have hT2 : IsPGroup 2 b.T := IsPGroup.of_card (n := 2) (b.isKleinFour_T.card_four.trans
    (by norm_num))
  have hTY : b.T ≤ Subgroup.normalizer (Y : Set G) := by
    intro x hx
    rcases b.mem_T_iff.mp hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ htY hτY
    · exact htY
    · exact hτY
    · exact Subgroup.one_mem _
  have h2Y : ¬ 2 ∣ Nat.card Y := fun h2 =>
    (Nat.not_even_iff_odd.mpr hYodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨P₀, hP₀T⟩ := exists_sylow_normalized_of_coprime hT2 hTY h2Y h.p
  set P := (P₀ : Subgroup Y).map Y.subtype with hPdef
  have hPY : P ≤ Y := Subgroup.map_subtype_le _
  have hPp : IsPGroup h.p P := P₀.isPGroup'.map _
  have hPcard : Nat.card P = h.q ^ k := by
    rw [hPdef, Subgroup.card_map_of_injective Y.subtype_injective, P₀.card_eq_multiplicity,
      hYcard, Nat.factorization_mul (pow_ne_zero _ (by
        rw [JTHyp.q_eq]; exact pow_ne_zero _ (Fact.out : h.p.Prime).ne_zero)) hc0.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcp.symm), add_zero, JTHyp.q_eq, ← pow_mul,
      Nat.Prime.factorization_pow Fact.out, Finsupp.single_eq_same, pow_mul]
  have hPodd : Odd (Nat.card P) := Odd.of_dvd_nat hYodd (Subgroup.card_dvd_of_le hPY)
  have htP : h.t ∈ Subgroup.normalizer (P : Set G) := hP₀T b.t_mem_T
  have hτP : b.τ ∈ Subgroup.normalizer (P : Set G) := hP₀T b.τ_mem_T
  have hPu : ∀ (u : G) (e : ℕ), e ≤ 1 →
      Nat.card (Y ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = h.q ^ e * Nat.card b.C →
      (e = 1 → ∃ N : Subgroup G, N ≤ Y ⊓ Subgroup.centralizer ({u} : Set G) ∧
          (∀ x ∈ Y ⊓ Subgroup.centralizer ({u} : Set G), x ∈ Subgroup.normalizer (N : Set G)) ∧
          IsPGroup h.p N ∧ Nat.card N = h.q) →
      ∃ N : Subgroup G, P ⊓ Subgroup.centralizer ({u} : Set G) ≤ N ∧
        N ≤ Y ⊓ Subgroup.centralizer ({u} : Set G) ∧
        (∀ x ∈ Y ⊓ Subgroup.centralizer ({u} : Set G), x ∈ Subgroup.normalizer (N : Set G)) ∧
        Nat.card N = h.q ^ e := by
    intro u e he hce hNe
    rcases Nat.lt_or_ge e 1 with he0 | he1
    ·
      have he0 : e = 0 := by omega
      refine ⟨⊥, fun y hy => ?_, bot_le, fun x _ => ?_, by rw [he0, pow_zero, Subgroup.card_bot]⟩
      · have hyo : orderOf y ∣ Nat.card b.C := by
          have := Subgroup.orderOf_dvd_natCard _ (show y ∈ Y ⊓ Subgroup.centralizer
            ({u} : Set G) from ⟨hPY hy.1, hy.2⟩)
          rwa [hce, he0, pow_zero, one_mul] at this
        obtain ⟨n, hn⟩ := hPp ⟨y, hy.1⟩
        have hyn : y ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
        have h1 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n hcp.symm)
          (orderOf_dvd_of_pow_eq_one hyn) hyo
        exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
      · exact mem_normalizer_of_conj_mem fun y hy => by
          rw [Subgroup.mem_bot] at hy ⊢
          rw [hy, mul_one, mul_inv_cancel]
    · have he1' : e = 1 := by omega
      obtain ⟨N, hNY, hNn, hNp, hNcard⟩ := hNe he1'
      refine ⟨N, fun y hy => ?_, hNY, hNn, by rw [hNcard, he1', pow_one]⟩
      obtain ⟨n, hn⟩ := hPp ⟨y, hy.1⟩
      have hyn : y ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
      exact mem_of_pow_eq_one_of_normal hNY hNn hNp (m := Nat.card b.C)
        (by rw [hce, hNcard, he1', pow_one]) hcp ⟨hPY hy.1, hy.2⟩ hyn
  obtain ⟨N₁, hPN₁, hN₁Y, hN₁n, hN₁c⟩ := hPu h.t e₁ he₁ hc₁ hN₁
  obtain ⟨N₂, hPN₂, hN₂Y, hN₂n, hN₂c⟩ := hPu b.τ e₂ he₂ hc₂ hN₂
  obtain ⟨N₃, hPN₃, hN₃Y, hN₃n, hN₃c⟩ := hPu (h.t * b.τ) e₃ he₃ hc₃ hN₃
  have hPT : P ⊓ Subgroup.centralizer ({h.t} : Set G) ⊓ Subgroup.centralizer ({b.τ} : Set G) =
      ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyC : y ∈ b.C := hYT ▸ (⟨⟨hPY hy.1.1, hy.1.2⟩, hy.2⟩ : y ∈ Y ⊓
      Subgroup.centralizer ({h.t} : Set G) ⊓ Subgroup.centralizer ({b.τ} : Set G))
    have h1 : orderOf y ∣ Nat.card b.C := Subgroup.orderOf_dvd_natCard _ hyC
    obtain ⟨n, hn⟩ := hPp ⟨y, hy.1.1⟩
    have hyn : y ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left n hcp.symm) (orderOf_dvd_of_pow_eq_one hyn) h1))
  have hBWP : ∀ P' : Subgroup G, IsPGroup h.p P' → P' ≤ Y →
      h.t ∈ Subgroup.normalizer (P' : Set G) → b.τ ∈ Subgroup.normalizer (P' : Set G) →
      Nat.card P' = Nat.card (P' ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) *
        Nat.card (P' ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) *
        Nat.card (P' ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) : Subgroup G) := by
    intro P' hP'p hP'Y htP' hτP'
    have hBW := b.card_mul_sq P' htP' hτP' (Odd.of_dvd_nat hYodd (Subgroup.card_dvd_of_le hP'Y))
    have hP'T : P' ⊓ Subgroup.centralizer ({h.t} : Set G) ⊓
        Subgroup.centralizer ({b.τ} : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyC : y ∈ b.C := hYT ▸ (⟨⟨hP'Y hy.1.1, hy.1.2⟩, hy.2⟩ : y ∈ Y ⊓
        Subgroup.centralizer ({h.t} : Set G) ⊓ Subgroup.centralizer ({b.τ} : Set G))
      have h1 : orderOf y ∣ Nat.card b.C := Subgroup.orderOf_dvd_natCard _ hyC
      obtain ⟨n, hn⟩ := hP'p ⟨y, hy.1.1⟩
      have hyn : y ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
      exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left n hcp.symm) (orderOf_dvd_of_pow_eq_one hyn) h1))
    rw [hP'T, Subgroup.card_bot, one_pow, mul_one] at hBW
    exact hBW
  have hPcard' := hBWP P hPp hPY htP hτP
  have hle₁ := Subgroup.card_le_of_le hPN₁
  have hle₂ := Subgroup.card_le_of_le hPN₂
  have hle₃ := Subgroup.card_le_of_le hPN₃
  rw [hN₁c] at hle₁
  rw [hN₂c] at hle₂
  rw [hN₃c] at hle₃
  have hprod : h.q ^ e₁ * h.q ^ e₂ * h.q ^ e₃ = h.q ^ k := by rw [hkdef, pow_add, pow_add]
  have hpos : ∀ X : Subgroup G, 0 < Nat.card X := fun X => Nat.card_pos
  have heq : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}, 0 < a₁ → 0 < a₂ → 0 < a₃ → a₁ ≤ b₁ → a₂ ≤ b₂ →
      a₃ ≤ b₃ → a₁ * a₂ * a₃ = b₁ * b₂ * b₃ → a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
    intro a₁ a₂ a₃ b₁ b₂ b₃ h1 h2 h3 h4 h5 h6 h7
    have k1 : a₁ * a₂ * a₃ ≤ b₁ * a₂ * a₃ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h4)
    have k2 : b₁ * a₂ * a₃ ≤ b₁ * b₂ * a₃ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h5)
    have k3 : b₁ * b₂ * a₃ ≤ b₁ * b₂ * b₃ := Nat.mul_le_mul_left _ h6
    have hb₁ : 0 < b₁ := lt_of_lt_of_le h1 h4
    have hb₂ : 0 < b₂ := lt_of_lt_of_le h2 h5
    refine ⟨?_, ?_, ?_⟩
    · by_contra hne
      have : a₁ * a₂ * a₃ < b₁ * a₂ * a₃ := Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne h4 hne) h2) h3
      omega
    · by_contra hne
      have : b₁ * a₂ * a₃ < b₁ * b₂ * a₃ := Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left (lt_of_le_of_ne h5 hne) hb₁) h3
      omega
    · by_contra hne
      have : b₁ * b₂ * a₃ < b₁ * b₂ * b₃ := Nat.mul_lt_mul_of_pos_left (lt_of_le_of_ne h6 hne)
        (Nat.mul_pos hb₁ hb₂)
      omega
  obtain ⟨hq₁, hq₂, hq₃⟩ := heq (hpos _) (hpos _) (hpos _) hle₁ hle₂ hle₃
    (by rw [← hPcard', hPcard, hprod])
  have hPN₁' : P ⊓ Subgroup.centralizer ({h.t} : Set G) = N₁ :=
    Subgroup.eq_of_le_of_card_ge hPN₁ (by rw [hq₁, hN₁c])
  have hPN₂' : P ⊓ Subgroup.centralizer ({b.τ} : Set G) = N₂ :=
    Subgroup.eq_of_le_of_card_ge hPN₂ (by rw [hq₂, hN₂c])
  have hPN₃' : P ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) = N₃ :=
    Subgroup.eq_of_le_of_card_ge hPN₃ (by rw [hq₃, hN₃c])
  have hCP : b.C ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    have hxY := hCY hx
    have hxt : x * h.t = h.t * x := b.C_comm_t hx
    have hxτ : x * b.τ = b.τ * x := b.C_comm x hx
    set P' := P.map (MulAut.conj x).toMonoidHom with hP'def
    have hP'Y : P' ≤ Y := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxY) y).mp (hPY hy)
    have hP'p : IsPGroup h.p P' := hPp.map _
    have hconjN : ∀ {u : G}, x * u = u * x → u ∈ Subgroup.normalizer (P : Set G) →
        u ∈ Subgroup.normalizer (P' : Set G) := by
      intro u hxu huP
      refine mem_normalizer_of_conj_mem fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨u * y * u⁻¹, (Subgroup.mem_normalizer_iff.mp huP y).mp hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h1 : x⁻¹ * u = u * x⁻¹ := (Commute.inv_left (hxu : Commute x u)).eq
      calc x * (u * y * u⁻¹) * x⁻¹ = (x * u) * y * (x * u)⁻¹ := by group
        _ = (u * x) * y * (u * x)⁻¹ := by rw [hxu]
        _ = u * (x * y * x⁻¹) * u⁻¹ := by group
    have htP' : h.t ∈ Subgroup.normalizer (P' : Set G) := hconjN hxt htP
    have hτP' : b.τ ∈ Subgroup.normalizer (P' : Set G) := hconjN hxτ hτP
    have hNu : ∀ {u : G} {N : Subgroup G}, x * u = u * x →
        (∀ x ∈ Y ⊓ Subgroup.centralizer ({u} : Set G), x ∈ Subgroup.normalizer (N : Set G)) →
        P ⊓ Subgroup.centralizer ({u} : Set G) = N →
        N ≤ P ⊓ P' ⊓ Subgroup.centralizer ({u} : Set G) := by
      intro u N hxu hNn hPN y hy
      have hy' : y ∈ P ⊓ Subgroup.centralizer ({u} : Set G) := hPN ▸ hy
      refine ⟨⟨hy'.1, ?_⟩, hy'.2⟩
      have hxN : x ∈ Subgroup.normalizer (N : Set G) :=
        hNn x ⟨hxY, Subgroup.mem_centralizer_singleton_iff.mpr hxu⟩
      have hz : x⁻¹ * y * x ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) y).mp hy
        simpa using this
      have hz' : x⁻¹ * y * x ∈ P ⊓ Subgroup.centralizer ({u} : Set G) := hPN ▸ hz
      refine ⟨x⁻¹ * y * x, hz'.1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hxtτ : x * (h.t * b.τ) = h.t * b.τ * x := by
      rw [← mul_assoc, hxt, mul_assoc, hxτ, ← mul_assoc]
    have hinfN : ∀ {u : G}, u ∈ Subgroup.normalizer (P : Set G) →
        u ∈ Subgroup.normalizer (P' : Set G) →
        u ∈ Subgroup.normalizer ((P ⊓ P' : Subgroup G) : Set G) := fun h1 h2 =>
      mem_normalizer_of_conj_mem fun y hy =>
        ⟨(Subgroup.mem_normalizer_iff.mp h1 y).mp hy.1,
          (Subgroup.mem_normalizer_iff.mp h2 y).mp hy.2⟩
    have hI := hBWP (P ⊓ P') (hPp.to_le inf_le_left) (inf_le_left.trans hPY) (hinfN htP htP')
      (hinfN hτP hτP')
    have hk₁ := Subgroup.card_le_of_le (hNu hxt hN₁n hPN₁')
    have hk₂ := Subgroup.card_le_of_le (hNu hxτ hN₂n hPN₂')
    have hk₃ := Subgroup.card_le_of_le (hNu hxtτ hN₃n hPN₃')
    have hge : Nat.card P ≤ Nat.card (P ⊓ P' : Subgroup G) := by
      rw [hI, hPcard', hPN₁', hPN₂', hPN₃']
      exact Nat.mul_le_mul (Nat.mul_le_mul hk₁ hk₂) hk₃
    have hPP' : P ⊓ P' = P := Subgroup.eq_of_le_of_card_ge inf_le_left hge
    have hPP'' : P = P' := Subgroup.eq_of_le_of_card_ge (hPP' ▸ inf_le_right)
      (by rw [hP'def, Subgroup.card_map_of_injective (MulAut.conj x).injective])
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    rw [hPP'']
    exact ⟨y, hy, rfl⟩
  have hdisj : Disjoint b.C P := Subgroup.disjoint_of_coprime_natCard (by
    rw [hPcard, JTHyp.q_eq, ← pow_mul]
    exact Nat.Coprime.pow_right _ hcp)
  have hCPcard := card_sup_eq_mul_of_disjoint hCP hdisj
  have hYeq : b.C ⊔ P = Y := Subgroup.eq_of_le_of_card_ge (sup_le hCY hPY)
    (by rw [hCPcard, hYcard, hPcard, mul_comm])
  have hYN : ∀ y ∈ Y, y ∈ Subgroup.normalizer (P : Set G) := by
    intro y hy
    rw [← hYeq, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCP] at hy
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    exact Subgroup.mul_mem _ (hCP ha) (Subgroup.le_normalizer hz)
  have hYcard' : Nat.card Y = Nat.card P * Nat.card b.C := by rw [hYcard, hPcard]
  refine ⟨P, hPY, hPp, fun y hy n hyn => mem_of_pow_eq_one_of_normal hPY hYN hPp hYcard' hcp hy
    hyn, hYcard', k, by omega, hPcard⟩

end BorelData

end CFSG.Walter.JT
