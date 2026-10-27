module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DI

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615B

theorem two_coords_ch615 (c : Cx615B G T M L V H n)
    {ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)} (hψ : Function.Injective ψ)
    (hr : ψ.range = autI c.hU (thompsonJ H)) {t : ↥H} (htT : (t : G) ∈ T)
    (ht₁ : ∀ u : SL22, ∃ v : SL22, c.cvH t * ψ (u, 1) * (c.cvH t)⁻¹ = ψ (1, v)) :
    ∃ (a b : ↥H) (r₁ r₂ : SL22), (a : G) ∈ thompsonJ T ∧ (b : G) ∈ thompsonJ T ∧
      r₁ ≠ 1 ∧ r₁ ^ 2 = 1 ∧ r₂ ≠ 1 ∧ r₂ ^ 2 = 1 ∧ c.cvH a = ψ (r₁, 1) ∧
      c.cvH b = ψ (1, r₂) ∧ ∀ j ∈ (thompsonJ T).subgroupOf H,
        c.cvH j = 1 ∨ c.cvH j = ψ (r₁, 1) ∨ c.cvH j = ψ (1, r₂) ∨ c.cvH j = ψ (r₁, r₂) := by
  classical
  obtain ⟨-, -, hsyl, -, -⟩ := c.coords_ch615
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hTH : T ≤ H := c.hH.1.1
  have hJTH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans hTH
  set S := autI c.hU (thompsonJ T) with hS
  rw [← hr] at hsyl
  have hBcard : Nat.card ψ.range = 36 := by
    rw [← card_sl22_sq]
    exact Nat.card_congr (MonoidHom.ofInjective hψ).symm.toEquiv
  have hScard : Nat.card S = 4 := by
    obtain ⟨k, hk⟩ := hsyl.2.1.exists_card_eq
    have hmul : S.relIndex ψ.range * Nat.card S = 36 := by
      have h1 := Subgroup.relIndex_mul_card S ψ.range
      rwa [inf_eq_left.mpr hsyl.1, hBcard] at h1
    rw [hk] at hmul ⊢
    have hodd : ¬ 2 ∣ S.relIndex ψ.range := hsyl.2.2
    have hk5 : k < 6 := by
      by_contra hk6
      have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < S.relIndex ψ.range := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hmul)
      nlinarith
    interval_cases k <;> omega
  have hSmap : (S.comap ψ).map ψ = S := Subgroup.map_comap_eq_self hsyl.1
  have hS'card : Nat.card (S.comap ψ) = 4 := by
    rw [← hScard]
    conv_rhs => rw [← hSmap]
    rw [Subgroup.card_map_of_injective hψ]
  have hS'2 : ∀ s ∈ S.comap ψ, s ^ 2 = 1 := by
    intro s hs
    obtain ⟨k, hk⟩ := hsyl.2.1 ⟨ψ s, hs⟩
    have hk' : ψ (s ^ 2 ^ k) = 1 := by
      rw [map_pow]; simpa using congrArg Subtype.val hk
    exact pow_two_of_pow_two_pow_ch615 (hψ (hk'.trans (map_one ψ).symm))
  have hS'comm : ∀ s ∈ S.comap ψ, ∀ s' ∈ S.comap ψ, s * s' = s' * s := by
    intro s hs s' hs'
    have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := ↥(S.comap ψ))
      (by rw [hS'card]; norm_num)).is_comm.comm ⟨s, hs⟩ ⟨s', hs'⟩
    simpa using congrArg Subtype.val this
  obtain ⟨s₁, hs₁, hs₁1⟩ : ∃ s₁ ∈ S.comap ψ, s₁ ≠ 1 := by
    by_contra hall
    have : S.comap ψ = ⊥ := eq_bot_iff.mpr fun s hs => by
      by_contra hs1
      exact hall ⟨s, hs, hs1⟩
    rw [this, Subgroup.card_bot] at hS'card
    omega
  obtain ⟨s₂, hs₂, hs₂z⟩ : ∃ s₂ ∈ S.comap ψ, s₂ ∉ Subgroup.zpowers s₁ := by
    by_contra hall
    have hle : S.comap ψ ≤ Subgroup.zpowers s₁ := fun s hs => by
      by_contra hs1
      exact hall ⟨s, hs, hs1⟩
    have h1 : Nat.card (S.comap ψ) ≤ Nat.card (Subgroup.zpowers s₁) :=
      Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf s₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (hS'2 s₁ hs₁)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hs₂1 : s₂ ≠ 1 := fun h1 => hs₂z (h1 ▸ Subgroup.one_mem _)
  have hs₁₂ : s₁ ≠ s₂ := fun h1 => hs₂z (h1 ▸ Subgroup.mem_zpowers _)
  obtain ⟨s, hsS', hs2, hs1⟩ : ∃ s ∈ S.comap ψ, s.2 = 1 ∧ s.1 ≠ 1 := by
    rcases exists_inl_sl22 s₁ s₂ hs₁1 hs₂1 hs₁₂ (hS'2 s₁ hs₁) (hS'2 s₂ hs₂)
      (hS'comm s₁ hs₁ s₂ hs₂) with h | h | h
    · exact ⟨s₁, hs₁, h⟩
    · exact ⟨s₂, hs₂, h⟩
    · exact ⟨s₁ * s₂, (S.comap ψ).mul_mem hs₁ hs₂, h⟩
  set r₁ := s.1 with hr₁
  have hseq : s = (r₁, 1) := Prod.ext rfl hs2
  have hr₁2 : r₁ ^ 2 = 1 := by
    have := hS'2 s hsS'
    rw [hseq] at this
    simpa using congrArg Prod.fst this
  have hmem : ψ (r₁, 1) ∈ S := by rw [← hseq]; exact hsS'
  rw [hS, autI_eq_map_convHom c.hU hHN hJTH] at hmem
  obtain ⟨a, ha, haa⟩ := hmem
  have haa' : c.cvH a = ψ (r₁, 1) := haa
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
  obtain ⟨r₂, hr₂⟩ := ht₁ r₁
  set b : ↥H := t * a * t⁻¹ with hb
  have hbJ : (b : G) ∈ thompsonJ T := by
    show (t : G) * a * (t : G)⁻¹ ∈ thompsonJ T
    exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_thompsonJ T)) htT) _).mp ha
  have hbb : c.cvH b = ψ (1, r₂) := by
    rw [hb, map_mul, map_mul, map_inv, haa', hr₂]
  have hr₂1 : r₂ ≠ 1 := by
    intro h1
    apply hs1
    have e : ψ (r₁, 1) = 1 := by
      have := hr₂
      rw [h1, show ((1 : SL22), (1 : SL22)) = 1 from rfl, map_one] at this
      have e2 := congrArg (fun z => (c.cvH t)⁻¹ * z * c.cvH t) this
      simpa [mul_assoc] using e2
    have := hψ (e.trans (map_one ψ).symm)
    simpa using congrArg Prod.fst this
  have hr₂2 : r₂ ^ 2 = 1 := by
    have e : ψ ((1, r₂) ^ 2) = 1 := by
      rw [map_pow, ← hr₂, conj_pow, ← map_pow,
        show (r₁, (1 : SL22)) ^ 2 = 1 from Prod.ext hr₁2 (one_pow 2), map_one]
      group
    have := hψ (e.trans (map_one ψ).symm)
    simpa using congrArg Prod.snd this
  refine ⟨a, b, r₁, r₂, ha, hbJ, hs1, hr₁2, hr₂1, hr₂2, haa', hbb, fun j hj => ?_⟩
  have hjS : c.cvH j ∈ S := by
    rw [hS, autI_eq_map_convHom c.hU hHN hJTH]
    exact ⟨j, hj, rfl⟩
  have hjr : c.cvH j ∈ ψ.range := hsyl.1 hjS
  obtain ⟨w, hw⟩ := hjr
  have hwS : w ∈ S.comap ψ := by rw [Subgroup.mem_comap, hw]; exact hjS
  have hbS : (1, r₂) ∈ S.comap ψ := by
    rw [Subgroup.mem_comap, ← hbb, hS, autI_eq_map_convHom c.hU hHN hJTH]
    exact ⟨b, Subgroup.mem_subgroupOf.mpr hbJ, rfl⟩
  have hw2 := hS'2 w hwS
  have hcw1 := hS'comm w hwS _ hsS'
  have hcw2 := hS'comm w hwS _ hbS
  rw [hseq] at hcw1
  obtain ⟨w₁, w₂⟩ := w
  have hw₁2 : w₁ ^ 2 = 1 := by simpa using congrArg Prod.fst hw2
  have hw₂2 : w₂ ^ 2 = 1 := by simpa using congrArg Prod.snd hw2
  have hc1 : w₁ * r₁ = r₁ * w₁ := by simpa using congrArg Prod.fst hcw1
  have hc2 : w₂ * r₂ = r₂ * w₂ := by simpa using congrArg Prod.snd hcw2
  have k1 : w₁ = 1 ∨ w₁ = r₁ := by
    rcases eq_of_commute_sl22 w₁ r₁ hw₁2 hr₁2 hc1 with h | h | h
    · exact Or.inl h
    · exact absurd h hs1
    · exact Or.inr h
  have k2 : w₂ = 1 ∨ w₂ = r₂ := by
    rcases eq_of_commute_sl22 w₂ r₂ hw₂2 hr₂2 hc2 with h | h | h
    · exact Or.inl h
    · exact absurd h hr₂1
    · exact Or.inr h
  rcases k1 with h1 | h1 <;> rcases k2 with h2 | h2
  · left
    rw [← hw, h1, h2]
    exact map_one ψ
  · right; right; left
    rw [← hw, h1, h2]
  · right; left
    rw [← hw, h1, h2]
  · right; right; right
    rw [← hw, h1, h2]

end Cx615B

namespace Cx615B

variable (c : Cx615B G T M L V H n)

abbrev fac1615 (ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)) :
    Subgroup (MulAut (IntMod (Cx615.UH T H) c.hU)) :=
  ((⊤ : Subgroup SL22).prod ⊥).map ψ

abbrev k1615 (ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)) : Subgroup G :=
  Subgroup.closure {k : G | ∃ hk : k ∈ H, k ∈ oTwoUpper H ∧ Odd (orderOf k) ∧
    c.cvH ⟨k, hk⟩ ∈ fac1615 c ψ}

theorem k1615_le (ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)) :
    k1615 c ψ ≤ oTwoUpper H :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hk, _⟩ => hk

theorem cvH_k1615 (ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)) {x : G}
    (hx : x ∈ k1615 c ψ) (hxH : x ∈ H) : c.cvH ⟨x, hxH⟩ ∈ fac1615 c ψ := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨hyH, -, -, hy⟩ := hy
    exact hy
  | one => rw [show (⟨1, hxH⟩ : ↥H) = 1 from rfl, map_one]; exact Subgroup.one_mem _
  | mul y z hy hz ihy ihz =>
    have hyH : y ∈ H := oTwoUpper_le H (k1615_le c ψ hy)
    have hzH : z ∈ H := oTwoUpper_le H (k1615_le c ψ hz)
    rw [show (⟨y * z, hxH⟩ : ↥H) = ⟨y, hyH⟩ * ⟨z, hzH⟩ from rfl, map_mul]
    exact Subgroup.mul_mem _ (ihy hyH) (ihz hzH)
  | inv y hy ihy =>
    have hyH : y ∈ H := oTwoUpper_le H (k1615_le c ψ hy)
    rw [show (⟨y⁻¹, hxH⟩ : ↥H) = (⟨y, hyH⟩ : ↥H)⁻¹ from rfl, map_inv]
    exact Subgroup.inv_mem _ (ihy hyH)

end Cx615B

namespace Cx615B

theorem pCoreOf_le_centralizer_ch615 (c : Cx615B G T M L V H n)
    {ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)} (hψ : Function.Injective ψ)
    {Y : Subgroup G} (hYH : Y ≤ H) (hY : autI c.hU Y = ψ.range) :
    pCoreOf 2 Y ≤ Subgroup.centralizer (Cx615.UH T H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  set Q := pCoreOf 2 Y with hQ
  have hQY : Q ≤ Y := pCoreOf_le 2 Y
  have hQH : Q ≤ H := hQY.trans hYH
  set N' := (autI c.hU Q).comap ψ with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun y hy w => ?_⟩
    rw [hN', Subgroup.mem_comap] at hy ⊢
    obtain ⟨z, hz, hzw⟩ := (mem_autI c.hU).mp (hY.ge ⟨w, rfl⟩)
    obtain ⟨q, hq, hqy⟩ := (mem_autI c.hU).mp hy
    rw [map_mul, map_mul, map_inv, ← hzw, ← hqy, ← map_inv, ← map_mul, ← map_mul]
    refine convI_mem_autI c.hU ?_ _
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y hz) _).mp hq
  have hN'2 : IsPGroup 2 N' := by
    rintro ⟨y, hy⟩
    obtain ⟨q, hq, hqy⟩ := (mem_autI c.hU).mp hy
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y ⟨q, hq⟩
    have hk' : (q : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    apply hψ
    have : ψ y ^ 2 ^ k = 1 := by
      rw [← hqy, ← map_pow]
      have : q ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
    simpa using this
  have hbot := eq_bot_of_normal_sl22_sq hN'n hN'2
  intro q hq
  have hqN : q ∈ Subgroup.normalizer (Cx615.UH T H : Set G) := hHN (hQH hq)
  have hmem : convI c.hU ⟨q, hqN⟩ ∈ ψ.range := by
    rw [← hY]
    exact convI_mem_autI c.hU (hQY hq) hqN
  obtain ⟨y, hy⟩ := hmem
  have hyN : y ∈ N' := by
    rw [hN', Subgroup.mem_comap, hy]
    exact convI_mem_autI c.hU hq hqN
  rw [hbot, Subgroup.mem_bot] at hyN
  rw [hyN, map_one] at hy
  exact (convI_eq_one_iff c.hU ⟨q, hqN⟩).mp hy.symm

end Cx615B

namespace Cx615B

theorem cvH_oTwoUpper_ch615 (c : Cx615B G T M L V H n)
    {ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)} (hψ : Function.Injective ψ)
    (hr : ψ.range = autI c.hU (thompsonJ H)) {k : G} (hkH : k ∈ H) (hkK : k ∈ oTwoUpper H) :
    ∃ u w : SL22, u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ c.cvH ⟨k, hkH⟩ = ψ (u, w) := by
  obtain ⟨hOJ, -⟩ := c.coords_ch615
  set A := Subgroup.zpowers g3_615
  have hA3 : ∀ u ∈ A, u ^ 3 = 1 := by
    intro u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, g3_615_pow_three,
      one_zpow]
  have hAof : ∀ u : SL22, u ^ 3 = 1 → u ∈ A := by
    intro u hu
    rcases eq_of_pow_three_sl22 u g3_615 hu g3_615_pow_three g3_615_ne_one with h | h | h
    · rw [h]; exact A.one_mem
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]; exact A.inv_mem (Subgroup.mem_zpowers _)
  have hX := c.cvH_mem_of_odd_ch615 hOJ (X := (A.prod A).map ψ) (fun x hx hodd => by
    rw [← hr] at hx
    obtain ⟨s, rfl⟩ := hx
    have hs : Odd (orderOf s) := by rwa [orderOf_injective ψ hψ] at hodd
    have hs3 := pow_three_of_odd_ch615 hs
    exact ⟨s, ⟨hAof s.1 (by simpa using congrArg Prod.fst hs3),
      hAof s.2 (by simpa using congrArg Prod.snd hs3)⟩, rfl⟩) ⟨k, hkH⟩
    (Subgroup.mem_subgroupOf.mpr hkK)
  obtain ⟨⟨u, w⟩, ⟨hu, hw⟩, huw⟩ := hX
  exact ⟨u, w, hA3 u hu, hA3 w hw, huw.symm⟩

theorem exists_mem_k1615_ch615 (c : Cx615B G T M L V H n)
    {ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)}
    (hr : ψ.range = autI c.hU (thompsonJ H)) :
    ∃ (x : G) (hx : x ∈ H), x ∈ k1615 c ψ ∧ Odd (orderOf x) ∧ ∃ g : SL22, g ≠ 1 ∧ g ^ 3 = 1 ∧
      c.cvH ⟨x, hx⟩ = ψ (g, 1) := by
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hm : ψ (g3_615, 1) ∈ autI c.hU (thompsonJ H) := by rw [← hr]; exact ⟨_, rfl⟩
  rw [autI_eq_map_convHom c.hU hHN (thompsonJ_le_self H)] at hm
  obtain ⟨x₀, -, hx₀⟩ := hm
  obtain ⟨e, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  have hodd : Odd (orderOf (x₀ ^ 2 ^ e)) := by
    rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hom, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (pow_pos two_pos e)]
    exact hm
  obtain ⟨hg1, hg3⟩ := g3_pow_two_pow_ch615 e
  have hxg : c.cvH (x₀ ^ 2 ^ e) = ψ (g3_615 ^ 2 ^ e, 1) := by
    rw [map_pow, hx₀, ← map_pow, Prod.pow_mk, one_pow]
  have hodd' : Odd (orderOf ((x₀ ^ 2 ^ e : ↥H) : G)) := by rwa [Subgroup.orderOf_coe]
  refine ⟨((x₀ ^ 2 ^ e : ↥H) : G), (x₀ ^ 2 ^ e).2, Subgroup.subset_closure
    ⟨(x₀ ^ 2 ^ e).2, mem_oTwoUpper_of_odd (x₀ ^ 2 ^ e).2 hodd', hodd', ?_⟩, hodd',
    g3_615 ^ 2 ^ e, hg1, hg3, hxg⟩
  rw [show (⟨((x₀ ^ 2 ^ e : ↥H) : G), (x₀ ^ 2 ^ e).2⟩ : ↥H) = x₀ ^ 2 ^ e from rfl, hxg]
  exact ⟨(g3_615 ^ 2 ^ e, 1), ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩, rfl⟩

theorem mul_mem_fac1615_ch615 (c : Cx615B G T M L V H n)
    {ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)} {x y : MulAut _}
    (hx : x ∈ ψ.range) (hy : y ∈ fac1615 c ψ) : x * y * x⁻¹ ∈ fac1615 c ψ := by
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨s, ⟨-, hs⟩, rfl⟩ := hy
  have hs' : s.2 = 1 := Subgroup.mem_bot.mp hs
  refine ⟨w * s * w⁻¹, ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr ?_⟩, by simp⟩
  show w.2 * s.2 * w.2⁻¹ = 1
  rw [hs', mul_one, mul_inv_cancel]

end Cx615B

namespace Cx615B

theorem cvH_eq_one_iff_ch615 (c : Cx615B G T M L V H n) {x : G} (hx : x ∈ H) :
    c.cvH ⟨x, hx⟩ = 1 ↔ x ∈ Subgroup.centralizer (Cx615.UH T H : Set G) := by
  rw [convHom_apply, convI_eq_one_iff]

theorem cvH_mul_ch615 (c : Cx615B G T M L V H n) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    c.cvH ⟨x * y, H.mul_mem hx hy⟩ = c.cvH ⟨x, hx⟩ * c.cvH ⟨y, hy⟩ := by
  rw [← map_mul]
  rfl

theorem cvH_inv_ch615 (c : Cx615B G T M L V H n) {x : G} (hx : x ∈ H) :
    c.cvH ⟨x⁻¹, H.inv_mem hx⟩ = (c.cvH ⟨x, hx⟩)⁻¹ := by
  rw [← map_inv]
  rfl

end Cx615B

namespace Cx615C

theorem mem_normalizer_k1615_ch615 (hR1 : L2RankOneSylowFact) (c : Cx615C G T M L V H n)
    {ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)} (hψ : Function.Injective ψ)
    (hr : ψ.range = autI c.hU (thompsonJ H)) {t : ↥H} (htT : (t : G) ∈ T)
    (ht₁ : ∀ u : SL22, ∃ v : SL22, c.cvH t * ψ (u, 1) * (c.cvH t)⁻¹ = ψ (1, v)) {d : G}
    (hdK : d ∈ Subgroup.normalizer (oTwoUpper H : Set G))
    (hdS : d ∈ Subgroup.normalizer (s2615 T L H : Set G)) (hdodd : Odd (orderOf d)) :
    d ∈ Subgroup.normalizer (c.k1615 ψ : Set G) := by
  classical
  have h := c.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := Cx615.UH T H with hUdef
  set K := oTwoUpper H with hKdef
  set S2 := s2615 T L H with hS2def
  obtain ⟨hS2T, -, -, -, hautS2, -, -⟩ := c.s2_facts_ch615 hR1
  obtain ⟨hOJ, -, hsyl, -, -⟩ := c.coords_ch615
  obtain ⟨a, b, r₁, r₂, haJ, hbJ, hr₁1, hr₁2, hr₂1, hr₂2, haa, hbb, hJT⟩ :=
    c.two_coords_ch615 hψ hr htT ht₁
  have hTH : T ≤ H := c.hH.1.1
  have hKH : K ≤ H := oTwoUpper_le H
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure _ _
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hS2H : S2 ≤ H := hS2T.trans hTH
  have hJTS2 : thompsonJ T ≤ S2 := (thompsonJ_le_baum_ch615 T).trans le_sup_left
  set Y := K ⊔ S2 with hYdef
  have hYH : Y ≤ H := sup_le hKH hS2H
  obtain ⟨x, hxH, hxK₁, hxodd, g, hg1, hg3, hxg⟩ := c.exists_mem_k1615_ch615 hr
  have hxK : x ∈ K := c.k1615_le ψ hxK₁
  obtain ⟨v, hv⟩ := ht₁ g
  have hv3 : v ^ 3 = 1 := by
    have e : ψ ((1, v) ^ 3) = 1 := by
      rw [map_pow, ← hv, conj_pow, ← map_pow,
        show (g, (1 : SL22)) ^ 3 = 1 from Prod.ext hg3 (one_pow 3), map_one]
      group
    have := hψ (e.trans (map_one ψ).symm)
    simpa using congrArg Prod.snd this
  have hv1 : v ≠ 1 := by
    intro h1
    apply hg1
    have e : ψ (g, 1) = 1 := by
      have := hv
      rw [h1, show ((1 : SL22), (1 : SL22)) = 1 from rfl, map_one] at this
      have e2 := congrArg (fun z => (c.cvH t)⁻¹ * z * c.cvH t) this
      simpa [mul_assoc] using e2
    have := hψ (e.trans (map_one ψ).symm)
    simpa using congrArg Prod.fst this
  set y := (t : G) * x * (t : G)⁻¹ with hydef
  have hyH : y ∈ H := H.mul_mem (H.mul_mem t.2 hxH) (H.inv_mem t.2)
  have hyK : y ∈ K := (Subgroup.mem_normalizer_iff.mp (hHK t.2) x).mp hxK
  have hyv : c.cvH ⟨y, hyH⟩ = ψ (1, v) := by
    rw [← hv, ← hxg, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hautY : autI c.hU Y = ψ.range := by
    apply le_antisymm
    · rw [hr, autI_eq_map_convHom c.hU hHN hYH, Subgroup.subgroupOf_sup hKH hS2H,
        Subgroup.map_sup, ← autI_eq_map_convHom c.hU hHN hKH,
        ← autI_eq_map_convHom c.hU hHN hS2H, hautS2]
      exact sup_le (autI_mono c.hU hOJ) hsyl.1
    · intro z hz
      have htop : (autI c.hU Y).comap ψ = ⊤ := by
        refine eq_top_sl22_sq_of hg1 hg3 hr₁1 hr₁2 hv1 hv3 hr₂1 hr₂2 ?_ ?_ ?_ ?_
        · rw [Subgroup.mem_comap, ← hxg]
          exact convI_mem_autI c.hU (Subgroup.mem_sup_left hxK) (hHN hxH)
        · rw [Subgroup.mem_comap, ← haa]
          exact convI_mem_autI c.hU (Subgroup.mem_sup_right (hJTS2 haJ)) (hHN a.2)
        · rw [Subgroup.mem_comap, ← hyv]
          exact convI_mem_autI c.hU (Subgroup.mem_sup_left hyK) (hHN hyH)
        · rw [Subgroup.mem_comap, ← hbb]
          exact convI_mem_autI c.hU (Subgroup.mem_sup_right (hJTS2 hbJ)) (hHN b.2)
      obtain ⟨w, rfl⟩ := hz
      have : w ∈ (autI c.hU Y).comap ψ := by rw [htop]; exact Subgroup.mem_top w
      exact this
  have hN₀ : Y ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 Y := by
    apply le_antisymm
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
          le_normalizer_centralizer_ch6 hHN (hYH hg)⟩) ?_
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le
        ((inf_le_inf_right _ hYH).trans c.cent.le)
    · exact le_inf (pCoreOf_le 2 Y)
        (c.toCx615B.pCoreOf_le_centralizer_ch615 hψ hYH hautY)
  have hdY : d ∈ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hdK hdS ⊢
    rw [hYdef, Subgroup.map_sup, hdK, hdS]
  have hdN₀ : d ∈ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) :
      Set G) := by
    rw [hN₀]
    exact normalizer_le_normalizer_pCoreOf 2 Y hdY
  have htr : ∀ z ∈ Y, z ∈ Subgroup.centralizer (U : Set G) →
      d * z * d⁻¹ ∈ Subgroup.centralizer (U : Set G) := fun z hz hzC =>
    ((Subgroup.mem_normalizer_iff.mp hdN₀ z).mp ⟨hz, hzC⟩).2
  have htr' : ∀ z ∈ Y, d * z * d⁻¹ ∈ Subgroup.centralizer (U : Set G) →
      z ∈ Subgroup.centralizer (U : Set G) := fun z hz hzC =>
    ((Subgroup.mem_normalizer_iff.mp hdN₀ z).mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hdY z).mp hz, hzC⟩).2
  have hconjY : ∀ z ∈ Y, d * z * d⁻¹ ∈ Y := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp hdY z).mp hz
  have hcomm : ∀ (z w : G) (hz : z ∈ H) (hw : w ∈ H), z * w * z⁻¹ * w⁻¹ ∈
      Subgroup.centralizer (U : Set G) ↔ c.cvH ⟨z, hz⟩ * c.cvH ⟨w, hw⟩ =
        c.cvH ⟨w, hw⟩ * c.cvH ⟨z, hz⟩ := by
    intro z w hz hw
    have hm : z * w * z⁻¹ * w⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hz hw) (H.inv_mem hz)) (H.inv_mem hw)
    rw [← c.cvH_eq_one_iff_ch615 hm]
    have e : c.cvH ⟨z * w * z⁻¹ * w⁻¹, hm⟩ = c.cvH ⟨z, hz⟩ * c.cvH ⟨w, hw⟩ *
        (c.cvH ⟨z, hz⟩)⁻¹ * (c.cvH ⟨w, hw⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  set P : G → Prop := fun s => ∃ k ∈ K, k ∉ Subgroup.centralizer (U : Set G) ∧
    s * k * s⁻¹ * k⁻¹ ∈ Subgroup.centralizer (U : Set G) with hPdef
  have hPb : P b := ⟨x, hxK, fun hC => hg1 (by
      have := (c.cvH_eq_one_iff_ch615 hxH).mpr hC
      rw [hxg] at this
      have := hψ (this.trans (map_one ψ).symm)
      simpa using congrArg Prod.fst this), by
    rw [hcomm b x b.2 hxH, hbb, hxg, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simp) (by simp)⟩
  have hPa : P a := ⟨y, hyK, fun hC => hv1 (by
      have := (c.cvH_eq_one_iff_ch615 hyH).mpr hC
      rw [hyv] at this
      have := hψ (this.trans (map_one ψ).symm)
      simpa using congrArg Prod.snd this), by
    rw [hcomm a y a.2 hyH, haa, hyv, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simp) (by simp)⟩
  have hPab : ¬ P (a * b) := by
    rintro ⟨k, hkK, hkC, hk⟩
    have hkH := hKH hkK
    obtain ⟨u, w, hu3, hw3, huw⟩ := c.cvH_oTwoUpper_ch615 hψ hr hkH hkK
    have hab : c.cvH ⟨(a : G) * b, H.mul_mem a.2 b.2⟩ = ψ (r₁, r₂) := by
      rw [c.cvH_mul_ch615 a.2 b.2, show (⟨(a : G), a.2⟩ : ↥H) = a from rfl,
        show (⟨(b : G), b.2⟩ : ↥H) = b from rfl, haa, hbb, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (by simp)
    rw [hcomm _ k (H.mul_mem a.2 b.2) hkH, hab, huw, ← map_mul, ← map_mul] at hk
    have hk' := hψ hk
    have h1 : r₁ * u = u * r₁ := by simpa using congrArg Prod.fst hk'
    have h2 : r₂ * w = w * r₂ := by simpa using congrArg Prod.snd hk'
    have hu1 := eq_one_of_comm_inv_sl22 u r₁ hu3 hr₁1 hr₁2 h1.symm
    have hw1 := eq_one_of_comm_inv_sl22 w r₂ hw3 hr₂1 hr₂2 h2.symm
    apply hkC
    rw [← c.cvH_eq_one_iff_ch615 hkH, huw, hu1, hw1]
    exact map_one ψ
  have hPd : ∀ s ∈ S2, P s → P (d * s * d⁻¹) := by
    rintro s hs ⟨k, hkK, hkC, hk⟩
    have hkY : k ∈ Y := Subgroup.mem_sup_left hkK
    refine ⟨d * k * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdK k).mp hkK, fun hC =>
      hkC (htr' k hkY hC), ?_⟩
    have hcY : s * k * s⁻¹ * k⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem (Y.mul_mem
      (Subgroup.mem_sup_right hs) hkY) (Y.inv_mem (Subgroup.mem_sup_right hs))) (Y.inv_mem hkY)
    have e : d * s * d⁻¹ * (d * k * d⁻¹) * (d * s * d⁻¹)⁻¹ * (d * k * d⁻¹)⁻¹ =
        d * (s * k * s⁻¹ * k⁻¹) * d⁻¹ := by group
    rw [e]
    exact htr _ hcY hk
  have hPimg : ∀ (s s' : G) (hs : s ∈ H) (hs' : s' ∈ H), c.cvH ⟨s, hs⟩ = c.cvH ⟨s', hs'⟩ →
      P s → P s' := by
    rintro s s' hs hs' he ⟨k, hkK, hkC, hk⟩
    refine ⟨k, hkK, hkC, ?_⟩
    rw [hcomm s' k hs' (hKH hkK), ← he]
    exact (hcomm s k hs (hKH hkK)).mp hk
  set cv : G → MulAut (IntMod U c.hU) := fun z => if hz : z ∈ H then c.cvH ⟨z, hz⟩ else 1
    with hcvdef
  have hcv : ∀ (z : G) (hz : z ∈ H), cv z = c.cvH ⟨z, hz⟩ := fun z hz => by
    simp only [hcvdef, hz, ↓reduceDIte]
  have hS2img : ∀ s ∈ S2, cv s = 1 ∨ cv s = ψ (r₁, 1) ∨ cv s = ψ (1, r₂) ∨
      cv s = ψ (r₁, r₂) := by
    intro s hs
    have hsH := hS2H hs
    have h1 : c.cvH ⟨s, hsH⟩ ∈ autI c.hU S2 := convI_mem_autI c.hU hs (hHN hsH)
    rw [hautS2, autI_eq_map_convHom c.hU hHN ((thompsonJ_le_self T).trans hTH)] at h1
    obtain ⟨j, hj, hjs⟩ := h1
    rw [hcv s hsH, ← hjs]
    exact hJT j hj
  have hteq : ∀ z ∈ Y, ∀ w ∈ Y, cv z = cv w → cv (d * z * d⁻¹) = cv (d * w * d⁻¹) := by
    intro z hz w hw he
    have hzH := hYH hz
    have hwH := hYH hw
    have hz' := hconjY z hz
    have hw' := hconjY w hw
    rw [hcv z hzH, hcv w hwH] at he
    have h1 : z⁻¹ * w ∈ Subgroup.centralizer (U : Set G) := by
      rw [← c.cvH_eq_one_iff_ch615 (H.mul_mem (H.inv_mem hzH) hwH), c.cvH_mul_ch615
        (H.inv_mem hzH) hwH, c.cvH_inv_ch615 hzH, he, inv_mul_cancel]
    have h2 := htr _ (Y.mul_mem (Y.inv_mem hz) hw) h1
    have e : d * (z⁻¹ * w) * d⁻¹ = (d * z * d⁻¹)⁻¹ * (d * w * d⁻¹) := by group
    rw [e, ← c.cvH_eq_one_iff_ch615 (H.mul_mem (H.inv_mem (hYH hz')) (hYH hw')),
      c.cvH_mul_ch615 (H.inv_mem (hYH hz')) (hYH hw'), c.cvH_inv_ch615 (hYH hz'),
      inv_mul_eq_one] at h2
    rw [hcv _ (hYH hz'), hcv _ (hYH hw')]
    exact h2
  have haY : (a : G) ∈ Y := Subgroup.mem_sup_right (hJTS2 haJ)
  have hbY : (b : G) ∈ Y := Subgroup.mem_sup_right (hJTS2 hbJ)
  have hcva : cv a = ψ (r₁, 1) := by rw [hcv _ a.2]; exact haa
  have hcvb : cv b = ψ (1, r₂) := by rw [hcv _ b.2]; exact hbb
  have hne : ψ (r₁, 1) ≠ ψ (1, r₂) := fun he => hr₁1 (by
    have := hψ he
    simpa using congrArg Prod.fst this)
  have hne1 : ψ (r₁, 1) ≠ 1 := fun he => hr₁1 (by
    have := hψ (he.trans (map_one ψ).symm)
    simpa using congrArg Prod.fst this)
  have hne2 : ψ (1, r₂) ≠ 1 := fun he => hr₂1 (by
    have := hψ (he.trans (map_one ψ).symm)
    simpa using congrArg Prod.snd this)
  have hab : cv ((a : G) * b) = ψ (r₁, r₂) := by
    rw [hcv _ (H.mul_mem a.2 b.2), c.cvH_mul_ch615 a.2 b.2,
      show (⟨(a : G), a.2⟩ : ↥H) = a from rfl, show (⟨(b : G), b.2⟩ : ↥H) = b from rfl,
      haa, hbb, ← map_mul]
    congr 1
    exact Prod.ext (by simp) (by simp)
  have himg : ∀ s : ↥H, (s : G) ∈ thompsonJ T → cv s ≠ 1 → P s →
      cv (d * s * d⁻¹) = ψ (r₁, 1) ∨ cv (d * s * d⁻¹) = ψ (1, r₂) := by
    intro s hsJ hs1 hPs
    have hsS2 := hJTS2 hsJ
    have hds : d * s * d⁻¹ ∈ S2 := (Subgroup.mem_normalizer_iff.mp hdS s).mp hsS2
    rcases hS2img _ hds with h1 | h1 | h1 | h1
    · exfalso
      apply hs1
      rw [hcv _ s.2, c.cvH_eq_one_iff_ch615 s.2]
      refine htr' _ (Subgroup.mem_sup_right hsS2) ?_
      rw [← c.cvH_eq_one_iff_ch615 (hS2H hds), ← hcv _ (hS2H hds)]
      exact h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      apply hPab
      refine hPimg _ _ (hS2H hds) (H.mul_mem a.2 b.2) ?_ (hPd _ hsS2 hPs)
      rw [← hcv _ (hS2H hds), ← hcv _ (H.mul_mem a.2 b.2), h1, hab]
  have hda := himg a haJ (by rw [hcva]; exact hne1) hPa
  have hdb := himg b hbJ (by rw [hcvb]; exact hne2) hPb
  have hdadb : cv (d * a * d⁻¹) ≠ cv (d * b * d⁻¹) := by
    intro he
    apply hne
    rw [← hcva, ← hcvb]
    have hda' := hconjY _ haY
    have hdb' := hconjY _ hbY
    rw [hcv _ (hYH hda'), hcv _ (hYH hdb')] at he
    have h1 : (d * a * d⁻¹)⁻¹ * (d * b * d⁻¹) ∈ Subgroup.centralizer (U : Set G) := by
      rw [← c.cvH_eq_one_iff_ch615 (H.mul_mem (H.inv_mem (hYH hda')) (hYH hdb')),
        c.cvH_mul_ch615 (H.inv_mem (hYH hda')) (hYH hdb'), c.cvH_inv_ch615 (hYH hda'), he,
        inv_mul_cancel]
    have e : (d * a * d⁻¹)⁻¹ * (d * b * d⁻¹) = d * ((a : G)⁻¹ * b) * d⁻¹ := by group
    rw [e] at h1
    have h2 := htr' _ (Y.mul_mem (Y.inv_mem haY) hbY) h1
    rw [← c.cvH_eq_one_iff_ch615 (H.mul_mem (H.inv_mem a.2) b.2), c.cvH_mul_ch615
      (H.inv_mem a.2) b.2, c.cvH_inv_ch615 a.2, inv_mul_eq_one] at h2
    rw [hcv _ a.2, hcv _ b.2]
    exact h2
  have hdbb : cv (d * b * d⁻¹) = ψ (1, r₂) := by
    rcases hdb with hdb | hdb
    · exfalso
      have hdaa : cv (d * a * d⁻¹) = ψ (1, r₂) := by
        rcases hda with hda | hda
        · exact absurd (hda.trans hdb.symm) hdadb
        · exact hda
      have hdpow : ∀ m : ℕ, d ^ m ∈ Subgroup.normalizer (Y : Set G) := fun m =>
        Subgroup.pow_mem _ hdY m
      have hind : ∀ m : ℕ, (Even m → cv (d ^ m * b * (d ^ m)⁻¹) = ψ (1, r₂) ∧
          cv (d ^ m * a * (d ^ m)⁻¹) = ψ (r₁, 1)) ∧
          (Odd m → cv (d ^ m * b * (d ^ m)⁻¹) = ψ (r₁, 1) ∧
          cv (d ^ m * a * (d ^ m)⁻¹) = ψ (1, r₂)) := by
        intro m
        induction m with
        | zero =>
          refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
          simp only [pow_zero, one_mul, inv_one, mul_one]
          exact ⟨hcvb, hcva⟩
        | succ m ih =>
          have hzb : d ^ m * b * (d ^ m)⁻¹ ∈ Y :=
            (Subgroup.mem_normalizer_iff.mp (hdpow m) _).mp hbY
          have hza : d ^ m * a * (d ^ m)⁻¹ ∈ Y :=
            (Subgroup.mem_normalizer_iff.mp (hdpow m) _).mp haY
          have eb : d ^ (m + 1) * b * (d ^ (m + 1))⁻¹ =
              d * (d ^ m * b * (d ^ m)⁻¹) * d⁻¹ := by
            rw [pow_succ']; group
          have ea : d ^ (m + 1) * a * (d ^ (m + 1))⁻¹ =
              d * (d ^ m * a * (d ^ m)⁻¹) * d⁻¹ := by
            rw [pow_succ']; group
          rw [eb, ea]
          refine ⟨fun hev => ?_, fun hodd => ?_⟩
          · have hmo : Odd m := by
              rcases Nat.even_or_odd m with hm | hm
              · exact absurd hev (by rw [Nat.even_add_one]; exact not_not.mpr hm)
              · exact hm
            obtain ⟨h1, h2⟩ := ih.2 hmo
            exact ⟨(hteq _ hzb _ haY (h1.trans hcva.symm)).trans hdaa,
              (hteq _ hza _ hbY (h2.trans hcvb.symm)).trans hdb⟩
          · have hme : Even m := by
              rcases Nat.even_or_odd m with hm | hm
              · exact hm
              · exact absurd hodd (by rw [Nat.odd_add_one]; exact not_not.mpr hm)
            obtain ⟨h1, h2⟩ := ih.1 hme
            exact ⟨(hteq _ hzb _ hbY (h1.trans hcvb.symm)).trans hdb,
              (hteq _ hza _ haY (h2.trans hcva.symm)).trans hdaa⟩
      have h1 := ((hind (orderOf d)).2 hdodd).1
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, hcvb] at h1
      exact hne h1.symm
    · exact hdb
  have hgen : ∀ k : G, (∃ hk : k ∈ H, k ∈ K ∧ Odd (orderOf k) ∧
      c.cvH ⟨k, hk⟩ ∈ c.fac1615 ψ) → d * k * d⁻¹ ∈ c.k1615 ψ := by
    rintro k ⟨hkH, hkK, hkodd, hkf⟩
    have hdkK : d * k * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdK k).mp hkK
    have hdkH := hKH hdkK
    have hkY : k ∈ Y := Subgroup.mem_sup_left hkK
    refine Subgroup.subset_closure ⟨hdkH, hdkK, ?_, ?_⟩
    · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hkodd
    · obtain ⟨u, w, hu3, hw3, huw⟩ := c.cvH_oTwoUpper_ch615 hψ hr hdkH hdkK
      obtain ⟨s, ⟨-, hs⟩, hsk⟩ := hkf
      have hs2 : s.2 = 1 := Subgroup.mem_bot.mp hs
      have hbk : (b : G) * k * (b : G)⁻¹ * k⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
        rw [hcomm b k b.2 hkH, hbb, ← hsk, ← map_mul, ← map_mul]
        congr 1
        refine Prod.ext (by simp) ?_
        simp [hs2]
      have hcY : (b : G) * k * (b : G)⁻¹ * k⁻¹ ∈ Y :=
        Y.mul_mem (Y.mul_mem (Y.mul_mem hbY hkY) (Y.inv_mem hbY)) (Y.inv_mem hkY)
      have h1 := htr _ hcY hbk
      have e : d * ((b : G) * k * (b : G)⁻¹ * k⁻¹) * d⁻¹ =
          (d * b * d⁻¹) * (d * k * d⁻¹) * (d * b * d⁻¹)⁻¹ * (d * k * d⁻¹)⁻¹ := by group
      rw [e] at h1
      have hdbH := hYH (hconjY _ hbY)
      rw [hcomm _ _ hdbH hdkH, ← hcv _ hdbH, hdbb, huw, ← map_mul, ← map_mul] at h1
      have h2 := hψ h1
      have hw : w * r₂ = r₂ * w := by simpa using (congrArg Prod.snd h2).symm
      have hw1 := eq_one_of_comm_inv_sl22 w r₂ hw3 hr₂1 hr₂2 hw
      rw [huw, hw1]
      exact ⟨(u, 1), ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩, rfl⟩
  apply mem_normalizer_of_conj_mem_ch6
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem z hz => exact hgen z hz
  | one => simp
  | mul z w _ _ ihz ihw => simpa [mul_assoc] using (c.k1615 ψ).mul_mem ihz ihw
  | inv z _ ih => simpa [mul_assoc] using (c.k1615 ψ).inv_mem ih

end Cx615C

namespace Cx615C

theorem exists_s3_two_ch615 (hR1 : L2RankOneSylowFact) (c : Cx615C G T M L V H n)
    (hK : borelL T L ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    {ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)} (hψ : Function.Injective ψ)
    (hr : ψ.range = autI c.hU (thompsonJ H)) {t : ↥H} (htT : (t : G) ∈ T)
    (ht₁ : ∀ u : SL22, ∃ v : SL22, c.cvH t * ψ (u, 1) * (c.cvH t)⁻¹ = ψ (1, v)) :
    ∃ S P₁ : Subgroup G, S ≤ T ∧ T ⊓ L ≤ S ∧ S ≤ Subgroup.normalizer (P₁ : Set G) ∧
      borelL T L ≤ Subgroup.normalizer (P₁ : Set G) ∧ ¬ P₁ ≤ M ∧ IsSylowTwoOf (S ⊓ P₁) P₁ ∧
      Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3)) ∧ CharTwo (L ⊔ S) ∧
      CharTwo (P₁ ⊔ S ⊔ borelL T L) := by
  classical
  have h := c.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := Cx615.UH T H with hUdef
  set K := oTwoUpper H with hKdef
  set S2 := s2615 T L H with hS2def
  set K₁ := c.k1615 ψ with hK₁def
  set P₁ := K₁ ⊔ S2 with hP₁def
  obtain ⟨hS2T, hTLS, hBS2, -, hautS2, hcL, hcX⟩ := c.s2_facts_ch615 hR1
  obtain ⟨hOJ, -, hsyl, hsylB, -⟩ := c.coords_ch615
  obtain ⟨a, b, r₁, r₂, haJ, hbJ, hr₁1, hr₁2, hr₂1, hr₂2, haa, hbb, hJT⟩ :=
    c.two_coords_ch615 hψ hr htT ht₁
  obtain ⟨x, hxH, hxK₁, hxodd, g, hg1, hg3, hxg⟩ := c.exists_mem_k1615_ch615 hr
  have hTH : T ≤ H := c.hH.1.1
  have hKH : K ≤ H := oTwoUpper_le H
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure _ _
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hS2H : S2 ≤ H := hS2T.trans hTH
  have hK₁K : K₁ ≤ K := c.k1615_le ψ
  have hK₁H : K₁ ≤ H := hK₁K.trans hKH
  have hP₁H : P₁ ≤ H := sup_le hK₁H hS2H
  have hJTS2 : thompsonJ T ≤ S2 := (thompsonJ_le_baum_ch615 T).trans le_sup_left
  have hS2r : ∀ s ∈ S2, ∀ hs : s ∈ H, c.cvH ⟨s, hs⟩ ∈ ψ.range := by
    intro s hs hsH
    rw [hr]
    have h1 : c.cvH ⟨s, hsH⟩ ∈ autI c.hU S2 := convI_mem_autI c.hU hs (hHN hsH)
    rw [hautS2] at h1
    exact hsyl.1 h1
  have hS2K₁ : S2 ≤ Subgroup.normalizer (K₁ : Set G) := by
    intro s hs
    apply mem_normalizer_of_conj_mem_ch6
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨hzH, hzK, hzodd, hzf⟩ := hz
      have hszK : s * z * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hHK (hS2H hs)) z).mp hzK
      refine Subgroup.subset_closure ⟨hKH hszK, hszK, ?_, ?_⟩
      · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hzodd
      · have e : c.cvH ⟨s * z * s⁻¹, hKH hszK⟩ =
            c.cvH ⟨s, hS2H hs⟩ * c.cvH ⟨z, hzH⟩ * (c.cvH ⟨s, hS2H hs⟩)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]; rfl
        rw [e]
        exact c.mul_mem_fac1615_ch615 (hS2r s hs (hS2H hs)) hzf
    | one => simp
    | mul z w _ _ ihz ihw => simpa [mul_assoc] using K₁.mul_mem ihz ihw
    | inv z _ ih => simpa [mul_assoc] using K₁.inv_mem ih
  have hsup : ∀ y : G, y ∈ Subgroup.normalizer (K₁ : Set G) →
      y ∈ Subgroup.normalizer (S2 : Set G) → y ∈ Subgroup.normalizer (P₁ : Set G) := by
    intro y h1 h2
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hBP : borelL T L ≤ Subgroup.normalizer (P₁ : Set G) := by
    rw [← h.toHyp5_0_1.borelL_eq_sup hD]
    refine sup_le (fun d hd => hsup d ?_ (hBS2 (hD.1 hd))) (fun s hs => hsup s (hS2K₁ (hTLS hs))
      (Subgroup.le_normalizer (hTLS hs)))
    exact c.mem_normalizer_k1615_ch615 hR1 hψ hr htT ht₁ (hK (hD.1 hd)) (hBS2 (hD.1 hd))
      (Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hd))
  refine ⟨S2, P₁, hS2T, hTLS, fun s hs => hsup s (hS2K₁ hs) (Subgroup.le_normalizer hs), hBP,
    ?_, ?_, ?_, hcL, ?_⟩
  ·
    intro hle
    apply c.oTwoUpper_not_le_ch615
    set Y := K₁ ⊔ T with hY
    have hYH : Y ≤ H := sup_le hK₁H hTH
    have hYM : Y ≤ M := sup_le (le_sup_left.trans hle) h.T_le
    refine le_trans ?_ hYM
    intro k hk
    have hkH := hKH hk
    obtain ⟨u, w, hu3, hw3, huw⟩ := c.cvH_oTwoUpper_ch615 hψ hr hkH hk
    have hpow : ∀ z : SL22, z ≠ 1 → z ^ 3 = 1 → ∀ u : SL22, u ^ 3 = 1 → ∃ i : ℕ, u = z ^ i := by
      intro z hz1 hz3 u hu
      rcases eq_of_pow_three_sl22 u z hu hz3 hz1 with h1 | h1 | h1
      · exact ⟨0, by rw [h1, pow_zero]⟩
      · exact ⟨1, by rw [h1, pow_one]⟩
      · refine ⟨2, ?_⟩
        rw [h1]
        calc z⁻¹ = z⁻¹ * z ^ 3 := by rw [hz3, mul_one]
          _ = z ^ 2 := by group
    obtain ⟨v, hv⟩ := ht₁ g
    have hv3 : v ^ 3 = 1 := by
      have e : ψ ((1, v) ^ 3) = 1 := by
        rw [map_pow, ← hv, conj_pow, ← map_pow,
          show (g, (1 : SL22)) ^ 3 = 1 from Prod.ext hg3 (one_pow 3), map_one]
        group
      have := hψ (e.trans (map_one ψ).symm)
      simpa using congrArg Prod.snd this
    have hv1 : v ≠ 1 := by
      intro h1
      apply hg1
      have e : ψ (g, 1) = 1 := by
        have := hv
        rw [h1, show ((1 : SL22), (1 : SL22)) = 1 from rfl, map_one] at this
        have e2 := congrArg (fun z => (c.cvH t)⁻¹ * z * c.cvH t) this
        simpa [mul_assoc] using e2
      have := hψ (e.trans (map_one ψ).symm)
      simpa using congrArg Prod.fst this
    obtain ⟨i, hi⟩ := hpow g hg1 hg3 u hu3
    obtain ⟨j, hj⟩ := hpow v hv1 hv3 w hw3
    have hyY : ∃ (y : G) (hy : y ∈ H), y ∈ Y ∧ c.cvH ⟨y, hy⟩ = ψ (u, w) := by
      refine ⟨x ^ i * ((t : G) * x ^ j * (t : G)⁻¹), H.mul_mem (H.pow_mem hxH i)
        (H.mul_mem (H.mul_mem t.2 (H.pow_mem hxH j)) (H.inv_mem t.2)),
        Y.mul_mem (Y.pow_mem (Subgroup.mem_sup_left hxK₁) i)
        (Y.mul_mem (Y.mul_mem (Subgroup.mem_sup_right htT)
          (Y.pow_mem (Subgroup.mem_sup_left hxK₁) j)) (Y.inv_mem (Subgroup.mem_sup_right htT))),
        ?_⟩
      have e : c.cvH ⟨x ^ i * ((t : G) * x ^ j * (t : G)⁻¹), H.mul_mem (H.pow_mem hxH i)
          (H.mul_mem (H.mul_mem t.2 (H.pow_mem hxH j)) (H.inv_mem t.2))⟩ =
          c.cvH ⟨x, hxH⟩ ^ i * (c.cvH t * c.cvH ⟨x, hxH⟩ ^ j * (c.cvH t)⁻¹) := by
        rw [← map_pow, ← map_pow, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [e, hxg, ← conj_pow, hv, ← map_pow, ← map_pow, ← map_mul, hi, hj]
      congr 1
      exact Prod.ext (by simp) (by simp)
    obtain ⟨y, hyH, hyY, hyuw⟩ := hyY
    have hyk : y⁻¹ * k ∈ Subgroup.centralizer (U : Set G) := by
      rw [← c.cvH_eq_one_iff_ch615 (H.mul_mem (H.inv_mem hyH) hkH),
        c.cvH_mul_ch615 (H.inv_mem hyH) hkH, c.cvH_inv_ch615 hyH, hyuw, huw, inv_mul_cancel]
    have hyT : y⁻¹ * k ∈ T := (F7.isSylowTwoOf_pCoreOf_le c.toCx615.isSylowTwoOf)
      (c.cent.le ⟨H.mul_mem (H.inv_mem hyH) hkH, hyk⟩)
    have e : k = y * (y⁻¹ * k) := by group
    rw [e]
    exact Y.mul_mem hyY (Subgroup.mem_sup_right hyT)
  · rw [inf_of_le_left le_sup_right]
    exact isSylowTwoOf_sup_ch615 (le_sup_left : baum T ≤ S2) (h.sylow.1.to_le hS2T) hS2K₁
      (F7.isSylowTwoOf_mono_right hsylB le_sup_right (sup_le_sup_right hK₁K _))
  ·
    have hP₁N : P₁ ≤ Subgroup.normalizer (U : Set G) := hP₁H.trans hHN
    set φ := convHom c.hU P₁ hP₁N with hφ
    set Ω : Subgroup (MulAut (IntMod U c.hU)) :=
      ((⊤ : Subgroup SL22).prod (Subgroup.zpowers r₂)).map ψ with hΩ
    have hrange : φ.range ≤ Ω := by
      rw [range_convHom, autI_eq_map_convHom c.hU hHN hP₁H,
        Subgroup.subgroupOf_sup hK₁H hS2H, Subgroup.map_sup,
        ← autI_eq_map_convHom c.hU hHN hK₁H, ← autI_eq_map_convHom c.hU hHN hS2H, hautS2]
      refine sup_le ?_ ?_
      · intro z hz
        obtain ⟨k, hk, rfl⟩ := (mem_autI c.hU).mp hz
        obtain ⟨s, hs, hsk⟩ := c.cvH_k1615 ψ hk (hK₁H hk)
        have hs2 : s.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hs).2
        refine ⟨s, Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ?_⟩, hsk⟩
        rw [hs2]
        exact Subgroup.one_mem _
      · intro z hz
        rw [autI_eq_map_convHom c.hU hHN ((thompsonJ_le_self T).trans hTH)] at hz
        obtain ⟨j, hj, rfl⟩ := hz
        rcases hJT j hj with h1 | h1 | h1 | h1 <;> rw [h1]
        · exact Ω.one_mem
        · exact ⟨(r₁, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩, rfl⟩
        · exact ⟨(1, r₂), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_zpowers _⟩,
            rfl⟩
        · exact ⟨(r₁, r₂), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_zpowers _⟩,
            rfl⟩
    have hΩr : Ω ≤ ψ.range := Subgroup.map_le_range ψ _
    set θ : SL22 × SL22 ≃* ↥ψ.range := MonoidHom.ofInjective hψ with hθ
    set ρ₀ : ↥P₁ →* SL22 × SL22 :=
      θ.symm.toMonoidHom.comp (φ.codRestrict ψ.range fun p => hΩr (hrange ⟨p, rfl⟩))
      with hρ₀
    have hψρ₀ : ∀ p : ↥P₁, ψ (ρ₀ p) = φ p := by
      intro p
      have e1 : θ (ρ₀ p) = ⟨φ p, hΩr (hrange ⟨p, rfl⟩)⟩ := by rw [hρ₀]; simp
      have := congrArg Subtype.val e1
      rw [hθ, MonoidHom.ofInjective_apply] at this
      exact this
    set ρ : ↥P₁ →* SL22 := (MonoidHom.fst SL22 SL22).comp ρ₀ with hρ
    have hker2 : IsPGroup 2 ρ.ker := by
      rintro ⟨p, hp⟩
      have hp1 : (ρ₀ p).1 = 1 := hp
      obtain ⟨⟨u', w'⟩, huw'm, huw'⟩ := hrange ⟨p, rfl⟩
      have hw' : w' ∈ Subgroup.zpowers r₂ := (Subgroup.mem_prod.mp huw'm).2
      have e1 : ρ₀ p = (u', w') := hψ ((hψρ₀ p).trans huw'.symm)
      rw [e1] at hp1
      have hu1 : u' = 1 := hp1
      have hw2 : w' ^ 2 = 1 := by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw'
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hr₂2,
          one_zpow]
      have hp2 : ρ₀ (p ^ 2) = 1 := by
        rw [map_pow, e1]
        exact Prod.ext (by simp [hu1]) (by simpa using hw2)
      have hpC : ((p ^ 2 : ↥P₁) : G) ∈ Subgroup.centralizer (U : Set G) := by
        have := congrArg ψ hp2
        rw [hψρ₀, map_one, hφ, convHom_apply, convI_eq_one_iff] at this
        exact this
      have hpO : ((p ^ 2 : ↥P₁) : G) ∈ pCoreOf 2 H :=
        c.cent.le ⟨hP₁H (p ^ 2).2, hpC⟩
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨_, hpO⟩
      refine ⟨k + 1, Subtype.ext (Subtype.ext ?_)⟩
      have hk' : (((p ^ 2 : ↥P₁) : G)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [pow_succ', pow_mul]
      simpa using hk'
    have hρs : Function.Surjective ρ := by
      rw [← MonoidHom.range_eq_top]
      set x' : ↥P₁ := ⟨x, Subgroup.mem_sup_left hxK₁⟩
      set a' : ↥P₁ := ⟨a, Subgroup.mem_sup_right (hJTS2 haJ)⟩
      have hx' : ρ x' = g := by
        have e1 : ρ₀ x' = (g, 1) := hψ ((hψρ₀ x').trans hxg)
        rw [hρ, MonoidHom.comp_apply, e1]
        rfl
      have ha' : ρ a' = r₁ := by
        have e1 : ρ₀ a' = (r₁, 1) := hψ ((hψρ₀ a').trans haa)
        rw [hρ, MonoidHom.comp_apply, e1]
        rfl
      exact eq_top_sl22 (a := r₁) (b := g) ⟨a', ha'⟩ hr₁1 hr₁2 ⟨x', hx'⟩ hg1 hg3
    exact nonempty_oTwoQuot_ch615 ρ hρs hker2
  · refine charTwo_of_le_ch615 (P := borelL T L ⊔ H) ?_ hcX ?_
    · exact sup_le (sup_le (hP₁H.trans le_sup_right) (hS2H.trans le_sup_right)) le_sup_left
    · exact (le_sup_right : pCoreOf 2 (borelL T L ⊔ H) ≤ S2).trans (le_sup_right.trans
        le_sup_left)

end Cx615C

end CFSG.Quasithin.H13
