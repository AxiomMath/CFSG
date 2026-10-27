module

public import CFSG.RankThree.PartTwo.Sec15.ThmDA10Commute
public import CFSG.RankThree.PartTwo.Sec15.ThmDA10Subgroup
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA.L10

theorem toP_support_card_three : ∀ i j k : Fin 3, (toP i j k).support.card = 3 →
    (toP i j k = pa ∨ toP i j k = pa⁻¹ ∨ toP i j k = pb ∨ toP i j k = pb⁻¹ ∨ toP i j k = pc ∨
      toP i j k = pc⁻¹) := by decide

theorem type_one_cases {x : alternatingGroup (Fin 10)} (hx : x ∈ Ebar)
    (h3 : (x : Perm (Fin 10)).IsThreeCycle) :
    x = ea ∨ x = ea⁻¹ ∨ x = eb ∨ x = eb⁻¹ ∨ x = ec ∨ x = ec⁻¹ := by
  obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hx
  have hc : (toP i j k).support.card = 3 := h3.card_support
  rcases toP_support_card_three i j k hc with h | h | h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h)))))

theorem toP_pow_three : ∀ i j k : Fin 3, toP i j k ^ 3 = 1 := by decide

theorem ew_mem_normalizer_Ebar : ew ∈ Subgroup.normalizer (Ebar : Set (alternatingGroup (Fin 10))) := by
  have h1 : ∀ x ∈ Ebar, ew * x * ew⁻¹ ∈ Ebar := by
    intro x hx
    obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hx
    have : ew * toE i j k * ew⁻¹ = toE k i j := Subtype.ext (pw_mul_toP i j k)
    rw [this]
    exact mem_Ebar_iff_toE.mpr ⟨_, _, _, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun h => ?_⟩
  have h2 := h1 _ h
  have h3 := h1 _ h2
  have e3 : ew * (ew * (ew * x * ew⁻¹) * ew⁻¹) * ew⁻¹ = x := by
    have : ew * ew * ew = 1 := by
      have := ew_pow_three
      simpa [pow_succ] using this
    calc ew * (ew * (ew * x * ew⁻¹) * ew⁻¹) * ew⁻¹ = (ew * ew * ew) * x * (ew * ew * ew)⁻¹ := by group
      _ = x := by rw [this]; simp
  rwa [e3] at h3

theorem card_map_of_injOn {H K : Type*} [Group H] [Group K] (θ : H →* K) {A B : Subgroup H}
    (hBA : B ≤ A) (hθA : ∀ a ∈ A, θ a = 1 → a = 1) : Nat.card (B.map θ) = Nat.card B := by
  have hinj : Function.Injective (θ.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hθA a a.2 ha)
  have h1 : (B.subgroupOf A).map (θ.comp A.subtype) = B.map θ := by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBA]
  rw [← h1, Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv

theorem a10_fusion_core_ebar {H : Type*} [Group H] (θ : H →* alternatingGroup (Fin 10))
    (A : Subgroup H) (hAE : A.map θ = Ebar) (hθA : ∀ a ∈ A, θ a = 1 → a = 1)
    (Ω : Set (Subgroup H))
    (hlift : ∀ n ∈ Subgroup.normalizer (Ebar : Set (alternatingGroup (Fin 10))),
      ∃ m ∈ Subgroup.normalizer (A : Set H), ∀ a ∈ A, θ (m * a * m⁻¹) = n * θ a * n⁻¹)
    (hΩinv : ∀ m ∈ Subgroup.normalizer (A : Set H), ∀ F ∈ Ω,
      F.map (MulAut.conj m).toMonoidHom ∈ Ω)
    (c : H) (hc : c ∈ A) (hcΩ : Subgroup.zpowers c ∈ Ω)
    (hc3 : ((θ c : alternatingGroup (Fin 10)) : Perm (Fin 10)).IsThreeCycle)
    (B : Subgroup H) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hBΩ : ∀ F ∈ Ω, ¬ F ≤ B)
    (p : H) (hp : ∀ b ∈ B, p * b = b * p) (hp2 : IsPGroup 2 (Subgroup.zpowers (θ p))) :
    θ p = 1 := by
  have hx : θ c ∈ Ebar := hAE ▸ Subgroup.mem_map_of_mem θ hc
  have conjpt : ∀ n ∈ Subgroup.normalizer (Ebar : Set (alternatingGroup (Fin 10))),
      ∃ cs ∈ A, Subgroup.zpowers cs ∈ Ω ∧ θ cs = n * θ c * n⁻¹ := by
    intro n hn
    obtain ⟨m, hm, hθm⟩ := hlift n hn
    refine ⟨m * c * m⁻¹, (Subgroup.mem_normalizer_iff.mp hm c).mp hc, ?_, hθm c hc⟩
    have : Subgroup.zpowers (m * c * m⁻¹) =
        (Subgroup.zpowers c).map (MulAut.conj m).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp [MulAut.conj_apply]
    rw [this]
    exact hΩinv m hm _ hcΩ
  have hew := ew_mem_normalizer_Ebar
  have hew2 : ew * ew ∈ Subgroup.normalizer (Ebar : Set (alternatingGroup (Fin 10))) :=
    Subgroup.mul_mem _ hew hew
  obtain ⟨c1, hc1A, hc1Ω, hθc1⟩ := conjpt ew hew
  obtain ⟨c2, hc2A, hc2Ω, hθc2⟩ := conjpt (ew * ew) hew2
  have cj1 : ∀ x : alternatingGroup (Fin 10), ew * x⁻¹ * ew⁻¹ = (ew * x * ew⁻¹)⁻¹ :=
    fun x => by group
  have cj2 : ∀ x : alternatingGroup (Fin 10),
      (ew * ew) * x * (ew * ew)⁻¹ = ew * (ew * x * ew⁻¹) * ew⁻¹ := fun x => by group
  have hthree : (∃ d ∈ A, Subgroup.zpowers d ∈ Ω ∧ (θ d = ea ∨ θ d = ea⁻¹)) ∧
      (∃ d ∈ A, Subgroup.zpowers d ∈ Ω ∧ (θ d = eb ∨ θ d = eb⁻¹)) ∧
      (∃ d ∈ A, Subgroup.zpowers d ∈ Ω ∧ (θ d = ec ∨ θ d = ec⁻¹)) := by
    rcases type_one_cases hx hc3 with h | h | h | h | h | h
    · rw [h, ew_mul_ea] at hθc1
      rw [h, cj2, ew_mul_ea, ew_mul_eb] at hθc2
      exact ⟨⟨c, hc, hcΩ, Or.inl h⟩, ⟨c1, hc1A, hc1Ω, Or.inl hθc1⟩, ⟨c2, hc2A, hc2Ω, Or.inl hθc2⟩⟩
    · rw [h, cj1, ew_mul_ea] at hθc1
      rw [h, cj2, cj1, ew_mul_ea, cj1, ew_mul_eb] at hθc2
      exact ⟨⟨c, hc, hcΩ, Or.inr h⟩, ⟨c1, hc1A, hc1Ω, Or.inr hθc1⟩, ⟨c2, hc2A, hc2Ω, Or.inr hθc2⟩⟩
    · rw [h, ew_mul_eb] at hθc1
      rw [h, cj2, ew_mul_eb, ew_mul_ec] at hθc2
      exact ⟨⟨c2, hc2A, hc2Ω, Or.inl hθc2⟩, ⟨c, hc, hcΩ, Or.inl h⟩, ⟨c1, hc1A, hc1Ω, Or.inl hθc1⟩⟩
    · rw [h, cj1, ew_mul_eb] at hθc1
      rw [h, cj2, cj1, ew_mul_eb, cj1, ew_mul_ec] at hθc2
      exact ⟨⟨c2, hc2A, hc2Ω, Or.inr hθc2⟩, ⟨c, hc, hcΩ, Or.inr h⟩, ⟨c1, hc1A, hc1Ω, Or.inr hθc1⟩⟩
    · rw [h, ew_mul_ec] at hθc1
      rw [h, cj2, ew_mul_ec, ew_mul_ea] at hθc2
      exact ⟨⟨c1, hc1A, hc1Ω, Or.inl hθc1⟩, ⟨c2, hc2A, hc2Ω, Or.inl hθc2⟩, ⟨c, hc, hcΩ, Or.inl h⟩⟩
    · rw [h, cj1, ew_mul_ec] at hθc1
      rw [h, cj2, cj1, ew_mul_ec, cj1, ew_mul_ea] at hθc2
      exact ⟨⟨c1, hc1A, hc1Ω, Or.inr hθc1⟩, ⟨c2, hc2A, hc2Ω, Or.inr hθc2⟩, ⟨c, hc, hcΩ, Or.inr h⟩⟩
  have hB'E : B.map θ ≤ Ebar := hAE ▸ Subgroup.map_mono hBA
  have hB'card : Nat.card (B.map θ) = 9 := (card_map_of_injOn θ hBA hθA).trans hB9
  have hnotin : ∀ d ∈ A, Subgroup.zpowers d ∈ Ω → ∀ e : alternatingGroup (Fin 10),
      (θ d = e ∨ θ d = e⁻¹) → e ∉ B.map θ := by
    intro d hdA hdΩ e hde heB
    obtain ⟨b, hbB, hbe⟩ := heB
    apply hBΩ _ hdΩ
    rw [Subgroup.zpowers_le]
    rcases hde with h | h
    · have h1 : θ (d * b⁻¹) = 1 := by rw [map_mul, map_inv, h, hbe, mul_inv_cancel]
      have h2 := hθA (d * b⁻¹) (A.mul_mem hdA (A.inv_mem (hBA hbB))) h1
      rw [mul_inv_eq_one.mp h2]
      exact hbB
    · have h1 : θ (d * b) = 1 := by rw [map_mul, h, hbe, inv_mul_cancel]
      have h2 := hθA (d * b) (A.mul_mem hdA (hBA hbB)) h1
      rw [eq_inv_of_mul_eq_one_left h2]
      exact B.inv_mem hbB
  obtain ⟨⟨d1, hd1A, hd1Ω, hd1⟩, ⟨d2, hd2A, hd2Ω, hd2⟩, ⟨d3, hd3A, hd3Ω, hd3⟩⟩ := hthree
  obtain ⟨⟨i₁, j₁, hi₁, hj₁, hu₁⟩, ⟨j₂, k₂, hj₂, hk₂, hu₂⟩, ⟨i₃, k₃, hi₃, hk₃, hu₃⟩⟩ :=
    exists_weight_two_of_card_nine hB'E hB'card (hnotin d1 hd1A hd1Ω ea hd1)
      (hnotin d2 hd2A hd2Ω eb hd2) (hnotin d3 hd3A hd3Ω ec hd3)
  have hcomm : ∀ i j k : Fin 3, toE i j k ∈ B.map θ →
      Commute (θ p : Perm (Fin 10)) (toP i j k) := by
    intro i j k hmem
    obtain ⟨b, hb, hbe⟩ := hmem
    have h1 : θ p * θ b = θ b * θ p := by rw [← map_mul, ← map_mul, hp b hb]
    rw [hbe] at h1
    exact congrArg Subtype.val h1
  obtain ⟨i, j, k, hijk⟩ := exists_toP_of_commute_three i₁ j₁ j₂ k₂ i₃ k₃ hi₁ hj₁ hj₂ hk₂ hi₃ hk₃ _
    (hcomm _ _ _ hu₁) (hcomm _ _ _ hu₂) (hcomm _ _ _ hu₃)
  have hθp : θ p = toE i j k := Subtype.ext hijk
  have hp3 : θ p ^ 3 = 1 := by
    rw [hθp]
    exact Subtype.ext (toP_pow_three i j k)
  obtain ⟨n, hn⟩ := hp2 ⟨θ p, Subgroup.mem_zpowers _⟩
  have hn' : θ p ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h1 : orderOf (θ p) ∣ 3 := orderOf_dvd_of_pow_eq_one hp3
  have h2 : orderOf (θ p) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem card_alternatingGroup_fin_ten : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

noncomputable def sylowPst : Sylow 3 (alternatingGroup (Fin 10)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Sylow.ofCard Pst ?_
  rw [card_Pst, card_alternatingGroup_fin_ten]
  have : (1814400 : ℕ).factorization 3 = 4 := by
    have h : (1814400 : ℕ) = 3 ^ 4 * 22400 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp
  rw [this]
  norm_num

theorem exists_conj_eq_Ebar {B : Subgroup (alternatingGroup (Fin 10))} (hB : Nat.card B = 27)
    (hab : ∀ x ∈ B, ∀ y ∈ B, Commute x y) :
    ∃ g : alternatingGroup (Fin 10), B.map (MulAut.conj g⁻¹).toMonoidHom = Ebar := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 3) (by rw [hB]; norm_num)
  obtain ⟨Q, hBQ⟩ := hB3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 10)) sylowPst Q
  have hle : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ Pst := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (Q : Subgroup (alternatingGroup (Fin 10))) := hBQ hx
    rw [← hg, Sylow.coe_subgroup_smul] at hxQ
    obtain ⟨s, hs, hsx⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hxQ
    have hxs : x = g * s * g⁻¹ := by
      rw [← hsx]
      simp [MulAut.smul_def, MulAut.conj_apply]
    have hs' : s ∈ Pst := hs
    have : (MulAut.conj g⁻¹).toMonoidHom x = s := by
      rw [hxs]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hs'
  refine ⟨g, eq_Ebar_of_abelian_card_27 hle ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact Commute.map (hab x hx y hy) _
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hB]

theorem isPGroup_zpowers_of_pow_eq_one {K : Type*} [Group K] {p k : ℕ} {x : K}
    (h : x ^ p ^ k = 1) : IsPGroup p (Subgroup.zpowers x) := by
  intro y
  refine ⟨k, Subtype.ext ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
  have : (y : K) = x ^ m := hm.symm
  show (y : K) ^ p ^ k = 1
  rw [this, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem a10_fusion_core {H : Type*} [Group H] (θ : H →* alternatingGroup (Fin 10))
    (A : Subgroup H) (hAcard : Nat.card A = 27) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hθA : ∀ a ∈ A, θ a = 1 → a = 1) (Ω : Set (Subgroup H))
    (hlift : ∀ n ∈ Subgroup.normalizer ((A.map θ : Subgroup (alternatingGroup (Fin 10))) :
        Set (alternatingGroup (Fin 10))),
      ∃ m ∈ Subgroup.normalizer (A : Set H), ∀ a ∈ A, θ (m * a * m⁻¹) = n * θ a * n⁻¹)
    (hΩinv : ∀ m ∈ Subgroup.normalizer (A : Set H), ∀ F ∈ Ω,
      F.map (MulAut.conj m).toMonoidHom ∈ Ω)
    (c : H) (hc : c ∈ A) (hcΩ : Subgroup.zpowers c ∈ Ω)
    (hc3 : ((θ c : alternatingGroup (Fin 10)) : Perm (Fin 10)).IsThreeCycle)
    (B : Subgroup H) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hBΩ : ∀ F ∈ Ω, ¬ F ≤ B)
    (p : H) (hp : ∀ b ∈ B, p * b = b * p) (hp2 : IsPGroup 2 (Subgroup.zpowers (θ p))) :
    θ p = 1 := by
  have hcardĀ : Nat.card (A.map θ) = 27 := (card_map_of_injOn θ le_rfl hθA).trans hAcard
  have habĀ : ∀ x ∈ A.map θ, ∀ y ∈ A.map θ, Commute x y := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact Commute.map (show Commute a b from hAab a ha b hb) θ
  obtain ⟨g, hg⟩ := exists_conj_eq_Ebar hcardĀ habĀ
  let κ : alternatingGroup (Fin 10) →* alternatingGroup (Fin 10) := (MulAut.conj g⁻¹).toMonoidHom
  have hκinj : Function.Injective κ := (MulAut.conj g⁻¹).injective
  have hκ : ∀ x, κ x = g⁻¹ * x * g := fun x => by simp [κ, MulAut.conj_apply]
  have hAE : A.map (κ.comp θ) = Ebar := by
    rw [← Subgroup.map_map]
    exact hg
  have hθ'A : ∀ a ∈ A, (κ.comp θ) a = 1 → a = 1 := by
    intro a ha h
    exact hθA a ha (hκinj (by simpa using h))
  have hmemĀ : ∀ x, x ∈ A.map θ ↔ κ x ∈ Ebar := by
    intro x
    constructor
    · intro hx
      rw [← hg]
      exact Subgroup.mem_map_of_mem κ hx
    · intro hx
      rw [← hg] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := hκinj hyx
      rwa [hyx'] at hy
  have hcoe : ∀ x : alternatingGroup (Fin 10),
      ((κ x : alternatingGroup (Fin 10)) : Perm (Fin 10)) =
        (g : Perm (Fin 10))⁻¹ * (x : Perm (Fin 10)) * (g : Perm (Fin 10)) := fun x => by
    rw [hκ]; rfl
  refine hκinj ((a10_fusion_core_ebar (κ.comp θ) A hAE hθ'A Ω ?_ hΩinv c hc hcΩ ?_ B hBA hB9 hBΩ
    p hp ?_).trans (map_one κ).symm)
  · intro n' hn'
    have hn : g * n' * g⁻¹ ∈ Subgroup.normalizer
        ((A.map θ : Subgroup (alternatingGroup (Fin 10))) : Set (alternatingGroup (Fin 10))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hmemĀ, hmemĀ]
      have key : κ ((g * n' * g⁻¹) * x * (g * n' * g⁻¹)⁻¹) = n' * κ x * n'⁻¹ := by
        simp only [hκ]
        group
      rw [key]
      exact (Subgroup.mem_normalizer_iff.mp hn' (κ x))
    obtain ⟨m, hm, hθm⟩ := hlift _ hn
    refine ⟨m, hm, fun a ha => ?_⟩
    simp only [MonoidHom.comp_apply, hκ, hθm a ha]
    group
  · have hconj : ((κ (θ c) : alternatingGroup (Fin 10)) : Perm (Fin 10)).cycleType =
        ((θ c : alternatingGroup (Fin 10)) : Perm (Fin 10)).cycleType := by
      rw [hcoe]
      have h := Equiv.Perm.cycleType_conj (τ := (g : Perm (Fin 10))⁻¹)
        (σ := ((θ c : alternatingGroup (Fin 10)) : Perm (Fin 10)))
      rwa [inv_inv] at h
    show _ = _
    simp only [MonoidHom.comp_apply]
    unfold Equiv.Perm.IsThreeCycle at hc3
    rw [hconj]
    exact hc3
  · obtain ⟨n, hn⟩ := hp2 ⟨θ p, Subgroup.mem_zpowers _⟩
    have hn' : θ p ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    refine isPGroup_zpowers_of_pow_eq_one (k := n) ?_
    simp only [MonoidHom.comp_apply]
    rw [← map_pow, hn', map_one]

end CFSG.RankThree.PartTwo.Sec15.ThmD
