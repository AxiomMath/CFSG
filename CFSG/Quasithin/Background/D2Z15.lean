module

public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_sup_of_normalizes {G : Type*} [Group G] {F K : Subgroup G}
    (hn : K ≤ Subgroup.normalizer (F : Set G)) (hinf : F ⊓ K = ⊥) :
    Nat.card ↥(F ⊔ K) = Nat.card F * Nat.card K := by
  let f : ↥F × ↥K → G := fun p => (p.1 : G) * (p.2 : G)
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a' : G)⁻¹ * a = (b' : G) * (b : G)⁻¹ := by
      have : (a : G) * b = a' * b' := h
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [this]
        _ = (b' : G) * (b : G)⁻¹ := by group
    have h2 : (a' : G)⁻¹ * a ∈ F ⊓ K :=
      ⟨F.mul_mem (F.inv_mem a'.2) a.2, by rw [h1]; exact K.mul_mem b'.2 (K.inv_mem b.2)⟩
    rw [hinf, Subgroup.mem_bot] at h2
    have ha : (a : G) = a' := by
      have := congrArg (fun y => (a' : G) * y) h2
      simpa using this
    have hb : (b : G) = b' := by
      have h3 : (b' : G) * (b : G)⁻¹ = 1 := by rw [← h1]; exact h2
      have := congrArg (fun y => y * (b : G)) h3
      exact (by simpa using this : (b' : G) = b).symm
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hrange : Set.range f = ((F ⊔ K : Subgroup G) : Set G) := by
    ext g
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact Subgroup.mul_mem_sup a.2 b.2
    · intro hg
      rw [Subgroup.coe_mul_of_right_le_normalizer_left F K hn] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(F ⊔ K) = Nat.card ↥(Set.range f) := by rw [hrange]; rfl
    _ = Nat.card (↥F × ↥K) := Nat.card_range_of_injective hinj
    _ = Nat.card F * Nat.card K := by rw [Nat.card_prod]

section Embed

variable {s : ℕ} {W : Fin s → Subgroup V} {K : Subgroup (MulAut V)}

omit [Finite V] in
@[expose] noncomputable def restrAll (hK : ∀ i, K ≤ stabSub (W i)) :
    K →* (∀ i, MulAut ↥(W i)) :=
  MonoidHom.pi fun i => (resHom (W i)).comp (Subgroup.inclusion (hK i))

omit [Finite V] in
theorem restrAll_apply (hK : ∀ i, K ≤ stabSub (W i)) (g : K) (i : Fin s) (w : ↥(W i)) :
    ((restrAll hK g i w : ↥(W i)) : V) = (g : MulAut V) w := rfl

omit [Finite V] in
theorem restrAll_injective (hK : ∀ i, K ≤ stabSub (W i)) (htop : ⨆ i, W i = ⊤) :
    Function.Injective (restrAll hK) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ∀ i, ∀ w ∈ W i, (g : MulAut V) w = w := by
    intro i w hw
    have h2 : ((restrAll hK g i ⟨w, hw⟩ : ↥(W i)) : V) = w := by
      rw [congrFun hg i]; rfl
    exact h2
  have : fixV (Subgroup.zpowers (g : MulAut V)) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup_le fun i w hw => mem_fixV_zpowers_iff.mpr (h1 i w hw)
  exact Subtype.ext (eq_one_of_fixV_eq_top this)

theorem card_pi_mulAut (hV : ∀ v : V, v ^ 2 = 1) (hrk : ∀ i, rk (W i) = 2) :
    Nat.card (∀ i, MulAut ↥(W i)) = 6 ^ s := by
  rw [Nat.card_pi]
  have : ∀ i, Nat.card (MulAut ↥(W i)) = 6 := fun i =>
    card_mulAut_of_rk_two (V := ↥(W i)) (fun w => Subtype.ext (by simpa using hV w)) (hrk i)
  simp [this]

theorem card_dvd_of_stab (hV : ∀ v : V, v ^ 2 = 1) (hrk : ∀ i, rk (W i) = 2)
    (htop : ⨆ i, W i = ⊤) (hK : ∀ i, K ≤ stabSub (W i)) : Nat.card K ∣ 6 ^ s := by
  rw [← card_pi_mulAut hV hrk]
  exact Subgroup.card_dvd_of_injective _ (restrAll_injective hK htop)

omit [Finite V] in
theorem rk_commV_involution_rank_two {U : Type*} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) (hrk : rk U = 2) {τ : MulAut U} (hτ : orderOf τ = 2) :
    rk (commV (Subgroup.zpowers τ)) = 1 := by
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := fun e => by rw [e, orderOf_one] at hτ; omega
  have h1 := rk_commV_add_rk_fixV τ
  have h2 := rk_mono (commV_zpowers_le_fixV hU hτ2)
  have h3 := one_le_rk_commV_zpowers hU hτ1
  omega

theorem exists_transvection_of_card_eq (hV : ∀ v : V, v ^ 2 = 1) (hs : 0 < s)
    (hind : iSupIndep W) (htop : ⨆ i, W i = ⊤) (hrk : ∀ i, rk (W i) = 2)
    (hK : ∀ i, K ≤ stabSub (W i)) (hcard : Nat.card K = 6 ^ s) :
    ∃ g ∈ K, g ≠ 1 ∧ g ^ 2 = 1 ∧ rk (commV (Subgroup.zpowers g)) = 1 := by
  classical
  have hbij : Function.Bijective (restrAll hK) :=
    (Nat.bijective_iff_injective_and_card _).mpr
      ⟨restrAll_injective hK htop, by rw [hcard, card_pi_mulAut hV hrk]⟩
  let i₀ : Fin s := ⟨0, hs⟩
  have hVW : ∀ i, ∀ w : ↥(W i), w ^ 2 = 1 := fun i w => Subtype.ext (by simpa using hV w)
  obtain ⟨τ, hτ⟩ : ∃ τ : MulAut ↥(W i₀), orderOf τ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine exists_prime_orderOf_dvd_card' 2 ?_
    rw [card_mulAut_of_rk_two (hVW i₀) (hrk i₀)]
    norm_num
  obtain ⟨g, hg⟩ := hbij.2 (Pi.mulSingle i₀ τ)
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := fun e => by rw [e, orderOf_one] at hτ; omega
  have hgi : ∀ i, i ≠ i₀ → restrAll hK g i = 1 := fun i hi => by
    rw [hg]; exact Pi.mulSingle_eq_of_ne hi _
  have hgi₀ : restrAll hK g i₀ = τ := by rw [hg]; exact Pi.mulSingle_eq_same _ _
  refine ⟨g, g.2, ?_, ?_, ?_⟩
  · intro hg1
    have hg1' : g = 1 := Subtype.ext hg1
    have : restrAll hK g i₀ = 1 := by rw [hg1', map_one]; rfl
    rw [hgi₀] at this
    exact hτ1 this
  · have : g ^ 2 = 1 := by
      apply restrAll_injective hK htop
      rw [map_pow, map_one, hg]
      funext i
      by_cases hi : i = i₀
      · subst hi
        rw [Pi.pow_apply, Pi.mulSingle_eq_same]
        exact hτ2
      · rw [Pi.pow_apply, Pi.mulSingle_eq_of_ne hi]
        simp
    exact congrArg Subtype.val this
  · have hst : ∀ i, (g : MulAut V) ∈ stabSub (W i) := fun i => hK i g.2
    have hinv : ∀ i, ∀ x ∈ Subgroup.zpowers (g : MulAut V), ∀ u ∈ W i, x u ∈ W i :=
      fun i x hx u hu => ((mem_stabSub.mp (Subgroup.zpowers_le.mpr (hst i) hx)) u).mpr hu
    rw [commV_eq_commSub, ← htop, rk_commSub_iSup W hind hinv]
    rw [Finset.sum_eq_single i₀]
    · have hgs := hst i₀
      have h1 := rk_commV_resHom hgs (hinv i₀)
      have e : resHom (W i₀) ⟨(g : MulAut V), hgs⟩ = τ := hgi₀
      rw [e] at h1
      rw [← h1]
      exact rk_commV_involution_rank_two (hVW i₀) (hrk i₀) hτ
    · intro i _ hi
      have hbot : commSub (W i) (Subgroup.zpowers (g : MulAut V)) = ⊥ := by
        rw [commSub_eq_bot_iff]
        intro w hw
        apply mem_fixV_zpowers_iff.mpr
        have h2 : ((restrAll hK g i ⟨w, hw⟩ : ↥(W i)) : V) = w := by
          rw [hgi i hi]; rfl
        exact h2
      rw [hbot, rk_bot]
    · intro hmem
      exact absurd (Finset.mem_univ i₀) hmem

end Embed

section Qhat

variable {X : Subgroup (MulAut V)}

theorem not_transvection (hV : ∀ v : V, v ^ 2 = 1) {r : ℚ} (hq : qhatOf X = (r : WithTop ℚ))
    (hr : 1 < r) {g : MulAut V} (hgX : g ∈ X) (hg1 : g ≠ 1) (hg2 : g ^ 2 = 1)
    (hrk : rk (commV (Subgroup.zpowers g)) = 1) : False := by
  have hBX : Subgroup.zpowers g ≤ X := Subgroup.zpowers_le.mpr hgX
  have hB2 : IsA2 X (Subgroup.zpowers g) :=
    ⟨hBX, fun hbot => hg1 (by rwa [Subgroup.zpowers_eq_bot] at hbot),
      ⟨fun a ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact ((Commute.refl g).zpow_zpow i j).eq,
        fun a ha => by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
          simp [hg2]⟩⟩
  have hB3 : commSeries (Subgroup.zpowers g) 3 = ⊥ :=
    commSeries_eq_bot_of_le (by norm_num)
      ((isQuadratic_iff_commSeries_two _).mp (isQuadratic_zpowers hV hg2))
  have hrB : rAV (Subgroup.zpowers g) ≤ 1 := by
    rw [rAV_zpowers hg1 hg2, hrk]; norm_num
  have h1 : qhatOf X ≤ ((1 : ℚ) : WithTop ℚ) := kq_le_iff.mpr ⟨_, hB2, hB3, hrB⟩
  rw [hq] at h1
  have := WithTop.coe_le_coe.mp h1
  linarith

end Qhat

end CFSG.Quasithin
