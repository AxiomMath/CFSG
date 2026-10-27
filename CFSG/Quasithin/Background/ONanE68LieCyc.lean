module

public import CFSG.Quasithin.Background.ONanE68LieMod
public import CFSG.Quasithin.Background.ONanE68LieSinger

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Singer

variable {S : Type} [Group S] [Finite S] {B W : Subgroup S} {x : S}

theorem SingerHyp.centralizes_pow_iff (h : SingerHyp B W x) (hW : W ≠ ⊥)
    (hBW : B ≤ Subgroup.normalizer (W : Set S)) (j : ℕ) :
    (∀ w ∈ W, x ^ j * w = w * x ^ j) ↔ (Nat.card W - 1) ∣ j := by
  rw [← h.orderOf_actHom hW hBW, orderOf_dvd_iff_pow_eq_one]
  have hxj : x ^ j ∈ B := B.pow_mem h.mem j
  have e : actHom W B hBW ⟨x, h.mem⟩ ^ j = conjOn W (x ^ j) (hBW hxj) := by
    rw [← map_pow, actHom_apply]
    rfl
  rw [e, conjOn_eq_one_iff, Subgroup.mem_centralizer_iff]
  exact ⟨fun hc w hw => (hc w hw).symm, fun hc w hw => (hc w hw).symm⟩

end Singer

section Aut

variable {G : Type} [Group G] {V L : Subgroup G}

theorem theta_range_invariant (hVN : V ≤ Subgroup.normalizer (L : Set G)) (θ : ↥V →* Bar.Qbar L)
    (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, hVN a.2⟩ = MulAut.conj (θ a))
    (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) {y : G} (hyL : y ∈ L)
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) :
    ∀ w ∈ θ.range, piG L y * w * (piG L y)⁻¹ ∈ θ.range := by
  rintro _ ⟨a, rfl⟩
  have hb : y * (a : G) * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hyN a).1 a.2
  refine ⟨⟨_, hb⟩, ?_⟩
  rw [piG_of_mem hyL]
  exact theta_equivariant hVN θ hθ hZ0 ⟨y, hyL⟩ a ⟨_, hb⟩ rfl

end Aut

section Rank

variable {G : Type} [Group G] [Finite G] {V L : Subgroup G}

theorem theta_range_ne_bot (hV2 : IsPGroup 2 V) (hVN : V ≤ Subgroup.normalizer (L : Set G))
    (θ : ↥V →* Bar.Qbar L) (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, hVN a.2⟩ = MulAut.conj (θ a))
    (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) (hperf : Group.IsPerfect ↥L)
    (hm : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≠ 0) : θ.range ≠ ⊥ := by
  intro h0
  have hk : Nat.card θ.range = 2 ^ 0 := by
    rw [h0, pow_zero]
    exact Subgroup.card_bot
  exact hm (mQuot_eq_of_card_range hV2 hVN θ hθ hZ0 hperf hk)

theorem mQuot_bot_eq_of_decomp {U C' : Subgroup G} (hV2 : IsPGroup 2 V) (hUV : U ≤ V)
    (hCV : C' ≤ V) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hinf : U ⊓ C' = ⊥)
    (hsup : U ⊔ C' = V) {n : ℕ} (hn : E3.mQuot V U = n) : E3.mQuot C' ⊥ = n := by
  have hnorm : C' ≤ Subgroup.normalizer (U : Set G) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      have : c * u * c⁻¹ = u := by
        rw [hVc c (hCV hc) u (hUV hu)]
        group
      rw [this]
      exact hu
    · intro hu
      have huV : c * u * c⁻¹ ∈ V := hUV hu
      have hu' : u ∈ V := by
        have := V.mul_mem (V.mul_mem (V.inv_mem (hCV hc)) huV) (hCV hc)
        simpa [mul_assoc] using this
      have : c * u * c⁻¹ = u := by
        rw [hVc c (hCV hc) u hu']
        group
      rwa [this] at hu
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U C' hnorm
    (disjoint_iff.2 hinf)
  rw [hsup] at hcard
  have h1 := E3.card_eq_two_pow_mul hV2 hUV
  rw [hn, hcard] at h1
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have h2 : Nat.card C' = 2 ^ n := by
    exact Nat.eq_of_mul_eq_mul_left hU0 (h1.trans (mul_comm _ _))
  have h3 := E3.card_eq_two_pow_mul (hV2.to_le hCV) (bot_le : (⊥ : Subgroup G) ≤ C')
  rw [h2, Subgroup.card_bot, mul_one] at h3
  exact (Nat.pow_right_injective le_rfl h3).symm

end Rank

section AutCyc

variable {G : Type} [Group G] [Finite G] {V L : Subgroup G}

theorem autI_cyclic_of_singerHyp (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hXL : X ≤ L)
    (hodd : Odd (Nat.card (autI hV X))) (hVN : V ≤ Subgroup.normalizer (L : Set G))
    (θ : ↥V →* Bar.Qbar L) (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, hVN a.2⟩ = MulAut.conj (θ a))
    (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) (hperf : Group.IsPerfect ↥L)
    {B W : Subgroup (Bar.Qbar L)} {x : Bar.Qbar L} (hS : SingerHyp B W x)
    (hBW : B ≤ Subgroup.normalizer (W : Set (Bar.Qbar L))) (hW : θ.range = W) (hW0 : W ≠ ⊥)
    {x₀ : G} (hx₀ : x₀ ∈ X) (hx : piG L x₀ = x)
    (hXB : ∀ y ∈ X, ∃ b ∈ B, ∀ w ∈ W, piG L y * w * (piG L y)⁻¹ = b * w * b⁻¹) :
    IsCyclic (autI hV X) ∧ Nat.card (autI hV X) = Nat.card W - 1 := by
  subst hW hx
  refine autI_cyclic_of_singer hV hXN hXL hodd hVN θ hθ hZ0 hperf hx₀
    (e := Nat.card θ.range - 1) ?_ ?_
  · intro y hy
    obtain ⟨b, hb, hbw⟩ := hXB y hy
    obtain ⟨j, hj⟩ := hS.exists_pow hb
    exact ⟨j, fun w hw => by rw [hbw w hw, hj w hw]⟩
  · intro j
    exact hS.centralizes_pow_iff hW0 hBW j

end AutCyc

end E68Proof

end E6

end CFSG.Quasithin
