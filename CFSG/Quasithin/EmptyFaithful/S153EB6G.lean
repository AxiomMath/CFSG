module

public import CFSG.Quasithin.EmptyFaithful.S153EB6F
public import CFSG.Quasithin.EmptyFaithful.S153E58In
public import CFSG.Quasithin.EmptyFaithful.S153EB6C

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

structure Induced (V : Type) [CommGroup V] (G Kb : Subgroup (MulAut V)) (a : MulAut V) : Prop where
  KbG : Kb ≤ G
  norm : ∀ g ∈ G, ∀ k ∈ Kb, g * k * g⁻¹ ∈ Kb
  sq : ∀ g ∈ G, g ^ 2 ∈ Kb
  perf : Kb ≤ ⁅Kb, Kb⁆
  ne : Kb ≠ ⊥
  aG : a ∈ G
  a2 : a ^ 2 = 1
  a1 : a ≠ 1
  card : Nat.card ↥(commV (Subgroup.zpowers a)) = 2
  mt : G64.ModuleType G ⊤
  big : 8 ≤ Nat.card V
  exp : ∀ v : V, v ^ 2 = 1

section Perfect

variable {W : Type} [CommGroup W] {H K : Subgroup (MulAut W)}

theorem K_perfect (hK : IsMinNormalIn H K) (hnonab : ¬ (∀ x ∈ K, ∀ y ∈ K, x * y = y * x)) :
    K ≤ ⁅K, K⁆ := by
  have hle : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.2 fun x hx y hy =>
    K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  have hnorm : ∀ h ∈ H, ∀ k ∈ ⁅K, K⁆, h * k * h⁻¹ ∈ ⁅K, K⁆ := by
    intro h hh k hk
    have h1 : ⁅K, K⁆.map (MulAut.conj h).toMonoidHom ≤ ⁅K, K⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_ <;>
      · rintro _ ⟨x, hx, rfl⟩
        exact hK.2.1 h hh x hx
    exact h1 ⟨k, hk, rfl⟩
  rcases hK.2.2.2 ⁅K, K⁆ hle hnorm with h | h
  · exfalso
    apply hnonab
    intro x hx y hy
    have : ⁅x, y⁆ ∈ ⁅K, K⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · rw [h]

end Perfect

section FromSummand

variable {W : Type} [CommGroup W] {H K : Subgroup (MulAut W)} {a : MulAut W}
  {U : Subgroup W}

theorem mem_Xg_iff (hC : Ctx H K a) {x : MulAut W} :
    x ∈ K ⊔ Subgroup.zpowers a ↔ ∃ k ∈ K, ∃ e : ℤ, x = k * a ^ e := by
  have hnorm : ∀ (e : ℤ) (y : MulAut W), y ∈ K → (a ^ e * y * (a ^ e)⁻¹ : MulAut W) ∈ K :=
    fun e y hy => hC.Kn _ (H.zpow_mem hC.aH e) y hy
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨x, hx, 0, by simp⟩
      · obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        exact ⟨1, one_mem _, e, by simp⟩
    | one => exact ⟨1, one_mem _, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k₁, hk₁, e₁, rfl⟩ := hx
      obtain ⟨k₂, hk₂, e₂, rfl⟩ := hy
      refine ⟨k₁ * (a ^ e₁ * k₂ * (a ^ e₁)⁻¹), K.mul_mem hk₁ (hnorm e₁ k₂ hk₂), e₁ + e₂, ?_⟩
      rw [zpow_add]
      group
    | inv x _ hx =>
      obtain ⟨k, hk, e, rfl⟩ := hx
      refine ⟨(a ^ (-e) * k⁻¹ * (a ^ (-e))⁻¹), ?_, -e, ?_⟩
      · exact hnorm (-e) k⁻¹ (K.inv_mem hk)
      · rw [zpow_neg]
        group
  · rintro ⟨k, hk, e, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) e))

theorem Xg_conj_mem (hC : Ctx H K a) {x y : MulAut W} (hx : x ∈ K ⊔ Subgroup.zpowers a)
    (hy : y ∈ K) : x * y * x⁻¹ ∈ K := by
  obtain ⟨k, hk, e, rfl⟩ := (mem_Xg_iff hC).1 hx
  have h1 : (a ^ e * y * (a ^ e)⁻¹ : MulAut W) ∈ K := hC.Kn _ (H.zpow_mem hC.aH e) y hy
  have h2 := hC.Kn k (hC.KH hk) _ h1
  have h3 : k * a ^ e * y * (k * a ^ e)⁻¹ = k * (a ^ e * y * (a ^ e)⁻¹) * k⁻¹ := by group
  rw [h3]
  exact h2

theorem Xg_sq_mem (hC : Ctx H K a) {x : MulAut W} (hx : x ∈ K ⊔ Subgroup.zpowers a) :
    x ^ 2 ∈ K := by
  obtain ⟨k, hk, e, rfl⟩ := (mem_Xg_iff hC).1 hx
  have h1 : (a ^ e * k * (a ^ e)⁻¹ : MulAut W) ∈ K := hC.Kn _ (H.zpow_mem hC.aH e) k hk
  have h2 : a ^ (e + e) = 1 := by
    rw [← two_mul, zpow_mul]
    have : a ^ (2 : ℤ) = 1 := by simpa using hC.a2
    rw [this, one_zpow]
  have h3 : (k * a ^ e) ^ 2 = k * (a ^ e * k * (a ^ e)⁻¹) * a ^ (e + e) := by
    rw [zpow_add, pow_two]; group
  rw [h3, h2, mul_one]
  exact K.mul_mem hk h1

variable [Finite W] in
theorem induced_of_summand (h : G64.LemmaG64) (hexp : ∀ w : W, w ^ 2 = 1) (hC : Ctx H K a)
    (hS : SumCtx K a U) (hK : IsMinNormalIn H K) (hnonab : ¬ (∀ x ∈ K, ∀ y ∈ K, x * y = y * x))
    (hbig : 8 ≤ Nat.card ↥U) :
    Induced ↥U (indG hC hS) (indK hC hS) (indA hC hS) := by
  have hexpU : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (hexp v)
  have hyp := hyp61_ind hexp hC hS
  have hc := card_commV_indA hC hS
  refine ⟨indK_le hC hS, ?_, ?_, ?_, ?_, indA_mem hC hS, indA_sq hC hS, indA_ne_one hC hS, hc,
    moduleType_top (h ↥U hexpU _ _ hyp hc) (exists_sylow_ind hC hS), hbig, hexpU⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨x * y * x⁻¹, ?_, by simp⟩
    exact Xg_conj_mem hC x.2 hy
  · rintro _ ⟨x, rfl⟩
    refine ⟨x ^ 2, ?_, by simp [pow_two]⟩
    exact Xg_sq_mem hC x.2
  · have hK' := K_perfect hK hnonab
    set X := K ⊔ Subgroup.zpowers a with hX
    have hKX : K ≤ X := le_sup_left
    have hmap : (K.subgroupOf X).map X.subtype = K := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 hKX
    have h1 : K.subgroupOf X ≤ ⁅K.subgroupOf X, K.subgroupOf X⁆ := by
      rw [← Subgroup.map_le_map_iff_of_injective X.subtype_injective, Subgroup.map_commutator,
        hmap]
      exact hK'
    unfold indK
    calc ((K.subgroupOf X).map (indRes hC hS))
        ≤ (⁅K.subgroupOf X, K.subgroupOf X⁆).map (indRes hC hS) := Subgroup.map_mono h1
      _ = ⁅(K.subgroupOf X).map (indRes hC hS), (K.subgroupOf X).map (indRes hC hS)⁆ :=
        Subgroup.map_commutator _ _ _
  · intro hbot
    have hfix : ∀ k ∈ K, ∀ u ∈ U, k u = u := by
      intro k hk u hu
      have h1 : indRes hC hS ⟨k, Subgroup.mem_sup_left hk⟩ ∈ indK hC hS := mem_indK hC hS hk
      rw [hbot, Subgroup.mem_bot] at h1
      exact (resX_eq_one_iff (hC.le_stab hS)).1 h1 u hu
    obtain ⟨u₀, hu₀U, hu₀⟩ : ∃ u ∈ U, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hS.irr.1 (eq_bot_iff.2 fun u hu => Subgroup.mem_bot.2 (hcon u hu))
    have hBU : Subgroup.zpowers u₀ ≤ U := Subgroup.zpowers_le.2 hu₀U
    have hBinv : ∀ k ∈ K, ∀ b ∈ Subgroup.zpowers u₀, k b ∈ Subgroup.zpowers u₀ := by
      intro k hk b hb
      rw [hfix k hk b (hBU hb)]
      exact hb
    rcases hS.irr.2.2 _ hBU hBinv with h1 | h1
    · exact hu₀ (Subgroup.mem_bot.1 (h1 ▸ Subgroup.mem_zpowers u₀))
    · have h2 : Nat.card ↥U ≤ 2 := by
        have h3 : Nat.card ↥(Subgroup.zpowers u₀) = orderOf u₀ := Nat.card_zpowers u₀
        have h4 : orderOf u₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (hexp u₀)
        rw [h1] at h3
        rw [h3]
        exact Nat.le_of_dvd (by norm_num) h4
      omega

end FromSummand

end S153EB6

end CFSG.Quasithin
