module

public import CFSG.Quasithin.EmptyFaithful.S143ID
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.Quasithin.EmptyFaithful.S143IC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Util

theorem isSylowTwoOf_of_le_of_sylow {G : Type} [Group G] {T H : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) : IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩

end Util

section Final

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.exists_commutator_of_conj_mem_qOf (hQ : qOf T = uOfL22 T M ⊔ dOf T M) {y z s : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (hys : y * z * y⁻¹ = s)
    (hζ : y⁻¹ * z * y ∈ qOf T) : ∃ a ∈ mcOf T, ∃ b ∈ mcOf T, a * b * a⁻¹ * b⁻¹ = s := by
  have h := c.h1281
  have hq8 := c.c15.q8sq
  have hcenter : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T := c.centerOf_uOfL22_eq
  rw [hQ] at hζ
  have hDN : dOf T M ≤ Subgroup.normalizer (uOfL22 T M : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2
  obtain ⟨u, hu, d, hd, hud⟩ :=
    (CFSG.QuasithinUnique.Lin2.mem_sup_iff_of_le_normalizer hDN).1 hζ
  have hdc : ∀ a ∈ uOfL22 T M, a * d = d * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 a ha
  have hZcen : ∀ x ∈ quasithinOmegaOneCenter T, ∀ w ∈ uOfL22 T M, x * w = w * x :=
    fun x hx w hw =>
      (Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hx).2 w hw).symm
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ uOfL22 T M ⊓ Subgroup.centralizer ({u} : Set G),
      ∃ b ∈ uOfL22 T M ⊓ Subgroup.centralizer ({u} : Set G), a * b ≠ b * a := by
    apply c.exists_noncomm_of_card_ge (inf_le_left)
    by_cases huZ : u ∈ quasithinOmegaOneCenter T
    · have hall : uOfL22 T M ⊓ Subgroup.centralizer ({u} : Set G) = uOfL22 T M :=
        inf_eq_left.mpr fun w hw =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hZcen u huZ w hw).symm
      rw [hall, hq8.1]
      norm_num
    · have hxc : u ∉ centerOf (uOfL22 T M) := by rw [hcenter]; exact huZ
      have := isQ8Sq_card_centralizer hq8 u hu hxc
      omega
  have hcomm_Z : a * b * a⁻¹ * b⁻¹ ∈ quasithinOmegaOneCenter T :=
    h.commutator_mem_omegaOneCenter ha.1 hb.1
  have hcomm_ne : a * b * a⁻¹ * b⁻¹ ≠ 1 := by
    intro he
    apply hab
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [he]; group
  have hcomm_z : a * b * a⁻¹ * b⁻¹ = z := by
    rcases c.mem_Z_cases hz hz1 hcomm_Z with h1 | h1
    · exact absurd h1 hcomm_ne
    · exact h1
  have hzy : z = y * (u * d) * y⁻¹ := by rw [← hud]; group
  have hcommute : ∀ w ∈ uOfL22 T M ⊓ Subgroup.centralizer ({u} : Set G),
      (y * w * y⁻¹) * z = z * (y * w * y⁻¹) := by
    intro w hw
    have hwu : w * u = u * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
    have hwζ : w * (u * d) = (u * d) * w := by
      calc w * (u * d) = (w * u) * d := by group
        _ = (u * w) * d := by rw [hwu]
        _ = u * (w * d) := by group
        _ = u * (d * w) := by rw [hdc w hw.1]
        _ = (u * d) * w := by group
    rw [hzy]
    calc y * w * y⁻¹ * (y * (u * d) * y⁻¹) = y * (w * (u * d)) * y⁻¹ := by group
      _ = y * ((u * d) * w) * y⁻¹ := by rw [hwζ]
      _ = y * (u * d) * y⁻¹ * (y * w * y⁻¹) := by group
  refine ⟨y * a * y⁻¹, c.mem_mcOf_of_comm hz hz1 (hcommute a ha), y * b * y⁻¹,
    c.mem_mcOf_of_comm hz hz1 (hcommute b hb), ?_⟩
  calc y * a * y⁻¹ * (y * b * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * b * y⁻¹)⁻¹
      = y * (a * b * a⁻¹ * b⁻¹) * y⁻¹ := by group
    _ = y * z * y⁻¹ := by rw [hcomm_z]
    _ = s := hys

theorem Counter.actK_mem_range (w : ↥(mcOf T)) :
    c.actK w ∈ autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) := by
  rw [← c.actK_range]
  exact ⟨w, rfl⟩

theorem Counter.actK_cube_of_mem_oTwoUpper {x : ↥(mcOf T)} (hx : (x : G) ∈ oTwoUpper (mcOf T)) :
    c.actK x ^ 3 = 1 := by
  have hF := c.oddFacts
  have key : ∀ w : G, w ∈ oTwoUpper (mcOf T) →
      ∃ hwH : w ∈ mcOf T, (c.actK ⟨w, hwH⟩) ^ 3 = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      refine ⟨hw.1, hF.cube_of_odd _ (c.actK_mem_range _) ?_⟩
      have hodd : Odd (orderOf (⟨w, hw.1⟩ : ↥(mcOf T))) := by
        rw [← Subgroup.orderOf_coe]; exact hw.2
      exact Odd.of_dvd_nat hodd (orderOf_map_dvd _ _)
    | one =>
      refine ⟨(mcOf T).one_mem, ?_⟩
      have e : (⟨1, (mcOf T).one_mem⟩ : ↥(mcOf T)) = 1 := rfl
      rw [e, map_one, one_pow]
    | mul a b _ _ ha hb =>
      obtain ⟨haH, ha3⟩ := ha
      obtain ⟨hbH, hb3⟩ := hb
      refine ⟨(mcOf T).mul_mem haH hbH, ?_⟩
      have e : (⟨a * b, (mcOf T).mul_mem haH hbH⟩ : ↥(mcOf T)) = ⟨a, haH⟩ * ⟨b, hbH⟩ := rfl
      rw [e, map_mul]
      exact hF.cube_mul _ (c.actK_mem_range _) _ (c.actK_mem_range _) ha3 hb3
    | inv a _ ha =>
      obtain ⟨haH, ha3⟩ := ha
      refine ⟨(mcOf T).inv_mem haH, ?_⟩
      have e : (⟨a⁻¹, (mcOf T).inv_mem haH⟩ : ↥(mcOf T)) = ⟨a, haH⟩⁻¹ := rfl
      rw [e, map_inv, inv_pow, ha3, inv_one]
  obtain ⟨hxH, hx3⟩ := key _ hx
  exact hx3

theorem Counter.mem_qOf_of_mem_T_oTwoUpper {k : G} (hkT : k ∈ T) (hk : k ∈ oTwoUpper (mcOf T)) :
    k ∈ qOf T := by
  have hkH : k ∈ mcOf T := oTwoUpper_le _ hk
  let k' : ↥(mcOf T) := ⟨k, hkH⟩
  have h3 : c.actK k' ^ 3 = 1 := c.actK_cube_of_mem_oTwoUpper (x := k') hk
  have hT2 : IsPGroup 2 ↥T := c.hyp.sylow.1
  obtain ⟨n, hn⟩ := hT2 ⟨k, hkT⟩
  have hk2 : k ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have h2 : c.actK k' ^ (2 ^ n) = 1 := by
    rw [← map_pow]
    have : k' ^ (2 ^ n) = 1 := Subtype.ext (by simpa using hk2)
    rw [this, map_one]
  have h1 : c.actK k' = 1 := by
    have h4 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    have hcop : Nat.gcd (2 ^ n) 3 = 1 := Nat.Coprime.pow_left n (by norm_num)
    rwa [hcop, pow_one] at h4
  exact c.mem_qOf_of_actK_eq_one h1

theorem Counter.not_mem_rq_sup_oTwoUpper {s : G} (hsT : s ∈ T) (hsRQ : s ∉ rOf T M ⊔ qOf T) :
    s ∉ (rOf T M ⊔ qOf T) ⊔ oTwoUpper (mcOf T) := by
  intro hs
  have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp c.h1281
  have hTH : T ≤ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H
  have hKN : rOf T M ⊔ qOf T ≤ Subgroup.normalizer (oTwoUpper (mcOf T) : Set G) := fun x hx =>
    normalizer_le_normalizer_oTwoUpper (mcOf T) (Subgroup.le_normalizer (hTH (hRQT hx)))
  rw [sup_comm] at hs
  obtain ⟨κ, hκ, ρ, hρ, hsκρ⟩ := (CFSG.QuasithinUnique.Lin2.mem_sup_iff_of_le_normalizer hKN).1 hs
  have hκT : κ ∈ T := by
    have : κ = s * ρ⁻¹ := by rw [hsκρ]; group
    rw [this]
    exact T.mul_mem hsT (T.inv_mem (hRQT hρ))
  have hκQ := c.mem_qOf_of_mem_T_oTwoUpper hκT hκ
  apply hsRQ
  rw [hsκρ]
  exact (rOf T M ⊔ qOf T).mul_mem ((le_sup_right : qOf T ≤ rOf T M ⊔ qOf T) hκQ) hρ

theorem Counter.commutator_mem_rq_sup_oTwoUpper (hidx : (rOf T M ⊔ qOf T).relIndex T = 2) {a b : G}
    (ha : a ∈ mcOf T) (hb : b ∈ mcOf T) :
    a * b * a⁻¹ * b⁻¹ ∈ (rOf T M ⊔ qOf T) ⊔ oTwoUpper (mcOf T) := by
  set K := oTwoUpper (mcOf T) with hK
  set N₀ := (rOf T M ⊔ qOf T) ⊔ K with hN₀
  have hTH : T ≤ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H
  have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_le_of_sylow c.hyp.sylow hTH
  have hHeq : T ⊔ K = mcOf T := by
    have := sup_twoResidual_eq hTsyl
    rwa [F6.twoResidual_eq_oTwoUpper] at this
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    normalizer_le_normalizer_oTwoUpper (mcOf T) (Subgroup.le_normalizer (hTH hx))
  have hdecomp : ∀ w ∈ mcOf T, ∃ k ∈ K, ∃ x ∈ T, w = k * x := by
    intro w hw
    rw [← hHeq, sup_comm] at hw
    exact (CFSG.QuasithinUnique.Lin2.mem_sup_iff_of_le_normalizer hTN).1 hw
  have hKconj : ∀ w ∈ mcOf T, ∀ k ∈ K, w * k * w⁻¹ ∈ K := fun w hw k hk =>
    conj_mem_oTwoUpper (Subgroup.le_normalizer hw) hk
  obtain ⟨k₁, hk₁, x₁, hx₁, rfl⟩ := hdecomp a ha
  obtain ⟨k₂, hk₂, x₂, hx₂, rfl⟩ := hdecomp b hb
  have hκ₁ : x₁ * k₂ * x₁⁻¹ ∈ K := hKconj x₁ (hTH hx₁) k₂ hk₂
  have hκ₂ : x₂ * k₁ * x₂⁻¹ ∈ K := hKconj x₂ (hTH hx₂) k₁ hk₁
  have hc : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ rOf T M ⊔ qOf T :=
    commutator_mem_of_relIndex_two hidx hx₁ hx₂
  have e : k₁ * x₁ * (k₂ * x₂) * (k₁ * x₁)⁻¹ * (k₂ * x₂)⁻¹ =
      (k₁ * (x₁ * k₂ * x₁⁻¹)) * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) *
        ((x₂ * k₁ * x₂⁻¹)⁻¹ * k₂⁻¹) := by group
  rw [e]
  exact N₀.mul_mem (N₀.mul_mem ((le_sup_right : K ≤ N₀) (K.mul_mem hk₁ hκ₁))
    ((le_sup_left : rOf T M ⊔ qOf T ≤ N₀) hc))
    ((le_sup_right : K ≤ N₀) (K.mul_mem (K.inv_mem hκ₂) (K.inv_mem hk₂)))

theorem Counter.not_commutator_of_not_mem_rq (hidx : (rOf T M ⊔ qOf T).relIndex T = 2) {s : G}
    (hsT : s ∈ T) (hsRQ : s ∉ rOf T M ⊔ qOf T) :
    ∀ a ∈ mcOf T, ∀ b ∈ mcOf T, a * b * a⁻¹ * b⁻¹ ≠ s := by
  intro a ha b hb he
  exact c.not_mem_rq_sup_oTwoUpper hsT hsRQ (he ▸ c.commutator_mem_rq_sup_oTwoUpper hidx ha hb)

end Final

end S143

end CFSG.Quasithin
