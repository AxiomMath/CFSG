module

public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin.RonanD33 Subgroup

section Beta

variable {G : Type} [Group G] [Finite G]

theorem no_index_three {H K O : Subgroup G} (hKH : K ≤ H) (hidx : K.relIndex H = 3)
    (hOK : O ≤ K) (hOn : ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O) (hO2 : IsPGroup 2 ↥O)
    (hcard : 4 * Nat.card ↥(pCoreOf 2 H) ≤ Nat.card ↥O) : False := by
  classical
  let X := ↥H ⧸ K.subgroupOf H
  have hX3 : Nat.card X = 3 := by
    have : K.relIndex H = Nat.card X := Subgroup.index_eq_card _
    omega
  let φ : ↥H →* Equiv.Perm X := MulAction.toPermHom ↥H X
  let N : Subgroup ↥H := φ.ker
  have hNn : N.Normal := φ.normal_ker
  let N₀ : Subgroup G := N.map H.subtype
  have hN₀H : N₀ ≤ H := Subgroup.map_subtype_le N
  have hN₀card : Nat.card ↥N₀ = Nat.card ↥N := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
  have hN₀K : N₀ ≤ K := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 : φ g = 1 := hg
    have h2 : g • ((1 : ↥H) : X) = ((1 : ↥H) : X) := by
      have h1' := congrArg (fun p : Equiv.Perm X => p ((1 : ↥H) : X)) h1
      exact h1'
    have h3 : ((g * 1 : ↥H) : X) = ((1 : ↥H) : X) := h2
    have h4 := QuotientGroup.eq.mp h3
    rw [mul_one, Subgroup.mem_subgroupOf] at h4
    have h5 := K.inv_mem h4
    simpa using h5
  have hN₀sub : N₀.subgroupOf H = N := by
    show (N.map H.subtype).comap H.subtype = N
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  have hN₀n : (N₀.subgroupOf H).Normal := by rw [hN₀sub]; exact hNn
  have hsub : IsSubnormal N₀ H := IsSubnormal.step hN₀H hN₀n (IsSubnormal.refl H)
  have hpc : pCoreOf 2 N₀ ≤ pCoreOf 2 H := pCoreOf_le_of_isSubnormal hsub
  have hcardH : Nat.card ↥K * 3 = Nat.card ↥H := by
    have := Subgroup.relIndex_mul_card (H := K) (K := H)
    rw [hidx, inf_eq_left.mpr hKH] at this
    linarith
  have hkerr : Nat.card ↥N * Nat.card ↥φ.range = Nat.card ↥H :=
    Subgroup.card_ker_mul_card_range φ
  have hr6 : Nat.card ↥φ.range ∣ 6 := by
    have h1 : Nat.card ↥φ.range ∣ Nat.card (Equiv.Perm X) := Subgroup.card_subgroup_dvd_card _
    have h6 : Nat.card (Equiv.Perm X) = 6 := by rw [Nat.card_perm, hX3]; rfl
    rwa [h6] at h1
  obtain ⟨k, hk⟩ : Nat.card ↥N ∣ Nat.card ↥K := by
    rw [← hN₀card]
    exact Subgroup.card_dvd_of_le hN₀K
  have hNpos : 0 < Nat.card ↥N := Nat.card_pos
  have hr : Nat.card ↥φ.range = 3 * k := by
    have h1 : Nat.card ↥N * (3 * k) = Nat.card ↥N * Nat.card ↥φ.range := by
      rw [hkerr, ← hcardH, hk]; ring
    exact (Nat.eq_of_mul_eq_mul_left hNpos h1).symm
  have hk2 : k ≤ 2 := by
    have : 3 * k ∣ 6 := hr ▸ hr6
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hrelK : N₀.relIndex K = k := by
    have h1 := Subgroup.relIndex_mul_card (H := N₀) (K := K)
    rw [inf_eq_left.mpr hN₀K, hN₀card] at h1
    rw [hk] at h1
    exact Nat.eq_of_mul_eq_mul_right hNpos (by rw [h1]; ring)
  have hrelO : N₀.relIndex O ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := N₀) hOK (by
      unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite)
    omega
  have hY1 : (N₀ ⊓ O) ≤ N₀ := inf_le_left
  have hYn : N₀ ≤ Subgroup.normalizer ((N₀ ⊓ O : Subgroup G) : Set G) :=
    le_normalizer_of_forall_conj_mem fun s hs y hy => by
      refine Subgroup.mem_inf.mpr ⟨N₀.mul_mem (N₀.mul_mem hs (Subgroup.mem_inf.mp hy).1)
        (N₀.inv_mem hs), hOn s (hN₀K hs) y (Subgroup.mem_inf.mp hy).2⟩
  have hYp : IsPGroup 2 ↥(N₀ ⊓ O) := hO2.to_le inf_le_right
  have hY0 : N₀ ⊓ O ≤ pCoreOf 2 N₀ := le_pCoreOf_of_le_normalizer hY1 hYn hYp
  have hYQ : N₀ ⊓ O ≤ pCoreOf 2 H := hY0.trans hpc
  have hcardY : Nat.card ↥(N₀ ⊓ O) ≤ Nat.card ↥(pCoreOf 2 H) := Subgroup.card_le_of_le hYQ
  have hOcard : N₀.relIndex O * Nat.card ↥(N₀ ⊓ O) = Nat.card ↥O :=
    Subgroup.relIndex_mul_card (H := N₀) (K := O)
  have hQpos : 0 < Nat.card ↥(pCoreOf 2 H) := Nat.card_pos
  have : Nat.card ↥O ≤ 2 * Nat.card ↥(N₀ ⊓ O) := by
    rw [← hOcard]
    exact Nat.mul_le_mul_right _ hrelO
  omega

end Beta

section Burnside

variable {G : Type} [Group G] [Finite G]

open CFSG.OrderReductions.FrattiniAutomorphisms in
theorem mem_of_trivial_action {H Q N : Subgroup G}
    (hQmax : ∀ X : Subgroup G, X ≤ H → (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → IsPGroup 2 ↥X →
      X ≤ Q)
    (hQH : Q ≤ H) (hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q) (hQ2 : IsPGroup 2 ↥Q)
    (hC : ∀ h ∈ H, (∀ x ∈ Q, h * x = x * h) → h ∈ Q)
    (hNQ : N ≤ Q) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hNfr : ∀ n (hn : n ∈ N), (⟨n, hNQ hn⟩ : ↥Q) ∈ frattini ↥Q)
    {h : G} (hh : h ∈ H) (htriv : ∀ x ∈ Q, h * x * h⁻¹ * x⁻¹ ∈ N) : h ∈ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G :=
    { carrier := {g | g ∈ H ∧ ∀ x ∈ Q, g * x * g⁻¹ * x⁻¹ ∈ N}
      one_mem' := ⟨H.one_mem, fun x _ => by simpa using N.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
        refine ⟨H.mul_mem haH hbH, fun x hx => ?_⟩
        have h1 := hNn a haH _ (hb x hx)
        have h2 := ha x hx
        have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
            (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
        rw [e]
        exact N.mul_mem h1 h2
      inv_mem' := by
        rintro a ⟨haH, ha⟩
        refine ⟨H.inv_mem haH, fun x hx => ?_⟩
        have hx' : a⁻¹ * x * a ∈ Q := by
          have := hQn a⁻¹ (H.inv_mem haH) x hx
          simpa using this
        have h1 := ha _ hx'
        have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = (a * (a⁻¹ * x * a) * a⁻¹ * (a⁻¹ * x * a)⁻¹)⁻¹ := by group
        rw [e]
        exact N.inv_mem h1 }
  have hXH : X ≤ H := fun g hg => hg.1
  have hXn : ∀ a ∈ H, ∀ g ∈ X, a * g * a⁻¹ ∈ X := by
    rintro a haH g ⟨hgH, hg⟩
    refine ⟨H.mul_mem (H.mul_mem haH hgH) (H.inv_mem haH), fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a ∈ Q := by
      have := hQn a⁻¹ (H.inv_mem haH) x hx
      simpa using this
    have h1 := hNn a haH _ (hg _ hx')
    have e : a * g * a⁻¹ * x * (a * g * a⁻¹)⁻¹ * x⁻¹ =
        a * (g * (a⁻¹ * x * a) * g⁻¹ * (a⁻¹ * x * a)⁻¹) * a⁻¹ := by group
    rw [e]
    exact h1
  have hX2 : IsPGroup 2 ↥X := by
    rintro ⟨g, hgX⟩
    obtain ⟨hgH, hgtriv⟩ := hgX
    have hgN : g ∈ Subgroup.normalizer (Q : Set G) :=
      Subgroup.mem_normalizer_fintype fun n hn => hQn g hgH n hn
    set σ : MulAut ↥Q := Q.normalizerMonoidHom ⟨g, hgN⟩ with hσ
    have hσx : ∀ x : ↥Q, ((σ x : ↥Q) : G) = g * x * g⁻¹ := fun x => rfl
    have hker : σ ∈ (quotientAutomorphism (frattini ↥Q)).ker := by
      rw [mem_quotientAutomorphism_kernel]
      intro x
      refine QuotientGroup.eq.mpr ?_
      have hx1 : (x : G)⁻¹ ∈ Q := Q.inv_mem x.2
      have hn := hgtriv _ hx1
      have h1 := hNfr _ hn
      have e : (σ x)⁻¹ * x = (⟨g * (x : G)⁻¹ * g⁻¹ * ((x : G)⁻¹)⁻¹, hNQ hn⟩ : ↥Q) :=
        Subtype.ext (by simp [hσx]; group)
      rw [e]
      exact h1
    obtain ⟨k, hk⟩ := frattini_automorphism_kernel_isPGroup 2 hQ2
      (⟨σ, hker⟩ : ↥(quotientAutomorphism (frattini ↥Q)).ker)
    have hk' : σ ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcomm : ∀ x ∈ Q, g ^ 2 ^ k * x = x * g ^ 2 ^ k := by
      intro x hx
      have h1 := congrArg (fun a : MulAut ↥Q => ((a ⟨x, hx⟩ : ↥Q) : G)) hk'
      have e : (σ ^ 2 ^ k) = Q.normalizerMonoidHom ((⟨g, hgN⟩ : Subgroup.normalizer (Q : Set G)) ^ 2 ^ k) := by
        rw [hσ, map_pow]
      simp only [e, MulAut.one_apply] at h1
      have h2 : (g ^ 2 ^ k) * x * (g ^ 2 ^ k)⁻¹ = x := h1
      calc g ^ 2 ^ k * x = (g ^ 2 ^ k * x * (g ^ 2 ^ k)⁻¹) * g ^ 2 ^ k := by group
        _ = x * g ^ 2 ^ k := by rw [h2]
    have hgQ : g ^ 2 ^ k ∈ Q := hC _ (H.pow_mem hgH _) hcomm
    obtain ⟨m, hm⟩ := hQ2 ⟨g ^ 2 ^ k, hgQ⟩
    have hm' : (g ^ 2 ^ k) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    refine ⟨k + m, Subtype.ext ?_⟩
    show g ^ 2 ^ (k + m) = 1
    rw [pow_add, pow_mul, hm']
  have hXQ : X ≤ Q := hQmax X hXH hXn hX2
  exact hXQ ⟨hh, htriv⟩

end Burnside

end CFSG.Quasithin.H13.I1277

end
