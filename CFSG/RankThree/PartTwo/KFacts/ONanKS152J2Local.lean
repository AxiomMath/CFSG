module

public import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2Sylow
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS152J2

open Subgroup CFSG.RankThree.PartTwo

theorem card_of_j2 {G : Type} [Group G]
    (hG : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2)) : Nat.card G = 604800 := by
  obtain ⟨e⟩ := hG
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.J2.card_J2

theorem four15_center
    {G : Type} [Group G] [Finite G]
    (hG : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2)) (S : Sylow 3 G) :
    Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) : Subgroup G) = 3 ∧
      Nat.card (Subgroup.centralizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) : Subgroup G) :
          Set G)) = 1080 := by
  have h415 := Sec4.Sporadic.rank3II_4_15 G hG S _ rfl _ rfl
  obtain ⟨⟨hHeis, -⟩, -, ⟨-, hExt, -⟩, -, -⟩ := h415
  refine ⟨?_, ?_⟩
  · rw [Sec4.Sporadic.inf_centralizer_eq_map_center,
      Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective]
    exact hHeis.1.2.2.2
  · obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := hExt
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [Nat.card_congr eK.toEquiv, Nat.card_congr eQ.toEquiv] at h1
    have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [h3, h360] at h1
    omega

theorem zpowers_eq_of_card_three {G : Type*} [Group G] [Finite G] {Z : Subgroup G}
    (hZ : Nat.card Z = 3) {z : G} (hz : z ∈ Z) (hne : z ≠ 1) : zpowers z = Z := by
  have hle : zpowers z ≤ Z := Subgroup.zpowers_le.mpr hz
  have hdvd : orderOf z ∣ 3 := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : Z)
    rwa [Subgroup.orderOf_mk, hZ] at this
  have h3 : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, h3, hZ])

theorem centralizer_singleton_eq_zpowers {G : Type*} [Group G] (z : G) :
    Subgroup.centralizer ({z} : Set G) =
      Subgroup.centralizer ((zpowers z : Subgroup G) : Set G) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, SetLike.mem_coe]
  constructor
  · intro h w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (show Commute z x from h) k).eq)
  · intro h
    exact h z (Subgroup.mem_zpowers z)

theorem gen_of_core
    {G : Type} [Group G] [Finite G]
    (hG : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2)) (T : Sylow 2 G) (W : Subgroup G)
    (hW : W ≤ Subgroup.closure ((fun x : G => x ^ 2) '' ((T : Subgroup G) : Set G)))
    (S₀ : Sylow 3 G) {z₀ : G} (hz₀ : z₀ ≠ 1) (hz₀S : z₀ ∈ (S₀ : Subgroup G))
    (hS₀ : (S₀ : Subgroup G) ≤ Subgroup.centralizer ({z₀} : Set G))
    {y₀ : G} (hy₀ : orderOf y₀ = 5) (hy₀z : z₀ * y₀ = y₀ * z₀)
    (hcore : ∀ g : G, W ⊔ Subgroup.zpowers (g * y₀ * g⁻¹) = ⊤)
    {y z : G} (S : Sylow 3 G) {Q : Subgroup G} (hy : orderOf y = 5) (hz : z ≠ 1)
    (hzS : z ∈ (S : Subgroup G)) (hS : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    (hyz : z * y = y * z) (hQ : IsPGroup 2 Q) (h64 : 64 ∣ Nat.card Q) :
    Q ⊔ Subgroup.zpowers y = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hGcard : Nat.card G = 604800 := card_of_j2 hG
  have hfac2 : (604800 : ℕ).factorization 2 = 7 := by
    rw [show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp
  have hTcard : Nat.card (T : Subgroup G) = 128 := by
    rw [Sylow.card_eq_multiplicity T, hGcard, hfac2]
    norm_num
  have hQcard : 64 ≤ Nat.card Q := Nat.le_of_dvd Nat.card_pos h64
  obtain ⟨g₁, hg₁⟩ := exists_conj_sq_mem T hQ (by omega)
  have hW₁ : W.map (MulAut.conj g₁).toMonoidHom ≤ Q := by
    refine (Subgroup.map_mono hW).trans ?_
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply] using hg₁ x hx
  obtain ⟨hZ3, -⟩ := four15_center hG S
  obtain ⟨hZ3₀, hK⟩ := four15_center hG S₀
  have hzZ : z ∈ ((S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) :
      Subgroup G) :=
    ⟨hzS, Subgroup.mem_centralizer_iff.mpr fun s hs => by
      have := Subgroup.mem_centralizer_iff.mp (hS hs) z rfl
      exact this.symm⟩
  have hz₀Z : z₀ ∈ ((S₀ : Subgroup G) ⊓ Subgroup.centralizer ((S₀ : Subgroup G) : Set G) :
      Subgroup G) :=
    ⟨hz₀S, Subgroup.mem_centralizer_iff.mpr fun s hs => by
      have := Subgroup.mem_centralizer_iff.mp (hS₀ hs) z₀ rfl
      exact this.symm⟩
  have hZeq := zpowers_eq_of_card_three hZ3 hzZ hz
  have hZ₀eq := zpowers_eq_of_card_three hZ3₀ hz₀Z hz₀
  rw [← hZ₀eq] at hK
  have hKcard : Nat.card (Subgroup.centralizer ({z₀} : Set G)) = 1080 := by
    rw [centralizer_singleton_eq_zpowers]
    exact hK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S
  have hgS : ∀ s₀ ∈ (S₀ : Subgroup G), g * s₀ * g⁻¹ ∈ (S : Subgroup G) := by
    intro s₀ hs₀
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨s₀, hs₀, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  have hgS' : ∀ s ∈ (S : Subgroup G), ∃ s₀ ∈ (S₀ : Subgroup G), g * s₀ * g⁻¹ = s := by
    intro s hs
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hs
    obtain ⟨s₀, hs₀, hse⟩ := hs
    exact ⟨s₀, hs₀, by simpa [MulAut.smul_def, MulAut.conj_apply] using hse⟩
  have hz₀' : g * z₀ * g⁻¹ ∈ Subgroup.zpowers z := by
    rw [hZeq]
    refine ⟨hgS z₀ hz₀S, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    obtain ⟨s₀, hs₀, rfl⟩ := hgS' s hs
    have := Subgroup.mem_centralizer_iff.mp (hS₀ hs₀) z₀ rfl
    calc g * s₀ * g⁻¹ * (g * z₀ * g⁻¹) = g * (s₀ * z₀) * g⁻¹ := by group
      _ = g * (z₀ * s₀) * g⁻¹ := by rw [this.symm]
      _ = g * z₀ * g⁻¹ * (g * s₀ * g⁻¹) := by group
  have hy'z : z₀ * (g⁻¹ * y * g) = (g⁻¹ * y * g) * z₀ := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz₀'
    have hc : (g * z₀ * g⁻¹) * y = y * (g * z₀ * g⁻¹) := by
      rw [← hj]
      exact (Commute.zpow_left (show Commute z y from hyz) j).eq
    calc z₀ * (g⁻¹ * y * g) = g⁻¹ * ((g * z₀ * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * z₀ * g⁻¹)) * g := by rw [hc]
      _ = (g⁻¹ * y * g) * z₀ := by group
  have hy'K : g⁻¹ * y * g ∈ Subgroup.centralizer ({z₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hy'z.symm
  have hy₀K : y₀ ∈ Subgroup.centralizer ({z₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hy₀z.symm
  have hoy' : orderOf (g⁻¹ * y * g) = 5 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y
    rw [← hy, ← this]
    simp
  obtain ⟨k, hkK, hk⟩ := exists_conj_zpowers_eq (K := Subgroup.centralizer ({z₀} : Set G))
    (p := 5) (by rw [hKcard]; norm_num) hy₀K hy'K hy₀ hoy'
  set h : G := g * k with hh
  have hyc : Subgroup.zpowers y = Subgroup.zpowers (h * y₀ * h⁻¹) := by
    have hyle : y ∈ Subgroup.zpowers (h * y₀ * h⁻¹) := by
      have hy'mem : g⁻¹ * y * g ∈ Subgroup.zpowers (k * y₀ * k⁻¹) := by
        rw [← hk]
        exact Subgroup.mem_zpowers _
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy'mem
      refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
      have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      rw [e, ← hj]
      have : h * y₀ * h⁻¹ = g * (k * y₀ * k⁻¹) * g⁻¹ := by rw [hh]; group
      rw [this, conj_zpow]
    have hord : orderOf (h * y₀ * h⁻¹) = 5 := by
      have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective y₀
      rw [← hy₀, ← this]
      rfl
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyle) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hy]
  have hcore' := hcore (g₁⁻¹ * h)
  have hconj : g₁ * ((g₁⁻¹ * h) * y₀ * (g₁⁻¹ * h)⁻¹) * g₁⁻¹ = h * y₀ * h⁻¹ := by group
  have hmap : (W ⊔ Subgroup.zpowers ((g₁⁻¹ * h) * y₀ * (g₁⁻¹ * h)⁻¹)).map
      (MulAut.conj g₁).toMonoidHom ≤ Q ⊔ Subgroup.zpowers y := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    apply sup_le_sup hW₁
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hconj, hyc]
  rw [hcore'] at hmap
  have htop : (⊤ : Subgroup G).map (MulAut.conj g₁).toMonoidHom = ⊤ := by
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj g₁).surjective
  rw [htop] at hmap
  exact top_le_iff.mp hmap

end CFSG.RankThree.PartTwo.KFacts.KS152J2
