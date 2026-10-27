module

public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace SzF53B2

section ModPart

theorem card_eq_sq_of_inversion {Y : Type*} [CommGroup Y] [Finite Y] (hY : ∀ y : Y, y * y = 1)
    (σ τ : MulAut Y) (hσ : σ ^ 3 = 1) (hτ : τ ^ 2 = 1) (hστ : τ * σ * τ⁻¹ = σ⁻¹)
    (hfix : ∀ y : Y, σ y = y → y = 1) :
    Nat.card Y = Nat.card {y : Y // τ y = y} ^ 2 := by
  have hτ2 : ∀ y : Y, τ (τ y) = y := by
    intro y
    have := congrArg (fun f : MulAut Y => f y) hτ
    simpa [pow_two] using this
  have hσ3 : ∀ y : Y, σ (σ (σ y)) = y := by
    intro y
    have := congrArg (fun f : MulAut Y => f y) hσ
    simpa [pow_succ] using this
  have hτσ : ∀ y : Y, τ (σ y) = σ (σ (τ y)) := by
    intro y
    have h1 : τ * σ = σ⁻¹ * τ := by
      have := congrArg (fun f : MulAut Y => f * τ) hστ
      simpa [mul_assoc] using this
    have h2 : σ⁻¹ = σ * σ := by
      have : σ * σ * σ = 1 := by simpa [pow_succ] using hσ
      exact (eq_inv_of_mul_eq_one_right (by simpa [mul_assoc] using this)).symm
    have h3 := congrArg (fun f : MulAut Y => f y) h1
    simp only [MulAut.mul_apply] at h3
    rw [h3, h2]
    rfl
  have hid : ∀ c : Y, c * σ c * σ (σ c) = 1 := by
    intro c
    apply hfix
    have : σ (c * σ c * σ (σ c)) = σ c * σ (σ c) * σ (σ (σ c)) := by simp [map_mul]
    rw [this, hσ3]
    ac_rfl
  let φ : Y →* Y :=
    { toFun := fun v => v * τ v
      map_one' := by simp
      map_mul' := fun v w => by simp only [map_mul]; exact mul_mul_mul_comm _ _ _ _ }
  have hker' : ∀ v : Y, v ∈ φ.ker ↔ τ v = v := by
    intro v
    simp only [MonoidHom.mem_ker, φ, MonoidHom.coe_mk, OneHom.coe_mk]
    constructor
    · intro h
      have : τ v = v⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact (eq_inv_of_mul_eq_one_left (hY v)).symm
    · intro h
      rw [h]; exact hY v
  have hrange : ∀ c : Y, c ∈ φ.range ↔ τ c = c := by
    intro c
    constructor
    · rintro ⟨v, rfl⟩
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, hτ2]
      exact mul_comm _ _
    · intro hc
      refine ⟨σ c, ?_⟩
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [hτσ, hc]
      have := hid c
      have h2 : σ c * σ (σ c) = c⁻¹ := by
        have : c * (σ c * σ (σ c)) = 1 := by rw [← mul_assoc]; exact this
        exact eq_inv_of_mul_eq_one_right this
      rw [h2]
      exact (eq_inv_of_mul_eq_one_left (hY c)).symm
  have hcard1 : Nat.card φ.range = Nat.card {y : Y // τ y = y} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun c => hrange c)
  have hcard2 : Nat.card φ.ker = Nat.card {y : Y // τ y = y} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun c => hker' c)
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hcard1, hcard2] at this
  rw [this, pow_two]

theorem card_eq_sq_of_perm3_action {Y : Type*} [Group Y] [Finite Y]
    (hcomm : ∀ a b : Y, a * b = b * a) (hY : ∀ y : Y, y * y = 1)
    (ρ : Equiv.Perm (Fin 3) →* MulAut Y) (hfix : ∀ y : Y, (∀ g, ρ g y = y) → y = 1)
    (τ : Equiv.Perm (Fin 3)) (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) :
    Nat.card Y = Nat.card {y : Y // ρ τ y = y} ^ 2 := by
  let : CommGroup Y := { ‹Group Y› with mul_comm := hcomm }
  obtain ⟨c, hc⟩ : ∃ c : Equiv.Perm (Fin 3), c = Equiv.swap 0 1 * Equiv.swap 1 2 := ⟨_, rfl⟩
  have hc3 : c ^ 3 = 1 := by rw [hc]; decide
  have hcτ : ∀ τ' : Equiv.Perm (Fin 3), τ' ≠ 1 → τ' * τ' = 1 → τ' * c * τ'⁻¹ = c⁻¹ := by
    rw [hc]; decide
  have hwords : ∀ τ' : Equiv.Perm (Fin 3), τ' ≠ 1 → τ' * τ' = 1 →
      ∀ g : Equiv.Perm (Fin 3),
        g = 1 ∨ g = c ∨ g = c * c ∨ g = τ' ∨ g = c * τ' ∨ g = c * c * τ' := by
    rw [hc]; decide
  have hτ2' : τ ^ 2 = 1 := by rw [pow_two]; exact hτ2
  have hfixed : ∀ y : Y, ρ c y = y → ρ τ y = y → y = 1 := by
    intro y hy1 hy2
    apply hfix
    intro g
    rcases hwords τ hτ1 hτ2 g with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · exact hy1
    · simp [hy1]
    · exact hy2
    · simp [hy1, hy2]
    · simp [hy1, hy2]
  have hcτ' : ∀ τ' : Equiv.Perm (Fin 3), τ' ≠ 1 → τ' * τ' = 1 → c * τ' = τ' * c⁻¹ := by
    rw [hc]; decide
  have hσfix : ∀ y : Y, ρ c y = y → y = 1 := by
    intro y₀ hy₀
    have hy₀' : ρ c⁻¹ y₀ = y₀ := by
      have : ρ c⁻¹ (ρ c y₀) = y₀ := by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
      rwa [hy₀] at this
    have hτσ : ρ c (ρ τ y₀) = ρ τ y₀ := by
      have h1 : ρ c (ρ τ y₀) = ρ (c * τ) y₀ := by rw [map_mul]; rfl
      rw [h1, hcτ' τ hτ1 hτ2, map_mul]
      show ρ τ (ρ c⁻¹ y₀) = ρ τ y₀
      rw [hy₀']
    have hττ : ρ τ (ρ τ y₀) = y₀ := by
      rw [← MulAut.mul_apply, ← map_mul, hτ2, map_one]; rfl
    have hy : y₀ * ρ τ y₀ = 1 := by
      apply hfixed
      · rw [map_mul, hy₀, hτσ]
      · rw [map_mul, hττ, hcomm]
    have hτy₀ : ρ τ y₀ = y₀ := by
      have h1 : ρ τ y₀ = y₀⁻¹ := eq_inv_of_mul_eq_one_right hy
      rw [h1]
      exact (eq_inv_of_mul_eq_one_left (hY y₀)).symm
    exact hfixed y₀ hy₀ hτy₀
  exact card_eq_sq_of_inversion (fun y => hY y) (ρ c) (ρ τ) (by rw [← map_pow, hc3, map_one])
    (by rw [← map_pow, hτ2', map_one])
    (by rw [← map_mul, ← map_inv, ← map_mul, hcτ τ hτ1 hτ2, map_inv]) hσfix

section Concrete

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_two_cases {Q S : Subgroup G} (h : Q.relIndex S = 2) :
    ∃ s ∈ S, s ∉ Q ∧ s * s ∈ Q ∧ ∀ u ∈ S, u ∈ Q ∨ u * s ∈ Q := by
  have h2 : (Q.subgroupOf S).index = 2 := h
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp h2
  have h1 : (1 : ↥S) ∈ Q.subgroupOf S := Subgroup.one_mem _
  have hanot : a ∉ Q.subgroupOf S := by
    rcases ha 1 with ⟨_, hy⟩ | ⟨_, hy⟩
    · exact absurd h1 hy
    · simpa using hy
  refine ⟨(a : G), a.2, fun hq => hanot hq, ?_, ?_⟩
  · rcases ha a with ⟨h1', _⟩ | ⟨h1', _⟩
    · exact h1'
    · exact absurd h1' hanot
  · intro u hu
    rcases ha ⟨u, hu⟩ with ⟨h1', _⟩ | ⟨h1', _⟩
    · right; exact h1'
    · left; exact h1'

theorem card_eq_sq_centralizer {M S Y : Subgroup G} (hY : IsElemAbelian 2 Y)
    (hYQ : Y ≤ pCoreOf 2 M) (hMY : M ≤ Subgroup.normalizer (Y : Set G))
    (hQ : pCoreOf 2 M ≤ Subgroup.centralizer (Y : Set G))
    (hperm : Nonempty (OTwoQuot M ≃* Equiv.Perm (Fin 3)))
    (hSM : S ≤ M) (hQS : (pCoreOf 2 M).relIndex S = 2)
    (hfix : Y ⊓ Subgroup.centralizer (M : Set G) = ⊥) :
    Nat.card Y = Nat.card ↥(Y ⊓ Subgroup.centralizer (S : Set G)) ^ 2 := by
  obtain ⟨e⟩ := hperm
  have hYM : Y ≤ M := hYQ.trans (pCoreOf_le 2 M)
  have hnorm : (Y.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hMY
  let φ : ↥M →* MulAut ↥(Y.subgroupOf M) := MulAut.conjNormal
  have hφ : ∀ (m : ↥M) (y : ↥(Y.subgroupOf M)), (((φ m y : ↥(Y.subgroupOf M)) : ↥M) : G) =
      (m : G) * (((y : ↥M)) : G) * (m : G)⁻¹ := fun m y => by
    simp [φ, MulAut.conjNormal_apply]
  have : (CFSG.Open.pCore 2 ↥M).Normal := inferInstance
  have hker : CFSG.Open.pCore 2 ↥M ≤ φ.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    ext y
    have hqQ : (q : G) ∈ pCoreOf 2 M := ⟨q, hq, rfl⟩
    have hyY : (((y : ↥M)) : G) ∈ Y := y.2
    have hcomm := Subgroup.mem_centralizer_iff.mp (hQ hqQ) _ hyY
    show (((φ q y : ↥(Y.subgroupOf M)) : ↥M) : G) = (((y : ↥M)) : G)
    rw [hφ]
    calc (q : G) * (((y : ↥M)) : G) * (q : G)⁻¹ = ((((y : ↥M)) : G) * q) * (q : G)⁻¹ := by
          rw [← hcomm]
      _ = (((y : ↥M)) : G) := by group
  let ρ : Equiv.Perm (Fin 3) →* MulAut ↥(Y.subgroupOf M) :=
    (QuotientGroup.lift (CFSG.Open.pCore 2 ↥M) φ hker).comp e.symm.toMonoidHom
  have hρ : ∀ m : ↥M, ρ (e (QuotientGroup.mk m)) = φ m := by
    intro m
    simp [ρ]
  obtain ⟨s, hsS, hsQ, hss, hSs⟩ := relIndex_two_cases hQS
  have hsM : s ∈ M := hSM hsS
  have hsQ' : (⟨s, hsM⟩ : ↥M) ∉ CFSG.Open.pCore 2 ↥M := fun hh => hsQ ⟨_, hh, rfl⟩
  have hssQ : (⟨s, hsM⟩ * ⟨s, hsM⟩ : ↥M) ∈ CFSG.Open.pCore 2 ↥M := by
    have : (s * s) ∈ pCoreOf 2 M := hss
    obtain ⟨x, hx, hxe⟩ := this
    have : x = ⟨s, hsM⟩ * ⟨s, hsM⟩ := Subtype.ext hxe
    rwa [this] at hx
  set τ : Equiv.Perm (Fin 3) := e (QuotientGroup.mk ⟨s, hsM⟩) with hτdef
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply hsQ'
    have : (QuotientGroup.mk (⟨s, hsM⟩ : ↥M) : OTwoQuot M) = 1 := by
      apply e.injective
      rw [map_one]
      exact h1
    exact (QuotientGroup.eq_one_iff _).mp this
  have hτ2 : τ * τ = 1 := by
    rw [hτdef, ← map_mul, ← QuotientGroup.mk_mul]
    have : (QuotientGroup.mk (⟨s, hsM⟩ * ⟨s, hsM⟩ : ↥M) : OTwoQuot M) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hssQ
    rw [this, map_one]
  have hfix' : ∀ y : ↥(Y.subgroupOf M), (∀ g, ρ g y = y) → y = 1 := by
    intro y hy
    have hyY : (((y : ↥M)) : G) ∈ Y := y.2
    have hyC : (((y : ↥M)) : G) ∈ Subgroup.centralizer (M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h1 := hy (e (QuotientGroup.mk ⟨m, hm⟩))
      rw [hρ] at h1
      have h2 := congrArg (fun z : ↥(Y.subgroupOf M) => (((z : ↥M)) : G)) h1
      simp only [hφ] at h2
      calc m * (((y : ↥M)) : G) = (m * (((y : ↥M)) : G) * m⁻¹) * m := by group
        _ = (((y : ↥M)) : G) * m := by rw [h2]

    have hmem : (((y : ↥M)) : G) ∈ Y ⊓ Subgroup.centralizer (M : Set G) := ⟨hyY, hyC⟩
    rw [hfix, Subgroup.mem_bot] at hmem
    apply Subtype.ext
    apply Subtype.ext
    simpa using hmem
  have hcomm : ∀ a b : ↥(Y.subgroupOf M), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact F7.isElemAbelian_comm hY a.2 b.2
  have hsq : ∀ y : ↥(Y.subgroupOf M), y * y = 1 := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have := F7.isElemAbelian_pow_eq_one hY y.2
    simpa [pow_two] using this
  have hmain := card_eq_sq_of_perm3_action hcomm hsq ρ hfix' τ hτ1 hτ2
  have hc1 : Nat.card ↥(Y.subgroupOf M) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv
  have hfixed_iff : ∀ y : ↥(Y.subgroupOf M),
      ρ τ y = y ↔ s * (((y : ↥M)) : G) * s⁻¹ = (((y : ↥M)) : G) := by
    intro y
    rw [hτdef, hρ]
    constructor
    · intro h1
      have := congrArg (fun z : ↥(Y.subgroupOf M) => (((z : ↥M)) : G)) h1
      simpa only [hφ] using this
    · intro h1
      apply Subtype.ext
      apply Subtype.ext
      simpa only [hφ] using h1
  have hS_iff : ∀ y : G, y ∈ Y →
      (s * y * s⁻¹ = y ↔ y ∈ Subgroup.centralizer (S : Set G)) := by
    intro y hy
    constructor
    · intro h1
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hsy : s * y = y * s := by
        calc s * y = (s * y * s⁻¹) * s := by group
          _ = y * s := by rw [h1]
      rcases hSs u hu with huQ | huQ
      · exact (Subgroup.mem_centralizer_iff.mp (hQ (show u ∈ pCoreOf 2 M from huQ)) y hy).symm
      · have h3 := Subgroup.mem_centralizer_iff.mp (hQ (show u * s ∈ pCoreOf 2 M from huQ)) y hy
        calc u * y = (u * s) * (s⁻¹ * y) := by group
          _ = (u * s) * (y * s⁻¹) := by
              congr 1
              calc s⁻¹ * y = s⁻¹ * (y * s) * s⁻¹ := by group
                _ = s⁻¹ * (s * y) * s⁻¹ := by rw [hsy]
                _ = y * s⁻¹ := by group
          _ = ((u * s) * y) * s⁻¹ := by group
          _ = (y * (u * s)) * s⁻¹ := by rw [h3]
          _ = y * u := by group
    · intro h1
      have := Subgroup.mem_centralizer_iff.mp h1 s hsS
      calc s * y * s⁻¹ = (y * s) * s⁻¹ := by rw [this]
        _ = y := by group
  let f : {y : ↥(Y.subgroupOf M) // ρ τ y = y} → ↥(Y ⊓ Subgroup.centralizer (S : Set G)) :=
    fun y => ⟨(((y.1 : ↥M)) : G), y.1.2, (hS_iff _ y.1.2).mp ((hfixed_iff y.1).mp y.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h3 := congrArg (fun z : ↥(Y ⊓ Subgroup.centralizer (S : Set G)) => (z : G)) hab
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      simpa [f] using h3
    · intro z
      have hzY : (z : G) ∈ Y := z.2.1
      have hzM : (z : G) ∈ M := hYM hzY
      refine ⟨⟨⟨⟨z, hzM⟩, hzY⟩, ?_⟩, rfl⟩
      rw [hfixed_iff]
      exact (hS_iff _ hzY).mpr z.2.2
  have hc2 : Nat.card {y : ↥(Y.subgroupOf M) // ρ τ y = y} =
      Nat.card ↥(Y ⊓ Subgroup.centralizer (S : Set G)) :=
    Nat.card_congr (Equiv.ofBijective f hf)
  rw [← hc1, hmain, hc2]

end Concrete

end ModPart

end SzF53B2

end CFSG.Quasithin
