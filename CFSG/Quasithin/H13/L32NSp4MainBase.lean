
module

public import CFSG.Quasithin.H13.L32NSp4S6
public import CFSG.Quasithin.H13.L32NSp4S120
public import CFSG.Quasithin.H13.L32NSp4S36

@[expose] public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable {b : Module.Basis (Fin 4) (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {s : Node}

omit [Finite V] in
theorem sub_els_of_inD (h : IsNodeOf b Γ s) {l : List (List ℕ)}
    (hl : ∀ x ∈ l, InD (Γ.map (phi4 b)) x) : ∀ x ∈ l, x ∈ s.els := by
  intro x hx
  obtain ⟨hxv, g, hg, hgx⟩ := hl x hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
  have : cf b γ = x := by rw [cf, hgx, colsOf4_decodeC4 hxv]
  rw [← this]
  exact h.mem_els hγ

omit [Finite V] in
theorem p9_sub_els (h : IsNodeOf b Γ s) (ha : InD (Γ.map (phi4 b)) a9C)
    (hb : InD (Γ.map (phi4 b)) b9C) : ∀ x ∈ p9C.1, x ∈ s.els :=
  sub_els_of_inD h (inD_of_mem_closeC fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb)

omit [Finite V] in
theorem cube_of_pow_nine [Sp4Data] {B : LinearMap.BilinForm (ZMod 2) V}
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) {y : V ≃ₗ[ZMod 2] V}
    (hy : y ∈ KGCert.spGroup B) (h9 : y ^ 9 = 1) : y ^ 3 = 1 := by
  have hsp : cf b y ∈ spElsC :=
    colsOf4_mem_spElsC ((phi4_mem_sympFour_iff b hgram y).mpr hy)
  have h1 : powC (cf b y) 9 = oneC4 := by rw [← cf_pow, h9, cf_one]
  have h2 := sp_no9 _ hsp h1
  rw [← cf_mul, ← cf_mul, ← cf_one b] at h2
  have h3 := cf_injective b h2
  rw [pow_succ, pow_two, mul_assoc]
  exact h3

theorem p9Sub_comm [Sp4Data] {π ρ : V ≃ₗ[ZMod 2] V} (hπ : π ∈ p9Sub b)
    (hρ : ρ ∈ p9Sub b) : π * ρ = ρ * π := S36.p9_comm hπ hρ

theorem p9Sub_cube [Sp4Data] {π : V ≃ₗ[ZMod 2] V} (hπ : π ∈ p9Sub b) :
    π ^ 3 = 1 := by
  have h := p9_cube _ hπ
  rw [← cf_mul, ← cf_mul, ← cf_one b] at h
  rw [pow_succ, pow_two, mul_assoc]
  exact cf_injective b h

theorem hasE9_of_18 [Sp4Data] {B : LinearMap.BilinForm (ZMod 2) V}
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) (hΓ : Γ ≤ KGCert.spGroup B)
    (h : IsNodeOf b Γ s) (ha : InD (Γ.map (phi4 b)) a9C) (hb : InD (Γ.map (phi4 b)) b9C)
    (h18 : Nat.card Γ = 18) : HasE9 Γ := by
  have hsub := p9_sub_els h ha hb
  have hle : p9Sub b ≤ Γ := listSub_le h hsub
  have hcard : Nat.card (p9Sub b) = 9 := (card_listSub h p9_nodup hsub).trans p9_len
  have hidx : ((p9Sub b).subgroupOf Γ).index = 2 := by
    have h1 := Subgroup.card_mul_index ((p9Sub b).subgroupOf Γ)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard, h18] at h1
    omega
  have hnorm : ((p9Sub b).subgroupOf Γ).Normal := Subgroup.normal_of_index_eq_two hidx
  refine ⟨p9Sub b, hle, hcard, fun γ hγ => ?_, fun _ hπ _ hρ => p9Sub_comm hπ hρ,
    fun _ hπ => p9Sub_cube hπ, fun y hy h9 => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro π
    constructor
    · intro hπ
      have := hnorm.conj_mem ⟨π, hle hπ⟩ (Subgroup.mem_subgroupOf.mpr hπ) ⟨γ, hγ⟩
      exact Subgroup.mem_subgroupOf.mp this
    · intro hπ
      have := hnorm.conj_mem ⟨γ * π * γ⁻¹, hle hπ⟩ (Subgroup.mem_subgroupOf.mpr hπ)
        ⟨γ, hγ⟩⁻¹
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv] at this
      rwa [show γ⁻¹ * (γ * π * γ⁻¹) * γ⁻¹⁻¹ = π by group] at this
  · have h3 := cube_of_pow_nine hgram (hΓ hy) h9
    have hsq : (⟨y, hy⟩ : ↥Γ) * ⟨y, hy⟩ ∈ (p9Sub b).subgroupOf Γ :=
      Subgroup.mul_self_mem_of_index_two hidx _
    rw [Subgroup.mem_subgroupOf] at hsq
    have e : y = y ^ 3 * (y * y)⁻¹ := by group
    rw [e, h3, one_mul]
    exact (p9Sub b).inv_mem hsq

theorem hasE9_of_36 [Sp4Data] {B : LinearMap.BilinForm (ZMod 2) V}
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) (hΓ : Γ ≤ KGCert.spGroup B)
    (h : IsNodeOf b Γ s) (h36 : ∀ x, x ∈ s.els ↔ x ∈ specK.s36.1) : HasE9 Γ := by
  refine ⟨p9Sub b, S36.p9_le h h36, S36.card_p9 h h36, S36.p9_normal h h36,
    fun _ hπ _ hρ => p9Sub_comm hπ hρ, fun _ hπ => p9Sub_cube hπ, fun y hy h9 => ?_⟩
  have h3 := cube_of_pow_nine hgram (hΓ hy) h9
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  · exact S36.mem_p9 h h36 hy hy1 h3

theorem sp4_classify_of [Sp4Data] {B : LinearMap.BilinForm (ZMod 2) V}
    (halt : ∀ v, B v v = 0) (hnd : B.Nondegenerate) (hd : Module.finrank (ZMod 2) V = 4)
    (hΓ : Γ ≤ KGCert.spGroup B) (h1018 : 10 ∣ Nat.card Γ ∨ 18 ∣ Nat.card Γ)
    {W : Submodule (ZMod 2) V} {u w : V} (hW : ∀ x ∈ W, x = 0 ∨ x = u ∨ x = w ∨ x = u + w)
    (huW : u ∈ W) (hwW : w ∈ W) (hu : u ≠ 0) (hw : w ≠ 0) (huw : u ≠ w) (hB : B u w = 0)
    (hT : Nat.gcd (Nat.card Γ) 16 ∣ Nat.card ↥(Γ ⊓ stabW W))
    (h3 : ∃ y ∈ Γ, y ∈ stabW W ∧ y ≠ 1 ∧ y ^ 3 = 1 ∧ ∃ x ∈ W, y x ≠ x)
    (hne : ¬ Γ ≤ stabW W)
    (h2 : ∃ t ∈ Γ, t ∈ stabW W ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ ∃ x ∈ W, t x ≠ x) :
    (Nat.card Γ = 18 ∧ HasE9 Γ) ∨
    (Nonempty (↥Γ ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧ HasE9 Γ ∧
      Nat.card ↥(Γ ⊓ fixW W) = 2 ∧
      ∃ X : Subgroup (V ≃ₗ[ZMod 2] V), X ≤ Γ ∧ Nat.card X = 6 ∧
        (∃ α ∈ X, ∃ β ∈ X, α * β ≠ β * α) ∧ Γ ≤ Subgroup.normalizer (X : Set _) ∧
        Γ ⊓ fixW W ≤ X ∧
        ∀ y ∈ Γ, y ∈ stabW W → y ∈ X → y ≠ 1 → y ^ 3 = 1 → ∀ x ∈ W, y x = x) ∨
    (Nonempty (↥Γ ≃* Equiv.Perm (Fin 5)) ∧
      (∃ (φ : ↥Γ ≃* RuType.SigmaL2F4) (ψ : V ≃+ (Fin 2 → RuType.F4)),
        ∀ (γ : ↥Γ) (v : V), ψ ((γ : V ≃ₗ[ZMod 2] V) v) = RuType.sigmaAct (φ γ) (ψ v)) ∧
      (∀ γ ∈ Γ ⊓ fixW W, γ ∈ (CFSG.Open.genFittingLayer ↥Γ).map Γ.subtype) ∧
      (∀ t ∈ Γ, t ∈ stabW W → t ≠ 1 → t ^ 2 = 1 → (∃ x ∈ W, t x ≠ x) →
        Nat.card ↥(Γ ⊓ (fixW W ⊓ Subgroup.centralizer {t})) = 2) ∧ QuadMoved B Γ u w) ∨
    (((Nonempty (↥Γ ≃* ↥(alternatingGroup (Fin 6))) ∧ Nat.card ↥(Γ ⊓ fixW W) = 4) ∨
      (Nonempty (↥Γ ≃* Equiv.Perm (Fin 6)) ∧ Nat.card ↥(Γ ⊓ fixW W) = 8 ∧
        ∀ γ ∈ Γ, (∀ f ∈ Γ ⊓ fixW W, f * γ = γ * f) → γ ∈ fixW W)) ∧ QuadMoved B Γ u w) := by
  classical
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have := finite_gl (V := V)
  obtain ⟨b₀, hb₀⟩ := exists_antidiag_basis4 halt hnd hd
  obtain ⟨b, hb, s, hsL, hnode, h9data⟩ : ∃ b : Module.Basis (Fin 4) (ZMod 2) V,
      (∀ i j, B (b i) (b j) = antidiagGram i j) ∧ ∃ s : Node, (s ∈ ov5K ∨ s ∈ ov9K) ∧
        IsNodeOf b Γ s ∧ (¬ 5 ∣ Nat.card Γ →
          InD (Γ.map (phi4 b)) a9C ∧ InD (Γ.map (phi4 b)) b9C) := by
    by_cases h5 : 5 ∣ Nat.card Γ
    · obtain ⟨b, hb, hx⟩ := exists_basis_inD_5 b₀ hb₀ hΓ h5
      obtain ⟨s, hs, hsD, hsΓ⟩ := exists_node_eq_5 (map_phi4_le b hb hΓ) hx
      exact ⟨b, hb, s, Or.inl hs, isNodeOf_of hsD hsΓ (node_nodup (Or.inl hs)),
        fun h => absurd h5 h⟩
    · have h9 : 9 ∣ Nat.card Γ := by
        rcases h1018 with h | h
        · exact absurd (Nat.dvd_trans (by norm_num) h) h5
        · exact Nat.dvd_trans (by norm_num) h
      obtain ⟨b, hb, ha, hb'⟩ := exists_basis_inD_9 b₀ hb₀ hΓ h9
      obtain ⟨s, hs, hsD, hsΓ⟩ := exists_node_eq_9 (map_phi4_le b hb hΓ) ha hb'
      exact ⟨b, hb, s, Or.inr hs, isNodeOf_of hsD hsΓ (node_nodup (Or.inr hs)),
        fun _ => ⟨ha, hb'⟩⟩
  have hfeas := feasible_of hnode hW huW hwW hu hw huw hT h3 hne h2
  have hc := lineOk_apply hsL (lineOf_mem b hb hu hw huw hB) hfeas
  have hG := hnode.card_eq
  have hquad : (s.mask = specK.s120.2 ∨ 360 ≤ s.els.length) → QuadMoved B Γ u w :=
    fun hcase q hq hq1 hq2 hq3 => exists_move_quad hsL hnode hcase hb hu hw huw hB hq hq1 hq2 hq3
  rcases concl_cases hsL hnode hW huW hwW hu hw huw hc with
    h18 | ⟨h36, hF2, hX⟩ | ⟨hm120, h120, hF60, hcen⟩ | ⟨h360, hF4⟩ | ⟨h720, hF8, hC⟩
  · left
    have h5' : ¬ 5 ∣ Nat.card Γ := by rw [h18]; norm_num
    obtain ⟨ha, hb'⟩ := h9data h5'
    exact ⟨h18, hasE9_of_18 hb hΓ hnode ha hb' h18⟩
  · right; left
    refine ⟨S36.mulEquiv hnode h36, hasE9_of_36 hb hΓ hnode h36, hF2, ?_⟩
    rcases hX with ⟨hA1, hA2⟩ | ⟨hB1, hB2⟩
    · exact ⟨factA b, S36.factA_le hnode h36, S36.card_factA hnode h36, S36.nonab_A hnode h36,
        S36.normal_A hnode h36, fun γ hγ => hA1 γ hγ,
        fun y hy hyW hyX => hA2 y ⟨hy, hyW⟩ hyX⟩
    · exact ⟨factB b, S36.factB_le hnode h36, S36.card_factB hnode h36, S36.nonab_B hnode h36,
        S36.normal_B hnode h36, fun γ hγ => hB1 γ hγ,
        fun y hy hyW hyX => hB2 y ⟨hy, hyW⟩ hyX⟩
  · right; right; left
    exact ⟨S120.permEquiv hnode h120, S120.natural hnode h120,
      fun γ hγ => S120.mem_layer hnode h120 hγ.1 (hF60 γ hγ),
      fun t ht htW ht1 ht2 hmove => hcen t ⟨ht, htW⟩ ht1 ht2 hmove, hquad (Or.inl hm120)⟩
  · right; right; right
    exact ⟨Or.inl ⟨S6.mulEquiv_alt hb hΓ h360, hF4⟩, hquad (Or.inr (by rw [← hG, h360]))⟩
  · right; right; right
    exact ⟨Or.inr ⟨S6.mulEquiv_perm hb hΓ h720, hF8, hC⟩,
      hquad (Or.inr (by rw [← hG, h720]; norm_num))⟩

end CFSG.Quasithin.H13.Sp4Cert
