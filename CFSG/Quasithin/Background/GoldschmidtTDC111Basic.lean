module

public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.TDC111

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Group

variable {Γ : Type*} [Group Γ]

theorem odd_mem_of_isSubnormal_of_index {K : Subgroup Γ} (hK : K.IsSubnormal) :
    (∃ n : ℕ, K.index = 2 ^ n) → ∀ {x : Γ}, Odd (orderOf x) → x ∈ K := by
  induction hK with
  | top => exact fun _ x _ => Subgroup.mem_top x
  | step H K' h_le _ hN ih =>
    intro ⟨n, hn⟩ x hx
    have hdvd : K'.index ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_of_le h_le
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hxK : x ∈ K' := ih ⟨m, hm⟩ hx
    have hrel : H.relIndex K' ∣ 2 ^ n := by
      refine Dvd.intro K'.index ?_
      rw [← hn]
      exact Subgroup.relIndex_mul_index h_le
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hrel
    let x' : ↥K' := ⟨x, hxK⟩
    have hx' : Odd (orderOf x') := by rwa [Subgroup.orderOf_mk]
    have hord : orderOf (QuotientGroup.mk x' : ↥K' ⧸ H.subgroupOf K') = 1 := by
      have h1 : orderOf (QuotientGroup.mk x' : ↥K' ⧸ H.subgroupOf K') ∣ orderOf x' :=
        orderOf_map_dvd (QuotientGroup.mk' (H.subgroupOf K')) x'
      have h2 : orderOf (QuotientGroup.mk x' : ↥K' ⧸ H.subgroupOf K') ∣ 2 ^ j := by
        have := orderOf_dvd_natCard (QuotientGroup.mk x' : ↥K' ⧸ H.subgroupOf K')
        rw [← Subgroup.index_eq_card] at this
        exact hj ▸ this
      have hodd : Odd (orderOf (QuotientGroup.mk x' : ↥K' ⧸ H.subgroupOf K')) :=
        hx'.of_dvd_nat h1
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right j hodd.coprime_two_right) h2
    have h3 : (QuotientGroup.mk x' : ↥K' ⧸ H.subgroupOf K') = 1 := orderOf_eq_one_iff.1 hord
    have h4 : x' ∈ H.subgroupOf K' := (QuotientGroup.eq_one_iff x').1 h3
    exact Subgroup.mem_subgroupOf.1 h4

section Finite

variable [Finite Γ]

theorem index_two_pow_of_mul {K S : Subgroup Γ} (hS : IsPGroup 2 S)
    (h : ∀ g : Γ, ∃ k ∈ K, ∃ s ∈ S, g = k * s) : ∃ n : ℕ, K.index = 2 ^ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let x : Γ ⧸ K := QuotientGroup.mk 1
  have horb : MulAction.orbit S x = Set.univ := by
    ext y
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    induction y using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk, s, hs, hgs⟩ := h g⁻¹
      refine ⟨⟨s⁻¹, S.inv_mem hs⟩, ?_⟩
      show (s⁻¹ : Γ) • (QuotientGroup.mk 1 : Γ ⧸ K) = QuotientGroup.mk g
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
      have hg : g = (k * s)⁻¹ := by rw [← hgs]; simp
      have : (s⁻¹)⁻¹ * g = k⁻¹ := by
        rw [hg]
        group
      rw [this]
      exact K.inv_mem hk
  obtain ⟨n, hn⟩ := hS.card_orbit x
  refine ⟨n, ?_⟩
  rw [Subgroup.index_eq_card, ← hn, horb]
  simp

end Finite

end Group

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem eq_oTwoUpper_of_subnormal_of_mul {H K S : Subgroup G}
    (hsub : (K.subgroupOf H).IsSubnormal) (hKH : K ≤ H) (hS : IsSylowTwoOf S H)
    (hprod : ∀ h ∈ H, ∃ k ∈ K, ∃ s ∈ S, h = k * s) (hKO : K ≤ oTwoUpper H) :
    K = oTwoUpper H := by
  refine le_antisymm hKO ?_
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hidx : ∃ n : ℕ, (K.subgroupOf H).index = 2 ^ n := by
    refine index_two_pow_of_mul hS2 fun g => ?_
    obtain ⟨k, hk, s, hs, hgs⟩ := hprod g g.2
    exact ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.2 hk, ⟨s, hS.1 hs⟩, Subgroup.mem_subgroupOf.2 hs,
      Subtype.ext hgs⟩
  refine (Subgroup.closure_le K).2 ?_
  rintro x ⟨hxH, hxodd⟩
  have hx' : Odd (orderOf (⟨x, hxH⟩ : ↥H)) := by rwa [Subgroup.orderOf_mk]
  exact Subgroup.mem_subgroupOf.1 (odd_mem_of_isSubnormal_of_index hsub hidx hx')

theorem isSubnormal_iSup_blocks {H : Subgroup G} {ι : Type} [Finite ι] {B : ι → Subgroup G}
    (hB : ∀ i, IsBlock2 H (B i)) : ((⨆ i, B i).subgroupOf H).IsSubnormal := by
  have h1 : (⨆ i, (B i).subgroupOf H).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_iSup_of_pair (fun _ _ => CFSG.GroupTheory.isSubnormal_sup) _
      fun i => (hB i).2.2
  have hle : (⨆ i, B i) ≤ H := iSup_le fun i => (hB i).2.1
  have h2 : (⨆ i, B i).subgroupOf H = ⨆ i, (B i).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_iSup]
    exact (iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hB i).2.1).symm)
  rwa [h2]

omit [Finite G] in
theorem mem_normalizer_iSup_of_forall {ι : Type*} {A : ι → Subgroup G} {g : G}
    (h : ∀ i, g ∈ Subgroup.normalizer (A i : Set G)) :
    g ∈ Subgroup.normalizer ((⨆ i, A i : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun i => Subgroup.mem_normalizer_iff_map_conj_eq.1 (h i)

omit [Finite G] in
theorem le_normalizer_of_commute {A B C : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hCB : C ≤ B) : A ≤ Subgroup.normalizer (C : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : a * x * a⁻¹ = x := by rw [hc a ha x (hCB hx)]; group
    rw [this]
    exact hx
  · intro hx
    have h' : a * (a * x * a⁻¹) = (a * x * a⁻¹) * a := hc a ha _ (hCB hx)
    have h'' : a * (a * x * a⁻¹) = a * x := by rw [h']; group
    have : a * x * a⁻¹ = x := mul_left_cancel (a := a) (h''.trans (by group))
    rw [← this]
    exact hx

end Ambient

end CFSG.Quasithin.TDC111
