module

public import CFSG.Quasithin.EmptyFaithful.S143NG
public import CFSG.Quasithin.EmptyFaithful.S143NE
public import CFSG.Quasithin.EmptyFaithful.S152RDef

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

open A6Model

section Cards

variable {Y Γ : Type*} [Group Y] [Finite Y] [Group Γ] {φ : Y →* Γ} {Â : Subgroup Y} {y : Y}

omit [Finite Y] in
theorem BlockData.card_Y (h : BlockData φ Â y) : Nat.card Y = 960 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (Y ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  rw [h2, h.card_range, h.ker, h.card] at h1
  exact h1

end Cards

section Sd

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

section Rel

variable {δ : G} (hδD : δ ∈ dOf T M)

include c hδD

theorem commutator_mem_Z_of_rU {x : G} (hx : x ∈ rOf T M ⊔ uOfL22 T M) :
    δ * x * δ⁻¹ * x⁻¹ ∈ quasithinOmegaOneCenter T := by
  have hURN : uOfL22 T M ≤ Subgroup.normalizer (rOf T M : Set G) := fun u hu =>
    le_normalizer_pCoreOf 2 (iTwo T M) (le_conjClosure _ _ hu)
  obtain ⟨ρ, hρ, u, hu, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hURN).1 hx
  have hcu : δ * u = u * δ := (Subgroup.mem_centralizer_iff.mp hδD.2 u hu).symm
  have e : δ * (ρ * u) * δ⁻¹ * (ρ * u)⁻¹ = δ * ρ * δ⁻¹ * ρ⁻¹ := by
    calc δ * (ρ * u) * δ⁻¹ * (ρ * u)⁻¹ = δ * ρ * (u * δ⁻¹) * u⁻¹ * ρ⁻¹ := by group
      _ = δ * ρ * (δ⁻¹ * u) * u⁻¹ * ρ⁻¹ := by
          have : u * δ⁻¹ = δ⁻¹ * u := by
            have h1 : δ⁻¹ * (δ * u) * δ⁻¹ = δ⁻¹ * (u * δ) * δ⁻¹ := by rw [hcu]
            simpa [mul_assoc] using h1
          rw [this]
      _ = δ * ρ * δ⁻¹ * ρ⁻¹ := by group
  rw [e]
  exact c.dOf_commutator_mem hδD hρ

theorem relIndex_rU_inf_centralizer_le :
    ((rOf T M ⊔ uOfL22 T M) ⊓ Subgroup.centralizer ({δ} : Set G)).relIndex
      (rOf T M ⊔ uOfL22 T M) ≤ 2 := by
  set X := rOf T M ⊔ uOfL22 T M with hX
  set C := X ⊓ Subgroup.centralizer ({δ} : Set G) with hC
  have hXT : X ≤ T := sup_le (rOf_le_T_of_hyp c.h1281)
    ((uOfL22_le_qOf c).trans (qOf_le_T_of_hyp c.h1281))
  by_cases hall : ∀ x ∈ X, x ∈ C
  · have hCX : C = X := le_antisymm inf_le_left hall
    rw [hCX, Subgroup.relIndex_self]
    norm_num
  · push Not at hall
    obtain ⟨x₀, hx₀, hx₀C⟩ := hall
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
      have h2 := c.h1281.card_omegaOneCenter
      have : Nontrivial ↥(quasithinOmegaOneCenter T) :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [h2]; norm_num)
      obtain ⟨w, hw⟩ := exists_ne (1 : ↥(quasithinOmegaOneCenter T))
      exact ⟨w, w.2, fun h => hw (Subtype.ext h)⟩
    have hz2 : z * z = 1 := by
      have := sq_eq_one_of_mem_omegaOneCenter T hz
      rwa [pow_two] at this
    have hzcen : ∀ u ∈ T, u * z = z * u := fun u hu =>
      Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T hz).2 u hu
    have hcomm : ∀ x ∈ X, x ∉ C → δ * x * δ⁻¹ = z * x := by
      intro x hx hxC
      have hZ := commutator_mem_Z_of_rU c hδD hx
      rcases c.mem_Z_cases hz hz1 hZ with h1 | h1
      · exfalso
        apply hxC
        refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_⟩
        rw [Set.mem_singleton_iff] at hh'
        subst hh'
        have h3 : h' * x * h'⁻¹ * x⁻¹ = 1 := h1
        calc h' * x = (h' * x * h'⁻¹ * x⁻¹) * (x * h') := by group
          _ = x * h' := by rw [h3, one_mul]
      · calc δ * x * δ⁻¹ = (δ * x * δ⁻¹ * x⁻¹) * x := by group
          _ = z * x := by rw [h1]
    rw [Subgroup.relIndex, show C.subgroupOf X = C.subgroupOf X from rfl]
    have h2 : (C.subgroupOf X).index = 2 := by
      rw [Subgroup.index_eq_two_iff_exists_notMem_and]
      refine ⟨⟨x₀, hx₀⟩, fun h => hx₀C (Subgroup.mem_subgroupOf.mp h), fun b => ?_⟩
      by_cases hbC : (b : G) ∈ C
      · right
        exact Subgroup.mem_subgroupOf.mpr hbC
      · left
        refine Subgroup.mem_subgroupOf.mpr ⟨X.mul_mem b.2 hx₀, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_
        rw [Set.mem_singleton_iff] at hh'
        subst hh'
        have e1 := hcomm b b.2 hbC
        have e2 := hcomm x₀ hx₀ hx₀C
        have : h' * ((b : G) * x₀) * h'⁻¹ = (b : G) * x₀ := by
          calc h' * ((b : G) * x₀) * h'⁻¹ = (h' * (b : G) * h'⁻¹) * (h' * x₀ * h'⁻¹) := by group
            _ = (z * (b : G)) * (z * x₀) := by rw [e1, e2]
            _ = z * ((b : G) * z) * x₀ := by group
            _ = z * (z * (b : G)) * x₀ := by rw [hzcen (b : G) (hXT b.2)]
            _ = (z * z) * ((b : G) * x₀) := by group
            _ = (b : G) * x₀ := by rw [hz2, one_mul]
        calc h' * ((b : G) * x₀) = (h' * ((b : G) * x₀) * h'⁻¹) * h' := by group
          _ = ((b : G) * x₀) * h' := by rw [this]
    omega

end Rel

section SdKd

variable {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2) {p : Fin 6}
  (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1)
  {y₅ : G} (hy₅ : y₅ ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) (hy₅o : orderOf y₅ = 5)

include hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o

theorem card_kd
    : Nat.card ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) = 960 :=
  (blockData_kd hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o).card_Y

theorem card_kd_inf_sd :
    Nat.card ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊓ sdOf T M δ) = 64 := by
  have hRU : rOf T M ⊔ uOfL22 T M ≤ kOf T M (c.Ac hrW hrV hr2) :=
    c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hRQ : rOf T M ⊔ uOfL22 T M ≤ rOf T M ⊔ qOf T := sup_le_sup_left (uOfL22_le_qOf c) _
  have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp c.h1281
  set W := (rOf T M ⊔ uOfL22 T M) ⊓ Subgroup.centralizer ({δ} : Set G) with hW
  have hWP : W ≤ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊓ sdOf T M δ := fun w hw =>
    ⟨⟨hRU hw.1, hw.2⟩, ⟨hRQ hw.1, hw.2⟩⟩
  have hWcard : 64 ≤ Nat.card W := by
    have h1 := Subgroup.relIndex_mul_card W (rOf T M ⊔ uOfL22 T M)
    have hWinf : W ⊓ (rOf T M ⊔ uOfL22 T M) = W :=
      inf_eq_left.mpr (inf_le_left : W ≤ rOf T M ⊔ uOfL22 T M)
    rw [hWinf, c.card_rOf_sup_uOfL22] at h1
    have h2 := relIndex_rU_inf_centralizer_le c hδD
    have h3 : W.relIndex (rOf T M ⊔ uOfL22 T M) ≤ 2 := h2
    by_contra hlt
    push Not at hlt
    have h4 : W.relIndex (rOf T M ⊔ uOfL22 T M) * Nat.card ↥W ≤ 2 * Nat.card ↥W :=
      Nat.mul_le_mul_right _ h3
    omega
  have hP2 : IsPGroup 2 ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊓ sdOf T M δ) :=
    c.hyp.sylow.1.to_le (fun w hw => hRQT hw.2.1)
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hdvd : Nat.card ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊓ sdOf T M δ) ∣ 960 := by
    rw [← card_kd c hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hn6 : n ≤ 6 := by
    by_contra hn7
    push Not at hn7
    have h7 : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 hn7
    rw [← hn] at h7
    have := dvd_trans h7 hdvd
    norm_num at this
  have hle : Nat.card ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊓ sdOf T M δ) ≤ 64 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
      _ = 64 := by norm_num
  have hge := hWcard.trans (Subgroup.card_le_of_le hWP)
  omega

omit hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o in
include c in
theorem relIndex_sdOf_le (hrq : (rOf T M ⊔ qOf T).relIndex T = 2) :
    (sdOf T M δ).relIndex (tdOf T δ) ≤ 2 := by
  have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp c.h1281
  have h1 : sdOf T M δ = (rOf T M ⊔ qOf T) ⊓ tdOf T δ := by
    ext w
    constructor
    · intro hw
      exact ⟨hw.1, hRQT hw.1, hw.2⟩
    · intro hw
      exact ⟨hw.1, hw.2.2⟩
  rw [h1, Subgroup.inf_relIndex_right]
  exact (Subgroup.relIndex_le_of_le_right inf_le_left (by rw [hrq]; norm_num)).trans hrq.le

omit hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o in
include c in
theorem sd_le_normalizer_kd
    (hNAK : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) =
      Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G)) :
    sdOf T M δ ≤ Subgroup.normalizer (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ : Set G) := by
  have key : ∀ s' ∈ sdOf T M δ, ∀ k ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ,
      s' * k * s'⁻¹ ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ := by
    intro s' hs' k hk
    have hsN : s' ∈ Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G) :=
      hNAK ▸ (c.isSylowTwoOf_rq_normalizer_Ac hrW hrV hr2).1 hs'.1
    refine ⟨(Subgroup.mem_normalizer_iff.mp hsN k).mp hk.1,
      Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_⟩
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    have hs : h' * s' = s' * h' := (Subgroup.mem_centralizer_iff.mp hs'.2 h' rfl)
    have hk' : h' * k = k * h' := Subgroup.mem_centralizer_iff.mp hk.2 h' rfl
    calc h' * (s' * k * s'⁻¹) = (h' * s') * k * s'⁻¹ := by group
      _ = (s' * h') * k * s'⁻¹ := by rw [hs]
      _ = s' * (h' * k) * s'⁻¹ := by group
      _ = s' * (k * h') * s'⁻¹ := by rw [hk']
      _ = (s' * k * s'⁻¹) * (s' * h' * s'⁻¹) := by group
      _ = (s' * k * s'⁻¹) * (h' * s' * s'⁻¹) := by rw [← hs]
      _ = (s' * k * s'⁻¹) * h' := by group
  intro s' hs'
  refine mem_normalizer_of_conj_mem (fun k hk => key s' hs' k hk) (fun k hk => ?_)
  have := key s'⁻¹ ((sdOf T M δ).inv_mem hs') k hk
  simpa using this

theorem isLocal_kd_sd
    (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
    (hNAK : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) =
      Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G)) :
    quasithinIsLocal (sdOf T M δ) (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN := sd_le_normalizer_kd c hNAK (δ := δ)
  have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp c.h1281
  refine ⟨c.hyp.sylow.1.to_le (fun w hw => hRQT hw.1),
    (mem_cComp_iff).mp (kd_cComp hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o hSN), ?_, ?_⟩
  ·
    have hKS := card_sup_mul_card_inf_of_le_normalizer hSN
    have h1 := Subgroup.relIndex_mul_card (sdOf T M δ)
      (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊔ sdOf T M δ)
    rw [inf_eq_left.mpr le_sup_right] at h1
    have h960 := card_kd c hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o
    have h64 := card_kd_inf_sd c hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o
    have hSpos : 0 < Nat.card ↥(sdOf T M δ) := Nat.card_pos
    rw [h960, h64] at hKS
    have h15 : (sdOf T M δ).relIndex (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊔ sdOf T M δ) = 15 := by
      apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < 64)
      apply Nat.eq_of_mul_eq_mul_right hSpos
      calc (sdOf T M δ).relIndex (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊔ sdOf T M δ) * 64 *
            Nat.card ↥(sdOf T M δ)
          = ((sdOf T M δ).relIndex (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊔ sdOf T M δ) *
            Nat.card ↥(sdOf T M δ)) * 64 := by ring
        _ = 960 * Nat.card ↥(sdOf T M δ) := by rw [h1]; omega
        _ = 15 * 64 * Nat.card ↥(sdOf T M δ) := by ring
    show ¬ 2 ∣ (sdOf T M δ).relIndex (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊔ sdOf T M δ)
    rw [h15]
    norm_num
  · intro hbot
    have hδ2 : δ * δ = 1 := Gamma_sq hS htT htRQ hM hC1 hδ
    have hδ1 : δ ≠ 1 := fun e => hδA (e ▸ (c.Ac hrW hrV hr2).one_mem)
    have hδS : δ ∈ sdOf T M δ :=
      ⟨(le_sup_right : qOf T ≤ rOf T M ⊔ qOf T) hδD.1, Subgroup.mem_centralizer_iff.mpr
        fun h' hh' => by rw [Set.mem_singleton_iff] at hh'; subst hh'; rfl⟩
    have hzp : IsPGroup 2 ↥(Subgroup.zpowers δ) := by
      have hord : orderOf δ = 2 := orderOf_eq_prime (by rw [← pow_two] at hδ2; exact hδ2) hδ1
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
    have hle : Subgroup.zpowers δ ≤ pCoreOf 2 (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊔ sdOf T M δ) :=
      le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hδS))
        (sup_le (inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers δ))
          (inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers δ))) hzp
    have hδmem : δ ∈ pCoreOf 2 (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊔ sdOf T M δ) :=
      hle (Subgroup.mem_zpowers δ)
    rw [hbot] at hδmem
    exact hδ1 (Subgroup.mem_bot.mp hδmem)

end SdKd

end Sd

end S143

end CFSG.Quasithin
