module

public import CFSG.Quasithin.EmptyFaithful.SzF53MNatL2
public import CFSG.Quasithin.EmptyFaithful.SzF53B1Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.F53Mod

open Equiv CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

private theorem two_conj_dec : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 4 = 1 →
    ∃ g h : Perm (Fin 5), (g * σ * g⁻¹ * (h * σ * h⁻¹)) ^ 4 ≠ 1 := by decide +kernel

private theorem pow_sixty : ∀ x : Perm (Fin 5), x ^ 60 = 1 := by decide +kernel

theorem pow_four_of_pGroup {N : Subgroup (Perm (Fin 5))} (hp : IsPGroup 2 N) {x : Perm (Fin 5)}
    (hx : x ∈ N) : x ^ 4 = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) ⟨x, hx⟩
  have h60 : orderOf x ∣ 60 := orderOf_dvd_of_pow_eq_one (pow_sixty x)
  have hord : orderOf x = 2 ^ k := by rw [← hk]; exact Subgroup.orderOf_coe ⟨x, hx⟩
  rw [hord] at h60
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h8.trans h60
    omega
  have : orderOf x ∣ 4 := by
    rw [hord]; exact (pow_dvd_pow 2 hk2 : 2 ^ k ∣ 2 ^ 2)
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem normal_pGroup_S5 {N : Subgroup (Perm (Fin 5))} (hN : N.Normal) (hp : IsPGroup 2 N) :
    N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  by_contra hne
  obtain ⟨g, h, hgh⟩ := two_conj_dec σ hne (pow_four_of_pGroup hp hσ)
  exact hgh (pow_four_of_pGroup hp (N.mul_mem (hN.conj_mem σ hσ g) (hN.conj_mem σ hσ h)))

theorem IsModelSec.cSecIn_eq_pCoreOf [Finite G] {M : Model 5} {F L X : Subgroup G}
    (h : IsModelSec M F L X) (hq : Nonempty (OTwoQuot F ≃* Perm (Fin 5))) :
    cSecIn F L X = pCoreOf 2 F := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨e⟩ := hq
  have hQF : pCoreOf 2 F ≤ F := LieType.BorelTits.pCoreOf_le 2 F
  have hCF : cSecIn F L X ≤ F := (Subgroup.closure_le F).mpr fun _ hx => hx.1
  have hQC : pCoreOf 2 F ≤ cSecIn F L X := by
    have hchar : (CFSG.Open.pCore 2 ↥F).Characteristic :=
      LieType.BorelTits.pCore_characteristic (G := ↥F) 2
    have hnF : (CFSG.Open.pCore 2 ↥F).Normal := inferInstance
    have hnorm : ((CFSG.Open.pCore 2 ↥F).map θ).Normal := hnF.map θ hθs
    have hp : IsPGroup 2 ((CFSG.Open.pCore 2 ↥F).map θ) :=
      (LieType.BorelTits.pCore_isPGroup (G := ↥F) 2).map θ
    have hbot := normal_pGroup_S5 hnorm hp
    intro x hx
    have hxF : x ∈ F := hQF hx
    have hx' : (⟨x, hxF⟩ : ↥F) ∈ CFSG.Open.pCore 2 ↥F := by
      rw [← F53B1.pCoreOf_subgroupOf F]; exact hx
    have : θ ⟨x, hxF⟩ ∈ (CFSG.Open.pCore 2 ↥F).map θ := ⟨_, hx', rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (mem_cSecIn_iff_of_ker hθk hxF).mp this
  have h1 : (pCoreOf 2 F).relIndex F = 120 := by
    rw [F53B1.relIndex_pCoreOf_eq_card e, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]; rfl
  have h2 : (cSecIn F L X).relIndex F = 120 := by
    unfold Subgroup.relIndex
    rw [← hθk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hθs, Subgroup.card_top,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have h3 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 F) (cSecIn F L X) F hQC hCF
  rw [h1, h2] at h3
  have h4 : (pCoreOf 2 F).relIndex (cSecIn F L X) = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h4) hQC

theorem isInvSub_commW_of_normal {n : ℕ} (M : Model n) {B C : Subgroup (Perm (Fin n))}
    {U : Subgroup M.W} (hBC : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B) (hU : IsInvSub M C U) :
    IsInvSub M C (commW M B U) := by
  intro c hc w hw
  unfold commW at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, u, hu, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨c * b * c⁻¹, hBC c hc b hb, M.act c u, hU c hc u hu, ?_⟩
    rw [map_mul, map_inv, act_mul_apply, act_mul_apply, act_inv_act]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

private theorem central_of_S5Syl : ∀ y ∈ S5SylF, y ≠ 1 → (∀ s ∈ S5SylF, s * y * s⁻¹ = y) →
    y = Equiv.swap 0 2 * Equiv.swap 1 3 := by decide +kernel

theorem eq_zpowers_of_normal_card_two {B : Subgroup (Perm (Fin 5))} (hB : Nat.card B = 2)
    (hBS : B ≤ S5Syl) (hn : ∀ s ∈ S5Syl, ∀ b ∈ B, s * b * s⁻¹ ∈ B) :
    B = Subgroup.zpowers (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) := by
  have hne : ∃ y ∈ B, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
    rw [this, Subgroup.card_bot] at hB
    omega
  obtain ⟨y, hyB, hy1⟩ := hne
  have hy2 : y ^ 2 = 1 := by
    have := pow_card_eq_one' (G := B) (x := ⟨y, hyB⟩)
    rw [hB] at this
    exact congrArg Subtype.val this
  have hord : orderOf y = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hy2 hy1
  have hBy : B = Subgroup.zpowers y := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hyB) ?_
    rw [Nat.card_zpowers, hord, hB]
  have hcent : ∀ s ∈ S5SylF, s * y * s⁻¹ = y := by
    intro s hs
    have h1 : s * y * s⁻¹ ∈ Subgroup.zpowers y := hBy ▸ hn s ((mem_S5Syl_iff s).mpr hs) y hyB
    rw [mem_zpowers_iff_of_pow_eq_one hy2 (by norm_num)] at h1
    obtain ⟨k, hk, hk'⟩ := h1
    interval_cases k
    · exfalso
      apply hy1
      have : s * y * s⁻¹ = 1 := by simpa using hk'.symm
      simpa using this
    · simpa using hk'.symm
  have hz : y = Equiv.swap 0 2 * Equiv.swap 1 3 :=
    central_of_S5Syl y ((mem_S5Syl_iff y).mp (hBS hyB)) hy1 hcent
  rw [hBy, hz]


section Fields

variable {H S Z : Subgroup G}

theorem comm_eq_one_iff {a x : G} : a * x * a⁻¹ * x⁻¹ = 1 ↔ a * x = x * a := by
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem IsModelSec.card_bot {n : ℕ} {M : Model n} (h : IsModelSec M H ⊥ Z) :
    Nat.card Z = Nat.card M.W := by
  have := IsModelSec.relIndex_eq h
  rwa [Subgroup.relIndex_bot_left] at this

theorem IsModelSec.card_fix_sylow {M : Model 5} (hM : M = orth ∨ M = nat)
    (h : IsModelSec M H ⊥ Z) (hS : IsSylowTwoOf S H) :
    Nat.card ↥(Z ⊓ Subgroup.centralizer (S : Set G)) = 2 := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, hsgn⟩ := hsd.exists_normalized hθs hθk hS
  have hW : Nat.card M.W = 16 := by
    rcases hM with rfl | rfl
    · exact card_orth
    · exact card_nat
  have hfix : fixSecIn S ⊥ Z = Z ⊓ Subgroup.centralizer (S : Set G) := by
    ext x
    rw [X1512.mem_fixSecIn bot_le, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hxZ, hx⟩
      refine ⟨hxZ, fun a ha => ?_⟩
      have := hx a ha
      rw [Subgroup.mem_bot] at this
      exact (comm_eq_one_iff.mp this)
    · rintro ⟨hxZ, hx⟩
      refine ⟨hxZ, fun a ha => ?_⟩
      rw [Subgroup.mem_bot]
      exact comm_eq_one_iff.mpr (hx a ha)
  have hD1 := hsd'.relIndex_fixSecIn (bot_le : ⊥ ≤ Z) hS.1
  rw [hPS, hfix] at hD1
  have hprof := profile_sylow M hM card_S5Syl
  have hf : Nat.card (fixW M S5Syl) = 2 := by
    have := congrArg (fun p => p.2.1) hprof
    exact this
  have hidx := Subgroup.card_mul_index (fixW M S5Syl)
  rw [hf, hW] at hidx
  have hrel := Subgroup.relIndex_mul_card (Z ⊓ Subgroup.centralizer (S : Set G)) Z
  rw [inf_of_le_left inf_le_left, hD1] at hrel
  have h16 : Nat.card Z = 16 := by
    have := IsModelSec.card_bot (⟨hn, θ, β, hθs, hθk, hsd⟩ : IsModelSec M H ⊥ Z)
    rw [this, hW]
  have h8 : (fixW M S5Syl).index = 8 := by omega
  rw [h8] at hrel
  omega


theorem IsModelSec.card_comm_sylow {M : Model 5} (hM : M = orth ∨ M = nat)
    (h : IsModelSec M H ⊥ Z) (hS : IsSylowTwoOf S H) : Nat.card ↥⁅Z, S⁆ = 8 := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, hsgn⟩ := hsd.exists_normalized hθs hθk hS
  have hD2 := hsd'.card_commSec (bot_le : ⊥ ≤ Z) hS.1
  rw [hPS] at hD2
  have hcomm_eq : commSec S ⊥ Z = ⁅Z, S⁆ := by unfold commSec; exact sup_bot_eq _
  rw [hcomm_eq, Subgroup.relIndex_bot_left] at hD2
  rw [hD2]
  have hprof := profile_sylow M hM card_S5Syl
  exact congrArg (fun p => p.1) hprof

theorem IsModelSec.unique2_aux {M : Model 5} (hM : M = orth ∨ M = nat) (h : IsModelSec M H ⊥ Z)
    (hS : IsSylowTwoOf S H) (hQ : cSecIn H ⊥ Z = pCoreOf 2 H) :
    ∀ Y : Subgroup G, Y ≤ S → S ≤ Subgroup.normalizer ((pCoreOf 2 H ⊔ Y : Subgroup G) : Set G) →
      (pCoreOf 2 H).relIndex (pCoreOf 2 H ⊔ Y) = 2 →
      Nat.card ↥⁅Z, Y⁆ = 4 ∧ ∀ U : Subgroup G, U ≤ Z →
        S ≤ Subgroup.normalizer (U : Set G) → Nat.card U = 4 → U = ⁅Z, Y⁆ := by
  intro Y hYS hSn h2
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, hsgn⟩ := hsd.exists_normalized hθs hθk hS
  have hSH : S ≤ H := hS.1
  have hYH : Y ≤ H := hYS.trans hSH
  have hQH : pCoreOf 2 H ≤ H := LieType.BorelTits.pCoreOf_le 2 H
  have hQY : pCoreOf 2 H ⊔ Y ≤ H := sup_le hQH hYH
  have hkΨQ : Ψ.ker = (pCoreOf 2 H).subgroupOf H := by rw [hkΨ, hQ]
  have hmapQY : (((pCoreOf 2 H) ⊔ Y).subgroupOf H).map Ψ = (Y.subgroupOf H).map Ψ := by
    rw [Subgroup.subgroupOf_sup hQH hYH, Subgroup.map_sup, ← hkΨQ,
      (Subgroup.map_eq_bot_iff _).mpr le_rfl, bot_sup_eq]
  have hcard : Nat.card ((Y.subgroupOf H).map Ψ) = 2 := by
    rw [← hmapQY, ← Subgroup.relIndex_ker, hkΨQ, Subgroup.relIndex_subgroupOf hQY, h2]
  have hYbarS : (Y.subgroupOf H).map Ψ ≤ S5Syl := by
    rw [← hPS]
    exact Subgroup.map_mono fun y hy =>
      Subgroup.mem_subgroupOf.mpr (hYS (Subgroup.mem_subgroupOf.mp hy))
  have hnorm : ∀ τ ∈ S5Syl, ∀ b ∈ (Y.subgroupOf H).map Ψ, τ * b * τ⁻¹ ∈ (Y.subgroupOf H).map Ψ := by
    intro τ hτ b hb
    rw [← hPS] at hτ
    obtain ⟨s, hs, rfl⟩ := hτ
    obtain ⟨y, hy, rfl⟩ := hb
    have hsy : (s : G) * (y : G) * (s : G)⁻¹ ∈ pCoreOf 2 H ⊔ Y :=
      ((Subgroup.mem_normalizer_iff.mp (hSn (Subgroup.mem_subgroupOf.mp hs))) (y : G)).mp
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy))
    rw [← hmapQY]
    refine ⟨s * y * s⁻¹, Subgroup.mem_subgroupOf.mpr hsy, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hYbar : (Y.subgroupOf H).map Ψ =
      Subgroup.zpowers (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) :=
    eq_zpowers_of_normal_card_two hcard hYbarS hnorm
  have hD2 := hsd'.card_commSec (bot_le : ⊥ ≤ Z) hYH
  have hcomm_eq : commSec Y ⊥ Z = ⁅Z, Y⁆ := by unfold commSec; exact sup_bot_eq _
  have hprof4 : Nat.card (commW M (Subgroup.zpowers (Equiv.swap (0 : Fin 5) 2 *
      Equiv.swap 1 3)) ⊤) = 4 := by
    rcases hM with rfl | rfl
    · exact congrArg (fun p => p.1) profile_orth.2.1
    · exact congrArg (fun p => p.1) profile_nat.2.1
  rw [hcomm_eq, Subgroup.relIndex_bot_left, hYbar] at hD2
  refine ⟨hD2.trans hprof4, ?_⟩
  intro U hUZ hSnU hU4
  have hinvU : ∀ k ∈ S, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    ((Subgroup.mem_normalizer_iff.mp (hSnU hk)) u).mp hu
  obtain ⟨YU, hYU, hYUm⟩ := (hsd'.invariant_iff_sub hSH bot_le hUZ).mp hinvU
  have hYUinv : IsInvSub M S5Syl YU := by rw [← hPS]; exact hYU
  have hφ : (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf Z)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', Subgroup.bot_subgroupOf]
  have hYUcard : Nat.card YU = 2 ^ 2 := by
    have h1 : Nat.card (YU.map β') = Nat.card YU := Subgroup.card_map_of_injective hsd'.inj
    rw [← h1, hYUm, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk',
      Subgroup.relIndex_subgroupOf hUZ, Subgroup.relIndex_bot_left, hU4]
    norm_num
  have hVinv : IsInvSub M S5Syl (commW M ((Y.subgroupOf H).map Ψ) ⊤) := by
    exact isInvSub_commW_of_normal M hnorm (fun _ _ _ _ => trivial)
  have hVcard : Nat.card (commW M ((Y.subgroupOf H).map Ψ) ⊤) = 2 ^ 2 := by
    rw [hYbar, hprof4]; norm_num
  have hYUV : YU = commW M ((Y.subgroupOf H).map Ψ) ⊤ :=
    (lemma26 M hM 2 (by norm_num)).unique ⟨hYUinv, hYUcard⟩ ⟨hVinv, hVcard⟩
  have hmapc := hsd'.map_commW (bot_le : ⊥ ≤ Z) hYH
  rw [← hYUV, hYUm, hcomm_eq] at hmapc
  have hinj := Subgroup.map_injective ((MonoidHom.ker_eq_bot_iff _).mp hφ) hmapc
  have hZY : ⁅Z, Y⁆ ≤ Z := hsd'.commutator_le hYH
  have := Subgroup.subgroupOf_inj.mp hinj
  rwa [inf_of_le_left hUZ, inf_of_le_left hZY] at this

end Fields

theorem zaFacts_of_modelSec [Finite G] {H S Z : Subgroup G} (hS : IsSylowTwoOf S H)
    (hq : Nonempty (OTwoQuot H ≃* Perm (Fin 5))) (hZ : IsOrthSec H ⊥ Z ∨ IsNatSec H ⊥ Z) :
    F53B1.ZaFacts H S Z := by
  obtain ⟨M, hM, h⟩ : ∃ M : Model 5, (M = orth ∨ M = nat) ∧ IsModelSec M H ⊥ Z := by
    rcases hZ with h | h
    · exact ⟨orth, Or.inl rfl, h⟩
    · exact ⟨nat, Or.inr rfl, h⟩
  have hsec := h.isSec (bot_le : ⊥ ≤ Z)
  have hW : Nat.card M.W = 16 := by
    rcases hM with rfl | rfl
    · exact card_orth
    · exact card_nat
  have hirr : ∀ Y : Subgroup M.W, (∀ σ : Perm (Fin 5), ∀ y ∈ Y, M.act σ y ∈ Y) →
      Y = ⊥ ∨ Y = ⊤ := by
    rcases hM with rfl | rfl
    · exact irreducible_orth
    · exact irreducible_nat
  refine ⟨⟨isMulCommutative_iff.mpr fun a b => Subtype.ext ?_, fun x hx => ?_⟩, ?_, hsec.normN,
    fun N hNZ hHN => IsModelSec.irred_of h hirr bot_le hNZ hHN,
    IsModelSec.card_fix_sylow hM h hS, IsModelSec.card_comm_sylow hM h hS,
    IsModelSec.unique2_aux hM h hS (h.cSecIn_eq_pCoreOf hq)⟩
  · have := hsec.comm a.1 a.2 b.1 b.2
    rw [Subgroup.mem_bot] at this
    exact comm_eq_one_iff.mp this
  · have := hsec.sq x hx
    rwa [Subgroup.mem_bot] at this
  · rw [IsModelSec.card_bot h, hW]

end CFSG.Quasithin.F53Mod
