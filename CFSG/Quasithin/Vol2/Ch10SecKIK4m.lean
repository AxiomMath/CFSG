module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4l
public import CFSG.Quasithin.Vol2.Ch10SecKIK4g

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem card_autOn_eq {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (hperf : ⁅L, L⁆ = L) (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hLW : ¬ L ≤ Subgroup.centralizer (W : Set G)) :
    ∃ k : ℕ, Nat.card ↥(autOn L W) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := InternalSec.autOnHom hLN with hρ
  have hker : ρ.ker ≤ CFSG.pCore 2 ↥L := by
    by_contra h
    apply hLW
    have htop := eq_top_of_not_le_pCore hperf hsimple h
    intro l hl
    exact (InternalSec.mem_ker_autOnHom hLN ⟨l, hl⟩).1 (htop ▸ Subgroup.mem_top _)
  have h1 := Subgroup.card_ker_mul_card_of_surjective (InternalSec.autOnHom_surjective hLN)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hker
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  have hmd : m ∣ 2 ^ a := ⟨Nat.card ↥ρ.ker, by rw [← ha, hm, mul_comm]⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hmd
  refine ⟨k, ?_⟩
  have hpos : 0 < Nat.card ↥ρ.ker := Nat.card_pos
  rw [hm, hk] at h2
  rw [← hk]
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, h2, hk]
  ring

theorem false_of_swap {K : Subgroup (Equiv.Perm (Fin 7))} (h7 : 7 ∣ Nat.card ↥K)
    (h2 : 2 < Nat.card ↥K) (hlt : Nat.card ↥K < 2520) {t : Equiv.Perm (Fin 7)} (ht : t.IsSwap)
    (htN : t ∈ Subgroup.normalizer (K : Set (Equiv.Perm (Fin 7)))) : False := by
  classical
  set M := K ⊔ Subgroup.zpowers t with hM
  have hMN : M ≤ Subgroup.normalizer (K : Set (Equiv.Perm (Fin 7))) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 htN)
  have hMtop : M = ⊤ := by
    refine Equiv.Perm.subgroup_eq_top_of_swap_mem (H := M) (by norm_num) ?_
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) ht
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact h7.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hKn : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hMtop]
    exact hMN
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
  rcases hs.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin 7))) with h | h
  ·
    have hinj : Function.Injective (Equiv.Perm.sign.comp K.subtype) := by
      rw [injective_iff_map_eq_one]
      intro k hk
      have hkA : (k : Equiv.Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := hk
      have : (⟨k, hkA⟩ : ↥(alternatingGroup (Fin 7))) ∈ K.subgroupOf (alternatingGroup (Fin 7)) :=
        Subgroup.mem_subgroupOf.2 k.2
      rw [h, Subgroup.mem_bot] at this
      have h1 := congrArg Subtype.val this
      exact Subtype.ext h1
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
    omega
  ·
    have hle : alternatingGroup (Fin 7) ≤ K := fun σ hσ =>
      Subgroup.mem_subgroupOf.1 (h ▸ Subgroup.mem_top (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 7))))
    have := Subgroup.card_le_of_le hle
    rw [card_alt7] at this
    omega

omit [Finite G] in
theorem conjAct_mul_mem_autOn {L W : Subgroup G} {g : Subgroup.normalizer (W : Set G)}
    (hg : (g : G) ∈ Subgroup.normalizer (L : Set G)) {φ : MulAut ↥W} (hφ : φ ∈ autOn L W) :
    conjAct W g * φ * (conjAct W g)⁻¹ ∈ autOn L W := by
  obtain ⟨l, hl, rfl⟩ := Setup.mem_autOn_iff.1 hφ
  have hgl : (g : G) * l * (g : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg l).mp hl
  rw [← map_inv, ← map_mul, ← map_mul]
  exact Setup.mem_autOn_iff.2 ⟨g * l * g⁻¹, hgl, rfl⟩

theorem card_comap_of_bijective {A B : Type*} [Group A] [Group B] {π : A →* B}
    (hπ : Function.Bijective π) (S : Subgroup B) : Nat.card ↥(S.comap π) = Nat.card ↥S := by
  rw [← Subgroup.card_map_of_injective hπ.1, Subgroup.map_comap_eq_self_of_surjective hπ.2]

theorem false_of_l32 (h42 : AsB42) {H R J W L : Subgroup G} [IsMulCommutative ↥W]
    (hW : IsElemAbelian 2 W) (hred : IsTwoReducedIn H W) (hS : IsSylowTwoOf R H) (hJH : J ≤ H)
    (hHJ : H ≤ Subgroup.normalizer (J : Set G)) (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J)
    (hSQ : SQTKGroup ↥J) (hCJ : J ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 J)
    (α : ↥J →* ↥(alternatingGroup (Fin 7))) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥J) (hJ : J = ⁅J, thompsonJ R⁆)
    (hJW : ¬ J ≤ Subgroup.centralizer (W : Set G))
    (hirr : ∀ X : Subgroup G, X ≤ W → J ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = W)
    (hcard : Nat.card ↥W = 2 ^ 6) (hLJ : L ≤ J) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (h7 : 7 ∣ Nat.card ↥(autOn L W)) (h2' : 2 < Nat.card ↥(autOn L W))
    (hlt : Nat.card ↥(autOn L W) < 2520) : False := by
  obtain ⟨π, hR, hinj, hJF, t, ht, g, hgR, hg⟩ :=
    exists_swap h42 hW hred hS hJH hHJ h2 hSQ hCJ α hαs hαk hJ hJW hirr hcard
  have hLF : autOn L W ≤ ffJ (autOn H W) := (A4.autOn_mono hLJ).trans hJF
  obtain ⟨K, hK⟩ : ∃ K : Subgroup (Equiv.Perm (Fin 7)),
      K = ((autOn L W).subgroupOf (ffJ (autOn H W))).comap π := ⟨_, rfl⟩
  have hKc : Nat.card ↥K = Nat.card ↥(autOn L W) := by
    rw [hK, card_comap_of_bijective ⟨hinj, hR.1⟩]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLF).toEquiv
  have hconj : ∀ y ∈ K, t * y * t⁻¹ ∈ K := by
    intro y hy
    rw [hK] at hy ⊢
    have hy' : ((π y : ↥(ffJ (autOn H W))) : MulAut ↥W) ∈ autOn L W :=
      Subgroup.mem_subgroupOf.1 hy
    show π (t * y * t⁻¹) ∈ (autOn L W).subgroupOf (ffJ (autOn H W))
    rw [Subgroup.mem_subgroupOf, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hg]
    exact conjAct_mul_mem_autOn (hRL hgR) hy'
  have htinv : t⁻¹ = t := by
    obtain ⟨a, b, -, rfl⟩ := ht
    exact Equiv.swap_inv a b
  have htN : t ∈ Subgroup.normalizer (K : Set (Equiv.Perm (Fin 7))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj x hx, fun hx => ?_⟩
    have := hconj _ hx
    have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = t⁻¹ * (t * x * t⁻¹) * t := by rw [htinv]
        _ = x := by group
    rwa [e] at this
  exact false_of_swap (hKc ▸ h7) (hKc ▸ h2') (hKc ▸ hlt) ht htN

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
