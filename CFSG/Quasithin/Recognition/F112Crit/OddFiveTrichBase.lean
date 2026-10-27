module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTrichQuot
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTrichDefs
public import CFSG.Quasithin.Recognition.F112Crit.RigidLocal
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)

variable {G : Type} [Group G] [Finite G]

open CosetGeom (graph stab ballStab nbrs γ₀ γ₁)

namespace BenderLocalOf

variable {L₁ L₂ S Z : Subgroup G}

local notation "ν₀" => γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "ν₁" => γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)

private theorem exists_odd_lift_surjective {X K : Type*} [Group X] [Finite X] [Group K]
    (ψ : X →* K) (hψ : Function.Surjective ψ) {g : K} (hg : Odd (orderOf g)) :
    ∃ x : X, Odd (orderOf x) ∧ ψ x = g := by
  obtain ⟨x₀, hx₀⟩ := hψ g
  obtain ⟨k, m, hm, hlm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  have hx₁ : orderOf (x₀ ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hlm]; exact dvd_mul_right _ _),
      hlm, Nat.mul_div_cancel_left _ (by positivity)]
  have hcop : Nat.Coprime (2 ^ k) (orderOf g) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hg)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(x₀ ^ 2 ^ k) ^ j, ?_, ?_⟩
  · have hdvd : orderOf ((x₀ ^ 2 ^ k) ^ j) ∣ m := hx₁ ▸ orderOf_pow_dvd _
    exact Odd.of_dvd_nat hm hdvd
  · rw [map_pow, map_pow, hx₀, hj]

theorem trichFor_γ₁ (hs : Setting L₁ L₂ S Z) {q i : ℕ} (hK : IsBenderQuot (oTwoQuot ↥L₂) q i)
    (hT : IsTrichQuot (oTwoQuot ↥L₂)) : TrichFor ν₀ ν₁ (S ⊓ oddGen L₂) := by
  intro N hEN hNU hUN hodd
  set π : ↥L₂ →* oTwoQuot ↥L₂ := QuotientGroup.mk' (pCore 2 ↥L₂) with hπ
  have hπ_one : ∀ z : ↥L₂, π z = 1 ↔ (z : G) ∈ pCoreOf 2 L₂ := by
    intro z
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← CFSG.mem_openPCoreOf_iff_open]
  have hπ_conj : ∀ a b : ↥L₂, π (a * b * a⁻¹) = π a * π b * (π a)⁻¹ := by
    intro a b
    simp only [map_mul, map_inv]
  have hπ_comm : ∀ a b : ↥L₂,
      π (a * b * a⁻¹ * b⁻¹) = π a * π b * (π a)⁻¹ * (π b)⁻¹ := by
    intro a b
    simp only [map_mul, map_inv]
  have hL₂_stab : L₂ ≤ stab ν₀ := by
    rw [stab_γ₀_eq hs]
    exact le_sup_left
  have hL₂_norm : L₂ ≤ Subgroup.normalizer (ballStab 1 ν₀ : Set G) :=
    hL₂_stab.trans (CosetGeom.le_normalizer_ballStab 1 ν₀)
  have hS₂_norm : S ⊓ L₂ ≤ Subgroup.normalizer (ballStab 1 ν₀ : Set G) :=
    inf_le_right.trans hL₂_norm
  have hU_le_S₂ : S ⊓ oddGen L₂ ≤ S ⊓ L₂ := inf_le_inf_left S (MS93.oddGen_le L₂)
  have hUE : (S ⊓ oddGen L₂) ⊔ ballStab 1 ν₀ = (S ⊓ L₂) ⊔ ballStab 1 ν₀ :=
    inf_oddGen_sup_ballStab hK hs
  have hN_le : N ≤ (S ⊓ L₂) ⊔ ballStab 1 ν₀ := by
    rw [← hUE]
    exact hNU
  have decomp : ∀ n ∈ N, ∃ m ∈ N ⊓ (S ⊓ L₂), ∃ e ∈ ballStab 1 ν₀, n = m * e := by
    intro n hn
    obtain ⟨s, hsS, e, heE, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer hS₂_norm).mp (hN_le hn)
    exact ⟨s, ⟨(N.mul_mem_cancel_right (hEN heE)).mp hn, hsS⟩, e, heE, rfl⟩
  set Nbar : Subgroup (oTwoQuot ↥L₂) := ((N ⊓ (S ⊓ L₂)).subgroupOf L₂).map π with hNbar
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot (isSylowTwoOf_inf hs)
  have hNbar_mem : ∀ m : ↥L₂, (m : G) ∈ N ⊓ (S ⊓ L₂) → π m ∈ Nbar := by
    intro m hm
    rw [hNbar]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hm)
  have hP_mem : ∀ u : ↥L₂, (u : G) ∈ S ⊓ L₂ → π u ∈ (P : Subgroup (oTwoQuot ↥L₂)) := by
    intro u hu
    rw [hP]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
  have hle : Nbar ≤ (P : Subgroup (oTwoQuot ↥L₂)) := by
    intro x hx
    rw [hNbar] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact hP_mem y (Subgroup.mem_subgroupOf.mp hy).2
  have hnormal : ∀ x ∈ (P : Subgroup (oTwoQuot ↥L₂)), ∀ y ∈ Nbar, x * y * x⁻¹ ∈ Nbar := by
    intro x hx y hy
    rw [hP] at hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [hNbar] at hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have hx'S₂ : (x' : G) ∈ S ⊓ L₂ := Subgroup.mem_subgroupOf.mp hx'
    have hy'NS₂ : (y' : G) ∈ N ⊓ (S ⊓ L₂) := Subgroup.mem_subgroupOf.mp hy'
    rw [← hπ_conj x' y']
    refine hNbar_mem (x' * y' * x'⁻¹) ⟨?_, ?_⟩
    · obtain ⟨u₀, hu₀, o, ho, hx'eq⟩ := exists_mul_inf_oddGen hK hs hx'S₂
      have hoN : o ∈ N := hEN (pCoreOf_le_ballStab hs ho)
      have h1 : o * (y' : G) * o⁻¹ ∈ N :=
        N.mul_mem (N.mul_mem hoN hy'NS₂.1) (N.inv_mem hoN)
      have h2 : u₀ * (o * (y' : G) * o⁻¹) * u₀⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hUN hu₀) _).mp h1
      have heq : ((x' * y' * x'⁻¹ : ↥L₂) : G) =
          u₀ * (o * (y' : G) * o⁻¹) * u₀⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx'eq]
        group
      rw [heq]
      exact h2
    · have heq : ((x' * y' * x'⁻¹ : ↥L₂) : G) = (x' : G) * (y' : G) * (x' : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [heq]
      exact ⟨S.mul_mem (S.mul_mem hx'S₂.1 hy'NS₂.2.1) (S.inv_mem hx'S₂.1),
        L₂.mul_mem (L₂.mul_mem hx'S₂.2 hy'NS₂.2.2) (L₂.inv_mem hx'S₂.2)⟩
  have hoddnorm : ∀ d ∈ Subgroup.normalizer
        ((P : Subgroup (oTwoQuot ↥L₂)) : Set (oTwoQuot ↥L₂)),
      Odd (orderOf d) → ∀ y ∈ Nbar, d * y * d⁻¹ ∈ Nbar := by
    intro d hd hdodd y hy
    obtain ⟨d', hd'odd, hd'eq⟩ :=
      exists_odd_lift_surjective π (QuotientGroup.mk'_surjective _) hdodd
    have hd'P₁ : (d' : G) ∈ P₁ L₁ L₂ S :=
      (RigidLocalOf.mk_mem_normalizer_iff hs hP d').mp (by rw [hd'eq]; exact hd)
    have hd'L₂ : (d' : G) ∈ L₂ := d'.2
    have hd'N : (d' : G) ∈ Subgroup.normalizer (N : Set G) := by
      refine hodd (d' : G) ⟨?_, ?_⟩ ?_
      · rw [stab_γ₀_eq hs]
        exact Subgroup.mem_sup_left hd'L₂
      · rw [stab_γ₁_eq hs]
        exact hd'P₁
      · rw [Subgroup.orderOf_coe]
        exact hd'odd
    have hd'S₂ : (d' : G) ∈ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) :=
      (mem_P₁_iff hs hd'L₂).mp hd'P₁
    rw [hNbar] at hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have hy'NS₂ : (y' : G) ∈ N ⊓ (S ⊓ L₂) := Subgroup.mem_subgroupOf.mp hy'
    rw [← hd'eq, ← hπ_conj d' y']
    refine hNbar_mem (d' * y' * d'⁻¹) ⟨?_, ?_⟩
    · have heq : ((d' * y' * d'⁻¹ : ↥L₂) : G) = (d' : G) * (y' : G) * (d' : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [heq]
      exact (Subgroup.mem_normalizer_iff.mp hd'N (y' : G)).mp hy'NS₂.1
    · have heq : ((d' * y' * d'⁻¹ : ↥L₂) : G) = (d' : G) * (y' : G) * (d' : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [heq]
      exact (Subgroup.mem_normalizer_iff.mp hd'S₂ (y' : G)).mp hy'NS₂.2
  rcases hT.trich P Nbar hle hnormal hoddnorm with hbot | htop | hthird
  ·
    left
    intro n hn
    obtain ⟨m, hm, e, he, rfl⟩ := decomp n hn
    have hmL₂ : m ∈ L₂ := hm.2.2
    have hπm : π ⟨m, hmL₂⟩ = 1 := by
      have h : π ⟨m, hmL₂⟩ ∈ Nbar := hNbar_mem ⟨m, hmL₂⟩ hm
      rw [hbot] at h
      simpa using h
    have hmE : m ∈ ballStab 1 ν₀ :=
      pCoreOf_le_ballStab hs ((hπ_one ⟨m, hmL₂⟩).mp hπm)
    exact (ballStab 1 ν₀).mul_mem hmE he
  ·
    right; left
    intro u hu
    have huS₂ : u ∈ S ⊓ L₂ := hU_le_S₂ hu
    have huL₂ : u ∈ L₂ := huS₂.2
    have huNbar : π ⟨u, huL₂⟩ ∈ Nbar := by
      rw [htop]
      exact hP_mem ⟨u, huL₂⟩ huS₂
    rw [hNbar] at huNbar
    obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp huNbar
    have hmNS₂ : (m : G) ∈ N ⊓ (S ⊓ L₂) := Subgroup.mem_subgroupOf.mp hm
    have hker : ((m⁻¹ * ⟨u, huL₂⟩ : ↥L₂) : G) ∈ pCoreOf 2 L₂ := by
      refine (hπ_one _).mp ?_
      rw [map_mul, map_inv, hmeq]
      exact inv_mul_cancel _
    have h1 : (m : G)⁻¹ * u ∈ N := hEN (pCoreOf_le_ballStab hs (by simpa using hker))
    have heq : u = (m : G) * ((m : G)⁻¹ * u) := by group
    rw [heq]
    exact N.mul_mem hmNS₂.1 h1
  ·
    right; right
    obtain ⟨hcent, hcom, hsq, hnonab⟩ := hthird
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn u hu
      obtain ⟨m, hm, e, he, rfl⟩ := decomp n hn
      have hmL₂ : m ∈ L₂ := hm.2.2
      have huS₂ : u ∈ S ⊓ L₂ := hU_le_S₂ hu
      have huL₂ : u ∈ L₂ := huS₂.2
      have hcomm_mu : π ((⟨m, hmL₂⟩ : ↥L₂) * ⟨u, huL₂⟩ * ⟨m, hmL₂⟩⁻¹ *
          ⟨u, huL₂⟩⁻¹) = 1 := by
        rw [hπ_comm]
        exact hcent _ (hNbar_mem ⟨m, hmL₂⟩ hm) _ (hP_mem _ huS₂)
      have hmuE : m * u * m⁻¹ * u⁻¹ ∈ ballStab 1 ν₀ := by
        have hz := pCoreOf_le_ballStab hs ((hπ_one _).mp hcomm_mu)
        simpa using hz
      have heu : e * u * e⁻¹ * u⁻¹ ∈ ballStab 1 ν₀ := by
        have h2 : u * e⁻¹ * u⁻¹ ∈ ballStab 1 ν₀ :=
          (Subgroup.mem_normalizer_iff.mp (hS₂_norm huS₂) e⁻¹).mp
            ((ballStab 1 ν₀).inv_mem he)
        have h3 : e * u * e⁻¹ * u⁻¹ = e * (u * e⁻¹ * u⁻¹) := by group
        rw [h3]
        exact (ballStab 1 ν₀).mul_mem he h2
      have hconj : m * (e * u * e⁻¹ * u⁻¹) * m⁻¹ ∈ ballStab 1 ν₀ :=
        (Subgroup.mem_normalizer_iff.mp (hS₂_norm hm.2) _).mp heu
      have hprod : (m * (e * u * e⁻¹ * u⁻¹) * m⁻¹) * (m * u * m⁻¹ * u⁻¹) ∈
          ballStab 1 ν₀ := (ballStab 1 ν₀).mul_mem hconj hmuE
      have heq : (m * e) * u * (m * e)⁻¹ * u⁻¹ =
          (m * (e * u * e⁻¹ * u⁻¹) * m⁻¹) * (m * u * m⁻¹ * u⁻¹) := by group
      rw [heq]
      exact hprod
    · intro a ha b hb
      have haS₂ : a ∈ S ⊓ L₂ := hU_le_S₂ ha
      have hbS₂ : b ∈ S ⊓ L₂ := hU_le_S₂ hb
      have haL₂ : a ∈ L₂ := haS₂.2
      have hbL₂ : b ∈ L₂ := hbS₂.2
      have hcomm_ab : π ((⟨a, haL₂⟩ : ↥L₂) * ⟨b, hbL₂⟩ * ⟨a, haL₂⟩⁻¹ *
          ⟨b, hbL₂⟩⁻¹) ∈ Nbar := by
        rw [hπ_comm]
        exact hcom _ (hP_mem _ haS₂) _ (hP_mem _ hbS₂)
      rw [hNbar] at hcomm_ab
      obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hcomm_ab
      have hmNS₂ : (m : G) ∈ N ⊓ (S ⊓ L₂) := Subgroup.mem_subgroupOf.mp hm
      have hker : ((m⁻¹ * (⟨a, haL₂⟩ * ⟨b, hbL₂⟩ * ⟨a, haL₂⟩⁻¹ *
          ⟨b, hbL₂⟩⁻¹) : ↥L₂) : G) ∈ pCoreOf 2 L₂ := by
        refine (hπ_one _).mp ?_
        rw [map_mul, map_inv, hmeq]
        exact inv_mul_cancel _
      have h1 : (m : G)⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ N :=
        hEN (pCoreOf_le_ballStab hs (by simpa using hker))
      have heq : a * b * a⁻¹ * b⁻¹ = (m : G) * ((m : G)⁻¹ * (a * b * a⁻¹ * b⁻¹)) :=
        by group
      rw [heq]
      exact N.mul_mem hmNS₂.1 h1
    · intro n hn
      obtain ⟨m, hm, e, he, rfl⟩ := decomp n hn
      have hmL₂ : m ∈ L₂ := hm.2.2
      have hmm : ((⟨m, hmL₂⟩ * ⟨m, hmL₂⟩ : ↥L₂) : G) ∈ pCoreOf 2 L₂ :=
        (hπ_one _).mp (by rw [map_mul]; exact hsq _ (hNbar_mem ⟨m, hmL₂⟩ hm))
      have hmmE : m * m ∈ ballStab 1 ν₀ := by
        have hz := pCoreOf_le_ballStab hs hmm
        simpa using hz
      have hmE : m⁻¹ * e * m ∈ ballStab 1 ν₀ := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ (hS₂_norm hm.2)) e).mp he
        simpa using h
      have hmem2 : m⁻¹ * e * m * e ∈ ballStab 1 ν₀ :=
        (ballStab 1 ν₀).mul_mem hmE he
      have heq : (m * e) * (m * e) = (m * m) * (m⁻¹ * e * m * e) := by group
      rw [heq]
      exact (ballStab 1 ν₀).mul_mem hmmE hmem2
    ·
      obtain ⟨abar, habar, bbar, hbbar, ybar, hybar⟩ := hnonab
      rw [hP] at habar hbbar
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp habar
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hbbar
      have ha'S₂ : (a' : G) ∈ S ⊓ L₂ := Subgroup.mem_subgroupOf.mp ha'
      have hb'S₂ : (b' : G) ∈ S ⊓ L₂ := Subgroup.mem_subgroupOf.mp hb'
      obtain ⟨a, haU, o, ho, haeq⟩ := exists_mul_inf_oddGen hK hs ha'S₂
      obtain ⟨b, hbU, o', ho', hbeq⟩ := exists_mul_inf_oddGen hK hs hb'S₂
      have haL₂ : a ∈ L₂ := MS93.oddGen_le L₂ haU.2
      have hbL₂ : b ∈ L₂ := MS93.oddGen_le L₂ hbU.2
      have hπa : π ⟨a, haL₂⟩ = π a' := by
        have hsplit : a' = ⟨a, haL₂⟩ * ⟨o, pCoreOf_le 2 L₂ ho⟩ := by
          apply Subtype.ext
          simpa using haeq
        rw [hsplit, map_mul, (hπ_one ⟨o, pCoreOf_le 2 L₂ ho⟩).mpr ho, mul_one]
      have hπb : π ⟨b, hbL₂⟩ = π b' := by
        have hsplit : b' = ⟨b, hbL₂⟩ * ⟨o', pCoreOf_le 2 L₂ ho'⟩ := by
          apply Subtype.ext
          simpa using hbeq
        rw [hsplit, map_mul, (hπ_one ⟨o', pCoreOf_le 2 L₂ ho'⟩).mpr ho', mul_one]
      refine ⟨a, haU, b, hbU, ?_⟩
      intro hEab
      have hEab' : a * b * a⁻¹ * b⁻¹ ∈ ballStab 1 ν₀ := hEab
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L₂) ybar
      have hyP₁ : (y : G)⁻¹ * (a * b * a⁻¹ * b⁻¹) * y ∈ P₁ L₁ L₂ S :=
        RigidLocalOf.conj_mem_P₁_of_mem_ballStab hs hEab' y.2
      have hz : ((y⁻¹ * (⟨a, haL₂⟩ * ⟨b, hbL₂⟩ * ⟨a, haL₂⟩⁻¹ * ⟨b, hbL₂⟩⁻¹) *
          y : ↥L₂) : G) ∈ P₁ L₁ L₂ S := by
        simpa using hyP₁
      have hz' : π (y⁻¹ * (⟨a, haL₂⟩ * ⟨b, hbL₂⟩ * ⟨a, haL₂⟩⁻¹ * ⟨b, hbL₂⟩⁻¹) *
          y) ∈ Subgroup.normalizer
            ((P : Subgroup (oTwoQuot ↥L₂)) : Set (oTwoQuot ↥L₂)) :=
        (RigidLocalOf.mk_mem_normalizer_iff hs hP _).mpr hz
      have hπa' : (QuotientGroup.mk' (pCore 2 ↥L₂)) a' =
          (QuotientGroup.mk' (pCore 2 ↥L₂)) ⟨a, haL₂⟩ := by
        have h := hπa.symm
        rwa [hπ] at h
      have hπb' : (QuotientGroup.mk' (pCore 2 ↥L₂)) b' =
          (QuotientGroup.mk' (pCore 2 ↥L₂)) ⟨b, hbL₂⟩ := by
        have h := hπb.symm
        rwa [hπ] at h
      have heq : π (y⁻¹ * (⟨a, haL₂⟩ * ⟨b, hbL₂⟩ * ⟨a, haL₂⟩⁻¹ * ⟨b, hbL₂⟩⁻¹) *
            y) = ybar⁻¹ * (π a' * π b' * (π a')⁻¹ * (π b')⁻¹) * ybar := by
        rw [hπ]
        simp only [map_mul, map_inv, hy, hπa', hπb']
      rw [heq] at hz'
      exact hybar hz'

end BenderLocalOf

end CFSG.Quasithin.F112Crit

end
