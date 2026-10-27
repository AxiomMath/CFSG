module

public import CFSG.Quasithin.EmptyFaithful.S143JA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Seven

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.normalizer_Ac_le_kOf_sup_dOf {A : Subgroup G} {t : G} (hb : Concl18b T M A t)
    (hq : Concl19a T M) (hK : IsA6Block (kOf T M A) A) :
    Subgroup.normalizer (A : Set G) ≤ kOf T M A ⊔ dOf T M := by
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq hb
  have hle := c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hRK : rOf T M ≤ kOf T M (c.Ac hrW hrV hr2) := le_sup_left.trans hle
  have hUK : uOfL22 T M ≤ kOf T M (c.Ac hrW hrV hr2) := le_sup_right.trans hle
  have hKN := c.kOf_le_normalizer_Ac hrW hrV hr2
  have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp c.h1281
  intro n hn
  obtain ⟨z, hzZ, hz1, -⟩ := c.h1281.exists_zgen
  have hzA : z ∈ c.Ac hrW hrV hr2 :=
    c.VZ_le_Ac hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hzZ)
  have hnzA : n * z * n⁻¹ ∈ c.Ac hrW hrV hr2 := (Subgroup.mem_normalizer_iff.mp hn z).mp hzA
  have hnz1 : n * z * n⁻¹ ≠ 1 := by
    intro he
    apply hz1
    have : z = n⁻¹ * (n * z * n⁻¹) * n := by group
    rw [this, he]; group
  obtain ⟨k, hkK, hk⟩ := hK.exists_conj_of_ne_one hnzA hzA hnz1 hz1
  have hmN : k * n ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.mul_mem _ (hKN hkK) hn
  have hmH : k * n ∈ mcOf T := by
    apply c.mem_mcOf_of_comm hzZ hz1
    calc k * n * z = (k * (n * z * n⁻¹) * k⁻¹) * (k * n) := by group
      _ = z * (k * n) := by rw [hk]
  have hmNH : k * n ∈ mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := ⟨hmH, hmN⟩
  have hsyl := c.isSylowTwoOf_rq_inf_normalizer_Ac hrW hrV hr2
  have hNH : oTwoUpper (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) ⊔
      (rOf T M ⊔ qOf T) = mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := by
    have := sup_twoResidual_eq hsyl
    rw [F6.twoResidual_eq_oTwoUpper, sup_comm] at this
    exact this
  have hRQN : rOf T M ⊔ qOf T ≤ Subgroup.normalizer
      (oTwoUpper (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) : Set G) := fun x hx =>
    normalizer_le_normalizer_oTwoUpper _ (Subgroup.le_normalizer (hsyl.le hx))
  rw [← hNH] at hmNH
  obtain ⟨ω, hω, ρ, hρ, hωρ⟩ := (Lin2.mem_sup_iff_of_le_normalizer hRQN).1 hmNH
  have hQR : qOf T ≤ Subgroup.normalizer (rOf T M : Set G) := fun x hx =>
    c.T_le_normalizer_rOf' (hRQT ((le_sup_right : qOf T ≤ rOf T M ⊔ qOf T) hx))
  obtain ⟨r', hr', q, hqQ, hρrq⟩ := (Lin2.mem_sup_iff_of_le_normalizer hQR).1 hρ
  have hDN : dOf T M ≤ Subgroup.normalizer (uOfL22 T M : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2
  rw [hq.q_eq] at hqQ
  obtain ⟨u, hu, d, hd, hqud⟩ := (Lin2.mem_sup_iff_of_le_normalizer hDN).1 hqQ
  have hωK : ω ∈ kOf T M (c.Ac hrW hrV hr2) := (le_sup_left : oTwoUpper _ ≤ _) hω
  have hn_eq : n = (k⁻¹ * (ω * r' * u)) * d := by
    have h1 : k * n = ω * (r' * (u * d)) := by rw [hωρ, hρrq, hqud]
    calc n = k⁻¹ * (k * n) := by group
      _ = k⁻¹ * (ω * (r' * (u * d))) := by rw [h1]
      _ = (k⁻¹ * (ω * r' * u)) * d := by group
  rw [hn_eq]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem _ ((kOf T M _).inv_mem hkK)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hωK (hRK hr')) (hUK hu))) hd

theorem Counter.normalizer_Ac_eq_normalizer_kOf {A : Subgroup G} {t : G} (hb : Concl18b T M A t)
    (hq : Concl19a T M) (hK : IsA6Block (kOf T M A) A) :
    Subgroup.normalizer (A : Set G) = Subgroup.normalizer (kOf T M A : Set G) := by
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq hb
  apply le_antisymm
  · intro n hn
    have hKD := c.normalizer_Ac_le_kOf_sup_dOf hb hq hK hn
    exact (sup_le Subgroup.le_normalizer (c.dOf_le_normalizer_kOf hrW hrV hr2)) hKD
  · intro n hn
    have := normalizer_le_normalizer_pCoreOf 2 (kOf T M (c.Ac hrW hrV hr2)) hn
    rwa [← hK.2.1] at this

end Seven

end S143

end CFSG.Quasithin
