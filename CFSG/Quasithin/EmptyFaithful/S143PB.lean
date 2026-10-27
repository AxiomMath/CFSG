module

public import CFSG.Quasithin.EmptyFaithful.S143PA
public import CFSG.Quasithin.EmptyFaithful.S143ND

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

open A6Model

section Conj

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)

include hS hP in
theorem psiA_conj_d {d : G} (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
    (hcd : cmat z a r r1 d = Tz) {e : G} (he : e ∈ c.Ac hrW hrV hr2) :
    psiA cm z a r r1 (d * e * d⁻¹) = n6Act s (psiA cm z a r r1 e) :=
  psiA_conj hS.basis hdN he (σ := s) fun w => by
    rw [hcd]
    exact psi_intertwine hP.conf.s_eq w

include hS hM hP in
theorem q_conj_d {d : G} (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
    (hcd : cmat z a r r1 d = Tz) {k : G} (hk : k ∈ kOf T M (c.Ac hrW hrV hr2))
    (hdk : d * k * d⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2)) :
    (hM.q ⟨d * k * d⁻¹, hdk⟩ : Equiv.Perm (Fin 6)) = s * (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)) * s⁻¹ := by
  have hB := hS.basis
  have hKN := c.kOf_le_normalizer_Ac hrW hrV hr2
  have hs2 : s * s = 1 := hP.conf.s_sq
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hss : ∀ b : N6, n6Act s (n6Act s b) = b := fun b => by
    rw [← MulAut.mul_apply, ← map_mul, hs2, map_one]; rfl
  refine perm_eq_of_n6Act_eq fun b => ?_
  obtain ⟨e, he, rfl⟩ := psiA_surj hB hM.inj b
  have hdinvN : d⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := (Subgroup.normalizer _).inv_mem hdN
  have he₁ : d⁻¹ * e * d ∈ c.Ac hrW hrV hr2 := by
    have := (Subgroup.mem_normalizer_iff.mp hdinvN e).mp he
    simpa using this
  have hψe₁ : psiA cm z a r r1 (d⁻¹ * e * d) = n6Act s (psiA cm z a r r1 e) := by
    have h1 := psiA_conj_d hS hP hdN hcd he₁
    have e1 : d * (d⁻¹ * e * d) * d⁻¹ = e := by group
    rw [e1] at h1
    rw [h1, hss]
  have he₂ : k * (d⁻¹ * e * d) * k⁻¹ ∈ c.Ac hrW hrV hr2 :=
    (Subgroup.mem_normalizer_iff.mp (hKN hk) _).mp he₁
  have hψe₂ : psiA cm z a r r1 (k * (d⁻¹ * e * d) * k⁻¹) =
      n6Act (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)) (psiA cm z a r r1 (d⁻¹ * e * d)) :=
    psiA_conj hB (hKN hk) he₁ (σ := (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)))
      (fun w => hM.q_act ⟨k, hk⟩ w)
  have hψe₃ : psiA cm z a r r1 (d * (k * (d⁻¹ * e * d) * k⁻¹) * d⁻¹) =
      n6Act s (psiA cm z a r r1 (k * (d⁻¹ * e * d) * k⁻¹)) := psiA_conj_d hS hP hdN hcd he₂
  have hψdk : psiA cm z a r r1 ((d * k * d⁻¹) * e * (d * k * d⁻¹)⁻¹) =
      n6Act (hM.q ⟨d * k * d⁻¹, hdk⟩ : Equiv.Perm (Fin 6)) (psiA cm z a r r1 e) :=
    psiA_conj hB (hKN hdk) he (σ := (hM.q ⟨d * k * d⁻¹, hdk⟩ : Equiv.Perm (Fin 6)))
      (fun w => hM.q_act ⟨d * k * d⁻¹, hdk⟩ w)
  have e3 : (d * k * d⁻¹) * e * (d * k * d⁻¹)⁻¹ = d * (k * (d⁻¹ * e * d) * k⁻¹) * d⁻¹ := by group
  rw [← hψdk, e3, hψe₃, hψe₂, hψe₁, hsinv]
  simp only [MulAut.mul_apply, map_mul]

end Conj

section Sq

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVr : ∀ σ ∈ Vr, ∃ ρ' ∈ rOf T M, mm cm (matOf6 σ) = mm (cmat z a r r1 ρ') cm)
  (hΓ : Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) = c.Ac hrW hrV hr2)
  (hAAt : rOf T M = c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t)

theorem conj_le_rOf (hAAt : rOf T M = c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t) :
    conjSubgroup (c.Ac hrW hrV hr2) t ≤ rOf T M := by
  rw [hAAt]
  exact le_sup_right

theorem exists_notComm_conj (htT : t ∈ T) {d : G} (hd : d ∈ dOf T M)
    (hdZ : d ∉ quasithinOmegaOneCenter T)
    (hΓ : Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) = c.Ac hrW hrV hr2)
    (hz1 : z ≠ 1) (hzZ : z ∈ quasithinOmegaOneCenter T) :
    ∃ ρ ∈ conjSubgroup (c.Ac hrW hrV hr2) t, d * ρ ≠ ρ * d := by
  by_contra hcon
  push Not at hcon
  have htH : t ∈ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H htT
  have hdt : t * d * t⁻¹ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun a' ha' => ?_
    have hw : t⁻¹ * a' * t ∈ conjSubgroup (c.Ac hrW hrV hr2) t :=
      mem_conjSubgroup_iff.mpr (by simpa [mul_assoc] using ha')
    have h1 := hcon _ hw
    calc a' * (t * d * t⁻¹) = t * ((t⁻¹ * a' * t) * d) * t⁻¹ := by group
      _ = t * (d * (t⁻¹ * a' * t)) * t⁻¹ := by rw [← h1]
      _ = (t * d * t⁻¹) * a' := by group
  rw [hΓ] at hdt
  have htdD : t * d * t⁻¹ ∈ dOf T M := c.conj_mem_dOf htH hd
  have hzt := D_inf_Ac_le_Z htdD hdt
  apply hdZ
  rcases c.mem_Z_cases hzZ hz1 hzt with h | h
  · have : d = 1 := by
      calc d = t⁻¹ * (t * d * t⁻¹) * t := by group
        _ = t⁻¹ * 1 * t := by rw [h]
        _ = 1 := by group
    rw [this]
    exact (quasithinOmegaOneCenter T).one_mem
  · have hzt' : t * z = z * t := mem_mcOf_comm htH hzZ
    have : d = z := by
      calc d = t⁻¹ * (t * d * t⁻¹) * t := by group
        _ = t⁻¹ * z * t := by rw [h]
        _ = z := by rw [mul_assoc, ← hzt']; group
    rw [this]
    exact hzZ

theorem conj_le_kOf (hAAt : rOf T M = c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t) :
    conjSubgroup (c.Ac hrW hrV hr2) t ≤ kOf T M (c.Ac hrW hrV hr2) :=
  (conj_le_rOf hAAt).trans (le_sup_left.trans (c.rOf_sup_uOfL22_le_kOf hrW hrV hr2))

include hS htT htRQ hM hP in
theorem q_commutes_s {d : G} (hd : d ∈ dOf T M)
    (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) (hcd : cmat z a r r1 d = Tz)
    {ρ : G} (hρR : ρ ∈ rOf T M) (hρK : ρ ∈ kOf T M (c.Ac hrW hrV hr2)) :
    (hM.q ⟨ρ, hρK⟩ : Equiv.Perm (Fin 6)) * s = s * (hM.q ⟨ρ, hρK⟩ : Equiv.Perm (Fin 6)) := by
  have hdKN := c.dOf_le_normalizer_kOf hrW hrV hr2 hd
  have hcZ := c.dOf_commutator_mem hd hρR
  have hz1 := hS.z_ne
  have hcA : d * ρ * d⁻¹ * ρ⁻¹ ∈ c.Ac hrW hrV hr2 := by
    rcases c.mem_Z_cases hS.z_mem hz1 hcZ with h | h
    · rw [h]; exact (c.Ac hrW hrV hr2).one_mem
    · rw [h]; exact hS.z_A
  have hcK : d * ρ * d⁻¹ * ρ⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2) :=
    (c.Ac_le_rOf hrW hrV hr2).trans (le_sup_left.trans (c.rOf_sup_uOfL22_le_kOf hrW hrV hr2)) hcA
  have hdk : d * ρ * d⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2) := (Subgroup.mem_normalizer_iff.mp hdKN ρ).mp hρK
  have h1 := q_conj_d hS hM hP hdN hcd hρK hdk
  have h2 : (⟨d * ρ * d⁻¹, hdk⟩ : ↥(kOf T M (c.Ac hrW hrV hr2))) =
      ⟨d * ρ * d⁻¹ * ρ⁻¹, hcK⟩ * ⟨ρ, hρK⟩ := Subtype.ext (by
    show d * ρ * d⁻¹ = d * ρ * d⁻¹ * ρ⁻¹ * ρ
    group)
  have h3 : hM.q ⟨d * ρ * d⁻¹ * ρ⁻¹, hcK⟩ = 1 := (hM.q_eq_one_iff htT htRQ _).mpr hcA
  have h4 : (hM.q ⟨d * ρ * d⁻¹, hdk⟩ : Equiv.Perm (Fin 6)) = (hM.q ⟨ρ, hρK⟩ : Equiv.Perm (Fin 6)) := by
    rw [h2, map_mul, h3, one_mul]
  rw [h4] at h1
  calc (hM.q ⟨ρ, hρK⟩ : Equiv.Perm (Fin 6)) * s = (s * (hM.q ⟨ρ, hρK⟩ : Equiv.Perm (Fin 6)) * s⁻¹) * s := by
        rw [← h1]
    _ = s * (hM.q ⟨ρ, hρK⟩ : Equiv.Perm (Fin 6)) := by group

include hS htT htRQ hM hP hVr hAAt in
theorem exists_swap_rho {d : G} (hd : d ∈ dOf T M)
    (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) (hcd : cmat z a r r1 d = Tz)
    {p₀ q₀ : Fin 6} (hsw : s = Equiv.swap p₀ q₀) (hp : p₀ ≠ q₀) :
    ∃ (ρ : G) (hρ : ρ ∈ conjSubgroup (c.Ac hrW hrV hr2) t),
      (hM.q ⟨ρ, conj_le_kOf hAAt hρ⟩ : Equiv.Perm (Fin 6)) p₀ = q₀ := by
  have hsp : s p₀ ≠ p₀ := by rw [hsw, Equiv.swap_apply_left]; exact hp.symm
  obtain ⟨σ₁, hσ₁Vr, hσ₁p⟩ := hP.rMoves p₀ hsp
  obtain ⟨ρ', hρ'R, hmat⟩ := hVr σ₁ hσ₁Vr
  have hRK : rOf T M ≤ kOf T M (c.Ac hrW hrV hr2) :=
    le_sup_left.trans (c.rOf_sup_uOfL22_le_kOf hrW hrV hr2)
  have hρ'K := hRK hρ'R
  have hq' : (hM.q ⟨ρ', hρ'K⟩ : Equiv.Perm (Fin 6)) = σ₁ :=
    perm_eq_of_act hM.inj (Equiv.Perm.mem_alternatingGroup.mp (hM.q _).2) (hP.vr_sign σ₁ hσ₁Vr)
      fun w' => by
        rw [hM.q_act]
        exact (psi_intertwine hmat w').symm
  have hAtN : conjSubgroup (c.Ac hrW hrV hr2) t ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (conj_le_rOf hAAt).trans (c.rOf_le_normalizer_Ac hrW hrV hr2)
  have hρ'mem : ρ' ∈ c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t := by
    rw [← hAAt]; exact hρ'R
  obtain ⟨a₁, ha₁, ρ₁, hρ₁, hρ'eq⟩ := (Lin2.mem_sup_iff_of_le_normalizer hAtN).1 hρ'mem
  refine ⟨ρ₁, hρ₁, ?_⟩
  have hρ₁K := conj_le_kOf hAAt hρ₁
  have ha₁K : a₁ ∈ kOf T M (c.Ac hrW hrV hr2) :=
    (c.Ac_le_rOf hrW hrV hr2).trans hRK ha₁
  have hqρ₁ : (hM.q ⟨ρ₁, hρ₁K⟩ : Equiv.Perm (Fin 6)) = σ₁ := by
    have h0 : (⟨ρ', hρ'K⟩ : ↥(kOf T M (c.Ac hrW hrV hr2))) = ⟨a₁, ha₁K⟩ * ⟨ρ₁, hρ₁K⟩ :=
      Subtype.ext hρ'eq
    have h1 : hM.q ⟨ρ', hρ'K⟩ = hM.q ⟨a₁, ha₁K⟩ * hM.q ⟨ρ₁, hρ₁K⟩ := by rw [h0, map_mul]
    rw [(hM.q_eq_one_iff htT htRQ ⟨a₁, ha₁K⟩).mpr ha₁, one_mul] at h1
    rw [← hq', h1]
  have hcomm := q_commutes_s hS htT htRQ hM hP hd hdN hcd (conj_le_rOf hAAt hρ₁) hρ₁K
  rw [hqρ₁, hsw] at hcomm
  rw [hqρ₁]
  rcases swap_comm_cases' p₀ q₀ σ₁ hp hcomm with h | h
  · exact absurd h.1 hσ₁p
  · exact h.1

include hS htT htRQ hM hP hVr hAAt in
theorem exists_good_rho
    {d : G} (hd : d ∈ dOf T M) (hdZ : d ∉ quasithinOmegaOneCenter T)
    (hΓ : Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) = c.Ac hrW hrV hr2)
    (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) (hcd : cmat z a r r1 d = Tz)
    {p₀ q₀ : Fin 6} (hsw : s = Equiv.swap p₀ q₀) (hp : p₀ ≠ q₀) :
    ∃ (ρ : G) (hρ : ρ ∈ conjSubgroup (c.Ac hrW hrV hr2) t), d * ρ * d⁻¹ * ρ⁻¹ = z ∧
      (hM.q ⟨ρ, conj_le_kOf hAAt hρ⟩ : Equiv.Perm (Fin 6)) p₀ = q₀ := by
  have hz1 := hS.z_ne
  have hzZ := hS.z_mem
  obtain ⟨ρ₀, hρ₀, hρ₀ne⟩ := exists_notComm_conj htT hd hdZ hΓ hz1 hzZ
  obtain ⟨ρ₁, hρ₁, hq₁⟩ := exists_swap_rho hS htT htRQ hM hP hVr hAAt hd hdN hcd hsw hp
  have hcom : ∀ ρ ∈ conjSubgroup (c.Ac hrW hrV hr2) t,
      d * ρ * d⁻¹ * ρ⁻¹ = 1 ∨ d * ρ * d⁻¹ * ρ⁻¹ = z := fun ρ hρ =>
    c.mem_Z_cases hzZ hz1 (c.dOf_commutator_mem hd (conj_le_rOf hAAt hρ))
  have hρ₀z : d * ρ₀ * d⁻¹ * ρ₀⁻¹ = z := by
    rcases hcom ρ₀ hρ₀ with h | h
    · exfalso
      apply hρ₀ne
      calc d * ρ₀ = (d * ρ₀ * d⁻¹ * ρ₀⁻¹) * (ρ₀ * d) := by group
        _ = ρ₀ * d := by rw [h, one_mul]
    · exact h
  have hρ₀K := conj_le_kOf hAAt hρ₀
  have hρ₁K := conj_le_kOf hAAt hρ₁
  have hcomm₀ := q_commutes_s hS htT htRQ hM hP hd hdN hcd (conj_le_rOf hAAt hρ₀) hρ₀K
  rw [hsw] at hcomm₀
  rcases swap_comm_cases' p₀ q₀ _ hp hcomm₀ with h0 | h0
  · by_cases hc1 : d * ρ₁ * d⁻¹ * ρ₁⁻¹ = z
    · exact ⟨ρ₁, hρ₁, hc1, hq₁⟩
    · have hc1' : d * ρ₁ * d⁻¹ * ρ₁⁻¹ = 1 := (hcom ρ₁ hρ₁).resolve_right hc1
      have hmem : ρ₀ * ρ₁ ∈ conjSubgroup (c.Ac hrW hrV hr2) t :=
        (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hρ₀ hρ₁
      refine ⟨ρ₀ * ρ₁, hmem, ?_, ?_⟩
      · calc d * (ρ₀ * ρ₁) * d⁻¹ * (ρ₀ * ρ₁)⁻¹
            = (d * ρ₀ * d⁻¹ * ρ₀⁻¹) * (ρ₀ * (d * ρ₁ * d⁻¹ * ρ₁⁻¹) * ρ₀⁻¹) := by group
          _ = z * (ρ₀ * 1 * ρ₀⁻¹) := by rw [hρ₀z, hc1']
          _ = z := by group
      · have h0' : (⟨ρ₀ * ρ₁, conj_le_kOf hAAt hmem⟩ : ↥(kOf T M (c.Ac hrW hrV hr2))) =
            ⟨ρ₀, hρ₀K⟩ * ⟨ρ₁, hρ₁K⟩ := rfl
        have h1 : (hM.q ⟨ρ₀ * ρ₁, conj_le_kOf hAAt hmem⟩ : Equiv.Perm (Fin 6)) =
            (hM.q ⟨ρ₀, hρ₀K⟩ : Equiv.Perm (Fin 6)) * (hM.q ⟨ρ₁, hρ₁K⟩ : Equiv.Perm (Fin 6)) := by
          rw [h0', map_mul]
          rfl
        rw [h1, Equiv.Perm.mul_apply, hq₁, h0.2]
  · exact ⟨ρ₀, hρ₀, hρ₀z, h0.1⟩

include hS hM hP hAAt in
theorem sq_core {d : G} (hd : d ∈ dOf T M)
    (hΓ : Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) = c.Ac hrW hrV hr2)
    (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) (hcd : cmat z a r r1 d = Tz)
    (hdd : d * d = 1 ∨ d * d = z) {p₀ q₀ : Fin 6} (hsw : s = Equiv.swap p₀ q₀) (hp : p₀ ≠ q₀)
    {ρ : G} (hρ : ρ ∈ conjSubgroup (c.Ac hrW hrV hr2) t) (hρd : d * ρ * d⁻¹ * ρ⁻¹ = z)
    (hρp : (hM.q ⟨ρ, conj_le_kOf hAAt hρ⟩ : Equiv.Perm (Fin 6)) p₀ = q₀) :
    d * d = z := by
  classical
  have hB := hS.basis
  have hz2 : z * z = 1 := c.sq_Ac hrW hrV hr2 hS.z_A
  have hz1 := hS.z_ne
  have hzZ := hS.z_mem
  have hzA := hS.z_A
  have hρK := conj_le_kOf hAAt hρ
  have hρR := conj_le_rOf hAAt hρ
  have hKN := c.kOf_le_normalizer_Ac hrW hrV hr2
  have hρN : ρ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := hKN hρK
  have hρH : ρ ∈ mcOf T := rOf_le_mcOf c hρR
  have hdH : d ∈ mcOf T := pCoreOf_le 2 _ hd.1
  have hρ2 : ρ * ρ = 1 := by
    have h := c.sq_Ac hrW hrV hr2 (mem_conjSubgroup_iff.mp hρ)
    calc ρ * ρ = t⁻¹ * ((t * ρ * t⁻¹) * (t * ρ * t⁻¹)) * t := by group
      _ = 1 := by rw [h]; group
  set σ : Equiv.Perm (Fin 6) := (hM.q ⟨ρ, hρK⟩ : Equiv.Perm (Fin 6)) with hσdef
  have hσsign : σ.sign = 1 := Equiv.Perm.mem_alternatingGroup.mp (hM.q _).2
  have hσ2 : σ * σ = 1 := by
    have h1 : hM.q ⟨ρ, hρK⟩ * hM.q ⟨ρ, hρK⟩ = 1 := by
      rw [← map_mul]
      have : (⟨ρ, hρK⟩ : ↥(kOf T M (c.Ac hrW hrV hr2))) * ⟨ρ, hρK⟩ = 1 := Subtype.ext hρ2
      rw [this, map_one]
    exact congrArg Subtype.val h1
  obtain ⟨a₁, b₁, hab, hsσ⟩ := even_invol_swap p₀ q₀ σ hp hσsign hσ2 hρp
  obtain ⟨τ, hτsign, hτ⟩ := exists_even_conj_swap p₀ q₀ a₁ b₁ hp hab
  obtain ⟨⟨k, hk⟩, hkq⟩ := hM.q_surjective ⟨τ, Equiv.Perm.mem_alternatingGroup.mpr hτsign⟩
  have hkτ : (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)) = τ := congrArg Subtype.val hkq
  have hkN : k ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := hKN hk
  have hτs : τ * s * τ⁻¹ = s * σ := by
    calc τ * s * τ⁻¹ = Equiv.swap a₁ b₁ := by rw [hsw]; exact hτ
      _ = s * σ := by rw [hsw]; exact hsσ.symm
  have hk'K : k⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2) := (kOf T M (c.Ac hrW hrV hr2)).inv_mem hk
  have hk'N : k⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := hKN hk'K
  have hqinv : (hM.q ⟨k⁻¹, hk'K⟩ : Equiv.Perm (Fin 6)) = τ⁻¹ := by
    have h0 : (⟨k⁻¹, hk'K⟩ : ↥(kOf T M (c.Ac hrW hrV hr2))) = (⟨k, hk⟩ : ↥(kOf T M (c.Ac hrW hrV hr2)))⁻¹ := rfl
    rw [h0, map_inv, Subgroup.coe_inv, hkτ]
  have hψg : ∀ e ∈ c.Ac hrW hrV hr2,
      psiA cm z a r r1 ((d * ρ) * e * (d * ρ)⁻¹) = n6Act (s * σ) (psiA cm z a r r1 e) := by
    intro e he
    have he₁ : ρ * e * ρ⁻¹ ∈ c.Ac hrW hrV hr2 := (Subgroup.mem_normalizer_iff.mp hρN e).mp he
    have h1 : psiA cm z a r r1 (ρ * e * ρ⁻¹) = n6Act σ (psiA cm z a r r1 e) :=
      psiA_conj hB hρN he (σ := σ) (fun w => hM.q_act ⟨ρ, hρK⟩ w)
    have h2 := psiA_conj_d hS hP hdN hcd he₁
    have e0 : (d * ρ) * e * (d * ρ)⁻¹ = d * (ρ * e * ρ⁻¹) * d⁻¹ := by group
    rw [e0, h2, h1, map_mul]
    rfl
  have hψk : ∀ e ∈ c.Ac hrW hrV hr2,
      psiA cm z a r r1 ((k * d * k⁻¹) * e * (k * d * k⁻¹)⁻¹) =
        n6Act (s * σ) (psiA cm z a r r1 e) := by
    intro e he
    have he₀ : k⁻¹ * e * k ∈ c.Ac hrW hrV hr2 := by
      have := (Subgroup.mem_normalizer_iff.mp hk'N e).mp he
      simpa using this
    have h0 : psiA cm z a r r1 (k⁻¹ * e * k) = n6Act τ⁻¹ (psiA cm z a r r1 e) := by
      have := psiA_conj hB hk'N he (σ := τ⁻¹) (fun w => by rw [← hqinv]; exact hM.q_act ⟨k⁻¹, hk'K⟩ w)
      simpa using this
    have h1 := psiA_conj_d hS hP hdN hcd he₀
    have he₃ : d * (k⁻¹ * e * k) * d⁻¹ ∈ c.Ac hrW hrV hr2 :=
      (Subgroup.mem_normalizer_iff.mp hdN _).mp he₀
    have h2 : psiA cm z a r r1 (k * (d * (k⁻¹ * e * k) * d⁻¹) * k⁻¹) =
        n6Act τ (psiA cm z a r r1 (d * (k⁻¹ * e * k) * d⁻¹)) :=
      psiA_conj hB hkN he₃ (σ := τ) (fun w => by rw [← hkτ]; exact hM.q_act ⟨k, hk⟩ w)
    have e0 : (k * d * k⁻¹) * e * (k * d * k⁻¹)⁻¹ = k * (d * (k⁻¹ * e * k) * d⁻¹) * k⁻¹ := by group
    rw [e0, h2, h1, h0, ← hτs, map_mul, map_mul]
    rfl
  have hdkN : k * d * k⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hkN hdN) hk'N
  have hgN : d * ρ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (Subgroup.normalizer _).mul_mem hdN hρN
  have hconj : ∀ e ∈ c.Ac hrW hrV hr2,
      (d * ρ) * e * (d * ρ)⁻¹ = (k * d * k⁻¹) * e * (k * d * k⁻¹)⁻¹ := by
    intro e he
    exact psiA_inj hB hM.inj ((Subgroup.mem_normalizer_iff.mp hgN e).mp he)
      ((Subgroup.mem_normalizer_iff.mp hdkN e).mp he) ((hψg e he).trans (hψk e he).symm)
  have ha₀ : (k * d * k⁻¹)⁻¹ * (d * ρ) ∈ c.Ac hrW hrV hr2 := by
    rw [← hΓ]
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have h := hconj e he
    calc e * ((k * d * k⁻¹)⁻¹ * (d * ρ))
        = (k * d * k⁻¹)⁻¹ * (((k * d * k⁻¹) * e * (k * d * k⁻¹)⁻¹) * (d * ρ)) := by group
      _ = (k * d * k⁻¹)⁻¹ * (((d * ρ) * e * (d * ρ)⁻¹) * (d * ρ)) := by rw [h]
      _ = ((k * d * k⁻¹)⁻¹ * (d * ρ)) * e := by group
  have hzd : d * z = z * d := mem_mcOf_comm hdH hzZ
  have hg2 : (d * ρ) * (d * ρ) = z * (d * d) := by
    have h1 : d * ρ = z * (ρ * d) := by
      calc d * ρ = (d * ρ * d⁻¹ * ρ⁻¹) * (ρ * d) := by group
        _ = z * (ρ * d) := by rw [hρd]
    have hρd' : ρ * d = z * (d * ρ) := by
      calc ρ * d = (z * z) * (ρ * d) := by rw [hz2, one_mul]
        _ = z * (z * (ρ * d)) := by group
        _ = z * (d * ρ) := by rw [← h1]
    calc (d * ρ) * (d * ρ) = d * (ρ * d) * ρ := by group
      _ = d * (z * (d * ρ)) * ρ := by rw [hρd']
      _ = (d * z) * d * (ρ * ρ) := by group
      _ = (z * d) * d * 1 := by rw [hzd, hρ2]
      _ = z * (d * d) := by group
  have hg2' : ∃ c₅ ∈ quasithinOmegaOneCenter T,
      (d * ρ) * (d * ρ) = k * ((d * d) * c₅) * k⁻¹ := by
    obtain ⟨a₀, ha₀def⟩ : ∃ a₀ : G, a₀ = (k * d * k⁻¹)⁻¹ * (d * ρ) := ⟨_, rfl⟩
    rw [← ha₀def] at ha₀
    have hg : d * ρ = (k * d * k⁻¹) * a₀ := by rw [ha₀def]; group
    obtain ⟨a', ha'def⟩ : ∃ a' : G, a' = k⁻¹ * a₀ * k := ⟨_, rfl⟩
    have ha'A : a' ∈ c.Ac hrW hrV hr2 := by
      have := (Subgroup.mem_normalizer_iff.mp hk'N a₀).mp ha₀
      rw [ha'def]
      simpa using this
    have ha'R : a' ∈ rOf T M := c.Ac_le_rOf hrW hrV hr2 ha'A
    have hd'D : d⁻¹ ∈ dOf T M := (dOf T M).inv_mem hd
    have hc₂ := c.dOf_commutator_mem hd'D ha'R
    refine ⟨d⁻¹ * a' * d⁻¹⁻¹ * a'⁻¹, hc₂, ?_⟩
    have ha'2 : a' * a' = 1 := c.sq_Ac hrW hrV hr2 ha'A
    have ha₀eq : a₀ = k * a' * k⁻¹ := by rw [ha'def]; group
    calc (d * ρ) * (d * ρ) = ((k * d * k⁻¹) * a₀) * ((k * d * k⁻¹) * a₀) := by rw [← hg]
      _ = k * (d * a' * d * a') * k⁻¹ := by rw [ha₀eq]; group
      _ = k * ((d * d) * ((d⁻¹ * a' * d⁻¹⁻¹ * a'⁻¹) * (a' * a'))) * k⁻¹ := by group
      _ = k * ((d * d) * (d⁻¹ * a' * d⁻¹⁻¹ * a'⁻¹)) * k⁻¹ := by rw [ha'2, mul_one]
  have hne : k * z * k⁻¹ ≠ z := by
    intro hkz
    have key : ∀ e ∈ c.Ac hrW hrV hr2, ∃ c₆ ∈ quasithinOmegaOneCenter T,
        ρ * e * ρ⁻¹ = c₆ * e := by
      intro e he
      have he₁ : ρ * e * ρ⁻¹ ∈ c.Ac hrW hrV hr2 := (Subgroup.mem_normalizer_iff.mp hρN e).mp he
      have he₀ : k⁻¹ * e * k ∈ c.Ac hrW hrV hr2 := by
        have := (Subgroup.mem_normalizer_iff.mp hk'N e).mp he
        simpa using this
      have hc₃ := c.dOf_commutator_mem hd (c.Ac_le_rOf hrW hrV hr2 he₁)
      have hc₄ := c.dOf_commutator_mem hd (c.Ac_le_rOf hrW hrV hr2 he₀)
      have hk4Z : k * (d * (k⁻¹ * e * k) * d⁻¹ * (k⁻¹ * e * k)⁻¹) * k⁻¹ ∈
          quasithinOmegaOneCenter T := by
        rcases c.mem_Z_cases hzZ hz1 hc₄ with h | h
        · rw [h]; simp
        · rw [h, hkz]; exact hzZ
      have hconje := hconj e he
      have e1 : (d * ρ) * e * (d * ρ)⁻¹ =
          (d * (ρ * e * ρ⁻¹) * d⁻¹ * (ρ * e * ρ⁻¹)⁻¹) * (ρ * e * ρ⁻¹) := by group
      have e2 : (k * d * k⁻¹) * e * (k * d * k⁻¹)⁻¹ =
          (k * (d * (k⁻¹ * e * k) * d⁻¹ * (k⁻¹ * e * k)⁻¹) * k⁻¹) * e := by group
      rw [e1, e2] at hconje
      refine ⟨(d * (ρ * e * ρ⁻¹) * d⁻¹ * (ρ * e * ρ⁻¹)⁻¹)⁻¹ *
        (k * (d * (k⁻¹ * e * k) * d⁻¹ * (k⁻¹ * e * k)⁻¹) * k⁻¹),
        (quasithinOmegaOneCenter T).mul_mem ((quasithinOmegaOneCenter T).inv_mem hc₃) hk4Z, ?_⟩
      calc ρ * e * ρ⁻¹ = (d * (ρ * e * ρ⁻¹) * d⁻¹ * (ρ * e * ρ⁻¹)⁻¹)⁻¹ *
            ((d * (ρ * e * ρ⁻¹) * d⁻¹ * (ρ * e * ρ⁻¹)⁻¹) * (ρ * e * ρ⁻¹)) := by group
        _ = (d * (ρ * e * ρ⁻¹) * d⁻¹ * (ρ * e * ρ⁻¹)⁻¹)⁻¹ *
            ((k * (d * (k⁻¹ * e * k) * d⁻¹ * (k⁻¹ * e * k)⁻¹) * k⁻¹) * e) := by rw [hconje]
        _ = ((d * (ρ * e * ρ⁻¹) * d⁻¹ * (ρ * e * ρ⁻¹)⁻¹)⁻¹ *
            (k * (d * (k⁻¹ * e * k) * d⁻¹ * (k⁻¹ * e * k)⁻¹) * k⁻¹)) * e := by group
    have hσne : σ ≠ 1 := by
      intro h
      rw [h] at hρp
      exact hp (by simpa using hρp)
    obtain ⟨b₁, b₂, h1, h2, h12⟩ := n6Comm_not_transvection σ hσsign hσne
    have hcomZ : ∀ b : N6, n6Comm σ b = 1 ∨ n6Comm σ b = psiA cm z a r r1 z := by
      intro b
      obtain ⟨e, he, rfl⟩ := psiA_surj hB hM.inj b
      obtain ⟨c₆, hc₆, hc⟩ := key e he
      have hc₆A : c₆ ∈ c.Ac hrW hrV hr2 := by
        rcases c.mem_Z_cases hzZ hz1 hc₆ with h | h
        · rw [h]; exact (c.Ac hrW hrV hr2).one_mem
        · rw [h]; exact hzA
      have hψ : n6Comm σ (psiA cm z a r r1 e) = psiA cm z a r r1 c₆ := by
        unfold n6Comm
        have h0 : n6Act σ (psiA cm z a r r1 e) = psiA cm z a r r1 (ρ * e * ρ⁻¹) :=
          (psiA_conj hB hρN he (σ := σ) (fun w => hM.q_act ⟨ρ, hρK⟩ w)).symm
        rw [h0, hc, psiA_mul hB hc₆A he, mul_inv_cancel_right]
      rcases c.mem_Z_cases hzZ hz1 hc₆ with h | h
      · left
        rw [hψ, h, psiA_one hB]
      · right
        rw [hψ, h]
    rcases hcomZ b₁ with h | h
    · exact h1 h
    rcases hcomZ b₂ with h' | h'
    · exact h2 h'
    exact h12 (h.trans h'.symm)
  obtain ⟨c₅, hc₅, hg2eq⟩ := hg2'
  have hdd' : d * d ∈ quasithinOmegaOneCenter T := by
    rcases hdd with h | h
    · rw [h]; exact (quasithinOmegaOneCenter T).one_mem
    · rw [h]; exact hzZ
  have hprodZ : (d * d) * c₅ ∈ quasithinOmegaOneCenter T :=
    (quasithinOmegaOneCenter T).mul_mem hdd' hc₅
  rcases hdd with h1 | h1
  · exfalso
    have hgz : (d * ρ) * (d * ρ) = z := by rw [hg2, h1, mul_one]
    rcases c.mem_Z_cases hzZ hz1 hprodZ with h | h
    · rw [h] at hg2eq
      have : (d * ρ) * (d * ρ) = 1 := by rw [hg2eq]; group
      rw [hgz] at this
      exact hz1 this
    · rw [h, hgz] at hg2eq
      exact hne hg2eq.symm
  · exact h1

include hS htT htRQ hM hP hVr hAAt in
theorem sq_eq_z_of_mem_dOf
    (hΓ : Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) = c.Ac hrW hrV hr2) {d : G}
    (hd : d ∈ dOf T M) (hdZ : d ∉ quasithinOmegaOneCenter T) : d * d = z := by
  have hB := hS.basis
  have hz1 := hS.z_ne
  have hzZ := hS.z_mem
  have hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) hd
  have hcd : cmat z a r r1 d = Tz := by
    rcases D_cmat hS hd with h | h
    · exfalso
      have h1 : d ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
        (hB.cmat_eq_one_iff_mem_centralizer hdN).mp h
      rw [hΓ] at h1
      exact hdZ (D_inf_Ac_le_Z hd h1)
    · exact h
  have hdd : d * d = 1 ∨ d * d = z := by
    have hdd1 : d * d ∈ dOf T M := (dOf T M).mul_mem hd hd
    have hc : cmat z a r r1 (d * d) = I4 := by
      rw [hB.cmat_mul hdN hdN, hcd, Tz_sq]
    have h1 : d * d ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
      (hB.cmat_eq_one_iff_mem_centralizer ((Subgroup.normalizer _).mul_mem hdN hdN)).mp hc
    rw [hΓ] at h1
    exact c.mem_Z_cases hzZ hz1 (D_inf_Ac_le_Z hdd1 h1)
  have hs1 : ∃ p₀, s p₀ ≠ p₀ := by
    by_contra hcon
    push Not at hcon
    have h0 : s = 1 := Equiv.ext hcon
    have h := hP.conf.s_sign
    rw [h0] at h
    exact absurd h (by decide)
  obtain ⟨p₀, hp₀⟩ := hs1
  have hsw : s = Equiv.swap p₀ (s p₀) := hP.swap p₀ hp₀
  obtain ⟨ρ, hρ, hρd, hρp⟩ := exists_good_rho hS htT htRQ hM hP hVr hAAt hd hdZ hΓ hdN hcd hsw
    (Ne.symm hp₀)
  exact sq_core hS hM hP hAAt hd hΓ hdN hcd hdd hsw (Ne.symm hp₀) hρ hρd hρp

include hS htT htRQ hM hP hVr hAAt in
theorem exists_cyclic_of_dOf_ne
    (hΓ : Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) = c.Ac hrW hrV hr2)
    (hDZ : dOf T M ≠ quasithinOmegaOneCenter T) :
    ∃ d ∈ dOf T M, d * d = z ∧ dOf T M = Subgroup.zpowers d ∧ orderOf d = 4 := by
  have hB := hS.basis
  have hz1 := hS.z_ne
  have hzZ := hS.z_mem
  have hz2 : z * z = 1 := c.sq_Ac hrW hrV hr2 hS.z_A
  have hZD := Z_le_dOf c
  obtain ⟨d, hd, hdZ⟩ : ∃ d ∈ dOf T M, d ∉ quasithinOmegaOneCenter T := by
    by_contra hh
    push Not at hh
    exact hDZ (le_antisymm (fun x hx => hh x hx) hZD)
  have hdd := sq_eq_z_of_mem_dOf hS htT htRQ hM hP hVr hAAt hΓ hd hdZ
  have hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) hd
  have hcd : cmat z a r r1 d = Tz := by
    rcases D_cmat hS hd with h | h
    · exfalso
      have h1 : d ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
        (hB.cmat_eq_one_iff_mem_centralizer hdN).mp h
      rw [hΓ] at h1
      exact hdZ (D_inf_Ac_le_Z hd h1)
    · exact h
  have hzd : z ∈ Subgroup.zpowers d := by
    rw [← hdd, ← pow_two]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) 2
  have hdinv : d⁻¹ ∈ Subgroup.zpowers d := (Subgroup.zpowers d).inv_mem (Subgroup.mem_zpowers d)
  refine ⟨d, hd, hdd, le_antisymm (fun e he => ?_) (Subgroup.zpowers_le.mpr hd), ?_⟩
  · have heN : e ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
      dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) he
    rcases D_cmat hS he with h | h
    · have h1 : e ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
        (hB.cmat_eq_one_iff_mem_centralizer heN).mp h
      rw [hΓ] at h1
      rcases c.mem_Z_cases hzZ hz1 (D_inf_Ac_le_Z he h1) with h' | h'
      · rw [h']; exact (Subgroup.zpowers d).one_mem
      · rw [h']; exact hzd
    · have hed : e * d ∈ dOf T M := (dOf T M).mul_mem he hd
      have hc : cmat z a r r1 (e * d) = I4 := by
        rw [hB.cmat_mul heN hdN, h, hcd, Tz_sq]
      have h1 : e * d ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
        (hB.cmat_eq_one_iff_mem_centralizer ((Subgroup.normalizer _).mul_mem heN hdN)).mp hc
      rw [hΓ] at h1
      rcases c.mem_Z_cases hzZ hz1 (D_inf_Ac_le_Z hed h1) with h' | h'
      · have : e = d⁻¹ := eq_inv_of_mul_eq_one_left h'
        rw [this]; exact hdinv
      · have : e = z * d⁻¹ := by
          calc e = (e * d) * d⁻¹ := by group
            _ = z * d⁻¹ := by rw [h']
        rw [this]
        exact (Subgroup.zpowers d).mul_mem hzd hdinv
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : orderOf d = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow ?_ ?_
      · intro h
        apply hz1
        rw [← hdd, ← pow_two]
        simpa using h
      · calc d ^ 2 ^ (1 + 1) = d ^ (2 + 2) := by norm_num
          _ = (d * d) * (d * d) := by rw [pow_add, pow_two]
          _ = 1 := by rw [hdd, hz2]
    simpa using h2

end Sq

end S143

end CFSG.Quasithin
