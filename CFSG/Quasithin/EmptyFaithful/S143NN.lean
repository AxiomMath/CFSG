module

public import CFSG.Quasithin.EmptyFaithful.S143NM
public import CFSG.Quasithin.EmptyFaithful.S143NL
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S143IE
public import CFSG.Quasithin.EmptyFaithful.S143NI

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

open A6Model

section CH

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)
  (hVr : ∀ σ ∈ Vr, ∃ ρ' ∈ rOf T M, mm cm (matOf6 σ) = mm (cmat z a r r1 ρ') cm)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2) {p : Fin 6} (hps : s p ≠ p)
  (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1)
  (hemb : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X))
  (hrq : (rOf T M ⊔ qOf T).relIndex T = 2)
  (hAAt : rOf T M = c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t)
  (hnc : ∀ x' : G, x' * z * x'⁻¹ ≠ δ)

include hS htT htRQ hM hP hVl hC1 hδD hδ hδA hnc in
theorem conj_delta_cases {w : G} (hwH : w ∈ mcOf T)
    (hwN : w ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) :
    w * δ * w⁻¹ = δ ∨ w * δ * w⁻¹ = z * δ := by
  have hδ1 : δ ≠ 1 := fun e => hδA (e ▸ (c.Ac hrW hrV hr2).one_mem)
  have hwD : w * δ * w⁻¹ ∈ dOf T M := c.conj_mem_dOf hwH hδD
  have hwΓ : w * δ * w⁻¹ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun a' ha' => ?_
    have hb : w⁻¹ * a' * w ∈ c.Ac hrW hrV hr2 := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hwN) a').mp ha'
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hδ _ hb
    calc a' * (w * δ * w⁻¹) = w * ((w⁻¹ * a' * w) * δ) * w⁻¹ := by group
      _ = w * (δ * (w⁻¹ * a' * w)) * w⁻¹ := by rw [h1]
      _ = (w * δ * w⁻¹) * a' := by group
  rcases D0_cases hS htT htRQ hM hP hVl hC1 hδD hδ hδA hwD hwΓ with h | h | h | h
  · exfalso
    apply hδ1
    have : δ = w⁻¹ * (w * δ * w⁻¹) * w := by group
    rw [this, h]
    group
  · exfalso
    apply hnc w⁻¹
    have : δ = w⁻¹ * (w * δ * w⁻¹) * w := by group
    rw [this, h]
    simp
  · exact Or.inl h
  · exact Or.inr h

include hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hAAt hnc in
theorem exists_eps_conj : ∃ ε ∈ dOf T M, ε * δ * ε⁻¹ = z * δ := by
  obtain ⟨ε, hεD, hε⟩ := exists_eps hS htT htRQ hM hP hVr hδD hδ hδA hps hcoc hAAt
  refine ⟨ε, hεD, ?_⟩
  have hεH : ε ∈ mcOf T := pCoreOf_le 2 _ hεD.1
  have hεN : ε ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) hεD
  rcases conj_delta_cases hS htT htRQ hM hP hVl hC1 hδD hδ hδA hnc hεH hεN with h | h
  · exact absurd h (D_noncomm hS htT htRQ hM hP.conf hVl hC1 hεD hε hδD hδ hδA)
  · exact h

omit [Finite G] in
theorem comm_of_conj_eq {w δ : G} (h : w * δ * w⁻¹ = δ) : δ * w = w * δ := by
  calc δ * w = (w * δ * w⁻¹) * w := by rw [h]
    _ = w * δ := by group

include hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hAAt hnc in
theorem R_mul_eps_mem_CH {ρ : G} (hρ : ρ ∈ rOf T M) :
    ∃ ε ∈ dOf T M, ρ * ε ∈ mcOf T ⊓ Subgroup.centralizer ({δ} : Set G) := by
  have hρH : ρ ∈ mcOf T := rOf_le_mcOf c hρ
  have hρN : ρ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (c.isSylowTwoOf_rq_normalizer_Ac hrW hrV hr2).1 ((le_sup_left : rOf T M ≤ rOf T M ⊔ qOf T) hρ)
  have hzρ : ρ * z = z * ρ := mem_mcOf_comm hρH hS.z_mem
  have hz2 : z * z = 1 := c.sq_Ac hrW hrV hr2 hS.z_A
  rcases conj_delta_cases hS htT htRQ hM hP hVl hC1 hδD hδ hδA hnc hρH hρN with h | h
  · refine ⟨1, (dOf T M).one_mem, ?_⟩
    rw [mul_one]
    refine ⟨hρH, Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_⟩
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact comm_of_conj_eq h
  · obtain ⟨ε, hεD, hε⟩ :=
      exists_eps_conj hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hAAt hnc
    refine ⟨ε, hεD, ?_⟩
    have hεH : ε ∈ mcOf T := pCoreOf_le 2 _ hεD.1
    refine ⟨(mcOf T).mul_mem hρH hεH, Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_⟩
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    have hρz : ρ * z * ρ⁻¹ = z := by rw [hzρ]; group
    have key : (ρ * ε) * h' * (ρ * ε)⁻¹ = h' := by
      calc (ρ * ε) * h' * (ρ * ε)⁻¹ = ρ * (ε * h' * ε⁻¹) * ρ⁻¹ := by group
        _ = ρ * (z * h') * ρ⁻¹ := by rw [hε]
        _ = (ρ * z * ρ⁻¹) * (ρ * h' * ρ⁻¹) := by group
        _ = z * (z * h') := by rw [hρz, h]
        _ = (z * z) * h' := by group
        _ = h' := by rw [hz2, one_mul]
    exact comm_of_conj_eq key

section OmegaCH

variable {Ω : Subgroup (MulAut (UT T M))} (hΩle : Ω ≤ c.actK.range)
  (hrel : Ω.relIndex c.actK.range = 2) (hα : c.alphaOf hrW hrV hr2 ∈ Ω)

include hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hemb hrq hAAt hΩle hrel hα in
theorem actK_ch_mem_Omega
    {h : G} (hhH : h ∈ mcOf T) (hhδ : h * δ = δ * h) :
    c.actK ⟨h, hhH⟩ ∈ Ω := by
  have hSyl : IsSylowTwoOf T (mcOf T) := sylow_G1_of_hyp c.h1281
  have hTH : T ≤ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H
  have hHeq := eq_oTwoUpper_sup_of_isSylowTwoOf hSyl
  have hTN : T ≤ Subgroup.normalizer (oTwoUpper (mcOf T) : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper (mcOf T))
  have hhmem : h ∈ oTwoUpper (mcOf T) ⊔ T := by rw [← hHeq]; exact hhH
  obtain ⟨o, ho, τ, hτ, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hTN).1 hhmem
  have hoH : o ∈ mcOf T := oTwoUpper_le _ ho
  have hoδ : o * δ = δ * o :=
    (Subgroup.mem_centralizer_iff.mp
      (oTwoUpper_mcOf_le_centralizer hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb ho) δ rfl).symm
  have hτH : τ ∈ mcOf T := hTH hτ
  have hτδ : τ * δ = δ * τ := by
    have : o * (τ * δ) = o * (δ * τ) := by
      calc o * (τ * δ) = (o * τ) * δ := by group
        _ = δ * (o * τ) := hhδ
        _ = (δ * o) * τ := by group
        _ = (o * δ) * τ := by rw [hoδ]
        _ = o * (δ * τ) := by group
    exact mul_left_cancel this
  have hτRQ : τ ∈ rOf T M ⊔ qOf T :=
    tdOf_le_rq hS htT htRQ hM hP hVr hδD hδ hδA hps hcoc hrq hAAt
      ⟨hτ, Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
        rw [Set.mem_singleton_iff] at hh'; subst hh'; exact hτδ.symm⟩
  have hτΩ : c.actK ⟨τ, hτH⟩ ∈ Ω :=
    c.actK_rq_mem_Omega hrW hrV hr2 hΩle hrel hα htT hAAt hτRQ hτH
  have hoΩ : c.actK ⟨o, hoH⟩ ∈ Ω :=
    mem_of_cube_of_relIndex_two hrel ⟨⟨o, hoH⟩, rfl⟩ (c.actK_cube_of_mem_oTwoUpper ho)
  have e : (⟨o * τ, hhH⟩ : ↥(mcOf T)) = ⟨o, hoH⟩ * ⟨τ, hτH⟩ := rfl
  rw [e, map_mul]
  exact Ω.mul_mem hoΩ hτΩ

include hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hemb hrq hAAt hnc hΩle hrel hα in
theorem map_actK_ch_eq_Omega (hcardΩ : Nat.card ↥Ω = 36) :
    ((mcOf T ⊓ Subgroup.centralizer ({δ} : Set G)).subgroupOf (mcOf T)).map c.actK = Ω := by
  set CH := mcOf T ⊓ Subgroup.centralizer ({δ} : Set G) with hCH
  have hCHH : CH ≤ mcOf T := inf_le_left
  have hle : (CH.subgroupOf (mcOf T)).map c.actK ≤ Ω := by
    rintro _ ⟨⟨h, hh⟩, hmem, rfl⟩
    have hmem' : h ∈ CH := Subgroup.mem_subgroupOf.mp hmem
    have hc : h * δ = δ * h := (Subgroup.mem_centralizer_iff.mp hmem'.2 δ rfl).symm
    exact actK_ch_mem_Omega hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hemb hrq hAAt hΩle
      hrel hα hh hc
  have h1 := card_map_mul_card_inf_ker hCHH c.actK
  rw [c.actK_ker_map] at h1
  have h2 : Nat.card ↥(imageOTwoQuot (mcOf T) CH) * Nat.card ↥(CH ⊓ qOf T) = Nat.card CH :=
    card_imageOTwoQuot_mul hCHH
  have hpos : 0 < Nat.card ↥(CH ⊓ qOf T) := Nat.card_pos
  have hcard_eq : Nat.card ↥((CH.subgroupOf (mcOf T)).map c.actK) =
      Nat.card ↥(imageOTwoQuot (mcOf T) CH) :=
    Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  obtain ⟨P, hP9, hPle⟩ := c.exists_card_nine_le_image
  have hO2CH : oTwoUpper (mcOf T) ≤ CH :=
    le_inf (oTwoUpper_le _) (oTwoUpper_mcOf_le_centralizer hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb)
  have h9 : 9 ∣ Nat.card ↥(imageOTwoQuot (mcOf T) CH) := by
    have := Subgroup.card_dvd_of_le (hPle.trans (imageOTwoQuot_mono hO2CH))
    rwa [hP9] at this
  have hRI : imageOTwoQuot (mcOf T) (rOf T M) ≤ imageOTwoQuot (mcOf T) CH := by
    intro u hu
    obtain ⟨w, hwH, hwR, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    obtain ⟨ε, hεD, hwε⟩ :=
      R_mul_eps_mem_CH hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hAAt hnc hwR
    have hεH : ε ∈ mcOf T := pCoreOf_le 2 _ hεD.1
    refine mem_imageOTwoQuot_iff.mpr ⟨w * ε, hwε.1, hwε, ?_⟩
    have e : (⟨w * ε, hwε.1⟩ : ↥(mcOf T)) = ⟨w, hwH⟩ * ⟨ε, hεH⟩ := rfl
    have hε1 : (QuotientGroup.mk ⟨ε, hεH⟩ : OTwoQuot (mcOf T)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ((mem_pCore_iff _).mpr hεD.1)
    rw [e, QuotientGroup.mk_mul, hε1, mul_one]
  have h4 : 4 ∣ Nat.card ↥(imageOTwoQuot (mcOf T) CH) := by
    have := Subgroup.card_dvd_of_le hRI
    rwa [rstar_card_of c] at this
  have h36 : 36 ∣ Nat.card ↥(imageOTwoQuot (mcOf T) CH) := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 4) h9 h4
    simpa using this
  have hge : Nat.card ↥Ω ≤ Nat.card ↥((CH.subgroupOf (mcOf T)).map c.actK) := by
    rw [hcardΩ, hcard_eq]
    exact Nat.le_of_dvd Nat.card_pos h36
  exact Subgroup.eq_of_le_of_card_ge hle hge

end OmegaCH

section Pattern

variable {Gc : Type*} [Group Gc]

include hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hemb hrq hAAt hnc in
theorem exists_pattern_gd (hnc' : ∀ x' : G, x' * z * x'⁻¹ ≠ z * δ)
    (hq : qOf T = uOfL22 T M ⊔ dOf T M) (hzGd : z ∈ Subgroup.centralizer ({δ} : Set G))
    (φ : ↥(Subgroup.centralizer ({δ} : Set G)) →* Gc) (hφs : Function.Surjective φ)
    (hφk : φ.ker = (Subgroup.zpowers δ).subgroupOf (Subgroup.centralizer ({δ} : Set G))) :
    ∃ P : Subgroup Gc, P ≤ Subgroup.centralizer ({φ ⟨z, hzGd⟩} : Set Gc) ∧
      P.relIndex (Subgroup.centralizer ({φ ⟨z, hzGd⟩} : Set Gc)) ≤ 2 ∧ ExtQ8SqS3S3 ↥P := by
  obtain ⟨Ω, hΩle, hrel, hcardΩ, ⟨e⟩, hα⟩ := c.exists_OmegaPkg hrW hrV hr2
  set CH := mcOf T ⊓ Subgroup.centralizer ({δ} : Set G) with hCH
  have hCHH : CH ≤ mcOf T := inf_le_left
  have hmap : (CH.subgroupOf (mcOf T)).map c.actK = Ω := map_actK_ch_eq_Omega hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hemb hrq hAAt
    hnc hΩle hrel hα hcardΩ
  have hδ2 : δ * δ = 1 := Gamma_sq hS htT htRQ hM hC1 hδ
  have hz2 : z * z = 1 := c.sq_Ac hrW hrV hr2 hS.z_A
  have hδQ : δ ∈ qOf T := hδD.1
  have hδGd : δ ∈ Subgroup.centralizer ({δ} : Set G) := Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
    rw [Set.mem_singleton_iff] at hh'; subst hh'; rfl
  have hUH : uOfL22 T M ≤ mcOf T := c.h1281.uOfL22_le_g1
  have hUGd : uOfL22 T M ≤ Subgroup.centralizer ({δ} : Set G) := fun u hu => Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
    rw [Set.mem_singleton_iff] at hh'; subst hh'
    exact (Subgroup.mem_centralizer_iff.mp hδD.2 u hu).symm
  have hUCH : uOfL22 T M ≤ CH := le_inf hUH hUGd
  have hUQ : uOfL22 T M ≤ qOf T := uOfL22_le_qOf c
  have hfΩ : ∀ x : ↥CH, c.actK (Subgroup.inclusion hCHH x) ∈ Ω := fun x =>
    actK_ch_mem_Omega hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hemb hrq hAAt hΩle hrel hα
      (hCHH x.2) (Subgroup.mem_centralizer_iff.mp x.2.2 δ rfl).symm
  let fH : ↥CH →* ↥Ω := (c.actK.comp (Subgroup.inclusion hCHH)).codRestrict Ω hfΩ
  let f : ↥CH →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) := e.toMonoidHom.comp fH
  have hfx : ∀ x : ↥CH, f x = 1 ↔ c.actK (Subgroup.inclusion hCHH x) = 1 := by
    intro x
    constructor
    · intro h
      have h1 : fH x = 1 := e.injective (by rw [map_one]; exact h)
      exact congrArg Subtype.val h1
    · intro h
      have h1 : fH x = 1 := Subtype.ext h
      show e (fH x) = 1
      rw [h1, map_one]
  have hf : Function.Surjective f := by
    intro b
    have hb : ((e.symm b : ↥Ω) : MulAut (UT T M)) ∈ (CH.subgroupOf (mcOf T)).map c.actK := by
      rw [hmap]
      exact (e.symm b).2
    obtain ⟨y, hy, hyb⟩ := hb
    refine ⟨⟨(y : G), (Subgroup.mem_subgroupOf.mp hy)⟩, ?_⟩
    have : fH ⟨(y : G), (Subgroup.mem_subgroupOf.mp hy)⟩ = e.symm b := Subtype.ext hyb
    show e (fH _) = b
    rw [this, MulEquiv.apply_symm_apply]
  have hδqz : ∀ x : ↥CH, (x : G) ∈ Subgroup.zpowers δ → f x = 1 := by
    intro x hx
    rw [hfx]
    exact c.actK_eq_one_of_mem_qOf ((Subgroup.zpowers_le.mpr hδQ) hx)
  have hfU : ∀ x : ↥CH, (x : G) ∈ uOfL22 T M → f x = 1 := by
    intro x hx
    rw [hfx]
    exact c.actK_eq_one_of_mem_qOf (hUQ hx)
  have hfker : ∀ x : ↥CH, f x = 1 →
      ∃ u ∈ uOfL22 T M, ∃ w ∈ Subgroup.zpowers δ, (x : G) = u * w := by
    intro x hx
    have h1 := (hfx x).mp hx
    have hxQ : (x : G) ∈ qOf T := c.mem_qOf_of_actK_eq_one h1
    have hxδ : (x : G) * δ = δ * (x : G) := (Subgroup.mem_centralizer_iff.mp x.2.2 δ rfl).symm
    exact exists_decomp_of_qOf_centralizer hS htT htRQ hM hP hVl hC1 hδD hδ hδA hq hxQ hxδ
  have hUN : ∀ x ∈ CH, ∀ u ∈ uOfL22 T M, x * u * x⁻¹ ∈ uOfL22 T M := fun x hx u hu =>
    (Subgroup.mem_normalizer_iff.mp (c.hHU hx.1) u).mp hu
  have hcen : ∀ x : ↥CH, (∀ u ∈ uOfL22 T M, (x : G) * u = u * (x : G)) → f x = 1 := by
    intro x hx
    rw [hfx]
    refine c.actK_eq_one_of_centralizes (hCHH x.2) (fun u hu => ?_)
    calc (x : G) * u * (x : G)⁻¹ = (u * (x : G)) * (x : G)⁻¹ := by rw [hx u hu]
      _ = u := by group
  have hker : ∀ x : ↥(Subgroup.centralizer ({δ} : Set G)), φ x = 1 ↔ (x : G) ∈ Subgroup.zpowers δ := by
    intro x
    rw [← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  have hext := ext_of_data φ (inf_le_right : CH ≤ Subgroup.centralizer ({δ} : Set G)) hUCH hker f hf hδqz hfU hfker
    (U_inf_zpowers_delta hS htT htRQ hM hC1 hδ hδA) hUN hcen c.c15.q8sq
  refine ⟨(CH.subgroupOf (Subgroup.centralizer ({δ} : Set G))).map φ, ?_, ?_, hext⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    have hxCH : (x : G) ∈ CH := Subgroup.mem_subgroupOf.mp hx
    have hcomm : (x : G) * z = z * (x : G) := mem_mcOf_comm hxCH.1 hS.z_mem
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm.symm
  · rw [Subgroup.relIndex_eq_one.mpr]
    · norm_num
    · intro p hp
      obtain ⟨x, rfl⟩ := hφs p
      have hcomm := Subgroup.mem_centralizer_iff.mp hp (φ ⟨z, hzGd⟩) rfl
      refine ⟨x, ?_, rfl⟩
      have h1 : φ (⟨z, hzGd⟩ * x * (x * ⟨z, hzGd⟩)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, map_mul, ← hcomm]
        simp
      have h2 := (hker _).mp h1
      have e1 : (((⟨z, hzGd⟩ * x * (x * ⟨z, hzGd⟩)⁻¹ : ↥(Subgroup.centralizer ({δ} : Set G)))) : G) = z * (x : G) * ((x : G) * z)⁻¹ := rfl
      rw [e1] at h2
      rcases mem_zpowers_of_sq_eq_one hδ2 h2 with h3 | h3
      · have hxz : (x : G) * z = z * (x : G) := by
          have : z * (x : G) = (x : G) * z := by
            calc z * (x : G) = (z * (x : G) * ((x : G) * z)⁻¹) * ((x : G) * z) := by group
              _ = (x : G) * z := by rw [h3, one_mul]
          exact this.symm
        refine Subgroup.mem_subgroupOf.mpr ⟨c.mem_mcOf_of_comm hS.z_mem hS.z_ne hxz, x.2⟩
      · exfalso
        apply hnc' (x : G)
        have hzd : z * δ = δ * z := (Subgroup.mem_centralizer_iff.mp hzGd δ rfl).symm
        calc (x : G) * z * (x : G)⁻¹ = (z * (x : G) * ((x : G) * z)⁻¹)⁻¹ * z := by group
          _ = δ⁻¹ * z := by rw [h3]
          _ = z * δ := by
            rw [show δ⁻¹ = δ from inv_eq_of_mul_eq_one_right hδ2]
            exact hzd.symm

end Pattern

end CH

end S143

end CFSG.Quasithin
