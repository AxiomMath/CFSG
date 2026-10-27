module

public import CFSG.Quasithin.EmptyFaithful.S143IE
public import CFSG.Quasithin.EmptyFaithful.S143NM
public import CFSG.Quasithin.EmptyFaithful.S143QA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Quasithin.S152O4

namespace S143


section Model

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c in
theorem Counter.exists_gam_model :
    ∃ (cm : UT T M ≃* Vec) (ρ : Gam →* MulAut (UT T M)),
      Function.Injective ρ ∧ (∀ γ v, cm (ρ γ v) = act γ (cm v)) ∧
      (∀ (u : G) (hu : u ∈ uOfL22 T M), detQ (cm (tclsE c.hUN hu)) = 0 ↔ u * u = 1) ∧
      (∀ (n : G) (hn : n ∈ mcOf T), n ∈ oTwoUpper (mcOf T) →
        ∃ γ : Gam, γ ^ 3 = 1 ∧ c.actK ⟨n, hn⟩ = ρ γ) ∧
      (∀ γ : Gam, γ ^ 3 = 1 → ∃ (n : G) (hn : n ∈ mcOf T), n ∈ oTwoUpper (mcOf T) ∧
        c.actK ⟨n, hn⟩ = ρ γ) := by
  have h := c.h1281
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  let _ : CommGroup (UT T M) :=
    { (inferInstance : Group (UT T M)) with
      mul_comm := fun a b => (tilde_isMulCommutative h).is_comm.comm a b }
  have hrange : c.actK.range = orthogonalGroupOf q := c.actK_range.trans hq6
  have hexp : ∀ w : UT T M, w * w = 1 := tilde_mul_self h
  obtain ⟨U₁, U₂, hinf, hsup, φ₁, φ₂, hqe⟩ :=
    S153.exists_decomposition_of_plusType hexp hq4 hq1 hq2 hq3
  let cm : UT T M ≃* Vec := (S1417.coordEquiv hinf hsup φ₁ φ₂).trans kappa
  have hqc : ∀ v, q v = detQ (cm v) := by
    intro v
    rw [hqe v, quadOf_eq_qFloc hinf hsup φ₁ φ₂ v]
    exact qFloc_eq_detQ _
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hq4 hq1 hq2 hq3
  have hO72 : Nat.card (orthogonalGroupOf q) = 72 := hS.card_X
  have hOq : ∀ γ : Gam, rhoV cm γ ∈ orthogonalGroupOf q := by
    intro γ v
    rw [hqc, hqc, rhoV_apply, detQ_act]
  have hle : (rhoV cm).range ≤ orthogonalGroupOf q := by
    rintro _ ⟨γ, rfl⟩
    exact hOq γ
  have hR36 : Nat.card (rhoV cm).range = 36 := by
    rw [← card_Gam]
    exact (Nat.card_congr (MonoidHom.ofInjective (rhoV_injective cm)).toEquiv).symm
  have hrel : (rhoV cm).range.relIndex (orthogonalGroupOf q) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (rhoV cm).range (orthogonalGroupOf q)
    rw [inf_eq_left.mpr hle, hR36, hO72] at h1
    omega
  have hle' : (rhoV cm).range ≤ c.actK.range := by rw [hrange]; exact hle
  have hrel' : (rhoV cm).range.relIndex c.actK.range = 2 := by rw [hrange]; exact hrel
  refine ⟨cm, rhoV cm, rhoV_injective cm, fun γ v => rhoV_apply cm γ v, ?_, ?_, ?_⟩
  · intro u hu
    have := hq5 _ (tclsE c.hUN hu).2 ⟨u, c.hUN hu⟩ hu rfl
    rw [← hqc (tclsE c.hUN hu), pow_two] at *
    exact this
  · intro n hn hnN
    have h3 := c.actK_cube_of_mem_oTwoUpper (x := ⟨n, hn⟩) hnN
    have hmem : c.actK ⟨n, hn⟩ ∈ (rhoV cm).range :=
      mem_of_cube_of_relIndex_two hrel' ⟨⟨n, hn⟩, rfl⟩ h3
    obtain ⟨γ, hγ⟩ := hmem
    refine ⟨γ, ?_, hγ.symm⟩
    apply rhoV_injective cm
    rw [map_pow, hγ, h3, map_one]
  · intro γ hγ3
    obtain ⟨h, hh⟩ := hle' ⟨γ, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (mcOf T) h.2
    have hσ3 : (rhoV cm γ) ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
    have hodd : Odd (orderOf (rhoV cm γ)) :=
      Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hσ3)
    have hcop : Nat.Coprime (2 ^ k) (orderOf (rhoV cm γ)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (A4.mem_zpowers_pow_of_coprime hcop)
    have hnH : ((h : G) ^ 2 ^ k) ^ j ∈ mcOf T := Subgroup.zpow_mem _ ((mcOf T).pow_mem h.2 _) j
    refine ⟨((h : G) ^ 2 ^ k) ^ j, hnH, Subgroup.zpow_mem _ hk j, ?_⟩
    have e : (⟨((h : G) ^ 2 ^ k) ^ j, hnH⟩ : ↥(mcOf T)) = (h ^ 2 ^ k) ^ j := rfl
    rw [e, map_zpow, map_pow, hh, hj]

theorem gam_stab_le : ∀ m : Vec, detQ m = 1 →
    Fintype.card {γ : Gam // γ ^ 3 = 1 ∧ act γ m = m} ≤ 3 := by decide +kernel

theorem gam_stab_ex : ∀ m : Vec, detQ m = 1 →
    ∃ γ : Gam, γ ≠ 1 ∧ γ ^ 3 = 1 ∧ act γ m = m := by decide +kernel

theorem zmod_two_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

include c in
theorem Counter.card_centralizer_oTwoUpper {z u₀ : G} (hzZ : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hu₀ : u₀ ∈ uOfL22 T M) (hu₀z : u₀ * u₀ = z) :
    Nat.card ↥(oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({u₀} : Set G)) = 48 ∧
      ∃ ω ∈ oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({u₀} : Set G), orderOf ω = 3 := by
  classical
  obtain ⟨cm, ρ, hρinj, hρcm, hdet, hM1, hM3⟩ := c.exists_gam_model
  have hNH : oTwoUpper (mcOf T) ≤ mcOf T := oTwoUpper_le _
  set C := oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({u₀} : Set G) with hC
  have hCN : C ≤ oTwoUpper (mcOf T) := inf_le_left
  have hCH : C ≤ mcOf T := hCN.trans hNH
  let f : ↥C →* MulAut (UT T M) := c.actK.comp (Subgroup.inclusion hCH)
  have hfapply : ∀ n : ↥C, f n = c.actK ⟨n, hCH n.2⟩ := fun n => rfl
  have hu₀nc : u₀ ∉ centerOf (uOfL22 T M) := by
    intro h
    rw [c.centerOf_uOfL22_eq] at h
    have := sq_eq_one_of_mem_omegaOneCenter T h
    rw [pow_two, hu₀z] at this
    exact hz1 this
  have hU16 := isQ8Sq_card_centralizer c.c15.q8sq u₀ hu₀ hu₀nc
  have hker : f.ker.map C.subtype = uOfL22 T M ⊓ Subgroup.centralizer ({u₀} : Set G) := by
    ext n
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨⟨n', hn'⟩, hk, rfl⟩
      have h1 : c.actK ⟨n', hCH hn'⟩ = 1 := hk
      have hq : n' ∈ qOf T := c.mem_qOf_of_actK_eq_one h1
      exact ⟨inf_qOf_le_uOfL22 c ⟨hCN hn', hq⟩, hn'.2⟩
    · rintro ⟨hnU, hnc⟩
      have hnN : n ∈ oTwoUpper (mcOf T) := uOfL22_le_oTwoUpper c hnU
      have hnC : n ∈ C := ⟨hnN, hnc⟩
      refine ⟨⟨n, hnC⟩, ?_, rfl⟩
      show f ⟨n, hnC⟩ = 1
      rw [hfapply]
      exact c.actK_eq_one_of_mem_qOf (uOfL22_le_qOf c hnU)
  have hkercard : Nat.card f.ker = 16 := by
    rw [← hU16, ← hker]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective f.ker C.subtype C.subtype_injective).toEquiv)
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hkercard] at hmul
  set m₀ : Vec := cm (tclsE c.hUN hu₀) with hm₀
  have hdet1 : detQ m₀ = 1 := by
    apply zmod_two_ne_zero
    intro h0
    have := (hdet u₀ hu₀).mp h0
    rw [hu₀z] at this
    exact hz1 this
  have hfix : ∀ n : ↥C, c.actK ⟨n, hCH n.2⟩ (tclsE c.hUN hu₀) = tclsE c.hUN hu₀ := by
    intro n
    have hnc : (n : G) * u₀ * (n : G)⁻¹ = u₀ := by
      have := Subgroup.mem_centralizer_singleton_iff.mp n.2.2
      rw [this]
      group
    have hu' : (n : G) * u₀ * (n : G)⁻¹ ∈ uOfL22 T M := by rw [hnc]; exact hu₀
    show actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) (hHN_of T) c.hHU
      ⟨n, hCH n.2⟩ (tclsE c.hUN hu₀) = _
    rw [actTilde_tclsE c.hUN (hHN_of T) c.hHU ⟨n, hCH n.2⟩ hu₀ hu']
    exact tclsE_congr c.hUN hu' hu₀ hnc
  have hrange_le : Nat.card f.range ≤ 3 := by
    have key : ∀ σ : f.range, ∃ γ : Gam, γ ^ 3 = 1 ∧ act γ m₀ = m₀ ∧ ρ γ = σ := by
      rintro ⟨_, ⟨n, rfl⟩⟩
      obtain ⟨γ, hγ3, hγ⟩ := hM1 n (hCH n.2) (hCN n.2)
      refine ⟨γ, hγ3, ?_, ?_⟩
      · have h1 := hfix n
        rw [hγ] at h1
        have := congrArg cm h1
        rw [hρcm] at this
        exact this
      · exact hγ.symm
    choose γ hγ using key
    let F : f.range → {γ : Gam // γ ^ 3 = 1 ∧ act γ m₀ = m₀} :=
      fun σ => ⟨γ σ, (hγ σ).1, (hγ σ).2.1⟩
    have hF : Function.Injective F := by
      intro σ τ h
      apply Subtype.ext
      have h1 : γ σ = γ τ := congrArg Subtype.val h
      rw [← (hγ σ).2.2, ← (hγ τ).2.2, h1]
    calc Nat.card f.range ≤ Nat.card {γ : Gam // γ ^ 3 = 1 ∧ act γ m₀ = m₀} :=
          Nat.card_le_card_of_injective F hF
      _ = Fintype.card {γ : Gam // γ ^ 3 = 1 ∧ act γ m₀ = m₀} := Nat.card_eq_fintype_card
      _ ≤ 3 := gam_stab_le m₀ hdet1
  obtain ⟨γ₀, hγ₀1, hγ₀3, hγ₀m⟩ := gam_stab_ex m₀ hdet1
  obtain ⟨n₁, hn₁H, hn₁N, hn₁⟩ := hM3 γ₀ hγ₀3
  have hn₁U : n₁ * u₀ * n₁⁻¹ ∈ uOfL22 T M := (Subgroup.mem_normalizer_iff.mp (c.hHU hn₁H) u₀).mp hu₀
  have hρfix : ρ γ₀ (tclsE c.hUN hu₀) = tclsE c.hUN hu₀ := by
    apply cm.injective
    rw [hρcm]
    exact hγ₀m
  have hu₁eq : tclsE c.hUN hn₁U = tclsE c.hUN hu₀ := by
    have h1 : c.actK ⟨n₁, hn₁H⟩ (tclsE c.hUN hu₀) = tclsE c.hUN hn₁U := by
      show actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) (hHN_of T) c.hHU
        ⟨n₁, hn₁H⟩ (tclsE c.hUN hu₀) = _
      exact actTilde_tclsE c.hUN (hHN_of T) c.hHU ⟨n₁, hn₁H⟩ hu₀ hn₁U
    rw [← h1, hn₁, hρfix]
  have hu₁Z : u₀⁻¹ * (n₁ * u₀ * n₁⁻¹) ∈ quasithinOmegaOneCenter T :=
    (tclsE_eq_iff c.hUN hu₀ hn₁U).mp hu₁eq.symm
  have hcZ : ∀ v ∈ uOfL22 T M, v * u₀ * v⁻¹ * u₀⁻¹ ∈ quasithinOmegaOneCenter T := fun v hv => by
    rw [← c.centerOf_uOfL22_eq]
    exact isQ8Sq_comm_mem_centerOf c.c15.q8sq v hv u₀ hu₀
  have hzcentral : ∀ v ∈ uOfL22 T M, v * z * v⁻¹ = z := by
    intro v hv
    have hz' : z ∈ centerOf (uOfL22 T M) := by rw [c.centerOf_uOfL22_eq]; exact hzZ
    have := Subgroup.mem_centralizer_iff.mp hz'.2 v hv
    rw [this]; group
  have hzz : z * z = 1 := by
    have := sq_eq_one_of_mem_omegaOneCenter T hzZ
    rwa [pow_two] at this
  obtain ⟨n', hn'C, hn'H, hn'⟩ : ∃ n' : G, n' ∈ C ∧ ∃ hn'H : n' ∈ mcOf T,
      c.actK ⟨n', hn'H⟩ = ρ γ₀ := by
    rcases c.mem_Z_cases hzZ hz1 hu₁Z with h | h
    · have h2 : n₁ * u₀ * n₁⁻¹ = u₀ := by
        have := congrArg (u₀ * ·) h
        simpa using this
      refine ⟨n₁, ⟨hn₁N, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hn₁H, hn₁⟩
      have := congrArg (· * n₁) h2
      simpa [mul_assoc] using this
    · have h2 : n₁ * u₀ * n₁⁻¹ = u₀ * z := by
        have := congrArg (u₀ * ·) h
        simpa using this
      obtain ⟨v, hvU, hv⟩ : ∃ v ∈ uOfL22 T M, v * u₀ * v⁻¹ ≠ u₀ := by
        by_contra hcon
        push Not at hcon
        apply hu₀nc
        refine ⟨hu₀, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
        have := hcon v hv
        have h3 := congrArg (· * v) this
        simpa [mul_assoc] using h3
      have hvz : v * u₀ * v⁻¹ = z * u₀ := by
        rcases c.mem_Z_cases hzZ hz1 (hcZ v hvU) with h3 | h3
        · exfalso
          apply hv
          have := congrArg (· * u₀) h3
          simpa [mul_assoc] using this
        · have := congrArg (· * u₀) h3
          simpa [mul_assoc] using this
      have hvN : v ∈ oTwoUpper (mcOf T) := uOfL22_le_oTwoUpper c hvU
      have hvH : v ∈ mcOf T := hNH hvN
      have hu₀z' : u₀ * z = z * u₀ := by
        have hz' : z ∈ centerOf (uOfL22 T M) := by rw [c.centerOf_uOfL22_eq]; exact hzZ
        exact Subgroup.mem_centralizer_iff.mp hz'.2 u₀ hu₀
      refine ⟨v * n₁, ⟨(oTwoUpper (mcOf T)).mul_mem hvN hn₁N,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, (mcOf T).mul_mem hvH hn₁H, ?_⟩
      · have hconj : v * n₁ * u₀ * (v * n₁)⁻¹ = u₀ := by
          calc v * n₁ * u₀ * (v * n₁)⁻¹ = v * (n₁ * u₀ * n₁⁻¹) * v⁻¹ := by group
            _ = v * (u₀ * z) * v⁻¹ := by rw [h2]
            _ = (v * u₀ * v⁻¹) * (v * z * v⁻¹) := by group
            _ = (z * u₀) * z := by rw [hvz, hzcentral v hvU]
            _ = u₀ := by rw [mul_assoc, hu₀z', ← mul_assoc, hzz, one_mul]
        have := congrArg (· * (v * n₁)) hconj
        simpa [mul_assoc] using this
      · have e : (⟨v * n₁, (mcOf T).mul_mem hvH hn₁H⟩ : ↥(mcOf T)) = ⟨v, hvH⟩ * ⟨n₁, hn₁H⟩ := rfl
        rw [e, map_mul, c.actK_eq_one_of_mem_qOf (uOfL22_le_qOf c hvU), hn₁, one_mul]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσord : orderOf (ρ γ₀) = 3 := by
    have h3 : orderOf γ₀ = 3 := orderOf_eq_prime hγ₀3 hγ₀1
    rw [orderOf_injective ρ hρinj γ₀, h3]
  have hn'3 : n' ^ 3 ∈ uOfL22 T M := by
    have hH3 : n' ^ 3 ∈ mcOf T := (mcOf T).pow_mem hn'H 3
    have hq : c.actK ⟨n' ^ 3, hH3⟩ = 1 := by
      have e : (⟨n' ^ 3, hH3⟩ : ↥(mcOf T)) = (⟨n', hn'H⟩ : ↥(mcOf T)) ^ 3 := rfl
      rw [e, map_pow, hn', ← map_pow, hγ₀3, map_one]
    exact inf_qOf_le_uOfL22 c ⟨(oTwoUpper (mcOf T)).pow_mem (hCN hn'C) 3,
      c.mem_qOf_of_actK_eq_one hq⟩
  have hU2 : IsPGroup 2 ↥(uOfL22 T M) := c.h1281.sylow.1.to_le (uOfL22_le_T_of_hyp c.h1281)
  obtain ⟨j, hj⟩ := hU2 ⟨n' ^ 3, hn'3⟩
  have hj' : (n' ^ 3) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hω3 : (n' ^ 2 ^ j) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hj'
  have hωH : n' ^ 2 ^ j ∈ mcOf T := (mcOf T).pow_mem hn'H _
  have hω1 : n' ^ 2 ^ j ≠ 1 := by
    intro h1
    have h2 : c.actK ⟨n' ^ 2 ^ j, hωH⟩ = 1 := by
      have e : (⟨n' ^ 2 ^ j, hωH⟩ : ↥(mcOf T)) = (⟨n', hn'H⟩ : ↥(mcOf T)) ^ 2 ^ j := rfl
      have : (⟨n' ^ 2 ^ j, hωH⟩ : ↥(mcOf T)) = 1 := Subtype.ext h1
      rw [this, map_one]
    have e : (⟨n' ^ 2 ^ j, hωH⟩ : ↥(mcOf T)) = (⟨n', hn'H⟩ : ↥(mcOf T)) ^ 2 ^ j := rfl
    rw [e, map_pow, hn'] at h2
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hσord] at hd
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hωC : n' ^ 2 ^ j ∈ C := C.pow_mem hn'C _
  have hωord : orderOf (n' ^ 2 ^ j) = 3 := orderOf_eq_prime hω3 hω1
  have hmem : ρ γ₀ ∈ f.range := ⟨⟨n', hn'C⟩, by rw [hfapply]; exact hn'⟩
  have hdvd : 3 ∣ Nat.card f.range := by
    have := Subgroup.orderOf_dvd_natCard f.range hmem
    rwa [hσord] at this
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have h3 : Nat.card f.range = 3 := by omega
  refine ⟨?_, ⟨n' ^ 2 ^ j, hωC, hωord⟩⟩
  rw [h3] at hmul
  omega

end Model


section Odd

variable {G : Type*} [Group G]

theorem conj_fix_of_odd {d h : G} (hd4 : orderOf d = 4) (hodd : Odd (orderOf h))
    (hmem : h * d * h⁻¹ ∈ Subgroup.zpowers d) : h * d * h⁻¹ = d := by
  have hdd : (d * d) * (d * d) = 1 ∧ d * d ≠ 1 := by
    have h4 : d ^ 4 = 1 := by rw [← hd4]; exact pow_orderOf_eq_one d
    refine ⟨?_, fun h2 => ?_⟩
    · calc (d * d) * (d * d) = d ^ 4 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := h4
    · have : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
      rw [hd4] at this; omega
  rcases mem_zpowers_four (d := d) (z := d * d) rfl hdd.1 hmem with h1 | h1 | h1 | h1
  · exfalso
    have : d = 1 := by
      have e : d = h⁻¹ * (h * d * h⁻¹) * h := by group
      rw [e, h1]; group
    apply hdd.2
    rw [this]; group
  · exact h1
  · exfalso
    have : (h * d * h⁻¹) * (h * d * h⁻¹) = h * (d * d) * h⁻¹ := by group
    rw [h1, hdd.1] at this
    apply hdd.2
    have h3 : h * (d * d) * h⁻¹ = 1 := this.symm
    have : d * d = h⁻¹ * (h * (d * d) * h⁻¹) * h := by group
    rw [this, h3]; group
  ·
    exfalso
    have hinv : h * d * h⁻¹ = d⁻¹ := by
      rw [h1]
      have : d * (d * d) * d = 1 := by
        calc d * (d * d) * d = (d * d) * (d * d) := by group
          _ = 1 := hdd.1
      exact eq_inv_of_mul_eq_one_left (by
        calc d * (d * d) * d = 1 := this)
    have hc : (h * h) * d * (h * h)⁻¹ = d := by
      calc (h * h) * d * (h * h)⁻¹ = h * (h * d * h⁻¹) * h⁻¹ := by group
        _ = h * d⁻¹ * h⁻¹ := by rw [hinv]
        _ = (h * d * h⁻¹)⁻¹ := by group
        _ = d := by rw [hinv, inv_inv]
    obtain ⟨l, hl⟩ := hodd
    have hhm : h ^ orderOf h = 1 := pow_orderOf_eq_one h
    rw [hl] at hhm
    have hcl : (h * h) ^ l * d * ((h * h) ^ l)⁻¹ = d := by
      have hcomm : Commute (h * h) d := by
        have : (h * h) * d = d * (h * h) := by
          have := congrArg (· * (h * h)) hc
          simpa [mul_assoc] using this
        exact this
      have := (hcomm.pow_left l).eq
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have key : h ^ (2 * l + 1) * d * (h ^ (2 * l + 1))⁻¹ = d⁻¹ := by
      calc h ^ (2 * l + 1) * d * (h ^ (2 * l + 1))⁻¹
          = ((h * h) ^ l * h) * d * ((h * h) ^ l * h)⁻¹ := by
            rw [pow_succ, pow_mul, pow_two]
        _ = (h * h) ^ l * (h * d * h⁻¹) * ((h * h) ^ l)⁻¹ := by group
        _ = (h * h) ^ l * d⁻¹ * ((h * h) ^ l)⁻¹ := by rw [hinv]
        _ = ((h * h) ^ l * d * ((h * h) ^ l)⁻¹)⁻¹ := by group
        _ = d⁻¹ := by rw [hcl]
    rw [hhm] at key
    have h5 : d = d⁻¹ := by simpa using key
    apply hdd.2
    have : d * d = 1 := by
      have := congrArg (d * ·) h5.symm
      simpa using this.symm
    exact this

end Odd

section NCentral

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)

include c hD hd4 in
theorem oTwoUpper_le_centralizer_d : oTwoUpper (mcOf T) ≤ Subgroup.centralizer ({d} : Set G) := by
  refine (Subgroup.closure_le _).mpr fun w hw => ?_
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hwH : w ∈ mcOf T := hw.1
  have hQ : w * d * w⁻¹ ∈ qOf T :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hwH) d).mp hd.1
  have hC : w * d * w⁻¹ ∈ Subgroup.centralizer (uOfL22 T M : Set G) :=
    centralizer_conj_mem (c.hHU hwH) hd.2
  have hmem : w * d * w⁻¹ ∈ Subgroup.zpowers d := hD ▸ ⟨hQ, hC⟩
  have h := conj_fix_of_odd hd4 hw.2 hmem
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have := congrArg (· * w) h
  simpa [mul_assoc] using this

end NCentral


end S143

end CFSG.Quasithin
