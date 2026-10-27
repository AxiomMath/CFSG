module

public import CFSG.Quasithin.EmptyFaithful.S143FM
public import CFSG.Quasithin.EmptyFaithful.S143EE
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabNatural

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section TCls

variable {G : Type} [Group G] {Z U : Subgroup G} (hUN : U ≤ Subgroup.normalizer (Z : Set G))

noncomputable def tcls {u : G} (hu : u ∈ U) : ↥(tildeOf Z U) :=
  ⟨secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩,
    secMk_mem_secImg (X := U) (x := ⟨u, hUN hu⟩) hu⟩

include hUN

theorem tcls_eq_one_iff {u : G} (hu : u ∈ U) : tcls hUN hu = 1 ↔ u ∈ Z := by
  rw [Subtype.ext_iff]
  exact secMk_eq_one_iff

theorem tcls_eq_iff {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) :
    tcls hUN hu = tcls hUN hu' ↔ u⁻¹ * u' ∈ Z := by
  rw [Subtype.ext_iff]
  exact secMk_eq_secMk_iff

theorem tcls_mul {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) :
    tcls hUN (U.mul_mem hu hu') = tcls hUN hu * tcls hUN hu' := by
  apply Subtype.ext
  exact map_mul (secMk (Subgroup.normalizer (Z : Set G)) Z) ⟨u, hUN hu⟩ ⟨u', hUN hu'⟩

theorem actTilde_tcls {H : Subgroup G} (hHN : H ≤ Subgroup.normalizer (Z : Set G))
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (h' : ↥H) {u : G} (hu : u ∈ U)
    (hu' : (h' : G) * u * (h' : G)⁻¹ ∈ U) :
    actTilde Z U H hHN hHU h' (tcls hUN hu) = tcls hUN hu' := by
  apply Subtype.ext
  rw [actTilde_apply]
  show secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h', hHN h'.2⟩ *
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩ *
      (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h', hHN h'.2⟩)⁻¹ =
    secMk (Subgroup.normalizer (Z : Set G)) Z ⟨(h' : G) * u * (h' : G)⁻¹, hUN hu'⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem tcls_congr {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) (h : u = u') :
    tcls hUN hu = tcls hUN hu' := by
  subst h
  rfl

end TCls

section T4

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.conj_ne_coset {t : G} (htT : t ∈ T) (htRQ : t ∉ rOf T M ⊔ qOf T) :
    ∀ e ∈ VZ T M, t * r * t⁻¹ ≠ r * e := by
  intro e he hte
  have h := c.h1281
  have hg := c.goodElt
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  have hHN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    h.uOfL22_le_g1.trans hHN
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hTM : T ≤ M := c.hyp.m_max.1.2
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    { (inferInstance : Group ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) with
      mul_comm := fun a b => (tilde_isMulCommutative h).is_comm.comm a b }
  obtain ⟨L₁, L₂, t₀, hS, hsing⟩ := exists_ofourStruct_of_plusType
    (W := ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) (q := q)
    (tilde_mul_self h) hq4 hq1 hq2 hq3
  set ρ := actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) hHN hHU with hρ
  have hrange : ρ.range = orthogonalGroupOf q :=
    (range_actTilde _ _ _ hHN hHU).trans hq6
  have hT' : IsSylowTwoOf ((T.subgroupOf (mcOf T)).map ρ) (orthogonalGroupOf q) := by
    have := isSylowTwoOf_map_range' (sylow_G1_of_hyp h) ρ
    rwa [hrange] at this
  have hRT : rOf T M ≤ T := rOf_le_T_of_hyp h
  have hR''T : ((rOf T M).subgroupOf (mcOf T)).map ρ ≤ (T.subgroupOf (mcOf T)).map ρ :=
    Subgroup.map_mono fun x hx => hRT hx
  have hR''card : Nat.card ↥(((rOf T M).subgroupOf (mcOf T)).map ρ) = 4 := by
    have h1 : Nat.card ↥(((rOf T M).subgroupOf (mcOf T)).map ρ) *
        Nat.card ↥(rOf T M ⊓ ρ.ker.map (mcOf T).subtype) = Nat.card (rOf T M) :=
      card_map_mul_card_inf_ker (rOf_le_mcOf c) ρ
    have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
    rw [ker_actTilde_map c hHN hHU hUN, rOf_inf_qOf c, hW, card_rOf c] at h1
    omega
  obtain ⟨z, a, hzZ, hz1, ha, haV, haZ, hzz, haa, hza, hga, hgza, hcases⟩ :=
    exists_three_cycle h hg
  have hrU : r ∈ uOfL22 T M := hrW.1
  have haU : a ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M haV
  have hZV : ∀ y ∈ quasithinOmegaOneCenter T, y ∈ VZ T M := fun y hy =>
    Hyp1281Two.omegaOneCenter_le_VZ T M hy
  have hzV : z ∈ VZ T M := hZV z hzZ
  have hVU : ∀ y ∈ VZ T M, y ∈ uOfL22 T M := fun y hy => Hyp1281Two.VZ_le_uOfL22 T M hy
  set x := tcls hUN hrU with hx
  set v := tcls hUN haU with hv
  have hclsV : ∀ (e' : G) (he' : e' ∈ VZ T M), tcls hUN (hVU e' he') = 1 ∨
      tcls hUN (hVU e' he') = v := by
    intro e' he'
    rcases hcases e' he' with rfl | rfl | rfl | rfl
    · left; exact (tcls_eq_one_iff hUN _).mpr (quasithinOmegaOneCenter T).one_mem
    · left; exact (tcls_eq_one_iff hUN _).mpr hzZ
    · right; rfl
    · right
      have hm := tcls_mul hUN (hVU z hzV) haU
      have e1 : tcls hUN (hVU (z * a) he') =
          tcls hUN ((uOfL22 T M).mul_mem (hVU z hzV) haU) := rfl
      rw [e1, hm, (tcls_eq_one_iff hUN _).mpr hzZ, one_mul]
  have hv1 : v ≠ 1 := fun he => haZ ((tcls_eq_one_iff hUN haU).mp he)
  have hx1 : x ≠ 1 := fun he => hrV (hZV _ ((tcls_eq_one_iff hUN hrU).mp he))
  have hxv : x ≠ v := by
    intro he
    have h1 : r⁻¹ * a ∈ VZ T M := hZV _ ((tcls_eq_iff hUN hrU haU).mp he)
    apply hrV
    have h2 : r⁻¹ ∈ VZ T M := by
      have := (VZ T M).mul_mem h1 ((VZ T M).inv_mem haV)
      simpa using this
    simpa using (VZ T M).inv_mem h2
  have hxq : q x = 0 := (hq5 x.1 x.2 ⟨r, hUN hrU⟩ hrU rfl).mpr (by rw [sq]; exact hr2)
  have har : a * r = r * a := Subgroup.mem_centralizer_iff.mp hrW.2 a haV
  have hvxq : q (v * x) = 0 := by
    have hu : a * r ∈ uOfL22 T M := (uOfL22 T M).mul_mem haU hrU
    have e : v * x = tcls hUN hu := (tcls_mul hUN haU hrU).symm
    rw [e]
    refine (hq5 _ _ ⟨a * r, hUN hu⟩ hu rfl).mpr ?_
    rw [sq]
    calc a * r * (a * r) = a * (r * a) * r := by group
      _ = a * (a * r) * r := by rw [← har]
      _ = (a * a) * (r * r) := by group
      _ = 1 := by rw [haa, hr2, one_mul]
  have hvfix : ∀ y ∈ (T.subgroupOf (mcOf T)).map ρ, y v = v := by
    intro y hy
    obtain ⟨τ', hτ', rfl⟩ := Subgroup.mem_map.mp hy
    have hτT : (τ' : G) ∈ T := hτ'
    have hτa : (τ' : G) * a * (τ' : G)⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (hHU τ'.2) a).mp haU
    rw [hv, actTilde_tcls hUN hHN hHU τ' haU hτa]
    refine (tcls_eq_iff hUN hτa haU).mpr ?_
    have hτN : (τ' : G) ∈ Subgroup.normalizer (VZ T M : Set G) := by
      rw [h.normalizer_VZ]; exact hTM hτT
    have hτaV : (τ' : G) * a * (τ' : G)⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp hτN a).mp haV
    have hτz : (τ' : G) * z * (τ' : G)⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp τ'.2 z hzZ
      rw [← this]; group
    rcases hcases _ hτaV with he | he | he | he
    · exfalso
      apply haZ
      have : a = (τ' : G)⁻¹ * ((τ' : G) * a * (τ' : G)⁻¹) * (τ' : G) := by group
      rw [this, he]
      simp [(quasithinOmegaOneCenter T).one_mem]
    · exfalso
      apply haZ
      have : a = (τ' : G)⁻¹ * ((τ' : G) * a * (τ' : G)⁻¹) * (τ' : G) := by group
      rw [this, he]
      have h2 : (τ' : G)⁻¹ * z * (τ' : G) = z := by
        calc (τ' : G)⁻¹ * z * (τ' : G) = (τ' : G)⁻¹ * ((τ' : G) * z * (τ' : G)⁻¹) * (τ' : G) := by
              rw [hτz]
          _ = z := by group
      rw [h2]; exact hzZ
    · rw [he, inv_mul_cancel]; exact (quasithinOmegaOneCenter T).one_mem
    · rw [he]
      have : (z * a)⁻¹ * a = z⁻¹ := by rw [hza]; group
      rw [this]; exact (quasithinOmegaOneCenter T).inv_mem hzZ
  have hR : ∀ y ∈ ((rOf T M).subgroupOf (mcOf T)).map ρ, y x = x ∨ y x = x * v := by
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    have hy₀R : (y₀ : G) ∈ rOf T M := hy₀
    have hy₀S : (y₀ : G) ∈ pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M) := by
      rw [← rOf_eq_pCoreOf_sup c]; exact hy₀R
    have hrS : r ∈ pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M) :=
      h.wOfU_le_pCoreOf c.nonab hg hrW
    have hcomm := h.commutator_mem_inf_of_mem_pCoreOf c.nonab hg
      ((pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M)).inv_mem hrS) hy₀S
    set e' : G := r⁻¹ * ((y₀ : G) * r * (y₀ : G)⁻¹) with he'
    have he'V : e' ∈ VZ T M := by
      rw [← E_eq_VZ c]
      have e : r⁻¹ * (y₀ : G) * r⁻¹⁻¹ * (y₀ : G)⁻¹ = e' := by rw [he']; group
      rwa [e] at hcomm
    have hconj : (y₀ : G) * r * (y₀ : G)⁻¹ = r * e' := by rw [he']; group
    have hyU : (y₀ : G) * r * (y₀ : G)⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (hHU y₀.2) r).mp hrU
    have hreU : r * e' ∈ uOfL22 T M := (uOfL22 T M).mul_mem hrU (hVU e' he'V)
    rw [hx, actTilde_tcls hUN hHN hHU y₀ hrU hyU, tcls_congr hUN hyU hreU hconj,
      tcls_mul hUN hrU (hVU e' he'V)]
    rcases hclsV e' he'V with h1 | h1
    · left; rw [h1, mul_one]
    · right; rw [h1]
  have hρtT : ρ ⟨t, hTH htT⟩ ∈ (T.subgroupOf (mcOf T)).map ρ := ⟨⟨t, hTH htT⟩, htT, rfl⟩
  have hρtR : ρ ⟨t, hTH htT⟩ ∉ ((rOf T M).subgroupOf (mcOf T)).map ρ := by
    rintro ⟨y₀, hy₀, hyt⟩
    have h1 : ρ (⟨t, hTH htT⟩ * y₀⁻¹) = 1 := by
      rw [map_mul, map_inv, hyt, mul_inv_cancel]
    have h2 : (((⟨t, hTH htT⟩ * y₀⁻¹ : ↥(mcOf T))) : G) ∈ qOf T := by
      rw [← centralizerMod_eq_qOf c]
      exact ⟨(⟨t, hTH htT⟩ * y₀⁻¹ : ↥(mcOf T)).2, hHN (⟨t, hTH htT⟩ * y₀⁻¹ : ↥(mcOf T)).2,
        (actTilde_eq_one_iff _ _ _ hHN hHU hUN _).mp h1⟩
    apply htRQ
    have e : t = (t * (y₀ : G)⁻¹) * (y₀ : G) := by group
    rw [e]
    exact (rOf T M ⊔ qOf T).mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hy₀)
  have key := not_stabilizes_coset hS hsing (tilde_mul_self h) hT' hR''T hR''card hv1 hvfix hx1
    hxv hxq hvxq hR (ρ ⟨t, hTH htT⟩) hρtT hρtR
  have htr : t * r * t⁻¹ ∈ uOfL22 T M :=
    (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_uOfL22 htT) r).mp hrU
  have hρx : ρ ⟨t, hTH htT⟩ x = tcls hUN htr :=
    actTilde_tcls hUN hHN hHU ⟨t, hTH htT⟩ hrU htr
  have hreU : r * e ∈ uOfL22 T M := (uOfL22 T M).mul_mem hrU (hVU e he)
  rw [tcls_congr hUN htr hreU hte, tcls_mul hUN hrU (hVU e he)] at hρx
  rcases hclsV e he with h1 | h1
  · exact key.1 (by rw [hρx, h1, mul_one])
  · exact key.2 (by rw [hρx, h1])

end T4

end S143

end CFSG.Quasithin
