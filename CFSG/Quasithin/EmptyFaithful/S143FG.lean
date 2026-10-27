module

public import CFSG.Quasithin.EmptyFaithful.S143FA
public import CFSG.Quasithin.EmptyFaithful.S143FE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section TCls

variable {G : Type} [Group G] {Z U : Subgroup G} (hUN : U ≤ Subgroup.normalizer (Z : Set G))

@[expose] noncomputable def tclsE {u : G} (hu : u ∈ U) : ↥(tildeOf Z U) :=
  ⟨secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩,
    secMk_mem_secImg (X := U) (x := ⟨u, hUN hu⟩) hu⟩

include hUN

theorem tclsE_val {u : G} (hu : u ∈ U) :
    ((tclsE hUN hu : ↥(tildeOf Z U)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩ := rfl

theorem tclsE_eq_one_iff {u : G} (hu : u ∈ U) : tclsE hUN hu = 1 ↔ u ∈ Z := by
  rw [Subtype.ext_iff]
  exact secMk_eq_one_iff

theorem tclsE_eq_iff {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) :
    tclsE hUN hu = tclsE hUN hu' ↔ u⁻¹ * u' ∈ Z := by
  rw [Subtype.ext_iff]
  exact secMk_eq_secMk_iff

theorem tclsE_mul {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) :
    tclsE hUN (U.mul_mem hu hu') = tclsE hUN hu * tclsE hUN hu' := by
  apply Subtype.ext
  exact map_mul (secMk (Subgroup.normalizer (Z : Set G)) Z) ⟨u, hUN hu⟩ ⟨u', hUN hu'⟩

theorem actTilde_tclsE {H : Subgroup G} (hHN : H ≤ Subgroup.normalizer (Z : Set G))
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (h' : ↥H) {u : G} (hu : u ∈ U)
    (hu' : (h' : G) * u * (h' : G)⁻¹ ∈ U) :
    actTilde Z U H hHN hHU h' (tclsE hUN hu) = tclsE hUN hu' := by
  apply Subtype.ext
  rw [actTilde_apply]
  show secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h', hHN h'.2⟩ *
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩ *
      (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h', hHN h'.2⟩)⁻¹ =
    secMk (Subgroup.normalizer (Z : Set G)) Z ⟨(h' : G) * u * (h' : G)⁻¹, hUN hu'⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem tclsE_congr {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) (h : u = u') :
    tclsE hUN hu = tclsE hUN hu' := by
  subst h
  rfl

end TCls

section Action

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

abbrev UT (T M : Subgroup G) : Type :=
  ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))

omit [Finite G] in
theorem hHN_of (T : Subgroup G) :
    mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.centralizer_le_normalizer _

include c

theorem Counter.hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
  c.h1281.g1_le_normalizer_uOfL22

theorem Counter.hUN : uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  c.h1281.uOfL22_le_g1.trans (hHN_of T)

@[expose] noncomputable def Counter.actK : ↥(mcOf T) →* MulAut (UT T M) :=
  actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) (hHN_of T) c.hHU

theorem Counter.actK_ker_map : c.actK.ker.map (mcOf T).subtype = qOf T :=
  ker_actTilde_map c (hHN_of T) c.hHU c.hUN

theorem Counter.mem_qOf_of_actK_eq_one {x : ↥(mcOf T)} (hx : c.actK x = 1) : (x : G) ∈ qOf T := by
  rw [← c.actK_ker_map]
  exact ⟨x, MonoidHom.mem_ker.mpr hx, rfl⟩

theorem Counter.actK_eq_one_of_mem_qOf {x : ↥(mcOf T)} (hx : (x : G) ∈ qOf T) : c.actK x = 1 := by
  rw [← c.actK_ker_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact MonoidHom.mem_ker.mp hy

theorem Counter.actK_range : c.actK.range =
    autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
  range_actTilde _ _ _ _ _

end Action

section Identify

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.exists_Ac_eq {A : Subgroup G} {t : G} (hb : Concl18b T M A t) :
    ∃ (r : G) (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1),
      A = c.Ac hrW hrV hr2 := by
  have h := c.h1281
  have key : ∀ (r' : G) (hrW' : r' ∈ Hyp1281Two.wOfU T M) (hrV' : r' ∉ VZ T M)
      (hr2' : r' * r' = 1), r' ∈ A → A = c.Ac hrW' hrV' hr2' := by
    intro r' hrW' hrV' hr2' hrA
    have hVA : VZ T M ≤ A := hb.v_eq_inf ▸ inf_le_left
    have hgN : g ∈ Subgroup.normalizer (A : Set G) :=
      hb.normal_A (Subgroup.mem_sup_left c.g_mem_iTwo)
    have hg1 : g * r' * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgN r').mp hrA
    have hg2 : g * g * r' * (g * g)⁻¹ ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp hgN (g * r' * g⁻¹)).mp hg1
      have e : g * (g * r' * g⁻¹) * g⁻¹ = g * g * r' * (g * g)⁻¹ := by group
      rwa [e] at this
    have hle : c.Ac hrW' hrV' hr2' ≤ A := by
      intro x hx
      obtain ⟨e, he, hcases⟩ := c.mem_Ac_cases hrW' hrV' hr2' hx
      have heA := hVA he
      rcases hcases with rfl | rfl | rfl | rfl
      · exact heA
      · exact A.mul_mem hrA heA
      · exact A.mul_mem hg1 heA
      · exact A.mul_mem hg2 heA
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [c.card_Ac hrW' hrV' hr2', hb.A_card])).symm
  obtain ⟨r, hrW, hrV, hr2⟩ := Counter.exists_involution_wOfU c
  have hBle : VZ T M ⊔ Subgroup.zpowers r ≤ c.Ac hrW hrV hr2 :=
    sup_le (c.VZ_le_Ac hrW hrV hr2) ((Subgroup.zpowers_le).2 (c.r_mem_Ac hrW hrV hr2))
  have hBR : VZ T M ⊔ Subgroup.zpowers r ≤ rOf T M := hBle.trans (c.Ac_le_rOf hrW hrV hr2)
  have hBe : IsElemAbelian 2 (VZ T M ⊔ Subgroup.zpowers r) := by
    have hsq : ∀ x ∈ VZ T M ⊔ Subgroup.zpowers r, x * x = 1 := fun x hx =>
      c.sq_Ac hrW hrV hr2 (hBle hx)
    exact ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_sq_eq_one hsq a.2 b.2)⟩⟩, fun x hx => by
      rw [sq]; exact hsq x hx⟩
  have hrB : r ∈ VZ T M ⊔ Subgroup.zpowers r := Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
  rcases hb.maximal _ hBR hBe with hA | hAt
  · exact ⟨r, hrW, hrV, hr2, key r hrW hrV hr2 (hA hrB)⟩
  · have hr' : t * r * t⁻¹ ∈ A := mem_conjSubgroup_iff.mp (hAt hrB)
    have htT := hb.t_mem
    have hW' : t * r * t⁻¹ ∈ Hyp1281Two.wOfU T M :=
      (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_wOfU htT) r).mp hrW
    have hV' : t * r * t⁻¹ ∉ VZ T M := by
      intro hmem
      apply hrV
      have hN : t⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
        Subgroup.inv_mem _ (c.T_mem_normalizer_VZ htT)
      have := (Subgroup.mem_normalizer_iff.mp hN _).mp hmem
      have e : t⁻¹ * (t * r * t⁻¹) * t⁻¹⁻¹ = r := by group
      rwa [e] at this
    have h2' : (t * r * t⁻¹) * (t * r * t⁻¹) = 1 := by
      have e : (t * r * t⁻¹) * (t * r * t⁻¹) = t * (r * r) * t⁻¹ := by group
      rw [e, hr2]; group
    exact ⟨t * r * t⁻¹, hW', hV', h2', key _ hW' hV' h2' hr'⟩

end Identify

section Alpha

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.wOfU_le_qOf : Hyp1281Two.wOfU T M ≤ qOf T := fun w hw => by
  have : w ∈ rOf T M ⊓ qOf T := by
    rw [rOf_inf_qOf c]; exact hw
  exact this.2

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include hrW hrV hr2

theorem Counter.Ac_le_mcOf : c.Ac hrW hrV hr2 ≤ mcOf T :=
  (c.Ac_le_rOf hrW hrV hr2).trans (rOf_le_mcOf c)

theorem Counter.r1_mem_mcOf : g * r * g⁻¹ ∈ mcOf T :=
  c.Ac_le_mcOf hrW hrV hr2 (c.r1_mem_Ac hrW hrV hr2)

@[expose] noncomputable def Counter.alphaOf : MulAut (UT T M) :=
  c.actK ⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩

theorem Counter.r1_not_mem_qOf : g * r * g⁻¹ ∉ qOf T := by
  intro hq
  have hR : g * r * g⁻¹ ∈ rOf T M := c.Ac_le_rOf hrW hrV hr2 (c.r1_mem_Ac hrW hrV hr2)
  have hW : g * r * g⁻¹ ∈ Hyp1281Two.wOfU T M := by
    have : g * r * g⁻¹ ∈ rOf T M ⊓ qOf T := ⟨hR, hq⟩
    rwa [rOf_inf_qOf c] at this
  apply hrV
  rw [← E_eq_VZ c]
  exact ⟨hrW, mem_rconj.mpr hW⟩

theorem Counter.alphaOf_ne_one : c.alphaOf hrW hrV hr2 ≠ 1 := fun he =>
  c.r1_not_mem_qOf hrW hrV hr2 (c.mem_qOf_of_actK_eq_one he)

theorem Counter.alphaOf_sq : c.alphaOf hrW hrV hr2 * c.alphaOf hrW hrV hr2 = 1 := by
  have h1 : (⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩ : ↥(mcOf T)) *
      ⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩ = 1 :=
    Subtype.ext (c.sq_Ac hrW hrV hr2 (c.r1_mem_Ac hrW hrV hr2))
  unfold Counter.alphaOf
  rw [← map_mul, h1, map_one]

theorem Counter.alphaOf_mem_T :
    c.alphaOf hrW hrV hr2 ∈ (T.subgroupOf (mcOf T)).map c.actK := by
  have hRT : rOf T M ≤ T := rOf_le_T_of_hyp c.h1281
  refine ⟨⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr
    (hRT (c.Ac_le_rOf hrW hrV hr2 (c.r1_mem_Ac hrW hrV hr2)))

theorem Counter.actK_Ac {a : G} (ha : a ∈ c.Ac hrW hrV hr2) :
    c.actK ⟨a, c.Ac_le_mcOf hrW hrV hr2 ha⟩ = 1 ∨
      c.actK ⟨a, c.Ac_le_mcOf hrW hrV hr2 ha⟩ = c.alphaOf hrW hrV hr2 := by
  have hWQ := c.wOfU_le_qOf
  have hV1 : ∀ (e : G) (he : e ∈ VZ T M) (he' : e ∈ mcOf T), c.actK ⟨e, he'⟩ = 1 := fun e he he' =>
    c.actK_eq_one_of_mem_qOf (hWQ (Hyp1281Two.VZ_le_wOfU c.h1281 he))
  have hr1 : c.actK ⟨r, c.Ac_le_mcOf hrW hrV hr2 (c.r_mem_Ac hrW hrV hr2)⟩ = 1 :=
    c.actK_eq_one_of_mem_qOf (hWQ hrW)
  have hmul : ∀ (x y : G) (hx : x ∈ mcOf T) (hy : y ∈ mcOf T),
      c.actK ⟨x * y, (mcOf T).mul_mem hx hy⟩ = c.actK ⟨x, hx⟩ * c.actK ⟨y, hy⟩ := fun x y hx hy => by
    rw [← map_mul]; rfl
  have hα1 : c.actK ⟨g * g * r * (g * g)⁻¹, c.Ac_le_mcOf hrW hrV hr2 (c.r2_mem_Ac hrW hrV hr2)⟩ =
      c.alphaOf hrW hrV hr2 := by
    have hnorm := c.norm_mem_VZ hrW hrV hr2
    have hnH : r * (g * r * g⁻¹) * (g * g * r * (g * g)⁻¹) ∈ mcOf T :=
      (mcOf T).mul_mem ((mcOf T).mul_mem
        (c.Ac_le_mcOf hrW hrV hr2 (c.r_mem_Ac hrW hrV hr2)) (c.r1_mem_mcOf hrW hrV hr2))
        (c.Ac_le_mcOf hrW hrV hr2 (c.r2_mem_Ac hrW hrV hr2))
    have h1 := c.actK_eq_one_of_mem_qOf (x := ⟨r * (g * r * g⁻¹) * (g * g * r * (g * g)⁻¹), hnH⟩)
      (hWQ (Hyp1281Two.VZ_le_wOfU c.h1281 hnorm))
    have e : (⟨r * (g * r * g⁻¹) * (g * g * r * (g * g)⁻¹), hnH⟩ : ↥(mcOf T)) =
        ⟨r, c.Ac_le_mcOf hrW hrV hr2 (c.r_mem_Ac hrW hrV hr2)⟩ *
          ⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩ *
          ⟨g * g * r * (g * g)⁻¹, c.Ac_le_mcOf hrW hrV hr2 (c.r2_mem_Ac hrW hrV hr2)⟩ := rfl
    rw [e, map_mul, map_mul, hr1, one_mul] at h1
    have hsq := c.alphaOf_sq hrW hrV hr2
    have h2 : c.alphaOf hrW hrV hr2 * c.actK ⟨g * g * r * (g * g)⁻¹, _⟩ = 1 := h1
    have h3 : c.actK ⟨g * g * r * (g * g)⁻¹, c.Ac_le_mcOf hrW hrV hr2
        (c.r2_mem_Ac hrW hrV hr2)⟩ = (c.alphaOf hrW hrV hr2)⁻¹ := eq_inv_of_mul_eq_one_right h2
    rw [h3]
    exact inv_eq_of_mul_eq_one_right hsq
  obtain ⟨e, he, hcases⟩ := c.mem_Ac_cases hrW hrV hr2 ha
  have heH : e ∈ mcOf T := c.Ac_le_mcOf hrW hrV hr2 (c.VZ_le_Ac hrW hrV hr2 he)
  rcases hcases with rfl | rfl | rfl | rfl
  · left; exact hV1 _ he heH
  · left
    rw [hmul r e (c.Ac_le_mcOf hrW hrV hr2 (c.r_mem_Ac hrW hrV hr2)) heH, hr1, hV1 _ he heH,
      one_mul]
  · right
    rw [hmul (g * r * g⁻¹) e (c.r1_mem_mcOf hrW hrV hr2) heH, hV1 _ he heH, mul_one]
    rfl
  · right
    rw [hmul (g * g * r * (g * g)⁻¹) e
      (c.Ac_le_mcOf hrW hrV hr2 (c.r2_mem_Ac hrW hrV hr2)) heH, hV1 _ he heH, mul_one]
    exact hα1

theorem Counter.alphaOf_tclsE :
    c.alphaOf hrW hrV hr2 (tclsE c.hUN hrW.1) = tclsE c.hUN hrW.1 := by
  have hcomm : g * r * g⁻¹ * r = r * (g * r * g⁻¹) :=
    mul_comm_of_sq_eq_one (fun x hx => c.sq_Ac hrW hrV hr2 hx) (c.r1_mem_Ac hrW hrV hr2)
      (c.r_mem_Ac hrW hrV hr2)
  have hconj : (g * r * g⁻¹) * r * (g * r * g⁻¹)⁻¹ = r := by
    calc (g * r * g⁻¹) * r * (g * r * g⁻¹)⁻¹ = (r * (g * r * g⁻¹)) * (g * r * g⁻¹)⁻¹ := by
          rw [hcomm]
      _ = r := by group
  have hrU' : (g * r * g⁻¹) * r * (g * r * g⁻¹)⁻¹ ∈ uOfL22 T M := by rw [hconj]; exact hrW.1
  have := actTilde_tclsE c.hUN (hHN_of T) c.hHU ⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩ hrW.1 hrU'
  exact this.trans (tclsE_congr c.hUN hrU' hrW.1 hconj)

theorem Counter.card_inf_qOf_Ac : Nat.card ↥(c.Ac hrW hrV hr2 ⊓ qOf T) = 8 := by
  have hker := c.actK_ker_map
  have h1 := card_map_mul_card_inf_ker (c.Ac_le_mcOf hrW hrV hr2) c.actK
  rw [hker, c.card_Ac hrW hrV hr2] at h1
  have himg : ((c.Ac hrW hrV hr2).subgroupOf (mcOf T)).map c.actK =
      Subgroup.zpowers (c.alphaOf hrW hrV hr2) := by
    apply le_antisymm
    · rintro y ⟨⟨a, haH⟩, hamem, rfl⟩
      have ha : a ∈ c.Ac hrW hrV hr2 := hamem
      rcases c.actK_Ac hrW hrV hr2 ha with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
    · refine (Subgroup.zpowers_le).2 ?_
      exact ⟨⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩,
        Subgroup.mem_subgroupOf.mpr (c.r1_mem_Ac hrW hrV hr2), rfl⟩
  have hord : orderOf (c.alphaOf hrW hrV hr2) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact c.alphaOf_sq hrW hrV hr2) (c.alphaOf_ne_one hrW hrV hr2)
  rw [himg, Nat.card_zpowers, hord] at h1
  omega

theorem Counter.Ac_inf_qOf_le_uOfL22 : c.Ac hrW hrV hr2 ⊓ qOf T ≤ uOfL22 T M := fun x hx => by
  have : x ∈ rOf T M ⊓ qOf T := ⟨c.Ac_le_rOf hrW hrV hr2 hx.1, hx.2⟩
  rw [rOf_inf_qOf c] at this
  exact Hyp1281Two.wOfU_le_uOfL22 T M this

theorem Counter.VZ_le_Ac_inf_qOf : VZ T M ≤ c.Ac hrW hrV hr2 ⊓ qOf T := fun _ he =>
  ⟨c.VZ_le_Ac hrW hrV hr2 he, c.wOfU_le_qOf (Hyp1281Two.VZ_le_wOfU c.h1281 he)⟩

end Alpha

end S143

end CFSG.Quasithin
