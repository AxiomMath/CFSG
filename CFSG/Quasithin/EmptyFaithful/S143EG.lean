module

public import CFSG.Quasithin.EmptyFaithful.S143EF
public import CFSG.Quasithin.EmptyFaithful.S143EE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

noncomputable def actH (h : Hyp1281Two G T M (yOfL22 T M)) :
    ↥(mcOf T) →* MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
  actTilde _ _ _ (Subgroup.centralizer_le_normalizer _) h.g1_le_normalizer_uOfL22

theorem actH_range (h : Hyp1281Two G T M (yOfL22 T M)) :
    (actH h).range = autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
  range_actTilde _ _ _ _ _

theorem actH_ker_map {g : G} (c : Counter T M g) :
    (actH c.h1281).ker.map (mcOf T).subtype = qOf T :=
  ker_actTilde_map c _ _ (c.h1281.uOfL22_le_g1.trans (Subgroup.centralizer_le_normalizer _))

theorem actH_mem_range (h : Hyp1281Two G T M (yOfL22 T M)) (x : ↥(mcOf T)) :
    actH h x ∈ autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) := by
  rw [← actH_range h]
  exact ⟨x, rfl⟩

theorem mem_qOf_of_actH_eq_one {g : G} (c : Counter T M g) {x : ↥(mcOf T)}
    (hx : actH c.h1281 x = 1) : (x : G) ∈ qOf T := by
  rw [← actH_ker_map c]
  exact ⟨x, MonoidHom.mem_ker.mpr hx, rfl⟩

section Commutator

variable {g : G} (c : Counter T M g)

include c

theorem commutator_rOf_qOf_mem {r q : G} (hr : r ∈ rOf T M) (hq : q ∈ qOf T) :
    r * q * r⁻¹ * q⁻¹ ∈ uOfL22 T M := by
  have hrH : r ∈ mcOf T := rOf_le_mcOf c hr
  have h1 : r * q * r⁻¹ * q⁻¹ ∈ rOf T M := by
    have := (Subgroup.mem_normalizer_iff.mp (qOf_le_normalizer_rOf c hq) r⁻¹).mp
      ((rOf T M).inv_mem hr)
    have e : r * q * r⁻¹ * q⁻¹ = r * (q * r⁻¹ * q⁻¹) := by group
    rw [e]
    exact (rOf T M).mul_mem hr this
  have h2 : r * q * r⁻¹ * q⁻¹ ∈ qOf T := by
    have hn := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (mcOf T) hrH) q).mp hq
    exact (qOf T).mul_mem hn ((qOf T).inv_mem hq)
  have h3 : r * q * r⁻¹ * q⁻¹ ∈ rOf T M ⊓ qOf T := ⟨h1, h2⟩
  rw [rOf_inf_qOf c] at h3
  exact Hyp1281Two.wOfU_le_uOfL22 T M h3

end Commutator

section Inverting

variable {g : G} (c : Counter T M g)

include c

theorem exists_inverting :
    ∃ y : ↥(mcOf T), (y : G) ∈ rOf T M ∧ ∀ x : ↥(mcOf T), Odd (orderOf x) →
      actH c.h1281 y * actH c.h1281 x * (actH c.h1281 y)⁻¹ = (actH c.h1281 x)⁻¹ := by
  have h := c.h1281
  have hF := c.oddFacts
  set ρ := actH h with hρ
  have hT' : IsSylowTwoOf ((T.subgroupOf (mcOf T)).map ρ)
      (autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
        (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) := by
    have := isSylowTwoOf_map_range' (sylow_G1_of_hyp h) ρ
    rwa [actH_range h] at this
  obtain ⟨r₀, hr₀T, hr₀1, hr₀cen, hr₀inv⟩ := hF.central _ hT'
  have hRT : rOf T M ≤ T := rOf_le_T_of_hyp h
  set R' : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :=
    ((rOf T M).subgroupOf (mcOf T)).map ρ with hR'
  set T' := (T.subgroupOf (mcOf T)).map ρ with hT'def
  have hR'T : R' ≤ T' := Subgroup.map_mono fun x hx => hRT hx
  have hR'card : Nat.card R' = 4 := by
    have h1 : Nat.card R' * Nat.card ↥(rOf T M ⊓ ρ.ker.map (mcOf T).subtype) =
        Nat.card (rOf T M) := card_map_mul_card_inf_ker (rOf_le_mcOf c) ρ
    have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
    rw [actH_ker_map c, rOf_inf_qOf c, hW, card_rOf c] at h1
    omega
  have hT'card : Nat.card T' = 8 := hF.card_sylow _ hT'
  have hidx : (R'.subgroupOf T').index = 2 := by
    have h1 := Subgroup.relIndex_mul_card R' T'
    rw [inf_eq_left.mpr hR'T, hR'card, hT'card] at h1
    exact (by omega : R'.relIndex T' = 2)
  have : (R'.subgroupOf T').Normal := Subgroup.normal_of_index_eq_two hidx
  have hne : R'.subgroupOf T' ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (R'.subgroupOf T') = 4 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'T).toEquiv).trans hR'card
    rw [hbot, Subgroup.card_bot] at h1
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T' := hT'.2.1.isNilpotent
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨a', ha'mem⟩, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  have haR : a'.1 ∈ R' := ha'mem.1
  have hacen : ∀ x ∈ T', x * a'.1 = a'.1 * x := fun x hx =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp ha'mem.2 ⟨x, hx⟩)
  have ha1 : a'.1 ≠ 1 := by
    intro he
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    exact he
  have hr₀R : r₀ ∈ R' := by
    rcases hr₀cen _ a'.2 hacen with he | he
    · exact absurd he ha1
    · rw [← he]; exact haR
  obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp hr₀R
  refine ⟨y, hy, fun x hx => ?_⟩
  have hxodd : Odd (orderOf (ρ x)) := Odd.of_dvd_nat hx (orderOf_map_dvd ρ x)
  rw [hyr]
  exact hr₀inv _ (actH_mem_range h x) hxodd

end Inverting

section OddElements

variable {g : G} (c : Counter T M g)

include c

theorem mcOf_conj_mem_centralizerMod {h' : G} (hh : h' ∈ mcOf T) {x : G}
    (hx : x ∈ centralizerMod (uOfL22 T M) (mcOf T) (qOf T)) :
    h' * x * h'⁻¹ ∈ centralizerMod (uOfL22 T M) (mcOf T) (qOf T) := by
  obtain ⟨hxH, -, hxc⟩ := hx
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
    c.h1281.g1_le_normalizer_uOfL22
  have hconjH : h' * x * h'⁻¹ ∈ mcOf T :=
    (mcOf T).mul_mem ((mcOf T).mul_mem hh hxH) ((mcOf T).inv_mem hh)
  refine ⟨hconjH, hHU hconjH, fun q hq => ?_⟩
  have hq' : h'⁻¹ * q * h'⁻¹⁻¹ ∈ qOf T :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (mcOf T) ((mcOf T).inv_mem hh)) q).mp
      hq
  have h1 := hxc _ hq'
  have h2 : h' * (x * (h'⁻¹ * q * h'⁻¹⁻¹) * x⁻¹ * (h'⁻¹ * q * h'⁻¹⁻¹)⁻¹) * h'⁻¹ ∈
      uOfL22 T M := (Subgroup.mem_normalizer_iff.mp (hHU hh) _).mp h1
  have e : h' * (x * (h'⁻¹ * q * h'⁻¹⁻¹) * x⁻¹ * (h'⁻¹ * q * h'⁻¹⁻¹)⁻¹) * h'⁻¹ =
      (h' * x * h'⁻¹) * q * (h' * x * h'⁻¹)⁻¹ * q⁻¹ := by group
  rwa [e] at h2

theorem mcOf_le_normalizer_centralizerMod :
    mcOf T ≤ Subgroup.normalizer
      (centralizerMod (uOfL22 T M) (mcOf T) (qOf T) : Set G) := by
  intro h' hh
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => mcOf_conj_mem_centralizerMod c hh hz, fun hz => ?_⟩
  have := mcOf_conj_mem_centralizerMod c ((mcOf T).inv_mem hh) hz
  simpa [mul_assoc] using this

theorem rOf_mem_centralizerMod {r : G} (hr : r ∈ rOf T M) :
    r ∈ centralizerMod (uOfL22 T M) (mcOf T) (qOf T) :=
  ⟨rOf_le_mcOf c hr, c.h1281.g1_le_normalizer_uOfL22 (rOf_le_mcOf c hr),
    fun _ hq => commutator_rOf_qOf_mem c hr hq⟩

theorem odd_mem_centralizerMod {x : G} (hx : x ∈ mcOf T) (hodd : Odd (orderOf x)) :
    x ∈ centralizerMod (uOfL22 T M) (mcOf T) (qOf T) := by
  have h := c.h1281
  obtain ⟨y, hyR, hyinv⟩ := exists_inverting c
  set ρ := actH h with hρ
  set x' : ↥(mcOf T) := ⟨x, hx⟩ with hx'
  have hx'odd : Odd (orderOf x') := by
    rw [← Subgroup.orderOf_coe]; exact hodd
  obtain ⟨k, hk⟩ := hx'odd
  set x'' : ↥(mcOf T) := x' ^ (k + 1) with hx''
  have hsq : x'' * x'' = x' := by
    rw [hx'', ← pow_add]
    have : k + 1 + (k + 1) = orderOf x' + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hodd'' : Odd (orderOf x'') :=
    Odd.of_dvd_nat ⟨k, hk⟩ (orderOf_dvd_of_pow_eq_one (by
      rw [hx'', ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]))
  have hinv2 := hyinv x''⁻¹ (by rwa [orderOf_inv])
  set d : ↥(mcOf T) := x'' * y * x''⁻¹ * y⁻¹ with hd
  have hρd : ρ d = ρ x' := by
    rw [hd, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h3 : ρ y * (ρ x'')⁻¹ * (ρ y)⁻¹ = ρ x'' := by
      rw [map_inv, inv_inv] at hinv2
      exact hinv2
    calc ρ x'' * ρ y * (ρ x'')⁻¹ * (ρ y)⁻¹ = ρ x'' * (ρ y * (ρ x'')⁻¹ * (ρ y)⁻¹) := by group
      _ = ρ x'' * ρ x'' := by rw [h3]
      _ = ρ x' := by rw [← map_mul, hsq]
  have hdC : (d : G) ∈ centralizerMod (uOfL22 T M) (mcOf T) (qOf T) := by
    have hyC := rOf_mem_centralizerMod c hyR
    have h1 := mcOf_conj_mem_centralizerMod c (x''.2) hyC
    have h2 := (centralizerMod (uOfL22 T M) (mcOf T) (qOf T)).mul_mem h1
      ((centralizerMod (uOfL22 T M) (mcOf T) (qOf T)).inv_mem hyC)
    simpa [hd] using h2
  set q : ↥(mcOf T) := d⁻¹ * x' with hq
  have hρq : ρ q = 1 := by
    rw [hq, map_mul, map_inv, hρd, inv_mul_cancel]
  have hqQ : (q : G) ∈ qOf T := mem_qOf_of_actH_eq_one c hρq
  have hxdq : x * (q : G)⁻¹ = (d : G) := by
    have : (x : G) = (d : G) * (q : G) := by
      have e : d * q = x' := by rw [hq]; group
      exact congrArg Subtype.val e.symm
    rw [this]; group
  have hq2 : ∃ k : ℕ, (q : G) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (mcOf T) ⟨(q : G), hqQ⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine mem_of_odd_of_two_pow (K := mcOf T) (mcOf_le_normalizer_centralizerMod c) hx q.2 hodd hq2 ?_
  rw [hxdq]
  exact hdC

theorem oTwoUpper_le_centralizerMod :
    oTwoUpper (mcOf T) ≤ centralizerMod (uOfL22 T M) (mcOf T) (qOf T) :=
  (Subgroup.closure_le _).mpr fun _ hx => odd_mem_centralizerMod c hx.1 hx.2

end OddElements

section Surjective

theorem exists_mul_inv_apply_eq {W : Type*} [CommGroup W] [Finite W] (σ : MulAut W)
    (hσ : ∀ w : W, σ w = w → w = 1) (a : W) : ∃ b : W, b * (σ b)⁻¹ = a := by
  have hinj : Function.Injective (fun b : W => b * (σ b)⁻¹) := by
    intro b b' hbb'
    simp only at hbb'
    have e : σ (b * b'⁻¹) = b * b'⁻¹ := by
      rw [map_mul, map_inv]
      have h1 : b * (σ b)⁻¹ * (b' * (σ b')⁻¹)⁻¹ = 1 := by rw [hbb', mul_inv_cancel]
      have h2 : b * (σ b)⁻¹ * (b' * (σ b')⁻¹)⁻¹ = (b * b'⁻¹) * (σ b * (σ b')⁻¹)⁻¹ := by
        simp only [mul_inv_rev, inv_inv, mul_assoc, mul_comm, mul_left_comm]
      rw [h2, mul_inv_eq_one] at h1
      exact h1.symm
    have := hσ _ e
    exact mul_inv_eq_one.mp this
  exact (Finite.injective_iff_surjective.mp hinj) a

end Surjective

section ULeK

variable {g : G} (c : Counter T M g)

include c

theorem exists_eq_mul_of_mem_uOfL22 {u : G} (hu : u ∈ uOfL22 T M) :
    ∃ k ∈ oTwoUpper (mcOf T), ∃ z ∈ quasithinOmegaOneCenter T, u = k * z := by
  have h := c.h1281
  have hF := c.oddFacts
  obtain ⟨cX, hcX, hcodd, hffp⟩ := hF.exists_ffp
  set ρ := actH h with hρ
  obtain ⟨cH, hcHodd, hcH⟩ := exists_odd_lift ρ (by rw [actH_range h]; exact hcX) hcodd
  have hHN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    h.uOfL22_le_g1.trans hHN
  have hw : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) ⟨u, hUN hu⟩ ∈
      tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M) :=
    secMk_mem_secImg (X := uOfL22 T M) (x := ⟨u, hUN hu⟩) hu
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    { (inferInstance : Group ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) with
      mul_comm := fun a b => (tilde_isMulCommutative h).is_comm.comm a b }
  obtain ⟨b, hb⟩ := exists_mul_inv_apply_eq (ρ cH) (fun w hw' => hffp w (by rw [← hcH]; exact hw'))
    (⟨_, hw⟩ : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)))
  obtain ⟨x, hxU, hxb⟩ := mem_secImg.1 b.2
  have hρb := actTilde_apply (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) hHN
    h.g1_le_normalizer_uOfL22 cH b
  have hb' := congrArg Subtype.val hb
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hb'
  have hρb' : ((ρ cH b : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
      SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T)) = _ := hρb
  rw [hρb', ← hxb] at hb'
  set cN : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) := ⟨cH, hHN cH.2⟩ with hcN
  have hsec : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) (x * (cN * x * cN⁻¹)⁻¹) =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, hUN hu⟩ := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv]
    exact hb'
  have hz := secMk_eq_secMk_iff.mp hsec
  set k : G := (x : G) * ((cH : G) * (x : G) * (cH : G)⁻¹)⁻¹ with hk
  have hkK : k ∈ oTwoUpper (mcOf T) := by
    have e : k = ((x : G) * (cH : G) * (x : G)⁻¹) * (cH : G)⁻¹ := by rw [hk]; group
    rw [e]
    have hcK : (cH : G) ∈ oTwoUpper (mcOf T) :=
      mem_oTwoUpper_of_odd cH.2 (by rwa [Subgroup.orderOf_coe])
    have hxH : (x : G) ∈ mcOf T := h.uOfL22_le_g1 hxU
    exact (oTwoUpper (mcOf T)).mul_mem
      (conj_mem_oTwoUpper (Subgroup.le_normalizer hxH) hcK) ((oTwoUpper (mcOf T)).inv_mem hcK)
  refine ⟨k, hkK, k⁻¹ * u, ?_, by group⟩
  simpa [hk] using hz

theorem omegaOneCenter_le_oTwoUpper :
    quasithinOmegaOneCenter T ≤ oTwoUpper (mcOf T) := by
  have h := c.h1281
  have hU := c.nonab
  obtain ⟨a, b, hab⟩ : ∃ a b : ↥(uOfL22 T M), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hU ⟨⟨fun a b => hcon a b⟩⟩
  obtain ⟨k₁, hk₁, z₁, hz₁, he₁⟩ := exists_eq_mul_of_mem_uOfL22 c a.2
  have hz₁c : ∀ y ∈ uOfL22 T M, z₁ * y = y * z₁ := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hz₁).2 y hy).symm
  have hcomm : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ oTwoUpper (mcOf T) := by
    have e : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = k₁ * ((b : G) * k₁⁻¹ * (b : G)⁻¹) := by
      have hzb := hz₁c (b : G) b.2
      rw [he₁]
      calc k₁ * z₁ * (b : G) * (k₁ * z₁)⁻¹ * (b : G)⁻¹
          = k₁ * (z₁ * (b : G)) * z₁⁻¹ * k₁⁻¹ * (b : G)⁻¹ := by group
        _ = k₁ * ((b : G) * z₁) * z₁⁻¹ * k₁⁻¹ * (b : G)⁻¹ := by rw [hzb]
        _ = k₁ * ((b : G) * k₁⁻¹ * (b : G)⁻¹) := by group
    rw [e]
    have hbH : (b : G) ∈ mcOf T := h.uOfL22_le_g1 b.2
    exact (oTwoUpper (mcOf T)).mul_mem hk₁
      (conj_mem_oTwoUpper (Subgroup.le_normalizer hbH) ((oTwoUpper (mcOf T)).inv_mem hk₁))
  have hZ : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ quasithinOmegaOneCenter T :=
    h.commutator_mem_omegaOneCenter a.2 b.2
  have hne : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ≠ 1 := by
    intro he
    apply hab
    apply Subtype.ext
    have h1 : (a : G) * (b : G) * (a : G)⁻¹ = (b : G) := mul_inv_eq_one.mp he
    have h2 : (a : G) * (b : G) = (b : G) * (a : G) := by
      calc (a : G) * (b : G) = ((a : G) * (b : G) * (a : G)⁻¹) * (a : G) := by group
        _ = (b : G) * (a : G) := by rw [h1]
    simpa using h2
  intro z hz
  obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))).mp
    h.card_omegaOneCenter
  have h1 : (⟨_, hZ⟩ : ↥(quasithinOmegaOneCenter T)) ≠ 1 := fun he => hne (congrArg Subtype.val he)
  have hz' : z = 1 ∨ z = (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ := by
    by_cases hz1 : (⟨z, hz⟩ : ↥(quasithinOmegaOneCenter T)) = 1
    · exact Or.inl (congrArg Subtype.val hz1)
    · exact Or.inr (congrArg Subtype.val ((hw _ hz1).trans (hw _ h1).symm))
  rcases hz' with rfl | rfl
  · exact (oTwoUpper (mcOf T)).one_mem
  · exact hcomm

theorem uOfL22_le_oTwoUpper : uOfL22 T M ≤ oTwoUpper (mcOf T) := by
  intro u hu
  obtain ⟨k, hk, z, hz, rfl⟩ := exists_eq_mul_of_mem_uOfL22 c hu
  exact (oTwoUpper (mcOf T)).mul_mem hk (omegaOneCenter_le_oTwoUpper c hz)

end ULeK

section Final

variable {g : G} (c : Counter T M g)

include c

theorem actH_cube_of_mem_oTwoUpper {x : ↥(mcOf T)} (hx : (x : G) ∈ oTwoUpper (mcOf T)) :
    (actH c.h1281 x) ^ 3 = 1 := by
  have h := c.h1281
  have hF := c.oddFacts
  have key : ∀ w : G, w ∈ oTwoUpper (mcOf T) →
      ∃ hwH : w ∈ mcOf T, (actH h ⟨w, hwH⟩) ^ 3 = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      refine ⟨hw.1, hF.cube_of_odd _ (actH_mem_range h _) ?_⟩
      have hodd : Odd (orderOf (⟨w, hw.1⟩ : ↥(mcOf T))) := by
        rw [← Subgroup.orderOf_coe]; exact hw.2
      exact Odd.of_dvd_nat hodd (orderOf_map_dvd _ _)
    | one =>
      refine ⟨(mcOf T).one_mem, ?_⟩
      have e : (⟨1, (mcOf T).one_mem⟩ : ↥(mcOf T)) = 1 := rfl
      rw [e, map_one, one_pow]
    | mul a b _ _ ha hb =>
      obtain ⟨haH, ha3⟩ := ha
      obtain ⟨hbH, hb3⟩ := hb
      refine ⟨(mcOf T).mul_mem haH hbH, ?_⟩
      have e : (⟨a * b, (mcOf T).mul_mem haH hbH⟩ : ↥(mcOf T)) = ⟨a, haH⟩ * ⟨b, hbH⟩ := rfl
      rw [e, map_mul]
      exact hF.cube_mul _ (actH_mem_range h _) _ (actH_mem_range h _) ha3 hb3
    | inv a _ ha =>
      obtain ⟨haH, ha3⟩ := ha
      refine ⟨(mcOf T).inv_mem haH, ?_⟩
      have e : (⟨a⁻¹, (mcOf T).inv_mem haH⟩ : ↥(mcOf T)) = ⟨a, haH⟩⁻¹ := rfl
      rw [e, map_inv, inv_pow, ha3, inv_one]
  obtain ⟨hxH, hx3⟩ := key _ hx
  exact hx3

theorem odd_relIndex_inf_qOf :
    Odd ((oTwoUpper (mcOf T) ⊓ qOf T).relIndex (oTwoUpper (mcOf T))) := by
  have h := c.h1281
  set ρ := actH h with hρ
  set K := oTwoUpper (mcOf T) with hK
  have hKH : K ≤ mcOf T := oTwoUpper_le _
  have h1 : Nat.card ((K.subgroupOf (mcOf T)).map ρ) *
      Nat.card ↥(K ⊓ ρ.ker.map (mcOf T).subtype) = Nat.card K :=
    card_map_mul_card_inf_ker hKH ρ
  rw [actH_ker_map c] at h1
  have h2 := Subgroup.relIndex_mul_card (K ⊓ qOf T) K
  rw [inf_eq_left.mpr (inf_le_left : K ⊓ qOf T ≤ K)] at h2
  have hpos : 0 < Nat.card ↥(K ⊓ qOf T) := Nat.card_pos
  have h2' : (K ⊓ qOf T).relIndex K * Nat.card ↥(K ⊓ qOf T) = Nat.card K := h2
  have h3 : (K ⊓ qOf T).relIndex K = Nat.card ((K.subgroupOf (mcOf T)).map ρ) :=
    (Nat.eq_of_mul_eq_mul_right hpos (h2'.trans h1.symm))
  rw [h3]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : IsPGroup 3 ↥((K.subgroupOf (mcOf T)).map ρ) := by
    intro y
    refine ⟨1, ?_⟩
    obtain ⟨xk, hxk, hxky⟩ := Subgroup.mem_map.mp y.2
    have e : y.1 ^ 3 = 1 := by
      rw [← hxky]
      exact actH_cube_of_mem_oTwoUpper c hxk
    exact Subtype.ext (by simpa using e)
  obtain ⟨m, hm⟩ := hp3.exists_card_eq
  rw [hm]
  exact Odd.pow (by decide)

theorem inf_qOf_le_uOfL22 : oTwoUpper (mcOf T) ⊓ qOf T ≤ uOfL22 T M := by
  have h := c.h1281
  set K := oTwoUpper (mcOf T) with hK
  have hKH : K ≤ mcOf T := oTwoUpper_le _
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22
  have hKU : K ≤ Subgroup.normalizer (uOfL22 T M : Set G) := hKH.trans hHU
  have hUK : uOfL22 T M ≤ K := uOfL22_le_oTwoUpper c
  have hQn : mcOf T ≤ Subgroup.normalizer (qOf T : Set G) := le_normalizer_pCoreOf 2 _
  have hKY : K ≤ Subgroup.normalizer ((K ⊓ qOf T : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk, hQn (hKH hk)⟩
  have hUn : (uOfL22 T M |>.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKU
  have hYn : ((K ⊓ qOf T).subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKY
  have hUY : (uOfL22 T M).subgroupOf K ≤ (K ⊓ qOf T).subgroupOf K := fun x hx =>
    ⟨x.2, uOfL22_le_qOf c hx⟩
  have hY2 : IsPGroup 2 ↥((K ⊓ qOf T).subgroupOf K) := by
    intro y
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (mcOf T) ⟨(y.1 : G), (y.2 : (y.1 : G) ∈ K ⊓ qOf T).2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hcomm : ∀ k : ↥K, ∀ y ∈ (K ⊓ qOf T).subgroupOf K, k * y * k⁻¹ * y⁻¹ ∈
      (uOfL22 T M).subgroupOf K := by
    intro k y hy
    have := (oTwoUpper_le_centralizerMod c k.2).2.2 (y : G) (hy : (y : G) ∈ K ⊓ qOf T).2
    exact this
  have hgen : (⊤ : Subgroup ↥K) ≤ Subgroup.closure {x : ↥K | Odd (orderOf x)} := by
    intro g' _
    have hKle : K ≤ (Subgroup.closure {x : ↥K | Odd (orderOf x)}).map K.subtype := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      refine ⟨⟨x, mem_oTwoUpper_of_odd hx.1 hx.2⟩, Subgroup.subset_closure ?_, rfl⟩
      show Odd (orderOf (⟨x, mem_oTwoUpper_of_odd hx.1 hx.2⟩ : ↥K))
      rw [Subgroup.orderOf_mk]
      exact hx.2
    obtain ⟨s, hs, hsg⟩ := hKle g'.2
    have : s = g' := Subtype.ext hsg
    rwa [← this]
  have hmain := le_of_central_sylow hUY hY2 (odd_relIndex_inf_qOf c) hcomm hgen
  intro z hz
  exact hmain (show (⟨z, hz.1⟩ : ↥K) ∈ (K ⊓ qOf T).subgroupOf K from hz)

theorem u_eq_of : uOfL22 T M = pCoreOf 2 (oTwoUpper (mcOf T)) := by
  have h := c.h1281
  have hKH : oTwoUpper (mcOf T) ≤ mcOf T := oTwoUpper_le _
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 (uOfL22_le_oTwoUpper c) (hKH.trans hHU)
      ((pCoreOf_isPGroup 2 (mcOf T)).to_le (uOfL22_le_qOf c))
  · have hnorm : mcOf T ≤ Subgroup.normalizer
        (pCoreOf 2 (oTwoUpper (mcOf T)) : Set G) :=
      (le_normalizer_oTwoUpper (mcOf T)).trans (normalizer_le_normalizer_pCoreOf 2 _)
    have h1 : pCoreOf 2 (oTwoUpper (mcOf T)) ≤ qOf T :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hKH) hnorm
        (pCoreOf_isPGroup 2 _)
    exact fun z hz => inf_qOf_le_uOfL22 c ⟨pCoreOf_le 2 _ hz, h1 hz⟩

end Final

end S143

end CFSG.Quasithin
