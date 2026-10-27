module

public import CFSG.RankThree.GF2n.Stroth80.Sec11CM
public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem mem_XbarPre_iff (hc : Ctx M Q Z B) {x : G} (hx : x ∈ M) :
    x ∈ XbarPre M Q Z B ↔
      (QuotientGroup.mk ⟨x, hx⟩ : Mbar M Q) ∈ Xbar M Q Z B := by
  unfold XbarPre
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, hmx⟩
    rw [Subgroup.mem_comap] at hm
    have hsub : m = ⟨x, hx⟩ := Subtype.ext hmx
    rwa [hsub] at hm
  · intro hxbar
    exact ⟨⟨x, hx⟩, by rwa [Subgroup.mem_comap], rfl⟩

theorem XbarPre_le_M (hc : Ctx M Q Z B) : XbarPre M Q Z B ≤ M :=
  Subgroup.map_subtype_le _

theorem Q_le_XbarPre (hc : Ctx M Q Z B) : Q ≤ XbarPre M Q Z B := by
  intro q hq
  have hqM : q ∈ M := by
    have hq' : q ∈ inSubgroup (pCore 2) M := hc.hyp.hQ ▸ hq
    exact Subgroup.map_subtype_le _ hq'
  rw [mem_XbarPre_iff hc hqM]
  have hmem : (⟨q, hqM⟩ : ↥M) ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.mpr hq
  have hone : (QuotientGroup.mk ⟨q, hqM⟩ : Mbar M Q) = 1 :=
    (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) _).mpr hmem
  rw [hone]
  exact (Xbar M Q Z B).one_mem

theorem XbarPre_normal (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    conjSubgroup m (XbarPre M Q Z B) = XbarPre M Q Z B := by
  have hconj : ∀ {d : G}, d ∈ M → ∀ {x : G}, x ∈ XbarPre M Q Z B →
      d * x * d⁻¹ ∈ XbarPre M Q Z B := by
    intro d hd x hx
    have hxM := XbarPre_le_M hc hx
    have hxbar := (mem_XbarPre_iff hc hxM).mp hx
    have hdxM : d * x * d⁻¹ ∈ M := M.mul_mem (M.mul_mem hd hxM) (M.inv_mem hd)
    refine (mem_XbarPre_iff hc hdxM).mpr ?_
    have hclass : (QuotientGroup.mk ⟨d * x * d⁻¹, hdxM⟩ : Mbar M Q) =
        (QuotientGroup.mk ⟨d, hd⟩ : Mbar M Q) *
          (QuotientGroup.mk ⟨x, hxM⟩ : Mbar M Q) *
          (QuotientGroup.mk ⟨d, hd⟩ : Mbar M Q)⁻¹ := by
      have heq : (⟨d * x * d⁻¹, hdxM⟩ : ↥M) = ⟨d, hd⟩ * ⟨x, hxM⟩ * ⟨d, hd⟩⁻¹ := by
        ext
        simp
      rw [heq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hclass]
    exact (hc.Xbar_normal).conj_mem (QuotientGroup.mk ⟨x, hxM⟩) hxbar
      (QuotientGroup.mk ⟨d, hd⟩)
  refine conjSubgroup_eq_self_iff.mpr ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hconj hm hx
  · intro hx
    have h1 := hconj (M.inv_mem hm) hx
    have h1' : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x := by group
    rwa [h1'] at h1

theorem bar_preimage (hc : Ctx M Q Z B) (C : Subgroup (Mbar M Q)) :
    bar M Q ((C.comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype) = C := by
  unfold bar
  have hsub : ((C.comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype).subgroupOf M =
      C.comap (QuotientGroup.mk' (Q.subgroupOf M)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, hmx⟩
      have hsub : m = x := Subtype.ext hmx
      rwa [hsub] at hm
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hsub, Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (Q.subgroupOf M)) C]

theorem bar_XbarPre (hc : Ctx M Q Z B) :
    bar M Q (XbarPre M Q Z B) = Xbar M Q Z B := by
  unfold XbarPre
  exact bar_preimage hc (Xbar M Q Z B)

theorem XbarPre_le_H0 (hc : Ctx M Q Z B) : XbarPre M Q Z B ≤ H0 M Z := by
  have hQH0 : Q ≤ H0 M Z := by
    intro q hq
    refine ⟨hc.hyp.Q_normal.1 hq, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hZc : Z ≤ Subgroup.centralizer (Q : Set G) := by
      rw [hc.hyp.hZ, cen_eq]
      exact inf_le_right
    exact (Subgroup.mem_centralizer_iff.mp (hZc hz) q hq).symm
  have hXH : Xbar M Q Z B ≤ bar M Q (H0 M Z) := by
    rw [Xbar]
    exact (Subgroup.closure_le _).mpr fun d hd => hc.Ebar_subset_H hd
  intro x hx
  have hxM := XbarPre_le_M hc hx
  have hxbar : (QuotientGroup.mk ⟨x, hxM⟩ : Mbar M Q) ∈ Xbar M Q Z B :=
    (mem_XbarPre_iff hc hxM).mp hx
  have hxH : (QuotientGroup.mk ⟨x, hxM⟩ : Mbar M Q) ∈ bar M Q (H0 M Z) := hXH hxbar
  rw [bar, Subgroup.mem_map] at hxH
  obtain ⟨y, hy, hqy⟩ := hxH
  have hyH0 : (y : G) ∈ H0 M Z := Subgroup.mem_subgroupOf.mp hy
  have hxyM : x * (y : G)⁻¹ ∈ M :=
    M.mul_mem hxM (M.inv_mem hyH0.1)
  have hxyQ : x * (y : G)⁻¹ ∈ Q := by
    have hker : (⟨x * (y : G)⁻¹, hxyM⟩ : ↥M) ∈ Q.subgroupOf M := by
      rw [← QuotientGroup.ker_mk' (Q.subgroupOf M), MonoidHom.mem_ker]
      have heq : (⟨x * (y : G)⁻¹, hxyM⟩ : ↥M) = ⟨x, hxM⟩ * y⁻¹ := by
        ext
        simp
      rw [heq, map_mul, map_inv, hqy]
      simpa using mul_inv_cancel ((QuotientGroup.mk' (Q.subgroupOf M)) ⟨x, hxM⟩)
    exact Subgroup.mem_subgroupOf.mp hker
  have hxyH0 : x * (y : G)⁻¹ ∈ H0 M Z := hQH0 hxyQ
  have hxEq : x = (x * (y : G)⁻¹) * (y : G) := by group
  rw [hxEq]
  exact (H0 M Z).mul_mem hxyH0 hyH0

theorem mem_XbarH_iff (hc : Ctx M Q Z B) (h : ↥(H0 M Z)) :
    h ∈ XbarH M Q Z B ↔ (h : G) ∈ XbarPre M Q Z B := by
  rw [mem_XbarPre_iff hc h.2.1]
  unfold XbarH
  rw [Subgroup.mem_comap]
  rfl

section Model

variable {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem pi_one : M₀.π 1 = 0 := by
  have h := M₀.π_mul 1 Q.one_mem 1 Q.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem pi_inv {x : G} (hx : x ∈ Q) : M₀.π x⁻¹ = -M₀.π x := by
  have h := M₀.π_mul x hx x⁻¹ (Q.inv_mem hx)
  rw [mul_inv_cancel, pi_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem pi_commutatorElement (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {q : G} (hq : q ∈ Q) (m : ↥(H0 M Z)) :
    M₀.π ⁅q, (m : G)⁆ = M₀.π q - φ m (M₀.π q) := by
  have hmQ : (m : G) * q⁻¹ * (m : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 m.2.1) q⁻¹).mp (Q.inv_mem hq)
  have e : ⁅q, (m : G)⁆ = q * ((m : G) * q⁻¹ * (m : G)⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e, M₀.π_mul q hq _ hmQ, hφπ m q⁻¹ (Q.inv_mem hq), pi_inv hq, map_neg]
  abel

theorem commutator_le_Q (hc : Ctx M Q Z B) :
    ⁅Q, XbarPre M Q Z B⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq s hs
  have hsM := XbarPre_le_M hc hs
  have hsq : s * q * s⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) q).mp hq
  have e : ⁅q, s⁆ = q * (s * q * s⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Q.mul_mem hq (Q.inv_mem hsq)

theorem exists_XbarH_of_mem_XbarPre (hc : Ctx M Q Z B) {s : G}
    (hs : s ∈ XbarPre M Q Z B) :
    ∃ m : XbarH M Q Z B, (m : G) = s := by
  let m0 : ↥(H0 M Z) := ⟨s, XbarPre_le_H0 hc hs⟩
  have hm0 : m0 ∈ XbarH M Q Z B := (mem_XbarH_iff hc m0).mpr hs
  exact ⟨⟨m0, hm0⟩, rfl⟩

theorem pi_smul_mem_image_commutator (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {x : G} (hx : x ∈ ⁅Q, XbarPre M Q Z B⁆) (c : K) :
    c • M₀.π x ∈ M₀.π '' ((⁅Q, XbarPre M Q Z B⁆ : Subgroup G) : Set G) := by
  let S : Set G := {g | ∃ g1 ∈ Q, ∃ g2 ∈ XbarPre M Q Z B, ⁅g1, g2⁆ = g}
  have hH : ⁅Q, XbarPre M Q Z B⁆ = Subgroup.closure S := Subgroup.commutator_def Q _
  rw [hH] at hx ⊢
  refine Subgroup.closure_induction (p := fun x _ =>
    c • M₀.π x ∈ M₀.π '' (Subgroup.closure S : Set G)) ?mem ?one ?mul ?inv hx
  · intro y hy
    obtain ⟨q, hq, s, hs, rfl⟩ := hy
    obtain ⟨m, hms⟩ := exists_XbarH_of_mem_XbarPre hc hs
    subst hms
    obtain ⟨q', hq', hq'π⟩ := M₀.π_surj (c • M₀.π q)
    refine ⟨⁅q', (m : G)⁆, Subgroup.commutator_mem_commutator hq' hs, ?_⟩
    rw [pi_commutatorElement hc φ hφπ hq m, pi_commutatorElement hc φ hφπ hq' m, hq'π,
      map_smul, smul_sub]
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [pi_one, smul_zero]
  · intro y z hy hz ihy ihz
    obtain ⟨a, ha, haπ⟩ := ihy
    obtain ⟨b, hb, hbπ⟩ := ihz
    have hy' : y ∈ ⁅Q, XbarPre M Q Z B⁆ := by rwa [hH]
    have hz' : z ∈ ⁅Q, XbarPre M Q Z B⁆ := by rwa [hH]
    have ha' : a ∈ ⁅Q, XbarPre M Q Z B⁆ := by rwa [hH]
    have hb' : b ∈ ⁅Q, XbarPre M Q Z B⁆ := by rwa [hH]
    refine ⟨a * b, Subgroup.mul_mem _ ha' hb', ?_⟩
    rw [M₀.π_mul a (commutator_le_Q hc ha') b (commutator_le_Q hc hb'), haπ, hbπ,
      M₀.π_mul y (commutator_le_Q hc hy') z (commutator_le_Q hc hz'), smul_add]
  · intro y hy ihy
    obtain ⟨a, ha, haπ⟩ := ihy
    have hy' : y ∈ ⁅Q, XbarPre M Q Z B⁆ := by rwa [hH]
    have ha' : a ∈ ⁅Q, XbarPre M Q Z B⁆ := by rwa [hH]
    refine ⟨a⁻¹, Subgroup.inv_mem _ ha', ?_⟩
    rw [pi_inv (commutator_le_Q hc ha'), haπ, pi_inv (commutator_le_Q hc hy'), smul_neg]

theorem mem_cmComm_iff [Finite K] (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (e : M₀.E) :
    e ∈ cmComm M Q Z B K γ M₀ φ ↔
      ∃ x : G, x ∈ ⁅Q, XbarPre M Q Z B⁆ ∧ M₀.π x = e := by
  let Kc : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ M₀.π x ∈ cmComm M Q Z B K γ M₀ φ}
      one_mem' := ⟨Q.one_mem, by rw [pi_one]; exact (cmComm M Q Z B K γ M₀ φ).zero_mem⟩
      mul_mem' := by
        rintro x y ⟨hxQ, hxπ⟩ ⟨hyQ, hyπ⟩
        refine ⟨Q.mul_mem hxQ hyQ, ?_⟩
        rw [M₀.π_mul x hxQ y hyQ]
        exact (cmComm M Q Z B K γ M₀ φ).add_mem hxπ hyπ
      inv_mem' := by
        rintro x ⟨hxQ, hxπ⟩
        refine ⟨Q.inv_mem hxQ, ?_⟩
        rw [pi_inv hxQ]
        exact (cmComm M Q Z B K γ M₀ φ).neg_mem hxπ }
  have hH_le_K : ⁅Q, XbarPre M Q Z B⁆ ≤ Kc := by
    rw [Subgroup.commutator_le]
    intro q hq s hs
    obtain ⟨m, hms⟩ := exists_XbarH_of_mem_XbarPre hc hs
    subst hms
    have hsM := XbarPre_le_M hc hs
    have hsq : (m : G) * q * (m : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) q).mp hq
    have hcommQ : ⁅q, (m : G)⁆ ∈ Q := by
      have e : ⁅q, (m : G)⁆ = q * ((m : G) * q * (m : G)⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Q.mul_mem hq (Q.inv_mem hsq)
    refine ⟨hcommQ, ?_⟩
    have hgen : φ m (M₀.π q) - M₀.π q ∈ cmComm M Q Z B K γ M₀ φ := by
      refine Submodule.mem_iSup_of_mem m ?_
      exact ⟨M₀.π q, by simp⟩
    have hneg : -(φ m (M₀.π q) - M₀.π q) ∈ cmComm M Q Z B K γ M₀ φ :=
      (cmComm M Q Z B K γ M₀ φ).neg_mem hgen
    rw [pi_commutatorElement hc φ hφπ hq m]
    simpa [neg_sub] using hneg
  let P : Submodule K M₀.E :=
    { carrier := M₀.π '' ((⁅Q, XbarPre M Q Z B⁆ : Subgroup G) : Set G)
      zero_mem' := ⟨1, (⁅Q, XbarPre M Q Z B⁆).one_mem, pi_one⟩
      add_mem' := by
        rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        refine ⟨x * y, Subgroup.mul_mem _ hx hy, ?_⟩
        rw [M₀.π_mul x (commutator_le_Q hc hx) y (commutator_le_Q hc hy)]
      smul_mem' := by
        rintro c a ⟨x, hx, rfl⟩
        exact pi_smul_mem_image_commutator hc φ hφπ hx c }
  have hcm_le_P : cmComm M Q Z B K γ M₀ φ ≤ P := by
    refine iSup_le fun m => ?_
    rintro e ⟨f, rfl⟩
    obtain ⟨q, hq, hqπ⟩ := M₀.π_surj (-f)
    have hmPre : (m : G) ∈ XbarPre M Q Z B :=
      (mem_XbarH_iff hc (m : ↥(H0 M Z))).mp m.2
    refine ⟨⁅q, (m : G)⁆, Subgroup.commutator_mem_commutator hq hmPre, ?_⟩
    rw [pi_commutatorElement hc φ hφπ hq m, hqπ, map_neg]
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    abel
  constructor
  · intro he
    have heP := hcm_le_P he
    change e ∈ M₀.π '' ((⁅Q, XbarPre M Q Z B⁆ : Subgroup G) : Set G) at heP
    simpa using heP
  · rintro ⟨x, hx, rfl⟩
    exact (hH_le_K hx).2

theorem cmComm_invariant (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (s : ↥(XbarPre M Q Z B)) :
    Submodule.map ((φ ⟨s, XbarPre_le_H0 hc s.2⟩ : M₀.E ≃ₗ[K] M₀.E) :
        M₀.E →ₗ[K] M₀.E) (cmComm M Q Z B K γ M₀ φ) =
      cmComm M Q Z B K γ M₀ φ := by
  set hs : ↥(H0 M Z) := ⟨s, XbarPre_le_H0 hc s.2⟩ with hhs
  have hmem : hs ∈ XbarH M Q Z B := (mem_XbarH_iff hc hs).mpr s.2
  set sh : XbarH M Q Z B := ⟨hs, hmem⟩ with hsh
  have hmap_range : ∀ T U : M₀.E ≃ₗ[K] M₀.E,
      Submodule.map (T : M₀.E →ₗ[K] M₀.E)
        (LinearMap.range ((U : M₀.E →ₗ[K] M₀.E) - 1)) =
      LinearMap.range
        (((T * U * T⁻¹ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro T U
    rw [← LinearMap.range_comp]
    have hcomp : ((T : M₀.E →ₗ[K] M₀.E).comp ((U : M₀.E →ₗ[K] M₀.E) - 1)) =
        ((((T * U * T⁻¹ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1).comp
          (T : M₀.E →ₗ[K] M₀.E)) := by
      ext y
      simp [LinearEquiv.mul_apply]
    rw [hcomp, LinearMap.range_comp, LinearMap.range_eq_top.mpr T.surjective,
      Submodule.map_top]
  have hstep : ∀ k : XbarH M Q Z B,
      Submodule.map ((φ hs : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
        (LinearMap.range (((φ k : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)) =
      LinearMap.range
        (((φ (sh * k * sh⁻¹) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro k
    have hconj : ((φ hs : M₀.E ≃ₗ[K] M₀.E) * (φ k) * (φ hs)⁻¹) =
        φ (sh * k * sh⁻¹) := by
      simp [map_mul, map_inv, hsh]
    rw [← hconj]
    exact hmap_range (φ hs) (φ k)
  calc
    Submodule.map ((φ hs : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
        (cmComm M Q Z B K γ M₀ φ)
        = ⨆ k : XbarH M Q Z B,
            Submodule.map ((φ hs : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
              (LinearMap.range
                (((φ k : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)) := by
          rw [cmComm, Submodule.map_iSup]
    _ = ⨆ k : XbarH M Q Z B,
          LinearMap.range
            (((φ (sh * k * sh⁻¹) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) := by
          exact iSup_congr fun k => hstep k
    _ = ⨆ k : XbarH M Q Z B,
          LinearMap.range (((φ k : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) := by
          apply le_antisymm
          · refine iSup_le fun k => ?_
            exact le_iSup (fun j : XbarH M Q Z B => LinearMap.range
              (((φ j : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1))
              (sh * k * sh⁻¹)
          · refine iSup_le fun k => ?_
            refine le_iSup_of_le (sh⁻¹ * k * sh) ?_
            rw [show (sh : ↥(H0 M Z)) *
                ((sh⁻¹ * k * sh : XbarH M Q Z B) : ↥(H0 M Z)) *
                ((sh⁻¹ : XbarH M Q Z B) : ↥(H0 M Z)) = (k : ↥(H0 M Z)) by
              have hcoe : ((sh⁻¹ * k * sh : XbarH M Q Z B) : ↥(H0 M Z)) =
                  (sh : ↥(H0 M Z))⁻¹ * (k : ↥(H0 M Z)) * (sh : ↥(H0 M Z)) := by
                rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
              have hinv : ((sh⁻¹ : XbarH M Q Z B) : ↥(H0 M Z)) =
                  (sh : ↥(H0 M Z))⁻¹ := rfl
              rw [hcoe, hinv]
              group]
    _ = cmComm M Q Z B K γ M₀ φ := by rw [cmComm]

end Model

end CFSG.RankThree.GF2n.Stroth80
