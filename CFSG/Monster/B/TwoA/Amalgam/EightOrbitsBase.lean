module

public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsRad
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsCount
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsPres

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Unitary

@[expose] def piFibre
    (s : Shat) (u : CVert) : Set CVert :=
  {x | ∃ (hx : cvMul x s⁻¹ ∈ cPi0) (hu : cvMul u s⁻¹ ∈ cPi0), cpsi ⟨_, hx⟩ = cpsi ⟨_, hu⟩}

theorem piFibre_eq
    {t s : Shat} {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) (hv : cvMul cv0 t ∈ cPi s)
    (hw : cvMul (cvOf (jhatS k)) t ∈ cPi s) :
    piFibre s (cvMul cv0 t) = {cvMul cv0 t, cvMul (cvOf a0S) t} := by
  have hv' := mem_cPi_iff.1 hv
  have hus : cvMul ((⟨_, hv'⟩ : cPi0) : CVert) s = cvMul cv0 t := cvMul_inv_cancel' (cvMul cv0 t) s
  ext x
  constructor
  · rintro ⟨hx, hu, hψ⟩
    by_cases hxv : x = cvMul cv0 t
    · exact Or.inl hxv
    · right
      have hne : (⟨_, hv'⟩ : cPi0) ≠ ⟨_, hx⟩ := fun e => hxv (by
        have h := congrArg (fun z : cPi0 => cvMul (z : CVert) s) e
        simp only [cvMul_inv_cancel'] at h
        exact h.symm)
      have h := eq_partner_of_fibre hk0 hk hv hw hne hψ.symm hus
      simp only [cvMul_inv_cancel'] at h
      exact h
  · rintro (h | h)
    · rw [h]
      exact ⟨hv', hv', rfl⟩
    · rw [Set.mem_singleton_iff] at h
      subst h
      have h2 : 1 < (cpsi ⁻¹' {cpsi ⟨_, hv'⟩}).ncard := by
        rw [ncard_cpsi_preimage]
        norm_num
      obtain ⟨u'', hu'', hne⟩ := Set.exists_ne_of_one_lt_ncard h2 ⟨_, hv'⟩
      have hψ : cpsi ⟨_, hv'⟩ = cpsi u'' := (Set.mem_singleton_iff.1 hu'').symm
      have h3 := eq_partner_of_fibre hk0 hk hv hw (Ne.symm hne) hψ hus
      rw [← h3]
      have hu2 : cvMul (cvMul (u'' : CVert) s) s⁻¹ ∈ cPi0 := by
        rw [cvMul_inv_cancel]
        exact u''.2
      refine ⟨hu2, hv', ?_⟩
      have e : (⟨cvMul (cvMul (u'' : CVert) s) s⁻¹, hu2⟩ : cPi0) = u'' :=
        Subtype.ext (cvMul_inv_cancel _ _)
      rw [e]
      exact hψ.symm

section Pull

variable {v : CVert} (iv : cgraph.neighborSet v ≃ rootClass)

theorem nbrPull_midSet
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) (d : Fin 5) (c : ℕ) :
    nbrPull iv (midSet θ d c) =
      {u | u ∈ nbrPull iv (fibOrbit d) ∧ nquot θ d (nbrRoot iv u) ∈ quotOrb d c} := by
  ext u
  constructor
  · rintro ⟨hu, h1, h2⟩
    rw [← nbrRoot_of_mem iv hu] at h1 h2
    exact ⟨(mem_nbrPull_iff_nbrRoot iv hu).2 h1, h2⟩
  · rintro ⟨hu, h2⟩
    exact (mem_nbrPull_iff_nbrRoot iv hu.fst).2 ⟨nbrRoot_mem_of_mem_nbrPull iv hu, h2⟩

theorem cvOrbit_eq_of_conjOrbit {G₀ : Subgroup Shat} {H : Subgroup GStar} {A : Set GStar}
    (horb : ∀ u : cgraph.neighborSet v,
      cvOrbit G₀ u = nbrPull iv (conjOrbit H (SemidirectProduct.inl (iv u : stdGroup))))
    (hA : ∃ x ∈ A, A = conjOrbit H x) {u : CVert} (hu : u ∈ nbrPull iv A) :
    cvOrbit G₀ u = nbrPull iv A := by
  obtain ⟨hu', hx⟩ := hu
  obtain ⟨x, -, rfl⟩ := hA
  have h := horb ⟨u, hu'⟩
  rw [conjOrbit_eq_of_mem hx] at h
  exact h

end Pull


section Defs

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar}
  (hx : θ (QuotientGroup.mk xhatEam) = rootStar)
  (hinj : ∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
    (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (e'⁻¹ * xhatEam * e'))
  (t : Shat)

abbrev ivB :
    cgraph.neighborSet (cvMul cv0 t) ≃ rootClass := rootV θ hx hinj rfl

@[expose] def omegaB
    (i : Fin 8) : Set CVert := nbrPull (ivB hx hinj t) (eightSet θ i)

@[expose] def rootSubB
    (d : Fin 5) : Set CVert := nbrPull (ivB hx hinj t) (fibOrbit d)

@[expose] def quotB
    (d : Fin 5) (u : CVert) : Submodule F4 V6 :=
  nquot θ d (nbrRoot (ivB hx hinj t) u)

end Defs

section Base

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)
  (hx : θ (QuotientGroup.mk xhatEam) = rootStar)
  (hinj : ∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
    (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (e'⁻¹ * xhatEam * e'))
  (t : Shat) {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0) (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k)))
  (hτ : psiW (labE k) = tauW)

include hk0 hk in
theorem cvOrbit_pairStab_eq
    (u : cgraph.neighborSet (cvMul cv0 t)) :
    cvOrbit (vStab (cvMul cv0 t) ⊓ vStab (cvMul (cvOf (jhatS k)) t)) u =
      nbrPull (ivB hx hinj t)
        (conjOrbit ((q4P k).map (rho1 θ)) (SemidirectProduct.inl (ivB hx hinj t u : stdGroup))) :=
  cvOrbit_eq_nbrPull (ivB hx hinj t) (rhoV θ rfl) (inl_rootV_stabAct θ hx hinj rfl) inf_le_left
    (mem_map_q4P_iff θ hk0 hk rfl) u

include hadj hfeq hfB in
theorem cvOrbit_edgeStab_eq
    (u : cgraph.neighborSet (cvMul cv0 t)) :
    cvOrbit (vStab (cvMul cv0 t) ⊓ vStab (cvMul (cvOf a0S) t)) u =
      nbrPull (ivB hx hinj t)
        (conjOrbit (parStar firstJ) (SemidirectProduct.inl (ivB hx hinj t u : stdGroup))) :=
  cvOrbit_eq_nbrPull (ivB hx hinj t) (rhoV θ rfl) (inl_rootV_stabAct θ hx hinj rfl) inf_le_left
    (mem_parStar_iff_rhoV θ hadj hfeq hfB rfl) u

include hadj hfeq hfB hk0 hk in
theorem cvOrbit_radV_eq
    (u : cgraph.neighborSet (cvMul cv0 t)) :
    cvOrbit (radV (cvMul cv0 t) (cvMul (cvOf a0S) t)) u =
      nbrPull (ivB hx hinj t)
        (conjOrbit radStar (SemidirectProduct.inl (ivB hx hinj t u : stdGroup))) :=
  cvOrbit_eq_nbrPull (ivB hx hinj t) (rhoV θ rfl) (inl_rootV_stabAct θ hx hinj rfl)
    ((radV_le _ _).trans inf_le_left) (mem_radStar_iff_rhoV t hadj hfeq hfB hk0 hk) u

theorem omegaB_subset
    (i : Fin 8) : omegaB hx hinj t i ⊆ cgraph.neighborSet (cvMul cv0 t) :=
  nbrPull_subset _ _

include hadj hfeq hfB in
theorem existsUnique_mem_omegaB
    {u : CVert} (hu : u ∈ cgraph.neighborSet (cvMul cv0 t)) :
    ∃! i, u ∈ omegaB hx hinj t i :=
  existsUnique_mem_nbrPull _ (fun _ hy => existsUnique_mem_eightSet hadj hfeq hfB hy) u hu

include hadj hfeq hfB hk0 hk hτ in
theorem cvOrbit_omegaB
    (i : Fin 8) {u : CVert} (hu : u ∈ omegaB hx hinj t i) :
    cvOrbit (vStab (cvMul cv0 t) ⊓ vStab (cvMul (cvOf (jhatS k)) t)) u = omegaB hx hinj t i :=
  cvOrbit_eq_of_conjOrbit _ (cvOrbit_pairStab_eq hx hinj t hk0 hk)
    (eightSet_eq_conjOrbit hadj hfeq hfB hk0 hk hτ i) hu

include hadj hfeq hfB hk0 hk hτ in
theorem ncard_omegaB
    (i : Fin 8) : (omegaB hx hinj t i).ncard = eightSize i :=
  (ncard_nbrPull _ (eightSet_subset_rootClass θ i)).trans
    (ncard_eightSet hadj hfeq hfB hk0 hk hτ i)

include hadj hfeq hfB hx hinj hk0 hk hτ in
theorem ncard_setOf_cvOrbit_pairStab :
    {O | ∃ u ∈ cgraph.neighborSet (cvMul cv0 t),
      O = cvOrbit (vStab (cvMul cv0 t) ⊓ vStab (cvMul (cvOf (jhatS k)) t)) u}.ncard = 8 := by
  have hne : ∀ i, (omegaB hx hinj t i).Nonempty := fun i =>
    Set.nonempty_of_ncard_ne_zero (by
      rw [ncard_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ]
      revert i
      decide)
  have e : {O | ∃ u ∈ cgraph.neighborSet (cvMul cv0 t),
      O = cvOrbit (vStab (cvMul cv0 t) ⊓ vStab (cvMul (cvOf (jhatS k)) t)) u} =
        Set.range (omegaB hx hinj t) := by
    ext O
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, hi, -⟩ := existsUnique_mem_omegaB hadj hfeq hfB hx hinj t hu
      exact ⟨i, (cvOrbit_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ i hi).symm⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨u, hu⟩ := hne i
      exact ⟨u, omegaB_subset hx hinj t i hu,
        (cvOrbit_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ i hu).symm⟩
  have hinj' : Function.Injective (omegaB hx hinj t) := by
    intro i j hij
    have h := congrArg Set.ncard hij
    rw [ncard_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ,
      ncard_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ] at h
    clear hij
    revert i j
    decide
  rw [e, Set.ncard_range_of_injective hinj', Nat.card_eq_fintype_card, Fintype.card_fin]

theorem rootSubB_subset
    (d : Fin 5) : rootSubB hx hinj t d ⊆ cgraph.neighborSet (cvMul cv0 t) :=
  nbrPull_subset _ _

theorem existsUnique_mem_rootSubB
    {u : CVert} (hu : u ∈ cgraph.neighborSet (cvMul cv0 t)) :
    ∃! d, u ∈ rootSubB hx hinj t d :=
  existsUnique_mem_nbrPull _ (fun _ hy => existsUnique_mem_fibOrbit hy) u hu

include hadj hfeq hfB in
theorem cvOrbit_rootSubB
    (d : Fin 5) {u : CVert} (hu : u ∈ rootSubB hx hinj t d) :
    cvOrbit (vStab (cvMul cv0 t) ⊓ vStab (cvMul (cvOf a0S) t)) u = rootSubB hx hinj t d :=
  cvOrbit_eq_of_conjOrbit _ (cvOrbit_edgeStab_eq hadj hfeq hfB hx hinj t) (A := fibOrbit d)
    ⟨_, mem_conjOrbit_self _ _, rfl⟩ hu

theorem ncard_rootSubB
    (d : Fin 5) : (rootSubB hx hinj t d).ncard = repSize d :=
  (ncard_nbrPull _ (fibOrbit_subset_rootClass d)).trans (ncard_fibOrbit d)

include hadj hfeq hfB in
theorem rootSubB_eq_omegaB :
    rootSubB hx hinj t 0 = omegaB hx hinj t 3 ∧
      rootSubB hx hinj t 1 = omegaB hx hinj t 0 ∪ omegaB hx hinj t 4 ∧
      rootSubB hx hinj t 2 = omegaB hx hinj t 1 ∪ omegaB hx hinj t 5 ∧
      rootSubB hx hinj t 3 = omegaB hx hinj t 2 ∪ omegaB hx hinj t 6 ∧
      rootSubB hx hinj t 4 = omegaB hx hinj t 7 := by
  have hg := fibOrbit_eq_eightSet hadj hfeq hfB (θ := θ)
  exact ⟨congrArg (nbrPull _) hg.1, (congrArg (nbrPull _) hg.2.1).trans (nbrPull_union _ _ _),
    (congrArg (nbrPull _) hg.2.2.1).trans (nbrPull_union _ _ _),
    (congrArg (nbrPull _) hg.2.2.2.1).trans (nbrPull_union _ _ _),
    congrArg (nbrPull _) hg.2.2.2.2⟩

include hadj hfeq hfB in
theorem omegaB_three :
    omegaB hx hinj t 3 = {cvMul (cvOf a0S) t} := by
  have hp : (ivB hx hinj t ⟨_, partner_mem_neighborSet rfl⟩ : stdGroup) = rootInv :=
    rootV_partner θ hx hinj rfl
  have e : rootStar = SemidirectProduct.inl
      (ivB hx hinj t ⟨_, partner_mem_neighborSet rfl⟩ : stdGroup) := by
    rw [hp]
    rfl
  show nbrPull _ (eightSet θ 3) = _
  rw [← (fibOrbit_eq_eightSet hadj hfeq hfB (θ := θ)).1, fibOrbit_zero, e]
  exact nbrPull_singleton _

include hk0 hk in
theorem mem_sphereFour_base :
    cvMul (cvOf (jhatS k)) t ∈ sphereFour (cvMul cv0 t) :=
  mem_sphereFour_of_cPi (cvMul_mem_cPi cv0_mem_cPi0 t) (cvMul_mem_cPi (jhatS_mem_cPi0 k) t)
    (fun e => hk0 (cvMul_injective t e).symm) fun h => hk ((cgraph_adj_cvMul _ _ t).1 h)

include hadj hfeq hfB hk0 hk hτ in
theorem omegaB_zero :
    omegaB hx hinj t 0 = cgraph.commonNeighbors (cvMul cv0 t) (cvMul (cvOf (jhatS k)) t) := by
  have hw := mem_sphereFour_base t hk0 hk
  have htrans := native_coset_graph_two_distance_two_orbits.2.2.2.1
  have h648 := (native_coset_graph_order_four_common_neighbors.1 _ _ hw).2.1
  obtain ⟨u₀, hu₀⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h648]; norm_num :
    (cgraph.commonNeighbors (cvMul cv0 t) (cvMul (cvOf (jhatS k)) t)).ncard ≠ 0)
  have hcn : cgraph.commonNeighbors (cvMul cv0 t) (cvMul (cvOf (jhatS k)) t) =
      cvOrbit (vStab (cvMul cv0 t) ⊓ vStab (cvMul (cvOf (jhatS k)) t)) u₀ := by
    ext u
    constructor
    · intro hu
      obtain ⟨y, hyv, hyw, rfl⟩ := htrans _ _ hw.1 u₀ hu₀ u hu
      exact ⟨y, Subgroup.mem_inf.2 ⟨hyv, hyw⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyv, hyw⟩ := Subgroup.mem_inf.1 hy
      refine ⟨?_, ?_⟩
      · have h := (cgraph_adj_cvMul _ u₀ y).2 hu₀.1
        rwa [mem_vStab.1 hyv] at h
      · have h := (cgraph_adj_cvMul _ u₀ y).2 hu₀.2
        rwa [mem_vStab.1 hyw] at h
  obtain ⟨i, hi, -⟩ := existsUnique_mem_omegaB hadj hfeq hfB hx hinj t hu₀.1
  have e := (cvOrbit_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ i hi).symm.trans hcn.symm
  have hi0 : i = 0 := by
    have h := ncard_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ i
    rw [e, h648] at h
    clear e hi
    revert h
    revert i
    decide
  subst hi0
  exact e

include hadj hfeq hfB in
theorem neighborSet_inter_cPi_eq :
    cgraph.neighborSet (cvMul cv0 t) ∩ cPi t =
      omegaB hx hinj t 0 ∪ omegaB hx hinj t 3 ∪ omegaB hx hinj t 4 := by
  rw [neighborSet_inter_cPi rfl]
  obtain ⟨δ, hδ⟩ := Set.nonempty_of_ncard_ne_zero (by rw [ncard_piDelta]; norm_num :
    piDelta.ncard ≠ 0)
  have hδv : cvMul δ t ∈ cgraph.neighborSet (cvMul cv0 t) := by
    have h : cvMul δ t ∈ cgraph.neighborSet (cvMul cv0 t) ∩ cPi t := by
      rw [neighborSet_inter_cPi rfl]
      exact Or.inr ⟨δ, hδ, rfl⟩
    exact h.1
  obtain ⟨d, hd, -⟩ := existsUnique_mem_rootSubB hx hinj t hδv
  have e := (image_piDelta_eq_cvOrbit rfl hδ).trans (cvOrbit_rootSubB hadj hfeq hfB hx hinj t d hd)
  have hd1 : d = 1 := by
    have h := ncard_rootSubB hx hinj t d
    rw [← e, ncard_image_piDelta] at h
    exact repSize_injective (h.symm.trans rfl)
  subst hd1
  rw [e, ← omegaB_three hadj hfeq hfB hx hinj t, (rootSubB_eq_omegaB hadj hfeq hfB hx hinj t).2.1,
    ← Set.union_assoc, Set.union_comm (omegaB hx hinj t 3) (omegaB hx hinj t 0)]

include hadj hfeq hfB hk0 hk hτ in
theorem omegaB_three_union_four_subset :
    omegaB hx hinj t 3 ∪ omegaB hx hinj t 4 ⊆ sphereFour (cvMul (cvOf (jhatS k)) t) := by
  intro u hu
  have huPi : u ∈ cgraph.neighborSet (cvMul cv0 t) ∩ cPi t := by
    rw [neighborSet_inter_cPi_eq hadj hfeq hfB hx hinj t]
    rcases hu with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hn0 : u ∉ omegaB hx hinj t 0 := by
    intro h0
    obtain ⟨i, -, hi⟩ := existsUnique_mem_omegaB hadj hfeq hfB hx hinj t huPi.1
    rcases hu with h | h
    · exact absurd ((hi 0 h0).trans (hi 3 h).symm) (by decide)
    · exact absurd ((hi 0 h0).trans (hi 4 h).symm) (by decide)
  have hna : ¬ cgraph.Adj (cvMul (cvOf (jhatS k)) t) u := fun h =>
    hn0 (by rw [omegaB_zero hadj hfeq hfB hx hinj t hk0 hk hτ]; exact ⟨huPi.1, h⟩)
  have hne : cvMul (cvOf (jhatS k)) t ≠ u := by
    rintro rfl
    exact (cgraph_dist_eq_two_iff.1 (mem_sphereFour_base t hk0 hk).1).2.1 huPi.1
  exact mem_sphereFour_of_cPi (cvMul_mem_cPi (jhatS_mem_cPi0 k) t) huPi.2 hne hna

include hadj hfeq hfB hk0 hk in
theorem cvOrbit_radV_eq_nbrRoot
    (d : Fin 5) {u : CVert} (hu : u ∈ rootSubB hx hinj t d) :
    cvOrbit (radV (cvMul cv0 t) (cvMul (cvOf a0S) t)) u =
      nbrPull (ivB hx hinj t) (conjOrbit radStar (nbrRoot (ivB hx hinj t) u)) := by
  refine (cvOrbit_radV_eq hadj hfeq hfB hx hinj t hk0 hk ⟨u, hu.fst⟩).trans ?_
  rw [nbrRoot_of_mem _ hu.fst]

include hadj hfeq hfB hk0 hk in
theorem ncard_cvOrbit_radV
    (d : Fin 5) {u : CVert} (hu : u ∈ rootSubB hx hinj t d) :
    (cvOrbit (radV (cvMul cv0 t) (cvMul (cvOf a0S) t)) u).ncard = fibUSize d := by
  have hxd := nbrRoot_mem_of_mem_nbrPull _ hu
  rw [cvOrbit_radV_eq_nbrRoot hadj hfeq hfB hx hinj t hk0 hk d hu,
    ncard_nbrPull _ ((conjOrbit_subset_fibOrbit radStar_le_parStar hxd).trans
      (fibOrbit_subset_rootClass d)), ncard_conjOrbit_radStar hxd]

include hadj hfeq hfB hk0 hk in
theorem cvOrbit_radV_of_JJ
    {d : Fin 5} (hd : d = 0 ∨ d = 4) {u : CVert}
    (hu : u ∈ rootSubB hx hinj t d) :
    cvOrbit (radV (cvMul cv0 t) (cvMul (cvOf a0S) t)) u = rootSubB hx hinj t d := by
  have hxd := nbrRoot_mem_of_mem_nbrPull _ hu
  rw [cvOrbit_radV_eq_nbrRoot hadj hfeq hfB hx hinj t hk0 hk d hu]
  exact congrArg (nbrPull _) (Set.Subset.antisymm
    (conjOrbit_subset_fibOrbit radStar_le_parStar hxd) fun y hy =>
      mem_conjOrbit_radStar_of_JJ hd hxd hy)

include hadj hfeq hfB hk0 hk in
theorem quotB_eq_iff
    {d : Fin 5} (hd : IsMid d) {u u' : CVert} (hu : u ∈ rootSubB hx hinj t d)
    (hu' : u' ∈ rootSubB hx hinj t d) :
    quotB hx hinj t d u = quotB hx hinj t d u' ↔
      u' ∈ cvOrbit (radV (cvMul cv0 t) (cvMul (cvOf a0S) t)) u := by
  rw [cvOrbit_radV_eq_nbrRoot hadj hfeq hfB hx hinj t hk0 hk d hu,
    mem_nbrPull_iff_nbrRoot _ hu'.fst]
  exact nquot_eq_iff hadj hfeq hfB hd (nbrRoot_mem_of_mem_nbrPull _ hu)
    (nbrRoot_mem_of_mem_nbrPull _ hu')

include hadj hfeq hfB in
theorem image_quotB
    {d : Fin 5} (hd : IsMid d) :
    quotB hx hinj t d '' rootSubB hx hinj t d = {S | UIso (quotDim d) S} := by
  show (fun u => nquot θ d (nbrRoot (ivB hx hinj t) u)) '' nbrPull (ivB hx hinj t) (fibOrbit d) = _
  rw [← Set.image_image (nquot θ d) (nbrRoot (ivB hx hinj t)),
    image_nbrRoot_nbrPull _ (fibOrbit_subset_rootClass d), image_nquot hadj hfeq hfB hd]

include hadj hfeq hfB in
theorem quotB_cvMul
    {d : Fin 5} (hd : IsMid d) {u : CVert} (hu : u ∈ rootSubB hx hinj t d)
    (q : ↥(vStab (cvMul cv0 t) ⊓ vStab (cvMul (cvOf (jhatS k)) t))) :
    quotB hx hinj t d (cvMul u q) =
      sigmaAct (quotB hx hinj t d u) (phiU (pairProj t hk0 hk q)) := by
  have hxd := nbrRoot_mem_of_mem_nbrPull _ hu
  have hqP : ((t * q * t⁻¹ : Shat) : Dfull) ∈ Pc 0 :=
    conj_mem_P1_of_mem_pairStab t (pairStab_le t hk0 hk q.2)
  have hρ : rhoV θ (rfl : cvMul cv0 t = cvMul cv0 t) ⟨q, q.2.1⟩ = rho1 θ ⟨_, hqP⟩ := rfl
  have hmem : cvMul u q ∈ cgraph.neighborSet (cvMul cv0 t) :=
    cvMul_mem_neighborSet q.2.1 hu.fst
  have e1 : nbrRoot (ivB hx hinj t) (cvMul u q) =
      (rho1 θ ⟨_, hqP⟩)⁻¹ * nbrRoot (ivB hx hinj t) u * rho1 θ ⟨_, hqP⟩ := by
    rw [nbrRoot_of_mem _ hmem, nbrRoot_of_mem _ hu.fst, ← hρ]
    exact inl_rootV_stabAct θ hx hinj rfl ⟨q, q.2.1⟩ ⟨u, hu.fst⟩
  have e2 : pairProj t hk0 hk q = p1Proj ⟨_, hqP⟩ := pairProj_apply t hk0 hk q
  calc nquot θ d (nbrRoot (ivB hx hinj t) (cvMul u q))
      = nquot θ d ((rho1 θ ⟨_, hqP⟩)⁻¹ * nbrRoot (ivB hx hinj t) u * rho1 θ ⟨_, hqP⟩) :=
        congrArg (nquot θ d) e1
    _ = sigmaAct (nquot θ d (nbrRoot (ivB hx hinj t) u)) (rhoP1 ⟨_, hqP⟩) :=
        nquot_conj_inv hadj hfeq hfB hd hxd ⟨_, hqP⟩
    _ = sigmaAct (nquot θ d (nbrRoot (ivB hx hinj t) u)) (phiU (pairProj t hk0 hk q)) := by
        rw [e2, rhoP1_apply]

theorem omegaB_eq_quot
    {i : Fin 8} (hi : ¬ (eightLevel i = 0 ∨ eightLevel i = 4)) :
    omegaB hx hinj t i = {u | u ∈ rootSubB hx hinj t (eightLevel i) ∧
      quotB hx hinj t (eightLevel i) u ∈ quotOrb (eightLevel i) (eightIdx i)} := by
  show nbrPull _ (eightSet θ i) = _
  rw [eightSet_eq_of_mid hi, nbrPull_midSet]
  rfl

theorem omegaB_eq_parts :
    omegaB hx hinj t 0 = {u | u ∈ rootSubB hx hinj t 1 ∧ quotB hx hinj t 1 u ∈ plOrbit 0} ∧
      omegaB hx hinj t 4 = {u | u ∈ rootSubB hx hinj t 1 ∧ quotB hx hinj t 1 u ∈ plOrbit 1} ∧
      omegaB hx hinj t 1 = {u | u ∈ rootSubB hx hinj t 2 ∧ quotB hx hinj t 2 u ∈ ptOrbit 0} ∧
      omegaB hx hinj t 5 = {u | u ∈ rootSubB hx hinj t 2 ∧ quotB hx hinj t 2 u ∈ ptOrbit 1} ∧
      omegaB hx hinj t 2 = {u | u ∈ rootSubB hx hinj t 3 ∧ quotB hx hinj t 3 u ∈ plOrbit 0} ∧
      omegaB hx hinj t 6 = {u | u ∈ rootSubB hx hinj t 3 ∧ quotB hx hinj t 3 u ∈ plOrbit 1} :=
  ⟨omegaB_eq_quot hx hinj t (i := 0) (by decide), omegaB_eq_quot hx hinj t (i := 4) (by decide),
    omegaB_eq_quot hx hinj t (i := 1) (by decide), omegaB_eq_quot hx hinj t (i := 5) (by decide),
    omegaB_eq_quot hx hinj t (i := 2) (by decide), omegaB_eq_quot hx hinj t (i := 6) (by decide)⟩

end Base

end CFSG.Monster.B.TwoA.Amalgam
