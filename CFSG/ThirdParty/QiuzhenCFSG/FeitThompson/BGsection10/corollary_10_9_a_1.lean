module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_8_c
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_sylow_eq_bot_of_not_mem_hall
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {p : Nat.Primes}
    {K : Subgroup H} (hKHall : IsHallSubgroup π K) (hpπ : p ∉ π)
    (P : Sylow p.val K) :
    (P : Subgroup K) = ⊥ := by
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases P.isPGroup'.card_eq_or_dvd with hcard | hp_dvd
  · exact (Subgroup.card_eq_one (H := (P : Subgroup K))).mp hcard
  · exact False.elim <| hpπ
      (hKHall.p_in_pi_of_p_dvd_card p
        (hp_dvd.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup K))))

private theorem CFSG.section10_ambient_sylow_le_centralizer_of_not_mem_sigma
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∉ section10SigmaPrimes M) :
    ∃ Pσ : Sylow p.val (section10Msigma M),
      section10AmbientSylowSubgroup (section10Msigma M) Pσ ≤
        Subgroup.centralizer (X : Set G) := by
  classical
  let Pσ : Sylow p.val (section10Msigma M) :=
    Classical.choice (Sylow.nonempty (p := p.val) (G := section10Msigma M))
  have hHallσ : IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M) :=
    (theorem_10_2_b (G := G) hM).1
  have hPbot : (Pσ : Subgroup (section10Msigma M)) = ⊥ :=
    section10_sylow_eq_bot_of_not_mem_hall hHallσ hpσ Pσ
  refine ⟨Pσ, ?_⟩
  intro y hy
  have hy1 : y = 1 := by
    simpa [section10AmbientSylowSubgroup, hPbot] using hy
  rw [hy1]
  exact Subgroup.one_mem _

private theorem CFSG.section10_pCore_commute_of_ne
    {R : Type*} [Group R] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    ∀ x ∈ pCore p R, ∀ y ∈ pCore q R, x * y = y * x := by
  intro x hx y hy
  have hdisj : Disjoint (pCore p R) (pCore q R) :=
    IsPGroup.disjoint_of_ne p q hpq (pCore p R) (pCore q R)
      pCore_isPGroup pCore_isPGroup
  have hmem_comm : ⁅x, y⁆ ∈ ⁅pCore p R, pCore q R⁆ :=
    Subgroup.commutator_mem_commutator hx hy
  have hle : ⁅pCore p R, pCore q R⁆ ≤ pCore p R ⊓ pCore q R :=
    Subgroup.commutator_le_inf (H₁ := pCore p R) (H₂ := pCore q R)
  have hmem_inf : ⁅x, y⁆ ∈ pCore p R ⊓ pCore q R := hle hmem_comm
  have hinf_eq : (pCore p R ⊓ pCore q R : Subgroup R) = ⊥ := hdisj.eq_bot
  rw [hinf_eq] at hmem_inf
  have h1 : ⁅x, y⁆ = (1 : R) := by simpa using hmem_inf
  rwa [commutatorElement_eq_one_iff_mul_comm] at h1

omit [IsMinCE G] in
private theorem CFSG.section10_nilpotent_sylow_le_centralizer_of_pSubgroup_ne
    {R : Type*} [Group R] [Finite R] [Group.IsNilpotent R]
    {p q : Nat.Primes} (hpq : p ≠ q) (P : Sylow p.val R)
    {Q : Subgroup R} (hQq : IsPGroup q.val Q) :
    (P : Subgroup R) ≤ Subgroup.centralizer (Q : Set R) := by
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  have hpq_val : p.val ≠ q.val := by
    intro hpq_val
    exact hpq (Subtype.ext hpq_val)
  have hP_le_core : (P : Subgroup R) ≤ pCore p.val R := by
    have hPnormal : (P : Subgroup R).Normal :=
      Group.IsNilpotent.sylow_normal (p := p.val) inferInstance P
    exact le_sSup ⟨hPnormal, P.isPGroup'⟩
  have hQ_le_core : Q ≤ pCore q.val R := by
    obtain ⟨Q₀, hQ_le_Q₀⟩ := IsPGroup.exists_le_sylow (G := R) (p := q.val) hQq
    have hQ₀normal : (Q₀ : Subgroup R).Normal :=
      Group.IsNilpotent.sylow_normal (p := q.val) inferInstance Q₀
    exact hQ_le_Q₀.trans (le_sSup ⟨hQ₀normal, Q₀.isPGroup'⟩)
  intro x hxP
  rw [Subgroup.mem_centralizer_iff]
  intro y hyQ
  exact (section10_pCore_commute_of_ne hpq_val x (hP_le_core hxP) y (hQ_le_core hyQ)).symm

omit [IsMinCE G] in
public theorem CFSG.section10_pSubgroup_le_centralizer_of_nilpotent_overgroup
    {L X P : Subgroup G} {p q : Nat.Primes} (hpq : p ≠ q)
    (hLnil : Group.IsNilpotent L) (hPL : P ≤ L) (hXL : X ≤ L)
    (hPp : IsPGroup p.val P) (hXq : IsPGroup q.val X) :
    P ≤ Subgroup.centralizer (X : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let Psub : Subgroup L := P.subgroupOf L
  let Xsub : Subgroup L := X.subgroupOf L
  have hPsubp : IsPGroup p.val Psub := by
    exact hPp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := P) (K := L) hPL).symm
  have hXsubq : IsPGroup q.val Xsub := by
    exact hXq.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := X) (K := L) hXL).symm
  obtain ⟨PL, hPsub_le_PL⟩ :=
    IsPGroup.exists_le_sylow (G := L) (p := p.val) hPsubp
  let : Group.IsNilpotent L := hLnil
  have hPL_cent_Xsub : (PL : Subgroup L) ≤ Subgroup.centralizer (Xsub : Set L) :=
    section10_nilpotent_sylow_le_centralizer_of_pSubgroup_ne
      (R := L) hpq PL hXsubq
  intro y hyP
  rw [Subgroup.mem_centralizer_iff]
  intro x hxX
  let yL : L := ⟨y, hPL hyP⟩
  let xL : L := ⟨x, hXL hxX⟩
  have hyPsub : yL ∈ Psub := hyP
  have hxXsub : xL ∈ Xsub := hxX
  have hcommL :=
    (Subgroup.mem_centralizer_iff.mp (hPL_cent_Xsub (hPsub_le_PL hyPsub))) xL hxXsub
  exact congrArg Subtype.val hcommL

omit [IsMinCE G] in
private theorem CFSG.section10_ambient_sylow_le_centralizer_of_nilpotent_overgroup
    {S L X : Subgroup G} {p q : Nat.Primes} (hpq : p ≠ q)
    (hLnil : Group.IsNilpotent L) (P : Sylow p.val S)
    (hPL : section10AmbientSylowSubgroup S P ≤ L) (hXL : X ≤ L)
    (hXq : IsPGroup q.val X) :
    section10AmbientSylowSubgroup S P ≤ Subgroup.centralizer (X : Set G) := by
  classical
  have hPp : IsPGroup p.val (section10AmbientSylowSubgroup S P) := by
    exact IsPGroup.map (p := p.val) (H := (P : Subgroup S)) P.isPGroup' S.subtype
  exact section10_pSubgroup_le_centralizer_of_nilpotent_overgroup
    (G := G) hpq hLnil hPL hXL hPp hXq


public theorem CFSG.section10_isPiSubgroup_compl_of_isPGroup_not_mem
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {X : Subgroup H}
    {q : Nat.Primes} (hqπ : q ∉ π) (hXq : IsPGroup q.val X) :
    IsPiSubgroup (G := H) πᶜ X := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  intro r hr_dvd
  rw [Set.mem_compl_iff]
  obtain ⟨n, hcard⟩ := hXq.exists_card_eq
  have hr_dvd_q : r.val ∣ q.val :=
    r.property.dvd_of_dvd_pow (by simpa [hcard] using hr_dvd)
  have hrq : r = q :=
    Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.property q.property).mp hr_dvd_q)
  simpa [hrq] using hqπ

public theorem CFSG.section10_sylow_le_normal_hall_of_mem
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {S : Subgroup H}
    [S.Normal] (hSHall : IsHallSubgroup π S) {p : Nat.Primes} (hpπ : p ∈ π)
    (P : Sylow p.val H) :
    (P : Subgroup H) ≤ S := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PS : Sylow p.val S := Classical.choice (Sylow.nonempty (p := p.val) (G := S))
  let Psub : Subgroup H := (PS : Subgroup S).map S.subtype
  have hPsub_p : IsPGroup p.val Psub := by
    exact IsPGroup.map (p := p.val) (H := (PS : Subgroup S)) PS.isPGroup' S.subtype
  have hp_not_S_index : ¬ p.val ∣ S.index := by
    intro hp_dvd
    exact (hSHall.p_in_pi_of_p_dvd_index p hp_dvd) hpπ
  have hp_not_Psub_index : ¬ p.val ∣ Psub.index := by
    intro hp_dvd
    have hidx : Psub.index = (PS : Subgroup S).index * S.index := by
      simpa [Psub] using (Subgroup.index_map_subtype (H := S) (K := (PS : Subgroup S)))
    have hp_prod : p.val ∣ (PS : Subgroup S).index * S.index := by
      simpa [hidx] using hp_dvd
    rcases p.property.dvd_or_dvd hp_prod with hp_PS | hp_S
    · exact PS.not_dvd_index hp_PS
    · exact hp_not_S_index hp_S
  let Q : Sylow p.val H := hPsub_p.toSylow hp_not_Psub_index
  have hQ_le_S : (Q : Subgroup H) ≤ S := by
    intro x hx
    have hxPsub : x ∈ Psub := by
      simpa [Q] using hx
    rcases Subgroup.mem_map.mp hxPsub with ⟨y, _hy, rfl⟩
    exact y.property
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  have hgQ_le_S : ((g • Q : Sylow p.val H) : Subgroup H) ≤ S := by
    intro x hx
    rw [Sylow.coe_subgroup_smul] at hx
    have hx' : g⁻¹ * x * g ∈ (Q : Subgroup H) := by
      simpa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_apply, mul_assoc] using hx
    have hxS' : g⁻¹ * x * g ∈ S := hQ_le_S hx'
    simpa [mul_assoc] using ((inferInstance : S.Normal).conj_mem (g⁻¹ * x * g) hxS' g)
  simpa [hg] using hgQ_le_S

public theorem CFSG.section10_exists_sylow_subgroupOf_with_same_ambient
    {H : Type*} [Group H] [Finite H] {S D : Subgroup H} (hSD : S ≤ D)
    {p : Nat.Primes} (P : Sylow p.val D)
    (hPS : (P : Subgroup D) ≤ S.subgroupOf D) :
    ∃ PS : Sylow p.val S,
      (PS : Subgroup S).map S.subtype = ((P : Subgroup D).map D.subtype : Subgroup H) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let SsubD : Subgroup D := S.subgroupOf D
  let Psub : Sylow p.val SsubD := P.subtype hPS
  let e : SsubD ≃* S := Subgroup.subgroupOfEquivOfLe hSD
  let PS : Sylow p.val S := Psub.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨PS, ?_⟩
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨yS, hyPS, rfl⟩
    have hyPS' : yS ∈ (Psub : Subgroup SsubD).map e.toMonoidHom := by
      simpa [PS] using hyPS
    rcases Subgroup.mem_map.mp hyPS' with ⟨yD, hyPsub, hyD_eq⟩
    refine ⟨(yD : D), ?_, ?_⟩
    · exact hyPsub
    · exact congrArg Subtype.val hyD_eq
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨yD, hyP, rfl⟩
    have hySsub : (⟨yD, hPS hyP⟩ : SsubD) ∈ Psub := hyP
    refine ⟨e ⟨yD, hPS hyP⟩, ?_, ?_⟩
    · change e ⟨yD, hPS hyP⟩ ∈ (Psub : Subgroup SsubD).map e.toMonoidHom
      exact Subgroup.mem_map.mpr ⟨⟨yD, hPS hyP⟩, hySsub, rfl⟩
    · rfl

omit [IsMinCE G] in
public theorem CFSG.section10_exists_sylow_centralized_of_local_nilpotent_hall_pair
    {S : Subgroup G} {π : Set Nat.Primes} {p q : Nat.Primes}
    {L : Subgroup S} {X : Subgroup L}
    (hpq : p ≠ q) (hpπ : p ∈ π) (hLHall : IsHallSubgroup π L)
    (hLnil : Group.IsNilpotent L) (hXq : IsPGroup q.val X) :
    ∃ P : Sylow p.val S,
      section10AmbientSylowSubgroup S P ≤
        Subgroup.centralizer (((X.map L.subtype).map S.subtype : Subgroup G) : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PL : Sylow p.val L := Classical.choice (Sylow.nonempty (p := p.val) (G := L))
  let PsubS : Subgroup S := (PL : Subgroup L).map L.subtype
  have hPsubS_p : IsPGroup p.val PsubS := by
    exact IsPGroup.map (p := p.val) (H := (PL : Subgroup L)) PL.isPGroup' L.subtype
  have hp_not_L_index : ¬ p.val ∣ L.index := by
    intro hp_dvd
    exact (hLHall.p_in_pi_of_p_dvd_index p hp_dvd) hpπ
  have hPsubS_index : PsubS.index = (PL : Subgroup L).index * L.index := by
    simpa [PsubS] using (Subgroup.index_map_subtype (H := L) (K := (PL : Subgroup L)))
  have hp_not_PsubS_index : ¬ p.val ∣ PsubS.index := by
    intro hp_dvd
    have hp_prod : p.val ∣ (PL : Subgroup L).index * L.index := by
      simpa [hPsubS_index] using hp_dvd
    rcases p.property.dvd_or_dvd hp_prod with hp_PL | hp_L
    · exact PL.not_dvd_index hp_PL
    · exact hp_not_L_index hp_L
  let P : Sylow p.val S := hPsubS_p.toSylow hp_not_PsubS_index
  have hPL_cent_X : (PL : Subgroup L) ≤ Subgroup.centralizer (X : Set L) := by
    let : Group.IsNilpotent L := hLnil
    exact section10_nilpotent_sylow_le_centralizer_of_pSubgroup_ne
      (R := L) hpq PL hXq
  refine ⟨P, ?_⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hy' : y ∈ PsubS.map S.subtype := by
    simpa [P, PsubS, section10AmbientSylowSubgroup] using hy
  rcases Subgroup.mem_map.mp hy' with ⟨yS, hyS, rfl⟩
  rcases Subgroup.mem_map.mp hyS with ⟨yL, hyPL, rfl⟩
  rcases Subgroup.mem_map.mp hx with ⟨xS, hxS, rfl⟩
  rcases Subgroup.mem_map.mp hxS with ⟨xL, hxX, rfl⟩
  have hcommL := (Subgroup.mem_centralizer_iff.mp (hPL_cent_X hyPL)) xL hxX
  exact congrArg (fun z : L => ((z : S) : G)) hcommL

public theorem CFSG.section10_exists_nilpotent_hall_containing
    {H : Type*} [Group H] [Finite H]
    {π : Set Nat.Primes} {K X : Subgroup H}
    (hKsolv : Group.IsSolvable K)
    (hHas : section10HasNilpotentHallSubgroup π K)
    (hXK : X ≤ K) (hXπ : IsPiSubgroup π (X.subgroupOf K)) :
    ∃ L : Subgroup H, L ≤ K ∧ X ≤ L ∧
      IsHallSubgroup π (L.subgroupOf K) ∧ Group.IsNilpotent L := by
  classical
  let Xsub : Subgroup K := X.subgroupOf K
  let : MulDistribMulAction PUnit.{1} K := {
    smul := fun _ x => x
    one_smul := by intro x; rfl
    mul_smul := by intro a b x; rfl
    smul_mul := by intro a x y; rfl
    smul_one := by intro a; rfl }
  have hXsub_inv : IsInvariant PUnit.{1} K Xsub := by
    refine ⟨?_⟩
    intro a x
    simp
  obtain ⟨C, hCHall, _hCinv, hXsubC⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := K) (A := PUnit.{1}) hKsolv (by simp) π Xsub hXπ hXsub_inv
  rcases hHas with ⟨N, hNK, hNHall, hNnil⟩
  let Nsub : Subgroup K := N.subgroupOf K
  have hNsub_nil : Group.IsNilpotent Nsub := by
    let e : N ≃* Nsub := (Subgroup.subgroupOfEquivOfLe (H := N) (K := K) hNK).symm
    let : Group.IsNilpotent N := hNnil
    exact Group.nilpotent_of_mulEquiv (G := N) (G' := Nsub) e
  obtain ⟨k, hk⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := K) hKsolv (H₁ := Nsub) (H₂ := C) hNHall hCHall
  have hCnil : Group.IsNilpotent C := by
    let Nconj : Subgroup K := Nsub.map (MulAut.conj k).toMonoidHom
    have hNconj_nil : Group.IsNilpotent Nconj := by
      let e : Nsub ≃* Nconj :=
        Subgroup.equivMapOfInjective Nsub (MulAut.conj k).toMonoidHom
          (MulAut.conj k).injective
      let : Group.IsNilpotent Nsub := hNsub_nil
      exact Group.nilpotent_of_mulEquiv (G := Nsub) (G' := Nconj) e
    have hC_eq : C = Nconj := by simpa [Nconj] using hk
    let e : Nconj ≃* C := MulEquiv.subgroupCongr hC_eq.symm
    let : Group.IsNilpotent Nconj := hNconj_nil
    exact Group.nilpotent_of_mulEquiv (G := Nconj) (G' := C) e
  let L : Subgroup H := C.map K.subtype
  have hLK : L ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hLsub_eq : L.subgroupOf K = C := by
    simpa [L] using (subgroupOf_map_subtype_eq (K := K) C)
  have hXL : X ≤ L := by
    intro x hx
    have hxK : x ∈ K := hXK hx
    have hxXsub : (⟨x, hxK⟩ : K) ∈ Xsub := hx
    exact ⟨⟨x, hxK⟩, hXsubC hxXsub, rfl⟩
  have hLnil : Group.IsNilpotent L := by
    let e : C ≃* L := Subgroup.equivMapOfInjective C K.subtype K.subtype_injective
    let : Group.IsNilpotent C := hCnil
    exact Group.nilpotent_of_mulEquiv (G := C) (G' := L) e
  exact ⟨L, hLK, hXL, by simpa [hLsub_eq] using hCHall, hLnil⟩

omit [IsMinCE G] in
private theorem CFSG.section10_lift_msigma_local_centralizer
    {M X : Subgroup G} {p : Nat.Primes} (hXleM : X ≤ M)
    (hlocal :
      ∃ P : Sylow p.val (section10MsigmaSubgroup M),
        section10AmbientSylowSubgroup (section10MsigmaSubgroup M) P ≤
          Subgroup.centralizer ((X.subgroupOf M) : Set M)) :
    ∃ Pσ : Sylow p.val (section10Msigma M),
      section10AmbientSylowSubgroup (section10Msigma M) Pσ ≤
        Subgroup.centralizer (X : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases hlocal with ⟨P, hPcent⟩
  let S : Subgroup M := section10MsigmaSubgroup M
  let Sg : Subgroup G := section10Msigma M
  let e : S ≃* Sg := by
    change S ≃* S.map M.subtype
    exact Subgroup.equivMapOfInjective S M.subtype M.subtype_injective
  let Pσ : Sylow p.val Sg := P.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Pσ, ?_⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hxX
  rw [section10AmbientSylowSubgroup] at hy
  rcases Subgroup.mem_map.mp hy with ⟨ySg, hyPσ, rfl⟩
  have hyPσ' : ySg ∈ (P : Subgroup S).map e.toMonoidHom := by
    simpa [Pσ] using hyPσ
  rcases Subgroup.mem_map.mp hyPσ' with ⟨yS, hyP, hyS_eq⟩
  let xM : M := ⟨x, hXleM hxX⟩
  have hyLocal :
      ((yS : S) : M) ∈ section10AmbientSylowSubgroup S P := by
    exact ⟨yS, hyP, rfl⟩
  have hxM : xM ∈ X.subgroupOf M := hxX
  have hcommM :=
    (Subgroup.mem_centralizer_iff.mp (hPcent hyLocal)) xM hxM
  have hySg_val : (ySg : G) = ((yS : S) : M) := by
    calc
      (ySg : G) = (e yS : G) := by
        exact congrArg Subtype.val hyS_eq.symm
      _ = ((yS : S) : M) := by
        unfold e
        exact Subgroup.coe_equivMapOfInjective_apply
          S M.subtype M.subtype_injective yS
  simpa [xM, hySg_val] using congrArg Subtype.val hcommM

private theorem CFSG.section10_corollary_10_9_a_1_of_le_derived
    {M X : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpβ : p ∉ section10BetaPrimes M)
    (hqβ : q ∉ section10BetaPrimes M) (hpq : p ≠ q) (hpσ : p ∈ section10SigmaPrimes M)
    (hXle : X ≤ M) (hXq : IsPGroup q.val X) (hXD : X ≤ ambientDerivedSubgroup M) :
    ∃ Pσ : Sylow p.val (section10Msigma M),
      section10AmbientSylowSubgroup (section10Msigma M) Pσ ≤
        Subgroup.centralizer (X : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let D : Subgroup M := derivedSubgroup M
  let S : Subgroup M := section10MsigmaSubgroup M
  let XM : Subgroup M := X.subgroupOf M
  have hXMD : XM ≤ D := by
    intro x hx
    have hxG : ((x : M) : G) ∈ ambientDerivedSubgroup M := hXD hx
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxG
    rcases hxG with ⟨y, hyD, hyx⟩
    change y ∈ derivedSubgroup M at hyD
    change x ∈ derivedSubgroup M
    have hyxM : y = x := Subtype.ext hyx
    simpa [hyxM] using hyD
  have hXMq : IsPGroup q.val XM := by
    exact hXq.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hXle).symm
  let XsubD : Subgroup D := XM.subgroupOf D
  have hXsubDq : IsPGroup q.val XsubD := by
    exact hXMq.of_equiv (Subgroup.subgroupOfEquivOfLe (H := XM) (K := D) hXMD).symm
  have hXsubDπ : IsPiSubgroup (G := D) (section10BetaPrimes M)ᶜ XsubD :=
    section10_isPiSubgroup_compl_of_isPGroup_not_mem
      (π := section10BetaPrimes M) hqβ hXsubDq
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have : Group.IsSolvable M := hMsolv
  have hDsolv : Group.IsSolvable D := by infer_instance
  obtain ⟨L, hLD, hXML, hLHallD, hLnil⟩ :=
    section10_exists_nilpotent_hall_containing
      (H := M) (π := (section10BetaPrimes M)ᶜ) (K := D) (X := XM)
      hDsolv (lemma_10_8_b (G := G) hM).1 hXMD hXsubDπ
  let LsubD : Subgroup D := L.subgroupOf D
  have hLsubDnil : Group.IsNilpotent LsubD := by
    let e : L ≃* LsubD := (Subgroup.subgroupOfEquivOfLe hLD).symm
    let : Group.IsNilpotent L := hLnil
    exact Group.nilpotent_of_mulEquiv (G := L) (G' := LsubD) e
  have hXsubD_le_LsubD : XsubD ≤ LsubD := by
    intro x hx
    exact hXML hx
  let Xloc : Subgroup LsubD := XsubD.subgroupOf LsubD
  have hXlocq : IsPGroup q.val Xloc := by
    exact hXsubDq.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := XsubD) (K := LsubD) hXsubD_le_LsubD).symm
  have hpβc : p ∈ (section10BetaPrimes M)ᶜ := by
    simpa using hpβ
  obtain ⟨PD, hPDcent⟩ :=
    section10_exists_sylow_centralized_of_local_nilpotent_hall_pair
      (G := M) (S := D) (π := (section10BetaPrimes M)ᶜ) (p := p) (q := q)
      (L := LsubD) (X := Xloc) hpq hpβc hLHallD hLsubDnil hXlocq
  have hSleD : S ≤ D := by
    simpa [S, D] using section10_msigmaSubgroup_le_derivedSubgroup hM
  let SsubD : Subgroup D := S.subgroupOf D
  have hSsubDNormal : SsubD.Normal := by
    simpa [SsubD, S, D] using
      (Subgroup.Normal.subgroupOf (inferInstance : S.Normal) D)
  have hSHallD : IsHallSubgroup (section10SigmaPrimes M) SsubD := by
    simpa [SsubD, S] using (section10_msigmaSubgroup_isHall hM).subgroupOf hSleD
  have hPDleSsubD : (PD : Subgroup D) ≤ SsubD := by
    have : SsubD.Normal := hSsubDNormal
    exact section10_sylow_le_normal_hall_of_mem hSHallD hpσ PD
  obtain ⟨PS, hPSamb⟩ :=
    section10_exists_sylow_subgroupOf_with_same_ambient hSleD PD hPDleSsubD
  have hlocal :
      ∃ P : Sylow p.val S,
        section10AmbientSylowSubgroup S P ≤
          Subgroup.centralizer ((X.subgroupOf M) : Set M) := by
    refine ⟨PS, ?_⟩
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hxXM
    have hyD : y ∈ section10AmbientSylowSubgroup D PD := by
      simpa [section10AmbientSylowSubgroup, hPSamb] using hy
    have hxD : x ∈ D := hXMD hxXM
    let xD : D := ⟨x, hxD⟩
    have hxXsubD : xD ∈ XsubD := hxXM
    have hxLsubD : xD ∈ LsubD := hXsubD_le_LsubD hxXsubD
    let xL : LsubD := ⟨xD, hxLsubD⟩
    have hxXloc : xL ∈ Xloc := hxXsubD
    have hxMapped : x ∈ ((Xloc.map LsubD.subtype).map D.subtype : Subgroup M) := by
      refine ⟨xD, ?_, rfl⟩
      exact ⟨xL, hxXloc, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hPDcent hyD)) x hxMapped
  exact section10_lift_msigma_local_centralizer hXle hlocal

private theorem CFSG.section10_corollary_10_9_a_1_of_nilpotent_pair_hall
    {M X : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpq : p ≠ q)
    (hpσ : p ∈ section10SigmaPrimes M) (hXle : X ≤ M)
    (hXq : IsPGroup q.val X) {W : Subgroup M}
    (hXW : X.subgroupOf M ≤ W)
    (hWHall : IsHallSubgroup ({p, q} : Set Nat.Primes) W)
    (hWnil : Group.IsNilpotent W) :
    ∃ Pσ : Sylow p.val (section10Msigma M),
      section10AmbientSylowSubgroup (section10Msigma M) Pσ ≤
        Subgroup.centralizer (X : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let S : Subgroup M := section10MsigmaSubgroup M
  let XM : Subgroup M := X.subgroupOf M
  have hXMq : IsPGroup q.val XM := by
    exact hXq.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hXle).symm
  let PW : Sylow p.val W := Classical.choice (Sylow.nonempty (p := p.val) (G := W))
  let PsubM : Subgroup M := (PW : Subgroup W).map W.subtype
  have hPsubM_p : IsPGroup p.val PsubM := by
    exact IsPGroup.map (p := p.val) (H := (PW : Subgroup W)) PW.isPGroup' W.subtype
  have hp_pair : p ∈ ({p, q} : Set Nat.Primes) := by
    simp
  have hp_not_W_index : ¬ p.val ∣ W.index := by
    intro hp_dvd
    exact (hWHall.p_in_pi_of_p_dvd_index p hp_dvd) hp_pair
  have hp_not_PsubM_index : ¬ p.val ∣ PsubM.index := by
    intro hp_dvd
    have hidx : PsubM.index = (PW : Subgroup W).index * W.index := by
      simpa [PsubM] using (Subgroup.index_map_subtype (H := W) (K := (PW : Subgroup W)))
    have hp_prod : p.val ∣ (PW : Subgroup W).index * W.index := by
      simpa [hidx] using hp_dvd
    rcases p.property.dvd_or_dvd hp_prod with hp_PW | hp_W
    · exact PW.not_dvd_index hp_PW
    · exact hp_not_W_index hp_W
  let PM : Sylow p.val M := hPsubM_p.toSylow hp_not_PsubM_index
  have hPsubM_le_W : PsubM ≤ W := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hPM_le_W : (PM : Subgroup M) ≤ W := by
    intro x hx
    have hxPsub : x ∈ PsubM := by
      simpa [PM, IsPGroup.toSylow_coe] using hx
    exact hPsubM_le_W hxPsub
  have hSHall : IsHallSubgroup (section10SigmaPrimes M) S := by
    simpa [S] using (theorem_10_2_b (G := G) hM).2
  have hPM_le_S : (PM : Subgroup M) ≤ S := by
    exact section10_sylow_le_normal_hall_of_mem hSHall hpσ PM
  let PsubS : Subgroup S := (PM : Subgroup M).subgroupOf S
  have hPsubS_p : IsPGroup p.val PsubS := by
    exact PM.isPGroup'.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := (PM : Subgroup M)) (K := S) hPM_le_S).symm
  have hp_not_S_index : ¬ p.val ∣ S.index := by
    intro hp_dvd
    exact (hSHall.p_in_pi_of_p_dvd_index p hp_dvd) hpσ
  have hp_not_PsubS_index : ¬ p.val ∣ PsubS.index := by
    intro hp_dvd
    have hmap : PsubS.map S.subtype = (PM : Subgroup M) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hPM_le_S hx⟩, hx, rfl⟩
    have hidx : (PM : Subgroup M).index = PsubS.index * S.index := by
      simpa [hmap] using (Subgroup.index_map_subtype (H := S) (K := PsubS))
    exact PM.not_dvd_index (by
      rw [hidx]
      exact dvd_mul_of_dvd_left hp_dvd S.index)
  let PS : Sylow p.val S := hPsubS_p.toSylow hp_not_PsubS_index
  have hPS_le_W : section10AmbientSylowSubgroup S PS ≤ W := by
    intro y hy
    rw [section10AmbientSylowSubgroup] at hy
    rcases Subgroup.mem_map.mp hy with ⟨yS, hyPS, rfl⟩
    have hyPsubS : yS ∈ PsubS := by
      simpa [PS, IsPGroup.toSylow_coe] using hyPS
    exact hPM_le_W hyPsubS
  have hlocal :
      ∃ P : Sylow p.val S,
        section10AmbientSylowSubgroup S P ≤
          Subgroup.centralizer ((X.subgroupOf M) : Set M) := by
    refine ⟨PS, ?_⟩
    exact section10_ambient_sylow_le_centralizer_of_nilpotent_overgroup
      (G := M) (S := S) (L := W) (X := XM) hpq hWnil PS hPS_le_W hXW hXMq
  exact section10_lift_msigma_local_centralizer hXle hlocal

private theorem CFSG.section10_pSubgroup_le_pPrimeCore_of_largest_lt
    {H : Type*} [Group H] [Finite H] {p q : Nat.Primes} {X : Subgroup H}
    (hlargest : IsLargestPrimeDivisor p.val (Nat.card (H ⧸ pPrimeCore p.val H)))
    (hXq : IsPGroup q.val X) (hpq_lt : p.val < q.val) :
    X ≤ pPrimeCore p.val H := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let π : H →* H ⧸ pPrimeCore p.val H := QuotientGroup.mk' (pPrimeCore p.val H)
  have hXmap_bot : X.map π = ⊥ := by
    by_contra hne
    have hcard_ne : Nat.card (X.map π) ≠ 1 := by
      intro hcard
      exact hne ((Subgroup.card_eq_one (H := X.map π)).mp hcard)
    have hXmapq : IsPGroup q.val (X.map π) := hXq.map π
    rcases hXmapq.card_eq_or_dvd with hcard | hq_dvd
    · exact hcard_ne hcard
    · have hq_dvd_quot : q.val ∣ Nat.card (H ⧸ pPrimeCore p.val H) :=
        hq_dvd.trans (Subgroup.card_subgroup_dvd_card (X.map π))
      have hq_le_p : q.val ≤ p.val := hlargest.2.2 q.val q.property hq_dvd_quot
      omega
  have hX_le_ker : X ≤ π.ker :=
    (Subgroup.map_eq_bot_iff (H := X) (f := π)).mp hXmap_bot
  have hker_eq : π.ker = pPrimeCore p.val H := by
    simp [π]
  rwa [hker_eq] at hX_le_ker

private theorem CFSG.section10_inf_derived_nilpotent_of_pair_hall
    {M : Subgroup G} {p q : Nat.Primes} {W : Subgroup M}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpβ : p ∉ section10BetaPrimes M) (hqβ : q ∉ section10BetaPrimes M)
    (hWHall : IsHallSubgroup ({p, q} : Set Nat.Primes) W) :
    Group.IsNilpotent (W ⊓ derivedSubgroup M : Subgroup M) := by
  classical
  let D : Subgroup M := derivedSubgroup M
  let A : Subgroup M := W ⊓ D
  have hAD : A ≤ D := by
    simp [A]
  have hAπD : IsPiSubgroup (G := D) (section10BetaPrimes M)ᶜ (A.subgroupOf D) := by
    intro r hr_dvd
    rw [Set.mem_compl_iff]
    have hcard_eq : Nat.card (A.subgroupOf D) = Nat.card A := by
      simpa using Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := D) hAD).toEquiv
    have hrA : r.val ∣ Nat.card A := by
      simpa [hcard_eq] using hr_dvd
    have hrW : r.val ∣ Nat.card W :=
      hrA.trans (Subgroup.card_dvd_of_le (show A ≤ W from by simp [A]))
    have hrpair : r ∈ ({p, q} : Set Nat.Primes) :=
      hWHall.p_in_pi_of_p_dvd_card r hrW
    rcases (Set.mem_insert_iff.mp hrpair) with hrp | hrq
    · intro hrβ
      exact hpβ (by simpa [hrp] using hrβ)
    · have hrq' : r = q := by simpa using hrq
      intro hrβ
      exact hqβ (by simpa [hrq'] using hrβ)
  have hDsolv : Group.IsSolvable D := by
    have hMsolv : Group.IsSolvable M :=
      IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
    let : Group.IsSolvable M := hMsolv
    exact by infer_instance
  obtain ⟨L, _hLD, hAL, _hLHall, hLnil⟩ :=
    section10_exists_nilpotent_hall_containing
      (H := M) (π := (section10BetaPrimes M)ᶜ) (K := D) (X := A)
      hDsolv (lemma_10_8_b (G := G) hM).1 hAD hAπD
  let AsubL : Subgroup L := A.subgroupOf L
  have hAsubLnil : Group.IsNilpotent AsubL := by
    let : Group.IsNilpotent L := hLnil
    infer_instance
  let e : AsubL ≃* A := Subgroup.subgroupOfEquivOfLe hAL
  exact Group.nilpotent_of_mulEquiv (G := AsubL) (G' := A) e

private theorem CFSG.section10_pSubgroup_le_inf_derived_of_sigma
    {M : Subgroup G} {p : Nat.Primes} {W : Subgroup M} {P : Subgroup W}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hPp : IsPGroup p.val P) :
    P ≤ ((W ⊓ derivedSubgroup M : Subgroup M).subgroupOf W) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let D : Subgroup M := derivedSubgroup M
  let A : Subgroup M := W ⊓ D
  let qD : M →* M ⧸ D := QuotientGroup.mk' D
  let φ : W →* M ⧸ D := qD.comp W.subtype
  have hp_not_dvd_quot : ¬ p.val ∣ Nat.card (M ⧸ D) := by
    exact section10_sigma_not_dvd_quotient_derived hM hpσ
  have hPmap_bot : P.map φ = ⊥ := by
    by_contra hne
    have hcard_ne : Nat.card (P.map φ) ≠ 1 := by
      intro hcard
      exact hne ((Subgroup.card_eq_one (H := P.map φ)).mp hcard)
    have hPmap_p : IsPGroup p.val (P.map φ) := hPp.map φ
    rcases hPmap_p.card_eq_or_dvd with hcard | hp_dvd
    · exact hcard_ne hcard
    · exact hp_not_dvd_quot (hp_dvd.trans (Subgroup.card_subgroup_dvd_card (P.map φ)))
  have hP_le_ker : P ≤ φ.ker :=
    (Subgroup.map_eq_bot_iff (H := P) (f := φ)).mp hPmap_bot
  have hker_eq : φ.ker = A.subgroupOf W := by
    ext x
    constructor
    · intro hx
      change qD (x : M) = 1 at hx
      have hxD : (x : M) ∈ D :=
        (QuotientGroup.eq_one_iff (N := D) (x : M)).1 hx
      exact ⟨x.property, hxD⟩
    · intro hx
      change qD (x : M) = 1
      exact (QuotientGroup.eq_one_iff (N := D) (x : M)).2 hx.2
  simpa [A, D] using hP_le_ker.trans (le_of_eq hker_eq)

omit [IsMinCE G] in
private theorem CFSG.section10_qSubgroup_le_inf_pPrimeCore_of_largest_lt
    {M : Subgroup G} {p q : Nat.Primes} {W : Subgroup M} {Q : Subgroup W}
    (hlargest : IsLargestPrimeDivisor p.val (Nat.card (M ⧸ pPrimeCore p.val M)))
    (hQq : IsPGroup q.val Q) (hpq_lt : p.val < q.val) :
    Q ≤ ((W ⊓ pPrimeCore p.val M : Subgroup M).subgroupOf W) := by
  classical
  have hQmap_q : IsPGroup q.val (Q.map W.subtype) :=
    IsPGroup.map (p := q.val) (H := Q) hQq W.subtype
  have hQmap_le_core : Q.map W.subtype ≤ pPrimeCore p.val M :=
    section10_pSubgroup_le_pPrimeCore_of_largest_lt
      (H := M) (p := p) (q := q) hlargest hQmap_q hpq_lt
  intro x hx
  have hxmap : (x : M) ∈ Q.map W.subtype := ⟨x, hx, rfl⟩
  exact ⟨x.property, hQmap_le_core hxmap⟩

omit [IsMinCE G] in
private theorem CFSG.section10_inf_pPrimeCore_subgroupOf_isPGroup_of_pair_hall
    {M : Subgroup G} {p q : Nat.Primes} {W : Subgroup M}
    (_hpq : p ≠ q) (hWHall : IsHallSubgroup ({p, q} : Set Nat.Primes) W) :
    IsPGroup q.val ((W ⊓ pPrimeCore p.val M : Subgroup M).subgroupOf W) := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let B : Subgroup M := W ⊓ pPrimeCore p.val M
  let BW : Subgroup W := B.subgroupOf W
  refine (IsPGroup.iff_card (p := q.val) (G := BW)).2 ?_
  have hcard_pos : Nat.card BW ≠ 0 := Nat.card_pos.ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hcard_pos ?_⟩
  intro r hrprime hr_dvd
  let r' : Nat.Primes := ⟨r, hrprime⟩
  have hcard_eq : Nat.card BW = Nat.card B := by
    simpa [BW] using
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := B) (K := W)
        (by intro x hx; exact hx.1)).toEquiv
  have hr_dvd_B : r ∣ Nat.card B := by
    simpa [hcard_eq] using hr_dvd
  have hr_dvd_W : r ∣ Nat.card W :=
    hr_dvd_B.trans (Subgroup.card_dvd_of_le (show B ≤ W from by
      intro x hx
      exact hx.1))
  have hr_pair : r' ∈ ({p, q} : Set Nat.Primes) :=
    hWHall.p_in_pi_of_p_dvd_card r' hr_dvd_W
  rcases Set.mem_insert_iff.mp hr_pair with hrp | hrq
  · exfalso
    have hr_eq_p : r = p.val := congrArg Subtype.val hrp
    have hp_dvd_B : p.val ∣ Nat.card B := by
      simpa [hr_eq_p] using hr_dvd_B
    have hp_dvd_core : p.val ∣ Nat.card (pPrimeCore p.val M) :=
      hp_dvd_B.trans (Subgroup.card_dvd_of_le (show B ≤ pPrimeCore p.val M from by
        intro x hx
        exact hx.2))
    have : Fact p.val.Prime := ⟨p.property⟩
    exact ((p.property.coprime_iff_not_dvd).1
      (pPrimeCore_coprime_card (G := M) (p := p.val))) hp_dvd_core
  · have hrq' : r' = q := by simpa using hrq
    exact congrArg Subtype.val hrq'

private theorem CFSG.section10_pair_hall_nilpotent_of_inf_derived_nilpotent
    {M : Subgroup G} {p q : Nat.Primes} {W : Subgroup M}
    (hM : M ∈ section9MaximalSubgroups G) (hpq : p ≠ q)
    (hpσ : p ∈ section10SigmaPrimes M)
    (hWHall : IsHallSubgroup ({p, q} : Set Nat.Primes) W)
    (hWinfDnil : Group.IsNilpotent (W ⊓ derivedSubgroup M : Subgroup M))
    (hlargest : IsLargestPrimeDivisor p.val (Nat.card (M ⧸ pPrimeCore p.val M)))
    (hpq_lt : p.val < q.val) :
    Group.IsNilpotent W := by
  classical
  have hnil_iff := (Group.isNilpotent_of_finite_tfae (G := W)).out 1 4
  rw [hnil_iff]
  intro r hr P
  by_cases hrW : r ∣ Nat.card W
  · let r' : Nat.Primes := ⟨r, hr.out⟩
    have hr_pair : r' ∈ ({p, q} : Set Nat.Primes) :=
      hWHall.p_in_pi_of_p_dvd_card r' hrW
    rcases Set.mem_insert_iff.mp hr_pair with hrp | hrq
    · have hr_eq_p : r = p.val := congrArg Subtype.val hrp
      subst r
      have : Fact p.val.Prime := ⟨p.property⟩
      let A : Subgroup M := W ⊓ derivedSubgroup M
      let AW : Subgroup W := A.subgroupOf W
      have hAWnormal : AW.Normal := by
        simpa [A, AW, inf_comm] using
          (Subgroup.Normal.subgroupOf
            (inferInstance : (derivedSubgroup M).Normal) W)
      have hAWnil : Group.IsNilpotent AW := by
        have hAW_le : A ≤ W := by
          intro x hx
          exact hx.1
        let e : A ≃* AW := (Subgroup.subgroupOfEquivOfLe (H := A) (K := W) hAW_le).symm
        let : Group.IsNilpotent A := hWinfDnil
        exact Group.nilpotent_of_mulEquiv (G := A) (G' := AW) e
      have hP_le_AW : (P : Subgroup W) ≤ AW :=
        section10_pSubgroup_le_inf_derived_of_sigma
          (G := G) (M := M) (p := p) (W := W) (P := (P : Subgroup W))
          hM hpσ P.isPGroup'
      let PA : Sylow p.val AW := P.subtype hP_le_AW
      have hPAmap_eq : (PA : Subgroup AW).map AW.subtype = (P : Subgroup W) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hP_le_AW hx⟩, hx, rfl⟩
      have hPAmap_le_core :
          (PA : Subgroup AW).map AW.subtype ≤ pCore p.val W :=
        section10_sylow_map_le_pCore_of_nilpotent_normal
          (H := W) (N := AW) hAWnormal hAWnil p.val PA
      have hP_le_core : (P : Subgroup W) ≤ pCore p.val W := by
        intro x hx
        exact hPAmap_le_core (by simpa [hPAmap_eq] using hx)
      have hcore_eq : pCore p.val W = (P : Subgroup W) :=
        P.is_maximal' (pCore_isPGroup (G := W) (p := p.val)) hP_le_core
      rw [← hcore_eq]
      infer_instance
    · have hr_eq_q : r = q.val := by
        have hrq' : r' = q := by simpa using hrq
        exact congrArg Subtype.val hrq'
      subst r
      have : Fact q.val.Prime := ⟨q.property⟩
      let B : Subgroup M := W ⊓ pPrimeCore p.val M
      let BW : Subgroup W := B.subgroupOf W
      have hBWnormal : BW.Normal := by
        simpa [B, BW, inf_comm] using
          (Subgroup.Normal.subgroupOf
            (inferInstance : (pPrimeCore p.val M).Normal) W)
      have hBWq : IsPGroup q.val BW := by
        simpa [B, BW] using
          section10_inf_pPrimeCore_subgroupOf_isPGroup_of_pair_hall
            (G := G) (M := M) (p := p) (q := q) (W := W) hpq hWHall
      have hP_le_BW : (P : Subgroup W) ≤ BW :=
        section10_qSubgroup_le_inf_pPrimeCore_of_largest_lt
          (G := G) (M := M) (p := p) (q := q) (W := W) (Q := (P : Subgroup W))
          hlargest P.isPGroup' hpq_lt
      have hBW_le_core : BW ≤ pCore q.val W :=
        le_sSup (show BW ∈ {K : Subgroup W | K.Normal ∧ IsPGroup q.val K} from
          ⟨hBWnormal, hBWq⟩)
      have hP_le_core : (P : Subgroup W) ≤ pCore q.val W :=
        hP_le_BW.trans hBW_le_core
      have hcore_eq : pCore q.val W = (P : Subgroup W) :=
        P.is_maximal' (pCore_isPGroup (G := W) (p := q.val)) hP_le_core
      rw [← hcore_eq]
      infer_instance
  · have hPbot : (P : Subgroup W) = ⊥ := by
      rcases P.isPGroup'.card_eq_or_dvd with hcard | hdiv
      · exact (Subgroup.card_eq_one (H := (P : Subgroup W))).mp hcard
      · exact False.elim
          (hrW (hdiv.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup W))))
    rw [hPbot]
    infer_instance

private theorem CFSG.section10_exists_nilpotent_pair_hall_containing_of_lt
    {M X : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpM : p ∈ subgroupPrimeSet M)
    (_hqM : q ∈ subgroupPrimeSet M) (hpβ : p ∉ section10BetaPrimes M)
    (hqβ : q ∉ section10BetaPrimes M) (hpq : p ≠ q)
    (hpσ : p ∈ section10SigmaPrimes M) (hXle : X ≤ M)
    (hXq : IsPGroup q.val X) (hpq_lt : p.val < q.val) :
    ∃ W : Subgroup M, X.subgroupOf M ≤ W ∧
      IsHallSubgroup ({p, q} : Set Nat.Primes) W ∧ Group.IsNilpotent W := by
  classical
  let XM : Subgroup M := X.subgroupOf M
  have hXMq : IsPGroup q.val XM := by
    exact hXq.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hXle).symm
  have hXM_le_pPrimeCore : XM ≤ pPrimeCore p.val M := by
    exact section10_pSubgroup_le_pPrimeCore_of_largest_lt
      (H := M) (p := p) (q := q)
      (lemma_10_8_c (G := G) hM hpM hpβ).2.2 hXMq hpq_lt
  have hXMpair : IsPiSubgroup (G := M) ({p, q} : Set Nat.Primes) XM := by
    have : Fact q.val.Prime := ⟨q.property⟩
    intro r hr_dvd
    obtain ⟨n, hcard⟩ := hXMq.exists_card_eq
    have hr_dvd_q : r.val ∣ q.val :=
      r.property.dvd_of_dvd_pow (by simpa [hcard] using hr_dvd)
    have hrq : r = q :=
      Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.property q.property).mp hr_dvd_q)
    simp [hrq]
  let : MulDistribMulAction PUnit.{1} M := {
    smul := fun _ x => x
    one_smul := by intro x; rfl
    mul_smul := by intro a b x; rfl
    smul_mul := by intro a x y; rfl
    smul_one := by intro a; rfl }
  have hXM_inv : IsInvariant PUnit.{1} M XM := by
    refine ⟨?_⟩
    intro a x
    simp
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  obtain ⟨W, hWHall, _hWinv, hXW⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := PUnit.{1}) hMsolv (by simp) ({p, q} : Set Nat.Primes)
      XM hXMpair hXM_inv
  have hWinfDnil : Group.IsNilpotent (W ⊓ derivedSubgroup M : Subgroup M) :=
    section10_inf_derived_nilpotent_of_pair_hall hM hpβ hqβ hWHall
  refine ⟨W, hXW, hWHall, ?_⟩
  exact section10_pair_hall_nilpotent_of_inf_derived_nilpotent
    hM hpq hpσ hWHall hWinfDnil
    (lemma_10_8_c (G := G) hM hpM hpβ).2.2 hpq_lt

/-- Corollary 10.9(a)(1). -/
public theorem CFSG.corollary_10_9_a_1
    {M X : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpM : p ∈ subgroupPrimeSet M)
    (hqM : q ∈ subgroupPrimeSet M) (hpβ : p ∉ section10BetaPrimes M)
    (hqβ : q ∉ section10BetaPrimes M) (hpq : p ≠ q) (hXle : X ≤ M)
    (hXq : IsPGroup q.val X) (hXhyp : X ≤ ambientDerivedSubgroup M ∨ p.val < q.val) :
    ∃ Pσ : Sylow p.val (section10Msigma M),
      section10AmbientSylowSubgroup (section10Msigma M) Pσ ≤ Subgroup.centralizer (X : Set G) := by
  classical
  by_cases hpσ : p ∈ section10SigmaPrimes M
  · rcases hXhyp with hXD | hpq_lt
    · exact section10_corollary_10_9_a_1_of_le_derived
        hM hpβ hqβ hpq hpσ hXle hXq hXD
    · obtain ⟨W, hXW, hWHall, hWnil⟩ :=
        section10_exists_nilpotent_pair_hall_containing_of_lt
          hM hpM hqM hpβ hqβ hpq hpσ hXle hXq hpq_lt
      exact section10_corollary_10_9_a_1_of_nilpotent_pair_hall
        hM hpq hpσ hXle hXq hXW hWHall hWnil
  · exact section10_ambient_sylow_le_centralizer_of_not_mem_sigma hM hpσ
