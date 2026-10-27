module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.lemma_13_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 13 8 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_sylowSubgroupIn_le
    {H K : Subgroup G} {p : Nat.Primes}
    (hK : section12SylowSubgroupIn p K H) :
    K ≤ H := by
  rcases hK with ⟨S, rfl⟩
  exact section13_ambient_sylow_le_base (G := G) H S

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_sylowSubgroupIn_isPGroup
    {H K : Subgroup G} {p : Nat.Primes}
    (hK : section12SylowSubgroupIn p K H) :
    IsPGroup p.val K := by
  rcases hK with ⟨S, rfl⟩
  change IsPGroup p.val ((S : Subgroup H).map H.subtype)
  exact IsPGroup.map (p := p.val) (H := (S : Subgroup H)) S.isPGroup' H.subtype

omit [IsMinCE G] in
private theorem CFSG.section13_sylow_inf_comm
    {M N : Subgroup G} {p : Nat.Primes}
    (R : Sylow p.val (M ⊓ N : Subgroup G)) :
    ∃ R' : Sylow p.val (N ⊓ M : Subgroup G),
      section10AmbientSylowSubgroup (N ⊓ M) R' =
        section10AmbientSylowSubgroup (M ⊓ N) R := by
  classical
  let _ : Fact (Nat.Prime p.val) := ⟨p.property⟩
  let e : (M ⊓ N : Subgroup G) ≃* (N ⊓ M : Subgroup G) :=
    MulEquiv.subgroupCongr (by rw [inf_comm])
  let Rsub : Subgroup (N ⊓ M : Subgroup G) :=
    (R : Subgroup (M ⊓ N : Subgroup G)).map e.toMonoidHom
  have hcard_Rsub :
      Nat.card Rsub = p.val ^ Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p.val := by
    have hmap : Nat.card Rsub = Nat.card (R : Subgroup (M ⊓ N : Subgroup G)) := by
      simpa [Rsub] using
        Subgroup.card_map_of_injective (K := (R : Subgroup (M ⊓ N : Subgroup G)))
          (f := e.toMonoidHom) e.injective
    have hcard_inf :
        Nat.card (M ⊓ N : Subgroup G) = Nat.card (N ⊓ M : Subgroup G) :=
      Nat.card_congr e.toEquiv
    rw [hmap, Sylow.card_eq_multiplicity R, hcard_inf]
  let R' : Sylow p.val (N ⊓ M : Subgroup G) := Sylow.ofCard Rsub hcard_Rsub
  refine ⟨R', ?_⟩
  ext x
  constructor
  · intro hx
    change x ∈ (R' : Subgroup (N ⊓ M : Subgroup G)).map
      (N ⊓ M : Subgroup G).subtype at hx
    change x ∈ Rsub.map (N ⊓ M : Subgroup G).subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    change y ∈ Rsub at hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hyz⟩
    exact Subgroup.mem_map.mpr ⟨z, hz, by
      calc
        (z : G) = (e z : G) := by rfl
        _ = (y : G) := congrArg Subtype.val hyz⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    change ((z : (M ⊓ N : Subgroup G)) : G) ∈
      (R' : Subgroup (N ⊓ M : Subgroup G)).map (N ⊓ M : Subgroup G).subtype
    change ((z : (M ⊓ N : Subgroup G)) : G) ∈
      Rsub.map (N ⊓ M : Subgroup G).subtype
    refine Subgroup.mem_map.mpr ?_
    refine ⟨e z, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem e.toMonoidHom hz
    · rfl

omit [IsMinCE G] in
private theorem CFSG.section13_sylowSubgroupIn_inf_comm
    {M N Q : Subgroup G} {p : Nat.Primes}
    (hQ : section12SylowSubgroupIn p Q (M ⊓ N)) :
    section12SylowSubgroupIn p Q (N ⊓ M) := by
  rcases hQ with ⟨R, hR⟩
  rcases section13_sylow_inf_comm (G := G) (M := M) (N := N) (p := p) R with
    ⟨R', hR'⟩
  exact ⟨R', hR'.trans hR⟩

omit [IsMinCE G] in
private theorem CFSG.section13_sylowSubgroupIn_of_inf_normalizer_le_right
    {M Mstar Q : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q (M ⊓ Mstar))
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar) :
    section12SylowSubgroupIn q Q M := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  rcases hQ with ⟨S, hS⟩
  have hnorm :
      Subgroup.normalizer
          (section8SubgroupInAmbient (S : Subgroup (M ⊓ Mstar : Subgroup G)) : Set G) ≤
        Mstar := by
    intro g hg
    exact hNQ (by
      simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient, ← hS] using hg)
  rcases section8_exists_sylow_left_eq_inf_sylow_of_normalizer_le
      (G := G) (p := q.val) (M := Mstar) (N := M) S hnorm with
    ⟨SM, hSM⟩
  refine ⟨SM, ?_⟩
  calc
    section10AmbientSylowSubgroup M SM =
        section10AmbientSylowSubgroup (M ⊓ Mstar) S := by
      simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hSM
    _ = Q := hS

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_sylowSubgroupIn_of_overgroup_sylow_with_pgroups_le
    {C L Q : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q C)
    (hQleL : Q ≤ L)
    (hL_p_le_C : ∀ Y : Subgroup G, Y ≤ L → IsPGroup q.val Y → Y ≤ C) :
    section12SylowSubgroupIn q Q L := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  rcases hQ with ⟨S, hS⟩
  let Rsub : Subgroup L := Q.subgroupOf L
  have hQp : IsPGroup q.val Q := by
    have hmap_p : IsPGroup q.val (section10AmbientSylowSubgroup C S) := by
      change IsPGroup q.val ((S : Subgroup C).map C.subtype)
      exact IsPGroup.map (p := q.val) (H := (S : Subgroup C)) S.isPGroup' C.subtype
    rw [← hS]
    exact hmap_p
  have hRsub_p : IsPGroup q.val Rsub :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Q) (K := L) hQleL).symm
  have hRsub_max :
      ∀ {Y : Subgroup L}, IsPGroup q.val Y → Rsub ≤ Y → Y = Rsub := by
    intro Y hYp hRsubY
    let YG : Subgroup G := Y.map L.subtype
    have hYGp : IsPGroup q.val YG := IsPGroup.map hYp L.subtype
    have hYG_le_L : YG ≤ L := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hYG_le_C : YG ≤ C := hL_p_le_C YG hYG_le_L hYGp
    let YC : Subgroup C := YG.subgroupOf C
    have hYCp : IsPGroup q.val YC :=
      hYGp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := YG) (K := C) hYG_le_C).symm
    have hS_le_YC : (S : Subgroup C) ≤ YC := by
      intro z hz
      have hzQ : ((z : C) : G) ∈ Q := by
        rw [← hS]
        exact Subgroup.mem_map_of_mem C.subtype hz
      have hzL : ((z : C) : G) ∈ L := hQleL hzQ
      let zL : L := ⟨((z : C) : G), hzL⟩
      have hzR : zL ∈ Rsub := by
        simpa [Rsub, Subgroup.mem_subgroupOf, zL] using hzQ
      have hzY : zL ∈ Y := hRsubY hzR
      have hzYG : ((z : C) : G) ∈ YG :=
        Subgroup.mem_map_of_mem L.subtype hzY
      simpa [YC, Subgroup.mem_subgroupOf] using hzYG
    have hYC_eq : YC = S := S.is_maximal' hYCp hS_le_YC
    apply le_antisymm
    · intro y hy
      have hyYG : ((y : L) : G) ∈ YG := Subgroup.mem_map_of_mem L.subtype hy
      have hyC : ((y : L) : G) ∈ C := hYG_le_C hyYG
      let yC : C := ⟨((y : L) : G), hyC⟩
      have hyYC : yC ∈ YC := by
        simpa [YC, Subgroup.mem_subgroupOf, yC] using hyYG
      have hyS : yC ∈ (S : Subgroup C) := by
        simpa [hYC_eq] using hyYC
      have hyQ : ((y : L) : G) ∈ Q := by
        rw [← hS]
        exact Subgroup.mem_map_of_mem C.subtype hyS
      simpa [Rsub, Subgroup.mem_subgroupOf] using hyQ
    · exact hRsubY
  let R : Sylow q.val L := ⟨Rsub, hRsub_p, by
    intro Y hYp hRsubY
    exact hRsub_max hYp hRsubY⟩
  refine ⟨R, ?_⟩
  calc
    section10AmbientSylowSubgroup L R = Rsub.map L.subtype := by
      simp [section10AmbientSylowSubgroup, R]
    _ = Q := Subgroup.map_subgroupOf_eq_of_le hQleL

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_ne_bot_of_normalizer_le_maximal
    {M Q : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ M) :
    Q ≠ ⊥ := by
  intro hQbot
  have htop_le_M : (⊤ : Subgroup G) ≤ M := by
    intro g _hg
    exact hNQ (by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp [hQbot])
  exact hM.1 (top_le_iff.mp htop_le_M)

omit [IsMinCE G] in
public theorem CFSG.section13_notUnique_of_crossed_normalizer
    {M Mstar Q : Subgroup G}
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar) :
    section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M} := by
  intro huniq
  have hMstar_mem :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) :=
    ⟨hMstar, hNQ⟩
  have hMstar_eq_M : Mstar = M := by
    simpa [huniq] using hMstar_mem
  exact hnotconj 1 (by
    simpa [hMstar_eq_M] using section8_conjBy_one (G := G) Mstar)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_primeOrderSubgroupsIn_isPGroup
    {P H : Subgroup G} {p : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p H) :
    IsPGroup p.val P := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨_hPH, hPcard⟩
  refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
  simpa [pow_one] using hPcard

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_primeOrderSubgroupsIn_mono
    {P H K : Subgroup G} {p : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p H) (hHK : H ≤ K) :
    P ∈ section10PrimeOrderSubgroupsIn p K := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPH, hPcard⟩
  simpa [section10PrimeOrderSubgroupsIn] using ⟨hPH.trans hHK, hPcard⟩

omit [IsMinCE G] in
public theorem CFSG.section13_ne_of_fixedpoint_free_p_sylow
    {P Q H : Subgroup G} {p q : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p H)
    (hQq : IsPGroup q.val Q)
    (hQne : Q ≠ ⊥)
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥) :
    q ≠ p := by
  intro hqp
  subst q
  let _ : Fact p.val.Prime := ⟨p.property⟩
  have hPp : IsPGroup p.val P :=
    section13_primeOrderSubgroupsIn_isPGroup (G := G) hP
  have hQ_dvd : p.val ∣ Nat.card Q := by
    rcases hQq.card_eq_or_dvd with hcard | hdiv
    · exact False.elim (hQne ((Subgroup.card_eq_one (H := Q)).1 hcard))
    · exact hdiv
  let _ : Subgroup.Normalizes P Q := ⟨hPinvQ⟩
  have hone_fixed : (1 : Q) ∈ MulAction.fixedPoints P Q := by
    simp [MulAction.mem_fixedPoints]
  rcases hPp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := Q) hQ_dvd hone_fixed with
    ⟨x, hxfix, h1x⟩
  have hfixed_eq :
      fixedPointSubgroup (↥P) (↥Q) = (subgroupCentralizerIn Q P).subgroupOf Q := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Q P hPinvQ
  have hxfix_sub : x ∈ fixedPointSubgroup (↥P) (↥Q) := by
    simpa [fixedPointSubgroup] using hxfix
  have hxCsub : x ∈ (subgroupCentralizerIn Q P).subgroupOf Q := by
    simpa [hfixed_eq] using hxfix_sub
  have hxC : (x : G) ∈ subgroupCentralizerIn Q P := by
    simpa [Subgroup.mem_subgroupOf] using hxCsub
  have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
    simpa [hCQ] using hxC
  have hx_one : x = 1 := by
    apply Subtype.ext
    simpa using hxbot
  exact h1x hx_one.symm

omit [IsMinCE G] in
public theorem CFSG.section13_pPrimeSet_of_fixedpoint_free_sylow
    {P Q H : Subgroup G} {p q : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p H)
    (hQq : IsPGroup q.val Q)
    (hQne : Q ≠ ⊥)
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥) :
    q ∈ section10PPrimeSet p := by
  rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact section13_ne_of_fixedpoint_free_p_sylow
    (G := G) (P := P) (Q := Q) (H := H) (p := p) (q := q)
    hP hQq hQne hPinvQ hCQ

omit [IsMinCE G] in
public theorem CFSG.section13_E3_sylow_as_E_sylow
    {M E E₃ : Subgroup G} {q : Nat.Primes}
    (hE₃Hall : section12HallSubgroupIn (section12Tau3Primes M) E₃ E)
    (hqτ3 : q ∈ section12Tau3Primes M) (S : Sylow q.val E₃) :
    ∃ T : Sylow q.val E,
      section10AmbientSylowSubgroup E T = section10AmbientSylowSubgroup E₃ S := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  rcases hE₃Hall with ⟨hE₃E, hHallE₃⟩
  let f : E₃ →* E := E₃.subtype.codRestrict E (fun x => hE₃E x.property)
  let K : Subgroup E := (S : Subgroup E₃).map f
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : E => (z : G)) hxy
  have hKp : IsPGroup q.val K := by
    change IsPGroup q.val ((S : Subgroup E₃).map f)
    exact IsPGroup.map (p := q.val) (H := (S : Subgroup E₃)) S.isPGroup' f
  have hK_not_index : ¬ q.val ∣ K.index := by
    intro hqKidx
    have hidx : K.index = (S : Subgroup E₃).index * f.range.index := by
      simpa [K] using (Subgroup.index_map_of_injective (H := (S : Subgroup E₃)) hf_inj)
    have hqprod : q.val ∣ (S : Subgroup E₃).index * f.range.index := by
      simpa [hidx] using hqKidx
    rcases q.property.dvd_mul.mp hqprod with hqSidx | hqrange
    · exact S.not_dvd_index hqSidx
    · have hrange_eq : f.range = E₃.subgroupOf E := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, _hy, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x, hx⟩, by simp [f]⟩
      exact (hHallE₃.p_in_pi_of_p_dvd_index q (by simpa [hrange_eq] using hqrange)) hqτ3
  let T : Sylow q.val E := hKp.toSylow hK_not_index
  refine ⟨T, ?_⟩
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨t, ht, rfl⟩
    change ((t : E) : G) ∈ section10AmbientSylowSubgroup E₃ S
    have htK : (t : E) ∈ K := by
      simpa [T, IsPGroup.toSylow_coe] using ht
    rcases Subgroup.mem_map.mp htK with ⟨s, hs, hs_eq⟩
    rw [← congrArg Subtype.val hs_eq]
    exact Subgroup.mem_map_of_mem E₃.subtype hs
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨s, hs, rfl⟩
    change ((s : E₃) : G) ∈ section10AmbientSylowSubgroup E T
    have hfs : f s ∈ (T : Subgroup E) := by
      simpa [T, K, IsPGroup.toSylow_coe] using Subgroup.mem_map_of_mem f hs
    rw [section10AmbientSylowSubgroup, Subgroup.mem_map]
    exact ⟨f s, hfs, by simp [f]⟩

public theorem CFSG.section13_E_sylowSubgroupIn_M_of_sigma_compl
    {M E : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E)
    (hqσc : q ∉ section10SigmaPrimes M) (T : Sylow q.val E) :
    section12SylowSubgroupIn q (section10AmbientSylowSubgroup E T) M := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  have hEM : E ≤ M := hcomp.2.1
  have hHallE : IsHallSubgroup (section10SigmaPrimes M)ᶜ (E.subgroupOf M) :=
    section12_msigma_complement_isHall_sigma_compl hM hcomp
  let f : E →* M := E.subtype.codRestrict M (fun x => hEM x.property)
  let K : Subgroup M := (T : Subgroup E).map f
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : M => (z : G)) hxy
  have hKp : IsPGroup q.val K := by
    change IsPGroup q.val ((T : Subgroup E).map f)
    exact IsPGroup.map (p := q.val) (H := (T : Subgroup E)) T.isPGroup' f
  have hqπ : q ∈ (section10SigmaPrimes M)ᶜ := by
    simpa using hqσc
  have hK_not_index : ¬ q.val ∣ K.index := by
    intro hqKidx
    have hidx : K.index = (T : Subgroup E).index * f.range.index := by
      simpa [K] using (Subgroup.index_map_of_injective (H := (T : Subgroup E)) hf_inj)
    have hqprod : q.val ∣ (T : Subgroup E).index * f.range.index := by
      simpa [hidx] using hqKidx
    rcases q.property.dvd_mul.mp hqprod with hqTidx | hqrange
    · exact T.not_dvd_index hqTidx
    · have hrange_eq : f.range = E.subgroupOf M := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, _hy, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x, hx⟩, by simp [f]⟩
      exact (hHallE.p_in_pi_of_p_dvd_index q (by simpa [hrange_eq] using hqrange)) hqπ
  let TM : Sylow q.val M := hKp.toSylow hK_not_index
  refine ⟨TM, ?_⟩
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨t, ht, rfl⟩
    change ((t : M) : G) ∈ section10AmbientSylowSubgroup E T
    have htK : (t : M) ∈ K := by
      simpa [TM, IsPGroup.toSylow_coe] using ht
    rcases Subgroup.mem_map.mp htK with ⟨s, hs, hs_eq⟩
    rw [← congrArg Subtype.val hs_eq]
    exact Subgroup.mem_map_of_mem E.subtype hs
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨s, hs, rfl⟩
    change ((s : E) : G) ∈ section10AmbientSylowSubgroup M TM
    have hfs : f s ∈ (TM : Subgroup M) := by
      simpa [TM, K, IsPGroup.toSylow_coe] using Subgroup.mem_map_of_mem f hs
    rw [section10AmbientSylowSubgroup, Subgroup.mem_map]
    exact ⟨f s, hfs, by simp [f]⟩

omit [IsMinCE G] in
public theorem CFSG.section13_subgroupCentralizerIn_eq_bot_of_cyclic_pgroup_noncentral
    {P Q : Subgroup G} {q : Nat.Primes}
    (hQq : IsPGroup q.val Q) (hQcyc : IsCyclic Q)
    (hPnormQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card P))
    (hnotCent : ¬ P ≤ Subgroup.centralizer (Q : Set G)) :
    subgroupCentralizerIn Q P = ⊥ := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let _ : IsCyclic Q := hQcyc
  rcases IsPGroup.commutator_eq_bot_or_commutator_eq_self
      (p := q.val) (P := Q) (K := P) hQq hPnormQ hcop with
    hcomm_bot | hcomm_self
  · exact False.elim <|
      hnotCent
        ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := P) (H₂ := Q)).mp
          hcomm_bot)
  have hcomm_QP : ⁅Q, P⁆ = Q := by
    simpa [Subgroup.commutator_comm] using hcomm_self
  have hQcomm : IsMulCommutative Q := by
    let _ : CommGroup Q := hQcyc.commGroup
    infer_instance
  let _ : Subgroup.Normalizes P Q := ⟨hPnormQ⟩
  let Cfix : Subgroup Q := fixedPointSubgroup (↥P) (↥Q)
  let Ccomm : Subgroup Q := commutatorAction (A := ↥P) (G := ↥Q)
  have hfixed_eq :
      Cfix = (subgroupCentralizerIn Q P).subgroupOf Q := by
    simpa [Cfix] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Q P hPnormQ
  have hcomm_map : Ccomm.map Q.subtype = ⁅Q, P⁆ := by
    simpa [Ccomm] using
      commutatorAction_subgroup_conj_map_eq_commutator Q P hPnormQ
  have hCcomm_top : Ccomm = ⊤ := by
    apply le_antisymm le_top
    intro x _hx
    have hxMap : (x : G) ∈ Ccomm.map Q.subtype := by
      rw [hcomm_map, hcomm_QP]
      exact x.property
    rcases Subgroup.mem_map.mp hxMap with ⟨y, hyC, hyx⟩
    have hy_eq : y = x := Subtype.ext hyx
    simpa [hy_eq] using hyC
  have hsolvQ : Group.IsSolvable Q := by
    let _ : IsMulCommutative Q := hQcomm
    infer_instance
  have hcompl : IsCompl Cfix Ccomm := by
    simpa [Cfix, Ccomm] using
      (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := Q) (A := P) hsolvQ hcop.symm hQcomm)
  have hfix_bot : Cfix = ⊥ := by
    have hdisj := hcompl.disjoint.eq_bot
    simpa [hCcomm_top] using hdisj
  have hCsub_bot : (subgroupCentralizerIn Q P).subgroupOf Q = ⊥ := by
    simpa [hfixed_eq] using hfix_bot
  refine le_bot_iff.mp ?_
  intro x hx
  have hxsub : (⟨x, hx.1⟩ : Q) ∈ (subgroupCentralizerIn Q P).subgroupOf Q := by
    simpa [Subgroup.mem_subgroupOf] using hx
  have hxbot : (⟨x, hx.1⟩ : Q) ∈ (⊥ : Subgroup Q) := by
    simpa [hCsub_bot] using hxsub
  have hxone : x = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
  simp [hxone]

omit [IsMinCE G] in
private theorem CFSG.section13_le_ambientDerived_of_fixedpoint_free_sylow
    {M P Q H : Subgroup G} {p q : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p H)
    (hP_M : P ≤ M)
    (hQ_M : Q ≤ M)
    (hQq : IsPGroup q.val Q)
    (hQne : Q ≠ ⊥)
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥) :
    Q ≤ ambientDerivedSubgroup M := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  have hq_ne_p : q ≠ p :=
    section13_ne_of_fixedpoint_free_p_sylow
      (G := G) (P := P) (Q := Q) (H := H) (p := p) (q := q)
      hP hQq hQne hPinvQ hCQ
  have hPp : IsPGroup p.val P :=
    section13_primeOrderSubgroupsIn_isPGroup (G := G) hP
  have hPπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) P :=
    section8_isPiSubgroup_singleton_of_isPGroup hPp
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
    section8_isPiSubgroup_singleton_of_isPGroup hQq
  have hdis_pq : Disjoint ({p} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro r hrp hrq
    have hrp_eq : r = p := by simpa using hrp
    have hrq_eq : r = q := by simpa using hrq
    exact hq_ne_p (hrq_eq.symm.trans hrp_eq)
  have hcop : Nat.Coprime (Nat.card P) (Nat.card Q) :=
    section13_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) hPπ hQπ hdis_pq
  let _ : Subgroup.Normalizes P Q := ⟨hPinvQ⟩
  have hfixed_eq :
      fixedPointSubgroup (↥P) (↥Q) = (subgroupCentralizerIn Q P).subgroupOf Q := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Q P hPinvQ
  have hfix_bot : fixedPointSubgroup (↥P) (↥Q) = ⊥ := by
    rw [hfixed_eq]
    simpa using congrArg (fun S : Subgroup G => S.subgroupOf Q) hCQ
  have hQnil : Group.IsNilpotent Q :=
    IsPGroup.isNilpotent (p := q.val) (G := Q) hQq
  let _ : Group.IsNilpotent Q := hQnil
  have hsolvQ : Group.IsSolvable Q := inferInstance
  have hsup :
      fixedPointSubgroup (↥P) (↥Q) ⊔ commutatorAction (A := ↥P) (G := ↥Q) = ⊤ :=
    proposition_1_6_a (G := ↥Q) (A := ↥P) hsolvQ hcop
  have hcomm_top : commutatorAction (A := ↥P) (G := ↥Q) = ⊤ := by
    rw [hfix_bot, bot_sup_eq] at hsup
    exact hsup
  have hcomm_map :
      (commutatorAction (A := ↥P) (G := ↥Q)).map Q.subtype = ⁅Q, P⁆ := by
    simpa using commutatorAction_subgroup_conj_map_eq_commutator Q P hPinvQ
  have htop_map : (⊤ : Subgroup Q).map Q.subtype = Q := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hcomm_eq : ⁅Q, P⁆ = Q := by
    calc
      ⁅Q, P⁆ = (commutatorAction (A := ↥P) (G := ↥Q)).map Q.subtype := by
        exact hcomm_map.symm
      _ = (⊤ : Subgroup Q).map Q.subtype := by rw [hcomm_top]
      _ = Q := htop_map
  rw [← hcomm_eq]
  exact section13_commutator_le_ambientDerived_of_le (G := G) hQ_M hP_M

omit [IsMinCE G] in
private theorem CFSG.section13_ambientDerived_sylow_of_sylowSubgroupIn
    {M Q : Subgroup G} {q : Nat.Primes}
    (hQ_M : section12SylowSubgroupIn q Q M)
    (hQ_D : Q ≤ ambientDerivedSubgroup M) :
    ∃ X : Sylow q.val (ambientDerivedSubgroup M),
      section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X = Q := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  rcases hQ_M with ⟨SM, hSM⟩
  let D : Subgroup M := derivedSubgroup M
  let Dg : Subgroup G := ambientDerivedSubgroup M
  have hSM_le_D : (SM : Subgroup M) ≤ D := by
    intro x hx
    have hxQ : ((x : M) : G) ∈ Q := by
      rw [← hSM]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxDg : ((x : M) : G) ∈ Dg := hQ_D hxQ
    change ((x : M) : G) ∈ ambientDerivedSubgroup M at hxDg
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxDg
    rcases hxDg with ⟨y, hyD, hyx⟩
    have hyxM : y = x := Subtype.ext hyx
    simpa [D, hyxM] using hyD
  let SD : Sylow q.val D := SM.subtype hSM_le_D
  let e : D ≃* Dg := by
    change D ≃* D.map M.subtype
    exact Subgroup.equivMapOfInjective D M.subtype M.subtype_injective
  let X : Sylow q.val Dg := SD.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨X, ?_⟩
  ext x
  constructor
  · intro hx
    change x ∈ (X : Subgroup Dg).map Dg.subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨yDg, hyX, rfl⟩
    have hyX' : yDg ∈ (SD : Subgroup D).map e.toMonoidHom := by
      simpa [X] using hyX
    rcases Subgroup.mem_map.mp hyX' with ⟨yD, hySD, hy_eq⟩
    have hySM : (yD : M) ∈ (SM : Subgroup M) := by
      exact hySD
    have hyQ : (((yD : D) : M) : G) ∈ Q := by
      rw [← hSM]
      exact Subgroup.mem_map.mpr ⟨(yD : M), hySM, rfl⟩
    have hy_val : (yDg : G) = (((yD : D) : M) : G) := by
      calc
        (yDg : G) = (e yD : G) := congrArg Subtype.val hy_eq.symm
        _ = (((yD : D) : M) : G) := by
          unfold e
          exact Subgroup.coe_equivMapOfInjective_apply
            D M.subtype M.subtype_injective yD
    simpa [hy_val] using hyQ
  · intro hx
    have hxDg : x ∈ Dg := hQ_D hx
    let xDg : Dg := ⟨x, hxDg⟩
    have hxM : x ∈ M := by
      change x ∈ ambientDerivedSubgroup M at hxDg
      rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxDg
      rcases hxDg with ⟨y, _hyD, rfl⟩
      exact y.property
    let xM : M := ⟨x, hxM⟩
    have hxSM : xM ∈ (SM : Subgroup M) := by
      have hx_ambient : x ∈ section10AmbientSylowSubgroup M SM := by
        simpa [hSM] using hx
      rcases Subgroup.mem_map.mp hx_ambient with ⟨y, hySM, hyx⟩
      have hyxM : y = xM := Subtype.ext hyx
      simpa [hyxM] using hySM
    have hxD : xM ∈ D := hSM_le_D hxSM
    let xD : D := ⟨xM, hxD⟩
    have hxSD : xD ∈ (SD : Subgroup D) := by
      exact hxSM
    refine Subgroup.mem_map.mpr ?_
    refine ⟨xDg, ?_, rfl⟩
    change xDg ∈ (X : Subgroup Dg)
    change xDg ∈ (SD : Subgroup D).map e.toMonoidHom
    refine Subgroup.mem_map.mpr ?_
    refine ⟨xD, hxSD, ?_⟩
    apply Subtype.ext
    unfold e
    exact Subgroup.coe_equivMapOfInjective_apply
      D M.subtype M.subtype_injective xD

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_local_normalizer_le_subgroupNormalizerIn
    {M X : Subgroup G} (hXleM : X ≤ M) :
    Subgroup.normalizer (((X.subgroupOf M) : Subgroup M) : Set M) ≤
      (subgroupNormalizerIn M (X : Set G)).subgroupOf M := by
  classical
  let XM : Subgroup M := X.subgroupOf M
  intro x hx
  change (x : G) ∈ subgroupNormalizerIn M (X : Set G)
  rw [mem_subgroupNormalizerIn]
  constructor
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyX
      have hyM : y ∈ M := hXleM hyX
      let yM : M := ⟨y, hyM⟩
      have hyXM : yM ∈ XM := hyX
      have hconjM :
          ((x : M) * yM * (x : M)⁻¹ : M) ∈ XM :=
        (Subgroup.mem_normalizer_iff.mp hx yM).1 hyXM
      change ((x : G) * y * (x : G)⁻¹) ∈ X at hconjM
      exact hconjM
    · intro hconjX
      have hyM : y ∈ M := by
        have hxM : (x : G) ∈ M := x.property
        have hconjM : (x : G) * y * (x : G)⁻¹ ∈ M := hXleM hconjX
        have hy_eq : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) := by
          simp [mul_assoc]
        rw [hy_eq]
        exact M.mul_mem (M.mul_mem (M.inv_mem hxM) hconjM) hxM
      let yM : M := ⟨y, hyM⟩
      have hconjXM :
          ((x : M) * yM * (x : M)⁻¹ : M) ∈ XM := by
        change ((x : G) * y * (x : G)⁻¹) ∈ X
        exact hconjX
      exact (Subgroup.mem_normalizer_iff.mp hx yM).2 hconjXM
  · exact x.property

private theorem CFSG.section13_malpha_sup_subgroupNormalizerIn_of_derived_sylow
    {M Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hQ_M : section12SylowSubgroupIn q Q M)
    (hQ_D : Q ≤ ambientDerivedSubgroup M) :
    section10Malpha M ⊔ subgroupNormalizerIn M (Q : Set G) = M := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  rcases hQ_M with ⟨SQ, hSQmap⟩
  let K : Subgroup M := section10MalphaSubgroup M
  let Qsub : Subgroup M := Q.subgroupOf M
  let U : Subgroup G := subgroupNormalizerIn M (Q : Set G)
  let Usub : Subgroup M := U.subgroupOf M
  let J : Subgroup M := K ⊔ Qsub
  have hQ_le_M : Q ≤ M := by
    intro x hx
    rw [← hSQmap] at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hSQ_le_J : (SQ : Subgroup M) ≤ J := by
    intro x hx
    have hxQ : ((x : M) : G) ∈ Q := by
      rw [← hSQmap]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact Subgroup.mem_sup_right (show x ∈ Qsub from hxQ)
  let SJ : Sylow q.val J := SQ.subtype hSQ_le_J
  have hSJmap : (SJ : Subgroup J).map J.subtype = Qsub := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hySQ : (y : M) ∈ (SQ : Subgroup M) := by
        change (y : M) ∈ (SQ : Subgroup M) at hy
        exact hy
      have hyQ : (((y : J) : M) : G) ∈ Q := by
        rw [← hSQmap]
        exact Subgroup.mem_map.mpr ⟨(y : M), hySQ, rfl⟩
      exact hyQ
    · intro hx
      have hxQ : ((x : M) : G) ∈ Q := hx
      have hxSQ : x ∈ (SQ : Subgroup M) := by
        have hxmap : ((x : M) : G) ∈ (SQ : Subgroup M).map M.subtype := by
          have hxamb : ((x : M) : G) ∈ section10AmbientSylowSubgroup M SQ := by
            rwa [hSQmap]
          simpa [section10AmbientSylowSubgroup] using hxamb
        rcases Subgroup.mem_map.mp hxmap with ⟨y, hySQ, hyx⟩
        have hy_eq : y = x := Subtype.ext hyx
        simpa [hy_eq] using hySQ
      have hxJ : x ∈ J := hSQ_le_J hxSQ
      refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
      change (x : M) ∈ (SQ : Subgroup M)
      exact hxSQ
  have hJnormal : J.Normal := by
    rcases section13_ambientDerived_sylow_of_sylowSubgroupIn
        (G := G) (M := M) (Q := Q) (q := q) (show section12SylowSubgroupIn q Q M from
          ⟨SQ, hSQmap⟩) hQ_D with
      ⟨X, hXmap⟩
    have hnormal :=
      section10_malpha_sup_ambient_derived_sylow_normal
        (G := G) (M := M) hM X
    simpa [J, K, Qsub, hXmap] using hnormal
  let _ : J.Normal := hJnormal
  have hFr :
      Subgroup.normalizer ((Qsub : Subgroup M) : Set M) ⊔ J = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (G := M) (N := J) SJ
    simpa [hSJmap] using h
  have hQsub_le_Usub : Qsub ≤ Usub := by
    intro x hx
    change (x : G) ∈ U
    exact le_subgroupNormalizerIn hQ_le_M hx
  have hnorm_le_Usub :
      Subgroup.normalizer ((Qsub : Subgroup M) : Set M) ≤ Usub := by
    simpa [Qsub, U, Usub] using
      section13_local_normalizer_le_subgroupNormalizerIn (G := G) hQ_le_M
  have hlocal : K ⊔ Usub = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hFr]
    exact sup_le
      (hnorm_le_Usub.trans le_sup_right)
      (sup_le le_sup_left (hQsub_le_Usub.trans le_sup_right))
  have hU_le_M : U ≤ M := by
    simpa [U] using subgroupNormalizerIn_le M (Q : Set G)
  have hUmap : Usub.map M.subtype = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hU_le_M hx⟩, hx, rfl⟩
  have htop_map : (⊤ : Subgroup M).map M.subtype = M := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  calc
    section10Malpha M ⊔ U =
        (K ⊔ Usub).map M.subtype := by
          rw [Subgroup.map_sup]
          simp [K, Usub, U, section10Malpha, hUmap]
    _ = (⊤ : Subgroup M).map M.subtype := by rw [hlocal]
    _ = M := htop_map

private theorem CFSG.section13_lemma_13_8_side_12_18
    {M Mstar P Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hpM : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hQ : section12SylowSubgroupIn q Q (M ⊓ Mstar))
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar) :
    section10AlphaPrimes M = section10BetaPrimes M ∧
      section10Malpha M ≠ ⊥ ∧ q ∉ section10AlphaPrimes M ∧
        subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
          subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥ := by
  classical
  have hP_M : P ∈ section10PrimeOrderSubgroupsIn p M :=
    section13_primeOrderSubgroupsIn_mono (G := G) hP inf_le_left
  have hQ_M : section12SylowSubgroupIn q Q M :=
    section13_sylowSubgroupIn_of_inf_normalizer_le_right
      (G := G) (M := M) (Mstar := Mstar) hQ hNQ
  have hQ_le_M : Q ≤ M := section13_sylowSubgroupIn_le (G := G) hQ_M
  have hQq : IsPGroup q.val Q := section13_sylowSubgroupIn_isPGroup (G := G) hQ
  have hQne : Q ≠ ⊥ :=
    section13_ne_bot_of_normalizer_le_maximal (G := G) hMstar hNQ
  have hqP : q ∈ section10PPrimeSet p :=
    section13_pPrimeSet_of_fixedpoint_free_sylow
      (G := G) (P := P) (Q := Q) (H := M ⊓ Mstar)
      hP hQq hQne hPinvQ hCQ
  have hnotUnique :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M} :=
    section13_notUnique_of_crossed_normalizer
      (G := G) (M := M) (Mstar := Mstar) hMstar hnotconj hNQ
  exact lemma_12_18_b (G := G) (M := M) (P := P) (Q := Q)
    (p := p) (q := q) hM hpM hP_M hqP hQ_le_M hQne hQq hPinvQ hCQ
    hnotUnique hQ_M

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_lemma_13_8_absurd_of_malpha_centralizer_le_centralizer
    {A P Q : Subgroup G}
    (hCP_ne : subgroupCentralizerIn A P ≠ ⊥)
    (hCPQ_bot : subgroupCentralizerIn A (P ⊔ Q) = ⊥)
    (hCP_cent_Q : subgroupCentralizerIn A P ≤ Subgroup.centralizer (Q : Set G)) :
    False := by
  have hCP_le_CPQ :
      subgroupCentralizerIn A P ≤ subgroupCentralizerIn A (P ⊔ Q) :=
    section13_subgroupCentralizerIn_sup_of_le_centralizer
      (G := G) (A := A) (R := P) (Q := Q)
      (C := subgroupCentralizerIn A P) le_rfl hCP_cent_Q
  have hCP_bot : subgroupCentralizerIn A P = ⊥ :=
    le_bot_iff.mp (by
      rw [← hCPQ_bot]
      exact hCP_le_CPQ)
  exact hCP_ne hCP_bot

private theorem CFSG.section13_lemma_13_8_malpha_centralizer_le_mstar_of_theorem_13_4_bridge
    {M Mstar E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hrE : r ∈ subgroupPrimeSet E)
    (hR : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hNR_le_Mstar : Subgroup.normalizer (R : Set G) ≤ Mstar) :
    subgroupCentralizerIn (section10Malpha M) P ≤ Mstar := by
  classical
  have hCP_le_CPσ :
      subgroupCentralizerIn (section10Malpha M) P ≤
        subgroupCentralizerIn (section10Msigma M) P := by
    intro x hx
    exact ⟨section13_malpha_le_msigma (G := G) hM hx.1, hx.2⟩
  have hCPσ_le_CRσ :
      subgroupCentralizerIn (section10Msigma M) P ≤
        subgroupCentralizerIn (section10Msigma M) R :=
    theorem_13_4 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (R := R)
      (p := p) (r := r) hM hE hpτ1 hP hrE hR
  intro x hx
  exact hNR_le_Mstar ((centralizer_le_normalizer R) (hCPσ_le_CRσ (hCP_le_CPσ hx)).2)


private theorem CFSG.section13_lemma_13_8_bridge_of_beta_R_in_M_normalizer
    {M Mstar P Q R : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hpM : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hR_M : R ≤ M)
    (hR_normQ : R ≤ subgroupNormalizerIn M (Q : Set G))
    (hR_centP : R ≤ Subgroup.centralizer (P : Set G))
    (hRcard : Nat.card R = r.val)
    (hrβstar : r ∈ section10BetaPrimes Mstar) :
    ∃ r : Nat.Primes, ∃ R E E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ ∧
        P ∈ section10PrimeOrderSubgroupsIn p E ∧
          r ∈ subgroupPrimeSet E ∧
            R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P) ∧
              Subgroup.normalizer (R : Set G) ≤ Mstar := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_inf, hPcard⟩
  have hP_M : P ≤ M := hP_inf.1
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hp_notσ : p ∉ section10SigmaPrimes M := by
    rcases (by simpa [section12Tau1Primes] using hpM) with
      ⟨hpσ, _hpD, _hrank⟩
    exact hpσ
  have hPπc : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ P :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem hp_notσ hPp
  have hRr : IsPGroup r.val R := by
    refine IsPGroup.of_card (p := r.val) (G := R) (n := 1) ?_
    simpa [pow_one] using hRcard
  have hRne : R ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hRcard
  have hrαstar : r ∈ section10AlphaPrimes Mstar := hrβstar.1
  have hr_notσ : r ∉ section10SigmaPrimes M := by
    have hdis : Disjoint (section10AlphaPrimes Mstar) (section10SigmaPrimes M) :=
      (lemma_10_12_a (G := G) (M := Mstar) (H := M) hMstar hM
        (section13_notConjugate_symm (G := G) hnotconj)).2
    rw [Set.disjoint_left] at hdis
    exact hdis hrαstar
  have hRπc : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ R :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem hr_notσ hRr
  have hP_cent_R : P ≤ Subgroup.centralizer (R : Set G) :=
    (Subgroup.le_centralizer_iff (H := R) (K := P)).mp hR_centP
  have hP_norm_R : P ≤ Subgroup.normalizer (R : Set G) :=
    hP_cent_R.trans (centralizer_le_normalizer R)
  let A : Subgroup G := P ⊔ R
  have hA_M : A ≤ M := sup_le hP_M hR_M
  have hAπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ A := by
    simpa [A] using
      section13_isPiSubgroup_sup_of_le_normalizer
        (G := G) (π := (section10SigmaPrimes M)ᶜ) (H := P) (K := R)
        hPπc hRπc hP_norm_R
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := A) hM hA_M hAπ with
    ⟨E, E₁₂, E₁, E₂, E₃, hE, hA_E⟩
  have hP_E : P ∈ section10PrimeOrderSubgroupsIn p E := by
    have hPE : P ≤ E := (show P ≤ A from le_sup_left).trans hA_E
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hPE, hPcard⟩
  have hR_E : R ≤ E := (show R ≤ A from le_sup_right).trans hA_E
  have hrE : r ∈ subgroupPrimeSet E :=
    section8_subgroupPrimeSet_mono hR_E (by
      rw [subgroupPrimeSet, hRcard]
      exact dvd_rfl)
  have hR_CEP : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P) := by
    simpa [section10PrimeOrderSubgroupsIn, subgroupCentralizerIn] using
      ⟨⟨hR_E, hR_centP⟩, hRcard⟩
  have hR_Mstar : R ≤ Mstar :=
    hR_normQ.trans ((subgroupNormalizerIn_le_normalizer M (Q : Set G)).trans hNQ)
  have hRπβstar : IsPiSubgroup (G := G) (section10BetaPrimes Mstar) R := by
    intro s hsR
    have hs_single : s ∈ ({r} : Set Nat.Primes) :=
      section8_isPiSubgroup_singleton_of_isPGroup hRr s hsR
    have hs_eq : s = r := by simpa using hs_single
    simpa [hs_eq] using hrβstar
  let S : Sylow r.val G := Classical.choice (Sylow.nonempty (p := r.val) (G := G))
  have hNR_le_Mstar : Subgroup.normalizer (R : Set G) ≤ Mstar :=
    proposition_10_14_d (G := G) (p := r) hrβstar.2 S
      (M := Mstar) (Y := R) hMstar hR_Mstar hRne hRπβstar
  exact ⟨r, R, E, E₁₂, E₁, E₂, E₃, hE, hP_E, hrE, hR_CEP, hNR_le_Mstar⟩


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_malpha_le_maximal (M : Subgroup G) :
    section10Malpha M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

private theorem CFSG.section13_lemma_13_8_exists_beta_prime_in_malpha_centralizer
    {M P : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hαβ : section10AlphaPrimes M = section10BetaPrimes M)
    (hCP_ne : subgroupCentralizerIn (section10Malpha M) P ≠ ⊥) :
    ∃ r : Nat.Primes,
      r ∈ section10BetaPrimes M ∧
        r ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Malpha M) P) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn (section10Malpha M) P
  have hC_card_ne_one : Nat.card C ≠ 1 := by
    intro hcard
    exact hCP_ne ((Subgroup.card_eq_one (H := C)).1 hcard)
  obtain ⟨r0, hr0prime, hr0C⟩ := Nat.exists_prime_and_dvd hC_card_ne_one
  let r : Nat.Primes := ⟨r0, hr0prime⟩
  have hrC : r.val ∣ Nat.card C := by
    simpa [r] using hr0C
  have hrα : r ∈ section10AlphaPrimes M :=
    ((theorem_10_2_a (G := G) hM).1).p_in_pi_of_p_dvd_card r
      (hrC.trans (Subgroup.card_dvd_of_le
        (inf_le_left : C ≤ section10Malpha M)))
  have hrβ : r ∈ section10BetaPrimes M := by
    simpa [← hαβ] using hrα
  exact ⟨r, hrβ, hrC⟩

private theorem CFSG.section13_lemma_13_8_centralizer_prime_order_ne_top
    {M P : Subgroup G} {p : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M) :
    Subgroup.centralizer (P : Set G) ≠ ⊤ := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨_hPM, hPcard⟩
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  intro hCtop
  have hP_center : P ≤ Subgroup.center G := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hyC : y ∈ Subgroup.centralizer (P : Set G) := by
      rw [hCtop]
      exact Subgroup.mem_top y
    exact ((Subgroup.mem_centralizer_iff.mp hyC) x hx).symm
  have hPbot : P ≤ ⊥ := by
    simpa [center_eq_bot_of_min_ce (G := G)] using hP_center
  exact hPne (le_bot_iff.mp hPbot)

private theorem CFSG.section13_lemma_13_8_exists_hall_in_centralizer_containing_piSubgroup
    {P K : Subgroup G} {π : Set Nat.Primes}
    (hCproper : Subgroup.centralizer (P : Set G) ≠ ⊤)
    (hK_C : K ≤ Subgroup.centralizer (P : Set G))
    (hKπ : IsPiSubgroup (G := G) π K) :
    ∃ H : Subgroup (Subgroup.centralizer (P : Set G)),
      IsHallSubgroup π H ∧ K.subgroupOf (Subgroup.centralizer (P : Set G)) ≤ H := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have hsolvC : Group.IsSolvable C :=
    IsMinCE.proper_subgroups_solvable C (lt_top_iff_ne_top.2 (by simpa [C] using hCproper))
  let _ : MulDistribMulAction PUnit.{1} C := {
    smul := fun _ x => x
    one_smul := by intro x; rfl
    mul_smul := by intro a b x; rfl
    smul_mul := by intro a x y; rfl
    smul_one := by intro a; rfl }
  have hcop : Nat.Coprime (Nat.card PUnit.{1}) (Nat.card C) := by simp
  have hKπC : IsPiSubgroup (G := C) π (K.subgroupOf C) :=
    section13_isPiSubgroup_subgroupOf (G := G) hKπ (by simpa [C] using hK_C)
  have hKinv : IsInvariant PUnit.{1} C (K.subgroupOf C) := by
    refine ⟨?_⟩
    intro a x
    cases a
    simp
  rcases exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := C) (A := PUnit.{1}) hsolvC hcop π (K.subgroupOf C) hKπC hKinv with
    ⟨H, hHHall, _hHinv, hKH⟩
  exact ⟨H, hHHall, hKH⟩

omit [IsMinCE G] in
private theorem CFSG.section13_exists_prime_order_subgroup_le_of_prime_dvd
    {A : Subgroup G} {r : Nat.Primes}
    (hrA : r ∈ subgroupPrimeSet A) :
    ∃ R : Subgroup G, R ≤ A ∧ Nat.card R = r.val := by
  classical
  let _ : Fact r.val.Prime := ⟨r.property⟩
  obtain ⟨a, ha_order⟩ := exists_prime_orderOf_dvd_card' (G := A) r.val hrA
  let R : Subgroup G := Subgroup.zpowers ((a : A) : G)
  have hR_le_A : R ≤ A := by
    exact Subgroup.zpowers_le.2 a.property
  have horderG : orderOf ((a : A) : G) = r.val := by
    simpa [Subgroup.orderOf_coe] using ha_order
  have hRcard : Nat.card R = r.val := by
      simp [R, Nat.card_zpowers, horderG]
  exact ⟨R, hR_le_A, hRcard⟩

private theorem CFSG.section13_lemma_13_8_hall_beta_transitivity_endpoint
    {M H Y : Subgroup G} {t : Nat.Primes} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (htβ : t ∈ section10BetaPrimes M)
    (hYne : Y ≠ ⊥)
    (hYt : IsPGroup t.val Y)
    (hYM : Y ≤ M)
    (hYH : Y ≤ H)
    (hH_le_Mg : H ≤ M.conjBy g) :
    H ≤ M := by
  classical
  have htσ : t ∈ section10SigmaPrimes M :=
    section13_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM htβ.1
  have hY_Mg : Y ≤ M.conjBy g := hYH.trans hH_le_Mg
  have htrans :
      ConjugationActionTransitiveOn (Subgroup.centralizer (Y : Set G))
        (section10ConjugatesContaining M Y) :=
    theorem_10_1_b (G := G) (M := M) (X := Y) (p := t)
      hM htσ hYne hYt hYM
  have hM_mem : M ∈ section10ConjugatesContaining M Y :=
    ⟨1, (section8_conjBy_one (G := G) M).symm, hYM⟩
  have hMg_mem : M.conjBy g ∈ section10ConjugatesContaining M Y :=
    ⟨g, rfl, hY_Mg⟩
  rcases htrans M hM_mem (M.conjBy g) hMg_mem with ⟨c, hc⟩
  have hYπβ : IsPiSubgroup (G := G) (section10BetaPrimes M) Y := by
    intro u hu
    have hu_single : u ∈ ({t} : Set Nat.Primes) :=
      section8_isPiSubgroup_singleton_of_isPGroup hYt u hu
    have hut : u = t := by simpa using hu_single
    simpa [hut] using htβ
  let S : Sylow t.val G := Classical.choice (Sylow.nonempty (p := t.val) (G := G))
  have hNY_le_M : Subgroup.normalizer (Y : Set G) ≤ M :=
    proposition_10_14_d (G := G) (p := t) htβ.2 S
      (M := M) (Y := Y) hM hYM hYne hYπβ
  have hcM : (c : G) ∈ M :=
    hNY_le_M ((centralizer_le_normalizer Y) c.property)
  have hMg_eq_M : M.conjBy g = M := by
    calc
      M.conjBy g = M.conjBy (c : G) := hc
      _ = M := section13_conjBy_eq_of_mem_normalizer (H := M)
        (Subgroup.le_normalizer hcM)
  rw [hMg_eq_M] at hH_le_Mg
  exact hH_le_Mg

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_normalizer_le_conjBy_of_conjBy_inv_le
    {M X : Subgroup G} {g : G}
    (hN : Subgroup.normalizer (X.conjBy g⁻¹ : Set G) ≤ M) :
    Subgroup.normalizer (X : Set G) ≤ M.conjBy g := by
  intro n hn
  have hn' : g⁻¹ * n * g ∈ Subgroup.normalizer (X.conjBy g⁻¹ : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hxX, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨n * x * n⁻¹, (hn x).1 hxX, ?_⟩
      simp [mul_assoc]
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hxX, hxz⟩
      refine Subgroup.mem_map.mpr ?_
      have hpre : n⁻¹ * x * n ∈ X := by
        exact (hn (n⁻¹ * x * n)).2 (by simpa [mul_assoc] using hxX)
      refine ⟨n⁻¹ * x * n, hpre, ?_⟩
      have hxz' : g⁻¹ * x * g = g⁻¹ * n * g * z * (g⁻¹ * n * g)⁻¹ := by
        simpa [MulAut.conj_apply] using hxz
      change g⁻¹ * (n⁻¹ * x * n) * (g⁻¹)⁻¹ = z
      calc
        g⁻¹ * (n⁻¹ * x * n) * (g⁻¹)⁻¹ =
            (g⁻¹ * n * g)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * n * g) := by
          group
        _ = (g⁻¹ * n * g)⁻¹ *
              (g⁻¹ * n * g * z * (g⁻¹ * n * g)⁻¹) * (g⁻¹ * n * g) := by
                rw [hxz']
        _ = z := by group
  have hconjM : g⁻¹ * n * g ∈ M := hN hn'
  refine Subgroup.mem_map.mpr ?_
  exact ⟨g⁻¹ * n * g, hconjM, by simp [mul_assoc]⟩

private theorem CFSG.section13_lemma_13_8_hall_beta_normalizer_conjugate_endpoint
    {M H X : Subgroup G} {s : Nat.Primes} {g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hsβ : s ∈ section10BetaPrimes M)
    (hXne : X ≠ ⊥)
    (hXs : IsPGroup s.val X)
    (hX_le_Mg : X ≤ M.conjBy g)
    (hH_le_normX : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ M.conjBy g := by
  classical
  let Xg : Subgroup G := X.conjBy g⁻¹
  have hXg_le_M : Xg ≤ M := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hxX, rfl⟩
    have hxMg : x ∈ M.conjBy g := hX_le_Mg hxX
    rcases Subgroup.mem_map.mp hxMg with ⟨m, hmM, hmx⟩
    have hx_eq : x = g * m * g⁻¹ := hmx.symm
    simpa [hx_eq, mul_assoc] using hmM
  have hXg_ne : Xg ≠ ⊥ := by
    intro hbot
    apply hXne
    ext x
    constructor
    · intro hx
      have hxg : g⁻¹ * x * g ∈ Xg := by
        refine Subgroup.mem_map.mpr ?_
        exact ⟨x, hx, by simp [mul_assoc]⟩
      have hxone : g⁻¹ * x * g = 1 := by
        have hxbot : g⁻¹ * x * g ∈ (⊥ : Subgroup G) := by simpa [hbot] using hxg
        simpa using hxbot
      have hx_eq_one : x = 1 := by
        calc
          x = g * (g⁻¹ * x * g) * g⁻¹ := by simp [mul_assoc]
          _ = 1 := by simp [hxone]
      simp [hx_eq_one]
    · intro hx
      have hxone : x = 1 := by simpa using hx
      simp [hxone]
  have hXg_s : IsPGroup s.val Xg := by
    change IsPGroup s.val (X.map ((MulAut.conj g⁻¹).toMonoidHom))
    exact IsPGroup.map (p := s.val) (H := X) hXs
      ((MulAut.conj g⁻¹).toMonoidHom)
  have hXgπβ : IsPiSubgroup (G := G) (section10BetaPrimes M) Xg := by
    intro u hu
    have hu_single : u ∈ ({s} : Set Nat.Primes) :=
      section8_isPiSubgroup_singleton_of_isPGroup hXg_s u hu
    have hus : u = s := by simpa using hu_single
    simpa [hus] using hsβ
  let S : Sylow s.val G := Classical.choice (Sylow.nonempty (p := s.val) (G := G))
  have hNXg_le_M : Subgroup.normalizer (Xg : Set G) ≤ M :=
    proposition_10_14_d (G := G) (p := s) hsβ.2 S
      (M := M) (Y := Xg) hM hXg_le_M hXg_ne hXgπβ
  have hNX_le_Mg : Subgroup.normalizer (X : Set G) ≤ M.conjBy g := by
    simpa [Xg] using
      section13_normalizer_le_conjBy_of_conjBy_inv_le
        (G := G) (M := M) (X := X) (g := g) hNXg_le_M
  exact hH_le_normX.trans hNX_le_Mg

omit [IsMinCE G] in
private theorem CFSG.section13_lemma_13_8_hall_beta_fitting_endpoint_of_pcore
    {M P : Subgroup G} {s : Nat.Primes} {g : G}
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hsβ : s ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥)
    (hCore_le_Mg :
      (pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype)).map
          (H.map (Subgroup.centralizer (P : Set G)).subtype).subtype ≤
        M.conjBy g) :
    ∃ s : Nat.Primes, ∃ X : Subgroup G, ∃ g : G,
      s ∈ section10BetaPrimes M ∧ X ≠ ⊥ ∧ IsPGroup s.val X ∧
        X ≤ M.conjBy g ∧
          H.map (Subgroup.centralizer (P : Set G)).subtype ≤
            Subgroup.normalizer (X : Set G) := by
  classical
  let Hamb : Subgroup G := H.map (Subgroup.centralizer (P : Set G)).subtype
  let X : Subgroup G := (pCore s.val Hamb).map Hamb.subtype
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hcore_bot : pCore s.val Hamb = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := pCore s.val Hamb) (f := Hamb.subtype)
        Hamb.subtype_injective).1 (by simpa [X, Hamb] using hXbot)
    exact hCore_ne hcore_bot
  have hXs : IsPGroup s.val X := by
    change IsPGroup s.val ((pCore s.val Hamb).map Hamb.subtype)
    exact IsPGroup.map (p := s.val) (H := pCore s.val Hamb)
      (pCore_isPGroup (G := Hamb) (p := s.val)) Hamb.subtype
  have hHamb_normX : Hamb ≤ Subgroup.normalizer (X : Set G) := by
    simpa [X, Hamb] using
      section13_map_subtype_le_normalizer_of_normal (G := G) Hamb (pCore s.val Hamb)
  exact ⟨s, X, g, hsβ, hXne, hXs, by simpa [X, Hamb] using hCore_le_Mg,
    by simpa [Hamb, X] using hHamb_normX⟩

private theorem CFSG.section13_lemma_13_8_hall_beta_fitting_pcore_conjugate_of_left_prime
    {M P : Subgroup G} {s : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hsβ : s ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    ∃ g : G,
      (pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype)).map
          (H.map (Subgroup.centralizer (P : Set G)).subtype).subtype ≤
        M.conjBy g := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let Hamb : Subgroup G := H.map C.subtype
  let X : Subgroup G := (pCore s.val Hamb).map Hamb.subtype
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hcore_bot : pCore s.val Hamb = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := pCore s.val Hamb) (f := Hamb.subtype)
        Hamb.subtype_injective).1 (by simpa [X, Hamb] using hXbot)
    exact hCore_ne (by simpa [Hamb, C] using hcore_bot)
  have hXs : IsPGroup s.val X := by
    change IsPGroup s.val ((pCore s.val Hamb).map Hamb.subtype)
    exact IsPGroup.map (p := s.val) (H := pCore s.val Hamb)
      (pCore_isPGroup (G := Hamb) (p := s.val)) Hamb.subtype
  have hsσ : s ∈ section10SigmaPrimes M :=
    section13_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hsβ.1
  rcases section10_exists_conjBy_le_of_isPGroup_of_sigma
      (G := G) (M := M) (Y := X) (p := s) hsσ hXs with
    ⟨g, hX_le_Mg⟩
  exact ⟨g, by simpa [X, Hamb, C] using hX_le_Mg⟩

omit [IsMinCE G] in
private theorem CFSG.section13_pSubgroup_le_pCore_of_nilpotent_for_hall
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    [Group.IsNilpotent R] {B : Subgroup R} (hBp : IsPGroup p B) :
    B ≤ pCore p R := by
  obtain ⟨S, hB_le_S⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hBp
  have hS_normal : (S : Subgroup R).Normal :=
    Group.IsNilpotent.sylow_normal (p := p) inferInstance S
  exact hB_le_S.trans (le_sSup ⟨hS_normal, S.isPGroup'⟩)

omit [IsMinCE G] in
private theorem CFSG.section13_pCore_ne_bot_of_dvd_card_nilpotent_for_hall
    {R : Type*} [Group R] [Finite R] [Group.IsNilpotent R]
    {q : ℕ} [Fact q.Prime] (hq : q ∣ Nat.card R) :
    pCore q R ≠ ⊥ := by
  classical
  let S : Sylow q R := Classical.choice inferInstance
  have hS_le : (S : Subgroup R) ≤ pCore q R :=
    section13_pSubgroup_le_pCore_of_nilpotent_for_hall (p := q) (R := R) S.isPGroup'
  have hqS : q ∣ Nat.card (S : Subgroup R) :=
    Sylow.dvd_card_of_dvd_card S hq
  intro hbot
  have hSbot : (S : Subgroup R) = ⊥ :=
    le_bot_iff.mp (hS_le.trans (le_of_eq hbot))
  have hcardS : Nat.card (S : Subgroup R) = 1 := by
    simp [hSbot]
  rw [hcardS] at hqS
  exact (Fact.out : Nat.Prime q).not_dvd_one hqS

omit [IsMinCE G] in
private theorem CFSG.section13_pCore_ne_bot_of_dvd_fitting_for_hall
    {R : Type*} [Group R] [Finite R] {q : Nat.Primes}
    (hq : q.val ∣ Nat.card (fittingSubgroup R)) :
    pCore q.val R ≠ ⊥ := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let F : Subgroup R := fittingSubgroup R
  have hFcore_ne : pCore q.val F ≠ ⊥ :=
    section13_pCore_ne_bot_of_dvd_card_nilpotent_for_hall
      (R := F) (q := q.val) (by simpa [F] using hq)
  let X : Subgroup R := (pCore q.val F).map F.subtype
  have hX_ne : X ≠ ⊥ := by
    intro hXbot
    have hcore_bot : pCore q.val F = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := pCore q.val F) (f := F.subtype)
        F.subtype_injective).1 (by simpa [X] using hXbot)
    exact hFcore_ne hcore_bot
  have hX_normal : X.Normal := by
    let _ : F.Normal := by infer_instance
    let _ : (pCore q.val F).Characteristic :=
      pCore_characteristic (G := F) (p := q.val)
    simpa [X] using (inferInstance : ((pCore q.val F).map F.subtype).Normal)
  have hX_p : IsPGroup q.val X := by
    change IsPGroup q.val ((pCore q.val F).map F.subtype)
    exact IsPGroup.map (p := q.val) (H := pCore q.val F)
      (pCore_isPGroup (G := F) (p := q.val)) F.subtype
  have hX_le_core : X ≤ pCore q.val R :=
    le_sSup ⟨hX_normal, hX_p⟩
  intro hcore_bot
  exact hX_ne (le_bot_iff.mp (hX_le_core.trans (le_of_eq hcore_bot)))

private theorem CFSG.section13_pCore_prime_dvd_card_of_ne_bot_for_hall
    {R : Type*} [Group R] [Finite R] {q : Nat.Primes}
    (hcore : pCore q.val R ≠ ⊥) :
    q.val ∣ Nat.card R := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  have hcore_nontrivial : Nontrivial (pCore q.val R) :=
    (Subgroup.nontrivial_iff_ne_bot (pCore q.val R)).2 hcore
  rcases (IsPGroup.nontrivial_iff_card
      (p := q.val) (G := pCore q.val R)
      (hG := pCore_isPGroup (G := R) (p := q.val))).1 hcore_nontrivial with
    ⟨n, hn, hcard⟩
  have hdiv_core : q.val ∣ Nat.card (pCore q.val R) := by
    rw [hcard]
    exact dvd_pow_self q.val (Nat.ne_of_gt hn)
  exact hdiv_core.trans (Subgroup.card_subgroup_dvd_card (pCore q.val R))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_pCore_ne_bot_of_mulEquiv_for_hall
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    {q : Nat.Primes} (e : A ≃* B) (hcore : pCore q.val A ≠ ⊥) :
    pCore q.val B ≠ ⊥ := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let X : Subgroup B := (pCore q.val A).map e.toMonoidHom
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hcore_bot : pCore q.val A = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := pCore q.val A) (f := e.toMonoidHom)
        e.injective).1 (by simpa [X] using hXbot)
    exact hcore hcore_bot
  have hXnormal : X.Normal := by
    simpa [X] using
      Subgroup.Normal.map (H := pCore q.val A) inferInstance
        e.toMonoidHom e.surjective
  have hXp : IsPGroup q.val X := by
    change IsPGroup q.val ((pCore q.val A).map e.toMonoidHom)
    exact IsPGroup.map (p := q.val) (H := pCore q.val A)
      (pCore_isPGroup (G := A) (p := q.val)) e.toMonoidHom
  have hX_le_core : X ≤ pCore q.val B :=
    le_sSup ⟨hXnormal, hXp⟩
  intro hbot
  exact hXne (le_bot_iff.mp (hX_le_core.trans (le_of_eq hbot)))

private theorem CFSG.section13_lemma_13_8_hall_beta_pcore_ne_bot_transfer
    {P : Subgroup G} {π : Set Nat.Primes}
    {H₁ H₂ : Subgroup (Subgroup.centralizer (P : Set G))} {s : Nat.Primes}
    (hCproper : Subgroup.centralizer (P : Set G) ≠ ⊤)
    (hHall₁ : IsHallSubgroup π H₁) (hHall₂ : IsHallSubgroup π H₂)
    (hCore_ne :
      pCore s.val (H₁.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    pCore s.val (H₂.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥ := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have hsolvC : Group.IsSolvable C :=
    IsMinCE.proper_subgroups_solvable C (lt_top_iff_ne_top.2 (by simpa [C] using hCproper))
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := C) hsolvC hHall₁ hHall₂ with
    ⟨c, hH₂eq⟩
  let Hamb₁ : Subgroup G := H₁.map C.subtype
  let Hamb₂ : Subgroup G := H₂.map C.subtype
  let H₁c : Subgroup C := H₁.map (MulAut.conj c).toMonoidHom
  let e₁ : H₁ ≃* Hamb₁ :=
    Subgroup.equivMapOfInjective (H := H₁) (f := C.subtype) C.subtype_injective
  let e₂ : H₁ ≃* H₁c :=
    Subgroup.equivMapOfInjective (H := H₁)
      (f := (MulAut.conj c).toMonoidHom) (EquivLike.injective (MulAut.conj c))
  let e₃ : H₁c ≃* H₂ := MulEquiv.subgroupCongr (by simpa [H₁c] using hH₂eq.symm)
  let e₄ : H₂ ≃* Hamb₂ :=
    Subgroup.equivMapOfInjective (H := H₂) (f := C.subtype) C.subtype_injective
  let e : Hamb₁ ≃* Hamb₂ := e₁.symm.trans (e₂.trans (e₃.trans e₄))
  exact
    section13_pCore_ne_bot_of_mulEquiv_for_hall
      (q := s) e (by simpa [Hamb₁, C] using hCore_ne)

private theorem CFSG.section13_lemma_13_8_hall_beta_fitting_union_side_choice
    {M Mstar P Y : Subgroup G} {p t : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hMstar : Mstar ∈ section9MaximalSubgroups G)
    (_hnotconj : section12NotConjugate Mstar M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (_hαβ : section10AlphaPrimes M = section10BetaPrimes M)
    (_hαβstar : section10AlphaPrimes Mstar = section10BetaPrimes Mstar)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hHHall :
      IsHallSubgroup (section10BetaPrimes M ∪ section10BetaPrimes Mstar) H)
    (_htβ : t ∈ section10BetaPrimes M)
    (hYne : Y ≠ ⊥)
    (_hYt : IsPGroup t.val Y)
    (hY_le_H : Y ≤ H.map (Subgroup.centralizer (P : Set G)).subtype) :
    ∃ s : Nat.Primes,
      (s ∈ section10BetaPrimes M ∨ s ∈ section10BetaPrimes Mstar) ∧
        pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥ := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let Hamb : Subgroup G := H.map C.subtype
  have hHamb_ne : Hamb ≠ ⊥ := by
    intro hHamb_bot
    have hY_bot : Y ≤ ⊥ := by
      intro y hy
      exact (show y ∈ (⊥ : Subgroup G) from by
        simpa [Hamb, C, hHamb_bot] using hY_le_H hy)
    exact hYne (le_bot_iff.mp hY_bot)
  have hHamb_le_C : Hamb ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hCproper : C ≠ ⊤ := by
    simpa [C] using
      section13_lemma_13_8_centralizer_prime_order_ne_top
        (G := G) (M := M ⊓ Mstar) (P := P) (p := p) hP
  have hHamb_proper : Hamb ≠ ⊤ := by
    intro htop
    have hCtop : C = ⊤ := by
      apply eq_top_iff.mpr
      intro x _hx
      exact hHamb_le_C (by simp [htop] : x ∈ Hamb)
    exact hCproper hCtop
  have hsolvHamb : Group.IsSolvable Hamb :=
    IsMinCE.proper_subgroups_solvable Hamb (lt_top_iff_ne_top.2 hHamb_proper)
  let _ : Group.IsSolvable Hamb := hsolvHamb
  have hF_ne : fittingSubgroup Hamb ≠ ⊥ := by
    intro hFbot
    have hcard : Nat.card Hamb = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable Hamb).mp hFbot
    exact hHamb_ne ((Subgroup.card_eq_one (H := Hamb)).1 hcard)
  have hF_card_ne_one : Nat.card (fittingSubgroup Hamb) ≠ 1 := by
    intro hcard
    exact hF_ne ((Subgroup.card_eq_one (H := fittingSubgroup Hamb)).1 hcard)
  obtain ⟨s0, hs0prime, hs0dvd⟩ := Nat.exists_prime_and_dvd hF_card_ne_one
  let s : Nat.Primes := ⟨s0, hs0prime⟩
  have hCore_ne : pCore s.val Hamb ≠ ⊥ :=
    section13_pCore_ne_bot_of_dvd_fitting_for_hall
      (R := Hamb) (q := s) (by simpa [s] using hs0dvd)
  have hsHamb : s.val ∣ Nat.card Hamb :=
    section13_pCore_prime_dvd_card_of_ne_bot_for_hall
      (R := Hamb) (q := s) hCore_ne
  have hHamb_card : Nat.card Hamb = Nat.card H := by
    simpa [Hamb, C] using
      (Subgroup.card_map_of_injective (K := H) (f := C.subtype)
        C.subtype_injective)
  have hsH : s.val ∣ Nat.card H := by
    simpa [hHamb_card] using hsHamb
  have hsπ :
      s ∈ section10BetaPrimes M ∪ section10BetaPrimes Mstar :=
    hHHall.p_in_pi_of_p_dvd_card s hsH
  exact ⟨s, by simpa using hsπ, by simpa [Hamb, C] using hCore_ne⟩

private theorem CFSG.section13_lemma_13_8_hall_beta_union_centralizer_fitting_pcore_conjugate
    {M Mstar P Y : Subgroup G} {p t s : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hMstar : Mstar ∈ section9MaximalSubgroups G)
    (_hnotconj : section12NotConjugate Mstar M)
    (_hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (_hαβ : section10AlphaPrimes M = section10BetaPrimes M)
    (_hαβstar : section10AlphaPrimes Mstar = section10BetaPrimes Mstar)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (_hHHall :
      IsHallSubgroup (section10BetaPrimes M ∪ section10BetaPrimes Mstar) H)
    (_htβ : t ∈ section10BetaPrimes M)
    (_hYne : Y ≠ ⊥)
    (_hYt : IsPGroup t.val Y)
    (_hY_le_H : Y ≤ H.map (Subgroup.centralizer (P : Set G)).subtype)
    (hsβ : s ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    ∃ s : Nat.Primes, ∃ g : G,
      s ∈ section10BetaPrimes M ∧
        pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥ ∧
          (pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype)).map
              (H.map (Subgroup.centralizer (P : Set G)).subtype).subtype ≤
            M.conjBy g := by
  classical
  rcases section13_lemma_13_8_hall_beta_fitting_pcore_conjugate_of_left_prime
      (G := G) (M := M) (P := P) (s := s) hM H hsβ hCore_ne with
    ⟨g, hCore_le_Mg⟩
  exact ⟨s, g, hsβ, hCore_ne, hCore_le_Mg⟩

private theorem CFSG.section13_lemma_13_8_hall_beta_union_centralizer_fitting_endpoint
    {M Mstar P Y : Subgroup G} {p t s : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hαβ : section10AlphaPrimes M = section10BetaPrimes M)
    (hαβstar : section10AlphaPrimes Mstar = section10BetaPrimes Mstar)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hHHall :
      IsHallSubgroup (section10BetaPrimes M ∪ section10BetaPrimes Mstar) H)
    (htβ : t ∈ section10BetaPrimes M)
    (hYne : Y ≠ ⊥)
    (hYt : IsPGroup t.val Y)
    (hY_le_H : Y ≤ H.map (Subgroup.centralizer (P : Set G)).subtype)
    (hsβ : s ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    ∃ s : Nat.Primes, ∃ X : Subgroup G, ∃ g : G,
      s ∈ section10BetaPrimes M ∧ X ≠ ⊥ ∧ IsPGroup s.val X ∧
        X ≤ M.conjBy g ∧
          H.map (Subgroup.centralizer (P : Set G)).subtype ≤
            Subgroup.normalizer (X : Set G) := by
  classical
  rcases section13_lemma_13_8_hall_beta_union_centralizer_fitting_pcore_conjugate
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Y := Y)
      (p := p) (t := t) (s := s) hM hMstar hnotconj hP hαβ hαβstar H hHHall
      htβ hYne hYt hY_le_H hsβ hCore_ne with
    ⟨s, g, hsβ, hCore_ne, hCore_le_Mg⟩
  exact
    section13_lemma_13_8_hall_beta_fitting_endpoint_of_pcore
      (G := G) (M := M) (P := P) (s := s) (g := g) H hsβ hCore_ne
      hCore_le_Mg

private theorem CFSG.section13_lemma_13_8_hall_beta_union_centralizer_le_conjugate_core
    {M Mstar P Y : Subgroup G} {p t s : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hαβ : section10AlphaPrimes M = section10BetaPrimes M)
    (hαβstar : section10AlphaPrimes Mstar = section10BetaPrimes Mstar)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hHHall :
      IsHallSubgroup (section10BetaPrimes M ∪ section10BetaPrimes Mstar) H)
    (htβ : t ∈ section10BetaPrimes M)
    (hYne : Y ≠ ⊥)
    (hYt : IsPGroup t.val Y)
    (hY_le_H : Y ≤ H.map (Subgroup.centralizer (P : Set G)).subtype)
    (hsβ : s ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    ∃ g : G, H.map (Subgroup.centralizer (P : Set G)).subtype ≤ M.conjBy g := by
  classical
  rcases section13_lemma_13_8_hall_beta_union_centralizer_fitting_endpoint
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Y := Y)
      (p := p) (t := t) (s := s) hM hMstar hnotconj hP hαβ hαβstar H hHHall
      htβ hYne hYt hY_le_H hsβ hCore_ne with
    ⟨s, X, g, hsβ, hXne, hXs, hX_le_Mg, hH_le_normX⟩
  exact ⟨g,
    section13_lemma_13_8_hall_beta_normalizer_conjugate_endpoint
      (G := G) (M := M) (H := H.map (Subgroup.centralizer (P : Set G)).subtype)
      (X := X) (s := s) (g := g) hM hsβ hXne hXs hX_le_Mg
      hH_le_normX⟩

private theorem CFSG.section13_lemma_13_8_hall_beta_union_centralizer_le_M_core
    {M Mstar P : Subgroup G} {p s : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hαβ : section10AlphaPrimes M = section10BetaPrimes M)
    (hαβstar : section10AlphaPrimes Mstar = section10BetaPrimes Mstar)
    (hCPα_ne : subgroupCentralizerIn (section10Malpha M) P ≠ ⊥)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hHHall :
      IsHallSubgroup (section10BetaPrimes M ∪ section10BetaPrimes Mstar) H)
    (hCstar_le_H :
      (subgroupCentralizerIn (section10Malpha M) P).subgroupOf
          (Subgroup.centralizer (P : Set G)) ≤ H)
    (hsβ : s ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore s.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    H.map (Subgroup.centralizer (P : Set G)).subtype ≤ M := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let Cα : Subgroup G := subgroupCentralizerIn (section10Malpha M) P
  rcases section13_lemma_13_8_exists_beta_prime_in_malpha_centralizer
      (G := G) (M := M) (P := P) hM hαβ hCPα_ne with
    ⟨t, htβ, htCα⟩
  rcases section13_exists_prime_order_subgroup_le_of_prime_dvd
      (G := G) (A := Cα) (r := t) htCα with
    ⟨Y, hY_le_Cα, hYcard⟩
  have hYne : Y ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hYcard
  have hYt : IsPGroup t.val Y := by
    refine IsPGroup.of_card (p := t.val) (G := Y) (n := 1) ?_
    simpa [pow_one] using hYcard
  have hYM : Y ≤ M := by
    intro y hy
    exact section13_malpha_le_maximal (G := G) M (hY_le_Cα hy).1
  let Hamb : Subgroup G := H.map C.subtype
  have hYH : Y ≤ Hamb := by
    intro y hy
    have hyCα : y ∈ Cα := hY_le_Cα hy
    have hyC : y ∈ C := hyCα.2
    have hySub : (⟨y, hyC⟩ : C) ∈ Cα.subgroupOf C := hyCα
    refine Subgroup.mem_map.mpr ?_
    exact ⟨⟨y, hyC⟩, hCstar_le_H (by simpa [Cα, C] using hySub), rfl⟩
  rcases section13_lemma_13_8_hall_beta_union_centralizer_le_conjugate_core
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Y := Y)
      (p := p) (t := t) (s := s) hM hMstar hnotconj hP hαβ hαβstar H hHHall
      htβ hYne hYt (by simpa [Hamb, C] using hYH) hsβ hCore_ne with
    ⟨g, hHamb_le_Mg⟩
  exact
    section13_lemma_13_8_hall_beta_transitivity_endpoint
      (G := G) (M := M) (H := Hamb) (Y := Y) (t := t) (g := g)
      hM htβ hYne hYt hYM hYH (by simpa [Hamb, C] using hHamb_le_Mg)

private theorem CFSG.section13_lemma_13_8_source_hall_beta_prime_in_centralizer
    {M Mstar P Q Qstar : Subgroup G} {p q qstar sleft : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (_hpM : p ∈ section12Tau1Primes M)
    (_hpMstar : p ∈ section12Tau1Primes Mstar)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (_hQ_M : section12SylowSubgroupIn q Q M)
    (_hQ_le_M : Q ≤ M)
    (_hQ_le_Mstar : Q ≤ Mstar)
    (_hQq : IsPGroup q.val Q)
    (_hQne : Q ≠ ⊥)
    (_hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (_hCQ : subgroupCentralizerIn Q P = ⊥)
    (_hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (_hQ_derived_Mstar : Q ≤ ambientDerivedSubgroup Mstar)
    (h12M :
      section10AlphaPrimes M = section10BetaPrimes M ∧
        section10Malpha M ≠ ⊥ ∧ q ∉ section10AlphaPrimes M ∧
          subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥)
    (h12Mstar :
      section10AlphaPrimes Mstar = section10BetaPrimes Mstar ∧
        section10Malpha Mstar ≠ ⊥ ∧ qstar ∉ section10AlphaPrimes Mstar ∧
          subgroupCentralizerIn (section10Malpha Mstar) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha Mstar) (P ⊔ Qstar) = ⊥)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hHHall :
      IsHallSubgroup (section10BetaPrimes M ∪ section10BetaPrimes Mstar) H)
    (hCα_le_H :
      (subgroupCentralizerIn (section10Malpha M) P).subgroupOf
          (Subgroup.centralizer (P : Set G)) ≤ H)
    (hsleftβ : sleft ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore sleft.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    ∃ r : Nat.Primes,
      r ∈ section10BetaPrimes Mstar ∧
        r ∈ subgroupPrimeSet (subgroupCentralizerIn M P) := by
  classical
  rcases section13_lemma_13_8_exists_beta_prime_in_malpha_centralizer
      (G := G) (M := M) (P := P) hM h12M.1 h12M.2.2.2.1 with
    ⟨t, htβ, htCα⟩
  have hCα_le_CM :
      subgroupCentralizerIn (section10Malpha M) P ≤ subgroupCentralizerIn M P := by
    intro x hx
    exact ⟨section13_malpha_le_maximal (G := G) M hx.1, hx.2⟩
  have htCM : t ∈ subgroupPrimeSet (subgroupCentralizerIn M P) :=
    htCα.trans (Subgroup.card_dvd_of_le hCα_le_CM)
  rcases section13_lemma_13_8_exists_beta_prime_in_malpha_centralizer
      (G := G) (M := Mstar) (P := P) hMstar h12Mstar.1 h12Mstar.2.2.2.1 with
    ⟨s, hsβstar, hsCαstar⟩
  let πβ : Set Nat.Primes := section10BetaPrimes M ∪ section10BetaPrimes Mstar
  let Cα : Subgroup G := subgroupCentralizerIn (section10Malpha M) P
  have hH_le_M :
      H.map (Subgroup.centralizer (P : Set G)).subtype ≤ M :=
    section13_lemma_13_8_hall_beta_union_centralizer_le_M_core
      (G := G) (M := M) (Mstar := Mstar) (P := P) (p := p)
      (s := sleft)
      hM hMstar hnotconj hP h12M.1 h12Mstar.1 h12M.2.2.2.1 H
      (by simpa [πβ] using hHHall)
      (by simpa [Cα] using hCα_le_H) hsleftβ hCore_ne
  have hsπβ : s ∈ πβ := by
    exact Or.inr hsβstar
  have hsC :
      s.val ∣ Nat.card (Subgroup.centralizer (P : Set G)) :=
    hsCαstar.trans (Subgroup.card_dvd_of_le
      (inf_le_right :
        subgroupCentralizerIn (section10Malpha Mstar) P ≤
          Subgroup.centralizer (P : Set G)))
  have hsHcard : s.val ∣ Nat.card H := by
    have hs_prod : s.val ∣ H.index * Nat.card H := by
      have hcardC :
          H.index * Nat.card H = Nat.card (Subgroup.centralizer (P : Set G)) :=
        Subgroup.index_mul_card (H := H)
      simpa [hcardC] using hsC
    rcases s.2.dvd_mul.mp hs_prod with hs_idx | hs_card
    · exact False.elim ((hHHall.p_in_pi_of_p_dvd_index s hs_idx) hsπβ)
    · exact hs_card
  let Camb : Subgroup G := H.map (Subgroup.centralizer (P : Set G)).subtype
  have hCamb_card : Nat.card Camb = Nat.card H := by
    simpa [Camb] using
      (Subgroup.card_map_of_injective (K := H)
        (f := (Subgroup.centralizer (P : Set G)).subtype)
        (Subgroup.centralizer (P : Set G)).subtype_injective)
  have hsCamb : s ∈ subgroupPrimeSet Camb := by
    rw [subgroupPrimeSet, hCamb_card]
    exact hsHcard
  have hCamb_le_CMP : Camb ≤ subgroupCentralizerIn M P := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (P : Set G) := by
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    exact ⟨hH_le_M (by simpa [Camb] using hx), hxC⟩
  exact ⟨s, hsβstar, hsCamb.trans (Subgroup.card_dvd_of_le hCamb_le_CMP)⟩

private theorem CFSG.section13_not_alpha_of_not_sigma
    {M : Subgroup G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hr_notσ : r ∉ section10SigmaPrimes M) :
    r ∉ section10AlphaPrimes M := by
  intro hrα
  exact hr_notσ (section13_sigmaPrimes_mem_of_alphaPrimes_mem (G := G) hM hrα)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_le_subgroupNormalizerIn_of_le_normalizer
    {A M Q : Subgroup G}
    (hAM : A ≤ M) (hAnormQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    A ≤ subgroupNormalizerIn M (Q : Set G) := by
  intro x hx
  exact mem_subgroupNormalizerIn.mpr ⟨hAnormQ hx, hAM hx⟩

private theorem CFSG.section13_prime_order_disjoint_malpha_of_not_sigma
    {M R : Subgroup G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hr_notσ : r ∉ section10SigmaPrimes M)
    (hRcard : Nat.card R = r.val) :
    Disjoint R (section10Malpha M) := by
  classical
  have hr_notα : r ∉ section10AlphaPrimes M :=
    section13_not_alpha_of_not_sigma (G := G) hM hr_notσ
  have hRr : IsPGroup r.val R := by
    refine IsPGroup.of_card (p := r.val) (G := R) (n := 1) ?_
    simpa [pow_one] using hRcard
  have hRπc : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ R :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem (G := G) hr_notα hRr
  have hMαπ : IsPiSubgroup (G := G) (section10AlphaPrimes M) (section10Malpha M) := by
    intro s hs
    exact ((theorem_10_2_a (G := G) hM).1).p_in_pi_of_p_dvd_card s hs
  have hinf_bot : R ⊓ section10Malpha M = ⊥ :=
    section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
      (π := section10AlphaPrimes M) (H := R ⊓ section10Malpha M)
      (Y := R) (C := section10Malpha M)
      inf_le_left inf_le_right hRπc hMαπ
  rw [Subgroup.disjoint_def]
  intro x hxR hxα
  have hxinf : x ∈ R ⊓ section10Malpha M := ⟨hxR, hxα⟩
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hinf_bot] using hxinf
  simpa using hxbot

omit [IsMinCE G] in
private theorem CFSG.section13_fixedPointSubgroup_quotient_eq_map_of_solvable_kernel_coprime
    {L A : Type*} [Group L] [Finite L] [Group A] [Finite A]
    [MulDistribMulAction A L]
    (K : Subgroup L) [K.Normal] (hKinv : IsInvariant A L K)
    (hKsolv : Group.IsSolvable K)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K)) :
    letI : MulDistribMulAction A (L ⧸ K) :=
      quotientMulDistribMulAction (A := A) (G := L) K hKinv
    fixedPointSubgroup A (L ⧸ K) =
      (fixedPointSubgroup A L).map (QuotientGroup.mk' K) := by
  classical
  let _ : IsInvariant A L K := hKinv
  let _ : MulAction.QuotientAction A K :=
    quotientAction_of_isInvariant (A := A) (G := L) K hKinv
  let _ : MulDistribMulAction A (L ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := L) K hKinv
  refine le_antisymm ?_ ?_
  · intro q
    refine QuotientGroup.induction_on q ?_
    intro g hq
    have hqfix : ∀ a : A, a • ((g : L) : L ⧸ K) = ((g : L) : L ⧸ K) := by
      simpa [fixedPointSubgroup] using hq
    let c : A → K := fun a =>
      ⟨g⁻¹ * (a • g), by
        have hqeq : (QuotientGroup.mk' K) (a • g) = (QuotientGroup.mk' K) g := by
          simpa using hqfix a
        have hdiv_mem : (a • g) / g ∈ K := (QuotientGroup.eq_iff_div_mem).1 hqeq
        have hmul_mem : (a • g) * g⁻¹ ∈ K := by
          simpa [div_eq_mul_inv] using hdiv_mem
        have hconj_mem : g⁻¹ * ((a • g) * g⁻¹) * (g⁻¹)⁻¹ ∈ K :=
          (inferInstance : K.Normal).conj_mem _ hmul_mem g⁻¹
        simpa [mul_assoc] using hconj_mem⟩
    have hcocycle : ∀ a b : A, c (a * b) = c a * (a • c b) := by
      intro a b
      ext
      change g⁻¹ * ((a * b) • g) =
        (g⁻¹ * (a • g)) * (a • (g⁻¹ * (b • g)))
      simp [mul_assoc, smul_mul', smul_smul]
    rcases exists_principal_cocycle_of_solvable_coprime
        (A := A) hKsolv hcop c hcocycle with
      ⟨n, hn⟩
    let x : L := g * (n : L)
    have hxfix : ∀ a : A, a • x = x := by
      intro a
      have hcn : (g⁻¹ * (a • g) : L) = (((n * (a • n)⁻¹ : K) : K) : L) := by
        exact congrArg Subtype.val (by simpa [c] using hn a)
      calc
        a • x = (a • g) * (a • (n : L)) := by
          simp [x, smul_mul']
        _ = g * (g⁻¹ * (a • g)) * (a • (n : L)) := by
          simp
        _ = g * ((((n * (a • n)⁻¹ : K) : K) : L) * (a • (n : L))) := by
          rw [hcn]
          simp [mul_assoc]
        _ = g * (n : L) := by
          have hsmul_coe : a • (n : L) = ((a • n : K) : L) := rfl
          rw [hsmul_coe]
          simp [mul_assoc]
        _ = x := by
          simp [x]
    refine ⟨x, ?_, ?_⟩
    · simpa [fixedPointSubgroup] using hxfix
    · simp [x]
  · exact fixedPointSubgroup_map_mk'_le_fixedPointSubgroup_quotient
      (A := A) (G := L) K hKinv

private theorem CFSG.section13_lemma_13_8_fixed_point_prime_order_lift_to_normalizer_Q_divisor
    {M P Q R₀ : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hP_M : P ≤ M)
    (hP_NQ : P ≤ subgroupNormalizerIn M (Q : Set G))
    (hP_norm_malpha : P ≤ Subgroup.normalizer (section10Malpha M : Set G))
    (_hPp : IsPGroup p.val P)
    (hPαc : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ P)
    (hM_eq_malpha_sup_NQ :
      section10Malpha M ⊔ subgroupNormalizerIn M (Q : Set G) = M)
    (_hr_notα : r ∉ section10AlphaPrimes M)
    (hR₀_CMP : R₀ ≤ subgroupCentralizerIn M P)
    (_hR₀r : IsPGroup r.val R₀)
    (_hR₀αc : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ R₀)
    (hR₀_disj_malpha : Disjoint R₀ (section10Malpha M))
    (hR₀card : Nat.card R₀ = r.val) :
    r ∈ subgroupPrimeSet
      (subgroupCentralizerIn (subgroupNormalizerIn M (Q : Set G)) P) := by
    classical
    -- Repaired replacement for docs/section13.tex:L347-L348:
    -- prove the fixed `r`-divisor survives in `N_M(Q)` through the
    -- `P`-stable normal Hall kernel `M_α`.
    let U : Subgroup G := subgroupNormalizerIn M (Q : Set G)
    let K : Subgroup G := section10Malpha M
    let KU : Subgroup G := K ⊓ U
    have hU_le_M : U ≤ M := by
      intro x hx
      exact (mem_subgroupNormalizerIn.mp hx).2
    have hP_norm_U : P ≤ Subgroup.normalizer (U : Set G) :=
      hP_NQ.trans Subgroup.le_normalizer
    have hP_norm_K : P ≤ Subgroup.normalizer (K : Set G) := by
      simpa [K] using hP_norm_malpha
    have hU_norm_K : U ≤ Subgroup.normalizer (K : Set G) := by
      exact hU_le_M.trans (by simpa [K] using section13_le_normalizer_malpha (G := G))
    have hU_norm_U : U ≤ Subgroup.normalizer (U : Set G) :=
      Subgroup.le_normalizer
    have hU_norm_KU : U ≤ Subgroup.normalizer (KU : Set G) := by
      simpa [KU] using
        section13_le_normalizer_inf (G := G) (A := U) (H := K) (K := U)
          hU_norm_K hU_norm_U
    have hP_norm_KU : P ≤ Subgroup.normalizer (KU : Set G) := by
      simpa [KU, K, U] using
        section13_le_normalizer_inf (G := G) (A := P)
          (H := section10Malpha M) (K := subgroupNormalizerIn M (Q : Set G))
          hP_norm_malpha hP_norm_U
    let _ : Subgroup.Normalizes P U := ⟨hP_norm_U⟩
    let KUsub : Subgroup U := K.subgroupOf U
    let _ : KUsub.Normal := by
      dsimp [KUsub]
      exact Subgroup.normal_subgroupOf_of_le_normalizer (N := K) hU_norm_K
    have hKUinv : IsInvariant (↥P) (↥U) KUsub := by
      refine ⟨?_⟩
      intro a x
      change ((x : U) : G) ∈ K ↔
        ((a : G) * ((x : U) : G) * (a : G)⁻¹) ∈ K
      exact Subgroup.mem_normalizer_iff.mp (hP_norm_K a.property) ((x : U) : G)
    have hUne : U ≠ ⊤ := by
      intro hUtop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        intro x hx
        exact hU_le_M (by simp [hUtop])
      exact hM.1 (top_le_iff.mp htop_le_M)
    let _ : Group.IsSolvable U :=
      IsMinCE.proper_subgroups_solvable U (lt_top_iff_ne_top.2 hUne)
    have hKUsolv : Group.IsSolvable KUsub := by infer_instance
    have hKπ : IsPiSubgroup (G := G) (section10AlphaPrimes M) K := by
      intro s hs
      exact ((theorem_10_2_a (G := G) hM).1).p_in_pi_of_p_dvd_card s
        (by simpa [K] using hs)
    have hKUπ : IsPiSubgroup (G := G) (section10AlphaPrimes M) KU :=
      IsPiSubgroup.of_le inf_le_left hKπ
    have hdisj : Disjoint (section10AlphaPrimes M)ᶜ (section10AlphaPrimes M) := by
      rw [Set.disjoint_left]
      intro s hscomp hs
      exact hscomp hs
    have hcopKU : Nat.Coprime (Nat.card P) (Nat.card KU) :=
      section13_coprime_card_of_isPiSubgroup_disjoint_primes
        (G := G) hPαc hKUπ hdisj
    have hKUsub_card : Nat.card KUsub = Nat.card KU := by
      have hmap : KUsub.map U.subtype = KU := by
        change (K.subgroupOf U).map U.subtype = K ⊓ U
        exact Subgroup.subgroupOf_map_subtype K U
      have hcard_map : Nat.card (KUsub.map U.subtype) = Nat.card KUsub := by
        simpa using
          (Subgroup.card_map_of_injective (K := KUsub) (f := U.subtype)
            U.subtype_injective)
      simpa [hmap] using hcard_map.symm
    have hcop : Nat.Coprime (Nat.card P) (Nat.card KUsub) := by
      simpa [hKUsub_card] using hcopKU
    let _ : IsInvariant (↥P) (↥U) KUsub := hKUinv
    let _ : MulAction.QuotientAction (↥P) KUsub :=
      quotientAction_of_isInvariant (A := ↥P) (G := ↥U) KUsub hKUinv
    let _ : MulDistribMulAction (↥P) (↥U ⧸ KUsub) :=
      quotientMulDistribMulAction (A := ↥P) (G := ↥U) KUsub hKUinv
    have hfixed_eq :
        fixedPointSubgroup (↥P) (↥U ⧸ KUsub) =
          (fixedPointSubgroup (↥P) ↥U).map (QuotientGroup.mk' KUsub) :=
      section13_fixedPointSubgroup_quotient_eq_map_of_solvable_kernel_coprime
        (K := KUsub) hKUinv hKUsolv hcop
    let S : Subgroup G := U ⊔ K
    have hP_norm_S : P ≤ Subgroup.normalizer (S : Set G) := by
      have hforward :
          ∀ g ∈ P, ∀ x, x ∈ U ⊔ K → g * x * g⁻¹ ∈ U ⊔ K := by
        intro g hg x hx
        rw [Subgroup.sup_eq_closure] at hx ⊢
        refine
          Subgroup.closure_induction (p := fun y _hy =>
            g * y * g⁻¹ ∈ Subgroup.closure ((U : Set G) ∪ (K : Set G)))
            ?_ ?_ ?_ ?_ hx
        · intro y hy
          rcases hy with hyU | hyK
          · exact Subgroup.subset_closure
              (Or.inl ((Subgroup.mem_normalizer_iff.mp (hP_norm_U hg) y).1 hyU))
          · exact Subgroup.subset_closure
              (Or.inr ((Subgroup.mem_normalizer_iff.mp (hP_norm_K hg) y).1 hyK))
        · simp
        · intro y z _hy _hz hy hz
          simpa [mul_assoc] using
            (Subgroup.closure ((U : Set G) ∪ (K : Set G))).mul_mem hy hz
        · intro y _hy hy
          simpa [mul_assoc] using
            (Subgroup.closure ((U : Set G) ∪ (K : Set G))).inv_mem hy
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        simpa [S] using hforward g hg x (by simpa [S] using hx)
      · intro hx
        have hx' := hforward g⁻¹ (P.inv_mem hg) (g * x * g⁻¹) (by simpa [S] using hx)
        simpa [S, mul_assoc] using hx'
    let _ : Subgroup.Normalizes P S := ⟨hP_norm_S⟩
    let KsubS : Subgroup S := K.subgroupOf S
    let _ : KsubS.Normal := by
      dsimp [KsubS, S]
      exact Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := U) (N := K) hU_norm_K
    have hKsubS_inv : IsInvariant (↥P) (↥S) KsubS := by
      simpa [KsubS] using
        section13_isInvariant_subgroupOf_of_le_normalizer
          (G := G) (A := P) (H := S) (K := K)
          hP_norm_S hP_norm_K le_sup_right
    let _ : IsInvariant (↥P) (↥S) KsubS := hKsubS_inv
    let _ : MulAction.QuotientAction (↥P) KsubS :=
      quotientAction_of_isInvariant (A := ↥P) (G := ↥S) KsubS hKsubS_inv
    let _ : MulDistribMulAction (↥P) (↥S ⧸ KsubS) :=
      quotientMulDistribMulAction (A := ↥P) (G := ↥S) KsubS hKsubS_inv
    let e : ↥U ⧸ KUsub ≃* ↥S ⧸ KsubS := by
      simpa [KUsub, KU, KsubS, S] using
        QuotientGroup.quotientInfEquivProdNormalizerQuotient U K hU_norm_K
    have hequiv : ∀ (a : P) (x : ↥U ⧸ KUsub), e (a • x) = a • e x := by
      intro a x
      refine QuotientGroup.induction_on x ?_
      intro u
      rfl
    have hS_eq_M : S = M := by
      simpa [S, U, K, sup_comm] using hM_eq_malpha_sup_NQ
    have hR₀_le_S : R₀ ≤ S := by
      intro x hx
      have hxM : x ∈ M := (hR₀_CMP hx).1
      simpa [hS_eq_M] using hxM
    let R₀S : Subgroup S := R₀.subgroupOf S
    let qS : S →* S ⧸ KsubS := QuotientGroup.mk' KsubS
    let RbarS : Subgroup (S ⧸ KsubS) := R₀S.map qS
    have hqS_inj : Function.Injective (fun x : R₀S => qS (x : S)) := by
      rintro ⟨aS, haR₀S⟩ ⟨bS, hbR₀S⟩ hab
      change qS aS = qS bS at hab
      have hdivKsub : aS⁻¹ * bS ∈ KsubS := QuotientGroup.eq.mp hab
      have hdivK : ((aS : G)⁻¹ * (bS : G)) ∈ K := by
        simpa [KsubS, Subgroup.mem_subgroupOf] using hdivKsub
      have haR : (aS : G) ∈ R₀ := by
        simpa [R₀S, Subgroup.mem_subgroupOf] using haR₀S
      have hbR : (bS : G) ∈ R₀ := by
        simpa [R₀S, Subgroup.mem_subgroupOf] using hbR₀S
      have hdivR : (aS : G)⁻¹ * (bS : G) ∈ R₀ :=
        R₀.mul_mem (R₀.inv_mem haR) hbR
      have hdiv_one : (aS : G)⁻¹ * (bS : G) = 1 := by
        have hbot : (aS : G)⁻¹ * (bS : G) ∈ (⊥ : Subgroup G) :=
          (Subgroup.disjoint_def.mp hR₀_disj_malpha) hdivR (by simpa [K] using hdivK)
        simpa using hbot
      have hb_eq_a : (bS : G) = (aS : G) := by
        have hmul := congrArg (fun y : G => (aS : G) * y) hdiv_one
        simpa [mul_assoc] using hmul
      apply Subtype.ext
      apply Subtype.ext
      exact hb_eq_a.symm
    have hRbarS_card : Nat.card RbarS = r.val := by
      let f : R₀S → RbarS := fun x =>
        ⟨qS x, by
          refine ⟨x, x.property, rfl⟩⟩
      have hf_inj : Function.Injective f := by
        intro a b hab
        exact hqS_inj (by simpa [f] using congrArg Subtype.val hab)
      have hf_surj : Function.Surjective f := by
        rintro ⟨z, hz⟩
        rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      have hmap_card : Nat.card RbarS = Nat.card R₀S :=
        (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
      have hR₀S_card : Nat.card R₀S = Nat.card R₀ := by
        simpa [R₀S] using natCard_subgroupOf_eq R₀ S hR₀_le_S
      simpa [hR₀card] using hmap_card.trans hR₀S_card
    have hRbarS_fixed : RbarS ≤ fixedPointSubgroup (↥P) (↥S ⧸ KsubS) := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hxR, rfl⟩
      change ∀ a : P, a • qS x = qS x
      intro a
      have hxR₀ : ((x : S) : G) ∈ R₀ := by
        simpa [R₀S, Subgroup.mem_subgroupOf] using hxR
      have hxC : ((x : S) : G) ∈ Subgroup.centralizer (P : Set G) :=
        (hR₀_CMP hxR₀).2
      have hcomm : (a : G) * ((x : S) : G) = ((x : S) : G) * (a : G) :=
        Subgroup.mem_centralizer_iff.mp hxC (a : G) a.property
      have hconj : (a : G) * ((x : S) : G) * (a : G)⁻¹ = ((x : S) : G) := by
        calc
          (a : G) * ((x : S) : G) * (a : G)⁻¹ =
              (((x : S) : G) * (a : G)) * (a : G)⁻¹ := by rw [hcomm]
          _ = ((x : S) : G) := by simp [mul_assoc]
      have hconjS : a • x = x := by
        apply Subtype.ext
        exact hconj
      change qS (a • x) = qS x
      rw [hconjS]
    let RbarU : Subgroup (↥U ⧸ KUsub) := RbarS.map e.symm.toMonoidHom
    have hRbarU_card : Nat.card RbarU = r.val := by
      have hmap_card : Nat.card RbarU = Nat.card RbarS := by
        simpa [RbarU] using
          (Subgroup.card_map_of_injective (K := RbarS) (f := e.symm.toMonoidHom)
            e.symm.injective)
      simpa [hRbarS_card] using hmap_card
    have hRbarU_fixed : RbarU ≤ fixedPointSubgroup (↥P) (↥U ⧸ KUsub) := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨y, hyR, rfl⟩
      change ∀ a : P, a • e.symm y = e.symm y
      intro a
      apply e.injective
      calc
        e (a • e.symm y) = a • e (e.symm y) := hequiv a (e.symm y)
        _ = a • y := by simp
        _ = y := (hRbarS_fixed hyR) a
        _ = e (e.symm y) := by simp
    have hr_fixed_quot :
        r.val ∣ Nat.card (fixedPointSubgroup (↥P) (↥U ⧸ KUsub)) := by
      rw [← hRbarU_card]
      exact Subgroup.card_dvd_of_le hRbarU_fixed
    have hr_fixed_U_map :
        r.val ∣
          Nat.card ((fixedPointSubgroup (↥P) ↥U).map (QuotientGroup.mk' KUsub)) := by
      simpa [hfixed_eq] using hr_fixed_quot
    have hr_fixed_U : r.val ∣ Nat.card (fixedPointSubgroup (↥P) ↥U) :=
      dvd_trans hr_fixed_U_map
        (Subgroup.card_map_dvd (H := fixedPointSubgroup (↥P) ↥U)
          (QuotientGroup.mk' KUsub))
    have hfixed_U_eq :
        fixedPointSubgroup (↥P) ↥U =
          (subgroupCentralizerIn U P).subgroupOf U := by
      simpa [U] using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn U P hP_norm_U
    have hfixed_U_card :
        Nat.card (fixedPointSubgroup (↥P) ↥U) =
          Nat.card (subgroupCentralizerIn U P) := by
      rw [hfixed_U_eq]
      exact natCard_subgroupOf_eq (subgroupCentralizerIn U P) U inf_le_left
    rw [subgroupPrimeSet]
    change r.val ∣ Nat.card (subgroupCentralizerIn U P)
    rw [← hfixed_U_card]
    exact hr_fixed_U

private theorem CFSG.section13_lemma_13_8_fixed_point_prime_order_lift_to_normalizer_Q_core
    {M P Q R₀ : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP_M : P ≤ M)
    (hP_NQ : P ≤ subgroupNormalizerIn M (Q : Set G))
    (hP_norm_malpha : P ≤ Subgroup.normalizer (section10Malpha M : Set G))
    (hPp : IsPGroup p.val P)
    (hPαc : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ P)
    (hM_eq_malpha_sup_NQ :
      section10Malpha M ⊔ subgroupNormalizerIn M (Q : Set G) = M)
    (hr_notα : r ∉ section10AlphaPrimes M)
    (hR₀_CMP : R₀ ≤ subgroupCentralizerIn M P)
    (hR₀r : IsPGroup r.val R₀)
    (hR₀αc : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ R₀)
    (hR₀_disj_malpha : Disjoint R₀ (section10Malpha M))
    (hR₀card : Nat.card R₀ = r.val) :
    ∃ R : Subgroup G,
      R ≤ M ∧ R ≤ subgroupNormalizerIn M (Q : Set G) ∧
        R ≤ Subgroup.centralizer (P : Set G) ∧ Nat.card R = r.val := by
  classical
  have hrU :
      r ∈ subgroupPrimeSet
        (subgroupCentralizerIn (subgroupNormalizerIn M (Q : Set G)) P) :=
    section13_lemma_13_8_fixed_point_prime_order_lift_to_normalizer_Q_divisor
      (G := G) (M := M) (P := P) (Q := Q) (R₀ := R₀) (p := p) (r := r)
      hM hP_M hP_NQ hP_norm_malpha hPp hPαc hM_eq_malpha_sup_NQ
      hr_notα hR₀_CMP hR₀r hR₀αc hR₀_disj_malpha hR₀card
  rcases section13_exists_prime_order_subgroup_le_of_prime_dvd
      (G := G) (A := subgroupCentralizerIn (subgroupNormalizerIn M (Q : Set G)) P)
      (r := r) hrU with
    ⟨R, hR_le_UC, hRcard⟩
  refine ⟨R, ?_, ?_, ?_, hRcard⟩
  · intro x hx
    exact (mem_subgroupNormalizerIn.mp (hR_le_UC hx).1).2
  · intro x hx
    exact (hR_le_UC hx).1
  · intro x hx
    exact (hR_le_UC hx).2

private theorem CFSG.section13_lemma_13_8_fixed_point_prime_order_lift_to_normalizer_Q
    {M Mstar P Q R₀ : Subgroup G} {p q r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpM : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (_hQ_M : section12SylowSubgroupIn q Q M)
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hM_eq_malpha_sup_NQ :
      section10Malpha M ⊔ subgroupNormalizerIn M (Q : Set G) = M)
    (hr_notσ : r ∉ section10SigmaPrimes M)
    (hR₀_M : R₀ ≤ M)
    (hR₀_centP : R₀ ≤ Subgroup.centralizer (P : Set G))
    (hR₀card : Nat.card R₀ = r.val) :
    ∃ R : Subgroup G,
      R ≤ M ∧ R ≤ subgroupNormalizerIn M (Q : Set G) ∧
        R ≤ Subgroup.centralizer (P : Set G) ∧ Nat.card R = r.val := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPinf, hPcard⟩
  have hP_M : P ≤ M := by
    exact hPinf.1
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hp_notσ : p ∉ section10SigmaPrimes M := by
    rcases (by simpa [section12Tau1Primes] using hpM) with
      ⟨hpσ, _hpD, _hrank⟩
    exact hpσ
  have hp_notα : p ∉ section10AlphaPrimes M :=
    section13_not_alpha_of_not_sigma (G := G) hM hp_notσ
  have hPαc : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ P :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem (G := G) hp_notα hPp
  have hP_NQ : P ≤ subgroupNormalizerIn M (Q : Set G) :=
    section13_le_subgroupNormalizerIn_of_le_normalizer (G := G) hP_M hPinvQ
  have hP_norm_malpha : P ≤ Subgroup.normalizer (section10Malpha M : Set G) :=
    hP_M.trans (section13_le_normalizer_malpha (G := G))
  have hr_notα : r ∉ section10AlphaPrimes M :=
    section13_not_alpha_of_not_sigma (G := G) hM hr_notσ
  have hR₀_CMP : R₀ ≤ subgroupCentralizerIn M P := by
    intro x hx
    exact ⟨hR₀_M hx, hR₀_centP hx⟩
  have hR₀r : IsPGroup r.val R₀ := by
    refine IsPGroup.of_card (p := r.val) (G := R₀) (n := 1) ?_
    simpa [pow_one] using hR₀card
  have hR₀αc : IsPiSubgroup (G := G) (section10AlphaPrimes M)ᶜ R₀ :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem (G := G) hr_notα hR₀r
  have hR₀_disj_malpha : Disjoint R₀ (section10Malpha M) :=
    section13_prime_order_disjoint_malpha_of_not_sigma
      (G := G) (M := M) (R := R₀) (r := r) hM hr_notσ hR₀card
  exact
    section13_lemma_13_8_fixed_point_prime_order_lift_to_normalizer_Q_core
      (G := G) (M := M) (P := P) (Q := Q) (R₀ := R₀) (p := p) (r := r)
      hM hP_M hP_NQ hP_norm_malpha hPp hPαc hM_eq_malpha_sup_NQ
      hr_notα hR₀_CMP hR₀r hR₀αc hR₀_disj_malpha hR₀card

private theorem CFSG.section13_lemma_13_8_fixed_point_lift_to_normalizer_Q
    {M Mstar P Q : Subgroup G} {p q r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpM : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hQ_M : section12SylowSubgroupIn q Q M)
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hM_eq_malpha_sup_NQ :
      section10Malpha M ⊔ subgroupNormalizerIn M (Q : Set G) = M)
    (hr_notσ : r ∉ section10SigmaPrimes M)
    (hrCM : r ∈ subgroupPrimeSet (subgroupCentralizerIn M P)) :
    ∃ R : Subgroup G,
      R ≤ M ∧ R ≤ subgroupNormalizerIn M (Q : Set G) ∧
        R ≤ Subgroup.centralizer (P : Set G) ∧ Nat.card R = r.val := by
  classical
  rcases section13_exists_prime_order_subgroup_le_of_prime_dvd
      (G := G) (A := subgroupCentralizerIn M P) (r := r) hrCM with
    ⟨R₀, hR₀_le_CMP, hR₀card⟩
  have hR₀_M : R₀ ≤ M := by
    intro x hx
    exact (hR₀_le_CMP hx).1
  have hR₀_centP : R₀ ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    exact (hR₀_le_CMP hx).2
  exact section13_lemma_13_8_fixed_point_prime_order_lift_to_normalizer_Q
    (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q) (R₀ := R₀)
    (p := p) (q := q) (r := r) hM hpM hP hQ_M hPinvQ
    hM_eq_malpha_sup_NQ hr_notσ hR₀_M hR₀_centP hR₀card

private theorem CFSG.section13_lemma_13_8_exists_beta_R_in_M_normalizer_centralizer
    {M Mstar P Q Qstar : Subgroup G} {p q qstar sleft : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hpM : p ∈ section12Tau1Primes M)
    (hpMstar : p ∈ section12Tau1Primes Mstar)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hQ_M : section12SylowSubgroupIn q Q M)
    (hQ_le_M : Q ≤ M)
    (hQ_le_Mstar : Q ≤ Mstar)
    (hQq : IsPGroup q.val Q)
    (hQne : Q ≠ ⊥)
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hQ_derived_Mstar : Q ≤ ambientDerivedSubgroup Mstar)
    (hM_eq_malpha_sup_NQ :
      section10Malpha M ⊔ subgroupNormalizerIn M (Q : Set G) = M)
    (h12M :
      section10AlphaPrimes M = section10BetaPrimes M ∧
        section10Malpha M ≠ ⊥ ∧ q ∉ section10AlphaPrimes M ∧
          subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥)
    (h12Mstar :
      section10AlphaPrimes Mstar = section10BetaPrimes Mstar ∧
        section10Malpha Mstar ≠ ⊥ ∧ qstar ∉ section10AlphaPrimes Mstar ∧
          subgroupCentralizerIn (section10Malpha Mstar) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha Mstar) (P ⊔ Qstar) = ⊥)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hHHall :
      IsHallSubgroup (section10BetaPrimes M ∪ section10BetaPrimes Mstar) H)
    (hCα_le_H :
      (subgroupCentralizerIn (section10Malpha M) P).subgroupOf
          (Subgroup.centralizer (P : Set G)) ≤ H)
    (hsleftβ : sleft ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore sleft.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    ∃ r : Nat.Primes, ∃ R : Subgroup G,
      r ∈ section10BetaPrimes Mstar ∧ R ≤ M ∧
        R ≤ subgroupNormalizerIn M (Q : Set G) ∧
          R ≤ Subgroup.centralizer (P : Set G) ∧ Nat.card R = r.val := by
  classical
  rcases section13_lemma_13_8_source_hall_beta_prime_in_centralizer
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q)
      (Qstar := Qstar) (p := p) (q := q) (qstar := qstar) (sleft := sleft)
      hM hMstar hnotconj hpM hpMstar hP hQ_M hQ_le_M hQ_le_Mstar
      hQq hQne hPinvQ hCQ hNQ hQ_derived_Mstar h12M h12Mstar
      H hHHall hCα_le_H hsleftβ hCore_ne with
    ⟨r, hrβstar, hrCM⟩
  have hr_notσ : r ∉ section10SigmaPrimes M := by
    have hdis : Disjoint (section10AlphaPrimes Mstar) (section10SigmaPrimes M) :=
      (lemma_10_12_a (G := G) (M := Mstar) (H := M) hMstar hM
        (section13_notConjugate_symm (G := G) hnotconj)).2
    rw [Set.disjoint_left] at hdis
    exact hdis hrβstar.1
  rcases section13_lemma_13_8_fixed_point_lift_to_normalizer_Q
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q)
      (p := p) (q := q) (r := r)
      hM hpM hP hQ_M hPinvQ hM_eq_malpha_sup_NQ hr_notσ hrCM with
    ⟨R, hR_M, hR_normQ, hR_centP, hRcard⟩
  exact ⟨r, R, hrβstar, hR_M, hR_normQ, hR_centP, hRcard⟩

private theorem CFSG.section13_lemma_13_8_exists_theorem_13_4_bridge
    {M Mstar P Q Qstar : Subgroup G} {p q qstar sleft : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hpM : p ∈ section12Tau1Primes M)
    (hpMstar : p ∈ section12Tau1Primes Mstar)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hQ_M : section12SylowSubgroupIn q Q M)
    (hQ_le_M : Q ≤ M)
    (hQ_le_Mstar : Q ≤ Mstar)
    (hQq : IsPGroup q.val Q)
    (hQne : Q ≠ ⊥)
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hQ_derived_Mstar : Q ≤ ambientDerivedSubgroup Mstar)
    (hM_eq_malpha_sup_NQ :
      section10Malpha M ⊔ subgroupNormalizerIn M (Q : Set G) = M)
    (h12M :
      section10AlphaPrimes M = section10BetaPrimes M ∧
        section10Malpha M ≠ ⊥ ∧ q ∉ section10AlphaPrimes M ∧
          subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥)
    (h12Mstar :
      section10AlphaPrimes Mstar = section10BetaPrimes Mstar ∧
        section10Malpha Mstar ≠ ⊥ ∧ qstar ∉ section10AlphaPrimes Mstar ∧
          subgroupCentralizerIn (section10Malpha Mstar) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha Mstar) (P ⊔ Qstar) = ⊥)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hHHall :
      IsHallSubgroup (section10BetaPrimes M ∪ section10BetaPrimes Mstar) H)
    (hCα_le_H :
      (subgroupCentralizerIn (section10Malpha M) P).subgroupOf
          (Subgroup.centralizer (P : Set G)) ≤ H)
    (hsleftβ : sleft ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore sleft.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    ∃ r : Nat.Primes, ∃ R E E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ ∧
        P ∈ section10PrimeOrderSubgroupsIn p E ∧
          r ∈ subgroupPrimeSet E ∧
            R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P) ∧
              Subgroup.normalizer (R : Set G) ≤ Mstar := by
  classical
  -- Hall-beta route from the book proof: find a beta-prime subgroup
  -- `R ≤ N_M(Q)` centralized by `P`, then use Theorem 13.4.
  rcases section13_lemma_13_8_exists_beta_R_in_M_normalizer_centralizer
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q)
      (Qstar := Qstar) (p := p) (q := q) (qstar := qstar) (sleft := sleft)
      hM hMstar hnotconj hpM hpMstar hP hQ_M hQ_le_M hQ_le_Mstar
      hQq hQne hPinvQ hCQ hNQ hQ_derived_Mstar hM_eq_malpha_sup_NQ
      h12M h12Mstar H hHHall hCα_le_H hsleftβ hCore_ne with
    ⟨r, R, hrβstar, hR_M, hR_normQ, hR_centP, hRcard⟩
  exact section13_lemma_13_8_bridge_of_beta_R_in_M_normalizer
    (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q) (R := R)
    (p := p) (r := r) hM hMstar hnotconj hpM hP hNQ hR_M
    hR_normQ hR_centP hRcard hrβstar

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_isPiSubgroup_map
    {R S : Type*} [Group R] [Group S] {π : Set Nat.Primes} {H : Subgroup R}
    (hH : IsPiSubgroup (G := R) π H) (f : R →* S) :
    IsPiSubgroup (G := S) π (H.map f) := by
  intro p hp
  exact hH p (hp.trans (Subgroup.card_map_dvd (H := H) f))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_pSubgroup_le_pCore_of_nilpotent
    {R : Type*} [Group R] [Finite R] [Group.IsNilpotent R]
    {p : ℕ} [Fact p.Prime] {B : Subgroup R} (hBp : IsPGroup p B) :
    B ≤ pCore p R := by
  obtain ⟨S, hB_le_S⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hBp
  have hS_normal : (S : Subgroup R).Normal :=
    Group.IsNilpotent.sylow_normal (p := p) inferInstance S
  exact hB_le_S.trans (le_sSup ⟨hS_normal, S.isPGroup'⟩)

private theorem CFSG.section13_lemma_13_8_commutator_malpha_inf_le_mstar_malpha
    {M Mstar Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hQ_le_M : Q ≤ M)
    (hQ_le_Mstar : Q ≤ Mstar)
    (hQq : IsPGroup q.val Q)
    (hQ_derived_Mstar : Q ≤ ambientDerivedSubgroup Mstar)
    (hq_notα : q ∉ section10AlphaPrimes M) :
    ⁅section10Malpha M ⊓ Mstar, Q⁆ ≤ section10Malpha Mstar := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let K : Subgroup G := section10Malpha M ⊓ Mstar
  let C : Subgroup G := ⁅K, Q⁆
  let α : Subgroup Mstar := section10MalphaSubgroup Mstar
  let D : Subgroup Mstar := derivedSubgroup Mstar
  rcases (theorem_10_2_d (G := G) hMstar).2 with ⟨hαD, hαDnorm, hDquot_nil⟩
  let _ : (α.subgroupOf D).Normal := by
    simpa [α, D] using hαDnorm
  let _ : α.Normal := by
    dsimp [α]
    infer_instance
  let qMstar : Mstar →* Mstar ⧸ α := QuotientGroup.mk' α
  let Dbar : Subgroup (Mstar ⧸ α) := D.map qMstar
  have hDbar_norm : Dbar.Normal := by
    dsimp [Dbar]
    exact Subgroup.Normal.map (H := D) inferInstance qMstar
      (QuotientGroup.mk'_surjective α)
  let _ : Dbar.Normal := hDbar_norm
  have hDbar_nil : Group.IsNilpotent Dbar := by
    let e : D ⧸ α.subgroupOf D ≃* Dbar := quotientSubgroupRangeEquiv D α
    exact Group.nilpotent_of_mulEquiv (G := D ⧸ α.subgroupOf D) (G' := Dbar) e
  let QbarM : Subgroup (Mstar ⧸ α) := (Q.subgroupOf Mstar).map qMstar
  have hQsub_p : IsPGroup q.val (Q.subgroupOf Mstar) := by
    exact hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQ_le_Mstar).symm
  have hQbar_p : IsPGroup q.val QbarM := by
    change IsPGroup q.val ((Q.subgroupOf Mstar).map qMstar)
    exact IsPGroup.map (p := q.val) (H := Q.subgroupOf Mstar) hQsub_p qMstar
  have hQsub_le_D : Q.subgroupOf Mstar ≤ D := by
    intro x hx
    have hxDg : ((x : Mstar) : G) ∈ ambientDerivedSubgroup Mstar :=
      hQ_derived_Mstar (by
        exact hx)
    change ((x : Mstar) : G) ∈ ambientDerivedSubgroup Mstar at hxDg
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxDg
    rcases hxDg with ⟨y, hyD, hyx⟩
    have hy_eq : y = x := Subtype.ext hyx
    change y ∈ D at hyD
    rw [hy_eq] at hyD
    exact hyD
  have hQbar_le_Dbar : QbarM ≤ Dbar := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxQ, rfl⟩
    exact Subgroup.mem_map.mpr ⟨x, hQsub_le_D hxQ, rfl⟩
  let QbarD : Subgroup Dbar := QbarM.subgroupOf Dbar
  have hQbarD_p : IsPGroup q.val QbarD := by
    let e : QbarD ≃* QbarM := Subgroup.subgroupOfEquivOfLe hQbar_le_Dbar
    exact hQbar_p.of_equiv e.symm
  let PbarSub : Subgroup Dbar := pCore q.val Dbar
  have hPbarSub_char : PbarSub.Characteristic := by
    dsimp [PbarSub]
    exact pCore_characteristic (G := Dbar) (p := q.val)
  let _ : PbarSub.Characteristic := hPbarSub_char
  have hQbarD_le_pcore : QbarD ≤ PbarSub := by
    let _ : Group.IsNilpotent Dbar := hDbar_nil
    simpa [PbarSub] using
      section13_pSubgroup_le_pCore_of_nilpotent
        (R := Dbar) (p := q.val) (B := QbarD) hQbarD_p
  let Pbar : Subgroup (Mstar ⧸ α) := PbarSub.map Dbar.subtype
  have hPbar_norm : Pbar.Normal := by
    dsimp [Pbar]
    infer_instance
  let Nsub : Subgroup Mstar := Pbar.comap qMstar
  have hNsub_norm : Nsub.Normal := by
    dsimp [Nsub]
    exact hPbar_norm.comap qMstar
  let N : Subgroup G := Nsub.map Mstar.subtype
  have hNle : N ≤ Mstar := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hNsub_eq : N.subgroupOf Mstar = Nsub := by
    simpa [N] using subgroupOf_map_subtype_eq (K := Mstar) Nsub
  have hNnorm : (N.subgroupOf Mstar).Normal := by
    rw [hNsub_eq]
    exact hNsub_norm
  have hQ_le_N : Q ≤ N := by
    intro x hxQ
    refine Subgroup.mem_map.mpr ?_
    refine ⟨⟨x, hQ_le_Mstar hxQ⟩, ?_, rfl⟩
    change qMstar ⟨x, hQ_le_Mstar hxQ⟩ ∈ Pbar
    have hxQbar : qMstar ⟨x, hQ_le_Mstar hxQ⟩ ∈ QbarM := by
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hQ_le_Mstar hxQ⟩,
          by simpa [Subgroup.mem_subgroupOf] using hxQ, rfl⟩
    have hxDbar : qMstar ⟨x, hQ_le_Mstar hxQ⟩ ∈ Dbar :=
      hQbar_le_Dbar hxQbar
    have hxQbarD :
        (⟨qMstar ⟨x, hQ_le_Mstar hxQ⟩, hxDbar⟩ : Dbar) ∈ QbarD := by
      simpa [QbarD, Subgroup.mem_subgroupOf] using hxQbar
    have hxpcore : (⟨qMstar ⟨x, hQ_le_Mstar hxQ⟩, hxDbar⟩ : Dbar) ∈ PbarSub :=
      hQbarD_le_pcore hxQbarD
    exact Subgroup.mem_map.mpr
      ⟨⟨qMstar ⟨x, hQ_le_Mstar hxQ⟩, hxDbar⟩, hxpcore, rfl⟩
  have hKleMstar : K ≤ Mstar := inf_le_right
  have hKq' : IsPiSubgroup (G := G) (section10PPrimeSet q) K := by
    intro r hrK
    have hrα : r ∈ section10AlphaPrimes M := by
      exact (theorem_10_2_a (G := G) hM).1.p_in_pi_of_p_dvd_card r
        (hrK.trans (Subgroup.card_dvd_of_le (inf_le_left : K ≤ section10Malpha M)))
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hrq
    exact hq_notα (by simpa [hrq] using hrα)
  have hQ_norm_malpha : Q ≤ Subgroup.normalizer (section10Malpha M : Set G) :=
    hQ_le_M.trans (section13_le_normalizer_malpha (G := G))
  have hQ_norm_mstar : Q ≤ Subgroup.normalizer (Mstar : Set G) :=
    hQ_le_Mstar.trans Subgroup.le_normalizer
  have hQ_norm_K : Q ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K] using
      section13_le_normalizer_inf
        (G := G) (A := Q) (H := section10Malpha M) (K := Mstar)
        hQ_norm_malpha hQ_norm_mstar
  have hC_le_K : C ≤ K := by
    simpa [C, K] using section13_commutator_le_left_of_le_normalizer
      (G := G) (K := K) (P := Q) hQ_norm_K
  have hC_le_Mstar : C ≤ Mstar := hC_le_K.trans hKleMstar
  have hC_le_N : C ≤ N := by
    have hMstar_norm_N : Mstar ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mp hNnorm
    exact section13_commutator_le_right_of_le_normalizer
      (G := G) (K := K) (P := Q) (L := N)
      (hKleMstar.trans hMstar_norm_N) hQ_le_N
  let Cbar : Subgroup (Mstar ⧸ α) := (C.subgroupOf Mstar).map qMstar
  have hCq' : IsPiSubgroup (G := G) (section10PPrimeSet q) C :=
    IsPiSubgroup.of_le hC_le_K hKq'
  have hCsub_q' : IsPiSubgroup (G := Mstar) (section10PPrimeSet q) (C.subgroupOf Mstar) :=
    section13_isPiSubgroup_subgroupOf hCq' hC_le_Mstar
  have hCbar_q' : IsPiSubgroup (G := Mstar ⧸ α) (section10PPrimeSet q) Cbar := by
    simpa [Cbar] using section13_isPiSubgroup_map hCsub_q' qMstar
  have hPbar_q : IsPiSubgroup (G := Mstar ⧸ α) ({q} : Set Nat.Primes) Pbar := by
    have hPbar_p : IsPGroup q.val Pbar := by
      dsimp [Pbar, PbarSub]
      exact IsPGroup.map (pCore_isPGroup (G := Dbar) (p := q.val)) Dbar.subtype
    exact section8_isPiSubgroup_singleton_of_isPGroup hPbar_p
  have hCbar_le_Pbar : Cbar ≤ Pbar := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxC, rfl⟩
    have hxCG : ((x : Mstar) : G) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using hxC
    have hxN : ((x : Mstar) : G) ∈ N := hC_le_N hxCG
    rcases Subgroup.mem_map.mp hxN with ⟨z, hzN, hzx⟩
    have hz_eq : z = x := Mstar.subtype_injective hzx
    have hxNsub : x ∈ Nsub := by
      simpa [hz_eq] using hzN
    exact hxNsub
  have hCbar_q : IsPiSubgroup (G := Mstar ⧸ α) ({q} : Set Nat.Primes) Cbar :=
    IsPiSubgroup.of_le hCbar_le_Pbar hPbar_q
  have hCbar_bot : Cbar = ⊥ := by
    exact section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
      (π := ({q} : Set Nat.Primes)) (H := Cbar) (Y := Cbar) (C := Cbar)
      le_rfl le_rfl (by simpa [section10PPrimeSet] using hCbar_q') hCbar_q
  intro x hxC
  have hxMstar : x ∈ Mstar := hC_le_Mstar hxC
  let xMstar : Mstar := ⟨x, hxMstar⟩
  have hxCsub : xMstar ∈ C.subgroupOf Mstar := by
    simpa [xMstar, Subgroup.mem_subgroupOf] using hxC
  have hxmap : qMstar xMstar ∈ Cbar :=
    Subgroup.mem_map.mpr ⟨xMstar, hxCsub, rfl⟩
  have hxone : qMstar xMstar = 1 := by
    simpa [hCbar_bot] using hxmap
  have hxker : xMstar ∈ qMstar.ker := by
    simpa [MonoidHom.mem_ker] using hxone
  have hxα : xMstar ∈ α := by
    simpa [qMstar, QuotientGroup.ker_mk'] using hxker
  change x ∈ (section10MalphaSubgroup Mstar).map Mstar.subtype
  exact Subgroup.mem_map.mpr ⟨xMstar, by simpa [α] using hxα, rfl⟩

private theorem CFSG.section13_lemma_13_8_malpha_centralizer_le_centralizer_of_le_mstar
    {M Mstar P Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hQ_le_M : Q ≤ M)
    (hQ_le_Mstar : Q ≤ Mstar)
    (hQq : IsPGroup q.val Q)
    (hQ_derived_Mstar : Q ≤ ambientDerivedSubgroup Mstar)
    (hq_notα : q ∉ section10AlphaPrimes M)
    (hCP_le_Mstar : subgroupCentralizerIn (section10Malpha M) P ≤ Mstar) :
    subgroupCentralizerIn (section10Malpha M) P ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  let X : Subgroup G := subgroupCentralizerIn (section10Malpha M) P
  let K : Subgroup G := section10Malpha M ⊓ Mstar
  have hX_le_malpha : X ≤ section10Malpha M := fun x hx => hx.1
  have hX_le_K : X ≤ K := by
    intro x hx
    exact ⟨hx.1, hCP_le_Mstar hx⟩
  have hQ_norm_malpha : Q ≤ Subgroup.normalizer (section10Malpha M : Set G) :=
    hQ_le_M.trans (section13_le_normalizer_malpha (G := G))
  have hcomm_le_malpha : ⁅X, Q⁆ ≤ section10Malpha M := by
    exact (Subgroup.commutator_mono hX_le_malpha le_rfl).trans
      (section13_commutator_le_left_of_le_normalizer (G := G) hQ_norm_malpha)
  have hcomm_le_mstar_alpha : ⁅X, Q⁆ ≤ section10Malpha Mstar := by
    exact (Subgroup.commutator_mono hX_le_K le_rfl).trans
      (section13_lemma_13_8_commutator_malpha_inf_le_mstar_malpha
        (G := G) (M := M) (Mstar := Mstar) (Q := Q) (q := q)
        hM hMstar hQ_le_M hQ_le_Mstar hQq hQ_derived_Mstar hq_notα)
  have hdis :
      Disjoint (section10Malpha M) (section10Msigma Mstar) :=
    (lemma_10_12_a (G := G) (M := M) (H := Mstar) hM hMstar hnotconj).1
  have hMstar_alpha_le_sigma : section10Malpha Mstar ≤ section10Msigma Mstar :=
    section13_malpha_le_msigma (G := G) hMstar
  have hcomm_bot : ⁅X, Q⁆ = ⊥ :=
    le_bot_iff.mp (by
      rw [← hdis.eq_bot]
      intro x hx
      exact ⟨hcomm_le_malpha hx, hMstar_alpha_le_sigma (hcomm_le_mstar_alpha hx)⟩)
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := X) (H₂ := Q)).mp
    hcomm_bot

private theorem CFSG.section13_lemma_13_8_malpha_centralizer_le_centralizer
    {M Mstar P Q Qstar : Subgroup G} {p q qstar sleft : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hpM : p ∈ section12Tau1Primes M)
    (hpMstar : p ∈ section12Tau1Primes Mstar)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hQ_M : section12SylowSubgroupIn q Q M)
    (hQ_le_M : Q ≤ M)
    (hQ_le_Mstar : Q ≤ Mstar)
    (hQq : IsPGroup q.val Q)
    (hQne : Q ≠ ⊥)
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hQ_derived_Mstar : Q ≤ ambientDerivedSubgroup Mstar)
    (hM_eq_malpha_sup_NQ :
      section10Malpha M ⊔ subgroupNormalizerIn M (Q : Set G) = M)
    (h12M :
      section10AlphaPrimes M = section10BetaPrimes M ∧
        section10Malpha M ≠ ⊥ ∧ q ∉ section10AlphaPrimes M ∧
          subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥)
    (h12Mstar :
      section10AlphaPrimes Mstar = section10BetaPrimes Mstar ∧
        section10Malpha Mstar ≠ ⊥ ∧ qstar ∉ section10AlphaPrimes Mstar ∧
          subgroupCentralizerIn (section10Malpha Mstar) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha Mstar) (P ⊔ Qstar) = ⊥)
    (H : Subgroup (Subgroup.centralizer (P : Set G)))
    (hHHall :
      IsHallSubgroup (section10BetaPrimes M ∪ section10BetaPrimes Mstar) H)
    (hCα_le_H :
      (subgroupCentralizerIn (section10Malpha M) P).subgroupOf
          (Subgroup.centralizer (P : Set G)) ≤ H)
    (hsleftβ : sleft ∈ section10BetaPrimes M)
    (hCore_ne :
      pCore sleft.val (H.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥) :
    subgroupCentralizerIn (section10Malpha M) P ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  rcases section13_lemma_13_8_exists_theorem_13_4_bridge
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q)
      (Qstar := Qstar) (p := p) (q := q) (qstar := qstar) (sleft := sleft)
      hM hMstar hnotconj hpM hpMstar hP hQ_M hQ_le_M hQ_le_Mstar
      hQq hQne hPinvQ hCQ hNQ hQ_derived_Mstar hM_eq_malpha_sup_NQ
      h12M h12Mstar H hHHall hCα_le_H hsleftβ hCore_ne with
    ⟨r, R, E, E₁₂, E₁, E₂, E₃, hE, hP_E, hrE, hR_CEP, hNR_le_Mstar⟩
  have hCP_le_Mstar :
      subgroupCentralizerIn (section10Malpha M) P ≤ Mstar :=
    section13_lemma_13_8_malpha_centralizer_le_mstar_of_theorem_13_4_bridge
      (G := G) (M := M) (Mstar := Mstar) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (R := R)
      (p := p) (r := r) hM hE hpM hP_E hrE hR_CEP hNR_le_Mstar
  exact
    section13_lemma_13_8_malpha_centralizer_le_centralizer_of_le_mstar
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q) (q := q)
      hM hMstar hnotconj hQ_le_M hQ_le_Mstar hQq hQ_derived_Mstar
      h12M.2.2.1 hCP_le_Mstar

/-- Lemma 13.8: the listed two-maximal-subgroup configuration with
`P ∈ 𝓔_p^1(M ∩ M*)`, `P`-invariant Sylow subgroups `Q,Q*`,
trivial `P`-centralizers in both, and crossed normalizer containments is
impossible. -/
public theorem CFSG.lemma_13_8
    {M Mstar P Q Qstar : Subgroup G} {p q qstar : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hpM : p ∈ section12Tau1Primes M)
    (hpMstar : p ∈ section12Tau1Primes Mstar)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hQ : section12SylowSubgroupIn q Q (M ⊓ Mstar))
    (hQstar : section12SylowSubgroupIn qstar Qstar (M ⊓ Mstar))
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hPinvQstar : P ≤ Subgroup.normalizer (Qstar : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hCQstar : subgroupCentralizerIn Qstar P = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hNQstar : Subgroup.normalizer (Qstar : Set G) ≤ M) :
    False := by
  classical
  have h12M :
      section10AlphaPrimes M = section10BetaPrimes M ∧
        section10Malpha M ≠ ⊥ ∧ q ∉ section10AlphaPrimes M ∧
          subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥ :=
    section13_lemma_13_8_side_12_18
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q)
      (p := p) (q := q) hM hMstar hnotconj hpM hP hQ hPinvQ hCQ hNQ
  have hP_le_M : P ≤ M := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
      ⟨hPinf, _hPcard⟩
    exact hPinf.1
  have hP_le_Mstar : P ≤ Mstar := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
      ⟨hPinf, _hPcard⟩
    exact hPinf.2
  have hQ_M : section12SylowSubgroupIn q Q M :=
    section13_sylowSubgroupIn_of_inf_normalizer_le_right
      (G := G) (M := M) (Mstar := Mstar) hQ hNQ
  have hQ_le_M : Q ≤ M := section13_sylowSubgroupIn_le (G := G) hQ_M
  have hQ_le_Mstar : Q ≤ Mstar := by
    have hQ_inf : Q ≤ M ⊓ Mstar := section13_sylowSubgroupIn_le (G := G) hQ
    intro x hx
    exact (hQ_inf hx).2
  have hQq : IsPGroup q.val Q := section13_sylowSubgroupIn_isPGroup (G := G) hQ
  have hQne : Q ≠ ⊥ :=
    section13_ne_bot_of_normalizer_le_maximal (G := G) hMstar hNQ
  have hQ_derived_M : Q ≤ ambientDerivedSubgroup M :=
    section13_le_ambientDerived_of_fixedpoint_free_sylow
      (G := G) (M := M) (P := P) (Q := Q) (H := M ⊓ Mstar)
      (p := p) (q := q) hP hP_le_M hQ_le_M hQq hQne hPinvQ hCQ
  have hQ_derived_Mstar : Q ≤ ambientDerivedSubgroup Mstar :=
    section13_le_ambientDerived_of_fixedpoint_free_sylow
      (G := G) (M := Mstar) (P := P) (Q := Q) (H := M ⊓ Mstar)
      (p := p) (q := q) hP hP_le_Mstar hQ_le_Mstar hQq hQne hPinvQ hCQ
  have hM_eq_malpha_sup_NQ :
      section10Malpha M ⊔ subgroupNormalizerIn M (Q : Set G) = M :=
    section13_malpha_sup_subgroupNormalizerIn_of_derived_sylow
      (G := G) (M := M) (Q := Q) (q := q) hM hQ_M hQ_derived_M
  have hnotconj_symm : section12NotConjugate M Mstar :=
    section13_notConjugate_symm (G := G) hnotconj
  have hP_swap : P ∈ section10PrimeOrderSubgroupsIn p (Mstar ⊓ M) := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
      ⟨hPinf, hPcard⟩
    simpa [section10PrimeOrderSubgroupsIn] using ⟨⟨hPinf.2, hPinf.1⟩, hPcard⟩
  have hQstar_swap : section12SylowSubgroupIn qstar Qstar (Mstar ⊓ M) :=
    section13_sylowSubgroupIn_inf_comm (G := G) (M := M) (N := Mstar) hQstar
  have h12Mstar :
      section10AlphaPrimes Mstar = section10BetaPrimes Mstar ∧
        section10Malpha Mstar ≠ ⊥ ∧ qstar ∉ section10AlphaPrimes Mstar ∧
          subgroupCentralizerIn (section10Malpha Mstar) P ≠ ⊥ ∧
            subgroupCentralizerIn (section10Malpha Mstar) (P ⊔ Qstar) = ⊥ :=
    section13_lemma_13_8_side_12_18
      (G := G) (M := Mstar) (Mstar := M) (P := P) (Q := Qstar)
      (p := p) (q := qstar) hMstar hM hnotconj_symm hpMstar hP_swap
      hQstar_swap hPinvQstar hCQstar hNQstar
  have hQstar_Mstar : section12SylowSubgroupIn qstar Qstar Mstar :=
    section13_sylowSubgroupIn_of_inf_normalizer_le_right
      (G := G) (M := Mstar) (Mstar := M) hQstar_swap hNQstar
  have hQstar_le_Mstar : Qstar ≤ Mstar :=
    section13_sylowSubgroupIn_le (G := G) hQstar_Mstar
  have hQstar_le_M : Qstar ≤ M := by
    have hQstar_inf : Qstar ≤ M ⊓ Mstar :=
      section13_sylowSubgroupIn_le (G := G) hQstar
    intro x hx
    exact (hQstar_inf hx).1
  have hQstarq : IsPGroup qstar.val Qstar :=
    section13_sylowSubgroupIn_isPGroup (G := G) hQstar
  have hQstarne : Qstar ≠ ⊥ :=
    section13_ne_bot_of_normalizer_le_maximal (G := G) hM hNQstar
  have hQstar_derived_Mstar : Qstar ≤ ambientDerivedSubgroup Mstar :=
    section13_le_ambientDerived_of_fixedpoint_free_sylow
      (G := G) (M := Mstar) (P := P) (Q := Qstar) (H := M ⊓ Mstar)
      (p := p) (q := qstar) hP hP_le_Mstar hQstar_le_Mstar hQstarq
      hQstarne hPinvQstar hCQstar
  have hQstar_derived_M : Qstar ≤ ambientDerivedSubgroup M :=
    section13_le_ambientDerived_of_fixedpoint_free_sylow
      (G := G) (M := M) (P := P) (Q := Qstar) (H := M ⊓ Mstar)
      (p := p) (q := qstar) hP hP_le_M hQstar_le_M hQstarq
      hQstarne hPinvQstar hCQstar
  have hMstar_eq_malpha_sup_NQstar :
      section10Malpha Mstar ⊔ subgroupNormalizerIn Mstar (Qstar : Set G) = Mstar :=
    section13_malpha_sup_subgroupNormalizerIn_of_derived_sylow
      (G := G) (M := Mstar) (Q := Qstar) (q := qstar)
      hMstar hQstar_Mstar hQstar_derived_Mstar
  let πβ : Set Nat.Primes := section10BetaPrimes M ∪ section10BetaPrimes Mstar
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let Cα : Subgroup G := subgroupCentralizerIn (section10Malpha M) P
  have hCαπ : IsPiSubgroup (G := G) πβ Cα := by
    intro u hu
    have huα : u ∈ section10AlphaPrimes M :=
      ((theorem_10_2_a (G := G) hM).1).p_in_pi_of_p_dvd_card u
        (hu.trans (Subgroup.card_dvd_of_le (inf_le_left : Cα ≤ section10Malpha M)))
    exact Or.inl (by simpa [πβ, Cα, ← h12M.1] using huα)
  have hCGPproper : C ≠ ⊤ := by
    simpa [C] using
      section13_lemma_13_8_centralizer_prime_order_ne_top
        (G := G) (M := M ⊓ Mstar) (P := P) (p := p) hP
  rcases section13_lemma_13_8_exists_hall_in_centralizer_containing_piSubgroup
      (G := G) (P := P) (K := Cα) (π := πβ)
      (by simpa [C] using hCGPproper) inf_le_right hCαπ with
    ⟨Hleft, hHleftHall, hCα_le_Hleft⟩
  rcases section13_lemma_13_8_exists_beta_prime_in_malpha_centralizer
      (G := G) (M := M) (P := P) hM h12M.1 h12M.2.2.2.1 with
    ⟨t, htβ, htCα⟩
  rcases section13_exists_prime_order_subgroup_le_of_prime_dvd
      (G := G) (A := Cα) (r := t) htCα with
    ⟨Y, hY_le_Cα, hYcard⟩
  have hYne : Y ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hYcard
  have hYt : IsPGroup t.val Y := by
    refine IsPGroup.of_card (p := t.val) (G := Y) (n := 1) ?_
    simpa [pow_one] using hYcard
  have hYHleft : Y ≤ Hleft.map C.subtype := by
    intro y hy
    have hyCα : y ∈ Cα := hY_le_Cα hy
    have hyC : y ∈ C := hyCα.2
    have hySub : (⟨y, hyC⟩ : C) ∈ Cα.subgroupOf C := hyCα
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hyC⟩, hCα_le_Hleft (by simpa [Cα, C] using hySub), rfl⟩
  rcases section13_lemma_13_8_hall_beta_fitting_union_side_choice
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Y := Y)
      (p := p) (t := t) hM hMstar hnotconj hP h12M.1 h12Mstar.1
      Hleft (by simpa [πβ] using hHleftHall) htβ hYne hYt
      (by simpa [C] using hYHleft) with
    ⟨s, hsSide, hCoreLeft⟩
  cases hsSide with
  | inl hsβ =>
      exact
        section13_lemma_13_8_absurd_of_malpha_centralizer_le_centralizer
          (G := G) (A := section10Malpha M) (P := P) (Q := Q)
          h12M.2.2.2.1 h12M.2.2.2.2
          (section13_lemma_13_8_malpha_centralizer_le_centralizer
            (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q)
            (Qstar := Qstar) (p := p) (q := q) (qstar := qstar)
            (sleft := s)
            hM hMstar hnotconj hpM hpMstar hP hQ_M hQ_le_M hQ_le_Mstar
            hQq hQne hPinvQ hCQ hNQ hQ_derived_Mstar hM_eq_malpha_sup_NQ
            h12M h12Mstar Hleft (by simpa [πβ] using hHleftHall)
            (by simpa [Cα, C] using hCα_le_Hleft) hsβ
            (by simpa [C] using hCoreLeft))
  | inr hsβstar =>
      let Cαstar : Subgroup G := subgroupCentralizerIn (section10Malpha Mstar) P
      have hCαstarπ : IsPiSubgroup (G := G) πβ Cαstar := by
        intro u hu
        have huα : u ∈ section10AlphaPrimes Mstar :=
          ((theorem_10_2_a (G := G) hMstar).1).p_in_pi_of_p_dvd_card u
            (hu.trans (Subgroup.card_dvd_of_le
              (inf_le_left : Cαstar ≤ section10Malpha Mstar)))
        exact Or.inr (by simpa [πβ, Cαstar, ← h12Mstar.1] using huα)
      rcases section13_lemma_13_8_exists_hall_in_centralizer_containing_piSubgroup
          (G := G) (P := P) (K := Cαstar) (π := πβ)
          (by simpa [C] using hCGPproper) inf_le_right hCαstarπ with
        ⟨Hright, hHrightHall, hCαstar_le_Hright⟩
      have hCoreRight :
          pCore s.val (Hright.map (Subgroup.centralizer (P : Set G)).subtype) ≠ ⊥ :=
        section13_lemma_13_8_hall_beta_pcore_ne_bot_transfer
          (G := G) (P := P) (π := πβ) (H₁ := Hleft) (H₂ := Hright) (s := s)
          (by simpa [C] using hCGPproper)
          (by simpa [πβ] using hHleftHall)
          (by simpa [πβ] using hHrightHall)
          (by simpa [C] using hCoreLeft)
      have hHrightHall_swap :
          IsHallSubgroup (section10BetaPrimes Mstar ∪ section10BetaPrimes M) Hright := by
        simpa [πβ, Set.union_comm] using hHrightHall
      exact
        section13_lemma_13_8_absurd_of_malpha_centralizer_le_centralizer
          (G := G) (A := section10Malpha Mstar) (P := P) (Q := Qstar)
          h12Mstar.2.2.2.1 h12Mstar.2.2.2.2
          (section13_lemma_13_8_malpha_centralizer_le_centralizer
            (G := G) (M := Mstar) (Mstar := M) (P := P) (Q := Qstar)
            (Qstar := Q) (p := p) (q := qstar) (qstar := q)
            (sleft := s)
            hMstar hM hnotconj_symm hpMstar hpM hP_swap hQstar_Mstar
            hQstar_le_Mstar hQstar_le_M hQstarq hQstarne hPinvQstar hCQstar
            hNQstar hQstar_derived_M hMstar_eq_malpha_sup_NQstar h12Mstar h12M
            Hright hHrightHall_swap
            (by simpa [Cαstar, C] using hCαstar_le_Hright) hsβstar
            hCoreRight)

end Section13
