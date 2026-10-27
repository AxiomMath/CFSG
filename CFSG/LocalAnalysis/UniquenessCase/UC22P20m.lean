module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20j
import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThree.PartTwo.Sec18 in
theorem uc22p20m_le_of_perfect_sup {Y : Type*} [Group Y] [Finite Y] {X N O : Subgroup Y}
    (hX : ⁅X, X⁆ = X) (hXNO : X ≤ N ⊔ O) (hOn : O ≤ normalizer (N : Set Y)) (hO : IsPGroup 2 O) :
    X ≤ N := by
  have hNU : N ≤ N ⊔ O := le_sup_left
  have hUn : N ⊔ O ≤ normalizer (N : Set Y) := sup_le Subgroup.le_normalizer hOn
  haveI hNn : (N.subgroupOf (N ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNU).2 hUn
  haveI : Group.IsNilpotent ↥O := hO.isNilpotent
  haveI : Group.IsSolvable ↥O := inferInstance
  have hsurj : Function.Surjective ((QuotientGroup.mk' (N.subgroupOf (N ⊔ O))).comp
      (Subgroup.inclusion (le_sup_right : O ≤ N ⊔ O))) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf (N ⊔ O)) q
    have hx' : x ∈ ((N ⊔ O : Subgroup Y) : Set Y) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N O hOn] at hx'
    obtain ⟨n, hn, o, ho, rfl⟩ := hx'
    refine ⟨⟨o, ho⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff''.1 (hOn ho) n).1 hn
  have hsolv : Group.IsSolvable ((N ⊔ O : Subgroup Y) ⧸ N.subgroupOf (N ⊔ O)) :=
    Group.isSolvable_of_surjective hsurj
  exact (le_inSubgroup_perfectResidual hX hXNO).trans
    (inSubgroup_perfectResidual_le_of_isSolvable hNU hsolv)

open CFSG.RankThree.PartTwo.Sec18 in
open CFSG.RankThree.PartTwo.Sec18.Claim184LcProof in
theorem uc22p20m_eq_hinf_of_bar (D : Data G) {L K Q : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hKL : K ≤ L) (hKT : D.T ≤ normalizer (K : Set G)) (hKperf : ⁅K, K⁆ = K)
    (hQL : Q ≤ L) (hOQ : pCoreOf 2 L ≤ Q)
    (hbar : Hinf ((Q.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) =
      (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) : K = Hinf Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set O : Subgroup ↥L := CFSG.pCore 2 ↥L with hO
  set Q' : Subgroup ↥L := Q.subgroupOf L with hQ'
  set K' : Subgroup ↥L := K.subgroupOf L with hK'
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  have hOQ' : O ≤ Q' := fun x hx => Subgroup.mem_subgroupOf.2 (hOQ ⟨x, hx, rfl⟩)
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  have hstar : (Hinf Q').map π = K'.map π := by
    rw [← hbar]
    exact map_inSubgroup_perfectResidual π Q'
  have hK'perf : ⁅K', K'⁆ = K' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hK', Subgroup.map_subgroupOf_eq_of_le hKL, hKperf]
  have hQ'perf : ⁅Hinf Q', Hinf Q'⁆ = Hinf Q' := commutator_inSubgroup_perfectResidual Q'
  have hOK : O ≤ normalizer (K' : Set ↥L) := by
    intro x hx
    have hxT : (x : G) ∈ D.T := (uc22p20i_pCoreOf_le D hL ⟨x, hx, rfl⟩).1
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.1 (hKT hxT) (y : G)
    exact this
  have hOQ'n : O ≤ normalizer (Hinf Q' : Set ↥L) :=
    hOQ'.trans (le_normalizer_inSubgroup_perfectResidual Q')
  have h1 : K' ≤ Hinf Q' := by
    refine uc22p20m_le_of_perfect_sup hK'perf ?_ hOQ'n hO2
    intro x hx
    have hx' : π x ∈ (Hinf Q').map π := by rw [hstar]; exact ⟨x, hx, rfl⟩
    have := Subgroup.comap_map_eq π (Hinf Q') ▸ (Subgroup.mem_comap.2 hx' : x ∈ (((Hinf Q').map π).comap π))
    rwa [hker] at this
  have h2 : Hinf Q' ≤ K' := by
    refine uc22p20m_le_of_perfect_sup hQ'perf ?_ hOK hO2
    intro x hx
    have hx' : π x ∈ K'.map π := by rw [← hstar]; exact ⟨x, hx, rfl⟩
    have := Subgroup.comap_map_eq π K' ▸ (Subgroup.mem_comap.2 hx' : x ∈ ((K'.map π).comap π))
    rwa [hker] at this
  have hKK : K' = Hinf Q' := le_antisymm h1 h2
  have e1 : K = K'.map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hKL).symm
  have e2 : Hinf Q = (Hinf Q').map L.subtype := by
    have := inSubgroup_perfectResidual_map L.subtype L.subtype_injective Q'
    rw [hQ', Subgroup.map_subgroupOf_eq_of_le hQL] at this
    exact this
  rw [e1, e2, hKK]

theorem uc22p20m_conj_mem_pCoreOf (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {t x : G}
    (ht : t ∈ D.T) (hx : x ∈ pCoreOf 2 L) : t * x * t⁻¹ ∈ pCoreOf 2 L := by
  have hTL : D.T ≤ normalizer (L : Set G) := hL.1
  have hP2 : IsPGroup 2 (pCoreOf 2 L) := uc22p20b_isPGroup_pCoreOf L
  have hPL : pCoreOf 2 L ≤ L := uc22p20b_pCoreOf_le L
  have hmapL : (pCoreOf 2 L).map (MulAut.conj t).toMonoidHom ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hTL ht) y).1 (hPL hy)
  have hmap2 : IsPGroup 2 ((pCoreOf 2 L).map (MulAut.conj t).toMonoidHom) := hP2.map _
  have hmapn : ∀ l ∈ L, ∀ y ∈ (pCoreOf 2 L).map (MulAut.conj t).toMonoidHom,
      l * y * l⁻¹ ∈ (pCoreOf 2 L).map (MulAut.conj t).toMonoidHom := by
    rintro l hl _ ⟨y, hy, rfl⟩
    have hl' : t⁻¹ * l * t ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.1 (hTL (D.T.inv_mem ht)) l).1 hl
    refine ⟨(t⁻¹ * l * t) * y * (t⁻¹ * l * t)⁻¹, uc22p20b_conj_mem_pCoreOf_self hl' hy, ?_⟩
    simp only [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    group
  exact uc22p20b_le_pCoreOf hmapL hmap2 hmapn ⟨x, hx, rfl⟩

theorem uc22p20m_mem_normalizer_bar_iff (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (l : ↥L) : QuotientGroup.mk' (CFSG.pCore 2 ↥L) l ∈
      normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) ↔
      (l : G) ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
  refine ⟨uc22p20i_mem_normalizer_of_borel D hL l, fun hl => ?_⟩
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨l₂, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
  have e : π l * π l₂ * (π l)⁻¹ = π (l * l₂ * l⁻¹) := by simp [map_mul, map_inv]
  rw [e, uc22p20i_mem_sylowBar_iff D hL, uc22p20i_mem_sylowBar_iff D hL]
  have := Subgroup.mem_normalizer_iff.1 hl (l₂ : G)
  simpa using this

open CFSG.RankThree.PartTwo.Sec18 in
theorem uc22p20m_l0Parabolic_of_sandwich (D : Data G)
    (hS : H1930 D → ∀ L ∈ calL D.T D.M, uc22p20jSandwich (Bar2 L)) : L0Parabolic D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h1930 L hL K hK hKL
  obtain ⟨hKT, hKperf, -, -⟩ := hK.prop
  have hTL : D.T ≤ normalizer (L : Set G) := hL.1
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set U : Sylow 2 (Bar2 L) :=
    (uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL) with hU
  have hUdef : (U : Subgroup (Bar2 L)) = uc22p20iSylowBar D L := rfl
  set Kb : Subgroup (Bar2 L) := (K.subgroupOf L).map π with hKb
  obtain ⟨Pb, hNP, hYP, hPinf⟩ := hS h1930 L hL U (Kb ⊔ (U : Subgroup (Bar2 L))) le_sup_right
  have hKbP : Kb ≤ Pb := le_sup_left.trans hYP
  have hUP : (U : Subgroup (Bar2 L)) ≤ Pb := le_sup_right.trans hYP
  set Q₀ : Subgroup G := (Pb.comap π).map L.subtype with hQ₀
  have hmem₀ : ∀ x : G, x ∈ Q₀ ↔ ∃ hx : x ∈ L, π ⟨x, hx⟩ ∈ Pb := by
    intro x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.2, hl⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  set Q : Subgroup G := ⨅ t : D.T, Q₀.comap (MulAut.conj ((t : G)⁻¹)).toMonoidHom with hQ
  have hmemQ : ∀ x : G, x ∈ Q ↔ ∀ t : D.T, (t : G)⁻¹ * x * (t : G) ∈ Q₀ := by
    intro x
    simp only [hQ, Subgroup.mem_iInf, Subgroup.mem_comap, MulAut.conj_apply,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, inv_inv]
  have hQQ₀ : Q ≤ Q₀ := fun x hx => by simpa using (hmemQ x).1 hx ⟨1, D.T.one_mem⟩
  have hQL : Q ≤ L := fun x hx => ((hmem₀ x).1 (hQQ₀ hx)).1
  have hTconj : ∀ t ∈ D.T, ∀ l : G, l ∈ L → t⁻¹ * l * t ∈ L := fun t ht l hl => by
    simpa using (Subgroup.mem_normalizer_iff.1 (hTL (D.T.inv_mem ht)) l).1 hl
  have hTSn : D.T ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨D.T.mul_mem (D.T.mul_mem ht hxT) (D.T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.1 (hTL ht) x).1 hxL⟩
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, ?_⟩
      · have := D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) hxT) ht
        simpa [mul_assoc] using this
      · exact (Subgroup.mem_normalizer_iff.1 (hTL ht) x).2 hxL
  have hKQ : K ≤ Q := by
    intro k hk
    rw [hmemQ]
    intro t
    have hk' : (t : G)⁻¹ * k * t ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.1 (hKT (D.T.inv_mem t.2)) k).1 hk
    exact (hmem₀ _).2 ⟨hKL hk', hKbP ⟨⟨_, hKL hk'⟩, Subgroup.mem_subgroupOf.2 hk', rfl⟩⟩
  have hSQ : ∀ s : G, s ∈ D.T ⊓ L → s ∈ Q := by
    intro s hs
    rw [hmemQ]
    intro t
    have hs' : (t : G)⁻¹ * s * t ∈ D.T ⊓ L := by
      simpa using (Subgroup.mem_normalizer_iff.1 (hTSn (D.T.inv_mem t.2)) s).1 hs
    exact (hmem₀ _).2 ⟨hs'.2, hUP ⟨⟨_, hs'.2⟩, Subgroup.mem_subgroupOf.2 hs', rfl⟩⟩
  have hpc : ∀ z ∈ pCoreOf 2 L, z ∈ Q₀ := by
    rintro z ⟨y, hy, rfl⟩
    refine (hmem₀ _).2 ⟨y.2, ?_⟩
    have h1 : π y = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hy
    have h2 : (⟨L.subtype y, y.2⟩ : ↥L) = y := rfl
    rw [h2, h1]
    exact Pb.one_mem
  have hOQ : pCoreOf 2 L ≤ Q := fun o ho =>
    (hmemQ o).2 fun t =>
      hpc _ (by simpa using uc22p20m_conj_mem_pCoreOf D hL (D.T.inv_mem t.2) ho)
  have hTQ : D.T ≤ normalizer (Q : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemQ, hmemQ]
    constructor
    · intro h t
      have := h ⟨s⁻¹ * (t : G), D.T.mul_mem (D.T.inv_mem hs) t.2⟩
      have e : (s⁻¹ * (t : G))⁻¹ * x * (s⁻¹ * (t : G)) = (t : G)⁻¹ * (s * x * s⁻¹) * (t : G) := by
        group
      rw [e] at this
      exact this
    · intro h t
      have := h ⟨s * (t : G), D.T.mul_mem hs t.2⟩
      have e : (s * (t : G))⁻¹ * (s * x * s⁻¹) * (s * (t : G)) = (t : G)⁻¹ * x * (t : G) := by
        group
      rw [e] at this
      exact this
  have hNQ : normalizer ((U : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ (Q.subgroupOf L).map π := by
    intro y hy
    obtain ⟨l, rfl⟩ := hπs y
    refine ⟨l, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    have hl : (l : G) ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
      (uc22p20m_mem_normalizer_bar_iff D hL l).1 hy
    rw [hmemQ]
    intro t
    have hl' : (t : G)⁻¹ * l * t ∈ L := hTconj t t.2 l l.2
    refine (hmem₀ _).2 ⟨hl', hNP ?_⟩
    refine (uc22p20m_mem_normalizer_bar_iff D hL ⟨_, hl'⟩).2 ?_
    exact mul_mem (mul_mem (inv_mem (hTSn t.2)) hl) (hTSn t.2)
  have hRP : (Q.subgroupOf L).map π ≤ Pb := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨hx, h⟩ := (hmem₀ _).1 (hQQ₀ (Subgroup.mem_subgroupOf.1 hl))
    exact h
  have hKR : Kb ≤ (Q.subgroupOf L).map π := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.2 (hKQ (Subgroup.mem_subgroupOf.1 hl)), rfl⟩
  have hUR : (U : Subgroup (Bar2 L)) ≤ (Q.subgroupOf L).map π := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.2 (hSQ _ (Subgroup.mem_subgroupOf.1 hl)), rfl⟩
  have hK'perf : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKL, hKperf]
  have hKbperf : ⁅Kb, Kb⁆ = Kb := by
    rw [hKb, ← Subgroup.map_commutator, hK'perf]
  have hUKb : (U : Subgroup (Bar2 L)) ≤ normalizer (Kb : Set (Bar2 L)) := by
    refine uc22p20e_le_normalizer_of_conj fun y hy x hx => ?_
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨a * k * a⁻¹, ?_, by simp only [map_mul, map_inv]; try rfl⟩
    have haT : (a : G) ∈ D.T := (Subgroup.mem_subgroupOf.1 ha).1
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    exact Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 (hKT haT) (k : G)).1 hkK)
  have hbar : Hinf ((Q.subgroupOf L).map π) = Kb := by
    refine le_antisymm ?_ ?_
    · refine uc22p20m_le_of_perfect_sup (commutator_inSubgroup_perfectResidual _) ?_ hUKb
        U.isPGroup'
      exact (inSubgroup_perfectResidual_mono hRP).trans hPinf
    · exact le_inSubgroup_perfectResidual hKbperf hKR
  have hEq : K = Hinf Q := uc22p20m_eq_hinf_of_bar D hL hKL hKT hKperf hQL hOQ hbar
  exact ⟨Q, ⟨hOQ, hQL, U, hNQ⟩, hTQ, hEq⟩

end Lift

end CFSG.LocalAnalysis.UniquenessCase.UC22
