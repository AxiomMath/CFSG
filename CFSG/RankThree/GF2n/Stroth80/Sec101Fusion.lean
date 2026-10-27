module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Pair
public import CFSG.RankThree.GF2n.Stroth80.Sec101O2
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndNormal
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailSylow
public import CFSG.GroupTheory.TISylowLocal
public import CFSG.LargeExtraspecial.S111SHCor3

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem exists_sylow_bar_LB_le_normalizer [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X : Subgroup G} (hX : IsClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X)
    (hBX : B ≤ X) :
    ∃ S : Sylow 2 (Mbar M Q),
      bar M Q (LB M Q B) ≤ (S : Subgroup (Mbar M Q)) ∧
      (S : Subgroup (Mbar M Q)) ≤
        Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ∧
      (S : Subgroup (Mbar M Q)) ≤ bar M Q (M ⊓ Subgroup.normalizer (X : Set G)) := by
  haveI : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  have hΛ2 : IsPGroup 2 (bar M Q (LB M Q B)) := hc.isElemAbelian_bar_LB.isPGroup
  obtain ⟨S, hΛS⟩ := IsPGroup.exists_le_sylow hΛ2
  have hSN : (S : Subgroup (Mbar M Q)) ≤
      Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) :=
    (hc.swapHyp H.width H.n_gt H.noA2).sylow S S.isPGroup' hΛS
  refine ⟨S, hΛS, hSN, ?_⟩
  intro s hs
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) s
  have hyN : (y : G) ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    mem_normalizer_of_mk_mem_normalizer_bar (le_sup_left : Q ≤ LB M Q B) hc.LB_le_M y (hSN hs)
  have hyX : (y : G) ∈ Subgroup.normalizer (X : Set G) :=
    IsSaturated101.mem_normalizer_of_mem_normalizer_LB H hX hsat (IsRootB.self (M := M)) hBX
      y.2 hyN
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨y.2, hyX⟩)

theorem IsSaturated101.exists_central_O2 [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {X : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X) (hBX : B ≤ X) :
    ∃ S : Sylow 2 (↥M ⧸ Q.subgroupOf M),
      (S : Subgroup (↥M ⧸ Q.subgroupOf M)) ≤
        Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (↥M ⧸ Q.subgroupOf M)) :
          Set (↥M ⧸ Q.subgroupOf M)) ∧
      (S : Subgroup (↥M ⧸ Q.subgroupOf M)) ≤ bar M Q (M ⊓ Subgroup.normalizer (X : Set G)) ∧
      ∃ t ∈ bar M Q (LB M Q B), t ≠ 1 ∧ t ∈ (S : Subgroup (↥M ⧸ Q.subgroupOf M)) ∧
        (∀ x ∈ (S : Subgroup (↥M ⧸ Q.subgroupOf M)), x * t = t * x) ∧
        t ∈ inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) := by
  haveI : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  obtain ⟨S, hΛS, hSN, hSX⟩ := exists_sylow_bar_LB_le_normalizer h34 H hX hsat hBX
  have hΛ2 : IsPGroup 2 (bar M Q (LB M Q B)) := hc.isElemAbelian_bar_LB.isPGroup
  set O : Subgroup (Mbar M Q) :=
    inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) with hO
  set A : Subgroup (Mbar M Q) := bar M Q (LB M Q B) ⊓ O with hA
  have hA2 : IsPGroup 2 A := hΛ2.to_le inf_le_left
  have hA1 : A ≠ ⊥ := by
    rw [hA, hO]
    exact IsSaturated101.bar_LB_inf_pCore_ne_bot h34 H hX hsat hBX
  have hSA : (S : Subgroup (Mbar M Q)) ≤ Subgroup.normalizer (A : Set (Mbar M Q)) := by
    intro s hs
    exact CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_inf (hSN hs)
      ((CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2
        (bar M Q (M ⊓ Subgroup.normalizer (X : Set G)))) (Subgroup.le_normalizer (hSX hs)))
  obtain ⟨t, htA, ht1, htS, htcc⟩ := endg_exists_sylow_central hA2 hA1 S hSA
  exact ⟨S, hSN, hSX, t, htA.1, ht1, htS, htcc, htA.2⟩

private theorem mk_mem_normalizer_pCore_of_mem_normalizer [(Q.subgroupOf M).Normal]
    {X : Subgroup G} (g : ↥M) (hgN : (g : G) ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' (Q.subgroupOf M) g ∈
      Subgroup.normalizer (inSubgroup (pCore 2)
        (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) : Set (Mbar M Q)) := by
  have hmN : QuotientGroup.mk' (Q.subgroupOf M) g ∈
      bar M Q (M ⊓ Subgroup.normalizer (X : Set G)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨g.2, hgN⟩)
  exact (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2
    (bar M Q (M ⊓ Subgroup.normalizer (X : Set G)))) (Subgroup.le_normalizer hmN)

private theorem conj_mem_pCore_of_mem_normalizer [(Q.subgroupOf M).Normal]
    {X : Subgroup G} (g : ↥M) (hgN : (g : G) ∈ Subgroup.normalizer (X : Set G))
    {t : Mbar M Q}
    (htO : t ∈ inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G)))) :
    QuotientGroup.mk' (Q.subgroupOf M) g * t * (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ ∈
      inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) :=
  (Subgroup.mem_normalizer_iff.mp (mk_mem_normalizer_pCore_of_mem_normalizer g hgN) t).mp htO

private theorem conj_centralizes_pCore_of_mem_normalizer [(Q.subgroupOf M).Normal]
    {X : Subgroup G} {S : Sylow 2 (Mbar M Q)}
    (hOS : inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) ≤
      (S : Subgroup (Mbar M Q)))
    {t : Mbar M Q}
    (htc : ∀ x ∈ (S : Subgroup (Mbar M Q)), x * t = t * x)
    (g : ↥M) (hgN : (g : G) ∈ Subgroup.normalizer (X : Set G))
    {z : Mbar M Q}
    (hz : z ∈ inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G)))) :
    z * (QuotientGroup.mk' (Q.subgroupOf M) g * t *
        (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹) =
      (QuotientGroup.mk' (Q.subgroupOf M) g * t *
        (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹) * z := by
  have hmO : QuotientGroup.mk' (Q.subgroupOf M) g ∈
      Subgroup.normalizer (inSubgroup (pCore 2)
        (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) : Set (Mbar M Q)) :=
    mk_mem_normalizer_pCore_of_mem_normalizer g hgN
  have hzinv : (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ * z *
      QuotientGroup.mk' (Q.subgroupOf M) g ∈
      inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmO) z).mp hz
    simpa using this
  have hzt : ((QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ * z *
        QuotientGroup.mk' (Q.subgroupOf M) g) * t =
      t * ((QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ * z *
        QuotientGroup.mk' (Q.subgroupOf M) g) :=
    htc _ (hOS hzinv)
  calc z * (QuotientGroup.mk' (Q.subgroupOf M) g * t *
          (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹)
      = QuotientGroup.mk' (Q.subgroupOf M) g *
          (((QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ * z *
            QuotientGroup.mk' (Q.subgroupOf M) g) * t) *
          (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ := by group
    _ = QuotientGroup.mk' (Q.subgroupOf M) g *
          (t * ((QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ * z *
            QuotientGroup.mk' (Q.subgroupOf M) g)) *
          (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ := by rw [hzt]
    _ = (QuotientGroup.mk' (Q.subgroupOf M) g * t *
          (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹) * z := by group

private theorem commutator_mem_Q_of_mk_eq [(Q.subgroupOf M).Normal]
    {t y : Mbar M Q} {σ : ↥M} {τ : G} (hτM : τ ∈ M)
    (hσmk : QuotientGroup.mk' (Q.subgroupOf M) σ = t)
    (hτmk : QuotientGroup.mk' (Q.subgroupOf M) ⟨τ, hτM⟩ = y)
    (hcomm : y * t = t * y) :
    ⁅(σ : G), τ⁆ ∈ Q := by
  set τ' : ↥M := ⟨τ, hτM⟩ with hτ'
  have hq : QuotientGroup.mk' (Q.subgroupOf M) (⁅σ, τ'⁆ : ↥M) = 1 := by
    rw [map_commutatorElement]
    rw [hσmk, hτmk, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  have hmem : (⁅σ, τ'⁆ : ↥M) ∈ Q.subgroupOf M := (QuotientGroup.eq_one_iff _).mp hq
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa [τ', commutatorElement_def] using this

private theorem false_of_inf_eq_Z [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ}
    (h34 : Stroth34Statement) (H : Sec10Hyp hc n) {X : Subgroup G}
    (hX : IsMaxClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X) (hBX : B ≤ X)
    {t : Mbar M Q} (ht : t ∈ bar M Q (LB M Q B)) (ht1 : t ≠ 1) (g : ↥M)
    (hZ : X ⊓ conjSubgroup (g : G) X = Z)
    (hcomm : (QuotientGroup.mk' (Q.subgroupOf M) g * t *
        (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹) * t =
      t * (QuotientGroup.mk' (Q.subgroupOf M) g * t *
        (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹)) : False := by
  obtain ⟨σ, hσLB, hσQ, hσmk⟩ := hc.exists_lift_ne_one ht ht1
  set τ : G := (g : G) * (σ : G) * (g : G)⁻¹ with hτ
  have hτLB : τ ∈ LB M Q (conjSubgroup (g : G) B) := by
    rw [hc.LB_conj g.2]
    refine mem_conjSubgroup.mpr ?_
    have h : (g : G)⁻¹ * τ * (g : G) = (σ : G) := by rw [hτ]; group
    rwa [h]
  have hτM : τ ∈ M := by
    rw [hτ]
    exact M.mul_mem (M.mul_mem g.2 (hc.LB_le_M hσLB)) (M.inv_mem g.2)
  have hτQ : τ ∉ Q := by
    intro hτQ
    have h1 : (g : G)⁻¹ * τ * (g : G) ∈ Q := by
      have hmem : τ ∈ conjSubgroup (g : G) Q := by rwa [hc.conj_Q_eq g.2]
      exact mem_conjSubgroup.mp hmem
    have h2 : (g : G)⁻¹ * τ * (g : G) = (σ : G) := by rw [hτ]; group
    exact hσQ (h2 ▸ h1)
  have hτmk : QuotientGroup.mk' (Q.subgroupOf M) ⟨τ, hτM⟩ =
      QuotientGroup.mk' (Q.subgroupOf M) g * t *
        (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ := by
    have h1 : (⟨τ, hτM⟩ : ↥M) = ⟨g, g.2⟩ * σ * ⟨g, g.2⟩⁻¹ := by
      ext
      simp [hτ]
    rw [h1, map_mul, map_mul, map_inv]
    rw [show QuotientGroup.mk' (Q.subgroupOf M) σ = t by simpa using hσmk]
  have hστ : ⁅(σ : G), τ⁆ ∈ Q :=
    commutator_mem_Q_of_mk_eq hτM hσmk hτmk hcomm
  exact IsSaturated101.no_commuting_pair h34 H hX hsat (hX.1.conj hc g.2)
    (hsat.conj hc g.2) hZ (IsRootB.self (M := M)) hBX
    (IsRootB.conj (IsRootB.self (M := M)) g.2) (Subgroup.map_mono hBX)
    hσLB hσQ hτLB hτQ hστ

private theorem wclSet_subset_pCore_centralizer [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X : Subgroup G} (hX : IsMaxClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X)
    (hBX : B ≤ X) (S : Sylow 2 (Mbar M Q))
    (hSX : (S : Subgroup (Mbar M Q)) ≤ bar M Q (M ⊓ Subgroup.normalizer (X : Set G)))
    {t : Mbar M Q} (ht : t ∈ bar M Q (LB M Q B)) (ht1 : t ≠ 1)
    (htc : ∀ x ∈ (S : Subgroup (Mbar M Q)), x * t = t * x)
    (htO : t ∈ inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G)))) :
    CFSG.LargeExtraspecial.S11.wclSet t ⊆
      (inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) ⊓
        Subgroup.centralizer (inSubgroup (pCore 2)
          (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) : Set (Mbar M Q)) :
        Subgroup (Mbar M Q)) := by
  haveI : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  set O : Subgroup (Mbar M Q) :=
    inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G)))
  have hOS : O ≤ (S : Subgroup (Mbar M Q)) :=
    CFSG.GroupTheory.inSubgroup_pCore_le_of_isSylow hSX
  rintro y ⟨m, rfl, hym⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) m
  rcases IsSaturated101.inf_eq hc hX.1 hsat g.2 with hZ | hXg
  · exact (false_of_inf_eq_Z h34 H hX hsat hBX ht ht1 g hZ hym).elim
  · have hgN : (g : G) ∈ Subgroup.normalizer (X : Set G) := conjSubgroup_eq_self_iff.mp hXg
    refine ⟨conj_mem_pCore_of_mem_normalizer g hgN htO, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact conj_centralizes_pCore_of_mem_normalizer hOS htc g hgN hz

theorem IsSaturated101.isMulCommutative_wcl [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {X : Subgroup G}
    (hX : IsMaxClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X) (hBX : B ≤ X)
    (S : Sylow 2 (↥M ⧸ Q.subgroupOf M))
    (hSX : (S : Subgroup (↥M ⧸ Q.subgroupOf M)) ≤ bar M Q (M ⊓ Subgroup.normalizer (X : Set G)))
    {t : ↥M ⧸ Q.subgroupOf M} (ht : t ∈ bar M Q (LB M Q B)) (ht1 : t ≠ 1)
    (htc : ∀ x ∈ (S : Subgroup (↥M ⧸ Q.subgroupOf M)), x * t = t * x)
    (htO : t ∈ inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G)))) :
    IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl t) := by
  have hsub := wclSet_subset_pCore_centralizer h34 H hX hsat hBX S hSX ht ht1 htc htO
  have hpair : (CFSG.LargeExtraspecial.S11.wclSet t).Pairwise Commute := by
    intro a ha b hb _
    have ha' := hsub ha
    have hb' := hsub hb
    exact Subgroup.mem_centralizer_iff.mp hb'.2 a ha'.1
  exact Subgroup.isMulCommutative_closure hpair

end CFSG.RankThree.GF2n.Stroth80
