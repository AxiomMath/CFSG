module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_d

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# lemma_12_1_e
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_normal_of_derivedSubgroup_le
    {R : Type*} [Group R] (N : Subgroup R) (hder : derivedSubgroup R ≤ N) :
    N.Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  have hcomm : ⁅g, n⁆ ∈ derivedSubgroup R := by
    change ⁅g, n⁆ ∈ derivedSeries R 1
    rw [derivedSeries_one]
    exact Subgroup.commutator_mem_commutator
      (H₁ := (⊤ : Subgroup R)) (H₂ := (⊤ : Subgroup R)) (by simp) (by simp)
  have hconj_eq : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]
    group
  rw [hconj_eq]
  exact N.mul_mem (hder hcomm) hn

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_normalIn_of_ambientDerivedSubgroup_le
    {H K : Subgroup G} (hKH : K ≤ H) (hder : ambientDerivedSubgroup H ≤ K) :
    section10NormalIn K H := by
  refine ⟨hKH, ?_⟩
  apply section12_normal_of_derivedSubgroup_le
  intro x hx
  change (x : G) ∈ K
  exact hder (Subgroup.mem_map_of_mem H.subtype hx)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isPiSubgroup_of_hall
    {R : Type*} [Group R] {π : Set Nat.Primes} {H : Subgroup R}
    (hH : IsHallSubgroup π H) :
    IsPiSubgroup (G := R) π H :=
  hH.p_in_pi_of_p_dvd_card

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isPiSubgroup_map
    {R S : Type*} [Group R] [Group S] {π : Set Nat.Primes} {H : Subgroup R}
    (hH : IsPiSubgroup (G := R) π H) (f : R →* S) :
    IsPiSubgroup (G := S) π (H.map f) := by
  intro p hp
  exact hH p (hp.trans (Subgroup.card_map_dvd (H := H) f))

omit [IsMinCE G] in
private theorem CFSG.section12_isPiSubgroup_sup_of_normal_right
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes} {H K : Subgroup R}
    (hH : IsPiSubgroup (G := R) π H) (hK : IsPiSubgroup (G := R) π K)
    [K.Normal] :
    IsPiSubgroup (G := R) π (H ⊔ K) := by
  intro p hpSup
  have hmul : (↑(H ⊔ K) : Set R) = (H : Set R) * (K : Set R) := by
    simpa using (Subgroup.mul_normal H K)
  have hcard_sup_set :
      Nat.card (↑(H ⊔ K) : Set R) = Nat.card ((H : Set R) * (K : Set R) : Set R) :=
    Nat.card_congr (Set.equivOfEq hmul)
  have hcard_sup :
      Nat.card (↥(H ⊔ K)) = Nat.card ((H : Set R) * (K : Set R) : Set R) := by
    simpa using hcard_sup_set
  have hcard_mul :
      Nat.card ((H : Set R) * (K : Set R) : Set R) =
        Nat.card K * Nat.card ((H : Set R).image (↑) : Set (R ⧸ K)) := by
    simpa using
      (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := K) (t := (H : Set R)))
  have hset_image :
      ((H : Set R).image (↑) : Set (R ⧸ K)) =
        (H.map (QuotientGroup.mk' K) : Set (R ⧸ K)) := by
    simp [Subgroup.coe_map]
  have hcard_image_set :
      Nat.card ((H : Set R).image (↑) : Set (R ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K) : Set (R ⧸ K)) :=
    Nat.card_congr (Set.equivOfEq hset_image)
  have hcard_image_subgroup :
      Nat.card ((H : Set R).image (↑) : Set (R ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K)) := by
    exact hcard_image_set
  have hp_mul :
      p.val ∣ Nat.card K * Nat.card ((H : Set R).image (↑) : Set (R ⧸ K)) := by
    rw [← hcard_mul, ← hcard_sup]
    exact hpSup
  rcases p.2.dvd_mul.mp hp_mul with hpK | hpImg
  · exact hK p hpK
  · have hpMap : p.val ∣ Nat.card (H.map (QuotientGroup.mk' K)) := by
      rwa [hcard_image_subgroup] at hpImg
    exact (section12_isPiSubgroup_map hH (QuotientGroup.mk' K)) p hpMap

omit [IsMinCE G] in
public theorem CFSG.section12_normal_piSubgroup_le_hall
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes} {K L : Subgroup R}
    [K.Normal] (hKπ : IsPiSubgroup (G := R) π K) (hLHall : IsHallSubgroup π L) :
    K ≤ L := by
  classical
  let KL : Subgroup R := L ⊔ K
  have hLπ : IsPiSubgroup (G := R) π L := section12_isPiSubgroup_of_hall hLHall
  have hKLπ : IsPiSubgroup (G := R) π KL := by
    simpa [KL] using section12_isPiSubgroup_sup_of_normal_right hLπ hKπ
  have hKLHall : IsHallSubgroup π KL := by
    refine isHallSubgroup_of (G := R) π KL hKLπ ?_
    intro p hpπ hpidx
    have hidx_dvd : KL.index ∣ L.index :=
      Subgroup.index_dvd_of_le (show L ≤ KL by exact le_sup_left)
    exact (hLHall.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ
  have hEq : L = KL := hLHall.eq_of_le hKLHall le_sup_left
  intro x hx
  have hxKL : x ∈ KL := (le_sup_right : K ≤ KL) hx
  simpa [hEq] using hxKL

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_nilpotent_ambientDerivedSubgroup_of_le
    {H K : Subgroup G} (hHK : H ≤ K)
    (hnilK : Group.IsNilpotent (ambientDerivedSubgroup K)) :
    Group.IsNilpotent (ambientDerivedSubgroup H) := by
  let e : (ambientDerivedSubgroup H).subgroupOf (ambientDerivedSubgroup K) ≃*
      ambientDerivedSubgroup H :=
    Subgroup.subgroupOfEquivOfLe
      (H := ambientDerivedSubgroup H) (K := ambientDerivedSubgroup K)
      (section12_ambientDerivedSubgroup_mono hHK)
  have : Group.IsNilpotent (ambientDerivedSubgroup K) := hnilK
  have hsubnil :
      Group.IsNilpotent ((ambientDerivedSubgroup H).subgroupOf (ambientDerivedSubgroup K)) :=
    inferInstance
  exact Group.nilpotent_of_mulEquiv
    (G := (ambientDerivedSubgroup H).subgroupOf (ambientDerivedSubgroup K))
    (G' := ambientDerivedSubgroup H) e

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_E1_hall_in_E
    {M E E₁₂ E₁ : Subgroup G}
    (hE12 : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE1 : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂) :
    section12HallSubgroupIn (section12Tau1Primes M) E₁ E := by
  classical
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  refine ⟨hE1E12.trans hE12E, ?_⟩
  refine isHallSubgroup_of (G := E) (section12Tau1Primes M) (E₁.subgroupOf E) ?_ ?_
  · intro p hp
    have hcardE : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
      natCard_subgroupOf_eq _ _ (hE1E12.trans hE12E)
    have hcardE12 : Nat.card (E₁.subgroupOf E₁₂) = Nat.card E₁ :=
      natCard_subgroupOf_eq _ _ hE1E12
    exact hHallE1.p_in_pi_of_p_dvd_card p (by simpa [hcardE, hcardE12] using hp)
  · intro p hpτ1 hpidx
    change p.val ∣ E₁.relIndex E at hpidx
    have hmul :
        E₁.relIndex E₁₂ * E₁₂.relIndex E = E₁.relIndex E :=
      Subgroup.relIndex_mul_relIndex E₁ E₁₂ E hE1E12 hE12E
    have hprod : p.val ∣ E₁.relIndex E₁₂ * E₁₂.relIndex E := by
      simpa [hmul] using hpidx
    rcases p.2.dvd_mul.mp hprod with hpidx1 | hpidx12
    · exact (hHallE1.p_in_pi_of_p_dvd_index p (by simpa [Subgroup.relIndex] using hpidx1))
        hpτ1
    · exact (hHallE12.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidx12)) (Or.inl hpτ1)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_E2_hall_in_E
    {M E E₁₂ E₂ : Subgroup G}
    (hE12 : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE2 : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂) :
    section12HallSubgroupIn (section12Tau2Primes M) E₂ E := by
  classical
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE2 with ⟨hE2E12, hHallE2⟩
  refine ⟨hE2E12.trans hE12E, ?_⟩
  refine isHallSubgroup_of (G := E) (section12Tau2Primes M) (E₂.subgroupOf E) ?_ ?_
  · intro p hp
    have hcardE : Nat.card (E₂.subgroupOf E) = Nat.card E₂ :=
      natCard_subgroupOf_eq _ _ (hE2E12.trans hE12E)
    have hcardE12 : Nat.card (E₂.subgroupOf E₁₂) = Nat.card E₂ :=
      natCard_subgroupOf_eq _ _ hE2E12
    exact hHallE2.p_in_pi_of_p_dvd_card p (by simpa [hcardE, hcardE12] using hp)
  · intro p hpτ2 hpidx
    change p.val ∣ E₂.relIndex E at hpidx
    have hmul :
        E₂.relIndex E₁₂ * E₁₂.relIndex E = E₂.relIndex E :=
      Subgroup.relIndex_mul_relIndex E₂ E₁₂ E hE2E12 hE12E
    have hprod : p.val ∣ E₂.relIndex E₁₂ * E₁₂.relIndex E := by
      simpa [hmul] using hpidx
    rcases p.2.dvd_mul.mp hprod with hpidx2 | hpidx12
    · exact (hHallE2.p_in_pi_of_p_dvd_index p (by simpa [Subgroup.relIndex] using hpidx2))
        hpτ2
    · exact (hHallE12.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidx12)) (Or.inr hpτ2)

omit [IsMinCE G] in
private theorem CFSG.section12_no_tau1_prime_dvd_derivedSubgroup
    {M H E₁ : Subgroup G}
    (hHM : H ≤ M)
    (hE1H : section12HallSubgroupIn (section12Tau1Primes M) E₁ H)
    (hInfBot : E₁ ⊓ ambientDerivedSubgroup M = ⊥)
    (hnilH : Group.IsNilpotent (ambientDerivedSubgroup H))
    {p : Nat.Primes} (hpτ1 : p ∈ section12Tau1Primes M) :
    ¬ p.val ∣ Nat.card (derivedSubgroup H) := by
  classical
  intro hpD
  have : Fact p.val.Prime := ⟨p.2⟩
  rcases hE1H with ⟨hE1Hle, hHallE1H⟩
  let D : Subgroup H := derivedSubgroup H
  let P : Sylow p.val D := Classical.choice (Sylow.nonempty (p := p.val) (G := D))
  have hP_ne_bot : (P : Subgroup D) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := D) P (by simpa [D] using hpD)
  let Pmap : Subgroup H := (P : Subgroup D).map D.subtype
  have hPmap_ne_bot : Pmap ≠ ⊥ := by
    intro hPmap_bot
    have hP_bot : (P : Subgroup D) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (P : Subgroup D)) (f := D.subtype)
        D.subtype_injective).1 (by simpa [Pmap] using hPmap_bot)
    exact hP_ne_bot hP_bot
  have hPmap_p : IsPGroup p.val Pmap :=
    IsPGroup.map P.isPGroup' D.subtype
  have hDnil : Group.IsNilpotent D :=
    section12_nilpotent_derivedSubgroup_of_ambient hnilH
  have hP_normal_D : (P : Subgroup D).Normal :=
    Group.IsNilpotent.sylow_normal hDnil p.val P
  have : (P : Subgroup D).Characteristic :=
    Sylow.characteristic_of_normal P hP_normal_D
  have : D.Normal := by
    dsimp [D]
    infer_instance
  have : Pmap.Normal := by
    change ((P : Subgroup D).map D.subtype).Normal
    infer_instance
  have hPmapπ : IsPiSubgroup (G := H) (section12Tau1Primes M) Pmap :=
    section12_isPiSubgroup_of_isPGroup_of_mem hPmap_p hpτ1
  have hPmap_le_E1 : Pmap ≤ E₁.subgroupOf H :=
    section12_normal_piSubgroup_le_hall (K := Pmap) (L := E₁.subgroupOf H)
      hPmapπ hHallE1H
  have hPmap_le_bot : Pmap ≤ ⊥ := by
    intro x hx
    have hxE1 : (x : G) ∈ E₁ := hPmap_le_E1 hx
    have hxD : x ∈ D := by
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hxDerH : (x : G) ∈ ambientDerivedSubgroup H :=
      Subgroup.mem_map_of_mem H.subtype hxD
    have hxDerM : (x : G) ∈ ambientDerivedSubgroup M :=
      section12_ambientDerivedSubgroup_mono hHM hxDerH
    have hxInf : (x : G) ∈ E₁ ⊓ ambientDerivedSubgroup M := ⟨hxE1, hxDerM⟩
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      simpa [hInfBot] using hxInf
    exact Subtype.ext (by simpa using hxbot)
  exact hPmap_ne_bot (le_bot_iff.mp hPmap_le_bot)

omit [IsMinCE G] in
public theorem CFSG.section12_normal_pSubgroup_le_of_isHallSubgroup_of_prime_mem
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {H N : Subgroup R} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hNp : IsPGroup p N) (hHall : IsHallSubgroup π H)
    (hp_mem : (⟨p, Fact.out⟩ : Nat.Primes) ∈ π) :
    N ≤ H := by
  classical
  let PH : Sylow p H := Classical.choice (Sylow.nonempty (p := p) (G := H))
  let Psub : Subgroup R := (PH : Subgroup H).map H.subtype
  have hPsub_p : IsPGroup p Psub := by
    simpa [Psub] using
      (IsPGroup.map (p := p) (H := (PH : Subgroup H)) PH.isPGroup' H.subtype)
  have hp_not_dvd_Hindex : ¬ p ∣ H.index := by
    intro hp_dvd
    exact (hHall.p_in_pi_of_p_dvd_index ⟨p, Fact.out⟩ hp_dvd) hp_mem
  have hp_not_dvd_PHindex : ¬ p ∣ (PH : Subgroup H).index := PH.not_dvd_index
  have hp_not_dvd_Psubindex : ¬ p ∣ Psub.index := by
    have hidx : Psub.index = (PH : Subgroup H).index * H.index := by
      simpa [Psub] using (Subgroup.index_map_subtype (K := (PH : Subgroup H)))
    rw [hidx]
    exact Nat.Prime.not_dvd_mul Fact.out hp_not_dvd_PHindex hp_not_dvd_Hindex
  let S : Sylow p R := IsPGroup.toSylow (p := p) hPsub_p hp_not_dvd_Psubindex
  have hS_le_H : (S : Subgroup R) ≤ H := by
    intro x hx
    change x ∈ Psub at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  obtain ⟨Q, hNQ⟩ := IsPGroup.exists_le_sylow (p := p) hNp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R Q S
  have hN_le_gQ : N ≤ ((g • Q : Sylow p R) : Subgroup R) := by
    intro n hn
    rw [Sylow.coe_subgroup_smul]
    refine (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g)
      (S := (Q : Subgroup R)) (x := n)).2 ?_
    have hconj : g⁻¹ * n * g ∈ N := by
      simpa using ((inferInstance : N.Normal).conj_mem n hn g⁻¹)
    have hQ : g⁻¹ * n * g ∈ (Q : Subgroup R) := hNQ hconj
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hQ
  have hN_le_S : N ≤ (S : Subgroup R) := by
    simpa [hg] using hN_le_gQ
  exact le_trans hN_le_S hS_le_H

omit [IsMinCE G] in
private theorem CFSG.section12_ambientDerivedSubgroup_E12_le_E2
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hnilE : Group.IsNilpotent (ambientDerivedSubgroup E)) :
    ambientDerivedSubgroup E₁₂ ≤ E₂ := by
  classical
  rcases hE with ⟨hcomp, hE12, hE1, hE2, _hE3⟩
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE2 with ⟨hE2E12, hHallE2⟩
  have hInfBot : E₁ ⊓ ambientDerivedSubgroup M = ⊥ :=
    section12_E1_inf_ambientDerivedSubgroup_M_eq_bot (M := M) (E₁₂ := E₁₂) (E₁ := E₁) hE1
  have hnilE12 : Group.IsNilpotent (ambientDerivedSubgroup E₁₂) :=
    section12_nilpotent_ambientDerivedSubgroup_of_le hE12E hnilE
  have hD12π2 : IsPiSubgroup (G := E₁₂) (section12Tau2Primes M) (derivedSubgroup E₁₂) := by
    intro p hpD
    have hpE12 : p.val ∣ Nat.card E₁₂ :=
      hpD.trans (Subgroup.card_subgroup_dvd_card (derivedSubgroup E₁₂))
    have hpE12sub : p.val ∣ Nat.card (E₁₂.subgroupOf E) := by
      simpa [natCard_subgroupOf_eq _ _ hE12E] using hpE12
    have hpτ12 : p ∈ section12Tau1Primes M ∪ section12Tau2Primes M :=
      hHallE12.p_in_pi_of_p_dvd_card p hpE12sub
    rcases hpτ12 with hpτ1 | hpτ2
    · exact False.elim
        (section12_no_tau1_prime_dvd_derivedSubgroup
          (M := M) (H := E₁₂) (E₁ := E₁) (hE12E.trans hcomp.2.1)
          hE1 hInfBot hnilE12 hpτ1 hpD)
    · exact hpτ2
  have hD12_le_E2sub : derivedSubgroup E₁₂ ≤ E₂.subgroupOf E₁₂ :=
    section12_normal_piSubgroup_le_hall (K := derivedSubgroup E₁₂)
      (L := E₂.subgroupOf E₁₂) hD12π2 hHallE2
  intro x hx
  have hxE12 : x ∈ E₁₂ := section12_ambientDerivedSubgroup_le hx
  let x12 : E₁₂ := ⟨x, hxE12⟩
  have hxD12 : x12 ∈ derivedSubgroup E₁₂ := by
    have hxsub : x12 ∈ (ambientDerivedSubgroup E₁₂).subgroupOf E₁₂ := hx
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hxsub
  exact hD12_le_E2sub hxD12

omit [Finite G] [IsMinCE G] in
set_option maxHeartbeats 800000 in
private theorem CFSG.section12_E12_eq_E1_sup_E2
    {M E E₁₂ E₁ E₂ : Subgroup G}
    (hE12 : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE1 : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂)
    (hE2 : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂) :
    E₁₂ = E₁ ⊔ E₂ := by
  classical
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  rcases hE2 with ⟨hE2E12, hHallE2⟩
  let K12 : Subgroup E₁₂ := (E₁ ⊔ E₂).subgroupOf E₁₂
  have hK12top : K12 = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hqprime hqidx
    let p : Nat.Primes := ⟨q, hqprime⟩
    have hpidx : p.val ∣ K12.index := by simpa [p] using hqidx
    have hE1sub_le_K12 : E₁.subgroupOf E₁₂ ≤ K12 := by
      intro x hx
      change (x : G) ∈ E₁ ⊔ E₂
      exact Subgroup.mem_sup_left hx
    have hE2sub_le_K12 : E₂.subgroupOf E₁₂ ≤ K12 := by
      intro x hx
      change (x : G) ∈ E₁ ⊔ E₂
      exact Subgroup.mem_sup_right hx
    have hp_not_tau1 : p ∉ section12Tau1Primes M :=
      hHallE1.p_in_pi_of_p_dvd_index p
        (hpidx.trans (Subgroup.index_dvd_of_le hE1sub_le_K12))
    have hp_not_tau2 : p ∉ section12Tau2Primes M :=
      hHallE2.p_in_pi_of_p_dvd_index p
        (hpidx.trans (Subgroup.index_dvd_of_le hE2sub_le_K12))
    have hpE12 : p.val ∣ Nat.card E₁₂ := by
      have hmul : K12.index * Nat.card K12 = Nat.card E₁₂ :=
        Subgroup.index_mul_card (H := K12)
      exact hmul ▸ dvd_mul_of_dvd_left hpidx _
    have hpE12sub : p.val ∣ Nat.card (E₁₂.subgroupOf E) := by
      simpa [natCard_subgroupOf_eq _ _ hE12E] using hpE12
    have hpτ12 : p ∈ section12Tau1Primes M ∪ section12Tau2Primes M :=
      hHallE12.p_in_pi_of_p_dvd_card p hpE12sub
    rcases hpτ12 with hpτ1 | hpτ2
    · exact hp_not_tau1 hpτ1
    · exact hp_not_tau2 hpτ2
  have hlocal : (E₁ ⊔ E₂).subgroupOf E₁₂ = ⊤ := by
    simpa [K12] using hK12top
  exact le_antisymm (Subgroup.subgroupOf_eq_top.1 hlocal) (sup_le hE1E12 hE2E12)

private theorem CFSG.section12_E12_sup_E3_subgroupOf_E_eq_top
    {M E E₁₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E)
    (hE12 : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE3 : section12HallSubgroupIn (section12Tau3Primes M) E₃ E) :
    (E₁₂ ⊔ E₃).subgroupOf E = ⊤ := by
  classical
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  apply Subgroup.index_eq_one.mp
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hqprime hqidx
  let p : Nat.Primes := ⟨q, hqprime⟩
  have hpidx : p.val ∣ ((E₁₂ ⊔ E₃).subgroupOf E).index := by
    simpa [p] using hqidx
  have hE12sub_le_join : E₁₂.subgroupOf E ≤ (E₁₂ ⊔ E₃).subgroupOf E := by
    intro x hx
    change (x : G) ∈ E₁₂ ⊔ E₃
    exact Subgroup.mem_sup_left hx
  have hE3sub_le_join : E₃.subgroupOf E ≤ (E₁₂ ⊔ E₃).subgroupOf E := by
    intro x hx
    change (x : G) ∈ E₁₂ ⊔ E₃
    exact Subgroup.mem_sup_right hx
  have hp_not_tau12 : p ∉ section12Tau1Primes M ∪ section12Tau2Primes M :=
    hHallE12.p_in_pi_of_p_dvd_index p
      (hpidx.trans (Subgroup.index_dvd_of_le hE12sub_le_join))
  have hp_not_tau3 : p ∉ section12Tau3Primes M :=
    hHallE3.p_in_pi_of_p_dvd_index p
      (hpidx.trans (Subgroup.index_dvd_of_le hE3sub_le_join))
  have hpE : p.val ∣ Nat.card E := by
    have hmul :
        ((E₁₂ ⊔ E₃).subgroupOf E).index *
            Nat.card ((E₁₂ ⊔ E₃).subgroupOf E) = Nat.card E :=
      Subgroup.index_mul_card (H := (E₁₂ ⊔ E₃).subgroupOf E)
    exact hmul ▸ dvd_mul_of_dvd_left hpidx _
  have hpτ :
      p ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M :=
    section12_prime_mem_tau_union_of_mem_E hM hcomp (by
      simpa [subgroupPrimeSet] using hpE)
  rcases hpτ with hpτ12 | hpτ3
  · exact hp_not_tau12 hpτ12
  · exact hp_not_tau3 hpτ3

set_option maxHeartbeats 800000 in
private theorem CFSG.section12_E12_sup_E3_eq_E
    {M E E₁₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E)
    (hE12 : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE3 : section12HallSubgroupIn (section12Tau3Primes M) E₃ E) :
    E = E₁₂ ⊔ E₃ := by
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  have hlocal : (E₁₂ ⊔ E₃).subgroupOf E = ⊤ :=
    section12_E12_sup_E3_subgroupOf_E_eq_top
      (M := M) (E := E) (E₁₂ := E₁₂) (E₃ := E₃) hM hcomp
      ⟨hE12E, hHallE12⟩ ⟨hE3E, hHallE3⟩
  have hE_le : E ≤ E₁₂ ⊔ E₃ := Subgroup.subgroupOf_eq_top.1 hlocal
  have hsup_le : E₁₂ ⊔ E₃ ≤ E := sup_le hE12E hE3E
  exact le_antisymm hE_le hsup_le

omit [IsMinCE G] in
public theorem CFSG.section12_E2_sup_E3_hall_in_E
    {M E E₁₂ E₂ E₃ : Subgroup G}
    (hE12 : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE2 : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂)
    (hE3 : section12HallSubgroupIn (section12Tau3Primes M) E₃ E)
    (hE3normIn : section10NormalIn E₃ E) :
    section12HallSubgroupIn (section12Tau2Primes M ∪ section12Tau3Primes M)
      (E₂ ⊔ E₃) E := by
  classical
  rcases hE3 with ⟨hE3E, hHallE3⟩
  rcases hE3normIn with ⟨_hE3E', hE3sub_norm⟩
  have hE2EHall : section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E (M := M) (E := E) (E₁₂ := E₁₂) (E₂ := E₂) hE12 hE2
  rcases hE2EHall with ⟨hE2E, hHallE2E⟩
  let K : Subgroup E := E₂.subgroupOf E ⊔ E₃.subgroupOf E
  have : (E₃.subgroupOf E).Normal := hE3sub_norm
  have hKπ : IsPiSubgroup (G := E)
      (section12Tau2Primes M ∪ section12Tau3Primes M) K := by
    have hE2π : IsPiSubgroup (G := E)
        (section12Tau2Primes M ∪ section12Tau3Primes M) (E₂.subgroupOf E) := by
      intro p hp
      exact Or.inl (hHallE2E.p_in_pi_of_p_dvd_card p hp)
    have hE3π : IsPiSubgroup (G := E)
        (section12Tau2Primes M ∪ section12Tau3Primes M) (E₃.subgroupOf E) := by
      intro p hp
      exact Or.inr (hHallE3.p_in_pi_of_p_dvd_card p hp)
    simpa [K] using section12_isPiSubgroup_sup_of_normal_right hE2π hE3π
  have hKHall : IsHallSubgroup
      (section12Tau2Primes M ∪ section12Tau3Primes M) K := by
    refine isHallSubgroup_of (G := E)
      (section12Tau2Primes M ∪ section12Tau3Primes M) K hKπ ?_
    intro p hpτ hpidx
    rcases hpτ with hpτ2 | hpτ3
    · have hidx_dvd : K.index ∣ (E₂.subgroupOf E).index :=
        Subgroup.index_dvd_of_le (show E₂.subgroupOf E ≤ K by exact le_sup_left)
      exact (hHallE2E.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpτ2
    · have hidx_dvd : K.index ∣ (E₃.subgroupOf E).index :=
        Subgroup.index_dvd_of_le (show E₃.subgroupOf E ≤ K by exact le_sup_right)
      exact (hHallE3.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpτ3
  refine ⟨sup_le hE2E hE3E, ?_⟩
  have hsub_eq : (E₂ ⊔ E₃).subgroupOf E = K :=
    Subgroup.subgroupOf_sup (A := E₂) (A' := E₃) (B := E) hE2E hE3E
  simpa [hsub_eq] using hKHall

private theorem CFSG.section12_ambientDerivedSubgroup_E_le_E2_sup_E3
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hnilE : Group.IsNilpotent (ambientDerivedSubgroup E)) :
    ambientDerivedSubgroup E ≤ E₂ ⊔ E₃ := by
  classical
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3⟩
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  have hE1E : section12HallSubgroupIn (section12Tau1Primes M) E₁ E :=
    section12_E1_hall_in_E (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      ⟨hE12E, hHallE12⟩ ⟨hE1E12, hHallE1⟩
  have hInfBot : E₁ ⊓ ambientDerivedSubgroup M = ⊥ :=
    section12_E1_inf_ambientDerivedSubgroup_M_eq_bot
      (M := M) (E₁₂ := E₁₂) (E₁ := E₁) ⟨hE1E12, hHallE1⟩
  have hDπ23 : IsPiSubgroup (G := E)
      (section12Tau2Primes M ∪ section12Tau3Primes M) (derivedSubgroup E) := by
    intro p hpD
    have hpE : p ∈ subgroupPrimeSet E :=
      hpD.trans (Subgroup.card_subgroup_dvd_card (derivedSubgroup E))
    have hpτ : p ∈
        section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M :=
      section12_prime_mem_tau_union_of_mem_E hM hcomp hpE
    rcases hpτ with hpτ12 | hpτ3
    · rcases hpτ12 with hpτ1 | hpτ2
      · exact False.elim
          (section12_no_tau1_prime_dvd_derivedSubgroup
            (M := M) (H := E) (E₁ := E₁) hcomp.2.1 hE1E hInfBot hnilE hpτ1 hpD)
      · exact Or.inl hpτ2
    · exact Or.inr hpτ3
  have hE3normIn : section10NormalIn E₃ E :=
    (lemma_12_1_b (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      (E₃ := E₃) hM
      ⟨hcomp, ⟨hE12E, hHallE12⟩, ⟨hE1E12, hHallE1⟩, hE2,
        ⟨hE3E, hHallE3⟩⟩).2
  have hK23HallIn : section12HallSubgroupIn
      (section12Tau2Primes M ∪ section12Tau3Primes M) (E₂ ⊔ E₃) E :=
    section12_E2_sup_E3_hall_in_E
      (M := M) (E := E) (E₁₂ := E₁₂) (E₂ := E₂) (E₃ := E₃)
      ⟨hE12E, hHallE12⟩ hE2 ⟨hE3E, hHallE3⟩ hE3normIn
  rcases hK23HallIn with ⟨hK23E, hHallK23⟩
  have hD_le_K23sub : derivedSubgroup E ≤ (E₂ ⊔ E₃).subgroupOf E :=
    section12_normal_piSubgroup_le_hall (K := derivedSubgroup E)
      (L := (E₂ ⊔ E₃).subgroupOf E) hDπ23 hHallK23
  intro x hx
  have hxE : x ∈ E := section12_ambientDerivedSubgroup_le hx
  let xE : E := ⟨x, hxE⟩
  have hxD : xE ∈ derivedSubgroup E := by
    have hxsub : xE ∈ (ambientDerivedSubgroup E).subgroupOf E := hx
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hxsub
  exact hD_le_K23sub hxD

omit [Finite G] [IsMinCE G] in
set_option maxHeartbeats 800000 in
public theorem CFSG.section12_sylow_inf_center_eq_bot_of_le_commutator
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (P : Sylow p R) (hPcyc : IsCyclic (P : Subgroup R))
    (hPcomm : (P : Subgroup R) ≤ commutator R) :
    (P : Subgroup R) ⊓ Subgroup.center R = ⊥ := by
  classical
  let PE : Subgroup R := P
  by_cases hPbot : PE = ⊥
  · simp [PE, hPbot]
  let Nrm : Subgroup R := Subgroup.normalizer (PE : Set R)
  let PN : Sylow p Nrm := P.subtype (by simpa [PE, Nrm] using P.le_normalizer)
  let Ploc : Subgroup Nrm := PE.subgroupOf Nrm
  have hPN_eq : (PN : Subgroup Nrm) = Ploc := rfl
  have hPN_norm : (PN : Subgroup Nrm).Normal := by
    simpa [PE, Nrm, PN] using P.normal_in_normalizer
  have : Ploc.Normal := by
    rw [← hPN_eq]
    exact hPN_norm
  have hPloc_cyc : IsCyclic Ploc := by
    let : IsCyclic PE := hPcyc
    let e : Ploc ≃* PE :=
      Subgroup.subgroupOfEquivOfLe (H := PE) (K := Nrm) (by
        simpa [PE, Nrm] using P.le_normalizer)
    exact e.isCyclic.2 inferInstance
  have hPN_cyc : IsCyclic (PN : Subgroup Nrm) := by
    rw [hPN_eq]
    exact hPloc_cyc
  let : IsCyclic (PN : Subgroup Nrm) := hPN_cyc
  have : (PN : Subgroup Nrm).Normal := hPN_norm
  have hcopPloc : Nat.Coprime (Nat.card Ploc) Ploc.index := by
    rw [← hPN_eq]
    exact PN.card_coprime_index
  obtain ⟨K, hKcomp⟩ :=
    Subgroup.exists_left_complement'_of_coprime (N := Ploc) hcopPloc
  have hcomm_or : ⁅K, Ploc⁆ = ⊥ ∨ ⁅K, Ploc⁆ = Ploc := by
    simpa [Ploc, hPN_eq] using
      Sylow.commutator_eq_bot_or_commutator_eq_self (P := PN) (K := K)
        (by simpa [hPN_eq] using hKcomp)
  have hcomm_self : ⁅K, Ploc⁆ = Ploc := by
    rcases hcomm_or with hcomm_bot | hcomm_self
    · exfalso
      have hK_le_cent : K ≤ Subgroup.centralizer (Ploc : Set Nrm) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm_bot
      have hPloc_comm : IsMulCommutative Ploc := by
        let : IsCyclic Ploc := hPloc_cyc
        infer_instance
      have hPloc_le_cent : Ploc ≤ Subgroup.centralizer (Ploc : Set Nrm) :=
        (Subgroup.le_centralizer_iff_isMulCommutative (K := Ploc)).2 hPloc_comm
      have htop_le_cent : (⊤ : Subgroup Nrm) ≤ Subgroup.centralizer (Ploc : Set Nrm) := by
        rw [← hKcomp.sup_eq_top]
        exact sup_le hK_le_cent hPloc_le_cent
      have hNrm_le_cent : Nrm ≤ Subgroup.centralizer (PE : Set R) := by
        intro n hn
        rw [Subgroup.mem_centralizer_iff]
        intro a haPE
        let nN : Nrm := ⟨n, hn⟩
        let aN : Nrm := ⟨a, by simpa [PE, Nrm] using P.le_normalizer haPE⟩
        have haPloc : aN ∈ Ploc := by
          change a ∈ PE
          exact haPE
        have hncent : nN ∈ Subgroup.centralizer (Ploc : Set Nrm) := htop_le_cent trivial
        have hcomm : aN * nN = nN * aN :=
          Subgroup.mem_centralizer_iff.mp hncent aN haPloc
        exact congrArg Subtype.val hcomm
      let : IsCyclic PE := by simpa [PE] using hPcyc
      let : CommGroup PE := IsCyclic.commGroup
      let tr := MonoidHom.transferSylow P hNrm_le_cent
      have hP_le_ker : PE ≤ tr.ker := by
        intro x hx
        exact Abelianization.commutator_subset_ker tr (hPcomm hx)
      have htr_comp : tr.ker.IsComplement' PE :=
        MonoidHom.ker_transferSylow_isComplement' P hNrm_le_cent
      have hP_le_bot : PE ≤ ⊥ := by
        intro x hx
        have hxinf : x ∈ tr.ker ⊓ PE := ⟨hP_le_ker hx, hx⟩
        have hinf : tr.ker ⊓ PE = ⊥ := (disjoint_iff).1 htr_comp.disjoint
        simpa [hinf] using hxinf
      exact hPbot (le_bot_iff.mp hP_le_bot)
    · exact hcomm_self
  have hKnormPloc : K ≤ Subgroup.normalizer (Ploc : Set Nrm) := by
    intro k _hk
    simp [Ploc.normalizer_eq_top]
  have : Subgroup.Normalizes K Ploc := ⟨hKnormPloc⟩
  have hcomm_self' : ⁅Ploc, K⁆ = Ploc := by
    simpa [Subgroup.commutator_comm] using hcomm_self
  have hcomm_map :
      (commutatorAction (A := K) (G := Ploc)).map Ploc.subtype = Ploc := by
    simpa [hcomm_self'] using
      commutatorAction_subgroup_conj_map_eq_commutator Ploc K hKnormPloc
  have hcomm_top : commutatorAction (A := K) (G := Ploc) = ⊤ := by
    apply eq_top_iff.2
    intro x _hx
    have hxmap : (x : Nrm) ∈ (commutatorAction (A := K) (G := Ploc)).map Ploc.subtype := by
      rw [hcomm_map]
      exact x.2
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
    have hy_eq_x : y = x := Ploc.subtype_injective hyx
    simpa [hy_eq_x] using hy
  have hPloc_comm : IsMulCommutative Ploc := by
    let : IsCyclic Ploc := hPloc_cyc
    infer_instance
  have hPloc_solv : Group.IsSolvable Ploc := by
    let : IsMulCommutative Ploc := hPloc_comm
    infer_instance
  have hcopKPloc : Nat.Coprime (Nat.card K) (Nat.card Ploc) := by
    simpa [hKcomp.index_eq_card] using hcopPloc.symm
  have hcompl : IsCompl (fixedPointSubgroup K Ploc) (commutatorAction (A := K) (G := Ploc)) :=
    proposition_1_6_d (G := Ploc) (A := K) hPloc_solv hcopKPloc hPloc_comm
  have hfixed_bot : fixedPointSubgroup K Ploc = ⊥ := by
    apply eq_bot_iff.2
    intro x hx
    have hxinf : x ∈ fixedPointSubgroup K Ploc ⊓ commutatorAction (A := K) (G := Ploc) := by
      exact ⟨hx, by simp [hcomm_top]⟩
    have hinf : fixedPointSubgroup K Ploc ⊓ commutatorAction (A := K) (G := Ploc) = ⊥ :=
      (disjoint_iff).1 hcompl.disjoint
    simpa [hinf] using hxinf
  apply le_bot_iff.mp
  intro x hx
  let xN : Nrm := ⟨x, by simpa [PE, Nrm] using P.le_normalizer hx.1⟩
  let xP : Ploc := ⟨xN, by
    change x ∈ PE
    exact hx.1⟩
  have hxfix : xP ∈ fixedPointSubgroup K Ploc := by
    rw [FixedPoints.mem_subgroup]
    intro k
    ext
    change ((k : Nrm) : R) * x * ((k : Nrm) : R)⁻¹ = x
    have hxcenter : x ∈ Subgroup.center R := hx.2
    have hcomm : ((k : Nrm) : R) * x = x * ((k : Nrm) : R) :=
      (Subgroup.mem_center_iff.mp hxcenter) ((k : Nrm) : R)
    calc
      ((k : Nrm) : R) * x * ((k : Nrm) : R)⁻¹ =
          (x * ((k : Nrm) : R)) * ((k : Nrm) : R)⁻¹ := by rw [hcomm]
      _ = x := by simp [mul_assoc]
  have hxbot : xP ∈ (⊥ : Subgroup Ploc) := by
    simpa [hfixed_bot] using hxfix
  have hxoneP : xP = 1 := by simpa using hxbot
  have hxone : x = 1 := by
    simpa [xP, xN] using congrArg (fun y : Ploc => ((y : Nrm) : R)) hxoneP
  simp [hxone]

/-- Lemma 12.1(e). -/
public theorem CFSG.lemma_12_1_e
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    E = E₁ ⊔ E₂ ⊔ E₃ ∧ E₁₂ = E₁ ⊔ E₂ ∧
      section10NormalIn (E₂ ⊔ E₃) E ∧ section10NormalIn E₂ E₁₂ := by
  classical
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3⟩
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  rcases hE2 with ⟨hE2E12, hHallE2⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, ⟨hE12E, hHallE12⟩, ⟨hE1E12, hHallE1⟩, ⟨hE2E12, hHallE2⟩,
      ⟨hE3E, hHallE3⟩⟩
  have hnilE : Group.IsNilpotent (ambientDerivedSubgroup E) :=
    lemma_12_1_a (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      (E₃ := E₃) hM hEdata
  have hE12eq : E₁₂ = E₁ ⊔ E₂ :=
    section12_E12_eq_E1_sup_E2
      (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      ⟨hE12E, hHallE12⟩ ⟨hE1E12, hHallE1⟩ ⟨hE2E12, hHallE2⟩
  have hEeqE12E3 : E = E₁₂ ⊔ E₃ :=
    section12_E12_sup_E3_eq_E
      (M := M) (E := E) (E₁₂ := E₁₂) (E₃ := E₃)
      hM hcomp ⟨hE12E, hHallE12⟩ ⟨hE3E, hHallE3⟩
  have hEeq : E = E₁ ⊔ E₂ ⊔ E₃ := by
    calc
      E = E₁₂ ⊔ E₃ := hEeqE12E3
      _ = E₁ ⊔ E₂ ⊔ E₃ := by rw [hE12eq]
  have hK23E : E₂ ⊔ E₃ ≤ E := sup_le (hE2E12.trans hE12E) hE3E
  have hK23norm : section10NormalIn (E₂ ⊔ E₃) E :=
    section12_normalIn_of_ambientDerivedSubgroup_le hK23E
      (section12_ambientDerivedSubgroup_E_le_E2_sup_E3
        (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        hM hEdata hnilE)
  have hE2norm : section10NormalIn E₂ E₁₂ :=
    section12_normalIn_of_ambientDerivedSubgroup_le hE2E12
      (section12_ambientDerivedSubgroup_E12_le_E2
        (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        hM hEdata hnilE)
  exact ⟨hEeq, hE12eq, hK23norm, hE2norm⟩

end Section12
