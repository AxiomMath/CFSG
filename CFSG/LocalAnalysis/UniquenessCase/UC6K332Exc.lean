module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Syl
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Milestones.ASVolI.I2
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate3139
public import Certificates.Certificate8020
import CFSG.Sporadic.J2
import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.RankThree.PartTwo.Sec4 (IsoGTwoPrime)

@[expose] def K332Exclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    ∀ S : Subgroup G, IsSylowOf 3 S ⊤ →
    ∀ Z : Subgroup G, Z ≤ S → Nat.card Z = 3 → IsWeaklyClosedIn Z S →
    Disjoint (Z.subgroupOf S) (commutator ↥S) →
      ¬ IsoGTwoPrime (Subgroup.normalClosure (Z : Set G)) ∧
        ¬ Nonempty (Subgroup.normalClosure (Z : Set G) ≃* CFSG.Blueprint.NativeSporadic.J2)

private theorem map_mem_commutator {A B : Type*} [Group A] [Group B] (f : A →* B) {a : A}
    (ha : a ∈ commutator A) : f a ∈ commutator B := by
  have h : (commutator A).map f ≤ commutator B := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  exact h ⟨a, ha, rfl⟩

theorem sylowCenterLeCommutator_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : SylowCenterLeCommutator X) : SylowCenterLeCommutator Y := by
  intro T x hxc hx3
  let T' : Sylow 3 X := T.comapOfInjective e.toMonoidHom e.injective
    fun y _ => ⟨e.symm y, e.apply_symm_apply y⟩
  let ψ : ↥(T' : Subgroup X) →* ↥(T : Subgroup Y) :=
    e.toMonoidHom.subgroupComap (T : Subgroup Y)
  let x' : ↥(T' : Subgroup X) := ⟨e.symm (x : Y), by
    show e (e.symm (x : Y)) ∈ (T : Subgroup Y)
    rw [e.apply_symm_apply]
    exact x.2⟩
  have hψx' : ψ x' = x := Subtype.ext (e.apply_symm_apply (x : Y))
  have hx'c : x' ∈ Subgroup.center ↥(T' : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : e (g : X) * (x : Y) = (x : Y) * e (g : X) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc (ψ g))
    apply Subtype.ext
    apply e.injective
    show e ((g : X) * e.symm (x : Y)) = e (e.symm (x : Y) * (g : X))
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact h1
  have hx'3 : x' ^ 3 = 1 := by
    apply Subtype.ext
    show (e.symm (x : Y)) ^ 3 = 1
    rw [← map_pow, show (x : Y) ^ 3 = 1 from congrArg Subtype.val hx3, map_one]
  have hcomm := map_mem_commutator ψ (h T' x' hx'c hx'3)
  rwa [hψx'] at hcomm

private theorem card_sylow_three_J2
    (T : Sylow 3 CFSG.Blueprint.NativeSporadic.J2) : Nat.card T = 3 ^ 3 := by
  have h0 : (604800 : ℕ) ≠ 0 := by norm_num
  have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization h0).1 (by norm_num : 3 ^ 3 ∣ 604800)
  have h2 : ¬ 4 ≤ (604800 : ℕ).factorization 3 := fun h => by
    have := (Nat.prime_three.pow_dvd_iff_le_factorization h0).2 h
    norm_num at this
  rw [Sylow.card_eq_multiplicity T, CFSG.Sporadic.J2.card_J2,
    show (604800 : ℕ).factorization 3 = 3 by omega]

theorem sylowCenterLeCommutator_J2 :
    SylowCenterLeCommutator CFSG.Blueprint.NativeSporadic.J2 := by
  intro T x hxc _
  have hcard : Nat.card (T : Subgroup CFSG.Blueprint.NativeSporadic.J2) = 3 ^ 3 :=
    card_sylow_three_J2 T
  have hnc : ¬ IsMulCommutative ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.J2) := by
    intro hcomm
    obtain ⟨a, b, -, -, -, hab, -, -, hP, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
    obtain ⟨T₀, hT₀⟩ := (IsPGroup.of_card hP).exists_le_sylow
    haveI : Finite (Sylow 3 CFSG.Blueprint.NativeSporadic.J2) := Sylow.finite_of_finiteIndex T
    have ha : a ∈ (T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2) :=
      hT₀ (Subgroup.subset_closure (Set.mem_insert _ _))
    have hb : b ∈ (T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2) :=
      hT₀ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    let φ := Sylow.equiv T₀ T
    have h1 : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ :=
      isMulCommutative_iff.mp hcomm _ _
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val (φ.injective h1)
    exact hab (commutatorElement_eq_one_iff_mul_comm.mpr h2)
  have hZ : Nat.card (Subgroup.center ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.J2)) = 3 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.card_center_of_nonabelian_card_p_cube hcard hnc
  exact center_le_commutator_of_card_center_eq_prime T.isPGroup' hnc hZ hxc

theorem sylowCenterLeCommutator_of_mulEquiv_J2
    {X : Type} [Group X] [Finite X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) : SylowCenterLeCommutator X := by
  obtain ⟨e⟩ := h
  exact sylowCenterLeCommutator_of_mulEquiv e.symm sylowCenterLeCommutator_J2

private theorem mem_conjugate_iff {G : Type} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem le_normalizer_of_isWeaklyClosedIn {G : Type} [Group G] {S Z : Subgroup G}
    (hZS : Z ≤ S) (hwc : IsWeaklyClosedIn Z S) : S ≤ Subgroup.normalizer (Z : Set G) := by
  intro s hs
  have hc : CFSG.conjugate Z s = Z := by
    apply hwc s
    intro x hx
    have hxS : s * x * s⁻¹ ∈ S := hZS (mem_conjugate_iff.mp hx)
    have e : x = s⁻¹ * (s * x * s⁻¹) * s := by group
    rw [e]
    exact S.mul_mem (S.mul_mem (S.inv_mem hs) hxS) hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← mem_conjugate_iff, hc]

private theorem le_centralizer_of_le_normalizer {G : Type} [Group G] [Finite G] {S Z : Subgroup G}
    (hSp : IsPGroup 3 S) (hZS : Z ≤ S) (hN : S ≤ Subgroup.normalizer (Z : Set G))
    (hcard : Nat.card Z = 3) : Z ≤ Subgroup.centralizer (S : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent S := hSp.isNilpotent
  have hZcard : Nat.card (Z.subgroupOf S) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv, hcard]
  have hnormal : (Z.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hne : Z.subgroupOf S ≠ ⊥ := by
    intro hbot
    have h1 := hZcard
    rw [hbot, Subgroup.card_bot] at h1
    omega
  set H : Subgroup ↥S := Z.subgroupOf S ⊓ Subgroup.center ↥S with hH
  have hinter : H ≠ ⊥ := by
    rw [hH]
    exact Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hdvd : Nat.card H ∣ 3 := by
    rw [hH, ← hZcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne1 : Nat.card H ≠ 1 := fun h1 => hinter ((Subgroup.card_eq_one).mp h1)
  have hcardinf : Nat.card H = Nat.card (Z.subgroupOf S) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · rw [h, hZcard]
  have heq : H = Z.subgroupOf S := by
    rw [hH]
    exact Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcardinf.symm)
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hz' : (⟨z, hZS hz⟩ : S) ∈ Z.subgroupOf S := Subgroup.mem_subgroupOf.mpr hz
  have hzc : (⟨z, hZS hz⟩ : S) ∈ Subgroup.center ↥S := by
    have hmem : (⟨z, hZS hz⟩ : S) ∈ H := by rw [heq]; exact hz'
    rw [hH] at hmem
    exact hmem.2
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨y, hy⟩)

theorem false_of_sylowCenterLeCommutator {G : Type} [Group G] [Finite G] {S Z H : Subgroup G}
    [H.Normal] (hS : IsSylowOf 3 S ⊤) (hZS : Z ≤ S) (hZH : Z ≤ H) (hZ : Nat.card Z = 3)
    (hwc : IsWeaklyClosedIn Z S) (hdisj : Disjoint (Z.subgroupOf S) (commutator ↥S))
    (h : SylowCenterLeCommutator ↥H) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSH : IsSylowOf 3 (S ⊓ H) H :=
    hS.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top (H := H)).ge
  obtain ⟨Q, hQ⟩ := hSH.exists_sylow_eq_subgroupOf
  have hZne : Z ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨x, hxZ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZne
  have hxne : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  have hx3 : x ^ 3 = 1 := by
    have h1 : orderOf x ∣ 3 := hZ ▸ Subgroup.orderOf_dvd_natCard Z hxZ
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hxS : x ∈ S := hZS hxZ
  have hxH : x ∈ H := hZH hxZ
  have hcent : Z ≤ Subgroup.centralizer (S : Set G) :=
    le_centralizer_of_le_normalizer hS.isPGroup hZS (le_normalizer_of_isWeaklyClosedIn hZS hwc) hZ
  have hQS : ∀ q : ↥(Q : Subgroup ↥H), (q : ↥H).1 ∈ S := fun q => by
    have hq : (q : ↥H) ∈ (S ⊓ H).subgroupOf H := by rw [← hQ]; exact q.2
    exact (Subgroup.mem_subgroupOf.mp hq).1
  let f : ↥(Q : Subgroup ↥H) →* ↥S :=
    ((H.subtype).comp (Q : Subgroup ↥H).subtype).codRestrict S hQS
  have hxQ : (⟨x, hxH⟩ : ↥H) ∈ (Q : Subgroup ↥H) := by
    rw [hQ]
    exact Subgroup.mem_subgroupOf.mpr ⟨hxS, hxH⟩
  let xQ : ↥(Q : Subgroup ↥H) := ⟨⟨x, hxH⟩, hxQ⟩
  have hxc : xQ ∈ Subgroup.center ↥(Q : Subgroup ↥H) := by
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent hxZ) _ (hQS q)))
  have hxQ3 : xQ ^ 3 = 1 := Subtype.ext (Subtype.ext hx3)
  have hcomm := map_mem_commutator f (h Q xQ hxc hxQ3)
  have hfx : f xQ = ⟨x, hxS⟩ := Subtype.ext rfl
  rw [hfx] at hcomm
  exact hxne (congrArg Subtype.val
    (Subgroup.disjoint_def.1 hdisj (Subgroup.mem_subgroupOf.mpr hxZ) hcomm))

theorem k332Exclusion_of_sylowG2
    (hG2 : ∀ (X : Type) [Group X] [Finite X], CFSG.RankThree.PartTwo.Sec4.IsoGTwoPrime X →
      SylowCenterLeCommutator X) : K332Exclusion := by
  intro G _ _ S hS Z hZS hZ3 hwc hdisj
  refine ⟨fun hiso => ?_, fun ⟨e⟩ => ?_⟩
  · exact false_of_sylowCenterLeCommutator hS hZS Subgroup.le_normalClosure hZ3 hwc hdisj
      (hG2 _ hiso)
  · exact false_of_sylowCenterLeCommutator hS hZS Subgroup.le_normalClosure hZ3 hwc hdisj
      (sylowCenterLeCommutator_of_mulEquiv_J2 ⟨e⟩)

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
