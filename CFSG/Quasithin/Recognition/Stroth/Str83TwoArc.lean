module

public import CFSG.Quasithin.Recognition.Stroth.Str86Frame
public import CFSG.Quasithin.Recognition.Stroth.Str83OrdersParts
public import CFSG.Quasithin.Recognition.Stroth.F112Moufang
public import CFSG.Quasithin.Background.F7E1

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]


private theorem ad_of_mem {L : Subgroup G} (x : ↥L) :
    oTwoQuotConj L ⟨(x : G), Subgroup.le_normalizer x.2⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [oTwoQuotConj_mk, MulAut.conj_apply]
    change (QuotientGroup.mk (⟨(x : G) * (y : G) * (x : G)⁻¹, _⟩ : ↥L) : oTwoQuot ↥L) =
      (QuotientGroup.mk x : oTwoQuot ↥L) * (QuotientGroup.mk y : oTwoQuot ↥L) *
        ((QuotientGroup.mk x : oTwoQuot ↥L))⁻¹
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1

theorem pCoreOf_le_K1_map {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤
      (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype := by
  let P : Subgroup G := L1 ⊔ bigB L1 L2 S
  let Q : Subgroup G := pCoreOf 2 P
  have hQleB : Q ≤ bigB L1 L2 S :=
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)).trans
      (le_sup_right : S ≤ bigB L1 L2 S)
  have hQleB' : (CFSG.pCore 2 ↥P).map P.subtype ≤ bigB L1 L2 S := by
    simpa [Q, CFSG.Open.pCoreOf] using hQleB
  have hQsub : (CFSG.pCore 2 ↥P) ≤
      ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf P := by
    intro x hx
    have h1 : (CFSG.pCore 2 ↥P).map P.subtype ≤
        (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) := by
      rw [f112_parabolic_inf_eq_bigB hF]
      exact hQleB'
    exact Subgroup.mem_subgroupOf.mpr (h1 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  have hleCore : (CFSG.pCore 2 ↥P) ≤ f112K1 L1 L2 S := by
    rw [f112K1]
    exact (Subgroup.normal_le_normalCore).mpr hQsub
  change (CFSG.pCore 2 ↥P).map P.subtype ≤ (f112K1 L1 L2 S).map P.subtype
  exact Subgroup.map_mono hleCore

theorem inf_K1_map_sup_eq_pCoreOf {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hL1 : IsSimpleGroup (oTwoQuot ↥L1))
    (hE : S = (S ⊓ L1) ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) :
    (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype ⊓ S =
      pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
  let P : Subgroup G := L1 ⊔ bigB L1 L2 S
  let Q : Subgroup G := pCoreOf 2 P
  let K1 : Subgroup ↥P := f112K1 L1 L2 S
  let K1g : Subgroup G := K1.map P.subtype
  have hK1gB : K1g ≤ bigB L1 L2 S := by
    have hK1le : K1 ≤ ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf P := by
      dsimp only [K1]
      exact Subgroup.normalCore_le _
    have hmap := Subgroup.map_mono (f := P.subtype) hK1le
    rw [Subgroup.map_subgroupOf_eq_of_le
      (inf_le_left : ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)) ≤ P),
      f112_parabolic_inf_eq_bigB hF] at hmap
    exact hmap
  have hQleB : Q ≤ bigB L1 L2 S :=
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)).trans
      (le_sup_right : S ≤ bigB L1 L2 S)
  have hQleK1 : Q ≤ K1g := by
    dsimp only [K1g, Q, P]
    exact pCoreOf_le_K1_map hF
  have hL1NQ : L1 ≤ Subgroup.normalizer (Q : Set G) :=
    (le_sup_left : L1 ≤ P).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hQN : Q ≤ Subgroup.normalizer (L1 : Set G) :=
    hQleB.trans (bigB_le_normalizer_of_hyp111 hF.1)
  have hded : (K1g ⊓ L1) ⊔ Q = K1g ⊓ (L1 ⊔ Q) := by
    refine le_antisymm ?_ ?_
    · exact sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
        (le_inf hQleK1 le_sup_right)
    · intro x hx
      obtain ⟨hxK, hxLQ⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨l, hl, q, hq, rfl⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes hQN).mp hxLQ
      have hqK : q ∈ K1g := hQleK1 hq
      have hlK : l ∈ K1g := by
        have h1 : l = (l * q) * q⁻¹ := by group
        rw [h1]
        exact K1g.mul_mem hxK (K1g.inv_mem hqK)
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hlK, hl⟩) hq
  have hK1L : K1g ⊓ L1 = pCoreOf 2 L1 := by
    dsimp only [K1g]
    rw [inf_comm]
    exact f112_inf_map_K1_eq_pCoreOf hF hL1
  have hSQ : S ≤ L1 ⊔ Q := by
    rw [hE]
    exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hQS : Q ≤ S := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  refine le_antisymm ?_ (le_inf hQleK1 hQS)
  intro x hx
  have hxK : x ∈ K1g := hx.1
  have hxLQ : x ∈ L1 ⊔ Q := hSQ hx.2
  have hx' : x ∈ K1g ⊓ (L1 ⊔ Q) := Subgroup.mem_inf.mpr ⟨hxK, hxLQ⟩
  rw [← hded, hK1L] at hx'
  exact (sup_le (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1) le_rfl) hx'

end CFSG.Quasithin.Stroth

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_K2_map {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤
      (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype := by
  let P : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q : Subgroup G := pCoreOf 2 P
  have hQleB : Q ≤ bigB L1 L2 S :=
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)).trans
      (le_sup_right : S ≤ bigB L1 L2 S)
  have hQleB' : (CFSG.pCore 2 ↥P).map P.subtype ≤ bigB L1 L2 S := by
    simpa [Q, CFSG.Open.pCoreOf] using hQleB
  have hQsub : (CFSG.pCore 2 ↥P) ≤
      ((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)).subgroupOf P := by
    intro x hx
    have h1 : (CFSG.pCore 2 ↥P).map P.subtype ≤
        (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) := by
      rw [inf_comm, f112_parabolic_inf_eq_bigB hF]
      exact hQleB'
    exact Subgroup.mem_subgroupOf.mpr (h1 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  have hleCore : (CFSG.pCore 2 ↥P) ≤ f112K2 L1 L2 S := by
    rw [f112K2]
    exact (Subgroup.normal_le_normalCore).mpr hQsub
  change (CFSG.pCore 2 ↥P).map P.subtype ≤ (f112K2 L1 L2 S).map P.subtype
  exact Subgroup.map_mono hleCore

theorem inf_K2_map_sup_eq_pCoreOf {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hL2 : IsSimpleGroup (oTwoQuot ↥L2))
    (hE : S = (S ⊓ L2) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) :
    (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype ⊓ S =
      pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
  let P : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q : Subgroup G := pCoreOf 2 P
  let K1 : Subgroup ↥P := f112K2 L1 L2 S
  let K1g : Subgroup G := K1.map P.subtype
  have hK1gB : K1g ≤ bigB L1 L2 S := by
    have hK1le : K1 ≤ ((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)).subgroupOf P := by
      dsimp only [K1]
      exact Subgroup.normalCore_le _
    have hmap := Subgroup.map_mono (f := P.subtype) hK1le
    have hinf : (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
      rw [inf_comm]
      exact f112_parabolic_inf_eq_bigB hF
    rw [Subgroup.map_subgroupOf_eq_of_le
      (inf_le_left : ((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)) ≤ P), hinf] at hmap
    exact hmap
  have hQleB : Q ≤ bigB L1 L2 S :=
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)).trans
      (le_sup_right : S ≤ bigB L1 L2 S)
  have hQleK1 : Q ≤ K1g := by
    dsimp only [K1g, Q, P]
    exact pCoreOf_le_K2_map hF
  have hL2NQ : L2 ≤ Subgroup.normalizer (Q : Set G) :=
    (le_sup_left : L2 ≤ P).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hQN : Q ≤ Subgroup.normalizer (L2 : Set G) := by
    have h := bigB_le_normalizer_of_hyp111 hF.1.symm
    exact hQleB.trans (by simpa [bigB_comm] using h)
  have hded : (K1g ⊓ L2) ⊔ Q = K1g ⊓ (L2 ⊔ Q) := by
    refine le_antisymm ?_ ?_
    · exact sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
        (le_inf hQleK1 le_sup_right)
    · intro x hx
      obtain ⟨hxK, hxLQ⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨l, hl, q, hq, rfl⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes hQN).mp hxLQ
      have hqK : q ∈ K1g := hQleK1 hq
      have hlK : l ∈ K1g := by
        have h1 : l = (l * q) * q⁻¹ := by group
        rw [h1]
        exact K1g.mul_mem hxK (K1g.inv_mem hqK)
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hlK, hl⟩) hq
  have hK1L : K1g ⊓ L2 = pCoreOf 2 L2 := by
    dsimp only [K1g]
    rw [inf_comm]
    exact f112_inf_map_K2_eq_pCoreOf hF hL2
  have hSQ : S ≤ L2 ⊔ Q := by
    rw [hE]
    exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hQS : Q ≤ S := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)
  refine le_antisymm ?_ (le_inf hQleK1 hQS)
  intro x hx
  have hxK : x ∈ K1g := hx.1
  have hxLQ : x ∈ L2 ⊔ Q := hSQ hx.2
  have hx' : x ∈ K1g ⊓ (L2 ⊔ Q) := Subgroup.mem_inf.mpr ⟨hxK, hxLQ⟩
  rw [← hded, hK1L] at hx'
  have hO : pCoreOf 2 L2 ≤ Q := by
    simpa [Q, P, bigB_comm] using
      (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm)
  exact (sup_le hO le_rfl) hx'

namespace Rq

theorem mem_pCoreOf_of_two_arc_left {L1 L2 S : Subgroup G}
    {n₀ m₀ k₀ : ℕ} (hF : F112HypW L1 L2 S) (hBT1 : BenderType (oTwoQuot ↥L1) n₀ m₀ k₀)
    (hE : S = (S ⊓ L1) ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
    {t g : G} (hg : g ∈ L1 ⊔ bigB L1 L2 S) (hgB : g ∉ bigB L1 L2 S)
    (ht : t ∈ bigB L1 L2 S) (htg : g⁻¹ * t * g ∈ bigB L1 L2 S) (h2 : ∃ k, orderOf t = 2 ^ k) :
    t ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
  classical
  let P : Subgroup G := L1 ⊔ bigB L1 L2 S
  let B : Subgroup G := bigB L1 L2 S
  let Q1 : Subgroup G := pCoreOf 2 P
  let K1 : Subgroup ↥P := f112K1 L1 L2 S
  let K1g : Subgroup G := K1.map P.subtype
  have hSimple1 : IsSimpleGroup (oTwoQuot ↥L1) := hBT1.isSimple
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hSylP : IsSylowTwoOf S P := f112_isSylowTwoOf_P1 hF
  have hQ1leK1g : Q1 ≤ K1g := pCoreOf_le_K1_map hF
  have hK1gB : K1g ≤ B := by
    have hK1le : K1 ≤ ((L1 ⊔ B) ⊓ (L2 ⊔ B)).subgroupOf P := by
      dsimp only [K1]
      exact Subgroup.normalCore_le _
    have hmap := Subgroup.map_mono (f := P.subtype) hK1le
    rw [Subgroup.map_subgroupOf_eq_of_le
      (inf_le_left : ((L1 ⊔ B) ⊓ (L2 ⊔ B)) ≤ P),
      f112_parabolic_inf_eq_bigB hF] at hmap
    exact hmap
  have hS_le : S ≤ L1 ⊔ K1g := by
    rw [hE]
    exact sup_le (inf_le_right.trans le_sup_left) (hQ1leK1g.trans le_sup_right)
  have hQ1leS : Q1 ≤ S := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hSylP
  have hK1S : K1g ⊓ S = Q1 := by
    simpa [K1g, Q1, P, B] using inf_K1_map_sup_eq_pCoreOf hF hSimple1 hE
  let R : Subgroup G := L1 ⊔ K1g
  have hRleP : R ≤ P := sup_le le_sup_left (hK1gB.trans le_sup_right)
  let N : Subgroup ↥P := R.subgroupOf P
  have hNindex : Odd N.index := by
    have h1 : N.index = R.relIndex P := by
      dsimp only [N]
      rw [show N.index = (R.subgroupOf P).relIndex (P.subgroupOf P) from by
        rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right]]
      exact Subgroup.relIndex_subgroupOf (H := R) (K := P) (L := P) le_rfl
    have h2 : R.relIndex P ∣ S.relIndex P :=
      Subgroup.relIndex_dvd_of_le_left P hS_le
    have h3 : Odd (S.relIndex P) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hSylP
    rw [h1]
    exact Odd.of_dvd_nat h3 h2
  have htP : t ∈ P := (le_sup_right : B ≤ P) ht
  let tP : ↥P := ⟨t, htP⟩
  obtain ⟨k, hk⟩ := h2
  have hkP : orderOf tP = 2 ^ k := by
    simpa [tP] using hk
  have hP2 : IsPGroup 2 (Subgroup.zpowers tP) := by
    rw [isPGroup_iff_exists_orderOf_dvd_pow]
    refine ⟨k, fun x => ?_⟩
    have hx : (x : ↥P) ∈ Subgroup.zpowers tP := x.2
    have hxdvd : orderOf (x : ↥P) ∣ 2 ^ k :=
      (orderOf_dvd_of_mem_zpowers hx).trans (by rw [hkP])
    rw [← Subgroup.orderOf_coe x]
    exact hxdvd
  have hPN : P ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1)
  have hK1g_normal : P ≤ Subgroup.normalizer (K1g : Set G) := by
    have htop : Subgroup.normalizer (K1 : Set ↥P) = ⊤ :=
      eq_top_iff.mpr (Subgroup.le_normalizer_of_normal)
    have h := Subgroup.le_normalizer_map (f := P.subtype) (H := K1)
    rw [htop, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  have hRnormal : P ≤ Subgroup.normalizer (R : Set G) := by
    dsimp only [R]
    exact F1.le_normalizer_sup hPN hK1g_normal
  have hNnormal : N.Normal := by
    dsimp only [N]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRleP).mpr hRnormal
  haveI : N.Normal := hNnormal
  have hleN : Subgroup.zpowers tP ≤ N :=
    CFSG.GH74.Uniqueness.SU.K.KI8.le_of_isPGroup_of_odd_index hNindex hP2
  have htR : t ∈ R := by
    have h1 : tP ∈ N := hleN (Subgroup.mem_zpowers tP)
    exact Subgroup.mem_subgroupOf.mp h1
  have hK1gN : K1g ≤ Subgroup.normalizer (L1 : Set G) :=
    hK1gB.trans (bigB_le_normalizer_of_hyp111 hF.1)
  obtain ⟨l, hlL, kk, hkK, hlk⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hK1gN).mp (by simpa [R] using htR)
  have htB : t ∈ B := ht
  have hkkK1g : kk ∈ K1g := hkK
  have hkkB : kk ∈ B := hK1gB hkK
  have hlB : l ∈ B := by
    have h1 : l = t * kk⁻¹ := by rw [hlk]; group
    rw [h1]
    exact B.mul_mem htB (B.inv_mem hkkB)
  have hB1l : l ∈ borelOf L1 S := by
    have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
    rw [← F1.inf_bigB_eq_borelOf hR]
    exact Subgroup.mem_inf.mpr ⟨hlL, hlB⟩
  obtain ⟨l0, hl0L, b0, hb0B, hgl0b0⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes
      (show B ≤ Subgroup.normalizer (L1 : Set G) from bigB_le_normalizer_of_hyp111 hF.1)).mp
      (by simpa [P] using hg)
  have hl0B1 : l0 ∉ borelOf L1 S := by
    intro hl0B1
    apply hgB
    rw [hgl0b0]
    exact B.mul_mem (by
      have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
      exact (((F1.inf_bigB_eq_borelOf hR).ge).trans inf_le_right) hl0B1) hb0B
  have hglB : g⁻¹ * l * g ∈ B := by
    have hgk : g⁻¹ * kk * g ∈ K1g := by
      obtain ⟨kP, hkPmem, hkPeq⟩ := Subgroup.mem_map.mp hkK
      let gP : ↥P := ⟨g, hg⟩
      have hconj : gP⁻¹ * kP * gP ∈ K1 := by
        simpa using (f112K1_normal L1 L2 S).conj_mem kP hkPmem gP⁻¹
      refine Subgroup.mem_map.mpr ⟨gP⁻¹ * kP * gP, hconj, ?_⟩
      simpa [gP, hkPeq]
    have h1 : g⁻¹ * l * g = (g⁻¹ * t * g) * (g⁻¹ * kk * g)⁻¹ := by
      rw [hlk]; group
    rw [h1]
    exact B.mul_mem htg (B.inv_mem (hK1gB hgk))
  have hconjL1 : l0⁻¹ * l * l0 ∈ L1 :=
    L1.mul_mem (L1.mul_mem (L1.inv_mem hl0L) hlL) hl0L
  have hconjB : b0⁻¹ * (l0⁻¹ * l * l0) * b0 ∈ B := by
    have h1 : b0⁻¹ * (l0⁻¹ * l * l0) * b0 = g⁻¹ * l * g := by
      rw [hgl0b0]; group
    rw [h1]
    exact hglB
  have hb0N : b0 ∈ Subgroup.normalizer (L1 : Set G) :=
    (bigB_le_normalizer_of_hyp111 hF.1) hb0B
  have hconjL : b0⁻¹ * (l0⁻¹ * l * l0) * b0 ∈ L1 := by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (L1 : Set G)).inv_mem hb0N) (l0⁻¹ * l * l0)).mp hconjL1
    simpa using h
  have hconjB1 : b0⁻¹ * (l0⁻¹ * l * l0) * b0 ∈ borelOf L1 S := by
    rw [← F1.inf_bigB_eq_borelOf hR]
    exact Subgroup.mem_inf.mpr ⟨hconjL, hconjB⟩
  have hB1N : B ≤ Subgroup.normalizer (borelOf L1 S : Set G) :=
    (F1.bigB_le_normalizer_borelOf hR).1
  have hb0NB1 : b0 ∈ Subgroup.normalizer (borelOf L1 S : Set G) := hB1N hb0B
  have hconjB1' : l0⁻¹ * l * l0 ∈ borelOf L1 S := by
    have hconjB1'' : b0⁻¹ * (l0⁻¹ * l * l0) * b0⁻¹⁻¹ ∈ borelOf L1 S := by
      simpa using hconjB1
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (borelOf L1 S : Set G)).inv_mem hb0NB1)
      (l0⁻¹ * l * l0)).mpr hconjB1''
    simpa using h
  let K : Type := oTwoQuot ↥L1
  let π : ↥L1 →* K := QuotientGroup.mk' (pCore 2 ↥L1)
  let Qimg : Subgroup K := ((S ⊓ L1).subgroupOf L1).map π
  have hmapB := F1.map_borelOf_eq_normalizer hF.1.h1.sylow
  obtain ⟨hQimg2, hQimgodd, hMmap⟩ := hmapB
  let Qsyl : Sylow 2 K := hQimg2.toSylow hQimgodd
  have hQsyl : (Qsyl : Subgroup K) = Qimg := IsPGroup.toSylow_coe hQimg2 hQimgodd
  obtain ⟨t0, hc⟩ := hBT1.exists_benderCore Qsyl
  have hM : borel (Qsyl : Subgroup K) = ((borelOf L1 S).subgroupOf L1).map π := by
    rw [CFSG.GH74.Uniqueness.Bender.borel, hQsyl, ← hMmap]
  let lbar : K := π ⟨l, hlL⟩
  let x : K := π ⟨l0, hl0L⟩
  have hlbarM : lbar ∈ borel (Qsyl : Subgroup K) := by
    rw [hM]
    exact Subgroup.mem_map.mpr ⟨⟨l, hlL⟩, Subgroup.mem_subgroupOf.mpr hB1l, rfl⟩
  have hxconj : x⁻¹ * lbar * x = π ⟨l0⁻¹ * l * l0, hconjL1⟩ := by
    dsimp only [x, lbar]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hxconjM : x⁻¹ * lbar * x ∈ borel (Qsyl : Subgroup K) := by
    rw [hxconj, hM]
    exact Subgroup.mem_map.mpr
      ⟨⟨l0⁻¹ * l * l0, hconjL1⟩, Subgroup.mem_subgroupOf.mpr hconjB1', rfl⟩
  have hxNotM : x ∉ borel (Qsyl : Subgroup K) := by
    intro hx
    rw [hM] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyB1 : (y : G) ∈ borelOf L1 S := Subgroup.mem_subgroupOf.mp hy
    have hyx' : π y = π ⟨l0, hl0L⟩ := hyx
    have hker : π (y * ⟨l0, hl0L⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hyx']
      simp
    have hmem : (y * ⟨l0, hl0L⟩⁻¹ : ↥L1) ∈ pCore 2 ↥L1 := by
      rw [← QuotientGroup.ker_mk' (pCore 2 ↥L1)]
      exact MonoidHom.mem_ker.mpr hker
    have hmemO : ((y : G) * l0⁻¹) ∈ pCoreOf 2 L1 :=
      (F1.mem_pCore_iff_coe (y * ⟨l0, hl0L⟩⁻¹)).mp hmem
    have hOleB1 : pCoreOf 2 L1 ≤ borelOf L1 S :=
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow).trans
        (F1.sylow_le_borelOf L1 S)
    have hl0B1' : l0 ∈ borelOf L1 S := by
      have h1 : l0 = ((y : G) * l0⁻¹)⁻¹ * (y : G) := by group
      rw [h1]
      exact (borelOf L1 S).mul_mem ((borelOf L1 S).inv_mem (hOleB1 hmemO)) hyB1
    exact hl0B1 hl0B1'
  have hAdkk : oTwoQuotConj L1 ⟨kk, hPN ((le_sup_right : B ≤ P) (hK1gB hkK))⟩ = 1 := by
    obtain ⟨kP, hkP, hkPeq⟩ := Subgroup.mem_map.mp hkK
    have hkkK1 : (⟨kk, (le_sup_right : B ≤ P) (hK1gB hkK)⟩ : ↥P) ∈ K1 := by
      have h : (⟨kk, (le_sup_right : B ≤ P) (hK1gB hkK)⟩ : ↥P) = kP := Subtype.ext hkPeq.symm
      rwa [h]
    rw [oTwoQuotConj_eq_one_iff]
    intro l' hl'
    have hc' := f112_kernel_centralizes_of_isSimpleGroup hF hSimple1 kk
      (Subgroup.mem_map.mpr
        ⟨⟨kk, (le_sup_right : B ≤ P) (hK1gB hkK)⟩, hkkK1, rfl⟩) l' hl'
    have hN : L1 ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L1
    have hconj := (Subgroup.mem_normalizer_iff.mp (hN (L1.inv_mem hl')) _).mp hc'
    convert hconj using 2 <;> group
  have hAdt : oTwoQuotConj L1 ⟨t, hPN htP⟩ =
      oTwoQuotConj L1 ⟨l, hPN ((le_sup_left : L1 ≤ P) hlL)⟩ := by
    have ht_eq : (⟨t, hPN htP⟩ : ↥(Subgroup.normalizer (L1 : Set G))) =
        ⟨l, hPN ((le_sup_left : L1 ≤ P) hlL)⟩ *
          ⟨kk, hPN ((le_sup_right : B ≤ P) (hK1gB hkK))⟩ := by
      apply Subtype.ext
      exact hlk
    rw [ht_eq, map_mul, hAdkk, mul_one]
  have hAdl : oTwoQuotConj L1 ⟨l, hPN ((le_sup_left : L1 ≤ P) hlL)⟩ =
      MulAut.conj lbar := by
    change oTwoQuotConj L1 ⟨l, _⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L1) (⟨l, hlL⟩ : ↥L1))
    simpa using ad_of_mem (L := L1) (x := ⟨l, hlL⟩)
  have htNorder : orderOf (⟨t, hPN htP⟩ : ↥(Subgroup.normalizer (L1 : Set G))) = 2 ^ k := by
    simpa using hk
  have hpow : (oTwoQuotConj L1 ⟨t, hPN htP⟩) ^ (2 ^ k) = 1 := by
    rw [← htNorder, ← map_pow, pow_orderOf_eq_one, map_one]
  have hconjpow : (MulAut.conj lbar) ^ (2 ^ k) = 1 := by
    rw [← hAdl, ← hAdt]
    exact hpow
  have hlbarpow : lbar ^ (2 ^ k) = 1 := by
    have hcenter : lbar ^ (2 ^ k) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hconjpow' : MulAut.conj (lbar ^ (2 ^ k)) = 1 := by
        rw [map_pow]
        exact hconjpow
      have h := congrArg (fun f : MulAut K => f g) hconjpow'
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      have h' : lbar ^ (2 ^ k) * g * (lbar ^ (2 ^ k))⁻¹ = g := h
      calc g * lbar ^ (2 ^ k) = (lbar ^ (2 ^ k) * g * (lbar ^ (2 ^ k))⁻¹) *
            lbar ^ (2 ^ k) := by rw [h']
        _ = lbar ^ (2 ^ k) * g := by group
    have hmem : lbar ^ (2 ^ k) ∈ (⊥ : Subgroup K) := by
      rw [← BenderType.center_eq_bot hBT1]
      exact hcenter
    exact Subgroup.mem_bot.mp hmem
  have hlbarInt : lbar ∈ borel (Qsyl : Subgroup K) ⊓
      conjugate (borel (Qsyl : Subgroup K)) x⁻¹ := by
    refine Subgroup.mem_inf.mpr ⟨hlbarM, ?_⟩
    rw [mem_conjugate_iff_mul_inv]
    have hx' : x⁻¹ * lbar * (x⁻¹)⁻¹ ∈ borel (Qsyl : Subgroup K) := by
      rw [inv_inv]
      exact hxconjM
    exact hx' 
  have hxinvNotM : x⁻¹ ∉ borel (Qsyl : Subgroup K) := by
    intro h
    have hx : (x⁻¹)⁻¹ ∈ borel (Qsyl : Subgroup K) :=
      (borel (Qsyl : Subgroup K)).inv_mem h
    rw [inv_inv] at hx
    exact hxNotM hx
  have hOddCard := hc.strong.2.2 x⁻¹ hxinvNotM
  have hOddOrder : Odd (orderOf lbar) :=
    Odd.of_dvd_nat hOddCard (Subgroup.orderOf_dvd_natCard _ hlbarInt)
  have hdvd : orderOf lbar ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hlbarpow
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    exact (Nat.not_even_iff_odd.mpr (hj ▸ hOddOrder))
      ((Nat.even_pow).mpr ⟨even_two, hj0⟩)
  have hlbar_one : lbar = 1 := by
    apply orderOf_eq_one_iff.mp
    rw [hj, hj0, pow_zero]
  have hlO : l ∈ pCoreOf 2 L1 := by
    have h1 : π ⟨l, hlL⟩ = 1 := hlbar_one
    have h2 : (⟨l, hlL⟩ : ↥L1) ∈ pCore 2 ↥L1 := by
      rw [← QuotientGroup.ker_mk' (pCore 2 ↥L1)]
      exact MonoidHom.mem_ker.mpr h1
    exact (F1.mem_pCore_iff_coe ⟨l, hlL⟩).mp h2
  have hlK1g : l ∈ K1g :=
    pCoreOf_le_K1_map hF (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1 hlO)
  have htK1g : t ∈ K1g := by
    rw [hlk]
    exact K1g.mul_mem hlK1g hkK
  have hK1g_leP : K1g ≤ P := hK1gB.trans le_sup_right
  have hS_le_NK1g : S ≤ Subgroup.normalizer (K1g : Set G) :=
    ((le_sup_right : S ≤ B).trans le_sup_right).trans hK1g_normal
  have hQ1Sylow : IsSylowTwoOf Q1 K1g := by
    have h := CFSG.Quasithin.F7.isSylowTwoOf_inf_normal hSylP hK1g_leP hS_le_NK1g
    have h' : S ⊓ K1g = Q1 := by rw [inf_comm, hK1S]
    simpa [h'] using h
  have hQ1normal : (Q1.subgroupOf K1g).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQ1leK1g]
    exact hK1g_leP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hX : IsPGroup 2 (Subgroup.zpowers t) := by
    rw [isPGroup_iff_exists_orderOf_dvd_pow]
    refine ⟨k, fun x => ?_⟩
    have htp : t ^ (2 ^ k) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one t
    rw [← Subgroup.orderOf_coe x]
    exact (orderOf_dvd_of_mem_zpowers x.2).trans (orderOf_dvd_of_pow_eq_one htp)
  exact CFSG.Quasithin.F7.le_of_normal_sylow hQ1Sylow hQ1normal
    (Subgroup.zpowers_le.mpr htK1g) hX (Subgroup.mem_zpowers t)

theorem mem_pCoreOf_of_two_arc_right {L1 L2 S : Subgroup G}
    {n₀ m₀ k₀ : ℕ} (hF : F112HypW L1 L2 S) (hBT2 : BenderType (oTwoQuot ↥L2) n₀ m₀ k₀)
    (hE : S = (S ⊓ L2) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S))
    {t g : G} (hg : g ∈ L2 ⊔ bigB L1 L2 S) (hgB : g ∉ bigB L1 L2 S)
    (ht : t ∈ bigB L1 L2 S) (htg : g⁻¹ * t * g ∈ bigB L1 L2 S) (h2 : ∃ k, orderOf t = 2 ^ k) :
    t ∈ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
  have hc : bigB L2 L1 S = bigB L1 L2 S := bigB_comm L1 L2 S
  rw [← hc] at hE hg hgB ht htg ⊢
  exact mem_pCoreOf_of_two_arc_left (F112HypW.symm hF) hBT2 hE hg hgB ht htg h2

end Rq

theorem str83_mem_pCoreOf_of_two_arc {L1 L2 S : Subgroup G}
    {a : ℕ} (hF : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    {t g : G} (hg : g ∈ L1 ⊔ bigB L1 L2 S) (hgB : g ∉ bigB L1 L2 S)
    (ht : t ∈ bigB L1 L2 S) (htg : g⁻¹ * t * g ∈ bigB L1 L2 S) (h2 : ∃ k, orderOf t = 2 ^ k) :
    t ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
  obtain ⟨e1⟩ := hSz
  exact Rq.mem_pCoreOf_of_two_arc_left hF
    (BenderType.suzuki a ha (e1.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))
    (str83_eq_sup_pCoreOf hF.1 ha ⟨e1⟩ hL2).1 hg hgB ht htg h2

theorem str83_mem_pCoreOf_of_two_arc_right {L1 L2 S : Subgroup G}
    {a : ℕ} (hF : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    {t g : G} (hg : g ∈ L2 ⊔ bigB L1 L2 S) (hgB : g ∉ bigB L1 L2 S)
    (ht : t ∈ bigB L1 L2 S) (htg : g⁻¹ * t * g ∈ bigB L1 L2 S) (h2 : ∃ k, orderOf t = 2 ^ k) :
    t ∈ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
  obtain ⟨e2⟩ := hL2
  exact Rq.mem_pCoreOf_of_two_arc_right hF (BenderType.linear (2 * a + 1) (by omega) e2)
    (str83_eq_sup_pCoreOf hF.1 ha hSz ⟨e2⟩).2 hg hgB ht htg h2

theorem str83_pCoreOf_sup_pCoreOf
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2)) :
    pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = S := by
  have hSB := str83_bigB_le_normalizer hF.1 ha hSz hL2
  have h1 : VSzBig L1 ∨ VU3Big L1 := Or.inl ⟨a, ha, hSz⟩
  have hn : 2 ≤ 2 * a + 1 := by omega
  have h := str86_pCoreOf_sup_pCoreOf (n := 2 * a + 1) hF hSB h1 hn hL2
  simpa [Q1, Q2, P1, P2] using h

end CFSG.Quasithin.Stroth
