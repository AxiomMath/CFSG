module

public import CFSG.Quasithin.Recognition.Stroth.F112Tree
public import CFSG.Quasithin.Recognition.Stroth.U3Vertex
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

open scoped commutatorElement

private theorem f112U3_K1_map_le_bigB {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype ≤ bigB L1 L2 S := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hmem := Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hy)
  rwa [f112_parabolic_inf_eq_bigB hF.toW] at hmem

private theorem f112U3_K1_map_normal_in_parabolic {G : Type} [Group G]
    (L1 L2 S : Subgroup G) :
    (L1 ⊔ bigB L1 L2 S) ≤
      Subgroup.normalizer (((f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype :
        Subgroup G) : Set G) :=
  CFSG.ABGLocalTools.le_normalizer_map_subtype (L1 ⊔ bigB L1 L2 S) (f112K1 L1 L2 S)

private theorem f112U3_K1_map_le_normalizer_left
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype ≤
      Subgroup.normalizer (L1 : Set G) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  exact (f112U3_K1_map_le_bigB hF).trans (F1.bigB_le_normalizer_left hR).1

private theorem f112U3_le_normalizer_K1_map {G : Type} [Group G] (L1 L2 S : Subgroup G) :
    L1 ≤ Subgroup.normalizer (((f112K1 L1 L2 S).map
      (L1 ⊔ bigB L1 L2 S).subtype : Subgroup G) : Set G) :=
  le_sup_left.trans (f112U3_K1_map_normal_in_parabolic L1 L2 S)

private theorem f112U3_inf_K1_map_le_borelOf {G : Type}
    [Group G] [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    L1 ⊓ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype ≤ borelOf L1 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  rw [← F1.inf_bigB_eq_borelOf hR]
  exact inf_le_inf_left L1 (f112U3_K1_map_le_bigB hF)

private theorem f112U3_sup_inf_K1_pCoreOf_lt {G : Type}
    [Group G] [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    (L1 ⊓ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype) ⊔ pCoreOf 2 L1 < L1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  refine lt_of_le_of_lt (sup_le (f112U3_inf_K1_map_le_borelOf hF) ?_)
    (F1.lt_borelOf hR)
  exact (F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow).trans (F1.sylow_le_borelOf L1 S)

private theorem f112U3_pCoreOf_le_inf_K1_map {G : Type}
    [Group G] [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    pCoreOf 2 L1 ≤ L1 ⊓ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hpL1 : pCoreOf 2 L1 ≤ L1 := pCoreOf_le 2 L1
  have hpP1 : pCoreOf 2 L1 ≤ L1 ⊔ bigB L1 L2 S := hpL1.trans le_sup_left
  have hpB : pCoreOf 2 L1 ≤ bigB L1 L2 S :=
    (F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow).trans (inf_le_left.trans le_sup_right)
  have hPnorm : L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    F7.le_normalizer_pCoreOf_of_le_normalizer (F1.parabolic_le_normalizer hR)
  let Z : Subgroup ↥(L1 ⊔ bigB L1 L2 S) := (pCoreOf 2 L1).subgroupOf (L1 ⊔ bigB L1 L2 S)
  have hZnormal : Z.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hpP1).mpr hPnorm
  have hZleB : Z ≤ (bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S) := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hpB (Subgroup.mem_subgroupOf.mp hx))
  have hZleQ : Z ≤ ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf
      (L1 ⊔ bigB L1 L2 S) := by
    rwa [f112_parabolic_inf_eq_bigB hF.toW]
  have hcore : Z ≤ (((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf
      (L1 ⊔ bigB L1 L2 S)).normalCore :=
    Subgroup.normal_le_normalCore.mpr hZleQ
  refine le_inf hpL1 ?_
  calc pCoreOf 2 L1 = Z.map (L1 ⊔ bigB L1 L2 S).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hpP1).symm
    _ ≤ _ := Subgroup.map_mono hcore

private theorem f112U3_pCoreOf_le_bigB {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    pCoreOf 2 L1 ≤ bigB L1 L2 S :=
  (F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow).trans (inf_le_left.trans le_sup_right)

private theorem f112U3_conj_bigB {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {l : ↥L1}
    (hz : QuotientGroup.mk' (pCore 2 ↥L1) l ∈ Subgroup.center (oTwoQuot ↥L1))
    {c : G} (hcB : c ∈ bigB L1 L2 S) :
    ∃ l' : ↥L1, (l' : G) = c * (l : G) * c⁻¹ ∧
      QuotientGroup.mk' (pCore 2 ↥L1) l' ∈ Subgroup.center (oTwoQuot ↥L1) ∧
      (l' : G) ∈ bigB L1 L2 S := by
  classical
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hcL1 : c ∈ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left hR).1 hcB
  have hcmem : c * (l : G) * c⁻¹ ∈ L1 :=
    (Subgroup.mem_normalizer_iff.mp hcL1 (l : G)).mp l.2
  let l' : ↥L1 := ⟨c * (l : G) * c⁻¹, hcmem⟩
  have hcP1 : c ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hcB
  let φ : MulAut (oTwoQuot ↥L1) :=
    CFSG.GroupTheory.conjModPCore 2 L1 (L1 ⊔ bigB L1 L2 S)
      (F1.parabolic_le_normalizer hR) ⟨c, hcP1⟩
  have hφ : φ (QuotientGroup.mk' (pCore 2 ↥L1) l) =
      QuotientGroup.mk' (pCore 2 ↥L1) l' := by
    change CFSG.GroupTheory.conjModPCore 2 L1 (L1 ⊔ bigB L1 L2 S)
      (F1.parabolic_le_normalizer hR) ⟨c, hcP1⟩
        (QuotientGroup.mk (s := pCore 2 ↥L1) l) =
      QuotientGroup.mk (s := pCore 2 ↥L1) l'
    rw [CFSG.GroupTheory.conjModPCore_mk]
  have hz' : QuotientGroup.mk' (pCore 2 ↥L1) l' ∈ Subgroup.center (oTwoQuot ↥L1) := by
    rw [← hφ, Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := φ.surjective y
    calc φ y' * φ (QuotientGroup.mk' (pCore 2 ↥L1) l)
        = φ (y' * QuotientGroup.mk' (pCore 2 ↥L1) l) := (map_mul φ y' _).symm
      _ = φ (QuotientGroup.mk' (pCore 2 ↥L1) l * y') := by
          rw [Subgroup.mem_center_iff.mp hz y']
      _ = φ (QuotientGroup.mk' (pCore 2 ↥L1) l) * φ y' := map_mul φ _ y'
  have hlB1 := mem_borelOf_of_mk_mem_center (G := G) (L := L1) (S := S) (l := l)
    hF.1.h1.sylow hz
  have hBn : bigB L1 L2 S ≤ Subgroup.normalizer (borelOf L1 S : Set G) :=
    (F1.bigB_le_normalizer_borelOf hR).1
  have hl'B1 : c * (l : G) * c⁻¹ ∈ borelOf L1 S :=
    (Subgroup.mem_normalizer_iff.mp (hBn hcB) (l : G)).mp hlB1
  have hl'B : (l' : G) ∈ bigB L1 L2 S :=
    (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S) hl'B1
  exact ⟨l', rfl, hz', hl'B⟩

private theorem f112U3_conj_L1_mem_bigB {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {l : ↥L1}
    (hz : QuotientGroup.mk' (pCore 2 ↥L1) l ∈ Subgroup.center (oTwoQuot ↥L1))
    {g : G} (hg : g ∈ L1) :
    g * (l : G) * g⁻¹ ∈ bigB L1 L2 S := by
  have hlB1 := mem_borelOf_of_mk_mem_center (G := G) (L := L1) (S := S) (l := l)
    hF.1.h1.sylow hz
  have hlB : (l : G) ∈ bigB L1 L2 S :=
    (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S) hlB1
  have hcomm : g * (l : G) * g⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 L1 := by
    have hcent : QuotientGroup.mk' (pCore 2 ↥L1)
        (⟨g, hg⟩ * l * ⟨g, hg⟩⁻¹ * l⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [Subgroup.mem_center_iff.mp hz (QuotientGroup.mk' (pCore 2 ↥L1) ⟨g, hg⟩)]
      group
    have hcent' : ((⟨g, hg⟩ * l * ⟨g, hg⟩⁻¹ * l⁻¹ : ↥L1) : oTwoQuot ↥L1) = 1 := by
      simpa only [QuotientGroup.mk'_apply] using hcent
    exact (F1.mem_pCore_iff_coe (⟨g, hg⟩ * l * ⟨g, hg⟩⁻¹ * l⁻¹)).mp
      ((QuotientGroup.eq_one_iff _).mp hcent')
  have h := (bigB L1 L2 S).mul_mem (f112U3_pCoreOf_le_bigB hF hcomm) hlB
  simpa [mul_assoc] using h

private theorem f112U3_center_mem_K1_map {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {l : ↥L1}
    (hz : QuotientGroup.mk' (pCore 2 ↥L1) l ∈ Subgroup.center (oTwoQuot ↥L1)) :
    (l : G) ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype := by
  classical
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hBnorm : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left hR).1
  have hmem : (⟨(l : G), (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) l.2⟩ :
      ↥(L1 ⊔ bigB L1 L2 S)) ∈ f112K1 L1 L2 S := by
    intro b
    change ((b * ⟨(l : G), (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) l.2⟩ * b⁻¹ :
        ↥(L1 ⊔ bigB L1 L2 S)) : G) ∈
      (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · change (b : G) * (l : G) * (b : G)⁻¹ ∈ L1 ⊔ bigB L1 L2 S
      exact (L1 ⊔ bigB L1 L2 S).mul_mem
        ((L1 ⊔ bigB L1 L2 S).mul_mem b.2
          ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) l.2))
        ((L1 ⊔ bigB L1 L2 S).inv_mem b.2)
    · obtain ⟨g, hgL1, c, hcB, hbc⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes hBnorm).mp b.2
      change (b : G) * (l : G) * (b : G)⁻¹ ∈ L2 ⊔ bigB L1 L2 S
      rw [hbc]
      have hconj_eq : (g * c) * (l : G) * (g * c)⁻¹ =
          g * (c * (l : G) * c⁻¹) * g⁻¹ := by group
      rw [hconj_eq]
      obtain ⟨l', hl'eq, hz', -⟩ := f112U3_conj_bigB hF hz hcB
      rw [← hl'eq]
      exact (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S)
        (f112U3_conj_L1_mem_bigB hF hz' hgL1)
  exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

theorem f112_kernel_centralizes_of_u3 {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (hU : VU3Big L1) :
    ∀ t ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L1,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L1 := by
  obtain ⟨k, hk, F, hField, hFin, hFc, hU3⟩ := hU
  letI : Field F := hField
  haveI : Finite F := hFin
  have hq : CFSG.IsQuasisimple (oTwoQuot ↥L1) := isQuasisimple_oTwoQuot_of_u3 hk hFc hU3
  refine comm_mem_pCoreOf_of_isQuasisimple (L := L1)
    (K := (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype) hq ?_ ?_ ?_
  · exact f112U3_K1_map_le_normalizer_left hF
  · exact f112U3_le_normalizer_K1_map L1 L2 S
  · exact f112U3_sup_inf_K1_pCoreOf_lt hF

theorem f112_exists_normal_iso_psu3_left {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {k : ℕ} (hk : 2 ≤ k)
    {F : Type} [Field F] [Finite F] (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    ∃ N : Subgroup (↥(L1 ⊔ bigB L1 L2 S) ⧸ f112K1 L1 L2 S),
      N.Normal ∧ Nonempty (↥N ≃* StatedProj (StatedSU 3 (2 ^ k) F)) := by
  classical
  haveI : (f112K1 L1 L2 S).Normal := f112K1_normal L1 L2 S
  let P1 := L1 ⊔ bigB L1 L2 S
  let K : Subgroup G := (f112K1 L1 L2 S).map P1.subtype
  let Nsub : Subgroup G := L1 ⊓ K
  have hNsub_normal : (Nsub.subgroupOf L1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (F1.le_normalizer_inf_of_le (f112U3_le_normalizer_K1_map L1 L2 S))
  have hON : pCoreOf 2 L1 ≤ Nsub := f112U3_pCoreOf_le_inf_K1_map hF
  have hNlt : Nsub < L1 := lt_of_le_of_lt (f112U3_inf_K1_map_le_borelOf hF)
    (F1.lt_borelOf (Hyp111R.of_hyp111 rankOneListedFacts hF.1))
  have hZN : ∀ l : ↥L1, QuotientGroup.mk' (pCore 2 ↥L1) l ∈
      Subgroup.center (oTwoQuot ↥L1) → (l : G) ∈ Nsub := by
    intro l hz
    exact ⟨l.2, f112U3_center_mem_K1_map hF hz⟩
  obtain ⟨e⟩ := nonempty_quotient_equiv_psu3 hk hFc hU3 inf_le_left hNsub_normal hON hNlt hZN
  let ψ : ↥L1 →* ↥P1 ⧸ f112K1 L1 L2 S :=
    (QuotientGroup.mk' (f112K1 L1 L2 S)).comp
      (Subgroup.inclusion (le_sup_left : L1 ≤ P1))
  have hψrange : ψ.range = (L1.subgroupOf P1).map
      (QuotientGroup.mk' (f112K1 L1 L2 S)) := by
    rw [show ψ = (QuotientGroup.mk' (f112K1 L1 L2 S)).comp
        (Subgroup.inclusion (le_sup_left : L1 ≤ P1)) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range]
  have hL1n : (L1.subgroupOf P1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (F1.parabolic_le_normalizer (Hyp111R.of_hyp111 rankOneListedFacts hF.1))
  have hker : ψ.ker = Nsub.subgroupOf L1 := by
    ext x
    rw [MonoidHom.mem_ker]
    change ((Subgroup.inclusion (le_sup_left : L1 ≤ P1) x : ↥P1) :
      ↥P1 ⧸ f112K1 L1 L2 S) = 1 ↔ x ∈ Nsub.subgroupOf L1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact ⟨x.2, Subgroup.mem_map.mpr ⟨_, hx, rfl⟩⟩
    · rintro ⟨-, y, hy, hxy⟩
      have hyx : y = Subgroup.inclusion (le_sup_left : L1 ≤ P1) x := Subtype.ext hxy
      rwa [hyx] at hy
  refine ⟨ψ.range, ?_, ?_⟩
  · rw [hψrange]
    exact hL1n.map _ (QuotientGroup.mk'_surjective _)
  · exact ⟨(QuotientGroup.quotientKerEquivRange ψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans e)⟩

theorem f112_relIndex_bigB_of_u3 {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {k : ℕ} (hk : 2 ≤ k)
    {F : Type} [Field F] [Finite F] (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = (2 ^ k) ^ 3 + 1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hrel : (borelOf L1 S).relIndex L1 = (2 ^ k) ^ 3 + 1 := by
    have h' := index_borelOf_of_u3 hk hFc hF.1.h1.sylow hU3
    simpa [Subgroup.relIndex] using h'
  rw [F112W.relIndex_sup_eq_relIndex_inf (N := L1) (B := bigB L1 L2 S)
    ((F1.bigB_le_normalizer_left hR).1), F1.inf_bigB_eq_borelOf hR]
  exact hrel

end CFSG.Quasithin.Stroth
