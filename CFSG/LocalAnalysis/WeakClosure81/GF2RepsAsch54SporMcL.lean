module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporZTwo
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Sporadic.Schreier.PairMcLOut
public import Certificates.Certificate75341
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace SporMcL

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier.Co3.Native CFSG.ClassicalInvolution CFSG.ClassicalInvolution.McLData
  CFSG.ClassicalInvolution.McLProof
open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open scoped Pointwise commutatorElement

section Model

theorem pa_mem_S : pa ∈ S := Certificates.certificate75341.1

theorem pa_ne_one : pa ≠ 1 := by
  intro h
  have := orderOf_pa
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem S_le_P : S ≤ P := S_le_K.trans K_le_P

noncomputable abbrev T0 : Subgroup P := S.subgroupOf P

theorem mem_T0 {x : P} : x ∈ T0 ↔ (x : Equiv.Perm (Fin 275)) ∈ S := mem_subgroupOf

noncomputable abbrev zC : P := ⟨pa, pa_mem⟩

theorem zC_ne_one : zC ≠ 1 := fun h => pa_ne_one (congrArg Subtype.val h)

theorem comm_pa_of_mem_S {s : Equiv.Perm (Fin 275)} (hs : s ∈ S) : s * pa = pa * s :=
  (mem_centralizerIn.1 (K_le_cent (S_le_K hs))).2

theorem zC_mem_T0 : zC ∈ T0 := mem_T0.2 pa_mem_S

theorem zC_comm : ∀ p ∈ T0, zC * p = p * zC := fun _ hp =>
  Subtype.ext (comm_pa_of_mem_S (mem_T0.1 hp)).symm

theorem zC_mul_self : zC * zC = 1 := by
  have h := pow_orderOf_eq_one pa
  rw [orderOf_pa, pow_two] at h
  exact Subtype.ext h

theorem center_T0 : ∀ x ∈ T0, (∀ p ∈ T0, x * p = p * x) → x = 1 ∨ x = zC := by
  intro x hx hxt
  have h := Certificates.certificate75341.2.1 x (mem_T0.1 hx) fun t ht =>
    congrArg Subtype.val (hxt ⟨t, S_le_P ht⟩ (mem_T0.2 ht))
  rcases h with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

noncomputable abbrev V : Subgroup P := zTwoOf T0 zC zC_comm zC_mul_self

theorem coe_commutatorElement (x p : P) :
    ((⁅x, p⁆ : P) : Equiv.Perm (Fin 275)) =
      (x : Equiv.Perm (Fin 275)) * p * (x : Equiv.Perm (Fin 275))⁻¹ *
        (p : Equiv.Perm (Fin 275))⁻¹ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]

theorem mem_V {x : P} : x ∈ V ↔ (x : Equiv.Perm (Fin 275)) ∈ z2Set := by
  rw [mem_zTwoOf]
  refine and_congr mem_T0 ?_
  constructor
  · intro h t ht
    rcases h ⟨t, S_le_P ht⟩ (mem_T0.2 ht) with h | h
    · refine Or.inl ?_
      have := congrArg Subtype.val h
      rwa [coe_commutatorElement] at this
    · refine Or.inr ?_
      have := congrArg Subtype.val h
      rwa [coe_commutatorElement] at this
  · intro h t ht
    rcases h _ (mem_T0.1 ht) with h | h
    · exact Or.inl (Subtype.ext (by rw [coe_commutatorElement]; exact h))
    · exact Or.inr (Subtype.ext (by rw [coe_commutatorElement]; exact h))

theorem z2Set_le_P {y : Equiv.Perm (Fin 275)} (hy : y ∈ z2Set) : y ∈ P := S_le_P hy.1

end Model

section Normalizer

noncomputable abbrev B0 : Subgroup P := normalizer (V : Set P)

noncomputable abbrev NP : Subgroup (Equiv.Perm (Fin 275)) := P ⊓ normalizer z2Set

theorem B0_eq : B0 = NP.subgroupOf P := by
  ext g
  rw [mem_subgroupOf, mem_set_normalizer_iff]
  constructor
  · intro h
    refine ⟨g.2, ?_⟩
    change (g : Equiv.Perm (Fin 275)) ∈ normalizer z2Set
    rw [mem_set_normalizer_iff]
    intro y
    by_cases hy : y ∈ P
    · have := h ⟨y, hy⟩
      rw [SetLike.mem_coe, SetLike.mem_coe, mem_V, mem_V] at this
      exact this
    · refine ⟨fun h' => absurd (z2Set_le_P h') hy, fun h' => absurd ?_ hy⟩
      have h2 := z2Set_le_P h'
      have : y = (g : Equiv.Perm (Fin 275))⁻¹ * ((g : Equiv.Perm (Fin 275)) * y *
          (g : Equiv.Perm (Fin 275))⁻¹) * g := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem g.2) h2) g.2
  · rintro ⟨-, h⟩ x
    change (g : Equiv.Perm (Fin 275)) ∈ normalizer z2Set at h
    rw [mem_set_normalizer_iff] at h
    rw [SetLike.mem_coe, SetLike.mem_coe, mem_V, mem_V]
    exact h x

theorem card_B0 : Nat.card B0 = 1152 := by
  rw [B0_eq, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : NP ≤ P)).toEquiv]
  exact Certificates.certificate75341.2.2.1

end Normalizer

section Centralizer

noncomputable abbrev A0 : Subgroup P := centralizer ({zC} : Set P)

theorem A0_eq : A0 = K.subgroupOf P := by
  rw [A0, centralizer_mk_eq pa_mem, ← centralizerIn_P card_P]
  ext x
  rw [mem_subgroupOf, mem_subgroupOf, mem_centralizerIn, mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem card_A0 : Nat.card A0 = 40320 := by
  rw [A0_eq, Nat.card_congr (subgroupOfEquivOfLe K_le_P).toEquiv, card_K card_P]

theorem T0_le_A0 : T0 ≤ A0 := by
  rw [A0_eq]
  intro x hx
  rw [mem_subgroupOf] at hx ⊢
  exact S_le_K hx

theorem ne_top_of_card {Q : Subgroup P} {m : ℕ} (hQ : Nat.card Q = m) (hm : m ≠ 898128000) :
    Q ≠ ⊤ := by
  rintro rfl
  rw [card_top, card_P] at hQ
  exact hm hQ.symm

theorem not_hasCompFactor_A0 :
    ¬ HasCompFactor A0 IsCalL0 := by
  rintro ⟨L, _, hL, hcal⟩
  have e : ↥A0 ≃* ↥K := (MulEquiv.subgroupCongr A0_eq).trans (subgroupOfEquivOfLe K_le_P)
  have hLK := (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).1 hL
  have hq := K_quasisimple
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hq.1.2
  rcases isCompositionFactor_of_normal (center ↥K) hLK with h | h
  · exact not_isCalL0_of_isCompositionFactor_of_dvd
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 1) (N := 2)
      (by decide +kernel) (by rw [card_center_K]) h hcal
  · have hcard : Nat.card (↥K ⧸ center ↥K) = 20160 := by
      have := (center ↥K).card_eq_card_quotient_mul_card_subgroup
      rw [card_K card_P, card_center_K] at this
      omega
    exact not_isCalL0_of_isCompositionFactor_of_isSimpleGroup
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 6)
      (by rw [hcard]; decide +kernel) h hcal

theorem not_hasCompFactor_B0 :
    ¬ HasCompFactor B0 IsCalL0 :=
  not_hasCompFactor_isCalL0_of_dvd CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    (k := 7) (N := 1152) (by decide +kernel) (by rw [card_B0])

theorem A0_sup_B0 : A0 ⊔ B0 = ⊤ := by
  rw [A0_eq, B0_eq, ← subgroupOf_sup K_le_P (inf_le_left : NP ≤ P), eq_top_iff]
  intro x _
  rw [mem_subgroupOf]
  exact Certificates.certificate75341.2.2.2 x.2

theorem isSylowIn_T0 : IsSylowIn 2 T0 ⊤ := by
  have hcard : Nat.card T0 = 128 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe S_le_P).toEquiv, card_S]
  refine ⟨le_top, IsPGroup.of_card (n := 7) (by rw [hcard]; norm_num), ?_⟩
  rw [relIndex_top_right]
  exact S_index_odd card_P

theorem map_A0_B0 (ψ : P ≃* P) (hψ : T0.map ψ.toMonoidHom = T0) :
    A0.map ψ.toMonoidHom = A0 ∧ B0.map ψ.toMonoidHom = B0 :=
  map_centralizer_normalizer_zTwoOf_eq zC_mem_T0 zC_ne_one zC_comm zC_mul_self center_T0 ψ hψ

end Centralizer

end SporMcL

open SporMcL in
theorem asch54SporGenAt_mcl :
    Asch54SporGenAt .McL := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have hsC : Nonempty (TauCeti.SporadicName.McL.Group ≃* ↥CFSG.ClassicalInvolution.McLProof.P) :=
    ⟨e.symm.trans CFSG.ClassicalInvolution.McLProof.mclEquivP⟩
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥CFSG.ClassicalInvolution.McLProof.P) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.Schreier.McL_outer_card_le_two.1
      CFSG.ClassicalInvolution.McLProof.mclEquivP.symm
  have hP0 : ∀ (X : Type) [Group X] [Finite X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a :=
    fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1
  have hpair : IsLPair IsCalL0 T0 A0 B0 :=
    ⟨T0_le_A0, le_normalizer_zTwoOf T0 zC zC_comm zC_mul_self, ne_top_of_card card_A0 (by norm_num),
      ne_top_of_card card_B0 (by norm_num), not_hasCompFactor_A0, not_hasCompFactor_B0,
      A0_sup_B0⟩
  exact asch54SporGenAt_of_isLPair_of_aut hsC hP0 hOut isSylowIn_T0 hpair map_A0_B0

end CFSG.LocalAnalysis.WeakClosure81

end
