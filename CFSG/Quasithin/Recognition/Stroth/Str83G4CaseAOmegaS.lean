module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseASuzuki
import CFSG.Quasithin.Recognition.Stroth.Str83G4CP
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseATheta
public import CFSG.Quasithin.Recognition.Stroth.Str83G4NMGen

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem caseA_le_sup_Q1_of_commute
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {A E : Subgroup G} (hAS : A ≤ S) (hES : E ≤ S)
    (hAel : IsElemAbelian 2 A) (hAidx : (A ⊓ Q1 L1 L2 S).relIndex A = 2 ^ (2 * a + 1))
    (hquad : ⁅str83X L1 L2 S, A⁆ ≤ A) (hEA : ∀ e ∈ E, ∀ x ∈ A, e * x = x * e) :
    E ≤ A ⊔ Q1 L1 L2 S := by
  classical
  have ha : 1 ≤ a := hfr.2.2.1
  obtain ⟨L, N, hstep, -, hnc⟩ := str83G4_exists_chiefStep hfr
  have hNX : N ≤ str83X L1 L2 S := hstep.1.1
  have hNleqA : ⁅N, A⁆ ≤ A := (Subgroup.commutator_mono hNX le_rfl).trans hquad
  have hquad2 : ⁅⁅N, A⁆, A⁆ ≤ L := by
    refine (Subgroup.commutator_mono hNleqA le_rfl).trans ?_
    rw [Subgroup.commutator_self_eq_bot_iff.mpr hAel.1]
    exact bot_le
  have hU3 : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ (2 * a + 1)) :=
    str83G4_isSzU3Quot_sup_left hfr
  have hSyl := str83G4_isSylowTwoOf_sup_left hfr
  obtain ⟨X0, hX0mem, hQ1X0, hX0rel, -⟩ := exists_X0 hU3 hSyl
  have hpCore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := str83G4_pCoreOf_sup_left hfr
  have hQ1X0' : Q1 L1 L2 S ≤ X0 := by rw [← hpCore]; exact hQ1X0
  have hX0rel' : (Q1 L1 L2 S).relIndex X0 = 2 ^ (2 * a + 1) := by
    rw [← hpCore]; exact hX0rel
  have hAX0 : A ≤ X0 := by
    intro x hx
    rw [hX0mem x]
    exact ⟨hAS hx, by rw [hAel.2 x hx]; exact one_mem _⟩
  have hSNQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hANQ1 : A ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := hAS.trans hSNQ1
  have hq1 : (Q1 L1 L2 S).relIndex (A ⊔ Q1 L1 L2 S) = 2 ^ (2 * a + 1) := by
    rw [CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hANQ1]
    exact (Subgroup.inf_relIndex_left (H := A) (K := Q1 L1 L2 S)).symm.trans hAidx
  have hMX0 : A ⊔ Q1 L1 L2 S ≤ X0 := sup_le hAX0 hQ1X0'
  have hmul := Subgroup.relIndex_mul_relIndex (Q1 L1 L2 S) (A ⊔ Q1 L1 L2 S) X0
    le_sup_right hMX0
  have hmul' : 2 ^ (2 * a + 1) * (A ⊔ Q1 L1 L2 S).relIndex X0 =
      2 ^ (2 * a + 1) * 1 := by
    rw [mul_one]
    calc 2 ^ (2 * a + 1) * (A ⊔ Q1 L1 L2 S).relIndex X0
        = (Q1 L1 L2 S).relIndex (A ⊔ Q1 L1 L2 S) *
            (A ⊔ Q1 L1 L2 S).relIndex X0 := by rw [hq1]
      _ = (Q1 L1 L2 S).relIndex X0 := hmul
      _ = 2 ^ (2 * a + 1) := hX0rel'
  have hX0eq : A ⊔ Q1 L1 L2 S = X0 :=
    le_antisymm hMX0 (Subgroup.relIndex_eq_one.mp
      (Nat.eq_of_mul_eq_mul_left (by positivity) hmul'))
  have hC : ∀ s : G, s ∈ A ⊔ Q1 L1 L2 S ↔ s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S :=
    fun s => by rw [hX0eq, hX0mem s, hpCore]
  have hnat : IsSzNaturalSection (L1 ⊔ S) N L a :=
    str83G4_isSzNaturalSection_of_quadratic_chiefStep hfr hC (str83X_le_q1 hfr) hstep hquad2 hnc
  have hcomm : ⁅⁅N, A⁆, E⁆ ≤ L := by
    have hAE : ⁅A, E⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun e he => hEA e he a ha
    refine (Subgroup.commutator_mono hNleqA le_rfl).trans ?_
    rw [hAE]
    exact bot_le
  have hAne : ¬ A ≤ pCoreOf 2 (L1 ⊔ S) := by
    rw [hpCore]
    intro hle
    have h1 : (A ⊓ Q1 L1 L2 S).relIndex A = 1 := by
      rw [inf_of_le_left hle]
      exact Subgroup.relIndex_eq_one.mpr le_rfl
    rw [hAidx] at h1
    exact absurd h1 (ne_of_gt (one_lt_pow' (by norm_num : (1 : ℕ) < 2) (by omega)))
  have hA : ∀ s : G, s ∈ A ⊔ pCoreOf 2 (L1 ⊔ S) ↔
      s ∈ S ∧ s ^ 2 ∈ pCoreOf 2 (L1 ⊔ S) := fun s => by rw [hpCore]; exact hC s
  simpa [hpCore] using
    (caseA_le_sup_pCoreOf_of_natural_section (H := L1 ⊔ S) ha hnat hstep.1.2 hSyl
      hAS hES hA hAne hcomm)

theorem caseA_le_sup_Qy_of_commute
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α τ : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false)
    (hτ : τ ∈ CosetGeom.nbrs α) {A E : Subgroup (f112Amalgam L1 L2 S).Ghat}
    (hAS : A ≤ caseAS α τ) (hES : E ≤ caseAS α τ) (hAel : IsElemAbelian 2 A)
    (hAidx : (A ⊓ CosetGeom.Qy α).relIndex A = 2 ^ (2 * a + 1))
    (hquad : ⁅caseAX α, A⁆ ≤ A) (hEA : ∀ e ∈ E, ∀ x ∈ A, e * x = x * e) :
    E ≤ A ⊔ CosetGeom.Qy α := by
  classical
  obtain ⟨φ, hφα, hφτ, -, -, -, hmQα, -, -, -, hmXα, -, hmS, -, -⟩ :=
    caseA_exists_chart_edge hfr hα hτ
  let P : Subgroup (f112Amalgam L1 L2 S).Ghat := CosetGeom.stab α
  have hφα' : Set.InjOn φ (P : Set (f112Amalgam L1 L2 S).Ghat) := hφα
  have hinj : Function.Injective (φ.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : (f112Amalgam L1 L2 S).Ghat) = 1 :=
      hφα' x.2 P.one_mem (by rw [map_one]; exact hx)
    exact Subtype.ext hx1
  have hmap_sub (H : Subgroup (f112Amalgam L1 L2 S).Ghat) (hH : H ≤ P) :
      (H.subgroupOf P).map (φ.comp P.subtype) = H.map φ := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hH]
  have hA_stab : A ≤ P := hAS.trans (caseAS_le_stab_left α τ)
  have hE_stab : E ≤ P := hES.trans (caseAS_le_stab_left α τ)
  have hQy_stab : CosetGeom.Qy α ≤ P := caseA_Qy_le_stab α
  have hsub : (A ⊓ CosetGeom.Qy α).subgroupOf P
      = A.subgroupOf P ⊓ (CosetGeom.Qy α).subgroupOf P :=
    Subgroup.comap_inf A (CosetGeom.Qy α) P.subtype
  have hinfmap : ((A ⊓ CosetGeom.Qy α).subgroupOf P).map (φ.comp P.subtype)
      = A.map φ ⊓ Q1 L1 L2 S := by
    rw [hsub, Subgroup.map_inf _ _ (φ.comp P.subtype) hinj, hmap_sub A hA_stab,
      hmap_sub (CosetGeom.Qy α) hQy_stab, hmQα]
  have hinfmap' : (A ⊓ CosetGeom.Qy α).map φ = A.map φ ⊓ Q1 L1 L2 S :=
    (hmap_sub (A ⊓ CosetGeom.Qy α) (inf_le_left.trans hA_stab)).symm.trans hinfmap
  have hAidx' : (A.map φ ⊓ Q1 L1 L2 S).relIndex (A.map φ) = 2 ^ (2 * a + 1) := by
    have h1 := Subgroup.relIndex_map_map_of_injective
      ((A ⊓ CosetGeom.Qy α).subgroupOf P) (A.subgroupOf P) hinj
    rw [hmap_sub (A ⊓ CosetGeom.Qy α) (inf_le_left.trans hA_stab), hmap_sub A hA_stab,
      Subgroup.relIndex_subgroupOf hA_stab] at h1
    rw [hinfmap'] at h1
    exact h1.trans hAidx
  have hAS' : A.map φ ≤ S := (Subgroup.map_mono hAS).trans (le_of_eq hmS)
  have hES' : E.map φ ≤ S := (Subgroup.map_mono hES).trans (le_of_eq hmS)
  have hAel' : IsElemAbelian 2 (A.map φ) := IsElemAbelian.map hAel φ
  have hquad' : ⁅str83X L1 L2 S, A.map φ⁆ ≤ A.map φ := by
    have h : (⁅caseAX α, A⁆).map φ ≤ A.map φ := Subgroup.map_mono (f := φ) hquad
    rw [Subgroup.map_commutator, hmXα] at h
    exact h
  have hEA' : ∀ e ∈ E.map φ, ∀ x ∈ A.map φ, e * x = x * e := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hEA e he x hx]
  have hbase : E.map φ ≤ A.map φ ⊔ Q1 L1 L2 S :=
    caseA_le_sup_Q1_of_commute hfr hAS' hES' hAel' hAidx' hquad' hEA'
  have hbase' : (E.subgroupOf P).map (φ.comp P.subtype)
      ≤ ((A ⊔ CosetGeom.Qy α).subgroupOf P).map (φ.comp P.subtype) := by
    rw [hmap_sub E hE_stab, hmap_sub (A ⊔ CosetGeom.Qy α) (sup_le hA_stab hQy_stab),
      Subgroup.map_sup, hmQα]
    exact hbase
  have hle' : E.subgroupOf P ≤ (A ⊔ CosetGeom.Qy α).subgroupOf P :=
    (Subgroup.map_le_map_iff_of_injective hinj).mp hbase'
  intro x hx
  have hx' : (⟨x, hE_stab hx⟩ : ↥P) ∈ E.subgroupOf P := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hle' hx')

end CFSG.Quasithin.Stroth

end
