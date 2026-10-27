module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAV1
import CFSG.Quasithin.Recognition.Stroth.Str83G4Basic2
import CFSG.Quasithin.Recognition.Stroth.Str83Moufang
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseATwoArc

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem v2a_exists_smul_base_of_mem_nbrs {β α : f112Gamma L1 L2 S}
    (hβ : CosetGeom.vtype β = true) (hα : α ∈ CosetGeom.nbrs β) :
    ∃ g : f112Acting L1 L2 S,
      g • f112Gamma1 L1 L2 S = β ∧ g • f112Gamma0 L1 L2 S = α := by
  obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge
    (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
    (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2)
    (u := β) (v := α) hα
  · exfalso
    have hv : CosetGeom.vtype (g • f112Gamma0 L1 L2 S) = false := by
      rw [CosetGeom.vtype_smul]; exact CosetGeom.vtype_γ₀
    rw [hg.1] at hv
    exact Bool.false_ne_true (hv.symm.trans hβ)
  · exact ⟨g, hg.2, hg.1⟩

private theorem v2a_z1_inf_conjSub_dw {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) :
    Z1 L1 L2 S ⊓ conjSub d.w (Z1 L1 L2 S) = ⊥ := by
  have h : Z1 L1 L2 S ⊓ conjSub d.w⁻¹ (Z1 L1 L2 S) = ⊥ := by
    simpa [CFSG.conjugate, conjSub] using str83G4_z1_inf_conjugate_w hfr d
  have h2 := congrArg (conjSub d.w) h
  rw [conjSub_inf, conjSub_bot, conjSub_inv_conjSub, inf_comm] at h2
  exact h2

private theorem v2a_base_Z_inf_centralizer {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    caseAZ (f112Gamma1 L1 L2 S) ⊓
        Subgroup.centralizer (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :
          Set (f112Amalgam L1 L2 S).Ghat) =
      caseAZ (f112Gamma0 L1 L2 S) := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr'
  have hZ0 : caseAZ (f112Gamma0 L1 L2 S) ≤ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    (caseA_Z_le_Qy _).trans
      ((caseA_Qy_le_caseAS hfr (CosetGeom.adj_γ₀_γ₁)).trans (caseAS_le_stab_right _ _))
  have hZ1 : caseAZ (f112Gamma1 L1 L2 S) ≤ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    (caseA_Z_le_Qy _).trans (caseA_Qy_le_stab _)
  have hS1 : caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) ≤
      CosetGeom.stab (f112Gamma1 L1 L2 S) := caseAS_le_stab_left _ _
  have hmap : ∀ {H : Subgroup (f112Amalgam L1 L2 S).Ghat}
      (hH : H ≤ CosetGeom.stab (f112Gamma1 L1 L2 S)),
      (H.subgroupOf (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
          ((caseATheta L1 L2 S).comp (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype) =
        H.map (caseATheta L1 L2 S) := by
    intro H hH
    rw [← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hH]
  have hψ : Function.Injective
      ((caseATheta L1 L2 S).comp (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype) :=
    fun x y h => Subtype.ext (caseATheta_injOn_stab_γ₁ x.2 y.2 h)
  have hSmap : (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)).map
      (caseATheta L1 L2 S) = S := by
    rw [caseAS_comm (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S), caseATheta_map_S hfr]
  have hbase : Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S :=
    (str83_caseI_basics hF hB ha hSz hL2 hZI).2.2.2.2
  refine le_antisymm ?_ ?_
  · have hle : (caseAZ (f112Gamma1 L1 L2 S) ⊓
        Subgroup.centralizer (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :
          Set (f112Amalgam L1 L2 S).Ghat)).map (caseATheta L1 L2 S) ≤
        (caseAZ (f112Gamma0 L1 L2 S)).map (caseATheta L1 L2 S) := by
      calc (caseAZ (f112Gamma1 L1 L2 S) ⊓
            Subgroup.centralizer (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :
              Set (f112Amalgam L1 L2 S).Ghat)).map (caseATheta L1 L2 S)
          ≤ (caseAZ (f112Gamma1 L1 L2 S)).map (caseATheta L1 L2 S) ⊓
              (Subgroup.centralizer (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :
                Set (f112Amalgam L1 L2 S).Ghat)).map (caseATheta L1 L2 S) :=
            Subgroup.map_inf_le _ _ _
        _ ≤ Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) := by
            refine le_inf (inf_le_left.trans (le_of_eq caseATheta_map_Z_γ₁)) ?_
            have h1 := Subgroup.map_centralizer_le_centralizer_image
              (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :
                Set (f112Amalgam L1 L2 S).Ghat) (caseATheta L1 L2 S)
            rw [← Subgroup.coe_map (caseATheta L1 L2 S)
              (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)), hSmap] at h1
            exact inf_le_right.trans h1
        _ = Z1 L1 L2 S := hbase
        _ = (caseAZ (f112Gamma0 L1 L2 S)).map (caseATheta L1 L2 S) :=
            (caseATheta_map_Z_γ₀ L1 L2 S).symm
    have hsub : ((caseAZ (f112Gamma1 L1 L2 S) ⊓
        Subgroup.centralizer (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :
          Set (f112Amalgam L1 L2 S).Ghat)).subgroupOf
            (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
        ((caseATheta L1 L2 S).comp (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype) ≤
        ((caseAZ (f112Gamma0 L1 L2 S)).subgroupOf
          (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
        ((caseATheta L1 L2 S).comp (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype) := by
      rw [hmap (inf_le_left.trans hZ1), hmap hZ0]
      exact hle
    have hsub' := (Subgroup.map_le_map_iff_of_injective hψ).mp hsub
    calc caseAZ (f112Gamma1 L1 L2 S) ⊓
          Subgroup.centralizer (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :
            Set (f112Amalgam L1 L2 S).Ghat)
        = ((caseAZ (f112Gamma1 L1 L2 S) ⊓
            Subgroup.centralizer (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :
              Set (f112Amalgam L1 L2 S).Ghat)).subgroupOf
                (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
            (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hZ1)).symm
      _ ≤ ((caseAZ (f112Gamma0 L1 L2 S)).subgroupOf
            (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
            (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype := Subgroup.map_mono hsub'
      _ = caseAZ (f112Gamma0 L1 L2 S) := Subgroup.map_subgroupOf_eq_of_le hZ0
  · refine le_inf ?_ ?_
    · have hle : ((caseAZ (f112Gamma0 L1 L2 S)).subgroupOf
          (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
          ((caseATheta L1 L2 S).comp (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype) ≤
          ((caseAZ (f112Gamma1 L1 L2 S)).subgroupOf
            (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
          ((caseATheta L1 L2 S).comp (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype) := by
        rw [hmap hZ0, hmap hZ1, caseATheta_map_Z_γ₀ L1 L2 S,
          caseATheta_map_Z_γ₁, ← hbase]
        exact inf_le_left
      have hsub' := (Subgroup.map_le_map_iff_of_injective hψ).mp hle
      calc caseAZ (f112Gamma0 L1 L2 S)
          = ((caseAZ (f112Gamma0 L1 L2 S)).subgroupOf
              (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
              (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hZ0).symm
        _ ≤ ((caseAZ (f112Gamma1 L1 L2 S)).subgroupOf
              (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
              (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype := Subgroup.map_mono hsub'
        _ = caseAZ (f112Gamma1 L1 L2 S) := Subgroup.map_subgroupOf_eq_of_le hZ1
    · intro x hx
      rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
      intro y hy
      have hxP : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := hZ0 hx
      have hyP : y ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := hS1 hy
      have hxyP : ⁅x, y⁆ ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := by
        have := (CosetGeom.stab (f112Gamma1 L1 L2 S)).mul_mem
          ((CosetGeom.stab (f112Gamma1 L1 L2 S)).mul_mem hxP hyP)
          ((CosetGeom.stab (f112Gamma1 L1 L2 S)).mul_mem
            ((CosetGeom.stab (f112Gamma1 L1 L2 S)).inv_mem hxP)
            ((CosetGeom.stab (f112Gamma1 L1 L2 S)).inv_mem hyP))
        simpa [commutatorElement_def, mul_assoc] using this
      have hxZ : (caseATheta L1 L2 S) x ∈ Z1 L1 L2 S := by
        rw [← caseATheta_map_Z_γ₀]
        exact Subgroup.mem_map_of_mem _ hx
      have hyS : (caseATheta L1 L2 S) y ∈ S := by
        have hthis : (caseATheta L1 L2 S) y ∈
            (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)).map (caseATheta L1 L2 S) :=
          Subgroup.mem_map_of_mem _ hy
        rwa [hSmap] at hthis
      have hZ1C : Z1 L1 L2 S ≤ Subgroup.centralizer (S : Set G) := by
        rw [← hbase]
        exact inf_le_right
      have h1 : (caseATheta L1 L2 S) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp (hZ1C hxZ))
          ((caseATheta L1 L2 S) y) hyS
      have h2 : (caseATheta L1 L2 S) ⁅x, y⁆ = (caseATheta L1 L2 S) 1 := by
        rw [h1, map_one]
      exact caseATheta_injOn_stab_γ₁ hxyP (CosetGeom.stab (f112Gamma1 L1 L2 S)).one_mem h2

private theorem v2a_base_Z_inf_Z {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    {g : f112Acting L1 L2 S}
    (hgθ : caseATheta L1 L2 S (g : (f112Amalgam L1 L2 S).Ghat) = d.w)
    (hgstab : (g : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.stab (f112Gamma1 L1 L2 S)) :
    caseAZ (f112Gamma0 L1 L2 S) ⊓ caseAZ (g • f112Gamma0 L1 L2 S) = ⊥ := by
  have hZ0 : caseAZ (f112Gamma0 L1 L2 S) ≤ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    (caseA_Z_le_Qy _).trans
      ((caseA_Qy_le_caseAS hfr (CosetGeom.adj_γ₀_γ₁)).trans (caseAS_le_stab_right _ _))
  have hgZ : caseAZ (g • f112Gamma0 L1 L2 S) ≤ CosetGeom.stab (f112Gamma1 L1 L2 S) := by
    rw [caseA_Z_smul]
    calc conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAZ (f112Gamma0 L1 L2 S))
        ≤ conjSub (g : (f112Amalgam L1 L2 S).Ghat)
            (CosetGeom.stab (f112Gamma1 L1 L2 S)) := conjSub_mono _ hZ0
      _ = CosetGeom.stab (f112Gamma1 L1 L2 S) := by
          rw [← CosetGeom.stab_smul, CosetGeom.smul_eq_of_mem_stab hgstab]
  apply le_bot_iff.mp
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hx0, hxg⟩ := hx
  have hxP : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := hZ0 hx0
  have hxg' : x ∈ conjSub (g : (f112Amalgam L1 L2 S).Ghat)
      (caseAZ (f112Gamma0 L1 L2 S)) := by rwa [caseA_Z_smul] at hxg
  have hθ0 : caseATheta L1 L2 S x ∈ Z1 L1 L2 S := by
    have := Subgroup.mem_map_of_mem (caseATheta L1 L2 S) hx0
    rwa [caseATheta_map_Z_γ₀] at this
  have hθg : caseATheta L1 L2 S x ∈ conjSub d.w (Z1 L1 L2 S) := by
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxg'
    rw [← hyx]
    change caseATheta L1 L2 S ((g : (f112Amalgam L1 L2 S).Ghat) * y *
      (g : (f112Amalgam L1 L2 S).Ghat)⁻¹) ∈ conjSub d.w (Z1 L1 L2 S)
    rw [map_mul, map_mul, map_inv, hgθ]
    refine mul_mem_conjSub ?_
    have := Subgroup.mem_map_of_mem (caseATheta L1 L2 S) hy
    rwa [caseATheta_map_Z_γ₀] at this
  have hxbot : caseATheta L1 L2 S x ∈ (⊥ : Subgroup G) := by
    rw [← v2a_z1_inf_conjSub_dw hfr d]
    exact ⟨hθ0, hθg⟩
  rw [Subgroup.mem_bot] at hxbot
  rw [Subgroup.mem_bot]
  exact caseATheta_injOn_stab_γ₁ hxP (Subgroup.one_mem _) (by rw [hxbot, map_one])

theorem caseA_commutator_Z_zpowers
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β α : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true)
    (hα : α ∈ CosetGeom.nbrs β) {x : (f112Amalgam L1 L2 S).Ghat} (hx : x ∈ caseAS β α)
    (hxQ : x ∉ CosetGeom.Qy β) : ⁅caseAZ β, Subgroup.zpowers x⁆ = caseAZ α := by
  have hαfalse : CosetGeom.vtype α = false := CosetGeom.vtype_eq_false_of_adj hα hβ
  have hβmem : β ∈ CosetGeom.nbrs α := CosetGeom.mem_nbrs_symm hα
  obtain ⟨φ, -, hφβ, -, -, -, -, hQβ, hZα, hZβ, -, -, hS, -, -⟩ :=
    caseA_exists_chart_edge hfr hαfalse hβmem
  have hxP : x ∈ CosetGeom.stab β := caseAS_le_stab_left β α hx
  have hxP' : x ∈ caseAS α β := by rw [← caseAS_comm β α]; exact hx
  have hφxS : φ x ∈ S :=
    (congrArg (fun T : Subgroup G => φ x ∈ T) hS).mp
      (Subgroup.mem_map_of_mem φ hxP')
  have hφxQ : φ x ∉ Q2 L1 L2 S := by
    intro hxQ2
    have hxQ2' : φ x ∈ (CosetGeom.Qy β).map φ := by rw [hQβ]; exact hxQ2
    obtain ⟨y, hyQ, hyφ⟩ := Subgroup.mem_map.mp hxQ2'
    have hyP : y ∈ CosetGeom.stab β := caseA_Qy_le_stab β hyQ
    have hyx : y = x := hφβ hyP hxP hyφ
    exact hxQ (hyx ▸ hyQ)
  have hbase : ⁅Z2 L1 L2 S, Subgroup.zpowers (φ x)⁆ = Z1 L1 L2 S :=
    str83G4_commutator_z2_zpowers hfr hφxS hφxQ
  have hH : ⁅caseAZ β, Subgroup.zpowers x⁆ ≤ CosetGeom.stab β :=
    (Subgroup.commutator_mono ((caseA_Z_le_Qy β).trans (caseA_Qy_le_stab β))
      (Subgroup.zpowers_le.mpr hxP)).trans
      (Subgroup.commutator_le_self (CosetGeom.stab β))
  have hK : caseAZ α ≤ CosetGeom.stab β :=
    (caseA_Z_le_Qy α).trans
      ((caseA_Qy_le_caseAS hfr hβmem).trans (caseAS_le_stab_right α β))
  have hmap : ∀ {H : Subgroup (f112Amalgam L1 L2 S).Ghat}
      (hH : H ≤ CosetGeom.stab β),
      (H.subgroupOf (CosetGeom.stab β)).map (φ.comp (CosetGeom.stab β).subtype) = H.map φ := by
    intro H hH
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hH]
  have hψ : Function.Injective (φ.comp (CosetGeom.stab β).subtype) :=
    fun x y h => Subtype.ext (hφβ x.2 y.2 h)
  have heq : (⁅caseAZ β, Subgroup.zpowers x⁆).map φ = (caseAZ α).map φ := by
    rw [Subgroup.map_commutator, hZβ, MonoidHom.map_zpowers, hbase, hZα]
  apply le_antisymm
  · have hsub : (⁅caseAZ β, Subgroup.zpowers x⁆).subgroupOf (CosetGeom.stab β) ≤
        (caseAZ α).subgroupOf (CosetGeom.stab β) :=
      (Subgroup.map_le_map_iff_of_injective hψ).mp
        (by rw [hmap hH, hmap hK]; exact heq.le)
    calc ⁅caseAZ β, Subgroup.zpowers x⁆
        = ((⁅caseAZ β, Subgroup.zpowers x⁆).subgroupOf (CosetGeom.stab β)).map
            (CosetGeom.stab β).subtype := (Subgroup.map_subgroupOf_eq_of_le hH).symm
      _ ≤ ((caseAZ α).subgroupOf (CosetGeom.stab β)).map
            (CosetGeom.stab β).subtype := Subgroup.map_mono hsub
      _ = caseAZ α := Subgroup.map_subgroupOf_eq_of_le hK
  · have hsub : (caseAZ α).subgroupOf (CosetGeom.stab β) ≤
        (⁅caseAZ β, Subgroup.zpowers x⁆).subgroupOf (CosetGeom.stab β) :=
      (Subgroup.map_le_map_iff_of_injective hψ).mp
        (by rw [hmap hK, hmap hH]; exact heq.ge)
    calc caseAZ α
        = ((caseAZ α).subgroupOf (CosetGeom.stab β)).map
            (CosetGeom.stab β).subtype := (Subgroup.map_subgroupOf_eq_of_le hK).symm
      _ ≤ ((⁅caseAZ β, Subgroup.zpowers x⁆).subgroupOf (CosetGeom.stab β)).map
            (CosetGeom.stab β).subtype := Subgroup.map_mono hsub
      _ = ⁅caseAZ β, Subgroup.zpowers x⁆ := Subgroup.map_subgroupOf_eq_of_le hH

theorem caseA_commutator_Z_caseAS
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β α : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true)
    (hα : α ∈ CosetGeom.nbrs β) : ⁅caseAZ β, caseAS β α⁆ = caseAZ α := by
  have hαfalse : CosetGeom.vtype α = false := CosetGeom.vtype_eq_false_of_adj hα hβ
  have hβmem : β ∈ CosetGeom.nbrs α := CosetGeom.mem_nbrs_symm hα
  obtain ⟨φ, -, hφβ, -, -, -, -, -, hZα, hZβ, -, -, hS, -, -⟩ :=
    caseA_exists_chart_edge hfr hαfalse hβmem
  have hZβP : caseAZ β ≤ CosetGeom.stab β :=
    (caseA_Z_le_Qy β).trans (caseA_Qy_le_stab β)
  have hSP : caseAS β α ≤ CosetGeom.stab β := caseAS_le_stab_left β α
  have hH : ⁅caseAZ β, caseAS β α⁆ ≤ CosetGeom.stab β :=
    (Subgroup.commutator_mono hZβP hSP).trans
      (Subgroup.commutator_le_self (CosetGeom.stab β))
  have hK : caseAZ α ≤ CosetGeom.stab β :=
    (caseA_Z_le_Qy α).trans
      ((caseA_Qy_le_caseAS hfr hβmem).trans (caseAS_le_stab_right α β))
  have hbase : ⁅Z2 L1 L2 S, S⁆ = Z1 L1 L2 S := str83G4_commutator_z2_s hfr
  have hmap : ∀ {H : Subgroup (f112Amalgam L1 L2 S).Ghat}
      (hH : H ≤ CosetGeom.stab β),
      (H.subgroupOf (CosetGeom.stab β)).map (φ.comp (CosetGeom.stab β).subtype) = H.map φ := by
    intro H hH
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hH]
  have hψ : Function.Injective (φ.comp (CosetGeom.stab β).subtype) :=
    fun x y h => Subtype.ext (hφβ x.2 y.2 h)
  have heq : (⁅caseAZ β, caseAS β α⁆).map φ = (caseAZ α).map φ := by
    rw [Subgroup.map_commutator, hZβ, caseAS_comm β α, hS, hbase, hZα]
  apply le_antisymm
  · have hsub : (⁅caseAZ β, caseAS β α⁆).subgroupOf (CosetGeom.stab β) ≤
        (caseAZ α).subgroupOf (CosetGeom.stab β) :=
      (Subgroup.map_le_map_iff_of_injective hψ).mp
        (by rw [hmap hH, hmap hK]; exact heq.le)
    calc ⁅caseAZ β, caseAS β α⁆
        = ((⁅caseAZ β, caseAS β α⁆).subgroupOf (CosetGeom.stab β)).map
            (CosetGeom.stab β).subtype := (Subgroup.map_subgroupOf_eq_of_le hH).symm
      _ ≤ ((caseAZ α).subgroupOf (CosetGeom.stab β)).map
            (CosetGeom.stab β).subtype := Subgroup.map_mono hsub
      _ = caseAZ α := Subgroup.map_subgroupOf_eq_of_le hK
  · have hsub : (caseAZ α).subgroupOf (CosetGeom.stab β) ≤
        (⁅caseAZ β, caseAS β α⁆).subgroupOf (CosetGeom.stab β) :=
      (Subgroup.map_le_map_iff_of_injective hψ).mp
        (by rw [hmap hK, hmap hH]; exact heq.ge)
    calc caseAZ α
        = ((caseAZ α).subgroupOf (CosetGeom.stab β)).map
            (CosetGeom.stab β).subtype := (Subgroup.map_subgroupOf_eq_of_le hK).symm
      _ ≤ ((⁅caseAZ β, caseAS β α⁆).subgroupOf (CosetGeom.stab β)).map
            (CosetGeom.stab β).subtype := Subgroup.map_mono hsub
      _ = ⁅caseAZ β, caseAS β α⁆ := Subgroup.map_subgroupOf_eq_of_le hH

private theorem v2b_natCard_nbrs {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true) :
    Nat.card (CosetGeom.nbrs β) = 2 ^ (2 * a + 1) + 1 := by
  rw [show CosetGeom.nbrs β = (f112Amalgam L1 L2 S).graphHat.neighborSet β from rfl]
  rw [f112_natCard_neighborSet_of_vtype_true hfr.1 hβ,
    f112_relIndex_right_l2 (L1 := L1) (L2 := L2) (S := S) hfr.1 (by omega) hfr.2.2.2.2.1]

theorem caseA_relIndex_Qy_caseAS_type2 {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β α : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true)
    (hα : α ∈ CosetGeom.nbrs β) :
    (CosetGeom.Qy β).relIndex (caseAS β α) = 2 ^ (2 * a + 1) := by
  have ha : 1 ≤ a := hfr.2.2.1
  have hrel {H K : Subgroup (f112Amalgam L1 L2 S).Ghat}
      (hH : H ≤ CosetGeom.stab (f112Gamma1 L1 L2 S))
      (hK : K ≤ CosetGeom.stab (f112Gamma1 L1 L2 S)) :
      (H.map (caseATheta L1 L2 S)).relIndex (K.map (caseATheta L1 L2 S)) = H.relIndex K := by
    have hHmap : (H.subgroupOf (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
        ((caseATheta L1 L2 S).comp (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype) =
        H.map (caseATheta L1 L2 S) := by
      rw [← Subgroup.map_map,
        Subgroup.map_subgroupOf_eq_of_le hH]
    have hKmap : (K.subgroupOf (CosetGeom.stab (f112Gamma1 L1 L2 S))).map
        ((caseATheta L1 L2 S).comp (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype) =
        K.map (caseATheta L1 L2 S) := by
      rw [← Subgroup.map_map,
        Subgroup.map_subgroupOf_eq_of_le hK]
    have hψ : Function.Injective
        ((caseATheta L1 L2 S).comp (CosetGeom.stab (f112Gamma1 L1 L2 S)).subtype) :=
      fun x y h => Subtype.ext (caseATheta_injOn_stab_γ₁ x.2 y.2 h)
    rw [← hHmap, ← hKmap, Subgroup.relIndex_map_map_of_injective _ _ hψ,
      Subgroup.relIndex_subgroupOf hK]
  have hSmap : (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)).map
      (caseATheta L1 L2 S) = S := by
    rw [caseAS_comm (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S), caseATheta_map_S hfr]
  have hbase : (CosetGeom.Qy (f112Gamma1 L1 L2 S)).relIndex
      (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)) = 2 ^ (2 * a + 1) := by
    rw [← hrel (caseA_Qy_le_stab (f112Gamma1 L1 L2 S))
      (caseAS_le_stab_left (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)),
      caseATheta_map_Qy_γ₁, hSmap]
    exact str86_relIndex_q2_s hfr.1 hfr.2.1 (by omega) hfr.2.2.2.2.1
  obtain ⟨k, hk | hk⟩ :=
    CosetGeom.exists_smul_edge (u := β) (v := α) (show (f112Amalgam L1 L2 S).graphHat.Adj β α
      from hα)
  · exfalso
    have hvt : CosetGeom.vtype (k • f112Gamma0 L1 L2 S) = true := by rw [hk.1, hβ]
    rw [CosetGeom.vtype_smul] at hvt
    exact Bool.false_ne_true hvt
  · obtain ⟨hkα, hkβ⟩ := hk
    have hS : caseAS β α = conjSub (k : (f112Amalgam L1 L2 S).Ghat)
        (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)) := by
      rw [← hkβ, ← hkα, caseA_S_smul k (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)]
    have hQ : CosetGeom.Qy β = conjSub (k : (f112Amalgam L1 L2 S).Ghat)
        (CosetGeom.Qy (f112Gamma1 L1 L2 S)) := by
      rw [← hkβ, caseA_Qy_smul k (f112Gamma1 L1 L2 S)]
    rw [hS, hQ]
    exact (Subgroup.relIndex_map_map_of_injective
      (f := (MulAut.conj (k : (f112Amalgam L1 L2 S).Ghat)).toMonoidHom)
      (CosetGeom.Qy (f112Gamma1 L1 L2 S))
      (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S))
      (MulEquiv.injective _)).trans hbase

theorem caseA_exists_caseAS_smul_eq {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β α α₁ α₂ : f112Gamma L1 L2 S}
    (hβ : CosetGeom.vtype β = true) (hα : α ∈ CosetGeom.nbrs β)
    (h₁ : α₁ ∈ CosetGeom.nbrs β) (h₂ : α₂ ∈ CosetGeom.nbrs β) (hα₁ : α₁ ≠ α) (hα₂ : α₂ ≠ α) :
    ∃ g : f112Acting L1 L2 S,
      (g : (f112Amalgam L1 L2 S).Ghat) ∈ caseAS β α ∧ g • α₁ = α₂ := by
  classical
  let Msub : Subgroup (f112Amalgam L1 L2 S).Ghat :=
    (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2
  let T : Subgroup ↥Msub := (caseAS β α).subgroupOf Msub
  let Q : Subgroup ↥Msub := (CosetGeom.Qy β).subgroupOf Msub
  have hTle : (caseAS β α : Subgroup (f112Amalgam L1 L2 S).Ghat) ≤ Msub :=
    (caseAS_le_stab_left β α).trans (CosetGeom.stab_le β)
  have hstab : MulAction.stabilizer T α₁ = Q.subgroupOf T := by
    ext t
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro ht
      have htmem : ((t : ↥Msub) : (f112Amalgam L1 L2 S).Ghat) ∈ caseAS β α :=
        Subgroup.mem_subgroupOf.mp t.2
      have hgtβ : ((t : ↥Msub) : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.stab β :=
        caseAS_le_stab_left β α htmem
      have hgtα : ((t : ↥Msub) : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.stab α :=
        caseAS_le_stab_right β α htmem
      have htM : (t : ↥Msub) • α₁ = α₁ := ht
      have hgtα₁ : ((t : ↥Msub) : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.stab α₁ :=
        CosetGeom.mem_stab_of_smul_eq htM
      have h2 : ∃ k, orderOf (((t : ↥Msub) : (f112Amalgam L1 L2 S).Ghat)) = 2 ^ k := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        let H : Subgroup (f112Amalgam L1 L2 S).Ghat :=
          CosetGeom.stab β ⊓ CosetGeom.stab α
        have h := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
        obtain ⟨k, hk⟩ := h.exists_orderOf_eq_pow
          (⟨((t : ↥Msub) : (f112Amalgam L1 L2 S).Ghat), by
            simpa [H, caseAS, CFSG.Open.pCoreOf] using htmem⟩ :
            ↥((pCore 2 ↥H).map H.subtype))
        exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
      exact Subgroup.mem_subgroupOf.mpr
        (caseA_mem_Qy_of_fixes_two_nbrs hfr hα h₁ hα₁.symm hgtβ hgtα hgtα₁ h2)
    · intro ht
      have hqQy : ((t : ↥Msub) : (f112Amalgam L1 L2 S).Ghat) ∈ CosetGeom.Qy β :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp ht)
      have hball := caseA_Qy_le_ballStab_one hfr β hqQy
      have hdist : CosetGeom.dist β α₁ ≤ 1 :=
        le_of_eq ((CosetGeom.dist_eq_one_iff_adj).mpr h₁)
      have hstabα₁ := CosetGeom.ballStab_le_stab_of_dist_le (n := 1) hdist hball
      exact CosetGeom.smul_eq_of_mem_stab hstabα₁
  have horbit : (MulAction.orbit T α₁).ncard = 2 ^ (2 * a + 1) := by
    rw [← MulAction.index_stabilizer T α₁, hstab]
    have hQrel : (Q.subgroupOf T).index = (CosetGeom.Qy β).relIndex (caseAS β α) :=
      Subgroup.relIndex_subgroupOf (H := CosetGeom.Qy β) (K := caseAS β α) (L := Msub) hTle
    rw [hQrel, caseA_relIndex_Qy_caseAS_type2 hfr hβ hα]
  have hsub : MulAction.orbit T α₁ ⊆ CosetGeom.nbrs β \ {α} := by
    rintro x ⟨t, rfl⟩
    constructor
    · have htβ : (t : ↥Msub) • β = β :=
        CosetGeom.smul_eq_of_mem_stab (caseAS_le_stab_left β α (Subgroup.mem_subgroupOf.mp t.2))
      have hadj := (CosetGeom.smul_adj (t : ↥Msub)).mpr h₁
      rwa [htβ] at hadj
    · intro hx
      have hx' : (t : ↥Msub) • α₁ = α := by
        rw [← Subgroup.smul_def]; simpa using hx
      have htα : (t : ↥Msub) • α = α :=
        CosetGeom.smul_eq_of_mem_stab (caseAS_le_stab_right β α (Subgroup.mem_subgroupOf.mp t.2))
      have hα₁α : α₁ = α := by
        calc α₁ = (t : ↥Msub)⁻¹ • ((t : ↥Msub) • α₁) := by rw [inv_smul_smul]
          _ = (t : ↥Msub)⁻¹ • α := by rw [hx']
          _ = α := (inv_smul_eq_iff).mpr htα.symm
      exact hα₁ hα₁α
  have hVcard : (CosetGeom.nbrs β \ {α}).ncard = 2 ^ (2 * a + 1) := by
    rw [Set.ncard_sdiff_singleton_of_mem hα]
    have hcard : (CosetGeom.nbrs β).ncard = 2 ^ (2 * a + 1) + 1 := by
      rw [← Nat.card_coe_set_eq]; exact v2b_natCard_nbrs hfr hβ
    rw [hcard]; simp
  haveI : Finite ↥(CosetGeom.nbrs β) := by
    apply Nat.finite_of_card_ne_zero
    rw [v2b_natCard_nbrs hfr hβ]
    omega
  have horbitV : MulAction.orbit T α₁ = CosetGeom.nbrs β \ {α} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hVcard, horbit])
  have hα₂mem : α₂ ∈ MulAction.orbit T α₁ := by
    rw [horbitV]; exact ⟨h₂, hα₂⟩
  obtain ⟨t, ht⟩ := MulAction.mem_orbit_iff.mp hα₂mem
  refine ⟨(t : ↥Msub), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp t.2
  · rw [← Subgroup.smul_def]; exact ht

theorem caseA_exists_smul_two {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β α₁ α₂ α₃ α₄ : f112Gamma L1 L2 S}
    (hβ : CosetGeom.vtype β = true) (h₁ : α₁ ∈ CosetGeom.nbrs β) (h₂ : α₂ ∈ CosetGeom.nbrs β)
    (h₃ : α₃ ∈ CosetGeom.nbrs β) (h₄ : α₄ ∈ CosetGeom.nbrs β) (h₁₂ : α₁ ≠ α₂)
    (h₃₄ : α₃ ≠ α₄) :
    ∃ g : f112Acting L1 L2 S, g • β = β ∧ g • α₁ = α₃ ∧ g • α₂ = α₄ := by
  obtain ⟨g₁, hg₁stab, hg₁⟩ := f112_stabilizer_transitive_on_nbrs hfr.1 h₁ h₃
  have hg₁β : g₁ • β = β := MulAction.mem_stabilizer_iff.mp hg₁stab
  have hg₁α₂ : g₁ • α₂ ∈ CosetGeom.nbrs β := by
    have hadj := (CosetGeom.smul_adj g₁).mpr h₂
    rwa [hg₁β] at hadj
  have hne : g₁ • α₂ ≠ α₃ := by
    intro h
    apply h₁₂
    have h' : g₁ • α₂ = g₁ • α₁ := by rw [hg₁]; exact h
    have := congrArg (fun z => g₁⁻¹ • z) h'
    simpa using this.symm
  obtain ⟨h, hh_mem, hh⟩ :=
    caseA_exists_caseAS_smul_eq hfr hβ h₃ hg₁α₂ h₄ hne (Ne.symm h₃₄)
  exact ⟨h * g₁, by
      rw [mul_smul, hg₁β]
      exact CosetGeom.smul_eq_of_mem_stab (caseAS_le_stab_left β α₃ hh_mem), by
      rw [mul_smul, hg₁]
      exact CosetGeom.smul_eq_of_mem_stab (caseAS_le_stab_right β α₃ hh_mem), by
      rw [mul_smul]; exact hh⟩

theorem caseA_Z_inf_Z_eq_bot {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β α₁ α₂ : f112Gamma L1 L2 S}
    (hβ : CosetGeom.vtype β = true) (h₁ : α₁ ∈ CosetGeom.nbrs β)
    (h₂ : α₂ ∈ CosetGeom.nbrs β) (hne : α₁ ≠ α₂) : caseAZ α₁ ⊓ caseAZ α₂ = ⊥ := by
  obtain ⟨d⟩ := str83G4Data_nonempty hfr
  have hmap : d.w ∈ (caseALhat (f112Gamma1 L1 L2 S)).map (caseATheta L1 L2 S) := by
    rw [caseATheta_map_Lhat_γ₁ hfr]
    exact d.hwH2
  obtain ⟨ŵ, hŵL, hŵθ⟩ := Subgroup.mem_map.mp hmap
  have hŵstab : ŵ ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := caseALhat_le_stab _ hŵL
  obtain ⟨hŵG, hŵfix⟩ := CosetGeom.mem_stab.mp hŵstab
  let w' : f112Acting L1 L2 S := ⟨ŵ, hŵG⟩
  have hw'coe : (w' : (f112Amalgam L1 L2 S).Ghat) = ŵ := rfl
  have hw'θ : caseATheta L1 L2 S (w' : (f112Amalgam L1 L2 S).Ghat) = d.w := by
    rw [hw'coe, hŵθ]
  have hw'stab : (w' : (f112Amalgam L1 L2 S).Ghat) ∈
      CosetGeom.stab (f112Gamma1 L1 L2 S) := by
    rw [hw'coe]; exact hŵstab
  have hw'γ₁ : w' • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S := hŵfix
  have hbase := v2a_base_Z_inf_Z (g := w') hfr d hw'θ hw'stab
  obtain ⟨g, hgβ⟩ := CosetGeom.exists_smul_eq_γ₁ hβ
  let δ₁ : f112Gamma L1 L2 S := g • f112Gamma0 L1 L2 S
  let δ₂ : f112Gamma L1 L2 S := g • (w' • f112Gamma0 L1 L2 S)
  have hδ₁n : δ₁ ∈ CosetGeom.nbrs β := by
    have hadj := (CosetGeom.smul_adj (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔
        (f112Amalgam L1 L2 S).Ghat2) (G₁ := (f112Amalgam L1 L2 S).Ghat1)
        (G₂ := (f112Amalgam L1 L2 S).Ghat2) g).mpr (CosetGeom.adj_γ₀_γ₁)
    simpa [δ₁, hgβ, CosetGeom.nbrs] using hadj.symm
  have hδ₂n : δ₂ ∈ CosetGeom.nbrs β := by
    have h1 : (CosetGeom.graph ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
        (f112Amalgam L1 L2 S).Ghat1 (f112Amalgam L1 L2 S).Ghat2).Adj
        (f112Gamma1 L1 L2 S) (w' • f112Gamma0 L1 L2 S) := by
      have hadj := (CosetGeom.smul_adj (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔
          (f112Amalgam L1 L2 S).Ghat2) (G₁ := (f112Amalgam L1 L2 S).Ghat1)
          (G₂ := (f112Amalgam L1 L2 S).Ghat2) w').mpr (CosetGeom.adj_γ₀_γ₁)
      simpa [hw'γ₁] using hadj.symm
    have hadj := (CosetGeom.smul_adj (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔
        (f112Amalgam L1 L2 S).Ghat2) (G₁ := (f112Amalgam L1 L2 S).Ghat1)
        (G₂ := (f112Amalgam L1 L2 S).Ghat2) g).mpr h1
    simpa [δ₂, hgβ, CosetGeom.nbrs] using hadj
  have hw'γ₀ : w' • f112Gamma0 L1 L2 S ≠ f112Gamma0 L1 L2 S := by
    intro hcon
    have hmem0 : (w' : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.stab (f112Gamma0 L1 L2 S) := CosetGeom.mem_stab_of_smul_eq hcon
    have hB : (w' : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.stab (f112Gamma0 L1 L2 S) ⊓ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
      ⟨hmem0, hw'stab⟩
    have hwB : d.w ∈ bigB L1 L2 S := by
      have := Subgroup.mem_map_of_mem (caseATheta L1 L2 S) hB
      rw [caseATheta_map_stab_inf hfr] at this
      rwa [hw'θ] at this
    exact d.hwNotN (hfr.2.1 hwB)
  have hδne : δ₁ ≠ δ₂ := by
    intro hcon
    apply hw'γ₀
    have hthis : f112Gamma0 L1 L2 S = w' • f112Gamma0 L1 L2 S := by
      have := congrArg (fun t => g⁻¹ • t) hcon
      simpa [δ₁, δ₂, smul_smul] using this
    exact hthis.symm
  have hZ12 : caseAZ δ₁ ⊓ caseAZ δ₂ = ⊥ := by
    have e1 : caseAZ δ₁ = conjSub (g : (f112Amalgam L1 L2 S).Ghat)
        (caseAZ (f112Gamma0 L1 L2 S)) := by
      dsimp [δ₁]
      rw [caseA_Z_smul]
    have e2 : caseAZ δ₂ = conjSub (g : (f112Amalgam L1 L2 S).Ghat)
        (caseAZ (w' • f112Gamma0 L1 L2 S)) := by
      dsimp [δ₂]
      rw [caseA_Z_smul]
    rw [e1, e2, ← conjSub_inf, hbase, conjSub_bot]
  obtain ⟨k, -, hk₁, hk₂⟩ :=
    caseA_exists_smul_two hfr hβ h₁ h₂ hδ₁n hδ₂n hne hδne
  have e1 : caseAZ α₁ = conjSub ((k : (f112Amalgam L1 L2 S).Ghat)⁻¹) (caseAZ δ₁) := by
    have h1 : conjSub (k : (f112Amalgam L1 L2 S).Ghat) (caseAZ α₁) = caseAZ δ₁ := by
      rw [← caseA_Z_smul k α₁, hk₁]
    rw [← h1, conjSub_conjSub_inv]
  have e2 : caseAZ α₂ = conjSub ((k : (f112Amalgam L1 L2 S).Ghat)⁻¹) (caseAZ δ₂) := by
    have h2 : conjSub (k : (f112Amalgam L1 L2 S).Ghat) (caseAZ α₂) = caseAZ δ₂ := by
      rw [← caseA_Z_smul k α₂, hk₂]
    rw [← h2, conjSub_conjSub_inv]
  rw [e1, e2, ← conjSub_inf, hZ12, conjSub_bot]

theorem caseA_Z_inf_centralizer_caseAS {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β α : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true)
    (hα : α ∈ CosetGeom.nbrs β) :
    caseAZ β ⊓ Subgroup.centralizer (caseAS β α : Set (f112Amalgam L1 L2 S).Ghat) =
      caseAZ α := by
  obtain ⟨g, hg₁, hg₀⟩ := v2a_exists_smul_base_of_mem_nbrs hβ hα
  have hZβ : caseAZ β = conjSub (g : (f112Amalgam L1 L2 S).Ghat)
      (caseAZ (f112Gamma1 L1 L2 S)) := by rw [← hg₁, caseA_Z_smul]
  have hSβα : caseAS β α = conjSub (g : (f112Amalgam L1 L2 S).Ghat)
      (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)) := by
    rw [← hg₁, ← hg₀, caseA_S_smul]
  have hZα : caseAZ α = conjSub (g : (f112Amalgam L1 L2 S).Ghat)
      (caseAZ (f112Gamma0 L1 L2 S)) := by rw [← hg₀, caseA_Z_smul]
  have hC : Subgroup.centralizer (conjSub (g : (f112Amalgam L1 L2 S).Ghat)
      (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S)) :
        Set (f112Amalgam L1 L2 S).Ghat) =
      conjSub (g : (f112Amalgam L1 L2 S).Ghat)
        (Subgroup.centralizer (caseAS (f112Gamma1 L1 L2 S) (f112Gamma0 L1 L2 S) :
          Set (f112Amalgam L1 L2 S).Ghat)) :=
    CFSG.Quasithin.conjSub_centralizer (g : (f112Amalgam L1 L2 S).Ghat) _
  rw [hZβ, hSβα, hZα, hC, ← conjSub_inf, v2a_base_Z_inf_centralizer hfr]

theorem caseA_relIndex_inf_Qy_le_type2 {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β α : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true)
    (hα : α ∈ CosetGeom.nbrs β) {A : Subgroup (f112Amalgam L1 L2 S).Ghat}
    (hA : A ≤ caseAS β α) : (A ⊓ CosetGeom.Qy β).relIndex A ≤ 2 ^ (2 * a + 1) := by
  have hq := caseA_relIndex_Qy_caseAS_type2 hfr hβ hα
  have hne : (CosetGeom.Qy β).relIndex (caseAS β α) ≠ 0 := by
    rw [hq]; exact pow_ne_zero _ (by norm_num)
  calc (A ⊓ CosetGeom.Qy β).relIndex A
      = (CosetGeom.Qy β).relIndex A := Subgroup.inf_relIndex_left A (CosetGeom.Qy β)
    _ ≤ (CosetGeom.Qy β).relIndex (caseAS β α) :=
        Subgroup.relIndex_le_of_le_right hA hne
    _ = 2 ^ (2 * a + 1) := hq

theorem caseA_exists_nbr_ne {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true)
    (u v : f112Gamma L1 L2 S) : ∃ w ∈ CosetGeom.nbrs β, w ≠ u ∧ w ≠ v := by
  by_contra h
  push Not at h
  have hsub : CosetGeom.nbrs β ⊆ ({u, v} : Set (f112Gamma L1 L2 S)) := by
    intro w hw
    by_cases hwu : w = u
    · simp [hwu]
    · have hwv : w = v := (h w hw) hwu
      simp [hwv]
  have hle : Nat.card (CosetGeom.nbrs β) ≤ 2 := by
    have h1 : (CosetGeom.nbrs β).ncard ≤ ({u, v} : Set (f112Gamma L1 L2 S)).ncard :=
      Set.ncard_le_ncard hsub
    have h2 : ({u, v} : Set (f112Gamma L1 L2 S)).ncard ≤ 2 := by
      by_cases huv : u = v
      · simp [huv]
      · exact le_of_eq (Set.ncard_pair huv)
    rw [Nat.card_coe_set_eq]
    exact h1.trans h2
  have h3 : 3 ≤ Nat.card (CosetGeom.nbrs β) := by
    rw [v2b_natCard_nbrs hfr hβ]
    have h2 : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

end CFSG.Quasithin.Stroth

end
