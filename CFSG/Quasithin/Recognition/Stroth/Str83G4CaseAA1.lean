module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAV1
import CFSG.Quasithin.Background.SimsD1TransGrp
import CFSG.Quasithin.Background.HZ82Base
import CFSG.Quasithin.Recognition.Stroth.Str83G4CP
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseABall
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAFact5

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem caseA_X_le_N {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {α : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false) : caseAX α ≤ caseAN α := by
  unfold caseAX caseAN
  refine iSup₂_le fun w hw => ?_
  have hwadj : (f112Amalgam L1 L2 S).graphHat.Adj α w := hw
  obtain ⟨α'', hα''adj, hα''ne⟩ := f112_no_dead_ends hfr.1 hwadj.symm
  have hdist : CosetGeom.dist α α'' = 2 := by
    have hle : CosetGeom.dist α α'' ≤ 2 := by
      have htri := CosetGeom.dist_triangle_of_adj hwadj α''
      have h1 : CosetGeom.dist α w = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hwadj
      have h2 : CosetGeom.dist w α'' = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hα''adj
      omega
    have hne0 : CosetGeom.dist α α'' ≠ 0 := by
      intro h0
      exact hα''ne ((CosetGeom.dist_eq_zero_iff rfl).mp h0).symm
    have hne1 : CosetGeom.dist α α'' ≠ 1 := by
      intro h1
      have hadj : (f112Amalgam L1 L2 S).graphHat.Adj α α'' :=
        CosetGeom.dist_eq_one_iff_adj.mp h1
      have hne := CosetGeom.vtype_ne_of_adj hadj
      have hwv : CosetGeom.vtype w = true := by
        have h := CosetGeom.vtype_ne_of_adj hwadj
        rw [hα] at h
        cases h' : CosetGeom.vtype w <;> simp_all
      have hα''v : CosetGeom.vtype α'' = false := by
        have h := CosetGeom.vtype_ne_of_adj hα''adj
        rw [hwv] at h
        cases h' : CosetGeom.vtype α'' <;> simp_all
      rw [hα, hα''v] at hne
      exact hne rfl
    omega
  have hmem : caseAZ w ≤ caseAX α'' := by
    unfold caseAX
    exact le_iSup₂ (f := fun u (_ : u ∈ CosetGeom.nbrs α'') => caseAZ u) w hα''adj.symm
  exact hmem.trans
    (le_iSup₂ (f := fun w' (_ : CosetGeom.dist α w' = 2) => caseAX w') α'' hdist)

theorem caseA_N_le_Y
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S)
    {α : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false) : caseAN α ≤ caseAY α := by
  have hb : caseABoundAt L1 L2 S 4 := caseA_boundAt_four hfr hA
  unfold caseAY
  refine le_inf ?_ ?_
  ·
    unfold caseAN
    refine iSup₂_le fun w hw => ?_
    have hwv : CosetGeom.vtype w = false := by
      have h := (CosetGeom.vtype_eq_iff_even_dist rfl α w).mpr (by rw [hw]; exact even_two)
      rw [hα] at h
      exact h.symm
    unfold caseAX
    refine iSup₂_le fun u hu => ?_
    have huw : (f112Amalgam L1 L2 S).graphHat.Adj w u := hu
    have huv : CosetGeom.vtype u = true := by
      have h := CosetGeom.vtype_ne_of_adj huw
      rw [hwv] at h
      cases h' : CosetGeom.vtype u <;> simp_all
    have hdist : CosetGeom.dist u α ≤ 4 := by
      have htri := CosetGeom.dist_triangle rfl u w α
      have h1 : CosetGeom.dist u w = 1 := CosetGeom.dist_eq_one_iff_adj.mpr huw.symm
      have h2 : CosetGeom.dist w α = 2 := by rw [CosetGeom.dist_comm]; exact hw
      omega
    exact hb u α huv hdist
  ·
    unfold caseAN
    refine iSup₂_le fun w hw => ?_
    have hwv : CosetGeom.vtype w = false := by
      have h := (CosetGeom.vtype_eq_iff_even_dist rfl α w).mpr (by rw [hw]; exact even_two)
      rw [hα] at h
      exact h.symm
    unfold caseAX
    refine iSup₂_le fun u hu => ?_
    have huw : (f112Amalgam L1 L2 S).graphHat.Adj w u := hu
    have huv : CosetGeom.vtype u = true := by
      have h := CosetGeom.vtype_ne_of_adj huw
      rw [hwv] at h
      cases h' : CosetGeom.vtype u <;> simp_all
    refine Subgroup.le_centralizer_iff.mpr ?_
    refine iSup₂_le fun β' hβ' => ?_
    have hαβ' : (f112Amalgam L1 L2 S).graphHat.Adj α β' := hβ'
    have hβ'v : CosetGeom.vtype β' = true := by
      have h := CosetGeom.vtype_ne_of_adj hαβ'
      rw [hα] at h
      cases h' : CosetGeom.vtype β' <;> simp_all
    have hdist : CosetGeom.dist u β' ≤ 4 := by
      have htri := CosetGeom.dist_triangle rfl u α β'
      have huα : CosetGeom.dist u α ≤ 3 := by
        have htri' := CosetGeom.dist_triangle rfl u w α
        have h1 : CosetGeom.dist u w = 1 := CosetGeom.dist_eq_one_iff_adj.mpr huw.symm
        have h2 : CosetGeom.dist w α = 2 := by rw [CosetGeom.dist_comm]; exact hw
        omega
      have hαβ'd : CosetGeom.dist α β' = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hαβ'
      omega
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact caseA_commute_Z hb huv hβ'v hdist hz hy

theorem caseA_stab_le_normalizer_N (v : f112Gamma L1 L2 S) :
    CosetGeom.stab v ≤ Subgroup.normalizer (caseAN v : Set (f112Amalgam L1 L2 S).Ghat) := by
  intro x hx
  obtain ⟨hxG, hxv⟩ := CosetGeom.mem_stab.mp hx
  have h := caseA_N_smul (⟨x, hxG⟩ : f112Acting L1 L2 S) v
  rw [hxv] at h
  exact CosetGeom.mem_normalizer_of_conjSub_eq h.symm

theorem caseA_R_le_Qy_two
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S)
    {β ε : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true) (hd : CosetGeom.dist β ε ≤ 2) :
    caseAR β ≤ CosetGeom.Qy ε :=
  caseA_R_le_Qy (caseA_boundAt_four hfr hA) hβ (by omega)

private theorem a1b_Lhat_eq_sup_twoResidual
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {α β : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hβ : β ∈ CosetGeom.nbrs α) :
    caseALhat α = caseAS α β ⊔ twoResidual (caseALhat α) := by
  obtain ⟨φ, hinjα, -, -, -, -, -, -, -, -, -, -, hS, hLhat, -⟩ :=
    caseA_exists_chart_edge hfr hα hβ
  have hA : caseALhat α ≤ CosetGeom.stab α := caseALhat_le_stab α
  have hAS : caseAS α β ≤ CosetGeom.stab α := caseAS_le_stab_left α β
  have hLHS : caseAS α β ⊔ twoResidual (caseALhat α) ≤ CosetGeom.stab α :=
    sup_le hAS ((twoResidual_le (caseALhat α)).trans hA)
  have hmapTR : (twoResidual (caseALhat α)).map φ = twoResidual (L1 ⊔ S) := by
    have htr : twoResidual (caseALhat α) =
        (twoResidual (⊤ : Subgroup ↥(caseALhat α))).map (caseALhat α).subtype := by
      rw [← CFSG.Quasithin.SimsD1.TransGrp.twoResidual_map_eq (caseALhat α).subtype
        (caseALhat α).subtype_injective (⊤ : Subgroup ↥(caseALhat α)),
        Subgroup.map_top, Subgroup.range_subtype]
    rw [htr, Subgroup.map_map,
      ← CFSG.Quasithin.SimsD1.TransGrp.twoResidual_map_eq (φ.comp (caseALhat α).subtype)
        (fun x y h => Subtype.ext
          (hinjα (caseALhat_le_stab α x.2) (caseALhat_le_stab α y.2) h))
        (⊤ : Subgroup ↥(caseALhat α)),
      Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype, hLhat]
  have hmap : ((caseAS α β) ⊔ twoResidual (caseALhat α)).map φ = (caseALhat α).map φ := by
    rw [Subgroup.map_sup, hS, hmapTR,
      sup_twoResidual_eq (str83G4_isSylowTwoOf_sup_left hfr), hLhat]
  have hψ : Function.Injective (φ.comp (CosetGeom.stab α).subtype) :=
    fun a b h => Subtype.ext (hinjα a.2 b.2 h)
  have hmapH : ∀ {H : Subgroup (f112Amalgam L1 L2 S).Ghat}, H ≤ CosetGeom.stab α →
      H.map φ = (H.subgroupOf (CosetGeom.stab α)).map
        (φ.comp (CosetGeom.stab α).subtype) := by
    intro H hH
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hH]
  refine le_antisymm ?_ (sup_le ?_ (twoResidual_le (caseALhat α)))
  · have hsub : (caseALhat α).subgroupOf (CosetGeom.stab α) ≤
        (caseAS α β ⊔ twoResidual (caseALhat α)).subgroupOf (CosetGeom.stab α) := by
      apply (Subgroup.map_le_map_iff_of_injective hψ).mp
      rw [← hmapH hA, ← hmapH hLHS]
      exact hmap.ge
    calc caseALhat α = ((caseALhat α).subgroupOf (CosetGeom.stab α)).map
          (CosetGeom.stab α).subtype := (Subgroup.map_subgroupOf_eq_of_le hA).symm
      _ ≤ ((caseAS α β ⊔ twoResidual (caseALhat α)).subgroupOf
            (CosetGeom.stab α)).map (CosetGeom.stab α).subtype := Subgroup.map_mono hsub
      _ = caseAS α β ⊔ twoResidual (caseALhat α) :=
          Subgroup.map_subgroupOf_eq_of_le hLHS
  · exact le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs α) => caseAS α w) β hβ

private theorem a1b_stab_eq_sup_edgeStab
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {α β : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hβ : β ∈ CosetGeom.nbrs α) :
    CosetGeom.stab α = caseALhat α ⊔ (CosetGeom.stab α ⊓ CosetGeom.stab β) := by
  obtain ⟨φ, hinjα, -, hP1, -, hB, -, -, -, -, -, -, -, hLhat, -⟩ :=
    caseA_exists_chart_edge hfr hα hβ
  have hA : caseALhat α ≤ CosetGeom.stab α := caseALhat_le_stab α
  have hBle : CosetGeom.stab α ⊓ CosetGeom.stab β ≤ CosetGeom.stab α := inf_le_left
  have hSleB : S ≤ bigB L1 L2 S := le_sup_right
  have hmap : (caseALhat α ⊔ (CosetGeom.stab α ⊓ CosetGeom.stab β)).map φ =
      (CosetGeom.stab α).map φ := by
    rw [Subgroup.map_sup, hLhat, hB, hP1,
      show P1 L1 L2 S = L1 ⊔ bigB L1 L2 S from rfl, sup_assoc, sup_eq_right.mpr hSleB]
  have hψ : Function.Injective (φ.comp (CosetGeom.stab α).subtype) :=
    fun a b h => Subtype.ext (hinjα a.2 b.2 h)
  have hmapH : ∀ {H : Subgroup (f112Amalgam L1 L2 S).Ghat}, H ≤ CosetGeom.stab α →
      H.map φ = (H.subgroupOf (CosetGeom.stab α)).map
        (φ.comp (CosetGeom.stab α).subtype) := by
    intro H hH
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hH]
  refine le_antisymm ?_ (sup_le hA hBle)
  have hsub : (CosetGeom.stab α).subgroupOf (CosetGeom.stab α) ≤
      (caseALhat α ⊔ (CosetGeom.stab α ⊓ CosetGeom.stab β)).subgroupOf
        (CosetGeom.stab α) := by
    apply (Subgroup.map_le_map_iff_of_injective hψ).mp
    rw [← hmapH le_rfl, ← hmapH (sup_le hA hBle)]
    exact hmap.ge
  calc CosetGeom.stab α =
        ((CosetGeom.stab α).subgroupOf (CosetGeom.stab α)).map (CosetGeom.stab α).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le le_rfl).symm
    _ ≤ ((caseALhat α ⊔ (CosetGeom.stab α ⊓ CosetGeom.stab β)).subgroupOf
          (CosetGeom.stab α)).map (CosetGeom.stab α).subtype := Subgroup.map_mono hsub
    _ = caseALhat α ⊔ (CosetGeom.stab α ⊓ CosetGeom.stab β) :=
        Subgroup.map_subgroupOf_eq_of_le (sup_le hA hBle)

private theorem a1b_ar_le_an
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α β : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hβ : β ∈ CosetGeom.nbrs α) :
    caseAR β ≤ caseAN α := by
  have hβadj : (f112Amalgam L1 L2 S).graphHat.Adj α β := by simpa [CosetGeom.nbrs] using hβ
  have hβv : CosetGeom.vtype β = true := by
    have hne := CosetGeom.vtype_ne_of_adj hβadj
    rw [hα] at hne
    cases h : CosetGeom.vtype β <;> simp_all
  unfold caseAR caseAN
  refine iSup₂_le fun w hw => ?_
  by_cases hwα : w = α
  · subst hwα
    exact caseA_X_le_N hfr hα
  · refine le_iSup₂ (f := fun w' (_ : CosetGeom.dist α w' = 2) => caseAX w') w ?_
    have hwadj : (f112Amalgam L1 L2 S).graphHat.Adj β w := by simpa [CosetGeom.nbrs] using hw
    have hwv : CosetGeom.vtype w = false := by
      have hne := CosetGeom.vtype_ne_of_adj hwadj
      rw [hβv] at hne
      cases h : CosetGeom.vtype w <;> simp_all
    have hle2 : CosetGeom.dist α w ≤ 2 := by
      have h1 := CosetGeom.dist_triangle_of_adj hβadj w
      have h1' : CosetGeom.dist α β = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hβadj
      have h2 : CosetGeom.dist β w = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hwadj
      omega
    have hne0 : CosetGeom.dist α w ≠ 0 := by
      intro h0
      have hαw : α = w := (CosetGeom.dist_eq_zero_iff rfl).mp h0
      exact hwα hαw.symm
    have hne1 : CosetGeom.dist α w ≠ 1 := fun h1 =>
      (CosetGeom.vtype_ne_of_adj (CosetGeom.dist_eq_one_iff_adj.mp h1)) (by rw [hα, hwv])
    omega

private theorem a1b_an_le_ar
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S)
    {α β : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false)
    (hβ : β ∈ CosetGeom.nbrs α)
    (h : twoResidual (caseALhat α) ≤
      centralizerMod (caseAX α) (caseALhat α) (caseAN α))
    (hLhat : caseALhat α = caseAS α β ⊔ twoResidual (caseALhat α))
    (hstab : CosetGeom.stab α = caseALhat α ⊔ (CosetGeom.stab α ⊓ CosetGeom.stab β)) :
    caseAN α ≤ caseAR β := by
  have hRB : caseAR β ≤ caseAN α := a1b_ar_le_an hfr hα hβ
  have hαβ : α ∈ CosetGeom.nbrs β := by
    have h := (by simpa [CosetGeom.nbrs] using hβ :
      (f112Amalgam L1 L2 S).graphHat.Adj α β)
    simpa [CosetGeom.nbrs] using h.symm
  have hXA : caseAX α ≤ caseAR β :=
    le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs β) => caseAX w) α hαβ
  have hconj_le (x : (f112Amalgam L1 L2 S).Ghat)
      (hx : x ∈ twoResidual (caseALhat α)) : conjSub x (caseAR β) ≤ caseAR β := by
    intro y hy
    rw [conjSub] at hy
    obtain ⟨r, hr, hy⟩ := Subgroup.mem_map.mp hy
    have hy' : x * r * x⁻¹ = y := by simpa [MulAut.conj_apply] using hy
    rw [← hy']
    have hmem : x * r * x⁻¹ * r⁻¹ ∈ caseAX α :=
      (mem_centralizerMod.mp (h hx)).2.2 r (hRB hr)
    have e : x * r * x⁻¹ = (x * r * x⁻¹ * r⁻¹) * r := by group
    rw [e]
    exact (caseAR β).mul_mem (hXA hmem) hr
  have hO2 : twoResidual (caseALhat α) ≤
      Subgroup.normalizer (caseAR β : Set (f112Amalgam L1 L2 S).Ghat) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm (hconj_le x hx)
    have hxinv : x⁻¹ ∈ twoResidual (caseALhat α) := (twoResidual (caseALhat α)).inv_mem hx
    calc caseAR β = conjSub x (conjSub x⁻¹ (caseAR β)) :=
          (conjSub_inv_conjSub x (caseAR β)).symm
      _ ≤ conjSub x (caseAR β) := conjSub_mono x (hconj_le x⁻¹ hxinv)
  have hS : caseAS α β ≤ Subgroup.normalizer (caseAR β : Set (f112Amalgam L1 L2 S).Ghat) :=
    (caseAS_le_stab_right α β).trans (caseA_stab_le_normalizer_R β)
  have hLhatN : caseALhat α ≤
      Subgroup.normalizer (caseAR β : Set (f112Amalgam L1 L2 S).Ghat) := by
    rw [hLhat]
    exact sup_le hS hO2
  have hStabN : CosetGeom.stab α ≤
      Subgroup.normalizer (caseAR β : Set (f112Amalgam L1 L2 S).Ghat) := by
    rw [hstab]
    exact sup_le hLhatN (inf_le_right.trans (caseA_stab_le_normalizer_R β))
  unfold caseAN
  refine iSup₂_le fun w hw => ?_
  obtain ⟨β', hadj, hdist⟩ := CosetGeom.exists_adj_dist_eq rfl
    (show CosetGeom.dist α w = 1 + 1 by omega)
  have hβ'nbrs : β' ∈ CosetGeom.nbrs α := by
    simpa [CosetGeom.nbrs] using CosetGeom.dist_eq_one_iff_adj.mp hdist
  have hwnbrs : w ∈ CosetGeom.nbrs β' := by simpa [CosetGeom.nbrs] using hadj.symm
  have hXR : caseAX w ≤ caseAR β' :=
    le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs β') => caseAX w) w hwnbrs
  obtain ⟨g, hgstab, hgw⟩ := CosetGeom.stab_transitive_on_nbrs hβ hβ'nbrs
  have hRβ' : caseAR β' = caseAR β := by
    rw [← hgw, caseA_R_smul g β]
    have hmem := hStabN hgstab
    simpa [conjSub] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem)
  exact hXR.trans hRβ'.le

private theorem a1b_an_eq_ar
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S)
    {α β : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false)
    (hβ : β ∈ CosetGeom.nbrs α)
    (h : twoResidual (caseALhat α) ≤
      centralizerMod (caseAX α) (caseALhat α) (caseAN α))
    (hLhat : caseALhat α = caseAS α β ⊔ twoResidual (caseALhat α))
    (hstab : CosetGeom.stab α = caseALhat α ⊔ (CosetGeom.stab α ⊓ CosetGeom.stab β)) :
    caseAN α = caseAR β :=
  le_antisymm (a1b_an_le_ar hfr hA hα hβ h hLhat hstab) (a1b_ar_le_an hfr hα hβ)

theorem caseA_not_twoResidual_le_centralizerMod
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S)
    {α : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false) :
    ¬ twoResidual (caseALhat α) ≤ centralizerMod (caseAX α) (caseALhat α) (caseAN α) := by
  intro h
  obtain ⟨β, hβ⟩ := CosetGeom.exists_adj α
  have hβadj : (f112Amalgam L1 L2 S).graphHat.Adj α β := by simpa [CosetGeom.nbrs] using hβ
  have hβv : CosetGeom.vtype β = true := by
    have hne := CosetGeom.vtype_ne_of_adj hβadj
    rw [hα] at hne
    cases hh : CosetGeom.vtype β <;> simp_all
  have hLhat := a1b_Lhat_eq_sup_twoResidual hfr hα hβ
  have hstab := a1b_stab_eq_sup_edgeStab hfr hα hβ
  have hNeq : caseAN α = caseAR β := a1b_an_eq_ar hfr hA hα hβ h hLhat hstab
  have hNnormβ : CosetGeom.stab β ≤
      Subgroup.normalizer (caseAN α : Set (f112Amalgam L1 L2 S).Ghat) := by
    rw [hNeq]
    exact caseA_stab_le_normalizer_R β
  have hNα : caseAN α ≤ CosetGeom.stab α := by
    rw [hNeq]
    have hd : CosetGeom.dist β α ≤ 2 := by
      have h1 : CosetGeom.dist β α = 1 := by
        rw [CosetGeom.dist_comm]
        exact CosetGeom.dist_eq_one_iff_adj.mpr hβadj
      omega
    exact (caseA_R_le_Qy_two hfr hA hβv hd).trans (caseA_Qy_le_stab α)
  have hNβ : caseAN α ≤ CosetGeom.stab β := by
    rw [hNeq]
    have hd : CosetGeom.dist β β ≤ 2 := by
      rw [CosetGeom.dist_self]
      norm_num
    exact (caseA_R_le_Qy_two hfr hA hβv hd).trans (caseA_Qy_le_stab β)
  have hbot : caseAN α = ⊥ :=
    caseA_eq_bot_of_le_normalizer hfr hβ hNα hNβ (caseA_stab_le_normalizer_N α) hNnormβ
  have hZle : caseAZ α ≤ caseAN α := (caseA_Z_le_X hfr hα).trans (caseA_X_le_N hfr hα)
  exact caseA_Z_ne_bot hfr α (le_bot_iff.mp (hbot ▸ hZle))

private theorem a1d_pCoreOf_Lhat_eq_Qy
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {α τ : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hτ : τ ∈ CosetGeom.nbrs α) :
    pCoreOf 2 (caseALhat α) = CosetGeom.Qy α := by
  obtain ⟨φ, hinjα, -, -, -, -, hQy, -, -, -, -, -, -, hLhat, -⟩ :=
    caseA_exists_chart_edge hfr hα hτ
  have hψ : Function.Injective (φ.comp (caseALhat α).subtype) :=
    fun a b h => Subtype.ext (hinjα (caseALhat_le_stab α a.2) (caseALhat_le_stab α b.2) h)
  have hrange : (φ.comp (caseALhat α).subtype).range = L1 ⊔ S := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hLhat]
  have hmap := CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2
    (φ.comp (caseALhat α).subtype) hψ (⊤ : Subgroup ↥(caseALhat α))
  have hpcQ1 : (pCoreOf 2 (caseALhat α)).map φ = Q1 L1 L2 S := by
    calc (pCoreOf 2 (caseALhat α)).map φ
        = ((pCoreOf 2 (⊤ : Subgroup ↥(caseALhat α))).map
            (caseALhat α).subtype).map φ := by
          rw [CFSG.Quasithin.E1.map_subtype_pCoreOf_top]
      _ = (pCoreOf 2 (⊤ : Subgroup ↥(caseALhat α))).map
            (φ.comp (caseALhat α).subtype) := by rw [Subgroup.map_map]
      _ = pCoreOf 2 ((⊤ : Subgroup ↥(caseALhat α)).map
            (φ.comp (caseALhat α).subtype)) := hmap.symm
      _ = Q1 L1 L2 S := by
          rw [Subgroup.map_top, hrange, str83G4_pCoreOf_sup_left hfr]
  have hψ_stab : Function.Injective (φ.comp (CosetGeom.stab α).subtype) :=
    fun a b h => Subtype.ext (hinjα a.2 b.2 h)
  have hmapH : ∀ {H : Subgroup (f112Amalgam L1 L2 S).Ghat}, H ≤ CosetGeom.stab α →
      H.map φ = (H.subgroupOf (CosetGeom.stab α)).map
        (φ.comp (CosetGeom.stab α).subtype) := by
    intro H hH
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hH]
  have hpc_le : pCoreOf 2 (caseALhat α) ≤ CosetGeom.stab α :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (caseALhat α)).trans (caseALhat_le_stab α)
  have hQy_le : CosetGeom.Qy α ≤ CosetGeom.stab α := caseA_Qy_le_stab α
  have hsub : (pCoreOf 2 (caseALhat α)).subgroupOf (CosetGeom.stab α) =
      (CosetGeom.Qy α).subgroupOf (CosetGeom.stab α) := by
    apply Subgroup.map_injective hψ_stab
    rw [← hmapH hpc_le, ← hmapH hQy_le, hpcQ1, hQy]
  calc pCoreOf 2 (caseALhat α)
      = ((pCoreOf 2 (caseALhat α)).subgroupOf (CosetGeom.stab α)).map
          (CosetGeom.stab α).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hpc_le).symm
    _ = ((CosetGeom.Qy α).subgroupOf (CosetGeom.stab α)).map
          (CosetGeom.stab α).subtype := by rw [hsub]
    _ = CosetGeom.Qy α := Subgroup.map_subgroupOf_eq_of_le hQy_le

private theorem a1d_nonempty_mulEquiv_Lhat
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {α τ : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hτ : τ ∈ CosetGeom.nbrs α) :
    Nonempty (↥(caseALhat α) ≃* ↥(L1 ⊔ S)) := by
  obtain ⟨φ, hinjα, -, -, -, -, -, -, -, -, -, -, -, hLhat, -⟩ :=
    caseA_exists_chart_edge hfr hα hτ
  have hψ : Function.Injective (φ.comp (caseALhat α).subtype) :=
    fun a b h => Subtype.ext (hinjα (caseALhat_le_stab α a.2) (caseALhat_le_stab α b.2) h)
  have hrange : (φ.comp (caseALhat α).subtype).range = L1 ⊔ S := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hLhat]
  exact ⟨(MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)⟩

private theorem a1d_isSzU3Quot_Lhat
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {α τ : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hτ : τ ∈ CosetGeom.nbrs α) :
    IsSzU3Quot (oTwoQuot ↥(caseALhat α)) (2 ^ (2 * a + 1)) := by
  obtain ⟨e⟩ := a1d_nonempty_mulEquiv_Lhat hfr hα hτ
  exact IsSzU3Quot.of_mulEquiv (oTwoQuotCongr e) (str83G4_isSzU3Quot_sup_left hfr)

private theorem a1d_isNormalIn_subgroupOf {A : Type*} [Group A] {H U N : Subgroup A}
    (h : IsNormalIn H U N) : IsNormalIn ⊤ (U.subgroupOf H) (N.subgroupOf H) := by
  refine ⟨Subgroup.subgroupOf_mono H h.1, ?_⟩
  intro g _ x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have e : ((g * x * g⁻¹ : ↥H) : A) = (g : A) * (x : A) * (g : A)⁻¹ := by simp
  rw [e]
  exact h.2 (g : A) g.2 (x : A) hx

theorem caseA_sq_le_relIndex_centralizerMod_N
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S)
    {α τ : f112Gamma L1 L2 S} (hα : CosetGeom.vtype α = false) (hτ : τ ∈ CosetGeom.nbrs α)
    {t : (f112Amalgam L1 L2 S).Ghat} (ht : t ∈ caseAS α τ) (ht2 : t * t = 1)
    (htQ : t ∉ CosetGeom.Qy α) :
    (2 ^ (2 * a + 1)) ^ 2 ≤
      (centralizerMod (caseAX α) (caseAN α) (Subgroup.zpowers t)).relIndex (caseAN α) := by
  haveI : Finite ↥(CosetGeom.stab α) := caseA_finite_stab L1 L2 S α
  haveI : Finite ↥(caseALhat α) :=
    Finite.of_injective (Subgroup.inclusion (caseALhat_le_stab α))
      (Subgroup.inclusion_injective (caseALhat_le_stab α))
  have hcore := a1d_pCoreOf_Lhat_eq_Qy hfr hα hτ
  have hQy_le : CosetGeom.Qy α ≤ caseALhat α :=
    hcore ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 (caseALhat α)
  have hAN_le : caseAN α ≤ caseALhat α :=
    ((caseA_N_le_Y hfr hA hα).trans inf_le_left).trans hQy_le
  have hAX_le : caseAX α ≤ caseALhat α := (caseA_X_le_N hfr hα).trans hAN_le
  have hH' : IsSzU3Quot (oTwoQuot ↥(⊤ : Subgroup ↥(caseALhat α))) (2 ^ (2 * a + 1)) :=
    IsSzU3Quot.of_mulEquiv
      (oTwoQuotCongr (Subgroup.topEquiv : (⊤ : Subgroup ↥(caseALhat α)) ≃* ↥(caseALhat α)))
      (a1d_isSzU3Quot_Lhat hfr hα hτ)
  have hUbase : IsPGroup 2 (CosetGeom.Qy α) := by
    unfold CosetGeom.Qy CFSG.Open.pCoreOf
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(CosetGeom.stab α))).map
      (CosetGeom.stab α).subtype
  have hU' : IsPGroup 2 ((CosetGeom.Qy α).subgroupOf (caseALhat α)) :=
    hUbase.of_equiv (Subgroup.subgroupOfEquivOfLe hQy_le).symm
  have hQySub : (CosetGeom.Qy α).subgroupOf (caseALhat α) =
      pCore 2 ↥(caseALhat α) := by
    apply Subgroup.map_injective (caseALhat α).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hQy_le,
      ← CFSG.Quasithin.E1.pCoreOf_top_eq 2 ↥(caseALhat α),
      CFSG.Quasithin.E1.map_subtype_pCoreOf_top (caseALhat α), hcore]
  have hUQ' : (CosetGeom.Qy α).subgroupOf (caseALhat α) ≤
      pCoreOf 2 (⊤ : Subgroup ↥(caseALhat α)) := by
    rw [CFSG.Quasithin.E1.pCoreOf_top_eq]
    exact le_of_eq hQySub
  have hZU : IsNormalIn (caseALhat α) (CosetGeom.Qy α) (caseAX α) :=
    F112W.isNormalIn_of_le_normalizer
      (caseA_X_le_Qy (caseA_boundAt_four hfr hA) hα (by rw [CosetGeom.dist_self]; norm_num))
      ((caseALhat_le_stab α).trans (caseA_stab_le_normalizer_X α))
  have hXU : IsNormalIn (caseALhat α) (CosetGeom.Qy α) (caseAN α) :=
    F112W.isNormalIn_of_le_normalizer
      ((caseA_N_le_Y hfr hA hα).trans inf_le_left)
      ((caseALhat_le_stab α).trans (caseA_stab_le_normalizer_N α))
  have hZU' := a1d_isNormalIn_subgroupOf hZU
  have hXU' := a1d_isNormalIn_subgroupOf hXU
  have hZX' : (caseAX α).subgroupOf (caseALhat α) ≤
      (caseAN α).subgroupOf (caseALhat α) :=
    Subgroup.subgroupOf_mono (caseALhat α) (caseA_X_le_N hfr hα)
  have hnot := caseA_not_twoResidual_le_centralizerMod hfr hA hα
  have hTRmap : (twoResidual (⊤ : Subgroup ↥(caseALhat α))).map (caseALhat α).subtype =
      twoResidual (caseALhat α) := by
    rw [← CFSG.Quasithin.SimsD1.TransGrp.twoResidual_map_eq (caseALhat α).subtype
      (caseALhat α).subtype_injective ⊤, Subgroup.map_top, Subgroup.range_subtype]
  have hCMmap : (centralizerMod ((caseAX α).subgroupOf (caseALhat α))
        (⊤ : Subgroup ↥(caseALhat α)) ((caseAN α).subgroupOf (caseALhat α))).map
        (caseALhat α).subtype =
      centralizerMod (caseAX α) (caseALhat α) (caseAN α) := by
    rw [CFSG.Quasithin.centralizerMod_map_of_injective (caseALhat α).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hAX_le, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hAN_le]
  have hnot' : ¬ twoResidual (⊤ : Subgroup ↥(caseALhat α)) ≤
      centralizerMod ((caseAX α).subgroupOf (caseALhat α))
        (⊤ : Subgroup ↥(caseALhat α)) ((caseAN α).subgroupOf (caseALhat α)) := by
    intro hle
    apply hnot
    have hm : ((twoResidual (⊤ : Subgroup ↥(caseALhat α))).map (caseALhat α).subtype) ≤
        ((centralizerMod ((caseAX α).subgroupOf (caseALhat α))
          (⊤ : Subgroup ↥(caseALhat α))
          ((caseAN α).subgroupOf (caseALhat α))).map (caseALhat α).subtype) :=
      Subgroup.map_mono hle
    rwa [hTRmap, hCMmap] at hm
  have htH : t ∈ caseALhat α :=
    le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs α) => caseAS α w) τ hτ ht
  have ht' : (⟨t, htH⟩ : ↥(caseALhat α)) * ⟨t, htH⟩ ∈
      pCoreOf 2 (⊤ : Subgroup ↥(caseALhat α)) := by
    rw [CFSG.Quasithin.E1.pCoreOf_top_eq, ← hQySub, Subgroup.mem_subgroupOf]
    change t * t ∈ CosetGeom.Qy α
    rw [ht2]
    exact Subgroup.one_mem _
  have htO' : (⟨t, htH⟩ : ↥(caseALhat α)) ∉
      pCoreOf 2 (⊤ : Subgroup ↥(caseALhat α)) := by
    rw [CFSG.Quasithin.E1.pCoreOf_top_eq, ← hQySub, Subgroup.mem_subgroupOf]
    simpa using htQ
  have hM7 := caseA_sq_le_relIndex_centralizerMod_section
    (H := (⊤ : Subgroup ↥(caseALhat α)))
    (U := (CosetGeom.Qy α).subgroupOf (caseALhat α))
    (Z := (caseAX α).subgroupOf (caseALhat α))
    (X := (caseAN α).subgroupOf (caseALhat α))
    hH' hU' le_top hUQ' hZU' hXU' hZX' hnot' (t := ⟨t, htH⟩) trivial ht' htO'
  have hCMmap2 : (centralizerMod ((caseAX α).subgroupOf (caseALhat α))
        ((caseAN α).subgroupOf (caseALhat α))
        (Subgroup.zpowers (⟨t, htH⟩ : ↥(caseALhat α)))).map (caseALhat α).subtype =
      centralizerMod (caseAX α) (caseAN α) (Subgroup.zpowers t) := by
    rw [CFSG.Quasithin.centralizerMod_map_of_injective (caseALhat α).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hAX_le, Subgroup.map_subgroupOf_eq_of_le hAN_le,
      MonoidHom.map_zpowers]
    rfl
  have hXmap2 : ((caseAN α).subgroupOf (caseALhat α)).map (caseALhat α).subtype =
      caseAN α := Subgroup.map_subgroupOf_eq_of_le hAN_le
  have hEq : (centralizerMod ((caseAX α).subgroupOf (caseALhat α))
        ((caseAN α).subgroupOf (caseALhat α))
        (Subgroup.zpowers (⟨t, htH⟩ : ↥(caseALhat α)))).relIndex
        ((caseAN α).subgroupOf (caseALhat α)) =
      (centralizerMod (caseAX α) (caseAN α) (Subgroup.zpowers t)).relIndex (caseAN α) := by
    rw [← Subgroup.relIndex_map_map_of_injective _ _ (caseALhat α).subtype_injective,
      hCMmap2, hXmap2]
  exact hM7.trans (le_of_eq hEq)

end CFSG.Quasithin.Stroth

end
