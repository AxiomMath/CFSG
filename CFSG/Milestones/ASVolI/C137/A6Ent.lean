module

public import CFSG.Milestones.ASVolI.C137.Gen
public import CFSG.Quasithin.H13.GoldschmidtC137S6Std
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open CFSG.Quasithin.C124
open scoped commutatorElement

variable {G : Type} [Group G]

theorem burnsideC137_inf_centralizer_le [Finite G] {X L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hred : IsTwoReducedIn X V) (hLX : L ≤ X) (hn : X ≤ normalizer (L : Set G)) :
    L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ centralizer (V : Set G) := by
  have hXN : X ≤ normalizer (V : Set G) := hred.2.1
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans hXN
  have hO2 : pCoreOf 2 (autI hV L) = ⊥ := pCoreOf_autI_L_eq_bot hV hred hLX hn
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hXN hg) (hn hg)
  set C : Subgroup G := L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) with hCdef
  have hCN : C ≤ normalizer (V : Set G) := inf_le_left.trans hLN
  have hsq : ∀ l ∈ C, l ^ 2 ∈ centralizer (V : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hlv : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLN hl.1) v).1 hv
    obtain ⟨c, hc⟩ : ∃ c : G, c = v⁻¹ * (l * v * l⁻¹) := ⟨_, rfl⟩
    have hcU : c ∈ (⁅V, L⁆ : Subgroup G) := by
      have : c = ⁅v⁻¹, l⁆ := by rw [hc, commutatorElement_def]; group
      rw [this]
      exact Subgroup.commutator_mem_commutator (V.inv_mem hv) hl.1
    have hlc : l * c * l⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.1 hl.2 c hcU
      rw [← this, mul_inv_cancel_right]
    have hcV : c ∈ V := by
      rw [hc]
      exact V.mul_mem (V.inv_mem hv) hlv
    have hc2 : c * c = 1 := by
      have := hV.2 c hcV
      simpa [pow_two] using this
    have h1 : l * v * l⁻¹ = v * c := by rw [hc]; group
    have h2 : (l * l) * v * (l * l)⁻¹ = v := by
      calc (l * l) * v * (l * l)⁻¹ = l * (l * v * l⁻¹) * l⁻¹ := by group
        _ = l * (v * c) * l⁻¹ := by rw [h1]
        _ = (l * v * l⁻¹) * (l * c * l⁻¹) := by group
        _ = v * c * c := by rw [h1, hlc]
        _ = v := by rw [mul_assoc, hc2, mul_one]
    rw [pow_two]
    calc v * (l * l) = ((l * l) * v * (l * l)⁻¹) * (l * l) := by rw [h2]
      _ = (l * l) * v := by group
  have hp : IsPGroup 2 ↥(autI hV C) := by
    intro φ
    refine ⟨1, ?_⟩
    obtain ⟨g, hgC, hg⟩ := (mem_autI hV).1 φ.2
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hg, ← map_pow]
    rw [convI_eq_one_iff]
    simpa using hsq g hgC
  have hCL : autI hV C ≤ autI hV L := autI_mono hV inf_le_left
  have hLC : L ≤ normalizer (C : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1
      (Subgroup.le_normalizer hx : x ∈ normalizer (L : Set G)) y
    have h2 := Subgroup.mem_normalizer_iff.1
      (burnsideC137_mem_normalizer_centralizer (hXU (hLX hx))) y
    simp only [hCdef, Subgroup.mem_inf]
    rw [h1, h2]
  have hCn : autI hV L ≤ normalizer (autI hV C : Set (MulAut (IntMod V hV))) :=
    H13.U3.GC137.autI_le_normalizer_autI_gc hV hLC
  have hCle : autI hV C ≤ pCoreOf 2 (autI hV L) := le_pCoreOf_of_le_normalizer 2 hCL hCn hp
  rw [hO2, le_bot_iff, autI_eq_bot_iff hV hCN] at hCle
  exact hCle

theorem burnsideC137_centralizer_U_le [Finite G] {X T V L : Subgroup G}
    (hred : IsTwoReducedIn X V) (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hcomp : L ∈ cComp X)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hVL : ⁅V, L⁆ ≠ ⊥) :
    X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ centralizer (V : Set G) := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hXN : X ≤ normalizer (V : Set G) := hred.2.1
  have hLX : L ≤ X := le_of_mem_cComp hcomp
  have hn : X ≤ normalizer (L : Set G) := le_normalizer_of_prod hT hprod hcomp
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2
  obtain ⟨-, -, hfs, -⟩ := B2_10_2 hV hred hQT le_rfl hT hLX hn hprod hVL (Or.inl hLq)
  have hCUV := burnsideC137_inf_centralizer_le hV hred hLX hn
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hXN hg) (hn hg)
  have hLU : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hLX.trans hXU
  intro x hx
  have hxX : x ∈ X := hx.1
  have hxN : x ∈ normalizer (V : Set G) := hXN hxX
  have hxc : ∀ u ∈ (⁅V, L⁆ : Subgroup G), x * u * x⁻¹ = u := fun u hu => by
    have := Subgroup.mem_centralizer_iff.1 hx.2 u hu
    rw [← this]
    group
  have hycomm : ∀ φ ∈ autI hV L, convI hV ⟨x, hxN⟩ * φ = φ * convI hV ⟨x, hxN⟩ := by
    intro φ hφ
    obtain ⟨l, hl, rfl⟩ := (mem_autI hV).1 hφ
    have hlU' : ∀ u ∈ (⁅V, L⁆ : Subgroup G), (l : G)⁻¹ * u * (l : G) ∈ (⁅V, L⁆ : Subgroup G) :=
      fun u hu => by
        have := (Subgroup.mem_normalizer_iff.1 ((normalizer ((⁅V, L⁆ : Subgroup G) : Set G)).inv_mem
          (hLU hl)) u).1 hu
        simpa using this
    have hzL : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ L := by
      have h1 : x * (l : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hn hxX) l).1 hl
      exact L.mul_mem h1 (L.inv_mem hl)
    have hzU : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu₁ := hlU' u hu
      have h2 : x⁻¹ * ((l : G)⁻¹ * u * (l : G)) * x = (l : G)⁻¹ * u * (l : G) := by
        have := hxc _ hu₁
        calc x⁻¹ * ((l : G)⁻¹ * u * (l : G)) * x
            = x⁻¹ * (x * ((l : G)⁻¹ * u * (l : G)) * x⁻¹) * x := by rw [this]
          _ = (l : G)⁻¹ * u * (l : G) := by group
      have key : (x * (l : G) * x⁻¹ * (l : G)⁻¹) * u * (x * (l : G) * x⁻¹ * (l : G)⁻¹)⁻¹ = u := by
        have e1 : (x * (l : G) * x⁻¹ * (l : G)⁻¹) * u * (x * (l : G) * x⁻¹ * (l : G)⁻¹)⁻¹ =
            x * (l : G) * (x⁻¹ * ((l : G)⁻¹ * u * (l : G)) * x) * (l : G)⁻¹ * x⁻¹ := by group
        rw [e1, h2]
        have e2 : x * (l : G) * ((l : G)⁻¹ * u * (l : G)) * (l : G)⁻¹ * x⁻¹ = x * u * x⁻¹ := by
          group
        rw [e2, hxc u hu]
      exact (mul_inv_eq_iff_eq_mul.1 key).symm
    have hzV : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ centralizer (V : Set G) := hCUV ⟨hzL, hzU⟩
    have hzN : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ normalizer (V : Set G) :=
      (normalizer (V : Set G)).mul_mem
        ((normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem hxN l.2)
          ((normalizer (V : Set G)).inv_mem hxN)) ((normalizer (V : Set G)).inv_mem l.2)
    have h1 := (convI_eq_one_iff hV ⟨_, hzN⟩).2 hzV
    have h2 : (⟨x * (l : G) * x⁻¹ * (l : G)⁻¹, hzN⟩ : ↥(normalizer (V : Set G))) =
        ⟨x, hxN⟩ * l * ⟨x, hxN⟩⁻¹ * l⁻¹ := Subtype.ext rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hyX : convI hV ⟨x, hxN⟩ ∈ autI hV X := convI_mem_autI hV hxX hxN
  have hycent : convI hV ⟨x, hxN⟩ ∈ centralizer
      ((quasithinGenFitting (autI hV X) : Subgroup (MulAut (IntMod V hV))) : Set _) := by
    rw [hfs, Subgroup.mem_centralizer_iff]
    intro φ hφ
    exact (hycomm φ hφ).symm
  have hyL : convI hV ⟨x, hxN⟩ ∈ autI hV L := by
    rw [← hfs]
    exact centralizer_quasithinGenFitting_le (autI hV X) ⟨hyX, hycent⟩
  obtain ⟨g, hgL, hg⟩ := (mem_autI hV).1 hyL
  have hgU : (g : G) ∈ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have huV : u ∈ V := (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLX.trans hXN)) hu
    have h1 := congrArg (fun φ : MulAut (IntMod V hV) => (φ (IntMod.mk hV ⟨u, huV⟩)).val) hg
    simp only [convI_apply_val] at h1
    have h2 : (g : G) * u * (g : G)⁻¹ = u := by
      change (g : G) * u * (g : G)⁻¹ = u
      rw [show (g : G) * u * (g : G)⁻¹ = x * u * x⁻¹ from h1]
      exact hxc u hu
    calc u * (g : G) = ((g : G) * u * (g : G)⁻¹) * g := by rw [h2]
      _ = g * u := by group
  have hgV := hCUV ⟨hgL, hgU⟩
  have h1 : convI hV g = 1 := (convI_eq_one_iff hV g).2 hgV
  rw [hg] at h1
  exact (convI_eq_one_iff hV ⟨x, hxN⟩).1 h1

theorem burnsideC137_a6_reduce [Finite G] {X T V L : Subgroup G} (hred : IsTwoReducedIn X V)
    (hT : IsSylowTwoOf T X) (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t)
    (hcomp : L ∈ cComp X) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hVL : ⁅V, L⁆ ≠ ⊥) :
    IsTwoReducedIn X ⁅V, L⁆ ∧ ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ ∧
      X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G) := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hXN : X ≤ normalizer (V : Set G) := hred.2.1
  have hLX : L ≤ X := le_of_mem_cComp hcomp
  have hn : X ≤ normalizer (L : Set G) := le_normalizer_of_prod hT hprod hcomp
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans hXN
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hUe : IsElemAbelian 2 ⁅V, L⁆ := B2F.isElemAbelian_mono hUV hV
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hXN hg) (hn hg)
  have hUU : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ :=
    SBd5.commutator_commutator_eq_self hperf hLN
      (fun x hx y hy => B2F.isElemAbelian_comm hV hx hy)
  have hle := burnsideC137_centralizer_U_le hred hT hprod hcomp hLq hVL
  have hCeq : X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G) :=
    le_antisymm (le_inf inf_le_left hle) (inf_le_inf_left X (Subgroup.centralizer_le hUV))
  refine ⟨⟨hUV.trans hred.1, hXU, hUe, fun D hDX hXD hD => ?_⟩, hUU, hCeq⟩
  have hD' : D ≤ centralizer (V : Set G) := by
    refine hred.2.2.2 D hDX hXD fun d hd => ?_
    obtain ⟨k, hk⟩ := hD d hd
    exact ⟨k, hle ⟨(pow_mem (hDX hd) _ : d ^ 2 ^ k ∈ X), hk⟩⟩
  exact hD'.trans (Subgroup.centralizer_le hUV)

structure burnsideC137_A6Entry [Finite G] (X L U R : Subgroup G) (hU : IsElemAbelian 2 U) :
    Prop where
  QC : pCoreOf 2 X = R ⊓ centralizer (U : Set G)
  hJ : ¬ thompsonJ R ≤ centralizer (U : Set G)
  fstarX : quasithinGenFitting (autI hU X) = autI hU L
  stab : IsStableFF (autI hU X) (offenderImagesConjIn hU X R)
  ffJP_le : ffJP (offenderImagesConjIn hU X R) (autI hU X) ≤ ffJ (autI hU X)
  fstar : quasithinGenFitting (ffJP (offenderImagesConjIn hU X R) (autI hU X)) = autI hU L
  quasi : CFSG.IsQuasisimple ↥(autI hU L)
  o2 : pCoreOf 2 (autI hU L) = ⊥
  surj : ∃ ψ : ↥(autI hU L) →* ↥(alternatingGroup (Fin 6)), Function.Surjective ψ
  card : ∃ z : ℕ, Odd z ∧ Nat.card ↥(autI hU L) = Nat.card ↥(alternatingGroup (Fin 6)) * z
  case1i : B51Case1i (ffJP (offenderImagesConjIn hU X R) (autI hU X)) (autI hU L)

section Certs

set_option linter.unusedSectionVars false


theorem burnsideC137_a6_entry_or_concl1
    [Finite G] {X T U L R : Subgroup G}
    (hSQ : SQTKGroup ↥X) (hred : IsTwoReducedIn X U) (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hcomp : L ∈ cComp X)
    (hUL : ⁅U, L⁆ ≠ ⊥) (halt : IsAltQuotient L (oTwoZIn L) 6) (hQR : pCoreOf 2 X ≤ R)
    (hRT : R ≤ T) :
    (∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ baum R ∧ (C.subgroupOf (baum R)).Characteristic ∧
        X ≤ normalizer (C : Set G)) ∨ burnsideC137_A6Entry X L U R hred.2.2.1 := by
  have hU : IsElemAbelian 2 U := hred.2.2.1
  have hLX : L ≤ X := le_of_mem_cComp hcomp
  have hn : X ≤ normalizer (L : Set G) := le_normalizer_of_prod hT hprod hcomp
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    isQuasisimple_of_altQuotient hcomp halt (by norm_num)
  obtain ⟨⟨-, hQC⟩, hqc, hF, hbranch⟩ :=
    B2_10_2 hU hred hQR hRT hT hLX hn hprod hUL (Or.inl hLq)
  have hUR : U ≤ R := (le_pCoreOf_of_reduced hred).trans hQR
  rcases hbranch with hb | ⟨hstab, hffle, hfstar⟩
  · exact Or.inl (concl1_of_baum_eq hT hred hQR hRT hUL hb)
  by_cases hJ : thompsonJ R ≤ centralizer (U : Set G)
  · refine Or.inl (concl1_of_baum_eq hT hred hQR hRT hUL ?_)
    have hJR : thompsonJ R ≤ R ⊓ centralizer (U : Set G) := le_inf (thompsonJ_le_self R) hJ
    rw [← hQC] at hJR
    rw [baum_eq_baum_centralizer hU hUR (hQC ▸ hJR), hQC]
  right
  have hquasi : CFSG.IsQuasisimple ↥(autI hU L) := by
    rcases hqc with h | h3
    · exact h
    · exfalso
      have hperf : Group.IsPerfect ↥(autI hU L) := by
        have : Group.IsPerfect ↥L := isPerfect_of_comm_eq (perfect_of_mem_cComp hcomp)
        exact Group.IsPerfect.ofSurjective (f := starHom hU L (hLX.trans hred.2.1))
          (starHom_surjective hU _)
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic ↥(autI hU L) := isCyclic_of_prime_card h3
      have hnil : Group.IsNilpotent ↥(autI hU L) := inferInstance
      have : Nontrivial ↥(autI hU L) :=
        Finite.one_lt_card_iff_nontrivial.1 (by rw [h3]; norm_num)
      exact Group.IsPerfect.not_isNilpotent _ hnil
  have ho2 : pCoreOf 2 (autI hU L) = ⊥ := pCoreOf_autI_L_eq_bot hU hred hLX hn
  have hψ := exists_surj_alt_aux (hV := hU) hred hLX hn halt hquasi (by norm_num)
  have hz := card_of_surj_alt hquasi ho2 (by norm_num) hψ
  obtain ⟨z, hzo, hzc⟩ := hz
  have hcase1i := b51Case1i_ffJP hU
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
    asA21SQTKSection asA36NoOddCover_holds hSQ hred.2.1 hLX hstab hfstar hquasi ho2
    (by norm_num : 6 = 5 ∨ 6 = 6 ∨ 6 = 7) hzo hzc
  exact ⟨hQC, hJ, hF, hstab, hffle, hfstar, hquasi, ho2, hψ, ⟨z, hzo, hzc⟩, hcase1i⟩

end Certs

theorem burnsideC137_a6_classes [Finite G] {X L U R : Subgroup G} {hU : IsElemAbelian 2 U}
    (E : burnsideC137_A6Entry X L U R hU) (hcomm : commV (autI hU L) = ⊤) :
    ClassCases (autI hU L) ⊤ (fixV (autI hU L)) 6 := by
  have hB := E.case1i.2.1
  rw [hcomm, inf_top_eq] at hB
  exact classify (by norm_num) E.card E.surj hB

end CFSG.ASVolI
