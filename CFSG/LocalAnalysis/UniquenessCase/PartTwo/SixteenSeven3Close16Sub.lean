module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Frat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Zc
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem close16_exists_noncyclic_three_lbar (hS : Close16Setting D V L hV) :
    ∃ E : Subgroup (MulAut (Vtil ⊥ V hV)),
      E ≤ lBar ⊥ V hV L ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E := by
  classical
  let H := lBar ⊥ V hV L
  have hcard : Nat.card ↥H = 20160 := close16_card_lbar hS
  obtain ⟨Q⟩ := Sylow.nonempty (p := 3) (G := ↥H)
  let K : Subgroup ↥H := Q.toSubgroup
  let E : Subgroup (MulAut (Vtil ⊥ V hV)) := K.map H.subtype
  have hE : E ≤ lBar ⊥ V hV L := Subgroup.map_subtype_le _
  have hEp : IsPGroup 3 ↥E := Q.isPGroup'.map H.subtype
  refine ⟨E, hE, hEp, ?_⟩
  intro hcyc
  have hcycQ : IsCyclic ↥K :=
    isCyclic_of_injective
      (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective).injective
  haveI := hcycQ
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥K)
  have h9Q : 9 ∣ Nat.card ↥K := by
    have h1 : 3 ^ 2 ∣ Nat.card ↥H := by rw [hcard]; norm_num
    have h2 := Q.pow_dvd_card_of_pow_dvd_card h1
    simpa using h2
  have h9g : 9 ∣ orderOf g := by rw [hg]; exact h9Q
  let g' : ↥(Mbar D.M ⊥ V hV) :=
    ⟨((g : ↥H) : MulAut (Vtil ⊥ V hV)), close16_lbar_le_mbar hS (g : ↥H).2⟩
  have hg'ord : orderOf g' = orderOf g := by
    show orderOf (⟨((g : ↥H) : MulAut (Vtil ⊥ V hV)),
      close16_lbar_le_mbar hS (g : ↥H).2⟩ : ↥(Mbar D.M ⊥ V hV)) = orderOf g
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  exact close16_mbar_not_nine hS g' (hg'ord.symm ▸ h9g)

theorem close16_inf_eq (hS : Close16Setting D V L hV) (h61 : UC6.R6_1 D) {Y : Subgroup G}
    (hY : Close16Pack D V L hV Y) {z : G} (hz : z ∈ V ⊓ centralizer (D.T : Set G)) (hz1 : z ≠ 1)
    {N : Subgroup G} (hN : rankThreeIsMaxTwoLocal N) (hZN : Y ⊓ centralizer ({z} : Set G) ≤ N)
    (hNM : ¬ N ≤ D.M) : Y ⊓ N = Y ⊓ centralizer ({z} : Set G) := by
  classical
  let Z := Y ⊓ centralizer ({z} : Set G)
  let w := close16Vec V hV z (Subgroup.mem_inf.1 hz).1
  let Hb := lBar ⊥ V hV L
  let St := MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) w
  have hM : D.M ≤ stabTil ⊥ V := close16_le_stabTil hS
  have hbar : barSub ⊥ V hV Z = Hb ⊓ St :=
    close16_barSub_cent_eq hS hY (Subgroup.mem_inf.1 hz).1
  have hpt : Close16PtStab Hb w := close16_ptStab_central hS hz hz1
  have hZle : Z ≤ Y ⊓ N := le_inf inf_le_left hZN
  let J := barSub ⊥ V hV (Y ⊓ N)
  have hle1 : Hb ⊓ St ≤ J := hbar ▸ barSub_mono ⊥ V hV hZle
  have hle2 : J ≤ Hb := (barSub_mono ⊥ V hV inf_le_left).trans (le_of_eq hY.bar_eq)
  rcases hpt.maximal J hle1 hle2 with hJ | hJ
  · apply le_antisymm
    · intro x hx
      have hxM : x ∈ D.M := hY.le hx.1
      have hxS : x ∈ stabTil ⊥ V := hM hxM
      have hxJ : actTil ⊥ V hV ⟨x, hxS⟩ ∈ J := actTil_mem_barSub ⊥ V hV hx hxS
      rw [hJ] at hxJ
      have hxw : actTil ⊥ V hV ⟨x, hxS⟩ w = w := by
        simpa only [MulAut.smul_def] using MulAction.mem_stabilizer_iff.1 hxJ.2
      have hxz : x * z = z * x :=
        (close16_actTil_vec_eq_iff ⟨x, hxS⟩ (Subgroup.mem_inf.1 hz).1).1 hxw
      exact Subgroup.mem_inf.2 ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.2 hxz⟩
    · exact hZle
  · exfalso
    obtain ⟨E, hEHb, hEp, hEnc⟩ := close16_exists_noncyclic_three_lbar hS
    have hEJ : E ≤ J := hJ.symm ▸ hEHb
    have hPY : Y ⊓ N ≤ D.M := inf_le_left.trans hY.le
    obtain ⟨P, hPJ, hPp, hPE⟩ :=
      close16_exists_lift_barSub hM hPY hEJ (p := 3) (by norm_num) hEp
    have hnc : ¬ IsCyclic ↥(barSub ⊥ V hV P) := by rw [hPE]; exact hEnc
    have hPnc : ¬ IsCyclic ↥P := close16_not_isCyclic_of_barSub hM (hPJ.trans hPY) hnc
    have h3 : 3 ∈ D.sig := by rw [hS.shape.2.2]; simp
    have huniq : UniqueMax D.M P := h61 3 h3 P (hPJ.trans hPY) hPp hPnc
    have hNmem : N ∈ calMOf P := ⟨hN, hPJ.trans inf_le_right⟩
    rw [huniq] at hNmem
    have hNMD : N = D.M := by simpa using hNmem
    exact hNM (le_of_eq hNMD)

theorem close16_opp_mem_calC (hS : Close16Setting D V L hV) {Y : Subgroup G}
    (hY : Close16Pack D V L hV Y) {z : G} (hz : z ∈ V ⊓ centralizer (D.T : Set G))
    (hz1 : z ≠ 1) {N : Subgroup G} (hYN : Y ⊓ N = Y ⊓ centralizer ({z} : Set G)) :
    Opp 3 (Y ⊓ centralizer ({z} : Set G)) ∈ calC (N ⊓ D.M) := by
  let Z := Y ⊓ centralizer ({z} : Set G)
  obtain ⟨Ψ, hΨ, -⟩ := close16_zc_quot hS hY hz hz1
  have hZle : Z ≤ N ⊓ D.M := by
    rw [show Z = Y ⊓ N from hYN.symm]
    exact le_inf inf_le_right (inf_le_left.trans hY.le)
  have hZnormal : (Z.subgroupOf (N ⊓ D.M)).Normal := by
    haveI := hY.normal
    rw [show Z = Y ⊓ N from hYN.symm]
    have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A' := Y) (A := D.M) N
    rwa [inf_comm D.M N] at h
  have hsub : CFSG.Open.IsSubnormal Z (N ⊓ D.M) :=
    CFSG.Open.IsSubnormal.step hZle hZnormal (CFSG.Open.IsSubnormal.refl (N ⊓ D.M))
  exact ⟨CFSG.Open.IsSubnormal.step (close16_opp_le 3 Z) (close16_opp_normal 3 Z) hsub,
    hΨ.opp_perfect, hΨ.opp_quasisimple⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
