module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Frat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Zc
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open S18 (tilOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16t_l4_exists_noncyclic_three_lbar (hS : S16tL4Setting D V₀ V L hV) :
    ∃ E : Subgroup (MulAut (Vtil V₀ V hV)),
      E ≤ lBar V₀ V hV L ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E := by
  classical
  let H := lBar V₀ V hV L
  have hcard : Nat.card ↥H = 20160 := s16t_l4_card_lbar hS
  obtain ⟨Q⟩ := Sylow.nonempty (p := 3) (G := ↥H)
  let K : Subgroup ↥H := Q.toSubgroup
  let E : Subgroup (MulAut (Vtil V₀ V hV)) := K.map H.subtype
  have hE : E ≤ lBar V₀ V hV L := Subgroup.map_subtype_le _
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
  let g' : ↥(Mbar D.M V₀ V hV) :=
    ⟨((g : ↥H) : MulAut (Vtil V₀ V hV)), s16t_l4_lbar_le_mbar hS (g : ↥H).2⟩
  have hg'ord : orderOf g' = orderOf g := by
    show orderOf (⟨((g : ↥H) : MulAut (Vtil V₀ V hV)),
      s16t_l4_lbar_le_mbar hS (g : ↥H).2⟩ : ↥(Mbar D.M V₀ V hV)) = orderOf g
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  exact s16t_l4_mbar_not_nine hS g' (hg'ord.symm ▸ h9g)

theorem s16t_l4_fix_of_inf (hS : S16tL4Setting D V₀ V L hV) (h61 : UC6.R6_1 D)
    {Y : Subgroup G} (hY : S16tL4Pack D V₀ V L hV Y) {w : G} (hw : w ∈ V)
    (hpt : Close16PtStab (lBar V₀ V hV L) (tilOf V₀ V hV w hw)) {N : Subgroup G}
    (hN : rankThreeIsMaxTwoLocal N) (hZN : Y ⊓ centralizer ({w} : Set G) ≤ N)
    (hNM : ¬ N ≤ D.M) : ∀ x ∈ Y ⊓ N, ⁅x, w⁆ ∈ V₀ := by
  classical
  let Z := Y ⊓ centralizer ({w} : Set G)
  let w' := tilOf V₀ V hV w hw
  let Hb := lBar V₀ V hV L
  let St := MulAction.stabilizer (MulAut (Vtil V₀ V hV)) w'
  have hM : D.M ≤ stabTil V₀ V := s16t_l4_le_stabTil hS
  have hbar : barSub V₀ V hV Z = Hb ⊓ St := s16t_l4_barSub_cent_eq hS hY hw hpt
  have hZle : Z ≤ Y ⊓ N := le_inf inf_le_left hZN
  let J := barSub V₀ V hV (Y ⊓ N)
  have hle1 : Hb ⊓ St ≤ J := hbar ▸ barSub_mono V₀ V hV hZle
  have hle2 : J ≤ Hb := (barSub_mono V₀ V hV inf_le_left).trans (le_of_eq hY.bar_eq)
  rcases hpt.maximal J hle1 hle2 with hJ | hJ
  · intro x hx
    have hxM : x ∈ D.M := hY.le hx.1
    have hxS : x ∈ stabTil V₀ V := hM hxM
    have hxJ : actTil V₀ V hV ⟨x, hxS⟩ ∈ J := actTil_mem_barSub V₀ V hV hx hxS
    rw [hJ] at hxJ
    have hxw : actTil V₀ V hV ⟨x, hxS⟩ w' = w' := by
      simpa only [MulAut.smul_def] using MulAction.mem_stabilizer_iff.1 hxJ.2
    exact (s16t_l4_actTil_tilOf_eq_iff ⟨x, hxS⟩ hw).1 hxw
  · exfalso
    obtain ⟨E, hEHb, hEp, hEnc⟩ := s16t_l4_exists_noncyclic_three_lbar hS
    have hEJ : E ≤ J := hJ.symm ▸ hEHb
    have hPY : Y ⊓ N ≤ D.M := inf_le_left.trans hY.le
    obtain ⟨P, hPJ, hPp, hPE⟩ :=
      s16t_l4_exists_lift_barSub hM hPY hEJ (p := 3) (by norm_num) hEp
    have hnc : ¬ IsCyclic ↥(barSub V₀ V hV P) := by rw [hPE]; exact hEnc
    have hPnc : ¬ IsCyclic ↥P := s16t_l4_not_isCyclic_of_barSub hM (hPJ.trans hPY) hnc
    have h3 : 3 ∈ D.sig := by rw [hS.shape.2.2]; simp
    have huniq : UniqueMax D.M P := h61 3 h3 P (hPJ.trans hPY) hPp hPnc
    have hNmem : N ∈ calMOf P := ⟨hN, hPJ.trans inf_le_right⟩
    rw [huniq] at hNmem
    have hNMD : N = D.M := by simpa using hNmem
    exact hNM (le_of_eq hNMD)

theorem s16t_l4_opp_mem_calC (hS : S16tL4Setting D V₀ V L hV) {Y : Subgroup G}
    (hY : S16tL4Pack D V₀ V L hV Y) {w : G} (hw : w ∈ V)
    (hpt : Close16PtStab (lBar V₀ V hV L) (tilOf V₀ V hV w hw)) {N : Subgroup G}
    (hZN : Y ⊓ centralizer ({w} : Set G) ≤ N) (hfix : ∀ x ∈ Y ⊓ N, ⁅x, w⁆ ∈ V₀) :
    Opp 3 (Y ⊓ centralizer ({w} : Set G)) ∈ calC (N ⊓ D.M) := by
  let Z := Y ⊓ centralizer ({w} : Set G)
  obtain ⟨Ψ, hΨ, -⟩ := s16t_l4_zc_quot hS hY hw hpt
  have hYc : ∀ y ∈ Y, ∀ u ∈ V₀, y * u = u * y := fun y hy u hu =>
    (Subgroup.mem_centralizer_iff.1 (s16t_l4_le_centralizer_v0 hS hY hy) u hu).symm
  have hZY : Z ≤ Y ⊓ N := le_inf inf_le_left hZN
  have hYN : Y ⊓ N ≤ N ⊓ D.M := le_inf inf_le_right (inf_le_left.trans hY.le)
  have hYNnormal : ((Y ⊓ N).subgroupOf (N ⊓ D.M)).Normal := by
    haveI := hY.normal
    have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A' := Y) (A := D.M) N
    rwa [inf_comm D.M N] at h
  have hZnormal : (Z.subgroupOf (Y ⊓ N)).Normal := by
    refine ⟨fun z hz g => ?_⟩
    have hzZ : (z : G) ∈ Z := hz
    have hxN := hfix (g : G) g.2
    have hcomm := s16t_l4_comm_conj hYc (Subgroup.mem_inf.1 g.2).1 hzZ.1 hxN
      (commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_singleton_iff.1 hzZ.2))
    refine Subgroup.mem_inf.2 ⟨Y.mul_mem (Y.mul_mem (Subgroup.mem_inf.1 g.2).1 hzZ.1)
      (Y.inv_mem (Subgroup.mem_inf.1 g.2).1), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.1 hcomm
  have hsubYN : CFSG.Open.IsSubnormal (Y ⊓ N) (N ⊓ D.M) :=
    CFSG.Open.IsSubnormal.step hYN hYNnormal (CFSG.Open.IsSubnormal.refl (N ⊓ D.M))
  have hsub : CFSG.Open.IsSubnormal Z (N ⊓ D.M) :=
    CFSG.Open.IsSubnormal.step hZY hZnormal hsubYN
  exact ⟨CFSG.Open.IsSubnormal.step (close16_opp_le 3 Z) (close16_opp_normal 3 Z) hsub,
    hΨ.opp_perfect, hΨ.opp_quasisimple⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
