module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABAA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResSum
import CFSG.Quasithin.Background.D216Restrict
import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_l3_data_faithful {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} (D : L3Data L U Z) {l : MulAut V} (hl : l ∈ L)
    (h : ∀ u ∈ U, l u = u) : l = 1 := by
  obtain ⟨γ, rfl⟩ := D.exists_rho hl
  have hγ : γ = 1 := by
    apply L3.act_injective
    intro w
    obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd w)
    have hmem : D.rho γ (u : V) ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
    have h2 := D.β_rho γ (u : V) u.2 hmem
    have h3 : (⟨D.rho γ (u : V), hmem⟩ : ↥U) = u := Subtype.ext (h _ u.2)
    rw [h3, hu] at h2
    exact (Multiplicative.ofAdd.injective h2).symm
  rw [hγ, map_one]

theorem s16h_e3_l3_rk_inf_fixV_le_one (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsSLn ↥L 3 1) {J : Subgroup W} (hJc : commSub J L = J)
    (hJ : BinaryNaturalSL L J (J ⊓ fixV L) 3 1) :
    rk ↥(J ⊓ fixV L) ≤ 1 := by
  obtain ⟨D0⟩ := hJ.toL3Coord
  have hJinv : ∀ x ∈ L, ∀ u ∈ J, x u ∈ J := fun x hx u hu => D0.inv_U x hx u hu
  have hLJ : L ≤ stabSub J := fun x hx => by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h := hJinv x⁻¹ (L.inv_mem hx) (x u) hu
      simpa using h
    · exact hJinv x hx u
  let incl : ↥L →* ↥(stabSub J) := Subgroup.inclusion hLJ
  let ρ : ↥L →* ↥(autSub L J) :=
    ((resHom J).comp incl).codRestrict (autSub L J) fun x => by
      exact Subgroup.mem_map.mpr
        ⟨incl x, Subgroup.mem_subgroupOf.mpr (by
          rw [Subgroup.coe_inclusion]
          exact x.2), rfl⟩
  have hρsurj : Function.Surjective ρ := by
    intro y
    have hy : y.1 ∈ (L.subgroupOf (stabSub J)).map (resHom J) := by
      simpa [autSub] using y.2
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    have hgL : (g : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp hg
    refine ⟨⟨(g : MulAut W), hgL⟩, ?_⟩
    apply Subtype.ext
    change resHom J (incl ⟨(g : MulAut W), hgL⟩) = y.1
    rw [show incl ⟨(g : MulAut W), hgL⟩ = g from Subtype.ext rfl]
    exact hgy
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hfix : ∀ u : ↥J, (a : MulAut W) (u : W) = u := by
      intro u
      have h1 : resHom J (incl a) = 1 := by
        have ha' : (ρ a : MulAut ↥J) = 1 := by rw [ha]; rfl
        exact ha'
      have h2 := congrArg (fun f : MulAut ↥J => ((f u : ↥J) : W)) h1
      simpa [incl, resHom_apply, Subgroup.coe_inclusion] using h2
    obtain ⟨D⟩ := hJ.toL3Coord
    exact Subtype.ext (s16h_e3_l3_data_faithful D a.2 (fun u hu => hfix ⟨u, hu⟩))
  let e : ↥L ≃* ↥(autSub L J) := MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  have hL' : IsSLn ↥(autSub L J) 3 1 := by
    obtain ⟨K, hK, hKfin, hKcard, ⟨φ⟩⟩ := hL
    exact ⟨K, hK, hKfin, hKcard, ⟨e.symm.trans φ⟩⟩
  have hmap1 : commSub J L = (commV (autSub L J)).map J.subtype :=
    commSub_eq_map_commV (A := L) (U := J) hLJ
  have htopmap : ((⊤ : Subgroup ↥J)).map J.subtype = J := by
    ext v
    constructor
    · rintro ⟨u, -, rfl⟩
      exact u.2
    · intro hv
      exact ⟨⟨v, hv⟩, Subgroup.mem_top _, rfl⟩
  have hmap : (commV (autSub L J)).map J.subtype = J := by
    rw [← hmap1, hJc]
  have hcommV : commV (autSub L J) = ⊤ :=
    Subgroup.map_injective J.subtype_injective (by rw [hmap, htopmap])
  have hcomm : commSub (⊤ : Subgroup ↥J) (autSub L J) = ⊤ := by
    rw [commV_eq_commSub] at hcommV
    exact hcommV
  obtain ⟨K, hK, hKfin, hKcard, hR⟩ := hJ
  have hR' := s16h_realizes_autSub hLJ le_rfl inf_le_left hR
  have hZeq : (J ⊓ fixV L).subgroupOf J = fixV (autSub L J) := by
    ext u
    rw [Subgroup.mem_subgroupOf, mem_fixV_autSub]
    constructor
    · intro hu
      exact fun g hg _ => mem_fixV.mp hu.2 g hg
    · intro hu
      exact ⟨u.2, mem_fixV.mpr (fun g hg => hu g hg (hLJ hg))⟩
  have hnat : BinaryNaturalSL (autSub L J) ⊤ (⊤ ⊓ fixV (autSub L J)) 3 1 :=
    ⟨K, hK, hKfin, hKcard, by
      simpa [Subgroup.subgroupOf_self, top_inf_eq, hZeq] using hR'⟩
  have hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (autSub L J)
      (commSub ⊤ (autSub L J)) (commSub ⊤ (autSub L J) ⊓ fixV (autSub L J)) 1 := by
    rw [hcomm]
    refine ⟨fun _ => ⊤, ?_, ?_, ?_, ?_⟩
    · intro _
      exact le_top
    · intro i
      have hbot : (⨆ (j : Fin 1) (_ : j ≠ i), (⊤ : Subgroup ↥J)) = ⊥ := by
        rw [iSup_eq_bot]
        intro j
        rw [iSup_eq_bot]
        intro hij
        exact absurd (Subsingleton.elim j i) hij
      rw [hbot, sup_bot_eq]
      exact inf_le_right
    · have htop : (⨆ _ : Fin 1, (⊤ : Subgroup ↥J)) = ⊤ := by
        apply le_antisymm le_top
        exact le_iSup (fun _ : Fin 1 => (⊤ : Subgroup ↥J)) 0
      rw [htop, sup_top_eq]
    · intro _
      exact hnat
  have hL3sum : s16h_H5L3Sum (autSub L J) (commSub ⊤ (autSub L J))
      (commSub ⊤ (autSub L J) ⊓ fixV (autSub L J)) 1 := ⟨hL', hsum⟩
  have hW' : ∀ w : ↥J, w ^ 2 = 1 := fun w => Subtype.ext (hW (w : W))
  have hle := s16h_e3_l3_sumOfNat_fix_le hW' hL3sum
  rw [hcomm, top_inf_eq, rk_fixV_autSub hLJ] at hle
  exact hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo