module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXD
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXEA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX.isPGroup
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

private theorem w16g_even_W6_cost (h : Cfg133 A t 3) {z : MulAut W}
    {N : Subgroup (MulAut W)} (hD : Data8 A t z N)
    (hW6 : commSub ⊤ (Subgroup.zpowers z) ∈
      s13IsoComps (conjClosure A (Subgroup.zpowers z)))
    (hfix : ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)),
      U.map t.toMonoidHom = U) :
    Even (rk ↥(commSub (commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t))) := by
  classical
  obtain ⟨hXe, hXA, -, -⟩ := w16g_s13_eight_X_facts h hD
  set X : Subgroup (MulAut W) := conjClosure A (Subgroup.zpowers z) with hXdef
  set W6 : Subgroup W := commSub ⊤ (Subgroup.zpowers z) with hW6def
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian h.hp (by norm_num) hXe
  have htt : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun x hx => hXA t h.htA x hx
  have hW6mem : W6 ∈ s13IsoComps X := by rw [hW6def, hXdef]; exact hW6
  have hsU : ∀ u ∈ W6, t u ∈ W6 := by
    intro u hu
    have h1 : t u ∈ W6.map t.toMonoidHom := Subgroup.mem_map_of_mem t.toMonoidHom hu
    rwa [hfix W6 hW6mem] at h1
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  have hoddz : Odd (Nat.card ↥(Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hD.hz3]; norm_num
  have hW6ne : W6 ≠ ⊥ := by
    intro hbot
    have h6 : rk ↥W6 = 6 := by rw [hW6def]; exact hD.hrkz
    rw [hbot, rk_bot] at h6
    omega
  have hHmem := s13KerOn_mem_hyperplanes h.hW h.hp (by norm_num : (3 : ℕ) ≠ 2) hXe hW6mem
  have hHle : s13KerOn X W6 ≤ X := hHmem.1
  have hidx : (s13KerOn X W6).relIndex X = 3 := hHmem.2
  have hsH : ∀ x ∈ s13KerOn X W6, t * x * t⁻¹ ∈ s13KerOn X W6 :=
    w16g_normalizes_kerOn htt htX hsU
  have hzX : z ∈ X := by
    rw [hXdef]
    exact Subgroup.subset_closure ⟨1, A.one_mem, z, Subgroup.mem_zpowers z, by group⟩
  have hzH : z ∉ s13KerOn X W6 := by
    intro hzmem
    have hzcent : z ∈ centSub W6 := by
      have h := hzmem
      rw [s13KerOn] at h
      exact (Subgroup.mem_inf.mp h).2
    have hle : W6 ≤ fixV (Subgroup.zpowers z) := by
      intro u hu
      rw [mem_fixV_zpowers_iff_apply]
      exact (mem_centSub.mp hzcent) u hu
    have hbot : W6 = ⊥ := by
      have h1 : W6 ≤ fixV (Subgroup.zpowers z) ⊓ commSub ⊤ (Subgroup.zpowers z) :=
        le_inf hle le_rfl
      have h2 : fixV (Subgroup.zpowers z) ⊓ commSub ⊤ (Subgroup.zpowers z) = ⊥ :=
        CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW2 hoddz
      exact le_bot_iff.mp (h2 ▸ h1)
    exact hW6ne hbot
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hXe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := hXe.2
  have hcent : ∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ s13KerOn X W6 :=
    w16g_cent_of_fixed_outside hXc hX3 hHle hidx htt htX hsH hzX hzH hD.htz
  exact even_rk_commSub_fixed_central h.hW hXe htt htX hW6mem hsU hcent

private theorem w16g_rk_commSub_top_eq_W6 (h : Cfg133 A t 3) {z : MulAut W}
    {N : Subgroup (MulAut W)} (hD : Data8 A t z N)
    (htop : commSub ⊤ (conjClosure A (Subgroup.zpowers z)) = ⊤)
    (hW6 : commSub ⊤ (Subgroup.zpowers z) ∈
      s13IsoComps (conjClosure A (Subgroup.zpowers z)))
    (hfix : ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)),
      U.map t.toMonoidHom = U)
    (hoff : ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)),
      U ≠ commSub ⊤ (Subgroup.zpowers z) → commSub U (Subgroup.zpowers t) = ⊥) :
    rk ↥(commSub ⊤ (Subgroup.zpowers t)) =
      rk ↥(commSub (commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t)) := by
  classical
  obtain ⟨hXe, -, -, -⟩ := w16g_s13_eight_X_facts h hD
  set X : Subgroup (MulAut W) := conjClosure A (Subgroup.zpowers z) with hXdef
  set C : Set (Subgroup W) := s13IsoComps X with hCdef
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian h.hp (by norm_num) hXe
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fintype ↥C := Fintype.ofFinite _
  let F : ↥C → Subgroup W := Subtype.val
  have hF : iSupIndep F := by
    have h1 : sSupIndep C := by
      rw [hCdef, hXdef]
      exact s13IsoComps_sSupIndep h.hW hodd
    exact (sSupIndep_iff C).mp h1
  have hs : ∀ i : ↥C, ∀ u ∈ F i, t u ∈ F i := by
    intro i u hu
    have h := hfix (i : Subgroup W) i.2
    have h1 : t u ∈ (i : Subgroup W).map t.toMonoidHom :=
      Subgroup.mem_map_of_mem t.toMonoidHom hu
    rwa [h] at h1
  have hsup : (⨆ i : ↥C, F i) = ⊤ := by
    have h2 : (⨆ i : ↥C, F i) = commSub ⊤ X := by
      apply le_antisymm
      · refine iSup_le fun i => (s13IsoComps_le_commSub h.hW hodd i.2).2
      · rw [← iSup_s13IsoComps h.hW hodd]
        refine iSup_le fun U => iSup_le fun hU => ?_
        exact le_iSup (fun i : ↥C => F i) ⟨U, by rw [hCdef]; exact hU⟩
    rw [h2, hXdef]
    exact htop
  have hsum := rk_commSub_iSup_eq_sum h.hW t F hF hs
  rw [hsup] at hsum
  let i0 : ↥C := ⟨commSub ⊤ (Subgroup.zpowers z), by rw [hCdef, hXdef]; exact hW6⟩
  have hsingle : ∑ i : ↥C, rk ↥(commSub (F i) (Subgroup.zpowers t)) =
      rk ↥(commSub (commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t)) := by
    refine Finset.sum_eq_single i0 ?_ ?_
    · intro i _ hi
      have hne : (i : Subgroup W) ≠ commSub ⊤ (Subgroup.zpowers z) := by
        intro h
        exact hi (Subtype.ext h)
      have hz := hoff (i : Subgroup W) i.2 hne
      rw [hz, rk_bot]
    · intro hnot
      exact absurd (Finset.mem_univ i0) hnot
  rw [hsum, hsingle]

theorem s13_eight_cost_false (h : Cfg133 A t 3) {z : MulAut W} {N : Subgroup (MulAut W)}
    (hD : Data8 A t z N)
    (htop : commSub ⊤ (conjClosure A (Subgroup.zpowers z)) = ⊤)
    (hW6 : commSub ⊤ (Subgroup.zpowers z) ∈
      s13IsoComps (conjClosure A (Subgroup.zpowers z)))
    (hfix : ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)),
      U.map t.toMonoidHom = U)
    (hoff : ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)),
      U ≠ commSub ⊤ (Subgroup.zpowers z) → commSub U (Subgroup.zpowers t) = ⊥) :
    False := by
  have heven := w16g_even_W6_cost h hD hW6 hfix
  have hsum := w16g_rk_commSub_top_eq_W6 h hD htop hW6 hfix hoff
  obtain ⟨k, hk⟩ := heven
  rw [← hsum, hD.hrkt] at hk
  omega

end CFSG.LocalAnalysis.WeakClosure81
