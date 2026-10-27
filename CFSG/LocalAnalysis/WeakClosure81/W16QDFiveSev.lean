module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDFiveModelA
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup

variable {G : Type} [Group G] [Finite G]

section Certified


namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

theorem w16q_seven_fifteen_apply [Finite X] (d : DichCfg M V₀ V U S H φ)
    (D : ModDataE H (iSub16 V H)) {p : ℕ}
    (h : Heis2p X (SevenK.barSub (conjClosure V H) φ V) p)
    (hexp : Monoid.exponent ↥(fusionOddCore X) = p)
    (hfaith : conjClosure V H ⊓ centralizer (iSub16 V H : Set G) ≤ iSub16 V H) :
    ∃ k : ℕ,
      Nat.card ↥(iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) = 2 ^ (p * k) ∧
      Nat.card ↥(UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V) ⊓
          iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
            (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) =
        2 ^ ((p - 1) * k / 2) ∧
      ⁅iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)),
        centerMod (kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)))
          (iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
            (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)))⁆ =
        iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨h.prime⟩
  let V' : Subgroup (VG (D.img H)) := UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V)
  let E' : Subgroup (VG (D.img H)) := vHat (D.img H)
  let K' : Subgroup (VG (D.img H)) := kSub V' ⊤ E'
  let I' : Subgroup (VG (D.img H)) := iSub V' ⊤ E'
  have hHyp : SevenK.Hyp716 V' ⊤ E' :=
    IsMinFam16.hyp716_UAOf_img d.cfg.one d.cfg.five d.cfg.std d.cfg.cex d.cfg.min d.cfg.not_le D
  obtain ⟨ψ, hψbar, hψproj⟩ :=
    IsMinFam16.exists_isBarMap_kSub_UAOf_img d.cfg.one d.cfg.five d.cfg.std d.cfg.cex
      d.cfg.min d.cfg.not_le D
  obtain ⟨θ, hθφ⟩ := w16q_exists_theta d D hfaith
  let O : Subgroup X := fusionOddCore X
  let Oθ : Subgroup ↥(D.img (conjClosure V H)) := O.map θ.toMonoidHom
  let Q' : Subgroup (VG (D.img H)) := (Oθ.comap ψ).map K'.subtype
  have hQK : Q' ≤ K' := Subgroup.map_subtype_le _
  have hIK : I' ≤ K' := iSub_le_kSub V' ⊤ E'
  have hIQ : I' ≤ Q' := by
    intro i hi
    refine Subgroup.mem_map.mpr ⟨⟨i, hIK hi⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, (hψbar.ker_iff ⟨i, hIK hi⟩).mpr hi]
    exact Oθ.one_mem
  have hQ'sub : Q'.subgroupOf K' = Oθ.comap ψ := by
    ext k
    rw [Subgroup.mem_subgroupOf]
    change (k : VG (D.img H)) ∈ Q' ↔ ψ k ∈ Oθ
    change (k : VG (D.img H)) ∈ (Oθ.comap ψ).map K'.subtype ↔ ψ k ∈ Oθ
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, hsk⟩
      have hsk' : s = k := Subtype.ext hsk
      rwa [hsk'] at hs
    · exact fun hk => ⟨k, hk, rfl⟩
  have hOθ_normal : Oθ.Normal :=
    Subgroup.Normal.map (fusionOddCore_normal X) θ.toMonoidHom θ.surjective
  have hQnorm : (Q'.subgroupOf K').Normal := by
    rw [hQ'sub]
    exact hOθ_normal.comap ψ
  have hVK : V ≤ conjClosure V H := le_conjClosure V H
  have hVH : V ≤ H := hVK.trans d.cfg.conjClosure_le_H
  have hVDH : D.img V ≤ D.img H := D.img_mono hVH
  have hV'K' : V' ≤ K' := le_kSub hHyp.toHyp73.mem
  have hprojV : V'.map (projG (D.img H)) = D.img V :=
    map_projG_wHat_sup_aHat (G := D.img H) (W := D.conjImgSpace V₀ V (D.img V))
      (A := D.img V) hVDH
  have hYmap : (SevenK.barSub (conjClosure V H) φ V).map θ.toMonoidHom =
      (D.img V).subgroupOf (D.img (conjClosure V H)) := by
    let ρK : ↥(conjClosure V H) →* ↥(D.img (conjClosure V H)) :=
      (D.ρ.comp (Subgroup.inclusion d.cfg.conjClosure_le_H)).codRestrict _
        (fun k => D.mem_img.mpr
          ⟨Subgroup.inclusion d.cfg.conjClosure_le_H k, by simpa using k.2, rfl⟩)
    have hθρK : θ.toMonoidHom.comp φ = ρK :=
      MonoidHom.ext fun k => Subtype.ext (congrArg Subtype.val (hθφ k))
    rw [SevenK.barSub, Subgroup.map_map, hθρK]
    apply le_antisymm
    · rintro z ⟨k, hk, rfl⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      exact D.mem_img.mpr ⟨Subgroup.inclusion d.cfg.conjClosure_le_H k,
        Subgroup.mem_subgroupOf.mp hk, rfl⟩
    · intro z hz
      obtain ⟨h, hh, hhρ⟩ := D.mem_img.mp (Subgroup.mem_subgroupOf.mp hz)
      refine Subgroup.mem_map.mpr ⟨⟨(h : G), hVK hh⟩, hh, ?_⟩
      apply Subtype.ext
      show D.ρ (Subgroup.inclusion d.cfg.conjClosure_le_H ⟨(h : G), hVK hh⟩) = (z : LGL 2 D.W)
      rw [show Subgroup.inclusion d.cfg.conjClosure_le_H ⟨(h : G), hVK hh⟩ = h from
        Subtype.ext rfl]
      exact hhρ
  have hXmap : (⊤ : Subgroup X).map θ.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective θ.toMonoidHom θ.surjective
  have htop : (⊤ : Subgroup ↥(D.img (conjClosure V H))) =
      Oθ ⊔ (D.img V).subgroupOf (D.img (conjClosure V H)) := by
    rw [← hXmap, ← h.sup_eq, Subgroup.map_sup, hYmap]
    exact sup_comm _ _
  have hQ'map : (Q'.subgroupOf K').map ψ = Oθ := by
    rw [hQ'sub, Subgroup.map_comap_eq,
      show ψ.range = ⊤ from MonoidHom.range_eq_top.2 hψbar.surjective, top_inf_eq]
  have hV'map : (V'.subgroupOf K').map ψ =
      (D.img V).subgroupOf (D.img (conjClosure V H)) := by
    apply le_antisymm
    · rintro y ⟨k, hk, rfl⟩
      have hk' : (k : VG (D.img H)) ∈ V' := Subgroup.mem_subgroupOf.mp hk
      have hmem : projG (D.img H) (k : VG (D.img H)) ∈ V'.map (projG (D.img H)) :=
        ⟨(k : VG (D.img H)), hk', rfl⟩
      rw [hprojV] at hmem
      exact Subgroup.mem_subgroupOf.mpr (by simpa only [hψproj k] using hmem)
    · intro y hy
      have hy' : (y : LGL 2 D.W) ∈ D.img V := Subgroup.mem_subgroupOf.mp hy
      rw [← hprojV] at hy'
      obtain ⟨x, hxV', hxproj⟩ := hy'
      refine Subgroup.mem_map.mpr ⟨⟨x, hV'K' hxV'⟩, hxV', ?_⟩
      apply Subtype.ext
      rw [hψproj ⟨x, hV'K' hxV'⟩]
      exact hxproj
  have hkerψ : ψ.ker = I'.subgroupOf K' := by
    ext k
    rw [MonoidHom.mem_ker]
    exact hψbar.ker_iff k
  have hA : Q' ⊔ V' ≤ K' := sup_le hQK hV'K'
  have hHmap : ((Q' ⊔ V').subgroupOf K').map ψ = ⊤ := by
    rw [Subgroup.subgroupOf_sup hQK hV'K', Subgroup.map_sup, hQ'map, hV'map, htop]
  have hHtop : (Q' ⊔ V').subgroupOf K' = ⊤ := by
    have hrange : ψ.range = ⊤ := MonoidHom.range_eq_top.2 hψbar.surjective
    have hHmap' : ((Q' ⊔ V').subgroupOf K').map ψ = ψ.range := by rw [hHmap, hrange]
    have hcodisj : (Q' ⊔ V').subgroupOf K' ⊔ ψ.ker = ⊤ :=
      codisjoint_iff.mp (Subgroup.map_eq_range_iff.mp hHmap')
    have hker_le : ψ.ker ≤ (Q' ⊔ V').subgroupOf K' := by
      rw [hkerψ]
      intro k hk
      exact (hIQ.trans le_sup_left) hk
    rwa [sup_eq_left.mpr hker_le] at hcodisj
  have hmaptop : (⊤ : Subgroup ↥K').map K'.subtype = K' := by
    rw [← Subgroup.subgroupOf_self (H := K'), Subgroup.map_subgroupOf_eq_of_le le_rfl]
  have hKQV : K' = Q' ⊔ V' := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hA, hHtop, hmaptop]
  let ψQ : ↥Q' →* ↥(D.img (conjClosure V H)) := ψ.comp (Subgroup.inclusion hQK)
  have hkerψQ : ψQ.ker = I'.subgroupOf Q' := by
    ext q
    rw [MonoidHom.mem_ker]
    exact hψbar.ker_iff (Subgroup.inclusion hQK q)
  have hψQrange : ψQ.range = Oθ := by
    rw [MonoidHom.range_eq_map]
    have hcomp : (⊤ : Subgroup ↥Q').map ψQ =
        ((⊤ : Subgroup ↥Q').map (Subgroup.inclusion hQK)).map ψ := by
      rw [Subgroup.map_map]
    rw [hcomp, show (⊤ : Subgroup ↥Q').map (Subgroup.inclusion hQK) = Q'.subgroupOf K' from
      (MonoidHom.range_eq_map (Subgroup.inclusion hQK)).symm.trans
        (Subgroup.inclusion_range hQK)]
    exact hQ'map
  haveI hInorm : (I'.subgroupOf Q').Normal := hkerψQ ▸ MonoidHom.normal_ker ψQ
  let ψQ' : ↥Q' →* ↥Oθ :=
    ψQ.codRestrict Oθ (fun q => hψQrange ▸ MonoidHom.mem_range.mpr ⟨q, rfl⟩)
  have hkerψQ' : ψQ'.ker = I'.subgroupOf Q' := by
    rw [MonoidHom.ker_codRestrict, hkerψQ]
  have hsurjψQ' : Function.Surjective ψQ' := by
    intro z
    have hz : (z : ↥(D.img (conjClosure V H))) ∈ ψQ.range := by
      rw [hψQrange]
      exact z.2
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hz
    exact ⟨q, Subtype.ext hq⟩
  let e : (↥Q' ⧸ I'.subgroupOf Q') ≃* ↥Oθ :=
    (QuotientGroup.quotientMulEquivOfEq hkerψQ').symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψQ' hsurjψQ')
  haveI hextOθ : CFSG.IsExtraspecial p ↥Oθ := by
    haveI : CFSG.IsExtraspecial p ↥O := h.ext
    exact w16q_isExtraspecial_of_mulEquiv
      (Subgroup.equivMapOfInjective O θ.toMonoidHom θ.injective)
  have hcardOθ : Nat.card ↥Oθ = Nat.card ↥O :=
    Nat.card_congr (Subgroup.equivMapOfInjective O θ.toMonoidHom θ.injective).symm.toEquiv
  have hexpOθ : Monoid.exponent ↥Oθ = Monoid.exponent ↥O :=
    Monoid.exponent_eq_of_mulEquiv (Subgroup.equivMapOfInjective O θ.toMonoidHom θ.injective).symm
  have hcard : Nat.card (↥Q' ⧸ I'.subgroupOf Q') = p ^ 3 :=
    (Nat.card_congr e.toEquiv).trans (hcardOθ.trans h.card_O)
  have hexp' : Monoid.exponent (↥Q' ⧸ I'.subgroupOf Q') = p :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (hexpOθ.trans hexp)
  haveI hext : CFSG.IsExtraspecial p (↥Q' ⧸ I'.subgroupOf Q') :=
    w16q_isExtraspecial_of_mulEquiv e.symm
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
    seven_fifteen (G := VG (D.img H)) (p := p) h.ne_two hHyp.toHyp73.elemAbelian
      hHyp.toHyp73.ti hHyp.toHyp73.abelian le_top hHyp.toHyp73.normal (fun _ _ => le_top)
      hHyp.toHyp73.mem hQK hIQ hQnorm hKQV hcard hexp'
  exact ⟨k, hk1, hk3, hk4⟩

end DichCfg

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
