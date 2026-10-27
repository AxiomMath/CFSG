module

public import CFSG.RankThree.GF2n.Tim79a34BigEnd
public import CFSG.RankThree.GF2n.Tim79a34IW
import all CFSG.GroupTheory.ConjActionModPCore

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType CFSG.LieType.Universal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

theorem BigEndHyp.exists_sp_data (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) :
    ∃ (f n : ℕ) (hn : 2 ≤ n) (hf : 2 ≤ f), 2 ^ f = qBar V H ∧
      ∃ (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
        (g : ↥(StatedSp n (GaloisField 2 f))),
      ((conjSub ((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup
        ((Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 : Fin n → ℤ))) g).map
          Φ.toMonoidHom = Vy V H) := by
  obtain ⟨f, hf, h2f, n, hn, Φ₀, hΦ₀, hΔ⟩ := h.three
  have hf2 : 2 ≤ f := by
    rcases Nat.lt_or_ge f 2 with hlt | hge
    · interval_cases f
      rw [pow_one] at h2f
      have hq := h.q_big
      rw [← h2f] at hq
      norm_num at hq
    · exact hge
  let eZ : Xbar V H ≃* XbarZ V H := MulEquiv.ofBijective (projZ V H)
    (iw_projZ_bijective hZ)
  let Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H :=
    (MulEquiv.ofBijective Φ₀ hΦ₀).trans eZ.symm
  have hΦ : ∀ x, projZ V H (Φ x) = Φ₀ x := fun x => by
    have h := MulEquiv.ofBijective_apply_symm_apply (projZ V H) (iw_projZ_bijective hZ)
      (n := (MulEquiv.ofBijective Φ₀ hΦ₀) x)
    simpa only [Φ, MulEquiv.trans_apply, eZ, MulEquiv.ofBijective_apply] using h
  have hVZ : VZ V H ∈ rootClassZ V H := ⟨1, (conjSub_one (VZ V H)).symm⟩
  obtain ⟨g, hg⟩ := (hΔ (VZ V H)).1 hVZ
  refine ⟨f, n, hn, hf2, h2f, Φ, g, ?_⟩
  refine Subgroup.map_injective (iw_projZ_injective hZ) ?_
  have hcomp : (projZ V H).comp Φ.toMonoidHom = Φ₀ := MonoidHom.ext hΦ
  rw [Subgroup.map_map, hcomp]
  exact hg.symm

theorem Vy.exists_lift (hc : MinCex M V Q P H) {y : Xbar V H} (hy : y ∈ Vy V H) :
    ∃ v : ↥V, xToXbar hc.V_le_H
      ⟨(v : G), le_xOf (V_mem_omegaOf V H) v.2⟩ = y := by
  have hy' : (y : Hbar V H) ∈ barOf V H V := Subgroup.mem_subgroupOf.mp hy
  obtain ⟨x, hxV, hxy⟩ := mem_barOf_iff.mp hy'
  let xX : ↥(xOf V H) := ⟨(x : G), le_xOf (V_mem_omegaOf V H) hxV⟩
  have hxX : ((Subgroup.inclusion (xOf_le_H hc.V_le_H)) xX : ↥H) = x := Subtype.ext rfl
  refine ⟨⟨(x : G), hxV⟩, Subtype.ext ?_⟩
  rw [coe_xToXbar]
  change piBar V H ((Subgroup.inclusion (xOf_le_H hc.V_le_H)) xX) = (y : Hbar V H)
  rw [hxX]
  exact hxy

end CFSG.RankThree.GF2n.Tim79a
