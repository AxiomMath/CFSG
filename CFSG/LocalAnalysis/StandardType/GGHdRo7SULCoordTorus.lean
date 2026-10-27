module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordSplit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordTorusA

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly
open CFSG.StandardType.UCoord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SULCoordAux_torusCfg
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) (hx : x ∈ Bs) :
    ∃ (m : ℕ) (e : ↥(sumZero m p) ≃* ↥(Bs ⊓ L)),
      p = 3 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧
      ∀ a : MulAut ↥Bs,
        a ∈ ggAutomizer L Bs ↔
          (a ⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ ∧
          ∃ σ : Equiv.Perm (Fin m), ∀ f : ↥(sumZero m p),
            ((a ⟨(e f : ↥(Bs ⊓ L)).1, (e f).2.1⟩ : ↥Bs) : G) =
              ((e (permAutV σ f) : ↥(Bs ⊓ L)) : G) := by
  obtain ⟨m, e, hp3, hm7, hm3d, hperm, hnorm⟩ := hdRo7SULCoordAux_permDataCfg hH hRig hrow
  have hLCx : L ≤ Subgroup.centralizer ({x} : Set G) := by
    obtain ⟨-, -, -, -, -, -, hSStar, -⟩ := hH.1.1
    exact hSStar.2.2.2.1.1
  refine ⟨m, e, hp3, hm7, hm3d, ?_⟩
  intro a
  constructor
  · intro ha
    rw [mem_ggAutomizer_iff] at ha
    obtain ⟨g, hgL, hgN, hag⟩ := ha
    have hxg : g * x = x * g :=
      (Subgroup.mem_centralizer_iff.mp (hLCx hgL) x (Set.mem_singleton x)).symm
    have hxfix : (a ⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ := by
      apply Subtype.ext
      rw [hag ⟨x, hx⟩]
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hxg]
        _ = x := by group
    refine ⟨hxfix, ?_⟩
    have hgNorm : ∀ t : ↥(Bs ⊓ L), ∃ t' : ↥(Bs ⊓ L),
        (g : G) * (t : G) * (g : G)⁻¹ = (t' : G) := by
      intro t
      refine ⟨⟨g * (t : G) * g⁻¹, ?_, ?_⟩, rfl⟩
      · exact (Subgroup.mem_normalizer_iff.mp hgN (t : G)).mp t.2.1
      · exact L.mul_mem (L.mul_mem hgL t.2.2) (L.inv_mem hgL)
    obtain ⟨π, hπ⟩ := hnorm g hgL hgNorm
    refine ⟨π, fun f => ?_⟩
    rw [hag ⟨(e f).1, (e f).2.1⟩]
    simpa using hπ f
  · rintro ⟨hax, σ, hσ⟩
    obtain ⟨w, hwL, hwperm⟩ := hperm σ
    have hwT : ∀ t : ↥(Bs ⊓ L), ∃ t' : ↥(Bs ⊓ L),
        (w : G) * (t : G) * (w : G)⁻¹ = (t' : G) := by
      intro t
      obtain ⟨f, hf⟩ := e.surjective t
      refine ⟨e (permAutV σ f), ?_⟩
      have h := hwperm f
      rwa [hf] at h
    have hwC : ∀ c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G)),
        (w : G) * (c : G) * (w : G)⁻¹ = (c : G) := by
      intro c
      have hcw : (w : G) * (c : G) = (c : G) * (w : G) :=
        Subgroup.mem_centralizer_iff.mp c.2.2 (w : G) hwL
      rw [hcw]; group
    rw [mem_ggAutomizer_iff]
    refine ⟨w, hwL, ?_, ?_⟩
    · have hmaple : Bs.map (MulAut.conj w).toMonoidHom ≤ Bs := by
        rintro y ⟨x, hx, rfl⟩
        show (w : G) * x * (w : G)⁻¹ ∈ Bs
        obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SULCoordAux_splitCfg hH hRig hrow x hx
        obtain ⟨t', hwt'⟩ := hwT ⟨t, ht⟩
        rw [hbc, show (w : G) * (t * (c : G)) * (w : G)⁻¹ =
            ((w : G) * t * (w : G)⁻¹) * ((w : G) * (c : G) * (w : G)⁻¹) by group,
          hwt', hwC ⟨c, hc⟩]
        exact Bs.mul_mem t'.2.1 hc.1
      have hconjinj : Function.Injective (MulAut.conj w) := by
        intro x y hxy
        rw [MulAut.conj_apply, MulAut.conj_apply] at hxy
        exact mul_left_cancel (mul_right_cancel hxy)
      have hcard : Nat.card ↥(Bs.map (MulAut.conj w).toMonoidHom) = Nat.card ↥Bs :=
        Subgroup.card_map_of_injective hconjinj
      have hmap : Bs.map (MulAut.conj w).toMonoidHom = Bs :=
        Subgroup.eq_of_le_of_card_ge hmaple (by rw [hcard])
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hmaple ⟨x, hx, rfl⟩
      · intro hx
        have hx' : (MulAut.conj w) x ∈ Bs.map (MulAut.conj w).toMonoidHom := by
          rw [hmap]; exact hx
        obtain ⟨y, hy, hyx⟩ := hx'
        rw [← hconjinj hyx]
        exact hy
    · intro b
      obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SULCoordAux_splitCfg hH hRig hrow (b : G) b.2
      obtain ⟨f, hf⟩ := e.surjective ⟨t, ht⟩
      have hat : (a ⟨t, ht.1⟩ : G) = (w : G) * t * (w : G)⁻¹ := by
        have h1 := hσ f
        rw [hf] at h1
        have h2 := hwperm f
        rw [hf] at h2
        rw [h1, h2]
      have hac' : a (⟨(c : G), hc.1⟩ : ↥Bs) = ⟨(c : G), hc.1⟩ := by
        have hcZ : (c : G) ∈ Subgroup.zpowers x := by
          rw [← hdRo7SULCoordAux_centralizerCfg hH hp3]; exact hc
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcZ
        have hxk : (⟨x, hx⟩ : ↥Bs) ^ k = (⟨(c : G), hc.1⟩ : ↥Bs) := by
          apply Subtype.ext
          simpa using hk
        calc a (⟨(c : G), hc.1⟩ : ↥Bs) = a ((⟨x, hx⟩ : ↥Bs) ^ k) := by rw [hxk]
          _ = (a ⟨x, hx⟩) ^ k := by rw [map_zpow]
          _ = (⟨x, hx⟩ : ↥Bs) ^ k := by rw [hax]
          _ = ⟨(c : G), hc.1⟩ := hxk
      have hac : (a ⟨(c : G), hc.1⟩ : G) = (c : G) := congrArg Subtype.val hac'
      have hb_eq : b = ⟨t, ht.1⟩ * ⟨(c : G), hc.1⟩ := Subtype.ext hbc
      calc (↑(a b) : G) = (↑(a (⟨t, ht.1⟩ * ⟨(c : G), hc.1⟩)) : G) := by rw [hb_eq]
        _ = (↑(a ⟨t, ht.1⟩ * a ⟨(c : G), hc.1⟩) : G) := by rw [map_mul]
        _ = (a ⟨t, ht.1⟩ : G) * (a ⟨(c : G), hc.1⟩ : G) := rfl
        _ = ((w : G) * t * (w : G)⁻¹) * ((w : G) * (c : G) * (w : G)⁻¹) := by
              rw [hat, hac, hwC ⟨c, hc⟩]
        _ = (w : G) * (t * (c : G)) * (w : G)⁻¹ := by group
        _ = (w : G) * (b : G) * (w : G)⁻¹ := by rw [hb_eq]; rfl

end CFSG.StandardType.HdRo7SU
