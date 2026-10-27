module

public import CFSG.Quasithin.Background.ElemAbTransport
public import CFSG.Quasithin.H13.GoldschmidtC137U33Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.Quasithin.Vol2.Ch12Sec4G2Off

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Transport

variable {W M : Type} [CommGroup W] [CommGroup M] (e : W ≃* M)

@[expose] def cg : MulAut W →* MulAut M := (MulAut.congr e).toMonoidHom

theorem cg_apply (a : MulAut W) (w : W) : cg e a (e w) = e (a w) := by
  simp [cg, MulAut.congr_apply]

theorem cg_injective : Function.Injective (cg e) := (MulAut.congr e).injective

theorem card_map_cg (A : Subgroup (MulAut W)) : Nat.card ↥(A.map (cg e)) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (cg_injective e)

theorem fixV_map_cg (A : Subgroup (MulAut W)) :
    fixV (A.map (cg e)) = (fixV A).map e.toMonoidHom := fixV_map_congr e A

theorem card_fixV_map_cg (A : Subgroup (MulAut W)) :
    Nat.card ↥(fixV (A.map (cg e))) = Nat.card ↥(fixV A) := by
  rw [fixV_map_cg]
  exact Subgroup.card_map_of_injective e.injective

theorem rkIdx_map_cg (A : Subgroup (MulAut W)) :
    rkIdx (fixV (A.map (cg e))) = rkIdx (fixV A) := by
  unfold rkIdx
  rw [fixV_map_cg]
  exact congrArg (padicValNat 2) (Subgroup.index_map_equiv _ e)

theorem le_map_cg {A B : Subgroup (MulAut W)} : A.map (cg e) ≤ B.map (cg e) ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective (cg_injective e)

theorem isElemAbelian2_map_cg_iff {A : Subgroup (MulAut W)} :
    IsElemAbelian2 (A.map (cg e)) ↔ IsElemAbelian2 A :=
  CFSG.Quasithin.FixVLat.isElemAbelian2_map_iff_of_injective (MulAut.congr e).injective

theorem isFFStarOffender_map_cg {X A : Subgroup (MulAut W)} :
    IsFFStarOffender (X.map (cg e)) (A.map (cg e)) ↔ IsFFStarOffender X A :=
  isFFStarOffender_map_congr_equiv_iff e

theorem pCoreOf_map_cg (P : Subgroup (MulAut W)) :
    pCoreOf 2 (P.map (cg e)) = (pCoreOf 2 P).map (cg e) :=
  CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.congr e) P

theorem isSylowTwoOf_map_cg {S X : Subgroup (MulAut W)} :
    IsSylowTwoOf (S.map (cg e)) (X.map (cg e)) ↔ IsSylowTwoOf S X :=
  QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv (MulAut.congr e)

theorem map_cg_symm (A : Subgroup (MulAut M)) :
    (A.map (MulAut.congr e).symm.toMonoidHom).map (cg e) = A := by
  rw [Subgroup.map_map]
  have : (cg e).comp (MulAut.congr e).symm.toMonoidHom = MonoidHom.id _ := by
    ext x
    simp [cg]
  rw [this, Subgroup.map_id]

theorem mem_normalizer_map_cg {S : Subgroup (MulAut W)} {x : MulAut W}
    (hx : x ∈ normalizer (S : Set (MulAut W))) :
    cg e x ∈ normalizer ((S.map (cg e) : Subgroup (MulAut M)) : Set (MulAut M)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx s).1 hs, by simp⟩
  · rintro ⟨s, hs, hsh⟩
    obtain ⟨t, rfl⟩ : ∃ t, cg e t = h := by
      refine ⟨(MulAut.congr e).symm h, ?_⟩
      exact (MulAut.congr e).apply_symm_apply h
    refine ⟨t, ?_, rfl⟩
    have h1 : cg e (x * t * x⁻¹) = cg e s := by rw [map_mul, map_mul, map_inv, hsh]
    have h2 := cg_injective e h1
    exact (Subgroup.mem_normalizer_iff.1 hx t).2 (h2 ▸ hs)

theorem G2Line.of_map {L P : Subgroup (MulAut W)} [Finite W] [Finite M]
    (h : G2Line (L.map (cg e)) (P.map (cg e))) : G2Line L P := by
  obtain ⟨l', hl1, hl2, hl3⟩ := h
  refine ⟨l'.map e.symm.toMonoidHom, fun w hw => ?_, ?_, fun φ hφ w hw => ?_⟩
  · have : e w ∈ fixV (L.map (cg e)) := by
      rw [fixV_map_cg]
      exact ⟨w, hw, rfl⟩
    exact ⟨e w, hl1 this, by simp⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hl2, card_fixV_map_cg]
  · obtain ⟨m, hm, rfl⟩ := hw
    have h1 := hl3 (cg e φ) ⟨φ, hφ, rfl⟩ m hm
    refine ⟨cg e φ m, h1, ?_⟩
    obtain ⟨w0, rfl⟩ := e.surjective m
    simp [cg_apply]

theorem map_conjAut_cg (c : MulAut W) (A : Subgroup (MulAut W)) :
    (B1.conjAut c A).map (cg e) = B1.conjAut (cg e c) (A.map (cg e)) := by
  ext y
  rw [B1.mem_conjAut]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ B1.conjAut c A := hx
    rw [B1.mem_conjAut] at hx'
    exact ⟨_, hx', by simp⟩
  · rintro ⟨a, ha, hay⟩
    refine ⟨c * a * c⁻¹, ?_, ?_⟩
    · show c * a * c⁻¹ ∈ B1.conjAut c A
      rw [B1.mem_conjAut]
      simpa [mul_assoc] using ha
    · have : y = cg e c * cg e a * (cg e c)⁻¹ := by
        rw [hay]
        group
      rw [this, map_mul, map_mul, map_inv]

theorem G2Point.of_map {X L P : Subgroup (MulAut W)} [Finite W] [Finite M]
    (h : G2Point (X.map (cg e)) (L.map (cg e)) (P.map (cg e))) : G2Point X L P := by
  obtain ⟨A', hA1, hA2, hA3, hA4, hA5, hA6, c', hc', hL⟩ := h
  set A : Subgroup (MulAut W) := A'.map (MulAut.congr e).symm.toMonoidHom with hAdef
  have hAA : A.map (cg e) = A' := map_cg_symm e A'
  refine ⟨A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : A.map (cg e) ≤ (pCoreOf 2 P).map (cg e) := by
      rw [hAA, ← pCoreOf_map_cg]
      exact hA1
    exact (le_map_cg e).1 this
  · rw [← isFFStarOffender_map_cg e, hAA]
    exact hA2
  · intro B hB hBo
    have h1 : B.map (cg e) ≤ pCoreOf 2 (P.map (cg e)) := by
      rw [pCoreOf_map_cg]
      exact (le_map_cg e).2 hB
    have h2 := hA3 _ h1 ((isFFStarOffender_map_cg e).2 hBo)
    rw [← hAA] at h2
    exact Subgroup.map_injective (cg_injective e) h2
  · intro x hx
    have hx1 : cg e x ∈ pCoreOf 2 (P.map (cg e)) := by
      rw [pCoreOf_map_cg]
      exact ⟨x, hx.1, rfl⟩
    have hx2 : cg e x ∈ centSub (fixV A') := by
      intro u hu
      rw [← hAA, fixV_map_cg] at hu
      obtain ⟨w, hw, rfl⟩ := hu
      show cg e x (e w) = e w
      rw [cg_apply, hx.2 w hw]
    have h3 := hA4 ⟨hx1, hx2⟩
    rw [← hAA] at h3
    exact (Subgroup.mem_map_iff_mem (cg_injective e)).1 h3
  · rw [← card_map_cg e A, hAA]
    exact hA5
  · rw [← rkIdx_map_cg e A, hAA]
    exact hA6
  · obtain ⟨c, hc, rfl⟩ := hc'
    refine ⟨c, hc, (le_map_cg e).1 ?_⟩
    rw [Subgroup.map_sup, map_conjAut_cg, hAA]
    exact hL

theorem G2Facts.of_equiv {X₀ L₀ : Subgroup (MulAut W)} {Xm Lm : Subgroup (MulAut M)}
    [Finite W] [Finite M] (hX : X₀.map (cg e) = Xm) (hL : L₀.map (cg e) = Lm) (h : G2Facts Xm Lm) :
    G2Facts X₀ L₀ := by
  subst hX hL
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← card_map_cg e]
    exact h.card_X
  · rw [← rkIdx_map_cg e]
    exact h.rk_L
  · intro B hB hB1 hB2 hB3
    refine h.no_off (B.map (cg e)) ((le_map_cg e).2 hB) ?_
      ((isElemAbelian2_map_cg_iff e).2 hB2) ?_
    · intro h0
      exact hB1 ((Subgroup.map_eq_bot_iff_of_injective B (cg_injective e)).1 h0)
    · rw [card_map_cg, card_fixV_map_cg, ← Nat.card_congr e.toEquiv]
      exact hB3
  · intro S hS x hx
    have h1 := h.sylow_self (S.map (cg e)) ((isSylowTwoOf_map_cg e).2 hS)
    have hx1 : cg e x ∈ X₀.map (cg e) ⊓
        normalizer ((S.map (cg e) : Subgroup (MulAut M)) : Set (MulAut M)) :=
      ⟨⟨x, hx.1, rfl⟩, mem_normalizer_map_cg e hx.2⟩
    exact (Subgroup.mem_map_iff_mem (cg_injective e)).1 (h1 hx1)
  · intro S P hS hSP hPX hPne hmax
    have hmax' : ∀ H' : Subgroup (MulAut M), P.map (cg e) ≤ H' → H' ≤ X₀.map (cg e) →
        H' = P.map (cg e) ∨ H' = X₀.map (cg e) := by
      intro H' hPH' hH'X
      set H : Subgroup (MulAut W) := H'.map (MulAut.congr e).symm.toMonoidHom with hH
      have hHH : H.map (cg e) = H' := map_cg_symm e H'
      have h1 : P ≤ H := (le_map_cg e).1 (by rw [hHH]; exact hPH')
      have h2 : H ≤ X₀ := (le_map_cg e).1 (by rw [hHH]; exact hH'X)
      rcases hmax H h1 h2 with h3 | h3
      · left
        rw [← hHH, h3]
      · right
        rw [← hHH, h3]
    rcases h.dichotomy (S.map (cg e)) (P.map (cg e)) ((isSylowTwoOf_map_cg e).2 hS)
        (Subgroup.map_mono hSP) (Subgroup.map_mono hPX)
        (fun h0 => hPne (Subgroup.map_injective (cg_injective e) h0)) hmax' with hl | hp
    · exact Or.inl (G2Line.of_map e hl)
    · exact Or.inr (G2Point.of_map e hp)

end Transport

end CFSG.Quasithin.H13.U3.GC137
