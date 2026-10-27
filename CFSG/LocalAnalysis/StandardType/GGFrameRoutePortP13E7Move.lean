module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13E7Hyp
import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.OddStandard.SmallF3.Omega.E7RootSet
  Certificates.OmegaSevenMax TableBExcTwo TableBExcTwoTB TableBExcTwoFusion

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section E7


variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem p13e7Aux_exists_conj_tE_eq_of_torusWord (hK : Nat.card K = 2)
    (w : List (Fin Tag.E7.rank)) :
    ∃ n : adjointGroup .E7 K, ∀ u v : Fin 7 → ZMod 3,
      TableBExc.torusWord Tag.E7 3 w (p13e7Coord u) = p13e7Coord v →
        n * tE K frameE7 (Multiplicative.ofAdd u) * n⁻¹ =
          tE K frameE7 (Multiplicative.ofAdd v) := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3)
    (three_dvd_natCard_ext_sub_one hK)
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hfull : ∀ a : Fin Tag.E7.rank → Lˣ,
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E7 a ∈
        torusGroup Tag.E7 L :=
    TableBExc.full_of_E7_E8 (Or.inl rfl)
  let pc : (Fin 7 → ZMod 3) → (Fin Tag.E7.rank → ZMod 3) := fun x => p13e7Coord x
  set g := langElt frameE7 hωo with hg
  set m : adjointGroup .E7 L :=
    ⟨canonicalRep (coxeterSystem Tag.E7) L ((coxeterSystem Tag.E7).wordProd w),
      canonicalRep_mem_adjointGroup (coxeterSystem Tag.E7) L _⟩ with hm
  set D : (Fin Tag.E7.rank → ZMod 3) → adjointGroup .E7 L := fun s =>
    ⟨ExcFrames.frameDiag ω hω3 s,
      ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 s⟩ with hD
  have hDconj : ∀ s, m * D s * m⁻¹ = D (TableBExc.torusWord Tag.E7 3 w s) := by
    intro s
    have h := ExcFrames.canonicalRep_conj_frameDiag (τ := Tag.E7) (L := L) (p := 3) ω hω3
      ((coxeterSystem Tag.E7).wordProd w) s
    rw [TableBExc.torusWord_eq_torusAct TableBExc.Three.cartan_symm_E7]
    apply Subtype.ext
    exact h
  have hDtE : ∀ u, adjointMap .E7 (algebraMap K L) (tE K frameE7 (Multiplicative.ofAdd u)) =
      g * D (pc u) * g⁻¹ := by
    intro u
    exact ExcFrameIso.adjointMap_tE_eq frameE7.symm_one frameE7 hωo hω3 hfull u
  obtain ⟨n, hn⟩ := exists_adjointMap_eq_of_frob (Or.inl rfl)
    (adjointMap_frob_conj_langElt hK frameE7 frameE7_reflections
      TableBExc.Three.cartan_symm_E7
      (TableBExc.isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E7 (by norm_num))
      (TableBExc.card_torusPow_E7 (K := L) Nat.prime_three
        (three_dvd_natCard_ext_sub_one hK)) hωo
      (m := m) (CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup L
        ((coxeterSystem Tag.E7).wordProd w)))
  refine ⟨n, ?_⟩
  intro u v huv
  have huv' : TableBExc.torusWord Tag.E7 3 w (pc u) = pc v := by
    simpa [pc] using huv
  apply adjointMap_injective (algebraMap K L)
  calc
    adjointMap .E7 (algebraMap K L) (n * tE K frameE7 (Multiplicative.ofAdd u) * n⁻¹)
        = adjointMap .E7 (algebraMap K L) n *
            adjointMap .E7 (algebraMap K L) (tE K frameE7 (Multiplicative.ofAdd u)) *
            (adjointMap .E7 (algebraMap K L) n)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = (g * m * g⁻¹) * (g * D (pc u) * g⁻¹) * (g * m * g⁻¹)⁻¹ := by
          rw [hn, hDtE u]
    _ = g * (m * D (pc u) * m⁻¹) * g⁻¹ := by group
    _ = g * D (pc v) * g⁻¹ := by rw [hDconj, huv']
    _ = adjointMap .E7 (algebraMap K L) (tE K frameE7 (Multiplicative.ofAdd v)) :=
          (hDtE v).symm

theorem p13e7_exists_conj_hyp (hK : Nat.card K = 2) {β : Fin Tag.E7.rank → ℤ}
    (hβ : IsRoot Tag.E7 β) :
    ∃ k : adjointGroup .E7 K,
      (tE K frameE7).range.map (MulAut.conj k).toMonoidHom = (tE K frameE7).range ∧
      (p13e7Hyp K (redV β)).map (MulAut.conj k).toMonoidHom =
        p13e7Hyp K (redV (frameE7.root 0)) := by
  classical
  obtain ⟨u, hu⟩ := GGFinModel.G5.ggG5_orbit_simplyLaced (τ := Tag.E7) (Or.inr (Or.inl rfl))
    hβ (frameE7.isRoot 0)
  obtain ⟨w, hw⟩ := (coxeterSystem Tag.E7).wordProd_surjective u
  obtain ⟨n, hn⟩ := p13e7Aux_exists_conj_tE_eq_of_torusWord (K := K) hK w
  have hT : Nat.card (tE K frameE7).range = 3 ^ 7 := by
    calc
      Nat.card (tE K frameE7).range = Nat.card (Multiplicative (Fin 7 → ZMod 3)) :=
        Nat.card_congr (Equiv.ofInjective (tE K frameE7) (tE_injective frameE7)).symm
      _ = Nat.card (Fin 7 → ZMod 3) := Nat.card_congr Multiplicative.toAdd
      _ = 3 ^ 7 := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have htorusAct : ∀ x : Fin Tag.E7.rank → ZMod 3,
      (TableBExc.torusAct Tag.E7 3 u x : V) = rhoEquiv u x := by
    intro x
    have hxv : redV (TableBExc.liftMod Tag.E7 3 x) = x :=
      TableBExc.redMod_liftMod (τ := Tag.E7) (p := 3) x
    have h1 : (TableBExc.torusAct Tag.E7 3 u x : V) =
        redV (u • TableBExc.liftMod Tag.E7 3 x) := rfl
    have h2 : redV (u • TableBExc.liftMod Tag.E7 3 x) =
        rhoEquiv u (redV (TableBExc.liftMod Tag.E7 3 x)) :=
      (rhoEquiv_redV u (TableBExc.liftMod Tag.E7 3 x)).symm
    have h3 : rhoEquiv u (redV (TableBExc.liftMod Tag.E7 3 x)) = rhoEquiv u x := by
      rw [hxv]
    exact h1.trans (h2.trans h3)
  choose v hv using fun a : Fin 7 → ZMod 3 =>
    p13e7Coord_surjective (rhoEquiv u (p13e7Coord a))
  let pc : (Fin 7 → ZMod 3) → (Fin Tag.E7.rank → ZMod 3) := fun x => p13e7Coord x
  have hconj : ∀ a : Fin 7 → ZMod 3,
      MulAut.conj n (tE K frameE7 (Multiplicative.ofAdd a)) =
        tE K frameE7 (Multiplicative.ofAdd (v a)) := by
    intro a
    have hword : TableBExc.torusWord Tag.E7 3 w (pc a) = pc (v a) := by
      have h1 : TableBExc.torusWord Tag.E7 3 w (pc a) =
          TableBExc.torusAct Tag.E7 3 u (pc a) := by
        simpa [hw] using TableBExc.torusWord_eq_torusAct (τ := Tag.E7) (p := 3)
          TableBExc.Three.cartan_symm_E7 w (pc a)
      have h2 : TableBExc.torusAct Tag.E7 3 u (pc a) = rhoEquiv u (pc a) :=
        htorusAct (pc a)
      have h3 : rhoEquiv u (pc a) = pc (v a) := by
        simpa [pc] using (hv a).symm
      exact h1.trans (h2.trans h3)
    simpa only [MulAut.conj_apply] using hn a (v a) hword
  have hTmap : (tE K frameE7).range.map (MulAut.conj n).toMonoidHom =
      (tE K frameE7).range := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := hx
      refine ⟨Multiplicative.ofAdd (v (Multiplicative.toAdd a)), ?_⟩
      simpa [ofAdd_toAdd] using (hconj (Multiplicative.toAdd a)).symm
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have htheta : redV (frameE7.root 0) = rhoEquiv u (redV β) := by
    rw [← hu]
    exact (rhoEquiv_redV u β).symm
  have hpolar : ∀ a : Fin 7 → ZMod 3,
      polarV (redV (frameE7.root 0)) (p13e7Coord (v a)) =
        polarV (redV β) (p13e7Coord a) := by
    intro a
    simpa [hv a, htheta] using p13e7_polarV_rhoEquiv u (redV β) (p13e7Coord a)
  have hpolar' : ∀ a : Fin 7 → ZMod 3,
      polarV (redV β) (p13e7Coord a) =
        polarV (redV (frameE7.root 0)) (p13e7Coord (v a)) := fun a => (hpolar a).symm
  have hFmap : (p13e7Hyp K (redV β)).map (MulAut.conj n).toMonoidHom =
      p13e7Hyp K (redV (frameE7.root 0)) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ (p13e7HypVec (redV β)).toSubgroup.map (tE K frameE7) := hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy'
      have ha' : Multiplicative.toAdd a ∈ p13e7HypVec (redV β) := ha
      refine Subgroup.mem_map.mpr
        ⟨Multiplicative.ofAdd (v (Multiplicative.toAdd a)), ?_, ?_⟩
      · show v (Multiplicative.toAdd a) ∈ p13e7HypVec (redV (frameE7.root 0))
        rw [mem_p13e7HypVec, hpolar (Multiplicative.toAdd a)]
        exact (mem_p13e7HypVec.mp ha')
      · simpa [ofAdd_toAdd] using
          (hconj (Multiplicative.toAdd a)).symm
    · intro x hx
      have hxT : x ∈ (tE K frameE7).range := by
        have hx' : x ∈ (p13e7HypVec (redV (frameE7.root 0))).toSubgroup.map
            (tE K frameE7) := hx
        obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hx'
        exact ⟨a, rfl⟩
      have hxmap : x ∈ (tE K frameE7).range.map (MulAut.conj n).toMonoidHom := by
        rw [hTmap]
        exact hxT
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxmap
      obtain ⟨a, rfl⟩ := hy
      rw [← hxy] at hx
      rw [← hxy]
      have hxva : tE K frameE7 (Multiplicative.ofAdd (v (Multiplicative.toAdd a))) ∈
          p13e7Hyp K (redV (frameE7.root 0)) := by
        rw [← hconj (Multiplicative.toAdd a)]
        exact hx
      have hva : v (Multiplicative.toAdd a) ∈ p13e7HypVec (redV (frameE7.root 0)) := by
        have hxva' : tE K frameE7 (Multiplicative.ofAdd (v (Multiplicative.toAdd a))) ∈
            (p13e7HypVec (redV (frameE7.root 0))).toSubgroup.map (tE K frameE7) := hxva
        obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hxva'
        have hb' : b = Multiplicative.ofAdd (v (Multiplicative.toAdd a)) :=
          tE_injective frameE7 hbeq
        rwa [hb'] at hb
      have hmem : Multiplicative.toAdd a ∈ p13e7HypVec (redV β) := by
        rw [mem_p13e7HypVec, hpolar' (Multiplicative.toAdd a)]
        exact (mem_p13e7HypVec.mp hva)
      exact Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom
        (Subgroup.mem_map.mpr ⟨a, hmem, rfl⟩)
  exact ⟨n, hTmap, hFmap⟩

end E7

end CFSG.StandardType.FrameRoute
