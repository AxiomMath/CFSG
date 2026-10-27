module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusLineStabAux
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OTs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC
open scoped Matrix

theorem exists_plane_of_rk_eq {W : Type} [CommGroup W] [Finite W]
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {b c : F}
    (hF : Nat.card F = 2 ^ n) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {W' : Subgroup W} (ψ : W' ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (E : Subgroup W) (hEW : E ≤ W') (hrk : rk E = 2 * n)
    (hsing : ∀ x (hx : x ∈ E),
      StatedQuadMinus 3 F b c (Multiplicative.toAdd (ψ ⟨x, hEW hx⟩)) = 0) :
    ∃ Y : Submodule F (OW F), Module.finrank F Y = 2 ∧
      (∀ y ∈ Y, StatedQuadMinus 3 F b c y = 0) ∧
      ∀ (x : W) (hx : x ∈ W'), x ∈ E ↔ Multiplicative.toAdd (ψ ⟨x, hx⟩) ∈ Y := by
  classical
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx =>
    congrArg Subtype.val (coords_mul_self_eq_one ψ ⟨x, hEW hx⟩)
  have hIsP : IsPGroup 2 ↥E :=
    isPGroup_two_of_sq_eq_one fun x => Subtype.ext (by simpa [sq] using hE2 x x.2)
  have hcardE : Nat.card ↥E = 2 ^ rk E := card_eq_two_pow_of_isPGroup hIsP
  have hFE : Nat.card ↥E = Nat.card F ^ 2 := by
    have hpow : ((2 : ℕ) ^ n) ^ 2 = 2 ^ (2 * n) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hcardE, hrk, hF, hpow]
  obtain ⟨S, hmem, hcard⟩ := exists_addSubgroup_image ψ E hEW
  have hSsing : ∀ v ∈ S, StatedQuadMinus 3 F b c v = 0 := by
    intro v hv
    have hxE : ((ψ.symm (Multiplicative.ofAdd v) : W') : W) ∈ E := by
      rw [hmem _ (ψ.symm (Multiplicative.ofAdd v)).2]
      rw [show (⟨((ψ.symm (Multiplicative.ofAdd v) : W') : W),
          (ψ.symm (Multiplicative.ofAdd v)).2⟩ : W') =
          ψ.symm (Multiplicative.ofAdd v) from rfl, MulEquiv.apply_symm_apply]
      simpa using hv
    have h := hsing _ hxE
    rw [show (⟨((ψ.symm (Multiplicative.ofAdd v) : W') : W), hEW hxE⟩ : W') =
        ψ.symm (Multiplicative.ofAdd v) from rfl, MulEquiv.apply_symm_apply] at h
    simpa using h
  obtain ⟨Y, hSY, hY2, hYs⟩ := ts_eq_plane hirr S hSsing (hcard.trans hFE)
  refine ⟨Y, hY2, hYs, ?_⟩
  intro x hx
  rw [hmem x hx]
  exact hSY _

private theorem transport_maps_into_OC {W : Type} [CommGroup W]
    {F : Type} [Field F] [Finite F] {b c : F}
    (H : Subgroup (MulAut W)) {W' : Subgroup W} (hW' : StableUnder H W')
    (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : W' ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hψ : NatCoordsOmegaMinusOn H W' hW' F b c ε ψ)
    (E : Subgroup W) (hEW : E ≤ W') (Y : Submodule F (OW F))
    (hEY : ∀ (x : W) (hx : x ∈ W'), x ∈ E ↔ Multiplicative.toAdd (ψ ⟨x, hx⟩) ∈ Y)
    (E' : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F))
    (hE'Y : ∀ g ∈ E', ∀ y ∈ Y,
      ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y ∈
          Y)
    (x : MulAut W)
    (hx : x ∈ (E'.subgroupOf (StatedOmega (StatedQuadMinus 3 F b c))).map
      (H.subtype.comp (MulEquiv.symm ε).toMonoidHom)) :
    ∀ u ∈ E, x u ∈ E := by
  intro u hu
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  change (((ε.symm y : ↥H) : MulAut W)) u ∈ E
  have hy' : (y : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ∈ E' :=
    (Subgroup.mem_subgroupOf).1 hy
  have hxuW' : (((ε.symm y : ↥H) : MulAut W)) u ∈ W' :=
    hW' (ε.symm y) (ε.symm y).2 u (hEW hu)
  rw [hEY _ hxuW']
  have h1 : Multiplicative.toAdd (ψ ⟨((ε.symm y : ↥H) : MulAut W) u, hxuW'⟩) =
      ((y : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
        Multiplicative.toAdd (ψ ⟨u, hEW hu⟩) := by
    have h := congrArg Multiplicative.toAdd (hψ (ε.symm y) ⟨u, hEW hu⟩)
    simpa using h
  rw [h1]
  exact hE'Y y hy' _ ((hEY u (hEW hu)).mp hu)

theorem exists_stab_transport {W : Type} [CommGroup W]
    {F : Type} [Field F] [Finite F] {b c : F} {p : ℕ}
    (H : Subgroup (MulAut W)) {W' : Subgroup W} (hW' : StableUnder H W')
    (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : W' ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hψ : NatCoordsOmegaMinusOn H W' hW' F b c ε ψ)
    (E : Subgroup W) (hEW : E ≤ W') (Y : Submodule F (OW F))
    (hEY : ∀ (x : W) (hx : x ∈ W'), x ∈ E ↔ Multiplicative.toAdd (ψ ⟨x, hx⟩) ∈ Y)
    (E' : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F))
    (hE'S : E' ≤ StatedOmega (StatedQuadMinus 3 F b c)) (hE'a : IsElemAbelian p E')
    (hE'Y : ∀ g ∈ E', ∀ y ∈ Y,
      ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y ∈
          Y) :
    ∃ P : Subgroup (MulAut W), P ≤ H ⊓ stabSub E ∧ IsElemAbelian p P ∧
      Nat.card ↥P = Nat.card ↥E' := by
  classical
  let S : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :=
    StatedOmega (StatedQuadMinus 3 F b c)
  let f : ↥S →* MulAut W := H.subtype.comp ε.symm.toMonoidHom
  let P : Subgroup (MulAut W) := (E'.subgroupOf S).map f
  have hPH : P ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    exact (ε.symm y).2
  have hPa : IsElemAbelian p P := (hE'a.subgroupOf S).map f
  have hPcard : Nat.card ↥P = Nat.card ↥E' := by
    have h2 : Nat.card ↥(E'.subgroupOf S) = Nat.card ↥E' := by
      calc Nat.card ↥(E'.subgroupOf S) =
            Nat.card ↥((E'.subgroupOf S).map S.subtype) :=
            (Subgroup.card_map_of_injective (K := E'.subgroupOf S) (f := S.subtype)
              S.subtype_injective).symm
        _ = Nat.card ↥E' := by rw [Subgroup.map_subgroupOf_eq_of_le hE'S]
    calc Nat.card ↥P = Nat.card ↥(E'.subgroupOf S) := by
          change Nat.card ↥((E'.subgroupOf S).map f) = Nat.card ↥(E'.subgroupOf S)
          exact Subgroup.card_map_of_injective (K := E'.subgroupOf S) (f := f)
            (H.subtype_injective.comp ε.symm.injective)
      _ = Nat.card ↥E' := h2
  have hfwd : ∀ x ∈ P, ∀ u ∈ E, x u ∈ E := fun x hx =>
    transport_maps_into_OC H hW' ε ψ hψ E hEW Y hEY E' hE'Y x hx
  have hPstab : P ≤ stabSub E := by
    intro x hx
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
      have hmem := hfwd x⁻¹ (P.inv_mem hx) (x u) hu
      rwa [MulAut.inv_apply_self] at hmem, fun hu => hfwd x hx u hu⟩
  exact ⟨P, fun x hx => ⟨hPH hx, hPstab hx⟩, hPa, hPcard⟩

theorem k_K_Omega6Minus_lineStab_holds : K_Omega6Minus_lineStab := by
  intro W _ _ H n p F _ _ b c hF hirr hp _hp2 hcong W' hW' _hN ε ψ hψ E hEW hrk hsing
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := n) hF
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF, hn0, pow_zero] at h2
    omega
  obtain ⟨M⟩ := nonempty_normModel (F := F) (b := b) (c := c) hirr hF hn1
  have hpq : p ∣ Nat.card F + 1 := by
    rw [hF]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  obtain ⟨Y, hY2, hYs, hEY⟩ := exists_plane_of_rk_eq hF hirr ψ E hEW hrk hsing
  obtain ⟨E', hE'S, hE'a, hE'c, hE'Y⟩ := exists_stab_plane M hirr hp hpq Y hY2 hYs
  obtain ⟨P, hP, hPa, hPc⟩ := exists_stab_transport H hW' ε ψ hψ E hEW Y hEY E' hE'S hE'a hE'Y
  exact ⟨P, hP, hPa.isPGroup,
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_not_isCyclic_of_card_sq hp hPa
      (hPc.trans hE'c)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
