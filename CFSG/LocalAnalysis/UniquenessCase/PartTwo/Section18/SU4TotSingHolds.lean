module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.SU4TotSingModel
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Open
open Subgroup CFSG.Quasithin
open scoped Matrix

private theorem sq_eq_one_of_char_two_T1J7 {W : Type} [CommGroup W] {F : Type} [Field F]
    (h2 : (2 : F) = 0) (ψ : W ≃* Multiplicative (Fin 4 → F)) : ∀ v : W, v ^ 2 = 1 := by
  intro v
  have hx : Multiplicative.toAdd (ψ (v ^ 2)) = 0 := by
    rw [map_pow, toAdd_pow, two_nsmul]
    funext i
    rw [Pi.add_apply, Pi.zero_apply, ← two_mul, h2, zero_mul]
  apply ψ.injective
  rw [map_one, ← ofAdd_toAdd (ψ (v ^ 2))]
  exact (ofAdd_eq_one).mpr hx

private theorem card_toAddSubgroup'_map_T1J7 {W : Type} [CommGroup W] {F : Type} [Field F]
    (ψ : W ≃* Multiplicative (Fin 4 → F)) (E : Subgroup W) :
    Nat.card (Subgroup.toAddSubgroup' (E.map ψ.toMonoidHom)) = Nat.card E := by
  rw [show Nat.card (Subgroup.toAddSubgroup' (E.map ψ.toMonoidHom)) =
      Nat.card (E.map ψ.toMonoidHom) from rfl]
  exact Subgroup.card_map_of_injective ψ.injective

private theorem herm_eq_zero_on_toAddSubgroup'_T1J7 {F : Type} [Field F] {W : Type} [CommGroup W]
    {σ : F ≃+* F} {n : ℕ} (hσpow : ∀ c : F, σ c = c ^ 2 ^ n)
    (ψ : W ≃* Multiplicative (Fin 4 → F)) (E : Subgroup W)
    (hsing : ∀ x ∈ E, ∑ i, (Multiplicative.toAdd (ψ x)) i ^ (2 ^ n + 1) = 0)
    (E' : AddSubgroup (Fin 4 → F))
    (hE'mem : ∀ y : Fin 4 → F, y ∈ E' ↔ ψ.symm (Multiplicative.ofAdd y) ∈ E) :
    ∀ y ∈ E', herm σ y y = 0 := by
  intro y hy
  have hyE : ψ.symm (Multiplicative.ofAdd y) ∈ E := (hE'mem y).1 hy
  have h1 := hsing _ hyE
  have h2 : Multiplicative.toAdd (ψ (ψ.symm (Multiplicative.ofAdd y))) = y := by
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  rw [herm_def]
  calc ∑ i, σ (y i) * y i = ∑ i, y i ^ (2 ^ n + 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hσpow (y i), pow_succ]
    _ = 0 := by rw [← h2]; exact h1

private theorem exists_transport_subgroup_T1J7 {W : Type} [CommGroup W] {F : Type} [Field F]
    (ψ : W ≃* Multiplicative (Fin 4 → F)) (E : Subgroup W)
    (E' : AddSubgroup (Fin 4 → F))
    (hE'mem : ∀ y : Fin 4 → F, y ∈ E' ↔ ψ.symm (Multiplicative.ofAdd y) ∈ E)
    (X' : AddSubgroup (Fin 4 → F)) (hX'E : X' ≤ E') (hX'ne : X' ≠ ⊥) :
    ∃ X : Subgroup W, X ≤ E ∧ X ≠ ⊥ ∧
      ∀ u : W, u ∈ X ↔ Multiplicative.toAdd (ψ u) ∈ X' := by
  classical
  let X : Subgroup W := (Subgroup.toAddSubgroup'.symm X').map ψ.symm.toMonoidHom
  have hXmem : ∀ u : W, u ∈ X ↔ Multiplicative.toAdd (ψ u) ∈ X' := by
    intro u
    change u ∈ (Subgroup.toAddSubgroup'.symm X').map ψ.symm.toMonoidHom ↔
      Multiplicative.toAdd (ψ u) ∈ X'
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    exact Multiplicative.mem_toSubgroup X' (ψ u)
  have hXE : X ≤ E := by
    intro u hu
    have h1 : Multiplicative.toAdd (ψ u) ∈ E' := hX'E ((hXmem u).1 hu)
    have h2 : ψ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (ψ u))) ∈ E :=
      (hE'mem _).1 h1
    rwa [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h2
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hX'ne
    rw [eq_bot_iff]
    intro y hy
    have hu : ψ.symm (Multiplicative.ofAdd y) ∈ X :=
      (hXmem (ψ.symm (Multiplicative.ofAdd y))).2 (by simpa using hy)
    rw [hbot, Subgroup.mem_bot] at hu
    have hy0 : y = 0 := by
      have := congrArg (fun u : W => Multiplicative.toAdd (ψ u)) hu
      simpa [MulEquiv.apply_symm_apply] using this
    simpa using hy0
  exact ⟨X, hXE, hXne, hXmem⟩

private theorem pullback_card_T1J7 {W : Type} [CommGroup W] {F : Type} [Field F]
    {S : Subgroup (GL (Fin 4) F)} {f : ↥S →* MulAut W}
    (hfinj : Function.Injective f) {P' : Subgroup (GL (Fin 4) F)} (hP'S' : P' ≤ S)
    {p : ℕ} (hP'card : Nat.card ↥P' = p ^ 2) :
    Nat.card ↥((P'.subgroupOf S).map f) = p ^ 2 := by
  have hP2 : Nat.card ↥(P'.subgroupOf S) = Nat.card ↥P' := by
    calc Nat.card ↥(P'.subgroupOf S) = Nat.card ↥((P'.subgroupOf S).map S.subtype) :=
          (Subgroup.card_map_of_injective (K := P'.subgroupOf S) (f := S.subtype)
            S.subtype_injective).symm
      _ = Nat.card ↥P' := by rw [Subgroup.map_subgroupOf_eq_of_le hP'S']
  calc Nat.card ↥((P'.subgroupOf S).map f) = Nat.card ↥(P'.subgroupOf S) :=
        Subgroup.card_map_of_injective hfinj
    _ = Nat.card ↥P' := hP2
    _ = p ^ 2 := hP'card

private theorem map_subgroupOf_le_stabSub_T1J7 {W : Type} [CommGroup W] {F : Type} [Field F]
    {n : ℕ} {H : Subgroup (MulAut W)} {ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F)}
    {ψ : W ≃* Multiplicative (Fin 4 → F)} (hψ : NatCoordsSU4 H n F ε ψ)
    {X : Subgroup W} {X' : AddSubgroup (Fin 4 → F)}
    (hXmem : ∀ u : W, u ∈ X ↔ Multiplicative.toAdd (ψ u) ∈ X')
    {P' : Subgroup (GL (Fin 4) F)}
    (hP'stab : ∀ g ∈ P', ∀ x : Fin 4 → F,
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ X' ↔ x ∈ X') :
    ((P'.subgroupOf (StatedSU 4 (2 ^ n) F)).map
      (H.subtype.comp ε.symm.toMonoidHom)) ≤ stabSub X := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_stabSub]
  intro u
  change ((ε.symm y : ↥H) : MulAut W) u ∈ X ↔ u ∈ X
  have hy' : (y : GL (Fin 4) F) ∈ P' := (Subgroup.mem_subgroupOf).1 hy
  have h1 : ψ (((ε.symm y : ↥H) : MulAut W) u) =
      Multiplicative.ofAdd (((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
        Multiplicative.toAdd (ψ u)) := by
    have := hψ (ε.symm y) u
    rwa [MulEquiv.apply_symm_apply] at this
  simp only [hXmem, h1, toAdd_ofAdd]
  exact hP'stab (y : GL (Fin 4) F) hy' (Multiplicative.toAdd (ψ u))

private theorem pullback_stab_T1J7 {W : Type} [CommGroup W] [Finite W] {F : Type} [Field F]
    {n : ℕ} {H : Subgroup (MulAut W)} {ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F)}
    (ψ : W ≃* Multiplicative (Fin 4 → F)) (hψ : NatCoordsSU4 H n F ε ψ)
    {σ : F ≃+* F} (hSU : SUid σ 4 = StatedSU 4 (2 ^ n) F)
    {X : Subgroup W} {X' : AddSubgroup (Fin 4 → F)}
    (hXmem : ∀ u : W, u ∈ X ↔ Multiplicative.toAdd (ψ u) ∈ X')
    {p : ℕ} (hp : p.Prime) {P' : Subgroup (GL (Fin 4) F)}
    (hP'S : P' ≤ SUid σ 4) (hP'a : IsElemAbelian p P') (hP'card : Nat.card P' = p ^ 2)
    (hP'stab : ∀ g ∈ P', ∀ x : Fin 4 → F,
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ X' ↔ x ∈ X') :
    ∃ P : Subgroup (MulAut W), P ≤ H ∧ IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
      ¬ IsCyclic P ∧ P ≤ stabSub X := by
  classical
  let S : Subgroup (GL (Fin 4) F) := StatedSU 4 (2 ^ n) F
  let f : ↥S →* MulAut W := H.subtype.comp ε.symm.toMonoidHom
  have hP'S' : P' ≤ S := by
    change P' ≤ StatedSU 4 (2 ^ n) F
    rw [← hSU]
    exact hP'S
  have hfinj : Function.Injective f := H.subtype_injective.comp ε.symm.injective
  have hmem : (P'.subgroupOf S).map f = (P'.subgroupOf (StatedSU 4 (2 ^ n) F)).map
      (H.subtype.comp ε.symm.toMonoidHom) := rfl
  refine ⟨(P'.subgroupOf S).map f, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (ε.symm y).2
  · exact (hP'a.subgroupOf S).map f
  · exact pullback_card_T1J7 hfinj hP'S' hP'card
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_not_isCyclic_of_card_sq hp
      ((hP'a.subgroupOf S).map f) (pullback_card_T1J7 hfinj hP'S' hP'card)
  · rw [hmem]
    exact map_subgroupOf_le_stabSub_T1J7 hψ hXmem hP'stab

theorem k_K_SU4Nat_totallySingular_holds : K_SU4Nat_totallySingular := by
  intro W _ _ H p n hn2 _hSUn _hNat hp hcong F _ _ hF ε ψ hψ E hrk hsing
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_sq (p := 2) (f := n) hF
  let σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 n
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := n) hF
  have hσpow : ∀ c : F, σ c = c ^ 2 ^ n :=
    CFSG.LieType.BorelTits.unitaryInvolution_apply F 2 n
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hpq : p ∣ 2 ^ n + 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  have hSU : SUid σ 4 = StatedSU 4 (2 ^ n) F := SUid_eq_statedSU (p := 2) (f := n) hF 4
  let E' : AddSubgroup (Fin 4 → F) := Subgroup.toAddSubgroup' (E.map ψ.toMonoidHom)
  have hE'mem : ∀ y : Fin 4 → F, y ∈ E' ↔ ψ.symm (Multiplicative.ofAdd y) ∈ E := by
    intro y
    exact (Subgroup.mem_toAddSubgroup' (E.map ψ.toMonoidHom) y).trans
      (Subgroup.mem_map_equiv (f := ψ) (K := E) (x := Multiplicative.ofAdd y))
  have hV : ∀ v : W, v ^ 2 = 1 := sq_eq_one_of_char_two_T1J7 h2 ψ
  have hcardE : Nat.card E = 2 ^ (4 * n) := by
    rw [card_eq_two_pow hV E, hrk]
  have hcardE' : Nat.card E' = 2 ^ (4 * n) := by
    change Nat.card (Subgroup.toAddSubgroup' (E.map ψ.toMonoidHom)) = 2 ^ (4 * n)
    rw [card_toAddSubgroup'_map_T1J7 ψ E, hcardE]
  have hQ' : ∀ y ∈ E', herm σ y y = 0 :=
    herm_eq_zero_on_toAddSubgroup'_T1J7 hσpow ψ E hsing E' hE'mem
  obtain ⟨X', hX'E, hX'ne, P', hP'S, hP'a, hP'card, hP'stab⟩ :=
    exists_noncyclic_stab_of_totSing (σ := σ) (n := n) (p := p)
      hσ hσpow h2 hF hp hpq E' hcardE' hQ'
  obtain ⟨X, hXE, hXne, hXmem⟩ :=
    exists_transport_subgroup_T1J7 ψ E E' hE'mem X' hX'E hX'ne
  obtain ⟨P, hPH, hPa, hPcard, hPnc, hPstab⟩ :=
    pullback_stab_T1J7 ψ hψ hSU hXmem hp hP'S hP'a hP'card hP'stab
  exact ⟨X, hXE, hXne, P, le_inf hPH hPstab, hPa, hPnc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
