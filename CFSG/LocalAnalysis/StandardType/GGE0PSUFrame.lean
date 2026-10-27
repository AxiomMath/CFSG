module

public import CFSG.LocalAnalysis.StandardType.GGE0LiftGeneric
public import CFSG.LocalAnalysis.StandardType.GGSixTCLiftGroup
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers Matrix CFSG.StandardType.ClassicalPosition
open scoped commutatorElement
open CFSG.LieType.Universal.Unitary (conjTr conjTr_mul conjTr_one antidiag)

theorem GUFull_eq_heldGU {m Q : ℕ} {E : Type} [Field E] {τ : E ≃+* E} {hτ : ∀ x, τ (τ x) = x}
    (hτQ : ∀ x, τ x = x ^ Q) :
    ClassicalBlocks.GUFull m Q E = Held.heldGU m E τ hτ := by
  have hmap : ∀ A : Matrix (Fin m) (Fin m) E, A.map (· ^ Q) = A.map τ := fun A => by
    ext i j
    simp only [Matrix.map_apply, hτQ]
  apply le_antisymm
  · rw [ClassicalBlocks.GUFull, Subgroup.closure_le]
    intro A hA
    rw [Set.mem_setOf_eq, hmap] at hA
    exact Held.mem_heldGU.mpr hA
  · intro A hA
    refine Subgroup.subset_closure ?_
    rw [Set.mem_setOf_eq, hmap]
    exact Held.mem_heldGU.mp hA

theorem conj_mem_heldGU_of_unitary {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ x, σ (σ x) = x) {P t : GL (Fin n) F}
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      antidiag n)
    (ht : conjTr σ (t : Matrix (Fin n) (Fin n) F) * antidiag n * (t : Matrix (Fin n) (Fin n) F) =
      antidiag n) :
    P * t * P⁻¹ ∈ Held.heldGU n F σ hσ := by
  rw [Held.mem_heldGU]
  change conjTr σ ((P * t * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
    ((P * t * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
  rw [Units.val_mul, Units.val_mul]
  set Pm := (P : Matrix (Fin n) (Fin n) F)
  set Pi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Tm := (t : Matrix (Fin n) (Fin n) F)
  have hPP : Pm * Pi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc conjTr σ (Pm * Tm * Pi) * (Pm * Tm * Pi)
      = conjTr σ Pi * (conjTr σ Tm * (conjTr σ Pm * Pm) * Tm) * Pi := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = conjTr σ Pi * (conjTr σ Pm * Pm) * Pi := by rw [hP, ht]
    _ = conjTr σ (Pm * Pi) * (Pm * Pi) := by simp only [conjTr_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hPP, conjTr_one, Matrix.one_mul]

private theorem charP_of_card_eq_pow_two_mul {L M : Type} [Field L] [Finite L] [CharP L 2]
    [Field M] [Finite M] {Q k : ℕ} (hL : Nat.card L = Q ^ 2)
    (hM : Nat.card M = Q ^ (2 * k)) : CharP M 2 := by
  let instFintypeL : Fintype L := Fintype.ofFinite L
  obtain ⟨n, -, hn⟩ := @FiniteField.card L _ (Fintype.ofFinite L) 2 ‹CharP L 2›
  have hQ : Q ^ 2 = 2 ^ (n : ℕ) := by
    rw [← hL, @Nat.card_eq_fintype_card L (Fintype.ofFinite L), hn]
  have hM2 : Nat.card M = 2 ^ ((n : ℕ) * k) := by
    calc Nat.card M = Q ^ (2 * k) := hM
      _ = (Q ^ 2) ^ k := pow_mul Q 2 k
      _ = (2 ^ (n : ℕ)) ^ k := by rw [hQ]
      _ = 2 ^ ((n : ℕ) * k) := (pow_mul 2 (n : ℕ) k).symm
  let instFintypeM : Fintype M := Fintype.ofFinite M
  exact charP_of_card_eq_prime_pow (p := 2) (f := (n : ℕ) * k) (by
    rwa [← @Nat.card_eq_fintype_card M (Fintype.ofFinite M)])

theorem ggE0Concl_centralizer_heldGU {N Q : ℕ} {L : Type} [Field L] [Finite L] [CharP L 2]
    {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (s : GL (Fin N) L) (hs : s ∈ Held.heldGU N L τ hτ)
    (hodd : Odd (orderOf s)) {C : Subgroup (GL (Fin N) L)}
    (hC : IsComponentOf C (Subgroup.centralizer {s} ⊓ Held.heldGU N L τ hτ)) :
    GGE0Concl (Subgroup.centralizer {s} ⊓ Held.heldGU N L τ hτ) C := by
  have hord : (orderOf s : L) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff L 2] at h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨r, H, hHgrp, hHfin, hblock, ⟨e⟩⟩ :=
    LocalAnalysis.GLTheoremA.Y10GInnUni.centralizerDecomposition_gu hτ hτQ hL s hs hord
  let instGroup : ∀ k, Group (H k) := hHgrp
  let instFinite : ∀ k, Finite (H k) := hHfin
  refine ggE0Concl_of_mulEquiv (e.trans Subgroup.topEquiv.symm) ?_ hC
  intro C₀ hC₀
  refine ggE0Concl_pi (fun k Ck hCk => ?_) hC₀
  rcases hblock k with huni | hlin
  · obtain ⟨a, d, M, hField, hFinite, τ', hτ', hd, hτQ', hcard, ⟨eb⟩⟩ := huni
    let instField : Field M := hField
    let instFiniteM : Finite M := hFinite
    have instCharP : CharP M 2 := charP_of_card_eq_pow_two_mul hL (by
      calc Nat.card M = (Q ^ d) ^ 2 := hcard
        _ = Q ^ (d * 2) := (pow_mul Q d 2).symm
        _ = Q ^ (2 * d) := by rw [Nat.mul_comm d 2])
    have hGU : ClassicalBlocks.GUFull a (Q ^ d) M = Held.heldGU a M τ' hτ' :=
      GUFull_eq_heldGU (m := a) (Q := Q ^ d) (E := M) (τ := τ') (hτ := hτ') hτQ'
    refine ggE0Concl_of_mulEquiv (Subgroup.topEquiv.trans (eb.trans
      (MulEquiv.subgroupCongr hGU.symm))) (fun C' hC' => ggE0Concl_unitaryFull hcard C' hC')
      hCk
  · obtain ⟨b, k, M, hField, hFinite, hcard, ⟨eb⟩⟩ := hlin
    let instField : Field M := hField
    let instFiniteM : Finite M := hFinite
    have instCharP : CharP M 2 := charP_of_card_eq_pow_two_mul hL hcard
    exact ggE0Concl_of_mulEquiv (Subgroup.topEquiv.trans (eb.trans
      Subgroup.topEquiv.symm)) (fun C' hC' => ggE0Concl_top_generalLinear C' hC') hCk

theorem largeEvenMarking_of_isComponentOf_centralizer_heldGU {N Q : ℕ} {L : Type} [Field L] [Finite L] [CharP L 2]
    {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (s : GL (Fin N) L) (hs : s ∈ Held.heldGU N L τ hτ)
    (hodd : Odd (orderOf s)) {C : Subgroup (GL (Fin N) L)}
    (hC : IsComponentOf C (Subgroup.centralizer {s} ⊓ Held.heldGU N L τ hτ)) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  have hord : (orderOf s : L) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff L 2] at h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨r, H, hHgrp, hHfin, hblock, ⟨e⟩⟩ :=
    LocalAnalysis.GLTheoremA.Y10GInnUni.centralizerDecomposition_gu hτ hτQ hL s hs hord
  let instGroup : ∀ k, Group (H k) := hHgrp
  let instFinite : ∀ k, Finite (H k) := hHfin
  refine largeEvenMarking_of_isComponentOf_mulEquiv (e.trans Subgroup.topEquiv.symm) ?_ hC
  intro C₀ hC₀
  refine largeEvenMarking_of_isComponentOf_pi (fun k Ck hCk => ?_) hC₀
  rcases hblock k with huni | hlin
  · obtain ⟨a, d, M, hField, hFinite, τ', hτ', hd, hτQ', hcard, ⟨eb⟩⟩ := huni
    let instField : Field M := hField
    let instFiniteM : Finite M := hFinite
    have instCharP : CharP M 2 := charP_of_card_eq_pow_two_mul hL (by
      calc Nat.card M = (Q ^ d) ^ 2 := hcard
        _ = Q ^ (d * 2) := (pow_mul Q d 2).symm
        _ = Q ^ (2 * d) := by rw [Nat.mul_comm d 2])
    have hGU : ClassicalBlocks.GUFull a (Q ^ d) M = Held.heldGU a M τ' hτ' :=
      GUFull_eq_heldGU (m := a) (Q := Q ^ d) (E := M) (τ := τ') (hτ := hτ') hτQ'
    refine largeEvenMarking_of_isComponentOf_mulEquiv (Subgroup.topEquiv.trans (eb.trans
      (MulEquiv.subgroupCongr hGU.symm))) (fun C' hC' => largeEvenMarking_of_isComponentOf_unitaryFull hcard hC')
      hCk
  · obtain ⟨b, k, M, hField, hFinite, hcard, ⟨eb⟩⟩ := hlin
    let instField : Field M := hField
    let instFiniteM : Finite M := hFinite
    have instCharP : CharP M 2 := charP_of_card_eq_pow_two_mul hL hcard
    exact largeEvenMarking_of_isComponentOf_mulEquiv (Subgroup.topEquiv.trans (eb.trans
      Subgroup.topEquiv.symm)) (fun C' hC' => largeEvenMarking_of_isComponentOf_top_generalLinear hC') hCk

private theorem exists_frobenius_statedSU {N₀ Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) :
    ∃ (_f : ℕ) (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x),
      (∀ x, τ x = x ^ Q) ∧
      ClassicalBlocks.GUFull N₀ Q E = Held.heldGU N₀ E τ hτ ∧
      CFSG.Open.StatedSU N₀ Q E = Held.heldSU N₀ E τ hτ := by
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q) (by
    rw [← Nat.card_eq_fintype_card]; exact hE)
  let τ : E ≃+* E := RingEquiv.ofBijective hUF.bar
    ⟨fun a b h => by
        have h' := congrArg hUF.bar h
        simpa only [hUF.bar_bar] using h',
      fun y => ⟨hUF.bar y, hUF.bar_bar y⟩⟩
  have hτ : ∀ x, τ (τ x) = x := hUF.bar_bar
  have hτQ : ∀ x, τ x = x ^ Q := by
    intro x
    change hUF.bar x = x ^ Q
    rw [hUF.bar_apply, hQf]
  refine ⟨f, τ, hτ, hτQ, ?_, ?_⟩
  · exact GUFull_eq_heldGU (m := N₀) (Q := Q) (E := E) (τ := τ) (hτ := hτ) hτQ
  · exact (Held.hct_heldSU_eq_statedSU (a := N₀) (Q := Q) (M := E) (τ := τ) (hτ := hτ) hτQ).symm

theorem isComponentOf_centralizer_statedSU_iff {N Q : ℕ} {E : Type} [Field E] [Finite E]
    [CharP E 2] (hE : Nat.card E = Q ^ 2) (s : ↥(CFSG.Open.StatedSU N Q E))
    {C : Subgroup (GL (Fin N) E)} :
    IsComponentOf C (Subgroup.centralizer ({(s : GL (Fin N) E)} : Set (GL (Fin N) E)) ⊓
        ClassicalBlocks.GUFull N Q E) ↔
      IsComponentOf C
        ((Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSU N Q E))).map
          (CFSG.Open.StatedSU N Q E).subtype) := by
  obtain ⟨f, τ, hτ, hτQ, hGU, hSU⟩ := exists_frobenius_statedSU (N₀ := N) hE
  let SU := CFSG.Open.StatedSU N Q E
  let H : Subgroup (GL (Fin N) E) :=
    Subgroup.centralizer ({(s : GL (Fin N) E)} : Set (GL (Fin N) E)) ⊓ Held.heldGU N E τ hτ
  let Nsu : Subgroup (GL (Fin N) E) :=
    SU ⊓ Subgroup.centralizer ({(s : GL (Fin N) E)} : Set (GL (Fin N) E))
  have hmap : (Subgroup.centralizer ({s} : Set ↥SU)).map SU.subtype = Nsu := by
    have h := CFSG.ABGDGroups.map_inf_centralizer_of_injective SU.subtype
      (Subtype.val_injective) (⊤ : Subgroup ↥SU) s
    simpa only [Subgroup.map_top, Subgroup.range_subtype, top_inf_eq, Subgroup.coe_subtype,
      Nsu] using h
  have hNH : Nsu ≤ H := by
    rintro x ⟨hxSU, hxC⟩
    refine ⟨hxC, ?_⟩
    have hxSU' : x ∈ CFSG.Open.StatedSU N Q E := hxSU
    rw [hSU] at hxSU'
    exact hxSU'.1
  have hab : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ Nsu := by
    intro a ha b hb
    have hcomm : ⁅a, b⁆ ∈ Held.heldSU N E τ hτ := Held.commutatorElement_mem_heldSU ha.2 hb.2
    rw [← hSU] at hcomm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [commutatorElement_def] using hcomm
    · exact mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1)
  rw [hmap, hGU]
  exact isComponentOf_iff_of_normal_of_commutator_le hNH hab

theorem largeEvenMarking_of_isComponentOf_centralizer_statedSU {N Q : ℕ} {E : Type} [Field E]
    [Finite E] [CharP E 2] (hE : Nat.card E = Q ^ 2) (s : ↥(CFSG.Open.StatedSU N Q E))
    (hs : Odd (orderOf s)) {C : Subgroup ↥(CFSG.Open.StatedSU N Q E)}
    (hC : IsComponentOf C (Subgroup.centralizer {s})) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  obtain ⟨f, τ, hτ, hτQ, hGU, hSU⟩ := exists_frobenius_statedSU (N₀ := N) hE
  let SU := CFSG.Open.StatedSU N Q E
  let e : ↥(Subgroup.centralizer ({s} : Set ↥SU)) ≃*
      ↥((Subgroup.centralizer ({s} : Set ↥SU)).map SU.subtype) :=
    Subgroup.equivMapOfInjective _ _ (Subtype.val_injective)
  refine largeEvenMarking_of_isComponentOf_mulEquiv e ?_ hC
  intro C' hC'
  have hC'' : IsComponentOf C'
      (Subgroup.centralizer ({(s : GL (Fin N) E)} : Set (GL (Fin N) E)) ⊓
        ClassicalBlocks.GUFull N Q E) := by
    exact (isComponentOf_centralizer_statedSU_iff hE s).mpr hC'
  rw [hGU] at hC''
  have hsGU : (s : GL (Fin N) E) ∈ Held.heldGU N E τ hτ := by
    have hsSU : (s : GL (Fin N) E) ∈ Held.heldSU N E τ hτ := by
      rw [← hSU]
      exact s.2
    exact hsSU.1
  have hodd : Odd (orderOf (s : GL (Fin N) E)) := by rwa [Subgroup.orderOf_coe]
  exact largeEvenMarking_of_isComponentOf_centralizer_heldGU hτ hτQ hE (s : GL (Fin N) E) hsGU
    hodd hC''

theorem ggE0Concl_centralizer_statedSU {N Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) (s : ↥(CFSG.Open.StatedSU N Q E))
    (hs : Odd (orderOf s)) {C : Subgroup ↥(CFSG.Open.StatedSU N Q E)}
    (hC : IsComponentOf C (Subgroup.centralizer {s})) :
    GGE0Concl (Subgroup.centralizer {s}) C := by
  obtain ⟨f, τ, hτ, hτQ, hGU, hSU⟩ := exists_frobenius_statedSU (N₀ := N) hE
  let SU := CFSG.Open.StatedSU N Q E
  let H : Subgroup (GL (Fin N) E) :=
    Subgroup.centralizer ({(s : GL (Fin N) E)} : Set (GL (Fin N) E)) ⊓ Held.heldGU N E τ hτ
  let Nsu : Subgroup (GL (Fin N) E) :=
    SU ⊓ Subgroup.centralizer ({(s : GL (Fin N) E)} : Set (GL (Fin N) E))
  have hmap : (Subgroup.centralizer ({s} : Set ↥SU)).map SU.subtype = Nsu := by
    have h := CFSG.ABGDGroups.map_inf_centralizer_of_injective SU.subtype
      (Subtype.val_injective) (⊤ : Subgroup ↥SU) s
    simpa only [Subgroup.map_top, Subgroup.range_subtype, top_inf_eq, Subgroup.coe_subtype,
      Nsu] using h
  have hNH : Nsu ≤ H := by
    rintro x ⟨hxSU, hxC⟩
    refine ⟨hxC, ?_⟩
    have hxSU' : x ∈ CFSG.Open.StatedSU N Q E := hxSU
    rw [hSU] at hxSU'
    exact hxSU'.1
  have hab : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ Nsu := by
    intro a ha b hb
    have hcomm : ⁅a, b⁆ ∈ Held.heldSU N E τ hτ := Held.commutatorElement_mem_heldSU ha.2 hb.2
    rw [← hSU] at hcomm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [commutatorElement_def] using hcomm
    · exact mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1)
  have hC' : IsComponentOf (C.map SU.subtype) Nsu := by
    rw [← hmap]
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (Subtype.val_injective)).mpr hC
  have hC_GU : IsComponentOf (C.map SU.subtype) H :=
    (isComponentOf_iff_of_normal_of_commutator_le (N := Nsu) (H := H) hNH hab).mpr hC'
  have hsGU : (s : GL (Fin N) E) ∈ Held.heldGU N E τ hτ := by
    have hsSU : (s : GL (Fin N) E) ∈ Held.heldSU N E τ hτ := by
      rw [← hSU]
      exact s.2
    exact hsSU.1
  have hodd : Odd (orderOf (s : GL (Fin N) E)) := by rwa [Subgroup.orderOf_coe]
  have hGUconcl : GGE0Concl H (C.map SU.subtype) :=
    ggE0Concl_centralizer_heldGU hτ hτQ hE (s : GL (Fin N) E) hsGU hodd hC_GU
  have hmono : GGE0Concl Nsu (C.map SU.subtype) := ggE0Concl_mono hNH hGUconcl
  rw [← hmap] at hmono
  exact (ggE0Concl_map_iff SU.subtype (Subtype.val_injective)
    (Subgroup.centralizer {s}) C).1 hmono

theorem ggE0Concl_centralizer_statedSU_strong {N Q : ℕ} {E : Type} [Field E] [Finite E]
    [CharP E 2] (hE : Nat.card E = Q ^ 2) (s : ↥(CFSG.Open.StatedSU N Q E))
    (hs : Odd (orderOf s)) {C : Subgroup ↥(CFSG.Open.StatedSU N Q E)}
    (hC : IsComponentOf C (Subgroup.centralizer {s})) :
    Subgroup.centralizer {s} ≤ Subgroup.normalizer (C : Set ↥(CFSG.Open.StatedSU N Q E)) ∧
      LargeEvenMarking ↥C (fun lab _R _ I _F θ => GGChevStTag lab ∧
        ∀ ε ∈ Subgroup.centralizer {s}, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' : ↥C =>
            (l' : ↥(CFSG.Open.StatedSU N Q E)) = ε⁻¹ * l * ε) φ) := by
  obtain ⟨hnorm, hact⟩ := ggE0Concl_centralizer_statedSU hE s hs hC
  exact ⟨hnorm, hact (largeEvenMarking_of_isComponentOf_centralizer_statedSU hE s hs hC)⟩

end CFSG.StandardType
