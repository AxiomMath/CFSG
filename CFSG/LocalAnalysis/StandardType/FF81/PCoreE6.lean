module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import CFSG.GroupTheory.PCore.Construction
import CFSG.LocalAnalysis.StandardType.FF81.E6Position
import CFSG.LocalAnalysis.StandardType.FF81.CentralizerOdd
import CFSG.LocalAnalysis.StandardType.FF81.TransvectionCentO2
import CFSG.LocalAnalysis.StandardType.FS81.RootCentralizerO2
import CFSG.LocalAnalysis.StandardType.FS81.S7Fusion
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRootO2
import CFSG.GroupTheory.OppositeRadicals
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.StandardType.FF81

open CFSG CFSG.Assembly CFSG.Open

private theorem pce6_conj_normalizer {G : Type*} [Group G]
    {L T : Subgroup G} {y b t b' s : G}
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hTN : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (T : Set G))
    (hb' : b' = y * b * y⁻¹) (hs : s = y⁻¹ * t * y) :
    L ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({b'} : Set G)).map
        (MulAut.conj y⁻¹).toMonoidHom : Set G) := by
  intro c hc
  have hcb : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp (hLb hc.1)
  have hcs : c * s = s * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hycy_t : y * c * y⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : c * (y⁻¹ * t * y) = (y⁻¹ * t * y) * c := by rw [← hs]; exact hcs
    calc y * c * y⁻¹ * t = y * (c * (y⁻¹ * t * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * t * y) * c) * y⁻¹ := by rw [h]
      _ = t * (y * c * y⁻¹) := by group
  have hycy_b' : y * c * y⁻¹ ∈ Subgroup.centralizer ({b'} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hb']
    calc y * c * y⁻¹ * (y * b * y⁻¹) = y * (c * b) * y⁻¹ := by group
      _ = y * (b * c) * y⁻¹ := by rw [hcb]
      _ = (y * b * y⁻¹) * (y * c * y⁻¹) := by group
  have hycy_inf : y * c * y⁻¹ ∈ Subgroup.normalizer (T : Set G) ⊓
      Subgroup.normalizer (Subgroup.centralizer ({b'} : Set G) : Set G) :=
    ⟨hTN hycy_t, Subgroup.le_normalizer hycy_b'⟩
  have hycy_N : y * c * y⁻¹ ∈
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({b'} : Set G)) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf hycy_inf
  change c ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({b'} : Set G)).map
    (MulAut.conj y⁻¹).toMonoidHom : Set G)
  rw [← Subgroup.map_equiv_normalizer_eq (H := T ⊓ Subgroup.centralizer ({b'} : Set G))
    (MulAut.conj y⁻¹)]
  exact Subgroup.mem_map.mpr ⟨y * c * y⁻¹, hycy_N, by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩

private theorem pce6_conj_2subgroup {G : Type*} [Group G]
    {L T : Subgroup G} {y b t b' s : G}
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hT2 : IsPGroup 2 T)
    (hTH : T ≤ Subgroup.centralizer ({t} : Set G))
    (hTN : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (T : Set G))
    (hb' : b' = y * b * y⁻¹) (hs : s = y⁻¹ * t * y) :
    ∃ P' : Subgroup G, IsPGroup 2 P' ∧
      P' ≤ Subgroup.centralizer ({b} : Set G) ∧
      P' ≤ Subgroup.centralizer ({s} : Set G) ∧
      L ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer (P' : Set G) ∧
      (∀ x ∈ T ⊓ Subgroup.centralizer ({b'} : Set G), y⁻¹ * x * y ∈ P') := by
  classical
  let Cb' : Subgroup G := Subgroup.centralizer ({b'} : Set G)
  let P' : Subgroup G := (T ⊓ Cb').map (MulAut.conj y⁻¹).toMonoidHom
  have hP'2 : IsPGroup 2 P' := (hT2.to_le inf_le_left).map _
  have hP'Cb : P' ≤ Subgroup.centralizer ({b} : Set G) := by
    rintro z ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Subgroup.mem_centralizer_singleton_iff]
    have hxb' : x * b' = b' * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    rw [hb'] at hxb'
    calc y⁻¹ * x * y * b = y⁻¹ * (x * (y * b * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * b * y⁻¹) * x) * y := by rw [hxb']
      _ = b * (y⁻¹ * x * y) := by group
  have hP's : P' ≤ Subgroup.centralizer ({s} : Set G) := by
    rintro z ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Subgroup.mem_centralizer_singleton_iff, hs]
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hTH hx.1)
    calc y⁻¹ * x * y * (y⁻¹ * t * y) = y⁻¹ * (x * t) * y := by group
      _ = y⁻¹ * (t * x) * y := by rw [hxt]
      _ = y⁻¹ * t * y * (y⁻¹ * x * y) := by group
  have hnor : L ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer (P' : Set G) :=
    pce6_conj_normalizer hLb hTN hb' hs
  refine ⟨P', hP'2, hP'Cb, hP's, hnor, ?_⟩
  intro x hx
  have h := Subgroup.mem_map_of_mem (MulAut.conj y⁻¹).toMonoidHom (K := T ⊓ Cb') hx
  simpa only [P', MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h

private theorem pce6_inf_centralizer_le_Y {G : Type*} [Group G] [Finite G]
    {Y L T P' : Subgroup G} {y b b' s : G} {m : ℕ}
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hLN : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer (L : Set G))))
    (hP'2 : IsPGroup 2 P') (hP'b : P' ≤ Subgroup.centralizer ({b} : Set G))
    (hP's : P' ≤ Subgroup.centralizer ({s} : Set G))
    (hnor : L ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer (P' : Set G))
    (hP'mem : ∀ x ∈ T ⊓ Subgroup.centralizer ({b'} : Set G), y⁻¹ * x * y ∈ P')
    (hyY : y ∈ Y) (hLY : L ≤ Y)
    (hm : 5 ≤ m) (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (hsL : s ∈ L)
    (hes : ∃ (i j : Fin m) (hij : i ≠ j),
      e ⟨s, hsL⟩ = Matrix.SpecialLinearGroup.transvection hij 1) :
    T ⊓ Subgroup.centralizer ({b'} : Set G) ≤ Y := by
  have hP'L : P' ≤ L :=
    le_of_isPGroup_of_le_centralizer_transvection (m := m) hm e hsL hes
      hLb hLN hodd hP'2 hP'b hP's hnor
  intro x hx
  have hx' : y⁻¹ * x * y ∈ P' := hP'mem x hx
  have hx'L : y⁻¹ * x * y ∈ L := hP'L hx'
  have hY : y * (y⁻¹ * x * y) * y⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem hyY (hLY hx'L)) (Y.inv_mem hyY)
  simpa [mul_assoc] using hY

private theorem pce6_inf_range_eq_map_centralizer {X G : Type*} [Group X] [Group G]
    (φ : X →* G) (hφ : Function.Injective φ) (Y : Subgroup G) (hY : φ.range = Y)
    {x : X} {t : G} (hx : φ x = t) :
    Subgroup.centralizer ({t} : Set G) ⊓ Y =
      (Subgroup.centralizer ({x} : Set X)).map φ := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨hzC, hzY⟩
    have hzr : z ∈ φ.range := by
      rw [hY]
      exact hzY
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hzr
    have hzCt : z * t = t * z := Subgroup.mem_centralizer_singleton_iff.mp hzC
    refine Subgroup.mem_map.mpr ⟨a, ?_, ha⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hφ
    rw [map_mul, map_mul, hx, ha]
    exact hzCt
  · rintro z ⟨a, haC, rfl⟩
    have haC' : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp haC
    refine ⟨?_, ?_⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← hx, ← map_mul, ← map_mul, haC']
    · rw [← hY]
      exact MonoidHom.mem_range.mpr ⟨a, rfl⟩

private theorem pce6_irreducible_of_map {X G : Type*} [Group X] [Group G] {φ : X →* G}
    (hφ : Function.Injective φ) {Q L : Subgroup G} {U L₀ : Subgroup X} {x : X} {t : G}
    (hQ : Q = U.map φ) (hL : L₀.map φ = L) (hx : φ x = t)
    (hirr : ∀ V : Subgroup X, Subgroup.zpowers x ≤ V → V ≤ U →
      L₀ ≤ Subgroup.normalizer (V : Set X) → V = Subgroup.zpowers x ∨ V = U) :
    ∀ V : Subgroup G, Subgroup.zpowers t ≤ V → V ≤ Q →
      L ≤ Subgroup.normalizer (V : Set G) → V = Subgroup.zpowers t ∨ V = Q := by
  intro V h1 h2 hN
  have hQrange : Q ≤ φ.range := by rw [hQ]; exact Subgroup.map_le_range φ U
  have hVrange : V ≤ φ.range := h2.trans hQrange
  have hVmap : (V.comap φ).map φ = V := Subgroup.map_comap_eq_self hVrange
  have h1' : Subgroup.zpowers x ≤ V.comap φ := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_comap, hx]
    exact h1 (Subgroup.mem_zpowers t)
  have h2' : V.comap φ ≤ U := by
    intro a ha
    have hφa : φ a ∈ U.map φ := by
      rw [← hQ]
      exact h2 ha
    obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp hφa
    rwa [hφ hua] at hu
  have hN' : L₀ ≤ Subgroup.normalizer ((V.comap φ) : Set X) := by
    intro l hl
    have hφl : φ l ∈ L := by
      rw [← hL]
      exact Subgroup.mem_map_of_mem φ hl
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have hmem : φ l * φ a * (φ l)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hN hφl) (φ a)).mp (Subgroup.mem_comap.mp ha)
      simpa [map_mul, map_inv] using hmem
    · intro ha
      have hmem : φ l * φ a * (φ l)⁻¹ ∈ V := by
        simpa [map_mul, map_inv] using (Subgroup.mem_comap.mp ha)
      exact (Subgroup.mem_normalizer_iff.mp (hN hφl) (φ a)).mpr hmem
  rcases hirr (V.comap φ) h1' h2' hN' with h | h
  · left
    rw [← hVmap, h, MonoidHom.map_zpowers, hx]
  · right
    rw [← hVmap, h]
    exact hQ.symm

section PCoreE6

private theorem pce6_pCoreOf_eq_of_transvection {G : Type} [Group G] [Finite G]
    {Y L P : Subgroup G} {b t b' s y : G} {m : ℕ}
    (hm : 5 ≤ m) (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (hsL : s ∈ L)
    (hes : ∃ (i j : Fin m) (hij : i ≠ j),
      e ⟨s, hsL⟩ = Matrix.SpecialLinearGroup.transvection hij 1)
    (hLY : L ≤ Y) (hyY : y ∈ Y)
    (hLt : L ≤ Subgroup.centralizer ({t} : Set G))
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hLN : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer (L : Set G))))
    (hPL : P ≤ L)
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hb' : b' = y * b * y⁻¹) (hb'P : b' ∈ P) (hs : s = y⁻¹ * t * y)
    (hb'3 : orderOf b' = 3) (ht : orderOf t = 2)
    (hcharH : CFSG.QuasithinUnique.CharTwo (Subgroup.centralizer ({t} : Set G)))
    (φ : GGSixE6Two.EC →* G) (hφinj : Function.Injective φ) (hφrange : φ.range = Y)
    (hφx : φ (GGSixE6Two.xr (CFSG.SeitzReduction.highRoot .E6)) = t)
    (hφL : GGSixE6Two.lE.map φ = L) :
    pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) =
      pCoreOf 2 (Subgroup.centralizer ({t} : Set G) ⊓ Y) := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let T : Subgroup G := pCoreOf 2 H
  let Q : Subgroup G := pCoreOf 2 (H ⊓ Y)
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H
  have hTH : T ≤ H := CFSG.LieType.BorelTits.pCoreOf_le (r := 2) H
  have hTN : H ≤ Subgroup.normalizer (T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H
  obtain ⟨P', hP'2, hP'b, hP's, hnor, hP'mem⟩ :=
    pce6_conj_2subgroup hLb hT2 hTH hTN hb' hs
  have hCY : T ⊓ Subgroup.centralizer ({b'} : Set G) ≤ Y :=
    pce6_inf_centralizer_le_Y hLb hLN hodd hP'2 hP'b hP's hnor hP'mem hyY hLY hm e hsL hes
  have hTY : T ⊓ Y ≤ Q := by
    change T ⊓ Y ≤ pCoreOf 2 (H ⊓ Y)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) ?_ ?_ ?_
    · exact le_inf (inf_le_left.trans hTH) inf_le_right
    · exact (le_inf (inf_le_left.trans hTN) (inf_le_right.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact hT2.to_le inf_le_left
  have hCTQ : T ⊓ Subgroup.centralizer ({b'} : Set G) ≤ Q :=
    (le_inf inf_le_left hCY).trans hTY
  have hHYeq : H ⊓ Y =
      (Subgroup.centralizer ({GGSixE6Two.xr (CFSG.SeitzReduction.highRoot .E6)} :
        Set GGSixE6Two.EC)).map φ :=
    pce6_inf_range_eq_map_centralizer φ hφinj Y hφrange hφx
  have hQeq : Q =
      (CFSG.SeitzReduction.EPilot.highRadical .E6 CFSG.StandardType.GGHalf.F2).map φ := by
    change pCoreOf 2 (H ⊓ Y) = _
    rw [hHYeq, CFSG.GroupTheory.pCoreOf_map_of_injective 2 φ hφinj,
      GGSixE6Two.pCoreOf_centralizer_xr_highRoot]
  have hirr : ∀ V : Subgroup G, Subgroup.zpowers t ≤ V → V ≤ Q →
      L ≤ Subgroup.normalizer (V : Set G) → V = Subgroup.zpowers t ∨ V = Q :=
    pce6_irreducible_of_map (φ := φ) hφinj hQeq hφL hφx
      (fun V h1 h2 hN => GGSixE6Two.eq_zpowers_or_eq_highRadical_of_le h1 h2 hN)
  have hLHY : L ≤ H ⊓ Y := le_inf hLt hLY
  have hLU : L ≤ Subgroup.normalizer (Q : Set G) := by
    change L ≤ Subgroup.normalizer (pCoreOf 2 (H ⊓ Y) : Set G)
    exact hLHY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (H ⊓ Y))
  have hmain := CFSG.StandardType.FrameRoute.FS81.pCoreOf_centralizer_eq_of_inf_centralizer_le
    (X := G) ht hLt hLU hirr hb'3 hb'P hPL hP hCTQ hcharH
  simpa [H, Q] using hmain

private theorem pce6_position_data {G : Type*} [Group G] {Y L : Subgroup G} {b t : G}
    (hb : orderOf b = 3)
    (φ : GGSixE6Two.EC →* G) (hφinj : Function.Injective φ) (hφrange : φ.range = Y)
    (hφx : φ (GGSixE6Two.xr (CFSG.SeitzReduction.highRoot .E6)) = t)
    (hφz : φ GGSixE6Two.zE = b) (hφL : GGSixE6Two.lE.map φ = L) :
    ∃ (y b' s : G) (P : Subgroup G)
      (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)),
      y ∈ Y ∧ b' = y * b * y⁻¹ ∧ s = y⁻¹ * t * y ∧ b' ∈ P ∧ P ≤ L ∧
      Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      orderOf b' = 3 ∧
      ∃ (hsL : s ∈ L) (i j : Fin 6) (hij : i ≠ j),
        e ⟨s, hsL⟩ = Matrix.SpecialLinearGroup.transvection hij 1 := by
  classical
  obtain ⟨g, J, hJlE, ⟨eJ⟩, hgzJ, i, j, hij, hgt⟩ :=
    GGSixE6Two.exists_conj_zE_mem_slThree_and_transvection
  let ψ : Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) →* G :=
    φ.comp GGSixE6Two.slSixToEC
  have hψinj : Function.Injective ψ := hφinj.comp GGSixE6Two.injective_slSixToEC
  have hψrange : ψ.range = L := by
    rw [MonoidHom.range_comp, GGSixE6Two.range_slSixToEC, hφL]
  let e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) :=
    (MulEquiv.subgroupCongr hψrange.symm).trans (MonoidHom.ofInjective hψinj).symm
  let y : G := φ g
  let b' : G := y * b * y⁻¹
  let s : G := y⁻¹ * t * y
  have hyY : y ∈ Y := by
    rw [← hφrange]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hb'eq : b' = φ (g * GGSixE6Two.zE * g⁻¹) := by
    rw [show b' = φ g * b * (φ g)⁻¹ from rfl]
    rw [map_mul, map_mul, map_inv, hφz]
  let P : Subgroup G := J.map φ
  have hPL : P ≤ L := by
    change J.map φ ≤ L
    rw [← hφL]
    exact Subgroup.map_mono hJlE
  have hb'P : b' ∈ P := by
    rw [hb'eq]
    exact Subgroup.mem_map_of_mem φ hgzJ
  have hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    ⟨(J.equivMapOfInjective φ hφinj).symm.trans eJ⟩
  have hb'3 : orderOf b' = 3 := by
    have h := (MulAut.conj y).orderOf_eq b
    rw [hb, MulAut.conj_apply] at h
    simpa only [b'] using h
  have hseq : s = φ (g⁻¹ * GGSixE6Two.xr (CFSG.SeitzReduction.highRoot .E6) * g) := by
    rw [show s = (φ g)⁻¹ * t * φ g from rfl]
    rw [map_mul, map_mul, map_inv, hφx]
  have hstr : s = ψ (Matrix.SpecialLinearGroup.transvection hij 1) := by
    rw [hseq, hgt]
    rfl
  have hsL : s ∈ L := by
    rw [hstr, ← hψrange]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hes : e ⟨s, hsL⟩ = Matrix.SpecialLinearGroup.transvection hij 1 := by
    apply hψinj
    change ψ ((MonoidHom.ofInjective hψinj).symm
      (MulEquiv.subgroupCongr hψrange.symm ⟨s, hsL⟩)) =
        ψ (Matrix.SpecialLinearGroup.transvection hij 1)
    rw [MonoidHom.apply_ofInjective_symm]
    simpa using hstr
  exact ⟨y, b', s, P, e, hyY, rfl, rfl, hb'P, hPL, hP, hb'3, hsL, i, j, hij, hes⟩

theorem pCore_centralizer_eq_in_Y_of_e6
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hchar : IsCharTwoType G)
    (n : ℕ) (b : G) (L : Subgroup G) (hA : HypA G n b L)
    (K : ℕ → Subgroup G) (t : G) (hup : Upstream n b L K t)
    (hYd : YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t)
    (h5 : n = 5)
    (hlab : GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ))) :
    let Y := ⨆ i : Fin (n + 2), K (i : ℕ)
    let H := Subgroup.centralizer ({t} : Set G)
    let HY := H ⊓ Y
    (CFSG.pCore 2 ↥H).map H.subtype =
      (CFSG.pCore 2 ↥HY).map HY.subtype := by
  classical
  subst h5
  have hFS : FrameSystem 5 b L K t := hup.choose_spec.2
  obtain ⟨φ, hφinj, hφrange, hφx, hφz, hφL, -⟩ :=
    exists_e6Position_of_yData hA hup hYd rfl hlab
  obtain ⟨y, b', s, P, e, hyY, hb', hs, hb'P, hPL, hP, hb'3, hsL, i, j, hij, hes⟩ :=
    pce6_position_data hA.ord φ hφinj hφrange hφx hφz hφL
  have htK0 : t ∈ K 0 := by
    rw [hFS.K0]
    exact (le_sup_right : Subgroup.zpowers t ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers t)
      (Subgroup.mem_zpowers t)
  have hLt : L ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hFS.comm_L t htK0 x hx).symm
  have hcharH : CFSG.QuasithinUnique.CharTwo (Subgroup.centralizer ({t} : Set G)) :=
    CFSG.StandardType.FrameRoute.FS81.centralizer_inf_le_pCoreOf_of_isCharTwoType
      hchar hFS.ord_t
  have hmain := pce6_pCoreOf_eq_of_transvection (m := 6) (by norm_num) e hsL
    ⟨i, j, hij, hes⟩ hYd.le hyY hLt hA.le hA.nor
    (odd_card_centralizer_inf_centralizer hA hup) hPL hP hb' hb'P hs hb'3 hFS.ord_t hcharH
    φ hφinj hφrange hφx hφL
  dsimp only
  rw [← CFSG.Assembly.pCoreOf_eq_map_pCore 2 (Subgroup.centralizer ({t} : Set G)),
    ← CFSG.Assembly.pCoreOf_eq_map_pCore 2 (Subgroup.centralizer ({t} : Set G) ⊓
      ⨆ i : Fin (5 + 2), K (i : ℕ))]
  exact hmain

end PCoreE6

end CFSG.StandardType.FF81

end
