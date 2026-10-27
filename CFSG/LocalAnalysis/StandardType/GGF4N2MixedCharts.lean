module

public import CFSG.LocalAnalysis.StandardType.GGF4N2JPositions
public import CFSG.LocalAnalysis.StandardType.GGF4N2Frame
public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartAlign
public import CFSG.LocalAnalysis.StandardType.GGF4N2CentralImageE6
public import CFSG.LocalAnalysis.StandardType.GGF4N2NbrReflectionMinus
public import CFSG.LocalAnalysis.StandardType.GGF4N2TorusTraceWitness
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGE0ShapeConjAux
import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan

theorem ggBlockFourMat_eq_blockMat {K : Type} [Field K] (A : Matrix (Fin 4) (Fin 4) K) :
    CFSG.SeitzReduction.E6Pilot.blockFourMat A = blockMat 6 0 A := by
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;>
    simp [CFSG.SeitzReduction.E6Pilot.blockFourMat, CFSG.SeitzReduction.E6Pilot.e46, Matrix.fromBlocks]

theorem ggBlockFour_eq_blockSL {K : Type} [Field K] :
    (CFSG.SeitzReduction.E6Pilot.blockFour (K := K) :
        Matrix.SpecialLinearGroup (Fin 4) K →* Matrix.SpecialLinearGroup (Fin 6) K) =
      blockSL K 6 4 0 (by norm_num) :=
  MonoidHom.ext fun A => Subtype.ext (by
    rw [CFSG.SeitzReduction.E6Pilot.coe_blockFour, coe_blockSL, ggBlockFourMat_eq_blockMat])

theorem ggBlockSL_range_eq_blockSpecialLinear {F : Type} [Field F] {m k i : ℕ} (h : i + k ≤ m)
    (I : Finset (Fin m)) (hI : ∀ a : Fin m, a ∈ I ↔ i ≤ a.val ∧ a.val < i + k) :
    (blockSL F m k i h).range = CFSG.SeitzReduction.LinearPilot.blockSpecialLinear I := by
  ext A
  constructor
  · rintro ⟨B, rfl⟩
    intro a b hab
    rw [coe_blockSL]
    rcases hab with ha | hb
    · exact blockMat_apply_of_not_mem_left _ (fun h' => ha ((hI a).2 h')) b
    · exact blockMat_apply_of_not_mem_right _ a (fun h' => hb ((hI b).2 h'))
  · intro hA
    let B : Matrix (Fin k) (Fin k) F :=
      fun x y => (A : Matrix (Fin m) (Fin m) F) (blockIdx i h x) (blockIdx i h y)
    have hBA : blockMat m i B = (A : Matrix (Fin m) (Fin m) F) := by
      ext a b
      rw [blockMat_apply]
      split_ifs with hab
      · have ha : blockIdx i h ⟨a.val - i, by omega⟩ = a := Fin.ext (by simp; omega)
        have hb : blockIdx i h ⟨b.val - i, by omega⟩ = b := Fin.ext (by simp; omega)
        simp only [B, ha, hb]
      · refine (hA a b ?_).symm
        by_contra hc
        push Not at hc
        exact hab ⟨(hI a).1 hc.1, (hI b).1 hc.2⟩
    have hdet : B.det = 1 := by rw [← det_blockMat h, hBA]; exact A.2
    exact ⟨⟨B, hdet⟩, Subtype.ext hBA⟩

theorem ggSL6Chart_complement_eq_commutator_centralizer {G : Type} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) :
    (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ =
      ⁅ψ.range ⊓ Subgroup.centralizer
          (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G),
        ψ.range ⊓ Subgroup.centralizer
          (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G)⁆ := by
  have hM : (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range = N2KComplementary.blockM :=
    ggBlockSL_range_eq_blockSpecialLinear _ _ (by decide)
  have hM' : (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range = N2KComplementary.blockM' :=
    ggBlockSL_range_eq_blockSpecialLinear _ _ (by decide)
  rw [hM, hM']
  have hker : ψ.rangeRestrict.ker ≤ Subgroup.center _ := by rwa [MonoidHom.ker_rangeRestrict]
  have key := congrArg (Subgroup.map ψ.range.subtype)
    (N2KComplementary.commutator_centralizer_map_blockM_eq_map_blockM' ψ.rangeRestrict
      ψ.rangeRestrict_surjective hker)
  have hcomp : ψ.range.subtype.comp ψ.rangeRestrict = ψ := MonoidHom.subtype_comp_rangeRestrict ψ
  have hC : (Subgroup.centralizer
        ((N2KComplementary.blockM.map ψ.rangeRestrict : Subgroup ψ.range) : Set ψ.range)).map
        ψ.range.subtype =
      ψ.range ⊓ Subgroup.centralizer ((N2KComplementary.blockM.map ψ : Subgroup G) : Set G) := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hh
      refine Subgroup.mem_inf.mpr ⟨h.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨m, hm, rfl⟩
      simpa using congrArg Subtype.val (hh (ψ.rangeRestrict m) ⟨m, hm, rfl⟩)
    · intro hg'
      obtain ⟨hg, hgc⟩ := Subgroup.mem_inf.mp hg'
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at hgc
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ ⟨m, hm, rfl⟩
      exact Subtype.ext (by simpa using hgc (ψ m) ⟨m, hm, rfl⟩)
  rw [Subgroup.map_commutator, hC, Subgroup.map_map, hcomp] at key
  exact key.symm

theorem ggSL6Chart_mem_complement_of_mem_centralizer {G : Type} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) {u : G} (hu : u ∈ ψ.range) (hu5 : u ^ 5 = 1)
    (huC : u ∈ Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ : Subgroup G) : Set G)) :
    u ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ := by
  have hM : (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range = N2KComplementary.blockM :=
    ggBlockSL_range_eq_blockSpecialLinear _ _ (by decide)
  have hM' : (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range = N2KComplementary.blockM' :=
    ggBlockSL_range_eq_blockSpecialLinear _ _ (by decide)
  rw [hM] at huC
  rw [hM']
  exact N2KComplementary.mem_map_blockM'_of_mem_centralizer_map_blockM ψ hψ hu hu5 huC


theorem ggF4N2K_chart_blockSL_torus {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ ψ₁ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G,
      ψ₁.ker ≤ Subgroup.center _ ∧ ψ₁.range = K ∧
      (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J ∧
      ∃ rho : Bs →* Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2),
        rho.range = N2KCoordinate.coordinateTorus ∧ rho.ker = (Subgroup.zpowers y).subgroupOf Bs ∧
        (∀ hx : x ∈ Bs, rho ⟨x, hx⟩ ∈ N2KCoordinate.coordT45) ∧ (∀ b : Bs, rho b ^ 5 = 1) ∧
        (∀ (b : Bs) (k : G), k ∈ K → ψ₁ (rho b) * k * (ψ₁ (rho b))⁻¹ = b * k * b⁻¹) ∧
        Nat.card rho.range = 5 ^ 3 ∧ (ψ₁.comp rho).range = Bs ⊓ K := by
  obtain ⟨ψ, rho, hsurj, hker, -, hPoint, hPow, hRhoKer, hCard, hRangeK, -, hTorus, hT45, hJ, -⟩ :=
    ggF4N2K_originalLiteralChart_of_original_data hR hNbr hL hK
  refine ⟨K.subtype.comp ψ, fun z hz => hker (Subtype.ext hz), ?_, ?_, rho, hTorus, hRhoKer,
    fun _ => hT45, hPow, fun b k hk => congrArg Subtype.val (hPoint b ⟨k, hk⟩), hCard, hRangeK⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · rw [MonoidHom.range_comp, ← ggBlockFour_eq_blockSL, hJ]

theorem ggF4N2K_chart_blockSL {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ ψ₁ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G,
      ψ₁.ker ≤ Subgroup.center _ ∧ ψ₁.range = K ∧
      (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J := by
  obtain ⟨ψ₁, h₁, hK₁, hJ₁, -⟩ := ggF4N2K_chart_blockSL_torus hR hNbr hL hK
  exact ⟨ψ₁, h₁, hK₁, hJ₁⟩

theorem ggF4N2L_swap_normalizes {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) {g : G} (hgL : g ∈ L)
    (hinvL : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hxg : g * x * g⁻¹ = x) :
    ∃ a : L, (a : G) ∈ D ∧ orderOf a = 5 ∧ D = Subgroup.zpowers x ⊔ Subgroup.zpowers (a : G) ∧
      J = (LargeEvenLayer (Subgroup.centralizer ({a} : Set L))).map L.subtype ∧
      g * (a : G) * g⁻¹ = (a : G)⁻¹ ∧
      g ∈ Subgroup.normalizer (D : Set G) ∧ g ∈ Subgroup.normalizer (J : Set G) := by
  classical
  obtain ⟨a, haD, ha5, hD, -, hJ⟩ := ggF4N2J_plane_basis hR hL
  have hDBs : D ≤ Bs := hR.1.2.2.1.1.trans hR.1.2.1.1
  have hag : g * (a : G) * g⁻¹ = (a : G)⁻¹ := hinvL _ ⟨hDBs haD, a.2⟩
  have hmapD : D.map (MulAut.conj g).toMonoidHom = D := by
    rw [hD, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxg, hag, Subgroup.zpowers_inv]
  set gL : L := ⟨g, hgL⟩ with hgLdef
  have hagL : gL * a * gL⁻¹ = a⁻¹ := Subtype.ext (by simpa using hag)
  have hA : gL * a⁻¹ * gL⁻¹ = a := by
    calc gL * a⁻¹ * gL⁻¹ = (gL * a * gL⁻¹)⁻¹ := by group
      _ = a := by rw [hagL, inv_inv]
  have hA' : gL⁻¹ * a⁻¹ * gL = a := by
    have h1 : gL⁻¹ * a * gL = a⁻¹ := by
      calc gL⁻¹ * a * gL = gL⁻¹ * (gL * a⁻¹ * gL⁻¹) * gL := by rw [hA]
        _ = a⁻¹ := by group
    calc gL⁻¹ * a⁻¹ * gL = (gL⁻¹ * a * gL)⁻¹ := by group
      _ = a := by rw [h1, inv_inv]
  have hcinv : ∀ w : L, w * a = a * w → w * a⁻¹ = a⁻¹ * w := fun w hw => by
    calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
      _ = a⁻¹ * (w * a) * a⁻¹ := by rw [hw]
      _ = a⁻¹ * w := by group
  have hmapC : (Subgroup.centralizer ({a} : Set L)).map (MulAut.conj gL).toMonoidHom =
      Subgroup.centralizer ({a} : Set L) := by
    ext z
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      calc gL * w * gL⁻¹ * a = gL * w * gL⁻¹ * (gL * a⁻¹ * gL⁻¹) := by rw [hA]
        _ = gL * (w * a⁻¹) * gL⁻¹ := by group
        _ = gL * (a⁻¹ * w) * gL⁻¹ := by rw [hcinv w hw]
        _ = (gL * a⁻¹ * gL⁻¹) * (gL * w * gL⁻¹) := by group
        _ = a * (gL * w * gL⁻¹) := by rw [hA]
    · intro hz
      refine ⟨gL⁻¹ * z * gL, ?_, by group⟩
      calc gL⁻¹ * z * gL * a = gL⁻¹ * z * gL * (gL⁻¹ * a⁻¹ * gL) := by rw [hA']
        _ = gL⁻¹ * (z * a⁻¹) * gL := by group
        _ = gL⁻¹ * (a⁻¹ * z) * gL := by rw [hcinv z hz]
        _ = (gL⁻¹ * a⁻¹ * gL) * (gL⁻¹ * z * gL) := by group
        _ = a * (gL⁻¹ * z * gL) := by rw [hA']
  have hmapE : (LargeEvenLayer (Subgroup.centralizer ({a} : Set L))).map (MulAut.conj gL).toMonoidHom =
      LargeEvenLayer (Subgroup.centralizer ({a} : Set L)) := by
    rw [shapeConj_largeEvenLayer_map_conj, hmapC]
  have hmapJ : J.map (MulAut.conj g).toMonoidHom = J := by
    have hcomm : (MulAut.conj g).toMonoidHom.comp L.subtype =
        L.subtype.comp (MulAut.conj gL).toMonoidHom := by
      ext z
      simp [hgLdef]
    rw [hJ, Subgroup.map_map, hcomm, ← Subgroup.map_map, hmapE]
  have hnorm : ∀ H : Subgroup G, H.map (MulAut.conj g).toMonoidHom = H →
      g ∈ Subgroup.normalizer (H : Set G) := by
    intro H hH
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hH]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← hH] at hh
      obtain ⟨h', hh', he⟩ := hh
      have : h' = h := by
        simpa using he
      rw [← this]
      exact hh'
  exact ⟨a, haD, ha5, hD, hJ, hag, hnorm D hmapD, hnorm J hmapJ⟩

theorem ggF4N2L_swap_sq_centralizes {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) {g : G} (hgL : g ∈ L)
    (hinvL : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hxg : g * x * g⁻¹ = x) :
    D ≤ Subgroup.centralizer ({g ^ 2} : Set G) := by
  obtain ⟨a, -, -, hD, -, hag, -, -⟩ := ggF4N2L_swap_normalizes hR hL hgL hinvL hxg
  have hsq : ∀ u : G, (g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹) →
      u ∈ Subgroup.centralizer ({g ^ 2} : Set G) := by
    intro u hu
    have h2 : (MulAut.conj (g ^ 2)) u = u := by
      rw [map_pow, pow_two, MulAut.mul_apply]
      simp only [MulAut.conj_apply]
      rcases hu with h | h
      · rw [h, h]
      · rw [h, show g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ by group, h, inv_inv]
    rw [MulAut.conj_apply] at h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * g ^ 2 = g ^ 2 * u * (g ^ 2)⁻¹ * g ^ 2 := by rw [h2]
      _ = g ^ 2 * u := inv_mul_cancel_right _ _
  rw [hD]
  exact sup_le (Subgroup.zpowers_le.mpr (hsq x (Or.inl hxg)))
    (Subgroup.zpowers_le.mpr (hsq _ (Or.inr hag)))

theorem ggF4N2L_exists_swap {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) :
    ∃ a : L, (a : G) ∈ D ∧ orderOf a = 5 ∧ D = Subgroup.zpowers x ⊔ Subgroup.zpowers (a : G) ∧
      J = (LargeEvenLayer (Subgroup.centralizer ({a} : Set L))).map L.subtype ∧
      ∃ g ∈ L, g ∈ Subgroup.normalizer (Bs : Set G) ∧ (∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) ∧
        g * x * g⁻¹ = x ∧ g * (a : G) * g⁻¹ = (a : G)⁻¹ ∧
        g ∈ Subgroup.normalizer (D : Set G) ∧ g ∈ Subgroup.normalizer (J : Set G) := by
  classical
  obtain ⟨τ, -, hτR, -, χ, -, κ, hx, hτ, -, hFull⟩ := ggF4N2Bstar_whole_coordinates hR hL
  have hinv : SpCoord.IsSignedPerm (p := 5) (k := 3)
      ⇑(MulEquiv.inv (Fin 3 → Multiplicative (ZMod 5))) :=
    ⟨1, fun _ => -1, fun _ => Or.inr rfl, fun f i => by simp⟩
  obtain ⟨u, hu⟩ := ggSpSigned_isSignedPerm_mem_range (p := 5) (k := 3) (by decide) hinv
  have hw : ggF4N2Bstar_signedAction κ u ∈ ggAutomizer L Bs := by
    rw [← hFull]
    exact ⟨u, rfl⟩
  obtain ⟨g, hgL, hgN, hg⟩ := mem_ggAutomizer_iff.mp hw
  have hact : ∀ m f, ggF4N2Bstar_signedAction κ u (κ (m, f)) = κ (m, f⁻¹) := by
    intro m f
    simp [ggF4N2Bstar_signedAction, hu]
  have hinvL : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹ := by
    intro b hb
    have hbL : (⟨b, hb.2⟩ : L) ∈ τ.range := by
      rw [hτR]
      exact Subgroup.mem_subgroupOf.mpr hb
    obtain ⟨f, hf⟩ := hbL
    have hb' : κ (1, f) = ⟨b, hb.1⟩ := Subtype.ext (by rw [hτ, hf])
    have h1 := hg (κ (1, f))
    rw [hact] at h1
    have h2 : κ (1, f⁻¹) = (κ (1, f))⁻¹ := by
      rw [← map_inv]
      simp
    rw [h2, hb'] at h1
    simpa using h1.symm
  have hxg : g * x * g⁻¹ = x := by
    have h1 := hg (κ (Multiplicative.ofAdd 1, 1))
    rw [hact, inv_one, hx] at h1
    exact h1.symm
  obtain ⟨a, haD, ha5, hD, hJ, hag, hgD, hgJ⟩ := ggF4N2L_swap_normalizes hR hL hgL hinvL hxg
  exact ⟨a, haD, ha5, hD, hJ, g, hgL, hgN, hinvL, hxg, hag, hgD, hgJ⟩

theorem ggF4N2L_swap_field_free {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (eJ : J ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2))
    {g : G} (hgL : g ∈ L)
    (hinvL : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹)
    (hxg : g * x * g⁻¹ = x) :
    ∃ (C : Matrix.GeneralLinearGroup (Fin 4) (GaloisField 2 2)) (δ : ℕ), δ ≤ 1 ∧
      ∀ z : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2),
        g * (eJ.symm z : G) * g⁻¹ = (eJ.symm (N2KFieldCoefficient.blockGamma C δ z) : G) := by
  obtain ⟨a, -, -, -, hJ, -, -, hgJ⟩ := ggF4N2L_swap_normalizes hR hL hgL hinvL hxg
  obtain ⟨w, hw, h0, h1, hinv⟩ := ggF4N2_exists_torus_trace_witness hR hNbr hL hK eJ
  have hJL : J ≤ L := by
    rw [hJ]
    exact Subgroup.map_subtype_le _
  have htw : g * (eJ.symm w : G) * g⁻¹ = (eJ.symm w : G)⁻¹ :=
    hinvL _ ⟨hw.1, hJL (eJ.symm w).2⟩
  exact exists_blockGamma_on_subgroup_of_inv_trace eJ hgJ htw h0 h1 hinv

theorem ggF4N2_secondChart_of_chart {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) {K : Subgroup G}
    {ψ₁ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G}
    (h₁ : ψ₁.ker ≤ Subgroup.center _) (hK₁ : ψ₁.range = K)
    (hJ₁ : (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J)
    {g : G} (hgL : g ∈ L) (hinv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hxg : g * x * g⁻¹ = x) :
    ∃ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G,
      ψ₂.ker ≤ Subgroup.center _ ∧ ψ₂.range = K.map (MulAut.conj g).toMonoidHom ∧
      ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
        ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) := by
  obtain ⟨-, -, -, -, -, -, -, hgJ⟩ := ggF4N2L_swap_normalizes hR hL hgL hinv hxg
  obtain ⟨ψ₂, h₂, hK₂, hblock⟩ := ggSLChart_exists_align (F := GaloisField 2 2) (m := 6) (k := 4)
    (by norm_num) (by norm_num) ψ₁ h₁ (g := g) (by rw [hJ₁]; exact hgJ)
  refine ⟨ψ₂, h₂, ?_, hblock⟩
  rw [hK₂, hK₁]

theorem ggF4N2_exists_secondChart {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G, ∃ g ∈ L,
      ψ₁.ker ≤ Subgroup.center _ ∧ ψ₁.range = K ∧
      (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J ∧
      g ∈ Subgroup.normalizer (Bs : Set G) ∧ (∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) ∧ g * x * g⁻¹ = x ∧
      ψ₂.ker ≤ Subgroup.center _ ∧ ψ₂.range = K.map (MulAut.conj g).toMonoidHom ∧
      ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
        ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) := by
  obtain ⟨ψ₁, h₁, hK₁, hJ₁⟩ := ggF4N2K_chart_blockSL hR hNbr hL hK
  obtain ⟨-, -, -, -, -, g, hgL, hgN, hinv, hxg, -, -, -⟩ := ggF4N2L_exists_swap hR hL
  obtain ⟨ψ₂, h₂, hK₂, hblock⟩ := ggF4N2_secondChart_of_chart hR hL h₁ hK₁ hJ₁ hgL hinv hxg
  exact ⟨ψ₁, ψ₂, g, hgL, h₁, hK₁, hJ₁, hgN, hinv, hxg, h₂, hK₂, hblock⟩

theorem ggF4N2_sStar_map_conj
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) :
    LargeEvenSStar 5 B (g * y * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) := by
  have h := shapeConj_largeEvenSStar_map_conj (p := 5) (ggF4N2_sStar_K hR hNbr hL hK) g
  have hBmap : B.map (MulAut.conj g).toMonoidHom = B := by
    rw [ggF4N2_B_eq_Bs hR hL]
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  simpa only [hBmap] using h

theorem ggF4N2_mixed_E6_of_charts {G : Type} [Group G] [Finite G] {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hNbr : GGNbr 5 B x D J y K)
    {ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G} {g : G} (hgL : g ∈ L)
    (h₁ : ψ₁.ker ≤ Subgroup.center _) (hK₁ : ψ₁.range = K)
    (h₂ : ψ₂.ker ≤ Subgroup.center _) (hK₂ : ψ₂.range = K.map (MulAut.conj g).toMonoidHom)
    (hblock : ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
      ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))) :
    ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂ ≤ ggG0 5 B x L D J ∧
      ((∀ a ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁,
          ∀ b ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂, a * b = b * a) →
        ggG0 5 B x L D J ≤ ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂ →
        GGCentralImage .E6 0 2 (ggG0 5 B x L D J)) := by
  have hKG : K ≤ ggG0 5 B x L D J := le_ggG0_of_ggNbr hNbr
  have hgG : g ∈ ggG0 5 B x L D J := le_ggG0_left 5 B x L D J hgL
  have hle : ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂ ≤ ggG0 5 B x L D J := by
    refine sup_le (hK₁ ▸ hKG) ?_
    refine (Subgroup.map_le_range ψ₂ _).trans ?_
    rw [hK₂]
    rintro _ ⟨k, hk, rfl⟩
    exact (ggG0 5 B x L D J).mul_mem ((ggG0 5 B x L D J).mul_mem hgG (hKG hk))
      ((ggG0 5 B x L D J).inv_mem hgG)
  refine ⟨hle, fun hM hge => ?_⟩
  have hc := ggCentralImage_E6_of_twoSL6Charts (le_refl 2) ψ₁ ψ₂ h₁ h₂ hblock.symm hM
  rwa [le_antisymm hle hge] at hc

theorem ggF4N2_mixed_centralImage_of_charts {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G, ∃ g ∈ L,
      ψ₁.ker ≤ Subgroup.center _ ∧ ψ₁.range = K ∧
      (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J ∧
      g ∈ Subgroup.normalizer (Bs : Set G) ∧ (∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) ∧ g * x * g⁻¹ = x ∧
      ψ₂.ker ≤ Subgroup.center _ ∧ ψ₂.range = K.map (MulAut.conj g).toMonoidHom ∧
      ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
        ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) ∧
      ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂ ≤ ggG0 5 B x L D J ∧
      ((∀ a ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁,
          ∀ b ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂, a * b = b * a) →
        ggG0 5 B x L D J ≤ ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂ →
        GGCentralImage .E6 0 2 (ggG0 5 B x L D J)) := by
  obtain ⟨ψ₁, ψ₂, g, hgL, h₁, hK₁, hJ₁, hgN, hinv, hxg, h₂, hK₂, hblock⟩ :=
    ggF4N2_exists_secondChart hR hNbr hL hK
  obtain ⟨hle, hfin⟩ := ggF4N2_mixed_E6_of_charts hNbr hgL h₁ hK₁ h₂ hK₂ hblock
  exact ⟨ψ₁, ψ₂, g, hgL, h₁, hK₁, hJ₁, hgN, hinv, hxg, h₂, hK₂, hblock, hle, hfin⟩

end CFSG.StandardType

end
