module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105AutOddU4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesMap
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU4Line
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Models.PGL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.AutOdd

open Matrix Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec21.U4Lines (mapL mapL_le card_mapL mapL_inf_centralizer
  mapL_perfectResidual_inf mapL_conj nonempty_projSU_mulEquiv_SU card_galoisField_two_mul
  card_rootsOfUnity_three unitaryInvolution_rootsOfUnity perfectResidual_conj perfectResidual_short
  nonempty_shortSL_mulEquiv_galois torusD coe_torusD torusD_apply shortSL)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Comb_four d8Vec_mem_SU diagU d8Vec)

theorem mapL_top {G G' : Type} [Group G] [Group G'] {Y : Subgroup G'}
    (E : (⊤ : Subgroup G) ≃* Y) : mapL E ⊤ = Y := by
  rw [mapL]
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact (E y).2
  · intro hx
    exact ⟨E.symm ⟨x, hx⟩, Subgroup.mem_top _,
      by simp [CFSG.RankThree.PartTwo.Sec21.U4Lines.embedOf]⟩

theorem mapL_congr_apply_eq_self {X : Type} [Group X] {F : Type} [Field F]
    [Finite F] [CharP F 2] {n : ℕ} (E : X ≃* ↥(SU (unitaryInvolution F 2 n) 4))
    (α : MulAut X) {K : Subgroup X} (hK : ∀ x ∈ K, α x = x) :
    ∀ y : ↥(SU (unitaryInvolution F 2 n) 4),
      (y : GL (Fin 4) F) ∈ mapL (Subgroup.topEquiv.trans E) K → MulAut.congr E α y = y := by
  rintro y ⟨z, hz, hzy⟩
  have hzK : (z : X) ∈ K := Subgroup.mem_subgroupOf.mp hz
  have hy : E (z : X) = y := Subtype.ext hzy
  change E (α (E.symm y)) = y
  rw [← hy, MulEquiv.symm_apply_apply]
  exact congrArg E (hK (z : X) hzK)

theorem notationB8103_mapL_top {X : Type} [Group X] [Finite X] {F : Type} [Field F]
    [Finite F] [CharP F 2] {n : ℕ} (E : X ≃* ↥(SU (unitaryInvolution F 2 n) 4))
    {B₀ : Subgroup X} (hB : F08.NotationB8103 ⊤ ⊤ n B₀) :
    F08.NotationB8103 (SU (unitaryInvolution F 2 n) 4)
        (SU (unitaryInvolution F 2 n) 4) n
        (mapL (Subgroup.topEquiv.trans E) B₀) ∧
      Nat.card (mapL (Subgroup.topEquiv.trans E) B₀) = 3 := by
  have hBle : B₀ ≤ ⊤ := le_top
  have htop : mapL (Subgroup.topEquiv.trans E) (⊤ : Subgroup X) =
      SU (unitaryInvolution F 2 n) 4 := mapL_top _
  refine ⟨?_, ?_⟩
  · have h :=
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.notationB8103_mapL_iff
        (E := Subgroup.topEquiv.trans E) (P := ⊤) (B := B₀) hBle (n := n)).mpr hB
    rwa [htop] at h
  · rw [card_mapL (Subgroup.topEquiv.trans E) hBle, hB.1]

theorem kOf8103_mapL_top {X : Type} [Group X] [Finite X] {F : Type} [Field F]
    [Finite F] [CharP F 2] {n : ℕ} (E : X ≃* ↥(SU (unitaryInvolution F 2 n) 4))
    (B₀ : Subgroup X) :
    F08.KOf8103 (SU (unitaryInvolution F 2 n) 4)
        (mapL (Subgroup.topEquiv.trans E) B₀) =
      mapL (Subgroup.topEquiv.trans E) (F08.KOf8103 ⊤ B₀) := by
  change inSubgroup perfectResidual (SU (unitaryInvolution F 2 n) 4 ⊓ Subgroup.centralizer
      (mapL (Subgroup.topEquiv.trans E) B₀ : Set (GL (Fin 4) F))) =
    mapL (Subgroup.topEquiv.trans E)
      (inSubgroup perfectResidual (⊤ ⊓ Subgroup.centralizer (B₀ : Set X)))
  exact (mapL_perfectResidual_inf _ le_top).symm

theorem kOf8103_zpowers_torusD_eq_shortSL {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn0 : 0 < n) (hn : Even n) (hF : Nat.card F = (2 ^ n) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) :
    F08.KOf8103 (SU (unitaryInvolution F 2 n) 4)
        (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) =
      shortSL (unitaryInvolution F 2 n) := by
  have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hn; omega
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois (unitaryInvolution F 2 n) hn0 hF
  have hperfS : ⁅shortSL (unitaryInvolution F 2 n), shortSL (unitaryInvolution F 2 n)⁆ =
      shortSL (unitaryInvolution F 2 n) :=
    Subgroup.isPerfect_iff.mp
      (CFSG.RankThree.PartTwo.Sec21.isPerfect_of_mulEquiv_projSL (by omega) eS)
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    have hcube : a = a ^ 3 := by
      calc a = a * (a * a) := by rw [h2, mul_one]
        _ = a ^ 3 := by ring
    exact hcube.trans ha3
  have hσσ : ∀ c, unitaryInvolution F 2 n (unitaryInvolution F 2 n c) = c :=
    unitaryInvolution_involutive hF
  have ht₃ : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  change inSubgroup perfectResidual (SU (unitaryInvolution F 2 n) 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
    shortSL (unitaryInvolution F 2 n)
  exact perfectResidual_short (unitaryInvolution F 2 n) hσσ ht₃ hainv hperfS

theorem kOf8103_zpowers_torusD_map_conj {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn0 : 0 < n) (hn : Even n) (hF : Nat.card F = (2 ^ n) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {g : GL (Fin 4) F}
    (hg : g ∈ SU (unitaryInvolution F 2 n) 4) :
    F08.KOf8103 (SU (unitaryInvolution F 2 n) 4)
        ((Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
          (MulAut.conj g).toMonoidHom) =
      (shortSL (unitaryInvolution F 2 n)).map (MulAut.conj g).toMonoidHom := by
  have h := perfectResidual_conj (Y := SU (unitaryInvolution F 2 n) 4) hg
    (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)))
  have hKshort : inSubgroup perfectResidual (SU (unitaryInvolution F 2 n) 4 ⊓
      Subgroup.centralizer (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) :
        Set (GL (Fin 4) F))) = shortSL (unitaryInvolution F 2 n) :=
    kOf8103_zpowers_torusD_eq_shortSL hn0 hn hF hω
  change inSubgroup perfectResidual (SU (unitaryInvolution F 2 n) 4 ⊓
      Subgroup.centralizer ((Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
        (MulAut.conj g).toMonoidHom : Set (GL (Fin 4) F))) =
    (shortSL (unitaryInvolution F 2 n)).map (MulAut.conj g).toMonoidHom
  rw [← hKshort]
  exact h

theorem exists_pow_eq_one_of_mulEquiv_congr {X Y : Type} [Group X] [Group Y] (E : X ≃* Y)
    (α : MulAut X) (hα : ∃ k : ℕ, α ^ 2 ^ k = 1) :
    ∃ k : ℕ, MulAut.congr E α ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hα
  refine ⟨k, ?_⟩
  have h := map_pow (MulAut.congr E) α (2 ^ k)
  rw [hk, map_one] at h
  exact h.symm

theorem eq_one_of_fix_map_conj {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : Even n) (hF : Nat.card F = (2 ^ n) ^ 2) {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    (α : MulAut ↥(SU (unitaryInvolution F 2 n) 4))
    (hα : ∃ k : ℕ, α ^ 2 ^ k = 1) {g : GL (Fin 4) F}
    (hg : g ∈ SU (unitaryInvolution F 2 n) 4)
    (hK : ∀ x : ↥(SU (unitaryInvolution F 2 n) 4),
      (x : GL (Fin 4) F) ∈
        (shortSL (unitaryInvolution F 2 n)).map (MulAut.conj g).toMonoidHom → α x = x)
    (ht : ∀ x : ↥(SU (unitaryInvolution F 2 n) 4),
      (x : GL (Fin 4) F) ∈
        (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
          (MulAut.conj g).toMonoidHom → α x = x) :
    α = 1 := by
  let g' : ↥(SU (unitaryInvolution F 2 n) 4) := ⟨g, hg⟩
  let c : MulAut ↥(SU (unitaryInvolution F 2 n) 4) := MulAut.conj g'
  let α'' : MulAut ↥(SU (unitaryInvolution F 2 n) 4) := c⁻¹ * α * c
  have hα''eq : α'' = MulAut.conj c⁻¹ α := by
    show c⁻¹ * α * c = MulAut.conj c⁻¹ α
    rw [MulAut.conj_apply, inv_inv]
  have hα''pow : ∃ k : ℕ, α'' ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hα
    refine ⟨k, ?_⟩
    rw [hα''eq, ← map_pow (MulAut.conj c⁻¹) α (2 ^ k), hk, map_one]
  have hfixK : ∀ x : ↥(SU (unitaryInvolution F 2 n) 4),
      (x : GL (Fin 4) F) ∈ shortSL (unitaryInvolution F 2 n) → α'' x = x := by
    intro x hx
    have hcx : (c x : GL (Fin 4) F) ∈
        (shortSL (unitaryInvolution F 2 n)).map (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨(x : GL (Fin 4) F), hx, ?_⟩
      rfl
    have hfixc : α (c x) = c x := hK (c x) hcx
    change c⁻¹ (α (c x)) = x
    rw [hfixc]
    exact MulEquiv.symm_apply_apply c x
  have hfixt : ∀ x : ↥(SU (unitaryInvolution F 2 n) 4),
      (x : GL (Fin 4) F) = torusD ((ω, ω) : D8Mod 3 F) → α'' x = x := by
    intro x hx
    have hcx : (c x : GL (Fin 4) F) ∈
        (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
          (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_map.mpr
        ⟨torusD ((ω, ω) : D8Mod 3 F), Subgroup.mem_zpowers _, ?_⟩
      rw [← hx]
      rfl
    have hfixc : α (c x) = c x := ht (c x) hcx
    change c⁻¹ (α (c x)) = x
    rw [hfixc]
    exact MulEquiv.symm_apply_apply c x
  have hα''1 : α'' = 1 := eq_one_of_fix_shortSL_torusD hn hF hω α'' hα''pow hfixK hfixt
  have h : c * α'' * c⁻¹ = α := by
    show c * (c⁻¹ * α * c) * c⁻¹ = α
    group
  rw [hα''1] at h
  simpa using h.symm

theorem not_notationB8103_zpowers_torusD_one_map_conj {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn0 : 0 < n) (hn : Even n) (hF : Nat.card F = (2 ^ n) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {g : GL (Fin 4) F}
    (hg : g ∈ SU (unitaryInvolution F 2 n) 4) :
    ¬ F08.NotationB8103 (SU (unitaryInvolution F 2 n) 4)
      (SU (unitaryInvolution F 2 n) 4) n
      ((Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))).map
        (MulAut.conj g).toMonoidHom) := by
  have ht₁SU : (torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) ∈
      SU (unitaryInvolution F 2 n) 4 := by
    rw [show (torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) =
      diagU (d8Vec 4 ((ω, 1) : D8Mod 3 F)) from torusD_apply _]
    exact d8Vec_mem_SU (Or.inl rfl) d8Comb_four _
      (fun u => unitaryInvolution_rootsOfUnity hn u) _
  have hzp : Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) ≤
      SU (unitaryInvolution F 2 n) 4 := Subgroup.zpowers_le.mpr ht₁SU
  have hmap : mapL (MulAut.conj (⟨g, hg⟩ : ↥(SU (unitaryInvolution F 2 n) 4)))
      (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))) =
      (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))).map
        (MulAut.conj g).toMonoidHom := mapL_conj _ hzp
  have hL : mapL (MulAut.conj (⟨g, hg⟩ : ↥(SU (unitaryInvolution F 2 n) 4)))
      (SU (unitaryInvolution F 2 n) 4) = SU (unitaryInvolution F 2 n) 4 := by
    rw [mapL_conj _ (le_refl _)]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  intro hB'
  have h :=
    (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.notationB8103_mapL_iff
      (E := MulAut.conj (⟨g, hg⟩ : ↥(SU (unitaryInvolution F 2 n) 4)))
      (P := SU (unitaryInvolution F 2 n) 4)
      (B := Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))) hzp (n := n))
  rw [hL, hmap] at h
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.u4_not_notationB_line
    hn0 hn hF hω (h.mp hB')

theorem eq_one_of_isU4_of_fix_of_line_three {X : Type} [Group X] [Finite X] {F : Type}
    [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn0 : 0 < n) (hn : Even n)
    (hF : Nat.card F = (2 ^ n) ^ 2) {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    (E : X ≃* ↥(SU (unitaryInvolution F 2 n) 4)) {B₀ : Subgroup X} (α : MulAut X)
    (hα : ∃ k : ℕ, α ^ 2 ^ k = 1) (hK : ∀ x ∈ F08.KOf8103 ⊤ B₀, α x = x)
    (hB₀ : ∀ x ∈ B₀, α x = x) {g : GL (Fin 4) F}
    (hg : g ∈ SU (unitaryInvolution F 2 n) 4)
    (hℓ : mapL (Subgroup.topEquiv.trans E) B₀ =
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
        (MulAut.conj g).toMonoidHom) :
    α = 1 := by
  let E' : (⊤ : Subgroup X) ≃* SU (unitaryInvolution F 2 n) 4 :=
    Subgroup.topEquiv.trans E
  let α' : MulAut ↥(SU (unitaryInvolution F 2 n) 4) := MulAut.congr E α
  have hα'pow : ∃ k : ℕ, α' ^ 2 ^ k = 1 :=
    exists_pow_eq_one_of_mulEquiv_congr E α hα
  have hKmap : F08.KOf8103 (SU (unitaryInvolution F 2 n) 4) (mapL E' B₀) =
      mapL E' (F08.KOf8103 ⊤ B₀) := kOf8103_mapL_top E B₀
  have hSg : F08.KOf8103 (SU (unitaryInvolution F 2 n) 4)
      ((Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
        (MulAut.conj g).toMonoidHom) =
      (shortSL (unitaryInvolution F 2 n)).map (MulAut.conj g).toMonoidHom :=
    kOf8103_zpowers_torusD_map_conj hn0 hn hF hω hg
  have hα'fixK : ∀ y : ↥(SU (unitaryInvolution F 2 n) 4),
      (y : GL (Fin 4) F) ∈
        (shortSL (unitaryInvolution F 2 n)).map (MulAut.conj g).toMonoidHom → α' y = y := by
    intro y hy
    have hy' : (y : GL (Fin 4) F) ∈
        F08.KOf8103 (SU (unitaryInvolution F 2 n) 4) (mapL E' B₀) := by
      rw [hℓ]
      exact hSg.symm ▸ hy
    exact mapL_congr_apply_eq_self E α hK y (hKmap ▸ hy')
  have hα'fixt : ∀ y : ↥(SU (unitaryInvolution F 2 n) 4),
      (y : GL (Fin 4) F) ∈
        (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
          (MulAut.conj g).toMonoidHom → α' y = y := by
    intro y hy
    exact mapL_congr_apply_eq_self E α hB₀ y (hℓ.symm ▸ hy)
  have hα'1 : α' = 1 := eq_one_of_fix_map_conj hn hF hω α' hα'pow hg hα'fixK hα'fixt
  exact (MulAut.congr E).injective (by
    have h : MulAut.congr E α = 1 := hα'1
    rw [h, map_one])

theorem eq_one_of_isU4_of_fix {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU4 X n)
    (hn : Even n) {B₀ : Subgroup X} (hB : F08.NotationB8103 ⊤ ⊤ n B₀) (α : MulAut X)
    (hα : ∃ k : ℕ, α ^ 2 ^ k = 1) (hK : ∀ x ∈ F08.KOf8103 ⊤ B₀, α x = x)
    (hB₀ : ∀ x ∈ B₀, α x = x) : α = 1 := by
  have hn0 : 0 < n := (CFSG.Blueprint.LieModel.admissible hX).2.1
  let F := GaloisField 2 (2 * n)
  let σ : F ≃+* F := unitaryInvolution F 2 n
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      (CFSG.Blueprint.LieModel.admissible hX) (MulEquiv.refl _))
  obtain ⟨e₀⟩ := nonempty_projSU_mulEquiv_SU n hn0
  have hF : Nat.card F = (2 ^ n) ^ 2 := card_galoisField_two_mul n hn0
  have hμ : Nat.card (rootsOfUnity 3 F) = 3 := card_rootsOfUnity_three hn hF
  have hnt : Nontrivial (rootsOfUnity 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := @exists_ne (rootsOfUnity 3 F) hnt 1
  let E : X ≃* ↥(SU σ 4) := e.trans e₀
  let E' : (⊤ : Subgroup X) ≃* SU σ 4 := Subgroup.topEquiv.trans E
  let ℓ : Subgroup (GL (Fin 4) F) := mapL E' B₀
  have hℓdata := notationB8103_mapL_top E hB
  have hℓB : F08.NotationB8103 (SU σ 4) (SU σ 4) n ℓ := hℓdata.1
  have hℓcard : Nat.card ℓ = 3 := hℓdata.2
  have hℓSU : ℓ ≤ SU σ 4 := mapL_le E' B₀
  obtain ⟨g, hg, hℓ₁ | hℓt⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.u4_conj_line
      hn hF hω hℓSU hℓcard
  · rw [hℓ₁] at hℓB
    exact (not_notationB8103_zpowers_torusD_one_map_conj hn0 hn hF hω hg hℓB).elim
  · exact eq_one_of_isU4_of_fix_of_line_three hn0 hn hF hω E α hα hK hB₀ hg hℓt

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.AutOdd

end
