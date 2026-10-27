module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4DiagPSU
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.ClassicalGroups.Unitary.Transitivity
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSUComm
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43
public import Certificates.Certificate7233Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.PartOne.KFU
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

variable {K : Type} [Field K] [Finite K]

theorem s16k_mem_statedSU_of_det_normalizer (hK : Nat.card K = 4)
    {g : GL (Fin 4) K}
    (hg : g ∈ Subgroup.normalizer (StatedSU 4 2 K : Set (GL (Fin 4) K)))
    (hdet : (g : Matrix (Fin 4) (Fin 4) K).det = 1) : g ∈ StatedSU 4 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI : CharP K 2 := charP_of_card_sq (p := 2) (f := 1) hcard2
  let σ : K ≃+* K := unitaryInvolution K 2 1
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hcard2
  have hσapply : ∀ x : K, σ x = x ^ 2 := fun x => by
    rw [show σ = unitaryInvolution K 2 1 from rfl, unitaryInvolution_apply, pow_one]
  have hunit := s16k_normalizer_statedSU_unitary hK (by norm_num : 3 ≤ 4) hg
  have hunit' : (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    have hmap : (fun x : K => x ^ 2) = ⇑σ := funext fun x => (hσapply x).symm
    simpa [hmap] using hunit
  have hSUeq : SUid σ 4 = StatedSU 4 2 K := by
    change SUid (frobeniusEquiv K 2) 4 = StatedSU 4 2 K
    simpa using SUid_eq_statedSU (p := 2) (f := 1) hcard2 4
  rw [← hSUeq]
  refine (mem_SUid_iff σ).mpr ⟨hdet, fun x y => ?_⟩
  rw [herm_mulVec]
  have hconj : conjTr σ ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ := rfl
  rw [hconj, hunit', Matrix.one_mulVec]

theorem s16k_not_isCyclic_of_card_pow {G : Type*} [Group G] {B : Subgroup G}
    [Finite B] {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hcard : Nat.card B = p ^ k)
    (hexp : ∀ x : B, x ^ p = 1) : ¬ IsCyclic B := by
  intro hcyc
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
  have hxp : x ^ p = 1 := hexp x
  have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rw [hx, hcard] at hdvd
  have hle : p ^ k ≤ p := Nat.le_of_dvd hp.pos hdvd
  have hlt : p < p ^ k := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ k := Nat.pow_lt_pow_right hp.one_lt hk
  exact (not_lt_of_ge hle) hlt

private theorem s16k_herm_single {K : Type} [Field K] {σ : K ≃+* K} (i j : Fin 4) (a b : K) :
    herm σ (Pi.single i a) (Pi.single j b) = if i = j then σ a * b else 0 := by
  classical
  rw [herm_def]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k = i
    · subst hki
      simp [Pi.single_apply, h]
    · simp [Pi.single_eq_of_ne hki]

private theorem s16k_conj_fix {K : Type} [Field K] {A : GL (Fin 4) K}
    {B : Subgroup (GL (Fin 4) K)} {v : Fin 4 → K}
    (hB : ∀ b ∈ B, (b : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v) :
    ∀ b ∈ B.map (MulAut.conj A⁻¹).toMonoidHom,
      (b : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) =
      ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
  have hb : ((MulAut.conj A⁻¹) x : GL (Fin 4) K) = A⁻¹ * x * A := by
    rw [MulAut.conj_apply, inv_inv]
  change ((MulAut.conj A⁻¹) x : GL (Fin 4) K) *ᵥ
    (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) =
    ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v
  rw [hb]
  rw [show (((A⁻¹ * x * A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v)) =
      ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        ((x : Matrix (Fin 4) (Fin 4) K) *ᵥ
          (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
            (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v))) by
      simp only [Units.val_mul, mul_assoc, Matrix.mulVec_mulVec]]
  rw [show (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v)) = v by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec],
    hB x hx]

theorem s16k_exists_torus_pair [Fact (Nat.Prime 2)] [CharP K 2] (hK : Nat.card K = 4)
    {F : Subgroup (GL (Fin 4) K)}
    (hFN : F ≤ Subgroup.normalizer (StatedSU 4 2 K : Set (GL (Fin 4) K)))
    (hF : IsElemAbelian 3 F) (hFcard : 81 ≤ Nat.card F) :
    ∃ (B₁ B₂ : Subgroup (GL (Fin 4) K)) (w₁ w₂ : Fin 4 → K),
      B₁ ≤ F ∧ B₂ ≤ F ∧ IsPGroup 3 B₁ ∧ IsPGroup 3 B₂ ∧
      Nat.card B₁ = 27 ∧ Nat.card B₂ = 9 ∧
      ¬ IsCyclic ↥B₁ ∧ ¬ IsCyclic ↥B₂ ∧
      w₁ ≠ 0 ∧ herm (unitaryInvolution K 2 1) w₁ w₁ = 1 ∧
      w₂ ≠ 0 ∧ herm (unitaryInvolution K 2 1) w₂ w₂ = 0 ∧
      (∀ b ∈ B₁, (b : Matrix (Fin 4) (Fin 4) K) *ᵥ w₁ = w₁) ∧
      (∀ b ∈ B₂, (b : Matrix (Fin 4) (Fin 4) K) *ᵥ w₂ = w₂) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI : CharP K 2 := charP_of_card_sq (p := 2) (f := 1) hcard2
  let σ : K ≃+* K := unitaryInvolution K 2 1
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hcard2
  have hσapply : ∀ x : K, σ x = x ^ 2 := fun x => by
    rw [show σ = unitaryInvolution K 2 1 from rfl, unitaryInvolution_apply, pow_one]
  let Γ : Subgroup (GL (Fin 4) K) := StatedSU 4 2 K
  let A0 : Subgroup (GL (Fin 4) K) := F ⊓ StatedSU 4 2 K
  have hA0el : IsElemAbelian 3 A0 := hF.mono inf_le_left
  have hA0subel : IsElemAbelian 3 (A0.subgroupOf Γ) := hA0el.subgroupOf Γ
  obtain ⟨hS, hdiag⟩ := exists_unitary_conj_diag_su (r := 2) (K := K) Nat.prime_two
    (by norm_num [hK]) (by norm_num : 2 % 3 = 2) (A0.subgroupOf Γ) hA0subel
  obtain ⟨ζ⟩ : Nonempty (CubeRoot K) :=
    CubeRoot.exists_of_dvd (K := K) (by norm_num [hK])
  let φ : ↥F →* Kˣ := (Matrix.GeneralLinearGroup.det).comp F.subtype
  let hconj : GL (Fin 4) K := (hS : GL (Fin 4) K)
  let F' : Subgroup (GL (Fin 4) K) := F.map (MulAut.conj hconj).toMonoidHom
  have hF'el : IsElemAbelian 3 F' := hF.map _
  have hF'comm : ∀ a ∈ F', ∀ b ∈ F', a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hF'el.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hrange_le : Nat.card φ.range ≤ 3 := by
    have h1 : Nat.card φ.range ≤ Nat.card Kˣ :=
      Nat.card_le_card_of_injective φ.range.subtype Subtype.val_injective
    rwa [Nat.card_units, hK] at h1
  have hdetker : φ.ker = A0.subgroupOf F := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxdet : ((x.1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
        have h := congrArg (fun u : Kˣ => (u : K)) hx
        simpa [φ] using congrArg (fun u : Kˣ => (u : K)) hx
      rw [Subgroup.mem_subgroupOf]
      exact ⟨x.2, s16k_mem_statedSU_of_det_normalizer hK (hFN x.2) hxdet⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker]
      apply Units.ext
      simpa [φ] using CFSG.Open.StatedAPI.det_of_mem_statedSU hx.2
  have hcardF_eq : Nat.card F = Nat.card A0 * Nat.card φ.range := by
    rw [← Subgroup.card_ker_mul_card_range φ, hdetker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hlower : 27 ≤ Nat.card A0 := by
    by_contra h
    have hle : Nat.card A0 ≤ 26 := by omega
    have h81 : 81 ≤ Nat.card A0 * Nat.card φ.range := by
      rw [← hcardF_eq]; exact hFcard
    have hle' : Nat.card A0 * Nat.card φ.range ≤ 26 * 3 :=
      Nat.mul_le_mul hle hrange_le
    omega
  have hmaple : A0.map (MulAut.conj hconj).toMonoidHom ≤ D₀ ζ := by
    rintro y ⟨x, hx, rfl⟩
    let xsub : A0.subgroupOf Γ := ⟨⟨x, hx.2⟩, hx⟩
    have hd : (((MulAut.conj hconj) x : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).IsDiag := by
      convert hdiag xsub xsub.2 using 2
      simp [xsub, hconj, Subgroup.coe_mul, Subgroup.coe_inv]
    refine mem_D₀_of_diag ζ hd ?_ ?_
    · change ((MulAut.conj hconj) x : GL (Fin 4) K) ^ 3 = 1
      rw [← map_pow, hF.2 x hx.1, map_one]
    · change (((MulAut.conj hconj) x : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).det = 1
      have hyΓ : (MulAut.conj hconj) x ∈ Γ := by
        change hS * x * hS⁻¹ ∈ Γ
        exact Γ.mul_mem (Γ.mul_mem hS.2 hx.2) (Γ.inv_mem hS.2)
      exact CFSG.Open.StatedAPI.det_of_mem_statedSU hyΓ
  have hcardmap : Nat.card (A0.map (MulAut.conj hconj).toMonoidHom) =
      Nat.card A0 :=
    Subgroup.card_map_of_injective (MulAut.conj hconj).injective
  have hupper : Nat.card A0 ≤ 27 := by
    calc Nat.card A0 = Nat.card (A0.map (MulAut.conj hconj).toMonoidHom) :=
          hcardmap.symm
      _ ≤ Nat.card (D₀ ζ) := by
          exact Nat.card_le_card_of_injective (Subgroup.inclusion hmaple)
            (Subgroup.inclusion_injective hmaple)
      _ = 27 := card_D₀ ζ
  have hcardFΓ : Nat.card A0 = 27 := le_antisymm hupper hlower
  have hcardF_le : Nat.card F ≤ 81 := by
    calc Nat.card F = Nat.card A0 * Nat.card φ.range := hcardF_eq
      _ = 27 * Nat.card φ.range := by rw [hcardFΓ]
      _ ≤ 27 * 3 := Nat.mul_le_mul_left _ hrange_le
      _ = 81 := by norm_num
  have hcardF : Nat.card F = 81 := le_antisymm hcardF_le hFcard
  have hD0map : A0.map (MulAut.conj hconj).toMonoidHom = D₀ ζ := by
    refine Subgroup.eq_of_le_of_card_ge hmaple ?_
    rw [hcardmap, hcardFΓ, card_D₀]
  have hD0leF' : D₀ ζ ≤ F' := by
    rw [← hD0map]
    exact Subgroup.map_mono inf_le_left
  have hF'diag : ∀ x ∈ F', ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag := by
    intro x hx
    let xF : ↥F' := ⟨x, hx⟩
    have hxmem : xF ∈ Subgroup.centralizer
        (((D₀ ζ).subgroupOf F' : Subgroup ↥F') : Set ↥F') := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact (hF'comm x hx y y.2).symm
    have hd := centralizer_D₀_comm_diag ζ (H := F') hD0leF' hxmem
    simpa using hd
  have hF'leRange : F' ≤ (diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K).range := by
    intro x hx
    obtain ⟨d, hd⟩ := exists_diagU_of_isDiag (hF'diag x hx)
    exact ⟨d, by simpa [diagUHom] using hd⟩
  have hcardF' : Nat.card F' = 81 := by
    change Nat.card (F.map (MulAut.conj hconj).toMonoidHom) = 81
    rw [Subgroup.card_map_of_injective (MulAut.conj hconj).injective, hcardF]
  let D : Subgroup (Fin 4 → Kˣ) := F'.comap (diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K)
  let C : Subgroup (Fin 4 → Kˣ) := Subgroup.pi Set.univ fun _ => rootsOfUnity 3 K
  have hDC : D ≤ C := by
    intro d hd
    rw [Subgroup.mem_pi]
    intro i _
    rw [mem_rootsOfUnity]
    have hdF' : (diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K) d ∈ F' := hd
    have hpow : ((diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K) d) ^ 3 = 1 :=
      hF'el.2 _ hdF'
    have hpow' : (diagU d) ^ 3 = 1 := hpow
    rw [diagU_pow] at hpow'
    have hd3 : d ^ 3 = 1 := diagU_injective (by simpa [diagU_one] using hpow')
    exact congrFun hd3 i
  have hmapD : D.map (diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K) = F' := by
    change (F'.comap (diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K)).map
      (diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K) = F'
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hF'leRange
  have hcardD : Nat.card D = 81 := by
    rw [← hcardF', ← hmapD, Subgroup.card_map_of_injective diagU_injective]
  have hCcard_le : Nat.card C ≤ 81 := by
    have hinj : Function.Injective (fun d : C =>
        (fun i : Fin 4 => (⟨d.1 i, (Subgroup.mem_pi Set.univ (H := fun _ => rootsOfUnity 3 K)).mp
          d.2 i trivial⟩ : rootsOfUnity 3 K))) := by
      intro d e hde
      apply Subtype.ext
      funext i
      exact congrArg (fun x : rootsOfUnity 3 K => (x : Kˣ)) (congrFun hde i)
    have h1 := Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card (Fin 4 → rootsOfUnity 3 K) =
        Nat.card (rootsOfUnity 3 K) ^ 4 := by
      rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h3 : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
    calc Nat.card C ≤ Nat.card (Fin 4 → rootsOfUnity 3 K) := h1
      _ = Nat.card (rootsOfUnity 3 K) ^ 4 := h2
      _ ≤ 3 ^ 4 := Nat.pow_le_pow_left h3 4
      _ = 81 := by norm_num
  have hD_eq_C : D = C :=
    Subgroup.eq_of_le_of_card_ge hDC (by rw [hcardD]; exact hCcard_le)
  let proj0 : ↥C →* Kˣ := (Pi.evalMonoidHom (fun _ : Fin 4 => Kˣ) 0).comp C.subtype
  let proj01 : ↥C →* Kˣ × Kˣ :=
    ((Pi.evalMonoidHom (fun _ : Fin 4 => Kˣ) 0).prod
      (Pi.evalMonoidHom (fun _ : Fin 4 => Kˣ) 1)).comp C.subtype
  have hpowK (u : Kˣ) : u ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Kˣ) (x := u)
    rwa [Nat.card_units, hK] at h
  have hproj0_surj : Function.Surjective proj0 := by
    intro u
    have hu3 : u ^ 3 = 1 := hpowK u
    let d : Fin 4 → Kˣ := Pi.mulSingle 0 u
    have hdC : d ∈ C := by
      rw [Subgroup.mem_pi]
      intro i _
      rw [mem_rootsOfUnity]
      by_cases hi : i = 0
      · subst hi; simpa [d] using hu3
      · simp [d, Pi.mulSingle, hi]
    refine ⟨⟨d, hdC⟩, ?_⟩
    show d 0 = u
    simp [d]
  have hcardC : Nat.card C = 81 := by
    rw [← hD_eq_C, hcardD]
  have hproj0_ker_card : Nat.card proj0.ker = 27 := by
    have h := Subgroup.card_ker_mul_card_range proj0
    have hrange : proj0.range = ⊤ := MonoidHom.range_eq_top.mpr hproj0_surj
    rw [hrange] at h
    simp only [Subgroup.card_top] at h
    have hKunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    rw [hcardC, hKunits] at h
    omega
  have hproj01_surj : Function.Surjective proj01 := by
    intro uv
    obtain ⟨u, v⟩ := uv
    have hu3 : u ^ 3 = 1 := hpowK u
    have hv3 : v ^ 3 = 1 := hpowK v
    let d : Fin 4 → Kˣ := Pi.mulSingle 0 u * Pi.mulSingle 1 v
    have hdC : d ∈ C := by
      rw [Subgroup.mem_pi]
      intro i _
      rw [mem_rootsOfUnity]
      by_cases hi0 : i = 0
      · subst hi0
        simp [d, Pi.mulSingle, hu3]
      · by_cases hi1 : i = 1
        · subst hi1
          simp [d, Pi.mulSingle, hv3]
        · simp [d, Pi.mulSingle, hi0, hi1]
    refine ⟨⟨d, hdC⟩, ?_⟩
    apply Prod.ext
    · show d 0 = u
      simp [d, Pi.mulSingle]
    · show d 1 = v
      simp [d, Pi.mulSingle]
  have hproj01_ker_card : Nat.card proj01.ker = 9 := by
    have h := Subgroup.card_ker_mul_card_range proj01
    have hrange : proj01.range = ⊤ := MonoidHom.range_eq_top.mpr hproj01_surj
    rw [hrange] at h
    simp only [Subgroup.card_top] at h
    have hKunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    have hprod : Nat.card (Kˣ × Kˣ) = 9 := by simp [Nat.card_prod, hKunits]
    rw [hcardC, hprod] at h
    omega
  let B₁' : Subgroup (GL (Fin 4) K) :=
    proj0.ker.map ((diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K).comp C.subtype)
  let B₂' : Subgroup (GL (Fin 4) K) :=
    proj01.ker.map ((diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K).comp C.subtype)
  have hB₁'le : B₁' ≤ F' := by
    rintro b ⟨d, hd, rfl⟩
    have hdD : (d : Fin 4 → Kˣ) ∈ D := by rw [hD_eq_C]; exact d.2
    simpa [D] using hdD
  have hB₂'le : B₂' ≤ F' := by
    rintro b ⟨d, hd, rfl⟩
    have hdD : (d : Fin 4 → Kˣ) ∈ D := by rw [hD_eq_C]; exact d.2
    simpa [D] using hdD
  have hB₁'card : Nat.card B₁' = 27 := by
    change Nat.card (proj0.ker.map
      ((diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K).comp C.subtype)) = 27
    have hinj : Function.Injective
        ((diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K).comp C.subtype) := by
      intro a b hab
      exact Subtype.ext (diagU_injective hab)
    rw [Subgroup.card_map_of_injective hinj, hproj0_ker_card]
  have hB₂'card : Nat.card B₂' = 9 := by
    change Nat.card (proj01.ker.map
      ((diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K).comp C.subtype)) = 9
    have hinj : Function.Injective
        ((diagUHom : (Fin 4 → Kˣ) →* GL (Fin 4) K).comp C.subtype) := by
      intro a b hab
      exact Subtype.ext (diagU_injective hab)
    rw [Subgroup.card_map_of_injective hinj, hproj01_ker_card]
  have hB₁'exp : ∀ x : ↥B₁', x ^ 3 = 1 := by
    intro x
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp x.2
    have hd3 : (d : Fin 4 → Kˣ) ^ 3 = 1 := by
      have hmem := (Subgroup.mem_pi Set.univ (H := fun _ => rootsOfUnity 3 K)).mp d.2
      funext i
      exact (mem_rootsOfUnity 3 (d.1 i)).mp (hmem i trivial)
    apply Subtype.ext
    change ((x : GL (Fin 4) K)) ^ 3 = 1
    rw [← hdx]
    change (diagU (d : Fin 4 → Kˣ)) ^ 3 = 1
    rw [diagU_pow, hd3, diagU_one]
  have hB₂'exp : ∀ x : ↥B₂', x ^ 3 = 1 := by
    intro x
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp x.2
    have hd3 : (d : Fin 4 → Kˣ) ^ 3 = 1 := by
      have hmem := (Subgroup.mem_pi Set.univ (H := fun _ => rootsOfUnity 3 K)).mp d.2
      funext i
      exact (mem_rootsOfUnity 3 (d.1 i)).mp (hmem i trivial)
    apply Subtype.ext
    change ((x : GL (Fin 4) K)) ^ 3 = 1
    rw [← hdx]
    change (diagU (d : Fin 4 → Kˣ)) ^ 3 = 1
    rw [diagU_pow, hd3, diagU_one]
  have hB₁'p : IsPGroup 3 B₁' := hF'el.isPGroup.to_le hB₁'le
  have hB₂'p : IsPGroup 3 B₂' := hF'el.isPGroup.to_le hB₂'le
  have hB₁'nc : ¬ IsCyclic ↥B₁' :=
    s16k_not_isCyclic_of_card_pow (p := 3) (k := 3) Nat.prime_three (by norm_num)
      (by rw [hB₁'card]; norm_num) hB₁'exp
  have hB₂'nc : ¬ IsCyclic ↥B₂' :=
    s16k_not_isCyclic_of_card_pow (p := 3) (k := 2) Nat.prime_three (by norm_num)
      (by rw [hB₂'card]; norm_num) hB₂'exp
  let e0 : Fin 4 → K := Pi.single 0 1
  let e1 : Fin 4 → K := Pi.single 1 1
  have hB₁'fix : ∀ b ∈ B₁', (b : Matrix (Fin 4) (Fin 4) K) *ᵥ e0 = e0 := by
    intro b hb
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hb
    have hd0 : d.1 0 = 1 := by
      have := MonoidHom.mem_ker.mp hd
      simpa [proj0] using this
    change ((diagU (d : Fin 4 → Kˣ) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) *ᵥ e0 = e0
    rw [diagU_val]
    ext i
    rw [mulVec_diagonal]
    by_cases hi : i = 0
    · subst hi; simp [e0, hd0]
    · simp [e0, hi]
  have hB₂'fix : ∀ b ∈ B₂', (b : Matrix (Fin 4) (Fin 4) K) *ᵥ (e0 + e1) = e0 + e1 := by
    intro b hb
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hb
    have hd01 := MonoidHom.mem_ker.mp hd
    have hd0 : d.1 0 = 1 := by simpa [proj01] using congrArg Prod.fst hd01
    have hd1 : d.1 1 = 1 := by simpa [proj01] using congrArg Prod.snd hd01
    change ((diagU (d : Fin 4 → Kˣ) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) *ᵥ (e0 + e1) = e0 + e1
    rw [diagU_val]
    ext i
    rw [mulVec_add, Pi.add_apply, mulVec_diagonal, mulVec_diagonal]
    by_cases hi0 : i = 0
    · subst hi0; simp [e0, e1, hd0]
    · by_cases hi1 : i = 1
      · subst hi1; simp [e0, e1, hd1]
      · simp [e0, e1, hi0, hi1]
  let B₁ : Subgroup (GL (Fin 4) K) :=
    B₁'.map (MulAut.conj (hconj⁻¹)).toMonoidHom
  let B₂ : Subgroup (GL (Fin 4) K) :=
    B₂'.map (MulAut.conj (hconj⁻¹)).toMonoidHom
  have hB₁le : B₁ ≤ F := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
    have hxF' : x ∈ F' := hB₁'le hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxF'
    have hb_eq : MulAut.conj (hconj⁻¹) x = y := by
      rw [← hyx, MulAut.conj_apply]
      change hconj⁻¹ * (hconj * y * hconj⁻¹) * (hconj⁻¹)⁻¹ = y
      group
    change ((MulAut.conj (hconj⁻¹)) x : GL (Fin 4) K) ∈ F
    rwa [hb_eq]
  have hB₂le : B₂ ≤ F := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
    have hxF' : x ∈ F' := hB₂'le hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxF'
    have hb_eq : MulAut.conj (hconj⁻¹) x = y := by
      rw [← hyx, MulAut.conj_apply]
      change hconj⁻¹ * (hconj * y * hconj⁻¹) * (hconj⁻¹)⁻¹ = y
      group
    change ((MulAut.conj (hconj⁻¹)) x : GL (Fin 4) K) ∈ F
    rwa [hb_eq]
  have hB₁card : Nat.card B₁ = 27 := by
    change Nat.card (B₁'.map (MulAut.conj (hconj⁻¹)).toMonoidHom) = 27
    rw [Subgroup.card_map_of_injective (MulAut.conj (hconj⁻¹)).injective, hB₁'card]
  have hB₂card : Nat.card B₂ = 9 := by
    change Nat.card (B₂'.map (MulAut.conj (hconj⁻¹)).toMonoidHom) = 9
    rw [Subgroup.card_map_of_injective (MulAut.conj (hconj⁻¹)).injective, hB₂'card]
  have hB₁p : IsPGroup 3 B₁ := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [hB₁card]; norm_num
  have hB₂p : IsPGroup 3 B₂ := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hB₂card]; norm_num
  have hB₁nc : ¬ IsCyclic ↥B₁ := by
    intro hcyc
    exact hB₁'nc ((MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective B₁' (MulAut.conj (hconj⁻¹)).toMonoidHom
        (MulAut.conj (hconj⁻¹)).injective)).mpr hcyc)
  have hB₂nc : ¬ IsCyclic ↥B₂ := by
    intro hcyc
    exact hB₂'nc ((MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective B₂' (MulAut.conj (hconj⁻¹)).toMonoidHom
        (MulAut.conj (hconj⁻¹)).injective)).mpr hcyc)
  let w₁ : Fin 4 → K := ((hconj⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ e0
  let w₂ : Fin 4 → K := ((hconj⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (e0 + e1)
  have hSUid : (hS : GL (Fin 4) K) ∈ SUid σ 4 := by
    have hSUeq : SUid σ 4 = StatedSU 4 2 K := by
      change SUid (frobeniusEquiv K 2) 4 = StatedSU 4 2 K
      simpa using SUid_eq_statedSU (p := 2) (f := 1) hcard2 4
    rw [hSUeq]
    exact hS.2
  let gSU : SUid σ 4 := ⟨(hS : GL (Fin 4) K), hSUid⟩
  have hisoInv : ∀ v : Fin 4 → K,
      herm σ (((hconj⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v)
        (((hconj⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) = herm σ v v := by
    intro v
    have h := herm_smul_smul σ gSU⁻¹ v v
    have hsmul : gSU⁻¹ • v = ((hconj⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) *ᵥ v := by
      rw [smul_def]
      rfl
    rwa [hsmul] at h
  have hw₁ : w₁ ≠ 0 := by
    intro hzero
    have h1 : ((hconj : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w₁ = e0 := by
      simp only [w₁]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hzero, Matrix.mulVec_zero] at h1
    have h2 : e0 = 0 := h1.symm
    have h3 := congrFun h2 0
    simp [e0] at h3
  have hw₂ : w₂ ≠ 0 := by
    intro hzero
    have h1 : ((hconj : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w₂ = e0 + e1 := by
      simp only [w₂]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hzero, Matrix.mulVec_zero] at h1
    have h2 : e0 + e1 = 0 := h1.symm
    have h3 := congrFun h2 0
    simp [e0, e1] at h3
  have hw₁norm : herm σ w₁ w₁ = 1 := by
    simp only [w₁]
    rw [hisoInv]
    rw [show e0 = Pi.single 0 1 from rfl, s16k_herm_single]
    simp [hσapply]
  have hw₂norm : herm σ w₂ w₂ = 0 := by
    simp only [w₂]
    rw [hisoInv]
    simp only [herm_add_left, herm_add_right]
    have h00 : herm σ e0 e0 = 1 := by
      rw [show e0 = Pi.single 0 1 from rfl, s16k_herm_single]
      simp [hσapply]
    have h11 : herm σ e1 e1 = 1 := by
      rw [show e1 = Pi.single 1 1 from rfl, s16k_herm_single]
      simp [hσapply]
    have h01 : herm σ e0 e1 = 0 := by
      rw [show e0 = Pi.single 0 1 from rfl, show e1 = Pi.single 1 1 from rfl,
        s16k_herm_single]
      norm_num
    have h10 : herm σ e1 e0 = 0 := by
      rw [show e0 = Pi.single 0 1 from rfl, show e1 = Pi.single 1 1 from rfl,
        s16k_herm_single]
      norm_num
    rw [h00, h11, h01, h10]
    simpa using CharTwo.add_self_eq_zero (1 : K)
  have hB₁fix : ∀ b ∈ B₁, (b : Matrix (Fin 4) (Fin 4) K) *ᵥ w₁ = w₁ := by
    simpa only [w₁, B₁] using s16k_conj_fix (A := hconj) hB₁'fix
  have hB₂fix : ∀ b ∈ B₂, (b : Matrix (Fin 4) (Fin 4) K) *ᵥ w₂ = w₂ := by
    simpa only [w₂, B₂] using s16k_conj_fix (A := hconj) hB₂'fix
  exact ⟨B₁, B₂, w₁, w₂, hB₁le, hB₂le, hB₁p, hB₂p, hB₁card, hB₂card, hB₁nc, hB₂nc,
    hw₁, hw₁norm, hw₂, hw₂norm, hB₁fix, hB₂fix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
