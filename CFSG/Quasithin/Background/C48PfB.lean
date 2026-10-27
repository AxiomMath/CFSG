module

public import CFSG.Quasithin.Background.C48PfA
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Background.SmithB42Dispatch
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338

public section

namespace CFSG.Quasithin.C48Pf

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem inf_centralizer_le (h27 : ASC27Statement G)
    (h : HypC28 H R M L V) (hK : K ∈ cComp H) (hchar : CharTwo K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ M)
    (h41 : C41Conclusion H R M L V K) (h4 : C41Case4 H R M L V K) :
    K ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤ pCoreOf 2 K := by
  have hRK := le_normalizer_K h h41
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rcases h4.1 with h4' | h5'
    · exact center_eq_bot_of_isPSL_two_one h4'
    · exact center_eq_bot_of_isPSL_two_one h5'
  set Q := pCoreOf 2 (K ⊔ R) with hQ
  set U := omegaOneCenterOf Q with hU
  obtain ⟨⟨-, hC, -⟩, -⟩ := h27 H R M K U (c2_10_four h) hK hq hchar hKM hRK rfl
  have hCQ : (K ⊔ R) ⊓ Subgroup.centralizer (U : Set G) ≤ Q :=
    hC.trans (sup_le le_rfl ((oTwoZIn_le_pCoreOf hZ).trans (pCoreOf_le_pCoreOf_sup hRK)))
  have hKQn : K ≤ Subgroup.normalizer ((K ⊓ Q : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) x
    have h2 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R) (Subgroup.mem_sup_left hk)) x
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  have hKQ : K ⊓ Q ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hKQn
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  intro x hx
  exact hKQ ⟨hx.1, hCQ ⟨Subgroup.mem_sup_left hx.1, hx.2⟩⟩

theorem pCoreOf_le_centralizer (hRK : R ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 K ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : u ∈ centerOf (pCoreOf 2 (K ⊔ R)) := by
    have : omegaOneOf (centerOf (pCoreOf 2 (K ⊔ R))) ≤ centerOf (pCoreOf 2 (K ⊔ R)) := by
      rw [omegaOneOf, Subgroup.closure_le]
      exact fun y hy => hy.1
    exact this hu
  exact (Subgroup.mem_centralizer_iff.mp hu'.2 x (pCoreOf_le_pCoreOf_sup hRK hx)).symm

theorem isTwoReducedIn_U (h27 : ASC27Statement G) (h : HypC28 H R M L V) (hK : K ∈ cComp H)
    (hchar : CharTwo K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ M)
    (h41 : C41Conclusion H R M L V K) :
    IsTwoReducedIn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
  (h27 H R M K _ (c2_10_four h) hK hq hchar hKM (le_normalizer_K h h41) rfl).1.2.2

theorem ker_autOnHom_eq (h27 : ASC27Statement G) (h : HypC28 H R M L V) (hK : K ∈ cComp H)
    (hchar : CharTwo K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ M)
    (h41 : C41Conclusion H R M L V K) (h4 : C41Case4 H R M L V K)
    (hKU : K ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G)) :
    (InternalSec.autOnHom hKU).ker = CFSG.pCore 2 ↥K := by
  have hle := inf_centralizer_le h27 h hK hchar hq hKM h41 h4
  have hge := pCoreOf_le_centralizer (le_normalizer_K h h41)
  have hpc : pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := C2A3Orbits.pCoreOf_eq_map_pCore K
  ext k
  rw [InternalSec.mem_ker_autOnHom]
  constructor
  · intro hk
    have : (k : G) ∈ pCoreOf 2 K := hle ⟨k.2, hk⟩
    rw [hpc] at this
    obtain ⟨k', hk', hkk'⟩ := this
    rw [show k = k' from Subtype.ext hkk'.symm]
    exact hk'
  · intro hk
    apply hge
    rw [hpc]
    exact ⟨k, hk, rfl⟩

theorem isPSL_autOn (h27 : ASC27Statement G) (h : HypC28 H R M L V) (hK : K ∈ cComp H)
    (hchar : CharTwo K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ M)
    (h41 : C41Conclusion H R M L V K) (h4 : C41Case4 H R M L V K) :
    IsPSL 4 2 1 ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ∨
      IsPSL 5 2 1 ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) := by
  have hKU : K ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :=
    le_sup_left.trans (isTwoReducedIn_U h27 h hK hchar hq hKM h41).2.1
  have hker := ker_autOnHom_eq h27 h hK hchar hq hKM h41 h4 hKU
  let e : ModO2 K ≃* ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (InternalSec.autOnHom_surjective hKU))
  rcases h4.1 with h4' | h5'
  · exact Or.inl (Setup.Family.statedClassicalModel_of_mulEquiv e h4')
  · exact Or.inr (Setup.Family.statedClassicalModel_of_mulEquiv e h5')

theorem alt15127_autOn (h27 : ASC27Statement G) (h51 : AsB51) (hI16 : AsI16Cover)
    (hA8 : AsI16CoverA8) (h : HypC28 H R M L V) (hK : K ∈ cComp H) (hchar : CharTwo K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ M)
    (h41 : C41Conclusion H R M L V K) (h4 : C41Case4 H R M L V K) :
    ∃ hU : IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))),
      @Alt15127 ↥(omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) (commGroupOfElemAbelian hU)
        (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
        (@commV _ (commGroupOfElemAbelian hU)
          (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) := by
  set U := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hUdef
  have hRK := le_normalizer_K h h41
  obtain ⟨⟨-, -, hred⟩, ⟨-, hV, -, A, -, hA⟩, -⟩ :=
    h27 H R M K U (c2_10_four h) hK hq hchar hKM hRK rfl
  refine ⟨hV, ?_⟩
  have : IsMulCommutative ↥U := hV.1
  have hYW : K ⊔ R ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hYW
  have hYK : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have h2K : ∀ y ∈ K ⊔ R, ∃ e : ℕ, y ^ 2 ^ e ∈ K := InternalSec.two_of_sup h.pgroup hRK
  have h2 : ∀ y ∈ K ⊔ R, ∃ e : ℕ, y ^ 2 ^ e ∈ K ⊔ Subgroup.centralizer (U : Set G) :=
    fun y hy => by
      obtain ⟨e, he⟩ := h2K y hy
      exact ⟨e, Subgroup.mem_sup_left he⟩
  have hO2 : pCoreOf 2 (autOn (K ⊔ R) U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hKX : autOn K U ≤ autOn (K ⊔ R) U := InternalSec.autOn_le_autOn_of_le le_sup_left
  have hXK : autOn (K ⊔ R) U ≤ Subgroup.normalizer (autOn K U : Set (MulAut ↥U)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact InternalSec.autOn_normal_of hYK x hx k hk
    · intro hk
      have := InternalSec.autOn_normal_of hYK x⁻¹ ((autOn (K ⊔ R) U).inv_mem hx) _ hk
      simpa [mul_assoc] using this
  have hO2K : pCoreOf 2 (autOn K U) = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ hKX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).2 hXK)
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hle := inf_centralizer_le h27 h hK hchar hq hKM h41 h4
  have hnt : ¬ K ≤ Subgroup.centralizer (U : Set G) := by
    intro hKC
    have hKO : K ≤ pCoreOf 2 K := fun k hk => hle ⟨hk, hKC hk⟩
    have : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) := CFSG.LocalCores.isQuasisimple_nontrivial hq
    obtain ⟨a, b, hab⟩ := this
    apply hab
    have hall : ∀ q : ↥K ⧸ CFSG.pCore 2 ↥K, q = 1 := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      rw [QuotientGroup.eq_one_iff]
      have hk := hKO k.2
      rw [C2A3Orbits.pCoreOf_eq_map_pCore K] at hk
      obtain ⟨k', hk', hkk'⟩ := hk
      rw [show k = k' from Subtype.ext hkk'.symm]
      exact hk'
    rw [hall a, hall b]
  have hqK := InternalSec.isQuasisimple_autOn hKU hq hO2K hnt
  have hSK : SQTKGroup ↥K := B42Dispatch.sqtkGroup_of_le h.sqtk (le_of_mem_cComp hK)
  have hker2 : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (U : Set G)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hle
  have hS := InternalSec.sqtkGroup_autOn hKU hSK hker2
  have hLA : ⁅autOn K U, A⁆ = autOn K U :=
    H13.Ch3Sec3.commutator_eq_of_two hXK (InternalSec.autOn_two_of hKU h2) hO2 hqK hA.1
      hA.2.1 (fun a ha => hA.2.2.1.2 a ha)
  obtain ⟨hB, -⟩ := InternalSec.b51Hyp_ffJ_autOn hYW le_sup_left hYK h2 hO2 hqK hS hA hLA
  have hV2 : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  exact alt15127_of_b51 h51 hI16 hA8 hV2 hB (isPSL_autOn h27 h hK hchar hq hKM h41 h4)

end CFSG.Quasithin.C48Pf
