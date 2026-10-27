module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Z
public import CFSG.Quasithin.EmptyFaithful.S1421QA15R
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtB42ListFTypes
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtLJComm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtLJCtx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.g0Of_eq_of_le (c : Core3Ctx T M H K1 L M₁) (hY : yOfL22 T M ≤ L) :
    g0Of T M H K1 = L ⊔ sOf T K1 := by
  rw [c.eq, sup_eq_left.mpr hY]

theorem Core3Ctx.sOf_ne_bot (c : Core3Ctx T M H K1 L M₁) : sOf T K1 ≠ ⊥ := by
  obtain ⟨z, hz, hz1, -⟩ := exists_generator c.st
  intro h
  have := z_mem_sOf c.st hz
  rw [h, Subgroup.mem_bot] at this
  exact hz1 this

theorem Core3Ctx.commutator_thompsonJ_eq (h210 : Lemma14210) (c : Core3Ctx T M H K1 L M₁)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hY : yOfL22 T M ≤ L) :
    ⁅L, thompsonJ (sOf T K1)⁆ = L := by
  have hG0 := c.g0Of_eq_of_le hY
  have hLX : L ∈ cComp (L ⊔ sOf T K1) := hG0 ▸ c.mem
  have hSyl : IsSylowTwoOf (sOf T K1) (L ⊔ sOf T K1) := hG0 ▸ isSylowTwoOf_g0 c.inM c.sylow
  have hSN : sOf T K1 ≤ Subgroup.normalizer (L : Set G) :=
    ((le_sup_right : sOf T K1 ≤ L ⊔ sOf T K1).trans hG0.symm.le).trans c.g0Of_le_normalizer
  have hJS : thompsonJ (sOf T K1) ≤ sOf T K1 := thompsonJ_le_self151 _
  refine LJ.commutator_thompsonJ_eq_of_le_normalizer hSyl (subnormal_of_mem_cComp hLX)
    (hJS.trans hSN) (perfect_of_mem_cComp hLX) hq (M := Subgroup.normalizer
      (thompsonJ (sOf T K1) : Set G)) le_rfl fun h => c.not_le_mc ?_
  exact le_mcOf_of_le_normalizer_char c.st c.lt h210
    (Setup.thompsonJ_ne_bot (isPGroup_sOf c.st) c.sOf_ne_bot) hJS
    (Setup.characteristic_thompsonJ _) c.lt_L.le h

theorem Core3Ctx.omegaOneCenter_le_vz (c : Core3Ctx T M H K1 L M₁) {X : Subgroup G} :
    quasithinOmegaOneCenter T ≤ VZ (sOf T K1) X := by
  refine (Subgroup.closure_le _).mpr fun z hz => ?_
  have hzZ : z ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure hz
  have hzS : z ∈ sOf T K1 := z_mem_sOf c.st hzZ
  have hzZS : z ∈ quasithinOmegaOneCenter (sOf T K1) :=
    Subgroup.subset_closure ⟨⟨hzS, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hz.1.2 y (sOf_le_T hy)⟩, hz.2⟩
  exact le_conjClosure _ _ hzZS

end S1421

@[expose] def ListAD (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ IsPSL 2 2 n X) ∨
    (((∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n X) ∨ (∃ n : ℕ, 2 ≤ n ∧ IsPSp4 2 n X) ∨
        ∃ n : ℕ, 2 ≤ n ∧ IsG2 2 n X) ∨
      ∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n (X ⧸ Subgroup.center X)) ∨
    (IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X) ∨
    (IsAlt 7 (X ⧸ Subgroup.center X) ∨ IsPSL 3 2 1 (X ⧸ Subgroup.center X) ∨
      IsAlt 6 (X ⧸ Subgroup.center X) ∨ IsPSU 3 3 1 (X ⧸ Subgroup.center X))

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.listTypes
    (h56 : AsB56) (hcover : AsA36NoOddCover) (hG2 : FactG2Cayley)
    (h210 : Lemma14210) (c : Core3Ctx T M H K1 L M₁) (hchar : CharTwo (g0Of T M H K1))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hY : yOfL22 T M ≤ L) :
    ListAD (↥L ⧸ CFSG.pCore 2 ↥L) := by
  set S := sOf T K1 with hSdef
  have hG0 := c.g0Of_eq_of_le hY
  have hLX : L ∈ cComp (L ⊔ S) := hG0 ▸ c.mem
  have hSyl : IsSylowTwoOf S (L ⊔ S) := hG0 ▸ isSylowTwoOf_g0 c.inM c.sylow
  have hX : CharTwo (L ⊔ S) := hG0 ▸ hchar
  have hpcX : pCoreOf 2 (L ⊔ S) ≠ ⊥ := hG0 ▸ c.pCore_ne
  have hred := C1GN.isTwoReducedIn_VZ hX hSyl
  have hVe : IsElemAbelian 2 (VZ S (L ⊔ S)) := hred.2.2.1
  have : IsMulCommutative ↥(VZ S (L ⊔ S)) := hVe.1
  have hO2 := LJ.pCoreOf_le_centralizer hred
  have hLnV : ¬ L ≤ Subgroup.centralizer (VZ S (L ⊔ S) : Set G) := by
    intro hLV
    apply c.not_le_mc
    intro x hx
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr c.omegaOneCenter_le_vz) (hLV hx)
  have hSQ : SQTKGroup ↥(L ⊔ S) :=
    sqtkGroup_of_pCoreOf_ne_bot c.st.hyp.qtke c.st.hyp.simple c.st.hyp.nonabelian hpcX
  have hJX : thompsonJ S ≤ thompsonJ (L ⊔ S) := thompsonJ_le_thompsonJ_of_isSylowTwoOf hSyl
  have hJ : ⁅L, thompsonJ S⁆ = L := c.commutator_thompsonJ_eq h210 hq hY
  have hLJ : L ≤ thompsonJ (L ⊔ S) := by
    have h1 : ⁅L, thompsonJ S⁆ ≤ thompsonJ (L ⊔ S) := by
      rw [Subgroup.commutator_le]
      intro l hl j hj
      have hl' : l ∈ Subgroup.normalizer (thompsonJ (L ⊔ S) : Set G) :=
        GammaExtra.normalizer_le_normalizer_thompsonJ (L ⊔ S)
          (Subgroup.le_normalizer ((le_sup_left : L ≤ L ⊔ S) hl))
      have h2 := (Subgroup.mem_normalizer_iff.mp hl' j).1 (hJX hj)
      rw [commutatorElement_def]
      exact (thompsonJ (L ⊔ S)).mul_mem h2 ((thompsonJ (L ⊔ S)).inv_mem (hJX hj))
    rwa [hJ] at h1
  have hLcJ : L ∈ cComp (thompsonJ (L ⊔ S)) :=
    cComp_mem_of_le hLX hLJ (thompsonJ_le_self _)
  have hLN : L ≤ Subgroup.normalizer (VZ S (L ⊔ S) : Set G) := le_sup_left.trans hred.2.1
  have hsub : IsSubnormal L (L ⊔ S) := subnormal_of_mem_cComp hLX
  have hO2L : pCoreOf 2 L ≤ Subgroup.centralizer (VZ S (L ⊔ S) : Set G) := fun x hx =>
    hO2 (S151S5.pCoreOf_le_of_isSubnormal' hsub hx)
  have hle : CFSG.pCore 2 ↥L ≤ (InternalSec.autOnHom hLN).ker := by
    intro x hx
    rw [InternalSec.mem_ker_autOnHom]
    exact hO2L ⟨x, by assumption, rfl⟩
  let ρ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L (VZ S (L ⊔ S))) :=
    QuotientGroup.lift _ (InternalSec.autOnHom hLN) hle
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hLN y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hne : ∃ k, ρ k ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hLnV
    intro l hl
    have h1 : ρ (QuotientGroup.mk ⟨l, hl⟩) = 1 := hall _
    have h2 : (InternalSec.autOnHom hLN) ⟨l, hl⟩ = 1 := h1
    exact (InternalSec.mem_ker_autOnHom hLN ⟨l, hl⟩).1 h2
  have hY' : CFSG.IsQuasisimple ↥(autOn L (VZ S (L ⊔ S))) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hρs hne
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hne
  have hlist := SBc3.autOn_mem_list_of_component h56 hVe hred hSQ hLcJ hY'
  have hSQL : SQTKGroup ↥L := B5.sqtk_of_le hSQ le_sup_left
  have hSQX : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    InternalSec.sqtkGroup_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
      hSQL
  have hO2X : CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    Setup.Campbell.pCore_quotient_pCore_eq_bot' 2
  exact B42ListF.list_of_b56 hcover hG2 hq hSQX hO2X hY' ρ hρs hker hlist

end S1421

end CFSG.Quasithin
