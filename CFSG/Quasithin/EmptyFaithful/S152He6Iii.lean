module

public import CFSG.Quasithin.EmptyFaithful.S152He6IiiAbs
public import CFSG.Quasithin.EmptyFaithful.S152He6Small
public import CFSG.Quasithin.EmptyFaithful.S152L27Insp
public import CFSG.Quasithin.EmptyFaithful.S152He5Defs
public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.EmptyFaithful.S146xThreeA
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B69Cent
public import CFSG.Quasithin.Background.B69Main
public import CFSG.Quasithin.Background.B69Stab
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.EmptyFaithfulMultiple.Bridge
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15Proof
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs3
public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE
public import CFSG.Quasithin.Vol2.Ch3Sec1Lem319Aux
public import CFSG.Quasithin.Vol2.Ch3zGood
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique He6
open scoped commutatorElement

theorem isPerfect_oTwoQuot {G : Type} [Group G] {L : Subgroup G} (hperf : ⁅L, L⁆ = L) :
    Group.IsPerfect (OTwoQuot L) := by
  have hL : Group.IsPerfect ↥L := by
    refine ⟨?_⟩
    rw [commutator_def]
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hperf]
  exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _)

section Bridge

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Mv_of_conjSub {s : G} {B B' : Subgroup G} (h : conjSub s B' = B) : Mv s⁻¹ B B' := by
  intro x
  rw [← h, mem_conjSub, inv_inv]

omit [Finite G] in
theorem conjSub_inj' {g : G} {H K : Subgroup G} (h : conjSub g H = conjSub g K) : H = K := by
  have := congrArg (conjSub g⁻¹) h
  rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

theorem iii_of_setting
    (Fam : (G : Type) → [Group G] → Prop)
    (hFamIso : ∀ (G H : Type) [Group G] [Group H], G ≃* H → Fam G → Fam H)
    (hFamSimple : ∀ (G : Type) [Group G], Fam G → IsSimpleGroup G) (k : ℕ)
    {T Mc M H L N A : Subgroup G} {t : G} (hs : Setting152 T Mc M)
    (hL : L ∈ cComp Mc) (ht : t ∈ T) (htN : t ∉ Subgroup.normalizer (L : Set G))
    (hKc : conjClosure (oTwoUpper H) Mc = L ⊔ conjSub t L)
    (hcomm : ⁅L, conjSub t L⁆ ≤ pCoreOf 2 Mc) (hFamQ : Fam (OTwoQuot L))
    (hstep : IsChiefStep (conjClosure (oTwoUpper H) Mc ⊔ T) (pCoreOf 2 Mc) A N)
    (hnot : ¬ ⁅N, V154 T Mc M⁆ ≤ A)
    (hbound : Nat.card ↥(⁅N, V154 T Mc M⁆ ⊔ A) ≤ k * Nat.card ↥A)
    (final : ∀ (W : Type) [CommGroup W] [Finite W] (P : PairData W)
      (Tb Vb : Subgroup (MulAut W)) (τ : MulAut W),
      Fam ↥P.A → Fam ↥P.A' → P.A ≤ P.Xb → P.A' ≤ P.Xb → Tb ≤ P.Xb → IsPGroup 2 Tb →
      (∀ S : Subgroup (MulAut W), S ≤ P.Xb → IsPGroup 2 S →
        ∃ g ∈ P.Xb, ∀ s ∈ S, g * s * g⁻¹ ∈ Tb) →
      (∀ x ∈ P.Xb, ∃ κ ∈ P.A ⊔ P.A', ∃ s ∈ Tb, x = κ * s) →
      (∀ Q' : Subgroup (MulAut W), Q' ≤ P.Xb → (Q'.subgroupOf P.Xb).Normal → IsPGroup 2 Q' →
        Q' = ⊥) →
      τ ∈ Tb → (∀ x, x ∈ P.A ↔ τ * x * τ⁻¹ ∈ P.A') → (∀ x, x ∈ P.A' ↔ τ * x * τ⁻¹ ∈ P.A) →
      Vb ≤ Tb → (∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb) → Vb ≠ ⊥ →
      (∀ v ∈ Vb, Nat.card (cmt v ⊤) ≤ k) → False) : False := by
  classical
  set K : Subgroup G := conjClosure (oTwoUpper H) Mc with hKdef
  set Lt : Subgroup G := conjSub t L with hLtdef
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hTM : T ≤ M := hs.mf.1.1.2
  have hsyl : ∀ P : Subgroup G, T ≤ P → IsSylowTwoOf T P := fun P hTP =>
    isSylowTwoOf_of_le151 hs.qtfe.sylow hTP
  have hQT : pCoreOf 2 Mc ≤ T := pCoreOf_le_of_isSylowTwoOf (hsyl Mc hTMc)
  have hQ2 : IsPGroup 2 (pCoreOf 2 Mc) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mc
  have hLMc : L ≤ Mc := le_of_mem_cComp hL
  have hLtMc : Lt ≤ Mc := by
    intro x hx
    have h1 : t⁻¹ * x * t ∈ L := mem_conjSub.mp hx
    have h2 : t * (t⁻¹ * x * t) * t⁻¹ ∈ Mc :=
      Mc.mul_mem (Mc.mul_mem (hTMc ht) (hLMc h1)) (Mc.inv_mem (hTMc ht))
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [e] at h2
  have hKMc : K ≤ Mc := by rw [hKc]; exact sup_le hLMc hLtMc
  have hXMc : K ⊔ T ≤ Mc := sup_le hKMc hTMc
  have hMcn : Mc ≤ Subgroup.normalizer (K : Set G) := le_normalizer_conjClosure (oTwoUpper H) Mc
  have hXn : ∀ g ∈ K ⊔ T, ∀ κ ∈ K, g * κ * g⁻¹ ∈ K := fun g hg κ hκ =>
    (Subgroup.mem_normalizer_iff.mp (hMcn (hXMc hg)) κ).mp hκ
  have hQn : ∀ g ∈ K ⊔ T, ∀ q ∈ pCoreOf 2 Mc, g * q * g⁻¹ ∈ pCoreOf 2 Mc := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc (hXMc hg)) q).mp hq
  have hQX : pCoreOf 2 Mc ≤ K ⊔ T := hQT.trans le_sup_right
  have hLt_mem : Lt ∈ cComp Mc := map_conj_mem_cComp hL (hTMc ht)
  have hLne : L ≠ Lt := by
    intro h
    apply htN
    exact A38.map_conj_eq_iff.mp h.symm
  have hconjK : ∀ g ∈ Mc, conjSub g K = K := fun g hg => A38.map_conj_eq_iff.mpr (hMcn hg)
  have hperm : ∀ g ∈ Mc, (conjSub g L = L ∧ conjSub g Lt = Lt) ∨
      (conjSub g L = Lt ∧ conjSub g Lt = L) := by
    intro g hg
    have ha : conjSub g L ∈ cComp Mc := map_conj_mem_cComp hL hg
    have hb : conjSub g Lt ∈ cComp Mc := map_conj_mem_cComp hLt_mem hg
    have h1 : conjSub g (L ⊔ Lt) = L ⊔ Lt := by rw [← hKc]; exact hconjK g hg
    have ha' : conjSub g L ≤ L ⊔ Lt :=
      calc conjSub g L ≤ conjSub g (L ⊔ Lt) := conjSub_mono g le_sup_left
        _ = L ⊔ Lt := h1
    have hb' : conjSub g Lt ≤ L ⊔ Lt :=
      calc conjSub g Lt ≤ conjSub g (L ⊔ Lt) := conjSub_mono g le_sup_right
        _ = L ⊔ Lt := h1
    rcases cComp_eq_of_le_sup ha hL hLt_mem ha' with h2 | h2 <;>
      rcases cComp_eq_of_le_sup hb hL hLt_mem hb' with h3 | h3
    · exact absurd (conjSub_inj' (h3.trans h2.symm)).symm hLne
    · exact Or.inl ⟨h2, h3⟩
    · exact Or.inr ⟨h2, h3⟩
    · exact absurd (conjSub_inj' (h2.trans h3.symm)) hLne
  have hTperm : ∀ s ∈ T, (Mv s⁻¹ L L ∧ Mv s⁻¹ Lt Lt) ∨ (Mv s⁻¹ L Lt ∧ Mv s⁻¹ Lt L) := by
    intro s hsT
    rcases hperm s (hTMc hsT) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Mv_of_conjSub h1, Mv_of_conjSub h2⟩
    · exact Or.inr ⟨Mv_of_conjSub h2, Mv_of_conjSub h1⟩
  have hLt : Mv t⁻¹ Lt L := Mv_of_conjSub rfl
  have hLc : Mv t⁻¹ L Lt := by
    rcases hperm t (hTMc ht) with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1.symm hLne
    · exact Mv_of_conjSub h2
  have hO2L : ∀ x : ↥L, x ∈ CFSG.Open.pCore 2 ↥L → (x : G) ∈ pCoreOf 2 Mc := by
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hL) h1
  have hVT : V154 T Mc M ≤ T := S152N.V154_le_T hs
  have hVM : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hEn : ∀ s ∈ T, ∀ e ∈ V154 T Mc M, s * e * s⁻¹ ∈ V154 T Mc M := fun s hsT e he =>
    (Subgroup.mem_normalizer_iff.mp (hVM (hTM hsT)) e).mp he
  exact iii_reduce Fam hFamIso hFamSimple k rfl hXn (hsyl _ le_sup_right) hKc
    (perfect_of_mem_cComp hL) hLt hLc ht hTperm hcomm hO2L hFamQ hQ2 hQn hQX hVT hEn hstep hnot
    hbound final

end Bridge

@[expose] def Insp15227TransIi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H : Subgroup G), Setting152 T Mc M → IsHStar T M H →
    ¬ V154 T Mc M ≤ pCoreOf 2 Mc → Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) →
    ∀ L N : Subgroup G, IsChiefStep (conjClosure (oTwoUpper H) Mc ⊔ T) (pCoreOf 2 Mc) L N →
      Nat.card ↥(⁅N, V154 T Mc M⁆ ⊔ L) ≠ 2 * Nat.card ↥L

@[expose] def Insp15227TransIii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H : Subgroup G), Setting152 T Mc M → IsHStar T M H →
    ¬ V154 T Mc M ≤ pCoreOf 2 Mc → Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) →
    ∀ L N : Subgroup G, IsChiefStep (conjClosure (oTwoUpper H) Mc ⊔ T) (pCoreOf 2 Mc) L N →
      Nat.card ↥(⁅N, V154 T Mc M⁆ ⊔ L) ≠ 2 * Nat.card ↥L

theorem insp15227TransLn_of_parts (hii : Insp15227TransIi) (hiii : Insp15227TransIii) :
    Insp15227TransLn := by
  intro G _ _ T Mc M H hs hH hV hcase L N hstep
  rcases hcase with h | h
  · exact hii G T Mc M H hs hH hV h L N hstep
  · exact hiii G T Mc M H hs hH hV h L N hstep

theorem insp15227TransIii_of_autL2 (hAut : AutL2SylowInner) : Insp15227TransIii := by
  intro G _ _ T Mc M H hs hH hVQ hcase A N hstep heq
  obtain ⟨L, t, -, hL, ht, htN, hKc, hcomm, hquot⟩ := hcase
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hL
  have : Group.IsPerfect (OTwoQuot L) := isPerfect_oTwoQuot hperf
  have hFam : FamPSL (OTwoQuot L) := famPSL_of_perfect hquot
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  refine iii_of_setting FamPSL (fun _ _ _ _ e h => famPSL_iso e h)
    (fun _ _ h => famPSL_simple h) 2 hs hL ht htN hKc hcomm hFam hstep ?_ heq.le ?_
  · intro hle
    have : ⁅N, V154 T Mc M⁆ ⊔ A = A := sup_eq_right.mpr hle
    rw [this] at heq
    omega
  · intro W _ _ P Tb Vb τ hf _ hAX hA'X hTX hT2 hconj2 hXKT hO2 hτ hτA hτA' hVT hVn hVne hz
    exact P.trans_false hAut hf hAX hA'X hTX hT2 hconj2 hXKT hO2 hτ hτA hτA' hVT hVn hVne hz

@[expose] def Insp15227ShapeSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H : Subgroup G), Setting152 T Mc M → IsHStar T M H →
    ¬ V154 T Mc M ≤ pCoreOf 2 Mc →
    ∀ (L : Subgroup G) (t : G), L ∈ cComp Mc → t ∈ T → t ∉ Subgroup.normalizer (L : Set G) →
      conjClosure (oTwoUpper H) Mc = L ⊔ conjSub t L → ⁅L, conjSub t L⁆ ≤ pCoreOf 2 Mc →
      IsL2Prime 7 (OTwoQuot L) →
      ∀ A N : Subgroup G, IsChiefStep (conjClosure (oTwoUpper H) Mc ⊔ T) (pCoreOf 2 Mc) A N →
        quasithinOmegaOneCenter T ≤ A → ¬ ⁅N, V154 T Mc M⁆ ≤ A →
        Nat.card ↥(⁅N, V154 T Mc M⁆ ⊔ A) ≤ 4 * Nat.card ↥A →
        GoodShape152 (conjClosure (oTwoUpper H) Mc ⊔ T)

theorem insp15227Shape_of_seven (hAut : AutL2SylowInner) (h7 : Insp15227ShapeSeven) :
    Insp15227Shape := by
  intro G _ _ T Mc M H hs hH hVQ hcase A N hstep hZA hnot hle4
  rcases hcase with hii | hiii
  · obtain ⟨-, -, n, hn, he⟩ := hii
    exact Or.inl ⟨n, hn, he⟩
  · obtain ⟨L, t, -, hL, ht, htN, hKc, hcomm, hquot⟩ := hiii
    have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hL
    have : Group.IsPerfect (OTwoQuot L) := isPerfect_oTwoQuot hperf
    have hFam : FamPSL (OTwoQuot L) := famPSL_of_perfect hquot
    by_cases hne7 : FamPSLne7 (OTwoQuot L)
    · exfalso
      refine iii_of_setting FamPSLne7 (fun _ _ _ _ e h => famPSLne7_iso e h)
        (fun _ _ h => famPSLne7_simple h) 4 hs hL ht htN hKc hcomm hne7 hstep hnot hle4 ?_
      intro W _ _ P Tb Vb τ hf hf' hAX hA'X hTX hT2 hconj2 hXKT hO2 hτ hτA hτA' hVT hVn hVne hz
      exact P.shape_false hAut hf hf' hAX hA'X hTX hT2 hconj2 hXKT hO2 hτ hτA hτA' hVT hVn hVne hz
    · have h7' : IsL2Prime 7 (OTwoQuot L) := by
        rcases hFam with ⟨f, hf, hf2, e⟩ | ⟨p, hp, hp5, e⟩
        · exact absurd (Or.inl ⟨f, hf, hf2, e⟩) hne7
        · by_cases hp7 : p = 7
          · subst hp7
            exact e
          · exact absurd (Or.inr ⟨p, hp, hp5, hp7, e⟩) hne7
      exact h7 G T Mc M H hs hH hVQ L t hL ht htN hKc hcomm h7' A N hstep hZA hnot hle4

end CFSG.Quasithin
