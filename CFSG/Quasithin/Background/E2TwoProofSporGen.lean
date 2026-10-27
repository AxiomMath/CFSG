module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique B6

namespace E2P

namespace SporB

section TwoMax

variable {H : Type} [Group H] {K T : Subgroup H}

theorem le_normalizer_inf (hK : K.Normal) :
    T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup H) : Set H) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxT, hxK⟩
    exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), hK.conj_mem x hxK t⟩
  · rintro ⟨hxT, hxK⟩
    have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [e]
    refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht, ?_⟩
    have := hK.conj_mem _ hxK t⁻¹
    rwa [inv_inv] at this

theorem sup_ne_top {Y : Subgroup H} (hYK : Y ≤ K) (hSY : T ⊓ K ≤ Y) (hY : Y ≠ K)
    (hT : T ≤ Subgroup.normalizer (Y : Set H)) : Y ⊔ T ≠ ⊤ := by
  intro h
  apply hY
  refine le_antisymm hYK fun x hxK => ?_
  have hxZ : x ∈ Y ⊔ T := by rw [h]; trivial
  obtain ⟨y, hy, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hT hxZ
  have htK : t ∈ K := by
    have := K.mul_mem (K.inv_mem (hYK hy)) hxK
    simpa using this
  exact Y.mul_mem hy (hSY ⟨ht, htK⟩)

theorem exists_max_of_ne_top [Finite H] {Y : Subgroup H} (hY : Y ≠ ⊤) :
    ∃ M : Subgroup H, IsMaxSubgroupIn ⊤ M ∧ Y ≤ M := by
  obtain ⟨M, hM, hYM⟩ := (eq_top_or_exists_le_coatom Y).resolve_left hY
  exact ⟨M, ⟨lt_top_iff_ne_top.mpr hM.1, fun L hML _ => hM.2 L hML⟩, hYM⟩

theorem exists_two_max [Finite H] (hKT : K ⊔ T = ⊤) {Q₀ Q₁ : Subgroup H} (h₀K : Q₀ ≤ K)
    (h₁K : Q₁ ≤ K) (hS₀ : T ⊓ K ≤ Q₀) (hS₁ : T ⊓ K ≤ Q₁) (h₀ : Q₀ ≠ K) (h₁ : Q₁ ≠ K)
    (hT₀ : T ≤ Subgroup.normalizer (Q₀ : Set H)) (hT₁ : T ≤ Subgroup.normalizer (Q₁ : Set H))
    (hgen : K ≤ Q₀ ⊔ Q₁) :
    ∃ M₁ M₂ : Subgroup H, IsMaxSubgroupIn ⊤ M₁ ∧ IsMaxSubgroupIn ⊤ M₂ ∧ M₁ ≠ M₂ ∧ T ≤ M₁ ∧
      T ≤ M₂ := by
  obtain ⟨M₁, hM₁, hY₁⟩ := exists_max_of_ne_top (sup_ne_top h₀K hS₀ h₀ hT₀)
  obtain ⟨M₂, hM₂, hY₂⟩ := exists_max_of_ne_top (sup_ne_top h₁K hS₁ h₁ hT₁)
  refine ⟨M₁, M₂, hM₁, hM₂, fun h => ?_, le_sup_right.trans hY₁, le_sup_right.trans hY₂⟩
  apply hM₁.1.ne
  rw [eq_top_iff, ← hKT]
  refine sup_le (hgen.trans (sup_le (le_sup_left.trans hY₁) ?_)) (le_sup_right.trans hY₁)
  rw [h]
  exact le_sup_left.trans hY₂

end TwoMax

section Model

variable {H : Type} [Group H] {K : Subgroup H} {C : Type} [Group C]

theorem exists_equiv_sylow [Finite C] (e : ↥K ≃* C) {S : Subgroup H} (hS : IsSylowTwoOf S K)
    {U : Subgroup C} (hU : IsSylowTwoOf U ⊤) :
    ∃ e' : ↥K ≃* C, (S.subgroupOf K).map e'.toMonoidHom = U := by
  have hS' := isSylowTwoOf_map_top_equiv e hS
  obtain ⟨g, -, hg⟩ := isSylowTwoOf_exists_conj hS' hU
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hg]
  show _ = ((S.subgroupOf K).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_map]
  rfl

variable [K.Normal]

@[expose] noncomputable def autK (e : ↥K ≃* C) (t : H) : MulAut C :=
  e.symm.trans ((MulAut.conjNormal t).trans e)

theorem autK_apply (e : ↥K ≃* C) (t : H) (c : C) :
    autK e t c = e ⟨t * (e.symm c : H) * t⁻¹, ‹K.Normal›.conj_mem _ (e.symm c).2 t⟩ := rfl

theorem map_conj_pull (e : ↥K ≃* C) (t : H) (P : Subgroup C) :
    ((P.map e.symm.toMonoidHom).map K.subtype).map (MulAut.conj t).toMonoidHom =
      ((P.map (autK e t).toMonoidHom).map e.symm.toMonoidHom).map K.subtype := by
  simp only [Subgroup.map_map]
  congr 1
  ext c
  simp [autK_apply]

theorem mem_normalizer_pull (e : ↥K ≃* C) {t : H} {P : Subgroup C}
    (h : P.map (autK e t).toMonoidHom = P) :
    t ∈ Subgroup.normalizer (((P.map e.symm.toMonoidHom).map K.subtype : Subgroup H) :
      Set H) := by
  have h2 : ((P.map e.symm.toMonoidHom).map K.subtype).map (MulAut.conj t).toMonoidHom =
      (P.map e.symm.toMonoidHom).map K.subtype := by
    rw [map_conj_pull, h]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

theorem map_autK_of_mem_normalizer (e : ↥K ≃* C) {t : H} {P : Subgroup C}
    (h : t ∈ Subgroup.normalizer (((P.map e.symm.toMonoidHom).map K.subtype : Subgroup H) :
      Set H)) : P.map (autK e t).toMonoidHom = P := by
  apply pull_injective e
  dsimp only
  have h2 : ((P.map e.symm.toMonoidHom).map K.subtype).map (MulAut.conj t).toMonoidHom =
      (P.map e.symm.toMonoidHom).map K.subtype := Subgroup.mem_normalizer_iff_map_conj_eq.mp h
  rw [← map_conj_pull, h2]

theorem map_autK_of_mem_normalizer' (e : ↥K ≃* C) {t : H} {Y : Subgroup H} (hYK : Y ≤ K)
    (h : t ∈ Subgroup.normalizer (Y : Set H)) :
    ((Y.subgroupOf K).map e.toMonoidHom).map (autK e t).toMonoidHom =
      (Y.subgroupOf K).map e.toMonoidHom := by
  apply map_autK_of_mem_normalizer e
  rwa [pull_map e hYK]

end Model

@[expose] def HasInvPair (Γ : Type) [Group Γ] : Prop :=
  ∃ U P₀ P₁ : Subgroup Γ, IsSylowTwoOf U ⊤ ∧ U ≤ P₀ ∧ U ≤ P₁ ∧ P₀ ≠ ⊤ ∧ P₁ ≠ ⊤ ∧
    P₀ ⊔ P₁ = ⊤ ∧ ∀ α : MulAut Γ, U.map α.toMonoidHom = U →
      P₀.map α.toMonoidHom = P₀ ∧ P₁.map α.toMonoidHom = P₁

theorem asc86bClauseB_of_hasInvPair {s : TauCeti.SporadicName} {Γ : Type} [Group Γ] [Finite Γ]
    (eΓ : CFSG.Blueprint.NativeSporadic.Carrier s ≃* Γ) (hP : HasInvPair Γ) :
    Asc86bClauseB s := by
  obtain ⟨U, P₀, P₁, hU, hU₀, hU₁, h₀, h₁, hgen, hinv⟩ := hP
  intro H _ _ K T hK hs _ hT hKT
  obtain ⟨e₀⟩ := hs
  have hSK : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_normal hT le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow (e₀.trans eΓ) hSK hU
  have hα : ∀ t ∈ T, U.map (autK e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact map_autK_of_mem_normalizer' e' inf_le_right (le_normalizer_inf hK ht)
  have hS : ∀ {P : Subgroup Γ}, U ≤ P → T ⊓ K ≤ (P.map e'.symm.toMonoidHom).map K.subtype :=
    fun hUP => (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
  exact exists_two_max hKT (pull_le e' P₀) (pull_le e' P₁) (hS hU₀) (hS hU₁)
    (pull_ne e' h₀) (pull_ne e' h₁)
    (fun t ht => mem_normalizer_pull e' (hinv _ (hα t ht)).1)
    (fun t ht => mem_normalizer_pull e' (hinv _ (hα t ht)).2)
    (by rw [← pull_sup, hgen, pull_top])

theorem asc86bClauseB_of_inner {s : TauCeti.SporadicName} {Γ : Type} [Group Γ] [Finite Γ]
    (eΓ : CFSG.Blueprint.NativeSporadic.Carrier s ≃* Γ)
    (hin : ∀ α : MulAut Γ, ∃ g : Γ, α = MulAut.conj g) {U P₀ P₁ : Subgroup Γ}
    (hU : IsSylowTwoOf U ⊤) (hU₀ : U ≤ P₀) (hU₁ : U ≤ P₁) (h₀ : P₀ ≠ ⊤) (h₁ : P₁ ≠ ⊤)
    (hgen : P₀ ⊔ P₁ = ⊤) : Asc86bClauseB s := by
  intro H _ _ K T hK hs hC hT hKT
  obtain ⟨e₀⟩ := hs
  have := hK
  set e : ↥K ≃* Γ := e₀.trans eΓ with he
  have hHK : ∀ h : H, h ∈ K := by
    intro h
    obtain ⟨g, hg⟩ := hin (autK e h)
    set k : ↥K := e.symm g with hk
    have key : ∀ y ∈ K, h * y * h⁻¹ = (k : H) * y * (k : H)⁻¹ := by
      intro y hy
      have h1 : autK e h (e ⟨y, hy⟩) = MulAut.conj g (e ⟨y, hy⟩) := by rw [hg]
      have h2 := congrArg (fun c => (e.symm c : H)) h1
      simpa [autK_apply, hk] using h2
    have hc : (k : H)⁻¹ * h ∈ Subgroup.centralizer (K : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := key y hy
      calc y * ((k : H)⁻¹ * h) = (k : H)⁻¹ * ((k : H) * y * (k : H)⁻¹) * h := by group
        _ = (k : H)⁻¹ * (h * y * h⁻¹) * h := by rw [this]
        _ = (k : H)⁻¹ * h * y := by group
    rw [hC, Subgroup.mem_bot] at hc
    have : h = k := by
      calc h = (k : H) * ((k : H)⁻¹ * h) := by group
        _ = k := by rw [hc, mul_one]
    rw [this]
    exact k.2
  have hTK : T ≤ K := fun x _ => hHK x
  have hSK : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_normal hT le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e hSK hU
  have hS : ∀ {P : Subgroup Γ}, U ≤ P → T ⊓ K ≤ (P.map e'.symm.toMonoidHom).map K.subtype :=
    fun hUP => (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
  have hTn : ∀ {P : Subgroup Γ}, U ≤ P →
      T ≤ Subgroup.normalizer (((P.map e'.symm.toMonoidHom).map K.subtype : Subgroup H) :
        Set H) := fun hUP t ht =>
    Subgroup.le_normalizer (hS hUP ⟨ht, hTK ht⟩)
  exact exists_two_max hKT (pull_le e' P₀) (pull_le e' P₁) (hS hU₀) (hS hU₁)
    (pull_ne e' h₀) (pull_ne e' h₁) (hTn hU₀) (hTn hU₁)
    (by rw [← pull_sup, hgen, pull_top])

section Invariance

variable {Γ : Type} [Group Γ]

theorem map_eq_of_unique_card {U P : Subgroup Γ} (hUP : U ≤ P)
    (huniq : ∀ Y : Subgroup Γ, U ≤ Y → Nat.card Y = Nat.card P → Y = P) (α : MulAut Γ)
    (hα : U.map α.toMonoidHom = U) : P.map α.toMonoidHom = P := by
  refine huniq _ ?_ (Subgroup.card_map_of_injective α.injective)
  rw [← hα]
  exact Subgroup.map_mono hUP

theorem map_inf_eq_of_pair {U P P' : Subgroup Γ} (hUP : U ≤ P) (hUP' : U ≤ P')
    (hcard : Nat.card P' = Nat.card P)
    (hpair : ∀ Y : Subgroup Γ, U ≤ Y → Nat.card Y = Nat.card P → Y = P ∨ Y = P')
    (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (P ⊓ P').map α.toMonoidHom = P ⊓ P' := by
  have hm : ∀ {Y : Subgroup Γ}, U ≤ Y → U ≤ Y.map α.toMonoidHom := fun h => by
    rw [← hα]
    exact Subgroup.map_mono h
  have hinj : Function.Injective (fun Y : Subgroup Γ => Y.map α.toMonoidHom) :=
    Subgroup.map_injective α.injective
  have h1 := hpair _ (hm hUP) (Subgroup.card_map_of_injective α.injective)
  have h2 := hpair _ (hm hUP') ((Subgroup.card_map_of_injective α.injective).trans hcard)
  rw [Subgroup.map_inf_eq _ _ _ α.injective]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
  · rw [show P = P' from hinj (h1.trans h2.symm)]
  · exact inf_comm _ _
  · rw [show P = P' from hinj (h1.trans h2.symm)]

theorem map_eq_of_center_pair {U P P' : Subgroup Γ} (hUP : U ≤ P) (hUP' : U ≤ P')
    (hcard : Nat.card P' = Nat.card P)
    (hpair : ∀ Y : Subgroup Γ, U ≤ Y → Nat.card Y = Nat.card P → Y = P ∨ Y = P')
    {z : Γ} (hzP : z ∈ P) (hz1 : z ≠ 1) (hz : ∀ x ∈ P, z * x = x * z)
    (hZ' : ∀ w ∈ P', (∀ x ∈ P', w * x = x * w) → w = 1) (α : MulAut Γ)
    (hα : U.map α.toMonoidHom = U) :
    P.map α.toMonoidHom = P ∧ P'.map α.toMonoidHom = P' := by
  have hm : ∀ {Y : Subgroup Γ}, U ≤ Y → U ≤ Y.map α.toMonoidHom := fun h => by
    rw [← hα]
    exact Subgroup.map_mono h
  have h1 := hpair _ (hm hUP) (Subgroup.card_map_of_injective α.injective)
  have h2 := hpair _ (hm hUP') ((Subgroup.card_map_of_injective α.injective).trans hcard)
  have hP : P.map α.toMonoidHom = P := by
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      apply hz1
      have hw : α z ∈ P' := by
        rw [← h1]
        exact Subgroup.mem_map_of_mem α.toMonoidHom hzP
      have hcen : ∀ x ∈ P', α z * x = x * α z := by
        intro x hx
        rw [← h1] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        show α z * α y = α y * α z
        rw [← map_mul α, ← map_mul α, hz y hy]
      exact α.injective ((hZ' (α z) hw hcen).trans (map_one α).symm)
  refine ⟨hP, ?_⟩
  rcases h2 with h2 | h2
  · have : P' = P := Subgroup.map_injective α.injective (h2.trans hP.symm)
    rw [this, hP]
  · exact h2

theorem hasInvPair_of_unique {U P₀ P₁ : Subgroup Γ} (hU : IsSylowTwoOf U ⊤) (hU₀ : U ≤ P₀)
    (hU₁ : U ≤ P₁) (h₀ : P₀ ≠ ⊤) (h₁ : P₁ ≠ ⊤)
    (hu₀ : ∀ Y : Subgroup Γ, U ≤ Y → Nat.card Y = Nat.card P₀ → Y = P₀)
    (hu₁ : ∀ Y : Subgroup Γ, U ≤ Y → Nat.card Y = Nat.card P₁ → Y = P₁)
    (hgen : P₀ ⊔ P₁ = ⊤) : HasInvPair Γ :=
  ⟨U, P₀, P₁, hU, hU₀, hU₁, h₀, h₁, hgen, fun α hα =>
    ⟨map_eq_of_unique_card hU₀ hu₀ α hα, map_eq_of_unique_card hU₁ hu₁ α hα⟩⟩

end Invariance

section Lat

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def latSz (L : Array ℕ) (N j : ℕ) : ℕ := if j < L.size then L[j]! else N

@[expose] def LatPairOK (L : Array ℕ) (N a b : ℕ) : Prop :=
  a < L.size ∧ b < L.size ∧ (∀ j < L.size + 1, latSz L N j = latSz L N a → j = a) ∧
    (∀ j < L.size + 1, latSz L N j = latSz L N b → j = b) ∧
    ∀ j < L.size, latSz L N a ∣ latSz L N j → ¬ latSz L N b ∣ latSz L N j

instance (L : Array ℕ) (N a b : ℕ) : Decidable (LatPairOK L N a b) := by
  unfold LatPairOK; infer_instance

@[expose] def LatMeetOK (L : Array ℕ) (N a c d : ℕ) : Prop :=
  a < L.size ∧ c < L.size ∧ d < L.size ∧
    (∀ j < L.size + 1, latSz L N j = latSz L N a → j = a) ∧ latSz L N c ≠ N ∧
    latSz L N d = latSz L N c ∧
    (∀ j < L.size + 1, latSz L N j = latSz L N c → j = c ∨ j = d) ∧
    ∀ j < L.size, latSz L N a ∣ latSz L N j → j = a

instance (L : Array ℕ) (N a c d : ℕ) : Decidable (LatMeetOK L N a c d) := by
  unfold LatMeetOK; infer_instance

section List

variable {Γ : Type} [Group Γ] {S : Subgroup Γ} {Y : ℕ → Subgroup Γ} {L : Array ℕ} {N k : ℕ}

theorem list_card (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k)
    (hΓ : Nat.card Γ = N * 2 ^ k) (j : ℕ) :
    Nat.card (memberOrTop L.size Y j) = latSz L N j * 2 ^ k := by
  unfold memberOrTop latSz
  by_cases hj : j < L.size
  · rw [ite_eq_left hj, ite_eq_left hj]
    exact hcard j hj
  · rw [ite_eq_right hj, ite_eq_right hj, Subgroup.card_top, hΓ]

theorem list_S_le (hSY : ∀ j < L.size, S ≤ Y j) (j : ℕ) : S ≤ memberOrTop L.size Y j := by
  unfold memberOrTop
  by_cases hj : j < L.size
  · rw [ite_eq_left hj]
    exact hSY j hj
  · rw [ite_eq_right hj]
    exact le_top

theorem list_unique (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k) (hΓ : Nat.card Γ = N * 2 ^ k)
    {a : ℕ} (hua : ∀ j < L.size + 1, latSz L N j = latSz L N a → j = a) (Z : Subgroup Γ)
    (hZ : S ≤ Z) (hZa : Nat.card Z = Nat.card (memberOrTop L.size Y a)) :
    Z = memberOrTop L.size Y a := by
  obtain ⟨j, hj, rfl⟩ := hall Z hZ
  rw [list_card hcard hΓ, list_card hcard hΓ] at hZa
  rw [hua j (Nat.lt_succ_of_le hj) (Nat.eq_of_mul_eq_mul_right (by positivity) hZa)]

theorem list_ne_top (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k)
    (hΓ : Nat.card Γ = N * 2 ^ k) {a : ℕ} (ha : a < L.size)
    (hua : ∀ j < L.size + 1, latSz L N j = latSz L N a → j = a) :
    memberOrTop L.size Y a ≠ ⊤ := by
  intro h
  have h1 := congrArg (fun Z : Subgroup Γ => Nat.card Z) h
  rw [list_card hcard hΓ, Subgroup.card_top, hΓ] at h1
  have h2 : latSz L N a = N := Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have h3 : latSz L N L.size = latSz L N a := by
    rw [h2]
    unfold latSz
    rw [ite_eq_right (lt_irrefl _)]
  have h4 := hua L.size (Nat.lt_succ_self _) h3
  omega

theorem list_dvd_of_le (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k)
    (hΓ : Nat.card Γ = N * 2 ^ k) {a j : ℕ}
    (h : memberOrTop L.size Y a ≤ memberOrTop L.size Y j) : latSz L N a ∣ latSz L N j := by
  have := Subgroup.card_dvd_of_le h
  rw [list_card hcard hΓ, list_card hcard hΓ] at this
  exact Nat.dvd_of_mul_dvd_mul_right (by positivity) this

theorem list_member {a : ℕ} (ha : a < L.size) : memberOrTop L.size Y a = Y a := by
  unfold memberOrTop
  rw [ite_eq_left ha]

theorem hasInvPair_of_list (hS : IsSylowTwoOf S ⊤)
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hSY : ∀ j < L.size, S ≤ Y j) (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k)
    (hΓ : Nat.card Γ = N * 2 ^ k) {a b : ℕ} (hok : LatPairOK L N a b) : HasInvPair Γ := by
  obtain ⟨ha, hb, hua, hub, hjoin⟩ := hok
  refine hasInvPair_of_unique hS (list_S_le hSY a) (list_S_le hSY b)
    (list_ne_top hcard hΓ ha hua) (list_ne_top hcard hΓ hb hub) (list_unique hall hcard hΓ hua)
    (list_unique hall hcard hΓ hub) ?_
  obtain ⟨j, hj, hjZ⟩ := hall _ (le_sup_of_le_left (list_S_le hSY a) :
    S ≤ memberOrTop L.size Y a ⊔ memberOrTop L.size Y b)
  rw [hjZ]
  by_cases hjL : j < L.size
  · exfalso
    have ha := list_dvd_of_le hcard hΓ (le_sup_left.trans hjZ.le)
    have hb := list_dvd_of_le hcard hΓ (le_sup_right.trans hjZ.le)
    exact hjoin j hjL ha hb
  · unfold memberOrTop
    rw [ite_eq_right hjL]

theorem hasInvPair_of_list_meet (hS : IsSylowTwoOf S ⊤)
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hSY : ∀ j < L.size, S ≤ Y j) (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k)
    (hΓ : Nat.card Γ = N * 2 ^ k) {a c d m : ℕ} (hok : LatMeetOK L N a c d)
    (hmc : Y m ≤ Y c) (hmd : Y m ≤ Y d) (hma : ¬ Y m ≤ Y a) : HasInvPair Γ := by
  obtain ⟨ha, hc, hd, hua, hcN, hdc, hucd, hmax⟩ := hok
  rw [← list_member (Y := Y) ha] at hma
  rw [← list_member (Y := Y) hc] at hmc
  rw [← list_member (Y := Y) hd] at hmd
  have hcd : Nat.card (memberOrTop L.size Y d) = Nat.card (memberOrTop L.size Y c) := by
    rw [list_card hcard hΓ, list_card hcard hΓ, hdc]
  have hpair : ∀ Z : Subgroup Γ, S ≤ Z → Nat.card Z = Nat.card (memberOrTop L.size Y c) →
      Z = memberOrTop L.size Y c ∨ Z = memberOrTop L.size Y d := by
    intro Z hZ hZc
    obtain ⟨j, hj, rfl⟩ := hall Z hZ
    rw [list_card hcard hΓ, list_card hcard hΓ] at hZc
    rcases hucd j (Nat.lt_succ_of_le hj) (Nat.eq_of_mul_eq_mul_right (by positivity) hZc) with
      rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hYc : memberOrTop L.size Y c ≠ ⊤ := by
    intro h
    have h1 := congrArg (fun Z : Subgroup Γ => Nat.card Z) h
    rw [list_card hcard hΓ, Subgroup.card_top, hΓ] at h1
    exact hcN (Nat.eq_of_mul_eq_mul_right (by positivity) h1)
  refine ⟨S, memberOrTop L.size Y a, memberOrTop L.size Y c ⊓ memberOrTop L.size Y d, hS,
    list_S_le hSY a, le_inf (list_S_le hSY c) (list_S_le hSY d), list_ne_top hcard hΓ ha hua,
    fun h => hYc (eq_top_iff.mpr (h.symm.le.trans inf_le_left)), ?_,
    fun α hα => ⟨map_eq_of_unique_card (list_S_le hSY a) (list_unique hall hcard hΓ hua) α hα,
      map_inf_eq_of_pair (list_S_le hSY c) (list_S_le hSY d) hcd hpair α hα⟩⟩
  obtain ⟨j, hj, hjZ⟩ := hall _ (le_sup_of_le_left (list_S_le hSY a) :
    S ≤ memberOrTop L.size Y a ⊔ (memberOrTop L.size Y c ⊓ memberOrTop L.size Y d))
  rw [hjZ]
  by_cases hjL : j < L.size
  · exfalso
    have hja : j = a := hmax j hjL (list_dvd_of_le hcard hΓ (le_sup_left.trans hjZ.le))
    rw [hja] at hjZ
    exact hma ((le_inf hmc hmd).trans (le_sup_right.trans hjZ.le))
  · unfold memberOrTop
    rw [ite_eq_right hjL]

end List

section Ctx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] {Lab : Type}
  [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem lat_J_eq (C : LatCtx Γ n Lab) {L : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = L) : C.J = L.size := by
  have h2 : C.D.Om.size = C.D.mw.size := C.membersOK.2.2.2.1
  have h3 : L.size = C.D.Om.size := by rw [← hL, Array.size_map]
  show C.D.mw.size = L.size
  omega

theorem lat_all (C : LatCtx Γ n Lab) {L : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = L) :
    ∀ Z : Subgroup Γ, C.S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size C.Y j := by
  intro Z hZ
  obtain ⟨j, hj, hZj⟩ := C.complete Z hZ
  rw [lat_J_eq C hL] at hj hZj
  exact ⟨j, hj, hZj⟩

theorem lat_card (C : LatCtx Γ n Lab) {L : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = L) :
    ∀ j < L.size, Nat.card (C.Y j) = L[j]! * 2 ^ C.k := by
  intro j hj
  rw [C.Y_card (by rw [lat_J_eq C hL]; exact hj)]
  subst hL
  have hj' : j < C.D.Om.size := by simpa using hj
  rw [getElem!_pos C.D.Om j hj', getElem!_pos _ j hj, Array.getElem_map]

theorem hasInvPair_of_lat (C : LatCtx Γ n Lab) (hS : IsSylowTwoOf C.S ⊤) {L : Array ℕ} {N : ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = L) (hN : C.D.O.lbl.size = N) {a b : ℕ}
    (hok : LatPairOK L N a b) : HasInvPair Γ :=
  hasInvPair_of_list hS (lat_all C hL) (fun j hj => C.S_le_Y j) (lat_card C hL)
    (by rw [C.hΓ, hN]) hok

theorem hasInvPair_of_lat_meet (C : LatCtx Γ n Lab) (hS : IsSylowTwoOf C.S ⊤) {L : Array ℕ}
    {N : ℕ} (hL : C.D.Om.map (fun o => o.lbl.size) = L) (hN : C.D.O.lbl.size = N)
    {a c d m : ℕ} (hok : LatMeetOK L N a c d) (hmc : C.Y m ≤ C.Y c) (hmd : C.Y m ≤ C.Y d)
    (hma : ¬ C.Y m ≤ C.Y a) : HasInvPair Γ :=
  hasInvPair_of_list_meet hS (lat_all C hL) (fun j hj => C.S_le_Y j) (lat_card C hL)
    (by rw [C.hΓ, hN]) hok hmc hmd hma

end Ctx

end Lat

end SporB

end E2P

end CFSG.Quasithin
