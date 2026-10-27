module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.StatementsFSU
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem conjClosure_eq_self_of_normalizes {K T : Subgroup G}
    (h : T ≤ Subgroup.normalizer (K : Set G)) : conjClosure K T = K :=
  le_antisymm (conjClosure_le fun _ ht k hk => (Subgroup.mem_normalizer_iff.1 (h ht) k).1 hk)
    (le_conjClosure K T)

section Action

variable {K V : Subgroup G} [IsMulCommutative ↥V]

theorem fixV_autOn_eq (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    fixV (autOn K V) = (Subgroup.centralizer (K : Set G)).subgroupOf V :=
  CFSG.Quasithin.AutOn.fixV_autOn_eq hKV

theorem fixV_autOn_eq_bot_iff (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    fixV (autOn K V) = ⊥ ↔ V ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  rw [fixV_autOn_eq hKV]
  constructor
  · intro h
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxC⟩
    have : (⟨x, hxV⟩ : ↥V) ∈ (Subgroup.centralizer (K : Set G)).subgroupOf V := hxC
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · intro h
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have : (x : G) ∈ V ⊓ Subgroup.centralizer (K : Set G) := ⟨x.2, hx⟩
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this

theorem commV_autOn_eq_top (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hc : ⁅V, K⁆ = V) :
    commV (autOn K V) = ⊤ :=
  CFSG.Quasithin.AutOn.commV_autOn_eq_top hKV hc

omit [IsMulCommutative ↥V] in
theorem le_normalizer_map_of_invariant (hKV : K ≤ Subgroup.normalizer (V : Set G))
    {W : Subgroup ↥V} (hW : ∀ h ∈ autOn K V, ∀ w ∈ W, (h : MulAut ↥V) w ∈ W) :
    K ≤ Subgroup.normalizer ((W.map V.subtype : Subgroup G) : Set G) := by
  have key : ∀ k ∈ K, ∀ x ∈ W.map V.subtype, k * x * k⁻¹ ∈ W.map V.subtype := by
    rintro k hk _ ⟨w, hw, rfl⟩
    have hmem : A4.actionOn V K hKV ⟨k, hk⟩ ∈ autOn K V := (A4.mem_autOn_iff hKV).mpr ⟨⟨k, hk⟩, rfl⟩
    refine ⟨_, hW _ hmem w hw, ?_⟩
    rw [Subgroup.subtype_apply, A4.actionOn_apply_coe]
    rfl
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key k hk x
  · intro hx
    have := key k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using this

omit [IsMulCommutative ↥V] in
theorem nonempty_autOn_mulEquiv_of_simple {Γ : Type*} [Group Γ] [IsSimpleGroup Γ]
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (V : Set G)) (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Γ) :
    Nonempty (↥(autOn K V) ≃* Γ) := by
  set α : ↥K →* MulAut ↥V := A4.actionOn V K hKV with hα
  have hrange : α.range = autOn K V := by
    ext a
    rw [MonoidHom.mem_range, A4.mem_autOn_iff hKV]
  set α' : ↥K →* ↥(autOn K V) := α.codRestrict (autOn K V) fun k => hrange ▸ ⟨k, rfl⟩
  have hα'surj : Function.Surjective α' := by
    rintro ⟨a, ha⟩
    obtain ⟨k, rfl⟩ := (A4.mem_autOn_iff hKV).mp ha
    exact ⟨k, rfl⟩
  have hker : CFSG.pCore 2 ↥K ≤ α'.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show α k = 1
    rw [hα, A4.actionOn_eq_one_iff]
    apply hO2
    exact ⟨k, hk, rfl⟩
  set β : Γ →* ↥(autOn K V) :=
    (QuotientGroup.lift (CFSG.pCore 2 ↥K) α' hker).comp e.symm.toMonoidHom with hβ
  have hβsurj : Function.Surjective β := by
    intro a
    obtain ⟨k, rfl⟩ := hα'surj a
    exact ⟨e (k : ↥K ⧸ CFSG.pCore 2 ↥K), by simp [hβ]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal β.ker with h | h
  · exact ⟨(MulEquiv.ofBijective β ⟨(MonoidHom.ker_eq_bot_iff β).mp h, hβsurj⟩).symm⟩
  · exfalso
    apply hne
    intro k hk
    have h1 : α' ⟨k, hk⟩ = 1 := by
      obtain ⟨g, hg⟩ := hβsurj (α' ⟨k, hk⟩)
      rw [← hg]
      exact (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top g)
    have h2 : α ⟨k, hk⟩ = 1 := congrArg Subtype.val h1
    rw [hα, A4.actionOn_eq_one_iff] at h2
    exact h2

end Action

section Invariant

variable {K V : Subgroup G}

theorem invariant_subgroupOf_of_le_normalizer (hKV : K ≤ Subgroup.normalizer (V : Set G))
    {W : Subgroup G} (hKW : K ≤ Subgroup.normalizer (W : Set G)) :
    ∀ h ∈ autOn K V, ∀ w ∈ W.subgroupOf V, (h : MulAut ↥V) w ∈ W.subgroupOf V := by
  intro h hh w hw
  obtain ⟨⟨k, hk⟩, rfl⟩ := (A4.mem_autOn_iff hKV).mp hh
  rw [Subgroup.mem_subgroupOf, A4.actionOn_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp (hKW hk) _).mp (Subgroup.mem_subgroupOf.mp hw)

end Invariant

theorem conjugate_eq_self_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : CFSG.conjugate H g = H := by
  ext x
  simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff''.mp hg y).mp hy
  · intro hx
    refine ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp hx, ?_⟩
    group

theorem autOn_sup_eq_sup_autOn {H K V : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (hK : K ≤ Subgroup.normalizer (V : Set G)) : autOn (H ⊔ K) V = autOn H V ⊔ autOn K V :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hH hK

theorem autOn_le_normalizer_autOn {L T V : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hT : T ≤ Subgroup.normalizer (V : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    autOn T V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hTL

section Sylow

variable [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_of_quasithinIsSylowTwo {T H : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTH : T ≤ H) : QuasithinUnique.IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩

theorem pCoreOf_le_of_le_normalizer {T I : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTI : T ≤ Subgroup.normalizer (I : Set G)) : pCoreOf 2 I ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hT
  have hTP : T ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
    hTI.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 I)
  have hsup : IsPGroup 2 ↥(T ⊔ pCoreOf 2 I) :=
    IsPGroup.to_sup_of_normal_right' (hS ▸ S.isPGroup') (LieType.BorelTits.pCoreOf_isPGroup 2 I)
      hTP
  have hmax : T ⊔ pCoreOf 2 I = T := by
    have := S.is_maximal' hsup (by rw [hS]; exact le_sup_left)
    rwa [hS] at this
  rw [← hmax]
  exact le_sup_right

theorem reducedAggregate_le_pCoreOf (X : Subgroup G) : reducedAggregate X ≤ pCoreOf 2 X := by
  unfold reducedAggregate pCoreOf
  apply Subgroup.map_mono
  exact le_pCore_of_isPrimeReduced (isPrimeReduced_primeReducedAggregate 2)

theorem pCoreOf_le_centralizer_of_isPrimeReduced_sup {L T V : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hVLT : V ≤ L ⊔ T)
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) :
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
  have hE : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (sup_le Subgroup.le_normalizer hTL).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hle : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.map_subtype_le _).trans le_sup_left) hE (LieType.BorelTits.pCoreOf_isPGroup 2 L)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hle hx
  have hy' : y ∈ CFSG.pCore 2 ↥(L ⊔ T) := by assumption
  have hyc := pCore_le_centralizer_of_isPrimeReduced hred hy'
  rw [Subgroup.mem_centralizer_iff] at hyc ⊢
  intro v hv
  exact congrArg Subtype.val (hyc ⟨v, hVLT hv⟩ hv)

end Sylow

end CFSG.Quasithin.H13
