module

public import CFSG.Quasithin.Background.E2TwoProofDefs
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique B6

namespace E2P

section Inj

variable {G G' : Type} [Group G] [Group G'] {f : G →* G'}

theorem mem_normalizer_map_iff_of_injective (hf : Function.Injective f) {P : Subgroup G}
    {g : G} :
    f g ∈ Subgroup.normalizer (P.map f : Set G') ↔ g ∈ Subgroup.normalizer (P : Set G) := by
  simp only [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h (f x)
    rw [← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hf,
      Subgroup.mem_map_iff_mem hf] at this
    exact this
  · intro h y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g * x * g⁻¹, (h x).mp hx, by simp⟩
    · rintro ⟨z, hz, hzy⟩
      have hy : y = f (g⁻¹ * z * g) := by
        rw [map_mul, map_mul, map_inv, hzy]
        group
      rw [hy]
      refine ⟨g⁻¹ * z * g, (h _).mpr ?_, rfl⟩
      simpa [mul_assoc] using hz

theorem exists_mul_of_mem_sup_of_le_normalizer' {N T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ T) :
    ∃ n ∈ N, ∃ t ∈ T, n * t = x := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left N T hT
  have hx' : x ∈ ((N ⊔ T : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨n, hn, t, ht, rfl⟩ := hx'
  exact ⟨n, hn, t, ht, rfl⟩

theorem isSylowTwoOf_map_top_equiv {Γ : Type} [Group Γ] {K S : Subgroup Γ} (e : ↥K ≃* G)
    (hS : IsSylowTwoOf S K) : IsSylowTwoOf ((S.subgroupOf K).map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · have hS2 : IsPGroup 2 (S.subgroupOf K) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    exact hS2.map _
  · have e1 : (((S.subgroupOf K).map e.toMonoidHom).subgroupOf ⊤).index =
        ((S.subgroupOf K).map e.toMonoidHom).index := Subgroup.relIndex_top_right _
    rw [e1]
    have h := Subgroup.index_map_equiv (S.subgroupOf K) e
    rw [show (S.subgroupOf K).map e.toMonoidHom = (S.subgroupOf K).map (e : ↥K →* G) from rfl, h]
    exact hS.2.2

end Inj

section Pull

variable {X : Type} [Group X] {K T : Subgroup X} {C : Type} [Group C]

theorem pull_le (e : ↥K ≃* C) (P : Subgroup C) : (P.map e.symm.toMonoidHom).map K.subtype ≤ K := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem pull_top (e : ↥K ≃* C) : ((⊤ : Subgroup C).map e.symm.toMonoidHom).map K.subtype = K := by
  rw [Subgroup.map_top_of_surjective _ e.symm.surjective, Subgroup.map_top, Subgroup.range_subtype]

theorem pull_injective (e : ↥K ≃* C) :
    Function.Injective fun P : Subgroup C => (P.map e.symm.toMonoidHom).map K.subtype :=
  fun _ _ h => Subgroup.map_injective e.symm.injective
    (Subgroup.map_injective K.subtype_injective h)

theorem pull_ne (e : ↥K ≃* C) {P : Subgroup C} (hP : P ≠ ⊤) :
    (P.map e.symm.toMonoidHom).map K.subtype ≠ K := fun h =>
  hP (pull_injective e (h.trans (pull_top e).symm))

theorem pull_sup (e : ↥K ≃* C) (P Q : Subgroup C) :
    ((P ⊔ Q).map e.symm.toMonoidHom).map K.subtype =
      (P.map e.symm.toMonoidHom).map K.subtype ⊔ (Q.map e.symm.toMonoidHom).map K.subtype := by
  rw [Subgroup.map_sup, Subgroup.map_sup]

theorem pull_inf (e : ↥K ≃* C) (P Q : Subgroup C) :
    ((P ⊓ Q).map e.symm.toMonoidHom).map K.subtype =
      (P.map e.symm.toMonoidHom).map K.subtype ⊓ (Q.map e.symm.toMonoidHom).map K.subtype := by
  rw [Subgroup.map_inf _ _ _ e.symm.injective, Subgroup.map_inf _ _ _ K.subtype_injective]

theorem pull_mono (e : ↥K ≃* C) {P Q : Subgroup C} (h : P ≤ Q) :
    (P.map e.symm.toMonoidHom).map K.subtype ≤ (Q.map e.symm.toMonoidHom).map K.subtype :=
  Subgroup.map_mono (Subgroup.map_mono h)

theorem le_pull_iff (e : ↥K ≃* C) {Y : Subgroup X} (hYK : Y ≤ K) {P : Subgroup C} :
    Y ≤ (P.map e.symm.toMonoidHom).map K.subtype ↔ (Y.subgroupOf K).map e.toMonoidHom ≤ P := by
  constructor
  · rintro h _ ⟨y, hy, rfl⟩
    obtain ⟨z, ⟨w, hw, rfl⟩, hz⟩ := h hy
    have : e.symm w = y := Subtype.ext hz
    rw [← this]
    simpa using hw
  · intro h y hy
    refine ⟨⟨y, hYK hy⟩, ⟨e ⟨y, hYK hy⟩, h ⟨⟨y, hYK hy⟩, hy, rfl⟩, by simp⟩, rfl⟩

theorem map_pull (e : ↥K ≃* C) (P : Subgroup C) :
    (((P.map e.symm.toMonoidHom).map K.subtype).subgroupOf K).map e.toMonoidHom = P := by
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective,
    Subgroup.map_map]
  convert Subgroup.map_id P
  ext c
  simp

theorem pull_normalizer (e : ↥K ≃* C) :
    ((Subgroup.normalizer ((((T ⊓ K).subgroupOf K).map e.toMonoidHom : Subgroup C) :
      Set C)).map e.symm.toMonoidHom).map K.subtype =
      K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) := by
  ext x
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨(e.symm c).2, ?_⟩
    have h1 : e (e.symm c) ∈ Subgroup.normalizer
        ((((T ⊓ K).subgroupOf K).map e.toMonoidHom : Subgroup C) : Set C) := by simpa using hc
    have h2 := (mem_normalizer_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp h1
    have h3 := (mem_normalizer_map_iff_of_injective (f := K.subtype) K.subtype_injective).mpr h2
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h3
  · rintro ⟨hxK, hxN⟩
    refine ⟨⟨x, hxK⟩, ⟨e ⟨x, hxK⟩, ?_, by simp⟩, rfl⟩
    have h3 : K.subtype ⟨x, hxK⟩ ∈ Subgroup.normalizer
        ((((T ⊓ K).subgroupOf K).map K.subtype : Subgroup X) : Set X) := by
      rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    have h2 := (mem_normalizer_map_iff_of_injective (f := K.subtype) K.subtype_injective).mp h3
    exact (mem_normalizer_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr h2

theorem pull_map (e : ↥K ≃* C) {Y : Subgroup X} (hYK : Y ≤ K) :
    (((Y.subgroupOf K).map e.toMonoidHom).map e.symm.toMonoidHom).map K.subtype = Y := by
  rw [Subgroup.map_map, Subgroup.map_map]
  have : (K.subtype.comp e.symm.toMonoidHom).comp e.toMonoidHom = K.subtype := by
    ext x
    simp
  rw [this, Subgroup.map_subgroupOf_eq_of_le hYK]

end Pull

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

namespace ASHyp

variable (hX : ASHyp K T M)
include hX

theorem M_ne_top : M ≠ ⊤ := hX.minPar.maximal.1.ne

theorem mem_normalizer_K (x : X) : x ∈ Subgroup.normalizer (K : Set X) := by
  have := hX.normal
  rw [Subgroup.normalizer_eq_top_iff.mpr this]
  trivial

theorem isSylow_inf : IsSylowTwoOf (T ⊓ K) K :=
  isSylowTwoOf_inf_normal hX.minPar.isSylow le_top fun x _ => hX.mem_normalizer_K x

theorem le_normalizer_inf : T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hK := Subgroup.mem_normalizer_iff.mp (hX.mem_normalizer_K t) x
  constructor
  · rintro ⟨hxT, hxK⟩
    exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), hK.mp hxK⟩
  · rintro ⟨hxT, hxK⟩
    refine ⟨?_, hK.mpr hxK⟩
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
    simpa [mul_assoc] using this

theorem le_M_of_normalized {Y : Subgroup X} (hYK : Y ≤ K) (hSY : T ⊓ K ≤ Y) (hY : Y ≠ K)
    (hT : T ≤ Subgroup.normalizer (Y : Set X)) : Y ≤ M := by
  have hZK : (Y ⊔ T) ⊓ K ≤ Y := by
    rintro x ⟨hxZ, hxK⟩
    obtain ⟨y, hy, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hT hxZ
    have htK : t ∈ K := by
      have := K.mul_mem (K.inv_mem (hYK hy)) hxK
      simpa using this
    exact Y.mul_mem hy (hSY ⟨ht, htK⟩)
  have hZ : Y ⊔ T ≠ ⊤ := by
    intro h
    apply hY
    apply le_antisymm hYK
    rw [h, top_inf_eq] at hZK
    exact hZK
  exact le_sup_left.trans (hX.minPar.le_of_lt le_sup_right (lt_top_iff_ne_top.mpr hZ))

theorem false_of_pair {P₁ P₂ : Subgroup X} (h₁K : P₁ ≤ K) (h₂K : P₂ ≤ K) (hS₁ : T ⊓ K ≤ P₁)
    (hS₂ : T ⊓ K ≤ P₂) (h₁ : P₁ ≠ K) (h₂ : P₂ ≠ K) (hT₁ : T ≤ Subgroup.normalizer (P₁ : Set X))
    (hT₂ : T ≤ Subgroup.normalizer (P₂ : Set X)) (hgen : K ≤ P₁ ⊔ P₂) : False := by
  have hKM : K ≤ M := hgen.trans (sup_le (hX.le_M_of_normalized h₁K hS₁ h₁ hT₁)
    (hX.le_M_of_normalized h₂K hS₂ h₂ hT₂))
  apply hX.M_ne_top
  rw [eq_top_iff, ← hX.sup]
  exact sup_le hKM hX.minPar.le

theorem even_card : Even (Nat.card K) := by
  by_contra hodd
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard K (Nat.not_even_iff_odd.mp hodd)
  have := hX.simple
  obtain ⟨a, b, hab⟩ := hX.nonab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)

theorem inf_ne_bot : T ⊓ K ≠ ⊥ := by
  intro h
  have hS := hX.isSylow_inf
  rw [h] at hS
  have h1 : ((⊥ : Subgroup X).subgroupOf K).index = Nat.card K := by
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
  have h2 := hS.2.2
  rw [h1] at h2
  exact h2 (even_iff_two_dvd.mp hX.even_card)

theorem normalizer_ne : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) ≠ K := by
  intro h
  have hle : K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) := fun x hx => by
    have : x ∈ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) := by rw [h]; exact hx
    exact this.2
  have hn : ((T ⊓ K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_right : T ⊓ K ≤ K)).mpr hle
  have := hX.simple
  rcases hn.eq_bot_or_eq_top with hb | ht
  · apply hX.inf_ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : ↥K) ∈ (T ⊓ K).subgroupOf K := hx
    rw [hb, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  ·
    have hKS : K ≤ T ⊓ K := by
      intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ (T ⊓ K).subgroupOf K := by rw [ht]; trivial
      exact this
    have h2 : IsPGroup 2 K := by
      have h := hX.isSylow_inf.2.1
      intro x
      obtain ⟨n, hn⟩ := h ⟨x, hKS x.2⟩
      exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent K := h2.isNilpotent
    obtain ⟨a, b, hab⟩ := hX.nonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance) a b)

theorem le_normalizer_normalizer :
    T ≤ Subgroup.normalizer ((K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) :
      Subgroup X) : Set X) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hK := Subgroup.mem_normalizer_iff.mp (hX.mem_normalizer_K t) x
  have htS := hX.le_normalizer_inf ht
  set N := Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X)
  constructor
  · rintro ⟨hxK, hxN⟩
    exact ⟨hK.mp hxK, N.mul_mem (N.mul_mem htS hxN) (N.inv_mem htS)⟩
  · rintro ⟨hxK, hxN⟩
    refine ⟨hK.mpr hxK, ?_⟩
    have := N.mul_mem (N.mul_mem (N.inv_mem htS) hxN) htS
    simpa [mul_assoc] using this

theorem normalizer_le_M : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) ≤ M :=
  hX.le_M_of_normalized inf_le_left (le_inf inf_le_right Subgroup.le_normalizer)
    hX.normalizer_ne hX.le_normalizer_normalizer

theorem inf_M_ne : M ⊓ K ≠ K := by
  intro h
  have hKM : K ≤ M := by
    rw [← h]
    exact inf_le_left
  apply hX.M_ne_top
  rw [eq_top_iff, ← hX.sup]
  exact sup_le hKM hX.minPar.le

theorem le_normalizer_inf_M : T ≤ Subgroup.normalizer ((M ⊓ K : Subgroup X) : Set X) := by
  intro t ht
  have htM : t ∈ M := hX.minPar.le ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hK := Subgroup.mem_normalizer_iff.mp (hX.mem_normalizer_K t) x
  constructor
  · rintro ⟨hxM, hxK⟩
    exact ⟨M.mul_mem (M.mul_mem htM hxM) (M.inv_mem htM), hK.mp hxK⟩
  · rintro ⟨hxM, hxK⟩
    refine ⟨?_, hK.mpr hxK⟩
    have := M.mul_mem (M.mul_mem (M.inv_mem htM) hxM) htM
    simpa [mul_assoc] using this

theorem inf_le_inf_M : T ⊓ K ≤ M ⊓ K := inf_le_inf_right K hX.minPar.le

section Model

variable {C : Type} [Group C]

@[expose] noncomputable def autC (e : ↥K ≃* C) (t : X) : MulAut C :=
  haveI := hX.normal
  e.symm.trans ((MulAut.conjNormal t).trans e)

theorem autC_apply (e : ↥K ≃* C) (t : X) (c : C) :
    hX.autC e t c = e ⟨t * (e.symm c : X) * t⁻¹, hX.normal.conj_mem _ (e.symm c).2 t⟩ := rfl

theorem map_conj_pull (e : ↥K ≃* C) (t : X) (P : Subgroup C) :
    ((P.map e.symm.toMonoidHom).map K.subtype).map (MulAut.conj t).toMonoidHom =
      ((P.map (hX.autC e t).toMonoidHom).map e.symm.toMonoidHom).map K.subtype := by
  simp only [Subgroup.map_map]
  congr 1
  ext c
  simp [autC_apply]

theorem mem_normalizer_pull (e : ↥K ≃* C) {t : X} {P : Subgroup C}
    (h : P.map (hX.autC e t).toMonoidHom = P) :
    t ∈ Subgroup.normalizer (((P.map e.symm.toMonoidHom).map K.subtype : Subgroup X) : Set X) := by
  have h2 : ((P.map e.symm.toMonoidHom).map K.subtype).map (MulAut.conj t).toMonoidHom =
      (P.map e.symm.toMonoidHom).map K.subtype := by
    rw [hX.map_conj_pull, h]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

theorem normalizes_pull (e : ↥K ≃* C) {P : Subgroup C}
    (h : ∀ t ∈ T, P.map (hX.autC e t).toMonoidHom = P) :
    T ≤ Subgroup.normalizer (((P.map e.symm.toMonoidHom).map K.subtype : Subgroup X) : Set X) :=
  fun t ht => hX.mem_normalizer_pull e (h t ht)

theorem map_autC_of_mem_normalizer (e : ↥K ≃* C) {t : X} {P : Subgroup C}
    (h : t ∈ Subgroup.normalizer (((P.map e.symm.toMonoidHom).map K.subtype : Subgroup X) :
      Set X)) : P.map (hX.autC e t).toMonoidHom = P := by
  apply pull_injective e
  dsimp only
  have h2 : ((P.map e.symm.toMonoidHom).map K.subtype).map (MulAut.conj t).toMonoidHom =
      (P.map e.symm.toMonoidHom).map K.subtype := Subgroup.mem_normalizer_iff_map_conj_eq.mp h
  rw [← hX.map_conj_pull, h2]

theorem map_autC_of_mem_normalizer' (e : ↥K ≃* C) {t : X} {Y : Subgroup X} (hYK : Y ≤ K)
    (h : t ∈ Subgroup.normalizer (Y : Set X)) :
    ((Y.subgroupOf K).map e.toMonoidHom).map (hX.autC e t).toMonoidHom =
      (Y.subgroupOf K).map e.toMonoidHom := by
  apply hX.map_autC_of_mem_normalizer e
  rwa [pull_map e hYK]

theorem map_autC_sylow (e : ↥K ≃* C) {t : X} (ht : t ∈ T) :
    (((T ⊓ K).subgroupOf K).map e.toMonoidHom).map (hX.autC e t).toMonoidHom =
      ((T ⊓ K).subgroupOf K).map e.toMonoidHom :=
  hX.map_autC_of_mem_normalizer' e inf_le_right (hX.le_normalizer_inf ht)

theorem exists_equiv_sylow [Finite C] (e : ↥K ≃* C) {U : Subgroup C} (hU : IsSylowTwoOf U ⊤) :
    ∃ e' : ↥K ≃* C, ((T ⊓ K).subgroupOf K).map e'.toMonoidHom = U := by
  have hS := isSylowTwoOf_map_top_equiv e hX.isSylow_inf
  obtain ⟨g, -, hg⟩ := isSylowTwoOf_exists_conj hS hU
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hg]
  show _ = (((T ⊓ K).subgroupOf K).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_map]
  rfl

theorem false_of_invPair [Finite C] (e : ↥K ≃* C) {U P₀ P₁ : Subgroup C}
    (hU : IsSylowTwoOf U ⊤) (hU₀ : U ≤ P₀) (hU₁ : U ≤ P₁) (h₀ : P₀ ≠ ⊤) (h₁ : P₁ ≠ ⊤)
    (hgen : P₀ ⊔ P₁ = ⊤)
    (hinv : ∀ α : MulAut C, U.map α.toMonoidHom = U →
      P₀.map α.toMonoidHom = P₀ ∧ P₁.map α.toMonoidHom = P₁) : False := by
  obtain ⟨e', he'⟩ := hX.exists_equiv_sylow e hU
  have hα : ∀ t ∈ T, U.map (hX.autC e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact hX.map_autC_sylow e' ht
  have hS : ∀ {P : Subgroup C}, U ≤ P → T ⊓ K ≤ (P.map e'.symm.toMonoidHom).map K.subtype :=
    fun hUP => (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
  refine hX.false_of_pair (pull_le e' P₀) (pull_le e' P₁) (hS hU₀) (hS hU₁)
    (pull_ne e' h₀) (pull_ne e' h₁)
    (hX.normalizes_pull e' fun t ht => (hinv _ (hα t ht)).1)
    (hX.normalizes_pull e' fun t ht => (hinv _ (hα t ht)).2) ?_
  rw [← pull_sup, hgen, pull_top]

theorem rankTwo [Finite C] (e : ↥K ≃* C) {U P₀ P₁ : Subgroup C} (hU : IsSylowTwoOf U ⊤)
    (hU₀ : U ≤ P₀) (hU₁ : U ≤ P₁) (hne : P₀ ≠ P₁)
    (hco : ∀ Y : Subgroup C, U ≤ Y → (IsCoatom Y ↔ Y = P₀ ∨ Y = P₁))
    (hB : P₀ ⊓ P₁ ≤ Subgroup.normalizer (U : Set C)) :
    E2.IsDiagramNontrivial T K (T ⊓ K) ∧ E2.IsBorelIn K (M ⊓ K) := by
  obtain ⟨e', he'⟩ := hX.exists_equiv_sylow e hU
  have hα : ∀ t ∈ T, U.map (hX.autC e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact hX.map_autC_sylow e' ht
  have hc₀ : IsCoatom P₀ := (hco P₀ hU₀).mpr (Or.inl rfl)
  have hc₁ : IsCoatom P₁ := (hco P₁ hU₁).mpr (Or.inr rfl)
  have hcov : ∀ Y : Subgroup C, U ≤ Y → Y ≠ ⊤ → Y ≤ P₀ ∨ Y ≤ P₁ := by
    intro Y hUY hY
    obtain ⟨Z, hYZ, hZ⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.mpr hY)
    rcases (hco Z (hUY.trans hYZ)).mp hZ.isCoatom with rfl | rfl
    · exact Or.inl hYZ
    · exact Or.inr hYZ
  have hmapc : ∀ (α : MulAut C) (P : Subgroup C), IsCoatom P → IsCoatom (P.map α.toMonoidHom) :=
    fun α P hP => ((MulEquiv.mapSubgroup α).isCoatom_iff P).mpr hP
  have hperm : ∀ t ∈ T, (P₀.map (hX.autC e' t).toMonoidHom = P₀ ∧
      P₁.map (hX.autC e' t).toMonoidHom = P₁) ∨ (P₀.map (hX.autC e' t).toMonoidHom = P₁ ∧
      P₁.map (hX.autC e' t).toMonoidHom = P₀) := by
    intro t ht
    set α := hX.autC e' t
    have hinj : P₀.map α.toMonoidHom ≠ P₁.map α.toMonoidHom := fun h =>
      hne (Subgroup.map_injective α.injective h)
    have h0 := (hco _ (hα t ht ▸ Subgroup.map_mono hU₀)).mp (hmapc α _ hc₀)
    have h1 := (hco _ (hα t ht ▸ Subgroup.map_mono hU₁)).mp (hmapc α _ hc₁)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hinj
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (h0.trans h1.symm) hinj
  have hS : ∀ {P : Subgroup C}, U ≤ P → T ⊓ K ≤ (P.map e'.symm.toMonoidHom).map K.subtype :=
    fun hUP => (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
  by_cases hall : ∀ t ∈ T, P₀.map (hX.autC e' t).toMonoidHom = P₀
  · exfalso
    have hall₁ : ∀ t ∈ T, P₁.map (hX.autC e' t).toMonoidHom = P₁ := fun t ht => by
      rcases hperm t ht with h | h
      · exact h.2
      · exact absurd ((hall t ht).symm.trans h.1) hne
    refine hX.false_of_pair (pull_le e' P₀) (pull_le e' P₁) (hS hU₀) (hS hU₁)
      (pull_ne e' hc₀.1) (pull_ne e' hc₁.1) (hX.normalizes_pull e' hall)
      (hX.normalizes_pull e' hall₁) ?_
    rw [← pull_sup, hc₀.sup_eq_top_of_ne hc₁ hne, pull_top]
  push Not at hall
  obtain ⟨t₀, ht₀, hne₀⟩ := hall
  obtain ⟨hsw₀, hsw₁⟩ := (hperm t₀ ht₀).resolve_left fun h => hne₀ h.1
  have key : ∀ Y : Subgroup X, Y ≤ K → T ⊓ K ≤ Y → Y ≠ K →
      T ≤ Subgroup.normalizer (Y : Set X) → (Y.subgroupOf K).map e'.toMonoidHom ≤ P₀ ⊓ P₁ := by
    intro Y hYK hSY hY hTY
    have hUY : U ≤ (Y.subgroupOf K).map e'.toMonoidHom := by
      rw [← he']
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono K hSY)
    have hY' : (Y.subgroupOf K).map e'.toMonoidHom ≠ ⊤ := by
      intro h
      apply hY
      have h1 := pull_map e' hYK
      rw [h, pull_top] at h1
      exact h1.symm
    have hfix := hX.map_autC_of_mem_normalizer' e' hYK (hTY ht₀)
    rcases hcov _ hUY hY' with h | h
    · refine le_inf h ?_
      rw [← hfix, ← hsw₀]
      exact Subgroup.map_mono h
    · refine le_inf ?_ h
      rw [← hfix, ← hsw₁]
      exact Subgroup.map_mono h
  have hMK := key (M ⊓ K) inf_le_right hX.inf_le_inf_M hX.inf_M_ne hX.le_normalizer_inf_M
  have hMN : M ⊓ K ≤ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) := by
    rw [← pull_normalizer e', he']
    exact (le_pull_iff e' inf_le_right).mpr (hMK.trans hB)
  have hNM : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) ≤ M ⊓ K :=
    le_inf hX.normalizer_le_M inf_le_left
  refine ⟨?_, ⟨T ⊓ K, hX.isSylow_inf, le_antisymm hMN hNM⟩⟩
  intro P hP hBP hTP
  obtain ⟨⟨hPK, -⟩, hPne, hPmax⟩ := hP
  have hSP : T ⊓ K ≤ P := le_trans (le_inf inf_le_right Subgroup.le_normalizer) hBP
  have hP0 : P ≤ (P₀.map e'.symm.toMonoidHom).map K.subtype :=
    (le_pull_iff e' hPK).mpr ((key P hPK hSP hPne hTP).trans inf_le_left)
  have hQ0 : IsParabolic2 K ((P₀.map e'.symm.toMonoidHom).map K.subtype) := by
    refine ⟨pull_le e' P₀, T ⊓ K, hX.isSylow_inf, ?_⟩
    exact hNM.trans ((le_pull_iff e' inf_le_right).mpr (hMK.trans inf_le_left))
  have hPQ := hPmax _ hQ0 (pull_ne e' hc₀.1) hP0
  apply hne₀
  apply hX.map_autC_of_mem_normalizer e'
  rw [hPQ]
  exact hTP ht₀

end Model

end ASHyp

end E2P

end CFSG.Quasithin
