module

public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.StandardType

open CFSG.Open
open scoped commutatorElement

@[expose] def GGRootNormInner {K : Type*} [Group K] (R : Subgroup K) : Prop :=
  ∀ y : MulAut K, (∃ k : ℕ, y ^ 2 ^ k = 1) → R.map y.toMonoidHom = R →
    (∀ n ∈ Subgroup.normalizer (R : Set K),
      y n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (R : Set K))) →
    ∃ k : K, y = MulAut.conj k

@[expose] def GGRootNormNoCentral {K : Type*} [Group K] (R : Subgroup K) : Prop :=
  ∀ A B' : Subgroup K, R ≤ A → A ≤ B' → B' ≤ pCoreOf 2 (Subgroup.normalizer (R : Set K)) →
    Subgroup.normalizer (R : Set K) ≤ Subgroup.normalizer (A : Set K) →
    Subgroup.normalizer (R : Set K) ≤ Subgroup.normalizer (B' : Set K) →
    ⁅B', Subgroup.normalizer (R : Set K)⁆ ≤ A → B' ≤ A

@[expose] def GGRootNormInnerDiag {K : Type*} [Group K] (R : Subgroup K) (δ : MulAut K) :
    Prop :=
  R.map δ.toMonoidHom = R ∧
    ((⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) ⊔ Subgroup.zpowers δ).Normal ∧
    ∀ y : MulAut K, (∃ k : ℕ, y ^ 2 ^ k = 1) → R.map y.toMonoidHom = R →
      (∀ n ∈ Subgroup.normalizer (R : Set K),
        y n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (R : Set K))) →
      δ * y * δ⁻¹ * y⁻¹ ∈ pCoreOf 2
        ((Subgroup.normalizer (R : Set K)).map (MulAut.conj : K →* MulAut K) ⊔
          Subgroup.zpowers δ) →
      ∃ k : K, y = MulAut.conj k

namespace GGRootNorm

section PCore

variable {G : Type*} [Group G]

theorem pCoreOf_le (N : Subgroup G) : pCoreOf 2 N ≤ N :=
  Subgroup.map_subtype_le _

theorem isPGroup_pCoreOf (N : Subgroup G) : IsPGroup 2 (pCoreOf 2 N) :=
  (CFSG.BaerSuzuki.Helpers.pCore_isPGroup (G := N) 2).map N.subtype

theorem le_normalizer_pCoreOf (N : Subgroup G) :
    N ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  rintro n hn _ ⟨t, ht, rfl⟩
  exact ⟨⟨n, hn⟩ * t * ⟨n, hn⟩⁻¹,
    (CFSG.BaerSuzuki.Helpers.pCore_normal (G := N) 2).conj_mem t ht ⟨n, hn⟩, rfl⟩

theorem le_pCoreOf_of_normalized {T N : Subgroup G} (hTN : T ≤ N) (hT : IsPGroup 2 T)
    (hn : ∀ m ∈ N, ∀ t ∈ T, m * t * m⁻¹ ∈ T) : T ≤ pCoreOf 2 N := by
  have h1 : (T.subgroupOf N).Normal :=
    ⟨fun t ht m => hn m m.2 t ht⟩
  have h2 : IsPGroup 2 (T.subgroupOf N) :=
    hT.comap_of_injective N.subtype N.subtype_injective
  have h3 := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup h1 h2
  intro t ht
  exact ⟨⟨t, hTN ht⟩, h3 ht, rfl⟩

theorem pCoreOf_subgroupOf {H K : Subgroup G} (hHK : H ≤ K) :
    pCoreOf 2 (H.subgroupOf K) = (pCoreOf 2 H).subgroupOf K := by
  apply le_antisymm
  · intro t ht
    have hT : (pCoreOf 2 (H.subgroupOf K)).map K.subtype ≤ pCoreOf 2 H := by
      refine le_pCoreOf_of_normalized ?_ ?_ ?_
      · refine (Subgroup.map_mono (pCoreOf_le _)).trans ?_
        rw [Subgroup.subgroupOf_map_subtype]
        exact inf_le_left
      · exact (isPGroup_pCoreOf _).map K.subtype
      · rintro m hm _ ⟨t₀, ht₀, rfl⟩
        have hmem : (⟨m, hHK hm⟩ : K) ∈ H.subgroupOf K := hm
        exact ⟨⟨m, hHK hm⟩ * t₀ * ⟨m, hHK hm⟩⁻¹,
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf _ hmem) t₀).mp ht₀, rfl⟩
    exact hT ⟨t, ht, rfl⟩
  · refine le_pCoreOf_of_normalized (Subgroup.subgroupOf_mono K (pCoreOf_le H)) ?_ ?_
    · exact (isPGroup_pCoreOf H).comap_of_injective K.subtype K.subtype_injective
    · intro m hm t ht
      have hm' : (m : G) ∈ H := hm
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf H hm') (t : G)).mp ht

end PCore

section Stab

variable {K : Type*} [Group K]

def ggStab (R : Subgroup K) : Subgroup (MulAut K) where
  carrier := {a | ∀ x : K, a x ∈ R ↔ x ∈ R}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from by simp] at this
    exact this.symm

theorem mem_ggStab_iff {R : Subgroup K} {a : MulAut K} :
    a ∈ ggStab R ↔ R.map a.toMonoidHom = R := by
  constructor
  · intro ha
    ext x
    rw [Subgroup.mem_map_equiv]
    have := ha (a.symm x)
    rw [show a (a.symm x) = x from by simp] at this
    exact this.symm
  · intro h x
    have := (SetLike.ext_iff.mp h) (a x)
    rw [Subgroup.mem_map_equiv, show a.symm (a x) = x from by simp] at this
    exact this.symm

theorem innerAut_normal :
    ((⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K)).Normal := by
  refine ⟨fun a ha φ => ?_⟩
  obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp ha
  refine Subgroup.mem_map.mpr ⟨φ k, Subgroup.mem_top _, ?_⟩
  ext x
  simp [MulAut.conj_apply]

end Stab

section Induced

variable {G : Type*} [Group G] {K R : Subgroup G}

theorem coe_normalizerMonoidHom {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (k : K) :
    ((K.normalizerMonoidHom ⟨g, hg⟩ k : K) : G) = g * k * g⁻¹ := rfl

theorem normalizerMonoidHom_conj (k : K) :
    K.normalizerMonoidHom ⟨k, Subgroup.le_normalizer k.2⟩ = MulAut.conj k := by
  ext x
  rfl

theorem mem_normalizer_subgroupOf_iff (hRK : R ≤ K) (n : K) :
    n ∈ Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) ↔
      (n : G) ∈ Subgroup.normalizer (R : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hRK, Subgroup.mem_subgroupOf]

theorem normalizerMonoidHom_mem_ggStab {g : G} (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (hgR : g ∈ Subgroup.normalizer (R : Set G)) :
    K.normalizerMonoidHom ⟨g, hgK⟩ ∈ ggStab (R.subgroupOf K) := by
  intro x
  exact (Subgroup.mem_normalizer_iff.mp hgR x).symm

theorem mem_sup_centralizer_of_induced_inner {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    {k : K} (hk : K.normalizerMonoidHom ⟨y, hy⟩ = MulAut.conj k) :
    y ∈ K ⊔ Subgroup.centralizer (K : Set G) := by
  have hcent : (k : G)⁻¹ * y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 := congrArg (fun a : MulAut K => ((a ⟨c, hc⟩ : K) : G)) hk
    have h2 : y * c * y⁻¹ = (k : G) * c * (k : G)⁻¹ := h1
    calc c * ((k : G)⁻¹ * y) = (k : G)⁻¹ * ((k : G) * c * (k : G)⁻¹) * y := by group
      _ = (k : G)⁻¹ * (y * c * y⁻¹) * y := by rw [h2]
      _ = (k : G)⁻¹ * y * c := by group
  have := Subgroup.mul_mem_sup k.2 hcent
  simpa using this

end Induced

section Reduction

variable {G : Type*} [Group G] {K R Y : Subgroup G}
  (hRK : R ≤ K) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
  (hYR : Y ≤ Subgroup.normalizer (R : Set G)) (hY2 : IsPGroup 2 Y)
  (hNY : K ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Y : Set G))
include hRK hYK hYR hY2 hNY

theorem induced_isTwoPower {y : G} (hy : y ∈ Y) :
    ∃ k : ℕ, K.normalizerMonoidHom ⟨y, hYK hy⟩ ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hY2 ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have h1 : (⟨y, hYK hy⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  rw [← map_pow, h1, map_one]

theorem induced_map_eq {y : G} (hy : y ∈ Y) :
    (R.subgroupOf K).map (K.normalizerMonoidHom ⟨y, hYK hy⟩).toMonoidHom = R.subgroupOf K :=
  mem_ggStab_iff.mp (normalizerMonoidHom_mem_ggStab (hYK hy) (hYR hy))

theorem induced_commutes {y : G} (hy : y ∈ Y) :
    ∀ n ∈ Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K),
      K.normalizerMonoidHom ⟨y, hYK hy⟩ n * n⁻¹ ∈
        pCoreOf 2 (Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K)) := by
  intro n hn
  set N : Subgroup K := Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) with hN
  have hnG : (n : G) ∈ Subgroup.normalizer (R : Set G) :=
    (mem_normalizer_subgroupOf_iff hRK n).mp hn
  have hnY : (n : G) ∈ Subgroup.normalizer (Y : Set G) := hNY ⟨n.2, hnG⟩
  have hT : Y.subgroupOf K ⊓ N ≤ pCoreOf 2 N := by
    refine le_pCoreOf_of_normalized inf_le_right ?_ ?_
    · exact (hY2.comap_of_injective K.subtype K.subtype_injective).to_le inf_le_left
    · intro m hm t ht
      have hmG : (m : G) ∈ Subgroup.normalizer (R : Set G) :=
        (mem_normalizer_subgroupOf_iff hRK m).mp hm
      have hmY : (m : G) ∈ Subgroup.normalizer (Y : Set G) := hNY ⟨m.2, hmG⟩
      refine ⟨?_, N.mul_mem (N.mul_mem hm ht.2) (N.inv_mem hm)⟩
      show (m : G) * (t : G) * (m : G)⁻¹ ∈ Y
      exact (Subgroup.mem_normalizer_iff.mp hmY (t : G)).mp ht.1
  refine hT ⟨?_, ?_⟩
  · show y * (n : G) * y⁻¹ * (n : G)⁻¹ ∈ Y
    have h1 : (n : G) * y⁻¹ * (n : G)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hnY y⁻¹).mp (Y.inv_mem hy)
    have := Y.mul_mem hy h1
    simpa [mul_assoc] using this
  · refine N.mul_mem ?_ (N.inv_mem hn)
    refine (mem_normalizer_subgroupOf_iff hRK _).mpr ?_
    show y * (n : G) * y⁻¹ ∈ Subgroup.normalizer (R : Set G)
    exact (Subgroup.normalizer (R : Set G)).mul_mem
      ((Subgroup.normalizer (R : Set G)).mul_mem (hYR hy) hnG)
      ((Subgroup.normalizer (R : Set G)).inv_mem (hYR hy))

end Reduction

section InducedGroup

variable {G : Type*} [Group G] {K Y : Subgroup G}

variable (K Y) in
def inducedGroup : Subgroup (MulAut K) :=
  (Y.subgroupOf (Subgroup.normalizer (K : Set G))).map K.normalizerMonoidHom

theorem isPGroup_inducedGroup (hY2 : IsPGroup 2 Y) : IsPGroup 2 (inducedGroup K Y) :=
  (hY2.comap_of_injective (Subgroup.normalizer (K : Set G)).subtype
    (Subgroup.normalizer (K : Set G)).subtype_injective).map _

theorem normalizerMonoidHom_mem_normalizer_inducedGroup (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    {s : Subgroup.normalizer (K : Set G)} (hs : (s : G) ∈ Subgroup.normalizer (Y : Set G)) :
    K.normalizerMonoidHom s ∈
      Subgroup.normalizer ((inducedGroup K Y : Subgroup (MulAut K)) : Set (MulAut K)) := by
  have h1 : s ∈ Subgroup.normalizer
      ((Y.subgroupOf (Subgroup.normalizer (K : Set G)) : Subgroup _) : Set _) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hYK]
    exact hs
  exact Subgroup.le_normalizer_map K.normalizerMonoidHom ⟨s, h1, rfl⟩

end InducedGroup

section Transport

variable {K K' : Type*} [Group K] [Group K']

theorem pCoreOf_map_le (e : K ≃* K') (N : Subgroup K) :
    (pCoreOf 2 N).map e.toMonoidHom ≤ pCoreOf 2 (N.map e.toMonoidHom) := by
  refine le_pCoreOf_of_normalized (Subgroup.map_mono (pCoreOf_le N)) ?_ ?_
  · exact (isPGroup_pCoreOf N).map e.toMonoidHom
  · rintro m hm t ht
    obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
    exact ⟨m₀ * t₀ * m₀⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf N hm₀) t₀).mp ht₀, by simp⟩

theorem map_symm_map (e : K ≃* K') (N : Subgroup K) :
    (N.map e.toMonoidHom).map e.symm.toMonoidHom = N := by
  simp [Subgroup.map_map]

theorem map_map_symm (e : K ≃* K') (M : Subgroup K') :
    (M.map e.symm.toMonoidHom).map e.toMonoidHom = M := by
  simp [Subgroup.map_map]

theorem congr_conj (e : K ≃* K') (k : K) :
    MulAut.congr e (MulAut.conj k) = MulAut.conj (e k) := by
  ext x
  change e (k * (e.symm x) * k⁻¹) = e k * x * (e k)⁻¹
  simp

theorem pCoreOf_map_mulEquiv (e : K ≃* K') (N : Subgroup K) :
    pCoreOf 2 (N.map e.toMonoidHom) = (pCoreOf 2 N).map e.toMonoidHom := by
  apply le_antisymm
  · have h1 := pCoreOf_map_le e.symm (N.map e.toMonoidHom)
    rw [map_symm_map e N] at h1
    have h2 := Subgroup.map_mono (f := e.toMonoidHom) h1
    rwa [map_map_symm e (pCoreOf 2 (N.map e.toMonoidHom))] at h2
  · exact pCoreOf_map_le e N

theorem normalizer_map_mulEquiv (e : K ≃* K') (R : Subgroup K) :
    Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup K') : Set K') =
      (Subgroup.normalizer (R : Set K)).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro n
    have h := hx (e n)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h
    simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using h
  · intro hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro n
    have h := hx (e.symm n)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simpa only [map_mul, map_inv] using h

end Transport

section Injective

variable {E G : Type*} [Group E] [Group G]

theorem map_subgroupOf_equivMapOfInjective (ι : E →* G) (hι : Function.Injective ι)
    (K' R' : Subgroup E) :
    (R'.subgroupOf K').map (K'.equivMapOfInjective ι hι).toMonoidHom =
      (R'.map ι).subgroupOf (K'.map ι) := by
  ext z
  have hz : ι ((((K'.equivMapOfInjective ι hι).symm z : ↥K') : E)) = (z : G) := by
    have h := Subgroup.coe_equivMapOfInjective_apply K' ι hι
      ((K'.equivMapOfInjective ι hι).symm z)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← hz,
    Subgroup.mem_map_iff_mem hι]

theorem congr_equivMapOfInjective_normalizerMonoidHom (ι : E →* G) (hι : Function.Injective ι)
    (K' : Subgroup E) (δ : ↥(Subgroup.normalizer (K' : Set E)))
    (δ₂ : ↥(Subgroup.normalizer ((K'.map ι : Subgroup G) : Set G)))
    (hδ : (δ₂ : G) = ι (δ : E)) :
    MulAut.congr (K'.equivMapOfInjective ι hι) (K'.normalizerMonoidHom δ) =
      (K'.map ι).normalizerMonoidHom δ₂ := by
  set e := K'.equivMapOfInjective ι hι with he
  ext z
  have hz : ι (((e.symm z) : ↥K') : E) = (z : G) := by
    have h := Subgroup.coe_equivMapOfInjective_apply K' ι hι (e.symm z)
    rw [← he, MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hL : ((MulAut.congr e (K'.normalizerMonoidHom δ)) z : G) =
      ι (((K'.normalizerMonoidHom δ (e.symm z)) : ↥K') : E) := rfl
  rw [hL]
  have hcoe : (((K'.normalizerMonoidHom δ (e.symm z)) : ↥K') : E) =
      (δ : E) * ((e.symm z : ↥K') : E) * (δ : E)⁻¹ :=
    GGRootNorm.coe_normalizerMonoidHom δ.2 (e.symm z)
  rw [hcoe, map_mul, map_mul, map_inv, hz]
  rw [GGRootNorm.coe_normalizerMonoidHom (K := K'.map ι) δ₂.2 z, hδ]

end Injective

end GGRootNorm

theorem ggRootNormInner_le_sup_centralizer {G : Type*} [Group G] {K R Y : Subgroup G}
    (hRK : R ≤ K) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYR : Y ≤ Subgroup.normalizer (R : Set G)) (hY2 : IsPGroup 2 Y)
    (hNY : K ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (hI : GGRootNormInner (R.subgroupOf K)) :
    Y ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
  intro y hy
  obtain ⟨k, hk⟩ := hI _ (GGRootNorm.induced_isTwoPower hRK hYK hYR hY2 hNY hy)
    (GGRootNorm.induced_map_eq hRK hYK hYR hY2 hNY hy)
    (GGRootNorm.induced_commutes hRK hYK hYR hY2 hNY hy)
  exact GGRootNorm.mem_sup_centralizer_of_induced_inner (hYK hy) hk

theorem ggRootNormInnerDiag_le_sup_centralizer {G : Type*} [Group G] {K R Y : Subgroup G} {δ : G}
    (hRK : R ≤ K) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYR : Y ≤ Subgroup.normalizer (R : Set G)) (hY2 : IsPGroup 2 Y)
    (hNY : K ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (hδK : δ ∈ Subgroup.normalizer (K : Set G)) (hδR : δ ∈ Subgroup.normalizer (R : Set G))
    (hδY : δ ∈ Subgroup.normalizer (Y : Set G))
    (hI : GGRootNormInnerDiag (R.subgroupOf K) (K.normalizerMonoidHom ⟨δ, hδK⟩)) :
    Y ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
  obtain ⟨-, hnorm, hmain⟩ := hI
  intro y hy
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := hYK hy
  set δ' : MulAut K := K.normalizerMonoidHom ⟨δ, hδK⟩ with hδ'
  set y' : MulAut K := K.normalizerMonoidHom ⟨y, hyK⟩ with hy'
  set R' : Subgroup K := R.subgroupOf K with hR'
  set Inn : Subgroup (MulAut K) :=
    (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) with hInn
  set Nbar : Subgroup (MulAut K) :=
    (Subgroup.normalizer (R' : Set K)).map (MulAut.conj : K →* MulAut K) with hNbar
  set H : Subgroup (MulAut K) := Nbar ⊔ Subgroup.zpowers δ' with hH
  set ρY : Subgroup (MulAut K) := GGRootNorm.inducedGroup K Y with hρY
  haveI : Inn.Normal := GGRootNorm.innerAut_normal
  set c : MulAut K := δ' * y' * δ'⁻¹ * y'⁻¹ with hc
  have hδst : δ' ∈ GGRootNorm.ggStab R' := GGRootNorm.normalizerMonoidHom_mem_ggStab hδK hδR
  have hyst : y' ∈ GGRootNorm.ggStab R' :=
    GGRootNorm.normalizerMonoidHom_mem_ggStab hyK (hYR hy)
  have hcst : c ∈ GGRootNorm.ggStab R' :=
    (GGRootNorm.ggStab R').mul_mem
      ((GGRootNorm.ggStab R').mul_mem ((GGRootNorm.ggStab R').mul_mem hδst hyst)
        ((GGRootNorm.ggStab R').inv_mem hδst)) ((GGRootNorm.ggStab R').inv_mem hyst)
  have hcY : c ∈ ρY := by
    refine Subgroup.mem_map.mpr ⟨⟨δ, hδK⟩ * ⟨y, hyK⟩ * ⟨δ, hδK⟩⁻¹ * ⟨y, hyK⟩⁻¹, ?_, ?_⟩
    · show δ * y * δ⁻¹ * y⁻¹ ∈ Y
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hδY y).mp hy) (Y.inv_mem hy)
    · rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have hcInd : c ∈ Inn ⊔ Subgroup.zpowers δ' := by
    have h1 : δ' ∈ Inn ⊔ Subgroup.zpowers δ' := Subgroup.mem_sup_right (Subgroup.mem_zpowers δ')
    have h2 : y' * δ'⁻¹ * y'⁻¹ ∈ Inn ⊔ Subgroup.zpowers δ' :=
      hnorm.conj_mem _ ((Inn ⊔ Subgroup.zpowers δ').inv_mem h1) y'
    have := (Inn ⊔ Subgroup.zpowers δ').mul_mem h1 h2
    simpa [hc, mul_assoc] using this
  have hcH : c ∈ H := by
    obtain ⟨i, hi, z, hz, hiz⟩ := Subgroup.mem_sup_of_normal_left.mp hcInd
    have hzst : z ∈ GGRootNorm.ggStab R' := (Subgroup.zpowers_le.mpr hδst) hz
    have hist : i ∈ GGRootNorm.ggStab R' := by
      have : i = c * z⁻¹ := by rw [← hiz]; group
      rw [this]
      exact (GGRootNorm.ggStab R').mul_mem hcst ((GGRootNorm.ggStab R').inv_mem hzst)
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hi
    have hkN : k ∈ Subgroup.normalizer (R' : Set K) :=
      Subgroup.mem_normalizer_iff.mpr fun x => (hist x).symm
    rw [← hiz]
    exact Subgroup.mul_mem_sup (Subgroup.mem_map.mpr ⟨k, hkN, rfl⟩) hz
  have hcore : c ∈ pCoreOf 2 H := by
    have hT : ρY ⊓ H ≤ pCoreOf 2 H := by
      refine GGRootNorm.le_pCoreOf_of_normalized inf_le_right ?_ ?_
      · exact (GGRootNorm.isPGroup_inducedGroup hY2).to_le inf_le_left
      · intro m hm t ht
        have hHn : H ≤ Subgroup.normalizer (ρY : Set (MulAut K)) := by
          refine sup_le ?_ ?_
          · rintro _ ⟨n, hn, rfl⟩
            have hnG := (GGRootNorm.mem_normalizer_subgroupOf_iff hRK n).mp hn
            have hnY := hNY ⟨n.2, hnG⟩
            rw [← GGRootNorm.normalizerMonoidHom_conj n]
            exact GGRootNorm.normalizerMonoidHom_mem_normalizer_inducedGroup hYK hnY
          · exact Subgroup.zpowers_le.mpr
              (GGRootNorm.normalizerMonoidHom_mem_normalizer_inducedGroup hYK
                (s := ⟨δ, hδK⟩) hδY)
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hHn hm) t).mp ht.1,
          H.mul_mem (H.mul_mem hm ht.2) (H.inv_mem hm)⟩
    exact hT ⟨hcY, hcH⟩
  obtain ⟨k, hk⟩ := hmain y' (GGRootNorm.induced_isTwoPower hRK hYK hYR hY2 hNY hy)
    (GGRootNorm.induced_map_eq hRK hYK hYR hY2 hNY hy)
    (GGRootNorm.induced_commutes hRK hYK hYR hY2 hNY hy) hcore
  exact GGRootNorm.mem_sup_centralizer_of_induced_inner hyK hk

theorem ggRootNormNoCentral_ambient {G : Type*} [Group G] {K R : Subgroup G} (hRK : R ≤ K)
    (h : GGRootNormNoCentral (R.subgroupOf K)) :
    ∀ A B' : Subgroup G, R ≤ A → A ≤ B' →
      B' ≤ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) →
      K ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (A : Set G) →
      K ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (B' : Set G) →
      ⁅B', K ⊓ Subgroup.normalizer (R : Set G)⁆ ≤ A → B' ≤ A := by
  intro A B' hRA hAB hBp hNA hNB hcomm
  have hNK : (K ⊓ Subgroup.normalizer (R : Set G)).subgroupOf K =
      Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hRK]
  have hBK : B' ≤ K := hBp.trans ((GGRootNorm.pCoreOf_le _).trans inf_le_left)
  have hnorm : ∀ {X : Subgroup G}, K ⊓ Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (X : Set G) →
        Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) ≤
          Subgroup.normalizer ((X.subgroupOf K : Subgroup K) : Set K) := by
    intro X hX n hn
    have hnG : (n : G) ∈ Subgroup.normalizer (R : Set G) :=
      (GGRootNorm.mem_normalizer_subgroupOf_iff hRK n).mp hn
    exact Subgroup.le_normalizer_comap K.subtype (hX ⟨n.2, hnG⟩)
  have key := h (A.subgroupOf K) (B'.subgroupOf K) (Subgroup.subgroupOf_mono K hRA)
    (Subgroup.subgroupOf_mono K hAB) ?_ (hnorm hNA) (hnorm hNB) ?_
  · intro b hb
    exact key (show (⟨b, hBK hb⟩ : K) ∈ B'.subgroupOf K from hb)
  · rw [← hNK, GGRootNorm.pCoreOf_subgroupOf inf_le_left]
    exact Subgroup.subgroupOf_mono K hBp
  · refine Subgroup.commutator_le.mpr fun b hb n hn => ?_
    have hnG : (n : G) ∈ Subgroup.normalizer (R : Set G) :=
      (GGRootNorm.mem_normalizer_subgroupOf_iff hRK n).mp hn
    exact hcomm (Subgroup.commutator_mem_commutator hb ⟨n.2, hnG⟩)


section Transport

variable {K K' : Type*} [Group K] [Group K']

theorem ggRootNormInner_map_mulEquiv (e : K ≃* K') {R : Subgroup K} (h : GGRootNormInner R) :
    GGRootNormInner (R.map e.toMonoidHom) := by
  intro y' hy'2 hy'R hy'mod
  set y : MulAut K := (MulAut.congr e).symm y' with hy_def
  have hycongr : MulAut.congr e y = y' := by
    rw [hy_def]; exact MulEquiv.apply_symm_apply _ _
  have hyapply : ∀ x : K, y' (e x) = e (y x) := by
    intro x
    rw [← hycongr]
    change e (y (e.symm (e x))) = e (y x)
    simp
  have hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hy'2
    refine ⟨k, ?_⟩
    have hh := congrArg ((MulAut.congr e).symm) hk
    rw [map_pow, map_one] at hh
    simpa [hy_def] using hh
  have hyR : R.map y.toMonoidHom = R := by
    have h1 : (R.map y.toMonoidHom).map e.toMonoidHom
        = (R.map e.toMonoidHom).map y'.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      have hh : e.toMonoidHom.comp y.toMonoidHom = y'.toMonoidHom.comp e.toMonoidHom := by
        ext x; exact (hyapply x).symm
      rw [hh]
    rw [hy'R] at h1
    exact Subgroup.map_injective e.injective h1
  have hymod : ∀ n ∈ Subgroup.normalizer (R : Set K),
      y n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (R : Set K)) := by
    intro n hn
    have hen : e n ∈ Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup K') : Set K') := by
      rw [GGRootNorm.normalizer_map_mulEquiv e R, Subgroup.mem_map_equiv]
      simpa using hn
    have hmod := hy'mod (e n) hen
    rw [GGRootNorm.normalizer_map_mulEquiv e R,
      GGRootNorm.pCoreOf_map_mulEquiv e (Subgroup.normalizer (R : Set K))] at hmod
    rw [Subgroup.mem_map_equiv] at hmod
    have heq : e.symm (y' (e n) * (e n)⁻¹) = y n * n⁻¹ := by
      rw [map_mul, map_inv, hyapply n]
      simp
    rwa [heq] at hmod
  obtain ⟨k, hk⟩ := h y hy2 hyR hymod
  refine ⟨e k, ?_⟩
  rw [← hycongr, hk, GGRootNorm.congr_conj]

theorem ggRootNormNoCentral_map_mulEquiv (e : K ≃* K') {R : Subgroup K}
    (h : GGRootNormNoCentral R) : GGRootNormNoCentral (R.map e.toMonoidHom) := by
  intro A' B'' hR'A' hA'B'' hB''core hnormA' hnormB'' hcomm
  have hmain : B''.map e.symm.toMonoidHom ≤ A'.map e.symm.toMonoidHom := by
    refine h (A'.map e.symm.toMonoidHom) (B''.map e.symm.toMonoidHom) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← GGRootNorm.map_symm_map e R]
      exact Subgroup.map_mono hR'A'
    · exact Subgroup.map_mono hA'B''
    · have hx := Subgroup.map_mono (f := e.symm.toMonoidHom) hB''core
      rw [← GGRootNorm.pCoreOf_map_mulEquiv e.symm
            (Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup K') : Set K')),
          ← GGRootNorm.normalizer_map_mulEquiv e.symm (R.map e.toMonoidHom),
          GGRootNorm.map_symm_map e R] at hx
      exact hx
    · have hx := Subgroup.map_mono (f := e.symm.toMonoidHom) hnormA'
      rw [← GGRootNorm.normalizer_map_mulEquiv e.symm (R.map e.toMonoidHom),
          GGRootNorm.map_symm_map e R,
          ← GGRootNorm.normalizer_map_mulEquiv e.symm A'] at hx
      exact hx
    · have hx := Subgroup.map_mono (f := e.symm.toMonoidHom) hnormB''
      rw [← GGRootNorm.normalizer_map_mulEquiv e.symm (R.map e.toMonoidHom),
          GGRootNorm.map_symm_map e R,
          ← GGRootNorm.normalizer_map_mulEquiv e.symm B''] at hx
      exact hx
    · have hx := Subgroup.map_mono (f := e.symm.toMonoidHom) hcomm
      rw [Subgroup.map_commutator,
          ← GGRootNorm.normalizer_map_mulEquiv e.symm (R.map e.toMonoidHom),
          GGRootNorm.map_symm_map e R] at hx
      exact hx
  have hx := Subgroup.map_mono (f := e.toMonoidHom) hmain
  rwa [GGRootNorm.map_map_symm e B'', GGRootNorm.map_map_symm e A'] at hx

theorem ggRootNormInnerDiag_map_mulEquiv (e : K ≃* K') {R : Subgroup K} {δ : MulAut K}
    (h : GGRootNormInnerDiag R δ) :
    GGRootNormInnerDiag (R.map e.toMonoidHom) (MulAut.congr e δ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.map_map]
    have hh : (MulAut.congr e δ).toMonoidHom.comp e.toMonoidHom
        = e.toMonoidHom.comp δ.toMonoidHom := by
      ext k
      change e (δ (e.symm (e k))) = e (δ k)
      simp
    rw [hh, ← Subgroup.map_map, h1]
  · have hInn : ((⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K)).map
          (MulAut.congr e).toMonoidHom
        = (⊤ : Subgroup K').map (MulAut.conj : K' →* MulAut K') := by
      rw [Subgroup.map_map]
      have hh : (MulAut.congr e).toMonoidHom.comp (MulAut.conj : K →* MulAut K)
          = (MulAut.conj : K' →* MulAut K').comp e.toMonoidHom := by
        apply MonoidHom.ext
        intro k
        exact GGRootNorm.congr_conj e k
      rw [hh, ← Subgroup.map_map, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    have hM : (((⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) ⊔ Subgroup.zpowers δ).map
          (MulAut.congr e).toMonoidHom)
        = ((⊤ : Subgroup K').map (MulAut.conj : K' →* MulAut K') ⊔
            Subgroup.zpowers (MulAut.congr e δ)) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hInn]
      rfl
    rw [← hM]
    exact h2.map (MulAut.congr e).toMonoidHom (MulAut.congr e).surjective
  · intro y' hy'2 hy'R hy'mod hδ'y'
    set y : MulAut K := (MulAut.congr e).symm y' with hy_def
    have hycongr : MulAut.congr e y = y' := by
      rw [hy_def]; exact MulEquiv.apply_symm_apply _ _
    have hyapply : ∀ x : K, y' (e x) = e (y x) := by
      intro x
      rw [← hycongr]
      change e (y (e.symm (e x))) = e (y x)
      simp
    have hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hy'2
      refine ⟨k, ?_⟩
      have hh := congrArg ((MulAut.congr e).symm) hk
      rw [map_pow, map_one] at hh
      simpa [hy_def] using hh
    have hyR : R.map y.toMonoidHom = R := by
      have h1' : (R.map y.toMonoidHom).map e.toMonoidHom
          = (R.map e.toMonoidHom).map y'.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        have hh : e.toMonoidHom.comp y.toMonoidHom = y'.toMonoidHom.comp e.toMonoidHom := by
          ext x; exact (hyapply x).symm
        rw [hh]
      rw [hy'R] at h1'
      exact Subgroup.map_injective e.injective h1'
    have hymod : ∀ n ∈ Subgroup.normalizer (R : Set K),
        y n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (R : Set K)) := by
      intro n hn
      have hen : e n ∈ Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup K') : Set K') := by
        rw [GGRootNorm.normalizer_map_mulEquiv e R, Subgroup.mem_map_equiv]
        simpa using hn
      have hmod := hy'mod (e n) hen
      rw [GGRootNorm.normalizer_map_mulEquiv e R,
        GGRootNorm.pCoreOf_map_mulEquiv e (Subgroup.normalizer (R : Set K))] at hmod
      rw [Subgroup.mem_map_equiv] at hmod
      have heq : e.symm (y' (e n) * (e n)⁻¹) = y n * n⁻¹ := by
        rw [map_mul, map_inv, hyapply n]
        simp
      rwa [heq] at hmod
    have hδy : δ * y * δ⁻¹ * y⁻¹ ∈ pCoreOf 2
        ((Subgroup.normalizer (R : Set K)).map (MulAut.conj : K →* MulAut K) ⊔
          Subgroup.zpowers δ) := by
      have hx : (MulAut.congr e).symm
            (MulAut.congr e δ * y' * (MulAut.congr e δ)⁻¹ * y'⁻¹)
          ∈ pCoreOf 2 ((Subgroup.normalizer (R : Set K)).map
              (MulAut.conj : K →* MulAut K) ⊔ Subgroup.zpowers δ) := by
        have h0 := hδ'y'
        have hM : (((Subgroup.normalizer (R : Set K)).map (MulAut.conj : K →* MulAut K) ⊔
              Subgroup.zpowers δ).map (MulAut.congr e).toMonoidHom)
            = (Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup K') : Set K')).map
                (MulAut.conj : K' →* MulAut K') ⊔ Subgroup.zpowers (MulAut.congr e δ) := by
          rw [Subgroup.map_sup, MonoidHom.map_zpowers]
          have hInn' : ((Subgroup.normalizer (R : Set K)).map
                (MulAut.conj : K →* MulAut K)).map (MulAut.congr e).toMonoidHom
              = (Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup K') : Set K')).map
                  (MulAut.conj : K' →* MulAut K') := by
            rw [Subgroup.map_map]
            have hh : (MulAut.congr e).toMonoidHom.comp (MulAut.conj : K →* MulAut K)
                = (MulAut.conj : K' →* MulAut K').comp e.toMonoidHom := by
              apply MonoidHom.ext
              intro k
              exact GGRootNorm.congr_conj e k
            rw [hh, ← Subgroup.map_map, GGRootNorm.normalizer_map_mulEquiv e R]
          rw [hInn']
          rfl
        rw [← hM, GGRootNorm.pCoreOf_map_mulEquiv (MulAut.congr e)
            ((Subgroup.normalizer (R : Set K)).map (MulAut.conj : K →* MulAut K) ⊔
              Subgroup.zpowers δ)] at h0
        rw [Subgroup.mem_map_equiv] at h0
        exact h0
      have hconv : (MulAut.congr e).symm
            (MulAut.congr e δ * y' * (MulAut.congr e δ)⁻¹ * y'⁻¹)
          = δ * y * δ⁻¹ * y⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        simp only [MulEquiv.symm_apply_apply]
        rw [← hy_def]
      rwa [hconv] at hx
    obtain ⟨k, hk⟩ := h3 y hy2 hyR hymod hδy
    refine ⟨e k, ?_⟩
    rw [← hycongr, hk, GGRootNorm.congr_conj]

end Transport


section Injective

variable {E G : Type*} [Group E] [Group G]

theorem ggRootNormInner_of_map_injective (ι : E →* G) (hι : Function.Injective ι)
    {K' R' : Subgroup E} {K R : Subgroup G} (hK : K'.map ι = K) (hR : R'.map ι = R)
    (h : GGRootNormInner (R'.subgroupOf K')) : GGRootNormInner (R.subgroupOf K) := by
  subst hK
  subst hR
  rw [← GGRootNorm.map_subgroupOf_equivMapOfInjective ι hι K' R']
  exact ggRootNormInner_map_mulEquiv (K'.equivMapOfInjective ι hι) h

theorem ggRootNormNoCentral_of_map_injective (ι : E →* G) (hι : Function.Injective ι)
    {K' R' : Subgroup E} {K R : Subgroup G} (hK : K'.map ι = K) (hR : R'.map ι = R)
    (h : GGRootNormNoCentral (R'.subgroupOf K')) : GGRootNormNoCentral (R.subgroupOf K) := by
  subst hK
  subst hR
  rw [← GGRootNorm.map_subgroupOf_equivMapOfInjective ι hι K' R']
  exact ggRootNormNoCentral_map_mulEquiv (K'.equivMapOfInjective ι hι) h

theorem ggRootNormInnerDiag_of_map_injective (ι : E →* G) (hι : Function.Injective ι)
    {K' R' : Subgroup E} {K R : Subgroup G} (hK : K'.map ι = K) (hR : R'.map ι = R)
    {δ : ↥(Subgroup.normalizer (K' : Set E))} {δ₂ : ↥(Subgroup.normalizer (K : Set G))}
    (hδ : (δ₂ : G) = ι (δ : E))
    (h : GGRootNormInnerDiag (R'.subgroupOf K') (K'.normalizerMonoidHom δ)) :
    GGRootNormInnerDiag (R.subgroupOf K) (K.normalizerMonoidHom δ₂) := by
  subst hK
  subst hR
  have hδ' := GGRootNorm.congr_equivMapOfInjective_normalizerMonoidHom ι hι K' δ δ₂ hδ
  rw [← GGRootNorm.map_subgroupOf_equivMapOfInjective ι hι K' R']
  rw [← hδ']
  exact ggRootNormInnerDiag_map_mulEquiv (K'.equivMapOfInjective ι hι) h

end Injective

end CFSG.StandardType
