module

public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section

@[expose] noncomputable def quotPCoreAut614 (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ CFSG.pCore 2 Y) where
  toFun σ := QuotientGroup.congr (CFSG.pCore 2 Y) (CFSG.pCore 2 Y) σ (CFSG.pCore_map_iso 2 σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl

theorem quotPCoreAut614_mk (Y : Type*) [Group Y] (σ : MulAut Y) (y : Y) :
    quotPCoreAut614 Y σ (y : Y ⧸ CFSG.pCore 2 Y) = ((σ y : Y) : Y ⧸ CFSG.pCore 2 Y) := rfl

@[expose] def LocFus614 (G : Type*) [Group G] (N : Subgroup G) : Prop :=
  ∀ (T X E : Subgroup G), IsSylowTwoOf T (N ⊔ T) → X ≤ N → X = oTwoUpper X →
    (X ⊓ T).relIndex X = 5 → ((X ⊓ T).subgroupOf X).Normal →
    T ≤ Subgroup.normalizer (X : Set G) →
    E ≤ pCoreOf 2 (X ⊔ T) → IsElemAbelian 2 E → E ≠ ⊥ →
      ∃ n ∈ N, E.map (MulAut.conj n).toMonoidHom ≤ T ∧
        ¬ E.map (MulAut.conj n).toMonoidHom ≤ pCoreOf 2 (X ⊔ T)

variable {Γ : Type} [Group Γ]

@[expose] noncomputable def actModO2_614 (K : Subgroup Γ) :
    ↥(Subgroup.normalizer (K : Set Γ)) →* MulAut (ModO2 K) :=
  (quotPCoreAut614 ↥K).comp K.normalizerMonoidHom

theorem actModO2_614_mk (K : Subgroup Γ) (n : ↥(Subgroup.normalizer (K : Set Γ))) (k : ↥K) :
    actModO2_614 K n (k : ModO2 K) =
      ((⟨(n : Γ) * k * (n : Γ)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 k).mp k.2⟩ : ↥K) :
        ModO2 K) := by
  show quotPCoreAut614 ↥K (K.normalizerMonoidHom n) (k : ModO2 K) = _
  rw [quotPCoreAut614_mk]
  congr 1

section Reduction

variable {K T : Subgroup Γ}

theorem sup_le_normalizer614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) :
    K ⊔ T ≤ Subgroup.normalizer (K : Set Γ) :=
  sup_le Subgroup.le_normalizer hTK

@[expose] noncomputable def piKT614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) :
    ↥(K ⊔ T) →* MulAut (ModO2 K) :=
  (actModO2_614 K).comp (Subgroup.inclusion (sup_le_normalizer614 hTK))

theorem piKT614_of_mem (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) {k : Γ} (hk : k ∈ K) :
    piKT614 hTK ⟨k, (le_sup_left : K ≤ K ⊔ T) hk⟩ =
      MulAut.conj (((⟨k, hk⟩ : ↥K) : ModO2 K)) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    show actModO2_614 K _ (y : ModO2 K) = _
    rw [actModO2_614_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

@[expose] noncomputable def imKT614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) (A : Subgroup Γ) :
    Subgroup (MulAut (ModO2 K)) :=
  (A.subgroupOf (K ⊔ T)).map (piKT614 hTK)

theorem mem_imKT614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) {A : Subgroup Γ} {x : Γ}
    (hx : x ∈ A) (hxKT : x ∈ K ⊔ T) : piKT614 hTK ⟨x, hxKT⟩ ∈ imKT614 hTK A :=
  ⟨⟨x, hxKT⟩, hx, rfl⟩

theorem imKT614_mono (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) {A B : Subgroup Γ}
    (h : A ≤ B) : imKT614 hTK A ≤ imKT614 hTK B :=
  Subgroup.map_mono fun _ hx => h hx

theorem imKT614_sup (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) {A B : Subgroup Γ}
    (hA : A ≤ K ⊔ T) (hB : B ≤ K ⊔ T) :
    imKT614 hTK (A ⊔ B) = imKT614 hTK A ⊔ imKT614 hTK B := by
  unfold imKT614
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem imKT614_eq_map (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) {A X : Subgroup Γ}
    (hAX : A ≤ X) (hX : X ≤ K ⊔ T) :
    imKT614 hTK A = (A.subgroupOf X).map ((piKT614 hTK).comp (Subgroup.inclusion hX)) := by
  ext φ
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hAX hb⟩, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨Subgroup.inclusion hX b, hb, rfl⟩

theorem imKT614_self (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) :
    imKT614 hTK K = (MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range := by
  ext φ
  constructor
  · rintro ⟨⟨k, hkKT⟩, hk, rfl⟩
    exact ⟨_, (piKT614_of_mem hTK hk).symm⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨⟨k, (le_sup_left : K ≤ K ⊔ T) hk⟩, hk, piKT614_of_mem hTK hk⟩


theorem mem_pCoreOf_of_piKT614_eq_one (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hT2 : IsPGroup 2 T) (hZ : Subgroup.center (ModO2 K) = ⊥) {y : ↥(K ⊔ T)}
    (hy : piKT614 hTK y = 1) : (y : Γ) ∈ pCoreOf 2 (K ⊔ T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKker : ∀ (k : Γ) (hk : k ∈ K), piKT614 hTK ⟨k, (le_sup_left : K ≤ K ⊔ T) hk⟩ = 1 →
      ∃ m : ℕ, k ^ 2 ^ m = 1 := by
    intro k hk h1
    rw [piKT614_of_mem] at h1
    have hc : ((⟨k, hk⟩ : ↥K) : ModO2 K) ∈ Subgroup.center (ModO2 K) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ : MulAut (ModO2 K) => φ z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨⟨k, hk⟩, hc⟩
    exact ⟨m, by simpa using congrArg (fun z => ((z : ↥K) : Γ)) (congrArg Subtype.val hm)⟩
  have hpowK : ∀ (k t : Γ), k ∈ K → t ∈ T → ∀ n : ℕ, (k * t) ^ n * (t ^ n)⁻¹ ∈ K := by
    intro k t hk ht n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : t ^ n * k * (t ^ n)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).pow_mem (hTK ht) n) k).mp hk
      have e : (k * t) ^ (n + 1) * (t ^ (n + 1))⁻¹ =
          ((k * t) ^ n * (t ^ n)⁻¹) * (t ^ n * k * (t ^ n)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact K.mul_mem ih h1
  set N : Subgroup Γ := (piKT614 hTK).ker.map (K ⊔ T).subtype with hN
  have hNle : N ≤ K ⊔ T := Subgroup.map_subtype_le _
  have hcoe : ((K ⊔ T : Subgroup Γ) : Set Γ) = (K : Set Γ) * (T : Set Γ) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K T hTK
  have hN2 : IsPGroup 2 N := by
    rintro ⟨_, ⟨z, hz, rfl⟩⟩
    have hz' : (z : Γ) ∈ (K : Set Γ) * (T : Set Γ) := hcoe ▸ z.2
    obtain ⟨k, hk, t, ht, hkt⟩ := hz'
    have hkt' : k * t = (z : Γ) := hkt
    obtain ⟨m, hm⟩ := hT2 ⟨t, ht⟩
    have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h1 : (z : Γ) ^ 2 ^ m ∈ K := by
      have := hpowK k t hk ht (2 ^ m)
      rw [htm, inv_one, mul_one, hkt'] at this
      exact this
    have h2 : piKT614 hTK ⟨(z : Γ) ^ 2 ^ m, (le_sup_left : K ≤ K ⊔ T) h1⟩ = 1 := by
      have e : (⟨(z : Γ) ^ 2 ^ m, (le_sup_left : K ≤ K ⊔ T) h1⟩ : ↥(K ⊔ T)) = z ^ 2 ^ m :=
        Subtype.ext (by simp)
      rw [e, map_pow, MonoidHom.mem_ker.mp hz, one_pow]
    obtain ⟨m', hm'⟩ := hKker _ h1 h2
    refine ⟨m + m', Subtype.ext ?_⟩
    simp only [Subgroup.coe_subtype, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul]
    exact hm'
  have hNnorm : K ⊔ T ≤ Subgroup.normalizer (N : Set Γ) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨g, hg⟩ * z * (⟨g, hg⟩ : ↥(K ⊔ T))⁻¹, ?_, by simp⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, MonoidHom.mem_ker.mp hz,
        mul_one, map_inv, mul_inv_cancel]
    · rintro ⟨z, hz, hzx⟩
      refine ⟨(⟨g, hg⟩ : ↥(K ⊔ T))⁻¹ * z * ⟨g, hg⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, MonoidHom.mem_ker.mp hz,
          mul_one, map_inv, inv_mul_cancel]
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hzx ⊢
        rw [hzx]
        group
  have hNO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNle hNnorm hN2
  exact hNO ⟨y, hy, rfl⟩

theorem mem_of_piKT614_mem (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) (hZ : Subgroup.center (ModO2 K) = ⊥) {g : ↥(K ⊔ T)}
    (hg : piKT614 hTK g ∈ imKT614 hTK T) : (g : Γ) ∈ T := by
  obtain ⟨t, ht, he⟩ := hg
  have h1 : piKT614 hTK (g * t⁻¹) = 1 := by rw [map_mul, map_inv, ← he, mul_inv_cancel]
  have h2 := mem_pCoreOf_of_piKT614_eq_one hTK hTs.2.1 hZ h1
  have h3 : ((g * t⁻¹ : ↥(K ⊔ T)) : Γ) ∈ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTs h2
  have e : (g : Γ) = ((g * t⁻¹ : ↥(K ⊔ T)) : Γ) * t := by simp
  rw [e]
  exact T.mul_mem h3 ht

theorem ker_piKT614_le (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) (hZ : Subgroup.center (ModO2 K) = ⊥) :
    (piKT614 hTK).ker ≤ T.subgroupOf (K ⊔ T) := fun _ hg =>
  EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTs
    (mem_pCoreOf_of_piKT614_eq_one hTK hTs.2.1 hZ (MonoidHom.mem_ker.mp hg))

theorem isSylowTwoOf_imKT614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) (hZ : Subgroup.center (ModO2 K) = ⊥) :
    IsSylowTwoOf (imKT614 hTK T)
      ((MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range ⊔ imKT614 hTK T) := by
  have hrange : (MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range ⊔ imKT614 hTK T =
      (piKT614 hTK).range := by
    rw [← imKT614_self hTK, ← imKT614_sup hTK le_sup_left le_sup_right, imKT614,
      Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  rw [hrange]
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · have hT2 : IsPGroup 2 (T.subgroupOf (K ⊔ T)) :=
      hTs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTs.1).symm
    exact hT2.map _
  · set ρ := (piKT614 hTK).rangeRestrict
    have hsub : (imKT614 hTK T).subgroupOf (piKT614 hTK).range = (T.subgroupOf (K ⊔ T)).map ρ := by
      ext ⟨φ, hφ⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, he⟩
        exact ⟨t, ht, Subtype.ext he⟩
      · rintro ⟨t, ht, he⟩
        exact ⟨t, ht, congrArg Subtype.val he⟩
    rw [hsub, Subgroup.index_map, MonoidHom.range_eq_top.mpr (MonoidHom.rangeRestrict_surjective _),
      Subgroup.index_top, mul_one, MonoidHom.ker_rangeRestrict,
      sup_eq_left.mpr (ker_piKT614_le hTK hTs hZ)]
    exact hTs.2.2

theorem kg614Fusion_conclusion_of_locFus [Finite Γ] (hZ : Subgroup.center (ModO2 K) = ⊥)
    (hloc : LocFus614 (MulAut (ModO2 K)) (MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range)
    {X : Subgroup Γ} (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) (hTs : IsSylowTwoOf T (K ⊔ T))
    (hXK : X ≤ K) (hXO : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) (hTX : T ≤ Subgroup.normalizer (X : Set Γ))
    {E : Subgroup Γ} (hE : E ≤ pCoreOf 2 (X ⊔ T)) (hEa : IsElemAbelian 2 E)
    (hEK : ¬ E ≤ pCoreOf 2 (K ⊔ T)) :
    ∃ k ∈ K, E.map (MulAut.conj k).toMonoidHom ≤ T ∧
      ¬ E.map (MulAut.conj k).toMonoidHom ≤ pCoreOf 2 (X ⊔ T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := piKT614 hTK with hπ
  set Inn := (MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range
  have hXKT : X ≤ K ⊔ T := hXK.trans le_sup_left
  have hTKT : T ≤ K ⊔ T := le_sup_right
  have hXTKT : X ⊔ T ≤ K ⊔ T := sup_le hXKT hTKT
  set O := pCoreOf 2 (X ⊔ T) with hO
  have hOXT : O ≤ X ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hEKT : E ≤ K ⊔ T := (hE.trans hOXT).trans hXTKT
  set X' := imKT614 hTK X with hX'def
  set T' := imKT614 hTK T with hT'def
  set E' := imKT614 hTK E with hE'def
  have hTs' := isSylowTwoOf_imKT614 hTK hTs hZ
  have hX'N : X' ≤ Inn := (imKT614_mono hTK hXK).trans (imKT614_self hTK).le
  set πX := π.comp (Subgroup.inclusion hXKT) with hπX
  have hX'eq : X' = (⊤ : Subgroup ↥X).map πX := by
    rw [hX'def, imKT614_eq_map hTK le_rfl hXKT, Subgroup.subgroupOf_self]
  have hXTeq : X' ⊓ T' = ((X ⊓ T).subgroupOf X).map πX := by
    rw [hπX, ← imKT614_eq_map hTK inf_le_left hXKT]
    refine le_antisymm ?_ ?_
    · rintro φ ⟨⟨⟨x, hxKT⟩, hx, rfl⟩, hφT⟩
      exact ⟨⟨x, hxKT⟩, ⟨hx, mem_of_piKT614_mem hTK hTs hZ hφT⟩, rfl⟩
    · exact le_inf (imKT614_mono hTK inf_le_left) (imKT614_mono hTK inf_le_right)
  have hkerX : πX.ker ≤ (X ⊓ T).subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x.2, ?_⟩
    have := ker_piKT614_le hTK hTs hZ (show Subgroup.inclusion hXKT x ∈ π.ker from hx)
    exact this
  have hX5' : (X' ⊓ T').relIndex X' = 5 := by
    rw [hXTeq, hX'eq, Subgroup.relIndex_map_map, sup_eq_left.mpr hkerX, top_sup_eq,
      Subgroup.relIndex_top_right]
    exact hX5
  have hXn' : ((X' ⊓ T').subgroupOf X').Normal := by
    have hsub : (X' ⊓ T').subgroupOf X' = ((X ⊓ T).subgroupOf X).map
        (πX.codRestrict X' fun x => by rw [hX'eq]; exact ⟨x, Subgroup.mem_top x, rfl⟩) := by
      ext ⟨φ, hφ⟩
      rw [Subgroup.mem_subgroupOf, hXTeq, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, he⟩
        exact ⟨x, hx, Subtype.ext he⟩
      · rintro ⟨x, hx, he⟩
        exact ⟨x, hx, congrArg Subtype.val he⟩
    rw [hsub]
    refine hXn.map _ ?_
    rintro ⟨φ, hφ⟩
    rw [hX'eq] at hφ
    obtain ⟨x, -, rfl⟩ := hφ
    exact ⟨x, rfl⟩
  have hXO' : X' = oTwoUpper X' := by
    have h1 : oTwoUpper (X.subgroupOf (K ⊔ T)) = (oTwoUpper X).subgroupOf (K ⊔ T) := by
      apply Subgroup.map_injective (K ⊔ T).subtype_injective
      rw [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le hXKT,
        Subgroup.map_subgroupOf_eq_of_le ((oTwoUpper_le X).trans hXKT)]
    show (X.subgroupOf (K ⊔ T)).map π = oTwoUpper ((X.subgroupOf (K ⊔ T)).map π)
    rw [oTwoUpper_map, h1, ← hXO]
  have hTX' : T' ≤ Subgroup.normalizer (X' : Set (MulAut (ModO2 K))) := by
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map π)
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hTX ht) h
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hE' : E' ≤ pCoreOf 2 (X' ⊔ T') := by
    have hO' : imKT614 hTK O ≤ pCoreOf 2 (X' ⊔ T') := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
      · rw [← imKT614_sup hTK hXKT hTKT]
        exact imKT614_mono hTK hOXT
      · rw [← imKT614_sup hTK hXKT hTKT]
        refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map π)
        intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro h
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T) hg) h
      · have : IsPGroup 2 (O.subgroupOf (K ⊔ T)) :=
          hO2.of_equiv (Subgroup.subgroupOfEquivOfLe (hOXT.trans hXTKT)).symm
        exact this.map _
    exact (imKT614_mono hTK hE).trans hO'
  have hEa' : IsElemAbelian 2 E' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      show π x * π y = π y * π x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have := hEa.1.is_comm.comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩
      have h2 : (x : Γ) * y = y * x := congrArg Subtype.val this
      exact h2
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hEa.2 _ hx)
      rw [this, map_one]
  have hE'ne : E' ≠ ⊥ := by
    intro hbot
    apply hEK
    intro e he
    have h1 : π ⟨e, hEKT he⟩ = 1 := by
      have : π ⟨e, hEKT he⟩ ∈ E' := mem_imKT614 hTK he (hEKT he)
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    exact mem_pCoreOf_of_piKT614_eq_one hTK hTs.2.1 hZ h1
  obtain ⟨φ, hφN, hφT, hφO⟩ := hloc T' X' E' hTs' hX'N hXO' hX5' hXn' hTX' hE' hEa' hE'ne
  obtain ⟨s, rfl⟩ := hφN
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective s
  have hkKT : k ∈ K ⊔ T := (le_sup_left : K ≤ K ⊔ T) hk
  have hπk := piKT614_of_mem hTK hk
  have hconj : ∀ e (he : e ∈ K ⊔ T), π ⟨k * e * k⁻¹, (K ⊔ T).mul_mem
      ((K ⊔ T).mul_mem hkKT he) ((K ⊔ T).inv_mem hkKT)⟩ =
      MulAut.conj (MulAut.conj (((⟨k, hk⟩ : ↥K) : ModO2 K))) (π ⟨e, he⟩) := by
    intro e he
    rw [MulAut.conj_apply, ← hπk, ← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨k, hk, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    have he' := hEKT he
    have hmem : π ⟨k * e * k⁻¹, (K ⊔ T).mul_mem ((K ⊔ T).mul_mem hkKT he')
        ((K ⊔ T).inv_mem hkKT)⟩ ∈ T' := by
      rw [hconj e he']
      exact hφT ⟨π ⟨e, he'⟩, mem_imKT614 hTK he he', rfl⟩
    exact mem_of_piKT614_mem hTK hTs hZ hmem
  · intro hle
    apply hφO
    rintro _ ⟨_, ⟨⟨e, he'⟩, he, rfl⟩, rfl⟩
    have hmem := hle ⟨e, he, rfl⟩
    have h1 : π ⟨k * e * k⁻¹, (K ⊔ T).mul_mem ((K ⊔ T).mul_mem hkKT he')
        ((K ⊔ T).inv_mem hkKT)⟩ ∈ imKT614 hTK O := mem_imKT614 hTK hmem _
    rw [hconj e he'] at h1
    have hO' : imKT614 hTK O ≤ pCoreOf 2 (X' ⊔ T') := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
      · rw [← imKT614_sup hTK hXKT hTKT]
        exact imKT614_mono hTK hOXT
      · rw [← imKT614_sup hTK hXKT hTKT]
        refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map π)
        intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro h
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T) hg) h
      · have : IsPGroup 2 (O.subgroupOf (K ⊔ T)) :=
          hO2.of_equiv (Subgroup.subgroupOfEquivOfLe (hOXT.trans hXTKT)).symm
        exact this.map _
    exact hO' h1

end Reduction

end

end CFSG.Quasithin.H13
