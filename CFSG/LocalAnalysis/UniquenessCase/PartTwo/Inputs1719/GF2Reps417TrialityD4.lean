module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4ParabolicHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoParabolicHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Normal
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W] [Finite W]

private lemma conj_map_subtype_trialityD4 (L : Subgroup (MulAut W)) (t : MulAut W)
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (Z : Subgroup ↥L) :
    (Z.map L.subtype).map (MulAut.conj t).toMonoidHom =
      (Z.map (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom).map L.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private lemma map_normalizerMonoidHom_subgroupOf_inf (T L : Subgroup (MulAut W)) (t : MulAut W)
    (ht : t ∈ T) (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ((T ⊓ L).subgroupOf L).map (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom =
      (T ⊓ L).subgroupOf L := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : MulAut W) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hx
    have hval : ((L.normalizerMonoidHom ⟨t, htN⟩ x : ↥L) : MulAut W) =
        t * (x : MulAut W) * t⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨t, htN⟩ x
    show (L.normalizerMonoidHom ⟨t, htN⟩ x : ↥L) ∈ (T ⊓ L).subgroupOf L
    rw [Subgroup.mem_subgroupOf, hval]
    exact ⟨T.mul_mem (T.mul_mem ht hx'.1) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp htN (x : MulAut W)).mp x.2⟩
  · exact (Subgroup.card_map_of_injective
      (f := (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom) (MulEquiv.injective _)).ge

private lemma map_conj_eq_of_invariant (T L : Subgroup (MulAut W)) (S : Subgroup ↥L)
    (hSdef : S = (T ⊓ L).subgroupOf L) (Z : Subgroup ↥L)
    (hZ : ∀ α : MulAut ↥L, S.map α.toMonoidHom = S → Z.map α.toMonoidHom = Z)
    (t : MulAut W) (ht : t ∈ T)
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    (Z.map L.subtype).map (MulAut.conj t).toMonoidHom = Z.map L.subtype := by
  rw [conj_map_subtype_trialityD4 L t htN Z]
  have h := hZ _ (by rw [hSdef]; exact map_normalizerMonoidHom_subgroupOf_inf T L t ht htN)
  rw [h]

private lemma nonempty_bar2_map_subtype (L : Subgroup (MulAut W)) (Z : Subgroup ↥L) :
    Nonempty (Bar2 Z ≃* Bar2 (Z.map L.subtype)) := by
  let e : ↥Z ≃* ↥(Z.map L.subtype) := Z.equivMapOfInjective L.subtype L.subtype_injective
  exact ⟨QuotientGroup.congr (CFSG.pCore 2 ↥Z) (CFSG.pCore 2 ↥(Z.map L.subtype)) e
    (CFSG.pCore_map_iso 2 e)⟩

private lemma isSylowIn_sup_of_le_trialityD4 {T Y : Subgroup (MulAut W)} (hsyl : IsSylowIn 2 T Y)
    {K : Subgroup (MulAut W)} (hKY : K ≤ Y) : IsSylowIn 2 T (K ⊔ T) := by
  refine ⟨le_sup_right, hsyl.2.1, fun h => hsyl.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T (K ⊔ T) Y le_sup_right (sup_le hKY hsyl.1)]
  exact Dvd.dvd.mul_right h _

private lemma bParam_le_of_pair_inFSq (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    {K₁ K₂ : Subgroup (MulAut W)} {n₁ n₂ c : ℕ} (hK₁L : K₁ ≤ L) (hK₂L : K₂ ≤ L)
    (hLle : L ≤ K₁ ⊔ K₂ ⊔ T) (h₁ : InFSq n₁ (K₁ ⊔ T)) (h₂ : InFSq n₂ (K₂ ⊔ T))
    (hc : n₁ + n₂ ≤ c) : bParam L Y ≤ c := by
  have hTY : T ≤ Y := hsyl.1
  have hLY : L ≤ Y := hcomp.1
  have hsupΔ : (⨆ H ∈ ({K₁ ⊔ T, K₂ ⊔ T} : Set (Subgroup (MulAut W))), H) = Y := by
    rw [iSup_insert, iSup_singleton]
    refine le_antisymm (sup_le (sup_le (hK₁L.trans hLY) hTY) (sup_le (hK₂L.trans hLY) hTY)) ?_
    rw [← hLT]
    refine sup_le (hLle.trans (sup_le (sup_le ?_ ?_) ?_)) ?_
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  have hsum : fIndexSum ({K₁ ⊔ T, K₂ ⊔ T} : Set (Subgroup (MulAut W))) ≤ (c : ℕ∞) := by
    by_cases h12 : K₁ ⊔ T = K₂ ⊔ T
    · rw [h12, Set.pair_eq_singleton, fIndexSum, finsum_mem_singleton]
      refine (fIndex_le_iff.mpr h₂).trans ?_
      exact_mod_cast (le_trans (Nat.le_add_left n₂ n₁) hc)
    · rw [fIndexSum, finsum_mem_pair h12]
      calc fIndex (K₁ ⊔ T) + fIndex (K₂ ⊔ T) ≤ (n₁ : ℕ∞) + n₂ :=
            add_le_add (fIndex_le_iff.mpr h₁) (fIndex_le_iff.mpr h₂)
        _ = ((n₁ + n₂ : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ (c : ℕ∞) := by exact_mod_cast hc
  refine bParam_le_of_fIndexSum_le w4Lem4_16_holds hW hLT hcomp hsyl hO2 hfix
    ((Set.finite_singleton _).insert _) ?_ hsupΔ hsum
  intro H hH
  rcases hH with rfl | hH
  · exact ⟨sup_le (hK₁L.trans hLY) hTY, le_sup_right⟩
  · rw [Set.mem_singleton_iff.mp hH]
    exact ⟨sup_le (hK₂L.trans hLY) hTY, le_sup_right⟩

theorem bParam_le_four_mul_of_is3D4_of_kFacts
    (hA : K_3D4ParabolicGen) (hB : K_3D4TwoParabolicGen)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {n : ℕ} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    (hTN : T ≤ Subgroup.normalizer (L : Set (MulAut W))) (hD : Is3D4 ↥L n) :
    bParam L Y ≤ 4 * n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTY : T ≤ Y := hsyl.1
  have hLY : L ≤ Y := hcomp.1
  have hTL : IsSylowIn 2 (T ⊓ L) L :=
    CFSG.Quasithin.F6.isSylowIn_inf_of_isSubnormal hcomp.2.1 hsyl
  set S : Subgroup ↥L := (T ⊓ L).subgroupOf L with hSdef
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, hTL.2.1.comap_of_injective L.subtype L.subtype_injective, ?_⟩
    have h1 : (S.subgroupOf (⊤ : Subgroup ↥L)).index = S.index := Subgroup.relIndex_top_right _
    rw [h1]
    exact hTL.2.2
  have hsylH : ∀ K : Subgroup (MulAut W), K ≤ Y → IsSylowIn 2 T (K ⊔ T) :=
    fun K hKY => isSylowIn_sup_of_le_trialityD4 hsyl hKY
  rcases Nat.lt_or_ge n 2 with hlt | hge
  ·
    have hn1 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hD).2.1
    obtain rfl : n = 1 := by omega
    obtain ⟨Y₁, X₂, hperf₁, hL2₁, hSX₂, hcardX₂, hgen, hinv⟩ := hB ↥L hD S hS
    set K₁ : Subgroup (MulAut W) := Y₁.map L.subtype with hK₁
    set K₂ : Subgroup (MulAut W) := X₂.map L.subtype with hK₂
    have hK₁L : K₁ ≤ L := Subgroup.map_subtype_le Y₁
    have hK₂L : K₂ ≤ L := Subgroup.map_subtype_le X₂
    have hinv₁ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
        K₁.map (MulAut.conj t).toMonoidHom = K₁ :=
      fun t ht htN => map_conj_eq_of_invariant T L S hSdef Y₁
        (fun α hα => (hinv α hα).1) t ht htN
    have hinv₂ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
        K₂.map (MulAut.conj t).toMonoidHom = K₂ :=
      fun t ht htN => map_conj_eq_of_invariant T L S hSdef X₂
        (fun α hα => (hinv α hα).2) t ht htN
    have hInF₁ : InFSq 3 (K₁ ⊔ T) := by
      obtain ⟨e₁⟩ := nonempty_bar2_map_subtype L Y₁
      refine inFSq_sup_of_isSubnormal_rankOne
        CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.w3Lem45_2Chief_holds
        (isSubnormal_sup_of_le_of_isComponentOf hcomp hTY hK₁L hinv₁) ?_
        (hsylH K₁ (hK₁L.trans hLY)) (Or.inl (LieModel.of_mulEquiv e₁ hL2₁))
      rw [hK₁, ← Subgroup.map_commutator, hperf₁]
    have hcardS : Nat.card S = Nat.card ↥(T ⊓ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ L ≤ L)).toEquiv
    have hcardK₂ : Nat.card K₂ = 3 * Nat.card ↥(T ⊓ L) := by
      rw [hK₂, Subgroup.card_map_of_injective L.subtype_injective, hcardX₂, hcardS]
    have hTLleK₂ : T ⊓ L ≤ K₂ := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hSX₂ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hinf₂ : T ⊓ K₂ = T ⊓ L := by
      refine le_antisymm ?_ ?_
      · intro x hx
        exact Subgroup.mem_inf.mpr
          ⟨(Subgroup.mem_inf.mp hx).1, hK₂L (Subgroup.mem_inf.mp hx).2⟩
      · intro x hx
        exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hTLleK₂ hx⟩
    have hidx₂ : (T ⊓ L).relIndex K₂ = 3 := by
      have h := Subgroup.relIndex_mul_card (T ⊓ L) K₂
      rw [inf_eq_left.mpr hTLleK₂, hcardK₂] at h
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
    have hTK₂ : T ≤ Subgroup.normalizer (K₂ : Set (MulAut W)) := fun t ht =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hinv₂ t ht (hTN ht))
    have hH₂card : Nat.card ↥(K₂ ⊔ T) = 3 * Nat.card T := by
      have h := Subgroup.relIndex_mul_card T (K₂ ⊔ T)
      rw [inf_eq_left.mpr le_sup_right, sup_comm K₂ T,
        (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hTK₂).1,
        hinf₂, hidx₂] at h
      rw [sup_comm K₂ T]
      exact h.symm
    have h3dvd : 3 ∣ Nat.card K₂ := by
      rw [hcardK₂]; exact dvd_mul_right 3 _
    obtain ⟨y₂, hy₂⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
    let A₂ : Subgroup (MulAut W) := Subgroup.zpowers (y₂ : MulAut W)
    have hA₂K : A₂ ≤ K₂ := Subgroup.zpowers_le.mpr y₂.2
    have hA₂card : Nat.card A₂ = 3 := by
      rw [show Nat.card A₂ = orderOf (y₂ : MulAut W) from Nat.card_zpowers _,
        Subgroup.orderOf_coe, hy₂]
    have hA₂inf : A₂ ⊓ T = ⊥ := by
      refine Subgroup.inf_eq_bot_of_coprime ?_
      rw [hA₂card]
      obtain ⟨k, hk⟩ := hsyl.2.1.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
    have hH₂perm : Permutes A₂ T := by
      refine CFSG.Quasithin.H.L3Wr.permute_of_card hA₂inf ?_
      have hle : A₂ ⊔ T ≤ K₂ ⊔ T := sup_le (hA₂K.trans le_sup_left) le_sup_right
      calc Nat.card ↥(A₂ ⊔ T) ≤ Nat.card ↥(K₂ ⊔ T) :=
            Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
        _ = 3 * Nat.card T := hH₂card
        _ = Nat.card A₂ * Nat.card T := by rw [hA₂card]
    have hInF₂ : InFSq 1 (K₂ ⊔ T) := by
      have hle : A₂ ⊔ T ≤ K₂ ⊔ T := sup_le (hA₂K.trans le_sup_left) le_sup_right
      have hcardsup : Nat.card ↥(A₂ ⊔ T) = Nat.card ↥(K₂ ⊔ T) := by
        rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hH₂perm hA₂inf,
          hA₂card, hH₂card]
      have heq : A₂ ⊔ T = K₂ ⊔ T :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardsup.symm)
      rw [← heq]
      exact inFSq_one_of_prime_mul_two_group A₂ T 3 Nat.prime_three (by norm_num) hA₂card
        hsyl.2.1 hH₂perm
    have hgenL : K₁ ⊔ K₂ = L := by
      have h := congrArg (Subgroup.map L.subtype) hgen
      rwa [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    have hLle : L ≤ K₁ ⊔ K₂ ⊔ T := by
      rw [← hgenL]
      exact le_sup_left
    exact bParam_le_of_pair_inFSq hW hLT hcomp hsyl hO2 hfix hK₁L hK₂L hLle hInF₁ hInF₂
      (by omega)
  ·
    obtain ⟨Y₁, Y₂, hperf₁, hperf₂, hL2₁, hL2₂, hgen, hinv⟩ := hA ↥L n hge hD S hS
    set K₁ : Subgroup (MulAut W) := Y₁.map L.subtype with hK₁
    set K₂ : Subgroup (MulAut W) := Y₂.map L.subtype with hK₂
    have hK₁L : K₁ ≤ L := Subgroup.map_subtype_le Y₁
    have hK₂L : K₂ ≤ L := Subgroup.map_subtype_le Y₂
    have hinv₁ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
        K₁.map (MulAut.conj t).toMonoidHom = K₁ :=
      fun t ht htN => map_conj_eq_of_invariant T L S hSdef Y₁
        (fun α hα => (hinv α hα).1) t ht htN
    have hinv₂ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
        K₂.map (MulAut.conj t).toMonoidHom = K₂ :=
      fun t ht htN => map_conj_eq_of_invariant T L S hSdef Y₂
        (fun α hα => (hinv α hα).2) t ht htN
    have hInF₁ : InFSq (3 * n) (K₁ ⊔ T) := by
      obtain ⟨e₁⟩ := nonempty_bar2_map_subtype L Y₁
      refine inFSq_sup_of_isSubnormal_rankOne
        CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.w3Lem45_2Chief_holds
        (isSubnormal_sup_of_le_of_isComponentOf hcomp hTY hK₁L hinv₁) ?_
        (hsylH K₁ (hK₁L.trans hLY)) (Or.inl (LieModel.of_mulEquiv e₁ hL2₁))
      rw [hK₁, ← Subgroup.map_commutator, hperf₁]
    have hInF₂ : InFSq n (K₂ ⊔ T) := by
      obtain ⟨e₂⟩ := nonempty_bar2_map_subtype L Y₂
      refine inFSq_sup_of_isSubnormal_rankOne
        CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.w3Lem45_2Chief_holds
        (isSubnormal_sup_of_le_of_isComponentOf hcomp hTY hK₂L hinv₂) ?_
        (hsylH K₂ (hK₂L.trans hLY)) (Or.inl (LieModel.of_mulEquiv e₂ hL2₂))
      rw [hK₂, ← Subgroup.map_commutator, hperf₂]
    have hLle : L ≤ K₁ ⊔ K₂ ⊔ T := by
      have hmap := congrArg (Subgroup.map L.subtype) hgen
      rw [Subgroup.map_sup, Subgroup.map_sup, hSdef, Subgroup.subgroupOf_map_subtype,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
      calc L = Y₁.map L.subtype ⊔ Y₂.map L.subtype ⊔ T ⊓ L ⊓ L := hmap.symm
        _ ≤ K₁ ⊔ K₂ ⊔ T := by
          rw [hK₁, hK₂]
          exact sup_le le_sup_left ((inf_le_left.trans inf_le_left).trans le_sup_right)
    exact bParam_le_of_pair_inFSq hW hLT hcomp hsyl hO2 hfix hK₁L hK₂L hLle hInF₁ hInF₂
      (by omega)

theorem w4Lem4_17TrialityD4N_holds :
    W4Lem4_17TrialityD4N := by
  intro W _ _ hW Y L T n _ _ hLT hcomp hsyl hO2 hfix hTN hD
  exact bParam_le_four_mul_of_is3D4_of_kFacts k_3D4ParabolicGen_holds
    k_3D4TwoParabolicGen_holds hW hLT hcomp hsyl hO2 hfix hTN hD

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
