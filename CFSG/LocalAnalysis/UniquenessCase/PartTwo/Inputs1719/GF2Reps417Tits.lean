module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Delta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsFourSixteenHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TitsParabolicHolds
public import CFSG.LocalAnalysis.WeakClosure81.InFSqPrimeTwoGroup
public import CFSG.Quasithin.Background.HL3WrNPrime
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81

theorem bParam_le_two_of_isTits_of_le_normalizer
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    (hTN : T ≤ Subgroup.normalizer (L : Set (MulAut W))) (hT : IsTits ↥L) :
    bParam L Y ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTY : T ≤ Y := hsyl.1
  have hLY : L ≤ Y := hcomp.1
  have hLM : LieModel ↥L .Tits 0 2 1 :=
    (CFSG.Blueprint.LieModel.reeTits_iff (t := .Tits) (n := 0) (p := 2) (f := 1)
      (by decide)).2 ⟨rfl, hT⟩
  have hTL : IsSylowIn 2 (T ⊓ L) L :=
    CFSG.Quasithin.F6.isSylowIn_inf_of_isSubnormal hcomp.2.1 hsyl
  set S : Subgroup ↥L := (T ⊓ L).subgroupOf L with hSdef
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, hTL.2.1.comap_of_injective L.subtype L.subtype_injective, ?_⟩
    have h1 : (S.subgroupOf (⊤ : Subgroup ↥L)).index = S.index :=
      Subgroup.relIndex_top_right _
    rw [h1]
    exact hTL.2.2
  obtain ⟨P₁, P₂, hSP₁, hSP₂, hcard₁, hcard₂, hsup, hinv⟩ :=
    k_TitsParabolicGen_holds ↥L hLM S hS
  set K₁ : Subgroup (MulAut W) := P₁.map L.subtype with hK₁
  set K₂ : Subgroup (MulAut W) := P₂.map L.subtype with hK₂
  have hK₁L : K₁ ≤ L := Subgroup.map_subtype_le P₁
  have hK₂L : K₂ ≤ L := Subgroup.map_subtype_le P₂
  have hcompat : ∀ (t : MulAut W) (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)))
      (Z : Subgroup ↥L), (Z.map L.subtype).map (MulAut.conj t).toMonoidHom =
        (Z.map (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom).map L.subtype := by
    intro t htN Z
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hαS : ∀ (t : MulAut W) (ht : t ∈ T)
      (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))),
      S.map (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom = S := by
    intro t ht htN
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
  have hKinv : ∀ (Z : Subgroup ↥L), (∀ α : MulAut ↥L, S.map α.toMonoidHom = S →
      Z.map α.toMonoidHom = Z) → ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      (Z.map L.subtype).map (MulAut.conj t).toMonoidHom = Z.map L.subtype := by
    intro Z hZ t ht htN
    rw [hcompat t htN Z, hZ _ (hαS t ht htN)]
  have hinv₁ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      K₁.map (MulAut.conj t).toMonoidHom = K₁ :=
    hKinv P₁ (fun α hα => (hinv α hα).1)
  have hinv₂ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      K₂.map (MulAut.conj t).toMonoidHom = K₂ :=
    hKinv P₂ (fun α hα => (hinv α hα).2)
  have hTK₁ : T ≤ Subgroup.normalizer (K₁ : Set (MulAut W)) := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hinv₁ t ht (hTN ht))
  have hTK₂ : T ≤ Subgroup.normalizer (K₂ : Set (MulAut W)) := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hinv₂ t ht (hTN ht))
  have hcardS : Nat.card S = Nat.card ↥(T ⊓ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ L ≤ L)).toEquiv
  have hcardK₁ : Nat.card K₁ = 3 * Nat.card ↥(T ⊓ L) := by
    rw [hK₁, Subgroup.card_map_of_injective L.subtype_injective, hcard₁, hcardS]
  have hcardK₂ : Nat.card K₂ = 5 * Nat.card ↥(T ⊓ L) := by
    rw [hK₂, Subgroup.card_map_of_injective L.subtype_injective, hcard₂, hcardS]
  have hTLleK₁ : T ⊓ L ≤ K₁ := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hSP₁ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hTLleK₂ : T ⊓ L ≤ K₂ := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hSP₂ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hinf₁ : T ⊓ K₁ = T ⊓ L := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_inf.mp hx).1, hK₁L (Subgroup.mem_inf.mp hx).2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hTLleK₁ hx⟩
  have hinf₂ : T ⊓ K₂ = T ⊓ L := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_inf.mp hx).1, hK₂L (Subgroup.mem_inf.mp hx).2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hTLleK₂ hx⟩
  have hidx₁ : (T ⊓ L).relIndex K₁ = 3 := by
    have h := Subgroup.relIndex_mul_card (T ⊓ L) K₁
    rw [inf_eq_left.mpr hTLleK₁, hcardK₁] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hidx₂ : (T ⊓ L).relIndex K₂ = 5 := by
    have h := Subgroup.relIndex_mul_card (T ⊓ L) K₂
    rw [inf_eq_left.mpr hTLleK₂, hcardK₂] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hH₁card : Nat.card ↥(K₁ ⊔ T) = 3 * Nat.card T := by
    have h := Subgroup.relIndex_mul_card T (K₁ ⊔ T)
    rw [inf_eq_left.mpr le_sup_right, sup_comm K₁ T,
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hTK₁).1,
      hinf₁, hidx₁] at h
    rw [sup_comm K₁ T]
    exact h.symm
  have hH₂card : Nat.card ↥(K₂ ⊔ T) = 5 * Nat.card T := by
    have h := Subgroup.relIndex_mul_card T (K₂ ⊔ T)
    rw [inf_eq_left.mpr le_sup_right, sup_comm K₂ T,
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hTK₂).1,
      hinf₂, hidx₂] at h
    rw [sup_comm K₂ T]
    exact h.symm
  have h3dvd : 3 ∣ Nat.card K₁ := by
    rw [hcardK₁]; exact dvd_mul_right 3 _
  have h5dvd : 5 ∣ Nat.card K₂ := by
    rw [hcardK₂]; exact dvd_mul_right 5 _
  obtain ⟨y₁, hy₁⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  obtain ⟨y₂, hy₂⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  let A₁ : Subgroup (MulAut W) := Subgroup.zpowers (y₁ : MulAut W)
  let A₂ : Subgroup (MulAut W) := Subgroup.zpowers (y₂ : MulAut W)
  have hA₁K : A₁ ≤ K₁ := Subgroup.zpowers_le.mpr y₁.2
  have hA₂K : A₂ ≤ K₂ := Subgroup.zpowers_le.mpr y₂.2
  have hA₁card : Nat.card A₁ = 3 := by
    rw [show Nat.card A₁ = orderOf (y₁ : MulAut W) from Nat.card_zpowers _,
      Subgroup.orderOf_coe, hy₁]
  have hA₂card : Nat.card A₂ = 5 := by
    rw [show Nat.card A₂ = orderOf (y₂ : MulAut W) from Nat.card_zpowers _,
      Subgroup.orderOf_coe, hy₂]
  have hA₁inf : A₁ ⊓ T = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hA₁card]
    obtain ⟨k, hk⟩ := hsyl.2.1.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  have hA₂inf : A₂ ⊓ T = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hA₂card]
    obtain ⟨k, hk⟩ := hsyl.2.1.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 5 2)
  have hH₁perm : Permutes A₁ T := by
    refine CFSG.Quasithin.H.L3Wr.permute_of_card hA₁inf ?_
    have hle : A₁ ⊔ T ≤ K₁ ⊔ T := sup_le (hA₁K.trans le_sup_left) le_sup_right
    calc Nat.card ↥(A₁ ⊔ T) ≤ Nat.card ↥(K₁ ⊔ T) :=
          Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
      _ = 3 * Nat.card T := hH₁card
      _ = Nat.card A₁ * Nat.card T := by rw [hA₁card]
  have hH₂perm : Permutes A₂ T := by
    refine CFSG.Quasithin.H.L3Wr.permute_of_card hA₂inf ?_
    have hle : A₂ ⊔ T ≤ K₂ ⊔ T := sup_le (hA₂K.trans le_sup_left) le_sup_right
    calc Nat.card ↥(A₂ ⊔ T) ≤ Nat.card ↥(K₂ ⊔ T) :=
          Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
      _ = 5 * Nat.card T := hH₂card
      _ = Nat.card A₂ * Nat.card T := by rw [hA₂card]
  have hInF₁ : InFSq 1 (K₁ ⊔ T) := by
    have hle : A₁ ⊔ T ≤ K₁ ⊔ T := sup_le (hA₁K.trans le_sup_left) le_sup_right
    have hcardsup : Nat.card ↥(A₁ ⊔ T) = Nat.card ↥(K₁ ⊔ T) := by
      rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hH₁perm hA₁inf,
        hA₁card, hH₁card]
    have heq : A₁ ⊔ T = K₁ ⊔ T :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardsup.symm)
    rw [← heq]
    exact CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group A₁ T 3
      Nat.prime_three (by norm_num) hA₁card hsyl.2.1 hH₁perm
  have hInF₂ : InFSq 1 (K₂ ⊔ T) := by
    have hle : A₂ ⊔ T ≤ K₂ ⊔ T := sup_le (hA₂K.trans le_sup_left) le_sup_right
    have hcardsup : Nat.card ↥(A₂ ⊔ T) = Nat.card ↥(K₂ ⊔ T) := by
      rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hH₂perm hA₂inf,
        hA₂card, hH₂card]
    have heq : A₂ ⊔ T = K₂ ⊔ T :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardsup.symm)
    rw [← heq]
    exact CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group A₂ T 5
      Nat.prime_five (by norm_num) hA₂card hsyl.2.1 hH₂perm
  have hKsup : K₁ ⊔ K₂ = L := by
    have h := congrArg (Subgroup.map L.subtype) hsup
    rwa [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hsup_eq : (K₁ ⊔ T) ⊔ (K₂ ⊔ T) = (K₁ ⊔ K₂) ⊔ T := by
    refine le_antisymm ?_ ?_
    · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_left.trans le_sup_right
      · exact le_sup_right.trans le_sup_left
  have hsupΔ : (⨆ H ∈ ({K₁ ⊔ T, K₂ ⊔ T} : Set (Subgroup (MulAut W))), H) = Y := by
    rw [iSup_insert, iSup_singleton, hsup_eq, hKsup, hLT]
  have hsum : fIndexSum ({K₁ ⊔ T, K₂ ⊔ T} : Set (Subgroup (MulAut W))) ≤
      ((2 : ℕ) : ℕ∞) := by
    by_cases h12 : K₁ ⊔ T = K₂ ⊔ T
    · rw [h12, Set.pair_eq_singleton, fIndexSum, finsum_mem_singleton]
      exact (fIndex_le_iff.mpr hInF₂).trans (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
    · rw [fIndexSum, finsum_mem_pair h12]
      calc fIndex (K₁ ⊔ T) + fIndex (K₂ ⊔ T) ≤ (1 : ℕ∞) + 1 :=
            add_le_add (fIndex_le_iff.mpr hInF₁) (fIndex_le_iff.mpr hInF₂)
        _ = ((2 : ℕ) : ℕ∞) := by push_cast; ring
  refine bParam_le_of_fIndexSum_le w4Lem4_16_holds hW hLT hcomp hsyl hO2 hfix
    ((Set.finite_singleton _).insert _) ?_ hsupΔ hsum
  intro H hH
  rcases hH with rfl | hH
  · exact ⟨sup_le (hK₁L.trans hLY) hTY, le_sup_right⟩
  · rw [Set.mem_singleton_iff.mp hH]
    exact ⟨sup_le (hK₂L.trans hLY) hTY, le_sup_right⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
