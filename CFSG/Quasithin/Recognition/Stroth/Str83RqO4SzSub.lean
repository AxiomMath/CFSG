module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackBasic
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
import CFSG.Quasithin.Recognition.Stroth.F112Tree
import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Quasithin.EmptyFaithful.S152Y06

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5
open CFSG.Quasithin.RonanF13 (HallTwoPrime)

variable {G : Type} [Group G] [Finite G]

private noncomputable def szModelEquiv {L : Subgroup G} {a : ℕ}
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) :
    oTwoQuot ↥L ≃* CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1)) :=
  (Classical.choice hSz).trans (Classical.choice
    (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a))

private theorem sup_imageOTwoQuot_eq_normalizer {L T D : Subgroup G}
    {a : ℕ} (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L)
    (hD : HallTwoPrime D (L ⊓ normalizer (T : Set G))) :
    imageOTwoQuot L T ⊔ imageOTwoQuot L D =
      Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ L := hT.le
  have hQL : pCoreOf 2 L ≤ T := hT.pCoreOf_le
  have hDL : D ≤ L := hD.1.trans inf_le_left
  set Tq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L T with hTq
  set Dq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L D with hDq
  obtain ⟨S, hScoe⟩ := exists_sylow_imageOTwoQuot hT
  have hTqcard : Nat.card Tq = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hTq, ← hScoe]
    exact (CFSG.RankThree.S4Free.Suzuki.card_sylow_and_center ha
      (GaloisField.card 2 (2 * a + 1) (by omega)) (szModelEquiv hSz) S).1
  have hDqcard : Nat.card Dq = 2 ^ (2 * a + 1) - 1 := by
    rw [hDq, QA12.card_image_of_odd hDL hD.2.1,
      card_hallTwoPrime_eq_sz (L := L) (T := T) (D := D) ha hSz hT hD]
  have hqodd : Odd (2 ^ (2 * a + 1) - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hdisj : Dq ⊓ Tq = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hDqcard, hTqcard, ← pow_mul,
      show (2 * a + 1) * 2 = 2 * (2 * a + 1) by ring]
    exact hqodd.coprime_two_right.pow_right (2 * (2 * a + 1))
  have hDqN : Dq ≤ Subgroup.normalizer (Tq : Set (oTwoQuot ↥L)) := by
    have hN : Subgroup.normalizer (Tq : Set (oTwoQuot ↥L)) =
        imageOTwoQuot L (L ⊓ Subgroup.normalizer (T : Set G)) := by
      rw [hTq]
      exact QA12.normalizer_image_eq hTL hQL
    rw [hN]
    exact imageOTwoQuot_mono hD.1
  have hsup_le : Tq ⊔ Dq ≤ Subgroup.normalizer (Tq : Set (oTwoQuot ↥L)) :=
    sup_le Subgroup.le_normalizer hDqN
  have hNcard : Nat.card (Subgroup.normalizer (Tq : Set (oTwoQuot ↥L))) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
    rw [hTq]
    exact card_normalizer_imageOTwoQuot_sz ha hSz hT
  have hcard_sup : Nat.card ↥(Tq ⊔ Dq) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
    have h := C5.card_sup_mul_card_inf_of_le_normalizer (A := Dq) (B := Tq) hDqN
    have hbot : Nat.card ↥(Dq ⊓ Tq) = 1 := by rw [hdisj]; simp
    rw [hbot, mul_one] at h
    rw [sup_comm]
    rw [h, hDqcard, hTqcard, mul_comm]
  have hN_eq : Tq ⊔ Dq = Subgroup.normalizer (Tq : Set (oTwoQuot ↥L)) := by
    refine Subgroup.eq_of_le_of_card_ge hsup_le ?_
    rw [hNcard, hcard_sup]
  simpa only [hTq, hDq] using hN_eq

private theorem image_eq_bot_or_eq_center_or_eq_sylow
    {L T D X : Subgroup G} {a : ℕ} (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a))
    (hT : IsSylowTwoOf T L) (hD : HallTwoPrime D (L ⊓ normalizer (T : Set G)))
    (hXT : X ≤ T) (hTX : T ≤ normalizer (X : Set G))
    (hXD : D ≤ normalizer (X : Set G)) (S : Sylow 2 (oTwoQuot ↥L))
    (hScoe : (S : Subgroup (oTwoQuot ↥L)) = imageOTwoQuot L T) :
    imageOTwoQuot L X = ⊥ ∨
      imageOTwoQuot L X = ((S : Subgroup (oTwoQuot ↥L)) ⊓
        Subgroup.centralizer ((S : Subgroup (oTwoQuot ↥L)) : Set _)) ∨
      imageOTwoQuot L X = (S : Subgroup (oTwoQuot ↥L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNX : Subgroup.normalizer ((S : Subgroup (oTwoQuot ↥L)) : Set _) ≤
      Subgroup.normalizer (imageOTwoQuot L X : Set (oTwoQuot ↥L)) := by
    rw [hScoe, ← sup_imageOTwoQuot_eq_normalizer ha hSz hT hD]
    exact sup_le (S152Y.imageOTwoQuot_le_normalizer (M := L) hTX)
      (S152Y.imageOTwoQuot_le_normalizer (M := L) hXD)
  have hWS : imageOTwoQuot L X ≤ (S : Subgroup (oTwoQuot ↥L)) := by
    rw [hScoe]
    exact imageOTwoQuot_mono hXT
  exact CFSG.RankThree.S4Free.Suzuki.eq_bot_or_eq_center_or_eq_sylow
    (K := GaloisField 2 (2 * a + 1)) ha
    (GaloisField.card 2 (2 * a + 1) (by omega)) (szModelEquiv hSz) S hWS hNX

private theorem le_pCoreOf_of_imageOTwoQuot_eq_bot {L T X : Subgroup G} (hTL : T ≤ L)
    (hXT : X ≤ T) (h : imageOTwoQuot L X = ⊥) : X ≤ pCoreOf 2 L := by
  intro x hx
  have hxL : x ∈ L := hTL (hXT hx)
  have hmk : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) ∈ imageOTwoQuot L X :=
    mem_imageOTwoQuot_iff.mpr ⟨x, hxL, hx, rfl⟩
  rw [h, Subgroup.mem_bot] at hmk
  exact (mk_eq_one_iff_mem_pCoreOf ⟨x, hxL⟩).mp hmk

private theorem sq_mem_and_mem_sup_of_imageOTwoQuot_eq_center
    {L T X : Subgroup G} {a : ℕ} (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a))
    (hT : IsSylowTwoOf T L) (hXT : X ≤ T) (S : Sylow 2 (oTwoQuot ↥L))
    (hScoe : (S : Subgroup (oTwoQuot ↥L)) = imageOTwoQuot L T)
    (h : imageOTwoQuot L X = ((S : Subgroup (oTwoQuot ↥L)) ⊓
      Subgroup.centralizer ((S : Subgroup (oTwoQuot ↥L)) : Set _))) :
    (∀ x ∈ X, x * x ∈ pCoreOf 2 L) ∧
      ∀ x ∈ T, x * x ∈ pCoreOf 2 L → x ∈ X ⊔ pCoreOf 2 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ L := hT.le
  have hZmem := (sz_center_card_and_mem ha (szModelEquiv hSz) S).2
  constructor
  · intro x hx
    have hxT : x ∈ T := hXT hx
    have hxL : x ∈ L := hTL hxT
    have hmkZ : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) ∈
        ((S : Subgroup (oTwoQuot ↥L)) ⊓
          Subgroup.centralizer ((S : Subgroup (oTwoQuot ↥L)) : Set _)) := by
      rw [← h]
      exact mem_imageOTwoQuot_iff.mpr ⟨x, hxL, hx, rfl⟩
    have hsq := (hZmem _).mp hmkZ |>.2
    have hmul : (QuotientGroup.mk (⟨x, hxL⟩ * ⟨x, hxL⟩) : oTwoQuot ↥L) = 1 := by
      rw [QuotientGroup.mk_mul]
      exact hsq
    have hmem := (mk_eq_one_iff_mem_pCoreOf (⟨x, hxL⟩ * ⟨x, hxL⟩)).mp hmul
    simpa using hmem
  · intro x hxT hxx
    have hxL : x ∈ L := hTL hxT
    have hmkS : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) ∈ (S : Subgroup _) := by
      rw [hScoe]
      exact mem_imageOTwoQuot_iff.mpr ⟨x, hxL, hxT, rfl⟩
    have hmk2 : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) *
        (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) = 1 := by
      rw [← QuotientGroup.mk_mul]
      exact (mk_eq_one_iff_mem_pCoreOf (⟨x, hxL⟩ * ⟨x, hxL⟩)).mpr (by simpa using hxx)
    have hmkZ : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) ∈
        ((S : Subgroup (oTwoQuot ↥L)) ⊓
          Subgroup.centralizer ((S : Subgroup (oTwoQuot ↥L)) : Set _)) :=
      (hZmem _).mpr ⟨hmkS, hmk2⟩
    have hmkX : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) ∈ imageOTwoQuot L X := by
      rw [h]
      exact hmkZ
    exact mem_sup_pCoreOf_of_mk_mem (M := L) (A := X) (x := ⟨x, hxL⟩) hmkX

private theorem le_sup_of_imageOTwoQuot_eq_sylow {L T X : Subgroup G} (hTL : T ≤ L)
    (S : Sylow 2 (oTwoQuot ↥L))
    (hScoe : (S : Subgroup (oTwoQuot ↥L)) = imageOTwoQuot L T)
    (h : imageOTwoQuot L X = (S : Subgroup (oTwoQuot ↥L))) : T ≤ X ⊔ pCoreOf 2 L := by
  intro x hxT
  have hxL : x ∈ L := hTL hxT
  have hmkS : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) ∈ (S : Subgroup _) := by
    rw [hScoe]
    exact mem_imageOTwoQuot_iff.mpr ⟨x, hxL, hxT, rfl⟩
  have hmkX : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) ∈ imageOTwoQuot L X := by
    rw [h]
    exact hmkS
  exact mem_sup_pCoreOf_of_mk_mem (M := L) (A := X) (x := ⟨x, hxL⟩) hmkX

theorem le_or_sq_or_le_of_sz {L T D X : Subgroup G} {a : ℕ}
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L)
    (hD : HallTwoPrime D (L ⊓ normalizer (T : Set G))) (hXT : X ≤ T)
    (hTX : T ≤ normalizer (X : Set G)) (hXD : D ≤ normalizer (X : Set G)) :
    X ≤ pCoreOf 2 L ∨
      ((∀ x ∈ X, x * x ∈ pCoreOf 2 L) ∧ ∀ x ∈ T, x * x ∈ pCoreOf 2 L → x ∈ X ⊔ pCoreOf 2 L) ∨
      T ≤ X ⊔ pCoreOf 2 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hScoe⟩ := exists_sylow_imageOTwoQuot hT
  rcases image_eq_bot_or_eq_center_or_eq_sylow ha hSz hT hD hXT hTX hXD S hScoe with
    hbot | hcen | htop
  · exact Or.inl (le_pCoreOf_of_imageOTwoQuot_eq_bot hT.le hXT hbot)
  · exact Or.inr (Or.inl
      (sq_mem_and_mem_sup_of_imageOTwoQuot_eq_center ha hSz hT hXT S hScoe hcen))
  · exact Or.inr (Or.inr (le_sup_of_imageOTwoQuot_eq_sylow hT.le S hScoe htop))

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem inf_sup_normalizer_eq {L1 L2 S : Subgroup G}
    (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    (L1 ⊔ S) ⊓ Subgroup.normalizer (S : Set G) = S ⊔ t.D1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : F112HypW L1 L2 S := hfr.hF
  have hH : Hyp111 L1 L2 S := hF.1
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hH hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hB1N : borelOf L1 S ≤ Subgroup.normalizer (S : Set G) := by
    have hB1Q : borelOf L1 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
      ((F1.borelOf_le L1 S).trans (le_sup_left : L1 ≤ P1 L1 L2 S)).trans
        (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
    have h := F1.le_normalizer_sup (F1.borelOf_le_normalizer L1 S) hB1Q
    rwa [← hS1] at h
  have hD1N : t.D1 ≤ Subgroup.normalizer (S : Set G) :=
    (t.hD1sup.symm ▸ (le_sup_right : t.D1 ≤ (S ⊓ L1) ⊔ t.D1)).trans hB1N
  have hD1L1 : t.D1 ≤ L1 :=
    (t.hD1sup.symm ▸ (le_sup_right : t.D1 ≤ (S ⊓ L1) ⊔ t.D1)).trans (F1.borelOf_le L1 S)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxH, hxN⟩ := Subgroup.mem_inf.mp hx
    rw [sup_comm] at hxH
    obtain ⟨s, hs, l, hl, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer
        (H := S) (K := L1) hH.h1.normalizes).mp hxH
    have hlN : l ∈ Subgroup.normalizer (S : Set G) := by
      have hsN : s ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer hs
      have h := (Subgroup.normalizer (S : Set G)).mul_mem
        ((Subgroup.normalizer (S : Set G)).inv_mem hsN) hxN
      simpa [mul_assoc] using h
    have hlB : l ∈ borelOf L1 S :=
      Subgroup.mem_inf.mpr ⟨hl,
        A4.mem_normalizer_inf (A := S) (B := L1) hlN (Subgroup.le_normalizer hl)⟩
    rw [t.hD1sup] at hlB
    have hle : (S ⊓ L1) ⊔ t.D1 ≤ S ⊔ t.D1 := by
      refine sup_le ?_ ?_
      · exact inf_le_left.trans le_sup_left
      · exact le_sup_right
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (hle hlB)
  · exact sup_le (le_inf le_sup_right Subgroup.le_normalizer)
      (le_inf (hD1L1.trans le_sup_left) hD1N)

private theorem hallTwoPrime_D1 {L1 L2 S : Subgroup G}
    (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    HallTwoPrime t.D1 ((L1 ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : Hyp111 L1 L2 S := hfr.hF.1
  have hNA := t.inf_sup_normalizer_eq hfr
  rw [hNA]
  have hD1N : t.D1 ≤ Subgroup.normalizer (S : Set G) := by
    have h1 : t.D1 ≤ (L1 ⊔ S) ⊓ Subgroup.normalizer (S : Set G) := by
      rw [hNA]
      exact le_sup_right
    exact h1.trans inf_le_right
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH.h1.pgroup
  have hdisj : t.D1 ⊓ S = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hn]
    exact t.hD1hall.2.1.coprime_two_right.pow_right n
  refine ⟨le_sup_right, t.hD1hall.2.1, n, ?_⟩
  have hrel := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := t.D1) (K := S) hD1N).1
  rw [sup_comm, hrel, hdisj, Subgroup.relIndex_bot_left, hn]

theorem trichotomy_Qv_zero {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {X : Subgroup G} (hXS : X ≤ S) (hSX : S ≤ normalizer (X : Set G))
    (hKX : t.K ≤ normalizer (X : Set G)) :
    X ≤ t.Qv 0 ∨ ((∀ x ∈ X, x * x ∈ t.Qv 0) ∧ ∀ s ∈ S, s * s ∈ t.Qv 0 → s ∈ X ⊔ t.Qv 0) ∨
      S ≤ X ⊔ t.Qv 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : F112HypW L1 L2 S := hfr.hF
  have hH : Hyp111 L1 L2 S := hF.1
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hH hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hsup : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup]
    exact pCoreOf_sup_pCoreOf hH
  have hSyl : IsSylowTwoOf S (L1 ⊔ S) := by
    refine F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF) le_sup_right ?_
    exact sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hSzH : Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Sz a) :=
    ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr (MulEquiv.subgroupCongr hsup)).trans
      ((oTwoQuotSupEquiv hH).trans (Classical.choice hfr.hSz))⟩
  have hHall := t.hallTwoPrime_D1 hfr
  have hmain := le_or_sq_or_le_of_sz (L := L1 ⊔ S) (T := S) (D := t.D1) (X := X)
    hfr.ha hSzH hSyl hHall hXS hSX (fun d hd => hKX (Subgroup.mem_sup_left hd))
  simpa [hpCore, t.Qv_zero] using hmain

end Track

end CFSG.Quasithin.Stroth.Rq

end
