module

public import CFSG.Quasithin.Background.RonanF13Hall
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Quot
public import CFSG.Quasithin.EmptyFaithful.S152Y06
public import CFSG.Quasithin.Recognition.St84.L2Group
public import CFSG.RankThree.S4Free.StellmacherSzSylow
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.Quasithin.H13.L32NLem1444d
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernelBasic
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement MatrixGroups
open CFSG.Quasithin.RonanF13 (HallTwoPrime)

variable {G : Type} [Group G] [Finite G]

private theorem odd_mul_two_pow_eq {d q m k : ℕ} (hd : Odd d) (hq : Odd (q - 1))
    (h : d * 2 ^ k = 2 ^ m * (q - 1)) : d = q - 1 := by
  have hdm : d ∣ q - 1 := by
    have hcop : Nat.Coprime d (2 ^ m) := hd.coprime_two_right.pow_right m
    apply hcop.dvd_of_dvd_mul_right
    rw [mul_comm (q - 1) (2 ^ m), ← h]
    exact dvd_mul_right d (2 ^ k)
  have hqd : q - 1 ∣ d := by
    have hcop : Nat.Coprime (q - 1) (2 ^ k) := hq.coprime_two_right.pow_right k
    apply hcop.dvd_of_dvd_mul_right
    rw [h]
    exact dvd_mul_left (q - 1) (2 ^ m)
  exact Nat.dvd_antisymm hdm hqd

theorem mem_sup_pCoreOf_of_mk_mem {M A : Subgroup G} {x : ↥M}
    (hx : (QuotientGroup.mk x : OTwoQuot M) ∈ imageOTwoQuot M A) :
    (x : G) ∈ A ⊔ pCoreOf 2 M := by
  obtain ⟨a, haM, haA, ha⟩ := mem_imageOTwoQuot_iff.mp hx
  have hker : (QuotientGroup.mk (x * (⟨a, haM⟩ : ↥M)⁻¹) : OTwoQuot M) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← ha, mul_inv_cancel]
  have hpc : ((x * (⟨a, haM⟩ : ↥M)⁻¹ : ↥M) : G) ∈ pCoreOf 2 M :=
    (mk_eq_one_iff_mem_pCoreOf (x * (⟨a, haM⟩ : ↥M)⁻¹)).mp hker
  have hxeq : (x : G) = ((x * (⟨a, haM⟩ : ↥M)⁻¹ : ↥M) : G) * a := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hxeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hpc) (Subgroup.mem_sup_left haA)

theorem exists_sylow_imageOTwoQuot {L T : Subgroup G} (hT : IsSylowTwoOf T L) :
    ∃ S : Sylow 2 (oTwoQuot ↥L), (S : Subgroup (oTwoQuot ↥L)) = imageOTwoQuot L T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : pCoreOf 2 L ≤ T := hT.pCoreOf_le
  have hTq : IsSylowTwoOf (imageOTwoQuot L T) ⊤ := QA12.isSylowTwoOf_image_top hT hQ
  have hidx : ¬ 2 ∣ (imageOTwoQuot L T).index := by
    have heq : ((imageOTwoQuot L T).subgroupOf ⊤).index = (imageOTwoQuot L T).index := by
      have h1 := (Subgroup.relIndex_subgroupOf (H := imageOTwoQuot L T)
        (K := (⊤ : Subgroup (oTwoQuot ↥L))) (L := ⊤) le_rfl)
      simpa [Subgroup.subgroupOf_self] using h1
    intro h
    exact hTq.2.2 (heq.symm ▸ h)
  exact ⟨hTq.2.1.toSylow hidx, IsPGroup.toSylow_coe _ _⟩

private theorem card_normalizer_imageOTwoQuot_l2 {L T : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    Nat.card (Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))) =
      2 ^ f * (2 ^ f - 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hScoe⟩ := exists_sylow_imageOTwoQuot hT
  obtain ⟨e⟩ := hL2
  let U : Sylow 2 (PSL(2, GaloisField 2 f)) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hUcoe : (U : Subgroup (PSL(2, GaloisField 2 f))) =
      (imageOTwoQuot L T).map e.toMonoidHom := by
    have h := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
    simpa [U, hScoe] using h
  have hmap : (Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))).map e.toMonoidHom =
      Subgroup.normalizer ((U : Subgroup (PSL(2, GaloisField 2 f))) : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, ← hUcoe]
  refine (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm.trans ?_
  rw [hmap]
  exact CFSG.Walter.psl2_even_card_normalizer_sylow_two (f := f) (by omega) U

theorem card_hallTwoPrime_eq_l2 {L T D : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD : HallTwoPrime D (L ⊓ Subgroup.normalizer (T : Set G))) :
    Nat.card D = 2 ^ f - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ L := hT.le
  have hQ : pCoreOf 2 L ≤ T := hT.pCoreOf_le
  set Q : Subgroup G := pCoreOf 2 L with hQdef
  set M : Subgroup G := L ⊓ Subgroup.normalizer (T : Set G) with hMdef
  have hDM : D ≤ M := hD.1
  have hQM : Q ≤ M := le_inf (hQ.trans hTL) (hQ.trans (Subgroup.le_normalizer))
  obtain ⟨hDodd, k, hk⟩ := hD.2
  have hMcard : Nat.card M = Nat.card D * 2 ^ k := by
    have h := Subgroup.relIndex_mul_card (H := D) (K := M)
    rw [hk, inf_eq_left.mpr hDM, mul_comm] at h
    exact h.symm
  have hNq : Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) = imageOTwoQuot L M :=
    QA12.normalizer_image_eq hTL hQ
  have hMcard' : Nat.card M =
      Nat.card (Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))) * Nat.card Q := by
    have h := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul L M inf_le_left
    rw [← hNq, inf_eq_right.mpr hQM] at h
    exact h
  have hNcard := card_normalizer_imageOTwoQuot_l2 hf hL2 hT
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 L)
  have harith : Nat.card D * 2 ^ k = 2 ^ (m + f) * (2 ^ f - 1) := by
    have h1 : Nat.card D * 2 ^ k =
        Nat.card (Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))) * Nat.card Q := by
      rw [← hMcard, hMcard']
    rw [h1, hNcard, hm, pow_add]
    ring
  have hpowodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  exact odd_mul_two_pow_eq hDodd hpowodd harith

private theorem l2_sylow_le_of_torus {f : ℕ} (hf : 2 ≤ f)
    {V D' Y' : Subgroup (PSL(2, GaloisField 2 f))} (hV2 : IsPGroup 2 V)
    (hVidx : ¬ 2 ∣ V.index) (hD'card : Nat.card D' = 2 ^ f - 1)
    (hD'N : D' ≤ Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f))))
    (hY'V : Y' ≤ V) (hY'N : D' ≤ Subgroup.normalizer (Y' : Set (PSL(2, GaloisField 2 f))))
    (hY'ne : Y' ≠ ⊥) : V ≤ Y' := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Us : Sylow 2 (PSL(2, GaloisField 2 f)) := hV2.toSylow hVidx
  have hUcoe : (Us : Subgroup (PSL(2, GaloisField 2 f))) = V := IsPGroup.toSylow_coe _ _
  have hVcard : Nat.card V = 2 ^ f := by
    rw [← hUcoe]
    exact St84.psl2_sylow_two_card (by omega) Us
  have hdisj : D' ⊓ V = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hD'card, hVcard]
    exact (Nat.Even.sub_odd (Nat.one_le_two_pow)
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one).coprime_two_right.pow_right f
  have hNcardU : Nat.card (Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f)))) =
      2 ^ f * (2 ^ f - 1) := by
    rw [← hUcoe]
    exact CFSG.Walter.psl2_even_card_normalizer_sylow_two (f := f) (by omega) Us
  have hsup : D' ⊔ V = Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f))) := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hD'N Subgroup.le_normalizer) ?_
    have hrel := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := D') (K := V) hD'N).2
    have h1 := Subgroup.relIndex_mul_card (H := V) (K := D' ⊔ V)
    rw [hrel, hdisj, Subgroup.relIndex_bot_left,
      inf_eq_left.mpr (le_sup_right : V ≤ D' ⊔ V)] at h1
    rw [← h1, hD'card, hVcard, hNcardU]
    exact Nat.le_of_eq (mul_comm _ _)
  obtain ⟨z₀, hz₀Y', hz₀1⟩ := Y'.bot_or_exists_ne_one.resolve_left hY'ne
  have hz₀V : z₀ ∈ V := hY'V hz₀Y'
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]; exact Y'.one_mem
  · obtain ⟨d, hdD', hdv⟩ :=
      St84.psl2_torus_regular_on_sylow (f := f) (U := Us) (D := D')
        hf hdisj hsup z₀ hz₀V hz₀1 v hv hv1
    rw [← hdv]
    exact (Subgroup.mem_normalizer_iff.mp (hY'N hdD') z₀).mp hz₀Y'

section Vertex
variable {L T : Subgroup G}

theorem le_sup_pCoreOf_of_torus_of_l2 {D X : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD : HallTwoPrime D (L ⊓ Subgroup.normalizer (T : Set G)))
    (hXT : X ≤ T) (hXD : D ≤ Subgroup.normalizer (X : Set G)) (hX : ¬ X ≤ pCoreOf 2 L) :
    T ≤ X ⊔ pCoreOf 2 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ L := hT.le
  let Tq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L T
  let Xq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L X
  let Dq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L D
  have hDL : D ≤ L := hD.1.trans inf_le_left
  have hDcard : Nat.card D = 2 ^ f - 1 :=
    card_hallTwoPrime_eq_l2 (L := L) (T := T) (D := D) (f := f) hf hL2 hT hD
  have hDqcard : Nat.card Dq = 2 ^ f - 1 := by
    rw [QA12.card_image_of_odd hDL hD.2.1, hDcard]
  obtain ⟨S, hScoe⟩ := exists_sylow_imageOTwoQuot hT
  obtain ⟨e⟩ := hL2
  let U : Sylow 2 (PSL(2, GaloisField 2 f)) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hUcoe : (U : Subgroup (PSL(2, GaloisField 2 f))) = Tq.map e.toMonoidHom := by
    have h := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
    simpa [U, Tq, hScoe] using h
  let D' : Subgroup (PSL(2, GaloisField 2 f)) := Dq.map e.toMonoidHom
  have hD'card : Nat.card D' = 2 ^ f - 1 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hDqcard]
  have hNDq : Dq ≤ Subgroup.normalizer (Tq : Set (oTwoQuot ↥L)) := by
    rw [show Subgroup.normalizer (Tq : Set (oTwoQuot ↥L)) =
      imageOTwoQuot L (L ⊓ Subgroup.normalizer (T : Set G)) from
        QA12.normalizer_image_eq hTL hT.pCoreOf_le]
    exact imageOTwoQuot_mono hD.1
  have hD'N : D' ≤ Subgroup.normalizer ((U : Subgroup (PSL(2, GaloisField 2 f))) : Set _) := by
    have h := Subgroup.map_mono (f := e.toMonoidHom) hNDq
    rw [Subgroup.map_equiv_normalizer_eq] at h
    rw [← hUcoe] at h
    exact h
  have hXq_ne : Xq ≠ ⊥ := by
    intro hbot
    apply hX
    intro x hx
    have hmem : (QuotientGroup.mk ⟨x, hTL (hXT hx)⟩ : oTwoQuot ↥L) ∈ Xq :=
      mem_imageOTwoQuot_iff.mpr ⟨x, hTL (hXT hx), hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (mk_eq_one_iff_mem_pCoreOf ⟨x, hTL (hXT hx)⟩).mp hmem
  have hX'U : Xq.map e.toMonoidHom ≤ (U : Subgroup (PSL(2, GaloisField 2 f))) := by
    rw [hUcoe]
    exact Subgroup.map_mono (f := e.toMonoidHom) (imageOTwoQuot_mono hXT)
  have hX'N : D' ≤ Subgroup.normalizer (Xq.map e.toMonoidHom :
      Set (PSL(2, GaloisField 2 f))) := by
    have hXn : Dq ≤ Subgroup.normalizer (Xq : Set (oTwoQuot ↥L)) :=
      CFSG.Quasithin.S152Y.imageOTwoQuot_le_normalizer (M := L) (X := D) (Y := X) hXD
    have h := Subgroup.map_mono (f := e.toMonoidHom) hXn
    rw [Subgroup.map_equiv_normalizer_eq] at h
    exact h
  have hX'ne : Xq.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hXq_ne
    rw [← Subgroup.map_bot (f := e.toMonoidHom)] at hbot
    exact Subgroup.map_injective e.injective hbot
  have hUX' : (U : Subgroup (PSL(2, GaloisField 2 f))) ≤ Xq.map e.toMonoidHom :=
    l2_sylow_le_of_torus (f := f) hf (V := (U : Subgroup (PSL(2, GaloisField 2 f))))
      U.isPGroup' U.not_dvd_index hD'card hD'N hX'U hX'N hX'ne
  have hTq_le_Xq : Tq ≤ Xq := by
    intro y hy
    have hy' : e y ∈ (U : Subgroup (PSL(2, GaloisField 2 f))) := by
      rw [hUcoe]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hy
    have hx := hUX' hy'
    simpa using (Subgroup.mem_map_equiv.mp hx)
  intro t ht
  have hmemTq : (QuotientGroup.mk ⟨t, hTL ht⟩ : oTwoQuot ↥L) ∈ Tq :=
    mem_imageOTwoQuot_iff.mpr ⟨t, hTL ht, ht, rfl⟩
  exact mem_sup_pCoreOf_of_mk_mem (M := L) (A := X) (x := ⟨t, hTL ht⟩)
    (hTq_le_Xq hmemTq)


theorem sz_center_card_and_mem {Xq : Type*} [Group Xq]
    [Finite Xq] {a : ℕ} (ha : 1 ≤ a)
    (e : Xq ≃* CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1))) (S : Sylow 2 Xq) :
    Nat.card ↥((S : Subgroup Xq) ⊓ Subgroup.centralizer ((S : Subgroup Xq) : Set Xq)) =
        2 ^ (2 * a + 1) ∧
      ∀ z : Xq, z ∈ ((S : Subgroup Xq) ⊓ Subgroup.centralizer ((S : Subgroup Xq) : Set Xq)) ↔
        z ∈ (S : Subgroup Xq) ∧ z * z = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  obtain ⟨φ, hSφ, -⟩ := CFSG.RankThree.S4Free.Suzuki.exists_mulEquiv_sylow_eq hK e S
  have hZeq : (S : Subgroup Xq) ⊓ Subgroup.centralizer ((S : Subgroup Xq) : Set Xq) =
      (CFSG.LieType.Ree.suzukiZ0 a K).comap φ.toMonoidHom :=
    CFSG.RankThree.S4Free.Suzuki.inf_centralizer_eq_comap ha hK φ hSφ
  have hZcard : Nat.card ↥((S : Subgroup Xq) ⊓
      Subgroup.centralizer ((S : Subgroup Xq) : Set Xq)) = 2 ^ (2 * a + 1) := by
    rw [hZeq, Subgroup.comap_equiv_eq_map_symm',
      Subgroup.card_map_of_injective (f := φ.symm.toMonoidHom) φ.symm.injective]
    exact CFSG.ShultStronglyClosedTI.SuzukiModel.card_suzukiZ0 hK
  refine ⟨hZcard, fun z => ?_⟩
  rw [hZeq, Subgroup.mem_comap,
    CFSG.ShultStronglyClosedTI.SuzukiLayerKernel.mem_suzukiZ0_iff_sq_eq_one hK, hSφ,
    Subgroup.mem_comap]
  constructor
  · rintro ⟨hzU, hz2⟩
    refine ⟨hzU, φ.injective ?_⟩
    rw [map_mul, map_one]
    simpa [pow_two] using hz2
  · rintro ⟨hzS, hz2⟩
    refine ⟨hzS, ?_⟩
    rw [pow_two, ← map_mul, hz2, map_one]

theorem sz_center_le_of_torus {Xq : Type*} [Group Xq]
    [Finite Xq] {a : ℕ} (ha : 1 ≤ a)
    (e : Xq ≃* CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1)))
    {S : Sylow 2 Xq} {Dq Xq' : Subgroup Xq}
    (hDqcard : Nat.card Dq = 2 ^ (2 * a + 1) - 1)
    (hDqN : Dq ≤ Subgroup.normalizer ((S : Subgroup Xq) : Set Xq))
    (hX'S : Xq' ≤ (S : Subgroup Xq))
    (hX'N : Dq ≤ Subgroup.normalizer (Xq' : Set Xq)) (hX'ne : Xq' ≠ ⊥) :
    (S : Subgroup Xq) ⊓ Subgroup.centralizer ((S : Subgroup Xq) : Set Xq) ≤ Xq' := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZcard, hZmem⟩ := sz_center_card_and_mem ha e S
  let Z : Subgroup Xq := (S : Subgroup Xq) ⊓ Subgroup.centralizer ((S : Subgroup Xq) : Set Xq)
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  have hScard : Nat.card (S : Subgroup Xq) = (2 ^ (2 * a + 1)) ^ 2 :=
    (CFSG.RankThree.S4Free.Suzuki.card_sylow_and_center ha hK e S).1
  have hqodd : Odd (2 ^ (2 * a + 1) - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hDqS : Dq ⊓ (S : Subgroup Xq) = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hDqcard, hScard, ← pow_mul, mul_comm (2 * a + 1) 2]
    exact hqodd.coprime_two_right.pow_right (2 * (2 * a + 1))
  have hdz : ∀ d z, d ∈ Dq → z ∈ Z → z ≠ 1 → d * z * d⁻¹ = z → d = 1 := by
    intro d z hd hz hz1 hdz
    have hzS : z ∈ (S : Subgroup Xq) := ((hZmem z).mp hz).1
    have hz2 : z * z = 1 := ((hZmem z).mp hz).2
    have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    have hC := CFSG.RankThree.S4Free.Suzuki.centralizer_eq_sylow_of_mulEquiv hK e S hzord hzS
    have hdC : d ∈ Subgroup.centralizer ({z} : Set Xq) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc d * z = (d * z * d⁻¹) * d := by group
        _ = z * d := by rw [hdz]
    have hdS : d ∈ (S : Subgroup Xq) := hC ▸ hdC
    have hmem : d ∈ Dq ⊓ (S : Subgroup Xq) := ⟨hd, hdS⟩
    rw [hDqS] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hX'2 : IsPGroup 2 Xq' := S.isPGroup'.to_le hX'S
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX'2
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hX'ne ((Subgroup.card_eq_one).mp hn)
  have hdvd : 2 ∣ Nat.card Xq' := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨z₀', hz₀'ord⟩ := exists_prime_orderOf_dvd_card' (G := Xq') 2 hdvd
  have hz₀'ne : (z₀' : Xq') ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz₀'ord
    omega
  let z₀ : Xq := (z₀' : Xq)
  have hz₀X' : z₀ ∈ Xq' := z₀'.2
  have hz₀S : z₀ ∈ (S : Subgroup Xq) := hX'S hz₀X'
  have hz₀2 : z₀ * z₀ = 1 := by
    have h := pow_orderOf_eq_one z₀'
    rw [hz₀'ord] at h
    have h' : (z₀' : Xq) ^ 2 = 1 := by simpa using congrArg Subtype.val h
    simpa [pow_two, z₀] using h'
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    exact hz₀'ne (Subtype.ext h)
  have hz₀Z : z₀ ∈ Z := (hZmem z₀).mpr ⟨hz₀S, hz₀2⟩
  have hconjZ : ∀ d ∈ Dq, ∀ z ∈ Z, d * z * d⁻¹ ∈ Z := by
    intro d hd z hz
    obtain ⟨hzS, hz2⟩ := (hZmem z).mp hz
    refine (hZmem _).mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hDqN hd) z).mp hzS
    · have h : (d * z * d⁻¹) * (d * z * d⁻¹) = d * (z * z) * d⁻¹ := by group
      rw [h, hz2, mul_one, mul_inv_cancel]
  let orbit : Dq → {z : Xq // z ∈ Z ∧ z ≠ 1} := fun d =>
    ⟨d * z₀ * (d : Xq)⁻¹, hconjZ d d.2 z₀ hz₀Z, by
      intro h
      apply hz₀1
      have := congrArg (fun w => (d : Xq)⁻¹ * w * (d : Xq)) h
      simpa [mul_assoc] using this⟩
  have horbit_inj : Function.Injective orbit := by
    intro d₁ d₂ h
    have hval : d₁ * z₀ * (d₁ : Xq)⁻¹ = d₂ * z₀ * (d₂ : Xq)⁻¹ := congrArg Subtype.val h
    have hfix : ((d₂ : Xq)⁻¹ * d₁) * z₀ * ((d₂ : Xq)⁻¹ * d₁)⁻¹ = z₀ := by
      calc ((d₂ : Xq)⁻¹ * d₁) * z₀ * ((d₂ : Xq)⁻¹ * d₁)⁻¹
          = (d₂ : Xq)⁻¹ * (d₁ * z₀ * (d₁ : Xq)⁻¹) * d₂ := by group
        _ = (d₂ : Xq)⁻¹ * (d₂ * z₀ * (d₂ : Xq)⁻¹) * d₂ := by rw [hval]
        _ = z₀ := by group
    have hmemDq : ((d₂ : Xq)⁻¹ * d₁) ∈ Dq := Dq.mul_mem (Dq.inv_mem d₂.2) d₁.2
    have h1 := hdz _ _ hmemDq hz₀Z hz₀1 hfix
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hIcard : Nat.card {z : Xq // z ∈ Z ∧ z ≠ 1} = 2 ^ (2 * a + 1) - 1 := by
    have h1 : Nat.card {z : Xq // z ∈ Z ∧ z ≠ 1} = Nat.card ↥((Z : Set Xq) \ {1}) := rfl
    rw [h1, Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem (show (1 : Xq) ∈ Z from Z.one_mem)]
    rw [← Nat.card_coe_set_eq]
    exact congrArg (· - 1) hZcard
  have horbit_surj : Function.Surjective orbit := by
    haveI : Fintype Dq := Fintype.ofFinite _
    haveI : Fintype {z : Xq // z ∈ Z ∧ z ≠ 1} := Fintype.ofFinite _
    have hcard : Fintype.card Dq = Fintype.card {z : Xq // z ∈ Z ∧ z ≠ 1} := by
      simpa only [Nat.card_eq_fintype_card] using (show
        Nat.card Dq = Nat.card {z : Xq // z ∈ Z ∧ z ≠ 1} by rw [hIcard, hDqcard])
    exact (Finite.injective_iff_surjective_of_equiv (f := orbit)
      (Fintype.equivOfCardEq hcard)).mp horbit_inj
  rintro z hz
  by_cases hz1 : z = 1
  · rw [hz1]; exact Xq'.one_mem
  · obtain ⟨d, hd⟩ := horbit_surj ⟨z, hz, hz1⟩
    have hdz : d * z₀ * (d : Xq)⁻¹ = z := congrArg Subtype.val hd
    rw [← hdz]
    exact (Subgroup.mem_normalizer_iff.mp (hX'N d.2) z₀).mp hz₀X'

theorem card_normalizer_imageOTwoQuot_sz {L T : Subgroup G}
    {a : ℕ} (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) :
    Nat.card (Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  obtain ⟨S, hScoe⟩ := exists_sylow_imageOTwoQuot hT
  obtain ⟨e₀⟩ := hSz
  obtain ⟨e₁⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  let e : oTwoQuot ↥L ≃* CFSG.Blueprint.suzukiGroup a K := e₀.trans e₁
  exact hScoe ▸ CFSG.RankThree.S4Free.Suzuki.card_normalizer_sylow hK e S

theorem card_hallTwoPrime_eq_sz {L T D : Subgroup G} {a : ℕ}
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L)
    (hD : HallTwoPrime D (L ⊓ Subgroup.normalizer (T : Set G))) :
    Nat.card D = 2 ^ (2 * a + 1) - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ L := hT.le
  have hQ : pCoreOf 2 L ≤ T := hT.pCoreOf_le
  set Q : Subgroup G := pCoreOf 2 L with hQdef
  set M : Subgroup G := L ⊓ Subgroup.normalizer (T : Set G) with hMdef
  have hDM : D ≤ M := hD.1
  have hQM : Q ≤ M := le_inf (hQ.trans hTL) (hQ.trans (Subgroup.le_normalizer))
  obtain ⟨hDodd, k, hk⟩ := hD.2
  have hMcard : Nat.card M = Nat.card D * 2 ^ k := by
    have h := Subgroup.relIndex_mul_card (H := D) (K := M)
    rw [hk, inf_eq_left.mpr hDM, mul_comm] at h
    exact h.symm
  have hNq : Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L)) = imageOTwoQuot L M :=
    QA12.normalizer_image_eq hTL hQ
  have hMcard' : Nat.card M =
      Nat.card (Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))) * Nat.card Q := by
    have h := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul L M inf_le_left
    rw [← hNq, inf_eq_right.mpr hQM] at h
    exact h
  have hNcard := card_normalizer_imageOTwoQuot_sz ha hSz hT
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 L)
  have harith : Nat.card D * 2 ^ k = 2 ^ (m + 2 * (2 * a + 1)) * (2 ^ (2 * a + 1) - 1) := by
    have h1 : Nat.card D * 2 ^ k =
        Nat.card (Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))) * Nat.card Q := by
      rw [← hMcard, hMcard']
    have hpow : (2 ^ (2 * a + 1)) ^ 2 * 2 ^ m = 2 ^ (m + 2 * (2 * a + 1)) := by
      rw [← pow_mul, ← pow_add]
      ring
    rw [h1, hNcard, hm,
      show (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * 2 ^ m =
        (2 ^ (2 * a + 1)) ^ 2 * 2 ^ m * (2 ^ (2 * a + 1) - 1) from by ring, hpow]
  have hpowodd : Odd (2 ^ (2 * a + 1) - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  exact odd_mul_two_pow_eq hDodd hpowodd harith

theorem mem_sup_pCoreOf_of_torus_of_sz {D X : Subgroup G} {a : ℕ}
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L)
    (hD : HallTwoPrime D (L ⊓ Subgroup.normalizer (T : Set G)))
    (hXT : X ≤ T) (hXD : D ≤ Subgroup.normalizer (X : Set G)) (hX : ¬ X ≤ pCoreOf 2 L) :
    ∀ x ∈ T, x * x ∈ pCoreOf 2 L → x ∈ X ⊔ pCoreOf 2 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ L := hT.le
  let Tq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L T
  let Xq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L X
  let Dq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L D
  have hDL : D ≤ L := hD.1.trans inf_le_left
  have hDcard : Nat.card D = 2 ^ (2 * a + 1) - 1 :=
    card_hallTwoPrime_eq_sz (L := L) (T := T) (D := D) ha hSz hT hD
  have hDqcard : Nat.card Dq = 2 ^ (2 * a + 1) - 1 := by
    rw [QA12.card_image_of_odd hDL hD.2.1, hDcard]
  obtain ⟨S, hScoe⟩ := exists_sylow_imageOTwoQuot hT
  let K := GaloisField 2 (2 * a + 1)
  obtain ⟨e₀⟩ := hSz
  obtain ⟨e₁⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  let e : oTwoQuot ↥L ≃* CFSG.Blueprint.suzukiGroup a K := e₀.trans e₁
  have hDqN : Dq ≤ Subgroup.normalizer ((S : Subgroup (oTwoQuot ↥L)) : Set _) := by
    rw [show (S : Subgroup (oTwoQuot ↥L)) = Tq from hScoe]
    rw [show Subgroup.normalizer (Tq : Set (oTwoQuot ↥L)) =
      imageOTwoQuot L (L ⊓ Subgroup.normalizer (T : Set G)) from
        QA12.normalizer_image_eq hTL hT.pCoreOf_le]
    exact imageOTwoQuot_mono hD.1
  have hXq_ne : Xq ≠ ⊥ := by
    intro hbot
    apply hX
    intro x hx
    have hmem : (QuotientGroup.mk ⟨x, hTL (hXT hx)⟩ : oTwoQuot ↥L) ∈ Xq :=
      mem_imageOTwoQuot_iff.mpr ⟨x, hTL (hXT hx), hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (mk_eq_one_iff_mem_pCoreOf ⟨x, hTL (hXT hx)⟩).mp hmem
  have hX'S : Xq ≤ (S : Subgroup (oTwoQuot ↥L)) := by
    rw [show (S : Subgroup (oTwoQuot ↥L)) = Tq from hScoe]
    exact imageOTwoQuot_mono hXT
  have hX'N : Dq ≤ Subgroup.normalizer (Xq : Set (oTwoQuot ↥L)) :=
    CFSG.Quasithin.S152Y.imageOTwoQuot_le_normalizer (M := L) (X := D) (Y := X) hXD
  have hZle : (S : Subgroup (oTwoQuot ↥L)) ⊓
      Subgroup.centralizer ((S : Subgroup (oTwoQuot ↥L)) : Set _) ≤ Xq :=
    sz_center_le_of_torus ha e hDqcard hDqN hX'S hX'N hXq_ne
  intro x hxT hxx
  have hxL : x ∈ L := hTL hxT
  have hmkS : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) ∈
      (S : Subgroup (oTwoQuot ↥L)) := by
    rw [show (S : Subgroup (oTwoQuot ↥L)) = Tq from hScoe]
    exact mem_imageOTwoQuot_iff.mpr ⟨x, hxL, hxT, rfl⟩
  have hmk2 : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) *
      (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) = 1 := by
    rw [← QuotientGroup.mk_mul]
    exact (mk_eq_one_iff_mem_pCoreOf (⟨x, hxL⟩ * ⟨x, hxL⟩ : ↥L)).mpr (by
      simpa using hxx)
  have hmkZ : (QuotientGroup.mk ⟨x, hxL⟩ : oTwoQuot ↥L) ∈
      (S : Subgroup (oTwoQuot ↥L)) ⊓
        Subgroup.centralizer ((S : Subgroup (oTwoQuot ↥L)) : Set _) :=
    ((sz_center_card_and_mem ha e S).2 _).mpr ⟨hmkS, hmk2⟩
  exact mem_sup_pCoreOf_of_mk_mem (M := L) (A := X) (x := ⟨x, hxL⟩) (hZle hmkZ)

end Vertex
