module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.Quasithin.Vol2.KGFact4413Borel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeFive

public section

namespace CFSG.ASVolI

open CFSG.Open

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.Blueprint CFSG.SectionRank in
theorem burnsideC1h_card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have := CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 3
  simpa [Nat.factorial] using this

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.Blueprint CFSG.SectionRank in
theorem burnsideC1h_five_le_of_dvd_factorial {k : ℕ} (h : 60 ∣ k.factorial) : 5 ≤ k := by
  by_contra hk
  have : k ≤ 4 := by omega
  interval_cases k <;> simp [Nat.factorial] at h

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.Blueprint CFSG.SectionRank in
theorem burnsideC1h_isKGroupCat_alt5 : IsKGroupCat (alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  refine isKGroupCat_of_simple (Or.inr (Or.inl ⟨5, le_rfl, ⟨MulEquiv.refl _⟩⟩))
    fun H hH N _ hs hnab => ?_
  exfalso
  have hdvd := card_dvd_factorial_index hH
  rw [burnsideC1h_card_alt_five] at hdvd
  have h5 := burnsideC1h_five_le_of_dvd_factorial hdvd
  have hmul := H.card_mul_index
  rw [burnsideC1h_card_alt_five] at hmul
  obtain ⟨h60, hle⟩ := sixty_le_card_section N hs hnab
  have hH12 : Nat.card H ≤ 12 := by
    by_contra h
    have : 13 * 5 ≤ Nat.card H * H.index := Nat.mul_le_mul (by omega) h5
    omega
  omega

open CFSG.Quasithin.H13.U3.GC137.SQ in
theorem burnsideC1h_rankLeTwo_alt5 : RankLeTwo (alternatingGroup (Fin 5)) := by
  intro p hp hp2 E hE
  refine card_le_of_cube_free hp ?_ hE
  rw [burnsideC1h_card_alt_five]
  intro hd
  have h60 : p ^ 3 ≤ 60 := Nat.le_of_dvd (by norm_num) hd
  have hp4 : p < 4 := by
    by_contra h
    have : 4 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases p <;> first
    | (exfalso; revert hp; norm_num; done)
    | omega
    | (exfalso; revert hd; norm_num; done)


open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.U3.GC137.SQ CFSG.SectionRank in
theorem burnsideC1h_sqtkGroup {G : Type} [Group G] [Finite G] {X T L : Subgroup G}
    (hT : IsSylowTwoOf T X) (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hL : L ∈ cComp X)
    (hA : IsAlt 5 (↥L ⧸ CFSG.pCore 2 ↥L)) : SQTKGroup ↥X := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hN : X ≤ Subgroup.normalizer (L : Set G) := C124.le_normalizer_of_prod hT hprod hL
  have hnorm : (L.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hN
  have : (Subgroup.inclusion hLX).range.Normal := by
    rw [Subgroup.inclusion_range]
    exact hnorm
  have hq := isPGroup_quotient_of_prod hT hprod hLX
  have hO : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨e⟩ := hA
  have hK : IsKGroupCat (↥L ⧸ CFSG.pCore 2 ↥L) :=
    IsKGroupCat.of_mulEquiv burnsideC1h_isKGroupCat_alt5 e
  have hR : RankLeTwo (↥L ⧸ CFSG.pCore 2 ↥L) := rankLeTwo_of_mulEquiv e burnsideC1h_rankLeTwo_alt5
  exact ⟨stronglyQuasithin_of_rankLeTwo (rankLeTwo_of_hom (Subgroup.inclusion hLX)
      (Subgroup.inclusion_injective hLX) hq (CFSG.pCore 2 ↥L) hO hR),
    isKGroupCat_of_ext (Subgroup.inclusion hLX) (Subgroup.inclusion_injective hLX) hq
      (CFSG.pCore 2 ↥L) hO hK⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC1h_unique_max {G : Type} [Group G] [Finite G] {X R L : Subgroup G}
    (hR : IsSylowTwoOf R X) (hL : L ∈ cComp X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ r ∈ R, x = l * r)
    (hA : IsAlt 5 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsUniqueMaxOver X R (X ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hRX : R ≤ X := hR.1
  have hN : X ≤ Subgroup.normalizer (L : Set G) := C124.le_normalizer_of_prod hR hprod hL
  have hRL : IsSylowTwoOf (R ⊓ L) L :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hR hLX
      (CFSG.Open.IsSubnormal.subgroupOf (subnormal_of_mem_cComp hL))
  have hQR : pCoreOf 2 L ≤ R := (B6.pCoreOf_two_le_of_isSylowTwoOf hRL).trans inf_le_left
  set Q : Subgroup ↥L := CFSG.pCore 2 ↥L with hQdef
  let φ : ↥L →* ↥L ⧸ Q := QuotientGroup.mk' Q
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective Q
  have hQmemR : ∀ y : ↥L, y ∈ Q → (y : G) ∈ R := fun y hy => hQR ⟨y, hy, rfl⟩
  set S₀ : Subgroup ↥L := (R ⊓ L).subgroupOf L with hS₀
  let D : Subgroup (↥L ⧸ Q) := S₀.map φ
  have hS₀mem : ∀ y : ↥L, y ∈ S₀ ↔ (y : G) ∈ R := fun y => by
    rw [hS₀, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  have hDmem : ∀ y : ↥L, φ y ∈ D ↔ (y : G) ∈ R := by
    intro y
    constructor
    · rintro ⟨s, hs, hsy⟩
      have h1 : s⁻¹ * y ∈ Q := QuotientGroup.eq.1 hsy
      have h2 : (y : G) = (s : G) * ((s⁻¹ * y : ↥L) : G) := by simp
      rw [h2]
      exact R.mul_mem ((hS₀mem s).1 hs) (hQmemR _ h1)
    · intro hy
      exact ⟨y, (hS₀mem y).2 hy, rfl⟩
  obtain ⟨e⟩ := hA
  have hsimple : IsSimpleGroup (↥L ⧸ Q) :=
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    e.isSimpleGroup
  have hcardA : Nat.card (↥L ⧸ Q) = 60 := by
    rw [Nat.card_congr e.toEquiv, burnsideC1h_card_alt_five]
  have hD2 : IsPGroup 2 D := by
    have h1 : IsPGroup 2 S₀ := hRL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hRL.1).symm
    exact h1.map φ
  have hDidx : D.index = S₀.index := by
    have hcomap : D.comap φ = S₀ := by
      ext y
      rw [Subgroup.mem_comap, hDmem, hS₀mem]
    rw [← hcomap, Subgroup.index_comap_of_surjective D hφ]
  have hDodd : ¬ 2 ∣ D.index := by
    rw [hDidx]
    exact hRL.2.2
  have hDcard : Nat.card D = 4 := by
    obtain ⟨n, hn⟩ := hD2.exists_card_eq
    have hmul := D.card_mul_index
    rw [hcardA, hn] at hmul
    rcases n with _ | _ | _ | n
    · simp at hmul
      omega
    · simp at hmul
      omega
    · simpa using hn
    · exfalso
      have h8 : 8 ∣ 60 := ⟨2 ^ n * D.index, by rw [← hmul]; ring⟩
      omega
  obtain ⟨κ⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 (GaloisField 2 2)
    CFSG.Quasithin.A5Model.card_gf4 CFSG.Quasithin.A5Model.card_sl2_gf4
  have hF : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  let e' : (↥L ⧸ Q) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) := e.trans κ.symm
  have hdich : ∀ B : Subgroup (↥L ⧸ Q), D ≤ B →
      B = ⊤ ∨ B ≤ Subgroup.normalizer (D : Set (↥L ⧸ Q)) := fun B hB =>
    CFSG.Quasithin.C126.Nat.dichotomy_sl2 (n := 2) hF e' (by rw [hDcard, hF]; norm_num) hB
  have hDnn : ¬ D.Normal := by
    intro hDn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with h | h
    · rw [h, Subgroup.card_bot] at hDcard
      omega
    · rw [h, Subgroup.card_top, hcardA] at hDcard
      omega
  have hnormL : ∀ l : ↥L, φ l ∈ Subgroup.normalizer (D : Set (↥L ⧸ Q)) →
      ∀ z ∈ R ⊓ L, (l : G) * z * (l : G)⁻¹ ∈ R ⊓ L := by
    intro l hl z hz
    refine ⟨?_, L.mul_mem (L.mul_mem l.2 hz.2) (L.inv_mem l.2)⟩
    have hzD : φ ⟨z, hz.2⟩ ∈ D := (hDmem _).2 hz.1
    have h1 := (Subgroup.mem_normalizer_iff.1 hl (φ ⟨z, hz.2⟩)).1 hzD
    have h2 : l * ⟨z, hz.2⟩ * l⁻¹ = (⟨(l : G) * z * (l : G)⁻¹, L.mul_mem (L.mul_mem l.2 hz.2)
        (L.inv_mem l.2)⟩ : ↥L) := rfl
    have h2 : φ l * φ ⟨z, hz.2⟩ * (φ l)⁻¹ = φ (l * ⟨z, hz.2⟩ * l⁻¹) := by
      simp [map_mul, map_inv]
    rw [h2, hDmem] at h1
    simpa using h1
  have hnormL' : ∀ l : ↥L, φ l ∈ Subgroup.normalizer (D : Set (↥L ⧸ Q)) →
      (l : G) ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
    intro l hl
    refine B6.mem_normalizer_of_forall_mem (hnormL l hl) fun z hz => ?_
    have hl' : φ l⁻¹ ∈ Subgroup.normalizer (D : Set (↥L ⧸ Q)) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hl
    simpa using hnormL l⁻¹ hl' z hz
  have hRnorm' : ∀ g ∈ R, ∀ x ∈ R ⊓ L, g * x * g⁻¹ ∈ R ⊓ L := fun g hg x hx =>
    ⟨R.mul_mem (R.mul_mem hg hx.1) (R.inv_mem hg),
      (Subgroup.mem_normalizer_iff.1 (hN (hRX hg)) x).1 hx.2⟩
  have hRnorm : ∀ r ∈ R, r ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := fun r hr =>
    B6.mem_normalizer_of_forall_mem (hRnorm' r hr) fun x hx => by
      simpa using hRnorm' r⁻¹ (R.inv_mem hr) x hx
  have hRM : R ≤ X ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) :=
    le_inf hRX fun r hr => hRnorm r hr
  have hMne : ¬ X ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
    intro hXN
    apply hDnn
    refine ⟨fun d hd g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hd
    obtain ⟨l, rfl⟩ := hφ g
    rw [← map_inv, ← map_mul, ← map_mul, hDmem]
    have hyRL : (y : G) ∈ R ⊓ L := ⟨(hS₀mem y).1 hy, y.2⟩
    have := (Subgroup.mem_normalizer_iff.1 (hXN (hLX l.2)) (y : G)).1 hyRL
    simpa using this.1
  have hmax : ∀ K : Subgroup G, R ≤ K → K < X →
      K ≤ X ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
    intro K hRK hKX
    let B : Subgroup (↥L ⧸ Q) := ((K ⊓ L).subgroupOf L).map φ
    have hDB : D ≤ B := by
      apply Subgroup.map_mono
      intro y hy
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨hRK ((hS₀mem y).1 hy), y.2⟩
    rcases hdich B hDB with hB | hB
    · exfalso
      have hLK : L ≤ K := by
        intro l hl
        have hmem : φ ⟨l, hl⟩ ∈ B := by rw [hB]; trivial
        obtain ⟨s, hs, hsl⟩ := hmem
        have h1 : s⁻¹ * ⟨l, hl⟩ ∈ Q := QuotientGroup.eq.1 hsl
        have h2 : l = (s : G) * ((s⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
        rw [h2]
        exact K.mul_mem (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).1
          (hRK (hQmemR _ h1))
      have hXK : X ≤ K := by
        intro x hx
        obtain ⟨l, hl, r, hr, rfl⟩ := hprod x hx
        exact K.mul_mem (hLK hl) (hRK hr)
      exact absurd (le_antisymm hKX.le hXK) (ne_of_lt hKX)
    · intro k hk
      have hkX : k ∈ X := hKX.le hk
      obtain ⟨l, hl, r, hr, rfl⟩ := hprod k hkX
      have hlK : l ∈ K := by
        have : l = l * r * r⁻¹ := by group
        rw [this]
        exact K.mul_mem hk (K.inv_mem (hRK hr))
      have hlB : φ ⟨l, hl⟩ ∈ B := ⟨⟨l, hl⟩, Subgroup.mem_subgroupOf.2 ⟨hlK, hl⟩, rfl⟩
      have hlM : l ∈ X ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) :=
        ⟨hLX hl, hnormL' ⟨l, hl⟩ (hB hlB)⟩
      exact Subgroup.mul_mem _ hlM (hRM hr)
  rw [isUniqueMaxOver_iff]
  have hMlt : X ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) < X :=
    lt_of_le_of_ne inf_le_left fun h => hMne (inf_eq_left.1 h)
  refine ⟨⟨hMlt, fun K hMK hKX => ?_⟩, hRM, fun N' hN' hRN' => ?_⟩
  · by_contra hne
    have hKlt : K < X := lt_of_le_of_ne hKX hne
    exact absurd (hmax K (hRM.trans hMK.le) hKlt) (not_le_of_gt hMK)
  · have hle := hmax N' hRN' hN'.1
    by_contra hne
    exact absurd (hN'.2 _ (lt_of_le_of_ne hle hne) inf_le_left) (ne_of_lt hMlt)

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC1h_uFamHat {G : Type} [Group G] [Finite G] {X R L : Subgroup G}
    (hR : IsSylowTwoOf R X) (hL : L ∈ cComp X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ r ∈ R, x = l * r)
    (hA : IsAlt 5 (↥L ⧸ CFSG.pCore 2 ↥L)) : X ∈ uFamHat X R := by
  have hU := burnsideC1h_unique_max hR hL hprod hA
  have hmin := CFSG.Quasithin.H13.KG4413.minParabolic_of_cComp hR hU hL
  exact ⟨⟨le_rfl, hmin.lt, by rw [hmin.uniqueMax]; exact Set.ncard_singleton _⟩, hmin.not_normal⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC1h_block_eq {G : Type} [Group G] [Finite G] {X R L K : Subgroup G}
    (hR : IsSylowTwoOf R X) (hL : L ∈ cComp X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ r ∈ R, x = l * r)
    (hA : IsAlt 5 (↥L ⧸ CFSG.pCore 2 ↥L)) (hK : IsBlock2 X K) : K = L := by
  classical
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hN : X ≤ Subgroup.normalizer (L : Set G) := C124.le_normalizer_of_prod hR hprod hL
  have hnorm : (L.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hN
  haveI : (Subgroup.inclusion hLX).range.Normal := by
    rw [Subgroup.inclusion_range]
    exact hnorm
  have hq : IsPGroup 2 (↥X ⧸ (Subgroup.inclusion hLX).range) :=
    CFSG.Quasithin.H13.U3.GC137.SQ.isPGroup_quotient_of_prod hR hprod hLX
  obtain ⟨hshort, hKX, hKsub⟩ := hK
  have hKL : K ≤ L := by
    let f : ↥K →* ↥X ⧸ (Subgroup.inclusion hLX).range :=
      (QuotientGroup.mk' _).comp (Subgroup.inclusion hKX)
    have hfker : f.ker = ⊤ := by
      have h2 : IsPGroup 2 (↥K ⧸ f.ker) :=
        hq.of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
      exact hshort.1 f.ker h2
    intro k hk
    have h1 : (⟨k, hk⟩ : ↥K) ∈ f.ker := by rw [hfker]; trivial
    rw [MonoidHom.mem_ker] at h1
    have h3 : (QuotientGroup.mk (⟨k, hKX hk⟩ : ↥X) :
        ↥X ⧸ (Subgroup.inclusion hLX).range) = 1 := h1
    rw [QuotientGroup.eq_one_iff] at h3
    obtain ⟨⟨l, hl⟩, hlk⟩ := h3
    have h4 := congrArg Subtype.val hlk
    simp only [Subgroup.coe_inclusion] at h4
    rw [← h4]
    exact hl
  have hKsubX : CFSG.Open.IsSubnormal K X := (CFSG.Open.IsSubnormal.iff_subgroupOf hKX).2 hKsub
  have hKsubL : CFSG.Open.IsSubnormal K L := A3.subnormal_of_le_of_le hKsubX hKL hLX
  set Q : Subgroup ↥L := CFSG.pCore 2 ↥L with hQdef
  let φ : ↥L →* ↥L ⧸ Q := QuotientGroup.mk' Q
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective Q
  obtain ⟨e⟩ := hA
  have hsimple : IsSimpleGroup (↥L ⧸ Q) :=
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    e.isSimpleGroup
  have hcardA : Nat.card (↥L ⧸ Q) = 60 := by
    rw [Nat.card_congr e.toEquiv, burnsideC1h_card_alt_five]
  have hnsolv : ¬ Group.IsSolvable (↥L ⧸ Q) := by
    intro hs
    have hcomm : ∀ a b : ↥L ⧸ Q, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.2 hs
    haveI : IsMulCommutative (↥L ⧸ Q) := ⟨⟨hcomm⟩⟩
    have hp := (Group.is_simple_iff_prime_card.1 hsimple)
    rw [hcardA] at hp
    exact absurd hp (by norm_num)
  have hsubφ : CFSG.Open.IsSubnormal ((K.subgroupOf L).map φ) (⊤ : Subgroup (↥L ⧸ Q)) := by
    have h1 := (CFSG.Open.IsSubnormal.of_mathlib hKsubL.subgroupOf).map φ
    rwa [Subgroup.map_top_of_surjective φ hφ] at h1
  rcases CFSG.Open.IsSubnormal.eq_bot_or_top hsubφ with hbot | htop
  ·
    exfalso
    have hKQ : ∀ k : ↥K, ((k : G)) ∈ pCoreOf 2 L := by
      intro k
      have hmem : φ ⟨k, hKL k.2⟩ ∈ (K.subgroupOf L).map φ := ⟨⟨k, hKL k.2⟩, k.2, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact ⟨⟨k, hKL k.2⟩, (QuotientGroup.eq_one_iff _).1 hmem, rfl⟩
    have hK2 : IsPGroup 2 ↥K := by
      intro k
      obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨(k : G), hKQ k⟩
      exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
    have htopK : CFSG.pCore 2 ↥K = ⊤ := by
      have hN : (⊤ : Subgroup ↥K).Normal := inferInstance
      exact top_le_iff.1 (CFSG.LieType.BorelTits.le_pCore 2 hN
        (hK2.of_equiv Subgroup.topEquiv.symm))
    have hsub : Subsingleton (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [htopK]
      exact QuotientGroup.subsingleton_quotient_top
    rcases hshort.2.2.2.1 with hqs | hcard
    · obtain ⟨-, -, a, b, hab⟩ := hqs
      exact hab (Subsingleton.elim _ _)
    · rw [Nat.card_unique] at hcard
      omega
  ·
    have hKsolv : ¬ Group.IsSolvable ↥K := by
      intro hs
      let ψ : ↥K →* ↥L ⧸ Q := φ.comp (Subgroup.inclusion hKL)
      have hψ : Function.Surjective ψ := by
        intro a
        have : a ∈ (K.subgroupOf L).map φ := by rw [htop]; trivial
        obtain ⟨y, hy, rfl⟩ := this
        exact ⟨⟨y, hy⟩, rfl⟩
      exact hnsolv (solvable_of_surjective hψ)
    have hcore : perfectCore K ≠ ⊥ := fun h => hKsolv ((isSolvable_iff_perfectCore_eq_bot K).2 h)
    have hcoreL : perfectCore K ≤ L := (perfectCore_le K).trans hKL
    have hcoreEq : perfectCore K = L := by
      by_contra hne
      exact not_subnormal_of_mem_cComp hL (lt_of_le_of_ne hcoreL hne) hcore (perfectCore_perfect K)
        (A3.subnormal_perfectCore hKsubX)
    exact le_antisymm hKL (hcoreEq ▸ perfectCore_le K)

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC1h_ne_bot {G : Type} [Group G] [Finite G] {X R L : Subgroup G}
    (hR : IsSylowTwoOf R X) (hL : L ∈ cComp X) (hA : IsAlt 5 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    R ≠ ⊥ := by
  intro h
  have hRL : IsSylowTwoOf (R ⊓ L) L :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hR (le_of_mem_cComp hL)
      (CFSG.Open.IsSubnormal.subgroupOf (subnormal_of_mem_cComp hL))
  have hidx := hRL.2.2
  rw [h, bot_inf_eq, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hidx
  obtain ⟨e⟩ := hA
  have h60 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
    rw [Nat.card_congr e.toEquiv, burnsideC1h_card_alt_five]
  have hmul := (CFSG.pCore 2 ↥L).card_mul_index
  have hidx60 : (CFSG.pCore 2 ↥L).index = 60 := h60
  rw [hidx60] at hmul
  exact hidx ⟨30 * Nat.card (CFSG.pCore 2 ↥L), by omega⟩

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_1_23
    : C_1_23 := by
  intro Ω _ _ C₁ C₂ hGN T R X L hT hbaum hRT hSyl hL hprod hChar _
  have hprod' : ∀ x ∈ X, ∃ l ∈ L, ∃ r ∈ R, x = l * r := by
    intro x hx
    have hx' : x ∈ (X : Set Ω) := hx
    rw [hprod] at hx'
    obtain ⟨l, hl, r, hr, rfl⟩ := Set.mem_mul.1 hx'
    exact ⟨l, hl, r, hr, rfl⟩
  refine ⟨fun hA5 => ?_, fun _ hExc => ?_⟩
  ·
    have hSQ : CFSG.Quasithin.IsSQTKTC X :=
      (CFSG.Quasithin.C1GN.isSQTKTC_iff_sqtkGroup).2 (burnsideC1h_sqtkGroup hSyl hprod' hL hA5)
    have hMin : CFSG.Quasithin.IsMinParabolicOf X X :=
      ⟨R, hSyl, burnsideC1h_uFamHat hSyl hL hprod' hA5⟩
    have hR0 : R ≠ ⊥ := burnsideC1h_ne_bot hSyl hL hA5
    have hR2 : IsPGroup 2 R := hSyl.2.1
    have hT0 : T ≠ ⊥ := fun h => hR0 (le_bot_iff.1 (h ▸ hRT))
    have hJTR : thompsonJ T ≤ R := (B6.thompsonJ_le_baum T).trans hbaum
    have hJeq : thompsonJ R = thompsonJ T := B6.thompsonJ_eq_of_le hJTR hRT
    have hbaumEq : baum R = baum T := by
      ext x
      unfold baum
      rw [hJeq]
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨hRT h.1, h.2⟩, fun h => ⟨hbaum (by simpa [baum] using h), h.2⟩⟩
    rcases CFSG.Quasithin.theoremC126_proved Ω C₁ C₂ hGN X R hSQ hSyl hChar hMin with
      h1 | h2 | ⟨r, K', hr, hK', -, -, -, -⟩
    · left
      refine le_trans ?_ h1
      intro z hz
      have hz' := (hGN.c1_eq T hT hT0) ▸ hz
      obtain ⟨-, h1Z, -, -, -, -, -⟩ := hGN.pair T hT hT0
      have hzB : z ∈ baum T := (h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)) (by
        rw [hGN.c1_eq T hT hT0] at hz ⊢
        exact hz)
      have hzR : z ∈ R := hbaum hzB
      rw [hGN.c1_eq R hR2 hR0]
      refine ⟨⟨hzR, Subgroup.centralizer_le hRT hz'.1.2⟩, ?_⟩
      rw [hbaumEq]
      exact hz'.2
    · right; left
      have hC₂ : C₂ R = C₂ T :=
        (hGN.c2_eq R hR2 hR0).trans ((congrArg C₂ hbaumEq).trans (hGN.c2_eq T hT hT0).symm)
      rwa [hC₂] at h2
    · right; right
      have hr0 : 0 < r := by omega
      obtain ⟨hK, hKJ⟩ := hK' ⟨0, hr0⟩
      have hKL : K' ⟨0, hr0⟩ = L := burnsideC1h_block_eq hSyl hL hprod' hA5 hK.1
      refine ⟨hKL ▸ hK.1, ?_, ?_⟩
      · obtain ⟨e⟩ := hA5
        have hshortL : IsShort2 L := hKL ▸ hK.1.1
        let α₀ : ↥L →* alternatingGroup (Fin 5) :=
          e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
        have hs : Function.Surjective α₀ :=
          e.surjective.comp (QuotientGroup.mk'_surjective _)
        have hker : α₀.ker = CFSG.pCore 2 ↥L := by
          ext x
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
          show e (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) = 1 ↔ _
          rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isAlt5_or_lin2 hshortL
          (perfect_of_mem_cComp hL) α₀ hs hker
      · rw [← hKL, ← hJeq]
        exact hKJ
  · exact L246.C123.theoremC123Two_holds Ω C₁ C₂ hGN T R X L hT hbaum hRT hSyl hChar hL hprod' hExc

end

end CFSG.ASVolI
