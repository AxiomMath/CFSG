module

public import CFSG.Quasithin.Background.G64Statement
public import CFSG.Quasithin.Background.G6Transvection
public import CFSG.Quasithin.Background.G64Linear
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem sqtkGroup_of_isSQTKCat {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.SectionRank.IsSQTKCat Y) : SQTKGroup Y :=
  ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mp h.1, h.2⟩

theorem isQuotientOfSQTKCat_of_le {M : Type} [Group M] {G K : Subgroup M} (hKG : K ≤ G)
    (h : IsQuotientOfSQTKCat ↥G) : IsQuotientOfSQTKCat ↥K := by
  obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := h
  set K' : Subgroup (Y ⧸ N) := (K.subgroupOf G).map e.toMonoidHom with hK'
  set Yt : Subgroup Y := K'.comap (QuotientGroup.mk' N) with hYt
  have hYtsq : CFSG.SectionRank.IsSQTKCat Yt := CFSG.SectionRank.IsSQTKCat.subgroup hY Yt
  let f : ↥Yt →* ↥K' := ((QuotientGroup.mk' N).comp Yt.subtype).codRestrict K' fun y => y.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
    exact ⟨⟨y, hq⟩, rfl⟩
  have hker : f.ker = N.subgroupOf Yt := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    exact ⟨fun hy => congrArg Subtype.val hy, fun hy => Subtype.ext hy⟩
  refine ⟨↥Yt, inferInstance, inferInstance, N.subgroupOf Yt, inferInstance, hYtsq, ⟨?_⟩⟩
  have e1 : ↥K ≃* ↥(K.subgroupOf G) := (Subgroup.subgroupOfEquivOfLe hKG).symm
  have e2 : ↥(K.subgroupOf G) ≃* ↥K' :=
    (K.subgroupOf G).equivMapOfInjective e.toMonoidHom e.injective
  have e3 : ↥K' ≃* ↥Yt ⧸ f.ker := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm
  exact (e1.trans e2).trans (e3.trans (QuotientGroup.quotientMulEquivOfEq hker))

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {a : MulAut V}

theorem classK_le (h : Hyp61 G a) : conjClosure (Subgroup.zpowers a) G ≤ G :=
  G6.classClosure_le h.mem

theorem commV_classK (h : Hyp61 G a) : commV (conjClosure (Subgroup.zpowers a) G) = ⊤ := by
  rw [eq_top_iff, ← h.span]
  refine iSup₂_le fun g hg => ?_
  rw [← G6.commV_zpowers_conj]
  refine G6.commV_mono ?_
  rw [Subgroup.zpowers_le]
  exact mem_conjClosure hg (Subgroup.mem_zpowers a)

theorem pCoreOf_classK [Finite V] (h : Hyp61 G a) :
    pCoreOf 2 (conjClosure (Subgroup.zpowers a) G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := conjClosure (Subgroup.zpowers a) G with hK
  have hnormK : G ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
    le_normalizer_conjClosure (Subgroup.zpowers a) G
  have hNX : pCoreOf 2 K ≤ G := (pCoreOf_le 2 K).trans (classK_le h)
  have hnormN : G ≤ Subgroup.normalizer (pCoreOf 2 K : Set (MulAut V)) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 K (hnormK hg)
  have := le_pCoreOf_of_le_normalizer 2 hNX hnormN (pCoreOf_isPGroup 2 K)
  rw [h.pCore_eq_bot] at this
  exact le_bot_iff.1 this

@[expose] def transSet (G : Subgroup (MulAut V)) (a : MulAut V) : Set (MulAut V) :=
  {d | ∃ g ∈ G, d = g * a * g⁻¹}

theorem closure_transSet (G : Subgroup (MulAut V)) (a : MulAut V) :
    Subgroup.closure (transSet G a) = conjClosure (Subgroup.zpowers a) G :=
  G6.closure_conj_set_eq G a

theorem transSet_subset (G : Subgroup (MulAut V)) (a : MulAut V) :
    transSet G a ⊆ conjClosure (Subgroup.zpowers a) G := by
  rintro d ⟨g, hg, rfl⟩
  exact mem_conjClosure hg (Subgroup.mem_zpowers a)

theorem card_commV_conj {d : MulAut V} (htr : Nat.card (commV (Subgroup.zpowers a)) = 2)
    (hd : d ∈ transSet G a) : Nat.card (commV (Subgroup.zpowers d)) = 2 := by
  obtain ⟨g, -, rfl⟩ := hd
  rw [G6.card_commV_zpowers_conj, htr]

theorem sq_of_mem_transSet (h : Hyp61 G a) {d : MulAut V} (hd : d ∈ transSet G a) : d ^ 2 = 1 := by
  obtain ⟨g, -, rfl⟩ := hd
  rw [conj_pow, h.sq_eq_one]
  group

theorem transSet_conj {g d : MulAut V} (hg : g ∈ G) (hd : d ∈ transSet G a) :
    g * d * g⁻¹ ∈ transSet G a := by
  obtain ⟨h, hh, rfl⟩ := hd
  exact ⟨g * h, G.mul_mem hg hh, by group⟩

theorem eq_one_or_eq_of_mem_zpowers {M : Type*} [Group M] {d x : M} (hd : d ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers d) : x = 1 ∨ x = d := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : d ^ (2 : ℤ) = 1 := by exact_mod_cast hd
  rcases Int.emod_two_eq_zero_or_one z with h0 | h1
  · left
    rw [(Int.mul_ediv_add_emod z 2).symm, h0, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [(Int.mul_ediv_add_emod z 2).symm, h1, zpow_add, zpow_mul, h2, one_zpow, one_mul,
      zpow_one]

theorem card_fixV_mul_card_commV [Finite V] {d : MulAut V} (hd : d ^ 2 = 1) :
    Nat.card (fixV (Subgroup.zpowers d)) * Nat.card (commV (Subgroup.zpowers d)) = Nat.card V := by
  let φ : V →* V :=
    { toFun := fun v => d v * v⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul, mul_inv_rev]
        rw [mul_comm w⁻¹ v⁻¹, mul_mul_mul_comm] }
  have hker : φ.ker = fixV (Subgroup.zpowers d) := by
    ext v
    rw [MonoidHom.mem_ker, fixV_zpowers_iff]
    show d v * v⁻¹ = 1 ↔ d v = v
    exact mul_inv_eq_one
  have hrange : φ.range = commV (Subgroup.zpowers d) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact G6.mem_commV_of_mem (Subgroup.mem_zpowers d) v
    · rw [G6.commV_le_iff]
      intro x hx v
      rcases eq_one_or_eq_of_mem_zpowers hd hx with h1 | h1 <;> rw [h1]
      · exact ⟨1, by simp [φ]⟩
      · exact ⟨v, rfl⟩
  rw [← hker, ← hrange, ← Subgroup.index_ker]
  exact Subgroup.card_mul_index φ.ker

theorem isFFStarOffender_zpowers [Finite V] {X : Subgroup (MulAut V)} {d : MulAut V} (hdX : d ∈ X)
    (hd2 : d ^ 2 = 1) (hd : Nat.card (commV (Subgroup.zpowers d)) = 2) :
    IsFFStarOffender X (Subgroup.zpowers d) := by
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot] at hd
    have : commV (⊥ : Subgroup (MulAut V)) = ⊥ := by
      rw [eq_bot_iff, G6.commV_le_iff]
      intro x hx v
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      simp
    rw [this, Subgroup.card_bot] at hd
    omega
  have hcard : Nat.card (Subgroup.zpowers d) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hd2 hd1
  have hfix := card_fixV_mul_card_commV hd2
  rw [hd] at hfix
  refine ⟨Subgroup.zpowers_le.2 hdX, fun h => hd1 (Subgroup.zpowers_eq_bot.1 h), ⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_add, ← zpow_add, add_comm]
  · intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_cast
    rw [hd2, one_zpow]
  · intro B hB
    rw [hcard]
    by_cases hB1 : B = ⊥
    · subst hB1
      have : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
        rw [eq_top_iff]
        intro v _ x hx
        rw [Subgroup.mem_bot] at hx
        rw [hx]
        rfl
      rw [Subgroup.card_bot, this, Subgroup.card_top, one_mul, ← hfix, mul_comm]
    · have hBd : B = Subgroup.zpowers d := by
        refine le_antisymm hB ?_
        obtain ⟨⟨x, hxB⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
        rcases eq_one_or_eq_of_mem_zpowers hd2 (hB hxB) with h | h
        · exact absurd (Subtype.ext h) hx1
        · rw [Subgroup.zpowers_le, ← h]
          exact hxB
      rw [hBd, hcard]

theorem ffJ_classK [Finite V] (h : Hyp61 G a) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    ffJ (conjClosure (Subgroup.zpowers a) G) = conjClosure (Subgroup.zpowers a) G := by
  apply le_antisymm
  · exact iSup₂_le fun A hA => hA.1
  · intro x hx
    rw [← closure_transSet G a] at hx
    refine (Subgroup.closure_le _).2 ?_ hx
    intro d hd
    have hoff := isFFStarOffender_zpowers (transSet_subset G a hd) (sq_of_mem_transSet h hd)
      (card_commV_conj htr hd)
    exact (le_iSup₂ (f := fun (A : Subgroup (MulAut V)) (_ : IsFFStarOffender
      (conjClosure (Subgroup.zpowers a) G) A) => A) _ hoff) (Subgroup.mem_zpowers d)

theorem b53Hyp_classK [Finite V] (h : Hyp61 G a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    B53Hyp (conjClosure (Subgroup.zpowers a) G) := by
  refine ⟨pCoreOf_classK h, (ffJ_classK h htr).symm, ?_⟩
  obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := isQuotientOfSQTKCat_of_le (classK_le h) h.quotient_sqtk
  exact ⟨Y, inferInstance, inferInstance, N, inferInstance, sqtkGroup_of_isSQTKCat hY, ⟨e⟩⟩

end CFSG.Quasithin.G64
