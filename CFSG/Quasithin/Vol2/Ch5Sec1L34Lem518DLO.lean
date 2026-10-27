module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs518F
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem522X

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section QuotO2

variable {G : Type} [Group G]

@[expose] def imgO2 (K Y : Subgroup G) : Subgroup (O2Q K) :=
  (Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

theorem mk_mem_imgO2 {K Y : Subgroup G} {x : G} (hxK : x ∈ K) (hxY : x ∈ Y) :
    (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : O2Q K) ∈ imgO2 K Y :=
  ⟨⟨x, hxK⟩, hxY, rfl⟩

theorem mem_preimageModTwoCore {K : Subgroup G} {R : Subgroup (O2Q K)} {x : G} :
    x ∈ preimageModTwoCore K R ↔
      ∃ hx : x ∈ K, (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : O2Q K) ∈ R := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem preimageModTwoCore_le (K : Subgroup G) (R : Subgroup (O2Q K)) :
    preimageModTwoCore K R ≤ K := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem mem_pCoreOf_iff_mk_eq_one {K : Subgroup G} {x : G} (hxK : x ∈ K) :
    x ∈ pCoreOf 2 K ↔ (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : O2Q K) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨_, h, rfl⟩

theorem pCoreOf_le_preimageModTwoCore (K : Subgroup G) (R : Subgroup (O2Q K)) :
    pCoreOf 2 K ≤ preimageModTwoCore K R := by
  intro x hx
  have hxK : x ∈ K := pCoreOf_le 2 K hx
  refine mem_preimageModTwoCore.mpr ⟨hxK, ?_⟩
  rw [(mem_pCoreOf_iff_mk_eq_one hxK).mp hx]
  exact R.one_mem

theorem preimageModTwoCore_imgO2 {K Y : Subgroup G} (hOY : pCoreOf 2 K ≤ Y) (hYK : Y ≤ K) :
    preimageModTwoCore K (imgO2 K Y) = Y := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxK, ⟨y, hy, hyx⟩⟩ := mem_preimageModTwoCore.mp hx
    replace hy : (y : G) ∈ Y := hy
    have hmem : y⁻¹ * ⟨x, hxK⟩ ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq]
      exact hyx
    have hO : ((y⁻¹ * ⟨x, hxK⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
      exact ⟨_, hmem, rfl⟩
    have := Y.mul_mem hy (hOY hO)
    simpa using this
  · intro x hx
    exact mem_preimageModTwoCore.mpr ⟨hYK hx, mk_mem_imgO2 (hYK hx) hx⟩

theorem card_preimageModTwoCore [Finite G] (K : Subgroup G) (R : Subgroup (O2Q K)) :
    Nat.card (preimageModTwoCore K R) = Nat.card R * Nat.card (pCoreOf 2 K) := by
  set f := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hf
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  have h1 : Nat.card (preimageModTwoCore K R) = Nat.card (R.comap f) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have h2 : Nat.card (pCoreOf 2 K) = Nat.card (CFSG.pCore 2 ↥K) := by
    exact Subgroup.card_map_of_injective K.subtype_injective
  have hidx : (R.comap f).index = R.index := Subgroup.index_comap_of_surjective R hsurj
  have hK := (R.comap f).card_mul_index
  have hQ := R.card_mul_index
  have hKQ : Nat.card ↥K = Nat.card (O2Q K) * Nat.card (CFSG.pCore 2 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hpos : 0 < R.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h1, h2]
  rw [hidx] at hK
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hK, hKQ, ← hQ]
  ring

theorem mem_normalizer_preimageModTwoCore {K : Subgroup G} {R : Subgroup (O2Q K)}
    (g : ↥(Subgroup.normalizer (K : Set G)))
    (hR : R.map (quotConjAut K g).toMonoidHom = R) :
    (g : G) ∈ Subgroup.normalizer (preimageModTwoCore K R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxK, hxR⟩ := mem_preimageModTwoCore.mp hx
    have hgx : (g : G) * x * (g : G)⁻¹ ∈ K := (g.2 x).mp hxK
    refine mem_preimageModTwoCore.mpr ⟨hgx, ?_⟩
    have e := quotConjAut_mk K g ⟨x, hxK⟩
    have hmem : quotConjAut K g (QuotientGroup.mk ⟨x, hxK⟩) ∈ R := by
      rw [← hR]
      exact ⟨_, hxR, rfl⟩
    rw [e] at hmem
    exact hmem
  · intro hx
    obtain ⟨hgxK, hgxR⟩ := mem_preimageModTwoCore.mp hx
    have hxK : x ∈ K := by
      have := (g.2 x).mpr hgxK
      exact this
    refine mem_preimageModTwoCore.mpr ⟨hxK, ?_⟩
    have e := quotConjAut_mk K g ⟨x, hxK⟩
    have hmem : quotConjAut K g (QuotientGroup.mk ⟨x, hxK⟩) ∈
        R.map (quotConjAut K g).toMonoidHom := by
      rw [hR, e]
      exact hgxR
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = QuotientGroup.mk ⟨x, hxK⟩ := (quotConjAut K g).injective hyx
    rw [← this]
    exact hy

theorem map_quotConjAut_imgO2 {K Y : Subgroup G} (hYK : Y ≤ K)
    (g : ↥(Subgroup.normalizer (K : Set G))) (hg : (g : G) ∈ Subgroup.normalizer (Y : Set G)) :
    (imgO2 K Y).map (quotConjAut K g).toMonoidHom = imgO2 K Y := by
  ext q
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    replace hy : (y : G) ∈ Y := hy
    show quotConjAut K g (QuotientGroup.mk y) ∈ imgO2 K Y
    rw [quotConjAut_mk]
    exact mk_mem_imgO2 _ ((Subgroup.mem_normalizer_iff.mp hg _).mp hy)
  · rintro ⟨y, hy, rfl⟩
    replace hy : (y : G) ∈ Y := hy
    have hgi : (g : G)⁻¹ ∈ Subgroup.normalizer (Y : Set G) := inv_mem hg
    have hz : (g : G)⁻¹ * y * (g : G)⁻¹⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hgi _).mp hy
    have hzK : (g : G)⁻¹ * y * (g : G)⁻¹⁻¹ ∈ K := hYK hz
    refine ⟨QuotientGroup.mk ⟨_, hzK⟩, mk_mem_imgO2 hzK hz, ?_⟩
    show quotConjAut K g (QuotientGroup.mk ⟨_, hzK⟩) = _
    rw [quotConjAut_mk]
    congr 1
    apply Subtype.ext
    simp only [inv_inv]
    group

theorem mk_mem_normalizer_imgO2 {K Y : Subgroup G} (hYK : Y ≤ K) {y : G} (hyK : y ∈ K)
    (hy : y ∈ Subgroup.normalizer (Y : Set G)) :
    (QuotientGroup.mk (⟨y, hyK⟩ : ↥K) : O2Q K) ∈ Subgroup.normalizer (imgO2 K Y : Set (O2Q K)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h := map_quotConjAut_imgO2 hYK ⟨y, Subgroup.le_normalizer hyK⟩ hy
  rw [quotConjAut_of_mem (X := K) ⟨y, hyK⟩] at h
  exact h

theorem isSylowTwoOf_imgO2 {K Y : Subgroup G} (hY : IsSylowTwoOf Y K) :
    IsSylowTwoOf (imgO2 K Y) ⊤ :=
  isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hY) _
    (QuotientGroup.mk'_surjective _)

theorem mk_mem_imgO2_iff {K Y : Subgroup G} (hOY : pCoreOf 2 K ≤ Y) (k : ↥K) :
    (QuotientGroup.mk k : O2Q K) ∈ imgO2 K Y ↔ (k : G) ∈ Y := by
  constructor
  · rintro ⟨y, hy, hyk⟩
    replace hy : (y : G) ∈ Y := hy
    have hmem : y⁻¹ * k ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq]
      exact hyk
    have hO : ((y⁻¹ * k : ↥K) : G) ∈ pCoreOf 2 K := by
      exact ⟨_, hmem, rfl⟩
    have := Y.mul_mem hy (hOY hO)
    simpa using this
  · intro hk
    exact ⟨k, hk, rfl⟩

theorem preimageModTwoCore_mono {K : Subgroup G} {R R' : Subgroup (O2Q K)} (h : R ≤ R') :
    preimageModTwoCore K R ≤ preimageModTwoCore K R' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem imgO2_preimageModTwoCore (K : Subgroup G) (R : Subgroup (O2Q K)) :
    imgO2 K (preimageModTwoCore K R) = R := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [mk_mem_imgO2_iff (pCoreOf_le_preimageModTwoCore K R)]
    constructor
    · intro hk
      obtain ⟨hkK, hkR⟩ := mem_preimageModTwoCore.mp hk
      exact hkR
    · intro hk
      exact mem_preimageModTwoCore.mpr ⟨k.2, hk⟩

theorem exists_quotConjAut_pow_eq_one {K S : Subgroup G} (hS : IsPGroup 2 S) {s : G}
    (hs : s ∈ S) (hsN : s ∈ Subgroup.normalizer (K : Set G)) :
    ∃ m : ℕ, quotConjAut K ⟨s, hsN⟩ ^ 2 ^ m = 1 := by
  obtain ⟨m, hm⟩ := hS ⟨s, hs⟩
  refine ⟨m, ?_⟩
  have e : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ m = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hm)
  rw [← map_pow, e, map_one]

end QuotO2

section RankOne

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_top_eq_top {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : ¬ IsPGroup 2 Q) : oTwoUpper (⊤ : Subgroup Q) = ⊤ := by
  have : (oTwoUpper (⊤ : Subgroup Q)).Normal :=
    ⟨fun n hn g => conj_mem_oTwoUpper (Subgroup.le_normalizer (Subgroup.mem_top g)) hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oTwoUpper (⊤ : Subgroup Q)) with h | h
  · exfalso
    apply hQ
    intro x
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (⊤ : Subgroup Q) (Subgroup.mem_top x)
    rw [h, Subgroup.mem_bot] at hk
    exact ⟨k, hk⟩
  · exact h

theorem pCore_eq_bot_of_isSimple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : ¬ IsPGroup 2 Q) : CFSG.Open.pCore 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.Open.pCore 2 Q).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 Q) with h | h
  · exact h
  · exfalso
    apply hQ
    have hp : IsPGroup 2 (CFSG.Open.pCore 2 Q) := CFSG.LieType.BorelTits.pCore_isPGroup 2
    intro x
    obtain ⟨k, hk⟩ := hp ⟨x, h ▸ Subgroup.mem_top x⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem oTwoUpper_subgroupOf_self (X : Subgroup G) :
    (oTwoUpper X).subgroupOf X = oTwoUpper (⊤ : Subgroup ↥X) := by
  have h := oTwoUpper_map X.subtype (⊤ : Subgroup ↥X)
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rw [h]
  exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _

theorem map_oTwoUpper_eq_top_and_nonempty {X N : Subgroup G} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hQ : ¬ IsPGroup 2 Q) (φ : ↥X →* Q) (hφ : Function.Surjective φ)
    (hker : φ.ker = N.subgroupOf X) (hN : IsPGroup 2 N) :
    ((oTwoUpper X).subgroupOf X).map φ = ⊤ ∧
      Nonempty (oTwoQuot ↥(oTwoUpper X) ≃* Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : ((oTwoUpper X).subgroupOf X).map φ = ⊤ := by
    rw [oTwoUpper_subgroupOf_self, ← oTwoUpper_map, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hφ]
    exact oTwoUpper_top_eq_top hQ
  refine ⟨hmap, ?_⟩
  set K₂ := oTwoUpper X with hK₂
  let ψ : ↥K₂ →* Q := φ.comp (Subgroup.inclusion (oTwoUpper_le X))
  have hs : Function.Surjective ψ := by
    intro q
    have hq : q ∈ ((oTwoUpper X).subgroupOf X).map φ := by rw [hmap]; exact Subgroup.mem_top q
    obtain ⟨y, hy, rfl⟩ := hq
    exact ⟨⟨y, hy⟩, rfl⟩
  have hkerψ : CFSG.Open.pCore 2 ↥K₂ = ψ.ker := by
    refine le_antisymm ?_ ?_
    · set P := CFSG.Open.pCore 2 ↥K₂ with hP
      have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
      have hPp : IsPGroup 2 P := CFSG.LieType.BorelTits.pCore_isPGroup 2
      have hmapn : (P.map ψ).Normal := Subgroup.Normal.map hPn ψ hs
      have hle : P.map ψ ≤ CFSG.Open.pCore 2 Q :=
        CFSG.LieType.BorelTits.le_pCore 2 hmapn (hPp.map ψ)
      rw [pCore_eq_bot_of_isSimple hQ, le_bot_iff] at hle
      intro x hx
      have h1 : ψ x ∈ P.map ψ := Subgroup.mem_map_of_mem ψ hx
      rw [hle, Subgroup.mem_bot] at h1
      exact h1
    · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker ψ) ?_
      intro x
      have hx : Subgroup.inclusion (oTwoUpper_le X) (x : ↥K₂) ∈ φ.ker := x.2
      rw [hker, Subgroup.mem_subgroupOf] at hx
      obtain ⟨k, hk⟩ := hN ⟨_, hx⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hs)⟩

theorem eq_of_isSylowTwoOf_le_top {X : Type*} [Group X] [Finite X] {S Q : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) (hQ : IsPGroup 2 Q) (hSQ : S ≤ Q) : Q = S := by
  have hmul := Subgroup.relIndex_mul_relIndex S Q ⊤ hSQ le_top
  have hodd : ¬ 2 ∣ S.relIndex ⊤ := hS.2.2
  have hodd1 : ¬ 2 ∣ S.relIndex Q := fun h => hodd (h.trans ⟨_, hmul.symm⟩)
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : S.relIndex Q ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card S Q
  obtain ⟨m, -, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm : m = 0 := by
    by_contra hm0
    exact hodd1 (hmeq ▸ dvd_pow_self 2 hm0)
  have h1 : S.relIndex Q = 1 := by rw [hmeq, hm, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hSQ

theorem card_psl24' :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 := by
  rw [CFSG.Quasithin.card_psl_two_gf2 2 (by norm_num)]
  norm_num

theorem isSimpleGroup_psl24 :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num)

theorem not_isPGroup_psl24 :
    ¬ IsPGroup 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  intro hp
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [card_psl24'] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem not_isSolvable_psl24 :
    ¬ Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  have := isSimpleGroup_psl24
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  intro hc
  let _ : CommGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    { (inferInstance : Group _) with mul_comm := hc }
  have hp : (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2))).Prime :=
    IsSimpleGroup.prime_card
  rw [card_psl24'] at hp
  exact absurd hp (by norm_num)

theorem oTwoUpper_parabolic_facts {K T U X : Subgroup G}
    (hX : X = K ⊓ Subgroup.normalizer (U : Set G)) (hTK : IsSylowTwoOf (T ⊓ K) K)
    (hUTK : U ≤ T ⊓ K) (hTKN : T ⊓ K ≤ Subgroup.normalizer (U : Set G))
    (φ : ↥X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (hφs : Function.Surjective φ) (hφk : φ.ker = U.subgroupOf X) :
    IsL2Quot 2 (oTwoQuot ↥(oTwoUpper X)) ∧ ¬ Group.IsSolvable ↥(oTwoUpper X) ∧
      5 ∣ Nat.card ↥(oTwoUpper X) ∧ IsSylowTwoOf (T ⊓ oTwoUpper X) (oTwoUpper X) ∧
      oTwoUpper X ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper X : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  subst hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isSimpleGroup_psl24
  have hU2 : IsPGroup 2 U := hTK.2.1.to_le hUTK
  obtain ⟨hmap, hiso⟩ := map_oTwoUpper_eq_top_and_nonempty not_isPGroup_psl24 φ hφs hφk hU2
  let ψ : ↥(oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    φ.comp (Subgroup.inclusion (oTwoUpper_le _))
  have hψs : Function.Surjective ψ := by
    intro q
    have hq : q ∈ ((oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))).subgroupOf
        (K ⊓ Subgroup.normalizer (U : Set G))).map φ := by rw [hmap]; exact Subgroup.mem_top q
    obtain ⟨y, hy, rfl⟩ := hq
    exact ⟨⟨y, hy⟩, rfl⟩
  have hTKX : T ⊓ K ≤ K ⊓ Subgroup.normalizer (U : Set G) := le_inf inf_le_right hTKN
  have hTX : IsSylowTwoOf (T ⊓ K) (K ⊓ Subgroup.normalizer (U : Set G)) :=
    A4.isSylowTwoOf_mono hTK hTKX inf_le_left
  have hK₂X : oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)) ≤
      K ⊓ Subgroup.normalizer (U : Set G) := oTwoUpper_le _
  have hK₂K : oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)) ≤ K := hK₂X.trans inf_le_left
  have hTK₂ : IsSylowTwoOf (T ⊓ oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)))
      (oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))) := by
    have h1 := A4.isSylowTwoOf_inf_normal hTX hK₂X (le_normalizer_oTwoUpper _)
    rwa [inf_assoc, inf_eq_right.mpr hK₂K] at h1
  refine ⟨hiso, ?_, ?_, hTK₂, ?_⟩
  · intro hs
    exact not_isSolvable_psl24 (Group.isSolvable_of_surjective hψs)
  · have h1 := Subgroup.card_range_dvd ψ
    rw [MonoidHom.range_eq_top.mpr hψs, Subgroup.card_top, card_psl24'] at h1
    exact (by norm_num : 5 ∣ 60).trans h1
  ·
    have hY : ((T ⊓ K).subgroupOf (K ⊓ Subgroup.normalizer (U : Set G))).map φ =
        ((T ⊓ oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))).subgroupOf
          (oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)))).map ψ := by
      apply eq_of_isSylowTwoOf_le_top
      · exact isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTK₂) ψ hψs
      · exact (A4.isPGroup_subgroupOf_of_le hTX.1 hTX.2.1).map φ
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨Subgroup.inclusion (oTwoUpper_le _) y, ?_, rfl⟩
        exact ⟨hy.1, hK₂K y.2⟩
    have hsup : T ⊓ K = (T ⊓ oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))) ⊔ U := by
      apply le_antisymm
      · intro t ht
        have hmem : φ ⟨t, hTKX ht⟩ ∈
            ((T ⊓ oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))).subgroupOf
              (oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)))).map ψ := by
          rw [← hY]
          exact ⟨⟨t, hTKX ht⟩, ht, rfl⟩
        obtain ⟨y, hy, hyt⟩ := hmem
        have hker : (Subgroup.inclusion (oTwoUpper_le _) y)⁻¹ * ⟨t, hTKX ht⟩ ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv]
          change (ψ y)⁻¹ * _ = 1
          rw [hyt, inv_mul_cancel]
        rw [hφk, Subgroup.mem_subgroupOf] at hker
        have e : t = (y : G) * (((Subgroup.inclusion (oTwoUpper_le _) y)⁻¹ *
            ⟨t, hTKX ht⟩ : ↥(K ⊓ Subgroup.normalizer (U : Set G))) : G) := by
          simp
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hker)
      · exact sup_le (inf_le_inf_left T hK₂K) hUTK
    rw [hsup]
    exact le_normalizer_sup_of_le inf_le_right
      (fun x hx => (hK₂X hx.1).2)
end RankOne

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem isSylowTwoOf_inf_K : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
  A4.isSylowTwoOf_inf_normal (h.hyp.toHyp5_0_1.isSylowTwoOf h.hyp.hStar.1.1) (oTwoUpper_le H)
    (le_normalizer_oTwoUpper H)

theorem inf_normalizer_le_normalizer_inf_K (h510 : Stmt5_1_10) :
    M ⊓ Subgroup.normalizer (oTwoUpper H : Set G) ≤
      Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨-, -, hBorel, -⟩ := h510 G T M L H B D n h.hyp h.notation59
  have hMK := h.hyp.borel_eq hBorel
  have hTK := h.isSylowTwoOf_inf_K
  have hTKM : T ⊓ oTwoUpper H ≤ M ⊓ oTwoUpper H := inf_le_inf_right _ hh.T_le
  have hMKN :
      M ⊓ oTwoUpper H ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [hMK]
    exact inf_le_right
  have hTsyl : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
    A4.isSylowTwoOf_mono hTK hTKM inf_le_right
  have hO : pCoreOf 2 (M ⊓ oTwoUpper H) = T ⊓ oTwoUpper H :=
    le_antisymm (F7.isSylowTwoOf_pCoreOf_le hTsyl)
      (le_pCoreOf_of_le_normalizer 2 hTKM hMKN hTK.2.1)
  have h1 : M ⊓ Subgroup.normalizer (oTwoUpper H : Set G) ≤
      Subgroup.normalizer ((M ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans Subgroup.le_normalizer) inf_le_right).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rw [← hO]
  exact h1.trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem DBT_le_M_of_le {D' : Subgroup G} (hD'D : D' ≤ D) : D' ⊔ B ⊔ T ≤ M := by
  have hh := h.hyp.toHyp5_0_1
  refine sup_le (sup_le ?_ ?_) hh.T_le
  · exact hD'D.trans (h.notation59.2.1.1.trans (inf_le_left.trans hh.L_le))
  · exact h.notation59.1.1.trans inf_le_left

theorem DBT_le_Mp_of_le {D' : Subgroup G}
    (hD' : D' ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    D' ⊔ B ⊔ T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  sup_le (sup_le hD' (h.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))))
    h.T_le_Mp

theorem DBT_le_normalizer_inf_K_of_le (h510 : Stmt5_1_10) {D' : Subgroup G} (hD'D : D' ≤ D)
    (hD' : D' ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    D' ⊔ B ⊔ T ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
  (le_inf (h.DBT_le_M_of_le hD'D) (h.DBT_le_Mp_of_le hD')).trans
    (h.inf_normalizer_le_normalizer_inf_K h510)

theorem DBT_le_normalizer_inf_K (h510 : Stmt5_1_10)
    (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    D ⊔ B ⊔ T ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
  h.DBT_le_normalizer_inf_K_of_le h510 le_rfl hD

theorem DBT_le_normalizer_inf_L_of_le (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    {D' : Subgroup G} (hD'D : D' ≤ D) :
    D' ⊔ B ⊔ T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have hh := h.hyp.toHyp5_0_1
  refine sup_le (sup_le ?_ ?_) hh.T_le_normalizer_inf
  · exact hD'D.trans (h.notation59.2.1.1.trans inf_le_right)
  · exact (h.notation59.1.1.trans (le_of_eq (inf_comm M H))).trans
      (hh.inf_le_normalizer_inf h331 hR h.hyp.hStar)

theorem S_facts_of_le (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    {D' : Subgroup G} (hD'D : D' ≤ D) (hD' : D' ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    pCoreOf 2 (D' ⊔ B ⊔ T) ≤ T ∧ T ⊓ L ≤ pCoreOf 2 (D' ⊔ B ⊔ T) ∧
      T ⊓ oTwoUpper H ≤ pCoreOf 2 (D' ⊔ B ⊔ T) ∧ pCoreOf 2 M ≤ pCoreOf 2 (D' ⊔ B ⊔ T) ∧
      pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ pCoreOf 2 (D' ⊔ B ⊔ T) ∧
      D' ⊔ B ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (D' ⊔ B ⊔ T) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  have hTX : T ≤ D' ⊔ B ⊔ T := le_sup_right
  have hT2 : IsPGroup 2 T := hh.sylow.1
  refine ⟨F7.isSylowTwoOf_pCoreOf_le (hh.isSylowTwoOf hTX), ?_, ?_, ?_, ?_,
    le_normalizer_pCoreOf 2 _⟩
  · exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTX)
      (h.DBT_le_normalizer_inf_L_of_le h331 hR hD'D) (hT2.to_le inf_le_left)
  · exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTX)
      (h.DBT_le_normalizer_inf_K_of_le h510 hD'D hD') (hT2.to_le inf_le_left)
  · exact le_pCoreOf_of_le_normalizer 2
      ((F7.isSylowTwoOf_pCoreOf_le (hh.isSylowTwoOf hh.T_le)).trans hTX)
      ((h.DBT_le_M_of_le hD'D).trans (le_normalizer_pCoreOf 2 M)) (pCoreOf_isPGroup 2 M)
  · exact le_pCoreOf_of_le_normalizer 2
      ((F7.isSylowTwoOf_pCoreOf_le (hh.isSylowTwoOf h.T_le_Mp)).trans hTX)
      ((h.DBT_le_Mp_of_le hD').trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem S_facts (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    pCoreOf 2 (D ⊔ B ⊔ T) ≤ T ∧ T ⊓ L ≤ pCoreOf 2 (D ⊔ B ⊔ T) ∧
      T ⊓ oTwoUpper H ≤ pCoreOf 2 (D ⊔ B ⊔ T) ∧ pCoreOf 2 M ≤ pCoreOf 2 (D ⊔ B ⊔ T) ∧
      pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ pCoreOf 2 (D ⊔ B ⊔ T) ∧
      D ⊔ B ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (D ⊔ B ⊔ T) : Set G) :=
  h.S_facts_of_le h510 h331 hR le_rfl hD

theorem mem_K_of_mem_B {b : G} (hb : b ∈ B) : b ∈ oTwoUpper H := by
  have hodd : Odd (orderOf b) := by
    have h1 : orderOf b ∣ Nat.card B := by
      rw [← Subgroup.orderOf_mk b hb]
      exact orderOf_dvd_natCard _
    exact h.notation59.1.2.1.of_dvd_nat h1
  exact mem_oTwoUpper_of_odd (h.notation59.1.1 hb).2 hodd

theorem quotConjAut_eq_conj_of_mem_S_of_le (hTA : L34TwoAutFact) (h510 : Stmt5_1_10)
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) {D' : Subgroup G} (hD'D : D' ≤ D)
    (hD : D' ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {d₀ : G} (hd₀D : d₀ ∈ D')
    (hd₀3 : d₀ ^ 3 = 1) (hd₀ : ∀ k ∈ oTwoUpper H, d₀ * k⁻¹ ∉ centralizerModO2 (oTwoUpper H))
    {s : G} (hs : s ∈ pCoreOf 2 (D' ⊔ B ⊔ T))
    (hsN : s ∈ Subgroup.normalizer (oTwoUpper H : Set G)) :
    ∃ x ∈ imgO2 (oTwoUpper H) (T ⊓ oTwoUpper H),
      quotConjAut (oTwoUpper H) ⟨s, hsN⟩ = MulAut.conj x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set S := pCoreOf 2 (D' ⊔ B ⊔ T) with hSdef
  obtain ⟨hST, -, hTKS, -, -, hSN⟩ := h.S_facts_of_le h510 h331 hR hD'D hD
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  have hTK := h.isSylowTwoOf_inf_K
  have hOTK : pCoreOf 2 K ≤ T ⊓ K := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK
  have hd₀N : d₀ ∈ Subgroup.normalizer (K : Set G) := hD hd₀D
  have hBX : B ≤ D' ⊔ B ⊔ T := le_sup_right.trans le_sup_left
  have hDX : D' ≤ D' ⊔ B ⊔ T := le_sup_left.trans le_sup_left
  have hB3 : Nat.card B = 3 := h.card_B_eq_three h510
  obtain ⟨b₀, hb₀B, hb₀1⟩ : ∃ b₀ ∈ B, b₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
    rw [hbot, Subgroup.card_bot] at hB3
    omega
  have hb₀K : b₀ ∈ K := h.mem_K_of_mem_B hb₀B
  have hb₀N : b₀ ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    h.DBT_le_normalizer_inf_K_of_le h510 hD'D hD (hBX hb₀B)
  have hsT : s ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hST hs), hsN⟩
  obtain ⟨x, hx, hxe⟩ := hTA (O2Q K) h.l34 _ (isSylowTwoOf_imgO2 hTK)
    (quotConjAut K ⟨s, hsN⟩) (quotConjAut K ⟨d₀, hd₀N⟩)
    (exists_quotConjAut_pow_eq_one hS2 hs hsN)
    (map_quotConjAut_imgO2 inf_le_right ⟨s, hsN⟩ hsT)
    (by
      have e : (⟨d₀, hd₀N⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hd₀3)
      rw [← map_pow, e, map_one])
    (by
      rintro ⟨q, hq⟩
      induction q using QuotientGroup.induction_on with
      | H k =>
        apply hd₀ k k.2
        have h1 : quotConjAut K (⟨d₀, hd₀N⟩ * ⟨k, Subgroup.le_normalizer k.2⟩⁻¹) = 1 := by
          rw [map_mul, map_inv, quotConjAut_of_mem k, ← hq, mul_inv_cancel]
        exact mem_centralizerModO2_of_quotConjAut_eq_one h1)
    (by
      have hc : s * d₀ * s⁻¹ * d₀⁻¹ ∈ S := by
        have h1 : d₀ * s⁻¹ * d₀⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp (hSN (hDX hd₀D)) _).mp (S.inv_mem hs)
        have := S.mul_mem hs h1
        simpa [mul_assoc] using this
      obtain ⟨m, hm⟩ := exists_quotConjAut_pow_eq_one (K := K) hS2 hc
        ((Subgroup.normalizer (K : Set G)).mul_mem ((Subgroup.normalizer (K : Set G)).mul_mem
          ((Subgroup.normalizer (K : Set G)).mul_mem hsN hd₀N)
          ((Subgroup.normalizer (K : Set G)).inv_mem hsN))
          ((Subgroup.normalizer (K : Set G)).inv_mem hd₀N))
      refine ⟨m, ?_⟩
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact hm)
    _ (mk_mem_normalizer_imgO2 inf_le_right hb₀K hb₀N)
    (by
      rw [mk_mem_imgO2_iff hOTK]
      intro hb
      apply hb₀1
      have h2 : ∃ m : ℕ, b₀ ^ 2 ^ m = 1 := by
        obtain ⟨m, hm⟩ := (h.hyp.toHyp5_0_1.sylow.1.to_le inf_le_left) ⟨b₀, hb⟩
        exact ⟨m, by simpa using congrArg Subtype.val hm⟩
      obtain ⟨m, hm⟩ := h2
      have hodd : Odd (orderOf b₀) := by
        have h1 : orderOf b₀ ∣ Nat.card B := by
          rw [← Subgroup.orderOf_mk b₀ hb₀B]
          exact orderOf_dvd_natCard _
        exact h.notation59.1.2.1.of_dvd_nat h1
      have hd : orderOf b₀ ∣ Nat.gcd (2 ^ m) (orderOf b₀) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) dvd_rfl
      rw [Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)] at hd
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))
    (by
      have hsb : s * b₀ * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hsN b₀).mp hb₀K
      have hc : s * b₀ * s⁻¹ * b₀⁻¹ ∈ T ⊓ K := by
        refine ⟨hST ?_, K.mul_mem hsb (K.inv_mem hb₀K)⟩
        have h1 : b₀ * s⁻¹ * b₀⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp (hSN (hBX hb₀B)) _).mp (S.inv_mem hs)
        have := S.mul_mem hs h1
        simpa [mul_assoc] using this
      have e : quotConjAut K ⟨s, hsN⟩ (QuotientGroup.mk ⟨b₀, hb₀K⟩) *
          (QuotientGroup.mk ⟨b₀, hb₀K⟩ : O2Q K)⁻¹ =
          QuotientGroup.mk (⟨s * b₀ * s⁻¹ * b₀⁻¹, hc.2⟩ : ↥K) := by
        rw [quotConjAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      rw [e]
      exact mk_mem_imgO2 hc.2 hc)
  exact ⟨x, hx, hxe⟩

theorem quotConjAut_eq_conj_of_mem_S (hTA : L34TwoAutFact) (h510 : Stmt5_1_10)
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {d₀ : G} (hd₀D : d₀ ∈ D)
    (hd₀3 : d₀ ^ 3 = 1) (hd₀ : ∀ k ∈ oTwoUpper H, d₀ * k⁻¹ ∉ centralizerModO2 (oTwoUpper H))
    {s : G} (hs : s ∈ pCoreOf 2 (D ⊔ B ⊔ T))
    (hsN : s ∈ Subgroup.normalizer (oTwoUpper H : Set G)) :
    ∃ x ∈ imgO2 (oTwoUpper H) (T ⊓ oTwoUpper H),
      quotConjAut (oTwoUpper H) ⟨s, hsN⟩ = MulAut.conj x :=
  h.quotConjAut_eq_conj_of_mem_S_of_le hTA h510 h331 hR le_rfl hD hd₀D hd₀3 hd₀ hs hsN

theorem exists_parabolic (hPF : L34ParabolicFact) (hTA : L34TwoAutFact) (h510 : Stmt5_1_10)
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {d₀ : G} (hd₀D : d₀ ∈ D)
    (hd₀3 : d₀ ^ 3 = 1) (hd₀ : ∀ k ∈ oTwoUpper H, d₀ * k⁻¹ ∉ centralizerModO2 (oTwoUpper H)) :
    ∃ U : Subgroup G, pCoreOf 2 (oTwoUpper H) ≤ U ∧ U ≤ T ⊓ oTwoUpper H ∧
      (∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (oTwoUpper H)) ∧
      (∀ x ∈ U, x ^ 2 ∈ pCoreOf 2 (oTwoUpper H)) ∧
      Nat.card U = 16 * Nat.card (pCoreOf 2 (oTwoUpper H)) ∧
      D ⊔ B ⊔ pCoreOf 2 (D ⊔ B ⊔ T) ≤ Subgroup.normalizer (U : Set G) ∧
      ∃ φ : ↥(oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) →*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
        Function.Surjective φ ∧
          φ.ker = U.subgroupOf (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set S := pCoreOf 2 (D ⊔ B ⊔ T) with hSdef
  obtain ⟨hST, -, -, -, -, -⟩ := h.S_facts h510 h331 hR hD
  have hTK := h.isSylowTwoOf_inf_K
  have hOTK : pCoreOf 2 K ≤ T ⊓ K := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK
  have hBX : B ≤ D ⊔ B ⊔ T := le_sup_right.trans le_sup_left
  have hDX : D ≤ D ⊔ B ⊔ T := le_sup_left.trans le_sup_left
  have hXN := h.DBT_le_normalizer_inf_K h510 hD
  obtain ⟨P, R, hNP, hRS, hNR, hRab, hR16, ⟨π, hπs, hπk⟩, hodd⟩ :=
    hPF (O2Q K) h.l34 _ (isSylowTwoOf_imgO2 hTK)
  set U := preimageModTwoCore K R with hUdef
  have hUK : U ≤ K := preimageModTwoCore_le K R
  have hOU : pCoreOf 2 K ≤ U := pCoreOf_le_preimageModTwoCore K R
  have hUTK : U ≤ T ⊓ K :=
    (preimageModTwoCore_mono hRS).trans (preimageModTwoCore_imgO2 hOTK inf_le_right).le
  have hRU : imgO2 K U = R := imgO2_preimageModTwoCore K R
  have hoddN : ∀ g ∈ Subgroup.normalizer (K : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) → Odd (orderOf g) →
        g ∈ Subgroup.normalizer (U : Set G) := by
    intro g hgK hgT hgo
    apply mem_normalizer_preimageModTwoCore ⟨g, hgK⟩
    apply hodd
    · refine hgo.of_dvd_nat ((orderOf_map_dvd _ _).trans ?_)
      rw [Subgroup.orderOf_mk]
    · exact map_quotConjAut_imgO2 inf_le_right ⟨g, hgK⟩ hgT
  have hoddD : ∀ x ∈ D, Odd (orderOf x) := fun x hx =>
    h.notation59.2.1.2.1.of_dvd_nat
      (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _)
  have hoddB : ∀ x ∈ B, Odd (orderOf x) := fun x hx =>
    h.notation59.1.2.1.of_dvd_nat (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _)
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    h.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))
  have hTMp := h.T_le_Mp
  refine ⟨U, hOU, hUTK, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy
    obtain ⟨hxK, hxR⟩ := mem_preimageModTwoCore.mp hx
    obtain ⟨hyK, hyR⟩ := mem_preimageModTwoCore.mp hy
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem hxK hyK) (K.inv_mem hxK)) (K.inv_mem hyK)
    rw [mem_pCoreOf_iff_mk_eq_one hmem]
    have e : (⟨x * y * x⁻¹ * y⁻¹, hmem⟩ : ↥K) =
        ⟨x, hxK⟩ * ⟨y, hyK⟩ * (⟨x, hxK⟩ : ↥K)⁻¹ * (⟨y, hyK⟩ : ↥K)⁻¹ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    have hc : (QuotientGroup.mk ⟨x, hxK⟩ : O2Q K) * QuotientGroup.mk ⟨y, hyK⟩ =
        QuotientGroup.mk ⟨y, hyK⟩ * QuotientGroup.mk ⟨x, hxK⟩ :=
      congrArg Subtype.val (hRab.1.is_comm.comm ⟨_, hxR⟩ ⟨_, hyR⟩)
    rw [hc]
    group
  ·
    intro x hx
    obtain ⟨hxK, hxR⟩ := mem_preimageModTwoCore.mp hx
    rw [mem_pCoreOf_iff_mk_eq_one (K.pow_mem hxK 2)]
    have e : (⟨x ^ 2, K.pow_mem hxK 2⟩ : ↥K) = (⟨x, hxK⟩ : ↥K) ^ 2 := rfl
    rw [e, QuotientGroup.mk_pow]
    exact hRab.2 _ hxR
  · rw [card_preimageModTwoCore, hR16]
  · refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      exact hoddN x (hD hx) (hXN (hDX hx)) (hoddD x hx)
    · intro x hx
      exact hoddN x (hBK hx) (hXN (hBX hx)) (hoddB x hx)
    · intro s hs
      have hsN : s ∈ Subgroup.normalizer (K : Set G) := hTMp (hST hs)
      obtain ⟨x, hx, hxe⟩ := h.quotConjAut_eq_conj_of_mem_S hTA h510 h331 hR hD hd₀D hd₀3 hd₀ hs hsN
      apply mem_normalizer_preimageModTwoCore ⟨s, hsN⟩
      rw [hxe]
      have hxR : x ∈ Subgroup.normalizer (R : Set (O2Q K)) := hNR ▸ hNP (Subgroup.le_normalizer hx)
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxR
  ·
    have hP : ∀ x : ↥(K ⊓ Subgroup.normalizer (U : Set G)),
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left) x) ∈ P := by
      intro x
      rw [← hNR, ← hRU]
      exact mk_mem_normalizer_imgO2 hUK x.2.1 x.2.2
    let ψ : ↥(K ⊓ Subgroup.normalizer (U : Set G)) →* ↥P :=
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left)).codRestrict P hP
    refine ⟨π.comp ψ, ?_, ?_⟩
    · intro q
      obtain ⟨⟨y, hyP⟩, rfl⟩ := hπs q
      induction y using QuotientGroup.induction_on with
      | H k =>
        have hkN : (k : G) ∈ Subgroup.normalizer (U : Set G) := by
          refine mem_normalizer_preimageModTwoCore (K := K)
            (⟨(k : G), Subgroup.le_normalizer k.2⟩ : ↥(Subgroup.normalizer (K : Set G))) ?_
          rw [quotConjAut_of_mem k]
          have hkR : (QuotientGroup.mk k : O2Q K) ∈ Subgroup.normalizer (R : Set (O2Q K)) :=
            hNR ▸ hyP
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hkR
        exact ⟨⟨k, k.2, hkN⟩, congrArg π (Subtype.ext rfl)⟩
    · ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπk,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact mem_preimageModTwoCore.mpr ⟨x.2.1, hx⟩
      · intro hx
        exact (mem_preimageModTwoCore.mp hx).2

omit [Finite G] h in
theorem mem_normalizer_oTwoUpper_inf {K U : Subgroup G} {g : G}
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer
      (oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)) : Set G) :=
  normalizer_le_normalizer_oTwoUpper _
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hgK, Subgroup.le_normalizer hgU⟩)

end Hyp5_1_14

end Setting

end CFSG.Quasithin.H13
