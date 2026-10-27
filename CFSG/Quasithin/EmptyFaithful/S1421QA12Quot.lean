module

public import CFSG.Quasithin.EmptyFaithful.S1421QA12Borel
public import CFSG.Quasithin.Background.C2PushLift
public import CFSG.Quasithin.EmptyFaithful.S1421QEx
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualAbs
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace QA12

section Transfer

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

abbrev piK (K : Subgroup G) : ↥K →* OTwoQuot K := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)

omit [Finite G] in
theorem imageOTwoQuot_self (K : Subgroup G) : imageOTwoQuot K K = ⊤ := by
  unfold imageOTwoQuot
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

omit [Finite G] in
theorem mk_mem_iff {A : Subgroup G} (hW : pCoreOf 2 K ≤ A) (z : ↥K) :
    (QuotientGroup.mk z : OTwoQuot K) ∈ imageOTwoQuot K A ↔ (z : G) ∈ A := by
  have h := imageOTwoQuot_comap hW
  have h2 : z ∈ (imageOTwoQuot K A).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)) ↔
      z ∈ A.subgroupOf K := by rw [h]
  simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using h2

omit [Finite G] in
theorem imageOTwoQuot_inj {A B : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K) (hWA : pCoreOf 2 K ≤ A)
    (hWB : pCoreOf 2 K ≤ B) (h : imageOTwoQuot K A = imageOTwoQuot K B) : A = B := by
  ext x
  constructor
  · intro hx
    have h1 := (mk_mem_iff hWA ⟨x, hAK hx⟩).mpr hx
    rw [h] at h1
    exact (mk_mem_iff hWB ⟨x, hAK hx⟩).mp h1
  · intro hx
    have h1 := (mk_mem_iff hWB ⟨x, hBK hx⟩).mpr hx
    rw [← h] at h1
    exact (mk_mem_iff hWA ⟨x, hBK hx⟩).mp h1

omit [Finite G] in
theorem exists_preimage (A : Subgroup (OTwoQuot K)) :
    ∃ A₀ : Subgroup G, A₀ ≤ K ∧ pCoreOf 2 K ≤ A₀ ∧ imageOTwoQuot K A₀ = A ∧
      ∀ z : ↥K, (z : G) ∈ A₀ ↔ (QuotientGroup.mk z : OTwoQuot K) ∈ A := by
  refine ⟨(A.comap (piK K)).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ :=
      Subgroup.mem_map.mp (show x ∈ (CFSG.Open.pCore 2 ↥K).map K.subtype from hx)
    exact Subgroup.mem_map.mpr ⟨y, by
      show piK K y ∈ A
      rw [show piK K y = 1 from (QuotientGroup.eq_one_iff y).mpr hy]
      exact A.one_mem, rfl⟩
  · ext u
    rw [mem_imageOTwoQuot_iff]
    constructor
    · rintro ⟨x, hx, hxA, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxA
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      subst this
      exact hy
    · intro hu
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective u
      exact ⟨z, z.2, Subgroup.mem_map.mpr ⟨z, hu, rfl⟩, rfl⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
      have : y = z := Subtype.ext hyz
      subst this
      exact hy
    · intro hz
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩

omit [Finite G] in
theorem covBy_comap_of_surjective {H H' : Type*} [Group H] [Group H'] {π : H →* H'}
    (hπ : Function.Surjective π) {A B : Subgroup H'} (h : A ⋖ B) : A.comap π ⋖ B.comap π := by
  refine ⟨lt_of_le_of_ne (Subgroup.comap_mono h.le) fun he => h.ne ?_, fun C hAC hCB => ?_⟩
  · have := congrArg (Subgroup.map π) he
    rwa [Subgroup.map_comap_eq_self_of_surjective hπ,
      Subgroup.map_comap_eq_self_of_surjective hπ] at this
  · have hker : π.ker ≤ A.comap π := fun x hx => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact A.one_mem
    have hCC : (C.map π).comap π = C := Subgroup.comap_map_eq_self (hker.trans hAC.le)
    refine h.2 (c := C.map π) ?_ ?_
    · refine lt_of_le_of_ne ?_ fun he => hAC.ne ?_
      · rw [← Subgroup.map_comap_eq_self_of_surjective hπ A]
        exact Subgroup.map_mono hAC.le
      · have := congrArg (Subgroup.comap π) he
        rw [hCC] at this
        exact this
    · refine lt_of_le_of_ne ?_ fun he => hCB.ne ?_
      · have := Subgroup.map_mono (f := π) hCB.le
        rwa [Subgroup.map_comap_eq_self_of_surjective hπ] at this
      · have := congrArg (Subgroup.comap π) he
        rw [hCC] at this
        exact this

omit [Finite G] in
theorem covBy_image_iff {A : Subgroup G} (hAK : A ≤ K) (hW : pCoreOf 2 K ≤ A) :
    A ⋖ K ↔ imageOTwoQuot K A ⋖ ⊤ := by
  have hsurj : Function.Surjective (piK K) := QuotientGroup.mk'_surjective _
  have hcomap := imageOTwoQuot_comap hW
  constructor
  · intro h
    have h1 : A.subgroupOf K ⋖ ⊤ := by
      rw [CFSG.QuasithinUnique.Setup.X6.covBy_top_iff_map_subtype,
        Subgroup.map_subgroupOf_eq_of_le hAK]
      exact h
    have hker : (piK K).ker ≤ A.subgroupOf K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hW ((mk_eq_one_iff_mem_pCoreOf x).mp (MonoidHom.mem_ker.mp hx))
    have := CFSG.QuasithinUnique.Setup.X7a.covBy_map_of_ker_le hsurj hker h1
    rwa [Subgroup.map_top_of_surjective _ hsurj] at this
  · intro h
    have h1 := covBy_comap_of_surjective hsurj h
    rw [hcomap, Subgroup.comap_top] at h1
    rw [CFSG.QuasithinUnique.Setup.X6.covBy_top_iff_map_subtype,
      Subgroup.map_subgroupOf_eq_of_le hAK] at h1
    exact h1

theorem isSylowTwoOf_image_top {U : Subgroup G} (hU : IsSylowTwoOf U K)
    (hW : pCoreOf 2 K ≤ U) : IsSylowTwoOf (imageOTwoQuot K U) ⊤ := by
  have h := (C2Push.isSylowTwoOf_imageOTwoQuot_iff (M := K) (A := K) (S := U) le_rfl hU.1 hU.2.1
    (inf_le_right.trans hW)).mp hU
  rwa [imageOTwoQuot_self] at h

omit [Finite G] in
theorem normalizer_image_eq {U : Subgroup G} (hUK : U ≤ K) (hW : pCoreOf 2 K ≤ U) :
    Subgroup.normalizer (imageOTwoQuot K U : Set (OTwoQuot K)) =
      imageOTwoQuot K (K ⊓ Subgroup.normalizer (U : Set G)) := by
  have hWN : pCoreOf 2 K ≤ K ⊓ Subgroup.normalizer (U : Set G) := fun w hw =>
    ⟨pCoreOf_le 2 K hw, Subgroup.le_normalizer (hW hw)⟩
  ext u
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective u
  rw [mk_mem_iff hWN z, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
    Subgroup.mem_normalizer_iff]
  have hz : (z : G) ∈ K := z.2
  refine ⟨fun h => ⟨hz, fun g => ?_⟩, fun hh => fun ū => ?_⟩
  · constructor
    · intro hg
      have hgK : g ∈ K := hUK hg
      have h1 := (h (QuotientGroup.mk ⟨g, hgK⟩)).mp ((mk_mem_iff hW ⟨g, hgK⟩).mpr hg)
      have e : (QuotientGroup.mk z * QuotientGroup.mk ⟨g, hgK⟩ * (QuotientGroup.mk z)⁻¹ :
          OTwoQuot K) = QuotientGroup.mk (z * ⟨g, hgK⟩ * z⁻¹) := by
        simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [e] at h1
      exact (mk_mem_iff hW _).mp h1
    · intro hg
      have hgK : g ∈ K := by
        have : (z : G)⁻¹ * (z * g * z⁻¹) * z ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem hz) (hUK hg)) hz
        simpa [mul_assoc] using this
      have h1 : (QuotientGroup.mk z * QuotientGroup.mk ⟨g, hgK⟩ * (QuotientGroup.mk z)⁻¹ :
          OTwoQuot K) ∈ imageOTwoQuot K U := by
        have e : (QuotientGroup.mk z * QuotientGroup.mk ⟨g, hgK⟩ * (QuotientGroup.mk z)⁻¹ :
            OTwoQuot K) = QuotientGroup.mk (z * ⟨g, hgK⟩ * z⁻¹) := by
          simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [e]
        exact (mk_mem_iff hW _).mpr hg
      exact (mk_mem_iff hW ⟨g, hgK⟩).mp ((h (QuotientGroup.mk ⟨g, hgK⟩)).mpr h1)
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ū
    have e : (QuotientGroup.mk z * QuotientGroup.mk y * (QuotientGroup.mk z)⁻¹ : OTwoQuot K) =
        QuotientGroup.mk (z * y * z⁻¹) := by
      simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [e, mk_mem_iff hW, mk_mem_iff hW]
    exact hh.2 (y : G)

omit [Finite G] in
theorem image_perfectCore [Finite G] {A : Subgroup G} (hAK : A ≤ K) :
    imageOTwoQuot K (perfectCore A) = perfectCore (imageOTwoQuot K A) := by
  have h1 := map_perfectCore K.subtype (A.subgroupOf K)
  rw [Subgroup.map_subgroupOf_eq_of_le hAK] at h1
  have h2 : (perfectCore A).subgroupOf K = perfectCore (A.subgroupOf K) := by
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  unfold imageOTwoQuot
  rw [h2]
  exact map_perfectCore (piK K) (A.subgroupOf K)

omit [Finite G] in
theorem ker_piK_le {X : Subgroup G} (hW : pCoreOf 2 K ≤ X) : (piK K).ker ≤ X.subgroupOf K := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  exact hW ((mk_eq_one_iff_mem_pCoreOf x).mp (MonoidHom.mem_ker.mp hx))

theorem card_image_of_odd {B : Subgroup G} (hBK : B ≤ K) (hB : Odd (Nat.card B)) :
    Nat.card (imageOTwoQuot K B) = Nat.card B := by
  have hinj : Function.Injective ((piK K).comp (B.subgroupOf K).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : piK K (x : ↥K) = 1 := MonoidHom.mem_ker.mp hx
    have hmem : ((x : ↥K) : G) ∈ pCoreOf 2 K := (mk_eq_one_iff_mem_pCoreOf _).mp hx1
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 K) ⟨_, hmem⟩
    have hpow : (((x : ↥K) : G)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hxB : ((x : ↥K) : G) ∈ B := Subgroup.mem_subgroupOf.mp x.2
    have hodd : Odd (orderOf ((x : ↥K) : G)) :=
      hB.of_dvd_nat (Subgroup.orderOf_dvd_natCard B hxB)
    have h1 : orderOf ((x : ↥K) : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
    have hcop : Nat.Coprime (orderOf ((x : ↥K) : G)) (2 ^ k) :=
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)).symm
    have h2 : orderOf ((x : ↥K) : G) = 1 := Nat.Coprime.eq_one_of_dvd hcop h1
    have h3 : ((x : ↥K) : G) = 1 := orderOf_eq_one_iff.mp h2
    have h4 : x = 1 := Subtype.ext (Subtype.ext h3)
    simp [h4]
  have hrange : ((piK K).comp (B.subgroupOf K).subtype).range = imageOTwoQuot K B := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv]

theorem isHallOdd_image {B X : Subgroup G} (hB : S1421.IsHallOdd B X) (hXK : X ≤ K)
    (hW : pCoreOf 2 K ≤ X) : S1421.IsHallOdd (imageOTwoQuot K B) (imageOTwoQuot K X) := by
  have hBK : B ≤ K := hB.1.trans hXK
  refine ⟨imageOTwoQuot_mono hB.1, ?_, ?_⟩
  · rw [card_image_of_odd hBK hB.2.1]
    exact hB.2.1
  · obtain ⟨k, hk⟩ := hB.2.2
    have h1 : (imageOTwoQuot K B).relIndex (imageOTwoQuot K X) ∣ 2 ^ k := by
      unfold imageOTwoQuot
      rw [Subgroup.relIndex_map_map, sup_eq_left.mpr (ker_piK_le hW), ← hk,
        ← Subgroup.relIndex_subgroupOf hXK]
      exact Subgroup.relIndex_dvd_of_le_left _ le_sup_left
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨j, hj⟩

omit [Finite G] in
theorem imageOTwoQuot_pCoreOf (K : Subgroup G) : imageOTwoQuot K (pCoreOf 2 K) = ⊥ := by
  ext u
  rw [mem_imageOTwoQuot_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨x, hx, hxW, rfl⟩
    exact (mk_eq_one_iff_mem_pCoreOf ⟨x, hx⟩).mpr hxW
  · rintro rfl
    exact ⟨1, K.one_mem, (pCoreOf 2 K).one_mem, rfl⟩

omit [Finite G] in
theorem imageOTwoQuot_sup_pCoreOf {X : Subgroup G} (hXK : X ≤ K) :
    imageOTwoQuot K (X ⊔ pCoreOf 2 K) = imageOTwoQuot K X := by
  rw [imageOTwoQuot_sup hXK (pCoreOf_le 2 K), imageOTwoQuot_pCoreOf, sup_bot_eq]

theorem mk_mem_perfectCore_iff {A : Subgroup G} (hAK : A ≤ K) (z : ↥K) :
    (QuotientGroup.mk z : OTwoQuot K) ∈ perfectCore (imageOTwoQuot K A) ↔
      (z : G) ∈ perfectCore A ⊔ pCoreOf 2 K := by
  rw [← image_perfectCore hAK, ← imageOTwoQuot_sup_pCoreOf ((perfectCore_le A).trans hAK)]
  exact mk_mem_iff le_sup_right z

theorem mem_of_mem_sup_pCoreOf {A : Subgroup G}
    (hWA : pCoreOf 2 K ≤ Subgroup.normalizer (A : Set G))
    {b : G} (hb : b ∈ A ⊔ pCoreOf 2 K) (hodd : Odd (orderOf b)) : b ∈ A := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hWA] at hb
  obtain ⟨a, ha, w, hw, hab⟩ := hb
  have hab' : a * w = b := hab
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 K) ⟨w, hw⟩
  have hwk : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨x', hx', hpow⟩ := A4.exists_pow_mul_eq ha (hWA hw) (2 ^ k)
  have hbk : b ^ 2 ^ k ∈ A := by
    rw [← hab', hpow, hwk, mul_one]
    exact hx'
  have hcop : Nat.Coprime (2 ^ k) (orderOf b) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact (Subgroup.zpowers_le.mpr hbk) (A4.mem_zpowers_pow_of_coprime hcop)

omit [Finite G] in
theorem isTwoParabolicsOver_image {U P P' : Subgroup G} (hUK : U ≤ K) (hW : pCoreOf 2 K ≤ U)
    (hPK : P ≤ K) (hP'K : P' ≤ K) (hne : P ≠ P') (hUP : U ≤ P) (hUP' : U ≤ P')
    (hBor : K ⊓ Subgroup.normalizer (U : Set G) ≤ P ⊓ P')
    (hcov : ∀ A : Subgroup G, U ≤ A → A ≤ K → (A ⋖ K ↔ A = P ∨ A = P')) :
    IsTwoParabolicsOver (imageOTwoQuot K U) (imageOTwoQuot K P) (imageOTwoQuot K P') := by
  have hWP : pCoreOf 2 K ≤ P := hW.trans hUP
  have hWP' : pCoreOf 2 K ≤ P' := hW.trans hUP'
  refine ⟨fun h => hne (imageOTwoQuot_inj hPK hP'K hWP hWP' h), imageOTwoQuot_mono hUP,
    imageOTwoQuot_mono hUP', ?_, fun A hA => ?_⟩
  · rw [normalizer_image_eq hUK hW]
    exact le_inf (imageOTwoQuot_mono (hBor.trans inf_le_left))
      (imageOTwoQuot_mono (hBor.trans inf_le_right))
  · obtain ⟨A₀, hA₀K, hWA₀, hA₀A, hmem⟩ := exists_preimage A
    have hUA₀ : U ≤ A₀ := fun u hu =>
      (hmem ⟨u, hUK hu⟩).mpr (hA ((mk_mem_iff hW ⟨u, hUK hu⟩).mpr hu))
    rw [← hA₀A, ← covBy_image_iff hA₀K hWA₀, hcov A₀ hUA₀ hA₀K]
    exact or_congr ⟨fun h => h ▸ rfl, fun h => imageOTwoQuot_inj hA₀K hPK hWA₀ hWP h⟩
      ⟨fun h => h ▸ rfl, fun h => imageOTwoQuot_inj hA₀K hP'K hWA₀ hWP' h⟩

end Transfer

section LieStep

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem mem_sup_of_swap (st : Setting1427 T M H K1) {t : G} (htQ : t ∈ pCoreOf 2 M)
    {P Q : Subgroup G} (hconj : P.map (MulAut.conj t).toMonoidHom = Q)
    (hUQ : T ⊓ oTwoUpper H ≤ perfectCore Q ⊔ pCoreOf 2 (oTwoUpper H)) {b : G}
    (hbM : b ∈ M ⊓ oTwoUpper H) (hb : b ∈ perfectCore P ⊔ pCoreOf 2 (oTwoUpper H)) :
    b ∈ perfectCore Q ⊔ pCoreOf 2 (oTwoUpper H) := by
  have htT : t ∈ T := pCoreOf_M_le_T st htQ
  have hc := commutator_mem_inf st htQ hbM
  have hWinv : (pCoreOf 2 (oTwoUpper H)).map (MulAut.conj t).toMonoidHom =
      pCoreOf 2 (oTwoUpper H) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_pCoreOf 2 _ (T_le_normalizer_K st htT))
  have h1 : t * b * t⁻¹ ∈ perfectCore Q ⊔ pCoreOf 2 (oTwoUpper H) := by
    have hmem : (MulAut.conj t).toMonoidHom b ∈
        (perfectCore P ⊔ pCoreOf 2 (oTwoUpper H)).map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hb
    rw [Subgroup.map_sup, map_perfectCore, hconj, hWinv] at hmem
    simpa [MulAut.conj_apply] using hmem
  have e : b = (t * b * t⁻¹ * b⁻¹)⁻¹ * (t * b * t⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUQ hc)) h1

theorem lie_step
    (hR1 : LieSylowLePerfectCore) (hR2 : LieTorusCoincide)
    (st : Setting1427 T M H K1) (hK : oTwoUpper H ∈ cComp H)
    (hs3 : ShapeL3Sp4 T K1 (oTwoUpper H)) {t : G} (htQ : t ∈ pCoreOf 2 M)
    (htK1 : t ∉ Subgroup.normalizer (K1 : Set G)) {B : Subgroup G}
    (hB : S1421.IsHallOdd B (M ⊓ oTwoUpper H)) :
    IsPSL 3 2 2 (OTwoQuot (oTwoUpper H)) ∧ B ≤ K1 ∧ Nat.card B = 3 := by
  have htT : t ∈ T := pCoreOf_M_le_T st htQ
  obtain ⟨P, P', hne, hP, hP', hBor, hK1P, hcov⟩ := hs3.parabolic
  obtain ⟨n, hn2, -, hcen⟩ := hs3.exists_n
  have hex := exactType_oTwoQuot (perfect_of_mem_cComp hK) hn2 hcen
  have hTH : T ≤ H := st.hStar.1.1
  have hSylT : IsSylowTwoOf T H := isSylowTwoOf_of_isSylowTwo st.hyp.sylow hTH
  have hSylU : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hSylT (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hWU : pCoreOf 2 (oTwoUpper H) ≤ T ⊓ oTwoUpper H := pCoreOf_two_le_of_isSylowTwoOf hSylU
  have hUK : T ⊓ oTwoUpper H ≤ oTwoUpper H := inf_le_right
  have hPK : P ≤ oTwoUpper H := hP.1.1
  have hP'K : P' ≤ oTwoUpper H := hP'.1.1
  have hUP : T ⊓ oTwoUpper H ≤ P := fun x hx => (hBor ⟨hx.2, Subgroup.le_normalizer hx⟩).1
  have hUP' : T ⊓ oTwoUpper H ≤ P' := fun x hx => (hBor ⟨hx.2, Subgroup.le_normalizer hx⟩).2
  have hSyl := isSylowTwoOf_image_top hSylU hWU
  have hPar := isTwoParabolicsOver_image hUK hWU hPK hP'K hne hUP hUP' hBor hcov
  obtain ⟨hU1, hU2⟩ := hR1 (OTwoQuot (oTwoUpper H)) n hn2 hex _ _ _ hSyl hPar
  obtain ⟨hc1, hc2⟩ := map_conj_swap st hne hP hP' hBor hK1P hcov htT htK1
  have hUsup : ∀ {Q : Subgroup G}, Q ≤ oTwoUpper H →
      imageOTwoQuot (oTwoUpper H) (T ⊓ oTwoUpper H) ≤
        perfectCore (imageOTwoQuot (oTwoUpper H) Q) →
      T ⊓ oTwoUpper H ≤ perfectCore Q ⊔ pCoreOf 2 (oTwoUpper H) := by
    intro Q hQK hle u hu
    exact (mk_mem_perfectCore_iff hQK ⟨u, hUK hu⟩).mp
      (hle ((mk_mem_iff hWU ⟨u, hUK hu⟩).mpr hu))
  have hUP1 := hUsup hPK hU1
  have hUP2 := hUsup hP'K hU2
  have hBM : B ≤ M ⊓ oTwoUpper H := hB.1
  have hBK : B ≤ oTwoUpper H := hBM.trans inf_le_right
  have hEq : imageOTwoQuot (oTwoUpper H) B ⊓ perfectCore (imageOTwoQuot (oTwoUpper H) P) =
      imageOTwoQuot (oTwoUpper H) B ⊓ perfectCore (imageOTwoQuot (oTwoUpper H) P') := by
    have key : ∀ {Q Q' : Subgroup G}, Q ≤ oTwoUpper H → Q' ≤ oTwoUpper H →
        Q.map (MulAut.conj t).toMonoidHom = Q' →
        T ⊓ oTwoUpper H ≤ perfectCore Q' ⊔ pCoreOf 2 (oTwoUpper H) →
        ∀ u, u ∈ imageOTwoQuot (oTwoUpper H) B →
          u ∈ perfectCore (imageOTwoQuot (oTwoUpper H) Q) →
          u ∈ perfectCore (imageOTwoQuot (oTwoUpper H) Q') := by
      intro Q Q' hQK hQ'K hconj hUQ' u huB huQ
      obtain ⟨x, hxK, hxB, rfl⟩ := mem_imageOTwoQuot_iff.mp huB
      have h1 := (mk_mem_perfectCore_iff hQK ⟨x, hxK⟩).mp huQ
      have h2 := mem_sup_of_swap st htQ hconj hUQ' (hBM hxB) h1
      exact (mk_mem_perfectCore_iff hQ'K ⟨x, hxK⟩).mpr h2
    ext u
    constructor
    · rintro ⟨huB, huP⟩
      exact ⟨huB, key hPK hP'K hc1 hUP2 u huB huP⟩
    · rintro ⟨huB, huP⟩
      exact ⟨huB, key hP'K hPK hc2 hUP1 u huB huP⟩
  have hMK := inf_eq_inf_normalizer st hs3
  have hWMK : pCoreOf 2 (oTwoUpper H) ≤ M ⊓ oTwoUpper H := fun w hw =>
    ⟨st.hyp.m_max.1.2 (hWU hw).1, (hWU hw).2⟩
  have hHall : S1421.IsHallOdd (imageOTwoQuot (oTwoUpper H) B)
      (Subgroup.normalizer (imageOTwoQuot (oTwoUpper H) (T ⊓ oTwoUpper H) :
        Set (OTwoQuot (oTwoUpper H)))) := by
    rw [normalizer_image_eq hUK hWU, ← hMK]
    exact isHallOdd_image hB inf_le_right hWMK
  obtain ⟨hpsl, hBle, hcard⟩ := hR2 (OTwoQuot (oTwoUpper H)) n hn2 hex _ _ _ _ hSyl hPar hHall hEq
  refine ⟨hpsl, fun b hb => ?_, ?_⟩
  · have hbK : b ∈ oTwoUpper H := hBK hb
    have h1 := (hBle (mem_imageOTwoQuot_iff.mpr ⟨b, hbK, hb, rfl⟩)).1
    have h2 := (mk_mem_perfectCore_iff hPK ⟨b, hbK⟩).mp h1
    rw [← hK1P] at h2
    have hWK1 : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.normalizer (K1 : Set G) := fun w hw => by
      rw [hK1P]
      exact normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer (hUP (hWU hw)))
    exact mem_of_mem_sup_pCoreOf hWK1 h2
      (hB.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard B hb))
  · rw [← card_image_of_odd hBK hB.2.1]
    exact hcard

end LieStep

end QA12

end CFSG.Quasithin
