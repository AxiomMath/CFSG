module

public import CFSG.RankThree.Coprime.HighTwoRankOddKernelLocal
public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
public import CFSG.RankThree.PartTwo.Setup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG
open CFSG.Assembly.RankThreeEven (localRank)

universe u v

theorem map_eq_map_pCore_of_le_ker_pPrimeCore {C : Type*} [Group C] [Finite C] {r : ℕ}
    [Fact r.Prime] {H : Type*} [Group H] (hC : Group.IsNilpotent C) (f : C →* H)
    (hf : CFSG.pPrimeCore r C ≤ f.ker) :
    (⊤ : Subgroup C).map f = (CFSG.pCore r C).map f := by
  refine le_antisymm ?_ (Subgroup.map_mono le_top)
  calc (⊤ : Subgroup C).map f ≤ (CFSG.pCore r C ⊔ CFSG.pPrimeCore r C).map f :=
        Subgroup.map_mono (CFSG.nilpotent_top_le_pCore_sup_pPrimeCore hC)
    _ = (CFSG.pCore r C).map f := by
        rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr hf, sup_bot_eq]

theorem map_top_le_normalizer_of_normal_isPGroup_two {G K : Type*} [Group G] [Group K]
    (R : Subgroup K) [R.Normal] (hR2 : IsPGroup 2 R) (hR0 : R ≠ ⊥)
    (ι : K →* G) (hι : Function.Injective ι) :
    (⊤ : Subgroup K).map ι ≤ Subgroup.normalizer ((R.map ι : Subgroup G) : Set G) := by
  rintro _ ⟨k, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨k * x * k⁻¹, (inferInstance : R.Normal).conj_mem x hx k,
      by simp [map_mul, map_inv]⟩
  · rintro ⟨x, hx, hxg⟩
    refine ⟨k⁻¹ * x * k, by
      simpa using (inferInstance : R.Normal).conj_mem x hx k⁻¹, ?_⟩
    have h := congrArg (fun y => (ι k)⁻¹ * y * ι k) hxg
    simp only [map_mul, map_inv] at h ⊢
    rw [h]
    group

theorem exists_surjective_map_comap {G : Type u} [Group G] (H : Subgroup G) {B : Type v}
    [Group B] (q : H →* B) (hq : Function.Surjective q) (M : Subgroup B) :
    ∃ (H₁ : Subgroup G) (π : H₁ →* M), H₁ ≤ H ∧ Function.Surjective π := by
  classical
  let H' : Subgroup H := M.comap q
  let H₁ : Subgroup G := H'.map H.subtype
  let e1 : H₁ ≃* H' := (H'.equivMapOfInjective H.subtype H.subtype_injective).symm
  let π : H₁ →* M := ((q.comp H'.subtype).codRestrict M (fun x => x.2)).comp e1.toMonoidHom
  refine ⟨H₁, π, Subgroup.map_subtype_le _, ?_⟩
  intro m
  obtain ⟨h, hh⟩ := hq (m : B)
  have hmem : h ∈ H' := by
    show q h ∈ M
    rw [hh]
    exact m.2
  refine ⟨e1.symm ⟨h, hmem⟩, ?_⟩
  apply Subtype.ext
  show (q.comp H'.subtype) (e1 (e1.symm ⟨h, hmem⟩)) = (m : B)
  rw [MulEquiv.apply_symm_apply]
  exact hh

private theorem exists_minimal_cover {G : Type u} [Group G] [Finite G] {M : Type v} [Group M]
    [Finite M] (hM : CFSG.layer M = ⊤) (H : Subgroup G) (π : H →* M)
    (hπ : Function.Surjective π) :
    ∃ (K : Subgroup H) (πK : K →* M) (C : Subgroup K), Group.IsPerfect K ∧
      Function.Surjective πK ∧ C.Normal ∧ C = (center M).comap πK ∧ Group.IsNilpotent C ∧
      (∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q C),
        ((Q : Subgroup C).map C.subtype).Normal) := by
  classical
  obtain ⟨K, -, hKmin⟩ := Finite.exists_le_minimal (p := fun K : Subgroup H => K.map π = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective π hπ])
  set πK : K →* M := π.comp K.subtype with hπK
  have hπKs : Function.Surjective πK := by
    intro x
    have hx : x ∈ K.map π := by rw [hKmin.prop]; exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin : ∀ Y : Subgroup K, Y ≠ ⊤ → Y.map πK ≠ ⊤ := by
    intro Y hY hYmap
    apply hY
    have h1 : (Y.map K.subtype).map π = ⊤ := by rw [Subgroup.map_map]; exact hYmap
    have h2 := hKmin.le_of_le h1 (Subgroup.map_subtype_le Y)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  obtain ⟨hKperf, hCn, hCnil, hCsyl, -, -, -, -, -⟩ := SectionRank.minimal_semisimple_cover
    hM πK hπKs hmin
  exact ⟨K, πK, (center M).comap πK, hKperf, hπKs, hCn, rfl, hCnil, hCsyl⟩

theorem isPGroup_map_quotient_pPrimeCore {K : Type*} [Group K] [Finite K] {r : ℕ}
    [hr : Fact r.Prime] (C : Subgroup K) [C.Normal] (hCnil : Group.IsNilpotent C) :
    IsPGroup r (C.map (QuotientGroup.mk' ((CFSG.pPrimeCore r C).map C.subtype))) := by
  classical
  let N : Subgroup C := CFSG.pPrimeCore r C
  let N' : Subgroup K := N.map C.subtype
  have hN'n : N'.Normal := by
    dsimp only [N', N]
    infer_instance
  haveI : N'.Normal := hN'n
  let f := (QuotientGroup.mk' N').comp C.subtype
  have hf : CFSG.pPrimeCore r C ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x, hx, rfl⟩
  have htop : C.map (QuotientGroup.mk' N') = (⊤ : Subgroup C).map f := by
    rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
  show IsPGroup r (C.map (QuotientGroup.mk' N'))
  rw [htop, map_eq_map_pCore_of_le_ker_pPrimeCore hCnil f hf]
  exact (CFSG.pCore_isPGroup (p := r) (G := C)).map f

private theorem exists_central_cover_of_nilpotent_kernel {K : Type u} {S : Type v} [Group K]
    [Finite K] [Group S] [Finite S] [Group.IsPerfect K] {m r : ℕ} [hr : Fact r.Prime]
    (hr2 : r ≠ 2) (π : K →* S) (hπ : Function.Surjective π) (C : Subgroup K) [C.Normal]
    (hCnil : Group.IsNilpotent C) (hCker : π.ker = C) (hsimple : IsSimpleGroup S)
    (he : ∀ N : Subgroup K, CFSG.Open.IsTwoLocal N → CFSG.Open.pRank r N ≤ m)
    (U : Subgroup S) (hU : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 2 ^ (m + 2)) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y) (_ : Group.IsPerfect Y) (φ : Y →* S),
      Function.Surjective φ ∧ φ.ker ≤ center Y ∧
        CFSG.Open.twoLocalPrimeRank r Y ≤ CFSG.Open.twoLocalPrimeRank r K ∧
        CFSG.pRank r Y = CFSG.pRank r K := by
  classical
  let N' : Subgroup K := (CFSG.pPrimeCore r C).map C.subtype
  haveI hN'n : N'.Normal := by
    dsimp only [N']
    infer_instance
  have hN'r : ¬ r ∣ Nat.card N' := by
    rw [show Nat.card N' = Nat.card (CFSG.pPrimeCore r C) from
      Subgroup.card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hr.out).mp
      (CFSG.pPrimeCore_coprime_card (p := r) (G := C))
  let φ : K ⧸ N' →* S :=
    QuotientGroup.lift N' π (by rw [hCker]; exact Subgroup.map_subtype_le (H := C) _)
  have hφs : Function.Surjective φ := by
    intro s
    obtain ⟨k, rfl⟩ := hπ s
    exact ⟨QuotientGroup.mk k, QuotientGroup.lift_mk' N' _ k⟩
  have hφker : φ.ker = C.map (QuotientGroup.mk' N') := by
    change (QuotientGroup.lift N' π _).ker = C.map (QuotientGroup.mk' N')
    rw [QuotientGroup.ker_lift, hCker]
  set R : Subgroup (K ⧸ N') := C.map (QuotientGroup.mk' N') with hR
  have hRp : IsPGroup r R := by simpa [hR] using isPGroup_map_quotient_pPrimeCore C hCnil
  have hRodd : Odd (Nat.card R) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk]
    exact (hr.out.odd_of_ne_two hr2).pow
  have hRsolv : Group.IsSolvable R := by
    have := hRp.isNilpotent
    infer_instance
  have hφR : φ.ker = R := hφker.trans hR.symm
  have hkerp : IsPGroup r φ.ker := by rw [hφR]; exact hRp
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφR]; exact hRodd
  have hkersolv : Group.IsSolvable φ.ker := by rw [hφR]; exact hRsolv
  let iso := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  obtain ⟨hU', hUcard'⟩ := isElementaryAbelian_map_mulEquiv iso.symm hU
  have hKrank : CFSG.Open.twoLocalPrimeRank r K ≤ m := by
    apply csSup_le'
    rintro k ⟨N₀, hN₀, rfl⟩
    exact he N₀ hN₀
  have hYlocal : CFSG.Open.twoLocalPrimeRank r (K ⧸ N') ≤
      CFSG.Open.twoLocalPrimeRank r K :=
    CFSG.RankThree.Classical2.localRank_quotient_le hr.out hr2 N' hN'r
  have heY : ∀ N₀ : Subgroup (K ⧸ N'), CFSG.Open.IsTwoLocal N₀ →
      CFSG.Open.pRank r N₀ ≤ m := fun N₀ hN₀ =>
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr.out N₀ hN₀).trans
      (hYlocal.trans hKrank)
  have hcenter : φ.ker ≤ center (K ⧸ N') :=
    le_center_of_high_two_rank_of_local (K := K ⧸ N') m hr2 heY φ.ker hkersolv hkerodd
      iso.isSimpleGroup (U.map iso.symm.toMonoidHom) hU' (hUcard'.trans hUcard) φ.ker hkerp
  exact ⟨K ⧸ N', inferInstance, inferInstance, inferInstance, φ, hφs, hcenter, hYlocal,
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr.out N' hN'r⟩

theorem exists_central_cover_of_twoLocalPrimeRank_le {G : Type u} [Group G] [Finite G] (m : ℕ)
    {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (he : CFSG.Open.twoLocalPrimeRank r G ≤ m)
    {S : Type*} [Group S] [Finite S] (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a)
    (hS : ∃ U : Subgroup S, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (m + 2))
    (H : Subgroup G) (π : H →* S) (hπ : Function.Surjective π) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y), Group.IsPerfect Y ∧
      ∃ φ : Y →* S, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center Y ∧
        CFSG.Open.twoLocalPrimeRank r Y ≤ m := by
  classical
  haveI := hSs
  obtain ⟨hSq, hSZ⟩ := LocalCores.isQuasisimple_of_isSimpleGroup hSnab
  obtain ⟨K, πK, C, hKperf, hπKs, hCn, hC, hCnil, -⟩ :=
    exists_minimal_cover (layer_eq_top_of_isQuasisimple hSq) H π hπ
  haveI : Group.IsPerfect K := hKperf
  haveI : C.Normal := hCn
  have hCker : πK.ker = C := by rw [hC, hSZ, MonoidHom.comap_bot]
  have hKG : CFSG.Open.twoLocalPrimeRank r K ≤ m := by
    refine (show CFSG.Open.twoLocalPrimeRank r K ≤ CFSG.Open.twoLocalPrimeRank r H from
      CFSG.RankThree.PartTwo.localRank_subgroup_le hr.out K).trans ?_
    exact (show CFSG.Open.twoLocalPrimeRank r H ≤ CFSG.Open.twoLocalPrimeRank r G from
      CFSG.RankThree.PartTwo.localRank_subgroup_le hr.out H).trans he
  have heK : ∀ N : Subgroup K, CFSG.Open.IsTwoLocal N → CFSG.Open.pRank r N ≤ m :=
    fun N hN =>
      (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr.out N hN).trans hKG
  obtain ⟨U, hU, hUcard⟩ := hS
  obtain ⟨Y, _, _, hYp, φ, hφs, hφZ, hYrank, -⟩ :=
    exists_central_cover_of_nilpotent_kernel hr2 πK hπKs C hCnil hCker inferInstance heK
      U hU hUcard
  exact ⟨Y, _, _, hYp, φ, hφs, hφZ, hYrank.trans hKG⟩

theorem exists_central_cover_of_even_center_of_twoLocalPrimeRank_le {G : Type u} [Group G]
    [Finite G] (m : ℕ) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (he : CFSG.Open.twoLocalPrimeRank r G ≤ m) {M : Type*} [Group M] [Finite M]
    (hM : IsQuasisimple M) (hZ : Even (Nat.card (center M)))
    (hS : ∃ U : Subgroup (M ⧸ center M), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (m + 2))
    (H : Subgroup G) (π : H →* M) (hπ : Function.Surjective π) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y) (_ : Group.IsPerfect Y)
      (φ : Y →* M ⧸ center M), Function.Surjective φ ∧ φ.ker ≤ center Y ∧
        CFSG.Open.pRank r (⊤ : Subgroup Y) ≤ m := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, πK, C, hKperf, hπKs, hCn, hC, hCnil, hCsyl⟩ :=
    exists_minimal_cover (layer_eq_top_of_isQuasisimple hM) H π hπ
  haveI : Group.IsPerfect K := hKperf
  haveI : C.Normal := hCn
  have hCZ : Function.Surjective ((πK.comp C.subtype).codRestrict (center M)
      (fun x => hC ▸ x.2)) := by
    intro z
    obtain ⟨k, hk⟩ := hπKs z
    exact ⟨⟨k, by rw [hC]; exact show πK k ∈ center M by rw [hk]; exact z.2⟩,
      Subtype.ext hk⟩
  have h2C : 2 ∣ Nat.card C :=
    (even_iff_two_dvd.mp hZ).trans (Subgroup.card_dvd_of_surjective hCZ)
  set T : Sylow 2 C := default with hT
  set R : Subgroup K := (T : Subgroup C).map C.subtype with hR
  haveI hRn : R.Normal := hCsyl 2 T
  have hRp : IsPGroup 2 R := T.isPGroup'.map _
  have hRne : R ≠ ⊥ := by
    rw [hR, Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
    exact T.ne_bot_of_dvd_card h2C
  set ι : K →* G := H.subtype.comp K.subtype with hι
  have hιinj : Function.Injective ι := H.subtype_injective.comp K.subtype_injective
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer ((R.map ι : Subgroup G) : Set G)) :=
    ⟨R.map ι, by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hιinj]; exact hRne, hRp.map ι, rfl⟩
  have hKrank : CFSG.pRank r K ≤ m := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    calc CFSG.Open.pRank r (⊤ : Subgroup K)
        ≤ CFSG.Open.pRank r ((⊤ : Subgroup K).map ι) :=
          CFSG.SectionRank.pRank_le_map hr.out.one_lt ι hιinj ⊤
      _ ≤ CFSG.Open.pRank r (Subgroup.normalizer ((R.map ι : Subgroup G) : Set G)) :=
          CFSG.SectionRank.pRank_mono hr.out.one_lt
            (map_top_le_normalizer_of_normal_isPGroup_two R hRp hRne ι hιinj)
      _ ≤ CFSG.Open.twoLocalPrimeRank r G :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr.out _ hloc
      _ ≤ m := he
  have heK : ∀ X : Subgroup K, CFSG.Open.IsTwoLocal X → CFSG.Open.pRank r X ≤ m := by
    intro X _
    calc CFSG.Open.pRank r X ≤ CFSG.Open.pRank r (⊤ : Subgroup K) :=
          CFSG.SectionRank.pRank_mono hr.out.one_lt le_top
      _ = CFSG.pRank r K := (CFSG.SectionRank.pRank_eq_open_pRank_top r K).symm
      _ ≤ m := hKrank
  let πS : K →* M ⧸ center M := (QuotientGroup.mk' (center M)).comp πK
  have hCker : πS.ker = C := by
    rw [hC, show πS = (QuotientGroup.mk' (center M)).comp πK from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hπSs : Function.Surjective πS :=
    (QuotientGroup.mk'_surjective (center M)).comp hπKs
  obtain ⟨U, hU, hUcard⟩ := hS
  obtain ⟨Y, _, _, hYp, φ, hφs, hφZ, -, hYrank⟩ :=
    exists_central_cover_of_nilpotent_kernel hr2 πS hπSs C hCnil hCker hM.2.1 heK
      U hU hUcard
  exact ⟨Y, _, _, hYp, φ, hφs, hφZ,
    (CFSG.SectionRank.pRank_eq_open_pRank_top r Y).symm.trans_le (hYrank.trans_le hKrank)⟩

end CFSG.RankThree.Coprime
