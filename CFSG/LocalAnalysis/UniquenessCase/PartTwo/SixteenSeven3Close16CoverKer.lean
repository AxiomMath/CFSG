module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uf
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416QAlt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem close16_le_center_of_isSolvable {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.rankThreeLayer (⊤ : Subgroup Q) = ⊤) {S : Subgroup Q} [hSn : S.Normal]
    (hS : Group.IsSolvable ↥S) : S ≤ Subgroup.center Q := by
  have h1 := (CFSG.LocalCores.component_solvable_centralizer hS hSn.isSubnormal).2
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_layer_eq_rankThreeLayer_top, hQ] at h1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  have h2 : (⊤ : Subgroup Q) ≤ centralizer (S : Set Q) := h1
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.1 (h2 (Subgroup.mem_top g)) x hx).symm

theorem close16_pCore_le_of_alt_quot {Q : Type} [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal]
    (e : Q ⧸ N ≃* alternatingGroup (Fin 8)) : CFSG.pCore 2 Q ≤ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (Q ⧸ N) := MulEquiv.isSimpleGroup e
  let π : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  haveI hPn : ((CFSG.pCore 2 Q).map π).Normal :=
    Subgroup.Normal.map inferInstance π hπ
  have hP2 : IsPGroup 2 ↥((CFSG.pCore 2 Q).map π) :=
    (CFSG.pCore_isPGroup).map π
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 Q).map π)) with h | h
  · intro x hx
    have : π x ∈ (CFSG.pCore 2 Q).map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · exfalso
    have hq2 : IsPGroup 2 (Q ⧸ N) := by
      rw [h] at hP2
      exact hP2.of_equiv Subgroup.topEquiv
    have hq2' : IsPGroup 2 (alternatingGroup (Fin 8)) := hq2.of_equiv e
    obtain ⟨n, hn⟩ := hq2'.exists_card_eq
    have hcard : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [hcard] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 20160)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem close16_card_ker_dvd_two {Q : Type} [Group Q] [Finite Q] (hQ : Group.IsPerfect Q)
    (q : Q →* alternatingGroup (Fin 8)) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center Q) : Nat.card q.ker ∣ 2 := by
  have : Group.IsPerfect Q := hQ
  have : Group.IsPerfect (alternatingGroup (Fin 8)) := Group.IsPerfect.ofSurjective hq
  obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_schur_multiplier q hq hker
  rw [← Nat.card_congr e'.toEquiv]
  refine (Subgroup.card_quotient_dvd_card _).trans ?_
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    CFSG.LocalAnalysis.GLTheoremA.griess_card_alt_eight]

theorem close16_le_pCore_of_alt_quot {Q : Type} [Group Q] [Finite Q] (hQ : Group.IsPerfect Q)
    (hL : CFSG.Open.rankThreeLayer (⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q)) = ⊤)
    (N : Subgroup Q) [N.Normal] (hN : Group.IsSolvable ↥N)
    (e : Q ⧸ N ≃* alternatingGroup (Fin 8)) : N ≤ CFSG.pCore 2 Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect Q := hQ
  set R := CFSG.pCore 2 Q with hR
  have hRN : R ≤ N := close16_pCore_le_of_alt_quot N e
  let π : Q →* Q ⧸ R := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  let f : Q →* alternatingGroup (Fin 8) := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hfR : ∀ x ∈ R, f x = 1 := by
    intro x hx
    have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr (hRN hx)
    simp only [f, MonoidHom.comp_apply, h1, map_one]
  let q : Q ⧸ R →* alternatingGroup (Fin 8) := QuotientGroup.lift R f hfR
  have hqπ : ∀ x : Q, q (π x) = f x := fun x => rfl
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x, hx⟩ := e.surjective a |>.imp fun y hy => hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact ⟨π x, by rw [hqπ]; exact hx⟩
  have hkerS : q.ker = N.map π := by
    ext y
    obtain ⟨x, rfl⟩ := hπ y
    rw [MonoidHom.mem_ker, hqπ, Subgroup.mem_map]
    constructor
    · intro hfx
      refine ⟨x, ?_, rfl⟩
      have : QuotientGroup.mk' N x = 1 := by
        apply e.injective
        simpa [f] using hfx
      exact (QuotientGroup.eq_one_iff x).mp this
    · rintro ⟨x', hx', hxx'⟩
      have hx'' : x'⁻¹ * x ∈ R := (QuotientGroup.eq).mp hxx'
      have hxN : x ∈ N := by
        have := N.mul_mem hx' (hRN hx'')
        simpa using this
      have : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hxN
      simp only [f, MonoidHom.comp_apply, this, map_one]
  have hSsolv : Group.IsSolvable ↥q.ker := by
    rw [hkerS]
    exact Group.isSolvable_of_surjective (f := π.subgroupMap N)
      (MonoidHom.subgroupMap_surjective π N)
  haveI : q.ker.Normal := MonoidHom.normal_ker q
  have hSc : q.ker ≤ Subgroup.center (Q ⧸ R) := close16_le_center_of_isSolvable hL hSsolv
  have hQb : Group.IsPerfect (Q ⧸ R) := Group.IsPerfect.ofSurjective hπ
  have hdvd := close16_card_ker_dvd_two hQb q hq hSc
  have hS2 : IsPGroup 2 ↥q.ker := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 1)).mp (by simpa using hdvd)
    exact IsPGroup.of_card (n := k) hk'
  have hSle : q.ker ≤ CFSG.pCore 2 (Q ⧸ R) := le_sSup ⟨inferInstance, hS2⟩
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hSle
  intro x hx
  have hmem : π x ∈ q.ker := by rw [hkerS]; exact Subgroup.mem_map_of_mem π hx
  have h1 : π x = 1 := by simpa using hSle hmem
  exact (QuotientGroup.eq_one_iff x).mp h1

private theorem close16_layer_top_of_O2E_eq {Y : Subgroup G} (hYE : F11.O2E Y = Y) :
    CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ := by
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) :=
    QuotientGroup.mk'_surjective _
  have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hcomap : (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    change F11.O2E Y = (⊤ : Subgroup ↥Y).map Y.subtype
    rw [hYE, hTop]
  have h := Subgroup.map_comap_eq_self_of_surjective hπ
    (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)))
  rw [hcomap, Subgroup.map_top_of_surjective _ hπ] at h
  exact h.symm

theorem close16_ker_eq_pcore {Y C : Subgroup G} [((Y ⊓ C).subgroupOf Y).Normal]
    (hperf : ⁅Y, Y⁆ = Y) (hlayer : F11.O2E Y = Y) (hsolv : Y ⊓ C ≤ OInf Y)
    (hA8 : IsAlt (↥Y ⧸ (Y ⊓ C).subgroupOf Y) 8) : Y ⊓ C = pCoreOf 2 Y := by
  have hP : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hL := close16_layer_top_of_O2E_eq hlayer
  have hN : Group.IsSolvable ↥((Y ⊓ C).subgroupOf Y) := by
    have hle : (Y ⊓ C).subgroupOf Y ≤ CFSG.solvableRadical ↥Y := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hsolv (Subgroup.mem_subgroupOf.mp hx)
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
    haveI := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := ↥Y)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  obtain ⟨e⟩ := hA8
  have h1 := close16_pCore_le_of_alt_quot ((Y ⊓ C).subgroupOf Y) e
  have h2 := close16_le_pCore_of_alt_quot hP hL ((Y ⊓ C).subgroupOf Y) hN e
  have heq : (Y ⊓ C).subgroupOf Y = CFSG.pCore 2 ↥Y := le_antisymm h2 h1
  unfold pCoreOf
  rw [← heq, Subgroup.map_subgroupOf_eq_of_le inf_le_left]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
