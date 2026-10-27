module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Subnormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
import TauCeti.Algebra.Group.Subgroup.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

open Subgroup

variable {G : Type} [Group G]

private noncomputable def barImageHom {L K : Subgroup G} {J : Subgroup (Bar2 L)} (hKL : K ≤ L)
    (hJ : barImage L K = J) : ↥K →* ↥J :=
  MonoidHom.codRestrict
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hKL)) J
    (fun x => by
      have hx : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (Subgroup.inclusion hKL x) ∈
          barImage L K := by
        rw [barImage]
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKL x, by
          rw [Subgroup.mem_subgroupOf]
          exact x.2, rfl⟩
      simpa [hJ] using hx)

private theorem barImageHom_surjective {L K : Subgroup G} {J : Subgroup (Bar2 L)} (hKL : K ≤ L)
    (hJ : barImage L K = J) : Function.Surjective (barImageHom hKL hJ) := by
  intro y
  have hy : (y : Bar2 L) ∈ barImage L K := by simpa [hJ] using y.2
  obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hy
  have hxK : x.1 ∈ K := by
    rw [Subgroup.mem_subgroupOf] at hx
    exact hx
  refine ⟨⟨x.1, hxK⟩, ?_⟩
  apply Subtype.ext
  change (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (Subgroup.inclusion hKL ⟨x.1, hxK⟩) = (y : Bar2 L)
  have hincl : Subgroup.inclusion hKL ⟨x.1, hxK⟩ = x := Subtype.ext rfl
  rw [hincl, hxval]

private theorem not_isPGroup_two_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ¬ IsPGroup 2 Q := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial Q := nontrivial_of_isQuasisimple hQ
  haveI : Group.IsPerfect Q := Group.isPerfect_def.mpr hQ.1
  exact Group.IsPerfect.not_isNilpotent Q h2.isNilpotent

private theorem commutator_eq_bot_of_le_center_subgroupOf {X : Type*} [Group X]
    {N H : Subgroup X} [N.Normal] [H.Normal] (hNH : N ≤ H)
    (h : N.subgroupOf H ≤ Subgroup.center ↥H) : ⁅N, H⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
  intro y hy
  have hxH : x ∈ H := hNH hx
  have hxc : (⟨x, hxH⟩ : ↥H) ∈ Subgroup.center ↥H :=
    h (Subgroup.mem_subgroupOf.mpr hx)
  have hcomm : (⟨y, hy⟩ : ↥H) * ⟨x, hxH⟩ = ⟨x, hxH⟩ * ⟨y, hy⟩ :=
    Subgroup.mem_center_iff.mp hxc ⟨y, hy⟩
  exact Commute.commutator_eq (Subtype.ext_iff.mp hcomm).symm

private theorem commutator_eq_bot_of_normal_twoGroup {X : Type*} [Group X] [Finite X]
    {N K : Subgroup X} [N.Normal] [K.Normal] (hN : IsPGroup 2 N)
    (hK : CFSG.Open.IsQuasisimple ↥K) : ⁅N, K⁆ = ⊥ := by
  haveI hMnormal : (N.subgroupOf K).Normal :=
    show (N.comap K.subtype).Normal from (inferInstance : N.Normal).comap K.subtype
  have hM2 : IsPGroup 2 (N.subgroupOf K) := hN.comap_subtype
  have hMK : N.subgroupOf K ≤ Subgroup.center ↥K := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hK) (N.subgroupOf K) with hle | htop
    · exact hle
    · exfalso
      have hKN : K ≤ N := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥K) ∈ N.subgroupOf K := by
          rw [htop]
          exact Subgroup.mem_top _
        rw [Subgroup.mem_subgroupOf] at hx'
        exact hx'
      exact not_isPGroup_two_of_isQuasisimple hK (hN.to_le hKN)
  have hA : ⁅⁅N, K⁆, K⁆ = ⊥ := by
    have hAint : ⁅N, K⁆ ≤ K := Subgroup.commutator_le_right (H₁ := N) (H₂ := K)
    have hAsub : (⁅N, K⁆).subgroupOf K ≤ N.subgroupOf K :=
      Subgroup.subgroupOf_mono K (Subgroup.commutator_le_left (H₁ := N) (H₂ := K))
    exact commutator_eq_bot_of_le_center_subgroupOf hAint (hAsub.trans hMK)
  have hKN : ⁅K, N⁆ = ⊥ := by
    refine CFSG.LocalCores.perfect_double_commutator ?_ ?_
    · exact Group.isPerfect_def.mpr hK.1
    · simpa only [Subgroup.commutator_comm N K] using hA
  rwa [Subgroup.commutator_comm N K]

private theorem center_quotient_center_eq_bot_of_isSimpleGroup {X : Type*} [Group X]
    [IsSimpleGroup X] : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  by_cases hc : IsMulCommutative X
  · haveI : IsMulCommutative X := hc
    have htop : Subgroup.center X = ⊤ := Subgroup.center_eq_top
    haveI : Subsingleton (X ⧸ Subgroup.center X) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx1 : x = 1 := Subsingleton.elim x 1
    simpa [hx1]
  · haveI : Group.IsPerfect X := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hc
    exact Group.IsPerfect.center_quotient_center_eq_bot X

private theorem exists_surjective_quotient_center_of_barImage_eq [Finite G]
    {L K : Subgroup G} {J : Subgroup (Bar2 L)} (hKL : K ≤ L) (hJ : barImage L K = J)
    (hJq : CFSG.Open.IsQuasisimple ↥J ∨ IsSimpleGroup ↥J) :
    ∃ ψ : Bar2 K →* ↥J ⧸ Subgroup.center ↥J, Function.Surjective ψ := by
  let κ := barImageHom hKL hJ
  have hκ : Function.Surjective κ := barImageHom_surjective hKL hJ
  let π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let ρ : ↥K →* ↥J ⧸ Subgroup.center ↥J := π.comp κ
  have hρ : Function.Surjective ρ := hπ.comp hκ
  let P : Subgroup ↥K := CFSG.pCore 2 ↥K
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup (p := 2) (G := ↥K)
  have hQnormal : (P.map κ).Normal :=
    (CFSG.pCore_normal (p := 2) (G := ↥K)).map κ hκ
  have hQ2 : IsPGroup 2 (P.map κ) := hP2.map κ
  haveI : (P.map κ).Normal := hQnormal
  have hQcenter : P.map κ ≤ Subgroup.center ↥J := by
    rcases hJq with hq | hs
    · rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple
          (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq) (P.map κ) with h | h
      · exact h
      · have hJ2 : IsPGroup 2 ↥J := by
          have htop : IsPGroup 2 (⊤ : Subgroup ↥J) := by
            rw [← h]
            exact hQ2
          exact IsPGroup.of_equiv htop Subgroup.topEquiv
        exact absurd hJ2 (not_isPGroup_two_of_isQuasisimple hq)
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map κ) with h | h
      · rw [h]
        exact bot_le
      · have hJ2 : IsPGroup 2 ↥J := by
          have htop : IsPGroup 2 (⊤ : Subgroup ↥J) := by
            rw [← h]
            exact hQ2
          exact IsPGroup.of_equiv htop Subgroup.topEquiv
        have hne : Subgroup.center ↥J ≠ ⊥ := by
          intro hbot
          haveI : Nontrivial (Subgroup.center ↥J) := hJ2.center_nontrivial
          obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (Subgroup.center ↥J))
          have ha : (a : ↥J) = 1 := by simpa [hbot] using a.2
          have hb : (b : ↥J) = 1 := by simpa [hbot] using b.2
          exact hab (Subtype.ext (ha.trans hb.symm))
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with hZ | hZ
        · exact absurd hZ hne
        · rw [hZ]
          exact le_top
  have hPker : P ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (κ x)).mpr (hQcenter ⟨x, hx, rfl⟩)
  refine ⟨QuotientGroup.lift P ρ hPker, ?_⟩
  exact QuotientGroup.lift_surjective_of_surjective P ρ hρ hPker

theorem exists_surjective_single [Finite G] {L K : Subgroup G} (hK : K ∈ calC L)
    (hX : IsSimpleGroup (Bar2 L) ∨ CFSG.Open.IsQuasisimple (Bar2 L)) :
    (∃ ψ : Bar2 K →* Bar2 L ⧸ center (Bar2 L), Function.Surjective ψ) ∧
      center (Bar2 L ⧸ center (Bar2 L)) = ⊥ := by
  have hπsub : CFSG.Open.IsSubnormal (barImage L K) ⊤ := isSubnormal_barImage hK.1
  have hπperf : ⁅barImage L K, barImage L K⁆ = barImage L K :=
    commutator_barImage hK.1.le hK.2.1
  have hπne : barImage L K ≠ ⊥ := barImage_ne_bot hK
  have htop : barImage L K = ⊤ := by
    rcases le_center_or_eq_top_of_isSubnormal hX hπsub with hle | htop
    · exact absurd (eq_bot_of_le_center hle hπperf) hπne
    · exact htop
  have hJq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup (Bar2 L)) ∨
      IsSimpleGroup ↥(⊤ : Subgroup (Bar2 L)) := by
    rcases hX with hs | hq
    · exact Or.inr (by haveI := hs; exact MulEquiv.isSimpleGroup Subgroup.topEquiv)
    · exact Or.inl (CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hq)
  obtain ⟨ψ, hψ⟩ := exists_surjective_quotient_center_of_barImage_eq hK.1.le htop hJq
  let e : (↥(⊤ : Subgroup (Bar2 L)) ⧸ Subgroup.center ↥(⊤ : Subgroup (Bar2 L))) ≃*
      Bar2 L ⧸ Subgroup.center (Bar2 L) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)
  refine ⟨⟨e.toMonoidHom.comp ψ, ?_⟩, ?_⟩
  · exact e.surjective.comp hψ
  · rcases hX with hs | hq
    · haveI := hs
      exact center_quotient_center_eq_bot_of_isSimpleGroup
    · exact center_quotient_center_eq_bot hq

theorem exists_surjective_sup [Finite G] {L K : Subgroup G} (hK : K ∈ calC L)
    {K₁ K₂ : Subgroup (Bar2 L)} (hsup : K₁ ⊔ K₂ = ⊤) (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (h₁ : CFSG.Open.IsQuasisimple ↥K₁) (h₂ : CFSG.Open.IsQuasisimple ↥K₂) :
    ∃ K' ∈ ({K₁, K₂} : Set (Subgroup (Bar2 L))),
      ∃ ψ : Bar2 K →* ↥K' ⧸ center ↥K', Function.Surjective ψ := by
  have hK₁perf : ⁅K₁, K₁⁆ = K₁ := by
    haveI : Group.IsPerfect ↥K₁ := Group.isPerfect_def.mpr h₁.1
    exact Subgroup.isPerfect_iff.mp inferInstance
  have hK₂perf : ⁅K₂, K₂⁆ = K₂ := by
    haveI : Group.IsPerfect ↥K₂ := Group.isPerfect_def.mpr h₂.1
    exact Subgroup.isPerfect_iff.mp inferInstance
  have hπsub : CFSG.Open.IsSubnormal (barImage L K) ⊤ := isSubnormal_barImage hK.1
  have hπperf : ⁅barImage L K, barImage L K⁆ = barImage L K :=
    commutator_barImage hK.1.le hK.2.1
  have hπne : barImage L K ≠ ⊥ := barImage_ne_bot hK
  rcases eq_or_eq_or_eq_top_of_sup hsup hcomm h₁ h₂ hπsub hπperf hπne with h | h | htop
  · obtain ⟨ψ, hψ⟩ :=
      exists_surjective_quotient_center_of_barImage_eq hK.1.le h (Or.inl h₁)
    exact ⟨K₁, by simp, ψ, hψ⟩
  · obtain ⟨ψ, hψ⟩ :=
      exists_surjective_quotient_center_of_barImage_eq hK.1.le h (Or.inl h₂)
    exact ⟨K₂, by simp, ψ, hψ⟩
  · exfalso
    have hK₁normal : K₁.Normal :=
      TauCeti.normal_of_commute_of_sup_eq_top (fun a ha b hb => hcomm a ha b hb) hsup
    have hK₂normal : K₂.Normal :=
      TauCeti.normal_of_commute_of_sup_eq_top
        (fun a ha b hb => (hcomm b hb a ha).symm) (by rw [sup_comm]; exact hsup)
    haveI : K₁.Normal := hK₁normal
    haveI : K₂.Normal := hK₂normal
    let κ : ↥K →* Bar2 L :=
      Subgroup.topEquiv.toMonoidHom.comp (barImageHom hK.1.le htop)
    have hκ : Function.Surjective κ :=
      Subgroup.topEquiv.surjective.comp (barImageHom_surjective hK.1.le htop)
    let P : Subgroup ↥K := CFSG.pCore 2 ↥K
    let N : Subgroup (Bar2 L) := P.map κ
    have hNnormal : N.Normal := (CFSG.pCore_normal (p := 2) (G := ↥K)).map κ hκ
    haveI : N.Normal := hNnormal
    have hN2 : IsPGroup 2 N := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map κ
    let q : Bar2 L →* Bar2 L ⧸ N := QuotientGroup.mk' N
    let ρ : ↥K →* Bar2 L ⧸ N := q.comp κ
    have hρ : Function.Surjective ρ := (QuotientGroup.mk'_surjective N).comp hκ
    have hPker : P ≤ ρ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (κ x)).mpr ⟨x, hx, rfl⟩
    let ρbar : Bar2 K →* Bar2 L ⧸ N := QuotientGroup.lift P ρ hPker
    have hρbar : Function.Surjective ρbar :=
      QuotientGroup.lift_surjective_of_surjective P ρ hρ hPker
    have hNK₁ : ⁅N, K₁⁆ = ⊥ := commutator_eq_bot_of_normal_twoGroup hN2 h₁
    have hNK₂ : ⁅N, K₂⁆ = ⊥ := commutator_eq_bot_of_normal_twoGroup hN2 h₂
    have hNcenter : N ≤ Subgroup.center (Bar2 L) := by
      rw [← Subgroup.commutator_top_left_eq_bot_iff_le_center, Subgroup.commutator_comm,
        ← hsup, Subgroup.commutator_sup_left N K₁ K₂, hNK₁, hNK₂, sup_bot_eq]
    let P₁ : Subgroup (Bar2 L ⧸ N) := K₁.map q
    have hP₁normal : P₁.Normal := hK₁normal.map q (QuotientGroup.mk'_surjective N)
    let M : Subgroup (Bar2 K) := P₁.comap ρbar
    have hMnormal : M.Normal := hP₁normal.comap ρbar
    haveI : M.Normal := hMnormal
    have hP₁map : M.map ρbar = P₁ := by
      rw [Subgroup.map_comap_eq (f := ρbar) (H := P₁),
        MonoidHom.range_eq_top.mpr hρbar]
      simp
    have hMq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hMq) M with hMcenter | hMtop
    · have hP₁center : P₁ ≤ Subgroup.center (Bar2 L ⧸ N) := by
        rw [← hP₁map]
        exact (Subgroup.map_mono hMcenter).trans (Subgroup.map_center_le_center hρbar)
      have hK₁N : K₁ ≤ N := by
        have hmapcomm : ⁅K₁, K₁⁆.map q = ⊥ := by
          rw [Subgroup.map_commutator]
          change ⁅P₁, P₁⁆ = ⊥
          exact le_antisymm ((Subgroup.commutator_mono_right hP₁center).trans
            (le_of_eq (Subgroup.commutator_center_right P₁))) bot_le
        have hcommK : ⁅K₁, K₁⁆ ≤ N := by
          rw [← QuotientGroup.ker_mk' N]
          exact (Subgroup.map_eq_bot_iff (f := q) ⁅K₁, K₁⁆).mp hmapcomm
        rwa [hK₁perf] at hcommK
      exact absurd (hN2.to_le hK₁N) (not_isPGroup_two_of_isQuasisimple h₁)
    · have hP₁top : P₁ = ⊤ := by
        rw [← hP₁map, hMtop, Subgroup.map_top_of_surjective ρbar hρbar]
      have hK₁Ntop : K₁ ⊔ N = ⊤ := by
        have h := QuotientGroup.comap_map_mk' N K₁
        change Subgroup.comap q P₁ = N ⊔ K₁ at h
        rw [hP₁top, Subgroup.comap_top] at h
        simpa [sup_comm] using h.symm
      have hK₂le_sup : K₂ ≤ K₁ ⊔ N := by
        rw [hK₁Ntop]
        exact le_top
      have hK₁Nbot : ⁅K₁, N⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hNK₁
      have hNNbot : ⁅N, N⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
          (hNcenter.trans (Subgroup.center_le_centralizer (N : Set (Bar2 L))))
      have hcommKN : ⁅K₁ ⊔ N, K₁ ⊔ N⁆ = K₁ := by
        rw [Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
          Subgroup.commutator_sup_left, hK₁perf, hK₁Nbot, hNK₁, hNNbot]
        simp
      have hK₂le : K₂ ≤ K₁ := by
        calc K₂ = ⁅K₂, K₂⁆ := hK₂perf.symm
          _ ≤ ⁅K₁ ⊔ N, K₁ ⊔ N⁆ :=
              Subgroup.commutator_mono hK₂le_sup hK₂le_sup
          _ = K₁ := hcommKN
      have hK₂bot : K₂ = ⊥ := by
        have hcomm₁₂ : ⁅K₁, K₂⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro a ha
          rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
          intro b hb
          exact Commute.commutator_eq (hcomm a ha b hb)
        have hle : K₂ ≤ ⊥ := by
          calc K₂ = ⁅K₂, K₂⁆ := hK₂perf.symm
            _ ≤ ⁅K₁, K₂⁆ := Subgroup.commutator_mono hK₂le le_rfl
            _ = ⊥ := hcomm₁₂
        exact le_antisymm hle bot_le
      obtain ⟨a, b, hab⟩ := (nontrivial_of_isQuasisimple h₂).exists_pair_ne
      haveI : Subsingleton ↥K₂ := by
        rw [hK₂bot]
        infer_instance
      exact hab (Subsingleton.elim a b)

end CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
