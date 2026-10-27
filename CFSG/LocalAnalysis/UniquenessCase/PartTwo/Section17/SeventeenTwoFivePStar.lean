module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwoFiveSevenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOneSevenNarrow
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxM
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoBender

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_normal_isSolvable_alt5_prod
    {N : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))} [N.Normal]
    (hN : Group.IsSolvable ↥N) : N = ⊥ := by
  classical
  haveI : Group.IsSolvable ↥N := hN
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hAnot : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) :=
    CFSG.Quasithin.H13.CTK.not_isSolvable_alt5
  let p1 : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* alternatingGroup (Fin 5) :=
    MonoidHom.fst _ _
  let p2 : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* alternatingGroup (Fin 5) :=
    MonoidHom.snd _ _
  have hsurj1 : Function.Surjective p1 := fun y => ⟨(y, 1), rfl⟩
  have hsurj2 : Function.Surjective p2 := fun y => ⟨(1, y), rfl⟩
  have hN1 : N ⊓ p1.ker = ⊥ := by
    by_contra hne
    haveI hN1n : (N ⊓ p1.ker).Normal := inferInstance
    haveI hN1solv : Group.IsSolvable ↥(N ⊓ p1.ker) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ p1.ker ≤ N)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe _).surjective
    haveI hmapn : ((N ⊓ p1.ker).map p2).Normal := hN1n.map p2 hsurj2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ p1.ker).map p2) with h | h
    · exfalso
      apply hne
      refine le_antisymm ?_ bot_le
      intro x hx
      have hx2 : p2 x = 1 := by
        have hmem : p2 x ∈ (N ⊓ p1.ker).map p2 := Subgroup.mem_map_of_mem _ hx
        rw [h] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hx1 : p1 x = 1 := hx.2
      have hxeq : x = 1 := by
        rcases x with ⟨a, b⟩
        exact Prod.ext (show a = 1 from hx1) (show b = 1 from hx2)
      rw [hxeq]
      exact Subgroup.one_mem _
    · exfalso
      have hsurj : Function.Surjective (p2.comp (N ⊓ p1.ker).subtype) := by
        intro y
        have hy : y ∈ (N ⊓ p1.ker).map p2 := by rw [h]; exact Subgroup.mem_top y
        obtain ⟨x, hx, hxy⟩ := hy
        exact ⟨⟨x, hx⟩, hxy⟩
      exact hAnot (Group.isSolvable_of_surjective
        (f := p2.comp (N ⊓ p1.ker).subtype) hsurj)
  have hinjN : ∀ x ∈ N, p1 x = 1 → x = 1 := by
    intro x hx h1
    have hx1 : x ∈ p1.ker := h1
    have hmem : x ∈ N ⊓ p1.ker := ⟨hx, hx1⟩
    rw [hN1] at hmem
    exact Subgroup.mem_bot.mp hmem
  haveI : (N.map p1).Normal := (inferInstance : N.Normal).map p1 hsurj1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map p1) with h | h
  · refine le_antisymm ?_ bot_le
    intro x hx
    have h1 : p1 x = 1 := by
      have hmem : p1 x ∈ N.map p1 := Subgroup.mem_map_of_mem _ hx
      rw [h] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [hinjN x hx h1]
    exact Subgroup.one_mem _
  · exfalso
    have hsurj : Function.Surjective (p1.comp N.subtype) := by
      intro y
      have hy : y ∈ N.map p1 := by rw [h]; exact Subgroup.mem_top y
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, hxy⟩
    exact hAnot (Group.isSolvable_of_surjective (f := p1.comp N.subtype) hsurj)


theorem cyclic_sylow_of_r7_8 (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h2 : R17_2_2At D V₀ V hV) (h3 : R17_2_3At D V₀ V hV) (h78 : R7_8At5 D)
    (hM5 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M)
    (h72 : F07.R72 D) (h72u : R72UnitaryFiveOne D)
    {D' Y : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hD'M : D' ≤ D.M) (hD'5 : IsPGroup 5 ↥D') (hD'nc : ¬ IsCyclic ↥D')
    (hD'exp : ∀ x ∈ D', x ^ 5 = 1) (hD'class : ⁅⁅D', D'⁆, D'⁆ = ⊥)
    (hnormal' : ((D' ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hYq : IsPGroup q ↥Y) (hYM : Y ≤ D.M) (hYne : Y ≠ ⊥)
    (hD'Y : D' ≤ Subgroup.centralizer (Y : Set G))
    (hH : ¬ Subgroup.normalizer (Y : Set G) ≤ D.M) :
    ∃ S : Subgroup G,
        CFSG.ABGLocalTools.IsSylowOf 2 S (Subgroup.normalizer (Y : Set G) ⊓ D.M) ∧
          IsCyclic ↥S := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fact q.Prime := ⟨hq⟩
  let H : Subgroup G := Subgroup.normalizer (Y : Set G)
  have hD'H : D' ≤ H := hD'Y.trans (Subgroup.centralizer_le_normalizer (Y : Set G))
  have hD'le : D' ≤ H ⊓ D.M := le_inf hD'H hD'M
  obtain ⟨hD'card, -, -, -⟩ :=
    h2 5 D' (by norm_num) (by norm_num) hD'M hD'5 hD'nc hD'exp hD'class hnormal'
  have hD'ne : D' ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥D' = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hD'card] at h1
    norm_num at h1
  have hHtop : H ≠ ⊤ := by
    intro htop
    have htop' : Subgroup.normalizer (Y : Set G) = ⊤ := htop
    have hYnormal : Y.Normal := Subgroup.normalizer_eq_top_iff.mp htop'
    rcases D.standing.simple.eq_bot_or_eq_top_of_normal Y with hYbot | hYtop
    · exact hYne hYbot
    · have hGq : IsPGroup q (⊤ : Subgroup G) := by
        rw [← hYtop]
        exact hYq
      have hGq' : IsPGroup q G := hGq.of_equiv Subgroup.topEquiv
      haveI : Group.IsNilpotent G := hGq'.isNilpotent
      haveI : IsSimpleGroup G := D.standing.simple
      obtain ⟨a, b, hab⟩ := D.standing.nonab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b)
  have hD'comm : IsMulCommutative ↥D' :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) hD'card
  have hD'el : IsElemAbelian 5 D' := ⟨hD'comm, hD'exp⟩
  have hrank : 1 < CFSG.Open.pRank 5 (H ⊓ D.M) := by
    have h2le : 2 ≤ CFSG.Open.pRank 5 (H ⊓ D.M) :=
      CFSG.SectionRank.le_pRank (by norm_num : 1 < 5) hD'le hD'el hD'card
    omega
  have hSec : Sec7Hyp D 5 H := ⟨by norm_num, by norm_num, hM5, hHtop, hH, hrank⟩
  obtain ⟨P, hPsyl, hD'P⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge (p := 5) hD'le hD'5
  let D₀ : Subgroup G := CFSG.RankThree.PartOne.omegaOne 5 P
  have halt := h78 H P D₀ hSec hPsyl rfl
  have hnotIrr : ¬ IrrOn (D.M ⊓ Subgroup.normalizer (D' : Set G)) D' :=
    (h3 5 D' (by norm_num) (by norm_num) hD'M hD'5 hD'nc hD'exp hD'class hnormal').1
  rcases halt with halt1 | halt2 | hA5
  ·
    rcases halt1 with ⟨hirr, hPD₀⟩
    exfalso
    have hPD' : P = D' := eq_of_r7_8_one D h72 h72u hSec hPsyl hD'P hD'nc hnormal'
      (by rwa [← hPD₀] at hirr)
    have hD₀D' : D₀ = D' := hPD₀.symm.trans hPD'
    haveI : Fact (IsPGroup 5 ↥D') := ⟨hD'5⟩
    haveI : IsElementaryAbelian 5 ↥D' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 5 D').2 hD'el
    have hΦ : CFSG.inSubgroup frattini D' = ⊥ := by
      simp [CFSG.inSubgroup, CFSG.frattini_eq_bot_of_isElementaryAbelian (p := 5)]
    let N : Subgroup G := H ⊓ Subgroup.normalizer (P : Set G)
    have hirr' : IrrOnMod N D' ⊥ := by
      simpa [N, hD₀D', hΦ] using hirr
    have hirrOn : IrrOn N D' := by
      intro W hW hNW
      exact hirr' W bot_le hW hNW
    have hN_le : N ≤ D.M ⊓ Subgroup.normalizer (D' : Set G) := by
      have hPne : P ≠ ⊥ := by
        rw [hPD']
        exact hD'ne
      have hNM : N ≤ D.M := inf_le_right.trans
        (hM5.normalizer_le hPne hPsyl.isPGroup (hPsyl.le.trans inf_le_right))
      have hNP' : N ≤ Subgroup.normalizer (D' : Set G) := by
        rw [← hPD']
        exact inf_le_right
      exact le_inf hNM hNP'
    have hIrrM : IrrOn (D.M ⊓ Subgroup.normalizer (D' : Set G)) D' :=
      fun W hW hNW => hirrOn W hW (hN_le.trans hNW)
    exact hnotIrr hIrrM
  ·
    rcases halt2 with ⟨S, hSsyl, hScyc⟩
    exact ⟨S, hSsyl, hScyc⟩
  ·
    exfalso
    let K : Subgroup G := Opp 5 (H ⊓ D.M)
    have hA5K : IsA5xA5 ↥K := hA5
    obtain ⟨e⟩ := hA5K
    have hKle : K ≤ H ⊓ D.M := by
      intro x hx
      change x ∈ Subgroup.closure
        {y : G | y ∈ H ⊓ D.M ∧ ∃ k : ℕ, orderOf y = 5 ^ k} at hx
      exact (Subgroup.closure_le (H ⊓ D.M)).2 (fun y hy => hy.1) hx
    have hKM : K ≤ D.M := hKle.trans inf_le_right
    have hD'K : D' ≤ K := by
      intro d hd
      have hdX : d ∈ H ⊓ D.M := ⟨hD'H hd, hD'M hd⟩
      have hd5 : ∃ k : ℕ, orderOf d = 5 ^ k := by
        obtain ⟨k, hk⟩ := hD'5 ⟨d, hd⟩
        have hk' : d ^ (5 ^ k) = 1 := congrArg Subtype.val hk
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).1
          (orderOf_dvd_of_pow_eq_one hk')
        exact ⟨j, hj⟩
      change d ∈ Subgroup.closure
        {y : G | y ∈ H ⊓ D.M ∧ ∃ k : ℕ, orderOf y = 5 ^ k}
      exact Subgroup.subset_closure ⟨hdX, hd5⟩
    let Dk : Subgroup ↥K := D'.subgroupOf K
    let M₀ : Subgroup G := D' ⊔ CFSG.Open.pCoreOf 2 D.M
    have hM₀M : M₀ ≤ D.M :=
      sup_le hD'M (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
    have hM₀normM : (M₀.subgroupOf D.M).Normal := hnormal'
    have hM₀normM' : D.M ≤ Subgroup.normalizer (M₀ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hM₀M).1 hM₀normM
    have hK_normM₀ : K ≤ Subgroup.normalizer (M₀ : Set G) :=
      hKM.trans hM₀normM'
    have hM₀normK : (M₀.subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
      exact (le_inf hK_normM₀ Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hDk_le : Dk ≤ M₀.subgroupOf K := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
    let Nk : Subgroup ↥K := Subgroup.normalClosure (Dk : Set ↥K)
    haveI hNkN : Nk.Normal := Subgroup.normalClosure_normal
    have hDkNk : Dk ≤ Nk := Subgroup.le_normalClosure
    have hNk_le : Nk ≤ M₀.subgroupOf K :=
      Subgroup.normalClosure_le_normal (N := M₀.subgroupOf K) hDk_le
    have hOsolv : Group.IsSolvable ↥(CFSG.Open.pCoreOf 2 D.M) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 D.M) :=
        CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
      haveI : Group.IsNilpotent ↥(CFSG.Open.pCoreOf 2 D.M) := hO2.isNilpotent
      infer_instance
    have hD'solv : Group.IsSolvable ↥D' := by
      haveI : Group.IsNilpotent ↥D' := hD'5.isNilpotent
      infer_instance
    have hD'O_norm : D' ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 D.M : Set G) :=
      hD'M.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    have hM₀solv : Group.IsSolvable ↥M₀ :=
      CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210.isSolvable_sup_of_le_normalizer
        (T := CFSG.Open.pCoreOf 2 D.M) (D := D') hD'O_norm hOsolv hD'solv
    have hM₀K_solv : Group.IsSolvable ↥(M₀.subgroupOf K) := by
      haveI : Group.IsSolvable ↥M₀ := hM₀solv
      let φ : ↥(M₀.subgroupOf K) →* ↥M₀ :=
        { toFun := fun x => ⟨K.subtype x.1, Subgroup.mem_subgroupOf.mp x.2⟩
          map_one' := by ext; simp
          map_mul' := fun a b => by ext; simp }
      exact Group.isSolvable_of_isSolvable_injective (f := φ) (by
        intro a b hab
        have hval := congrArg Subtype.val hab
        change K.subtype a.1 = K.subtype b.1 at hval
        exact Subtype.ext (K.subtype_injective hval))
    have hNksolv : Group.IsSolvable ↥Nk := by
      haveI : Group.IsSolvable ↥(M₀.subgroupOf K) := hM₀K_solv
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNk_le)
        (Subgroup.inclusion_injective hNk_le)
    have hNksolvMap : Group.IsSolvable ↥(Nk.map e.toMonoidHom) := by
      haveI : Group.IsSolvable ↥Nk := hNksolv
      exact CFSG.LieType.SteinbergBR.isSolvable_map e.toMonoidHom Nk
    have hNkmapNormal : (Nk.map e.toMonoidHom).Normal :=
      hNkN.map e.toMonoidHom e.surjective
    have hNkmapBot : Nk.map e.toMonoidHom = ⊥ := by
      haveI : (Nk.map e.toMonoidHom).Normal := hNkmapNormal
      exact eq_bot_of_normal_isSolvable_alt5_prod hNksolvMap
    have hNkbot : Nk = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxmap : e x ∈ Nk.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hx
      rw [hNkmapBot] at hxmap
      exact Subgroup.mem_bot.mpr (e.injective (by simpa using Subgroup.mem_bot.mp hxmap))
    have hD'Nk : D' ≤ Nk.map K.subtype := by
      intro d hd
      have hdK : d ∈ K := hD'K hd
      have hdk : (⟨d, hdK⟩ : ↥K) ∈ Dk :=
        Subgroup.mem_subgroupOf.mpr hd
      exact Subgroup.mem_map_of_mem K.subtype (hDkNk hdk)
    have hNkmapKbot : Nk.map K.subtype = ⊥ := by rw [hNkbot]; simp
    exact hD'ne (le_bot_iff.mp (hD'Nk.trans (le_of_eq hNkmapKbot)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
