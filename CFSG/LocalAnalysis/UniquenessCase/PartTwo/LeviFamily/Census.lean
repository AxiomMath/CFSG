module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Lift
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.OddW
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index
import CFSG.Quasithin.Background.G64Case1Pre

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin.G64

theorem pCore_two_eq_bot_of_le_normalizer_of_odd_relIndex_finite {ι : Type} [Finite ι]
    {G : ι → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    {Λ : Subgroup (∀ j, G j)} (hSΛ : Subgroup.pi Set.univ S ≤ Λ)
    (hΛS : Λ ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hodd : Odd ((Subgroup.pi Set.univ S).relIndex Λ))
    (hS : ∀ j (N : Subgroup ↥(S j)), N.Normal → IsPGroup 2 N → N = ⊥) :
    CFSG.pCore 2 ↥Λ = ⊥ := by
  classical
  let N : Subgroup ↥Λ := (Subgroup.pi Set.univ S).subgroupOf Λ
  have hNnormal : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSΛ).mpr hΛS
  have hNindex : N.index = (Subgroup.pi Set.univ S).relIndex Λ := rfl
  have hPle : CFSG.pCore 2 ↥Λ ≤ N :=
    CFSG.ComponentClassification.AS76b.Lemma22Full.le_of_isPGroup_of_odd_relIndex
      (N := N) (Y := ⊤) (P := CFSG.pCore 2 ↥Λ) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hNnormal])
      (by simpa [Subgroup.relIndex_top_right, hNindex] using hodd) le_top
      CFSG.pCore_isPGroup
  have hcoord_mem : ∀ (j : ι) (x : ↥N),
      (((x : ↥N) : ↥Λ) : ∀ i, G i) j ∈ S j := by
    intro j x
    have hxpi := Subgroup.mem_subgroupOf.mp x.2
    rw [Subgroup.mem_pi] at hxpi
    exact hxpi j (Set.mem_univ j)
  let coord : ∀ j, ↥N →* ↥(S j) := fun j =>
    { toFun := fun x => ⟨(((x : ↥N) : ↥Λ) : ∀ i, G i) j, hcoord_mem j x⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := fun _ _ => by apply Subtype.ext; rfl }
  have hcoord_apply : ∀ (j : ι) (x : ↥N),
      ((coord j x : ↥(S j)) : G j) = (((x : ↥N) : ↥Λ) : ∀ i, G i) j :=
    fun _ _ => rfl
  have hcoord_surj : ∀ j, Function.Surjective (coord j) := by
    intro j y
    refine ⟨⟨⟨MonoidHom.mulSingle G j (y : G j),
        hSΛ ((Subgroup.mulSingle_mem_pi j (y : G j)).mpr fun _ => y.2)⟩,
      Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mulSingle_mem_pi j (y : G j)).mpr fun _ => y.2)⟩, ?_⟩
    apply Subtype.ext
    exact Pi.mulSingle_eq_same ..
  have hcoord_bot : ∀ j, ((CFSG.pCore 2 ↥Λ).subgroupOf N).map (coord j) = ⊥ := by
    intro j
    have hnormal : (((CFSG.pCore 2 ↥Λ).subgroupOf N).map (coord j)).Normal :=
      ((CFSG.pCore_normal (p := 2) (G := ↥Λ)).subgroupOf N).map (coord j) (hcoord_surj j)
    have h2 : IsPGroup 2 (((CFSG.pCore 2 ↥Λ).subgroupOf N).map (coord j)) :=
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥Λ)).comap_subtype).map (coord j)
    exact hS j _ hnormal h2
  rw [eq_bot_iff]
  intro y hy
  have hyN : y ∈ N := hPle hy
  apply Subtype.ext
  funext j
  have hy' : coord j ⟨y, hyN⟩ ∈ ((CFSG.pCore 2 ↥Λ).subgroupOf N).map (coord j) :=
    ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rw [hcoord_bot j, Subgroup.mem_bot] at hy'
  have h1 : (((⟨y, hyN⟩ : ↥N) : ↥Λ) : ∀ i, G i) j = 1 :=
    (hcoord_apply j ⟨y, hyN⟩).symm.trans (congrArg Subtype.val hy')
  simpa using h1

variable {R : Type} [Group R] [Finite R]
variable {Q : Type} [Group Q] [Finite Q] {σ : Q →* R}
variable {n : ℕ} {G : Fin n → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
variable {S : ∀ j, Subgroup (G j)} {β : Q →* ∀ j, G j}

private abbrev leviBlockSub (j : Fin n) : Subgroup (∀ j, G j) :=
  (S j).map (MonoidHom.mulSingle G j)

omit [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockSub_subgroupOf_normal (_hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i))) (j : Fin n) :
    ((leviBlockSub (S := S) j).subgroupOf β.range).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨s, hs, hxs⟩ := Subgroup.mem_map.mp hx
  have hgN : (g : ∀ i, G i) ∈ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)) :=
    hn g.2
  have hxpi : (x : ∀ i, G i) ∈ Subgroup.pi Set.univ S :=
    hxs ▸ (Subgroup.mulSingle_mem_pi j s).mpr fun _ => hs
  have hpi : (g : ∀ i, G i) * (x : ∀ i, G i) * (g : ∀ i, G i)⁻¹ ∈
      Subgroup.pi Set.univ S :=
    (Subgroup.mem_normalizer_iff.mp hgN _).mp hxpi
  have heq : (g : ∀ i, G i) * (x : ∀ i, G i) * (g : ∀ i, G i)⁻¹ =
      MonoidHom.mulSingle G j ((g : ∀ i, G i) j * s * ((g : ∀ i, G i) j)⁻¹) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [Pi.mul_apply, MonoidHom.mulSingle_apply, ← hxs]
    · simp [Pi.mul_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hk, ← hxs]
  change (g : ∀ i, G i) * (x : ∀ i, G i) * (g : ∀ i, G i)⁻¹ ∈ leviBlockSub (S := S) j
  rw [heq]
  refine Subgroup.mem_map.mpr ⟨(g : ∀ i, G i) j * s * ((g : ∀ i, G i) j)⁻¹, ?_, rfl⟩
  simpa [← hxs] using (Subgroup.mem_pi Set.univ).mp hpi j (Set.mem_univ j)

omit [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockSub_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (leviBlockSub (S := S) i) (leviBlockSub (S := S) j) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hxi, hxj⟩
  obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hxi
  obtain ⟨t, -, ht⟩ := Subgroup.mem_map.mp hxj
  have hs : s = 1 := by
    have h := congrFun ht i
    rw [MonoidHom.mulSingle_apply, MonoidHom.mulSingle_apply,
      Pi.mulSingle_eq_of_ne hij, Pi.mulSingle_eq_same] at h
    exact h.symm
  rw [Subgroup.mem_bot, hs, map_one]

omit [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockSub_subgroupOf_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint ((leviBlockSub (S := S) i).subgroupOf β.range)
      ((leviBlockSub (S := S) j).subgroupOf β.range) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  obtain ⟨hxi, hxj⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_subgroupOf] at hxi hxj
  have h := (disjoint_iff_inf_le.mp (leviBlockSub_disjoint (S := S) hij))
    (Subgroup.mem_inf.mpr ⟨hxi, hxj⟩)
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h))

omit [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockSub_commutator_eq_bot (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)))
    {i j : Fin n} (hij : i ≠ j) :
    ⁅(leviBlockSub (S := S) i).subgroupOf β.range,
      (leviBlockSub (S := S) j).subgroupOf β.range⁆ = ⊥ := by
  have := leviBlockSub_subgroupOf_normal (S := S) (β := β) hle hn i
  have := leviBlockSub_subgroupOf_normal (S := S) (β := β) hle hn j
  exact Subgroup.commutator_eq_bot_of_disjoint (leviBlockSub_subgroupOf_disjoint hij)

omit [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockSub_le_pi (j : Fin n) :
    leviBlockSub (S := S) j ≤ Subgroup.pi Set.univ S := by
  rintro _ ⟨s, hs, rfl⟩
  exact (Subgroup.mulSingle_mem_pi j s).mpr fun _ => hs

private noncomputable def leviBlockSingle (hle : Subgroup.pi Set.univ S ≤ β.range) (j : Fin n) :
    ↥(S j) →* ↥β.range :=
  ((MonoidHom.mulSingle G j).comp (S j).subtype).codRestrict β.range fun s =>
    hle ((Subgroup.mulSingle_mem_pi j (s : G j)).mpr fun _ => s.2)

omit [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockSingle_injective (hle : Subgroup.pi Set.univ S ≤ β.range) (j : Fin n) :
    Function.Injective (leviBlockSingle (S := S) (β := β) hle j) := by
  intro a b hab
  have h := congrArg (fun x : ↥β.range => (x : ∀ i, G i) j) hab
  simp only [leviBlockSingle, MonoidHom.comp_apply, MonoidHom.codRestrict_apply,
    MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] at h
  exact Subtype.ext h

omit [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockSingle_mem (hle : Subgroup.pi Set.univ S ≤ β.range) (j : Fin n)
    (s : ↥(S j)) :
    leviBlockSingle (S := S) (β := β) hle j s ∈
      (leviBlockSub (S := S) j).subgroupOf β.range := by
  refine Subgroup.mem_subgroupOf.mpr ?_
  exact Subgroup.mem_map.mpr ⟨s, s.2, rfl⟩

private noncomputable def leviBlockMap (hle : Subgroup.pi Set.univ S ≤ β.range)
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) (j : Fin n) :
    ↥(S j) →* ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) :=
  (ψ.comp (leviBlockSingle (S := S) (β := β) hle j)).codRestrict _ fun s =>
    Subgroup.mem_map_of_mem ψ (leviBlockSingle_mem hle j s)

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockMap_surjective (hle : Subgroup.pi Set.univ S ≤ β.range)
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) (j : Fin n) :
    Function.Surjective (leviBlockMap (S := S) (β := β) hle ψ j) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨s, hs, hseq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
  refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
  exact congrArg ψ (Subtype.ext hseq)

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockMap_ker_le_center (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict) (j : Fin n) :
    (leviBlockMap (S := S) (β := β) hle ψ j).ker ≤ Subgroup.center ↥(S j) := by
  intro s hs
  have hmem : leviBlockSingle (S := S) (β := β) hle j s ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg (fun x : ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) =>
      (x : R ⧸ CFSG.pCore 2 R)) hs
  obtain ⟨z, hz, hzβ⟩ := Subgroup.mem_map.mp (hψker hmem)
  have hβz : (leviBlockSingle (S := S) (β := β) hle j s : ∀ i, G i) = β z := by
    rw [← hzβ]
    rfl
  have hcentral : ∀ w : ↥β.range,
      leviBlockSingle (S := S) (β := β) hle j s * w =
        w * leviBlockSingle (S := S) (β := β) hle j s := by
    intro w
    obtain ⟨q, hq⟩ := MonoidHom.rangeRestrict_surjective β w
    apply Subtype.ext
    have hw : (w : ∀ i, G i) = β q := by rw [← hq]; rfl
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hβz, hw]
    have hcz := Subgroup.mem_center_iff.mp (hc hz) q
    simpa only [map_mul] using congrArg β hcz.symm
  rw [Subgroup.mem_center_iff]
  intro t
  refine leviBlockSingle_injective hle j ?_
  rw [map_mul, map_mul]
  exact (hcentral (leviBlockSingle (S := S) (β := β) hle j t)).symm

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem isLeviBlock_leviBlockMap (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict) {j : Fin n}
    (hL : IsLeviBlock ↥(S j)) :
    IsLeviBlock ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) := by
  have hZ := leviBlockMap_ker_le_center (S := S) (β := β) hc hle ψ hψker j
  have : (leviBlockMap (S := S) (β := β) hle ψ j).ker.Normal :=
    MonoidHom.normal_ker _
  have hq : IsLeviBlock (↥(S j) ⧸ (leviBlockMap (S := S) (β := β) hle ψ j).ker) :=
    IsLeviBlock.quotient hL hZ
  exact IsLeviBlock.of_mulEquiv
    (QuotientGroup.quotientKerEquivOfSurjective _ (leviBlockMap_surjective hle ψ j)) hq

omit [Finite Q] in
private theorem pCore_range_eq_bot (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range)
    (hS : ∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) :
    CFSG.pCore 2 ↥β.range = ⊥ := by
  refine pCore_two_eq_bot_of_le_normalizer_of_odd_relIndex_finite hle hn
    (Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp hi)) ?_
  intro j N hN h2
  rcases hS j with hbot | hL
  · have : Subsingleton ↥(S j) := by rw [hbot]; infer_instance
    exact Subgroup.eq_bot_of_subsingleton N
  · exact IsLeviBlock.eq_bot_of_normal_isPGroup_two hL hN h2

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockSub_subgroupOf_map_normal (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)))
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) (hψ : Function.Surjective ψ) (j : Fin n) :
    (((leviBlockSub (S := S) j).subgroupOf β.range).map ψ).Normal :=
  (leviBlockSub_subgroupOf_normal hle hn j).map ψ hψ

private noncomputable def leviBlockEquiv (hle : Subgroup.pi Set.univ S ≤ β.range)
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) (j : Fin n) :
    ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) ≃*
      ↥(S j) ⧸ (leviBlockMap (S := S) (β := β) hle ψ j).ker :=
  (QuotientGroup.quotientKerEquivOfSurjective _
    (leviBlockMap_surjective (S := S) (β := β) hle ψ j)).symm

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem isQuasisimple_leviBlockMap_of_isQuasisimple (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict) {j : Fin n}
    (hq : CFSG.Open.IsQuasisimple ↥(S j)) :
    CFSG.Open.IsQuasisimple
      ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) :=
  CFSG.Open.IsQuasisimple.of_mulEquiv (leviBlockEquiv (S := S) (β := β) hle ψ j)
    (CFSG.ComponentClassification.Quasisimple.central_quotient hq _
      (leviBlockMap_ker_le_center (S := S) (β := β) hc hle ψ hψker j))

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem isQuasisimple_of_isQuasisimple_leviBlockMap (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict) {j : Fin n}
    (hL : IsLeviBlock ↥(S j))
    (hq : CFSG.Open.IsQuasisimple
      ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ)) :
    CFSG.Open.IsQuasisimple ↥(S j) := by
  by_contra hqs
  have hZbot : (leviBlockMap (S := S) (β := β) hle ψ j).ker = ⊥ :=
    le_bot_iff.mp ((leviBlockMap_ker_le_center hc hle ψ hψker j).trans_eq
      (IsLeviBlock.center_eq_bot_of_not_isQuasisimple hL hqs))
  have hinj : Function.Injective (leviBlockMap (S := S) (β := β) hle ψ j) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hZbot
  have hqS : CFSG.Open.IsQuasisimple ↥(S j) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (MulEquiv.ofBijective _ ⟨hinj, leviBlockMap_surjective hle ψ j⟩
        : ↥(S j) ≃* ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ)) hq
  rcases hL with ⟨e3⟩ | ⟨e6⟩ | ⟨hq', -⟩
  · obtain ⟨e⟩ := e3
    exact not_isQuasisimple_of_perm (n := 3) (by norm_num) e
      ⟨Group.isPerfect_def.mpr hqS.1, hqS.2,
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hqS⟩
  · obtain ⟨e⟩ := e6
    exact not_isQuasisimple_of_perm (n := 6) (by norm_num) e
      ⟨Group.isPerfect_def.mpr hqS.1, hqS.2,
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hqS⟩
  · exact hqs hq'

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem nonempty_center_quotient_leviBlockMap (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict) {j : Fin n}
    (hq : CFSG.Open.IsQuasisimple ↥(S j)) :
    Nonempty (↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) ⧸
        center ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) ≃*
      ↥(S j) ⧸ center ↥(S j)) := by
  have hZ := leviBlockMap_ker_le_center (S := S) (β := β) hc hle ψ hψker j
  have : (leviBlockMap (S := S) (β := β) hle ψ j).ker.Normal := MonoidHom.normal_ker _
  exact ⟨(QuotientGroup.congr
    (Subgroup.center ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ))
    (Subgroup.center (↥(S j) ⧸ (leviBlockMap (S := S) (β := β) hle ψ j).ker))
    (leviBlockEquiv (S := S) (β := β) hle ψ j) (Subgroup.map_center_eq _)).trans
    (nonempty_quotient_center_quotient_mulEquiv hq hZ).some⟩

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem not_isL2_leviBlockMap (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict) {j : Fin n}
    (hq : CFSG.Open.IsQuasisimple ↥(S j))
    (hno : ∀ m, 3 ≤ m → ¬ IsL2 (↥(S j) ⧸ center ↥(S j)) m) {m : ℕ} (hm : 3 ≤ m) :
    ¬ IsL2 (↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) ⧸
      center ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ)) m := by
  obtain ⟨e⟩ := nonempty_center_quotient_leviBlockMap hc hle ψ hψker hq
  intro hL2
  exact hno m hm (CFSG.Blueprint.LieModel.of_mulEquiv e hL2)

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem not_two_dvd_iSup_index (hle : Subgroup.pi Set.univ S ≤ β.range)
    (_hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range)
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) (hψsurj : Function.Surjective ψ) :
    ¬ 2 ∣ (⨆ j, ((leviBlockSub (S := S) j).subgroupOf β.range).map ψ).index := by
  let J : Subgroup (R ⧸ CFSG.pCore 2 R) :=
    ⨆ j, ((leviBlockSub (S := S) j).subgroupOf β.range).map ψ
  have hle1 : ((Subgroup.pi Set.univ S).subgroupOf β.range).map ψ ≤ J := by
    rw [Subgroup.map_le_iff_le_comap]
    rw [← Subgroup.map_le_map_iff_of_injective β.range.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hle]
    rw [Subgroup.pi_le_iff]
    intro j y hy
    refine Subgroup.mem_map.mpr ⟨⟨y, hle ((leviBlockSub_le_pi (S := S) j) hy)⟩, ?_, rfl⟩
    exact Subgroup.mem_comap.mpr
      (le_iSup (fun j => ((leviBlockSub (S := S) j).subgroupOf β.range).map ψ) j
        (Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr hy)))
  have h1 : J.index ∣ (((Subgroup.pi Set.univ S).subgroupOf β.range).map ψ).index :=
    Subgroup.index_dvd_of_le hle1
  have h2 : (((Subgroup.pi Set.univ S).subgroupOf β.range).map ψ).index ∣
      ((Subgroup.pi Set.univ S).subgroupOf β.range).index :=
    Subgroup.index_map_dvd _ hψsurj
  have h3 : ¬ 2 ∣ ((Subgroup.pi Set.univ S).subgroupOf β.range).index := by
    rw [show ((Subgroup.pi Set.univ S).subgroupOf β.range).index =
      (Subgroup.pi Set.univ S).relIndex β.range from rfl]
    exact hi
  intro h
  exact h3 (h.trans (h1.trans h2))

private noncomputable def blocksFamily (_hle : Subgroup.pi Set.univ S ≤ β.range)
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) {d : ℕ}
    (eT : {j : Fin n // S j ≠ ⊥} ≃ Fin d) : Fin d → Subgroup (R ⧸ CFSG.pCore 2 R) :=
  fun i => ((leviBlockSub (S := S) (eT.symm i).1).subgroupOf β.range).map ψ

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem blocksFamily_normal (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)))
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) (hψsurj : Function.Surjective ψ) {d : ℕ}
    (eT : {j : Fin n // S j ≠ ⊥} ≃ Fin d) (i : Fin d) :
    (blocksFamily (S := S) (β := β) hle ψ eT i).Normal :=
  leviBlockSub_subgroupOf_map_normal hle hn ψ hψsurj (eT.symm i).1

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem blocksFamily_commutator_eq_bot (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)))
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) {d : ℕ}
    (eT : {j : Fin n // S j ≠ ⊥} ≃ Fin d) {i j : Fin d} (hij : i ≠ j) :
    ⁅blocksFamily (S := S) (β := β) hle ψ eT i,
      blocksFamily (S := S) (β := β) hle ψ eT j⁆ = ⊥ := by
  have hne : (eT.symm i).1 ≠ (eT.symm j).1 := fun h =>
    hij (eT.symm.injective (Subtype.ext h))
  simp only [blocksFamily]
  rw [← Subgroup.map_commutator, leviBlockSub_commutator_eq_bot hle hn hne,
    Subgroup.map_bot]

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem blocksFamily_isLeviBlock (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict)
    (hS : ∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) {d : ℕ}
    (eT : {j : Fin n // S j ≠ ⊥} ≃ Fin d) (i : Fin d) :
    IsLeviBlock ↥(blocksFamily (S := S) (β := β) hle ψ eT i) := by
  rcases hS (eT.symm i).1 with hbot | hL
  · exact absurd hbot (eT.symm i).2
  · exact isLeviBlock_leviBlockMap hc hle ψ hψker hL

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem iSup_blocksFamily_eq (hle : Subgroup.pi Set.univ S ≤ β.range)
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) {d : ℕ}
    (eT : {j : Fin n // S j ≠ ⊥} ≃ Fin d) :
    (⨆ i, blocksFamily (S := S) (β := β) hle ψ eT i) =
      ⨆ j, ((leviBlockSub (S := S) j).subgroupOf β.range).map ψ := by
  refine le_antisymm (iSup_le fun i => le_iSup
    (fun j => ((leviBlockSub (S := S) j).subgroupOf β.range).map ψ) (eT.symm i).1)
    (iSup_le fun j => ?_)
  by_cases hj : S j = ⊥
  · have hbot : ((leviBlockSub (S := S) j).subgroupOf β.range).map ψ = ⊥ := by
      change (((S j).map (MonoidHom.mulSingle G j)).subgroupOf β.range).map ψ = ⊥
      rw [hj]
      simp
    rw [hbot]
    exact bot_le
  · have h := le_iSup (fun i => blocksFamily (S := S) (β := β) hle ψ eT i) (eT ⟨j, hj⟩)
    have heq : blocksFamily (S := S) (β := β) hle ψ eT (eT ⟨j, hj⟩) =
        ((leviBlockSub (S := S) j).subgroupOf β.range).map ψ := by
      simp only [blocksFamily]
      rw [Equiv.symm_apply_apply]
    rwa [heq] at h

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem not_two_dvd_index_blocksFamily (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range)
    (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R) (hψsurj : Function.Surjective ψ) {d : ℕ}
    (eT : {j : Fin n // S j ≠ ⊥} ≃ Fin d) :
    ¬ 2 ∣ (⨆ i, blocksFamily (S := S) (β := β) hle ψ eT i).index := by
  rw [iSup_blocksFamily_eq]
  exact not_two_dvd_iSup_index hle hn hi ψ hψsurj

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem censusAlt_blocksFamily (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict)
    (hS : ∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) (halt : CensusAlt S) {d : ℕ}
    (eT : {j : Fin n // S j ≠ ⊥} ≃ Fin d) :
    (d ≤ 2 ∧ ∀ i, CFSG.Open.IsQuasisimple
      ↥(blocksFamily (S := S) (β := β) hle ψ eT i)) ∨
      ∀ i, CFSG.Open.IsQuasisimple ↥(blocksFamily (S := S) (β := β) hle ψ eT i) →
        ∀ m, 3 ≤ m → ¬ IsL2 (↥(blocksFamily (S := S) (β := β) hle ψ eT i) ⧸
          center ↥(blocksFamily (S := S) (β := β) hle ψ eT i)) m := by
  rcases halt with ⟨h2, hq⟩ | hno
  · left
    refine ⟨?_, fun i => ?_⟩
    · have hd : Nat.card {j : Fin n // S j ≠ ⊥} = d := by
        rw [Nat.card_congr eT]
        simp
      omega
    · rcases hq (eT.symm i).1 with hbot | hq'
      · exact absurd hbot (eT.symm i).2
      · exact isQuasisimple_leviBlockMap_of_isQuasisimple hc hle ψ hψker hq'
  · right
    intro i hqi m hm
    have hL : IsLeviBlock ↥(S (eT.symm i).1) := by
      rcases hS (eT.symm i).1 with hbot | hL
      · exact absurd hbot (eT.symm i).2
      · exact hL
    have hqS := isQuasisimple_of_isQuasisimple_leviBlockMap hc hle ψ hψker hL hqi
    exact not_isL2_leviBlockMap hc hle ψ hψker hqS
      (fun m hm => hno (eT.symm i).1 hqS m hm) hm

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem three_dvd_card_center_leviBlockMap (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict) {j : Fin n}
    (hq : CFSG.Open.IsQuasisimple ↥(S j))
    (h3 : 3 ∣ Nat.card (↥(S j) ⧸ center ↥(S j))) :
    3 ∣ Nat.card (↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) ⧸
      center ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ)) := by
  obtain ⟨e⟩ := nonempty_center_quotient_leviBlockMap hc hle ψ hψker hq
  rwa [← Nat.card_congr e.toEquiv] at h3

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem leviBlockMap_perm_three_imp (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict) {two big : Prop}
    (hB : BlockFacts two big S) {j : Fin n} (hL : IsLeviBlock ↥(S j))
    (h3 : Nonempty (↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) ≃*
      Equiv.Perm (Fin 3))) :
    two := by
  by_cases hqs : CFSG.Open.IsQuasisimple ↥(S j)
  · have hqb : CFSG.Open.IsQuasisimple
        ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) :=
      isQuasisimple_leviBlockMap_of_isQuasisimple hc hle ψ hψker hqs
    exact absurd h3 (not_nonempty_mulEquiv_perm_three (Or.inr hqb))
  · have hZ : Subgroup.center ↥(S j) = ⊥ :=
      IsLeviBlock.center_eq_bot_of_not_isQuasisimple hL hqs
    have hker : (leviBlockMap (S := S) (β := β) hle ψ j).ker = ⊥ :=
      le_bot_iff.mp ((leviBlockMap_ker_le_center hc hle ψ hψker j).trans_eq hZ)
    have hinj : Function.Injective (leviBlockMap (S := S) (β := β) hle ψ j) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact hker
    have eS : ↥(S j) ≃*
        ↥((leviBlockSub (S := S) j).subgroupOf β.range |>.map ψ) :=
      MulEquiv.ofBijective _ ⟨hinj, leviBlockMap_surjective hle ψ j⟩
    exact hB.2.1 _ ⟨eS.trans h3.some⟩

omit [Finite R] [Finite Q] [∀ (j : Fin n), Finite (G j)] in
private theorem blockFacts_blocksFamily (hc : σ.ker ≤ Subgroup.center Q)
    (hle : Subgroup.pi Set.univ S ≤ β.range) (ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R)
    (hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict)
    (hS : ∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) {two big : Prop} (hB : BlockFacts two big S)
    {d : ℕ} (eT : {j : Fin n // S j ≠ ⊥} ≃ Fin d) :
    (∀ i, CFSG.Open.IsQuasisimple ↥(blocksFamily (S := S) (β := β) hle ψ eT i) →
      3 ∣ Nat.card (↥(blocksFamily (S := S) (β := β) hle ψ eT i) ⧸
        center ↥(blocksFamily (S := S) (β := β) hle ψ eT i))) ∧
    (∀ i, Nonempty (↥(blocksFamily (S := S) (β := β) hle ψ eT i) ≃* Equiv.Perm (Fin 3)) →
      two) ∧
    (d ≤ 2 ∨ big) := by
  have hL : ∀ i, IsLeviBlock ↥(S (eT.symm i).1) := by
    intro i
    rcases hS (eT.symm i).1 with hbot | hL
    · exact absurd hbot (eT.symm i).2
    · exact hL
  refine ⟨fun i hq => ?_, fun i h3 => ?_, ?_⟩
  · have hqs := isQuasisimple_of_isQuasisimple_leviBlockMap hc hle ψ hψker (hL i) hq
    exact three_dvd_card_center_leviBlockMap hc hle ψ hψker hqs (hB.1 _ hqs)
  · exact leviBlockMap_perm_three_imp hc hle ψ hψker hB (hL i) h3
  · have hd : Nat.card {j : Fin n // S j ≠ ⊥} = d := by
      rw [Nat.card_congr eT]
      simp
    rcases hB.2.2 with h2 | hb
    · exact Or.inl (hd ▸ h2)
    · exact Or.inr hb

private theorem exists_blocks_of_fin {R : Type} [Group R] [Finite R]
    {Q : Type} [Group Q] [Finite Q] {σ : Q →* R} {n : ℕ} {G : Fin n → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    {β : Q →* ∀ j, G j} (hσ : Function.Surjective σ)
    (hc : σ.ker ≤ Subgroup.center Q) (ho : Odd (Nat.card σ.ker))
    (hβ : IsPGroup 2 β.ker) (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range)
    (hS : ∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) (halt : CensusAlt S) :
    ∃ (d : ℕ) (M : Fin d → Subgroup (R ⧸ CFSG.pCore 2 R)), (∀ i, (M i).Normal) ∧
      (∀ i j, i ≠ j → ⁅M i, M j⁆ = ⊥) ∧ (∀ i, IsLeviBlock ↥(M i)) ∧
      ¬ 2 ∣ (⨆ i, M i).index ∧
      ((d ≤ 2 ∧ ∀ i, CFSG.Open.IsQuasisimple ↥(M i)) ∨
        ∀ i, CFSG.Open.IsQuasisimple ↥(M i) → ∀ m, 3 ≤ m →
          ¬ IsL2 (↥(M i) ⧸ center ↥(M i)) m) ∧
      ∀ two big : Prop, BlockFacts two big S →
        (∀ i, CFSG.Open.IsQuasisimple ↥(M i) → 3 ∣ Nat.card (↥(M i) ⧸ center ↥(M i))) ∧
        (∀ i, Nonempty (↥(M i) ≃* Equiv.Perm (Fin 3)) → two) ∧ (d ≤ 2 ∨ big) := by
  classical
  have hpc : CFSG.pCore 2 ↥β.range = ⊥ := pCore_range_eq_bot hle hn hi hS
  obtain ⟨ψ, hψsurj, -, hψker⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.exists_levi_quotient_of_pCore_eq_bot
      hσ hc ho β hβ hpc
  let eT : {j : Fin n // S j ≠ ⊥} ≃ Fin (Nat.card {j : Fin n // S j ≠ ⊥}) :=
    Finite.equivFin _
  exact ⟨Nat.card {j : Fin n // S j ≠ ⊥},
    blocksFamily (S := S) (β := β) hle ψ eT, blocksFamily_normal hle hn ψ hψsurj eT,
    fun i j hij => blocksFamily_commutator_eq_bot hle hn ψ eT hij,
    blocksFamily_isLeviBlock hc hle ψ hψker hS eT,
    not_two_dvd_index_blocksFamily hle hn hi ψ hψsurj eT,
    censusAlt_blocksFamily hc hle ψ hψker hS halt eT,
    fun two big hB => blockFacts_blocksFamily hc hle ψ hψker hS hB eT⟩

private theorem blockFacts_comp {ι κ : Type} {G : ι → Type} [∀ j, Group (G j)]
    {S : ∀ j, Subgroup (G j)} {two big : Prop} (hB : BlockFacts two big S) (e : κ ≃ ι) :
    BlockFacts two big (fun k => S (e k)) := by
  refine ⟨fun k => hB.1 (e k), fun k => hB.2.1 (e k), ?_⟩
  rcases hB.2.2 with h2 | hb
  · left
    have hcard : Nat.card {k : κ // S (e k) ≠ ⊥} = Nat.card {j : ι // S j ≠ ⊥} :=
      Nat.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)
    rw [hcard]
    exact h2
  · exact Or.inr hb

private theorem exists_blocks_of_hasLeviData {R : Type} [Group R] [Finite R]
    {Q : Type} [Group Q] [Finite Q] {σ : Q →* R} {ι : Type} [Finite ι]
    {G : ι → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    {β : Q →* ∀ j, G j} (hσ : Function.Surjective σ)
    (hc : σ.ker ≤ Subgroup.center Q) (ho : Odd (Nat.card σ.ker))
    (hβ : IsPGroup 2 β.ker) (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ i, G i)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range)
    (hS : ∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) (halt : CensusAlt S) :
    ∃ (d : ℕ) (M : Fin d → Subgroup (R ⧸ CFSG.pCore 2 R)), (∀ i, (M i).Normal) ∧
      (∀ i j, i ≠ j → ⁅M i, M j⁆ = ⊥) ∧ (∀ i, IsLeviBlock ↥(M i)) ∧
      ¬ 2 ∣ (⨆ i, M i).index ∧
      ((d ≤ 2 ∧ ∀ i, CFSG.Open.IsQuasisimple ↥(M i)) ∨
        ∀ i, CFSG.Open.IsQuasisimple ↥(M i) → ∀ m, 3 ≤ m →
          ¬ IsL2 (↥(M i) ⧸ center ↥(M i)) m) ∧
      ∀ two big : Prop, BlockFacts two big S →
        (∀ i, CFSG.Open.IsQuasisimple ↥(M i) → 3 ∣ Nat.card (↥(M i) ⧸ center ↥(M i))) ∧
        (∀ i, Nonempty (↥(M i) ≃* Equiv.Perm (Fin 3)) → two) ∧ (d ≤ 2 ∨ big) := by
  classical
  let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
  let φe : (∀ j, G j) ≃* (∀ i : Fin (Nat.card ι), G (e.symm i)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.piReindex e
  let β' : Q →* (∀ i : Fin (Nat.card ι), G (e.symm i)) := φe.toMonoidHom.comp β
  let S' : ∀ i : Fin (Nat.card ι), Subgroup (G (e.symm i)) := fun i => S (e.symm i)
  have hβ' : IsPGroup 2 β'.ker := by
    have hker : β'.ker = β.ker := by
      ext z
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact φe.map_eq_one_iff
    rw [hker]
    exact hβ
  have hmap := CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.map_pi_piReindex (G := G) e
  have hle' : Subgroup.pi Set.univ S' ≤ β'.range := by
    rw [show β' = φe.toMonoidHom.comp β from rfl, MonoidHom.range_comp, ← hmap S]
    exact Subgroup.map_mono hle
  have hn' : β'.range ≤ normalizer (Subgroup.pi Set.univ S' :
      Set (∀ i : Fin (Nat.card ι), G (e.symm i))) := by
    rw [show β' = φe.toMonoidHom.comp β from rfl, MonoidHom.range_comp, ← hmap S,
      ← Subgroup.map_normalizer_eq_of_bijective (Subgroup.pi Set.univ S) φe.bijective]
    exact Subgroup.map_mono hn
  have hi' : ¬ 2 ∣ (Subgroup.pi Set.univ S').relIndex β'.range := by
    rw [show β' = φe.toMonoidHom.comp β from rfl, MonoidHom.range_comp, ← hmap S,
      Subgroup.relIndex_map_map_of_injective _ _ φe.injective]
    exact hi
  have hS' : ∀ i, S' i = ⊥ ∨ IsLeviBlock ↥(S' i) := fun i => hS (e.symm i)
  have halt' : CensusAlt S' := by
    rcases halt with ⟨h2, hq⟩ | hno
    · left
      refine ⟨?_, fun i => hq (e.symm i)⟩
      have hcard : Nat.card {i : Fin (Nat.card ι) // S' i ≠ ⊥} =
          Nat.card {j : ι // S j ≠ ⊥} :=
        Nat.card_congr (Equiv.subtypeEquiv e.symm fun i => Iff.rfl)
      rw [hcard]
      exact h2
    · exact Or.inr fun i => hno (e.symm i)
  obtain ⟨d, M, h1, h2, h3, h4, h5, hX⟩ :=
    exists_blocks_of_fin hσ hc ho hβ' hle' hn' hi' hS' halt'
  refine ⟨d, M, h1, h2, h3, h4, h5, ?_⟩
  intro two big hB
  exact hX two big (blockFacts_comp hB e.symm)

private theorem isLeviFamily_comap_bar_map_subtype {X : Type} [Group X] [Finite X]
    {J : Subgroup X} {d : ℕ} {M : Fin d → Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hd : d ≠ 0)
    (h : IsLeviFamily ⊤ d M) :
    IsLeviFamily J d
      (fun i => ((M i).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).map J.subtype) := by
  let π : ↥J →* ↥J ⧸ CFSG.pCore 2 ↥J := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have h1 := h.comap (φ := π) hπ hπker hd
  rw [Subgroup.comap_top] at h1
  have h2 := h1.map (φ := J.subtype) J.subtype_injective
  rwa [show (⊤ : Subgroup ↥J).map J.subtype = J from ?_] at h2
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem leviAlt_comap_bar_map_subtype {X : Type} [Group X] [Finite X]
    {J : Subgroup X} {d : ℕ} {M : Fin d → Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)}
    (h : LeviAlt ⊤ d M) :
    LeviAlt J d
      (fun i => ((M i).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).map J.subtype) := by
  let π : ↥J →* ↥J ⧸ CFSG.pCore 2 ↥J := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have h1 := h.comap (φ := π) hπ hπker
  rw [Subgroup.comap_top] at h1
  have h2 := h1.map (φ := J.subtype) J.subtype_injective
  rwa [show (⊤ : Subgroup ↥J).map J.subtype = J from ?_] at h2
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem ne_zero_of_isLeviFamily_top_bar {X : Type} [Group X] [Finite X]
    {J : Subgroup X} (hJ : S19.IsNontrivialParabolic X J) {d : ℕ}
    {M : Fin d → Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)}
    (hodd : ¬ 2 ∣ (⨆ i, M i).index) : d ≠ 0 := by
  rintro rfl
  have hbot : (⨆ i : Fin 0, M i) = ⊥ := by simp
  have hYodd : ¬ 2 ∣ Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) := by
    have h := hodd
    rw [hbot, Subgroup.index_bot] at h
    exact h
  have hOodd : Odd (CFSG.pCore 2 ↥J).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp hYodd)
  have hO2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
  obtain ⟨-, -, S, hSJ⟩ := hJ
  have hSleJ : (S : Subgroup X) ≤ J := Subgroup.le_normalizer.trans hSJ.le
  let SJ : Sylow 2 ↥J := S.subtype hSleJ
  have hSJcoe : (SJ : Subgroup ↥J) = (S : Subgroup X).subgroupOf J :=
    Sylow.coe_subtype S hSleJ
  have hle1 : CFSG.pCore 2 ↥J ≤ (SJ : Subgroup ↥J) :=
    IsPGroup.le_sylow_of_normal hO2 SJ
  have hle2 : (SJ : Subgroup ↥J) ≤ CFSG.pCore 2 ↥J :=
    CFSG.ComponentClassification.AS76b.Lemma22Full.le_of_isPGroup_of_odd_relIndex
      (N := CFSG.pCore 2 ↥J) (Y := ⊤) (P := (SJ : Subgroup ↥J)) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal])
      (by simpa [Subgroup.relIndex_top_right] using hOodd) le_top SJ.isPGroup'
  have hSeq : (S : Subgroup X) = pCoreOf 2 J := by
    calc (S : Subgroup X) = ((S : Subgroup X).subgroupOf J).map J.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hSleJ).symm
      _ = (SJ : Subgroup ↥J).map J.subtype := by rw [hSJcoe]
      _ = (CFSG.pCore 2 ↥J).map J.subtype := by rw [le_antisymm hle2 hle1]
      _ = pCoreOf 2 J := rfl
  have hnormal : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  have hset : (S : Set X) = (pCoreOf 2 J : Set X) :=
    congrArg (fun H : Subgroup X => (H : Set X)) hSeq
  have heq : Subgroup.normalizer (S : Set X) = J :=
    le_antisymm hSJ.le (by rw [hset]; exact hnormal)
  exact hSJ.ne heq

theorem HasLeviData.exists_blocks {R : Type} [Group R] [Finite R] (h : HasLeviData R) :
    ∃ (d : ℕ) (M : Fin d → Subgroup (R ⧸ CFSG.pCore 2 R)), (∀ i, (M i).Normal) ∧
      (∀ i j, i ≠ j → ⁅M i, M j⁆ = ⊥) ∧ (∀ i, IsLeviBlock ↥(M i)) ∧
      ¬ 2 ∣ (⨆ i, M i).index ∧
      ((d ≤ 2 ∧ ∀ i, CFSG.Open.IsQuasisimple ↥(M i)) ∨
        ∀ i, CFSG.Open.IsQuasisimple ↥(M i) → ∀ n, 3 ≤ n →
          ¬ IsL2 (↥(M i) ⧸ center ↥(M i)) n) := by
  classical
  obtain ⟨Q, hQg, hQf, σ, ι, hι, G, hGg, hGf, S, β, hσ, hc, ho, hβ, hle, hn, hi, hS, halt⟩ := h
  let _ : Group Q := hQg
  let _ : Finite Q := hQf
  let _ : ∀ j, Group (G j) := hGg
  let _ : ∀ j, Finite (G j) := hGf
  obtain ⟨d, M, h1, h2, h3, h4, h5, -⟩ :=
    exists_blocks_of_hasLeviData hσ hc ho hβ hle hn hi hS halt
  exact ⟨d, M, h1, h2, h3, h4, h5⟩

theorem HasLeviData.exists_isLeviFamily_leviAlt {X : Type} [Group X] [Finite X]
    {J : Subgroup X} (hJ : S19.IsNontrivialParabolic X J) (h : HasLeviData ↥J) :
    ∃ (d : ℕ) (L : Fin d → Subgroup X), IsLeviFamily J d L ∧ LeviAlt J d L := by
  obtain ⟨d, M, hMn, hMc, hMb, hodd, halt⟩ := h.exists_blocks
  have hR : CFSG.pCore 2 (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hfam := isLeviFamily_top_leviAlt_of_blocks hR M hMn hMc hMb hodd halt
  have hd : d ≠ 0 := ne_zero_of_isLeviFamily_top_bar hJ hodd
  exact ⟨d, fun i => ((M i).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).map J.subtype,
    isLeviFamily_comap_bar_map_subtype hd hfam.1, leviAlt_comap_bar_map_subtype hfam.2⟩

theorem hasLeviFamiliesAlt_of_hasLeviData {S : Type} [Group S] [Finite S]
    (h : ∀ J : Subgroup S, S19.IsNontrivialParabolic S J → HasLeviData ↥J) :
    HasLeviFamiliesAlt S := fun J hJ => (h J hJ).exists_isLeviFamily_leviAlt hJ

theorem HasLeviDataX.exists_blocks {two big : Prop} {R : Type} [Group R] [Finite R]
    (h : HasLeviDataX two big R) :
    ∃ (d : ℕ) (M : Fin d → Subgroup (R ⧸ CFSG.pCore 2 R)), (∀ i, (M i).Normal) ∧
      (∀ i j, i ≠ j → ⁅M i, M j⁆ = ⊥) ∧ (∀ i, IsLeviBlock ↥(M i)) ∧
      ¬ 2 ∣ (⨆ i, M i).index ∧
      ((d ≤ 2 ∧ ∀ i, CFSG.Open.IsQuasisimple ↥(M i)) ∨
        ∀ i, CFSG.Open.IsQuasisimple ↥(M i) → ∀ n, 3 ≤ n →
          ¬ IsL2 (↥(M i) ⧸ center ↥(M i)) n) ∧
      (∀ i, CFSG.Open.IsQuasisimple ↥(M i) → 3 ∣ Nat.card (↥(M i) ⧸ center ↥(M i))) ∧
      (∀ i, Nonempty (↥(M i) ≃* Equiv.Perm (Fin 3)) → two) ∧ (d ≤ 2 ∨ big) := by
  classical
  obtain ⟨Q, hQg, hQf, σ, ι, hι, G, hGg, hGf, S, β, hσ, hc, ho, hβ, hle, hn, hi, hS, halt,
    hB⟩ := h
  let _ : Group Q := hQg
  let _ : Finite Q := hQf
  let _ : ∀ j, Group (G j) := hGg
  let _ : ∀ j, Finite (G j) := hGf
  obtain ⟨d, M, h1, h2, h3, h4, h5, hX⟩ :=
    exists_blocks_of_hasLeviData hσ hc ho hβ hle hn hi hS halt
  obtain ⟨h6, h7, h8⟩ := hX two big hB
  exact ⟨d, M, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem HasLeviDataX.exists_isLeviFamily_leviAlt_leviBlk {two big : Prop} {X : Type} [Group X]
    [Finite X] {J : Subgroup X} (hJ : S19.IsNontrivialParabolic X J)
    (h : HasLeviDataX two big ↥J) :
    ∃ (d : ℕ) (L : Fin d → Subgroup X), IsLeviFamily J d L ∧ LeviAlt J d L ∧
      LeviBlk two big d L := by
  obtain ⟨d, M, hMn, hMc, hMb, hodd, halt, h3, h2, hd⟩ := h.exists_blocks
  have hR : CFSG.pCore 2 (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hfam := isLeviFamily_top_leviAlt_of_blocks hR M hMn hMc hMb hodd halt
  have hd0 : d ≠ 0 := ne_zero_of_isLeviFamily_top_bar hJ hodd
  exact ⟨d, fun i => ((M i).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).map J.subtype,
    isLeviFamily_comap_bar_map_subtype hd0 hfam.1, leviAlt_comap_bar_map_subtype hfam.2,
    (leviBlk_top_of_blocks hR M hMn hMb h3 h2 hd).comap_mk_map_subtype⟩

theorem hasLeviFamiliesBlk_of_hasLeviDataX {two big : Prop} {S : Type} [Group S] [Finite S]
    (h : ∀ J : Subgroup S, S19.IsNontrivialParabolic S J → HasLeviDataX two big ↥J) :
    HasLeviFamiliesBlk two big S := fun J hJ =>
  (h J hJ).exists_isLeviFamily_leviAlt_leviBlk hJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
