module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229U3E9
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFrat
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddKF7
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction
import CFSG.GroupTheory.PerfectSylowInversion
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem R847E3.two_le_pRank_normalizer_inf {M Y E X : Subgroup G} {p q : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : q.Prime) (hYM : Y ≤ M) (hEM : E ≤ M) (hEN : E ≤ normalizer (Y : Set G))
    (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hpY : CFSG.Open.pRank p Y ≤ 1)
    (hqY : CFSG.Open.pRank q Y ≤ 1) (hXY : X ≤ Y) (hXc : Nat.card X = q) :
    2 ≤ CFSG.Open.pRank p (normalizer (X : Set G) ⊓ M) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup G, Q = Y ⊔ E := ⟨_, rfl⟩
  have hYQ : Y ≤ Q := hQ ▸ le_sup_left
  have hEQ : E ≤ Q := hQ ▸ le_sup_right
  have hQM : Q ≤ M := hQ ▸ sup_le hYM hEM
  have hQN : Q ≤ normalizer (Y : Set G) := hQ ▸ sup_le Subgroup.le_normalizer hEN
  have : (Y.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYQ).2 hQN
  have hTQ : normalizer (X : Set G) ⊓ Q ≤ Q := inf_le_right
  have hf : Function.Surjective
      ((QuotientGroup.mk' (Y.subgroupOf Q)).comp (Subgroup.inclusion hTQ)) := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H g =>
      have hXg : X.map (MulAut.conj (g : G)).toMonoidHom ≤ Y := by
        rintro _ ⟨x, hx, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 (hQN g.2) x).1 (hXY hx)
      obtain ⟨y, hy, hyg⟩ := exists_mem_map_conj_eq_of_card_eq_prime hqY hXY hXg hXc
        (by rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective, hXc])
      have hn : y⁻¹ * (g : G) ∈ normalizer (X : Set G) := by
        refine Subgroup.mem_normalizer_iff.2 fun h => ?_
        have h1 := SetLike.ext_iff.1 hyg ((g : G) * h * (g : G)⁻¹)
        rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
          MulAut.conj_symm_apply] at h1
        rw [show y⁻¹ * (g : G) * h * (y⁻¹ * (g : G))⁻¹ =
          y⁻¹ * ((g : G) * h * (g : G)⁻¹) * y by group, h1,
          show (g : G)⁻¹ * ((g : G) * h * (g : G)⁻¹) * (g : G) = h by group]
      have hyQ : y⁻¹ * (g : G) ∈ Q := Q.mul_mem (Q.inv_mem (hYQ hy)) g.2
      refine ⟨⟨y⁻¹ * (g : G), hn, hyQ⟩, ?_⟩
      have hincl : Subgroup.inclusion hTQ ⟨y⁻¹ * (g : G), hn, hyQ⟩ =
          (⟨y, hYQ hy⟩ : ↥Q)⁻¹ * g := Subtype.ext rfl
      have h1 : QuotientGroup.mk' (Y.subgroupOf Q) (⟨y, hYQ hy⟩ : ↥Q) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hy)
      change QuotientGroup.mk' (Y.subgroupOf Q) (Subgroup.inclusion hTQ _) =
        QuotientGroup.mk' (Y.subgroupOf Q) g
      rw [hincl, map_mul, map_inv, h1, inv_one, one_mul]
  have hW : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥Q ⧸ Y.subgroupOf Q)) := by
    have hEY : IsElemAbelian p (E ⊓ Y) := hEel.mono inf_le_left
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hEY.isPGroup
    have hj1 : j ≤ 1 := (CFSG.SectionRank.le_pRank hp.one_lt inf_le_right hEY hj).trans hpY
    have hk := Subgroup.card_ker_mul_card_range
      ((QuotientGroup.mk' (Y.subgroupOf Q)).comp (Subgroup.inclusion hEQ))
    rw [uc22r8100b_card_ker (K := Y) hEQ, hj, hEc] at hk
    have hR : Nat.card ((QuotientGroup.mk' (Y.subgroupOf Q)).comp
        (Subgroup.inclusion hEQ)).range = p ^ (3 - j) := by
      refine Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos j) ?_
      rw [hk, ← pow_add, Nat.add_sub_cancel' (by omega)]
    have hRel : IsElemAbelian p ((QuotientGroup.mk' (Y.subgroupOf Q)).comp
        (Subgroup.inclusion hEQ)).range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self E]
      exact (hEel.subgroupOf E).map _
    have := CFSG.SectionRank.le_pRank hp.one_lt le_top hRel hR
    omega
  obtain ⟨F, hFel, hFc⟩ := uc22ine229u3e9_exists_elemAbelian_sq _ hf hp hp2 hW
  refine CFSG.SectionRank.le_pRank hp.one_lt ?_ (hFel.map (normalizer (X : Set G) ⊓ Q).subtype)
    (by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hFc])
  rintro _ ⟨t, -, rfl⟩
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 t.2).1, hQM (Subgroup.mem_inf.1 t.2).2⟩

theorem R847E3.exists_le_normalizer_inf_surjective {M Y X : Subgroup G} (hY : Y ∈ calC M)
    (hYN : ¬ (Y.subgroupOf M).Normal) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hXY : X ≤ Y)
    (hXc : Nat.card X = q) :
    ∃ W : Subgroup G, W ≤ normalizer (X : Set G) ⊓ M ∧
      ∃ π : ↥W →* Bar2 Y, Function.Surjective π := by
  have : Fact q.Prime := ⟨hq⟩
  have hYM : Y ≤ M := hY.1.le
  have hXM : X ≤ M := hXY.trans hYM
  obtain ⟨m, hmM, hmN⟩ : ∃ m ∈ M, m ∉ normalizer (Y : Set G) := by
    by_contra h
    push Not at h
    exact hYN ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 h)
  have hY' : Y.map (MulAut.conj m).toMonoidHom ∈ calC M :=
    uc22p2214_calC_of_mem_conjSetOf hY ⟨m, hmM, rfl⟩
  have hne : Y ≠ Y.map (MulAut.conj m).toMonoidHom := fun h =>
    hmN (Subgroup.mem_normalizer_iff_map_conj_eq.2 h.symm)
  have hNq : ¬ q ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  have hAq : IsPGroup q (X.subgroupOf M) := IsPGroup.of_card (n := 1)
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv).trans (hXc.trans (pow_one q).symm))
  have hlift : ∀ y : ↥M, (y : G) ∈ Y.map (MulAut.conj m).toMonoidHom →
      ∃ s ∈ normalizer ((X.subgroupOf M : Subgroup ↥M) : Set ↥M),
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) s = QuotientGroup.mk' (CFSG.pCore 2 ↥M) y := by
    intro y hy
    refine CFSG.GroupTheory.exists_mem_normalizer_mk'_eq (CFSG.pCore 2 ↥M) hNq hAq
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_))
    rintro _ ⟨a, ha, rfl⟩
    have hc : (a : G) * y * (a : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 M :=
      uc22ine229_commutator_mem_of_ne hY hY' hne (hXY (Subgroup.mem_subgroupOf.1 ha)) hy
    have hc' : a * y * a⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥M :=
      (Subgroup.mem_map_iff_mem M.subtype_injective).1 hc
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (a * y * a⁻¹ * y⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hc'
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  set Yb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
    ((Y.map (MulAut.conj m).toMonoidHom).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    with hYb
  set W0 : Subgroup ↥M := normalizer ((X.subgroupOf M : Subgroup ↥M) : Set ↥M) ⊓
    Yb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) with hW0
  let ψ : ↥W0 →* ↥Yb := ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp W0.subtype).codRestrict Yb
    fun w => (Subgroup.mem_inf.1 w.2).2
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨s, hs, hsy⟩ := hlift y (Subgroup.mem_subgroupOf.1 hy)
    have hsW : s ∈ W0 := Subgroup.mem_inf.2 ⟨hs, by
      rw [Subgroup.mem_comap, hsy]
      exact Subgroup.mem_map_of_mem _ hy⟩
    exact ⟨⟨s, hsW⟩, Subtype.ext hsy⟩
  obtain ⟨e₁, -⟩ := uc22p20d_bar2Equiv hY'.1.le hY'.1
  let e₀ : ↥Y ≃* ↥(Y.map (MulAut.conj m).toMonoidHom) :=
    Y.equivMapOfInjective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective
  let e₂ : Bar2 Y ≃* Bar2 (Y.map (MulAut.conj m).toMonoidHom) :=
    QuotientGroup.congr (CFSG.pCore 2 ↥Y) (CFSG.pCore 2 ↥(Y.map (MulAut.conj m).toMonoidHom)) e₀
      (CFSG.pCore_map_iso 2 e₀)
  let e₃ : ↥W0 ≃* ↥(W0.map M.subtype) := W0.equivMapOfInjective M.subtype M.subtype_injective
  refine ⟨W0.map M.subtype, ?_, ((e₂.symm.toMonoidHom.comp e₁.symm.toMonoidHom).comp ψ).comp
    e₃.symm.toMonoidHom, ((e₂.symm.surjective.comp e₁.symm.surjective).comp hψ).comp
    e₃.symm.surjective⟩
  rintro _ ⟨w, hw, rfl⟩
  have hwN : w ∈ (normalizer (X : Set G)).subgroupOf M := by
    rw [Subgroup.subgroupOf_normalizer_eq hXM]
    exact (Subgroup.mem_inf.1 hw).1
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hwN, w.2⟩

theorem R847E3.exists_surjective_map_pPrimeCore {p : ℕ} (hp : p.Prime) {H W : Subgroup G}
    (hWH : W ≤ H) {S : Type} [Group S] [IsSimpleGroup S] (π : ↥W →* S)
    (hπs : Function.Surjective π) (hpS : p ∣ Nat.card S) :
    ∃ f : ↥((W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) →* S,
      Function.Surjective f := by
  have : Fact p.Prime := ⟨hp⟩
  set I : Subgroup ↥H := CFSG.pPrimeCore p ↥H with hI
  set img := (W.subgroupOf H).map (QuotientGroup.mk' I) with himg
  have hIn : I.Normal := CFSG.pPrimeCore_normal
  have hmem : ∀ x : ↥W, (QuotientGroup.mk' I) (Subgroup.inclusion hWH x) ∈ img := fun x =>
    Subgroup.mem_map.2 ⟨Subgroup.inclusion hWH x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  let ψ : ↥W →* ↥img :=
    ((QuotientGroup.mk' I).comp (Subgroup.inclusion hWH)).codRestrict img hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, Subtype.ext rfl⟩
  set J : Subgroup ↥W := I.comap (Subgroup.inclusion hWH) with hJ
  have hJn : J.Normal := hIn.comap _
  have hJcard : Nat.card J ∣ Nat.card I :=
    Subgroup.card_comap_dvd_of_injective I (Subgroup.inclusion hWH)
      (Subgroup.inclusion_injective hWH)
  have hpI : ¬ p ∣ Nat.card I :=
    (hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p))
  have : (J.map π).Normal := hJn.map π hπs
  have hker : ψ.ker ≤ π.ker := by
    have hψJ : ψ.ker = J := by
      ext x
      rw [MonoidHom.mem_ker, hJ, Subgroup.mem_comap, ← QuotientGroup.eq_one_iff,
        ← Subtype.coe_inj]
      rfl
    rw [hψJ]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.map π) with hbot | htop
    · intro x hx
      have : π x ∈ J.map π := Subgroup.mem_map_of_mem π hx
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      have hsurj : Function.Surjective (π.comp J.subtype) := by
        intro b
        have hb : b ∈ J.map π := by rw [htop]; trivial
        obtain ⟨j, hj, hjb⟩ := Subgroup.mem_map.1 hb
        exact ⟨⟨j, hj⟩, hjb⟩
      exact hpI (hpS.trans ((Subgroup.card_dvd_of_surjective hsurj).trans hJcard))
  let f : ↥img →* S :=
    ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ) ⟨π, hker⟩
  have hfψ : ∀ x : ↥W, f (ψ x) = π x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨π, hker⟩ x
  refine ⟨f, fun b => ?_⟩
  obtain ⟨x, rfl⟩ := hπs b
  exact ⟨ψ x, hfψ x⟩

theorem R847E3.isAlt_of_kf7Use {D : Data G} (hKF7 : KF7Use D) {p : ℕ} (hp : p ∈ D.sig)
    {H W : Subgroup G} (hH : F07.Sec7Hyp D p H) (hWH : W ≤ H ⊓ D.M) {S : Type} [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S] (π : ↥W →* S) (hπ : Function.Surjective π)
    (hpS : p ∣ Nat.card S) : p = 5 ∧ IsAlt S 5 := by
  obtain ⟨f, hf⟩ :=
    R847E3.exists_surjective_map_pPrimeCore hH.1 (hWH.trans inf_le_left) π hπ hpS
  have hle : (W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ≤
      ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) :=
    Subgroup.map_mono (Subgroup.comap_mono hWH)
  rcases hKF7 p hp H hH with hsolv | ⟨hp5, hquot⟩
  · have : Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := hsolv
    have : Group.IsSolvable ↥((W.subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact absurd (solvable_of_surjective hf) (Group.IsPerfect.not_isSolvable S)
  · obtain ⟨P, hPperf, hPmap⟩ := PartOne.Section9.exists_perfect_map_eq_top f hf
    let N := (W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    let e := P.equivMapOfInjective N.subtype N.subtype_injective
    refine ⟨hp5, hquot (P.map N.subtype) ((Subgroup.map_subtype_le P).trans hle) ?_ _
      inferInstance ((f.comp P.subtype).comp e.symm.toMonoidHom) ?_⟩
    · rw [← Subgroup.map_commutator, hPperf]
    · intro s
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 (hPmap ▸ Subgroup.mem_top s)
      exact ⟨e ⟨a, ha⟩, by simp⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
