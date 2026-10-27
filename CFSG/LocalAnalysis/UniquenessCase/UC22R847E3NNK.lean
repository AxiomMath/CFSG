module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229U3E9
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFrat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem R847E3.two_le_pRank_normalizer_inf_of_card {M Y F X : Subgroup G} {p q : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hYM : Y ≤ M) (hFM : F ≤ M)
    (hFN : F ≤ normalizer (Y : Set G)) (hFel : IsElemAbelian p F)
    (hFc : p ^ 2 * Nat.card ↥(F ⊓ Y) ≤ Nat.card F) (hqY : CFSG.Open.pRank q Y ≤ 1)
    (hXY : X ≤ Y) (hXc : Nat.card X = q) :
    2 ≤ CFSG.Open.pRank p (normalizer (X : Set G) ⊓ M) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup G, Q = Y ⊔ F := ⟨_, rfl⟩
  have hYQ : Y ≤ Q := hQ ▸ le_sup_left
  have hFQ : F ≤ Q := hQ ▸ le_sup_right
  have hQM : Q ≤ M := hQ ▸ sup_le hYM hFM
  have hQN : Q ≤ normalizer (Y : Set G) := hQ ▸ sup_le Subgroup.le_normalizer hFN
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
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hFel.isPGroup
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (hFel.mono (inf_le_left : F ⊓ Y ≤ F)).isPGroup
    have hjn : 2 + j ≤ n := by
      rw [hj, hn, ← pow_add] at hFc
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hFc
    have hk := Subgroup.card_ker_mul_card_range
      ((QuotientGroup.mk' (Y.subgroupOf Q)).comp (Subgroup.inclusion hFQ))
    rw [uc22r8100b_card_ker (K := Y) hFQ, hj, hn] at hk
    have hR : Nat.card ((QuotientGroup.mk' (Y.subgroupOf Q)).comp
        (Subgroup.inclusion hFQ)).range = p ^ (n - j) := by
      refine Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos j) ?_
      rw [hk, ← pow_add, Nat.add_sub_cancel' (by omega)]
    have hRel : IsElemAbelian p ((QuotientGroup.mk' (Y.subgroupOf Q)).comp
        (Subgroup.inclusion hFQ)).range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self F]
      exact (hFel.subgroupOf F).map _
    have := CFSG.SectionRank.le_pRank hp.one_lt le_top hRel hR
    omega
  obtain ⟨T, hTel, hTc⟩ := uc22ine229u3e9_exists_elemAbelian_sq _ hf hp hp2 hW
  refine CFSG.SectionRank.le_pRank hp.one_lt ?_ (hTel.map (normalizer (X : Set G) ⊓ Q).subtype)
    (by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hTc])
  rintro _ ⟨t, -, rfl⟩
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 t.2).1, hQM (Subgroup.mem_inf.1 t.2).2⟩

theorem R847E3.inf_eq_bot_of_not_le_normalizer {M Y E : Subgroup G} (hY : Y ∈ calC M)
    (hZ : center (Bar2 Y) = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hEM : E ≤ M)
    (hEel : IsElemAbelian p E) (hEN : ¬ E ≤ normalizer (Y : Set G)) : E ⊓ Y = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, heE, heN⟩ := SetLike.not_le_iff_exists.1 hEN
  have hY' : Y.map (MulAut.conj e).toMonoidHom ∈ calC M :=
    uc22p2214_calC_of_mem_conjSetOf hY ⟨e, hEM heE, rfl⟩
  have hne : Y ≠ Y.map (MulAut.conj e).toMonoidHom := fun h =>
    heN (Subgroup.mem_normalizer_iff_map_conj_eq.2 h.symm)
  have hZ' : center (Bar2 (Y.map (MulAut.conj e).toMonoidHom)) = ⊥ := by
    rw [← Subgroup.card_eq_one, UC6S846.card_center_bar2_map, hZ, Subgroup.card_bot]
  have hdis := IsPGroup.disjoint_of_ne p 2 hp2 E (pCoreOf 2 Y) hEel.isPGroup
    ((CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype)
  refine le_bot_iff.1 fun y hy => hdis.le_bot ⟨hy.1, ?_⟩
  have hyY' : y ∈ Y.map (MulAut.conj e).toMonoidHom := by
    refine ⟨y, hy.2, ?_⟩
    have hc : e * y = y * e := CFSG.Open.IsElemAbelian.comm hEel heE hy.1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc, mul_inv_cancel_right]
  exact (PartTwo.calC_inf_le_pCore_of_ne hY hY' hne hZ hZ' ⟨hy.2, hyY'⟩).1

omit [Finite G] in
theorem R847E3.exists_surjective_map_pPrimeCore_of_dvd {p r : ℕ}
    {H W : Subgroup G} (hWH : W ≤ H) {S : Type} [Group S] [IsSimpleGroup S] (π : ↥W →* S)
    (hπs : Function.Surjective π) (hrS : r ∣ Nat.card S)
    (hrH : ¬ r ∣ Nat.card (CFSG.pPrimeCore p ↥H)) :
    ∃ f : ↥((W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) →* S,
      Function.Surjective f := by
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
  have hrJ : ¬ r ∣ Nat.card J := fun h => hrH (h.trans
    (Subgroup.card_comap_dvd_of_injective I (Subgroup.inclusion hWH)
      (Subgroup.inclusion_injective hWH)))
  have : (J.map π).Normal := hJn.map π hπs
  have hker : ψ.ker ≤ π.ker := by
    have hψJ : ψ.ker = J := by
      ext x
      rw [MonoidHom.mem_ker, hJ, Subgroup.mem_comap, ← QuotientGroup.eq_one_iff,
        ← Subtype.coe_inj]
      rfl
    rw [hψJ]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.map π) with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).1 hbot
    · exfalso
      have hsurj : Function.Surjective (π.comp J.subtype) := by
        intro b
        have hb : b ∈ J.map π := by rw [htop]; trivial
        obtain ⟨j, hj, hjb⟩ := Subgroup.mem_map.1 hb
        exact ⟨⟨j, hj⟩, hjb⟩
      exact hrJ (hrS.trans (Subgroup.card_dvd_of_surjective hsurj))
  let f : ↥img →* S :=
    ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ) ⟨π, hker⟩
  have hfψ : ∀ x : ↥W, f (ψ x) = π x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨π, hker⟩ x
  refine ⟨f, fun b => ?_⟩
  obtain ⟨x, rfl⟩ := hπs b
  exact ⟨ψ x, hfψ x⟩

theorem R847E3.eq_five_of_kf7Use {D : Data G} (hKF7 : KF7Use D) {p : ℕ} (hp : p ∈ D.sig)
    {H W : Subgroup G} (hH : F07.Sec7Hyp D p H) (hWH : W ≤ H ⊓ D.M) {S : Type} [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S] (π : ↥W →* S) (hπ : Function.Surjective π) {r : ℕ}
    (hrS : r ∣ Nat.card S) (hrH : ¬ r ∣ Nat.card (CFSG.pPrimeCore p ↥H)) : p = 5 := by
  obtain ⟨f, hf⟩ :=
    R847E3.exists_surjective_map_pPrimeCore_of_dvd (hWH.trans inf_le_left) π hπ hrS hrH
  rcases hKF7 p hp H hH with hsolv | ⟨hp5, -⟩
  · have hle : (W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ≤
        ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) :=
      Subgroup.map_mono (Subgroup.comap_mono hWH)
    have : Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := hsolv
    have : Group.IsSolvable ↥((W.subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact absurd (solvable_of_surjective hf) (Group.IsPerfect.not_isSolvable S)
  · exact hp5

theorem R847E3.even_card_of_thin {X : Type} [Group X]
    (h : (∃ a : ℕ, IsL2 X a) ∨ (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ IsL2Odd X r) ∨ (∃ a : ℕ, IsSz X a) ∨
      IsJ1 X) : Even (Nat.card X) := by
  rcases h with ⟨a, h⟩ | ⟨r, hr, hr2, h⟩ | ⟨a, h⟩ | h
  · exact PartTwo.S19.even_card_of_isL2_or_isSz (Or.inl h)
  · have hc := KNL23.card_isL2Odd hr hr2 h
    obtain ⟨k, rfl⟩ := hr.odd_of_ne_two hr2
    have h4 : 4 ∣ Nat.card X * 2 := by
      rw [hc]
      exact Dvd.dvd.mul_left ⟨k * (k + 1), Nat.sub_eq_of_eq_add (by ring)⟩ _
    exact even_iff_two_dvd.2 (by omega)
  · exact PartTwo.S19.even_card_of_isL2_or_isSz (Or.inr h)
  · rw [KNL23.card_isJ1 h]
    exact ⟨87780, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
