module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
import CFSG.GroupTheory.PElementSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Opp R72Shape)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (Sec7Hyp QuotK7 ImageModK LKQuot7 IsReeType)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded pElementSubgroup)

variable {G : Type} [Group G] [Finite G]

private theorem pElementSubgroup_top_normal {X : Type} [Group X] (p : ℕ) :
    (pElementSubgroup p (⊤ : Subgroup X)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hle : (pElementSubgroup p (⊤ : Subgroup X)).map (MulAut.conj g).toMonoidHom ≤
      pElementSubgroup p ⊤ := by
    unfold pElementSubgroup
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, ⟨-, j, hj⟩, rfl⟩
    exact ⟨Subgroup.mem_top _, j, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hj]⟩
  exact hle ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem imageModK_opp_eq_pElementSubgroup {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    ImageModK p H (Opp p H) = pElementSubgroup p (⊤ : Subgroup (QuotK7 p H)) := by
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    ext x
    exact ⟨fun hx => (Subgroup.mem_map.mp hx).elim fun y hy => hy.2 ▸ y.2,
      fun hx => Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩⟩
  have hmap : pElementSubgroup p H = (pElementSubgroup p (⊤ : Subgroup ↥H)).map H.subtype := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map hp H.subtype ⊤, htop]
  have hsub : (pElementSubgroup p H).subgroupOf H = pElementSubgroup p (⊤ : Subgroup ↥H) := by
    rw [hmap, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  unfold ImageModK Opp
  rw [hsub]
  refine (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map hp
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ⊤).trans ?_
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem config_of_sec7Hyp (k : Sec7Core4 G) {D : Data G} {H : Subgroup G}
    (h7 : Sec7Hyp D k.p H) (hM : k.M = D.M) : k.Config H := by
  obtain ⟨-, -, -, hne, hnle, hrank⟩ := h7
  refine ⟨hne, ?_, ?_⟩
  · rw [hM]
    exact hnle
  · rw [hM]
    exact hrank

theorem generalizedFitting_le_imageModK (k : Sec7Core4 G) {H : Subgroup G} (hH : k.Config H) :
    CFSG.generalizedFitting (QuotK7 k.p H) ≤ ImageModK k.p H (Opp k.p H) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  rw [imageModK_opp_eq_pElementSubgroup k.prime H]
  obtain ⟨hs, -, -, -⟩ := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI := hs
  haveI : (pElementSubgroup k.p (⊤ : Subgroup (QuotK7 k.p H))).Normal :=
    pElementSubgroup_top_normal k.p
  obtain ⟨z, hz⟩ :=
    exists_prime_orderOf_dvd_card' k.p (k.dvd_card_generalizedFitting_quotient hH)
  have hzP : z ∈ (pElementSubgroup k.p (⊤ : Subgroup (QuotK7 k.p H))).subgroupOf
      (CFSG.generalizedFitting (QuotK7 k.p H)) :=
    Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure
      ⟨Subgroup.mem_top _, 1, by rw [Subgroup.orderOf_coe, hz, pow_one]⟩)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((pElementSubgroup k.p
      (⊤ : Subgroup (QuotK7 k.p H))).subgroupOf (CFSG.generalizedFitting (QuotK7 k.p H)))
    with h | h
  · rw [h, Subgroup.mem_bot] at hzP
    rw [hzP, orderOf_one] at hz
    exact absurd hz k.prime.one_lt.ne
  · exact Subgroup.subgroupOf_eq_top.1 h

theorem genFittingFStar_le_imageModK (k : Sec7Core4 G) {H : Subgroup G} (hH : k.Config H) :
    CFSG.Open.genFittingFStar (QuotK7 k.p H) ≤ ImageModK k.p H (Opp k.p H) := by
  rw [CFSG.Adapters.genFittingFStar_eq_foundations]
  exact generalizedFitting_le_imageModK k hH

theorem forall_pow_mem_of_forall_mem_N (k : Sec7Core4 G) {H : Subgroup G} (hH : k.Config H)
    (h : ∀ z ∈ ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)),
      IsPGroup k.p (Subgroup.zpowers z) → z ∈ CFSG.generalizedFitting (QuotK7 k.p H)) :
    ∀ (x : QuotK7 k.p H) (n : ℕ), x ^ k.p ^ n = 1 →
      x ∈ CFSG.generalizedFitting (QuotK7 k.p H) := by
  intro x n hx
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨-, -, hFn, -⟩ := k.isSimpleGroup_generalizedFitting_quotient hH
  have hzp : ∀ y : QuotK7 k.p H, y ^ k.p ^ n = 1 → IsPGroup k.p (Subgroup.zpowers y) := by
    intro y hy
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow k.prime).1 (orderOf_dvd_of_pow_eq_one hy)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  obtain ⟨P, hP⟩ := (hzp x hx).exists_le_sylow
  obtain ⟨g, hg⟩ := (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH).exists_conj_ge
    (P := (P : Subgroup (QuotK7 k.p H)))
    ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  have hgx := CFSG.RankThree.PartOne.StrongP.mem_conjSub_iff.mp
    (hg (hP (Subgroup.mem_zpowers x)))
  have hpow : (g⁻¹ * x * g) ^ k.p ^ n = 1 := by
    have he : g⁻¹ * x * g = MulAut.conj g⁻¹ x := by simp [MulAut.conj_apply]
    rw [he, ← map_pow, hx, map_one]
  have hF := hFn.conj_mem _ (h _ hgx (hzp _ hpow)) g
  have he : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [he] at hF

theorem imageModK_opp_eq_generalizedFitting (k : Sec7Core4 G) {H : Subgroup G}
    (hH : k.Config H)
    (h : ∀ (x : QuotK7 k.p H) (n : ℕ), x ^ k.p ^ n = 1 →
      x ∈ CFSG.generalizedFitting (QuotK7 k.p H)) :
    ImageModK k.p H (Opp k.p H) = CFSG.generalizedFitting (QuotK7 k.p H) := by
  refine le_antisymm ?_ (generalizedFitting_le_imageModK k hH)
  rw [imageModK_opp_eq_pElementSubgroup k.prime H]
  unfold pElementSubgroup
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨-, j, hj⟩
  exact h x j (by rw [← hj]; exact pow_orderOf_eq_one x)

theorem imageModK_opp_eq_top (k : Sec7Core4 G) {H : Subgroup G} (hH : k.Config H)
    (h : ∃ n : ℕ, (CFSG.generalizedFitting (QuotK7 k.p H)).index = k.p ^ n) :
    ImageModK k.p H (Opp k.p H) = ⊤ := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨n, hn⟩ := h
  obtain ⟨S⟩ : Nonempty (Sylow k.p (QuotK7 k.p H)) := inferInstance
  have hS : (S : Subgroup (QuotK7 k.p H)) ≤ ImageModK k.p H (Opp k.p H) := by
    rw [imageModK_opp_eq_pElementSubgroup k.prime H]
    exact CFSG.le_pElementSubgroup_of_isPGroup k.prime S.isPGroup' le_top
  have h1 : (ImageModK k.p H (Opp k.p H)).index ∣ k.p ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_of_le (generalizedFitting_le_imageModK k hH)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow k.prime).1 h1
  rcases j with _ | j
  · exact Subgroup.index_eq_one.mp (by simpa using hj)
  · have h2 : k.p ^ (j + 1) ∣ (S : Subgroup (QuotK7 k.p H)).index := by
      rw [← hj]
      exact Subgroup.index_dvd_of_le hS
    exact absurd ((dvd_pow_self k.p (Nat.succ_ne_zero j)).trans h2) S.not_dvd_index

theorem isReeType_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {f : ℕ}
    (h : IsReeType X f) : IsReeType Y f := by
  obtain ⟨hodd, hS, t, ht, F, iF, iFt, hF, ⟨φ⟩⟩ := h
  have hC : (Subgroup.centralizer ({t} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e t} : Set Y) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      simpa using congrArg e hy
    · intro hy
      simpa using congrArg e.symm hy
  refine ⟨hodd, fun S => ?_, e t, by rw [MulEquiv.orderOf_eq, ht], F, iF, iFt, hF,
    ⟨((MulEquiv.subgroupCongr hC).symm.trans
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).symm).trans φ⟩⟩
  have hc : IsMulCommutative ↥((S : Subgroup Y).comap e.toMonoidHom) :=
    hS (S.comapOfInjective e.toMonoidHom e.injective
      (le_top.trans (MonoidHom.range_eq_top.mpr e.surjective).ge))
  rw [isMulCommutative_iff] at hc ⊢
  intro a b
  have hmem : ∀ y : ↥(S : Subgroup Y), e.symm (y : Y) ∈ (S : Subgroup Y).comap e.toMonoidHom :=
    fun y => by simp
  have hab : e.symm (a : Y) * e.symm (b : Y) = e.symm (b : Y) * e.symm (a : Y) :=
    congrArg Subtype.val (hc ⟨_, hmem a⟩ ⟨_, hmem b⟩)
  have h' := congrArg e hab
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h')

theorem r72Shape_of_mulEquiv {p : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : R72Shape p X) : R72Shape p Y := by
  have hS : ∀ s : TauCeti.SporadicName, UC22.IsSpor X s → UC22.IsSpor Y s := by
    intro s hs
    obtain ⟨φ⟩ := hs
    exact ⟨e.symm.trans φ⟩
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨hp, h | h | h⟩ | ⟨hp, h | h | h | h⟩ | ⟨hp, h⟩
  · exact Or.inl ⟨n, h.of_mulEquiv e⟩
  · exact Or.inr (Or.inl ⟨n, h.of_mulEquiv e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hp, Or.inl (isReeType_of_mulEquiv e h)⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inl (hS _ h))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inr
      (CFSG.Blueprint.LieModel.of_mulEquiv e h))⟩))
  · obtain ⟨S, iS, hSz, ⟨φ⟩⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inl ⟨S, iS, hSz, ⟨e.symm.trans φ⟩⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inl (h.of_mulEquiv e))⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inr (Or.inl (hS _ h)))⟩)))
  · obtain ⟨φ⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inr (Or.inr ⟨e.symm.trans φ⟩))⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, hS _ h⟩)))

theorem r72Shape_lkQuot7_of_eq {p : ℕ} {H : Subgroup G} {L : Subgroup (QuotK7 p H)}
    (hL : ImageModK p H (Opp p H) = L) (h : R72Shape p ↥L) : R72Shape p (LKQuot7 p H) :=
  r72Shape_of_mulEquiv (MulEquiv.subgroupCongr hL).symm h

theorem r72Shape_lkQuot7_of_eq_top {p : ℕ} {H : Subgroup G}
    (hL : ImageModK p H (Opp p H) = ⊤) (h : R72Shape p (QuotK7 p H)) :
    R72Shape p (LKQuot7 p H) :=
  r72Shape_lkQuot7_of_eq hL (r72Shape_of_mulEquiv Subgroup.topEquiv.symm h)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
