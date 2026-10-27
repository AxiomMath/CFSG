module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R1111 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, F11.Hyp11 D V₀ V →
    ∀ [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal],
    ∀ p ∈ D.sig, pRank p D.M ≤ pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) + 2 ∧
      1 ≤ pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V))

private theorem s15_Thirteen_fix_of_stab {U : Type} [CommGroup U] [Finite U]
    {W : Subgroup U} (hcard : Nat.card W = 4) {φ : MulAut U} (hφW : φ ∈ stabSub W)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hord : orderOf φ = p) :
    W ≤ fixV (Subgroup.zpowers φ) := by
  intro w hw
  rw [mem_fixV_zpowers]
  by_contra hne
  have hHle : Subgroup.zpowers φ ≤ stabSub W := Subgroup.zpowers_le.mpr hφW
  have hHcard : Nat.card (Subgroup.zpowers φ) = p := by rw [Nat.card_zpowers, hord]
  have hwO : w ∈ MulAction.orbit (Subgroup.zpowers φ) w := ⟨1, one_smul _ _⟩
  have hφwO : φ • w ∈ MulAction.orbit (Subgroup.zpowers φ) w :=
    ⟨⟨φ, Subgroup.mem_zpowers φ⟩, rfl⟩
  have hne' : w ≠ φ • w := by
    intro h
    apply hne
    have h' : φ • w = w := h.symm
    rwa [MulAut.smul_def] at h'
  have hOgt : 1 < (MulAction.orbit (Subgroup.zpowers φ) w).ncard := by
    have hsub : ({w, φ • w} : Set U) ⊆ MulAction.orbit (Subgroup.zpowers φ) w := by
      intro x hx
      rcases hx with rfl | rfl
      · exact hwO
      · exact hφwO
    have h2 : ({w, φ • w} : Set U).ncard = 2 := Set.ncard_pair hne'
    have := Set.ncard_le_ncard hsub
    rw [h2] at this
    omega
  have hidx : (MulAction.stabilizer (Subgroup.zpowers φ) w).index =
      (MulAction.orbit (Subgroup.zpowers φ) w).ncard := MulAction.index_stabilizer _ _
  have hdvd : (MulAction.orbit (Subgroup.zpowers φ) w).ncard ∣ p := by
    rw [← hidx, ← hHcard]
    exact ⟨Nat.card (MulAction.stabilizer (Subgroup.zpowers φ) w),
      (Subgroup.index_mul_card (H := MulAction.stabilizer (Subgroup.zpowers φ) w)).symm⟩
  have hOeq : (MulAction.orbit (Subgroup.zpowers φ) w).ncard = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · omega
    · exact h
  have hOsub : MulAction.orbit (Subgroup.zpowers φ) w ⊆ (W : Set U) := by
    rintro x ⟨h, rfl⟩
    have hh : (h : MulAut U) ∈ stabSub W := hHle h.2
    exact (mem_stabSub.mp hh w).2 hw
  have hle : p ≤ Nat.card W := by
    calc p = (MulAction.orbit (Subgroup.zpowers φ) w).ncard := hOeq.symm
      _ ≤ (W : Set U).ncard := Set.ncard_le_ncard hOsub
      _ = Nat.card W := by rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  omega

private theorem s15_Thirteen_prime_le_ncard {U : Type} [CommGroup U] [Finite U]
    {Y : Set (Subgroup U)} (hsup : sSup Y = ⊤) (hcard : ∀ W ∈ Y, Nat.card W = 4)
    {X : Subgroup (MulAut U)}
    (hperm : ∀ ψ ∈ X, ∀ W ∈ Y, W.map ψ.toMonoidHom ∈ Y)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {φ : MulAut U} (hφX : φ ∈ X)
    (hord : orderOf φ = p) (hφ1 : φ ≠ 1) : p ≤ Y.ncard := by
  by_cases hcase : ∃ W ∈ Y, W.map φ.toMonoidHom ≠ W
  · obtain ⟨W, hW, hWne⟩ := hcase
    have hHle : Subgroup.zpowers φ ≤ X := Subgroup.zpowers_le.mpr hφX
    have hHcard : Nat.card (Subgroup.zpowers φ) = p := by rw [Nat.card_zpowers, hord]
    have hWO : W ∈ MulAction.orbit (Subgroup.zpowers φ) W := ⟨1, one_smul _ _⟩
    have hφWO : φ • W ∈ MulAction.orbit (Subgroup.zpowers φ) W :=
      ⟨⟨φ, Subgroup.mem_zpowers φ⟩, rfl⟩
    have hne' : W ≠ φ • W := by
      intro h
      rw [Subgroup.pointwise_smul_def] at h
      exact hWne h.symm
    have hOgt : 1 < (MulAction.orbit (Subgroup.zpowers φ) W).ncard := by
      have hsub : ({W, φ • W} : Set (Subgroup U)) ⊆
          MulAction.orbit (Subgroup.zpowers φ) W := by
        intro x hx
        rcases hx with rfl | rfl
        · exact hWO
        · exact hφWO
      have h2 : ({W, φ • W} : Set (Subgroup U)).ncard = 2 := Set.ncard_pair hne'
      have := Set.ncard_le_ncard hsub
      rw [h2] at this
      omega
    have hidx : (MulAction.stabilizer (Subgroup.zpowers φ) W).index =
        (MulAction.orbit (Subgroup.zpowers φ) W).ncard := MulAction.index_stabilizer _ _
    have hdvd : (MulAction.orbit (Subgroup.zpowers φ) W).ncard ∣ p := by
      rw [← hidx, ← hHcard]
      exact ⟨Nat.card (MulAction.stabilizer (Subgroup.zpowers φ) W),
        (Subgroup.index_mul_card (H := MulAction.stabilizer (Subgroup.zpowers φ) W)).symm⟩
    have hOeq : (MulAction.orbit (Subgroup.zpowers φ) W).ncard = p := by
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · omega
      · exact h
    have hOsub : MulAction.orbit (Subgroup.zpowers φ) W ⊆ Y := by
      rintro Z ⟨h, rfl⟩
      exact hperm (h : MulAut U) (hHle h.2) W hW
    calc p = (MulAction.orbit (Subgroup.zpowers φ) W).ncard := hOeq.symm
      _ ≤ Y.ncard := Set.ncard_le_ncard hOsub
  · push Not at hcase
    exfalso
    apply hφ1
    refine MulEquiv.ext fun u => ?_
    have hfix : sSup Y ≤ fixV (Subgroup.zpowers φ) :=
      sSup_le fun W hW => s15_Thirteen_fix_of_stab (hcard W hW) (by
        rw [mem_stabSub]
        intro v
        constructor
        · intro hv
          obtain ⟨x, hx, hxv⟩ := Subgroup.mem_map.1 (by rw [hcase W hW]; exact hv)
          rwa [φ.injective hxv] at hx
        · intro hv
          rw [← hcase W hW]
          exact Subgroup.mem_map.2 ⟨v, hv, rfl⟩) hp hp5 hord
    have htop : fixV (Subgroup.zpowers φ) = ⊤ := le_antisymm le_top (hsup ▸ hfix)
    have hu : u ∈ fixV (Subgroup.zpowers φ) := by rw [htop]; exact Subgroup.mem_top u
    simpa using (mem_fixV.mp hu φ (Subgroup.mem_zpowers φ))


private noncomputable def psiStar13 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) : ↥D.M →* MulAut (vStar D.M V₀ V hV L) :=
  (actTil (v1Sub D.M V₀ V hV L) V hV).comp
    (Subgroup.inclusion (le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV)))

private theorem psiStar13_range (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) :
    (psiStar13 D h hV).range = Mbar D.M (v1Sub D.M V₀ V hV L) V hV := by
  ext φ
  rw [MonoidHom.mem_range, Mbar, mem_barSub]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨_, m.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨(g : G), hg⟩, ?_⟩
    change actTil (v1Sub D.M V₀ V hV L) V hV
      (Subgroup.inclusion _ ⟨(g : G), hg⟩) = actTil (v1Sub D.M V₀ V hV L) V hV g
    exact congrArg _ (Subtype.ext rfl)

private theorem psiStar13_ker (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) :
    (psiStar13 D h hV).ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf D.M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    mem_cTilde_iff hV h.hyp151.hyp125.pairFacts.le_normalizer]
  constructor
  · intro hm
    refine ⟨m.2, le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV) m.2, ?_⟩
    change psiStar13 D h hV m = 1
    exact hm
  · rintro ⟨-, hstab, hact⟩
    show psiStar13 D h hV m = 1
    change actTil (v1Sub D.M V₀ V hV L) V hV (Subgroup.inclusion _ m) = 1
    rw [show Subgroup.inclusion _ m = (⟨(m : G), hstab⟩ :
      stabTil (v1Sub D.M V₀ V hV L) V) from Subtype.ext rfl]
    exact hact

private noncomputable def psiBarStar13 (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) :
    ↥D.M →* ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
  (psiStar13 D h hV).codRestrict _ fun m => by
    rw [← psiStar13_range D h hV]
    exact MonoidHom.mem_range.2 ⟨m, rfl⟩

private theorem psiBarStar13_surjective (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) :
    Function.Surjective (psiBarStar13 D h hV) := by
  intro y
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 (by
    rw [psiStar13_range D h hV]
    exact y.2)
  exact ⟨m, Subtype.ext (by simpa [psiBarStar13] using hm)⟩

private theorem psiBarStar13_ker (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) :
    (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf D.M = (psiBarStar13 D h hV).ker := by
  simp only [psiBarStar13]
  rw [MonoidHom.ker_codRestrict]
  exact (psiStar13_ker D h hV).symm

private noncomputable def phi13 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (h1217 : R1217 D)
    [hN : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    F11.MBar11 D.M V₀ V ≃* ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
  QuotientGroup.liftEquiv ((F11.CTilde D.M V₀ V).subgroupOf D.M)
    (psiBarStar13_surjective D h hV)
    (by
      rw [← fifteen_two_cent D h1217 h.hyp151 hV]
      exact psiBarStar13_ker D h hV)

private theorem openPRank_map_mulEquiv13 {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (p : ℕ) (H : Subgroup X) :
    CFSG.Open.pRank p (H.map e.toMonoidHom) = CFSG.Open.pRank p H := by
  have h1 := CFSG.pRank_congr_of_mulEquiv
    (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective) p
  simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h1
  exact h1.symm

theorem s15_Thirteen_k_cases (D : Data G) : D.k = 1 ∨ D.k = 2 := by
  unfold Data.k RankThreeUC.kParam
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem s15_Thirteen_k_eq_one_of_three_mem (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h3 : 3 ∈ D.sig) : D.k = 1 := by
  have hsp := hSg.sig1_sp 3 (h1219 ▸ h3)
  unfold Data.k RankThreeUC.kParam
  rw [if_pos hsp]

theorem s15_Thirteen_mbar_primes (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal]
    (hγ : gamma15 D.M V₀ V hV L = 2) (hs : s15 D.M V₀ V hV L ≤ 6) {p : ℕ} (hp : p.Prime)
    (hpM : 1 ≤ pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V))) :
    p = 2 ∨ p = 3 ∨ (p = 5 ∧ 5 ≤ s15 D.M V₀ V hV L) := by
  by_cases h23 : p = 2 ∨ p = 3
  · rcases h23 with h2 | h3
    · exact Or.inl h2
    · exact Or.inr (Or.inl h3)
  · right; right
    have h2 : p ≠ 2 := fun hh => h23 (Or.inl hh)
    have h3 : p ≠ 3 := fun hh => h23 (Or.inr hh)
    have hp5 : 5 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      have hodd : ∃ k, p = 2 * k + 1 := by
        rcases hp.eq_two_or_odd' with h | h
        · exact absurd h h2
        · exact h
      clear hp h2
      rcases hodd with ⟨k, hk⟩
      omega
    have hmap : (⊤ : Subgroup (F11.MBar11 D.M V₀ V)).map
          (phi13 D h hV h1217).toMonoidHom =
        (⊤ : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (phi13 D h hV h1217).surjective
    have hrank_eq : CFSG.Open.pRank p
          (⊤ : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) =
        CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := by
      rw [← hmap]
      exact openPRank_map_mulEquiv13 (phi13 D h hV h1217) p
        (⊤ : Subgroup (F11.MBar11 D.M V₀ V))
    have hpM' : 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank p
        (⊤ : Subgroup (F11.MBar11 D.M V₀ V))]
      exact hpM
    have hp1 : 1 ≤ CFSG.Open.pRank p
        (⊤ : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) := by
      rw [hrank_eq]
      exact hpM'
    obtain ⟨E, -, hEel, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt
        (⊤ : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV))
    have hEp : p ≤ Nat.card E := by
      rw [hEcard]
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ CFSG.Open.pRank p
              (⊤ : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) :=
            Nat.pow_le_pow_right hp.pos hp1
    have hEne : E ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hEp
      have := hp.two_le
      omega
    obtain ⟨e, heE, he1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left hEne
    have hord_e : orderOf (e : MulAut (vStar D.M V₀ V hV L)) = p := by
      haveI : Fact p.Prime := ⟨hp⟩
      rw [orderOf_coe]
      exact orderOf_eq_prime (hEel.2 e heE) he1
    obtain ⟨-, hsup⟩ := fifteen_two_directSum D h1217 h.hyp151 hV hL
    have hsq : ∀ a : vStar D.M V₀ V hV L, a * a = 1 := fun a => by
      rw [← pow_two]
      exact s15_Infra_vtil_sq_eq_one _ V hV a
    have hpg : ∀ Z : Subgroup (vStar D.M V₀ V hV L), IsPGroup 2 Z := fun Z =>
      isPGroup_two_of_sq_eq_one fun a => Subtype.ext (by simpa [pow_two] using hsq a.1)
    have hcard : ∀ Z ∈ wStarConj D.M V₀ V hV L, Nat.card Z = 4 := fun Z hZ => by
      rw [card_eq_two_pow_mSub (hpg Z)]
      show 2 ^ rk ↥Z = 4
      rw [s15_Two_rk_wStarConj h.hyp151 hV hZ, hγ]
      norm_num
    have hperm : ∀ ψ ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV,
        ∀ Z ∈ wStarConj D.M V₀ V hV L, Z.map ψ.toMonoidHom ∈ wStarConj D.M V₀ V hV L :=
      fun ψ hψ Z hZ => s15_Six_map_mem_wStarConj (L := L) h.hyp151.hyp125 hV hψ hZ
    have hps : p ≤ s15 D.M V₀ V hV L := by
      have hle := s15_Thirteen_prime_le_ncard hsup hcard hperm hp hp5 e.2 hord_e
        (fun h1 => he1 (Subtype.ext h1))
      rwa [ncard_wStarConj D h.hyp151 hV] at hle
    have hp_eq : p = 5 := by
      have hp_le6 : p ≤ 6 := le_trans hps hs
      have hp_lt6 : p < 6 := lt_of_le_of_ne hp_le6 (by rintro rfl; norm_num at hp)
      exact le_antisymm (Nat.lt_succ_iff.mp hp_lt6) hp5
    exact ⟨hp_eq, by omega⟩

theorem s15_Thirteen_gamma_two (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1217 : R1217 D) (h1110 : R1110G D) (h1111 : R1111 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hγ : gamma15 D.M V₀ V hV L = 2) :
    D.k = 1 ∨ (5 ∈ D.sig ∧ (s15 D.M V₀ V hV L = 5 ∨ s15 D.M V₀ V hV L = 6)) := by
  by_cases h7 : 7 ≤ s15 D.M V₀ V hV L
  · exact Or.inl (s15_Thirteen_k_of_large_s D hSg h1219 h1217 h1110 h127 h hV hL hγ h7)
  · by_cases h3 : 3 ∈ D.sig
    · exact Or.inl (s15_Thirteen_k_eq_one_of_three_mem D hSg h1219 h3)
    · right
      obtain ⟨p, hp⟩ := hSg.nonempty
      have hpp := D.sig_prime p hp
      have hpf := h.hyp151.hyp125.pairFacts
      haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
        WeakClosure81.cTilde_subgroupOf_normal hV hpf.le_normalizer hpf.le_normalizer₀
      have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp151.hyp125
      obtain ⟨-, h1p⟩ := h1111 V₀ V hH11 p hp
      rcases s15_Thirteen_mbar_primes D h1217 h hV hL hγ (by omega) hpp.1 h1p with
        h2 | h3' | ⟨h5, hs5⟩
      · exact absurd h2 hpp.2
      · exact absurd (h3' ▸ hp) h3
      · exact ⟨h5 ▸ hp, by omega⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
