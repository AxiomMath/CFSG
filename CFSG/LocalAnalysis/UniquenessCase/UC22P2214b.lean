module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.U3Rank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2214_eq_one_of_central {X : Type*} [Group X] (hX : commutator X = ⊤) (σ : MulAut X)
    (h : ∀ x : X, σ x * x⁻¹ ∈ center X) : σ = 1 := by
  let f : X →* center X :=
    { toFun := fun x => ⟨σ x * x⁻¹, h x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hy := Subgroup.mem_center_iff.1 (h y) x
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc σ x * σ y * (y⁻¹ * x⁻¹) = σ x * x⁻¹ * (x * (σ y * y⁻¹) * x⁻¹) := by group
          _ = σ x * x⁻¹ * (σ y * y⁻¹ * x * x⁻¹) := by rw [hy]
          _ = σ x * x⁻¹ * (σ y * y⁻¹) := by group }
  have hker : commutator X ≤ f.ker := Abelianization.commutator_subset_ker f
  ext x
  have hx : f x = 1 := hker (hX ▸ Subgroup.mem_top x)
  have h1 : σ x * x⁻¹ = 1 := congrArg Subtype.val hx
  simpa [mul_inv_eq_one] using h1

theorem uc22p2214_comm_eq_one_of_central {Q : Type*} [Group Q] {L : Subgroup Q} (hL : commutator ↥L = ⊤)
    {y : Q} (hy : y ∈ normalizer (L : Set Q))
    (h : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ (center ↥L).map L.subtype) : ∀ l ∈ L, y * l * y⁻¹ = l := by
  have h1 : L.normalizerMonoidHom ⟨y, hy⟩ = 1 := by
    refine uc22p2214_eq_one_of_central hL _ fun l => ?_
    obtain ⟨z, hz, hzl⟩ := h l l.2
    have hzl' : z = L.normalizerMonoidHom ⟨y, hy⟩ l * l⁻¹ := Subtype.ext hzl
    rw [← hzl']
    exact hz
  intro l hl
  have h2 := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : Q)) h1
  exact h2

theorem uc22p2214_centralizesBar_of_comm {M V K : Subgroup G} (hVM : M ≤ normalizer (V : Set G))
    (hO2 : CFSG.pCore 2 (MBar M V) = ⊥) (hK : K ∈ calC M) (hKV : ¬ K ≤ centralizer (V : Set G)) {x : G}
    (hx : x ∈ normalizer (K : Set G)) (h : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ centralizer (V : Set G)) :
    CentralizesBar x K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : K ≤ M := uc22p22a_le_of_isSubnormal hK.1
  have hq : CFSG.Open.IsQuasisimple ↥(mbarImage M V K) :=
    (uc22br4_isComponentOf_mbarImage M V K hVM hO2 hK hKV).2.2
  have hmem : ∀ k : ↥K, uc22br4_phi M V K hKM k ∈ mbarImage M V K := fun k => by
    rw [← uc22br4_range_phi M V K hKM]
    exact ⟨k, rfl⟩
  let f : ↥K →* ↥(mbarImage M V K) := (uc22br4_phi M V K hKM).codRestrict _ hmem
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← uc22br4_range_phi M V K hKM] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨k, rfl⟩
  have hfker : ∀ k : ↥K, k ∈ f.ker ↔ (k : G) ∈ centralizer (V : Set G) := by
    intro k
    have h1 : k ∈ f.ker ↔ k ∈ (uc22br4_phi M V K hKM).ker := by
      simp only [MonoidHom.mem_ker, f, MonoidHom.codRestrict_apply, Subtype.ext_iff, OneMemClass.coe_one]
    rw [h1, uc22br4_ker_phi M V K hVM hKM, Subgroup.mem_subgroupOf]
  let g : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hg : Function.Surjective g := QuotientGroup.mk'_surjective _
  have hgker : Group.IsSolvable g.ker := by
    rw [QuotientGroup.ker_mk']
    haveI := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).isNilpotent
    infer_instance
  haveI hsolv : Group.IsSolvable f.ker := uc22p22a_ker_solvable g hg hgker hK.2.2 f hf hq
  have hcen : f.ker.map g ≤ center (Bar2 K) := by
    haveI : Group.IsSolvable ↥(f.ker.map g) := Group.isSolvable_of_surjective (g.subgroupMap_surjective f.ker)
    exact uc22p22a_qs_solvable_normal_le_center hK.2.2 ((inferInstance : f.ker.Normal).map _ hg) inferInstance
  have hchar : ∀ γ : ↥(normalizer (K : Set G)),
      (CFSG.pCore 2 ↥K).map (K.normalizerMonoidHom γ).toMonoidHom = CFSG.pCore 2 ↥K := fun γ =>
    Subgroup.characteristic_iff_map_eq.mp CFSG.pCore_characteristic _
  set σ := CFSG.LocalAnalysis.GLTheoremB.quotAutHom (CFSG.pCore 2 ↥K) K.normalizerMonoidHom hchar ⟨x, hx⟩
    with hσ
  have hσk : ∀ k : ↥K, σ (g k) = g (K.normalizerMonoidHom ⟨x, hx⟩ k) := fun k =>
    CFSG.LocalAnalysis.GLTheoremB.quotAutHom_mk _ _ hchar _ k
  have hcomm : ∀ k : ↥K, (⟨x * k * x⁻¹ * k⁻¹, K.mul_mem (K.normalizerMonoidHom ⟨x, hx⟩ k).2
      (K.inv_mem k.2)⟩ : ↥K) ∈ f.ker := fun k => (hfker _).2 (h k k.2)
  have hσ1 : σ = 1 := by
    refine uc22p2214_eq_one_of_central hK.2.2.1 σ fun q => ?_
    obtain ⟨k, rfl⟩ := hg q
    rw [hσk]
    have h2 := hcen (Subgroup.mem_map_of_mem g (hcomm k))
    convert h2 using 1
    rw [← map_inv, ← map_mul]
    rfl
  refine ⟨hx, fun l hl => ?_⟩
  have h3 := hσk ⟨l, hl⟩
  rw [hσ1, MulAut.one_apply] at h3
  have h4 := (QuotientGroup.eq_iff_div_mem (N := CFSG.pCore 2 ↥K)).1 h3.symm
  exact ⟨_, h4, by simp [div_eq_mul_inv]⟩

theorem uc22p2214_isSylowOf_inf {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime] {P H K : Subgroup Q}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hH : CFSG.Open.IsSubnormal H K) :
    CFSG.ABGLocalTools.IsSylowOf p (P ⊓ H) H := by
  induction hH with
  | refl A => rwa [inf_eq_left.2 hP.le]
  | step hHM hn _ ih =>
    have h1 := ih hP
    have h2 := h1.inf_of_le_normalizer hHM ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn)
    rwa [inf_assoc, inf_eq_right.2 hHM] at h2

theorem uc22p2214_conjSetOf_eq {M K K' : Subgroup G} (hK' : K' ∈ conjSetOf M K) :
    conjSetOf M K' = conjSetOf M K := by
  obtain ⟨g, hg, rfl⟩ := hK'
  ext A
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, M.mul_mem hh hg, uc22p22d_map_conj_map_conj K g h⟩
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h * g⁻¹, M.mul_mem hh (M.inv_mem hg), ?_⟩
    rw [uc22p22d_map_conj_map_conj K g (h * g⁻¹), inv_mul_cancel_right]

theorem uc22p2214_mem_normalizer_of_odd {M K : Subgroup G} (hc2 : (conjSetOf M K).ncard = 2) {g : G} (hg : g ∈ M)
    (hodd : Odd (orderOf g)) : g ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hpair := uc22p22d_conjSet_pair hg hne hc2
  have hmem : (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom ∈ conjSetOf M K := by
    rw [uc22p22d_map_conj_map_conj]
    exact ⟨g * g, M.mul_mem hg hg, rfl⟩
  have hgg : (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
    rw [hpair] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · exact absurd (Subgroup.map_injective (MulAut.conj g).injective h1) hne
  have hg2 : g * g ∈ normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [uc22p22d_map_conj_map_conj] at hgg
    exact hgg
  obtain ⟨j, hj⟩ := hodd
  have hgj : g = (g * g) ^ (j + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (j + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.1 (hgj ▸ (normalizer (K : Set G)).pow_mem hg2 _))

theorem uc22p2214_fix (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch) {K : Subgroup G} (hKM : K ≤ D.M)
    (hK : (K.subgroupOf D.M).Normal ∨ (conjSetOf D.M K).ncard = 2) :
    ∀ K' ∈ conjSetOf D.M K, c.B0 ≤ normalizer (K' : Set G) := by
  intro K' hK' b hb
  have hbM : b ∈ D.M := c.hBM hb
  rcases hK with hn | hc2
  · obtain ⟨g, hg, rfl⟩ := hK'
    have hMK : D.M ≤ normalizer (K : Set G) := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hn
    have hgK : K.map (MulAut.conj g).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hMK hg)
    rw [hgK]
    exact hMK hbM
  · have hc2' : (conjSetOf D.M K').ncard = 2 := by rw [uc22p2214_conjSetOf_eq hK']; exact hc2
    exact uc22p2214_mem_normalizer_of_odd hc2' hbM (uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb)

theorem uc22p2214_two_le_pRank_of_surj {K : Subgroup G} {Y : Type*} [Group Y] [Finite Y] (f : ↥K →* Y)
    (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) : 2 ≤ CFSG.Open.pRank p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, -, hE₀, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (⊤ : Subgroup Y)
  have hE₀p : IsPGroup p ↥E₀ := IsPGroup.of_card hcard
  have hE₀nc : ¬ IsCyclic ↥E₀ := by
    intro hc
    have h1 : Monoid.exponent ↥E₀ = Nat.card E₀ := IsCyclic.exponent_eq_card
    have h2 : Monoid.exponent ↥E₀ ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hE₀.2 x x.2)
    have h3 : Nat.card E₀ ≤ p := h1 ▸ Nat.le_of_dvd hp.pos h2
    rw [hcard] at h3
    have h4 : p ^ 2 ≤ p ^ CFSG.Open.pRank p (⊤ : Subgroup Y) := Nat.pow_le_pow_right hp.pos h
    have h5 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  let f' : ↥(E₀.comap f) →* ↥E₀ := f.subgroupComap E₀
  have hf' : Function.Surjective f' := f.subgroupComap_surjective_of_surjective E₀ hf
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥(E₀.comap f)))
  have hPtop : ((Sylow.mapSurjective hf' P : Sylow p ↥E₀) : Subgroup ↥E₀) = ⊤ :=
    ((Sylow.mapSurjective hf' P).is_maximal' (hE₀p.to_subgroup ⊤) le_top).symm
  have hPnc : ¬ IsCyclic ↥(P : Subgroup ↥(E₀.comap f)) := by
    intro hc
    apply hE₀nc
    have h1 : IsCyclic ↥((P : Subgroup ↥(E₀.comap f)).map f') := by
      haveI := hc
      exact isCyclic_of_surjective _ (f'.subgroupMap_surjective _)
    rw [← Sylow.coe_mapSurjective hf' P, hPtop] at h1
    exact isCyclic_of_surjective (Subgroup.topEquiv.toMonoidHom) Subgroup.topEquiv.surjective
  set R : Subgroup G := ((P : Subgroup ↥(E₀.comap f)).map (E₀.comap f).subtype).map K.subtype with hR
  have hinj : Function.Injective (K.subtype.comp (E₀.comap f).subtype) :=
    K.subtype_injective.comp (Subtype.val_injective)
  have hRe : R = (P : Subgroup ↥(E₀.comap f)).map (K.subtype.comp (E₀.comap f).subtype) := by
    rw [hR, Subgroup.map_map]
  have hRp : IsPGroup p ↥R := by
    rw [hRe]
    exact P.isPGroup'.map _
  have hRnc : ¬ IsCyclic ↥R := by
    rw [hRe]
    intro hc
    haveI := hc
    let e := (P : Subgroup ↥(E₀.comap f)).equivMapOfInjective _ hinj
    exact hPnc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  exact (CFSG.LocalAnalysis.UniquenessCase.UC6.two_le_pRank_of_not_isCyclic hp hp2 hRp hRnc).trans
    (CFSG.SectionRank.pRank_mono hp.one_lt hRK)

theorem uc22p2214_two_le_pRank_sp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSp4 X n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, F, _, _, -, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psp le_rfl

theorem uc22p2214_not_thin_single (M V : Subgroup G) {K : Subgroup G} (hKM : K ≤ M) {n : ℕ}
    (h : IsSp4 ↥(mbarImage M V K) n ∨ (IsSU3 ↥(mbarImage M V K) n ∧ Odd n)) : ¬ F08.Thin8 K := by
  obtain ⟨f, hf⟩ := uc22p22a_exists_surj M V K hKM
  intro hthin
  have h3 := hthin 3 Nat.prime_three (by norm_num)
  have h2 : 2 ≤ CFSG.Open.pRank 3 K := by
    rcases h with hsp | ⟨hsu, hodd⟩
    · exact uc22p2214_two_le_pRank_of_surj f hf Nat.prime_three (by norm_num) (uc22p2214_two_le_pRank_sp4 hsp)
    · refine uc22p2214_two_le_pRank_of_surj ((QuotientGroup.mk' (center ↥(mbarImage M V K))).comp f)
        ((QuotientGroup.mk'_surjective _).comp hf) Nat.prime_three (by norm_num) ?_
      exact CFSG.HardMathSupport.Timmesfeld.Tables.Census.two_le_pRank_three_psu_three_two_pow_odd hodd
        (CFSG.Blueprint.LieModel.statedClassicalModel hsu.2 (by decide))
  omega

theorem uc22p2214_not_thin_pair {M K : Subgroup G} (hK : K ∈ calC M) (hc2 : (conjSetOf M K).ncard = 2) :
    ¬ F08.Thin8 (conjClosure M K) := by
  have hKM : K ≤ M := uc22p22a_le_of_isSubnormal hK.1
  obtain ⟨K', hK', hne⟩ : ∃ K' ∈ conjSetOf M K, K' ≠ K := by
    by_contra hall
    have hsub : conjSetOf M K ⊆ {K} := fun A hA => by
      by_contra hA'
      exact hall ⟨A, hA, hA'⟩
    have := Set.ncard_le_ncard hsub (Set.finite_singleton K)
    rw [hc2, Set.ncard_singleton] at this
    omega
  obtain ⟨g, hg, rfl⟩ := hK'
  have hMM : M ≤ normalizer (M : Set G) := Subgroup.le_normalizer
  have hconj : K.map (MulAut.conj g).toMonoidHom = uniqueFourConj g⁻¹ K := by
    simp [uniqueFourConj]
  have hK'C : K.map (MulAut.conj g).toMonoidHom ∈ calC M := by
    rw [hconj]
    exact uc22p22u_calC_conj hMM hK (M.inv_mem hg)
  have hle : ∀ A ∈ conjSetOf M K, A ≤ conjClosure M K := fun A hA =>
    le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) A hA le_rfl
  exact uc22p22u_not_thin_of_conj hK hK'C hne ⟨g⁻¹, hconj⟩ (hle K ⟨1, M.one_mem, by ext x; simp⟩)
    (hle _ ⟨g, hg, rfl⟩) (uc22p22u_conjClosure_isProd le_rfl hMM hK).1

end CFSG.LocalAnalysis.UniquenessCase.UC22
