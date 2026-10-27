module

public import CFSG.RankThree.PartOne.Q1327T.GlueConf
public import CFSG.RankThree.PartOne.K133.KleinSL2
public import CFSG.RankThree.PartOne.K133C.UnitaryLeaves

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Q1327
  CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.K133C CFSG.RankThree.PartOne.Torsion37
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

section Generic

theorem exists_involution_of_model_PSL {K : Type} [Group K] {f : ℕ}
    (h : StatedClassicalModel K .PSL 2 2 f) : ∃ u : K, orderOf u = 2 := by
  obtain ⟨-, F, hF, hFin, hchar, -, ⟨e⟩⟩ := S15K.exists_mulEquiv_sl2_of_model h
  have h1 : tSL (1 : F) * tSL 1 = 1 := by
    rw [tSL_mul, ← tSL_zero (F := F)]
    congr 1
    exact CharTwo.add_self_eq_zero (1 : F)
  have h2 : tSL (1 : F) ≠ 1 := by
    intro h2
    rw [← tSL_zero (F := F)] at h2
    exact one_ne_zero (tSL_injective h2)
  refine ⟨e.symm (tSL 1), ?_⟩
  rw [MulEquiv.orderOf_eq]
  exact orderOf_eq_prime (by rwa [pow_two]) h2

variable {Q : Type} [Group Q]

theorem exists_moved_two_subgroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center Q = ⊥) (hR : RadAut Q) {u c : Q} (hu : orderOf u = 2)
    (hcu : c * u = u * c) (hc : c ^ p = 1) (hc1 : c ≠ 1) :
    ∃ Sq : Subgroup Q, IsPGroup 2 Sq ∧ (∀ x : Q, c * x * c⁻¹ ∈ Sq ↔ x ∈ Sq) ∧
      ∃ x ∈ Sq, c * x * c⁻¹ ≠ x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcinj := conj_injective_of_center_bot hZ
  obtain ⟨R, hRinn, hR2, hnorm, hcent⟩ := hR u hu
  set S : Subgroup Q := R.comap (MulAut.conj : Q →* MulAut Q) with hSdef
  have hS2 : IsPGroup 2 S := by
    intro x
    obtain ⟨k, hk⟩ := hR2 ⟨MulAut.conj (x : Q), x.2⟩
    refine ⟨k, Subtype.ext (hcinj ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hβc : MulAut.conj c ∈ Subgroup.centralizer ({MulAut.conj u} : Set (MulAut Q)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcu]
  have hβn := Subgroup.mem_normalizer_iff.1 (hnorm _ hβc)
  refine ⟨S, hS2, fun x => ?_, ?_⟩
  · have h1 : MulAut.conj (c * x * c⁻¹) = MulAut.conj c * MulAut.conj x * (MulAut.conj c)⁻¹ := by
      simp only [map_mul, map_inv]
    show MulAut.conj (c * x * c⁻¹) ∈ R ↔ MulAut.conj x ∈ R
    rw [h1]
    exact (hβn (MulAut.conj x)).symm
  · by_contra hno
    push Not at hno
    have hφcent : MulAut.conj c ∈ Subgroup.centralizer (R : Set (MulAut Q)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      obtain ⟨x, rfl⟩ := hRinn hr
      have hx : x ∈ S := hr
      have h1 := hno x hx
      have h2 : MulAut.conj c * MulAut.conj x = MulAut.conj x * MulAut.conj c := by
        rw [← map_mul, ← map_mul]
        congr 1
        calc c * x = (c * x * c⁻¹) * c := by group
          _ = x * c := by rw [h1]
      exact h2.symm
    obtain ⟨k, hk⟩ := hcent ⟨MulAut.conj c, hφcent⟩
    have hk' : (MulAut.conj c) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hcp : (MulAut.conj c) ^ p = 1 := by rw [← map_pow, hc, map_one]
    have hc1' : MulAut.conj c ≠ 1 := fun h1 => hc1 (hcinj (by rw [h1, map_one]))
    have hord : orderOf (MulAut.conj c) = p := orderOf_eq_prime hcp hc1'
    have hdvd : p ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

end Generic

section Theta

variable {G : Type} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem thetaQuotientConj_apply_of_mem (p : ℕ) {N : Subgroup G} (g : ↥N)
    (y : ↥N ⧸ aschbacherSolvableCore p ↥N) :
    thetaQuotientConj p N ⟨(g : G), Subgroup.le_normalizer g.2⟩ y =
      (g : ↥N ⧸ aschbacherSolvableCore p ↥N) * y *
        (g : ↥N ⧸ aschbacherSolvableCore p ↥N)⁻¹ := by
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [thetaQuotientConj_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

omit [Finite G] in
theorem mem_pElementSubgroup_of_pow_eq_one (hp : p.Prime) {X : Subgroup G} {x : G} (hx : x ∈ X)
    (hxp : x ^ p = 1) : x ∈ pElementSubgroup p X := by
  refine Subgroup.subset_closure ⟨hx, ?_⟩
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hxp) with h1 | h1
  · exact ⟨0, by simpa using h1⟩
  · exact ⟨1, by simpa using h1⟩

end Theta

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem exists_datum (hp : p.Prime) (hp5 : 5 ≤ p) (H : Hyp G p A c L E f r R s s' zs)
    {t : MulAut E} {a : G} {N P : Subgroup G} (d : PairN p f E R s t a N P)
    (hZ : Subgroup.center (↥N ⧸ aschbacherSolvableCore p ↥N) = ⊥)
    (hmodel : StatedClassicalModel (↥N ⧸ aschbacherSolvableCore p ↥N) .PSU 3 2 f) :
    ∃ A₀ S : Subgroup G, A₀ ≤ E ∧ IsElementaryAbelian p ↥A₀ ∧ Nat.card A₀ = p ^ 2 ∧
      S ≤ pElementSubgroup p (Subgroup.centralizer (R : Set G)) ∧ S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧
      A₀ ≤ Subgroup.normalizer (S : Set G) ∧ ⁅S, A₀⁆ = S := by
  classical
  have h := H.h12
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  set θ := aschbacherSolvableCore p ↥N with hθ
  set π := QuotientGroup.mk' θ with hπ
  obtain ⟨cbar, hcbarĒ, hcbar1, Kb, xb, hKbc, -, hKbmodel, -, -, -⟩ := d.conf.conf
  obtain ⟨c₀', hc₀'P, hc₀'cbar⟩ := Subgroup.mem_map.1 hcbarĒ
  have hc₀P : (c₀' : G) ∈ P := Subgroup.mem_subgroupOf.1 hc₀'P
  have hc₀N : (c₀' : G) ∈ N := c₀'.2
  have hc₀E : (c₀' : G) ∈ E := d.P_le_E hc₀P
  have hc₀p : (c₀' : G) ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h hc₀E
  have hc₀'p : c₀' ^ p = 1 := Subtype.ext hc₀p
  have hcbarp : cbar ^ p = 1 := by rw [← hc₀'cbar, ← map_pow, hc₀'p, map_one]
  have hc₀1 : (c₀' : G) ≠ 1 := fun h1 => hcbar1 (by
    rw [← hc₀'cbar, show c₀' = 1 from Subtype.ext h1, map_one])
  obtain ⟨u, hu⟩ := exists_involution_of_model_PSL hKbmodel
  have hu2 : orderOf ((u : Kb) : ↥N ⧸ θ) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hcu : cbar * (u : ↥N ⧸ θ) = (u : ↥N ⧸ θ) * cbar :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hKbc u.2)).symm
  have hR := radAut_of_model_PSU hZ hmodel
  obtain ⟨Sq, hSq2, hSqstab, x, hxSq, hxmov⟩ :=
    exists_moved_two_subgroup hp hp2 hZ hR hu2 hcu hcbarp hcbar1
  have hg : (c₀' : G) ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer c₀'.2
  have hconj : ∀ y, thetaQuotientConj p N ⟨(c₀' : G), hg⟩ y = cbar * y * cbar⁻¹ := fun y => by
    rw [thetaQuotientConj_apply_of_mem p c₀' y]
    exact congrArg (fun z => z * y * z⁻¹) hc₀'cbar
  have hmov : MovesTwoQuot p N (c₀' : G) :=
    ⟨hg, Sq, hSq2, fun y => by rw [hconj]; exact hSqstab y, x, hxSq, by rw [hconj]; exact hxmov⟩
  obtain ⟨T, hTN, hT1, hT2, hTnorm, hTcomm⟩ :=
    exists_invariant_two_subgroup hp hp2 h.E_elem hc₀E hmov
  have haconj : ∀ n ∈ N, a * n * a⁻¹ = n := fun n hn => by
    rw [d.a_cent n hn]
    group
  have haD : a ∈ thetaQuotientCentralizer p E N := by
    rw [mem_thetaQuotientCentralizer_iff]
    refine ⟨d.a_mem, ?_, fun k hk => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [haconj y hy]
        exact hy
      · intro hy
        have h1 : a * (a * y * a⁻¹) = (a * y * a⁻¹) * a := d.a_cent _ hy
        have h2 : a * y * a⁻¹ = y := by
          calc a * y * a⁻¹ = a⁻¹ * (a * (a * y * a⁻¹)) := by group
            _ = a⁻¹ * ((a * y * a⁻¹) * a) := by rw [h1]
            _ = y := by group
        rwa [h2] at hy
    · have : a * k * a⁻¹ * k⁻¹ = 1 := by rw [haconj k hk]; group
      rw [this]
      exact Subgroup.one_mem _
  set A₀ : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers (c₀' : G) with hA₀
  have haE := d.a_mem
  have hA₀E : A₀ ≤ E := sup_le (Subgroup.zpowers_le.2 haE) (Subgroup.zpowers_le.2 hc₀E)
  have ha_norm : a ∈ Subgroup.normalizer (T : Set G) := hTnorm (Subgroup.mem_sup_right haD)
  have hc_norm : (c₀' : G) ∈ Subgroup.normalizer (T : Set G) :=
    hTnorm (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hA₀N : A₀ ≤ Subgroup.normalizer (T : Set G) :=
    sup_le (Subgroup.zpowers_le.2 ha_norm) (Subgroup.zpowers_le.2 hc_norm)
  have hcomm : ⁅T, A₀⁆ = T := le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.1 hA₀N) (by
    calc T = ⁅T, Subgroup.zpowers (c₀' : G)⁆ := hTcomm.symm
      _ ≤ ⁅T, A₀⁆ := Subgroup.commutator_mono le_rfl le_sup_right)
  have hao : orderOf a = p := orderOf_eq_prime (Sec12Three.pow_eq_one_of_mem_E h haE) d.a_ne
  have hco : orderOf (c₀' : G) = p := orderOf_eq_prime hc₀p hc₀1
  have hza : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hao]
  have hzc : Nat.card (Subgroup.zpowers (c₀' : G)) = p := by rw [Nat.card_zpowers, hco]
  have hne : Subgroup.zpowers a ≠ Subgroup.zpowers (c₀' : G) := by
    intro heq
    apply d.a_not_P
    have : a ∈ Subgroup.zpowers (c₀' : G) := heq ▸ Subgroup.mem_zpowers a
    exact (Subgroup.zpowers_le.2 hc₀P) this
  have hdisj := inf_eq_bot_of_card_prime hp hza hzc hne
  have hcardA₀ : Nat.card A₀ = p ^ 2 := by
    rw [hA₀, Torsion37.card_sup_of_commute_disjoint (fun k hk l hl =>
      congrArg Subtype.val (h.E_elem.is_comm.comm
        (⟨k, (Subgroup.zpowers_le.2 haE) hk⟩ : ↥E) ⟨l, (Subgroup.zpowers_le.2 hc₀E) hl⟩))
      (disjoint_iff.2 hdisj), hza, hzc, pow_two]
  have hTM : T ≤ Subgroup.centralizer (R : Set G) := by
    have hNM : N ≤ Subgroup.centralizer (R : Set G) := by
      refine d.N_le.trans ?_
      rw [centralizer_union_eq]
      exact inf_le_left
    exact hTN.trans hNM
  have hTp : T ≤ pElementSubgroup p (Subgroup.centralizer (R : Set G)) := by
    rw [← hTcomm, Subgroup.commutator_le]
    intro t ht g hg
    have hgE : g ∈ E := (Subgroup.zpowers_le.2 hc₀E) hg
    have hgM : g ∈ Subgroup.centralizer (R : Set G) := E_le_centralizer_R H hgE
    have htM := hTM (by simpa [hTcomm] using ht)
    have hgp : g ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h hgE
    rw [commutatorElement_def]
    refine Subgroup.mul_mem _ ?_ ?_
    · refine mem_pElementSubgroup_of_pow_eq_one hp (mul_mem (mul_mem htM hgM) (inv_mem htM)) ?_
      rw [conj_pow, hgp]
      group
    · refine mem_pElementSubgroup_of_pow_eq_one hp (inv_mem hgM) ?_
      rw [inv_pow, hgp, inv_one]
  exact ⟨A₀, T, hA₀E, isElementaryAbelian_of_le' h.E_elem hA₀E, hcardA₀, hTp, hT1, hT2, hA₀N,
    hcomm⟩

end Main

end CFSG.RankThree.PartOne.Q1327T
