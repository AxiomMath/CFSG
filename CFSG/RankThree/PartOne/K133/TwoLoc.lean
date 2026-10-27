module

public import CFSG.RankThree.PartOne.K133.Quot
public import CFSG.RankThree.PartOne.K133.KillBasic
import CFSG.RankThree.PartOne.S10.PlaneLocalRankTwoLocal
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K

section Sylow

theorem exists_char_two_sylow {Q : Type*} [Group Q] [Finite Q] (Sh : Subgroup Q)
    (h2 : IsPGroup 2 (Sh.map (QuotientGroup.mk' (Subgroup.center Q)))) :
    ∃ S : Subgroup Q, S ≤ Sh ∧ IsPGroup 2 S ∧
      (∀ x ∈ Sh, ∃ y ∈ S, QuotientGroup.mk' (Subgroup.center Q) y =
        QuotientGroup.mk' (Subgroup.center Q) x) ∧
      ∀ φ : MulAut Q, (∀ s ∈ Sh, φ s ∈ Sh) → ∀ s ∈ S, φ s ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  let f : ↥Sh →* ↥(Sh.map π) := π.subgroupMap Sh
  have hf : Function.Surjective f := π.subgroupMap_surjective Sh
  have hker : f.ker ≤ Subgroup.center ↥Sh := by
    intro x hx
    have hx1 : π (x : Q) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hxc : (x : Q) ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).1 hx1
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxc z)
  have hnil2 : Group.IsNilpotent ↥(Sh.map π) := h2.isNilpotent
  have hnil : Group.IsNilpotent ↥Sh := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥Sh) := inferInstance
  have hPn : (P : Subgroup ↥Sh).Normal := inferInstance
  have hu : Unique (Sylow 2 ↥Sh) := Sylow.unique_of_normal P hPn
  refine ⟨(P : Subgroup ↥Sh).map Sh.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_, ?_⟩
  · intro x hx
    have hmax := (P.mapSurjective hf).is_maximal' (Q := ⊤) (h2.to_subgroup ⊤) le_top
    have hxm : f ⟨x, hx⟩ ∈ ((P.mapSurjective hf : Sylow 2 ↥(Sh.map π)) : Subgroup ↥(Sh.map π)) := by
      rw [← hmax]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hxm
    obtain ⟨y, hyP, hy⟩ := Subgroup.mem_map.1 hxm
    refine ⟨(y : Q), Subgroup.mem_map.2 ⟨y, hyP, rfl⟩, ?_⟩
    have := congrArg Subtype.val hy
    exact this
  · intro φ hφ s hs
    obtain ⟨s', hs'P, rfl⟩ := Subgroup.mem_map.1 hs
    set t : ↥Sh := ⟨φ (s' : Q), hφ _ s'.2⟩ with ht
    have hord : orderOf t = orderOf s' := by
      rw [← Subgroup.orderOf_coe t, ← Subgroup.orderOf_coe s']
      exact MulEquiv.orderOf_eq φ (s' : Q)
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨s', hs'P⟩
    have hsk : orderOf s' ∣ 2 ^ k := by
      have h1 := orderOf_dvd_of_pow_eq_one hk
      rw [← Subgroup.orderOf_coe (⟨s', hs'P⟩ : ↥(P : Subgroup ↥Sh))] at h1
      exact h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hsk
    have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hord, hj])
    obtain ⟨P', hP'⟩ := hzp.exists_le_sylow
    have hP'P : P' = P := Subsingleton.elim P' P
    have htP : t ∈ (P : Subgroup ↥Sh) := hP'P ▸ hP' (Subgroup.mem_zpowers t)
    exact Subgroup.mem_map.2 ⟨t, htP, rfl⟩

end Sylow

section Lift2

variable {G : Type} [Group G] [Finite G] {p : ℕ} {J : Subgroup G}

theorem exists_two_subgroup_of_simpleQuot (hp : p.Prime) (hp2 : p ≠ 2) {F : Subgroup G}
    (hF : IsPGroup p F) (hFJ : F ≤ Subgroup.normalizer (J : Set G))
    {S : Subgroup (SimpleQuot p J)} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hst : ∀ x : ↥F, ∀ s ∈ S, simpleQuotAction p hFJ x s ∈ S) :
    ∃ R : Subgroup G, R ≤ J ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ F ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ x : ↥F, (∃ s ∈ S, simpleQuotAction p hFJ x s ≠ s) → ∃ r ∈ R, (x : G) * r * (x : G)⁻¹ ≠ r := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set π : (↥J ⧸ aschbacherSolvableCore p ↥J) →* SimpleQuot p J :=
    QuotientGroup.mk' (Subgroup.center (↥J ⧸ aschbacherSolvableCore p ↥J)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Sh : Subgroup (↥J ⧸ aschbacherSolvableCore p ↥J) := S.comap π with hSh
  have hmap : Sh.map π = S := Subgroup.map_comap_eq_self_of_surjective hπs S
  have h2 : IsPGroup 2 (Sh.map π) := by rw [hmap]; exact hS2
  obtain ⟨St, -, hSt2, hStπ, hStφ⟩ := exists_char_two_sylow Sh h2
  have hSt_inv : ∀ x : ↥F, ∀ s ∈ St, thetaQuotientAction p hFJ x s ∈ St := fun x s hs =>
    hStφ (thetaQuotientAction p hFJ x) (fun s' hs' => hst x (π s') hs') s hs
  have hbH : F ≤ Subgroup.normalizer (hatSub p J St : Set G) := by
    intro g hg
    refine mem_normalizer_hatSub (hFJ hg) (fun y => ?_)
    constructor
    · intro hy
      have h1 : thetaQuotientAction p hFJ ⟨g⁻¹, F.inv_mem hg⟩
          (thetaQuotientAction p hFJ ⟨g, hg⟩ y) ∈ St := hSt_inv ⟨g⁻¹, F.inv_mem hg⟩ _ hy
      have h2 : thetaQuotientAction p hFJ ⟨g⁻¹, F.inv_mem hg⟩
          (thetaQuotientAction p hFJ ⟨g, hg⟩ y) = y := by
        rw [← MulAut.mul_apply, ← map_mul]
        have : (⟨g⁻¹, F.inv_mem hg⟩ : ↥F) * ⟨g, hg⟩ = 1 := Subtype.ext (inv_mul_cancel g)
        rw [this, map_one, MulAut.one_apply]
      rwa [h2] at h1
    · intro hy
      exact hSt_inv ⟨g, hg⟩ y hy
  have hbot : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 inferInstance
  obtain ⟨R, hRsyl, -, hFR⟩ := CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime hp
    Nat.prime_two hF hbH (not_dvd_card_hatSub hp hp2 hSt2) bot_le
    (IsPGroup.of_card (n := 0) (by simp)) (by rw [hbot]; exact le_top)
  obtain ⟨hRle, hRp⟩ : R ≤ hatSub p J St ∧ IsPGroup 2 R := by
    obtain ⟨Q, rfl⟩ := hRsyl
    exact ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _⟩
  obtain ⟨s, hsS, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hS1 ((Subgroup.eq_bot_iff_forall S).2 hno)
  obtain ⟨q, hq⟩ := hπs s
  obtain ⟨y, hyS, hyq⟩ := hStπ q (by rw [hSh, Subgroup.mem_comap, hq]; exact hsS)
  have hy1 : y ≠ 1 := by
    intro h1
    apply hs1
    rw [← hq, ← hyq, h1, map_one]
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective y
  have hwS : (w : G) ∈ hatSub p J St := by
    refine mem_hatSub.2 ⟨w.2, ?_⟩
    have : thetaMk p J ⟨(w : G), w.2⟩ = y := hw
    rw [this]
    exact hyS
  obtain ⟨r, hrR, n, hn, hrn⟩ := exists_mul_of_sylow hSt2 hRsyl _ hwS
  refine ⟨R, hRle.trans hatSub_le, ?_, hRp, hFR, ?_⟩
  · intro hR
    have hr1 : r = 1 := by
      rw [hR, Subgroup.mem_bot] at hrR
      exact hrR
    apply hy1
    rw [hr1, one_mul] at hrn
    have hwn : thetaMk p J ⟨(w : G), w.2⟩ = 1 := (thetaMk_eq_one_iff p J w.2).2 (hrn ▸ hn)
    rw [← hw]
    exact hwn
  ·
    intro x ⟨s, hsS, hxs⟩
    by_contra hno
    push Not at hno
    apply hxs
    obtain ⟨q, hq⟩ := hπs s
    obtain ⟨y, hyS, hyq⟩ := hStπ q (by rw [hSh, Subgroup.mem_comap, hq]; exact hsS)
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective y
    have hwS : (w : G) ∈ hatSub p J St := by
      refine mem_hatSub.2 ⟨w.2, ?_⟩
      have : thetaMk p J ⟨(w : G), w.2⟩ = y := hw
      rw [this]
      exact hyS
    obtain ⟨r, hrR, n, hn, hrn⟩ := exists_mul_of_sylow hSt2 hRsyl _ hwS
    have hxN : (x : G) ∈ Subgroup.normalizer (J : Set G) := hFJ x.2
    have hrI : r ∈ J := hatSub_le (hRle hrR)
    have hnI : n ∈ J := ((mem_theta_iff p J).1 hn).1
    have hxn : (x : G) * n * (x : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) J :=
      theta_conj_mem_of_normalizer p J hxN hn
    have hxnI : (x : G) * n * (x : G)⁻¹ ∈ J := ((mem_theta_iff p J).1 hxn).1
    have hxw : (x : G) * (w : G) * (x : G)⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hxN _).1 w.2
    have hreq : (x : G) * (w : G) * (x : G)⁻¹ = r * ((x : G) * n * (x : G)⁻¹) := by
      rw [hrn]
      have hcr : (x : G) * r * (x : G)⁻¹ = r := hno r hrR
      calc (x : G) * (r * n) * (x : G)⁻¹ = ((x : G) * r * (x : G)⁻¹) * ((x : G) * n * (x : G)⁻¹) := by
            group
        _ = r * ((x : G) * n * (x : G)⁻¹) := by rw [hcr]
    have hact := act_mk p J hxN w.2 hxw
    have e1 : (⟨(x : G) * (w : G) * (x : G)⁻¹, hxw⟩ : ↥J) =
        ⟨r * ((x : G) * n * (x : G)⁻¹), hreq ▸ hxw⟩ := Subtype.ext hreq
    have e2 : w = ⟨r * n, hrn ▸ w.2⟩ := Subtype.ext hrn
    have hmid : thetaQuotientConj p J ⟨(x : G), hxN⟩ (thetaMk p J w) = thetaMk p J w := by
      have hz' : thetaMk p J ⟨(w : G), w.2⟩ = thetaMk p J w := rfl
      rw [← hz', hact, e1, thetaMk_mul_theta hrI hxn _]
      conv_rhs => rw [e2]
      exact (thetaMk_mul_theta hrI hn _).symm
    have hy' : thetaMk p J w = y := hw
    rw [hy'] at hmid
    have h1 : simpleQuotAction p hFJ x (π y) = π y := by
      show π (thetaQuotientConj p J ⟨(x : G), hxN⟩ y) = π y
      rw [hmid]
    rw [← hq, ← hyq]
    exact h1

end Lift2

section Dead

theorem simpleQuotAction_image {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E ≠ A)
    {t : MulAut E} {b : G} (hb : b ∈ autFixedInG E t) (hb1 : b ≠ 1) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsAt p b) (hD : thetaQuotientCentralizer p E J = Subgroup.zpowers b) :
    ∃ hEJ : E ≤ Subgroup.normalizer (J : Set G),
      IsElementaryAbelian p (simpleQuotAction p hEJ).range ∧
        Nat.card (simpleQuotAction p hEJ).range = p ^ 3 := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hbE : b ∈ E := (Subgroup.map_subtype_le _) hb
  have hEJ : E ≤ Subgroup.normalizer (J : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components hbE hJ
  have hQ : Group.IsPerfect (↥J ⧸ aschbacherSolvableCore p ↥J) :=
    (isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hJ).1
  have hker : ((simpleQuotAction p hEJ).ker).map E.subtype = Subgroup.zpowers b := by
    rw [← hD, thetaQuotientCentralizer_eq_map_ker p hEJ]
    congr 1
    ext x
    exact ker_simpleQuotAction p hQ hEJ x
  have hbp : b ^ p = 1 := by
    have := h.E_elem
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) b hbE
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcardker : Nat.card (simpleQuotAction p hEJ).ker = p := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective (f := E.subtype), hker,
      Nat.card_zpowers, hbord]
  have hmul := Subgroup.card_ker_mul_card_range (simpleQuotAction p hEJ)
  rw [hcardker, card_E_of_ne hF hEA] at hmul
  have hcard3 : Nat.card (simpleQuotAction p hEJ).range = p ^ 3 := by
    have hp0 : 0 < p := hp.pos
    apply Nat.eq_of_mul_eq_mul_left hp0
    rw [hmul]
    ring
  exact ⟨hEJ, isElementaryAbelian_range h.E_elem _, hcard3⟩

theorem false_of_normalizes_two {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E ≠ A)
    {R : Subgroup G} (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hER : E ≤ Subgroup.normalizer (R : Set G)) : False := by
  have hp := h.prime
  have h4 : 4 ≤ RankThreeEven.localRank p G :=
    (SourceSixThirteen.le_localRank_iff_exists hp (by norm_num)).2
      ⟨R, hR2, hR1, E, hER, h.E_elem, card_E_of_ne hF hEA⟩
  have hpG : p ∣ Nat.card G :=
    (dvd_pow_self p (by norm_num : (4 : ℕ) ≠ 0)).trans
      ((card_E_of_ne hF hEA) ▸ Subgroup.card_subgroup_dvd_card E)
  have h3 := Theta.localRank_le_twoLocalOddRank hp (by have := h.three_lt; omega) hpG
  have he : twoLocalOddRank G = 3 := h.setup.2.2.2.2.1
  omega

@[expose] def Dead (p : ℕ) (X : Type) [Group X] : Prop :=
  ∀ Ē : Subgroup (MulAut X), IsElementaryAbelian p Ē → Nat.card Ē = p ^ 3 →
    ∃ S : Subgroup X, S ≠ ⊥ ∧ IsPGroup 2 S ∧ ∀ φ ∈ Ē, ∀ s ∈ S, φ s ∈ S

theorem NoRankThree.dead {p : ℕ} {X : Type} [Group X] (h : NoRankThree p X) : Dead p X :=
  fun Ē hE hc => absurd ⟨Ē, hE, hc⟩ h

theorem Dead.of_mulEquiv {p : ℕ} (hp : p.Prime) {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Dead p Y) : Dead p X := by
  intro Ē hE hc
  have : Fact p.Prime := ⟨hp⟩
  have hE' : IsElementaryAbelian p (Ē.map (MulAut.congr e).toMonoidHom) := by
    have := hE
    exact IsElementaryAbelian.map (MulAut.congr e).toMonoidHom
  have hc' : Nat.card (Ē.map (MulAut.congr e).toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hc]
  obtain ⟨S, hS1, hS2, hSst⟩ := h _ hE' hc'
  refine ⟨S.map e.symm.toMonoidHom, ?_, hS2.map _, ?_⟩
  · intro hbot
    exact hS1 ((Subgroup.map_eq_bot_iff_of_injective S e.symm.injective).1 hbot)
  · intro φ hφ s hs
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
    have hmem := hSst ((MulAut.congr e) φ) (Subgroup.mem_map_of_mem _ hφ) s' hs'
    refine Subgroup.mem_map.2 ⟨(MulAut.congr e φ) s', hmem, ?_⟩
    simp [MulAut.congr_apply]

theorem KF133ResMaxAt.of_dead {P : (X : Type) → [Group X] → Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      P X → ∀ p : ℕ, p.Prime → 5 ≤ p → Dead p X) :
    KF133ResMaxAt P := by
  intro G _ _ p A c L E h hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc hPJ
  exfalso
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hEJ, hEl, hcard3⟩ := simpleQuotAction_image h hF hEA hb hb1 hJ hD
  have hEe := h.E_elem
  have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hJ
  have : IsSimpleGroup (SimpleQuot p J) := hq.2.1
  obtain ⟨S, hS1, hS2, hSst⟩ := hP _ hq.2.2 hPJ p hp h5 _ hEl hcard3
  obtain ⟨R, hRJ, hR1, hR2, hER, -⟩ := exists_two_subgroup_of_simpleQuot hp (by omega)
    (IsElementaryAbelian.isPGroup p E) hEJ hS1 hS2 (fun x s hs => hSst _ ⟨x, rfl⟩ s hs)
  exact false_of_normalizes_two h hF hEA hR1 hR2 hER

end Dead

end CFSG.RankThree.PartOne.K133
