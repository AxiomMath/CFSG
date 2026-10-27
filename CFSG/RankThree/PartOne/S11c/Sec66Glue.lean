module

public import CFSG.RankThree.PartOne.S11c.Sec66
public import CFSG.RankThree.PartOne.S11c.Sec66Aut
public import CFSG.RankThree.PartOne.S11c.Sec66TGroup
public import CFSG.RankThree.PartOne.S11c.Sec66TRank
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.RankThree.PartOne.Sec66T

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {H : Type} [Group H]

theorem centerQuotientConj_of_mem {J : Subgroup H} (j : J) :
    centerQuotientConj J ⟨(j : H), Subgroup.le_normalizer j.2⟩ =
      MulAut.conj (j : J ⧸ Subgroup.center J) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
    change ((J.normalizerMonoidHom ⟨(j : H), Subgroup.le_normalizer j.2⟩ l : J) :
      J ⧸ Subgroup.center J) = _
    rw [MulAut.conj_apply]
    have : (J.normalizerMonoidHom ⟨(j : H), Subgroup.le_normalizer j.2⟩ l : J) = j * l * j⁻¹ := by
      apply Subtype.ext
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [this]
    rfl

theorem mem_sup_of_inner {J : Subgroup H} (hJ : Group.IsPerfect ↥J) {a : H}
    (ha : a ∈ Subgroup.normalizer (J : Set H)) {q : ↥J ⧸ Subgroup.center ↥J}
    (hq : centerQuotientConj J ⟨a, ha⟩ = MulAut.conj q) :
    a ∈ J ⊔ Subgroup.centralizer (J : Set H) := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
  have hj : ((j⁻¹ : J) : H) ∈ Subgroup.normalizer (J : Set H) := Subgroup.le_normalizer (j⁻¹).2
  have hg : (j : H)⁻¹ * a ∈ Subgroup.normalizer (J : Set H) :=
    Subgroup.mul_mem _ (by simpa using hj) ha
  have hg1 : centerQuotientConj J ⟨(j : H)⁻¹ * a, hg⟩ = 1 := by
    have h1 : (⟨(j : H)⁻¹ * a, hg⟩ : Subgroup.normalizer (J : Set H)) =
        ⟨((j⁻¹ : J) : H), hj⟩ * ⟨a, ha⟩ := by
      apply Subtype.ext
      simp
    rw [h1, map_mul, centerQuotientConj_of_mem (j⁻¹), hq, ← map_mul]
    simp
  have hAL : Subgroup.zpowers ((j : H)⁻¹ * a) ≤ Subgroup.normalizer (J : Set H) :=
    (Subgroup.zpowers_le).mpr hg
  have hcomm : ∀ l : J, ((j : H)⁻¹ * a) * l = l * ((j : H)⁻¹ * a) := by
    intro l
    exact commute_of_centerQuotientAction_eq_one hAL
      (⟨(j : H)⁻¹ * a, Subgroup.mem_zpowers _⟩ : Subgroup.zpowers ((j : H)⁻¹ * a)) hg1 l
  have hC : (j : H)⁻¹ * a ∈ Subgroup.centralizer (J : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hcomm ⟨l, hl⟩).symm
  have : a = (j : H) * ((j : H)⁻¹ * a) := by group
  rw [this]
  exact Subgroup.mul_mem_sup j.2 hC

variable [Finite H]

theorem exists_fixed_hom {p : ℕ} (hp : p.Prime) {J : Subgroup H}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {a : H}
    (ha : a ∈ Subgroup.normalizer (J : Set H)) (hap : a ^ p = 1) :
    ∃ θ : ↥(J ⊓ Subgroup.centralizer ({a} : Set H)) →*
        ↥(fixSub (centerQuotientConj J ⟨a, ha⟩)),
      Function.Surjective θ ∧
        θ.ker ≤ Subgroup.center ↥(J ⊓ Subgroup.centralizer ({a} : Set H)) ∧
        ∀ x : ↥(J ⊓ Subgroup.centralizer ({a} : Set H)),
          ((θ x : ↥(fixSub (centerQuotientConj J ⟨a, ha⟩))) : ↥J ⧸ Subgroup.center ↥J) =
            ((⟨(x : H), x.2.1⟩ : J) : J ⧸ Subgroup.center J) := by
  classical
  set α := centerQuotientConj J ⟨a, ha⟩ with hα
  have hαmk : ∀ l : J, α (l : J ⧸ Subgroup.center J) =
      ((⟨a * (l : H) * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha (l : H)).mp l.2⟩ : J) :
        J ⧸ Subgroup.center J) := by
    intro l
    rfl
  let ι : ↥(J ⊓ Subgroup.centralizer ({a} : Set H)) →* ↥J := Subgroup.inclusion inf_le_left
  have hfix : ∀ x : ↥(J ⊓ Subgroup.centralizer ({a} : Set H)),
      α ((ι x : J) : J ⧸ Subgroup.center J) = ((ι x : J) : J ⧸ Subgroup.center J) := by
    intro x
    rw [hαmk]
    congr 1
    apply Subtype.ext
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
    show a * (x : H) * a⁻¹ = (x : H)
    rw [← hx]
    group
  let θ : ↥(J ⊓ Subgroup.centralizer ({a} : Set H)) →* ↥(fixSub α) :=
    ((QuotientGroup.mk' (Subgroup.center J)).comp ι).codRestrict (fixSub α) (fun x => hfix x)
  refine ⟨θ, ?_, ?_, fun x => rfl⟩
  · intro y
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (y : J ⧸ Subgroup.center J)
    have hyfix : α (y : J ⧸ Subgroup.center J) = (y : J ⧸ Subgroup.center J) := y.2
    rw [← hl, hαmk] at hyfix
    rw [QuotientGroup.eq_iff_div_mem] at hyfix
    have hz : a * (l : H) * a⁻¹ * (l : H)⁻¹ ∈ (Subgroup.center J).map J.subtype := by
      refine ⟨_, hyfix, ?_⟩
      simp [div_eq_mul_inv]
    obtain ⟨z, hzJ, hzfix, hzcoset⟩ := PlaneInner.exists_fixed_in_coset hp hZ ha hap l.2 hz
    refine ⟨⟨z, hzJ, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        have : a * z * a⁻¹ = z := hzfix
        calc z * a = (a * z * a⁻¹) * a := by rw [this]
          _ = a * z := by group)
    · apply Subtype.ext
      show ((⟨z, hzJ⟩ : J) : J ⧸ Subgroup.center J) = (y : J ⧸ Subgroup.center J)
      rw [← hl, eq_comm, QuotientGroup.eq]
      obtain ⟨w, hw, hwz⟩ := hzcoset
      have : (l : H)⁻¹ * z = (w : H) := hwz.symm
      change (l⁻¹ * ⟨z, hzJ⟩ : J) ∈ Subgroup.center J
      have h2 : (l⁻¹ * ⟨z, hzJ⟩ : J) = w := Subtype.ext (by simpa using this)
      rw [h2]
      exact hw
  · intro x hx
    have hx1 : θ x = 1 := hx
    have h1 := congrArg Subtype.val hx1
    have hxZ : (ι x : J) ∈ Subgroup.center J :=
      (QuotientGroup.eq_one_iff (ι x : J)).mp h1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h3 := Subgroup.mem_center_iff.mp hxZ (ι g)
    exact congrArg (fun z : J => (z : H)) h3

theorem inducesFieldAut_of_fieldAutT {p : ℕ} (hp : p.Prime) {J : Subgroup H}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {a : H}
    (ha : a ∈ Subgroup.normalizer (J : Set H)) (hap : a ^ p = 1)
    (hnot : a ∉ J ⊔ Subgroup.centralizer (J : Set H))
    (hF : FieldAutT p (centerQuotientConj J ⟨a, ha⟩)) : InducesFieldAut p a J := by
  obtain ⟨t, n, f, hf, hmodelT, hfix⟩ := hF
  obtain ⟨θ, hsurj, hker, -⟩ := exists_fixed_hom hp hZ ha hap
  obtain ⟨e⟩ := nonempty_centerQuotient_perfectResidual_equiv
    (J ⊓ Subgroup.centralizer ({a} : Set H)) (fixSub (centerQuotientConj J ⟨a, ha⟩)) θ hsurj hker
  refine ⟨ha, hnot, by rw [hap]; exact Subgroup.one_mem _, t, n, f, hf, hmodelT, ?_⟩
  rcases hfix with h | ⟨ht, hn, hf1, h⟩
  · exact Or.inl (lieModel_of_mulEquiv e.symm h)
  · exact Or.inr ⟨ht, hn, hf1, lieModel_of_mulEquiv e.symm h⟩

omit [Finite H] in
theorem centerQuotientConj_pow {J : Subgroup H} {a : H}
    (ha : a ∈ Subgroup.normalizer (J : Set H)) {p : ℕ} (hap : a ^ p = 1) :
    centerQuotientConj J ⟨a, ha⟩ ^ p = 1 := by
  rw [← map_pow]
  have : (⟨a, ha⟩ : Subgroup.normalizer (J : Set H)) ^ p = 1 :=
    Subtype.ext (by simp [hap])
  rw [this, map_one]

omit [Finite H] in
theorem centerQuotientConj_ne_one {J : Subgroup H} (hJ : Group.IsPerfect ↥J) {a : H}
    (ha : a ∈ Subgroup.normalizer (J : Set H)) (hnot : a ∉ J ⊔ Subgroup.centralizer (J : Set H)) :
    centerQuotientConj J ⟨a, ha⟩ ≠ 1 := by
  intro h
  apply hnot
  have hAL : Subgroup.zpowers a ≤ Subgroup.normalizer (J : Set H) :=
    (Subgroup.zpowers_le).mpr ha
  have hcomm : ∀ l : J, a * l = l * a := fun l =>
    commute_of_centerQuotientAction_eq_one hAL
      (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) h l
  refine Subgroup.mem_sup_right ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (hcomm ⟨l, hl⟩).symm

theorem exists_elementary_ext {p : ℕ} (hp : p.Prime) {A : Subgroup H}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ p = 1) {m : ℕ}
    (hAcard : Nat.card A = p ^ m) {t : H} (htA : t ∉ A) (htp : t ^ p = 1)
    (htc : ∀ x ∈ A, x * t = t * x) :
    ∃ A' : Subgroup H, A ≤ A' ∧ A' ≤ A ⊔ Subgroup.zpowers t ∧ Nat.card A' = p ^ (m + 1) ∧
      (∀ x ∈ A', ∀ y ∈ A', x * y = y * x) ∧ ∀ x ∈ A', x ^ p = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ (m : A) (n : Subgroup.zpowers t),
      Commute (A.subtype m) ((Subgroup.zpowers t).subtype n) := by
    intro m n
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp n.2
    have h1 : Commute (m : H) t := htc m m.2
    show Commute (m : H) (n : H)
    rw [← hk]
    exact h1.zpow_right k
  let φ : A × Subgroup.zpowers t →* H := A.subtype.noncommCoprod (Subgroup.zpowers t).subtype hcomm
  have ht1 : t ≠ 1 := fun h => htA (h ▸ A.one_mem)
  have htord : orderOf t = p := orderOf_eq_prime htp ht1
  have hdisj : Disjoint A (Subgroup.zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxA hxt
    by_contra hx1
    have hxord : orderOf x = p := orderOf_eq_prime (hAp x hxA) hx1
    have hzx : Subgroup.zpowers x ≤ Subgroup.zpowers t := (Subgroup.zpowers_le).mpr hxt
    have hcard : Nat.card (Subgroup.zpowers t) ≤ Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, htord]
    have heq := Subgroup.eq_of_le_of_card_ge hzx hcard
    exact htA ((Subgroup.zpowers_le).mpr hxA (heq ▸ Subgroup.mem_zpowers t))
  have hinj : Function.Injective φ := by
    refine (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
      ⟨A.subtype_injective, (Subgroup.zpowers t).subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact hdisj
  refine ⟨φ.range, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(⟨x, hx⟩, 1), by simp [φ]⟩
  · rintro _ ⟨⟨m, n⟩, rfl⟩
    exact Subgroup.mul_mem_sup m.2 n.2
  · have h1 : Nat.card (A × Subgroup.zpowers t) = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [← h1, Nat.card_prod, hAcard, Nat.card_zpowers, htord, pow_succ]
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hAc _ x.1.2 _ y.1.2
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2.2
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp y.2.2
      show (x.2 : H) * (y.2 : H) = (y.2 : H) * (x.2 : H)
      rw [← hk, ← hl]
      exact (Commute.zpow_zpow_self t k l).eq
  · rintro _ ⟨⟨m, n⟩, rfl⟩
    rw [← map_pow]
    have hm : m ^ p = 1 := Subtype.ext (hAp m m.2)
    have hn : n ^ p = 1 := by
      apply Subtype.ext
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp n.2
      show (n : H) ^ p = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, htp, one_zpow]
    have hmn : ((m, n) : A × Subgroup.zpowers t) ^ p = 1 :=
      Prod.ext (by simpa using hm) (by simpa using hn)
    rw [hmn]
    exact map_one φ

theorem localRankAut_of_localRank {p : ℕ} (he : CFSG.Assembly.RankThreeEven.localRank p H ≤ 3)
    (hp : p.Prime)
    {J : Subgroup H} (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {a c : H}
    (ha : a ∈ Subgroup.normalizer (J : Set H)) (hap : a ^ p = 1)
    (haJ : a ∉ J ⊔ Subgroup.centralizer (J : Set H))
    (hcC : c ∈ Subgroup.centralizer (J : Set H)) (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (hac : a * c = c * a) :
    LocalRankAut p (↥J ⧸ Subgroup.center ↥J) (centerQuotientConj J ⟨a, ha⟩) := by
  classical
  intro _ _ R hR hRcard hRfix U hU1 hU2 hUinv hRU
  set α := centerQuotientConj J ⟨a, ha⟩ with hα
  set G : Subgroup H := J ⊓ Subgroup.centralizer ({a} : Set H) with hG
  obtain ⟨θ, hθsurj, -, hθval⟩ := exists_fixed_hom hp hZ ha hap
  let π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  have hkerdvd : Nat.card θ.ker ∣ Nat.card (Subgroup.center J) := by
    let ιJ : ↥G →* ↥J := Subgroup.inclusion inf_le_left
    have hker : θ.ker.map ιJ ≤ Subgroup.center J := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 := hθval x
      rw [MonoidHom.mem_ker.mp hx] at h1
      exact (QuotientGroup.eq_one_iff (ιJ x)).mp h1.symm
    have h2 : Nat.card (θ.ker.map ιJ) = Nat.card θ.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)
    rw [← h2]
    exact Subgroup.card_dvd_of_le hker
  have hcop : Nat.Coprime (Nat.card θ.ker) (p ^ 2) :=
    (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun h => hZ (h.trans hkerdvd)))).symm
  have hRle : R ≤ fixSub α := fun r hr => hRfix r hr
  let R₀ : Subgroup ↥(fixSub α) := R.subgroupOf (fixSub α)
  have hR₀card : Nat.card R₀ = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv, hRcard]
  obtain ⟨R', hR'map, hR'card, hR'inj⟩ :=
    exists_lift_of_surjective_coprime θ hθsurj hcop R₀ hR₀card
  have hπR : ∀ x ∈ R', π ⟨(x : H), x.2.1⟩ ∈ R := by
    intro x hx
    have h1 : θ x ∈ R₀ := by rw [← hR'map]; exact ⟨x, hx, rfl⟩
    have h2 : ((θ x : ↥(fixSub α)) : J ⧸ Subgroup.center J) ∈ R := h1
    rw [hθval x] at h2
    exact h2
  let A₂ : Subgroup H := R'.map G.subtype
  have hA₂J : ∀ x ∈ A₂, x ∈ J := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2.1
  have hA₂a : ∀ x ∈ A₂, x * a = a * x := by
    rintro _ ⟨x, -, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp x.2.2)
  have hA₂c : ∀ x ∈ A₂, x * c = c * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hcC) x (hA₂J x hx)
  have hA₂p : ∀ x ∈ A₂, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (θ (x ^ p) : ↥(fixSub α)) = θ 1 := by
      apply Subtype.ext
      rw [map_pow, map_one]
      have hr := hπR x hx
      have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := R)
        (π ⟨(x : H), x.2.1⟩) hr
      have h3 : ((θ x : ↥(fixSub α)) : J ⧸ Subgroup.center J) = π ⟨(x : H), x.2.1⟩ := hθval x
      show ((θ x : ↥(fixSub α)) : J ⧸ Subgroup.center J) ^ p = 1
      rw [h3]
      exact this
    have h2 := hR'inj _ (R'.pow_mem hx p) 1 R'.one_mem h1
    show ((x ^ p : ↥G) : H) = 1
    rw [h2]
    rfl
  have hA₂c' : ∀ x ∈ A₂, ∀ y ∈ A₂, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h1 : θ (x * y) = θ (y * x) := by
      apply Subtype.ext
      rw [map_mul, map_mul]
      have hxr := hπR x hx
      have hyr := hπR y hy
      have h4 := hR.is_comm.comm (⟨π ⟨(x : H), x.2.1⟩, hxr⟩ : R) ⟨π ⟨(y : H), y.2.1⟩, hyr⟩
      have h5 := congrArg Subtype.val h4
      simp only [Subgroup.coe_mul] at h5
      simp only [Subgroup.coe_mul]
      rw [hθval x, hθval y]
      exact h5
    have h2 := hR'inj _ (R'.mul_mem hx hy) _ (R'.mul_mem hy hx) h1
    exact congrArg (fun z : ↥G => (z : H)) h2
  have hA₂card : Nat.card A₂ = p ^ 2 := by
    rw [Subgroup.card_map_of_injective G.subtype_injective, hR'card]
  obtain ⟨S, hS2, hS1, hSφ⟩ := exists_aut_invariant_two_subgroup (Subgroup.center J)
    (fun z hz => hz) U hU2 hU1
  let S' : Subgroup H := S.map J.subtype
  have hSJ : S' ≤ J := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hS'1 : S' ≠ ⊥ := by
    intro h
    apply hS1
    have := (Subgroup.map_eq_bot_iff _).mp h
    rw [Subgroup.ker_subtype] at this
    exact eq_bot_iff.mpr this
  have hS'2 : IsPGroup 2 S' := hS2.map J.subtype
  have hconj : ∀ x ∈ R', ∀ s ∈ S, (⟨(x : H), x.2.1⟩ : J) * s * (⟨(x : H), x.2.1⟩ : J)⁻¹ ∈ S := by
    intro x hx s hs
    refine hSφ (MulAut.conj (⟨(x : H), x.2.1⟩ : J)) (fun y => ?_) s hs
    have h1 := (Subgroup.mem_normalizer_iff.mp (hRU (hπR x hx))) (π y)
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    exact h1
  have hA₂S : A₂ ≤ Subgroup.normalizer (S' : Set H) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨_, hconj x hx s hs, rfl⟩
    · rintro ⟨s, hs, hsh⟩
      refine ⟨_, hconj x⁻¹ (R'.inv_mem hx) s hs, ?_⟩
      have hs' : (s : H) = (x : H) * h * (x : H)⁻¹ := hsh
      show ((x⁻¹ : ↥G) : H) * (s : H) * ((x⁻¹ : ↥G) : H)⁻¹ = h
      rw [Subgroup.coe_inv, hs']
      group
  have hUα : ∀ x : J, π x ∈ U ↔ α (π x) ∈ U := by
    intro x
    refine ⟨hUinv _, fun h => ?_⟩
    have hle : Subgroup.map α.toMonoidHom U ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      exact hUinv u hu
    have hfin : Finite U := inferInstance
    have heq : Subgroup.map α.toMonoidHom U = U :=
      Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).ge
    rw [← heq] at h
    obtain ⟨u, hu, hux⟩ := h
    have : u = π x := α.injective hux
    rw [← this]
    exact hu
  let φa : MulAut J := J.normalizerMonoidHom ⟨a, ha⟩
  have hφa : ∀ x : J, π (φa x) = α (π x) := fun x => rfl
  have hφacoe : ∀ x : J, ((φa x : J) : H) = a * (x : H) * a⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨a, ha⟩ x
  have hSa : ∀ s ∈ S, φa s ∈ S := fun s hs =>
    hSφ φa (fun x => by rw [hφa]; exact hUα x) s hs
  have hSa' : ∀ s ∈ S, φa⁻¹ s ∈ S := fun s hs =>
    hSφ φa⁻¹ (fun x => by
      have h1 := hUα (φa⁻¹ x)
      rw [← hφa, MulAut.apply_inv_self] at h1
      exact h1.symm) s hs
  have haS' : a ∈ Subgroup.normalizer (S' : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨φa s, hSa s hs, (hφacoe s).symm⟩
    · rintro ⟨s, hs, hsh⟩
      refine ⟨φa⁻¹ s, hSa' s hs, ?_⟩
      have h1 := hφacoe (φa⁻¹ s)
      rw [MulAut.apply_inv_self] at h1
      have hsh' : (s : H) = a * h * a⁻¹ := hsh
      show ((φa⁻¹ s : J) : H) = h
      have h2 : ((φa⁻¹ s : J) : H) = a⁻¹ * (s : H) * a := by
        rw [h1]
        group
      rw [h2, hsh']
      group
  have hcA₂ : c ∉ A₂ := fun hc =>
    hc1 (PlaneInner.eq_one_of_pow_eq_one hp hZ (hA₂J c hc) hcC hcp)
  obtain ⟨A₃, -, hA₃le, hA₃card, hA₃c, hA₃p⟩ :=
    exists_elementary_ext hp hA₂c' hA₂p hA₂card hcA₂ hcp hA₂c
  have hcS : c ∈ Subgroup.normalizer (S' : Set H) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSJ) hcC)
  have hA₃S : A₃ ≤ Subgroup.normalizer (S' : Set H) :=
    hA₃le.trans (sup_le hA₂S ((Subgroup.zpowers_le).mpr hcS))
  have haA₃ : a ∉ A₃ := by
    intro h
    apply haJ
    have : A₂ ⊔ Subgroup.zpowers c ≤ J ⊔ Subgroup.centralizer (J : Set H) :=
      sup_le (fun x hx => Subgroup.mem_sup_left (hA₂J x hx))
        ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_right hcC))
    exact this (hA₃le h)
  have hacomm : ∀ x ∈ A₃, x * a = a * x := by
    intro x hx
    have : A₂ ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer ({a} : Set H) :=
      sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hA₂a y hy))
        ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr hac.symm))
    exact Subgroup.mem_centralizer_singleton_iff.mp (this (hA₃le hx))
  exact PlaneInner.false_of_commuting_extension_of_localRank he hp hA₃c hA₃p hA₃card hS'1 hS'2
    hA₃S haA₃ hap hacomm haS'

theorem localRankAut_of_evenRank (he : evenRank H ≤ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J : Subgroup H} (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {a c : H}
    (ha : a ∈ Subgroup.normalizer (J : Set H)) (hap : a ^ p = 1)
    (haJ : a ∉ J ⊔ Subgroup.centralizer (J : Set H))
    (hcC : c ∈ Subgroup.centralizer (J : Set H)) (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (hac : a * c = c * a) :
    LocalRankAut p (↥J ⧸ Subgroup.center ↥J) (centerQuotientConj J ⟨a, ha⟩) :=
  localRankAut_of_localRank ((CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans he) hp
    hZ ha hap haJ hcC hc1 hcp hac

theorem fieldAutTag_of_T (t : StatedLieTag) (h : Sec66T_K1 t) :
    ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (J : Subgroup H) (a c d : H), p.Prime → 5 ≤ p →
      CFSG.Assembly.RankThreeEven.localRank p H ≤ 3 → CFSG.IsQuasisimple ↥J →
      (∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧ LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 f) →
      ¬ p ∣ Nat.card (Subgroup.center ↥J) →
      a ∈ Subgroup.normalizer (J : Set H) → a ∉ J ⊔ Subgroup.centralizer (J : Set H) →
      a ^ p = 1 → c ∈ Subgroup.centralizer (J : Set H) → c ≠ 1 → c ^ p = 1 → d ∈ J → d ≠ 1 →
      d ^ p = 1 → a * c = c * a → a * d = d * a →
      (∃ S : Subgroup H, S ≤ J ∧ ¬ S ≤ (Subgroup.center ↥J).map J.subtype ∧ IsPGroup 2 S ∧
        a ∈ Subgroup.normalizer (S : Set H) ∧ c ∈ Subgroup.normalizer (S : Set H) ∧
        d ∈ Subgroup.normalizer (S : Set H) ∧
        ∃ s ∈ S, (a * s * a⁻¹)⁻¹ * s ∉ (Subgroup.center ↥J).map J.subtype ∨
          (d * s * d⁻¹)⁻¹ * s ∉ (Subgroup.center ↥J).map J.subtype) →
      InducesFieldAut p a J := by
  intro H _ _ p J a c d hp hp5 he hq hmodel hnZ ha haJ hap hcC hc1 hcp hdJ hd1 hdp hac had hS
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSJ, hSnc, hS2, haS, hcS, hdS, s, hs, hmv⟩ := hS
  have hperf : Group.IsPerfect ↥J := hq.1
  have hrank := localRankLeTwo_of_localRank he hp hnZ hcC hc1 hcp
  have hαp : centerQuotientConj J ⟨a, ha⟩ ^ p = 1 := centerQuotientConj_pow ha hap
  have hα1 : centerQuotientConj J ⟨a, ha⟩ ≠ 1 := centerQuotientConj_ne_one hperf ha haJ
  have hord : orderOf (centerQuotientConj J ⟨a, ha⟩) = p := orderOf_eq_prime hαp hα1
  have hαinn : centerQuotientConj J ⟨a, ha⟩ ∉ innerAut (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨q', hq'⟩
    exact haJ (mem_sup_of_inner hperf ha hq'.symm)
  have hαmk : ∀ l : J, centerQuotientConj J ⟨a, ha⟩ (l : J ⧸ Subgroup.center J) =
      ((⟨a * (l : H) * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha (l : H)).mp l.2⟩ : J) :
        J ⧸ Subgroup.center J) := fun l => rfl
  have hqd1 : ((⟨d, hdJ⟩ : J) : J ⧸ Subgroup.center J) ≠ 1 := by
    intro h1
    have hdZ : (⟨d, hdJ⟩ : J) ∈ Subgroup.center J := (QuotientGroup.eq_one_iff _).mp h1
    have hdC : d ∈ Subgroup.centralizer (J : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hdZ ⟨l, hl⟩)
    exact hd1 (PlaneInner.eq_one_of_pow_eq_one hp hnZ hdJ hdC hdp)
  have hqdp : ((⟨d, hdJ⟩ : J) : J ⧸ Subgroup.center J) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨d, hdJ⟩ : J) ^ p = 1 := Subtype.ext (by simpa using hdp)
    rw [this]
    rfl
  have hαqd : centerQuotientConj J ⟨a, ha⟩ ((⟨d, hdJ⟩ : J) : J ⧸ Subgroup.center J) =
      ((⟨d, hdJ⟩ : J) : J ⧸ Subgroup.center J) := by
    rw [hαmk]
    congr 1
    apply Subtype.ext
    show a * d * a⁻¹ = d
    rw [had]
    group
  have hU1 : (S.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J)) ≠ ⊥ := by
    intro hbot
    apply hSnc
    intro s hs
    have hsJ : (⟨s, hSJ hs⟩ : J) ∈ S.subgroupOf J := Subgroup.mem_subgroupOf.mpr hs
    have h1 : QuotientGroup.mk' (Subgroup.center J) ⟨s, hSJ hs⟩ ∈
        (S.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J)) := ⟨_, hsJ, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨s, hSJ hs⟩ : J) ∈ Subgroup.center J := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨_, h2, rfl⟩
  have hU2 : IsPGroup 2 ((S.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J))) :=
    (hS2.comap_subtype).map _
  have hαU : ∀ u ∈ (S.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J)),
      centerQuotientConj J ⟨a, ha⟩ u ∈
        (S.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J)) := by
    rintro _ ⟨sJ, hsJ, rfl⟩
    have hs : (sJ : H) ∈ S := Subgroup.mem_subgroupOf.mp hsJ
    have h1 := (Subgroup.mem_normalizer_iff.mp haS (sJ : H)).mp hs
    refine ⟨⟨a * (sJ : H) * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha (sJ : H)).mp sJ.2⟩,
      Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    exact (hαmk sJ).symm
  have hqU : ∀ u ∈ (S.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J)),
      ((⟨d, hdJ⟩ : J) : J ⧸ Subgroup.center J) * u *
        ((⟨d, hdJ⟩ : J) : J ⧸ Subgroup.center J)⁻¹ ∈
        (S.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J)) := by
    rintro _ ⟨sJ, hsJ, rfl⟩
    have hs : (sJ : H) ∈ S := Subgroup.mem_subgroupOf.mp hsJ
    have h1 := (Subgroup.mem_normalizer_iff.mp hdS (sJ : H)).mp hs
    refine ⟨⟨d, hdJ⟩ * sJ * ⟨d, hdJ⟩⁻¹, Subgroup.mem_subgroupOf.mpr (by simpa using h1), ?_⟩
    simp
  have hmove : ∃ u ∈ (S.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J)),
      centerQuotientConj J ⟨a, ha⟩ u ≠ u ∨
        ((⟨d, hdJ⟩ : J) : J ⧸ Subgroup.center J) * u *
          ((⟨d, hdJ⟩ : J) : J ⧸ Subgroup.center J)⁻¹ ≠ u := by
    have hsJ : (⟨s, hSJ hs⟩ : J) ∈ S.subgroupOf J := Subgroup.mem_subgroupOf.mpr hs
    refine ⟨((⟨s, hSJ hs⟩ : J) : J ⧸ Subgroup.center J), ⟨_, hsJ, rfl⟩, ?_⟩
    rcases hmv with h1 | h1
    · left
      intro heq
      rw [hαmk, QuotientGroup.eq] at heq
      exact h1 ⟨_, heq, by simp⟩
    · right
      intro heq
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq] at heq
      exact h1 ⟨_, heq, by simp⟩
  have hF := h (↥J ⧸ Subgroup.center ↥J) p hp hp5 hmodel hrank (centerQuotientConj J ⟨a, ha⟩)
    ((⟨d, hdJ⟩ : J) : J ⧸ Subgroup.center J) _ hord hαinn hqd1 hqdp hαqd hU1 hU2 hαU hqU hmove
    (localRankAut_of_localRank he hp hnZ ha hap haJ hcC hc1 hcp hac)
  exact inducesFieldAut_of_fieldAutT hp hnZ ha hap haJ hF


theorem evenOuterElementIsFieldAutTag_of_T (t : StatedLieTag) (h : Sec66T_K1 t) :
    EvenOuterElementIsFieldAutTag t := by
  intro H _ _ he p J a c d hp hp5 hq hmodel hnZ ha haJ hap hcC hc1 hcp hdJ hd1 hdp hac had hS
  exact fieldAutTag_of_T t h H p J a c d hp hp5
    ((CFSG.RankThree.OddKernel.localRank_le_evenRank hp (by omega)).trans he) hq hmodel hnZ ha haJ
    hap hcC hc1 hcp hdJ hd1 hdp hac had hS

theorem planeNoInnerPart_of_planeT :
    ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (J A : Subgroup H) (c : H), p.Prime → 5 ≤ p →
      CFSG.Assembly.RankThreeEven.localRank p H ≤ 3 → CFSG.IsQuasisimple ↥J →
      ¬ p ∣ Nat.card (Subgroup.center ↥J) → PlaneT p (↥J ⧸ Subgroup.center ↥J) →
      A ≤ Subgroup.normalizer (J : Set H) → IsElementaryAbelian p A → Nat.card A = p ^ 3 →
      c ∈ A → c ≠ 1 → c ∈ Subgroup.centralizer (J : Set H) →
      (∀ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c) → False := by
  intro H _ _ p J A c hp hp5 he hq hnZ hPlane hAN hAe hAcard hcA hc1 hcC hCA
  have : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect ↥J := hq.1
  have hcp : c ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) c hcA
  have hrank := localRankLeTwo_of_localRank he hp hnZ hcC hc1 hcp
  set f := centerQuotientAction hAN with hf
  have hzc : ∀ x ∈ Subgroup.zpowers c, x ∈ Subgroup.centralizer (J : Set H) := fun x hx =>
    (Subgroup.zpowers_le).mpr hcC hx
  have hker : f.ker = (Subgroup.zpowers c).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxC : (x : H) ∈ Subgroup.centralizer (J : Set H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (commute_of_centerQuotientAction_eq_one hAN x hx ⟨l, hl⟩).symm
      exact hCA (x : H) x.2 (Subgroup.mem_sup_right hxC)
    · intro hx
      have hxC := Subgroup.mem_centralizer_iff.mp (hzc _ hx)
      ext q
      induction q using QuotientGroup.induction_on with
      | H l =>
        rw [centerQuotientAction_mk, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        rw [coe_normalizerMonoidHom_apply]
        have := hxC l l.2
        show (x : H) * l * (x : H)⁻¹ = l
        rw [← this]
        group
  have hcord : orderOf c = p := orderOf_eq_prime hcp hc1
  have hkcard : Nat.card f.ker = p := by
    rw [hker, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe ((Subgroup.zpowers_le).mpr hcA)).toEquiv, Nat.card_zpowers,
      hcord]
  have hEcard : Nat.card f.range = p ^ 2 := by
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hkcard, hAcard] at h1
    have hp0 : 0 < p := hp.pos
    have : p * Nat.card f.range = p * p ^ 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  have hEinner : f.range ⊓ innerAut (↥J ⧸ Subgroup.center ↥J) = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨⟨x, rfl⟩, ⟨q, hq'⟩⟩
    have hxsup : (x : H) ∈ J ⊔ Subgroup.centralizer (J : Set H) :=
      mem_sup_of_inner hperf (hAN x.2) hq'.symm
    have hxc : (x : H) ∈ Subgroup.zpowers c := hCA (x : H) x.2 hxsup
    have hx1 : x ∈ f.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hxc
    rw [MonoidHom.mem_ker.mp hx1]
    exact Subgroup.one_mem _
  refine hPlane hrank f.range (isElementaryAbelian_range hAe f) hEcard hEinner ?_
  rintro _ ⟨x, rfl⟩
  by_cases hxsup : (x : H) ∈ J ⊔ Subgroup.centralizer (J : Set H)
  · intro _ hninn
    obtain ⟨q, hq'⟩ := PlaneInner.centerQuotientConj_inner_of_mem_sup (hAN x.2) hxsup
    exact absurd ⟨q, hq'.symm⟩ hninn
  · have hxp : (x : H) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) (x : H) x.2
    have hxc : (x : H) * c = c * (x : H) := by
      have h1 := hAe.is_comm.comm x ⟨c, hcA⟩
      exact congrArg Subtype.val h1
    exact localRankAut_of_localRank he hp hnZ (hAN x.2) hxp hxsup hcC hc1 hcp hxc



theorem planeNoInnerPartTag_of_T (t : StatedLieTag) (h : Sec66T_K2 t) :
    ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (J A : Subgroup H) (c : H), p.Prime → 5 ≤ p →
      CFSG.Assembly.RankThreeEven.localRank p H ≤ 3 → CFSG.IsQuasisimple ↥J →
      (∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧ LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 f) →
      ¬ p ∣ Nat.card (Subgroup.center ↥J) →
      A ≤ Subgroup.normalizer (J : Set H) → IsElementaryAbelian p A → Nat.card A = p ^ 3 →
      c ∈ A → c ≠ 1 → c ∈ Subgroup.centralizer (J : Set H) →
      (∀ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c) → False := by
  intro H _ _ p J A c hp hp5 he hq hmodel hnZ hAN hAe hAcard hcA hc1 hcC hCA
  exact planeNoInnerPart_of_planeT H p J A c hp hp5 he hq hnZ (h _ p hp hp5 hmodel) hAN hAe
    hAcard hcA hc1 hcC hCA

theorem evenOuterPlaneNoInnerPartTag_of_T (t : StatedLieTag) (h : Sec66T_K2 t) :
    EvenOuterPlaneNoInnerPartTag t := by
  intro H _ _ he p J A c hp hp5 hq hmodel hnZ hAN hAe hAcard hcA hc1 hcC hCA _hS
  exact planeNoInnerPartTag_of_T t h H p J A c hp hp5
    ((CFSG.RankThree.OddKernel.localRank_le_evenRank hp (by omega)).trans he) hq hmodel hnZ hAN hAe
    hAcard hcA hc1 hcC hCA

theorem sec6Six_of_T (hS : SchreierFor InCatalog) (h1 : ∀ t, Sec66T_K1 t)
    (h2 : ∀ t, Sec66T_K2 t) : Sec6SixFieldAutomorphismPlane :=
  sec6Six_of_inputs hS
    (evenOuterElementIsFieldAut_of_tags fun t => evenOuterElementIsFieldAutTag_of_T t (h1 t))
    (evenOuterPlaneNoInnerPart_of_tags fun t => evenOuterPlaneNoInnerPartTag_of_T t (h2 t))

end CFSG.RankThree.PartOne.Sec66T
