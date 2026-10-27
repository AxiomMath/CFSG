module

public import CFSG.Quasithin.Vol2.E2SevenCases
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzComp
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.E2SolvTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isQuasisimple_of_simple {Q : Type} [Group Q] [Group.IsPerfect Q] (hs : IsSimpleGroup Q)
    (hnab : ∃ a b : Q, a * b ≠ b * a) : CFSG.IsQuasisimple Q := by
  have hZ := center_eq_bot_of_simple' hs hnab
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨inferInstance, (MulEquiv.isSimpleGroup_congr e).mpr hs, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

omit [Finite G] in
noncomputable def cjSubEquiv (g : G) (K : Subgroup G) : ↥K ≃* ↥(cjSub g K) :=
  K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

omit [Finite G] in
theorem cjSub_cjSub (a b : G) (K : Subgroup G) : cjSub a (cjSub b K) = cjSub (a * b) K := by
  ext x
  simp only [mem_cjSub, mul_inv_rev, mul_assoc]

omit [Finite G] in
theorem cjSub_self_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) : cjSub g H = H := by
  ext x
  rw [mem_cjSub]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg

omit [Finite G] in
theorem mem_normalizer_of_cjSub_eq {N : Subgroup G} {g : G} (h : cjSub g N = N) :
    g ∈ Subgroup.normalizer (N : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

omit [Finite G] in
theorem mem_cComp_cjSub {H K : Subgroup G} (hK : K ∈ cComp H) {g : G} (hg : g ∈ H) :
    cjSub g K ∈ cComp H := by
  have h1 := cComp_map_mulEquiv (MulAut.conj g) hK
  have h2 : H.map (MulAut.conj g).toMonoidHom = H := cjSub_self_of_mem hg
  rw [h2] at h1
  exact h1

omit [Finite G] in
theorem commute_of_commutator_eq_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) {a b : G}
    (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a :=
  ((Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha)) b hb).symm

omit [Finite G] in
theorem eq_one_of_forall_commute {K : Subgroup G} (hs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) {x : G} (hx : x ∈ K) (hc : ∀ y ∈ K, x * y = y * x) :
    x = 1 := by
  have hZ := center_eq_bot_of_simple' hs hnab
  have hxZ : (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact congrArg Subtype.val hxZ

omit [Finite G] in
theorem nonabelian_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hnab : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

omit [Finite G] in
theorem isElemAbelian_sup_of_commute {p : ℕ} {A B : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian p A) (hB : CFSG.Assembly.IsElemAbelian p B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : CFSG.Assembly.IsElemAbelian p (A ⊔ B) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

omit [Finite G] in
theorem isElemAbelian_zpowers {p : ℕ} {x : G} (hx : orderOf x = p) :
    CFSG.Assembly.IsElemAbelian p (Subgroup.zpowers x) :=
  CFSG.Open.isElemAbelian_zpowers (hx ▸ pow_orderOf_eq_one x)

theorem le_pRank_top_of_le {p k : ℕ} (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : CFSG.Assembly.IsElemAbelian p E) (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Assembly.pRank p (⊤ : Subgroup ↥H) := by
  let e := Subgroup.subgroupOfEquivOfLe hEH
  refine le_csSup ⟨Nat.card ↥H, ?_⟩ ⟨E.subgroupOf H, le_top, ⟨?_, fun x hx => ?_⟩, ?_⟩
  · rintro r ⟨B, -, -, hB⟩
    calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card ↥H := Subgroup.card_le_card_group B
  · refine ⟨⟨fun x y => e.injective ?_⟩⟩
    rw [map_mul, map_mul]
    exact hE.1.is_comm.comm (e x) (e y)
  · have := hE.2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext (by simpa using this)
  · rw [← hk]
    exact Nat.card_congr e.toEquiv

theorem three_le_pRank_of_three {p : ℕ} (hp : p.Prime) {H A₁ A₂ A₃ : Subgroup G} {x₁ x₂ x₃ : G}
    (h₁ : x₁ ∈ A₁) (h₂ : x₂ ∈ A₂) (h₃ : x₃ ∈ A₃) (hA₁ : A₁ ≤ H) (hA₂ : A₂ ≤ H) (hA₃ : A₃ ≤ H)
    (ho₁ : orderOf x₁ = p) (ho₂ : orderOf x₂ = p) (ho₃ : orderOf x₃ = p)
    (c₁₂ : ⁅A₁, A₂⁆ = ⊥) (c₁₃ : ⁅A₁, A₃⁆ = ⊥) (c₂₃ : ⁅A₂, A₃⁆ = ⊥)
    (d₁₂ : A₁ ⊓ A₂ = ⊥) (d₃ : A₃ ⊓ (A₁ ⊔ A₂) = ⊥) :
    3 ≤ CFSG.Assembly.pRank p (⊤ : Subgroup ↥H) := by
  have hZ₁ : Subgroup.zpowers x₁ ≤ A₁ := Subgroup.zpowers_le.mpr h₁
  have hZ₂ : Subgroup.zpowers x₂ ≤ A₂ := Subgroup.zpowers_le.mpr h₂
  have hZ₃ : Subgroup.zpowers x₃ ≤ A₃ := Subgroup.zpowers_le.mpr h₃
  have hc₁₂ : ∀ a ∈ Subgroup.zpowers x₁, ∀ b ∈ Subgroup.zpowers x₂, a * b = b * a :=
    fun a ha b hb => commute_of_commutator_eq_bot c₁₂ (hZ₁ ha) (hZ₂ hb)
  have hE₁₂ := isElemAbelian_sup_of_commute (isElemAbelian_zpowers ho₁)
    (isElemAbelian_zpowers ho₂) hc₁₂
  have hle₁₂ : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ≤ A₁ ⊔ A₂ := sup_le_sup hZ₁ hZ₂
  have hc₃ : ∀ a ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, ∀ b ∈ Subgroup.zpowers x₃,
      a * b = b * a := by
    have hcent : A₁ ⊔ A₂ ≤ Subgroup.centralizer (A₃ : Set G) :=
      sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp c₁₃)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp c₂₃)
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp (hcent (hle₁₂ ha))) b (hZ₃ hb)).symm
  have hE := isElemAbelian_sup_of_commute hE₁₂ (isElemAbelian_zpowers ho₃) hc₃
  have hcard₁₂ : Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) = p ^ 2 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (fun b hb => mem_normalizer_of_forall_commute fun a ha => (hc₁₂ a ha b hb).symm)
      (by
        rw [Subgroup.disjoint_def]
        intro x hx1 hx2
        have : x ∈ A₁ ⊓ A₂ := ⟨hZ₁ hx1, hZ₂ hx2⟩
        rwa [d₁₂, Subgroup.mem_bot] at this),
      Nat.card_zpowers, Nat.card_zpowers, ho₁, ho₂]
    ring
  have hcard : Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃) =
      p ^ 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (fun b hb => mem_normalizer_of_forall_commute fun a ha => (hc₃ a ha b hb).symm)
      (by
        rw [Subgroup.disjoint_def]
        intro x hx1 hx2
        have : x ∈ A₃ ⊓ (A₁ ⊔ A₂) := ⟨hZ₃ hx2, hle₁₂ hx1⟩
        rwa [d₃, Subgroup.mem_bot] at this),
      hcard₁₂, Nat.card_zpowers, ho₃]
    ring
  exact le_pRank_top_of_le hp.one_lt
    (sup_le (sup_le (hZ₁.trans hA₁) (hZ₂.trans hA₂)) (hZ₃.trans hA₃)) hE hcard

theorem cjSub_eq_or_eq_of_sqtk {H K : Subgroup G} (hsq : SQTKGroup ↥H) (hKc : K ∈ cComp H)
    (hs : IsSimpleGroup ↥K) (hnab : ∃ a b : ↥K, a * b ≠ b * a) {t : G} (ht : t ∈ H)
    (hne : cjSub t K ≠ K) {s : G} (hsH : s ∈ H) : cjSub s K = K ∨ cjSub s K = cjSub t K := by
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  have : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
  have hq : CFSG.IsQuasisimple ↥K := isQuasisimple_of_simple hs hnab
  have hqt := CFSG.LocalCores.isQuasisimple_of_mulEquiv (cjSubEquiv t K) hq
  have hqs := CFSG.LocalCores.isQuasisimple_of_mulEquiv (cjSubEquiv s K) hq
  have hKt := mem_cComp_cjSub hKc ht
  have hKs := mem_cComp_cjSub hKc hsH
  have c₁₂ : ⁅K, cjSub t K⁆ = ⊥ :=
    (H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple hKc hKt hq hqt).resolve_left
      (Ne.symm hne)
  have c₁₃ : ⁅K, cjSub s K⁆ = ⊥ :=
    (H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple hKc hKs hq hqs).resolve_left
      (Ne.symm h1)
  have c₂₃ : ⁅cjSub t K, cjSub s K⁆ = ⊥ :=
    (H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple hKt hKs hqt hqs).resolve_left
      (fun h3 => h2 h3.symm)
  have hss : IsSimpleGroup ↥(cjSub s K) := (MulEquiv.isSimpleGroup_congr (cjSubEquiv s K)).mp hs
  have hnabs := nonabelian_of_mulEquiv (cjSubEquiv s K) hnab
  have d₁₂ : K ⊓ cjSub t K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxt⟩
    exact (Subgroup.mem_bot).mpr (eq_one_of_forall_commute hs hnab hxK fun y hy =>
      (commute_of_commutator_eq_bot c₁₂ hy hxt).symm)
  have d₃ : cjSub s K ⊓ (K ⊔ cjSub t K) = ⊥ := by
    have hcent : K ⊔ cjSub t K ≤ Subgroup.centralizer (cjSub s K : Set G) :=
      sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp c₁₃)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp c₂₃)
    rw [eq_bot_iff]
    rintro x ⟨hxs, hxN⟩
    exact (Subgroup.mem_bot).mpr (eq_one_of_forall_commute hss hnabs hxs fun y hy =>
      ((Subgroup.mem_centralizer_iff.mp (hcent hxN)) y hy).symm)
  obtain ⟨p, hp, hpd, hp2⟩ : ∃ p, p.Prime ∧ p ∣ Nat.card ↥K ∧ p ≠ 2 := by
    by_contra hno
    push Not at hno
    apply not_isPGroup_two_of_simple hs hnab
    refine IsPGroup.of_card (n := (Nat.card ↥K).primeFactorsList.length) ?_
    exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdd => hno d hd hdd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hx₁ : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  have hconj : ∀ g : G, orderOf (g * (x : G) * g⁻¹) = p := fun g => by
    rw [← hx₁, ← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
  have hmem : ∀ g : G, g * (x : G) * g⁻¹ ∈ cjSub g K := fun g => by
    rw [mem_cjSub]
    simp [mul_assoc]
  have h3 := three_le_pRank_of_three hp x.2 (hmem t) (hmem s) (le_of_mem_cComp hKc)
    (le_of_mem_cComp hKt) (le_of_mem_cComp hKs) hx₁ (hconj t) (hconj s) c₁₂ c₁₃ c₂₃ d₁₂ d₃
  have h4 := hsq.1 p hp hp2
  omega

theorem inf_centralizer_eq_bot_of_center {H T M : Subgroup G} (hmp : MinParabolic H T M)
    (hJ : kerIn M H = ⊥) {N : Subgroup G} (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hZ : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x = 1) (hNT : N ⊔ T = H) :
    H ⊓ Subgroup.centralizer (N : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := H ⊓ Subgroup.centralizer (N : Set G) with hC
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := hmp.isSylow.1.trans hHN
  have hpow : ∀ x ∈ H, ∃ m : ℕ, x ^ 2 ^ m ∈ N := by
    intro x hx
    have hx' : x ∈ ((T ⊔ N : Subgroup G) : Set G) := by
      rw [sup_comm, hNT]
      exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTN] at hx'
    obtain ⟨s, hs, n, hn, hsn⟩ := hx'
    replace hsn : s * n = x := hsn
    subst hsn
    obtain ⟨m, hm⟩ := hmp.isSylow.2.1 ⟨s, hs⟩
    have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine ⟨m, ?_⟩
    have key : ∀ j : ℕ, ∃ nj ∈ N, (s * n) ^ j = s ^ j * nj := by
      intro j
      induction j with
      | zero => exact ⟨1, N.one_mem, by simp⟩
      | succ j ih =>
        obtain ⟨nj, hnj, hnj'⟩ := ih
        refine ⟨(s⁻¹ * nj * s) * n, N.mul_mem ?_ hn, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem hs)) nj).mp hnj
          simpa [mul_assoc] using this
        · rw [pow_succ, hnj', pow_succ]
          group
    obtain ⟨nj, hnj, hnj'⟩ := key (2 ^ m)
    rw [hnj', hsm, one_mul]
    exact hnj
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨m, hm⟩ := hpow c c.2.1
    refine ⟨m, Subtype.ext ?_⟩
    have hcm : (c : G) ^ 2 ^ m ∈ Subgroup.centralizer (N : Set G) :=
      (Subgroup.centralizer (N : Set G)).pow_mem c.2.2 _
    have := hZ _ hm fun y hy => ((Subgroup.mem_centralizer_iff.mp hcm) y hy).symm
    simpa using this
  have hCn : H ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hxH, hx⟩
      refine ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), fun k hk => ?_⟩
      have hk' : g⁻¹ * k * g ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hg)) k).mp hk
        simpa using this
      have := hx _ hk'
      calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
        _ = g * x * g⁻¹ * k := by group
    · rintro ⟨hxH, hx⟩
      refine ⟨?_, fun k hk => ?_⟩
      · have := H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg
        simpa [mul_assoc] using this
      · have hk' : g * k * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hg) k).mp hk
        have := hx _ hk'
        calc k * x = g⁻¹ * ((g * k * g⁻¹) * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * (g * k * g⁻¹)) * g := by rw [this]
          _ = x * k := by group
  have hle : C ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCn hC2
  have h2 := hle.trans hmp.pCoreOf_le_kerIn
  rw [hJ] at h2
  exact le_bot_iff.mp h2

structure PairCase (H T K : Subgroup G) (t : G) : Prop where
  mem : t ∈ T
  comp : K ∈ cComp H
  comp' : cjSub t K ∈ cComp H
  ne : cjSub t K ≠ K
  simple : IsSimpleGroup ↥K
  nonab : ∃ a b : ↥K, a * b ≠ b * a
  comm : ⁅K, cjSub t K⁆ = ⊥
  inf : K ⊓ cjSub t K = ⊥
  orbit : ∀ s ∈ H, cjSub s K = K ∨ cjSub s K = cjSub t K
  norm : H ≤ Subgroup.normalizer ((K ⊔ cjSub t K : Subgroup G) : Set G)
  cent : H ⊓ Subgroup.centralizer ((K ⊔ cjSub t K : Subgroup G) : Set G) = ⊥

variable {H T M V : Subgroup G}

theorem pairCase_of (h : Hyp28 H T M V) (hJ : kerIn M H = ⊥) {K : Subgroup G}
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) {t : G} (htT : t ∈ T) (hne : cjSub t K ≠ K)
    (hs : IsSimpleGroup ↥(star M H K)) : PairCase H T K t := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  have htH : t ∈ H := hTH htT
  have hsK : IsSimpleGroup ↥K :=
    (MulEquiv.isSimpleGroup_congr (equivStarOfKerInEqBot hJ hKH)).mpr hs
  have : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    have : Nontrivial ↥K := hsK.toNontrivial
    exact nonabelian_of_perfect_of_surjective (MonoidHom.id ↥K) Function.surjective_id
  have hq : CFSG.IsQuasisimple ↥K := isQuasisimple_of_simple hsK hnab
  have hKt := mem_cComp_cjSub hKc htH
  have hKtH : cjSub t K ≤ H := le_of_mem_cComp hKt
  have hqt := CFSG.LocalCores.isQuasisimple_of_mulEquiv (cjSubEquiv t K) hq
  have hcomm : ⁅K, cjSub t K⁆ = ⊥ :=
    (H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple hKc hKt hq hqt).resolve_left
      (Ne.symm hne)
  have hst : IsSimpleGroup ↥(cjSub t K) :=
    (MulEquiv.isSimpleGroup_congr (cjSubEquiv t K)).mp hsK
  have hnabt := nonabelian_of_mulEquiv (cjSubEquiv t K) hnab
  have hinf : K ⊓ cjSub t K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxt⟩
    exact (Subgroup.mem_bot).mpr (eq_one_of_forall_commute hsK hnab hxK fun y hy =>
      (commute_of_commutator_eq_bot hcomm hy hxt).symm)
  have horb : ∀ s ∈ H, cjSub s K = K ∨ cjSub s K = cjSub t K := fun s hs =>
    cjSub_eq_or_eq_of_sqtk h.sqtk hKc hsK hnab htH hne hs
  have hnorm : H ≤ Subgroup.normalizer ((K ⊔ cjSub t K : Subgroup G) : Set G) := by
    intro s hs
    apply mem_normalizer_of_cjSub_eq
    rw [cjSub_sup, cjSub_cjSub]
    have hne' : cjSub s K ≠ cjSub (s * t) K := by
      intro heq
      apply hne
      have h3 := congrArg (cjSub s⁻¹) heq
      rw [cjSub_cjSub, cjSub_cjSub, inv_mul_cancel_left, inv_mul_cancel, cjSub_one] at h3
      exact h3.symm
    rcases horb s hs with h1 | h1 <;> rcases horb (s * t) (H.mul_mem hs htH) with h2 | h2
    · exact absurd (h1.trans h2.symm) hne'
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
    · exact absurd (h1.trans h2.symm) hne'
  have hKN : K ≤ Subgroup.normalizer (cjSub t K : Set G) := fun a ha =>
    mem_normalizer_of_forall_commute fun b hb => commute_of_commutator_eq_bot hcomm ha hb
  have hZ : ∀ x ∈ K ⊔ cjSub t K, (∀ y ∈ K ⊔ cjSub t K, x * y = y * x) → x = 1 := by
    intro x hx hc
    have hx' : x ∈ ((K ⊔ cjSub t K : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ hKN] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := hx'
    replace hab : a * b = x := hab
    subst hab
    have ha1 : a = 1 := eq_one_of_forall_commute hsK hnab ha fun y hy => by
      have h1 := hc y (Subgroup.mem_sup_left hy)
      have h2 : b * y = y * b := (commute_of_commutator_eq_bot hcomm hy hb).symm
      have h3 : a * y * b = y * a * b := by
        calc a * y * b = a * (y * b) := by group
          _ = a * (b * y) := by rw [h2]
          _ = a * b * y := by group
          _ = y * (a * b) := h1
          _ = y * a * b := by group
      exact mul_right_cancel h3
    have hb1 : b = 1 := eq_one_of_forall_commute hst hnabt hb fun y hy => by
      have h1 := hc y (Subgroup.mem_sup_right hy)
      rw [ha1, one_mul] at h1
      exact h1
    rw [ha1, hb1, one_mul]
  have hNT : K ⊔ cjSub t K ⊔ T = H := le_antisymm (sup_le (sup_le hKH hKtH) hTH) (by
    calc H = K ⊔ T := hHK
      _ ≤ K ⊔ cjSub t K ⊔ T := sup_le_sup_right le_sup_left _)
  exact ⟨htT, hKc, hKt, hne, hsK, hnab, hcomm, hinf, horb, hnorm,
    inf_centralizer_eq_bot_of_center h.minParabolic hJ hnorm hZ hNT⟩

omit [Finite G] in
theorem starMap_injective_of_kerIn_eq_bot (hJ : kerIn M H = ⊥) :
    Function.Injective (E2P.starMap M H) := by
  rw [← MonoidHom.ker_eq_bot_iff, E2P.ker_starMap, hJ, Subgroup.bot_subgroupOf]

omit [Finite G] in
theorem starMap_mem_star_iff (hJ : kerIn M H = ⊥) {X : Subgroup G} {x : G} (hxH : x ∈ H) :
    E2P.starMap M H ⟨x, hxH⟩ ∈ star M H X ↔ x ∈ X := by
  refine ⟨fun hx => ?_, starMap_mem_star hxH⟩
  obtain ⟨y, hy, hyx⟩ := hx
  have := starMap_injective_of_kerIn_eq_bot hJ hyx
  rw [this] at hy
  exact Subgroup.mem_subgroupOf.mp hy

omit [Finite G] in
theorem star_injective_of_kerIn_eq_bot (hJ : kerIn M H = ⊥) {A B : Subgroup G} (hA : A ≤ H)
    (hB : B ≤ H) (h : star M H A = star M H B) : A = B := by
  have h1 : A.subgroupOf H = B.subgroupOf H :=
    Subgroup.map_injective (starMap_injective_of_kerIn_eq_bot hJ) h
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hA, inf_of_le_left hB] at h1
  exact h1

omit [Finite G] in
theorem conj_mem_of_starMap_mem_normalizer (hJ : kerIn M H = ⊥) {X : Subgroup G} (hX : X ≤ H)
    {k : G} (hkH : k ∈ H)
    (hk : E2P.starMap M H ⟨k, hkH⟩ ∈ Subgroup.normalizer (star M H X : Set (StarQuot M H)))
    {z : G} (hz : z ∈ X) : k * z * k⁻¹ ∈ X := by
  have hzH := hX hz
  have hkz : k * z * k⁻¹ ∈ H := H.mul_mem (H.mul_mem hkH hzH) (H.inv_mem hkH)
  have h1 := (Subgroup.mem_normalizer_iff.mp hk (E2P.starMap M H ⟨z, hzH⟩)).mp
    ((starMap_mem_star_iff hJ hzH).mpr hz)
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  have e : (⟨k, hkH⟩ * ⟨z, hzH⟩ * (⟨k, hkH⟩ : ↥H)⁻¹ : ↥H) = ⟨k * z * k⁻¹, hkz⟩ := rfl
  rw [e] at h1
  exact (starMap_mem_star_iff hJ hkz).mp h1

omit [Finite G] in
theorem star_inf_normalizer_of_kerIn_eq_bot (hJ : kerIn M H = ⊥) {K X : Subgroup G}
    (hX : X ≤ H) :
    star M H (K ⊓ Subgroup.normalizer (X : Set G)) =
      star M H K ⊓ Subgroup.normalizer (star M H X : Set (StarQuot M H)) := by
  apply le_antisymm
  · rintro _ ⟨⟨k, hkH⟩, hk, rfl⟩
    replace hk : k ∈ K ⊓ Subgroup.normalizer (X : Set G) := Subgroup.mem_subgroupOf.mp hk
    exact ⟨starMap_mem_star hkH hk.1, starMap_mem_normalizer hkH hk.2⟩
  · rintro _ ⟨⟨⟨k, hkH⟩, hkK, rfl⟩, hy⟩
    replace hkK : k ∈ K := Subgroup.mem_subgroupOf.mp hkK
    have hkinv : E2P.starMap M H ⟨k⁻¹, H.inv_mem hkH⟩ ∈
        Subgroup.normalizer (star M H X : Set (StarQuot M H)) := by
      have : E2P.starMap M H ⟨k⁻¹, H.inv_mem hkH⟩ = (E2P.starMap M H ⟨k, hkH⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [this]
      exact Subgroup.inv_mem _ hy
    refine ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr ⟨hkK, ?_⟩, rfl⟩
    show k ∈ Subgroup.normalizer (X : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact conj_mem_of_starMap_mem_normalizer hJ hX hkH hy
    · intro hz
      have := conj_mem_of_starMap_mem_normalizer hJ hX (H.inv_mem hkH) hkinv hz
      simpa [mul_assoc] using this

omit [Finite G] in
theorem star_inf_centralizer_of_kerIn_eq_bot (hJ : kerIn M H = ⊥) {K X : Subgroup G}
    (hX : X ≤ H) :
    star M H (K ⊓ Subgroup.centralizer (X : Set G)) =
      star M H K ⊓ Subgroup.centralizer (star M H X : Set (StarQuot M H)) := by
  apply le_antisymm
  · rintro _ ⟨⟨k, hkH⟩, hk, rfl⟩
    replace hk : k ∈ K ⊓ Subgroup.centralizer (X : Set G) := Subgroup.mem_subgroupOf.mp hk
    refine ⟨starMap_mem_star hkH hk.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨⟨x, hxH⟩, hx, rfl⟩
    replace hx : x ∈ X := Subgroup.mem_subgroupOf.mp hx
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hk.2) x hx)
  · rintro _ ⟨⟨⟨k, hkH⟩, hkK, rfl⟩, hy⟩
    replace hkK : k ∈ K := Subgroup.mem_subgroupOf.mp hkK
    refine ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr ⟨hkK, ?_⟩, rfl⟩
    show k ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxH := hX hx
    have h1 := (Subgroup.mem_centralizer_iff.mp hy) (E2P.starMap M H ⟨x, hxH⟩)
      ((starMap_mem_star_iff hJ hxH).mpr hx)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (starMap_injective_of_kerIn_eq_bot hJ h1)

theorem star_inf_eq_of_isBorelIn' {K : Subgroup G} (h : MinParabolic H T M)
    (hS : IsSylowTwoOf (star M H T ⊓ star M H K) (star M H K))
    (hB : IsBorelIn (star M H K) (star M H (M ⊓ K))) :
    star M H M ⊓ star M H K = star M H K ⊓
      Subgroup.normalizer ((star M H T ⊓ star M H K : Subgroup (StarQuot M H)) : Set _) := by
  have := E2P.finite_starQuot M H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSsyl, hSeq⟩ := hB
  rw [E2P.star_inf_M] at hSeq
  have hTM : star M H T ⊓ star M H K ≤ star M H M ⊓ star M H K :=
    inf_le_inf_right _ (star_mono h.le)
  rw [hSeq] at hTM
  have hTS : star M H T ⊓ star M H K ≤ S := by
    have hsup : IsPGroup 2 ↥((star M H T ⊓ star M H K) ⊔ S) :=
      IsPGroup.to_sup_of_normal_right' hS.2.1 hSsyl.2.1 (hTM.trans inf_le_right)
    have hle : (star M H T ⊓ star M H K) ⊔ S ≤ star M H K := sup_le hS.1 hSsyl.1
    have := (A4.isSylowTwoOf_iff_maximal.mp hSsyl).2.2 _ hle hsup le_sup_right
    exact le_sup_left.trans this
  have hSeq' : S = star M H T ⊓ star M H K :=
    le_antisymm ((A4.isSylowTwoOf_iff_maximal.mp hS).2.2 S hSsyl.1 hSsyl.2.1 hTS) hTS
  rw [hSeq, hSeq']

theorem inf_eq_of_isBorelIn_star (h : MinParabolic H T M) (hJ : kerIn M H = ⊥)
    {K : Subgroup G} (hKs : IsSubnormal K H) (hKH : K ≤ H)
    (hB : IsBorelIn (star M H K) (star M H (M ⊓ K))) :
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK := E2P.star_inf_T (M := M) h.isSylow hKs hKH
  have hS0 := E2P.isSylowTwoOf_inf_of_subnormal h.isSylow hKs
  have hS : IsSylowTwoOf (star M H T ⊓ star M H K) (star M H K) := by
    rw [← hTK]
    refine ⟨star_mono inf_le_right, ?_, ?_⟩
    · have h2 : IsPGroup 2 ↥((T ⊓ K).subgroupOf H) :=
        hS0.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hKH)).symm
      exact h2.map _
    · rw [show ((star M H (T ⊓ K)).subgroupOf (star M H K)).index =
          (star M H (T ⊓ K)).relIndex (star M H K) from rfl,
        relIndex_star (by rw [hJ]; exact bot_le) (by rw [hJ]; exact bot_le) hKH]
      exact hS0.2.2
  have h1 := star_inf_eq_of_isBorelIn' h hS hB
  rw [← E2P.star_inf_M, ← hTK, ← star_inf_normalizer_of_kerIn_eq_bot hJ
    (inf_le_right.trans hKH)] at h1
  exact star_injective_of_kerIn_eq_bot hJ (inf_le_right.trans hKH) (inf_le_left.trans hKH) h1

omit [Finite G] in
theorem inf_eq_of_star_centralizer (hJ : kerIn M H = ⊥) {K : Subgroup G} (hKH : K ≤ H)
    (hMK : star M H (M ⊓ K) = star M H K ⊓ Subgroup.centralizer
      ((star M H (T ⊓ K) ⊓ Subgroup.centralizer (star M H (T ⊓ K) : Set (StarQuot M H)) :
        Subgroup (StarQuot M H)) : Set (StarQuot M H))) :
    M ⊓ K = K ⊓ Subgroup.centralizer
      ((T ⊓ K ⊓ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hTKH : T ⊓ K ≤ H := inf_le_right.trans hKH
  have hZH : T ⊓ K ⊓ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G) ≤ H :=
    inf_le_left.trans hTKH
  have h1 := star_inf_centralizer_of_kerIn_eq_bot (K := T ⊓ K) hJ hTKH
  have h2 := star_inf_centralizer_of_kerIn_eq_bot (K := K) hJ hZH
  rw [h1] at h2
  rw [← h2] at hMK
  exact star_injective_of_kerIn_eq_bot hJ (inf_le_right.trans hKH) (inf_le_left.trans hKH) hMK

omit [Finite G] in
theorem autCard_star_of_kerIn_eq_bot (hJ : kerIn M H = ⊥) {X K : Subgroup G} (hXH : X ≤ H)
    (hKH : K ≤ H) : autCard (star M H X) (star M H K) = autCard X K := by
  unfold autCard
  have h1 := star_inf_normalizer_of_kerIn_eq_bot (K := X) hJ hKH
  have h2 := star_inf_centralizer_of_kerIn_eq_bot
    (K := X ⊓ Subgroup.normalizer (K : Set G)) hJ hKH
  rw [← h1, ← h2, relIndex_star (by rw [hJ]; exact bot_le) (by rw [hJ]; exact bot_le)
    (inf_le_left.trans hXH)]

omit [Finite G] in
theorem isPSL_of_mulEquiv_gen {A B : Type} [Group A] [Group B] (e : A ≃* B) {n p f : ℕ}
    (h : IsPSL n p f B) : IsPSL n p f A := by
  obtain ⟨hadm, K, h1, h2, hK, ⟨g⟩⟩ := h
  exact ⟨hadm, K, h1, h2, hK, ⟨e.trans g⟩⟩

theorem exists_inverted_of_not_mem_pCore {X : Type} [Group X] [Finite X] {x : X}
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxO : x ∉ CFSG.pCore 2 X) :
    ∃ c : X, ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf c = p ∧ x * c * x⁻¹ = c⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2' : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hx2 hx1
  obtain ⟨g, hg⟩ : ∃ g : X, ¬ IsPGroup 2 (Subgroup.closure ({x, g * x * g⁻¹} : Set X)) := by
    by_contra hall
    push Not at hall
    exact hxO (CFSG.BaerSuzuki.baer_suzuki x hx2' hall)
  set w := g * x * g⁻¹ with hw
  have hw2 : w ^ 2 = 1 := by
    rw [hw, sq]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [← sq, hx2, mul_one, mul_inv_cancel]
  set c₀ := x * w with hc₀
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2])
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← sq, hw2])
  have hxc : x * c₀ * x⁻¹ = c₀⁻¹ := by
    rw [hc₀, mul_inv_rev, hxinv, hwinv]
    calc x * (x * w) * x = (x * x) * w * x := by group
      _ = w * x := by rw [← sq, hx2, one_mul]
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers c₀ : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (x * c₀ * x⁻¹) = _
    rw [hxc, Subgroup.zpowers_inv]
  have hnot2 : ¬ ∃ k : ℕ, c₀ ^ 2 ^ k = 1 := by
    rintro ⟨k, hk⟩
    apply hg
    have hc2 : IsPGroup 2 (Subgroup.zpowers c₀) := by
      refine IsPGroup.of_card (n := (orderOf c₀).factorization 2) ?_
      rw [Nat.card_zpowers]
      have hd : orderOf c₀ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      rw [hi', Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    have hsup := IsPGroup.to_sup_of_normal_right' hx2' hc2 (Subgroup.zpowers_le.mpr hxN)
    refine hsup.to_le ((Subgroup.closure_le _).mpr ?_)
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have e : w = x⁻¹ * c₀ := by rw [hc₀, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hn0 : orderOf c₀ ≠ 0 := (orderOf_pos c₀).ne'
  obtain ⟨p, hp, hpd, hp2⟩ : ∃ p, p.Prime ∧ p ∣ orderOf c₀ ∧ p ≠ 2 := by
    by_contra hno
    push Not at hno
    apply hnot2
    refine ⟨(orderOf c₀).primeFactorsList.length, ?_⟩
    rw [← Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {d} hd hdd => hno d hd hdd)]
    exact pow_orderOf_eq_one c₀
  refine ⟨c₀ ^ (orderOf c₀ / p), p, hp, hp2, orderOf_pow_orderOf_div hn0 hpd, ?_⟩
  have := map_pow (MulAut.conj x) c₀ (orderOf c₀ / p)
  rw [MulAut.conj_apply, MulAut.conj_apply, hxc, inv_pow] at this
  exact this

theorem not_mem_pCore_of_simple {K : Subgroup G} (hs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) {x : ↥K} (hx1 : x ≠ 1) : x ∉ CFSG.pCore 2 ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hxm
  rcases hs.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 ↥K) with h0 | h0
  · rw [h0] at hxm
    exact hx1 ((Subgroup.mem_bot).mp hxm)
  · have hP2 : IsPGroup 2 ↥(pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
    have hPK : pCoreOf 2 K = K := by
      show (CFSG.Open.pCore 2 ↥K).map K.subtype = K
      rw [h0, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hPK] at hP2
    exact not_isPGroup_two_of_simple hs hnab hP2

theorem exists_isInIHTVC_of_pair_dihedral (h : Hyp28 H T M V) {K : Subgroup G} {t : G}
    (hP : PairCase H T K t) (hV : V = (V ⊓ K) ⊔ (V ⊓ cjSub t K))
    (h2 : Nat.card ↥(V ⊓ K) = 2) (hn : ∃ m : ℕ, E1.nParam H = m) :
    ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I := by
  have hnt : Nontrivial ↥(V ⊓ K) := Finite.one_lt_card_iff_nontrivial.mp (by rw [h2]; norm_num)
  obtain ⟨⟨v, hvVK⟩, hv1⟩ := exists_ne (1 : ↥(V ⊓ K))
  have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  have hvV : v ∈ V := hvVK.1
  have hvK : v ∈ K := hvVK.2
  have hv2 : v ^ 2 = 1 := h.elem.2 v hvV
  have hordv : orderOf v = 2 := orderOf_eq_prime hv2 hv1'
  have hVKv : V ⊓ K ≤ Subgroup.zpowers v := by
    have hle : Subgroup.zpowers v ≤ V ⊓ K := Subgroup.zpowers_le.mpr hvVK
    have hcard : Nat.card ↥(V ⊓ K) ≤ Nat.card (Subgroup.zpowers v) := by
      rw [Nat.card_zpowers, hordv, h2]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).ge
  set x : ↥K := ⟨v, hvK⟩ with hxdef
  have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa [hxdef] using hv2)
  have hx1 : x ≠ 1 := fun h1 => hv1' (congrArg Subtype.val h1)
  obtain ⟨c, p, hp, hp2, hcord, hxc⟩ :=
    exists_inverted_of_not_mem_pCore hx2 hx1 (not_mem_pCore_of_simple hP.simple hP.nonab hx1)
  have hvc : v * (c : G) * v⁻¹ = (c : G)⁻¹ := by
    have := congrArg Subtype.val hxc
    simpa [hxdef] using this
  have hVU : V ≤ (V ⊓ cjSub t K) ⊔ Subgroup.zpowers v :=
    calc V = (V ⊓ K) ⊔ (V ⊓ cjSub t K) := hV
      _ ≤ Subgroup.zpowers v ⊔ (V ⊓ cjSub t K) := sup_le_sup_right hVKv _
      _ = (V ⊓ cjSub t K) ⊔ Subgroup.zpowers v := sup_comm _ _
  exact ⟨_, h.isInIHTVC_of_dihedral (U := V ⊓ cjSub t K) inf_le_left hvV hVU
    (le_of_mem_cComp hP.comp c.2)
    (fun u hu => commute_of_commutator_eq_bot hP.comm c.2 hu.2) hvc hp hp2 le_rfl
    (by rw [Subgroup.orderOf_coe, hcord, pow_one]) hn⟩

theorem exists_isInIHTVC_of_l2two (hKG4 : KGL2OddTwo) (h : Hyp28 H T M V)
    (hJ : kerIn M H = ⊥) {K : Subgroup G} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) {t : G}
    (htT : t ∈ T) (hne : cjSub t K ≠ K) (hM : M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hK : IsPSL 2 p 1 ↥(star M H K))
    (hMK : star M H (M ⊓ K) = star M H K ⊓ Subgroup.centralizer
      ((star M H (T ⊓ K) ⊓ Subgroup.centralizer (star M H (T ⊓ K) : Set (StarQuot M H)) :
        Subgroup (StarQuot M H)) : Set (StarQuot M H)))
    (haut : 8 < autCard (star M H T) (star M H K)) (hn1 : E1.nParam H = 1)
    (hV4 : 4 ≤ Nat.card V) : ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  have hs : IsSimpleGroup ↥(star M H K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hK).2
  have hP := pairCase_of h hJ hKc hHK htT hne hs
  have hK' : IsPSL 2 p 1 ↥K := isPSL_of_mulEquiv_gen (equivStarOfKerInEqBot hJ hKH) hK
  have hMK' := inf_eq_of_star_centralizer hJ hKH hMK
  have haut' : 8 < autCard T K := by rwa [autCard_star_of_kerIn_eq_bot hJ hTH hKH] at haut
  obtain ⟨hV, hVK⟩ := hKG4 G H T M K V t p h.minParabolic hJ htT hKH hne hP.norm hP.cent
    hP.inf hP.comm hHK.symm hp hp8 hK' hM hMK' haut' h.le_pCoreOf h.elem h.normal_T hV4
  exact exists_isInIHTVC_of_pair_dihedral h hP hV hVK ⟨1, by rw [hn1, Nat.cast_one]⟩

end E2

end CFSG.Quasithin
