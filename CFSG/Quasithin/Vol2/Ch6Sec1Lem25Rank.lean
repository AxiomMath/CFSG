module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.Glue
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

theorem le_pRank_of_isElemAbelian_ch625 {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : 1 < p)
    {H E : Subgroup X} (hEH : E ≤ H) (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := CFSG.SectionRank.le_pRank hp hEH hE hk

variable {G : Type} [Group G] [Finite G]

theorem center_KQ_eq_bot_of_card_le_two {K : Subgroup G}
    (h2 : Nat.card (Subgroup.center (KQ K)) ≤ 2) : Subgroup.center (KQ K) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center (KQ K) with hZ
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hZ2 : IsPGroup 2 Z := by
    refine IsPGroup.of_card (n := if Nat.card Z = 1 then 0 else 1) ?_
    have hpos : 0 < Nat.card Z := Nat.card_pos
    split_ifs with h
    · simpa using h
    · simp only [pow_one]
      omega
  set P := Z.comap π with hP
  have hPn : P.Normal := Subgroup.Normal.comap inferInstance π
  have hP2 : IsPGroup 2 P := by
    have hker : π.ker = CFSG.pCore 2 ↥K := QuotientGroup.ker_mk' _
    have hkerP : IsPGroup 2 π.ker := by
      rw [hker]
      exact CFSG.pCore_isPGroup
    exact IsPGroup.comap_of_ker_isPGroup hZ2 π hkerP
  have hPO : P ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hPn, hP2⟩
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
  have hkP : k ∈ P := hz
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hPO hkP

omit [Finite G] in
theorem isMulCommutative_sup_of_commute_ch625 {X : Type*} [Group X] {A B : Subgroup X}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have h1 : ∀ a ∈ A, A ⊔ B ≤ Subgroup.centralizer ({a} : Set X) := fun a ha =>
    sup_le (fun a' ha' => Subgroup.mem_centralizer_singleton_iff.mpr (hA a ha a' ha').symm)
      fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hAB a ha b hb).symm
  have h2 : ∀ b ∈ B, A ⊔ B ≤ Subgroup.centralizer ({b} : Set X) := fun b hb =>
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hAB a ha b hb))
      fun b' hb' => Subgroup.mem_centralizer_singleton_iff.mpr (hB b hb b' hb').symm
  intro x hx y hy
  have h3 : A ⊔ B ≤ Subgroup.centralizer ({y} : Set X) := by
    refine sup_le (fun a ha => ?_) fun b hb => ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (h1 a ha hy)).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (h2 b hb hy)).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (h3 hx)

theorem isElemAbelian_of_isElemAbelianOfRank_ch625 {X : Type*} [Group X] {p n : ℕ}
    [Fact p.Prime] {E : Subgroup X} (hE : IsElemAbelianOfRank p n ↥E) :
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ p = 1) ∧ Nat.card E = p ^ n := by
  obtain ⟨e⟩ := hE
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_, ?_⟩
  · have h1 : e ⟨a, ha⟩ * e ⟨b, hb⟩ = e ⟨b, hb⟩ * e ⟨a, ha⟩ := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  · have h1 : e (⟨a, ha⟩ ^ p) = 1 := by
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      simp
    have h2 := e.injective (h1.trans (map_one e).symm)
    simpa using congrArg Subtype.val h2
  · rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, ZMod.card]

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

include hI in
theorem false_of_inner_rank_two {x : G} (hx : x ∈ DL) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hxr : orderOf x = r) (hinn : phiK K ⟨x, d.DL_le_NK hI hx⟩ ∈ innAut (KBar K))
    (hZ : Subgroup.center (KQ K) = ⊥) {E : Subgroup (KBar K)} (hE : IsElemAbelianOfRank r 2 ↥E) :
    False := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hn := Subgroup.normalizer (ch6ZS T L V : Set G) with hHn
  set W := Hn ⊓ Subgroup.normalizer (K : Set G) with hW
  have hKW : K ≤ W := le_inf d.K_le_H Subgroup.le_normalizer
  have hxN := d.DL_le_NK hI hx
  have hxW : x ∈ W := ⟨d.hyp.DL_le_normalizer_ZS d.hall hx, hxN⟩
  have hOW : pCoreOf 2 K ≤ W := (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKW
  set N : Subgroup ↥W := (pCoreOf 2 K).subgroupOf W with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOW).mpr
    (inf_le_right.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  set μ : ↥W →* ↥W ⧸ N := QuotientGroup.mk' N with hμ
  set κ : ↥K →* ↥W ⧸ N := μ.comp (Subgroup.inclusion hKW) with hκ
  have hκ1 : ∀ k : ↥K, κ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hκ, MonoidHom.comp_apply, hμ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      hN, Subgroup.mem_subgroupOf]
    rfl
  obtain ⟨yb, hyb⟩ := hinn
  obtain ⟨y₁, rfl⟩ := piK_surjective K yb
  have hy₁N : (y₁ : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer y₁.2
  set c := x * (y₁ : G)⁻¹ with hc
  have hcN : c ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hy₁N)
  have hcW : c ∈ W := W.mul_mem hxW (W.inv_mem (hKW y₁.2))
  have hφc : phiK K ⟨c, hcN⟩ = 1 := by
    have e : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨x, hxN⟩ * (⟨y₁, hy₁N⟩)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_inv, ← hyb, phiK_of_mem K y₁, mul_inv_cancel]
  have hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K := (phiK_eq_one_iff d.quasi _).mp hφc
  set cb : ↥W ⧸ N := μ ⟨c, hcW⟩ with hcb
  have hcomm : ∀ k : ↥K, cb * κ k = κ k * cb := by
    intro k
    have h1 : μ (⟨c, hcW⟩ * Subgroup.inclusion hKW k * (⟨c, hcW⟩)⁻¹ *
        (Subgroup.inclusion hKW k)⁻¹) = 1 := by
      rw [hμ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
      exact hcK k k.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc cb * κ k = (cb * κ k * cb⁻¹ * (κ k)⁻¹) * (κ k * cb) := by group
      _ = κ k * cb := by rw [show cb * κ k * cb⁻¹ * (κ k)⁻¹ = 1 from h1, one_mul]
  have hcR : ∀ k : ↥K, cb ≠ κ k := by
    intro k hck
    have h1 : μ (⟨c, hcW⟩ * (Subgroup.inclusion hKW k)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hcb]
      exact mul_inv_eq_one.mpr hck
    rw [hμ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at h1
    have hcK' : c ∈ K := by
      have h2 := K.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 K h1) k.2
      simpa using h2
    have hxK : x ∈ K := by
      have h3 := K.mul_mem hcK' y₁.2
      simpa [hc] using h3
    have hxI : x ∈ DL ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) := ⟨hx, d.K_le_I hxK⟩
    rw [d.hyp.DL_inf_I d.hall, Subgroup.mem_bot] at hxI
    rw [hxI, orderOf_one] at hxr
    exact hr.one_lt.ne hxr
  have hy₁r : (piK K y₁) ^ r = 1 := by
    have h1 : MulAut.conj ((piK K y₁) ^ r) = 1 := by
      rw [map_pow, hyb, ← map_pow]
      have e : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ r = 1 :=
        Subtype.ext (by simp [← hxr, pow_orderOf_eq_one])
      rw [e, map_one]
    have h2 := mem_center_of_conj_eq_one h1
    rwa [d.center_KBar, Subgroup.mem_bot] at h2
  have hκy : (κ y₁) ^ r = 1 := by
    rw [← map_pow, hκ1]
    have h1 : piK K (y₁ ^ r) = 1 := by rw [map_pow, hy₁r]
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (y₁ ^ r) : KQ K) ∈ Subgroup.center (KQ K) := by
      have := (QuotientGroup.eq_one_iff _).mp h1
      exact this
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    rw [pCoreOf_two_eq_map_ch625]
    exact ⟨_, h2, rfl⟩
  have hcr : cb ^ r = 1 := by
    have hxb : μ ⟨x, hxW⟩ = cb * κ y₁ := by
      rw [hcb, hκ, MonoidHom.comp_apply, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [hc]
    have hx1 : (μ ⟨x, hxW⟩) ^ r = 1 := by
      rw [← map_pow]
      have e : (⟨x, hxW⟩ : ↥W) ^ r = 1 := Subtype.ext (by simp [← hxr, pow_orderOf_eq_one])
      rw [e, map_one]
    rw [hxb, (Commute.mul_pow (hcomm y₁) r), hκy, mul_one] at hx1
    exact hx1
  set eK : KBar K ≃* KQ K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot with heK
  set κ' : KQ K →* ↥W ⧸ N := QuotientGroup.lift (CFSG.pCore 2 ↥K) κ (fun k hk => by
    rw [MonoidHom.mem_ker, hκ1, pCoreOf_two_eq_map_ch625]
    exact ⟨k, hk, rfl⟩) with hκ'
  have hκ'inj : Function.Injective κ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker] at hq
    have h1 : κ k = 1 := hq
    rw [hκ1, pCoreOf_two_eq_map_ch625] at h1
    obtain ⟨k', hk', hkk⟩ := h1
    have : k' = k := Subtype.ext hkk
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, ← this]
    exact hk'
  have hinj : Function.Injective (κ'.comp eK.toMonoidHom) := hκ'inj.comp eK.injective
  set E₁ := E.map (κ'.comp eK.toMonoidHom) with hE₁
  obtain ⟨hEc, hEp, hEcard⟩ := isElemAbelian_of_isElemAbelianOfRank_ch625 hE
  have hE₁card : Nat.card E₁ = r ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective hinj, hEcard]
  have hE₁κ : ∀ z ∈ E₁, ∃ k : ↥K, z = κ k := by
    rintro _ ⟨w, -, rfl⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (eK w)
    exact ⟨k, by simp [← hk, hκ']⟩
  set C := Subgroup.zpowers cb with hC
  have hEC : ∀ a ∈ E₁, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := hE₁κ a ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_left (hcomm k) j).eq).symm
  have hE₁comm : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  have hFc := isMulCommutative_sup_of_commute_ch625 hE₁comm hCcomm hEC
  have hcb1 : cb ≠ 1 := fun h0 => hcR 1 (by rw [h0, map_one])
  have hcbord : orderOf cb = r := orderOf_eq_prime hcr hcb1
  have hEC1 : E₁ ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzE, hzC⟩
    rw [Subgroup.mem_bot]
    by_contra hz1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzC
    have hcz : cb ∈ Subgroup.zpowers (cb ^ j) := by
      have hord : orderOf (cb ^ j) = r := by
        have hpow : (cb ^ j) ^ r = 1 := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcr, one_zpow]
        have hdvd : orderOf (cb ^ j) ∣ r := orderOf_dvd_of_pow_eq_one hpow
        rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hz1
        · exact h1
      have hle : Subgroup.zpowers (cb ^ j) ≤ Subgroup.zpowers cb :=
        Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers cb j)
      have heq : Subgroup.zpowers (cb ^ j) = Subgroup.zpowers cb :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hcbord])
      rw [heq]
      exact Subgroup.mem_zpowers cb
    obtain ⟨k, hk⟩ := hE₁κ _ hzE
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hcz
    apply hcR (k ^ i)
    rw [map_zpow, ← hk, hi]
  have hFcard : Nat.card ↥(E₁ ⊔ C) = r ^ 3 := by
    have hCN : C ≤ Subgroup.normalizer (E₁ : Set (↥W ⧸ N)) := by
      intro b hb
      refine mem_normalizer_of_forall_conj_mem_of_le fun a ha => ?_
      rw [← hEC a ha b hb]
      simpa using ha
    have h1 := A4.relIndex_sup_eq_of_le_normalizer' hCN
    have h2 : E₁.relIndex C = Nat.card C := by
      rw [← Subgroup.inf_relIndex_right, hEC1] at *
      rw [Subgroup.relIndex_bot_left]
    have h3 := Subgroup.relIndex_mul_card E₁ (C ⊔ E₁)
    rw [inf_eq_left.mpr le_sup_right, h1, h2, Nat.card_zpowers, hcbord, hE₁card] at h3
    rw [sup_comm, ← h3]
    ring
  have hFel : CFSG.Open.IsElemAbelian r (E₁ ⊔ C) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hFc a a.2 b b.2)⟩⟩, ?_⟩
    have hsub : E₁ ⊔ C ≤
        { carrier := {z | z ∈ E₁ ⊔ C ∧ z ^ r = 1}
          mul_mem' := fun {a b} ha hb => ⟨(E₁ ⊔ C).mul_mem ha.1 hb.1, by
            rw [(Commute.mul_pow (hFc a ha.1 b hb.1) r), ha.2, hb.2, one_mul]⟩
          one_mem' := ⟨(E₁ ⊔ C).one_mem, one_pow r⟩
          inv_mem' := fun {a} ha => ⟨(E₁ ⊔ C).inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ } := by
      refine sup_le (fun a ha => ⟨Subgroup.mem_sup_left ha, ?_⟩)
        fun b hb => ⟨Subgroup.mem_sup_right hb, ?_⟩
      · obtain ⟨w, hw, rfl⟩ := ha
        rw [← map_pow, hEp w hw, map_one]
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcr, one_zpow]
    intro z hz
    exact (hsub hz).2
  have h3 : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup (↥W ⧸ N)) :=
    le_pRank_of_isElemAbelian_ch625 hr.one_lt le_top hFel hFcard
  have hNr : ¬ r ∣ Nat.card N := by
    have hN2 : IsPGroup 2 N := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).of_equiv
      (Subgroup.subgroupOfEquivOfLe hOW).symm
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hN2
    rw [hm]
    intro hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
  have h4 := K1.pRank_top_quotient_le W N hr hNr
  have h5 : CFSG.Open.pRank r W ≤ CFSG.Open.pRank r Hn :=
    CFSG.SectionRank.pRank_mono hr.one_lt inf_le_left
  have h6 : CFSG.Open.pRank r Hn ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot d.hyp.qtke d.hyp.pCoreOf_H_ne_bot hr hr2
  omega

end Dat625

end CFSG.Quasithin.H13
