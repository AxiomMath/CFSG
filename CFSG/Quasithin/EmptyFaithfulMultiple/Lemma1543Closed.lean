module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs4
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1544
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1543Linear
import CFSG.Quasithin.Background.OrderingMax
import CFSG.LocalAnalysis.SectionRank.Induction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open

section Abstract

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem conj_pow_prime_pow {p : ℕ} {g a : Q} {k : ℕ} (ha : a ^ p ^ k = 1) :
    (g * a * g⁻¹) ^ p ^ k = 1 := by
  rw [conj_pow, ha, mul_one, mul_inv_cancel]

theorem mem_pCore_of_pow_eq_one (hsolv : Group.IsSolvable Q) {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hO2 : CFSG.Open.pCore 2 Q = ⊥)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup (CFSG.Open.pCore q Q)) ≤ 2)
    (hlt : ∀ q : ℕ, q.Prime → q ≠ p → q ∣ Nat.card Q → q < p) {x : Q} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x ∈ CFSG.Open.pCore p Q := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hcent : ∀ g : Q, (∃ k : ℕ, g ^ p ^ k = 1) → ∀ q : ℕ, q.Prime → q ≠ p →
      g ∈ Subgroup.centralizer (CFSG.Open.pCore q Q : Set Q) := by
    rintro g ⟨k, hk⟩ q hq hqp
    have : Fact q.Prime := ⟨hq⟩
    by_cases hq2 : q = 2
    · subst hq2
      rw [hO2]
      intro h hh
      rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]
    by_cases hqQ : q ∣ Nat.card Q
    · have hlt' := hlt q hq hqp hqQ
      have hPq : IsPGroup q (CFSG.Open.pCore q Q) := CFSG.LieType.BorelTits.pCore_isPGroup q
      have : (CFSG.Open.pCore q Q).Normal := CFSG.LieType.BorelTits.pCore_normal q
      have hα : (MulAut.conjNormal (H := CFSG.Open.pCore q Q) g) ^ p ^ k = 1 := by
        rw [← map_pow, hk, map_one]
      have h1 := eq_one_of_pow_eq_one_of_lt hq2 hPq (hrank q hq hq2) hp.out hp2 hlt' hα
      intro h hh
      have h2 := congrArg
        (fun α : MulAut (CFSG.Open.pCore q Q) => ((α ⟨h, hh⟩ : CFSG.Open.pCore q Q) : Q)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · have hbot : CFSG.Open.pCore q Q = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp
          (CFSG.LieType.BorelTits.pCore_isPGroup q (G := Q))) (⟨y, hy⟩ : CFSG.Open.pCore q Q)
        rw [Subgroup.orderOf_mk] at hm
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, pow_zero, orderOf_eq_one_iff] at hm
          exact Subgroup.mem_bot.mpr hm
        · exact absurd ((dvd_pow_self q h0.ne').trans (hm ▸ orderOf_dvd_natCard y)) hqQ
      rw [hbot]
      intro h hh
      rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]
  set E : Set Q := {g : Q | ∃ k : ℕ, g ^ p ^ k = 1} with hE
  set W := Subgroup.closure E with hWdef
  have hxW : x ∈ W := Subgroup.subset_closure ⟨k, hx⟩
  have hWn : W.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨k, hk⟩ := ha
      exact Subgroup.subset_closure ⟨k, conj_pow_prime_pow hk⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact W.mul_mem ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact W.inv_mem ha
  have hWc : ∀ q : ℕ, q.Prime → q ≠ p →
      W ≤ Subgroup.centralizer (CFSG.Open.pCore q Q : Set Q) := by
    intro q hq hqp
    rw [hWdef, Subgroup.closure_le]
    intro g hg
    exact hcent g hg q hq hqp
  set P := CFSG.Open.pCore p Q with hPdef
  have : P.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hPp : IsPGroup p P := CFSG.LieType.BorelTits.pCore_isPGroup p
  obtain ⟨φ, hφ⟩ := exists_hom_ker_eq_pCore_aut hp2 hPp (hrank p hp.out hp2)
  set ψ : Q →* GL (Fin 2) (ZMod p) := φ.comp (MulAut.conjNormal (H := P)) with hψ
  have hSsolv : Group.IsSolvable (W.map ψ) := by
    have := hsolv
    have : Group.IsSolvable W := Group.isSolvable_of_isSolvable_injective W.subtype_injective
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective ψ W)
  have hgen : ∀ g ∈ E, ∀ g' ∈ E, Commute (ψ g) (ψ g') := by
    rintro g ⟨a, ha⟩ g' ⟨b, hb⟩
    exact commute_of_isSolvable hp5 hSsolv
      (Subgroup.mem_map_of_mem ψ (Subgroup.subset_closure ⟨a, ha⟩))
      (Subgroup.mem_map_of_mem ψ (Subgroup.subset_closure ⟨b, hb⟩))
      (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
  have hW1 : ∀ w ∈ W, ∀ g ∈ E, Commute (ψ w) (ψ g) := by
    intro w hw g hg
    induction hw using Subgroup.closure_induction with
    | mem a ha => exact hgen a ha g hg
    | one => rw [map_one]; exact Commute.one_left _
    | mul a b _ _ ha hb => rw [map_mul]; exact ha.mul_left hb
    | inv a _ ha => rw [map_inv]; exact ha.inv_left
  have hW2 : ∀ w ∈ W, ∀ w' ∈ W, Commute (ψ w) (ψ w') := by
    intro w hw w' hw'
    induction hw' using Subgroup.closure_induction with
    | mem a ha => exact hW1 w hw a ha
    | one => rw [map_one]; exact Commute.one_right _
    | mul a b _ _ ha hb => rw [map_mul]; exact ha.mul_right hb
    | inv a _ ha => rw [map_inv]; exact ha.inv_right
  have hWp : ∀ w ∈ W, ∃ a : ℕ, (ψ w) ^ p ^ a = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨k, hk⟩ := ha
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    | one => exact ⟨0, by simp⟩
    | mul a b ha' hb' ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      refine ⟨m + n, ?_⟩
      have e1 : ψ a ^ p ^ (m + n) = 1 := by rw [pow_add, pow_mul, hm, one_pow]
      have e2 : ψ b ^ p ^ (m + n) = 1 := by rw [add_comm, pow_add, pow_mul, hn, one_pow]
      rw [map_mul, (hW2 a ha' b hb').mul_pow, e1, e2, one_mul]
    | inv a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨m, by rw [map_inv, inv_pow, hm, inv_one]⟩
  have hWP : ∀ w ∈ W, ∃ n : ℕ, w ^ p ^ n ∈ Subgroup.centralizer (P : Set Q) := by
    intro w hw
    obtain ⟨a, ha⟩ := hWp w hw
    have h1 : MulAut.conjNormal (H := P) (w ^ p ^ a) ∈ CFSG.Open.pCore p (MulAut P) := by
      rw [← hφ, MonoidHom.mem_ker]
      have : ψ (w ^ p ^ a) = 1 := by rw [map_pow, ha]
      exact this
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCore_isPGroup p (G := MulAut P) ⟨_, h1⟩
    have hb' : MulAut.conjNormal (H := P) (w ^ p ^ (a + b)) = 1 := by
      rw [pow_add, pow_mul, map_pow]
      simpa using congrArg Subtype.val hb
    refine ⟨a + b, fun h hh => ?_⟩
    have := congrArg (fun α : MulAut P => ((α ⟨h, hh⟩ : P) : Q)) hb'
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  set K : Subgroup Q := ⨆ q : {q : ℕ // q.Prime ∧ q ≠ p}, CFSG.Open.pCore q.1 Q with hK
  have hKn : K.Normal := by
    have : ∀ q : {q : ℕ // q.Prime ∧ q ≠ p}, (CFSG.Open.pCore q.1 Q).Normal := fun q =>
      CFSG.LieType.BorelTits.pCore_normal q.1
    exact Subgroup.iSup_normal _
  have hWK : W ≤ Subgroup.centralizer (K : Set Q) :=
    CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ fun q => hWc q.1 q.2.1 q.2.2
  have hPK : P ≤ Subgroup.centralizer (K : Set Q) := by
    refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ fun q => ?_
    have : Fact q.1.Prime := ⟨q.2.1⟩
    have hdis : Disjoint P (CFSG.Open.pCore q.1 Q) :=
      IsPGroup.disjoint_of_ne p q.1 (Ne.symm q.2.2) _ _ hPp
        (CFSG.LieType.BorelTits.pCore_isPGroup q.1)
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.commute_of_normal_of_disjoint _ _ inferInstance
      (CFSG.LieType.BorelTits.pCore_normal q.1) hdis u v hu hv).symm
  have hF : ∀ c ∈ W, c ∈ Subgroup.centralizer (P : Set Q) → ∃ b : ℕ, c ^ p ^ b ∈ K := by
    intro c hcW hcP
    have hcF : c ∈ Subgroup.centralizer (CFSG.fittingSubgroup Q : Set Q) := by
      refine CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores
        (P := Subgroup.zpowers c) (fun q => ?_) (Subgroup.mem_zpowers c)
      rw [Subgroup.zpowers_le]
      by_cases hqp : ((q : ℕ) : ℕ) = p
      · rw [hqp]
        exact hcP
      · exact hWc _ (Nat.prime_of_mem_primeFactors q.1.2) hqp hcW
    have hcF' : c ∈ CFSG.fittingSubgroup Q :=
      CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hcF
    have hFPK : CFSG.fittingSubgroup Q ≤ P ⊔ K := by
      rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
      refine iSup_le fun q => ?_
      by_cases hqp : (q : ℕ) = p
      · rw [hqp]
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup (fun q : {q : ℕ // q.Prime ∧ q ≠ p} =>
          CFSG.Open.pCore q.1 Q) ⟨q, Nat.prime_of_mem_primeFactors q.2, hqp⟩)
    obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup_of_normal_right.mp (hFPK hcF')
    obtain ⟨b, hb⟩ := hPp ⟨u, hu⟩
    have hub : u ^ p ^ b = 1 := by simpa using congrArg Subtype.val hb
    have huv' : Commute u v := (Subgroup.mem_centralizer_iff.mp (hPK hu) v hv).symm
    refine ⟨b, ?_⟩
    rw [← huv, huv'.mul_pow, hub, one_mul]
    exact K.pow_mem hv _
  set Z₀ : Subgroup W := K.subgroupOf W with hZ₀
  have hZc : Z₀ ≤ Subgroup.center W := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp (hWK w.2) z (Subgroup.mem_subgroupOf.mp hz)
    simpa using this.symm
  have : Z₀.Normal := Subgroup.normal_of_le_center hZc
  have hquot : IsPGroup p (W ⧸ Z₀) := by
    intro r
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨a, ha⟩ := hWP w w.2
    obtain ⟨b, hb⟩ := hF _ (W.pow_mem w.2 _) ha
    refine ⟨a + b, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, pow_add, pow_mul]
    exact hb
  have hWnil : Group.IsNilpotent W := by
    have := hquot.isNilpotent
    exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Z₀)
      (by rw [QuotientGroup.ker_mk']; exact hZc)
  obtain ⟨Syl⟩ := (inferInstance : Nonempty (Sylow p W))
  have hSn := Group.IsNilpotent.sylow_normal hWnil p Syl
  have huniq := Sylow.unique_of_normal Syl hSn
  have hWle : W ≤ (Syl : Subgroup W).map W.subtype := by
    conv_lhs => rw [hWdef]
    rw [Subgroup.closure_le]
    intro g hg
    have hgW : g ∈ W := Subgroup.subset_closure hg
    obtain ⟨k, hk⟩ := hg
    have hgp : IsPGroup p (Subgroup.zpowers (⟨g, hgW⟩ : W)) := by
      rintro ⟨_, n, rfl⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_zpow]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    obtain ⟨S', hS'⟩ := hgp.exists_le_sylow
    have hS'eq : S' = Syl := Subsingleton.elim _ _
    exact ⟨⟨g, hgW⟩, hS'eq ▸ hS' (Subgroup.mem_zpowers _), rfl⟩
  have hWp' : IsPGroup p W := (Syl.isPGroup'.map W.subtype).to_le hWle
  exact CFSG.LieType.BorelTits.le_pCore p hWn hWp' hxW

end Abstract

section Application

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

theorem pRank_pCore_quotient_le_two (hK : CFSG.QuasithinUnique.quasithinIsQTKECat G)
    {M : Subgroup G}
    (hM : IsTwoLocal M) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup (CFSG.Open.pCore q (M ⧸ CFSG.Open.pCore 2 M))) ≤ 2 := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pRank_top_subtype]
  refine (CFSG.SectionRank.pRank_mono hq.one_lt le_top).trans ?_
  have : (CFSG.Open.pCore 2 M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  rw [CFSG.SectionRank.pRank_quotient_two_group _ (CFSG.LieType.BorelTits.pCore_isPGroup 2) hq hq2,
    pRank_top_subtype]
  exact pRank_le_two_of_isTwoLocal_cat hK hM hq hq2

theorem pow_eq_one_of_odd_of_relIndex {X : Subgroup G} {p : ℕ} (hXp : (pCoreOf 2 X).relIndex X = p)
    {x : G} (hx : x ∈ X) (hodd : Odd (orderOf x)) : x ^ p = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 X :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have : ((pCoreOf 2 X).subgroupOf X).Normal := by
    rw [hN]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  have hcard : Nat.card (X ⧸ (pCoreOf 2 X).subgroupOf X) = p := by
    rw [← Subgroup.index_eq_card]
    exact hXp
  have h1 : (⟨x, hx⟩ : X) ^ p ∈ (pCoreOf 2 X).subgroupOf X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
    exact pow_card_eq_one'
  rw [Subgroup.mem_subgroupOf] at h1
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨_, h1⟩
  have hm' : (x ^ p) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hodd' : Odd (orderOf (x ^ p)) := hodd.of_dvd_nat (orderOf_pow_dvd p)
  have h2 : orderOf (x ^ p) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hodd'.coprime_two_right.pow_right m) h2)

theorem prime_lt_of_dvd_card_inM (hyp : MultipleCentralizerHypothesis G T)
    (h2 : Stmt1542Two G T) (h3 : Stmt1542Three G T) {p : ℕ} (hp5 : 5 ≤ p)
    (hmax : ∀ Y : Subgroup G, IsSmallXi T Y → (pCoreOf 2 Y).relIndex Y ≤ p) {M : Subgroup G}
    (hM : InM T M) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hqM : q ∣ Nat.card M) : q < p := by
  by_cases hq2 : q = 2
  · omega
  obtain ⟨Y, -, hY⟩ := exists_xi_of_le_inM hyp hM hM.2 le_rfl
    (pCoreOf_ne_bot_of_isTwoLocal hM.1.1) (h2 M hM) hq hq2 hqM
  rcases hY with ⟨hYi, hidx⟩ | ⟨hYi, hidx⟩
  · have h35 := (h3 Y hYi).2.2.2
    rw [hidx] at h35
    rcases h35 with ⟨k, hk⟩ | ⟨k, hk⟩
    · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
        (hq.dvd_of_dvd_pow (hk ▸ dvd_pow_self q two_ne_zero))
      omega
    · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp
        (hq.dvd_of_dvd_pow (hk ▸ dvd_pow_self q two_ne_zero))
      omega
  · have := hmax Y hYi
    omega

theorem mem_O2pOf_of_pow_eq_one (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T)
    (h3 : Stmt1542Three G T) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hmax : ∀ Y : Subgroup G, IsSmallXi T Y → (pCoreOf 2 Y).relIndex Y ≤ p) {M : Subgroup G}
    (hM : InM T M) {y : G} (hyM : y ∈ M) {k : ℕ} (hy : y ^ p ^ k = 1) : y ∈ O2pOf M p := by
  have hsolv : Group.IsSolvable (M ⧸ CFSG.Open.pCore 2 M) := by
    have := h2 M hM
    exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  have hlt : ∀ q : ℕ, q.Prime → q ≠ p → q ∣ Nat.card (M ⧸ CFSG.Open.pCore 2 M) → q < p :=
    fun q hq hqp hqQ => prime_lt_of_dvd_card_inM hyp h2 h3 hp5 hmax hM hq hqp
      (hqQ.trans (by rw [← Subgroup.index_eq_card]; exact Subgroup.index_dvd_card _))
  have hmem : QuotientGroup.mk' (CFSG.Open.pCore 2 M) ⟨y, hyM⟩ ∈
      CFSG.Open.pCore p (M ⧸ CFSG.Open.pCore 2 M) := by
    refine mem_pCore_of_pow_eq_one hsolv hp5 B6.pCore_quotient_pCore
      (fun q hq hq2 => pRank_pCore_quotient_le_two hyp.qtke hM.1.1 hq hq2) hlt (k := k) ?_
    rw [← map_pow]
    have : (⟨y, hyM⟩ : M) ^ p ^ k = 1 := Subtype.ext (by simpa using hy)
    rw [this, map_one]
  exact ⟨⟨y, hyM⟩, hmem, rfl⟩

theorem le_O2pOf_of_isSmallXi (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T)
    (h3 : Stmt1542Three G T) {X : Subgroup G} {p : ℕ} (hX : IsSmallXi T X)
    (hXp : (pCoreOf 2 X).relIndex X = p)
    (hmax : ∀ Y : Subgroup G, IsSmallXi T Y → (pCoreOf 2 Y).relIndex Y ≤ p) (hp3 : 3 < p)
    {M : Subgroup G} (hM : InM (X ⊔ T) M) : X ≤ O2pOf M p := by
  have hMT : InM T M := ⟨hM.1, le_sup_right.trans hM.2⟩
  obtain ⟨p', hp', -, hidx⟩ := hX.2.2.2
  obtain rfl : p' = p := hidx.symm.trans hXp
  have : Fact p'.Prime := ⟨hp'⟩
  have hp5 : 5 ≤ p' := by
    rcases (by omega : p' = 4 ∨ 5 ≤ p') with h | h
    · subst h
      exact absurd hp' (by norm_num)
    · exact h
  rw [hX.1]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_O2pOf_of_pow_eq_one hyp h2 h3 hp5 hmax hMT (hM.2 (le_sup_left (a := X) hx.1)) (k := 1)
    (by rw [pow_one]; exact pow_eq_one_of_odd_of_relIndex hXp hx.1 hx.2)

theorem pCoreOf_le_of_le_O2pOf {M X : Subgroup G} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hXM : X ≤ O2pOf M p) : pCoreOf 2 X ≤ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := hXM ((CFSG.LieType.BorelTits.pCoreOf_le 2 X) hy)
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨_, hy⟩
  have hm' : y' ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCore_isPGroup p
    (G := M ⧸ CFSG.Open.pCore 2 M) ⟨_, hy'⟩
  have hn' : (QuotientGroup.mk' (CFSG.Open.pCore 2 M) y') ^ p ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 M) y' = 1 :=
    eq_one_of_pow_prime_pow (Fact.out : p.Prime) Nat.prime_two hp2 hn'
      (by rw [← map_pow, hm', map_one])
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨y', h1, rfl⟩

theorem O2pOf_le_O2FOf (M : Subgroup G) (p : ℕ) [Fact p.Prime] : O2pOf M p ≤ O2FOf M := by
  refine Subgroup.map_mono fun y hy => ?_
  have h := CFSG.pCore_le_fitting (M ⧸ CFSG.Open.pCore 2 M) p
  exact h hy

end Application

end CFSG.Quasithin.EmptyFaithfulMultiple
