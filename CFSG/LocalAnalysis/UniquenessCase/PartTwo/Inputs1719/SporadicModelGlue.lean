module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17
public import CFSG.RankThree.PartTwo.Sec11.Item116R2Heis
public import CFSG.Quasithin.Background.RonanE43Lift3
public import CFSG.Quasithin.Background.HL3WrNPrime
public import CFSG.Quasithin.EmptyFaithful.T1531In68b
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.SporadicJ1
public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

theorem pow_three_eq_one_of_mem_closure_cubic {G : Type*} [Group G] {x y : G}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : g ^ 3 = 1 := by
  obtain ⟨i, j, k, -, -, -, rfl⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm (by norm_num) hx hy hzx hzy hg
  set z := ⁅x, y⁆ with hzdef
  have hz : z ^ 3 = 1 := by
    rw [hzdef, CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx, hx,
      commutatorElement_one_left]
  have h1 : y * x ^ i = x ^ i * y * z ^ (2 * i) := by
    have := CFSG.SectionRank.LocalWitness.y_mul_x_pow (r := 3) (by norm_num) hzx hzy hz i
    simpa using this
  have hyx : ∀ n : ℕ, y ^ n * x ^ i = x ^ i * y ^ n * z ^ (2 * i * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : Commute (z ^ (2 * i)) (y ^ n) := (hzy.pow_left _).pow_right _
      calc y ^ (n + 1) * x ^ i = y * (y ^ n * x ^ i) := by rw [pow_succ', mul_assoc]
        _ = (y * x ^ i) * y ^ n * z ^ (2 * i * n) := by rw [ih]; simp only [mul_assoc]
        _ = x ^ i * y * (z ^ (2 * i) * y ^ n) * z ^ (2 * i * n) := by
          rw [h1]; simp only [mul_assoc]
        _ = x ^ i * y * (y ^ n * z ^ (2 * i)) * z ^ (2 * i * n) := by rw [hc.eq]
        _ = x ^ i * (y * y ^ n) * (z ^ (2 * i) * z ^ (2 * i * n)) := by simp only [mul_assoc]
        _ = x ^ i * y ^ (n + 1) * z ^ (2 * i * (n + 1)) := by
          rw [← pow_succ', ← pow_add]
          congr 2
          ring
  have hwa : Commute (z ^ (2 * i * j)) (x ^ i) := (hzx.pow_left _).pow_right _
  have hwb : Commute (z ^ (2 * i * j)) (y ^ j) := (hzy.pow_left _).pow_right _
  have hcab : Commute (z ^ k) (x ^ i * y ^ j) :=
    ((hzx.pow_left _).pow_right _).mul_right ((hzy.pow_left _).pow_right _)
  have hp : ∀ (u : G) (n : ℕ), u ^ 3 = 1 → (u ^ n) ^ 3 = 1 := fun u n hu => by
    rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]
  rw [hcab.symm.mul_pow, CFSG.RankThree.PartTwo.Sec11.r116b_cube_aux (hyx j) hwa.eq hwb.eq,
    hp x i hx, hp y j hy, hp z _ hz, hp z k hz]
  simp
theorem exists_permutes_of_overgroup {Y : Type} [Group Y] [Finite Y] {K S H : Subgroup Y}
    (hKN : K.Normal) (hKidx : ∃ a : ℕ, K.index = 2 ^ a) (hS : IsPGroup 2 S) (hSH : S ≤ H)
    {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hH : Nat.card H = p ^ n * Nat.card S) :
    ∃ E : Subgroup Y, E ≤ H ∧ E ≤ K ∧ Nat.card E = p ^ n ∧ E ⊓ S = ⊥ ∧ E ⊔ S = H ∧
      Permutes E S := by
  obtain ⟨a, hKindex⟩ := hKidx
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥H) p (n := n)
    (by rw [hH]; exact dvd_mul_right _ _)
  set E : Subgroup Y := E₀.map H.subtype with hEdef
  have hEcard : Nat.card E = p ^ n := by
    rw [hEdef, Subgroup.card_map_of_injective H.subtype_injective, hE₀]
  have hEH : E ≤ H := by rw [hEdef]; exact Subgroup.map_subtype_le E₀
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
  have hcop : Nat.Coprime (Nat.card E) (Nat.card S) := by
    rw [hEcard, hk]
    exact Nat.Coprime.pow _ _ hcop2
  have hdisj : Disjoint E S := Subgroup.disjoint_of_coprime_natCard hcop
  have hinf : E ⊓ S = ⊥ := hdisj.eq_bot
  have hge : Nat.card H ≤ Nat.card ↥(E ⊔ S) := by
    rw [hH]
    have hfuninj : Function.Injective (fun q : ↥E × ↥S =>
        (⟨(q.1 : Y) * q.2, Subgroup.mul_mem_sup q.1.2 q.2.2⟩ : ↥(E ⊔ S))) := by
      intro q r hqr
      exact Subgroup.mul_injective_of_disjoint hdisj (congrArg Subtype.val hqr)
    have := Nat.card_le_card_of_injective
      (fun q : ↥E × ↥S =>
        (⟨(q.1 : Y) * q.2, Subgroup.mul_mem_sup q.1.2 q.2.2⟩ : ↥(E ⊔ S))) hfuninj
    simpa [Nat.card_prod, hEcard] using this
  have hsup : E ⊔ S = H := Subgroup.eq_of_le_of_card_ge (sup_le hEH hSH) hge
  have hperm : Permutes E S := by
    refine CFSG.Quasithin.H.L3Wr.permute_of_card hinf ?_
    rw [hsup, hH, hEcard]
  have hEK : E ≤ K := by
    have himgbot : E.map (QuotientGroup.mk' K) = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      have hdvd1 : Nat.card (E.map (QuotientGroup.mk' K)) ∣ p ^ n := by
        simpa [hEcard] using Subgroup.card_map_dvd (H := E) (f := QuotientGroup.mk' K)
      have hdvd2 : Nat.card (E.map (QuotientGroup.mk' K)) ∣ 2 ^ a := by
        have h := Subgroup.card_subgroup_dvd_card (E.map (QuotientGroup.mk' K))
        rwa [show Nat.card (Y ⧸ K) = 2 ^ a by
          rw [← Subgroup.index_eq_card K, hKindex]] at h
      have hcopg : Nat.Coprime (p ^ n) (2 ^ a) := Nat.Coprime.pow _ _ hcop2
      exact Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hcopg ▸ Nat.dvd_gcd hdvd1 hdvd2)
    have hker : E ≤ (QuotientGroup.mk' K).ker :=
      (Subgroup.map_eq_bot_iff (H := E) (f := QuotientGroup.mk' K)).mp himgbot
    simpa [QuotientGroup.ker_mk'] using hker
  exact ⟨E, hEH, hEK, hEcard, hinf, hsup, hperm⟩

theorem pow_eq_one_of_sylow_exponent {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (Q : Subgroup G) (hQ : Nat.card Q = p ^ (Nat.card G).factorization p)
    {m : ℕ} (hexp : ∀ q ∈ Q, q ^ m = 1) {g : G} {n : ℕ} (hg : g ^ (p ^ n) = 1) : g ^ m = 1 := by
  have hord : orderOf g ∣ p ^ n := orderOf_dvd_of_pow_eq_one hg
  obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow hp.out).mp hord
  have hpg : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := r) (by rw [Nat.card_zpowers, hr])
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hpg
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G (Sylow.ofCard Q hQ) P
  have hgP : g ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers _)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hgP
  have h := hexp _ hgP
  have e : (c⁻¹ * g * c) ^ m = c⁻¹ * g ^ m * c := by
    have := (conj_pow (a := c⁻¹) (b := g) (i := m))
    simpa using this
  rw [e] at h
  have h2 : g ^ m = c * (c⁻¹ * g ^ m * c) * c⁻¹ := by group
  rw [h2, h]
  group


theorem pow_eq_one_of_index {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (Q : Subgroup G) {k : ℕ} (hQc : Nat.card Q = p ^ k)
    (hQi : ¬ p ∣ Q.index) {m : ℕ} (hexp : ∀ q ∈ Q, q ^ m = 1) {g : G} {n : ℕ}
    (hg : g ^ (p ^ n) = 1) : g ^ m = 1 := by
  have hQ : Nat.card Q = p ^ (Nat.card G).factorization p := by
    have h := ((IsPGroup.of_card hQc).toSylow hQi).card_eq_multiplicity
    simpa using h
  exact pow_eq_one_of_sylow_exponent Q hQ hexp hg

theorem exists_nine_permutes_of_overgroup {Y : Type} [Group Y] [Finite Y] {K S H : Subgroup Y}
    (hKN : K.Normal) (hKidx : ∃ a : ℕ, K.index = 2 ^ a) (hS : IsSylowIn 2 S ⊤) (hSH : S ≤ H)
    (hH : Nat.card H = 9 * Nat.card S) (hexp : ∀ x ∈ K, x ^ 9 = 1 → x ^ 3 = 1) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ Permutes E S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hEK, hEcard, -, -, hperm⟩ := exists_permutes_of_overgroup hKN hKidx hS.2.1 hSH
    (p := 3) (n := 2) (by norm_num) (by rw [hH]; norm_num)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    refine hexp x (hEK hx) ?_
    have hdvd : orderOf x ∣ 9 := by simpa [hEcard] using Subgroup.orderOf_dvd_natCard E hx
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  refine ⟨E, hEK, ?_, ?_, hE3, ?_, hperm⟩
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hEcard
    norm_num at hEcard
  · intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hE3 g g.2)⟩
  · intro hcyc
    have := hcyc
    have hexpdvd : Monoid.exponent ↥E ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hE3 g g.2)
    rw [IsCyclic.exponent_eq_card, hEcard] at hexpdvd
    norm_num at hexpdvd

theorem exists_overgroup_of_card {Y : Type} [Group Y] [Finite Y] {S H₀ : Subgroup Y}
    (hS : Nat.card S = 2 ^ (Nat.card Y).factorization 2) (m : ℕ)
    (hH₀ : Nat.card H₀ = m * 2 ^ (Nat.card Y).factorization 2) :
    ∃ H : Subgroup Y, S ≤ H ∧ Nat.card H = m * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (Nat.card Y).factorization 2 with hf
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := H₀)
    rw [hH₀, zero_mul] at this
    exact lt_irrefl 0 this
  have hmodd : ¬ 2 ∣ m := by
    rintro ⟨r, rfl⟩
    have hdvd : 2 ^ (f + 1) ∣ Nat.card Y := by
      have h := Subgroup.card_subgroup_dvd_card H₀
      rw [hH₀] at h
      exact (Dvd.intro (r) (by ring)).trans h
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_two hdvd
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥H₀) := inferInstance
  have hT₀ : Nat.card T₀ = 2 ^ f := by
    rw [Sylow.card_eq_multiplicity, hH₀, Nat.factorization_mul hm0 (by positivity),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hmodd,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [hf]
  set T : Subgroup Y := (T₀ : Subgroup ↥H₀).map H₀.subtype with hTdef
  have hTcard : Nat.card T = 2 ^ f := by
    rw [hTdef, Subgroup.card_map_of_injective H₀.subtype_injective]
    exact hT₀
  have hTH : T ≤ H₀ := by rw [hTdef]; exact Subgroup.map_subtype_le _
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y (Sylow.ofCard T hTcard) (Sylow.ofCard S hS)
  refine ⟨MulAut.conj c • H₀, ?_, ?_⟩
  · have h1 : (S : Subgroup Y) = MulAut.conj c • T := by
      have := congrArg (fun P : Sylow 2 Y => (P : Subgroup Y)) hc
      simpa [Sylow.coe_subgroup_smul] using this.symm
    rw [h1]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hTH
  · rw [← Nat.card_congr (Subgroup.equivSMul (MulAut.conj c) H₀).toEquiv, hH₀, hS]

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem exists_overgroup_of_invariant {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [hK : K.Normal] {Γ : Type} [Group Γ] [Finite Γ]
    {U P : Subgroup Γ} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUP : U ≤ P) (m : ℕ)
    (hP : Nat.card P = m * Nat.card U)
    (hinv : ∀ α : MulAut Γ, U.map α.toMonoidHom = U → P.map α.toMonoidHom = P)
    (e : ↥K ≃* Γ) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ H : Subgroup Y, S ≤ H ∧ Nat.card H = m * Nat.card S := by
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e hSK hU
  have hα : ∀ t ∈ S, U.map (autK e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact map_autK_of_mem_normalizer' e' inf_le_right (SporB.le_normalizer_inf hK ht)
  set H₀ : Subgroup Y := (P.map e'.symm.toMonoidHom).map K.subtype with hH₀
  have hSH₀ : S ⊓ K ≤ H₀ := (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
  have hnorm : S ≤ Subgroup.normalizer (H₀ : Set Y) := fun t ht =>
    mem_normalizer_pull e' (hinv _ (hα t ht))
  have hH₀K : H₀ ≤ K := pull_le e' P
  have hinf : S ⊓ H₀ = S ⊓ K :=
    le_antisymm (inf_le_inf_left _ hH₀K) (le_inf inf_le_left hSH₀)
  have hcardH₀ : Nat.card H₀ = Nat.card P := by
    rw [hH₀, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e'.symm.injective]
  have hcardSK : Nat.card ↥(S ⊓ K) = Nat.card U := by
    rw [← he', Subgroup.card_map_of_injective e'.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hnorm
  refine ⟨S ⊔ H₀, le_sup_left, ?_⟩
  rw [hinf, hcardSK, hcardH₀, hP] at h
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have h2 : Nat.card ↥(S ⊔ H₀) * Nat.card U = (m * Nat.card S) * Nat.card U := by
    rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right hU0 h2

theorem exists_overgroup_of_eq_top {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    (hKtop : K = ⊤) (hS : Nat.card S = 2 ^ (Nat.card Y).factorization 2) {Γ : Type} [Group Γ]
    (e : ↥K ≃* Γ) {P : Subgroup Γ} (m : ℕ)
    (hP : Nat.card P = m * 2 ^ (Nat.card Γ).factorization 2) :
    ∃ H : Subgroup Y, S ≤ H ∧ Nat.card H = m * Nat.card S := by
  have hΓ : Nat.card Γ = Nat.card Y := by
    rw [← Nat.card_congr e.toEquiv, hKtop, Subgroup.card_top]
  refine exists_overgroup_of_card hS m (H₀ := (P.map e.symm.toMonoidHom).map K.subtype) ?_
  rw [Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective e.symm.injective, hP, hΓ]

theorem exists_nine_permutes_of_model {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    (hKY : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KYForm Y K S)
    {Γ : Type} [Group Γ] (e : ↥K ≃* Γ) (hexp : ∀ g : Γ, g ^ 9 = 1 → g ^ 3 = 1)
    (hH : ∃ H : Subgroup Y, S ≤ H ∧ Nat.card H = 9 * Nat.card S) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ Permutes E S := by
  obtain ⟨H, hSH, hHc⟩ := hH
  refine exists_nine_permutes_of_overgroup
    hKY.1 hKY.2.2.2.2.1 hKY.2.2.2.2.2 hSH hHc ?_
  intro x hx h9
  have h1 : (e ⟨x, hx⟩) ^ 9 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥K) ^ 9 = 1 := Subtype.ext (by simpa using h9)
    rw [this, map_one]
  have h2 := hexp _ h1
  rw [← map_pow, map_eq_one_iff _ e.injective] at h2
  simpa using congrArg Subtype.val h2

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem exists_equiv_pull_normalized {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [hK : K.Normal] {Γ : Type} [Group Γ] [Finite Γ] (e : ↥K ≃* Γ)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) {U : Subgroup Γ}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ e' : ↥K ≃* Γ,
      (∀ P : Subgroup Γ, U ≤ P → S ⊓ K ≤ (P.map e'.symm.toMonoidHom).map K.subtype) ∧
      ∀ P : Subgroup Γ, (∀ α : MulAut Γ, U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) →
        S ≤ Subgroup.normalizer (((P.map e'.symm.toMonoidHom).map K.subtype : Subgroup Y) :
          Set Y) := by
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e hSK hU
  refine ⟨e', fun P hUP => (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP), fun P hinv t ht => ?_⟩
  have hα : U.map (autK e' t).toMonoidHom = U := by
    rw [← he']
    exact map_autK_of_mem_normalizer' e' inf_le_right (SporB.le_normalizer_inf hK ht)
  exact mem_normalizer_pull e' (hinv _ hα)

open CFSG.Quasithin.E2P in
theorem autK_of_mem {H : Type} [Group H] {K : Subgroup H} [K.Normal] {C : Type} [Group C]
    (e : ↥K ≃* C) {t : H} (ht : t ∈ K) : SporB.autK e t = MulAut.conj (e ⟨t, ht⟩) := by
  ext c
  rw [SporB.autK_apply, MulAut.conj_apply]
  have h : (⟨t * ((e.symm c : ↥K) : H) * t⁻¹, ‹K.Normal›.conj_mem _ (e.symm c).2 t⟩ : ↥K) =
      ⟨t, ht⟩ * e.symm c * (⟨t, ht⟩ : ↥K)⁻¹ := rfl
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem exists_sThree_pair_of_equiv {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [hK : K.Normal] (hKidx : ∃ a : ℕ, K.index = 2 ^ a) {Γ : Type} [Group Γ] [Finite Γ]
    (e' : ↥K ≃* Γ) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) {U P₀ P₁ : Subgroup Γ}
    (he' : ((S ⊓ K).subgroupOf K).map e'.toMonoidHom = U) (hU₀ : U ≤ P₀) (hU₁ : U ≤ P₁)
    (hc₀ : Nat.card P₀ = 3 * Nat.card U) (hc₁ : Nat.card P₁ = 3 * Nat.card U)
    (hn₀ : ¬ P₀ ≤ Subgroup.normalizer (U : Set Γ)) (hn₁ : ¬ P₁ ≤ Subgroup.normalizer (U : Set Γ))
    (hgen : P₀ ⊔ P₁ = ⊤)
    (hinv : ∀ t ∈ S, P₀.map (autK e' t).toMonoidHom = P₀ ∧ P₁.map (autK e' t).toMonoidHom = P₁) :
    ∃ Q₀ Q₁ : Subgroup Y, S ≤ Q₀ ∧ S ≤ Q₁ ∧ Q₀ ⊔ Q₁ = ⊤ ∧
      Nonempty (Bar2 Q₀ ≃* Equiv.Perm (Fin 3)) ∧ Nonempty (Bar2 Q₁ ≃* Equiv.Perm (Fin 3)) := by
  have hcardSK : Nat.card ↥(S ⊓ K) = Nat.card U := by
    rw [← he', Subgroup.card_map_of_injective e'.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have key : ∀ P : Subgroup Γ, U ≤ P → Nat.card P = 3 * Nat.card U →
      ¬ P ≤ Subgroup.normalizer (U : Set Γ) →
      (∀ t ∈ S, P.map (autK e' t).toMonoidHom = P) →
      S ≤ S ⊔ (P.map e'.symm.toMonoidHom).map K.subtype ∧
        Nonempty (Bar2 (S ⊔ (P.map e'.symm.toMonoidHom).map K.subtype) ≃*
          Equiv.Perm (Fin 3)) := by
    intro P hUP hcP hnP hPinv
    set H₀ : Subgroup Y := (P.map e'.symm.toMonoidHom).map K.subtype with hH₀
    have hSH₀ : S ⊓ K ≤ H₀ := (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
    have hnorm : S ≤ Subgroup.normalizer (H₀ : Set Y) := fun t ht =>
      mem_normalizer_pull e' (hPinv t ht)
    have hH₀K : H₀ ≤ K := pull_le e' P
    have hinf : S ⊓ H₀ = S ⊓ K :=
      le_antisymm (inf_le_inf_left _ hH₀K) (le_inf inf_le_left hSH₀)
    have hcardH₀ : Nat.card H₀ = Nat.card P := by
      rw [hH₀, Subgroup.card_map_of_injective K.subtype_injective,
        Subgroup.card_map_of_injective e'.symm.injective]
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      hnorm
    rw [hinf, hcardSK, hcardH₀, hcP] at h
    have hU0 : 0 < Nat.card U := Nat.card_pos
    have hQc : Nat.card ↥(S ⊔ H₀) = 3 * Nat.card S := by
      have h2 : Nat.card ↥(S ⊔ H₀) * Nat.card U = (3 * Nat.card S) * Nat.card U := by
        rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_right hU0 h2
    have hSQ : S ≤ S ⊔ H₀ := le_sup_left
    have hrel : S.relIndex (S ⊔ H₀) = 3 := by
      have h1 := Subgroup.relIndex_mul_card (H := S) (K := S ⊔ H₀)
      rw [inf_of_le_left hSQ, hQc] at h1
      have hS0 : 0 < Nat.card S := Nat.card_pos
      have h2 : S.relIndex (S ⊔ H₀) * Nat.card S = 3 * Nat.card S := h1
      exact Nat.eq_of_mul_eq_mul_right hS0 h2
    have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf S (S ⊔ H₀) :=
      ⟨hSQ, hS.2.1, by
        change ¬ 2 ∣ S.relIndex (S ⊔ H₀)
        rw [hrel]; norm_num⟩
    have hnn : ¬ S ⊔ H₀ ≤ Subgroup.normalizer (S : Set Y) := by
      intro hle
      apply hnP
      have hH₀N : H₀ ≤ Subgroup.normalizer ((S ⊓ K : Subgroup Y) : Set Y) := by
        intro h hh
        have hS' := hle ((le_sup_right : H₀ ≤ S ⊔ H₀) hh)
        have hK' : h ∈ Subgroup.normalizer (K : Set Y) := by
          rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
        rw [Subgroup.mem_normalizer_iff] at hS' hK' ⊢
        intro y
        simp only [Subgroup.mem_inf]
        rw [hS' y, hK' y]
      intro p hp
      rw [Subgroup.mem_normalizer_iff]
      intro u
      set k : ↥K := e'.symm p with hk
      have hkH₀ : (k : Y) ∈ H₀ := ⟨k, ⟨p, hp, rfl⟩, rfl⟩
      have hN := Subgroup.mem_normalizer_iff.mp (hH₀N hkH₀)
      have hu : ∀ c : Γ, c ∈ U ↔ ((e'.symm c : ↥K) : Y) ∈ S ⊓ K := by
        intro c
        rw [← he']
        constructor
        · rintro ⟨w, hw, rfl⟩
          simpa [Subgroup.mem_subgroupOf] using hw
        · intro hc
          refine ⟨e'.symm c, ?_, by simp⟩
          exact Subgroup.mem_subgroupOf.mpr hc
      rw [hu u, hu (p * u * p⁻¹)]
      have e1 : ((e'.symm (p * u * p⁻¹) : ↥K) : Y) = (k : Y) * (e'.symm u : Y) * (k : Y)⁻¹ := by
        simp [hk, map_mul, map_inv]
      rw [e1]
      exact hN _
    refine ⟨hSQ, ?_⟩
    obtain ⟨φ⟩ := CFSG.Quasithin.nonempty_quotient_pCore_of_relIndex_eq_three' hsyl hrel hnn
    exact ⟨φ⟩
  obtain ⟨hS₀, hb₀⟩ := key P₀ hU₀ hc₀ hn₀ fun t ht => (hinv t ht).1
  obtain ⟨hS₁, hb₁⟩ := key P₁ hU₁ hc₁ hn₁ fun t ht => (hinv t ht).2
  refine ⟨_, _, hS₀, hS₁, ?_, hb₀, hb₁⟩
  have hKS : K ⊔ S = ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hidx : ¬ 2 ∣ S.index := by
      have := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
    exact CFSG.QuasiDihedralFusion.normal_sup_sylow_eq_top K hKidx (hS.2.1.toSylow hidx)
  have hKeq : K = (P₀.map e'.symm.toMonoidHom).map K.subtype ⊔
      (P₁.map e'.symm.toMonoidHom).map K.subtype := by
    refine (pull_top e').symm.trans ?_
    rw [← hgen, pull_sup]
  rw [eq_top_iff, ← hKS]
  refine sup_le ?_ (le_sup_left.trans le_sup_left)
  calc K = (P₀.map e'.symm.toMonoidHom).map K.subtype ⊔
        (P₁.map e'.symm.toMonoidHom).map K.subtype := hKeq
    _ ≤ _ := sup_le_sup le_sup_right le_sup_right

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem exists_sThree_pair_of_model {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [hK : K.Normal] (hKidx : ∃ a : ℕ, K.index = 2 ^ a) {Γ : Type} [Group Γ] [Finite Γ]
    (e : ↥K ≃* Γ) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) {U P₀ P₁ : Subgroup Γ}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hU₀ : U ≤ P₀) (hU₁ : U ≤ P₁)
    (hc₀ : Nat.card P₀ = 3 * Nat.card U) (hc₁ : Nat.card P₁ = 3 * Nat.card U)
    (hn₀ : ¬ P₀ ≤ Subgroup.normalizer (U : Set Γ)) (hn₁ : ¬ P₁ ≤ Subgroup.normalizer (U : Set Γ))
    (hgen : P₀ ⊔ P₁ = ⊤)
    (hinv : ∀ α : MulAut Γ, U.map α.toMonoidHom = U →
      P₀.map α.toMonoidHom = P₀ ∧ P₁.map α.toMonoidHom = P₁) :
    ∃ Q₀ Q₁ : Subgroup Y, S ≤ Q₀ ∧ S ≤ Q₁ ∧ Q₀ ⊔ Q₁ = ⊤ ∧
      Nonempty (Bar2 Q₀ ≃* Equiv.Perm (Fin 3)) ∧ Nonempty (Bar2 Q₁ ≃* Equiv.Perm (Fin 3)) := by
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e hSK hU
  refine exists_sThree_pair_of_equiv hKidx e' hS he' hU₀ hU₁ hc₀ hc₁ hn₀ hn₁ hgen fun t ht => ?_
  refine hinv _ ?_
  rw [← he']
  exact map_autK_of_mem_normalizer' e' inf_le_right (SporB.le_normalizer_inf hK ht)

theorem eq_top_of_sup_eq_top_of_central {Y : Type*} [Group Y] {K J Z : Subgroup Y} [Z.Normal]
    (hZK : Z ≤ K) (hZc : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z) (hperf : K ≤ ⁅K, K⁆)
    (hJ : J ⊔ Z = ⊤) : J = ⊤ := by
  have hdec : ∀ k ∈ K, ∃ q ∈ J ⊓ K, ∃ z ∈ Z, k = q * z := by
    intro k hk
    have hk' : k ∈ ((J ⊔ Z : Subgroup Y) : Set Y) := by rw [hJ]; trivial
    rw [Subgroup.mul_normal] at hk'
    obtain ⟨j, hj, z, hz, rfl⟩ := hk'
    refine ⟨j, ⟨hj, ?_⟩, z, hz, rfl⟩
    have : j = j * z * z⁻¹ := by group
    rw [this]
    exact K.mul_mem hk (K.inv_mem (hZK hz))
  have hKJ : K ≤ J ⊓ K :=
    CFSG.Quasithin.RonanE43.le_of_central_cover hperf inf_le_right hZK hZc hdec
  rw [eq_top_iff, ← hJ]
  exact sup_le le_rfl (hZK.trans (hKJ.trans inf_le_left))

theorem eq_top_of_inner_model {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    (hKY : KYForm Y K S) (hZ : Subgroup.center ↥K = ⊥) {Γ : Type} [Group Γ] (e : ↥K ≃* Γ)
    (hin : ∀ φ : MulAut Γ, ∃ g : Γ, φ = MulAut.conj g) : K = ⊤ := by
  have : K.Normal := hKY.1
  refine
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.eq_top_of_forall_inner
      (CFSG.GH74.Generic.BProg.B3.S3T2A7Loc.forall_inner_of_equiv e hin) ?_
  rw [hKY.2.2.2.1, hZ, Subgroup.map_bot]

theorem exists_overgroup_of_eq_top' {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    (hKtop : K = ⊤) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) {Γ : Type} [Group Γ]
    [Finite Γ] {P : Subgroup Γ} {m k : ℕ} (hP : Nat.card P = m * 2 ^ k) (hm : ¬ 2 ∣ m)
    (hPi : ¬ 2 ∣ P.index) (e : ↥K ≃* Γ) :
    ∃ H : Subgroup Y, S ≤ H ∧ Nat.card H = m * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  have hi0 : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2k : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hΓ : Nat.card Γ = m * 2 ^ k * P.index := by rw [← hP, Subgroup.card_mul_index]
  have hfac : (Nat.card Γ).factorization 2 = k := by
    rw [hΓ, Nat.factorization_mul (mul_ne_zero hm0 h2k) hi0, Nat.factorization_mul hm0 h2k,
      Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hm,
      Nat.factorization_eq_zero_of_not_dvd hPi, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  have hScard : Nat.card S = 2 ^ (Nat.card Y).factorization 2 := by
    simpa using (hS.2.1.toSylow hidx).card_eq_multiplicity
  exact exists_overgroup_of_eq_top hKtop hScard e m (by rw [hP, hfac])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
