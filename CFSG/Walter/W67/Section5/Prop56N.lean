module

public import CFSG.Walter.W67.Section5.Prop56R
public import CFSG.Walter.W67.Section5.P56Free

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Sec56

theorem card_dvd_card_sub_one_of_fpf {B M : Type*} [Group B] [Finite B] [MulAction B M]
    [Finite M] (m₀ : M) (hm₀ : ∀ b : B, b • m₀ = m₀)
    (hfix : ∀ b : B, b ≠ 1 → ∀ y : M, b • y = y → y = m₀) : Nat.card B ∣ Nat.card M - 1 := by
  classical
  let := Fintype.ofFinite B
  let := Fintype.ofFinite M
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group B M
  have h1 : Fintype.card (MulAction.fixedBy M (1 : B)) = Fintype.card M :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun y => one_smul B y)
  have h2 : ∀ b ∈ Finset.univ.erase (1 : B), Fintype.card (MulAction.fixedBy M b) = 1 := by
    intro b hb
    have hb1 : b ≠ 1 := Finset.ne_of_mem_erase hb
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨m₀, hm₀ b⟩, fun ⟨y, hy⟩ => Subtype.ext (hfix b hb1 y hy)⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), h1, Finset.sum_congr rfl h2,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    smul_eq_mul, mul_one] at hB
  have hM : 0 < Fintype.card M := Fintype.card_pos_iff.mpr ⟨m₀⟩
  have hBpos : 0 < Fintype.card B := Fintype.card_pos
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h3 : Fintype.card B ∣ (Fintype.card M - 1) + Fintype.card B := by
    rw [show Fintype.card M - 1 + Fintype.card B = Fintype.card M + (Fintype.card B - 1) by
      omega, hB]
    exact Dvd.intro_left _ rfl
  exact (Nat.dvd_add_left (dvd_refl _)).mp h3

theorem dvd_of_dvd_three_pow_sub_one {n m d : ℕ} (hn : 0 < n) (hd : 2 * d = 3 ^ n - 1)
    (hdvd : d ∣ 3 ^ m - 1) : n ∣ m := by
  have h1n : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hmod : 3 ^ n ≡ 1 [MOD d] :=
    ((Nat.modEq_iff_dvd' h1n).mpr ⟨2, by omega⟩).symm
  have hmodm : 3 ^ m ≡ 1 [MOD d] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr hdvd).symm
  set r := m % n with hr
  have hm : m = n * (m / n) + r := (Nat.div_add_mod m n).symm
  have hmodr : 3 ^ r ≡ 1 [MOD d] := by
    have h2 : 3 ^ m ≡ 3 ^ r [MOD d] := by
      rw [hm, pow_add, pow_mul]
      have := (hmod.pow (m / n)).mul_right (3 ^ r)
      rwa [one_pow, one_mul] at this
    exact h2.symm.trans hmodm
  have hrdvd : d ∣ 3 ^ r - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hmodr.symm
  by_contra hnm
  have hr0 : r ≠ 0 := fun h => hnm (Nat.dvd_of_mod_eq_zero h)
  have hrn : r < n := Nat.mod_lt m hn
  have hpos : 0 < 3 ^ r - 1 := by
    have : 3 ≤ 3 ^ r := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
      (Nat.one_le_iff_ne_zero.mpr hr0))
    omega
  have hle := Nat.le_of_dvd hpos hrdvd
  have h4 : 3 ^ r ≤ 3 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 3 ^ n = 3 ^ (n - 1) * 3 := by rw [← pow_succ, Nat.sub_add_cancel hn]
  have h6 : 1 ≤ 3 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem le_of_pow_dvd {t e u w : ℕ} (hu : ¬ 3 ∣ u) (hw : w ≠ 0) (h : 3 ^ t ∣ 3 ^ e * u * w) :
    t ≤ e + w.factorization 3 := by
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero 3)
  have hne : 3 ^ e * u * w ≠ 0 := by positivity
  have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization hne).mp h
  rw [Nat.factorization_mul (by positivity) hw, Nat.factorization_mul (by positivity) hu0,
    Nat.Prime.factorization_pow Nat.prime_three] at h1
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h1
  rw [Nat.factorization_eq_zero_of_not_dvd hu] at h1
  omega

end Sec56

namespace Std

theorem E_comm_all
    (s : Std G) : ∀ a ∈ s.fr.E, ∀ b ∈ s.fr.E, a * b = b * a := by
  obtain ⟨g, -, hgen⟩ := s.fr.exists_generator_E
  rw [s.F_eq_bot, sup_bot_eq] at hgen
  intro a ha b hb
  rw [← hgen] at ha hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_add, ← zpow_add, add_comm]

end Std

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

theorem E_le_normalizer_zpowers {b₀ : G} (hb₀ : b₀ ∈ f5.B) :
    s.fr.E ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
  have := f5.B_cyclic
  obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := f5.B)
  intro e he
  have hpow : ∃ k : ℤ, e * b₀ * e⁻¹ = b₀ ^ k := by
    have heβ : e * (β : G) * e⁻¹ ∈ f5.B :=
      (Subgroup.mem_normalizer_iff.mp (f5.E_le_normalizer_B he) β).mp β.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hβ ⟨_, heβ⟩)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hβ ⟨b₀, hb₀⟩)
    refine ⟨k, ?_⟩
    have hk' : (β : G) ^ k = e * (β : G) * e⁻¹ := by
      have := congrArg Subtype.val hk
      simpa using this
    have hi' : (β : G) ^ i = b₀ := by
      have := congrArg Subtype.val hi
      simpa using this
    rw [← hi', ← conj_zpow, ← hk', ← zpow_mul, ← zpow_mul, mul_comm]
  apply Sec53.mem_normalizer_of_conj_le
  intro y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨k, hk⟩ := hpow
  rw [← conj_zpow, hk, ← zpow_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

theorem three_not_dvd_B (hp : s.p = 3) : ¬ 3 ∣ Nat.card f5.B := by
  intro h3
  have := f5.card_B
  rw [Hyp.q, hp] at this
  have h3' : 3 ∣ 3 ^ s.f := dvd_pow_self 3 s.f_pos.ne'
  have h3'' : 3 ∣ 3 ^ s.f - 1 := this ▸ (Dvd.dvd.mul_left h3 2)
  have := Nat.dvd_sub h3' h3''
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at this
  norm_num at this

theorem inf_B_eq_bot (hp : s.p = 3) {Q : Subgroup G} (hQ : IsPGroup 3 Q) : Q ⊓ f5.B = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hQ.to_le (inf_le_left : Q ⊓ f5.B ≤ Q))
  have h1 : Nat.card (Q ⊓ f5.B : Subgroup G) ∣ Nat.card f5.B :=
    Subgroup.card_dvd_of_le inf_le_right
  have hk0 : k = 0 := by
    by_contra hk0
    exact f5.three_not_dvd_B hp ((dvd_pow_self 3 hk0).trans (hk ▸ h1))
  rw [hk0, pow_zero] at hk
  have := Subgroup.eq_bot_of_card_eq _ hk
  rw [this] at hy
  exact (Subgroup.mem_bot.mp hy)

theorem inf_E_eq_bot (h26i : S_lemma_2_6_i) (hp : s.p = 3) {Q : Subgroup G}
    (hQ : IsPGroup 3 Q) (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G)) : Q ⊓ s.fr.E = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyQ, hyE⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  obtain ⟨b, hb, hne⟩ := f5.exists_not_comm_B h26i hyE hy1
  apply hne
  have h1 : y * b * y⁻¹ * b⁻¹ ∈ f5.B := f5.B.mul_mem
    ((Subgroup.mem_normalizer_iff.mp (f5.E_le_normalizer_B hyE) b).mp hb) (f5.B.inv_mem hb)
  have h2 : y * b * y⁻¹ * b⁻¹ ∈ Q := by
    rw [show y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) by group]
    exact Q.mul_mem hyQ ((Subgroup.mem_normalizer_iff.mp (hBQ hb) y⁻¹).mp (Q.inv_mem hyQ))
  have h3 : y * b * y⁻¹ * b⁻¹ ∈ Q ⊓ f5.B := Subgroup.mem_inf.mpr ⟨h2, h1⟩
  rw [f5.inf_B_eq_bot hp hQ, Subgroup.mem_bot] at h3
  calc y * b = (y * b * y⁻¹ * b⁻¹) * (b * y) := by group
    _ = b * y := by rw [h3, one_mul]

theorem fpf_of_isPGroup
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) :
    ∀ b ∈ f5.B, b ≠ 1 → ∀ y ∈ Q, b * y = y * b → y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro b hb hb1 y hyQ hby
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 s.fr.E) := inferInstance
  set P₀ := (S₀ : Subgroup s.fr.E).map s.fr.E.subtype with hP₀def
  have hP₀E : P₀ ≤ s.fr.E := Subgroup.map_subtype_le _
  have hP₀3 : IsPGroup 3 P₀ := S₀.isPGroup'.map _
  have hP₀card : Nat.card P₀ = 3 ^ (Nat.card s.fr.E).factorization 3 := by
    rw [hP₀def, Subgroup.card_map_of_injective s.fr.E.subtype_injective,
      Sylow.card_eq_multiplicity]
  set C := Q ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) with hCdef
  have hEb := f5.E_le_normalizer_zpowers hb
  have hP₀C : P₀ ≤ Subgroup.normalizer (C : Set G) := fun e he =>
    Sec54.mem_normalizer_inf (hEQ (hP₀E he))
      (Sec54.mem_normalizer_centralizer (hEb (hP₀E he)))
  have hC3 : IsPGroup 3 C := hQ.to_le inf_le_left
  have hinf : C ⊓ P₀ = ⊥ := by
    have := f5.inf_E_eq_bot h26i hp hQ hBQ
    rw [eq_bot_iff, ← this]
    exact inf_le_inf inf_le_left hP₀E
  have hcard := Sec54.card_sup_eq_mul hP₀C hinf
  have hle : C ⊔ P₀ ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    sup_le (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)) (hP₀E.trans hEb)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcard, hP₀card] at hdvd
  have h53 := lemma_5_3_of h22 G s hp f5 hb hb1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hC3
  rw [hk, ← pow_add] at hdvd
  have hfac := (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  have hk0 : k = 0 := by omega
  rw [hk0, pow_zero] at hk
  have hC1 := Subgroup.eq_bot_of_card_eq C hk
  have hyC : y ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨hyQ, ?_⟩
    rw [Sec52.centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
    exact hby.symm
  rw [hC1, Subgroup.mem_bot] at hyC
  exact hyC

theorem card_eq_q_pow (hp : s.p = 3) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hfpf : ∀ b ∈ f5.B, b ≠ 1 → ∀ y ∈ Q, b * y = y * b → y = 1) :
    ∃ k, Nat.card Q = s.q ^ k := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ
  let := JT.conjAct f5.B Q hBQ
  have hdvd := Sec56.card_dvd_card_sub_one_of_fpf (B := f5.B) (M := Q) 1 (fun b => smul_one b)
    (fun b hb1 y hy => by
      have h1 : (b : G) * y * (b : G)⁻¹ = y := congrArg Subtype.val hy
      apply Subtype.ext
      apply hfpf b b.2 (fun h => hb1 (Subtype.ext h)) y y.2
      calc (b : G) * y = (b : G) * y * (b : G)⁻¹ * b := by group
        _ = y * b := by rw [h1])
  rw [hm] at hdvd
  have hn := Sec56.dvd_of_dvd_three_pow_sub_one s.f_pos (by rw [f5.card_B, Hyp.q, hp]) hdvd
  obtain ⟨k, rfl⟩ := hn
  exact ⟨k, by rw [hm, Hyp.q, hp, pow_mul]⟩

open Sec52 in
theorem card_inf_centralizer_le
    (h26i : S_lemma_2_6_i) (hJR : S_IsJRSubgroup_nonempty_jrGroup)
    (hR : RFacts) (hp : s.p = 3) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E)
    (hox : orderOf x = 3) :
    Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ s.q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.zpowers x with hXdef
  have hXE : X ≤ s.fr.E := Subgroup.zpowers_le.mpr hxE
  have hXcard : Nat.card X = 3 := by rw [Nat.card_zpowers, hox]
  have hX1 : X ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hXcard
    norm_num at hXcard
  have heX : s.eX X = 3 := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one, hXcard]
  obtain ⟨hediv, -, -⟩ := h26i G s.toHyp s.fr hXE hX1
  rw [heX] at hediv
  set m := s.f / 3 with hm
  have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd s.f_pos hediv) (by norm_num)
  have hf : s.f = 3 * m := (Nat.mul_div_cancel' hediv).symm
  have hLS := s.L_spec X hXE hX1
  obtain ⟨K', hK'jr, -⟩ := hLS.jr
  have hfpos : 0 < s.f / s.eX X := by rw [heX]; exact hmpos
  obtain ⟨hL', hL'p, hL'f, -, -⟩ := hJR G s.p_ne_two hfpos hK'jr
  have hq' : hL'.q = 3 ^ m := by rw [JRGroup.q, hL'p, hL'f, heX, hp]
  have hq'5 : hL'.q ≠ 5 := by
    rw [hq']
    intro h
    have : (3 : ℕ) ∣ 5 := h ▸ dvd_pow_self 3 hmpos.ne'
    norm_num at this
  obtain ⟨⟨-, hns, -, hsolv⟩, -⟩ := hR _ hL' hq'5
  have hLcard : ∃ e u, Nat.card (s.L X) = 3 ^ e * u ∧ ¬ 3 ∣ u ∧ e ≤ 3 * m := by
    by_cases hsol : Group.IsSolvable (s.L X)
    · obtain ⟨-, h168, -⟩ := hsolv hsol
      exact ⟨1, 56, by rw [h168]; norm_num, by norm_num, by omega⟩
    · have h := hns hsol
      rw [hq'] at h
      refine ⟨3 * m, ((3 ^ m) ^ 3 + 1) * (3 ^ m - 1), ?_, ?_, le_rfl⟩
      · rw [h, pow_mul']
        ring
      · intro h3
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
        · have h3m : 3 ∣ (3 ^ m) ^ 3 := dvd_pow (dvd_pow_self 3 hmpos.ne') (by norm_num)
          have := (Nat.dvd_add_right h3m).mp h
          norm_num at this
        · have h3m : 3 ∣ 3 ^ m := dvd_pow_self 3 hmpos.ne'
          have := Nat.dvd_sub h3m h
          rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at this
          norm_num at this
  have hCXeq := hLS.centralizer_eq (by rw [s.F_eq_bot]; exact bot_le)
  have hDN : Subgroup.centralizer (X : Set G) ⊓ s.fr.E ≤
      Subgroup.normalizer ((s.L X : Subgroup G) : Set G) := by
    intro d hd
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    have hdN : d ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hd).1
    exact Subgroup.mem_subgroupOf.mp (hLS.normal.2.conj_mem ⟨y, hLS.normal.1 hy⟩
      (Subgroup.mem_subgroupOf.mpr hy) ⟨d, hdN⟩)
  have h1 := card_sup_mul_card_inf hDN
  rw [sup_comm, ← hCXeq] at h1
  have hdvdC : Nat.card (Subgroup.centralizer (X : Set G)) ∣
      Nat.card (s.L X) * Nat.card s.fr.E :=
    (Dvd.intro _ h1).trans (Nat.mul_dvd_mul_left _ (Subgroup.card_dvd_of_le inf_le_right))
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 s.fr.E) := inferInstance
  set P₀ := (S₀ : Subgroup s.fr.E).map s.fr.E.subtype with hP₀def
  have hP₀E : P₀ ≤ s.fr.E := Subgroup.map_subtype_le _
  have hP₀card : Nat.card P₀ = 3 ^ (Nat.card s.fr.E).factorization 3 := by
    rw [hP₀def, Subgroup.card_map_of_injective s.fr.E.subtype_injective,
      Sylow.card_eq_multiplicity]
  have hP₀CX : P₀ ≤ Subgroup.centralizer (X : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => s.E_comm_all y (hXE hy) e (hP₀E he)
  set C := Q ⊓ Subgroup.centralizer (X : Set G) with hCdef
  have hP₀C : P₀ ≤ Subgroup.normalizer (C : Set G) := fun e he =>
    Sec54.mem_normalizer_inf (hEQ (hP₀E he)) (Subgroup.le_normalizer (hP₀CX he))
  have hinf : C ⊓ P₀ = ⊥ := by
    have := f5.inf_E_eq_bot h26i hp hQ hBQ
    rw [eq_bot_iff, ← this]
    exact inf_le_inf inf_le_left hP₀E
  have hcard := Sec54.card_sup_eq_mul hP₀C hinf
  have hle : C ⊔ P₀ ≤ Subgroup.centralizer (X : Set G) := sup_le inf_le_right hP₀CX
  have hdvd := (Subgroup.card_dvd_of_le hle).trans hdvdC
  rw [hcard, hP₀card] at hdvd
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hQ.to_le (inf_le_left : C ≤ Q))
  obtain ⟨e, u, hLe, hu, he⟩ := hLcard
  rw [hj, ← pow_add, hLe] at hdvd
  have h2 := Sec56.le_of_pow_dvd hu Nat.card_pos.ne' hdvd
  have hCC : Q ⊓ Subgroup.centralizer ({x} : Set G) = C := by
    rw [hCdef, hXdef, centralizer_zpowers_eq]
  rw [hCC, hj, Hyp.q, hp, hf]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

open Sec52 in
theorem card_inf_centralizer_pow_three_and_lift
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i)
    (hp : s.p = 3) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E)
    (hox : orderOf x = 3) :
    Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ^ 3 = Nat.card Q ∧
      ∀ i, ∀ c ∈ (Sec56.lpc 3 Q i).map Q.subtype,
        c⁻¹ * (x * c * x⁻¹) ∈ (Sec56.lpc 3 Q (i + 1)).map Q.subtype →
        ∃ a ∈ (Sec56.lpc 3 Q i).map Q.subtype, x * a = a * x ∧
          ∃ b ∈ (Sec56.lpc 3 Q (i + 1)).map Q.subtype, c = a * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfpf := f5.fpf_of_isPGroup h22 h26i hp hQ hBQ hEQ
  set Γ := Subgroup.normalizer (Q : Set G) with hΓdef
  let := JT.conjAct Γ Q le_rfl
  have hxΓ : x ∈ Γ := hEQ hxE
  set x' : Γ := ⟨x, hxΓ⟩ with hx'def
  have hox' : orderOf x' = 3 := by rw [hx'def, Subgroup.orderOf_mk, hox]
  have hxB : x ∈ Subgroup.normalizer (f5.B : Set G) := f5.E_le_normalizer_B hxE
  have hφmem : ∀ b ∈ f5.B, x * b * x⁻¹ * b⁻¹ ∈ f5.B := fun b hb =>
    f5.B.mul_mem ((Subgroup.mem_normalizer_iff.mp hxB b).mp hb) (f5.B.inv_mem hb)
  let φ : f5.B →* f5.B :=
    { toFun := fun b => ⟨x * b * x⁻¹ * b⁻¹, hφmem b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun b c => Subtype.ext (by
        have hxc : x * (c : G) * x⁻¹ ∈ f5.B := (Subgroup.mem_normalizer_iff.mp hxB c).mp c.2
        have h1 := f5.B_comm _ (f5.B.inv_mem b.2) _ (f5.B.mul_mem hxc (f5.B.inv_mem c.2))
        simp only [Subgroup.coe_mul]
        calc x * ((b : G) * c) * x⁻¹ * ((b : G) * c)⁻¹
            = (x * b * x⁻¹) * ((x * c * x⁻¹ * (c : G)⁻¹) * (b : G)⁻¹) := by group
          _ = (x * b * x⁻¹) * ((b : G)⁻¹ * (x * c * x⁻¹ * (c : G)⁻¹)) := by rw [← h1]
          _ = x * b * x⁻¹ * (b : G)⁻¹ * (x * c * x⁻¹ * (c : G)⁻¹) := by group) }
  set N₀G := (φ.range).map f5.B.subtype with hN₀Gdef
  have hN₀GB : N₀G ≤ f5.B := Subgroup.map_subtype_le _
  have hN₀GΓ : N₀G ≤ Γ := hN₀GB.trans hBQ
  set N₀ := N₀G.subgroupOf Γ with hN₀def
  have hmemN₀ : ∀ n : Γ, n ∈ N₀ ↔ (n : G) ∈ N₀G := fun n => Subgroup.mem_subgroupOf
  have hN₀ab : IsMulCommutative N₀ := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (f5.B_comm _ (hN₀GB ((hmemN₀ a).mp a.2)) _ (hN₀GB ((hmemN₀ b).mp b.2))))⟩⟩
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ := by
    intro h3
    have h1 : Nat.card N₀ = Nat.card N₀G :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀GΓ).toEquiv
    exact f5.three_not_dvd_B hp ((h1 ▸ h3).trans (Subgroup.card_dvd_of_le hN₀GB))
  have hxN₀ : x' ∈ Subgroup.normalizer (N₀ : Set Γ) := by
    apply Sec53.mem_normalizer_of_conj_le
    intro n hn
    rw [hmemN₀] at hn ⊢
    obtain ⟨_, ⟨b, rfl⟩, hnb⟩ := hn
    have hxb : x * (b : G) * x⁻¹ ∈ f5.B := (Subgroup.mem_normalizer_iff.mp hxB b).mp b.2
    refine ⟨φ ⟨_, hxb⟩, ⟨⟨_, hxb⟩, rfl⟩, ?_⟩
    change x * (x * b * x⁻¹) * x⁻¹ * (x * b * x⁻¹)⁻¹ = x * (n : G) * x⁻¹
    rw [← hnb]
    change _ = x * (x * b * x⁻¹ * (b : G)⁻¹) * x⁻¹
    group
  have hxfpf : ∀ n ∈ N₀, x' * n * x'⁻¹ = n → n = 1 := by
    intro n hn hxn
    rw [hmemN₀] at hn
    obtain ⟨_, ⟨b, rfl⟩, hnb⟩ := hn
    have hxn' : x * (n : G) * x⁻¹ = n := congrArg Subtype.val hxn
    have hnb' : (n : G) = x * b * x⁻¹ * (b : G)⁻¹ := hnb.symm
    have hcb : x * (b : G) * x⁻¹ = (n : G) * b := by
      rw [hnb']
      group
    have hx3 : x * x * x = 1 := (pow_three' x).symm.trans (hox ▸ pow_orderOf_eq_one x)
    have h2 : (x * x) * (b : G) * (x * x)⁻¹ = (n : G) * n * b := by
      calc (x * x) * (b : G) * (x * x)⁻¹ = x * (x * b * x⁻¹) * x⁻¹ := by group
        _ = x * ((n : G) * b) * x⁻¹ := by rw [hcb]
        _ = (x * (n : G) * x⁻¹) * (x * b * x⁻¹) := by group
        _ = (n : G) * ((n : G) * b) := by rw [hxn', hcb]
        _ = (n : G) * n * b := by group
    have h3 : (x * x * x) * (b : G) * (x * x * x)⁻¹ = (n : G) * n * n * b := by
      calc (x * x * x) * (b : G) * (x * x * x)⁻¹ = x * ((x * x) * b * (x * x)⁻¹) * x⁻¹ := by
            group
        _ = x * ((n : G) * n * b) * x⁻¹ := by rw [h2]
        _ = (x * (n : G) * x⁻¹) * (x * (n : G) * x⁻¹) * (x * b * x⁻¹) := by group
        _ = (n : G) * n * ((n : G) * b) := by rw [hxn', hcb]
        _ = (n : G) * n * n * b := by group
    rw [hx3, one_mul, inv_one, mul_one] at h3
    have hc3 : (n : G) ^ 3 = 1 := by
      rw [pow_three']
      have := congrArg (· * (b : G)⁻¹) h3
      simpa using this.symm
    have hcB : (n : G) ∈ f5.B := by
      rw [← hnb]
      exact (φ b).2
    have hoc : orderOf (n : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have hc1 : (n : G) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hoc with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        apply f5.three_not_dvd_B hp
        rw [← h]
        exact Subgroup.orderOf_dvd_natCard _ hcB
    exact Subtype.ext hc1
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hox
    norm_num at hox
  obtain ⟨b₀, hb₀, hb₀x⟩ := f5.exists_not_comm_B h26i hxE hx1
  have hfix : ∀ a : Q, (∀ r ∈ N₀, r • a = a) → a = 1 := by
    intro a ha
    set n₀ : G := x * b₀ * x⁻¹ * b₀⁻¹ with hn₀
    have hn₀N : n₀ ∈ N₀G := ⟨φ ⟨b₀, hb₀⟩, ⟨⟨b₀, hb₀⟩, rfl⟩, rfl⟩
    have hn₀1 : n₀ ≠ 1 := by
      intro h
      apply hb₀x
      calc x * b₀ = n₀ * (b₀ * x) := by rw [hn₀]; group
        _ = b₀ * x := by rw [h, one_mul]
    have h1 := ha ⟨n₀, hN₀GΓ hn₀N⟩ ((hmemN₀ _).mpr hn₀N)
    have h2 : n₀ * (a : G) * n₀⁻¹ = a := congrArg Subtype.val h1
    apply Subtype.ext
    apply hfpf n₀ (hN₀GB hn₀N) hn₀1 a a.2
    calc n₀ * (a : G) = n₀ * (a : G) * n₀⁻¹ * n₀ := by group
      _ = a * n₀ := by rw [h2]
  have hQ3 : IsPGroup 3 Q := hQ
  obtain ⟨key, hlift⟩ := Sec56.card_fix_pow_three_and_lift hQ3 hox' N₀ hN₀ab hN₀3 hxN₀ hxfpf
    hfix
  refine ⟨?_, ?_⟩
  · rw [← key]
    congr 1
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩, Subtype.ext (by
          have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2
          change x * (y : G) * x⁻¹ = y
          rw [← this, mul_inv_cancel_right])⟩
        invFun := fun y => ⟨y.1, Subgroup.mem_inf.mpr ⟨y.1.2, by
          have h1 : x * (y.1 : G) * x⁻¹ = y.1 := congrArg Subtype.val y.2
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc (y.1 : G) * x = x * (y.1 : G) * x⁻¹ * x := by rw [h1]
            _ = x * y.1 := by group⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · intro i c hc hcx
    obtain ⟨n, hn, rfl⟩ := hc
    obtain ⟨m, hm, hmeq⟩ := hcx
    have hn' : n⁻¹ * (x' • n) ∈ Sec56.lpc 3 Q (i + 1) := by
      have : m = n⁻¹ * (x' • n) := Subtype.ext hmeq
      rw [← this]
      exact hm
    obtain ⟨a, ha, hax, b, hb, rfl⟩ := hlift i n hn hn'
    refine ⟨a, ⟨a, ha, rfl⟩, ?_, b, ⟨b, hb, rfl⟩, rfl⟩
    have h1 : x * (a : G) * x⁻¹ = a := congrArg Subtype.val hax
    calc x * (a : G) = x * (a : G) * x⁻¹ * x := by group
      _ = a * x := by rw [h1]

theorem card_inf_centralizer_pow_three
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i)
    (hp : s.p = 3) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E)
    (hox : orderOf x = 3) :
    Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ^ 3 = Nat.card Q :=
  (f5.card_inf_centralizer_pow_three_and_lift h22 h26i hp hQ hBQ hEQ hxE hox).1

end Frame5

end CFSG.Walter.W67
