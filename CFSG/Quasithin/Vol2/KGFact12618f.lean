module

public import CFSG.Quasithin.Vol2.KGFact12618e
public import CFSG.Quasithin.Vol2.KGFact12618Lie
public import CFSG.Quasithin.Vol2.KGFact12614Proof
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.B5FinS8Core
public import CFSG.RankThree.SubgroupLists.LinearThreeFamily
public import CFSG.Quasithin.Vol2.KGFact12618

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Arith

theorem two_pow_odd_mod_five {n : ℕ} (hn : Odd n) : 2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 := by
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero => left; rfl
  | succ m ih =>
    have h : 2 ^ (2 * (m + 1) + 1) = 2 ^ (2 * m + 1) * 4 := by ring
    rw [h, Nat.mul_mod]
    rcases ih with h1 | h1 <;> rw [h1] <;> norm_num

theorem not_five_dvd_of_odd {n : ℕ} (hn : Odd n) :
    ¬ 5 ∣ (2 ^ n) ^ 3 ∧ ¬ 5 ∣ (2 ^ n) ^ 6 ∧ ¬ 5 ∣ (2 ^ n) ^ 2 - 1 ∧ ¬ 5 ∣ (2 ^ n) ^ 3 - 1 ∧
      ¬ 5 ∣ (2 ^ n) ^ 6 - 1 := by
  have hq := two_pow_odd_mod_five hn
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have p2 : (2 ^ n) ^ 2 % 5 = 4 := by
    rw [Nat.pow_mod]
    rcases hq with h | h <;> rw [h]
  have p3 : (2 ^ n) ^ 3 % 5 = 3 ∨ (2 ^ n) ^ 3 % 5 = 2 := by
    rw [Nat.pow_mod]
    rcases hq with h | h <;> rw [h] <;> simp
  have p6 : (2 ^ n) ^ 6 % 5 = 4 := by
    rw [Nat.pow_mod]
    rcases hq with h | h <;> rw [h]
  have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ (2 ^ n) ^ 6 := Nat.one_le_pow _ _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

end Arith

section Matrices

variable {F : Type} [Field F]

theorem det_eq_one_of_mem_statedSL {n : ℕ} {g : GL (Fin n) F} (hg : g ∈ StatedSL n F) :
    (g : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem sq_eq_one_of_pow_four_sl2 (h2 : (2 : F) = 0) (x : ↥(StatedSL 2 F)) (hx : x ^ 4 = 1) :
    x ^ 2 = 1 := by
  set m : Matrix (Fin 2) (Fin 2) F := ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hmdef
  have hdet : m.det = 1 := det_eq_one_of_mem_statedSL x.2
  have hm4 : m ^ 4 = 1 := by
    have := congrArg (fun A : ↥(StatedSL 2 F) => ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      hx
    simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] using this
  set t := m 0 0 + m 1 1
  have hdet' : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  have htr : (m ^ 4).trace = (1 : Matrix (Fin 2) (Fin 2) F).trace := by rw [hm4]
  simp only [Matrix.trace_fin_two, pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.one_apply_eq] at htr
  have ht4 : t ^ 4 = 0 := by
    linear_combination htr + (2 * t ^ 2 * (m 0 0 * m 1 1 - m 0 1 * m 1 0) -
      (m 0 0 * m 1 1 - m 0 1 * m 1 0) ^ 2 + 1) * h2
  have ht : t = 0 := pow_eq_zero_iff (by norm_num) |>.mp ht4
  have hm2 : m ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sq, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination (m 0 1) * ht
        | linear_combination (m 1 0) * ht
        | linear_combination (m 0 0) * ht - hdet' - h2
        | linear_combination (m 1 1) * ht - hdet' - h2
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  exact hm2

end Matrices

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem sq_eq_one_of_pow_two_pow {K : Subgroup Γ} (h4 : ∀ x ∈ K, x ^ 4 = 1 → x ^ 2 = 1) :
    ∀ (k : ℕ) {y : Γ}, y ∈ K → y ^ 2 ^ k = 1 → y ^ 2 = 1
  | 0, y, _, h => by rw [pow_zero, pow_one] at h; rw [h, one_pow]
  | 1, y, _, h => by rwa [pow_one] at h
  | k + 2, y, hy, h => by
    apply sq_eq_one_of_pow_two_pow h4 (k + 1) hy
    have h1 := h4 (y ^ 2 ^ k) (K.pow_mem hy _) (by
      rw [← pow_mul, show 2 ^ k * 4 = 2 ^ (k + 2) by ring]
      exact h)
    rwa [← pow_mul, show 2 ^ k * 2 = 2 ^ (k + 1) by ring] at h1

theorem false_of_sq_of_pow_four {B K : Subgroup Γ} (hBK : B ≤ K)
    (h4 : ∀ x ∈ K, x ^ 4 = 1 → x ^ 2 = 1) (φ : ↥B →* ↥(alternatingGroup (Fin 6)))
    (hφs : Function.Surjective φ) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 with hc
  have hcA : c ∈ alternatingGroup (Fin 6) := Perm.mem_alternatingGroup.2 (by decide)
  have hc4 : orderOf c = 2 ^ (1 + 1) := orderOf_eq_prime_pow (by decide) (by decide)
  obtain ⟨b, hb⟩ := hφs ⟨c, hcA⟩
  obtain ⟨k, u, hu, hku⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos b).ne'
  have hy : ((b : Γ) ^ u) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hku]
    have := pow_orderOf_eq_one b
    rw [← Subgroup.orderOf_coe] at this ⊢
    exact_mod_cast pow_orderOf_eq_one (b : Γ)
  have hy2 := sq_eq_one_of_pow_two_pow h4 k (K.pow_mem (hBK b.2) u) hy
  have hb2 : b ^ (u * 2) = 1 := by
    apply Subtype.ext
    rw [pow_mul]
    simpa using hy2
  have hc2 : c ^ (u * 2) = 1 := by
    have := congrArg (fun x => ((φ x : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6))) hb2
    simpa [hb] using this
  have hd := orderOf_dvd_of_pow_eq_one hc2
  rw [hc4] at hd
  obtain ⟨w, hw⟩ := hu
  omega

omit [Finite Γ] in
theorem pow_four_of_mulEquiv {K : Subgroup Γ} {X : Type*} [Group X] (eK : ↥K ≃* X)
    (h : ∀ x : X, x ^ 4 = 1 → x ^ 2 = 1) : ∀ x ∈ K, x ^ 4 = 1 → x ^ 2 = 1 := by
  intro x hx hx4
  have h1 : (⟨x, hx⟩ : ↥K) ^ 4 = 1 := Subtype.ext (by simpa using hx4)
  have h2 := h (eK ⟨x, hx⟩) (by rw [← map_pow, h1, map_one])
  rw [← map_pow, ← map_one eK] at h2
  have h3 := congrArg Subtype.val (eK.injective h2)
  simpa using h3

theorem card_inf_eq_of_sylow {T K : Subgroup Γ} (hTK : IsSylowTwoOf (T ⊓ K) K) {m u : ℕ}
    (hu : Odd u) (hK : Nat.card ↥K = 2 ^ m * u) : Nat.card ↥(T ⊓ K) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hTK.2.1
  have hodd := hTK.2.2
  have hu2 := Nat.odd_iff.1 hu
  have hc := ((T ⊓ K).subgroupOf K).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv, hj,
    hK] at hc
  have hjm : j ≤ m := by
    by_contra h
    have h1 : 2 ^ m * 2 ∣ 2 ^ m * u := by
      rw [← hc, ← pow_succ]
      exact (pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _)
    have := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    omega
  have hmj : m ≤ j := by
    by_contra h
    apply hodd
    have h1 : 2 ^ j * 2 ∣ 2 ^ j * ((T ⊓ K).subgroupOf K).index := by
      rw [hc, ← pow_succ]
      exact (pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _)
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
  rw [hj, show j = m by omega]

theorem false_of_sl52 (hL52 : FactKv12618L52) {Y K T T₀ B : Subgroup Γ}
    (hYK : Y ≤ Subgroup.normalizer (K : Set Γ)) (hKY : K ≤ Y)
    (eK : ↥K ≃* ↥(StatedSL 5 (ZMod 2))) (hT : IsSylowTwoOf T Y) (hBK : B ≤ K)
    (hT₀4 : T₀.relIndex T ≤ 4) (hT₀N : T₀ ≤ Subgroup.normalizer (B : Set Γ)) (hBB : ⁅B, B⁆ = B)
    (hBiso : Open.quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)))
    (hBc : ⁅Open.pCoreOf 2 B, B⁆ = ⊥) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := hBiso
  set B' := (B.subgroupOf K).map eK.toMonoidHom with hB'
  let ι : ↥B ≃* ↥B' := (Subgroup.subgroupOfEquivOfLe hBK).symm.trans
    ((B.subgroupOf K).equivMapOfInjective _ eK.injective)
  have hBK' : ⁅B.subgroupOf K, B.subgroupOf K⁆ = B.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hBK, hBB]
  have hperf : ⁅B', B'⁆ = B' := by rw [hB', ← Subgroup.map_commutator, hBK']
  have hiso : Open.quasithinO2QuotientIso B' ↥(alternatingGroup (Fin 6)) := by
    refine ⟨φ.comp ι.symm.toMonoidHom, hφs.comp ι.symm.surjective, ?_⟩
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 ι, ← hφk]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Subgroup.mem_map,
      MulEquiv.coe_toMonoidHom]
    constructor
    · intro hx
      exact ⟨ι.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hcent : ∀ z ∈ Open.pCore 2 ↥B, ∀ b : ↥B, z * b = b * z := by
    intro z hz b
    have h1 : ⁅(z : Γ), (b : Γ)⁆ ∈ ⁅Open.pCoreOf 2 B, B⁆ :=
      Subgroup.commutator_mem_commutator (by unfold Open.pCoreOf; exact ⟨z, hz, rfl⟩) b.2
    rw [hBc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subtype.ext h1
  have hcomm : ⁅Open.pCoreOf 2 B', B'⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    unfold Open.pCoreOf at hx
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 ι] at hx
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
    obtain ⟨b, rfl⟩ : ∃ b : ↥B, ((ι b : ↥B') : ↥(StatedSL 5 (ZMod 2))) = y :=
      ⟨ι.symm ⟨y, hy⟩, by simp⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have := congrArg (fun w => ((ι w : ↥B') : ↥(StatedSL 5 (ZMod 2)))) (hcent z hz b)
    simpa using this
  set T₂ := T₀ ⊓ (T ⊓ K) with hT₂
  set T₁ := (T₂.subgroupOf K).map eK.toMonoidHom with hT₁
  have hT₂K : T₂ ≤ K := inf_le_right.trans inf_le_right
  have hcT₁ : Nat.card ↥T₁ = Nat.card ↥T₂ := by
    rw [hT₁, Subgroup.card_map_of_injective eK.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₂K).toEquiv
  have hp2 : IsPGroup 2 ↥T₁ := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1
      (hT.2.1.to_le (inf_le_right.trans inf_le_left) : IsPGroup 2 ↥T₂)
    exact IsPGroup.of_card (by rw [hcT₁, hm])
  have hKn : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hYK
  have hTK := RankOneRecog.isSylowTwoOf_inf_of_subnormal hT hKY hKn.isSubnormal
  have hK : Nat.card ↥K = 2 ^ 10 * 9765 := by
    rw [Nat.card_congr eK.toEquiv, card_statedSL_five_zmod1527d]
    norm_num
  have hTK10 := card_inf_eq_of_sylow hTK (by decide) hK
  have hidx : T₀.relIndex (T ⊓ K) ≤ 4 :=
    (Subgroup.relIndex_le_of_le_right inf_le_left (relIndex_ne_zero_of_finite T₀ T)).trans hT₀4
  have hc := Subgroup.relIndex_mul_card T₀ (T ⊓ K)
  rw [hTK10, ← hT₂] at hc
  have hcard : 2 ^ 8 ≤ Nat.card ↥T₁ := by
    rw [hcT₁]
    norm_num at hc ⊢
    nlinarith [Nat.zero_le (Nat.card ↥T₂)]
  have hnorm : T₁ ≤ Subgroup.normalizer (B' : Set _) := by
    rw [hT₁, hB', ← Subgroup.map_equiv_normalizer_eq]
    apply Subgroup.map_mono
    intro t ht
    exact KG12614.mem_normalizer_subgroupOf (hT₀N (Subgroup.mem_subgroupOf.1 ht).1)
  exact hL52 B' T₁ hperf hiso hcomm hp2 hcard hnorm

theorem factKv12618_of (hLie : FactKv12618LieFam) (hL52 : FactKv12618L52) : FactKv12618 := by
  intro Γ _ _ Y K T T₀ B hKY hYK hKs hlist hT hYeq hO2 hBK hT₀ hT₀4 hT₀N hBB hBiso hBc
  classical
  have := hKs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := id hBiso
  have hD := KG12614.dataA6_of φ hφs (by exact hφk)
  obtain ⟨a, ha⟩ := hD.card
  have hBdvd : Nat.card ↥B ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hBK.le
  have h5K : 5 ∣ Nat.card ↥K :=
    (show 5 ∣ Nat.card ↥B by rw [ha]; exact dvd_mul_of_dvd_right (by norm_num) _).trans hBdvd
  have hBne : Nat.card ↥B ≠ Nat.card ↥K := fun h =>
    hBK.ne (Subgroup.eq_of_le_of_card_ge hBK.le h.ge)
  have hBle : Nat.card ↥B ≤ Nat.card ↥K := Nat.le_of_dvd Nat.card_pos hBdvd
  have h1a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hKnc : ∃ x y : ↥K, x * y ≠ y * x := by
    by_contra hc
    push Not at hc
    have hB1 : B = ⊥ := by
      rw [← hBB, eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      have := hc ⟨x, hBK.le hx⟩ ⟨y, hBK.le hy⟩
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val this
    rw [hB1, Subgroup.card_bot] at ha
    omega
  have hZK : 1 < Nat.card (Subgroup.center ↥K) → False := by
    intro hZ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · rw [h, Subgroup.card_bot] at hZ
      omega
    · obtain ⟨x, y, hxy⟩ := hKnc
      have hx : x ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top x
      exact hxy (Subgroup.mem_center_iff.1 hx y).symm
  have hF1 : ∀ (F : Type) [Field F] [Finite F], Nat.card F ≠ 1 := fun F _ _ h => by
    have := Finite.one_lt_card (α := F)
    omega
  rcases hlist with ⟨n, F, _, _, hF, ⟨eK⟩⟩ | ⟨n, F, _, _, hF, ⟨eK⟩⟩ | ⟨n, F, _, _, hF, ⟨eK⟩⟩ |
    ⟨n, F, _, _, hF, ⟨eK⟩⟩ | hA6 | hA7 | hHat | ⟨F, _, _, hF, ⟨eK⟩⟩ | hL4 | hL5
  ·
    have := FFC.charP_two_of_card_pow hF
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    exact (false_of_sq_of_pow_four hBK.le (pow_four_of_mulEquiv eK
      (sq_eq_one_of_pow_four_sl2 h2)) φ hφs).elim
  ·
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hodd
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact (hF1 F (by rw [hF]; rfl)).elim
      have hZ : Nat.card (Subgroup.center ↥K) = 3 := by
        rw [Nat.card_congr (Subgroup.centerCongr
          (eK.trans (specialLinearGroupEquivStatedSL 3 F).symm)).toEquiv,
          CFSG.RankThree.SubgroupLists.card_center_sl3, hF]
        have h3 : 3 ∣ 2 ^ (m + m) - 1 := by
          have h4 : 2 ^ (m + m) % 3 = 1 := by
            rw [← two_mul, pow_mul, Nat.pow_mod]
            norm_num
          have : 1 ≤ 2 ^ (m + m) := Nat.one_le_two_pow
          omega
        exact Nat.gcd_eq_right h3
      exact (hZK (by omega)).elim
    · obtain ⟨h1, -, h2, h3, -⟩ := not_five_dvd_of_odd hodd
      rw [Nat.card_congr eK.toEquiv, card_statedSL_three1527d, hF] at h5K
      rcases (Nat.Prime.dvd_mul (by norm_num)).1 h5K with h | h
      · exact (h1 h).elim
      rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
      · exact (h2 h).elim
      · exact (h3 h).elim
  ·
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact (hF1 F (by rw [hF]; rfl)).elim
      · have hK : Nat.card ↥K = 720 := by
          rw [Nat.card_congr eK.toEquiv,
            CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
          decide
        have hB360 : Nat.card ↥B = 360 := by
          rw [ha, hK] at hBdvd
          rw [ha, hK] at hBne
          rw [ha]
          rcases a with _ | _ | a
          · rfl
          · exact (hBne (by norm_num)).elim
          · have h1 := Nat.le_of_dvd (by norm_num) hBdvd
            have h2 : 4 ≤ 2 ^ (a + 2) := by
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
            nlinarith
        have hidx : (B.subgroupOf K).index = 2 := by
          have hc := (B.subgroupOf K).card_mul_index
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK.le).toEquiv, hB360, hK] at hc
          omega
        have hn := Subgroup.normal_of_index_eq_two hidx
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.subgroupOf K) with h | h
        · have hB1 : B = ⊥ := by
            have h2 := disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
            rwa [inf_eq_left.2 hBK.le] at h2
          rw [hB1, Subgroup.card_bot] at hB360
          omega
        · exact (hBK.ne (le_antisymm hBK.le (Subgroup.subgroupOf_eq_top.1 h))).elim
    · exact (hLie Γ Y K T T₀ B hKY hYK hKs (Or.inl ⟨n, F, inferInstance, inferInstance, hn, hF,
        ⟨eK⟩⟩) hT hYeq hO2 hBK hT₀ hT₀4 hT₀N hBB hBiso hBc).elim
  ·
    rcases Nat.even_or_odd n with hev | hodd
    · rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · exact (hF1 F (by rw [hF]; rfl)).elim
        · exact absurd hev (by decide)
      · exact (hLie Γ Y K T T₀ B hKY hYK hKs (Or.inr ⟨n, F, inferInstance, inferInstance, hn,
          hev, hF, ⟨eK⟩⟩) hT hYeq hO2 hBK hT₀ hT₀4 hT₀N hBB hBiso hBc).elim
    · obtain ⟨-, h6, h2, -, h6'⟩ := not_five_dvd_of_odd hodd
      rw [Nat.card_congr eK.toEquiv, card_quasithinG2_1527d hF, hF] at h5K
      rcases (Nat.Prime.dvd_mul (by norm_num)).1 h5K with h | h
      · exact (h6 h).elim
      rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
      · exact (h6' h).elim
      · exact (h2 h).elim
  ·
    obtain ⟨e6⟩ := hA6
    have hK : Nat.card ↥K = 360 := by
      rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    omega
  ·
    exact Or.inl ⟨hA7, a7_branch hYK hKY hKs hA7 hT hYeq hO2 hBK hBiso⟩
  ·
    exact (hZK (by rw [hHat.2.1]; norm_num)).elim
  ·
    have hG := card_quasithinG2_1527d (n := 1) (by rw [hF]; rfl)
    rw [hF] at hG
    have hd : Nat.card ↥K ∣ 12096 := by
      rw [Nat.card_congr eK.toEquiv]
      refine (Subgroup.card_dvd_of_le (Subgroup.commutator_le.2 fun x hx y hy => ?_)).trans
        (by rw [hG]; norm_num)
      rw [commutatorElement_def]
      exact (Open.quasithinG2 F).mul_mem ((Open.quasithinG2 F).mul_mem
        ((Open.quasithinG2 F).mul_mem hx hy) ((Open.quasithinG2 F).inv_mem hx))
        ((Open.quasithinG2 F).inv_mem hy)
    have := h5K.trans hd
    norm_num at this
  ·
    obtain ⟨eK⟩ := hL4
    have hα : Function.Bijective B5FinS8.alpha :=
      ⟨B5FinS8.slEquiv.symm.injective.comp B5FinS8.alphaHom_bijective.1,
        B5FinS8.alpha_surjective⟩
    let eA : ↥K ≃* ↥(alternatingGroup (Fin 8)) := eK.trans (MulEquiv.ofBijective _ hα).symm
    exact Or.inr ⟨⟨eA⟩, a8_branch hYK hKY eA hT hBK hT₀4 hT₀N hBB hBiso hBc⟩
  ·
    obtain ⟨eK⟩ := hL5
    exact (false_of_sl52 hL52 hYK hKY eK hT hBK.le hT₀4 hT₀N hBB hBiso hBc).elim

end CFSG.Quasithin.H13.KG12618
