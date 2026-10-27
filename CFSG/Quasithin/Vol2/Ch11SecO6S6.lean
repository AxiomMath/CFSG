module

public import CFSG.Quasithin.Vol2.Ch11SecO6S5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD.O6S

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecG.Bar
open CFSG.Quasithin.Vol2.Ch11.O6
open scoped MatrixGroups

section Arith

theorem card_GL_two_dvd (m : ℕ) (hm : m ≤ 8) :
    Nat.card (GL (Fin m) (ZMod 2)) ∣ 5348063769211699200 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases m <;> simp [Fin.prod_univ_succ]

theorem eq_gl8 :
    (5348063769211699200 : ℕ) = 17 * 31 * 127 * (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2) := by
  norm_num

theorem not_sq_dvd_gl8 {r : ℕ} (hr : r.Prime) (h11 : 11 ≤ r) :
    ¬ r ^ 2 ∣ 5348063769211699200 := by
  intro h
  rw [eq_gl8] at h
  have hcop : ∀ q : ℕ, q.Prime → q < 11 → Nat.Coprime r q := fun q hq hq11 =>
    (Nat.coprime_primes hr hq).mpr (by omega)
  have hc : Nat.Coprime (r ^ 2) (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2) := by
    apply Nat.Coprime.pow_left
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_) ?_
    · exact (hcop 2 Nat.prime_two (by norm_num)).pow_right _
    · exact (hcop 3 Nat.prime_three (by norm_num)).pow_right _
    · exact (hcop 5 Nat.prime_five (by norm_num)).pow_right _
    · exact (hcop 7 (by norm_num) (by norm_num)).pow_right _
  have h1 := hc.dvd_of_dvd_mul_right h
  have hr1 : r ∣ 17 * 31 * 127 := (dvd_pow_self r two_ne_zero).trans h1
  have key : r = 17 ∨ r = 31 ∨ r = 127 := by
    rcases (Nat.Prime.dvd_mul hr).mp hr1 with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h))
  rcases key with rfl | rfl | rfl <;> norm_num at h1

theorem not_five_cube_dvd_gl8 : ¬ 5 ^ 3 ∣ (5348063769211699200 : ℕ) := by
  norm_num

theorem card_mulAut_dvd_gl8 {E : Type} [Group E] [Finite E] (hcomm : ∀ a b : E, a * b = b * a)
    (hpow : ∀ e : E, e ^ 2 = 1) (hcard : Nat.card E ≤ 2 ^ 8) :
    Nat.card (MulAut E) ∣ 5348063769211699200 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsPGroup 2 E := fun e => ⟨1, by rw [pow_one, hpow]⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hE
  have hm8 : m ≤ 8 := by
    rw [hm] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hm
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e]
  exact card_GL_two_dvd m hm8


end Arith

section GL8



theorem factCase1GL8_holds : FactCase1GL8 := by
  intro G _ _ K n hlist h1 hKperf E _ _ hcommE hpowE hcardE ρ hall
  obtain ⟨p, hp, hp5', φK, hφKs, hφKk⟩ := h1
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by rcases hp5' with h | h <;> omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨φ, hφs, hφk, -⟩ := exists_kBar_hom hφKs hφKk
  have hsh := shape_of_lists hlist hp2 hφs
  have hD : Case1Data (KBar K) := case1Data_of_shape hsh
  have hOF : CFSG.oddCore (KBar K) = CFSG.fittingSubgroup (KBar K) := oddCore_eq hD
  have hKb : ⁅(⊤ : Subgroup (KBar K)), (⊤ : Subgroup (KBar K))⁆ = ⊤ :=
    commutator_top_eq_top hKperf
  have h2p := two_ne_zero_zmod hp5
  have hcard4 : 4 ≤ Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  set F := CFSG.fittingSubgroup (KBar K) with hFdef
  have hmemF : ∀ x : KBar K, φ x = 1 → x ∈ F := fun x hx => by
    rw [← hOF, ← hφk]
    exact hx
  obtain ⟨s, hφs1, e, hse⟩ := exists_two_elt_neg_one hφs
  have hsF : s ∉ F := fun h => by
    rw [← hOF, ← hφk, MonoidHom.mem_ker, hφs1] at h
    exact neg_one_ne_one h2p h
  have hs2 : s ^ 2 ∈ F := hmemF _ (by rw [map_pow, hφs1, neg_one_sq])
  have hsc' : ∀ x : KBar K, x⁻¹ * (MulAut.conj s) x ∈ F := fun x => hmemF _ (by
    rw [MulAut.conj_apply, map_mul, map_mul, map_mul, map_inv, map_inv, hφs1,
      show (-1 : SL(2, ZMod p)) * φ x = φ x * -1 by rw [neg_one_mul, mul_neg_one]]
    group)
  obtain ⟨r, hr, hrF, hinv⟩ := exists_prime_inverts hD hKb hsF hsc' hs2 hse
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    have := hD.struct.2.1 r hr hrF
    omega
  have hna := exists_not_triv r hD hrF (Or.inl hKb)
  have hnotneg : ∀ y : KBar K, φ y = -1 → ¬ ActsScalar r (MulAut.conj y) 1 := by
    intro y hy h1y
    have hf : y⁻¹ * s ∈ F := hmemF _ (by rw [map_mul, map_inv, hy, hφs1, inv_mul_cancel])
    have hfs : ActsScalar r (MulAut.conj (y⁻¹ * s)) 1 := by
      rw [← actsTrivially_iff]
      exact fitting_acts_triv r hf
    have h1s : ActsScalar r (MulAut.conj s) 1 := by
      have h' := ActsScalar.mul r h1y hfs
      rw [← map_mul, one_mul, mul_inv_cancel_left] at h'
      exact h'
    obtain ⟨x, z, hxz⟩ := hna
    apply hxz
    intro d hd
    exact mul_mem (inv_mem (le_frattiniIn_of_one_of_neg hr2 h1s hinv hd))
      (le_frattiniIn_of_one_of_neg hr2 h1s hinv
        ((CFSG.pCore_normal).conj_mem _ hd (x * z * x⁻¹ * z⁻¹)))
  have hZF : Subgroup.center (KBar K) ≤ F := by
    intro z hz
    have hcz : φ z ∈ Subgroup.center SL(2, ZMod p) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hφs g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    rcases (mem_center_iff h2p).mp hcz with h | h
    · exact hmemF z h
    · exfalso
      apply hnotneg z h
      intro d _
      rw [MulAut.conj_apply, ← Subgroup.mem_center_iff.mp hz d, mul_inv_cancel_right, pow_one,
        inv_mul_cancel]
      exact one_mem _
  set Nb : Subgroup (KBar K) := ρ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hNb
  have hNbn : Nb.Normal := (ρ.normal_ker).map _ (QuotientGroup.mk'_surjective _)
  have hsq : ∀ y ∈ Nb, y ^ 2 ∈ Subgroup.center (KBar K) := by
    rintro _ ⟨k, hk, rfl⟩
    have h := mem_center_of_mem_sectionCentralizer (pow_mem k.2 2) (hall k hk)
    have e : ((⟨(k : G) ^ 2, pow_mem k.2 2⟩ : ↥K) : KBar K) =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k) ^ 2 := by
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow]
      rfl
    rwa [e] at h
  have hNbFZ : ∀ y ∈ Nb, y ∈ F → y ∈ Subgroup.center (KBar K) := by
    intro y hy hyF
    have hodd : Odd (orderOf y) := by
      have h1 : orderOf y ∣ Nat.card F := by
        rw [← Subgroup.orderOf_mk y hyF]
        exact orderOf_dvd_natCard _
      have h2 : Odd (Nat.card F) := by
        rw [← hOF]
        exact Quasithin.A312.odd_card_oddCore _
      exact h2.of_dvd_nat h1
    obtain ⟨j, hj⟩ := hodd
    have e : y = (y ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [e]
    exact pow_mem (hsq y hy) _
  have hNbF : Nb ≤ F := by
    by_contra hcon
    have hne : Nb.map φ ≠ ⊥ := by
      intro hbot
      apply hcon
      intro y hy
      apply hmemF
      have : φ y ∈ Nb.map φ := Subgroup.mem_map_of_mem φ hy
      rwa [hbot, Subgroup.mem_bot] at this
    obtain ⟨n₀, hn₀, hφn₀⟩ := neg_one_mem_of_normal hcard4 h2p (hNbn.map φ hφs) hne
    apply hnotneg n₀ hφn₀
    refine actsScalar_one_of_comm_mem fun d hd => ?_
    have hcN : n₀ * d * n₀⁻¹ * d⁻¹ ∈ Nb := by
      have h' : d * n₀⁻¹ * d⁻¹ ∈ Nb := hNbn.conj_mem _ (inv_mem hn₀) d
      have e : n₀ * d * n₀⁻¹ * d⁻¹ = n₀ * (d * n₀⁻¹ * d⁻¹) := by group
      rw [e]
      exact mul_mem hn₀ h'
    have hcP : n₀ * d * n₀⁻¹ * d⁻¹ ∈ CFSG.pCore r (KBar K) :=
      mul_mem ((CFSG.pCore_normal).conj_mem _ hd n₀) (inv_mem hd)
    have hcZ := hNbFZ _ hcN (CFSG.pCore_le_fitting _ r hcP)
    have hfix : (MulAut.conj s) (n₀ * d * n₀⁻¹ * d⁻¹) = n₀ * d * n₀⁻¹ * d⁻¹ := by
      rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp hcZ s, mul_inv_cancel_right]
    exact mem_frattiniIn_of_neg_of_fix hr2 hinv hcP hfix
  set Z := Subgroup.center (KBar K) with hZ
  have hdvd : Z.index ∣ 5348063769211699200 := by
    have hkerW : ρ.ker ≤ Z.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := fun k hk =>
      hNbFZ _ ⟨k, hk, rfl⟩ (hNbF ⟨k, hk, rfl⟩)
    rw [← Subgroup.index_comap_of_surjective Z (QuotientGroup.mk'_surjective _)]
    calc (Z.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).index ∣ ρ.ker.index :=
          Subgroup.index_dvd_of_le hkerW
      _ = Nat.card ρ.range := Subgroup.index_ker ρ
      _ ∣ Nat.card (MulAut E) := Subgroup.card_subgroup_dvd_card _
      _ ∣ 5348063769211699200 := card_mulAut_dvd_gl8 hcommE hpowE hcardE
  have hFidx : F.index = p * (p ^ 2 - 1) := by
    rw [← hOF, ← hφk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs,
      Subgroup.card_top, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
  have hmul : Z.index = Z.relIndex F * (p * (p ^ 2 - 1)) := by
    rw [← hFidx, Subgroup.relIndex_mul_index hZF]
  have hrsq : r ^ 2 ∣ Z.relIndex F := by
    set P := CFSG.pCore r (KBar K) with hP
    have hZP : Z ⊓ P ≤ frattiniIn P := fun z hz =>
      mem_frattiniIn_of_neg_of_fix hr2 hinv hz.2
        (by rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp hz.1 s, mul_inv_cancel_right])
    have hΦP : frattiniIn P ≤ P := Subgroup.map_subtype_le _
    have hPΦ : (frattiniIn P).relIndex P = r ^ 2 := by
      rw [Subgroup.relIndex, frattiniIn, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
      exact card_frattiniQuot_eq r hD hrF hna
    have h1 : r ^ 2 ∣ Z.relIndex P := by
      rw [← Subgroup.inf_relIndex_right, ← Subgroup.relIndex_mul_relIndex (Z ⊓ P) _ P hZP hΦP,
        hPΦ]
      exact dvd_mul_left _ _
    have h2 : Z.relIndex P ∣ Z.relIndex F := by
      have hPF : P ≤ F := CFSG.pCore_le_fitting _ r
      rw [← Subgroup.relIndex_subgroupOf hPF]
      exact Subgroup.relIndex_dvd_index_of_normal _ _
    exact h1.trans h2
  have hdiv : r ^ 2 * (p * (p ^ 2 - 1)) ∣ 5348063769211699200 :=
    (mul_dvd_mul_right hrsq _).trans (hmul ▸ hdvd)
  rcases hsh with h4 | ⟨q, hq, hq5, -, -, hE, -⟩
  · have hp5eq : p = 5 := A313.p_eq_five_of_case4 hOF.symm h4 hp
      ⟨(QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩
    subst hp5eq
    rcases (h4.2.2.2 r hr hrF).1 with h | h | h
    · exact not_sq_dvd_gl8 hr (SecE.eleven_le_of_mod_five hr (Or.inl h))
        ((dvd_mul_right _ _).trans hdiv)
    · exact not_sq_dvd_gl8 hr (SecE.eleven_le_of_mod_five hr (Or.inr h))
        ((dvd_mul_right _ _).trans hdiv)
    · subst h
      exact not_five_cube_dvd_gl8 ((show 5 ^ 3 ∣ 5 ^ 2 * (5 * (5 ^ 2 - 1)) by norm_num).trans hdiv)
  · obtain ⟨eF⟩ := hE
    have hcardF : Nat.card F = q ^ 2 := by
      rw [Nat.card_congr eF.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have hrq : r = q :=
      (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow (hcardF ▸ hrF))
    subst hrq
    exact not_sq_dvd_gl8 hr (SecE.eleven_le_of_mod_five hr hq5) ((dvd_mul_right _ _).trans hdiv)

end GL8

end CFSG.Quasithin.Vol2.Ch11.SecD.O6S
