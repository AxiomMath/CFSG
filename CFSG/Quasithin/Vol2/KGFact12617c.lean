module

public import CFSG.Quasithin.Vol2.KGFact12618e
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv
open scoped commutatorElement

section Five

theorem eq_of_dvd_eight_of_modEq_five {a b : ℕ} (ha : a ∣ 8) (hb : b ∣ a)
    (h : a ≡ b [MOD 5]) : b = a := by
  have ha0 : a ≠ 0 := by rintro rfl; norm_num at ha
  have ha8 : a ≤ 8 := Nat.le_of_dvd (by norm_num) ha
  have hba : b ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hb
  unfold Nat.ModEq at h
  interval_cases a <;> interval_cases b <;> simp_all

theorem commute_of_orderOf_eq_five {X : Type*} [Group X] [Finite X] (P : Subgroup X) [P.Normal]
    (hP : Nat.card ↥P ∣ 8) {x : X} (hx : orderOf x = 5) : ∀ z ∈ P, x * z = z * x := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set G : Subgroup (ConjAct X) := Subgroup.zpowers (ConjAct.toConjAct x) with hG
  have hG5 : IsPGroup 5 ↥G := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers]
    simp [hx]
  have hmod := hG5.card_modEq_card_fixedPoints (α := ↥P)
  set F := FixedPoints.subgroup ↥G ↥P with hF
  have hcF : Nat.card (MulAction.fixedPoints ↥G ↥P) = Nat.card ↥F := rfl
  rw [hcF] at hmod
  have hFP : Nat.card ↥F = Nat.card ↥P :=
    eq_of_dvd_eight_of_modEq_five hP F.card_subgroup_dvd_card hmod
  have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F hFP
  intro z hz
  have hzF : (⟨z, hz⟩ : ↥P) ∈ F := htop ▸ Subgroup.mem_top _
  have h1 := hzF ⟨ConjAct.toConjAct x, Subgroup.mem_zpowers _⟩
  have h2 : x * z * x⁻¹ = z := congrArg Subtype.val h1
  calc x * z = x * z * x⁻¹ * x := by group
    _ = z * x := by rw [h2]

theorem commute_of_ker_card_dvd_eight {X : Type*} [Group X] [Finite X]
    (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) (φ : X →* ↥(alternatingGroup (Fin 6)))
    (hφs : Function.Surjective φ) (hP2 : IsPGroup 2 ↥φ.ker) (hP : Nat.card ↥φ.ker ∣ 8) :
    ∀ z ∈ φ.ker, ∀ y : X, z * y = y * z := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hX : Nat.card X = 360 * Nat.card ↥φ.ker := by
    rw [φ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv, hA6]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5
    (show 5 ∣ Nat.card X by rw [hX]; exact dvd_mul_of_dvd_left (by norm_num) _)
  have hφx : φ x ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := hP2 ⟨x, h⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd := orderOf_dvd_of_pow_eq_one hk'
    rw [hx] at hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow hd)
    norm_num at this
  have hxc := commute_of_orderOf_eq_five φ.ker hP hx
  set C := Subgroup.centralizer (φ.ker : Set X) with hC
  have hxC : x ∈ C := Subgroup.mem_centralizer_iff.2 fun z hz => (hxc z hz).symm
  have hCn : C.Normal := inferInstance
  have hCmap : C.map φ = ⊤ := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have : (C.map φ).Normal := hCn.map φ hφs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map φ) with h | h
    · exact absurd ((Subgroup.map_eq_bot_iff _).1 h hxC) hφx
    · exact h
  have hQ2 : IsPGroup 2 (X ⧸ C) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : φ y ∈ C.map φ := hCmap ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hcy⟩ := hy
    have hk : c⁻¹ * y ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcy, inv_mul_cancel]
    obtain ⟨k, hk'⟩ := hP2 ⟨c⁻¹ * y, hk⟩
    refine ⟨k, ?_⟩
    have e1 : ((y : X) : X ⧸ C) = ((c⁻¹ * y : X) : X ⧸ C) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c⁻¹).2 (C.inv_mem hc), one_mul]
    rw [e1, ← QuotientGroup.mk_pow]
    have : (c⁻¹ * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk'
    rw [this, QuotientGroup.mk_one]
  have hCtop : C = ⊤ := by
    have : Group.IsPerfect X := Group.isPerfect_def.2 hperf
    have : Group.IsNilpotent (X ⧸ C) := hQ2.isNilpotent
    by_contra hne
    have : Nontrivial (X ⧸ C) := by
      obtain ⟨y, hy⟩ : ∃ y : X, y ∉ C := by
        by_contra h
        push Not at h
        exact hne (eq_top_iff.2 fun y _ => h y)
      exact ⟨⟨(y : X ⧸ C), 1, fun h => hy ((QuotientGroup.eq_one_iff y).1 h)⟩⟩
    exact Group.IsPerfect.not_isNilpotent (X ⧸ C) inferInstance
  intro z hz y
  have hyC : y ∈ C := hCtop ▸ Subgroup.mem_top y
  exact (Subgroup.mem_centralizer_iff.1 hyC z hz)

end Five

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem comm_pCoreOf_eq_bot_of_card_dvd {B : Subgroup Γ} (hBB : ⁅B, B⁆ = B)
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)))
    (hB : Nat.card ↥B ∣ 20160) : ⁅pCoreOf 2 B, B⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := hBiso
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hX : Nat.card ↥B = 360 * Nat.card ↥φ.ker := by
    rw [φ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv, hA6]
  have hP2 : IsPGroup 2 ↥φ.ker := by
    rw [hφk]
    exact CFSG.pCore_isPGroup
  have hP : Nat.card ↥φ.ker ∣ 8 := by
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.1 hP2
    rw [hX, show (20160 : ℕ) = 360 * 56 by norm_num] at hB
    have h56 : 2 ^ i ∣ 56 := by
      rw [← hi]
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hB
    have hi3 : i ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ∣ 56 := (pow_dvd_pow 2 (by omega)).trans h56
      norm_num at this
    rw [hi, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 hi3
  have hperf : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hBB]
  have hc := commute_of_ker_card_dvd_eight hperf φ hφs hP2 hP
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro z hz b hb
  unfold pCoreOf at hz
  obtain ⟨z', hz', rfl⟩ := hz
  rw [← hφk] at hz'
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (hc z' hz' ⟨b, hb⟩)

theorem exists_imgA_eq_stab8 {K B : Subgroup Γ} (e : ↥K ≃* ↥(alternatingGroup (Fin 8)))
    (hBK : B ≤ K) (hBB : ⁅B, B⁆ = B)
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) :
    ∃ p q : Fin 8, p ≠ q ∧ imgA e B = stab8 p q ∧ pCoreOf 2 B = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card ↥K = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hBc := comm_pCoreOf_eq_bot_of_card_dvd hBB hBiso (hK ▸ Subgroup.card_dvd_of_le hBK)
  obtain ⟨φ, hφs, hφk⟩ := hBiso
  have hD := KG12614.dataA6_of φ hφs (by exact hφk)
  obtain ⟨a, ha⟩ := hD.card
  set H := imgA e B with hHdef
  let iB : ↥B ≃* ↥H := (Subgroup.subgroupOfEquivOfLe hBK).symm.trans
    ((B.subgroupOf K).equivMapOfInjective _ (injective_imgA_hom e))
  set ψ : ↥H →* ↥(alternatingGroup (Fin 6)) := φ.comp iB.symm.toMonoidHom with hψ
  have hψs : Function.Surjective ψ := hφs.comp iB.symm.surjective
  have hcent : ∀ z ∈ CFSG.Open.pCore 2 ↥B, ∀ b : ↥B, z * b = b * z := by
    intro z hz b
    have h1 : ⁅(z : Γ), (b : Γ)⁆ ∈ ⁅pCoreOf 2 B, B⁆ :=
      Subgroup.commutator_mem_commutator (by unfold pCoreOf; exact ⟨z, hz, rfl⟩) b.2
    rw [hBc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subtype.ext h1
  have hZ : ∀ z ∈ ψ.ker, ∀ h : ↥H, z * h = h * z := by
    intro z hz h
    have hz' : iB.symm z ∈ CFSG.Open.pCore 2 ↥B := by
      rw [← hφk, MonoidHom.mem_ker]
      exact (MonoidHom.mem_ker).1 hz
    have h2 := congrArg iB (hcent _ hz' (iB.symm h))
    simpa using h2
  have hBperf : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hBB]
  have hperf : ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ = ⊤ := by
    have h1 := congrArg (Subgroup.map iB.toMonoidHom) hBperf
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ iB.surjective] at h1
  have hcH : Nat.card ↥H = 2 ^ a * 360 := by
    rw [← ha]
    exact (Nat.card_congr iB.toEquiv).symm
  have h7 : ¬ 7 ∣ Nat.card ↥H := by
    rw [hcH]
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
        ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)
      norm_num at this
    · norm_num at h
  have hH1 : ∃ h ∈ H, h ≠ 1 := by
    by_contra hc
    push Not at hc
    have : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 hc
    rw [this, Subgroup.card_bot] at hcH
    have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    omega
  obtain ⟨p, q, hpq, hfix, -⟩ := exists_two_fixed_eight
    (orbit_ncard_eq_six ψ hψs (eq_top_of_map_index_le ψ hZ hperf) h7) hH1
  have hle : H ≤ stab8 p q := fun h hh =>
    mem_stab8.2 ⟨imgA_le e B hh, (hfix h hh).1, (hfix h hh).2⟩
  have hc360 : Nat.card ↥H ≤ 360 := card_stab8 hpq ▸ Subgroup.card_le_of_le hle
  have ha0 : a = 0 := by
    rw [hcH] at hc360
    by_contra h
    have : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hHeq : H = stab8 p q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_stab8 hpq, hcH, ha0]; norm_num)
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hφinj : Function.Injective φ :=
    (Function.Surjective.bijective_of_nat_card_le hφs (by rw [ha, ha0, hA6]; norm_num)).1
  have hO2B : pCoreOf 2 B = ⊥ := by
    have h1 : CFSG.Open.pCore 2 ↥B = ⊥ := by
      rw [← hφk]
      exact (MonoidHom.ker_eq_bot_iff φ).2 hφinj
    unfold pCoreOf
    rw [h1, Subgroup.map_bot]
  exact ⟨p, q, hpq, hHeq, hO2B⟩


end CFSG.Quasithin.H13.KG12618
