module

public import CFSG.Permutation.UnitaryThreeRecognition.Main

public section

open MulAction Subgroup

namespace CFSG.Permutation.SylowTrivialIntersection

variable {G : Type*} [Group G] {p : ℕ} {P : Sylow p G}

theorem mem_of_smul_eq {Q : Sylow p G} {u : G} (hu : u ∈ (P : Subgroup G)) (h : u • Q = Q) :
    u ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) := by
  have hmem : u ∈ (P : Subgroup G) ⊓ normalizer (Q : Set G) :=
    ⟨hu, Sylow.smul_eq_iff_mem_normalizer.mp h⟩
  rwa [P.2.inf_normalizer_sylow Q] at hmem

theorem eq_one_of_smul_eq (hTI : ∀ Q : Sylow p G, Q ≠ P → (P : Subgroup G) ⊓ Q = ⊥)
    {Q : Sylow p G} (hQ : Q ≠ P) {u : G} (hu : u ∈ (P : Subgroup G)) (h : u • Q = Q) :
    u = 1 := by
  have hmem := mem_of_smul_eq hu h
  rwa [hTI Q hQ, mem_bot] at hmem

theorem smul_self_of_mem {u : G} (hu : u ∈ (P : Subgroup G)) : u • P = P :=
  Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer hu)

theorem smul_ne_of_mem {u : G} (hu : u ∈ (P : Subgroup G)) {Q : Sylow p G} (hQ : Q ≠ P) :
    u • Q ≠ P := by
  intro h
  apply hQ
  rw [← inv_smul_smul u Q, h]
  exact smul_self_of_mem (inv_mem hu)

theorem smul_injective (hTI : ∀ Q : Sylow p G, Q ≠ P → (P : Subgroup G) ⊓ Q = ⊥)
    {Q : Sylow p G} (hQ : Q ≠ P) :
    Function.Injective fun u : (P : Subgroup G) => (u : G) • Q := by
  intro u v huv
  have huv' : (u : G) • Q = (v : G) • Q := huv
  have h : ((v : G)⁻¹ * u) • Q = Q := by
    rw [mul_smul]
    exact inv_smul_eq_iff.mpr huv'
  exact Subtype.ext (inv_mul_eq_one.mp
    (eq_one_of_smul_eq hTI hQ (mul_mem (inv_mem v.2) u.2) h)).symm

variable [Finite G]

theorem existsUnique_smul_eq (hTI : ∀ Q : Sylow p G, Q ≠ P → (P : Subgroup G) ⊓ Q = ⊥)
    (hcard : Nat.card (Sylow p G) = Nat.card P + 1) {β γ : Sylow p G} (hβ : β ≠ P)
    (hγ : γ ≠ P) : ∃! u : (P : Subgroup G), (u : G) • β = γ := by
  let f : ↥(P : Subgroup G) → {Q : Sylow p G // Q ≠ P} := fun u => ⟨(u : G) • β,
    smul_ne_of_mem u.2 hβ⟩
  have hinj : Function.Injective f := fun u v huv =>
    smul_injective hTI hβ (congrArg Subtype.val huv)
  have hcompl : Nat.card {Q : Sylow p G // Q ≠ P} = Nat.card (P : Subgroup G) := by
    have h := SubMulAction.nat_card_ofStabilizer_add_one_eq G P
    have h' : Nat.card (SubMulAction.ofStabilizer G P) = Nat.card {Q : Sylow p G // Q ≠ P} :=
      rfl
    have hP : Nat.card (P : Subgroup G) = Nat.card P := rfl
    omega
  have hbij := (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcompl.symm⟩
  obtain ⟨u, hu⟩ := hbij.2 ⟨γ, hγ⟩
  exact ⟨u, congrArg Subtype.val hu, fun v hv => hinj (Subtype.ext (hv.trans
    (congrArg Subtype.val hu).symm))⟩

theorem trivialIntersection_of_inf_eq_bot (hP : (P : Subgroup G) ≠ ⊥) {Q₁ : Sylow p G}
    (hQ₁ : (P : Subgroup G) ⊓ Q₁ = ⊥) (hcard : Nat.card (Sylow p G) ≤ Nat.card P + 1) :
    (∀ Q : Sylow p G, Q ≠ P → (P : Subgroup G) ⊓ Q = ⊥) ∧
      Nat.card (Sylow p G) = Nat.card P + 1 := by
  have hne : Q₁ ≠ P := by
    rintro rfl
    exact hP (by simpa using hQ₁)
  let f : ↥(P : Subgroup G) → {Q : Sylow p G // Q ≠ P} := fun u => ⟨(u : G) • Q₁,
    smul_ne_of_mem u.2 hne⟩
  have hfinj : Function.Injective f := by
    intro u v huv
    have huv' : (u : G) • Q₁ = (v : G) • Q₁ := congrArg Subtype.val huv
    have h : ((v : G)⁻¹ * u) • Q₁ = Q₁ := by
      rw [mul_smul]
      exact inv_smul_eq_iff.mpr huv'
    have hmem := mem_of_smul_eq (mul_mem (inv_mem v.2) u.2) h
    rw [hQ₁, mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem).symm
  have hcompl : Nat.card {Q : Sylow p G // Q ≠ P} + 1 = Nat.card (Sylow p G) :=
    SubMulAction.nat_card_ofStabilizer_add_one_eq G P
  have hle : Nat.card ↥(P : Subgroup G) ≤ Nat.card {Q : Sylow p G // Q ≠ P} :=
    Nat.card_le_card_of_injective f hfinj
  have hPc : Nat.card ↥(P : Subgroup G) = Nat.card P := rfl
  have heq : Nat.card (Sylow p G) = Nat.card P + 1 := by omega
  refine ⟨fun Q hQ => ?_, heq⟩
  have hbij := (Nat.bijective_iff_injective_and_card f).mpr ⟨hfinj, by omega⟩
  obtain ⟨u, hu⟩ := hbij.2 ⟨Q, hQ⟩
  have hQu : (u : G) • Q₁ = Q := congrArg Subtype.val hu
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwP, hwQ⟩ := mem_inf.mp hw
  rw [← hQu, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hwQ
  have hwP' : (MulAut.conj (u : G))⁻¹ • w ∈ (P : Subgroup G) := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
    exact mul_mem (mul_mem (inv_mem u.2) hwP) u.2
  have h1 : (MulAut.conj (u : G))⁻¹ • w ∈ (P : Subgroup G) ⊓ (Q₁ : Subgroup G) := ⟨hwP', hwQ⟩
  rw [hQ₁, mem_bot] at h1
  have h2 := congrArg (fun x => MulAut.conj (u : G) • x) h1
  simp only [smul_inv_smul, smul_one] at h2
  exact h2

variable [Fact p.Prime]

theorem isMultiplyPretransitive_two (hTI : ∀ Q : Sylow p G, Q ≠ P → (P : Subgroup G) ⊓ Q = ⊥)
    (hcard : Nat.card (Sylow p G) = Nat.card P + 1) :
    IsMultiplyPretransitive G (Sylow p G) 2 := by
  rw [is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq G a P
  obtain ⟨g₂, hg₂⟩ := exists_smul_eq G c P
  have hb : g₁ • b ≠ P := fun h => hab (smul_left_cancel g₁ (hg₁.trans h.symm))
  have hd : g₂ • d ≠ P := fun h => hcd (smul_left_cancel g₂ (hg₂.trans h.symm))
  obtain ⟨u, hu, -⟩ := existsUnique_smul_eq hTI hcard hb hd
  refine ⟨g₂⁻¹ * (u : G) * g₁, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hg₁, smul_self_of_mem u.2, inv_smul_eq_iff, hg₂]
  · rw [mul_smul, mul_smul, hu, inv_smul_smul]

end CFSG.Permutation.SylowTrivialIntersection

namespace CFSG.Permutation.SylowTrivialIntersection

open CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_psu_of_stabilizer_eq
    {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hf : 1 ≤ f) (P : Sylow p G) (hP : Nat.card P = (p ^ f) ^ 3)
    (hTI : ∀ Q : Sylow p G, Q ≠ P → (P : Subgroup G) ⊓ Q = ⊥)
    (hnum : Nat.card (Sylow p G) = (p ^ f) ^ 3 + 1) (K : Subgroup G) (hK : stabilizer G P = K)
    [((P : Subgroup G).subgroupOf K).Normal]
    (hcyc : IsCyclic (K ⧸ (P : Subgroup G).subgroupOf K))
    (hcard : Nat.card (K ⧸ (P : Subgroup G).subgroupOf K) =
      ((p ^ f) ^ 2 - 1) / Nat.gcd (p ^ f + 1) 3) :
    StatedClassicalModel G .PSU 3 p f := by
  have : Fact p.Prime := ⟨hp⟩
  subst hK
  have hcard' : Nat.card (Sylow p G) = Nat.card P + 1 := by rw [hnum, hP]
  have hQ : (P : Subgroup G) ≤ stabilizer G P := fun u hu => smul_self_of_mem hu
  exact UnitaryThreeRecognition.onan_unitary_three hnonab (isMultiplyPretransitive_two hTI hcard')
    p f hp hpodd hf hnum P (P : Subgroup G) hQ hP
    (fun β γ hβ hγ => existsUnique_smul_eq hTI hcard' hβ hγ) hcyc hcard

theorem statedClassicalModel_psu_of_trivialIntersection
    {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hf : 1 ≤ f) (P : Sylow p G) (hP : Nat.card P = (p ^ f) ^ 3)
    (hTI : ∀ Q : Sylow p G, Q ≠ P → (P : Subgroup G) ⊓ Q = ⊥)
    (hnum : Nat.card (Sylow p G) = (p ^ f) ^ 3 + 1)
    (hcyc : IsCyclic (normalizer ((P : Subgroup G) : Set G) ⧸
      (P : Subgroup G).subgroupOf (normalizer ((P : Subgroup G) : Set G))))
    (hcard : Nat.card (normalizer ((P : Subgroup G) : Set G) ⧸
      (P : Subgroup G).subgroupOf (normalizer ((P : Subgroup G) : Set G))) =
      ((p ^ f) ^ 2 - 1) / Nat.gcd (p ^ f + 1) 3) :
    StatedClassicalModel G .PSU 3 p f :=
  statedClassicalModel_psu_of_stabilizer_eq hnonab p f hp hpodd hf P hP hTI hnum
    (normalizer ((P : Subgroup G) : Set G)) (Sylow.stabilizer_eq_normalizer P) hcyc hcard

theorem coprime_of_dvd_sq_sub_one {p f h : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hh : h ∣ (p ^ f) ^ 2 - 1) : h.Coprime ((p ^ f) ^ 3) := by
  have hpq : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
  have hpos : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (pow_ne_zero _
    hp.ne_zero))
  have hndvd : ¬ p ∣ (p ^ f) ^ 2 - 1 := by
    intro hd
    have h1 : p ∣ (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) := Nat.dvd_sub hpq hd
    rw [Nat.sub_sub_self hpos] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hcop : ((p ^ f) ^ 2 - 1).Coprime p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)
  rw [← pow_mul]
  exact (hcop.pow_right (f * 3)).coprime_dvd_left hh

theorem statedClassicalModel_psu_of_sylow_normalizer
    {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hf : 1 ≤ f) (Q : Sylow p G) (hQ : Nat.card Q = (p ^ f) ^ 3) (H : Subgroup G)
    (hHN : H ≤ normalizer ((Q : Subgroup G) : Set G)) (hHcyc : IsCyclic H)
    (hHcard : Nat.card H = ((p ^ f) ^ 2 - 1) / Nat.gcd (p ^ f + 1) 3)
    (hG : Nat.card G = (p ^ f) ^ 3 * ((p ^ f) ^ 3 + 1) * Nat.card H)
    {Q₁ : Sylow p G} (hQ₁ : (Q : Subgroup G) ⊓ Q₁ = ⊥) :
    StatedClassicalModel G .PSU 3 p f := by
  have : Fact p.Prime := ⟨hp⟩
  set K := normalizer ((Q : Subgroup G) : Set G) with hK
  have hHdvd : Nat.card H ∣ (p ^ f) ^ 2 - 1 := by
    rw [hHcard]
    refine Nat.div_dvd_of_dvd ((Nat.gcd_dvd_left _ _).trans ?_)
    refine ⟨p ^ f - 1, ?_⟩
    have h1 : 1 ≤ p ^ f := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
    zify [h1, Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (pow_ne_zero f hp.ne_zero))]
    ring
  have hcop : (Nat.card H).Coprime (Nat.card (Q : Subgroup G)) := by
    have : Nat.card (Q : Subgroup G) = (p ^ f) ^ 3 := hQ
    rw [this]
    exact coprime_of_dvd_sq_sub_one hp hf hHdvd
  have hdisj : H ⊓ (Q : Subgroup G) = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  let φ : H →* K ⧸ (Q : Subgroup G).subgroupOf K :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hHN)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have hmem : (h : G) ∈ H ⊓ (Q : Subgroup G) := by
      refine ⟨h.2, ?_⟩
      have := (QuotientGroup.eq_one_iff _).mp hh
      exact this
    rw [hdisj, mem_bot] at hmem
    exact Subtype.ext hmem
  have hQK : (Q : Subgroup G) ≤ K := le_normalizer
  have hcardQ' : Nat.card ((Q : Subgroup G).subgroupOf K) = (p ^ f) ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv]
    exact hQ
  have hK1 : Nat.card K = Nat.card (K ⧸ (Q : Subgroup G).subgroupOf K) * (p ^ f) ^ 3 := by
    rw [← hcardQ']
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hK2 : Nat.card G = Nat.card (Sylow p G) * Nat.card K := by
    rw [Sylow.card_eq_index_normalizer Q]
    exact (Subgroup.index_mul_card K).symm
  have hle : Nat.card H ≤ Nat.card (K ⧸ (Q : Subgroup G).subgroupOf K) :=
    Nat.card_le_card_of_injective φ hφ
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hq3 : 0 < (p ^ f) ^ 3 := pow_pos (pow_pos hp.pos f) 3
  set m := Nat.card (K ⧸ (Q : Subgroup G).subgroupOf K) with hm
  set n := Nat.card (Sylow p G) with hn
  have heq : n * m = ((p ^ f) ^ 3 + 1) * Nat.card H := by
    have h1 : (p ^ f) ^ 3 * (n * m) = (p ^ f) ^ 3 * (((p ^ f) ^ 3 + 1) * Nat.card H) := by
      calc (p ^ f) ^ 3 * (n * m) = n * (m * (p ^ f) ^ 3) := by ring
        _ = Nat.card G := by rw [hK2, hK1]
        _ = _ := by rw [hG]; ring
    exact Nat.eq_of_mul_eq_mul_left hq3 h1
  have hnle : n ≤ (p ^ f) ^ 3 + 1 := by
    refine Nat.le_of_mul_le_mul_right ?_ hHpos
    calc n * Nat.card H ≤ n * m := Nat.mul_le_mul_left n hle
      _ = _ := heq
  have hQne : (Q : Subgroup G) ≠ ⊥ := by
    intro h
    have h1 : Nat.card (Q : Subgroup G) = 1 := by rw [h]; exact Subgroup.card_bot
    have h2 : Nat.card (Q : Subgroup G) = (p ^ f) ^ 3 := hQ
    have h3 : 1 < (p ^ f) ^ 3 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) hp.one_lt)
    omega
  obtain ⟨hTI, hnum⟩ := trivialIntersection_of_inf_eq_bot hQne hQ₁ (by rw [hQ]; exact hnle)
  rw [hQ] at hnum
  have hmH : m = Nat.card H := by
    have hn' : n = (p ^ f) ^ 3 + 1 := by rw [hn]; exact hnum
    rw [hn'] at heq
    exact Nat.eq_of_mul_eq_mul_left (by omega) heq
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hφ, hmH.symm⟩
  have hcyc : IsCyclic (K ⧸ (Q : Subgroup G).subgroupOf K) :=
    isCyclic_of_surjective φ hbij.2
  exact statedClassicalModel_psu_of_trivialIntersection hnonab p f hp hpodd hf Q hQ hTI hnum
    hcyc (hmH.trans hHcard)

end CFSG.Permutation.SylowTrivialIntersection
