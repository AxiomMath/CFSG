module

public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartOne.S12.Sec15Frattini
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.U5K

open CFSG CFSG.RankThree

section Act

variable {G : Type*} [Group G] (I : Subgroup G) {P : Type*} [Group P]

@[expose] noncomputable def U5Act (e : ↥I ⧸ Subgroup.center ↥I ≃* P) :
    ↥(Subgroup.normalizer (I : Set G)) →* MulAut P :=
  (MulAut.congr e).toMonoidHom.comp
    ((mulAutQuotientHom (Subgroup.center ↥I)).comp I.normalizerMonoidHom)

theorem U5Act_apply (e : ↥I ⧸ Subgroup.center ↥I ≃* P)
    (x : ↥(Subgroup.normalizer (I : Set G))) (i : ↥I) :
    U5Act I e x (e (i : ↥I ⧸ Subgroup.center ↥I)) =
      e ((I.normalizerMonoidHom x i : ↥I) : ↥I ⧸ Subgroup.center ↥I) := by
  simp [U5Act, mulAutQuotientHom_mk]

theorem U5Act_of_mem (e : ↥I ⧸ Subgroup.center ↥I ≃* P) (i : ↥I) :
    U5Act I e ⟨(i : G), I.le_normalizer i.2⟩ = MulAut.conj (e (i : ↥I ⧸ Subgroup.center ↥I)) := by
  ext z
  obtain ⟨w, rfl⟩ := e.surjective z
  induction w using QuotientGroup.induction_on with
  | H j =>
    rw [U5Act_apply]
    simp only [MulAut.conj_apply, ← map_mul, ← map_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv]
    rfl

theorem exists_mem_U5Act_eq_conj (e : ↥I ⧸ Subgroup.center ↥I ≃* P) (z : P) :
    ∃ (i : G) (hi : i ∈ I), U5Act I e ⟨i, I.le_normalizer hi⟩ = MulAut.conj z := by
  obtain ⟨w, rfl⟩ := e.surjective z
  obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective w
  exact ⟨i, i.2, U5Act_of_mem I e i⟩

end Act

section Generic

variable {G : Type} [Group G] {Â : Type} [Group Â]

@[expose] def rm (N : Subgroup G) (ρ : ↥N →* Â) (K : Subgroup G) : Subgroup Â :=
  (K.subgroupOf N).map ρ

variable {N : Subgroup G} {ρ : ↥N →* Â}

theorem mem_rm {K : Subgroup G} {a : Â} :
    a ∈ rm N ρ K ↔ ∃ (x : G) (hx : x ∈ N), x ∈ K ∧ ρ ⟨x, hx⟩ = a := by
  unfold rm
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, x.2, hx, rfl⟩
  · rintro ⟨x, hxN, hxK, rfl⟩
    exact ⟨⟨x, hxN⟩, hxK, rfl⟩

theorem rm_mono {K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) : rm N ρ K₁ ≤ rm N ρ K₂ := by
  intro a ha
  obtain ⟨x, hx, hxK, rfl⟩ := mem_rm.1 ha
  exact mem_rm.2 ⟨x, hx, h hxK, rfl⟩

theorem rm_le_range (K : Subgroup G) : rm N ρ K ≤ ρ.range := Subgroup.map_le_range _ _

theorem eq_one_of_pow_prime {q : ℕ} (hq : q.Prime) (hnd : ¬ q ∣ Nat.card ρ.ker) {x : ↥N}
    (hx : ρ x = 1) {k : ℕ} (hk : x ^ q ^ k = 1) : x = 1 := by
  have hker : x ∈ ρ.ker := hx
  set y : ρ.ker := ⟨x, hker⟩ with hy
  have h1 : orderOf y ∣ q ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext hk)
  have h2 : orderOf y ∣ Nat.card ρ.ker := orderOf_dvd_natCard y
  have hcop : Nat.Coprime (q ^ k) (Nat.card ρ.ker) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2 hnd)
  have h3 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)

theorem eq_one_of_isPGroup {q : ℕ} (hq : q.Prime) (hnd : ¬ q ∣ Nat.card ρ.ker) {K : Subgroup G}
    (hK : IsPGroup q K) {x : G} (hxK : x ∈ K) (hxN : x ∈ N) (hx : ρ ⟨x, hxN⟩ = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hK ⟨x, hxK⟩
  have hxk : x ^ q ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hk' : (⟨x, hxN⟩ : ↥N) ^ q ^ k = 1 := Subtype.ext (by simpa using hxk)
  exact congrArg Subtype.val (eq_one_of_pow_prime hq hnd hx hk')

theorem eq_one_of_isPGroup_two (hodd : ¬ 2 ∣ Nat.card ρ.ker) {K : Subgroup G} (hK : IsPGroup 2 K)
    {x : G} (hxK : x ∈ K) (hxN : x ∈ N) (hx : ρ ⟨x, hxN⟩ = 1) : x = 1 :=
  eq_one_of_isPGroup Nat.prime_two hodd hK hxK hxN hx

theorem isSylowOf_rm [Finite G] {T : Subgroup G} (hT : IsSylowOf 2 T N) :
    IsSylowOf 2 (rm N ρ T) ρ.range := by
  obtain ⟨-, hT2, hT3⟩ := hT
  refine ⟨rm_le_range _, (hT2.comap_subtype).map ρ, ?_⟩
  rw [rm, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  intro h
  exact hT3 (h.trans (Subgroup.index_dvd_of_le le_sup_left))

theorem le_of_rm_le {I S : Subgroup G} {Inn : Subgroup Â} (hI : (I.subgroupOf N).Normal)
    (hsurj : ∀ a ∈ Inn, ∃ i : ↥N, (i : G) ∈ I ∧ ρ i = a) (hodd : ¬ 2 ∣ Nat.card ρ.ker)
    (hSN : S ≤ N) (hS : IsPGroup 2 S) (hSInn : rm N ρ S ≤ Inn) : S ≤ I := by
  intro s hs
  have hsN : s ∈ N := hSN hs
  obtain ⟨i, hiI, hi⟩ := hsurj _ (hSInn (mem_rm.2 ⟨s, hsN, hs, rfl⟩))
  have hc : ρ (i⁻¹ * ⟨s, hsN⟩) = 1 := by rw [map_mul, map_inv, hi, inv_mul_cancel]
  have := hI
  let π := QuotientGroup.mk' (I.subgroupOf N)
  have hπi : π i = 1 := (QuotientGroup.eq_one_iff _).2 hiI
  have hπs : π ⟨s, hsN⟩ = π (i⁻¹ * ⟨s, hsN⟩) := by rw [map_mul, map_inv, hπi, inv_one, one_mul]
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hs2 : (⟨s, hsN⟩ : ↥N) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hsk)
  have h1 : (π ⟨s, hsN⟩) ^ 2 ^ k = 1 := by rw [← map_pow, hs2, map_one]
  have h2 : (π (i⁻¹ * ⟨s, hsN⟩)) ^ Nat.card ρ.ker = 1 := by
    rw [← map_pow]
    have : (i⁻¹ * ⟨s, hsN⟩) ^ Nat.card ρ.ker = 1 := by
      have := pow_card_eq_one' (G := ρ.ker) (x := ⟨i⁻¹ * ⟨s, hsN⟩, hc⟩)
      exact congrArg Subtype.val this
    rw [this, map_one]
  rw [← hπs] at h2
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ρ.ker) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have h3 : orderOf (π ⟨s, hsN⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have h4 : (⟨s, hsN⟩ : ↥N) ∈ I.subgroupOf N :=
    (QuotientGroup.eq_one_iff (N := I.subgroupOf N) _).1 (orderOf_eq_one_iff.1 h3)
  exact h4

theorem exists_lift [Finite G] {I S : Subgroup G} {Inn : Subgroup Â}
    (hI : (I.subgroupOf N).Normal) (hIN : I ≤ N)
    (hsurj : ∀ a ∈ Inn, ∃ i : ↥N, (i : G) ∈ I ∧ ρ i = a) (hodd : ¬ 2 ∣ Nat.card ρ.ker)
    (hS : IsPGroup 2 S) (hSI : S ≤ I) {a : Â}
    (ha : a ∈ Inn ⊓ Subgroup.normalizer (rm N ρ S : Set Â)) :
    ∃ (y : G) (hy : y ∈ N), y ∈ I ∧ y ∈ Subgroup.normalizer (S : Set G) ∧ ρ ⟨y, hy⟩ = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN : S ≤ N := hSI.trans hIN
  obtain ⟨g, hgI, hg⟩ := hsurj a ha.1
  have := hI
  set Kt : Subgroup ↥N := I.subgroupOf N ⊓ ρ.ker with hKt
  set Rt : Subgroup ↥N := S.subgroupOf N with hRt
  have hRt2 : IsPGroup 2 Rt := hS.comap_subtype
  have hKodd : ¬ 2 ∣ Nat.card Kt := fun h => hodd (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 Rt (Kt ⊔ Rt) :=
    Sec15Frattini.isSylowOf_sup_of_coprime hRt2 hKodd
  have hconj : ∀ r ∈ Rt, g * r * g⁻¹ ∈ Kt ⊔ Rt := by
    intro r hr
    have hrS : (r : G) ∈ S := hr
    have hgrI : ((g * r * g⁻¹ : ↥N) : G) ∈ I := by
      have h1 : ((g : ↥N) : G) ∈ I := hgI
      have h2 : (r : G) ∈ I := hSI hrS
      have : ((g * r * g⁻¹ : ↥N) : G) = (g : G) * (r : G) * (g : G)⁻¹ := rfl
      rw [this]
      exact I.mul_mem (I.mul_mem h1 h2) (I.inv_mem h1)
    have hmem : ρ (g * r * g⁻¹) ∈ rm N ρ S := by
      rw [map_mul, map_mul, map_inv, hg]
      have := (Subgroup.mem_normalizer_iff.1 ha.2 (ρ r)).1 (mem_rm.2 ⟨r, r.2, hrS, rfl⟩)
      exact this
    obtain ⟨s, hsN, hsS, hs⟩ := mem_rm.1 hmem
    have hst : (⟨s, hsN⟩ : ↥N) ∈ Rt := hsS
    have hk : (⟨s, hsN⟩ : ↥N)⁻¹ * (g * r * g⁻¹) ∈ Kt := by
      refine ⟨?_, ?_⟩
      · show ((⟨s, hsN⟩ : ↥N)⁻¹ * (g * r * g⁻¹) : ↥N).1 ∈ I
        have h1 : s ∈ I := hSI hsS
        have : (((⟨s, hsN⟩ : ↥N)⁻¹ * (g * r * g⁻¹) : ↥N) : G) =
            s⁻¹ * ((g * r * g⁻¹ : ↥N) : G) := rfl
        rw [this]
        exact I.mul_mem (I.inv_mem h1) hgrI
      · show ρ ((⟨s, hsN⟩ : ↥N)⁻¹ * (g * r * g⁻¹)) = 1
        rw [map_mul, map_inv, hs, inv_mul_cancel]
    have : g * r * g⁻¹ = (⟨s, hsN⟩ : ↥N) * ((⟨s, hsN⟩ : ↥N)⁻¹ * (g * r * g⁻¹)) := by group
    rw [this]
    exact (Kt ⊔ Rt).mul_mem (Subgroup.mem_sup_right hst) (Subgroup.mem_sup_left hk)
  obtain ⟨k, hk, hkn⟩ := Sec15Frattini.exists_mem_normalizer_of_normal hsyl hconj
  have hkI : (k : G) ∈ I := hk.1
  refine ⟨((k⁻¹ * g : ↥N) : G), (k⁻¹ * g).2, ?_, ?_, ?_⟩
  · have : ((k⁻¹ * g : ↥N) : G) = (k : G)⁻¹ * (g : G) := rfl
    rw [this]
    exact I.mul_mem (I.inv_mem hkI) hgI
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have hy := Subgroup.mem_normalizer_iff.1 hkn
    constructor
    · intro hx
      have hxN : x ∈ N := hSN hx
      have := (hy ⟨x, hxN⟩).1 hx
      exact this
    · intro hx
      have hxN : x ∈ N := by
        have hyN : ((k⁻¹ * g : ↥N) : G) ∈ N := (k⁻¹ * g).2
        have h1 : ((k⁻¹ * g : ↥N) : G) * x * ((k⁻¹ * g : ↥N) : G)⁻¹ ∈ N := hSN hx
        have h2 := N.mul_mem (N.mul_mem (N.inv_mem hyN) h1) hyN
        simpa [mul_assoc] using h2
      exact (hy ⟨x, hxN⟩).2 hx
  · rw [map_mul, map_inv, hg]
    have : ρ k = 1 := hk.2
    rw [this, inv_one, one_mul]

end Generic

end CFSG.RankThree.PartOne.U5K
