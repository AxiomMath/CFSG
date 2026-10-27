module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.AGLEmbedding

section Complement

variable {T : Type} [Group T] [Finite T] {p : ℕ} [Fact p.Prime]

theorem exists_central_complement (K : Subgroup T) (hKc : K ≤ Subgroup.center T)
    (hp : IsPGroup p K) (hcop : Nat.Coprime K.index p) :
    ∃ R : Subgroup T, R ⊓ K = ⊥ ∧ (∀ t : T, ∃ k ∈ K, ∃ r ∈ R, t = k * r) ∧
      ∀ x : T, x ∈ R ↔ x ^ K.index = 1 := by
  have hKn : K.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hKc hn) g
    rw [this]
    simpa using hn⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hcop' : Nat.Coprime (Nat.card K) K.index := by
    rw [hk]; exact Nat.Coprime.pow_left k hcop.symm
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  have hCcard : Nat.card C = K.index := hC.symm.index_eq_card.symm
  have hdec : ∀ t : T, ∃ k ∈ K, ∃ r ∈ C, t = k * r := by
    intro t
    have : t ∈ K ⊔ C := hC.sup_eq_top ▸ Subgroup.mem_top t
    obtain ⟨v, hv, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 this
    exact ⟨v, hv, d, hd, rfl⟩
  refine ⟨C, ?_, hdec, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [inf_comm]; exact disjoint_iff.1 hC.disjoint
  · have h1 : (⟨x, hx⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [hCcard] at h2
    simpa using h2
  · obtain ⟨κ, hκ, r, hr, rfl⟩ := hdec x
    have hrm : r ^ K.index = 1 := by
      have h1 : (⟨r, hr⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      rw [hCcard] at h2
      simpa using h2
    have hcomm : Commute κ r := (Subgroup.mem_center_iff.1 (hKc hκ) r).symm
    rw [hcomm.mul_pow, hrm, mul_one] at hx
    have hκ1 : κ = 1 := by
      obtain ⟨n, hn⟩ := hp ⟨κ, hκ⟩
      have hn' : κ ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
      have hm : Nat.Coprime K.index (p ^ n) := Nat.Coprime.pow_right n hcop
      have h1 : orderOf κ ∣ K.index := orderOf_dvd_of_pow_eq_one hx
      have h2 : orderOf κ ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn'
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hm h1 h2)
    rw [hκ1, one_mul]
    exact hr

end Complement

section Quotient

variable {E H : Type} [Group E] [Finite E] [Group H] {p : ℕ} [hpp : Fact p.Prime]

theorem exists_normal_complement_preimage (π : E →* H) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker) (Q : Subgroup H) [Q.Normal]
    (hQ : Nat.Coprime (Nat.card Q) p) :
    ∃ R : Subgroup E, R.Normal ∧ R ≤ Q.comap π ∧ R ⊓ π.ker = ⊥ ∧
      ∀ t ∈ Q.comap π, ∃ k ∈ π.ker, ∃ r ∈ R, t = k * r := by
  set T : Subgroup E := Q.comap π with hT
  have hKT : π.ker ≤ T := fun x hx => by
    rw [hT, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]; exact Q.one_mem
  set K' : Subgroup T := π.ker.subgroupOf T with hK'
  let φ : T →* Q := (π.comp T.subtype).codRestrict Q fun t => t.2
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨e, he⟩ := hπ q
    refine ⟨⟨e, by rw [hT, Subgroup.mem_comap, he]; exact q.2⟩, Subtype.ext he⟩
  have hφker : φ.ker = K' := by
    ext t
    rw [MonoidHom.mem_ker, hK', Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hidx : K'.index = Nat.card Q := by
    rw [← hφker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hφsurj, Subgroup.card_top]
  have hK'c : K' ≤ Subgroup.center T := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hC (Subgroup.mem_subgroupOf.1 hx)) (g : E))
  have hK'p : IsPGroup p K' := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hKT).symm
  obtain ⟨R₀, hR₀K, hdec, hchar⟩ :=
    exists_central_complement (p := p) K' hK'c hK'p (by rw [hidx]; exact hQ)
  refine ⟨R₀.map T.subtype, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    obtain ⟨r, hr, rfl⟩ := hn
    have hTn : T.Normal := Subgroup.normal_comap (H := Q) π
    have hmem : g * (r : E) * g⁻¹ ∈ T := hTn.conj_mem _ r.2 g
    refine ⟨⟨g * (r : E) * g⁻¹, hmem⟩, (hchar _).2 ?_, rfl⟩
    have hr1 := (hchar r).1 hr
    refine Subtype.ext ?_
    have := congrArg Subtype.val hr1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [conj_pow, this]
    simp
  · rintro x ⟨r, -, rfl⟩
    exact r.2
  · rw [eq_bot_iff]
    rintro x ⟨⟨r, hr, rfl⟩, hxk⟩
    have : r ∈ R₀ ⊓ K' := ⟨hr, Subgroup.mem_subgroupOf.2 hxk⟩
    rw [hR₀K, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, this]
    rfl
  · intro t ht
    obtain ⟨κ, hκ, r, hr, hrt⟩ := hdec ⟨t, ht⟩
    refine ⟨(κ : E), Subgroup.mem_subgroupOf.1 hκ, (r : E), ⟨r, hr, rfl⟩, ?_⟩
    exact congrArg Subtype.val hrt

theorem kernelTrivialAt_of_quotient (Q : Subgroup H) [Q.Normal]
    (hQ : Nat.Coprime (Nat.card Q) p) (h : KernelTrivialAt (H ⧸ Q) p) : KernelTrivialAt H p := by
  intro E _ _ _ π hπ hC hp
  obtain ⟨R, hRn, hRQ, hRK, hdec⟩ := exists_normal_complement_preimage π hπ hC hp Q hQ
  let π' : E ⧸ R →* H ⧸ Q := QuotientGroup.map R Q π hRQ
  have hπ'm : ∀ e : E, π' (e : E ⧸ R) = ((π e : H) : H ⧸ Q) := fun e => rfl
  have : Group.IsPerfect (E ⧸ R) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)
  have hπ's : Function.Surjective π' := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, rfl⟩ := hπ x
    exact ⟨e, rfl⟩
  have hker : ∀ x : E ⧸ R, π' x = 1 → ∃ κ ∈ π.ker, x = (κ : E ⧸ R) := by
    intro x hx
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hπ'm] at hx
    have heQ : π e ∈ Q := (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨κ, hκ, r, hr, rfl⟩ := hdec e (by rw [Subgroup.mem_comap]; exact heQ)
    refine ⟨κ, hκ, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff r).2 hr, mul_one]
  have hcen : π'.ker ≤ Subgroup.center (E ⧸ R) := by
    intro x hx
    obtain ⟨κ, hκ, rfl⟩ := hker x hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hC hκ) g]
  have hpg : IsPGroup p π'.ker := by
    intro x
    obtain ⟨κ, hκ, hx⟩ := hker x x.2
    obtain ⟨n, hn⟩ := hp ⟨κ, hκ⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hn' : κ ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have : ((x : π'.ker) : E ⧸ R) ^ (p ^ n) = 1 := by
      rw [hx, ← QuotientGroup.mk_pow, hn']; rfl
    simpa using this
  have hbot := h (E ⧸ R) π' hπ's hcen hpg
  rw [eq_bot_iff]
  intro κ hκ
  have hκ1 : (κ : E ⧸ R) = 1 := by
    have : (κ : E ⧸ R) ∈ π'.ker := by
      rw [MonoidHom.mem_ker, hπ'm, MonoidHom.mem_ker.1 hκ]; rfl
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hκR : κ ∈ R := (QuotientGroup.eq_one_iff κ).1 hκ1
  have : κ ∈ R ⊓ π.ker := ⟨hκR, hκ⟩
  rw [hRK] at this
  exact this

end Quotient

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
