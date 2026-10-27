module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivSylow

public section

namespace CFSG.Quasithin.Fan86.Univ

section Quotient

variable {Q : Type*} [Group Q] [Finite Q]

theorem exists_normal_five_of_card (hQ : Nat.card Q = 10 ∨ Nat.card Q = 20) :
    ∃ N : Subgroup Q, N.Normal ∧ Nat.card N = 5 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 Q) := inferInstance
  obtain ⟨m, hm, hm0, hcard⟩ : ∃ m : ℕ, (m = 2 ∨ m = 4) ∧ m ≠ 0 ∧ Nat.card Q = 5 * m := by
    rcases hQ with h | h
    · exact ⟨2, Or.inl rfl, by norm_num, by rw [h]⟩
    · exact ⟨4, Or.inr rfl, by norm_num, by rw [h]⟩
  have hm5 : ¬ 5 ∣ m := by omega
  have hPcard : Nat.card (P : Subgroup Q) = 5 := by
    rw [P.card_eq_multiplicity, hcard, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_five, Nat.factorization_eq_zero_of_not_dvd hm5]
    simp
  have hidx : (P : Subgroup Q).index = m := by
    have := (P : Subgroup Q).card_mul_index
    rw [hPcard, hcard] at this
    omega
  have hn5 : Nat.card (Sylow 5 Q) = 1 := by
    have h1 := card_sylow_modEq_one 5 Q
    have h3 := P.card_dvd_index
    rw [hidx] at h3
    have hle : Nat.card (Sylow 5 Q) ≤ 4 := (Nat.le_of_dvd (by omega) h3).trans (by omega)
    have hpos : 0 < Nat.card (Sylow 5 Q) := Nat.card_pos
    unfold Nat.ModEq at h1
    omega
  have hsub : Subsingleton (Sylow 5 Q) := by
    have : Nat.card (Sylow 5 Q) ≤ 1 := hn5.le
    exact (Finite.card_le_one_iff_subsingleton).mp (by simpa [Nat.card_eq_fintype_card] using this)
  exact ⟨P, Sylow.normal_of_subsingleton P, hPcard⟩

omit [Finite Q] in
theorem isMulCommutative_of_index_five (hQ : Nat.card Q = 10 ∨ Nat.card Q = 20) {S : Subgroup Q}
    (hSi : S.index = 5) : IsMulCommutative S := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSc : Nat.card S * 5 = Nat.card Q := hSi ▸ S.card_mul_index
  have hS : Nat.card S = 2 ∨ Nat.card S = 2 ^ 2 := by omega
  rcases hS with h | h
  · exact (isCyclic_of_prime_card (p := 2) h).isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq h

theorem two_point_trivial (hO : Open.pCore 2 Q = ⊥) (hQ : Nat.card Q = 10 ∨ Nat.card Q = 20)
    {S : Subgroup Q} (hS : IsPGroup 2 S) (hSi : S.index = 5) {x y g : Q}
    (hxy : x⁻¹ * y ∉ S) (hx : x⁻¹ * g * x ∈ S) (hy : y⁻¹ * g * y ∈ S) : g = 1 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨N, hNn, hN⟩ := exists_normal_five_of_card hQ
  have hSc : Nat.card S * 5 = Nat.card Q := hSi ▸ S.card_mul_index
  have hSab : IsMulCommutative S := isMulCommutative_of_index_five hQ hSi
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hdisj : Disjoint N S :=
    Subgroup.disjoint_of_coprime_natCard (by
      rw [hN, hk]
      exact Nat.Coprime.pow_right k (by norm_num))
  have hcomp : N.IsComplement' S :=
    Subgroup.isComplement'_iff_card_mul_and_disjoint.mpr ⟨by rw [hN]; omega, hdisj⟩
  obtain ⟨⟨⟨n₁, hn₁⟩, ⟨s₁, hs₁⟩⟩, rfl⟩ := hcomp.2 x
  obtain ⟨⟨⟨n₂, hn₂⟩, ⟨s₂, hs₂⟩⟩, rfl⟩ := hcomp.2 y
  simp only at hx hy hxy
  have hs : n₁⁻¹ * g * n₁ ∈ S := by
    have := S.mul_mem (S.mul_mem hs₁ hx) (S.inv_mem hs₁)
    simpa [mul_assoc] using this
  have ht : n₂⁻¹ * g * n₂ ∈ S := by
    have := S.mul_mem (S.mul_mem hs₂ hy) (S.inv_mem hs₂)
    simpa [mul_assoc] using this
  have hmN : n₁⁻¹ * n₂ ∈ N := N.mul_mem (N.inv_mem hn₁) hn₂
  have hmS : n₁⁻¹ * n₂ ∉ S := fun h => hxy (by
    have := S.mul_mem (S.mul_mem (S.inv_mem hs₁) h) hs₂
    simpa [mul_assoc] using this)
  set m : Q := n₁⁻¹ * n₂ with hm
  set s : Q := n₁⁻¹ * g * n₁ with hsdef
  set t : Q := n₂⁻¹ * g * n₂ with htdef
  have hst : s = m * t * m⁻¹ := by simp [hsdef, htdef, hm, mul_assoc]
  have hstN : s * t⁻¹ ∈ N := by
    have h1 : t * m⁻¹ * t⁻¹ ∈ N := hNn.conj_mem _ (N.inv_mem hmN) t
    have : s * t⁻¹ = m * (t * m⁻¹ * t⁻¹) := by rw [hst]; group
    rw [this]
    exact N.mul_mem hmN h1
  have hstS : s * t⁻¹ ∈ S := S.mul_mem hs (S.inv_mem ht)
  have hst1 : s * t⁻¹ = 1 := by
    have := hdisj.le_bot ⟨hstN, hstS⟩
    simpa using this
  have hsteq : s = t := mul_inv_eq_one.1 hst1
  have hmt : m * t = t * m := by
    have : m * t * m⁻¹ = t := by rw [← hst, hsteq]
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hm1 : m ≠ 1 := fun h => hmS (h ▸ S.one_mem)
  have hm5 : m ^ 5 = 1 := by
    have h := pow_card_eq_one' (G := N) (x := (⟨m, hmN⟩ : N))
    rw [hN] at h
    simpa using congrArg Subtype.val h
  have hmord : orderOf m = 5 := orderOf_eq_prime hm5 hm1
  have hzp : Subgroup.zpowers m = N := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hmN) ?_
    rw [Nat.card_zpowers, hmord, hN]
  have htN : ∀ n ∈ N, n * t = t * n := by
    intro n hn
    rw [← hzp] at hn
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    exact ((Commute.zpow_left (show Commute m t from hmt) j).eq)
  have htS : ∀ s' ∈ S, s' * t = t * s' := fun s' hs' =>
    congrArg Subtype.val (hSab.is_comm.comm (⟨s', hs'⟩ : S) (⟨t, ht⟩ : S))
  set Z : Subgroup Q := Subgroup.centralizer ({t} : Set Q) with hZ
  have hNZ : N ≤ Z := fun n hn => Subgroup.mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff.1 hy]
    exact (htN n hn).symm
  have hSZ : S ≤ Z := fun s' hs' => Subgroup.mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff.1 hy]
    exact (htS s' hs').symm
  have h5Z : 5 ∣ Nat.card Z := hN ▸ Subgroup.card_dvd_of_le hNZ
  have hSZd : Nat.card S ∣ Nat.card Z := Subgroup.card_dvd_of_le hSZ
  have hcop : Nat.Coprime 5 (Nat.card S) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hZtop : Z = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    have hd : 5 * Nat.card S ∣ Nat.card Z := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h5Z hSZd
    have hZd : Nat.card Z ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card Z
    refine Nat.dvd_antisymm hZd ?_
    have : Nat.card Q = 5 * Nat.card S := by omega
    rwa [this]
  have hcent : ∀ q : Q, t * q = q * t := fun q => by
    have hq : q ∈ Z := by rw [hZtop]; exact Subgroup.mem_top q
    exact Subgroup.mem_centralizer_iff.1 hq t (Set.mem_singleton t)
  have hzp2 : IsPGroup 2 (Subgroup.zpowers t) := hS.to_le (Subgroup.zpowers_le.2 ht)
  have hzn : (Subgroup.zpowers t).Normal := by
    refine ⟨fun n hn q => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute q (t ^ j) := ((Commute.symm (hcent q) : Commute q t).zpow_right j)
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers t j
  have hle : Subgroup.zpowers t ≤ Open.pCore 2 Q := CFSG.LieType.BorelTits.le_pCore 2 hzn hzp2
  rw [hO] at hle
  have ht1 : t = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers t))
  have hs1 : s = 1 := hsteq.trans ht1
  have : g = n₁ * s * n₁⁻¹ := by simp [hsdef, mul_assoc]
  rw [this, hs1]
  simp

end Quotient

section Lifted

variable {A : Type*} [Group A] [Finite A] {E : Subgroup A}

theorem frob_two_left (hE : IsPGroup 2 E) (hEi : E.index = 5)
    (hQ : Nat.card (oTwoQuot A) = 10 ∨ Nat.card (oTwoQuot A) = 20) {a b h : A}
    (hab : a⁻¹ * b ∉ E) (ha : a⁻¹ * h * a ∈ E) (hb : b⁻¹ * h * b ∈ E) :
    h ∈ Open.pCore 2 A := by
  have hn : (Open.pCore 2 A).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hodd : ¬ 2 ∣ E.index := by rw [hEi]; decide
  have hKE : Open.pCore 2 A ≤ E := pCore_le_of_index_odd hE hodd
  let π : A →* oTwoQuot A := QuotientGroup.mk' (Open.pCore 2 A)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Open.pCore 2 A := QuotientGroup.ker_mk' _
  have hcomap : (E.map π).comap π = E :=
    Subgroup.comap_map_eq_self ((le_of_eq hker).trans hKE)
  have hmem : ∀ z : A, π z ∈ E.map π ↔ z ∈ E := fun z => by
    rw [← Subgroup.mem_comap, hcomap]
  have hSi : (E.map π).index = 5 := by
    rw [← Subgroup.index_comap_of_surjective (E.map π) hπ, hcomap, hEi]
  have hSp : IsPGroup 2 ↥(E.map π) := hE.map π
  have hO : Open.pCore 2 (oTwoQuot A) = ⊥ := Model.pCore_quotient_pCore_eq_bot A
  have key := two_point_trivial hO hQ hSp hSi (x := π a) (y := π b) (g := π h)
    (fun hx => hab (by
      have := (hmem (a⁻¹ * b)).1 (by simpa using hx)
      exact this))
    (by
      have := (hmem (a⁻¹ * h * a)).2 ha
      simpa using this)
    (by
      have := (hmem (b⁻¹ * h * b)).2 hb
      simpa using this)
  rw [← hker]
  exact (MonoidHom.mem_ker).2 key

end Lifted

end CFSG.Quasithin.Fan86.Univ
