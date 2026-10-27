module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79D2

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

namespace R38K

variable {H : Type} [Group H] [Finite H]

theorem eq_one_of_pow_prime_pow {p : ℕ} {S : Subgroup H} (hS : Nat.Coprime p (Nat.card S))
    {x : H} (hx : x ∈ S) {m : ℕ} (h : x ^ (p ^ m) = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥S) ∣ p ^ m :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h))
  have h2 : orderOf (⟨x, hx⟩ : ↥S) ∣ Nat.card S := orderOf_dvd_natCard _
  have h3 : Nat.Coprime (orderOf (⟨x, hx⟩ : ↥S)) (p ^ m) :=
    Nat.Coprime.pow_right m (Nat.Coprime.coprime_dvd_left h2 hS.symm)
  have h4 : orderOf (⟨x, hx⟩ : ↥S) = 1 := Nat.eq_one_of_dvd_coprimes h3 (dvd_refl _) h1
  have := orderOf_eq_one_iff.1 h4
  simpa using congrArg Subtype.val this

theorem mem_sup_zpowers_of_mem_nor {N : Subgroup H} {x : H} (hx : x ∈ Nor N) {y : H}
    (hy : y ∈ N ⊔ Subgroup.zpowers x) : ∃ n ∈ N, ∃ i : ℤ, y = n * x ^ i := by
  have hxi : ∀ i : ℤ, ∀ n ∈ N, x ^ i * n * (x ^ i)⁻¹ ∈ N := fun i n hn =>
    (Subgroup.mem_normalizer_iff.mp ((Nor N).zpow_mem hx i) n).mp hn
  let T : Subgroup H :=
    { carrier := {y | ∃ n ∈ N, ∃ i : ℤ, y = n * x ^ i}
      one_mem' := ⟨1, N.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, i, rfl⟩ ⟨n', hn', j, rfl⟩
        refine ⟨n * (x ^ i * n' * (x ^ i)⁻¹), N.mul_mem hn (hxi i n' hn'), i + j, ?_⟩
        rw [zpow_add]
        group
      inv_mem' := by
        rintro _ ⟨n, hn, i, rfl⟩
        refine ⟨x ^ (-i) * n⁻¹ * (x ^ (-i))⁻¹, ?_, -i, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp ((Nor N).zpow_mem hx (-i)) n⁻¹).mp (N.inv_mem hn)
        · group }
  have hle : N ⊔ Subgroup.zpowers x ≤ T := by
    refine sup_le ?_ ?_
    · intro n hn
      exact ⟨n, hn, 0, by simp⟩
    · intro z hz
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact ⟨1, N.one_mem, i, by simp⟩
  exact hle hy


theorem odd_Opp_conj {β g : H} (h : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers β))))) :
    Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (g * β * g⁻¹))))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : conjBy g (Opp 3 (Nor (Subgroup.zpowers β))) =
      Opp 3 (Nor (Subgroup.zpowers (g * β * g⁻¹))) := by
    rw [L14.conjBy_Opp, Ctl34.conjBy_Nor_zpowers']
  rw [← hO, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact h


theorem exists_central_complement_p {p : ℕ} [Fact p.Prime] {R Z : Subgroup H} (hZR : Z ≤ R)
    (hZc : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r) (hZp : IsPGroup p Z)
    (hcop : ∀ r ∈ R, ∃ m : ℕ, Nat.Coprime p m ∧ r ^ m ∈ Z) :
    ∃ O : Subgroup H, O ≤ R ∧ Z ⊓ O = ⊥ ∧ (∀ r ∈ R, ∃ z ∈ Z, ∃ x ∈ O, r = z * x) ∧
      Nat.Coprime p (Nat.card O) := by
  classical
  let N : Subgroup ↥R := Z.subgroupOf R
  haveI hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have e : (g : H) * (n : H) * (g : H)⁻¹ = (n : H) := by
      calc (g : H) * (n : H) * (g : H)⁻¹ = ((n : H) * (g : H)) * (g : H)⁻¹ := by
            rw [← hZc (g : H) g.2 (n : H) hn]
        _ = (n : H) := by group
    simpa [e] using hn⟩
  have hNp : IsPGroup p N := hZp.comap_subtype
  have hidx : ¬ p ∣ N.index := by
    intro hp
    have hp' : p ∣ Nat.card (↥R ⧸ N) := hp
    obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' p hp'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x'
    obtain ⟨m, hm3, hmZ⟩ := hcop (x : H) x.2
    have hxm : (QuotientGroup.mk x : ↥R ⧸ N) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show ((x ^ m : ↥R) : H) ∈ Z
      simpa using hmZ
    have hd : orderOf (QuotientGroup.mk x : ↥R ⧸ N) ∣ m := orderOf_dvd_of_pow_eq_one hxm
    rw [hx'] at hd
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hm3 hd
  have hcopN : Nat.Coprime p N.index :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hidx
  obtain ⟨n, hn⟩ := hNp.exists_card_eq
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := N)
    (by rw [hn]; exact Nat.Coprime.pow_left n hcopN)
  refine ⟨K.map R.subtype, Subgroup.map_subtype_le K, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxZ, k, hkK, rfl⟩
    have hkN : k ∈ N := hxZ
    have hk1 : k = 1 := (Subgroup.disjoint_def.mp hK.disjoint) hkN hkK
    rw [hk1]
    exact Subgroup.one_mem _
  · intro r hr
    have hmem : (⟨r, hr⟩ : ↥R) ∈ N ⊔ K := by
      rw [hK.sup_eq_top]
      trivial
    obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    refine ⟨(n : H), hn, (k : H), ⟨k, hk, rfl⟩, ?_⟩
    have := congrArg Subtype.val hnk
    simpa using this.symm
  · have h1 : Nat.card (K.map R.subtype) = Nat.card K :=
      Subgroup.card_map_of_injective R.subtype_injective
    rw [h1, ← hK.symm.index_eq_card]
    exact hcopN

theorem mem_complement_of_coprime_orderOf_p {p : ℕ} [Fact p.Prime] {R Z O : Subgroup H}
    (hZc : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r) (hZp : IsPGroup p Z) (hOR : O ≤ R)
    (hdec : ∀ r ∈ R, ∃ z ∈ Z, ∃ x ∈ O, r = z * x) (hOc : Nat.Coprime p (Nat.card O))
    {x : H} (hxR : x ∈ R) (hx : Nat.Coprime p (orderOf x)) : x ∈ O := by
  classical
  obtain ⟨z, hz, o, ho, rfl⟩ := hdec x hxR
  by_cases hz1 : z = 1
  · rw [hz1, one_mul]
    exact ho
  exfalso
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZp ⟨z, hz⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hz1 (orderOf_eq_one_iff.mp (by simpa using hk))
  have hcomm : Commute z o := (hZc o (hOR ho) z hz).symm
  have ho1 : o ^ Nat.card O = 1 := by
    have h1 : (⟨o, ho⟩ : ↥O) ^ Nat.card O = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hpow : (z * o) ^ Nat.card O = z ^ Nat.card O := by
    rw [hcomm.mul_pow, ho1, mul_one]
  have hord : orderOf (z ^ Nat.card O) = p ^ k := by
    rw [Nat.Coprime.orderOf_pow (by rw [hk]; exact Nat.Coprime.pow_left k hOc), hk]
  have hdvd : orderOf (z ^ Nat.card O) ∣ orderOf (z * o) := by
    rw [← hpow]
    exact orderOf_pow_dvd _
  rw [hord] at hdvd
  have hpd : p ∣ orderOf (z * o) :=
    (dvd_pow_self p hk0).trans hdvd
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hx hpd

theorem conj_mem_complement_p {p : ℕ} [Fact p.Prime] {R Z O : Subgroup H}
    (hZc : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r) (hZp : IsPGroup p Z) (hOR : O ≤ R)
    (hdec : ∀ r ∈ R, ∃ z ∈ Z, ∃ x ∈ O, r = z * x) (hOc : Nat.Coprime p (Nat.card O))
    {g x : H} (hx : x ∈ O) (hgx : g * x * g⁻¹ ∈ R) : g * x * g⁻¹ ∈ O := by
  refine mem_complement_of_coprime_orderOf_p hZc hZp hOR hdec hOc hgx ?_
  rw [orderOf_conj_eq]
  exact hOc.coprime_dvd_right (Subgroup.orderOf_dvd_natCard O hx)

theorem nor_sup_decomp_rel {Γ Z : Subgroup H} {x : H} (hx : orderOf x = 3) (hxΓ : x ∈ Γ)
    (hZΓ : Z ≤ Γ) (hZn : ∀ g ∈ Γ, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (hZc : Nat.Coprime 3 (Nat.card Z)) {g : H} (hgΓ : g ∈ Γ)
    (hg : g ∈ Nor (Subgroup.zpowers x ⊔ Z)) :
    ∃ z ∈ Z, ∃ n ∈ Γ ⊓ Nor (Subgroup.zpowers x), g = z * n := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  set E : Subgroup H := Subgroup.zpowers x ⊔ Z with hE
  have hxE : x ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hxN : x ∈ Nor Z := Subgroup.mem_normalizer_fintype fun z hz => hZn x hxΓ z hz
  have hxZ : Subgroup.zpowers x ⊓ Z = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have hd1 : Nat.card ↥(Subgroup.zpowers x ⊓ Z) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers x ⊓ Z ≤ Subgroup.zpowers x)
      rwa [hcardx] at this
    have hd2 : Nat.card ↥(Subgroup.zpowers x ⊓ Z) ∣ Nat.card Z :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Nat.eq_one_of_dvd_coprimes hZc hd1 hd2
  have hcardE : Nat.card E = 3 * Nat.card Z := by
    have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (Z : Set H) := by
      rw [Subgroup.zpowers_le]
      exact hxN
    have := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hle
    rw [hxZ, hcardx, Subgroup.card_bot] at this
    simpa using this
  have hsyl : IsSylowOf 3 (Subgroup.zpowers x) E := by
    refine L14.isSylowOf_of_card le_sup_left ?_
    rw [hcardx, hcardE]
    have hz0 : Nat.card Z ≠ 0 := Nat.card_pos.ne'
    have : (3 * Nat.card Z).factorization 3 = 1 := by
      rw [Nat.factorization_mul (by norm_num) hz0, Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_three,
        Nat.factorization_eq_zero_of_not_dvd
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hZc)]
    rw [this]
    norm_num
  have hxg : g * x * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hg x).mp hxE
  have hle : Subgroup.zpowers (g * x * g⁻¹) ≤ E := Subgroup.zpowers_le.mpr hxg
  have hp3 : IsPGroup 3 (Subgroup.zpowers (g * x * g⁻¹)) := by
    refine isPGroup_zpowers_of_pow_three ?_
    calc (g * x * g⁻¹) ^ 3 = g * x ^ 3 * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hx3]; group
  obtain ⟨k, hkE, hk⟩ := L14.exists_conj_le_sylowOf hsyl hle hp3
  have hkgx : (k * g) * x * (k * g)⁻¹ ∈ Subgroup.zpowers x := by
    have := hk (g * x * g⁻¹) (Subgroup.mem_zpowers _)
    simpa [mul_assoc] using this
  have hkgN : k * g ∈ Nor (Subgroup.zpowers x) := mem_Nor_zpowers_of_conj hkgx
  have hkinv : k⁻¹ ∈ Z ⊔ Subgroup.zpowers x := by
    rw [sup_comm]
    exact E.inv_mem hkE
  obtain ⟨z, hz, i, hzi⟩ := mem_sup_zpowers_of_mem_nor hxN hkinv
  have hg' : g = z * (x ^ i * (k * g)) := by
    calc g = k⁻¹ * (k * g) := by group
      _ = (z * x ^ i) * (k * g) := by rw [hzi]
      _ = z * (x ^ i * (k * g)) := by group
  refine ⟨z, hz, x ^ i * (k * g), ⟨?_, ?_⟩, hg'⟩
  · have : x ^ i * (k * g) = z⁻¹ * g := by
      have := hg'
      calc x ^ i * (k * g) = z⁻¹ * (z * (x ^ i * (k * g))) := by group
        _ = z⁻¹ * g := by rw [← hg']
    rw [this]
    exact Γ.mul_mem (Γ.inv_mem (hZΓ hz)) hgΓ
  · exact (Nor (Subgroup.zpowers x)).mul_mem (Subgroup.zpow_mem _ (Subgroup.le_normalizer
      (Subgroup.mem_zpowers x)) i) hkgN

theorem weak_rel {b t b₁ b₂ : H} {J : Subgroup H} (h : FS79Hyp b t b₁ b₂ J) {E : Subgroup H}
    (hbE : b ∈ E) {h' : H} (hb' : h' * b * h'⁻¹ ∈ Nor E) : h' * b * h'⁻¹ ∈ E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set b' : H := h' * b * h'⁻¹ with hb'def
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hb'3 : b' ^ 3 = 1 := by
    rw [hb'def, conj_pow, hb3]
    group
  set F : Subgroup H := E ⊔ Subgroup.zpowers b' with hF
  have hFN : F ≤ Nor E := sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hb')
  have hbF : b ∈ F := Subgroup.mem_sup_left hbE
  have hb'F : b' ∈ F := Subgroup.mem_sup_right (Subgroup.mem_zpowers b')
  have hbp : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf F) :=
    (isPGroup_zpowers_of_pow_three hb3).of_equiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hbF)).symm
  obtain ⟨S, hS⟩ := hbp.exists_le_sylow
  set S₀ : Subgroup H := (S : Subgroup ↥F).map F.subtype with hS₀
  have hS₀syl : IsSylowOf 3 S₀ F := by
    have : CFSG.ABGLocalTools.IsSylowOf 3 S₀ F := ⟨S, rfl⟩
    exact abgSylow_to_ff79 this
  have hS₀p : IsPGroup 3 S₀ := hS₀syl.2.1
  have hbS₀ : b ∈ S₀ := ⟨⟨b, hbF⟩, hS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b)), rfl⟩
  have hb'p : IsPGroup 3 (Subgroup.zpowers b') := isPGroup_zpowers_of_pow_three hb'3
  obtain ⟨k, hkF, hk⟩ := L14.exists_conj_le_sylowOf hS₀syl (Subgroup.zpowers_le.mpr hb'F) hb'p
  have hkb' : k * b' * k⁻¹ ∈ S₀ := hk b' (Subgroup.mem_zpowers b')
  have hkb'' : (k * h') * b * (k * h')⁻¹ ∈ S₀ := by simpa [hb'def, mul_assoc] using hkb'
  have hmem := h.conj_mem_zpowers_of_pgroup hS₀p hbS₀ hkb''
  have hkN : k⁻¹ ∈ Nor E := (Nor E).inv_mem (hFN hkF)
  have hE1 : (k * h') * b * (k * h')⁻¹ ∈ E := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hi]
    exact E.zpow_mem hbE i
  have := (Subgroup.mem_normalizer_iff.mp hkN _).mp hE1
  have e : k⁻¹ * ((k * h') * b * (k * h')⁻¹) * k⁻¹⁻¹ = b' := by
    rw [hb'def]
    group
  rw [e] at this
  exact this

end R38K

end CFSG.RankThree.PartTwo.Sec21.FF81
