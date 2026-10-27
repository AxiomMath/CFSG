module

public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Fusion
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79TP

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {H : Type} [Group H] [Finite H]

theorem exists_central_complement {R Z : Subgroup H} (hZR : Z ≤ R)
    (hZc : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r) (hZ3 : Nat.card Z = 3)
    (hcop : ∀ r ∈ R, ∃ m : ℕ, Nat.Coprime 3 m ∧ r ^ m ∈ Z) :
    ∃ O : Subgroup H, O ≤ R ∧ Z ⊓ O = ⊥ ∧ (∀ r ∈ R, ∃ z ∈ Z, ∃ x ∈ O, r = z * x) ∧
      Nat.Coprime 3 (Nat.card O) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥R := Z.subgroupOf R
  haveI hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have e : (g : H) * (n : H) * (g : H)⁻¹ = (n : H) := by
      calc (g : H) * (n : H) * (g : H)⁻¹ = ((n : H) * (g : H)) * (g : H)⁻¹ := by
            rw [← hZc (g : H) g.2 (n : H) hn]
        _ = (n : H) := by group
    simpa [e] using hn⟩
  have hNcard : Nat.card N = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv]
    exact hZ3
  have hidx : ¬ 3 ∣ N.index := by
    intro h3
    have h3' : 3 ∣ Nat.card (↥R ⧸ N) := h3
    obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' 3 h3'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x'
    obtain ⟨m, hm3, hmZ⟩ := hcop (x : H) x.2
    have hxm : (QuotientGroup.mk x : ↥R ⧸ N) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show ((x ^ m : ↥R) : H) ∈ Z
      simpa using hmZ
    have hd : orderOf (QuotientGroup.mk x : ↥R ⧸ N) ∣ m := orderOf_dvd_of_pow_eq_one hxm
    rw [hx'] at hd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hm3 hd
  have hcopN : Nat.Coprime 3 N.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := N)
    (by rw [hNcard]; exact hcopN)
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

theorem orderOf_conj_eq (g x : H) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using h

theorem mem_complement_of_coprime_orderOf {R Z O : Subgroup H}
    (hZc : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r) (hZ3 : Nat.card Z = 3) (hOR : O ≤ R)
    (hdec : ∀ r ∈ R, ∃ z ∈ Z, ∃ x ∈ O, r = z * x) (hOc : Nat.Coprime 3 (Nat.card O))
    {x : H} (hxR : x ∈ R) (hx : Nat.Coprime 3 (orderOf x)) : x ∈ O := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz, o, ho, rfl⟩ := hdec x hxR
  by_cases hz1 : z = 1
  · rw [hz1, one_mul]
    exact ho
  exfalso
  have hz3 : z ^ 3 = 1 := by
    have h1 : (⟨z, hz⟩ : ↥Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    rw [hZ3] at h1
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hcomm : Commute z o := (hZc o (hOR ho) z hz).symm
  have ho1 : o ^ Nat.card O = 1 := by
    have h1 : (⟨o, ho⟩ : ↥O) ^ Nat.card O = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hpow : (z * o) ^ Nat.card O = z ^ Nat.card O := by
    rw [hcomm.mul_pow, ho1, mul_one]
  have hord : orderOf (z ^ Nat.card O) = 3 := by
    rw [Nat.Coprime.orderOf_pow (by rw [hzo]; exact hOc), hzo]
  have hdvd : orderOf (z ^ Nat.card O) ∣ orderOf (z * o) := by
    rw [← hpow]
    exact orderOf_pow_dvd _
  rw [hord] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hx hdvd

theorem conj_mem_complement {R Z O : Subgroup H}
    (hZc : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r) (hZ3 : Nat.card Z = 3) (hOR : O ≤ R)
    (hdec : ∀ r ∈ R, ∃ z ∈ Z, ∃ x ∈ O, r = z * x) (hOc : Nat.Coprime 3 (Nat.card O))
    {g x : H} (hx : x ∈ O) (hgx : g * x * g⁻¹ ∈ R) : g * x * g⁻¹ ∈ O := by
  refine mem_complement_of_coprime_orderOf hZc hZ3 hOR hdec hOc hgx ?_
  rw [orderOf_conj_eq]
  exact hOc.coprime_dvd_right (Subgroup.orderOf_dvd_natCard O hx)

theorem conj_eq_of_coprime_normal {X Q : Subgroup H}
    (hQn : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hcop : Nat.Coprime 3 (Nat.card Q))
    {x q : H} (hx : x ∈ X) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hq : q ∈ Q)
    (hqx : q * x * q⁻¹ ∈ Subgroup.zpowers x) : q * x * q⁻¹ = x := by
  have hne : q * x * q⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    calc x = q⁻¹ * (q * x * q⁻¹) * q := by group
      _ = 1 := by rw [h1]; group
  rcases eq_or_inv_of_mem_zpowers_of_pow_three hx3 hx1 hqx hne with h1 | h2
  · exact h1
  · exfalso
    have hcomm : q * (x * q⁻¹ * x⁻¹) = x := by
      have e : q * (x * q⁻¹ * x⁻¹) = (q * x * q⁻¹) * x⁻¹ := by group
      rw [e, h2]
      have : x⁻¹ * x⁻¹ = x := by
        calc x⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ * (x ^ 3) := by rw [hx3, mul_one]
          _ = x := by group
      exact this
    have hxQ : x ∈ Q := by
      rw [← hcomm]
      refine Q.mul_mem hq ?_
      have := hQn x hx q⁻¹ (Q.inv_mem hq)
      simpa [mul_assoc] using this
    exact hx1 (eq_one_of_mem_coprime_of_pow_three hcop hxQ hx3)

variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.conj_mem_zpowers_of_pgroup (h : FS79Hyp b t b₁ b₂ J) {S₀ : Subgroup H}
    (hS : IsPGroup 3 S₀) (hbS : b ∈ S₀) {g : H} (hg : g * b * g⁻¹ ∈ S₀) :
    g * b * g⁻¹ ∈ Subgroup.zpowers b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTop : IsPGroup 3 (⊤ : Subgroup ↥S₀) := hS.of_equiv Subgroup.topEquiv.symm
  let P : Sylow 3 ↥S₀ := hTop.toSylow (by simp [Subgroup.index_top])
  have hPtop : (P : Subgroup ↥S₀) = ⊤ := rfl
  have hmap : (P : Subgroup ↥S₀).map S₀.subtype = S₀ := by
    rw [hPtop, Subgroup.map_top, Subgroup.range_subtype]
  have hbP : b ∈ (P : Subgroup ↥S₀).map S₀.subtype := by
    rw [hmap]
    exact hbS
  have hle : conjBy g (Subgroup.zpowers b) ≤ (P : Subgroup ↥S₀).map S₀.subtype := by
    rw [hmap]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : (MulAut.conj g).toMonoidHom (b ^ k) = (g * b * g⁻¹) ^ k := by
      simp [MulAut.conj_apply]
    rw [e]
    exact S₀.zpow_mem hg k
  have hD := h.weaklyClosed_sylow (M := S₀) (Subgroup.zpowers_le.mpr hbS) P hbP
    (conjBy g (Subgroup.zpowers b)) ⟨g, rfl⟩ hle
  rw [← hD]
  exact ⟨b, Subgroup.mem_zpowers b, by simp [MulAut.conj_apply]⟩

theorem FS79Hyp.nor_decomp (h : FS79Hyp b t b₁ b₂ J) {n : H}
    (hn : n ∈ Nor (Subgroup.zpowers b)) :
    ∃ k ∈ Opp 3 (Nor (Subgroup.zpowers b)), ∃ y ∈ Subgroup.closure ({b, t} : Set H),
      ∃ j ∈ J, n = k * y * j := by
  obtain ⟨hrM, hk⟩ := h.rho_spec hn
  obtain ⟨y, hy, j, hj, hyj⟩ := (CFSG.mem_sup_of_commute
    (A := Subgroup.closure ({b, t} : Set H)) (B := J)
    (fun a ha c hc => h.Y_comm_J ha hc)).mp hrM
  refine ⟨n * (h.rho n)⁻¹, hk, y, hy, j, hj, ?_⟩
  rw [mul_assoc, hyj]
  group

theorem FS79Hyp.conj_eq_of_decomp (h : FS79Hyp b t b₁ b₂ J) {k y j x : H}
    (hk : k ∈ Opp 3 (Nor (Subgroup.zpowers b))) (hy : y ∈ Subgroup.closure ({b, t} : Set H))
    (hj : j ∈ J) (hx : x ∈ J) : (k * y * j) * x * (k * y * j)⁻¹ = j * x * j⁻¹ := by
  have hw : j * x * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hx) (J.inv_mem hj)
  have hyw : y * (j * x * j⁻¹) = (j * x * j⁻¹) * y := h.Y_comm_J hy hw
  have hkw : k * (j * x * j⁻¹) = (j * x * j⁻¹) * k := h.K_comm_J hk hw
  calc (k * y * j) * x * (k * y * j)⁻¹ = k * (y * (j * x * j⁻¹) * y⁻¹) * k⁻¹ := by group
    _ = k * ((j * x * j⁻¹) * y * y⁻¹) * k⁻¹ := by rw [hyw]
    _ = k * (j * x * j⁻¹) * k⁻¹ := by group
    _ = (j * x * j⁻¹) * k * k⁻¹ := by rw [hkw]
    _ = j * x * j⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec21.FF81
