module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterOddQ
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.Walter.J1.A5
public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterC0

public section

namespace CFSG.Quasithin.H13.S3320

open CFSG.QuasithinUnique CFSG.GorensteinWalter

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem not_comm_of_perm3 {H : Subgroup Q} (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3))
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : False := by
  have hs := e.surjective.comp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H))
  obtain ⟨x, hx⟩ := hs (Equiv.swap 0 1)
  obtain ⟨y, hy⟩ := hs (Equiv.swap 1 2)
  have h : x * y = y * x := Subtype.ext (hcomm _ x.2 _ y.2)
  have h2 := congrArg (fun z => e (QuotientGroup.mk' (CFSG.pCore 2 ↥H) z)) h
  simp only [map_mul] at h2
  simp only [Function.comp_apply] at hx hy
  rw [hx, hy] at h2
  exact absurd h2 (by decide)

theorem alt4_comm : ∀ a b : alternatingGroup (Fin 4), a ≠ 1 → a ^ 3 = 1 → b ≠ 1 → b ^ 2 = 1 →
    a * b ≠ b * a := by
  decide

theorem dihedral_mem_zpowers_of_orderOf_three {z : ℕ} [NeZero z] {x y : DihedralGroup z}
    (hx : orderOf x = 3) (hy : orderOf y = 3) : y ∈ Subgroup.zpowers x := by
  have hrot : ∀ w : DihedralGroup z, orderOf w = 3 →
      w ∈ Subgroup.zpowers (DihedralGroup.r 1) := by
    intro w hw
    rcases w with a | a
    · refine ⟨(a.val : ℤ), ?_⟩
      show DihedralGroup.r 1 ^ ((a.val : ℕ) : ℤ) = DihedralGroup.r a
      rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    · rw [DihedralGroup.orderOf_sr] at hw
      omega
  let x' : Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z) := ⟨x, hrot x hx⟩
  let y' : Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z) := ⟨y, hrot y hy⟩
  have h : Subgroup.zpowers y' = Subgroup.zpowers x' := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hx, hy]
  have hy' : y' ∈ Subgroup.zpowers x' := h ▸ Subgroup.mem_zpowers y'
  obtain ⟨k, hk⟩ := hy'
  exact ⟨k, congrArg Subtype.val hk⟩

omit [Finite Q] in
theorem map_conj_eq_of_mem_normalizer {S : Subgroup Q} {q : Q}
    (hq : q ∈ Subgroup.normalizer (S : Set Q)) : S.map (MulAut.conj q).toMonoidHom = S := by
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hq s).mp hs
  · intro s hs
    refine ⟨q⁻¹ * s * q, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (S : Set Q)).inv_mem hq) s).mp hs
    simpa using this

theorem join_eq_top_of_L2prime {Y : Subgroup Q} [Y.Normal]
    (hC : Subgroup.centralizer (Y : Set Q) = ⊥) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hp5 : 5 ≤ p) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (eY : ↥Y ≃* PSL2 (GaloisField p 1))
    {S H : Subgroup Q} (hS : IsSylowTwoOf S ⊤) (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hSH : S ≤ H) (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) {q : Q}
    (hq : q ∈ Subgroup.normalizer (S : Set Q)) (hHq : H.map (MulAut.conj q).toMonoidHom ≠ H) :
    H ⊔ H.map (MulAut.conj q).toMonoidHom = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY := eq_top_of_L2prime hC hp2 hp5 eY hS hab
  set K := GaloisField p 1 with hKdef
  have hKcard : Nat.card K = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp.out, hp.out.odd_of_ne_two hp2, le_refl 1, hKcard⟩
  let E : Q ≃* PSL2 K := ((MulEquiv.subgroupCongr hY).trans Subgroup.topEquiv).symm.trans eY
  obtain ⟨W, hWS, hW2, hWc, hHW, hSW, h₀, hh₀H, hh₀, -⟩ := o2_facts hS hab hSH e
  have hS4 : 4 ≤ Nat.card S := by
    have h1 := card_inf_normal (Y := ⊤) hS
    rw [inf_top_eq, Subgroup.card_top, Nat.card_congr E.toEquiv, psl2_card_formula K hK,
      hKcard, pow_one] at h1
    have hpo : Odd p := hp.out.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := Nat.eight_dvd_sq_sub_one_of_odd hpo
    have hval : p * (p ^ 2 - 1) / 2 = 2 ^ 2 * (p * k) := by
      rw [hk, show p * (8 * k) = 2 * (2 ^ 2 * (p * k)) by ring, Nat.mul_div_cancel_left _ two_pos]
    have h4 : 2 ^ 2 ∣ p * (p ^ 2 - 1) / 2 := ⟨p * k, hval⟩
    have hk0 : 0 < k := by
      have h25 : 25 ≤ p ^ 2 := by nlinarith
      omega
    have hne : p * (p ^ 2 - 1) / 2 ≠ 0 := by
      rw [hval]
      exact (Nat.mul_pos (by norm_num) (Nat.mul_pos (by omega) hk0)).ne'
    have h5 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp h4
    rw [h1]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h5
  obtain ⟨w, hwW, hw1, hw2⟩ : ∃ w ∈ W, w ≠ 1 ∧ w ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    have hk1 : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      rw [this, pow_zero] at hk
      omega
    obtain ⟨w', hw'⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 2 (by
      rw [hk]
      exact dvd_pow_self 2 (by omega))
    refine ⟨(w' : Q), w'.2, ?_, ?_⟩
    · intro h
      have : w' = 1 := Subtype.ext h
      rw [this, orderOf_one] at hw'
      omega
    · have h2 : w' ^ 2 = 1 := by rw [← hw']; exact pow_orderOf_eq_one w'
      simpa using congrArg Subtype.val h2
  have hS2 : IsPGroup 2 S := hS.2.1
  obtain ⟨b, hb⟩ := hS2.exists_card_eq
  have hHeq : Subgroup.zpowers h₀ ⊔ S = H := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hh₀H) hSH)
    have h3 : 3 ∣ Nat.card ↥(Subgroup.zpowers h₀ ⊔ S) := by
      rw [← hh₀, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card S ∣ Nat.card ↥(Subgroup.zpowers h₀ ⊔ S) :=
      Subgroup.card_dvd_of_le le_sup_right
    have hcop : Nat.Coprime 3 (Nat.card S) := by
      rw [hb]
      exact Nat.Coprime.pow_right b (by norm_num)
    have h6 := hcop.mul_dvd_of_dvd_of_dvd h3 h2
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers h₀ ⊔ S) := Nat.card_pos
    have := Nat.le_of_dvd hpos h6
    rw [hHW]
    omega
  set c := MulAut.conj q with hc
  have hSq : S.map c.toMonoidHom = S := map_conj_eq_of_mem_normalizer hq
  have hHqeq : H.map c.toMonoidHom = Subgroup.zpowers (c h₀) ⊔ S := by
    rw [← hHeq, Subgroup.map_sup, MonoidHom.map_zpowers, hSq]
    rfl
  by_contra hM
  set M := H ⊔ H.map c.toMonoidHom with hMdef
  have hHM : H ≤ M := le_sup_left
  have hHqM : H.map c.toMonoidHom ≤ M := le_sup_right
  have hh₀M : h₀ ∈ M := hHM hh₀H
  have hch₀M : c h₀ ∈ M := hHqM ⟨h₀, hh₀H, rfl⟩
  have hwM : w ∈ M := hHM (hSH (hWS hwW))
  set M' := M.map E.toMonoidHom with hM'
  have hmem : ∀ x ∈ M, E x ∈ M' := fun x hx => ⟨x, hx, rfl⟩
  have habel : (∀ a ∈ M', ∀ b ∈ M', a * b = b * a) → False := by
    intro hcomm
    apply not_comm_of_perm3 e
    intro a ha b hb
    apply E.injective
    rw [map_mul, map_mul]
    exact hcomm _ (hmem a (hHM ha)) _ (hmem b (hHM hb))
  have hcomm₀ : h₀ * w = w * h₀ := hWc w hwW h₀ hh₀H
  have hh₀3 : h₀ ^ 3 = 1 := by rw [← hh₀]; exact pow_orderOf_eq_one h₀
  have hh₀1 : h₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hh₀
    omega
  rcases Glauberman.Dickson.dickson_psl2_subgroup_list hKcard M' with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨eD⟩⟩ | ⟨-, ⟨eA⟩⟩ | ⟨h16, -⟩ |
      ⟨-, ⟨eA⟩⟩ | ⟨m, t, -, -, -, -, E', C', hE', hE'el, -, hC'cyc, -, -, hsup, -, -⟩ |
      ⟨m, hm, ⟨eL⟩⟩ | ⟨m, hm, -⟩
  ·
    apply habel
    intro a ha b hb
    have := hel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  ·
    apply habel
    intro a ha b hb
    have := (IsCyclic.commGroup (α := ↥M')).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  ·
    have : NeZero z := ⟨by omega⟩
    have hx : orderOf (eD ⟨E h₀, hmem _ hh₀M⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hh₀]
    have hy : orderOf (eD ⟨E (c h₀), hmem _ hch₀M⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq,
        hh₀]
    obtain ⟨k, hk⟩ := dihedral_mem_zpowers_of_orderOf_three hx hy
    have hk' : h₀ ^ k = c h₀ := by
      apply E.injective
      have := congrArg (fun u => ((eD.symm u : ↥M') : PSL2 K)) hk
      simpa [map_zpow] using this
    have hle : Subgroup.zpowers (c h₀) ≤ Subgroup.zpowers h₀ := by
      rw [Subgroup.zpowers_le, ← hk']
      exact Subgroup.zpow_mem_zpowers h₀ k
    have heq : Subgroup.zpowers (c h₀) = Subgroup.zpowers h₀ := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, Nat.card_zpowers, MulEquiv.orderOf_eq]
    apply hHq
    rw [hHqeq, heq, hHeq]
  ·
    apply alt4_comm (eA ⟨E h₀, hmem _ hh₀M⟩) (eA ⟨E w, hmem _ hwM⟩)
    · rw [Ne, MulEquiv.map_eq_one_iff]
      intro h
      exact hh₀1 (E.injective ((congrArg Subtype.val h).trans (map_one E).symm))
    · rw [← map_pow]
      have : (⟨E h₀, hmem _ hh₀M⟩ : ↥M') ^ 3 = 1 := Subtype.ext (by simp [← map_pow, hh₀3])
      rw [this, map_one]
    · rw [Ne, MulEquiv.map_eq_one_iff]
      intro h
      exact hw1 (E.injective ((congrArg Subtype.val h).trans (map_one E).symm))
    · rw [← map_pow]
      have : (⟨E w, hmem _ hwM⟩ : ↥M') ^ 2 = 1 := Subtype.ext (by simp [← map_pow, hw2])
      rw [this, map_one]
    · rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp [← map_mul, hcomm₀])
  ·
    have h1 : (p ^ 1) ^ 2 % 16 = 1 % 16 := h16
    rw [pow_one, Nat.pow_mod] at h1
    have h2 : p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 11 ∨ p % 16 = 13 := by omega
    rcases h2 with h2 | h2 | h2 | h2 <;> rw [h2] at h1 <;> norm_num at h1
  ·
    have h := CFSG.Walter.J1.A5.centralizer_three (eA ⟨E h₀, hmem _ hh₀M⟩)
      (eA ⟨E w, hmem _ hwM⟩) ⟨?_, ?_, ?_⟩
    · have hw' : ∀ u : CFSG.Walter.J1.A5.A, u = eA ⟨E w, hmem _ hwM⟩ → u ≠ 1 ∧ u ^ 2 = 1 := by
        rintro u rfl
        refine ⟨?_, ?_⟩
        · rw [Ne, MulEquiv.map_eq_one_iff]
          intro h
          exact hw1 (E.injective ((congrArg Subtype.val h).trans (map_one E).symm))
        · rw [← map_pow]
          have : (⟨E w, hmem _ hwM⟩ : ↥M') ^ 2 = 1 := Subtype.ext (by simp [← map_pow, hw2])
          rw [this, map_one]
      have hx3 : (eA ⟨E h₀, hmem _ hh₀M⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨E h₀, hmem _ hh₀M⟩ : ↥M') ^ 3 = 1 := Subtype.ext (by simp [← map_pow, hh₀3])
        rw [this, map_one]
      obtain ⟨hu1, hu2⟩ := hw' _ rfl
      set u := eA ⟨E w, hmem _ hwM⟩ with hu
      have hcontra : u ^ 3 = 1 → False := fun h3 => hu1 (by
        calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
          _ = 1 := by rw [h3, hu2]; group)
      rcases h with h | h | h
      · exact hu1 h
      · exact hcontra (h ▸ hx3)
      · apply hcontra
        rw [h, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
    · rw [← map_pow]
      have : (⟨E h₀, hmem _ hh₀M⟩ : ↥M') ^ 3 = 1 := Subtype.ext (by simp [← map_pow, hh₀3])
      rw [this, map_one]
    · rw [Ne, MulEquiv.map_eq_one_iff]
      intro h
      exact hh₀1 (E.injective ((congrArg Subtype.val h).trans (map_one E).symm))
    · rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp [← map_mul, hcomm₀])
  ·
    apply not_comm_of_perm3 e
    intro a ha b hb
    have hquot : IsCyclic (↥M' ⧸ E') := by
      apply isCyclic_of_surjective ((QuotientGroup.mk' E').comp C'.subtype)
      intro u
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective E' u
      have hx : x ∈ E' ⊔ C' := hsup ▸ Subgroup.mem_top x
      rw [← SetLike.mem_coe, Subgroup.normal_mul] at hx
      obtain ⟨e₁, he₁, c₁, hc₁, rfl⟩ := hx
      refine ⟨⟨c₁, hc₁⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      have := hE'.conj_mem e₁ he₁ c₁⁻¹
      simpa [mul_assoc] using this
    set a' : ↥M' := ⟨E a, hmem a (hHM ha)⟩
    set b' : ↥M' := ⟨E b, hmem b (hHM hb)⟩
    have hk : a' * b' * a'⁻¹ * b'⁻¹ ∈ E' := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
        (IsCyclic.commGroup (α := ↥M' ⧸ E')).mul_comm (QuotientGroup.mk a')]
      group
    have hkp : (a * b * a⁻¹ * b⁻¹) ^ p = 1 := by
      have h2 : (a' * b' * a'⁻¹ * b'⁻¹) ^ p = 1 := by
        have := hE'el
        exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E') _ hk
      apply E.injective
      have := congrArg Subtype.val h2
      simpa [a', b'] using this
    have hkH : orderOf (a * b * a⁻¹ * b⁻¹) ∣ Nat.card H := by
      have := Subgroup.orderOf_dvd_natCard H
        (H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb))
      exact this
    have hcop : Nat.Coprime p (Nat.card H) := by
      rw [hHW]
      obtain ⟨j, hj⟩ := hW2.exists_card_eq
      rw [hj]
      have hc2 : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
      have hc3 : Nat.Coprime p 3 := (Nat.coprime_primes hp.out Nat.prime_three).mpr (by omega)
      have hc6 : Nat.Coprime p 6 := by
        have := Nat.Coprime.mul_right hc2 hc3
        simpa using this
      exact Nat.Coprime.mul_right hc6 (Nat.Coprime.pow_right j hc2)
    have hord : orderOf (a * b * a⁻¹ * b⁻¹) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hkp) hkH
    rw [orderOf_eq_one_iff] at hord
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hord, one_mul]
  ·
    apply hM
    have hm1 : m = 1 := Nat.dvd_one.mp hm
    subst hm1
    have hcard : Nat.card M' = Nat.card (PSL2 K) := Nat.card_congr eL.toEquiv
    have hM'top : M' = ⊤ := Subgroup.card_eq_iff_eq_top M' |>.mp hcard
    rw [eq_top_iff]
    intro x _
    have hx : E x ∈ M' := hM'top ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← E.injective hyx]
    exact hy
  ·
    have := Nat.le_of_dvd one_pos hm
    have hm0 : m = 0 := by omega
    rw [hm0] at hm
    simp at hm

end CFSG.Quasithin.H13.S3320
