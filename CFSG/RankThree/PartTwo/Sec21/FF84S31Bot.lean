module

public import CFSG.RankThree.PartTwo.Sec21.FF84S31TJ
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrFrattini

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG
open scoped commutatorElement

section Bot

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem coprime3_elt_C (h : FF84Sec3 b L B b₁ b₂) {a : G} (ha : a ∈ CenS L ⊓ Cen b) {m : ℕ}
    (hm : ¬ 3 ∣ m) (hn : a ^ m = 1) : a ∈ Opp 3 (Cen b) := by
  obtain ⟨i, z, hz, rfl⟩ := mem_C_decomp h ha
  have hcomm : Commute (b ^ i) z :=
    (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (Opp_le 3 _ hz)) i).symm
  rw [hcomm.mul_pow, ← zpow_natCast, ← zpow_mul] at hn
  have h1 : b ^ (i * (m : ℤ)) ∈ Subgroup.zpowers b ⊓ Opp 3 (Cen b) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers_iff.2 ⟨_, rfl⟩, ?_⟩
    have : b ^ (i * (m : ℤ)) = (z ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hn
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hz _)
  rw [(P_C_structure h).2.2, Subgroup.mem_bot] at h1
  have h3 : (3 : ℤ) ∣ i * (m : ℤ) := three_dvd_of_zpow_eq_one h.hyp.ord h1
  have h4 : (3 : ℤ) ∣ i := by
    rcases Int.prime_three.dvd_or_dvd h3 with h5 | h5
    · exact h5
    · exact absurd (by exact_mod_cast h5) hm
  have hbi : b ^ i = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [h.hyp.ord]; exact_mod_cast h4)
  rw [hbi, one_mul]
  exact hz

theorem pow_six_of_Eo {σ : P8} (h₁ : σ * m₁ = m₁ * σ) (h₂ : σ * m₂ = m₂ * σ) : σ ^ 6 = 1 := by
  obtain ⟨i, j, k, -, rfl⟩ := A3_centralizer_Eo σ h₁ h₂
  have c12 : Commute m₁ m₂ := by unfold Commute SemiconjBy; decide +kernel
  have c1t : Commute m₁ τ₀ := by unfold Commute SemiconjBy; decide +kernel
  have c2t : Commute m₂ τ₀ := by unfold Commute SemiconjBy; decide +kernel
  have e1 : m₁ ^ 6 = 1 := by decide +kernel
  have e2 : m₂ ^ 6 = 1 := by decide +kernel
  have e3 : τ₀ ^ 6 = 1 := by decide +kernel
  have hpow : ∀ (x : P8) (n : ℕ), x ^ 6 = 1 → (x ^ n) ^ 6 = 1 := fun x n hx => by
    rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
  have c12' : Commute (m₁ ^ i) (m₂ ^ j) := (c12.pow_left i).pow_right j
  have c3 : Commute (m₁ ^ i * m₂ ^ j) (τ₀ ^ k) :=
    ((c1t.pow_left i).pow_right k).mul_left ((c2t.pow_left j).pow_right k)
  rw [c3.mul_pow, c12'.mul_pow, hpow _ _ e1, hpow _ _ e2, hpow _ _ e3]
  simp

theorem Opp3_Cen_b₁ (hZ : Nat.card (Subgroup.center L) ∣ 2) (h : FF84Sec3 b L B b₁ b₂)
    (hodd : Odd (Nat.card (Opp 3 (Cen b)))) : Opp 3 (Cen b₁) = Opp 3 (Cen b) := by
  obtain ⟨θ, H⟩ := exists_theta h hZ
  have P : PreTheta L θ := H.toPreTheta
  obtain ⟨g, hg, hgb, hgb₁⟩ := exists_swap h
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂N : b₂ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₂).2
  have hconj : Opp 3 (Cen b₁) = conjBy g (Opp 3 (Cen b)) := by
    rw [← hgb, Cen_conjBy, Opp_conjBy]
  rw [hconj]
  have hle : conjBy g (Opp 3 (Cen b)) ≤ Opp 3 (Cen b) := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hxB : g * z * g⁻¹ ∈ CenS B := conj_mem_CenS hg (X_le_CenS_B h hz)
    have hxb : g * z * g⁻¹ ∈ Cen b :=
      Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hxB b (mem_B_b h)).symm
    have hxN : g * z * g⁻¹ ∈ Nor L := h.hyp.hLN hxb
    have hzo : orderOf z ∣ Nat.card (Opp 3 (Cen b)) := Subgroup.orderOf_dvd_natCard _ hz
    have hm2 : ¬ 2 ∣ orderOf z := fun h2 => (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 (h2.trans hzo))
    have hm3 : ¬ 3 ∣ orderOf z := opp3_not_dvd hz
    have hxm : (g * z * g⁻¹) ^ orderOf z = 1 := by
      rw [conj_pow, pow_orderOf_eq_one]; simp
    have hθm : (θ (g * z * g⁻¹)) ^ orderOf z = 1 := by
      rw [← P.pow hxN, hxm, P.one]
    have hc₁ : θ (g * z * g⁻¹) * m₁ = m₁ * θ (g * z * g⁻¹) := by
      have := P.comm hxN hb₁N
        (Subgroup.mem_centralizer_iff.1 hxB b₁ (mem_B_b₁ h)).symm
      rwa [H.hb₁] at this
    have hc₂ : θ (g * z * g⁻¹) * m₂ = m₂ * θ (g * z * g⁻¹) := by
      have := P.comm hxN hb₂N
        (Subgroup.mem_centralizer_iff.1 hxB b₂ (mem_B_b₂ h)).symm
      rwa [H.hb₂] at this
    have h6 := pow_six_of_Eo hc₁ hc₂
    have hcop : Nat.Coprime (orderOf z) 6 := by
      have c2 : Nat.Coprime (orderOf z) 2 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm2).symm
      have c3 : Nat.Coprime (orderOf z) 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3).symm
      exact Nat.Coprime.mul_right c2 c3
    have h1 : θ (g * z * g⁻¹) = 1 := by
      have := pow_gcd_eq_one.2 ⟨hθm, h6⟩
      rwa [hcop, pow_one] at this
    have hcen : g * z * g⁻¹ ∈ CenS L := (P.ker _ hxN).1 h1
    exact coprime3_elt_C h (Subgroup.mem_inf.2 ⟨hcen, hxb⟩) hm3 hxm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem eq_one_of_two_pow_odd {c : G} {k m : ℕ} (hk : c ^ (2 ^ k) = 1) (hm : c ^ m = 1)
    (hodd : Odd m) : c = 1 := by
  have hcop : Nat.Coprime (2 ^ k) m := by
    refine Nat.Coprime.pow_left k ?_
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_
    intro h2
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have := pow_gcd_eq_one.2 ⟨hk, hm⟩
  rwa [hcop, pow_one] at this

theorem mem_Nor_of_conj_closed {N : Subgroup G} {j : G} (h1 : ∀ n ∈ N, j * n * j⁻¹ ∈ N)
    (h2 : ∀ n ∈ N, j⁻¹ * n * j ∈ N) : j ∈ Nor N := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h1 n, fun hn => ?_⟩
  have := h2 _ hn
  simpa [mul_assoc] using this

theorem conj_mem_sup {A B : Subgroup G} {j : G} (hA : ∀ a ∈ A, j * a * j⁻¹ ∈ A)
    (hB : ∀ c ∈ B, j * c * j⁻¹ ∈ B) : ∀ n ∈ A ⊔ B, j * n * j⁻¹ ∈ A ⊔ B := by
  intro n hn
  rw [Subgroup.sup_eq_closure] at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Subgroup.subset_closure (Or.inl (hA x hx))
    · exact Subgroup.subset_closure (Or.inr (hB x hx))
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : j * (x * y) * j⁻¹ = (j * x * j⁻¹) * (j * y * j⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : j * x⁻¹ * j⁻¹ = (j * x * j⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem conj_mem_comm {Q : Subgroup G} {j : G} (hj : j ∈ Nor Q) :
    ∀ n ∈ ⁅Q, Q⁆, j * n * j⁻¹ ∈ ⁅Q, Q⁆ := by
  have hle : ⁅Q, Q⁆ ≤ Subgroup.comap (MulAut.conj j).toMonoidHom ⁅Q, Q⁆ := by
    rw [Subgroup.commutator_le]
    intro q₁ hq₁ q₂ hq₂
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj j).toMonoidHom ⁅q₁, q₂⁆ = ⁅j * q₁ * j⁻¹, j * q₂ * j⁻¹⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 hj q₁).1 hq₁)
      ((Subgroup.mem_normalizer_iff.1 hj q₂).1 hq₂)
  intro n hn
  have := hle hn
  rwa [Subgroup.mem_comap] at this

theorem Z_X_bot (hF : LemmaF) (hA8 : A8TJStmt) (hZ : Nat.card (Subgroup.center L) ∣ 2)
    (h : FF84Sec3 b L B b₁ b₂) (hodd : Odd (Nat.card (Opp 3 (Cen b)))) :
    Opp 3 (Cen b) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, H⟩ := exists_theta h hZ
  have P : PreTheta L θ := H.toPreTheta
  obtain ⟨T, K, hTA, hKA, hTe, hKT, hKs, hKc, hm₁, -⟩ := hA8
  have hZ2 : ∀ z ∈ L, z ∈ CenS L → z ^ 2 = 1 := fun z hz hzC => center_sq hZ hz hzC
  have hX1 : Opp 3 (Cen b₁) = Opp 3 (Cen b) := Opp3_Cen_b₁ hZ h hodd
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₁J : b₁ ∈ preL P K := ⟨hb₁L, by rw [H.hb₁]; exact hm₁⟩
  have hb₁ord := orderOf_b₁ h
  have hT2 : IsPGroup 2 (preL P T) := by
    intro g
    refine ⟨2, ?_⟩
    haveI := hTe.1
    have hg := g.2
    have h1 : (θ (g : G)) ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := T) _ hg.2
    have gN : (g : G) ∈ Nor L := Subgroup.le_normalizer hg.1
    have h2 : θ ((g : G) ^ 2) = 1 := by rw [P.pow gN, h1]
    have h3 : ((g : G) ^ 2) ^ 2 = 1 :=
      hZ2 _ (L.pow_mem hg.1 2)
        ((P.ker _ (Subgroup.le_normalizer (L.pow_mem hg.1 2))).1 h2)
    apply Subtype.ext
    simpa [← pow_mul] using h3
  have hTne : preL P T ≠ ⊥ := by
    intro hbot
    have hT8 : Nat.card T = 8 := by rw [hTe.2]; norm_num
    have : T = ⊥ := by
      rw [eq_bot_iff]
      intro t ht
      obtain ⟨x, hxL, hx⟩ := P.surj t (hTA ht)
      have hxT : x ∈ preL P T := ⟨hxL, by rw [hx]; exact ht⟩
      rw [hbot, Subgroup.mem_bot] at hxT
      rw [← hx, hxT, P.one]
      exact Subgroup.one_mem _
    rw [this, Subgroup.card_bot] at hT8
    omega
  have hJT : preL P K ≤ Nor (preL P T) := by
    have key : ∀ j ∈ preL P K, ∀ t ∈ preL P T, j * t * j⁻¹ ∈ preL P T := by
      intro j hj t ht
      have hjN : j ∈ Nor L := Subgroup.le_normalizer hj.1
      have htN : t ∈ Nor L := Subgroup.le_normalizer ht.1
      refine ⟨L.mul_mem (L.mul_mem hj.1 ht.1) (L.inv_mem hj.1), ?_⟩
      rw [P.conj hjN htN]
      exact (Subgroup.mem_normalizer_iff.1 (hKT hj.2) (θ t)).1 ht.2
    intro j hj
    exact mem_Nor_of_conj_closed (key j hj)
      (fun t ht => by simpa using key j⁻¹ (Subgroup.inv_mem _ hj) t ht)
  have hXN : Opp 3 (Cen b) ≤ Nor (preL P T) := fun x hx =>
    mem_Nor_of_comm (fun w hw =>
      (Subgroup.mem_centralizer_iff.1 ((P_C_structure h).1 hx) w hw.1).symm)
  have hQ2 : IsPGroup 2 (Op 2 (Nor (preL P T))) := Op_isPGroup 2 _
  have hJQ : ∀ j ∈ preL P K, j ∈ Nor (Op 2 (Nor (preL P T))) := fun j hj =>
    mem_Nor_Op 2 (Subgroup.le_normalizer (hJT hj))
  have hcent : ∀ u ∈ Op 2 (Nor (preL P T)) ⊓ Cen b₁, ∀ x ∈ Opp 3 (Cen b), x * u = u * x := by
    intro u hu x hx
    obtain ⟨huQ, huC⟩ := Subgroup.mem_inf.1 hu
    have hxL : x ∈ CenS L := (P_C_structure h).1 hx
    have hxb₁ : x ∈ Cen b₁ :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxL b₁ hb₁L).symm
    have hxu : x * u * x⁻¹ ∈ Op 2 (Nor (preL P T)) ⊓ Cen b₁ := by
      refine Subgroup.mem_inf.2 ⟨Op_conj_mem 2 (Subgroup.le_normalizer (hXN hx)) huQ, ?_⟩
      exact (Cen b₁).mul_mem ((Cen b₁).mul_mem hxb₁ huC) ((Cen b₁).inv_mem hxb₁)
    have hxX : u * x⁻¹ * u⁻¹ ∈ Opp 3 (Cen b) := by
      have hxi : x⁻¹ ∈ Opp 3 (Cen b₁) := by
        rw [hX1]
        exact Subgroup.inv_mem _ hx
      rw [← hX1]
      exact opp3_conj huC hxi
    have hc : x * u * x⁻¹ * u⁻¹ ∈ Opp 3 (Cen b) := by
      have : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hxX
    have hcQ : x * u * x⁻¹ * u⁻¹ ∈ Op 2 (Nor (preL P T)) :=
      Subgroup.mul_mem _ (Subgroup.mem_inf.1 hxu).1 (Subgroup.inv_mem _ huQ)
    obtain ⟨k, hk⟩ := pgroup_elt hQ2 hcQ
    have hcm : (x * u * x⁻¹ * u⁻¹) ^ Nat.card (Opp 3 (Cen b)) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hc)
    have h1 := eq_one_of_two_pow_odd hk hcm hodd
    have h2 : x * u * x⁻¹ = u := mul_inv_eq_one.1 h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = Op 2 (Nor (preL P T)) := ⟨_, rfl⟩
  rw [← hQdef] at hQ2 hJQ hcent
  have hQ₁Q : Q ⊓ CenS (Opp 3 (Cen b)) ≤ Q := inf_le_left
  have hcommQ : ⁅Q, Q⁆ ≤ Q := Subgroup.commutator_le.2 (fun a ha c hc => by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hc) (Q.inv_mem ha)) (Q.inv_mem hc))
  obtain ⟨N, hNdef⟩ : ∃ N, N = Q ⊓ CenS (Opp 3 (Cen b)) ⊔ ⁅Q, Q⁆ := ⟨_, rfl⟩
  have hNQ : N ≤ Q := hNdef ▸ sup_le hQ₁Q hcommQ
  have hNn : (N.subgroupOf Q).Normal := normal_subgroupOf_of_conj hNQ (fun q hq m hm => by
    have hmQ := hNQ hm
    have e : q * m * q⁻¹ = ⁅q, m⁆ * m := by simp only [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem (hNdef ▸ Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq hmQ)) hm)
  have hJN : preL P K ≤ Nor N := by
    intro j hj
    have hjQ := hJQ j hj
    have hQ₁c : ∀ j' ∈ L, j' ∈ Nor Q → ∀ q ∈ Q ⊓ CenS (Opp 3 (Cen b)),
        j' * q * j'⁻¹ ∈ Q ⊓ CenS (Opp 3 (Cen b)) := by
      intro j' hj'L hj'Q q hq
      obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.1 hq
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hj'Q q).1 hqQ, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 (fun x hx => ?_)
      have hxj : Commute x j' :=
        (Subgroup.mem_centralizer_iff.1 ((P_C_structure h).1 hx) j' hj'L).symm
      have hxq : Commute x q := Subgroup.mem_centralizer_iff.1 hqC x hx
      exact ((hxj.mul_right hxq).mul_right hxj.inv_right).eq
    have hjiQ : j⁻¹ ∈ Nor Q := Subgroup.inv_mem _ hjQ
    have f1 := conj_mem_sup (A := Q ⊓ CenS (Opp 3 (Cen b))) (B := ⁅Q, Q⁆)
      (hQ₁c j hj.1 hjQ) (conj_mem_comm hjQ)
    have f2 := conj_mem_sup (A := Q ⊓ CenS (Opp 3 (Cen b))) (B := ⁅Q, Q⁆)
      (hQ₁c j⁻¹ (L.inv_mem hj.1) hjiQ) (conj_mem_comm hjiQ)
    rw [← hNdef] at f1 f2
    exact mem_Nor_of_conj_closed f1 (fun n hn => by simpa using f2 n hn)
  have hfpf : ∀ x ∈ Q, (∃ n ∈ N, b₁ * x * b₁⁻¹ = x * n) → x ∈ N := by
    intro x hx hxn
    obtain ⟨u, hu, n', hn', rfl⟩ := B_coprime_quot 2 Q N b₁ hQ2 hNQ hNn (hJQ b₁ hb₁J)
      (hJN hb₁J) (by rw [hb₁ord]; omega) x hx hxn
    have huQ₁ : u ∈ Q ⊓ CenS (Opp 3 (Cen b)) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hu).1,
        Subgroup.mem_centralizer_iff.2 (fun x hx => hcent u hu x hx)⟩
    exact N.mul_mem (hNdef ▸ Subgroup.mem_sup_left huQ₁) hn'
  have hQN : Q ≤ N :=
    lemmaF_via hF P hZ2 K hKA hKs hKc hb₁J hb₁ord hQ2 hNQ hNn hJQ hJN hfpf
  have hQeq : Q ⊓ CenS (Opp 3 (Cen b)) = Q :=
    CFSG.AGLEmbedding.ParabAutIrr.eq_of_sup_commutator_eq hQ2 hQ₁Q
      (le_antisymm (hNdef ▸ hNQ) (hNdef ▸ hQN))
  have hXC : Opp 3 (Cen b) ≤ CenS Q := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 (fun q hq => ?_)
    have hq' : q ∈ Q ⊓ CenS (Opp 3 (Cen b)) := by rw [hQeq]; exact hq
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hq').2 x hx).symm
  have hXQ : Opp 3 (Cen b) ≤ Q := fun x hx => by
    rw [hQdef]
    exact B_charTwo h.hyp.char2 (preL P T) hTne hT2
      (Subgroup.mem_inf.2 ⟨hXN hx, hQdef ▸ hXC hx⟩)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := pgroup_elt hQ2 (hXQ hx)
  have hm : x ^ Nat.card (Opp 3 (Cen b)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hx)
  rw [Subgroup.mem_bot]
  exact eq_one_of_two_pow_odd hk hm hodd

theorem Z_center (hZ : Nat.card (Subgroup.center L) ∣ 2) (h : FF84Sec3 b L B b₁ b₂)
    (hX : Opp 3 (Cen b) = ⊥) : Subgroup.center L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzC : (z : G) ∈ CenS L := Subgroup.mem_centralizer_iff.2 (fun l hl => by
    have := Subgroup.mem_center_iff.1 hz ⟨l, hl⟩
    exact congrArg Subtype.val this)
  have hzb : (z : G) ∈ Cen b := h.hyp.hLC z.2
  have hz2 : (z : G) ^ 2 = 1 := center_sq hZ z.2 hzC
  have hzX := coprime3_elt_C h (Subgroup.mem_inf.2 ⟨hzC, hzb⟩) (m := 2) (by omega) hz2
  rw [hX, Subgroup.mem_bot] at hzX
  exact Subtype.ext hzX

end Bot

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
