module

public import CFSG.RankThree.PartOne.SEITZ12.Setup
public import CFSG.RankThree.PartOne.SEITZ12.Classes

public section

namespace CFSG.RankThree.PartOne.SEITZ12

section Generic

variable {G : Type*} [Group G]

theorem phi4t_exists_conj_of_le_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G}
    (hx : x ^ p = 1) : ∃ c : G, c⁻¹ * x * c ∈ (P : Subgroup G) := by
  have hord : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  have hyp : IsPGroup p (Subgroup.zpowers x) := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P Q
  have h1 : ((c • P : Sylow p G) : Subgroup G) = (Q : Subgroup G) := by rw [hc]
  rw [Sylow.coe_subgroup_smul] at h1
  have hxQ : x ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers x)
  rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  refine ⟨c, ?_⟩
  have h3 : (MulAut.conj c)⁻¹ • x = c⁻¹ * x * c := by
    simp [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply]
  rw [← h3]
  exact hxQ

theorem phi4t_conj_into_of_index_coprime [Finite G] {A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hidx : ¬ p ∣ A.index) {x : G} (hx : x ^ p = 1) : ∃ c : G, c⁻¹ * x * c ∈ A := by
  obtain ⟨P₀⟩ : Nonempty (Sylow p ↥A) := inferInstance
  have hcard : Nat.card ((P₀ : Subgroup ↥A).map A.subtype) =
      p ^ (Nat.card G).factorization p := by
    have h1 : Nat.card ((P₀ : Subgroup ↥A).map A.subtype) = Nat.card (P₀ : Subgroup ↥A) :=
      Subgroup.card_map_of_injective A.subtype_injective
    have h4 : Nat.card (P₀ : Subgroup ↥A) = p ^ (Nat.card ↥A).factorization p :=
      P₀.card_eq_multiplicity
    rw [h1, h4]
    have h2 := Subgroup.card_mul_index A
    have hN0 : Nat.card ↥A ≠ 0 := Nat.card_pos.ne'
    have hi0 : A.index ≠ 0 := Nat.card_pos.ne'
    have h3 := congrArg (fun n => n.factorization p) h2
    simp only [Nat.factorization_mul hN0 hi0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero] at h3
    rw [h3]
  obtain ⟨SG, hSG⟩ : ∃ SG : Sylow p G, (SG : Subgroup G) = (P₀ : Subgroup ↥A).map A.subtype :=
    ⟨Sylow.ofCard _ hcard, Sylow.coe_ofCard _ hcard⟩
  obtain ⟨c, hc⟩ := phi4t_exists_conj_of_le_sylow SG hx
  rw [hSG] at hc
  exact ⟨c, Subgroup.map_subtype_le _ hc⟩

theorem phi4t_conj_pow (g e : G) (n : ℕ) : (g⁻¹ * e * g) ^ n = g⁻¹ * e ^ n * g := by
  have h := conj_pow (a := g⁻¹) (b := e) (i := n)
  rwa [inv_inv] at h

theorem phi4t_square_root [Finite G] {Gam C R Rp D : Subgroup G} {z t e g s : G} {p : ℕ}
    [Fact p.Prime] (hCG : C ≤ Gam) (hCz : ∀ c ∈ C, c * z = z * c)
    (hCG' : ∀ x ∈ Gam, x * z = z * x → x ∈ C) (hidx : ¬ p ∣ (R.subgroupOf C).index)
    (hRpG : Rp ≤ Gam) (hRRp : ∀ r ∈ R, ∀ w ∈ Rp, r * w = w * r) (hg : g ∈ Gam)
    (hgt : g * z * g⁻¹ = t) (he : e ∈ Gam) (hep : e ^ p = 1) (het : t * e = e * t)
    (hD : ∀ y ∈ Gam, y * e = e * y → y ∈ D) (hs : s ∈ Rp) (hsz : s * s = z) :
    ∃ y ∈ D, y * y = t := by
  have hx1 : g⁻¹ * e * g ∈ C := by
    refine hCG' _ (mul_mem (mul_mem (inv_mem hg) he) hg) ?_
    have h : e * (g * z * g⁻¹) = (g * z * g⁻¹) * e := by rw [hgt]; exact het.symm
    calc g⁻¹ * e * g * z = g⁻¹ * (e * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * e) * g := by rw [h]
      _ = z * (g⁻¹ * e * g) := by group
  obtain ⟨x, hx⟩ : ∃ x : ↥C, (x : G) = g⁻¹ * e * g := ⟨⟨_, hx1⟩, rfl⟩
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hx, phi4t_conj_pow, hep]
    simp
  obtain ⟨c, hc⟩ := phi4t_conj_into_of_index_coprime hidx hxp
  have hc' : (c : G)⁻¹ * (g⁻¹ * e * g) * c ∈ R := by
    have h0 := Subgroup.mem_subgroupOf.mp hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hx] at h0
    exact h0
  obtain ⟨n, hnC, hnR⟩ : ∃ n : G, n ∈ C ∧ n⁻¹ * (g⁻¹ * e * g) * n ∈ R := ⟨c, c.2, hc'⟩
  have hu : g * n ∈ Gam := mul_mem hg (hCG hnC)
  have hu_t : g * n * z * (g * n)⁻¹ = t := by
    have h : n * z = z * n := hCz n hnC
    calc g * n * z * (g * n)⁻¹ = g * (n * z) * n⁻¹ * g⁻¹ := by group
      _ = g * (z * n) * n⁻¹ * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ := by group
      _ = t := hgt
  have hu_e : g * n * (n⁻¹ * (g⁻¹ * e * g) * n) * (g * n)⁻¹ = e := by group
  refine ⟨g * n * s * (g * n)⁻¹, ?_, ?_⟩
  · refine hD _ (mul_mem (mul_mem hu (hRpG hs)) (inv_mem hu)) ?_
    have h : n⁻¹ * (g⁻¹ * e * g) * n * s = s * (n⁻¹ * (g⁻¹ * e * g) * n) :=
      hRRp _ hnR s hs
    calc g * n * s * (g * n)⁻¹ * e
        = g * n * s * (g * n)⁻¹ * (g * n * (n⁻¹ * (g⁻¹ * e * g) * n) * (g * n)⁻¹) := by
          rw [hu_e]
      _ = g * n * (s * (n⁻¹ * (g⁻¹ * e * g) * n)) * (g * n)⁻¹ := by group
      _ = g * n * (n⁻¹ * (g⁻¹ * e * g) * n * s) * (g * n)⁻¹ := by rw [h]
      _ = (g * n * (n⁻¹ * (g⁻¹ * e * g) * n) * (g * n)⁻¹) * (g * n * s * (g * n)⁻¹) := by
          group
      _ = e * (g * n * s * (g * n)⁻¹) := by rw [hu_e]
  · calc g * n * s * (g * n)⁻¹ * (g * n * s * (g * n)⁻¹)
        = g * n * (s * s) * (g * n)⁻¹ := by group
      _ = g * n * z * (g * n)⁻¹ := by rw [hsz]
      _ = t := hu_t

end Generic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover
  CFSG.RankThree.PartOne.SEITZ7

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem phi4t_t_comm_e {a₀ : ModGL F4.tag K}
    (hcomm : a₀ * (szNw K * a₀ * (szNw K)⁻¹) = (szNw K * a₀ * (szNw K)⁻¹) * a₀) :
    szNw K * (a₀ * (szNw K * a₀ * (szNw K)⁻¹)) = (a₀ * (szNw K * a₀ * (szNw K)⁻¹)) * szNw K := by
  have ht2 : szNw K * szNw K = 1 := szNw_mul_self
  have hti : (szNw K)⁻¹ = szNw K := inv_eq_of_mul_eq_one_right ht2
  rw [hti] at hcomm ⊢
  calc szNw K * (a₀ * (szNw K * a₀ * szNw K))
      = szNw K * (szNw K * a₀ * szNw K * a₀) := by rw [hcomm]
    _ = (szNw K * szNw K) * a₀ * szNw K * a₀ := by group
    _ = a₀ * szNw K * a₀ := by rw [ht2, one_mul]
    _ = a₀ * szNw K * a₀ * (szNw K * szNw K) := by rw [ht2, mul_one]
    _ = a₀ * (szNw K * a₀ * szNw K) * szNw K := by group

theorem phi4t_e_ne_one (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {a₀ : ModGL F4.tag K}
    (ha₀ : a₀ ∈ rankOneGroupTwo K m) (ha₀1 : a₀ ≠ 1) :
    a₀ * (szNw K * a₀ * (szNw K)⁻¹) ≠ 1 := by
  intro h
  apply ha₀1
  have ha : a₀ = (szNw K * a₀ * (szNw K)⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hb : (szNw K * a₀ * (szNw K)⁻¹)⁻¹ ∈ szSubB K m := inv_mem (phi4_b₀_mem_szSubB ha₀)
  have hmem : a₀ ∈ rankOneGroupTwo K m ⊓ szSubB K m :=
    Subgroup.mem_inf.mpr ⟨ha₀, by rwa [← ha] at hb⟩
  rw [rankOneGroupTwo_inf_szSubB hm hK] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem phi4_t_mem_D (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {a₀ : ModGL F4.tag K}
    (ha₀ : a₀ ∈ rankOneGroupTwo K m) (ha₀1 : a₀ ≠ 1) : szNw K ∈ phi4D m K a₀ := by
  have hcomm : a₀ * (szNw K * a₀ * (szNw K)⁻¹) = (szNw K * a₀ * (szNw K)⁻¹) * a₀ :=
    commute_rankOneGroupTwo_szSubB a₀ ha₀ _ (phi4_b₀_mem_szSubB ha₀)
  exact phi4_mem_D szNw_mem_reeGamma (mul_mem phi4_a₀_mem_plane phi4_b₀_mem_plane)
    (phi4t_e_ne_one hm hK ha₀ ha₀1) (phi4t_t_comm_e hcomm)

theorem phi4t_not_dvd_index (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ ((rankOneGroupTwo K m).subgroupOf (centralizerZ K m)).index := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRC : rankOneGroupTwo K m ≤ centralizerZ K m := le_sup_right
  have h1 := Subgroup.card_mul_index ((rankOneGroupTwo K m).subgroupOf (centralizerZ K m))
  have h2 : Nat.card ((rankOneGroupTwo K m).subgroupOf (centralizerZ K m)) =
      Nat.card (rankOneGroupTwo K m) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
  rw [h2, card_centralizerZ hm hK] at h1
  have hpos : 0 < Nat.card (rankOneGroupTwo K m) := Nat.card_pos
  have h3 : ((rankOneGroupTwo K m).subgroupOf (centralizerZ K m)).index =
      Nat.card (F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h1]
    exact mul_comm _ _
  have hV : IsPGroup 2 (F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) :=
    (isPGroup_reeFixedPosUnipotent hm hK).to_le (reeFixedOrbitComplementUnipotent_le _)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV
  rw [h3, hn]
  intro hpd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpd))

theorem phi4_t_square (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a₀ : ModGL F4.tag K} (ha₀ : a₀ ∈ rankOneGroupTwo K m) (hord : orderOf a₀ = p) :
    ∃ y ∈ phi4D m K a₀, y * y = szNw K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hcomm : a₀ * (szNw K * a₀ * (szNw K)⁻¹) = (szNw K * a₀ * (szNw K)⁻¹) * a₀ :=
    commute_rankOneGroupTwo_szSubB a₀ ha₀ _ (phi4_b₀_mem_szSubB ha₀)
  have hap : a₀ ^ p = 1 := by
    have h := pow_orderOf_eq_one a₀
    rwa [hord] at h
  have hbp : (szNw K * a₀ * (szNw K)⁻¹) ^ p = 1 := by
    rw [conj_pow, hap, mul_one, mul_inv_cancel]
  have hep : (a₀ * (szNw K * a₀ * (szNw K)⁻¹)) ^ p = 1 := by
    have hc : Commute a₀ (szNw K * a₀ * (szNw K)⁻¹) := hcomm
    rw [hc.mul_pow, hap, hbp, one_mul]
  have he : a₀ * (szNw K * a₀ * (szNw K)⁻¹) ∈ F4.reeGamma K m :=
    mul_mem (rankOneGroupTwo_le_reeGamma hK ha₀) (phi4_szSubB_le hK (phi4_b₀_mem_szSubB ha₀))
  obtain ⟨g, hg, hgt⟩ := inTwoA_szNw hm hK
  obtain ⟨b, hb⟩ := phi4s_exists_sigma_mul_eq (m := m) hK (1 : K)
  have hs₂ : sylowB m K b 0 ∈ rankOneGroupTwo K m :=
    U₂_le_rankOneGroupTwo (sylowB_mem_U2 hK b 0)
  have hss : (szNw K * sylowB m K b 0 * (szNw K)⁻¹) * (szNw K * sylowB m K b 0 * (szNw K)⁻¹) =
      centralZ K m 1 := by
    have h1 := phi4s_sylowB_sq (m := m) (K := K) hK b 0
    rw [hb] at h1
    calc (szNw K * sylowB m K b 0 * (szNw K)⁻¹) * (szNw K * sylowB m K b 0 * (szNw K)⁻¹)
        = szNw K * (sylowB m K b 0 * sylowB m K b 0) * (szNw K)⁻¹ := by group
      _ = szNw K * sylowB m K 0 1 * (szNw K)⁻¹ := by rw [h1]
      _ = centralZ K m 1 := szNw_conj_sylowB_zero 1
  exact phi4t_square_root (Gam := F4.reeGamma K m) (C := centralizerZ K m)
    (R := rankOneGroupTwo K m) (Rp := szSubB K m) (D := phi4D m K a₀) (z := centralZ K m 1)
    (t := szNw K) (e := a₀ * (szNw K * a₀ * (szNw K)⁻¹)) (g := g)
    (s := szNw K * sylowB m K b 0 * (szNw K)⁻¹) (p := p)
    (centralizerZ_le_reeGamma hK)
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.1
      (centralizerZ_le_centralizer hm hK 1 hc))
    (fun x hx hxz => (reeGamma_inf_centralizer_eq hm hK).le
      (Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hxz⟩))
    (phi4t_not_dvd_index hm hK hp hp2) (phi4_szSubB_le hK) commute_rankOneGroupTwo_szSubB hg hgt
    he hep (phi4t_t_comm_e hcomm)
    (fun y hy hye => phi4_mem_D hy (mul_mem phi4_a₀_mem_plane phi4_b₀_mem_plane)
      (phi4t_e_ne_one hm hK ha₀ ha₀1) hye)
    (phi4_b₀_mem_szSubB hs₂) hss

end CFSG.RankThree.PartOne.SEITZ12
