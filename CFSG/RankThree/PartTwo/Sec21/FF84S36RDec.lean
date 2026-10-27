module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36RAct
public import CFSG.RankThree.PartTwo.Sec21.FF84S36Comm
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4FusionTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

variable {G : Type} [Group G] [Finite G]

theorem R_isPGroup_of_no_odd {K : Subgroup G}
    (h : ∀ x ∈ K, ∀ q : ℕ, q.Prime → q ≠ 2 → orderOf x ≠ q) : IsPGroup 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
  intro q hq hqd
  by_contra hq2
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) q hqd
  exact h x x.2 q hq hq2 (by rw [← hx]; exact Subgroup.orderOf_coe x)

theorem R_cen_le_op2 {b t b₁ b₂ : G} {L B : Subgroup G} (hchar : CFSG.Assembly.IsCharTwoType G)
    (d : F6Data b L B b₁ b₂ t) : Cen t ⊓ CenS (Op 2 (Cen t)) ≤ Op 2 (Cen t) := by
  have hNor : Nor (Subgroup.zpowers t) = Cen t :=
    le_antisymm (S36_nor_zpowers_le d.ht) (S36_cen_le_nor t)
  have hQne : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    have ht1 : t = 1 := Subgroup.zpowers_eq_bot.1 h
    have h' := d.ht
    rw [ht1, orderOf_one] at h'
    norm_num at h'
  have hB := B_charTwo hchar (Subgroup.zpowers t) hQne (S36_isPGroup_zpowers d.ht)
  rw [hNor] at hB
  exact hB

theorem R_zt_le {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t) :
    Subgroup.zpowers t ≤ Op 2 (Cen t) :=
  S36_zpowers_op2 d.ht (S36_mem_cen_of rfl) (fun g hg => (S36_comm_of_cen hg).symm)

theorem R_zt_norm {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t) :
    ((Subgroup.zpowers t).subgroupOf (Op 2 (Cen t))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hgt : (g : G) * t = t * (g : G) :=
    (S36_comm_of_cen (S36_op2_le _ g.2)).symm
  have hc : (g : G) * t ^ k = t ^ k * (g : G) :=
    ((show Commute (g : G) t from hgt).zpow_right k).eq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hk, hc, mul_inv_cancel_right]
  exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩

theorem R_d_facts {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t) :
    b₁ * b₂ ^ 2 ∈ L ∧ b₁ * b₂ ^ 2 ∈ Cen t ∧ orderOf (b₁ * b₂ ^ 2) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1B : b₁ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₁).1
  have hb2B : b₂ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₂).1
  have hb1L : b₁ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₁).2
  have hb2L : b₂ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₂).2
  have hdL : b₁ * b₂ ^ 2 ∈ L := mul_mem hb1L (pow_mem hb2L 2)
  have htc' : ∀ x ∈ L, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 d.htL x hx).symm
  refine ⟨hdL, S36_mem_cen_of (htc' _ hdL), ?_⟩
  have hsq : b₂ ^ 2 = b₂⁻¹ := S36_sq_eq_inv (pow3_of_mem_B d.sec hb2B)
  apply orderOf_eq_prime
  · have hcm : Commute b₁ (b₂ ^ 2) := (comm_of_mem_B d.sec hb1B hb2B).pow_right 2
    have h6 : (b₂ ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow3_of_mem_B d.sec hb2B, one_pow]
    rw [hcm.mul_pow, pow3_of_mem_B d.sec hb1B, h6, one_mul]
  · rw [hsq]
    exact b₁b₂inv_ne_one d.sec

theorem R_fpf {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) (h33 : FF84_3_3) :
    ∀ u ∈ Op 2 (Cen t), (∃ n ∈ Subgroup.zpowers t,
      (b₁ * b₂ ^ 2) * u * (b₁ * b₂ ^ 2)⁻¹ = u * n) → u ∈ Subgroup.zpowers t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hdCt, hd3⟩ := R_d_facts d
  have hCT := (F6_CT_c d h31 h33).2
  rintro u hu ⟨n, hn, hconj⟩
  obtain ⟨q, hq, n', hn', hqu⟩ := B_coprime_quot 2 (Op 2 (Cen t)) (Subgroup.zpowers t)
    (b₁ * b₂ ^ 2) (S36_op2_isPGroup _) (R_zt_le d) (R_zt_norm d) (S36_nor_op2 hdCt)
    (S36_cen_le_nor t hdCt) (by rw [hd3]; norm_num) u hu ⟨n, hn, hconj⟩
  have hq' : q ∈ Subgroup.zpowers t := by
    rw [← hCT]; exact hq
  rw [hqu]
  exact mul_mem hq' hn'

theorem R_decomp {b t b₁ b₂ : G} {L B : Subgroup G} (hchar : CFSG.Assembly.IsCharTwoType G)
    (d : F6Data b L B b₁ b₂ t) (h31 : FF84_3_1) (h33 : FF84_3_3)
    (hT : Nat.card (Op 2 (Cen t)) = 2 ^ 5) :
    Op 2 (Cen t) ⊓ L = ⊥ ∧ ∀ x ∈ Cen t, ∃ u ∈ Op 2 (Cen t), ∃ l ∈ L, x = u * l := by
  classical
  have hZ : Subgroup.center L = ⊥ := (h31 G b L B b₁ b₂ d.sec).2
  have hsimple : IsSimpleGroup ↥L := by
    have hq : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := d.sec.hyp.quasi.2.1
    haveI := hq
    exact (M0_quotIso hZ).symm.isSimpleGroup
  obtain ⟨e, -⟩ := M0_model d.sec hZ
  have hLcard : Nat.card L = 20160 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]
  have htc' : ∀ x ∈ L, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 d.htL x hx).symm
  have hLX : L ≤ Cen t := fun x hx => S36_mem_cen_of (htc' x hx)
  obtain ⟨hcomm, hsq, r, hr⟩ := F6_H d h31 h33
  have hNT : Subgroup.zpowers t ≤ Op 2 (Cen t) := R_zt_le d
  have hNn := R_zt_norm d
  have hXN : Cen t ≤ Nor (Op 2 (Cen t)) := fun x hx => S36_nor_op2 hx
  have hcen : ∀ x ∈ Cen t, ∀ n ∈ Subgroup.zpowers t, x * n = n * x :=
    fun x hx n hn => (S36_z_comm hn hx).symm
  have hr1 : r = 1 := by
    rw [hT] at hr
    have h16 : 16 ^ r = 16 ^ 1 := by omega
    exact Nat.pow_right_injective (by norm_num) h16
  have hVcard : Nat.card (↥(Op 2 (Cen t)) ⧸ (Subgroup.zpowers t).subgroupOf (Op 2 (Cen t))) = 16 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Subgroup.zpowers t).subgroupOf (Op 2 (Cen t)))
    have hN2 : Nat.card ((Subgroup.zpowers t).subgroupOf (Op 2 (Cen t))) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv, Nat.card_zpowers, d.ht]
    rw [hT, hN2] at h
    omega
  have hVcomm : ∀ a b : ↥(Op 2 (Cen t)) ⧸ (Subgroup.zpowers t).subgroupOf (Op 2 (Cen t)),
      a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H u => ?_
    induction b using QuotientGroup.induction_on with | H v => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have := hcomm (v : G)⁻¹ (Subgroup.inv_mem _ v.2) (u : G)⁻¹ (Subgroup.inv_mem _ u.2)
    simpa [mul_assoc] using this
  have hVsq : ∀ a : ↥(Op 2 (Cen t)) ⧸ (Subgroup.zpowers t).subgroupOf (Op 2 (Cen t)),
      a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with | H u => ?_
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have := hsq (u : G) u.2
    simpa [sq] using this
  have hAut := CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.card_mulAut_of_elemAb_sixteen hVcomm hVsq hVcard
  let ρ := actHom (Op 2 (Cen t)) (Subgroup.zpowers t) hNn (Cen t) hXN hcen
  let ι : ↥L →* ↥(Cen t) := Subgroup.inclusion hLX
  let ρL := ρ.comp ι
  have hinj : Function.Injective ρL := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal ρL.ker with h | h
    · exact h
    · exfalso
      obtain ⟨hc'L, -, -⟩ := R_d_facts d
      have hker : ρL ⟨b₁ * b₂ ^ 2, hc'L⟩ = 1 := by
        have : (⟨b₁ * b₂ ^ 2, hc'L⟩ : ↥L) ∈ ρL.ker := by rw [h]; trivial
        exact this
      have h1 := (actHom_eq_one_iff _ _ hNn (Cen t) hXN hcen ⟨_, hLX hc'L⟩).1 hker
      apply F6_r_pos hchar d
      exact le_antisymm (fun u hu => R_fpf d h31 h33 u hu (h1 u hu)) hNT
  have hrangeL : Nat.card ρL.range = 20160 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, hLcard]
  have hrange_le : ρL.range ≤ ρ.range := by
    rintro _ ⟨l, rfl⟩
    exact ⟨ι l, rfl⟩
  have hcard_le : Nat.card ρ.range ≤ 20160 := by
    calc Nat.card ρ.range ≤ Nat.card (MulAut (↥(Op 2 (Cen t)) ⧸
          (Subgroup.zpowers t).subgroupOf (Op 2 (Cen t)))) := Subgroup.card_le_card_group _
      _ = 20160 := hAut
  have hrange_eq : ρL.range = ρ.range :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hrangeL]; exact hcard_le)
  have hK'le : ρ.ker.map (Cen t).subtype ≤ Cen t := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hK'norm : ((ρ.ker.map (Cen t).subtype).subgroupOf (Cen t)).Normal := by
    have : (ρ.ker.map (Cen t).subtype).subgroupOf (Cen t) = ρ.ker :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective ρ.ker
    rw [this]
    infer_instance
  have hK'p : IsPGroup 2 (ρ.ker.map (Cen t).subtype) := by
    apply R_isPGroup_of_no_odd
    rintro _ ⟨y, hy, rfl⟩ q hq hq2 hord
    change orderOf (y : G) = q at hord
    have h1 := (actHom_eq_one_iff _ _ hNn (Cen t) hXN hcen y).1 hy
    have h2 : ∀ n ∈ Subgroup.zpowers t, (y : G) * n * (y : G)⁻¹ = n := by
      intro n hn
      rw [hcen _ y.2 n hn, mul_inv_cancel_right]
    have hyodd : ¬ 2 ∣ orderOf (y : G) := by
      intro h2d
      rw [hord] at h2d
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h2d).symm
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcs := B_stability 2 (Op 2 (Cen t)) (Subgroup.zpowers t) (y : G) (S36_op2_isPGroup _)
      hNT hNn (hXN y.2) hyodd h1 h2
    have hyT : (y : G) ∈ Op 2 (Cen t) := R_cen_le_op2 hchar d (Subgroup.mem_inf.2 ⟨y.2, hcs⟩)
    obtain ⟨k, hk⟩ := S36_op2_isPGroup (Cen t) ⟨(y : G), hyT⟩
    have hk' : (y : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : q ∣ 2 ^ k := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hk'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd))
  have hK'T : ρ.ker.map (Cen t).subtype ≤ Op 2 (Cen t) :=
    S36_op2_of_normal hK'le hK'norm hK'p
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    rintro u hu
    obtain ⟨huT, huL⟩ := Subgroup.mem_inf.1 hu
    have hker : ρL ⟨u, huL⟩ = 1 := by
      have := (actHom_eq_one_iff _ _ hNn (Cen t) hXN hcen ⟨_, hLX huL⟩).2 (by
        intro w hw
        refine ⟨w⁻¹ * (u * w * u⁻¹), ?_, by group⟩
        have := hcomm (w : G)⁻¹ (Subgroup.inv_mem _ hw) u huT
        simpa [mul_assoc] using this)
      exact this
    have : (⟨u, huL⟩ : ↥L) = 1 := hinj (by rw [hker, map_one])
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  · intro x hx
    have hrx : ρ ⟨x, hx⟩ ∈ ρL.range := by
      rw [hrange_eq]
      exact ⟨_, rfl⟩
    obtain ⟨l, hl⟩ := hrx
    refine ⟨x * (l : G)⁻¹, ?_, l, l.2, by group⟩
    have hmem : (ι l)⁻¹ * ⟨x, hx⟩ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : ρ (ι l) = ρ ⟨x, hx⟩ := hl
      rw [this, inv_mul_cancel]
    have h1 : (l : G)⁻¹ * x ∈ Op 2 (Cen t) := hK'T ⟨_, hmem, rfl⟩
    have h2 := S36_op2_conj (H := Cen t) (hLX l.2) h1
    simpa [mul_assoc] using h2

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
