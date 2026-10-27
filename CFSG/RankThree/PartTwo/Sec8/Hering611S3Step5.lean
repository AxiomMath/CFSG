module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {G : Type*} [Group G] [Finite G]

private theorem fmul_pow_pow {a c : G} (hac : Commute a c) (n k n' k' : ℕ) :
    (a ^ n * c ^ k) * (a ^ n' * c ^ k') = a ^ (n + n') * c ^ (k + k') := by
  rw [pow_add, pow_add, (hac.symm.pow_pow k n').mul_mul_mul_comm]

private def fsub {a c : G} (hac : a * c = c * a) (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1) :
    Subgroup G where
  carrier := {f | ∃ n k : ℕ, f = a ^ n * c ^ k}
  mul_mem' := by
    rintro _ _ ⟨n, k, rfl⟩ ⟨n', k', rfl⟩
    exact ⟨n + n', k + k', fmul_pow_pow hac n k n' k'⟩
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨n, k, rfl⟩
    refine ⟨2 * n, 2 * k, inv_eq_of_mul_eq_one_right ?_⟩
    rw [fmul_pow_pow hac, show n + 2 * n = 3 * n by ring, show k + 2 * k = 3 * k by ring,
      pow_mul, pow_mul, ha3, hc3, one_pow, one_pow, one_mul]

private theorem commute_fsub {a c : G} (hac : a * c = c * a) (ha3 : a ^ 3 = 1)
    (hc3 : c ^ 3 = 1) {x y : G} (hx : x ∈ fsub hac ha3 hc3) (hy : y ∈ fsub hac ha3 hc3) :
    Commute x y := by
  have hcomm : Commute a c := hac
  obtain ⟨n, k, rfl⟩ := hx
  obtain ⟨n', k', rfl⟩ := hy
  exact ((Commute.pow_pow (Commute.refl a) n n').mul_right (hcomm.pow_pow n k')).mul_left
    ((hcomm.symm.pow_pow k n').mul_right (Commute.pow_pow (Commute.refl c) k k'))

private abbrev fsubCommGroup {a c : G} (hac : a * c = c * a) (ha3 : a ^ 3 = 1)
    (hc3 : c ^ 3 = 1) : CommGroup (fsub hac ha3 hc3) :=
  { (inferInstance : Group (fsub hac ha3 hc3)) with
    mul_comm := fun x y => Subtype.ext (commute_fsub hac ha3 hc3 x.2 y.2).eq }

private theorem pow_three_fsub {a c : G} (hac : a * c = c * a) (ha3 : a ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (x : fsub hac ha3 hc3) : x ^ 3 = 1 := by
  have hcomm : Commute a c := hac
  obtain ⟨n, k, hx⟩ := x.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, hx, (hcomm.pow_pow n k).mul_pow, ← pow_mul,
    ← pow_mul, mul_comm n 3, mul_comm k 3, pow_mul, pow_mul, ha3, hc3, one_pow, one_pow,
    one_mul]

private theorem isPGroup_fsub {a c : G} (hac : a * c = c * a) (ha3 : a ^ 3 = 1)
    (hc3 : c ^ 3 = 1) : IsPGroup 3 (fsub hac ha3 hc3) :=
  fun x => ⟨1, by simpa using pow_three_fsub hac ha3 hc3 x⟩

private theorem not_isCyclic_fsub {a c : G} (hac : a * c = c * a) (ha3 : a ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hnc : a ∉ Subgroup.zpowers c) :
    ¬ IsCyclic (fsub hac ha3 hc3) := by
  intro hcyc
  have hcF : c ∈ fsub hac ha3 hc3 := ⟨0, 1, by simp⟩
  have haF : a ∈ fsub hac ha3 hc3 := ⟨1, 0, by simp⟩
  have hle : Nat.card (fsub hac ha3 hc3) ≤ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num)
      (Monoid.exponent_dvd_of_forall_pow_eq_one fun x => pow_three_fsub hac ha3 hc3 x)
  obtain ⟨c', hc'⟩ : ∃ c' : fsub hac ha3 hc3, (c' : G) = c := ⟨⟨c, hcF⟩, rfl⟩
  have hc'3 : c' ^ 3 = 1 := pow_three_fsub hac ha3 hc3 c'
  have hc'1 : c' ≠ 1 := fun h => hc1 (by rw [← hc', h, Subgroup.coe_one])
  have hord : orderOf c' = 3 := orderOf_eq_prime hc'3 hc'1
  have hdvd : 3 ∣ Nat.card (fsub hac ha3 hc3) := by
    rw [← hord]
    exact orderOf_dvd_natCard c'
  have hpos : 0 < Nat.card (fsub hac ha3 hc3) := Nat.card_pos
  have hcard : Nat.card (fsub hac ha3 hc3) = 3 := by
    obtain ⟨t, ht⟩ := hdvd
    omega
  have htop : Subgroup.zpowers c' = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hord, hcard]
  have hamem : (⟨a, haF⟩ : fsub hac ha3 hc3) ∈ Subgroup.zpowers c' := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hamem
  have hk' : c ^ k = a := by
    have h := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow, hc'] at h
    exact h
  exact hnc (Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩)

theorem centralizes_quotient_of_four {U V : Subgroup G} (hU2 : IsPGroup 2 U) (hVU : V ≤ U)
    (hVn : ∀ u ∈ U, ∀ v ∈ V, u * v * u⁻¹ ∈ V) {a c : G} (hac : a * c = c * a) (ha3 : a ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hnc : a ∉ Subgroup.zpowers c)
    (haU : a ∈ Subgroup.normalizer (U : Set G)) (haV : a ∈ Subgroup.normalizer (V : Set G))
    (hcU : c ∈ Subgroup.normalizer (U : Set G)) (hcV : c ∈ Subgroup.normalizer (V : Set G))
    (hfix : ∀ m : ℕ, m < 3 → ∀ u ∈ U, (c * a ^ m) * u * (c * a ^ m)⁻¹ = u → u ∈ V) :
    ∀ u ∈ U, a * u * a⁻¹ * u⁻¹ ∈ V := by
  have hcomm : Commute a c := hac
  have ha1 : a ≠ 1 := fun h => hnc (by rw [h]; exact Subgroup.one_mem _)
  have haF : a ∈ fsub hac ha3 hc3 := ⟨1, 0, by simp⟩
  have hyF : ∀ m : ℕ, a ^ m * c ∈ fsub hac ha3 hc3 := fun m => ⟨m, 1, by simp⟩
  letI : CommGroup (fsub hac ha3 hc3) := fsubCommGroup hac ha3 hc3
  haveI : Fact (IsPGroup 3 (fsub hac ha3 hc3)) := ⟨isPGroup_fsub hac ha3 hc3⟩
  haveI hN : (V.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff hVU).mpr fun h k hh hk => hVn k hk h hh
  have hFU : fsub hac ha3 hc3 ≤ Subgroup.normalizer (U : Set G) := by
    intro f hf
    obtain ⟨n, k, rfl⟩ := hf
    exact mul_mem (pow_mem haU n) (pow_mem hcU k)
  have hFV : fsub hac ha3 hc3 ≤ Subgroup.normalizer (V : Set G) := by
    intro f hf
    obtain ⟨n, k, rfl⟩ := hf
    exact mul_mem (pow_mem haV n) (pow_mem hcV k)
  obtain ⟨θ, hθ⟩ : ∃ θ : fsub hac ha3 hc3 →* MulAut U,
      ∀ (f : fsub hac ha3 hc3) (u : U), ((θ f u : U) : G) = (f : G) * (u : G) * (f : G)⁻¹ :=
    ⟨(Subgroup.normalizerMonoidHom U).comp (Subgroup.inclusion hFU), fun f u => by
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]⟩
  letI : MulDistribMulAction (fsub hac ha3 hc3) U := MulDistribMulAction.compHom U θ
  have hsmul : ∀ (f : fsub hac ha3 hc3) (u : U), f • u = θ f u := fun _ _ => rfl
  have hθV : ∀ (f : fsub hac ha3 hc3) (r : U), r ∈ V.subgroupOf U →
      θ f r ∈ V.subgroupOf U := by
    intro f r hr
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    rw [hθ]
    exact (Subgroup.mem_normalizer_iff.mp (hFV f.2) (r : G)).mp hr
  have hinv : CFSG.IsInvariant (fsub hac ha3 hc3) U (V.subgroupOf U) := by
    refine ⟨fun f r => ⟨fun hr => hθV f r hr, fun hr => ?_⟩⟩
    have h := hθV f⁻¹ (f • r) hr
    rwa [← hsmul, inv_smul_smul] at h
  letI : MulDistribMulAction (fsub hac ha3 hc3) (U ⧸ V.subgroupOf U) :=
    CFSG.quotientMulDistribMulAction (V.subgroupOf U) hinv
  have hsmulq : ∀ (f : fsub hac ha3 hc3) (u : U),
      f • ((u : U) : U ⧸ V.subgroupOf U) = ((f • u : U) : U ⧸ V.subgroupOf U) :=
    fun _ _ => rfl
  have hG : Nat.Coprime 3 (Nat.card (U ⧸ V.subgroupOf U)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU2
    have hdvd : Nat.card (U ⧸ V.subgroupOf U) ∣ Nat.card U :=
      Subgroup.card_quotient_dvd_card _
    rw [hn] at hdvd
    exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow_right n (by norm_num))
  have hp : ¬ 3 ∣ Nat.card (V.subgroupOf U) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU2
    have hdvd : Nat.card (V.subgroupOf U) ∣ Nat.card U := Subgroup.card_subgroup_dvd_card _
    rw [hn] at hdvd
    intro h
    have h3 : 3 ∣ 2 ^ n := h.trans hdvd
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h2
  have hncyc := not_isCyclic_fsub hac ha3 hc3 hc1 hnc
  have hsup := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := U ⧸ V.subgroupOf U) (A := fsub hac ha3 hc3) 3 hG hncyc
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hmoda : ∀ t : ℕ, a ^ t = a ^ (t % 3) := fun t => by
    rw [← pow_mod_orderOf a t, hoa]
  have hmodc : ∀ t : ℕ, c ^ t = c ^ (t % 3) := fun t => by
    rw [← pow_mod_orderOf c t, hoc]
  have hcomm_pow : ∀ n k e : ℕ, (a ^ n * c ^ k) ^ e = a ^ (n * e) * c ^ (k * e) := by
    intro n k e
    rw [(hcomm.pow_pow n k).mul_pow, ← pow_mul, ← pow_mul]
  have hpow_key : ∀ n k e : ℕ, (a ^ n * c ^ k) ^ e = a ^ (n * e % 3) * c ^ (k * e % 3) := by
    intro n k e
    rw [hcomm_pow, hmoda (n * e), hmodc (k * e)]
  have hfix1 : ∀ m : ℕ, m < 3 → ∀ y : fsub hac ha3 hc3, (y : G) = a ^ m * c →
      ∀ x : U ⧸ V.subgroupOf U, y • x = x → x = 1 := by
    intro m hm y hy x
    induction x using QuotientGroup.induction_on with
    | H u =>
    intro hx
    have hstab : Subgroup.zpowers y ≤
        MulAction.stabilizer (fsub hac ha3 hc3) ((u : U) : U ⧸ V.subgroupOf U) :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hx)
    have hcoset : ∀ b : Subgroup.zpowers y, (b.1 • u) * u⁻¹ ∈ V.subgroupOf U := by
      intro b
      have hb : b.1 • ((u : U) : U ⧸ V.subgroupOf U) = ((u : U) : U ⧸ V.subgroupOf U) :=
        MulAction.mem_stabilizer_iff.mp (hstab b.2)
      rw [hsmulq] at hb
      have h1 : (b.1 • u)⁻¹ * u ∈ V.subgroupOf U := QuotientGroup.eq.mp hb
      have h2 : (b.1 • u) * u⁻¹ = (b.1 • u) * ((b.1 • u)⁻¹ * u)⁻¹ * (b.1 • u)⁻¹ := by
        group
      rw [h2]
      exact hN.conj_mem _ ((V.subgroupOf U).inv_mem h1) _
    have hBp : IsPGroup 3 (Subgroup.zpowers y) :=
      (isPGroup_fsub hac ha3 hc3).to_subgroup _
    obtain ⟨u', hu'1, hu'2⟩ :=
      CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset.exists_fixed hBp
        (θ.comp (Subgroup.zpowers y).subtype) (V.subgroupOf U) hN
        (fun b r hr => hθV b.1 r hr) hp u hcoset
    have hu'G : (u' : G) ∈ V := by
      have h3 : θ y u' = u' := hu'2 ⟨y, Subgroup.mem_zpowers y⟩
      have h4 : ((θ y u' : U) : G) = (u' : G) := congrArg Subtype.val h3
      rw [hθ, hy] at h4
      have hcm : c * a ^ m = a ^ m * c := (hcomm.symm.pow_right m).eq
      apply hfix m hm (u' : G) u'.2
      rw [hcm]
      exact h4
    have hu'R : u' ∈ V.subgroupOf U := Subgroup.mem_subgroupOf.mpr hu'G
    apply (QuotientGroup.eq_one_iff u).mpr
    have h6 : u⁻¹ ∈ V.subgroupOf U := by
      have h7 := (V.subgroupOf U).mul_mem ((V.subgroupOf U).inv_mem hu'R) hu'1
      simpa using h7
    simpa using (V.subgroupOf U).inv_mem h6
  have hK : ∀ f : fsub hac ha3 hc3, f ≠ 1 → ∀ x : U ⧸ V.subgroupOf U, f • x = x →
      (⟨a, haF⟩ : fsub hac ha3 hc3) • x = x := by
    intro f hf1 x hfx
    have hpow : ∀ e : ℕ, (f ^ e) • x = x := by
      intro e
      induction e with
      | zero => rw [pow_zero, one_smul]
      | succ e ih => rw [pow_succ, mul_smul, hfx, ih]
    have hB : ∀ m : ℕ, m < 3 → ∀ e : ℕ, f ^ e = ⟨a ^ m * c, hyF m⟩ →
        (⟨a, haF⟩ : fsub hac ha3 hc3) • x = x := by
      intro m hm e he
      have h1 : (⟨a ^ m * c, hyF m⟩ : fsub hac ha3 hc3) • x = x := by
        rw [← he]
        exact hpow e
      rw [hfix1 m hm ⟨a ^ m * c, hyF m⟩ rfl x h1, smul_one]
    have hA : ∀ e : ℕ, f ^ e = ⟨a, haF⟩ → (⟨a, haF⟩ : fsub hac ha3 hc3) • x = x := by
      intro e he
      rw [← he]
      exact hpow e
    have hred : ∃ n' k' : ℕ, n' < 3 ∧ k' < 3 ∧ (f : G) = a ^ n' * c ^ k' := by
      obtain ⟨n, k, hnk⟩ := f.2
      exact ⟨n % 3, k % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
        by rw [hnk, hmoda n, hmodc k]⟩
    obtain ⟨n', k', hn', hk', hfnk⟩ := hred
    interval_cases n' <;> interval_cases k'
    · exact (hf1 (Subtype.ext (by rw [hfnk]; simp))).elim
    · exact hB 0 (by norm_num) 1
        (Subtype.ext (by rw [Subgroup.coe_pow, hfnk, hpow_key]; norm_num))
    · exact hB 0 (by norm_num) 2
        (Subtype.ext (by rw [Subgroup.coe_pow, hfnk, hpow_key]; norm_num))
    · exact hA 1 (Subtype.ext (by rw [Subgroup.coe_pow, hfnk, hpow_key]; norm_num))
    · exact hB 1 (by norm_num) 1
        (Subtype.ext (by rw [Subgroup.coe_pow, hfnk, hpow_key]; norm_num))
    · exact hB 2 (by norm_num) 2
        (Subtype.ext (by rw [Subgroup.coe_pow, hfnk, hpow_key]; norm_num))
    · exact hA 2 (Subtype.ext (by rw [Subgroup.coe_pow, hfnk, hpow_key]; norm_num))
    · exact hB 2 (by norm_num) 1
        (Subtype.ext (by rw [Subgroup.coe_pow, hfnk, hpow_key]; norm_num))
    · exact hB 1 (by norm_num) 2
        (Subtype.ext (by rw [Subgroup.coe_pow, hfnk, hpow_key]; norm_num))
  have hle : ∀ f : fsub hac ha3 hc3, f ≠ 1 →
      CFSG.fixedPointSubgroup (↥(Subgroup.zpowers f)) (U ⧸ V.subgroupOf U) ≤
        CFSG.fixedPointSubgroup (↥(Subgroup.zpowers (⟨a, haF⟩ : fsub hac ha3 hc3)))
          (U ⧸ V.subgroupOf U) := by
    intro f hf1 x hx
    have hfx : f • x = x := (FixedPoints.mem_subgroup _ _ _).mp hx ⟨f, Subgroup.mem_zpowers f⟩
    have hax := hK f hf1 x hfx
    refine (FixedPoints.mem_subgroup _ _ _).mpr fun m => ?_
    have hst : Subgroup.zpowers (⟨a, haF⟩ : fsub hac ha3 hc3) ≤
        MulAction.stabilizer (fsub hac ha3 hc3) x :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hax)
    exact MulAction.mem_stabilizer_iff.mp (hst m.2)
  have hT : (⊤ : Subgroup (U ⧸ V.subgroupOf U)) ≤
      CFSG.fixedPointSubgroup (↥(Subgroup.zpowers (⟨a, haF⟩ : fsub hac ha3 hc3)))
        (U ⧸ V.subgroupOf U) := by
    rw [← hsup]
    exact iSup₂_le fun f hf => hle f hf
  intro u hu
  have h1 : (⟨a, haF⟩ : fsub hac ha3 hc3) • ((⟨u, hu⟩ : U) : U ⧸ V.subgroupOf U) =
      ((⟨u, hu⟩ : U) : U ⧸ V.subgroupOf U) :=
    (FixedPoints.mem_subgroup _ _ _).mp
      (hT (Subgroup.mem_top ((⟨u, hu⟩ : U) : U ⧸ V.subgroupOf U))) ⟨_, Subgroup.mem_zpowers _⟩
  rw [hsmulq] at h1
  have h2 : (⟨u, hu⟩ : U)⁻¹ * ((⟨a, haF⟩ : fsub hac ha3 hc3) • (⟨u, hu⟩ : U)) ∈
      V.subgroupOf U :=
    QuotientGroup.eq.mp h1.symm
  have h3 : u⁻¹ * (a * u * a⁻¹) ∈ V := by
    have h4 := Subgroup.mem_subgroupOf.mp h2
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, hθ] at h4
    exact h4
  have h5 := hVn u hu _ h3
  have e : u * (u⁻¹ * (a * u * a⁻¹)) * u⁻¹ = a * u * a⁻¹ * u⁻¹ := by group
  rwa [e] at h5

end CFSG.RankThree.PartTwo.Sec8.Hering611
