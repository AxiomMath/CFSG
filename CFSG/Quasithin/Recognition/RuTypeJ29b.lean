module

public import CFSG.Quasithin.Recognition.RuTypeJ29a

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

noncomputable abbrev Ls [Finite G] (s : G) : Subgroup G :=
  CFSG.GorensteinWalter.pResidualOf (Cen s) 2

theorem Ls_le_Cen [Finite G] (s : G) : Ls s ≤ Cen s :=
  CFSG.GorensteinWalter.pResidualOf_le _ _

theorem mem_Ls_of_odd [Finite G] {s x : G} (hx : x ∈ Cen s) (hodd : Odd (orderOf x)) :
    x ∈ Ls s :=
  CFSG.GorensteinWalter.mem_pResidualOf_of_order_coprime _ 2 Nat.prime_two hx
    (Nat.coprime_two_left.mpr hodd)

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem S0_inf_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {s' : G} (hs' : s' ∈ M.S0)
    (hL : s' ∈ Ls s) : s' = 1 := by
  by_contra hs'1
  set N : Subgroup G := (M.trS s).ker.map (Cen s).subtype
  have hNle : N ≤ Cen s := Subgroup.map_subtype_le _
  have hNs : N.subgroupOf (Cen s) = (M.trS s).ker := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective
      (Cen s).subtype_injective]
  have hN : (N.subgroupOf (Cen s)).Normal := by rw [hNs]; infer_instance
  have hQ : IsPGroup 2 (Cen s ⧸ N.subgroupOf (Cen s)) := by
    have := hN
    have hA : IsPGroup 2 (Abelianization (M.S3.subgroupOf (Cen s))) := by
      have hP : IsPGroup 2 (M.S3.subgroupOf (Cen s)) := IsPGroup.of_card (n := 8) (by
        rw [card_subgroupOf_of_le (M.S3_le_Cen hs hs1), M.card_S3])
      exact hP.of_surjective Abelianization.of (QuotientGroup.mk_surjective)
    have hR : IsPGroup 2 (M.trS s).range := hA.to_subgroup _
    have h1 : IsPGroup 2 (Cen s ⧸ (M.trS s).ker) :=
      hR.of_equiv (QuotientGroup.quotientKerEquivRange (M.trS s)).symm
    exact h1.of_equiv (QuotientGroup.quotientMulEquivOfEq hNs).symm
  have hle := CFSG.GorensteinWalter.pResidualOf_le_of_quotient_isPGroup (Cen s) N 2
    Nat.prime_two hNle hN hQ
  obtain ⟨x, hx, hxs⟩ := hle hL
  apply M.trS_ne_one hs hs1 hs' hs'1
  have : x = ⟨s', M.S3_le_Cen hs hs1 (M.S0_le_S3 hs')⟩ := Subtype.ext hxs
  rw [← this]
  exact hx

theorem odd_orderOf_cel_pow (k : ℤ) : Odd (orderOf ((M.cel : G) ^ k)) := by
  have h7 : orderOf ((M.cel : G) ^ k) ∣ 7 := orderOf_dvd_of_pow_eq_one (by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, M.cel_pow_seven, one_zpow])
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h7 with h | h <;> rw [h] <;> decide

theorem S1_le_Ls {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) : M.S1 ≤ Ls s := by
  rw [← M.commutator_eq_S1 hs hs1, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have haC : a ∈ Cen s := (Subgroup.mem_inf.mp ha).2
  have hcC : (M.cel : G) ^ k ∈ Cen s := by
    have : (M.cel : G) ∈ Cen s := mem_Cen.mpr (M.mem_S0.mp hs).2
    exact zpow_mem this k
  rw [commutatorElement_def]
  have h1 : a * (M.cel : G) ^ k * a⁻¹ ∈ Ls s := by
    refine mem_Ls_of_odd (mul_mem (mul_mem haC hcC) (inv_mem haC)) ?_
    rw [show a * (M.cel : G) ^ k * a⁻¹ = a * (M.cel : G) ^ k * a⁻¹ from rfl, orderOf_conj_eq]
    exact M.odd_orderOf_cel_pow k
  have h2 : ((M.cel : G) ^ k)⁻¹ ∈ Ls s :=
    inv_mem (mem_Ls_of_odd hcC (M.odd_orderOf_cel_pow k))
  exact mul_mem h1 h2

theorem mem_S1_of_mem_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {x : G} (hx : x ∈ M.S3)
    (hL : x ∈ Ls s) : x ∈ M.S1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := M.exists_S0_S1 hx
  have haL : a ∈ Ls s := by
    have := mul_mem hL (inv_mem (M.S1_le_Ls hs hs1 hb))
    rwa [mul_inv_cancel_right] at this
  rw [M.S0_inf_Ls hs hs1 ha haL, one_mul]
  exact hb

theorem mem_S3_conj_of_comm_V
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {v : G} (hv : v ∈ ruV M.L)
    (hv1 : v ≠ 1) : ∃ k : ℕ, ∀ x ∈ Cen s, x * v = v * x →
      ((M.cel : G) ^ k)⁻¹ * x * (M.cel : G) ^ k ∈ M.S3 := by
  obtain ⟨k, hk⟩ := M.exists_cel_conj_V M.z_mem_V hv M.z_ne_one hv1
  refine ⟨k, fun x hx hxv => ?_⟩
  have hcC : (M.cel : G) ^ k ∈ Cen s := by
    have : (M.cel : G) ∈ Cen s := mem_Cen.mpr (M.mem_S0.mp hs).2
    exact pow_mem this k
  rw [← M.centralizer_H_eq_S3 hs hs1]
  refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem (inv_mem hcC) hx) hcC⟩
  rw [M.mem_H_iff_comm]
  rw [← hk] at hxv
  calc M.z * (((M.cel : G) ^ k)⁻¹ * x * (M.cel : G) ^ k) =
      ((M.cel : G) ^ k)⁻¹ * (((M.cel : G) ^ k * M.z * ((M.cel : G) ^ k)⁻¹) * x) *
        (M.cel : G) ^ k := by group
    _ = ((M.cel : G) ^ k)⁻¹ * (x * ((M.cel : G) ^ k * M.z * ((M.cel : G) ^ k)⁻¹)) *
        (M.cel : G) ^ k := by rw [hxv]
    _ = ((M.cel : G) ^ k)⁻¹ * x * (M.cel : G) ^ k * M.z := by group

theorem eq_one_of_odd_comm_V
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {v : G} (hv : v ∈ ruV M.L)
    (hv1 : v ≠ 1) {x : G} (hx : x ∈ Cen s) (hxv : x * v = v * x) (hodd : Odd (orderOf x)) :
    x = 1 := by
  obtain ⟨k, hk⟩ := M.mem_S3_conj_of_comm_V hs hs1 hv hv1
  have h := hk x hx hxv
  set y := ((M.cel : G) ^ k)⁻¹ * x * (M.cel : G) ^ k with hy
  have hy2 : orderOf y ∣ 2 ^ 8 := by
    rw [← M.card_S3]
    exact Subgroup.orderOf_dvd_natCard _ h
  have hyo : orderOf y = orderOf x := by
    rw [hy, show ((M.cel : G) ^ k)⁻¹ * x * (M.cel : G) ^ k =
      ((M.cel : G) ^ k)⁻¹ * x * ((M.cel : G) ^ k)⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq]
  rw [hyo] at hy2
  obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy2
  have hi0 : i = 0 := by
    by_contra h0
    rw [hie] at hodd
    exact Nat.not_even_iff_odd.mpr hodd ((Nat.even_pow' h0).mpr even_two)
  rw [hi0, pow_zero] at hie
  exact orderOf_eq_one_iff.mp hie

theorem eq_bot_of_odd
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {X : Subgroup G} (hXC : X ≤ Cen s)
    (hodd : Odd (Nat.card X)) (hXV : ∀ v ∈ ruV M.L, ∀ x ∈ X, v * x * v⁻¹ ∈ X) : X = ⊥ := by
  have hodd' : ∀ x ∈ X, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard X hx)
  let φ : ∀ v ∈ ruV M.L, X →* X := fun v hv =>
    { toFun := fun x => ⟨v * x * v⁻¹, hXV v hv x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hfpf : ∀ v (hv : v ∈ ruV M.L), v ≠ 1 → MonoidHom.FixedPointFree (φ v hv) := by
    intro v hv hv1 x hx
    have hxv : (x : G) * v = v * x := by
      have := congrArg Subtype.val hx
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk] at this
      calc (x : G) * v = (v * x * v⁻¹) * v := by rw [this]
        _ = v * x := by group
    exact Subtype.ext (M.eq_one_of_odd_comm_V hs hs1 hv hv1 (hXC x.2) hxv (hodd' _ x.2))
  have hinvol : ∀ v (hv : v ∈ ruV M.L), Function.Involutive (φ v hv) := by
    intro v hv x
    apply Subtype.ext
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
    have hv2 : v * v = 1 := by rw [← pow_two]; exact M.sq_eq_one_of_V hv
    calc v * (v * x * v⁻¹) * v⁻¹ = (v * v) * x * (v * v)⁻¹ := by group
      _ = x := by rw [hv2]; group
  have hv1V : (M.cel : G) * M.z * (M.cel : G)⁻¹ ∈ ruV M.L :=
    M.toRuData.conj_mem_V M.cel.2 M.z_mem_V
  have hzc : (M.cel : G) * M.z * (M.cel : G)⁻¹ ≠ M.z := by
    intro h
    have h' : (M.cel : G) * (⟨M.z, M.z_mem_V⟩ : ruV M.L) * (M.cel : G)⁻¹ =
        (⟨M.z, M.z_mem_V⟩ : ruV M.L) := h
    have h0 := SL3.c0_fix_vec _ ((M.conj_cel_V ⟨M.z, M.z_mem_V⟩).mp h')
    rw [show (⟨M.z, M.z_mem_V⟩ : ruV M.L) = M.zV from rfl, M.ψV_zV] at h0
    exact absurd h0 (by decide)
  set w := (M.cel : G) * M.z * (M.cel : G)⁻¹ with hwdef
  have hw1 : w ≠ 1 := fun h => M.z_ne_one (by
    have : M.z = (M.cel : G)⁻¹ * w * M.cel := by rw [hwdef]; group
    rw [this, h]; group)
  have hzw : M.z * w ∈ ruV M.L := mul_mem M.z_mem_V hv1V
  have hzw1 : M.z * w ≠ 1 := fun h => hzc (by
    have : w = M.z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right M.z_mul_self])
  rw [eq_bot_iff]
  intro x hx
  have h1 := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive
    (hfpf _ M.z_mem_V M.z_ne_one) (hinvol _ M.z_mem_V)) ⟨x, hx⟩
  have h2 := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive
    (hfpf _ hv1V hw1) (hinvol _ hv1V)) ⟨x, hx⟩
  have e1 : M.z * x * M.z⁻¹ = x⁻¹ := congrArg Subtype.val h1
  have e2 : w * x * w⁻¹ = x⁻¹ := congrArg Subtype.val h2
  have hcx : x * (M.z * w) = (M.z * w) * x := by
    have e3 : (M.z * w) * x * (M.z * w)⁻¹ = x := by
      calc (M.z * w) * x * (M.z * w)⁻¹ = M.z * (w * x * w⁻¹) * M.z⁻¹ := by group
        _ = M.z * x⁻¹ * M.z⁻¹ := by rw [e2]
        _ = (M.z * x * M.z⁻¹)⁻¹ := by group
        _ = x := by rw [e1, inv_inv]
    calc x * (M.z * w) = ((M.z * w) * x * (M.z * w)⁻¹) * (M.z * w) := by rw [e3]
      _ = (M.z * w) * x := by group
  exact Subgroup.mem_bot.mpr (M.eq_one_of_odd_comm_V hs hs1 hzw hzw1 (hXC hx) hcx (hodd' x hx))

theorem mem_S1_of_comm_V
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {v : G} (hv : v ∈ ruV M.L)
    (hv1 : v ≠ 1) {x : G} (hx : x ∈ Ls s) (hxv : x * v = v * x) : x ∈ M.S1 := by
  obtain ⟨k, hk⟩ := M.mem_S3_conj_of_comm_V hs hs1 hv hv1
  have hxC := Ls_le_Cen s hx
  have h := hk x hxC hxv
  have hcC : (M.cel : G) ^ k ∈ Cen s := by
    have : (M.cel : G) ∈ Cen s := mem_Cen.mpr (M.mem_S0.mp hs).2
    exact pow_mem this k
  have hLn : ((M.cel : G) ^ k)⁻¹ * x * (M.cel : G) ^ k ∈ Ls s := by
    have hn := CFSG.GorensteinWalter.pResidualOf_subgroupOf_normal (Cen s) 2
    have := hn.conj_mem ⟨x, hxC⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨_, inv_mem hcC⟩
    simpa using Subgroup.mem_subgroupOf.mp this
  have hy := M.mem_S1_of_mem_Ls hs hs1 h hLn
  have e : x = (M.cel : G) ^ k * (((M.cel : G) ^ k)⁻¹ * x * (M.cel : G) ^ k) *
      ((M.cel : G) ^ k)⁻¹ := by group
  rw [e]
  exact M.cel_pow_conj_S1 k hy

end RuDataM

end CFSG.Quasithin.RuType
