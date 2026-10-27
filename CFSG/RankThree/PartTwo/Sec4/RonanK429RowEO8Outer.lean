module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEO8Five
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowETools
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

namespace O8Out

open CFSG.EvenSmallLie.OmegaEight
open CFSG.RankThree.PartTwo.Sec4 (autFix mem_autFix)


noncomputable def z1 : omegaT := ⟨wordPerm w1, wordPerm_mem w1_lt⟩

noncomputable def z2 : omegaT := ⟨wordPerm w2, wordPerm_mem w2_lt⟩

theorem coe_z1 : ((z1 : omegaT) : Equiv.Perm (Fin 360)) = wordPerm w1 := by
  unfold z1
  exact Subtype.coe_mk _ _

theorem coe_z2 : ((z2 : omegaT) : Equiv.Perm (Fin 360)) = wordPerm w2 := by
  unfold z2
  exact Subtype.coe_mk _ _

theorem coe_z1_pow_mul (a b : ℕ) :
    ((z1 ^ a * z2 ^ b : omegaT) : Equiv.Perm (Fin 360)) = wordPerm (wab a b) := by
  rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, coe_z1, coe_z2, wab, wordPerm_append,
    wordPerm_powW, wordPerm_powW]

theorem wordPerm_eq_of_act {u w : List ℕ} (hu : ∀ i ∈ u, i < 8) (hw : ∀ i ∈ w, i < 8)
    (h : ∀ k < 3, ∀ v < 256, wordAct u k v = wordAct w k v) : wordPerm u = wordPerm w := by
  ext p
  obtain ⟨hv1, hv2, hp⟩ := pt_decomp p
  have hk : (p : ℕ) / 120 < 3 := by omega
  rw [(wordPerm_apply u hu hk hv1 hv2 p hp).1, (wordPerm_apply w hw hk hv1 hv2 p hp).1,
    h _ hk _ hv1]

theorem itA_five_zero : ∀ k < 3, ∀ v < 256, itA 5 0 k v = v := by decide +kernel

theorem itA_zero_five : ∀ k < 3, ∀ v < 256, itA 0 5 k v = v := by decide +kernel

theorem appM_comm : ∀ k < 3, ∀ v < 256, appM (m1 k) (appM (m2 k) v) = appM (m2 k) (appM (m1 k) v) := by
  decide +kernel

theorem z1_pow_five : z1 ^ 5 = 1 := by
  apply Subtype.ext
  have h := coe_z1_pow_mul 5 0
  rw [pow_zero, mul_one] at h
  rw [h, Subgroup.coe_one]
  have h1 : wordPerm (wab 5 0) = wordPerm [] :=
    wordPerm_eq_of_act (wab_lt 5 0) (by simp) fun k hk v hv => by
      rw [wordAct_wab 5 0 k hk hv, itA_five_zero k hk v hv]
      rfl
  rw [h1]
  rfl

theorem z2_pow_five : z2 ^ 5 = 1 := by
  apply Subtype.ext
  have h := coe_z1_pow_mul 0 5
  rw [pow_zero, one_mul] at h
  rw [h, Subgroup.coe_one]
  have h1 : wordPerm (wab 0 5) = wordPerm [] :=
    wordPerm_eq_of_act (wab_lt 0 5) (by simp) fun k hk v hv => by
      rw [wordAct_wab 0 5 k hk hv, itA_zero_five k hk v hv]
      rfl
  rw [h1]
  rfl

theorem z1_z2_comm : z1 * z2 = z2 * z1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_z1, coe_z2, ← wordPerm_append, ← wordPerm_append]
  refine wordPerm_eq_of_act (fun i hi => ?_) (fun i hi => ?_) fun k hk v hv => ?_
  · rcases List.mem_append.mp hi with h | h
    · exact w1_lt i h
    · exact w2_lt i h
  · rcases List.mem_append.mp hi with h | h
    · exact w2_lt i h
    · exact w1_lt i h
  · rw [wordAct_append, wordAct_append, w2_act k hk v hv, w1_act k hk v hv,
      w1_act k hk _ (appM_lt k hk v hv).2, w2_act k hk _ (appM_lt k hk v hv).1, appM_comm k hk v hv]

theorem z1_pow_mod (n : ℕ) : z1 ^ n = z1 ^ (n % 5) := pow_eq_pow_mod n z1_pow_five

theorem z2_pow_mod (n : ℕ) : z2 ^ n = z2 ^ (n % 5) := pow_eq_pow_mod n z2_pow_five

theorem zz_mul (a b c d : ℕ) : z1 ^ a * z2 ^ b * (z1 ^ c * z2 ^ d) = z1 ^ (a + c) * z2 ^ (b + d) := by
  have hc : Commute (z2 ^ b) (z1 ^ c) := (Commute.pow_pow z1_z2_comm.symm b c)
  rw [pow_add, pow_add, mul_assoc, ← mul_assoc (z2 ^ b), hc.eq]
  group

noncomputable def P5 : Subgroup omegaT where
  carrier := {g | ∃ a b : ℕ, a < 5 ∧ b < 5 ∧ g = z1 ^ a * z2 ^ b}
  mul_mem' := by
    rintro g h ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
    refine ⟨(a + c) % 5, (b + d) % 5, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    rw [zz_mul, ← z1_pow_mod, ← z2_pow_mod]
  one_mem' := ⟨0, 0, by norm_num, by norm_num, by rw [pow_zero, pow_zero, mul_one]⟩
  inv_mem' := by
    rintro g ⟨a, b, ha, hb, rfl⟩
    refine ⟨(5 - a) % 5, (5 - b) % 5, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← z1_pow_mod, ← z2_pow_mod]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [zz_mul, show a + (5 - a) = 5 by omega, show b + (5 - b) = 5 by omega, z1_pow_five,
      z2_pow_five, mul_one]

theorem zz_ne_one {a b : ℕ} (ha : a < 5) (hb : b < 5) (hab : ¬ (a = 0 ∧ b = 0)) :
    z1 ^ a * z2 ^ b ≠ 1 := by
  intro h1
  have hfix := (fix_wab ha hb hab).2
  have hk0 := k0tab_lt a b
  set k := (k0tab a b + 1) % 3 with hk
  have hp : wordPerm (wab a b) ⟨120 * k, by omega⟩ = ⟨120 * k, by omega⟩ := by
    rw [← coe_z1_pow_mul, h1, Subgroup.coe_one]
    rfl
  have := hfix _ hp
  rw [blk_val] at this
  simp only at this
  omega

theorem zz_inj {a b c d : ℕ} (ha : a < 5) (hb : b < 5) (hc : c < 5) (hd : d < 5)
    (h : z1 ^ a * z2 ^ b = z1 ^ c * z2 ^ d) : a = c ∧ b = d := by
  have h1 : z1 ^ ((a + (5 - c)) % 5) * z2 ^ ((b + (5 - d)) % 5) = 1 := by
    rw [← z1_pow_mod, ← z2_pow_mod, ← zz_mul, h, zz_mul, show c + (5 - c) = 5 by omega,
      show d + (5 - d) = 5 by omega, z1_pow_five, z2_pow_five, mul_one]
  by_contra hne
  refine zz_ne_one (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) ?_ h1
  rintro ⟨h2, h3⟩
  apply hne
  omega

theorem card_P5 : Nat.card P5 = 25 := by
  have hbij : Function.Bijective (fun ab : Fin 5 × Fin 5 =>
      (⟨z1 ^ (ab.1 : ℕ) * z2 ^ (ab.2 : ℕ), ab.1, ab.2, ab.1.2, ab.2.2, rfl⟩ : P5)) := by
    refine ⟨fun x y hxy => ?_, fun g => ?_⟩
    · have h := congrArg Subtype.val hxy
      obtain ⟨h1, h2⟩ := zz_inj x.1.2 x.2.2 y.1.2 y.2.2 h
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · obtain ⟨a, b, ha, hb, hg⟩ := g.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_fin]

theorem exists_conj_zz (x : omegaT) (hx : orderOf x = 5) :
    ∃ g : omegaT, ∃ a b : ℕ, a < 5 ∧ b < 5 ∧ ¬ (a = 0 ∧ b = 0) ∧
      x = g * (z1 ^ a * z2 ^ b) * g⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite omegaT := Nat.finite_of_card_ne_zero (by rw [card_omegaT]; norm_num)
  have hP5 : IsPGroup 5 P5 := IsPGroup.of_card (n := 2) (by rw [card_P5]; norm_num)
  have hidx : ¬ 5 ∣ P5.index := by
    intro h
    have hmul := Subgroup.card_mul_index P5
    rw [card_P5, card_omegaT] at hmul
    omega
  have hzx : IsPGroup 5 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hzx.exists_le_sylow
  let SP : Sylow 5 omegaT := hP5.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq omegaT SP Q
  have hQeq : (Q : Subgroup omegaT) = P5.map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • SP : Sylow 5 omegaT) : Subgroup omegaT) = (Q : Subgroup omegaT) := by rw [hg]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1.symm
  have hxQ : x ∈ (Q : Subgroup omegaT) := hQ (Subgroup.mem_zpowers x)
  rw [hQeq] at hxQ
  obtain ⟨y, hyP, rfl⟩ := hxQ
  obtain ⟨a, b, ha, hb, rfl⟩ := hyP
  refine ⟨g, a, b, ha, hb, fun hab => ?_, rfl⟩
  obtain ⟨rfl, rfl⟩ := hab
  rw [pow_zero, pow_zero, mul_one, map_one, orderOf_one] at hx
  norm_num at hx

theorem fix_one_copy (x : omegaT) (hx : orderOf x = 5) :
    ∃ p0 : Fin 360, (x : Equiv.Perm (Fin 360)) p0 = p0 ∧
      ∀ p, (x : Equiv.Perm (Fin 360)) p = p → blk p = blk p0 := by
  obtain ⟨g, a, b, ha, hb, hab, rfl⟩ := exists_conj_zz x hx
  obtain ⟨⟨q0, hq0⟩, hall⟩ := fix_wab ha hb hab
  have hgK : (g : Equiv.Perm (Fin 360)) ∈ K0 := omegaT_le_K0 g.2
  have hgiK : ((g⁻¹ : omegaT) : Equiv.Perm (Fin 360)) ∈ K0 := omegaT_le_K0 g⁻¹.2
  have hcoe : ((g * (z1 ^ a * z2 ^ b) * g⁻¹ : omegaT) : Equiv.Perm (Fin 360)) =
      (g : Equiv.Perm (Fin 360)) * wordPerm (wab a b) * ((g⁻¹ : omegaT) : Equiv.Perm (Fin 360)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_z1_pow_mul]
  have hgg : ∀ q, ((g⁻¹ : omegaT) : Equiv.Perm (Fin 360)) ((g : Equiv.Perm (Fin 360)) q) = q := by
    intro q
    rw [← Equiv.Perm.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      Equiv.Perm.one_apply]
  have hgg' : ∀ q, (g : Equiv.Perm (Fin 360)) (((g⁻¹ : omegaT) : Equiv.Perm (Fin 360)) q) = q := by
    intro q
    rw [← Equiv.Perm.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Equiv.Perm.one_apply]
  refine ⟨(g : Equiv.Perm (Fin 360)) q0, ?_, fun p hp => ?_⟩
  · rw [hcoe, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgg, hq0]
  · rw [hcoe, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hp
    have hfix : wordPerm (wab a b) (((g⁻¹ : omegaT) : Equiv.Perm (Fin 360)) p) =
        ((g⁻¹ : omegaT) : Equiv.Perm (Fin 360)) p := by
      have h := congrArg ((g⁻¹ : omegaT) : Equiv.Perm (Fin 360)) hp
      rwa [hgg] at h
    have h1 := hall _ hfix
    have h2 := hall _ hq0
    rw [hgK q0, ← hgiK p]
    exact Fin.ext (h1.trans h2.symm)

theorem not_five_dvd_autFix (τ : MulAut omegaT) (hτ3 : τ ^ 3 = 1)
    (hout : τ ∉ (MulAut.conj : omegaT →* MulAut omegaT).range) :
    ¬ 5 ∣ Nat.card (autFix τ) := by
  intro h5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite omegaT := Nat.finite_of_card_ne_zero (by rw [card_omegaT]; norm_num)
  obtain ⟨a, rfl⟩ := autConj_bijective.2 τ
  have ha3 : a ^ 3 = 1 := autConj_injective (by rw [map_pow, hτ3, map_one])
  have haO : (a : Equiv.Perm (Fin 360)) ∉ omegaT := by
    intro haO
    apply hout
    rw [← map_autConj_omegaT]
    exact ⟨a, by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact haO, rfl⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := autFix (autConj a)) 5 h5
  have hx5 : orderOf (x : omegaT) = 5 := by rw [Subgroup.orderOf_coe, hx]
  have hfx : autConj a (x : omegaT) = x := mem_autFix.mp x.2
  have hcomm : (a : Equiv.Perm (Fin 360)) * ((x : omegaT) : Equiv.Perm (Fin 360)) =
      ((x : omegaT) : Equiv.Perm (Fin 360)) * a := by
    have h := congrArg Subtype.val hfx
    rw [autConj_apply] at h
    calc (a : Equiv.Perm (Fin 360)) * ((x : omegaT) : Equiv.Perm (Fin 360))
        = (a : Equiv.Perm (Fin 360)) * ((x : omegaT) : Equiv.Perm (Fin 360)) *
            (a : Equiv.Perm (Fin 360))⁻¹ * a := by group
      _ = ((x : omegaT) : Equiv.Perm (Fin 360)) * a := by rw [h]
  obtain ⟨p0, hp0, hall⟩ := fix_one_copy (x : omegaT) hx5
  have hfa : ((x : omegaT) : Equiv.Perm (Fin 360)) ((a : Equiv.Perm (Fin 360)) p0) =
      (a : Equiv.Perm (Fin 360)) p0 := by
    rw [← Equiv.Perm.mul_apply, ← hcomm, Equiv.Perm.mul_apply, hp0]
  exact haO (mem_omegaT_of_fix_copy a ha3 p0 (hall _ hfa))

theorem good429_outer (τ : MulAut omegaT) (hτ3 : τ ^ 3 = 1)
    (hout : τ ∉ (MulAut.conj : omegaT →* MulAut omegaT).range) : RonanK429H.Good429 (autFix τ) :=
  good429_of_not_dvd (N := 174182400) (B := 559)
    (card_omegaT ▸ Subgroup.card_subgroup_dvd_card _) (by norm_num) (by norm_num) [5]
    (by simpa using not_five_dvd_autFix τ hτ3 hout) (by decide +kernel)

end O8Out

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
