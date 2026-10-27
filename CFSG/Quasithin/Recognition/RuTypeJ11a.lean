module

public import CFSG.Quasithin.Recognition.RuTypeJ47b
public import CFSG.Quasithin.Recognition.RuTypeJ44c
public import CFSG.Quasithin.Recognition.RuRank3TitsFacts

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuRank3
open scoped Pointwise

namespace RuDataM

variable {G : Type} [Group G] [Finite G] {F : Subgroup G}

@[expose] noncomputable def Fd (φ : ↥F ≃* titsA) : Subgroup G :=
  ((titsD.subgroupOf titsA).comap φ.toMonoidHom).map F.subtype

section Fd

variable (φ : ↥F ≃* titsA)

omit [Finite G] in
theorem Fd_le : Fd φ ≤ F := Subgroup.map_subtype_le _

omit [Finite G] in
theorem mem_Fd_iff {x : G} (hx : x ∈ F) : x ∈ Fd φ ↔ φ ⟨x, hx⟩ ∈ titsD.subgroupOf titsA := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite G] in
theorem subgroupOf_Fd : (Fd φ).subgroupOf F = (titsD.subgroupOf titsA).comap φ.toMonoidHom := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_Fd_iff φ x.2]
  rfl

omit [Finite G] in
theorem index_Fd : ((Fd φ).subgroupOf F).index = 2 := by
  rw [subgroupOf_Fd, Subgroup.index_comap_of_surjective _ φ.surjective, titsD_index]

omit [Finite G] in
theorem card_Fd : Nat.card (Fd φ) = 17971200 := by
  rw [Fd, Subgroup.card_map_of_injective F.subtype_injective,
    Nat.card_congr ((Subgroup.equivMapOfInjective ((titsD.subgroupOf titsA).comap φ.toMonoidHom)
      φ.toMonoidHom φ.injective).toEquiv)]
  have e : ((titsD.subgroupOf titsA).comap φ.toMonoidHom).map φ.toMonoidHom =
      titsD.subgroupOf titsA :=
    Subgroup.map_comap_eq_self_of_surjective φ.surjective _
  rw [e, card_subgroupOf_of_le titsD_le_titsA, card_titsD]

omit [Finite G] in
include φ in
theorem card_F_of : Nat.card F = 35942400 := by
  rw [Nat.card_congr φ.toEquiv, card_titsA]

omit [Finite G] in
theorem sq_mem_Fd {x : G} (hx : x ∈ F) : x ^ 2 ∈ Fd φ := by
  have h := Subgroup.sq_mem_of_index_two (index_Fd φ) ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

omit [Finite G] in
theorem mem_Fd_of_pow_odd {x : G} (hx : x ∈ F) {k : ℕ} (hk : x ^ (2 * k + 1) = 1) :
    x ∈ Fd φ := by
  have e : (x ^ 2) ^ (k + 1) = x := by
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hk, one_mul]
  rw [← e]
  exact pow_mem (sq_mem_Fd φ hx) _

omit [Finite G] in
theorem conj_mem_Fd {f x : G} (hf : f ∈ F) (hx : x ∈ Fd φ) : f * x * f⁻¹ ∈ Fd φ := by
  have hN := Subgroup.normal_of_index_eq_two (index_Fd φ)
  have h := hN.conj_mem ⟨x, Fd_le φ hx⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx) ⟨f, hf⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

omit [Finite G] in
theorem eq_Fd_of_le {K : Subgroup G} (hK : K ≤ F) (hcard : Nat.card K = 17971200) :
    K = Fd φ := by
  have hidx : ((K.subgroupOf F).map φ.toMonoidHom).index = 2 := by
    rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
    have h := Subgroup.card_mul_index (K.subgroupOf F)
    rw [card_subgroupOf_of_le hK, hcard, card_F_of φ] at h
    omega
  have h := eq_titsD_of_index_eq_two hidx
  have h2 : K.subgroupOf F = (Fd φ).subgroupOf F := by
    rw [subgroupOf_Fd, ← h]
    exact (Subgroup.comap_map_eq_self_of_injective φ.injective _).symm
  have hK' := Subgroup.subgroupOf_inj.mp h2
  rwa [inf_eq_left.mpr hK, inf_eq_left.mpr (Fd_le φ)] at hK'

omit [Finite G] in
theorem eq_one_of_mem_F_of_comm_Fd
    {x : G} (hx : x ∈ F) (hc : ∀ y ∈ Fd φ, x * y = y * x) : x = 1 := by
  have h : φ ⟨x, hx⟩ ∈ Subgroup.centralizer ((titsD.subgroupOf titsA : Subgroup titsA) :
      Set titsA) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : ((φ.symm d : ↥F) : G) ∈ Fd φ := by
      rw [mem_Fd_iff φ (φ.symm d).2]
      simpa using hd
    have hc' := hc _ hd'
    have : (⟨x, hx⟩ : ↥F) * φ.symm d = φ.symm d * ⟨x, hx⟩ := Subtype.ext hc'
    have h2 := congrArg φ this
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  rw [centralizer_titsD, Subgroup.mem_bot] at h
  have h3 : (⟨x, hx⟩ : ↥F) = 1 := φ.injective (by rw [h, map_one])
  exact congrArg Subtype.val h3

end Fd

variable (M : RuDataM G)

theorem centralizer_Fd_eq_bot
    (φ : ↥F ≃* titsA) {b : G} (hbF : b ∈ F) (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    Subgroup.centralizer (Fd φ : Set G) = ⊥ := by
  have hp5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.centralizer (Fd φ : Set G) with hK
  have hmemK : ∀ k ∈ K, ∀ y ∈ Fd φ, k * y = y * k := fun k hk y hy =>
    ((Subgroup.mem_centralizer_iff.mp hk) y hy).symm
  have hbFd : b ∈ Fd φ :=
    mem_Fd_of_pow_odd φ hbF (k := 2)
      (by rw [show 2 * 2 + 1 = 5 by norm_num, ← hb5]; exact pow_orderOf_eq_one b)
  have hKF : ∀ k ∈ K, k ∈ F → k = 1 := fun k hk hkF =>
    eq_one_of_mem_F_of_comm_Fd φ hkF (hmemK k hk)
  have hKb : ∀ k ∈ K, k ∈ G5 b := fun k hk => mem_G5.mpr (hmemK k hk b hbFd)
  have h2 : ∀ k ∈ K, k * k = 1 → k = 1 := by
    intro k hk hk2
    by_contra hk1
    have hkG : (⟨k, hKb k hk⟩ : G5 b) ∈ (Subgroup.zpowers (⟨k, hKb k hk⟩ : G5 b)) :=
      Subgroup.mem_zpowers _
    have hzp : IsPGroup 2 (Subgroup.zpowers (⟨k, hKb k hk⟩ : G5 b)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      refine orderOf_eq_prime ?_ ?_
      · exact Subtype.ext (by simpa [pow_two] using hk2)
      · exact fun h => hk1 (congrArg Subtype.val h)
    obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (G5 b) (T5syl hbH hb5) Q
    have hkQ : (⟨k, hKb k hk⟩ : G5 b) ∈
        ((c • T5syl hbH hb5 : Sylow 2 (G5 b)) : Subgroup (G5 b)) := by
      rw [hc]
      exact hQ hkG
    rw [Sylow.coe_subgroup_smul, coe_T5syl, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_subgroupOf] at hkQ
    have e : (((MulAut.conj c)⁻¹ • (⟨k, hKb k hk⟩ : G5 b) : G5 b) : G) =
        (c : G)⁻¹ * k * c := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
      simp
    rw [e] at hkQ
    have hτ2 : ((c : G)⁻¹ * k * c) ^ 2 = 1 := by
      rw [pow_two]
      calc (c : G)⁻¹ * k * c * ((c : G)⁻¹ * k * c) = (c : G)⁻¹ * (k * k) * c := by group
        _ = 1 := by rw [hk2]; group
    have hτ1 : (c : G)⁻¹ * k * c ≠ 1 := fun h => hk1 (by
      calc k = (c : G) * ((c : G)⁻¹ * k * c) * (c : G)⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have hτz := eq_z_of_T5 hbH hb5 hkQ hτ2 hτ1
    have hkz : IsConj M.z k := isConj_iff.mpr ⟨(c : G), by rw [← hτz]; group⟩
    have hle : Fd φ ≤ Subgroup.centralizer ({k} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hmemK k hk y hy).symm
    have hcd := Subgroup.card_dvd_of_le hle
    rw [card_Fd, M.card_centralizer_of_isConj hkz, M.toRuData.card_H] at hcd
    norm_num at hcd
  have h5 : ∀ k ∈ K, k ^ 5 = 1 → k = 1 := by
    intro k hk hk5
    by_contra hk1
    have hko : orderOf k = 5 := orderOf_eq_prime hk5 hk1
    have h25 : 5 ^ 2 ∣ Nat.card F := by rw [card_F_of φ]; norm_num
    obtain ⟨PF, hPF⟩ := Sylow.exists_subgroup_card_pow_prime 5 h25
    set P := PF.map F.subtype with hP
    have hPcard : Nat.card P = 25 := by
      rw [hP, Subgroup.card_map_of_injective F.subtype_injective, hPF]
      norm_num
    have hPF' : P ≤ F := Subgroup.map_subtype_le _
    have hPFd : P ≤ Fd φ := by
      intro y hy
      have hy25 : y ^ 25 = 1 := by
        have := pow_card_eq_one' (G := ↥P) (x := ⟨y, hy⟩)
        rw [hPcard] at this
        simpa using congrArg Subtype.val this
      exact mem_Fd_of_pow_odd φ (hPF' hy) (k := 12) hy25
    have hkP : ∀ y ∈ P, k * y = y * k := fun y hy => hmemK k hk y (hPFd hy)
    have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
      have hc : IsMulCommutative ↥P :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (by rw [hPcard]; norm_num)
      intro x hx y hy
      exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hknorm : Subgroup.zpowers k ≤ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.zpowers_le]
      exact mem_normalizer_of_conj_mem fun y hy => by rw [hkP y hy]; simpa using hy
    have hinf : Subgroup.zpowers k ⊓ P = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hyk, hyP⟩ := Subgroup.mem_inf.mp hy
      rw [Subgroup.mem_bot]
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyk
      have hkn : k ^ n ∈ K := Subgroup.zpow_mem _ hk n
      exact hKF _ hkn (hPF' hyP)
    have hcardX := card_sup_mul_inf_of_normalizes hknorm
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hko, hPcard] at hcardX
    set X := Subgroup.zpowers k ⊔ P with hX
    have hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
      have hXset : ((X : Subgroup G) : Set G) =
          ((Subgroup.zpowers k : Subgroup G) : Set G) * (P : Set G) := by
        rw [hX]
        exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hknorm
      have hdec : ∀ x ∈ X, ∃ m : ℤ, ∃ q ∈ P, x = k ^ m * q := by
        intro x hx
        have hx' : x ∈ ((Subgroup.zpowers k : Subgroup G) : Set G) * (P : Set G) := by
          rw [← hXset]
          exact hx
        obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp hx'
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact ⟨m, q, hq, rfl⟩
      have hkq : ∀ (m : ℤ) (q : G), q ∈ P → k ^ m * q = q * k ^ m := fun m q hq =>
        ((show Commute k q from hkP q hq).zpow_left m).eq
      intro x hx y hy
      obtain ⟨m, q, hq, rfl⟩ := hdec x hx
      obtain ⟨m', q', hq', rfl⟩ := hdec y hy
      calc k ^ m * q * (k ^ m' * q') = k ^ m * (q * k ^ m') * q' := by group
        _ = k ^ m * (k ^ m' * q) * q' := by rw [hkq m' q hq]
        _ = k ^ m' * k ^ m * (q * q') := by
            rw [show k ^ m * (k ^ m' * q) * q' = (k ^ m * k ^ m') * (q * q') by group,
              (Commute.zpow_zpow_self k m m').eq]
        _ = k ^ m' * k ^ m * (q' * q) := by rw [hPab q hq q' hq']
        _ = k ^ m' * (k ^ m * q') * q := by group
        _ = k ^ m' * (q' * k ^ m) * q := by rw [hkq m q' hq']
        _ = k ^ m' * q' * (k ^ m * q) := by group
    have hcardG := M.card_eq
    have hXsyl : IsPGroup 5 X := IsPGroup.of_card (n := 3) (by rw [hcardX]; norm_num)
    have hX5 : ¬ 5 ∣ X.index := by
      intro hd
      have h := Subgroup.card_mul_index X
      rw [hcardX, hcardG] at h
      obtain ⟨c, hc⟩ := hd
      rw [hc] at h
      norm_num at h
      omega
    have hP5syl : IsPGroup 5 (P5 b) :=
      IsPGroup.of_card (n := 3) (by rw [card_P5_eq_125 hbH hb5]; norm_num)
    have hP5idx : ¬ 5 ∣ (P5 b).index := by
      intro hd
      have h := Subgroup.card_mul_index (P5 b)
      rw [card_P5_eq_125 hbH hb5, hcardG] at h
      obtain ⟨c, hc⟩ := hd
      rw [hc] at h
      norm_num at h
      omega
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hXsyl.toSylow hX5) (hP5syl.toSylow hP5idx)
    apply not_comm_P5 hbH hb5
    intro x hx y hy
    have hsub : ((g • hXsyl.toSylow hX5 : Sylow 5 G) : Subgroup G) = P5 b := by
      rw [hg]
      rfl
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at hsub
    rw [← hsub] at hx hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx hy
    have h := hXab _ hx _ hy
    have e : ∀ w : G, (MulAut.conj g)⁻¹ • w = g⁻¹ * w * g := fun w => by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [e, e] at h
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = y * x := by group
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  by_contra hk1
  have hfin : Finite K := inferInstance
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show Nat.card K ≠ 1 by
    intro h1
    apply hk1
    have := Subgroup.card_eq_one.mp h1
    have hk' : k ∈ (⊥ : Subgroup G) := this ▸ hk
    exact Subgroup.mem_bot.mp hk')
  have hpf : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hxK : (x : G) ∈ K := x.2
  have hxo : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hx1 : (x : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    exact hp.one_lt.ne' hxo.symm
  have hdvd : p ∣ 1000 := by
    have h1 : orderOf (x : G) ∣ Nat.card (G5 b) := by
      have := Subgroup.orderOf_dvd_natCard (G5 b) (hKb x hxK)
      exact this
    rw [card_G5 hbH hb5, card_P5_eq_125 hbH hb5, hxo] at h1
    norm_num at h1
    exact h1
  have hp25 : p = 2 ∨ p = 5 := by
    have h1000 : (1000 : ℕ) = 2 ^ 3 * 5 ^ 3 := by norm_num
    rw [h1000] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h))
  rcases hp25 with rfl | rfl
  · exact hx1 (h2 _ hxK (by rw [← pow_two, ← hxo]; exact pow_orderOf_eq_one _))
  · exact hx1 (h5 _ hxK (by rw [← hxo]; exact pow_orderOf_eq_one _))


@[expose] noncomputable def FdEquiv (φ : ↥F ≃* titsA) :
    ↥(Fd φ) ≃* ↥titsD :=
  (((Subgroup.equivMapOfInjective ((titsD.subgroupOf titsA).comap φ.toMonoidHom) F.subtype
      F.subtype_injective).symm.trans
    (Subgroup.equivMapOfInjective _ _ φ.injective)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective φ.surjective _))).trans
    (Subgroup.subgroupOfEquivOfLe titsD_le_titsA)

theorem normalizer_Fd_le
    (φ : ↥F ≃* titsA) (hC : Subgroup.centralizer (Fd φ : Set G) = ⊥) :
    Subgroup.normalizer (Fd φ : Set G) ≤ F := by
  have hinj : Function.Injective (Subgroup.normalizerMonoidHom (Fd φ)) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC, Subgroup.bot_subgroupOf]
  have hMA : Nat.card (MulAut ↥(Fd φ)) = 35942400 := by
    rw [Nat.card_congr (MulAut.congr (FdEquiv φ)).toEquiv, ← Nat.card_congr titsConjEquiv.toEquiv,
      card_titsA]
  have hfin : Finite (MulAut ↥(Fd φ)) := Nat.finite_of_card_ne_zero (by rw [hMA]; norm_num)
  have hcard := Nat.card_le_card_of_injective _ hinj
  have hFle : F ≤ Subgroup.normalizer (Fd φ : Set G) := fun f hf =>
    mem_normalizer_of_conj_mem fun x hx => conj_mem_Fd φ hf hx
  have heq := Subgroup.eq_of_le_of_card_ge hFle (by rw [card_F_of φ]; omega)
  exact heq.symm.le

theorem normalizer_F_le
    (φ : ↥F ≃* titsA) (hC : Subgroup.centralizer (Fd φ : Set G) = ⊥) :
    Subgroup.normalizer (F : Set G) ≤ F := by
  intro g hg
  apply normalizer_Fd_le φ hC
  have hle : (Fd φ).map (MulAut.conj g).toMonoidHom ≤ F := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp (Fd_le φ hx)
  have hcard : Nat.card ((Fd φ).map (MulAut.conj g).toMonoidHom) = 17971200 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_Fd]
  have heq := eq_Fd_of_le φ hle hcard
  exact mem_normalizer_of_conj_mem fun x hx => by
    have : g * x * g⁻¹ ∈ (Fd φ).map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rwa [heq] at this

theorem eq_one_of_forall_conj_mem
    (φ : ↥F ≃* titsA) (hC : Subgroup.centralizer (Fd φ : Set G) = ⊥)
    (hG : Nat.card F < Nat.card G) {g : G} (hg : ∀ x : G, x * g * x⁻¹ ∈ F) : g = 1 := by
  set K := F.normalCore with hK
  have hgK : g ∈ K := fun b => hg b
  have hKF : K ≤ F := Subgroup.normalCore_le F
  have hKn : K.Normal := Subgroup.normalCore_normal F
  have hsimple : IsSimpleGroup titsD := titsD_simple
  have hLn : ((K.subgroupOf (Fd φ)).map (FdEquiv φ).toMonoidHom).Normal := by
    have : (K.subgroupOf (Fd φ)).Normal := Subgroup.normal_subgroupOf
    exact Subgroup.Normal.map this _ (FdEquiv φ).surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((K.subgroupOf (Fd φ)).map (FdEquiv φ).toMonoidHom) with h | h
  ·
    have hKd : ∀ x ∈ K, x ∈ Fd φ → x = 1 := by
      intro x hxK hxd
      have hx : (⟨x, hxd⟩ : Fd φ) ∈ K.subgroupOf (Fd φ) := hxK
      have hx' : (FdEquiv φ ⟨x, hxd⟩) ∈ (K.subgroupOf (Fd φ)).map (FdEquiv φ).toMonoidHom :=
        ⟨_, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at hx'
      have := (FdEquiv φ).injective (hx'.trans (map_one _).symm)
      exact congrArg Subtype.val this
    have hgC : g ∈ Subgroup.centralizer (Fd φ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hc1 : g * d * g⁻¹ * d⁻¹ ∈ K := by
        have : d * g⁻¹ * d⁻¹ ∈ K := hKn.conj_mem _ (inv_mem hgK) d
        have h2 := mul_mem hgK this
        rwa [show g * (d * g⁻¹ * d⁻¹) = g * d * g⁻¹ * d⁻¹ by group] at h2
      have hc2 : g * d * g⁻¹ * d⁻¹ ∈ Fd φ :=
        mul_mem (conj_mem_Fd φ (hKF hgK) hd) (inv_mem hd)
      have h1 := hKd _ hc1 hc2
      calc d * g = (g * d * g⁻¹ * d⁻¹)⁻¹ * (g * d) := by group
        _ = g * d := by rw [h1, inv_one, one_mul]
    rw [hC, Subgroup.mem_bot] at hgC
    exact hgC
  ·
    exfalso
    have hdK : Fd φ ≤ K := by
      intro x hx
      have hx' : (FdEquiv φ ⟨x, hx⟩) ∈ (K.subgroupOf (Fd φ)).map (FdEquiv φ).toMonoidHom := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : y = ⟨x, hx⟩ := (FdEquiv φ).injective hyx
      rw [hyx'] at hy
      exact hy
    have htop : (⊤ : Subgroup G) ≤ F := by
      intro x _
      apply normalizer_Fd_le φ hC
      have hle : (Fd φ).map (MulAut.conj x).toMonoidHom ≤ F := by
        rintro _ ⟨y, hy, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hKF (hKn.conj_mem y (hdK hy) x)
      have hcard : Nat.card ((Fd φ).map (MulAut.conj x).toMonoidHom) = 17971200 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, card_Fd]
      have heq := eq_Fd_of_le φ hle hcard
      exact mem_normalizer_of_conj_mem fun y hy => by
        have : x * y * x⁻¹ ∈ (Fd φ).map (MulAut.conj x).toMonoidHom :=
          ⟨y, hy, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
        rwa [heq] at this
    have := Subgroup.card_le_of_le htop
    rw [Subgroup.card_top] at this
    omega

end RuDataM

end CFSG.Quasithin.RuType
