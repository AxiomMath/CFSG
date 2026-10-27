module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.GroupTheory.CoprimeCosetFixed
import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

section Helpers

private theorem exists_zpow_mul_zpow_of_mem_sup {Q : Type} [Group Q] {c d x : Q}
    (hd : d ∈ Subgroup.center Q) (hx : x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    ∃ i j : ℤ, x = c ^ i * d ^ j := by
  haveI : (Subgroup.zpowers d).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hd)
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ⟨i, j, rfl⟩

private theorem zpow_eq_one_of_mem {Q : Type} [Group Q] {c : Q} {S : Subgroup Q}
    (hc : c ^ 3 = 1) (hcS : c ∉ S) {i : ℤ} (hi : c ^ i ∈ S) : c ^ i = 1 := by
  by_contra h1
  have h := TauCeti.zpowers_eq_zpowers_of_mem_zpowers Nat.prime_three hc h1
    (Subgroup.zpow_mem_zpowers c i)
  have hc' : c ∈ Subgroup.zpowers (c ^ i) := by
    rw [h]
    exact Subgroup.mem_zpowers c
  exact hcS (Subgroup.zpowers_le.mpr hi hc')

private theorem mk_mem_center {Q : Type} [Group Q] {J : Subgroup Q} {z : Q} (hzJ : z ∈ J)
    (hz : z ∈ Subgroup.center Q) : (⟨z, hzJ⟩ : ↥J) ∈ Subgroup.center ↥J :=
  Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp hz y)

private theorem mk_mem_normalizer_subgroupOf {Q : Type} [Group Q] {N H : Subgroup Q} {x : Q}
    (hxN : x ∈ N) (hx : x ∈ Subgroup.normalizer (H : Set Q)) :
    (⟨x, hxN⟩ : ↥N) ∈ Subgroup.normalizer ((H.subgroupOf N : Subgroup ↥N) : Set ↥N) :=
  Subgroup.mem_normalizer_iff.mpr fun y => Subgroup.mem_normalizer_iff.mp hx y.1

private theorem commutator_zpowers_subgroupOf {Q : Type} [Group Q] {N U : Subgroup Q} {x : Q}
    (hU : U ≤ N) (hx : x ∈ N) (h : ⁅U, Subgroup.zpowers x⁆ = U) :
    ⁅U.subgroupOf N, Subgroup.zpowers (⟨x, hx⟩ : ↥N)⁆ = U.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left hU]
  exact h

end Helpers

section Images

variable {P M : Type} [Group P] [Group M]

private theorem map_ne_one_of_commutator {ρ : P →* M} {c₁ : P} {U₁ : Subgroup P}
    (hU : ⁅U₁, Subgroup.zpowers c₁⁆ = U₁) (hne : ¬ U₁ ≤ ρ.ker) : ρ c₁ ≠ 1 := by
  intro h1
  refine hne ?_
  calc U₁ = ⁅U₁, Subgroup.zpowers c₁⁆ := hU.symm
    _ ≤ ⁅U₁, ρ.ker⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr h1))
    _ ≤ ρ.ker := Subgroup.commutator_le_right _ _

private theorem map_commutator_zpowers {ρ : P →* M} {g₁ : P} {U₁ : Subgroup P}
    (hU : ⁅U₁, Subgroup.zpowers g₁⁆ = U₁) :
    ⁅U₁.map ρ, Subgroup.zpowers (ρ g₁)⁆ = U₁.map ρ := by
  rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, hU]

private theorem commute_map_of_fixed [Finite P] {ρ : P →* M} {c₁ g₁ : P} {V₁ : Subgroup P}
    (hc3 : c₁ ^ 3 = 1) (hV : IsPGroup 2 V₁) (hcV : c₁ ∈ Subgroup.normalizer (V₁ : Set P))
    (hF : ∀ v ∈ V₁, Commute c₁ v → Commute g₁ v) :
    ∀ v ∈ V₁.map ρ, Commute (ρ c₁) v → Commute (ρ g₁) v := by
  intro v hv hcomm
  obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
  have hnorm : ∀ n ∈ V₁, c₁ * n * c₁⁻¹ ∈ V₁ := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp hcV n).mp hn
  have hWc : ∀ n ∈ V₁ ⊓ ρ.ker, c₁ * n * c₁⁻¹ ∈ V₁ ⊓ ρ.ker := by
    intro n hn
    refine Subgroup.mem_inf.mpr ⟨hnorm n hn.1, ?_⟩
    rw [MonoidHom.mem_ker]
    have h1 : ρ n = 1 := MonoidHom.mem_ker.mp hn.2
    simp [h1]
  have hg : v₀⁻¹ * (c₁ * v₀ * c₁⁻¹) ∈ V₁ ⊓ ρ.ker := by
    refine Subgroup.mem_inf.mpr ⟨V₁.mul_mem (V₁.inv_mem hv₀) (hnorm v₀ hv₀), ?_⟩
    rw [MonoidHom.mem_ker]
    have h1 : ρ c₁ * ρ v₀ = ρ v₀ * ρ c₁ := hcomm.eq
    simp only [map_mul, map_inv]
    rw [h1]
    group
  have hW2 : IsPGroup 2 ↥(V₁ ⊓ ρ.ker) := hV.to_inf_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hW2
  have hcop : Nat.Coprime (orderOf c₁) (Nat.card ↥(V₁ ⊓ ρ.ker)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hc3) (by decide))
  obtain ⟨n, hn, hfix⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime (V₁ ⊓ ρ.ker) hWc hg hcop
  have hv₁ : v₀ * n ∈ V₁ := V₁.mul_mem hv₀ hn.1
  have hcomm₁ : Commute c₁ (v₀ * n) := by
    show c₁ * (v₀ * n) = (v₀ * n) * c₁
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have h2 := hF _ hv₁ hcomm₁
  have h3 : ρ (v₀ * n) = ρ v₀ := by
    rw [map_mul, MonoidHom.mem_ker.mp hn.2, mul_one]
  rw [← h3]
  exact h2.map ρ

end Images

section Aut

variable {Q : Type} [Group Q] {J : Subgroup Q}

private theorem normalizerMonoidHom_fix_iff {x : Q} (hx : x ∈ Subgroup.normalizer (J : Set Q))
    (y : ↥J) : J.normalizerMonoidHom ⟨x, hx⟩ y = y ↔ x * (y : Q) = (y : Q) * x := by
  rw [Subtype.ext_iff, Subgroup.normalizerMonoidHom_apply_apply_coe, mul_inv_eq_iff_eq_mul]

private theorem normalizerMonoidHom_eq_one_iff {x : Q}
    (hx : x ∈ Subgroup.normalizer (J : Set Q)) :
    J.normalizerMonoidHom ⟨x, hx⟩ = 1 ↔ x ∈ Subgroup.centralizer (J : Set Q) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]

private theorem normalizerMonoidHom_eq_conj {x : Q} (hx : x ∈ Subgroup.normalizer (J : Set Q))
    (hxJ : x ∈ J) : J.normalizerMonoidHom ⟨x, hx⟩ = MulAut.conj (⟨x, hxJ⟩ : ↥J) := by
  refine MulEquiv.ext fun y => Subtype.ext ?_
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
  rfl

end Aut

namespace Res3Q

variable {Q : Type} [Group Q] [Finite Q] {c d g : Q} {A B₀ K V₀ U : Subgroup Q}
  (h : Res3Q c d g A B₀ K V₀ U)

include h

private theorem c_mem_A : c ∈ A := by
  rw [h.A_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

private theorem B₀_le_A : B₀ ≤ A := by
  rw [h.A_eq]
  exact le_sup_left

private theorem commute_c_g : Commute c g :=
  Subgroup.mem_centralizer_iff.mp h.g_cent c h.c_mem_A

private theorem c_mem_centralizer_B₀ : c ∈ Subgroup.centralizer (B₀ : Set Q) :=
  Subgroup.mem_centralizer_iff.mpr fun b hb =>
    Subgroup.mem_centralizer_iff.mp h.c_cent b (h.B₀_le hb)

private theorem g_mem_centralizer_B₀ : g ∈ Subgroup.centralizer (B₀ : Set Q) :=
  Subgroup.mem_centralizer_iff.mpr fun b hb =>
    Subgroup.mem_centralizer_iff.mp h.g_cent b (h.B₀_le_A hb)

private theorem mem_centralizer_A {x : Q} (hxK : x ∈ Subgroup.centralizer (K : Set Q))
    (hxc : c * x = x * c) : x ∈ Subgroup.centralizer (A : Set Q) := by
  have hA : A ≤ Subgroup.centralizer ({x} : Set Q) := by
    rw [h.A_eq]
    refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxK b (h.B₀_le hb))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxc
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (hA ha)

private theorem mem_sup_of_mem_J (hC : Res3QCompFacts c d A B₀ K) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hJK : J ≠ K) {x : Q} (hxJ : x ∈ J) (hxc : c * x = x * c)
    (hx3 : x ^ 3 = 1) : x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  have hxK : x ∈ Subgroup.centralizer (K : Set Q) := hC.le_centralizer J hJ hJK hxJ
  rw [← hC.inf_centralizer]
  exact ⟨h.A_max x (h.mem_centralizer_A hxK hxc) hx3, hxK⟩

private theorem cube_aux (hC : Res3QCompFacts c d A B₀ K) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hJK : J ≠ K) (hcJ : c ∉ Subgroup.centralizer (J : Set Q))
    (x : ↥J) (hxc : c * (x : Q) = (x : Q) * c) (hx3 : x ^ 3 ∈ Subgroup.center ↥J) :
    x ^ 3 = 1 := by
  have hxA : (x : Q) ∈ Subgroup.centralizer (A : Set Q) :=
    h.mem_centralizer_A (hC.le_centralizer J hJ hJK x.2) hxc
  have hx3J : (x : Q) ^ 3 ∈ Subgroup.centralizer (J : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx3 ⟨q, hq⟩)
  obtain ⟨k, hk⟩ := hC.center_pGroup J hJ hJK ⟨x ^ 3, hx3⟩
  have hxk : ((x : Q) ^ 3) ^ 3 ^ k = 1 := by
    have := congrArg (fun z : Subgroup.center ↥J => ((z : ↥J) : Q)) hk
    simpa using this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, orderOf (x : Q) = 3 ^ m := by
    have hdvd : orderOf (x : Q) ∣ 3 ^ (k + 1) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_succ', pow_mul]; exact hxk)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact ⟨m, hm⟩
  by_contra hne
  have hne' : (x : Q) ^ 3 ≠ 1 := fun h1 => hne (Subtype.ext (by simpa using h1))
  have hm2 : 2 ≤ m := by
    by_contra hlt
    refine hne' (orderOf_dvd_iff_pow_eq_one.mp ?_)
    rw [hm]
    interval_cases m <;> simp
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hy3 : ((x : Q) ^ 3 ^ n) ^ 3 = ((x : Q) ^ 3) ^ 3 ^ n := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hord : orderOf (((x : Q) ^ 3 ^ n) ^ 3) = 3 := by
    have hdvd : 3 ^ n * 3 ∣ orderOf (x : Q) := by
      rw [hm]
      exact ⟨3, by ring⟩
    rw [← pow_mul, orderOf_pow_of_dvd (by positivity) hdvd, hm]
    exact Nat.div_eq_of_eq_mul_left (by positivity) (by ring)
  have hyA : (x : Q) ^ 3 ^ n ∈ Subgroup.centralizer (A : Set Q) := Subgroup.pow_mem _ hxA _
  have hyP : IsPGroup 3 (Subgroup.zpowers ((x : Q) ^ 3 ^ n)) := by
    refine IsPGroup.of_card_dvd_pow (n := n + 2) ?_
    rw [Nat.card_zpowers, ← hm]
    exact orderOf_pow_dvd _
  have hcy := h.cube _ hyA hyP hord
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hcy
  have hy3J : ((x : Q) ^ 3 ^ n) ^ 3 ∈ Subgroup.centralizer (J : Set Q) := by
    rw [hy3]
    exact Subgroup.pow_mem _ hx3J _
  have h1 : c ^ i = 1 := zpow_eq_one_of_mem h.c_pow hcJ (by rw [hi]; exact hy3J)
  rw [h1] at hi
  rw [← hi, orderOf_one] at hord
  omega

private theorem outer_threes (hC : Res3QCompFacts c d A B₀ K) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hJK : J ≠ K) (hcN : c ∈ Subgroup.normalizer (J : Set Q)) :
    J.normalizerMonoidHom ⟨c, hcN⟩ ∉ (MulAut.conj : ↥J →* MulAut ↥J).range →
      ∀ x : ↥J, J.normalizerMonoidHom ⟨c, hcN⟩ x = x → x ^ 3 = 1 →
        x ∈ Subgroup.center ↥J := by
  intro hnot x hx hx3
  have hxc : c * (x : Q) = (x : Q) * c := (normalizerMonoidHom_fix_iff hcN x).mp hx
  have hx3Q : (x : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
  have hcJ : c ∉ J := fun hcJ => hnot ⟨⟨c, hcJ⟩, (normalizerMonoidHom_eq_conj hcN hcJ).symm⟩
  obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_of_mem_sup h.d_center
    (h.mem_sup_of_mem_J hC hJ hJK x.2 hxc hx3Q)
  have hdJ : d ∈ J := hC.d_mem J hJ hJK
  have hci : c ^ i = 1 := by
    refine zpow_eq_one_of_mem h.c_pow hcJ ?_
    have : c ^ i = (x : Q) * (d ^ j)⁻¹ := by rw [hij]; group
    rw [this]
    exact J.mul_mem x.2 (J.inv_mem (J.zpow_mem hdJ j))
  have hxd : (x : Q) = d ^ j := by rw [hij, hci, one_mul]
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  show (y : Q) * x = x * y
  rw [hxd]
  exact Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ h.d_center j) y

private theorem inner_threes (hC : Res3QCompFacts c d A B₀ K) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hJK : J ≠ K) (hcN : c ∈ Subgroup.normalizer (J : Set Q))
    (hcJ : c ∉ Subgroup.centralizer (J : Set Q))
    (hc3 : J.normalizerMonoidHom ⟨c, hcN⟩ ^ 3 = 1) :
    ∀ j : ↥J, MulAut.conj j = J.normalizerMonoidHom ⟨c, hcN⟩ →
      j ^ 3 = 1 ∧ ∀ x : ↥J, Commute x j → x ^ 3 = 1 →
        x ∈ Subgroup.zpowers j ⊔ Subgroup.center ↥J := by
  intro j hj
  have hjy : ∀ y : ↥J, (j : Q) * y * (j : Q)⁻¹ = c * y * c⁻¹ := by
    intro y
    have := congrArg (fun φ : MulAut ↥J => ((φ y : ↥J) : Q)) hj
    simpa [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  have hjc : c * (j : Q) = (j : Q) * c := by
    have e := hjy j
    rw [mul_inv_cancel_right] at e
    exact mul_inv_eq_iff_eq_mul.mp e.symm
  have hj3conj : (MulAut.conj (j ^ 3) : MulAut ↥J) = 1 := by
    rw [map_pow, hj, hc3]
  have hj3center : j ^ 3 ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := DFunLike.congr_fun hj3conj y
    rw [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  have hj3 : j ^ 3 = 1 := h.cube_aux hC hJ hJK hcJ j hjc hj3center
  refine ⟨hj3, ?_⟩
  have hj3Q : (j : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hj3
  have hjK : (j : Q) ∈ Subgroup.centralizer (K : Set Q) := hC.le_centralizer J hJ hJK j.2
  have hcj : Commute c (j : Q) := hjc
  have hzJ : (j : Q)⁻¹ * c ∈ Subgroup.centralizer (J : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have e := hjy ⟨y, hy⟩
    calc y * ((j : Q)⁻¹ * c) = (j : Q)⁻¹ * ((j : Q) * y * (j : Q)⁻¹) * c := by group
      _ = (j : Q)⁻¹ * (c * y * c⁻¹) * c := by rw [e]
      _ = ((j : Q)⁻¹ * c) * y := by group
  have hzc : c * ((j : Q)⁻¹ * c) = ((j : Q)⁻¹ * c) * c :=
    (hcj.inv_right.mul_right (Commute.refl c)).eq
  have hzK : (j : Q)⁻¹ * c ∈ Subgroup.centralizer (K : Set Q) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hjK) h.c_cent
  have hz3 : ((j : Q)⁻¹ * c) ^ 3 = 1 := by
    rw [(hcj.symm.inv_left).mul_pow, inv_pow, hj3Q, h.c_pow]
    simp
  have hzmem : (j : Q)⁻¹ * c ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [← hC.inf_centralizer]
    exact ⟨h.A_max _ (h.mem_centralizer_A hzK hzc) hz3, hzK⟩
  obtain ⟨a, b, hab⟩ := exists_zpow_mul_zpow_of_mem_sup h.d_center hzmem
  have hdb : d ^ b ∈ Subgroup.centralizer (J : Set Q) :=
    Subgroup.center_le_centralizer _ (Subgroup.zpow_mem _ h.d_center b)
  have hca : c ^ a = 1 := by
    refine zpow_eq_one_of_mem h.c_pow hcJ ?_
    have : c ^ a = ((j : Q)⁻¹ * c) * (d ^ b)⁻¹ := by rw [hab]; group
    rw [this]
    exact Subgroup.mul_mem _ hzJ (Subgroup.inv_mem _ hdb)
  have hcjd : c = (j : Q) * d ^ b := by
    have : (j : Q)⁻¹ * c = d ^ b := by rw [hab, hca, one_mul]
    rw [← this]
    group
  intro x hxj hx3
  have hxj' : (x : Q) * j = j * x := congrArg Subtype.val hxj
  have hxd : (x : Q) * d ^ b = d ^ b * x :=
    Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ h.d_center b) x
  have hxc : c * (x : Q) = (x : Q) * c := by
    rw [hcjd]
    calc (j : Q) * d ^ b * x = j * (d ^ b * x) := by rw [mul_assoc]
      _ = j * (x * d ^ b) := by rw [hxd]
      _ = (j * x) * d ^ b := by rw [mul_assoc]
      _ = (x * j) * d ^ b := by rw [hxj']
      _ = x * (j * d ^ b) := by rw [mul_assoc]
  have hx3Q : (x : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
  have hxmem := h.mem_sup_of_mem_J hC hJ hJK x.2 hxc hx3Q
  have hcmem : c ∈ Subgroup.zpowers (j : Q) ⊔ Subgroup.zpowers d := by
    rw [hcjd]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) (Subgroup.zpow_mem_zpowers d b)
  have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤
      Subgroup.zpowers (j : Q) ⊔ Subgroup.zpowers d :=
    sup_le (Subgroup.zpowers_le.mpr hcmem) le_sup_right
  obtain ⟨p, q, hpq⟩ := exists_zpow_mul_zpow_of_mem_sup h.d_center (hle hxmem)
  have hdJ : d ∈ J := hC.d_mem J hJ hJK
  have hxeq : x = j ^ p * (⟨d, hdJ⟩ : ↥J) ^ q := Subtype.ext (by simpa using hpq)
  rw [hxeq]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers j p)
    (Subgroup.zpow_mem _ (mk_mem_center hdJ h.d_center) q)

private theorem cube_field (hC : Res3QCompFacts c d A B₀ K) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hJK : J ≠ K) (hcN : c ∈ Subgroup.normalizer (J : Set Q))
    (hcJ : c ∉ Subgroup.centralizer (J : Set Q)) :
    ∀ x : ↥J, J.normalizerMonoidHom ⟨c, hcN⟩ x = x → x ^ 3 ∈ Subgroup.center ↥J →
      x ^ 3 = 1 := fun x hx hx3 =>
  h.cube_aux hC hJ hJK hcJ x ((normalizerMonoidHom_fix_iff hcN x).mp hx) hx3

private theorem primes_field (hC : Res3QCompFacts c d A B₀ K) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hJK : J ≠ K) (hcN : c ∈ Subgroup.normalizer (J : Set Q)) :
    ∀ x : ↥J, J.normalizerMonoidHom ⟨c, hcN⟩ x = x → (orderOf x).Prime →
      orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7 := by
  intro x hx hp
  have hxc := (normalizerMonoidHom_fix_iff hcN x).mp hx
  have hxA := h.mem_centralizer_A (hC.le_centralizer J hJ hJK x.2) hxc
  rw [← Subgroup.orderOf_coe] at hp ⊢
  exact h.primes _ hxA hp

private theorem d_ne_one : d ≠ 1 := by
  intro hd
  have h3 := h.K_cover.1
  have hmap : (Subgroup.center ↥K).map K.subtype = ⊥ := by
    rw [h.K_center, hd, Subgroup.zpowers_one_eq_bot]
  have hbot : Subgroup.center ↥K = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at hmap
    exact le_bot_iff.mp hmap
  rw [hbot, Subgroup.card_bot] at h3
  omega

end Res3Q

theorem Res3Q.exists_res3Datum {Q : Type} [Group Q] [Finite Q] {c d g : Q}
    {A B₀ K V₀ U : Subgroup Q} (h : Res3Q c d g A B₀ K V₀ U) (hC : Res3QCompFacts c d A B₀ K)
    {J : Subgroup Q} (hJ : CFSG.IsComponent J) (hJK : J ≠ K)
    (hUJ : ¬ U ≤ Subgroup.centralizer (J : Set Q))
    (hrank5 : ∀ E R : Subgroup ↥J, Nat.card E = 25 → (∀ x ∈ E, x ^ 5 = 1) → IsPGroup 2 R →
      R ≠ ⊥ → E ≤ Subgroup.normalizer (R : Set ↥J) → False) :
    ∃ (c' g' : MulAut ↥J) (V' U' : Subgroup (MulAut ↥J)), Res3Datum c' g' V' U' := by
  have hcN : c ∈ Subgroup.normalizer (J : Set Q) :=
    hC.normalizes J hJ c h.c_mem_centralizer_B₀
  have hgN : g ∈ Subgroup.normalizer (J : Set Q) :=
    hC.normalizes J hJ g h.g_mem_centralizer_B₀
  have hV₀N : V₀ ≤ Subgroup.normalizer (J : Set Q) := fun x hx =>
    hC.normalizes J hJ x (h.V₀_le hx)
  have hUN : U ≤ Subgroup.normalizer (J : Set Q) := h.U_le.trans hV₀N
  have hdJ : d ∈ J := hC.d_mem J hJ hJK
  have hc3 : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (J : Set Q))) ^ 3 = 1 := Subtype.ext h.c_pow
  have hcg : Commute (⟨c, hcN⟩ : ↥(Subgroup.normalizer (J : Set Q))) ⟨g, hgN⟩ :=
    Subtype.ext h.commute_c_g.eq
  have hV₁ : IsPGroup 2 ↥(V₀.subgroupOf (Subgroup.normalizer (J : Set Q))) :=
    h.V₀_isPGroup.comap_subtype
  have hUV : U.subgroupOf (Subgroup.normalizer (J : Set Q)) ≤
      V₀.subgroupOf (Subgroup.normalizer (J : Set Q)) := fun x hx => h.U_le hx
  have hcV := mk_mem_normalizer_subgroupOf hcN h.c_memV₀
  have hgV := mk_mem_normalizer_subgroupOf hgN h.g_memV₀
  have hgU := mk_mem_normalizer_subgroupOf hgN h.g_memU
  have hUg := commutator_zpowers_subgroupOf hUN hgN h.U_comm_g
  have hUc := commutator_zpowers_subgroupOf hUN hcN h.U_comm_c
  have hF : ∀ v ∈ V₀.subgroupOf (Subgroup.normalizer (J : Set Q)),
      Commute (⟨c, hcN⟩ : ↥(Subgroup.normalizer (J : Set Q))) v →
        Commute (⟨g, hgN⟩ : ↥(Subgroup.normalizer (J : Set Q))) v := by
    intro v hv hcv
    have hcv' : c * (v : Q) = (v : Q) * c := congrArg Subtype.val hcv
    exact Subtype.ext (h.F_cent v hv hcv')
  have hne : ¬ U.subgroupOf (Subgroup.normalizer (J : Set Q)) ≤
      J.normalizerMonoidHom.ker := by
    intro hle
    refine hUJ fun u hu => ?_
    have hu1 : J.normalizerMonoidHom ⟨u, hUN hu⟩ = 1 :=
      MonoidHom.mem_ker.mp (hle (Subgroup.mem_subgroupOf.mpr hu))
    exact (normalizerMonoidHom_eq_one_iff (hUN hu)).mp hu1
  have hc1 : J.normalizerMonoidHom ⟨c, hcN⟩ ≠ 1 := map_ne_one_of_commutator hUc hne
  have hcJ : c ∉ Subgroup.centralizer (J : Set Q) := fun hc =>
    hc1 ((normalizerMonoidHom_eq_one_iff hcN).mpr hc)
  have hc3' : J.normalizerMonoidHom ⟨c, hcN⟩ ^ 3 = 1 := by
    rw [← map_pow, hc3, map_one]
  refine ⟨J.normalizerMonoidHom ⟨c, hcN⟩, J.normalizerMonoidHom ⟨g, hgN⟩,
    (V₀.subgroupOf (Subgroup.normalizer (J : Set Q))).map J.normalizerMonoidHom,
    (U.subgroupOf (Subgroup.normalizer (J : Set Q))).map J.normalizerMonoidHom, ?_⟩
  exact
    { center_pGroup := hC.center_pGroup J hJ hJK
      center_ne := by
        intro hbot
        have hmem := mk_mem_center hdJ h.d_center
        rw [hbot, Subgroup.mem_bot] at hmem
        exact h.d_ne_one (congrArg Subtype.val hmem)
      c_pow := hc3'
      comm := hcg.map _
      g_primes := fun p hp hpd => h.g_primes p hp
        (hpd.trans ((orderOf_map_dvd _ _).trans (dvd_of_eq (Subgroup.orderOf_mk g hgN))))
      V_isPGroup := hV₁.map _
      U_le := Subgroup.map_mono hUV
      c_mem := Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hcV)
      g_mem := Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hgV)
      g_memU := Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hgU)
      U_comm := map_commutator_zpowers hUg
      U_ne := fun hbot => hne ((Subgroup.map_eq_bot_iff _).mp hbot)
      F_cent := commute_map_of_fixed hc3 hV₁ hcV hF
      outer_threes := h.outer_threes hC hJ hJK hcN
      inner_threes := h.inner_threes hC hJ hJK hcN hcJ hc3'
      cube := h.cube_field hC hJ hJK hcN hcJ
      primes := h.primes_field hC hJ hJK hcN
      rank5 := hrank5 }

theorem Res3Q.false_of_res3NoDatum {Q : Type} [Group Q] [Finite Q] {c d g : Q}
    {A B₀ K V₀ U : Subgroup Q} (hND : Res3NoDatum) (h : Res3Q c d g A B₀ K V₀ U)
    (hC : Res3QCompFacts c d A B₀ K)
    (hT28 : ∃ J : Subgroup Q, CFSG.IsComponent J ∧ J ≠ K ∧
      ¬ U ≤ Subgroup.centralizer (J : Set Q))
    (hrank5 : ∀ J : Subgroup Q, CFSG.IsComponent J → J ≠ K → ∀ E R : Subgroup ↥J,
      Nat.card E = 25 → (∀ x ∈ E, x ^ 5 = 1) → IsPGroup 2 R → R ≠ ⊥ →
      E ≤ Subgroup.normalizer (R : Set ↥J) → False) : False := by
  obtain ⟨J, hJ, hJK, hUJ⟩ := hT28
  obtain ⟨c', g', V', U', hdatum⟩ :=
    h.exists_res3Datum hC hJ hJK hUJ (hrank5 J hJ hJK)
  exact hND ↥J (h.fourHyp J hJ.1) hJ.1 c' g' V' U' hdatum

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
