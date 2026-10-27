module

public import CFSG.Walter.W67.Section6.Core64B
public import CFSG.Walter.W67.Section5.P56K3c
public import CFSG.Walter.W67.Section6.Core62G

public section

namespace CFSG.Walter.W67

namespace Sec6

variable {G : Type} [Group G] [Finite G] {s : Std G}

namespace Sol

variable (σ : Sol s)
include σ

theorem card_E_eq :
    Nat.card s.fr.E = 7 ^ (Nat.card s.H).factorization 7 := by
  rw [σ.factorization_H, pow_one, σ.E7]

theorem exists_conj_E
    {Y : Subgroup G} (hYH : Y ≤ s.H) (hY : Nat.card Y = 7) :
    ∃ c ∈ s.H, s.fr.E = cj c Y := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_conj_of_sylowIn hYH s.fr.E_le_H
    (by rw [hY, σ.factorization_H, pow_one]) σ.card_E_eq

theorem card_le_of_le_H
    {Y : Subgroup G} (hYH : Y ≤ s.H) (hY : IsPGroup 7 Y) :
    Nat.card Y ≤ 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  have h1 : 7 ^ k ∣ Nat.card s.H := hk ▸ Subgroup.card_dvd_of_le hYH
  have h2 := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').mp h1
  rw [σ.factorization_H] at h2
  rw [hk]
  calc 7 ^ k ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) h2
    _ = 7 := pow_one 7

theorem not_inv_of_mem_normalizer_E
    {z t : G} (hz : z ∈ Subgroup.normalizer (s.fr.E : Set G))
    (hz1 : z ≠ 1) {k : ℕ} (hzk : z ^ 7 ^ k = 1) (ht : t ∈ Subgroup.normalizer (s.fr.E : Set G))
    (htz : t * z * t⁻¹ = z⁻¹) (ht7 : Nat.Coprime (orderOf t) 7) : False := by
  have htL := σ.mem_L_of_coprime ht ht7
  obtain ⟨l, hl, e, he, rfl, hle⟩ := decomp hz
  have hte : t * e * t⁻¹ = e := by
    have hc := Subgroup.mem_centralizer_iff.mp (L_le_centralizer s le_rfl s.E_ne_bot htL) e he
    rw [← hc]
    group
  have h1 : t * l * t⁻¹ * e = l⁻¹ * e⁻¹ := by
    calc t * l * t⁻¹ * e = t * l * t⁻¹ * (t * e * t⁻¹) := by rw [hte]
      _ = t * (l * e) * t⁻¹ := by group
      _ = (l * e)⁻¹ := htz
      _ = (e * l)⁻¹ := by rw [hle]
      _ = l⁻¹ * e⁻¹ := by group
  have h2 : e * e = (l * (t * l * t⁻¹))⁻¹ := by
    have : t * l * t⁻¹ = l⁻¹ * e⁻¹ * e⁻¹ := by
      calc t * l * t⁻¹ = t * l * t⁻¹ * e * e⁻¹ := by group
        _ = l⁻¹ * e⁻¹ * e⁻¹ := by rw [h1]
    rw [this]
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : e * e ∈ s.L s.fr.E ⊓ s.fr.E := by
    refine Subgroup.mem_inf.mpr ⟨?_, s.fr.E.mul_mem he he⟩
    rw [h2]
    exact (s.L s.fr.E).inv_mem ((s.L s.fr.E).mul_mem hl
      ((s.L s.fr.E).mul_mem ((s.L s.fr.E).mul_mem htL hl) ((s.L s.fr.E).inv_mem htL)))
  rw [σ.L_inf_E, Subgroup.mem_bot] at hmem
  have he1 : e = 1 := by
    have he7 : e ^ 7 = 1 := by
      have := Subgroup.orderOf_dvd_natCard _ he
      rw [σ.E7] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have := pow_gcd_eq_one.mpr ⟨he7, (show e ^ 2 = 1 by rw [pow_two, hmem])⟩
    norm_num at this
    exact this
  subst he1
  rw [mul_one] at hz1 hzk htz
  have hl7 : l ^ 7 = 1 := by
    have h168 := Subgroup.orderOf_dvd_natCard _ hl
    rw [σ.L168.card_L] at h168
    have h7k : orderOf l ∣ 7 ^ k := orderOf_dvd_of_pow_eq_one hzk
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow (by norm_num)).mp h7k
    rw [hj'] at h168
    have hj1 : j ≤ 1 := by
      by_contra hj1
      have : 7 ^ 2 ∣ 7 ^ j := pow_dvd_pow 7 (by omega)
      have := this.trans h168
      norm_num at this
    have : orderOf l ∣ 7 := by
      rw [hj']
      exact (pow_dvd_pow 7 hj1).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.mp this
  exact σ.L168.not_inv hl hz1 hl7 htL htz

theorem not_comm_of_inv
    {x : G} (hx7 : orderOf x = 7) (hJx : s.J * x * s.J⁻¹ = x⁻¹)
    {u : G} (hu : u * u = 1) (hu1 : u ≠ 1) (hux : u * x = x * u) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set N := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) with hNdef
  have hxr : IsPGroup 7 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx7, pow_one])
  have huC : u ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute x u from hux.symm) i).eq
  have huN : u ∈ N := Subgroup.centralizer_le_normalizer _ huC
  have hJN : s.J ∈ N := by
    apply Sec53.mem_normalizer_of_conj_le
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hJx]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) i
  have hu2 : IsPGroup 2 (Subgroup.zpowers (⟨u, huN⟩ : N)) :=
    Huppert.isPGroup_zpowers (k := 1) (Subtype.ext (by
      change u ^ 2 ^ 1 = 1
      rw [pow_one, pow_two, hu]))
  have hJ2 : IsPGroup 2 (Subgroup.zpowers (⟨s.J, hJN⟩ : N)) :=
    Huppert.isPGroup_zpowers (k := 1) (Subtype.ext (by
      change s.J ^ 2 ^ 1 = 1
      rw [pow_one, pow_two, s.J_mul_J]))
  obtain ⟨T, hT⟩ := hu2.exists_le_sylow
  obtain ⟨T', hT'⟩ := hJ2.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N T T'
  have hun : n * ⟨u, huN⟩ * n⁻¹ ∈ (T' : Subgroup N) := by
    rw [← hn, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj n)⁻¹ • (n * ⟨u, huN⟩ * n⁻¹) = ⟨u, huN⟩ := by
      rw [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply]
      group
    rw [this]
    exact hT (Subgroup.mem_zpowers _)
  have hJT : (⟨s.J, hJN⟩ : N) ∈ (T' : Subgroup N) := hT' (Subgroup.mem_zpowers _)
  set T'' := (T' : Subgroup N).map N.subtype with hT''
  have hT''2 : IsPGroup 2 T'' := T'.isPGroup'.map _
  set u' : G := n * u * (n : G)⁻¹ with hu'
  have hu'T : u' ∈ T'' := ⟨_, hun, by simp [hu']⟩
  have hJT'' : s.J ∈ T'' := ⟨_, hJT, rfl⟩
  have hJu' := (two_facts s hT''2 hJT'' hu'T).1
  have hu'2 : u' * u' = 1 := by
    rw [hu']
    calc (n : G) * u * (n : G)⁻¹ * ((n : G) * u * (n : G)⁻¹) = n * (u * u) * (n : G)⁻¹ := by group
      _ = 1 := by rw [hu]; group
  have hu'o : orderOf u' = 2 := by
    apply orderOf_eq_prime (by rw [pow_two]; exact hu'2)
    intro h1
    apply hu1
    have : u = (n : G)⁻¹ * u' * n := by rw [hu']; group
    rw [this, h1]
    group
  have hxu' : x ∈ Subgroup.centralizer ({u'} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hn' : (n : G)⁻¹ * x * n ∈ Subgroup.zpowers x := by
      have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem n.2) x).mp (Subgroup.mem_zpowers x)
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp huC _ hn'
    calc x * u' = n * (((n : G)⁻¹ * x * n) * u) * (n : G)⁻¹ := by rw [hu']; group
      _ = n * (u * ((n : G)⁻¹ * x * n)) * (n : G)⁻¹ := by rw [hc]
      _ = u' * x := by rw [hu']; group
  have hJC : s.J ∈ Subgroup.centralizer ({u'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hJu'
  have hx1 := (σ.invFacts).no_real u' x s.J hu'o hxu' hJC s.J_mul_J hJx hxr
  rw [hx1, orderOf_one] at hx7
  norm_num at hx7

theorem inf_centralizer_ne_bot
    {S : Subgroup G}
    (hScard : Nat.card S = 7 ^ (Nat.card G).factorization 7)
    (hJS : s.J ∈ Subgroup.normalizer (S : Set G)) :
    S ⊓ Subgroup.centralizer ({s.J} : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro hbot
  have hinv := inv_of_fixedPointFree s.J_mul_J hJS (fun q hq hqJ => by
    have : q ∈ S ⊓ Subgroup.centralizer ({s.J} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc q * s.J = s.J * q * s.J⁻¹ * s.J := by rw [hqJ]
        _ = s.J * q := by group
    rwa [hbot, Subgroup.mem_bot] at this)
  obtain ⟨g, hg, hgen, hgo⟩ := σ.exists_gen
  have hE7 : IsPGroup 7 s.fr.E := IsPGroup.of_card (n := 1) (by rw [σ.E7, pow_one])
  obtain ⟨P, hP⟩ := hE7.exists_le_sylow
  set PS : Sylow 7 G := Sylow.ofCard S hScard
  have hPS : (PS : Subgroup G) = S := Sylow.coe_ofCard _ _
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P PS
  have hcg : c * g * c⁻¹ ∈ S := by
    rw [← hPS, ← hc, Sylow.coe_subgroup_smul]
    exact ⟨g, hP hg, rfl⟩
  have h1 := hinv _ hcg
  set t := c⁻¹ * s.J * c with ht
  have htg : t * g * t⁻¹ = g⁻¹ := by
    have : t * g * t⁻¹ = c⁻¹ * (s.J * (c * g * c⁻¹) * s.J⁻¹) * c := by rw [ht]; group
    rw [this, h1]
    group
  have htN : t ∈ Subgroup.normalizer (s.fr.E : Set G) := by
    apply Sec53.mem_normalizer_of_conj_le
    intro z hz
    rw [← hgen] at hz ⊢
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, htg]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)) i
  rw [normalizer_eq_centralizer] at htN
  have h2 : t * g * t⁻¹ = g := by
    rw [← (Subgroup.mem_centralizer_iff.mp htN g hg)]
    group
  rw [htg] at h2
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 2 [← h2]
    exact mul_inv_cancel g
  have := orderOf_dvd_of_pow_eq_one hg2
  rw [hgo] at this
  norm_num at this

theorem no_real_global :
    ∀ x y : G, orderOf x = 7 → y * x * y⁻¹ ≠ x⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro x y hx7 hyx
  obtain ⟨t, ⟨k, htk⟩, -, htx⟩ := Sec64.exists_two_pow_inv hyx
  have ht2 : t * t = 1 := (two_facts s (Huppert.isPGroup_zpowers htk) (Subgroup.mem_zpowers t)
    (Subgroup.mem_zpowers t)).2
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx7
    norm_num at hx7
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hx1
    have h : x = x⁻¹ := by simpa using htx
    have hx2 : x ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [h]; exact mul_inv_cancel x
    have := orderOf_dvd_of_pow_eq_one hx2
    rw [hx7] at this
    norm_num at this
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_J s hto)
  set x' := c * x * c⁻¹ with hx'
  have hx'7 : orderOf x' = 7 := by rw [hx', orderOf_conj_mul, hx7]
  have hJx' : s.J * x' * s.J⁻¹ = x'⁻¹ := by
    rw [← hc, hx']
    calc c * t * c⁻¹ * (c * x * c⁻¹) * (c * t * c⁻¹)⁻¹ = c * (t * x * t⁻¹) * c⁻¹ := by group
      _ = (c * x * c⁻¹)⁻¹ := by rw [htx]; group
  have hx'1 : x' ≠ 1 := by
    rintro h
    rw [h, orderOf_one] at hx'7
    norm_num at hx'7
  have hxr : IsPGroup 7 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'7, pow_one])
  have hJN : s.J ∈ Subgroup.normalizer ((Subgroup.zpowers x' : Subgroup G) : Set G) := by
    apply Sec53.mem_normalizer_of_conj_le
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hJx']
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x')) i
  have hnc : ∀ u ∈ Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G),
      u * u = 1 → u = 1 := by
    intro u hu hu2
    by_contra hu1
    exact σ.not_comm_of_inv hx'7 hJx' hu2 hu1
      (Subgroup.mem_centralizer_iff.mp hu x' (Subgroup.mem_zpowers x')).symm
  obtain ⟨S, hxS, hSr, hScard, hJS⟩ :=
    σ.invFacts.exists_sylow (by norm_num) s.orderOf_J hxr hJN hnc
  have hCne := σ.inf_centralizer_ne_bot hScard hJS
  set C := S ⊓ Subgroup.centralizer ({s.J} : Set G) with hCdef
  have hCH : C ≤ s.H := inf_le_right
  have hCr : IsPGroup 7 C := hSr.to_le inf_le_left
  have hCcard : Nat.card C = 7 := by
    have hle := σ.card_le_of_le_H hCH hCr
    obtain ⟨j, hj⟩ := hCr.exists_card_eq
    have hj0 : j ≠ 0 := by
      intro hj0
      rw [hj0, pow_zero] at hj
      exact hCne (Subgroup.eq_bot_of_card_eq C hj)
    rw [hj] at hle ⊢
    have : j ≤ 1 := by
      by_contra hj1
      have : 7 ^ 2 ≤ 7 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : j = 1 := by omega
    rw [this, pow_one]
  obtain ⟨d, hdH, hdE⟩ := σ.exists_conj_E hCH hCcard
  set S' := cj d S with hS'
  have hdJ : d * s.J = s.J * d := s.commute_J hdH
  have hES' : s.fr.E ≤ S' := by
    rw [hdE]
    exact cj_mono inf_le_left
  have hdJinv : d⁻¹ * s.J * d = s.J := by
    calc d⁻¹ * s.J * d = d⁻¹ * (s.J * d) := by group
      _ = d⁻¹ * (d * s.J) := by rw [hdJ]
      _ = s.J := by group
  have hJS' : s.J ∈ Subgroup.normalizer (S' : Set G) := by
    rw [hS', ← cj_normalizer, mem_cj, hdJinv]
    exact hJS
  set x'' := d * x' * d⁻¹ with hx''
  have hx''S' : x'' ∈ S' := conj_mem_cj (hxS (Subgroup.mem_zpowers x'))
  have hJx'' : s.J * x'' * s.J⁻¹ = x''⁻¹ := by
    have hJd : s.J = d * s.J * d⁻¹ := by
      calc s.J = d * (d⁻¹ * s.J * d) * d⁻¹ := by group
        _ = d * s.J * d⁻¹ := by rw [hdJinv]
    calc s.J * x'' * s.J⁻¹ = (d * s.J * d⁻¹) * x'' * (d * s.J * d⁻¹)⁻¹ := by rw [← hJd]
      _ = d * (s.J * x' * s.J⁻¹) * d⁻¹ := by rw [hx'']; group
      _ = x''⁻¹ := by rw [hJx', hx'']; group
  have hx''1 : x'' ≠ 1 := by
    rw [hx'']
    intro h
    apply hx'1
    calc x' = d⁻¹ * (d * x' * d⁻¹) * d := by group
      _ = 1 := by rw [h]; group
  have hS'r : IsPGroup 7 S' := by
    rw [hS']
    exact hSr.map _
  have hx''E : x'' ∉ s.fr.E := by
    intro hE
    have hc := s.commute_J (s.fr.E_le_H hE)
    have : x'' = x''⁻¹ := by
      calc x'' = s.J * x'' * s.J⁻¹ := by rw [← hc]; group
        _ = x''⁻¹ := hJx''
    have hx2 : x'' ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [this]; exact mul_inv_cancel _
    have h7 : orderOf x'' = 7 := by rw [hx'', orderOf_conj_mul, hx'7]
    have := orderOf_dvd_of_pow_eq_one hx2
    rw [h7] at this
    norm_num at this
  have hlt : s.fr.E < S' := lt_of_le_of_ne hES' (fun h => hx''E (h ▸ hx''S'))
  obtain ⟨w, hwS', hwE, hwN⟩ := Sec56.exists_mem_normalizer_of_lt hS'r hlt
  have hJw : s.J * w * s.J⁻¹ ≠ w := by
    intro hJw
    have hwH : w ∈ s.H := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * s.J = s.J * w * s.J⁻¹ * s.J := by rw [hJw]
        _ = s.J * w := by group
    set Y := S' ⊓ s.H with hY
    have hYr : IsPGroup 7 Y := hS'r.to_le inf_le_left
    have hEY : s.fr.E ≤ Y := le_inf hES' s.fr.E_le_H
    have hwY : w ∈ Y := Subgroup.mem_inf.mpr ⟨hwS', hwH⟩
    have hle := σ.card_le_of_le_H (inf_le_right : Y ≤ s.H) hYr
    have heq : s.fr.E = Y := Subgroup.eq_of_le_of_card_ge hEY (by rw [σ.E7]; exact hle)
    exact hwE (heq ▸ hwY)
  have hJN' : s.J ∈ Subgroup.normalizer (s.fr.E : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun e he =>
      (s.commute_J (s.fr.E_le_H he)))
  obtain ⟨hzY, hz1, hJz⟩ := Sec64.inv_of_not_comm (Q := S' ⊓ Subgroup.normalizer
      (s.fr.E : Set G)) s.J_mul_J
    (Sec54.mem_normalizer_inf hJS' (Subgroup.le_normalizer hJN'))
    (Subgroup.mem_inf.mpr ⟨hwS', hwN⟩) hJw
  obtain ⟨hzS', hzN⟩ := Subgroup.mem_inf.mp hzY
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hS'r) ⟨_, hzS'⟩
  rw [Subgroup.orderOf_mk] at hm
  refine σ.not_inv_of_mem_normalizer_E hzN hz1 (k := m) (by rw [← hm, pow_orderOf_eq_one])
    hJN' hJz ?_
  rw [s.orderOf_J]
  norm_num

end Sol

end Sec6

end CFSG.Walter.W67
