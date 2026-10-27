module

public import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarNorm
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarCoords
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A L K : Subgroup G} {c d : G}

omit [Finite G] in
theorem isPGroup_zpowers_of_pow {y : G} {k : ℕ} (hy : y ^ 3 ^ k = 1) :
    IsPGroup 3 (Subgroup.zpowers y) := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy)
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

theorem commute_of_pow (H : Base A c L d K) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {k : ℕ} (hyk : y ^ 3 ^ k = 1) : y * c = c * y ∧ y * d = d * y := by
  obtain ⟨P, hP, hyP⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr hy)
    (isPGroup_zpowers_of_pow hyk)
  have hB := H.le_center P hP
  have hPc := le_centralizer_of_mem_center_map
    (hB (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))
  have hPd := le_centralizer_of_mem_center_map
    (hB (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
  have hyP' := hyP (Subgroup.mem_zpowers y)
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mp (hPc hyP'),
    Subgroup.mem_centralizer_singleton_iff.mp (hPd hyP')⟩

theorem conj_mem_zpowers_of_pow {S T : Subgroup G} (hTD : TData A c L d S T) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {k : ℕ} (hyk : y ^ 3 ^ k = 1) {e : G} (he : e ∈ A) :
    y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := by
  obtain ⟨P, hP, hyP⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr hy)
    (isPGroup_zpowers_of_pow hyk)
  obtain ⟨m, hm, hPm⟩ := exists_conj_of_isSylowOf hTD.isSylowOf hP
  have hyT : y ∈ T.map (MulAut.conj m).toMonoidHom := hPm ▸ hyP (Subgroup.mem_zpowers y)
  obtain ⟨τ, hτ, hτy⟩ := hyT
  have hτy' : m * τ * m⁻¹ = y := hτy
  have he' : m⁻¹ * e * m ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm.1) e).mp he
    simpa using this
  have h1 := hTD.conj_mem τ hτ _ he'
  have h2 : y * e * y⁻¹ * e⁻¹ =
      m * (τ * (m⁻¹ * e * m) * τ⁻¹ * (m⁻¹ * e * m)⁻¹) * m⁻¹ := by
    rw [← hτy']
    group
  rw [h2]
  exact (Subgroup.mem_normalizer_iff.mp hm.2 _).mp h1

theorem le_normalizer_B {S T : Subgroup G} (hTD : TData A c L d S T) :
    T ≤ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
  intro τ hτ
  refine Subgroup.mem_normalizer_fintype fun b hb => ?_
  have hb' := Subgroup.mem_centralizer_iff.mp (Base.B_le_centralizer hTD hb) τ hτ
  rw [SetLike.mem_coe, show τ * b * τ⁻¹ = b by rw [hb', mul_inv_cancel_right]]
  exact hb

theorem isSylowOf_centralizer_normalizer
    (H : Base A c L d K) {S T : Subgroup G}
    (hSD : SylowData A L d K S) (hTD : TData A c L d S T) :
    IsSylowOf 3 T (Subgroup.centralizer ({d} : Set G) ⊓
      Subgroup.normalizer ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : IsPGroup 3 T := hTD.isSylowOf.isPGroup
  refine isSylowOf_of_maximal (le_inf hTD.le_d (le_normalizer_B hTD)) hTp
    fun Q hTQ hQN hQ => ?_
  by_contra hne
  have hlt : T.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    apply le_antisymm _ hTQ
    intro x hx
    have : (⟨x, hx⟩ : Q) ∈ T.subgroupOf Q := htop ▸ Subgroup.mem_top _
    exact this
  have : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨y, hyN, hyT⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  have hyNT : (y : G) ∈ Subgroup.normalizer (T : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    have := (Subgroup.mem_normalizer_iff.mp hyN ⟨t, hTQ ht⟩).mp (Subgroup.mem_subgroupOf.mpr ht)
    exact Subgroup.mem_subgroupOf.mp this
  have hyd : (y : G) * d = d * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (hQN y.2).1
  obtain ⟨k, hk⟩ := hQ y
  have hyk : (y : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hyc := H.commute_c_of_pow hSD hTD hyNT hyd hyk
  have hY3 := isPGroup_zpowers_of_pow hyk
  have hsup : IsPGroup 3 ↥(T ⊔ Subgroup.zpowers (y : G)) :=
    hTp.to_sup_of_normal_left' hY3 (Subgroup.zpowers_le.mpr hyNT)
  have hle : T ⊔ Subgroup.zpowers (y : G) ≤
      Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) :=
    sup_le (le_inf hTD.le_c hTD.le_d) (Subgroup.zpowers_le.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyc,
        Subgroup.mem_centralizer_singleton_iff.mpr hyd⟩)
  have heq := hTD.isSylowOf_cd.eq_of_le le_sup_left hle hsup
  apply hyT
  have : (y : G) ∈ T := heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (y : G))
  exact Subgroup.mem_subgroupOf.mpr this

theorem commute_c_of_mem
    (H : Base A c L d K) {S T : Subgroup G} (hSD : SylowData A L d K S)
    (hTD : TData A c L d S T) {y : G}
    (hy : y ∈ Subgroup.centralizer ({d} : Set G) ⊓
      Subgroup.normalizer ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G))
    {k : ℕ} (hyk : y ^ 3 ^ k = 1) : y * c = c * y := by
  have hTsyl := isSylowOf_centralizer_normalizer H hSD hTD
  obtain ⟨P, hP, hyP⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr hy)
    (isPGroup_zpowers_of_pow hyk)
  obtain ⟨m, hm, hPm⟩ := exists_conj_of_isSylowOf hTsyl hP
  have hyT : y ∈ T.map (MulAut.conj m).toMonoidHom := hPm ▸ hyP (Subgroup.mem_zpowers y)
  obtain ⟨τ, hτ, hτy⟩ := hyT
  have hτy' : m * τ * m⁻¹ = y := hτy
  have hcB : m⁻¹ * c * m ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm.2) c).mp
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    simpa using this
  have hτc := Subgroup.mem_centralizer_iff.mp (Base.B_le_centralizer hTD hcB) τ hτ
  calc y * c = m * (τ * (m⁻¹ * c * m)) * τ⁻¹ * m⁻¹ * y := by rw [← hτy']; group
    _ = m * ((m⁻¹ * c * m) * τ) * τ⁻¹ * m⁻¹ * y := by rw [hτc]
    _ = c * y := by group

theorem false_of_conj_eq_mul
    (H : Base A c L d K) {S T : Subgroup G} (hSD : SylowData A L d K S)
    (hTD : TData A c L d S T) {g δ : G} (hgd : g * d = d * g)
    (hgB : g ∈ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G))
    (hδ : δ ∈ Subgroup.zpowers d) (hδ1 : δ ≠ 1) (hgc : g * c * g⁻¹ = c * δ) : False := by
  have hgδ : g * δ = δ * g := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    exact (Commute.zpow_right (show Commute g d from hgd) j).eq
  have hpow : ∀ n : ℕ, g ^ n * c * (g ^ n)⁻¹ = c * δ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hgδn : g * δ ^ n * g⁻¹ = δ ^ n := by
        rw [(Commute.pow_right (show Commute g δ from hgδ) n).eq, mul_inv_cancel_right]
      calc g ^ (n + 1) * c * (g ^ (n + 1))⁻¹ = g * (g ^ n * c * (g ^ n)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * c * g⁻¹ * (g * δ ^ n * g⁻¹) := by rw [ih]; group
        _ = c * δ ^ (n + 1) := by rw [hgc, hgδn, pow_succ', mul_assoc]
  obtain ⟨e, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3
    (by norm_num)
  have hy3 : (g ^ m) ^ 3 ^ e = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hyd : g ^ m ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Commute.pow_left (show Commute g d from hgd) m).eq
  have hyB := pow_mem hgB m
  have hyc := commute_c_of_mem H hSD hTD ⟨hyd, hyB⟩ hy3
  have hδm : δ ^ m = 1 := by
    have h1 := hpow m
    rw [show g ^ m * c * (g ^ m)⁻¹ = c by rw [hyc, mul_inv_cancel_right]] at h1
    have h2 : c * δ ^ m = c * 1 := by rw [mul_one, ← h1]
    exact mul_left_cancel h2
  have hδ3 : δ ^ 3 = 1 := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, H.d_pow, one_zpow]
  apply hδ1
  have h1 : orderOf δ ∣ Nat.gcd 3 m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hδ3) (orderOf_dvd_of_pow_eq_one hδm)
  have hcop : Nat.gcd 3 m = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem mem_normalizer_B {g : G}
    (hc : g * c * g⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (hd : g * d * g⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    g ∈ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
  set B := Subgroup.zpowers c ⊔ Subgroup.zpowers d with hB
  have hle : B ≤ B.comap (MulAut.conj g).toMonoidHom :=
    sup_le (Subgroup.zpowers_le.mpr hc) (Subgroup.zpowers_le.mpr hd)
  exact Subgroup.mem_normalizer_fintype fun b hb => hle hb

theorem zpowers_sup_eq_of_mem (H : Base A c L d K) {a : G} (haA : a ∈ A)
    (haB : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) (had : a ∉ Subgroup.zpowers d) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers d = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  have ha3 : a ^ 3 = 1 := H.data.isElemAbelian.2 a haA
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤
      Subgroup.zpowers c ⊔ Subgroup.zpowers d :=
    sup_le (Subgroup.zpowers_le.mpr haB) le_sup_right
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers d, x * y = y * x := by
    intro x hx y hy
    exact H.data.commute ((Subgroup.zpowers_le.mpr haA) hx) ((Subgroup.zpowers_le.mpr H.mem_A) hy)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [zpowers_inf_eq_bot ha3 had, Subgroup.card_bot, mul_one,
    card_zpowers_of_pow_three ha3 (fun h => had (h ▸ one_mem _)),
    card_zpowers_of_pow_three H.d_pow H.ne_one] at hcard
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, Base.card_B H]

theorem false_of_inverts
    (H : Base A c L d K) {S T : Subgroup G} (hSD : SylowData A L d K S)
    (hTD : TData A c L d S T) {a : G} (haA : a ∈ A)
    (haB : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) (hac : a ∉ Subgroup.zpowers c)
    (had : a ∉ Subgroup.zpowers d) {s : G} (hsa : s * a = a * s) (hsd : s * d * s⁻¹ = d⁻¹) :
    False := by
  have ha3 : a ^ 3 = 1 := H.data.isElemAbelian.2 a haA
  have hd3 := H.d_pow
  have hc3 := H.c_pow
  obtain ⟨t, htL, htd⟩ := H.exists_mem_L_conj_eq_inv
  have htc : t * c = c * t := H.comm_L htL
  have hadB := zpowers_sup_eq_of_mem H haA haB had
  have haC : a ∈ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact H.data.commute ((Subgroup.zpowers_le.mpr H.mem_A) hx) haA
  have hcmem : c ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
    rw [hadB]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  obtain ⟨k, e, he, hce⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup haC hcmem
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [mul_one] at hce
    apply hac
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers a :=
      Subgroup.zpowers_le.mpr (hce ▸ Subgroup.zpow_mem_zpowers a k)
    have heq : Subgroup.zpowers c = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [card_zpowers_of_pow_three ha3 (fun h => had (h ▸ one_mem _)), H.data.card_zpowers])
    exact heq ▸ Subgroup.mem_zpowers a
  have hinv : ∀ {u : G}, u * d * u⁻¹ = d⁻¹ → ∀ δ ∈ Subgroup.zpowers d, u * δ * u⁻¹ = δ⁻¹ := by
    intro u hu δ hδ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    rw [← conj_zpow, hu, inv_zpow]
  have hsak : s * a ^ k * s⁻¹ = a ^ k := by
    rw [← conj_zpow, show s * a * s⁻¹ = a by rw [hsa, mul_inv_cancel_right]]
  have hsc : s * c * s⁻¹ = c * (e⁻¹ * e⁻¹) := by
    calc s * c * s⁻¹ = (s * a ^ k * s⁻¹) * (s * e * s⁻¹) := by rw [hce]; group
      _ = a ^ k * e⁻¹ := by rw [hsak, hinv hsd e he]
      _ = c * (e⁻¹ * e⁻¹) := by rw [hce]; group
  set g := t * s with hg
  have he' : e⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := mul_mem (inv_mem he) (inv_mem he)
  have hgc : g * c * g⁻¹ = c * (e * e) := by
    have htc' : t * c * t⁻¹ = c := by rw [htc, mul_inv_cancel_right]
    have hte := hinv htd _ he'
    calc g * c * g⁻¹ = t * (s * c * s⁻¹) * t⁻¹ := by rw [hg]; group
      _ = (t * c * t⁻¹) * (t * (e⁻¹ * e⁻¹) * t⁻¹) := by rw [hsc]; group
      _ = c * (e * e) := by rw [htc', hte, mul_inv_rev, inv_inv]
  have hgd : g * d * g⁻¹ = d := by
    calc g * d * g⁻¹ = t * (s * d * s⁻¹) * t⁻¹ := by rw [hg]; group
      _ = (t * d * t⁻¹)⁻¹ := by rw [hsd]; group
      _ = d := by rw [htd, inv_inv]
  have hee : e * e ∈ Subgroup.zpowers d := mul_mem he he
  have hee1 : e * e ≠ 1 := by
    intro h
    have he3 : e ^ 3 = 1 := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
    apply he1
    calc e = e ^ 3 * (e * e)⁻¹ := by group
      _ = 1 := by rw [he3, h]; group
  refine false_of_conj_eq_mul H hSD hTD (g := g) ?_ ?_ hee hee1 hgc
  · calc g * d = g * d * g⁻¹ * g := by group
      _ = d * g := by rw [hgd]
  · refine mem_normalizer_B ?_ ?_
    · rw [hgc]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
        (Subgroup.mem_sup_right hee)
    · rw [hgd]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)

end CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail
