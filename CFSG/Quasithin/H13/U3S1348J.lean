module

public import CFSG.Quasithin.H13.U3S1348I
public import CFSG.Quasithin.Vol2.Ch11SecD556A

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

theorem elemAbelian_sup_zpowers {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {A : Subgroup X} (hA : IsElemAbelian p A) {y : X} (hy : y ∉ A) (hyp : y ^ p = 1)
    (hyA : ∀ a ∈ A, a * y = y * a) :
    IsElemAbelian p (A ⊔ zpowers y) ∧ Nat.card ↥(A ⊔ zpowers y) = Nat.card A * p := by
  have hy1 : y ≠ 1 := fun h => hy (h ▸ one_mem A)
  have hoy : orderOf y = p := orderOf_eq_prime hyp hy1
  have hcomm : ∀ a ∈ A, ∀ b ∈ zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hyA a ha) k).eq
  have hinf : A ⊓ zpowers y = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ zpowers y) ∣ p := by
      rw [← hoy, ← Nat.card_zpowers]
      exact card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h | h
    · exact card_eq_one.1 h
    · exfalso
      have hle : zpowers y ≤ A ⊓ zpowers y := by
        refine (eq_of_le_of_card_ge inf_le_right ?_).ge
        rw [h, Nat.card_zpowers, hoy]
      exact hy (hle (mem_zpowers y)).1
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, card_bot, mul_one, Nat.card_zpowers, hoy] at hcard
  have hle : A ≤ normalizer ((zpowers y : Subgroup X) : Set X) := by
    intro a ha
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  have hdec : ∀ x ∈ A ⊔ zpowers y, ∃ a ∈ A, ∃ k : ℤ, x = a * y ^ k := by
    intro x hx
    have hx' : x ∈ ((A : Set X) * (zpowers y : Set X)) := by
      rw [← coe_mul_of_left_le_normalizer_right A _ hle]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact ⟨a, ha, k, rfl⟩
  have hAc := hA.1
  refine ⟨⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, hcard⟩
  · obtain ⟨a, ha, k, hk⟩ := hdec u u.2
    obtain ⟨b, hb, l, hl⟩ := hdec v v.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hk, hl]
    have hab : a * b = b * a := congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)
    have h1 : y ^ k * b = b * y ^ k := (hcomm b hb _ (zpow_mem_zpowers y k)).symm
    have h2 : a * y ^ l = y ^ l * a := hcomm a ha _ (zpow_mem_zpowers y l)
    calc a * y ^ k * (b * y ^ l) = a * (y ^ k * b) * y ^ l := by group
      _ = a * (b * y ^ k) * y ^ l := by rw [h1]
      _ = (a * b) * (y ^ k * y ^ l) := by group
      _ = (b * a) * (y ^ l * y ^ k) := by rw [hab, ← zpow_add, ← zpow_add, add_comm]
      _ = b * (a * y ^ l) * y ^ k := by group
      _ = b * (y ^ l * a) * y ^ k := by rw [h2]
      _ = b * y ^ l * (a * y ^ k) := by group
  · obtain ⟨a, ha, k, rfl⟩ := hdec x hx
    rw [(Commute.zpow_right (hyA a ha) k).mul_pow, hA.2 a ha, one_mul, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace S134Plus

variable {S : A6.Setting134 G T L V} {Lp : Subgroup G} (P : S134Plus S Lp)
include P

theorem exists_cube {τ : Perm (Fin 6)} (hτ : τ ∈ S14.C3) :
    ∃ c ∈ Lp, c ^ 3 = 1 ∧ ∃ hc : c ∈ normalizer (V : Set G), S.frame.ρ ⟨c, hc⟩ = τ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxL, hxρ⟩ := P.three τ hτ
  obtain ⟨-, -, -, h3⟩ := S14.c3_facts τ hτ
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  set y := x ^ 4 ^ a with hy
  have hym : y ^ m = 1 := by
    have h1 : (x ^ (4 ^ a)) ^ m = (x ^ (2 ^ a * m)) ^ (2 ^ a) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      ring
    have h2 : x ^ (2 ^ a * m) = 1 := by rw [← hnm, pow_orderOf_eq_one]
    rw [hy, h1, h2, one_pow]
  have hyρ : S.frame.ρ y = τ := by rw [hy, map_pow, hxρ, pow_four_pow_of_cube h3]
  have hyL : (y : G) ∈ Lp := by simpa [hy] using Lp.pow_mem hxL (4 ^ a)
  have hy3C : (y : G) ^ 3 ∈ Lp ⊓ centralizer (V : Set G) := by
    refine ⟨Lp.pow_mem hyL 3, ?_⟩
    have := (s134_rho_eq_one_iff S (y ^ 3)).1 (by rw [map_pow, hyρ, h3])
    simpa using this
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, P.cent hy3C⟩
  have hk' : ((y : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hm' : ((y : G) ^ 3) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have := congrArg Subtype.val hym
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    rw [this, one_pow]
  have hg := pow_gcd_eq_one.2 ⟨hm', hk'⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm)),
    pow_one] at hg
  exact ⟨y, hyL, hg, y.2, hyρ⟩

end S134Plus

theorem s134_rank_autI_le (S : A6.Setting134 G T L V) {z : G} {H VH : Subgroup G}
    (hHz : InHz T L V z H) (hred : IsTwoReducedIn H VH)
    (hC : H ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    {E : Subgroup (MulAut (IntMod VH hred.2.2.1))} (hEH : E ≤ autI hred.2.2.1 H)
    (hE : IsElemAbelian 3 E) {r : ℕ} (hr : Nat.card E = 3 ^ r) : r ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hO2H, -⟩ := s134_inHz_facts S hHz
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  set φ := convHom hred.2.2.1 H hHN with hφ
  have hrange : φ.range = autI hred.2.2.1 H := range_convHom _ H hHN
  have hker : ∀ x : ↥H, φ.rangeRestrict x = 1 → ∃ i : ℕ, x ^ 2 ^ i = 1 := by
    intro x hx
    have h1 : φ x = 1 := congrArg Subtype.val hx
    rw [hφ, convHom_apply, convI_eq_one_iff] at h1
    have hxO : (x : G) ∈ pCoreOf 2 H := hC ▸ mem_inf.2 ⟨x.2, h1⟩
    obtain ⟨i, hi⟩ := pCoreOf_isPGroup 2 H ⟨x, hxO⟩
    exact ⟨i, Subtype.ext (by simpa using congrArg Subtype.val hi)⟩
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ F : Subgroup G, F ≤ H → IsElemAbelian p F →
      ∀ k, Nat.card F = p ^ k → k ≤ 2 := fun p hp hp2 F hF hFab k hk =>
    Vol2.Ch11.SecD.le_two_of_elemAbelian S.fsu.qtke.2.2 hO2H (pCoreOf_isPGroup 2 H) hp hp2
      (hF.trans (le_normalizer_pCoreOf 2 H)) hFab hk
  have hEr : E ≤ φ.range := hrange ▸ hEH
  have hE' : IsElemAbelian 3 (E.subgroupOf φ.range) := by
    have hEc := hE.1
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := mul_comm (⟨((a : ↥φ.range) : MulAut (IntMod VH hred.2.2.1)), mem_subgroupOf.1 a.2⟩ :
        ↥E) ⟨((b : ↥φ.range) : MulAut (IntMod VH hred.2.2.1)), mem_subgroupOf.1 b.2⟩
      have h := congrArg Subtype.val this
      simpa using h
    · have h1 := hE.2 _ (mem_subgroupOf.1 hx)
      exact Subtype.ext (by simpa using h1)
  have hcard' : Nat.card ↥(E.subgroupOf φ.range) = 3 ^ r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEr).toEquiv, hr]
  exact le_two_of_elemAbelian_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective hker
    Nat.prime_three (by norm_num) (hrank 3 Nat.prime_three (by norm_num)) hE' hcard'

theorem s134_card_blocks_eq_one_of_C (S : A6.Setting134 G T L V) {Lp : Subgroup G}
    (P : S134Plus S Lp) {z : G}
    {H VH : Subgroup G} (hHz : InHz T L V z H) (hsolv : Group.IsSolvable ↥H)
    (hred : IsTwoReducedIn H VH) (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    (hC : H ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))}
    (B : BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 𝓘) (hne : 𝓘.Nonempty)
    (hcard : 𝓘.card ≤ 2) : 𝓘.card = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 1 ≤ 𝓘.card := Finset.card_pos.2 hne
  by_contra hne1
  have h2 : 𝓘.card = 2 := by omega
  obtain ⟨K₁, K₂, hK12, hI⟩ := Finset.card_eq_two.1 h2
  have hK₁ : K₁ ∈ 𝓘 := hI ▸ Finset.mem_insert_self _ _
  have hK₂ : K₂ ∈ 𝓘 := hI ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨c₁, hc₁K, hc₁⟩ := exists_orderOf_three_of_card_six (B.hb.card_eq K₁ (B.sub hK₁))
  obtain ⟨c₂, hc₂K, hc₂⟩ := exists_orderOf_three_of_card_six (B.hb.card_eq K₂ (B.sub hK₂))
  obtain ⟨hTsyl, hL1TH, -, -, -⟩ := s134_inHz_facts S hHz
  have hL1H : L₁Of L (fsuV1 T V) ≤ H := le_sup_left.trans hL1TH
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  have hIH : autI hred.2.2.1 (conjClosure (thompsonJ (r1Of T L V)) H) ≤ autI hred.2.2.1 H :=
    autI_mono _ (conjClosure_le fun h hh j hj => mul_mem (mul_mem hh
      ((((iSup₂_le fun _ hA => hA.1 : thompsonJ (r1Of T L V) ≤ r1Of T L V).trans
        (r1Of_le_T T L V)).trans hTsyl.1) hj)) (inv_mem hh))
  have hKI : ∀ K ∈ 𝓘, K ≤ ⨆ K' ∈ 𝓘, K' := fun K hK =>
    le_iSup₂_of_le (f := fun (K' : Subgroup (MulAut (IntMod VH hred.2.2.1))) (_ : K' ∈ 𝓘) => K')
      K hK le_rfl
  obtain ⟨c, hcL, hc3, hcNV, hcρ⟩ := P.exists_cube
    (inA4_cube_mem_C3 c012 c012_props.2.2 c012_props.2.1)
  have hcN : c ∈ normalizer (VH : Set G) := hHN (hL1H (P.le_L1 hcL))
  set d := convI hred.2.2.1 ⟨c, hcN⟩ with hd
  have hdH : d ∈ autI hred.2.2.1 H := convI_mem_autI _ (hL1H (P.le_L1 hcL)) hcN
  have hd3 : d ^ 3 = 1 := by
    rw [hd, ← map_pow]
    have : (⟨c, hcN⟩ : ↥(normalizer (VH : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hc1 : c ∉ centralizer (VH : Set G) := by
    intro hcC
    have hcO : c ∈ pCoreOf 2 H := hC ▸ mem_inf.2 ⟨hL1H (P.le_L1 hcL), hcC⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨c, hcO⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg : c ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨hc3, hk'⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at hg
    have h1 : (⟨c, hcNV⟩ : ↥(normalizer (V : Set G))) = 1 := Subtype.ext hg
    rw [h1, map_one] at hcρ
    exact absurd hcρ.symm (by decide)
  have hd1 : d ≠ 1 := fun h => hc1 ((convI_eq_one_iff _ _).1 h)
  have hd₁ := blocks_comm_of_pow_three B hcard hdH hd3 hK₁ hc₁K hc₁
  have hd₂ := blocks_comm_of_pow_three B hcard hdH hd3 hK₂ hc₂K hc₂
  have h12 : c₁ * c₂ = c₂ * c₁ := B.hb.comm K₁ (B.sub hK₁) K₂ (B.sub hK₂) hK12 c₁ hc₁K c₂ hc₂K
  have hc₁3 : c₁ ^ 3 = 1 := by rw [← hc₁]; exact pow_orderOf_eq_one c₁
  have hc₂3 : c₂ ^ 3 = 1 := by rw [← hc₂]; exact pow_orderOf_eq_one c₂
  have hbot : IsElemAbelian 3 (⊥ : Subgroup (MulAut (IntMod VH hred.2.2.1))) :=
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [(mem_bot).1 hx, one_pow]⟩
  have hc₁1 : c₁ ∉ (⊥ : Subgroup (MulAut (IntMod VH hred.2.2.1))) := fun h => by
    rw [(mem_bot).1 h, orderOf_one] at hc₁
    omega
  obtain ⟨hA₁, hA₁c⟩ := elemAbelian_sup_zpowers hbot hc₁1 hc₁3 (fun a ha => by
    rw [(mem_bot).1 ha, one_mul, mul_one])
  set A₁ := (⊥ : Subgroup (MulAut (IntMod VH hred.2.2.1))) ⊔ zpowers c₁ with hA₁def
  have hA₁K : A₁ ≤ K₁ := sup_le bot_le (zpowers_le.2 hc₁K)
  have hc₂A : c₂ ∉ A₁ := by
    intro h
    have hc2 : c₂ ∈ K₁ ⊓ K₂ := ⟨hA₁K h, hc₂K⟩
    rw [B.inf_eq_bot hK₁ hK₂ hK12, mem_bot] at hc2
    rw [hc2, orderOf_one] at hc₂
    omega
  have hcomm₂ : ∀ a ∈ A₁, a * c₂ = c₂ * a := by
    have hle : A₁ ≤ centralizer ({c₂} : Set (MulAut (IntMod VH hred.2.2.1))) :=
      sup_le bot_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 h12))
    exact fun a ha => mem_centralizer_singleton_iff.1 (hle ha)
  obtain ⟨hA₂, hA₂c⟩ := elemAbelian_sup_zpowers hA₁ hc₂A hc₂3 hcomm₂
  set A₂ := A₁ ⊔ zpowers c₂ with hA₂def
  have hA₂I : A₂ ≤ ⨆ K ∈ 𝓘, K :=
    sup_le (hA₁K.trans (hKI K₁ hK₁)) (zpowers_le.2 (hKI K₂ hK₂ hc₂K))
  have hdA : d ∉ A₂ := by
    intro h
    have hC' := s134_odd_trivial S P hHz hsolv hred hcR hJ B hcard hcL hcN
      (hA₂I h) ⟨3, by decide, hc3⟩
    exact hc1 hC'
  have hcomm₃ : ∀ a ∈ A₂, a * d = d * a := by
    have hle : A₂ ≤ centralizer ({d} : Set (MulAut (IntMod VH hred.2.2.1))) := by
      refine sup_le (sup_le bot_le (zpowers_le.2 ?_)) (zpowers_le.2 ?_)
      · exact mem_centralizer_singleton_iff.2 hd₁.symm
      · exact mem_centralizer_singleton_iff.2 hd₂.symm
    exact fun a ha => mem_centralizer_singleton_iff.1 (hle ha)
  obtain ⟨hA₃, hA₃c⟩ := elemAbelian_sup_zpowers hA₂ hdA hd3 hcomm₃
  have hA₃H : A₂ ⊔ zpowers d ≤ autI hred.2.2.1 H :=
    sup_le (hA₂I.trans (B.eq ▸ hIH)) (zpowers_le.2 hdH)
  have hcard3 : Nat.card ↥(A₂ ⊔ zpowers d) = 3 ^ 3 := by
    rw [hA₃c, hA₂c, hA₁c, card_bot]
    norm_num
  have := s134_rank_autI_le S hHz hred hC hA₃H hA₃ hcard3
  omega

end CFSG.Quasithin.H13.U3
