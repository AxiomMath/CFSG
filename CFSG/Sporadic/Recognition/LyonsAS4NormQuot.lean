module

public import CFSG.Sporadic.Recognition.LyonsAS4Aut
public import CFSG.Sporadic.Recognition.LyonsAS4Quot
public import CFSG.Sporadic.Recognition.LyonsAS4PermAut
public import CFSG.Sporadic.Recognition.McLASInvolutions
public import CFSG.Sporadic.Recognition.McLCentralizer

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.GH74.GLS.Stage12

section Generic

variable {K : Type*} [Group K]

theorem eq_of_zpow_eq_inv_mul {x t c : K} (hx : x ^ 3 = 1) (hx1 : x ≠ 1) (ht : t ^ 2 = 1)
    (hc : c ^ 2 = 1) (htx : t * x = x * t) {k : ℤ} (hk : x ^ k = c⁻¹ * t) : c = t := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hc])
  have htk : t * x ^ k = x ^ k * t := (Commute.zpow_right (show Commute t x from htx) k).eq
  rw [hci] at hk
  have h1 : t * (c * t) = (c * t) * t := by rw [← hk]; exact htk
  have htt : t * t = 1 := by rw [← pow_two, ht]
  have hcc : c * c = 1 := by rw [← pow_two, hc]
  have hct : t * c = c * t := by
    calc t * c = t * c * (t * t) := by rw [htt, mul_one]
      _ = (t * (c * t)) * t := by group
      _ = ((c * t) * t) * t := by rw [h1]
      _ = c * t * (t * t) := by group
      _ = c * t := by rw [htt, mul_one]
  have hsq : (x ^ k) ^ 2 = 1 := by
    rw [hk, pow_two]
    calc c * t * (c * t) = c * (t * c) * t := by group
      _ = c * (c * t) * t := by rw [hct]
      _ = c * c * (t * t) := by group
      _ = 1 := by rw [hcc, htt, mul_one]
  have hxk : x ^ k = 1 := by
    apply zpow_eq_one_of_zpow_two_mul hx hx1
    rw [mul_comm, zpow_mul]
    simpa using hsq
  rw [hxk] at hk
  exact (eq_inv_of_mul_eq_one_left hk.symm).trans (inv_eq_of_mul_eq_one_right htt)

theorem conj_eq_or_inv {X n : K} (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1) (hn : n ∈ NormX X) :
    n * X * n⁻¹ = X ∨ n * X * n⁻¹ = X⁻¹ := by
  have h := (mem_normalizer_iff.1 hn X).1 (Subgroup.mem_zpowers X)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases zpow_cases hX3 k with h1 | h1 | h1
  · exfalso
    rw [h1] at hk
    apply hX1
    calc X = n⁻¹ * (n * X * n⁻¹) * n := by group
      _ = 1 := by rw [← hk]; group
  · left
    rw [h1] at hk
    exact hk.symm
  · right
    rw [h1] at hk
    rw [← hk]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hX3])

theorem center_eq_bot_of_simple {K : Type*} [Group K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) : Subgroup.center K = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center K := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 this b).symm

end Generic

namespace LyData

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)} {x : ↥(centralizer ({t} : Set G))}

theorem mem_zpowers_of_normQuotAut_eq_one (D : LyData G t ρ) (hx3 : x ^ 3 = 1)
    (hx : ρ x = x1p) {n : ↥(NormX (x : G))} (hn : normQuotAut n = 1) :
    (n : G) ∈ zpowers (x : G) := by
  have hcov := D.cover
  have hXG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hX1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hx
    exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hx
  have ht2 : t ^ 2 = 1 := by rw [← D.order_t]; exact pow_orderOf_eq_one t
  have htX : t * (x : G) = (x : G) * t := (mem_centralizer_singleton_iff.1 x.2).symm
  have hact : ∀ m : ↥(centralizer ({(x : G)} : Set G)),
      ∃ k : ℤ, (x : G) ^ k = ((n : G) * m * (n : G)⁻¹)⁻¹ * m := by
    intro m
    have h1 : normQuotAut n (QuotientGroup.mk m) = QuotientGroup.mk m := by rw [hn]; rfl
    rw [normQuotAut_mk, QuotientGroup.eq] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa [conjCent_apply] using this
  have htM : t ∈ centralizer ({(x : G)} : Set G) := mem_centralizer_singleton_iff.2 htX
  obtain ⟨k0, hk0⟩ := hact ⟨t, htM⟩
  have hc2 : ((n : G) * t * (n : G)⁻¹) ^ 2 = 1 := by rw [conj_pow, ht2]; group
  have hnt : (n : G) * t * (n : G)⁻¹ = t := eq_of_zpow_eq_inv_mul hXG3 hX1 ht2 hc2 htX hk0
  have hnt' : (n : G) * t = t * (n : G) := by
    calc (n : G) * t = ((n : G) * t * (n : G)⁻¹) * (n : G) := by group
      _ = t * (n : G) := by rw [hnt]
  have hnH : (n : G) ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hnt'
  let nH : ↥(centralizer ({t} : Set G)) := ⟨(n : G), hnH⟩
  have hnx : nH * x * nH⁻¹ = x ∨ nH * x * nH⁻¹ = x⁻¹ := by
    rcases conj_eq_or_inv hXG3 hX1 n.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hσ : ρ nH * x1p * (ρ nH)⁻¹ = x1p ∨ ρ nH * x1p * (ρ nH)⁻¹ = x1p⁻¹ := by
    rcases hnx with h | h
    · left
      have := congrArg ρ h
      simpa [map_mul, map_inv, hx] using this
    · right
      have := congrArg ρ h
      simpa [map_mul, map_inv, hx] using this
  have hLcomm : ∀ l : ↥(centralizer ({t} : Set G)), l ∈ IsCover11.Lsub ρ → nH * l * nH⁻¹ = l := by
    intro l hl
    have hl' : nH * l * nH⁻¹ ∈ IsCover11.Lsub ρ := by
      show ρ (nH * l * nH⁻¹) ∈ fix012
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_fix012_of_normalizes hσ hl
    obtain ⟨k, hk⟩ := hact (D.toCent hx3 hx ⟨l, hl⟩)
    have hd : (nH * l * nH⁻¹)⁻¹ * l = x ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    have hdL : x ^ k ∈ IsCover11.Lsub ρ := by
      rw [← hd]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hl') hl
    have h1 : x ^ k = 1 := zpow_eq_one_of_mem_Lsub hx3 hx hdL
    rw [h1] at hd
    exact inv_mul_eq_one.1 hd
  have hcommσ : ∀ τ ∈ fix012 ⊓ alternatingGroup (Fin 11), ρ nH * τ = τ * ρ nH := by
    rintro τ ⟨hτ, hτA⟩
    obtain ⟨e, he⟩ : τ ∈ ρ.range := hcov.range_eq ▸ hτA
    have heL : e ∈ IsCover11.Lsub ρ := by
      show ρ e ∈ fix012
      rw [he]; exact hτ
    have h1 : nH * e = e * nH := mul_inv_eq_iff_eq_mul.1 (hLcomm e heL)
    have h2 : ρ nH * ρ e = ρ e * ρ nH := by rw [← map_mul, ← map_mul, h1]
    rw [he] at h2
    exact h2
  have hfix : ∀ i : Fin 11, 3 ≤ i.val → ρ nH i = i := fun i hi => fix_of_commute_all hcommσ hi
  have hsign : sign (ρ nH) = 1 := hcov.sign_rho nH
  obtain ⟨y, hyx, hy⟩ : ∃ y : ↥(centralizer ({t} : Set G)), y ∈ zpowers x ∧ ρ y = ρ nH := by
    rcases eq_pow_x1p_of_fix_of_even hfix hsign with h1 | h1 | h1
    · exact ⟨1, one_mem _, by rw [map_one, h1]⟩
    · exact ⟨x, mem_zpowers x, by rw [hx, h1]⟩
    · exact ⟨x ^ 2, Subgroup.pow_mem _ (mem_zpowers x) 2, by rw [map_pow, hx, h1]⟩
  have hyX : (y : G) ∈ zpowers (x : G) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyx
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← hk, Subgroup.coe_zpow]
  rcases hcov.eq_or_eq_mul_z hy with hn1 | hn2
  · rw [show (n : G) = (y : G) from congrArg Subtype.val hn1]
    exact hyX
  ·
    exfalso
    have htN : t ∈ NormX (x : G) := centralizer_le_normX htM
    have hyN : (y : G) ∈ NormX (x : G) := Subgroup.le_normalizer hyX
    have hnG : (n : G) = (y : G) * t := congrArg Subtype.val hn2
    have hnyt : n = (⟨(y : G), hyN⟩ : ↥(NormX (x : G))) * ⟨t, htN⟩ := Subtype.ext hnG
    have htriv : normQuotAut (⟨t, htN⟩ : ↥(NormX (x : G))) = 1 := by
      have h1 := normQuotAut_of_mem_zpowers (X := (x : G)) hyX
      rw [hnyt, map_mul, h1, one_mul] at hn
      exact hn
    obtain ⟨hsimple, hnab, -⟩ := D.centQuot_facts hx3 hx
    have hcen := center_eq_bot_of_simple hsimple hnab
    have htq : tQuot x ∈ Subgroup.center (CentQuot (x : G)) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      have h1 : normQuotAut (⟨t, htN⟩ : ↥(NormX (x : G))) (QuotientGroup.mk m) =
          QuotientGroup.mk m := by rw [htriv]; rfl
      rw [normQuotAut_mk] at h1
      have h2 : (tQuot x) * QuotientGroup.mk m * (tQuot x)⁻¹ = QuotientGroup.mk m := by
        change QuotientGroup.mk (⟨t, htM⟩ : ↥(centralizer ({(x : G)} : Set G))) *
          QuotientGroup.mk m * (QuotientGroup.mk (⟨t, htM⟩ :
            ↥(centralizer ({(x : G)} : Set G))))⁻¹ = QuotientGroup.mk m
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact h1
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    rw [hcen, Subgroup.mem_bot] at htq
    have := D.orderOf_tQuot hx3 hx
    rw [htq, orderOf_one] at this
    exact absurd this (by norm_num)

theorem ker_normQuotAut (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    (normQuotAut : ↥(NormX (x : G)) →* MulAut (CentQuot (x : G))).ker =
      (zpowers (x : G)).subgroupOf (NormX (x : G)) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · exact D.mem_zpowers_of_normQuotAut_eq_one hx3 hx
  · intro hn
    have := normQuotAut_of_mem_zpowers (X := (x : G)) hn
    have h2 : n = (⟨(n : G), Subgroup.le_normalizer hn⟩ : ↥(NormX (x : G))) := rfl
    rw [h2]
    exact this

theorem normQuotAutQuot_injective (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    Function.Injective (normQuotAutQuot : NormQuot (x : G) →* MulAut (CentQuot (x : G))) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H n =>
    change normQuotAut n = 1 at hq
    have h1 : n ∈ (normQuotAut : ↥(NormX (x : G)) →* MulAut (CentQuot (x : G))).ker := hq
    rw [D.ker_normQuotAut hx3 hx] at h1
    exact (QuotientGroup.eq_one_iff n).2 h1

omit [Finite G] in
theorem exists_inverting (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    ∃ h : ↥(centralizer ({t} : Set G)), h * x * h⁻¹ = x⁻¹ := by
  obtain ⟨h, hh⟩ := D.cover.exists_lift invP_sign
  refine ⟨h, D.cover.eq_of_rho_eq_of_pow_three ?_ ?_ ?_⟩
  · rw [conj_pow, hx3]; group
  · rw [inv_pow, hx3, inv_one]
  · rw [map_mul, map_mul, map_inv, map_inv, hh, hx]
    exact invP_conj

omit [Finite G] in
theorem index_centralizer_normX (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    ((centralizer ({(x : G)} : Set G)).subgroupOf (NormX (x : G))).index = 2 := by
  have hXG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hX1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hx
    exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hx
  obtain ⟨h, hh⟩ := D.exists_inverting hx3 hx
  have hhG : (h : G) * (x : G) * (h : G)⁻¹ = (x : G)⁻¹ := congrArg Subtype.val hh
  have hhN : (h : G) ∈ NormX (x : G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    show zpowers ((h : G) * (x : G) * (h : G)⁻¹) = zpowers (x : G)
    rw [hhG, Subgroup.zpowers_inv]
  have hne : (x : G) ≠ (x : G)⁻¹ := by
    intro h2
    apply hX1
    have h3 : (x : G) * (x : G) = 1 := by
      calc (x : G) * (x : G) = (x : G) * (x : G)⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel _
    calc (x : G) = (x : G) ^ 3 * ((x : G) * (x : G))⁻¹ := by group
      _ = 1 := by rw [hXG3, h3]; group
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨(h : G), hhN⟩, fun b => ?_⟩
  have hb := conj_eq_or_inv hXG3 hX1 b.2
  have hiff1 : (b : G) * (x : G) = (x : G) * (b : G) ↔ (b : G) * (x : G) * (b : G)⁻¹ = (x : G) :=
    (mul_inv_eq_iff_eq_mul).symm
  have hiff2 : (b : G) * (h : G) * (x : G) = (x : G) * ((b : G) * (h : G)) ↔
      (b : G) * (x : G) * (b : G)⁻¹ = (x : G)⁻¹ := by
    have e1 : (b : G) * (h : G) * (x : G) * ((b : G) * (h : G))⁻¹ =
        ((b : G) * (x : G) * (b : G)⁻¹)⁻¹ := by
      calc (b : G) * (h : G) * (x : G) * ((b : G) * (h : G))⁻¹
          = (b : G) * ((h : G) * (x : G) * (h : G)⁻¹) * (b : G)⁻¹ := by group
        _ = (b : G) * (x : G)⁻¹ * (b : G)⁻¹ := by rw [hhG]
        _ = ((b : G) * (x : G) * (b : G)⁻¹)⁻¹ := by group
    rw [← mul_inv_eq_iff_eq_mul, e1, inv_eq_iff_eq_inv, eq_comm]
  simp only [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff, Subgroup.coe_mul]
  rw [hiff1, hiff2]
  rcases hb with h1 | h1
  · right
    refine ⟨h1, ?_⟩
    rw [h1]
    exact hne
  · left
    refine ⟨h1, ?_⟩
    rw [h1]
    exact fun h2 => hne h2.symm

omit [Finite G] in
theorem card_normX (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    Nat.card ↥(NormX (x : G)) = 2 * Nat.card ↥(centralizer ({(x : G)} : Set G)) := by
  have h1 := Subgroup.card_mul_index ((centralizer ({(x : G)} : Set G)).subgroupOf
    (NormX (x : G)))
  rw [D.index_centralizer_normX hx3 hx, Nat.card_congr
    (subgroupOfEquivOfLe centralizer_le_normX).toEquiv] at h1
  rw [← h1, mul_comm]

omit [Finite G] in
theorem card_normQuot (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    Nat.card (NormQuot (x : G)) = 2 * Nat.card (CentQuot (x : G)) := by
  have hXG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hX1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hx
    exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hx
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf (x : G) = 3 := orderOf_eq_prime hXG3 hX1
  have h1 : Nat.card ↥(NormX (x : G)) = Nat.card (NormQuot (x : G)) *
      Nat.card ↥((zpowers (x : G)).subgroupOf (NormX (x : G))) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [Nat.card_congr (subgroupOfEquivOfLe (Subgroup.le_normalizer (H := zpowers (x : G)))).toEquiv,
    Nat.card_zpowers, hord] at h1
  have h2 : Nat.card ↥(centralizer ({(x : G)} : Set G)) =
      Nat.card (CentQuot (x : G)) *
        Nat.card ↥(zpowers (⟨(x : G), self_mem_centralizer_singleton _⟩ :
          ↥(centralizer ({(x : G)} : Set G)))) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord] at h2
  have h3 := D.card_normX hx3 hx
  rw [h1, h2] at h3
  omega

end LyData

section AutCount

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem card_mulAut_of_outer (hc : Subgroup.center K = ⊥) (ho : Nat.card (Outer K) = 2) :
    Nat.card (MulAut K) = 2 * Nat.card K := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner K)
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have : a ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun σ : MulAut K => σ g) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * a = (a * g * a⁻¹) * a := by rw [this]
        _ = a * g := by group
    rw [hc, Subgroup.mem_bot] at this
    exact this
  have h2 := Subgroup.card_ker_mul_card_range (MulAut.conj : K →* MulAut K)
  rw [(MonoidHom.ker_eq_bot_iff _).2 hinj, Subgroup.card_bot, one_mul] at h2
  change Nat.card (MulAut K) = Nat.card (Outer K) * Nat.card (inner K) at h1
  rw [h1, ho]
  change 2 * Nat.card (MulAut.conj : K →* MulAut K).range = 2 * Nat.card K
  rw [h2]

end AutCount

theorem outer_card_of_equiv_mcl
    {K : Type} [Group K]
    (e : K ≃* Blueprint.NativeSporadic.McL) : Nat.card (Outer K) = 2 := by
  have h2 := CFSG.Sporadic.Recognition.McLAS.card_outer_mcl
  have h3 := Nat.card_congr (@CFSG.ComponentClassification.OuterAutomorphisms.equivalence K
    Blueprint.NativeSporadic.McL _ inferInstance e).toEquiv
  exact h3.trans h2

namespace LyData

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)} {x : ↥(centralizer ({t} : Set G))}

theorem normQuot_mulEquiv_aut (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p)
    (hout : Nat.card (Outer (CentQuot (x : G))) = 2) :
    Nonempty (NormQuot (x : G) ≃* MulAut (CentQuot (x : G))) := by
  obtain ⟨hsimple, hnab, -⟩ := D.centQuot_facts hx3 hx
  have hcen := center_eq_bot_of_simple hsimple hnab
  have hinj := D.normQuotAutQuot_injective hx3 hx
  have hcard : Nat.card (MulAut (CentQuot (x : G))) ≤ Nat.card (NormQuot (x : G)) := by
    rw [card_mulAut_of_outer hcen hout, D.card_normQuot hx3 hx]
  exact ⟨MulEquiv.ofBijective (normQuotAutQuot : NormQuot (x : G) →* MulAut (CentQuot (x : G)))
    (hinj.bijective_of_nat_card_le hcard)⟩

theorem lemma43
    (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    Nonempty (CentQuot (x : G) ≃* Blueprint.NativeSporadic.McL) ∧
      Nonempty (NormQuot (x : G) ≃* MulAut Blueprint.NativeSporadic.McL) := by
  obtain ⟨e⟩ := D.centQuot_mcl hx3 hx
  refine ⟨⟨e⟩, ?_⟩
  have hout : Nat.card (Outer (CentQuot (x : G))) = 2 := outer_card_of_equiv_mcl e
  obtain ⟨f⟩ := D.normQuot_mulEquiv_aut hx3 hx hout
  exact ⟨f.trans (@MulAut.congr (CentQuot (x : G)) _ Blueprint.NativeSporadic.McL inferInstance e)⟩

omit [Finite G] in
theorem card_centralizer_eq_three_mul (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    Nat.card ↥(centralizer ({(x : G)} : Set G)) = 3 * Nat.card (CentQuot (x : G)) := by
  have hXG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hX1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hx
    exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hx
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf (x : G) = 3 := orderOf_eq_prime hXG3 hX1
  have h2 : Nat.card ↥(centralizer ({(x : G)} : Set G)) =
      Nat.card (CentQuot (x : G)) *
        Nat.card ↥(zpowers (⟨(x : G), self_mem_centralizer_singleton _⟩ :
          ↥(centralizer ({(x : G)} : Set G)))) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord] at h2
  rw [h2, mul_comm]

theorem card_centralizer_x1
    (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    Nat.card ↥(centralizer ({(x : G)} : Set G)) = 2 ^ 7 * 3 ^ 7 * 5 ^ 3 * 7 * 11 := by
  obtain ⟨e⟩ := D.centQuot_mcl hx3 hx
  rw [card_centralizer_eq_three_mul hx3 hx, Nat.card_congr e.toEquiv,
    CFSG.Sporadic.Recognition.McLAS.card_mcl_eq]
  norm_num

end LyData

theorem exists_lemma43_of_oneClassDoubleCover
    {G : Type} [Group G] [Finite G] (hG : OneClassDoubleCover G 11) :
    ∃ x : G, orderOf x = 3 ∧ Nonempty (CentQuot x ≃* Blueprint.NativeSporadic.McL) ∧
      Nonempty (NormQuot x ≃* MulAut Blueprint.NativeSporadic.McL) := by
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover hG
  obtain ⟨x, hx3, hx⟩ := D.exists_lift_x1p
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hx
    exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hx
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨h1, h2⟩ := D.lemma43 hx3 hx
  exact ⟨(x : G), orderOf_eq_prime hxG3 hx1, h1, h2⟩

end CFSG.Sporadic.Recognition.LyonsSims
