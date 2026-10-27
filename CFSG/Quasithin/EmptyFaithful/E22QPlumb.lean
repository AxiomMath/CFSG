module

public import CFSG.Quasithin.EmptyFaithful.E22QRes
public import CFSG.Quasithin.EmptyFaithful.E22QWr
public import CFSG.Quasithin.EmptyFaithful.E22PFinal
public import CFSG.Quasithin.Background.C2Inputs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB CFSG.GorensteinWalter
open scoped Pointwise commutatorElement

theorem plumb_dihedral_center_rot {n : ℕ} [NeZero n] (hn : 3 ≤ n) {x : DihedralGroup n}
    (hx : x ∈ Subgroup.center (DihedralGroup n)) :
    ∃ i : ZMod n, x = DihedralGroup.r i ∧ 2 * i = 0 := by
  rcases x with i | i
  · refine ⟨i, rfl, ?_⟩
    have h := Subgroup.mem_center_iff.mp hx (DihedralGroup.sr 0)
    rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at h
    have h' : (0 + i : ZMod n) = 0 - i := DihedralGroup.sr.inj h
    linear_combination h'
  · exfalso
    have h := Subgroup.mem_center_iff.mp hx (DihedralGroup.r 1)
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h
    have h' : (i - 1 : ZMod n) = i + 1 := DihedralGroup.sr.inj h
    have h2 : (2 : ZMod n) = 0 := by linear_combination -h'
    have h3 : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h2
    have h4 := (ZMod.natCast_eq_zero_iff 2 n).mp h3
    have := Nat.le_of_dvd (by norm_num) h4
    omega

theorem plumb_zmod_half {n : ℕ} [NeZero n] {i j : ZMod n} (hi : 2 * i = 0) (hj : 2 * j = 0)
    (hi0 : i ≠ 0) (hj0 : j ≠ 0) : i = j := by
  have key : ∀ k : ZMod n, 2 * k = 0 → k ≠ 0 → 2 * k.val = n := by
    intro k hk hk0
    have h1 : ((2 * k.val : ℕ) : ZMod n) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hk
    have h2 := (ZMod.natCast_eq_zero_iff (2 * k.val) n).mp h1
    have h3 : k.val ≠ 0 := fun h => hk0 ((ZMod.val_eq_zero k).mp h)
    have h4 : k.val < n := ZMod.val_lt k
    exact Nat.eq_of_dvd_of_lt_two_mul (by omega) h2 (by omega)
  have := key i hi hi0
  have := key j hj hj0
  exact ZMod.val_injective n (by omega)

theorem plumb_dihedral_center_unique {n : ℕ} [NeZero n] (hn : 3 ≤ n) {x y : DihedralGroup n}
    (hx : x ∈ Subgroup.center (DihedralGroup n)) (hy : y ∈ Subgroup.center (DihedralGroup n))
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨i, rfl, hi⟩ := plumb_dihedral_center_rot hn hx
  obtain ⟨j, rfl, hj⟩ := plumb_dihedral_center_rot hn hy
  have hi0 : i ≠ 0 := fun h => hx1 (by rw [h]; rfl)
  have hj0 : j ≠ 0 := fun h => hy1 (by rw [h]; rfl)
  rw [plumb_zmod_half hi hj hi0 hj0]

theorem plumb_dihedral_data {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp7 : 7 ≤ p) {J P : Subgroup G} (hJ : IsPSL 2 p 1 ↥J)
    (hP : IsSylowIn 2 P J) :
    ∃ z : G, z ∈ P ∧ orderOf z = 2 ∧ (∀ x ∈ P, z * x = x * z) ∧
      (∀ c ∈ P, (∀ x ∈ P, c * x = x * c) → c = 1 ∨ c = z) ∧
      (∀ y ∈ J, (∀ x ∈ J, x * z = z * x → x * y = y * x) → y = 1 ∨ y = z) ∧
      Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G) ⊓ J) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hJ
  have hK : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hodd : IsOddPrimePower (Nat.card (ZMod p)) := E22L2.e22pl2pgl_isOddPrimePower hp7 hK
  have hq8 : Nat.card (ZMod p) % 8 = 1 ∨ Nat.card (ZMod p) % 8 = 7 := by rwa [hK]
  have hPJ : P ≤ J := hP.le
  have hP' : IsSylowIn 2 (P.subgroupOf J) ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := P) (K := J) (H := J) hPJ le_rfl).mpr hP
    rwa [Subgroup.subgroupOf_self] at h
  obtain ⟨P₀, hP₀def⟩ : ∃ P₀ : Subgroup (PSL2 (ZMod p)), P₀ = (P.subgroupOf J).map φ.toMonoidHom :=
    ⟨_, rfl⟩
  have hP₀ : IsSylowIn 2 P₀ ⊤ := by
    have h := (E1.isSylowIn_map_mulEquiv φ (P := P.subgroupOf J) (H := ⊤)).mpr hP'
    rwa [Subgroup.map_top_of_surjective _ φ.surjective, ← hP₀def] at h
  obtain ⟨S, m, hST, hm2, ⟨e⟩⟩ := E22L2.e22pl2psl_sylow_dihedral_q hodd hq8 hP₀
  have e' : ↥P₀ ≃* DihedralGroup (2 ^ m) := (MulEquiv.subgroupCongr hST).symm.trans e
  obtain ⟨z₀, hz₀P, hz₀2, hz₀c, -⟩ := E22L2.dihedral_sylow_data hm2 e'
  have hz₀mem : z₀ ∈ (P.subgroupOf J).map φ.toMonoidHom := hP₀def ▸ hz₀P
  obtain ⟨y₀, hy₀P, hy₀⟩ := Subgroup.mem_map.mp hz₀mem
  have hy₀P' : (y₀ : G) ∈ P := Subgroup.mem_subgroupOf.mp hy₀P
  have hφy₀ : φ y₀ = z₀ := hy₀
  have hmemP : ∀ x : ↥J, (x : G) ∈ P ↔ φ x ∈ P₀ := by
    intro x
    rw [hP₀def]
    constructor
    · intro hx
      exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    · rintro ⟨x', hx', hxx'⟩
      have : x' = x := φ.injective hxx'
      subst this
      exact Subgroup.mem_subgroupOf.mp hx'
  have hord : orderOf (y₀ : G) = 2 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ y₀, hφy₀, hz₀2]
  have hcomm : ∀ x ∈ P, (y₀ : G) * x = x * (y₀ : G) := by
    intro x hx
    have hxJ : x ∈ J := hPJ hx
    have h1 := hz₀c (φ ⟨x, hxJ⟩) ((hmemP ⟨x, hxJ⟩).mp hx)
    rw [← hφy₀, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (φ.injective h1)
  have hcen : ∀ c ∈ P, (∀ x ∈ P, c * x = x * c) → c = 1 ∨ c = (y₀ : G) := by
    intro c hc hcc
    have hcJ : c ∈ J := hPJ hc
    have hz₀ne : e' ⟨z₀, hz₀P⟩ ≠ 1 := by
      intro h
      have : (⟨z₀, hz₀P⟩ : ↥P₀) = 1 := e'.injective (h.trans (map_one e').symm)
      have h1 : z₀ = 1 := congrArg Subtype.val this
      rw [h1, orderOf_one] at hz₀2
      omega
    have hz₀cen : e' ⟨z₀, hz₀P⟩ ∈ Subgroup.center (DihedralGroup (2 ^ m)) := by
      rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨q, rfl⟩ := e'.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hz₀c _ q.2).symm
    have hccen : e' ⟨φ ⟨c, hcJ⟩, (hmemP ⟨c, hcJ⟩).mp hc⟩ ∈
        Subgroup.center (DihedralGroup (2 ^ m)) := by
      rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨q, rfl⟩ := e'.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      obtain ⟨x, hxP⟩ := q
      have hx' : ∃ x' : ↥J, φ x' = x := ⟨φ.symm x, by simp⟩
      obtain ⟨x', rfl⟩ := hx'
      have hxP' : (x' : G) ∈ P := (hmemP x').mpr hxP
      have := hcc (x' : G) hxP'
      apply Subtype.ext
      show φ x' * φ ⟨c, hcJ⟩ = φ ⟨c, hcJ⟩ * φ x'
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext this.symm
    have hn3 : 3 ≤ 2 ^ m := by
      calc 3 ≤ 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have : NeZero (2 ^ m) := ⟨by positivity⟩
    by_cases hc1 : e' ⟨φ ⟨c, hcJ⟩, (hmemP ⟨c, hcJ⟩).mp hc⟩ = 1
    · left
      have : (⟨φ ⟨c, hcJ⟩, (hmemP ⟨c, hcJ⟩).mp hc⟩ : ↥P₀) = 1 :=
        e'.injective (hc1.trans (map_one e').symm)
      have h1 : φ ⟨c, hcJ⟩ = 1 := congrArg Subtype.val this
      have h2 : (⟨c, hcJ⟩ : ↥J) = 1 := φ.injective (h1.trans (map_one φ).symm)
      exact congrArg Subtype.val h2
    · right
      have := plumb_dihedral_center_unique hn3 hccen hz₀cen hc1 hz₀ne
      have h1 := e'.injective this
      have h2 : φ ⟨c, hcJ⟩ = z₀ := congrArg Subtype.val h1
      rw [← hφy₀] at h2
      exact congrArg Subtype.val (φ.injective h2)
  have hzJ : (y₀ : G) ∈ J := y₀.2
  have hodd' : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution (ZMod p) (p := p) (f := 1)
    (by rw [hK, pow_one]) hodd' one_pos hz₀2
  obtain ⟨n, hn3, ⟨eC⟩⟩ : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(Subgroup.centralizer ({z₀} : Set (PSL2 (ZMod p)))) ≃* DihedralGroup n) := by
    rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
    · obtain ⟨-, he⟩ := h1 (by rw [pow_one]; exact h)
      exact ⟨(p ^ 1 - 1) / 2, by rw [pow_one]; omega, he⟩
    · obtain ⟨-, he⟩ := h3 (by rw [pow_one]; exact h)
      exact ⟨(p ^ 1 + 1) / 2, by rw [pow_one]; omega, he⟩
  have : NeZero n := ⟨by omega⟩
  refine ⟨(y₀ : G), hy₀P', hord, hcomm, hcen, ?_, ?_⟩
  ·
    intro y hyJ hy
    set w : PSL2 (ZMod p) := φ ⟨y, hyJ⟩ with hw
    have hzy : (y₀ : G) * y = y * (y₀ : G) := hy (y₀ : G) hzJ rfl
    have hwC : w ∈ Subgroup.centralizer ({z₀} : Set (PSL2 (ZMod p))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rw [hw, ← hφy₀, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzy
    have hz₀C : z₀ ∈ Subgroup.centralizer ({z₀} : Set (PSL2 (ZMod p))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
    have hwcen : eC ⟨w, hwC⟩ ∈ Subgroup.center (DihedralGroup n) := by
      rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨q, rfl⟩ := eC.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      obtain ⟨c₀, hc₀⟩ := q
      obtain ⟨x', rfl⟩ : ∃ x' : ↥J, φ x' = c₀ := ⟨φ.symm c₀, by simp⟩
      have hc₀' := Subgroup.mem_centralizer_iff.mp hc₀ z₀ rfl
      rw [← hφy₀, ← map_mul, ← map_mul] at hc₀'
      have hxz : (x' : G) * (y₀ : G) = (y₀ : G) * (x' : G) :=
        (congrArg Subtype.val (φ.injective hc₀')).symm
      have hxy := hy (x' : G) x'.2 hxz
      apply Subtype.ext
      show φ x' * w = w * φ x'
      rw [hw, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxy
    have hzcen : eC ⟨z₀, hz₀C⟩ ∈ Subgroup.center (DihedralGroup n) := by
      rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨q, rfl⟩ := eC.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp q.2 z₀ rfl).symm
    have hz₀ne : eC ⟨z₀, hz₀C⟩ ≠ 1 := by
      intro h
      have : (⟨z₀, hz₀C⟩ : ↥(Subgroup.centralizer ({z₀} : Set (PSL2 (ZMod p))))) = 1 :=
        eC.injective (h.trans (map_one eC).symm)
      have h1 : z₀ = 1 := congrArg Subtype.val this
      rw [h1, orderOf_one] at hz₀2
      omega
    by_cases hw1 : eC ⟨w, hwC⟩ = 1
    · left
      have : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z₀} : Set (PSL2 (ZMod p))))) = 1 :=
        eC.injective (hw1.trans (map_one eC).symm)
      have h1 : w = 1 := congrArg Subtype.val this
      have h2 : (⟨y, hyJ⟩ : ↥J) = 1 := φ.injective (h1.trans (map_one φ).symm)
      exact congrArg Subtype.val h2
    · right
      have := plumb_dihedral_center_unique hn3 hwcen hzcen hw1 hz₀ne
      have h1 := eC.injective this
      have h2 : w = z₀ := congrArg Subtype.val h1
      rw [← hφy₀] at h2
      exact congrArg Subtype.val (φ.injective h2)
  ·
    have hsolv := E22L2.e22pl2psl_centralizer_isSolvable hodd (by omega) hz₀2
    let f : ↥(Subgroup.centralizer ({(y₀ : G)} : Set G) ⊓ J) →*
        ↥(Subgroup.centralizer ({z₀} : Set (PSL2 (ZMod p)))) :=
      (φ.toMonoidHom.comp (Subgroup.inclusion inf_le_right)).codRestrict _ (by
        intro x
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        have hx := Subgroup.mem_centralizer_iff.mp x.2.1 (y₀ : G) rfl
        rw [hh, ← hφy₀]
        show φ y₀ * φ (Subgroup.inclusion inf_le_right x) =
          φ (Subgroup.inclusion inf_le_right x) * φ y₀
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hx)
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subgroup.inclusion_injective _ (φ.injective this)
    exact Group.isSolvable_of_isSolvable_injective hf

section W

variable {G : Type} [Group G]

theorem plumb_conj_inf (g : G) (A B : Subgroup G) :
    A1b.conjSub g (A ⊓ B) = A1b.conjSub g A ⊓ A1b.conjSub g B :=
  Subgroup.map_inf A B _ (MulAut.conj g).injective

theorem plumb_conj_sup (g : G) (A B : Subgroup G) :
    A1b.conjSub g (A ⊔ B) = A1b.conjSub g A ⊔ A1b.conjSub g B :=
  Subgroup.map_sup A B _

theorem plumb_le_normalizer_of_comm {J₁ J₂ : Subgroup G}
    (hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) : J₁ ≤ Subgroup.normalizer (J₂ : Set G) :=
  fun a ha => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm a ha b hb).symm)

theorem plumb_mem_sup_of_comm {J₁ J₂ : Subgroup G} (hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a)
    {x : G} (hx : x ∈ J₁ ⊔ J₂) : ∃ a ∈ J₁, ∃ b ∈ J₂, x = a * b := by
  have hle := plumb_le_normalizer_of_comm hcomm
  have : x ∈ (J₁ : Set G) * (J₂ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right J₁ J₂ hle]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := this
  exact ⟨a, ha, b, hb, rfl⟩

theorem plumb_swap_or_fix {T J₁ J₂ : Subgroup G} (hne : J₁ ≠ J₂)
    (hperm : ∀ t ∈ T, A1b.conjSub t J₁ = J₁ ∨ A1b.conjSub t J₁ = J₂) {t₀ : G} (ht₀ : t₀ ∈ T)
    (hswap : A1b.conjSub t₀ J₁ = J₂) :
    ∀ s ∈ T, (A1b.conjSub s J₁ = J₁ ∧ A1b.conjSub s J₂ = J₂) ∨
      (A1b.conjSub s J₁ = J₂ ∧ A1b.conjSub s J₂ = J₁) := by
  intro s hs
  have h2 : A1b.conjSub s J₂ = A1b.conjSub (s * t₀) J₁ := by rw [A1b.conjSub_mul, hswap]
  have hst : s * t₀ ∈ T := T.mul_mem hs ht₀
  rcases hperm s hs with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rcases hperm (s * t₀) hst with h3 | h3
    · exact absurd ((A1b.conjSub_inj s).mp (h1.trans (h2.trans h3).symm)) hne
    · rw [h2, h3]
  · right
    refine ⟨h1, ?_⟩
    rcases hperm (s * t₀) hst with h3 | h3
    · rw [h2, h3]
    · exact absurd ((A1b.conjSub_inj s).mp (h1.trans (h2.trans h3).symm)) hne

theorem plumb_conj_X {T J₁ J₂ : Subgroup G}
    (hfix : ∀ s ∈ T, (A1b.conjSub s J₁ = J₁ ∧ A1b.conjSub s J₂ = J₂) ∨
      (A1b.conjSub s J₁ = J₂ ∧ A1b.conjSub s J₂ = J₁)) :
    ∀ s ∈ T, A1b.conjSub s (J₁ ⊔ J₂) = J₁ ⊔ J₂ := by
  intro s hs
  rw [plumb_conj_sup]
  rcases hfix s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

theorem plumb_isSolvable_sup_of_le_normalizer {N T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hN : Group.IsSolvable N)
    (hT : Group.IsSolvable T) : Group.IsSolvable (N ⊔ T : Subgroup G) := by
  set V := N ⊔ T
  have hNV : N ≤ V := le_sup_left
  have hTV : T ≤ V := le_sup_right
  have hVN : V ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hTN
  have : (N.subgroupOf V).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNV).mpr hVN
  set π := QuotientGroup.mk' (N.subgroupOf V)
  set f : T →* V ⧸ N.subgroupOf V := π.comp (Subgroup.inclusion hTV)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hv : (v : G) ∈ ((T ⊔ N : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTN] at hv
    obtain ⟨t, ht, n, hn, htn⟩ := hv
    refine ⟨⟨t, ht⟩, ?_⟩
    change π (Subgroup.inclusion hTV ⟨t, ht⟩) = π v
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h : ((Subgroup.inclusion hTV ⟨t, ht⟩)⁻¹ * v : V) = (t⁻¹ * v : G) := rfl
    rw [h, ← htn, inv_mul_cancel_left]
    exact hn
  have hNVsol : Group.IsSolvable (N.subgroupOf V) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNV).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNV).injective
  have hQsol : Group.IsSolvable (V ⧸ N.subgroupOf V) := Group.isSolvable_of_surjective hf
  refine Group.isSolvable_of_ker_le_range (N.subgroupOf V).subtype π ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

theorem plumb_eq_one_of_central {J : Subgroup G} (hs : IsSimpleGroup ↥J)
    (hnc : ∃ a b : ↥J, a * b ≠ b * a) {a : G} (ha : a ∈ J) (hc : ∀ x ∈ J, a * x = x * a) :
    a = 1 := by
  have hZ : Subgroup.center ↥J = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
  have hmem : (⟨a, ha⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem plumb_cent [Finite G] {T J₁ J₂ : Subgroup G} (hT2 : IsPGroup 2 T)
    (hs₁ : IsSimpleGroup ↥J₁) (hnc₁ : ∃ a b : ↥J₁, a * b ≠ b * a)
    (hs₂ : IsSimpleGroup ↥J₂) (hnc₂ : ∃ a b : ↥J₂, a * b ≠ b * a)
    (hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a)
    (hnormal : (J₁ ⊔ J₂).Normal) (hgen : J₁ ⊔ J₂ ⊔ T = ⊤)
    (ho2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) :
    Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := J₁ ⊔ J₂ with hX
  set C := Subgroup.centralizer (X : Set G) with hC
  have hCn : C.Normal := inferInstance
  have hCX : ∀ c ∈ C, c ∈ X → c = 1 := by
    intro c hcC hcX
    obtain ⟨a, ha, b, hb, rfl⟩ := plumb_mem_sup_of_comm hcomm hcX
    have hc := Subgroup.mem_centralizer_iff.mp hcC
    have h1 : a = 1 := by
      refine plumb_eq_one_of_central hs₁ hnc₁ ha fun x hx => ?_
      have := hc x (Subgroup.mem_sup_left hx)
      have hbx : x * b = b * x := hcomm x hx b hb
      have h2 : x * a * b = a * x * b := by
        calc x * a * b = x * (a * b) := by rw [mul_assoc]
          _ = a * b * x := this
          _ = a * (b * x) := by rw [mul_assoc]
          _ = a * (x * b) := by rw [hbx]
          _ = a * x * b := by rw [mul_assoc]
      exact (mul_right_cancel h2).symm
    have h2 : b = 1 := by
      refine plumb_eq_one_of_central hs₂ hnc₂ hb fun x hx => ?_
      have := hc x (Subgroup.mem_sup_right hx)
      have hax : a * x = x * a := hcomm a ha x hx
      have h3 : a * (x * b) = a * (b * x) := by
        calc a * (x * b) = (a * x) * b := by rw [mul_assoc]
          _ = (x * a) * b := by rw [hax]
          _ = x * (a * b) := by rw [mul_assoc]
          _ = a * b * x := this
          _ = a * (b * x) := by rw [mul_assoc]
      exact (mul_left_cancel h3).symm
    rw [h1, h2, one_mul]
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal (N := X) (T := T) hT2 (c : G)
      (hgen ▸ Subgroup.mem_top _)
    refine ⟨e, Subtype.ext ?_⟩
    simpa using hCX _ (C.pow_mem c.2 _) he
  have hle : C ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
      (fun x _ => by rw [Subgroup.normalizer_eq_top_iff.mpr hCn]; exact Subgroup.mem_top x) hC2
  rw [ho2] at hle
  exact le_bot_iff.mp hle

theorem plumb_mem_of_normalizes [Finite G] {P J : Subgroup G} (hP : IsSylowIn 2 P J) {a : G}
    (haJ : a ∈ J) (ha2 : ∃ e : ℕ, a ^ 2 ^ e = 1) (hn : ∀ u ∈ P, a * u * a⁻¹ ∈ P)
    (hn' : ∀ u ∈ P, a⁻¹ * u * a ∈ P) : a ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Sylow 2 ↥J := hP.toSylow with hS
  set a' : ↥J := ⟨a, haJ⟩ with ha'
  obtain ⟨e, he⟩ := ha2
  have hZ : IsPGroup 2 (Subgroup.zpowers a') := by
    have hord : orderOf a' ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using he))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hmem : a' ∈ Subgroup.normalizer ((S : Subgroup ↥J) : Set ↥J) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hSx : ∀ y : ↥J, y ∈ (S : Subgroup ↥J) ↔ (y : G) ∈ P := fun y => Iff.rfl
    rw [hSx, hSx]
    constructor
    · intro hx
      exact hn _ hx
    · intro hx
      have hx' : a * (x : G) * a⁻¹ ∈ P := hx
      have := hn' _ hx'
      have e : a⁻¹ * (a * (x : G) * a⁻¹) * a = x := by group
      rwa [e] at this
  have hZN : Subgroup.zpowers a' ≤ Subgroup.normalizer ((S : Subgroup ↥J) : Set ↥J) :=
    Subgroup.zpowers_le.mpr hmem
  have h1 := hZ.inf_normalizer_sylow S
  have h2 : a' ∈ Subgroup.zpowers a' ⊓ (S : Subgroup ↥J) := by
    rw [← h1]
    exact ⟨Subgroup.mem_zpowers a', hZN (Subgroup.mem_zpowers a')⟩
  exact h2.2

theorem plumb_factor_mem [Finite G] {T J₁ J₂ : Subgroup G} (hT2 : IsPGroup 2 T)
    (hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (hdisj : J₁ ⊓ J₂ = ⊥)
    (hP : IsSylowIn 2 (T ⊓ J₁) J₁) {a b : G} (ha : a ∈ J₁) (hb : b ∈ J₂) (hs : a * b ∈ T) :
    a ∈ T := by
  have hab : a * b = b * a := hcomm a ha b hb
  have ha2 : ∃ e : ℕ, a ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hT2 ⟨a * b, hs⟩
    refine ⟨e, ?_⟩
    have h1 : (a * b) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have hcab : Commute a b := hab
    rw [hcab.mul_pow] at h1
    have h2 : a ^ 2 ^ e = (b ^ 2 ^ e)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a ^ 2 ^ e ∈ J₁ ⊓ J₂ :=
      ⟨J₁.pow_mem ha _, by rw [h2]; exact J₂.inv_mem (J₂.pow_mem hb _)⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    exact h3
  have hn : ∀ u ∈ T ⊓ J₁, a * u * a⁻¹ ∈ T ⊓ J₁ := by
    intro u hu
    have hbu : b * u = u * b := (hcomm u hu.2 b hb).symm
    have h1 : (a * b) * u * (a * b)⁻¹ = a * u * a⁻¹ := by
      rw [mul_inv_rev]
      calc a * b * u * (b⁻¹ * a⁻¹) = a * (b * u) * b⁻¹ * a⁻¹ := by group
        _ = a * (u * b) * b⁻¹ * a⁻¹ := by rw [hbu]
        _ = a * u * a⁻¹ := by group
    rw [← h1]
    exact ⟨T.mul_mem (T.mul_mem hs hu.1) (T.inv_mem hs), by
      rw [h1]; exact J₁.mul_mem (J₁.mul_mem ha hu.2) (J₁.inv_mem ha)⟩
  have hn' : ∀ u ∈ T ⊓ J₁, a⁻¹ * u * a ∈ T ⊓ J₁ := by
    intro u hu
    have hJ : a⁻¹ * u * a ∈ J₁ := J₁.mul_mem (J₁.mul_mem (J₁.inv_mem ha) hu.2) ha
    have hbw : (a⁻¹ * u * a) * b⁻¹ = b⁻¹ * (a⁻¹ * u * a) := hcomm _ hJ b⁻¹ (J₂.inv_mem hb)
    have h1 : (a * b)⁻¹ * u * (a * b) = a⁻¹ * u * a := by
      rw [mul_inv_rev]
      calc b⁻¹ * a⁻¹ * u * (a * b) = b⁻¹ * (a⁻¹ * u * a) * b := by group
        _ = (a⁻¹ * u * a) * b⁻¹ * b := by rw [← hbw]
        _ = a⁻¹ * u * a := by group
    rw [← h1]
    exact ⟨T.mul_mem (T.mul_mem (T.inv_mem hs) hu.1) hs, by rw [h1]; exact hJ⟩
  exact (plumb_mem_of_normalizes hP ha ha2 hn hn').1

theorem plumb_psl_simple {p : ℕ} {Y : Type} [Group Y] (h : IsPSL 2 p 1 Y) : IsSimpleGroup Y :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 p 1 h).2

theorem plumb_psl_nonab {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] (h : IsPSL 2 p 1 Y) :
    ∃ a b : Y, a * b ≠ b * a := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model h
  have hnt : Nontrivial Y := (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 p 1 h).1
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (1 : Y)
  have hxc : φ x ∈ Subgroup.center (PSL2 (ZMod p)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hcon y x]
  rw [psl2_center_eq_bot, Subgroup.mem_bot] at hxc
  exact hx (φ.injective (hxc.trans (map_one φ).symm))

theorem plumb_isPSL_conj {p : ℕ} {J : Subgroup G} (t : G) (h : IsPSL 2 p 1 ↥J) :
    IsPSL 2 p 1 ↥(A1b.conjSub t J) :=
  CFSG.SectionRank.statedClassicalModel_of_mulEquiv ((MulAut.conj t).subgroupMap J).symm h

theorem plumb_wr_of_data [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (hpsl : IsPSL 2 p 1 ↥J₁)
    (hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (hdisj : J₁ ⊓ J₂ = ⊥)
    (hperm : ∀ t ∈ T, A1b.conjSub t J₁ = J₁ ∨ A1b.conjSub t J₁ = J₂)
    (hswap : ∃ t ∈ T, A1b.conjSub t J₁ = J₂)
    (hgen : J₁ ⊔ T = ⊤) (ho2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥)
    (hcoatom : IsCoatom M) (hTM : T ≤ M)
    (hMsplit : M = (M ⊓ J₁) ⊔ (M ⊓ J₂) ⊔ T)
    (hP : IsSylowIn 2 (T ⊓ J₁) J₁)
    (hMJ : M ⊓ J₁ = J₁ ⊓ Subgroup.centralizer
      (((T ⊓ J₁) ⊓ Subgroup.centralizer ((T ⊓ J₁ : Subgroup G) : Set G) : Subgroup G) :
        Set G)) :
    ∃ z₁ : G, Wr p T M J₁ J₂ z₁ := by
  have hp7 : 7 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨t₀, ht₀T, hswap⟩ := hswap
  have hs₁ : IsSimpleGroup ↥J₁ := plumb_psl_simple hpsl
  have hnc₁ : ∃ a b : ↥J₁, a * b ≠ b * a := plumb_psl_nonab hp hpsl
  have hpsl₂ : IsPSL 2 p 1 ↥J₂ := hswap ▸ plumb_isPSL_conj t₀ hpsl
  have hs₂ : IsSimpleGroup ↥J₂ := plumb_psl_simple hpsl₂
  have hnc₂ : ∃ a b : ↥J₂, a * b ≠ b * a := plumb_psl_nonab hp hpsl₂
  have hJ₁ne : J₁ ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hnc₁
    apply hab
    have h1 : a = 1 := Subtype.ext (by simpa using (h ▸ a.2 : (a : G) ∈ (⊥ : Subgroup G)))
    rw [h1, one_mul, mul_one]
  have hne : J₁ ≠ J₂ := fun h => hJ₁ne (by rw [← hdisj, ← h, inf_idem])
  have hfix := plumb_swap_or_fix hne hperm ht₀T hswap
  have hXT := plumb_conj_X hfix
  have hgen' : J₁ ⊔ J₂ ⊔ T = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le_sup_right le_sup_left T
  have hTN : T ≤ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) :=
    fun s hs => A1b.conjSub_eq_iff_mem_normalizer.mp (hXT s hs)
  have hnormal : (J₁ ⊔ J₂).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen']
    exact sup_le Subgroup.le_normalizer hTN
  have hcent := plumb_cent hT.isPGroup hs₁ hnc₁ hs₂ hnc₂ hcomm hnormal hgen' ho2
  have hP₂ : IsSylowIn 2 (T ⊓ J₂) J₂ := by
    have h := (E1.isSylowIn_conj_iff t₀ (p := 2) (P := T ⊓ J₁) (H := J₁)).mpr hP
    have hT' : A1b.conjSub t₀ T = T :=
      A1b.conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ht₀T)
    rwa [plumb_conj_inf, hswap, hT'] at h
  obtain ⟨z, hzP, hz2, hzc, hzcen, hcenfact, hsolv⟩ := plumb_dihedral_data hp hp8 hp7 hpsl hP
  have hZP : Subgroup.centralizer
      (((T ⊓ J₁) ⊓ Subgroup.centralizer ((T ⊓ J₁ : Subgroup G) : Set G) : Subgroup G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
    ext x
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h c hc
      rw [Set.mem_singleton_iff] at hc
      subst hc
      refine h c ?_
      exact ⟨hzP, Subgroup.mem_centralizer_iff.mpr fun y hy => (hzc y hy).symm⟩
    · intro h c hc
      have hc' : c ∈ (T ⊓ J₁) ⊓ Subgroup.centralizer ((T ⊓ J₁ : Subgroup G) : Set G) := hc
      have hcc := Subgroup.mem_centralizer_iff.mp hc'.2
      rcases hzcen c hc'.1 (fun y hy => (hcc y hy).symm) with h1 | h1
      · rw [h1, one_mul, mul_one]
      · rw [h1]
        exact h z rfl
  have hMJ1 : M ⊓ J₁ = Subgroup.centralizer ({z} : Set G) ⊓ J₁ := by
    rw [hMJ, hZP, inf_comm]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hcentral : ∀ s ∈ T ⊓ Subgroup.normalizer (J₁ : Set G), z * s = s * z := by
    intro s hs
    have hsT : s ∈ T := hs.1
    have hsN : s ∈ Subgroup.normalizer (J₁ : Set G) := hs.2
    have hsN' : s⁻¹ ∈ Subgroup.normalizer (J₁ : Set G) := inv_mem hsN
    have hnorm : ∀ u ∈ T ⊓ J₁, s * u * s⁻¹ ∈ T ⊓ J₁ := fun u hu =>
      ⟨T.mul_mem (T.mul_mem hsT hu.1) (T.inv_mem hsT),
        (Subgroup.mem_normalizer_iff.mp hsN u).mp hu.2⟩
    have hnorm' : ∀ u ∈ T ⊓ J₁, s⁻¹ * u * s ∈ T ⊓ J₁ := fun u hu =>
      ⟨T.mul_mem (T.mul_mem (T.inv_mem hsT) hu.1) hsT, by
        have := (Subgroup.mem_normalizer_iff.mp hsN' u).mp hu.2
        simpa using this⟩
    have hz' : s * z * s⁻¹ = z := by
      have hcz : ∀ x ∈ T ⊓ J₁, (s * z * s⁻¹) * x = x * (s * z * s⁻¹) := by
        intro x hx
        have hy := hzc _ (hnorm' x hx)
        calc s * z * s⁻¹ * x = s * (z * (s⁻¹ * x * s)) * s⁻¹ := by group
          _ = s * ((s⁻¹ * x * s) * z) * s⁻¹ := by rw [hy]
          _ = x * (s * z * s⁻¹) := by group
      rcases hzcen (s * z * s⁻¹) (hnorm z hzP) hcz with h | h
      · exfalso
        apply hz1
        have h2 : s * z = s := by simpa using (mul_inv_eq_one.mp h)
        exact mul_left_cancel (h2.trans (mul_one s).symm)
      · exact h
    exact (mul_inv_eq_iff_eq_mul.mp hz').symm
  have hMT : ∀ s ∈ T, A1b.conjSub s M = M := fun s hs =>
    A1b.conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hTM hs))
  have hD₂ : M ⊓ J₂ = A1b.conjSub t₀ (M ⊓ J₁) := by
    rw [plumb_conj_inf, hMT t₀ ht₀T, hswap]
  have hDfix : ∀ s ∈ T, A1b.conjSub s ((M ⊓ J₁) ⊔ (M ⊓ J₂)) = (M ⊓ J₁) ⊔ (M ⊓ J₂) := by
    intro s hs
    rw [plumb_conj_sup, plumb_conj_inf, plumb_conj_inf, hMT s hs]
    rcases hfix s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  have hTD : T ≤ Subgroup.normalizer (((M ⊓ J₁) ⊔ (M ⊓ J₂) : Subgroup G) : Set G) :=
    fun s hs => A1b.conjSub_eq_iff_mem_normalizer.mp (hDfix s hs)
  have hD₁sol : Group.IsSolvable ↥(M ⊓ J₁) := by
    rw [hMJ1]
    exact hsolv
  have hD₂sol : Group.IsSolvable ↥(M ⊓ J₂) := by
    rw [hD₂]
    let e := (MulAut.conj t₀).subgroupMap (M ⊓ J₁)
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  have hDsol : Group.IsSolvable ↥((M ⊓ J₁) ⊔ (M ⊓ J₂)) := by
    have h := plumb_isSolvable_sup_of_le_normalizer (N := M ⊓ J₂) (T := M ⊓ J₁)
      (plumb_le_normalizer_of_comm fun a ha b hb => hcomm a ha.2 b hb.2) hD₂sol hD₁sol
    rwa [sup_comm] at h
  have hTsol : Group.IsSolvable ↥T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥T := hT.isPGroup.isNilpotent
    infer_instance
  have hMsol : Group.IsSolvable ↥M := by
    have h := plumb_isSolvable_sup_of_le_normalizer hTD hDsol hTsol
    rwa [← hMsplit] at h
  have hMX : M ⊓ (J₁ ⊔ J₂) ≤ (M ⊓ J₁) ⊔ (M ⊓ J₂) := by
    intro x hx
    have hxM : x ∈ M := hx.1
    have hxX : x ∈ J₁ ⊔ J₂ := hx.2
    set D := (M ⊓ J₁) ⊔ (M ⊓ J₂) with hD
    have hxMT : x ∈ ((D ⊔ T : Subgroup G) : Set G) := by
      rw [← hMsplit]
      exact hxM
    rw [Subgroup.coe_mul_of_right_le_normalizer_left D T hTD] at hxMT
    obtain ⟨d, hd, s, hs, rfl⟩ := hxMT
    have hDX : D ≤ J₁ ⊔ J₂ :=
      sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)
    have hsX : s ∈ J₁ ⊔ J₂ := by
      have := (J₁ ⊔ J₂).mul_mem ((J₁ ⊔ J₂).inv_mem (hDX hd)) hxX
      simpa using this
    obtain ⟨a, ha, b, hb, rfl⟩ := plumb_mem_sup_of_comm hcomm hsX
    have haT : a ∈ T := plumb_factor_mem hT.isPGroup hcomm hdisj hP ha hb hs
    have hbT : b ∈ T := by
      have hba : b * a = a * b := (hcomm a ha b hb).symm
      have hs' : b * a ∈ T := by rw [hba]; exact hs
      exact plumb_factor_mem hT.isPGroup (fun x hx y hy => (hcomm y hy x hx).symm)
        (by rwa [inf_comm]) hP₂ hb ha hs'
    have haD : a ∈ D := Subgroup.mem_sup_left ⟨hTM haT, ha⟩
    have hbD : b ∈ D := Subgroup.mem_sup_right ⟨hTM hbT, hb⟩
    exact D.mul_mem hd (D.mul_mem haD hbD)
  refine ⟨z, ?_⟩
  exact
    { sylow := hT
      p_prime := hp
      p_mod := hp8
      p_ge := hp7
      psl₁ := hpsl
      comm := hcomm
      disj := hdisj
      normal_X := hnormal
      gen := hgen'
      cent := hcent
      o2 := ho2
      perm := hperm
      swap := ⟨t₀, ht₀T, hswap⟩
      z₁_mem := hzP.2
      z₁_ord := hz2
      z₁_central := hcentral
      cen_fact := hcenfact
      coatom := hcoatom
      solv := hMsol
      T_le := hTM
      M_J₁ := hMJ1
      M_X := hMX }

end W

section Main

variable {Γ : Type} [Group Γ]

theorem plumb_star_mono {M H S S' : Subgroup Γ} (h : S ≤ S') :
    E2.star M H S ≤ E2.star M H S' :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono H h)

theorem plumb_star_sup {M H S S' : Subgroup Γ} (hS : S ≤ H) (hS' : S' ≤ H) :
    E2.star M H (S ⊔ S') = E2.star M H S ⊔ E2.star M H S' := by
  unfold E2.star
  rw [Subgroup.subgroupOf_sup hS hS', Subgroup.map_sup]

theorem plumb_conj_le {H S : Subgroup Γ} {g : Γ} (hg : g ∈ H) (hS : S ≤ H) :
    A1b.conjSub g S ≤ H := by
  intro x hx
  have h1 := hS (A1b.mem_conjSub_iff.mp hx)
  have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg h1) (H.inv_mem hg)
  simpa [mul_assoc] using h2

theorem plumb_star_conj {M H S : Subgroup Γ} (hSH : S ≤ H) {s : Γ} (hs : s ∈ H) :
    E2.star M H (A1b.conjSub s S) = A1b.conjSub (E2P.starMap M H ⟨s, hs⟩) (E2.star M H S) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : s⁻¹ * (x : Γ) * s ∈ S := A1b.mem_conjSub_iff.mp hx
    rw [A1b.mem_conjSub_iff]
    refine ⟨⟨s⁻¹ * x * s, hSH hx'⟩, hx', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · intro y hy
    rw [A1b.mem_conjSub_iff] at hy
    obtain ⟨b, hb, hby⟩ := hy
    have hbS : (b : Γ) ∈ S := hb
    have hmem : s * (b : Γ) * s⁻¹ ∈ H := H.mul_mem (H.mul_mem hs b.2) (H.inv_mem hs)
    refine ⟨⟨_, hmem⟩, A1b.mem_conjSub_of_mem hbS, ?_⟩
    have e : (⟨s * (b : Γ) * s⁻¹, hmem⟩ : ↥H) = ⟨s, hs⟩ * b * (⟨s, hs⟩)⁻¹ :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_mul, map_inv, hby]
    group

theorem plumb_star_comm {M H K K' : Subgroup Γ} (hc : ⁅K, K'⁆ ≤ kerIn M H) :
    ∀ a ∈ E2.star M H K, ∀ b ∈ E2.star M H K', a * b = b * a := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hxy : ⁅(x : Γ), (y : Γ)⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hx hy
  have h1 : ⁅x, y⁆ ∈ (kerIn M H).subgroupOf H := Subgroup.mem_subgroupOf.mpr (hc hxy)
  have h2 : E2P.starMap M H ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
  rw [map_commutatorElement] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

theorem plumb_star_disj {M H K K' : Subgroup Γ}
    (h : (K ⊔ kerIn M H) ⊓ (K' ⊔ kerIn M H) ≤ kerIn M H) :
    E2.star M H K ⊓ E2.star M H K' = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  rw [Subgroup.mem_bot]
  have h1 : x⁻¹ * y ∈ (kerIn M H).subgroupOf H := by
    refine QuotientGroup.eq.mp ?_
    exact hxy.symm
  have h2 : (y : Γ) ∈ K ⊔ kerIn M H := by
    have h3 : (y : Γ) = (x : Γ) * ((x⁻¹ * y : ↥H) : Γ) := by simp
    rw [h3]
    exact Subgroup.mul_mem_sup hx (Subgroup.mem_subgroupOf.mp h1)
  have h3 : (y : Γ) ∈ K' ⊔ kerIn M H := Subgroup.mem_sup_left hy
  have h4 : y ∈ (kerIn M H).subgroupOf H := Subgroup.mem_subgroupOf.mpr (h ⟨h2, h3⟩)
  have h5 : E2P.starMap M H y = 1 := (QuotientGroup.eq_one_iff _).mpr h4
  rw [← hxy]
  exact h5

theorem plumb_isSylow_star_inf [Finite Γ] {H T M K : Subgroup Γ} (hT : IsSylowTwoOf T H)
    (hK : CFSG.Open.IsSubnormal K H) (hKH : K ≤ H) :
    IsSylowTwoOf (E2.star M H (T ⊓ K)) (E2.star M H K) := by
  have hS := E2P.isSylowTwoOf_inf_of_subnormal hT hK
  set ρ : ↥K →* E2.StarQuot M H := (E2P.starMap M H).comp (Subgroup.inclusion hKH) with hρ
  have hrange : ρ.range = E2.star M H K := by
    rw [hρ, MonoidHom.range_comp, E2P.star_def]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have himage : ((T ⊓ K).subgroupOf K).map ρ = E2.star M H (T ⊓ K) := by
    rw [hρ, E2P.star_def, ← Subgroup.map_map]
    congr 1
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx, rfl⟩
  have hSyl := E2P.isSylowTwoOf_map_hom hS ρ
  rwa [himage, hrange] at hSyl

theorem plumb_pCore_quotient {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : N = CFSG.Open.pCore 2 X) : pCoreOf 2 (⊤ : Subgroup (X ⧸ N)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hN
  rw [pCoreOf_top]
  set N : Subgroup X := CFSG.Open.pCore 2 X with hNdef
  set K : Subgroup X := (CFSG.Open.pCore 2 (X ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKn : K.Normal := Subgroup.normal_comap _
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := X ⧸ N) 2) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := CFSG.LieType.BorelTits.le_pCore 2 hKn hKp
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

theorem plumb_exists_wr [Finite Γ] (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    {H T M K : Subgroup Γ} (hmin : MinParabolic H T M) (hSQ : SQTKGroup ↥H)
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) (hJ : kerIn M H = pCoreOf 2 H)
    (ht : ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T)
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hK : IsPSL 2 p 1 ↥(E2.star M H K))
    (hMK : E2.star M H (M ⊓ K) = E2.star M H K ⊓ Subgroup.centralizer
      (((E2.star M H (T ⊓ K) ⊓ Subgroup.centralizer
        ((E2.star M H (T ⊓ K) : Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H)) :
        Subgroup (E2.StarQuot M H))) : Set (E2.StarQuot M H))) :
    ∃ (J₂ : Subgroup (E2.StarQuot M H)) (z₁ : E2.StarQuot M H),
      Wr p (E2.star M H T) (E2.star M H M) (E2.star M H K) J₂ z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (E2.StarQuot M H) := E2P.finite_starQuot M H
  have hTH : T ≤ H := hmin.isSylow.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hMmax : M ∈ maxOver H T := by
    have h : maxOver H T = {M} := hmin.uniqueMax
    rw [h]
    exact Set.mem_singleton M
  have hMH : M ≤ H := hMmax.1.1.le
  have hTM : T ≤ M := hMmax.2
  obtain ⟨hconj, hcase⟩ := hOrb Γ H T K hSQ hmin.isSylow hKc
  rcases hcase with hnorm | ⟨t₁, ht₁T, ht₁n, hpair, hcomm, hdisj, hTX⟩
  · exfalso
    obtain ⟨t, htT, hne, -⟩ := ht
    exact hne (A1b.conjSub_eq_iff_mem_normalizer.mpr (hnorm t htT))
  obtain ⟨K', hK'def⟩ : ∃ K' : Subgroup Γ, K' = A1b.conjSub t₁ K := ⟨_, rfl⟩
  have hpair' : conjSubgroupsBy T K = {K, K'} := by rw [hK'def]; exact hpair
  have hcomm' : ⁅K, K'⁆ ≤ kerIn M H := by rw [hK'def, hJ]; exact hcomm
  have hdisj' : (K ⊔ kerIn M H) ⊓ (K' ⊔ kerIn M H) ≤ kerIn M H := by
    rw [hK'def, hJ]; exact hdisj.le
  have hK'H : K' ≤ H := hK'def ▸ plumb_conj_le (hTH ht₁T) hKH
  obtain ⟨t₀, ht₀T, hne₀, hMsplit₀⟩ := ht
  have hK₀ : A1b.conjSub t₀ K = K' := by
    have hmem : A1b.conjSub t₀ K ∈ conjSubgroupsBy T K := ⟨t₀, ht₀T, rfl⟩
    rw [hpair'] at hmem
    rcases hmem with h | h
    · exact absurd h hne₀
    · exact h
  have hMT : ∀ s ∈ T, A1b.conjSub s M = M := fun s hs =>
    A1b.conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hTM hs))
  have hMsplit : M = (M ⊓ K) ⊔ (M ⊓ K') ⊔ T := by
    have e : cjSub t₀ (M ⊓ K) = M ⊓ K' := by
      show A1b.conjSub t₀ (M ⊓ K) = M ⊓ K'
      rw [plumb_conj_inf, hMT t₀ ht₀T, hK₀]
    rwa [e] at hMsplit₀
  have hgen : E2.star M H K ⊔ E2.star M H T = ⊤ := by
    rw [← plumb_star_sup hKH hTH, ← hHK]
    exact E2P.star_top M H
  have hperm : ∀ s ∈ E2.star M H T, A1b.conjSub s (E2.star M H K) = E2.star M H K ∨
      A1b.conjSub s (E2.star M H K) = E2.star M H K' := by
    rintro _ ⟨y, hy, rfl⟩
    have hyT : (y : Γ) ∈ T := hy
    have h1 : E2.star M H (A1b.conjSub (y : Γ) K) =
        A1b.conjSub (E2P.starMap M H y) (E2.star M H K) := plumb_star_conj hKH y.2
    have hmem : A1b.conjSub (y : Γ) K ∈ conjSubgroupsBy T K := ⟨y, hyT, rfl⟩
    rw [hpair'] at hmem
    rcases hmem with h | h
    · left
      rw [← h1, h]
    · right
      rw [← h1, h]
  have hswap : ∃ t ∈ E2.star M H T, A1b.conjSub t (E2.star M H K) = E2.star M H K' :=
    ⟨E2P.starMap M H ⟨t₁, hTH ht₁T⟩, ⟨⟨t₁, hTH ht₁T⟩, ht₁T, rfl⟩, by
      rw [← plumb_star_conj hKH (hTH ht₁T), hK'def]⟩
  have hMstar : E2.star M H M = (E2.star M H M ⊓ E2.star M H K) ⊔
      (E2.star M H M ⊓ E2.star M H K') ⊔ E2.star M H T := by
    have h := congrArg (E2.star M H) hMsplit
    have hMK₁ : M ⊓ K ≤ H := inf_le_left.trans hMH
    have hMK₂ : M ⊓ K' ≤ H := inf_le_left.trans hMH
    rw [plumb_star_sup (sup_le hMK₁ hMK₂) hTH, plumb_star_sup hMK₁ hMK₂, E2P.star_inf_M,
      E2P.star_inf_M] at h
    exact h
  have hSyl : IsSylowTwoOf (E2.star M H T) ⊤ := (E2P.minParabolic_star hmin).isSylow
  have hP : IsSylowIn 2 (E2.star M H T ⊓ E2.star M H K) (E2.star M H K) := by
    have h := plumb_isSylow_star_inf (M := M) hmin.isSylow hKc.2.2.1 hKH
    rwa [E2P.star_inf_T hmin.isSylow hKc.2.2.1 hKH] at h
  have hMJ : E2.star M H M ⊓ E2.star M H K = E2.star M H K ⊓ Subgroup.centralizer
      (((E2.star M H T ⊓ E2.star M H K) ⊓ Subgroup.centralizer
        ((E2.star M H T ⊓ E2.star M H K : Subgroup (E2.StarQuot M H)) :
          Set (E2.StarQuot M H)) : Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H)) := by
    rw [E2P.star_inf_T hmin.isSylow hKc.2.2.1 hKH, E2P.star_inf_M] at hMK
    exact hMK
  have hmax : IsMaxSubgroupIn ⊤ (E2.star M H M) := by
    have h : maxOver ⊤ (E2.star M H T) = {E2.star M H M} := (E2P.minParabolic_star hmin).uniqueMax
    have : E2.star M H M ∈ maxOver ⊤ (E2.star M H T) := by rw [h]; exact Set.mem_singleton _
    exact this.1
  have hcoatom : IsCoatom (E2.star M H M) :=
    ⟨hmax.1.ne, fun b hb => hmax.2 b hb le_top⟩
  have ho2 : pCoreOf 2 (⊤ : Subgroup (E2.StarQuot M H)) = ⊥ := by
    refine plumb_pCore_quotient ((kerIn M H).subgroupOf H) ?_
    rw [hJ]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  obtain ⟨z₁, hz₁⟩ := plumb_wr_of_data (T := E2.star M H T) (M := E2.star M H M)
    (J₁ := E2.star M H K) (J₂ := E2.star M H K') ⟨hSyl.1, hSyl.2.1, hSyl.2.2⟩ hp hp8 hK
    (plumb_star_comm hcomm') (plumb_star_disj hdisj') hperm hswap hgen ho2 hcoatom
    (plumb_star_mono hTM) hMstar hP hMJ
  exact ⟨E2.star M H K', z₁, hz₁⟩

theorem plumb_nParam_le_one [Finite Γ]
    (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (hWr : WrCore)
    {H T M K : Subgroup Γ} (hmin : MinParabolic H T M) (hSQ : SQTKGroup ↥H)
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) (hJ : kerIn M H = pCoreOf 2 H)
    (ht : ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T)
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hK : IsPSL 2 p 1 ↥(E2.star M H K))
    (hMK : E2.star M H (M ⊓ K) = E2.star M H K ⊓ Subgroup.centralizer
      (((E2.star M H (T ⊓ K) ⊓ Subgroup.centralizer
        ((E2.star M H (T ⊓ K) : Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H)) :
        Subgroup (E2.StarQuot M H))) : Set (E2.StarQuot M H))) :
    E1.nParam H ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (E2.StarQuot M H) := E2P.finite_starQuot M H
  have hTH : T ≤ H := hmin.isSylow.1
  obtain ⟨J₂, z₁, hz₁⟩ := plumb_exists_wr hOrb hmin hSQ hKc hHK hJ ht hp hp8 hK hMK
  have hIH : E1.InE 1 (⊤ : Subgroup (E2.StarQuot M H)) :=
    (E1.inE_iff_inEFor hz₁.sylow).mpr (hWr p (E2.StarQuot M H) _ _ _ _ _ hz₁)
  have hT' : IsSylowIn 2 (T.subgroupOf H) ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := T) (K := H) (H := H) hTH le_rfl).mpr
      hmin.isSylow
    rwa [Subgroup.subgroupOf_self] at h
  have hN : (kerIn M H).subgroupOf H ≤ T.subgroupOf H := by
    rw [hJ]
    exact Subgroup.subgroupOf_mono H (pCoreOf_le_of_isSylowIn hmin.isSylow)
  have hNM : ∀ Ω : Set (Subgroup ↥H), E1.IsInvColl ⊤ Ω → (kerIn M H).subgroupOf H ≤
      E1.eGen 1 ⊤ (T.subgroupOf H) Ω ⊔
        (⊤ ⊓ Subgroup.normalizer (E1.weakClosure (T.subgroupOf H) Ω : Set ↥H)) := by
    intro Ω hΩ x hx
    exact Subgroup.mem_sup_right ⟨Subgroup.mem_top x, E1.le_normalizer_weakClosure hΩ (hN hx)⟩
  have hInEFor : E1.InEFor 1 ⊤ (T.subgroupOf H) := E1.inEFor_of_quotient hIH hT' hNM
  have hInE : E1.InE 1 (⊤ : Subgroup ↥H) := (E1.inE_iff_inEFor hT').mpr hInEFor
  rw [E1.nParam_subgroupOf]
  have := (E1.nParam_le_iff (H := (⊤ : Subgroup ↥H)) (n := 1) one_pos).mpr hInE
  simpa using this

end Main

theorem e22NParamW_of_wrCore
    (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (hWr : WrCore)
    (h114 : E114OneResRest) : E2.E22NParamW := by
  have h114a : E114OneResNoA6 := e114OneResNoA6_of_rest h114
  intro Γ _ _ H T M K hmin hSQ hns hKc hHK hq hcases hSQs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (E2.StarQuot M H) := E2P.finite_starQuot M H
  have hTH : T ≤ H := hmin.isSylow.1
  have hT2 : IsPGroup 2 T := hmin.isSylow.2.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hJs : Group.IsSolvable ↥(kerIn M H) := isSolvable_kerIn_of_e22CasesNoN hcases
  have hO2T : oTwoUpper H ⊔ T = H := C1Pack12.oTwoUpper_sup_eq_of_sylow hmin.isSylow
  have hge1 := E22A.one_le_nParam hmin
  set Ks := E2.star M H K with hKs
  set π := QuotientGroup.mk' ((kerIn M H).subgroupOf H) with hπ
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKc
  have hnab : IsSimpleGroup ↥Ks → ∃ a b : ↥Ks, a * b ≠ b * a := fun hsimp => by
    have : Nontrivial ↥Ks := hsimp.toNontrivial
    exact nonabelian_of_perfect_surjective
      ((π.subgroupMap (K.subgroupOf H)).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      ((π.subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)
  have hSQK : SQTKGroup ↥Ks := sqtkGroup_subgroup hSQs Ks
  have h114' : E114OneRes := e114OneRes_of_noA6 h114a
  have hP : TypeOneRes ↥Ks → ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
      (∃ a b : X, a * b ≠ b * a) → Nonempty (X ≃* ↥Ks) → ∀ B : Subgroup (MulAut X),
      IsPGroup 2 B → IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
        (MulAut.conj : X →* MulAut X).range →
      E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ ((1 : ℕ) : ℕ∞) :=
    fun hty X _ _ _ hnabX ⟨e⟩ B hB hBI => by
      have hSQX : SQTKGroup X := sqtkGroup_of_mulEquiv e hSQK
      simpa using nParam_sup_le_one_of_res h114' hnabX hSQX (TypeOneRes.of_mulEquiv e hty) hB hBI
  have hfin : E1.nParam (T ⊔ oTwoUpper H) ≤ 1 → E1.nParam H = 1 :=
    fun h => by
      refine le_antisymm ?_ hge1
      rw [sup_comm, hO2T] at h
      simpa using h
  have hOneN : T ≤ Subgroup.normalizer (K : Set Γ) → TypeOneRes ↥Ks → E1.nParam H = 1 := by
    intro hTK hty
    refine hfin ?_
    have h := nParam_le_of_starC (Q := fun X _ => TypeOne X) (C := SolvSimpSolv)
      typeOne_isoInv (fun Y _ _ hH hK hC => e111ForQnC_sss typeOne_isoInv le_rfl Y hH hK hC)
      hTH hT2 hKc hHK hJs hty.toTypeOne.isSimpleGroup hty.toTypeOne (hP hty) hTH
      (solvSimpSolv_of_star hTH hT2 hKc hHK hTK hJs hty.toTypeOne.isSimpleGroup hTH)
    exact_mod_cast h
  dsimp only [E2.E22NParamWCases]
  refine ⟨fun hJ ht p hp hp8 hK hMK _ =>
    le_antisymm (plumb_nParam_le_one hOrb hWr hmin hSQ hKc hHK hJ ht hp hp8 hK hMK) hge1,
    fun hTK _ =>
    ⟨fun n hn1 hty _ _ hn => ?_, fun p e hp hp3 he hpe8 hK _ _ => hOneN hTK ?_,
      fun p hp hp2 hK _ => hOneN hTK ?_⟩⟩
  ·
    subst hn
    refine (hOneN hTK ?_).le
    rcases hty with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by simpa [IsSp4Prime] using h))
  ·
    exact Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe8, hK⟩))
  ·
    rcases hK with ⟨h4, hK⟩ | ⟨h4, hK, -⟩
    · exact Or.inr (Or.inr (Or.inr ⟨false, p, hp, hp2, by simp, fun _ => h4, hK⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨true, p, hp, hp2, fun _ => h4, by simp, hK⟩))

end CFSG.Quasithin.E2.E22N
