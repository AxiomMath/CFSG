module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQMid2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQCore
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQGam2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQMid1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQSev1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQSev3
public import CFSG.Quasithin.EmptyFaithful.S151V6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
open scoped Pointwise commutatorElement

namespace V2InQ

variable {G : Type} [Group G] [Finite G]

theorem false_of_data {T M V Z₁ V₂ L : Subgroup G} {hVe : IsElemAbelian 2 V}
    (d : Seven7Data V M T hVe) (hZV : Z₁ ≤ V) (hWV : V₂ ≤ V) (hsplit : Z₁ ⊔ V₂ = V)
    (hZc : Nat.card Z₁ = 4) (hWc : Nat.card V₂ = 16)
    (hLZ : ∀ ℓ ∈ L, ∀ a ∈ Z₁, ℓ * a * ℓ⁻¹ = a) (hb : IsLnBlock L 3)
    (hV₂Y : V₂ ≤ oPrimeResidualOf 3 (M ⊓ L))
    (hnorm : ∀ y ∈ oPrimeResidualOf 3 (M ⊓ L), ∀ a ∈ V₂, y * a * y⁻¹ ∈ V₂)
    (hfpf : ∃ c ∈ oPrimeResidualOf 3 (M ⊓ L), ∀ a ∈ V₂, c * a * c⁻¹ = a → a = 1)
    (hx0 : ∀ x : G, x ∈ Subgroup.normalizer (Z₁ : Set G) → Odd (orderOf x) →
      x ∈ Subgroup.normalizer (L : Set G)) : False := by
  classical
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  obtain ⟨c₀, hc₀Y, hfpf⟩ := hfpf
  have hY₀ML : oPrimeResidualOf 3 (M ⊓ L) ≤ M ⊓ L := zb_oPrime_le
  have hc₀ML : c₀ ∈ M ⊓ L := hY₀ML hc₀Y
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := d.hMN
  have hc₀N : c₀ ∈ Subgroup.normalizer (V : Set G) := hMN hc₀ML.1
  obtain ⟨hc₀N', hcP⟩ := conjAct_mem_oTwoUpper_of_oPrime (X := M ⊓ L) inf_le_left hMN hc₀Y
  set y : MulAut ↥V := conjAct V ⟨c₀, hc₀N⟩ with hydef
  have hyP : y ∈ oTwoUpper (autOn M V) := hcP
  obtain ⟨hy3, hfix, hfixne, hfixc, hker, hy1, hyZ⟩ := ybar_facts d hZV hWV hsplit hZc hWc hc₀N hcP
    (hLZ c₀ hc₀ML.2) (hnorm c₀ hc₀Y) hfpf hydef
  set z : MulAut ↥V := d.z with hzdef
  have hz3 : z ^ 3 = 1 := SevenGen.z3 d.ctx d.gen
  have hzfpf : ∀ w : ↥V, z w = w → w = 1 := SevenGen.fpf_z' d.ctx d.gen
  have hzP : z ∈ oTwoUpper (autOn M V) := d.ctx.Z_le_P d.gen.zZ
  have hzy : z * y = y * z := (d.ctx.Z_central d.gen.zZ hyP).symm
  obtain ⟨q, hqP, hqy⟩ := exists_conj_mul_of_not_mem_Z d.ctx d.gen hyP hyZ
  have hqz : q * z = z * q := d.ctx.Z_central d.gen.zZ hqP
  set E := Ebar z y hz3 hy3 hzy with hEdef
  have hEP : E ≤ oTwoUpper (autOn M V) := Ebar_le hzP hyP
  have hcore : ∀ g ∈ E, g ≠ 1 → Nat.card (fixOf g) ≤ 4 := by
    intro g hg hg1
    obtain ⟨a, b, rfl, hab⟩ := exists_not_dvd_of_ne_one hg hg1
    exact card_fixOf_le hz3 hy3 hzfpf hzy hqz hqy (le_of_eq hfixc) hab
  obtain ⟨x₀, hx₀M, hx₀N, ⟨i, hi3, hx₀act⟩, ⟨k, hx₀ord⟩⟩ := exists_x0 d
  have hx₀comm : conjAct V ⟨x₀, hx₀N⟩ * y = y * conjAct V ⟨x₀, hx₀N⟩ := by
    rw [hx₀act]
    exact (Commute.pow_left (show Commute z y from hzy) i).eq
  have hx₀Z : x₀ ∈ Subgroup.normalizer (Z₁ : Set G) :=
    normalizes_of_commute hVe hZV hfix hx₀N hx₀comm
  have hx₀L : x₀ ∈ Subgroup.normalizer (L : Set G) :=
    hx0 x₀ hx₀Z (by rw [hx₀ord]; exact Odd.pow (by decide))
  obtain ⟨e, β, hs⟩ := exists_lnStr hb
  set A : Subgroup G := preOn (M ⊓ Subgroup.normalizer (L : Set G)) V E with hAdef
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := fun g hg => (mem_preOn.1 hg).2.choose
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := fun g hg => (mem_preOn.1 hg).1.2
  have hx₀A : x₀ ∈ A := mem_preOn.2 ⟨⟨hx₀M, hx₀L⟩, hx₀N, by
    rw [hx₀act]
    exact ⟨i, 0, by rw [pow_zero, mul_one]⟩⟩
  have hc₀A : c₀ ∈ A :=
    mem_preOn.2 ⟨⟨hc₀ML.1, Subgroup.le_normalizer hc₀ML.2⟩, hc₀N, y_mem_Ebar⟩
  let Θ : ↥A →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hAN)
  let Γ : ↥A →* MulAut (Multiplicative (Vt 3)) := (gammaMap hs).comp (Subgroup.inclusion hAL)
  have hΘE : ∀ a : ↥A, Θ a ∈ E := fun a => (mem_preOn.1 a.2).2.choose_spec
  have hΘz : z ∈ Θ.range := by
    refine (Subgroup.zpowers_le.2 (show z ^ i ∈ Θ.range from ⟨⟨x₀, hx₀A⟩, hx₀act⟩))
      (A4.mem_zpowers_pow_of_coprime ?_)
    have : orderOf z = 3 := orderOf_eq_prime hz3 d.gen.z1
    rw [this]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hi3))
  have hΘy : y ∈ Θ.range := ⟨⟨c₀, hc₀A⟩, rfl⟩
  have hlt : 3 < Nat.card Θ.range := by
    by_contra hle
    push Not at hle
    have hz1 : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 d.gen.z1]
    have heq := Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hΘz) (by rw [hz1]; exact hle)
    apply hyZ
    rw [SevenGen.Z_eq_zpowers d.ctx d.gen, heq]
    exact hΘy
  have hΘdvd : Nat.card Θ.range ∣ 27 := by
    have hle : Θ.range ≤ oTwoUpper (autOn M V) := by
      rintro _ ⟨a, rfl⟩
      exact hEP (hΘE a)
    exact (Subgroup.card_dvd_of_le hle).trans (d.ctx.card_P ▸ dvd_refl _)
  have hΓdvd : Nat.card Γ.range ∣ 168 :=
    card_mulAut_vt3 ▸ Subgroup.card_subgroup_dvd_card Γ.range
  obtain ⟨a, haΓ, haΘ⟩ := exists_ker_ne_one_of_card Γ Θ hΓdvd hΘdvd (by norm_num) hlt
  set c : G := (a : G) with hcdef
  have hcA : c ∈ A := a.2
  obtain ⟨hcML, hcNV, hγE⟩ := mem_preOn.1 hcA
  have hcNL : c ∈ Subgroup.normalizer (L : Set G) := hcML.2
  set γ : MulAut ↥V := conjAct V ⟨c, hcNV⟩ with hγdef
  have hγ1 : γ ≠ 1 := haΘ
  have hΓ : gammaMap hs ⟨c, hcNL⟩ = 1 := haΓ
  have hcQ : ∀ ℓ ∈ L, c * ℓ * c⁻¹ * ℓ⁻¹ ∈ blockQ L := fun ℓ hℓ =>
    comm_mem_blockQ_of_gamma_eq_one hs ⟨c, hcNL⟩ hΓ hℓ
  have hcU : ∀ u ∈ blockU L, u⁻¹ * (c * u * c⁻¹) ∈ blockZ L := fun u hu =>
    comm_mem_blockZ_of_gamma_eq_one hs ⟨c, hcNL⟩ hΓ hu
  have hV2L : V₂ ≤ L := hV₂Y.trans (hY₀ML.trans inf_le_right)
  have hsq : ∀ a ∈ V₂, a * a = 1 := fun a ha => congrArg Subtype.val (d.ctx.sq ⟨a, hWV ha⟩)
  have hcV : ∀ a ∈ V₂, c * a * c⁻¹ ∈ V₂ :=
    normalizes_W hVe hWV hker (Ebar_comm_y hγE) hcNV hγdef
  have hcommV₂ : ∀ a ∈ V₂, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, hWV ha⟩ : ↥V) ⟨b, hWV hb⟩)
  have hVQ : V₂ ⊓ blockQ L ≤ blockU L := inf_blockQ_le_blockU hcommV₂ hc₀ML.2 (hnorm c₀ hc₀Y) hfpf
  have hVZ : ∀ a ∈ V₂, a ∈ blockZ L → a = 1 := inf_blockZ_trivial hc₀ML.2 hfpf
  have hγ3 : conjAct V ⟨c, hcNV⟩ ^ 3 = 1 := Ebar_cube hγE
  have hc3 := cube_centralizes hcNV hγ3
  have hcent := centralizes_of_comm hcQ hcU hV2L hsq hcV hVQ hVZ (fun a ha => hc3 a (hWV ha))
  have hfixγ : V₂.subgroupOf V ≤ fixOf γ := by
    intro u hu
    show γ u = u
    apply Subtype.ext
    rw [hγdef, conj_coe_apply]
    exact hcent u hu
  have hcardle : Nat.card (V₂.subgroupOf V) ≤ Nat.card (fixOf γ) := Subgroup.card_le_of_le hfixγ
  have h4 := hcore γ hγE hγ1
  rw [card_subgroupOf_of_le hWV, hWc] at hcardle
  omega

end V2InQ

end CFSG.Quasithin
