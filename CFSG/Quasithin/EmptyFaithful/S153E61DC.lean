module

public import CFSG.Quasithin.EmptyFaithful.S153E61DB
public import CFSG.Quasithin.EmptyFaithful.S153E55C

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E61D

section Dat

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N N' : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}

theorem concl53_symm {cx : Ctx15350 T Mc M V₁ V₂ t} (h : Concl15353One cx N N') :
    Concl15353One cx N' N where
  omega := by
    obtain ⟨Ω, h1, h2, h3⟩ := h.omega
    exact ⟨Ω, h1, h2, by rw [sup_comm]; exact h3⟩
  inf := by rw [inf_comm]; exact h.inf
  comm := fun a ha b hb => (h.comm b hb a ha).symm
  iso₁ := h.iso₂
  iso₂ := h.iso₁
  comm₁ := h.comm₂
  comm₂ := h.comm₁

theorem concl54_symm {cx : Ctx15350 T Mc M V₁ V₂ t} (h : Concl15354 cx N N' g s) :
    Concl15354 cx N' N g s where
  one := h.one
  two_prod := h.two_prod
  two_center := h.two_center
  three_eq := h.three_eq
  three_perp := h.three_perp
  three_klein := h.three_klein
  four_sup := by rw [sup_comm]; exact h.four_sup
  four_inf := by rw [inf_comm]; exact h.four_inf
  four_cent₁ := h.four_cent₂
  four_cent₂ := h.four_cent₁
  four_nat₁ := h.four_nat₂
  four_nat₂ := h.four_nat₁
  five_comm := h.five_comm
  five_norm := h.five_norm

theorem chain54_symm {cx : Ctx15350 T Mc M V₁ V₂ t} (c : Chain15354 cx N N' g s) :
    Chain15354 cx N' N g s where
  nonab := c.nonab
  h51 := c.h51
  h52 := c.h52
  h53one := concl53_symm c.h53one
  h53two := c.h53two
  hg := c.hg
  hgZ := c.hgZ
  h54 := concl54_symm c.h54

structure Dat61 (cx : Ctx15350 T Mc M V₁ V₂ t) (N N' : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) : Prop where
  c54 : Chain15354 cx N N' g s
  h55 : Concl15355 cx g
  hs : s = 1
  h59 : Concl15359 cx

theorem Dat61.symm {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) : Dat61 cx N' N g s :=
  ⟨chain54_symm d.c54, d.h55, d.hs, d.h59⟩

theorem dat61_of_chain {cx : Ctx15350 T Mc M V₁ V₂ t} {y t₁ : G}
    (c : Chain15359 cx N N' g s y t₁) : Dat61 cx N N' g s :=
  ⟨c.toChain15354, c.h55, c.h58.two_s, c.h59⟩

theorem Dat61.pd {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) :
    S153E55.PDecomp (Y153 Mc M ⊔ UH153 T M V₁ Mc) (Pgp153 T M V₁ Mc g) (VZ T M)
      (Ni153 T Mc M V₁ N) (Ni153 T Mc M V₁ N') (Pi153 T Mc M V₁ N g) (Pi153 T Mc M V₁ N' g) :=
  S153E55.pdecomp cx d.c54

end Dat

section Transitive

variable {Γ : Type} [Group Γ]

theorem transitive_of_nat {M' Si S S₂ : Subgroup Γ} (h : IsSumOfNatSL2ModulesN153 1 M' Si S S₂)
    (hnorm : ∀ m ∈ M', ∀ x ∈ Si, m * x * m⁻¹ ∈ Si) :
    ∀ a ∈ Si, a ∉ S₂ → ∀ b ∈ Si, b ∉ S₂ → ∃ m ∈ M', m * a * m⁻¹ * b⁻¹ ∈ S₂ := by
  obtain ⟨β, φ, hβs, -, -, hφk, hequiv⟩ := h
  intro a ha haS b hb hbS
  have hne : ∀ x : ↥Si, (x : Γ) ∉ S₂ → Multiplicative.toAdd (φ x) 0 ≠ 0 := by
    intro x hx h0
    apply hx
    rw [← hφk]
    have : Multiplicative.toAdd (φ x) = 0 := by
      funext j
      rw [Subsingleton.elim j 0]
      exact h0
    exact this
  obtain ⟨A, hA⟩ := sl2_transitive _ _ (hne ⟨a, ha⟩ haS) (hne ⟨b, hb⟩ hbS)
  obtain ⟨m, hm⟩ := hβs A
  refine ⟨m, m.2, ?_⟩
  have hy := hequiv m ⟨a, ha⟩ ⟨(m : Γ) * a * (m : Γ)⁻¹, hnorm m m.2 a ha⟩ rfl
  have hyb : φ ⟨(m : Γ) * a * (m : Γ)⁻¹, hnorm m m.2 a ha⟩ = φ ⟨b, hb⟩ := by
    rw [hy]
    apply Multiplicative.toAdd.injective
    funext j
    rw [Subsingleton.elim j 0]
    simp only [toAdd_ofAdd, hm]
    exact hA
  have h1 : φ (⟨(m : Γ) * a * (m : Γ)⁻¹, hnorm m m.2 a ha⟩ * (⟨b, hb⟩ : ↥Si)⁻¹) = 1 := by
    rw [map_mul, map_inv, hyb, mul_inv_cancel]
  exact (hφk _).1 h1

end Transitive

section Instance

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N N' : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}

theorem transitive_Pi {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) :
    ∀ a ∈ Pi153 T Mc M V₁ N g, a ∉ VZ T M → ∀ b ∈ Pi153 T Mc M V₁ N g, b ∉ VZ T M →
      ∃ γ ∈ Ni153 T Mc M V₁ N, γ * a * γ⁻¹ * b⁻¹ ∈ VZ T M := by
  have hnat := d.c54.h54.four_nat₁
  rw [d.hs] at hnat
  exact transitive_of_nat hnat fun m hm x hx => d.pd.conj_P₁ (preAut153_le hm) hx

theorem exists_d_aux (cx : Ctx15350 T Mc M V₁ V₂ t) {g : G}
    (hI : Igp153 T M V₁ Mc g = Y153 Mc M ⊔ UH153 T M V₁ Mc)
    {N' : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    (hNY : N' ≤ autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc))
    (e : ↥N' ≃* Equiv.Perm (Fin 3)) (hcomm : commV N' = ⊤) :
    ∃ y : G, y ∈ Ni153 T Mc M V₁ N' ∧ y ^ 3 = 1 ∧
      ∀ v ∈ VZ T M, y * v * y⁻¹ = v → v = 1 := by
  have hV := cx.c.hyp.elemAbelian
  let a₀ : ↥N' := e.symm (finRotate 3)
  have ha₀3 : a₀ ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    simp only [a₀, MulEquiv.apply_symm_apply]
    decide
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    have h1 := congrArg e h
    simp only [a₀, MulEquiv.apply_symm_apply, map_one] at h1
    exact absurd h1 (by decide)
  obtain ⟨y', hy'YU, hy'⟩ := (mem_autI hV).1 (hNY a₀.2)
  obtain ⟨k, hk⟩ := S153E55.exists_pow_two_pow_odd (y' : G)
  have hyN : (y' : G) ^ 2 ^ k ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.pow_mem _ y'.2 _
  have hyYU : (y' : G) ^ 2 ^ k ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.pow_mem _ hy'YU _
  have hconv : convI hV ⟨(y' : G) ^ 2 ^ k, hyN⟩ = (a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k := by
    have h1 : (⟨(y' : G) ^ 2 ^ k, hyN⟩ : Subgroup.normalizer (VZ T M : Set G)) = y' ^ 2 ^ k :=
      Subtype.ext rfl
    rw [h1, map_pow, hy']
  have ha_N : (a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k ∈ N' := Subgroup.pow_mem _ a₀.2 _
  have ha3 : ((a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have h1 : (a₀ : MulAut (IntMod (VZ T M) hV)) ^ 3 = 1 := by
      have := congrArg Subtype.val ha₀3
      simpa using this
    rw [h1, one_pow]
  have ha1 : (a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k ≠ 1 := by
    intro h
    have h1 : a₀ ^ 2 ^ k = 1 := Subtype.ext (by simpa using h)
    have h2 : a₀ ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.2 ⟨h1, ha₀3⟩
    have h3 : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [h3, pow_one] at h2
    exact ha₀1 h2
  refine ⟨(y' : G) ^ 2 ^ k, ?_, ?_, ?_⟩
  · refine mem_preAut153.2 ⟨hyYU, hyN, ?_⟩
    show convI hV ⟨(y' : G) ^ 2 ^ k, hyN⟩ ∈ N'
    rw [hconv]
    exact ha_N
  ·
    set y : G := (y' : G) ^ 2 ^ k with hy
    have hy3N : y ^ 3 ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.pow_mem _ hyN 3
    have hconv3 : convI hV ⟨y ^ 3, hy3N⟩ = 1 := by
      have h1 : (⟨y ^ 3, hy3N⟩ : Subgroup.normalizer (VZ T M : Set G)) = ⟨y, hyN⟩ ^ 3 := Subtype.ext rfl
      rw [h1, map_pow, hconv]
      exact ha3
    have hcent : y ^ 3 ∈ Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV _).1 hconv3
    have hyP : y ^ 3 ∈ Pgp153 T M V₁ Mc g :=
      S153E55.centralizer_le_P hI cx ⟨Subgroup.pow_mem _ hyYU 3, hcent⟩
    have hP2 : IsPGroup 2 (Pgp153 T M V₁ Mc g) := S153E55.P_isPGroup hI
    obtain ⟨n, hn⟩ := hP2 ⟨y ^ 3, hyP⟩
    have hn' : (y ^ 3) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hd1 : orderOf (y ^ 3) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have hd2 : orderOf (y ^ 3) ∣ orderOf y := orderOf_pow_dvd 3
    have hodd : Odd (orderOf (y ^ 3)) := Odd.of_dvd_nat hk hd2
    have hcop : Nat.Coprime (orderOf (y ^ 3)) (2 ^ n) := by
      apply Nat.Coprime.pow_right
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      have := Nat.odd_iff.1 hodd
      omega
    have h1 : orderOf (y ^ 3) = 1 := Nat.Coprime.eq_one_of_dvd hcop hd1
    exact orderOf_eq_one_iff.1 h1
  · intro v hv hvy
    have hfix := S153E55.fixV_eq_bot_of_perm (W := IntMod (VZ T M) hV) IntMod.sq_eq_one e hcomm ha_N
      ha3 ha1
    have hw : IntMod.mk hV ⟨v, hv⟩ ∈
        fixV (Subgroup.zpowers ((a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k)) := by
      rw [mem_fixV_zpowers_iff, ← hconv]
      refine IntMod.val_injective ?_
      rw [convI_apply_val]
      exact hvy
    rw [hfix, Subgroup.mem_bot] at hw
    exact congrArg IntMod.val hw

theorem exists_d {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) :
    ∃ y : G, y ∈ Ni153 T Mc M V₁ N' ∧ y ^ 3 = 1 ∧
      ∀ v ∈ VZ T M, y * v * y⁻¹ = v → v = 1 := by
  have hV := cx.c.hyp.elemAbelian
  have h53 := d.c54.h53one
  obtain ⟨e⟩ := h53.iso₂
  have hNY : N' ≤ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    rw [S153E55.autI_YU_eq cx h53]
    exact le_sup_right
  exact exists_d_aux cx d.c54.h54.one hNY e (S153E55.commV_eq_top cx hNY h53.comm₂)

end Instance

end S153E61D

end CFSG.Quasithin
