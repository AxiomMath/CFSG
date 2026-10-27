module

public import CFSG.Quasithin.EmptyFaithful.S153E58F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E58

open S153E57

section XData

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

omit [Group G] [Finite G] in
theorem sq_eq_one_pi {n : ℕ} (v : Multiplicative (Fin n → ZMod 2)) : v ^ 2 = 1 := by
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  funext i
  simp [CharTwo.add_self_eq_zero]

theorem XS_data {cx : Ctx15350 T Mc M V₁ V₂ t} (c : Chain15356 cx N₁ N₂ g s y t₁) :
    XS T M V₁ Mc y ≤ HStar153 T M V₁ Mc ∧
      (∀ a ∈ XS T M V₁ Mc y, ∀ b ∈ XS T M V₁ Mc y, a * b = b * a) ∧
      (∀ a ∈ XS T M V₁ Mc y, a ^ 2 = 1) ∧ Nat.card ↥(XS T M V₁ Mc y) = 2 ^ (s + 1) := by
  obtain ⟨e⟩ := c.h56.X_rank
  refine ⟨XStar_le_HStar cx (X_le_Mc cx c.hy.1 c.h56.V0_eq), XS_comm c, fun a ha => ?_, ?_⟩
  · have h1 : e ((⟨a, ha⟩ : ↥(XS T M V₁ Mc y)) ^ 2) = 1 := by
      rw [map_pow]
      exact sq_eq_one_pi _
    have h2 : (⟨a, ha⟩ : ↥(XS T M V₁ Mc y)) ^ 2 = 1 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val h2
  · rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]

theorem exists_D {cx : Ctx15350 T Mc M V₁ V₂ t} (c : Chain15356 cx N₁ N₂ g s y t₁) (hs : 0 < s)
    {a : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))}
    (ha : a ∈ XStar153 T M V₁ Mc (VZ T M)) :
    ∃ D : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))),
      D ≤ HStar153 T M V₁ Mc ∧ (∀ d ∈ D, d * a = a * d) ∧ a ∈ ⁅D, D⁆ := by
  refine ⟨XS T M V₁ Mc y ⊔ XS' T M V₁ Mc y t₁, A_le_HStar cx c, A_comm_v c ha, ?_⟩
  set D := XS T M V₁ Mc y ⊔ XS' T M V₁ Mc y t₁ with hD
  have hext : CFSG.IsExtraspecial 2 ↥D := by
    rcases c.h56.D8s with ⟨h0, -⟩ | ⟨-, h⟩
    · omega
    · exact h.1
  have haD : a ∈ D := Subgroup.mem_sup_left (Vs_le_XS c ha)
  have hcent : (⟨a, haD⟩ : ↥D) ∈ Subgroup.center ↥D := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (A_comm_v c ha z z.2)
  have hZ2 : Nat.card ↥(Subgroup.center ↥D) = 2 := CFSG.IsExtraspecial.center_order_p 2 ↥D
  have hQab := CFSG.IsExtraspecial.quotient_elementary_abelian 2 ↥D
  have hQnt := CFSG.IsExtraspecial.quotient_nontrivial 2 ↥D
  have hQcomm : ∀ p q : ↥D ⧸ Subgroup.center ↥D, p * q = q * p := fun p q =>
    hQab.toIsMulCommutative.is_comm.comm p q
  have hcomm_center : ∀ x y : ↥D, ⁅x, y⁆ ∈ Subgroup.center ↥D := by
    intro x y
    rw [← QuotientGroup.eq_one_iff]
    have h := hQcomm (QuotientGroup.mk x) (QuotientGroup.mk y)
    simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h]
    group
  have hnonab : ∃ x y : ↥D, ⁅x, y⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ x : ↥D, x ∈ Subgroup.center ↥D := by
      intro x
      rw [Subgroup.mem_center_iff]
      intro z
      have := hcon z x
      simp only [commutatorElement_def] at this
      calc z * x = (z * x * z⁻¹ * x⁻¹) * x * z := by group
        _ = x * z := by rw [this]; group
    have hsub : Subsingleton (↥D ⧸ Subgroup.center ↥D) := ⟨fun p q => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      rw [(QuotientGroup.eq_one_iff x).2 (hall x), (QuotientGroup.eq_one_iff y).2 (hall y)]⟩
    exact (not_nontrivial_iff_subsingleton.2 hsub) hQnt
  set Zd : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :=
    (Subgroup.center ↥D).map D.subtype with hZd_def
  have hZd : Nat.card ↥Zd = 2 := by
    rw [hZd_def, Subgroup.card_map_of_injective D.subtype_injective]
    exact hZ2
  have hCle : ⁅D, D⁆ ≤ Zd := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact ⟨⁅(⟨x, hx⟩ : ↥D), ⟨y, hy⟩⁆, hcomm_center _ _, rfl⟩
  have hCne : ⁅D, D⁆ ≠ ⊥ := by
    obtain ⟨x, y, hxy⟩ := hnonab
    intro hbot
    apply hxy
    have : ⁅(x : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))), (y : MulAut _)⁆ ∈
        ⁅D, D⁆ := Subgroup.commutator_mem_commutator x.2 y.2
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hCeq : ⁅D, D⁆ = Zd := by
    have hdvd : Nat.card ↥⁅D, D⁆ ∣ 2 := hZd ▸ Subgroup.card_dvd_of_le hCle
    have hne1 : Nat.card ↥⁅D, D⁆ ≠ 1 := fun h1 => hCne (Subgroup.card_eq_one.1 h1)
    have h2 : Nat.card ↥⁅D, D⁆ = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact absurd h hne1
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hCle (by omega)
  rw [hCeq]
  exact ⟨⟨a, haD⟩, hcent, rfl⟩

theorem exists_fixed_T {cx : Ctx15350 T Mc M V₁ V₂ t} (c : Chain15356 cx N₁ N₂ g s y t₁) :
    ∃ z₀ : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)), z₀ ≠ 1 ∧
      z₀ ∈ S153E.tildeZS T M V₁ Mc ∧
      ∀ w : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)),
        (∀ x ∈ XStar153 T M V₁ Mc T, x w = w) ↔ (w = 1 ∨ w = z₀) := by
  obtain ⟨z₀', hz₀'⟩ := exists_z₀ cx
  obtain ⟨zS, hzS, hzSZ⟩ := exists_zS_aux cx
  have hzSU : zS ∈ UH153 T M V₁ Mc := S153E.ZS_le_U cx hzS
  have hz₀ne : piU cx ⟨zS, hzSU⟩ ≠ 1 := fun h => hzSZ ((piU_eq_one_iff cx _).1 h)
  have hz₀eq : piU cx ⟨zS, hzSU⟩ = z₀' := (hz₀' ⟨zS, hzSU⟩ hzS).resolve_left hz₀ne
  have hz₀ZS : z₀' ∈ S153E.tildeZS T M V₁ Mc := hz₀eq ▸ (mem_tildeZS_iff cx _).2 hzS
  have hz₀'ne : z₀' ≠ 1 := hz₀eq ▸ hz₀ne
  have hfix : ∀ x ∈ XStar153 T M V₁ Mc T, x z₀' = z₀' := by
    intro x hx
    obtain ⟨n, hnT, rfl⟩ := (mem_XStar_iff cx T x).1 hx
    have hnMc : (n : G) ∈ Mc := NZ_le_Mc cx n.2
    have hnZS : (n : G) * zS * (n : G)⁻¹ ∈ ZS153 T M V₁ := by
      have hnorm : T ≤ Subgroup.normalizer (ZS153 T M V₁ : Set G) :=
        le_sup_right.trans cx.hF.L₁T_normalizes_Vp
      exact (Subgroup.mem_normalizer_iff.1 (hnorm hnT) zS).1 hzS
    have h1 := piU_conj cx n hnMc ⟨zS, hzSU⟩
    rw [hz₀eq] at h1
    rcases hz₀' ⟨(n : G) * zS * (n : G)⁻¹, S153E.U_conj_mem hnMc hzSU⟩ hnZS with h | h
    · exfalso
      rw [h] at h1
      apply hz₀'ne
      have : rho cx n z₀' = 1 := h1.symm
      exact (map_eq_one_iff _ (rho cx n).injective).1 this
    · rw [h] at h1
      exact h1.symm
  refine ⟨z₀', hz₀'ne, hz₀ZS, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  ·
    have ht₁ := c.ht₁.1
    have hSig2 : IsPGroup 2 ↥(XS T M V₁ Mc y ⊔ XS' T M V₁ Mc y t₁ ⊔
        Subgroup.zpowers (ttOf cx ht₁)) :=
      IsPGroup.to_sup_of_normal_left' (isPGroup_A cx c) (isPGroup_zpowers_tt cx ht₁)
        (Subgroup.zpowers_le.2 (tt_mem_normalizer cx c))
    have hSigH : XS T M V₁ Mc y ⊔ XS' T M V₁ Mc y t₁ ⊔ Subgroup.zpowers (ttOf cx ht₁) ≤
        HStar153 T M V₁ Mc :=
      sup_le (A_le_HStar cx c) (Subgroup.zpowers_le.2 (tt_mem_HStar cx ht₁))
    obtain ⟨S, hS, hSigS⟩ := A4.exists_isSylowTwoOf_ge hSigH hSig2
    obtain ⟨h, -, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hS (S153E.isSylowTwoOf_HStar_T cx)
    have hSfix : ∀ v : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)),
        (∀ x ∈ XStar153 T M V₁ Mc T, x v = v) → ∀ s' ∈ S, s' (h⁻¹ v) = h⁻¹ v := by
      intro v hv s' hs'
      have hx : h * s' * h⁻¹ ∈ XStar153 T M V₁ Mc T := by
        rw [hconj]
        simpa [mul_assoc] using hs'
      have h1 := hv _ hx
      have h2 : (h * s' * h⁻¹) v = v := h1
      have h3 : s' (h⁻¹ v) = h⁻¹ v := by
        have := congrArg (fun x => h⁻¹ x) h2
        simpa [MulAut.mul_apply] using this
      exact h3
    have hcases : ∀ v : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)),
        (∀ x ∈ XStar153 T M V₁ Mc T, x v = v) → h⁻¹ v = 1 ∨ h⁻¹ v = z₀' := by
      intro v hv
      exact fixed_cases cx c z₀' hz₀' (h⁻¹ v)
        (fun d hd => hSfix v hv d (hSigS (Subgroup.mem_sup_left (Subgroup.mem_sup_left hd))))
        (hSfix v hv _ (hSigS (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))))
    rcases hcases w hw with h1 | h1
    · left
      have : w = h (h⁻¹ w) := by simp
      rw [this, h1, map_one]
    · right
      have hz : h⁻¹ z₀' = 1 ∨ h⁻¹ z₀' = z₀' := hcases z₀' hfix
      have hz' : h⁻¹ z₀' = z₀' := hz.resolve_left (fun h0 => hz₀'ne
        ((map_eq_one_iff _ (h⁻¹ : MulAut _).injective).1 h0))
      have e : w = h (h⁻¹ w) := by simp
      rw [e, h1]
      have : h z₀' = z₀' := by
        have := congrArg (fun x => h x) hz'
        simpa using this.symm
      exact this
  · rcases hw with rfl | rfl
    · intro x _
      exact map_one x
    · exact hfix

end XData

end S153E58

end CFSG.Quasithin
