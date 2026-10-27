module

public import CFSG.Sporadic.Co1Patterson.AmalgamTransfer

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

variable {G X : Type*} [Group G] [Group X] {A Z : G → X} {a e w : G} {t W : X}

@[expose] def KeyId (A Z : G → X) (a e : G) (ε : X) (x : G) : Prop :=
  ∀ k ∈ C[a] ⊓ C[e], A (x * k * x⁻¹) = (Z x * ε) * A k * (Z x * ε)⁻¹

theorem keyId_of_mem (hA : IsoOn A C[a] C[t]) (hagree : ∀ y ∈ C[a] ⊓ C[w], Z y = A y)
    {x : G} (hx : x ∈ C[a] ⊓ C[w]) : KeyId A Z a e 1 x := by
  intro k hk
  rw [mul_one, hagree x hx, hA.map_conj (mem_inf.1 hx).1 (mem_inf.1 hk).1]

theorem KeyId.mul (hZ : IsoOn Z C[w] C[W]) {x₁ x₂ : G} {ε₁ ε₂ : X} (hx₁ : x₁ ∈ C[w])
    (hx₂ : x₂ ∈ C[w]) (hx₂K : ∀ k ∈ C[a] ⊓ C[e], x₂ * k * x₂⁻¹ ∈ C[a] ⊓ C[e])
    (hc : ε₁ * Z x₂ = Z x₂ * ε₁) (h₁ : KeyId A Z a e ε₁ x₁) (h₂ : KeyId A Z a e ε₂ x₂) :
    KeyId A Z a e (ε₁ * ε₂) (x₁ * x₂) := by
  intro k hk
  have e1 : Z x₁ * ε₁ * (Z x₂ * ε₂) = Z (x₁ * x₂) * (ε₁ * ε₂) := by
    rw [hZ.map_mul _ hx₁ _ hx₂]
    calc Z x₁ * ε₁ * (Z x₂ * ε₂) = Z x₁ * (ε₁ * Z x₂) * ε₂ := by group
      _ = Z x₁ * (Z x₂ * ε₁) * ε₂ := by rw [hc]
      _ = Z x₁ * Z x₂ * (ε₁ * ε₂) := by group
  rw [show x₁ * x₂ * k * (x₁ * x₂)⁻¹ = x₁ * (x₂ * k * x₂⁻¹) * x₁⁻¹ by group,
    h₁ _ (hx₂K k hk), h₂ k hk, ← e1]
  group

theorem KeyId.inv (hZ : IsoOn Z C[w] C[W]) {x : G} {ε : X} (hx : x ∈ C[w])
    (hxK : ∀ k ∈ C[a] ⊓ C[e], x⁻¹ * k * x ∈ C[a] ⊓ C[e]) (hc : ε * Z x = Z x * ε)
    (h : KeyId A Z a e ε x) : KeyId A Z a e ε⁻¹ x⁻¹ := by
  intro k hk
  have h' := h _ (hxK k hk)
  rw [show x * (x⁻¹ * k * x) * x⁻¹ = k by group] at h'
  have hu : Z x⁻¹ * ε⁻¹ = (Z x * ε)⁻¹ := by
    rw [hZ.map_inv hx, mul_inv_rev]
    exact (Commute.inv_inv (show Commute ε (Z x) from hc)).eq.symm
  rw [hu, inv_inv, inv_inv, h']
  group

theorem keyId_dichotomy (hA : IsoOn A C[a] C[t]) (he : e ∈ C[a])
    (hZ : IsoOn Z C[w] C[W]) (hwa : w ∈ C[a]) (hAw : A w = W)
    (hagree : ∀ y ∈ C[a] ⊓ C[w], Z y = A y) (hrig : AutRigidAt a e w) {x : G} (hxw : x ∈ C[w])
    (hxK : ∀ k, k ∈ C[a] ⊓ C[e] ↔ x * k * x⁻¹ ∈ C[a] ⊓ C[e])
    (hxX : ∀ y, y ∈ C[t] ⊓ C[A e] ↔ (Z x)⁻¹ * y * (Z x)⁻¹⁻¹ ∈ C[t] ⊓ C[A e]) :
    KeyId A Z a e 1 x ∨ KeyId A Z a e W x := by
  have hAK : IsoOn A (C[a] ⊓ C[e]) (C[t] ⊓ C[A e]) := hA.inf_cent he
  have hf := ((isoOn_conj x hxK).comp hAK).comp (isoOn_conj (Z x)⁻¹ hxX) |>.comp hAK.isoOn_inv
  have htriv : ∀ g : ↥(C[a] ⊓ C[e]), (g : G) ∈ C[w] → hf.toMulEquiv g = g := by
    intro g hg
    apply Subtype.ext
    rw [IsoOn.toMulEquiv_apply]
    have hxg : x * g * x⁻¹ ∈ C[a] ⊓ C[w] :=
      mem_inf.2 ⟨(mem_inf.1 ((hxK g).1 g.2)).1, mul_mem (mul_mem hxw hg) (inv_mem hxw)⟩
    have hgw : (g : G) ∈ C[a] ⊓ C[w] := mem_inf.2 ⟨(mem_inf.1 g.2).1, hg⟩
    show hAK.inv ((Z x)⁻¹ * A (x * g * x⁻¹) * (Z x)⁻¹⁻¹) = g
    rw [← hagree _ hxg, hZ.map_conj hxw hg, hagree _ hgw,
      show (Z x)⁻¹ * (Z x * A g * (Z x)⁻¹) * (Z x)⁻¹⁻¹ = A g by group, hAK.inv_apply g.2]
  have hcase : ∀ k (hk : k ∈ C[a] ⊓ C[e]),
      (Z x)⁻¹ * A (x * k * x⁻¹) * (Z x)⁻¹⁻¹ = A (hf.toMulEquiv ⟨k, hk⟩ : G) := by
    intro k hk
    rw [IsoOn.toMulEquiv_apply]
    have hm : (Z x)⁻¹ * A (x * k * x⁻¹) * (Z x)⁻¹⁻¹ ∈ C[t] ⊓ C[A e] :=
      (hxX _).1 (hAK.map_mem _ ((hxK k).1 hk))
    exact (hAK.apply_inv hm).symm
  rcases hrig hf.toMulEquiv htriv with h1 | h1
  · left
    intro k hk
    have := hcase k hk
    rw [h1 ⟨k, hk⟩] at this
    rw [mul_one, ← this]
    group
  · right
    intro k hk
    have := hcase k hk
    rw [h1 ⟨k, hk⟩, hA.map_conj hwa (mem_inf.1 hk).1, hAw] at this
    calc A (x * k * x⁻¹) = Z x * ((Z x)⁻¹ * A (x * k * x⁻¹) * (Z x)⁻¹⁻¹) * (Z x)⁻¹ := by group
      _ = Z x * W * A k * (Z x * W)⁻¹ := by rw [this]; group

omit [Group X] in
theorem conj_mem_inf_iff_of {x a' e' : G} (h1 : x * a * x⁻¹ = a') (h2 : x * e * x⁻¹ = e')
    (hK : ∀ k, k ∈ C[a'] ⊓ C[e'] ↔ k ∈ C[a] ⊓ C[e]) (k : G) :
    k ∈ C[a] ⊓ C[e] ↔ x * k * x⁻¹ ∈ C[a] ⊓ C[e] := by
  rw [← hK (x * k * x⁻¹), mem_inf, mem_inf, mem_cent_conj_iff x k a, mem_cent_conj_iff x k e,
    h1, h2]

omit [Group X] in
theorem mem_inf_mul_right_iff (hae : a * e = e * a) (k : G) :
    k ∈ C[a] ⊓ C[a * e] ↔ k ∈ C[a] ⊓ C[e] := by
  rw [hae, ← mem_cent_inf_mul_iff, inf_comm]

theorem keyId_of_rigid (hA : IsoOn A C[a] C[t]) (hAa : A a = t) (he : e ∈ C[a])
    (hZ : IsoOn Z C[w] C[W])
    (hwa : w ∈ C[a]) (hwe : w ∈ C[e]) (hAw : A w = W) (hagree : ∀ y ∈ C[a] ⊓ C[w], Z y = A y)
    (hrig : AutRigidAt a e w) (ha2 : a * a = 1) (he2 : e * e = 1) {τ ρ : G} (hτw : τ ∈ C[w])
    (hτa : τ * a * τ⁻¹ = e) (hτe : τ * e * τ⁻¹ = a) (hρw : ρ ∈ C[w]) (hρa : ρ * a * ρ⁻¹ = e)
    (hρe : ρ * e * ρ⁻¹ = a * e) : KeyId A Z a e 1 τ := by
  subst hAa
  have hae : a * e = e * a := (mem_cent_iff.1 he).symm
  have haw : a ∈ C[a] ⊓ C[w] :=
    mem_inf.2 ⟨mem_cent_iff.2 rfl, mem_cent_iff.2 (mem_cent_iff.1 hwa).symm⟩
  have hew : e ∈ C[a] ⊓ C[w] := mem_inf.2 ⟨he, mem_cent_iff.2 (mem_cent_iff.1 hwe).symm⟩
  have hρa' : ρ⁻¹ * a * ρ = a * e := by
    have : ρ * (a * e) * ρ⁻¹ = a := by
      calc ρ * (a * e) * ρ⁻¹ = (ρ * a * ρ⁻¹) * (ρ * e * ρ⁻¹) := by group
        _ = e * (a * e) := by rw [hρa, hρe]
        _ = a * (e * e) := by rw [← mul_assoc, ← hae, mul_assoc]
        _ = a := by rw [he2, mul_one]
    calc ρ⁻¹ * a * ρ = ρ⁻¹ * (ρ * (a * e) * ρ⁻¹) * ρ := by rw [this]
      _ = a * e := by group
  have hρe' : ρ⁻¹ * e * ρ = a := by rw [← hρa]; group
  have hKea : ∀ k, k ∈ C[e] ⊓ C[a] ↔ k ∈ C[a] ⊓ C[e] := fun k => by rw [inf_comm]
  have hKeae : ∀ k, k ∈ C[e] ⊓ C[a * e] ↔ k ∈ C[a] ⊓ C[e] := fun k =>
    (mem_cent_inf_mul_iff k a e).symm
  have hρK := conj_mem_inf_iff_of hρa hρe hKeae
  have hρK' : ∀ k ∈ C[a] ⊓ C[e], ρ⁻¹ * k * ρ ∈ C[a] ⊓ C[e] := fun k hk =>
    (hρK _).2 (by simpa [mul_assoc] using hk)
  have hρK'' : ∀ k ∈ C[a] ⊓ C[e], ρ * k * ρ⁻¹ ∈ C[a] ⊓ C[e] := fun k hk => (hρK k).1 hk
  have ht'a : τ * ρ * a * (τ * ρ)⁻¹ = a := by
    calc τ * ρ * a * (τ * ρ)⁻¹ = τ * (ρ * a * ρ⁻¹) * τ⁻¹ := by group
      _ = a := by rw [hρa, hτe]
  have ht'e : τ * ρ * e * (τ * ρ)⁻¹ = a * e := by
    calc τ * ρ * e * (τ * ρ)⁻¹ = τ * (ρ * e * ρ⁻¹) * τ⁻¹ := by group
      _ = (τ * a * τ⁻¹) * (τ * e * τ⁻¹) := by rw [hρe]; group
      _ = a * e := by rw [hτa, hτe, hae]
  have ht'w : τ * ρ ∈ C[w] := mul_mem hτw hρw
  have ht' : τ * ρ ∈ C[a] ⊓ C[w] := by
    refine mem_inf.2 ⟨mem_cent_iff.2 ?_, ht'w⟩
    calc τ * ρ * a = τ * ρ * a * (τ * ρ)⁻¹ * (τ * ρ) := by group
      _ = a * (τ * ρ) := by rw [ht'a]
  have ht'K : ∀ k ∈ C[a] ⊓ C[e], τ * ρ * k * (τ * ρ)⁻¹ ∈ C[a] ⊓ C[e] := fun k hk =>
    (conj_mem_inf_iff_of ht'a ht'e (mem_inf_mul_right_iff hae) k).1 hk
  have hkt' := keyId_of_mem (e := e) hA hagree ht'
  have hZa : Z a = A a := hagree a haw
  have hZe : Z e = A e := hagree e hew
  have hρX : ∀ y, y ∈ C[A a] ⊓ C[A e] ↔ (Z ρ)⁻¹ * y * (Z ρ)⁻¹⁻¹ ∈ C[A a] ⊓ C[A e] := by
    intro y
    have h1 : (Z ρ)⁻¹ * A a * (Z ρ)⁻¹⁻¹ = A a * A e := by
      calc (Z ρ)⁻¹ * A a * (Z ρ)⁻¹⁻¹ = Z ρ⁻¹ * Z a * (Z ρ⁻¹)⁻¹ := by rw [hZ.map_inv hρw, hZa]
        _ = Z (ρ⁻¹ * a * ρ⁻¹⁻¹) := (hZ.map_conj (inv_mem hρw) (mem_inf.1 haw).2).symm
        _ = Z (a * e) := by rw [inv_inv, hρa']
        _ = A a * A e := by rw [hZ.map_mul _ (mem_inf.1 haw).2 _ (mem_inf.1 hew).2, hZa, hZe]
    have h2 : (Z ρ)⁻¹ * A e * (Z ρ)⁻¹⁻¹ = A a := by
      calc (Z ρ)⁻¹ * A e * (Z ρ)⁻¹⁻¹ = Z ρ⁻¹ * Z e * (Z ρ⁻¹)⁻¹ := by rw [hZ.map_inv hρw, hZe]
        _ = Z (ρ⁻¹ * e * ρ⁻¹⁻¹) := (hZ.map_conj (inv_mem hρw) (mem_inf.1 hew).2).symm
        _ = Z a := by rw [inv_inv, hρe']
        _ = A a := hZa
    have hAae : A a * A e = A e * A a := by
      rw [← hA.map_mul _ (mem_inf.1 haw).1 _ he, ← hA.map_mul _ he _ (mem_inf.1 haw).1, hae]
    refine conj_mem_inf_iff_of h1 h2 (fun k => ?_) y
    rw [inf_comm]
    exact mem_inf_mul_right_iff hAae k
  have hdich := keyId_dichotomy (t := A a) hA he hZ hwa hAw hagree hrig hρw hρK hρX
  have hZρ : W * Z ρ = Z ρ * W := (mem_cent_iff.1 (hZ.map_mem ρ hρw)).symm
  have hZt' : W⁻¹ * Z (τ * ρ) = Z (τ * ρ) * W⁻¹ := by
    have := (mem_cent_iff.1 (hZ.map_mem _ ht'w)).symm
    calc W⁻¹ * Z (τ * ρ) = W⁻¹ * (Z (τ * ρ) * W) * W⁻¹ := by group
      _ = W⁻¹ * (W * Z (τ * ρ)) * W⁻¹ := by rw [this]
      _ = Z (τ * ρ) * W⁻¹ := by group
  have hm : KeyId A Z a e 1 (ρ⁻¹ * (τ * ρ) * ρ) := by
    have key : ∀ ε : X, ε * Z ρ = Z ρ * ε → ε⁻¹ * Z (τ * ρ) = Z (τ * ρ) * ε⁻¹ →
        KeyId A Z a e ε ρ → KeyId A Z a e 1 (ρ⁻¹ * (τ * ρ) * ρ) := by
      intro ε hε hε' hk
      have i1 := KeyId.inv hZ hρw hρK' hε hk
      have i2 := KeyId.mul hZ (inv_mem hρw) ht'w ht'K hε' i1 hkt'
      have hc : ε⁻¹ * 1 * Z ρ = Z ρ * (ε⁻¹ * 1) := by
        rw [mul_one]
        calc ε⁻¹ * Z ρ = ε⁻¹ * (Z ρ * ε) * ε⁻¹ := by group
          _ = ε⁻¹ * (ε * Z ρ) * ε⁻¹ := by rw [hε]
          _ = Z ρ * ε⁻¹ := by group
      have i3 := KeyId.mul hZ (mul_mem (inv_mem hρw) ht'w) hρw hρK'' hc i2 hk
      rwa [show ε⁻¹ * 1 * ε = 1 by group] at i3
    rcases hdich with h | h
    · exact key 1 (by group) (by group) h
    · exact key W hZρ hZt' h
  have hma : ρ⁻¹ * (τ * ρ) * ρ * a * (ρ⁻¹ * (τ * ρ) * ρ)⁻¹ = e := by
    calc ρ⁻¹ * (τ * ρ) * ρ * a * (ρ⁻¹ * (τ * ρ) * ρ)⁻¹
        = ρ⁻¹ * (τ * (ρ * (ρ * a * ρ⁻¹) * ρ⁻¹) * τ⁻¹) * ρ := by group
      _ = ρ⁻¹ * (τ * (a * e) * τ⁻¹) * ρ := by rw [hρa, hρe]
      _ = ρ⁻¹ * ((τ * a * τ⁻¹) * (τ * e * τ⁻¹)) * ρ := by group
      _ = ρ⁻¹ * (e * a) * ρ := by rw [hτa, hτe]
      _ = (ρ⁻¹ * e * ρ) * (ρ⁻¹ * a * ρ) := by group
      _ = e := by
        rw [hρe', hρa', ← mul_assoc, ha2, one_mul]
  have hn : (ρ⁻¹ * (τ * ρ) * ρ)⁻¹ * τ ∈ C[a] ⊓ C[w] := by
    refine mem_inf.2 ⟨mem_cent_iff.2 ?_, mul_mem (inv_mem (mul_mem (mul_mem (inv_mem hρw)
      ht'w) hρw)) hτw⟩
    set m := ρ⁻¹ * (τ * ρ) * ρ
    have h1 : m⁻¹ * e * m = a := by rw [← hma]; group
    calc m⁻¹ * τ * a = m⁻¹ * (τ * a * τ⁻¹) * τ := by group
      _ = m⁻¹ * e * m * (m⁻¹ * τ) := by rw [hτa]; group
      _ = a * (m⁻¹ * τ) := by rw [h1]
  have hnK : ∀ k ∈ C[a] ⊓ C[e], (ρ⁻¹ * (τ * ρ) * ρ)⁻¹ * τ * k *
      ((ρ⁻¹ * (τ * ρ) * ρ)⁻¹ * τ)⁻¹ ∈ C[a] ⊓ C[e] := by
    intro k hk
    set m := ρ⁻¹ * (τ * ρ) * ρ with hm_def
    have hme : m * e * m⁻¹ = a := by
      calc m * e * m⁻¹ = ρ⁻¹ * (τ * (ρ * (ρ * e * ρ⁻¹) * ρ⁻¹) * τ⁻¹) * ρ := by
            rw [hm_def]; group
        _ = ρ⁻¹ * (τ * (ρ * (a * e) * ρ⁻¹) * τ⁻¹) * ρ := by rw [hρe]
        _ = ρ⁻¹ * (τ * ((ρ * a * ρ⁻¹) * (ρ * e * ρ⁻¹)) * τ⁻¹) * ρ := by group
        _ = ρ⁻¹ * (τ * (e * (a * e)) * τ⁻¹) * ρ := by rw [hρa, hρe]
        _ = ρ⁻¹ * (τ * a * τ⁻¹) * ρ := by
          rw [show e * (a * e) = a by rw [← mul_assoc, ← hae, mul_assoc, he2, mul_one]]
        _ = a := by rw [hτa, hρe']
    have hn1 : m⁻¹ * τ * a * (m⁻¹ * τ)⁻¹ = a := by
      have := mem_cent_iff.1 (mem_inf.1 hn).1
      calc m⁻¹ * τ * a * (m⁻¹ * τ)⁻¹ = a * (m⁻¹ * τ) * (m⁻¹ * τ)⁻¹ := by rw [this]
        _ = a := by group
    have hn2 : m⁻¹ * τ * e * (m⁻¹ * τ)⁻¹ = e := by
      calc m⁻¹ * τ * e * (m⁻¹ * τ)⁻¹ = m⁻¹ * (τ * e * τ⁻¹) * m := by group
        _ = e := by rw [hτe, ← hme]; group
    exact (conj_mem_inf_iff_of hn1 hn2 (fun _ => Iff.rfl) k).1 hk
  have hkn := keyId_of_mem (e := e) hA hagree hn
  have := KeyId.mul hZ (mul_mem (mul_mem (inv_mem hρw) ht'w) hρw) (mem_inf.1 hn).2 hnK
    (by group) hm hkn
  rwa [mul_inv_cancel_left, mul_one] at this

end CFSG.Sporadic.Co1Patterson
