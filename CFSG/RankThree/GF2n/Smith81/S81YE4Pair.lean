module

public import CFSG.RankThree.GF2n.Smith81.S81YE4Def
public import CFSG.RankThree.GF2n.Smith81.S81YE5Odd
public import CFSG.RankThree.GF2n.Smith81.S81D6Bruhat
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe7

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5
open scoped commutatorElement

variable
  {K : Type} [Field K]

theorem e4_root_sum_fin : ∀ k : Fin 126, (Tag.rootCertificate .E7).root k node1 ≠ 0 →
    (Tag.rootCertificate .E7).root k ≠ theta → (Tag.rootCertificate .E7).root k ≠ -theta →
    (∃ k' : Fin 126, (Tag.rootCertificate .E7).root k' = (Tag.rootCertificate .E7).root k + theta) ∨
    (∃ k' : Fin 126, (Tag.rootCertificate .E7).root k' =
      (Tag.rootCertificate .E7).root k + -theta) := by
  decide +kernel

theorem e4_root_sum {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (h1 : γ node1 ≠ 0)
    (h2 : γ ≠ theta) (h3 : γ ≠ -theta) : IsRoot .E7 (γ + theta) ∨ IsRoot .E7 (γ + -theta) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hroot : ∀ k : Fin 126, IsRoot .E7 ((Tag.rootCertificate .E7).root k) := fun k =>
    RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)
  refine (forall_isRoot_iff (fun γ => γ node1 ≠ 0 → γ ≠ theta → γ ≠ -theta →
    IsRoot .E7 (γ + theta) ∨ IsRoot .E7 (γ + -theta))).2 (fun k hk1 hk2 hk3 => ?_) γ hγ h1 h2 h3
  rcases e4_root_sum_fin k hk1 hk2 hk3 with ⟨k', hk'⟩ | ⟨k', hk'⟩
  · exact Or.inl (by rw [← hk']; exact hroot k')
  · exact Or.inr (by rw [← hk']; exact hroot k')

theorem e4_theta_comm_zero [CharP K 2] {a c : K}
    (h : e7Data_valid.xm K theta a * e7Data_valid.xm K (-theta) c =
      e7Data_valid.xm K (-theta) c * e7Data_valid.xm K theta a) : a * c = 0 := by
  have h' : e7Data_valid.xu K theta a * e7Data_valid.xu K (-theta) c =
      e7Data_valid.xu K (-theta) c * e7Data_valid.xu K theta a := congrArg Subtype.val h
  rw [xu_theta a, xu_neg_theta c, ← map_mul, ← map_mul] at h'
  have hinj : Function.Injective (jHom (K := K)) :=
    (injective_iff_map_eq_one (jHom (K := K))).2 fun P hP => jHom_eq_one_imp P hP
  have hm := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) K =>
    (m : Matrix (Fin 2) (Fin 2) K) 0 0) (hinj h')
  simp [Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slLower_val,
    MinData.Valid.slUpper_val, Matrix.mul_apply, Fin.sum_univ_two] at hm
  rcases hm with h0 | h0 <;> simp [h0]

theorem perp_of_xu_mem_Lam [CharP K 2] {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) {b : K}
    (hb : b ≠ 0) (h : (e7Data_valid.xu K δ b : (Module.End K (V K))ˣ) ∈ Lam K) : δ ∈ Perp := by
  rw [perp_iff]
  refine ⟨hδ, ?_⟩
  by_contra hn
  have hjθ : (e7Data_valid.xu K theta 1 : (Module.End K (V K))ˣ) ∈ Jgrp K := by
    unfold Jgrp
    exact Subgroup.subset_closure ⟨1, Or.inl rfl⟩
  have hjm : (e7Data_valid.xu K (-theta) 1 : (Module.End K (V K))ˣ) ∈ Jgrp K := by
    unfold Jgrp
    exact Subgroup.subset_closure ⟨1, Or.inr rfl⟩
  have cθ := Lam_commute_J h hjθ
  have cm := Lam_commute_J h hjm
  by_cases hδθ : δ = theta
  · subst hδθ
    have h0 := e4_theta_comm_zero (a := b) (c := 1) (Subtype.ext cm)
    exact hb (by simpa using h0)
  by_cases hδmθ : δ = -theta
  · subst hδmθ
    have h0 := e4_theta_comm_zero (a := 1) (c := b) (Subtype.ext cθ.symm)
    exact hb (by simpa using h0)
  have hcomP : ⁅e7Data_valid.xm K δ b, e7Data_valid.xm K theta 1⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subtype.ext cθ)
  have hcomM : ⁅e7Data_valid.xm K δ b, e7Data_valid.xm K (-theta) 1⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subtype.ext cm)
  rcases e4_root_sum hδ hn hδθ hδmθ with hr | hr
  · have hne : δ + theta ≠ 0 := fun h0 => hδmθ (eq_neg_of_add_eq_zero_left h0)
    obtain ⟨σ, hσ, hc⟩ := (e7Data_valid.commutator_xm K hδ isRoot_theta hne).1 hr
    have h1 : e7Data_valid.xm K (δ + theta) (σ * b * 1) = e7Data_valid.xm K (δ + theta) 0 := by
      rw [e7Data_valid.xm_zero, ← hc b 1]
      exact hcomP
    have h2 := e7Data_valid.xm_injective K hr h1
    have hσ0 : σ ≠ 0 := by
      rcases hσ with h | h <;> simp [h]
    apply hb
    rw [mul_one] at h2
    exact (mul_eq_zero.1 h2).resolve_left hσ0
  · have hne : δ + -theta ≠ 0 := fun h0 => hδθ (by
      have := eq_neg_of_add_eq_zero_left h0
      rwa [neg_neg] at this)
    obtain ⟨σ, hσ, hc⟩ :=
      (e7Data_valid.commutator_xm K hδ (isRoot_neg isRoot_theta) hne).1 hr
    have h1 : e7Data_valid.xm K (δ + -theta) (σ * b * 1) = e7Data_valid.xm K (δ + -theta) 0 := by
      rw [e7Data_valid.xm_zero, ← hc b 1]
      exact hcomM
    have h2 := e7Data_valid.xm_injective K hr h1
    have hσ0 : σ ≠ 0 := by
      rcases hσ with h | h <;> simp [h]
    apply hb
    rw [mul_one] at h2
    exact (mul_eq_zero.1 h2).resolve_left hσ0

theorem e4V_pairNF [CharP K 2] {x y : G7 K} (hx : IsRootEltL K x) (hy : IsRootEltL K y) :
    ∃ e : G7 K, e ∈ LG K ∧ ∃ (a b : K) (δ : Fin (Tag.rank .E7) → ℤ), a ≠ 0 ∧ b ≠ 0 ∧ δ ∈ Perp ∧
      e * x * e⁻¹ = e7Data_valid.xm K theta4 a ∧ e * y * e⁻¹ = e7Data_valid.xm K δ b := by
  have hyL : (y : (Module.End K (V K))ˣ) ∈ Lam K := by
    obtain ⟨h, β, c, hh, hβ, -, hy_eq⟩ := hy
    rw [hy_eq]
    show (h : (Module.End K (V K))ˣ) * e7Data_valid.xu K β c * (h : (Module.End K (V K))ˣ)⁻¹ ∈ Lam K
    exact mul_mem (mul_mem hh (xu_mem_Lam hβ c)) (inv_mem hh)
  obtain ⟨p, hp, a, ha, rfl⟩ := hx.exists_conj_theta4
  obtain ⟨q, hq, d, hd, rfl⟩ := hy.exists_conj_theta4
  have hpq : ((p⁻¹ * q : G7 K) : (Module.End K (V K))ˣ) ∈ Lam K := by
    have : ((p⁻¹ * q : G7 K) : (Module.End K (V K))ˣ) =
        (p : (Module.End K (V K))ˣ)⁻¹ * (q : (Module.End K (V K))ˣ) := rfl
    rw [this]
    exact mul_mem (inv_mem hp) hq
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := Lam_bruhat hpq
  obtain ⟨d', hconj₂, hdd⟩ := borL_conj_xm_theta4 hb₂ d
  obtain ⟨γ', c'', hγ', hconjW, hcc⟩ := nW_conj_xm_theta4 w d'
  obtain ⟨a', hconj₁, haa⟩ := borL_conj_xm_theta4 (inv_mem hb₁) a
  have hq' : q = p * (b₁ * nW K w * b₂) := by
    rw [← hg, mul_inv_cancel_left]
  have hx_e : b₁⁻¹ * p⁻¹ * (p * e7Data_valid.xm K theta4 a * p⁻¹) * (b₁⁻¹ * p⁻¹)⁻¹
      = e7Data_valid.xm K theta4 a' := by
    rw [← hconj₁]
    group
  have hy_e : b₁⁻¹ * p⁻¹ * (q * e7Data_valid.xm K theta4 d * q⁻¹) * (b₁⁻¹ * p⁻¹)⁻¹
      = e7Data_valid.xm K γ' c'' := by
    rw [hq']
    calc b₁⁻¹ * p⁻¹ * (p * (b₁ * nW K w * b₂) * e7Data_valid.xm K theta4 d
          * (p * (b₁ * nW K w * b₂))⁻¹) * (b₁⁻¹ * p⁻¹)⁻¹
        = nW K w * (b₂ * e7Data_valid.xm K theta4 d * b₂⁻¹) * (nW K w)⁻¹ := by group
      _ = nW K w * e7Data_valid.xm K theta4 d' * (nW K w)⁻¹ := by rw [hconj₂]
      _ = e7Data_valid.xm K γ' c'' := hconjW
  obtain ⟨u, hu, t, ht, hb₁eq⟩ := mem_BorL_iff.1 hb₁
  have huL : (u : (Module.End K (V K))ˣ) ∈ Lam K := UL_le_Lam (Subgroup.mem_comap.1 hu)
  obtain ⟨s₁, hs₁, hts₁⟩ := tor_conj_xm_theta4 ht
  obtain ⟨s₂, hs₂, hts₂⟩ := tor_conj_xm ht hγ'
  have hc''0 : c'' ≠ 0 := hcc (hdd hd)
  have heL : ((u⁻¹ * p⁻¹ : G7 K) : (Module.End K (V K))ˣ) ∈ Lam K := by
    have : ((u⁻¹ * p⁻¹ : G7 K) : (Module.End K (V K))ˣ) =
        (u : (Module.End K (V K))ˣ)⁻¹ * (p : (Module.End K (V K))ˣ)⁻¹ := rfl
    rw [this]
    exact mul_mem (inv_mem huL) (inv_mem hp)
  have he : u⁻¹ * p⁻¹ ∈ LG K := mem_LG.2 heL
  have hyLG : q * e7Data_valid.xm K theta4 d * q⁻¹ ∈ LG K := mem_LG.2 hyL
  have hyconj : u⁻¹ * p⁻¹ * (q * e7Data_valid.xm K theta4 d * q⁻¹) * (u⁻¹ * p⁻¹)⁻¹
      = e7Data_valid.xm K γ' (s₂ * c'') := by
    rw [← hts₂ c'', ← hy_e, hb₁eq]
    group
  have hmem : (e7Data_valid.xu K γ' (s₂ * c'') : (Module.End K (V K))ˣ) ∈ Lam K := by
    have h1 : u⁻¹ * p⁻¹ * (q * e7Data_valid.xm K theta4 d * q⁻¹) * (u⁻¹ * p⁻¹)⁻¹ ∈ LG K :=
      mul_mem (mul_mem he hyLG) (inv_mem he)
    rw [hyconj] at h1
    exact mem_LG.1 h1
  have hδ := perp_of_xu_mem_Lam hγ' (mul_ne_zero hs₂ hc''0) hmem
  refine ⟨u⁻¹ * p⁻¹, he, s₁ * a', s₂ * c'', γ', mul_ne_zero hs₁ (haa ha),
    mul_ne_zero hs₂ hc''0, hδ, ?_, hyconj⟩
  rw [← hts₁ a', ← hx_e, hb₁eq]
  group

end CFSG.RankThree.GF2n.Smith81.RootGenE4
