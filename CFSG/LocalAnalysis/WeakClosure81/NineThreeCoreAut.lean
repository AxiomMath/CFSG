module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeOddFrame
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonClass

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.ClassicalInvolution.Asc77 Subgroup
open scoped Pointwise commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {m : ℕ} {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}

private lemma nine3_zmodRefl_self3 (c : ZMod 3) : zmodRefl 3 c * zmodRefl 3 c = 1 := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply, Equiv.Perm.one_apply]
  ring

private lemma nine3_zmodRefl_conj3 (s a : ZMod 3) :
    zmodRefl 3 s * zmodRefl 3 a * zmodRefl 3 s = zmodRefl 3 (2 * s - a) := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply]
  ring

private lemma nine3_zmod3_eq (a b c : ZMod 3) (hba : b ≠ a) (hca : c ≠ a) (hbc : b ≠ c) :
    c = 2 * a - b := by
  revert a b c
  decide

private lemma nine3_zmod3_add_one_ne (a : ZMod 3) : a + 1 ≠ a := by
  revert a
  decide

private lemma nine3_fibre_nonempty (h : Nine3OddFrame 3 m π D) (hm : 0 < m) (a : ZMod 3) :
    ∃ f : Γ, f ∈ D ∧ π f = zmodRefl 3 a := by
  have hpos : 0 < Nat.card {x : Γ // x ∈ D ∧ π x = zmodRefl 3 a} := by
    rw [h.card a]
    exact hm
  obtain ⟨⟨f, hfD, hfpi⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨f, hfD, hfpi⟩

theorem nine3OddFrame_cent_eq (h : Nine3OddFrame 3 m π D) {a : ZMod 3} {d : Γ}
    (hd : d ∈ nine3FibreSet π D a) : Star3T.cent D d = nine3FibreSet π D a := by
  ext e
  constructor
  · intro he
    obtain ⟨c, hc⟩ := h.refl e he.1
    refine ⟨he.1, ?_⟩
    by_contra hca
    have hcne : c ≠ a := fun h' => hca (by rw [hc, h'])
    have hne : π d ≠ π e := by
      rw [hd.2, hc]
      intro hh
      exact hcne (zmodRefl_inj (p := 3) (by norm_num) (by norm_num) hh).symm
    have h3 := h.pow d hd.1 e he.1 hne
    have h2 : (d * e) * (d * e) = 1 := by
      calc (d * e) * (d * e)
          = d * (e * (d * e)) := by rw [mul_assoc d e (d * e)]
        _ = d * ((e * d) * e) := by rw [← mul_assoc e d e]
        _ = d * ((d * e) * e) := by rw [he.2]
        _ = d * (d * (e * e)) := by rw [mul_assoc d e e]
        _ = d * (d * 1) := by rw [h.sq e he.1]
        _ = d * d := by rw [mul_one]
        _ = 1 := h.sq d hd.1
    have h1 : d * e = 1 := by
      have e3 : (d * e) ^ 3 = (d * e) ^ 2 * (d * e) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one]
      rw [e3, pow_two, h2, one_mul] at h3
      exact h3
    have heq : e = d := by
      have := eq_inv_of_mul_eq_one_right h1
      rwa [inv_eq_of_mul_eq_one_right (h.sq d hd.1)] at this
    exact hne (by rw [heq])
  · intro he
    exact ⟨he.1, h.comm e he.1 d hd.1 (by rw [he.2, hd.2])⟩

theorem nine3OddFrame_conj_transitive (h : Nine3OddFrame 3 m π D) (hm : 0 < m) (a : ZMod 3)
    {d e : Γ} (hd : d ∈ D) (he : e ∈ D) (hda : π d ≠ zmodRefl 3 a) (hea : π e ≠ zmodRefl 3 a) :
    ∃ s ∈ Subgroup.closure (nine3FibreSet π D a), s * d * s⁻¹ = e := by
  obtain ⟨b, hb⟩ := h.refl d hd
  obtain ⟨c, hc⟩ := h.refl e he
  have hba : b ≠ a := fun h' => hda (by rw [hb, h'])
  have hca : c ≠ a := fun h' => hea (by rw [hc, h'])
  by_cases hbc : b = c
  · have hc' : π e = zmodRefl 3 b := hc.trans (by rw [hbc])
    obtain ⟨z, hz, hzconj⟩ := h.trans b a hba d hd hb e he hc'
    exact ⟨z, hz.1, hzconj⟩
  · have hc_eq : c = 2 * a - b := nine3_zmod3_eq a b c hba hca hbc
    obtain ⟨f, hfD, hfpi⟩ := nine3_fibre_nonempty h hm a
    have hfmem : f ∈ nine3FibreSet π D a := ⟨hfD, hfpi⟩
    have hconjD : f * d * f⁻¹ ∈ D := h.conj d hd f
    have hconjpi : π (f * d * f⁻¹) = zmodRefl 3 c := by
      rw [map_mul, map_mul, map_inv, hfpi, hb,
        inv_eq_of_mul_eq_one_right (nine3_zmodRefl_self3 a), nine3_zmodRefl_conj3 a b,
        hc_eq]
    obtain ⟨z, hz, hzconj⟩ := h.trans c a hca (f * d * f⁻¹) hconjD hconjpi e he hc
    refine ⟨z * f, Subgroup.mul_mem _ hz.1 (Subgroup.subset_closure hfmem), ?_⟩
    calc (z * f) * d * (z * f)⁻¹ = z * (f * d * f⁻¹) * z⁻¹ := by group
      _ = e := hzconj

theorem nine3OddFrame_aut_eq_conj (h : Nine3OddFrame 3 m π D) (hm : 0 < m) (a : ZMod 3)
    {φ : Γ →* Γ} (hinj : Function.Injective φ) (hD : ∀ d ∈ D, φ d ∈ D)
    (hfix : ∀ d ∈ nine3FibreSet π D a, φ d = d) :
    ∃ s ∈ Subgroup.closure (nine3FibreSet π D a), ∀ y, φ y = s * y * s⁻¹ := by
  obtain ⟨d₀, hd0D, hd0pi⟩ := nine3_fibre_nonempty h hm a
  have hd0mem : d₀ ∈ nine3FibreSet π D a := ⟨hd0D, hd0pi⟩
  let b : ZMod 3 := a + 1
  have hba : b ≠ a := nine3_zmod3_add_one_ne a
  obtain ⟨d₁, hd1D, hd1pi⟩ := nine3_fibre_nonempty h hm b
  have hpiba : zmodRefl 3 b ≠ zmodRefl 3 a := fun hh =>
    hba (zmodRefl_inj (p := 3) (by norm_num) (by norm_num) hh)
  have hne : π d₀ ≠ π d₁ := by
    rw [hd0pi, hd1pi]
    intro hh
    exact hpiba hh.symm
  have hnotconn : ¬ Star3T.Conn D d₀ d₁ := nine3OddFrame_not_conn h hd0D hd1D hne
  have hplane : Star3T.IsPlane D d₀ d₁ (d₀ * d₁ * d₀) :=
    Star3T.isPlane_of_not_conn hd0D hd1D hnotconn
  have htop : Subgroup.closure (insert d₁ (Star3T.cent D d₀)) = ⊤ :=
    Star3T.IsTT.closure_insert_cent_eq_top (nine3OddFrame_isTT h) (nine3OddFrame_isStar h) hplane
  rw [nine3OddFrame_cent_eq h hd0mem] at htop
  have hphi_notmem : φ d₁ ∉ nine3FibreSet π D a := by
    intro hmem
    have hfix' : φ (φ d₁) = φ d₁ := hfix (φ d₁) hmem
    have hEq : φ d₁ = d₁ := hinj hfix'
    have hpid1 : π d₁ = zmodRefl 3 a := by rw [← hEq]; exact hmem.2
    exact hpiba (by rw [← hd1pi, hpid1])
  have hphi_pi : π (φ d₁) ≠ zmodRefl 3 a := fun hh =>
    hphi_notmem ⟨hD d₁ hd1D, hh⟩
  have hd1_a : π d₁ ≠ zmodRefl 3 a := by rw [hd1pi]; exact hpiba
  obtain ⟨s, hs, hsd⟩ :=
    nine3OddFrame_conj_transitive h hm a hd1D (hD d₁ hd1D) hd1_a hphi_pi
  let ψ : Γ →* Γ := (MulAut.conj s).toMonoidHom
  have hψ : ∀ y, ψ y = s * y * s⁻¹ := fun y => MulAut.conj_apply s y
  have hEqOn : Set.EqOn φ ψ (insert d₁ (nine3FibreSet π D a)) := by
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · rw [hx, hψ d₁]
      exact hsd.symm
    · rw [hfix x hx, hψ x]
      have hcomm : s * x = x * s := by
        have hle : Subgroup.closure (nine3FibreSet π D a) ≤
            Subgroup.centralizer ({x} : Set Γ) := by
          rw [Subgroup.closure_le]
          intro y hy
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (h.comm y hy.1 x hx.1 (by rw [hy.2, hx.2]))
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hs)
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hphi_eq : φ = ψ := MonoidHom.eq_of_eqOn_dense htop hEqOn
  exact ⟨s, hs, fun y => by rw [hphi_eq, hψ y]⟩

end CFSG.LocalAnalysis.WeakClosure81
