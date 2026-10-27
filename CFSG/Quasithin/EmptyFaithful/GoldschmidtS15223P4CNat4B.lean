module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat4A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace S15223P4

namespace C

namespace Nat4

theorem map_eq_top_of_normal_of_mul {P Y : Type} [Group P] [Group Y] [IsSimpleGroup Y]
    {Φ : P →* Y} (hΦ : Function.Surjective Φ) {N : Subgroup P} (hN : N.Normal)
    {V : Subgroup Y} (hV : V ≠ ⊤) (h : ∀ p : P, ∃ n ∈ N, ∃ u : P, Φ u ∈ V ∧ p = n * u) :
    N.map Φ = ⊤ := by
  have := hN.map Φ hΦ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map Φ) with h0 | h1
  · exfalso
    apply hV
    rw [eq_top_iff]
    intro y _
    obtain ⟨p, rfl⟩ := hΦ y
    obtain ⟨n, hn, u, hu, rfl⟩ := h p
    have hΦn : Φ n = 1 := by
      have := Subgroup.mem_map_of_mem Φ hn
      rw [h0] at this
      simpa using this
    rw [map_mul, hΦn, one_mul]
    exact hu
  · exact h1

theorem Ut_four_ne_top : Ut 4 ≠ ⊤ := by
  intro h
  have hUt : Nat.card ↥(Ut 4) = 64 := by
    have := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular (K := ZMod 2) 4
    rw [Nat.card_zmod] at this
    simpa using this
  have h2 := CFSG.QuasithinUnique.Bridge.card_sl4
  rw [h, Subgroup.card_top] at hUt
  have h3 : (64 : ℕ) = 20160 := hUt.symm.trans h2
  omega

end Nat4

variable {G : Type} [Group G] [Finite G] {T Mc M H : Subgroup G}
  {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G} {W : ℕ → Subgroup G}

namespace CData

variable (d : CData T Mc M H B₀ I X) (hF : ¬ X ≤ Mc)
  (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) 5 W)
  (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1)

include d hF D hZW

theorem rho_mem_QI_of_centralizer {x : G} (hx : x ∈ X)
    (hC : x ∈ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) :
    D.rho ⟨x, Subgroup.mem_sup_left hx⟩ ∈ QI 5 {1} := by
  have hF' := d.facts15128 hF
  have h := (FLc.centralizer_zU_eq hF'.decomp hF'.ZU hF'.ULU x hx).1 hC
  have h' : x ∈ Subgroup.centralizer (W 1 : Set G) := by rw [← hZW]; exact h
  rw [mem_flagStabilizer]
  intro j hj
  rw [Set.mem_singleton_iff] at hj
  subst hj
  exact (D.mem_normalizer_W_iff le_rfl (by norm_num) _).1
    (Subgroup.centralizer_le_normalizer _ h')

@[expose] noncomputable def rhoK : ↥(kI T Mc M B₀) →* ↥(QI 5 {1}) :=
  (D.rho.comp (Subgroup.inclusion (d.kI_le_X.trans le_sup_left))).codRestrict (QI 5 {1})
    fun k => d.rho_mem_QI_of_centralizer hF D hZW (d.kI_le_X k.2)
      (kI_le_centralizer T Mc M B₀ k.2)

theorem coe_rhoK (k : ↥(kI T Mc M B₀)) :
    ((d.rhoK hF D hZW k : ↥(QI 5 {1})) : SLt 5) =
      D.rho ⟨(k : G), Subgroup.mem_sup_left (d.kI_le_X k.2)⟩ := rfl

theorem exists_lift (p : ↥(QI 5 {1})) :
    ∃ a : ↥X, D.rho ⟨(a : G), Subgroup.mem_sup_left a.2⟩ = p.1 ∧
      (a : G) ∈ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
  obtain ⟨a, ha⟩ := D.surj p.1
  have hρa : D.rho ⟨(a : G), Subgroup.mem_sup_left a.2⟩ = p.1 := by rw [D.rho_apply_L, ha]
  exact ⟨a, hρa, d.mem_centralizer_of_rho hF D (by norm_num) hZW a.2 (by rw [hρa]; exact p.2)⟩

theorem normal_range_rhoK : (d.rhoK hF D hZW).range.Normal := by
  refine ⟨?_⟩
  rintro _ ⟨k, rfl⟩ p
  obtain ⟨a, hρa, haC⟩ := d.exists_lift hF D hZW p
  have hN : (a : G) ∈ Subgroup.normalizer (kI T Mc M B₀ : Set G) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_oPrimeResidualOf1516 3 _)) haC
  refine ⟨⟨(a : G) * k * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.1 hN k).1 k.2⟩, ?_⟩
  apply Subtype.ext
  have key : ∀ x y : ↥(X ⊔ sOf152 T Mc M B₀),
      D.rho (x * y * x⁻¹) = D.rho x * D.rho y * (D.rho x)⁻¹ := fun x y => by simp
  rw [coe_rhoK]
  have e := key ⟨(a : G), Subgroup.mem_sup_left a.2⟩
    ⟨(k : G), Subgroup.mem_sup_left (d.kI_le_X k.2)⟩
  rw [hρa] at e
  exact e

theorem exists_mul_decomp (p : ↥(QI 5 {1})) :
    ∃ n ∈ (d.rhoK hF D hZW).range, ∃ u : ↥(QI 5 {1}),
      Nat4.blkHom 4 u ∈ Ut 4 ∧ p = n * u := by
  obtain ⟨a, hρa, haC⟩ := d.exists_lift hF D hZW p
  have haK : (a : G) ∈ kI T Mc M B₀ ⊔ (sOf152 T Mc M B₀ ⊓ X) :=
    d.inf_centralizer_le_kI_sup ⟨a.2, haC⟩
  have hSK : sOf152 T Mc M B₀ ⊓ X ≤ Subgroup.normalizer (kI T Mc M B₀ : Set G) := fun s hs =>
    d.T_le_normalizer_kI (S_le_T152 hs.1)
  obtain ⟨k, hk, s, hs, hks⟩ : ∃ k ∈ kI T Mc M B₀, ∃ s ∈ sOf152 T Mc M B₀ ⊓ X, (a : G) = k * s := by
    have : (a : G) ∈ ((kI T Mc M B₀ : Subgroup G) : Set G) *
        ((sOf152 T Mc M B₀ ⊓ X : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSK]
      exact haK
    obtain ⟨k, hk, s, hs, e⟩ := this
    exact ⟨k, hk, s, hs, e.symm⟩
  refine ⟨d.rhoK hF D hZW ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩,
    ⟨D.rho ⟨s, Subgroup.mem_sup_right hs.1⟩, Ut_le_QI 5 {1} (D.rho_S_le_Ut hs.1)⟩,
    Nat4.blkHom_mem_Ut (D.rho_S_le_Ut hs.1), ?_⟩
  apply Subtype.ext
  rw [← hρa]
  show D.rho ⟨a, _⟩ = D.rho ⟨k, _⟩ * D.rho ⟨s, _⟩
  rw [← map_mul]
  exact congrArg D.rho (Subtype.ext hks)

@[expose] noncomputable def psi : ↥(kI T Mc M B₀) →* SLt 4 :=
  (Nat4.blkHom 4).comp (d.rhoK hF D hZW)

theorem psi_surjective : Function.Surjective (d.psi hF D hZW) := by
  have : IsSimpleGroup (SLt 4) := CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 4 (by norm_num)
  have h := Nat4.map_eq_top_of_normal_of_mul (Nat4.blkHom_surjective 4)
    (d.normal_range_rhoK hF D hZW) Nat4.Ut_four_ne_top (d.exists_mul_decomp hF D hZW)
  rw [← MonoidHom.range_eq_top, psi, MonoidHom.range_comp]
  exact h

theorem psi_ker_isPGroup : IsPGroup 2 ↥(d.psi hF D hZW).ker := by
  intro x
  have hx : Nat4.blkHom 4 (d.rhoK hF D hZW x.1) = 1 := x.2
  have hsq := Nat4.mul_self_eq_one_of_blkHom_eq_one hx
  set y : ↥(X ⊔ sOf152 T Mc M B₀) :=
    ⟨(x.1 : G), Subgroup.mem_sup_left (d.kI_le_X x.1.2)⟩ with hy
  have hsq' : D.rho y * D.rho y = 1 := hsq
  have h1 : D.rho (y * y) = 1 := by rw [map_mul]; exact hsq'
  have hS : ((y * y : ↥(X ⊔ sOf152 T Mc M B₀)) : G) ∈ sOf152 T Mc M B₀ := D.ker_le_S h1
  obtain ⟨j, hj⟩ := D.S2 ⟨((y * y : ↥(X ⊔ sOf152 T Mc M B₀)) : G), hS⟩
  refine ⟨j + 1, ?_⟩
  have hj' : ((x.1 : G) * x.1) ^ 2 ^ j = 1 := by
    have := congrArg (fun z : ↥(sOf152 T Mc M B₀) => ((z : ↥(sOf152 T Mc M B₀)) : G)) hj
    simpa [hy] using this
  apply Subtype.ext
  apply Subtype.ext
  show (x.1 : G) ^ 2 ^ (j + 1) = 1
  rw [pow_succ', pow_mul, sq]
  exact hj'

end CData

end C

end S15223P4

end CFSG.Quasithin
