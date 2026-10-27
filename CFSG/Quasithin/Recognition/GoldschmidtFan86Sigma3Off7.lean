module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off6
public import CFSG.Quasithin.Background.PushS3Main
public import CFSG.Quasithin.Background.A1a

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x : H}

theorem perm3_gen : ∀ σ ρ : Equiv.Perm (Fin 3), σ ≠ 1 → ρ ^ 3 = 1 → ρ ≠ 1 →
    ρ = σ ∨ ρ = σ⁻¹ ∨ ρ = σ * ρ * σ⁻¹ * ρ⁻¹ := by
  decide

theorem Sig3.not_cent_mod (hx : orderOf x = 3) (hnc : ¬ ∀ q ∈ oQ H, x * q = q * x)
    (ψ : H →* Equiv.Perm (Fin 3)) (hker : ψ.ker = oQ H) {c₁ : H}
    (hc₁ : c₁ ∈ Subgroup.centralizer (oQ H : Set H)) (hψ : ψ c₁ = ψ x) : False := by
  have hq' : c₁⁻¹ * x ∈ oQ H := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hψ, inv_mul_cancel]
  have hcomm : ∀ y ∈ oQ H, c₁ * y = y * c₁ := fun y hy =>
    (Subgroup.mem_centralizer_iff.1 hc₁ y hy).symm
  have h5 : ∀ y ∈ oQ H, x * y * x⁻¹ = (c₁⁻¹ * x)⁻¹⁻¹ * y * (c₁⁻¹ * x)⁻¹ := by
    intro y hy
    have hy' : (c₁⁻¹ * x) * y * (c₁⁻¹ * x)⁻¹ ∈ oQ H :=
      (oQ H).mul_mem ((oQ H).mul_mem hq' hy) ((oQ H).inv_mem hq')
    have := hcomm _ hy'
    calc x * y * x⁻¹ = c₁ * ((c₁⁻¹ * x) * y * (c₁⁻¹ * x)⁻¹) * c₁⁻¹ := by group
      _ = ((c₁⁻¹ * x) * y * (c₁⁻¹ * x)⁻¹) * c₁ * c₁⁻¹ := by rw [this]
      _ = (c₁⁻¹ * x)⁻¹⁻¹ * y * (c₁⁻¹ * x)⁻¹ := by group
  exact hnc (x_central_of_inner hx ((oQ H).inv_mem hq') h5)

theorem Sig3.centralizer_le_Q (h : Sig3 H S) (hx : orderOf x = 3)
    (hnc : ¬ ∀ q ∈ oQ H, x * q = q * x) : Subgroup.centralizer (oQ H : Set H) ≤ oQ H := by
  intro c hc
  by_contra hcQ
  obtain ⟨ψ, -, hker⟩ := h.exists_hom
  have hker' : ψ.ker = oQ H := hker
  have hcψ : ψ c ≠ 1 := fun h1 => hcQ (hker' ▸ h1)
  have hxψ : ψ x ≠ 1 := fun h1 => Sig3.not_mem_Q_of_order hx (hker ▸ h1)
  have hx3 : (ψ x) ^ 3 = 1 := by
    have : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    rw [← map_pow, this, map_one]
  rcases perm3_gen (ψ c) (ψ x) hcψ hx3 hxψ with h1 | h1 | h1
  · exact Sig3.not_cent_mod hx hnc ψ hker hc h1.symm
  · refine Sig3.not_cent_mod hx hnc ψ hker (Subgroup.inv_mem _ hc) ?_
    rw [map_inv, ← h1]
  · have hcn : (x * c⁻¹ * x⁻¹) ∈ Subgroup.centralizer (oQ H : Set H) :=
      (inferInstance : (Subgroup.centralizer (oQ H : Set H)).Normal).conj_mem _
        (Subgroup.inv_mem _ hc) x
    refine Sig3.not_cent_mod hx hnc ψ hker (Subgroup.mul_mem _ hc hcn) ?_
    calc ψ (c * (x * c⁻¹ * x⁻¹)) = ψ c * ψ x * (ψ c)⁻¹ * (ψ x)⁻¹ := by
          simp only [map_mul, map_inv, mul_assoc]
      _ = ψ x := h1.symm

theorem Hyp3.charTwo_top (h : Hyp3 H S x) : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup H) := by
  unfold CFSG.QuasithinUnique.CharTwo
  rw [CFSG.Quasithin.pCoreOf_top]
  intro c hc
  exact h.sig.centralizer_le_Q h.ord h.nc hc.2

omit [Finite H] in
theorem isKleinFour_of_card {E : Subgroup H} [Finite E] (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) : IsKleinFour E := by
  have : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  refine ⟨h4, ?_⟩
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  refine orderOf_eq_prime ?_ hg
  exact Subtype.ext (by simpa [pow_two] using hE.2 g g.2)

theorem Hyp3.isKleinFour_nQ (h : Hyp3 H S x) : IsKleinFour ↥(nQ H x) :=
  isKleinFour_of_card (nQ_elem x) h.offender.1

theorem Sig3.not_normal_S (h : Sig3 H S) : ¬ S.Normal := by
  intro hS
  have h1 := CFSG.LieType.BorelTits.le_pCore 2 hS h.two
  have h2 := Subgroup.card_le_of_le h1
  have h3 := h.card_S
  have : 0 < Nat.card (CFSG.Open.pCore 2 H) := Nat.card_pos
  omega

theorem Hyp3.card_oddOrder (h : Hyp3 H S x) :
    Nat.card ↥(CFSG.QuasithinUnique.Setup.oddOrderSubgroup (⊤ : Subgroup H)) = 12 := by
  obtain ⟨-, a, haJ, haS, -, n, hn, hne⟩ := h.offender
  have hx3 := mul_mul_eq_one_of_orderOf h.ord
  have hNn := h.sig.nQ_normal h.ord
  refine CFSG.Quasithin.F6.PushS3.card_oddOrderSubgroup_eq_twelve_of_campbell ⊤ S (nQ H x) x a
    le_top h.sig.two ?_ ?_ le_top h.isKleinFour_nQ ?_ (Subgroup.mem_top x) h.ord
    (fun n hn hf => nQ_fix hx3 hn hf) haS ⟨n, hn, hne⟩ h.charTwo_top ?_ ?_
  · rw [Subgroup.relIndex_top_right]
    exact h.sig.index_S
  · intro hle
    exact h.sig.not_normal_S (Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 hle))
  · exact top_le_iff.2 (Subgroup.normalizer_eq_top_iff.2 hNn)
  · intro C hCS hCne hCc hle
    exact hCne (h.no C hCS hCc (Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 hle)))
  · intro hle
    apply hne
    have := Subgroup.mem_centralizer_iff.1 (hle haJ) n hn
    rw [← this]
    group

end CFSG.Quasithin.Fan86.Sigma3
