module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCOXb
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFin

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.L216 CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL)
open scoped MatrixGroups

theorem conj_mem_X_pCoreOf {G : Type} [Group G] [Finite G] {T M L V X : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4)
    (hF : Nat.card F = 16) {ψ : ↥(autOn L V) ≃* SL(2, F)}
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hXL : X ≤ L) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G))
    {x : G} (hx : x ∈ X) : g * x * g⁻¹ ∈ X ⊔ pCoreOf 2 L := by
  have hLV := h.L_le_normalizer
  have hC := h.sup_inf_centralizer_le_T_ch6
  have hVL := h.module.2.2
  have hgup := coordHom_upper hLV ψ hψ ⟨g, hgL⟩ hgN
  have hsup : ∀ y ∈ Xb hLV ψ hXL, (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    fun y hy => Xb_le_borel hLV ψ hXL (Ub_ne_bot hLV ψ hXL hF hC hψ hTX hX5) hC hψ hXn hy
  obtain ⟨s, hs, hζ5, hζ1⟩ := exists_zeta hLV ψ hXL hF hC hψ hTX hXn hX5
  have hU : ∀ b : F, unipSL b ∈ Xb hLV ψ hXL := fun b =>
    Ub_le_Xb hLV ψ hXL (unip_mem_Ub hLV ψ hXL hF hC hψ hXn
      (Ub_ne_bot hLV ψ hXL hF hC hψ hTX hX5) hs (hsup s hs) hζ5 hζ1 b)
  have hyL : g * x * g⁻¹ ∈ L := L.mul_mem (L.mul_mem hgL (hXL hx)) (L.inv_mem hgL)
  have hxX : coordHom hLV ψ ⟨x, hXL hx⟩ ∈ Xb hLV ψ hXL :=
    (mem_Xb_iff hLV ψ hXL _).mpr ⟨⟨x, hx⟩, rfl⟩
  have hconj := conj_borel_mem_Xb hLV ψ hXL hU hsup hgup hxX
  have hmemy : coordHom hLV ψ ⟨g * x * g⁻¹, hyL⟩ ∈ Xb hLV ψ hXL := by
    have e : coordHom hLV ψ ⟨g * x * g⁻¹, hyL⟩ =
        coordHom hLV ψ ⟨g, hgL⟩ * coordHom hLV ψ ⟨x, hXL hx⟩ *
          (coordHom hLV ψ ⟨g, hgL⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact hconj
  obtain ⟨x', hx'⟩ := (mem_Xb_iff hLV ψ hXL _).mp hmemy
  set x'L : ↥L := ⟨(x' : G), hXL x'.2⟩ with hx'L
  set ℓ' : ↥L := x'L⁻¹ * ⟨g * x * g⁻¹, hyL⟩ with hℓ'
  have hker : coordHom hLV ψ ℓ' = 1 := by
    have hx'' : coordHom hLV ψ x'L = coordHom hLV ψ ⟨g * x * g⁻¹, hyL⟩ := hx'
    rw [hℓ', map_mul, map_inv, hx'', inv_mul_cancel]
  have hcent := (coordHom_eq_one_iff hLV ψ ℓ').mp hker
  have hpc : (ℓ' : G) ∈ pCoreOf 2 L :=
    h.toHyp5_0_1.inf_centralizer_le hLV hVL ⟨ℓ'.2, hcent⟩
  have hfac : g * x * g⁻¹ = (x' : G) * (ℓ' : G) := by
    rw [hℓ', hx'L]
    simp
  rw [hfac]
  exact (X ⊔ pCoreOf 2 L).mul_mem (le_sup_left (a := X) (b := pCoreOf 2 L) x'.2)
    (le_sup_right (a := X) (b := pCoreOf 2 L) hpc)

theorem l216NormalizerFact_holds : L216NormalizerFact := by
  intro G _ _ T M L V X h horth hXL _hX2 hX5 hXn hTX
  obtain ⟨F, _, _, _, hF, ψ, Y, -, -, -, -, hψ⟩ :=
    IsOrthCh5.exists_sylowCoord (m := 2) (show IsOrthCh5 L V (2 * 2) from horth)
      h.isSylowTwoOf_inf_ch6
  have hF16 : Nat.card F = 16 := by rw [hF]; norm_num
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgN, hgL⟩ := hg
  apply mem_normalizer_of_conj_mem
  intro k hk
  rw [Subgroup.sup_eq_closure] at hk
  induction hk using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hyX | hyO
    · exact conj_mem_X_pCoreOf h horth hF16 hψ hXL hX5 hXn hTX hgL hgN hyX
    · exact le_sup_right (a := X) (b := pCoreOf 2 L) ((Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hgL) _).mp hyO)
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact (X ⊔ pCoreOf 2 L).mul_mem iha ihb
  | inv a _ iha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact (X ⊔ pCoreOf 2 L).inv_mem iha

end CFSG.Quasithin.H13.T614
