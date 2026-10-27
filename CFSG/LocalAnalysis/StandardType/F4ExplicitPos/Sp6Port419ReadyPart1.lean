module

public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl

@[expose] public section

public section

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType.F4ExplicitPos.Neighbors

variable {X : Type} [Group X] [Finite X]

variable {n f : ℕ} {p : ℕ}

variable {G₀ B₁ D J L : Subgroup X} {x : X}

theorem f4_neighbor_normalized_by_B1
    {ψ : (ggU .F4 n f).K →* X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x)
    {e : X} (he : e ∈ D) {K : Subgroup X}
    (_hKG : K ≤ G₀)
    (hKcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({e} : Set X)))
    (hJK : J ≤ K) :
    B₁ ≤ Subgroup.normalizer (K : Set X) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hJq : CFSG.Assembly.IsQuasisimple J := h15.2.2
  intro b hb
  have hbe : b * e = e * b := by
    have : IsMulCommutative B₁ := h9.1
    have hbc := mul_comm' (⟨b, hb⟩ : B₁) (⟨e, h11 he⟩ : B₁)
    simpa using congrArg (fun z : B₁ => (z : X)) hbc
  have hbe' : b * e * b⁻¹ = e := by
    rw [hbe, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : (Subgroup.centralizer ({e} : Set X)).map (MulAut.conj b).toMonoidHom =
      Subgroup.centralizer ({e} : Set X) := by
    rw [map_conj_centralizer_singleton b e, hbe']
  have hKb : CFSG.Assembly.IsComponentOf (K.map (MulAut.conj b).toMonoidHom)
      (Subgroup.centralizer ({e} : Set X)) := by
    have h := isComponentOf_map_conj hKcomp b
    rwa [hfix] at h
  have hJKb : J ≤ K.map (MulAut.conj b).toMonoidHom := by
    have hJb : J.map (MulAut.conj b).toMonoidHom = J :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := J) (g := b)).1 (h13 hb)
    have hmono : J.map (MulAut.conj b).toMonoidHom ≤ K.map (MulAut.conj b).toMonoidHom :=
      Subgroup.map_mono hJK
    rwa [hJb] at hmono
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hcomm : ⁅K, K.map (MulAut.conj b).toMonoidHom⁆ = ⊥ :=
    (isComponentOf_eq_or_commute hKcomp hKb).resolve_left (Ne.symm hne)
  exact not_le_of_le_commutator_eq_bot hJq hJK hJKb hcomm

theorem f4_neighbor_not_centralized_by_D
    {ψ : (ggU .F4 n f).K →* X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x)
    {e : X} (he : e ∈ D) {K : Subgroup X}
    (hKG : K ≤ G₀)
    (hKcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({e} : Set X)))
    (hJK : J ≤ K) (hKne : K ≠ J) :
    ¬ D ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  intro hDleC
  have hKcentD : K ≤ Subgroup.centralizer (D : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : d ∈ Subgroup.centralizer (K : Set X) := hDleC hd
    rw [Subgroup.mem_centralizer_iff] at hd'
    exact (hd' k hk).symm
  let H : Subgroup X := G₀ ⊓ Subgroup.centralizer (D : Set X)
  have hKH : K ≤ H := le_inf hKG hKcentD
  have hHleC : H ≤ Subgroup.centralizer ({e} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have hyc : y ∈ Subgroup.centralizer (D : Set X) := hy.2
    rw [Subgroup.mem_centralizer_iff] at hyc
    exact hyc e he
  have hKcompH : CFSG.Assembly.IsComponentOf K H := isComponentOf_of_le hKcomp hKH hHleC
  have hJcompH : CFSG.Assembly.IsComponentOf J H := h15
  exact hKne (eq_of_isComponentOf_le hJcompH hKcompH hJK).symm

end CFSG.StandardType.F4ExplicitPos.Neighbors

end

end
