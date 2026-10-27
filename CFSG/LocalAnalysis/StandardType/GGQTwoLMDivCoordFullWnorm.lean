module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullAux3
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.UCoord Matrix CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {m : ℕ}
  {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
  {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
  {hN : Bs ≤ Subgroup.normalizer (L : Set G)}

theorem qTwoLMDivF_scalar_conj {Z : GL (Fin m) F0} {z : F0}
    (hZ : (Z : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => z) (X : GL (Fin m) F0) :
    Z * X * Z⁻¹ = X := by
  have hc : Z * X = X * Z := by
    apply Units.ext
    simp only [Units.val_mul, hZ]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact mul_comm _ _
  rw [hc, mul_inv_cancel_right]

theorem qTwoLMDivF_c_gamma (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (b : ↥Bs) (l : ↥L) :
    c (ggGamma L hN b l) = ρ b (c l) := by
  have h := hU.induced b l
  rw [← h]
  congr 1

theorem qTwoLMDivF_c_conjgamma (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (n : ↥L)
    (b : ↥Bs) (l : ↥L) :
    c ((MulAut.conj n * ggGamma L hN b * (MulAut.conj n)⁻¹) l) =
      c n * ρ b ((c n)⁻¹ * c l * c n) * (c n)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply,
    map_mul c, map_mul c, map_inv c, qTwoLMDivF_c_gamma hU b, map_mul c, map_mul c, map_inv c]

theorem qTwoLMDivF_conj_act (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {n : ↥L}
    {u : Su F0 2 1 m} (hn : c n = π u) (b : ↥Bs) (s : Su F0 2 1 m) :
    ∃ s' : Su F0 2 1 m, (s' : GL (Fin m) F0) =
        ((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹) *
          (s : GL (Fin m) F0) *
          ((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹)⁻¹ ∧
      c n * ρ b ((c n)⁻¹ * π s * c n) * (c n)⁻¹ = π s' := by
  obtain ⟨s1, hs1, hπ1⟩ := qTwoLMDivF_rep_act hU b (u⁻¹ * s * u)
  refine ⟨u * s1 * u⁻¹, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hs1 ⊢
    rw [hs1]
    group
  · have h2 : (π u)⁻¹ * π s * π u = π (u⁻¹ * s * u) := by
      simp only [map_mul, map_inv]
    rw [hn, h2, hπ1]
    simp only [map_mul, map_inv]

theorem qTwoLMDivF_gamma_eq (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {n : ↥L} {u : Su F0 2 1 m}
    (hn : c n = π u) {b b' : ↥Bs} {z : F0}
    (hz : ((qTwoLMDivF_rep hU b' * ((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b *
      (u : GL (Fin m) F0)⁻¹)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        Matrix.diagonal fun _ => z) :
    ggGamma L hN b' = MulAut.conj n * ggGamma L hN b * (MulAut.conj n)⁻¹ := by
  have hAB : (ggGamma L hN b').toMonoidHom =
      (MulAut.conj n * ggGamma L hN b * (MulAut.conj n)⁻¹).toMonoidHom := by
    apply qTwoFrameLP_eq_of_mul_inv_mem_center hperf
    intro l
    apply hU.c_ker
    rw [MonoidHom.mem_ker]
    obtain ⟨s, hs⟩ := hU.π_surj (c l)
    obtain ⟨s', hs', hπ'⟩ := qTwoLMDivF_conj_act hU hn b s
    obtain ⟨s2, hs2, hπ2⟩ := qTwoLMDivF_rep_act hU b' s
    have hs2s' : s2 = s' := by
      apply Subtype.ext
      rw [hs2, hs']
      have hZ := qTwoLMDivF_scalar_conj hz
        (((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹) *
          (s : GL (Fin m) F0) *
          ((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹)⁻¹)
      calc qTwoLMDivF_rep hU b' * (s : GL (Fin m) F0) * (qTwoLMDivF_rep hU b')⁻¹
          = (qTwoLMDivF_rep hU b' * ((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b *
              (u : GL (Fin m) F0)⁻¹)⁻¹) *
            (((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹) *
              (s : GL (Fin m) F0) *
              ((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹)⁻¹) *
            (qTwoLMDivF_rep hU b' * ((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b *
              (u : GL (Fin m) F0)⁻¹)⁻¹)⁻¹ := by group
        _ = _ := hZ
    show c (ggGamma L hN b' l * ((MulAut.conj n * ggGamma L hN b * (MulAut.conj n)⁻¹) l)⁻¹) = 1
    rw [map_mul, map_inv, qTwoLMDivF_c_gamma hU b' l, qTwoLMDivF_c_conjgamma hU n b l,
      ← hs, hπ2, hπ', hs2s', mul_inv_cancel]
  exact MulEquiv.ext fun l => DFunLike.congr_fun hAB l

theorem qTwoLMDivF_scalar_of_gamma_eq (hm : 4 ≤ m)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {n : ↥L} {u : Su F0 2 1 m}
    (hn : c n = π u) {b b' : ↥Bs}
    (h : ggGamma L hN b' = MulAut.conj n * ggGamma L hN b * (MulAut.conj n)⁻¹) :
    ∃ z : F0, ((qTwoLMDivF_rep hU b' * ((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b *
      (u : GL (Fin m) F0)⁻¹)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        Matrix.diagonal fun _ => z := by
  refine qTwoLMDivF_rigid_scalar hm hU
    (g1 := (u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹)
    (g2 := qTwoLMDivF_rep hU b') (b := b') ?_ (qTwoLMDivF_rep_act hU b')
  intro s
  obtain ⟨s', hs', hπ'⟩ := qTwoLMDivF_conj_act hU hn b s
  refine ⟨s', hs', ?_⟩
  obtain ⟨l, hl⟩ := hU.c_surj (π s)
  have h1 := qTwoLMDivF_c_gamma hU b' l
  rw [h, qTwoLMDivF_c_conjgamma hU n b l, hl] at h1
  rw [← h1, hπ']

theorem qTwoLMDivF_wnorm_fwd (hm : 4 ≤ m) (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    (hsurj : Function.Surjective (qTwoLMDivF_phi hm hU hF0 hδ))
    {n : ↥L} {u : Su F0 2 1 m} (hn : c n = π u) (σ : Equiv.Perm (Fin m))
    (hu : ∀ f, (u : GL (Fin m) F0) * δ f * (u : GL (Fin m) F0)⁻¹ =
      δ (SpCoord.permAut σ f)) (b : ↥Bs) :
    ∃ b' : ↥Bs, ggGamma L hN b' = MulAut.conj n * ggGamma L hN b * (MulAut.conj n)⁻¹ := by
  obtain ⟨b', hb'⟩ := hsurj (QuotientGroup.mk (SpCoord.permAut σ (qTwoLMDivF_coord hU hF0 hδ b)))
  have hb'' : (QuotientGroup.mk (qTwoLMDivF_coord hU hF0 hδ b') : QTwoQm m) =
      QuotientGroup.mk (SpCoord.permAut σ (qTwoLMDivF_coord hU hF0 hδ b)) := by
    rw [← qTwoLMDivF_phi_apply hm hU hF0 hδ]
    exact hb'
  have hk := (QuotientGroup.eq_iff_div_mem).mp hb''
  obtain ⟨z, hz⟩ := (hδ.scalar _).mpr hk
  have h1 : qTwoLMDivF_rep hU b' = δ (qTwoLMDivF_coord hU hF0 hδ b') :=
    (qTwoLMDivF_coord_spec hU hF0 hδ b').symm
  have h2 : (u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹ =
      δ (SpCoord.permAut σ (qTwoLMDivF_coord hU hF0 hδ b)) := by
    rw [← qTwoLMDivF_coord_spec hU hF0 hδ b]
    exact hu _
  have h3 : δ (qTwoLMDivF_coord hU hF0 hδ b') *
      (δ (SpCoord.permAut σ (qTwoLMDivF_coord hU hF0 hδ b)))⁻¹ =
      δ (qTwoLMDivF_coord hU hF0 hδ b' /
        SpCoord.permAut σ (qTwoLMDivF_coord hU hF0 hδ b)) := by
    rw [map_div, div_eq_mul_inv]
  refine ⟨b', qTwoLMDivF_gamma_eq hperf hU hn (b := b) (b' := b') (z := z) ?_⟩
  rw [h1, h2, h3]
  exact hz

theorem qTwoLMDivF_wnorm_full (hm : 4 ≤ m) (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    (hsurj : Function.Surjective (qTwoLMDivF_phi hm hU hF0 hδ))
    {n : ↥L} {u : Su F0 2 1 m} (hn : c n = π u) (σ : Equiv.Perm (Fin m))
    (hu : ∀ f, (u : GL (Fin m) F0) * δ f * (u : GL (Fin m) F0)⁻¹ =
      δ (SpCoord.permAut σ f)) :
    MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hn' : c n⁻¹ = π u⁻¹ := by rw [map_inv, hn, map_inv]
  have hu' : ∀ f, ((u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) * δ f *
      ((u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0)⁻¹ = δ (SpCoord.permAut σ⁻¹ f) := by
    intro f
    have h := hu (SpCoord.permAut σ⁻¹ f)
    have hf : SpCoord.permAut σ (SpCoord.permAut σ⁻¹ f) = f := by
      funext i
      simp [SpCoord.permAut_apply]
    rw [hf] at h
    simp only [Subgroup.coe_inv, inv_inv]
    rw [← h]
    group
  constructor
  · rintro ⟨b, rfl⟩
    exact qTwoLMDivF_wnorm_fwd hm hperf hU hF0 hδ hsurj hn σ hu b
  · intro hg
    obtain ⟨b, hb⟩ := hg
    obtain ⟨b', hb'⟩ := qTwoLMDivF_wnorm_fwd hm hperf hU hF0 hδ hsurj hn' σ⁻¹ hu' b
    refine ⟨b', ?_⟩
    rw [hb', hb]
    simp only [map_inv, inv_inv]
    group

end CFSG.StandardType.QTwo

end
