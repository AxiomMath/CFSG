module

public import CFSG.RankThree.GF2n.Smith81.S81BNoA2
public import CFSG.RankThree.GF2n.Smith81.S81BCount

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube
open scoped commutatorElement

section Orbit

variable {K : Type} [Field K]

theorem iSup_span_gam_p0 :
    (⨆ γ : Gam K, Submodule.span K {(γ : Cube K ≃ₗ[K] Cube K) (p0 K)}) = ⊤ := by
  classical
  rw [eq_top_iff, ← (cubeBasis K).span_eq, Submodule.span_le]
  rintro _ ⟨I, rfl⟩
  have hpure : ∀ J, IsPure K (cubeBasis K J) := fun J =>
    ⟨fun i => Pi.basisFun K (Fin 6) (enum J i), by rw [cubeBasis, exteriorPower.basis_apply]; rfl⟩
  obtain ⟨g, hdet, hg⟩ := isPure_transitive (hpure S024) (hpure I) ((cubeBasis K).ne_zero _)
    ((cubeBasis K).ne_zero _)
  have hgSL : g ∈ StatedSL 6 K := Subgroup.subset_closure hdet
  have hγ : rhoEquiv K g ∈ Gam K := Subgroup.mem_map_of_mem _ hgSL
  refine Submodule.mem_iSup_of_mem ⟨rhoEquiv K g, hγ⟩ (Submodule.subset_span ?_)
  rw [Set.mem_singleton_iff, rhoEquiv_apply, p0, hg]

end Orbit

variable {G : Type} [Group G]

private theorem quad_pi_one {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) : M₀.π 1 = 0 := by
  have h := M₀.π_mul 1 Q.one_mem 1 Q.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

private theorem quad_pi_inv {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {x : G} (hx : x ∈ Q) : M₀.π x⁻¹ = -M₀.π x := by
  have h := M₀.π_mul x hx x⁻¹ (Q.inv_mem hx)
  rw [mul_inv_cancel, quad_pi_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem commutatorElement_mul_of_commute {z₁ z₂ r₁ r₂ : G} (h11 : Commute z₁ r₁)
    (h12 : Commute z₁ r₂) (h21 : Commute z₂ r₁) (h22 : Commute z₂ r₂) (hzz : Commute z₁ z₂) :
    ⁅z₁ * r₁, z₂ * r₂⁆ = ⁅r₁, r₂⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have e1 : z₁ * r₁ * (z₂ * r₂) * (r₁⁻¹ * z₁⁻¹) * (r₂⁻¹ * z₂⁻¹) =
      (z₁ * z₂ * z₁⁻¹ * z₂⁻¹) * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) := by
    have a1 : r₁ * z₂ = z₂ * r₁ := h21.eq.symm
    have a2 : r₂ * z₁⁻¹ = z₁⁻¹ * r₂ := (h12.inv_left).eq.symm
    have a3 : r₁ * z₁⁻¹ = z₁⁻¹ * r₁ := (h11.inv_left).eq.symm
    have a4 : r₁⁻¹ * z₁⁻¹ = z₁⁻¹ * r₁⁻¹ := (h11.inv_inv).eq.symm
    have a5 : r₂⁻¹ * z₂⁻¹ = z₂⁻¹ * r₂⁻¹ := (h22.inv_inv).eq.symm
    have a6 : r₁⁻¹ * z₂⁻¹ = z₂⁻¹ * r₁⁻¹ := (h21.inv_inv).eq.symm
    have a7 : r₂ * z₂⁻¹ = z₂⁻¹ * r₂ := (h22.inv_left).eq.symm
    have a8 : r₁ * z₂⁻¹ = z₂⁻¹ * r₁ := (h21.inv_left).eq.symm
    calc z₁ * r₁ * (z₂ * r₂) * (r₁⁻¹ * z₁⁻¹) * (r₂⁻¹ * z₂⁻¹)
        = z₁ * (r₁ * z₂) * r₂ * (r₁⁻¹ * z₁⁻¹) * (r₂⁻¹ * z₂⁻¹) := by group
      _ = z₁ * z₂ * r₁ * r₂ * (z₁⁻¹ * r₁⁻¹) * (z₂⁻¹ * r₂⁻¹) := by
          rw [a1, a4, a5]; group
      _ = z₁ * z₂ * (r₁ * (r₂ * z₁⁻¹)) * r₁⁻¹ * z₂⁻¹ * r₂⁻¹ := by group
      _ = z₁ * z₂ * (r₁ * z₁⁻¹) * r₂ * r₁⁻¹ * z₂⁻¹ * r₂⁻¹ := by rw [a2]; group
      _ = z₁ * z₂ * z₁⁻¹ * r₁ * r₂ * (r₁⁻¹ * z₂⁻¹) * r₂⁻¹ := by rw [a3]; group
      _ = z₁ * z₂ * z₁⁻¹ * r₁ * (r₂ * z₂⁻¹) * r₁⁻¹ * r₂⁻¹ := by rw [a6]; group
      _ = z₁ * z₂ * z₁⁻¹ * (r₁ * z₂⁻¹) * r₂ * r₁⁻¹ * r₂⁻¹ := by rw [a7]; group
      _ = (z₁ * z₂ * z₁⁻¹ * z₂⁻¹) * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) := by rw [a8]; group
  rw [e1]
  have hz : z₁ * z₂ * z₁⁻¹ * z₂⁻¹ = 1 := by
    rw [hzz.eq]
    group
  rw [hz, one_mul]

theorem genByB_of_uniform_E3L [Finite G]
    (hFE1 : Smith24E3LUniformStatement) {M Q Z B : Subgroup G}
    (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h3L : InCaseE3L M Q Z B)
    {B' : Subgroup G} (hB' : Ctx M Q Z B') : GenByB M Q B' := by
  classical
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h3L K γ M₀ hg
  have hLM : Lgen M (LB M Q B) ≤ M := iSup₂_le fun m hm => by
    calc conjSubgroup m (LB M Q B) ≤ conjSubgroup m M := Subgroup.map_mono hc.ctx.LB_le_M
      _ = M := hc.ctx.conj_M_eq hm
  set R : Subgroup G := ⨆ (m : G) (_ : m ∈ M), conjSubgroup m B' with hR
  have hRQ : R ≤ Q := iSup₂_le fun m hm =>
    (Subgroup.map_mono hB'.le).trans (hc.ctx.conj_Q_eq hm).le
  have hmemR : ∀ m ∈ M, ∀ b ∈ B', m * b * m⁻¹ ∈ R := fun m hm b hb =>
    (le_iSup₂ (f := fun m (_ : m ∈ M) => conjSubgroup m B') m hm)
      (mem_conjSubgroup.mpr (by simpa [mul_assoc] using hb))
  obtain ⟨g₀, hg₀, hline, -⟩ := d.point B' hB'.conj hB'.le hB'.ne
  have hsurj : ∀ v : Cube K, ∃ r ∈ R, ψ (M₀.π r) = v := by
    intro v
    have hv : v ∈ ⨆ γ' : Gam K, Submodule.span K {(γ' : Cube K ≃ₗ[K] Cube K) (p0 K)} := by
      rw [iSup_span_gam_p0]
      trivial
    induction hv using Submodule.iSup_induction' with
    | mem γ' w hw =>
      have hγ' : (γ' : Cube K ≃ₗ[K] Cube K) * g₀⁻¹ ∈ φ.range := by
        rw [d.range]
        exact (Gam K).mul_mem γ'.2 ((Gam K).inv_mem hg₀)
      obtain ⟨s, hs⟩ := hγ'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have hc0 : c • g₀ (p0 K) ∈ (fun a : G => ψ (M₀.π a)) '' (B' : Set G) := by
        rw [hline]
        exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
      obtain ⟨b, hb, hbv⟩ := hc0
      have hbv' : ψ (M₀.π b) = c • g₀ (p0 K) := hbv
      refine ⟨(s : G) * b * (s : G)⁻¹, hmemR _ (hLM s.2) b hb, ?_⟩
      rw [d.equivariant s b (hB'.le hb), hbv', map_smul]
      congr 1
      rw [show (φ s) (g₀ (p0 K)) = ((φ s) * g₀) (p0 K) from rfl, hs, inv_mul_cancel_right]
    | zero => exact ⟨1, R.one_mem, by rw [quad_pi_one, map_zero]⟩
    | add v₁ v₂ _ _ h₁ h₂ =>
      obtain ⟨r₁, hr₁, e₁⟩ := h₁
      obtain ⟨r₂, hr₂, e₂⟩ := h₂
      refine ⟨r₁ * r₂, R.mul_mem hr₁ hr₂, ?_⟩
      rw [M₀.π_mul r₁ (hRQ hr₁) r₂ (hRQ hr₂), map_add, e₁, e₂]
  have hZR : ∀ x ∈ Q, ∃ r ∈ R, x * r⁻¹ ∈ Z := by
    intro x hx
    obtain ⟨r, hr, e⟩ := hsurj (ψ (M₀.π x))
    refine ⟨r, hr, (M₀.π_ker _ (Q.mul_mem hx (Q.inv_mem (hRQ hr)))).mp ?_⟩
    have e' : M₀.π r = M₀.π x := ψ.injective e
    rw [M₀.π_mul x hx r⁻¹ (Q.inv_mem (hRQ hr)), quad_pi_inv M₀ (hRQ hr), e', add_neg_cancel]
  have hZc : ∀ z ∈ Z, ∀ y ∈ Q, Commute z y := by
    intro z hz y hy
    have hz' : z ∈ cen Q := hc.ctx.hyp.hZ ▸ hz
    rw [cen_eq] at hz'
    exact ((Subgroup.mem_centralizer_iff.mp hz'.2) y hy).symm
  have hZQ : Z ≤ Q := fun z hz => by
    have hz' : z ∈ cen Q := hc.ctx.hyp.hZ ▸ hz
    rw [cen_eq] at hz'
    exact hz'.1
  have hZle : Z ≤ R := by
    rw [← hc.ctx.hyp.special.1, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨ra, hra, hza⟩ := hZR a ha
    obtain ⟨rb, hrb, hzb⟩ := hZR b hb
    have e : ⁅a, b⁆ = ⁅(a * ra⁻¹) * ra, (b * rb⁻¹) * rb⁆ := by
      rw [inv_mul_cancel_right, inv_mul_cancel_right]
    rw [e, commutatorElement_mul_of_commute (hZc _ hza _ (hRQ hra)) (hZc _ hza _ (hRQ hrb))
      (hZc _ hzb _ (hRQ hra)) (hZc _ hzb _ (hRQ hrb)) (hZc _ hza _ (hZQ hzb))]
    exact Subgroup.commutator_mem_commutator hra hrb |> fun h => (Subgroup.commutator_le_self R h)
  refine le_antisymm ?_ hRQ
  intro x hx
  obtain ⟨r, hr, hz⟩ := hZR x hx
  have : x = (x * r⁻¹) * r := by rw [inv_mul_cancel_right]
  rw [this]
  exact R.mul_mem (hZle hz) hr

theorem eTacitE3L_of_uniform (hFE1 : Smith24E3LUniformStatement) :
    ETacitE3LStatement := by
  intro G _ _ M Q Z B IH hc h3L B' hB'
  exact ⟨noA2All_of_inCaseE3L hc.toCfg h3L B' hB'.conj hB'.le hB'.ne,
    genByB_of_uniform_E3L hFE1 IH hc h3L hB'⟩

end CFSG.RankThree.GF2n.Smith81
