module

public import CFSG.Quasithin.EmptyFaithful.A38c10Env
public import CFSG.Quasithin.EmptyFaithful.A38c10Num

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.InternalSec CFSG.Quasithin.S1417
open scoped commutatorElement IsMulCommutative

section Gen

variable {G : Type} [Group G]

theorem mem_normalizer_omegaOneCenterOf {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (omegaOneCenterOf X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x ∈ omegaOneCenterOf X,
      g * x * g⁻¹ ∈ omegaOneCenterOf X := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ⟨⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hy.1.1, ?_⟩, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_aux hg) y).mp hy.1.2
      · calc (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := conj_pow
          _ = 1 := by rw [hy.2]; group
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key g hg x hx, fun hx => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hx⟩

end Gen
section Ctx

variable {G : Type} [Group G] [Finite G]

theorem nine_dvd_card_of_elemAbelian {H : Type*} [Group H] [Finite H]
    (hE : IsElemAbelianOfRank 3 2 (H ⧸ CFSG.Open.pCore 2 H)) : 9 ∣ Nat.card H := by
  obtain ⟨e⟩ := hE
  have h1 : Nat.card (H ⧸ CFSG.Open.pCore 2 H) = 9 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi]
  rw [← h1]
  exact Subgroup.card_quotient_dvd_card _

theorem env4_of_ctx (h113 : StageLemma14113) (h36 : Input15336One)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (c : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (c17 : Concl15317 T V₁ Yp I L) (hq : IsLnTwoQuot L 4) :
    ∃ Y₁ Y₂ : Subgroup G,
      Env4 L (Sgp153 T V₁) (R153 T V₁ Yp) Yp Y₁ Y₂ (VL153 T V₁ Yp L) := by
  obtain ⟨hYθ, hθ⟩ := concl15317_two4 c17 hq
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hF : Facts15311 T M V₁ Yp I := c.facts
  have hS : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLIc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLI : L ≤ I := le_of_mem_cComp hLIc
  have hYL : Yp ≤ L := hθ ▸ hYθ
  have hIL : ∀ g ∈ I, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    rw [← hθ] at hl ⊢
    exact A38c7.conj_mem_thetaOf hg hl
  have hIN : I ≤ Subgroup.normalizer (L : Set G) := FLc.le_normalizer_of_conj_mem hIL
  have hSL : ∀ s ∈ Sgp153 T V₁, ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun s hs l hl => hIL s (hS.1 hs) l hl
  have hSLn : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := FLc.le_normalizer_of_conj_mem hSL
  have hB : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := A4.isSylowTwoOf_inf_normal hS hLI hIN
  have hSM : Sgp153 T V₁ ≤ M := (inf_le_left : Sgp153 T V₁ ≤ T).trans hh.hyp.T_le
  have hSN : ∀ s ∈ Sgp153 T V₁, ∀ y ∈ Yp, s * y * s⁻¹ ∈ Yp := by
    intro s hs y hy
    have hs' : s ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by
      rw [hF.norm_eq]
      exact ⟨hSM hs, hS.1 hs⟩
    exact (Subgroup.mem_normalizer_iff.1 hs'.2 y).1 hy
  have hE : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) := by
    rcases hF.struct_Yp with h | h
    · exact h
    · exfalso
      have h27 : Nat.card (OTwoQuot Yp) = 3 ^ 3 := h.2.1
      apply not_dvd_27_card_of_quot4 hq
      have h1 : Nat.card (OTwoQuot Yp) ∣ Nat.card Yp := Subgroup.card_quotient_dvd_card _
      have h2 : Nat.card Yp ∣ Nat.card L := Subgroup.card_dvd_of_le hYL
      rw [h27] at h1
      exact (by norm_num : (27 : ℕ) = 3 ^ 3) ▸ h1.trans h2
  obtain ⟨φ, hφ, hker⟩ := h36 G T Mc M V₁ V₂ Yp t hh c.ctx.rank I c.ctx.inH
  obtain ⟨Y₁, Y₂, hY₁Y, hY₂Y, hYY, hY₁S, hY₂S, hY₁c, hY₂c⟩ :=
    A38c7.exists_two_factors hS.2.1 hSN hE φ hφ hker
  obtain ⟨⟨h1a, -, h1c⟩, ⟨-, hVe, hFF, -⟩, -⟩ := c.c16.desc
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
    S153D.pCoreOf_sup_R153_le c.facts hLIc hLq hRN
  have hsqI : SQTKGroup ↥I := (S153D.lemma_15_3_15_one c.ctx.hyp c.ctx.inH c.facts).sqtk
  have hsqL : SQTKGroup ↥L := B5.sqtk_of_le hsqI hLI
  have hSR : Sgp153 T V₁ ≤ Subgroup.normalizer (R153 T V₁ Yp : Set G) := fun s hs =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Yp ⊔ Sgp153 T V₁) (Subgroup.mem_sup_right hs)
  have hSLR : Sgp153 T V₁ ≤ Subgroup.normalizer ((L ⊔ R153 T V₁ Yp : Subgroup G) : Set G) :=
    fun s hs => Subgroup.inf_normalizer_le_normalizer_sup L _ ⟨hSLn hs, hSR hs⟩
  have hSV : Sgp153 T V₁ ≤ Subgroup.normalizer (VL153 T V₁ Yp L : Set G) := fun s hs =>
    mem_normalizer_omegaOneCenterOf
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (L ⊔ R153 T V₁ Yp) (hSLR hs))
  have hnt : ¬ L ≤ Subgroup.centralizer (VL153 T V₁ Yp L : Set G) := by
    intro hc
    apply hh.Yp_not_le_centralizer_UI h113 c.ctx.inH
    have hVZ : VZ T M ≤ VL153 T V₁ Yp L := S153D.VZ_le_VL153 hh c.ctx hF hLIc hO
    have hZV : ∀ z ∈ quasithinOmegaOneCenter T, z ∈ VL153 T V₁ Yp L := fun z hz =>
      hVZ (hh.hyp.Z_le_VZ hz)
    intro y hy x hx
    have hxK : x ∈ Subgroup.centralizer ({y} : Set G) := by
      refine (conjClosure_le (K := Subgroup.centralizer ({y} : Set G)) ?_) hx
      intro g hg z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ L := hIL g⁻¹ (I.inv_mem hg) y (hYL hy)
      have h1 := Subgroup.mem_centralizer_iff.mp (hc hy') z (hZV z hz)
      calc (g * z * g⁻¹) * y = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by
          have : (g⁻¹ * y * g) * z = z * (g⁻¹ * y * g) := by simpa using h1.symm
          rw [this]
        _ = y * (g * z * g⁻¹) := by group
    exact (Subgroup.mem_centralizer_singleton_iff).mp hxK
  refine ⟨Y₁, Y₂, ⟨hVe, ?_, hSV, hRN, hSLn, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, h1c, hFF, hLq, hsqL, hnt, hq, hB,
    hY₁Y, hY₂Y, hYL, hYY, hY₁S, hY₂S, hY₁c, hY₂c, ?_⟩⟩
  · exact le_sup_left.trans h1c.2.1
  · have := nine_dvd_card_of_elemAbelian hE
    exact this

end Ctx

end CFSG.Quasithin.A38c10
