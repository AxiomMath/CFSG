module

public import CFSG.Quasithin.EmptyFaithful.SzN7Trace
public import CFSG.Quasithin.EmptyFaithful.S153D16
public import CFSG.Quasithin.EmptyFaithful.S153DInputs
public import CFSG.Quasithin.EmptyFaithful.SzN4Local

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

section Decomp

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN7_V_decomp (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (hRL : IsSylowTwoOf (R153 T V₁ Yp ⊓ L) L) {v : G} (hv : v ∈ VZ T M) :
    ∃ a ∈ blockU L ⊓ Subgroup.centralizer ((R153 T V₁ Yp ⊓ L : Subgroup G) : Set G),
      ∃ c ∈ WL153 T M L ⊓ Subgroup.centralizer (L : Set G), v = a * c := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := ctx.ctx.hyp
  have hF : Facts15311 T M V₁ Yp I := ctx.facts
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ ctx.conc.1
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := ctx.c16.R_norm
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := ctx.conc.2.2.2.2.2
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
    S153D.pCoreOf_sup_R153_le hF hLI hLq hRN
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVc := S153D.VZ_le_centerOf hh ctx.ctx hF hLI hO
  have hWc := S153D.WL_le_centerOf hh ctx.ctx hF hLI hO
  have hvR : v ∈ centerOf (R153 T V₁ Yp) := S153D.lemma_15_3_14_one hh hF hv
  have hvQ := hVc hv
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := hRN (hO hvQ.1)
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ R153 T V₁ Yp) : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  have hvQc : ∀ x ∈ L, v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
    intro x hx
    have h1 : v * x * v⁻¹ * x⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hvN x).mp hx
      exact L.mul_mem this (L.inv_mem hx)
    have h2 : v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 (L ⊔ R153 T V₁ Yp) := by
      have h3 : x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 (L ⊔ R153 T V₁ Yp) :=
        (Subgroup.mem_normalizer_iff.mp (hLQ hx) _).mp ((pCoreOf 2 _).inv_mem hvQ.1)
      have e : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 _).mul_mem hvQ.1 h3
    have hmem : v * x * v⁻¹ * x⁻¹ ∈ L ⊓ pCoreOf 2 (L ⊔ R153 T V₁ Yp) := ⟨h1, h2⟩
    have hle : L ⊓ pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ pCoreOf 2 L :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hLQ hg⟩)
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hle hmem
  have hcom : ∀ l ∈ L, v * (l * v * l⁻¹)⁻¹ ∈ blockU L := by
    intro l hl
    have e : v * (l * v * l⁻¹)⁻¹ = v * l * v⁻¹ * l⁻¹ := by group
    rw [e]
    exact szN4_conj_comm_mem_blockU hperf hvN hvQc l hl
  have hWL : WL153 T M L ≤ pCoreOf 2 (L ⊔ R153 T V₁ Yp) ⊓
      Subgroup.centralizer (pCoreOf 2 (L ⊔ R153 T V₁ Yp) : Set G) := hWc
  obtain ⟨c, hcW, hcL, hcP⟩ := szN7_trace (L := L) (Rl := R153 T V₁ Yp ⊓ L) (W := WL153 T M L)
    (v := v) hRL.2.2
    (fun a ha b hb => by
      have := Subgroup.mem_centralizer_iff.mp (hWL ha).2 b (hWL hb).1
      exact this.symm)
    (fun l hl w hw => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (VZ T M) L hl) w).mp hw)
    (le_conjClosure (VZ T M) L hv) (hh.hyp.elemAbelian.2 v hv)
    (fun r hr => by
      have := Subgroup.mem_centralizer_iff.mp hvR.2 r hr.1
      calc r * v * r⁻¹ = v * r * r⁻¹ := by rw [this]
        _ = v := by group)
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have := hcL l hl
    calc l * c = (l * c * l⁻¹) * l := by group
      _ = c * l := by rw [this]
  have ha := hcP (blockU L) hcom
  refine ⟨v * c⁻¹, ⟨ha, ?_⟩, c, ⟨hcW, hcC⟩, by group⟩
  refine Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
  have hrv : r * v = v * r := Subgroup.mem_centralizer_iff.mp hvR.2 r hr.1
  have hrc : r * c = c * r := Subgroup.mem_centralizer_iff.mp hcC r hr.2
  have hrc' : r * c⁻¹ = c⁻¹ * r := by
    calc r * c⁻¹ = c⁻¹ * (c * r) * c⁻¹ := by group
      _ = c⁻¹ * (r * c) * c⁻¹ := by rw [hrc]
      _ = c⁻¹ * r := by group
  calc r * (v * c⁻¹) = (r * v) * c⁻¹ := by group
    _ = (v * r) * c⁻¹ := by rw [hrv]
    _ = v * (r * c⁻¹) := by group
    _ = v * (c⁻¹ * r) := by rw [hrc']
    _ = (v * c⁻¹) * r := by group

end Decomp

end CFSG.Quasithin
