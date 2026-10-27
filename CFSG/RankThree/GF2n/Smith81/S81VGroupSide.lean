module

public import CFSG.RankThree.GF2n.Smith81.S81JGLift
public import CFSG.RankThree.GF2n.Smith81.S81BTacitFree
public import CFSG.RankThree.GF2n.Smith81.S81VLemmaJ
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.GF2n.Smith81.Sec2Consequences

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Module

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

private theorem polar_preserved_of_Qf_comp {k E : Type} [Field k] [AddCommGroup E] [Module k E]
    (Bf : LinearMap.BilinForm k E) (Qf : E → k)
    (hadd : ∀ e f, Qf (e + f) = Qf e + Qf f + Bf e f) (t : E ≃ₗ[k] E)
    (hQ : ∀ e, Qf (t e) = Qf e) (u w : E) :
    Bf (t u) (t w) = Bf u w := by
  have h4 := hadd (t u) (t w)
  have h5 := hadd u w
  have hC : Qf (t u + t w) = Qf (u + w) := by
    rw [← map_add t u w]
    exact hQ (u + w)
  linear_combination -h4 + hC + h5 - hQ u - hQ w

theorem exists_T_Lgen_isom (hctx : Ctx M Q Z B) (hg : GlobalModelData M Q Z γ M₀) :
    ∃ T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E),
      (∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
        M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x)) ∧
      (∀ s : Lgen M (LB M Q B), T s = 1 ↔ (s : G) ∈ Q) ∧
      ∀ (s : Lgen M (LB M Q B)) (u w : M₀.E), M₀.B (T s u) (T s w) = M₀.B u w := by
  obtain ⟨φ, h1, h2, h3⟩ := exists_actionHom_H0 hctx.hyp hg
  have hle := Lgen_le_H0 hctx
  exact ⟨φ.comp (Subgroup.inclusion hle), fun s x hx => h1 ⟨(s : G), hle s.2⟩ x hx,
    fun s => h2 ⟨(s : G), hle s.2⟩,
    fun s u w => polar_preserved_of_Qf_comp M₀.B M₀.Qf M₀.Qf_add
      ((φ.comp (Subgroup.inclusion hle)) s) (fun e => h3 ⟨(s : G), hle s.2⟩ e) u w⟩

theorem exists_W_of_barU {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
    (hσ : IsUnitaryInvolution σ) {X : Type} [Group X] (Θ : ↥(SUid σ 6) →* X)
    (hΘ : Function.Surjective Θ) (hk3 : ∀ n ∈ Θ.ker, n ^ 3 = 1)
    (hkc : ∀ n ∈ Θ.ker, ∀ x : ↥(SUid σ 6), n * x = x * n) (Eb : Subgroup X)
    (hc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x) (hs : ∀ x ∈ Eb, x * x = 1)
    (hcard : Nat.card Eb = Nat.card (Fσ σ) ^ 9) :
    ∃ (W : Submodule F (Fin 6 → F)) (E : Subgroup ↥(SUid σ 6)), IsTotIso σ W ∧ finrank F W = 3 ∧
      E.map Θ = Eb ∧ E = PtStab σ W := by
  obtain ⟨E, hinv, hcomm, hmap, hcardE⟩ :=
    CFSG.RankThree.GF2n.Smith81.S81J.exists_lift_involutions Θ hΘ hk3 hkc Eb hc hs
  have hsq : ∀ x ∈ E, x ^ 2 = 1 := fun x hx => by rw [pow_two]; exact hinv x hx
  have hEA : CFSG.Open.IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm (a : ↥(SUid σ 6)) a.2 (b : ↥(SUid σ 6)) b.2)⟩⟩, hsq⟩
  have hcard9 : Nat.card (Fσ σ) ^ 9 ≤ Nat.card E :=
    le_of_eq (by rw [hcardE, hcard])
  obtain ⟨W, hW, hW3, hEW⟩ := lemmaJU hσ hEA hcard9
  exact ⟨W, E, hW, hW3, hmap, hEW⟩

theorem LB_le_Lgen_of_point_E3U (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h3U : InCaseE3U M Q Z B)
    {C : Subgroup G} (hC : Ctx M Q Z C) : LB M Q C ≤ Lgen M (LB M Q B) := by
  obtain ⟨n, k, hw, hnk⟩ := hc.e.exists_width
  have hn : 3 ≤ n := by
    have := hnk.ten_le
    omega
  have hTac : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') ∧ GenByB M Q B' :=
    eTacitE3U_of_genByB hGen G M Q Z B IH hc h3U
  have hno : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') :=
    fun B' hB' => (hTac B' hB').1
  have h15c : ∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G) := fun B' hB' =>
    (stroth_3_5 h34 hB' hw (by omega) (hTac B' hB').1 (hTac B' hB').2).2.1
  have h25 := smith25_of_117 smith117Statement_holds hc.ctx hw hn hno h15c
  have hmem : C ⊔ Z ∈ {V : Subgroup G | ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧
      V = A ⊔ Z} := ⟨C, hC.conj, hC.le, hC.ne, rfl⟩
  rw [h25] at hmem
  obtain ⟨g, hg, hCg⟩ := hmem
  have hcg : Ctx M Q Z (conjSubgroup g B) := hc.ctx.conj_of_mem hg
  have hle : conjSubgroup g B ≤ Z ⊔ C := by
    rw [sup_comm, hCg]
    exact le_sup_left
  obtain ⟨p, hpQ, hp⟩ := hC.exists_conj_of_le_ZB hcg hle
  have hpM : p ∈ M := hc.ctx.hyp.Q_normal.1 hpQ
  have hCeq : C = conjSubgroup (p⁻¹ * g) B := by
    rw [conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hm : p⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hpM) hg
  rw [hCeq, hc.ctx.LB_conj hm]
  exact le_iSup₂_of_le (p⁻¹ * g) hm le_rfl

end CFSG.RankThree.GF2n.Smith81.S81V
