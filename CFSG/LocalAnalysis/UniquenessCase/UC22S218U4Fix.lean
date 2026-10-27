module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4Fld
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4Hyp
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSU
import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveDiag
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom)
open CFSG.Quasithin.H13.Sec53F.Unit (fieldAutHom)
open CFSG.LieType.SeitzGeneration.ExcHigh.TwFive (diagP exists_conj_le_diagP card_diagP_le)

variable {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K)

section Subfield

variable {K₀ : Type} [Field K₀] {f₀ : ℕ}

private noncomputable def uc22s218_u4_emb (h₀ : UnitaryFieldData 2 f₀ K₀) (ι : K₀ →+* K)
    (hbar : ∀ a, h.bar (ι a) = ι (h₀.bar a)) :
    ↥(unitarySU 2 f₀ K₀ 4) →* ↥(unitarySU 2 n K 4) :=
  MonoidHom.codRestrict
    ((Matrix.GeneralLinearGroup.map ι).comp (unitarySU 2 f₀ K₀ 4).subtype) _
    fun g => (CFSG.StandardType.OrdPFieldNsU.mem_unitarySU_map_iff h h₀ ι hbar _).mpr g.2

private theorem uc22s218_u4_emb_injective (h₀ : UnitaryFieldData 2 f₀ K₀) (ι : K₀ →+* K)
    (hbar : ∀ a, h.bar (ι a) = ι (h₀.bar a)) :
    Function.Injective (uc22s218_u4_emb h h₀ ι hbar) := by
  intro a b hab
  have h1 := congrArg (fun z : ↥(unitarySU 2 n K 4) =>
    ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hab
  exact Subtype.ext (Units.ext (Matrix.map_injective ι.injective h1))

private theorem uc22s218_u4_exists_conj_eq_diagP (h₀ : UnitaryFieldData 2 f₀ K₀) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ f₀ + 1) {A : Subgroup ↥(unitarySU 2 f₀ K₀ 4)}
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 3) :
    ∃ P : ↥(unitarySU 2 f₀ K₀ 4), A = (diagP 2 f₀ p 4 K₀).map (MulAut.conj P).toMonoidHom := by
  have := h₀.finite
  obtain ⟨P, hP⟩ := exists_conj_le_diagP h₀ hp hpq A hA
  refine ⟨P, Subgroup.eq_of_le_of_card_ge hP ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj P).injective, hAc]
  simpa using card_diagP_le (ℓ := 2) (f := f₀) (K := K₀) (p := p) (n := 4) hp.pos (by norm_num)

private theorem uc22s218_u4_exists_diag_omega (h₀ : UnitaryFieldData 2 f₀ K₀) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ f₀ + 1) :
    ∃ (ω : K₀ˣ) (D : ↥(unitarySU 2 f₀ K₀ 4)), D ∈ diagP 2 f₀ p 4 K₀ ∧ D ≠ 1 ∧
      (D : GL (Fin 4) K₀) = diagHom 4 ![ω, ω, ω⁻¹, ω⁻¹] := by
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h₀ hp hpq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set ω : K₀ˣ := Units.mk0 ζ hζ0 with hωdef
  have hωp : ω ^ p = 1 := Units.ext (by simpa [hωdef] using hζ.pow_eq_one)
  have hω1 : ω ≠ 1 := fun h1 =>
    hζ.ne_one hp.one_lt (by simpa [hωdef] using congrArg Units.val h1)
  have hωq : ω ^ (2 ^ f₀ + 1) = 1 := by
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, hωp, one_pow]
  have hσq : ∀ k : Fin 4, ((![ω, ω, ω⁻¹, ω⁻¹] k : K₀ˣ) : K₀) ^ (2 ^ f₀ + 1) = 1 := by
    intro k
    rw [← Units.val_pow_eq_pow_val]
    fin_cases k <;> simp [hωq, inv_pow]
  have hmem := CFSG.StandardType.TableBUD.diagHom_mem_primeFormUnitary h₀ hσq
  have hdet : ((diagHom 4 ![ω, ω, ω⁻¹, ω⁻¹] : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀).det =
      1 := by
    rw [CFSG.SectionRank.OddCover.det_diagHom, Fin.prod_univ_four]
    simp
  have hSU := CFSG.StandardType.TableBUE.mem_unitarySU_of_mem_primeFormUnitary h₀ hmem hdet
  refine ⟨ω, ⟨_, hSU⟩, ⟨?_, ?_⟩, ?_, rfl⟩
  · rw [CFSG.SectionRank.OddCover.coe_diagHom]
    exact Matrix.isDiag_diagonal _
  · refine Subtype.ext ?_
    rw [Subgroup.coe_pow, ← map_pow]
    have hσp : (![ω, ω, ω⁻¹, ω⁻¹] : Fin 4 → K₀ˣ) ^ p = 1 := by
      funext k
      fin_cases k <;> simp [hωp, inv_pow]
    rw [hσp, map_one]
    rfl
  · intro h1
    apply hω1
    have h2 : diagHom 4 ![ω, ω, ω⁻¹, ω⁻¹] = diagHom 4 (1 : Fin 4 → K₀ˣ) := by
      rw [map_one]
      exact congrArg Subtype.val h1
    simpa using congrFun (CFSG.SectionRank.OddCover.diagHom_injective 4 h2) 0

private theorem uc22s218_u4_transport_map (h₀ : UnitaryFieldData 2 f₀ K₀) (ι : K₀ →+* K)
    (hbar : ∀ a, h.bar (ι a) = ι (h₀.bar a)) {T₀ : Matrix (Fin 4) (HypIndex 2 0) K₀}
    (hT₀ : IsGramHypTransport (r := 2) (ε := 0) h₀ (idGram K₀ 4) T₀) :
    IsGramHypTransport (r := 2) (ε := 0) h (idGram K 4) (T₀.map ι) ∧
      gramHypInv (r := 2) (ε := 0) h (idGram K 4) (T₀.map ι) =
        (gramHypInv (r := 2) (ε := 0) h₀ (idGram K₀ 4) T₀).map ι := by
  have e1 : (T₀.map ι).map h.bar = (T₀.map h₀.bar).map ι := by
    ext i j
    exact hbar _
  have e2 : idGram K 4 = (idGram K₀ 4).map ι :=
    (Matrix.map_one ι (map_zero ι) (map_one ι)).symm
  refine ⟨?_, ?_⟩
  · unfold IsGramHypTransport at hT₀ ⊢
    rw [e1, e2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hT₀, hypGram_map]
  · unfold gramHypInv
    rw [e1, e2, ← Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul, hypGram_map]

private theorem uc22s218_u4_fixed_frame_of_subfield (h₀ : UnitaryFieldData 2 f₀ K₀)
    (ι : K₀ →+* K) (hbar : ∀ a, h.bar (ι a) = ι (h₀.bar a)) {θ : K ≃+* K}
    (hθι : ∀ a, θ (ι a) = ι a)
    (hdesc : ∀ g : GL (Fin 4) K, glAut θ g = g →
      ∃ g₀ : GL (Fin 4) K₀, Matrix.GeneralLinearGroup.map ι g₀ = g)
    {p : ℕ} (hp : p.Prime) (hpq₀ : p ∣ 2 ^ f₀ + 1) (W : Subgroup ↥(unitarySU 2 n K 4))
    (hW : IsElemAbelian p W) (hWc : Nat.card W = p ^ 3)
    (hWθ : ∀ w ∈ W, uc22s218_u4_field h θ w = w) :
    ∃ eT : ↥(unitarySU 2 n K 4) ≃* ↥(hypSU h 2 0),
      (∀ s, eT (uc22s218_u4_field h θ s) = fieldAutHom h 2 0 θ (eT s)) ∧
      ∃ y ∈ W, y ≠ 1 ∧ eT y ∈ hypTorus h 2 0 := by
  have := h₀.finite
  set κ := uc22s218_u4_emb h h₀ ι hbar
  have hκ : Function.Injective κ := uc22s218_u4_emb_injective h h₀ ι hbar
  have hrange : W ≤ κ.range := by
    intro w hw
    have hfix : glAut θ (w : GL (Fin 4) K) = w := congrArg Subtype.val (hWθ w hw)
    obtain ⟨g₀, hg₀⟩ := hdesc _ hfix
    have hg₀U : g₀ ∈ unitarySU 2 f₀ K₀ 4 :=
      (CFSG.StandardType.OrdPFieldNsU.mem_unitarySU_map_iff h h₀ ι hbar g₀).mp (hg₀ ▸ w.2)
    exact ⟨⟨g₀, hg₀U⟩, Subtype.ext hg₀⟩
  have hW₀ : IsElemAbelian p (W.comap κ) := hW.comap hκ
  have hW₀c : Nat.card (W.comap κ) = p ^ 3 := by
    have hmap : (W.comap κ).map κ = W := by
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr hrange]
    calc Nat.card (W.comap κ) = Nat.card ((W.comap κ).map κ) :=
          (Subgroup.card_map_of_injective hκ).symm
      _ = Nat.card W := by rw [hmap]
      _ = p ^ 3 := hWc
  obtain ⟨P, hPW⟩ := uc22s218_u4_exists_conj_eq_diagP h₀ hp hpq₀ hW₀ hW₀c
  obtain ⟨ω, D, hDmem, hD1, hDmat⟩ := uc22s218_u4_exists_diag_omega h₀ hp hpq₀
  set x₀ : ↥(unitarySU 2 f₀ K₀ 4) := MulAut.conj P D with hx₀def
  have hx₀W₀ : x₀ ∈ W.comap κ := by
    rw [hPW]
    exact Subgroup.mem_map.mpr ⟨D, hDmem, rfl⟩
  have hx₀1 : x₀ ≠ 1 := by
    rw [hx₀def, Ne, MulEquiv.map_eq_one_iff]
    exact hD1
  have hx₀mat : (x₀ : GL (Fin 4) K₀) =
      (P : GL (Fin 4) K₀) * diagHom 4 ![ω, ω, ω⁻¹, ω⁻¹] * (P : GL (Fin 4) K₀)⁻¹ := by
    rw [← hDmat]
    rfl
  obtain ⟨T₀, hT₀, d₀, hd₀⟩ := uc22s218_u4_hyp_frame h₀ _
    (CFSG.StandardType.TableBUE.unitarySU_le_primeFormUnitary h₀ P.2) ω ω⁻¹
  obtain ⟨hT, hGinv⟩ := uc22s218_u4_transport_map h h₀ ι hbar hT₀
  have hmapfix : ∀ {ρ γ : Type} (M : Matrix ρ γ K₀), (M.map ι).map θ = M.map ι := fun M => by
    ext i j
    exact hθι _
  have hTθ : (T₀.map ι).map θ = T₀.map ι := hmapfix T₀
  have hGθ : (gramHypInv (r := 2) (ε := 0) h (idGram K 4) (T₀.map ι)).map θ =
      gramHypInv (r := 2) (ε := 0) h (idGram K 4) (T₀.map ι) := by
    rw [hGinv]
    exact hmapfix _
  refine ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 4)).trans
    (gramHypEquiv (r := 2) (ε := 0) h (idGram K 4) hT), fun s => ?_, κ x₀,
    Subgroup.mem_comap.mp hx₀W₀, fun h1 => hx₀1 (hκ (h1.trans (map_one κ).symm)), ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show gramHypInv (r := 2) (ε := 0) h (idGram K 4) (T₀.map ι) *
        (((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map θ) * T₀.map ι =
      (gramHypInv (r := 2) (ε := 0) h (idGram K 4) (T₀.map ι) *
        ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * T₀.map ι).map θ
    rw [Matrix.map_mul, Matrix.map_mul, hGθ, hTθ]
  · refine CFSG.RankThree.CentralLiftU.mem_hypTorus_of_diag h (q := fun x => ι (d₀ x)) ?_
    show gramHypInv (r := 2) (ε := 0) h (idGram K 4) (T₀.map ι) *
        (((x₀ : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀).map ι) * T₀.map ι =
      diagonal fun x => ι (d₀ x)
    rw [hGinv, ← Matrix.map_mul, ← Matrix.map_mul, hx₀mat, hd₀, Matrix.diagonal_map (map_zero ι)]

end Subfield

theorem uc22s218_u4_fixed_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {θ : K ≃+* K} (hθ : orderOf θ = p) (W : Subgroup ↥(unitarySU 2 n K 4))
    (hW : IsElemAbelian p W) (hWc : Nat.card W = p ^ 3)
    (hWθ : ∀ w ∈ W, uc22s218_u4_field h θ w = w) :
    ∃ eT : ↥(unitarySU 2 n K 4) ≃* ↥(hypSU h 2 0),
      (∀ s, eT (uc22s218_u4_field h θ s) = fieldAutHom h 2 0 θ (eT s)) ∧
      ∃ y ∈ W, y ≠ 1 ∧ eT y ∈ hypTorus h 2 0 := by
  obtain ⟨f₀, hf₀, h₀⟩ :=
    CFSG.StandardType.OrdPFieldNsU.exists_unitaryFieldData_fixed h hp hp2 hθ
  set K₀ := FixedPoints.subfield (Subgroup.zpowers θ) K
  have hbar : ∀ a : K₀, h.bar (K₀.subtype a) = K₀.subtype (h₀.bar a) := by
    subst hf₀
    exact CFSG.StandardType.OrdPFieldNsU.bar_coe h h₀ (hp.odd_of_ne_two hp2) K₀.subtype
  have : Fact p.Prime := ⟨hp⟩
  have hz : (2 : ZMod p) ^ n = 2 ^ f₀ := by
    rw [hf₀, mul_comm, pow_mul, ZMod.pow_card]
  have hpq₀ : p ∣ 2 ^ f₀ + 1 := by
    rw [← ZMod.natCast_eq_zero_iff] at hpq ⊢
    push_cast at hpq ⊢
    rw [← hz]
    exact hpq
  refine uc22s218_u4_fixed_frame_of_subfield h h₀ K₀.subtype hbar
    (fun a => CFSG.StandardType.OrdPFieldNs.fixed_of_mem_fixed a) (fun g hg => ?_) hp hpq₀ W hW
    hWc hWθ
  exact CFSG.StandardType.OrdPFieldNs.exists_gl_map_eq g (Units.ext (congrArg Units.val hg))

end CFSG.LocalAnalysis.UniquenessCase.UC22
