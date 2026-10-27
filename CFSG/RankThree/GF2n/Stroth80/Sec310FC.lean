module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Symm
public import CFSG.RankThree.GF2n.Stroth80.Sec310Perp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.Vt_le_QB_conj (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B))
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    (hV : Vt M (LB M Q B) B Z t ≤ QB B) {m : G} (hm : m ∈ M)
    (htm : t ∈ conjSubgroup m (LB M Q B)) :
    Vt M (LB M Q B) B Z t ≤ QB (conjSubgroup m B) := by
  classical
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  set V := Vt M (LB M Q B) B Z t with hVdef
  set R := Rt M (LB M Q B) t with hRdef
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hC : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hCV : conjSubgroup m B ≤ V := sec39_conjB_le_Vt hm htm
  have hVr : ∀ r ∈ R, V ≤ QB (conjSubgroup r B) := by
    intro r hr
    have hnr : conjSubgroup r V = V :=
      conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hr)
    calc V = conjSubgroup r V := hnr.symm
      _ ≤ conjSubgroup r (QB B) := Subgroup.map_mono hV
      _ = QB (conjSubgroup r B) := (QB_conj r B).symm
  have hBrC : ∀ r ∈ R, conjSubgroup r B ≤ QB (conjSubgroup m B) := by
    intro r hr
    by_cases hrC : conjSubgroup r B = conjSubgroup m B
    · rw [hrC]
      exact hC.B_le_QB
    · have hrM : r ∈ M := (hc.Rt_le_H0 t hr).1
      exact (hc.hyp.le_QB_iff_le_QB (hc.conj_of_mem hrM).conj hC.conj hrC).mpr
        (hCV.trans (hVr r hr))
  let gens : Set M₀.E := {e | ∃ r ∈ R, e ∈ M₀.img (conjSubgroup r B)}
  let Sp : Submodule (GaloisField 2 n') M₀.E := Submodule.span _ gens
  obtain ⟨b₀, hb0, -, hB, -, -⟩ := hc.dictB h
  have hb₀gens : b₀ ∈ gens :=
    ⟨1, R.one_mem, by
      rw [conjSubgroup_one]
      exact (hB b₀).mpr ⟨1, (one_smul _ _).symm⟩⟩
  have hSp0 : Sp ≠ ⊥ := fun h0 => hb0 (by
    have h1 : b₀ ∈ Sp := Submodule.subset_span hb₀gens
    rw [h0] at h1
    simpa using h1)
  have hSp : ∀ l ∈ R, ∀ S : M₀.E ≃ₗ[GaloisField 2 n'] M₀.E,
      (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) → (∀ e, M₀.Qf (S e) = M₀.Qf e) →
        ∀ v ∈ Sp, S v ∈ Sp := by
    intro l hl S hS _ v hv
    have hlM : l ∈ M := (hc.Rt_le_H0 t hl).1
    induction hv using Submodule.span_induction with
    | mem e he =>
      obtain ⟨r, hr, x, hxB, hxQ, rfl⟩ := he
      rw [← hS x hxQ]
      apply Submodule.subset_span
      refine ⟨l * r, R.mul_mem hl hr, ?_⟩
      have hlxQ : l * x * l⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) x).mp hxQ
      refine M₀.pi_mem_img ?_ hlxQ
      rw [mem_conjSubgroup] at hxB ⊢
      have e1 : (l * r)⁻¹ * (l * x * l⁻¹) * (l * r) = r⁻¹ * x * r := by group
      rw [e1]
      exact hxB
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Sp.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Sp.smul_mem a hx
  have hVSp := hc.img_Vt_le_of_invariant h35 h t Sp hSp0 hSp
  have h1n : 1 ≤ n := by omega
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup m B)) := hc.noA2_conj hno hm
  have hcardC := (hC.card_of_3_3 hw h1n hnoC (stroth_3_3 hC hw h1n)).2
  obtain ⟨WC, hWC⟩ := hC.exists_submodule_inf_QB hw hcardC h
  have hSpW : Sp ≤ WC := by
    refine Submodule.span_le.mpr ?_
    rintro e ⟨r, hr, x, hxB, hxQ, rfl⟩
    exact (hWC _).mpr (M₀.pi_mem_img ⟨hxQ, hBrC r hr hxB⟩ hxQ)
  intro x hx
  have hxQ : x ∈ Q := hVQ hx
  have hmem : M₀.π x ∈ WC := hSpW (hVSp _ (M₀.pi_mem_img hx hxQ))
  exact ((M₀.mem_img_iff (le_inf hc.Z_le_Q hC.Z_le_QB.1) hxQ).mp ((hWC _).mp hmem)).2

end CFSG.RankThree.GF2n.Stroth80
