module

public import CFSG.Quasithin.Vol2.Ch9Sec2Hyp
public import CFSG.Quasithin.Vol2.Ch10SecASL2OverQ
public import CFSG.Quasithin.Vol2.Ch9Sec2Z

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin.H CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix
open CFSG.QuasithinUnique

section Model

variable {K : Type} [Field K]

theorem card_uni [Finite K] : Nat.card ↥(uni K) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective (fun c : K => (⟨⟨!![1, c; 0, 1], by
    simp [Matrix.det_fin_two_of]⟩, mem_uni_iff.mpr ⟨c, rfl⟩⟩ : ↥(uni K))) ⟨fun c c' h => ?_,
    fun u => ?_⟩)).symm
  · have := congrArg (fun u : ↥(uni K) => ((u : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 1) h
    simpa using this
  · obtain ⟨c, hc⟩ := mem_uni_iff.mp u.2
    exact ⟨c, Subtype.ext (Subtype.ext hc.symm)⟩

theorem isSylowTwoOf_uni_prod [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsSylowTwoOf ((uni K).prod (uni K)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcu : Nat.card ↥(uni K) = 2 ^ n := by rw [card_uni, hK]
  refine ⟨le_top, ?_, ?_⟩
  · rw [IsPGroup.iff_card, Nat.card_congr ((uni K).prodEquiv (uni K)).toEquiv, Nat.card_prod,
      hcu, ← pow_add]
    exact ⟨_, rfl⟩
  · rw [show (((uni K).prod (uni K)).subgroupOf ⊤).index = ((uni K).prod (uni K)).index from
      Subgroup.relIndex_top_right _, Subgroup.index_prod]
    have hidx : (uni K).index = 4 ^ n - 1 := by
      have h := Subgroup.card_mul_index (uni K)
      rw [hcu, Vol2.Ch10.SecA.card_SL_two_pow hK] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    rw [hidx]
    have hodd := Vol2.Ch10.SecA.odd_four_pow_sub_one (m := n) (by omega)
    exact fun h => (Nat.not_even_iff_odd.mpr (hodd.mul hodd)) (even_iff_two_dvd.mpr h)

theorem fixV_rho_uni_prod [CharP K 2] {Y : Om4.VM K}
    (hY : ∀ p ∈ (uni K).prod (uni K), Om4.rho p Y = Y) :
    Multiplicative.toAdd Y = !![Multiplicative.toAdd Y 0 0, 0; 0, 0] := by
  have h1 : !![(1 : K), 1; 0, 1] * Multiplicative.toAdd Y * (1 : Matrix (Fin 2) (Fin 2) K)ᵀ =
      Multiplicative.toAdd Y := by
    have := congrArg Multiplicative.toAdd (hY (u1 K, 1) ⟨u1_mem, (uni K).one_mem⟩)
    rw [toAdd_rho] at this
    exact this
  have h2 : (1 : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd Y * !![(1 : K), 1; 0, 1]ᵀ =
      Multiplicative.toAdd Y := by
    have := congrArg Multiplicative.toAdd (hY (1, u1 K) ⟨(uni K).one_mem, u1_mem⟩)
    rw [toAdd_rho] at this
    exact this
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have f00 := congrFun (congrFun h2 0) 0
  rw [mul_mul_transpose_apply] at e00 e01 f00
  simp at e00 e01 f00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, f00]

end Model

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem isSylowTwoOf_T_inf_L0 : IsSylowTwoOf (T ⊓ fsuL0 T L) (fsuL0 T L) := by
  have hloc := S.hyp.fsu.maximal.1
  exact B6.isSylowTwoOf_inf_normal ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
    (Vol2.Ch10.SecA.fsuL0_le_sup T L)
    (sup_le ((Vol2.Ch10.SecA.le_fsuL0 T L).trans Subgroup.le_normalizer)
      (Vol2.Ch10.SecA.le_fsuM T L))

theorem exists_coord_adapted :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2), Fintype.card K = 2 ^ n ∧
      ∃ (e : ↥(fsuV T I) ≃* Om4.VM K)
        (ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K),
        Function.Surjective ψ ∧
        (∀ k : ↥(fsuL0 T L), MulAut.congr e
          (conjAct (fsuV T I) (Subgroup.inclusion S.L0_le_normalizer_V k)) = Om4.rho (ψ k)) ∧
        ((T ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map ψ = (uni K).prod (uni K) := by
  classical
  obtain ⟨K, _, _, _, hK, e₀, he⟩ := S.exists_coord
  have hK' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  set ρe := MonoidHom.ofInjective (Om4.rho_injective (K := K)) with hρe
  have hmem : ∀ k : ↥(fsuL0 T L), MulAut.congr e₀
      (conjAct (fsuV T I) (Subgroup.inclusion S.L0_le_normalizer_V k)) ∈
        (Om4.rho (K := K)).range := by
    intro k
    rw [← he]
    exact ⟨_, ⟨Subgroup.inclusion S.L0_le_normalizer_V k, k.2, rfl⟩, rfl⟩
  let ψ₀ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K :=
    ρe.symm.toMonoidHom.comp (MonoidHom.codRestrict ((MulAut.congr e₀).toMonoidHom.comp
      ((conjAct (fsuV T I)).comp (Subgroup.inclusion S.L0_le_normalizer_V))) _ hmem)
  have hψ₀ : ∀ k, Om4.rho (ψ₀ k) = MulAut.congr e₀
      (conjAct (fsuV T I) (Subgroup.inclusion S.L0_le_normalizer_V k)) := fun k =>
    congrArg Subtype.val (ρe.apply_symm_apply ⟨_, hmem k⟩)
  have hψ₀s : Function.Surjective ψ₀ := by
    intro γ
    obtain ⟨x, hxL, hx⟩ := exists_mem_L0_of_rho he γ
    refine ⟨⟨x, hxL⟩, Om4.rho_injective ?_⟩
    rw [hψ₀, ← hx]
    rfl
  have hS' := Vol2.Ch10.SecA.isSylowTwoOf_map_of_surjective S.isSylowTwoOf_T_inf_L0 ψ₀ hψ₀s
  have hU := isSylowTwoOf_uni_prod (K := K) (by have := S.two_le; omega) hK'
  obtain ⟨δ, -, hδ⟩ := A4.exists_conj_of_isSylowTwoOf hU hS'
  let c : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →*
      SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K :=
    (MulAut.conj δ⁻¹).toMonoidHom
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, e₀.trans (Om4.rho δ⁻¹),
    c.comp ψ₀, ?_, fun k => ?_, ?_⟩
  · exact (MulAut.conj δ⁻¹).surjective.comp hψ₀s
  · refine MulEquiv.ext fun X => ?_
    have h1 := congrArg (fun φ : MulAut (Om4.VM K) => φ ((Om4.rho δ⁻¹).symm X)) (hψ₀ k)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply] at h1
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
      MonoidHom.comp_apply]
    have hc : c (ψ₀ k) = δ⁻¹ * ψ₀ k * δ := by simp [c]
    have hsymm : (Om4.rho δ⁻¹).symm X = Om4.rho δ X := by rw [map_inv]; rfl
    rw [← h1, hc, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hsymm]
  · rw [← Subgroup.map_map]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hδ x).mp hx
      simpa [c] using this
    · intro hy
      refine ⟨δ * y * δ⁻¹, (hδ _).mpr (by simpa [mul_assoc] using hy), ?_⟩
      simp [c, mul_assoc]

end Setup

end CFSG.Quasithin.H13.Ch9
