module

public import CFSG.Quasithin.Vol2.Ch10SecB4Lift2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem conjLBar_surjective {K T : Subgroup G} {k : ℕ}
    (hK : StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL k 2 1) (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hEN : K ⊔ T ≤ Subgroup.normalizer (K : Set G))
    (hAut : Nonempty (↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T) ≃*
      MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)))) :
    Function.Surjective (conjLBar K T hEN) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcl := center_lbar_eq_bot hK
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hK
  have hF2 : Nat.card F = 2 := by simpa using hF
  set e := e₀.trans (Setup.Family.statedProjSL_equiv_of_card_two k F hF2)
  set φ := conjLBar K T hEN with hφ
  have : (K.subgroupOf (K ⊔ T)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEN
  have hq := isPGroup_quotient_sup hT hTK
  have hkerp : IsPGroup 2 φ.ker := by
    intro x
    obtain ⟨a, ha⟩ := hq (QuotientGroup.mk (x : ↥(K ⊔ T)))
    have h1 : (x : ↥(K ⊔ T)) ^ 2 ^ a ∈ K.subgroupOf (K ⊔ T) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact ha
    have hyK : ((x : ↥(K ⊔ T)) ^ 2 ^ a : G) ∈ K := h1
    have hy : (x : ↥(K ⊔ T)) ^ 2 ^ a ∈ φ.ker := Subgroup.pow_mem _ x.2 _
    have hyO : (⟨_, hyK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      have hc : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨_, hyK⟩ ∈
          Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
        rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective _ z
        have h2 := DFunLike.congr_fun (MonoidHom.mem_ker.1 hy) (QuotientGroup.mk' _ ⟨l, hl⟩)
        rw [conjLBar_mk, MulAut.one_apply] at h2
        have h3 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨_, hyK⟩ * ⟨l, hl⟩ * (⟨_, hyK⟩ : ↥K)⁻¹) =
            QuotientGroup.mk' _ ⟨l, hl⟩ := by
          rw [← h2]
          congr 1
        rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at h3
        exact h3.symm
      rw [hcl, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
      exact hc
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hyO⟩
    refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
    have hb' : (((x : ↥(K ⊔ T)) ^ 2 ^ a : ↥(K ⊔ T)) : G) ^ 2 ^ b = 1 :=
      congrArg (fun z => ((z : ↥K) : G)) (congrArg Subtype.val hb)
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at hb' ⊢
    rw [pow_add, pow_mul, hb']
  have hle : φ.ker ≤ CFSG.pCore 2 ↥(K ⊔ T) := le_sSup ⟨φ.normal_ker, hkerp⟩
  obtain ⟨ι⟩ := hAut
  have : Finite (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Finite.of_injective (fun f : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) => (f : _ → _))
      DFunLike.coe_injective
  have hc1 : Nat.card (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) =
      Nat.card (↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T)) := by
    rw [Nat.card_congr ι.toEquiv, Nat.card_congr (MulAut.congr e).toEquiv]
  have hc2 : Nat.card (↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T)) ≤ Nat.card φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hle)
  have htop : φ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm ?_ (hc1 ▸ hc2))
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  exact MonoidHom.range_eq_top.1 htop

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
