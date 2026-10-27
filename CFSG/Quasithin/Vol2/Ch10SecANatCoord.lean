module

public import CFSG.Quasithin.Vol2.Ch10SecALiftMain
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

structure NatCoord (T L I : Subgroup G) [IsMulCommutative ↥(fsuUL T L I)] (F : Type)
    [Field F] where
  eρ : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(autOn L (fsuUL T L I))
  β : ↥(fsuUL T L I) →* Multiplicative (Fin 2 → F)
  g : Matrix.SpecialLinearGroup (Fin 2) F
  surj : Function.Surjective β
  ker : ∀ w, β w = 1 ↔ w ∈ Ch10.cV1 T L I
  equivariant : ∀ γ w, β (((eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) w) =
    Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β w)))
  unip : ∀ γ, ((eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
    autOn (T ⊓ L) (fsuUL T L I) ↔ ∃ b : F, g * γ * g⁻¹ = unipSL b

theorem exists_natCoord (hyp : Ch10.Hyp10 G T L I) {n : ℕ} (h1 : Ch10.Case10_1_1One T L I n) :
    ∃ (_ : IsMulCommutative ↥(fsuUL T L I)) (F : Type) (_ : Field F) (_ : Finite F)
      (_ : CharP F 2), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧ Nonempty (NatCoord T L I F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, -, hUab, F, _, _, hF, π, hR⟩ := h1
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_beta_of_realizesVia_nat hR
  have hloc := hyp.fsu.maximal.1
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply FFModel.nat_faithful _ γ
    intro m _
    obtain ⟨w, rfl⟩ := hβs m
    have h1 : ((π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) w = w := by
      rw [hγ]
      rfl
    have h := hβe γ w
    rw [h1] at h
    exact Subgroup.mem_bot.mpr (mul_inv_eq_one.mpr h.symm)
  set eρ : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(autOn L (fsuUL T L I)) :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).trans
      (MulEquiv.ofBijective π ⟨hπinj, hR.1⟩) with heρ
  set Q' := (autOn (T ⊓ L) (fsuUL T L I)).subgroupOf (autOn L (fsuUL T L I)) with hQ'def
  have hQ' : Q' = ((T ⊓ L).subgroupOf L).map (autOnHomOf hLU) :=
    autOn_subgroupOf_eq_map (W := fsuUL T L I) (inf_le_right : T ⊓ L ≤ L) hLU
  set P := Q'.comap eρ.toMonoidHom with hPdef
  have hsylTL := isSylowTwoOf_inf hloc
  have hP2 : IsPGroup 2 P := by
    have hle : autOn (T ⊓ L) (fsuUL T L I) ≤ autOn L (fsuUL T L I) := A4.autOn_mono inf_le_right
    have hQ2 : IsPGroup 2 Q' :=
      (isPGroup_autOn hsylTL.2.1).of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
    exact hQ2.comap_of_injective eρ.toMonoidHom eρ.injective
  have hPidx : ¬ 2 ∣ P.index := by
    rw [hPdef, Subgroup.index_comap_of_surjective Q' eρ.surjective, hQ']
    exact fun h => hsylTL.2.2 (h.trans (Subgroup.index_map_dvd _ (autOnHomOf_surjective hLU)))
  obtain ⟨g, hgP, hPg⟩ := exists_conj_unip hF hP2 hPidx
  refine ⟨hUab, F, inferInstance, inferInstance, inferInstance, by omega, hF,
    ⟨⟨eρ, β, g, hβs, hβk, fun γ w => hβe _ w, fun γ => ?_⟩⟩⟩
  constructor
  · intro h
    exact hgP γ h
  · rintro ⟨b, hb⟩
    have h1 := hPg b
    have h2 : γ = g⁻¹ * unipSL b * g := by rw [← hb]; group
    rw [h2]
    exact h1

end CFSG.Quasithin.Vol2.Ch10.SecA
