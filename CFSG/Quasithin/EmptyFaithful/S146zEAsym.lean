module

public import CFSG.Quasithin.EmptyFaithful.S146zERank

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section AsymMain

variable {G : Type} [Group G] [Finite G] {T M K Kp U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem asym_facts (S : Setting146 G T M) (c23 : Conc14623 T M)
    (cK : ThreeC.CCtx T M K U₁ U₂ s) (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (hNorm₁ : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (K : Set G))
    (hNorm₂ : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (Kp : Set G))
    (hA : F8.A₁ Zz (g : G) ≤ ⁅uOfL22 T M, K⁆ ⊔ Zz)
    (hlt : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) <
      mIdx (uOfL22 T M) (centralizerMod Zz (uOfL22 T M) (F8.Uγ (VZ T M) (mcOf T) (g : G))))
    (hasym : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) <
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)))
    (hNK : ¬ F8.Uγ (VZ T M) (mcOf T) (g : G) ≤
        centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, K⁆ ⊔ Zz) →
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
          (centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, K⁆ ⊔ Zz)) + 1 ≤
        mIdx (⁅uOfL22 T M, K⁆ ⊔ Zz)
          (centralizerMod Zz (⁅uOfL22 T M, K⁆ ⊔ Zz) (F8.Uγ (VZ T M) (mcOf T) (g : G))))
    (hNp : ¬ F8.Uγ (VZ T M) (mcOf T) (g : G) ≤
        centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, Kp⁆ ⊔ Zz) →
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
          (centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, Kp⁆ ⊔ Zz)) + 1 ≤
        mIdx (⁅uOfL22 T M, Kp⁆ ⊔ Zz)
          (centralizerMod Zz (⁅uOfL22 T M, Kp⁆ ⊔ Zz) (F8.Uγ (VZ T M) (mcOf T) (g : G)))) :
    (∀ e ∈ F8.Uγ (VZ T M) (mcOf T) (g : G), ∀ y ∈ ⁅uOfL22 T M, Kp⁆ ⊔ Zz, e * y * e⁻¹ * y⁻¹ ∈ Zz) ∧
      mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) = 1 ∧
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) = 2 ∧
      (∀ b ∈ F8.Uγ (VZ T M) (mcOf T) (g : G), conjSub b U₁ = U₁) ∧
      ¬ F8.Uγ (VZ T M) (mcOf T) (g : G) ≤
        centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, K⁆ ⊔ Zz) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨hF81, hF98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hG)
  have hK := cK.hKc
  have hXH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hXab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hXN : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (Zz : Set G) := fun e he => by
    rw [S.normalizer_Z]; exact hXH he
  have hUKU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hK)
  have hUpU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKp)
  have hA₁c : Nat.card (F8.A₁ Zz (g : G)) = 2 := hF98.card_A₁
  have hA₁Z : F8.A₁ Zz (g : G) ⊓ Zz = ⊥ := by rw [inf_comm]; exact F8.F87_5b hF81 hsetup
  have hrank : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
      (centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, K⁆ ⊔ Zz)) ≤ 2 := by
    rw [cK.hsup]
    exact cK.rank_le_two S hXH hNorm₁ hXab
  obtain ⟨hUpE, hd1, hr2, hnt⟩ := ThreeC.asym_numerics (Z := Zz) (U := uOfL22 T M)
    (UK := ⁅uOfL22 T M, K⁆ ⊔ Zz) (Up := ⁅uOfL22 T M, Kp⁆ ⊔ Zz)
    (X := F8.Uγ (VZ T M) (mcOf T) (g : G)) (C := cuOf T M) (A₁ := F8.A₁ Zz (g : G))
    (D := F8.DH (VZ T M) Zz (mcOf T) (g : G)) (Dg := F8.Dγ (VZ T M) Zz (mcOf T) (g : G))
    hUab hXab hUN hUKU hUpU le_sup_right le_sup_right
    (inf_eq_Z_two S c23 hK hKp hne) (cuOf_le T M)
    (fun v hv => exists_decomp_two S c23 hcomps hK hKp hv)
    (fun c hc e he => (mem_cuOf.mp hc).2.2 e (hXH he)) hXN
    (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_commutator_sup (hNorm₁ he) (le_normalizer_conjClosure _ _ (hXH he)) (hXN he)) y).mp hy)
    (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_commutator_sup (hNorm₂ he) (le_normalizer_conjClosure _ _ (hXH he)) (hXN he)) y).mp hy)
    (fun e he y hy => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ (hXH he)) y).mp hy)
    hF98.A₁_le_Uγ hA₁c rfl hA₁Z hA (centralizerMod_le_left _ _ _)
    (fun x hx v hv => hx.2.2 v hv) (fun x hx h => ⟨hx, hXN hx, h⟩) hlt hasym hrank hNK hNp
  have hpos : 0 < mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) := by
    omega
  have hle' : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) := hasym.le
  have hQ := (hF98.F916_2_aux hsetup hpos hle').1
  have hUgp : IsPGroup 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := isPGroup_of_isElemAbelian hXab
  have hrel : ¬ (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)).relIndex
      (F8.Uγ (VZ T M) (mcOf T) (g : G)) ∣ 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUgp, hr2]; norm_num
  have hin := all_inner3 S c23 cK hKp hcomps hXH hNorm₁ hXab
    (hF98.Dγ_eq_inf_pCoreOf hsetup) hrel hQ.2.2.2.1 hUpE
  exact ⟨hUpE, hd1, hr2, hin, hnt⟩

theorem asym_main (S : Setting146 G T M) (h4 : Stage1463Four) (c23 : Conc14623 T M)
    (cK : PCtx T M K U₁ U₂ s u) (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (hNorm₁ : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (K : Set G))
    (hNorm₂ : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (Kp : Set G))
    (hA : F8.A₁ Zz (g : G) ≤ ⁅uOfL22 T M, K⁆ ⊔ Zz)
    (hlt : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) <
      mIdx (uOfL22 T M) (centralizerMod Zz (uOfL22 T M) (F8.Uγ (VZ T M) (mcOf T) (g : G))))
    (hasym : mIdx (uOfL22 T M) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) <
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)))
    (hNK : ¬ F8.Uγ (VZ T M) (mcOf T) (g : G) ≤
        centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, K⁆ ⊔ Zz) →
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
          (centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, K⁆ ⊔ Zz)) + 1 ≤
        mIdx (⁅uOfL22 T M, K⁆ ⊔ Zz)
          (centralizerMod Zz (⁅uOfL22 T M, K⁆ ⊔ Zz) (F8.Uγ (VZ T M) (mcOf T) (g : G))))
    (hNp : ¬ F8.Uγ (VZ T M) (mcOf T) (g : G) ≤
        centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, Kp⁆ ⊔ Zz) →
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
          (centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (⁅uOfL22 T M, Kp⁆ ⊔ Zz)) + 1 ≤
        mIdx (⁅uOfL22 T M, Kp⁆ ⊔ Zz)
          (centralizerMod Zz (⁅uOfL22 T M, Kp⁆ ⊔ Zz) (F8.Uγ (VZ T M) (mcOf T) (g : G)))) :
    False := by
  classical
  obtain ⟨hUpE, hd1, hr2, hin, -⟩ := asym_facts S c23 cK.toCCtx hKp hne hcomps hsetup hNorm₁ hNorm₂ hA hlt
    hasym hNK hNp
  exact false_of_rank_two_one3 S h4 c23 cK hKp hcomps hsetup hNorm₁ hin hUpE hd1 (by omega)

end AsymMain

end CFSG.Quasithin.ThreeD
