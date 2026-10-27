module

public import CFSG.Quasithin.EmptyFaithful.S146zNCount
public import CFSG.Quasithin.EmptyFaithful.S146F22
public import CFSG.Quasithin.EmptyFaithful.S146yB
public import CFSG.Quasithin.EmptyFaithful.S146zDNum

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section ClaimNum

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem claim_of_numerics (S : Setting146 G T M) (hB : HypB146 T M) (c19 : Conc14619 T M)
    (c23 : Conc14623 T M) {K Kp U₁ U₂ U₁' U₂' : Subgroup G} {s s' : G}
    (hKc : K ∈ cComp (mcOf T)) (hL3K : KbarIsL3Two K) (hdec : IsDecompUK T M K U₁ U₂ s)
    (hKpc : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (hL3Kp : KbarIsL3Two Kp)
    (hdecKp : IsDecompUK T M Kp U₁' U₂' s')
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (hle : mIdx (conjClosure (VZ T M) (mcOf T)) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)))
    (hlt : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) <
      mIdx (conjClosure (VZ T M) (mcOf T))
        (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) (F8.Uγ (VZ T M) (mcOf T) (g : G))))
    (hNorm₁ : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (K : Set G))
    (hNorm₂ : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (Kp : Set G)) :
    F8.A₁ Zz (g : G) ≤ ⁅uOfL22 T M, K⁆ ⊔ Zz ∨ F8.A₁ Zz (g : G) ≤ ⁅uOfL22 T M, Kp⁆ ⊔ Zz := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hnK, hnp⟩ := hcon
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hXH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hXab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) :=
    S.conjClosure_le_normalizer_Z hG
  have hXN : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (Zz : Set G) := fun e he => by
    rw [S.normalizer_Z]; exact hXH he
  have hUKU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKc)
  have hUpU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKpc)
  refine ThreeC.claim_contra (Z := Zz) (U := uOfL22 T M)
    (UK := ⁅uOfL22 T M, K⁆ ⊔ Zz)
    (Up := ⁅uOfL22 T M, Kp⁆ ⊔ Zz)
    (X := F8.Uγ (VZ T M) (mcOf T) (g : G)) (C := cuOf T M)
    (A₁ := F8.A₁ Zz (g : G))
    (D := F8.DH (VZ T M) Zz (mcOf T) (g : G))
    (Dg := F8.Dγ (VZ T M) Zz (mcOf T) (g : G))
    hUab hXab hUN hUKU hUpU le_sup_right le_sup_right
    (inf_eq_Z_two S c23 hKc hKpc hne) (cuOf_le T M)
    (fun v hv => exists_decomp_two S c23 hcomps hKc hKpc hv)
    (fun c hc e he => (mem_cuOf.mp hc).2.2 e (hXH he)) hXN
    (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_commutator_sup (hNorm₁ he) (le_normalizer_conjClosure _ _ (hXH he)) (hXN he)) y).mp hy)
    (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_commutator_sup (hNorm₂ he) (le_normalizer_conjClosure _ _ (hXH he)) (hXN he)) y).mp hy)
    (fun e he y hy => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ (hXH he)) y).mp hy)
    hF98.A₁_le_Uγ hF98.card_A₁ rfl hnK hnp (centralizerMod_le_left _ _ _)
    (fun x hx v hv => hx.2.2 v hv) (fun x hx h => ⟨hx, hXN hx, h⟩) hle hlt
    (fun hn => input14624NonFF_proof G T M S hB c19 K U₁ U₂ s hKc hL3K hdec _ hXH hNorm₁ hXab hn)
    (fun hn => input14624NonFF_proof G T M S hB c19 Kp U₁' U₂' s' hKpc hL3Kp hdecKp _ hXH hNorm₂ hXab hn)

theorem norm_of_numerics (S : Setting146 G T M) (hB : HypB146 T M) (c23 : Conc14623 T M)
    {K Kp : Subgroup G} (hK : K ∈ cComp (mcOf T)) (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (hL3K : KbarIsL3Two K) (hL3Kp : KbarIsL3Two Kp)
    (hrankK : mIdx (⁅uOfL22 T M, K⁆ ⊔ Zz) Zz = 6) (hrankKp : mIdx (⁅uOfL22 T M, Kp⁆ ⊔ Zz) Zz = 6)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)))
    (hle : mIdx (conjClosure (VZ T M) (mcOf T)) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G))) :
    F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (K : Set G) ∧
      F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (Kp : Set G) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hAH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hAab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hQ := (hF98.F916_2_aux hsetup hpos hle).1
  have hoff := hQ.2.2.2.2
  have hcomps' : ∀ L ∈ cComp (mcOf T), L = Kp ∨ L = K := fun L hL => (hcomps L hL).symm
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra hxn
    exact false_of_swap S hB c23 hK hKp hne hcomps hL3K hrankK hAH hAab hoff hx hxn
  · by_contra hxn
    exact false_of_swap S hB c23 hKp hK hne.symm hcomps' hL3Kp hrankKp hAH hAab hoff hx hxn

theorem claim_of_numerics' (S : Setting146 G T M) (hB : HypB146 T M) (c19 : Conc14619 T M)
    (c23 : Conc14623 T M) {K Kp U₁ U₂ U₁' U₂' : Subgroup G} {s s' : G}
    (hKc : K ∈ cComp (mcOf T)) (hL3K : KbarIsL3Two K) (hdec : IsDecompUK T M K U₁ U₂ s)
    (hKpc : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (hL3Kp : KbarIsL3Two Kp)
    (hdecKp : IsDecompUK T M Kp U₁' U₂' s')
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (hDlt : F8.Dγ (VZ T M) Zz (mcOf T) (g : G) < F8.Uγ (VZ T M) (mcOf T) (g : G))
    (hle : mIdx (conjClosure (VZ T M) (mcOf T)) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)))
    (hNorm₁ : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (K : Set G))
    (hNorm₂ : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (Kp : Set G)) :
    F8.A₁ Zz (g : G) ≤ ⁅uOfL22 T M, K⁆ ⊔ Zz ∨ F8.A₁ Zz (g : G) ≤ ⁅uOfL22 T M, Kp⁆ ⊔ Zz := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hXH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hXab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hXN : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (Zz : Set G) := fun e he => by
    rw [S.normalizer_Z]; exact hXH he
  have hUKU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKc)
  have hUpU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKpc)
  have hlt : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) <
      mIdx (conjClosure (VZ T M) (mcOf T))
        (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) (F8.Uγ (VZ T M) (mcOf T) (g : G))) := by
    refine r_lt_f (Z := Zz) (U := uOfL22 T M)
      (UK := ⁅uOfL22 T M, K⁆ ⊔ Zz) (Up := ⁅uOfL22 T M, Kp⁆ ⊔ Zz)
      (X := F8.Uγ (VZ T M) (mcOf T) (g : G)) (C := cuOf T M)
      hUab hXab hUN hUKU hUpU le_sup_right le_sup_right
      (inf_eq_Z_two S c23 hKc hKpc hne) (cuOf_le T M)
      (fun v hv => exists_decomp_two S c23 hcomps hKc hKpc hv)
      (fun c hc e he => (mem_cuOf.mp hc).2.2 e (hXH he)) hXN
      (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_commutator_sup (hNorm₁ he) (le_normalizer_conjClosure _ _ (hXH he)) (hXN he))
          y).mp hy)
      (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_commutator_sup (hNorm₂ he) (le_normalizer_conjClosure _ _ (hXH he)) (hXN he))
          y).mp hy)
      (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure _ _ (hXH he)) y).mp hy)
      ?_ ?_ ?_
    · intro hX
      exact hDlt.ne (le_antisymm hDlt.le hX)
    · exact fun hn => input14624NonFF_proof G T M S hB c19 K U₁ U₂ s hKc hL3K hdec _ hXH hNorm₁ hXab hn
    · exact fun hn => input14624NonFF_proof G T M S hB c19 Kp U₁' U₂' s' hKpc hL3Kp hdecKp _ hXH
        hNorm₂ hXab hn
  exact claim_of_numerics S hB c19 c23 hKc hL3K hdec hKpc hne hcomps hL3Kp hdecKp hsetup hle hlt
    hNorm₁ hNorm₂

end ClaimNum

end CFSG.Quasithin.ThreeD
