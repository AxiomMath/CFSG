module

public import CFSG.Quasithin.EmptyFaithful.S146zDSym
public import CFSG.Quasithin.EmptyFaithful.S146zDClaim

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem threeD_sym (S : Setting146 G T M) (hB : HypB146 T M)
    {K U₁ U₂ : Subgroup G} {s u : G} {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)}
    {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)} (hfull : Full24 T M K U₁ U₂ s u γ γ' g)
    {Kp : Subgroup G} (hC : Comps24 T M K Kp) (hnorm : Norm24 T M K Kp g)
    (hclaim : Claim24 T M K Kp g)
    (hsym : mIdx (conjClosure (VZ T M) (mcOf T)) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) =
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G))) : False := by
  classical
  obtain ⟨hctx, hall, hgeom⟩ := hfull
  obtain ⟨c19, -, c23, hKc, -, c22, hdec, -⟩ := hctx
  obtain ⟨hsetup, hDlt, hpos, hle, hlt, -⟩ := hgeom
  obtain ⟨hNorm₁, hNorm₂, -⟩ := hnorm
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨hF81, hF98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hG)
  obtain ⟨⟨U₁', U₂', s', hdecKp⟩, hc22Kp'⟩ := (hall Kp hC.mem).2
  have cK : ThreeC.CCtx T M K U₁ U₂ s := ThreeC.CCtx.ofDecomp S c19 hKc hC.l3.1 hdec
  have cKp : ThreeC.CCtx T M Kp U₁' U₂' s' := ThreeC.CCtx.ofDecomp S c19 hC.mem hC.l3.2 hdecKp
  have hc22K : ⁅⁅uOfL22 T M, K⁆, Kp⁆ = ⊥ := c22.2 Kp hC.mem hC.ne
  have hc22Kp : ⁅⁅uOfL22 T M, Kp⁆, K⁆ = ⊥ := hc22Kp' K hKc hC.ne.symm
  have hcompsK : ∀ L ∈ cComp (mcOf T), L = Kp ∨ L = K := fun L hL => (hC.comps L hL).symm
  have hkz : perfectCore (mcOf T) = Kp ⊔ K := by rw [hC.kz, sup_comm]
  have hEH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hEab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hA₁c : Nat.card (F8.A₁ Zz (g : G)) = 2 := hF98.card_A₁
  have hA₁Z : F8.A₁ Zz (g : G) ⊓ Zz = ⊥ := by rw [inf_comm]; exact F8.F87_5b hF81 hsetup
  have hntU : ¬ F8.Uγ (VZ T M) (mcOf T) (g : G) ≤
      centralizerMod Zz (F8.Uγ (VZ T M) (mcOf T) (g : G)) (uOfL22 T M) := fun h =>
    hDlt.ne (le_antisymm hDlt.le h)
  have hn := hF98.not_Vγ_le_ballStab_of_lt hsetup hDlt
  obtain ⟨δ, δ', k, y, hsetup', hyγ, hyγ₁, hUδ, hUy, hDHδ, hDγδ⟩ :=
    hF98.exists_symmetric_setup hsetup hn
  have hd : mIdx (F8.Uγ (VZ T M) (mcOf T) (k : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (k : G)) =
      mIdx (conjClosure (VZ T M) (mcOf T)) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) := by
    rw [hUδ, hDγδ, F9.mIdx_conjSub]
  have hr : mIdx (conjClosure (VZ T M) (mcOf T)) (F8.DH (VZ T M) Zz (mcOf T) (k : G)) =
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) := by
    rw [hDHδ]
    have e : conjClosure (VZ T M) (mcOf T) =
        conjSub (y : G) (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hUy.symm
    rw [e, F9.mIdx_conjSub]
  have hle_k : mIdx (conjClosure (VZ T M) (mcOf T)) (F8.DH (VZ T M) Zz (mcOf T) (k : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (k : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (k : G)) := by
    rw [hr, hd]; omega
  have hpos_k : 0 < mIdx (F8.Uγ (VZ T M) (mcOf T) (k : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (k : G)) := by
    rw [hd]; exact hpos
  have hDlt_k : F8.Dγ (VZ T M) Zz (mcOf T) (k : G) < F8.Uγ (VZ T M) (mcOf T) (k : G) := by
    rw [hDγδ, hUδ]
    have h17 := hF98.lemma_14_5_17 hsetup
    exact lt_of_le_of_ne (conjSub_mono _ h17.le) (fun h => h17.ne ((conjSub_inj _).mp h))
  obtain ⟨hNorm₁', hNorm₂'⟩ := ThreeD.norm_of_numerics S hB c23 hKc hC.mem hC.ne hC.comps hC.l3.1 hC.l3.2
    hC.rank.1 hC.rank.2 hsetup' hpos_k hle_k
  have hclaim_k := ThreeD.claim_of_numerics' S hB c19 c23 hKc hC.l3.1 hdec hC.mem hC.ne hC.comps hC.l3.2
    hdecKp hsetup' hDlt_k hle_k hNorm₁' hNorm₂'
  have hA₁c' : Nat.card (F8.A₁ Zz (k : G)) = 2 := hF98.card_A₁
  have hA₁Z' : F8.A₁ Zz (k : G) ⊓ Zz = ⊥ := by rw [inf_comm]; exact F8.F87_5b hF81 hsetup'
  have hygH : (y : G) * (g : G) ∈ mcOf T := by
    have h1'' : (y * g) • F8.γ₁ T (yOfL22 T M) (mcOf T) = F8.γ₁ T (yOfL22 T M) (mcOf T) := by
      rw [mul_smul, hsetup.edge₁, hyγ]
    have := mem_stab_of_smul_eq h1''
    rwa [stab_γ₁ hF98.amalgamHypV.le₂] at this
  have hkyH : (k : G)⁻¹ * (y : G) ∈ mcOf T := by
    have h1'' : (k⁻¹ * y) • F8.γ₁ T (yOfL22 T M) (mcOf T) = F8.γ₁ T (yOfL22 T M) (mcOf T) := by
      rw [mul_smul, hyγ₁, ← hsetup'.edge₁, inv_smul_smul]
    have := mem_stab_of_smul_eq h1''
    rw [stab_γ₁ hF98.amalgamHypV.le₂] at this
    simpa using this
  rcases hclaim with hA | hA <;> rcases hclaim_k with hA' | hA'
  ·
    have hnt := ThreeD.datum_nontriv S c23 cK cKp hC.mem hC.comps hC.kz hc22K hc22Kp rfl rfl hA₁c
      hA₁Z (hA.trans cK.hsup.le) hEH hEab hNorm₂ hntU
    exact ThreeD.sym_core S c19 c23 cK cK hC.mem hC.mem hC.ne hC.comps hC.comps hC.kz hC.kz
      hc22K hc22Kp hc22K hc22Kp rfl rfl rfl hEH hEab hNorm₁ hNorm₂ hA₁c hA₁Z (hA.trans cK.hsup.le)
      hnt hA₁c' hA₁Z' (hA'.trans cK.hsup.le) hygH hkyH
  ·
    have hnt := ThreeD.datum_nontriv S c23 cK cKp hC.mem hC.comps hC.kz hc22K hc22Kp rfl rfl hA₁c
      hA₁Z (hA.trans cK.hsup.le) hEH hEab hNorm₂ hntU
    exact ThreeD.sym_core S c19 c23 cK cKp hC.mem hKc hC.ne hC.comps hcompsK hC.kz hkz
      hc22K hc22Kp hc22Kp hc22K rfl rfl rfl hEH hEab hNorm₁ hNorm₂ hA₁c hA₁Z (hA.trans cK.hsup.le)
      hnt hA₁c' hA₁Z' (hA'.trans cKp.hsup.le) hygH hkyH
  ·
    have hnt := ThreeD.datum_nontriv S c23 cKp cK hKc hcompsK hkz hc22Kp hc22K rfl rfl hA₁c
      hA₁Z (hA.trans cKp.hsup.le) hEH hEab hNorm₁ hntU
    exact ThreeD.sym_core S c19 c23 cKp cK hKc hC.mem hC.ne.symm hcompsK hC.comps hkz hC.kz
      hc22Kp hc22K hc22K hc22Kp rfl rfl rfl hEH hEab hNorm₂ hNorm₁ hA₁c hA₁Z (hA.trans cKp.hsup.le)
      hnt hA₁c' hA₁Z' (hA'.trans cK.hsup.le) hygH hkyH
  ·
    have hnt := ThreeD.datum_nontriv S c23 cKp cK hKc hcompsK hkz hc22Kp hc22K rfl rfl hA₁c
      hA₁Z (hA.trans cKp.hsup.le) hEH hEab hNorm₁ hntU
    exact ThreeD.sym_core S c19 c23 cKp cKp hKc hKc hC.ne.symm hcompsK hcompsK hkz hkz
      hc22Kp hc22K hc22Kp hc22K rfl rfl rfl hEH hEab hNorm₂ hNorm₁ hA₁c hA₁Z (hA.trans cKp.hsup.le)
      hnt hA₁c' hA₁Z' (hA'.trans cKp.hsup.le) hygH hkyH

@[expose] def Input14624ThreeDAsym : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G)
      (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
      Full24 T M K U₁ U₂ s u γ γ' g → ∀ Kp : Subgroup G, Comps24 T M K Kp → Norm24 T M K Kp g →
        Claim24 T M K Kp g →
        mIdx (conjClosure (VZ T M) (mcOf T))
            (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) <
          mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
            (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) → False

theorem input14624ThreeD_of (hasym : Input14624ThreeDAsym) : Input14624ThreeD := by
  intro G _ _ T M S hB K U₁ U₂ s u γ γ' g hfull Kp hC hnorm hclaim
  have hle := hfull.2.2.2.2.2.1
  rcases hle.lt_or_eq with hlt | heq
  · exact hasym G T M S hB K U₁ U₂ s u γ γ' g hfull Kp hC hnorm hclaim hlt
  · exact threeD_sym S hB hfull hC hnorm hclaim heq

end Main

end CFSG.Quasithin
