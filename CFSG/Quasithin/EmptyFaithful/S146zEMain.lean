module

public import CFSG.Quasithin.EmptyFaithful.S146zEAsym
public import CFSG.Quasithin.EmptyFaithful.S146zEChoice
public import CFSG.Quasithin.EmptyFaithful.S146zDMain

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem isCase2_of_isCase2_comp (S : Setting146 G T M) {K Kp : Subgroup G} (hKp : Kp ∈ cComp (mcOf T))
    (hne : Kp ≠ K) (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (h : IsCase2 T Kp) :
    IsCase2 T K := by
  obtain ⟨t, htT, htn, hpc⟩ := h
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have htH : t ∈ mcOf T := hG.1.1 htT
  have h1 : conjSub t Kp ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hKp htH
  have hK : conjSub t Kp = K := by
    rcases hcomps _ h1 with h | h
    · exact h
    · exact absurd (mem_normalizer_of_conjSub_eq h) htn
  refine ⟨t⁻¹, T.inv_mem htT, ?_, ?_⟩
  · intro htK
    apply hne
    have h2 : conjSub t⁻¹ K = K := conjSub_eq_of_mem_normalizer htK
    have h3 : conjSub t K = K := by
      have := congrArg (conjSub t) h2
      rw [conjSub_inv_conjSub] at this
      exact this.symm
    have h4 : conjSub t Kp = conjSub t K := by rw [hK, h3]
    exact (conjSub_inj t).mp h4
  · have h5 : conjSub t⁻¹ K = Kp := by rw [← hK, conjSub_conjSub_inv]
    rw [h5, hpc, ← hK, sup_comm]

theorem natCard_comp_eq_of_isCase2 (S : Setting146 G T M) {K Kp : Subgroup G}
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (hK : K ∈ cComp (mcOf T))
    (h : IsCase2 T K) : Nat.card Kp = Nat.card K := by
  obtain ⟨t, htT, htn, -⟩ := h
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have h1 : conjSub t K ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK (hG.1.1 htT)
  have hKp : conjSub t K = Kp := by
    rcases hcomps _ h1 with h | h
    · exact absurd (mem_normalizer_of_conjSub_eq h) htn
    · exact h
  rw [← hKp, natCard_conjSub_eq]

theorem mem_cComp_of_le_of_isCase2 (S : Setting146 G T M) {K Kp : Subgroup G}
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (hK : K ∈ cComp (mcOf T))
    (h2 : IsCase2 T K) {g : G} {J : Subgroup G} (hJ : J ∈ cComp (conjSub g (mcOf T))) (hle : Kp ≤ J) :
    Kp ∈ cComp (conjSub g (mcOf T)) := by
  obtain ⟨L, hL, rfl⟩ := ThreeD.exists_conj_mem_cComp hJ
  have hcard := natCard_comp_eq_of_isCase2 S hcomps hK h2
  have hJc : Nat.card (conjSub g L) = Nat.card Kp := by
    rw [natCard_conjSub_eq]
    rcases hcomps L hL with h | h
    · rw [h, hcard]
    · rw [h]
  have heq : Kp = conjSub g L := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hJc)
  rw [heq]; exact hJ

end Main

section Asym

@[expose] def Input14624ThreeDAsymTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G)
      (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
      Full24 T M K U₁ U₂ s u γ γ' g → ∀ Kp : Subgroup G, Comps24 T M K Kp → Norm24 T M K Kp g →
        IsCase2 T K →
        mIdx (conjClosure (VZ T M) (mcOf T))
            (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) <
          mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
            (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) →
        (F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤
            ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T →
          ∃ J ∈ cComp (conjSub (g : G) (mcOf T)), Kp ≤ J) ∧
        (F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤
            ⁅uOfL22 T M, Kp⁆ ⊔ quasithinOmegaOneCenter T →
          ∃ J ∈ cComp (conjSub (g : G) (mcOf T)), K ≤ J)

theorem input14624ThreeDAsym_of (h4 : Stage1463Four) (h5 : Stage1461Five) (iU1 : Input14624U1)
    (iU3 : Input14624U3) (iKM : Input14624KMoves) (i2 : Input14624ThreeDAsymTwo) :
    Input14624ThreeDAsym := by
  intro G _ _ T M S hB K U₁ U₂ s u γ γ' g hfull Kp hC hnorm hclaim hlt
  classical
  have hfull' := hfull
  have hnorm' := hnorm
  obtain ⟨hctx, hall, hgeom⟩ := hfull
  obtain ⟨c19, c20, c23, hKc, c21, c22, hdec, -⟩ := hctx
  obtain ⟨hsetup, hDlt, hpos, hle, hltf, -⟩ := hgeom
  obtain ⟨hNorm₁, hNorm₂, -⟩ := hnorm
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨hF81, hF98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hG)
  obtain ⟨c21p, c22p⟩ := hall Kp hC.mem
  obtain ⟨⟨U₁', U₂', s', hdecKp⟩, -⟩ := c22p
  have hc22Kp : Conc14622 T M Kp := (hall Kp hC.mem).2
  have cK0 : ThreeC.CCtx T M K U₁ U₂ s := ThreeC.CCtx.ofDecomp S c19 hKc hC.l3.1 hdec
  have cKp0 : ThreeC.CCtx T M Kp U₁' U₂' s' := ThreeC.CCtx.ofDecomp S c19 hC.mem hC.l3.2 hdecKp
  have hXH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hXab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hNK := fun hn => input14624NonFF_proof G T M S hB c19 K U₁ U₂ s hKc hC.l3.1 hdec _ hXH hNorm₁ hXab hn
  have hNp := fun hn => input14624NonFF_proof G T M S hB c19 Kp U₁' U₂' s' hC.mem hC.l3.2 hdecKp _ hXH
    hNorm₂ hXab hn
  have hcompsK : ∀ L ∈ cComp (mcOf T), L = Kp ∨ L = K := fun L hL => (hC.comps L hL).symm
  have hA₁c : Nat.card (F8.A₁ (quasithinOmegaOneCenter T) (g : G)) = 2 := hF98.card_A₁
  have hA₁Z : F8.A₁ (quasithinOmegaOneCenter T) (g : G) ⊓ (quasithinOmegaOneCenter T) = ⊥ := by rw [inf_comm]; exact F8.F87_5b hF81 hsetup
  by_cases hC2 : IsCase2 T K
  ·
    obtain ⟨hJ₁, hJ₂⟩ := i2 G T M S hB K U₁ U₂ s u γ γ' g hfull' Kp hC hnorm' hC2 hlt
    rcases hclaim with hA | hA
    · obtain ⟨-, -, -, -, hnt⟩ := ThreeD.asym_facts S c23 cK0 hC.mem hC.ne hC.comps hsetup hNorm₁ hNorm₂
        hA hltf hlt hNK hNp
      obtain ⟨J, hJ, hKpJ⟩ := hJ₁ hA
      have hKpC := mem_cComp_of_le_of_isCase2 S hC.comps hKc hC2 hJ hKpJ
      rw [cK0.hsup] at hnt
      exact ThreeD.engine S c19 cK0 hC.mem hC.ne hC.comps rfl rfl hXH hXab hNorm₁ hNorm₂ hA₁c hA₁Z
        (hA.trans cK0.hsup.le) hnt hKpC
    · obtain ⟨-, -, -, -, hnt⟩ := ThreeD.asym_facts S c23 cKp0 hKc hC.ne.symm hcompsK hsetup hNorm₂
        hNorm₁ hA hltf hlt hNp hNK
      obtain ⟨J, hJ, hKJ⟩ := hJ₂ hA
      have hC2p : IsCase2 T Kp := isCase2_of_isCase2_comp S (K := Kp) (Kp := K) hKc hC.ne.symm hcompsK hC2
      have hKC := mem_cComp_of_le_of_isCase2 S hcompsK hC.mem hC2p hJ hKJ
      rw [cKp0.hsup] at hnt
      exact ThreeD.engine S c19 cKp0 hKc hC.ne.symm hcompsK rfl rfl hXH hXab hNorm₂ hNorm₁ hA₁c hA₁Z
        (hA.trans cKp0.hsup.le) hnt hKC
  ·
    have hC2p : ¬ IsCase2 T Kp := fun h => hC2 (isCase2_of_isCase2_comp S hC.mem hC.ne hC.comps h)
    obtain ⟨uK, cK⟩ := ThreeD.exists_pctx S hB h5 iU1 iU3 iKM c19 c20 c23 hKc c21 c22 hC.l3.1 hdec hC2
    obtain ⟨uKp, cKp⟩ := ThreeD.exists_pctx S hB h5 iU1 iU3 iKM c19 c20 c23 hC.mem c21p hc22Kp hC.l3.2
      hdecKp hC2p
    rcases hclaim with hA | hA
    · exact ThreeD.asym_main S h4 c23 cK hC.mem hC.ne hC.comps hsetup hNorm₁ hNorm₂ hA hltf hlt hNK hNp
    · exact ThreeD.asym_main S h4 c23 cKp hKc hC.ne.symm hcompsK hsetup hNorm₂ hNorm₁ hA hltf hlt hNp hNK

end Asym

end CFSG.Quasithin
