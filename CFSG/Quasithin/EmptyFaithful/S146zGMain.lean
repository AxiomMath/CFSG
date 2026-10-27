module

public import CFSG.Quasithin.EmptyFaithful.S146zGClaim
public import CFSG.Quasithin.EmptyFaithful.S146zGNum
public import CFSG.Quasithin.EmptyFaithful.S146zGSwap
public import CFSG.Quasithin.EmptyFaithful.S146zEMain
public import CFSG.Quasithin.EmptyFaithful.S146zDSym
public import CFSG.Quasithin.Background.GoldschmidtS146RQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.EmptyFaithful.S146F4

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section Contain

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

omit [Finite G] in
theorem mul_inv_mem_of_relIndex_two {D E : Subgroup G} (h : D.relIndex E = 2) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) (hxD : x ∉ D) (hyD : y ∉ D) : x * y⁻¹ ∈ D := by
  obtain ⟨b₀, hb₀, hb⟩ := Subgroup.relIndex_dvd_two_iff.mp (by rw [h])
  have h1 : x * b₀ ∈ D := (hb x hx).resolve_right hxD
  have h2 : y * b₀ ∈ D := (hb y hy).resolve_right hyD
  have e : x * y⁻¹ = (x * b₀) * (y * b₀)⁻¹ := by group
  rw [e]
  exact D.mul_mem h1 (D.inv_mem h2)

theorem contain_main (S : Setting146 G T M) (c19 : Conc14619 T M) (c23 : Conc14623 T M)
    {Ko Kop Uo₁ Uo₂ Vo₁ Vo₂ : Subgroup G} {so so' : G}
    (cKo : ThreeC.CCtx T M Ko Uo₁ Uo₂ so) (cKop : ThreeC.CCtx T M Kop Vo₁ Vo₂ so')
    (hneo : Kop ≠ Ko) (hcompso : ∀ L ∈ cComp (mcOf T), L = Ko ∨ L = Kop)
    (hkzo : perfectCore (mcOf T) = Ko ⊔ Kop)
    (hc22o₁ : ⁅⁅uOfL22 T M, Ko⁆, Kop⁆ = ⊥) (hc22o₂ : ⁅⁅uOfL22 T M, Kop⁆, Ko⁆ = ⊥)
    (hrk : mIdx (⁅uOfL22 T M, Ko⁆ ⊔ Zz) Zz = 6)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (hDlt : F8.Dγ (VZ T M) Zz (mcOf T) (g : G) < F8.Uγ (VZ T M) (mcOf T) (g : G))
    (hA : F8.A₁ Zz (g : G) ≤ Uo₁ ⊔ Uo₂)
    (hd1 : mIdx (conjClosure (VZ T M) (mcOf T)) (F8.DH (VZ T M) Zz (mcOf T) (g : G)) = 1)
    (hr2 : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G)) (F8.Dγ (VZ T M) Zz (mcOf T) (g : G)) = 2) :
    ∃ J ∈ cComp (conjSub (g : G) (mcOf T)), Kop ≤ J := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨hF81, hF98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hG)
  have hKo := cKo.hKc
  have hKop := cKop.hKc
  have hKoH : Ko ≤ mcOf T := le_of_mem_cComp hKo
  have hKopH : Kop ≤ mcOf T := le_of_mem_cComp hKop
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (conjClosure (VZ T M) (mcOf T)) := isPGroup_of_isElemAbelian hUab
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hUN : conjClosure (VZ T M) (mcOf T) ≤ Subgroup.normalizer (Zz : Set G) :=
    S.conjClosure_le_normalizer_Z hG
  have hA₁c : Nat.card (F8.A₁ Zz (g : G)) = 2 := hF98.card_A₁
  have hA₁Z : F8.A₁ Zz (g : G) ⊓ Zz = ⊥ := by rw [inf_comm]; exact F8.F87_5b hF81 hsetup
  obtain ⟨hKopg, -⟩ := partI S c23 cKo hKop hcompso hkzo hc22o₁ hc22o₂ (g := (g : G))
    (A₁ := F8.A₁ Zz (g : G)) rfl hA₁c hA₁Z hA
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
  have hygH : (y : G) * (g : G) ∈ mcOf T := by
    have h1'' : (y * g) • F8.γ₁ T (yOfL22 T M) (mcOf T) = F8.γ₁ T (yOfL22 T M) (mcOf T) := by
      rw [mul_smul, hsetup.edge₁, hyγ]
    have := mem_stab_of_smul_eq h1''
    rwa [stab_γ₁ hF98.amalgamHypV.le₂] at this
  have hconj1 : conjSub (y : G) (conjSub (g : G) (mcOf T)) = mcOf T := by
    rw [← conjSub_mul]; exact conjSub_eq_of_mem hygH
  have hconj3 : conjSub (y : G)⁻¹ (mcOf T) = conjSub (g : G) (mcOf T) := by
    have := congrArg (conjSub (y : G)⁻¹) hconj1
    rw [conjSub_conjSub_inv] at this
    exact this.symm
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, L = conjSub (y : G) Kop := ⟨_, rfl⟩
  have hLH : L ≤ mcOf T := by
    have h1 := conjSub_mono (y : G) hKopg
    rw [hconj1] at h1
    rw [hL]; exact h1
  have hLperf : ⁅L, L⁆ = L := by
    rw [hL, conjSub_commutator, perfect_of_mem_cComp hKop]
  have hLs : IsSimpleGroup (KBar L) := by
    have hsK : IsSimpleGroup (KBar Kop) := (c19 (mcOf T) hG).2 Kop hKop
    obtain ⟨e⟩ := GoldS146R.nonempty_kbar_conj (y : G) Kop
    rw [hL]
    exact (MulEquiv.isSimpleGroup_congr e).mpr hsK
  have hL168 : (pCoreOf 2 L).relIndex L = 168 := by
    rw [hL, pCoreOf_conjSub, F9.relIndex_conjSub]
    exact cKop.h168
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, E = F8.Uγ (VZ T M) (mcOf T) (k : G) := ⟨_, rfl⟩
  have hEH : E ≤ mcOf T := by rw [hE]; exact hF98.Uγ_le_H hsetup'
  have hEab : IsElemAbelian 2 E := by rw [hE]; exact hF98.isElemAbelian_Uγ
  have hEp : IsPGroup 2 E := isPGroup_of_isElemAbelian hEab
  have hEy : E = conjSub (y : G) (conjClosure (VZ T M) (mcOf T)) := by rw [hE]; exact hUδ
  have hDeq : F8.Dγ (VZ T M) Zz (mcOf T) (k : G) = E ⊓ pCoreOf 2 (mcOf T) := by
    rw [hE]; exact hF98.Dγ_eq_inf_pCoreOf hsetup'
  have hD1 : mIdx E (E ⊓ pCoreOf 2 (mcOf T)) = 1 := by
    rw [← hDeq, hE, hd, hd1]
  have hrel2 : (E ⊓ pCoreOf 2 (mcOf T)).relIndex E = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hEp, hD1]; norm_num
  obtain ⟨b, hbE, hbnQ'⟩ : ∃ b ∈ E, b ∉ E ⊓ pCoreOf 2 (mcOf T) := by
    by_contra hcon
    push Not at hcon
    have : (E ⊓ pCoreOf 2 (mcOf T)).relIndex E = 1 := Subgroup.relIndex_eq_one.mpr hcon
    omega
  have hbnQ : b ∉ pCoreOf 2 (mcOf T) := fun h => hbnQ' ⟨hbE, h⟩
  have hbH : b ∈ mcOf T := hEH hbE
  have hLE : L ≤ Subgroup.normalizer (E : Set G) := by
    rw [hL, hEy]
    exact conjSub_le_normalizer (hKopH.trans hHU)
  have hbL : ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 (mcOf T) := by
    intro l hl
    have hlH : l ∈ mcOf T := hLH hl
    have hlE : l * b * l⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hLE hl) b).mp hbE
    have hnD : l * b * l⁻¹ ∉ E ⊓ pCoreOf 2 (mcOf T) := by
      rintro ⟨-, hQ⟩
      apply hbnQ
      have h5 := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (mcOf T) ((mcOf T).inv_mem hlH)) _).mp hQ
      have e5 : l⁻¹ * (l * b * l⁻¹) * l⁻¹⁻¹ = b := by group
      rwa [e5] at h5
    have h1 := mul_inv_mem_of_relIndex_two hrel2 hlE hbE hnD hbnQ'
    have h2 : l * b * l⁻¹ * b⁻¹ ∈ pCoreOf 2 (mcOf T) := h1.2
    have e : b * l * b⁻¹ * l⁻¹ = (l * b * l⁻¹ * b⁻¹)⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 (mcOf T)).inv_mem h2
  have hnsw : conjSub b Ko ≠ Kop := by
    intro hsw
    have hbU : b ∈ Subgroup.normalizer (uOfL22 T M : Set G) := hHU hbH
    have hbZ : b ∈ Subgroup.normalizer (Zz : Set G) := by rw [S.normalizer_Z]; exact hbH
    have hb2 : b * b = 1 := by
      have := isElemAbelian_pow_eq_one hEab hbE
      simpa [pow_two] using this
    have hUKU := commutator_sup_le_U (T := T) (M := M) hKoH
    have hswapK : conjSub b (⁅uOfL22 T M, Ko⁆ ⊔ Zz) = ⁅uOfL22 T M, Kop⁆ ⊔ Zz := by
      rw [conjSub_sup, conjSub_commutator', conjSub_eq_of_mem_normalizer hbU, hsw,
        conjSub_eq_of_mem_normalizer hbZ]
    have h6 := ThreeC.swap_count (Z := Zz) (U := conjClosure (VZ T M) (mcOf T))
      (UK := ⁅uOfL22 T M, Ko⁆ ⊔ Zz) (Up := ⁅uOfL22 T M, Kop⁆ ⊔ Zz) hUp hUKU le_sup_right
      (inf_eq_Z_two S c23 hKo hKop hneo) hbZ hb2 hswapK hrk
    have hA₁c' : Nat.card (F8.A₁ Zz (k : G)) = 2 := hF98.card_A₁
    have hA₁Z' : F8.A₁ Zz (k : G) ⊓ Zz = ⊥ := by rw [inf_comm]; exact F8.F87_5b hF81 hsetup'
    have hf : mIdx (conjClosure (VZ T M) (mcOf T)) (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) E) ≤
        mIdx (conjClosure (VZ T M) (mcOf T)) (F8.DH (VZ T M) Zz (mcOf T) (k : G)) +
          mIdx E (F8.Dγ (VZ T M) Zz (mcOf T) (k : G)) := by
      rw [hE]
      exact ThreeC.mIdx_centralizerMod_le_add (Z := Zz) (U := conjClosure (VZ T M) (mcOf T))
        (X := F8.Uγ (VZ T M) (mcOf T) (k : G)) (A₁ := F8.A₁ Zz (k : G))
        (D := F8.DH (VZ T M) Zz (mcOf T) (k : G)) (Dg := F8.Dγ (VZ T M) Zz (mcOf T) (k : G))
        hUab hF98.isElemAbelian_Uγ hUN hF98.A₁_le_Uγ hA₁c' rfl hA₁Z'
        (centralizerMod_le_left _ _ _) (fun x hx v hv => hx.2.2 v hv)
    have hf2 : mIdx (conjClosure (VZ T M) (mcOf T))
          (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) (Subgroup.zpowers b)) ≤
        mIdx (conjClosure (VZ T M) (mcOf T)) (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) E) :=
      ThreeC.mIdx_anti_of_le (centralizerMod_anti_right _ (Subgroup.zpowers_le.mpr hbE))
    have hd' : mIdx E (F8.Dγ (VZ T M) Zz (mcOf T) (k : G)) = 1 := by rw [hE, hd, hd1]
    omega
  have hcases := perfect_le_comp S c23 cKo cKop hneo hcompso hkzo hc22o₁ hc22o₂ hLH hLperf hLs hL168
    hbH hbnQ hbL hnsw
  have hKopL : Kop ≤ conjSub (y : G)⁻¹ L := by
    rw [hL, conjSub_conjSub_inv]
  have hJ : ∀ K' ∈ cComp (mcOf T), conjSub (y : G)⁻¹ K' ∈ cComp (conjSub (g : G) (mcOf T)) := by
    intro K' hK'
    have h1 := cComp_map_mulEquiv (MulAut.conj (y : G)⁻¹) hK'
    have e1 : (mcOf T).map (MulAut.conj (y : G)⁻¹).toMonoidHom = conjSub (g : G) (mcOf T) := hconj3
    rw [e1] at h1
    exact h1
  rcases hcases with h | h
  · exact ⟨conjSub (y : G)⁻¹ Ko, hJ Ko hKo, hKopL.trans (conjSub_mono _ h)⟩
  · exact ⟨conjSub (y : G)⁻¹ Kop, hJ Kop hKop, hKopL.trans (conjSub_mono _ h)⟩

end Contain

end CFSG.Quasithin.ThreeD

namespace CFSG.Quasithin

section Final

theorem input14624ThreeDAsymTwo_proof : Input14624ThreeDAsymTwo := by
  intro G _ _ T M S hB K U₁ U₂ s u γ γ' g hfull Kp hC hnorm _ hlt
  classical
  obtain ⟨hctx, hall, hgeom⟩ := hfull
  obtain ⟨c19, c20, c23, hKc, c21, c22, hdec, -⟩ := hctx
  obtain ⟨hsetup, hDlt, hpos, hle, hltf, -⟩ := hgeom
  obtain ⟨hNorm₁, hNorm₂, -⟩ := hnorm
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨hF81, hF98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hG)
  obtain ⟨⟨U₁', U₂', s', hdecKp⟩, hc22Kp'⟩ := (hall Kp hC.mem).2
  have cK0 : ThreeC.CCtx T M K U₁ U₂ s := ThreeC.CCtx.ofDecomp S c19 hKc hC.l3.1 hdec
  have cKp0 : ThreeC.CCtx T M Kp U₁' U₂' s' := ThreeC.CCtx.ofDecomp S c19 hC.mem hC.l3.2 hdecKp
  have hc22K : ⁅⁅uOfL22 T M, K⁆, Kp⁆ = ⊥ := c22.2 Kp hC.mem hC.ne
  have hc22Kp : ⁅⁅uOfL22 T M, Kp⁆, K⁆ = ⊥ := hc22Kp' K hKc hC.ne.symm
  have hXH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hXab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hNK := fun hn => input14624NonFF_proof G T M S hB c19 K U₁ U₂ s hKc hC.l3.1 hdec _ hXH hNorm₁
    hXab hn
  have hNp := fun hn => input14624NonFF_proof G T M S hB c19 Kp U₁' U₂' s' hC.mem hC.l3.2 hdecKp _ hXH
    hNorm₂ hXab hn
  have hcompsK : ∀ L ∈ cComp (mcOf T), L = Kp ∨ L = K := fun L hL => (hC.comps L hL).symm
  have hkz' : perfectCore (mcOf T) = Kp ⊔ K := by rw [hC.kz, sup_comm]
  refine ⟨fun hA => ?_, fun hA => ?_⟩
  · obtain ⟨-, hd1, hr2, -, -⟩ := ThreeD.asym_facts S c23 cK0 hC.mem hC.ne hC.comps hsetup hNorm₁
      hNorm₂ hA hltf hlt hNK hNp
    exact ThreeD.contain_main S c19 c23 cK0 cKp0 hC.ne hC.comps hC.kz hc22K hc22Kp hC.rank.1 hsetup
      hDlt (hA.trans cK0.hsup.le) hd1 hr2
  · obtain ⟨-, hd1, hr2, -, -⟩ := ThreeD.asym_facts S c23 cKp0 hKc hC.ne.symm hcompsK hsetup hNorm₂
      hNorm₁ hA hltf hlt hNp hNK
    exact ThreeD.contain_main S c19 c23 cKp0 cK0 hC.ne.symm hcompsK hkz' hc22Kp hc22K hC.rank.2
      hsetup hDlt (hA.trans cKp0.hsup.le) hd1 hr2

end Final

end CFSG.Quasithin
