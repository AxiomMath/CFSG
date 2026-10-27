module

public import CFSG.Quasithin.EmptyFaithful.S151YB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem ya7_stab_mul {σ τ : Equiv.Perm (Fin 7)} {P : Finset (Finset (Fin 7))}
    (hσ : StabilizesPartition σ P) (hτ : StabilizesPartition τ P) :
    StabilizesPartition (σ * τ) P := by
  unfold StabilizesPartition at *
  have h : P.image (Finset.image ⇑(σ * τ)) = (P.image (Finset.image ⇑τ)).image (Finset.image ⇑σ) := by
    rw [Finset.image_image]
    congr 1
    funext B
    simp [Finset.image_image]
  rw [h, hτ, hσ]

theorem ya7_stab_inv {σ : Equiv.Perm (Fin 7)} {P : Finset (Finset (Fin 7))}
    (hσ : StabilizesPartition σ P) : StabilizesPartition σ⁻¹ P := by
  unfold StabilizesPartition at *
  have h : (P.image (Finset.image ⇑σ)).image (Finset.image ⇑σ⁻¹) = P := by
    rw [Finset.image_image]
    have : Finset.image ⇑σ⁻¹ ∘ Finset.image ⇑σ = id := by
      funext B
      simp [Finset.image_image]
    rw [this, Finset.image_id]
  calc P.image (Finset.image ⇑σ⁻¹) = (P.image (Finset.image ⇑σ)).image (Finset.image ⇑σ⁻¹) := by
        rw [hσ]
    _ = P := h

@[expose] def ya7PartStab (P : Finset (Finset (Fin 7))) : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {σ | StabilizesPartition (σ : Equiv.Perm (Fin 7)) P}
  mul_mem' := fun {a b} ha hb => ya7_stab_mul ha hb
  one_mem' := by
    show StabilizesPartition ((1 : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) P
    unfold StabilizesPartition
    have h1 : Finset.image ⇑((1 : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        (id : Finset (Fin 7) → Finset (Fin 7)) := by
      funext B
      simp
    rw [h1, Finset.image_id]
  inv_mem' := fun {a} ha => ya7_stab_inv ha

@[expose] def ya7Pre {G : Type} [Group G] (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (P : Finset (Finset (Fin 7))) : Subgroup G :=
  ((ya7PartStab P).comap α).map L.subtype

theorem mem_ya7Pre {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
    {P : Finset (Finset (Fin 7))} {x : G} :
    x ∈ ya7Pre L α P ↔ ∃ hx : x ∈ L, StabilizesPartition (α ⟨x, hx⟩ : Equiv.Perm (Fin 7)) P := by
  unfold ya7Pre
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem ya7Pre_le {G : Type} [Group G] (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (P : Finset (Finset (Fin 7))) : ya7Pre L α P ≤ L := by
  intro x hx
  exact (mem_ya7Pre.mp hx).1

theorem ya7_isSylowTwoOf_restrict {G : Type} [Group G] {S P H : Subgroup G} (hS : IsSylowTwoOf S H)
    (hSP : S ≤ P) (hPH : P ≤ H) : IsSylowTwoOf S P := by
  refine ⟨hSP, hS.2.1, fun hd => hS.2.2 ?_⟩
  have h := Subgroup.relIndex_mul_relIndex S P H hSP hPH
  have h2 : S.relIndex P ∣ S.relIndex H := h ▸ dvd_mul_right _ _
  exact dvd_trans hd h2

theorem ya7_centralizer_le_mc {G : Type} [Group G] [Finite G] {T Mc : Subgroup G}
    (hq : quasithinQTFE14Cat G T Mc) {z : G} (hzZ : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Mc := by
  have hzT : z ∈ T := (Subgroup.closure_le T).mpr (fun y hy => hy.1.1) hzZ
  have hP : IsPGroup 2 (Subgroup.zpowers z) := hq.sylow.1.to_le (Subgroup.zpowers_le.mpr hzT)
  have hne : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    exact hz1 (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_zpowers z))
  have hloc : IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :=
    ⟨Subgroup.zpowers z, hne, hP, rfl⟩
  obtain ⟨K, hK, hle⟩ := exists_maxTwoLocal_ge hloc
  have hCz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro c hc
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hcz : z * c = c * z := Subgroup.mem_centralizer_iff.1 hc z rfl
    exact ((Commute.zpow_left (show Commute z c from hcz) k).eq)
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzZ)
  have hKMc : K = Mc := hq.mc_unique K hK (hCZ.trans (hCz.trans hle))
  exact hCz.trans (hKMc ▸ hle)

@[expose] def C126Third {G : Type} [Group G] (H T : Subgroup G) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Subgroup G), 1 ≤ r ∧
    (∀ i, IsChi0Block H (K i) ∧ ⁅K i, thompsonJ T⁆ = K i) ∧
    (∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) ∧ twoResidual H = ⨆ i, K i ∧
    (∀ t ∈ T, ∀ i, ∃ j, B6.conjSub t (K i) = K j) ∧
    (∀ i j, ∃ t ∈ T, B6.conjSub t (K i) = K j)

@[expose] def Input15122A7Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G)
    (α : ↥L →* alternatingGroup (Fin 7)) (P : Finset (Finset (Fin 7))),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsAltBlockTypeWith L 7 α → IsPartitionOfType P {2, 2, 2, 1} →
    (∀ x : ↥L, (x : G) ∈ s1516 T Z₁ → StabilizesPartition (α x : Equiv.Perm (Fin 7)) P) →
    CharTwo (ya7Pre L α P ⊔ s1516 T Z₁) ∧
      IsMinParabolicOf (ya7Pre L α P ⊔ s1516 T Z₁) (ya7Pre L α P ⊔ s1516 T Z₁) ∧
      ¬ C126Third (ya7Pre L α P ⊔ s1516 T Z₁) (s1516 T Z₁)

theorem ya7_bang_of_local (h118 : TheoremC118) (h126 : TheoremC126) (hloc : Input15122A7Local) :
    Input15122A7Bang := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L α v P hc hα hv2 hvS hvM hPpart hsP hstabS hmove x hx
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  obtain ⟨hchar, hmin, hno3⟩ := hloc G T Mc M Z₁ Z₂ V₁ V₂ L α P hc hα hPpart hstabS
  set S := s1516 T Z₁ with hSdef
  set Pt := ya7Pre L α P with hPt
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hHG : Pt ⊔ S ≤ g1_1516 Z₁ := sup_le ((ya7Pre_le L α P).trans hLG) (s1516_le_g1 T Z₁)
  have hSH : IsSylowTwoOf S (Pt ⊔ S) :=
    ya7_isSylowTwoOf_restrict hc.h18.four le_sup_right hHG
  have hpc : pCoreOf 2 (Pt ⊔ S) ≠ ⊥ := by
    have h1 : pCoreOf 2 (g1_1516 Z₁) ≤ S := hc.h18.four.pCoreOf_le
    have h2 : pCoreOf 2 (g1_1516 Z₁) ≤ pCoreOf 2 (Pt ⊔ S) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
        (hHG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (g1_1516 Z₁)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (g1_1516 Z₁))
    exact ne_bot_of_le_ne_bot (hSet.pCore_g1_ne_bot hq hMf) h2
  have hSQ : IsSQTKTC (Pt ⊔ S) :=
    ⟨kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpc,
      stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hpc⟩
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) h118
  have hT2 : IsPGroup 2 T := hq.sylow.1
  have hS2 : IsPGroup 2 S := hSH.2.1
  have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
  have hT0 : T ≠ ⊥ := ne_bot_of_le_ne_bot hSet.z1_ne hZ₁T
  have hST : S ≤ T := s1516_le T Z₁
  obtain ⟨h1ne, h1Z, -⟩ := hC.pair T hT2 hT0
  have hC1T : C₁ T ≤ centerOf T := h1Z.trans (C1GN.omegaOneCenterOf_le_centerOf T)
  have hcTS : centerOf T ≤ S := fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hz.2 y (hZ₁T hy)⟩
  have hS0 : S ≠ ⊥ := ne_bot_of_le_ne_bot h1ne (hC1T.trans hcTS)
  have hcTcS : centerOf T ≤ centerOf S := fun z hz =>
    ⟨hcTS hz, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hST) hz.2⟩
  have hc1S : C₁ T ≤ C₁ S := by
    rw [hC.c1_eq T hT2 hT0, hC.c1_eq S hS2 hS0, hc.h17.baumS]
    exact inf_le_inf hcTcS le_rfl
  rcases h126 G C₁ C₂ hC (Pt ⊔ S) S hSQ hSH hchar hmin with h1 | h2 | h3
  ·
    exfalso
    obtain ⟨x₀, hx₀P, hx₀v⟩ := hmove
    have hx₀Pt : (x₀ : G) ∈ Pt := mem_ya7Pre.mpr ⟨x₀.2, hx₀P⟩
    have hHc : ∀ y ∈ C₁ S, ∀ h ∈ Pt ⊔ S, y * h = h * y := fun y hy h hh =>
      (Subgroup.mem_centralizer_iff.mp (h1 hy).2 h hh).symm
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1ne
    have hzZ : (z : G) ∈ quasithinOmegaOneCenter T := h1Z z.2
    have hzC : (z : G) ∈ C₁ S := hc1S z.2
    have hx₀C : (x₀ : G) ∈ Subgroup.centralizer ({(z : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hHc (z : G) hzC x₀ (Subgroup.mem_sup_left hx₀Pt)
    have hx₀Mc : (x₀ : G) ∈ Mc :=
      ya7_centralizer_le_mc hq hzZ (fun h => hz1 (Subtype.ext h)) hx₀C
    have hx₀Mz : (x₀ : G) ∈ mZ1516 Mc Z₁ := ⟨hLG x₀.2, hx₀Mc⟩
    exact hx₀v ((hvM x₀).mp hx₀Mz)
  ·
    obtain ⟨-, -, -, h2ne, h2B, h2char, -⟩ := hC.pair S hS2 hS0
    have hNle : Subgroup.normalizer (C₂ S : Set G) ≤ M := by
      refine le_trans ?_ hc.h17.cgs
      exact le_iSup_of_le (C₂ S) (le_iSup_of_le h2B (le_iSup_of_le h2ne
        (le_iSup_of_le h2char le_rfl)))
    have hxPt : (x : G) ∈ Pt := mem_ya7Pre.mpr ⟨x.2, hx⟩
    exact hNle (h2 (Subgroup.mem_sup_left hxPt))
  · exact (hno3 h3).elim

theorem input15122A7_of_local (h118 : TheoremC118) (h126 : TheoremC126) (hloc : Input15122A7Local) :
    Input15122A7 :=
  input15122A7_of_bang (ya7_bang_of_local h118 h126 hloc)

end CFSG.Quasithin
