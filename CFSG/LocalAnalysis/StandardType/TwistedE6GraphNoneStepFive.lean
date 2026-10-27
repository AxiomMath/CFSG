module

public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepFive
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneFrobIndex
public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close CFSG.StandardType.E6GraphNoneSteps
  CFSG.StandardType CFSG.StandardType.TableB

abbrev L2 : Type := AlgebraicClosure (ZMod 2)

theorem isElemAbelian_range {G M : Type*} [Group G] [Group M] {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) (φ : E →* M) : CFSG.Open.IsElemAbelian p φ.range := by
  have h := (hE.comap E.subtype_injective).map φ
  rw [Subgroup.comap_subtype, Subgroup.subgroupOf_self] at h
  rwa [MonoidHom.range_eq_map]


section L

variable {L : Type} [Field L] [CharP L 2]

private lemma exists_involution_negating_roots (Fr : L →+* L)
    (m : ModGL TwistTag.E6.tag L) (s : V6 → V6) (hs : ∀ v, s v = -v)
    (hm : ∀ δ : V6, IsRoot TwistTag.E6.tag δ →
      m * pinnedX TwistTag.E6.tag L δ 1 * m⁻¹ = pinnedX TwistTag.E6.tag L (s δ) 1)
    {a : Fin TwistTag.E6.tag.rank → Lˣ} {α : V6} (hα : α ∈ movedPosT)
    (hka : rootChar a α = 1) :
    ∃ z₀ : ModGL TwistTag.E6.tag L, z₀ ∈ adjointGroup TwistTag.E6.tag L ∧
      Commute z₀ (rootDiagUnit TwistTag.E6.tag a) ∧
      m * Units.map (entrywiseHom Fr) z₀ * m⁻¹ = z₀ ∧
      diagramMap TwistTag.E6 L * z₀ * (diagramMap TwistTag.E6 L)⁻¹ ≠ z₀ ∧ z₀ * z₀ = 1 := by
  obtain ⟨hαr, hβr, hne, hne', hp, hmr⟩ := moved_facts hα
  set x : V6 → ModGL TwistTag.E6.tag L := fun δ => pinnedX TwistTag.E6.tag L δ 1 with hx
  have hFx : ∀ δ, Units.map (entrywiseHom Fr) (x δ) = x δ := fun δ => frob_pinnedX_one Fr δ
  have hnx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → m * x δ * m⁻¹ = x (s δ) := fun hδ => hm _ hδ
  have hPx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → diagramMap TwistTag.E6 L * x δ *
      (diagramMap TwistTag.E6 L)⁻¹ = x (permLattice TwistTag.E6.perm δ) :=
    fun hδ => diagram_conj_pinnedX hδ 1
  have hdx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → rootChar a δ = 1 →
      Commute (rootDiagUnit TwistTag.E6.tag a) (x δ) := fun hδ h => commute_rdu_pinnedX hδ h 1
  have hka' : rootChar a (-α) = 1 := by
    rw [E6SignedGraph.rootChar_neg', hka, inv_one]
  have hadj : ∀ δ, x δ ∈ adjointGroup TwistTag.E6.tag L := fun δ => pinnedX_mem_adjointGroup δ 1
  have cm : ∀ (u y y' : ModGL TwistTag.E6.tag L), u * (y * y') * u⁻¹ =
      (u * y * u⁻¹) * (u * y' * u⁻¹) := fun u y y' => by group
  refine ⟨x α * x (-α) * x α, mul_mem (mul_mem (hadj _) (hadj _)) (hadj _), ?_, ?_, ?_, ?_⟩
  · exact (((hdx hαr.1 hka).mul_right (hdx (IsRoot.neg hαr.1) hka')).mul_right
      (hdx hαr.1 hka)).symm
  · rw [map_mul, map_mul, hFx, hFx, cm, cm, hnx hαr.1, hnx (IsRoot.neg hαr.1), hs, hs, neg_neg]
    exact (nRoot_eq' (L := L) hαr.1).symm
  · rw [cm, cm, hPx hαr.1, hPx (IsRoot.neg hαr.1), rho_neg]
    intro h
    exact nRoot_ne (L := L) hαr hβr.1 hne hne' hp hmr h.symm
  · exact nRoot_mul_self (L := L) hαr.1

private lemma exists_involution_negating_rho_roots (Fr : L →+* L)
    (m : ModGL TwistTag.E6.tag L) (s : V6 → V6)
    (hs : ∀ v, s v = -permLattice TwistTag.E6.perm v)
    (hm : ∀ δ : V6, IsRoot TwistTag.E6.tag δ →
      m * pinnedX TwistTag.E6.tag L δ 1 * m⁻¹ = pinnedX TwistTag.E6.tag L (s δ) 1)
    {a : Fin TwistTag.E6.tag.rank → Lˣ} {α : V6} (hα : α ∈ movedPosT)
    (hka : rootChar a α = 1) (hkρ : rootChar a (permLattice TwistTag.E6.perm α) = 1) :
    ∃ z₀ : ModGL TwistTag.E6.tag L, z₀ ∈ adjointGroup TwistTag.E6.tag L ∧
      Commute z₀ (rootDiagUnit TwistTag.E6.tag a) ∧
      m * Units.map (entrywiseHom Fr) z₀ * m⁻¹ = z₀ ∧
      diagramMap TwistTag.E6 L * z₀ * (diagramMap TwistTag.E6 L)⁻¹ ≠ z₀ ∧ z₀ * z₀ = 1 := by
  obtain ⟨hαr, hβr, hne, hne', hp, hmr⟩ := moved_facts hα
  set β := permLattice TwistTag.E6.perm α with hβ
  set x : V6 → ModGL TwistTag.E6.tag L := fun δ => pinnedX TwistTag.E6.tag L δ 1 with hx
  have hFx : ∀ δ, Units.map (entrywiseHom Fr) (x δ) = x δ := fun δ => frob_pinnedX_one Fr δ
  have hnx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → m * x δ * m⁻¹ = x (s δ) := fun hδ => hm _ hδ
  have hPx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → diagramMap TwistTag.E6 L * x δ *
      (diagramMap TwistTag.E6 L)⁻¹ = x (permLattice TwistTag.E6.perm δ) :=
    fun hδ => diagram_conj_pinnedX hδ 1
  have hdx : ∀ {δ}, IsRoot TwistTag.E6.tag δ → rootChar a δ = 1 →
      Commute (rootDiagUnit TwistTag.E6.tag a) (x δ) := fun hδ h => commute_rdu_pinnedX hδ h 1
  have hkρ' : rootChar a (-β) = 1 := by
    rw [E6SignedGraph.rootChar_neg', hkρ, inv_one]
  have hadj : ∀ δ, x δ ∈ adjointGroup TwistTag.E6.tag L := fun δ => pinnedX_mem_adjointGroup δ 1
  have cm : ∀ (u y y' : ModGL TwistTag.E6.tag L), u * (y * y') * u⁻¹ =
      (u * y * u⁻¹) * (u * y' * u⁻¹) := fun u y y' => by group
  have hc : Commute (x α) (x (-β)) :=
    commute_pinnedX (L := L) hαr.1 (IsRoot.neg hβr.1) hne'
      (fun h => hne (h.trans (neg_neg _))) hmr 1 1
  refine ⟨x α * x (-β), mul_mem (hadj _) (hadj _), ?_, ?_, ?_, ?_⟩
  · exact ((hdx hαr.1 hka).mul_right (hdx (IsRoot.neg hβr.1) hkρ')).symm
  · rw [map_mul, hFx, hFx, cm, hnx hαr.1, hnx (IsRoot.neg hβr.1), hs, hs, rho_neg, neg_neg,
      ← hβ, rho_rho]
    exact hc.eq.symm
  · rw [cm, hPx hαr.1, hPx (IsRoot.neg hβr.1), rho_neg, ← hβ, rho_rho]
    intro h
    exact pinnedX_mul_ne (L := L) hαr hβr hne h.symm
  · rw [hc.symm.mul_mul_mul_comm, show x α * x α = 1 from pinnedX_one_mul_self _,
      show x (-β) * x (-β) = 1 from pinnedX_one_mul_self _, one_mul]

private theorem exists_z0g (Fr : L →+* L) (m : ModGL TwistTag.E6.tag L) (s : V6 → V6)
    (hs : (∀ v, s v = -v) ∨ (∀ v, s v = -permLattice TwistTag.E6.perm v))
    (hm : ∀ δ : V6, IsRoot TwistTag.E6.tag δ →
      m * pinnedX TwistTag.E6.tag L δ 1 * m⁻¹ = pinnedX TwistTag.E6.tag L (s δ) 1)
    {a : Fin TwistTag.E6.tag.rank → Lˣ} {α : V6} (hα : α ∈ movedPosT)
    (hka : rootChar a α = 1) (hkρ : rootChar a (permLattice TwistTag.E6.perm α) = 1) :
    ∃ z₀ : ModGL TwistTag.E6.tag L, z₀ ∈ adjointGroup TwistTag.E6.tag L ∧
      Commute z₀ (rootDiagUnit TwistTag.E6.tag a) ∧
      m * Units.map (entrywiseHom Fr) z₀ * m⁻¹ = z₀ ∧
      diagramMap TwistTag.E6 L * z₀ * (diagramMap TwistTag.E6 L)⁻¹ ≠ z₀ ∧ z₀ * z₀ = 1 := by
  rcases hs with hw | hw
  · exact exists_involution_negating_roots Fr m s hw hm hα hka
  · exact exists_involution_negating_rho_roots Fr m s hw hm hα hka hkρ

end L

private lemma rootDiagUnit_cube_mem_graphFixedRootGroup {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {b : Fin 6 → Kˣ}
    (hb : b ∈ TwE6.compat σ.toRingHom) :
    rootDiagUnit TwistTag.E6.tag b ^ 3 ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  have hq : 2 ≤ 2 ^ n := le_self_pow₀ (by norm_num) (by omega)
  obtain ⟨x, hx⟩ := TwE6.exists_mul_edge_inv_mem hq hK (σ := σ.toRingHom) hσ hb
  have hb3 : b ^ 3 ∈ TwE6.torus₀ σ.toRingHom := by
    have e : b ^ 3 = (b * (TwE6.edge σ.toRingHom x)⁻¹) ^ 3 *
        TwE6.edge σ.toRingHom (x ^ 3) := by
      rw [map_pow, mul_pow, inv_pow, inv_mul_cancel_right]
    rw [e]
    exact mul_mem (pow_mem hx 3) (TwE6.edge_pow_three_mem (TwE6.sigma_sigma hK hσ) x)
  obtain ⟨s, hs, hseq⟩ := hb3
  have h := TwE6.rootDiagUnit_cartanChar_mem (t := TwistTag.E6) (K := K)
    (σ := σ.toRingHom) hs
  have e : rootDiagUnit TwistTag.E6.tag b ^ 3 = rootDiagUnit TwistTag.E6.tag (b ^ 3) :=
    (map_pow (rootDiagUnitHom TwistTag.E6.tag K) b 3).symm
  rw [e]
  convert h using 2
  exact hseq.symm

private lemma mem_of_pow_three_mul_mem_normal_subgroup {L : Type} [Field L]
    {C R : Subgroup (ModGL TwistTag.E6.tag L)} (hCR : C ≤ R)
    (hnorm : (C.subgroupOf R).Normal) {z t u : ModGL TwistTag.E6.tag L}
    (hzR : z ∈ R) (hzz : z * z = 1) (htC : t ^ 3 ∈ C) (huC : u ∈ C)
    (htu : t * u = z) : z ∈ C := by
  have := hnorm
  set π := QuotientGroup.mk' (C.subgroupOf R)
  have hker : ∀ w : R, π w = 1 ↔ (w : ModGL TwistTag.E6.tag L) ∈ C := fun w => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have htR : t ∈ R := by
    have : t = z * u⁻¹ := by rw [← htu, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hzR (inv_mem (hCR huC))
  have hzt : (⟨z, hzR⟩ : R) = ⟨t, htR⟩ * ⟨u, hCR huC⟩ := Subtype.ext htu.symm
  have hπz : π ⟨z, hzR⟩ = π ⟨t, htR⟩ := by
    rw [hzt, map_mul, (hker ⟨u, hCR huC⟩).2 huC, mul_one]
  have h3 : π ⟨t, htR⟩ ^ 3 = 1 := by
    rw [← map_pow, hker]
    simpa using htC
  have h2 : π ⟨z, hzR⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨z, hzR⟩ : R) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two, hzz]; rfl)
    rw [this, map_one]
  have h1 : π ⟨z, hzR⟩ = 1 := by
    have h3' : π ⟨z, hzR⟩ ^ 3 = 1 := by rw [hπz]; exact h3
    calc π ⟨z, hzR⟩ = π ⟨z, hzR⟩ ^ 3 * (π ⟨z, hzR⟩ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2, inv_one, mul_one]
  exact (hker _).1 h1

private theorem twE6_mem_of_mul_self {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) {L : Type}
    [Field L] [Algebra K L] [IsAlgClosure K L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {z : ModGL TwistTag.E6.tag L} (hz : z ∈ twistedFixedGroup TwistTag.E6 L Fr)
    (hzz : z * z = 1) :
    z ∈ (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K L)) := by
  obtain ⟨hR, hCR, hnorm, -⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6
    Nat.prime_two hn K hK σ.toRingHom hσ L Fr hFr
  have h1 : z ∈ (twistedFixedGroup TwistTag.E6 L Fr : Set (ModGL TwistTag.E6.tag L)) := hz
  rw [hR] at h1
  obtain ⟨t, ht, y, ⟨c, hc, rfl⟩, htc⟩ := h1
  obtain ⟨b, hb, rfl⟩ := RecipeExcLang.exists_compat_of_mem_graphFixedTorus hK σ hσ Fr hFr ht
  have hd3 := rootDiagUnit_cube_mem_graphFixedRootGroup hn hK hσ hb
  refine mem_of_pow_three_mul_mem_normal_subgroup (C := (graphFixedRootGroup TwistTag.E6 K
      σ.toRingHom).map (baseChangeGL (algebraMap K L)))
    (R := twistedFixedGroup TwistTag.E6 L Fr) hCR hnorm hz hzz ?_ ?_ htc
  · rw [← map_pow]
    exact ⟨_, hd3, rfl⟩
  · exact ⟨c, hc, rfl⟩

section L

variable {L : Type} [Field L]

private lemma permLattice_of_weylAct_inversions [IsAlgClosed L] [CharP L 2]
    {ω : List (Fin TwistTag.E6.tag.rank)}
    (hw : ∀ b : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (wt ω)
        (fun i => b (e6IndexToF4 i)) = (fun i => b (e6IndexToF4 i))⁻¹) :
    (∀ v : V6, permLattice TwistTag.E6.perm (wt ω • v) = -v) ∨
      (∀ v : V6, permLattice TwistTag.E6.perm (wt ω • v) = -permLattice TwistTag.E6.perm v) := by
  rcases wt_cases (wt ω) hw with h | h
  · exact Or.inr fun v => by rw [h, rho_neg]
  · exact Or.inl fun v => by rw [h, rho_neg, rho_rho]

private lemma diagramMap_mul_weylWord_conj_pinnedX [CharP L 2]
    (ω : List (Fin TwistTag.E6.tag.rank)) :
    ∀ δ : V6, IsRoot TwistTag.E6.tag δ →
      (diagramMap TwistTag.E6 L * weylWord (τ := TwistTag.E6.tag) L ω) *
        pinnedX TwistTag.E6.tag L δ 1 *
        (diagramMap TwistTag.E6 L * weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ =
      pinnedX TwistTag.E6.tag L (permLattice TwistTag.E6.perm (wt ω • δ)) 1 := by
  intro δ hδ
  calc (diagramMap TwistTag.E6 L * weylWord (τ := TwistTag.E6.tag) L ω) *
        pinnedX TwistTag.E6.tag L δ 1 *
        (diagramMap TwistTag.E6 L * weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ =
      diagramMap TwistTag.E6 L * (weylWord (τ := TwistTag.E6.tag) L ω *
        pinnedX TwistTag.E6.tag L δ 1 * (weylWord (τ := TwistTag.E6.tag) L ω)⁻¹) *
        (diagramMap TwistTag.E6 L)⁻¹ := by group
    _ = diagramMap TwistTag.E6 L * pinnedX TwistTag.E6.tag L (wt ω • δ) 1 *
        (diagramMap TwistTag.E6 L)⁻¹ := by rw [weylWord_conj_pinnedX' ω hδ 1]
    _ = _ := diagram_conj_pinnedX (CFSG.LieType.Chevalley.IsRoot.smul hδ _) 1

private lemma conj_mem_twistedFixedGroup {Fr : L →+* L} {g z₀ : ModGL TwistTag.E6.tag L}
    {ω : List (Fin TwistTag.E6.tag.rank)}
    (hg : g ∈ adjointGroup TwistTag.E6.tag L) (hz₀C : z₀ ∈ adjointGroup TwistTag.E6.tag L)
    (hP : diagramMap TwistTag.E6 L * g = g * diagramMap TwistTag.E6 L)
    (hlang : Units.map (entrywiseHom Fr) g = g * weylWord (τ := TwistTag.E6.tag) L ω)
    (hz₀F : (diagramMap TwistTag.E6 L * weylWord (τ := TwistTag.E6.tag) L ω) *
        Units.map (entrywiseHom Fr) z₀ *
        (diagramMap TwistTag.E6 L * weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ = z₀) :
    g * z₀ * g⁻¹ ∈ twistedFixedGroup TwistTag.E6 L Fr := by
  have hzC : g * z₀ * g⁻¹ ∈ adjointGroup TwistTag.E6.tag L :=
    mul_mem (mul_mem hg hz₀C) (inv_mem hg)
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).2 ⟨hzC, ?_⟩
  rw [twistHom_apply, map_mul, map_mul, map_inv, hlang]
  conv_rhs => rw [← hz₀F]
  calc diagramMap TwistTag.E6 L *
        (g * weylWord (τ := TwistTag.E6.tag) L ω *
          Units.map (entrywiseHom Fr) z₀ *
          (g * weylWord (τ := TwistTag.E6.tag) L ω)⁻¹) *
        (diagramMap TwistTag.E6 L)⁻¹ =
      (diagramMap TwistTag.E6 L * g) * weylWord (τ := TwistTag.E6.tag) L ω *
        Units.map (entrywiseHom Fr) z₀ * (weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ *
        (diagramMap TwistTag.E6 L * g)⁻¹ := by group
    _ = (g * diagramMap TwistTag.E6 L) * weylWord (τ := TwistTag.E6.tag) L ω *
        Units.map (entrywiseHom Fr) z₀ * (weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ *
        (g * diagramMap TwistTag.E6 L)⁻¹ := by rw [hP]
    _ = _ := by group

private lemma commute_conj_rootDiagUnit {g z₀ : ModGL TwistTag.E6.tag L}
    {c : Fin Tag.F4.rank → Lˣ}
    (hz₀d : Commute z₀ (rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)))) :
    Commute (g * z₀ * g⁻¹)
      (g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹) := by
  change g * z₀ * g⁻¹ *
      (g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹) =
    g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹ *
      (g * z₀ * g⁻¹)
  calc g * z₀ * g⁻¹ *
        (g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹) =
      g * (z₀ * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i))) * g⁻¹ := by group
    _ = g * (rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * z₀) * g⁻¹ := by
        rw [hz₀d.eq]
    _ = _ := by group

private lemma diagramMap_conj_ne {g z₀ : ModGL TwistTag.E6.tag L}
    (hP : diagramMap TwistTag.E6 L * g = g * diagramMap TwistTag.E6 L)
    (hz₀P : diagramMap TwistTag.E6 L * z₀ * (diagramMap TwistTag.E6 L)⁻¹ ≠ z₀) :
    diagramMap TwistTag.E6 L * (g * z₀ * g⁻¹) * (diagramMap TwistTag.E6 L)⁻¹ ≠
      g * z₀ * g⁻¹ := by
  intro h
  have e : diagramMap TwistTag.E6 L * (g * z₀ * g⁻¹) * (diagramMap TwistTag.E6 L)⁻¹ =
      g * (diagramMap TwistTag.E6 L * z₀ * (diagramMap TwistTag.E6 L)⁻¹) * g⁻¹ := by
    calc diagramMap TwistTag.E6 L * (g * z₀ * g⁻¹) * (diagramMap TwistTag.E6 L)⁻¹ =
          (diagramMap TwistTag.E6 L * g) * z₀ * (diagramMap TwistTag.E6 L * g)⁻¹ := by group
      _ = (g * diagramMap TwistTag.E6 L) * z₀ * (g * diagramMap TwistTag.E6 L)⁻¹ := by rw [hP]
      _ = _ := by group
  rw [e] at h
  exact hz₀P (mul_left_cancel (mul_right_cancel h))

end L

theorem twE6_step5 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) {L : Type}
    [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {g : ModGL TwistTag.E6.tag L} (hg : g ∈ adjointGroup TwistTag.E6.tag L)
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hlang : Units.map (entrywiseHom Fr) g = g * weylWord (τ := TwistTag.E6.tag) L ω)
    (hw : ∀ b : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (wt ω)
        (fun i => b (e6IndexToF4 i)) = (fun i => b (e6IndexToF4 i))⁻¹)
    {c : Fin Tag.F4.rank → Lˣ} (hc : ∀ k, c k ^ 3 = 1) :
    ∃ z ∈ (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K L)),
      Commute z (g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹) ∧
      diagramMap TwistTag.E6 L * z * (diagramMap TwistTag.E6 L)⁻¹ ≠ z := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨ζ, hζ⟩ := exists_orderOf_three L
  choose y hy using fun k => exists_zmod_of_pow_three hζ (hc k)
  obtain ⟨α, hα, hk1, hk2⟩ := killT y
  have hs := permLattice_of_weylAct_inversions (L := L) (ω := ω) hw
  have hm := diagramMap_mul_weylWord_conj_pinnedX (L := L) (ω := ω)
  obtain ⟨z₀, hz₀C, hz₀d, hz₀F, hz₀P, hz₀2⟩ :=
    exists_z0g Fr (diagramMap TwistTag.E6 L * weylWord (τ := TwistTag.E6.tag) L ω)
      (fun v => permLattice TwistTag.E6.perm (wt ω • v)) hs hm hα
      (rootChar_cube hζ hy hk1) (rootChar_cube hζ hy hk2)
  have hP := diagramMap_mul_of_mem_twistedFixedGroup hgP
  have hzR := conj_mem_twistedFixedGroup (g := g) (z₀ := z₀) (ω := ω)
    hg hz₀C hP hlang hz₀F
  have hz2 : g * z₀ * g⁻¹ * (g * z₀ * g⁻¹) = 1 := by
    calc g * z₀ * g⁻¹ * (g * z₀ * g⁻¹) = g * (z₀ * z₀) * g⁻¹ := by group
      _ = 1 := by rw [hz₀2]; group
  exact ⟨g * z₀ * g⁻¹, twE6_mem_of_mul_self hn hK hσ hFr hzR hz2,
    commute_conj_rootDiagUnit hz₀d, diagramMap_conj_ne hP hz₀P⟩

end CFSG.StandardType.E6GraphNoneSteps
