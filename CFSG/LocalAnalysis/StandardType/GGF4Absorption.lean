module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHCRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylInfDefs
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGF4AbsorbConj
import CFSG.LocalAnalysis.StandardType.GGF4EndpointType
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGF4ReflGroup
import CFSG.LocalAnalysis.StandardType.GGF4ReflLin
import CFSG.LocalAnalysis.StandardType.GGF4ReflOrbit
import CFSG.LocalAnalysis.StandardType.GGF4TypeCards
import CFSG.LocalAnalysis.StandardType.GGSecFiveBEqualJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
import CFSG.GroupTheory.PLayer.Transfer
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.PLayer.PIndex

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.F4Model

private theorem ggF4_join_nonempty {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hF1 : ∀ y K, GGNbr p B x D J y K → ∀ b : ↥Bs,
      (∀ a ∈ ggAutomizer K Bs, a b = b) → (b : G) ∈ Subgroup.centralizer (K : Set G))
    (hRM : ∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    𝒦.Nonempty := by
  classical
  let hc : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨hp, hBs, hxBs, hLx, h4⟩ := hc.tableB_facts
  obtain ⟨y, K, hN⟩ := exists_ggNbr hc.1.2.2.2.2.2.2.2 hc.2.2
  by_contra hne
  have hKempty : 𝒦 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hA : ggAutomizerJoin L Bs 𝒦 = ggAutomizer L Bs := by
    rw [ggAutomizerJoin, hKempty]
    simp
  have hKle : ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    rw [← hA]
    exact hRM y K hN
  have hxfixK : ∀ a ∈ ggAutomizer K Bs, a ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := fun a ha =>
    ggRC_automizer_fixes_y (K := L) hxBs hLx a (hKle ha)
  have hxC : (x : G) ∈ Subgroup.centralizer (K : Set G) := hF1 y K hN ⟨x, hxBs⟩ hxfixK
  have hxB : x ∈ B := hc.1.2.2.2.2.2.2.1.2.1
  have hxinf : (x : G) ∈ B ⊓ Subgroup.centralizer (K : Set G) := ⟨hxB, hxC⟩
  rw [inf_centralizer_eq_zpowers_of_sHat hN.1] at hxinf
  have hyx : y ∉ Subgroup.zpowers x := GGConfig.not_mem_zpowers_of_ggNbr hc hN
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hx1 : x ≠ 1 := hc.1.2.2.2.2.2.2.1.2.2.1
  have hxpow : x ^ p = 1 := hBs.2 x hxBs
  have hypow : y ^ p = 1 := hBs.2 y (hc.2.1.1 hN.1.2.1)
  have hxord : orderOf x = p := orderOf_eq_prime (hp := ⟨hp⟩) hxpow hx1
  have hyord : orderOf y = p := orderOf_eq_prime (hp := ⟨hp⟩) hypow hy1
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hxinf
  have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle (by simp [Nat.card_zpowers, hxord, hyord])
  exact hyx (heq.symm ▸ Subgroup.mem_zpowers y)

theorem ggF4_join_fix_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hF1 : ∀ y K, GGNbr p B x D J y K → ∀ b : ↥Bs,
      (∀ a ∈ ggAutomizer K Bs, a b = b) → (b : G) ∈ Subgroup.centralizer (K : Set G))
    (hne : 𝒦.Nonempty) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizerJoin L Bs 𝒦, a b = b) → b = 1 := by
  classical
  intro b hb
  have hbL : ∀ a ∈ ggAutomizer L Bs, a b = b := fun a ha => hb a (Subgroup.mem_sup_left ha)
  have hbz : (b : G) ∈ Subgroup.zpowers x := hFixL b hbL
  obtain ⟨K, hK⟩ := hne
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
  have hxB : x ∈ B := hR.1.1.1.2.2.2.2.2.2.1.2.1
  have hbB : (b : G) ∈ B := (Subgroup.zpowers_le.mpr hxB) hbz
  have hbK : ∀ a ∈ ggAutomizer K Bs, a b = b := fun a ha =>
    hb a (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem K (Subgroup.mem_iSup_of_mem hK ha)))
  have hbC : (b : G) ∈ Subgroup.centralizer (K : Set G) := hF1 y K hN b hbK
  have hbY : (b : G) ∈ Subgroup.zpowers y := by
    have hmem : (b : G) ∈ B ⊓ Subgroup.centralizer (K : Set G) := ⟨hbB, hbC⟩
    rwa [inf_centralizer_eq_zpowers_of_sHat hN.1] at hmem
  have hc : GGConfig p B Bs x L D J := hR.1.1
  have hyx : y ∉ Subgroup.zpowers x := GGConfig.not_mem_zpowers_of_ggNbr hc hN
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  obtain ⟨hp, hBs, hxBs, hLx, h4⟩ := hc.tableB_facts
  have hypow : y ^ p = 1 := hBs.2 y (hc.2.1.1 hN.1.2.1)
  have hdisj : Subgroup.zpowers y ⊓ Subgroup.zpowers x = ⊥ :=
    CFSG.zpowers_inf_eq_bot_of_not_mem hp hypow hy1 hyx
  have hmem : (b : G) ∈ Subgroup.zpowers y ⊓ Subgroup.zpowers x := ⟨hbY, hbz⟩
  rw [hdisj] at hmem
  have hb1 : (b : G) = 1 := Subgroup.mem_bot.mp hmem
  exact Subtype.ext hb1

theorem ggF4_join_B_eq_bstar {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    (hfixA : ∀ b : ↥Bs, (∀ a ∈ ggAutomizerJoin L Bs 𝒦, a b = b) → b = 1) : B = Bs := by
  obtain ⟨⟨-, -, -, -, -, hβ, hS, -⟩, hBs, -⟩ := hR.1.1
  have hp : p.Prime := hR.1.1.tableB_facts.1
  have hB : Nat.card B = p ^ CFSG.Open.twoLocalPrimeRank p G := hS.1.2.1
  have h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank p G := hβ.2.2.2
  obtain ⟨e', rfl⟩ := hF4
  have : Fintype ι := Fintype.ofEquiv (Fin 4) e'
  have hcardι : Fintype.card ι = 4 := by rw [← Fintype.card_congr e', Fintype.card_fin]
  have hW : GGWeylOfType p (CoxeterMatrix.F₄.reindex e') (ggAutomizerJoin L Bs 𝒦) := ⟨e, hP.2⟩
  have hcard4 : Nat.card ↥Bs ≤ p ^ 4 := by
    have h := SpJoinRefl.card_le_pow_of_weylOfType hW hfixA
    rwa [hcardι] at h
  refine Subgroup.eq_of_le_of_card_ge hBs.1 ?_
  rw [hB]
  exact hcard4.trans (Nat.pow_le_pow_right hp.pos h4)

private theorem ggF4_join_fixLine_L {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) → (b : G) ∈ Subgroup.zpowers x) :
    GGFixLineComp Bs x L :=
  hR.1.1.fixLineComp_L_of_fix hFixL

private theorem ggF4_join_fixLine_nbr {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs)
    (hF1 : ∀ y K, GGNbr p B x D J y K → ∀ b : ↥Bs, (∀ a ∈ ggAutomizer K Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G))
    {y : G} {K : Subgroup G} (hn : GGNbr p B x D J y K) : GGFixLineComp Bs y K :=
  hR.1.1.fixLineComp_nbr_of_fix hB hn (hF1 y K hn)

private theorem ggF4_join_endpoint
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    (hfixA : ∀ b : ↥Bs, (∀ a ∈ ggAutomizerJoin L Bs 𝒦, a b = b) → b = 1)
    {u : G} {X : Subgroup G} (hX : GGFixLineComp Bs u X) (hu1 : u ≠ 1)
    (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hWX : GGWeylReflectionGroup p (ggAutomizer X Bs)) :
    ∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧ t ⟨u, hX.mem⟩ = ⟨u, hX.mem⟩⁻¹ ∧
      (∀ φ ∈ ggAutomizer X Bs, φ * t = t * φ) ∧
      (Nat.card ↥(ggAutomizer X Bs) = 24 ∨ Nat.card ↥(ggAutomizer X Bs) = 48) := by
  obtain ⟨hp, hBs, -, -, h4⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
    exact hp2
  have hNT : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hAind := ggAutomizerJoin_le_ggInduced_top (Bs := Bs) L 𝒦
  exact ggF4_exists_endpointRefl hp2 hBs h4 hNT hAind hP hF4 hfixA hXA hWX hX.mem hu1 hX.fix_iff

private theorem ggF4_frame {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {tL t₁ t₂ : MulAut ↥Bs} (h₁N : t₁ ∈ ggInduced ⊤ Bs) (h₂N : t₂ ∈ ggInduced ⊤ Bs)
    (hL : GGIsReflection p tL) (h₁ : GGIsReflection p t₁) (h₂ : GGIsReflection p t₂)
    {x y₁ y₂ : ↥Bs} (hx : x ≠ 1) (hLx : tL x = x⁻¹) (h₁y : t₁ y₁ = y₁⁻¹) (h₂y : t₂ y₂ = y₂⁻¹)
    (hy₁ : (y₁ : G) ∉ Subgroup.zpowers (x : G)) (hy₂ : (y₂ : G) ∉ Subgroup.zpowers (x : G))
    (hy₂₁ : (y₂ : G) ∈ Subgroup.closure ({(x : G), (y₁ : G)} : Set G))
    (hc₁ : Commute tL t₁) (hc₂ : Commute tL t₂) : t₁ = t₂ := by
  have key : ∀ {y : ↥Bs} (t : MulAut ↥Bs), t y = y⁻¹ →
      (y : G) ∉ Subgroup.zpowers (x : G) → t ≠ tL := by
    intro y t hty hyx h
    have hinv : tL y = y⁻¹ := by
      rw [← h]
      exact hty
    have hmem : y ∈ Subgroup.zpowers x :=
      GGIsReflection.mem_zpowers_of_apply_eq_inv hp2 hBs hL hx hLx hinv
    have hmap : (y : G) ∈ (Subgroup.zpowers x).map (Subgroup.subtype Bs) :=
      ⟨y, hmem, rfl⟩
    rw [MonoidHom.map_zpowers] at hmap
    exact hyx hmap
  have h₁ne : t₁ ≠ tL := key t₁ h₁y hy₁
  have h₂ne : t₂ ≠ tL := key t₂ h₂y hy₂
  have hfix₁ : tL y₁ = y₁ :=
    GGIsReflection.apply_eq_of_commute hp2 hBs hL h₁ hc₁ (Ne.symm h₁ne) h₁y
  have hfix₂ : tL y₂ = y₂ :=
    GGIsReflection.apply_eq_of_commute hp2 hBs hL h₂ hc₂ (Ne.symm h₂ne) h₂y
  have hy₂pow : (y₂ : G) ∈ Subgroup.zpowers (y₁ : G) :=
    mem_zpowers_of_apply_eq_of_mem_closure hp2 hBs hLx hfix₁ hfix₂ hy₂₁
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy₂pow
  have hk' : y₁ ^ k = y₂ := Subtype.ext (by simpa using hk)
  have h₁y₂ : t₁ y₂ = y₂⁻¹ := by
    rw [← hk', map_zpow, h₁y, inv_zpow]
  have hy₂1 : y₂ ≠ 1 := by
    rintro rfl
    exact hy₂ (Subgroup.one_mem _)
  exact GGIsReflection.eq_of_apply_eq_inv hp2 hBs hNT h₁N h₂N h₁ h₂ hy₂1 h₁y₂ h₂y

private theorem ggF4_plane {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {tL t' tK s : MulAut ↥Bs} (hsN : s ∈ ggInduced ⊤ Bs) (hKN : tK ∈ ggInduced ⊤ Bs)
    (hL : GGIsReflection p tL) (h' : GGIsReflection p t') (hs : GGIsReflection p s)
    (hK : GGIsReflection p tK) {x y' y : ↥Bs} (hLx : tL x = x⁻¹) (h'y : t' y' = y'⁻¹)
    (hKy : tK y = y⁻¹) (hy1 : y ≠ 1)
    (hy : (y : G) ∈ Subgroup.closure ({(x : G), (y' : G)} : Set G))
    (hnc : ¬ Commute tL t') (hsL : Commute s tL) (hs' : Commute s t') : Commute s tK := by
  have hsLne : s ≠ tL := fun h => hnc (h ▸ hs')
  have hs'ne : s ≠ t' := fun h => hnc (h ▸ hsL).symm
  have hsx : s x = x :=
    GGIsReflection.apply_eq_of_commute hp2 hBs hs hL hsL hsLne hLx
  have hsy' : s y' = y' :=
    GGIsReflection.apply_eq_of_commute hp2 hBs hs h' hs' hs'ne h'y
  have hsy : s y = y := apply_eq_of_mem_closure_pair hsx hsy' hy
  exact GGIsReflection.commute_of_apply_eq hp2 hBs hNT hsN hKN hK hy1 hKy hsy

private theorem ggF4_join_gen {G : Type} [Group G] {Bs L : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {tL : MulAut ↥Bs} {t : Subgroup G → MulAut ↥Bs}
    (hLc : ∀ φ ∈ ggAutomizer L Bs, φ * tL = tL * φ)
    (htc : ∀ K ∈ 𝒦, ∀ φ ∈ ggAutomizer K Bs, φ * t K = t K * φ) :
    ggAutomizerJoin L Bs 𝒦 ≤
      (ggAutomizerJoin L Bs 𝒦 ⊓ Subgroup.centralizer ({tL} : Set (MulAut ↥Bs))) ⊔
        ⨆ K ∈ 𝒦, (ggAutomizerJoin L Bs 𝒦 ⊓ Subgroup.centralizer ({t K} : Set (MulAut ↥Bs))) := by
  unfold ggAutomizerJoin
  refine sup_le ?_ ?_
  · intro φ hφ
    exact Subgroup.mem_sup_left ⟨Subgroup.mem_sup_left hφ,
      Subgroup.mem_centralizer_singleton_iff.mpr (hLc φ hφ)⟩
  · refine iSup₂_le fun K hK => ?_
    intro φ hφ
    exact Subgroup.mem_sup_right <|
      Subgroup.mem_iSup_of_mem K <|
        Subgroup.mem_iSup_of_mem hK ⟨
          Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem K (Subgroup.mem_iSup_of_mem hK hφ)),
          Subgroup.mem_centralizer_singleton_iff.mpr (htc K hK φ hφ)⟩

private structure GGJoinEndpoints {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (yK : G) (K : Subgroup G) where
  fixL : GGFixLineComp Bs x L
  fixK : GGFixLineComp Bs yK K
  tL : MulAut ↥Bs
  tK : MulAut ↥Bs
  t : Subgroup G → MulAut ↥Bs
  y : (K' : Subgroup G) → K' ∈ 𝒦 → G
  nbr : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦), GGNbr p B x D J (y K' hK') K'
  fixN : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦), GGFixLineComp Bs (y K' hK') K'
  tL_mem : tL ∈ ggAutomizerJoin L Bs 𝒦
  tL_refl : GGIsReflection p tL
  tL_inv : tL ⟨x, fixL.mem⟩ = ⟨x, fixL.mem⟩⁻¹
  tL_comm : ∀ φ ∈ ggAutomizer L Bs, φ * tL = tL * φ
  tL_card : Nat.card ↥(ggAutomizer L Bs) = 24 ∨ Nat.card ↥(ggAutomizer L Bs) = 48
  tK_mem : tK ∈ ggAutomizerJoin L Bs 𝒦
  tK_refl : GGIsReflection p tK
  tK_inv : tK ⟨yK, fixK.mem⟩ = ⟨yK, fixK.mem⟩⁻¹
  tK_comm : ∀ φ ∈ ggAutomizer K Bs, φ * tK = tK * φ
  tK_card : Nat.card ↥(ggAutomizer K Bs) = 24 ∨ Nat.card ↥(ggAutomizer K Bs) = 48
  tN_mem : ∀ (K' : Subgroup G) (_ : K' ∈ 𝒦), t K' ∈ ggAutomizerJoin L Bs 𝒦
  tN_refl : ∀ (K' : Subgroup G) (_ : K' ∈ 𝒦), GGIsReflection p (t K')
  tN_inv : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦),
    t K' ⟨y K' hK', (fixN K' hK').mem⟩ = ⟨y K' hK', (fixN K' hK').mem⟩⁻¹
  tN_comm : ∀ (K' : Subgroup G) (_ : K' ∈ 𝒦), ∀ φ ∈ ggAutomizer K' Bs,
    φ * t K' = t K' * φ
  tN_card : ∀ (K' : Subgroup G) (_ : K' ∈ 𝒦),
    Nat.card ↥(ggAutomizer K' Bs) = 24 ∨ Nat.card ↥(ggAutomizer K' Bs) = 48

private structure GGJoinChosen {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} where
  y : (K' : Subgroup G) → K' ∈ 𝒦 → G
  nbr : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦), GGNbr p B x D J (y K' hK') K'
  fixN : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦), GGFixLineComp Bs (y K' hK') K'
  t : Subgroup G → MulAut ↥Bs
  tN_mem : ∀ (K' : Subgroup G) (_ : K' ∈ 𝒦), t K' ∈ ggAutomizerJoin L Bs 𝒦
  tN_refl : ∀ (K' : Subgroup G) (_ : K' ∈ 𝒦), GGIsReflection p (t K')
  tN_inv : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦),
    t K' ⟨y K' hK', (fixN K' hK').mem⟩ = ⟨y K' hK', (fixN K' hK').mem⟩⁻¹
  tN_comm : ∀ (K' : Subgroup G) (_ : K' ∈ 𝒦), ∀ φ ∈ ggAutomizer K' Bs,
    φ * t K' = t K' * φ
  tN_card : ∀ (K' : Subgroup G) (_ : K' ∈ 𝒦),
    Nat.card ↥(ggAutomizer K' Bs) = 24 ∨ Nat.card ↥(ggAutomizer K' Bs) = 48

private theorem ggF4_join_automizer_le {G : Type} [Group G] {Bs L : Subgroup G}
    (𝒦 : Finset (Subgroup G)) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K' ∈ 𝒦, K') Bs := by
  rw [ggAutomizerJoin]
  refine sup_le (ggAutomizer_mono Bs le_sup_left) (iSup₂_le fun K hK => ?_)
  exact ggAutomizer_mono Bs (le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl))

private theorem ggF4_join_chosen_hex
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hF4 : GGIsWeylMatrixF4 M)
    (hfixA : ∀ b : ↥Bs, (∀ a ∈ ggAutomizerJoin L Bs 𝒦, a b = b) → b = 1)
    (hRM : ∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hWK : ∀ y K, GGNbr p B x D J y K → GGWeylReflectionGroup p (ggAutomizer K Bs))
    {y' : (K' : Subgroup G) → K' ∈ 𝒦 → G}
    {hN' : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦), GGNbr p B x D J (y' K' hK') K'}
    {hfixN : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦), GGFixLineComp Bs (y' K' hK') K'} :
    ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦), ∃ t' : MulAut ↥Bs,
      t' ∈ ggAutomizerJoin L Bs 𝒦 ∧ GGIsReflection p t' ∧
      t' ⟨y' K' hK', (hfixN K' hK').mem⟩ = ⟨y' K' hK', (hfixN K' hK').mem⟩⁻¹ ∧
      (∀ φ ∈ ggAutomizer K' Bs, φ * t' = t' * φ) ∧
      (Nat.card ↥(ggAutomizer K' Bs) = 24 ∨ Nat.card ↥(ggAutomizer K' Bs) = 48) := by
  intro K' hK'
  have hy'1 : y' K' hK' ≠ 1 := fun h =>
    GGConfig.not_mem_zpowers_of_ggNbr hR.1.1 (hN' K' hK') (h ▸ Subgroup.one_mem _)
  exact ggF4_join_endpoint hR hP hF4 hfixA (hfixN K' hK') hy'1
    (hRM _ _ (hN' K' hK')) (hWK _ _ (hN' K' hK'))

private noncomputable def ggF4_join_chosen
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    (hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hRM : ∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hWK : ∀ y K, GGNbr p B x D J y K → GGWeylReflectionGroup p (ggAutomizer K Bs))
    (hF1 : ∀ y K, GGNbr p B x D J y K → ∀ b : ↥Bs, (∀ a ∈ ggAutomizer K Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G)) :
    GGJoinChosen (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
      (𝒦 := 𝒦) := by
  classical
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hfixA := ggF4_join_fix_one hR hFixL hF1 (ggF4_join_nonempty hR hF1 hRM)
  have hB : B = Bs := ggF4_join_B_eq_bstar hR hP hF4 hfixA
  let y' : (K' : Subgroup G) → K' ∈ 𝒦 → G := fun K' hK' =>
    Classical.choose (hR.2.2.2.1.2 K' hK')
  let hN' : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦), GGNbr p B x D J (y' K' hK') K' :=
    fun K' hK' => Classical.choose_spec (hR.2.2.2.1.2 K' hK')
  have hfixN : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦), GGFixLineComp Bs (y' K' hK') K' :=
    fun K' hK' => ggF4_join_fixLine_nbr hR hB hF1 (hN' K' hK')
  have hex := ggF4_join_chosen_hex hR hP hF4 hfixA hRM hWK
    (y' := y') (hN' := hN') (hfixN := hfixN)
  let t : Subgroup G → MulAut ↥Bs := fun K' =>
    if hK' : K' ∈ 𝒦 then Classical.choose (hex K' hK') else 1
  have ht : ∀ (K' : Subgroup G) (hK' : K' ∈ 𝒦),
      t K' ∈ ggAutomizerJoin L Bs 𝒦 ∧ GGIsReflection p (t K') ∧
      t K' ⟨y' K' hK', (hfixN K' hK').mem⟩ = ⟨y' K' hK', (hfixN K' hK').mem⟩⁻¹ ∧
      (∀ φ ∈ ggAutomizer K' Bs, φ * t K' = t K' * φ) ∧
      (Nat.card ↥(ggAutomizer K' Bs) = 24 ∨ Nat.card ↥(ggAutomizer K' Bs) = 48) := by
    intro K' hK'
    dsimp only [t]
    rw [dif_pos hK']
    exact Classical.choose_spec (hex K' hK')
  exact ⟨y', hN', hfixN, t,
    fun K' hK' => (ht K' hK').1, fun K' hK' => (ht K' hK').2.1,
    fun K' hK' => (ht K' hK').2.2.1, fun K' hK' => (ht K' hK').2.2.2.1,
    fun K' hK' => (ht K' hK').2.2.2.2⟩

private noncomputable def ggF4_join_endpoints
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    (hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hWL : GGWeylReflectionGroup p (ggAutomizer L Bs))
    (hRM : ∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hWK : ∀ y K, GGNbr p B x D J y K → GGWeylReflectionGroup p (ggAutomizer K Bs))
    (hF1 : ∀ y K, GGNbr p B x D J y K → ∀ b : ↥Bs, (∀ a ∈ ggAutomizer K Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G))
    {y : G} {K : Subgroup G} (hn : GGNbr p B x D J y K) :
    GGJoinEndpoints (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
      (𝒦 := 𝒦) y K := by
  classical
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hfixA := ggF4_join_fix_one hR hFixL hF1 (ggF4_join_nonempty hR hF1 hRM)
  have hB : B = Bs := ggF4_join_B_eq_bstar hR hP hF4 hfixA
  have hfixLinL : GGFixLineComp Bs x L := ggF4_join_fixLine_L hR hFixL
  have hfixLinK : GGFixLineComp Bs y K := ggF4_join_fixLine_nbr hR hB hF1 hn
  have hy1 : y ≠ 1 := fun h =>
    GGConfig.not_mem_zpowers_of_ggNbr hR.1.1 hn (h ▸ Subgroup.one_mem _)
  let C := ggF4_join_chosen hR hP hF4 hFixL hRM hWK hF1
  let tL : MulAut ↥Bs := Classical.choose
    (ggF4_join_endpoint hR hP hF4 hfixA hfixLinL hx1 le_sup_left hWL)
  have htL := Classical.choose_spec
    (ggF4_join_endpoint hR hP hF4 hfixA hfixLinL hx1 le_sup_left hWL)
  let tK : MulAut ↥Bs := Classical.choose
    (ggF4_join_endpoint hR hP hF4 hfixA hfixLinK hy1 (hRM y K hn) (hWK y K hn))
  have htK := Classical.choose_spec
    (ggF4_join_endpoint hR hP hF4 hfixA hfixLinK hy1 (hRM y K hn) (hWK y K hn))
  exact ⟨hfixLinL, hfixLinK, tL, tK, C.t, C.y, C.nbr, C.fixN,
    htL.1, htL.2.1, htL.2.2.1, htL.2.2.2.1, htL.2.2.2.2,
    htK.1, htK.2.1, htK.2.2.1, htK.2.2.2.1, htK.2.2.2.2,
    C.tN_mem, C.tN_refl, C.tN_inv, C.tN_comm, C.tN_card⟩

private theorem ggF4_join_frame_cond {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {y : G} {K : Subgroup G}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) (hx1 : x ≠ 1)
    (hAind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs)
    (E : GGJoinEndpoints (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
      (𝒦 := 𝒦) y K) :
    ∀ i ∈ 𝒦, ∀ j ∈ 𝒦, Commute E.tL (E.t i) → Commute E.tL (E.t j) →
      E.t i = E.t j := by
  intro i hi j hj hci hcj
  have hx'1 : (⟨x, E.fixL.mem⟩ : ↥Bs) ≠ 1 :=
    fun h => hx1 (by simpa using congrArg Subtype.val h)
  have hyi : (E.y i hi : G) ∉ Subgroup.zpowers (x : G) :=
    GGConfig.not_mem_zpowers_of_ggNbr hR.1.1 (E.nbr i hi)
  have hyj : (E.y j hj : G) ∉ Subgroup.zpowers (x : G) :=
    GGConfig.not_mem_zpowers_of_ggNbr hR.1.1 (E.nbr j hj)
  have hclos : (E.y j hj : G) ∈ Subgroup.closure ({(x : G), (E.y i hi : G)} : Set G) :=
    GGNbr.mem_closure_pair (E.nbr j hj) (E.nbr i hi)
  exact ggF4_frame (tL := E.tL) (t₁ := E.t i) (t₂ := E.t j)
    (x := ⟨x, E.fixL.mem⟩) (y₁ := ⟨E.y i hi, (E.fixN i hi).mem⟩)
    (y₂ := ⟨E.y j hj, (E.fixN j hj).mem⟩)
    hp2 hBs hNT (hAind (E.tN_mem i hi)) (hAind (E.tN_mem j hj)) E.tL_refl
    (E.tN_refl i hi) (E.tN_refl j hj) hx'1 E.tL_inv (E.tN_inv i hi) (E.tN_inv j hj) hyi hyj
    hclos hci hcj

private theorem ggF4_join_plane_cond {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {y : G} {K : Subgroup G}
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hAind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs)
    (E : GGJoinEndpoints (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
      (𝒦 := 𝒦) y K) (hn : GGNbr p B x D J y K) (hy1 : y ≠ 1) :
    ∀ i ∈ 𝒦, ¬ Commute E.tL (E.t i) → ∀ s ∈ ggAutomizerJoin L Bs 𝒦,
      GGIsReflection p s → Commute s E.tL → Commute s (E.t i) → Commute s E.tK := by
  intro i hi hnc s hsA hsrefl hsL hsi
  have hy : (y : G) ∈ Subgroup.closure ({(x : G), (E.y i hi : G)} : Set G) :=
    GGNbr.mem_closure_pair hn (E.nbr i hi)
  have hy'1 : (⟨y, E.fixK.mem⟩ : ↥Bs) ≠ 1 :=
    fun h => hy1 (by simpa using congrArg Subtype.val h)
  exact ggF4_plane (tL := E.tL) (t' := E.t i) (tK := E.tK) (s := s)
    (x := ⟨x, E.fixL.mem⟩) (y' := ⟨E.y i hi, (E.fixN i hi).mem⟩)
    (y := ⟨y, E.fixK.mem⟩) hp2 hBs hNT (hAind hsA)
    (hAind E.tK_mem) E.tL_refl (E.tN_refl i hi) hsrefl
    E.tK_refl E.tL_inv (E.tN_inv i hi) E.tK_inv hy'1 hy hnc hsL hsi

private theorem ggF4_join_conj
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {y : G} {K : Subgroup G}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hAind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs) (hx1 : x ≠ 1)
    (E : GGJoinEndpoints (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
      (𝒦 := 𝒦) y K) (hn : GGNbr p B x D J y K) (hy1 : y ≠ 1) :
    ∃ w ∈ ggAutomizerJoin L Bs 𝒦, w * E.tK * w⁻¹ = E.tL ∨
      ∃ K' ∈ 𝒦, w * E.tK * w⁻¹ = E.t K' := by
  have hcomm := ggF4_join_frame_cond hR hp2 hBs hNT hx1 hAind E
  have hplane := ggF4_join_plane_cond hp2 hBs hNT hAind E hn hy1
  have hgen := ggF4_join_gen E.tL_comm E.tN_comm
  exact ggF4_exists_conj_of_cover hp2 hBs hNT hAind hP hF4 𝒦 E.tL_mem E.tK_mem E.tN_mem
    E.tL_refl E.tK_refl E.tN_refl hcomm hplane hgen

private theorem ggF4_join_absorb
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {y : G} {K : Subgroup G}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hAind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs)
    (hAH : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K' ∈ 𝒦, K') Bs)
    (hRM : ∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (E : GGJoinEndpoints (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
      (𝒦 := 𝒦) y K) (hn : GGNbr p B x D J y K) (hy1 : y ≠ 1)
    {X : Subgroup G} {u : G} (hX : GGFixLineComp Bs u X)
    (hXH : X ≤ L ⊔ ⨆ K' ∈ 𝒦, K')
    (hBX : Bs ≤ Subgroup.normalizer (X : Set G)) (hu1 : u ≠ 1)
    (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {tX : MulAut ↥Bs} (htXA : tX ∈ ggAutomizerJoin L Bs 𝒦)
    (htXrefl : GGIsReflection p tX)
    (htXu : tX ⟨u, hX.mem⟩ = ⟨u, hX.mem⟩⁻¹)
    (hXcomm : ∀ φ ∈ ggAutomizer X Bs, φ * tX = tX * φ)
    (hXcard : Nat.card ↥(ggAutomizer X Bs) = 24 ∨ Nat.card ↥(ggAutomizer X Bs) = 48)
    {w : MulAut ↥Bs} (hwA : w ∈ ggAutomizerJoin L Bs 𝒦) (hw : w * E.tK * w⁻¹ = tX) :
    K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have hC : Nat.card ↥(ggAutomizerJoin L Bs 𝒦 ⊓
      Subgroup.centralizer ({tX} : Set (MulAut ↥Bs))) ≤ 96 :=
    ggF4_card_inf_centralizer_le hp2 hBs hNT hAind hP hF4 htXA htXrefl
  exact GGFixLineComp.le_of_conj_endpointRefl (H := L ⊔ ⨆ K' ∈ 𝒦, K') (X := X) (K := K)
    (u := u) (y := y) hp2 hBs hX E.fixK hXH hBX hu1 hy1 hAH hwA hw htXrefl htXu E.tK_inv
    hXA (hRM y K hn) hXcomm E.tK_comm hXcard E.tK_card hC

private theorem ggF4_join_nbr_le
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    (hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hWL : GGWeylReflectionGroup p (ggAutomizer L Bs))
    (hRM : ∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hWK : ∀ y K, GGNbr p B x D J y K → GGWeylReflectionGroup p (ggAutomizer K Bs))
    (hF1 : ∀ y K, GGNbr p B x D J y K → ∀ b : ↥Bs, (∀ a ∈ ggAutomizer K Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G))
    {y : G} {K : Subgroup G} (hn : GGNbr p B x D J y K) : K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hpFact : Fact p.Prime := ⟨hp⟩
  let : Fact p.Prime := hpFact
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hNT : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hAind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs := ggAutomizerJoin_le_ggInduced_top L 𝒦
  have hAH : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K' ∈ 𝒦, K') Bs :=
    ggF4_join_automizer_le 𝒦
  have hyNot : y ∉ Subgroup.zpowers x := GGConfig.not_mem_zpowers_of_ggNbr hR.1.1 hn
  have hy1 : y ≠ 1 := fun h => hyNot (h ▸ Subgroup.one_mem _)
  have E := ggF4_join_endpoints hR hP hF4 hFixL hWL hRM hWK hF1 hn
  obtain ⟨w, hwA, hw | ⟨i, hi, hw⟩⟩ :=
    ggF4_join_conj hR hP hF4 hp2 hBs hNT hAind hx1 E hn hy1
  · exact ggF4_join_absorb hP hF4 hp2 hBs hNT hAind hAH hRM E hn hy1 E.fixL le_sup_left
      ((hR.1.2.2.1.1).le_normalizer) hx1 le_sup_left E.tL_mem E.tL_refl E.tL_inv E.tL_comm
      E.tL_card hwA hw
  · exact ggF4_join_absorb hP hF4 hp2 hBs hNT hAind hAH hRM E hn hy1 (E.fixN i hi)
      (le_sup_of_le_right (le_iSup₂_of_le i hi le_rfl))
      ((hR.1.2.2.1.2 _ _ (E.nbr i hi)).le_normalizer)
      (fun h => GGConfig.not_mem_zpowers_of_ggNbr hR.1.1 (E.nbr i hi) (h ▸ Subgroup.one_mem _))
      (hRM _ _ (E.nbr i hi)) (E.tN_mem i hi) (E.tN_refl i hi) (E.tN_inv i hi)
      (E.tN_comm i hi) (E.tN_card i hi) hwA hw

theorem ggSecFiveF4Join_of_suppliers
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    (hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hWL : GGWeylReflectionGroup p (ggAutomizer L Bs))
    (hRM : ∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hWK : ∀ y K, GGNbr p B x D J y K → GGWeylReflectionGroup p (ggAutomizer K Bs))
    (hF1 : ∀ y K, GGNbr p B x D J y K → ∀ b : ↥Bs, (∀ a ∈ ggAutomizer K Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G)) :
    ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K :=
  GGSecFiveRouteCfg.ggG0_eq_of_forall_le hR fun _ _ hn =>
    ggF4_join_nbr_le hR hP hF4 hFixL hWL hRM hWK hF1 hn

theorem ggSecFiveRowJoinOffQAt_F4_of_reflMaxAt
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hTBF : GGTBFixInput)
    (hFC : GGResNbrFixCentralizesInput) (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M) :
    GGSecFiveRowJoinOffQAt fun M => GGIsWeylMatrixF4 M := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 hQ ι M e hP hF
  have hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) →
      (b : G) ∈ Subgroup.zpowers x := fun b hb =>
    ((GGSecFiveRestHyp.fixLineComp_L hTBF hR.1 hR.2.1).fix_iff b).1 hb
  have hWL : GGWeylReflectionGroup p (ggAutomizer L Bs) :=
    GGSecFiveRestHyp.weylReflectionGroup_L hX hTCJ hRig hR.1 hR.2.1
  have hRM' : ∀ y K, GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 := fun y K hn =>
    hRM G p B Bs x L D J 𝒦 hR ι M e hP hF y K hn
  have hWK : ∀ y K, GGNbr p B x D J y K →
      GGWeylReflectionGroup p (ggAutomizer K Bs) := fun y K hn =>
    GGSecFiveRestHyp.weylReflectionGroup_nbr hX hTCJ hRig hTPn hA8 hraw hiso hR.1 hR.2.1 hn
  have hF1 : ∀ y K, GGNbr p B x D J y K → ∀ b : ↥Bs,
      (∀ a ∈ ggAutomizer K Bs, a b = b) → (b : G) ∈ Subgroup.centralizer (K : Set G) :=
    fun y K hn b hb =>
      hFC G p B Bs x L D J y K
        ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hn, hR.2.1 y K hn, Or.inr hR.2.1⟩ b hb
  exact ggSecFiveF4Join_of_suppliers hR hP hF hFixL hWL hRM' hWK hF1

end CFSG.StandardType

end
