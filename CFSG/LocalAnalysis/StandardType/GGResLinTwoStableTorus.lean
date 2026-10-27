module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGTorusGenLinTwoLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordAux
public import CFSG.GroupTheory.IndexThreeCosets
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.StandardType.HdRo7C

private theorem largeEvenRawDatumLegacy_exists_stable {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatumLegacy lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> dsimp only [LargeEvenRawDatumLegacy] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, _, b, c, _, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, _, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

theorem GGResHyp.linTwo_stable_torus
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (lab : LargeEvenLabel) (hlab : GGLinTwoLabel 3 lab)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hL : GGInnerDiagOnLabel (fun p lab' => p = 3 ∧ lab' = lab) 3 Bs L) :
    ∃ (s : ℕ) (T : LinTwoTB.TorusData ↥L s),
      T.IsTorusAut (ggGamma L hN).range ∧
      (∀ g h : ↥L, MulAut.conj g = MulAut.conj h → g = h) ∧
      Bs ⊓ L = T.tor.map L.subtype ∧
      Nat.card ↥(Bs ⊓ L) = 3 ^ s ∧
      s = (lab.rank + 1) / 2 ∧
      Nat.card ↥Bs = 3 ^ (s + 1) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hperf, lab', hlab', hraw⟩ := hL
  let Q : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
        (fun p lab' => p = 3 ∧ lab' = lab) 3 lab' ∧
          Bs ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L =>
              (l' : G) = b⁻¹ * (l : G) * b) φ
  have hrawQ : LargeEvenRawDatumLegacy lab' Q := hraw
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatumLegacy_exists_stable (Q := Q) hrawQ
  have hlab'_eq : lab' = lab := hQ.2.2.choose_spec.1.2
  subst lab'
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, hp⟩ := hlab
  subst ht
  subst hn
  have hl' : 5 ≤ l := by simpa using hl
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeLinear] at hraw
  obtain ⟨K, hfield, hfinite, hK, hrawP⟩ := hraw
  obtain ⟨θ, hP⟩ := hrawP.2.2
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hK2 : Nat.card K = 2 := by simpa using hK
  let d : ℕ := l + 1
  have hd : 6 ≤ d := by dsimp [d]; omega
  have hd5 : 5 ≤ d := by omega
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := hP.2.1
  have hBs3 : ∀ b ∈ Bs, ∃ φ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      LargeEvenInduces (θ := θ) (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ := by
    simpa [d] using hP.2.2
  let ψ : ↥L →* projectiveSL d K :=
    (TypeA.recipeEquiv d K).toMonoidHom.comp (ggQuotHom θ)
  let A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hA : IsElemAbelian 3 A :=
    isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
      (fun b => Subtype.ext (hBs.2 b b.2)) (ggGamma L hBsN)
  have hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : ↥L,
      φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨φ, hφI, hφind⟩ := hBs3 (b⁻¹) (Bs.inv_mem b.2)
    refine ⟨MulAut.congr (TypeA.recipeEquiv d K) φ,
      TypeA.congr_recipeEquiv_mem hφI, ?_⟩
    intro l
    have hmemL : (b : G) * (l : G) * (b : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hBsN b.2) (l : G)).mp l.2
    let l' : ↥L := ⟨(b : G) * (l : G) * (b : G)⁻¹, hmemL⟩
    have hrel : (l' : G) = (b⁻¹ : ↥Bs)⁻¹ * (l : G) * (b⁻¹ : ↥Bs) := by
      dsimp [l']; simp only [Subgroup.coe_inv, inv_inv]
    have hind := hφind l l' hrel
    have hgl : ((ggGamma L hBsN) b) l = l' := Subtype.ext (ggGamma_coe L hBsN b l)
    change (MulAut.congr (TypeA.recipeEquiv d K) φ) (ψ l) =
      ψ (((ggGamma L hBsN) b) l)
    have hψl : ψ l = (TypeA.recipeEquiv d K) (θ (QuotientGroup.mk l)) := rfl
    have hψl' : ψ l' = (TypeA.recipeEquiv d K) (θ (QuotientGroup.mk l')) := rfl
    rw [hgl, MulAut.congr_apply, hψl, hψl']
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hind]
  have hker : ψ.ker = Subgroup.center ↥L := by
    ext l
    show (TypeA.recipeEquiv d K) ((ggQuotHom θ) l) = 1 ↔ l ∈ Subgroup.center ↥L
    rw [(TypeA.recipeEquiv d K).map_eq_one_iff, ← MonoidHom.mem_ker, ker_ggQuotHom]
  have hψ : Function.Surjective (ψ) :=
    (TypeA.recipeEquiv d K).surjective.comp (ggQuotHom_surjective θ)
  have hkerGG : (ggGamma L hBsN).ker = (Subgroup.zpowers x).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
    constructor
    · intro h
      have hmem : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨b.2, h⟩
      rwa [hdRo7CLCoordAux_bstar_centralizer_eq hH] at hmem
    · intro h
      have hmem : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        rwa [hdRo7CLCoordAux_bstar_centralizer_eq hH]
      exact hmem.2
  have hkernelCard : Nat.card ↥((ggGamma L hBsN).ker) = 3 := by
    rw [hkerGG]
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hH.1.tableB_facts.2.2.1)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH)
        (hdRo7CLCoordAux_x_ne_one hH)]
  have hcardRangeMul : Nat.card ↥A * 3 = Nat.card ↥Bs := by
    have h1 := TableB.card_range_mul_card_ker (ggGamma L hBsN)
    rw [hkerGG] at h1
    have hk : Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) = 3 := by
      rw [← hkerGG]; exact hkernelCard
    rw [hk] at h1
    simpa [A] using h1
  have hCharP : CharP K 2 := by
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      (by simpa using hK)
  letI : CharP K 2 := hCharP
  have hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut L θ ⟨b, hBsN hb⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ := by
    intro b hb
    exact ggLAut_mem_of_induces L θ hBsN hBs3 hb
  have hlift0 : GGTorusLift 3 (d / 2) (projectiveSL d K) :=
    TwoThree.ggTorusLift_two hK2 hd5
  have hlift : GGTorusLift 3 (d / 2)
      (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K) hlift0
  have hTB := ggTorusTBGroup_of_L hH.1 hperf θ hBsN hBsI hlift
  have hr : 3 ^ (d / 2) ≤ Nat.card ↥A := hTB.2.2.2.2.2.1
  obtain ⟨s, e, T, wt, hZinj, hTA, hs, hwpos, hwt, hwinv⟩ :=
    LinTwoTB.exists_data_with_rank_bound hK2 hd ψ hψ hker.le hperf A hA hAI hr
  have hcardT : Nat.card ↥T.tor = 3 ^ s := by
    rw [show T.tor = T.ι.range from rfl]
    rw [← Nat.card_congr (MonoidHom.ofInjective T.inj).toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hcardA : Nat.card ↥A = 3 ^ s := by
    let f : (Fin s → ZMod 3) → ↥A := fun v =>
      ⟨MulAut.conj (T.el v), (hTA _).mpr ⟨v, rfl⟩⟩
    have hfinj : Function.Injective f := by
      intro v w h
      have hc : MulAut.conj (T.el v) = MulAut.conj (T.el w) := congrArg Subtype.val h
      exact T.el_inj (hZinj _ _ hc)
    have hfsurj : Function.Surjective f := by
      intro a
      obtain ⟨v, hv⟩ := (hTA (a : MulAut ↥L)).mp a.2
      exact ⟨v, Subtype.ext hv.symm⟩
    rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)]
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hTorLe : T.tor.map L.subtype ≤ Bs ⊓ L := by
    rintro z ⟨t, ht, rfl⟩
    have htBs : (t : G) ∈ Bs := by
      apply hSC (t : G)
      · rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨v, hv⟩ := (hTA (ggGamma L hBsN ⟨b, hb⟩)).mp ⟨⟨b, hb⟩, rfl⟩
        let s0 : ↥L := T.el v
        let z0 : G := (s0 : G)⁻¹ * b
        have hb_eq : (b : G) = (s0 : G) * z0 := by dsimp [z0]; group
        have hzcent : z0 ∈ Subgroup.centralizer (L : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          have hγ : ((b : G) * l * (b : G)⁻¹) =
              ((s0 : G) * l * (s0 : G)⁻¹) := by
            have h := congrArg (fun f : MulAut ↥L => (((f ⟨l, hl⟩ : ↥L) : G))) hv
            simpa [ggGamma_coe, MulAut.conj_apply, s0] using h
          have hzconj : z0 * l * z0⁻¹ = l := by
            dsimp [z0]
            calc
              ((s0 : G)⁻¹ * b) * l * ((s0 : G)⁻¹ * b)⁻¹
                  = (s0 : G)⁻¹ * ((b : G) * l * (b : G)⁻¹) * s0 := by group
              _ = (s0 : G)⁻¹ * ((s0 : G) * l * (s0 : G)⁻¹) * s0 := by rw [hγ]
              _ = l := by group
          calc
            l * z0 = (z0 * l * z0⁻¹) * z0 := by rw [hzconj]
            _ = z0 * l := by group
        have htcomm_s : (t : G) * (s0 : G) = (s0 : G) * (t : G) := by
          obtain ⟨vt, hvt⟩ := T.mem_tor.mp ht
          rw [hvt]
          exact congrArg (fun u : ↥L => (u : G)) (T.el_comm vt v)
        have htcomm_z : (t : G) * z0 = z0 * (t : G) :=
          Subgroup.mem_centralizer_iff.mp hzcent (t : G) t.2
        symm
        calc
          (t : G) * b = (t : G) * ((s0 : G) * z0) := by rw [hb_eq]
          _ = ((t : G) * (s0 : G)) * z0 := by group
          _ = ((s0 : G) * (t : G)) * z0 := by rw [htcomm_s]
          _ = (s0 : G) * ((t : G) * z0) := by group
          _ = (s0 : G) * (z0 * (t : G)) := by rw [htcomm_z]
          _ = ((s0 : G) * z0) * (t : G) := by group
          _ = b * (t : G) := by rw [hb_eq]
      · obtain ⟨v, hv⟩ := T.mem_tor.mp ht
        rw [hv]
        exact congrArg (fun u : ↥L => (u : G)) (T.el_cube v)
    exact ⟨htBs, t.2⟩
  have hLeTor : Bs ⊓ L ≤ T.tor.map L.subtype := by
    rintro z hz
    obtain ⟨hzBs, hzL⟩ := hz
    let t : ↥L := ⟨z, hzL⟩
    have hγt : ggGamma L hBsN ⟨z, hzBs⟩ = MulAut.conj t := by
      ext l
      simp [ggGamma_coe, MulAut.conj_apply, t]
    have hγA : ggGamma L hBsN ⟨z, hzBs⟩ ∈ A := ⟨⟨z, hzBs⟩, rfl⟩
    obtain ⟨v, hv⟩ := (hTA (ggGamma L hBsN ⟨z, hzBs⟩)).mp hγA
    have ht_eq : t = T.el v := hZinj t (T.el v) (by rw [← hγt, hv])
    exact ⟨t, T.mem_tor.mpr ⟨v, ht_eq⟩, rfl⟩
  have hEq : Bs ⊓ L = T.tor.map L.subtype := le_antisymm hLeTor hTorLe
  have hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ s := by
    rw [hEq, Subgroup.card_map_of_injective (f := L.subtype)
      (fun a b h => Subtype.ext h)]
    exact hcardT
  have hsge : d / 2 ≤ s := by
    have hpow : 3 ^ (d / 2) ≤ 3 ^ s := by
      calc 3 ^ (d / 2) ≤ Nat.card ↥A := hr
        _ = 3 ^ s := hcardA
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
  have hs_eq : s = d / 2 := le_antisymm hs hsge
  have hcardBs : Nat.card ↥Bs = 3 ^ (s + 1) := by
    rw [← hcardRangeMul, hcardA, pow_succ]
  exact ⟨s, T, hTA, hZinj, hEq, hcardE, by dsimp [d] at hs_eq; omega, hcardBs⟩

end CFSG.StandardType

end
