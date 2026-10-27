module

public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoord
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordC
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordStd
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotAut
import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameModule
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordStdA
import CFSG.LocalAnalysis.StandardType.GGQTwoDSlConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGQTwoDNbrSixFrame {G : Type} [Group G] [Finite G] (B Bs X : Subgroup G)
    (z : Additive ↥Bs ≃+ DVec 6) where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  [instChar : CharP K 2]
  card_K : Nat.card K = 4
  Q : Type
  [instGroup : Group Q]
  [instFiniteQ : Finite Q]
  f : ↥(Subgroup.normalizer (X : Set G)) →* Q
  ψ : Su K 2 1 6 →* Q
  φ₀ : Equiv.Perm (Fin 6) →* ↥(ggAutomizer X Bs)
  P : DVec 6 ≃ₗ[ZMod 3] DVec 6
  ρ : Equiv.Perm (Fin 6)
  t : Fin 6 → ZMod 3
  ω : Kˣ
  perfect : Group.IsPerfect ↥X
  cent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = 3
  datum : NsQuot.Datum 3 (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X)
  range : ψ.range = NsQuot.img (Subgroup.normalizer (X : Set G)) f X
  hyp : GGNSLocalHyp 3 (NsQuot.img (Subgroup.normalizer (X : Set G)) f B)
    (NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs) K 1 6 ψ
  diag : GGActsDiagonally (p := 2) (f := 1) ψ (NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs)
  φ₀_injective : Function.Injective φ₀
  refl : ∀ a b : Fin 6, a ≠ b →
    GGIsReflection 3 ((φ₀ (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
  perm : ∀ (σ : Equiv.Perm (Fin 6)) (s : ↥Bs)
    (hs : (((((φ₀ σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s : ↥Bs)) : G) ∈
      Subgroup.normalizer (X : Set G))
    (hs' : (s : G) ∈ Subgroup.normalizer (X : Set G)),
    f ⟨_, hs⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs'⟩ * (ψ (ggPermSU σ⁻¹))⁻¹
  sign : ∀ i, t i = 1 ∨ t i = -1
  P_basis : ∀ i, P (dBasis 6 i) = t i • dBasis 6 (ρ i)
  P_equivariant : ∀ (σ : Equiv.Perm (Fin 6)) (s : ↥Bs),
    P (z (Additive.ofMul (((φ₀ σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s))) =
      dPerm 6 σ (P (z (Additive.ofMul s)))
  ω_order : orderOf ω = 3
  induces : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (X : Set G)),
    qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun k => ω ^ (P (z (Additive.ofMul s)) k).val)

attribute [instance] GGQTwoDNbrSixFrame.instField GGQTwoDNbrSixFrame.instFinite
  GGQTwoDNbrSixFrame.instChar GGQTwoDNbrSixFrame.instGroup GGQTwoDNbrSixFrame.instFiniteQ

theorem ggQTwoDNbrSix_signedFrame_of_cent
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {y : G} {X : Subgroup G} (hyB : y ∈ B) (hy1 : y ≠ 1)
    (hXy : X ≤ Subgroup.centralizer ({y} : Set G))
    (hcentX : Nat.card ↥(B ⊓ Subgroup.centralizer (X : Set G)) = p)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X)
    (hcentBs' : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = p)
    (hRM : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (z : Additive ↥Bs ≃+ DVec 6)
    (hz : ∀ r ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection 3 r → ∃ (sgn : Bool) (a b : Fin 6),
      a ≠ b ∧ ∀ s : ↥Bs, z (Additive.ofMul (r s)) = dTau 6 sgn a b (z (Additive.ofMul s))) :
    p = 3 ∧ Nonempty (GGQTwoDNbrSixFrame B Bs X z) := by
  classical
  obtain ⟨K, hf, hfin, lab, m', θ, hK, -, hmrank, hSide, hdvd, hperf, -, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn1, hr5⟩ := hSide
  change n = 1 at hn1
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn1
  subst hr5
  obtain rfl : m' = 6 := by omega
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hdvd)
  subst hp3
  obtain ⟨Q, hQ, hQfin, f, ψ, hD, hrange, hhyp, hdiag⟩ := ggNsq2Member_frame hcfg hcentX hK hdvd
    (Or.inr rfl) θ hperf hBsN hbs
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hyBs : y ∈ Bs := hcfg.1.1.2.1.1 hyB
  have hyX : ∀ l ∈ X, l * y = y * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXy hl)
  have hyord : orderOf y = 3 := orderOf_eq_prime (hD.Bsp y hyBs) hy1
  have hcentBs : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers y := by
    have hle : Subgroup.zpowers y ≤ Bs ⊓ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.2 ⟨hyBs, Subgroup.mem_centralizer_iff.2 fun l hl => hyX l hl⟩
    refine (Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)).symm
    rw [Nat.card_zpowers, hyord, ← hcentBs']
  have hperfX : Group.IsPerfect ↥X := ⟨hperf⟩
  have hy : y ∈ Subgroup.normalizer (X : Set G) := hD.BsN hyBs
  have hcardBs : Nat.card ↥Bs = 3 ^ 6 := by
    calc Nat.card ↥Bs = Nat.card (DVec 6) := Nat.card_congr (Additive.ofMul.trans z.toEquiv)
      _ = 3 ^ 6 := by
        rw [Nat.card_pi]
        simp
  have hcardQ : Nat.card ↥(NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs) = 3 ^ 6 := by
    rw [hD.card_img le_rfl, hcardBs]
  have hfy3 : (f ⟨y, hy⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa [hyord] using pow_orderOf_eq_one y)
    rw [this, map_one]
  have hfy1 : f ⟨y, hy⟩ ≠ 1 := by
    intro h1
    have hinj := hD.injOn (U := Bs) le_rfl
    have hyU : (⟨y, hy⟩ : ↥(Subgroup.normalizer (X : Set G))) ∈ Bs.subgroupOf _ :=
      Subgroup.mem_subgroupOf.mpr hyBs
    have h := @hinj ⟨⟨y, hy⟩, hyU⟩ 1 (by simpa using h1)
    have hy1' : y = 1 := by
      simpa using congrArg
        (fun u : ↥(Bs.subgroupOf _) => ((u : ↥(Subgroup.normalizer (X : Set G))) : G)) h
    exact hy1 hy1'
  have hyord' : orderOf (f ⟨y, hy⟩) = 3 := orderOf_eq_prime hfy3 hfy1
  have hymem : f ⟨y, hy⟩ ∈ NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs :=
    NsQuot.mem_img.2 ⟨⟨y, hy⟩, hyBs, rfl⟩
  have hcentQ : NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs ⊓
      Subgroup.centralizer (NsQuot.img (Subgroup.normalizer (X : Set G)) f X : Set Q) =
      Subgroup.zpowers (f ⟨y, hy⟩) := by
    have hle : Subgroup.zpowers (f ⟨y, hy⟩) ≤ NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs ⊓
        Subgroup.centralizer (NsQuot.img (Subgroup.normalizer (X : Set G)) f X : Set Q) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.2 ⟨hymem, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      obtain ⟨u, huX, rfl⟩ := NsQuot.mem_img.1 hq
      have hcomm : (u : G) * y = y * (u : G) := hyX _ huX
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext hcomm)
    refine (Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)).symm
    rw [hD.cent hperfX le_rfl, hcentBs, Nat.card_zpowers, Nat.card_zpowers, hyord, hyord']
  rw [← hrange] at hcentQ
  obtain ⟨ε, hε, hεrefl⟩ := ggNSDiag_automizer_perm hhyp hdiag
  let τ := hD.tau
  have hmemA : ∀ σ : Equiv.Perm (Fin 6),
      (MulAut.congr τ).symm ((ε σ : ↥(ggAutomizer _ _)) :
        MulAut ↥(NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs)) ∈ ggAutomizer X Bs := by
    intro σ
    have hmem : ((ε σ : ↥(ggAutomizer _ _)) :
        MulAut ↥(NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs)) ∈
        ggAutomizer (NsQuot.img (Subgroup.normalizer (X : Set G)) f X)
          (NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs) := hrange ▸ (ε σ).2
    obtain ⟨r, hr, hrε⟩ := Subgroup.mem_map.1 (hD.automizer_le_map hD.ZL hD.LN hmem)
    have hr' : (MulAut.congr τ).symm ((ε σ : ↥(ggAutomizer _ _)) : MulAut _) = r := by
      rw [← hrε]
      exact (MulAut.congr τ).symm_apply_apply r
    rw [hr']
    exact hr
  let φ₀ : Equiv.Perm (Fin 6) →* ↥(ggAutomizer X Bs) :=
    ((MulAut.congr τ).symm.toMonoidHom.comp
      ((ggAutomizer _ _).subtype.comp ε.toMonoidHom)).codRestrict (ggAutomizer X Bs) hmemA
  have hφ₀ : ∀ σ : Equiv.Perm (Fin 6), ((φ₀ σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
      (MulAut.congr τ).symm ((ε σ : ↥(ggAutomizer _ _)) : MulAut _) := fun _ => rfl
  have hφ₀inj : Function.Injective φ₀ := by
    intro σ σ' h
    apply ε.injective
    apply Subtype.ext
    apply (MulAut.congr τ).symm.injective
    rw [← hφ₀, ← hφ₀, h]
  have hrefl₀ : ∀ a b : Fin 6, a ≠ b →
      GGIsReflection 3 ((φ₀ (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
    intro a b hab
    rw [hφ₀]
    exact (ggIsReflection_congr_iff τ _).1 (by
      rw [MulEquiv.apply_symm_apply]
      exact hεrefl a b hab)
  let φ : Equiv.Perm (Fin 6) →* (DVec 6 ≃ₗ[ZMod 3] DVec 6) :=
    (ggLin (p := 3) z).comp ((ggAutomizer X Bs).subtype.comp φ₀)
  have hφapp : ∀ (σ : Equiv.Perm (Fin 6)) (s : ↥Bs),
      φ σ (z (Additive.ofMul s)) =
        z (Additive.ofMul (((φ₀ σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s)) := by
    intro σ s
    exact ggLin_apply_ofMul (p := 3) z _ s
  have hinj : Function.Injective φ := by
    intro σ σ' h
    apply hφ₀inj
    apply Subtype.ext
    exact ggLin_injective (p := 3) z h
  have hφ : ∀ a b : Fin 6, a ≠ b → ∃ (sgn : Bool) (a' b' : Fin 6), a' ≠ b' ∧
      φ (Equiv.swap a b) = dTau 6 sgn a' b' := by
    intro a b hab
    obtain ⟨sgn, a', b', hab', hv⟩ :=
      hz _ (hRM (φ₀ (Equiv.swap a b)).2) (hrefl₀ a b hab)
    refine ⟨sgn, a', b', hab', LinearEquiv.ext fun v => ?_⟩
    obtain ⟨s, rfl⟩ := (Additive.ofMul.trans z.toEquiv).surjective v
    change φ (Equiv.swap a b) (z (Additive.ofMul s)) = dTau 6 sgn a' b' (z (Additive.ofMul s))
    rw [hφapp, hv s]
  obtain ⟨P, πP, t, ht, hP, hPerm⟩ := ggQTwoDUnit_perm_standard (by norm_num) φ hinj hφ
  have hPz : ∀ (σ : Equiv.Perm (Fin 6)) (s : ↥Bs),
      P (z (Additive.ofMul (((φ₀ σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s))) =
        dPerm 6 σ (P (z (Additive.ofMul s))) := by
    intro σ s
    have h := congrArg (fun L₀ : DVec 6 ≃ₗ[ZMod 3] DVec 6 => L₀ (P (z (Additive.ofMul s))))
      (hPerm σ)
    rw [show (P * φ σ * P⁻¹) (P (z (Additive.ofMul s))) = P (φ σ (z (Additive.ofMul s))) by
      simp [LinearEquiv.mul_apply]] at h
    rw [← h, hφapp]
  let βQ : Additive ↥(NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs) ≃+ DVec 6 :=
    (MulEquiv.toAdditive τ.symm).trans (z.trans P.toAddEquiv)
  have hβQ : ∀ s : ↥Bs, βQ (Additive.ofMul (τ s)) = P (z (Additive.ofMul s)) := by
    intro s
    change P (z (Additive.ofMul (τ.symm (τ s)))) = P (z (Additive.ofMul s))
    rw [MulEquiv.symm_apply_apply]
  have hβQperm : ∀ (σ : Equiv.Perm (Fin 6))
      (q : ↥(NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs)),
      βQ (Additive.ofMul ((((ε σ : ↥(ggAutomizer _ _)) :
        MulAut ↥(NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs))) q)) =
        dPerm 6 σ (βQ (Additive.ofMul q)) := by
    intro σ q
    obtain ⟨s, rfl⟩ := τ.surjective q
    have hεσ : ((ε σ : ↥(ggAutomizer _ _)) :
        MulAut ↥(NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs)) =
        MulAut.congr τ ((φ₀ σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
      rw [hφ₀, MulEquiv.apply_symm_apply]
    rw [hεσ, congr_apply_tau, hβQ, hβQ]
    exact hPz σ s
  have hmodel : QTwoOrdModel (NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs) ψ.range ψ :=
    ⟨rfl, hhyp.ker, fun b => by
      obtain ⟨g, hg, hgu⟩ := hdiag (b : Q) b.2
      exact ⟨g, hg, fun u => by
        obtain ⟨u', hu'1, hu'2⟩ := hgu.2 u
        exact ⟨u', hu'1, hu'2.symm⟩⟩⟩
  obtain ⟨ω, hω, hind⟩ := qtwoDB19_coords_induces (m := 6)
    (Bs := NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs) (L := ψ.range)
    (x := f ⟨y, hy⟩) (ψ := ψ) (ε := ε) hK4 hhyp.ker (by norm_num) rfl hcentQ hcardQ hyord'
    (fun b => qTwoChartTwoThree_induces_of_ordModel hmodel b) hε hβQperm
  have hperm₀ : ∀ (σ : Equiv.Perm (Fin 6)) (s : ↥Bs)
      (hs : (((((φ₀ σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s : ↥Bs)) : G) ∈
        Subgroup.normalizer (X : Set G))
      (hs' : (s : G) ∈ Subgroup.normalizer (X : Set G)),
      f ⟨_, hs⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs'⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ := by
    intro σ s hs hs'
    have hεσ : ((ε σ : ↥(ggAutomizer _ _)) :
        MulAut ↥(NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs)) =
        MulAut.congr τ ((φ₀ σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
      rw [hφ₀, MulEquiv.apply_symm_apply]
    have h := hε σ (τ s)
    rw [hεσ, congr_apply_tau] at h
    exact h
  refine ⟨rfl, ⟨⟨K, hK4, Q, f, ψ, φ₀, P, πP, t, ω, hperfX, hcentBs', hD, hrange, hhyp, hdiag,
    hφ₀inj, hrefl₀, hperm₀, ht, hP, hPz, hω, fun s hs => ?_⟩⟩⟩
  have h := hind (τ s)
  rw [hβQ] at h
  exact h

theorem ggQTwoDNbrSix_signedFrame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {y : G} {X : Subgroup G} (hnbr : GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X)
    (hBBs : B = Bs) (hRM : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (z : Additive ↥Bs ≃+ DVec 6)
    (hz : ∀ r ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection 3 r → ∃ (sgn : Bool) (a b : Fin 6),
      a ≠ b ∧ ∀ s : ↥Bs, z (Additive.ofMul (r s)) = dTau 6 sgn a b (z (Additive.ofMul s))) :
    p = 3 ∧ Nonempty (GGQTwoDNbrSixFrame B Bs X z) :=
  ggQTwoDNbrSix_signedFrame_of_cent hcfg hnbr.1.2.1 hnbr.1.2.2.1 hnbr.1.2.2.2.1
    (ggNSPosPD_routeCfg_cent_K (ggRouteCfg_prime hcfg).1 hnbr) hmark
    (hBBs ▸ ggNSPosPD_routeCfg_cent_K (ggRouteCfg_prime hcfg).1 hnbr) hRM z hz

theorem ggQTwoDNbrSix_signedFrame_base
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L)
    (z : Additive ↥Bs ≃+ DVec 6)
    (hz : ∀ r ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection 3 r → ∃ (sgn : Bool) (a b : Fin 6),
      a ≠ b ∧ ∀ s : ↥Bs, z (Additive.ofMul (r s)) = dTau 6 sgn a b (z (Additive.ofMul s))) :
    p = 3 ∧ Nonempty (GGQTwoDNbrSixFrame B Bs L z) := by
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hS : LargeEvenSStar p B x L := hconf.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := by
    intro h
    have h1 := hconf.orderOf_x
    rw [h, orderOf_one] at h1
    exact (ggRouteCfg_prime hcfg).1.one_lt.ne h1
  have hcentBs : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hconf.bstar_inf_centralizer_L, Nat.card_zpowers, hconf.orderOf_x]
  exact ggQTwoDNbrSix_signedFrame_of_cent hcfg hS.2.1 hx1 hconf.tableB_facts.2.2.2.1
    (ggNSPosPD_routeCfg_cent_L hconf) hmark hcentBs
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)) z hz

theorem ggQTwoD_join_refl_dTau
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 4 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (β : Additive ↥Bs ≃+ DVec m)
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizerJoin L Bs 𝒦) (hrefl : GGIsReflection 3 r) :
    ∃ (sgn : Bool) (a b : Fin m), a ≠ b ∧
      ∀ s : ↥Bs, β (Additive.ofMul (r s)) = dTau m sgn a b (β (Additive.ofMul s)) := by
  classical
  subst hM
  have hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) ((ggCoxeterMatrixD m).reindex e') e :=
    hcfg.2.2.2.1
  have hrc : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  obtain ⟨ϑ, hϑ⟩ := dEven_equiv (m := m) hm
  have hΘ : ∀ (w : (ggCoxeterMatrixD m).Group) (v : DVec m),
      ggLin (p := 3) β ((qtwoE0 e' e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) v =
        (((ϑ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m)) v := by
    let Φ₁ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
      (ggLin (p := 3) β).comp ((ggAutomizerJoin L Bs 𝒦).subtype.comp (qtwoE0 e' e).toMonoidHom)
    let Φ₂ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
      (dEven m).subtype.comp ϑ.toMonoidHom
    have hsimple : ∀ (i : Fin m) (v : DVec m),
        Φ₁ ((ggCoxeterMatrixD m).simple i) v = Φ₂ ((ggCoxeterMatrixD m).simple i) v := by
      intro i v
      have h1 : Φ₁ ((ggCoxeterMatrixD m).simple i) = dTau m (decide (i.val + 1 = m))
          (OrthTorus.simpleLo i) (OrthTorus.simpleHi i) := by
        refine LinearEquiv.ext fun v => ?_
        obtain ⟨s, rfl⟩ := β.surjective v
        change ggLin (p := 3) β ((qtwoE0 e' e ((ggCoxeterMatrixD m).simple i) :
          ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) (β s) = _
        rw [← qtwoDB19_ofMul_toMul s, qtwoE0_simple, ggLin_apply_ofMul,
          hβ i (Additive.toMul s)]
      have h2 : Φ₂ ((ggCoxeterMatrixD m).simple i) = dTau m (decide (i.val + 1 = m))
          (OrthTorus.simpleLo i) (OrthTorus.simpleHi i) := by
        simpa [Φ₂] using hϑ i
      rw [h1, h2]
    intro w v
    exact qtwo_intertwine_of_simple Φ₁ Φ₂ (LinearEquiv.refl (ZMod 3) (DVec m)) hsimple w v
  obtain ⟨sgn, a, b, hab, hv⟩ := ggQTwoD_refl_conj hrc hm e' hpres β
    (Θ := LinearEquiv.refl (ZMod 3) (DVec m)) (ϑ := ϑ) hϑ hΘ hr hrefl
  refine ⟨sgn, a, b, hab, fun s => ?_⟩
  have h := hv (β (Additive.ofMul s))
  rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, ggLin_apply_ofMul] at h
  exact h

theorem ggQTwoDNbrSix_signedFrame_of_sel
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (e' : Fin 6 ≃ ι) (hM : M = (ggCoxeterMatrixD 6).reindex e')
    (β : Additive ↥Bs ≃+ DVec 6)
    (hβ : ∀ (t : Fin 6) (s : ↥Bs),
      β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) s)) =
        dTau 6 (decide (t.val + 1 = 6)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    {y : G} {X : Subgroup G} (hnbr : GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X)
    (hBBs : B = Bs) (hRM : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    p = 3 ∧ Nonempty (GGQTwoDNbrSixFrame B Bs X β) := by
  have hp3 : p = 3 := by
    obtain ⟨K, -, -, lab, -, -, hK, -, -, hSide, hdvd, -⟩ :=
      ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
    obtain ⟨-, hn1, -⟩ := hSide
    obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg.1
    have hdvd' : p ∣ 2 ^ 1 + 1 := by rwa [hn1] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hdvd')
  subst hp3
  exact ggQTwoDNbrSix_signedFrame hcfg.1 hnbr hmark hBBs hRM β
    (fun r hr hrefl => ggQTwoD_join_refl_dTau hcfg e' (by norm_num) hM β hβ hr hrefl)

theorem ggQTwoDNbrSix_signedFrame_base_of_sel
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (e' : Fin 6 ≃ ι) (hM : M = (ggCoxeterMatrixD 6).reindex e')
    (β : Additive ↥Bs ≃+ DVec 6)
    (hβ : ∀ (t : Fin 6) (s : ↥Bs),
      β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) s)) =
        dTau 6 (decide (t.val + 1 = 6)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    p = 3 ∧ Nonempty (GGQTwoDNbrSixFrame B Bs L β) := by
  have hp3 : p = 3 := by
    obtain ⟨K, -, -, lab, -, -, hK, -, -, hSide, hdvd, -⟩ :=
      ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
    obtain ⟨-, hn1, -⟩ := hSide
    obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg.1
    have hdvd' : p ∣ 2 ^ 1 + 1 := by rwa [hn1] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hdvd')
  subst hp3
  exact ggQTwoDNbrSix_signedFrame_base hcfg.1 hmark β
    (fun r hr hrefl => ggQTwoD_join_refl_dTau hcfg e' (by norm_num) hM β hβ hr hrefl)

end CFSG.StandardType.QTwo

end
