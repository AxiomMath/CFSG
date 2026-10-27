module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameFusion
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnModel
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Cover
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelQ8Kernel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

private theorem ggc_mem_centralizer_of_conj_action {X : Subgroup G} {b x : G}
    (h : ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  calc y * (x⁻¹ * b) = x⁻¹ * (x * y * x⁻¹) * b := by group
    _ = x⁻¹ * (b * y * b⁻¹) * b := by rw [← h y hy]
    _ = (x⁻¹ * b) * y := by group

private theorem ggc_center_of_conj_eq {X : Subgroup G} {u v : ↥X}
    (h : ∀ y ∈ X, (u : G) * y * (u : G)⁻¹ = (v : G) * y * (v : G)⁻¹) :
    v⁻¹ * u ∈ Subgroup.center ↥X := by
  have hc := ggc_mem_centralizer_of_conj_action (X := X) (b := (u : G)) (x := (v : G)) h
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have := Subgroup.mem_centralizer_iff.mp hc (y : G) y.2
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this

private theorem ggc_exists_pow_eq {X : Type*} [Group X] [Finite X] (N : Subgroup X)
    (hN : N ≤ Subgroup.center X) (hZp : ∀ z ∈ Subgroup.center X, z ^ p = 1 → z = 1)
    {a : X} (ha : a ∈ N) : ∃ z ∈ N, z ^ p = a := by
  have hcop : (Nat.card ↥N).Coprime p := by
    rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hdvd
    have hzp : ((z : X)) ^ p = 1 := by
      have h : ((z : ↥N)) ^ p = 1 := by rw [← hz, pow_orderOf_eq_one]
      simpa using congrArg (fun w : ↥N => ((w : ↥N) : X)) h
    have hz1 : z = 1 := Subtype.ext (hZp _ (hN z.2) hzp)
    rw [hz1, orderOf_one] at hz
    exact (Fact.out : p.Prime).ne_one hz.symm
  obtain ⟨z, hz⟩ := (Nat.Coprime.pow_left_bijective (G := ↥N) hcop).surjective ⟨a, ha⟩
  exact ⟨(z : X), z.2, by simpa using congrArg (fun w : ↥N => ((w : ↥N) : X)) hz⟩

theorem ggEnnAdjointModelCover [Finite G] {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {R : Type} [Group R] (π : ↥X →* R) (hπs : Function.Surjective π)
    (hπk : π.ker ≤ Subgroup.center ↥X)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    ∃ E : Subgroup R, IsElemAbelian p E ∧
      (∀ g : R, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
      (ggGamma X hN).range = E.map (ReflInner.liftConj π hπs hπk) := by
  classical
  have hcenterpow : ∀ (c x : ↥X), c ∈ Subgroup.center ↥X → x ^ p = 1 → (x * c) ^ p = c ^ p := by
    intro c x hc hx
    have hcomm : Commute x c := (Subgroup.mem_center_iff.mp hc) x
    rw [hcomm.mul_pow, hx, one_mul]
  have hmem : ∀ (x : ↥X) (b : G), b ∈ Bs → (∀ y ∈ X, b * y * b⁻¹ = (x : G) * y * (x : G)⁻¹) →
      x ^ p = 1 → (x : G) ∈ Bs := by
    intro x b hb hact hxp
    have hxpG : (x : G) ^ p = 1 := by simpa using congrArg Subtype.val hxp
    refine hSC (x : G) ?_ hxpG
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hb'X : b' ∈ Subgroup.normalizer (X : Set G) := hN hb'
    have hb'xX : b' * (x : G) * b'⁻¹ ∈ X :=
      ((Subgroup.mem_normalizer_iff.mp hb'X) (x : G)).mp x.2
    let u : ↥X := ⟨b' * (x : G) * b'⁻¹, hb'xX⟩
    have hact' : ∀ y ∈ X, (u : G) * y * (u : G)⁻¹ = (x : G) * y * (x : G)⁻¹ := by
      intro y hy
      have hb'iyX : b'⁻¹ * y * b' ∈ X := by
        simpa using ((Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (X : Set G)).inv_mem hb'X)) y).mp hy
      calc (u : G) * y * (u : G)⁻¹
          = b' * ((x : G) * (b'⁻¹ * y * b') * (x : G)⁻¹) * b'⁻¹ := by
            change b' * (x : G) * b'⁻¹ * y * (b' * (x : G) * b'⁻¹)⁻¹ = _
            group
        _ = b' * (b * (b'⁻¹ * y * b') * b⁻¹) * b'⁻¹ := by rw [hact _ hb'iyX]
        _ = (b' * b * b'⁻¹) * y * (b' * b * b'⁻¹)⁻¹ := by group
        _ = b * y * b⁻¹ := by
              rw [CFSG.Open.IsElemAbelian.comm hBs hb' hb]
              group
        _ = (x : G) * y * (x : G)⁻¹ := hact y hy
    have hc : x⁻¹ * u ∈ Subgroup.center ↥X := ggc_center_of_conj_eq hact'
    have hup : u ^ p = 1 := by
      apply Subtype.ext
      change (b' * (x : G) * b'⁻¹) ^ p = 1
      rw [conj_pow, hxpG]
      group
    have hu : u = x * (x⁻¹ * u) := by group
    have hcp : (x⁻¹ * u) ^ p = 1 := by
      have := hcenterpow (x⁻¹ * u) x hc hxp
      rw [← hu, hup] at this
      exact this.symm
    have hc1 : x⁻¹ * u = 1 := hZp _ hc hcp
    have hux : u = x := by
      calc u = x * (x⁻¹ * u) := hu
        _ = x := by rw [hc1, mul_one]
    have hux' : b' * (x : G) * b'⁻¹ = (x : G) := congrArg Subtype.val hux
    calc b' * (x : G) = (b' * (x : G) * b'⁻¹) * b' := by group
      _ = (x : G) * b' := by rw [hux']
  have hlift : ∀ b ∈ Bs, ∃ x : ↥X, (x : G) ∈ Bs ∧
      ∀ y ∈ X, b * y * b⁻¹ = (x : G) * y * (x : G)⁻¹ := by
    intro b hb
    obtain ⟨x₀, hx₀X, hx₀⟩ := hinner b hb
    let x₀' : ↥X := ⟨x₀, hx₀X⟩
    have hcb : x₀⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
      ggc_mem_centralizer_of_conj_action hx₀
    have hxc : Commute x₀ (x₀⁻¹ * b) := Subgroup.mem_centralizer_iff.mp hcb x₀ hx₀X
    have hbp : b ^ p = 1 := hBs.2 b hb
    have hpow : x₀ ^ p * (x₀⁻¹ * b) ^ p = 1 := by
      rw [← hxc.mul_pow, show x₀ * (x₀⁻¹ * b) = b by group, hbp]
    have hx0pC : x₀ ^ p ∈ Subgroup.centralizer (X : Set G) := by
      rw [mul_eq_one_iff_eq_inv.mp hpow]
      exact (Subgroup.centralizer (X : Set G)).inv_mem ((Subgroup.centralizer (X : Set G)).pow_mem hcb p)
    have hx0pZ : x₀' ^ p ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hx0pC (y : G) y.2
      simpa [Subgroup.coe_mul, Subgroup.coe_pow] using this
    obtain ⟨z, hzZ, hz⟩ := ggc_exists_pow_eq (p := p) (Subgroup.center ↥X) le_rfl hZp
      (a := (x₀' ^ p)⁻¹) ((Subgroup.center ↥X).inv_mem hx0pZ)
    have hxz : Commute x₀' z := (Subgroup.mem_center_iff.mp hzZ) x₀'
    have hxp : (x₀' * z) ^ p = 1 := by
      rw [hxz.mul_pow, hz, mul_inv_cancel]
    have hact : ∀ y ∈ X, b * y * b⁻¹ = ((x₀' * z : ↥X) : G) * y * ((x₀' * z : ↥X) : G)⁻¹ := by
      intro y hy
      rw [hx₀ y hy]
      have hzy : (z : G) * y = y * (z : G) := by
        have := (Subgroup.mem_center_iff.mp hzZ) ⟨y, hy⟩
        simpa [Subgroup.coe_mul] using (congrArg Subtype.val this).symm
      simp only [Subgroup.coe_mul]
      calc x₀ * y * x₀⁻¹ = x₀ * ((z : G) * y * (z : G)⁻¹) * x₀⁻¹ := by
            rw [hzy]; group
        _ = x₀ * (z : G) * y * ((x₀ * (z : G))⁻¹) := by group
    exact ⟨x₀' * z, hmem _ b hb hact hxp, hact⟩
  let Λ := ReflInner.liftConj π hπs hπk
  let E : Subgroup R := (Bs.subgroupOf X).map π
  have hArange : (ggGamma X hN).range = E.map Λ := by
    apply le_antisymm
    · rintro _ ⟨b, rfl⟩
      obtain ⟨x, hxBs, hxact⟩ := hlift b b.2
      have hconj : ggGamma X hN b = MulAut.conj x := by
        ext y
        exact hxact y y.2
      refine Subgroup.mem_map.mpr ⟨π x,
        Subgroup.mem_map_of_mem π (show x ∈ Bs.subgroupOf X from hxBs), ?_⟩
      rw [ReflInner.liftConj_eq hπs hπk rfl]
      exact hconj.symm
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hc
      have hxBs : (x : G) ∈ Bs := hx
      refine ⟨⟨(x : G), hxBs⟩, ?_⟩
      rw [ReflInner.liftConj_eq hπs hπk rfl]
      ext y
      rfl
  have hEel : IsElemAbelian p E :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hBs X) π
  have hEsc : ∀ g : R, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E := by
    intro g hgc hgp
    obtain ⟨z₀, hz₀⟩ := hπs g
    have hz₀ker : (z₀ ^ p)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_inv, map_pow, hz₀, hgp, inv_one]
    obtain ⟨w, hwker, hw⟩ := ggc_exists_pow_eq (p := p) π.ker hπk hZp (a := (z₀ ^ p)⁻¹) hz₀ker
    have hwπ : π w = 1 := MonoidHom.mem_ker.mp hwker
    let z : ↥X := z₀ * w
    have hzg : π z = g := by
      change π (z₀ * w) = g
      rw [map_mul, hz₀, hwπ, mul_one]
    have hzp : z ^ p = 1 := by
      have hcomm : Commute z₀ w := (Subgroup.mem_center_iff.mp (hπk hwker)) z₀
      change (z₀ * w) ^ p = 1
      rw [hcomm.mul_pow, hw, mul_inv_cancel]
    have hzpG : (z : G) ^ p = 1 := by simpa using congrArg Subtype.val hzp
    have hzC : (z : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨x, hxBs, hxact⟩ := hlift b hb
      have hxpG : (x : G) ^ p = 1 := hBs.2 (x : G) hxBs
      have hxp : x ^ p = 1 := Subtype.ext (by simpa using hxpG)
      have hEx : π x ∈ E := Subgroup.mem_map_of_mem π (show x ∈ Bs.subgroupOf X from hxBs)
      have hπt : π (x⁻¹ * (z * x * z⁻¹)) = 1 := by
        have h := hgc (π x) hEx
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hzg]
        have h' : g * π x * g⁻¹ = π x := by rw [h]; group
        rw [h', inv_mul_cancel]
      have ht : x⁻¹ * (z * x * z⁻¹) ∈ Subgroup.center ↥X := hπk (MonoidHom.mem_ker.mpr hπt)
      have hcp : (x⁻¹ * (z * x * z⁻¹)) ^ p = 1 := by
        have h1 : (z * x * z⁻¹) ^ p = 1 := by rw [conj_pow, hxp]; group
        have h2 := hcenterpow (x⁻¹ * (z * x * z⁻¹)) x ht hxp
        rw [show x * (x⁻¹ * (z * x * z⁻¹)) = z * x * z⁻¹ by group, h1] at h2
        exact h2.symm
      have ht1 : x⁻¹ * (z * x * z⁻¹) = 1 := hZp _ ht hcp
      have hzx : z * x = x * z := by
        have : z * x * z⁻¹ = x := by
          calc z * x * z⁻¹ = x * (x⁻¹ * (z * x * z⁻¹)) := by group
            _ = x := by rw [ht1, mul_one]
        calc z * x = (z * x * z⁻¹) * z := by group
          _ = x * z := by rw [this]
      have hzxG : (z : G) * (x : G) = (x : G) * (z : G) := congrArg Subtype.val hzx
      have hcb : (x : G)⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
        ggc_mem_centralizer_of_conj_action hxact
      have hzcb : (z : G) * ((x : G)⁻¹ * b) = ((x : G)⁻¹ * b) * (z : G) :=
        Subgroup.mem_centralizer_iff.mp hcb (z : G) z.2
      calc b * (z : G) = (x : G) * ((x : G)⁻¹ * b) * (z : G) := by group
        _ = (x : G) * ((z : G) * ((x : G)⁻¹ * b)) := by rw [mul_assoc, ← hzcb]
        _ = ((x : G) * (z : G)) * ((x : G)⁻¹ * b) := by group
        _ = ((z : G) * (x : G)) * ((x : G)⁻¹ * b) := by rw [hzxG]
        _ = (z : G) * b := by group
    have hzBs : (z : G) ∈ Bs := hSC (z : G) hzC hzpG
    exact Subgroup.mem_map.mpr ⟨z, show z ∈ Bs.subgroupOf X from hzBs, hzg⟩
  exact ⟨E, hEel, hEsc, hArange⟩

end Generic

theorem ggTwE6Split_coverModel_K
      (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp5 : 5 < p) (hpn : p ∣ 2 ^ n - 1) (h3 : 3 ∣ 2 ^ n + 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (F : Type) (_ : Field F) (_ : Finite F)
      (σ : F →+* F) (_ : Nat.card F = (2 ^ n) ^ 2) (_ : ∀ c, σ c = c ^ 2 ^ n)
      (ζ : Fˣ) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : F) = ζ)
      (π : ↥K →* ↥(graphFixedRootGroup TwistTag.E6 F σ)) (hπs : Function.Surjective π)
      (hπk : π.ker ≤ Subgroup.center ↥K),
      Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 F σ) = ⊥ ∧
      (∀ z ∈ Subgroup.center ↥K, z ^ p = 1 → z = 1) ∧ orderOf ζ = p ∧
      (ggGamma K hN).range =
        (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range.map (ReflInner.liftConj π hπs hπk) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hn : 1 ≤ n := hΛ.1
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn' : n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl
    · have : p ∣ 1 := by simpa using hpn
      exact hp.ne_one (Nat.dvd_one.mp this)
    · have h3p : p ∣ 3 := by simpa using hpn
      have := Nat.le_of_dvd (by norm_num) h3p
      omega
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hinnerDiag : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨hKperf, lab, _hlab, hraw⟩ :=
    ggInnerDiagOn_relabel hRig hinnerDiag hΛ hK
  let Q : LargeEvenRawCont := fun R x I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R,
        (fun lab' x x_1 I x_2 (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) =>
          lab' = { tag := LargeEvenLieTag.twE6, rank := 0, n := n } ∧
            Bs ≤ Subgroup.normalizer (K : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
        lab R x I F θ
  have hraw_canon : LargeEvenRawDatum lab Q := (largeEvenRawDatum_legacy lab Q).mpr hraw
  obtain ⟨R, _instR, I, F_set, hQ⟩ := largeEvenRawDatum_exists (Q := Q) hraw_canon
  obtain ⟨_hSimple0, _hNA0, _θ0, hP0⟩ := hQ
  obtain ⟨hlabeq, _hNmark0, _hBsI0⟩ := hP0
  have hlab_eq : lab = ⟨.twE6, 0, n⟩ := hlabeq
  obtain ⟨F, _instF, _finF, hFcard, hQF⟩ := (hlab_eq ▸ hraw)
  obtain ⟨_hSimple, _hNA, θ, hP⟩ := hQF
  obtain ⟨_hlabeq, hNmark, hBsI⟩ := hP
  have hOut : GGOutdiagPrime p (TwE6Delta.RecipeR F n) (TwE6Delta.RecipeI F n) :=
    TwE6Delta.ggOutdiagPrime_twE6 hn hFcard hp hp3
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ l ∈ K, b * l * b⁻¹ = x * l * x⁻¹ := by
    refine F4AutRefl.exists_conj_of_inn hKperf θ
      (I := Set.range (MulAut.conj : TwE6Delta.RecipeR F n →* MulAut (TwE6Delta.RecipeR F n)))
      Set.Subset.rfl hNmark ?_
    intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hBsI b hb
    refine ⟨φ, hOut φ hφI ?_, hφ⟩
    rw [eq_ggLAut_of_induces K θ (hNmark hb) hφ, ← map_pow]
    have hb1 : (⟨b⁻¹, inv_mem (hNmark hb)⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := by
      apply Subtype.ext
      simp [inv_pow, hBs.2 b hb]
    rw [hb1, map_one]
  haveI : CharP F 2 :=
    charP_two_of_card (K := F) (m := 2 * n) (by rw [hFcard, ← pow_mul, mul_comm])
  let σ : F →+* F := iterateFrobenius F 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hpF : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hFcard]
    have h1 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
    exact hpn.trans h1
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpF
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζσ : σ (ζ : F) = ζ := by
    obtain ⟨k, hk⟩ := id hpn
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    have hq : 2 ^ n = p * k + 1 := by omega
    rw [hσ, ← Units.val_pow_eq_pow_val, hq, pow_add, pow_mul, hζ, one_pow, one_mul, pow_one]
  obtain ⟨e2⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hFcard σ hσ
  let ψ : ↥K →* TwE6Delta.RecipeR F n :=
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* TwE6Delta.RecipeR F n).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center ↥K))
  have hψs : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = Subgroup.center ↥K := by
    ext z
    change θ (QuotientGroup.mk' (Subgroup.center ↥K) z) = 1 ↔ _
    rw [map_eq_one_iff _ θ.injective]
    exact QuotientGroup.eq_one_iff z
  let π₁ : ↥K →* ↥(graphFixedRootGroup TwistTag.E6 F σ) := e2.toMonoidHom.comp ψ
  have hπ₁s : Function.Surjective π₁ := e2.surjective.comp hψs
  have hπ₁k : π₁.ker ≤ Subgroup.center ↥K := by
    intro z hz
    have : ψ z = 1 := by
      have h1 : e2 (ψ z) = 1 := hz
      exact (map_eq_one_iff _ e2.injective).mp h1
    exact hψker ▸ (MonoidHom.mem_ker.mpr this)
  have hdvd3 : Nat.card ↥(Subgroup.center ↥K) ∣ 3 := by
    have := TwE6Delta.card_ker_dvd_three_q8 hn3 hFcard hψs hψker.le hKperf
    rwa [hψker] at this
  have hZp : ∀ z ∈ Subgroup.center ↥K, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have h2 : orderOf z ∣ 3 :=
      (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hz).trans hdvd3
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr hp3
    have h3' : orderOf z ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [hcop] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3')
  have hZR : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 F σ) = ⊥ := by
    have hZ0 : Subgroup.center (TwE6Delta.RecipeR F n) = ⊥ := by
      haveI : IsSimpleGroup (TwE6Delta.RecipeR F n) := _hSimple
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (TwE6Delta.RecipeR F n)) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := _hNA
        have ha : a ∈ Subgroup.center (TwE6Delta.RecipeR F n) := by rw [h]; exact Subgroup.mem_top a
        exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
    have h1 : (Subgroup.center (TwE6Delta.RecipeR F n)).map (e2 : _ →* _) =
        Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 F σ) :=
      Subgroup.map_center_eq e2
    rw [← h1, hZ0, Subgroup.map_bot]
  obtain ⟨E', hE'el, hE'sc, hγ⟩ :=
    ggEnnAdjointModelCover hBs hSC hZp π₁ hπ₁s hπ₁k hinner hNmark
  have hT : SylowTorus ↥(graphFixedRootGroup TwistTag.E6 F σ) p 4 :=
    (sylowTorus_recipeR_split hn hFcard hp (le_of_lt hp5) hpn).of_mulEquiv e2
  set ι := ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ with hιdef
  have hιinj : Function.Injective ι := ExcFrames.twE6SplitFrameHom_injective σ (le_of_lt hp5) hζo hζ hζσ
  have hEl : IsElemAbelian p ι.range := by
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := b.2
      change (a : ↥(graphFixedRootGroup TwistTag.E6 F σ)) * b = b * a
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨u, rfl⟩ := hx
      rw [← map_pow, ← ofAdd_toAdd u, ← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero, ofAdd_zero,
        map_one]
  have hcard : Nat.card ι.range = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin Tag.F4.rank → ZMod p) ≃ _),
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  obtain ⟨c, hc⟩ := exists_conj_eq_of_selfCentralizing_of_sylowTorus hp hT hEl hcard hE'el hE'sc
  let π : ↥K →* ↥(graphFixedRootGroup TwistTag.E6 F σ) := (MulAut.conj c⁻¹).toMonoidHom.comp π₁
  have hπs : Function.Surjective π := (MulAut.conj c⁻¹).surjective.comp hπ₁s
  have hπk : π.ker ≤ Subgroup.center ↥K := by
    intro z hz
    apply hπ₁k
    have h1 : (MulAut.conj c⁻¹) (π₁ z) = 1 := hz
    exact (map_eq_one_iff _ (MulAut.conj c⁻¹).injective).mp h1
  refine ⟨hNmark, F, inferInstance, inferInstance, σ, hFcard, hσ, ζ, hζ, hζσ, π, hπs, hπk, hZR,
    hZp, hζo, ?_⟩
  have hΛ' : ReflInner.liftConj π hπs hπk =
      (ReflInner.liftConj π₁ hπ₁s hπ₁k).comp (MulAut.conj c).toMonoidHom := by
    refine MonoidHom.ext fun r => ?_
    obtain ⟨z, rfl⟩ := hπs r
    rw [ReflInner.liftConj_eq hπs hπk rfl]
    have : π₁ z = c * π z * c⁻¹ := by
      change π₁ z = c * ((MulAut.conj c⁻¹) (π₁ z)) * c⁻¹
      rw [MulAut.conj_apply]
      group
    change MulAut.conj z = ReflInner.liftConj π₁ hπ₁s hπ₁k ((MulAut.conj c) (π z))
    rw [MulAut.conj_apply, ← this, ReflInner.liftConj_eq hπ₁s hπ₁k rfl]
  rw [hΛ', ← Subgroup.map_map, ← hc]
  exact hγ

end CFSG.StandardType

end
