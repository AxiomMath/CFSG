module

public import CFSG.LocalAnalysis.StandardType.GGKGPosSpRootKer
public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGRankOneModel
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSp
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourTwins
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGPos
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGStdPosAutWeyl
import CFSG.LocalAnalysis.StandardType.GGStdPosRefl
import CFSG.LocalAnalysis.StandardType.GGStdPosLeviSub
import CFSG.LocalAnalysis.StandardType.GGStdPosLeviCent
import CFSG.LocalAnalysis.StandardType.GGStdPosCardScalar
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical
import CFSG.LocalAnalysis.StandardType.GGStdPosAutHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosLeviHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosIsogCore
import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSpFrame
import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeSp
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Open.StatedAPI
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

section Pipeline

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

private theorem ggStdPos_bruhatData_PSp
    {n f : ℕ} (hrank : 3 ≤ bnRank .PSp n) :
    (ggU .PSp n f).D.divisible = ∅ ∧
      (∃ (nn : Fin (ggU .PSp n f).D.rank → (ggU .PSp n f).K)
        (H : Fin (ggU .PSp n f).D.rank → Subgroup (ggU .PSp n f).K),
        IsCTGroupDatum (coxeterMatrix (ggU .PSp n f).D.isFiniteType).toCoxeterSystem
            (weylAction (ggU .PSp n f).D.isFiniteType) (ggU .PSp n f).D.roots
            (ggU .PSp n f).D.rootGroup nn H ∧
          SteinbergExtras (ggU .PSp n f).D nn H ∧ BruhatExtras (ggU .PSp n f).D H) ∧
      ∃ (x : (Fin (ggU .PSp n f).D.rank → ℤ) → GaloisField 2 f → (ggU .PSp n f).K)
        (C : (Fin (ggU .PSp n f).D.rank → ℤ) → (Fin (ggU .PSp n f).D.rank → ℤ) → ℕ × ℕ → ℤ)
        (O : CommOrder (Steinberg.RootSystem.ofCartan (ggU .PSp n f).D.isFiniteType
          (ggU .PSp n f).D.divisible)),
        ChevalleyExtras (ggU .PSp n f).D (GaloisField 2 f) x C O := by
  have hn2 : 2 ≤ n := by simp only [bnRank] at hrank; omega
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Symplectic.rootDatum n (GaloisField 2 f)).isFiniteType
    (Dv := (Symplectic.rootDatum n (GaloisField 2 f)).divisible) rfl
  exact ⟨rfl, ⟨_, _, Symplectic.isCTGroupDatum n _, Symplectic.steinbergExtras n _,
    GGRootSp.bruhatExtras⟩, _, _, O,
    Steinberg.Sp.chevalleyExtras hn2 O _ (Steinberg.Sp.commutatorFormula O)⟩

private theorem ggRankOneModel_PSp
    {n f : ℕ} (hrank : 3 ≤ bnRank .PSp n) :
    GGRankOneModel (ggU .PSp n f).D (GaloisField 2 f) := by
  have hn2 : 2 ≤ n := by simp only [bnRank] at hrank; omega
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Symplectic.rootDatum n (GaloisField 2 f)).isFiniteType
    (Dv := (Symplectic.rootDatum n (GaloisField 2 f)).divisible) rfl
  exact ⟨Steinberg.Sp.x n (GaloisField 2 f), Steinberg.Sp.commC, O,
    Steinberg.Sp.chevalleyExtras hn2 O _ (Steinberg.Sp.commutatorFormula O),
    fun h hh i => PsiDiag.Symp.ggTorus_conj_x _ (single_mem_roots i) h hh⟩

private theorem ggStdPos_rankOneIn_eq {K : Type*} [Group K] {D : UniversalRootDatum K}
    {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {k : Type*} [Field k] [Finite k]
    [CharP k 2] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hext : SteinbergExtras D nn H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D k x C O)
    (hdiv : D.divisible = ∅) {s : kˣ} (hs : s ≠ 1) {G : Type} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ} {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {ν : GGWeyl D →* K} (hν : GGWeylLift D ν) (w : GGWeyl D) (i : Fin D.rank)
    (hR1 : ∀ β ∈ D.roots, D.rootGroup β ≤ Subgroup.centralizer
        (ggTorusRootKer D p (weylAction D.isFiniteType w (Pi.single i 1))) →
      β = weylAction D.isFiniteType w (Pi.single i 1) ∨
        β = -weylAction D.isFiniteType w (Pi.single i 1))
    (hR2 : ∀ w' : GGWeyl D,
      (∀ h ∈ ggTorusRootKer D p (weylAction D.isFiniteType w (Pi.single i 1)),
        ν w' * h * (ν w')⁻¹ * h⁻¹ ∈ Subgroup.center K) →
      w' = 1 ∨ w' = w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹)
    {r : MulAut ↥Bs} (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) =
      ψ (ν (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹)) * b *
        (ψ (ν (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹)))⁻¹) :
    ggRankOneIn ψ.range Bs r =
      (D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) ⊔
        D.rootGroup (-weylAction D.isFiniteType w (Pi.single i 1))).map ψ := by
  have hyp : ∀ (a : MulAut ↥Bs) (g : G), (∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) →
      ∀ b : G, b ∈ (ggHyperplane Bs a : Set G) ↔ b ∈ Bs ∧ b * g = g * b := by
    intro a g ha b
    constructor
    · rintro ⟨b', hb', rfl⟩
      have h1 : ((a b' : ↥Bs) : G) = b' := congrArg Subtype.val hb'
      rw [ha] at h1
      exact ⟨b'.2, (mul_inv_eq_iff_eq_mul.mp h1).symm⟩
    · rintro ⟨hb, hbg⟩
      refine ⟨⟨b, hb⟩, Subtype.ext ?_, rfl⟩
      show ((a ⟨b, hb⟩ : ↥Bs) : G) = b
      rw [ha, ← hbg, mul_inv_cancel_right]
  have hS := hyp r _ hr
  have hγ : weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots :=
    weylAction_mem_roots (single_mem_roots i) w
  have hsq : ∀ β ∈ D.roots, ∀ z ∈ D.rootGroup β, ψ z ^ 2 ^ 1 = 1 := by
    intro β hβ z hz
    obtain ⟨c, rfl⟩ := ((hE.param β hβ).1 z).mp hz
    rw [pow_one, ← map_pow, sq, ← (hE.param β hβ).2.1, CharTwo.add_self_eq_zero, hE.x_zero hβ,
      map_one]
  rw [ggRankOneIn, ggOTwoPrime]
  refine le_antisymm ((Subgroup.closure_le _).mpr fun y hy => ?_) ?_
  · obtain ⟨⟨hyX, hyC⟩, e, he⟩ := hy
    exact ggStdPosLevi_mem_map hct hext hBU hE hdiv hs ψ hker hBs hC3 hν w i hR1 hR2 hS hyX hyC he
  · rw [Subgroup.map_le_iff_le_comap]
    refine sup_le (fun z hz => Subgroup.mem_comap.mpr (Subgroup.subset_closure ?_))
      (fun z hz => Subgroup.mem_comap.mpr (Subgroup.subset_closure ?_))
    · exact ⟨⟨⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun b hb =>
        ggStdPosLevi_commute hct hext hBU hE ψ hker hBs hν w i ((hS b).mp hb).1
          ((hS b).mp hb).2 z (Subgroup.mem_sup_left hz)⟩, 1, hsq _ hγ z hz⟩
    · exact ⟨⟨⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun b hb =>
        ggStdPosLevi_commute hct hext hBU hE ψ hker hBs hν w i ((hS b).mp hb).1
          ((hS b).mp hb).2 z (Subgroup.mem_sup_right hz)⟩, 1,
        hsq _ (OfCartan.neg_mem_roots _ hγ) z hz⟩

private theorem ggTableBPos_of_tagData
    {t : StatedLieTag} {n f : ℕ}
    {nn : Fin (ggU t n f).D.rank → (ggU t n f).K}
    {H : Fin (ggU t n f).D.rank → Subgroup (ggU t n f).K}
    (hct : IsCTGroupDatum (coxeterMatrix (ggU t n f).D.isFiniteType).toCoxeterSystem
      (weylAction (ggU t n f).D.isFiniteType) (ggU t n f).D.roots (ggU t n f).D.rootGroup nn H)
    (hext : SteinbergExtras (ggU t n f).D nn H) (hBU : BruhatExtras (ggU t n f).D H)
    (hdiv : (ggU t n f).D.divisible = ∅) (h2 : 2 ≤ (ggU t n f).D.rank)
    {x : (Fin (ggU t n f).D.rank → ℤ) → GaloisField 2 f → (ggU t n f).K}
    {C : (Fin (ggU t n f).D.rank → ℤ) → (Fin (ggU t n f).D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (Steinberg.RootSystem.ofCartan (ggU t n f).D.isFiniteType
      (ggU t n f).D.divisible)}
    (hE : ChevalleyExtras (ggU t n f).D (GaloisField 2 f) x C O)
    (hlin : ∀ h ∈ ggTorus (ggU t n f).D, ∀ i : Fin (ggU t n f).D.rank, ∃ χ : GaloisField 2 f,
      ∀ c : GaloisField 2 f, h * x (Pi.single i 1) c * h⁻¹ = x (Pi.single i 1) (χ * c))
    {ν : GGWeyl (ggU t n f).D →* (ggU t n f).K} (hν : GGWeylLift (ggU t n f).D ν)
    {p : ℕ} (hp : p.Prime) {ζ : (GaloisField 2 f)ˣ} (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (hRK : ∀ (u : GGWeyl (ggU t n f).D) (i : Fin (ggU t n f).D.rank),
      (∀ β ∈ (ggU t n f).D.roots, (ggU t n f).D.rootGroup β ≤
          Subgroup.centralizer (ggTorusRootKer (ggU t n f).D p
            (weylAction (ggU t n f).D.isFiniteType u (Pi.single i 1))) →
        β = weylAction (ggU t n f).D.isFiniteType u (Pi.single i 1) ∨
          β = -weylAction (ggU t n f).D.isFiniteType u (Pi.single i 1)) ∧
      ∀ w : GGWeyl (ggU t n f).D, (∀ h ∈ ggTorusRootKer (ggU t n f).D p
          (weylAction (ggU t n f).D.isFiniteType u (Pi.single i 1)),
          ν w * h * (ν w)⁻¹ * h⁻¹ ∈ Subgroup.center (ggU t n f).K) →
        w = 1 ∨ w = u * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * u⁻¹)
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {ψ : (ggU t n f).K →* G}
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = X)
    (hpow : ∀ b ∈ Bs, b ^ p = 1) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hstd : GGKGPosStdPos (ggU t n f).D ψ Bs) :
    GGTableBPos p Bs X t n f ψ := by
  subst hrange
  obtain ⟨ε, hε⟩ := ggStdPos_exists_autWeyl hct hext hBU hE hdiv h2 hζ hζ1 hν
    (fun u i => (hRK u i).2) ψ hker hstd hN hpow hC3
  exact ⟨ε, fun i => ggStdPos_isReflection hE hlin ψ hker hp hstd hpow hν ε hε i,
    fun w i => ggStdPos_rankOneIn_eq hct hext hBU hE hdiv hζ1 ψ hker hstd hC3 hν w i
      (hRK w i).1 (hRK w i).2 (hε _),
    ggStdPos_card_le_pow_rank_mul hct hdiv hE hlin ψ hker hp.ne_zero hstd hpow⟩

private theorem statedLieAdmissible_PSp_three {f : ℕ} (hf : 1 ≤ f) :
    StatedLieAdmissible .PSp 3 2 f :=
  ⟨Nat.prime_two, hf, by norm_num, by simp⟩

@[expose] def GGKGPosLocalHypSp
    (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) (f : ℕ) (ψ : (ggU .PSp 3 f).K →* G) : Prop :=
  (p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ∣ 2 ^ f - 1) ∧
    (ψ.ker ≤ Subgroup.center (ggU .PSp 3 f).K ∧ ψ.range = X) ∧
    (IsElemAbelian p Bs ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) ∧
    (∀ b ∈ Bs, GGPsiInnerDiag (ggU .PSp 3 f).D ψ b) ∧
    p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs

private theorem ggTableBPos_of_stdPos_PSp
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {f : ℕ} {ψ : (ggU .PSp 3 f).K →* G} (hloc : GGKGPosLocalHypSp p Bs X f ψ)
    (hstd : GGKGPosStdPos (ggU .PSp 3 f).D ψ Bs) : GGTableBPos p Bs X .PSp 3 f ψ := by
  obtain ⟨⟨hp, hp2, hf, hpf⟩, ⟨hker, hrange⟩, ⟨hel, hN, hC3⟩, -, -⟩ := hloc
  obtain ⟨ν, hν⟩ := (ggTagFacts_PSp (statedLieAdmissible_PSp_three hf) le_rfl).2.1
  obtain ⟨hdiv, ⟨nn, H, hct, hext, hBU⟩, -⟩ := ggStdPos_bruhatData_PSp (n := 3) (f := f) le_rfl
  obtain ⟨x, C, O, hE, hlin⟩ := ggRankOneModel_PSp (n := 3) (f := f) le_rfl
  obtain ⟨ζ, hζ, hζ1⟩ : ∃ ζ : (GaloisField 2 f)ˣ, ζ ^ p = 1 ∧ ζ ≠ 1 := by
    have : Fact p.Prime := ⟨hp⟩
    have hcard : Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by
      rw [Nat.card_units, GaloisField.card 2 f (by omega)]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 f)ˣ) p (hcard ▸ hpf)
    refine ⟨ζ, hζ ▸ pow_orderOf_eq_one ζ, fun h => hp.one_lt.ne' ?_⟩
    rw [← hζ, h, orderOf_one]
  exact ggTableBPos_of_tagData hct hext hBU hdiv (by show 2 ≤ 3; norm_num) hE hlin hν hp hζ hζ1
    (fun u i => ggRootKerStmt_PSp3 hf hp hp2 hpf ν hν u i) hker hrange hel.2 hN hC3 hstd

private def GGKGPosStdPosSp :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G) (f : ℕ)
    (ψ : (ggU .PSp 3 f).K →* G), GGKGPosLocalHypSp p Bs X f ψ →
      ∃ k : (ggU .PSp 3 f).K,
        GGKGPosStdPos (ggU .PSp 3 f).D (ψ.comp (MulAut.conj k).toMonoidHom) Bs

private theorem ggKGPosLocalHypSp_comp_conj
    {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} {f : ℕ}
    {ψ : (ggU .PSp 3 f).K →* G} (h : GGKGPosLocalHypSp p Bs X f ψ) (k : (ggU .PSp 3 f).K) :
    GGKGPosLocalHypSp p Bs X f (ψ.comp (MulAut.conj k).toMonoidHom) := by
  obtain ⟨hA, ⟨hker, hrange⟩, hC, hdiag, hE⟩ := h
  have hr : (ψ.comp (MulAut.conj k).toMonoidHom).range = X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj k).surjective,
      Subgroup.map_top, hrange]
  have e2 : ∀ w, (ψ.comp (MulAut.conj k).toMonoidHom) w = ψ k * ψ w * (ψ k)⁻¹ := fun w => by
    simp [MonoidHom.comp_apply, MulAut.conj_apply, map_mul, map_inv]
  refine ⟨hA, ⟨fun z hz => ?_, hr⟩, hC, fun b hb => ?_, hE⟩
  · have hc := hker (show ψ (k * z * k⁻¹) = 1 from hz)
    have := Subgroup.Normal.conj_mem inferInstance _ hc k⁻¹
    simpa [mul_assoc] using this
  · obtain ⟨g, hg, hγ⟩ := hdiag b hb
    have ha : ψ k ∈ X := hrange ▸ ⟨k, rfl⟩
    have hbaX : b⁻¹ * ψ k * b ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hC.2.1 (inv_mem hb)) (ψ k)).mp ha
      simpa using this
    refine ⟨b⁻¹ * ψ k * b * g * (ψ k)⁻¹, hr ▸ ?_, fun γ hγ' => ?_⟩
    · exact mul_mem (mul_mem hbaX (hrange ▸ hg)) (inv_mem ha)
    · obtain ⟨h, hh, hz⟩ := hγ γ hγ'
      refine ⟨h, hh, fun z hz' => ?_⟩
      rw [e2, e2]
      calc _ = ψ k * ((b * g)⁻¹ * ψ z * (b * g)) * (ψ k)⁻¹ := by group
        _ = _ := by rw [hz z hz']

private theorem ggKGPosSp_of_stdPos
    (hS2 : GGKGPosStdPosSp) {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs X : Subgroup G} {f : ℕ} {ψ : (ggU .PSp 3 f).K →* G}
    (hloc : GGKGPosLocalHypSp p Bs X f ψ) :
    ∃ ψ' : (ggU .PSp 3 f).K →* G, ψ'.ker ≤ Subgroup.center (ggU .PSp 3 f).K ∧ ψ'.range = X ∧
      GGTableBPos p Bs X .PSp 3 f ψ' := by
  obtain ⟨k, hstd⟩ := hS2 G p Bs X f ψ hloc
  have hloc' := ggKGPosLocalHypSp_comp_conj hloc k
  exact ⟨_, hloc'.2.1.1, hloc'.2.1.2, ggTableBPos_of_stdPos_PSp hloc' hstd⟩

end Pipeline

section Std

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

namespace StdPosSp

private theorem exists_stdPos {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {G : Type} [Group G] [Finite G] {ψ : StatedSp n F →* G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) {Bs : Subgroup G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, GGPsiInnerDiag (Symplectic.rootDatum n F) ψ b)
    (hc : p ^ n * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    ∃ s : StatedSp n F,
      GGKGPosStdPos (Symplectic.rootDatum n F) (ψ.comp (MulAut.conj s).toMonoidHom) Bs := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := F) hpF
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  refine StdPosExc.exists_stdPos_of_toral (r := n)
    (V := (TableBSymp.spTorusGL (m := n) hζp).range.comap (StatedSp n F).subtype)
    (by rw [Symplectic.center_eq, CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot])
    hker (fun x hx => ?_) (fun E hE hcard => ?_) hBs
    (fun b hb => PsiDiag.Symp.exists_mem_centralizer hn ψ hker (hinn b hb)) hc
  ·
    obtain ⟨g, hg⟩ := Subgroup.mem_comap.mp hx
    rw [TableBSymp.spTorusGL_apply] at hg
    have hx' : x = Symplectic.equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal _) :=
      Subtype.ext ((RestSp.coe_equiv_diagonal _).trans hg).symm
    rw [hx']
    exact CompatSp.diagonal_mem_ggTorus _
  ·
    set E' : Subgroup (GL (Fin n ⊕ Fin n) F) := E.map (StatedSp n F).subtype with hE'
    have hESp : E' ≤ LargeEvenSpGroup F n := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hcard' : p ^ n ≤ Nat.card E' := by
      rw [hE', Subgroup.card_map_of_injective (StatedSp n F).subtype_injective]
      exact hcard
    obtain ⟨P, hP, hPE⟩ := TableBSymp.exists_conj_eq_range_spTorusGL hp2
      (TableBSymp.natCast_ne_zero_of_charTwo hp hp2) hζ hζp hESp
      (TableB.isElemAbelian_map hE _) hcard'
    refine ⟨⟨P⁻¹, inv_mem hP⟩, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_comap, ← hPE]
    refine ⟨(e : GL (Fin n ⊕ Fin n) F), ⟨e, he, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]

theorem exists_toralPos {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {G : Type} [Group G] [Finite G] {ψ : StatedSp n F →* G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) {Bs : Subgroup G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, GGPsiInnerDiag (Symplectic.rootDatum n F) ψ b)
    (hc : p ^ n * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    ∃ (s : StatedSp n F) (ζ : Fˣ), orderOf ζ = p ∧
      GGKGPosStdPos (Symplectic.rootDatum n F) (ψ.comp (MulAut.conj s).toMonoidHom) Bs ∧
      ∀ i : Fin n, ∃ b ∈ Bs, ∀ z, b * (ψ.comp (MulAut.conj s).toMonoidHom) z * b⁻¹ =
        (ψ.comp (MulAut.conj s).toMonoidHom)
          (Symplectic.equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (Pi.mulSingle i ζ)) *
            z * (Symplectic.equivStatedSp n F
              (TauCeti.GLSymplecticFin.diagonal (Pi.mulSingle i ζ)))⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := F) hpF
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  set V : Subgroup (StatedSp n F) :=
    (TableBSymp.spTorusGL (m := n) hζp).range.comap (StatedSp n F).subtype with hVdef
  have hVT : V ≤ ggTorus (Symplectic.rootDatum n F) := by
    intro x hx
    obtain ⟨g, hg⟩ := Subgroup.mem_comap.mp hx
    rw [TableBSymp.spTorusGL_apply] at hg
    have hx' : x = Symplectic.equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal _) :=
      Subtype.ext ((RestSp.coe_equiv_diagonal _).trans hg).symm
    rw [hx']
    exact CompatSp.diagonal_mem_ggTorus _
  have hT : ∀ E : Subgroup (StatedSp n F), IsElemAbelian p E → p ^ n ≤ Nat.card E →
      ∃ g : StatedSp n F, E.map (MulAut.conj g).toMonoidHom ≤ V := by
    intro E hE hcard
    set E' : Subgroup (GL (Fin n ⊕ Fin n) F) := E.map (StatedSp n F).subtype with hE'
    have hESp : E' ≤ LargeEvenSpGroup F n := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hcard' : p ^ n ≤ Nat.card E' := by
      rw [hE', Subgroup.card_map_of_injective (StatedSp n F).subtype_injective]
      exact hcard
    obtain ⟨P, hP, hPE⟩ := TableBSymp.exists_conj_eq_range_spTorusGL hp2
      (TableBSymp.natCast_ne_zero_of_charTwo hp hp2) hζ hζp hESp
      (TableB.isElemAbelian_map hE _) hcard'
    refine ⟨⟨P⁻¹, inv_mem hP⟩, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_comap, ← hPE]
    refine ⟨(e : GL (Fin n ⊕ Fin n) F), ⟨e, he, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]
  obtain ⟨s, hs, hsurj⟩ := StdPosExc.exists_toralPos_of_toral_isog (ι := MonoidHom.id _)
    (fun x => ⟨x, rfl⟩)
    (by rw [Symplectic.center_eq, CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot])
    (MonoidHom.ker_id.trans_le bot_le) (V := V) hker hT hBs
    (fun b hb => PsiDiag.Symp.exists_mem_centralizer hn ψ hker (hinn b hb)) hc
  refine ⟨s, ζ, hζ, fun b hb γ _ => ?_, fun i => ?_⟩
  · obtain ⟨v, hv, hbv⟩ := hs b hb
    exact ⟨v, hVT hv, fun z _ => hbv z⟩
  ·
    have hmem : Symplectic.equivStatedSp n F
        (TauCeti.GLSymplecticFin.diagonal (Pi.mulSingle i ζ)) ∈ V := by
      refine Subgroup.mem_comap.mpr ⟨Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p)), ?_⟩
      rw [TableBSymp.spTorusGL_apply, Subgroup.subtype_apply, RestSp.coe_equiv_diagonal]
      congr 2
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
        simpa using TableBSymp.zmodPowHom_natCast hζp 1
      · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]
    have hcard : Nat.card V ≤ p ^ n := by
      calc Nat.card V = Nat.card (V.map (StatedSp n F).subtype) :=
            (Nat.card_congr (V.equivMapOfInjective _ (StatedSp n F).subtype_injective).toEquiv)
        _ ≤ Nat.card (TableBSymp.spTorusGL (m := n) hζp).range :=
            Subgroup.card_le_of_le (Subgroup.map_comap_le _ _)
        _ ≤ Nat.card (Fin n → Multiplicative (ZMod p)) :=
            Nat.card_le_card_of_surjective _
              (TableBSymp.spTorusGL (m := n) hζp).rangeRestrict_surjective
        _ = p ^ n := by simp [Nat.card_eq_fintype_card, ZMod.card]
    obtain ⟨b, hb, v, hv, hbv⟩ := hsurj inferInstance hcard _ hmem
    have hv' : v = Symplectic.equivStatedSp n F
        (TauCeti.GLSymplecticFin.diagonal (Pi.mulSingle i ζ)) := hv
    exact ⟨b, hb, fun z => by rw [hbv z, hv']⟩

end StdPosSp

private theorem ggKGPosStdPosSp_holds :
    GGKGPosStdPosSp := by
  intro G _ _ p Bs X f ψ hloc
  obtain ⟨⟨hp, hp2, hf, hpf⟩, ⟨hker, hX⟩, ⟨hBs, -, -⟩, hinn, hc⟩ := hloc
  subst hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact StdPosSp.exists_stdPos (n := 3) (F := GaloisField 2 f) (by norm_num) hp hp2
    (by rw [GaloisField.card 2 f (by omega)]; exact hpf) hker hBs hinn hc

theorem ggKGPosF4_exists_central_elt {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {X : Subgroup G} (hX : X = L ∨ X = K) :
    ∃ z : G, z ∈ B ∧ z ≠ 1 ∧ z ^ p = 1 ∧
      B ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z := by
  obtain ⟨hp, -, -, -⟩ := hcfg.1.1.1.2.2.2.2.2.1
  rcases hX with hXL | hXK
  · have hS : LargeEvenSStar p B x L := hcfg.1.1.1.2.2.2.2.2.2.1
    rw [hXL]
    exact ⟨x, hS.2.1, hS.2.2.1, hS.1.1.2 x hS.2.1, inf_centralizer_eq_zpowers_of_sstar hp hS⟩
  · have hS : LargeEvenSHat p B y K := hcfg.2.2.2.1
    rw [hXK]
    exact ⟨y, hS.2.1, hS.2.2.1, hS.1.1.2 y hS.2.1, inf_centralizer_eq_zpowers_of_sHat hS⟩

theorem ggKGPosF4_pow_mul_card_le {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {X : Subgroup G} (hX : X = L ∨ X = K) :
    p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs := by
  obtain ⟨hp, -, -, h4⟩ := hcfg.1.1.1.2.2.2.2.2.1
  obtain ⟨z, -, hz1, hzp, hBC⟩ := ggKGPosF4_exists_central_elt hcfg hX
  have := Fact.mk hp
  have hBBs : B ≤ Bs := hcfg.1.1.2.1.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.1.1.2.2.2.2.2.2.1.1.2.1
  set C : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hC
  have hBC' : B ⊓ C = Subgroup.zpowers z := by
    rw [hC, ← inf_assoc, inf_eq_left.mpr hBBs, hBC]
  have h1 : B.relIndex C * p = Nat.card C := by
    have := Subgroup.relIndex_mul_card B C
    rwa [hBC', Nat.card_zpowers, orderOf_eq_prime hzp hz1] at this
  have h2 : B.relIndex Bs * p ^ LargeEvenTwoLocalRank p G = Nat.card Bs := by
    have := Subgroup.relIndex_mul_card B Bs
    rwa [inf_eq_left.mpr hBBs, hBcard] at this
  have hne : B.relIndex Bs ≠ 0 := fun h0 =>
    (Nat.card_pos (α := Bs)).ne' (by rw [← h2, h0, zero_mul])
  have h3 : B.relIndex C ≤ B.relIndex Bs :=
    Subgroup.relIndex_le_of_le_right inf_le_left hne
  have hpm : p ^ 3 * p ^ (LargeEvenTwoLocalRank p G - 4) * p = p ^ LargeEvenTwoLocalRank p G := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  calc p ^ 3 * Nat.card C ≤ p ^ 3 * p ^ (LargeEvenTwoLocalRank p G - 4) * Nat.card C :=
        Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (pow_pos hp.pos _))
    _ = B.relIndex C * (p ^ 3 * p ^ (LargeEvenTwoLocalRank p G - 4) * p) := by rw [← h1]; ring
    _ ≤ B.relIndex Bs * p ^ LargeEvenTwoLocalRank p G := by
        rw [hpm]; exact Nat.mul_le_mul_right _ h3
    _ = Nat.card Bs := h2

theorem ggKGPosLocalHypSp_of_innerDiagOn
    (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs X : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : GGBstar p B Bs) {f : ℕ} (hf : 1 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) (hInn : GGInnerDiagOn Bs X) (hX : GGCentralImage .PSp 3 f X)
    (hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs) :
    ∃ ψ : (ggU .PSp 3 f).K →* G, GGKGPosLocalHypSp p Bs X f ψ := by
  obtain ⟨ψ, hadm, hker, hrange⟩ := hX
  have hrk2 : 2 ≤ (ggU .PSp 3 f).D.rank :=
    two_le_lieUniversal_rank .PSp 3 2 f Nat.prime_two hadm (by decide)
  obtain ⟨-, lab, -, hraw⟩ := hMp G .PSp 3 f ψ hadm hrk2 hker X hrange _ hInn
  obtain ⟨R, _, I, _, -, -, θ, ⟨hBsN, hI⟩, himp⟩ := largeEvenRawDatum_exists hraw
  exact ⟨ψ, ⟨hp, hp2, hf, hpf⟩, ⟨hker, hrange⟩, ⟨hBs.2.1, hBsN, hBs.2.2.2⟩,
    fun b hb => himp b (hBsN hb) (hI b hb), hcard⟩

theorem ggKGPosLocalHypSp_of_f4_mp_of_centralImage
    (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (X : Subgroup G) (hX : X = L ∨ X = K) (himg : GGCentralImage .PSp 3 f X) :
    ∃ ψ : (ggU .PSp 3 f).K →* G, GGKGPosLocalHypSp p Bs X f ψ := by
  obtain ⟨hp, hp2, -, -⟩ := hcfg.1.1.1.2.2.2.2.2.1
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | rfl
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 _ _ hcfg.2.2.2
  exact ggKGPosLocalHypSp_of_innerDiagOn hMp hp hp2 hcfg.1.1.2.1 (by omega) hpf hInn himg
    (ggKGPosF4_pow_mul_card_le hcfg hX)

theorem ggKGPosLocalHypSp_of_f4_mp
    (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (hrow : GGF4QGeFourRowHyp .S1 f L K) :
    ∀ X : Subgroup G, (X = L ∨ X = K) →
      ∃ ψ : (ggU .PSp 3 f).K →* G, GGKGPosLocalHypSp p Bs X f ψ := by
  intro X hX
  have himg : GGCentralImage .PSp 3 f X := by
    rcases hX with rfl | rfl
    · exact hrow.1
    · exact hrow.2
  exact ggKGPosLocalHypSp_of_f4_mp_of_centralImage hMp hcfg hf hpf X hX himg

theorem ggKGPosSp_of_f4_mp
    (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (hrow : GGF4QGeFourRowHyp .S1 f L K) (X : Subgroup G) (hX : X = L ∨ X = K) :
    ∃ ψ' : (ggU .PSp 3 f).K →* G, ψ'.ker ≤ Subgroup.center (ggU .PSp 3 f).K ∧ ψ'.range = X ∧
      GGTableBPos p Bs X .PSp 3 f ψ' := by
  obtain ⟨ψ, hloc⟩ := ggKGPosLocalHypSp_of_f4_mp hMp hcfg hf hpf hrow X hX
  exact ggKGPosSp_of_stdPos ggKGPosStdPosSp_holds hloc

theorem ggKGPosSp_tableBPos_torus
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {f : ℕ} {ψ : (ggU .PSp 3 f).K →* G} (hloc : GGKGPosLocalHypSp p Bs X f ψ) :
    ∃ ψ' : (ggU .PSp 3 f).K →* G, ψ'.ker ≤ Subgroup.center (ggU .PSp 3 f).K ∧ ψ'.range = X ∧
      GGTableBPos p Bs X .PSp 3 f ψ' ∧
      ∀ b ∈ Bs, ∃ t ∈ ggTorus (ggU .PSp 3 f).D, ∀ z, b * ψ' z * b⁻¹ = ψ' (t * z * t⁻¹) := by
  obtain ⟨k, hstd⟩ := ggKGPosStdPosSp_holds G p Bs X f ψ hloc
  have hloc' := ggKGPosLocalHypSp_comp_conj hloc k
  set ψ' : (ggU .PSp 3 f).K →* G := ψ.comp (MulAut.conj k).toMonoidHom with hψ'
  refine ⟨ψ', hloc'.2.1.1, hloc'.2.1.2, ggTableBPos_of_stdPos_PSp hloc' hstd, fun b hb => ?_⟩
  have hinj : Function.Injective ψ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hloc'.2.1.1.trans (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot
      (K := GaloisField 2 f) (n := 3) (by norm_num)).le
  obtain ⟨g, hg, hgc⟩ :=
    PsiDiag.Symp.exists_mem_centralizer (n := 3) (F := GaloisField 2 f) (by norm_num) ψ'
      hloc'.2.1.1 (hloc'.2.2.2.1 b hb)
  obtain ⟨g0, rfl⟩ : ∃ g0 : (ggU .PSp 3 f).K, ψ' g0 = g := hg
  have hact : ∀ z, b * ψ' z * b⁻¹ = ψ' (g0⁻¹ * z * g0⁻¹⁻¹) := by
    intro z
    have h1 := Subgroup.mem_centralizer_iff.mp hgc (ψ' (g0⁻¹ * z * g0)) ⟨_, rfl⟩
    have hz : ψ' z = ψ' g0 * ψ' (g0⁻¹ * z * g0) * (ψ' g0)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; congr 1; group
    rw [inv_inv, hz]
    calc b * (ψ' g0 * ψ' (g0⁻¹ * z * g0) * (ψ' g0)⁻¹) * b⁻¹
        = b * ψ' g0 * ψ' (g0⁻¹ * z * g0) * (b * ψ' g0)⁻¹ := by group
      _ = ψ' (g0⁻¹ * z * g0) * (b * ψ' g0) * (b * ψ' g0)⁻¹ := by rw [← h1]
      _ = ψ' (g0⁻¹ * z * g0) := by group
  refine ⟨g0⁻¹, ?_, hact⟩
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  obtain ⟨h, hh, hhz⟩ := hstd b hb γ hγ
  have hhN : h ∈ Subgroup.normalizer ((ggU .PSp 3 f).D.rootGroup γ : Set (ggU .PSp 3 f).K) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh γ hγ
  have heq : ∀ z ∈ (ggU .PSp 3 f).D.rootGroup γ, g0⁻¹ * z * g0⁻¹⁻¹ = h * z * h⁻¹ :=
    fun z hz => hinj ((hact z).symm.trans (hhz z hz))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hhN ⊢
  refine le_antisymm ?_ ?_ |>.trans hhN
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz, (heq z hz).symm⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz, heq z hz⟩

@[expose] noncomputable def ggSpDiag
    (f : ℕ) (t : Fin 3 → (GaloisField 2 f)ˣ) :
    (ggU .PSp 3 f).K :=
  Symplectic.equivStatedSp 3 (GaloisField 2 f) (TauCeti.GLSymplecticFin.diagonal t)

theorem ggKGPosSp_of_f4_mp_toral
    (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (hrow : GGF4QGeFourRowHyp .S1 f L K) (X : Subgroup G) (hX : X = L ∨ X = K) :
    ∃ (ψ' : (ggU .PSp 3 f).K →* G) (ζ : (GaloisField 2 f)ˣ),
      ψ'.ker ≤ Subgroup.center (ggU .PSp 3 f).K ∧ ψ'.range = X ∧
      GGTableBPos p Bs X .PSp 3 f ψ' ∧ orderOf ζ = p ∧
      ∀ i : Fin 3, ∃ b ∈ Bs, ∀ z, b * ψ' z * b⁻¹ =
        ψ' (ggSpDiag f (Pi.mulSingle i ζ) * z * (ggSpDiag f (Pi.mulSingle i ζ))⁻¹) := by
  obtain ⟨ψ, hloc⟩ := ggKGPosLocalHypSp_of_f4_mp hMp hcfg hf hpf hrow X hX
  obtain ⟨⟨hp, hp2, hf1, hpf'⟩, ⟨hker, hXr⟩, ⟨hBs, -, -⟩, hinn, hc⟩ := id hloc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc' : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs := by
    rw [hXr]; exact hc
  obtain ⟨s, ζ, hζ, hstd, htor⟩ := StdPosSp.exists_toralPos (n := 3) (F := GaloisField 2 f)
    (by norm_num) hp hp2 (by rw [GaloisField.card 2 f (by omega)]; exact hpf') hker hBs hinn hc'
  have hloc' := ggKGPosLocalHypSp_comp_conj hloc s
  exact ⟨_, ζ, hloc'.2.1.1, hloc'.2.1.2, ggTableBPos_of_stdPos_PSp hloc' hstd, hζ, htor⟩

theorem ggF4QGeFourKGPosInput_S1
    (hMp : GGInnerDiagMpInput) : GGF4QGeFourKGPosInput .S1 := by
  intro G _ _ p B Bs x L D J y K hcfg _ f hf hpf hrow
  exact ⟨ggKGPosSp_of_f4_mp hMp hcfg hf hpf hrow L (Or.inl rfl),
    ggKGPosSp_of_f4_mp hMp hcfg hf hpf hrow K (Or.inr rfl)⟩

end Std

end CFSG.StandardType

end
