module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJNormOfFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJReflOfCore
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGRankOneModel
import CFSG.LocalAnalysis.StandardType.GGKGPosGenCox
import CFSG.LocalAnalysis.StandardType.GGSecFiveRk1OfKGPos
import CFSG.LocalAnalysis.StandardType.GGCoxReflConv
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.Quasithin.Vol2.Ch10SecHeLMain
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.Quasithin.Background.A3Structure312Facts
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B5FinOut
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.E2Hyp
import CFSG.Quasithin.Background.E2SolvTwo
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.Quasithin.Vol2.Ch12Sec2Statements
import CFSG.Quasithin.Vol2.Ch1Faithful
import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Steinberg

section Pure

theorem s2jn_pow_induced {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {r : MulAut ↥Bs} {j : G}
    (hj : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = j * b * j⁻¹) (k : ℕ) :
    ∀ b : ↥Bs, (((r ^ k) b : ↥Bs) : G) = j ^ k * b * (j ^ k)⁻¹ := by
  induction k with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    rw [pow_succ', MulAut.mul_apply, hj, ih, pow_succ']
    group

theorem s2jn_ggRankOneIn_le_of_simple {G : Type} [Group G] [Finite G] {Bs X J D : Subgroup G} {r₀ : MulAut ↥Bs}
    (hr₀J : r₀ ∈ ggAutomizer J Bs) (hr₀2 : r₀ ^ 2 = 1) (hr₀1 : r₀ ≠ 1) (hJX : J ≤ X)
    (hDB : D ≤ Bs) (hJD : J ≤ Subgroup.centralizer (D : Set G))
    (hDJ : ∀ c ∈ Subgroup.centralizer (D : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hsimp : ∀ N : Subgroup G, N ≤ ggRankOneIn X Bs r₀ → N ≠ ⊥ →
      (∀ a ∈ ggRankOneIn X Bs r₀, ∀ b ∈ N, a * b * a⁻¹ ∈ N) → ggRankOneIn X Bs r₀ ≤ N) :
    ggRankOneIn X Bs r₀ ≤ J := by
  obtain ⟨j, hjJ, -, hj⟩ := mem_ggAutomizer_iff.mp hr₀J
  have hjH : j ∈ Subgroup.centralizer (ggHyperplane Bs r₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : r₀ b = b := hb
    have h1 := hj b
    rw [hb'] at h1
    change (b : G) * j = j * b
    calc (b : G) * j = (j * b * j⁻¹) * j := by rw [← h1]
      _ = j * b := by group
  have hDH : D ≤ ggHyperplane Bs r₀ := by
    intro d hd
    refine ⟨⟨d, hDB hd⟩, ?_, rfl⟩
    change r₀ ⟨d, hDB hd⟩ = ⟨d, hDB hd⟩
    apply Subtype.ext
    rw [hj]
    have hjd := (Subgroup.mem_centralizer_iff.mp (hJD hjJ)) d hd
    change j * d * j⁻¹ = d
    rw [← hjd]; group
  have hRD : ggRankOneIn X Bs r₀ ≤ Subgroup.centralizer (D : Set G) :=
    (ggOTwoPrime_le _).trans (inf_le_right.trans (Subgroup.centralizer_le hDH))
  obtain ⟨e, m, hm2, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (orderOf_pos j).ne' 2 (by norm_num)
  have hmodd : m % 2 = 1 := Nat.two_dvd_ne_zero.mp hm2
  have hj2 : (j ^ m) ^ (2 ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hj2ne : j ^ m ≠ 1 := by
    intro h1
    apply hr₀1
    have hrm : r₀ ^ m = 1 := by
      ext b
      rw [s2jn_pow_induced hj m b, h1]
      simp
    have : r₀ ^ m = r₀ := by
      rw [← Nat.div_add_mod m 2, hmodd, pow_add, pow_mul, hr₀2, one_pow, one_mul, pow_one]
    rw [← this, hrm]
  have hj2R : j ^ m ∈ ggRankOneIn X Bs r₀ :=
    Subgroup.subset_closure ⟨⟨hJX (J.pow_mem hjJ m), Subgroup.pow_mem _ hjH m⟩, e, hj2⟩
  refine (hsimp (ggRankOneIn X Bs r₀ ⊓ J) inf_le_left ?_ ?_).trans inf_le_right
  · intro hbot
    apply hj2ne
    have : j ^ m ∈ ggRankOneIn X Bs r₀ ⊓ J := ⟨hj2R, J.pow_mem hjJ m⟩
    rw [hbot] at this
    exact this
  · rintro a ha b ⟨hbR, hbJ⟩
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hbR) (Subgroup.inv_mem _ ha),
      hDJ a (hRD ha) b hbJ⟩

end Pure

section Inputs

@[expose] def GGSecFiveSplitNbrGuardInput'
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      GGSecFiveRegionGuard p L Bs 𝒦 →
      ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
        ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 → GGSplitLie p K'

end Inputs

section Table

theorem s2jn_refl_conj_of_tableBPos {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f)
    (ε : (coxeterMatrix (ggU t n f).D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs))
    (hεrefl : ∀ i, GGIsReflection p
      ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) :
        MulAut ↥Bs))
    {r r₀ : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r)
    (hr₀ : r₀ ∈ ggCoxRefl (coxeterMatrix (ggU t n f).D.isFiniteType) ε) :
    ∃ a ∈ ggAutomizer X Bs, r = a * r₀ * a⁻¹ := by
  obtain ⟨hW, h3⟩ := ggTag_weylMatrix ht hadm
  have hpres : GGCoxeterPres p (ggAutomizer X Bs) _ ε := ⟨hW, hεrefl⟩
  have hrC : r ∈ ggCoxRefl _ ε :=
    ggCoxRefl_of_isReflection hp hodd hBs hpres h3
      (ggNoTransvection_of_le_automizer hNT (ggAutomizer_le_top X Bs)) hrA hr
  exact ggCoxRefl_conj_of_connected ε (ggSimplyLacedConnected_of_weyl hW h3) hr₀ hrC

theorem s2jn_exists_sl2_range_rankOne
    {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] (hM : GGRankOneModel D k) (i : Fin D.rank) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective φ ∧
      φ.range = CFSG.LieType.CurtisTits.rankOne D.rootGroup i := by
  unfold GGRankOneModel at hM
  obtain ⟨x, C, O, hE, -⟩ := hM
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  refine ⟨φ, hφinj, ?_⟩
  apply le_antisymm
  · rintro y ⟨M, rfl⟩
    have hM' : M ∈ Subgroup.closure
        (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
          Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) := by
      rw [CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top]
      exact Subgroup.mem_top M
    have hs : (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
        Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) ⊆
        (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ := by
      rintro x (hx | hx)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Upper c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφu c]
        exact Subgroup.mem_sup_left
          (((hE.param (Pi.single i 1) (single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Lower c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφl c]
        exact Subgroup.mem_sup_right
          (((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
    exact Subgroup.mem_comap.mp
      (Subgroup.mem_closure.mp hM'
        ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ) hs)
  · change D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ φ.range
    apply sup_le
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Upper c, by rw [hφu c, hc]⟩
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Lower c, by rw [hφl c, hc]⟩

theorem s2jn_range_simple {G : Type} [Group G] [Finite G]
    {S : Type*} [Group S] [IsSimpleGroup S] (θ : S →* G)
    (hθ : Function.Injective θ) (N : Subgroup G) (hN : N ≤ θ.range) (hN1 : N ≠ ⊥)
    (hnorm : ∀ a ∈ θ.range, ∀ b ∈ N, a * b * a⁻¹ ∈ N) : θ.range ≤ N := by
  haveI hN' : (N.comap θ).Normal := ⟨fun n hn s => by
    change θ (s * n * s⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ ⟨s, rfl⟩ _ hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap θ) with h | h
  · exfalso
    apply hN1
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨s, rfl⟩ := hN hb
    have : s ∈ N.comap θ := hb
    rw [h] at this
    rw [Subgroup.mem_bot] at this ⊢
    rw [this, map_one]
  · rintro _ ⟨s, rfl⟩
    have : s ∈ N.comap θ := by rw [h]; trivial
    exact this

theorem s2jn_exists_sl2_of_tableBPos {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3t : 3 ≤ bnRank t n)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hpos : GGTableBPos p Bs X t n f ψ)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    ∃ θ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* G,
      Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r := by
  unfold GGTableBPos at hpos
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  have hrk : 2 ≤ (ggU t n f).D.rank := two_le_lieUniversal_rank t n 2 f Nat.prime_two hadm h3t
  let i₁ : Fin (ggU t n f).D.rank := ⟨0, by omega⟩
  let r₁ : MulAut ↥Bs :=
    ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i₁) : ↥(ggAutomizer X Bs)) :
      MulAut ↥Bs)
  have hr₁C : r₁ ∈ ggCoxRefl (coxeterMatrix (ggU t n f).D.isFiniteType) ε :=
    ⟨1, i₁, by simp [r₁]⟩
  obtain ⟨a, haA, hra⟩ := s2jn_refl_conj_of_tableBPos hp hodd hBs hNT ht hadm ε hεrefl hrA hr hr₁C
  obtain ⟨g, hgX, -, hga⟩ := mem_ggAutomizer_iff.mp haA
  have hX : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgX)
  have hmap : (ggRankOneIn X Bs r₁).map (MulAut.conj g).toMonoidHom = ggRankOneIn X Bs r := by
    rw [ggRankOneIn_map_conj hga r₁, hX, hra]
  have hlevi₁ : ggRankOneIn X Bs r₁ = (ggRootLevi (ggU t n f).D (Pi.single i₁ 1)).map ψ := by
    have h := hεlevi 1 i₁
    simp only [one_mul, inv_one, mul_one, map_one, Module.End.one_apply] at h
    exact h
  have hMod : GGRankOneModel (ggU t n f).D (GaloisField 2 f) := ggRankOneModel_of_tag ht hadm h3t
  obtain ⟨φ, hφinj, hφrange⟩ := s2jn_exists_sl2_range_rankOne hMod i₁
  let θ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* G :=
    (MulAut.conj g).toMonoidHom.comp (ψ.comp φ)
  have hψφinj : Function.Injective (ψ.comp φ) :=
    PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker
  have hθinj : Function.Injective θ := (MulAut.conj g).injective.comp hψφinj
  have hθrange : θ.range = ggRankOneIn X Bs r := by
    change ((MulAut.conj g).toMonoidHom.comp (ψ.comp φ)).range = ggRankOneIn X Bs r
    rw [← MonoidHom.map_range (MulAut.conj g).toMonoidHom (ψ.comp φ), ← MonoidHom.map_range ψ φ,
      hφrange]
    have hlevi' : (CFSG.LieType.CurtisTits.rankOne (ggU t n f).D.rootGroup i₁).map ψ =
        (ggRootLevi (ggU t n f).D (Pi.single i₁ 1)).map ψ := rfl
    rw [hlevi', ← hlevi₁, hmap]
  exact ⟨θ, hθinj, hθrange⟩

theorem s2jn_rankOne_simple_of_tableBPos {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3t : 3 ≤ bnRank t n)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hpf : p ∣ 2 ^ f - 1)
    (hpos : GGTableBPos p Bs X t n f ψ)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    ∀ N : Subgroup G, N ≤ ggRankOneIn X Bs r → N ≠ ⊥ →
      (∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ N, a * b * a⁻¹ ∈ N) → ggRankOneIn X Bs r ≤ N := by
  obtain ⟨θ, hθinj, hθrange⟩ :=
    s2jn_exists_sl2_of_tableBPos hp hodd hBs hNT ht hadm h3t hker hpos hrA hr
  have hf1 : 1 ≤ f := hadm.2.1
  have hf2 : 2 ≤ f := by
    rcases Nat.lt_or_ge f 2 with h | h
    · have hf : f = 1 := by omega
      subst hf
      exact absurd (Nat.le_of_dvd (by norm_num) hpf) (by have := hp.two_le; omega)
    · exact h
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    CFSG.Quasithin.Vol2.Ch10.HeL.sl2_isSimpleGroup h4
  intro N hN hN1 hnorm
  rw [← hθrange] at hN hnorm ⊢
  exact s2jn_range_simple θ hθinj N hN hN1 hnorm

theorem s2jn_le_iSup_conj_of_tableBPos {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3t : 3 ≤ bnRank t n) (hrange : ψ.range = X)
    (hpos : GGTableBPos p Bs X t n f ψ)
    {r₀ : MulAut ↥Bs} (hr₀A : r₀ ∈ ggAutomizer X Bs) (hr₀ : GGIsReflection p r₀)
    (hanchor : ggRankOneIn X Bs r₀ ≤ J) :
    X ≤ ⨆ (g : G) (_ : g ∈ X) (_ : ∃ φ : MulAut ↥Bs, g ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹), J.map (MulAut.conj g).toMonoidHom := by
  unfold GGTableBPos at hpos
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  have hdiv : (ggU t n f).D.divisible = ∅ := s2jn_ggU_divisible_eq_empty ht
  have hgen : ggSub (ggU t n f).D (ggU t n f).D.roots = ⊤ :=
    (ggTagFacts_of_admissible hadm h3t).2.2.1
  conv_lhs => rw [← hrange]
  rw [MonoidHom.range_eq_map, ← hgen, ggSub]
  simp only [Subgroup.map_iSup]
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨w, i, rfl⟩ := s2jn_exists_weylAction_of_mem_roots (ggU t n f).D hdiv hγ
  have hlevi := hεlevi w i
  simp only [ggRootLevi] at hlevi
  refine le_trans (Subgroup.map_mono (le_sup_left : (ggU t n f).D.rootGroup
    (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) ≤
    (ggU t n f).D.rootGroup (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) ⊔
    (ggU t n f).D.rootGroup (-(weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))))) ?_
  rw [← hlevi]
  set r : MulAut ↥Bs :=
    ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
      ↥(ggAutomizer X Bs)) : MulAut ↥Bs) with hr_def
  have hrC : r ∈ ggCoxRefl (coxeterMatrix (ggU t n f).D.isFiniteType) ε := ⟨w, i, rfl⟩
  obtain ⟨hW, h3⟩ := ggTag_weylMatrix ht hadm
  have hpres : GGCoxeterPres p (ggAutomizer X Bs) _ ε := ⟨hW, hεrefl⟩
  have hr₀C : r₀ ∈ ggCoxRefl _ ε :=
    ggCoxRefl_of_isReflection hp hodd hBs hpres h3
      (ggNoTransvection_of_le_automizer hNT (ggAutomizer_le_top X Bs)) hr₀A hr₀
  obtain ⟨a, haA, hra⟩ :=
    ggCoxRefl_conj_of_connected ε (ggSimplyLacedConnected_of_weyl hW h3) hr₀C hrC
  obtain ⟨g, hgX, hgN, hga⟩ := mem_ggAutomizer_iff.mp haA
  have hmap : (ggRankOneIn X Bs r₀).map (MulAut.conj g).toMonoidHom = ggRankOneIn X Bs r := by
    have hX : X.map (MulAut.conj g).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgX)
    rw [ggRankOneIn_map_conj hga r₀, hX, hra]
  rw [← hmap]
  refine (Subgroup.map_mono hanchor).trans ?_
  exact le_iSup_of_le g (le_iSup_of_le hgX (le_iSup_of_le ⟨a, hgN, hga⟩ le_rfl))

end Table

section Assembly

theorem s2jn_ggSecFiveNbrGenKNInput'
    (hKG : GGSecFiveKGPosNbrInput')
    (hSplit : GGSecFiveSplitNbrGuardInput') (hSub : GGNbrSubcomponentInput)
    (hJR : GGSecFiveJReflInput') (hJD : GGSecFiveJNormDInput') : GGSecFiveNbrGenKNInput' := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL hguard y K' hnb hle
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hcfg0 := hcfg
  obtain ⟨⟨⟨⟨_, _, _, _, _, hβ, _⟩, _⟩, _⟩, _⟩ := hcfg0
  obtain ⟨hp, hp2, _⟩ := hβ
  have hBs : IsElemAbelian p Bs := hC.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hDB : D ≤ Bs := hC.2.2.1.1.trans hC.2.1.1
  have hJcomp := hC.2.2.1.2.2.2.2.2.1
  have hJDc : J ≤ Subgroup.centralizer (D : Set G) := hJcomp.1.trans inf_le_right
  have hJK : J ≤ K' := hSub G p B x L D J hC.1 hC.2.2 y K' hnb
  have hKs : GGSplitLie p K' := hSplit G p B Bs x L D J 𝒦 hcfg hL hguard y K' hnb hle
  obtain ⟨t, n, f, ψ, hadm, h3t, hker, hrange, ht, hpf, hpos⟩ :=
    hKG G p B Bs x L D J 𝒦 hcfg hL y K' hnb hKs
  obtain ⟨r₀, hr₀J, hr₀⟩ := hJR G p B Bs x L D J 𝒦 hcfg hL
  have hr₀A : r₀ ∈ ggAutomizer K' Bs := ggAutomizer_mono Bs hJK hr₀J
  have hr₀1 : r₀ ≠ 1 := by
    intro h1
    have hcard := hr₀.2
    rw [h1] at hcard
    have hfix : Nat.card {b : ↥Bs // (1 : MulAut ↥Bs) b = b} = Nat.card ↥Bs :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)
    rw [hfix] at hcard
    have hpos' : 0 < Nat.card ↥Bs := Nat.card_pos
    have : Nat.card ↥Bs * 1 < Nat.card ↥Bs * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hpos'
    omega
  have hsimp := s2jn_rankOne_simple_of_tableBPos hp hp2 hBs hNT ht hadm h3t hker hpf hpos hr₀A hr₀
  have hanchor : ggRankOneIn K' Bs r₀ ≤ J :=
    s2jn_ggRankOneIn_le_of_simple hr₀J hr₀.1 hr₀1 hJK hDB hJDc
      (hJD G p B Bs x L D J 𝒦 hcfg hL) hsimp
  exact s2jn_le_iSup_conj_of_tableBPos hp hp2 hBs hNT ht hadm h3t hrange hpos hr₀A hr₀ hanchor

end Assembly

end CFSG.StandardType
