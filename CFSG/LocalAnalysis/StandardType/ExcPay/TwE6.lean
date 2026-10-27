module

public import CFSG.LocalAnalysis.StandardType.ExcPay.CoverTwE6
public import CFSG.LocalAnalysis.StandardType.ExcPay.SquareTwE6
public import Certificates.Certificate13723
public import Certificates.Certificate13724

import CFSG.LocalAnalysis.StandardType.ExcPay.CardTwE6
import CFSG.LocalAnalysis.StandardType.ExcPay.CoreGen
import CFSG.LocalAnalysis.StandardType.ExcPay.InnerSplit
import CFSG.LocalAnalysis.StandardType.ExcPay.LiftSU
import CFSG.LocalAnalysis.StandardType.ExcPay.ModelTwE6

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem excPayT_mem_tp {G : Type} [Group G] {p f : ℕ} {Bs X : Subgroup G}
    {ht : GGExcFive .twistedE6} {M : GGDatumModel .twistedE6 f p ht} (η : ↥X →* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag .twistedE6) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag .twistedE6) GGL) = z) ↔
        ∃ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag .twistedE6) a = z) (y : ↥M.D.Γ) :
    y ∈ excPayTp M ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y := by
  rw [excPayTp, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hay⟩
    obtain ⟨x, hx, hxy⟩ := (hη y).2 ⟨a, fun i => congrFun (MonoidHom.mem_ker.1 ha) i, hay⟩
    exact ⟨x, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, hay⟩ := (hη (η x)).1 ⟨x, hx, rfl⟩
    exact ⟨a, MonoidHom.mem_ker.2 (funext ha), hay⟩

private theorem excPayT_lifts {G : Type} [Group G] [Finite G] {p f : ℕ} {Bs X : Subgroup G}
    {ht : GGExcFive .twistedE6} (hp : p.Prime) (hBs : IsElemAbelian p Bs)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    {M : GGDatumModel .twistedE6 f p ht} (η : ↥X →* ↥M.D.Γ) (hηs : Function.Surjective η)
    (hker : η.ker = Subgroup.center ↥X) (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥X)))
    (hB : ∀ y : ↥M.D.Γ, y ∈ excPayTp M ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    (S : ExcPaySquare .twistedE6 ht f p (excPayTp M) ⊤)
    (hS : ∀ k, ∃ (g : ↥M.D.Γ) (hg : g ∈ Subgroup.normalizer (excPayTp M : Set ↥M.D.Γ)),
      S.s k = ggConjAut (excPayTp M) hg) :
    ∃ (x : Fin 6 → G) (hxN : ∀ k, x k ∈ Subgroup.normalizer (Bs : Set G)), (∀ k, x k ∈ X) ∧
      (∀ k, GGIsReflection p (ggConjAut Bs (hxN k))) ∧
      ∀ k, ((ggRankOneIn X Bs (ggConjAut Bs (hxN k))).subgroupOf X).map η =
        ggRankOneIn ⊤ (excPayTp M) (S.s k) := by
  have h : ∀ k : Fin 6, ∃ (x : G) (hxN : x ∈ Subgroup.normalizer (Bs : Set G)), x ∈ X ∧
      GGIsReflection p (ggConjAut Bs hxN) ∧
      ((ggRankOneIn X Bs (ggConjAut Bs hxN)).subgroupOf X).map η =
        ggRankOneIn ⊤ (excPayTp M) (S.s k) := by
    intro k
    obtain ⟨g, hg, hgk⟩ := hS k
    obtain ⟨x, hxN, hxX, hrefl, hmap⟩ := excPayL_refl_lift hp hBs hsplit η hηs hker hZ hodd hB
      hg (by rw [← hgk]; exact S.s_refl k)
    exact ⟨x, hxN, hxX, hrefl, by rw [hmap, hgk]⟩
  choose x hxN hxX hrefl hmap using h
  exact ⟨x, hxN, hxX, hrefl, hmap⟩

private theorem excPayT_pair {G : Type} [Group G] [Finite G] {p f : ℕ} [NeZero f]
    {Bs X : Subgroup G} {ht : GGExcFive .twistedE6} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 2 ≤ f)
    (hplus : p ∣ 2 ^ f + 1) {M : GGDatumModel .twistedE6 f p ht} [Finite ↥M.D.Γ]
    (η : ↥X →* ↥M.D.Γ) (hηs : Function.Surjective η) (hker : η.ker = Subgroup.center ↥X)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥X)))
    (S : ExcPaySquare .twistedE6 ht f p (excPayTp M) ⊤) (s : Fin 6 → MulAut ↥Bs)
    (hmap : ∀ k, ((ggRankOneIn X Bs (s k)).subgroupOf X).map η =
      ggRankOneIn ⊤ (excPayTp M) (S.s k))
    {i j : Fin 6} (h3 : CoxeterMatrix.E₆ i j = 3) :
    ∃ θG : Su (actualQuadraticSubfield f) 2 f 3 →* G, Function.Injective θG ∧
      (B12 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs (s i) ∧
      (B23 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs (s j) := by
  obtain ⟨θY, hθY, -, h12, h23, -⟩ :=
    excPaySquare_pair (Or.inl rfl) hp hp2 hplus S (isA2Pair_simple_E6 h3)
  obtain ⟨θG, hθG, -, hB12, hB23⟩ :=
    excPayL_lift_su3 (card_actualQuadraticSubfield (f := f) (by omega)) hf η hηs hker.le
      (by rw [hker]; exact hodd) inf_le_left inf_le_left θY hθY
      (h12.trans (hmap i).symm) (h23.trans (hmap j).symm)
  exact ⟨θG, hθG, hB12, hB23⟩

private theorem excPayT_rankOne_iso {G : Type} [Group G] [Finite G] {p f : ℕ} [NeZero f]
    {Bs X : Subgroup G} {ht : GGExcFive .twistedE6} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 2 ≤ f)
    (hplus : p ∣ 2 ^ f + 1) {M : GGDatumModel .twistedE6 f p ht} [Finite ↥M.D.Γ]
    (η : ↥X →* ↥M.D.Γ) (hηs : Function.Surjective η) (hker : η.ker = Subgroup.center ↥X)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥X)))
    (S : ExcPaySquare .twistedE6 ht f p (excPayTp M) ⊤) (s : Fin 6 → MulAut ↥Bs)
    (hmap : ∀ k, ((ggRankOneIn X Bs (s k)).subgroupOf X).map η =
      ggRankOneIn ⊤ (excPayTp M) (S.s k)) (i : Fin 6) :
    Nonempty (Su (actualQuadraticSubfield f) 2 f 2 ≃* ggRankOneIn X Bs (s i)) := by
  obtain ⟨j, hj⟩ := exists_edge_E6 i
  obtain ⟨θG, hθinj, hB12, -⟩ := excPayT_pair hp hp2 hf hplus η hηs hker hodd S s hmap hj
  refine ⟨(MonoidHom.ofInjective
    (CFSG.LieType.Steinberg.embSUid_injective
      (CFSG.LieType.BorelTits.unitaryInvolution
        (actualQuadraticSubfield f) 2 f) 2)).trans ?_⟩
  exact (Subgroup.equivMapOfInjective (B12 (actualQuadraticSubfield f) 2 f) θG hθinj).trans
    (MulEquiv.subgroupCongr hB12)

private theorem excPayT_comm {G : Type} [Group G] [Finite G] {p f : ℕ} {Bs X : Subgroup G}
    {ht : GGExcFive .twistedE6} (hp : p.Prime) (hp2 : p ≠ 2) {M : GGDatumModel .twistedE6 f p ht}
    (η : ↥X →* ↥M.D.Γ) (hker : η.ker = Subgroup.center ↥X)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥X)))
    (S : ExcPaySquare .twistedE6 ht f p (excPayTp M) ⊤) (s : Fin 6 → MulAut ↥Bs)
    (hmap : ∀ k, ((ggRankOneIn X Bs (s k)).subgroupOf X).map η =
      ggRankOneIn ⊤ (excPayTp M) (S.s k))
    {i j : Fin 6} (hij : i ≠ j) (h2 : CoxeterMatrix.E₆ i j = 2) :
    ∀ a ∈ ggRankOneIn X Bs (s i), ∀ b ∈ ggRankOneIn X Bs (s j), a * b = b * a := by
  have hY := excPaySquare_comm (Or.inl rfl) hp hp2 S (orth_simple_E6 hij h2)
  exact excPayL_comm_lift η hker.le (by rw [hker]; exact hodd) inf_le_left inf_le_left
    fun x hx y hy => hY x ((hmap i).le hx) y ((hmap j).le hy)

private theorem excPayT_of_model {G : Type} [Group G] [Finite G] {p f : ℕ} {Bs X : Subgroup G}
    {ht : GGExcFive .twistedE6} (hp : p.Prime) (hp5 : 5 ≤ p) (hBs : IsElemAbelian p Bs)
    (hf : 2 ≤ f) (hplus : p ∣ 2 ^ f + 1) (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥X)))
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsCentralQuotientOf (lieUniversal .twistedE6 0 2 f Nat.prime_two) ↥X)
    {M : GGDatumModel .twistedE6 f p ht} (η : ↥X →* ↥M.D.Γ) (hηs : Function.Surjective η)
    (hker : η.ker = Subgroup.center ↥X) (hZΓ : Subgroup.center ↥M.D.Γ = ⊥)
    (hη : ∀ z : ModGL (langTag .twistedE6) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag .twistedE6) GGL) = z) ↔
        ∃ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag .twistedE6) a = z) :
    GGExcPhanPayloadOf 6 CoxeterMatrix.E₆ .twistedE6 p Bs X := by
  have hne : NeZero f := ⟨by omega⟩
  have hp2 : p ≠ 2 := by omega
  haveI : Finite ↥M.D.Γ := Finite.of_surjective η hηs
  obtain ⟨S, hS⟩ := exists_excPaySquareY_TwE6 hp hp5 (by omega) hplus M hZΓ fun a ha => by
    obtain ⟨x, -, hx⟩ := (hη (rootDiagUnit (langTag .twistedE6) a)).2 ⟨a, ha, rfl⟩
    rw [← hx]
    exact (η x).2
  obtain ⟨x, hxN, hxX, hrefl, hmap⟩ :=
    excPayT_lifts hp hBs hsplit η hηs hker hZ hodd (excPayT_mem_tp η hη) S hS
  have hq : 4 ≤ 2 ^ f := by
    have h : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    simpa using h
  refine ⟨f, hq, hCQ, fun k => ggConjAut Bs (hxN k),
    fun k => ⟨ggConjAut_mem_ggAutomizer (hxX k) (hxN k), hrefl k⟩, actualQuadraticSubfield f,
    inferInstance, inferInstance, inferInstance, card_actualQuadraticSubfield (f := f) (by omega),
    fun i => excPayT_rankOne_iso hp hp2 hf hplus η hηs hker hodd S _ hmap i,
    fun i j hij h2 => excPayT_comm hp hp2 η hker hodd S _ hmap hij h2, fun i j h3 => ?_⟩
  obtain ⟨θG, hθG, h12, h23⟩ := excPayT_pair hp hp2 hf hplus η hηs hker hodd S _ hmap h3
  have hc : ∀ H : Subgroup (Su (actualQuadraticSubfield f) 2 f 3),
      H.map (MulAut.conj (1 : Su (actualQuadraticSubfield f) 2 f 3)⁻¹).toMonoidHom = H :=
    fun H => by
      rw [inv_one, map_one]
      ext x
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.one_apply, exists_eq_right]
  refine ⟨θG.range, θG, 1, rfl, ?_, Or.inl ⟨by rw [hc]; exact h12, by rw [hc]; exact h23⟩⟩
  rw [(MonoidHom.ker_eq_bot_iff θG).2 hθG]
  exact bot_le

theorem exists_excPhanPayload_of_marking_TwE6 {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hp3 : p ≠ 3) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X) :
    GGExcPhanPayloadOf 6 CoxeterMatrix.E₆ .twistedE6 p Bs X := by
  obtain ⟨f, hf, hplus, ψ₀, hpres, hZ3, hinn⟩ := exists_twE6Cover_of_marking hp hp3 hBs hmark
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hplus
    omega
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  have hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p :=
    Nat.Coprime.coprime_dvd_left hZ3 ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
  obtain ⟨hsplit, hsplit2⟩ :=
    excPay_inner_split_of_coprime hp hBs hSC hZ fun b hb => (hinn b hb).2
  obtain ⟨M, η, hηs, hker, hZΓ, hη⟩ := exists_excPayModel_TwE6
    (ht := Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hp hp5 (by omega) hplus hBs hpres hZ3
    (card_inf_eq_pow_six_of_marking_twE6 hp hp5 hBs hmark hZ hsplit2)
  exact excPayT_of_model hp hp5 hBs hf hplus hZ (Odd.of_dvd_nat ⟨1, rfl⟩ hZ3) hsplit
    (isCentralQuotientOf_of_presentsG0 hpres) η hηs hker hZΓ hη

end CFSG.StandardType.ExcPay
