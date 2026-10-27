module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusOneData
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusCenter
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2der
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derExistsY

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SympMinus

theorem sympMinus_conj_unique {X : Type} [Group X] {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} [NeZero m] {ψ : X →* LargeEvenProj (LargeEvenSpGroup K m)}
    (hψ : Function.Surjective ψ) {a : MulAut X} {g g' : LargeEvenProj (LargeEvenSpGroup K m)}
    (hg : ∀ l : X, ψ (a l) = g * ψ l * g⁻¹) (hg' : ∀ l : X, ψ (a l) = g' * ψ l * g'⁻¹) :
    g = g' := by
  have hc : g⁻¹ * g' ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    have h1 := hg l
    have h2 := hg' l
    calc ψ l * (g⁻¹ * g') = g⁻¹ * (g * ψ l * g⁻¹) * g' := by group
      _ = g⁻¹ * (g' * ψ l * g'⁻¹) * g' := by rw [← h1, h2]
      _ = (g⁻¹ * g') * ψ l := by group
  have h1 : g⁻¹ * g' = 1 := by
    have hmem : g⁻¹ * g' ∈ (⊥ : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))) := by
      rwa [← TableBSymp.center_spProj_eq_bot]
    exact Subgroup.mem_bot.mp hmem
  have h2 : g' = g := by
    calc g' = g * (g⁻¹ * g') := by group
      _ = g * 1 := by rw [h1]
      _ = g := by rw [mul_one]
  exact h2.symm

theorem ggTBJNbr_sympMinus_one_of_marking
    (hA1 : GGB2derSympKnown)
    (hI3 : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel (fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ lab.n = 1) p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨m, Kf, _, _, _, hN, θ, hm3, hK2, hpq, hXc, hBsI⟩ := exists_data_of_marking_one hmark
  haveI : NeZero m := ⟨by omega⟩
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  rcases ggTBJ_sympMinus_side hp2 hm3 (Or.inr hK2) hpq hBs hSC hN hXc θ hBsI hxBs hJcomp
      hcfg.card_bstar_inf_centralizer_J_le (sympMinus_J_ne_K hH) with h | h | ⟨-, g, -, -, -, ⟨e6⟩⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have hp3 : p = 3 := by
      rw [hK2] at hpq
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpq
    subst hp3
    exact ggConfig_not_B2der hA1 hcfg
      (CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_b2der e6)

theorem ggTBJLeft_sympMinus_one_of_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel (fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ lab.n = 1) p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨m, Kf, _, _, _, hN, θ, hm3, hK2, hpq, hXc, hBsI⟩ := exists_data_of_marking_one hmark
  haveI : NeZero m := ⟨by omega⟩
  have hp3 : p = 3 := by
    rw [hK2] at hpq
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpq
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hcon1, hcon2⟩ := hcon
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hDB : D ≤ B := hcfg.2.2.1.1
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hDcent : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  have hcount := hcfg.card_bstar_inf_centralizer_J_le
  have hBL : B ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_largeEvenStandardType hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hψ, hker, hperf, hAe, hAI, hsc⟩ := tbFacts_of_marking hBs hSC hXc θ hN hBsI
  subst hp3
  have hA6 : ∀ y' : G, y' ∈ D → y' ∉ Subgroup.zpowers x → ∃ hy' : y' ∈ Bs,
      SympA6Out L J (ggQuotHom θ) (ggGamma L hN ⟨y', hy'⟩) := by
    intro y' hy'D hy'x
    have hy'Bs : y' ∈ Bs := hBBs (hDB hy'D)
    refine ⟨hy'Bs, ?_⟩
    have hDgen := ggB2der_D_gen hS.1.1 hDB hDcard hxD hx1 hy'D hy'x
    have hLD : L ⊓ Subgroup.centralizer (D : Set G) =
        L ⊓ Subgroup.centralizer ({y'} : Set G) := by
      ext l
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
        forall_eq]
      constructor
      · rintro ⟨hl, h⟩
        exact ⟨hl, h y' hy'D⟩
      · rintro ⟨hl, h⟩
        refine ⟨hl, fun d hd => ?_⟩
        obtain ⟨i, j, rfl⟩ := hDgen d hd
        have hcx : Commute x l := Subgroup.mem_centralizer_iff.mp (hLx hl) x rfl
        have hcy : Commute y' l := h
        exact (((hcx.zpow_left i).mul_left (hcy.zpow_left j)) : Commute (x ^ i * y' ^ j) l).eq
    have hJc' : IsComponentOf J (L ⊓ Subgroup.centralizer ({y'} : Set G)) := hLD ▸ hJcomp
    have hJL : J ≠ L := by
      intro hJL'
      have hy'C : y' ∈ Subgroup.centralizer (J : Set G) := by
        have h : y' ∈ B ⊓ Subgroup.centralizer (J : Set G) := hDcent ▸ hy'D
        exact h.2
      rw [hJL'] at hy'C
      apply hy'x
      rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
      exact ⟨hDB hy'D, hy'C⟩
    rcases ggTBJ_sympMinus_side hp2 hm3 (Or.inr hK2) hpq hBs hSC hN hXc θ hBsI hy'Bs hJc'
        hcount hJL with h | h | h
    · exact absurd h hcon1
    · exact absurd h hcon2
    · exact h
  obtain ⟨y₀, hy₀D, hy₀x, -⟩ := ggB2der_exists_y hS.1.1 hDB hDcard hxD hx1
  obtain ⟨_, hout₀⟩ := hA6 y₀ hy₀D hy₀x
  obtain ⟨-, -, -, -, -, ⟨e6⟩⟩ := hout₀
  have hex : ∀ b : ↥B, ∃ g : LargeEvenProj (LargeEvenSpGroup Kf m), ∀ l : ↥L,
      ggQuotHom θ ((L.normalizerMonoidHom (Subgroup.inclusion hBL b)) l) =
        g * ggQuotHom θ l * g⁻¹ := by
    intro b
    obtain ⟨φ, ⟨g, hg⟩, hφ⟩ := hAI (ggGamma L hN ⟨b, hBBs b.2⟩) ⟨⟨b, hBBs b.2⟩, rfl⟩
    refine ⟨g, fun l => ?_⟩
    have h1 := hφ l
    rw [← hg, MulAut.conj_apply] at h1
    exact h1.symm
  obtain ⟨β, hβ⟩ := ggB2der_beta_of_exists (hBL := hBL) hψ hex
  have hZ := sympMinus_center_two hXc hK2 hm3 θ
  refine ggConfig_not_B2der_of_model hcfg
    (CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_b2der e6) hBL ?_
  refine ⟨Kf, inferInstance, inferInstance, inferInstance, m, inferInstance, hK2, hm3,
    ggQuotHom θ, β, ⟨hψ, ker_ggQuotHom θ, hβ⟩, fun b hbD hbx => ?_⟩
  obtain ⟨hbBs, -, g, hg, hdim, hmap, -⟩ := hA6 (b : G) hbD hbx
  have hgβ : g = β b :=
    sympMinus_conj_unique (a := ggGamma L hN ⟨(b : G), hbBs⟩) hψ hg (fun l => hβ b l)
  subst hgβ
  exact ⟨hZ.1, hZ.2, hdim, hmap⟩

end SympMinus

theorem ggTBJNbrOn_sympMinus_one
    (hA1 : GGB2derSympKnown) (hI3 : GGNbrSubcomponentInput) :
    GGTBJNbrOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ lab.n = 1 := by
  intro G _ _ p B Bs x L D J y K hH hp hK _
  rcases SympMinus.ggTBJNbr_sympMinus_one_of_marking hA1 hI3 hH hK with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJLeftOn_sympMinus_one :
    GGTBJLeftOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ lab.n = 1 := by
  intro G _ _ p B Bs x L D J y K hH hp hL _
  rcases SympMinus.ggTBJLeft_sympMinus_one_of_marking hH hL with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end CFSG.StandardType

end
