module

public import CFSG.LocalAnalysis.StandardType.GGWAutEngine
public import CFSG.LocalAnalysis.StandardType.GGQTwoProp898
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_prop898_m_ge_five {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : ¬ GGQTwoI1 Bs D J) : ∃ m : ℕ, 5 ≤ m ∧ Nat.card Bs = p ^ m := by
  subst p
  obtain ⟨hpp, hBs, -, -, -⟩ := hS.1.1.tableB_facts
  have hDpre : CFSG.Assembly.LargeEvenStdSubPre 3 B x L D J := hS.1.1.2.2.1
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hDpre.2.2.2.2.2.2
  have hBle : B ≤ Bs := hS.1.1.2.1.1
  have hcard_le : Nat.card Bs ≤ 3 * Nat.card B := hS.1.1.2.1.2.2.1
  have hBpow := hS.1.1.1.2.2.2.2.2.2.1.1.2.1
  have h4 := hS.1.1.1.2.2.2.2.2.1.2.2.2
  obtain ⟨m, hm⟩ := IsPGroup.exists_card_eq (isPGroup_of_isElemAbelian hBs)
  have hstrict : B < Bs := by
    rcases lt_or_eq_of_le hBle with h | h
    · exact h
    · exfalso
      apply hI1
      intro b hb hcent
      have hbB : b ∈ B := by rw [← h] at hb; exact hb
      have hbc : b ∈ Subgroup.centralizer (J : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun j hj => (hcent j hj).symm
      rw [hDeq]
      exact ⟨hbB, hbc⟩
  have hcard_lt : Nat.card B < Nat.card Bs := by
    rcases lt_or_eq_of_le (Subgroup.card_le_of_le hBle) with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hBle h.ge) hstrict.ne
  have h1 : 3 ^ LargeEvenTwoLocalRank 3 G < 3 ^ m := by
    rw [← hBpow, ← hm]; exact hcard_lt
  have h2 : 3 ^ m ≤ 3 ^ (LargeEvenTwoLocalRank 3 G + 1) := by
    calc 3 ^ m = Nat.card Bs := hm.symm
      _ ≤ 3 * Nat.card B := hcard_le
      _ = 3 * 3 ^ LargeEvenTwoLocalRank 3 G := by rw [hBpow]
      _ = 3 ^ (LargeEvenTwoLocalRank 3 G + 1) := by rw [pow_succ']
  have hp1 : 1 < 3 := hpp.one_lt
  have hrm : LargeEvenTwoLocalRank 3 G < m := (Nat.pow_lt_pow_iff_right hp1).mp h1
  have hmr : m ≤ LargeEvenTwoLocalRank 3 G + 1 := (Nat.pow_le_pow_iff_right hp1).mp h2
  exact ⟨m, by omega, hm⟩

@[expose] def GGQ2Prop898NotOrth : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J → ∀ [Fact p.Prime],
      ∀ m : ℕ, Nat.card Bs = p ^ m → Even m →
        ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V),
          ¬ GGOrthType ((ggReflGp p Bs).map (ggLin (p := p) ι))

private theorem ggWAutP_transvectionFree {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (hNT : GGNoTransvection p Bs) :
    TransvectionFree ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) := by
  rintro g hg ⟨u, ψ, hu, hψ, hψu, hgv⟩
  rw [Subgroup.mem_map] at hg
  obtain ⟨φ, hφ, rfl⟩ := hg
  obtain ⟨k, -, hkN, hkφ⟩ := mem_ggAutomizer_iff.mp hφ
  exact hNT φ ⟨k, Subgroup.mem_top k, hkN, hkφ⟩
    (ggIsTransvection_of_apply ι hu hψ hψu hgv)

private theorem ggWAutP_reflGp_map {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (hp2 : p ≠ 2) :
    reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) =
      (ggReflGp p Bs).map (ggLin (p := p) ι) := by
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hST : ggLin (p := p) ι '' {φ | φ ∈ ggAutomizer ⊤ Bs ∧ GGIsReflection p φ} =
      {t | t ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι) ∧ IsReflLin t} := by
    ext t
    constructor
    · rintro ⟨φ, ⟨hφA, hφr⟩, hφt⟩
      refine ⟨Subgroup.mem_map.mpr ⟨φ, hφA, hφt⟩, ?_⟩
      obtain ⟨c, f, hcf, hφc⟩ := exists_of_ggIsReflection (p := p) ι hφr
      exact ⟨c, f, hcf, hφt.symm.trans (ggLin_eq_reflection ι hcf hφc)⟩
    · rintro ⟨htlin, ht⟩
      rw [Subgroup.mem_map] at htlin
      obtain ⟨φ, hφA, hφt⟩ := htlin
      obtain ⟨c, g, hg, ht_eq⟩ := ht
      exact ⟨φ, ⟨hφA, ggIsReflection_of_eq_reflection hp2 ι hg (hφt.trans ht_eq)⟩, hφt⟩
  rw [reflGp, ggReflGp, MonoidHom.map_closure, hST]

private theorem ggWAutP_absIrred {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (ρ : Representation (ZMod 3) ↥(ggReflGp 3 Bs) V)
    (hρ : ∀ (g : ↥(ggReflGp 3 Bs)) (v : V), ρ g v = ggLin (p := 3) ι g v)
    (habs : Theory.Representation.IsAbsolutelyIrreducible ρ) :
    ZS.AbsIrred 3 ((ggReflGp 3 Bs).map (ggLin (p := 3) ι)) := by
  let R : Subgroup (V ≃ₗ[ZMod 3] V) := (ggReflGp 3 Bs).map (ggLin (p := 3) ι)
  have hIrr : ρ.IsIrreducible :=
    Theory.Representation.IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  let : ρ.IsIrreducible := hIrr
  have hsurj : Function.Surjective (algebraMap (ZMod 3) (Theory.Representation.End ρ)) :=
    (Theory.Representation.isAbsolutelyIrreducible_iff_surjective ρ).mp habs
  refine ⟨?_, ?_⟩
  · intro W hWinv
    let S : Subrepresentation ρ :=
      { toSubmodule := W
        apply_mem_toSubmodule := fun g v hv => by
          have hmem : ggLin (p := 3) ι g ∈ R := Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩
          simpa [hρ g v] using hWinv (ggLin (p := 3) ι g) hmem v hv }
    rcases eq_bot_or_eq_top S with hbot | htop
    · left
      have h := congrArg Subrepresentation.toSubmodule hbot
      rw [show (⊥ : Subrepresentation ρ).toSubmodule = ⊥ from rfl] at h
      simpa [S] using h
    · right
      have h := congrArg Subrepresentation.toSubmodule htop
      rw [show (⊤ : Subrepresentation ρ).toSubmodule = ⊤ from rfl] at h
      simpa [S] using h
  · intro T hT
    let e : Theory.Representation.End ρ :=
      Representation.IntertwiningMap.mk T (fun g => by
        have hmem : ggLin (p := 3) ι g ∈ R := Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩
        have hcomm := hT (ggLin (p := 3) ι g) hmem
        have hρlin : ρ g = (ggLin (p := 3) ι g).toLinearMap := LinearMap.ext fun v => hρ g v
        rw [hρlin]
        exact hcomm)
    obtain ⟨c, hc⟩ := hsurj e
    refine ⟨c, ?_⟩
    have h2 : (algebraMap (ZMod 3) (Theory.Representation.End ρ) c).toLinearMap =
        c • LinearMap.id := by
      change (c • (1 : Theory.Representation.End ρ)).toLinearMap = c • LinearMap.id
      ext v
      simp
    calc T = e.toLinearMap := rfl
      _ = (algebraMap (ZMod 3) (Theory.Representation.End ρ) c).toLinearMap := by rw [← hc]
      _ = c • LinearMap.id := h2

private theorem ggWAutP_exists_inducing {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {ρ : MulAut ↥Bs} (hρ : ρ ∈ ggReflGp p Bs) :
    ∃ rG ∈ Subgroup.closure {h : G | ∃ φ : MulAut ↥Bs, GGQ2Ind Bs h φ ∧ GGIsReflection p φ},
      GGQ2Ind Bs rG ρ := by
  let T : Subgroup G :=
    Subgroup.closure {h : G | ∃ φ : MulAut ↥Bs, GGQ2Ind Bs h φ ∧ GGIsReflection p φ}
  rw [ggReflGp] at hρ
  refine Subgroup.closure_induction (p := fun φ _ => ∃ rG ∈ T, GGQ2Ind Bs rG φ) ?_ ?_ ?_ ?_ hρ
  · intro φ hφ
    obtain ⟨g, -, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ.1
    exact ⟨g, Subgroup.subset_closure ⟨φ, ⟨hgN, hgφ⟩, hφ.2⟩, hgN, hgφ⟩
  · exact ⟨1, T.one_mem, Subgroup.one_mem _, fun b => by simp⟩
  · intro a b ha hb iha ihb
    obtain ⟨rG, hrG, hrN, hra⟩ := iha
    obtain ⟨sG, hsG, hsN, hsb⟩ := ihb
    exact ⟨rG * sG, T.mul_mem hrG hsG, Subgroup.mul_mem _ hrN hsN, fun c => by
      rw [MulAut.mul_apply, hra (b c), hsb c]; group⟩
  · intro a ha iha
    obtain ⟨rG, hrG, hrN, hra⟩ := iha
    exact ⟨rG⁻¹, T.inv_mem hrG, Subgroup.inv_mem _ hrN, fun c => by
      rw [inv_apply_of_forall hra c, inv_inv]⟩

theorem ggQ2_orbitStable_of_engine (hE : GGWAutEngine) {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} (hNT : GGNoTransvection 3 Bs) (hAbs : GGQ2ReflAbsIrred 3 Bs) {m : ℕ}
    (hm5 : 5 ≤ m) (hm : Nat.card Bs = 3 ^ m)
    (hNO : Even m → ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V),
      ¬ GGOrthType ((ggReflGp 3 Bs).map (ggLin (p := 3) ι))) :
    ∀ u : ↥Bs, GGOrbitStableAt 3 Bs u := by
  intro u φ hφ
  obtain ⟨V, hACG, hMod, ι, habs⟩ := hAbs
  let : AddCommGroup V := hACG
  let : Module (ZMod 3) V := hMod
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  let A : Subgroup (V ≃ₗ[ZMod 3] V) := (ggAutomizer ⊤ Bs).map (ggLin (p := 3) ι)
  have hTF : TransvectionFree A := ggWAutP_transvectionFree ι hNT
  have hrefl : reflGp A = (ggReflGp 3 Bs).map (ggLin (p := 3) ι) :=
    ggWAutP_reflGp_map ι (by norm_num)
  have hcardV : Nat.card V = Nat.card Bs := (card_eq_of_ggLin ι).symm
  have hfr : Module.finrank (ZMod 3) V = m := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV, hm] at hcard
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hcard).symm
  let ρ : Representation (ZMod 3) ↥(ggReflGp 3 Bs) V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 3) (M := V)).comp
      ((ggLin (p := 3) ι).comp (ggReflGp 3 Bs).subtype)
  have habsρ : Theory.Representation.IsAbsolutelyIrreducible ρ := habs
  have hρ : ∀ (g : ↥(ggReflGp 3 Bs)) (v : V), ρ g v = ggLin (p := 3) ι g v := fun _ _ => rfl
  have habsZS : ZS.AbsIrred 3 (reflGp A) := by
    rw [hrefl]
    exact ggWAutP_absIrred ι ρ hρ habsρ
  rcases hE V m hfr hm5 A hTF habsZS with horth | hpm
  · exfalso
    exact (hNO horth.1 V ι) (hrefl ▸ horth.2)
  · have hφA : ggLin (p := 3) ι φ ∈ A := Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
    obtain ⟨rV, hrV, hpmr⟩ := hpm (ggLin (p := 3) ι φ) hφA
    rw [hrefl] at hrV
    obtain ⟨ρ', hρ', hρ'eq⟩ := Subgroup.mem_map.mp hrV
    refine ⟨ρ', hρ', ?_⟩
    rcases hpmr with heq | hneg
    · have hEqV : ggLin (p := 3) ι φ (ι (Additive.ofMul u)) =
          ggLin (p := 3) ι ρ' (ι (Additive.ofMul u)) := by
        rw [heq, ← hρ'eq]
      have hOf : Additive.ofMul (φ u) = Additive.ofMul (ρ' u) := by
        apply ι.injective
        rw [← ggLin_apply_ofMul (p := 3) ι φ u, ← ggLin_apply_ofMul (p := 3) ι ρ' u]
        exact hEqV
      rw [Additive.ofMul.injective hOf]
    · have hEqV : ggLin (p := 3) ι φ (ι (Additive.ofMul u)) =
          - ggLin (p := 3) ι ρ' (ι (Additive.ofMul u)) := by
        rw [hneg, ← hρ'eq]
      have hOf : Additive.ofMul (φ u) = Additive.ofMul (ρ' u)⁻¹ := by
        apply ι.injective
        rw [← ggLin_apply_ofMul (p := 3) ι φ u, ofMul_inv, map_neg,
          ← ggLin_apply_ofMul (p := 3) ι ρ' u]
        exact hEqV
      rw [Additive.ofMul.injective hOf, Subgroup.zpowers_inv]

theorem ggQ2Prop898_of_engine (hE : GGWAutEngine) (hNO : GGQ2Prop898NotOrth) : GGQ2Prop898 := by
  intro G _ _ p B Bs x L D J hS hp hI1 _ hAbs _
  subst p
  obtain ⟨-, -, hxBs, -, -⟩ := hS.1.1.tableB_facts
  obtain ⟨m, hm5, hm⟩ := ggQ2_prop898_m_ge_five (p := 3) hS rfl hI1
  have hstab := ggQ2_orbitStable_of_engine hE hS.1.2.2.2.1 hAbs hm5 hm
    (fun he V _ _ ι => hNO hS rfl hI1 m hm he V ι) ⟨x, hxBs⟩
  intro g hg
  let φg : MulAut ↥Bs := ggConjAut Bs hg
  obtain ⟨ρ', hρ', hzp⟩ := hstab φg (ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg)
  obtain ⟨rG, hrG, hInd⟩ := ggWAutP_exists_inducing (p := 3) hρ'
  refine ⟨rG, hrG, ?_⟩
  let b : ↥Bs := ⟨x, hxBs⟩
  have hφga : (φg b : G) = g * x * g⁻¹ := by simpa [b] using ggConjAut_apply Bs hg b
  have hρ'a : (ρ' b : G) = rG * x * rG⁻¹ := by simpa [b] using hInd.2 b
  have hmap := congrArg (Subgroup.map Bs.subtype) hzp
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
  simpa [b, hφga, hρ'a] using hmap

end CFSG.StandardType

end
