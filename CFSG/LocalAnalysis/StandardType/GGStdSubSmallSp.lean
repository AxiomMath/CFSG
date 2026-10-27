module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSpSiegel
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSymplectic
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallTypeA

public section

namespace CFSG.StandardType

namespace StdSubSp

open CFSG.Assembly CFSG.Assembly.LowTwoRank TableBSymp CFSG.SeitzReduction.SymplecticPilot

variable {K : Type} [Field K]

theorem ggStdSubTwoTorusElt_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {m : ℕ} (hm : 2 ≤ m) :
    GGStdSubTwoTorusElt p m (LargeEvenProj (LargeEvenSpGroup K m)) := by
  have : NeZero m := ⟨by omega⟩
  intro A hA hr _ a haA _ hcent
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hK4 := four_le_card_of_dvd hp hp2 hpq
  set e := spProjEquivSp (K := K) (m := m) with he
  set A₁ : Subgroup (GL (Fin m ⊕ Fin m) K) :=
    (A.map e.toMonoidHom).map (LargeEvenSpGroup K m).subtype with hA₁
  have hA₁e : IsElemAbelian p A₁ := TableB.isElemAbelian_map (TableB.isElemAbelian_map hA _) _
  have hcard₁ : Nat.card A₁ = Nat.card A := by
    rw [hA₁, ← Nat.card_congr ((A.map e.toMonoidHom).equivMapOfInjective
      _ (LargeEvenSpGroup K m).subtype_injective).toEquiv,
      ← Nat.card_congr (A.equivMapOfInjective _ e.injective).toEquiv]
  obtain ⟨P, hP, hconj⟩ := exists_conj_eq_range_spTorusGL hp2 (natCast_ne_zero_of_charTwo hp hp2)
    hζo hζ (Subgroup.map_subtype_le _) hA₁e (hcard₁ ▸ hr)
  set Pg : LargeEvenSpGroup K m := ⟨P, hP⟩ with hPg
  set Φ : LargeEvenProj (LargeEvenSpGroup K m) ≃* StatedSp m K :=
    e.trans (MulAut.conj Pg⁻¹) with hΦ
  have hΦapp : ∀ x, ((Φ x : StatedSp m K) : GL (Fin m ⊕ Fin m) K) =
      P⁻¹ * (e x : GL (Fin m ⊕ Fin m) K) * P := by
    intro x
    show ((Pg⁻¹ * e x * Pg⁻¹⁻¹ : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) = _
    rw [inv_inv]
    rfl
  have hAΦ : A.map Φ.toMonoidHom = (spTorusSt (n := m) hζ).range := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hmem : P⁻¹ * (e s : GL (Fin m ⊕ Fin m) K) * P ∈ (spTorusGL (m := m) hζ).range := by
        rw [← hconj]
        refine ⟨(e s : GL (Fin m ⊕ Fin m) K), ⟨e s, ⟨s, hs, rfl⟩, rfl⟩, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      obtain ⟨f, hf⟩ := hmem
      exact ⟨f, Subtype.ext (by rw [coe_spTorusSt, hf, MulEquiv.coe_toMonoidHom, hΦapp])⟩
    · rintro ⟨f, rfl⟩
      have hmem : spTorusGL (m := m) hζ f ∈ A₁.map (MulAut.conj P⁻¹).toMonoidHom := by
        rw [hconj]
        exact ⟨f, rfl⟩
      obtain ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hq⟩ := hmem
      refine ⟨s, hs, Subtype.ext ?_⟩
      rw [MulEquiv.coe_toMonoidHom, hΦapp, coe_spTorusSt, ← hq, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      rfl
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, spTorusSt hζ f₀ = Φ a := by
    have : Φ a ∈ A.map Φ.toMonoidHom := ⟨a, haA, rfl⟩
    rw [hAΦ] at this
    exact this
  have hcent' : ∀ g : Fin m → Multiplicative (ZMod p),
      (∀ c ∈ Subgroup.centralizer ({spTorusSt hζ f₀} : Set (StatedSp m K)),
        spTorusSt hζ g * c = c * spTorusSt hζ g) →
      spTorusSt hζ g ∈ Subgroup.zpowers (spTorusSt hζ f₀) := by
    intro g hg
    have hgA : spTorusSt hζ g ∈ A.map Φ.toMonoidHom := by
      rw [hAΦ]
      exact ⟨g, rfl⟩
    obtain ⟨b, hb, hbg⟩ := hgA
    rw [MulEquiv.coe_toMonoidHom] at hbg
    have hb' : b ∈ Subgroup.zpowers a := by
      refine hcent b hb fun c hc => Φ.injective ?_
      have h1 : Φ c ∈ Subgroup.centralizer ({spTorusSt hζ f₀} : Set (StatedSp m K)) := by
        rw [Subgroup.mem_centralizer_singleton_iff, hf₀, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.mp hc]
      have h2 := hg (Φ c) h1
      rw [map_mul, map_mul, hbg]
      exact h2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [hf₀, ← hbg, ← hk, map_zpow]
  apply GGStdSubEltData.of_mulEquiv Φ
  rw [hAΦ, ← hf₀]
  exact ggStdSubEltData_spTorusSt hK4 hm hp hp2 hζo hζ f₀ hcent'

theorem ggStdSubTwoTorus_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {m : ℕ} (hm : 2 ≤ m) :
    GGStdSubTwoTorus p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  exact ggStdSubTwoTorus_of_elt hp hp2 sp_I_subset_inn center_spProj_eq_bot
    (ggStdSubTwoTorusElt_symplectic hp hp2 hpq hm)

end StdSubSp

open CFSG.Assembly

theorem ggStdSubTwoTorus_symplectic_of_card : ∀ (l n p : ℕ) (K : Type) [Field K] [Finite K],
    Nat.card K = 2 ^ n → p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 → 3 ≤ l →
      GGStdSubTwoTorus p l (LargeEvenProj (LargeEvenSpGroup K l))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l)) :=
  fun _ _ _ K _ _ hK hp hp2 hpn hl => by
    have := charP_two_of_card hK
    exact StdSubSp.ggStdSubTwoTorus_symplectic hp hp2 (by rw [hK]; exact hpn) (by omega)

theorem ggStdSubSmallInputOn_symplectic :
    GGStdSubSmallInputOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1 :=
  ggStdSubSmallInputOn_symplectic_of_sp ggStdSubTwoTorus_symplectic_of_card

theorem ggStdSubSmallInput_of_rest_symplectic
    (h : GGStdSubSmallInputOn fun p lab => ¬ GGTypeASplitLabel p lab ∧
      ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) : GGStdSubSmallInput :=
  ggStdSubSmallInput_of_cover
    ((ggStdSubSmallInputOn_typeA_split_holds.or ggStdSubSmallInputOn_symplectic).or h)
    fun p lab _ _ => by
      by_cases h1 : GGTypeASplitLabel p lab
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨h1, h2⟩

end CFSG.StandardType

end
