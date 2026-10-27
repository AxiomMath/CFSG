module

public import CFSG.LocalAnalysis.StandardType.GGR4JCardDefs
public import CFSG.LocalAnalysis.StandardType.GGCentreTwoKnownHolds
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGR4Centre

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggR4J_card_Bs {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod 3) V}
    [Fact (Nat.Prime 3)] (hD : GGExtDatum ι X φ' h' α')
    (hspan : Submodule.span (ZMod 3) (Set.range h') = ⊤) (hcard : Fintype.card Λ = 4) :
    Nat.card Bs = 3 ^ 5 := by
  have hb : Module.Basis (Option Λ) (ZMod 3) V :=
    Module.Basis.mk hD.indep (le_of_eq hspan.symm)
  have hdim : Module.finrank (ZMod 3) V = 5 := by
    rw [Module.finrank_eq_card_basis hb, Fintype.card_option, hcard]
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Fintype V := Fintype.ofFinite V
  have hcardV : Nat.card V = 3 ^ 5 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3) (V := V), hdim,
      ZMod.card]
  calc Nat.card Bs = Nat.card V := card_eq_of_ggLin ι
    _ = 3 ^ 5 := hcardV

theorem ggR4J_inn_of_meet {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs D J : Subgroup G} (hBsEA : IsElemAbelian p Bs) (hDBs : D ≤ Bs)
    (hDcard : Nat.card D = p ^ 2) (hDJ : D ≤ Subgroup.centralizer (J : Set G))
    (hZ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime p (orderOf g))
    (hBs : Nat.card Bs ≤ p ^ 5) (hE : p ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G)) :
    ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹ := by
  let E : Subgroup G := Bs ⊓ J
  have hDinfJ : D ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hgD : g ∈ D := hg.1
    have hgJ : g ∈ J := hg.2
    have hgBs : g ∈ Bs := hDBs hgD
    have hgp : g ^ p = 1 := hBsEA.2 g hgBs
    have hcent : (⟨g, hgJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      simpa using Subgroup.mem_centralizer_iff.mp (hDJ hgD) (l : G) l.2
    have hcop : Nat.Coprime p (orderOf (⟨g, hgJ⟩ : ↥J)) := hZ _ hcent
    have hdvd : orderOf (⟨g, hgJ⟩ : ↥J) ∣ p := orderOf_dvd_of_pow_eq_one (by
      apply Subtype.ext
      simpa using hgp)
    have hone : orderOf (⟨g, hgJ⟩ : ↥J) = 1 := hcop.symm.eq_one_of_dvd hdvd
    exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp hone)
  have hDEbot : D ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hgE : g ∈ Bs ⊓ J := hg.2
    have hg' : g ∈ D ⊓ J := ⟨hg.1, (Subgroup.mem_inf.mp hgE).2⟩
    rw [hDinfJ] at hg'
    exact Subgroup.mem_bot.mp hg'
  have hcommDE : ∀ d ∈ D, ∀ e ∈ E, d * e = e * d := by
    intro d hd e he
    have heJ : e ∈ J := (Subgroup.mem_inf.mp he).2
    exact (Subgroup.mem_centralizer_iff.mp (hDJ hd) e heJ).symm
  let φ : ↥D × ↥E →* G :=
    { toFun := fun de => (de.1 : G) * (de.2 : G)
      map_one' := by simp
      map_mul' := fun a b => by
        have hc : (b.1 : G) * (a.2 : G) = (a.2 : G) * (b.1 : G) :=
          hcommDE (b.1 : G) b.1.2 (a.2 : G) a.2.2
        calc ((a.1 : G) * (b.1 : G)) * ((a.2 : G) * (b.2 : G))
            = (a.1 : G) * ((b.1 : G) * (a.2 : G)) * (b.2 : G) := by group
          _ = (a.1 : G) * ((a.2 : G) * (b.1 : G)) * (b.2 : G) := by rw [hc]
          _ = ((a.1 : G) * (a.2 : G)) * ((b.1 : G) * (b.2 : G)) := by group }
  have hφinj : Function.Injective φ := by
    rintro ⟨d1, e1⟩ ⟨d2, e2⟩ hab
    have hab' : (d1 : G) * (e1 : G) = (d2 : G) * (e2 : G) := hab
    have h' : (d2 : G)⁻¹ * (d1 : G) = (e2 : G) * (e1 : G)⁻¹ := by
      have hc := congrArg (fun x => (d2 : G)⁻¹ * x * (e1 : G)⁻¹) hab'
      simpa [mul_assoc] using hc
    have hmem : (d2 : G)⁻¹ * (d1 : G) ∈ D ⊓ E :=
      ⟨D.mul_mem (D.inv_mem d2.2) d1.2, h' ▸ E.mul_mem e2.2 (E.inv_mem e1.2)⟩
    rw [hDEbot] at hmem
    have h1 : (d2 : G)⁻¹ * (d1 : G) = 1 := Subgroup.mem_bot.mp hmem
    have hd : (d1 : ↥D) = d2 := Subtype.ext (inv_mul_eq_one.mp h1).symm
    have he : (e1 : ↥E) = e2 := Subtype.ext (mul_inv_eq_one.mp (h1 ▸ h').symm).symm
    exact Prod.ext hd he
  have hle : D ⊔ E ≤ φ.range := by
    refine sup_le ?_ ?_
    · intro x hx
      exact ⟨(⟨x, hx⟩, 1), by simp [φ]⟩
    · intro x hx
      exact ⟨(1, ⟨x, hx⟩), by simp [φ]⟩
  have hge : φ.range ≤ D ⊔ E := by
    rintro _ ⟨⟨d, e⟩, rfl⟩
    exact Subgroup.mul_mem_sup d.2 e.2
  have hRange : D ⊔ E = φ.range := le_antisymm hle hge
  have hcardjoin : Nat.card ↥(D ⊔ E) = Nat.card D * Nat.card E := by
    rw [hRange, MonoidHom.range_eq_map φ, Subgroup.card_map_of_injective hφinj,
      Subgroup.card_top, Nat.card_prod]
  have hleBs : D ⊔ E ≤ Bs := sup_le hDBs inf_le_left
  have hcardge : Nat.card Bs ≤ Nat.card ↥(D ⊔ E) := by
    rw [hcardjoin, hDcard]
    calc Nat.card Bs ≤ p ^ 5 := hBs
      _ = p ^ 2 * p ^ 3 := by ring
      _ ≤ p ^ 2 * Nat.card (Bs ⊓ J : Subgroup G) := Nat.mul_le_mul_left _ hE
  have hjoin : D ⊔ E = Bs := Subgroup.eq_of_le_of_card_ge hleBs hcardge
  intro b hb
  have hbjoin : b ∈ D ⊔ E := by rw [hjoin]; exact hb
  have hb' : b ∈ φ.range := by rw [← hRange]; exact hbjoin
  obtain ⟨⟨d, e⟩, hde⟩ := MonoidHom.mem_range.mp hb'
  have hde' : b = (d : G) * (e : G) := by rw [← hde]; rfl
  have heJ : (e : G) ∈ J := (Subgroup.mem_inf.mp e.2).2
  refine ⟨(e : G), heJ, ?_⟩
  intro l hl
  have hmem : (e : G) * l * (e : G)⁻¹ ∈ J :=
    J.mul_mem (J.mul_mem heJ hl) (J.inv_mem heJ)
  have hcomm : (d : G) * ((e : G) * l * (e : G)⁻¹) =
      ((e : G) * l * (e : G)⁻¹) * (d : G) :=
    (Subgroup.mem_centralizer_iff.mp (hDJ d.2) ((e : G) * l * (e : G)⁻¹) hmem).symm
  rw [hde']
  calc ((d : G) * (e : G)) * l * ((d : G) * (e : G))⁻¹
      = (d : G) * ((e : G) * l * (e : G)⁻¹) * (d : G)⁻¹ := by group
    _ = ((e : G) * l * (e : G)⁻¹) * (d : G) * (d : G)⁻¹ := by rw [hcomm]
    _ = (e : G) * l * (e : G)⁻¹ := by group

private theorem tbd_one_le_of_hasLabel_C {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.C, 3, f⟩ R) : 1 ≤ f := by
  unfold GGHasLabel at h
  rw [show CFSG.StandardType.LargeEvenRawDatum ⟨.C, 3, f⟩ =
      LargeEvenRecipeSymplectic 3 (2 ^ f) false from rfl] at h
  unfold LargeEvenRecipeSymplectic at h
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  have := hK
  have := hKfin
  have h2 : 2 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  rw [hKcard] at h2
  by_contra hf
  have hf0 : f = 0 := by omega
  rw [hf0] at h2
  norm_num at h2

theorem ggR4J_center_coprime (hZk : GGCentreTwoKnown) {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hJperf : commutator ↥J = ⊤) {f : ℕ}
    (hC3 : GGHasLabel ⟨.C, 3, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g) := by
  have hfl : 1 ≤ f := tbd_one_le_of_hasLabel_C hC3
  have hlab2 : LargeEvenInLambda2 ⟨.C, 3, f⟩ := by simp [LargeEvenInLambda2, hfl]
  have hZ2 : ∀ g ∈ Subgroup.center ↥J, ∃ k : ℕ, orderOf g = 2 ^ k :=
    ggCentreTwo_of_label hZk hlab2 (by simp) hJperf hC3
  intro g hg
  obtain ⟨k, hk⟩ := hZ2 g hg
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

end CFSG.StandardType

end
