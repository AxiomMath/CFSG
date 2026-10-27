module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientActionPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FixedImage

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.FixedImage

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped commutatorElement

namespace CFSG.StandardType.F4ExplicitPos.ComponentAttach

variable {K L X : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Group X] [Finite X]

noncomputable def etaF4
    (ψ : adjointGroup Tag.F4 K →* X) (G0 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥) (g0 : ModGL Tag.F4 L) :
    G0 →* ModGL Tag.F4 L :=
  (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjointGroup Tag.F4 L).subtype.comp (iotaF4 (L := L) ψ G0 hG0 hker hcenter))

noncomputable def ThetaF4
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (g0 : ModGL Tag.F4 L) : B1 →* ModGL Tag.F4 L :=
  (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjointGroup Tag.F4 L).subtype.comp
      (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner))

@[simp] theorem etaF4_apply
    (ψ : adjointGroup Tag.F4 K →* X) (G0 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥) (g0 : ModGL Tag.F4 L) (y : G0) :
    etaF4 (L := L) ψ G0 hG0 hker hcenter g0 y =
      g0⁻¹ * ((iotaF4 (L := L) ψ G0 hG0 hker hcenter y : adjointGroup Tag.F4 L) :
        ModGL Tag.F4 L) * g0 := by
  rw [etaF4, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change MulAut.conj g0⁻¹
    ((adjointGroup Tag.F4 L).subtype ((iotaF4 (L := L) ψ G0 hG0 hker hcenter) y)) = _
  rw [MulAut.conj_apply]
  simp

@[simp] theorem ThetaF4_apply
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (g0 : ModGL Tag.F4 L) (b : B1) :
    ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 b =
      g0⁻¹ * ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b :
        adjointGroup Tag.F4 L) : ModGL Tag.F4 L) * g0 := by
  rw [ThetaF4, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change MulAut.conj g0⁻¹
    ((adjointGroup Tag.F4 L).subtype
      ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner) b)) = _
  rw [MulAut.conj_apply]
  simp

noncomputable def langDatumF4
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w) :
    LangDatum Tag.F4 L :=
  LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C (by
    have h1 : Units.map (entrywiseHom Fr) g0 =
        ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
          ModGL Tag.F4 L) := by
      rw [frobF4_apply_coe, bcGL, bcEndHom_eq_entrywiseHom]
    rw [h1, hg0])

@[simp] theorem langDatumF4_n
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w) :
    (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).n =
      canonicalRep (coxeterSystem Tag.F4) L w :=
  rfl

@[simp] theorem langDatumF4_g0
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w) :
    (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).g0 = g0 :=
  rfl

@[simp] theorem langDatumF4_Phi
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w) :
    (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).Φ =
      Units.map (entrywiseHom Fr) :=
  rfl

theorem frobF4_coe_eq_unitsMap
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (g : adjointGroup Tag.F4 L) :
    ((frobF4 (K := K) (L := L) Fr hFr g : adjointGroup Tag.F4 L) : ModGL Tag.F4 L) =
      Units.map (entrywiseHom Fr) (g : ModGL Tag.F4 L) := by
  rw [frobF4_apply_coe, bcGL, bcEndHom_eq_entrywiseHom]

theorem jF4_range_eq
    (K L : Type) [Field K] [Finite K] [Field L] [Algebra K L] :
    (jF4 (K := K) (L := L)).range.map (adjointGroup Tag.F4 L).subtype =
      (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K L)) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, rfl⟩ := hz
    exact ⟨u, u.2, jF4_apply u⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨jF4 (K := K) (L := L) ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, jF4_apply _⟩

theorem etaF4_range_model
    (ψ : adjointGroup Tag.F4 K →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w) :
    (etaF4 (L := L) ψ G0 hG0 hker hcenter g0).range =
      (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).model := by
  classical
  set F := frobF4 (K := K) (L := L) Fr hFr with hF
  set n : ModGL Tag.F4 L := canonicalRep (coxeterSystem Tag.F4) L w with hn
  set D := langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0 with hD
  have hFg0 : Units.map (entrywiseHom Fr) g0 = g0 * n := by
    rw [← frobF4_coe_eq_unitsMap Fr hFr ⟨g0, hg0C⟩, hg0]
  have hPhi_iota : ∀ y : G0,
      Units.map (entrywiseHom Fr)
          ((iotaF4 (L := L) ψ G0 hG0 hker hcenter y : adjointGroup Tag.F4 L) :
            ModGL Tag.F4 L) =
        ((iotaF4 (L := L) ψ G0 hG0 hker hcenter y : adjointGroup Tag.F4 L) :
          ModGL Tag.F4 L) := by
    intro y
    rw [← frobF4_coe_eq_unitsMap Fr hFr (iotaF4 (L := L) ψ G0 hG0 hker hcenter y)]
    exact congrArg Subtype.val (frobF4_iotaF4 Fr hFr ψ G0 hG0 hker hcenter y)
  have hstep_mem : ∀ y : G0, D.n * D.Φ (etaF4 (L := L) ψ G0 hG0 hker hcenter g0 y) *
      D.n⁻¹ = etaF4 (L := L) ψ G0 hG0 hker hcenter g0 y := by
    intro y
    rw [etaF4_apply, langDatumF4_n, langDatumF4_Phi, ← hn]
    rw [map_mul, map_mul, map_inv, hFg0, hPhi_iota y]
    group
  have hrange_le : (etaF4 (L := L) ψ G0 hG0 hker hcenter g0).range ≤ D.model := by
    rintro z ⟨y, rfl⟩
    rw [LangDatum.mem_model]
    refine ⟨?_, ?_⟩
    · have h1 : g0⁻¹ ∈ adjointGroup Tag.F4 L := Subgroup.inv_mem _ hg0C
      have h2 : ((iotaF4 (L := L) ψ G0 hG0 hker hcenter y : adjointGroup Tag.F4 L) :
          ModGL Tag.F4 L) ∈ adjointGroup Tag.F4 L :=
        (iotaF4 (L := L) ψ G0 hG0 hker hcenter y).2
      have h3 := Subgroup.mul_mem (adjointGroup Tag.F4 L)
        (Subgroup.mul_mem (adjointGroup Tag.F4 L) h1 h2) hg0C
      simpa [etaF4_apply] using h3
    · have hstep : D.step (etaF4 (L := L) ψ G0 hG0 hker hcenter g0 y) =
          etaF4 (L := L) ψ G0 hG0 hker hcenter g0 y := by
        simp only [LangDatum.step, MonoidHom.comp_apply]
        exact hstep_mem y
      exact hstep
  refine le_antisymm hrange_le ?_
  intro z hz
  rw [LangDatum.mem_model] at hz
  obtain ⟨hzadj, hzstep⟩ := hz
  set a : ModGL Tag.F4 L := g0 * z * g0⁻¹ with ha
  have haadj : a ∈ adjointGroup Tag.F4 L :=
    Subgroup.mul_mem (adjointGroup Tag.F4 L)
      (Subgroup.mul_mem (adjointGroup Tag.F4 L) hg0C hzadj)
      (Subgroup.inv_mem _ hg0C)
  have hzstep' : n * Units.map (entrywiseHom Fr) z * n⁻¹ = z := by
    have h := hzstep
    rw [langDatumF4_n, langDatumF4_Phi, ← hn] at h
    exact h
  have hPhia : Units.map (entrywiseHom Fr) a = a := by
    calc Units.map (entrywiseHom Fr) a
        = Units.map (entrywiseHom Fr) g0 * Units.map (entrywiseHom Fr) z *
            (Units.map (entrywiseHom Fr) g0)⁻¹ := by
          rw [ha, map_mul, map_mul, map_inv]
      _ = (g0 * n) * Units.map (entrywiseHom Fr) z * (g0 * n)⁻¹ := by rw [hFg0]
      _ = g0 * (n * Units.map (entrywiseHom Fr) z * n⁻¹) * g0⁻¹ := by group
      _ = g0 * z * g0⁻¹ := by rw [hzstep']
      _ = a := rfl
  have hamap : a ∈ (adjointGroup Tag.F4 K).map
      (bcGL (τ := Tag.F4) (algebraMap K L)) := by
    rw [f4_finite_field_fixed_eq_map (K := K) (Ω := L) Fr hFr]
    exact Subgroup.mem_inf.2 ⟨haadj, hPhia⟩
  have hamap' : a ∈ (jF4 (K := K) (L := L)).range.map
      (adjointGroup Tag.F4 L).subtype := by
    rw [jF4_range_eq K L]
    exact hamap
  obtain ⟨z', hz', hz'a⟩ := hamap'
  have haz : z' = ⟨a, haadj⟩ := Subtype.ext hz'a
  have hairange : (⟨a, haadj⟩ : adjointGroup Tag.F4 L) ∈
      (iotaF4 (L := L) ψ G0 hG0 hker hcenter).range := by
    rw [FixedImage.iotaF4_range (K := K) (Ω := L) ψ G0 hG0 hker hcenter]
    simpa [haz] using hz'
  obtain ⟨y, hy⟩ := hairange
  refine ⟨y, ?_⟩
  rw [etaF4_apply, hy]
  simp only [ha]
  group

theorem etaF4_action
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (g0 : ModGL Tag.F4 L) (b : B1) (y : G0) :
    etaF4 (L := L) ψ G0 hG0 hker hcenter g0
        ((G0.normalizerMonoidHom ⟨b, hBN b.property⟩) y) =
      ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 b *
        etaF4 (L := L) ψ G0 hG0 hker hcenter g0 y *
        (ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 b)⁻¹ := by
  rw [etaF4_apply, ThetaF4_apply,
    iotaF4_normalizer (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b y]
  rw [etaF4_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem ThetaF4_ker
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (g0 : ModGL Tag.F4 L) :
    (ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0).ker =
      (Subgroup.centralizer (G0 : Set X)).subgroupOf B1 := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hconj : (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b :
        adjointGroup Tag.F4 L) = 1 := by
      have h' := h
      rw [ThetaF4_apply] at h'
      have : g0⁻¹ * ((thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b :
          adjointGroup Tag.F4 L) : ModGL Tag.F4 L) * g0 = 1 := h'
      have h2 := congrArg (fun t : ModGL Tag.F4 L => g0 * t * g0⁻¹) this
      simpa [mul_assoc] using h2
    have hk := thetaF4_ker (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner
    have hbker : b ∈ (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner).ker := by
      rw [MonoidHom.mem_ker]; exact hconj
    rw [hk, betaF4_ker ψ G0 B1 hG0 hker hcenter hBN hinner] at hbker
    exact Subgroup.mem_subgroupOf.mp hbker
  · intro hb
    rw [ThetaF4_apply]
    have hk := thetaF4_ker (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner
    have hbker : b ∈ (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner).ker := by
      rw [hk, betaF4_ker ψ G0 B1 hG0 hker hcenter hBN hinner]
      exact Subgroup.mem_subgroupOf.mpr hb
    rw [MonoidHom.mem_ker] at hbker
    rw [hbker]
    change g0⁻¹ * (1 : ModGL Tag.F4 L) * g0 = 1
    group

theorem iotaF4_injective
    (ψ : adjointGroup Tag.F4 K →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥) :
    Function.Injective (iotaF4 (L := L) ψ G0 hG0 hker hcenter) := by
  intro a b hab
  obtain ⟨u, rfl⟩ := (eF4 ψ G0 hG0 hker hcenter).surjective a
  obtain ⟨v, rfl⟩ := (eF4 ψ G0 hG0 hker hcenter).surjective b
  have huv : u = v := by
    apply jF4_injective (K := K) (L := L)
    rw [← iotaF4_e ψ G0 hG0 hker hcenter u,
      ← iotaF4_e ψ G0 hG0 hker hcenter v]
    exact hab
  rw [huv]

theorem etaF4_injective
    (ψ : adjointGroup Tag.F4 K →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥) (g0 : ModGL Tag.F4 L) :
    Function.Injective (etaF4 (L := L) ψ G0 hG0 hker hcenter g0) := by
  intro x y h
  rw [etaF4_apply, etaF4_apply] at h
  apply iotaF4_injective (L := L) ψ G0 hG0 hker hcenter
  apply Subtype.ext
  have h' := congrArg (fun t : ModGL Tag.F4 L => g0 * t * g0⁻¹) h
  simpa [mul_assoc] using h'

end CFSG.StandardType.F4ExplicitPos.ComponentAttach
end

end
