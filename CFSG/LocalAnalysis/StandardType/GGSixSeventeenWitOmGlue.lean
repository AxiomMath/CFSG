module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmMain
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmExcl
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

namespace SevOm

open CFSG.Assembly Multiplicative

section Transport

variable {H G : Type} [Group H] [Group G] {Ω : Subgroup H} {φ : ↥Ω →* G}

theorem map_centralizer (hφ : Function.Injective φ) (a : ↥Ω) :
    (Subgroup.centralizer ({a} : Set ↥Ω)).map φ =
      φ.range ⊓ Subgroup.centralizer {φ a} := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, hφ (by rw [map_mul, map_mul]; exact hy), rfl⟩

theorem map_subtype_centralizer (a : ↥Ω) :
    (Subgroup.centralizer ({a} : Set ↥Ω)).map Ω.subtype =
      Ω ⊓ Subgroup.centralizer {(a : H)} := by
  have := map_centralizer (φ := Ω.subtype) Ω.subtype_injective a
  rwa [Subgroup.range_subtype] at this

theorem isComponentOf_transport (hφ : Function.Injective φ) (a : ↥Ω) {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer {φ a})) :
    IsComponentOf ((L₁.comap φ).map Ω.subtype) (Ω ⊓ Subgroup.centralizer {(a : H)}) ∧
      (L₁.comap φ).map φ = L₁ := by
  rw [← map_centralizer hφ a] at hL₁
  obtain ⟨h1, h2⟩ := isComponentOf_comap_of_injective φ hφ hL₁
  have h3 := isComponentOf_map_of_injective Ω.subtype Ω.subtype_injective h1
  rw [map_subtype_centralizer] at h3
  exact ⟨h3, h2⟩

theorem isComponentOf_transport' (hφ : Function.Injective φ) (a : ↥Ω) {L₂ : Subgroup H}
    (hL₂ : IsComponentOf L₂ (Ω ⊓ Subgroup.centralizer {(a : H)})) :
    IsComponentOf ((L₂.comap Ω.subtype).map φ) (φ.range ⊓ Subgroup.centralizer {φ a}) ∧
      (L₂.comap Ω.subtype).map Ω.subtype = L₂ := by
  rw [← map_subtype_centralizer a] at hL₂
  obtain ⟨h1, h2⟩ := isComponentOf_comap_of_injective Ω.subtype Ω.subtype_injective hL₂
  have h3 := isComponentOf_map_of_injective φ hφ h1
  rw [map_centralizer hφ a] at h3
  exact ⟨h3, h2⟩

theorem card_inf_centralizer_le [Finite G] [Finite H] (hφ : Function.Injective φ)
    {A : Subgroup H} {Bs : Subgroup G} (hBφ : Bs ≤ φ.range)
    (hAB : ∀ g : ↥Ω, (g : H) ∈ A ↔ φ g ∈ Bs) {L₂ : Subgroup H} (hL₂ : L₂ ≤ Ω) :
    Nat.card (Bs ⊓ Subgroup.centralizer (((L₂.comap Ω.subtype).map φ : Subgroup G) : Set G) :
      Subgroup G) ≤ Nat.card (A ⊓ Subgroup.centralizer (L₂ : Set H) : Subgroup H) := by
  classical
  have hex : ∀ b : ↥(Bs ⊓ Subgroup.centralizer
      (((L₂.comap Ω.subtype).map φ : Subgroup G) : Set G)), ∃ g : ↥Ω, φ g = b :=
    fun b => hBφ (Subgroup.mem_inf.mp b.2).1
  choose σ hσ using hex
  have hmem : ∀ b, ((σ b : ↥Ω) : H) ∈ A ⊓ Subgroup.centralizer (L₂ : Set H) := by
    intro b
    refine Subgroup.mem_inf.mpr ⟨(hAB _).mpr (by rw [hσ]; exact (Subgroup.mem_inf.mp b.2).1),
      Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp b.2).2 (φ ⟨l, hL₂ hl⟩)
      ⟨⟨l, hL₂ hl⟩, hl, rfl⟩
    rw [← hσ b, ← map_mul, ← map_mul] at hc
    exact congrArg Subtype.val (hφ hc)
  refine Nat.card_le_card_of_injective (fun b => ⟨_, hmem b⟩) fun b b' hbb => ?_
  have h0 := congrArg (fun z : ↥(A ⊓ Subgroup.centralizer (L₂ : Set H)) => (z : H)) hbb
  have h1 : σ b = σ b' := Subtype.ext h0
  apply Subtype.ext
  rw [← hσ b, ← hσ b', h1]

end Transport

section Model

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.KCOrthComm CFSG.RankThree.Classical2 NoOffOm CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem witness_of_matrixModel {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} (htL : t ≠ .PSL) (htU : t ≠ .PSU) {f : ℕ}
    (hf : 1 ≤ f) {d : ℕ} {Q : QuadraticForm (GaloisField 2 f) (Fin d → GaloisField 2 f)}
    (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule (GaloisField 2 f) (Fin d → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (φ : matrixDerived Q →* G) (hφ : Function.Injective φ) (hrange : φ.range = ggG0 p B x L D J)
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : GGBstar p B Bs) (hBφ : Bs ≤ φ.range)
    (hcard : p ^ 4 ≤ Nat.card Bs) (hres : ¬ ((f = 1 ∧ p = 3) ∨ (f = 2 ∧ p = 5)))
    {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}))
    (hpL : p ∣ Nat.card L₁) :
    ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e ∨
      (e ∈ Bs ∧ e ≠ 1 ∧ GGSixSeventeenSixteen p B Bs x L D J t f e) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hp5 : p = 5 → f ≠ 2 := fun h5 h2 => hres (Or.inr ⟨h2, h5⟩)
  have hA := genMax_of_orth hnd hT hp hp2 hBs.2.1 hBs.2.2.2 φ hφ hBφ
  obtain ⟨r, ⟨F⟩⟩ := exists_frame_of_genMax hA
  set A := ((Bs.comap φ).map (matrixDerived Q).subtype).map
    (matrixLinearIso (d := d) (K := GaloisField 2 f)).toMonoidHom with hAdef
  set Ω := orthDerived Q with hΩ
  set φV : ↥Ω →* G := φ.comp (matrixDerivedEquiv Q).symm.toMonoidHom with hφVdef
  have hφV : Function.Injective φV := hφ.comp (matrixDerivedEquiv Q).symm.injective
  have hφVr : φV.range = φ.range := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨X, rfl⟩
      exact ⟨matrixDerivedEquiv Q X, by simp [hφVdef]⟩
  have : Finite ((Fin d → GaloisField 2 f) ≃ₗ[GaloisField 2 f] (Fin d → GaloisField 2 f)) :=
    CFSG.RankThree.PartOne.KCOrthComm.finite_linearEquiv
  have hAB : ∀ g : ↥Ω, ((g : ↥Ω) : (Fin d → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      (Fin d → GaloisField 2 f)) ∈ A ↔ φV g ∈ Bs := by
    intro g
    constructor
    · rintro ⟨_, ⟨Y, hY, rfl⟩, hYg⟩
      have hYg' : (matrixDerivedEquiv Q).symm g = Y := by
        apply (matrixDerivedEquiv Q).injective
        rw [MulEquiv.apply_symm_apply]
        exact Subtype.ext hYg.symm
      show φ ((matrixDerivedEquiv Q).symm g) ∈ Bs
      rw [hYg']
      exact hY
    · intro hg
      exact ⟨((matrixDerivedEquiv Q).symm g).1, ⟨(matrixDerivedEquiv Q).symm g, hg, rfl⟩, by
        have h1 := coe_matrixDerivedEquiv Q ((matrixDerivedEquiv Q).symm g)
        rw [MulEquiv.apply_symm_apply] at h1
        exact h1.symm⟩
  have hAΩ : A ≤ Ω := by
    rintro _ ⟨_, ⟨Y, -, rfl⟩, rfl⟩
    have h1 := (matrixDerivedEquiv Q Y).2
    rwa [coe_matrixDerivedEquiv] at h1
  have hBφV : Bs ≤ φV.range := hφVr ▸ hBφ
  have hmax : ∀ g ∈ Ω, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine (hAB ⟨g, hg⟩).mpr (hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_) ?_)
    · obtain ⟨c, rfl⟩ := hBφV hy
      have h1 := hgc c ((hAB c).mpr hy)
      rw [← map_mul, ← map_mul]
      exact congrArg φV (Subtype.ext h1.symm)
    · rw [← map_pow]
      have h1 : (⟨g, hg⟩ : ↥Ω) ^ p = 1 := Subtype.ext (by simpa using hgp)
      rw [h1, map_one]
  have hr : 4 ≤ r := by
    have hcA : Nat.card A = p ^ r := by
      rw [← F.range, Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv.symm,
        Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hle : Nat.card Bs ≤ Nat.card A := by
      have hex : ∀ y : Bs, ∃ g : ↥Ω, φV g = y := fun y => hBφV y.2
      choose σ hσ using hex
      refine Nat.card_le_card_of_injective (fun y => ⟨σ y, (hAB _).mpr (by rw [hσ]; exact y.2)⟩)
        fun y y' hyy => ?_
      have h0 := congrArg (fun z : A => (z : (Fin d → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin d → GaloisField 2 f))) hyy
      have h1 : σ y = σ y' := Subtype.ext h0
      exact Subtype.ext (by rw [← hσ y, ← hσ y', h1])
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard.trans (hle.trans hcA.le))
  obtain ⟨a', rfl⟩ := hBφV hb
  obtain ⟨s₀, hs₀⟩ := F.exists_eq ((hAB a').mpr hb)
  rw [← hrange, ← hφVr] at hL₁
  obtain ⟨hL, hmapL⟩ := isComponentOf_transport hφV a' hL₁
  rw [← hs₀] at hL
  have hpL' : p ∣ Nat.card ((L₁.comap φV).map Ω.subtype) := by
    rw [Subgroup.card_map_of_injective Ω.subtype_injective,
      ← Subgroup.card_map_of_injective hφV, hmapL]
    exact hpL
  have hG₀ : φV.range = ggG0 p B x L D J := hφVr.trans hrange
  have hdir : ∀ z : ↥Ω, ((z : ↥Ω) : (Fin d → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      (Fin d → GaloisField 2 f)) ∈ A → z ≠ 1 → ∀ M,
      IsComponentOf M (Ω ⊓ Subgroup.centralizer {((z : ↥Ω) : (Fin d → GaloisField 2 f) ≃ₗ[
        GaloisField 2 f] (Fin d → GaloisField 2 f))}) →
      Nat.card (A ⊓ Subgroup.centralizer (M : Set ((Fin d → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin d → GaloisField 2 f))) : Subgroup _) ≤ p ^ 2 →
      GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) (φV z) := by
    intro z hzA hz1 M hM hMc
    refine ⟨(hAB z).mp hzA, fun h => hz1 (hφV (h.trans (map_one φV).symm)),
      Or.inr ⟨(M.comap Ω.subtype).map φV, ?_, ?_⟩⟩
    · have h1 := (isComponentOf_transport' hφV z hM).1
      rwa [hG₀] at h1
    · exact (card_inf_centralizer_le hφV hBφV hAB (hM.1.trans inf_le_left)).trans hMc
  rcases exists_witness_orth hnd hp hp2 hAΩ F hr hmax s₀ hL hpL' with
    ⟨e, heL, heA, he1, L₂, hL₂, hcard₂⟩ |
      ⟨hK2', e, heL, heA, he1, L₂, L₃, hL₂, hL₃, ⟨e₂⟩, ⟨e₃⟩, e', he'mem, he'A, he'1, L₄, hL₄,
        hcard₄⟩ |
      hK2
  · obtain ⟨y, hy, rfl⟩ := heL
    exact ⟨φV y, hy, Or.inl (hdir y heA (fun h => he1 (by rw [h]; rfl)) L₂ hL₂ hcard₂)⟩
  · obtain ⟨y, hy, rfl⟩ := heL
    have hf2 : 2 ≤ f := by
      by_contra h
      have hf1 : f = 1 := by omega
      rw [hK, hf1, pow_one] at hK2'
      exact hK2' rfl
    have hy1 : y ≠ 1 := fun h => he1 (by rw [h]; rfl)
    have heBs : φV y ∈ Bs := (hAB y).mp heA
    have he1' : φV y ≠ 1 := fun h => hy1 (hφV (h.trans (map_one φV).symm))
    have hnex : ∀ M : Subgroup ((Fin d → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin d → GaloisField 2 f)), M ≤ Ω → Nonempty (↥M ≃* SL(2, GaloisField 2 f)) →
        ¬ GGSixSeventeenExcluded p t f ((M.comap Ω.subtype).map φV) := by
      rintro M hM ⟨eM⟩
      have hMr : M ≤ Ω.subtype.range := by rwa [Subgroup.range_subtype]
      refine WitOm.not_ggSixSeventeenExcluded_SL2 hK hf2 htL htU hp5
        (((M.comap Ω.subtype).equivMapOfInjective φV hφV).symm.trans
          ((((M.comap Ω.subtype).equivMapOfInjective Ω.subtype Ω.subtype_injective).trans
            (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hMr))).trans eM))
    have hT₂ := (isComponentOf_transport' hφV y hL₂).1
    have hT₃ := (isComponentOf_transport' hφV y hL₃).1
    rw [hG₀] at hT₂ hT₃
    have hL₂Ω : L₂ ≤ Ω := hL₂.1.trans inf_le_left
    have hL₃Ω : L₃ ≤ Ω := hL₃.1.trans inf_le_left
    set e'' : ↥Ω := ⟨e', hAΩ he'A⟩ with he''
    have he''mem : e'' ∈ L₂.comap Ω.subtype ⊔ L₃.comap Ω.subtype := by
      have hX : (L₂.comap Ω.subtype ⊔ L₃.comap Ω.subtype).map Ω.subtype = L₂ ⊔ L₃ := by
        rw [Subgroup.map_sup,
          Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype] : L₂ ≤ Ω.subtype.range),
          Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype] : L₃ ≤ Ω.subtype.range)]
      rw [← hX] at he'mem
      obtain ⟨z, hz, hze⟩ := he'mem
      have : z = e'' := Subtype.ext hze
      rw [← this]
      exact hz
    refine ⟨φV y, hy, Or.inr ⟨heBs, he1', _, _, ⟨heBs, he1', hT₂, hnex L₂ hL₂Ω ⟨e₂⟩⟩,
      ⟨heBs, he1', hT₃, hnex L₃ hL₃Ω ⟨e₃⟩⟩, φV e'', ?_, ?_⟩⟩
    · rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem φV he''mem
    · exact hdir e'' he'A (fun h => he'1 (congrArg Subtype.val h)) L₄ hL₄ hcard₄
  · exfalso
    obtain ⟨hK2, hp3⟩ := hK2
    rw [hK] at hK2
    have : f = 1 := Nat.pow_right_injective le_rfl (hK2.trans (pow_one 2).symm)
    exact hres (Or.inl ⟨this, hp3⟩)

end Model

end SevOm

end CFSG.StandardType
