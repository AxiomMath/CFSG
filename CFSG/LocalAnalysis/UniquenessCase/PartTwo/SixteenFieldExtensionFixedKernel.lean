module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Out
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionKernelCardinality
public import CFSG.LinearAlgebra.SL2CharTwoScalar
public import CFSG.ClassicalGroups.Symplectic.InvariantForm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Stroth80
open Matrix
open scoped Matrix

variable {W : Type} [CommGroup W]
variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem exists_faithful_nat_hom_of_isCoord
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {A H : Subgroup (MulAut W)}
    (hHA : H ≤ A)
    (hAn : A ≤ Subgroup.normalizer (H : Set (MulAut W)))
    {π : Γ →* H} {f : W → (ι → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat Γ) H (fixV H) π f)
    (hcomm : commSub ⊤ H = ⊤) :
    ∃ ρ : A →* MulAut (Multiplicative (ι → K)),
      Function.Injective ρ ∧
      (∀ (a : A) (w : W),
        ρ a (Multiplicative.ofAdd (f w)) =
          Multiplicative.ofAdd (f ((a : MulAut W) w))) ∧
      ρ.comp ((Subgroup.inclusion hHA).comp π) =
        (s16gNatHom ι K).comp Γ.subtype ∧
      (H.subgroupOf A).map ρ = Γ.map (s16gNatHom ι K) ∧
      (∀ a : A, ρ a ∈ s16gNorm Γ) := by
  classical
  let β : W →* Multiplicative (ι → K) := hf.toHom
  have hβs : Function.Surjective β := by
    intro y
    obtain ⟨w, hw⟩ := hf.surj (Multiplicative.toAdd y)
    exact ⟨w, by
      show Multiplicative.ofAdd (f w) = y
      rw [hw]
      rfl⟩
  have hβone : ∀ w : W, β w = 1 ↔ f w = 0 := by
    intro w
    constructor
    · intro h
      have := congrArg Multiplicative.toAdd h
      simpa [β, KGNat.IsCoord.toHom] using this
    · intro h
      rw [show β w = Multiplicative.ofAdd (f w) from rfl, h]
      rfl
  have hβk : ∀ w : W, β w = 1 ↔ w ∈ fixV H := by
    intro w
    rw [hβone w, hf.ker]
  have hπsurj : Function.Surjective π := hf.onto
  have hpres : ∀ (a : A) (w : W), β w = 1 ↔ β ((a : MulAut W) w) = 1 := by
    intro a w
    rw [hβk w, hβk ((a : MulAut W) w)]
    exact (FixVLat.le_stabSub_fixV_of_le_normalizer hAn a.2 w).symm
  choose ρ₀ hρ₀ using fun a : A => s16g_exists_induced_aut β hβs (hpres a)
  have hρ₀_mul : ∀ a b : A, ρ₀ (a * b) = ρ₀ a * ρ₀ b := by
    intro a b
    ext y
    obtain ⟨w, rfl⟩ := hβs y
    rw [hρ₀ (a * b) w, MulAut.mul_apply, hρ₀ b w, hρ₀ a ((b : MulAut W) w)]
    simp
  let ρ : A →* MulAut (Multiplicative (ι → K)) := MonoidHom.mk' ρ₀ hρ₀_mul
  have hρ : ∀ (a : A) (w : W), ρ a (β w) = β ((a : MulAut W) w) := fun a w => hρ₀ a w
  have hπβ : ∀ (γ : Γ) (w : W), β (((π γ : ↥H) : MulAut W) w) =
      s16gNatHom ι K (γ : GL ι K) (β w) := by
    intro γ w
    have hact : f (((π γ : ↥H) : MulAut W) w) =
        (KGNat.linModelNat Γ).lin γ (f w) := hf.act γ w
    change Multiplicative.ofAdd (f (((π γ : ↥H) : MulAut W) w)) =
      s16gNatHom ι K (γ : GL ι K) (Multiplicative.ofAdd (f w))
    rw [hact, KGNat.linModelNat_lin, s16gNatHom_apply]
    rfl
  have hρπ : ∀ γ : Γ, ρ ⟨π γ, hHA (π γ).2⟩ = s16gNatHom ι K (γ : GL ι K) := by
    intro γ
    ext y
    obtain ⟨w, rfl⟩ := hβs y
    rw [hρ, hπβ γ w]
  have hcomp : ρ.comp ((Subgroup.inclusion hHA).comp π) =
      (s16gNatHom ι K).comp Γ.subtype :=
    MonoidHom.ext fun γ => hρπ γ
  have hmap : (H.subgroupOf A).map ρ = Γ.map (s16gNatHom ι K) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haH : (a : MulAut W) ∈ H := Subgroup.mem_subgroupOf.mp ha
      obtain ⟨γ, hγ⟩ := hπsurj ⟨(a : MulAut W), haH⟩
      refine Subgroup.mem_map.mpr ⟨γ, γ.2, ?_⟩
      have hsub : (⟨π γ, hHA (π γ).2⟩ : ↥A) = a := by
        rw [hγ]
      rw [← hρπ γ, hsub]
    · rintro ⟨γ, hγ, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨⟨π ⟨γ, hγ⟩, hHA (π ⟨γ, hγ⟩).2⟩,
          Subgroup.mem_subgroupOf.mpr (π ⟨γ, hγ⟩).2, hρπ ⟨γ, hγ⟩⟩
  have hconj : ∀ (b : A) (x : MulAut (Multiplicative (ι → K))),
      x ∈ Γ.map (s16gNatHom ι K) → ρ b * x * (ρ b)⁻¹ ∈ Γ.map (s16gNatHom ι K) := by
    intro b x hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
    have hmemH : (b : MulAut W) * ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) * (b : MulAut W)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (hAn b.2) ((π ⟨γ, hγ⟩ : ↥H) : MulAut W)).1
        (π ⟨γ, hγ⟩).2
    obtain ⟨γ', hγ'⟩ := hπsurj ⟨_, hmemH⟩
    refine Subgroup.mem_map.mpr ⟨γ', γ'.2, ?_⟩
    have hsub : (⟨π γ', hHA (π γ').2⟩ : ↥A) =
        b * ⟨π ⟨γ, hγ⟩, hHA (π ⟨γ, hγ⟩).2⟩ * b⁻¹ := by
      apply Subtype.ext
      rw [hγ']
      rfl
    rw [← hρπ γ', hsub]
    simp only [map_mul, map_inv, hρπ ⟨γ, hγ⟩]
  have hnorm : ∀ a : A, ρ a ∈ s16gNorm Γ := by
    intro a
    rw [s16gNorm, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj a x
    · intro hx
      have h1 : ρ a⁻¹ * (ρ a * x * (ρ a)⁻¹) * (ρ a⁻¹)⁻¹ ∈
          Γ.map (s16gNatHom ι K) := hconj a⁻¹ _ hx
      have heq : ρ a⁻¹ * (ρ a * x * (ρ a)⁻¹) * (ρ a⁻¹)⁻¹ = x := by
        rw [map_inv]
        group
      rwa [heq] at h1
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hHinj : ∀ h : ↥H, ρ ⟨h, hHA h.2⟩ = 1 → h = 1 := by
      intro h hh
      obtain ⟨γ, hγ⟩ := hπsurj h
      have hj : s16gNatHom ι K (γ : GL ι K) = 1 := by
        rw [← hρπ γ]
        have hsub : (⟨π γ, hHA (π γ).2⟩ : ↥A) = ⟨h, hHA h.2⟩ := by
          apply Subtype.ext
          rw [hγ]
        rw [hsub, hh]
      have hγ1 : γ = 1 := by
        apply Subtype.ext
        apply s16gNatHom_injective
        simpa using hj
      have hπγ : π γ = 1 := by rw [hγ1, map_one]
      rw [← hγ, hπγ]
    have hcent : ∀ h ∈ H, (a : MulAut W) * h = h * (a : MulAut W) := by
      intro h hh
      have hmem : (a : MulAut W) * h * (a : MulAut W)⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff.mp (hAn a.2) h).1 hh
      have hcH : (a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹ ∈ H :=
        H.mul_mem hmem (H.inv_mem hh)
      have hc1 : ρ ⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hHA hcH⟩ = 1 := by
        have heq : (⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hHA hcH⟩ : ↥A) =
            a * ⟨h, hHA hh⟩ * a⁻¹ * ⟨h, hHA hh⟩⁻¹ := Subtype.ext rfl
        rw [heq]
        simp [map_mul, map_inv, ha]
      have hcW : (a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹ = 1 := by
        have h5 : (⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hcH⟩ : ↥H) = 1 :=
          hHinj ⟨_, hcH⟩ hc1
        exact congrArg Subtype.val h5
      have hconj_eq : (a : MulAut W) * h * (a : MulAut W)⁻¹ = h :=
        mul_inv_eq_one.mp hcW
      calc (a : MulAut W) * h = (a : MulAut W) * h * (a : MulAut W)⁻¹ * (a : MulAut W) := by
            group
        _ = h * (a : MulAut W) := by rw [hconj_eq]
    have hfix : ∀ w : W, (a : MulAut W) w * w⁻¹ ∈ fixV H := by
      intro w
      rw [← hβk ((a : MulAut W) w * w⁻¹), map_mul, map_inv]
      have h1 : β ((a : MulAut W) w) = β w := by
        rw [← hρ a w, ha]
        rfl
      rw [h1, mul_inv_cancel]
    have ha1 : (a : MulAut W) = 1 := s16g_eq_one_of_commSub hcomm hcent hfix
    exact Subtype.ext ha1
  exact ⟨ρ, hinj, fun a w => hρ a w, hcomp, hmap, hnorm⟩

theorem inf_centSub_fixV_eq_of_nat
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {A H : Subgroup (MulAut W)}
    (hHA : H ≤ A)
    (hAn : A ≤ Subgroup.normalizer (H : Set (MulAut W)))
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [Nonempty ι]
    {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ)
    (hreal : (FFModel.nat Γ).Realizes H ⊤ (fixV H))
    (hcomm : commSub ⊤ H = ⊤)
    {p : ℕ} (hp : p.Prime) (hpK : Nat.card K = p + 1) (hpodd : Odd p)
    (hcentral : A ⊓ Subgroup.centralizer (H : Set (MulAut W)) ≠ ⊥)
    (hfix : fixV H ≠ ⊥)
    (hdecomp : ∀ g ∈ Subgroup.normalizer (Γ : Set (GL ι K)),
      ∃ (μ : K) (s : GL ι K), μ ≠ 0 ∧ s ∈ Γ ∧
        ∀ x : ι → K,
          (g : Matrix ι ι K) *ᵥ x = μ • ((s : Matrix ι ι K) *ᵥ x)) :
    A ⊓ centSub (fixV H) = H := by
  classical
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat Γ) hπ
  have hscal : ∀ T : (ι → K) →+ (ι → K),
      (∀ (γ : (FFModel.nat Γ).Gam) (x : ι → K),
        T ((KGNat.linModelNat Γ).lin γ x) = (KGNat.linModelNat Γ).lin γ (T x)) →
      ∃ a : K, ∀ x, T x = a • x := by
    intro T hT
    refine hΓ T (fun A _ v => ?_)
    have h := hT ⟨A, by assumption⟩ v
    simpa only [KGNat.linModelNat_lin] using h
  obtain ⟨ρ, hρinj, hρcoord, hρcomp, hρmap, hρnorm⟩ :=
    exists_faithful_nat_hom_of_isCoord (Γ := Γ) (π := π) (f := f) hHA hAn hf hcomm
  let Z : Subgroup W := fixV H
  let C : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (H : Set (MulAut W))
  have hCA : ∀ c : ↥C, (c : MulAut W) ∈ A := by
    intro c
    have h : (c : MulAut W) ∈ A ⊓ Subgroup.centralizer (H : Set (MulAut W)) := by
      simpa only [C] using c.2
    exact h.1
  have hCC : ∀ c : ↥C, (c : MulAut W) ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
    intro c
    have h : (c : MulAut W) ∈ A ⊓ Subgroup.centralizer (H : Set (MulAut W)) := by
      simpa only [C] using c.2
    exact h.2
  have hmain := card_centralizer_eq_and_modFix_eq_bot_of_extension
    (W := W) (A := A) (H := H) (K := K) (M := ι → K)
    (D := FFModel.nat Γ) (LM := KGNat.linModelNat Γ)
    hW ⟨π, hπ⟩ hcomm hp hpK hpodd hcentral hscal
  change Nat.card ↥C = p ∧ modFix C (⊤ : Subgroup W) = ⊥ at hmain
  obtain ⟨hCcard, hCbot⟩ := hmain
  obtain ⟨χ, hχinj, hχeq⟩ :=
    exists_scalar_hom_of_isCoord (D := FFModel.nat Γ) (K := K) (M := ι → K)
      (LM := KGNat.linModelNat Γ) hf hcomm hscal
  let ιC : ↥C →* ↥(Subgroup.centralizer (H : Set (MulAut W))) :=
    Subgroup.inclusion (inf_le_right : C ≤ Subgroup.centralizer (H : Set (MulAut W)))
  let χC : ↥C →* Kˣ := χ.comp ιC
  have hχCinj : Function.Injective χC := hχinj.comp (Subgroup.inclusion_injective _)
  have hχCeq : ∀ (c : ↥C) (w : W), f ((c : MulAut W) w) = (χC c : K) • f w :=
    fun c w => hχeq (ιC c) w
  have hcardC : Nat.card ↥C = Nat.card Kˣ := by
    rw [hCcard, Nat.card_units, hpK]
    omega
  have hχCsurj : Function.Surjective χC :=
    Function.Injective.surjective_of_finite (Finite.card_eq.mp hcardC).some hχCinj
  have hstabC : C ≤ stabSub Z :=
    FixVLat.le_stabSub_fixV_of_le_normalizer
      ((inf_le_right : C ≤ Subgroup.centralizer (H : Set (MulAut W))).trans
        (Subgroup.centralizer_le_normalizer (H : Set (MulAut W))))
  have hCZ : C ⊓ centSub Z = ⊥ := by
    have hfact : Fact (Nat.card ↥C).Prime := ⟨by rw [hCcard]; exact hp⟩
    let D : Subgroup ↥C := (C ⊓ centSub Z).subgroupOf C
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (hp := hfact) D with hbot | htop
    · rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxD : (⟨x, hx.1⟩ : ↥C) ∈ D := Subgroup.mem_subgroupOf.mpr hx
      rw [hbot] at hxD
      have hx1 : (⟨x, hx.1⟩ : ↥C) = 1 := by simpa using hxD
      exact congrArg Subtype.val hx1
    · exfalso
      have hCle : C ≤ centSub Z := by
        intro c hc
        have hcD : (⟨c, hc⟩ : ↥C) ∈ D := by rw [htop]; trivial
        exact (Subgroup.mem_subgroupOf.mp hcD).2
      have hZle : Z ≤ modFix C (⊤ : Subgroup W) := by
        intro z hz
        rw [show modFix C (⊤ : Subgroup W) = XMod.fixed ↥C ⊤ from rfl, XMod.mem_fixed]
        refine ⟨trivial, fun c => ?_⟩
        have hc : (c : MulAut W) ∈ centSub Z := hCle c.2
        rw [mem_centSub] at hc
        simpa [Subgroup.smul_def, MulAut.smul_def] using hc z hz
      rw [hCbot, le_bot_iff] at hZle
      exact hfix hZle
  have hANc : A ≤ Subgroup.normalizer
      (Subgroup.centralizer (H : Set (MulAut W)) : Set (MulAut W)) :=
    hAn.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (H : Set (MulAut W)))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (H : Set (MulAut W))))
  have hcommC : ∀ a ∈ A ⊓ centSub Z, ∀ c : ↥C,
      (a : MulAut W) * (c : MulAut W) = (c : MulAut W) * (a : MulAut W) := by
    intro a ha c
    have haA : a ∈ A := ha.1
    have haZ : a ∈ centSub Z := ha.2
    have hcA : (c : MulAut W) ∈ A := hCA c
    have hcCent : (c : MulAut W) ∈
        Subgroup.centralizer (H : Set (MulAut W)) := hCC c
    have hcommA : (a : MulAut W) * (c : MulAut W) * (a : MulAut W)⁻¹ * (c : MulAut W)⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem haA hcA) (A.inv_mem haA)) (A.inv_mem hcA)
    have hcommH : (a : MulAut W) * (c : MulAut W) * (a : MulAut W)⁻¹ * (c : MulAut W)⁻¹ ∈
        Subgroup.centralizer (H : Set (MulAut W)) :=
      (Subgroup.centralizer (H : Set (MulAut W))).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hANc haA) (c : MulAut W)).mp hcCent)
        ((Subgroup.centralizer (H : Set (MulAut W))).inv_mem hcCent)
    have hcommZ : (a : MulAut W) * (c : MulAut W) * (a : MulAut W)⁻¹ * (c : MulAut W)⁻¹ ∈
        centSub Z := by
      rw [mem_centSub]
      intro z hz
      have hcinvZ : (c : MulAut W)⁻¹ z ∈ Z := (hstabC (C.inv_mem c.2) z).2 hz
      have hainvZ : (a : MulAut W)⁻¹ ((c : MulAut W)⁻¹ z) = (c : MulAut W)⁻¹ z :=
        mem_centSub.mp ((centSub Z).inv_mem haZ) _ hcinvZ
      have hcz : (c : MulAut W) ((c : MulAut W)⁻¹ z) = z := by simp
      calc ((a : MulAut W) * (c : MulAut W) * (a : MulAut W)⁻¹ * (c : MulAut W)⁻¹) z =
            (a : MulAut W) ((c : MulAut W) ((a : MulAut W)⁻¹ ((c : MulAut W)⁻¹ z))) := by
              simp [MulAut.mul_apply]
        _ = (a : MulAut W) ((c : MulAut W) ((c : MulAut W)⁻¹ z)) := by rw [hainvZ]
        _ = (a : MulAut W) z := by rw [hcz]
        _ = z := (mem_centSub.mp haZ) z hz
    have htriv : (a : MulAut W) * (c : MulAut W) * (a : MulAut W)⁻¹ * (c : MulAut W)⁻¹ = 1 := by
      have hmem : (a : MulAut W) * (c : MulAut W) * (a : MulAut W)⁻¹ * (c : MulAut W)⁻¹ ∈
          C ⊓ centSub Z := ⟨⟨hcommA, hcommH⟩, hcommZ⟩
      rw [hCZ] at hmem
      simpa using hmem
    have hconj : (a : MulAut W) * (c : MulAut W) * (a : MulAut W)⁻¹ = (c : MulAut W) :=
      mul_inv_eq_one.mp htriv
    calc (a : MulAut W) * (c : MulAut W) =
          (a : MulAut W) * (c : MulAut W) * (a : MulAut W)⁻¹ * (a : MulAut W) := by group
      _ = (c : MulAut W) * (a : MulAut W) := by rw [hconj]
  have hzero : ∀ v : Multiplicative (ι → K), s16gSMul (0 : K) v = 1 := by
    intro v
    simp [s16gSMul]
  refine le_antisymm ?_ ?_
  · intro a ha
    have haA : a ∈ A := ha.1
    have haZ : a ∈ centSub Z := ha.2
    let ρa : MulAut (Multiplicative (ι → K)) := ρ ⟨a, haA⟩
    have hρanorm : ρa ∈ s16gNorm Γ := hρnorm ⟨a, haA⟩
    have hscalar : ∀ (c : K) (v : Multiplicative (ι → K)),
        ρa (s16gSMul c v) = s16gSMul c (ρa v) := by
      intro c v
      by_cases hc : c = 0
      · subst hc
        rw [hzero v, hzero (ρa v), map_one]
      · obtain ⟨c0, hc0⟩ := hχCsurj (Units.mk0 c hc)
        have hc0K : (χC c0 : K) = c := by
          have := congrArg Units.val hc0
          simpa using this
        have hρc0 : ∀ v : Multiplicative (ι → K),
            ρ ⟨c0, hCA c0⟩ v = s16gSMul c v := by
          intro v
          obtain ⟨w, hw⟩ := hf.surj (Multiplicative.toAdd v)
          have hv : v = Multiplicative.ofAdd (f w) := by rw [hw]; rfl
          rw [hv, hρcoord ⟨c0, hCA c0⟩ w, hχCeq c0 w, hc0K]
          rfl
        have hcommA : (⟨a, haA⟩ : ↥A) * ⟨c0, hCA c0⟩ = ⟨c0, hCA c0⟩ * ⟨a, haA⟩ := by
          apply Subtype.ext
          exact hcommC a ha c0
        have himg : (ρ ⟨a, haA⟩) * ρ ⟨c0, hCA c0⟩ = ρ ⟨c0, hCA c0⟩ * ρ ⟨a, haA⟩ := by
          rw [← map_mul, ← map_mul, hcommA]
        calc ρa (s16gSMul c v) = ρa (ρ ⟨c0, hCA c0⟩ v) := by rw [hρc0 v]
          _ = (ρa * ρ ⟨c0, hCA c0⟩) v := rfl
          _ = (ρ ⟨c0, hCA c0⟩ * ρa) v := by rw [himg]
          _ = ρ ⟨c0, hCA c0⟩ (ρa v) := rfl
          _ = s16gSMul c (ρa v) := hρc0 (ρa v)
    obtain ⟨θ, hθsem, hθker⟩ := s16g_exists_theta (Γ := Γ) hΓ
    have hθone : θ ⟨ρa, hρanorm⟩ = 1 := by
      ext c
      let v0 : Multiplicative (ι → K) :=
        Multiplicative.ofAdd (Pi.single (Classical.arbitrary ι) (1 : K))
      have hv0 : v0 ≠ 1 := by
        intro h
        have h2 := congrArg
          (fun v : Multiplicative (ι → K) => Multiplicative.toAdd v (Classical.arbitrary ι)) h
        simp [v0] at h2
      have hw : ρa v0 ≠ 1 := by
        intro h
        apply hv0
        apply ρa.injective
        rw [h, map_one]
      have h1 := hθsem ⟨ρa, hρanorm⟩ c v0
      have h2 := hscalar c v0
      have h3 : s16gSMul (θ ⟨ρa, hρanorm⟩ c) (ρa v0) = s16gSMul c (ρa v0) :=
        h1.symm.trans h2
      obtain ⟨i, hi⟩ : ∃ i, Multiplicative.toAdd (ρa v0) i ≠ 0 := by
        by_contra h
        have hzero' : Multiplicative.toAdd (ρa v0) = 0 :=
          funext fun i => not_not.mp (not_exists.mp h i)
        apply hw
        change Multiplicative.ofAdd (Multiplicative.toAdd (ρa v0)) = 1
        rw [hzero']
        rfl
      have h4 := congrArg
        (fun w : Multiplicative (ι → K) => Multiplicative.toAdd w i) h3
      simpa [s16gSMul] using mul_right_cancel₀ hi h4
    have hlin : ρa ∈ s16gLin ι K := (hθker ⟨ρa, hρanorm⟩).1 hθone
    have hlin' : ρa ∈ (s16gNatHom ι K).range := hlin
    obtain ⟨g, hg⟩ := hlin'
    have hgnorm : g ∈ Subgroup.normalizer (Γ : Set (GL ι K)) := by
      apply (s16g_mem_norm_natHom_iff Γ g).mp
      rw [hg]
      exact hρanorm
    obtain ⟨μ, s, hμ, hs, hvec⟩ := hdecomp g hgnorm
    have hρa_formula : ∀ v : Multiplicative (ι → K),
        ρa v = s16gSMul μ (s16gNatHom ι K s v) := by
      intro v
      rw [← hg, s16gNatHom_apply, hvec (Multiplicative.toAdd v), s16gSMul,
        s16gNatHom_apply]
      simp
    obtain ⟨c0, hc0⟩ := hχCsurj (Units.mk0 μ hμ)
    have hc0K : (χC c0 : K) = μ := by
      have := congrArg Units.val hc0
      simpa using this
    let cA : ↥A := ⟨c0, hCA c0⟩
    let hH : ↥A := ⟨π ⟨s, hs⟩, hHA (π ⟨s, hs⟩).2⟩
    have hρc0 : ∀ v : Multiplicative (ι → K), ρ cA v = s16gSMul μ v := by
      intro v
      obtain ⟨w, hw⟩ := hf.surj (Multiplicative.toAdd v)
      have hv : v = Multiplicative.ofAdd (f w) := by rw [hw]; rfl
      rw [hv, hρcoord cA w, hχCeq c0 w, hc0K]
      rfl
    have hρh : ρ hH = s16gNatHom ι K s := by
      have h := congrArg (fun φ : Γ →* MulAut (Multiplicative (ι → K)) => φ ⟨s, hs⟩) hρcomp
      have h' : ρ ⟨π ⟨s, hs⟩, hHA (π ⟨s, hs⟩).2⟩ = s16gNatHom ι K s := h
      simpa [hH] using h'
    have hρaeq : ρ ⟨a, haA⟩ = ρ cA * ρ hH := by
      ext v
      rw [hρa_formula v, MulAut.mul_apply, hρc0, hρh]
    have heqA : (⟨a, haA⟩ : ↥A) = cA * hH := hρinj (by rw [hρaeq, map_mul])
    have ha_val : a = (c0 : MulAut W) * ((π ⟨s, hs⟩ : ↥H) : MulAut W) :=
      congrArg Subtype.val heqA
    have hc0Z : (c0 : MulAut W) ∈ centSub Z := by
      rw [mem_centSub]
      intro z hz
      have hzH : ((π ⟨s, hs⟩ : ↥H) : MulAut W) z = z := mem_fixV.mp hz _ (π ⟨s, hs⟩).2
      have hc0val : (c0 : MulAut W) =
          (a : MulAut W) * (((π ⟨s, hs⟩ : ↥H) : MulAut W))⁻¹ := by
        rw [ha_val]
        group
      rw [hc0val]
      have hinv : (((π ⟨s, hs⟩ : ↥H) : MulAut W))⁻¹ z = z := by
        rw [← hzH, MulAut.inv_apply_self, hzH]
      rw [MulAut.mul_apply, hinv]
      exact (mem_centSub.mp haZ) z hz
    have hc0bot : (c0 : MulAut W) ∈ C ⊓ centSub Z := ⟨c0.2, hc0Z⟩
    rw [hCZ] at hc0bot
    have hc0one : (c0 : MulAut W) = 1 := by simpa using hc0bot
    have haH : a ∈ H := by
      rw [ha_val, hc0one]
      simp
    exact haH
  · intro a ha
    exact ⟨hHA ha, mem_centSub.mpr (fun z hz => mem_fixV.mp hz a ha)⟩

theorem inf_centSub_fixV_eq_of_sl2_nat
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {A H : Subgroup (MulAut W)}
    (hHA : H ≤ A)
    (hAn : A ≤ Subgroup.normalizer (H : Set (MulAut W)))
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : A ⊓ Subgroup.centralizer (H : Set (MulAut W)) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    A ⊓ centSub (fixV H) = H := by
  classical
  let p : ℕ := Nat.card K - 1
  have hpK : Nat.card K = p + 1 := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hp : p.Prime := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hpodd : Odd p := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := by
    rcases hK with h4 | h8
    · exact charP_of_card_eq_prime_pow (p := 2) (f := 2)
        (by rw [← Nat.card_eq_fintype_card, h4]; norm_num)
    · exact charP_of_card_eq_prime_pow (p := 2) (f := 3)
        (by rw [← Nat.card_eq_fintype_card, h8]; norm_num)
  have hΓ : AddCommutantScalar (StatedSL 2 K) := addCommutantScalar_statedSL (m := 2) (by norm_num)
  have hdecomp : ∀ g ∈ Subgroup.normalizer (StatedSL 2 K : Set (GL (Fin 2) K)),
      ∃ (μ : K) (s : GL (Fin 2) K), μ ≠ 0 ∧ s ∈ StatedSL 2 K ∧
        ∀ x : Fin 2 → K,
          (g : Matrix (Fin 2) (Fin 2) K) *ᵥ x =
            μ • ((s : Matrix (Fin 2) (Fin 2) K) *ᵥ x) := by
    intro g _
    have hdet : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := g.det_ne_zero
    obtain ⟨s, μ, hμ, hMs, -⟩ :=
      CFSG.LinearAlgebra.exists_specialLinear_conj_eq_of_det_ne_zero
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) hdet
    refine ⟨μ, (specialLinearGroupEquivStatedSL 2 K s : GL (Fin 2) K), hμ,
      (specialLinearGroupEquivStatedSL 2 K s).2, fun x => ?_⟩
    have hmat : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        μ • (((specialLinearGroupEquivStatedSL 2 K s : GL (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K) := by
      rw [hMs, specialLinearGroupEquivStatedSL_coe]
    rw [hmat, Matrix.smul_mulVec]
  exact inf_centSub_fixV_eq_of_nat (W := W) (A := A) (H := H)
    (ι := Fin 2) (K := K) (Γ := StatedSL 2 K)
    hW hHA hAn hΓ hreal hcomm hp hpK hpodd hcentral hfix hdecomp

theorem inf_centSub_fixV_eq_of_sp4_nat
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {A H : Subgroup (MulAut W)}
    (hHA : H ≤ A)
    (hAn : A ≤ Subgroup.normalizer (H : Set (MulAut W)))
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : A ⊓ Subgroup.centralizer (H : Set (MulAut W)) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    A ⊓ centSub (fixV H) = H := by
  classical
  let p : ℕ := Nat.card K - 1
  have hpK : Nat.card K = p + 1 := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hp : p.Prime := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hpodd : Odd p := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := by
    rcases hK with h4 | h8
    · exact charP_of_card_eq_prime_pow (p := 2) (f := 2)
        (by rw [← Nat.card_eq_fintype_card, h4]; norm_num)
    · exact charP_of_card_eq_prime_pow (p := 2) (f := 3)
        (by rw [← Nat.card_eq_fintype_card, h8]; norm_num)
  have hΓ : AddCommutantScalar (StatedSp 2 K) := addCommutantScalar_statedSp (m := 2)
  have hdecomp : ∀ g ∈ Subgroup.normalizer (StatedSp 2 K : Set (GL (Fin 2 ⊕ Fin 2) K)),
      ∃ (μ : K) (s : GL (Fin 2 ⊕ Fin 2) K), μ ≠ 0 ∧ s ∈ StatedSp 2 K ∧
        ∀ x : Fin 2 ⊕ Fin 2 → K,
          (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x =
            μ • ((s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) := by
    intro g hg
    exact CFSG.ClassicalGroups.Symplectic.exists_smul_statedSp_of_normalizes
      (m := 2) (K := K) (by norm_num)
      (fun A hA => (Subgroup.mem_normalizer_iff.mp hg A).1 hA)
  exact inf_centSub_fixV_eq_of_nat (W := W) (A := A) (H := H)
    (ι := Fin 2 ⊕ Fin 2) (K := K) (Γ := StatedSp 2 K)
    hW hHA hAn hΓ hreal hcomm hp hpK hpodd hcentral hfix hdecomp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
