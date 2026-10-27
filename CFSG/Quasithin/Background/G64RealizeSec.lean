module

public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Background.B4ModelsApi
public import CFSG.Quasithin.Background.G6Swap

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {V : Type*} [CommGroup V]

theorem RealizesVia.exists_moved {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) {γ : D.Gam} (hγ : γ ≠ 1) :
    ∃ u ∈ U, ((π γ : ↥H) : MulAut V) u * u⁻¹ ∉ Z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨_, hZU, _, hHU, _, hsec, _, β, hβs, hβk, hβe⟩ := h
  apply hγ
  apply hD
  intro m hm
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have hact : D.act γ m ∈ D.sec := hsec γ m hm
  have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
  have h1 := hβe γ u ⟨m, hm⟩ hu' hact hu
  have hc : ((π γ : ↥H) : MulAut V) (u : V) * (u : V)⁻¹ ∈ Z := hcon u u.2
  have h2 : β ⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ = β u := by
    have hcU : ((π γ : ↥H) : MulAut V) (u : V) * (u : V)⁻¹ ∈ U := U.mul_mem hu' (U.inv_mem u.2)
    have : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) =
        ⟨_, hcU⟩ * u := Subtype.ext (by simp)
    rw [this, map_mul, (hβk _).2 hc, one_mul]
  rw [h2, hu] at h1
  have h3 := QuotientGroup.eq.mp h1
  have h4 : m⁻¹ * D.act γ m ∈ D.ker := h3
  rw [mul_comm]
  exact h4

theorem RealizesVia.injective_of_faithful' {D : FFModel} (hD : D.Faithful)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

theorem RealizesVia.exists_secMap {D : FFModel} (hker : D.ker = ⊥) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    ∃ f : ↥U →* ↥D.sec, Function.Surjective f ∧ (∀ u : ↥U, f u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : D.Gam) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        ((f ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ : ↥D.sec) : D.Amb) =
          D.act γ ((f u : ↥D.sec) : D.Amb) := by
  obtain ⟨_, _, _, _, _, hsec, _, β, hβs, hβk, hβe⟩ := h
  have hqi : Function.Injective (QuotientGroup.mk' (D.ker.subgroupOf D.sec)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker,
      Subgroup.mem_bot] at hx
    exact Subtype.ext hx
  let Q : ↥D.sec ≃* D.Mod :=
    MulEquiv.ofBijective (QuotientGroup.mk' (D.ker.subgroupOf D.sec))
      ⟨hqi, QuotientGroup.mk'_surjective _⟩
  refine ⟨Q.symm.toMonoidHom.comp β, ?_, ?_, ?_⟩
  · exact Q.symm.surjective.comp hβs
  · intro u
    rw [← hβk u]
    show Q.symm (β u) = 1 ↔ β u = 1
    exact MulEquiv.map_eq_one_iff _
  · intro γ u hu
    set m : ↥D.sec := Q.symm (β u) with hm
    have hm' : β u = QuotientGroup.mk m := by
      rw [hm]
      exact (Q.apply_symm_apply (β u)).symm
    have hact : D.act γ (m : D.Amb) ∈ D.sec := hsec γ m m.2
    have := hβe γ u m hu hact hm'
    show ((Q.symm (β ⟨_, hu⟩) : ↥D.sec) : D.Amb) = D.act γ (m : D.Amb)
    rw [this]
    have : Q.symm (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hact⟩) = ⟨D.act γ (m : D.Amb), hact⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this]

theorem eq_one_or_eq_of_mem_zpowers' {M : Type*} [Group M] {w x : M} (hw : w ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers w) : x = 1 ∨ x = w := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : w ^ (2 : ℤ) = 1 := by exact_mod_cast hw
  rcases Int.emod_two_eq_zero_or_one z with h0 | h1
  · left
    rw [(Int.mul_ediv_add_emod z 2).symm, h0, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [(Int.mul_ediv_add_emod z 2).symm, h1, zpow_add, zpow_mul, h2, one_zpow, one_mul,
      zpow_one]

theorem card_le_two_of_rankOne (hV2 : ∀ v : V, v ^ 2 = 1) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U Z π) {γ : ↥Γ}
    (hmove : ∃ u ∈ U, ((π γ : ↥H) : MulAut V) u * u⁻¹ ∉ Z)
    (hrank : ∃ w : V, ∀ u ∈ U, ((π γ : ↥H) : MulAut V) u * u⁻¹ ∈ Z ⊔ Subgroup.zpowers w) :
    Nat.card F ≤ 2 := by
  classical
  obtain ⟨w, hw⟩ := hrank
  obtain ⟨u₁, hu₁, hmv⟩ := hmove
  have hHU : ∀ u ∈ U, ((π γ : ↥H) : MulAut V) u ∈ U := fun u hu => h.2.2.2.1 (π γ) u hu
  obtain ⟨f, hfs, hfk, hfe⟩ := RealizesVia.exists_secMap (D := FFModel.nat Γ) rfl h
  let g : ↥U → (ι → F) := fun u => Multiplicative.toAdd
    ((((f u : ↥(FFModel.nat Γ).sec) : (FFModel.nat Γ).Amb)) : Multiplicative (ι → F))
  have hg_mul : ∀ u v : ↥U, g (u * v) = g u + g v := by
    intro u v
    show Multiplicative.toAdd (((f (u * v) : ↥(FFModel.nat Γ).sec) : (FFModel.nat Γ).Amb) :
      Multiplicative (ι → F)) = _
    rw [map_mul]
    rfl
  have hg_inv : ∀ u : ↥U, g u⁻¹ = - g u := by
    intro u
    show Multiplicative.toAdd (((f u⁻¹ : ↥(FFModel.nat Γ).sec) : (FFModel.nat Γ).Amb) :
      Multiplicative (ι → F)) = _
    rw [map_inv]
    rfl
  have hg_zero : ∀ u : ↥U, g u = 0 ↔ (u : V) ∈ Z := by
    intro u
    rw [← hfk u]
    constructor
    · intro h0
      exact Subtype.ext h0
    · intro h1
      rw [show g u = Multiplicative.toAdd (((f u : ↥(FFModel.nat Γ).sec) :
        (FFModel.nat Γ).Amb) : Multiplicative (ι → F)) from rfl, h1]
      rfl
  have hg_eq : ∀ (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      g ⟨_, hu⟩ = ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec (g u) := by
    intro u hu
    have := hfe γ u hu
    exact congrArg Multiplicative.toAdd this
  have hgs : ∀ x : ι → F, ∃ u : ↥U, g u = x := by
    intro x
    obtain ⟨u, hu⟩ := hfs ⟨Multiplicative.ofAdd x, trivial⟩
    refine ⟨u, ?_⟩
    show Multiplicative.toAdd (((f u : ↥(FFModel.nat Γ).sec) : (FFModel.nat Γ).Amb) :
      Multiplicative (ι → F)) = x
    rw [hu]
    rfl
  let comm : ↥U → ↥U := fun u => ⟨_, hHU u u.2⟩ * u⁻¹
  have hcomm_coe : ∀ u : ↥U, ((comm u : ↥U) : V) = ((π γ : ↥H) : MulAut V) u * (u : V)⁻¹ :=
    fun u => rfl
  have hcomm_g : ∀ u : ↥U, g (comm u) =
      ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec (g u) - g u := by
    intro u
    rw [hg_mul, hg_inv, hg_eq, sub_eq_add_neg]
  set y₀ := g (comm ⟨u₁, hu₁⟩) with hy₀
  have hy₀ne : y₀ ≠ 0 := fun h0 => hmv ((hg_zero _).1 h0)
  have hw2 : w ^ 2 = 1 := hV2 w
  have hval : ∀ u : ↥U, g (comm u) = 0 ∨ g (comm u) = y₀ := by
    intro u
    obtain ⟨z, hz, x, hx, hzx⟩ := Subgroup.mem_sup.1 (hw u u.2)
    obtain ⟨z₁, hz₁, x₁, hx₁, hzx₁⟩ := Subgroup.mem_sup.1 (hw u₁ hu₁)
    rcases eq_one_or_eq_of_mem_zpowers' hw2 hx with hx' | hx'
    · left
      rw [hg_zero, hcomm_coe, ← hzx, hx', mul_one]
      exact hz
    · right
      rcases eq_one_or_eq_of_mem_zpowers' hw2 hx₁ with hx₁' | hx₁'
      · exfalso
        apply hmv
        rw [← hzx₁, hx₁', mul_one]
        exact hz₁
      · have hdiff : ((comm u * (comm ⟨u₁, hu₁⟩)⁻¹ : ↥U) : V) ∈ Z := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hcomm_coe, hcomm_coe]
          simp only
          rw [← hzx, ← hzx₁, hx', hx₁']
          have : z * w * (z₁ * w)⁻¹ = z * z₁⁻¹ := by group
          rw [this]
          exact Z.mul_mem hz (Z.inv_mem hz₁)
        have h0 := (hg_zero _).2 hdiff
        rw [hg_mul, hg_inv] at h0
        rw [hy₀]
        exact (add_neg_eq_zero.1 h0)
  have hF : ∀ c : F, c = 0 ∨ c = 1 := by
    intro c
    obtain ⟨u, hu⟩ := hgs (c • g ⟨u₁, hu₁⟩)
    have hlin : g (comm u) = c • y₀ := by
      rw [hcomm_g, hu, hy₀, hcomm_g, Matrix.mulVec_smul, smul_sub]
    rcases hval u with h0 | h0 <;> rw [hlin] at h0
    · left
      exact (smul_eq_zero.1 h0).resolve_right hy₀ne
    · right
      have : (c - 1) • y₀ = 0 := by rw [sub_smul, one_smul, h0, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hy₀ne)
  calc Nat.card F ≤ Nat.card Bool :=
        Nat.card_le_card_of_surjective (fun b : Bool => if b then (1 : F) else 0) (by
          intro c
          rcases hF c with rfl | rfl
          · exact ⟨false, by simp⟩
          · exact ⟨true, by simp⟩)
    _ = 2 := by simp

theorem false_of_two_moved {h : MulAut V} (hcard : Nat.card (commV (Subgroup.zpowers h)) = 2)
    {U₁ U₂ Z : Subgroup V} (hU₁ : ∀ u ∈ U₁, h u ∈ U₁) (hU₂ : ∀ u ∈ U₂, h u ∈ U₂)
    (h12 : U₁ ⊓ U₂ ≤ Z) {u₁ u₂ : V} (hu₁ : u₁ ∈ U₁) (hu₂ : u₂ ∈ U₂) (hm₁ : h u₁ * u₁⁻¹ ∉ Z)
    (hm₂ : h u₂ * u₂⁻¹ ∉ Z) : False := by
  have hx₁ : h u₁ * u₁⁻¹ ∈ U₁ := U₁.mul_mem (hU₁ u₁ hu₁) (U₁.inv_mem hu₁)
  have hx₂ : h u₂ * u₂⁻¹ ∈ U₂ := U₂.mul_mem (hU₂ u₂ hu₂) (U₂.inv_mem hu₂)
  have h1 : h u₁ * u₁⁻¹ ≠ 1 := fun e => hm₁ (e ▸ Z.one_mem)
  have h2 : h u₂ * u₂⁻¹ ≠ 1 := fun e => hm₂ (e ▸ Z.one_mem)
  have hne : h u₁ * u₁⁻¹ ≠ h u₂ * u₂⁻¹ := by
    intro e
    exact hm₁ (h12 ⟨hx₁, e ▸ hx₂⟩)
  exact G6.false_of_card_two hcard (G6.mem_commV_of_mem (Subgroup.mem_zpowers h) u₁)
    (G6.mem_commV_of_mem (Subgroup.mem_zpowers h) u₂) h1 h2 hne

end CFSG.Quasithin.G64
