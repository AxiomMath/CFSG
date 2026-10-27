module

public import CFSG.Quasithin.MS93.S4A441B4
public import CFSG.Quasithin.MS93.S4A441B5
public import CFSG.Quasithin.MS93.S4A35
public import CFSG.Quasithin.MS93.S4AL3
public import CFSG.Quasithin.MS93.S46I464Lin

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Bridge

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

theorem exists_good_conj_or_secD (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le))
    {α α' μ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hμ : μ ∈ nablaSet h.le L α)
    (hQUD : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Uloc h.le L α ⊔ Dloc h.le L α)
    {x : 𝔘} (hx : x ∈ ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆) (hxD : x ∉ Dloc h.le L α) :
    (∃ k ∈ stab (puAmalgam h.le) α,
        (∃ w ∈ ZM (puAmalgam h.le) α', ⁅k * x * k⁻¹, w⁆ ∉ Dloc h.le L α) ∧
          ¬ ZM (puAmalgam h.le) (k • μ) ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)) ∨
      ∃ (ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)) (dual : Bool) (C : Subgroup 𝔘),
        Function.Surjective ψ ∧
        IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α) (Uloc h.le L α) ⊥ ψ false 1 ∧
        Uloc h.le L α ≤ C ∧ ⁅C, stab (puAmalgam h.le) α⁆ ≤ Uloc h.le L α ⊔ Dloc h.le L α ∧
        ⁅conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ), Qv (puAmalgam h.le) α⁆ ≤
          Uloc h.le L α ⊔ Dloc h.le L α ∧
        IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α)
          (conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ)) C ψ dual 1 ∧
        ∀ w ∈ conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ),
          ∀ g ∈ stab (puAmalgam h.le) α, w⁻¹ * (g * w * g⁻¹) ∈ C →
            w⁻¹ * (g * w * g⁻¹) ∈ Uloc h.le L α ⊔ Dloc h.le L α := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hα : IsMVtx _ α := hc.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα' : IsMVtx _ α' := hc'.1
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc h hφ hα
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hα'
  obtain ⟨hfixEq, -, -, hRcard, -, hEne⟩ := s35_core h hC hφ hc hψ₀ hψ'
  obtain ⟨hfixEq', hcardE, hrelE, -, -, -⟩ := s35_core h hC hφ hc' hψ' hψ₀
  have hE2 : ∀ g ∈ natImage ψ₀ (ZM (puAmalgam h.le) α'), g * g = 1 := by
    intro g hg
    obtain ⟨z, hz, rfl⟩ := mem_natImage.mp hg
    have h1 : (z : 𝔘) ^ 2 = 1 := sq_eq_one_of_mem_zv h hfull (ρ := α') (by
      rw [zv_of_isMVtx _ hα']; exact hz)
    have h2 : z * z = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq, h1, Subgroup.coe_one])
    rw [← map_mul, h2, map_one]
  have hEc : ∀ g ∈ natImage ψ₀ (ZM (puAmalgam h.le) α'),
      ∀ g' ∈ natImage ψ₀ (ZM (puAmalgam h.le) α'), g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨z, hz, rfl⟩ := mem_natImage.mp hg
    obtain ⟨z', hz', rfl⟩ := mem_natImage.mp hg'
    have h1 : (z : 𝔘) * z' = z' * z :=
      (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα' hz) _
        (zm_le_qv_self _ hα' hb0 hz')).symm
    have h2 : z * z' = z' * z := Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, h1])
    rw [← map_mul, ← map_mul, h2]
  have hEcard : Nat.card ↥(natImage ψ₀ (ZM (puAmalgam h.le) α')) =
      Nat.card F ^ (3 - Module.finrank F (fixN (natImage ψ₀ (ZM (puAmalgam h.le) α')))) := by
    rw [hcardE, hrelE, hfixEq']
  obtain ⟨s, hax, hT₀⟩ := exists_coords hE2 hEc hEne hEcard
  set ψ := conjSL s ψ₀ with hψdef
  have hψs : Function.Surjective ψ := conjSL_surjective hψ₀s
  have hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1 :=
    isSumOfNaturalModulesVia_conjSL hψ₀ s
  have hEψ : natImage ψ (ZM (puAmalgam h.le) α') =
      (natImage ψ₀ (ZM (puAmalgam h.le) α')).map (MulAut.conj s).toMonoidHom :=
    D432.natImage_conjSL' s ψ₀ _
  have hUs : Uloc h.le L α ≤ stab (puAmalgam h.le) α :=
    (uloc_le_zm h hfull hα).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α))
  have hDn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Dloc h.le L α : Set 𝔘) :=
    stab_le_normalizer_dloc h α
  have hUn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Uloc h.le L α : Set 𝔘) :=
    stab_le_normalizer_uloc h α
  have hUDn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer ((Uloc h.le L α ⊔ Dloc h.le L α : Subgroup 𝔘) : Set 𝔘) :=
    (le_inf hUn hDn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hxUD : x ∈ ((Uloc h.le L α ⊔ Dloc h.le L α : Subgroup 𝔘) : Set 𝔘) := hQUD hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUs.trans hDn)] at hxUD
  obtain ⟨u, hu, d, hd, hxud⟩ := hxUD
  simp only at hxud
  subst hxud
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hxD
    rw [one_mul]
    exact hd
  have hv0 : natVec hψ ⟨u, hu⟩ ≠ 0 := by
    intro h0
    apply hu1
    have : (⟨u, hu⟩ : ↥(Uloc h.le L α)) = 1 :=
      natVec_injective hψ (h0.trans (natVec_one hψ).symm)
    exact congrArg Subtype.val this
  obtain ⟨y, hy⟩ := S46.exists_mulVec_eq_e₁ hv0
  obtain ⟨g₀, hg₀⟩ := toSL3_surjective hψs (S46.rotE01 * y)
  have hu' : (g₀ : 𝔘) * u * (g₀ : 𝔘)⁻¹ ∈ Uloc h.le L α :=
    (Subgroup.mem_normalizer_iff.mp (hUn g₀.2) u).mp hu
  have hd' : (g₀ : 𝔘) * d * (g₀ : 𝔘)⁻¹ ∈ Dloc h.le L α :=
    (Subgroup.mem_normalizer_iff.mp (hDn g₀.2) d).mp hd
  have huc : natVec hψ ⟨_, hu'⟩ = (-1 : F) • ![1, 0, 0] := by
    rw [natVec_conj hψ g₀ ⟨u, hu⟩ ⟨_, hu'⟩ rfl, hg₀, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, hy, S46.rotE01_mulVec]
    ext i
    fin_cases i <;> simp
  have hg₀α : (g₀ : 𝔘) • α = α := g₀.2
  have hμ' : (g₀ : 𝔘) • μ ∈ nablaSet h.le L α := by
    have := (mem_nablaSet_smul h (g₀ : 𝔘) α μ).mpr hμ
    rwa [hg₀α] at this
  have hQUD' : ⁅ZM (puAmalgam h.le) ((g₀ : 𝔘) • μ), Qv (puAmalgam h.le) α⁆ ≤
      Uloc h.le L α ⊔ Dloc h.le L α := by
    rw [zm_smul]
    calc ⁅(ZM (puAmalgam h.le) μ).map (MulAut.conj (g₀ : 𝔘)).toMonoidHom, Qv (puAmalgam h.le) α⁆
        = ⁅(ZM (puAmalgam h.le) μ).map (MulAut.conj (g₀ : 𝔘)).toMonoidHom,
            (Qv (puAmalgam h.le) α).map (MulAut.conj (g₀ : 𝔘)).toMonoidHom⁆ := by
          rw [map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ α g₀.2)]
      _ = (⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆).map
            (MulAut.conj (g₀ : 𝔘)).toMonoidHom := (Subgroup.map_commutator _ _ _).symm
      _ ≤ (Uloc h.le L α ⊔ Dloc h.le L α).map (MulAut.conj (g₀ : 𝔘)).toMonoidHom :=
          Subgroup.map_mono hQUD
      _ = Uloc h.le L α ⊔ Dloc h.le L α := map_conj_eq_of_mem_normalizer (hUDn g₀.2)
  have hax' : ∀ v ∈ fixN (natImage ψ (ZM (puAmalgam h.le) α')), v 2 = 0 := by
    rw [hEψ]
    exact hax
  have hT' : ((rootGroup 0 2 : Subgroup (SL3 F)) ≤ natImage ψ (ZM (puAmalgam h.le) α') ∧
        Fintype.card F ≤ Nat.card ↥(critR (puAmalgam h.le) α α')) ∨
      ((∀ t ∈ (rootGroup 0 2 : Subgroup (SL3 F)), ∃ σ : SL3 F,
          ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
          ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
          σ * t * σ⁻¹ ∈ natImage ψ (ZM (puAmalgam h.le) α')) ∧
        Fintype.card F ^ 2 ≤ Nat.card ↥(critR (puAmalgam h.le) α α')) := by
    rw [hEψ, ← Nat.card_eq_fintype_card, hRcard]
    rcases hT₀ with ⟨hX, hd1⟩ | ⟨hX, hd2⟩
    · exact Or.inl ⟨hX, by rw [hd1, pow_one]⟩
    · exact Or.inr ⟨hX, by rw [hd2]⟩
  rcases exists_good_conj_or_secD_of_coords h hφ hC hb hc hμ' hQUD' hψs hψ hu' hd'
      (neg_ne_zero.mpr one_ne_zero) huc hax' hT' with
    ⟨k, hk, ⟨w, hw, hkw⟩, hkQ⟩ | ⟨dual, C, h1, h2, h3, h4, h5⟩
  · refine Or.inl ⟨k * g₀, (stab (puAmalgam h.le) α).mul_mem hk g₀.2, ⟨w, hw, ?_⟩, ?_⟩
    · have e : k * (g₀ : 𝔘) * (u * d) * (k * (g₀ : 𝔘))⁻¹ =
          k * ((g₀ : 𝔘) * u * (g₀ : 𝔘)⁻¹ * ((g₀ : 𝔘) * d * (g₀ : 𝔘)⁻¹)) * k⁻¹ := by
        group
      rw [e]
      exact hkw
    · rw [mul_smul]
      exact hkQ
  · have hW : conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) ((g₀ : 𝔘) • μ)) =
        conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ) := by
      have e := conjCl_map_conj (g₀ : 𝔘) (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ)
      rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer g₀.2),
        map_conj_eq_of_mem_normalizer (le_normalizer_conjCl _ _ g₀.2)] at e
      rw [zm_smul, ← e]
    rw [hW] at h3 h4 h5
    exact Or.inr ⟨ψ, dual, C, hψs, hψ, h1, h2, h3, h4, h5⟩

end Bridge

end CFSG.Quasithin.MS93.S4A.C441
