module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Leaves
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open

theorem isElemAbelian_of_card_three {G : Type} [Group G] {Q : Subgroup G} (hQ : Nat.card Q = 3) :
    IsElemAbelian 3 Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic Q := isCyclic_of_prime_card hQ
  refine ⟨⟨⟨fun a b => (IsCyclic.commGroup : CommGroup Q).mul_comm a b⟩⟩, fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : Q) ^ Nat.card Q = 1 := pow_card_eq_one'
  rw [hQ] at h
  simpa using congrArg Subtype.val h

theorem normalizer_le_gamma {G : Type} [Group G] [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ : Nat.card Q = 3) : Subgroup.normalizer (Q : Set G) ≤ rankThreeGamma 1 3 P := by
  unfold rankThreeGamma GLBCore
  refine le_sSup ⟨Q, hQP, ?_, rfl⟩
  exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl (isElemAbelian_of_card_three hQ)
    (k := 1) (by rw [hQ]; norm_num)

theorem assembly : AssemblyStatement := by
  intro G _ _ K hN hL Z X P hZK hXK hpos hP
  set Γ := rankThreeGamma 1 3 P with hΓ
  have hpos' := hpos
  obtain ⟨hZ3, hZX, hXC, -, -, -, -⟩ := hpos'
  have hZ3' : Nat.card Z = 3 := by rwa [card_subgroupOf_of_le hZK] at hZ3
  have hZXG : Z ≤ X := fun z hz => by
    have : (⟨z, hZK hz⟩ : K) ∈ X.subgroupOf K := hZX (by simpa [Subgroup.mem_subgroupOf] using hz)
    simpa [Subgroup.mem_subgroupOf] using this
  have hXCG : ∀ x ∈ X, ∀ z ∈ Z, z * x = x * z := by
    intro x hx z hz
    have hmem : (⟨x, hXK hx⟩ : K) ∈ Subgroup.centralizer ((Z.subgroupOf K : Subgroup K) : Set K) :=
      hXC (by simpa [Subgroup.mem_subgroupOf] using hx)
    have := Subgroup.mem_centralizer_iff.mp hmem ⟨z, hZK hz⟩
      (by simpa [Subgroup.mem_subgroupOf] using hz)
    simpa using congrArg Subtype.val this
  obtain ⟨Q, hQ⟩ := hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZP : Z ≤ P := by
    have hnorm : (Z.subgroupOf X).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hc := hXCG g g.2 n hn
      have : ((g * n * g⁻¹ : X) : G) = n := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hc]; group
      rw [this]; exact hn⟩
    have hpg : IsPGroup 3 (Z.subgroupOf X) :=
      IsPGroup.of_card (n := 1) (by rw [card_subgroupOf_of_le hZXG, hZ3', pow_one])
    have hle := hpg.le_sylow_of_normal Q
    intro z hz
    rw [← hQ]
    exact ⟨⟨z, hZXG hz⟩, hle (by simpa [Subgroup.mem_subgroupOf] using hz), rfl⟩
  have hNZ : Subgroup.normalizer (Z : Set G) ≤ Γ := normalizer_le_gamma hZP hZ3'
  obtain ⟨hCU, hCompU, Z₀, X₀, E₀, hpos0, hE₀X₀, -, hcard9, hsup⟩ := hL
  obtain ⟨k, hk⟩ := hCU _ _ _ _ hpos hpos0
  have hposk := pos_map (MulAut.conj k⁻¹) hpos
  have hk' : (Z.subgroupOf K).map (MulAut.conj k⁻¹).toMonoidHom = Z₀ := hk
  rw [hk'] at hposk
  have hXk : (X.subgroupOf K).map (MulAut.conj k⁻¹).toMonoidHom = X₀ := hCompU _ _ _ hposk hpos0
  set E₂ : Subgroup G := (E₀.map (MulAut.conj k).toMonoidHom).map K.subtype with hE₂
  have hE₂X : E₂ ≤ X := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    have he' : e ∈ (X.subgroupOf K).map (MulAut.conj k⁻¹).toMonoidHom := hXk ▸ hE₀X₀ he
    obtain ⟨x, hx, hxe⟩ := he'
    have hx' : (x : G) ∈ X := hx
    have : (MulAut.conj k).toMonoidHom e = x := by
      rw [← hxe]; simp [MulAut.conj_apply, mul_assoc]
    simp only [Subgroup.coe_subtype]
    rw [this]; exact hx'
  have hE₂card : Nat.card E₂ = 9 := by
    rw [hE₂, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj k).injective, hcard9]
  have hpg2 : IsPGroup 3 (E₂.subgroupOf X) :=
    IsPGroup.of_card (n := 2) (by rw [card_subgroupOf_of_le hE₂X, hE₂card]; norm_num)
  obtain ⟨R, hR⟩ := hpg2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q R
  set h : G := (g : G)⁻¹ * (k : G) with hh
  set ψ : K →* G := (MulAut.conj h).toMonoidHom.comp K.subtype with hψ
  have hψinj : Function.Injective ψ := (MulAut.conj h).injective.comp K.subtype_injective
  have hψP : ∀ e ∈ E₀, ψ e ∈ P := by
    intro e he
    have h2 : ((k : G) * (e : G) * (k : G)⁻¹) ∈ E₂ :=
      ⟨_, ⟨e, he, rfl⟩, by simp [MulAut.conj_apply]⟩
    have h3 : (⟨_, hE₂X h2⟩ : X) ∈ (R : Subgroup X) :=
      hR (by simpa [Subgroup.mem_subgroupOf] using h2)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h3
    obtain ⟨y, hy, hyx⟩ := h3
    have hyx' : (g : G) * (y : G) * (g : G)⁻¹ = (k : G) * (e : G) * (k : G)⁻¹ := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using congrArg Subtype.val hyx
    rw [← hQ]
    refine ⟨y, hy, ?_⟩
    simp only [hψ, hh, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have : (y : G) = (g : G)⁻¹ * ((k : G) * (e : G) * (k : G)⁻¹) * (g : G) := by
      rw [← hyx']; group
    rw [this]; group
  have hKΓ : K ≤ Γ := by
    have hKmap : K ≤ (⊤ : Subgroup K).map ψ := by
      intro x hx
      refine ⟨⟨h⁻¹ * x * h, ?_⟩, trivial, ?_⟩
      · simpa using hN.conj_mem x hx h⁻¹
      · simp [hψ, MulAut.conj_apply, mul_assoc]
    refine hKmap.trans ?_
    rw [← hsup]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun F => iSup_le fun hF => iSup_le fun hF3 => ?_
    have hFP : F.map ψ ≤ P := by
      rintro _ ⟨e, he, rfl⟩; exact hψP e (hF he)
    have hF3' : Nat.card (F.map ψ) = 3 := by rw [Subgroup.card_map_of_injective hψinj, hF3]
    refine le_trans ?_ ((Subgroup.centralizer_le_normalizer _).trans (normalizer_le_gamma hFP hF3'))
    rw [Subgroup.coe_map]
    exact Subgroup.map_centralizer_le_centralizer_image _ _
  rw [eq_top_iff]
  intro x _
  let φ : MulAut K := MulAut.conjNormal x
  have hposx := pos_map φ hpos
  obtain ⟨k₁, hk₁⟩ := hCU _ _ _ _ hposx hpos
  have hk₁' : ((Z.subgroupOf K).map φ.toMonoidHom).map (MulAut.conj k₁⁻¹).toMonoidHom =
      Z.subgroupOf K := hk₁
  set n : G := (k₁ : G)⁻¹ * x with hn
  have hfw : ∀ z ∈ Z, n * z * n⁻¹ ∈ Z := by
    intro z hz
    have hm : (MulAut.conj k₁⁻¹).toMonoidHom (φ.toMonoidHom ⟨z, hZK hz⟩) ∈ Z.subgroupOf K := by
      rw [← hk₁']
      exact ⟨_, ⟨⟨z, hZK hz⟩, by simpa [Subgroup.mem_subgroupOf] using hz, rfl⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hm
    simpa [φ, hn, MulAut.conj_apply, MulAut.conjNormal_apply, mul_assoc] using hm
  have hnZ : n ∈ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hfw z hz, fun hz => ?_⟩
    have hsub : (Z.map (MulAut.conj n).toMonoidHom) ≤ Z := by
      rintro _ ⟨w, hw, rfl⟩; simpa [MulAut.conj_apply] using hfw w hw
    have heq : Z.map (MulAut.conj n).toMonoidHom = Z :=
      Subgroup.eq_of_le_of_card_ge hsub
        (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
    rw [← heq] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = z := (MulAut.conj n).injective (by simpa [MulAut.conj_apply] using hwz)
    rwa [← this]
  have hx : x = (k₁ : G) * n := by rw [hn]; group
  rw [hx]
  exact Γ.mul_mem (hKΓ k₁.2) (hNZ hnZ)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
