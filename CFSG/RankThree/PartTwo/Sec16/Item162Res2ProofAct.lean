module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating10
public import CFSG.RankThree.PartTwo.Sec17.Item171GenProofA10
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res162b

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2 CFSG.RankThree.PartTwo.Sec17.Proof171Gen

variable {G : Type} [Group G]

theorem projTen_ker_isPGroup (Y : Subgroup G)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) [Finite G] :
    IsPGroup 2 (projTen Y φ).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨y, hy⟩
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y)
    ⟨y, (projTen_eq_one_iff Y φ y).mp hy⟩
  refine ⟨n, Subtype.ext ?_⟩
  have := congrArg Subtype.val hn
  simpa using this

theorem mem_range_projTen (Y : Subgroup G)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) {σ : Perm (Fin 10)}
    (hσ : σ ∈ alternatingGroup (Fin 10)) : σ ∈ (projTen Y φ).range := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) (φ.symm ⟨σ, hσ⟩)
  refine ⟨y, ?_⟩
  change ((φ (QuotientGroup.mk' _ y) : alternatingGroup (Fin 10)) : Perm (Fin 10)) = σ
  rw [hy, MulEquiv.apply_symm_apply]

theorem mem_pCoreOf_of_projTen_eq_one {Y : Subgroup G}
    {φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)} {y : ↥Y} (h : projTen Y φ y = 1) :
    (y : G) ∈ CFSG.Open.pCoreOf 2 Y :=
  (Step163Alt.mem_pCore_two_iff y).mp ((projTen_eq_one_iff Y φ y).mp h)

variable [Finite G]

theorem exists_conj_lift {A Y : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hAY : A ≤ Y)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) :
    (∀ a : ↥Y, (a : G) ∈ A → projTen Y φ a = 1 → a = 1) ∧
    ∃ g : Perm (Fin 10),
      (∀ a : ↥Y, (a : G) ∈ A → g * projTen Y φ a * g⁻¹ ∈ eTwentySeven) ∧
      (∀ x ∈ eTwentySeven, ∃ a : ↥Y, (a : G) ∈ A ∧ g * projTen Y φ a * g⁻¹ = x) ∧
      ∀ h ∈ normAlt, ∃ y : ↥Y, (y : G) ∈ Subgroup.normalizer (A : Set G) ∧
        (∀ a : ↥Y, (a : G) ∈ A →
          g * projTen Y φ (y * a * y⁻¹) * g⁻¹ = h * (g * projTen Y φ a * g⁻¹) * h⁻¹) ∧
        ∃ a₀ : ↥Y, (a₀ : G) ∈ A ∧ g * projTen Y φ y * g⁻¹ = h * (g * projTen Y φ a₀ * g⁻¹) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := projTen Y φ with hπ
  have hker2 := projTen_ker_isPGroup Y φ
  set A' := A.subgroupOf Y with hA'
  have hAmap : A'.map Y.subtype = A := by
    rw [hA', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAY]
  have hA'el : CFSG.Assembly.IsElemAbelian 3 A' :=
    Step163Alt.isElemAbelian_of_map_hom Y.subtype
      (fun b _ hb => Y.subtype_injective (by rw [hb, map_one]))
      (by rw [hAmap]; exact hA)
  have hA'3 : IsPGroup 3 A' := fun b => ⟨1, Subtype.ext (by simpa using hA'el.2 b b.2)⟩
  have hinj : ∀ b ∈ A', π b = 1 → b = 1 := by
    intro b hb hb1
    obtain ⟨m, hm⟩ := hker2 ⟨b, hb1⟩
    have h2 : b ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact Step163Alt.eq_one_of_two_three h2 (by rw [pow_one]; exact hA'el.2 b hb)
  refine ⟨fun a ha h1 => hinj a ha h1, ?_⟩
  set E := A'.map π with hE
  have hEel : CFSG.Assembly.IsElemAbelian 3 E := Step163Alt.isElemAbelian_map_hom π hA'el
  have hEcomm : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hE27 : Nat.card E = 27 := by
    set π' : ↥A' →* Perm (Fin 10) := π.comp A'.subtype with hπ'
    have hπ'inj : Function.Injective π' := by
      intro a b hab
      have hab' : π a = π b := hab
      have := hinj _ (A'.mul_mem a.2 (A'.inv_mem b.2))
        (by rw [map_mul, map_inv, hab', mul_inv_cancel])
      exact Subtype.ext (mul_inv_eq_one.mp this)
    have hrange : π'.range = E := by
      rw [hπ', MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 := Nat.card_congr (MonoidHom.ofInjective hπ'inj).toEquiv
    rw [hrange] at h1
    rw [← h1, hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv, hA27]
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.K412.exists_conj_eq_eTwentySeven hE27 hEcomm
  have hmemE : ∀ z : Perm (Fin 10), z ∈ E ↔ g * z * g⁻¹ ∈ eTwentySeven := by
    intro z
    rw [← hg, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
      show g⁻¹ * (g * z * g⁻¹) * g = z by group]
  have hgA : ∀ a : ↥Y, (a : G) ∈ A → g * π a * g⁻¹ ∈ eTwentySeven := fun a ha =>
    (hmemE _).mp ⟨a, ha, rfl⟩
  refine ⟨g, hgA, ?_, ?_⟩
  ·
    intro x hx
    have hx' : g⁻¹ * x * g ∈ E := by
      rw [hmemE, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
      exact hx
    obtain ⟨a, ha, hax⟩ := hx'
    refine ⟨a, ha, ?_⟩
    rw [hax]
    group
  ·
    intro h hh
    set h₀ := g⁻¹ * h * g with hh₀
    have hhA : h₀ ∈ alternatingGroup (Fin 10) := by
      have := (alternatingGroup.normal (α := Fin 10)).conj_mem h (Subgroup.mem_inf.mp hh).2 g⁻¹
      rwa [inv_inv] at this
    have hhN : h₀ ∈ Subgroup.normalizer ((E : Subgroup (Perm (Fin 10))) : Set (Perm (Fin 10))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [hmemE, hmemE,
        show g * (g⁻¹ * h * g * z * (g⁻¹ * h * g)⁻¹) * g⁻¹ = h * (g * z * g⁻¹) * h⁻¹ by group]
      exact Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hh).1 _
    obtain ⟨y, hyN, hyκ⟩ := Step163Alt.exists_normalizer_lift π hker2 hA'3 hEcomm
      (mem_range_projTen Y φ hhA) hhN
    have hyNG : (y : G) ∈ Subgroup.normalizer (A : Set G) := by
      have := Subgroup.le_normalizer_map Y.subtype ⟨y, hyN, rfl⟩
      rwa [hAmap] at this
    have hlift : ∀ a : ↥Y, (a : G) ∈ A →
        g * π (y * a * y⁻¹) * g⁻¹ = h * (g * π a * g⁻¹) * h⁻¹ := by
      intro a ha
      rw [hyκ a ha, hh₀]
      group
    refine ⟨y, hyNG, hlift, ?_⟩
    set e := h⁻¹ * (g * π y * g⁻¹) with he
    have hec : e ∈ Subgroup.centralizer (eTwentySeven : Set (Perm (Fin 10))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : g⁻¹ * x * g ∈ E := by
        rw [hmemE, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
        exact hx
      obtain ⟨a, ha, hax⟩ := hx'
      have hxa : x = g * π a * g⁻¹ := by rw [hax]; group
      have h1 := hlift a ha
      rw [map_mul, map_mul, map_inv] at h1
      rw [hxa, he]
      calc g * π a * g⁻¹ * (h⁻¹ * (g * π y * g⁻¹))
          = h⁻¹ * (h * (g * π a * g⁻¹) * h⁻¹) * (g * π y * g⁻¹) := by group
        _ = h⁻¹ * (g * (π y * π a * (π y)⁻¹) * g⁻¹) * (g * π y * g⁻¹) := by rw [h1]
        _ = h⁻¹ * (g * π y * g⁻¹) * (g * π a * g⁻¹) := by group
    rw [centralizer_eTwentySeven] at hec
    have he' : g⁻¹ * e * g ∈ E := by
      rw [hmemE, show g * (g⁻¹ * e * g) * g⁻¹ = e by group]
      exact hec
    obtain ⟨a₀, ha₀, ha₀e⟩ := he'
    refine ⟨a₀, ha₀, ?_⟩
    have h1 : g * π a₀ * g⁻¹ = e := by
      rw [show π a₀ = g⁻¹ * e * g from ha₀e]
      group
    rw [h1, he, mul_inv_cancel_left]

end CFSG.RankThree.PartTwo.Sec16.Res162b
