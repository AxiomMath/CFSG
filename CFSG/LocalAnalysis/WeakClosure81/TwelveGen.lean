module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveCartan
public import CFSG.LocalAnalysis.WeakClosure81.TwelvePartTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

private theorem b12_TwelveGen_isPGroup_of_isElemAbelian {G : Type} [Group G]
    {A : Subgroup G} (hA : IsElemAbelian 2 A) : IsPGroup 2 A := fun a => ⟨1, by
  have h : a ^ 2 = 1 := Subtype.ext (hA.2 a a.2)
  simpa using h⟩

private theorem b12_TwelveGen_isElemAbelian_conj {G : Type} [Group G]
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (g : G) :
    IsElemAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := by
  have hmul : ∀ x : G, x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [show (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply],
        show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      exact hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  refine ⟨IsMulCommutative.of_comm fun x y => Subtype.ext ?_, fun x hx => ?_⟩
  · have hx' : g⁻¹ * x.1 * g ∈ A := (hmul x.1).mp x.2
    have hy' : g⁻¹ * y.1 * g ∈ A := (hmul y.1).mp y.2
    have hc : (g⁻¹ * x.1 * g) * (g⁻¹ * y.1 * g)
        = (g⁻¹ * y.1 * g) * (g⁻¹ * x.1 * g) := by
      have hcomm := hA.1.is_comm.comm (⟨g⁻¹ * x.1 * g, hx'⟩ : A) ⟨g⁻¹ * y.1 * g, hy'⟩
      exact congrArg Subtype.val hcomm
    show x.1 * y.1 = y.1 * x.1
    calc x.1 * y.1 = g * ((g⁻¹ * x.1 * g) * (g⁻¹ * y.1 * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y.1 * g) * (g⁻¹ * x.1 * g)) * g⁻¹ := by rw [hc]
      _ = y.1 * x.1 := by group
  · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy2 : y ^ 2 = 1 := hA.2 y hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [pow_two, show (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group,
      ← pow_two, hy2]
    simp

section Generation

variable {G : Type} [Group G] [Finite G] {n : ℕ}

private theorem b12_TwelveGen_swap_data
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {S : Sylow 2 G}
    {A : Subgroup G} (hAS : A ≤ (S : Subgroup G)) (hA : IsElemAbelian 2 A) {g : G}
    (hgen : A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ∃ w b : G, w ∈ Subgroup.zpowers a ⊔ A.map (MulAut.conj g).toMonoidHom ∧ w * w = 1 ∧
      g = w * b ∧ b ∈ normalizer (S : Set G) ∧ w • S = g • S ∧ S ≠ g • S := by
  have hnotN : g ∉ normalizer (S : Set G) := by
    intro hgN
    have hAgle : A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) := by
      rintro x ⟨y, hy, rfl⟩
      rw [show (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
      exact (Subgroup.mem_set_normalizer_iff.mp hgN y).mp (hAS hy)
    have htop : (S : Subgroup G) = ⊤ := by
      have hle : (⊤ : Subgroup G) ≤ (S : Subgroup G) := by
        rw [← hgen]
        exact sup_le hAS hAgle
      exact top_le_iff.mp hle
    have hNtop : normalizer (S : Set G) = ⊤ := by
      have h1 : normalizer (S : Set G) = normalizer ((⊤ : Subgroup G) : Set G) :=
        congrArg (fun T : Subgroup G => normalizer (T : Set G)) htop
      rw [h1, Subgroup.normalizer_eq_top_iff]
      infer_instance
    exact rankOne_borel_ne_top hG S hNtop
  have hne : S ≠ g • S := fun heq =>
    hnotN (Sylow.smul_eq_iff_mem_normalizer.mp heq.symm)
  have haR : a ∈ rootCenter (S : Subgroup G) := rankOne_elemAbelian_le_rootCenter hG hAS hA ha
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.2 a ha
  let a₂ : G := g * a * g⁻¹
  have ha₂Ag : a₂ ∈ A.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have ha₂2 : a₂ * a₂ = 1 := by
    simp only [a₂]
    rw [show (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ by group, ha2]
    simp
  have ha₂1 : a₂ ≠ 1 := by
    intro h
    apply ha1
    have hh := congrArg (MulAut.conj g⁻¹) h
    have hconj : MulAut.conj g⁻¹ a₂ = a := by
      simp only [a₂, MulAut.conj_apply]
      group
    rwa [hconj, map_one] at hh
  have ha₂S : a₂ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
    rw [mem_sylow_smul_iff g S a₂]
    have hthis : g⁻¹ * a₂ * g = a := by
      simp only [a₂]
      group
    rw [hthis]
    exact hAS ha
  obtain ⟨w, hwmem, hww, hwa⟩ := rankOne_exists_swap_in_dihedral hG (S := S) (S' := g • S)
    hne (a := a) (b := a₂) (hAS ha) ha₂S ha2 ha₂2 ha1 ha₂1
  have hwH : w ∈ Subgroup.zpowers a ⊔ A.map (MulAut.conj g).toMonoidHom := by
    have hcl : Subgroup.closure ({a, a₂} : Set G) ≤
        Subgroup.zpowers a ⊔ A.map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
      · rw [hz]; exact Subgroup.mem_sup_right ha₂Ag
    exact hcl hwmem
  have ha₂wS : a₂ ∈ ((w • S : Sylow 2 G) : Subgroup G) := by
    rw [mem_sylow_smul_iff w S a₂]
    have hthis : w⁻¹ * a₂ * w = a := by
      rw [inv_eq_of_mul_eq_one_right hww]
      have hwa' : w * a * w = a₂ := by
        simpa only [inv_eq_of_mul_eq_one_right hww] using hwa
      calc w * a₂ * w = w * (w * a * w) * w := by rw [← hwa']
        _ = (w * w) * a * (w * w) := by group
        _ = a := by simp [hww]
    rw [hthis]
    exact hAS ha
  have ha₂ne : Subgroup.zpowers a₂ ≠ ⊥ := fun hbot =>
    ha₂1 (Subgroup.zpowers_eq_bot.mp hbot)
  have hwS : w • S = g • S :=
    rankOne_sylow_eq_of_ne_bot hG (S := g • S) (S₁ := w • S) ha₂ne
      (Subgroup.zpowers_le.mpr ha₂S) (Subgroup.zpowers_le.mpr ha₂wS)
  refine ⟨w, w⁻¹ * g, hwH, hww, ?_, ?_, hwS, hne⟩
  · show g = w * (w⁻¹ * g)
    group
  · rw [← Sylow.smul_eq_iff_mem_normalizer (P := S)]
    have hsmul : (w⁻¹ * g) • S = S := by
      calc (w⁻¹ * g) • S = w⁻¹ • (g • S) := mul_smul w⁻¹ g S
        _ = w⁻¹ • (w • S) := by rw [hwS]
        _ = S := inv_smul_smul w S
    exact hsmul

theorem rankOne_zpowers_sup_conj_eq_top
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {S : Sylow 2 G}
    {A : Subgroup G} (hAS : A ≤ (S : Subgroup G)) (hA : IsElemAbelian 2 A) {g : G}
    (hgen : A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.zpowers a ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ := by
  let H : Subgroup G := Subgroup.zpowers a ⊔ A.map (MulAut.conj g).toMonoidHom
  change H = ⊤
  obtain ⟨w, b, hwH, hww, hgb, hbN, hwS, hne⟩ :=
    b12_TwelveGen_swap_data hG hAS hA hgen ha ha1
  have haR : a ∈ rootCenter (S : Subgroup G) := rankOne_elemAbelian_le_rootCenter hG hAS hA ha
  have hAroot : A ≤ rootCenter (S : Subgroup G) := rankOne_elemAbelian_le_rootCenter hG hAS hA
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.2 a ha
  have hb_eq : b = w⁻¹ * g := by
    rw [hgb]
    group
  have hbyH : ∀ y ∈ A, b * y * b⁻¹ ∈ H := by
    intro y hy
    have hgy : g * y * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hgyH : g * y * g⁻¹ ∈ H := Subgroup.mem_sup_right hgy
    have heq : b * y * b⁻¹ = w⁻¹ * (g * y * g⁻¹) * w := by
      rw [hb_eq]
      group
    rw [heq]
    exact H.mul_mem (H.mul_mem (H.inv_mem hwH) hgyH) hwH
  let x : G := b * a * b⁻¹
  have hxH : x ∈ H := hbyH a ha
  have hxR : x ∈ rootCenter (S : Subgroup G) := conj_mem_rootCenter hbN haR
  have hxS : x ∈ (S : Subgroup G) := hxR.1
  have hx1 : x ≠ 1 := by
    intro h
    apply ha1
    have hh := congrArg (MulAut.conj b⁻¹) h
    have hconj : MulAut.conj b⁻¹ x = a := by
      simp only [x, MulAut.conj_apply]
      group
    rwa [hconj, map_one] at hh
  have hx2 : x * x = 1 := by
    simp only [x]
    rw [show (b * a * b⁻¹) * (b * a * b⁻¹) = b * (a * a) * b⁻¹ by group, ha2]
    simp
  let x' : G := w * x * w⁻¹
  have hx_ww : w * x * w = x' := by
    simp only [x']
    rw [inv_eq_of_mul_eq_one_right hww]
  have hx'H : x' ∈ H := by
    simp only [x']
    exact H.mul_mem (H.mul_mem hwH hxH) (H.inv_mem hwH)
  have hx'2 : x' * x' = 1 := by
    simp only [x']
    rw [show (w * x * w⁻¹) * (w * x * w⁻¹) = w * (x * x) * w⁻¹ by group, hx2]
    simp
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hx1
    calc x = (w * w) * x * (w * w) := by simp [hww]
      _ = w * (w * x * w) * w := by group
      _ = w * x' * w := by rw [hx_ww]
      _ = w * 1 * w := by rw [h]
      _ = 1 := by simp [hww]
  have hx'S : x' ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
    have hx'w : x' ∈ ((w • S : Sylow 2 G) : Subgroup G) := by
      rw [mem_sylow_smul_iff w S x']
      have hthis : w⁻¹ * x' * w = x := by
        simp only [x']
        group
      rw [hthis]
      exact hxS
    rw [hwS] at hx'w
    exact hx'w
  obtain ⟨w₂, hw₂mem, hw₂2, hw₂a⟩ := rankOne_exists_swap_in_dihedral hG (S := S)
    (S' := g • S) hne (a := a) (b := x') (hAS ha) hx'S ha2 hx'2 ha1 hx'1
  have hw₂H : w₂ ∈ H := by
    have hcl : Subgroup.closure ({a, x'} : Set G) ≤ H := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
      · rw [hz]; exact hx'H
    exact hcl hw₂mem
  have hcH : w * w₂ ∈ H := H.mul_mem hwH hw₂H
  have hca : (w * w₂) * a * (w * w₂)⁻¹ = x := by
    have h1 : (w * w₂) * a * (w * w₂)⁻¹ = w * (w₂ * a * w₂⁻¹) * w⁻¹ := by group
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    rw [h1, hw₂a]
    simp only [x']
    rw [hwinv]
    calc w * (w * x * w) * w = (w * w) * x * (w * w) := by group
      _ = x := by simp [hww]
  have hda : (b⁻¹ * (w * w₂)) * a * (b⁻¹ * (w * w₂))⁻¹ = a := by
    have h1 : (b⁻¹ * (w * w₂)) * a * (b⁻¹ * (w * w₂))⁻¹
        = b⁻¹ * ((w * w₂) * a * (w * w₂)⁻¹) * b := by group
    rw [h1, hca]
    simp only [x]
    group
  have hd_comm : (b⁻¹ * (w * w₂)) * a = a * (b⁻¹ * (w * w₂)) := by
    calc (b⁻¹ * (w * w₂)) * a
        = ((b⁻¹ * (w * w₂)) * a * (b⁻¹ * (w * w₂))⁻¹) * (b⁻¹ * (w * w₂)) := by group
      _ = a * (b⁻¹ * (w * w₂)) := by rw [hda]
  have hdC : b⁻¹ * (w * w₂) ∈ centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hd_comm.symm
  have hdS : b⁻¹ * (w * w₂) ∈ (S : Subgroup G) := by
    rw [← rankOne_centralizer_eq_sylow hG haR ha1]
    exact hdC
  have hAleH : A ≤ H := by
    intro y hy
    have hyR : y ∈ rootCenter (S : Subgroup G) := hAroot hy
    have hycomm : (b⁻¹ * (w * w₂)) * y = y * (b⁻¹ * (w * w₂)) :=
      (mem_rootCenter_iff.mp hyR).2 _ hdS
    have hdyd : (b⁻¹ * (w * w₂)) * y * (b⁻¹ * (w * w₂))⁻¹ = y := by
      calc (b⁻¹ * (w * w₂)) * y * (b⁻¹ * (w * w₂))⁻¹
          = ((b⁻¹ * (w * w₂)) * y) * (b⁻¹ * (w * w₂))⁻¹ := by group
        _ = (y * (b⁻¹ * (w * w₂))) * (b⁻¹ * (w * w₂))⁻¹ := by rw [hycomm]
        _ = y := by group
    have hcy : (w * w₂) * y * (w * w₂)⁻¹ = b * y * b⁻¹ := by
      have hc_eq : w * w₂ = b * (b⁻¹ * (w * w₂)) := by group
      rw [hc_eq]
      calc (b * (b⁻¹ * (w * w₂))) * y * (b * (b⁻¹ * (w * w₂)))⁻¹
          = b * ((b⁻¹ * (w * w₂)) * y * (b⁻¹ * (w * w₂))⁻¹) * b⁻¹ := by group
        _ = b * y * b⁻¹ := by rw [hdyd]
    have hcyH : (w * w₂) * y * (w * w₂)⁻¹ ∈ H := by
      rw [hcy]
      exact hbyH y hy
    have hy_eq : y = (w * w₂)⁻¹ * ((w * w₂) * y * (w * w₂)⁻¹) * (w * w₂) := by group
    rw [hy_eq]
    exact H.mul_mem (H.mul_mem (H.inv_mem hcH) hcyH) hcH
  refine eq_top_iff.mpr ?_
  calc (⊤ : Subgroup G) = A ⊔ A.map (MulAut.conj g).toMonoidHom := hgen.symm
    _ ≤ H := sup_le hAleH le_sup_right

theorem rankOne_zpowers_conj_sup_eq_top
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {S : Sylow 2 G}
    {A : Subgroup G} (hAS : A ≤ (S : Subgroup G)) (hA : IsElemAbelian 2 A) {g : G}
    (hgen : A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.zpowers (g * a * g⁻¹) ⊔ A = ⊤ := by
  let A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom
  have hA' : IsElemAbelian 2 A' := b12_TwelveGen_isElemAbelian_conj hA g
  have hA'S : A' ≤ ((g • S : Sylow 2 G) : Subgroup G) := by
    intro z hz
    simp only [A'] at hz
    rw [mem_sylow_smul_iff g S z]
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    have hthis : g⁻¹ * z * g = y := by
      rw [← hyz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hthis]
    exact hAS hy
  have hcomp : A'.map (MulAut.conj g⁻¹).toMonoidHom = A := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyz⟩
      have hyA : y ∈ A.map (MulAut.conj g).toMonoidHom := hy
      obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp hyA
      rw [← huy] at hyz
      have hthis : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom u) = u := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hthis] at hyz
      rwa [← hyz]
    · intro hz
      refine ⟨(MulAut.conj g).toMonoidHom z, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have hgen' : A' ⊔ A'.map (MulAut.conj g⁻¹).toMonoidHom = ⊤ := by
    rw [hcomp, ← hgen]
    exact sup_comm A' A
  have ha' : g * a * g⁻¹ ∈ A' := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have ha'1 : g * a * g⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have hh := congrArg (MulAut.conj g⁻¹) h
    have hconj : MulAut.conj g⁻¹ (g * a * g⁻¹) = a := by
      simp only [MulAut.conj_apply]
      group
    rwa [hconj, map_one] at hh
  have hres := rankOne_zpowers_sup_conj_eq_top hG (S := g • S) (A := A') hA'S hA' hgen' ha' ha'1
  rw [hcomp] at hres
  exact hres

end Generation

section PartOne

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] {n m : ℕ}

theorem twelveOne_partOne {ρ : G →* LGL 2 V} {B : Subgroup G}
    {Z : Submodule (ZMod 2) V} {A : Subgroup G} (h : Setting12One ρ B Z A n m) {g : G}
    (hgen : A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤) :
    Conclusion121 ρ.range (A.map ρ) (ρ g) (fun a => ∃ a₀ ∈ A, a₀ ≠ 1 ∧ ρ a₀ = a) := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_isBorelIn h.borel
  have hAS : A ≤ (S : Subgroup G) :=
    le_sylow_of_le_normalizer (b12_TwelveGen_isPGroup_of_isElemAbelian h.A_elem) h.A_le_B
  have hgen' : ρ.range = A.map ρ ⊔ cj (ρ g) (A.map ρ) := by
    rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup, map_conj_map_eq_cj]
  refine conclusion121_of_gen
    { g_mem := MonoidHom.mem_range.mpr ⟨g, rfl⟩, gen := hgen', quadratic := h.quad } ?_ ?_
  · intro a _ hPa
    obtain ⟨a₀, ha₀, ha₀1, rfl⟩ := hPa
    have hmap := congrArg (Subgroup.map ρ)
      (rankOne_zpowers_sup_conj_eq_top h.type hAS h.A_elem hgen ha₀ ha₀1)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, map_conj_map_eq_cj,
      Subgroup.map_top] at hmap
    exact hmap.symm
  · intro a _ hPa
    obtain ⟨a₀, ha₀, ha₀1, rfl⟩ := hPa
    have hmap := congrArg (Subgroup.map ρ)
      (rankOne_zpowers_conj_sup_eq_top h.type hAS h.A_elem hgen ha₀ ha₀1)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top] at hmap
    have hconj : (MulAut.conj (ρ g)) (ρ a₀) = ρ (g * a₀ * g⁻¹) := by
      simp [MulAut.conj_apply]
    rw [hconj]
    exact hmap.symm

end PartOne

end CFSG.LocalAnalysis.WeakClosure81
