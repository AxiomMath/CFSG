module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit Subgroup
open CFSG.QuasithinUnique.Setup.X1

private theorem m4_mem_normalizer_zpowers {G : Type} [Group G] {a b : G}
    (h : b * a * b⁻¹ ∈ Subgroup.zpowers a)
    (h' : b⁻¹ * a * b ∈ Subgroup.zpowers a) :
    b ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
    exact h
  · rw [Subgroup.zpowers_le, Subgroup.mem_map]
    refine ⟨b⁻¹ * a * b, h', ?_⟩
    change b * (b⁻¹ * a * b) * b⁻¹ = a
    group

private noncomputable def m4_restrictHom {P : Type} [Group P] (K : Subgroup (MulAut P))
    (U : Subgroup P) (hU : ∀ k ∈ K, ∀ x ∈ U, (k : MulAut P) x ∈ U) : ↥K →* MulAut ↥U where
  toFun k :=
    { toFun := fun x => ⟨(k : MulAut P) x, hU k k.2 x x.2⟩
      invFun := fun x => ⟨(k : MulAut P)⁻¹ x, hU k⁻¹ (K.inv_mem k.2) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  map_one' := by ext x; simp
  map_mul' k k' := by ext x; simp

theorem exists_fpf_module_of_order_three {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Y : Subgroup (MulAut W)} {ζ : MulAut W} (hζY : ζ ∈ Y)
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (hnorm : ∀ y ∈ Y, y * ζ * y⁻¹ = ζ ∨ y * ζ * y⁻¹ = ζ⁻¹) :
    ∃ (U : Type) (_ : CommGroup U) (_ : Finite U) (ρ : ↥Y →* MulAut U),
      (∀ u : U, u * u = 1) ∧ Nontrivial U ∧ (∀ u : U, ρ ⟨ζ, hζY⟩ u = u → u = 1) ∧
        ∀ y : ↥Y, (fixV (zpowers (ρ y))).index ≤ (fixV (zpowers (y : MulAut W))).index := by
  classical
  let A : Subgroup (MulAut W) := Subgroup.zpowers ζ
  have hA : A = Subgroup.zpowers ζ := rfl
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hcardA : Nat.card ↥A = 3 := by rw [hA, Nat.card_zpowers, hord]
  have hodd : Odd (Nat.card ↥A) := by rw [hcardA]; norm_num
  have hζA : ζ ∈ A := by rw [hA]; exact Subgroup.mem_zpowers ζ
  have hnormA : ∀ y ∈ Y, y ∈ Subgroup.normalizer (A : Set (MulAut W)) := by
    intro y hy
    have h1 : y * ζ * y⁻¹ ∈ Subgroup.zpowers ζ := by
      rcases hnorm y hy with h | h
      · rw [h]; exact Subgroup.mem_zpowers ζ
      · rw [h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)
    have h1' : y⁻¹ * ζ * y ∈ Subgroup.zpowers ζ := by
      have hc : y⁻¹ * ζ * y = ζ ∨ y⁻¹ * ζ * y = ζ⁻¹ := by
        rcases hnorm y hy with h | h
        · left
          have : y⁻¹ * (y * ζ * y⁻¹) * y = ζ := by group
          rwa [h] at this
        · right
          have : y⁻¹ * (y * ζ * y⁻¹)⁻¹ * y = ζ⁻¹ := by group
          rwa [h] at this
      rcases hc with h | h
      · rw [h]; exact Subgroup.mem_zpowers ζ
      · rw [h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)
    rw [hA]
    exact m4_mem_normalizer_zpowers h1 h1'
  let U₀ : Subgroup W := (normHom A).ker
  have hInv : ∀ y ∈ Y, ∀ u ∈ U₀, y u ∈ U₀ := fun y hy u hu =>
    map_ker_normHom (hnormA y hy) hu
  have hfix : fixV A ⊓ (normHom A).ker = ⊥ := fixV_inf_ker_normHom hW hodd
  have hcardK : Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W :=
    card_ker_normHom_mul hW hodd
  have hU₀ne : U₀ ≠ ⊥ := by
    intro hbot
    have hker1 : Nat.card ↥(normHom A).ker = 1 := by
      change Nat.card ↥U₀ = 1
      rw [hbot, Subgroup.card_bot]
    have hcard' := hcardK
    rw [hker1, mul_one] at hcard'
    have htop : fixV A = ⊤ := Subgroup.eq_top_of_card_eq _ hcard'
    apply hζ1
    ext w
    have hw : w ∈ fixV A := by rw [htop]; exact Subgroup.mem_top w
    exact mem_fixV.1 hw ζ hζA
  have hNontriv : Nontrivial ↥U₀ := (Subgroup.nontrivial_iff_ne_bot U₀).2 hU₀ne
  have hU₂ : ∀ u : ↥U₀, u * u = 1 := fun u => Subtype.ext (hW (u : W))
  let ρ : ↥Y →* MulAut ↥U₀ := m4_restrictHom Y U₀ hInv
  have hρval : ∀ (y : ↥Y) (u : ↥U₀), ((ρ y u : ↥U₀) : W) = (y : MulAut W) (u : W) :=
    fun y u => rfl
  have hfpf : ∀ u : ↥U₀, ρ ⟨ζ, hζY⟩ u = u → u = 1 := by
    intro u hu
    have huW : (u : W) ∈ fixV A := by
      rw [hA, mem_fixV_zpowers]
      simpa only [hρval] using congrArg Subtype.val hu
    have hmem : (u : W) ∈ fixV A ⊓ (normHom A).ker := Subgroup.mem_inf.2 ⟨huW, u.2⟩
    rw [hfix, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hdisp : ∀ y : ↥Y, (fixV (Subgroup.zpowers (ρ y))).index ≤
      (fixV (Subgroup.zpowers (y : MulAut W))).index := by
    intro y
    let φW : W →* W := MonoidHom.mk' (fun w => (y : MulAut W) w * w⁻¹) (fun a b => by
      simp only [map_mul, mul_inv_rev]
      ac_rfl)
    have hkerW : φW.ker = fixV (Subgroup.zpowers (y : MulAut W)) := by
      ext w
      rw [MonoidHom.mem_ker, mem_fixV_zpowers]
      change (y : MulAut W) w * w⁻¹ = 1 ↔ (y : MulAut W) w = w
      constructor
      · intro h
        have := congrArg (· * w) h
        simpa [mul_assoc] using this
      · intro h
        rw [h, mul_inv_cancel]
    have hidxW : (fixV (Subgroup.zpowers (y : MulAut W))).index = Nat.card φW.range := by
      rw [← hkerW, Subgroup.index_ker]
    let φU : ↥U₀ →* ↥U₀ := MonoidHom.mk' (fun u => ρ y u * u⁻¹) (fun a b => by
      simp only [map_mul, mul_inv_rev]
      ac_rfl)
    have hkerU : φU.ker = fixV (Subgroup.zpowers (ρ y)) := by
      ext u
      rw [MonoidHom.mem_ker, mem_fixV_zpowers]
      change ρ y u * u⁻¹ = 1 ↔ ρ y u = u
      constructor
      · intro h
        have := congrArg (· * u) h
        simpa [mul_assoc] using this
      · intro h
        rw [h, mul_inv_cancel]
    have hidxU : (fixV (Subgroup.zpowers (ρ y))).index = Nat.card φU.range := by
      rw [← hkerU, Subgroup.index_ker]
    have hcard_le : Nat.card φU.range ≤ Nat.card φW.range := by
      refine Nat.card_le_card_of_injective
        (fun x : φU.range => (⟨(x : ↥U₀), ?_⟩ : φW.range)) ?_
      · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 x.2
        refine MonoidHom.mem_range.2 ⟨(u : W), ?_⟩
        rw [← hu]
        rfl
      · intro x z hxz
        have h1 : ((x : ↥U₀) : W) = ((z : ↥U₀) : W) :=
          congrArg (fun t : φW.range => (t : W)) hxz
        exact Subtype.ext (Subtype.ext h1)
    rw [hidxU, hidxW]
    exact hcard_le
  exact ⟨↥U₀, inferInstance, inferInstance, ρ, hU₂, hNontriv, hfpf, hdisp⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
