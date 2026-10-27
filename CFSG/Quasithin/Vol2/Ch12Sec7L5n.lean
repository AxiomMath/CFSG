module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5m
public import CFSG.Quasithin.Background.FFC4Pair

public section

namespace CFSG.Quasithin.H13.S127.L5.Sp4

open CFSG.Open Matrix

variable {G : Type} [Group G] {F : Type} [Field F]

abbrev mat (g : ↥(StatedSp 2 F)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)

theorem mat_upperHom (a b c : F) :
    mat (upperHom (Multiplicative.ofAdd (a, b, c))) = upperMat (symMat a b c) := rfl

theorem mat_inv_mulVec (g : ↥(StatedSp 2 F)) (v : Fin 2 ⊕ Fin 2 → F) :
    mat g⁻¹ *ᵥ (mat g *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec]
  show ((g⁻¹ * g : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F).val *ᵥ v = v
  rw [inv_mul_cancel]
  exact Matrix.one_mulVec v

structure StdSplit (K U Z V : Subgroup G) (α : ↥K →* ↥(StatedSp 2 F))
    (β : ↥U →* Multiplicative (Fin 2 ⊕ Fin 2 → F)) : Prop where
  comm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  sq : ∀ a ∈ U, a ^ 2 = 1
  normU : K ≤ Subgroup.normalizer (U : Set G)
  kerc : ∀ k : ↥K, α k = 1 → ∀ u ∈ U, (k : G) * u = u * k
  surjα : Function.Surjective α
  surjβ : Function.Surjective β
  kerβ : β.ker = Z.subgroupOf U
  ZU : Z ≤ U
  Zc : ∀ z ∈ Z, ∀ k ∈ K, k * z = z * k
  equiv : ∀ (k : ↥K) (u v : ↥U), (v : G) = k * u * k⁻¹ →
    Multiplicative.toAdd (β v) = mat (α k) *ᵥ Multiplicative.toAdd (β u)
  VU : V ≤ U
  memV : ∀ u : ↥U, (u : G) ∈ V ↔ Multiplicative.toAdd (β u) ∈ ell0

namespace StdSplit

variable {K U Z V : Subgroup G} {α : ↥K →* ↥(StatedSp 2 F)}
  {β : ↥U →* Multiplicative (Fin 2 ⊕ Fin 2 → F)} (s : StdSplit K U Z V α β)
include s

theorem conj_mem {k : G} (hk : k ∈ K) {u : G} (hu : u ∈ U) : k * u * k⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.mp (s.normU hk) u).mp hu

theorem mem_Z {u : ↥U} (h : Multiplicative.toAdd (β u) = 0) : (u : G) ∈ Z := by
  have hk : u ∈ β.ker := MonoidHom.mem_ker.mpr h
  rw [s.kerβ] at hk
  exact Subgroup.mem_subgroupOf.mp hk

theorem Z_le_V : Z ≤ V := fun z hz => by
  have hk : (⟨z, s.ZU hz⟩ : ↥U) ∈ β.ker := by
    rw [s.kerβ]
    exact Subgroup.mem_subgroupOf.mpr hz
  have h1 : Multiplicative.toAdd (β ⟨z, s.ZU hz⟩) = 0 := MonoidHom.mem_ker.mp hk
  exact (s.memV ⟨z, s.ZU hz⟩).mpr (by rw [h1]; exact ell0.zero_mem)

omit s in
theorem toAdd_mul_inv (a b : ↥U) :
    Multiplicative.toAdd (β (a * b⁻¹)) =
      Multiplicative.toAdd (β a) - Multiplicative.toAdd (β b) := by
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]

theorem kerc_V {k : ↥K} (hk : α k = 1) {v : G} (hv : v ∈ V) : (k : G) * v = v * k :=
  s.kerc k hk v (s.VU hv)

theorem centralize_of_upper_ker [Fintype F] {k : ↥K} {a b c : F}
    (hk : α k = upperHom (Multiplicative.ofAdd (a, b, c))) {y : Fin 2 → F} (hy : y ≠ 0)
    (hSy : symMat a b c *ᵥ y = 0) {v : G} (hv : v ∈ V) : (k : G) * v = v * k := by
  obtain ⟨u₀, hu₀⟩ := s.surjβ (Multiplicative.ofAdd (Sum.elim 0 y))
  have hu₀' : Multiplicative.toAdd (β u₀) = Sum.elim (0 : Fin 2 → F) y := by rw [hu₀]; rfl
  set vU : ↥U := ⟨v, s.VU hv⟩ with hvU
  set x : Fin 2 → F := fun i => Multiplicative.toAdd (β vU) (Sum.inl i) with hx
  have hβv : Multiplicative.toAdd (β vU) = Sum.elim x 0 := by
    have hmem := (s.memV vU).mp hv
    funext i
    rcases i with i | i
    · rfl
    · exact mem_ell0.mp hmem i
  obtain ⟨a', b', c', hS'⟩ := exists_symMat_mulVec hy x
  obtain ⟨c₀, hc₀⟩ := s.surjα (upperHom (Multiplicative.ofAdd (a', b', c')))
  have hu₁U : (c₀ : G) * u₀ * (c₀ : G)⁻¹ ∈ U := s.conj_mem c₀.2 u₀.2
  set u₁ : ↥U := ⟨_, hu₁U⟩ with hu₁
  have hβu₁ : Multiplicative.toAdd (β u₁) = Sum.elim x y := by
    rw [s.equiv c₀ u₀ u₁ rfl, hc₀, mat_upperHom, hu₀', upperMat_mulVec]
    funext i
    rcases i with i | i
    · simp [hS']
    · simp
  have hku₀U : (k : G) * u₀ * (k : G)⁻¹ ∈ U := s.conj_mem k.2 u₀.2
  have hβku₀ : Multiplicative.toAdd (β ⟨_, hku₀U⟩) = Multiplicative.toAdd (β u₀) := by
    rw [s.equiv k u₀ ⟨_, hku₀U⟩ rfl, hk, mat_upperHom, hu₀', upperMat_mulVec]
    funext i
    rcases i with i | i
    · simp [hSy]
    · simp
  set e₀ : G := (k : G) * u₀ * (k : G)⁻¹ * (u₀ : G)⁻¹ with he₀
  have he₀Z : e₀ ∈ Z := by
    have h := s.mem_Z (u := ⟨_, hku₀U⟩ * u₀⁻¹) (by rw [toAdd_mul_inv, hβku₀, sub_self])
    simpa [he₀] using h
  have he₀U : e₀ ∈ U := s.ZU he₀Z
  set o : ↥K := k⁻¹ * c₀⁻¹ * k * c₀ with ho
  have hαo : α o = 1 := by
    have hcomm : α k * α c₀ = α c₀ * α k := by
      rw [hk, hc₀, ← map_mul upperHom, ← map_mul upperHom,
        mul_comm (Multiplicative.ofAdd (a, b, c))]
    simp only [ho, map_mul α, map_inv α]
    rw [mul_assoc _ (α k) (α c₀), hcomm]
    group
  have hou₀ : (o : G) * u₀ = u₀ * o := s.kerc o hαo u₀ u₀.2
  have hku₁ : (k : G) * u₁ * (k : G)⁻¹ = e₀ * u₁ := by
    have h1 : (c₀ : G)⁻¹ * (k : G) * (c₀ : G) = (k : G) * (o : G) := by
      rw [ho]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h3 : (o : G) * u₀ * (o : G)⁻¹ = u₀ := by rw [hou₀, mul_inv_cancel_right]
    have h4 : (c₀ : G) * e₀ * (c₀ : G)⁻¹ = e₀ := by
      rw [s.Zc e₀ he₀Z c₀ c₀.2, mul_inv_cancel_right]
    have hke : (k : G) * u₀ * (k : G)⁻¹ = e₀ * u₀ := by rw [he₀]; group
    show (k : G) * ((c₀ : G) * u₀ * (c₀ : G)⁻¹) * (k : G)⁻¹ =
      e₀ * ((c₀ : G) * u₀ * (c₀ : G)⁻¹)
    calc (k : G) * ((c₀ : G) * u₀ * (c₀ : G)⁻¹) * (k : G)⁻¹
        = (c₀ : G) * ((c₀ : G)⁻¹ * (k : G) * (c₀ : G)) * u₀ *
            ((c₀ : G)⁻¹ * (k : G) * (c₀ : G))⁻¹ * (c₀ : G)⁻¹ := by group
      _ = (c₀ : G) * ((k : G) * ((o : G) * u₀ * (o : G)⁻¹) * (k : G)⁻¹) * (c₀ : G)⁻¹ := by
          rw [h1]; group
      _ = (c₀ : G) * (e₀ * u₀) * (c₀ : G)⁻¹ := by rw [h3, hke]
      _ = ((c₀ : G) * e₀ * (c₀ : G)⁻¹) * ((c₀ : G) * u₀ * (c₀ : G)⁻¹) := by group
      _ = e₀ * ((c₀ : G) * u₀ * (c₀ : G)⁻¹) := by rw [h4]
  have hz : v * ((u₁ : G) * (u₀ : G)⁻¹)⁻¹ ∈ Z := by
    have h := s.mem_Z (u := vU * (u₁ * u₀⁻¹)⁻¹) (by
      rw [toAdd_mul_inv, toAdd_mul_inv, hβv, hβu₁, hu₀']
      funext i
      rcases i with i | i <;> simp)
    simpa using h
  set z : G := v * ((u₁ : G) * (u₀ : G)⁻¹)⁻¹ with hzdef
  have hvz : v = z * (u₁ * (u₀ : G)⁻¹) := by rw [hzdef]; group
  have hkz : (k : G) * z * (k : G)⁻¹ = z := by
    rw [s.Zc z hz k k.2, mul_inv_cancel_right]
  have hku₀' : (k : G) * u₀ * (k : G)⁻¹ = e₀ * u₀ := by rw [he₀]; group
  have hcomm₂ : e₀ * ((u₁ : G) * (u₀ : G)⁻¹) = ((u₁ : G) * (u₀ : G)⁻¹) * e₀ :=
    s.comm e₀ he₀U _ (U.mul_mem u₁.2 (U.inv_mem u₀.2))
  have hkv : (k : G) * v * (k : G)⁻¹ = v := by
    calc (k : G) * v * (k : G)⁻¹
        = ((k : G) * z * (k : G)⁻¹) * ((k : G) * u₁ * (k : G)⁻¹) *
            ((k : G) * u₀ * (k : G)⁻¹)⁻¹ := by rw [hvz]; group
      _ = z * (e₀ * u₁) * (e₀ * u₀)⁻¹ := by rw [hkz, hku₁, hku₀']
      _ = z * (e₀ * ((u₁ : G) * (u₀ : G)⁻¹)) * e₀⁻¹ := by group
      _ = v := by rw [hcomm₂, hvz]; group
  calc (k : G) * v = (k : G) * v * (k : G)⁻¹ * k := by group
    _ = v * k := by rw [hkv]

theorem centralize_of_upper [Fintype F] (hF : Fintype.card F = 4) {k : ↥K} {a b c : F}
    (hk : α k = upperHom (Multiplicative.ofAdd (a, b, c))) {v : G} (hv : v ∈ V) :
    (k : G) * v = v * k := by
  have : CharP F 2 :=
    FFC.charP_two_of_card_pow (n := 2) (by rw [Nat.card_eq_fintype_card, hF]; norm_num)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨k₁, hk₁⟩ := s.surjα (upperHom (Multiplicative.ofAdd (a + b, 0, 0)))
  obtain ⟨k₂, hk₂⟩ := s.surjα (upperHom (Multiplicative.ofAdd (0, 0, c + b)))
  obtain ⟨k₃, hk₃⟩ := s.surjα (upperHom (Multiplicative.ofAdd (b, b, b)))
  have e₁ := s.centralize_of_upper_ker hk₁ (y := ![0, 1]) (by
    intro h; have := congrFun h 1; simp at this) (by
    funext i; fin_cases i <;> simp [symMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]) hv
  have e₂ := s.centralize_of_upper_ker hk₂ (y := ![1, 0]) (by
    intro h; have := congrFun h 0; simp at this) (by
    funext i; fin_cases i <;> simp [symMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]) hv
  have e₃ := s.centralize_of_upper_ker hk₃ (y := ![1, 1]) (by
    intro h; have := congrFun h 0; simp at this) (by
    funext i; fin_cases i <;>
      simp [symMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ← two_mul, h2]) hv
  set o : ↥K := (k₁ * k₂ * k₃)⁻¹ * k with ho
  have hm : Multiplicative.ofAdd (a + b, (0 : F), (0 : F)) * Multiplicative.ofAdd (0, 0, c + b) *
      Multiplicative.ofAdd (b, b, b) = Multiplicative.ofAdd (a, b, c) := by
    rw [← ofAdd_add, ← ofAdd_add]
    congr 1
    simp only [Prod.mk_add_mk]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show a + b + 0 + b = a
      linear_combination b * h2
    · show (0 : F) + 0 + b = b
      ring
    · show (0 : F) + (c + b) + b = c
      linear_combination b * h2
  have hαo : α o = 1 := by
    rw [ho, map_mul α, map_inv α, map_mul α, map_mul α, hk₁, hk₂, hk₃, hk, ← hm,
      map_mul upperHom, map_mul upperHom, inv_mul_cancel]
  have eo := s.kerc_V hαo hv
  have hkk : (k : G) = k₁ * k₂ * k₃ * o := by
    rw [ho]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hkk]
  calc (k₁ : G) * k₂ * k₃ * o * v = k₁ * k₂ * k₃ * (o * v) := by group
    _ = k₁ * k₂ * (k₃ * v) * o := by rw [eo]; group
    _ = k₁ * (k₂ * v) * k₃ * o := by rw [e₃]; group
    _ = k₁ * v * k₂ * k₃ * o := by rw [e₂]; group
    _ = v * (k₁ * k₂ * k₃ * o) := by rw [e₁]; group

theorem centralize_of_fix [Fintype F] (hF : Fintype.card F = 4) {k : ↥K}
    (hk : ∀ x : Fin 2 → F, mat (α k) *ᵥ Sum.elim x 0 = Sum.elim x 0) {v : G} (hv : v ∈ V) :
    (k : G) * v = v * k := by
  obtain ⟨a, b, c, h⟩ := eq_upperMat_of_fix (α k) hk
  refine s.centralize_of_upper hF (a := a) (b := b) (c := c) ?_ hv
  apply Subtype.ext
  apply Units.ext
  rw [coe_upperHom]
  exact h

theorem mulVec_mem_ell0 {g : ↥K} (hg : (g : G) ∈ Subgroup.normalizer (V : Set G))
    {w : Fin 2 ⊕ Fin 2 → F} (hw : w ∈ (ell0 : Submodule F _)) :
    mat (α g) *ᵥ w ∈ (ell0 : Submodule F _) := by
  obtain ⟨u, hu⟩ := s.surjβ (Multiplicative.ofAdd w)
  have hu' : Multiplicative.toAdd (β u) = w := by rw [hu]; rfl
  have huV : (u : G) ∈ V := (s.memV u).mpr (by rw [hu']; exact hw)
  have hgu : (g : G) * u * (g : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg u).mp huV
  have := (s.memV ⟨_, s.VU hgu⟩).mp hgu
  rwa [s.equiv g u ⟨_, s.VU hgu⟩ rfl, hu'] at this

end StdSplit

end CFSG.Quasithin.H13.S127.L5.Sp4
