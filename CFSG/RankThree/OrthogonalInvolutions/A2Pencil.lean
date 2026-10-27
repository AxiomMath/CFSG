module

public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open Module QuadraticMap
open CFSG.RankThree.GF2n.Smith81 (IsOrthA2)

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem sub_one_mul_sub_one_apply_mem_inf {α β : V ≃ₗ[K] V} (hc : Commute α β) (v : V) :
    (((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1)) v ∈
      commSpace α ⊓ commSpace β := by
  have hcomm : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) =
      ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) := by
    have hc' : Commute (α : V →ₗ[K] V) (β : V →ₗ[K] V) := by
      change (α : V →ₗ[K] V) * (β : V →ₗ[K] V) = (β : V →ₗ[K] V) * (α : V →ₗ[K] V)
      rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hc.eq]
    exact (hc'.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  rw [Submodule.mem_inf]
  constructor
  · have h : (((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1)) v =
        ((α : V →ₗ[K] V) - 1) (((β : V →ₗ[K] V) - 1) v) := by
      rw [← Module.End.mul_apply]
      exact congrArg (fun T : V →ₗ[K] V => T v) hcomm.symm
    rw [h]
    exact sub_mem_commSpace α _
  · rw [Module.End.mul_apply]
    exact sub_mem_commSpace β _

private theorem polar_sub_one_apply_sub_one_apply_eq_zero [CharP K 2] {Q : QuadraticForm K V}
    {α β : V ≃ₗ[K] V} (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β)
    (hαβ : IsOrthA2 Q (α * β)) (v : V) :
    polar Q (((α : V →ₗ[K] V) - 1) v) (((β : V →ₗ[K] V) - 1) v) = 0 := by
  have hφv : ((α : V →ₗ[K] V) - 1) v ∈ commSpace α := sub_mem_commSpace α v
  have hψv : ((β : V →ₗ[K] V) - 1) v ∈ commSpace β := sub_mem_commSpace β v
  have hfix : α (((α : V →ₗ[K] V) - 1) v) = ((α : V →ₗ[K] V) - 1) v :=
    mem_fixSpace.mp (commSpace_le_fixSpace hα.mul_self hφv)
  have hdecomp : ((α * β) v - v) =
      α (((β : V →ₗ[K] V) - 1) v) + ((α : V →ₗ[K] V) - 1) v := by
    change α (β v) - v = α (β v - v) + (α v - v)
    rw [map_sub]
    abel
  have h0 : Q (α (((β : V →ₗ[K] V) - 1) v) + ((α : V →ₗ[K] V) - 1) v) = 0 := by
    rw [← hdecomp]
    exact hαβ.vanish _ (sub_mem_commSpace (α * β) v)
  rw [map_add_eq, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hα.mem,
    hβ.vanish _ hψv, hα.vanish _ hφv, zero_add, zero_add,
    polar_apply_eq_polar_apply hα.mem hα.mul_self, hfix, polar_comm Q] at h0
  simpa only [LinearMap.sub_apply, End.one_apply] using h0

private theorem polar_sub_one_mul_sub_one_apply {Q : QuadraticForm K V}
    {α β : V ≃ₗ[K] V} (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) (hc : Commute α β)
    (x y : V) :
    polar Q ((((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1)) x) y =
      polar Q x ((((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1)) y) := by
  have hcomm : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) =
      ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) := by
    have hc' : Commute (α : V →ₗ[K] V) (β : V →ₗ[K] V) := by
      change (α : V →ₗ[K] V) * (β : V →ₗ[K] V) = (β : V →ₗ[K] V) * (α : V →ₗ[K] V)
      rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hc.eq]
    exact (hc'.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  calc polar Q ((((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1)) x) y
      = polar Q (((β : V →ₗ[K] V) - 1) (((α : V →ₗ[K] V) - 1) x)) y := rfl
    _ = polar Q (((α : V →ₗ[K] V) - 1) x) (((β : V →ₗ[K] V) - 1) y) :=
        polar_sub_eq_polar_sub hβ.mem hβ.mul_self _ _
    _ = polar Q x (((α : V →ₗ[K] V) - 1) (((β : V →ₗ[K] V) - 1) y)) :=
        polar_sub_eq_polar_sub hα.mem hα.mul_self _ _
    _ = polar Q x ((((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1)) y) :=
        congrArg (fun T : V →ₗ[K] V => polar Q x (T y)) hcomm

private theorem polar_sub_one_mul_sub_one_apply_self [CharP K 2] {Q : QuadraticForm K V}
    {α β : V ≃ₗ[K] V} (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β)
    (hαβ : IsOrthA2 Q (α * β)) (v : V) :
    polar Q ((((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1)) v) v = 0 := by
  calc polar Q ((((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1)) v) v
      = polar Q (((β : V →ₗ[K] V) - 1) (((α : V →ₗ[K] V) - 1) v)) v := rfl
    _ = polar Q (((α : V →ₗ[K] V) - 1) v) (((β : V →ₗ[K] V) - 1) v) :=
        polar_sub_eq_polar_sub hβ.mem hβ.mul_self _ _
    _ = 0 := polar_sub_one_apply_sub_one_apply_eq_zero hα hβ hαβ v

private theorem eq_zero_of_range_le_span_of_polar_self_eq_zero
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {T : V →ₗ[K] V}
    (hT : ∀ x y, polar Q (T x) y = polar Q x (T y)) {w : V}
    (hrange : ∀ v, T v ∈ Submodule.span K {w})
    (hself : ∀ v, polar Q (T v) v = 0) : T = 0 := by
  by_cases hw : w = 0
  · apply LinearMap.ext
    intro v
    have hv := hrange v
    rw [hw] at hv
    simpa using hv
  · obtain ⟨x, hx⟩ : ∃ x, polar Q w x ≠ 0 := by
      by_contra h
      apply hw
      apply hQ.1 w
      intro y
      by_contra hy
      exact h ⟨y, hy⟩
    obtain ⟨v0, hv0⟩ : ∃ v0, polar Q w v0 = 1 := by
      refine ⟨(polar Q w x)⁻¹ • x, ?_⟩
      rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hx]
    have hT0 : T v0 = 0 := by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hrange v0)
      have hc0 : c = 0 := by
        have h := hself v0
        rw [← hc, polar_smul_left, smul_eq_mul, hv0, mul_one] at h
        exact h
      rw [← hc, hc0, zero_smul]
    apply LinearMap.ext
    intro v
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hrange v)
    have hf := hT v v0
    rw [hT0, polar_zero_right, ← hc, polar_smul_left, smul_eq_mul, hv0, mul_one] at hf
    rw [← hc, hf]
    simp

private theorem finrank_inf_commSpace_le_one_of_ne [FiniteDimensional K V]
    {Q : QuadraticForm K V} {α β : V ≃ₗ[K] V} (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β)
    (hne : commSpace α ≠ commSpace β) :
    finrank K ↥(commSpace α ⊓ commSpace β) ≤ 1 := by
  have hlt : commSpace α ⊓ commSpace β < commSpace α := by
    rw [lt_iff_le_and_ne]
    refine ⟨inf_le_left, ?_⟩
    intro heq
    apply hne
    have hle : commSpace α ≤ commSpace β := by
      simpa [heq] using (inf_le_right : commSpace α ⊓ commSpace β ≤ commSpace β)
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hα.finrank_eq, hβ.finrank_eq])
  have hlt' : finrank K ↥(commSpace α ⊓ commSpace β) < 2 := by
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    rwa [hα.finrank_eq] at h
  omega

private theorem fixSpace_sup_eq_top_of_commSpace_inf_eq_bot [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β)
    (hbot : commSpace α ⊓ commSpace β = ⊥) :
    fixSpace α ⊔ fixSpace β = ⊤ := by
  have hαfix : fixSpace α = LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace α) :=
    fixSpace_eq_orthogonal_commSpace hQ hα.mem hα.mul_self
  have hβfix : fixSpace β = LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace β) :=
    fixSpace_eq_orthogonal_commSpace hQ hβ.mem hβ.mul_self
  have horth : LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace α ⊔ commSpace β) =
      fixSpace α ⊓ fixSpace β := by
    rw [hαfix, hβfix]
    simpa [LinearMap.BilinForm.orthogonal] using
      (Submodule.orthogonalBilin_sup (B := Q.polarBilin) (commSpace α)
        (commSpace β))
  have hdim : finrank K ↥(fixSpace α ⊔ fixSpace β) = finrank K V := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace α) (fixSpace β)
    have h2 : finrank K ↥(fixSpace α ⊓ fixSpace β) =
        finrank K V - finrank K ↥(commSpace α ⊔ commSpace β) := by
      rw [← horth]
      exact LinearMap.BilinForm.finrank_orthogonal hQ _
    have h3 : finrank K ↥(commSpace α ⊔ commSpace β) = 4 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
      rw [hbot, finrank_bot, add_zero, hα.finrank_eq, hβ.finrank_eq] at h
      omega
    have h4 : finrank K ↥(fixSpace α) = finrank K V - 2 := by
      rw [hαfix, LinearMap.BilinForm.finrank_orthogonal hQ, hα.finrank_eq]
    have h5 : finrank K ↥(fixSpace β) = finrank K V - 2 := by
      rw [hβfix, LinearMap.BilinForm.finrank_orthogonal hQ, hβ.finrank_eq]
    have h6 : 4 ≤ finrank K V := h3 ▸ Submodule.finrank_le (commSpace α ⊔ commSpace β)
    rw [h2, h3, h4, h5] at h1
    omega
  exact Submodule.eq_top_of_finrank_eq hdim

private theorem commSpace_sup_le_commSpace_mul_of_fixSpace_sup_eq_top
    {α β : V ≃ₗ[K] V} (hc : Commute α β) (hV : fixSpace α ⊔ fixSpace β = ⊤) :
    commSpace α ⊔ commSpace β ≤ commSpace (α * β) := by
  have hleft : commSpace α ≤ commSpace (α * β) := by
    intro u hu
    obtain ⟨x, hx⟩ := mem_commSpace.mp hu
    have hxV : x ∈ fixSpace α ⊔ fixSpace β := by rw [hV]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hxV
    have hαa : α a = a := mem_fixSpace.mp ha
    have hβb : β b = b := mem_fixSpace.mp hb
    refine mem_commSpace.mpr ⟨b, ?_⟩
    calc (α * β) b - b = α (β b) - b := rfl
      _ = α b - b := by rw [hβb]
      _ = α (a + b) - (a + b) := by rw [map_add, hαa]; abel
      _ = u := hx
  have hright : commSpace β ≤ commSpace (α * β) := by
    intro w hw
    obtain ⟨y, hy⟩ := mem_commSpace.mp hw
    have hyV : y ∈ fixSpace α ⊔ fixSpace β := by rw [hV]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hyV
    have hαa : α a = a := mem_fixSpace.mp ha
    have hβb : β b = b := mem_fixSpace.mp hb
    have hαβa : α (β a) = β a := by
      calc α (β a) = (α * β) a := rfl
        _ = (β * α) a := by rw [hc.eq]
        _ = β (α a) := rfl
        _ = β a := by rw [hαa]
    refine mem_commSpace.mpr ⟨a, ?_⟩
    calc (α * β) a - a = α (β a) - a := rfl
      _ = β a - a := by rw [hαβa]
      _ = β (a + b) - (a + b) := by rw [map_add, hβb]; abel
      _ = w := hy
  exact sup_le hleft hright

private theorem sup_commSpace_le_commSpace_mul [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) (hc : Commute α β)
    (hbot : commSpace α ⊓ commSpace β = ⊥) :
    commSpace α ⊔ commSpace β ≤ commSpace (α * β) :=
  commSpace_sup_le_commSpace_mul_of_fixSpace_sup_eq_top hc
    (fixSpace_sup_eq_top_of_commSpace_inf_eq_bot hQ hα hβ hbot)

private theorem commSpace_inf_commSpace_ne_bot [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) (hc : Commute α β)
    (hαβ : IsOrthA2 Q (α * β)) : commSpace α ⊓ commSpace β ≠ ⊥ := by
  intro hbot
  have hle := sup_commSpace_le_commSpace_mul hQ hα hβ hc hbot
  have hdim : finrank K ↥(commSpace α ⊔ commSpace β) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
    rw [hbot, finrank_bot, add_zero, hα.finrank_eq, hβ.finrank_eq] at h
    omega
  have hmono := Submodule.finrank_mono hle
  rw [hdim, hαβ.finrank_eq] at hmono
  omega

private theorem sub_one_mul_sub_one_eq_zero_of_commSpace_ne [CharP K 2] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) (hc : Commute α β)
    (hαβ : IsOrthA2 Q (α * β)) (hne : commSpace α ≠ commSpace β) :
    ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) = 0 := by
  have hle := finrank_inf_commSpace_le_one_of_ne hα hβ hne
  by_cases hbot : commSpace α ⊓ commSpace β = ⊥
  · apply LinearMap.ext
    intro v
    have hmem := sub_one_mul_sub_one_apply_mem_inf hc v
    rw [hbot, Submodule.mem_bot] at hmem
    simpa using hmem
  · have hfin : finrank K ↥(commSpace α ⊓ commSpace β) = 1 := by
      have hpos : 1 ≤ finrank K ↥(commSpace α ⊓ commSpace β) :=
        Submodule.one_le_finrank_iff.mpr hbot
      omega
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff (commSpace α ⊓ commSpace β)).mp hbot
    have hspan : commSpace α ⊓ commSpace β = Submodule.span K {w} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hfin hw hw0
    exact eq_zero_of_range_le_span_of_polar_self_eq_zero (w := w) hQ
      (fun x y => polar_sub_one_mul_sub_one_apply hα hβ hc x y)
      (fun v => by rw [← hspan]; exact sub_one_mul_sub_one_apply_mem_inf hc v)
      (fun v => polar_sub_one_mul_sub_one_apply_self hα hβ hαβ v)

private theorem polar_eq_zero_of_mem_commSpace_of_mem_commSpace_of_mul_eq_zero
    {Q : QuadraticForm K V} {α β : V ≃ₗ[K] V}
    (hQ : Q.polarBilin.Nondegenerate) (hβ : IsOrthA2 Q β)
    (hT : ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) = 0)
    {u w : V} (hu : u ∈ commSpace α) (hw : w ∈ commSpace β) : polar Q u w = 0 := by
  obtain ⟨x, hx⟩ := mem_commSpace.mp hu
  have hx' : ((α : V →ₗ[K] V) - 1) x = u := by
    simpa only [LinearMap.sub_apply, End.one_apply, LinearEquiv.coe_coe] using hx
  have h : ((β : V →ₗ[K] V) - 1) (((α : V →ₗ[K] V) - 1) x) = 0 := by
    rw [← Module.End.mul_apply]
    exact LinearMap.congr_fun hT x
  have hfix : ((α : V →ₗ[K] V) - 1) x ∈ fixSpace β := by
    rw [fixSpace, LinearMap.mem_ker]
    exact h
  have hmem : ((α : V →ₗ[K] V) - 1) x ∈
      LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace β) := by
    rw [← fixSpace_eq_orthogonal_commSpace hQ hβ.mem hβ.mul_self]
    exact hfix
  have hzero : polar Q (((α : V →ₗ[K] V) - 1) x) w = 0 := by
    rw [polar_comm Q]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hmem) w hw
  rwa [hx'] at hzero

private theorem q_eq_zero_of_mem_commSpace_sup [CharP K 2] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) (hc : Commute α β)
    (hαβ : IsOrthA2 Q (α * β)) (hne : commSpace α ≠ commSpace β) :
    ∀ x ∈ commSpace α ⊔ commSpace β, Q x = 0 := by
  have hT := sub_one_mul_sub_one_eq_zero_of_commSpace_ne hQ hα hβ hc hαβ hne
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add_eq, hα.vanish u hu, hβ.vanish w hw, zero_add, zero_add]
  exact polar_eq_zero_of_mem_commSpace_of_mem_commSpace_of_mul_eq_zero hQ hβ hT hu hw

theorem commSpace_eq_or_pencil_of_mul [CharP K 2] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) (hc : Commute α β) (hαβ : IsOrthA2 Q (α * β)) :
    commSpace α = commSpace β ∨
      (finrank K ↥(commSpace α ⊓ commSpace β) = 1 ∧
        ∀ x ∈ commSpace α ⊔ commSpace β, Q x = 0) := by
  by_cases hne : commSpace α = commSpace β
  · exact Or.inl hne
  · right
    have hnebot := commSpace_inf_commSpace_ne_bot hQ hα hβ hc hαβ
    have hle := finrank_inf_commSpace_le_one_of_ne hα hβ hne
    have hpos : 1 ≤ finrank K ↥(commSpace α ⊓ commSpace β) :=
      Submodule.one_le_finrank_iff.mpr hnebot
    exact ⟨le_antisymm hle hpos, q_eq_zero_of_mem_commSpace_sup hQ hα hβ hc hαβ hne⟩

end CFSG.RankThree.OrthogonalInvolutions
