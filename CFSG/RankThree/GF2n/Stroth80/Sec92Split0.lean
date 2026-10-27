module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GF2n.Stroth80.Split92

variable {Γ : Type*} [Group Γ] {K E : Type*} [Semiring K] [AddCommGroup E] [Module K E]

theorem rho_conj_apply (ρ : Γ →* (E ≃ₗ[K] E)) (g n : Γ) (w : E) :
    ρ (g * n * g⁻¹) w = ρ g (ρ n (ρ g⁻¹ w)) := by
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]

theorem rho_rho_inv (ρ : Γ →* (E ≃ₗ[K] E)) (g : Γ) (w : E) : ρ g (ρ g⁻¹ w) = w := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one, id]

theorem rho_inv_rho (ρ : Γ →* (E ≃ₗ[K] E)) (g : Γ) (w : E) : ρ g⁻¹ (ρ g w) = w := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one, id]

theorem alpha_conj' (ρ : Γ →* (E ≃ₗ[K] E)) (u x : Γ) (y : E) :
    ρ (u * x * u⁻¹) (ρ u y) - ρ u y = ρ u (ρ x y - y) := by
  rw [rho_conj_apply, rho_inv_rho, map_sub]

theorem alpha_mul (ρ : Γ →* (E ≃ₗ[K] E)) {Vt : AddSubgroup E} {n n' : Γ}
    (hn : ∀ v ∈ Vt, ρ n v = v) {w : E} (hw : ρ n' w - w ∈ Vt) :
    ρ (n * n') w - w = (ρ n w - w) + (ρ n' w - w) := by
  have e : ρ n' w = w + (ρ n' w - w) := by abel
  rw [map_mul, LinearEquiv.mul_apply, e, map_add, hn _ hw]
  abel

theorem alpha_add_V (ρ : Γ →* (E ≃ₗ[K] E)) {n : Γ} {w v : E} (hv : ρ n v = v) :
    ρ n (w + v) - (w + v) = ρ n w - w := by
  rw [map_add, hv]
  abel

theorem alpha_conj (ρ : Γ →* (E ≃ₗ[K] E)) (g n : Γ) (w : E) :
    ρ (g * n * g⁻¹) w - w = ρ g (ρ n (ρ g⁻¹ w) - ρ g⁻¹ w) := by
  rw [rho_conj_apply, map_sub, rho_rho_inv]

theorem alpha_conj_of_triv (ρ : Γ →* (E ≃ₗ[K] E)) {Vt : AddSubgroup E} {n e : Γ}
    (hn : ∀ v ∈ Vt, ρ n v = v) {w : E} (hw : ρ e⁻¹ w - w ∈ Vt) :
    ρ (e * n * e⁻¹) w - w = ρ e (ρ n w - w) := by
  rw [alpha_conj]
  congr 1
  have e1 : ρ e⁻¹ w = w + (ρ e⁻¹ w - w) := by abel
  rw [e1, alpha_add_V ρ (hn _ hw)]

@[expose] def fixSub (ρ : Γ →* (E ≃ₗ[K] E)) (Vt : AddSubgroup E) (X : Set Γ) : AddSubgroup E where
  carrier := {v | v ∈ Vt ∧ ∀ x ∈ X, ρ x v = v}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Vt.add_mem ha hb, fun x hx => by rw [map_add, ha' x hx, hb' x hx]⟩
  zero_mem' := ⟨Vt.zero_mem, fun x _ => map_zero _⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨Vt.neg_mem ha, fun x hx => by rw [map_neg, ha' x hx]⟩

theorem rho_mem_fixSub (ρ : Γ →* (E ≃ₗ[K] E)) {Vt : AddSubgroup E} {N : Subgroup Γ} {X : Set Γ}
    (hVt : ∀ g : Γ, ∀ v ∈ Vt, ρ g v ∈ Vt) (hNV : ∀ n ∈ N, ∀ v ∈ Vt, ρ n v = v)
    {g : Γ} (hg : ∀ x ∈ X, x⁻¹ * (g⁻¹ * x * g) ∈ N) {v : E} (hv : v ∈ fixSub ρ Vt X) :
    ρ g v ∈ fixSub ρ Vt X := by
  refine ⟨hVt g v hv.1, fun x hx => ?_⟩
  have h1 : ρ (g⁻¹ * x * g) v = v := by
    have e : g⁻¹ * x * g = x * (x⁻¹ * (g⁻¹ * x * g)) := by group
    rw [e, map_mul, LinearEquiv.mul_apply, hNV _ (hg x hx) v hv.1, hv.2 x hx]
  calc ρ x (ρ g v) = ρ g (ρ (g⁻¹ * x * g) v) := by
        rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
    _ = ρ g v := by rw [h1]

variable {S : Type*} [Group S]

structure AlphaData (ρ : Γ →* (E ≃ₗ[K] E)) (Vt Wt : AddSubgroup E) (ψ : Γ →* S × S) : Prop where
  surj : Function.Surjective ψ
  V_inv : ∀ g : Γ, ∀ v ∈ Vt, ρ g v ∈ Vt
  W_inv : ∀ g : Γ, ∀ w ∈ Wt, ρ g w ∈ Wt
  NV : ∀ n ∈ ψ.ker, ∀ v ∈ Vt, ρ n v = v
  NW : ∀ n ∈ ψ.ker, ∀ w ∈ Wt, ρ n w - w ∈ Vt
  R₀W : ∀ e : Γ, (ψ e).2 = 1 → ∀ w ∈ Wt, ρ e w - w ∈ Vt
  R₀V : ∀ v ∈ Vt, (∀ e : Γ, (ψ e).2 = 1 → ρ e v = v) → v = 0

structure AlphaPair (ρ : Γ →* (E ≃ₗ[K] E)) (ψ : Γ →* S × S) (LB LA : Subgroup Γ)
    (U₁ U₂ U₁' U₂' : Subgroup S) : Prop where
  commB : ∀ a ∈ LB, ∀ b ∈ LB, ρ a * ρ b = ρ b * ρ a
  commA : ∀ a ∈ LA, ∀ b ∈ LA, ρ a * ρ b = ρ b * ρ a
  prodB : LB.map ψ = U₁.prod U₂
  prodA : LA.map ψ = U₁'.prod U₂'
  N_eq : ∀ n ∈ ψ.ker, ∃ a ∈ LB ⊓ ψ.ker, ∃ b ∈ LA ⊓ ψ.ker, n = a * b
  gen : U₁ ⊔ U₁' = ⊤
  U₂_ne : U₂ ≠ ⊥
  U₁'_ne : U₁' ≠ ⊥

namespace AlphaData

variable {ρ : Γ →* (E ≃ₗ[K] E)} {Vt Wt : AddSubgroup E} {ψ : Γ →* S × S}

theorem alpha_mem_fixSub (hD : AlphaData ρ Vt Wt ψ) {L : Subgroup Γ}
    (hL : ∀ a ∈ L, ∀ b ∈ L, ρ a * ρ b = ρ b * ρ a) {l : Γ} (hl : l ∈ L ⊓ ψ.ker) {w : E}
    (hw : w ∈ Wt) : ρ l w - w ∈ fixSub ρ Vt {e | e ∈ L ∧ (ψ e).2 = 1} := by
  refine ⟨hD.NW l hl.2 w hw, fun e he => ?_⟩
  have he' : (ψ e⁻¹).2 = 1 := by rw [map_inv, Prod.snd_inv, he.2, inv_one]
  have h1 := alpha_conj_of_triv ρ (hD.NV l hl.2) (hD.R₀W e⁻¹ he' w hw)
  have h2 : ρ (e * l * e⁻¹) = ρ l := by
    rw [map_mul, map_mul, hL e he.1 l hl.1, mul_assoc, ← map_mul, mul_inv_cancel, map_one,
      mul_one]
  rw [h2] at h1
  exact h1.symm

theorem alpha_inv (hD : AlphaData ρ Vt Wt ψ) {n : Γ} (hn : n ∈ ψ.ker) {w : E} (hw : w ∈ Wt) :
    ρ n⁻¹ w - w = -(ρ n w - w) := by
  have h1 := alpha_mul ρ (hD.NV n⁻¹ (ψ.ker.inv_mem hn)) (hD.NW n hn w hw)
  rw [inv_mul_cancel, map_one, LinearEquiv.coe_one, id, sub_self] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm

theorem alpha_conj_N (hD : AlphaData ρ Vt Wt ψ) {m y : Γ} (hm : m ∈ ψ.ker) (hy : y ∈ ψ.ker)
    {w : E} (hw : w ∈ Wt) : ρ (m * y * m⁻¹) w - w = ρ y w - w := by
  have hym : y * m⁻¹ ∈ ψ.ker := ψ.ker.mul_mem hy (ψ.ker.inv_mem hm)
  rw [mul_assoc, alpha_mul ρ (hD.NV m hm) (hD.NW _ hym w hw),
    alpha_mul ρ (hD.NV y hy) (hD.NW _ (ψ.ker.inv_mem hm) w hw), hD.alpha_inv hm hw]
  abel

theorem eq_zero_of_fix (hD : AlphaData ρ Vt Wt ψ) {LB LA : Subgroup Γ} {U₁ U₂ U₁' U₂' : Subgroup S}
    (hP : AlphaPair ρ ψ LB LA U₁ U₂ U₁' U₂') {v : E} (hv : v ∈ Vt)
    (hB : ∀ e ∈ LB, (ψ e).2 = 1 → ρ e v = v) (hA : ∀ e ∈ LA, (ψ e).2 = 1 → ρ e v = v) :
    v = 0 := by
  let F : Subgroup Γ :=
    { carrier := {e | ρ e v = v}
      mul_mem' := fun {a b} ha hb => by
        show ρ (a * b) v = v
        rw [map_mul, LinearEquiv.mul_apply, show ρ b v = v from hb, show ρ a v = v from ha]
      one_mem' := by show ρ 1 v = v; rw [map_one]; rfl
      inv_mem' := fun {a} ha => by
        show ρ a⁻¹ v = v
        have h1 : ρ a v = v := ha
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [h1]
          _ = v := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  have hmemF : ∀ e, e ∈ F ↔ ρ e v = v := fun e => Iff.rfl
  have hNF : ψ.ker ≤ F := fun n hn => (hmemF n).mpr (hD.NV n hn v hv)
  let F' : Subgroup S := (F.map ψ).comap (MonoidHom.inl S S)
  have hU₁ : U₁ ≤ F' := by
    intro u hu
    have h1 : ((u, 1) : S × S) ∈ LB.map ψ := by rw [hP.prodB]; exact ⟨hu, Subgroup.one_mem _⟩
    obtain ⟨l, hl, hlu⟩ := h1
    refine ⟨l, (hmemF l).mpr (hB l hl ?_), hlu⟩
    rw [hlu]
  have hU₁' : U₁' ≤ F' := by
    intro u hu
    have h1 : ((u, 1) : S × S) ∈ LA.map ψ := by rw [hP.prodA]; exact ⟨hu, Subgroup.one_mem _⟩
    obtain ⟨l, hl, hlu⟩ := h1
    refine ⟨l, (hmemF l).mpr (hA l hl ?_), hlu⟩
    rw [hlu]
  have hF' : F' = ⊤ := eq_top_iff.mpr (hP.gen ▸ sup_le hU₁ hU₁')
  refine hD.R₀V v hv fun e he => ?_
  have h1 : (ψ e).1 ∈ F' := hF' ▸ Subgroup.mem_top _
  obtain ⟨f, hf, hfe⟩ := h1
  have hfe' : ψ f = ψ e := by
    rw [show ψ e = ((ψ e).1, 1) from Prod.ext rfl he]
    exact hfe
  have hk : f⁻¹ * e ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hfe', inv_mul_cancel]
  have : e ∈ F := by
    rw [show e = f * (f⁻¹ * e) by group]
    exact F.mul_mem hf (hNF hk)
  exact this

theorem alpha_decomp (hD : AlphaData ρ Vt Wt ψ) {LB LA : Subgroup Γ}
    {U₁ U₂ U₁' U₂' : Subgroup S} (hP : AlphaPair ρ ψ LB LA U₁ U₂ U₁' U₂') {n : Γ}
    (hn : n ∈ ψ.ker) (hnW : ∀ w ∈ Wt, ρ n w = w) :
    ∃ a ∈ LB ⊓ ψ.ker, (∀ w ∈ Wt, ρ a w = w) ∧ ∃ b ∈ LA ⊓ ψ.ker, (∀ w ∈ Wt, ρ b w = w) ∧
      n = a * b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hP.N_eq n hn
  have hzero : ∀ w ∈ Wt, ρ a w - w = 0 := by
    intro w hw
    have h1 := alpha_mul ρ (hD.NV a ha.2) (hD.NW b hb.2 w hw)
    rw [hnW w hw, sub_self] at h1
    have hab : ρ a w - w = -(ρ b w - w) := eq_neg_of_add_eq_zero_left h1.symm
    have hBf := hD.alpha_mem_fixSub hP.commB ha hw
    have hAf := hD.alpha_mem_fixSub hP.commA hb hw
    refine hD.eq_zero_of_fix hP hBf.1 (fun e he he2 => hBf.2 e ⟨he, he2⟩) fun e he he2 => ?_
    rw [hab, map_neg, hAf.2 e ⟨he, he2⟩]
  have haW : ∀ w ∈ Wt, ρ a w = w := fun w hw => sub_eq_zero.mp (hzero w hw)
  refine ⟨a, ha, haW, b, hb, fun w hw => ?_, rfl⟩
  have h1 := hnW w hw
  rw [map_mul, LinearEquiv.mul_apply] at h1
  have h2 : ρ a (ρ b w) = ρ a w := by rw [h1, haW w hw]
  exact (ρ a).injective h2

theorem conj_mem_ker {g n : Γ} (hn : n ∈ ψ.ker) : g * n * g⁻¹ ∈ ψ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, MonoidHom.mem_ker.mp hn, mul_one, map_inv,
    mul_inv_cancel]

theorem comm_mem_ker {u g : Γ} (hu : (ψ u).2 = 1) (hg : (ψ g).1 = 1) :
    u⁻¹ * (g⁻¹ * u * g) ∈ ψ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
  refine Prod.ext ?_ ?_
  · simp [hg]
  · simp [hu]

theorem alpha_good [IsSimpleGroup S] (hD : AlphaData ρ Vt Wt ψ) {LB LA : Subgroup Γ}
    {U₁ U₂ U₁' U₂' : Subgroup S} (hP : AlphaPair ρ ψ LB LA U₁ U₂ U₁' U₂') {g : Γ}
    (hgL : g ∈ LB) (hg : (ψ g).1 = 1) {n : Γ} (hn : n ∈ ψ.ker) {w : E} (hw : w ∈ Wt) :
    ρ (g * n * g⁻¹) w - w = ρ n w - w := by
  classical
  let D : Set E := {x | ∃ m ∈ ψ.ker, ∃ y ∈ Wt,
    x = (ρ (g * m * g⁻¹) y - y) - (ρ m y - y)}
  let X : AddSubgroup E := AddSubgroup.closure D
  have hDfix : D ⊆ fixSub ρ Vt {e | e ∈ LA ∧ (ψ e).2 = 1} := by
    rintro _ ⟨m, hm, y, hy, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hP.N_eq m hm
    have hga : g * a * g⁻¹ ∈ ψ.ker := conj_mem_ker ha.2
    have hgb : g * b * g⁻¹ ∈ ψ.ker := conj_mem_ker hb.2
    have e1 : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    have hρa : ρ (g * a * g⁻¹) = ρ a := by
      rw [map_mul, map_mul, hP.commB g hgL a ha.1, mul_assoc, ← map_mul, mul_inv_cancel,
        map_one, mul_one]
    rw [e1, alpha_mul ρ (hD.NV _ hga) (hD.NW _ hgb y hy), hρa,
      alpha_mul ρ (hD.NV a ha.2) (hD.NW b hb.2 y hy)]
    have h1 : ρ (g * b * g⁻¹) y - y ∈ fixSub ρ Vt {e | e ∈ LA ∧ (ψ e).2 = 1} := by
      rw [alpha_conj]
      refine rho_mem_fixSub ρ hD.V_inv hD.NV (fun e he => comm_mem_ker he.2 hg) ?_
      exact hD.alpha_mem_fixSub hP.commA hb (hD.W_inv g⁻¹ y hy)
    have h2 := hD.alpha_mem_fixSub hP.commA hb hy
    have e2 : ρ a y - y + (ρ (g * b * g⁻¹) y - y) - (ρ a y - y + (ρ b y - y)) =
        (ρ (g * b * g⁻¹) y - y) - (ρ b y - y) := by abel
    rw [e2]
    exact (fixSub ρ Vt _).sub_mem h1 h2
  have hXfix : X ≤ fixSub ρ Vt {e | e ∈ LA ∧ (ψ e).2 = 1} :=
    (AddSubgroup.closure_le _).mpr hDfix
  have hDinv : ∀ u : Γ, (ψ u).2 = 1 → ∀ x ∈ D, ρ u x ∈ D := by
    rintro u hu _ ⟨m, hm, y, hy, rfl⟩
    set c := u⁻¹ * (g⁻¹ * u * g) with hc
    have hcN : c ∈ ψ.ker := comm_mem_ker hu hg
    set m' := u * (c * m * c⁻¹) * u⁻¹ with hm'
    have hcm : c * m * c⁻¹ ∈ ψ.ker := conj_mem_ker hm
    have hm'N : m' ∈ ψ.ker := conj_mem_ker hcm
    refine ⟨m', hm'N, ρ u y, hD.W_inv u y hy, ?_⟩
    have e1 : u * (g * m * g⁻¹) * u⁻¹ = g * m' * g⁻¹ := by rw [hm', hc]; group
    have h1 : ρ u (ρ (g * m * g⁻¹) y - y) = ρ (g * m' * g⁻¹) (ρ u y) - ρ u y := by
      rw [← e1, alpha_conj']
    have h2 : ρ u (ρ m y - y) = ρ m' (ρ u y) - ρ u y := by
      rw [hm', alpha_conj', hD.alpha_conj_N hcN hm hy]
    rw [map_sub, h1, h2]
  have hXinv : ∀ u : Γ, (ψ u).2 = 1 → ∀ x ∈ X, ρ u x ∈ X := by
    intro u hu x hx
    have hle : X ≤ X.comap (ρ u).toLinearMap.toAddMonoidHom :=
      (AddSubgroup.closure_le _).mpr fun y hy => AddSubgroup.subset_closure (hDinv u hu y hy)
    exact hle hx
  let F : Subgroup Γ :=
    { carrier := {e | ∀ x ∈ X, ρ e x = x}
      mul_mem' := fun {a b} ha hb x hx => by
        rw [map_mul, LinearEquiv.mul_apply, hb x hx, ha x hx]
      one_mem' := fun x _ => by rw [map_one]; rfl
      inv_mem' := fun {a} ha x hx => by
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha x hx]
          _ = x := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  have hmemF : ∀ e, e ∈ F ↔ ∀ x ∈ X, ρ e x = x := fun e => Iff.rfl
  have hNF : ψ.ker ≤ F := fun e he x hx => hD.NV e he x (hXfix hx).1
  have hconjF : ∀ u : Γ, (ψ u).2 = 1 → ∀ f ∈ F, u * f * u⁻¹ ∈ F := by
    intro u hu f hf x hx
    have hu' : (ψ u⁻¹).2 = 1 := by rw [map_inv, Prod.snd_inv, hu, inv_one]
    rw [rho_conj_apply, hf _ (hXinv _ hu' x hx), rho_rho_inv]
  let F₁ : Subgroup S := (F.map ψ).comap (MonoidHom.inl S S)
  haveI : F₁.Normal := ⟨fun s hs t => by
    obtain ⟨f, hf, hfs⟩ := hs
    obtain ⟨u, hu⟩ := hD.surj (t, 1)
    refine ⟨u * f * u⁻¹, hconjF u (by rw [hu]) f hf, ?_⟩
    rw [map_mul, map_mul, map_inv, hu, hfs]
    simp⟩
  have hF₁ : F₁ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal F₁ with h | h
    · exfalso
      obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP.U₁'_ne
      have h1 : ((s, 1) : S × S) ∈ LA.map ψ := by rw [hP.prodA]; exact ⟨hs, Subgroup.one_mem _⟩
      obtain ⟨e, he, hes⟩ := h1
      have heF : e ∈ F := fun x hx => (hXfix hx).2 e ⟨he, by rw [hes]⟩
      have : (s : S) ∈ F₁ := ⟨e, heF, hes⟩
      rw [h, Subgroup.mem_bot] at this
      exact hs1 (Subtype.ext this)
    · exact h
  have hR₀F : ∀ e : Γ, (ψ e).2 = 1 → e ∈ F := by
    intro e he
    have h1 : (ψ e).1 ∈ F₁ := hF₁ ▸ Subgroup.mem_top _
    obtain ⟨f, hf, hfe⟩ := h1
    have hfe' : ψ f = ψ e := by
      rw [show ψ e = ((ψ e).1, 1) from Prod.ext rfl he]
      exact hfe
    have hk : f⁻¹ * e ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfe', inv_mul_cancel]
    rw [show e = f * (f⁻¹ * e) by group]
    exact F.mul_mem hf (hNF hk)
  have hx : (ρ (g * n * g⁻¹) w - w) - (ρ n w - w) ∈ X :=
    AddSubgroup.subset_closure ⟨n, hn, w, hw, rfl⟩
  have hzero := hD.R₀V _ (hXfix hx).1 fun e he => hR₀F e he _ hx
  exact sub_eq_zero.mp hzero

theorem alpha_second [IsSimpleGroup S] (hD : AlphaData ρ Vt Wt ψ) {LB LA : Subgroup Γ}
    {U₁ U₂ U₁' U₂' : Subgroup S} (hP : AlphaPair ρ ψ LB LA U₁ U₂ U₁' U₂') {g : Γ}
    (hg : (ψ g).1 = 1) {n : Γ} (hn : n ∈ ψ.ker) {w : E} (hw : w ∈ Wt) :
    ρ (g * n * g⁻¹) w - w = ρ n w - w := by
  classical
  let K₂ : Subgroup Γ :=
    { carrier := {k | ∀ m ∈ ψ.ker, ∀ y ∈ Wt, ρ (k * m * k⁻¹) y - y = ρ m y - y}
      mul_mem' := fun {a b} ha hb m hm y hy => by
        rw [show a * b * m * (a * b)⁻¹ = a * (b * m * b⁻¹) * a⁻¹ by group,
          ha _ (conj_mem_ker hm) y hy, hb m hm y hy]
      one_mem' := fun m _ y _ => by rw [one_mul, inv_one, mul_one]
      inv_mem' := fun {a} ha m hm y hy => by
        have h1 := ha (a⁻¹ * m * a⁻¹⁻¹) (conj_mem_ker hm) y hy
        rw [show a * (a⁻¹ * m * a⁻¹⁻¹) * a⁻¹ = m by group] at h1
        exact h1.symm }
  have hmemK : ∀ k, k ∈ K₂ ↔ ∀ m ∈ ψ.ker, ∀ y ∈ Wt, ρ (k * m * k⁻¹) y - y = ρ m y - y :=
    fun k => Iff.rfl
  haveI hK₂n : K₂.Normal := ⟨fun k hk γ m hm y hy => by
    rw [show γ * k * γ⁻¹ * m * (γ * k * γ⁻¹)⁻¹ = γ * (k * (γ⁻¹ * m * γ⁻¹⁻¹) * k⁻¹) * γ⁻¹ by
        group, alpha_conj, hk _ (conj_mem_ker hm) _ (hD.W_inv _ y hy), ← alpha_conj,
      show γ * (γ⁻¹ * m * γ⁻¹⁻¹) * γ⁻¹ = m by group]⟩
  have hNK : ψ.ker ≤ K₂ := fun k hk m hm y hy => hD.alpha_conj_N hk hm hy
  obtain ⟨⟨s₂, hs₂⟩, hs₂1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP.U₂_ne
  have h1 : ((1, s₂) : S × S) ∈ LB.map ψ := by rw [hP.prodB]; exact ⟨Subgroup.one_mem _, hs₂⟩
  obtain ⟨g₁, hg₁L, hg₁⟩ := h1
  have hg₁K : g₁ ∈ K₂ := fun m hm y hy => hD.alpha_good hP hg₁L (by rw [hg₁]) hm hy
  let K₂' : Subgroup S := (K₂.map ψ).comap (MonoidHom.inr S S)
  haveI : K₂'.Normal := ⟨fun s hs t => by
    obtain ⟨k, hk, hks⟩ := hs
    obtain ⟨u, hu⟩ := hD.surj (1, t)
    refine ⟨u * k * u⁻¹, hK₂n.conj_mem k hk u, ?_⟩
    rw [map_mul, map_mul, map_inv, hu, hks]
    simp⟩
  have hK₂' : K₂' = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K₂' with h | h
    · exfalso
      have : (s₂ : S) ∈ K₂' := ⟨g₁, hg₁K, hg₁⟩
      rw [h, Subgroup.mem_bot] at this
      exact hs₂1 (Subtype.ext this)
    · exact h
  have hgK : g ∈ K₂ := by
    have h1 : (ψ g).2 ∈ K₂' := hK₂' ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkg⟩ := h1
    have hkg' : ψ k = ψ g := by
      rw [show ψ g = (1, (ψ g).2) from Prod.ext hg rfl]
      exact hkg
    have hk' : k⁻¹ * g ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkg', inv_mul_cancel]
    rw [show g = k * (k⁻¹ * g) by group]
    exact K₂.mul_mem hk (hNK hk')
  exact hgK n hn w hw

end AlphaData

theorem eq_one_of_conj_eq_mul {h x k : Γ} (hodd : Odd (orderOf h)) (hconj : h * x * h⁻¹ = k * x)
    (hk : h * k * h⁻¹ = k) {m : ℕ} (hkm : k ^ (2 ^ m) = 1) : k = 1 := by
  have hpow : ∀ j : ℕ, h ^ j * x * (h ^ j)⁻¹ = k ^ j * x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hkj : h * k ^ j * h⁻¹ = k ^ j := by
        rw [← conj_pow, hk]
      calc h ^ (j + 1) * x * (h ^ (j + 1))⁻¹ = h * (h ^ j * x * (h ^ j)⁻¹) * h⁻¹ := by
            rw [pow_succ']; group
        _ = h * k ^ j * h⁻¹ * (h * x * h⁻¹) := by rw [ih]; group
        _ = k ^ (j + 1) * x := by rw [hkj, hconj, pow_succ]; group
  have h1 := hpow (orderOf h)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hk1 : k ^ orderOf h = 1 := by
    have := congrArg (· * x⁻¹) h1
    simpa using this.symm
  have hd1 : orderOf k ∣ orderOf h := orderOf_dvd_of_pow_eq_one hk1
  have hd2 : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hkm
  have hcop : Nat.Coprime (2 ^ m) (orderOf h) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd2 hd1))

end CFSG.RankThree.GF2n.Stroth80.Split92
