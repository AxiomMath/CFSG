module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs2
public import CFSG.Quasithin.EmptyFaithful.S153E56P1

public section

namespace CFSG.Quasithin

namespace S153E56p

open scoped commutatorElement

section Pair

variable {G : Type} [Group G]

structure ExtraPair (P Z₀ : Subgroup G) : Prop where
  card_Z : Nat.card Z₀ = 2
  Z_le : Z₀ ≤ P
  central : ∀ z ∈ Z₀, ∀ u ∈ P, z * u = u * z
  comm_mem : ∀ u ∈ P, ∀ v ∈ P, ⁅u, v⁆ ∈ Z₀
  sq_mem : ∀ u ∈ P, u * u ∈ Z₀
  rad : ∀ u ∈ P, (∀ v ∈ P, ⁅u, v⁆ = 1) → u ∈ Z₀

variable {P Z₀ : Subgroup G}

theorem card_conjSubgroup' (A : Subgroup G) (g : G) : Nat.card (conjSubgroup A g) = Nat.card A := by
  unfold conjSubgroup
  exact Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective

theorem conj_commutator (g u v : G) : g * ⁅u, v⁆ * g⁻¹ = ⁅g * u * g⁻¹, g * v * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem ExtraPair.conj (h : ExtraPair P Z₀) (g : G) :
    ExtraPair (conjSubgroup P g) (conjSubgroup Z₀ g) where
  card_Z := by rw [card_conjSubgroup', h.card_Z]
  Z_le := Subgroup.map_mono h.Z_le
  central := fun z hz u hu => by
    rw [mem_conjSubgroup_iff] at hz hu
    have := h.central _ hz _ hu
    have e : g * (z * u) * g⁻¹ = g * (u * z) * g⁻¹ := by
      calc g * (z * u) * g⁻¹ = (g * z * g⁻¹) * (g * u * g⁻¹) := by group
        _ = (g * u * g⁻¹) * (g * z * g⁻¹) := this
        _ = g * (u * z) * g⁻¹ := by group
    simpa using e
  comm_mem := fun u hu v hv => by
    rw [mem_conjSubgroup_iff] at hu hv ⊢
    rw [conj_commutator]
    exact h.comm_mem _ hu _ hv
  sq_mem := fun u hu => by
    rw [mem_conjSubgroup_iff] at hu ⊢
    have := h.sq_mem _ hu
    have e : g * (u * u) * g⁻¹ = (g * u * g⁻¹) * (g * u * g⁻¹) := by group
    rwa [e]
  rad := fun u hu hr => by
    rw [mem_conjSubgroup_iff] at hu ⊢
    refine h.rad _ hu fun v hv => ?_
    have hv' : g⁻¹ * v * g ∈ conjSubgroup P g := by
      rw [mem_conjSubgroup_iff]
      have e : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
      rw [e]
      exact hv
    have h1 := hr _ hv'
    have h2 := conj_commutator g u (g⁻¹ * v * g)
    rw [h1] at h2
    have e : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
    rw [e] at h2
    simpa using h2.symm

namespace ExtraPair

theorem sq_Z (h : ExtraPair P Z₀) {z : G} (hz : z ∈ Z₀) : z * z = 1 := by
  have := pow_card_eq_one' (G := ↥Z₀) (x := ⟨z, hz⟩)
  rw [h.card_Z] at this
  have := congrArg Subtype.val this
  simpa [pow_two] using this

theorem eq_of_ne_one (h : ExtraPair P Z₀) {x y : G} (hx : x ∈ Z₀) (hy : y ∈ Z₀) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : x = y := by
  obtain ⟨y₀, -, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥Z₀)).mp h.card_Z
  have h1 : (⟨x, hx⟩ : ↥Z₀) = y₀ := hu _ (fun e => hx1 (congrArg Subtype.val e))
  have h2 : (⟨y, hy⟩ : ↥Z₀) = y₀ := hu _ (fun e => hy1 (congrArg Subtype.val e))
  exact congrArg Subtype.val (h1.trans h2.symm)

open scoped Classical in
theorem ite_mul (h : ExtraPair P Z₀) {x y : G} (hx : x ∈ Z₀) (hy : y ∈ Z₀) :
    (if x * y = 1 then (0 : ZMod 2) else 1) = (if x = 1 then 0 else 1) + (if y = 1 then 0 else 1) := by
  by_cases hx1 : x = 1
  · simp [hx1]
  by_cases hy1 : y = 1
  · simp [hy1]
  have hxy : x = y := h.eq_of_ne_one hx hy hx1 hy1
  subst hxy
  have h1 : x * x = 1 := h.sq_Z hx
  simp only [h1, hx1, ite_true, ite_false]
  decide

end ExtraPair

theorem comm153_eq_zero_iff {u v : G} : comm153 u v = 0 ↔ ⁅u, v⁆ = 1 := by
  unfold comm153
  split_ifs with h <;> simp [h]

theorem comm153_eq_one_iff {u v : G} : comm153 u v = 1 ↔ ⁅u, v⁆ ≠ 1 := by
  unfold comm153
  split_ifs with h <;> simp [h]

theorem comm153_symm (u v : G) : comm153 u v = comm153 v u := by
  unfold comm153
  rw [← commutatorElement_inv v u, inv_eq_one]

theorem comm153_one_left (v : G) : comm153 1 v = 0 :=
  comm153_eq_zero_iff.2 (by simp [commutatorElement_def])

namespace ExtraPair

theorem comm_mul_left (h : ExtraPair P Z₀) {u u' v : G} (hu : u ∈ P) (hu' : u' ∈ P) (hv : v ∈ P) :
    ⁅u * u', v⁆ = ⁅u', v⁆ * ⁅u, v⁆ := by
  have hc : ⁅u', v⁆ ∈ Z₀ := h.comm_mem _ hu' _ hv
  have hcen := h.central _ hc _ hu
  have e : ⁅u * u', v⁆ = u * ⁅u', v⁆ * u⁻¹ * ⁅u, v⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, ← hcen]
  group

theorem comm_mul_right (h : ExtraPair P Z₀) {u v v' : G} (hu : u ∈ P) (hv : v ∈ P) (hv' : v' ∈ P) :
    ⁅u, v * v'⁆ = ⁅u, v⁆ * ⁅u, v'⁆ := by
  have hc : ⁅u, v'⁆ ∈ Z₀ := h.comm_mem _ hu _ hv'
  have hcen := h.central _ hc _ hv
  have e : ⁅u, v * v'⁆ = ⁅u, v⁆ * (v * ⁅u, v'⁆ * v⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, ← hcen]
  group

theorem comm153_add_left (h : ExtraPair P Z₀) {u u' v : G} (hu : u ∈ P) (hu' : u' ∈ P) (hv : v ∈ P) :
    comm153 (u * u') v = comm153 u v + comm153 u' v := by
  classical
  have hc : ⁅u', v⁆ ∈ Z₀ := h.comm_mem _ hu' _ hv
  have hc' : ⁅u, v⁆ ∈ Z₀ := h.comm_mem _ hu _ hv
  unfold comm153
  rw [h.comm_mul_left hu hu' hv, h.ite_mul hc hc', add_comm]

theorem comm153_add_right (h : ExtraPair P Z₀) {u v v' : G} (hu : u ∈ P) (hv : v ∈ P) (hv' : v' ∈ P) :
    comm153 u (v * v') = comm153 u v + comm153 u v' := by
  classical
  have hc : ⁅u, v'⁆ ∈ Z₀ := h.comm_mem _ hu _ hv'
  have hc' : ⁅u, v⁆ ∈ Z₀ := h.comm_mem _ hu _ hv
  unfold comm153
  rw [h.comm_mul_right hu hv hv', h.ite_mul hc' hc]

theorem comm153_Z_left (h : ExtraPair P Z₀) {z v : G} (hz : z ∈ Z₀) (hv : v ∈ P) : comm153 z v = 0 :=
  comm153_eq_zero_iff.2 (by
    have := h.central _ hz _ hv
    simp [commutatorElement_def, this])

theorem comm153_mul_Z_left (h : ExtraPair P Z₀) {u z v : G} (hu : u ∈ P) (hz : z ∈ Z₀) (hv : v ∈ P) :
    comm153 (u * z) v = comm153 u v := by
  rw [h.comm153_add_left hu (h.Z_le hz) hv, h.comm153_Z_left hz hv, add_zero]

end ExtraPair

theorem prop_aux {C : Set G} (hC : ∀ w ∈ C, ∀ w' ∈ C, w * w' ∈ C) {f₁ f₂ : G → ZMod 2}
    (h₁ : ∀ w ∈ C, ∀ w' ∈ C, f₁ (w * w') = f₁ w + f₁ w')
    (h₂ : ∀ w ∈ C, ∀ w' ∈ C, f₂ (w * w') = f₂ w + f₂ w')
    (hker : ∀ w ∈ C, f₁ w = 0 → f₂ w = 0) : ∃ c : ZMod 2, ∀ w ∈ C, f₂ w = c * f₁ w := by
  by_cases hz : ∀ w ∈ C, f₁ w = 0
  · exact ⟨0, fun w hw => by rw [hker w hw (hz w hw), zero_mul]⟩
  · push Not at hz
    obtain ⟨w₀, hw₀, hne⟩ := hz
    have h1 : f₁ w₀ = 1 := S153E56p.zmod_two_eq_one hne
    refine ⟨f₂ w₀, fun w hw => ?_⟩
    rcases S153E56p.zmod_two_cases (f₁ w) with h0 | h0
    · rw [h0, mul_zero]
      exact hker w hw h0
    · have h3 : f₁ (w * w₀) = 0 := by rw [h₁ w hw w₀ hw₀, h0, h1]; decide
      have h4 := hker _ (hC w hw w₀ hw₀) h3
      rw [h₂ w hw w₀ hw₀] at h4
      rw [h0, mul_one]
      have : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact this _ _ h4

section Fin

variable [Finite G]

omit [Finite G] in
theorem ExtraPair.dc_aux (h : ExtraPair P Z₀) : ∀ S : Finset G, (↑S ⊆ (P : Set G)) → ∀ x ∈ P,
    (∀ w ∈ P, (∀ b ∈ S, ⁅b, w⁆ = 1) → ⁅x, w⁆ = 1) →
      ∃ b ∈ Subgroup.closure (S : Set G), x * b⁻¹ ∈ Z₀ := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ x hx hxw
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    have : x ∈ Z₀ := h.rad x hx (fun w hw => hxw w hw (by simp))
    simpa using this
  | insert b S hb ih =>
    intro hS x hx hxw
    have hbP : b ∈ P := hS (by simp)
    have hSP : (↑S : Set G) ⊆ P := fun y hy => hS (by simp [hy])
    set C₁ : Set G := {w | w ∈ P ∧ ∀ b' ∈ S, ⁅b', w⁆ = 1} with hC₁
    have hC : ∀ w ∈ C₁, ∀ w' ∈ C₁, w * w' ∈ C₁ := by
      rintro w ⟨hwP, hw⟩ w' ⟨hw'P, hw'⟩
      refine ⟨P.mul_mem hwP hw'P, fun b' hb' => ?_⟩
      rw [h.comm_mul_right (hSP hb') hwP hw'P, hw b' hb', hw' b' hb', mul_one]
    have h₁ : ∀ w ∈ C₁, ∀ w' ∈ C₁, comm153 b (w * w') = comm153 b w + comm153 b w' :=
      fun w hw w' hw' => h.comm153_add_right hbP hw.1 hw'.1
    have h₂ : ∀ w ∈ C₁, ∀ w' ∈ C₁, comm153 x (w * w') = comm153 x w + comm153 x w' :=
      fun w hw w' hw' => h.comm153_add_right hx hw.1 hw'.1
    have hker : ∀ w ∈ C₁, comm153 b w = 0 → comm153 x w = 0 := by
      intro w hw h0
      have h1 : ⁅b, w⁆ = 1 := comm153_eq_zero_iff.1 h0
      refine comm153_eq_zero_iff.2 (hxw w hw.1 fun b' hb' => ?_)
      rcases Finset.mem_insert.1 hb' with rfl | hb'
      · exact h1
      · exact hw.2 b' hb'
    obtain ⟨c, hc⟩ := prop_aux hC h₁ h₂ hker
    have hsub : Subgroup.closure (↑S : Set G) ≤ Subgroup.closure (↑(insert b S) : Set G) :=
      Subgroup.closure_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    rcases S153E56p.zmod_two_cases c with rfl | rfl
    · have hxw' : ∀ w ∈ P, (∀ b' ∈ S, ⁅b', w⁆ = 1) → ⁅x, w⁆ = 1 := fun w hw hb' =>
        comm153_eq_zero_iff.1 (by rw [hc w ⟨hw, hb'⟩, zero_mul])
      obtain ⟨b₁, hb₁, hz⟩ := ih hSP x hx hxw'
      exact ⟨b₁, hsub hb₁, hz⟩
    · have hxb : x * b ∈ P := P.mul_mem hx hbP
      have hxw' : ∀ w ∈ P, (∀ b' ∈ S, ⁅b', w⁆ = 1) → ⁅x * b, w⁆ = 1 := by
        intro w hw hb'
        refine comm153_eq_zero_iff.1 ?_
        rw [h.comm153_add_left hx hbP hw, hc w ⟨hw, hb'⟩, one_mul]
        exact S153E56p.zmod_two_add_self _
      obtain ⟨b₁, hb₁, hz⟩ := ih hSP (x * b) hxb hxw'
      refine ⟨b₁ * b⁻¹, Subgroup.mul_mem _ (hsub hb₁)
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))), ?_⟩
      have e : x * (b₁ * b⁻¹)⁻¹ = x * b * b₁⁻¹ := by group
      rw [e]
      exact hz

theorem ExtraPair.dc (h : ExtraPair P Z₀) {B : Subgroup G} (hB : B ≤ P) {x : G} (hx : x ∈ P)
    (hxw : ∀ w ∈ P, (∀ b ∈ B, ⁅b, w⁆ = 1) → ⁅x, w⁆ = 1) : ∃ b ∈ B, x * b⁻¹ ∈ Z₀ := by
  classical
  have hfin : (B : Set G).Finite := Set.toFinite _
  obtain ⟨b, hb, hz⟩ := h.dc_aux hfin.toFinset
    (by intro y hy; exact hB (by simpa using hy)) x hx
    (fun w hw hb' => hxw w hw (fun b hb => hb' b (by simpa using hb)))
  rw [Set.Finite.coe_toFinset, Subgroup.closure_eq] at hb
  exact ⟨b, hb, hz⟩

theorem ExtraPair.rep (h : ExtraPair P Z₀) {A : Subgroup G} (hA : A ≤ P) {f : G → ZMod 2}
    (hadd : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a + f b) (hZ : ∀ a ∈ A, a ∈ Z₀ → f a = 0) :
    ∃ p ∈ P, ∀ a ∈ A, comm153 p a = f a := by
  classical
  have hf1 : f 1 = 0 := by
    have := hadd 1 A.one_mem 1 A.one_mem
    rw [mul_one] at this
    have h2 : f 1 + f 1 = f 1 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h2
  have hfinv : ∀ a ∈ A, f a⁻¹ = f a := by
    intro a ha
    have := hadd a ha a⁻¹ (A.inv_mem ha)
    rw [mul_inv_cancel, hf1] at this
    have h2 : ∀ x y : ZMod 2, 0 = x + y → y = x := by decide
    exact h2 _ _ this
  let B : Subgroup G :=
    { carrier := {a | a ∈ A ∧ f a = 0}
      one_mem' := ⟨A.one_mem, hf1⟩
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        rw [hadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [hfinv a ha.1, ha.2]⟩ }
  by_cases hfa : ∀ a ∈ A, f a = 0
  · refine ⟨1, P.one_mem, fun a ha => ?_⟩
    rw [hfa a ha, comm153_one_left]
  · push Not at hfa
    obtain ⟨a₁, ha₁, hne⟩ := hfa
    have hf1' : f a₁ = 1 := S153E56p.zmod_two_eq_one hne
    have hex : ∃ p ∈ P, (∀ b ∈ B, ⁅b, p⁆ = 1) ∧ ⁅a₁, p⁆ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨b, hbB, hz⟩ := h.dc (B := B) (fun b hb => hA hb.1) (hA ha₁)
        (fun w hw hBw => hcon w hw hBw)
      have hA' : a₁ * b⁻¹ ∈ A := A.mul_mem ha₁ (A.inv_mem hbB.1)
      have h0 := hZ _ hA' hz
      rw [hadd _ ha₁ _ (A.inv_mem hbB.1), hfinv _ hbB.1, hbB.2, hf1', add_zero] at h0
      exact one_ne_zero h0
    obtain ⟨p, hpP, hpB, hp1⟩ := hex
    refine ⟨p, hpP, fun a ha => ?_⟩
    rcases S153E56p.zmod_two_cases (f a) with h0 | h0
    · rw [h0, comm153_symm]
      exact comm153_eq_zero_iff.2 (hpB a ⟨ha, h0⟩)
    · have haB : a * a₁⁻¹ ∈ B := ⟨A.mul_mem ha (A.inv_mem ha₁), by
        rw [hadd _ ha _ (A.inv_mem ha₁), hfinv _ ha₁, h0, hf1']; decide⟩
      have e1 : comm153 p a = comm153 (a * a₁⁻¹ * a₁) p := by
        rw [inv_mul_cancel_right, comm153_symm]
      have e2 := h.comm153_add_left (P.mul_mem (hA ha) (P.inv_mem (hA ha₁))) (hA ha₁) hpP
      have e3 : comm153 (a * a₁⁻¹) p = 0 := comm153_eq_zero_iff.2 (hpB _ haB)
      have e4 : comm153 a₁ p = 1 := comm153_eq_one_iff.2 hp1
      rw [h0, e1, e2, e3, e4, zero_add]

end Fin

end Pair

end S153E56p

end CFSG.Quasithin
