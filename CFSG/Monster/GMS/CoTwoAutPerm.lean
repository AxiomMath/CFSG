module

public import CFSG.Monster.GMS.CoTwoAssembly
public import CFSG.Monster.GMS.CoTwoAutKer
public import CFSG.Sporadic.Co1.Module.CoTwoAutGraph

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open CFSG.Sporadic.Co1.Module.CoTwoAut
open CFSG.Sporadic.Co2Rank3 (co2Graph co2Aut card_co2Aut mem_co2Aut)

namespace CoTwoAutPerm

theorem perp_of_q₀_eq
    {y : Fin 24 → ZMod 2} (h : q₀ (v₂ + y) = q₀ y) : bil₀ y v₂ = 0 := by
  rw [q₀_add, q₀_v₂, zero_add] at h
  have h' : bil₀ v₂ y = 0 := by
    have : q₀ y + bil₀ v₂ y = q₀ y + 0 := by rw [add_zero]; exact h
    exact add_left_cancel this
  rw [bil₀_comm]
  exact h'

theorem cls_three_perp
    {ω : Fin 24 → ZMod 2} (hω : ω ∈ Pairs.cls 3) : bil₀ ω v₂ = 0 := by
  obtain ⟨h1, h2⟩ := mem_cls_three_iff.1 hω
  exact perp_of_q₀_eq (by
    rw [Leech.q₀_eq_zero_of_mem_co1Orbit_zero h1, Leech.q₀_eq_zero_of_mem_co1Orbit_zero h2])

theorem cls_one_perp
    {y : Fin 24 → ZMod 2} (hy : y ∈ Pairs.cls 1) : bil₀ y v₂ = 0 := by
  obtain ⟨h1, h2⟩ := mem_cls_one_iff.1 hy
  exact perp_of_q₀_eq (by
    rw [Leech.q₀_eq_zero_of_mem_co1Orbit_zero h1, Leech.q₀_eq_zero_of_mem_co1Orbit_two h2])

theorem Tadj_perp
    {u : Fin 24 → ZMod 2} (hu : u ∈ Tadj) : bil₀ u v₂ = 0 := by
  rcases hu with hu | hu
  · exact cls_one_perp hu
  · have h := cls_one_perp hu
    rw [Leech.bil₀_add_left, bil₀_self, zero_add] at h
    exact h

theorem v₂_add_v₂_add (u : Fin 24 → ZMod 2) : v₂ + (v₂ + u) = u := by
  rw [← add_assoc, vec_add_self, zero_add]

theorem Tadj_add_v₂ {u : Fin 24 → ZMod 2} : v₂ + u ∈ Tadj ↔ u ∈ Tadj := by
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · rw [v₂_add_v₂_add] at h
      exact Or.inl h
  · rintro (h | h)
    · exact Or.inr (by rw [v₂_add_v₂_add]; exact h)
    · exact Or.inl h

theorem Tadj_class {u u' : Fin 24 → ZMod 2} (h : u' = u ∨ u' = v₂ + u) :
    u' ∈ Tadj ↔ u ∈ Tadj := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact Tadj_add_v₂

theorem cls_smul {g : Co1} (hg : g ∈ co1Stab v₂) {j : ℕ} {y : Fin 24 → ZMod 2}
    (hy : y ∈ Pairs.cls j) : co1Act g y ∈ Pairs.cls j :=
  Pairs.cls_smul_mem (show g • v₂ = v₂ from hg) hy

theorem Tadj_smul {g : Co1} (hg : g ∈ co1Stab v₂) {u : Fin 24 → ZMod 2} (hu : u ∈ Tadj) :
    co1Act g u ∈ Tadj := by
  rcases hu with hu | hu
  · exact Or.inl (cls_smul hg hu)
  · refine Or.inr ?_
    have := cls_smul hg hu
    rwa [map_add, show co1Act g v₂ = v₂ from hg] at this

theorem Tadj_smul_iff {g : Co1} (hg : g ∈ co1Stab v₂) {u : Fin 24 → ZMod 2} :
    co1Act g u ∈ Tadj ↔ u ∈ Tadj := by
  refine ⟨fun h => ?_, Tadj_smul hg⟩
  have := Tadj_smul (inv_mem hg) h
  rwa [CoTwoModule.co1Act_inv_apply] at this

theorem cls_three_smul {g : Co1} (hg : g ∈ co1Stab v₂) {ω : Fin 24 → ZMod 2}
    (hω : ω ∈ Pairs.cls 3) : co1Act g ω ∈ Pairs.cls 3 := cls_smul hg hω

@[expose] def spanΩ : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  Submodule.span (ZMod 2) (Pairs.cls 3 ∪ {v₂})

theorem mem_spanΩ_of_cls {w : Fin 24 → ZMod 2} (hw : w ∈ Pairs.cls 3) : w ∈ spanΩ :=
  Submodule.subset_span (Or.inl hw)

theorem v₂_mem_spanΩ : v₂ ∈ spanΩ := Submodule.subset_span (Or.inr rfl)

theorem spanΩ_le {S : Submodule (ZMod 2) (Fin 24 → ZMod 2)} (h1 : ∀ w ∈ Pairs.cls 3, w ∈ S)
    (h2 : v₂ ∈ S) : spanΩ ≤ S := by
  refine Submodule.span_le.2 ?_
  rintro w (hw | hw)
  · exact h1 w hw
  · rw [Set.mem_singleton_iff] at hw
    subst hw
    exact h2

theorem perp_le_span
    (y : Fin 24 → ZMod 2) (hy : bil₀ y v₂ = 0) : y ∈ spanΩ := by
  have hYperp : ∀ z ∈ spanΩ, bil₀ z v₂ = 0 := by
    have : spanΩ ≤ CoTwoModule.perpSpace v₂ :=
      spanΩ_le (fun z hz => CoTwoModule.mem_perpSpace.2 (cls_three_perp hz))
        (CoTwoModule.mem_perpSpace.2 (bil₀_self _))
    exact fun z hz => CoTwoModule.mem_perpSpace.1 (this hz)
  have hinv : ∀ A ∈ co1Stab v₂, ∀ z ∈ spanΩ, co1Act A z ∈ spanΩ := by
    intro A hA z hz
    have h1 : spanΩ ≤ spanΩ.comap (co1Act A) := by
      refine spanΩ_le ?_ ?_
      · intro w hw
        exact Submodule.mem_comap.2 (mem_spanΩ_of_cls (cls_three_smul hA hw))
      · refine Submodule.mem_comap.2 ?_
        rw [show co1Act A v₂ = v₂ from hA]
        exact v₂_mem_spanΩ
    exact Submodule.mem_comap.1 (h1 hz)
  rcases co2McLFacts.irred_co2 v₂ CoTwoModule.v₂_mem_co1Orbit spanΩ v₂_mem_spanΩ hYperp hinv with
    h | h
  · exfalso
    have hω : vtx 0 ∈ spanΩ := mem_spanΩ_of_cls (vtx_mem_cls_three 0)
    rw [h, Submodule.mem_span_singleton] at hω
    obtain ⟨c, hc⟩ := hω
    obtain ⟨h1, h2⟩ := mem_cls_three_iff.1 (vtx_mem_cls_three 0)
    have h1' : vtx 0 ∈ co1Orbit 0 := by
      rw [Pairs.co1Orbit_zero]
      exact h1
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul] at hc
      exact Leech.ne_zero_of_mem_co1Orbit h1' hc.symm
    · rw [one_smul] at hc
      have h0 : v₂ + vtx 0 = 0 := by rw [hc, vec_add_self]
      rw [h0] at h2
      have h2' : (0 : Fin 24 → ZMod 2) ∈ co1Orbit 0 := by
        rw [Pairs.co1Orbit_zero]
        exact h2
      exact Leech.ne_zero_of_mem_co1Orbit h2' rfl
  · exact h y hy

theorem perp_forall_of_cls
    {F : (Fin 24 → ZMod 2) → (Fin 24 → ZMod 2)}
    (hadd : ∀ a b, bil₀ a v₂ = 0 → bil₀ b v₂ = 0 → F (a + b) = F a + F b)
    (hcls : ∀ ω ∈ Pairs.cls 3, F ω = 0 ∨ F ω = v₂) (hv : F v₂ = 0 ∨ F v₂ = v₂) :
    ∀ w, bil₀ w v₂ = 0 → F w = 0 ∨ F w = v₂ := by
  have h00 : bil₀ (0 : Fin 24 → ZMod 2) v₂ = 0 := CoTwoModule.bil₀_zero_left v₂
  have hF0 : F 0 = 0 := by
    have h := hadd 0 0 h00 h00
    rw [add_zero] at h
    exact (add_eq_left.1 h.symm)
  let Y : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
    { carrier := {w | bil₀ w v₂ = 0 ∧ (F w = 0 ∨ F w = v₂)}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, ?_⟩
        · rw [Leech.bil₀_add_left, ha1, hb1, add_zero]
        · rw [hadd a b ha1 hb1]
          exact CoTwoAutKer.add01 ha2 hb2
      zero_mem' := ⟨h00, Or.inl hF0⟩
      smul_mem' := by
        intro c w hw
        rcases zmod2_cases c with rfl | rfl
        · rw [zero_smul]
          exact ⟨h00, Or.inl hF0⟩
        · rw [one_smul]
          exact hw }
  intro w hw
  have hle : spanΩ ≤ Y :=
    spanΩ_le (fun z hz => ⟨cls_three_perp hz, hcls z hz⟩) ⟨bil₀_self _, hv⟩
  exact (hle (perp_le_span w hw)).2

theorem eq_one_of_trivial_on_cls
    {g : Co1} (hg : g ∈ co1Stab v₂)
    (h : ∀ ω ∈ Pairs.cls 3, co1Act g ω + ω = 0 ∨ co1Act g ω + ω = v₂) : g = 1 := by
  have hperp := perp_forall_of_cls (F := fun w => co1Act g w + w)
    (fun a b _ _ => by
      show co1Act g (a + b) + (a + b) = (co1Act g a + a) + (co1Act g b + b)
      rw [map_add, add_add_add_comm]) h
    (Or.inl (by
      show co1Act g v₂ + v₂ = 0
      rw [show co1Act g v₂ = v₂ from hg]
      exact vec_add_self v₂))
  exact CoTwoAutKer.eq_one_of_trivial_on_perp CoTwoModule.v₂_mem_co1Orbit hg hperp

theorem vtx_add_mem01 {ω : Fin 24 → ZMod 2} {a i : Fin 2300}
    (ha : ω = vtx a ∨ ω = v₂ + vtx a) (hi : ω = vtx i ∨ ω = v₂ + vtx i) :
    vtx a + vtx i = 0 ∨ vtx a + vtx i = v₂ := by
  rcases ha with ha | ha <;> rcases hi with hi | hi
  · left
    rw [← ha, ← hi, vec_add_self]
  · right
    rw [← ha, hi, add_assoc, vec_add_self, add_zero]
  · right
    rw [← hi, ha, add_comm (vtx a), add_assoc, vec_add_self, add_zero]
  · left
    have h : v₂ + vtx a = v₂ + vtx i := ha.symm.trans hi
    rw [add_left_cancel h, vec_add_self]

@[expose, irreducible] noncomputable def idx (ω : Fin 24 → ZMod 2) : Fin 2300 :=
  if h : ∃ i : Fin 2300, ω = vtx i ∨ ω = v₂ + vtx i then h.choose else 0

theorem idx_spec
    {ω : Fin 24 → ZMod 2} (hω : ω ∈ Pairs.cls 3) :
    ω = vtx (idx ω) ∨ ω = v₂ + vtx (idx ω) := by
  have h := exists_vtx_of_mem_cls_three hω
  unfold idx
  split_ifs with hh
  · exact hh.choose_spec
  · exact absurd h hh

theorem idx_eq
    {ω : Fin 24 → ZMod 2} {i : Fin 2300} (h : ω = vtx i ∨ ω = v₂ + vtx i) :
    idx ω = i := by
  have hω : ω ∈ Pairs.cls 3 := by
    rcases h with rfl | rfl
    · exact vtx_mem_cls_three i
    · exact add_v₂_mem_cls_three (vtx_mem_cls_three i)
  by_contra hne
  rcases vtx_add_mem01 (idx_spec hω) h with h0 | h2
  · exact (vtx_add_ne hne).1 h0
  · exact (vtx_add_ne hne).2 h2

theorem idx_add_v₂
    {ω : Fin 24 → ZMod 2} (hω : ω ∈ Pairs.cls 3) : idx (v₂ + ω) = idx ω := by
  generalize hi : idx ω = i
  have h := idx_spec hω
  rw [hi] at h
  rcases h with h | h
  · exact idx_eq (Or.inr (by rw [h]))
  · exact idx_eq (Or.inl (by rw [h, v₂_add_v₂_add]))

@[expose] noncomputable def kperm (g : Co1) (i : Fin 2300) : Fin 2300 := idx (co1Act g (vtx i))

theorem kperm_spec
    {g : Co1} (hg : g ∈ co1Stab v₂) (i : Fin 2300) :
    co1Act g (vtx i) = vtx (kperm g i) ∨ co1Act g (vtx i) = v₂ + vtx (kperm g i) :=
  idx_spec (cls_three_smul hg (vtx_mem_cls_three i))

theorem kperm_mul
    {g h : Co1} (hg : g ∈ co1Stab v₂) (hh : h ∈ co1Stab v₂) (i : Fin 2300) :
    kperm (g * h) i = kperm g (kperm h i) := by
  show idx (co1Act (g * h) (vtx i)) = idx (co1Act g (vtx (kperm h i)))
  rw [CoTwoModule.co1Act_mul_apply]
  rcases kperm_spec hh i with e | e
  · rw [e]
  · rw [e, map_add, show co1Act g v₂ = v₂ from hg]
    exact idx_add_v₂ (cls_three_smul hg (vtx_mem_cls_three _))

theorem kperm_one
    (i : Fin 2300) : kperm 1 i = i := by
  show idx (co1Act 1 (vtx i)) = i
  rw [map_one, Module.End.one_apply]
  exact idx_eq (Or.inl rfl)

theorem kperm_inv_left
    {g : Co1} (hg : g ∈ co1Stab v₂) (i : Fin 2300) :
    kperm g⁻¹ (kperm g i) = i := by
  rw [← kperm_mul (inv_mem hg) hg, inv_mul_cancel]
  exact kperm_one i

theorem kperm_inv_right
    {g : Co1} (hg : g ∈ co1Stab v₂) (i : Fin 2300) :
    kperm g (kperm g⁻¹ i) = i := by
  rw [← kperm_mul hg (inv_mem hg), mul_inv_cancel]
  exact kperm_one i

@[expose] noncomputable def kPerm
    (g : ↥(co1Stab v₂)) : Equiv.Perm (Fin 2300) where
  toFun := kperm g
  invFun := kperm (g : Co1)⁻¹
  left_inv := kperm_inv_left g.2
  right_inv := kperm_inv_right g.2

theorem kPerm_apply
    (g : ↥(co1Stab v₂)) (i : Fin 2300) : kPerm g i = kperm g i := rfl

theorem kPerm_mul
    (g h : ↥(co1Stab v₂)) : kPerm (g * h) = kPerm g * kPerm h :=
  Equiv.ext fun i => by
    rw [Equiv.Perm.mul_apply, kPerm_apply, kPerm_apply, kPerm_apply]
    exact kperm_mul g.2 h.2 i

@[expose] noncomputable def kHom :
    ↥(co1Stab v₂) →* Equiv.Perm (Fin 2300) where
  toFun := kPerm
  map_one' := Equiv.ext fun i => kperm_one i
  map_mul' := kPerm_mul

theorem kHom_apply
    (g : ↥(co1Stab v₂)) (i : Fin 2300) : kHom g i = kperm g i := rfl

theorem add_class_aux {A B a b : Fin 24 → ZMod 2} (hA : A = a ∨ A = v₂ + a)
    (hB : B = b ∨ B = v₂ + b) : A + B = a + b ∨ A + B = v₂ + (a + b) := by
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · left; rfl
  · right; rw [add_left_comm]
  · right; rw [add_assoc]
  · left; rw [add_add_add_comm, vec_add_self, zero_add]

theorem kHom_adj
    (g : ↥(co1Stab v₂)) (x y : Fin 2300) :
    co2Graph.Adj (kHom g x) (kHom g y) ↔ co2Graph.Adj x y := by
  have h := add_class_aux (kperm_spec g.2 x) (kperm_spec g.2 y)
  rw [adj_iff_vtx_add_mem, adj_iff_vtx_add_mem, kHom_apply, kHom_apply, ← Tadj_class h,
    ← map_add, Tadj_smul_iff g.2]

theorem kHom_mem_co2Aut
    (g : ↥(co1Stab v₂)) : kHom g ∈ co2Aut :=
  mem_co2Aut.2 fun x y => kHom_adj g x y

theorem kHom_injective :
    Function.Injective kHom := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hk : ∀ i, kperm g i = i := fun i => by
    have := congrArg (fun σ : Equiv.Perm (Fin 2300) => σ i) hg
    simpa [kHom_apply] using this
  have hvtx : ∀ i, co1Act g (vtx i) + vtx i = 0 ∨ co1Act g (vtx i) + vtx i = v₂ := by
    intro i
    rcases kperm_spec g.2 i with e | e
    · rw [hk i] at e
      left
      rw [e, vec_add_self]
    · rw [hk i] at e
      right
      rw [e, add_assoc, vec_add_self, add_zero]
  have hcls : ∀ ω ∈ Pairs.cls 3, co1Act g ω + ω = 0 ∨ co1Act g ω + ω = v₂ := by
    intro ω hω
    obtain ⟨i, hi | hi⟩ := exists_vtx_of_mem_cls_three hω
    · rw [hi]
      exact hvtx i
    · rw [hi, map_add, show co1Act g v₂ = v₂ from g.2, add_add_add_comm, vec_add_self, zero_add]
      exact hvtx i
  exact Subtype.ext (eq_one_of_trivial_on_cls g.2 hcls)

theorem exists_kHom_eq
    {σ : Equiv.Perm (Fin 2300)} (hσ : σ ∈ co2Aut) :
    ∃ g : ↥(co1Stab v₂), kHom g = σ := by
  have hle : kHom.range ≤ co2Aut := by
    rintro _ ⟨g, rfl⟩
    exact kHom_mem_co2Aut g
  have hcard : Nat.card co2Aut ≤ Nat.card kHom.range := by
    rw [card_co2Aut, Nat.card_congr (MonoidHom.ofInjective kHom_injective).toEquiv.symm]
    exact (CFSG.Sporadic.Co1.Module.CoTwo.card_kc).ge
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq] at hσ
  exact hσ

end CoTwoAutPerm

end CFSG.Monster.GMS
