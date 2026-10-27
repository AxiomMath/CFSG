module

public import CFSG.Quasithin.Background.S1567Z6

public section

namespace CFSG.Quasithin.S153N.Bb

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

abbrev Qt (V E : Subgroup G) : Type := ↥V ⧸ E.subgroupOf V

@[expose, instance_reducible] def cgQt (V E : Subgroup G) [IsMulCommutative ↥V] :
    CommGroup (Qt V E) :=
  { (inferInstance : Group (Qt V E)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm' a b] }

@[expose] def mkQ (V E : Subgroup G) [IsMulCommutative ↥V] : ↥V →* Qt V E :=
  QuotientGroup.mk' (E.subgroupOf V)

theorem mkQ_apply (V E : Subgroup G) [IsMulCommutative ↥V] (v : ↥V) :
    mkQ V E v = (QuotientGroup.mk v : Qt V E) := rfl

theorem mkQ_surjective (V E : Subgroup G) [IsMulCommutative ↥V] : Function.Surjective (mkQ V E) :=
  QuotientGroup.mk'_surjective _

theorem mkQ_eq_one_iff (V E : Subgroup G) [IsMulCommutative ↥V] (v : ↥V) :
    mkQ V E v = 1 ↔ (v : G) ∈ E := by
  rw [mkQ_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mkQ_eq_iff (V E : Subgroup G) [IsMulCommutative ↥V] (a b : ↥V) :
    mkQ V E a = mkQ V E b ↔ (a : G)⁻¹ * b ∈ E := by
  rw [mkQ_apply, mkQ_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

section Count

variable (V E H : Subgroup G) [IsMulCommutative ↥V]

@[expose] def projOn (hHV : H ≤ V) : ↥H →* Qt V E := (mkQ V E).comp (Subgroup.inclusion hHV)

variable {V E H}

theorem projOn_apply (hHV : H ≤ V) (h : ↥H) : projOn V E H hHV h = mkQ V E ⟨h, hHV h.2⟩ := rfl

theorem projOn_ker (hHV : H ≤ V) : (projOn V E H hHV).ker = E.subgroupOf H := by
  ext h
  rw [MonoidHom.mem_ker, projOn_apply, mkQ_eq_one_iff, Subgroup.mem_subgroupOf]

theorem card_eq_mul_range (hHV : H ≤ V) (hEH : E ≤ H) :
    Nat.card H = Nat.card E * Nat.card (projOn V E H hHV).range := by
  have h1 := Subgroup.card_mul_index (projOn V E H hHV).ker
  rw [Subgroup.index_ker, projOn_ker hHV] at h1
  have h2 : Nat.card ↥(E.subgroupOf H) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem card_Qt (hEV : E ≤ V) : Nat.card V = Nat.card E * Nat.card (Qt V E) := by
  have h := card_eq_mul_range (le_refl V) hEV
  have hsurj : Function.Surjective (projOn V E V le_rfl) := by
    intro u
    obtain ⟨v, rfl⟩ := mkQ_surjective V E u
    exact ⟨⟨v.1, v.2⟩, rfl⟩
  have : (projOn V E V le_rfl).range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  rw [this, Subgroup.card_top] at h
  exact h

variable (V E H) in
@[expose] def imgQ (hHV : H ≤ V) : Subgroup (Qt V E) := (projOn V E H hHV).range

theorem mem_imgQ (hHV : H ≤ V) {u : Qt V E} :
    u ∈ imgQ V E H hHV ↔ ∃ (h : G) (hh : h ∈ H), u = mkQ V E ⟨h, hHV hh⟩ := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h.1, h.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem mkQ_mem_imgQ (hHV : H ≤ V) {h : G} (hh : h ∈ H) :
    mkQ V E ⟨h, hHV hh⟩ ∈ imgQ V E H hHV := (mem_imgQ hHV).2 ⟨h, hh, rfl⟩

end Count

section Action

variable (V E : Subgroup G) [IsMulCommutative ↥V]

@[expose] noncomputable def actN
    (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    ↥(Subgroup.normalizer (E : Set G)) →* MulAut (Qt V E) :=
  (S1567.barHom (V := V) (E := E)).comp (Subgroup.inclusion (le_inf hN le_rfl))

variable {V E}

theorem actN_mk (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))
    (g : ↥(Subgroup.normalizer (E : Set G))) (v : ↥V) :
    actN V E hN g (mkQ V E v) =
      mkQ V E ⟨g * (v : G) * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hN g.2) v).mp v.2⟩ :=
  S1567.barAut_mk (hN g.2) g.2 v

theorem actN_eq_one_of (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))
    (g : ↥(Subgroup.normalizer (E : Set G))) (h : ∀ v ∈ V, (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈ E) :
    actN V E hN g = 1 :=
  (S1567.barAut_eq_one_iff (hN g.2) g.2).mpr fun v hv => by
    simpa [commutatorElement_def] using h v hv

theorem actN_eq_one_iff (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))
    (g : ↥(Subgroup.normalizer (E : Set G))) :
    actN V E hN g = 1 ↔ ∀ v ∈ V, (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈ E := by
  refine ⟨fun h v hv => ?_, actN_eq_one_of hN g⟩
  have := (S1567.barAut_eq_one_iff (hN g.2) g.2).mp h v hv
  simpa [commutatorElement_def] using this

variable (V E) in
@[expose] noncomputable def rhoC
    (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    ↥(Subgroup.centralizer (E : Set G)) →* MulAut (Qt V E) :=
  (actN V E hN).comp (Subgroup.inclusion (Subgroup.centralizer_le_normalizer _))

theorem rhoC_mk (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))
    (c : ↥(Subgroup.centralizer (E : Set G))) (v : ↥V) :
    rhoC V E hN c (mkQ V E v) =
      mkQ V E ⟨c * (v : G) * (c : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.centralizer_le_normalizer _ c.2)) v).mp v.2⟩ :=
  actN_mk hN _ v

theorem rhoC_ker (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))
    (c : ↥(Subgroup.centralizer (E : Set G))) :
    c ∈ (rhoC V E hN).ker ↔ ∀ v ∈ V, (c : G) * v * (c : G)⁻¹ * v⁻¹ ∈ E :=
  actN_eq_one_iff hN _

end Action

end CFSG.Quasithin.S153N.Bb
