module

public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G]

@[expose] def cenL0 (T L I : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ fsuM T L ∧ ∀ l ∈ fsuL0 T L,
    g * l * g⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G)}
  one_mem' := ⟨Subgroup.one_mem _, fun l _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgc⟩ ⟨hh, hhc⟩
    refine ⟨Subgroup.mul_mem _ hg hh, fun l hl => ?_⟩
    have hgN : g ∈ Subgroup.normalizer
        ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
      SecA.le_normalizer_centralizer (SecA.fsuM_le_normalizer_fsuVM T L I) hg
    have h1 := (Subgroup.mem_normalizer_iff.mp hgN _).mp (hhc l hl)
    have h2 := Subgroup.mul_mem _ h1 (hgc l hl)
    have e : g * h * l * (g * h)⁻¹ * l⁻¹ =
        g * (h * l * h⁻¹ * l⁻¹) * g⁻¹ * (g * l * g⁻¹ * l⁻¹) := by group
    rw [e]
    exact h2
  inv_mem' := by
    rintro g ⟨hg, hgc⟩
    refine ⟨Subgroup.inv_mem _ hg, fun l hl => ?_⟩
    have hgN : g⁻¹ ∈ Subgroup.normalizer
        ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
      SecA.le_normalizer_centralizer (SecA.fsuM_le_normalizer_fsuVM T L I) (Subgroup.inv_mem _ hg)
    have h1 := (Subgroup.mem_normalizer_iff.mp hgN _).mp
      (Subgroup.inv_mem _ (hgc l hl))
    have e : g⁻¹ * l * g⁻¹⁻¹ * l⁻¹ = g⁻¹ * (g * l * g⁻¹ * l⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem mem_cenL0 {T L I : Subgroup G} {g : G} :
    g ∈ cenL0 T L I ↔ g ∈ fsuM T L ∧ ∀ l ∈ fsuL0 T L,
      g * l * g⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
  Iff.rfl

theorem fsuM_le_normalizer_cenL0 (T L I : Subgroup G) :
    fsuM T L ≤ Subgroup.normalizer (cenL0 T L I : Set G) := by
  have key : ∀ x ∈ fsuM T L, ∀ g ∈ cenL0 T L I, x * g * x⁻¹ ∈ cenL0 T L I := by
    intro x hx g ⟨hg, hgc⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hg) (Subgroup.inv_mem _ hx),
      fun l hl => ?_⟩
    have hl' : x⁻¹ * l * x ∈ fsuL0 T L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) l).mp hl
      simpa using this
    have hxN : x ∈ Subgroup.normalizer
        ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
      SecA.le_normalizer_centralizer (SecA.fsuM_le_normalizer_fsuVM T L I) hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN _).mp (hgc _ hl')
    have e : x * g * x⁻¹ * l * (x * g * x⁻¹)⁻¹ * l⁻¹ =
        x * (g * (x⁻¹ * l * x) * g⁻¹ * (x⁻¹ * l * x)⁻¹) * x⁻¹ := by group
    rw [e]
    exact h1
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact key x hx g
  · intro h
    have := key x⁻¹ (Subgroup.inv_mem _ hx) _ h
    simpa [mul_assoc] using this

variable [Finite G] {T L I : Subgroup G}

theorem not_dvd_of_mem_cenL0
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1013 : Stmt10_1_3) (hyp : Hyp10 G T L I) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G}
    (ha : a ∈ cenL0 T L I) (hao : orderOf a = p) :
    ¬ p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hpd
  have hM := h1013 G T L I hyp p hp hp2 hpd
  have haL0 : a ∈ fsuL0 T L := by
    rw [← hM]
    exact Subgroup.subset_closure ⟨ha.1, 1, by rw [pow_one, hao]⟩
  have hO : a ∈ pCoreOf 2 (fsuL0 T L) :=
    SecA.mem_pCoreOf_fsuL0_of_commutator h37 h38 hyp haL0 fun y hy =>
      SecA.fsuL0_inf_centralizer_le h37 h38 hyp
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haL0 hy)
          (Subgroup.inv_mem _ haL0)) (Subgroup.inv_mem _ hy), by
          rw [commutatorElement_def]; exact ha.2 y hy⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L)) ⟨a, hO⟩
  have hk' : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd : p ∣ 2 ^ k := hao ▸ orderOf_dvd_of_pow_eq_one hk'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))

end CFSG.Quasithin.Vol2.Ch10.SecB
