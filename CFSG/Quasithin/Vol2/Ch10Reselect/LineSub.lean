module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Model

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix
open scoped commutatorElement

namespace UModel

variable {G : Type} [Group G] {A U Z L : Subgroup G} {K : Type} [Field K]

@[expose] def lineSub (M : UModel A U Z L K) (w : Fin 2 → K) : Subgroup G where
  carrier := {u | ∃ hu : u ∈ U, Multiplicative.toAdd (M.ψ ⟨u, hu⟩) ∈ lineAdd K w}
  mul_mem' := by
    rintro a b ⟨ha, hpa⟩ ⟨hb, hpb⟩
    refine ⟨U.mul_mem ha hb, ?_⟩
    have hmul : M.ψ ⟨a * b, U.mul_mem ha hb⟩ = M.ψ ⟨a, ha⟩ * M.ψ ⟨b, hb⟩ :=
      map_mul M.ψ ⟨a, ha⟩ ⟨b, hb⟩
    rw [hmul, toAdd_mul]
    exact (lineAdd K w).add_mem hpa hpb
  one_mem' := by
    refine ⟨U.one_mem, ?_⟩
    have h1 : M.ψ ⟨1, U.one_mem⟩ = 1 := map_one M.ψ
    rw [h1, toAdd_one]
    exact (lineAdd K w).zero_mem
  inv_mem' := by
    rintro a ⟨ha, hpa⟩
    refine ⟨U.inv_mem ha, ?_⟩
    have h2 : M.ψ ⟨a⁻¹, U.inv_mem ha⟩ = (M.ψ ⟨a, ha⟩)⁻¹ := map_inv M.ψ ⟨a, ha⟩
    rw [h2, toAdd_inv]
    exact (lineAdd K w).neg_mem hpa

theorem mem_lineSub_iff (M : UModel A U Z L K) (w : Fin 2 → K) {u : G} :
    u ∈ M.lineSub w ↔ ∃ hu : u ∈ U, Multiplicative.toAdd (M.ψ ⟨u, hu⟩) ∈ lineAdd K w :=
  Iff.rfl

theorem lineSub_le_U (M : UModel A U Z L K) (w : Fin 2 → K) : M.lineSub w ≤ U := by
  intro u hu
  exact ((mem_lineSub_iff M w).mp hu).1

theorem L_le_normalizer_lineSub (M : UModel A U Z L K) (w : Fin 2 → K)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    L ≤ Subgroup.normalizer (M.lineSub w : Set G) := by
  have fwd : ∀ l ∈ L, ∀ x ∈ M.lineSub w, l * x * l⁻¹ ∈ M.lineSub w := by
    intro l hl x hx
    obtain ⟨hxU, hpx⟩ := (mem_lineSub_iff M w).mp hx
    have hlU : l * x * l⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hLU hl) x).mp hxU
    refine (mem_lineSub_iff M w).mpr ⟨hlU, ?_⟩
    have h2 : Multiplicative.toAdd (M.ψ ⟨l * x * l⁻¹, hlU⟩) =
        rhoSL K (M.γ ⟨l, hl⟩) (Multiplicative.toAdd (M.ψ ⟨x, hxU⟩)) :=
      congrArg Multiplicative.toAdd (M.equiv ⟨l, hl⟩ ⟨x, hxU⟩ hlU)
    rw [h2]
    exact rhoSL_mem_lineAdd _ hpx
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fwd l hl x
  · intro hx
    have h := fwd l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
    simpa [mul_assoc] using h

@[expose] def lineJ (M : UModel A U Z L K) (w : Fin 2 → K) : Subgroup G :=
  ⁅M.lineSub w, L⁆

theorem lineJ_le_lineSub (M : UModel A U Z L K) (w : Fin 2 → K)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) : M.lineJ w ≤ M.lineSub w := by
  show ⁅M.lineSub w, L⁆ ≤ M.lineSub w
  refine Subgroup.commutator_le.mpr ?_
  intro h hh k hk
  have hk' : k * h⁻¹ * k⁻¹ ∈ M.lineSub w :=
    (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_lineSub M w hLU hk) h⁻¹).mp
      ((M.lineSub w).inv_mem hh)
  have h3 := (M.lineSub w).mul_mem hh hk'
  rw [commutatorElement_def]
  simpa [mul_assoc] using h3

theorem lineJ_le_U (M : UModel A U Z L K) (w : Fin 2 → K)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) : M.lineJ w ≤ U :=
  (lineJ_le_lineSub M w hLU).trans (lineSub_le_U M w)

theorem L_le_normalizer_lineJ (M : UModel A U Z L K) (w : Fin 2 → K)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) : L ≤ Subgroup.normalizer (M.lineJ w : Set G) := by
  have fwd : ∀ l ∈ L, ∀ x ∈ M.lineJ w, l * x * l⁻¹ ∈ M.lineJ w := by
    intro l hl
    have hlN : l ∈ Subgroup.normalizer (M.lineSub w : Set G) :=
      L_le_normalizer_lineSub M w hLU hl
    have hlL : l ∈ Subgroup.normalizer (L : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      exact ⟨fun hh => L.mul_mem (L.mul_mem hl hh) (L.inv_mem hl),
        fun hh => by simpa [mul_assoc] using L.mul_mem (L.mul_mem (L.inv_mem hl) hh) hl⟩
    have key : ⁅M.lineSub w, L⁆ ≤
        (⁅M.lineSub w, L⁆ : Subgroup G).comap (MulAut.conj l).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro h hh k hk
      have hc : ⁅l * h * l⁻¹, l * k * l⁻¹⁆ ∈ ⁅M.lineSub w, L⁆ :=
        Subgroup.commutator_mem_commutator
          ((Subgroup.mem_normalizer_iff.mp hlN h).mp hh)
          ((Subgroup.mem_normalizer_iff.mp hlL k).mp hk)
      rw [Subgroup.mem_comap]
      simpa [commutatorElement_def, mul_assoc] using hc
    intro x hx
    exact Subgroup.mem_comap.mp (key hx)
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fwd l hl x
  · intro hx
    have h := fwd l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
    simpa [mul_assoc] using h

theorem psi_mem_line_of_mem_lineJ (M : UModel A U Z L K) (w : Fin 2 → K)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) {j : G} (hj : j ∈ M.lineJ w) (hjU : j ∈ U) :
    Multiplicative.toAdd (M.ψ ⟨j, hjU⟩) ∈ lineAdd K w := by
  obtain ⟨_, h⟩ := (mem_lineSub_iff M w).mp (lineJ_le_lineSub M w hLU hj)
  exact h

private def psiImage (M : UModel A U Z L K) (H : Subgroup G) : AddSubgroup (UTilde K) where
  carrier := {x | ∃ (j : G) (_ : j ∈ H) (hjU : j ∈ U), Multiplicative.toAdd (M.ψ ⟨j, hjU⟩) = x}
  add_mem' := by
    rintro _ _ ⟨a, ha, haU, rfl⟩ ⟨b, hb, hbU, rfl⟩
    refine ⟨a * b, H.mul_mem ha hb, U.mul_mem haU hbU, ?_⟩
    have hmul : M.ψ ⟨a * b, U.mul_mem haU hbU⟩ = M.ψ ⟨a, haU⟩ * M.ψ ⟨b, hbU⟩ :=
      map_mul M.ψ ⟨a, haU⟩ ⟨b, hbU⟩
    rw [hmul, toAdd_mul]
  zero_mem' := by
    refine ⟨1, H.one_mem, U.one_mem, ?_⟩
    have h1 : M.ψ ⟨1, U.one_mem⟩ = 1 := map_one M.ψ
    rw [h1, toAdd_one]
  neg_mem' := by
    rintro _ ⟨a, ha, haU, rfl⟩
    refine ⟨a⁻¹, H.inv_mem ha, U.inv_mem haU, ?_⟩
    have h2 : M.ψ ⟨a⁻¹, U.inv_mem haU⟩ = (M.ψ ⟨a, haU⟩)⁻¹ := map_inv M.ψ ⟨a, haU⟩
    rw [h2, toAdd_inv]

theorem exists_lineJ_psi_eq [Nontrivial K] (M : UModel A U Z L K) {w : Fin 2 → K} (hw : w ≠ 0)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) {p : UTilde K} (hp : p ∈ lineAdd K w) :
    ∃ (j : G) (hj : j ∈ M.lineJ w) (hjU : j ∈ U), Multiplicative.toAdd (M.ψ ⟨j, hjU⟩) = p := by
  have hle : lineAdd K w ≤ psiImage M (M.lineJ w) := by
    calc lineAdd K w
        = AddSubgroup.closure {x : UTilde K | ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K)
            (q : UTilde K), q ∈ lineAdd K w ∧ x = rhoSL K g q - q} := (lineAdd_perfect hw).symm
      _ ≤ psiImage M (M.lineJ w) := by
        rw [AddSubgroup.closure_le]
        rintro x ⟨g, q, hq, rfl⟩
        obtain ⟨u, hu⟩ := M.surj (Multiplicative.ofAdd q)
        obtain ⟨l, hl⟩ := M.γ_surj g
        have huq : Multiplicative.toAdd (M.ψ u) = q := by
          rw [hu, toAdd_ofAdd]
        have hu_line : (u : G) ∈ M.lineSub w := by
          refine (mem_lineSub_iff M w).mpr ⟨u.2, ?_⟩
          show Multiplicative.toAdd (M.ψ u) ∈ lineAdd K w
          rw [huq]
          exact hq
        have hlu : (l : G) * (u : G) * (l : G)⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (hLU l.2) (u : G)).mp u.2
        have hjlJ : (l : G) * (u : G) * (l : G)⁻¹ * (u : G)⁻¹ ∈ M.lineJ w := by
          have hc : ⁅(u : G), (l : G)⁆ ∈ M.lineJ w :=
            Subgroup.commutator_mem_commutator hu_line l.2
          have e : (⁅(u : G), (l : G)⁆)⁻¹ = (l : G) * (u : G) * (l : G)⁻¹ * (u : G)⁻¹ := by
            rw [commutatorElement_def]
            group
          rw [← e]
          exact (M.lineJ w).inv_mem hc
        have hjU : (l : G) * (u : G) * (l : G)⁻¹ * (u : G)⁻¹ ∈ U :=
          U.mul_mem hlu (U.inv_mem u.2)
        refine ⟨(l : G) * (u : G) * (l : G)⁻¹ * (u : G)⁻¹, hjlJ, hjU, ?_⟩
        have hsplit : (⟨(l : G) * (u : G) * (l : G)⁻¹ * (u : G)⁻¹, hjU⟩ : ↥U) =
            ⟨(l : G) * (u : G) * (l : G)⁻¹, hlu⟩ * u⁻¹ := rfl
        have h1 : M.ψ ⟨(l : G) * (u : G) * (l : G)⁻¹, hlu⟩ =
            Multiplicative.ofAdd (rhoSL K (M.γ l) q) := by
          rw [M.equiv l u hlu, huq]
        rw [hsplit, map_mul, map_inv, h1, hu, hl, toAdd_mul, toAdd_inv, toAdd_ofAdd,
          toAdd_ofAdd, sub_eq_add_neg]
  exact hle hp

theorem exists_lineJ_mul_mem_Z [Nontrivial K] (M : UModel A U Z L K) {w : Fin 2 → K} (hw : w ≠ 0)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) {u : G} (hu : u ∈ M.lineSub w) :
    ∃ j ∈ M.lineJ w, u * j⁻¹ ∈ Z := by
  obtain ⟨huU, hp⟩ := (mem_lineSub_iff M w).mp hu
  obtain ⟨j, hj, hjU, hpj⟩ := exists_lineJ_psi_eq M hw hLU hp
  have hψ : M.ψ ⟨j, hjU⟩ = M.ψ ⟨u, huU⟩ := Multiplicative.toAdd.injective hpj
  refine ⟨j, hj, ?_⟩
  have hmem : u * j⁻¹ ∈ U := U.mul_mem huU (U.inv_mem hjU)
  have hψ1 : M.ψ ⟨u * j⁻¹, hmem⟩ = 1 := by
    have e : (⟨u * j⁻¹, hmem⟩ : ↥U) = ⟨u, huU⟩ * ⟨j, hjU⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, hψ, mul_inv_cancel]
  exact (M.ker ⟨u * j⁻¹, hmem⟩).mp hψ1

end UModel

end CFSG.Quasithin.Vol2.Ch10Reselect
