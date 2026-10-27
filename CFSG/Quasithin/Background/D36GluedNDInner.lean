module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin

namespace XMod

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

theorem fixes_of_isHomComp (hQ : ∀ q : Q, q ^ 2 = 1) {M L : Subgroup Q} (hML : IsHomComp A M L)
    (c : Q → Q) (hmul : ∀ x y, c (x * y) = c x * c y) (hcc : ∀ x ∈ M, c (c x) = x)
    (hcM : ∀ q ∈ M, c q ∈ M) (hcequiv : ∀ (a : A), ∀ q ∈ L, c (a • q) = a • c q) :
    ∀ q ∈ L, c q = q := by
  obtain ⟨hirr, hLM, hmax⟩ := hML
  have hone : c 1 = 1 := by
    have h1 : c 1 * c 1 = c 1 * 1 := by rw [← hmul, mul_one, mul_one]
    exact mul_left_cancel h1
  have hinvc : ∀ x, c x⁻¹ = (c x)⁻¹ := fun x => by
    have h := hmul x x⁻¹
    rw [mul_inv_cancel, hone] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  let ch : Q →* Q := MonoidHom.mk' c hmul
  set L' : Subgroup Q := L.map ch with hL'
  have hL'mem : ∀ y, y ∈ L' ↔ ∃ x ∈ L, c x = y := fun y => by
    rw [hL', Subgroup.mem_map]
    rfl
  have hLL : ∀ x ∈ L, c x ∈ M := fun x hx => hcM x (hLM hx)
  have hcL' : ∀ y ∈ L', c y ∈ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hL'mem y).mp hy
    rw [hcc x (hLM hx)]
    exact hx
  have hequiv' : ∀ (a : A), ∀ y ∈ L', c (a • y) = a • c y := by
    intro a y hy
    obtain ⟨x, hx, rfl⟩ := (hL'mem y).mp hy
    have h1 : a • c x = c (a • x) := (hcequiv a x hx).symm
    have h2 : a • x ∈ L := hirr.1 a x hx
    rw [h1, hcc _ (hLM h2), hcc x (hLM hx)]
  have hinv' : IsInv A L' := by
    intro a y hy
    obtain ⟨x, hx, rfl⟩ := (hL'mem y).mp hy
    rw [← hcequiv a x hx]
    exact (hL'mem _).mpr ⟨a • x, hirr.1 a x hx, rfl⟩
  have hL'M : L' ≤ M := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := (hL'mem y).mp hy
    exact hLL x hx
  have hirr' : IsIrr A L' := by
    refine ⟨hinv', ?_, fun J hJ _ hJL' => ?_⟩
    · have hne : L ≠ ⊥ := hirr.2.1.ne'
      refine bot_lt_iff_ne_bot.2 fun h => hne ?_
      rw [eq_bot_iff]
      intro x hx
      have : c x ∈ L' := (hL'mem _).mpr ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      have h2 : c (c x) = c 1 := by rw [this]
      rw [hcc x (hLM hx), hone] at h2
      exact Subgroup.mem_bot.mpr h2
    ·
      let J' : Subgroup Q :=
        { carrier := {x | x ∈ L ∧ c x ∈ J}
          one_mem' := ⟨L.one_mem, by rw [hone]; exact J.one_mem⟩
          mul_mem' := fun {x y} hx hy => ⟨L.mul_mem hx.1 hy.1, by
            rw [hmul]; exact J.mul_mem hx.2 hy.2⟩
          inv_mem' := fun {x} hx => ⟨L.inv_mem hx.1, by
            rw [hinvc]; exact J.inv_mem hx.2⟩ }
      have hJ'inv : IsInv A J' := by
        intro a x hx
        refine ⟨hirr.1 a x hx.1, ?_⟩
        rw [hcequiv a x hx.1]
        exact hJ a _ hx.2
      have hJ'L : J' ≤ L := fun x hx => hx.1
      rcases hirr.2.2 J' hJ'inv bot_le hJ'L with h | h
      · left
        rw [eq_bot_iff]
        intro y hy
        have hyL' : y ∈ L' := hJL' hy
        have hcy : c y ∈ J' := ⟨hcL' y hyL', by rw [hcc y (hL'M hyL')]; exact hy⟩
        rw [h, Subgroup.mem_bot] at hcy
        have h2 : c (c y) = c 1 := by rw [hcy]
        rw [hcc y (hL'M hyL'), hone] at h2
        exact Subgroup.mem_bot.mpr h2
      · right
        refine le_antisymm hJL' fun y hy => ?_
        obtain ⟨x, hx, rfl⟩ := (hL'mem y).mp hy
        have : x ∈ J' := by rw [h]; exact hx
        have h3 := this.2
        exact h3
  have hiso : Iso A L' L := by
    refine ⟨{ toFun := fun y => ⟨c y, hcL' y y.2⟩
              invFun := fun x => ⟨c x, (hL'mem _).mpr ⟨x, x.2, rfl⟩⟩
              left_inv := fun y => Subtype.ext (hcc y (hL'M y.2))
              right_inv := fun x => Subtype.ext (hcc x (hLM x.2))
              map_mul' := fun y z => Subtype.ext (hmul y z) }, ?_⟩
    intro a l l' h
    show a • c (l : Q) = c (l' : Q)
    rw [← h]
    exact (hequiv' a l l.2).symm
  have hsub := hmax L' hL'M hirr' hiso
  have hcLL : ∀ x ∈ L, c x ∈ L := fun x hx => hsub ((hL'mem _).mpr ⟨x, hx, rfl⟩)
  let K : Subgroup Q :=
    { carrier := {x | x ∈ L ∧ c x = x}
      one_mem' := ⟨L.one_mem, hone⟩
      mul_mem' := fun {x y} hx hy => ⟨L.mul_mem hx.1 hy.1, by rw [hmul, hx.2, hy.2]⟩
      inv_mem' := fun {x} hx => ⟨L.inv_mem hx.1, by rw [hinvc, hx.2]⟩ }
  have hKinv : IsInv A K := fun a x hx => ⟨hirr.1 a x hx.1, by rw [hcequiv a x hx.1, hx.2]⟩
  have hKL : K ≤ L := fun x hx => hx.1
  have hne : L ≠ ⊥ := hirr.2.1.ne'
  rcases hirr.2.2 K hKinv bot_le hKL with hK | hK
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hNx : c x * x⁻¹ ∈ K := by
      refine ⟨L.mul_mem (hcLL x hx) (L.inv_mem hx), ?_⟩
      rw [hmul, hinvc, hcc x (hLM hx)]
      have e1 : (c x)⁻¹ = c x := by
        have := hQ (c x)
        rw [pow_two] at this
        exact inv_eq_of_mul_eq_one_right this
      have e2 : x⁻¹ = x := by
        have := hQ x
        rw [pow_two] at this
        exact inv_eq_of_mul_eq_one_right this
      rw [e1, e2, mul_comm]
    rw [hK, Subgroup.mem_bot, mul_inv_eq_one] at hNx
    have : x ∈ K := ⟨hx, hNx⟩
    rw [hK] at this
    exact this
  · intro q hq
    have : q ∈ K := by rw [hK]; exact hq
    exact this.2

end XMod

end CFSG.Quasithin
