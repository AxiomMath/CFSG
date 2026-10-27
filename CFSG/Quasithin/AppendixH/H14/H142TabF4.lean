module

public import CFSG.Quasithin.AppendixH.H14.H142Table
public import CFSG.Quasithin.AppendixH.H14.H142F4

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

variable {tab : Array (Array ℕ)}

@[expose] noncomputable def tabInv (hT : tabOK tab = true) :
    Multiplicative (Fin 2 → GF4) →* ↥(tabSub tab hT) where
  toFun w := ⟨tabPerm tab (codeOf (Multiplicative.toAdd w)),
    tabPerm_mem_tabSub hT (codeOf_lt _)⟩
  map_one' := by
    apply Subtype.ext
    show tabPerm tab (codeOf (Multiplicative.toAdd (1 : Multiplicative (Fin 2 → GF4)))) = 1
    have hc : codeOf (0 : Fin 2 → GF4) = 0 := by decide
    rw [toAdd_one, hc, tabPerm_zero hT]
  map_mul' := by
    intro a b
    apply Subtype.ext
    show tabPerm tab (codeOf (Multiplicative.toAdd (a * b))) =
      tabPerm tab (codeOf (Multiplicative.toAdd a)) * tabPerm tab (codeOf (Multiplicative.toAdd b))
    rw [toAdd_mul, codeOf_add]
    exact (tabPerm_mul hT (codeOf_lt (Multiplicative.toAdd a))
      (codeOf_lt (Multiplicative.toAdd b))).symm

theorem tabInv_ofAdd_wOfCode (hT : tabOK tab = true) {n : ℕ} (hn : n < 16) :
    tabInv hT (Multiplicative.ofAdd (wOfCode n)) =
      (⟨tabPerm tab n, tabPerm_mem_tabSub hT hn⟩ : ↥(tabSub tab hT)) := by
  apply Subtype.ext
  show tabPerm tab (codeOf (Multiplicative.toAdd (Multiplicative.ofAdd (wOfCode n)))) = tabPerm tab n
  rw [toAdd_ofAdd, codeOf_wOfCode hn]

theorem tabInv_bijective (hT : tabOK tab = true) : Function.Bijective (tabInv hT) := by
  constructor
  · intro a b h
    have h1 : tabPerm tab (codeOf (Multiplicative.toAdd a)) =
        tabPerm tab (codeOf (Multiplicative.toAdd b)) := congrArg Subtype.val h
    have h2 : codeOf (Multiplicative.toAdd a) = codeOf (Multiplicative.toAdd b) :=
      tabPerm_inj hT (codeOf_lt _) (codeOf_lt _) h1
    have h3 : Multiplicative.toAdd a = Multiplicative.toAdd b := by
      rw [← wOfCode_codeOf (Multiplicative.toAdd a),
        ← wOfCode_codeOf (Multiplicative.toAdd b), h2]
    simpa using congrArg Multiplicative.ofAdd h3
  · intro x
    obtain ⟨n, hn, heq⟩ := x.2
    refine ⟨Multiplicative.ofAdd (wOfCode n), ?_⟩
    apply Subtype.ext
    show (tabInv hT (Multiplicative.ofAdd (wOfCode n)) : S24) = (x : S24)
    rw [tabInv_ofAdd_wOfCode hT hn]
    exact heq.symm

@[expose] noncomputable def tabEquiv (hT : tabOK tab = true) :
    ↥(tabSub tab hT) ≃* Multiplicative (Fin 2 → GF4) :=
  (MulEquiv.ofBijective (tabInv hT) (tabInv_bijective hT)).symm

theorem tabEquiv_apply (hT : tabOK tab = true) {n : ℕ} (hn : n < 16) :
    tabEquiv hT ⟨tabPerm tab n, tabPerm_mem_tabSub hT hn⟩ =
      Multiplicative.ofAdd (wOfCode n) := by
  unfold tabEquiv
  apply (tabInv_bijective hT).1
  rw [MulEquiv.ofBijective_apply_symm_apply]
  exact (tabInv_ofAdd_wOfCode hT hn).symm

end CFSG.Quasithin.AppendixH.H14
