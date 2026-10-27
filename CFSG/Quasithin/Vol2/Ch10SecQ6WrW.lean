module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrCl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

variable {W : Type*} [CommGroup W] (ρ : SymFiveWrTwo →* MulAut W)

@[expose] noncomputable def Phi (c : W) (p : PMod) : W :=
  ∏ z : Fin 5 × Fin 5, (ρ (rep z) c) ^ (p z.1 z.2).val

theorem pow_val_add {w : W} (hw : w ^ 2 = 1) (a b : ZMod 2) :
    w ^ (a + b).val = w ^ a.val * w ^ b.val := by
  fin_cases a <;> fin_cases b
  · change w ^ 0 = w ^ 0 * w ^ 0
    simp
  · change w ^ 1 = w ^ 0 * w ^ 1
    simp
  · change w ^ 1 = w ^ 1 * w ^ 0
    simp
  · change w ^ 0 = w ^ 1 * w ^ 1
    rw [pow_zero, ← pow_add, hw]

theorem Phi_add (hW : ∀ w : W, w ^ 2 = 1) (c : W) (p p' : PMod) :
    Phi ρ c (p + p') = Phi ρ c p * Phi ρ c p' := by
  unfold Phi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun z _ => pow_val_add (hW _) _ _

theorem Phi_zero (c : W) : Phi ρ c 0 = 1 := by
  unfold Phi
  simp

theorem fix_of_mem_Y0 {c : W} (hc : c ∈ fixV (Y0.map ρ)) {y : SymFiveWrTwo} (hy : y ∈ Y0) :
    ρ y c = c :=
  hc _ ⟨y, hy, rfl⟩

theorem rho_mul_rep {c : W} (hc : c ∈ fixV (Y0.map ρ)) (g : SymFiveWrTwo)
    (z : Fin 5 × Fin 5) : ρ (g * rep z) c = ρ (rep (pairAct g z)) c := by
  rw [mul_rep_eq, map_mul, MulAut.mul_apply, fix_of_mem_Y0 ρ hc (rep_inv_mul_mem_Y0 g z)]

theorem Phi_gP {c : W} (hc : c ∈ fixV (Y0.map ρ)) (g : SymFiveWrTwo) (p : PMod) :
    ρ g (Phi ρ c p) = Phi ρ c (gP g p) := by
  unfold Phi
  rw [map_prod]
  refine Fintype.prod_equiv (pairPerm g) _ _ fun z => ?_
  change ρ g ((ρ (rep z) c) ^ (p z.1 z.2).val) =
    (ρ (rep (pairAct g z)) c) ^ (gP g p (pairAct g z).1 (pairAct g z).2).val
  rw [map_pow, ← MulAut.mul_apply, ← map_mul, rho_mul_rep ρ hc, gP_apply, pairAct_inv_pairAct]

theorem Phi_delta (c : W) (z : Fin 5 × Fin 5) : Phi ρ c (delta z) = ρ (rep z) c := by
  unfold Phi
  rw [Finset.prod_eq_single z (fun z' _ hz' => by simp [delta, hz']) (by simp)]
  simp only [delta, Prod.mk.eta, ite_true]
  exact pow_one _

theorem Phi_inj (hW : ∀ w : W, w ^ 2 = 1) {c : W} (hc : c ∈ fixV (Y0.map ρ))
    {V : AddSubgroup PMod} (hV : ∀ g : SymFiveWrTwo, ∀ v ∈ V, gP g v ∈ V)
    (hirr : ∀ K : AddSubgroup PMod, K ≤ V → (∀ g : SymFiveWrTwo, ∀ k ∈ K, gP g k ∈ K) →
      K ≠ ⊥ → V ≤ K)
    (hne : ∃ m ∈ V, Phi ρ c m ≠ 1) {m m' : PMod} (hm : m ∈ V) (hm' : m' ∈ V)
    (h : Phi ρ c m = Phi ρ c m') : m = m' := by
  let K : AddSubgroup PMod :=
    { carrier := {k | k ∈ V ∧ Phi ρ c k = 1}
      zero_mem' := ⟨V.zero_mem, Phi_zero ρ c⟩
      add_mem' := fun {a b} ha hb => ⟨V.add_mem ha.1 hb.1, by
        rw [Phi_add ρ hW, ha.2, hb.2, mul_one]⟩
      neg_mem' := fun {a} ha => ⟨V.neg_mem ha.1, by
        calc Phi ρ c (-a) = Phi ρ c a := by
              congr 1
              funext i j
              exact zmod_two_neg (a i j)
          _ = 1 := ha.2⟩ }
  have hKbot : K = ⊥ := by
    by_contra hK
    obtain ⟨m1, hm1, hm1'⟩ := hne
    apply hm1'
    exact (hirr K (fun _ hk => hk.1) (fun g k hk => ⟨hV g k hk.1, by
      rw [← Phi_gP ρ hc, hk.2, map_one]⟩) hK hm1).2
  have hmm : m + m' ∈ K := ⟨V.add_mem hm hm', by rw [Phi_add ρ hW, h, ← sq, hW]⟩
  rw [hKbot, AddSubgroup.mem_bot] at hmm
  funext i j
  have := congrFun (congrFun hmm i) j
  simp only [Pi.add_apply, Pi.zero_apply] at this
  exact zmod_two_eq_of_add this

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
