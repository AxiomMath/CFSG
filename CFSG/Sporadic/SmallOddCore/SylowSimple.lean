module

public import Mathlib.GroupTheory.Sylow
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

namespace CFSG.Sporadic.SmallOddCore

open scoped Pointwise

theorem isSimpleGroup_of_sylow_normalClosure {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (P : ℕ → Subgroup G)
    (hcard : ∀ p, p.Prime → p ∣ Nat.card G → Nat.card (P p) = p ^ (Nat.card G).factorization p)
    (hgen : ∀ p, p.Prime → p ∣ Nat.card G → ∀ x ∈ P p, orderOf x = p →
      Subgroup.normalClosure {x} = ⊤) :
    IsSimpleGroup G where
  eq_bot_or_eq_top_of_normal N hN := by
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    right
    have hN1 : Nat.card N ≠ 1 := fun h => hbot (Subgroup.card_eq_one.1 h)
    obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN1
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpN
    have hpG : p ∣ Nat.card G := hpN.trans (Subgroup.card_subgroup_dvd_card N)
    have hyo : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe, hy]
    have hpy : IsPGroup p (Subgroup.zpowers (y : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
    obtain ⟨S, hS⟩ := hpy.exists_le_sylow
    let Q : Sylow p G := Sylow.ofCard (P p) (hcard p hp hpG)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
    have hyS : (y : G) ∈ (S : Subgroup G) := hS (Subgroup.mem_zpowers _)
    have hmem : g * (y : G) * g⁻¹ ∈ P p := by
      have h1 : MulAut.conj g • (y : G) ∈ MulAut.conj g • (S : Subgroup G) :=
        Subgroup.smul_mem_pointwise_smul _ _ _ hyS
      rw [← Sylow.coe_subgroup_smul, hg, MulAut.smul_def, MulAut.conj_apply] at h1
      exact h1
    have hord : orderOf (g * (y : G) * g⁻¹) = p := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hyo]
    have hyN : g * (y : G) * g⁻¹ ∈ N := hN.conj_mem _ y.2 g
    rw [eq_top_iff, ← hgen p hp hpG _ hmem hord]
    exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.2 hyN)

theorem isSimpleGroup_of_sylow_normalClosure_le {H : Type*} [Group H] (D : Subgroup H)
    [Finite D] [Nontrivial D] (P : ℕ → Subgroup H) (hPD : ∀ p, P p ≤ D)
    (hcard : ∀ p, p.Prime → p ∣ Nat.card D → Nat.card (P p) = p ^ (Nat.card D).factorization p)
    (hgen : ∀ p, p.Prime → p ∣ Nat.card D → ∀ x : D, (x : H) ∈ P p → orderOf x = p →
      Subgroup.normalClosure {x} = ⊤) :
    IsSimpleGroup D :=
  isSimpleGroup_of_sylow_normalClosure (fun p => (P p).subgroupOf D)
    (fun p hp hd => by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPD p)).toEquiv]
      exact hcard p hp hd)
    (fun p hp hd x hx ho => hgen p hp hd x (Subgroup.mem_subgroupOf.1 hx) ho)

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def nclConjs (m : ℕ) (gens ginv : Array Tab) (x : Tab) (cs : List (List ℕ × List ℕ)) :
    Array Tab :=
  (cs.map fun c => comp m (comp m (wordTabS m gens c.1) x) (wordTabS m ginv c.2)).toArray

@[expose] def nclWordsOK (m : ℕ) (gens ginv : Array Tab) (x : Tab) (cs : List (List ℕ × List ℕ))
    (W : List (List ℕ)) : Bool :=
  cs.all (fun c => c.1.all (fun j => decide (j < gens.size)) &&
      c.2.all (fun j => decide (j < ginv.size)) &&
      comp m (wordTabS m ginv c.2) (wordTabS m gens c.1) == idTab m) &&
    allBelow gens.size fun j => (W.getD j []).all (fun i => decide (i < cs.length)) &&
      wordTabS m (nclConjs m gens ginv x cs) (W.getD j []) == gens[j]!

theorem wordProd_mem_genGroup {m : ℕ} {gens : Array Tab} {f : ℕ → Equiv.Perm (Fin m)}
    {w : List ℕ} (hw : ∀ j ∈ w, j < gens.size) : (w.map f).prod ∈ genGroup m gens f :=
  (genGroup m gens f).list_prod_mem fun z hz => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
    exact Subgroup.subset_closure ⟨j, hw j hj, rfl⟩

theorem normalClosure_eq_top_of_nclWordsOK {m : ℕ} {gens : Array Tab}
    {f : ℕ → Equiv.Perm (Fin m)} (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    {ginv : Array Tab} {fi : ℕ → Equiv.Perm (Fin m)}
    (hgis : ∀ j < ginv.size, TabRep ginv[j]! (fi j)) {x : genGroup m gens f} {xt : Tab}
    (hx : TabRep xt (x : Equiv.Perm (Fin m))) {cs : List (List ℕ × List ℕ)} {W : List (List ℕ)}
    (h : nclWordsOK m gens ginv xt cs W = true) :
    Subgroup.normalClosure ({x} : Set (genGroup m gens f)) = ⊤ := by
  set K := Subgroup.normalClosure ({x} : Set (genGroup m gens f))
  simp only [nclWordsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    allBelow_eq_true] at h
  obtain ⟨hcs, hW⟩ := h
  have hY : ∀ i < cs.length, ∃ y : genGroup m gens f,
      y ∈ K ∧ TabRep (nclConjs m gens ginv xt cs)[i]! (y : Equiv.Perm (Fin m)) := by
    intro i hi
    obtain ⟨⟨hu, hv⟩, h3⟩ := hcs _ (List.getElem_mem hi)
    have hg := tabRep_wordTabS hgs _ hu
    have hg' := tabRep_wordTabS hgis _ hv
    have hinv : (cs[i].2.map fi).prod = (cs[i].1.map f).prod⁻¹ := by
      have hc := (hg'.comp hg).perm_eq (by rw [h3]; exact TabRep.idTab)
      exact eq_inv_of_mul_eq_one_left hc
    rw [hinv] at hg'
    set g : genGroup m gens f := ⟨_, wordProd_mem_genGroup hu⟩
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · exact Subgroup.normalClosure_normal.conj_mem _
        (Subgroup.subset_normalClosure (Set.mem_singleton x)) _
    · have e : (nclConjs m gens ginv xt cs)[i]! =
          comp m (comp m (wordTabS m gens cs[i].1) xt) (wordTabS m ginv cs[i].2) := by
        rw [nclConjs, getElem!_pos _ i (by simpa using hi)]
        simp
      rw [e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (hg.comp hx).comp hg'
  obtain ⟨y, hy⟩ : ∃ y : ℕ → genGroup m gens f, ∀ i < cs.length,
      y i ∈ K ∧ TabRep (nclConjs m gens ginv xt cs)[i]! (y i : Equiv.Perm (Fin m)) := by
    classical
    exact ⟨fun i => if hi : i < cs.length then (hY i hi).choose else 1,
      fun i hi => by simpa [hi] using (hY i hi).choose_spec⟩
  have hsz : (nclConjs m gens ginv xt cs).size = cs.length := by simp [nclConjs]
  have hgen : ∀ j < gens.size, f j ∈ K.map (genGroup m gens f).subtype := by
    intro j hj
    obtain ⟨hlt, hw⟩ := hW j hj
    have hrep := tabRep_wordTabS (f := fun i => (y i : Equiv.Perm (Fin m)))
      (gs := nclConjs m gens ginv xt cs) (fun i hi => (hy i (hsz ▸ hi)).2) (W.getD j [])
      (fun i hi => hsz ▸ hlt i hi)
    rw [hw] at hrep
    have he := (hgs j hj).perm_eq hrep
    refine ⟨((W.getD j []).map y).prod, K.list_prod_mem fun z hz => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
      exact (hy i (hlt i hi)).1
    · rw [he, map_list_prod, List.map_map]
      rfl
  have hle : genGroup m gens f ≤ K.map (genGroup m gens f).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    exact hgen j hj
  rw [eq_top_iff]
  intro d _
  obtain ⟨d', hd', he⟩ := hle d.2
  rw [← Subtype.ext he]
  exact hd'

end CFSG.Sporadic.SmallOddCore

end
