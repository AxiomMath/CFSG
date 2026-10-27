module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Syl
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace A7Mod

@[expose] def Concl (K S : Subgroup (Equiv.Perm (Fin 7))) (v : V7)
    (U : Submodule (ZMod 2) V7) : Prop :=
  (∀ s ∈ S, ∀ u ∈ U, pAct s u ∈ U) ∧ (∀ u ∈ U, B0 v u = 0) ∧ v ∉ U ∧
    ((∀ A : Subgroup (Equiv.Perm (Fin 7)), A ≤ S → IsElemAbelian 2 A →
        (∀ a ∈ A, ∀ u ∈ U, pAct a u = u) → Nat.card A ≤ 2) ∨
      ((∀ A : Subgroup (Equiv.Perm (Fin 7)), A ≤ S → IsElemAbelian 2 A →
          (∀ a ∈ A, ∀ u ∈ U, pAct a u = u) → Nat.card A ≤ 4) ∧
        ∃ Y : Subgroup (Equiv.Perm (Fin 7)), Y ≤ K ∧ (∀ y ∈ Y, pAct y v = v) ∧
          IsElemAbelian 3 Y ∧ Nat.card Y = 9))

theorem pAct_conj_apply (g s : Equiv.Perm (Fin 7)) (u : V7) :
    pAct (MulAut.conj g s) (pAct g u) = pAct g (pAct s u) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  change pAct g (pAct s ((pAct g).symm (pAct g u))) = pAct g (pAct s u)
  rw [LinearEquiv.symm_apply_apply]

theorem pAct_inv_apply (g : Equiv.Perm (Fin 7)) (u : V7) : pAct g⁻¹ (pAct g u) = u := by
  rw [map_inv]
  exact LinearEquiv.symm_apply_apply _ u

theorem Concl.conj {K S : Subgroup (Equiv.Perm (Fin 7))} {v : V7} {U : Submodule (ZMod 2) V7}
    (hc : Concl K S v U) {g : Equiv.Perm (Fin 7)} (hg : g ∈ K) :
    Concl K (S.map (MulAut.conj g).toMonoidHom) (pAct g v)
      (U.map (pAct g : V7 ≃ₗ[ZMod 2] V7).toLinearMap) := by
  obtain ⟨hinv, horth, hnot, hcases⟩ := hc
  have hA : ∀ k : ℕ, (∀ A : Subgroup (Equiv.Perm (Fin 7)), A ≤ S → IsElemAbelian 2 A →
      (∀ a ∈ A, ∀ u ∈ U, pAct a u = u) → Nat.card A ≤ k) →
      ∀ A : Subgroup (Equiv.Perm (Fin 7)), A ≤ S.map (MulAut.conj g).toMonoidHom →
        IsElemAbelian 2 A → (∀ a ∈ A, ∀ u ∈ U.map (pAct g : V7 ≃ₗ[ZMod 2] V7).toLinearMap,
          pAct a u = u) → Nat.card A ≤ k := by
    intro k hk A hAS hAel hAU
    have h1 := hk (A.map (MulAut.conj g⁻¹).toMonoidHom) ?_
      (CFSG.SectionRank.isElemAbelian_map hAel _) ?_
    · rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h1
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨s, hs, rfl⟩ := hAS ha
      have e : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom s) = s := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact hs
    · rintro _ ⟨a, ha, rfl⟩ u hu
      have h2 := hAU a ha (pAct g u) ⟨u, hu, rfl⟩
      have e : (MulAut.conj g⁻¹).toMonoidHom a = MulAut.conj g⁻¹ a := rfl
      rw [e]
      have h3 := pAct_conj_apply g⁻¹ a (pAct g u)
      rw [h2, pAct_inv_apply] at h3
      exact h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨u, hu, rfl⟩
    refine ⟨pAct s u, hinv s hs u hu, ?_⟩
    exact (pAct_conj_apply g s u).symm
  · rintro _ ⟨u, hu, rfl⟩
    change B0 (pAct g v) (pAct g u) = 0
    rw [B0_pAct]
    exact horth u hu
  · rintro ⟨u, hu, hgu⟩
    apply hnot
    have e : u = v := (pAct g).injective hgu
    rw [← e]
    exact hu
  · rcases hcases with h2 | ⟨h4, Y, hYK, hYv, hY3, hY9⟩
    · exact Or.inl (hA 2 h2)
    · refine Or.inr ⟨hA 4 h4, Y.map (MulAut.conj g).toMonoidHom, ?_, ?_,
        CFSG.SectionRank.isElemAbelian_map hY3 _, ?_⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact K.mul_mem (K.mul_mem hg (hYK hy)) (K.inv_mem hg)
      · rintro _ ⟨y, hy, rfl⟩
        change pAct (MulAut.conj g y) (pAct g v) = pAct g v
        rw [pAct_conj_apply, hYv y hy]
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hY9]

@[expose] def Uof (J : Finset (Fin 7)) : Submodule (ZMod 2) V7 where
  carrier := {u | ∀ i ∈ J, (u : Fin 7 → ZMod 2) i = 0}
  add_mem' := fun {a b} ha hb i hi => by
    show (a : Fin 7 → ZMod 2) i + (b : Fin 7 → ZMod 2) i = 0
    rw [ha i hi, hb i hi, add_zero]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c x hx i hi => by
    show c * (x : Fin 7 → ZMod 2) i = 0
    rw [hx i hi, mul_zero]

theorem mem_cenList (h : A7Raw) {J : Finset (Fin 7)} {a : Equiv.Perm (Fin 7)} (haS : a ∈ S0)
    (ha : ∀ u ∈ Uof J, pAct a u = u) : a ∈ cenList J := by
  rw [cenList, List.mem_filter, decide_eq_true_eq]
  refine ⟨(mem_S0_iff h a).1 haS, fun u hu hJ i => ?_⟩
  have h1 := ha ⟨u, hu⟩ hJ
  exact congrFun (congrArg Subtype.val h1) i

theorem card_le_cenList (h : A7Raw) {J : Finset (Fin 7)} {A : Subgroup (Equiv.Perm (Fin 7))}
    (hAS : A ≤ S0) (hA : ∀ a ∈ A, ∀ u ∈ Uof J, pAct a u = u) :
    Nat.card A ≤ (cenList J).length := by
  classical
  let φ : ↥A → ↥((cenList J).toFinset) := fun a =>
    ⟨a, List.mem_toFinset.2 (mem_cenList h (hAS a.2) (hA a a.2))⟩
  have hφ : Function.Injective φ := fun a b hab => Subtype.ext
    (congrArg (fun x : ↥((cenList J).toFinset) => (x : Equiv.Perm (Fin 7))) hab)
  have h1 := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_eq_fintype_card (α := ↥((cenList J).toFinset)), Fintype.card_coe] at h1
  exact h1.trans (List.toFinset_card_le _)

theorem mem_of_card_eq (h : A7Raw) {A : Subgroup (Equiv.Perm (Fin 7))} (hAS : A ≤ S0)
    (hA : ∀ a ∈ A, ∀ u ∈ Uof J1, pAct a u = u) (hcard : Nat.card A = 8) :
    ∀ x ∈ cenList J1, x ∈ A := by
  classical
  intro x hx
  by_contra hxA
  let φ : ↥A → ↥((cenList J1).toFinset.erase x) := fun a =>
    ⟨a, Finset.mem_erase.2 ⟨fun he => hxA (he ▸ a.2),
      List.mem_toFinset.2 (mem_cenList h (hAS a.2) (hA a a.2))⟩⟩
  have hφ : Function.Injective φ := fun a b hab => Subtype.ext
    (congrArg (fun y : ↥((cenList J1).toFinset.erase x) => (y : Equiv.Perm (Fin 7))) hab)
  have h1 := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_eq_fintype_card (α := ↥((cenList J1).toFinset.erase x)), Fintype.card_coe,
    Finset.card_erase_of_mem (List.mem_toFinset.2 hx), hcard] at h1
  have h2 := List.toFinset_card_le (cenList J1)
  have h3 := h.2.2.2.2.2.2.2.2.1
  omega

@[expose] def Y9 : Subgroup (Equiv.Perm (Fin 7)) := Subgroup.closure {y1, y2}

theorem mem_Y9_iff (h : A7Raw) (y : Equiv.Perm (Fin 7)) : y ∈ Y9 ↔ y ∈ Ylist := by
  obtain ⟨h1, hmul, hinv, -⟩ := h.2.2.2.2.2.2.2.2.2.2
  constructor
  · intro hy
    have hgen : ∀ x ∈ ({y1, y2} : Set (Equiv.Perm (Fin 7))), x ∈ Ylist := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      simp only [Ylist, List.mem_flatMap, List.mem_map, List.mem_range]
      rcases hx with rfl | rfl
      · exact ⟨1, by norm_num, 0, by norm_num, by simp⟩
      · exact ⟨0, by norm_num, 1, by norm_num, by simp⟩
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one => exact h1
    | mul a b _ _ ha hb => exact hmul a ha b hb
    | inv a _ ha => exact hinv a ha
  · intro hy
    simp only [Ylist, List.mem_flatMap, List.mem_map, List.mem_range] at hy
    obtain ⟨i, -, j, -, rfl⟩ := hy
    exact Y9.mul_mem (Y9.pow_mem (Subgroup.subset_closure (by simp)) i)
      (Y9.pow_mem (Subgroup.subset_closure (by simp)) j)

theorem Y9_facts (h : A7Raw) :
    Y9 ≤ alternatingGroup (Fin 7) ∧ (∀ y ∈ Y9, ∀ i, w1 (y⁻¹ i) = w1 i) ∧ IsElemAbelian 3 Y9 ∧
      Nat.card Y9 = 9 := by
  obtain ⟨-, -, -, hnd, hlen, hcomm, hall⟩ := h.2.2.2.2.2.2.2.2.2.2
  refine ⟨fun y hy => ?_, fun y hy => (hall y ((mem_Y9_iff h y).1 hy)).2.2,
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a ((mem_Y9_iff h a).1 a.2) b
      ((mem_Y9_iff h b).1 b.2))⟩⟩, fun y hy => (hall y ((mem_Y9_iff h y).1 hy)).1⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    exact (hall y ((mem_Y9_iff h y).1 hy)).2.1
  · rw [card_eq_length (mem_Y9_iff h) hnd, hlen]

theorem exists_concl_base (h : A7Raw) {K : Subgroup (Equiv.Perm (Fin 7))}
    (hAK : alternatingGroup (Fin 7) ≤ K) (v : V7) (hv0 : v ≠ 0)
    (hfix : ∀ s ∈ S0 ⊓ alternatingGroup (Fin 7), pAct s v = v) :
    ∃ U, Concl K (S0 ⊓ K) v U := by
  have hR3 := h.2.2.1
  obtain ⟨hU1, hU2, hU3, hc2, hc3, hc1, hnab, -⟩ := h.2.2.2
  have hv : (v : Fin 7 → ZMod 2) = 0 ∨ (v : Fin 7 → ZMod 2) = w1 ∨
      (v : Fin 7 → ZMod 2) = w2 ∨ (v : Fin 7 → ZMod 2) = w3 := by
    refine hR3 (v : Fin 7 → ZMod 2) v.2 fun s hs hsign i => ?_
    have h1 := hfix s ⟨(mem_S0_iff h s).2 hs, (Equiv.Perm.mem_alternatingGroup).2 hsign⟩
    exact (congrFun (congrArg Subtype.val h1) i)
  have hbase : ∀ (w : Fin 7 → ZMod 2) (J : Finset (Fin 7)), UFacts w J →
      (v : Fin 7 → ZMod 2) = w →
      (∀ s ∈ S0 ⊓ K, ∀ u ∈ Uof J, pAct s u ∈ Uof J) ∧ (∀ u ∈ Uof J, B0 v u = 0) ∧
        v ∉ Uof J := by
    intro w J hUF hvw
    obtain ⟨hJ, horth, i, hi, hwi⟩ := hUF
    refine ⟨fun s hs u hu j hj => ?_, fun u hu => ?_, fun hvU => hwi ?_⟩
    · rw [pAct_apply]
      exact hu _ (hJ s ((mem_S0_iff h s).1 hs.1) j hj)
    · rw [B0_apply, hvw]
      exact horth u u.2 hu
    · rw [← hvw]
      exact hvU i hi
  rcases hv with hv | hv | hv | hv
  · exact absurd (Subtype.ext hv) hv0
  ·
    obtain ⟨hinv, horth, hnot⟩ := hbase w1 J1 hU1 hv
    obtain ⟨hYA, hYv, hY3, hY9⟩ := Y9_facts h
    refine ⟨Uof J1, hinv, horth, hnot, Or.inr ⟨fun A hAS hAel hAU => ?_, Y9, hYA.trans hAK,
      fun y hy => Subtype.ext (funext fun i => ?_), hY3, hY9⟩⟩
    · have hAS0 : A ≤ S0 := hAS.trans inf_le_left
      have h8 := (card_le_cenList h hAS0 hAU).trans hc1
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hAel.2 x x.2)⟩
      obtain ⟨m, hm⟩ := hp.exists_card_eq
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      · rw [hm]
        calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 4 := by norm_num
      · exfalso
        have h2m : 8 ≤ Nat.card A := by
          rw [hm]
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
        have hall := mem_of_card_eq h hAS0 hAU (by omega)
        obtain ⟨a, ha, b, hb, hab⟩ := hnab
        have := hAel.1.is_comm.comm ⟨a, hall a ha⟩ ⟨b, hall b hb⟩
        exact hab (congrArg Subtype.val this)
    · rw [pAct_apply, hv]
      exact hYv y hy i
  ·
    obtain ⟨hinv, horth, hnot⟩ := hbase w2 J2 hU2 hv
    exact ⟨Uof J2, hinv, horth, hnot, Or.inl fun A hAS _ hAU =>
      (card_le_cenList h (hAS.trans inf_le_left) hAU).trans hc2⟩
  ·
    obtain ⟨hinv, horth, hnot⟩ := hbase w3 J3 hU3 hv
    exact ⟨Uof J3, hinv, horth, hnot, Or.inl fun A hAS _ hAU =>
      (card_le_cenList h (hAS.trans inf_le_left) hAU).trans hc3⟩

theorem exists_concl (h : A7Raw) {K : Subgroup (Equiv.Perm (Fin 7))}
    (hK : K = alternatingGroup (Fin 7) ∨ K = ⊤) {S : Subgroup (Equiv.Perm (Fin 7))}
    (hS : IsSylowTwoOf S K) (v : V7) (hv0 : v ≠ 0) (hSv : ∀ s ∈ S, pAct s v = v) :
    ∃ U, Concl K S v U := by
  have hAK : alternatingGroup (Fin 7) ≤ K := by
    rcases hK with rfl | rfl
    · exact le_rfl
    · exact le_top
  have hS0K : IsSylowTwoOf (S0 ⊓ K) K := by
    rcases hK with rfl | rfl
    · exact isSylowTwoOf_S0_inf h
    · rw [inf_top_eq]
      exact isSylowTwoOf_S0 h
  obtain ⟨g, hgK, hSg⟩ := hS0K.exists_conj hS
  have h3 : pAct g (pAct g⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hv₀ : pAct g⁻¹ v ≠ 0 := fun h0 => hv0 (by rw [← h3, h0, map_zero])
  have hfix : ∀ s ∈ S0 ⊓ alternatingGroup (Fin 7), pAct s (pAct g⁻¹ v) = pAct g⁻¹ v := by
    intro s hs
    have hsS : MulAut.conj g s ∈ S := by
      rw [hSg]
      exact ⟨s, ⟨hs.1, hAK hs.2⟩, rfl⟩
    have h1 := hSv _ hsS
    have h2 := pAct_conj_apply g s (pAct g⁻¹ v)
    rw [h3, h1] at h2
    have h4 := congrArg (pAct g⁻¹) h2
    rw [pAct_inv_apply] at h4
    exact h4.symm
  obtain ⟨U₀, hU₀⟩ := exists_concl_base h hAK _ hv₀ hfix
  have hc := hU₀.conj hgK
  rw [h3, ← hSg] at hc
  exact ⟨_, hc⟩

end A7Mod

end CFSG.Quasithin.H13
