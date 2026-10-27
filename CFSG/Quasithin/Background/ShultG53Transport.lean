module

public import CFSG.Quasithin.Background.ShultG53Parts
public import CFSG.Quasithin.Background.ShultG53Part1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 Equiv

variable {V₁ : Md ↥(alternatingGroup (Fin 6))} {k : Fin 2}

@[expose] def Theta (e : V₁.carrier ≃+ V4) : (V₁.carrier → ZMod 2) ≃+ Fn where
  toFun u := fun x => u (e.symm x)
  invFun v := fun m => v (e m)
  left_inv u := by funext m; simp
  right_inv v := by funext x; simp
  map_add' _ _ := rfl

theorem Theta_permAct (e : V₁.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m))
    (g : ↥(alternatingGroup (Fin 6))) (u : V₁.carrier → ZMod 2) :
    permAct (Mk k) g (Theta e u) = Theta e (permAct V₁ g u) := by
  funext x
  show u (e.symm (ρk k g⁻¹ x)) = u (V₁.ρ g⁻¹ (e.symm x))
  congr 1
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

theorem Theta_permAct' (e : V₁.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m)) :
    ∀ (g : ↥(alternatingGroup (Fin 6))) (u : V₁.carrier → ZMod 2),
      permAct (Mk k) g (Theta e u) = Theta e (permAct V₁ g u) := Theta_permAct e he

theorem Theta_permCore (e : V₁.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m)) :
    (Theta e).mapAddSubgroup (permCore V₁) = permCore (Mk k) := by
  ext u'
  rw [mem_mapAddSubgroup (Theta e) (Theta_permAct' e he)]
  rw [mem_permCore_md, mem_permCore]
  have hw : weightHom V₁ ((Theta e).symm u') = ∑ w : V4, u' w := by
    show ∑ᶠ m, u' (e m) = _
    exact (finsum_comp_equiv e.toEquiv (f := u')).trans (finsum_eq_sum_of_fintype u')
  rw [hw]
  show (u' (e 0) = 0 ∧ _) ↔ _
  rw [map_zero]

section Maps

variable (e : V₁.carrier ≃+ V4)

@[expose] def lmapE (l : AddSubgroup V₁.carrier) : AddSubgroup V4 := l.map e.toAddMonoidHom

theorem mem_lmapE (l : AddSubgroup V₁.carrier) (x : V4) : x ∈ lmapE e l ↔ e.symm x ∈ l :=
  AddSubgroup.mem_map_equiv

theorem card_lmapE (l : AddSubgroup V₁.carrier) : Nat.card (lmapE e l) = Nat.card l :=
  Nat.card_congr (e.addSubgroupMap l).toEquiv.symm

theorem Theta_lineCompl (l : AddSubgroup V₁.carrier) :
    Theta e (lineCompl V₁ l) = lineCompl (Mk k) (lmapE e l) := by
  funext x
  show lineCompl V₁ l (e.symm x) = lineCompl (Mk k) (lmapE e l) x
  unfold lineCompl
  beta_reduce
  have hiff : (e.symm x = 0 ∨ e.symm x ∈ l) ↔ (x = 0 ∨ x ∈ lmapE e l) :=
    or_congr (map_eq_zero_iff e.symm e.symm.injective) (mem_lmapE e l x).symm
  by_cases h : e.symm x = 0 ∨ e.symm x ∈ l
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

end Maps

section Parts

variable (e : V₁.carrier ≃+ V4)
  (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m))

include he

theorem Theta_jradPow (n : ℕ) :
    (Theta e).mapAddSubgroup (jradPow (permAct V₁) n (permCore V₁)) =
      jradPow (permAct (Mk k)) n (permCore (Mk k)) := by
  have h := jradPow_map (Theta e) (Theta_permAct' e he) n (N := permCore V₁)
  rw [Theta_permCore e he] at h
  exact h.symm

theorem Theta_jradPow_eq (n : ℕ) (hn : n ≤ 5) :
    (Theta e).mapAddSubgroup (jradPow (permAct V₁) n (permCore V₁)) = Nk k n :=
  (Theta_jradPow e he n).trans (jradPow_Mk k n hn)

theorem mem_jradPow_iff (n : ℕ) (hn : n ≤ 5) (u : V₁.carrier → ZMod 2) :
    u ∈ jradPow (permAct V₁) n (permCore V₁) ↔ Theta e u ∈ Nk k n := by
  rw [← Theta_jradPow_eq e he n hn, mem_mapAddSubgroup (Theta e) (Theta_permAct' e he)]
  simp

theorem part2_of_iso : Part2 V₁ := by
  have hpow := Theta_jradPow_eq e he
  refine ⟨?_, fun n hn => ?_⟩
  · exact (Theta e).mapAddSubgroup.injective
      ((hpow 5 le_rfl).trans ((Nk_five k).trans (OrderIso.map_bot _).symm))
  · have h := (chain_isTop k n hn).isMaxInvSub
    rw [← hpow n hn.le, ← hpow (n + 1) hn] at h
    exact (isMaxInvSub_map_iff (Theta e) (Theta_permAct' e he)).mp h

variable (B : LinearMap.BilinForm (ZMod 2) V₁.carrier)
  (hB : ∀ x y : V4, B (e.symm x) (e.symm y) = B0 x y)

include hB

theorem lmapE_mem (l : AddSubgroup V₁.carrier) (hl : l ∈ singLines V₁ B) :
    lmapE e l ∈ singLines (Mk k) B0form := by
  refine ⟨(card_lmapE e l).trans hl.1, fun x hx y hy => ?_⟩
  rw [B0form_apply, ← hB]
  exact hl.2 _ ((mem_lmapE e l x).mp hx) _ ((mem_lmapE e l y).mp hy)

theorem exists_lmapE_preimage (l' : AddSubgroup V4) (hl' : l' ∈ singLines (Mk k) B0form) :
    ∃ l ∈ singLines V₁ B, lmapE e l = l' := by
  let l : AddSubgroup V₁.carrier := l'.map e.symm.toAddMonoidHom
  have hmem : ∀ m, m ∈ l ↔ e m ∈ l' := fun m => AddSubgroup.mem_map_equiv
  refine ⟨l, ⟨?_, fun m hm m' hm' => ?_⟩, ?_⟩
  · exact (Nat.card_congr (e.symm.addSubgroupMap l').toEquiv.symm).trans hl'.1
  · have h := hl'.2 _ ((hmem m).mp hm) _ ((hmem m').mp hm')
    rw [B0form_apply, ← hB] at h
    simpa using h
  · ext x
    rw [mem_lmapE, hmem]
    simp

theorem part3a_of_iso :
    jradPow (permAct V₁) 2 (permCore V₁) =
      AddSubgroup.closure {u | ∃ l ∈ singLines V₁ B, u = lineCompl V₁ l} := by
  apply (Theta e).mapAddSubgroup.injective
  refine (Theta_jradPow_eq e he 2 (by norm_num)).trans ?_
  have h2 : Nk k 2 = AddSubgroup.closure
      {u | ∃ l ∈ singLines (Mk k) B0form, u = lineCompl (Mk k) l} :=
    (jradPow_Mk k 2 (by norm_num)).symm.trans (jradPow_two_eq_closure k)
  refine h2.trans ?_
  show _ = AddSubgroup.map (Theta e).toAddMonoidHom _
  rw [AddMonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨l', hl', rfl⟩
    obtain ⟨l, hl, rfl⟩ := exists_lmapE_preimage e he B hB l' hl'
    exact ⟨lineCompl V₁ l, ⟨l, hl, rfl⟩, Theta_lineCompl e l⟩
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨lmapE e l, lmapE_mem e he B hB l hl, Theta_lineCompl (k := k) e l⟩

theorem Theta_perpCompl (x : V₁.carrier) :
    Theta e (perpCompl V₁ B x) = perpCompl (Mk k) B0form (e x) := by
  funext y
  show perpCompl V₁ B x (e.symm y) = perpCompl (Mk k) B0form (e x) y
  unfold perpCompl
  beta_reduce
  have hiff : (e.symm y ≠ 0 ∧ B (e.symm y) x ≠ 0) ↔ (y ≠ 0 ∧ B0form y (e x) ≠ 0) := by
    rw [B0form_apply, ← hB y (e x), e.symm_apply_apply]
    exact and_congr (not_congr (map_eq_zero_iff e.symm e.symm.injective)) Iff.rfl
  by_cases h : e.symm y ≠ 0 ∧ B (e.symm y) x ≠ 0
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem part4_of_iso : Part4 V₁ B := by
  obtain ⟨hset, f, hf⟩ := part4_Mk k
  refine ⟨?_, ?_⟩
  · ext u
    have h1 : u ∈ jradPow (permAct V₁) 4 (permCore V₁) ↔
        Theta e u ∈ jradPow (permAct (Mk k)) 4 (permCore (Mk k)) := by
      rw [mem_jradPow_iff e he 4 (by norm_num), ← jradPow_Mk k 4 (by norm_num)]
    have h2 := Set.ext_iff.mp hset (Theta e u)
    refine h1.trans (h2.trans ?_)
    constructor
    · rintro (⟨y, hy, hu⟩ | hu)
      · left
        refine ⟨e.symm y, ?_, ?_⟩
        · intro h0
          apply hy
          rw [← e.apply_symm_apply y, h0, map_zero]
        · apply (Theta e).injective
          rw [Theta_perpCompl e he B hB, e.apply_symm_apply]
          exact hu
      · right
        rw [Set.mem_singleton_iff] at hu ⊢
        apply (Theta e).injective
        rw [hu]
        exact (map_zero _).symm
    · rintro (⟨x, hx, hu⟩ | hu)
      · left
        refine ⟨e x, ?_, ?_⟩
        · intro h0
          apply hx
          exact e.injective (h0.trans (map_zero e).symm)
        · rw [hu, Theta_perpCompl e he B hB]
      · right
        rw [Set.mem_singleton_iff] at hu ⊢
        rw [hu]
        exact map_zero _
  · let T : ↥(jradPow (permAct V₁) 4 (permCore V₁)) ≃+
        ↥(jradPow (permAct (Mk k)) 4 (permCore (Mk k))) :=
      (AddEquiv.addSubgroupMap (Theta e) _).trans
        (AddEquiv.addSubgroupCongr (Theta_jradPow e he 4))
    have hT : ∀ u, ((T u : ↥(jradPow (permAct (Mk k)) 4 (permCore (Mk k)))) : Fn) =
        Theta e (u : V₁.carrier → ZMod 2) := fun u => rfl
    refine ⟨T.trans (f.trans e.symm), ?_⟩
    intro g u u' hu
    show e.symm (f (T u')) = V₁.ρ g (e.symm (f (T u)))
    have h1 : permAct (Mk k) g ↑(T u) = ↑(T u') :=
      (congrArg (permAct (Mk k) g) (hT u)).trans ((Theta_permAct e he g _).trans
        ((congrArg (Theta e) hu).trans (hT u').symm))
    have h2 := hf g (T u) (T u') h1
    rw [h2]
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]

end Parts

end CFSG.Quasithin.ShultG53
