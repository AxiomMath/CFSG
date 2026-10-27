module

public import CFSG.Quasithin.H13.L32AH63a

public section

namespace CFSG.Quasithin.H6

open scoped MatrixGroups

@[reducible] def borelActOn {M : Type} [AddGroup M] (ρ : Γ →* AddMonoid.End M)
    (W : AddSubgroup M) (hW : ∀ g : Γ, ∀ w ∈ W, ρ g w ∈ W) : MulAction ↥borel ↥W where
  smul t w := ⟨ρ t.1 w.1, hW t.1 w.1 w.2⟩
  one_smul w := Subtype.ext (by
    show ρ ((1 : ↥borel) : Γ) w.1 = w.1
    rw [Subgroup.coe_one, map_one]
    rfl)
  mul_smul s t w := Subtype.ext (by
    show ρ ((s * t : ↥borel) : Γ) w.1 = ρ s.1 (ρ t.1 w.1)
    rw [Subgroup.coe_mul, map_mul]
    rfl)

theorem isPGroup_borel : IsPGroup 2 ↥borel :=
  IsPGroup.of_card (n := 3) (by rw [card_borel]; norm_num)

theorem exists_fix_borel {M : Type} [AddGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M)
    (h2 : ∀ m : M, m + m = 0) (W : AddSubgroup M) (hW : ∀ g : Γ, ∀ w ∈ W, ρ g w ∈ W)
    {w₀ : M} (hw₀ : w₀ ∈ W) (hw₀0 : w₀ ≠ 0) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ t ∈ borel, ρ t w = w := by
  let _ := borelActOn ρ W hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : addOrderOf (⟨w₀, hw₀⟩ : ↥W) = 2 :=
    addOrderOf_eq_prime (Subtype.ext (show 2 • w₀ = 0 by rw [two_nsmul]; exact h2 w₀))
      (fun h => hw₀0 (congrArg Subtype.val h))
  have hdvd : 2 ∣ Nat.card ↥W := hord ▸ addOrderOf_dvd_natCard _
  have h0 : (0 : ↥W) ∈ MulAction.fixedPoints ↥borel ↥W := fun t =>
    Subtype.ext (show ρ t.1 0 = 0 from map_zero _)
  obtain ⟨b, hb, hne⟩ :=
    isPGroup_borel.exists_fixed_point_of_prime_dvd_card_of_fixed_point (↥W) hdvd h0
  refine ⟨b.1, b.2, fun h => hne (Subtype.ext h.symm), fun t ht => ?_⟩
  exact congrArg Subtype.val (hb ⟨t, ht⟩)

@[expose] def w0g : Γ := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩

theorem w0g_E13 : w0g • stE13 = stE31 := by decide

theorem st_top_of_E13 (W : AddSubgroup St) (hW : ∀ g : Γ, ∀ w ∈ W, ρSt g w ∈ W)
    (h : stE13 ∈ W) : W = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [st_free x]
  refine sum_mem fun t _ => ?_
  have ht : (t : Γ) • stE31 ∈ W := by
    rw [← w0g_E13, ← mul_smul]
    exact hW _ _ h
  unfold zsm
  split_ifs
  · exact zero_mem _
  · exact ht

theorem st_closure_E13 : AddSubgroup.closure (Set.range fun g : Γ => ρSt g stE13) = ⊤ :=
  st_top_of_E13 _ (fun g w hw => by
    refine AddSubgroup.closure_induction (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_)
      (fun y _ hy => ?_) hw
    · obtain ⟨h, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨g * h, ?_⟩
      show (g * h) • stE13 = g • h • stE13
      rw [mul_smul]
    · rw [map_zero]
      exact zero_mem _
    · rw [map_add]
      exact add_mem hy hz
    · rw [map_neg]
      exact neg_mem hy)
    (AddSubgroup.subset_closure ⟨1, show ρSt 1 stE13 = stE13 by rw [map_one]; rfl⟩)

theorem st_irred (W : AddSubgroup St) (hW : ∀ g : Γ, ∀ w ∈ W, ρSt g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  rcases W.bot_or_exists_ne_zero with hb | ⟨w₀, hw₀, hw₀0⟩
  · exact Or.inl hb
  obtain ⟨w, hw, hw0, hfix⟩ := exists_fix_borel ρSt st_add_self W hW hw₀ hw₀0
  have e := st_fix_bel_eq w hw0 fun i => hfix _ (bel_mem i)
  exact Or.inr (st_top_of_E13 W hW (e ▸ hw))

@[expose] def coreU2 : Core := ⟨![0, 0, 1, 1, 0, 0, 0, 0], by decide⟩

@[expose] def coreU4 : Core := ⟨![0, 0, 0, 0, 1, 1, 1, 1], by decide⟩

theorem core_add_self : ∀ c : Core, c + c = 0 := by decide +kernel

@[expose] def kappa : Core →+ V3 := epsHom.comp coreSub.subtype

theorem kappa_smul (g : Γ) (c : Core) : kappa (ρCore g c) = ρV g (kappa c) :=
  epsF_actF g c.1

theorem kappa_u2 : kappa coreU2 = ![1, 0, 0] := by decide

theorem coreU2_ne : coreU2 ≠ 0 := by decide

theorem kappa_surjective : Function.Surjective kappa := by
  have h : ∀ v : V3, ∃ c : Core, epsF c.1 = v := by decide +kernel
  exact h

theorem core_fix_bel : ∀ c : Core, (∀ i : Fin 8, bel i • c = c) →
    c = 0 ∨ c = coreU2 ∨ c = coreU4 ∨ c = coreU2 + coreU4 := by
  decide +kernel

@[expose] def coreGMat : Fin 8 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 1, 0; 0, 0, 1],
    !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![1, 0, 0; 0, 0, 1; 1, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0],
    !![1, 0, 0; 1, 1, 0; 1, 1, 1], !![0, 1, 0; 1, 0, 0; 1, 0, 1]]

@[expose] def coreG (i : Fin 8) : Γ := ⟨coreGMat i, by revert i; decide⟩

@[expose] def coreTerm (c : Core) (i : Fin 8) : Core := zsm (c.1 i) (coreG i • coreU2)

theorem core_decomp : ∀ c : Core, c = coreTerm c 2 + coreTerm c 3 + coreTerm c 4 +
    coreTerm c 5 + coreTerm c 6 + coreTerm c 7 := by
  decide +kernel

theorem core_top_of_u2 (W : AddSubgroup Core) (hW : ∀ g : Γ, ∀ w ∈ W, ρCore g w ∈ W)
    (h : coreU2 ∈ W) : W = ⊤ := by
  refine eq_top_iff.mpr fun c _ => ?_
  have ht : ∀ i, coreTerm c i ∈ W := fun i => by
    unfold coreTerm zsm
    split_ifs
    · exact zero_mem _
    · exact hW _ _ h
  rw [core_decomp c]
  exact add_mem (add_mem (add_mem (add_mem (add_mem (ht 2) (ht 3)) (ht 4)) (ht 5)) (ht 6)) (ht 7)

@[expose] def lineRepMat : Fin 7 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0],
    !![0, 1, 0; 0, 1, 1; 1, 0, 0], !![0, 1, 0; 1, 0, 0; 0, 1, 1], !![0, 1, 0; 1, 0, 0; 1, 0, 1],
    !![0, 1, 0; 1, 0, 0; 1, 1, 1]]

@[expose] def lineRep (k : Fin 7) : Γ := ⟨lineRepMat k, by revert k; decide⟩

theorem ker_kappa_cases : ∀ c : Core, epsF c.1 = 0 →
    c = 0 ∨ ∃ k : Fin 7, c = lineRep k • coreU4 := by
  decide +kernel

theorem coreU2_eq : coreU2 = llA • ((coreU2 + coreU4) + llA • (coreU2 + coreU4)) := by decide

theorem exists_smul_eq_e1 : ∀ v : V3, v ≠ 0 → ∃ g : Γ, g • v = ![1, 0, 0] := by decide +kernel

theorem core_sub (W : AddSubgroup Core) (hW : ∀ g : Γ, ∀ w ∈ W, ρCore g w ∈ W) :
    W = ⊥ ∨ W = kappa.ker ∨ W = ⊤ := by
  rcases W.bot_or_exists_ne_zero with hb | ⟨w₀, hw₀, hw₀0⟩
  · exact Or.inl hb
  right
  have hW' : ∀ g : Γ, ∀ w ∈ W, g • w ∈ W := hW
  obtain ⟨w, hw, hw0, hfix⟩ := exists_fix_borel ρCore core_add_self W hW hw₀ hw₀0
  have hu2 : coreU2 ∈ W → W = ⊤ := core_top_of_u2 W hW
  rcases core_fix_bel w (fun i => hfix _ (bel_mem i)) with h | h | h | h
  · exact absurd h hw0
  · exact Or.inr (hu2 (h ▸ hw))
  · have hker : kappa.ker ≤ W := fun c hc => by
      rcases ker_kappa_cases c hc with h0 | ⟨k, rfl⟩
      · rw [h0]
        exact zero_mem _
      · exact hW' _ _ (h ▸ hw)
    by_cases hle : W ≤ kappa.ker
    · exact Or.inl (le_antisymm hle hker)
    · right
      obtain ⟨c, hc, hcκ⟩ := IsConcreteLE.not_le_iff_exists.mp hle
      obtain ⟨g, hg⟩ := exists_smul_eq_e1 (kappa c) fun h0 => hcκ (AddMonoidHom.mem_ker.mpr h0)
      apply hu2
      have h1 : ρCore g c - coreU2 ∈ W := hker (by
        rw [AddMonoidHom.mem_ker, map_sub, kappa_smul, kappa_u2]
        exact sub_eq_zero.mpr hg)
      convert sub_mem (hW g c hc) h1 using 1
      exact (sub_sub_cancel _ _).symm
  · exact Or.inr (hu2 (by
      rw [coreU2_eq]
      exact hW' _ _ (add_mem (h ▸ hw) (hW' _ _ (h ▸ hw)))))

theorem prod_sub (W : AddSubgroup (Core × St))
    (hW : ∀ g : Γ, ∀ x ∈ W, prodRep ρCore ρSt g x ∈ W) :
    ∃ W₁ : AddSubgroup Core, ∃ W₂ : AddSubgroup St, W = W₁.prod W₂ ∧
      (W₁ = ⊥ ∨ W₁ = kappa.ker ∨ W₁ = ⊤) ∧ (W₂ = ⊥ ∨ W₂ = ⊤) := by
  have hW₁ : ∀ g : Γ, ∀ c ∈ W.comap (AddMonoidHom.inl Core St),
      ρCore g c ∈ W.comap (AddMonoidHom.inl Core St) := fun g c hc => by
    have h := hW g _ (AddSubgroup.mem_comap.mp hc)
    rw [prodRep_apply] at h
    rw [AddSubgroup.mem_comap]
    convert h using 1
    exact Prod.ext rfl (map_zero _).symm
  have hW₂ : ∀ g : Γ, ∀ s ∈ W.comap (AddMonoidHom.inr Core St),
      ρSt g s ∈ W.comap (AddMonoidHom.inr Core St) := fun g s hs => by
    have h := hW g _ (AddSubgroup.mem_comap.mp hs)
    rw [prodRep_apply] at h
    rw [AddSubgroup.mem_comap]
    convert h using 1
    exact Prod.ext (map_zero _).symm rfl
  have hP₂ : ∀ g : Γ, ∀ s ∈ W.map (AddMonoidHom.snd Core St),
      ρSt g s ∈ W.map (AddMonoidHom.snd Core St) := fun g s hs => by
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hs
    exact AddSubgroup.mem_map.mpr ⟨_, hW g x hx, rfl⟩
  have hcl : ∀ x ∈ W, (x.1, (0 : St)) ∈ W ∧ ((0 : Core), x.2) ∈ W := by
    rcases st_irred _ hW₂ with h2 | h2
    · have hinj : ∀ x ∈ W, ∀ y ∈ W, x.1 = y.1 → x = y := fun x hx y hy e => by
        have h0 : x.2 - y.2 ∈ W.comap (AddMonoidHom.inr Core St) := by
          rw [AddSubgroup.mem_comap]
          convert sub_mem hx hy using 1
          exact Prod.ext (by simp [e]) rfl
        rw [h2, AddSubgroup.mem_bot] at h0
        exact Prod.ext e (sub_eq_zero.mp h0)
      rcases st_irred _ hP₂ with h3 | h3
      · intro x hx
        have hx2 : x.2 = 0 := by
          have : x.2 ∈ W.map (AddMonoidHom.snd Core St) := AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩
          rwa [h3, AddSubgroup.mem_bot] at this
        refine ⟨?_, ?_⟩
        · convert hx using 1
          exact Prod.ext rfl hx2.symm
        · rw [hx2]
          exact zero_mem _
      · exfalso
        have h1 : Nat.card St ≤ Nat.card ↥W := by
          refine Nat.card_le_card_of_surjective (fun x : ↥W => x.1.2) fun s => ?_
          have hs : s ∈ W.map (AddMonoidHom.snd Core St) := h3 ▸ AddSubgroup.mem_top s
          obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hs
          exact ⟨⟨x, hx⟩, rfl⟩
        have h1' : Nat.card ↥W ≤ Nat.card Core :=
          Nat.card_le_card_of_injective (fun x : ↥W => x.1.1) fun x y e =>
            Subtype.ext (hinj x x.2 y y.2 e)
        rw [card_st] at h1
        rw [card_core] at h1'
        omega
    · intro x hx
      have h0 : ((0 : Core), x.2) ∈ W :=
        AddSubgroup.mem_comap.mp (h2 ▸ AddSubgroup.mem_top x.2 :
          x.2 ∈ W.comap (AddMonoidHom.inr Core St))
      refine ⟨?_, h0⟩
      convert sub_mem hx h0 using 1
      exact Prod.ext (sub_zero _).symm (sub_self _).symm
  refine ⟨W.comap (AddMonoidHom.inl Core St), W.comap (AddMonoidHom.inr Core St), ?_,
    core_sub _ hW₁, st_irred _ hW₂⟩
  ext x
  rw [AddSubgroup.mem_prod, AddSubgroup.mem_comap, AddSubgroup.mem_comap]
  constructor
  · intro hx
    exact hcl x hx
  · rintro ⟨h1, h2⟩
    convert add_mem h1 h2 using 1
    exact Prod.ext (add_zero _).symm (zero_add _).symm

end CFSG.Quasithin.H6
