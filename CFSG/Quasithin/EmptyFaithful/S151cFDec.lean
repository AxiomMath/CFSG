module

public import CFSG.Quasithin.EmptyFaithful.S151cUStar
public import CFSG.Quasithin.EmptyFaithful.S151cDich

public section

namespace CFSG.Quasithin

open CFSG.Open

section FDec151c

variable {W : Type*} [CommGroup W] [Finite W] {Y : Subgroup (MulAut W)} {s : ℕ}
  {Pi : Fin s → Subgroup (MulAut W)}

structure FDec (Y : Subgroup (MulAut W)) (Pi : Fin s → Subgroup (MulAut W)) : Prop where
  mem : ∀ i, Pi i ∈ Xk Y 1
  vindep : iSupIndep fun i => commV (Pi i)
  vsup : ⨆ i, commV (Pi i) = ⊤
  triv : ∀ i j, i ≠ j → commV (Pi i) ≤ fixV (Pi j)

omit [Finite W] in
theorem FDec.rk_eq (d : FDec Y Pi) (i : Fin s) : rk (commV (Pi i)) = 2 := by
  simpa using (d.mem i).2.2

omit [Finite W] in
theorem FDec.card_eq (d : FDec Y Pi) (i : Fin s) : Nat.card (Pi i) = 3 := by
  simpa using (d.mem i).2.1

omit [Finite W] in
theorem FDec.commV_ne_bot (d : FDec Y Pi) (i : Fin s) : commV (Pi i) ≠ ⊥ := by
  intro h
  have := d.rk_eq i
  rw [h, rk_bot] at this
  omega

omit [Finite W] in
theorem FDec.injective (d : FDec Y Pi) : Function.Injective Pi := by
  intro i j hij
  by_contra hne
  have hd := d.vindep.pairwiseDisjoint hne
  have h1 : commV (Pi i) ⊓ commV (Pi j) = ⊥ := disjoint_iff.mp hd
  rw [← hij, inf_idem] at h1
  exact d.commV_ne_bot i h1

@[expose] def FDec.compl (Pi : Fin s → Subgroup (MulAut W)) (i : Fin s) : Subgroup W :=
  ⨆ (j : Fin s) (_ : j ≠ i), commV (Pi j)

omit [Finite W] in
theorem FDec.inf_compl (d : FDec Y Pi) (i : Fin s) : commV (Pi i) ⊓ FDec.compl Pi i = ⊥ :=
  disjoint_iff.mp (d.vindep i)

omit [Finite W] in
theorem FDec.sup_compl (d : FDec Y Pi) (i : Fin s) : commV (Pi i) ⊔ FDec.compl Pi i = ⊤ := by
  rw [← d.vsup]
  exact (iSup_split_single (fun j => commV (Pi j)) i).symm

omit [Finite W] in
theorem FDec.fixes_compl (d : FDec Y Pi) (i : Fin s) {p : MulAut W} (hp : p ∈ Pi i) {b : W}
    (hb : b ∈ FDec.compl Pi i) : p b = b := by
  have hle : FDec.compl Pi i ≤ fixV (Pi i) := by
    unfold FDec.compl
    refine iSup₂_le fun j hj => ?_
    exact d.triv j i hj
  exact hle hb p hp

theorem FDec.inf_fixV (hV : ∀ v : W, v ^ 2 = 1) (d : FDec Y Pi) (i : Fin s) :
    commV (Pi i) ⊓ fixV (Pi i) = ⊥ :=
  (Xk_decomp hV (d.mem i)).2

theorem FDec.le_or_le_compl (hV : ∀ v : W, v ^ 2 = 1) (d : FDec Y Pi) (i : Fin s)
    {N : Subgroup W} (hN : ∀ p ∈ Pi i, ∀ n ∈ N, p n ∈ N) :
    commV (Pi i) ≤ N ∨ N ≤ FDec.compl Pi i := by
  by_cases hU : commV (Pi i) ≤ N
  · exact Or.inl hU
  · refine Or.inr ?_
    have hB : N ⊓ commV (Pi i) = ⊥ := by
      by_contra hne
      apply hU
      have hinv : ∀ g ∈ Pi i, ∀ f ∈ N ⊓ commV (Pi i), g f ∈ N ⊓ commV (Pi i) := by
        intro g hg f hf
        refine ⟨hN g hg f hf.1, ?_⟩
        have h1 : g f * f⁻¹ ∈ commV (Pi i) := Subgroup.subset_closure ⟨g, hg, f, rfl⟩
        have h2 : g f = (g f * f⁻¹) * f := by group
        rw [h2]
        exact (commV (Pi i)).mul_mem h1 hf.2
      have := Xk_irreducible hV (Or.inl rfl) (d.mem i) hinv inf_le_right hne
      rw [← this]
      exact inf_le_left
    intro n hn
    have hn' : n ∈ commV (Pi i) ⊔ FDec.compl Pi i := by rw [d.sup_compl i]; exact Subgroup.mem_top n
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hn'
    have ha1 : a = 1 := by
      have hfix : a ∈ fixV (Pi i) := by
        intro p hp
        have h1 : p (a * b) * (a * b)⁻¹ ∈ N := N.mul_mem (hN p hp _ hn) (N.inv_mem hn)
        have h2 : p (a * b) * (a * b)⁻¹ = p a * a⁻¹ := by
          rw [map_mul, d.fixes_compl i hp hb]
          group
        have h3 : p a * a⁻¹ ∈ commV (Pi i) := Subgroup.subset_closure ⟨p, hp, a, rfl⟩
        rw [h2] at h1
        have h4 : p a * a⁻¹ ∈ N ⊓ commV (Pi i) := ⟨h1, h3⟩
        rw [hB, Subgroup.mem_bot, mul_inv_eq_one] at h4
        exact h4
      have : a ∈ commV (Pi i) ⊓ fixV (Pi i) := ⟨ha, hfix⟩
      rw [d.inf_fixV hV i, Subgroup.mem_bot] at this
      exact this
    rw [ha1, one_mul]
    exact hb

omit [Finite W] in
theorem FDec.eq_one_of_mem (d : FDec Y Pi) (T' : Finset (Fin s)) {z : W}
    (hz : z ∈ ⨆ k ∈ T', commV (Pi k)) (hc : ∀ k ∈ T', z ∈ FDec.compl Pi k) : z = 1 := by
  classical
  induction T' using Finset.induction_on generalizing z with
  | empty => simpa using hz
  | insert a T'' ha ih =>
    have hle : (⨆ k ∈ insert a T'', commV (Pi k)) ≤
        commV (Pi a) ⊔ ⨆ k ∈ T'', commV (Pi k) := by
      refine iSup₂_le fun k hk => ?_
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂ (f := fun k (_ : k ∈ T'') => commV (Pi k)) k hk')
    obtain ⟨u, hu, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hle hz)
    have hbc : b ∈ FDec.compl Pi a := by
      have : (⨆ k ∈ T'', commV (Pi k)) ≤ FDec.compl Pi a := by
        refine iSup₂_le fun k hk => ?_
        have hka : k ≠ a := fun e => ha (e ▸ hk)
        exact le_iSup₂ (f := fun j (_ : j ≠ a) => commV (Pi j)) k hka
      exact this hb
    have hzc : u * b ∈ FDec.compl Pi a := hc a (Finset.mem_insert_self a T'')
    have hu1 : u = 1 := by
      have h1 : u ∈ FDec.compl Pi a := by
        have := (FDec.compl Pi a).mul_mem hzc ((FDec.compl Pi a).inv_mem hbc)
        simpa using this
      have : u ∈ commV (Pi a) ⊓ FDec.compl Pi a := ⟨hu, h1⟩
      rw [d.inf_compl a, Subgroup.mem_bot] at this
      exact this
    subst hu1
    simp only [one_mul] at hz hc ⊢
    exact ih hb (fun k hk => hc k (Finset.mem_insert_of_mem hk))

theorem FDec.closure_eq_top (hV : ∀ v : W, v ^ 2 = 1) (d : FDec Y Pi) {H : Subgroup (MulAut W)}
    (hH : IsPGroup 2 H) (hperm : ∀ τ ∈ H, ∀ i, ∃ j, conjBy τ (Pi i) = Pi j) :
    Subgroup.closure {x | ∃ p ∈ (⨆ i, Pi i), ∃ z ∈ fixV H, p z = x} = ⊤ := by
  classical
  set F : Subgroup (MulAut W) := ⨆ i, Pi i with hFdef
  set N : Subgroup W := Subgroup.closure {x | ∃ p ∈ F, ∃ z ∈ fixV H, p z = x} with hNdef
  have hPiF : ∀ i, Pi i ≤ F := fun i => le_iSup Pi i
  have hNF : ∀ p ∈ F, ∀ n ∈ N, p n ∈ N := by
    intro p hp n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q, hq, z, hz, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨p * q, F.mul_mem hp hq, z, hz, rfl⟩
    | one => rw [map_one]; exact N.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact N.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact N.inv_mem hx
  have hconjF : ∀ τ ∈ H, ∀ p ∈ F, τ * p * τ⁻¹ ∈ F := by
    intro τ hτ p hp
    have hle : F ≤ F.comap (MulAut.conj τ).toMonoidHom := by
      refine iSup_le fun i q hq => ?_
      obtain ⟨j, hj⟩ := hperm τ hτ i
      have : τ * q * τ⁻¹ ∈ conjBy τ (Pi i) := mem_conjBy_of_mem hq
      rw [hj] at this
      exact hPiF j this
    exact hle hp
  have hNH : ∀ τ ∈ H, ∀ n ∈ N, τ n ∈ N := by
    intro τ hτ n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q, hq, z, hz, rfl⟩ := hx
      have hτz : τ⁻¹ z = z := hz τ⁻¹ (H.inv_mem hτ)
      have : τ (q z) = (τ * q * τ⁻¹) z := by
        show τ (q z) = τ (q (τ⁻¹ z))
        rw [hτz]
      rw [this]
      exact Subgroup.subset_closure ⟨_, hconjF τ hτ q hq, z, hz, rfl⟩
    | one => rw [map_one]; exact N.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact N.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact N.inv_mem hx
  have hfix_le : fixV H ≤ N := fun z hz =>
    Subgroup.subset_closure ⟨1, F.one_mem, z, hz, rfl⟩
  by_cases hall : ∀ i, commV (Pi i) ≤ N
  · rw [eq_top_iff, ← d.vsup]
    exact iSup_le hall
  · exfalso
    push Not at hall
    obtain ⟨k₀, hk₀⟩ := hall
    let T : Finset (Fin s) := Finset.univ.filter fun k => ¬ commV (Pi k) ≤ N
    have hT : ∀ k, k ∈ T ↔ ¬ commV (Pi k) ≤ N := fun k => by simp [T]
    have hcompl : ∀ k ∈ T, N ≤ FDec.compl Pi k := by
      intro k hk
      rcases d.le_or_le_compl hV k (fun p hp n hn => hNF p (hPiF k hp) n hn) with h | h
      · exact absurd h ((hT k).mp hk)
      · exact h
    set U'' : Subgroup W := ⨆ k ∈ T, commV (Pi k) with hU''
    have hU''ne : U'' ≠ ⊥ := by
      intro h
      have : commV (Pi k₀) ≤ U'' := le_iSup₂ (f := fun k (_ : k ∈ T) => commV (Pi k)) k₀
        ((hT k₀).mpr hk₀)
      rw [h, le_bot_iff] at this
      exact d.commV_ne_bot k₀ this
    have hU''inv : ∀ τ ∈ H, ∀ u ∈ U'', τ u ∈ U'' := by
      intro τ hτ
      have hle : U'' ≤ U''.comap (τ : MulAut W).toMonoidHom := by
        refine iSup₂_le fun k hk u hu => ?_
        obtain ⟨j, hj⟩ := hperm τ hτ k
        have h1 : τ u ∈ commV (Pi j) := by
          have : τ u ∈ commV (conjBy τ (Pi k)) := by
            rw [commV_conjBy]
            exact ⟨u, hu, rfl⟩
          rwa [hj] at this
        have hjT : j ∈ T := by
          rw [hT]
          intro hjN
          apply (hT k).mp hk
          intro x hx
          have hτx : τ x ∈ commV (Pi j) := by
            have : τ x ∈ commV (conjBy τ (Pi k)) := by
              rw [commV_conjBy]
              exact ⟨x, hx, rfl⟩
            rwa [hj] at this
          have := hNH τ⁻¹ (H.inv_mem hτ) (τ x) (hjN hτx)
          simpa using this
        exact le_iSup₂ (f := fun k (_ : k ∈ T) => commV (Pi k)) j hjT h1
      intro u hu
      exact hle hu
    have hpos := rk_inf_fixV_pos_of_isPGroup_two hV hH hU''inv hU''ne
    have hne : (U'' ⊓ fixV H : Subgroup W) ≠ ⊥ := (rk_pos_iff_ne_bot' hV).mp hpos
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    apply hz1
    refine Subtype.ext (d.eq_one_of_mem T hz.1 fun k hk => hcompl k hk (hfix_le hz.2))

theorem exists_orbit_complement {P : Fin 3 → Subgroup (MulAut W)} (hinj : Function.Injective P)
    {H : Subgroup (MulAut W)} (hH : IsPGroup 2 H)
    (hperm : ∀ τ ∈ H, ∀ i, ∃ j, conjBy τ (P i) = P j) (i : Fin 3) :
    ∃ k, ∀ τ ∈ H, conjBy τ (P i) ≠ P k := by
  classical
  by_contra hcon
  push Not at hcon
  let act : ↥H → Fin 3 → Fin 3 := fun τ j => Classical.choose (hperm τ τ.2 j)
  have hact : ∀ τ : ↥H, ∀ j, conjBy (τ : MulAut W) (P j) = P (act τ j) := fun τ j =>
    Classical.choose_spec (hperm τ τ.2 j)
  have hone : ∀ j, act 1 j = j := fun j => hinj (by
    rw [← hact]
    exact conjBy_one _)
  have hmul : ∀ a b j, act (a * b) j = act a (act b j) := fun a b j => hinj (by
    rw [← hact, Subgroup.coe_mul, ← conjBy_conjBy, hact b j, hact a])
  let _ : MulAction ↥H (Fin 3) :=
    { smul := act
      one_smul := hone
      mul_smul := hmul }
  have horb : MulAction.orbit ↥H i = Set.univ := by
    refine Set.eq_univ_of_forall fun k => ?_
    obtain ⟨τ, hτ, hτk⟩ := hcon k
    refine ⟨⟨τ, hτ⟩, hinj ?_⟩
    show P (act ⟨τ, hτ⟩ i) = P k
    rw [← hact]
    exact hτk
  have h1 := MulAction.index_stabilizer ↥H i
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥H i)
  have h3 : (Set.univ : Set (Fin 3)).ncard = 3 := by simp
  rw [horb, h3] at h1
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hH
  have : 3 ∣ 2 ^ m := by
    rw [← hm, ← h2, h1]
    exact dvd_mul_left 3 _
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

omit [Finite W] in
theorem mem_fixV_iSup {ι : Type*} {f : ι → Subgroup (MulAut W)} {S : Set ι} {u : W}
    (h : ∀ j ∈ S, u ∈ fixV (f j)) : u ∈ fixV (⨆ j ∈ S, f j) := by
  have : (⨆ j ∈ S, f j) ≤ MulAction.stabilizer (MulAut W) u := by
    refine iSup₂_le fun j hj g hg => ?_
    exact h j hj g hg
  intro g hg
  exact this hg

theorem FDec.false_of_three (hV : ∀ v : W, v ^ 2 = 1) {Xr H Ξ : Subgroup (MulAut W)}
    (hU : UStar Xr H Ξ) {Pi : Fin 3 → Subgroup (MulAut W)} (d : FDec Y Pi)
    (hPiX : ∀ i, Pi i ≤ Xr) (hperm : ∀ τ ∈ H, ∀ i, ∃ j, conjBy τ (Pi i) = Pi j) : False := by
  classical
  have hPiΞ : ∀ i, Pi i ≤ Ξ := by
    intro i ψ hψ
    obtain ⟨k, hk⟩ := exists_orbit_complement d.injective hU.isP hperm i
    let O : Set (Fin 3) := {j | ∃ τ ∈ H, conjBy τ (Pi i) = Pi j}
    set R : Subgroup (MulAut W) := ⨆ j ∈ O, Pi j with hR
    have hiO : i ∈ O := ⟨1, H.one_mem, by rw [conjBy_one]⟩
    have hkO : k ∉ O := by
      rintro ⟨τ, hτ, hτk⟩
      exact hk τ hτ hτk
    have hRH : ∀ τ ∈ H, ∀ r ∈ R, τ * r * τ⁻¹ ∈ R := by
      intro τ hτ r hr
      have hle : R ≤ R.comap (MulAut.conj τ).toMonoidHom := by
        refine iSup₂_le fun j hj q hq => ?_
        obtain ⟨j', hj'⟩ := hperm τ hτ j
        obtain ⟨τ₀, hτ₀, hτ₀j⟩ := hj
        have hj'O : j' ∈ O := ⟨τ * τ₀, H.mul_mem hτ hτ₀, by rw [← conjBy_conjBy, hτ₀j, hj']⟩
        have : τ * q * τ⁻¹ ∈ conjBy τ (Pi j) := mem_conjBy_of_mem hq
        rw [hj'] at this
        exact (le_iSup₂ (f := fun j (_ : j ∈ O) => Pi j) j' hj'O) this
      exact hle hr
    have hinv : ∀ τ ∈ H, ∀ u ∈ fixV R, τ u ∈ fixV R := by
      intro τ hτ u hu r hr
      have h1 : τ⁻¹ * r * τ⁻¹⁻¹ ∈ R := hRH τ⁻¹ (H.inv_mem hτ) r hr
      have h2 := hu _ h1
      have : r (τ u) = τ u := by
        have h3 : (τ⁻¹ * r * τ⁻¹⁻¹) u = u := h2
        have h4 : (τ⁻¹ * r * τ) u = u := by simpa using h3
        have h5 := congrArg (fun w => τ w) h4
        simpa using h5
      exact this
    have hne : fixV R ≠ ⊥ := by
      intro hbot
      have hsub : commV (Pi k) ≤ fixV R := by
        intro u hu
        refine mem_fixV_iSup ?_
        intro j hj
        have hjk : j ≠ k := fun e => hkO (e ▸ hj)
        exact d.triv k j (Ne.symm hjk) hu
      rw [hbot, le_bot_iff] at hsub
      exact d.commV_ne_bot k hsub
    have hpos := rk_inf_fixV_pos_of_isPGroup_two hV hU.isP hinv hne
    have hne' : (fixV R ⊓ fixV H : Subgroup W) ≠ ⊥ := (rk_pos_iff_ne_bot' hV).mp hpos
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
    have hψR : ψ ∈ R := (le_iSup₂ (f := fun j (_ : j ∈ O) => Pi j) i hiO) hψ
    exact hU.hU z hz.2 (fun e => hz1 (Subtype.ext e)) ψ (hPiX i hψ) (hz.1 ψ hψR)
  have hFΞ : (⨆ i, Pi i) ≤ Ξ := iSup_le hPiΞ
  have htop := d.closure_eq_top hV hU.isP hperm
  have hne : (⊤ : Subgroup W) ≠ ⊥ := by
    intro h
    apply d.commV_ne_bot 0
    rw [eq_bot_iff, ← h]
    exact le_top
  refine hU.star ⊤ hne (fun _ _ w _ => Subgroup.mem_top _) (le_trans (le_of_eq htop.symm) ?_)
  refine Subgroup.closure_mono ?_
  rintro x ⟨p, hp, z, hz, rfl⟩
  exact ⟨p, hFΞ hp, z, ⟨hz, Subgroup.mem_top z⟩, rfl⟩

end FDec151c

end CFSG.Quasithin
