module

public import CFSG.YGroups.SymmetricGenerators
public import CFSG.YGroups.DoubleCoset

public section

namespace CFSG.YGroups

theorem relIndex_map_range_le {E G : Type*} [Group E] [Group G] [Finite E] (ψ : E →* G)
    (P : Subgroup E) : (P.map ψ).relIndex ψ.range ≤ P.index := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le le_sup_left)

namespace SymGen.Setup

variable {G E Ω : Type*} [Group G] [Group E] [MulAction E Ω] (S : Setup G E Ω)

theorem rcoset_iff_mem (a b : G) : S.RCoset a b ↔ a * b⁻¹ ∈ S.H := Iff.rfl

theorem index_le_of_points [Finite E] (r : ℕ) (x : ℕ → G) (hx0 : x 0 ∈ S.H)
    (P : ℕ → Subgroup E) (hP : ∀ j < r, ∀ e ∈ P j, x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (R : ℕ → Finset Ω) (hR : ∀ j < r, ∀ p : Ω, ∃ q ∈ R j, ∃ e ∈ P j, e • q = p)
    (tgt : ℕ → Ω → ℕ) (u : ℕ → Ω → E)
    (htgt : ∀ j < r, ∀ q ∈ R j, tgt j q < r ∧ S.RCoset (x j * S.T q) (x (tgt j q) * S.ψ (u j q)))
    (hgen : Subgroup.closure ((S.H : Set G) ∪ {S.t}) = ⊤) (hr : 0 < r) :
    S.H.FiniteIndex ∧ S.H.index ≤ ∑ j ∈ Finset.range r, (P j).index := by
  classical
  have : Finite S.H := Finite.of_surjective S.ψ.rangeRestrict S.ψ.rangeRestrict_surjective
  let C : Subgroup G := (MulAction.stabilizer E S.o).map S.ψ
  have hCH : C ≤ S.H := Subgroup.map_le_range _ _
  have htC : ∀ c ∈ C, S.t * c = c * S.t := by
    rintro _ ⟨e, he, rfl⟩
    exact (S.stab_comm e he).symm
  let pick : Fin r → G → Ω := fun i k =>
    if hk : ∃ q ∈ R i, S.ψ (S.w q) = k then Classical.choose hk else S.o
  have pick_spec : ∀ i : Fin r, ∀ k ∈ (R i).image (fun q => S.ψ (S.w q)),
      pick i k ∈ R i ∧ S.ψ (S.w (pick i k)) = k := by
    intro i k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hk
    have hex : ∃ q' ∈ R i, S.ψ (S.w q') = S.ψ (S.w q) := ⟨q, hq, rfl⟩
    simp only [pick, dite_eq_left hex]
    exact Classical.choose_spec hex
  let tgtF : Fin r → G → Fin r := fun i k =>
    if h : pick i k ∈ R i then ⟨tgt i (pick i k), (htgt i i.2 _ h).1⟩ else ⟨0, hr⟩
  let eltF : Fin r → G → G := fun i k =>
    if h : pick i k ∈ R i then S.ψ (u i (pick i k) * S.w (pick i k)) else 1
  have tgtF_eq : ∀ (i : Fin r) (k : G), pick i k ∈ R i →
      ((tgtF i k : Fin r) : ℕ) = tgt i (pick i k) := by
    intro i k h
    simp only [tgtF, dite_eq_left h]
  have eltF_eq : ∀ (i : Fin r) (k : G), pick i k ∈ R i →
      eltF i k = S.ψ (u i (pick i k) * S.w (pick i k)) := by
    intro i k h
    simp only [eltF, dite_eq_left h]
  let D : DoubleCosetData S.H C S.t r :=
    { x := fun i => x i
      S := fun i => (P i).map S.ψ
      rep := fun i => (R i).image (fun q => S.ψ (S.w q))
      tgt := tgtF
      tgtElt := eltF
      base := ⟨0, hr⟩
      base_mem := hx0
      S_le := fun i => Subgroup.map_le_range _ _
      S_conj := by
        intro i s hs
        obtain ⟨e, he, rfl⟩ := hs
        exact hP i i.2 e he
      rep_le := by
        intro i k hk
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hk
        exact ⟨S.w q, rfl⟩
      rep_cover := by
        intro i h hh
        obtain ⟨e, rfl⟩ := hh
        obtain ⟨q, hq, f, hf, hfq⟩ := hR i i.2 (e • S.o)
        refine ⟨S.ψ (S.w q), Finset.mem_image_of_mem _ hq, S.ψ f, Subgroup.mem_map_of_mem _ hf,
          S.ψ ((f * S.w q)⁻¹ * e), Subgroup.mem_map.2 ⟨(f * S.w q)⁻¹ * e, ?_, rfl⟩, ?_⟩
        · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hfq, mul_inv_rev, mul_smul, inv_smul_smul,
            inv_smul_eq_iff, S.w_smul]
        · rw [← map_mul, ← map_mul, mul_inv_cancel_left]
      tgtElt_mem := by
        intro i k hk
        have hq := (pick_spec i k hk).1
        rw [eltF_eq i k hq]
        exact ⟨_, rfl⟩
      tgt_spec := by
        intro i k hk
        obtain ⟨hq, hwq⟩ := pick_spec i k hk
        show (x i : G) * k * S.t * (x ((tgtF i k : Fin r) : ℕ) * eltF i k)⁻¹ ∈ S.H
        rw [tgtF_eq i k hq, eltF_eq i k hq]
        have hrc := (S.rcoset_iff_mem _ _).1 (htgt i i.2 _ hq).2
        generalize pick i k = q at hq hwq hrc ⊢
        subst hwq
        have key : x i * S.ψ (S.w q) * S.t *
            (x (tgt i q) * S.ψ (u i q * S.w q))⁻¹ =
            x i * S.T q * (x (tgt i q) * S.ψ (u i q))⁻¹ := by
          unfold Setup.T
          rw [map_mul]
          group
        rw [key]
        exact hrc }
  obtain ⟨hfi, hle⟩ := DoubleCosetData.index_le_sum D hCH S.t_mul_t htC hgen
  refine ⟨hfi, hle.trans ?_⟩
  rw [← Fin.sum_univ_eq_sum_range (fun j => (P j).index) r]
  exact Finset.sum_le_sum fun i _ => relIndex_map_range_le S.ψ (P i)

end SymGen.Setup

@[expose] def chainStab {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (β : ℕ → Fin n) (j : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | g ∈ S ∧ ∀ m < j, g (β m) = β m}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨S.mul_mem ha hb, fun m hm => ?_⟩
    rw [Equiv.Perm.mul_apply, hb' m hm, ha' m hm]
  one_mem' := ⟨S.one_mem, fun _ _ => rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨S.inv_mem ha, fun m hm => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha' m hm).symm

theorem mem_chainStab {n : ℕ} {S : Subgroup (Equiv.Perm (Fin n))} {β : ℕ → Fin n} {j : ℕ}
    {g : Equiv.Perm (Fin n)} : g ∈ chainStab S β j ↔ g ∈ S ∧ ∀ m < j, g (β m) = β m :=
  Iff.rfl

theorem chainStab_zero {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (β : ℕ → Fin n) :
    chainStab S β 0 = S := by
  ext g
  rw [mem_chainStab]
  exact ⟨fun h => h.1, fun h => ⟨h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩⟩

theorem card_chainStab_step {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (β : ℕ → Fin n) (l : ℕ)
    {K : Subgroup (Equiv.Perm (Fin n))} (hK : K ≤ chainStab S β l) {o : ℕ}
    (ho : o ≤ (MulAction.orbit K (β l)).ncard) :
    o * Nat.card (chainStab S β (l + 1)) ≤ Nat.card (chainStab S β l) := by
  set Z := chainStab S β l with hZ
  have hsub : (MulAction.orbit K (β l) : Set (Fin n)) ⊆ MulAction.orbit Z (β l) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k.1, hK k.2⟩, rfl⟩
  have h1 : o ≤ (MulAction.orbit Z (β l)).ncard :=
    ho.trans (Set.ncard_le_ncard hsub (Set.toFinite _))
  have h2 : Nat.card (MulAction.orbit Z (β l)) * Nat.card (MulAction.stabilizer Z (β l)) =
      Nat.card Z := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Z (β l))]
  have h3 : Nat.card (MulAction.stabilizer Z (β l)) = Nat.card (chainStab S β (l + 1)) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.1, g.1.2.1, fun m hm => ?_⟩
        invFun := fun g => ⟨⟨g.1, g.2.1, fun m hm => g.2.2 m (by omega)⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | rfl
      · exact g.1.2.2 m h
      · exact MulAction.mem_stabilizer_iff.1 g.2
    · exact g.2.2 l (Nat.lt_succ_self l)
  calc o * Nat.card (chainStab S β (l + 1))
      ≤ (MulAction.orbit Z (β l)).ncard * Nat.card (chainStab S β (l + 1)) :=
        Nat.mul_le_mul_right _ h1
    _ = Nat.card (MulAction.orbit Z (β l)) * Nat.card (MulAction.stabilizer Z (β l)) := by
        rw [h3, Nat.card_coe_set_eq]
    _ = Nat.card Z := h2

theorem card_ge_of_chain {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (k : ℕ)
    (β : ℕ → Fin n) (Y : ℕ → Set (Equiv.Perm (Fin n))) (hY : ∀ l < k, Y l ⊆ S)
    (hfix : ∀ l < k, ∀ y ∈ Y l, ∀ m < l, y (β m) = β m) (o : ℕ → ℕ)
    (horb : ∀ l < k, o l ≤ (MulAction.orbit (Subgroup.closure (Y l)) (β l)).ncard) :
    ∏ l ∈ Finset.range k, o l ≤ Nat.card S := by
  have hle : ∀ l < k, Subgroup.closure (Y l) ≤ chainStab S β l := by
    intro l hl
    rw [Subgroup.closure_le]
    intro y hy
    exact ⟨hY l hl hy, hfix l hl y hy⟩
  have key : ∀ j ≤ k, (∏ l ∈ Finset.range j, o l) * Nat.card (chainStab S β j) ≤
      Nat.card S := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [chainStab_zero]
      simp
    | succ j ih =>
      intro hj
      rw [Finset.prod_range_succ]
      have h1 := ih (by omega)
      have h2 := card_chainStab_step S β j (hle j (by omega)) (horb j (by omega))
      calc (∏ l ∈ Finset.range j, o l) * o j * Nat.card (chainStab S β (j + 1))
          = (∏ l ∈ Finset.range j, o l) * (o j * Nat.card (chainStab S β (j + 1))) := by ring
        _ ≤ (∏ l ∈ Finset.range j, o l) * Nat.card (chainStab S β j) :=
          Nat.mul_le_mul_left _ h2
        _ ≤ Nat.card S := h1
  have hpos : 0 < Nat.card (chainStab S β k) := Nat.card_pos
  calc ∏ l ∈ Finset.range k, o l
      ≤ (∏ l ∈ Finset.range k, o l) * Nat.card (chainStab S β k) :=
        Nat.le_mul_of_pos_right _ hpos
    _ ≤ Nat.card S := key k le_rfl

end CFSG.YGroups
