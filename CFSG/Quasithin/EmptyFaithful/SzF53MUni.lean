module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.F53Mod

open Equiv
open scoped Pointwise

theorem mem_map_conj {G : Type*} [Group G] (B : Subgroup G) (g σ : G) :
    σ ∈ B.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * σ * g ∈ B := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hb
  · intro h
    exact ⟨g⁻¹ * σ * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_fixW_map_conj {n : ℕ} (M : Model n) (g : Perm (Fin n)) (B : Subgroup (Perm (Fin n)))
    (w : M.W) :
    w ∈ fixW M (B.map (MulAut.conj g).toMonoidHom) ↔ M.act g⁻¹ w ∈ fixW M B := by
  constructor
  · intro h b hb
    have h1 := h (g * b * g⁻¹) ((mem_map_conj B g _).mpr (by simpa [mul_assoc] using hb))
    calc M.act b (M.act g⁻¹ w) = M.act (b * g⁻¹) w := (act_mul_apply M _ _ _).symm
      _ = M.act (g⁻¹ * (g * b * g⁻¹)) w := by congr 1; group
      _ = M.act g⁻¹ (M.act (g * b * g⁻¹) w) := act_mul_apply M _ _ _
      _ = M.act g⁻¹ w := by rw [h1]
  · intro h σ hσ
    have hb : g⁻¹ * σ * g ∈ B := (mem_map_conj B g σ).mp hσ
    have h1 := h _ hb
    calc M.act σ w = M.act g (M.act (g⁻¹ * σ * g) (M.act g⁻¹ w)) := by
          rw [← act_mul_apply, ← act_mul_apply]; congr 1; group
      _ = M.act g (M.act g⁻¹ w) := by rw [h1]
      _ = w := act_act_inv M g w

theorem card_fixW_conj {n : ℕ} (M : Model n) (g : Perm (Fin n)) (B : Subgroup (Perm (Fin n))) :
    Nat.card (fixW M (B.map (MulAut.conj g).toMonoidHom)) = Nat.card (fixW M B) :=
  Nat.card_congr
    { toFun := fun w => ⟨M.act g⁻¹ w.1, (mem_fixW_map_conj M g B w.1).mp w.2⟩
      invFun := fun w => ⟨M.act g w.1, (mem_fixW_map_conj M g B _).mpr
        (by rw [act_inv_act]; exact w.2)⟩
      left_inv := fun w => Subtype.ext (act_act_inv M g w.1)
      right_inv := fun w => Subtype.ext (act_inv_act M g w.1) }

theorem map_commW_conj {n : ℕ} (M : Model n) (g : Perm (Fin n)) (B : Subgroup (Perm (Fin n)))
    (U : Subgroup M.W) :
    (commW M B U).map (M.act g).toMonoidHom =
      commW M (B.map (MulAut.conj g).toMonoidHom) (U.map (M.act g).toMonoidHom) := by
  unfold commW
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨b, hb, u, hu, rfl⟩, rfl⟩
    refine ⟨g * b * g⁻¹, ⟨b, hb, by simp [MulAut.conj_apply]⟩, M.act g u, ⟨u, hu, rfl⟩, ?_⟩
    show M.act g (M.act b u * u⁻¹) = M.act (g * b * g⁻¹) (M.act g u) * (M.act g u)⁻¹
    rw [map_mul, map_inv, act_mul_apply, act_mul_apply, act_inv_act]
  · rintro ⟨_, ⟨b, hb, rfl⟩, _, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨M.act b u * u⁻¹, ⟨b, hb, u, hu, rfl⟩, ?_⟩
    show M.act g (M.act b u * u⁻¹) = M.act (MulAut.conj g b) (M.act g u) * (M.act g u)⁻¹
    rw [map_mul, map_inv, MulAut.conj_apply, act_mul_apply, act_mul_apply, act_inv_act]

theorem map_act_top {n : ℕ} (M : Model n) (g : Perm (Fin n)) :
    (⊤ : Subgroup M.W).map (M.act g).toMonoidHom = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)

theorem card_map_act {n : ℕ} (M : Model n) (g : Perm (Fin n)) (U : Subgroup M.W) :
    Nat.card (U.map (M.act g).toMonoidHom) = Nat.card U :=
  Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem profile_conj {n : ℕ} (M : Model n) (g : Perm (Fin n)) (B : Subgroup (Perm (Fin n))) :
    profile M (B.map (MulAut.conj g).toMonoidHom) = profile M B := by
  have h1 : commW M (B.map (MulAut.conj g).toMonoidHom) ⊤ =
      (commW M B ⊤).map (M.act g).toMonoidHom := by
    rw [map_commW_conj, map_act_top]
  have h2 : commW M (B.map (MulAut.conj g).toMonoidHom)
      (commW M (B.map (MulAut.conj g).toMonoidHom) ⊤) =
      (commW M B (commW M B ⊤)).map (M.act g).toMonoidHom := by
    rw [h1, ← map_commW_conj M g B (commW M B ⊤)]
  unfold profile
  rw [h2, h1, card_map_act, card_map_act, card_fixW_conj]

theorem card_S5SylF : S5SylF.card = 8 := by
  decide +kernel

theorem card_S5Syl : Nat.card S5Syl = 8 := by
  rw [← card_S5SylF, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight mem_S5Syl_iff)

theorem exists_conj_S5Syl {P : Subgroup (Perm (Fin 5))} (hP : Nat.card P = 8) :
    ∃ g : Perm (Fin 5), P = S5Syl.map (MulAut.conj g).toMonoidHom := by
  have hG : Nat.card (Perm (Fin 5)) = 2 ^ 3 * 15 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have idx : ∀ {E : Subgroup (Perm (Fin 5))}, Nat.card E = 2 ^ 3 → ¬ 2 ∣ E.index := by
    intro E hE
    have h1 := Subgroup.card_mul_index E
    rw [hE, hG] at h1
    rw [Nat.eq_of_mul_eq_mul_left (by positivity) h1]
    norm_num
  have h0 : Nat.card S5Syl = 2 ^ 3 := by rw [card_S5Syl]; norm_num
  have hD : Nat.card P = 2 ^ 3 := by rw [hP]; norm_num
  let P0 : Sylow 2 (Perm (Fin 5)) := (IsPGroup.of_card h0).toSylow (idx h0)
  let Q : Sylow 2 (Perm (Fin 5)) := (IsPGroup.of_card hD).toSylow (idx hD)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) P0 Q
  exact ⟨g, (congrArg (fun R : Sylow 2 (Perm (Fin 5)) => (R : Subgroup (Perm (Fin 5)))) hg).symm⟩

theorem profile_sylow (M : Model 5) (hM : M = orth ∨ M = nat) {P : Subgroup (Perm (Fin 5))}
    (hP : Nat.card P = 8) : profile M P = (8, 2, 4) := by
  obtain ⟨g, rfl⟩ := exists_conj_S5Syl hP
  rw [profile_conj]
  rcases hM with rfl | rfl
  · exact profile_orth.2.2.2.2.2
  · exact profile_nat.2.2.2.2.2

@[expose] def IsInvSub {n : ℕ} (M : Model n) (B : Subgroup (Perm (Fin n))) (U : Subgroup M.W) :
    Prop :=
  ∀ b ∈ B, ∀ u ∈ U, M.act b u ∈ U

@[expose] def commIter {n : ℕ} (M : Model n) (B : Subgroup (Perm (Fin n))) : ℕ → Subgroup M.W
  | 0 => ⊤
  | i + 1 => commW M B (commIter M B i)

def commIterF {n : ℕ} (M : Model n) [Fintype M.W] [DecidableEq M.W]
    (Bf : Finset (Perm (Fin n))) : ℕ → Finset M.W
  | 0 => Finset.univ
  | i + 1 => spanF (commGensF M Bf (commIterF M Bf i))

theorem mem_commIter_iff {n : ℕ} (M : Model n) [Fintype M.W] [DecidableEq M.W]
    {B : Subgroup (Perm (Fin n))} {Bf : Finset (Perm (Fin n))} (hB : ∀ σ, σ ∈ B ↔ σ ∈ Bf)
    (i : ℕ) (w : M.W) : w ∈ commIter M B i ↔ w ∈ commIterF M Bf i := by
  induction i generalizing w with
  | zero => simp [commIter, commIterF]
  | succ i ih => exact mem_commW_iff M hB ih w

def orbitSpanF {n : ℕ} (M : Model n) [DecidableEq M.W] (Bf : Finset (Perm (Fin n))) (x : M.W) :
    Finset M.W :=
  spanF (Bf.image fun b => M.act b x)

theorem isInvSub_commW {n : ℕ} (M : Model n) {B : Subgroup (Perm (Fin n))} {U : Subgroup M.W}
    (hU : IsInvSub M B U) : IsInvSub M B (commW M B U) := by
  intro b hb w hw
  unfold commW at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, u, hu, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨b * c * b⁻¹, B.mul_mem (B.mul_mem hb hc) (B.inv_mem hb), M.act b u, hU b hb u hu, ?_⟩
    rw [map_mul, map_inv, act_mul_apply, act_mul_apply, act_inv_act]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem commW_le {n : ℕ} (M : Model n) {B : Subgroup (Perm (Fin n))} {U : Subgroup M.W}
    (hU : IsInvSub M B U) : commW M B U ≤ U := by
  unfold commW
  rw [Subgroup.closure_le]
  rintro w ⟨c, hc, u, hu, rfl⟩
  exact U.mul_mem (hU c hc u hu) (U.inv_mem hu)

theorem isInvSub_commIter {n : ℕ} (M : Model n) (B : Subgroup (Perm (Fin n))) (i : ℕ) :
    IsInvSub M B (commIter M B i) := by
  induction i with
  | zero => intro b hb u hu; trivial
  | succ i ih => exact isInvSub_commW M ih

theorem card_commIter {n : ℕ} (M : Model n) [Fintype M.W] [DecidableEq M.W]
    {B : Subgroup (Perm (Fin n))} {Bf : Finset (Perm (Fin n))} (hB : ∀ σ, σ ∈ B ↔ σ ∈ Bf)
    (i : ℕ) : Nat.card (commIter M B i) = (commIterF M Bf i).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun w => mem_commIter_iff M hB i w)

theorem orbitSpanF_subset {n : ℕ} (M : Model n) [DecidableEq M.W] {B : Subgroup (Perm (Fin n))}
    {Bf : Finset (Perm (Fin n))} (hB : ∀ σ, σ ∈ B ↔ σ ∈ Bf) {U : Subgroup M.W}
    (hU : IsInvSub M B U) {x : M.W} (hx : x ∈ U) : ∀ w ∈ orbitSpanF M Bf x, w ∈ U := by
  intro w hw
  have h1 := spanF_subset_closure _ w hw
  refine (Subgroup.closure_le U).mpr ?_ h1
  intro v hv
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
  obtain ⟨b, hb, rfl⟩ := hv
  exact hU b ((hB b).mpr hb) x hx

theorem invSub_cases (M : Model 5) [Fintype M.W] [DecidableEq M.W]
    (hcard : ∀ i < 5, (commIterF M S5SylF i).card = 2 ^ (4 - i))
    (hgen : ∀ i < 4, ∀ x ∈ commIterF M S5SylF i,
      x ∈ commIterF M S5SylF (i + 1) ∨ 2 ^ (4 - i) ≤ (orbitSpanF M S5SylF x).card)
    (U : Subgroup M.W) (hU : IsInvSub M S5Syl U) :
    ∃ j ≤ 4, ∀ w, w ∈ U ↔ w ∈ commIterF M S5SylF j := by
  have key : ∀ d i : ℕ, i + d = 4 → (∀ u ∈ U, u ∈ commIterF M S5SylF i) →
      ∃ j ≤ 4, ∀ w, w ∈ U ↔ w ∈ commIterF M S5SylF j := by
    intro d
    induction d with
    | zero =>
      intro i hi hP
      have hi4 : i = 4 := by omega
      subst hi4
      refine ⟨4, le_rfl, fun w => ⟨hP w, fun hw => ?_⟩⟩
      have hc := hcard 4 (by norm_num)
      simp only [Nat.sub_self, pow_zero] at hc
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
      have h1 : (1 : M.W) ∈ commIterF M S5SylF 4 := one_mem_spanF _
      rw [ha, Finset.mem_singleton] at h1 hw
      rw [hw, ← h1]; exact U.one_mem
    | succ d ih =>
      intro i hi hP
      by_cases hP' : ∀ u ∈ U, u ∈ commIterF M S5SylF (i + 1)
      · exact ih (i + 1) (by omega) hP'
      · push Not at hP'
        obtain ⟨x, hxU, hx⟩ := hP'
        have hxi := hP x hxU
        have hlt : i < 4 := by omega
        have hg := hgen i hlt x hxi
        have hbig : 2 ^ (4 - i) ≤ (orbitSpanF M S5SylF x).card := hg.resolve_left hx
        have hsub : orbitSpanF M S5SylF x ⊆ commIterF M S5SylF i := by
          intro w hw
          have h2 : w ∈ U := orbitSpanF_subset M mem_S5Syl_iff hU hxU w hw
          exact hP w h2
        have heq : orbitSpanF M S5SylF x = commIterF M S5SylF i :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hcard i (by omega)]; exact hbig)
        refine ⟨i, by omega, fun w => ⟨hP w, fun hw => ?_⟩⟩
        rw [← heq] at hw
        exact orbitSpanF_subset M mem_S5Syl_iff hU hxU w hw
  exact key 4 0 rfl (fun u _ => Finset.mem_univ u)

theorem lemma26_of_check (M : Model 5) [Fintype M.W] [DecidableEq M.W]
    (hcard : ∀ i < 5, (commIterF M S5SylF i).card = 2 ^ (4 - i))
    (hgen : ∀ i < 4, ∀ x ∈ commIterF M S5SylF i,
      x ∈ commIterF M S5SylF (i + 1) ∨ 2 ^ (4 - i) ≤ (orbitSpanF M S5SylF x).card) :
    ∀ k ≤ 4, ∃! U : Subgroup M.W, IsInvSub M S5Syl U ∧ Nat.card U = 2 ^ k := by
  intro k hk
  refine ⟨commIter M S5Syl (4 - k), ⟨isInvSub_commIter M S5Syl _, ?_⟩, ?_⟩
  · rw [card_commIter M mem_S5Syl_iff, hcard _ (by omega)]
    congr 1; omega
  · rintro V ⟨hV, hVc⟩
    obtain ⟨j, hj, hVj⟩ := invSub_cases M hcard hgen V hV
    have hcj : Nat.card V = (commIterF M S5SylF j).card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight hVj)
    rw [hcard j (by omega), hVc] at hcj
    have hkj : k = 4 - j := Nat.pow_right_injective (le_refl 2) hcj
    ext w
    rw [hVj w, mem_commIter_iff M mem_S5Syl_iff]
    have : 4 - k = j := by omega
    rw [this]

set_option maxRecDepth 100000 in
private theorem uni_card_orth : ∀ i < 5, (commIterF orth S5SylF i).card = 2 ^ (4 - i) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem uni_gen_orth : ∀ i < 4, ∀ x ∈ commIterF orth S5SylF i,
    x ∈ commIterF orth S5SylF (i + 1) ∨ 2 ^ (4 - i) ≤ (orbitSpanF orth S5SylF x).card := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem uni_card_nat : ∀ i < 5, (commIterF nat S5SylF i).card = 2 ^ (4 - i) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem uni_gen_nat : ∀ i < 4, ∀ x ∈ commIterF nat S5SylF i,
    x ∈ commIterF nat S5SylF (i + 1) ∨ 2 ^ (4 - i) ≤ (orbitSpanF nat S5SylF x).card := by
  decide +kernel

theorem lemma26 (M : Model 5) (hM : M = orth ∨ M = nat) :
    ∀ k ≤ 4, ∃! U : Subgroup M.W, IsInvSub M S5Syl U ∧ Nat.card U = 2 ^ k := by
  rcases hM with rfl | rfl
  · exact lemma26_of_check orth uni_card_orth uni_gen_orth
  · exact lemma26_of_check nat uni_card_nat uni_gen_nat

theorem map_act_map_act_inv {n : ℕ} (M : Model n) (g : Perm (Fin n)) (V : Subgroup M.W) :
    (V.map (M.act g⁻¹).toMonoidHom).map (M.act g).toMonoidHom = V := by
  ext w
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    show M.act g (M.act g⁻¹ u) ∈ V
    rw [act_act_inv]; exact hu
  · intro hw
    exact ⟨_, ⟨w, hw, rfl⟩, act_act_inv M g w⟩

theorem map_act_inv_map_act {n : ℕ} (M : Model n) (g : Perm (Fin n)) (V : Subgroup M.W) :
    (V.map (M.act g).toMonoidHom).map (M.act g⁻¹).toMonoidHom = V := by
  have := map_act_map_act_inv M g⁻¹ V
  rwa [inv_inv] at this

theorem isInvSub_map_conj_iff {n : ℕ} (M : Model n) (g : Perm (Fin n))
    (B : Subgroup (Perm (Fin n))) (U : Subgroup M.W) :
    IsInvSub M (B.map (MulAut.conj g).toMonoidHom) U ↔
      IsInvSub M B (U.map (M.act g⁻¹).toMonoidHom) := by
  constructor
  · intro h b hb u' hu'
    obtain ⟨u, hu, rfl⟩ := hu'
    refine ⟨M.act (g * b * g⁻¹) u, h _ ((mem_map_conj B g _).mpr (by simpa [mul_assoc] using hb))
      u hu, ?_⟩
    show M.act g⁻¹ (M.act (g * b * g⁻¹) u) = M.act b (M.act g⁻¹ u)
    rw [← act_mul_apply, ← act_mul_apply]; congr 1; group
  · intro h σ hσ u hu
    have hb : g⁻¹ * σ * g ∈ B := (mem_map_conj B g σ).mp hσ
    obtain ⟨u₁, hu₁, h1⟩ := h _ hb (M.act g⁻¹ u) ⟨u, hu, rfl⟩
    have h2 : M.act σ u = u₁ := by
      have h3 : M.act g (M.act (g⁻¹ * σ * g) (M.act g⁻¹ u)) = M.act g (M.act g⁻¹ u₁) := by
        rw [← h1]; rfl
      rw [act_act_inv, ← act_mul_apply, ← act_mul_apply] at h3
      rw [← h3]; congr 1; group
    rw [h2]; exact hu₁

theorem lemma26_sylow (M : Model 5) (hM : M = orth ∨ M = nat) {P : Subgroup (Perm (Fin 5))}
    (hP : Nat.card P = 8) :
    ∀ k ≤ 4, ∃! U : Subgroup M.W, IsInvSub M P U ∧ Nat.card U = 2 ^ k := by
  obtain ⟨g, rfl⟩ := exists_conj_S5Syl hP
  intro k hk
  obtain ⟨U₀, ⟨hU₀, hc₀⟩, huniq⟩ := lemma26 M hM k hk
  refine ⟨U₀.map (M.act g).toMonoidHom, ⟨?_, ?_⟩, ?_⟩
  · rw [isInvSub_map_conj_iff, map_act_inv_map_act]; exact hU₀
  · rw [card_map_act, hc₀]
  · rintro V ⟨hV, hVc⟩
    have h1 : V.map (M.act g⁻¹).toMonoidHom = U₀ := by
      refine huniq _ ⟨(isInvSub_map_conj_iff M g _ V).mp hV, ?_⟩
      rw [card_map_act, hVc]
    rw [← h1, map_act_map_act_inv]

private theorem nat_trans_dec : ∀ x y : nat.W, x ≠ 1 → y ≠ 1 →
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ nat.act σ x = y := by decide +kernel

theorem nat_transitive (x y : nat.W) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ σ ∈ alternatingGroup (Fin 5), nat.act σ x = y := by
  obtain ⟨σ, h1, h2⟩ := nat_trans_dec x y hx hy
  exact ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr h1, h2⟩

@[expose] def wtO (x : orth.W) : ℕ :=
  (Finset.univ.filter fun i : Fin 5 => Multiplicative.toAdd (x : ↥(G6.coreMod 5)).1 i ≠ 0).card

private theorem wtO_act_dec : ∀ (σ : Perm (Fin 5)) (x : orth.W), wtO (orth.act σ x) = wtO x := by
  decide +kernel

theorem wtO_act (σ : Perm (Fin 5)) (x : orth.W) : wtO (orth.act σ x) = wtO x := wtO_act_dec σ x

private theorem orth_trans_dec : ∀ x y : orth.W, x ≠ 1 → y ≠ 1 → wtO x = wtO y →
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ orth.act σ x = y := by decide +kernel

theorem orth_orbits (x y : orth.W) (hx : x ≠ 1) (hy : y ≠ 1) :
    (∃ σ ∈ alternatingGroup (Fin 5), orth.act σ x = y) ↔ wtO x = wtO y := by
  constructor
  · rintro ⟨σ, -, rfl⟩
    exact (wtO_act σ x).symm
  · intro h
    obtain ⟨σ, h1, h2⟩ := orth_trans_dec x y hx hy h
    exact ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr h1, h2⟩

theorem irreducible_orth (Y : Subgroup orth.W)
    (hY : ∀ σ : Perm (Fin 5), ∀ y ∈ Y, orth.act σ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ :=
  X1512.coreMod_irreducible (Or.inr rfl) Y hY

theorem irreducible_nat (Y : Subgroup nat.W)
    (hY : ∀ σ : Perm (Fin 5), ∀ y ∈ Y, nat.act σ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : ∀ u ∈ Y, u = 1
  · exact Or.inl ((Subgroup.eq_bot_iff_forall Y).mpr hbot)
  · right
    push Not at hbot
    obtain ⟨x, hxY, hx1⟩ := hbot
    rw [eq_top_iff]
    intro y _
    by_cases hy1 : y = 1
    · rw [hy1]; exact Y.one_mem
    · obtain ⟨σ, -, hσ⟩ := nat_transitive x y hx1 hy1
      rw [← hσ]
      exact hY σ x hxY

set_option maxRecDepth 100000 in
private theorem nat_l2_table : ∀ τ ∈ S5SylF,
    (∀ y ∈ commIterF nat S5SylF 2, nat.act τ y = y) ↔ Perm.sign τ = 1 := by
  decide +kernel

theorem nat_centralizer_l2 {τ : Perm (Fin 5)} (hτ : τ ∈ S5Syl) (Y : Subgroup nat.W)
    (hY : IsInvSub nat S5Syl Y) (hc : Nat.card Y = 4) :
    (∀ y ∈ Y, nat.act τ y = y) ↔ τ ∈ alternatingGroup (Fin 5) := by
  have hcard : Nat.card (commIter nat S5Syl 2) = 2 ^ 2 := by
    rw [card_commIter nat mem_S5Syl_iff, uni_card_nat 2 (by norm_num)]
  have hYeq : Y = commIter nat S5Syl 2 :=
    ((lemma26 nat (Or.inr rfl) 2 (by norm_num)).unique ⟨hY, by rw [hc]; norm_num⟩
      ⟨isInvSub_commIter nat S5Syl 2, hcard⟩)
  rw [Equiv.Perm.mem_alternatingGroup, ← nat_l2_table τ ((mem_S5Syl_iff τ).mp hτ), hYeq]
  exact forall_congr' fun y => by rw [mem_commIter_iff nat mem_S5Syl_iff]

end CFSG.Quasithin.F53Mod
