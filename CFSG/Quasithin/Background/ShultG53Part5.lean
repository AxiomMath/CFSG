module

public import CFSG.Quasithin.Background.ShultG53Main
public import CFSG.Quasithin.Background.ShultG53Part5Pack

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 CFSG.Quasithin.H13.A6 Equiv

theorem card_closure_klein {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (a b c : M)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (habc : a + b + c = 0) :
    Nat.card ↥(AddSubgroup.closure ({a, b, c} : Set M)) = 4 := by
  classical
  have hdbl : ∀ x : M, x + x = 0 := fun x => by
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [← two_smul (ZMod 2) x, h2, zero_smul]
  have hc : c = a + b := by
    have h1 : c = -(a + b) := eq_neg_of_add_eq_zero_right habc
    rw [h1, neg_eq_iff_add_eq_zero, hdbl]
  let φ : (Fin 2 → ZMod 2) →+ M :=
    { toFun := fun v => v 0 • a + v 1 • b
      map_zero' := by simp
      map_add' := fun v w => by
        simp only [Pi.add_apply, add_smul]
        abel }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : v 0 • a + v 1 • b = 0 := hv
    have hc2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have hv0 : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rcases hc2 (v 0) with h0 | h0 <;> rcases hc2 (v 1) with h1 | h1
    · rw [hv0, h0, h1]
      funext i
      fin_cases i <;> rfl
    · rw [h0, h1] at hv'
      simp at hv'
      exact absurd hv' hb
    · rw [h0, h1] at hv'
      simp at hv'
      exact absurd hv' ha
    · rw [h0, h1] at hv'
      simp at hv'
      exact absurd (calc a = a + (b + b) := by rw [hdbl, add_zero]
          _ = (a + b) + b := by rw [add_assoc]
          _ = b := by rw [hv', zero_add]) hab
  have hrange : AddSubgroup.closure ({a, b, c} : Set M) = φ.range := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro x (rfl | rfl | rfl)
      · exact ⟨![1, 0], by simp [φ]⟩
      · exact ⟨![0, 1], by simp [φ]⟩
      · exact ⟨![1, 1], by simp [φ, hc]⟩
    · rintro _ ⟨v, rfl⟩
      have h1 := (AddSubgroup.toZModSubmodule 2 (AddSubgroup.closure ({a, b, c} : Set M))).smul_mem
        (v 0) (AddSubgroup.subset_closure (by simp : a ∈ ({a, b, c} : Set M)))
      have h2 := (AddSubgroup.toZModSubmodule 2 (AddSubgroup.closure ({a, b, c} : Set M))).smul_mem
        (v 1) (AddSubgroup.subset_closure (by simp : b ∈ ({a, b, c} : Set M)))
      exact AddSubgroup.add_mem _ h1 h2
  rw [hrange]
  have : Nat.card φ.range = Nat.card (Fin 2 → ZMod 2) :=
    Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv.symm
  rw [this]
  simp [Nat.card_fun, Nat.card_zmod]

instance (k : Fin 2) (y : V4) : Decidable (linePred k y) :=
  match k with
  | 0 => inferInstanceAs (Decidable (predLine4a y))
  | 1 => inferInstanceAs (Decidable (predLine4b y))

@[expose] def T5 : Fin 2 → Fin 2 → Perm (Fin 6)
  | 0 => T5_0
  | 1 => T5_1

@[expose] def uL (k : Fin 2) : Fin 3 → Fn :=
  ![U2gen k, fun w => U2gen k (Matrix.mulVec (Rm k (T5 k 0)⁻¹) w),
    fun w => U2gen k (Matrix.mulVec (Rm k (T5 k 1)⁻¹) w)]

theorem U2gen_notin : ∀ k : Fin 2, ∀ x : V4, ∃ w : V4, U2gen k w ≠ Cf x w :=
  Part5Pack.U2gen_notin_code

theorem uL_notin : ∀ k : Fin 2, ∀ i : Fin 3, ∀ x : V4, ∃ w : V4, uL k i w ≠ Cf x w := by
  rw [Fin.forall_fin_two]
  exact ⟨Part5Pack.uA_notin, Part5Pack.uB_notin⟩

theorem uL_sum : ∀ k : Fin 2, ∀ w : V4, uL k 0 w + uL k 1 w + uL k 2 w = Cf (x0 k) w := by
  rw [Fin.forall_fin_two]
  exact ⟨Part5Pack.uA_sum, Part5Pack.uB_sum⟩

theorem uL_pair : ∀ k : Fin 2, ∀ i j : Fin 3, i ≠ j → ∀ x : V4,
    ∃ w : V4, uL k i w + uL k j w ≠ Cf x w := by
  rw [Fin.forall_fin_two]
  exact ⟨Part5Pack.uA_pair, Part5Pack.uB_pair⟩

theorem T5_prop : ∀ k : Fin 2, ∀ i : Fin 2, Perm.sign (T5 k i) = 1 ∧
    ∀ y : V4, linePred (1 - k) y → linePred (1 - k) (Matrix.mulVec (Rm (1 - k) (T5 k i)) y) := by
  rw [Fin.forall_fin_two]
  exact ⟨Part5Pack.T5_0_prop, Part5Pack.T5_1_prop⟩

theorem Hl_orbit : ∀ k : Fin 2, ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    (∀ y : V4, linePred (1 - k) y → linePred (1 - k) (Matrix.mulVec (Rm (1 - k) σ) y)) →
    ∃ i : Fin 3, ∀ w : V4, U2gen k (Matrix.mulVec (Rm k σ⁻¹) w) = uL k i w := by
  rw [Fin.forall_fin_two]
  exact ⟨Part5Pack.orbit0, Part5Pack.orbit1⟩

theorem Hx_fix : ∀ k : Fin 2, ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    Matrix.mulVec (Rm (1 - k) σ) (x0 (1 - k)) = x0 (1 - k) →
    ∀ w : V4, U2gen k (Matrix.mulVec (Rm k σ⁻¹) w) = U2gen k w := by
  rw [Fin.forall_fin_two]
  exact ⟨Part5Pack.fix0, Part5Pack.fix1⟩


theorem N4_le_N2' (k : Fin 2) : Nk k 4 ≤ Nk k 2 := (N4_le_N3 k).trans (N3_le_N2 k)

theorem cover5_of_six (six : SixStmt) (k : Fin 2) :
    ∃ (C : Md ↥(alternatingGroup (Fin 6))) (π : ↥(Nk k 2) →+ C.carrier),
      Function.Surjective π ∧ (∀ n : ↥(Nk k 2), π n = 0 ↔ (n : Fn) ∈ Nk k 4) ∧
      (∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 2)),
        π ⟨permAct (Mk k) g n, N2_inv k g n n.2⟩ = C.ρ g (π n)) ∧
      C.IsFiveDimCover (Mk (1 - k)) := by
  obtain ⟨C, π, hs, hk, hρ⟩ := exists_quot_md (permRep (Mk k)) (N2_inv k) (N4_inv k) (N4_le_N2' k)
  refine ⟨C, π, hs, hk, hρ, ?_⟩
  have hcard : Nat.card C.carrier = 2 ^ 5 := by
    have h := card_eq_mul_of_quot (N4_le_N2' k) π hs hk
    rw [card_N2, card_N4] at h
    omega
  have hn₀ : U2gen k ∈ Nk k 2 := U2gen_mem k
  let w : C.carrier := π ⟨U2gen k, hn₀⟩
  have hact : ∀ g : ↥(alternatingGroup (Fin 6)),
      C.ρ g w = π ⟨permAct (Mk k) g (U2gen k), N2_inv k g _ hn₀⟩ :=
    fun g => (hρ g ⟨U2gen k, hn₀⟩).symm
  have hdbl : ∀ x : C.carrier, x + x = 0 := fun x => by
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [← two_smul (ZMod 2) x, h2, zero_smul]
  have hw0 : w ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := (hk ⟨U2gen k, hn₀⟩).mp h
    obtain ⟨w', hw'⟩ := U2gen_notin k x
    exact hw' (congrFun hx w').symm
  have hfix : ∀ h : ↥(alternatingGroup (Fin 6)), ρk (1 - k) h (x0 (1 - k)) = x0 (1 - k) →
      C.ρ h w = w := by
    intro h hh
    rw [hact]
    have hh' : Matrix.mulVec (Rm (1 - k) (h : Perm (Fin 6))) (x0 (1 - k)) = x0 (1 - k) := by
      rw [← ρk_apply]
      exact hh
    have hperm : permAct (Mk k) h (U2gen k) = U2gen k := by
      funext w'
      show U2gen k (ρk k h⁻¹ w') = U2gen k w'
      rw [ρk_apply]
      exact Hx_fix k h (Perm.mem_alternatingGroup.mp h.2) hh' w'
    exact congrArg π (Subtype.ext hperm)
  have hgen : AddSubgroup.closure
      (Set.range fun g : ↥(alternatingGroup (Fin 6)) => C.ρ g w) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨⟨n, hn⟩, rfl⟩ := hs c
    have key : ∀ x ∈ AddSubgroup.closure (Set.range fun h : ↥(alternatingGroup (Fin 6)) =>
        permRep (Mk k) h (U2gen k)), ∃ hx : x ∈ Nk k 2,
        π ⟨x, hx⟩ ∈ AddSubgroup.closure (Set.range fun g : ↥(alternatingGroup (Fin 6)) =>
          C.ρ g w) := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        refine ⟨N2_inv k g _ hn₀, ?_⟩
        have h1 : C.ρ g w ∈ AddSubgroup.closure
            (Set.range fun g' : ↥(alternatingGroup (Fin 6)) => C.ρ g' w) :=
          AddSubgroup.subset_closure ⟨g, rfl⟩
        rw [hact g] at h1
        exact h1
      | zero =>
        refine ⟨(Nk k 2).zero_mem, ?_⟩
        have h0 : (⟨0, (Nk k 2).zero_mem⟩ : ↥(Nk k 2)) = 0 := rfl
        rw [h0, map_zero]
        exact AddSubgroup.zero_mem _
      | add x y hx hy ihx ihy =>
        obtain ⟨hxN, hxS⟩ := ihx
        obtain ⟨hyN, hyS⟩ := ihy
        refine ⟨(Nk k 2).add_mem hxN hyN, ?_⟩
        have h1 : (⟨x + y, (Nk k 2).add_mem hxN hyN⟩ : ↥(Nk k 2)) = ⟨x, hxN⟩ + ⟨y, hyN⟩ := rfl
        rw [h1, map_add]
        exact AddSubgroup.add_mem _ hxS hyS
      | neg x hx ihx =>
        obtain ⟨hxN, hxS⟩ := ihx
        refine ⟨(Nk k 2).neg_mem hxN, ?_⟩
        have h1 : (⟨-x, (Nk k 2).neg_mem hxN⟩ : ↥(Nk k 2)) = -⟨x, hxN⟩ := rfl
        rw [h1, map_neg]
        exact AddSubgroup.neg_mem _ hxS
    obtain ⟨_, h⟩ := key n (gen2 k n hn)
    exact h
  let gT : Fin 2 → ↥(alternatingGroup (Fin 6)) := fun i =>
    ⟨T5 k i, Perm.mem_alternatingGroup.mpr (T5_prop k i).1⟩
  have hgT : ∀ i : Fin 2, ∀ y : V4, linePred (1 - k) y →
      linePred (1 - k) (ρk (1 - k) (gT i) y) := fun i y hy => by
    rw [ρk_apply]
    exact (T5_prop k i).2 y hy
  have hpa : ∀ i : Fin 2, permAct (Mk k) (gT i) (U2gen k) = uL k i.succ := fun i => by
    funext w'
    show U2gen k (ρk k (gT i)⁻¹ w') = _
    rw [ρk_apply]
    fin_cases i <;> rfl
  have hmemL : ∀ i : Fin 3, uL k i ∈ Nk k 2 := by
    intro i
    fin_cases i
    · exact hn₀
    · have h := N2_inv k (gT 0) _ hn₀
      rw [hpa 0] at h
      exact h
    · have h := N2_inv k (gT 1) _ hn₀
      rw [hpa 1] at h
      exact h
  let a : Fin 3 → C.carrier := fun i => π ⟨uL k i, hmemL i⟩
  have hact' : ∀ (g : ↥(alternatingGroup (Fin 6))) (i : Fin 3),
      permAct (Mk k) g (U2gen k) = uL k i → C.ρ g w = a i := fun g i h => by
    rw [hact g]
    exact congrArg π (Subtype.ext h)
  have ha0w : a 0 = w := rfl
  have hCf : Cf (x0 k) ∈ Nk k 2 := N4_le_N2' k (Cf_mem_N4 k _)
  have ha0 : a 0 ≠ 0 := hw0
  have ha1 : a 1 ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := (hk ⟨uL k 1, hmemL 1⟩).mp h
    obtain ⟨w', hw'⟩ := uL_notin k 1 x
    exact hw' (congrFun hx w').symm
  have ha01 : a 0 ≠ a 1 := by
    intro h
    have h2 : a 0 + a 1 = 0 := by
      rw [← h]
      exact hdbl _
    have h3 : π (⟨uL k 0, hmemL 0⟩ + ⟨uL k 1, hmemL 1⟩) = 0 := by
      rw [map_add]
      exact h2
    obtain ⟨x, hx⟩ := (hk _).mp h3
    obtain ⟨w', hw'⟩ := uL_pair k 0 1 (by decide) x
    exact hw' (congrFun hx w').symm
  have hsum : a 0 + a 1 + a 2 = 0 := by
    have h1 : (⟨uL k 0, hmemL 0⟩ + ⟨uL k 1, hmemL 1⟩ + ⟨uL k 2, hmemL 2⟩ : ↥(Nk k 2)) =
        ⟨Cf (x0 k), hCf⟩ :=
      Subtype.ext (funext fun w' => uL_sum k w')
    have h2 : π ⟨Cf (x0 k), hCf⟩ = 0 := (hk _).mpr (Cf_mem_N4 k _)
    rw [← h1, map_add, map_add] at h2
    exact h2
  have hrange : Set.range (fun g : {h : ↥(alternatingGroup (Fin 6)) //
      ∀ y : V4, linePred (1 - k) y → linePred (1 - k) (ρk (1 - k) h y)} =>
        C.ρ (g : ↥(alternatingGroup (Fin 6))) w) = {a 0, a 1, a 2} := by
    ext x
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨i, hi⟩ := Hl_orbit k g (Perm.mem_alternatingGroup.mp g.2) (fun y hy => by
        have := hg y hy
        rwa [ρk_apply] at this)
      have hperm : permAct (Mk k) g (U2gen k) = uL k i := funext fun w' => by
        show U2gen k (ρk k g⁻¹ w') = uL k i w'
        rw [ρk_apply]
        exact hi w'
      have h1 := hact' g i hperm
      show C.ρ g w ∈ ({a 0, a 1, a 2} : Set C.carrier)
      rw [h1]
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨1, fun y hy => by simpa using hy⟩, by
          show C.ρ 1 w = a 0
          rw [map_one]
          rfl⟩
      · exact ⟨⟨gT 0, hgT 0⟩, hact' (gT 0) 1 (hpa 0)⟩
      · exact ⟨⟨gT 1, hgT 1⟩, hact' (gT 1) 2 (hpa 1)⟩
  have hline : Nat.card ↥(AddSubgroup.closure (Set.range
      fun g : {h : ↥(alternatingGroup (Fin 6)) //
        ∀ y : V4, linePred (1 - k) y → linePred (1 - k) (ρk (1 - k) h y)} =>
        C.ρ (g : ↥(alternatingGroup (Fin 6))) w)) = 4 := by
    rw [hrange]
    exact card_closure_klein (a 0) (a 1) (a 2) ha0 ha1 ha01 hsum
  rcases six (1 - k) C w hw0 hfix hgen hline with h | h
  · exfalso
    obtain ⟨f, -⟩ := h
    have h1 : Nat.card C.carrier = Nat.card V4 := Nat.card_congr f.toEquiv
    rw [hcard, card_V4] at h1
    omega
  · exact h

end CFSG.Quasithin.ShultG53
