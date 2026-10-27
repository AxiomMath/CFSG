module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModK

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

theorem mem_spanX {P : ℕ → Prop} (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b))
    {l : List ℕ} (hl : ∀ g ∈ l, P g) : ∀ x ∈ spanX l, P x := by
  have key : ∀ (l : List ℕ), (∀ g ∈ l, P g) → ∀ acc : List ℕ, (∀ x ∈ acc, P x) →
      ∀ x ∈ l.foldl (fun acc g => if acc.contains g then acc else acc ++ acc.map (· ^^^ g)) acc,
        P x := by
    intro l
    induction l with
    | nil => intro _ acc hacc x hx; exact hacc x hx
    | cons g gs ih =>
      intro hl acc hacc
      rw [List.foldl_cons]
      apply ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
      intro x hxm
      split_ifs at hxm
      · exact hacc x hxm
      · rcases List.mem_append.1 hxm with h1 | h1
        · exact hacc x h1
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h1
          exact hx _ _ (hacc a ha) (hl g (List.mem_cons_self))
  exact key l hl [0] (by simpa using h0)

theorem mem_closureM {P : Mc → Prop} (hone : P Mc.one) (hmul : ∀ x y, P x → P y → P (x.mul y))
    {gens : List Mc} (hg : ∀ g ∈ gens, P g) : ∀ x ∈ closureM gens, P x := by
  have inner : ∀ x, P x → ∀ (gs : List Mc), (∀ g ∈ gs, P g) →
      ∀ sn : Array Bool × List Mc, (∀ y ∈ sn.2, P y) → ∀ y ∈ (bfsAdd gs sn x).2, P y := by
    intro x hx gs
    induction gs with
    | nil => intro _ sn hsn y hy; exact hsn y hy
    | cons g gs ih =>
      intro hgs sn hsn
      simp only [bfsAdd, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      split_ifs
      · exact hsn
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hmul _ _ hx (hgs g List.mem_cons_self)
        · exact hsn y hy
  have outer : ∀ (fr : List Mc), (∀ x ∈ fr, P x) → ∀ sn : Array Bool × List Mc,
      (∀ y ∈ sn.2, P y) → ∀ y ∈ (fr.foldl (bfsAdd gens) sn).2, P y := by
    intro fr
    induction fr with
    | nil => intro _ sn hsn y hy; exact hsn y hy
    | cons x xs ih =>
      intro hfr sn hsn
      rw [List.foldl_cons]
      exact ih (fun x' hx' => hfr x' (List.mem_cons_of_mem _ hx'))
        _ (inner x (hfr x List.mem_cons_self) gens hg sn hsn)
  have step : ∀ st : Array Bool × List Mc × List Mc, (∀ x ∈ st.2.1, P x) →
      (∀ x ∈ st.2.2, P x) →
      (∀ x ∈ (bfsStep gens st).2.1, P x) ∧ (∀ x ∈ (bfsStep gens st).2.2, P x) := by
    intro st hacc hfr
    have hnext := outer st.2.2 hfr (st.1, []) (by simp)
    refine ⟨fun y hy => ?_, fun y hy => hnext y hy⟩
    rcases List.mem_append.1 hy with h1 | h1
    · exact hacc y h1
    · exact hnext y h1
  have hbfs : ∀ n (st : Array Bool × List Mc × List Mc), (∀ x ∈ st.2.1, P x) →
      (∀ x ∈ st.2.2, P x) → ∀ x ∈ bfs gens n st, P x := by
    intro n
    induction n with
    | zero => intro st hacc _; exact hacc
    | succ n ih =>
      intro st hacc hfr
      simp only [bfs]
      split_ifs
      · exact hacc
      · obtain ⟨h1, h2⟩ := step st hacc hfr
        exact ih _ h1 h2
  exact hbfs 64 _ (by simpa using hone) (by simpa using hone)

theorem mem_of_spanHas {l ds : List ℕ} (h : spanHas l ds = true) : ∀ d ∈ ds, d ∈ spanX l := by
  simpa [spanHas, List.all_eq_true] using h

theorem mem_of_genAll {gens : List Mc} (h : genAll gens = true) :
    ∀ g ∈ gmList, g ∈ closureM gens := by
  simpa [genAll, List.all_eq_true] using h

@[expose] def wA : Mc := ⟨32, 42, 8⟩

@[expose] def wB : Mc := ⟨1, 12, 39⟩

theorem wA_facts : wA.Valid ∧ inGm wA = true ∧ presv p1c wA.toB6 = true ∧
    presv l2c wA.toB6 = false := by decide

theorem wB_facts : wB.Valid ∧ inGm wB = true ∧ presv l2c wB.toB6 = true ∧
    presv p1c wB.toB6 = false := by decide

theorem s0m_presv : ∀ s ∈ s0m, s.Valid ∧ presv p1c s.toB6 = true ∧ presv l2c s.toB6 = true := by
  decide

theorem dreps_inGm : ∀ r ∈ dreps, r.Valid ∧ inGm r = true := by decide

theorem presv_comp {l : List ℕ} {B D : B6} (hB : presv l B = true) (hD : presv l D = true) :
    presv l (B.comp D) = true := by
  rw [presv_iff] at hB hD ⊢
  intro c hc
  rw [B6.app_comp]
  exact hB _ (hD c hc)

section Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem dc_app_mem (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V)
    {C : Coding ↥V} (hC : Std C T L) {W : Subgroup G}
    (hPW : P1 T L V ≤ Subgroup.normalizer (W : Set G)) {c : ℕ} (hc : c < 64)
    (hcW : (C.dc c : G) ∈ W) {B : B6} (hB : B ∈ gm6.filter (presv p1c)) :
    (C.dc (B.app c) : G) ∈ W := by
  rw [List.mem_filter] at hB
  obtain ⟨a, rfl⟩ := hC.1.2 B hB.1
  have ha : a ∈ autOn (P1 T L V) V := by
    rw [P1, V1_eq h hC]
    exact (mem_autOn_Pof h1222 h hC.1 p1c_lt a).2 hB
  obtain ⟨x, hx, hxP, rfl⟩ := mem_autOn'.1 ha
  have hm := (Subgroup.mem_normalizer_iff.1 (hPW hxP) _).1 hcW
  have e := cd_conj C hx (C.dc c)
  rw [C.cd_dc c hc] at e
  rw [← e, C.dc_cd]
  exact hm

omit [Finite G] in
theorem dc_spanX_mem {C : Coding ↥V} {W : Subgroup G} {l : List ℕ}
    (hl : ∀ g ∈ l, g < 64 ∧ (C.dc g : G) ∈ W) : ∀ x ∈ spanX l, x < 64 ∧ (C.dc x : G) ∈ W :=
  mem_spanX (P := fun c => c < 64 ∧ (C.dc c : G) ∈ W)
    ⟨by norm_num, by rw [C.dc_zero]; exact W.one_mem⟩
    (fun _ _ ha hb => ⟨xor_lt_64' ha.1 hb.1, by
      rw [C.dc_xor ha.1 hb.1]
      exact W.mul_mem ha.2 hb.2⟩) hl

theorem card_V1 (h : Hyp1271 G T L V) {C : Coding ↥V}
    (hC : Std C T L) : Nat.card (V1 T L V) = 4 := by
  rw [V1_eq h hC, C.card_subG p1c_nodup p1c_lt]
  rfl

theorem lemma12_7_2_three
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    IsIrredOnSection (P1 T L V) V (V1 T L V) ∧ IsIrredOnSection (P1 T L V) (V1 T L V) ⊥ := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hV1 := V1_eq h hC
  have hPN := pof_le_normalizer h1222 h (V1 T L V)
  have hV1V : V1 T L V ≤ V := inf_le_left
  have hc4 := card_V1 h hC
  have hdcV1 : ∀ g ∈ p1c, (C.dc g : G) ∈ V1 T L V := fun g hg => by
    rw [hV1, C.mem_subG, C.cd_dc g (p1c_lt g hg)]
    exact hg
  refine ⟨⟨lt_of_le_of_ne hV1V fun e => ?_, hPN, inf_le_right, fun W hV1W hWV hPW => ?_⟩,
    ⟨bot_lt_iff_ne_bot.2 fun e => ?_, inf_le_right, fun x _ => ?_, fun W _ hWV1 hPW => ?_⟩⟩
  · have := card_V h1222 h
    rw [e] at hc4
    rw [hc4] at this
    norm_num at this
  · by_cases hW : W ≤ V1 T L V
    · exact Or.inl (le_antisymm hW hV1W)
    · right
      obtain ⟨w, hwW, hwV1⟩ := IsConcreteLE.not_le_iff_exists.1 hW
      have hwV := hWV hwW
      set c := C.cd ⟨w, hwV⟩ with hcdef
      have hc : c ∉ p1c := fun hc => hwV1 (by
        rw [hV1]
        exact (C.mem_subG ⟨w, hwV⟩).2 hc)
      have hcW : (C.dc c : G) ∈ W := by rw [hcdef, C.dc_cd]; exact hwW
      have hall := mem_of_spanHas (cert_irr1 c (List.mem_range.2 (C.cd_lt _)) hc)
      have hspan := dc_spanX_mem (C := C) (W := W)
        (l := p1c ++ (gm6.filter (presv p1c)).map (·.app c)) (by
          intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact ⟨p1c_lt g hg, hV1W (hdcV1 g hg)⟩
          · obtain ⟨B, hB, rfl⟩ := List.mem_map.1 hg
            exact ⟨B6.app_lt (gm6_valid B (List.mem_filter.1 hB).1) c,
              dc_app_mem h1222 h hC hPW (C.cd_lt _) hcW hB⟩)
      apply le_antisymm hWV
      intro v hv
      have := (hspan _ (hall _ (List.mem_range.2 (C.cd_lt ⟨v, hv⟩)))).2
      rwa [C.dc_cd] at this
  · rw [e] at hc4
    simp at hc4
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro hg
      have := congrArg (fun y => x⁻¹ * y * x) hg
      simpa [mul_assoc] using this
  · by_cases hW : W = ⊥
    · exact Or.inl hW
    · right
      obtain ⟨⟨w, hwW⟩, hw1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
      have hw1 : w ≠ 1 := fun e => hw1' (Subtype.ext e)
      have hwV1 := hWV1 hwW
      have hwV := hV1V hwV1
      set c := C.cd ⟨w, hwV⟩ with hcdef
      have hc : c ∈ p1c := by
        rw [hV1] at hwV1
        exact (C.mem_subG ⟨w, hwV⟩).1 hwV1
      have hc0 : c ≠ 0 := fun h0 => hw1 (by
        have := (C.cd_eq_zero (v := ⟨w, hwV⟩)).1 h0
        simpa using congrArg Subtype.val this)
      have hcW : (C.dc c : G) ∈ W := by rw [hcdef, C.dc_cd]; exact hwW
      have hall := mem_of_spanHas (cert_irr2 c hc hc0)
      have hspan := dc_spanX_mem (C := C) (W := W)
        (l := (gm6.filter (presv p1c)).map (·.app c)) (by
          intro g hg
          obtain ⟨B, hB, rfl⟩ := List.mem_map.1 hg
          exact ⟨B6.app_lt (gm6_valid B (List.mem_filter.1 hB).1) c,
            dc_app_mem h1222 h hC (fun x hx => hPW hx) (C.cd_lt _) hcW hB⟩)
      apply le_antisymm hWV1
      intro v hv
      have hvV := hV1V hv
      have hcv : C.cd ⟨v, hvV⟩ ∈ p1c := by
        rw [hV1] at hv
        exact (C.mem_subG ⟨v, hvV⟩).1 hv
      have := (hspan _ (hall _ hcv)).2
      rwa [C.dc_cd] at this

end Setting

end CFSG.Quasithin.H13.S127.Mod

end
