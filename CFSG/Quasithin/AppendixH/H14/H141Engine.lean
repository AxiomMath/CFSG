module

public import CFSG.Quasithin.AppendixH.H14.H141Table
public import CFSG.Quasithin.AppendixH.H14.H141Lin
public import CFSG.Quasithin.AppendixH.H14.H142Conj
public import CFSG.Quasithin.AppendixH.H14.H142Group

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

structure EngineHyp (tab : Array (Array ℕ)) (hT : tab64OK tab = true) (M : Subgroup S24)
    (gens : List (Array ℕ)) (gm : List ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop where
  le : tab64Sub tab hT ≤ M
  gens_mem : ∀ a ∈ gens, inAutOK a = true ∧ ∃ σ ∈ M, HasArr σ a
  len : gm.length = gens.length
  act : ∀ j < gens.length, ∀ n < 64, cmap64 tab gens[j]! n = linAct (gm.getD j 0) n
  bfs : sbfsOK gm L = true
  card : Nat.card ↥M ≤ L.length * 64

variable {tab : Array (Array ℕ)} {hT : tab64OK tab = true} {M : Subgroup S24}
  {gens : List (Array ℕ)} {gm : List ℕ} {L : List (ℕ × ℕ × ℕ)}

def bfsSt (L : List (ℕ × ℕ × ℕ)) (k : ℕ) : ℕ := (L.map Prod.fst).getD k idSt

theorem EngineHyp.gen_conj (h : EngineHyp tab hT M gens gm L) {j : ℕ} (hj : j < gens.length) :
    ∃ σ ∈ M, ∀ n < 64,
      σ * tab64Perm tab n * σ⁻¹ = tab64Perm tab (linAct (gm.getD j 0) n) := by
  have hjm : gens[j]! ∈ gens := by
    rw [getElem!_pos gens j hj]
    exact List.getElem_mem hj
  obtain ⟨hok, σ, hσM, hσarr⟩ := h.gens_mem (gens[j]!) hjm
  refine ⟨σ, hσM, fun n hn => ?_⟩
  have hlt : cmap64 tab gens[j]! n < 64 := by
    rw [h.act j hj n hn]
    exact linAct_lt _ _
  rw [conj_tab64Perm hT hσarr hok hn hlt, h.act j hj n hn]

theorem EngineHyp.rep (h : EngineHyp tab hT M gens gm L) {st : ℕ} (hst : StReach gm st) :
    ∃ g ∈ M, ∀ n < 64, g * tab64Perm tab n * g⁻¹ = tab64Perm tab (linAct st n) := by
  refine StReach.rec (motive := fun st _ => ∃ g ∈ M, ∀ n < 64,
      g * tab64Perm tab n * g⁻¹ = tab64Perm tab (linAct st n)) ?_ ?_ hst
  · exact ⟨1, M.one_mem, fun n hn => by rw [one_mul, inv_one, mul_one, linAct_idSt hn]⟩
  · intro j s hj hs ih
    obtain ⟨g, hgM, hgact⟩ := ih
    have hjlen : j < gens.length := by rw [← h.len]; exact hj
    obtain ⟨σ, hσM, hσconj⟩ := h.gen_conj hjlen
    refine ⟨σ * g, M.mul_mem hσM hgM, fun n hn => ?_⟩
    have hnlt : linAct s n < 64 := linAct_lt s n
    calc (σ * g) * tab64Perm tab n * (σ * g)⁻¹
        = σ * (g * tab64Perm tab n * g⁻¹) * σ⁻¹ := by group
      _ = σ * tab64Perm tab (linAct s n) * σ⁻¹ := by rw [hgact n hn]
      _ = tab64Perm tab (linAct (gm.getD j 0) (linAct s n)) := hσconj (linAct s n) hnlt
      _ = tab64Perm tab (linAct (compSt (gm.getD j 0) s) n) := by rw [linAct_compSt]

theorem EngineHyp.decomp (h : EngineHyp tab hT M gens gm L) :
    ∀ x ∈ M, ∃ st ∈ L.map Prod.fst, ∃ g ∈ M, ∃ e ∈ tab64Sub tab hT,
      x = g * e ∧ (st = idSt → g = 1) ∧
        ∀ n < 64, g * tab64Perm tab n * g⁻¹ = tab64Perm tab (linAct st n) := by
  classical
  have hsound := sbfsOK_sound h.bfs
  have hLne : L ≠ [] := by
    intro hnil
    have h1 := hsound.1
    rw [hnil] at h1
    simp at h1
  have hNpos : 0 < L.length := List.length_pos_iff.mpr hLne
  have hhead0 : bfsSt L 0 = idSt := by
    simp only [bfsSt]
    cases hL : L with
    | nil => exact absurd hL hLne
    | cons e es =>
        have he1 : e.1 = idSt := by
          have h1 := hsound.1
          rw [hL] at h1
          simpa using h1
        rw [List.map_cons, List.getD_cons_zero]
        exact he1
  have hstAt_mem : ∀ k (hk : k < L.length), bfsSt L k ∈ L.map Prod.fst := by
    intro k hk
    have hlt : k < (L.map Prod.fst).length := by simpa using hk
    have hmem : bfsSt L k = (L.map Prod.fst)[k]'hlt := by
      simp only [bfsSt]
      exact List.getD_eq_getElem (l := L.map Prod.fst) (d := idSt) hlt
    rw [hmem]
    exact List.getElem_mem hlt
  have hstAt_reach : ∀ k (hk : k < L.length), StReach gm (bfsSt L k) := by
    intro k hk
    obtain ⟨e, he, he1⟩ := List.mem_map.mp (hstAt_mem k hk)
    rw [← he1]
    exact hsound.2.2 e he
  have hstAt_exists : ∀ k (hk : k < L.length),
      ∃ g ∈ M, ∀ n < 64, g * tab64Perm tab n * g⁻¹ = tab64Perm tab (linAct (bfsSt L k) n) :=
    fun k hk => h.rep (hstAt_reach k hk)
  have hstAt_inj : ∀ k k' (hk : k < L.length) (hk' : k' < L.length),
      bfsSt L k = bfsSt L k' → k = k' := by
    intro k k' hk hk' heq
    have hlt : k < (L.map Prod.fst).length := by simpa using hk
    have hlt' : k' < (L.map Prod.fst).length := by simpa using hk'
    have hrow : (L.map Prod.fst)[k]'hlt = (L.map Prod.fst)[k']'hlt' := by
      rw [← List.getD_eq_getElem (l := L.map Prod.fst) (d := idSt) hlt,
          ← List.getD_eq_getElem (l := L.map Prod.fst) (d := idSt) hlt']
      exact heq
    exact (List.Nodup.getElem_inj_iff hsound.2.1).mp hrow
  let g : Fin L.length → S24 := fun k =>
    if hk : (k : ℕ) = 0 then 1 else Classical.choose (hstAt_exists (k : ℕ) k.2)
  have hg : ∀ k : Fin L.length, g k ∈ M ∧
      ∀ n < 64, g k * tab64Perm tab n * (g k)⁻¹ =
        tab64Perm tab (linAct (bfsSt L (k : ℕ)) n) := by
    intro k
    by_cases hk : (k : ℕ) = 0
    · have hst0 : bfsSt L (k : ℕ) = idSt := by rw [hk]; exact hhead0
      have hg1 : g k = 1 := by
        show (if hk' : (k : ℕ) = 0 then (1 : S24)
          else Classical.choose (hstAt_exists (k : ℕ) k.2)) = 1
        rw [dif_pos hk]
      refine ⟨?_, fun n hn => ?_⟩
      · rw [hg1]; exact M.one_mem
      · rw [hg1, one_mul, inv_one, mul_one, hst0, linAct_idSt hn]
    · have hspec := Classical.choose_spec (hstAt_exists (k : ℕ) k.2)
      have hgne : g k = Classical.choose (hstAt_exists (k : ℕ) k.2) := by
        show (if hk' : (k : ℕ) = 0 then (1 : S24)
          else Classical.choose (hstAt_exists (k : ℕ) k.2)) =
            Classical.choose (hstAt_exists (k : ℕ) k.2)
        rw [dif_neg hk]
      rw [hgne]
      exact hspec
  let act : S24 → (Fin 64 → S24) := fun x n => x * tab64Perm tab (n : ℕ) * x⁻¹
  have hact : ∀ k : Fin L.length, ∀ e ∈ tab64Sub tab hT, act (g k * e) = act (g k) := by
    intro k e he
    rw [mem_tab64Sub hT] at he
    obtain ⟨m, hm, rfl⟩ := he
    funext n
    dsimp only [act]
    have hc : tab64Perm tab m * tab64Perm tab (n : ℕ) * (tab64Perm tab m)⁻¹
        = tab64Perm tab (n : ℕ) := by
      rw [tab64Perm_comm hT hm n.2]
      group
    calc (g k * tab64Perm tab m) * tab64Perm tab (n : ℕ) * (g k * tab64Perm tab m)⁻¹
        = g k * (tab64Perm tab m * tab64Perm tab (n : ℕ) * (tab64Perm tab m)⁻¹) *
            (g k)⁻¹ := by group
      _ = g k * tab64Perm tab (n : ℕ) * (g k)⁻¹ := by rw [hc]
  have hinj : Function.Injective (fun k : Fin L.length => act (g k)) := by
    intro k k' hkk
    have hkey : ∀ n < 64, linAct (bfsSt L (k : ℕ)) n = linAct (bfsSt L (k' : ℕ)) n := by
      intro n hn
      have h1 := (hg k).2 n hn
      have h2 := (hg k').2 n hn
      have h3 : tab64Perm tab (linAct (bfsSt L (k : ℕ)) n)
          = tab64Perm tab (linAct (bfsSt L (k' : ℕ)) n) := by
        rw [← h1, ← h2]
        have := congrFun hkk ⟨n, hn⟩
        dsimp only [act] at this
        exact this
      exact tab64Perm_inj hT (linAct_lt _ _) (linAct_lt _ _) h3
    have hcol : ∀ i < 6, col (bfsSt L (k : ℕ)) i = col (bfsSt L (k' : ℕ)) i := by
      intro i hi
      have h2i : 2 ^ i < 64 := by interval_cases i <;> norm_num
      have := hkey (2 ^ i) h2i
      rwa [linAct_two_pow _ hi, linAct_two_pow _ hi] at this
    have hst : bfsSt L (k : ℕ) = bfsSt L (k' : ℕ) :=
      eq_of_col_eq (StReach.lt (hstAt_reach (k : ℕ) k.2))
        (StReach.lt (hstAt_reach (k' : ℕ) k'.2)) hcol
    exact Fin.ext (hstAt_inj (k : ℕ) (k' : ℕ) k.2 k'.2 hst)
  have hcard : Nat.card ↥M ≤ L.length * Nat.card ↥(tab64Sub tab hT) := by
    rw [card_tab64Sub hT]
    exact h.card
  intro x hx
  obtain ⟨k, e, he, hxeq⟩ := exists_mul_of_card_le (M := M) (E := tab64Sub tab hT)
    (N := L.length) (g := g) (act := act) (fun k => (hg k).1) h.le hact hinj hcard x hx
  refine ⟨bfsSt L (k : ℕ), hstAt_mem (k : ℕ) k.2, g k, (hg k).1, e, he, hxeq, ?_, (hg k).2⟩
  intro hstid
  by_cases hk0 : (k : ℕ) = 0
  · show g k = 1
    show (if hk' : (k : ℕ) = 0 then (1 : S24)
      else Classical.choose (hstAt_exists (k : ℕ) k.2)) = 1
    rw [dif_pos hk0]
  · exfalso
    exact hk0 (hstAt_inj (k : ℕ) 0 k.2 hNpos (by rw [hstid, hhead0]))

theorem EngineHyp.normal (h : EngineHyp tab hT M gens gm L) :
    ∀ g ∈ M, ∀ e ∈ tab64Sub tab hT, g * e * g⁻¹ ∈ tab64Sub tab hT := by
  intro g hg e he
  obtain ⟨st, -, g₀, -, e₀, he₀, hgeq, -, hact⟩ := h.decomp g hg
  obtain ⟨m, hm, rfl⟩ := (mem_tab64Sub hT).mp he
  rw [hgeq]
  have hconj : e₀ * tab64Perm tab m * e₀⁻¹ = tab64Perm tab m := by
    obtain ⟨l, hl, rfl⟩ := (mem_tab64Sub hT).mp he₀
    rw [tab64Perm_comm hT hl hm]
    group
  have hfinal : (g₀ * e₀) * tab64Perm tab m * (g₀ * e₀)⁻¹ =
      tab64Perm tab (linAct st m) := by
    calc (g₀ * e₀) * tab64Perm tab m * (g₀ * e₀)⁻¹
        = g₀ * (e₀ * tab64Perm tab m * e₀⁻¹) * g₀⁻¹ := by group
      _ = g₀ * tab64Perm tab m * g₀⁻¹ := by rw [hconj]
      _ = tab64Perm tab (linAct st m) := hact m hm
  rw [hfinal]
  exact tab64Perm_mem_tab64Sub hT (linAct_lt st m)

theorem EngineHyp.action (h : EngineHyp tab hT M gens gm L) :
    ∀ x ∈ M, ∃ st ∈ L.map Prod.fst,
      ∀ n < 64, x * tab64Perm tab n * x⁻¹ = tab64Perm tab (linAct st n) := by
  intro x hx
  obtain ⟨st, hstL, g₀, -, e₀, he₀, hxeq, -, hact⟩ := h.decomp x hx
  refine ⟨st, hstL, fun n hn => ?_⟩
  rw [hxeq]
  have hconj : e₀ * tab64Perm tab n * e₀⁻¹ = tab64Perm tab n := by
    obtain ⟨l, hl, rfl⟩ := (mem_tab64Sub hT).mp he₀
    rw [tab64Perm_comm hT hl hn]
    group
  calc (g₀ * e₀) * tab64Perm tab n * (g₀ * e₀)⁻¹
      = g₀ * (e₀ * tab64Perm tab n * e₀⁻¹) * g₀⁻¹ := by group
    _ = g₀ * tab64Perm tab n * g₀⁻¹ := by rw [hconj]
    _ = tab64Perm tab (linAct st n) := hact n hn

theorem EngineHyp.realize (h : EngineHyp tab hT M gens gm L) :
    ∀ st ∈ L.map Prod.fst, ∃ x ∈ M,
      ∀ n < 64, x * tab64Perm tab n * x⁻¹ = tab64Perm tab (linAct st n) := by
  intro st hst
  obtain ⟨e, he, he1⟩ := List.mem_map.mp hst
  have hreach : StReach gm st := by
    rw [← he1]
    exact (sbfsOK_sound h.bfs).2.2 e he
  exact h.rep hreach

theorem EngineHyp.selfCentralizing (h : EngineHyp tab hT M gens gm L) :
    ∀ g ∈ M, (∀ k ∈ tab64Sub tab hT, g * k = k * g) → g ∈ tab64Sub tab hT := by
  intro g hg hcomm
  obtain ⟨st, hstL, g₀, -, e₀, he₀, hgeq, hstid, hact⟩ := h.decomp g hg
  have hreach : StReach gm st := by
    obtain ⟨e, he, he1⟩ := List.mem_map.mp hstL
    rw [← he1]
    exact (sbfsOK_sound h.bfs).2.2 e he
  have hfixn : ∀ n < 64, linAct st n = n := by
    intro n hn
    have hcommn : g * tab64Perm tab n * g⁻¹ = tab64Perm tab n := by
      have h := hcomm (tab64Perm tab n) (tab64Perm_mem_tab64Sub hT hn)
      rw [h]; group
    have hexp : g * tab64Perm tab n * g⁻¹ = g₀ * tab64Perm tab n * g₀⁻¹ := by
      rw [hgeq]
      have hconj : e₀ * tab64Perm tab n * e₀⁻¹ = tab64Perm tab n := by
        obtain ⟨l, hl, rfl⟩ := (mem_tab64Sub hT).mp he₀
        rw [tab64Perm_comm hT hl hn]
        group
      calc (g₀ * e₀) * tab64Perm tab n * (g₀ * e₀)⁻¹
          = g₀ * (e₀ * tab64Perm tab n * e₀⁻¹) * g₀⁻¹ := by group
        _ = g₀ * tab64Perm tab n * g₀⁻¹ := by rw [hconj]
    have hpsi : tab64Perm tab (linAct st n) = tab64Perm tab n := by
      rw [← hact n hn, ← hexp]
      exact hcommn
    exact tab64Perm_inj hT (linAct_lt st n) hn hpsi
  have hcol : ∀ i < 6, col st i = col idSt i := by
    intro i hi
    have h2i : 2 ^ i < 64 := by interval_cases i <;> norm_num
    rw [← linAct_two_pow st hi, hfixn (2 ^ i) h2i,
        ← linAct_two_pow idSt hi, linAct_idSt h2i]
  have hstlt : st < 2 ^ 36 := StReach.lt hreach
  have hidlt : idSt < 2 ^ 36 := StReach.lt (StReach.base (gm := gm))
  have hfix : st = idSt := eq_of_col_eq hstlt hidlt hcol
  have hg₀1 : g₀ = 1 := hstid hfix
  rw [hgeq, hg₀1, one_mul]
  exact he₀

theorem EngineHyp.irreducible (h : EngineHyp tab hT M gens gm L) {v₁ v₂ : ℕ}
    {B₁ B₂ : List (ℕ × ℕ × ℕ)} {D₁ : List (ℕ × ℕ)}
    (hb₁ : vbfs64OK tab gens v₁ B₁ = true) (hb₂ : vbfs64OK tab gens v₂ B₂ = true)
    (hcover : (List.range 64).all (fun n =>
      n == 0 || (B₁.map Prod.fst).contains n || (B₂.map Prod.fst).contains n) = true)
    (hD₁ : derivOK (B₁.map Prod.fst) D₁ = true)
    (hlink : (B₂.map Prod.fst).any (fun b =>
      (B₂.map Prod.fst).any fun b' => (B₁.map Prod.fst).contains (b ^^^ b')) = true) :
    ∀ W : Subgroup S24, W ≤ tab64Sub tab hT → W ≠ ⊥ →
      (∀ g ∈ M, W.map (MulAut.conj g).toMonoidHom = W) → W = tab64Sub tab hT := by
  have h1 : ∀ b ∈ B₁.map Prod.fst, b < 64 ∧ ∃ g ∈ M,
      g * tab64Perm tab v₁ * g⁻¹ = tab64Perm tab b := by
    intro b hb
    obtain ⟨e, he, he1⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
    have hget : (B₁.getD k (0, 0, 0)).1 = b := by
      rw [List.getD_eq_getElem (l := B₁) (d := (0, 0, 0)) hk, hke, he1]
    obtain ⟨hlt, g, hgM, hconj⟩ := exists_conj_of_vbfs64 hT (hg := h.gens_mem) hb₁ k hk
    refine ⟨?_, g, hgM, ?_⟩
    · rw [← hget]; exact hlt
    · rw [← hget]; exact hconj
  have h2 : ∀ b ∈ B₂.map Prod.fst, b < 64 ∧ ∃ g ∈ M,
      g * tab64Perm tab v₂ * g⁻¹ = tab64Perm tab b := by
    intro b hb
    obtain ⟨e, he, he1⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
    have hget : (B₂.getD k (0, 0, 0)).1 = b := by
      rw [List.getD_eq_getElem (l := B₂) (d := (0, 0, 0)) hk, hke, he1]
    obtain ⟨hlt, g, hgM, hconj⟩ := exists_conj_of_vbfs64 hT (hg := h.gens_mem) hb₂ k hk
    refine ⟨?_, g, hgM, ?_⟩
    · rw [← hget]; exact hlt
    · rw [← hget]; exact hconj
  have hcoverMem : ∀ n, 0 < n → n < 64 →
      n ∈ B₁.map Prod.fst ∨ n ∈ B₂.map Prod.fst := by
    intro n hn0 hn64
    have hc := List.all_eq_true.1 hcover n (List.mem_range.2 hn64)
    have hbeq : (n == 0) = false := by
      rw [beq_eq_false_iff_ne]; omega
    rw [hbeq, Bool.false_or] at hc
    rw [Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · exact Or.inl (List.contains_iff_mem.mp hc)
    · exact Or.inr (List.contains_iff_mem.mp hc)
  exact irreducible_of_two_orbits64 hT h.le h1 h2 hcoverMem hD₁ hlink

theorem EngineHyp.pCore (h : EngineHyp tab hT M gens gm L) {v₁ v₂ : ℕ}
    {B₁ B₂ : List (ℕ × ℕ × ℕ)} {D₁ : List (ℕ × ℕ)}
    (hb₁ : vbfs64OK tab gens v₁ B₁ = true) (hb₂ : vbfs64OK tab gens v₂ B₂ = true)
    (hcover : (List.range 64).all (fun n =>
      n == 0 || (B₁.map Prod.fst).contains n || (B₂.map Prod.fst).contains n) = true)
    (hD₁ : derivOK (B₁.map Prod.fst) D₁ = true)
    (hlink : (B₂.map Prod.fst).any (fun b =>
      (B₂.map Prod.fst).any fun b' => (B₁.map Prod.fst).contains (b ^^^ b')) = true) :
    pCoreOf 2 M = tab64Sub tab hT :=
  pCoreOf_eq_of_selfCentralizing_irreducible h.le h.normal (isPGroup_tab64Sub hT)
    (tab64Sub_ne_bot hT) h.selfCentralizing (h.irreducible hb₁ hb₂ hcover hD₁ hlink)

end CFSG.Quasithin.AppendixH.H14
