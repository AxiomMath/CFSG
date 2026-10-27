module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Rig

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

structure HexAct {X : Type*} [Group X] (ρ : X →* Equiv.Perm (Fin 819)) (H N : Subgroup X) :
    Prop where
  mem_H : ∀ x, x ∈ H ↔ ρ x 0 = 0
  mem_N : ∀ x, x ∈ N ↔ f48L0.image (ρ x) = f48L0

variable {X : Type*} [Group X] {ρ : X →* Equiv.Perm (Fin 819)} {H N : Subgroup X}

theorem HexAct.mem_of_inB (S : HexAct ρ H N) {a : Array ℕ} {x : X} (ha : Rep 819 a (ρ x))
    (h : f48InB a = true) : x ∈ H ∧ x ∈ N :=
  ⟨(S.mem_H x).2 (f48InB_spec ha h).1, (S.mem_N x).2 (f48InB_spec ha h).2⟩

theorem HexAct.n_mem (S : HexAct ρ H N) {n : Array ℕ} {x : X} (hn : Rep 819 n (ρ x))
    (h : f48NOK n = true) : x ∈ H :=
  (S.mem_H x).2 (f48NOK_spec hn h).2

section

variable (S : HexAct ρ H N) {M p0 : ℕ} {lay n q : Array ℕ} {F : Array (Array ℕ)} {r : OrbRec}
  {nX qX : X} {fX : ℕ → X}

include S in
theorem hex_rigid_n (hM : M < 2 ^ 40) (hlay : f48LayOK lay p0 = true)
    (horb : f48OrbOK lay F r p0 = true) (hkey : f48KeyAll lay F r M p0 n q = true)
    (hnok : f48NOK n = true) (hfok : f48FOK n F = true) (hnR : Rep 819 n (ρ nX))
    (hqR : Rep 819 q (ρ qX)) (hFR : ∀ j < F.size, Rep 819 F[j]! (ρ (fX j)))
    (π : ↥H →* Equiv.Perm (Fin 819))
    (hB : ∀ (x : X) (hx : x ∈ H), x ∈ N → π ⟨x, hx⟩ = ρ x)
    (hNear : ∀ (x : X) (hx : x ∈ H) (p : Fin 819), lay[(p : ℕ)]! ≤ 4 → π ⟨x, hx⟩ p = ρ x p)
    (hnH : nX ∈ H) (hnn : nX * nX = 1) (hX : (π ⟨nX, hnH⟩ * ρ qX) ^ M = 1) :
    π ⟨nX, hnH⟩ = ρ nX := by
  have hnn' : ρ nX * ρ nX = 1 := (f48NOK_spec hnR hnok).1
  let nH : ↥H := ⟨nX, hnH⟩
  have hnH2 : nH * nH = 1 := Subtype.ext hnn
  have hpn2 : π nH * π nH = 1 := by rw [← map_mul, hnH2, map_one]
  set σ : Equiv.Perm (Fin 819) := ρ nX * π nH with hσ
  have hπn : π nH = ρ nX * σ := by rw [hσ, ← mul_assoc, hnn', one_mul]
  have hnear : ∀ p : Fin 819, lay[(p : ℕ)]! ≤ 4 → σ p = p := by
    intro p hp
    have h1 : π nH p = ρ nX p := hNear nX hnH p hp
    have h2 : ρ nX (ρ nX p) = p := by
      have := congrArg (fun g : Equiv.Perm (Fin 819) => g p) hnn'
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using this
    rw [hσ, Equiv.Perm.mul_apply, h1]
    exact h2
  have hcomm : ∀ j < F.size, σ * ρ (fX j) = ρ (fX j) * σ := by
    intro j hj
    obtain ⟨hfB, hfcB⟩ := f48FOK_spec hfok hj
    obtain ⟨hfH, hfN⟩ := S.mem_of_inB (hFR j hj) hfB
    have hcR : Rep 819 (f48Conj n F[j]!) (ρ (nX * (fX j * nX))) := by
      rw [map_mul, map_mul]
      exact rep_compA hnR (rep_compA (hFR j hj) hnR)
    obtain ⟨hcH, hcN⟩ := S.mem_of_inB hcR hfcB
    have e1 : π ⟨fX j, hfH⟩ = ρ (fX j) := hB _ hfH hfN
    have e2 : π ⟨nX * (fX j * nX), hcH⟩ = ρ nX * (ρ (fX j) * ρ nX) := by
      rw [hB _ hcH hcN, map_mul, map_mul]
    have e3 : (⟨nX * (fX j * nX), hcH⟩ : ↥H) = nH * (⟨fX j, hfH⟩ * nH) := rfl
    have key : π nH * (ρ (fX j) * π nH) = ρ nX * (ρ (fX j) * ρ nX) := by
      rw [← e2, e3, map_mul, map_mul, e1]
    have key2 : π nH * ρ (fX j) = ρ nX * (ρ (fX j) * ρ nX) * π nH := by
      calc π nH * ρ (fX j) = π nH * (ρ (fX j) * (π nH * π nH)) := by rw [hpn2, mul_one]
        _ = (π nH * (ρ (fX j) * π nH)) * π nH := by simp only [mul_assoc]
        _ = ρ nX * (ρ (fX j) * ρ nX) * π nH := by rw [key]
    calc σ * ρ (fX j) = ρ nX * (π nH * ρ (fX j)) := by rw [hσ, mul_assoc]
      _ = ρ nX * (ρ nX * (ρ (fX j) * ρ nX) * π nH) := by rw [key2]
      _ = (ρ nX * ρ nX) * (ρ (fX j) * ρ nX) * π nH := by simp only [mul_assoc]
      _ = ρ (fX j) * σ := by rw [hnn', one_mul, hσ]; simp only [mul_assoc]
  have hsq : (ρ nX * σ) * (ρ nX * σ) = 1 := by rw [← hπn]; exact hpn2
  have hexp : ((ρ nX * σ) * ρ qX) ^ M = 1 := by rw [← hπn]; exact hX
  have hσ1 : σ = 1 := hex_sigma_eq_one hM hlay horb hkey hnR hqR hFR hnear hcomm hsq hexp
  rw [hπn, hσ1, mul_one]

end

@[expose] def HexOnLine (lineTab : Array ℕ) (l p : ℕ) : Prop :=
  p = f48LinePt lineTab l 0 ∨ p = f48LinePt lineTab l 1 ∨ p = f48LinePt lineTab l 2

theorem f48LineHas0_iff {lineTab : Array ℕ} {l : ℕ} :
    f48LineHas0 lineTab l = true ↔ HexOnLine lineTab l 0 := by
  unfold f48LineHas0 HexOnLine
  simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]
  exact ⟨fun h => h.imp Eq.symm fun h' => h'.imp Eq.symm Eq.symm,
    fun h => h.imp Eq.symm fun h' => h'.imp Eq.symm Eq.symm⟩

theorem HexOnLine.mem3 {lineTab : Array ℕ} {l a b c p : ℕ} (hp : HexOnLine lineTab l p)
    (h : f48LineIn lineTab l a b c = true) : p = a ∨ p = b ∨ p = c := by
  simp only [f48LineIn, Bool.and_eq_true, f48In3_iff] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  rcases hp with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

section

variable (S : HexAct ρ H N) {M p0 : ℕ} {nW qW : List ℕ} {fW bW : List (List ℕ)}
  {lineTab lay : Array ℕ} {G : Array (Array ℕ)} {nX qX : X} {fX bX : ℕ → X}

include S in
theorem hex_rigid_gen (hc : hexF48Check M p0 nW qW fW bW lineTab lay G = true)
    (hnR : Rep 819 (f48EvalW G nW) (ρ nX)) (hqR : Rep 819 (f48EvalW G qW) (ρ qX))
    (hFR : ∀ j < (f48WordArrs G fW).size, Rep 819 (f48WordArrs G fW)[j]! (ρ (fX j)))
    (hbR : ∀ j < (f48WordArrs G bW).size, Rep 819 (f48WordArrs G bW)[j]! (ρ (bX j)))
    (π : ↥H →* Equiv.Perm (Fin 819))
    (hB : ∀ (x : X) (hx : x ∈ H), x ∈ N → π ⟨x, hx⟩ = ρ x)
    (hNear : ∀ (x : X) (hx : x ∈ H) (p : Fin 819), lay[(p : ℕ)]! ≤ 4 → π ⟨x, hx⟩ p = ρ x p)
    (hnH : nX ∈ H) (hnn : nX * nX = 1) (hX : (π ⟨nX, hnH⟩ * ρ qX) ^ M = 1)
    (hlines : ∀ x ∈ H, ∃ l < 2457, HexOnLine lineTab l 0 ∧
      ∀ p ∈ f48L0, HexOnLine lineTab l (ρ x p : ℕ))
    (y : ↥H) : π y = ρ y := by
  obtain ⟨hM, -, hnok, -, hfok, hbok, hlay, horb, hkey, hlinesOK, -⟩ := hexF48Check_spec hc
  have hπn : π ⟨nX, hnH⟩ = ρ nX :=
    hex_rigid_n S hM hlay horb hkey hnok hfok hnR hqR hFR π hB hNear hnH hnn hX
  obtain ⟨x, hx⟩ := y
  show π ⟨x, hx⟩ = ρ x
  obtain ⟨l, hl, hl0, hlx⟩ := hlines x hx
  rcases f48LinesOK_spec hlinesOK hl (f48LineHas0_iff.2 hl0) with hcase | ⟨j, hj, hcase⟩
  · refine hB x hx ((S.mem_N x).2 (image_f48L0_eq fun p hp => ?_))
    rw [mem_f48L0_iff]
    exact (hlx p hp).mem3 hcase
  · have hbs := f48BsOK_spec hbok
    have hjs : j < (f48WordArrs G bW).size := by rw [hbs.1]; exact hj
    obtain ⟨hbH, hbN⟩ := S.mem_of_inB (hbR j hjs) (hbs.2 j hjs)
    have hnu : Rep 819 (compA 819 (f48WordArrs G bW)[j]! (f48EvalW G nW))
        (ρ (bX j) * ρ nX) := rep_compA (hbR j hjs) hnR
    obtain ⟨g, hg⟩ : ∃ g : X, g = (bX j * nX)⁻¹ * x := ⟨_, rfl⟩
    have hxg : x = bX j * nX * g := by rw [hg, mul_inv_cancel_left]
    have hgH : g ∈ H := by
      rw [hg]
      exact H.mul_mem (H.inv_mem (H.mul_mem hbH hnH)) hx
    have hgN : g ∈ N := by
      refine (S.mem_N g).2 (image_f48L0_eq fun p hp => ?_)
      have hpl := (hlx p hp).mem3 hcase
      have key : ∀ q : Fin 819, q ∈ f48L0 → (ρ x p : ℕ) = (ρ (bX j) * ρ nX) q →
          ρ g p ∈ f48L0 := by
        intro q hq hpq
        have h1 : ρ x p = (ρ (bX j) * ρ nX) q := Fin.ext hpq
        have h2 : ρ g p = q := by
          rw [hg, map_mul, map_inv, map_mul, Equiv.Perm.mul_apply, h1]
          simp
        rw [h2]
        exact hq
      rcases hpl with h | h | h
      · exact key 0 (by simp [f48L0]) (h.trans (hnu 0))
      · exact key 1 (by simp [f48L0]) (h.trans (hnu 1))
      · exact key 5 (by simp [f48L0]) (h.trans (hnu 5))
    have e : π ⟨x, hx⟩ = π ⟨bX j, hbH⟩ * π ⟨nX, hnH⟩ * π ⟨g, hgH⟩ := by
      have : (⟨x, hx⟩ : ↥H) = ⟨bX j, hbH⟩ * ⟨nX, hnH⟩ * ⟨g, hgH⟩ := Subtype.ext hxg
      rw [this, map_mul, map_mul]
    rw [e, hB _ hbH hbN, hπn, hB _ hgH hgN]
    calc ρ (bX j) * ρ nX * ρ g = ρ (bX j * nX * g) := by rw [map_mul, map_mul]
      _ = ρ x := by rw [← hxg]

end

theorem map_f48WordVal {Y : Type*} [Group Y] (f : X →* Y) (g : ℕ → X) :
    ∀ w : List ℕ, f (f48WordVal g w) = f48WordVal (fun j => f (g j)) w
  | [] => by simp [f48WordVal]
  | l :: w => by rw [f48WordVal, f48WordVal, map_mul, map_f48WordVal f g w]

theorem f48WordArrs_get (G : Array (Array ℕ)) (ws : List (List ℕ)) {j : ℕ} (hj : j < ws.length) :
    (f48WordArrs G ws)[j]! = f48EvalW G ws[j]! := by
  have hj' : j < (f48WordArrs G ws).size := by simpa [f48WordArrs] using hj
  rw [getElem!_pos _ j hj', getElem!_pos ws j hj]
  simp [f48WordArrs]

section

variable (S : HexAct ρ H N) {M p0 : ℕ} {nW qW : List ℕ} {fW bW : List (List ℕ)}
  {lineTab lay : Array ℕ} {G : Array (Array ℕ)}

theorem hex_rep_words (hc : hexF48Check M p0 nW qW fW bW lineTab lay G = true) (g : ℕ → X)
    (hg : ∀ j < G.size, Rep 819 G[j]! (ρ (g j))) :
    ∀ w ∈ [nW, qW] ++ fW ++ bW, Rep 819 (f48EvalW G w) (ρ (f48WordVal g w)) := by
  intro w hw
  rw [map_f48WordVal]
  exact rep_f48EvalW hg w (f48LettersOK_spec (hexF48Check_spec hc).2.1 w hw)

include S in
theorem hex_n_mem (hc : hexF48Check M p0 nW qW fW bW lineTab lay G = true) (g : ℕ → X)
    (hg : ∀ j < G.size, Rep 819 G[j]! (ρ (g j))) : f48WordVal g nW ∈ H :=
  S.n_mem (hex_rep_words hc g hg nW (by simp)) (hexF48Check_spec hc).2.2.1

include S in
theorem hex_rigid_words (hc : hexF48Check M p0 nW qW fW bW lineTab lay G = true) (g : ℕ → X)
    (hg : ∀ j < G.size, Rep 819 G[j]! (ρ (g j))) (π : ↥H →* Equiv.Perm (Fin 819))
    (hB : ∀ (x : X) (hx : x ∈ H), x ∈ N → π ⟨x, hx⟩ = ρ x)
    (hNear : ∀ (x : X) (hx : x ∈ H) (p : Fin 819), lay[(p : ℕ)]! ≤ 4 → π ⟨x, hx⟩ p = ρ x p)
    (hnH : f48WordVal g nW ∈ H) (hnn : f48WordVal g nW * f48WordVal g nW = 1)
    (hX : (π ⟨f48WordVal g nW, hnH⟩ * ρ (f48WordVal g qW)) ^ M = 1)
    (hlines : ∀ x ∈ H, ∃ l < 2457, HexOnLine lineTab l 0 ∧
      ∀ p ∈ f48L0, HexOnLine lineTab l (ρ x p : ℕ))
    (y : ↥H) : π y = ρ y := by
  have hrep := hex_rep_words hc g hg
  refine hex_rigid_gen (fX := fun j => f48WordVal g fW[j]!) (bX := fun j => f48WordVal g bW[j]!) S
    hc (hrep nW (by simp)) (hrep qW (by simp)) (fun j hj => ?_) (fun j hj => ?_) π hB hNear hnH hnn
    hX hlines y
  · have hj' : j < fW.length := by simpa [f48WordArrs] using hj
    rw [f48WordArrs_get G fW hj']
    refine hrep _ ?_
    rw [getElem!_pos fW j hj']
    simp
  · have hj' : j < bW.length := by simpa [f48WordArrs] using hj
    rw [f48WordArrs_get G bW hj']
    refine hrep _ ?_
    rw [getElem!_pos bW j hj']
    simp

include S in
theorem hex_q_mem (hc : hexF48Check M p0 nW qW fW bW lineTab lay G = true) (g : ℕ → X)
    (hg : ∀ j < G.size, Rep 819 G[j]! (ρ (g j))) : f48WordVal g qW ∈ N :=
  (S.mem_N _).2 (f48MapsL0_spec (hex_rep_words hc g hg qW (by simp))
    (hexF48Check_spec hc).2.2.2.1)

include S in
theorem hex_fixed_point (hc : hexF48Check M p0 nW qW fW bW lineTab lay G = true) (g : ℕ → X)
    (hg : ∀ j < G.size, Rep 819 G[j]! (ρ (g j))) {w : Fin 819}
    (hw : ∀ x ∈ H ⊓ N, ρ x w = w) : w = 0 := by
  obtain ⟨-, -, -, -, hfok, -, -, -, -, -, hfix⟩ := hexF48Check_spec hc
  have hrep := hex_rep_words hc g hg
  refine Fin.ext (f48FixOK_spec hfix w.2 fun j hj => ?_)
  have hj' : j < fW.length := by simpa [f48WordArrs] using hj
  have hR : Rep 819 (f48WordArrs G fW)[j]! (ρ (f48WordVal g fW[j]!)) := by
    rw [f48WordArrs_get G fW hj']
    refine hrep _ ?_
    rw [getElem!_pos fW j hj']
    simp
  have hmem := S.mem_of_inB hR (f48FOK_spec hfok hj).1
  exact (hR w).trans (congrArg Fin.val (hw _ (Subgroup.mem_inf.2 hmem)))

end

end CFSG.Quasithin.D4Hex
