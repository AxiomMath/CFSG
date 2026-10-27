module

public import CFSG.YGroups.DCE.OutSpecB

public section

namespace CFSG.Monster.Existence.B433Cover

open CFSG.YGroups CFSG.YGroups.DCE CFSG.Monster.B.Co2

theorem exists_doubleCoset_of_points {G E Ω : Type*} [Group G] [Group E] [MulAction E Ω]
    (S : SymGen.Setup G E Ω) (r : ℕ) (x : ℕ → G)
    (hx0 : x 0 ∈ S.H) (P : ℕ → Subgroup E)
    (hP : ∀ j < r, ∀ e ∈ P j, x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (R : ℕ → Finset Ω) (hR : ∀ j < r, ∀ p : Ω, ∃ q ∈ R j, ∃ e ∈ P j, e • q = p)
    (tgt : ℕ → Ω → ℕ) (u : ℕ → Ω → E)
    (htgt : ∀ j < r, ∀ q ∈ R j, tgt j q < r ∧ S.RCoset (x j * S.T q) (x (tgt j q) * S.ψ (u j q)))
    (hgen : Subgroup.closure ((S.H : Set G) ∪ {S.t}) = ⊤) (hr : 0 < r) (g : G) :
    ∃ j < r, ∃ a ∈ S.H, ∃ b ∈ S.H, g = a * x j * b := by
  classical
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
          unfold SymGen.Setup.T
          rw [map_mul]
          group
        rw [key]
        exact hrc }
  obtain ⟨i, a, ha, b, hb, hab⟩ :=
    D.exists_eq_of_doubleCoset_data hCH S.t_mul_t htC hgen g
  exact ⟨i, i.2, a, ha, b, hb, hab⟩

theorem exists_doubleCoset_of_finalOK {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω]
    (E : B.EnvB) (S : SymGen.Setup G Eg Ω) {n : ℕ} (hn : E.C.n = n)
    (ρ : Eg →* Equiv.Perm (Fin n)) (pt : ℕ → Ω) (x : ℕ → G)
    (hW : ∀ j a, E.W j a → ∃ e, RepB n a (ρ e) ∧ x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (hV : ∀ i p k a, E.V i p k a → p < E.C.N ∧ ∃ e, S.RCoset (x i * S.T (pt p)) (x k * S.ψ e))
    (hactAll : ∀ (σ : ByteArray) (e : Eg), RepB n σ (ρ e) → ∀ p < E.C.N,
      B.u32get (E.C.actAll σ) p < E.C.N ∧ pt (B.u32get (E.C.actAll σ) p) = e • pt p)
    (hpt : ∀ ω : Ω, ∃ p < E.C.N, pt p = ω) (hx0 : x 0 ∈ S.H)
    (ord bound : ℕ) (hgen : Subgroup.closure ((S.H : Set G) ∪ {S.t}) = ⊤)
    (prog : Array B.Ins) (fins : Array (ℕ × B.NodeFin))
    (h : E.finalOK prog fins ord bound = true) (g : G) :
    ∃ l < fins.size, ∃ a ∈ S.H, ∃ b ∈ S.H, g = a * x fins[l]!.1 * b := by
  classical
  subst hn
  obtain ⟨-, hnn, hroot, hcl, hcount⟩ := B.EnvB.finalOK_spec h
  let st := B.replay E prog
  let live : Array ℕ := fins.map (·.1)
  let x' : ℕ → G := fun l => x fins[l]!.1
  have hx0' : x' 0 ∈ S.H := by
    show x fins[0]!.1 ∈ S.H
    rw [hroot]
    exact hx0
  let Q : ℕ → ℕ → ℕ → Prop := fun j a b => ∃ e ∈ B.stabSub S (x j), e • pt a = pt b
  have hrefl : ∀ j a, Q j a a := fun j a => ⟨1, one_mem _, one_smul _ _⟩
  have hsymm : ∀ j a b, Q j a b → Q j b a := fun j a b ⟨e, he, hab⟩ =>
    ⟨e⁻¹, inv_mem he, by rw [← hab, inv_smul_smul]⟩
  have htrans : ∀ j a b c, Q j a b → Q j b c → Q j a c := fun j a b c ⟨e₁, he₁, h₁⟩ ⟨e₂, he₂, h₂⟩ =>
    ⟨e₂ * e₁, mul_mem he₂ he₁, by rw [mul_smul, h₁, h₂]⟩
  have hQ : ∀ j (fin : B.NodeFin), ∀ w ∈ E.fgensOf st fin, w.1.1 = j →
      ∀ y < E.C.N, Q j y (B.u32get (E.C.actAll w.1.2) y) := by
    intro j fin w _ hwj y hy
    have hwW : E.W j w.1.2 := by
      have := w.2
      rwa [hwj] at this
    obtain ⟨e, hrep, he⟩ := hW j _ hwW
    obtain ⟨-, hpe⟩ := hactAll w.1.2 e hrep y hy
    exact ⟨e, (B.mem_stabSub S _ _).2 he, hpe.symm⟩
  have hnode : ∀ l < fins.size,
      (∀ f ∈ E.coverOf st fins[l]!.2, f.1.i = fins[l]!.1 ∧ f.1.k ∈ live ∧ f.1.p < E.C.N) ∧
      ∀ y < E.C.N, ∃ f ∈ E.coverOf st fins[l]!.2, Q fins[l]!.1 f.1.p y := by
    intro l hl
    obtain ⟨-, hfacts, hcov⟩ := B.EnvB.nodeCovered_spec (hcl l hl).1 (Q fins[l]!.1)
      (hrefl _) (hsymm _) (htrans _) (hQ _ _)
    exact ⟨hfacts, hcov⟩
  let R : ℕ → Finset Ω := fun l =>
    ((E.coverOf st fins[l]!.2).toList.map fun f => pt f.1.p).toFinset
  have hmemR : ∀ l (q : Ω), q ∈ R l ↔ ∃ f ∈ E.coverOf st fins[l]!.2, pt f.1.p = q := by
    intro l q
    simp [R]
  have hR : ∀ l < fins.size, ∀ p : Ω, ∃ q ∈ R l, ∃ e ∈ B.stabSub S (x' l), e • q = p := by
    intro l hl ω
    obtain ⟨p, hp, rfl⟩ := hpt ω
    obtain ⟨f, hf, e, he, hee⟩ := (hnode l hl).2 p hp
    exact ⟨pt f.1.p, (hmemR l _).2 ⟨f, hf, rfl⟩, e, he, hee⟩
  have hpos : ∀ k ∈ live, ∃ l', l' < fins.size ∧ fins[l']!.1 = k := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Array.mem_map.1 hk
    obtain ⟨l', hl', rfl⟩ := Array.mem_iff_getElem.1 ha
    exact ⟨l', hl', by rw [getElem!_pos fins l' hl']⟩
  have htgt : ∀ l < fins.size, ∀ q ∈ R l, ∃ k, ∃ e : Eg, k < fins.size ∧
      S.RCoset (x' l * S.T q) (x' k * S.ψ e) := by
    intro l hl q hq
    obtain ⟨f, hf, rfl⟩ := (hmemR l q).1 hq
    obtain ⟨hi, hk, -⟩ := (hnode l hl).1 f hf
    obtain ⟨-, e, he⟩ := hV f.1.i f.1.p f.1.k f.1.a f.2
    obtain ⟨l', hl', hl'k⟩ := hpos _ hk
    refine ⟨l', e, hl', ?_⟩
    show S.RCoset (x fins[l]!.1 * S.T (pt f.1.p)) (x fins[l']!.1 * S.ψ e)
    rw [hl'k, ← hi]
    exact he
  choose! tgt u htgt1 htgt2 using htgt
  exact exists_doubleCoset_of_points S fins.size x' hx0' (fun l => B.stabSub S (x' l))
    (fun l _ e he => (B.mem_stabSub S _ _).1 he) R hR tgt u
    (fun l hl q hq => ⟨htgt1 l hl q hq, htgt2 l hl q hq⟩) hgen hnn g

end CFSG.Monster.Existence.B433Cover
