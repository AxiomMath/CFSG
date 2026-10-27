module

public import CFSG.YGroups.DCE.Maximal
public import CFSG.YGroups.DCE.OutSpecB

public section


namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2

private theorem foldl_add_range' (f : ℕ → ℕ) (m init : ℕ) :
    (List.range m).foldl (fun a j => a + f j) init = init + ∑ j ∈ Finset.range m, f j := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ]
    ring

theorem points_of_finalOK {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω]
    [Finite Eg]
    (E : B.EnvB) (S : SymGen.Setup G Eg Ω) {n : ℕ} (hn : E.C.n = n)
    (ρ : Eg →* Equiv.Perm (Fin n)) (pt : ℕ → Ω) (x : ℕ → G)
    (hW : ∀ j a, E.W j a → ∃ e, RepB n a (ρ e) ∧ x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (hV : ∀ i p k a, E.V i p k a → p < E.C.N ∧ ∃ e, S.RCoset (x i * S.T (pt p)) (x k * S.ψ e))
    (hactAll : ∀ (σ : ByteArray) (e : Eg), RepB n σ (ρ e) → ∀ p < E.C.N,
      B.u32get (E.C.actAll σ) p < E.C.N ∧ pt (B.u32get (E.C.actAll σ) p) = e • pt p)
    (hpt : ∀ ω : Ω, ∃ p < E.C.N, pt p = ω) (hx0 : x 0 ∈ S.H)
    (hker : ∀ j e, ρ e = 1 → x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (ord bound : ℕ) (hord : Nat.card ρ.range = ord)
    (prog : Array B.Ins) (fins : Array (ℕ × B.NodeFin))
    (h : E.finalOK prog fins ord bound = true) :
    x fins[0]!.1 ∈ S.H ∧ 0 < fins.size ∧
      (∀ l < fins.size, (B.stabSub S (x fins[l]!.1)).index ≤
        ord / E.chainBound (B.replay E prog) fins[l]!.2) ∧
      ∃ (R : ℕ → Finset Ω) (tgt : ℕ → Ω → ℕ) (u : ℕ → Ω → Eg),
        (∀ l < fins.size, ∀ p : Ω, ∃ q ∈ R l, ∃ e ∈ B.stabSub S (x fins[l]!.1), e • q = p) ∧
        ∀ l < fins.size, ∀ q ∈ R l, tgt l q < fins.size ∧
          S.RCoset (x fins[l]!.1 * S.T q) (x fins[tgt l q]!.1 * S.ψ (u l q)) := by
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
  exact ⟨hx0', hnn, fun l hl =>
    B.index_stabSub_le st fins[l]!.1 fins[l]!.2 (hcl l hl).2 S ρ x hW hker hord,
    R, tgt, u, hR, fun l hl q hq => ⟨htgt1 l hl q hq, htgt2 l hl q hq⟩⟩

theorem eq_or_eq_top_of_finalOK {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω]
    [Finite G] [Finite Eg]
    (E : B.EnvB) (S : SymGen.Setup G Eg Ω) {n : ℕ} (hn : E.C.n = n)
    (ρ : Eg →* Equiv.Perm (Fin n)) (pt : ℕ → Ω) (x : ℕ → G)
    (hW : ∀ j a, E.W j a → ∃ e, RepB n a (ρ e) ∧ x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (hV : ∀ i p k a, E.V i p k a → p < E.C.N ∧ ∃ e, S.RCoset (x i * S.T (pt p)) (x k * S.ψ e))
    (hactAll : ∀ (σ : ByteArray) (e : Eg), RepB n σ (ρ e) → ∀ p < E.C.N,
      B.u32get (E.C.actAll σ) p < E.C.N ∧ pt (B.u32get (E.C.actAll σ) p) = e • pt p)
    (hpt : ∀ ω : Ω, ∃ p < E.C.N, pt p = ω) (hx0 : x 0 ∈ S.H)
    (hker : ∀ j e, ρ e = 1 → x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (ord bound : ℕ) (hord : Nat.card ρ.range = ord)
    (hgen : Subgroup.closure ((S.H : Set G) ∪ {S.t}) = ⊤)
    (prog : Array B.Ins) (fins : Array (ℕ × B.NodeFin))
    (h : E.finalOK prog fins ord bound = true)
    (hidx : (List.range fins.size).foldl
      (fun a l => a + ord / E.chainBound (B.replay E prog) fins[l]!.2) 0 ≤ S.H.index)
    (harith : ∀ U : Finset ℕ, U ⊆ Finset.range fins.size → 0 ∈ U →
      (∑ l ∈ U, ord / E.chainBound (B.replay E prog) fins[l]!.2) ∣
        ∑ l ∈ Finset.range fins.size, ord / E.chainBound (B.replay E prog) fins[l]!.2 →
      U = {0} ∨ U = Finset.range fins.size)
    (L : Subgroup G) (hHL : S.H ≤ L) : L = S.H ∨ L = ⊤ := by
  obtain ⟨hx0', hnn, hidxl, R, tgt, u, hR, htgt⟩ :=
    points_of_finalOK E S hn ρ pt x hW hV hactAll hpt hx0 hker ord bound hord prog fins h
  have hsum : ∑ l ∈ Finset.range fins.size,
      ord / E.chainBound (B.replay E prog) fins[l]!.2 ≤ S.H.index := by
    have e := foldl_add_range' (fun l => ord / E.chainBound (B.replay E prog) fins[l]!.2)
      fins.size 0
    rw [zero_add] at e
    rw [← e]
    exact hidx
  exact S.eq_or_eq_top_of_points fins.size (fun l => x fins[l]!.1) hx0'
    (fun l => B.stabSub S (x fins[l]!.1)) (fun l _ e he => (B.mem_stabSub S _ _).1 he) R hR
    tgt u htgt hgen hnn (fun l => ord / E.chainBound (B.replay E prog) fins[l]!.2) hidxl hsum
    harith L hHL

theorem exact_of_finalOK {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω]
    [Finite G] [Finite Eg]
    (E : B.EnvB) (S : SymGen.Setup G Eg Ω) {n : ℕ} (hn : E.C.n = n)
    (ρ : Eg →* Equiv.Perm (Fin n)) (pt : ℕ → Ω) (x : ℕ → G)
    (hW : ∀ j a, E.W j a → ∃ e, RepB n a (ρ e) ∧ x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (hV : ∀ i p k a, E.V i p k a → p < E.C.N ∧ ∃ e, S.RCoset (x i * S.T (pt p)) (x k * S.ψ e))
    (hactAll : ∀ (σ : ByteArray) (e : Eg), RepB n σ (ρ e) → ∀ p < E.C.N,
      B.u32get (E.C.actAll σ) p < E.C.N ∧ pt (B.u32get (E.C.actAll σ) p) = e • pt p)
    (hpt : ∀ ω : Ω, ∃ p < E.C.N, pt p = ω) (hx0 : x 0 ∈ S.H)
    (hker : ∀ j e, ρ e = 1 → x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (ord bound : ℕ) (hord : Nat.card ρ.range = ord)
    (hgen : Subgroup.closure ((S.H : Set G) ∪ {S.t}) = ⊤)
    (prog : Array B.Ins) (fins : Array (ℕ × B.NodeFin))
    (h : E.finalOK prog fins ord bound = true)
    (hidx : (List.range fins.size).foldl
      (fun a l => a + ord / E.chainBound (B.replay E prog) fins[l]!.2) 0 ≤ S.H.index) :
    (∀ l < fins.size, (B.stabSub S (x fins[l]!.1)).index =
      ord / E.chainBound (B.replay E prog) fins[l]!.2) ∧
    ∀ l < fins.size, ∀ l' < fins.size, ∀ a b : Eg,
      ((S.ψ a * (x fins[l]!.1)⁻¹ : G) : G ⧸ S.H) = ((S.ψ b * (x fins[l']!.1)⁻¹ : G) : G ⧸ S.H) →
        l = l' := by
  obtain ⟨hx0', hnn, hidxl, R, tgt, u, hR, htgt⟩ :=
    points_of_finalOK E S hn ρ pt x hW hV hactAll hpt hx0 hker ord bound hord prog fins h
  have hsum : ∑ l ∈ Finset.range fins.size,
      ord / E.chainBound (B.replay E prog) fins[l]!.2 ≤ S.H.index := by
    have e := foldl_add_range' (fun l => ord / E.chainBound (B.replay E prog) fins[l]!.2)
      fins.size 0
    rw [zero_add] at e
    rw [← e]
    exact hidx
  exact S.exact_of_points fins.size (fun l => x fins[l]!.1) hx0'
    (fun l => B.stabSub S (x fins[l]!.1)) (fun l _ e he => (B.mem_stabSub S _ _).1 he) R hR
    tgt u htgt hgen hnn (fun l => ord / E.chainBound (B.replay E prog) fins[l]!.2) hidxl hsum

end CFSG.YGroups.DCE
