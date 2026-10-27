module

public import CFSG.Quasithin.AppendixH.H12.ModelPlane
public import CFSG.Quasithin.AppendixH.H12.GroupPerm
public import CFSG.Certificates.Kernel.J4.ModelsSound

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (cenIn ptStab)

@[expose] def sigOf (Pg : ℕ → List ℕ) (n : ℕ) (w : List ℕ) : List ℕ :=
  (List.range n).map fun i => spanMask ((Pg i).map (mvN (tW w)))

theorem spanMask_eq_iff {b b' : List ℕ} (hb : ∀ c ∈ b, c < 4096) (hb' : ∀ c ∈ b', c < 4096) :
    spanMask b = spanMask b' ↔ spanSub b = spanSub b' := by
  constructor
  · intro h
    exact (spanSub_eq_iff hb hb').mpr fun c hc => mem_iff_of_maskOf_eq h c
  · intro h
    apply Nat.eq_of_testBit_eq
    intro c
    rw [spanMask, spanMask, testBit_maskOf, testBit_maskOf]
    by_cases hc : c < 4096
    · rw [decide_eq_decide]
      exact (spanSub_eq_iff hb hb').mp h c hc
    · have hcb : ¬ c ∈ spanN b := fun hmem => hc (spanN_lt hb c hmem)
      have hcb' : ¬ c ∈ spanN b' := fun hmem => hc (spanN_lt hb' c hmem)
      simp [hcb, hcb']

theorem smulSub_tU_spanSub (w b : List ℕ) :
    smulSub (tU w) (spanSub b) = spanSub (b.map (mvN (tW w))) := by
  rw [smulSub_spanSub]
  exact congrArg spanSub (List.map_congr_left fun c _ => gmv_tU w c)

theorem exists_actHom {n : ℕ} (H : Subgroup Γ12) (Pg : ℕ → List ℕ)
    (hinj : ∀ i < n, ∀ j < n, spanSub (Pg i) = spanSub (Pg j) → i = j)
    (hclosed : ∀ g ∈ H, ∀ i < n, ∃ j < n, smulSub g (spanSub (Pg i)) = spanSub (Pg j)) :
    ∃ π : ↥H →* Equiv.Perm (Fin n), ∀ (g : ↥H) (i : Fin n),
      smulSub (g : Γ12) (spanSub (Pg i)) = spanSub (Pg (π g i)) := by
  obtain ⟨π, hπ⟩ := exists_permHom (H := ↥H) (X := Subgroup Vec12)
    (fun (g : ↥H) (P : Subgroup Vec12) => smulSub (g : Γ12) P)
    (fun P => by simp only [Subgroup.coe_one, smulSub_one])
    (fun g h P => by simp only [Subgroup.coe_mul, smulSub_mul])
    (fun i : Fin n => spanSub (Pg i))
    (fun i j hij => Fin.ext (hinj i.1 i.2 j.1 j.2 hij))
    (fun g i => by
      obtain ⟨j, hj, hje⟩ := hclosed (g : Γ12) g.2 i.1 i.2
      exact ⟨⟨j, hj⟩, hje⟩)
  exact ⟨π, hπ⟩

theorem actHom_eq_one {n : ℕ} {H : Subgroup Γ12} (π : ↥H →* Equiv.Perm (Fin n)) (Pg : ℕ → List ℕ)
    (hinj : ∀ i < n, ∀ j < n, spanSub (Pg i) = spanSub (Pg j) → i = j)
    (hπ : ∀ (g : ↥H) (i : Fin n), smulSub (g : Γ12) (spanSub (Pg i)) = spanSub (Pg (π g i)))
    (g : ↥H) (hg : ∀ i < n, smulSub (g : Γ12) (spanSub (Pg i)) = spanSub (Pg i)) : π g = 1 := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  exact hinj (π g i).val (π g i).isLt i.val i.isLt (by rw [← hπ g i, hg i i.2])

theorem actHom_tU_eq_one {n : ℕ} {H : Subgroup Γ12} (π : ↥H →* Equiv.Perm (Fin n))
    (Pg : ℕ → List ℕ) (hvalid : ∀ i < n, ∀ c ∈ Pg i, c < 4096)
    (hinj : ∀ i < n, ∀ j < n, spanSub (Pg i) = spanSub (Pg j) → i = j)
    (hπ : ∀ (g : ↥H) (i : Fin n), smulSub (g : Γ12) (spanSub (Pg i)) = spanSub (Pg (π g i)))
    {w : List ℕ} (hw : tU w ∈ H)
    (hfix : ∀ i < n, spanMask ((Pg i).map (mvN (tW w))) = spanMask (Pg i)) :
    π ⟨tU w, hw⟩ = 1 := by
  refine actHom_eq_one π Pg hinj hπ ⟨tU w, hw⟩ ?_
  intro i hi
  rw [smulSub_tU_spanSub]
  refine (spanMask_eq_iff ?_ (hvalid i hi)).mp (hfix i hi)
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact mvN_lt (validN_evalW gG validN_gG w).2 d

theorem length_le_card_range_of_sig {n : ℕ} {H : Subgroup Γ12} (π : ↥H →* Equiv.Perm (Fin n))
    (Pg : ℕ → List ℕ) (hvalid : ∀ i < n, ∀ c ∈ Pg i, c < 4096)
    (hπ : ∀ (g : ↥H) (i : Fin n), smulSub (g : Γ12) (spanSub (Pg i)) = spanSub (Pg (π g i)))
    (ws : List (List ℕ)) (hmem : ∀ w ∈ ws, tU w ∈ H) (hnd : (ws.map (sigOf Pg n)).Nodup) :
    ws.length ≤ Nat.card π.range := by
  classical
  let g : {w // w ∈ ws} → ↥H := fun x => ⟨tU x.1, hmem x.1 x.2⟩
  let l : List ↥H := ws.attach.map g
  let F : Equiv.Perm (Fin n) → List ℕ := fun σ =>
    (List.range n).map fun i => if h : i < n then spanMask (Pg (σ ⟨i, h⟩)) else 0
  have hmask : ∀ x : {w // w ∈ ws}, ∀ i : Fin n,
      spanMask ((Pg i.1).map (mvN (tW x.1))) = spanMask (Pg (π (g x) i)) := by
    intro x i
    have hsub : spanSub ((Pg i.1).map (mvN (tW x.1))) = spanSub (Pg (π (g x) i)) := by
      rw [← smulSub_tU_spanSub x.1 (Pg i.1)]
      exact hπ (g x) i
    refine (spanMask_eq_iff ?_ (hvalid (π (g x) i).1 (π (g x) i).2)).mpr hsub
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact mvN_lt (validN_evalW gG validN_gG x.1).2 d
  have hkey : ∀ x : {w // w ∈ ws}, F (π (g x)) = sigOf Pg n x.1 := by
    intro x
    dsimp only [F, sigOf]
    apply List.map_congr_left
    intro i hi
    have hin : i < n := List.mem_range.mp hi
    simp only [dif_pos hin]
    exact (hmask x ⟨i, hin⟩).symm
  have h1 : (l.map π).map F = ws.attach.map (fun x => sigOf Pg n x.1) := by
    simp only [l, List.map_map]
    apply List.map_congr_left
    intro x _
    exact hkey x
  have h2 : ws.attach.map (fun x => sigOf Pg n x.1) = ws.map (sigOf Pg n) :=
    List.attach_map_val (f := sigOf Pg n)
  have hnd_l : (l.map π).Nodup := by
    apply List.Nodup.of_map F
    rw [h1, h2]
    exact hnd
  have hlen : l.length = ws.length := by
    simp only [l, List.length_map, List.length_attach]
  have hmain := length_le_card_range π l hnd_l
  rwa [hlen] at hmain

private theorem mem_spanN_singleton (y : ℕ) : ∀ z, z ∈ spanN [y] ↔ z = 0 ∨ z = y := by
  intro z
  unfold spanN
  rw [List.foldl_cons, List.foldl_nil]
  by_cases hy : y = 0
  · subst hy
    simp
  · have hc : ([0] : List ℕ).contains y = false := by
      cases hcont : ([0] : List ℕ).contains y with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.mp hcont) (by simp [hy])
    rw [hc]
    simp only [Bool.false_eq_true, if_false]
    simp [Nat.zero_xor]

theorem card_vecStab_mul_le {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) {l : List ℕ} (hnd : l.Nodup)
    (hpos : ∀ x ∈ l, 0 < x) (hl : ∀ x ∈ l, ∃ h ∈ G0, gmv h c = x) :
    l.length * Nat.card (vecStab c) ≤ Nat.card G0 := by
  classical
  have hinj_l : Function.Injective (fun x : {x // x ∈ l} => spanSub [x.1]) := by
    intro x y hxy
    apply Subtype.ext
    have hxlt : x.1 < 4096 := by
      obtain ⟨h, _, hhx⟩ := hl x.1 x.2
      rw [← hhx]
      exact gmv_lt h c
    have hylt : y.1 < 4096 := by
      obtain ⟨h, _, hhy⟩ := hl y.1 y.2
      rw [← hhy]
      exact gmv_lt h c
    have hxy' : spanSub [x.1] = spanSub [y.1] := hxy
    have hmem : dc x.1 ∈ spanSub [y.1] :=
      hxy' ▸ Subgroup.subset_closure ⟨x.1, List.mem_singleton_self x.1, rfl⟩
    have hcode : x.1 ∈ spanN [y.1] := by
      rw [← cd_dc hxlt]
      refine (mem_spanSub_iff ?_ (dc x.1)).mp hmem
      intro cc hcc
      rw [List.mem_singleton] at hcc
      subst hcc
      exact hylt
    rcases (mem_spanN_singleton y.1 x.1).mp hcode with h0 | hyx
    · exact absurd h0 (ne_of_gt (hpos x.1 x.2))
    · exact hyx
  have hndS : (l.map (fun x => spanSub [x])).Nodup := by
    rw [← List.attach_map_val (f := fun x => spanSub [x]) (l := l)]
    exact List.Nodup.map hinj_l hnd.attach
  have hl' : ∀ Q ∈ l.map (fun x => spanSub [x]), ∃ h ∈ G0, smulSub h (spanSub [c]) = Q := by
    intro Q hQ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hQ
    obtain ⟨h, hhG, hhc⟩ := hl x hx
    refine ⟨h, hhG, ?_⟩
    rw [smulSub_spanSub]
    simp only [List.map_cons, List.map_nil, hhc]
  have horbit := card_mul_le_of_orbit (H := G0) (spanSub [c])
    (l.map fun x => spanSub [x]) hndS hl'
  rw [List.length_map] at horbit
  have hle : vecStab c ≤ ptStab glHom G0 (spanSub [c]) := by
    intro gg hg
    rw [mem_vecStab_iff hc gg] at hg
    obtain ⟨hgG, hgc⟩ := hg
    rw [mem_ptStab_iff, smulSub_spanSub]
    exact ⟨hgG, by simp only [List.map_cons, List.map_nil, hgc]⟩
  have hcardle : Nat.card (vecStab c) ≤ Nat.card (ptStab glHom G0 (spanSub [c])) :=
    Subgroup.card_le_of_le hle
  calc l.length * Nat.card (vecStab c)
      ≤ l.length * Nat.card (ptStab glHom G0 (spanSub [c])) := Nat.mul_le_mul_left _ hcardle
    _ ≤ Nat.card G0 := horbit

theorem spanSub_append (b b' : List ℕ) : spanSub b ⊔ spanSub b' = spanSub (b ++ b') := by
  rw [spanSub, spanSub, spanSub, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact ⟨c, List.mem_append.mpr (Or.inl hc), rfl⟩
    · exact ⟨c, List.mem_append.mpr (Or.inr hc), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact Or.inl ⟨c, hc, rfl⟩
    · exact Or.inr ⟨c, hc, rfl⟩

end CFSG.Quasithin.AppendixH.H12.Model
