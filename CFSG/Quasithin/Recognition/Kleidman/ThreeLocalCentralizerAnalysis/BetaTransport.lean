module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaModels
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

variable {X Y : Type*} [Group X] [Fintype X] [DecidableEq X] [Group Y] [Fintype Y] [DecidableEq Y]

theorem mem_centSet_iff {c x : X} : x ∈ centSet c ↔ x * c = c * x := by
  simp [centSet]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem kleinSet_map (e : X ≃* Y) (c t : X) : kleinSet (e c) (e t) = (kleinSet c t).map e := by
  simp [kleinSet, map_mul, map_one]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem mem_map_iff_of_mulEquiv (e : X ≃* Y) {L : List X} {x : X} : e x ∈ L.map e ↔ x ∈ L := by
  rw [List.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => e.injective h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem mem_normSet_iff {c t g : X} :
    g ∈ normSet c t ↔ ∀ v ∈ kleinSet c t, g * v * g⁻¹ ∈ kleinSet c t := by
  simp [normSet]

theorem normSet_eq_all (c t : X) : normSet c t = Finset.univ.filter
    (fun g => (kleinSet c t).all (fun v => decide (g * v * g⁻¹ ∈ kleinSet c t)) = true) := by
  ext g
  simp [normSet, List.all_eq_true]

theorem map_mem_normSet_iff (e : X ≃* Y) {c t g : X} :
    e g ∈ normSet (e c) (e t) ↔ g ∈ normSet c t := by
  rw [mem_normSet_iff, mem_normSet_iff, kleinSet_map, List.forall_mem_map]
  refine forall₂_congr fun v _ => ?_
  rw [← map_inv, ← map_mul, ← map_mul, mem_map_iff_of_mulEquiv]

theorem normSet_map (e : X ≃* Y) (c t : X) :
    normSet (e c) (e t) = (normSet c t).map e.toEquiv.toEmbedding := by
  ext y
  obtain ⟨g, rfl⟩ := e.surjective y
  rw [map_mem_normSet_iff, Finset.mem_map]
  constructor
  · exact fun h => ⟨g, h, rfl⟩
  · rintro ⟨g', hg', h⟩
    rwa [show g = g' from e.injective h.symm]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem betaTup_map (e : X ≃* Y) (a2 a3 a4 s : X) :
    betaTup (e a2) (e a3) (e a4) (e s) = fun i => e (betaTup a2 a3 a4 s i) := by
  funext i
  fin_cases i <;> simp [betaTup]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem evalWord_mulEquiv (e : X ≃* Y) (t : Fin 7 → X) (r : List (Fin 7 × Bool)) :
    evalWord (fun i => e (t i)) r = e (evalWord t r) := by
  simp only [evalWord, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply]
  split_ifs <;> simp

theorem BetaCheck.of_mulEquiv (e : X ≃* Y) {c0 : X} (h : BetaCheck Y (e c0)) : BetaCheck X c0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨e.injective (by rw [map_mul, h1, map_one]), fun hc => h2 (by rw [hc, map_one]), ?_, ?_⟩
  · intro a ha1 ha2
    obtain ⟨g', hg'⟩ := h3 (e a) (by rw [← map_mul, ha1, map_one])
      (fun h => ha2 (e.injective (by rw [h, map_one])))
    obtain ⟨g, rfl⟩ := e.surjective g'
    exact ⟨g, e.injective (by rw [map_mul, map_mul, map_inv, hg'])⟩
  · intro a2 ha2 a3 ha3 hrel
    have hc2 : e a2 ∈ centSet (e c0) := by
      rw [mem_centSet_iff] at ha2 ⊢; rw [← map_mul, ← map_mul, ha2]
    have hc3 : e a3 ∈ centSet (e c0) := by
      rw [mem_centSet_iff] at ha3 ⊢; rw [← map_mul, ← map_mul, ha3]
    have hrel' : ∀ r ∈ d8Rels, evalWord (betaTup (e a2) (e a3) (e c0) 1) r = 1 := by
      intro r hr
      rw [← map_one e, betaTup_map, evalWord_mulEquiv, hrel r hr, map_one]
    obtain ⟨t', ht1, ht2, ht3, ht4, hcard, hmul, hinv, hm2, hm3, hmc, hcube, s', hs', hsr⟩ :=
      h4 (e a2) hc2 (e a3) hc3 hrel'
    obtain ⟨t, rfl⟩ := e.surjective t'
    obtain ⟨s, rfl⟩ := e.surjective s'
    have mem : ∀ g, e g ∈ normSet (e c0) (e t) ↔ g ∈ normSet c0 t := fun g => map_mem_normSet_iff e
    refine ⟨t, e.injective (by rw [map_mul, ht1, map_one]),
      e.injective (by rw [map_mul, map_mul, ht2]),
      fun h => ht3 (by rw [h, map_one]), fun h => ht4 (by rw [h]),
      by rw [← hcard, normSet_map, Finset.card_map], ?_, ?_, (mem a2).1 hm2, (mem a3).1 hm3,
      (mem c0).1 hmc, ?_, s, (mem s).1 hs', ?_⟩
    · intro x hx y hy
      rw [← mem, map_mul]
      exact hmul _ ((mem x).2 hx) _ ((mem y).2 hy)
    · intro x hx
      rw [← mem, map_inv]
      exact hinv _ ((mem x).2 hx)
    · intro x hx hx3 hx1
      obtain ⟨u', hu', hu⟩ := hcube (e x) ((mem x).2 hx) (by rw [← map_pow, hx3, map_one])
        (fun h => hx1 (e.injective (by rw [h, map_one])))
      obtain ⟨u, rfl⟩ := e.surjective u'
      exact ⟨u, (mem u).1 hu', e.injective (by rw [map_mul, map_mul, map_inv, map_inv, hu])⟩
    · intro r hr
      have := hsr r hr
      rw [betaTup_map, evalWord_mulEquiv] at this
      exact e.injective (by rw [this, map_one])

end CFSG.Quasithin.Kleidman.ThreeLocal
