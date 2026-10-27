module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteSevenList
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcNF
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcWord

public section

namespace CFSG.Quasithin.Fan86.Tutte.Seven

variable {H : Type*} [Group H] {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem contra_of_conj {hh hs d : H} (h : IsTutteSys 7 r l ξ Hs)
    (hpar : ∃ L : List ℤ, L.Pairwise (· > ·) ∧ (∀ t ∈ L, 1 ≤ t ∧ t < 7) ∧ Odd L.length ∧
      nfw r l (-1) L = hh)
    (hstar : ∀ L : List ℤ, Odd L.length → nfw r l (-1) L = hh →
      nfw r l (-1) (L.map fun t => 7 - t) = hs)
    (hsupp : ∀ L : List ℤ, L.Pairwise (· > ·) → (∀ t ∈ L, 1 ≤ t ∧ t < 7) → Odd L.length →
      nfw r l (-1) L = hh → ((6 : ℤ) ∈ L ↔ (1 : ℤ) ∈ L))
    (hd : d ∈ Hs 5) (hrel : hs * tx r l 6 * hh = d) : False := by
  obtain ⟨L, hL, hL1, hodd, hLh⟩ := hpar
  have hLs := hstar L hodd hLh
  have h6mem := hsupp L hL hL1 hodd hLh
  have hx6 : tx r l 6 ∉ Hs 5 := by simpa using h.x_not_mem 6 (by norm_num) (by norm_num)
  by_cases h6 : (6 : ℤ) ∈ L
  · have h1 : (1 : ℤ) ∈ L := h6mem.mp h6
    obtain ⟨L', hL'eq, hL'lt⟩ := head_eq hL (fun t ht => by have := (hL1 t ht).2; omega) h6
    obtain ⟨L'', hL''eq, hL''gt⟩ := last_eq hL (fun t ht => (hL1 t ht).1) h1
    have hL'ent : ∀ t ∈ L', 1 ≤ t ∧ t ≤ (5 : ℕ) := fun t ht =>
      ⟨(hL1 t (by rw [hL'eq]; exact List.mem_cons_of_mem _ ht)).1, by have := hL'lt t ht; omega⟩
    have hL''ent : ∀ t ∈ L'', 2 ≤ t ∧ t ≤ 6 := fun t ht =>
      ⟨by have := hL''gt t ht; omega,
        by have := (hL1 t (by rw [hL''eq]; exact List.mem_append_left _ ht)).2; omega⟩
    have hwmem : nfw r l 1 L' ∈ Hs 5 := nfw_mem h (by norm_num) 1 hL'ent
    have hw'mem : nfw r l (-1) (L''.map fun t => 7 - t) ∈ Hs 5 :=
      nfw_mem h (by norm_num) (-1) fun t ht => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
        have := hL''ent u hu
        push_cast
        omega
    have hhh : hh = (tx r l 6)⁻¹ * nfw r l 1 L' := by
      rw [← hLh, hL'eq]
      simp [nfw]
    have hLlen : Even L''.length := by
      have h2 : Odd (L''.length + 1) := by simpa [hL''eq] using hodd
      rw [Nat.even_iff]
      rw [Nat.odd_iff] at h2
      omega
    have hhs : hs = nfw r l (-1) (L''.map fun t => 7 - t) * (tx r l 6)⁻¹ := by
      rw [← hLs, hL''eq, List.map_append, List.map_cons, List.map_nil, nfw_append]
      simp [hLlen, nfw]
    have hd' : d = nfw r l (-1) (L''.map fun t => 7 - t) * (tx r l 6)⁻¹ * nfw r l 1 L' := by
      rw [← hrel, hhs, hhh]
      group
    apply hx6
    have hinv : (tx r l 6)⁻¹ ∈ Hs 5 := by
      have : (tx r l 6)⁻¹ = (nfw r l (-1) (L''.map fun t => 7 - t))⁻¹ * d * (nfw r l 1 L')⁻¹ := by
        rw [hd']
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hw'mem) hd) (inv_mem hwmem)
    simpa using (Hs 5).inv_mem hinv
  · have h1 : (1 : ℤ) ∉ L := fun h1 => h6 (h6mem.mpr h1)
    have hent : ∀ t ∈ L, 2 ≤ t ∧ t ≤ 5 := by
      intro t ht
      have := hL1 t ht
      have h6' : t ≠ 6 := fun e => h6 (e ▸ ht)
      have h1' : t ≠ 1 := fun e => h1 (e ▸ ht)
      omega
    have hhh : hh ∈ Hs 5 := hLh ▸ nfw_mem h (by norm_num) (-1) fun t ht =>
      ⟨by have := hent t ht; omega, by have := (hent t ht).2; push_cast; omega⟩
    have hss : hs ∈ Hs 5 := hLs ▸ nfw_mem h (by norm_num) (-1) (L := L.map fun t => 7 - t) (by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      have := hent u hu
      push_cast
      omega)
    apply hx6
    have : tx r l 6 = hs⁻¹ * d * hh⁻¹ := by
      rw [← hrel]
      group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hss) hd) (inv_mem hhh)

end CFSG.Quasithin.Fan86.Tutte.Seven
