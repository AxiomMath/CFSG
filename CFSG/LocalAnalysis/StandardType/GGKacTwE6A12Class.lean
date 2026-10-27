module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType

private theorem twE6_a12_kacRow_type {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p)
    (htag : lab.tag = .twE6) : row.T = .E6 ∧ row.tw = true := by
  have h := row.type_eq
  unfold ggKacTypeOfLabel at h
  rw [htag] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

private theorem twE6_a12_kacRow_d {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p)
    (hn : lab.n = 1) (hp : p = 3) : row.d = 2 := by
  have h : ¬ 3 ∣ 2 ^ 1 - 1 := by decide
  rw [row.d_eq, hn, hp, if_neg h]

private theorem twE6_a12_kac_check :
    ∀ s ∈ (k0VecsAux (k0DiagOf (GGKacType.E6)).marks 3).filter
        (fun s => decide (k0OrbMin (k0DiagOf (GGKacType.E6)) s = s)),
      ∀ base ∈ (k0KacBase (k0DiagOf (GGKacType.E6))
          (k0Rho0 (k0DiagOf (GGKacType.E6)) true 2) s).toList,
        ∀ rho ∈ k0Reps
            (((k0DiagOf (GGKacType.E6)).omega).filter (fun w => decide (k0pAct w s = s))) base,
          (∃ o ∈ (k0Datum (k0DiagOf (GGKacType.E6)) s rho 2 1
              (((k0DiagOf (GGKacType.E6)).omega.filter
                (fun w => decide (k0pAct w s = s))).length)).orbits,
            (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 1) ∧ o.qs = false) →
          (s.getD 1 0 + s.getD 5 0) % 3 ≠ (s.getD 3 0 + s.getD 6 0) % 3 := by
  decide +kernel

theorem kacRow_twE6_a12_kac_mod_three {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p)
    (htag : lab.tag = .twE6) (hn : lab.n = 1) (hp : p = 3)
    (j : Fin row.D.orbits.length) (hj : row.D.orbits[j].lab = ⟨.A, 1, 1⟩)
    (hjqs : row.D.orbits[j].qs = false) :
    ¬ row.s.getD 1 0 + row.s.getD 5 0 ≡ row.s.getD 3 0 + row.s.getD 6 0 [MOD 3] := by
  obtain ⟨hT, htw⟩ := twE6_a12_kacRow_type row htag
  have hd : row.d = 2 := twE6_a12_kacRow_d row hn hp
  have hsmin : k0OrbMin (k0DiagOf (GGKacType.E6)) row.s = row.s := by
    rw [← hT]
    exact row.s_min
  have hs : row.s ∈ (k0VecsAux (k0DiagOf (GGKacType.E6)).marks 3).filter
      (fun s => decide (k0OrbMin (k0DiagOf (GGKacType.E6)) s = s)) := by
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · simpa [hT, hn, hp] using row.s_mem
    · simp [hsmin]
  have hsbase : k0KacBase (k0DiagOf (GGKacType.E6))
      (k0Rho0 (k0DiagOf (GGKacType.E6)) true 2) row.s = some row.base := by
    have h := row.base_eq
    rw [hT, htw, hd] at h
    exact h
  have hbase : row.base ∈ (k0KacBase (k0DiagOf (GGKacType.E6))
      (k0Rho0 (k0DiagOf (GGKacType.E6)) true 2) row.s).toList := by
    rw [hsbase]
    simp
  have hreps : row.rho ∈ k0Reps (((k0DiagOf (GGKacType.E6)).omega).filter
      (fun w => decide (k0pAct w row.s = row.s))) row.base := by
    have h := row.rho_mem
    rw [hT] at h
    exact h
  have hex : ∃ o ∈ (k0Datum (k0DiagOf (GGKacType.E6)) row.s row.rho 2 1
      (((k0DiagOf (GGKacType.E6)).omega.filter
        (fun w => decide (k0pAct w row.s = row.s))).length)).orbits,
      (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 1) ∧ o.qs = false := by
    have hD := row.D_eq
    rw [hT, hd, hn] at hD
    refine ⟨row.D.orbits[j], ?_, ?_⟩
    · rw [← hD]
      exact List.getElem_mem j.2
    · rw [hj]
      exact ⟨⟨rfl, rfl, rfl⟩, hjqs⟩
  simpa only [Nat.ModEq] using
    twE6_a12_kac_check row.s hs row.base hbase row.rho hreps hex

end CFSG.StandardType.GGK0MarkedKacIface1587
