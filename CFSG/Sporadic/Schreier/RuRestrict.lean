
module

public import CFSG.Sporadic.Schreier.RuRestrictBase

public import CFSG.Sporadic.Schreier.RuCheckOrbits

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

theorem ruC_orbit_lab (x : Fin 4060) :
    MulAction.orbit ruC x = {y : Fin 4060 | ruCLab[(y : ℕ)]! = ruCLab[(x : ℕ)]!} := by
  have h := orbit_eq_label rep_ruCPair ruOrbits_check.2.2.2.2.2.2.2.2.1 x
  rw [show (#[ruC0A, ruC1A].size) = 2 from rfl, genSubgroup_pair] at h
  exact h

theorem ruN_orbit_lab (x : Fin 4060) :
    MulAction.orbit ruN x = {y : Fin 4060 | ruNLab[(y : ℕ)]! = ruNLab[(x : ℕ)]!} := by
  have h := orbit_eq_label rep_ruNsPair' ruOrbits_check.2.2.2.2.2.2.2.2.2 x
  rw [show (#[ruNs0A, ruNs1A].size) = 2 from rfl, genSubgroup_pair] at h
  exact h

theorem ruCOrbit_iff {k : ℕ} (hk : k < 4) (x : Fin 4060) :
    x ∈ ptSet 4060 (ruCOrbit k) ↔ ruCLab[(x : ℕ)]! = k := by
  rw [← ruCOrbits_getD hk]
  exact (labListsOK_spec ruOrbits_check.2.2.2.2.2.2.1).2 k (by simpa [ruCOrbits] using hk) x

theorem ruNOrbit_iff {k : ℕ} (hk : k < 3) (x : Fin 4060) :
    x ∈ ptSet 4060 (ruNOrbit k) ↔ ruNLab[(x : ℕ)]! = k := by
  rw [← ruNOrbits_getD hk]
  exact (labListsOK_spec ruOrbits_check.2.2.2.2.2.2.2.1).2 k (by simpa [ruNOrbits] using hk) x

theorem ruCLab_lt (x : Fin 4060) : ruCLab[(x : ℕ)]! < 4 := by
  have := (labListsOK_spec ruOrbits_check.2.2.2.2.2.2.1).1 x
  simpa [ruCOrbits] using this

theorem ruNLab_lt (x : Fin 4060) : ruNLab[(x : ℕ)]! < 3 := by
  have := (labListsOK_spec ruOrbits_check.2.2.2.2.2.2.2.1).1 x
  simpa [ruNOrbits] using this

theorem ruC_orbit
    {k : ℕ} (hk : k < 4) {x : Fin 4060} (hx : x ∈ ptSet 4060 (ruCOrbit k)) :
    MulAction.orbit ruC x = ptSet 4060 (ruCOrbit k) := by
  rw [ruC_orbit_lab]
  ext y
  rw [Set.mem_ofPred_eq, ruCOrbit_iff hk, (ruCOrbit_iff hk x).1 hx]

theorem ruN_orbit
    {k : ℕ} (hk : k < 3) {x : Fin 4060} (hx : x ∈ ptSet 4060 (ruNOrbit k)) :
    MulAction.orbit ruN x = ptSet 4060 (ruNOrbit k) := by
  rw [ruN_orbit_lab]
  ext y
  rw [Set.mem_ofPred_eq, ruNOrbit_iff hk, (ruNOrbit_iff hk x).1 hx]

theorem ruCOrbit_cover
    (x : Fin 4060) : ∃ k < 4, x ∈ ptSet 4060 (ruCOrbit k) :=
  ⟨_, ruCLab_lt x, (ruCOrbit_iff (ruCLab_lt x) x).2 rfl⟩

theorem ruNOrbit_cover
    (x : Fin 4060) : ∃ k < 3, x ∈ ptSet 4060 (ruNOrbit k) :=
  ⟨_, ruNLab_lt x, (ruNOrbit_iff (ruNLab_lt x) x).2 rfl⟩

theorem ruC_mapsTo
    {k : ℕ} (hk : k < 4) {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruC) :
    ∀ x ∈ ptSet 4060 (ruCOrbit k), g x ∈ ptSet 4060 (ruCOrbit k) := by
  intro x hx
  rw [← ruC_orbit hk hx]
  exact ⟨⟨g, hg⟩, rfl⟩

theorem ruC_le_stabF :
    ruC ≤ MulAction.stabilizer (Equiv.Perm (Fin 4060)) (ptSet 4060 ruF) := by
  intro g hg
  rw [ruOrbits_check.2.2.1]
  exact mem_stabilizer_ptSet (ruC_mapsTo (by norm_num) hg)

theorem ruC_le_stabY :
    ruC ≤ MulAction.stabilizer (Equiv.Perm (Fin 4060)) (ptSet 4060 ruY) := by
  intro g hg
  rw [ruOrbits_check.2.2.2.1]
  exact mem_stabilizer_ptSet (ruC_mapsTo (by norm_num) hg)

theorem ruF_ptList :
    PtList 4060 ruF := (ptPosOK_spec ruOrbits_check.1).1

theorem ruY_ptList :
    PtList 4060 ruY := (ptPosOK_spec ruOrbits_check.2.1).1

@[expose] def ruResF :
    ruC →* Equiv.Perm (Fin 1920) :=
  (Equiv.permCongrHom (finCongr ruF_size)).toMonoidHom.comp
    ((resHom ruF_ptList).comp (Subgroup.inclusion ruC_le_stabF))

@[expose] def ruResY :
    ruC →* Equiv.Perm (Fin 80) :=
  (Equiv.permCongrHom (finCongr ruY_size)).toMonoidHom.comp
    ((resHom ruY_ptList).comp (Subgroup.inclusion ruC_le_stabY))

open scoped Classical in
@[expose] def ruResFPerm
    (g : Equiv.Perm (Fin 4060)) : Equiv.Perm (Fin 1920) :=
  if h : g ∈ ruC then ruResF ⟨g, h⟩ else 1

open scoped Classical in
@[expose] def ruResYPerm
    (g : Equiv.Perm (Fin 4060)) : Equiv.Perm (Fin 80) :=
  if h : g ∈ ruC then ruResY ⟨g, h⟩ else 1

theorem ruResFPerm_of_mem
    {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruC) :
    ruResFPerm g = ruResF ⟨g, hg⟩ := by
  simp only [ruResFPerm, hg, ↓reduceDIte]

theorem ruResYPerm_of_mem
    {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruC) :
    ruResYPerm g = ruResY ⟨g, hg⟩ := by
  simp only [ruResYPerm, hg, ↓reduceDIte]

theorem rep_ruResF
    {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hg : g ∈ ruC) : Rep 1920 (resA ruF ruFPos t) (ruResFPerm g) := by
  rw [ruResFPerm_of_mem hg]
  exact rep_finCongr ruF_size
    (rep_resA ruF_ptList (ptPosOK_spec ruOrbits_check.1).2 ht (ruC_le_stabF hg))

theorem rep_ruResY
    {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hg : g ∈ ruC) : Rep 80 (resA ruY ruYPos t) (ruResYPerm g) := by
  rw [ruResYPerm_of_mem hg]
  exact rep_finCongr ruY_size
    (rep_resA ruY_ptList (ptPosOK_spec ruOrbits_check.2.1).2 ht (ruC_le_stabY hg))

end CFSG.Sporadic.RuSchreier
