module

public import CFSG.RankThree.GF2n.Parrott.Section1
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

theorem conj_eq_of_mem_centralizer_of_commutator_mem {G : Type*} [Group G] {z : G}
    (hz : orderOf z = 2) {U : Subgroup G} (hUH : U ≤ Subgroup.centralizer ({z} : Set G))
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z)
    (hcls : ∀ a ∈ U, ∀ b ∈ U, orderOf a = 2 → orderOf b = 2 → a ≠ z → b ≠ z →
      ∃ k : G, k * a * k⁻¹ = b)
    (hpair : ∀ y ∈ U, orderOf y = 2 → y ≠ z → ∃ a ∈ U, ∃ b ∈ U, orderOf a = 2 ∧ orderOf b = 2 ∧
      a * y = y * a ∧ b * y = y * b ∧ a * b ≠ b * a)
    (hcl : ∀ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) → g * z * g⁻¹ ∈ U) :
    ∀ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) → g * z * g⁻¹ = z := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  intro g hgC
  set y : G := g * z * g⁻¹ with hydef
  by_contra hyne
  have hy2 : orderOf y = 2 := by
    rw [hydef, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz
  have hyU : y ∈ U := hcl g (by simpa [hydef] using hgC)
  obtain ⟨a, haU, b, hbU, ha2, hb2, hay, hby, hab⟩ := hpair y hyU hy2 hyne
  have hza : z * a = a * z := (Subgroup.mem_centralizer_singleton_iff.mp (hUH haU)).symm
  have hzb : z * b = b * z := (Subgroup.mem_centralizer_singleton_iff.mp (hUH hbU)).symm
  have ha_ne : a ≠ z := by
    rintro rfl
    exact hab (by rw [hzb])
  have hb_ne : b ≠ z := by
    rintro rfl
    exact hab (by rw [hza])
  obtain ⟨k, hk⟩ := hcls y hyU a haU hy2 ha2 hyne ha_ne
  obtain ⟨l, hl⟩ := hcls y hyU b hbU hy2 hb2 hyne hb_ne
  have hgk : g⁻¹ * a * g = (g⁻¹ * k * g) * z * (g⁻¹ * k * g)⁻¹ := by
    rw [← hk, hydef]
    group
  have hgl : g⁻¹ * b * g = (g⁻¹ * l * g) * z * (g⁻¹ * l * g)⁻¹ := by
    rw [← hl, hydef]
    group
  have hza_conj : (g⁻¹ * a * g) * z = z * (g⁻¹ * a * g) := by
    calc (g⁻¹ * a * g) * z = g⁻¹ * (a * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * a) * g := by rw [hay]
      _ = z * (g⁻¹ * a * g) := by group
  have hzb_conj : (g⁻¹ * b * g) * z = z * (g⁻¹ * b * g) := by
    calc (g⁻¹ * b * g) * z = g⁻¹ * (b * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * b) * g := by rw [hby]
      _ = z * (g⁻¹ * b * g) := by group
  have hgaC : (g⁻¹ * k * g) * z * (g⁻¹ * k * g)⁻¹ ∈
      Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgk]
    exact hza_conj
  have hgbC : (g⁻¹ * l * g) * z * (g⁻¹ * l * g)⁻¹ ∈
      Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgl]
    exact hzb_conj
  have hgaU : g⁻¹ * a * g ∈ U := by
    rw [hgk]
    exact hcl (g⁻¹ * k * g) hgaC
  have hgbU : g⁻¹ * b * g ∈ U := by
    rw [hgl]
    exact hcl (g⁻¹ * l * g) hgbC
  set c : G := a * b * a⁻¹ * b⁻¹ with hcdef
  have hcz : c ∈ Subgroup.zpowers z := hcomm a haU b hbU
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
    (hcomm (g⁻¹ * a * g) hgaU (g⁻¹ * b * g) hgbU)
  have hcy : c ∈ Subgroup.zpowers y := by
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    have hy_pow : y ^ n = g * z ^ n * g⁻¹ := by
      rw [hydef, show g * z * g⁻¹ = MulAut.conj g z by rw [MulAut.conj_apply],
        ← map_zpow, MulAut.conj_apply]
    rw [hy_pow, hn, hcdef]
    group
  have hc1 : c = 1 := by
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz).mp hcz with h | h
    · exact h
    · rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hy2).mp hcy with h' | h'
      · exact absurd (h.symm.trans h') hz1
      · exact absurd (h.symm.trans h').symm hyne
  have hcab : a * b = b * a := by
    have h : (a * b) * (b * a)⁻¹ = 1 := by
      rw [← hc1, hcdef]
      group
    exact mul_inv_eq_one.mp h
  exact hab hcab

theorem exists_conj_mem_centralizer_not_mem {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) {U M : Subgroup G} (hUH : U ≤ Subgroup.centralizer ({z} : Set G))
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z)
    (hcls : ∀ a ∈ U, ∀ b ∈ U, orderOf a = 2 → orderOf b = 2 → a ≠ z → b ≠ z →
      ∃ k : G, k * a * k⁻¹ = b)
    (hpair : ∀ y ∈ U, orderOf y = 2 → y ≠ z → ∃ a ∈ U, ∃ b ∈ U, orderOf a = 2 ∧ orderOf b = 2 ∧
      a * y = y * a ∧ b * y = y * b ∧ a * b ≠ b * a)
    (hinv : ∀ x ∈ M, orderOf x = 2 → x ∈ U)
    (hne : Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤) :
    ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ∧ g * z * g⁻¹ ∉ M := by
  obtain ⟨y, ⟨g, hg⟩, hy2, hyC, hyNot⟩ := prop2_conj_centralizer hz hne
  by_contra hno
  push Not at hno
  have hcl : ∀ k : G, k * z * k⁻¹ ∈ Subgroup.centralizer ({z} : Set G) →
      k * z * k⁻¹ ∈ U := by
    intro k hkC
    refine hinv _ (hno k hkC) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz
  have hyC' : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by rwa [hg]
  have hyz : y = z := by
    rw [← hg]
    exact conj_eq_of_mem_centralizer_of_commutator_mem hz hUH hcomm hcls hpair hcl g hyC'
  exact hyNot (by rw [hyz]; exact Subgroup.mem_zpowers z)

end CFSG.RankThree.GF2n.Parrott
