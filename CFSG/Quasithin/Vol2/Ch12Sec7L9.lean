module

public import CFSG.Quasithin.Vol2.Ch12Sec7Orb

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mem_conj_of_conj_eq {L : Subgroup G} {i j l₁ l₂ : G} (hl₁ : l₁ ∈ L)
    (hl₂ : l₂ ∈ L) (h : l₁ * i * l₁⁻¹ = l₂ * j * l₂⁻¹) : ∃ l ∈ L, l * i * l⁻¹ = j :=
  ⟨l₂⁻¹ * l₁, L.mul_mem (L.inv_mem hl₂) hl₁, by
    calc l₂⁻¹ * l₁ * i * (l₂⁻¹ * l₁)⁻¹ = l₂⁻¹ * (l₁ * i * l₁⁻¹) * l₂ := by group
      _ = l₂⁻¹ * (l₂ * j * l₂⁻¹) * l₂ := by rw [h]
      _ = j := by group⟩

omit [Finite G] in
theorem conj_cross {i j a b l₁ l₂ g : G} (h₁ : l₁ * i * l₁⁻¹ = a) (h₂ : l₂ * j * l₂⁻¹ = b)
    (hg : g * i * g⁻¹ = j) : l₂ * g * l₁⁻¹ * a * (l₂ * g * l₁⁻¹)⁻¹ = b := by
  rw [← h₁, ← h₂, ← hg]
  group

theorem conj_ne_of_centralizer_le {T L V : Subgroup G} {t : G} (hS : Setting1273 G T L V t)
    {z : G} (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) (g : G) : g * z * g⁻¹ ≠ t := by
  intro hgz
  set T' := T.map (MulAut.conj g).toMonoidHom with hT'
  have hT'C : T' ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxz := Subgroup.mem_centralizer_singleton_iff.1 (hTz hx)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgz]
    show g * x * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [hxz]
      _ = g * z * g⁻¹ * (g * x * g⁻¹) := by group
  have hT'N : T' ≤ Subgroup.normalizer (L : Set G) := hT'C.trans hS.Gt_le
  have hsyl := hS.hyp.hyp.sylow
  have hT'syl : QuasithinUnique.IsSylowTwoOf T' (L ⊔ T') := by
    refine ⟨le_sup_right, hsyl.1.map _, fun h2 => hsyl.2 ?_⟩
    have h1 : T'.index = T.index := Subgroup.index_map_of_bijective (MulAut.conj g).bijective T
    rw [← h1]
    exact h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right)
  have hTL := B6.isSylowTwoOf_inf_normal hT'syl le_sup_left (sup_le Subgroup.le_normalizer hT'N)
  have hdvd : (Subgroup.centralizer ({t} : Set G)).relIndex L ∣ (T' ⊓ L).relIndex L :=
    Subgroup.relIndex_dvd_of_le_left L (inf_le_left.trans hT'C)
  rw [hS.orbit_t] at hdvd
  exact hTL.2.2 ((show 2 ∣ 18 by norm_num).trans hdvd)

theorem orbits_z_t (h1222 : Stmt12_2_2) {T L V : Subgroup G} {t : G}
    (hS : Setting1273 G T L V t) :
    ∃ z ∈ V, T ≤ Subgroup.centralizer ({z} : Set G) ∧
      ∀ v ∈ V, v ≠ 1 → (∃ l ∈ L, l * v * l⁻¹ = z) ∨ (∃ l ∈ L, l * v * l⁻¹ = t) := by
  obtain ⟨z, hzV₁, -, hTz, t₀, -, -, h45, -, horb⟩ := lemma12_7_4_part1_of h1222 hS.hyp
  have ht1 : t ≠ 1 := ne_one_of_relIndex hS.orbit_t (by decide)
  obtain ⟨l, hl, hlt⟩ : ∃ l ∈ L, l * t * l⁻¹ = t₀ := by
    rcases horb t hS.t_mem ht1 with ⟨l, hl, hlt⟩ | h
    · have h18 := hS.orbit_t
      rw [← relIndex_centralizer_conj hl, hlt, h45] at h18
      exact absurd h18 (by decide)
    · exact h
  refine ⟨z, (Subgroup.mem_inf.1 hzV₁).1, hTz, fun v hv hv1 => ?_⟩
  rcases horb v hv hv1 with h | ⟨m, hm, hmv⟩
  · exact Or.inl h
  · refine Or.inr ⟨l⁻¹ * m, L.mul_mem (L.inv_mem hl) hm, ?_⟩
    calc l⁻¹ * m * v * (l⁻¹ * m)⁻¹ = l⁻¹ * (m * v * m⁻¹) * l := by group
      _ = l⁻¹ * (l * t * l⁻¹) * l := by rw [hmv, hlt]
      _ = t := by group

theorem exists_conj_L_of_conj (h1222 : Stmt12_2_2) {T L V : Subgroup G} {t : G}
    (hS : Setting1273 G T L V t) (i : G) (hi : i ∈ V) (j : G) (hj : j ∈ V)
    (hij : ∃ g : G, g * i * g⁻¹ = j) : ∃ l ∈ L, l * i * l⁻¹ = j := by
  obtain ⟨g, hg⟩ := hij
  by_cases hi1 : i = 1
  · refine ⟨1, L.one_mem, ?_⟩
    rw [← hg, hi1]
    group
  have hj1 : j ≠ 1 := by
    rintro rfl
    apply hi1
    calc i = g⁻¹ * (g * i * g⁻¹) * g := by group
      _ = 1 := by rw [hg]; group
  obtain ⟨z, -, hTz, horb⟩ := orbits_z_t h1222 hS
  have hzt := conj_ne_of_centralizer_le hS hTz
  rcases horb i hi hi1 with ⟨l₁, hl₁, h₁⟩ | ⟨l₁, hl₁, h₁⟩ <;>
    rcases horb j hj hj1 with ⟨l₂, hl₂, h₂⟩ | ⟨l₂, hl₂, h₂⟩
  · exact exists_mem_conj_of_conj_eq hl₁ hl₂ (h₁.trans h₂.symm)
  · exact absurd (conj_cross h₁ h₂ hg) (hzt _)
  · exact absurd (conj_cross h₂ h₁ (show g⁻¹ * j * g⁻¹⁻¹ = i by rw [← hg]; group)) (hzt _)
  · exact exists_mem_conj_of_conj_eq hl₁ hl₂ (h₁.trans h₂.symm)

theorem conjClass_inter_eq_of (h1222 : Stmt12_2_2) {T L V : Subgroup G} {t : G}
    (hS : Setting1273 G T L V t) {v : G} (hv : v ∈ V) :
    {y | ∃ g : G, g⁻¹ * v * g = y} ∩ (V : Set G) =
      {y | ∃ n ∈ Subgroup.normalizer (V : Set G), n⁻¹ * v * n = y} := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hS.hyp.hyp.irrPlus.2.2.1
  ext y
  constructor
  · rintro ⟨⟨g, rfl⟩, hy⟩
    obtain ⟨l, hl, hly⟩ := exists_conj_L_of_conj h1222 hS v hv _ hy ⟨g⁻¹, by rw [inv_inv]⟩
    refine ⟨l⁻¹, Subgroup.inv_mem _ (hLV hl), ?_⟩
    rw [inv_inv]
    exact hly
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) v).1 hv
    simpa using this

theorem exists_centralizer_conj_of_mem (h1222 : Stmt12_2_2) {T L V : Subgroup G} {t : G}
    (hS : Setting1273 G T L V t) {v : G} (hv : v ∈ V) (g₁ g₂ : G)
    (h₁ : v ∈ conjSubgroup V g₁) (h₂ : v ∈ conjSubgroup V g₂) :
    ∃ c ∈ Subgroup.centralizer ({v} : Set G), conjSubgroup V g₂ = conjSubgroup V (g₁ * c) := by
  obtain ⟨c, hc, hce⟩ := (conjClass_inter_eq_iff_centralizer_transitive hv).1
    (conjClass_inter_eq_of h1222 hS hv) _ ⟨g₁, rfl⟩ _ ⟨g₂, rfl⟩ h₁ h₂
  exact ⟨c, hc, by rw [← hce, conjSubgroup_conjSubgroup]⟩

theorem conj_eq_of_t_mem (h1222 : Stmt12_2_2) {T L V : Subgroup G} {t : G}
    (hS : Setting1273 G T L V t) {g : G} (ht : t ∈ conjSubgroup V g) : conjSubgroup V g = V := by
  have hy := hS.hyp.hyp
  obtain ⟨hTN, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
    hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
  obtain ⟨⟨hVT, -⟩, hTI, -⟩ := hall V hy.irrPlus
  have hTI' : IsTISetIn V (Subgroup.normalizer (L : Set G)) := by
    refine ⟨hVT.trans hTN, fun m hm hmV => ?_⟩
    rcases hTI m hm with h | h
    · exact absurd (conjSubgroup_eq_iff_mem_normalizer.1 h) hmV
    · exact h
  have ht1 : t ≠ 1 := ne_one_of_relIndex hS.orbit_t (by decide)
  have hu := existsUnique_conjugate_mem_of_isTISetIn hS.t_mem ht1 hTI'
    (conjClass_inter_eq_of h1222 hS hS.t_mem) hS.Gt_le
  exact hu.unique ⟨⟨g, rfl⟩, ht⟩ ⟨⟨1, (conjSubgroup_one V).symm⟩, hS.t_mem⟩

end S127

open S127 in
theorem lemma12_7_9_of (h1222 : Stmt12_2_2) : Lemma12_7_9 := by
  intro G _ _ T L V t hS
  refine ⟨fun i hi j hj hij => ?_, fun v hv g₁ g₂ h₁ h₂ =>
    exists_centralizer_conj_of_mem h1222 hS hv g₁ g₂ h₁ h₂, fun g ht =>
    conj_eq_of_t_mem h1222 hS ht⟩
  obtain ⟨l, hl, hlij⟩ := exists_conj_L_of_conj h1222 hS i hi j hj hij
  exact ⟨l, Subgroup.le_normalizer hl, hlij⟩

end CFSG.Quasithin.H13
