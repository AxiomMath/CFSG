module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_sq {X : Type*} [Group X] {z : X} (h : z * z = 1) :
    IsPGroup 2 (Subgroup.zpowers z) := by
  have hz : z ^ 2 = 1 := by rw [sq]; exact h
  rintro ⟨_, m, rfl⟩
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (z ^ m) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

variable [Finite G]

theorem exists_mem_normalizer_not_mem {Q P : Subgroup G} (hP : IsPGroup 2 P) (hQP : Q ≤ P)
    (hne : Q ≠ P) : ∃ t ∈ P, t ∈ Subgroup.normalizer (Q : Set G) ∧ t ∉ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    exact le_antisymm hQP (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := P) _ hlt
  obtain ⟨t, htN, htQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQP, Subgroup.mem_subgroupOf] at htN
  exact ⟨t, t.2, htN, fun h => htQ (Subgroup.mem_subgroupOf.mpr h)⟩

omit [Finite G] in
theorem mem_of_isSylowTwoOf_of_central {P T : Subgroup G} {z : G} (hz2 : z * z = 1) (hzP : z ∈ P)
    (hc : ∀ q ∈ P, q * z = z * q) (hT : IsSylowTwoOf T P) : z ∈ T := by
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow hT
  set z' : ↥P := ⟨z, hzP⟩ with hz'
  have hzc : ∀ g : ↥P, Commute g z' := fun g => Subtype.ext (hc g g.2)
  have hnorm : (Subgroup.zpowers z').Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [((hzc g).zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers z' k⟩
  have hP : IsPGroup 2 (Subgroup.zpowers z') :=
    isPGroup_zpowers_of_sq (Subtype.ext hz2)
  have h1 : z' ∈ (S : Subgroup _) := hP.le_sylow_of_normal S (Subgroup.mem_zpowers z')
  rw [hS] at h1
  exact Subgroup.mem_subgroupOf.1 h1

omit [Finite G] in
theorem mem_of_isSylowTwoOf_centralizer {z : G} (hz2 : z * z = 1) {T : Subgroup G}
    (hT : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G))) : z ∈ T :=
  mem_of_isSylowTwoOf_of_central (P := Subgroup.centralizer ({z} : Set G)) hz2
    (Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh])
    (fun q hq => (Subgroup.mem_centralizer_iff.1 hq z rfl).symm) hT

theorem isSylowTwoOf_top {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1) {T : Subgroup G}
    (hT : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)))
    (hZ : ∀ w ∈ T, (∀ t ∈ T, t * w = w * t) → w = 1 ∨ w = z)
    (hN : ∀ h ∈ Subgroup.centralizer ({z} : Set G), (∀ t ∈ T, h * t * h⁻¹ ∈ T) →
      (∀ t ∈ T, h⁻¹ * t * h ∈ T) → h ∈ T) :
    IsSylowTwoOf T ⊤ := by
  classical
  have hzT : z ∈ T := mem_of_isSylowTwoOf_centralizer hz2 hT
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  by_cases hTeq : T = (S : Subgroup G)
  · refine F7.isSylowTwoOf_of_relIndex le_top hT.2.1 ?_
    rw [Subgroup.relIndex_top_right, hTeq]
    exact S.not_dvd_index
  · exfalso
    obtain ⟨t, htS, htN, htT⟩ := exists_mem_normalizer_not_mem S.isPGroup' hTS hTeq
    have hconj : ∀ s ∈ T, t * s * t⁻¹ ∈ T := fun s hs => (Subgroup.mem_normalizer_iff.1 htN s).1 hs
    have hconj' : ∀ s ∈ T, t⁻¹ * s * t ∈ T := fun s hs => by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ htN) s).1 hs
      simpa using this
    have htz : t * z * t⁻¹ ∈ T := hconj z hzT
    have hTz : ∀ s ∈ T, s * z = z * s := fun s hs =>
      (Subgroup.mem_centralizer_iff.1 (hT.1 hs) z rfl).symm
    have hcomm : ∀ s ∈ T, s * (t * z * t⁻¹) = (t * z * t⁻¹) * s := by
      intro s hs
      have h1 := hTz _ (hconj' s hs)
      calc s * (t * z * t⁻¹) = t * ((t⁻¹ * s * t) * z) * t⁻¹ := by group
        _ = t * (z * (t⁻¹ * s * t)) * t⁻¹ := by rw [h1]
        _ = (t * z * t⁻¹) * s := by group
    rcases hZ _ htz hcomm with h1 | h1
    · apply hz1
      calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
    · have htH : t ∈ Subgroup.centralizer ({z} : Set G) := by
        refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        rw [Set.mem_singleton_iff.1 hh]
        have : t * z = z * t := by
          calc t * z = (t * z * t⁻¹) * t := by group
            _ = z * t := by rw [h1]
        exact this.symm
      exact htT (hN t htH hconj hconj')

theorem normal_dichotomy {T Tp : Subgroup G} (hle : Tp ≤ T) (hcard : Nat.card T = 2 * Nat.card Tp)
    {u : G} (huT : u ∈ T) (huTp : u ∉ Tp) :
    (∀ t ∈ T, ∀ q ∈ Tp, t * q * t⁻¹ ∈ Tp) ∧ ∀ t ∈ T, t ∈ Tp ∨ u⁻¹ * t ∈ Tp := by
  classical
  set K : Subgroup T := Tp.subgroupOf T with hK
  have hKc : Nat.card K = Nat.card Tp := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hidx : K.index = 2 := by
    have h := Subgroup.card_mul_index K
    have hpos : 0 < Nat.card Tp := Nat.card_pos
    rw [hKc, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h]; ring)
  have hKn : K.Normal := Subgroup.normal_of_index_eq_two hidx
  have hmem : ∀ t : T, t ∈ K ↔ (t : G) ∈ Tp := fun t => Subgroup.mem_subgroupOf
  refine ⟨fun t ht q hq => ?_, fun t ht => ?_⟩
  · have := hKn.conj_mem ⟨q, hle hq⟩ ((hmem _).2 hq) ⟨t, ht⟩
    exact (hmem _).1 this
  · obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
    have hu : (⟨u, huT⟩ : T) ∉ K := fun h => huTp ((hmem _).1 h)
    by_cases h1 : t ∈ Tp
    · exact Or.inl h1
    · right
      have h1' : (⟨t, ht⟩ : T) ∉ K := fun h => h1 ((hmem _).1 h)
      have h2 : (⟨t, ht⟩ : T) * a ∈ K := by
        rcases ha ⟨t, ht⟩ with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h h1'
      have h3 : (⟨u, huT⟩ : T) * a ∈ K := by
        rcases ha ⟨u, huT⟩ with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hu
      have h4 : (⟨t, ht⟩ : T) * a * ((⟨u, huT⟩ : T) * a)⁻¹ ∈ K := K.mul_mem h2 (K.inv_mem h3)
      have h5 : (⟨t, ht⟩ : T) * (⟨u, huT⟩ : T)⁻¹ ∈ K := by
        simpa [mul_assoc] using h4
      have h6 := hKn.conj_mem _ h5 (⟨u, huT⟩ : T)⁻¹
      have h7 : (⟨u, huT⟩ : T)⁻¹ * ((⟨t, ht⟩ : T) * (⟨u, huT⟩ : T)⁻¹) * (⟨u, huT⟩ : T)⁻¹⁻¹ ∈ K :=
        h6
      have h8 : (⟨u, huT⟩ : T)⁻¹ * (⟨t, ht⟩ : T) ∈ K := by simpa [mul_assoc] using h7
      exact (hmem _).1 h8

theorem exists_conj_mem_of_simple [IsSimpleGroup G] {T Tp : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hle : Tp ≤ T) (hcard : Nat.card T = 2 * Nat.card Tp) {u : G} (huT : u ∈ T)
    (huTp : u ∉ Tp) (hu : u * u = 1) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∃ g : G, g⁻¹ * u * g ∈ Tp := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQn, hdich⟩ := normal_dichotomy hle hcard huT huTp
  have hidx : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    change ¬ 2 ∣ T.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Tp := by
    refine ⟨u, huT, fun t ht => ?_⟩
    rcases hdich t ht with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ T → g⁻¹ * u ^ (2 * k) * g ∈ Tp := by
    intro g k _
    have : u ^ (2 * k) = 1 := by rw [pow_mul, sq, hu, one_pow]
    rw [this]
    simp
  have hc : ∀ g : G, g⁻¹ * u * g ∈ T → CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 T (g⁻¹ * u * g) →
      g⁻¹ * u * g ∈ Tp ∨ u⁻¹ * (g⁻¹ * u * g) ∈ Tp := fun g hg _ => hdich _ hg
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hT.2.1 hidx hQn hcyc huT huTp
      hb hc with ⟨N, hN, hcycN, -, huN⟩ | ⟨g, hg, -, -⟩
  · exfalso
    have : N.Normal := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · subst h
      have := hcycN
      have hcycG : IsCyclic G :=
        isCyclic_of_surjective (QuotientGroup.quotientBot (G := G)).toMonoidHom
          (QuotientGroup.quotientBot (G := G)).surjective
      obtain ⟨a, b, hab⟩ := hnab
      obtain ⟨g, hg⟩ := hcycG.exists_generator
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
      exact hab ((Commute.zpow_zpow_self g m n).eq)
    · exact huN (h ▸ Subgroup.mem_top u)
  · exact ⟨g, hg⟩

end CFSG.Quasithin.H13.F431.G2Two
