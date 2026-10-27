module

public import CFSG.Quasithin.EmptyFaithful.S143UE
public import CFSG.Quasithin.EmptyFaithful.S143SD
public import CFSG.Quasithin.EmptyFaithful.S143SC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

@[expose] def Lemma14322InspectW2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl14319 T M A →
      Subgroup.centralizer (A : Set G) = A → Concl14321 T M →
        ∀ d : G, dOf T M = Subgroup.zpowers d → orderOf d = 4 →
          ∀ x ∈ yOfL22 T M, orderOf x = 3 →
            IsSylowTwoOf (T ⊓ Subgroup.centralizer ({wOfX d x} : Set G))
              (Subgroup.centralizer ({wOfX d x} : Set G)) →
            (∀ y : G, y * (d * d) * y⁻¹ ≠ wOfX d x) →
            (∃ s : G, s * wOfX d x * s⁻¹ = wOfX d x * (d * d)) →
            IsZ4Sq ↥(rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) →
            IsZ4StarSL23 ↥(oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) →
              ∃ L : Subgroup G, L ≤ Subgroup.centralizer ({wOfX d x} : Set G) ∧
                (d * d ∈ L ∨ wOfX d x * (d * d) ∈ L) ∧
                (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ * l₁ = 1 → l₁ ≠ 1 → l₂ * l₂ = 1 → l₂ ≠ 1 →
                  ∃ m ∈ L, m * l₁ * m⁻¹ = l₂) ∧
                T ⊓ Subgroup.centralizer ({wOfX d x} : Set G) ⊓ (rOf T M ⊔ qOf T) ≤
                  Subgroup.zpowers (wOfX d x) ⊔ L

section Deduce2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}
  (c : Counter T M g) (c21 : Concl14321 T M)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c c21 hD hd4 hxL hx3 in
theorem zfus_of_inspect2
    (hSyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({wOfX d x} : Set G))
      (Subgroup.centralizer ({wOfX d x} : Set G)))
    (hN1 : ∀ y : G, y * (d * d) * y⁻¹ ≠ wOfX d x)
    (hN2 : ∃ s : G, s * wOfX d x * s⁻¹ = wOfX d x * (d * d))
    {L : Subgroup G} (hLC : L ≤ Subgroup.centralizer ({wOfX d x} : Set G))
    (hLz : d * d ∈ L ∨ wOfX d x * (d * d) ∈ L)
    (hL1 : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ * l₁ = 1 → l₁ ≠ 1 → l₂ * l₂ = 1 → l₂ ≠ 1 →
      ∃ m ∈ L, m * l₁ * m⁻¹ = l₂)
    (hLT : T ⊓ Subgroup.centralizer ({wOfX d x} : Set G) ⊓ (rOf T M ⊔ qOf T) ≤
      Subgroup.zpowers (wOfX d x) ⊔ L) :
    ∀ u : G, (∃ s : G, u = s * (d * d) * s⁻¹) → u * wOfX d x = wOfX d x * u →
      ∃ k : G, k * wOfX d x = wOfX d x * k ∧ k * (d * d) * k⁻¹ = u := by
  have hzz : (d * d) * (d * d) = 1 := (dd_facts hd4).1
  have hz1 : d * d ≠ 1 := (dd_facts hd4).2
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hw2 : wOfX d x * wOfX d x = 1 := wOfX_sq c hD hd4 hxL hx3
  have hzw : (d * d) * wOfX d x = wOfX d x * (d * d) := by
    have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
    have hzX : d * d ∈ Xgen T M := (Xgen T M).mul_mem (le_Wgen (dOf_mem_delta c) hd)
      (le_Wgen (dOf_mem_delta c) hd)
    exact Xgen_comm c hD hd4 _ hzX _ (wOfX_mem_Xgen c hD hxL)
  have hcom : ∀ l ∈ L, wOfX d x * l = l * wOfX d x := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hLC hl) (wOfX d x) (Set.mem_singleton _)
  have hwz2 : (wOfX d x * (d * d)) * (wOfX d x * (d * d)) = 1 := by
    calc (wOfX d x * (d * d)) * (wOfX d x * (d * d))
        = wOfX d x * ((d * d) * wOfX d x) * (d * d) := by group
      _ = wOfX d x * (wOfX d x * (d * d)) * (d * d) := by rw [hzw]
      _ = (wOfX d x * wOfX d x) * ((d * d) * (d * d)) := by group
      _ = 1 := by rw [hw2, hzz, one_mul]
  have hwz1 : wOfX d x * (d * d) ≠ 1 := by
    intro h
    apply hN1 1
    have : wOfX d x = (d * d)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    have : (d * d)⁻¹ = d * d := inv_eq_of_mul_eq_one_right hzz
    rw [this]; group
  intro u ⟨s₁, hs₁⟩ hu
  have hu2 : u * u = 1 := by
    rw [hs₁]
    calc s₁ * (d * d) * s₁⁻¹ * (s₁ * (d * d) * s₁⁻¹) = s₁ * ((d * d) * (d * d)) * s₁⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hu1 : u ≠ 1 := by
    intro h
    apply hz1
    calc d * d = s₁⁻¹ * u * s₁ := by rw [hs₁]; group
      _ = 1 := by rw [h]; group
  have huH : u ∈ Subgroup.centralizer ({wOfX d x} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh; subst hh; exact hu.symm
  obtain ⟨s, hsH, hsS⟩ := exists_conj_into_sylow hSyl huH hu2
  have hsw : wOfX d x * s = s * wOfX d x :=
    Subgroup.mem_centralizer_iff.mp hsH (wOfX d x) (Set.mem_singleton _)
  set u' := s⁻¹ * u * s with hu'def
  have hu'2 : u' * u' = 1 := by
    rw [hu'def]
    calc s⁻¹ * u * s * (s⁻¹ * u * s) = s⁻¹ * (u * u) * s := by group
      _ = 1 := by rw [hu2]; group
  have hu'1 : u' ≠ 1 := by
    intro h
    apply hu1
    calc u = s * u' * s⁻¹ := by rw [hu'def]; group
      _ = 1 := by rw [h]; group
  have hu'z : u' = (s⁻¹ * s₁) * (d * d) * (s⁻¹ * s₁)⁻¹ := by
    rw [hu'def, hs₁]; group
  have hu'ord : orderOf u' = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hu'2) hu'1
  have hu'RQ : u' ∈ rOf T M ⊔ qOf T := by
    by_contra hn
    exact c21.not_fused u' hsS.1 hn hu'ord (s⁻¹ * s₁) (d * d) hzZ hz1 hu'z.symm
  have hu'L : u' ∈ Subgroup.zpowers (wOfX d x) ⊔ L := hLT ⟨hsS, hu'RQ⟩
  have hLN : L ≤ Subgroup.normalizer ((Subgroup.zpowers (wOfX d x) : Subgroup G) : Set G) := by
    intro l hl
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute (wOfX d x) l from hcom l hl) j).eq
  obtain ⟨wj, hwj, l, hl, hu'eq⟩ := (Lin2.mem_sup_iff_of_le_normalizer hLN).1 hu'L
  have hF0 : u' ≠ wOfX d x := fun h => hN1 (s⁻¹ * s₁) (by rw [← hu'z, h])
  have hF1 : ∀ m ∈ L, u' ≠ m * (wOfX d x * (d * d)) * m⁻¹ := by
    intro m hm h
    obtain ⟨s₂, hs₂⟩ := hN2
    refine hN1 (s₂⁻¹ * m⁻¹ * (s⁻¹ * s₁)) ?_
    have e1 : wOfX d x * (d * d) = m⁻¹ * u' * m := by rw [h]; group
    have e2 : wOfX d x = s₂⁻¹ * (wOfX d x * (d * d)) * s₂ := by rw [← hs₂]; group
    calc s₂⁻¹ * m⁻¹ * (s⁻¹ * s₁) * (d * d) * (s₂⁻¹ * m⁻¹ * (s⁻¹ * s₁))⁻¹
        = s₂⁻¹ * m⁻¹ * ((s⁻¹ * s₁) * (d * d) * (s⁻¹ * s₁)⁻¹) * (s₂⁻¹ * m⁻¹)⁻¹ := by group
      _ = s₂⁻¹ * (m⁻¹ * u' * m) * s₂ := by rw [← hu'z]; group
      _ = s₂⁻¹ * (wOfX d x * (d * d)) * s₂ := by rw [← e1]
      _ = wOfX d x := e2.symm
  have hclass : ∀ l ∈ L, l * l = 1 → l ≠ 1 →
      (∃ m ∈ L, m * (d * d) * m⁻¹ = l) ∨ (∃ m ∈ L, m * (wOfX d x * (d * d)) * m⁻¹ = l) := by
    intro l hl hl2 hl1
    rcases hLz with hzL | hwzL
    · left
      exact hL1 _ hzL l hl hzz hz1 hl2 hl1
    · right
      exact hL1 _ hwzL l hl hwz2 hwz1 hl2 hl1
  have hgood : ∀ m ∈ L, m * (d * d) * m⁻¹ = u' →
      ∃ k : G, k * wOfX d x = wOfX d x * k ∧ k * (d * d) * k⁻¹ = u := by
    intro m hm hmu
    refine ⟨s * m, ?_, ?_⟩
    · calc s * m * wOfX d x = s * (m * wOfX d x) := by group
        _ = s * (wOfX d x * m) := by rw [← hcom m hm]
        _ = (s * wOfX d x) * m := by group
        _ = (wOfX d x * s) * m := by rw [hsw]
        _ = wOfX d x * (s * m) := by group
    · calc (s * m) * (d * d) * (s * m)⁻¹ = s * (m * (d * d) * m⁻¹) * s⁻¹ := by group
        _ = s * u' * s⁻¹ := by rw [hmu]
        _ = u := by rw [hu'def]; group
  have hmC : ∀ m ∈ L, m * wOfX d x = wOfX d x * m := fun m hm => (hcom m hm).symm
  rcases mem_zpowers_of_sq_eq_one hw2 hwj with h1 | h1
  ·
    rw [h1, one_mul] at hu'eq
    have hl2 : l * l = 1 := by rw [← hu'eq]; exact hu'2
    have hl1 : l ≠ 1 := by rw [← hu'eq]; exact hu'1
    rcases hclass l hl hl2 hl1 with ⟨m, hm, hmz⟩ | ⟨m, hm, hmz⟩
    · exact hgood m hm (by rw [hmz, hu'eq])
    · exact absurd (by rw [hmz]; exact hu'eq) (hF1 m hm)
  ·
    rw [h1] at hu'eq
    have hl2 : l * l = 1 := by
      have h3 : (wOfX d x * l) * (wOfX d x * l) = l * l := by
        calc (wOfX d x * l) * (wOfX d x * l) = wOfX d x * (l * wOfX d x) * l := by group
          _ = wOfX d x * (wOfX d x * l) * l := by rw [← hcom l hl]
          _ = (wOfX d x * wOfX d x) * (l * l) := by group
          _ = l * l := by rw [hw2, one_mul]
      rw [← h3, ← hu'eq]; exact hu'2
    by_cases hl1 : l = 1
    · exfalso
      rw [hl1, mul_one] at hu'eq
      exact hF0 hu'eq
    · rcases hclass l hl hl2 hl1 with ⟨m, hm, hmz⟩ | ⟨m, hm, hmz⟩
      ·
        exfalso
        refine hF1 m hm ?_
        calc u' = wOfX d x * l := hu'eq
          _ = wOfX d x * (m * (d * d) * m⁻¹) := by rw [hmz]
          _ = m * (wOfX d x * (d * d)) * m⁻¹ := by
              calc wOfX d x * (m * (d * d) * m⁻¹) = (wOfX d x * m) * (d * d) * m⁻¹ := by group
                _ = (m * wOfX d x) * (d * d) * m⁻¹ := by rw [← hcom m hm]
                _ = m * (wOfX d x * (d * d)) * m⁻¹ := by group
      ·
        refine hgood m hm ?_
        calc m * (d * d) * m⁻¹ = (wOfX d x * wOfX d x) * (m * (d * d) * m⁻¹) := by
              rw [hw2, one_mul]
          _ = wOfX d x * (wOfX d x * (m * (d * d) * m⁻¹)) := by rw [mul_assoc]
          _ = wOfX d x * (m * (wOfX d x * (d * d)) * m⁻¹) := by
              congr 1
              calc wOfX d x * (m * (d * d) * m⁻¹) = (wOfX d x * m) * (d * d) * m⁻¹ := by group
                _ = (m * wOfX d x) * (d * d) * m⁻¹ := by rw [← hcom m hm]
                _ = m * (wOfX d x * (d * d)) * m⁻¹ := by group
          _ = wOfX d x * l := by rw [hmz]
          _ = u' := hu'eq.symm

include c c21 hD hd4 hxL hx3 in
theorem lemma14322TailFusion_of_inspect2'
    (hF : Lemma14322InspectW2) {A' : Subgroup G} {t' : G}
    (c18 : Concl14318 T M g A' t') (c19 : Concl14319 T M A')
    (hΓ : Subgroup.centralizer (A' : Set G) = A') :
    ∀ y : G, y * wOfX d x * y⁻¹ ∈ mcOf T → ∃ h ∈ mcOf T, y * wOfX d x * y⁻¹ = h * wOfX d x * h⁻¹ := by
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hz1 : d * d ≠ 1 := (dd_facts hd4).2
  have hSyl := isSylowTwoOf_Tw c c18 hD hd4 hxL hx3 hΓ
  have hN1 := wOfX_not_conj_sq c hD hd4 hxL hx3
  have hN2 := exists_conj_wOfX_eq_mul_sq c c18 hD hd4 hxL hx3 hΓ
  obtain ⟨L, hLC, hLz, hL1, hLT⟩ := hF G T M g A' t' c c18 c19 hΓ c21 d hD hd4 x hxL hx3 hSyl hN1 hN2
    (isZ4Sq_centralizer_R c c18 c19 hD hd4 hxL hx3 hΓ)
    (isZ4StarSL23_centralizer_oTwoUpper c c18 hD hd4 hxL hx3 hΓ)
  have hZF := zfus_of_inspect2 c c21 hD hd4 hxL hx3 hSyl hN1 hN2 hLC hLz hL1 hLT
  intro y hy
  have hy' : (d * d) * (y * wOfX d x * y⁻¹) = (y * wOfX d x * y⁻¹) * (d * d) :=
    Subgroup.mem_centralizer_iff.mp hy (d * d) hzZ
  obtain ⟨h, hh, hyh⟩ := fusion_of_zfus hZF hy'
  exact ⟨h, c.mem_mcOf_of_comm hzZ hz1 hh, hyh⟩

end Deduce2

theorem lemma14322TailFusion_of_inspect2
    (hF : Lemma14322InspectW2) : Lemma14322TailFusion := by
  intro G _ _ T M g A t c c18 c19 hΓ c21 d hD hd4 x hxL hx3 y hy
  exact lemma14322TailFusion_of_inspect2' c c21 hD hd4 hxL hx3 hF c18 c19 hΓ y hy

end S143

end CFSG.Quasithin
