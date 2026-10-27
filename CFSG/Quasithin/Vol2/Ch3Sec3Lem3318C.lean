module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316F

public section

namespace CFSG.Quasithin.H13.L3318

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)

section Aut

variable {K : Type} [Field K] [Finite K]

theorem map_unitriangular_eq {n : ℕ} (θ : MulAut (SpecialLinearGroup (Fin n) K))
    (hU : ∀ u ∈ unitriangular n K, θ u ∈ unitriangular n K) :
    (unitriangular n K).map θ.toMonoidHom = unitriangular n K :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨u, hu, rfl⟩; exact hU u hu)
    (by rw [Subgroup.card_map_of_injective θ.injective])

omit [Finite K] in
theorem overgroups_three {A : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hA : upperTriangular 3 K ≤ A) :
    A = ⊤ ∨ A = flagStabilizer 3 K {1} ∨ A = flagStabilizer 3 K {2} ∨
      A = flagStabilizer 3 K {1, 2} := by
  obtain ⟨hAeq, -⟩ := borel_overgroups A hA
  set I := borelOvergroupCuts A with hI
  have hIsub : ∀ i ∈ I, i = 1 ∨ i = 2 := by
    rintro i ⟨h1, h3, -⟩
    omega
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · right; right; right
    rw [hAeq]
    congr 1
    ext i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨hIsub i, by rintro (rfl | rfl) <;> assumption⟩
  · right; left
    rw [hAeq]
    congr 1
    ext i
    simp only [Set.mem_singleton_iff]
    refine ⟨fun hi => (hIsub i hi).resolve_right (by rintro rfl; exact h2 hi), ?_⟩
    rintro rfl
    exact h1
  · right; right; left
    rw [hAeq]
    congr 1
    ext i
    simp only [Set.mem_singleton_iff]
    refine ⟨fun hi => (hIsub i hi).resolve_left (by rintro rfl; exact h1 hi), ?_⟩
    rintro rfl
    exact h2
  · left
    rw [hAeq]
    have : I = ∅ := by
      ext i
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hi
      rcases hIsub i hi with rfl | rfl
      · exact h1 hi
      · exact h2 hi
    rw [this, flagStabilizer_empty]

abbrev tv3 (i j : Fin 3) (hij : i ≠ j) : SpecialLinearGroup (Fin 3) K :=
  SpecialLinearGroup.transvection hij (1 : K)

omit [Finite K] in
theorem tv3_not_mem {i j : Fin 3} (hij : i ≠ j) {c : ℕ} (hjc : (j : ℕ) < c) (hci : c ≤ (i : ℕ)) :
    tv3 (K := K) i j hij ∉ stabilizer (flagSpace 3 K c) := by
  intro hmem
  have h := stabilizer_entries hmem (k := i) (l := j) hjc hci
  rw [SpecialLinearGroup.transvection_coe] at h
  simp [Matrix.one_apply_ne hij] at h

omit [Finite K] in
theorem tv3_mem {i j : Fin 3} (hij : i ≠ j) {c : ℕ} (hc : ¬ ((j : ℕ) < c ∧ c ≤ (i : ℕ))) :
    tv3 (K := K) i j hij ∈ flagStabilizer 3 K {c} := by
  refine mem_flagStabilizer_of_entries fun k l c' hc' hl hk => ?_
  rw [Set.mem_singleton_iff] at hc'
  subst hc'
  rw [SpecialLinearGroup.transvection_coe]
  have hkl : k ≠ l := fun e => by subst e; omega
  have hne : ¬ (i = k ∧ j = l) := by
    rintro ⟨rfl, rfl⟩
    exact hc ⟨hl, hk⟩
  simp [Matrix.one_apply_ne hkl, hne]

omit [Finite K] in
theorem tv3_not_mem_upper {i j : Fin 3} (hij : i ≠ j) (hji : j < i) :
    tv3 (K := K) i j hij ∉ upperTriangular 3 K := by
  intro h
  have := h i j hji
  rw [SpecialLinearGroup.transvection_coe] at this
  simp [Matrix.one_apply_ne hij] at this

omit [Finite K] in
theorem flagStabilizer_one_two_le : flagStabilizer 3 K {1, 2} ≤ upperTriangular 3 K := by
  intro g hg i j hji
  rw [mem_flagStabilizer] at hg
  have hi := i.isLt
  have hj := Fin.lt_def.mp hji
  rcases (by omega : (j : ℕ) < 1 ∨ (1 ≤ (j : ℕ) ∧ (j : ℕ) < 2)) with h | h
  · exact stabilizer_entries (hg 1 (by simp)) h (by omega)
  · exact stabilizer_entries (hg 2 (by simp)) (by omega) (by omega)

theorem eq_one_of_mulAut_odd (hK : Nat.card K = 2) (θ : MulAut (SpecialLinearGroup (Fin 3) K))
    (hU : ∀ u ∈ unitriangular 3 K, θ u ∈ unitriangular 3 K) {m : ℕ} (hm : Odd m)
    (hθ : θ ^ m = 1) : θ = 1 := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl
    (by rw [hK]; norm_num)
  have hB : upperTriangular 3 K = unitriangular 3 K :=
    le_antisymm (upperTriangular_le_unitriangular hK) (unitriangular_le_upperTriangular 3 K)
  have hθB : (upperTriangular 3 K).map θ.toMonoidHom = upperTriangular 3 K := by
    rw [hB]
    exact map_unitriangular_eq θ hU
  set Q₁ := flagStabilizer 3 K {1} with hQ₁
  set Q₂ := flagStabilizer 3 K {2} with hQ₂
  have h01 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (2 : Fin 3) ≠ 1 := by decide
  have hBQ₁ : upperTriangular 3 K ≤ Q₁ := upperTriangular_le_flagStabilizer _
  have hBQ₂ : upperTriangular 3 K ≤ Q₂ := upperTriangular_le_flagStabilizer _
  have ha₁ : tv3 (K := K) 1 0 h01 ∉ Q₁ := by
    rw [hQ₁, flagStabilizer_singleton]
    exact tv3_not_mem h01 (by decide) (by decide)
  have ha₂ : tv3 (K := K) 1 0 h01 ∈ Q₂ := tv3_mem h01 (by decide)
  have hb₁ : tv3 (K := K) 2 1 h12 ∈ Q₁ := tv3_mem h12 (by decide)
  have hb₂ : tv3 (K := K) 2 1 h12 ∉ Q₂ := by
    rw [hQ₂, flagStabilizer_singleton]
    exact tv3_not_mem h12 (by decide) (by decide)
  have hinj := Subgroup.map_injective (f := θ.toMonoidHom) θ.injective
  have himage : ∀ P : Subgroup (SpecialLinearGroup (Fin 3) K), upperTriangular 3 K ≤ P →
      (∃ x ∈ P, x ∉ upperTriangular 3 K) → P ≠ ⊤ →
      P.map θ.toMonoidHom = Q₁ ∨ P.map θ.toMonoidHom = Q₂ := by
    intro P hBP hPB hPT
    have hle : upperTriangular 3 K ≤ P.map θ.toMonoidHom := by
      rw [← hθB]
      exact Subgroup.map_mono hBP
    rcases overgroups_three hle with h | h | h | h
    · exfalso
      apply hPT
      apply hinj
      rw [h, Subgroup.map_top_of_surjective _ θ.surjective]
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      obtain ⟨x, hxP, hxB⟩ := hPB
      have h1 : P.map θ.toMonoidHom ≤ (upperTriangular 3 K).map θ.toMonoidHom := by
        rw [hθB, h]
        exact flagStabilizer_one_two_le
      exact hxB ((Subgroup.map_le_map_iff_of_injective θ.injective).mp h1 hxP)
  have hQ₁T : Q₁ ≠ ⊤ := fun h => ha₁ (h ▸ Subgroup.mem_top _)
  have hQ₂T : Q₂ ≠ ⊤ := fun h => hb₂ (h ▸ Subgroup.mem_top _)
  have hQ₁₂ : Q₁ ≠ Q₂ := fun h => ha₁ (h ▸ ha₂)
  have hI₁ := himage Q₁ hBQ₁ ⟨_, hb₁, tv3_not_mem_upper h12 (by decide)⟩ hQ₁T
  have hI₂ := himage Q₂ hBQ₂ ⟨_, ha₂, tv3_not_mem_upper h01 (by decide)⟩ hQ₂T
  have hfix : Q₁.map θ.toMonoidHom = Q₁ := by
    rcases hI₁ with h | h
    · exact h
    · exfalso
      have h2 : Q₂.map θ.toMonoidHom = Q₁ := by
        rcases hI₂ with h' | h'
        · exact h'
        · exact absurd (hinj (h.trans h'.symm)) hQ₁₂
      have hmul : ∀ (θ₁ θ₂ : MulAut (SpecialLinearGroup (Fin 3) K))
          (P : Subgroup (SpecialLinearGroup (Fin 3) K)),
          P.map (θ₁ * θ₂).toMonoidHom = (P.map θ₂.toMonoidHom).map θ₁.toMonoidHom := by
        intro θ₁ θ₂ P
        rw [Subgroup.map_map]
        rfl
      have hsq : Q₁.map (θ * θ).toMonoidHom = Q₁ := by
        rw [hmul, h, h2]
      have hpow : ∀ r : ℕ, Q₁.map ((θ * θ) ^ r).toMonoidHom = Q₁ := by
        intro r
        induction r with
        | zero =>
          rw [pow_zero]
          ext x
          exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
        | succ r ih =>
          rw [pow_succ, hmul, hsq, ih]
      obtain ⟨r, rfl⟩ := hm
      have hθr : θ = (θ * θ) ^ (r + 1) := by
        rw [← pow_two, ← pow_mul, show 2 * (r + 1) = (2 * r + 1) + 1 by ring, pow_succ, hθ,
          one_mul]
      have := hpow (r + 1)
      rw [← hθr, h] at this
      exact hQ₁₂ this.symm
  have hQ : ∀ g ∈ stabilizer (flagSpace 3 K 1), θ g ∈ stabilizer (flagSpace 3 K 1) := by
    intro g hg
    rw [← flagStabilizer_singleton] at hg ⊢
    have : θ g ∈ Q₁.map θ.toMonoidHom := ⟨g, hg, rfl⟩
    rwa [hfix] at this
  obtain ⟨u, huU, hθu⟩ := Ln2.eq_conj_of_mulAut hK le_rfl θ hU hQ
  have hθc : θ = MulAut.conj u := MulEquiv.ext fun g => by rw [hθu]; rfl
  obtain ⟨a, ha⟩ := isPGroup_unitriangular_charTwo (K := K) (n := 3) (by norm_num) ⟨u, huU⟩
  have hua : u ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hθa : θ ^ 2 ^ a = 1 := by
    rw [hθc, ← map_pow, hua, map_one]
  have hcop : Nat.Coprime (2 ^ a) m := by
    obtain ⟨r, rfl⟩ := hm
    exact Nat.Coprime.pow_left _ (by
      rw [Nat.coprime_two_left]
      exact ⟨r, rfl⟩)
  have h1 := orderOf_dvd_of_pow_eq_one hθa
  have h2 := orderOf_dvd_of_pow_eq_one hθ
  have h3 : orderOf θ = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp h3

end Aut

section Levi

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

theorem mem_perfectCore_of_mem_liftCore {n : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) K}
    (hαs : Function.Surjective α) {P : Subgroup (SpecialLinearGroup (Fin n) K)} {y : G}
    (hy : y ∈ liftCore α P) : α ⟨y, liftCore_le α P hy⟩ ∈ perfectCore P := by
  rw [liftCore_eq] at hy
  obtain ⟨y', hy', hy'e⟩ := hy
  have : y' = ⟨y, liftCore_le α P (by rw [liftCore_eq]; exact ⟨y', hy', hy'e⟩)⟩ :=
    Subtype.ext hy'e
  rw [← map_perfectCore_comap hαs P, ← this]
  exact ⟨y', hy', rfl⟩

theorem exists_mem_liftCore {n : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) K}
    (hαs : Function.Surjective α) {P : Subgroup (SpecialLinearGroup (Fin n) K)}
    {p : SpecialLinearGroup (Fin n) K} (hp : p ∈ perfectCore P) :
    ∃ (y : G) (hy : y ∈ liftCore α P), α ⟨y, liftCore_le α P hy⟩ = p := by
  rw [← map_perfectCore_comap hαs P] at hp
  obtain ⟨y', hy', rfl⟩ := hp
  have hmem : (y' : G) ∈ liftCore α P := by
    rw [liftCore_eq]
    exact ⟨y', hy', rfl⟩
  exact ⟨y', hmem, rfl⟩

theorem exists_levi (hK : Nat.card K = 2) {n : ℕ} (hn5 : n ≤ 5)
    {α : ↥L →* SpecialLinearGroup (Fin n) K} (hαs : Function.Surjective α)
    (hαk : IsPGroup 2 ↥α.ker) {I : Set ℕ} {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) :
    ∃ ψ : ↥(liftCore α (flagStabilizer n K I)) →* SpecialLinearGroup (Fin m) K,
      Function.Surjective ψ ∧ IsPGroup 2 ↥ψ.ker ∧
      ∀ y : ↥(liftCore α (flagStabilizer n K I)),
        ((ψ y : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
          blkAt a m h ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl
    (by rw [hK]; norm_num)
  set P := flagStabilizer n K I with hP
  set Y := liftCore α P with hY
  let χ : ↥Y →* ↥(perfectCore P) :=
    (α.comp (Subgroup.inclusion (liftCore_le α P))).codRestrict (perfectCore P)
      fun y => mem_perfectCore_of_mem_liftCore hαs y.2
  have hχ : ∀ y : ↥Y, ((χ y : ↥(perfectCore P)) : SpecialLinearGroup (Fin n) K) =
      α ⟨y, liftCore_le α P y.2⟩ := fun y => rfl
  have hχs : Function.Surjective χ := by
    rintro ⟨p, hp⟩
    obtain ⟨y, hy, hye⟩ := exists_mem_liftCore hαs hp
    exact ⟨⟨y, hy⟩, Subtype.ext hye⟩
  set β := bigBlockHom (K := K) I a m h ha hb with hβ
  have hβk : IsPGroup 2 ↥β.ker :=
    isPGroup_ker_of_unitriangular (by omega) β fun x hx =>
      unitriangular_of_bigBlockHom hK hn5 h hm3 ha hb hno x hx
  refine ⟨β.comp χ, (bigBlockHom_surjective hK h hm3 ha hb hno).comp hχs, ?_, fun y => ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ := hβk ⟨χ y, hy⟩
    have h1 : χ (y ^ 2 ^ c) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hc
    have h2 : α ⟨((y ^ 2 ^ c : ↥Y) : G), liftCore_le α P (y ^ 2 ^ c).2⟩ = 1 := by
      rw [← hχ, h1]
      rfl
    obtain ⟨d, hd⟩ := hαk ⟨_, h2⟩
    refine ⟨c + d, Subtype.ext (Subtype.ext ?_)⟩
    have h3 := congrArg (fun z => ((z : ↥L) : G)) (congrArg Subtype.val hd)
    simp only [SubmonoidClass.mk_pow, Subgroup.coe_pow, OneMemClass.coe_one] at h3
    simp only [SubmonoidClass.mk_pow, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul]
    exact h3
  · rw [MonoidHom.comp_apply, bigBlockHom_coe, hχ]

end Levi

end CFSG.Quasithin.H13.L3318
