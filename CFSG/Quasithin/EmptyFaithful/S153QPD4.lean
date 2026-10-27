module

public import CFSG.Quasithin.EmptyFaithful.S153QPD3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic

public section

namespace CFSG.Quasithin.QP

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.L52 CFSG.Quasithin

section Embedding

variable {n : ℕ} {F : Type} [Field F]

@[expose] def embAt (a m : ℕ) (_h : a + m ≤ n) (B : Matrix (Fin m) (Fin m) F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j =>
    if hij : a ≤ (i : ℕ) ∧ (i : ℕ) < a + m ∧ a ≤ (j : ℕ) ∧ (j : ℕ) < a + m then
      B ⟨(i : ℕ) - a, by omega⟩ ⟨(j : ℕ) - a, by omega⟩
    else if i = j then 1 else 0

theorem blkAt_embAt (a m : ℕ) (h : a + m ≤ n) (B : Matrix (Fin m) (Fin m) F) :
    blkAt a m h (embAt a m h B) = B := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have e : ∀ k : Fin m, (⟨a + (k : ℕ) - a, by omega⟩ : Fin m) = k := fun k => Fin.ext (by simp)
  have hc : a ≤ a + (i : ℕ) ∧ a + (i : ℕ) < a + m ∧ a ≤ a + (j : ℕ) ∧ a + (j : ℕ) < a + m := by
    omega
  rw [blkAt_apply]
  simp only [embAt, Matrix.of_apply, hc]
  exact congrArg₂ (fun x y => B x y) (e i) (e j)

theorem exists_emb (a m : ℕ) (h : a + m ≤ n) {u' : SpecialLinearGroup (Fin m) F}
    (hu' : u' ∈ unitriangular m F) :
    ∃ u : SpecialLinearGroup (Fin n) F, u ∈ unitriangular n F ∧
      blkAt a m h (u : Matrix (Fin n) (Fin n) F) = (u' : Matrix (Fin m) (Fin m) F) := by
  obtain ⟨hlow, hdiag⟩ := hu'
  have hlow' : ∀ i j : Fin n, j < i → embAt a m h (u' : Matrix (Fin m) (Fin m) F) i j = 0 := by
    intro i j hji
    have hji' : (j : ℕ) < (i : ℕ) := hji
    by_cases hc : a ≤ (i : ℕ) ∧ (i : ℕ) < a + m ∧ a ≤ (j : ℕ) ∧ (j : ℕ) < a + m
    · simp only [embAt, Matrix.of_apply, hc]
      exact hlow _ _ (by show (j : ℕ) - a < (i : ℕ) - a; omega)
    · simp only [embAt, Matrix.of_apply, hc, ↓reduceDIte]
      simp [hji.ne']
  have hdiag' : ∀ i : Fin n, embAt a m h (u' : Matrix (Fin m) (Fin m) F) i i = 1 := by
    intro i
    by_cases hc : a ≤ (i : ℕ) ∧ (i : ℕ) < a + m ∧ a ≤ (i : ℕ) ∧ (i : ℕ) < a + m
    · simp only [embAt, Matrix.of_apply, hc]
      exact hdiag _
    · simp only [embAt, Matrix.of_apply, hc, ↓reduceDIte]
      simp
  have hdet : (embAt a m h (u' : Matrix (Fin m) (Fin m) F)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => hlow' i j hji)]
    simp [hdiag']
  exact ⟨⟨embAt a m h (u' : Matrix (Fin m) (Fin m) F), hdet⟩, ⟨hlow', hdiag'⟩,
    blkAt_embAt a m h _⟩

end Embedding

section Five

variable {F : Type} [Field F] [Finite F]

theorem perfectCore_cover {G : Type*} [Group G] [Finite G] (X : Subgroup G) {N : Type*} [Group N]
    [Finite N] [Group.IsPerfect N] (θ : ↥X →* N) (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) :
    Function.Surjective (θ.comp (Subgroup.inclusion (perfectCore_le X))) ∧
      IsPGroup 2 (θ.comp (Subgroup.inclusion (perfectCore_le X))).ker := by
  have hmapP : (perfectCore (⊤ : Subgroup ↥X)).map θ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective θ hθ]
    exact perfectCore_eq_self_of_perfect (by
      have := Group.isPerfect_def.1 (inferInstance : Group.IsPerfect N)
      rwa [commutator_def] at this)
  have hmapX : (perfectCore (⊤ : Subgroup ↥X)).map X.subtype = perfectCore X := by
    rw [map_perfectCore, Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨fun m => ?_, fun z => ?_⟩
  · have hm : m ∈ (perfectCore (⊤ : Subgroup ↥X)).map θ := by rw [hmapP]; trivial
    obtain ⟨p', hp', rfl⟩ := hm
    have hp'P : (p' : G) ∈ perfectCore X := by rw [← hmapX]; exact ⟨p', hp', rfl⟩
    exact ⟨⟨p', hp'P⟩, rfl⟩
  · have hz : Subgroup.inclusion (perfectCore_le X) (z : ↥(perfectCore X)) ∈ θ.ker := z.2
    obtain ⟨k, hk'⟩ := hk ⟨_, hz⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val (congrArg Subtype.val hk')
    simpa using h1

theorem false_of_block_four (hF : Nat.card F = 2) {I : Set ℕ} {a : ℕ} (h : a + 4 ≤ 5)
    (ha : a = 0 ∨ a ∈ I) (hb : a + 4 = 5 ∨ a + 4 ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + 4))
    {X : Subgroup (SpecialLinearGroup (Fin 5) F)} (hXQ : X ≤ flagStabilizer 5 F I)
    (hN : unitriangular 5 F ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin 5) F)))
    {N : Type} [Group N] [Finite N] [IsSimpleGroup N] (hN60 : Nat.card N = 60)
    (θ : ↥X →* N) (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperfN : Group.IsPerfect N := isPerfect_of_simple_card_sixty hN60
  have hUp : IsPGroup 2 (unitriangular 5 F) :=
    IsPGroup.of_card (n := 10) (by rw [card_unitriangular, hF])
  set P := perfectCore X with hP
  have hPX : P ≤ X := perfectCore_le X
  have hPperf : ⁅P, P⁆ = P := perfectCore_perfect X
  set Q := flagStabilizer 5 F I with hQ
  have hPQ' : P ≤ Q := hPX.trans hXQ
  have hPQ : P ≤ perfectCore Q := le_perfectCore_of_perfect hPQ' hPperf
  have hL : BlockLeft Q a 4 := blockLeft_of_cut 4 ha
  have hR : BlockRight Q a 4 := blockRight_of_cut hb
  let ι : ↥P →* SpecialLinearGroup (Fin 4) F :=
    (blkSLTwo hF Q a 4 h hL hR).comp (Subgroup.inclusion hPQ')
  have hι_coe : ∀ z : ↥P, ((ι z : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blkAt a 4 h ((z : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := fun z => rfl
  have hι : IsPGroup 2 ι.ker := by
    intro z
    have hz : ι (z : ↥P) = 1 := z.2
    have hzc : ((z : ↥P) : SpecialLinearGroup (Fin 5) F) ∈ perfectCore Q := hPQ (z : ↥P).2
    have h1 : bigBlockHom I a 4 h ha hb ⟨_, hzc⟩ = 1 := by
      apply Subtype.ext
      rw [bigBlockHom_coe]
      have := congrArg Subtype.val hz
      rw [hι_coe] at this
      rw [this]
    have hu := unitriangular_of_bigBlockHom hF (le_refl 5) h (by norm_num) ha hb hno ⟨_, hzc⟩ h1
    obtain ⟨k, hk'⟩ := hUp ⟨_, hu⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h2 := congrArg Subtype.val hk'
    simpa using h2
  obtain ⟨hθP, hkP⟩ := perfectCore_cover X θ hθ hk
  have hconj : ∀ u' ∈ unitriangular 4 F, ∀ h' ∈ ι.range, u' * h' * u'⁻¹ ∈ ι.range := by
    intro u' hu' h' hh'
    obtain ⟨p, rfl⟩ := hh'
    obtain ⟨u, huU, hublk⟩ := exists_emb a 4 h hu'
    have huQ : u ∈ Q := upperTriangular_le_flagStabilizer I (unitriangular_le_upperTriangular 5 F huU)
    have hunorm : u ∈ Subgroup.normalizer (P : Set (SpecialLinearGroup (Fin 5) F)) :=
      normalizer_le_normalizer_perfectCore X (hN huU)
    have hupu : u * (p : SpecialLinearGroup (Fin 5) F) * u⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hunorm p).1 p.2
    refine ⟨⟨_, hupu⟩, ?_⟩
    have hb1 : blkSLTwo hF Q a 4 h hL hR ⟨u, huQ⟩ = u' := Subtype.ext hublk
    have hb2 : ι ⟨u * (p : SpecialLinearGroup (Fin 5) F) * u⁻¹, hupu⟩ =
        blkSLTwo hF Q a 4 h hL hR (⟨u, huQ⟩ * ⟨(p : SpecialLinearGroup (Fin 5) F), hPQ' p.2⟩ *
          ⟨u, huQ⟩⁻¹) := rfl
    rw [hb2, map_mul, map_mul, map_inv, hb1]
    rfl
  have hNU : unitriangular 4 F ≤ Subgroup.normalizer (ι.range : Set (SpecialLinearGroup (Fin 4) F)) := by
    intro u' hu'
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    refine ⟨fun hh => hconj u' hu' h' hh, fun hh => ?_⟩
    have h3 := hconj u'⁻¹ (inv_mem hu') _ hh
    have e : u'⁻¹ * (u' * h' * u'⁻¹) * u'⁻¹⁻¹ = h' := by group
    rwa [e] at h3
  exact false_of_normalizes_sl4 hF ι hι hNU hN60 _ hθP hkP

theorem false_of_unitriangular_normalizes_sl5 (hF : Nat.card F = 2)
    {X : Subgroup (SpecialLinearGroup (Fin 5) F)}
    (hN : unitriangular 5 F ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin 5) F)))
    {N : Type} [Group N] [Finite N] [IsSimpleGroup N] (hN60 : Nat.card N = 60)
    (θ : ↥X →* N) (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := unitriangular 5 F with hU
  have hUp : IsPGroup 2 U := IsPGroup.of_card (n := 10) (by rw [hU, card_unitriangular, hF])
  set A := X ⊔ U with hA
  have : Group.IsPerfect (SpecialLinearGroup (Fin 5) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl (by norm_num))
  by_cases hAtop : A = ⊤
  · have hXtop : X = ⊤ := eq_top_of_sup_isPGroup_of_isPerfect hUp hN hAtop
    have hφ : Function.Surjective X.subtype := fun g => ⟨⟨g, hXtop ▸ Subgroup.mem_top g⟩, rfl⟩
    obtain ⟨b, hb⟩ := card_dvd_two_pow_mul_of_surjective X.subtype hφ θ hθ hk hN60
    exact not_seven_dvd_two_pow_mul_sixty b ((seven_dvd_card_sl_five hF).trans hb)
  · obtain ⟨i, hi1, hi5, hAi⟩ := exists_le_stabilizer_of_ne_top (le_sup_right : U ≤ A) hAtop
    obtain ⟨a, ha5⟩ := exists_orderOf_five hN60 θ hθ
    have hga5 : ((a : ↥X) : SpecialLinearGroup (Fin 5) F) ^ 5 = 1 := by
      have h5' : a ^ 5 = 1 := by
        have := pow_orderOf_eq_one a
        rwa [ha5] at this
      rw [← Subgroup.coe_pow, h5', Subgroup.coe_one]
    have hga1 : ((a : ↥X) : SpecialLinearGroup (Fin 5) F) ≠ 1 := by
      intro h1
      have : a = 1 := Subtype.ext h1
      rw [this, orderOf_one] at ha5
      omega
    have hmem : ((a : ↥X) : SpecialLinearGroup (Fin 5) F) ∈ stabilizer (flagSpace 5 F i) :=
      hAi (Subgroup.mem_sup_left a.2)
    have hi : i = 1 ∨ i = 4 := by
      by_contra hcon
      have h23 : 2 ≤ i ∧ i ≤ 3 := by omega
      refine false_of_stable_five hF (g := (((a : ↥X) : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))
        ?_ ?_ (W := flagSpace 5 F i) (fun w hw => mulVec_mem_of_mem_stabilizer hmem hw) ?_ ?_
      · rw [← Matrix.SpecialLinearGroup.coe_pow, hga5, Matrix.SpecialLinearGroup.coe_one]
      · exact fun h => hga1 (Subtype.ext h)
      · rw [finrank_flagSpace hi5.le]; exact h23.1
      · rw [finrank_flagSpace hi5.le]; exact h23.2
    have hXQ : ∀ j : ℕ, X ≤ stabilizer (flagSpace 5 F j) → X ≤ flagStabilizer 5 F {j} := by
      intro j hj g hg
      rw [mem_flagStabilizer]
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      subst hc
      exact hj hg
    have hXi : X ≤ stabilizer (flagSpace 5 F i) := (le_sup_left : X ≤ A).trans hAi
    rcases hi with rfl | rfl
    · exact false_of_block_four hF (I := {1}) (a := 1) (by norm_num) (Or.inr rfl) (Or.inl rfl)
        (by intro c hc; rw [Set.mem_singleton_iff] at hc; omega) (hXQ 1 hXi) hN hN60 θ hθ hk
    · exact false_of_block_four hF (I := {4}) (a := 0) (by norm_num) (Or.inl rfl) (Or.inr rfl)
        (by intro c hc; rw [Set.mem_singleton_iff] at hc; omega) (hXQ 4 hXi) hN hN60 θ hθ hk

end Five

end CFSG.Quasithin.QP
