module

public import CFSG.Quasithin.Vol2.Ch11SecDGroup
public import CFSG.Quasithin.Vol2.Ch11SecDFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem lOf_le_normalizer (L U : Subgroup G) : LOf L U ≤ Subgroup.normalizer (U : Set G) :=
  (perfectCore_le _).trans inf_le_right

theorem kOf_le_normalizer {L V₁ V₀ : Subgroup G}
    (h : LOf L V₁ ≤ Subgroup.normalizer (V₀ : Set G)) :
    KOf L V₁ V₀ ≤ Subgroup.normalizer (V₀ : Set G) :=
  conjClosure_le fun _ hg _ hx => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (h hx))
    (Subgroup.inv_mem _ hg)

theorem normalizer_le_normalizer_kOf (L V₁ V₀ : Subgroup G) :
    Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (KOf L V₁ V₀ : Set G) :=
  le_normalizer_conjClosure _ _

theorem mem_normalizer_lOf {L U : Subgroup G} {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) :
    x ∈ Subgroup.normalizer (LOf L U : Set G) :=
  normalizer_le_normalizer_perfectCore _ (mem_normalizer_inf hxL (Subgroup.le_normalizer hxU))

variable [Finite G]

theorem kOf_eq_of_cComp {L V₁ K₁ : Subgroup G} (hLK : LOf L V₁ ≤ K₁)
    (hK₁ : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hN : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hL₁ : LOf L V₁ ≠ ⊥) : KOf L V₁ V₁ = K₁ := by
  have hK₁G : K₁ ≤ Subgroup.normalizer (V₁ : Set G) := A3.subnormal_le hK₁.2.2.1
  refine le_antisymm
    (conjClosure_le fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hN hg) x).mp (hLK hx)) ?_
  have hK'le : conjClosure (LOf L V₁) K₁ ≤ K₁ :=
    conjClosure_le fun g hg x hx => K₁.mul_mem (K₁.mul_mem hg (hLK hx)) (K₁.inv_mem hg)
  have hsub : IsSubnormal (conjClosure (LOf L V₁) K₁) (Subgroup.normalizer (V₁ : Set G)) :=
    IsSubnormal.step hK'le ((Subgroup.normal_subgroupOf_iff_le_normalizer hK'le).mpr
      (le_normalizer_conjClosure _ _)) hK₁.2.2.1
  have hK'1 : conjClosure (LOf L V₁) K₁ ≠ ⊥ := fun h =>
    hL₁ (le_bot_iff.mp (h ▸ le_conjClosure _ _))
  have hK'eq : conjClosure (LOf L V₁) K₁ = K₁ := by
    by_contra hne
    exact hK₁.2.2.2 _ (lt_of_le_of_ne hK'le hne) hK'1 (conjClosure_perfect (perfectCore_perfect _))
      hsub
  rw [← hK'eq]
  exact conjClosure_mono le_rfl hK₁G

theorem kOf_eq_lOf_of_le {L V₁ : Subgroup G}
    (hK : quasithinIsCComponent (KOf L V₁ V₁) (Subgroup.normalizer (V₁ : Set G)))
    (hL₁ : LOf L V₁ ≠ ⊥) (hKM : KOf L V₁ V₁ ≤ Subgroup.normalizer (L : Set G)) :
    KOf L V₁ V₁ = LOf L V₁ := by
  have hL₁K : LOf L V₁ ≤ KOf L V₁ V₁ := le_conjClosure _ _
  have hKG : KOf L V₁ V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    kOf_le_normalizer (lOf_le_normalizer L V₁)
  have hnorm : KOf L V₁ V₁ ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    fun x hx => mem_normalizer_lOf (hKM hx) (hKG hx)
  have hsub : IsSubnormal (LOf L V₁) (Subgroup.normalizer (V₁ : Set G)) :=
    IsSubnormal.step hL₁K ((Subgroup.normal_subgroupOf_iff_le_normalizer hL₁K).mpr hnorm)
      hK.2.2.1
  by_contra hne
  exact hK.2.2.2 _ (lt_of_le_of_ne hL₁K (Ne.symm hne)) hL₁ (perfectCore_perfect _) hsub

variable {T L I : Subgroup G} {n : ℕ}

theorem lOf_ne_bot (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : LOf L V₁ ≠ ⊥ := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
  intro hbot
  have hsub : ∀ x : ↥(LOf L V₁) ⧸ CFSG.pCore 2 ↥(LOf L V₁), x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      have hy : y = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hbot _ y.2)
      rw [hy]
      rfl
  let A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have hA : A ≠ 1 := by
    intro hA1
    have h01 := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K =>
      (B : Matrix (Fin 2) (Fin 2) K) 0 1) hA1
    simp [A] at h01
  apply hA
  rw [← e.apply_symm_apply A, hsub (e.symm A), map_one]

theorem kOf_cComp (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    quasithinIsCComponent (KOf L V₁ V₁) (Subgroup.normalizer (V₁ : Set G)) := by
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  obtain ⟨X, hX⟩ := exists_isCartanX h
  obtain ⟨K₁, hLK, hK₁, hN, -, -⟩ :=
    h1112 G T L I n 1 V₁ V₁ V₂ X h (Or.inl rfl) hV₁ hV₁ hV₂ hX
  rw [kOf_eq_of_cComp hLK hK₁ hN (lOf_ne_bot h1110 h hV₁)]
  exact hK₁

theorem exists_z (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    ∃ z ∈ V₁, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) :=
  exists_mem_centralizer_ne_one h.fsu.sylow.1 ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h))
    (SecA.IsVi.le_normalizer hV₁) (SecA.IsVi.ne_bot h hV₁ le_rfl)

theorem kOf_le_centralizer_z (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {z : G} (hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G))
    (hz1 : z ≠ 1) : KOf L V₁ V₁ ≤ Subgroup.centralizer ({z} : Set G) := by
  intro k hk
  have hmem : k * 1 * 1 ∈ ((Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    rw [(h1143 G T L I n V₁ h hV₁ z hz hz1).1]
    exact Set.mul_mem_mul (Set.mul_mem_mul hk (Subgroup.one_mem _)) (Subgroup.one_mem _)
  simpa using hmem

theorem kOf_le_centralizer (hTI : PointsTIFact) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    KOf L V₁ V₁ ≤ Subgroup.centralizer (V₁ : Set G) := by
  have hset := natSetting11_of h1102 h1141 h hV₁
  obtain ⟨X, hX⟩ := exists_isCartanX h
  have htrans := (h1141 G T L I n V₁ X h hV₁ hX).1.2
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  obtain ⟨z, hzV₁, hz1, hzT⟩ := exists_z h hV₁
  have hKz := kOf_le_centralizer_z h1143 h hV₁ ⟨hV₁V hzV₁, hzT⟩ hz1
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1, one_mul, mul_one]
  obtain ⟨l, hl, hlv⟩ := htrans z (hV₁V hzV₁) v (hV₁V hv) hz1 hv1
  have hzl : z ∈ conjSubgroup V₁ l := mem_conjSubgroup_iff.mpr (by rw [hlv]; exact hv)
  have hne : V₁ ⊓ conjSubgroup V₁ l ≠ ⊥ := fun hbot => hz1 (by
    have hz' : z ∈ V₁ ⊓ conjSubgroup V₁ l := ⟨hzV₁, hzl⟩
    rw [hbot] at hz'
    exact Subgroup.mem_bot.mp hz')
  have hlN : l ∈ Subgroup.normalizer (V₁ : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp (hTI G T L I n V₁ hset hV₁ l hl hne)
  have hk' : l⁻¹ * k * l ∈ KOf L V₁ V₁ := by
    have := (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_kOf L V₁ V₁ (Subgroup.inv_mem _ hlN)) k).mp hk
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp (hKz hk') z rfl
  rw [← hlv]
  calc l * z * l⁻¹ * k = l * (z * (l⁻¹ * k * l)) * l⁻¹ := by group
    _ = l * (l⁻¹ * k * l * z) * l⁻¹ := by rw [hc]
    _ = k * (l * z * l⁻¹) := by group

end CFSG.Quasithin.Vol2.Ch11.SecD
