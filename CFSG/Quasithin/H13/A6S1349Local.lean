module

public import CFSG.Quasithin.H13.A6S1349
public import CFSG.Quasithin.H13.Sp62C3Verify

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint Equiv

@[expose] def Input1349Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting134 G T L V) (z : G),
    z ∈ fsuV1 T V → z ∉ Subgroup.centralizer (L : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) →
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) →
    ∃ H₀ : Subgroup G,
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ⊓ H₀ = T ∧
      (quasithinO2QuotientIso (Subgroup.normalizer (L : Set G)) ↥(alternatingGroup (Fin 6)) ∨
        quasithinO2QuotientIso (Subgroup.normalizer (L : Set G)) (Perm (Fin 6))) ∧
      quasithinO2QuotientIso (Subgroup.centralizer ({z} : Set G))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
          Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∧
      quasithinO2QuotientIso H₀ (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)) ∧ IsSylowTwoOf T H₀ ∧
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≠ T ∧
        Subgroup.normalizer (L : Set G) ⊓ H₀ ≠ T ∧
        Subgroup.centralizer ({z} : Set G) ⊓ H₀ ≠ T) ∧
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≠
          Subgroup.normalizer (L : Set G) ∧
        Subgroup.normalizer (L : Set G) ⊓ H₀ ≠ Subgroup.normalizer (L : Set G) ∧
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≠
          Subgroup.centralizer ({z} : Set G) ∧
        Subgroup.centralizer ({z} : Set G) ⊓ H₀ ≠ Subgroup.centralizer ({z} : Set G) ∧
        Subgroup.normalizer (L : Set G) ⊓ H₀ ≠ H₀ ∧ Subgroup.centralizer ({z} : Set G) ⊓ H₀ ≠ H₀) ∧
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≠
          Subgroup.normalizer (L : Set G) ⊓ H₀ ∧
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≠
          Subgroup.centralizer ({z} : Set G) ⊓ H₀ ∧
        Subgroup.normalizer (L : Set G) ⊓ H₀ ≠ Subgroup.centralizer ({z} : Set G) ⊓ H₀) ∧
      (LieModel ↥(Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ H₀)
          .PSp 3 2 1 →
        (∀ a ∈ Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ H₀,
          ∀ b ∈ Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ H₀,
            orderOf a = 2 → IsConj a b →
              ∃ e ∈ Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ H₀,
                e * a * e⁻¹ = b) ∧
        ∀ e : G, IsConj S.zV e → S.zV * e = e * S.zV → e ≠ S.zV →
          Subgroup.centralizer ({S.zV * e} : Set G) ≤
            Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ H₀)

namespace Setting134

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting134 G T L V)
include S

theorem d4 {X : Subgroup G} (hX : ¬ X ≤ Subgroup.normalizer (L : Set G)) (N : Subgroup G)
    (hNT : N ≤ T) (hN : Subgroup.normalizer (L : Set G) ⊔ X ≤ Subgroup.normalizer (N : Set G)) :
    N = ⊥ := by
  by_contra hN1
  have h2 : IsTwoLocal (Subgroup.normalizer (N : Set G)) :=
    ⟨N, hN1, S.h13.sylow.1.to_le hNT, rfl⟩
  have heq := S.uniqueM.1.1.2 _ h2 (le_sup_left.trans hN)
  exact hX (le_sup_right.trans (heq ▸ hN))

theorem d5 (h1222 : Stmt12_2_2) : Subgroup.center ↥(Subgroup.normalizer (L : Set G)) ≠ ⊥ := by
  have hzM : S.zV ∈ Subgroup.normalizer (L : Set G) :=
    S.T_le_NL (S.V_le_T S.zV_mem_V)
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨⟨S.zV, hzM⟩, Subgroup.mem_center_iff.2 fun g => ?_⟩, fun h => S.zV_ne_one ?_⟩
  · have hg : (g : G) ∈ Subgroup.centralizer ({S.zV} : Set G) := by
      rw [S.centralizer_zV h1222]
      exact g.2
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 hg
  · have := congrArg (fun x : ↥(Subgroup.center ↥(Subgroup.normalizer (L : Set G))) =>
      ((x : ↥(Subgroup.normalizer (L : Set G))) : G)) h
    simpa using this

end Setting134

theorem input1349_of_local (h1222 : Stmt12_2_2) (hloc : Input1349Local) : Input1349 := by
  intro G _ _ T L V S z hz hzL hCz hsol
  obtain ⟨H₀, hT, hD1, hD2a, hD2b, hsylz, hsylH, ⟨t1, t2, t3⟩, ⟨x1, x2, x3, x4, x5, x6⟩,
    ⟨d1, d2, d3⟩, hfus⟩ := hloc G T L V S z hz hzL hCz hsol
  refine ⟨H₀, ?_, hfus⟩
  set M := Subgroup.normalizer (L : Set G)
  set Gz := Subgroup.centralizer ({z} : Set G)
  have hsylM : IsSylowTwoOf T M := A5.isSylowTwoOf_of_le S.h13.sylow S.T_le_NL
  have hTe : ![M, Gz, H₀] 0 ⊓ ![M, Gz, H₀] 1 ⊓ ![M, Gz, H₀] 2 = T := hT
  refine isDSystemIn_C3_of ![M, Gz, H₀] hD1 hD2a hD2b ?_ ?_ ?_ ?_ ?_ (Or.inl (S.d5 h1222))
  · intro i
    rw [hTe]
    fin_cases i
    · exact hsylM
    · exact hsylz
    · exact hsylH
  · intro i j hij
    rw [hTe]
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact t1 | exact t2 | exact t3
      | exact fun h => t1 ((inf_comm _ _).trans h)
      | exact fun h => t2 ((inf_comm _ _).trans h)
      | exact fun h => t3 ((inf_comm _ _).trans h)
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact x1 | exact x2 | exact x4
      | exact fun h => x3 ((inf_comm _ _).trans h)
      | exact fun h => x5 ((inf_comm _ _).trans h)
      | exact fun h => x6 ((inf_comm _ _).trans h)
  · intro i j k hij hik hjk
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first
      | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
      | exact d1 | exact d1.symm
      | exact fun h => d2 ((inf_comm _ _).trans h)
      | exact fun h => d2 ((inf_comm _ _).trans h.symm)
      | exact fun h => d3 ((inf_comm _ _).trans (h.trans (inf_comm _ _)))
      | exact fun h => d3 ((inf_comm _ _).trans (h.symm.trans (inf_comm _ _)))
  · intro N hNT hN
    rw [hTe] at hNT
    exact S.d4 hCz N hNT (le_sup_left.trans hN)
