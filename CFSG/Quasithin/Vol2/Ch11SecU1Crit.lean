module

public import CFSG.Quasithin.EmptyFaithful.E22PGen
public import CFSG.Quasithin.Vol2.Ch11SecE3L0

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b

variable {G : Type} [Group G] [Finite G]

theorem inEFor_top_of_coatom_conj {T D : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTD : T ≤ D)
    (hDs : Group.IsSolvable ↥D) (hD : IsCoatom D)
    (hII : ∀ A : Subgroup G, A ≤ T → Nat.card A = 2 → IsE 1 ⊤ T A ⊤)
    (hK : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → 4 ≤ Nat.card A →
      ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ K : Subgroup G, IsE 1 ⊤ T (A1b.conjSub g A) K ∧ ¬ K ≤ D) :
    InEFor 1 ⊤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine inEFor_top_of_noTwo hT hII ?_
  intro Ω hΩ h2
  by_cases h4 : ∃ A ∈ Ω, A ≤ T ∧ 4 ≤ Nat.card A
  · obtain ⟨A, hA, hAT, hA4⟩ := h4
    obtain ⟨g, hgT, K, hK1, hK2⟩ := hK A hAT (hΩ.isElemAbelian A hA) hA4
    have hA' : A1b.conjSub g A ∈ Ω := hΩ.conj A hA g (Subgroup.mem_top g)
    have hDX := le_eGen_sup_normalizer_of_isSolvable hT hTD hDs hΩ
    have hKX := (le_eGen hA' hgT hK1).trans (le_sup_left :
      eGen 1 ⊤ T Ω ≤ eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)))
    have hlt : D < eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) :=
      lt_of_le_of_ne hDX fun h => hK2 (h ▸ hKX)
    exact hD.2 _ hlt
  · push Not at h4
    have hW : weakClosure T Ω = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => ?_)
      have hp := isPGroup_of_isElemAbelian (hΩ.isElemAbelian A hA)
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      have h4' := h4 A hA hAT
      have h2' := h2 A hA
      rcases k with _ | _ | k
      · exact le_bot_iff.mpr (Subgroup.card_eq_one.mp (by simpa using hk))
      · exact absurd (by simpa using hk) h2'
      · exfalso
        apply h4'.not_ge
        rw [hk]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hW, Subgroup.normalizer_eq_top_iff.mpr inferInstance, inf_top_eq, sup_top_eq]

omit [Finite G] in
theorem le_centralizer_of_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A) {v : G}
    (hv : v ∈ A) : A ≤ Subgroup.centralizer ({v} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hA.1.is_comm.comm (⟨a, ha⟩ : A) ⟨v, hv⟩
  exact congrArg Subtype.val this

theorem exists_conj_le_eq {T A : Subgroup G} (hT : IsSylowIn 2 T ⊤) {z : G}
    (hzT : ∀ t ∈ T, t * z = z * t) (hA : IsElemAbelian 2 A) {v l : G} (hvA : v ∈ A)
    (hl : l * v * l⁻¹ = z) : ∃ g : G, A1b.conjSub g A ≤ T ∧ g * v * g⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hTC : T ≤ C := fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hzT t ht)
  have hA'C : A1b.conjSub l A ≤ C := by
    intro x hx
    rw [A1b.mem_conjSub_iff] at hx
    have h1 := le_centralizer_of_isElemAbelian hA hvA hx
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    rw [← hl]
    calc x * (l * v * l⁻¹) = l * ((l⁻¹ * x * l) * v) * l⁻¹ := by group
      _ = l * (v * (l⁻¹ * x * l)) * l⁻¹ := by rw [h1]
      _ = l * v * l⁻¹ * x := by group
  have hA'2 : IsPGroup 2 (A1b.conjSub l A) := (isPGroup_of_isElemAbelian hA).map _
  have hTC' : IsSylowIn 2 T C := B6.isSylowTwoOf_mono hT hTC le_top
  obtain ⟨S, hS, hA'S⟩ := exists_isSylowIn_ge 2 hA'C hA'2
  obtain ⟨d, hdC, hdS⟩ := B6.isSylowTwoOf_exists_conj hS hTC'
  refine ⟨d * l, fun x hx => ?_, ?_⟩
  · rw [A1b.conjSub_mul, A1b.mem_conjSub_iff] at hx
    rw [hdS, B6.mem_conjSub]
    exact hA'S hx
  · have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
    calc d * l * v * (d * l)⁻¹ = d * (l * v * l⁻¹) * d⁻¹ := by group
      _ = z := by rw [hl, hdz]; group

theorem exists_conj_le_sylow {T A : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hA : IsElemAbelian 2 A) {b : G} (hbA : b ∈ A) :
    ∃ g : G, A1b.conjSub g A ≤ T ∧ IsSylowIn 2 (T ⊓ Subgroup.centralizer {g * b * g⁻¹})
      (Subgroup.centralizer {g * b * g⁻¹}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  obtain ⟨R, hR, hAR⟩ := exists_isSylowIn_ge 2 (le_centralizer_of_isElemAbelian hA hbA)
    (isPGroup_of_isElemAbelian hA)
  obtain ⟨S, hS, hRS⟩ := exists_isSylowIn_ge 2 (le_top : R ≤ ⊤) hR.2.1
  obtain ⟨g, -, hgS⟩ := B6.isSylowTwoOf_exists_conj hS hT
  have hsub : ∀ X : Subgroup G, X ≤ S → A1b.conjSub g X ≤ T := fun X hX x hx => by
    rw [A1b.mem_conjSub_iff] at hx
    rw [hgS, B6.mem_conjSub]
    exact hX hx
  refine ⟨g, hsub A (hAR.trans hRS), ?_⟩
  set C' := Subgroup.centralizer ({g * b * g⁻¹} : Set G) with hC'
  have hCC' : A1b.conjSub g C = C' := by
    ext x
    rw [A1b.mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      calc x * (g * b * g⁻¹) = g * ((g⁻¹ * x * g) * b) * g⁻¹ := by group
        _ = g * (b * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
        _ = g * b * g⁻¹ * x := by group
    · intro h1
      calc g⁻¹ * x * g * b = g⁻¹ * (x * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * b * g⁻¹ * x) * g := by rw [h1]
        _ = b * (g⁻¹ * x * g) := by group
  have hR'C' : A1b.conjSub g R ≤ T ⊓ C' :=
    le_inf (hsub R hRS) (hCC' ▸ Subgroup.map_mono hR.1)
  have hrel : (A1b.conjSub g R).relIndex C' = R.relIndex C := by
    rw [← hCC']
    exact Subgroup.relIndex_map_map_of_injective R C (MulAut.conj g).injective
  refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, fun h2 => hR.2.2 ?_⟩
  rw [← hrel, ← Subgroup.relIndex_mul_relIndex _ _ _ hR'C' inf_le_right]
  exact Dvd.dvd.mul_left h2 _

omit [Finite G] in
theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

omit [Finite G] in
theorem isElemAbelian_conjSub {A : Subgroup G} (hA : IsElemAbelian 2 A) (g : G) :
    IsElemAbelian 2 (A1b.conjSub g A) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    have h := congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    rw [← hax, ← hby, ← map_mul, h, map_mul]
  · obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_pow, hA.2 a ha, map_one]

theorem not_isSolvable_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : ¬ Group.IsSolvable X := by
  have : Group.IsPerfect X := ⟨SecE3.commutator_eq_top_of_simple hnab⟩
  exact Group.IsPerfect.not_isSolvable X

end CFSG.Quasithin.Vol2.Ch11.SecU1
