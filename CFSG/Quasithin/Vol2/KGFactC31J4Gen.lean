module

public import CFSG.Quasithin.Vol2.KGFactC31Gen

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open
open scoped Pointwise

variable {A : Type} [Group A]

theorem le_of_normalizer_le [Finite A] {R X Q : Subgroup A} (hR2 : IsPGroup 2 ↥R)
    (hrad : pCoreOf 2 (Subgroup.normalizer (R : Set A)) = R)
    (hNX : Subgroup.normalizer (R : Set A) ≤ X) (hQ2 : IsPGroup 2 ↥Q)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set A)) : Q ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Q ⊓ Subgroup.normalizer (R : Set A) ≤ R := by
    refine le_trans ?_ hrad.le
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (hQ2.to_le inf_le_left)
    intro x hx
    exact mem_normalizer_inf (hXQ (hNX hx)) (Subgroup.le_normalizer hx)
  have hRQ : R ≤ Subgroup.normalizer (Q : Set A) :=
    Subgroup.le_normalizer.trans (hNX.trans hXQ)
  have hK2 : IsPGroup 2 ↥(Q ⊔ R) := hQ2.to_sup_of_normal_left' hR2 hRQ
  have hKcoe : ((Q ⊔ R : Subgroup A) : Set A) = (Q : Set A) * (R : Set A) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q R hRQ
  by_contra hQR
  have hnil : Group.IsNilpotent ↥(Q ⊔ R) := hK2.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥(Q ⊔ R))
  have hlt : R.subgroupOf (Q ⊔ R) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hQR fun q hq => ?_
    have : (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(Q ⊔ R)) ∈ R.subgroupOf (Q ⊔ R) := by
      rw [h]; trivial
    exact this
  obtain ⟨k, hkN, hkR⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  have hkNA : (k : A) ∈ Subgroup.normalizer (R : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := (Subgroup.mem_normalizer_iff.mp hkN ⟨h, Subgroup.mem_sup_right hh⟩).mp
        (Subgroup.mem_subgroupOf.mpr hh)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hh
      have hhK : h ∈ Q ⊔ R := by
        have h2 : (k : A)⁻¹ * ((k : A) * h * (k : A)⁻¹) * (k : A) ∈ Q ⊔ R :=
          (Q ⊔ R).mul_mem ((Q ⊔ R).mul_mem ((Q ⊔ R).inv_mem k.2) (Subgroup.mem_sup_right hh)) k.2
        simpa [mul_assoc] using h2
      have := (Subgroup.mem_normalizer_iff.mp hkN ⟨h, hhK⟩).mpr
        (by simpa [Subgroup.mem_subgroupOf] using hh)
      simpa [Subgroup.mem_subgroupOf] using this
  have hk : (k : A) ∈ (Q : Set A) * (R : Set A) := hKcoe ▸ k.2
  obtain ⟨q, hq, r, hr, hqr⟩ := hk
  have hqN : q ∈ Subgroup.normalizer (R : Set A) := by
    have : q = (k : A) * r⁻¹ := by rw [← hqr]; group
    rw [this]
    exact (Subgroup.normalizer (R : Set A)).mul_mem hkNA
      (Subgroup.le_normalizer (R.inv_mem hr))
  apply hkR
  show (k : A) ∈ R
  rw [← hqr]
  exact R.mul_mem (h1 ⟨hq, hqN⟩) hr

theorem thompsonJ_eq_of_unique {R E : Subgroup A} (hE : CFSG.Quasithin.IsMaxElemAbelian R E)
    (huniq : ∀ B : Subgroup A, CFSG.Quasithin.IsMaxElemAbelian R B → B = E) :
    CFSG.Quasithin.thompsonJ R = E := by
  apply le_antisymm
  · exact iSup₂_le fun B hB => (huniq B hB).le
  · exact le_iSup₂_of_le E hE le_rfl

theorem eq_bot_of_perfect_of_comm {M₀ E : Subgroup A} (hM₀E : M₀ ≤ E)
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hper : ⁅M₀, M₀⁆ = M₀) : M₀ = ⊥ := by
  rw [← hper, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact hE y (hM₀E hy) x (hM₀E hx)

theorem eq_of_perfect_normal {H E M₀ : Subgroup A} (hEH : E ≤ H)
    (hEn : H ≤ Subgroup.normalizer (E : Set A)) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hmin : ∀ N : Subgroup A, N ≤ E → H ≤ Subgroup.normalizer (N : Set A) → N = ⊥ ∨ N = E)
    (hmax : ∀ N : Subgroup A, E ≤ N → N ≤ H → H ≤ Subgroup.normalizer (N : Set A) →
      N = E ∨ N = H)
    (hCE : H ⊓ Subgroup.centralizer (E : Set A) ≤ E) (hM₀H : M₀ ≤ H)
    (hM₀n : H ≤ Subgroup.normalizer (M₀ : Set A)) (hper : ⁅M₀, M₀⁆ = M₀) (hne : M₀ ≠ ⊥) :
    M₀ = H := by
  have hEM : E ≤ Subgroup.normalizer (M₀ : Set A) := hEH.trans hM₀n
  have hsup : H ≤ Subgroup.normalizer ((M₀ ⊔ E : Subgroup A) : Set A) := fun h hh =>
    mem_normalizer_sup (hM₀n hh) (hEn hh)
  rcases hmax (M₀ ⊔ E) le_sup_right (sup_le hM₀H hEH) hsup with h1 | h1
  · exact absurd (eq_bot_of_perfect_of_comm (h1 ▸ le_sup_left) hE hper) hne
  · have hinf : H ≤ Subgroup.normalizer ((M₀ ⊓ E : Subgroup A) : Set A) := fun h hh =>
      mem_normalizer_inf (hM₀n hh) (hEn hh)
    rcases hmin (M₀ ⊓ E) inf_le_right hinf with h2 | h2
    ·
      exfalso
      apply hne
      refine eq_bot_of_perfect_of_comm (E := E) (fun x hx => hCE ⟨hM₀H hx, ?_⟩) hE hper
      show x ∈ Subgroup.centralizer (E : Set A)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hc : e * x * e⁻¹ * x⁻¹ ∈ M₀ ⊓ E := by
        refine ⟨?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hEM he) x).mp hx
          exact M₀.mul_mem this (M₀.inv_mem hx)
        · have := (Subgroup.mem_normalizer_iff.mp (hEn (hM₀H hx)) e⁻¹).mp (E.inv_mem he)
          have h3 : e * (x * e⁻¹ * x⁻¹) ∈ E := E.mul_mem he this
          simpa [mul_assoc] using h3
      rw [h2, Subgroup.mem_bot] at hc
      have : e * x * e⁻¹ = x := by
        calc e * x * e⁻¹ = e * x * e⁻¹ * x⁻¹ * x := by group
          _ = x := by rw [hc, one_mul]
      calc e * x = e * x * e⁻¹ * e := by group
        _ = x * e := by rw [this]
    · rw [← h1]
      exact le_antisymm le_sup_left (sup_le le_rfl (h2 ▸ inf_le_left))

theorem commutator_eq_top_of_perfect {K : Subgroup A} (hper : ⁅K, K⁆ = K) :
    commutator ↥K = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, hper]

theorem eq_bot_of_perfect_of_isPGroup [Finite A] {K : Subgroup A} (hper : ⁅K, K⁆ = K)
    (hK : IsPGroup 2 ↥K) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥K := hK.isNilpotent
  have hsub := subsingleton_of_perfect_solvable (commutator_eq_top_of_perfect hper) inferInstance
  rw [eq_bot_iff]
  intro x hx
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥K) 1))

theorem pCoreOf_eq_of_max [Finite A] {H E : Subgroup A} (hEH : E ≤ H)
    (hEn : H ≤ Subgroup.normalizer (E : Set A)) (hE2 : IsPGroup 2 ↥E)
    (hmax : ∀ N : Subgroup A, E ≤ N → N ≤ H → H ≤ Subgroup.normalizer (N : Set A) →
      N = E ∨ N = H)
    (hH : ¬ IsPGroup 2 ↥H) : pCoreOf 2 H = E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : E ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hEH hEn hE2
  rcases hmax _ hle (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) with h | h
  · exact h
  · have h2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
    rw [h] at h2
    exact absurd h2 hH

theorem isShort2_of_irred [Finite A] {H E : Subgroup A} (hEn : H ≤ Subgroup.normalizer (E : Set A))
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEsq : ∀ a ∈ E, a * a = 1) (hE1 : E ≠ ⊥)
    (hmin : ∀ N : Subgroup A, N ≤ E → H ≤ Subgroup.normalizer (N : Set A) → N = ⊥ ∨ N = E)
    (hCE : H ⊓ Subgroup.centralizer (E : Set A) ≤ E) (hOE : pCoreOf 2 H = E)
    (hper : ⁅H, H⁆ = H) (hne : H ≠ ⊥) (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H)) :
    CFSG.QuasithinUnique.IsShort2 H := by
  have hQ : CFSG.QuasithinUnique.blockQ H = E := hOE
  have hcle : ⁅E, H⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro e he g hg
    have h1 : g * e⁻¹ * g⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hEn hg) e⁻¹).mp (E.inv_mem he)
    rw [commutatorElement_def]
    have h2 := E.mul_mem he h1
    simpa [mul_assoc] using h2
  have hcn : H ≤ Subgroup.normalizer ((⁅E, H⁆ : Subgroup A) : Set A) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEn hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)]
  have hcne : ⁅E, H⁆ ≠ ⊥ := by
    intro h0
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
    exact hne (eq_bot_of_perfect_of_comm (fun x hx => hCE ⟨hx, h0 hx⟩) hE hper)
  have hU : CFSG.QuasithinUnique.blockU H = E := by
    show ⁅CFSG.QuasithinUnique.blockQ H, H⁆ = E
    rw [hQ]
    exact (hmin _ hcle hcn).resolve_left hcne
  have hZ : CFSG.QuasithinUnique.blockZ H = ⊥ := by
    show CFSG.QuasithinUnique.blockU H ⊓ Subgroup.centralizer (H : Set A) = ⊥
    rw [hU]
    have hn : H ≤ Subgroup.normalizer
        ((E ⊓ Subgroup.centralizer (H : Set A) : Subgroup A) : Set A) := fun g hg =>
      mem_normalizer_inf (hEn hg)
        (normalizer_le_normalizer_centralizer H (Subgroup.le_normalizer hg))
    refine (hmin _ inf_le_left hn).resolve_right fun h1 => hcne ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h1.symm.le.trans inf_le_right
  refine ⟨?_, ?_, ⟨?_, ?_⟩, Or.inl hq, ?_, ?_⟩
  ·
    intro N _ hN
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent (↥H ⧸ N) := hN.isNilpotent
    have hc : commutator (↥H ⧸ N) = ⊤ := by
      have hsurj := QuotientGroup.mk'_surjective N
      rw [commutator_def, ← Subgroup.map_top_of_surjective _ hsurj, ← Subgroup.map_commutator,
        ← commutator_def, commutator_eq_top_of_perfect hper]
    have hsub := subsingleton_of_perfect_solvable hc inferInstance
    rw [eq_top_iff]
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  · show H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set A) ≤ pCoreOf 2 H
    rw [hOE]
    exact hCE
  · rw [hU, hQ]
    intro x hx
    exact ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => hE y hy x hx⟩
  · rw [hU]
    intro x hx
    rw [pow_two]
    exact hEsq x hx
  · rw [hZ, hU]
    exact bot_lt_iff_ne_bot.mpr hE1
  · intro W _ hWU hHW
    rw [hZ]
    rw [hU] at hWU ⊢
    exact hmin W hWU hHW

theorem comm_eq_bot_of_card_le_four [Finite A] {M₀ V : Subgroup A} (hper : ⁅M₀, M₀⁆ = M₀)
    (hM₀V : M₀ ≤ Subgroup.normalizer (V : Set A)) (hV : Nat.card V ≤ 4) : ⁅V, M₀⁆ = ⊥ := by
  have hconj : ∀ m : ↥M₀, ∀ v : ↥V, (m : A) * v * (m : A)⁻¹ ∈ V := fun m v =>
    (Subgroup.mem_normalizer_iff.mp (hM₀V m.2) v).mp v.2
  let φ : ↥M₀ →* Equiv.Perm ↥V :=
    { toFun := fun m =>
        { toFun := fun v => ⟨(m : A) * v * (m : A)⁻¹, hconj m v⟩
          invFun := fun v => ⟨(m : A)⁻¹ * v * (m : A), by
            simpa using hconj m⁻¹ v⟩
          left_inv := fun v => Subtype.ext (by simp [mul_assoc])
          right_inv := fun v => Subtype.ext (by simp [mul_assoc]) }
      map_one' := by ext v; simp
      map_mul' := fun m n => by ext v; simp [mul_assoc] }
  have hsolv : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable hV
  have hcommK : commutator ↥M₀ = ⊤ := commutator_eq_top_of_perfect hper
  have hf : Function.Surjective φ.rangeRestrict := MonoidHom.rangeRestrict_surjective φ
  have hcommR : commutator ↥φ.range = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ hf, ← Subgroup.map_commutator,
      ← commutator_def, hcommK]
  have hsub := subsingleton_of_perfect_solvable hcommR inferInstance
  have hφ : ∀ m : ↥M₀, φ m = 1 := fun m =>
    congrArg Subtype.val (Subsingleton.elim (φ.rangeRestrict m) 1)
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro v hv m hm
  have h1 := congrArg (fun σ : Equiv.Perm ↥V => ((σ ⟨v, hv⟩ : ↥V) : A)) (hφ ⟨m, hm⟩)
  simp only [Equiv.Perm.coe_one, id_eq] at h1
  rw [Subgroup.mem_bot, commutatorElement_def]
  have h2 : m * v * m⁻¹ = v := h1
  calc v * m * v⁻¹ * m⁻¹ = v * (m * v * m⁻¹)⁻¹ := by group
    _ = 1 := by rw [h2, mul_inv_cancel]

end CFSG.Quasithin.KGC31

end
