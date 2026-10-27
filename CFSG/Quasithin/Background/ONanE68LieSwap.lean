module

public import CFSG.Quasithin.Background.ONanE68LieRank1
public import CFSG.Quasithin.Background.ONanE68LieSp4Alg

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Conj

variable {G : Type} [Group G]

abbrev cg (g : G) : G →* G := (MulAut.conj g).toMonoidHom

theorem conjugate_eq_comap (H : Subgroup G) (g : G) : CFSG.conjugate H g = H.comap (cg g) := by
  ext x
  rw [BenderBranch.mem_conjugate_iff, Subgroup.mem_comap]
  rfl

theorem conjugate_normalizer (H : Subgroup G) (g : G) :
    CFSG.conjugate (Subgroup.normalizer (H : Set G)) g =
      Subgroup.normalizer ((CFSG.conjugate H g : Subgroup G) : Set G) := by
  rw [conjugate_eq_comap, conjugate_eq_comap]
  exact Subgroup.comap_normalizer_eq_of_le_range fun x _ =>
    ⟨g⁻¹ * x * g, by show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩

variable {T V : Subgroup G}

theorem conjugate_pgOf {g : G} (hg : g ∈ T ⊓ Subgroup.centralizer (V : Set G))
    (Λ : Subgroup G) : CFSG.conjugate (pgOf T V Λ) g = pgOf T V (CFSG.conjugate Λ g) := by
  unfold pgOf
  rw [BenderBranch.conjugate_inf, BenderBranch.conjugate_eq_iff_mem_normalizer.2
    (Subgroup.le_normalizer hg)]

theorem conjugate_borOf {g : G} (hg : g ∈ T ⊓ Subgroup.centralizer (V : Set G))
    (Λ : Subgroup G) : CFSG.conjugate (borOf T V Λ) g = borOf T V (CFSG.conjugate Λ g) := by
  unfold borOf
  rw [BenderBranch.conjugate_inf, conjugate_normalizer, conjugate_pgOf hg]

theorem sup_conj_mem {A B C : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ C)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ C) : ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ C := by
  have : A ⊔ B ≤ C.comap (cg g) := sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  exact fun x hx => this hx

end Conj

section Swap

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

omit [Finite G] in
theorem isSolvable_sup_of_commute {A B : Subgroup G} [Group.IsSolvable ↥A] [Group.IsSolvable ↥B]
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Group.IsSolvable ↥(A ⊔ B) := by
  have hc : ∀ (m : ↥A) (n : ↥B), Commute (A.subtype m) (B.subtype n) := fun a b => h a a.2 b b.2
  have hrange : (A.subtype.noncommCoprod B.subtype hc).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have : Group.IsSolvable ↥(A.subtype.noncommCoprod B.subtype hc).range :=
    Group.isSolvable_of_surjective (f := (A.subtype.noncommCoprod B.subtype hc).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  rwa [hrange] at this

theorem borel_le_M_or_small_swap (hInn : Ch1.EvenLieAutInner)
    (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L)) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hZ0L : Subgroup.center ↥L = ⊥)
    {q₀ : G} (hq₀ : q₀ ∈ T ⊓ Subgroup.centralizer (V : Set G))
    (hne : CFSG.conjugate L q₀ ≠ L)
    (hQ2 : ∀ q ∈ T ⊓ Subgroup.centralizer (V : Set G),
      CFSG.conjugate L q = L ∨ CFSG.conjugate L q = CFSG.conjugate L q₀)
    (hCh : CharTwo (borOf T V L))
    (hquot : ∀ a ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
        a * b * a⁻¹ * b⁻¹ ∈ sylowBar T V L)
    (hord : ∀ c ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)), orderOf c = 3 →
      4 < (sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L))).relIndex
        (sylowBar T V L) ∨
      (Nat.card (sylowBar T V L) = 4 ∧
        sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L)) = ⊥)) :
    borOf T V L ≤ M ∨ (Nat.card (pgOf T V L) = 4 ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQH : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
      (Subgroup.centralizer (U : Set G)) := e6_5_one h hU
  have hq₀H : q₀ ∈ Subgroup.centralizer (U : Set G) := hQH.1 hq₀
  have hL₂ : IsComponentIn (CFSG.conjugate L q₀) (Subgroup.centralizer (U : Set G)) :=
    isComponentIn_conjugate_of_mem hL hq₀H
  have hcommLL : ∀ x ∈ L, ∀ y ∈ CFSG.conjugate L q₀, x * y = y * x := by
    rcases BenderBranch.eq_or_commute_of_isComponentIn hL hL₂ with heq | hcomm
    · exact absurd heq.symm hne
    · have hLc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      intro x hx y hy
      exact (Subgroup.mem_centralizer_iff.1 (hLc hx) y hy).symm
  have hLL₂ : L ⊓ CFSG.conjugate L q₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxL₂⟩
    have hxc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcommLL g.1 g.2 x hxL₂)
    rw [hZ0L, Subgroup.mem_bot] at hxc
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hxc)
  have hZ2 := isPGroup_two_of_center_eq_bot hZ0L
  have hZ := center_le_sylow h hU hL hZ2
  have hSyl₁ : IsSylowTwoOf (pgOf T V L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hQH hL.1 hL.2.2
  have hcent₁ : ∀ y ∈ borOf T V L, (∀ p ∈ pgOf T V L, y * p = p * y) → y ∈ pgOf T V L :=
    (charTwo_borOf_iff hSyl₁).1 hCh
  have hcomm₁ : ∀ x ∈ borOf T V L, ∀ y ∈ borOf T V L, x * y * x⁻¹ * y⁻¹ ∈ pgOf T V L :=
    fun x hx y hy => comm_mem_pgOf hZ hquot hx hy
  have hB₂ : borOf T V (CFSG.conjugate L q₀) = CFSG.conjugate (borOf T V L) q₀ :=
    (conjugate_borOf hq₀ L).symm
  have hP₂ : pgOf T V (CFSG.conjugate L q₀) = CFSG.conjugate (pgOf T V L) q₀ :=
    (conjugate_pgOf hq₀ L).symm
  have hmemB₂ : ∀ y, y ∈ borOf T V (CFSG.conjugate L q₀) ↔ q₀ * y * q₀⁻¹ ∈ borOf T V L :=
    fun y => by rw [hB₂, BenderBranch.mem_conjugate_iff]
  have hmemP₂ : ∀ y, y ∈ pgOf T V (CFSG.conjugate L q₀) ↔ q₀ * y * q₀⁻¹ ∈ pgOf T V L :=
    fun y => by rw [hP₂, BenderBranch.mem_conjugate_iff]
  have hP₁2 : IsPGroup 2 (pgOf T V L) := h.isPGroup_Q.to_le inf_le_left
  have hP₂2 : IsPGroup 2 (pgOf T V (CFSG.conjugate L q₀)) := h.isPGroup_Q.to_le inf_le_left
  have hcent₂ : ∀ y ∈ borOf T V (CFSG.conjugate L q₀),
      (∀ p ∈ pgOf T V (CFSG.conjugate L q₀), y * p = p * y) →
        y ∈ pgOf T V (CFSG.conjugate L q₀) := by
    intro y hy hc
    rw [hmemP₂]
    refine hcent₁ _ ((hmemB₂ y).1 hy) fun p hp => ?_
    have hp₂ : q₀⁻¹ * p * q₀ ∈ pgOf T V (CFSG.conjugate L q₀) := by
      rw [hmemP₂, show q₀ * (q₀⁻¹ * p * q₀) * q₀⁻¹ = p by group]
      exact hp
    have := hc _ hp₂
    calc q₀ * y * q₀⁻¹ * p = q₀ * (y * (q₀⁻¹ * p * q₀)) * q₀⁻¹ := by group
      _ = q₀ * ((q₀⁻¹ * p * q₀) * y) * q₀⁻¹ := by rw [this]
      _ = p * (q₀ * y * q₀⁻¹) := by group
  have hcomm₂ : ∀ x ∈ borOf T V (CFSG.conjugate L q₀), ∀ y ∈ borOf T V (CFSG.conjugate L q₀),
      x * y * x⁻¹ * y⁻¹ ∈ pgOf T V (CFSG.conjugate L q₀) := by
    intro x hx y hy
    rw [hmemP₂]
    have h1 := hcomm₁ _ ((hmemB₂ x).1 hx) _ ((hmemB₂ y).1 hy)
    have e : q₀ * (x * y * x⁻¹ * y⁻¹) * q₀⁻¹ = q₀ * x * q₀⁻¹ * (q₀ * y * q₀⁻¹) *
        (q₀ * x * q₀⁻¹)⁻¹ * (q₀ * y * q₀⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  have hcommB : ∀ x ∈ borOf T V L, ∀ y ∈ borOf T V (CFSG.conjugate L q₀), x * y = y * x :=
    fun x hx y hy => hcommLL x (borOf_le_left hx) y (borOf_le_left hy)
  have hcommP : ∀ x ∈ pgOf T V L, ∀ y ∈ pgOf T V (CFSG.conjugate L q₀), x * y = y * x :=
    fun x hx y hy => hcommLL x (pgOf_le_left hx) y (pgOf_le_left hy)
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set L₂ := CFSG.conjugate L q₀ with hL₂def
  set K := borOf T V L ⊔ borOf T V L₂ with hK
  set D := pgOf T V L ⊔ pgOf T V L₂ with hD
  have hD2 : IsPGroup 2 D := h.isPGroup_Q.to_le (sup_le inf_le_left inf_le_left)
  have hconjQ : ∀ q ∈ Q, ∀ Λ : Subgroup G, (Λ = L ∨ Λ = L₂) →
      (CFSG.conjugate Λ q = L ∨ CFSG.conjugate Λ q = L₂) := by
    intro q hq Λ hΛ
    rcases hΛ with rfl | rfl
    · exact hQ2 q hq
    · rw [hL₂def, BenderBranch.conjugate_conjugate]
      exact hQ2 _ (Q.mul_mem hq₀ hq)
  have hQB : ∀ q ∈ Q, ∀ Λ : Subgroup G, (Λ = L ∨ Λ = L₂) → ∀ x ∈ borOf T V Λ, q * x * q⁻¹ ∈ K := by
    intro q hq Λ hΛ x hx
    have hq' : q⁻¹ ∈ Q := Q.inv_mem hq
    have hxc : q * x * q⁻¹ ∈ CFSG.conjugate (borOf T V Λ) q⁻¹ := by
      rw [BenderBranch.mem_conjugate_iff, show q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x by group]
      exact hx
    rw [conjugate_borOf hq'] at hxc
    rcases hconjQ q⁻¹ hq' Λ hΛ with h1 | h1
    · rw [h1] at hxc
      exact Subgroup.mem_sup_left hxc
    · rw [h1] at hxc
      exact Subgroup.mem_sup_right hxc
  have hQP : ∀ q ∈ Q, ∀ Λ : Subgroup G, (Λ = L ∨ Λ = L₂) → ∀ x ∈ pgOf T V Λ, q * x * q⁻¹ ∈ D := by
    intro q hq Λ hΛ x hx
    have hq' : q⁻¹ ∈ Q := Q.inv_mem hq
    have hxc : q * x * q⁻¹ ∈ CFSG.conjugate (pgOf T V Λ) q⁻¹ := by
      rw [BenderBranch.mem_conjugate_iff, show q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x by group]
      exact hx
    rw [conjugate_pgOf hq'] at hxc
    rcases hconjQ q⁻¹ hq' Λ hΛ with h1 | h1
    · rw [h1] at hxc
      exact Subgroup.mem_sup_left hxc
    · rw [h1] at hxc
      exact Subgroup.mem_sup_right hxc
  have hQN : Q ≤ Subgroup.normalizer (K : Set G) := fun q hq =>
    mem_normalizer_of_conj_le (sup_conj_mem (hQB q hq L (Or.inl rfl)) (hQB q hq L₂ (Or.inr rfl)))
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) := fun q hq =>
    mem_normalizer_of_conj_le (sup_conj_mem (hQP q hq L (Or.inl rfl)) (hQP q hq L₂ (Or.inr rfl)))
  have hB₁D : borOf T V L ≤ Subgroup.normalizer (D : Set G) := fun b hb =>
    mem_normalizer_of_conj_le (sup_conj_mem
      (fun p hp => Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.1 (borOf_le_normalizer hb) p).1 hp))
      (fun p hp => by
        rw [show b * p * b⁻¹ = p by rw [hcommLL b (borOf_le_left hb) p (pgOf_le_left hp)]; group]
        exact Subgroup.mem_sup_right hp))
  have hB₂D : borOf T V L₂ ≤ Subgroup.normalizer (D : Set G) := fun b hb =>
    mem_normalizer_of_conj_le (sup_conj_mem
      (fun p hp => by
        rw [show b * p * b⁻¹ = p by rw [← hcommLL p (pgOf_le_left hp) b (borOf_le_left hb)]; group]
        exact Subgroup.mem_sup_left hp)
      (fun p hp => Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.1 (borOf_le_normalizer hb) p).1 hp)))
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := sup_le hB₁D hB₂D
  have hDK' : D ≤ K := sup_le_sup pgOf_le_borOf pgOf_le_borOf
  have hDpc : D ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDK' hKD hD2
  have hKchar : CharTwo K := by
    intro y hy
    obtain ⟨hyK, hyC⟩ := hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommB hyK
    have hy₁c : ∀ p ∈ pgOf T V L, y₁ * p = p * y₁ := by
      intro p hp
      have h1 := Subgroup.mem_centralizer_iff.1 hyC p (hDpc (Subgroup.mem_sup_left hp))
      have h2 : p * y₂ = y₂ * p := hcommLL p (pgOf_le_left hp) y₂ (borOf_le_left hy₂)
      have h3 : (p * y₁) * y₂ = (y₁ * p) * y₂ := by
        calc p * y₁ * y₂ = p * (y₁ * y₂) := by group
          _ = (y₁ * y₂) * p := h1
          _ = y₁ * (y₂ * p) := by group
          _ = y₁ * (p * y₂) := by rw [h2]
          _ = y₁ * p * y₂ := by group
      exact (mul_right_cancel h3).symm
    have hy₂c : ∀ p ∈ pgOf T V L₂, y₂ * p = p * y₂ := by
      intro p hp
      have h1 := Subgroup.mem_centralizer_iff.1 hyC p (hDpc (Subgroup.mem_sup_right hp))
      have h2 : y₁ * p = p * y₁ := hcommLL y₁ (borOf_le_left hy₁) p (pgOf_le_left hp)
      have h3 : y₁ * (p * y₂) = y₁ * (y₂ * p) := by
        calc y₁ * (p * y₂) = (y₁ * p) * y₂ := by group
          _ = (p * y₁) * y₂ := by rw [h2]
          _ = p * (y₁ * y₂) := by group
          _ = (y₁ * y₂) * p := h1
          _ = y₁ * (y₂ * p) := by group
      exact (mul_left_cancel h3).symm
    exact hDpc (Subgroup.mul_mem_sup (hcent₁ y₁ hy₁ hy₁c) (hcent₂ y₂ hy₂ hy₂c))
  have hB₁solv : Group.IsSolvable ↥(borOf T V L) :=
    isSolvable_of_comm_le_pGroup pgOf_le_borOf hP₁2 hcomm₁
  have hB₂solv : Group.IsSolvable ↥(borOf T V L₂) :=
    isSolvable_of_comm_le_pGroup pgOf_le_borOf hP₂2 hcomm₂
  have hKsolv : Group.IsSolvable ↥K := isSolvable_sup_of_commute hcommB
  have hKH : K ≤ Subgroup.centralizer (U : Set G) :=
    sup_le (borOf_le_left.trans hL.1) (borOf_le_left.trans hL₂.1)
  have hDn : K ⊔ Q ≤ Subgroup.normalizer (D : Set G) := sup_le hKD hQD
  have hDK : D ≤ K ⊔ Q := (sup_le inf_le_left inf_le_left : D ≤ Q).trans le_sup_right
  rcases borel_le_M_or_alt3 h hU hKH hQN hKchar hKsolv hD2 hDn hDK with hle | ⟨B', c, hcK, hc3,
    hU4, hcomm, hrel, hLeq⟩
  · exact Or.inl (le_sup_left.trans hle)
  right
  have hcB' : c ∈ B' := by
    rw [hLeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  obtain ⟨b₁, hb₁, b₂, hb₂, hcb⟩ := exists_mul_of_mem_sup_of_commute hcommB hcK
  have hb12 : Commute b₁ b₂ := hcommB b₁ hb₁ b₂ hb₂
  have hc3' : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  have hpow : b₁ ^ 3 * b₂ ^ 3 = 1 := by rw [← hb12.mul_pow 3, ← hcb]; exact hc3'
  have hb₁3 : b₁ ^ 3 = 1 := by
    have h1 : b₁ ^ 3 = (b₂ ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have hmem : b₁ ^ 3 ∈ L ⊓ L₂ := ⟨L.pow_mem (borOf_le_left hb₁) 3, by
      rw [h1]; exact L₂.inv_mem (L₂.pow_mem (borOf_le_left hb₂) 3)⟩
    rw [hLL₂, Subgroup.mem_bot] at hmem
    exact hmem
  have hb₂3 : b₂ ^ 3 = 1 := by rwa [hb₁3, one_mul] at hpow
  have hdecomp : ∀ a ∈ V, c * a = a * c → b₁ * a = a * b₁ ∧ b₂ * a = a * b₂ := by
    intro a haV hac
    have haL : a ∈ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL haV
    have haL₂ : a ∈ Subgroup.normalizer (L₂ : Set G) := le_normalizer_of_component h hU hL₂ haV
    have huL : a * b₁ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 haL b₁).1 (borOf_le_left hb₁)
    have hwL₂ : a * b₂ * a⁻¹ ∈ L₂ := (Subgroup.mem_normalizer_iff.1 haL₂ b₂).1 (borOf_le_left hb₂)
    have huw : (a * b₁ * a⁻¹) * (a * b₂ * a⁻¹) = b₁ * b₂ := by
      calc (a * b₁ * a⁻¹) * (a * b₂ * a⁻¹) = a * (b₁ * b₂) * a⁻¹ := by group
        _ = a * c * a⁻¹ := by rw [hcb]
        _ = c := by rw [← hac]; group
        _ = b₁ * b₂ := hcb
    have h1 : b₁⁻¹ * (a * b₁ * a⁻¹) = b₂ * (a * b₂ * a⁻¹)⁻¹ := by
      calc b₁⁻¹ * (a * b₁ * a⁻¹) = b₁⁻¹ * ((a * b₁ * a⁻¹) * (a * b₂ * a⁻¹)) * (a * b₂ * a⁻¹)⁻¹ := by
            group
        _ = b₁⁻¹ * (b₁ * b₂) * (a * b₂ * a⁻¹)⁻¹ := by rw [huw]
        _ = b₂ * (a * b₂ * a⁻¹)⁻¹ := by group
    have h2 : b₁⁻¹ * (a * b₁ * a⁻¹) ∈ L ⊓ L₂ :=
      ⟨L.mul_mem (L.inv_mem (borOf_le_left hb₁)) huL, by
        rw [h1]; exact L₂.mul_mem (borOf_le_left hb₂) (L₂.inv_mem hwL₂)⟩
    rw [hLL₂, Subgroup.mem_bot] at h2
    have hu1 : a * b₁ * a⁻¹ = b₁ := by
      calc a * b₁ * a⁻¹ = b₁ * (b₁⁻¹ * (a * b₁ * a⁻¹)) := by group
        _ = b₁ := by rw [h2, mul_one]
    have hw1 : a * b₂ * a⁻¹ = b₂ := by
      have : b₁ * (a * b₂ * a⁻¹) = b₁ * b₂ := by rw [hu1] at huw; exact huw
      exact mul_left_cancel this
    exact ⟨by calc b₁ * a = (a * b₁ * a⁻¹) * a := by rw [hu1]
                _ = a * b₁ := by group,
      by calc b₂ * a = (a * b₂ * a⁻¹) * a := by rw [hw1]
                _ = a * b₂ := by group⟩
  have hrelle : ∀ (hsub : V ⊓ Subgroup.centralizer (B' : Set G) ≤
      V ⊓ Subgroup.centralizer (L : Set G)),
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2 := fun hsub => by
    have hdvd := Subgroup.relIndex_dvd_of_le_left V hsub
    have hne : (V ⊓ Subgroup.centralizer (B' : Set G)).relIndex V ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hrel
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hb₁1 : b₁ = 1
  ·
    have hb₂1 : b₂ ≠ 1 := by
      intro hb₂1
      have : c = 1 := by rw [hcb, hb₁1, hb₂1, one_mul]
      rw [this, orderOf_one] at hc3
      omega
    have hb₂o : orderOf b₂ = 3 := orderOf_eq_prime hb₂3 hb₂1
    have hc₁B : q₀ * b₂ * q₀⁻¹ ∈ borOf T V L := (hmemB₂ b₂).1 hb₂
    have hc₁o : orderOf (q₀ * b₂ * q₀⁻¹) = 3 := by
      rw [← hb₂o]
      exact orderOf_injective (cg q₀) (MulAut.conj q₀).injective b₂
    have hW₀ : Nat.card ((blockU B').map (cg q₀)) ≤ 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj q₀).injective, hU4]
    have hcommd : ∀ d ∈ pgOf T V L, d * (q₀ * b₂ * q₀⁻¹) * d⁻¹ * (q₀ * b₂ * q₀⁻¹)⁻¹ ∈
        (blockU B').map (cg q₀) := by
      intro d hd
      have hd₂ : q₀⁻¹ * d * q₀ ∈ pgOf T V L₂ := by
        rw [hmemP₂, show q₀ * (q₀⁻¹ * d * q₀) * q₀⁻¹ = d by group]
        exact hd
      have h1 := hcomm _ (Subgroup.mem_sup_right hd₂)
      rw [hcb, hb₁1, one_mul] at h1
      refine ⟨_, h1, ?_⟩
      show q₀ * (q₀⁻¹ * d * q₀ * b₂ * (q₀⁻¹ * d * q₀)⁻¹ * b₂⁻¹) * q₀⁻¹ =
        d * (q₀ * b₂ * q₀⁻¹) * d⁻¹ * (q₀ * b₂ * q₀⁻¹)⁻¹
      group
    obtain ⟨hexc, hcent⟩ := comm_le_centralizer_of_exceptional hInn hmod h hU hL hZ2 hord hc₁B
      hc₁o hW₀ hcommd
    have hsub : V ⊓ Subgroup.centralizer (B' : Set G) ≤ V ⊓ Subgroup.centralizer (L : Set G) := by
      rintro a ⟨haV, haC⟩
      refine ⟨haV, hcent a haV ?_⟩
      have hac : c * a = a * c := Subgroup.mem_centralizer_iff.1 haC c hcB'
      have hb₂a : b₂ * a = a * b₂ := (hdecomp a haV hac).2
      have hqa : a * q₀ = q₀ * a := Subgroup.mem_centralizer_iff.1 hq₀.2 a haV
      have hqa' : q₀⁻¹ * a = a * q₀⁻¹ := by
        calc q₀⁻¹ * a = q₀⁻¹ * (a * q₀) * q₀⁻¹ := by group
          _ = q₀⁻¹ * (q₀ * a) * q₀⁻¹ := by rw [hqa]
          _ = a * q₀⁻¹ := by group
      calc q₀ * b₂ * q₀⁻¹ * a = q₀ * b₂ * (q₀⁻¹ * a) := by group
        _ = q₀ * b₂ * (a * q₀⁻¹) := by rw [hqa']
        _ = q₀ * (b₂ * a) * q₀⁻¹ := by group
        _ = q₀ * (a * b₂) * q₀⁻¹ := by rw [hb₂a]
        _ = (q₀ * a) * b₂ * q₀⁻¹ := by group
        _ = (a * q₀) * b₂ * q₀⁻¹ := by rw [hqa]
        _ = a * (q₀ * b₂ * q₀⁻¹) := by group
    exact ⟨by rw [← card_sylowBar_of_center_eq_bot hZ0L]; exact hexc.1, hrelle hsub⟩
  ·
    have hb₁o : orderOf b₁ = 3 := orderOf_eq_prime hb₁3 hb₁1
    have hcommd : ∀ d ∈ pgOf T V L, d * b₁ * d⁻¹ * b₁⁻¹ ∈ blockU B' := by
      intro d hd
      have h1 := hcomm d (Subgroup.mem_sup_left hd)
      have hcd : Commute d b₂ := hcommLL d (pgOf_le_left hd) b₂ (borOf_le_left hb₂)
      have h3' : b₂ * d⁻¹ = d⁻¹ * b₂ := hcd.inv_left.eq.symm
      have e : d * c * d⁻¹ * c⁻¹ = d * b₁ * d⁻¹ * b₁⁻¹ := by
        rw [hcb]
        calc d * (b₁ * b₂) * d⁻¹ * (b₁ * b₂)⁻¹ = d * b₁ * (b₂ * d⁻¹) * b₂⁻¹ * b₁⁻¹ := by group
          _ = d * b₁ * (d⁻¹ * b₂) * b₂⁻¹ * b₁⁻¹ := by rw [h3']
          _ = d * b₁ * d⁻¹ * b₁⁻¹ := by group
      rwa [e] at h1
    obtain ⟨hexc, hcent⟩ := comm_le_centralizer_of_exceptional hInn hmod h hU hL hZ2 hord hb₁
      hb₁o (W₀ := blockU B') (by rw [hU4]) hcommd
    have hsub : V ⊓ Subgroup.centralizer (B' : Set G) ≤ V ⊓ Subgroup.centralizer (L : Set G) := by
      rintro a ⟨haV, haC⟩
      exact ⟨haV, hcent a haV (hdecomp a haV (Subgroup.mem_centralizer_iff.1 haC c hcB')).1⟩
    exact ⟨by rw [← card_sylowBar_of_center_eq_bot hZ0L]; exact hexc.1, hrelle hsub⟩

end Swap

end E68Proof

end E6

end CFSG.Quasithin
