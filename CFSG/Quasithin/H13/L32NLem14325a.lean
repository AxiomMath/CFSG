module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG.Quasithin.H13.L14325

open CFSG.Open

theorem perm_eq_one_of_pow_prime {α : Type*} [Finite α] {p k : ℕ} (hp : p.Prime)
    (hcard : Nat.card α < p) {σ : Equiv.Perm α} (hσ : σ ^ (p ^ k) = 1) : σ = 1 := by
  have h1 : orderOf σ ∣ p ^ k := orderOf_dvd_of_pow_eq_one hσ
  have h2 : orderOf σ ∣ (Nat.card α).factorial := by
    rw [← Nat.card_perm]
    exact orderOf_dvd_natCard σ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact orderOf_eq_one_iff.mp (by rw [hj, pow_zero])
  · rw [hj] at h2
    exact absurd ((Nat.Prime.dvd_factorial hp).mp ((dvd_pow_self p hj0.ne').trans h2))
      (by omega)

theorem smul_eq_of_pow_prime {M β : Type*} [Monoid M] [MulAction M β] {g : M} {S : Set β}
    [Finite S] {p k : ℕ} (hp : p.Prime) (hcard : Nat.card S < p) (hS : ∀ b ∈ S, g • b ∈ S)
    (hgp : ∀ b ∈ S, g ^ (p ^ k) • b = b) : ∀ b ∈ S, g • b = b := by
  have hpow : ∀ n : ℕ, ∀ b ∈ S, g ^ n • b ∈ S := by
    intro n
    induction n with
    | zero => intro b hb; rwa [pow_zero, one_smul]
    | succ n ih => intro b hb; rw [pow_succ', mul_smul]; exact hS _ (ih b hb)
  have hp1 : p ^ k - 1 + 1 = p ^ k := Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)
  let σ : Equiv.Perm S :=
    { toFun := fun b => ⟨g • (b : β), hS _ b.2⟩
      invFun := fun b => ⟨g ^ (p ^ k - 1) • (b : β), hpow _ _ b.2⟩
      left_inv := fun b => Subtype.ext (by
        show g ^ (p ^ k - 1) • g • (b : β) = b
        rw [← mul_smul, ← pow_succ, hp1, hgp _ b.2])
      right_inv := fun b => Subtype.ext (by
        show g • g ^ (p ^ k - 1) • (b : β) = b
        rw [← mul_smul, ← pow_succ', hp1, hgp _ b.2]) }
  have hσn : ∀ n : ℕ, ∀ b : S, ((σ ^ n) b : β) = g ^ n • (b : β) := by
    intro n
    induction n with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', mul_smul, ← ih]
      rfl
  have hσp : σ ^ (p ^ k) = 1 := Equiv.ext fun b => Subtype.ext (by
    rw [hσn, hgp _ b.2]
    rfl)
  have h1 := perm_eq_one_of_pow_prime hp hcard hσp
  intro b hb
  have := congrArg Subtype.val (Equiv.ext_iff.mp h1 ⟨b, hb⟩)
  exact this

variable {G : Type*} [Group G]

theorem centralizes_of_pow_five [Finite G] {W C : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1)
    (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hidx : C.relIndex W ≤ 4) {s : G} {k : ℕ}
    (hsW : ∀ w ∈ W, s * w * s⁻¹ ∈ W) (hs5 : ∀ w ∈ W, s ^ (5 ^ k) * w * (s ^ (5 ^ k))⁻¹ = w)
    (hsC : ∀ c ∈ C, s * c * s⁻¹ = c) : ∀ w ∈ W, s * w * s⁻¹ = w := by
  have hmemδ : ∀ w ∈ W, s * w * s⁻¹ * w⁻¹ ∈ W := fun w hw => W.mul_mem (hsW w hw) (W.inv_mem hw)
  let δ : ↥W →* ↥W :=
    { toFun := fun w => ⟨s * w * s⁻¹ * (w : G)⁻¹, hmemδ w w.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun v w => Subtype.ext (by
        show s * ((v : G) * w) * s⁻¹ * ((v : G) * w)⁻¹ =
          s * v * s⁻¹ * (v : G)⁻¹ * (s * w * s⁻¹ * (w : G)⁻¹)
        have h1 := hWc _ (W.inv_mem v.2) _ (hmemδ w w.2)
        calc s * ((v : G) * w) * s⁻¹ * ((v : G) * w)⁻¹
            = s * v * s⁻¹ * ((s * w * s⁻¹ * (w : G)⁻¹) * (v : G)⁻¹) := by group
          _ = s * v * s⁻¹ * ((v : G)⁻¹ * (s * w * s⁻¹ * (w : G)⁻¹)) := by rw [← h1]
          _ = s * v * s⁻¹ * (v : G)⁻¹ * (s * w * s⁻¹ * (w : G)⁻¹) := by group) }
  have hδ : ∀ w : ↥W, ((δ w : ↥W) : G) = s * w * s⁻¹ * (w : G)⁻¹ := fun _ => rfl
  have hker : C.subgroupOf W ≤ δ.ker := by
    intro w hw
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hδ, hsC _ (Subgroup.mem_subgroupOf.mp hw)]
    simp
  have hcard : Nat.card δ.range ≤ 4 := by
    rw [← Subgroup.index_ker]
    have h1 := Subgroup.index_antitone hker
    have h2 : (C.subgroupOf W).index = C.relIndex W := rfl
    omega
  set S : Set G := (δ.range.map W.subtype : Set G) with hS
  have : Finite S := Set.Finite.to_subtype (Set.toFinite S)
  have hcardS : Nat.card S < 5 := by
    have : Nat.card S = Nat.card δ.range :=
      Nat.card_congr (Subgroup.equivMapOfInjective δ.range W.subtype
        W.subtype_injective).toEquiv.symm
    omega
  have hSmem : ∀ w : ↥W, (δ w : G) ∈ S := fun w => ⟨δ w, ⟨w, rfl⟩, rfl⟩
  have hSW : ∀ x ∈ S, ∃ w : ↥W, x = δ w := by
    rintro x ⟨y, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, rfl⟩
  have hconjδ : ∀ w : ↥W, s * (δ w : G) * s⁻¹ = δ ⟨s * w * s⁻¹, hsW w w.2⟩ := by
    intro w
    rw [hδ, hδ]
    group
  have hfix := smul_eq_of_pow_prime (g := ConjAct.toConjAct s) (S := S) Nat.prime_five hcardS
    (fun x hx => by
      obtain ⟨w, rfl⟩ := hSW x hx
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hconjδ]
      exact hSmem _)
    (fun x hx => by
      rw [← map_pow, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
      obtain ⟨w, rfl⟩ := hSW x hx
      exact hs5 _ (δ w).2)
  have hδfix : ∀ w : ↥W, s * (δ w : G) * s⁻¹ = δ w := by
    intro w
    have := hfix _ (hSmem w)
    rwa [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at this
  have hs2 : ∀ w ∈ W, s ^ 2 * w * (s ^ 2)⁻¹ = w := by
    intro w hw
    have e1 : s * w * s⁻¹ = (δ ⟨w, hw⟩ : G) * w := by rw [hδ]; group
    have e2 := hδfix ⟨w, hw⟩
    have e3 : (δ ⟨w, hw⟩ : G) * (δ ⟨w, hw⟩ : G) = 1 := hW2 _ (δ ⟨w, hw⟩).2
    calc s ^ 2 * w * (s ^ 2)⁻¹ = s * (s * w * s⁻¹) * s⁻¹ := by rw [sq, mul_inv_rev]; group
      _ = s * ((δ ⟨w, hw⟩ : G) * w) * s⁻¹ := by rw [e1]
      _ = (s * (δ ⟨w, hw⟩ : G) * s⁻¹) * (s * w * s⁻¹) := by group
      _ = (δ ⟨w, hw⟩ : G) * ((δ ⟨w, hw⟩ : G) * w) := by rw [e2, e1]
      _ = w := by rw [← mul_assoc, e3, one_mul]
  have hpow2 : ∀ j : ℕ, ∀ w ∈ W, (s ^ 2) ^ j * w * ((s ^ 2) ^ j)⁻¹ = w := by
    intro j
    induction j with
    | zero => intro w _; simp
    | succ j ih =>
      intro w hw
      calc (s ^ 2) ^ (j + 1) * w * ((s ^ 2) ^ (j + 1))⁻¹
          = (s ^ 2) ^ j * (s ^ 2 * w * (s ^ 2)⁻¹) * ((s ^ 2) ^ j)⁻¹ := by group
        _ = w := by rw [hs2 w hw, ih w hw]
  obtain ⟨j, hj⟩ : ∃ j, 5 ^ k = 2 * j + 1 := Odd.exists_bit1 (Odd.pow (by decide))
  intro w hw
  have hw' : ((s ^ 2) ^ j)⁻¹ * w * (s ^ 2) ^ j = w := by
    calc ((s ^ 2) ^ j)⁻¹ * w * (s ^ 2) ^ j
        = ((s ^ 2) ^ j)⁻¹ * ((s ^ 2) ^ j * w * ((s ^ 2) ^ j)⁻¹) * (s ^ 2) ^ j := by
          rw [hpow2 j w hw]
      _ = w := by group
  have hsk : s ^ (5 ^ k) = s * (s ^ 2) ^ j := by
    rw [hj, ← pow_mul, pow_succ, mul_comm]
    exact (Commute.self_pow s _).eq.symm
  calc s * w * s⁻¹ = s ^ (5 ^ k) * (((s ^ 2) ^ j)⁻¹ * w * (s ^ 2) ^ j) * (s ^ (5 ^ k))⁻¹ := by
        rw [hsk]; group
    _ = w := by rw [hw', hs5 w hw]

omit [Group G] in
theorem mem_of_normal_of_not_dvd_relIndex [Group G] {N M : Subgroup G}
    (hN : (N.subgroupOf M).Normal) {p : ℕ} (hp : p.Prime) (hidx : ¬ p ∣ N.relIndex M) {x : G}
    (hx : x ∈ M) {k : ℕ} (hk : x ^ (p ^ k) = 1) : x ∈ N := by
  have := hN
  let x' : M := ⟨x, hx⟩
  let q : M ⧸ N.subgroupOf M := QuotientGroup.mk x'
  have h1 : q ^ (p ^ k) = 1 := by
    change QuotientGroup.mk (x' ^ (p ^ k)) = 1
    have : x' ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this]
    rfl
  have h2 : orderOf q ∣ N.relIndex M := orderOf_dvd_natCard q
  have h3 : orderOf q ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (p ^ k) (N.relIndex M) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hidx)
  have h4 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 h2
  have h5 : q = 1 := orderOf_eq_one_iff.mp h4
  exact (QuotientGroup.eq_one_iff x').1 h5

omit [Group G] in
theorem le_of_isSubnormal [Group G] {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K :=
  h.le

theorem mem_of_subnormal_of_pow_eq_one {H K : Subgroup G} (h : IsSubnormal H K) {p : ℕ}
    (hp : p.Prime) (hidx : ¬ p ∣ H.relIndex K) {x : G} (hxK : x ∈ K) {k : ℕ}
    (hk : x ^ (p ^ k) = 1) : x ∈ H := by
  induction h with
  | refl => exact hxK
  | @step H M K hHM hN hMK ih =>
    have hMK' : M ≤ K := le_of_isSubnormal hMK
    have hmul := Subgroup.relIndex_mul_relIndex H M K hHM hMK'
    have hHM' : ¬ p ∣ H.relIndex M := fun hd => hidx (hmul ▸ Dvd.dvd.mul_right hd _)
    have hMK'' : ¬ p ∣ M.relIndex K := fun hd => hidx (hmul ▸ Dvd.dvd.mul_left hd _)
    exact mem_of_normal_of_not_dvd_relIndex hN hp hHM' (ih hMK'' hxK) hk

end CFSG.Quasithin.H13.L14325
