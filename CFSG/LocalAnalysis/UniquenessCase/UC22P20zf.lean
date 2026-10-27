module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.ConclAt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22pwc_not_three_five (k : ℕ) (h3 : 3 ∣ 2 ^ k + 1) (h5 : 5 ∣ 2 ^ k + 1) : False := by
  have h : ∀ j : ℕ, 2 ^ j % 15 = 1 ∨ 2 ^ j % 15 = 2 ∨ 2 ^ j % 15 = 4 ∨ 2 ^ j % 15 = 8 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ]; omega
  have := h k
  omega

theorem uc22pwc_even_of_three_dvd {m : ℕ} (h : 3 ∣ 2 ^ m - 1) : Even m := by
  have key : ∀ j : ℕ, 2 ^ j % 3 = if j % 2 = 0 then 1 else 2 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ]; split_ifs at ih ⊢ <;> omega
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hk := key m
  rw [Nat.even_iff]
  split_ifs at hk with hm
  · exact hm
  · omega

theorem uc22pwc_eq_of_sq_eq_one {C : Type} [Group C] [IsCyclic C] {a b : C} (ha : a ^ 2 = 1) (ha1 : a ≠ 1)
    (hb : b ^ 2 = 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
  have h2 : ∀ k : ℤ, (g ^ k) ^ 2 = g ^ (2 * k) := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  rw [h2, ← orderOf_dvd_iff_zpow_eq_one] at ha hb
  rw [Ne, ← orderOf_dvd_iff_zpow_eq_one] at ha1 hb1
  rw [zpow_eq_zpow_iff_modEq, Int.modEq_iff_dvd]
  obtain ⟨q, hq⟩ := ha
  obtain ⟨r, hr⟩ := hb
  have hodd : ∀ {k s : ℤ}, 2 * k = (orderOf g : ℤ) * s → ¬ (orderOf g : ℤ) ∣ k → Odd s := by
    intro k s hks hnd
    rcases Int.even_or_odd s with ⟨s', hs'⟩ | hs
    · refine absurd ⟨s', mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) ?_⟩ hnd
      rw [hks, hs']
      ring
    · exact hs
  obtain ⟨a', ha'⟩ := hodd hq ha1
  obtain ⟨b', hb'⟩ := hodd hr hb1
  refine ⟨b' - a', mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) ?_⟩
  linear_combination hr - hq + (orderOf g : ℤ) * hb' - (orderOf g : ℤ) * ha'

theorem uc22pwc_pow_alike {H : Type} [Group H] (ρ : MulAut H) (F : Subgroup H) {k l : ℕ}
    (hk : ∀ x, x ∈ F ↔ (ρ ^ k) x ∈ F) (hl : ∀ x, x ∈ F ↔ (ρ ^ l) x ∈ F)
    (hk2 : ∀ x ∈ F, (ρ ^ k) ((ρ ^ k) x) = x) (hk1 : ∃ x ∈ F, (ρ ^ k) x ≠ x)
    (hl2 : ∀ x ∈ F, (ρ ^ l) ((ρ ^ l) x) = x) (hl1 : ∃ x ∈ F, (ρ ^ l) x ≠ x) :
    ∀ x ∈ F, (ρ ^ k) x = (ρ ^ l) x := by
  let K : Subgroup (MulAut H) := zpowers ρ ⊓ uc22pwtStab (MonoidHom.id (MulAut H)) F
  haveI : IsCyclic K := Subgroup.isCyclic_of_le inf_le_left
  let r : K →* MulAut F :=
    (uc22pwtRes (MonoidHom.id (MulAut H)) F).comp (Subgroup.inclusion inf_le_right)
  haveI : IsCyclic r.range := isCyclic_of_surjective r.rangeRestrict r.rangeRestrict_surjective
  have hr : ∀ (g : K) (x : F), (((r.rangeRestrict g : r.range) : MulAut F) x : H) = (g : MulAut H) x :=
    fun _ _ => rfl
  have hsq : ∀ g : K, (∀ x ∈ F, (g : MulAut H) ((g : MulAut H) x) = x) → (r.rangeRestrict g) ^ 2 = 1 := by
    intro g hg
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two, MulAut.mul_apply]
    exact (hr g _).trans (by rw [hr g x]; exact hg x x.2)
  have hne : ∀ g : K, (∃ x ∈ F, (g : MulAut H) x ≠ x) → r.rangeRestrict g ≠ 1 := by
    rintro g ⟨x, hx, hgx⟩ h1
    apply hgx
    have h := congrArg (fun c : r.range => (((c : MulAut F) ⟨x, hx⟩ : F) : H)) h1
    exact (hr g ⟨x, hx⟩).symm.trans h
  let gk : K := ⟨ρ ^ k, Subgroup.pow_mem _ (mem_zpowers ρ) k, hk⟩
  let gl : K := ⟨ρ ^ l, Subgroup.pow_mem _ (mem_zpowers ρ) l, hl⟩
  have hab := uc22pwc_eq_of_sq_eq_one (hsq gk hk2) (hne gk hk1) (hsq gl hl2) (hne gl hl1)
  intro x hx
  have h := congrArg (fun c : r.range => (((c : MulAut F) ⟨x, hx⟩ : F) : H)) hab
  exact (hr gk ⟨x, hx⟩).symm.trans (h.trans (hr gl ⟨x, hx⟩))

theorem uc22pwc_alike_of_shape {X : Type} [Group X] {U : Subgroup X} {P : Type} [Group P]
    {ψ : P →* MulAut X} {H : Type} [Group H] {ι : H →* X} (hι : Function.Injective ι)
    (hιU : ∀ t : H, ι t ∈ U → t = 1) {ρ : MulAut H} {g₁ g₂ : P} {m₁ m₂ : ℕ}
    (h₁ : ∀ t : H, ψ g₁ (ι t) * (ι ((ρ ^ m₁) t))⁻¹ ∈ U)
    (h₂ : ∀ t : H, ψ g₂ (ι t) * (ι ((ρ ^ m₂) t))⁻¹ ∈ U) {F : Subgroup X} (hFι : F ≤ ι.range)
    (hF₁ : ∀ x ∈ F, ψ g₁ x ∈ F) (hF₂ : ∀ x ∈ F, ψ g₂ x ∈ F)
    (hi₁ : ∀ x ∈ F, ψ g₁ (ψ g₁ x) = x) (hn₁ : ∃ x ∈ F, ψ g₁ x ≠ x)
    (hi₂ : ∀ x ∈ F, ψ g₂ (ψ g₂ x) = x) (hn₂ : ∃ x ∈ F, ψ g₂ x ≠ x) :
    ∀ x ∈ F, ψ g₁ x = ψ g₂ x := by
  have facts : ∀ (g : P) (m : ℕ), (∀ t : H, ψ g (ι t) * (ι ((ρ ^ m) t))⁻¹ ∈ U) →
      (∀ x ∈ F, ψ g x ∈ F) → (∀ x ∈ F, ψ g (ψ g x) = x) → (∃ x ∈ F, ψ g x ≠ x) →
      (∀ t : H, ι t ∈ F → ψ g (ι t) = ι ((ρ ^ m) t)) ∧
        (∀ t : H, t ∈ F.comap ι ↔ (ρ ^ m) t ∈ F.comap ι) ∧
        (∀ t ∈ F.comap ι, (ρ ^ m) ((ρ ^ m) t) = t) ∧ ∃ t ∈ F.comap ι, (ρ ^ m) t ≠ t := by
    intro g m hsh hF hi hn
    have hkey : ∀ t : H, ι t ∈ F → ψ g (ι t) = ι ((ρ ^ m) t) := by
      intro t ht
      obtain ⟨s, hs⟩ := hFι (hF (ι t) ht)
      have h1 : ι (s * ((ρ ^ m) t)⁻¹) ∈ U := by
        rw [map_mul, map_inv, hs]
        exact hsh t
      have h2 : s = (ρ ^ m) t := mul_inv_eq_one.1 (hιU _ h1)
      rw [← hs, h2]
    have hfwd : ∀ t : H, ι t ∈ F → ι ((ρ ^ m) t) ∈ F := fun t ht => hkey t ht ▸ hF _ ht
    have hinv : ∀ t : H, ι t ∈ F → (ρ ^ m) ((ρ ^ m) t) = t := fun t ht =>
      hι (by rw [← hkey _ (hfwd t ht), ← hkey t ht]; exact hi _ ht)
    refine ⟨hkey, fun t => ⟨hfwd t, fun ht => ?_⟩, hinv, ?_⟩
    · have h1 := hfwd _ ht
      have h3 : (ρ ^ m) ((ρ ^ m) t) = t := (ρ ^ m).injective (hinv _ ht)
      rw [h3] at h1
      exact h1
    · obtain ⟨x, hx, hne⟩ := hn
      obtain ⟨t, rfl⟩ := hFι hx
      exact ⟨t, hx, fun h => hne (by rw [hkey t hx, h])⟩
  obtain ⟨k₁, s₁, i₁, n₁⟩ := facts g₁ m₁ h₁ hF₁ hi₁ hn₁
  obtain ⟨k₂, s₂, i₂, n₂⟩ := facts g₂ m₂ h₂ hF₂ hi₂ hn₂
  have hA := uc22pwc_pow_alike ρ (F.comap ι) s₁ s₂ i₁ n₁ i₂ n₂
  intro x hx
  obtain ⟨t, rfl⟩ := hFι hx
  rw [k₁ t hx, k₂ t hx, hA t hx]

theorem uc22pwc_eq_one_of_odd {X H : Type} [Group X] [Group H] [Finite H] {U : Subgroup X}
    (hU : IsPGroup 2 U) {ι : H →* X} (hι : Function.Injective ι) (hodd : Odd (Nat.card H)) {t : H}
    (ht : ι t ∈ U) : t = 1 := by
  obtain ⟨k, hk⟩ := hU ⟨ι t, ht⟩
  have h1 : ι (t ^ 2 ^ k) = ι 1 := by
    rw [map_pow, map_one]
    simpa using congrArg Subtype.val hk
  have h2 : t ^ 2 ^ k = 1 := hι h1
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one (pow_card_eq_one' (x := t)))
  rw [(Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)).gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem uc22pwc_alike_of_gal {X : Type} [Group X] [Finite X] {U E : Subgroup X} (hU : IsPGroup 2 U)
    (hEab : IsMulCommutative E) (hEodd : Odd (Nat.card E)) {P : Type} [Group P] {ψ : P →* MulAut X}
    (hG : uc22pwlie_Gal U E ψ) {F : Subgroup X} (hFE : F ≤ E) {g₁ g₂ : P}
    (hF₁ : ∀ x ∈ F, ψ g₁ x ∈ F) (hF₂ : ∀ x ∈ F, ψ g₂ x ∈ F)
    (hi₁ : ∀ x ∈ F, ψ g₁ (ψ g₁ x) = x) (hn₁ : ∃ x ∈ F, ψ g₁ x ≠ x)
    (hi₂ : ∀ x ∈ F, ψ g₂ (ψ g₂ x) = x) (hn₂ : ∃ x ∈ F, ψ g₂ x ≠ x) :
    ∀ x ∈ F, ψ g₁ x = ψ g₂ x := by
  have hcomm : ∀ x y : E, x * y = y * x := fun x y =>
    Subtype.ext (Subgroup.mul_comm_of_mem_isMulCommutative E x.2 y.2)
  let sq : E →* E :=
    { toFun := fun x => x ^ 2
      map_one' := one_pow 2
      map_mul' := fun x y => (Commute.mul_pow (hcomm x y) 2) }
  have hinj : Function.Injective sq := by
    intro x y hxy
    have h1 : (x * y⁻¹) ^ 2 = 1 := by
      rw [(Commute.mul_pow (hcomm x y⁻¹) 2)]
      change x ^ 2 = y ^ 2 at hxy
      rw [hxy, inv_pow, mul_inv_cancel]
    have h2 : (x * y⁻¹) ^ Nat.card E = 1 := pow_card_eq_one'
    have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [(Nat.coprime_two_left.2 hEodd).gcd_eq_one] at h3
    exact mul_inv_eq_one.1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3))
  let ρ : MulAut E := MulEquiv.ofBijective sq ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have hρ : ∀ (i : ℕ) (x : E), (ρ ^ i) x = x ^ 2 ^ i := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih]
      change (x ^ 2) ^ 2 ^ i = x ^ 2 ^ (i + 1)
      rw [← pow_mul, pow_succ, mul_comm]
  have hshape : ∀ g : P, ∃ m : ℕ, ∀ t : E, ψ g (E.subtype t) * (E.subtype ((ρ ^ m) t))⁻¹ ∈ U := by
    intro g
    obtain ⟨i, hi⟩ := hG g
    refine ⟨i, fun t => ?_⟩
    rw [hρ]
    exact hi t t.2
  obtain ⟨m₁, h₁⟩ := hshape g₁
  obtain ⟨m₂, h₂⟩ := hshape g₂
  exact uc22pwc_alike_of_shape E.subtype_injective
    (fun t ht => Subtype.ext (uc22pws_eq_one_of_mem_inf hU hEodd t.2 ht)) h₁ h₂
    (hFE.trans (by rw [Subgroup.range_subtype])) hF₁ hF₂ hi₁ hn₁ hi₂ hn₂

theorem uc22pwc_alike_of_rshape {X : Type} [Group X] {U E : Subgroup X} (hU : IsPGroup 2 U) {P : Type}
    [Group P] {ψ : P →* MulAut X} (hR : uc22pwlie_RShape U E ψ) {F : Subgroup X} (hFE : F ≤ E) {g₁ g₂ : P}
    (hF₁ : ∀ x ∈ F, ψ g₁ x ∈ F) (hF₂ : ∀ x ∈ F, ψ g₂ x ∈ F)
    (hi₁ : ∀ x ∈ F, ψ g₁ (ψ g₁ x) = x) (hn₁ : ∃ x ∈ F, ψ g₁ x ≠ x)
    (hi₂ : ∀ x ∈ F, ψ g₂ (ψ g₂ x) = x) (hn₂ : ∃ x ∈ F, ψ g₂ x ≠ x) :
    ∀ x ∈ F, ψ g₁ x = ψ g₂ x := by
  obtain ⟨H, _, _, ι, ρ, hι, hodd, -, hEι, -, hsh⟩ := hR
  obtain ⟨m₁, h₁⟩ := hsh g₁
  obtain ⟨m₂, h₂⟩ := hsh g₂
  exact uc22pwc_alike_of_shape hι (fun t ht => uc22pwc_eq_one_of_odd hU hι hodd ht) h₁ h₂ (hFE.trans hEι)
    hF₁ hF₂ hi₁ hn₁ hi₂ hn₂

theorem uc22pwc_not_inv35_of_gal {X : Type} [Group X] [Finite X] {U E : Subgroup X} (hU : IsPGroup 2 U)
    (hEodd : Odd (Nat.card E)) {P : Type} [Group P] {ψ : P →* MulAut X} (hG : uc22pwlie_Gal U E ψ) (g : P)
    {x₃ x₅ : X} (h₃ : x₃ ∈ E) (h₅ : x₅ ∈ E) (ho₃ : orderOf x₃ = 3) (ho₅ : orderOf x₅ = 5)
    (hi₃ : ψ g x₃ * x₃ ∈ U) (hi₅ : ψ g x₅ * x₅ ∈ U) : False := by
  obtain ⟨i, hi⟩ := hG g
  have key : ∀ x ∈ E, ψ g x * x ∈ U → orderOf x ∣ 2 ^ i + 1 := by
    intro x hx hxU
    have h1 : x ^ 2 ^ i * x ∈ U := by
      have := U.mul_mem (U.inv_mem (hi x hx)) hxU
      rwa [show (ψ g x * (x ^ 2 ^ i)⁻¹)⁻¹ * (ψ g x * x) = x ^ 2 ^ i * x by group] at this
    have h2 := uc22pws_eq_one_of_mem_inf hU hEodd (E.mul_mem (E.pow_mem hx _) hx) h1
    rw [← pow_succ] at h2
    exact orderOf_dvd_of_pow_eq_one h2
  exact uc22pwc_not_three_five i (ho₃ ▸ key x₃ h₃ hi₃) (ho₅ ▸ key x₅ h₅ hi₅)

theorem uc22pwc_not_inv35_of_rshape {X : Type} [Group X] {U E : Subgroup X} (hU : IsPGroup 2 U) {P : Type}
    [Group P] {ψ : P →* MulAut X} (hR : uc22pwlie_RShape U E ψ) (g : P) {x₃ x₅ : X} (h₃ : x₃ ∈ E)
    (h₅ : x₅ ∈ E) (ho₃ : orderOf x₃ = 3) (ho₅ : orderOf x₅ = 5) (hi₃ : ψ g x₃ * x₃ ∈ U)
    (hi₅ : ψ g x₅ * x₅ ∈ U) : False := by
  obtain ⟨H, _, _, ι, ρ, hι, hodd, -, hEι, hρ, hsh⟩ := hR
  obtain ⟨m, hm⟩ := hsh g
  have key : ∀ t : H, ψ g (ι t) * ι t ∈ U → (ρ ^ m) t = t⁻¹ := by
    intro t ht
    have h1 : ι ((ρ ^ m) t * t) ∈ U := by
      have := U.mul_mem (U.inv_mem (hm t)) ht
      rw [map_mul]
      rwa [show (ψ g (ι t) * (ι ((ρ ^ m) t))⁻¹)⁻¹ * (ψ g (ι t) * ι t) = ι ((ρ ^ m) t) * ι t by
        group] at this
    exact eq_inv_of_mul_eq_one_left (uc22pwc_eq_one_of_odd hU hι hodd h1)
  have hpow : ∀ (k : ℕ) (t : H), (ρ ^ (2 * k)) t = t ^ 2 ^ k := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [Nat.mul_succ, pow_add, MulAut.mul_apply, pow_two, MulAut.mul_apply, hρ, ih, ← pow_mul, pow_succ,
        mul_comm]
  obtain ⟨t₃, rfl⟩ := hEι h₃
  obtain ⟨t₅, rfl⟩ := hEι h₅
  have ho₃' : orderOf t₃ = 3 := by rw [← orderOf_injective ι hι t₃]; exact ho₃
  have ho₅' : orderOf t₅ = 5 := by rw [← orderOf_injective ι hι t₅]; exact ho₅
  have k₃ := key t₃ hi₃
  have k₅ := key t₅ hi₅
  have hfix : t₃ ^ 2 ^ m = t₃ := by
    rw [← hpow, two_mul, pow_add, MulAut.mul_apply, k₃, map_inv, k₃, inv_inv]
  have hm3 : 3 ∣ 2 ^ m - 1 := by
    rw [← ho₃']
    refine orderOf_dvd_of_pow_eq_one ?_
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h2 : t₃ ^ (2 ^ m - 1) * t₃ = t₃ := by rw [← pow_succ, Nat.sub_add_cancel h1, hfix]
    exact (mul_eq_right.1 h2)
  obtain ⟨k, hk⟩ := uc22pwc_even_of_three_dvd hm3
  rw [hk, ← two_mul] at k₃ k₅
  rw [hpow] at k₃ k₅
  have hd : ∀ t : H, t ^ 2 ^ k = t⁻¹ → orderOf t ∣ 2 ^ k + 1 := fun t ht =>
    orderOf_dvd_of_pow_eq_one (by rw [pow_succ, ht, inv_mul_cancel])
  exact uc22pwc_not_three_five k (ho₃' ▸ hd t₃ k₃) (ho₅' ▸ hd t₅ k₅)

end CFSG.LocalAnalysis.UniquenessCase.UC22
