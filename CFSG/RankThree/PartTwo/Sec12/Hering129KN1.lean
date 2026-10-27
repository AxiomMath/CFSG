module

public import CFSG.Assembly.Defs
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec12

@[expose] def commSubgroup {Q : Type} [Group Q] (τ : Q ≃* Q) : Subgroup Q :=
  Subgroup.closure {q | ∃ y : Q, q = y * (τ y)⁻¹}

@[expose] def EndLocalX {X : Type} [Group X] (U : Subgroup X) (x t c : X) : Prop :=
  ∃ (S : Subgroup X) (hcS : c ∈ S) (Q : Type) (_ : Group Q) (_ : Finite Q) (ρ : ↥S →* Q)
    (τ : Q ≃* Q), S ≤ U ∧ (∀ s ∈ S, x * s = s * x) ∧ (∀ s ∈ S, c * s = s * c) ∧
    (∀ s ∈ S, t * s * t⁻¹ ∈ S) ∧ Function.Surjective ρ ∧ ¬ 3 ∣ Nat.card ρ.ker ∧
    (∀ (s : ↥S) (hs : t * (s : X) * t⁻¹ ∈ S), ρ ⟨t * s * t⁻¹, hs⟩ = τ (ρ s)) ∧
    Nat.card (commSubgroup τ) = 9 ∧
    (∀ v ∈ commSubgroup τ, ∀ w ∈ commSubgroup τ, v * w = w * v) ∧
    (∀ v ∈ commSubgroup τ, v ^ 3 = 1) ∧ (∀ v ∈ commSubgroup τ, τ v = v⁻¹) ∧
    ρ ⟨c, hcS⟩ ∈ commSubgroup τ

namespace Hering129KN1

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {g : G} {p : ℕ} (h : g ^ p = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  rintro ⟨y, hy⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem conj_inv_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) : ∀ h ∈ H, g⁻¹ * h * g ∈ H := by
  have hk : ∀ k : ℕ, ∀ h ∈ H, g ^ k * h * (g ^ k)⁻¹ ∈ H := by
    intro k
    induction k with
    | zero => intro h hh; simpa using hh
    | succ k ih =>
      intro h hh
      have h1 := hg _ (ih h hh)
      rw [pow_succ']
      simpa only [mul_inv_rev, mul_assoc] using h1
  intro h hh
  have hn : g ^ (orderOf g - 1) = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos g),
      pow_orderOf_eq_one]
  simpa only [hn, inv_inv] using hk (orderOf g - 1) h hh

open scoped Pointwise in
theorem exists_inv_mul_conj_mem {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (P : Sylow p H) {g : G} (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) :
    ∃ n ∈ H, ∀ v ∈ (P : Subgroup H).map H.subtype,
      n⁻¹ * (g * v * g⁻¹) * n ∈ (P : Subgroup H).map H.subtype := by
  have hg' := conj_inv_mem hg
  let σ : MulAut H :=
    { toFun := fun h => ⟨g * h * g⁻¹, hg h h.2⟩
      invFun := fun h => ⟨g⁻¹ * h * g, hg' h h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hσ : ∀ h : H, ((σ h : H) : G) = g * h * g⁻¹ := fun h => rfl
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq H P (σ • P)
  refine ⟨n, n.2, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have h1 : σ • w ∈ ((σ • P : Sylow p H) : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul w σ (P : Subgroup H) hw
  rw [← hn, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  refine ⟨_, h1, ?_⟩
  rw [MulAut.smul_def, MulAut.conj_inv_apply, MulAut.smul_def]
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hσ]

theorem exists_odd_pow_isPGroup_two {G : Type*} [Group G] [Finite G] (u : G) :
    ∃ k : ℕ, Odd k ∧ IsPGroup 2 (Subgroup.zpowers (u ^ k)) := by
  obtain ⟨s, m, hm, hsm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos u).ne'
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  refine ⟨m, hm, IsPGroup.of_card (n := s) ?_⟩
  rw [Nat.card_zpowers, orderOf_pow_of_dvd hm0 (by rw [hsm]; exact Dvd.intro_left _ rfl), hsm,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

theorem odd_pow_conj_eq_inv {G : Type*} [Group G] {u v : G} (h : u * v * u⁻¹ = v⁻¹) {k : ℕ}
    (hk : Odd k) : u ^ k * v * (u ^ k)⁻¹ = v⁻¹ := by
  have h2 : Commute (u ^ 2) v := by
    have h3 : u ^ 2 * v * (u ^ 2)⁻¹ = v := by
      calc u ^ 2 * v * (u ^ 2)⁻¹ = u * (u * v * u⁻¹) * u⁻¹ := by rw [sq]; group
        _ = u * v⁻¹ * u⁻¹ := by rw [h]
        _ = (u * v * u⁻¹)⁻¹ := by group
        _ = v := by rw [h, inv_inv]
    calc u ^ 2 * v = u ^ 2 * v * (u ^ 2)⁻¹ * u ^ 2 := by rw [inv_mul_cancel_right]
      _ = v * u ^ 2 := by rw [h3]
  obtain ⟨j, rfl⟩ := hk
  calc u ^ (2 * j + 1) * v * (u ^ (2 * j + 1))⁻¹
      = (u ^ 2) ^ j * (u * v * u⁻¹) * ((u ^ 2) ^ j)⁻¹ := by group
    _ = v⁻¹ := by rw [h, (h2.inv_right.pow_left j).eq, mul_inv_cancel_right]

theorem eq_one_of_pow_prime_pow_eq_one {G : Type*} [Group G] {H : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hH : ¬ p ∣ Nat.card H) {g : G} (hg : g ∈ H) {k : ℕ}
    (hgk : g ^ p ^ k = 1) : g = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hgk)
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · have h1 : p ^ (j + 1) ∣ Nat.card H := hj ▸ H.orderOf_dvd_natCard hg
    exact absurd ((dvd_pow_self p j.succ_ne_zero).trans h1) hH

end Hering129KN1

theorem exists_inverted_lift {N0 : Type} [Group N0] [Finite N0] (T : Subgroup N0) [T.Normal]
    (hT : ¬ 3 ∣ Nat.card T) {U : Subgroup (N0 ⧸ T)} {x c t : N0} (hx3 : x ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hxc : x * c = c * x) (htx : t * x = x * t)
    (htc : t * c * t⁻¹ = c⁻¹) (ht2 : IsPGroup 2 (Subgroup.zpowers t)) {Yn : Subgroup N0}
    (htY : t ∈ Yn)
    (hYn : ∀ m : N0, m * x = x * m → m * c = c * m → ∀ y ∈ Yn, m * y * m⁻¹ ∈ Yn)
    (hloc : EndLocalX U (QuotientGroup.mk' T x) (QuotientGroup.mk' T t)
      (QuotientGroup.mk' T c)) :
    ∃ (V : Subgroup N0) (t' : N0), V ≤ Yn ∧ CFSG.Assembly.IsElemAbelian 3 V ∧
      Nat.card V = 9 ∧ c ∈ V ∧ (∀ v ∈ V, QuotientGroup.mk' T v ∈ U) ∧
      (∀ v ∈ V, v * x = x * v) ∧ t' ∈ Yn ∧ IsPGroup 2 (Subgroup.zpowers t') ∧
      t' * x = x * t' ∧ t' * c * t'⁻¹ = c⁻¹ ∧ (∀ v ∈ V, t' * v * t'⁻¹ = v⁻¹) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hcS, Q, _, _, ρ, τ, hSU, hSx, hSc, hSt, hρ, hker, hρτ, hE9, hEcomm, hE3, hEinv,
    -⟩ := hloc
  set π : N0 →* N0 ⧸ T := QuotientGroup.mk' T
  have htc' : t * c⁻¹ * t⁻¹ = c := by
    rw [show t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ by group, htc, inv_inv]
  have hlift : ∀ s ∈ S, ∃ m : N0, π m = s ∧ Commute m x ∧ Commute m c := by
    intro s hs
    obtain ⟨m₀, rfl⟩ := QuotientGroup.mk'_surjective T s
    have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers c : Set N0) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((Commute.zpow_right (show Commute x c from hxc) i).eq).symm
    have hAp : IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) :=
      IsPGroup.to_sup_of_normal_right' (Hering129KN1.isPGroup_zpowers_of_pow_eq_one hx3)
        (Hering129KN1.isPGroup_zpowers_of_pow_eq_one hc3) hxN
    have hAc : Subgroup.zpowers x ⊔ Subgroup.zpowers c ≤
        (Subgroup.centralizer {π m₀}).comap π := by
      refine sup_le ?_ ?_ <;>
        rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      · exact hSx _ hs
      · exact hSc _ hs
    let α : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) →* MulAut N0 :=
      (MulAut.conj : N0 →* MulAut N0).comp (Subgroup.zpowers x ⊔ Subgroup.zpowers c).subtype
    have hinv : ∀ (a : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c)) (y : N0),
        m₀⁻¹ * y ∈ T → m₀⁻¹ * α a y ∈ T := by
      intro a y hy
      have h1 : π m₀ = π y := QuotientGroup.eq.mpr hy
      have h2 : π a * π m₀ = π m₀ * π a := by
        have := hAc a.2
        rwa [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
      apply QuotientGroup.eq.mp
      change π m₀ = π ((a : N0) * y * (a : N0)⁻¹)
      rw [map_mul, map_mul, map_inv, ← h1, h2, mul_inv_cancel_right]
    obtain ⟨m, hmT, hmfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3
      hAp α T hT m₀).2 hinv
    have hfix : ∀ a ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers c, Commute m a := by
      intro a ha
      have h1 : α ⟨a, ha⟩ m = m := hmfix ⟨a, ha⟩
      change a * m * a⁻¹ = m at h1
      calc m * a = (a * m * a⁻¹) * a := by rw [h1]
        _ = a * m := by group
    exact ⟨m, (QuotientGroup.eq.mpr hmT).symm,
      hfix x (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)),
      hfix c (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))⟩
  obtain ⟨M₁, hmemM₁⟩ : ∃ M₁ : Subgroup N0,
      ∀ m, m ∈ M₁ ↔ π m ∈ S ∧ Commute m x ∧ Commute m c :=
    ⟨{ carrier := {m | π m ∈ S ∧ Commute m x ∧ Commute m c}
       mul_mem' := fun {a b} ha hb =>
         ⟨by rw [map_mul]; exact S.mul_mem ha.1 hb.1, ha.2.1.mul_left hb.2.1,
           ha.2.2.mul_left hb.2.2⟩
       one_mem' := ⟨by rw [map_one]; exact S.one_mem, Commute.one_left x, Commute.one_left c⟩
       inv_mem' := fun {a} ha =>
         ⟨by rw [map_inv]; exact S.inv_mem ha.1, ha.2.1.inv_left, ha.2.2.inv_left⟩ },
      fun m => Iff.rfl⟩
  have htM₁ : ∀ m ∈ M₁, t * m * t⁻¹ ∈ M₁ := by
    intro m hm
    rw [hmemM₁] at hm ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv]; exact hSt _ hm.1
    · exact ((show Commute t x from htx).mul_left hm.2.1).mul_left
        (show Commute t x from htx).inv_left
    · show t * m * t⁻¹ * c = c * (t * m * t⁻¹)
      calc t * m * t⁻¹ * c = t * m * t⁻¹ * (t * c⁻¹ * t⁻¹) := by rw [htc']
        _ = t * (m * c⁻¹) * t⁻¹ := by group
        _ = t * (c⁻¹ * m) * t⁻¹ := by rw [hm.2.2.inv_right.eq]
        _ = (t * c⁻¹ * t⁻¹) * (t * m * t⁻¹) := by group
        _ = c * (t * m * t⁻¹) := by rw [htc']
  obtain ⟨N₁, hN₁def⟩ : ∃ N₁ : Subgroup N0,
      N₁ = Subgroup.closure {g | ∃ m ∈ M₁, g = m * t * m⁻¹ * t⁻¹} := ⟨_, rfl⟩
  have hgen : ∀ m ∈ M₁, m * t * m⁻¹ * t⁻¹ ∈ N₁ := by
    intro m hm
    rw [hN₁def]
    exact Subgroup.subset_closure ⟨m, hm, rfl⟩
  have hN₁M₁ : N₁ ≤ M₁ := by
    rw [hN₁def, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, show m * t * m⁻¹ * t⁻¹ = m * (t * m⁻¹ * t⁻¹) by group]
    exact M₁.mul_mem hm (htM₁ _ (M₁.inv_mem hm))
  have hN₁Y : N₁ ≤ Yn := by
    rw [hN₁def, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    rw [hmemM₁] at hm
    exact Yn.mul_mem (hYn m hm.2.1 hm.2.2 t htY) (Yn.inv_mem htY)
  have htN₁ : ∀ n ∈ N₁, t * n * t⁻¹ ∈ N₁ := by
    have : N₁ ≤ N₁.comap (MulAut.conj t).toMonoidHom := by
      conv_lhs => rw [hN₁def]
      rw [Subgroup.closure_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      convert hgen _ (htM₁ m hm) using 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact fun n hn => this hn
  have hN₁S : ∀ n ∈ N₁, π n ∈ S := fun n hn => ((hmemM₁ n).mp (hN₁M₁ hn)).1
  have hcM₁ : c ∈ M₁ := (hmemM₁ c).mpr ⟨hcS, hxc.symm, Commute.refl c⟩
  have hcN₁ : c ∈ N₁ := by
    have h1 : c * c ∈ N₁ := by
      have := hgen c hcM₁
      rwa [show c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) by group, htc'] at this
    have h3 : c * (c * c) = 1 := by rw [← pow_three]; exact hc3
    have h2 : c = (c * c) * (c * c) := by
      rw [show (c * c) * (c * c) = (c * (c * c)) * c by simp only [mul_assoc], h3, one_mul]
    rw [h2]
    exact N₁.mul_mem h1 h1
  obtain ⟨ψ, hψ⟩ : ∃ ψ : N0 → Q, ∀ g (h : π g ∈ S), ψ g = ρ ⟨π g, h⟩ :=
    ⟨fun g => if h : π g ∈ S then ρ ⟨π g, h⟩ else 1, fun g h => dif_pos h⟩
  have hψmul : ∀ a b, π a ∈ S → π b ∈ S → ψ (a * b) = ψ a * ψ b := by
    intro a b ha hb
    rw [hψ _ (by rw [map_mul]; exact S.mul_mem ha hb), hψ a ha, hψ b hb, ← map_mul ρ]
    exact congrArg ρ (Subtype.ext (map_mul π a b))
  have hψinv : ∀ a, π a ∈ S → ψ a⁻¹ = (ψ a)⁻¹ := by
    intro a ha
    rw [hψ _ (by rw [map_inv]; exact S.inv_mem ha), hψ a ha, ← map_inv ρ]
    exact congrArg ρ (Subtype.ext (map_inv π a))
  have hψone : ψ 1 = 1 := by
    rw [hψ 1 (by rw [map_one]; exact S.one_mem), ← map_one ρ]
    exact congrArg ρ (Subtype.ext (map_one π))
  have hψt : ∀ a, π a ∈ S → ψ (t * a * t⁻¹) = τ (ψ a) := by
    intro a ha
    have hs : π t * π a * (π t)⁻¹ ∈ S := hSt _ ha
    rw [hψ _ (by rw [map_mul, map_mul, map_inv]; exact hs), hψ a ha, ← hρτ ⟨π a, ha⟩ hs]
    exact congrArg ρ (Subtype.ext (by simp only [map_mul, map_inv]))
  have hψpow : ∀ a, π a ∈ S → ∀ k : ℕ, ψ (a ^ k) = ψ a ^ k := by
    intro a ha k
    induction k with
    | zero => rw [pow_zero, pow_zero, hψone]
    | succ k ih =>
      rw [pow_succ, pow_succ, hψmul _ _ (by rw [map_pow]; exact S.pow_mem ha k) ha, ih]
  have hgenψ : ∀ m ∈ M₁, ψ (m * t * m⁻¹ * t⁻¹) = ψ m * (τ (ψ m))⁻¹ := by
    intro m hm
    have hmS := ((hmemM₁ m).mp hm).1
    have hmS' : π m⁻¹ ∈ S := by rw [map_inv]; exact S.inv_mem hmS
    have htS : π (t * m⁻¹ * t⁻¹) ∈ S := ((hmemM₁ _).mp (htM₁ _ (M₁.inv_mem hm))).1
    rw [show m * t * m⁻¹ * t⁻¹ = m * (t * m⁻¹ * t⁻¹) by group, hψmul _ _ hmS htS,
      hψt _ hmS', hψinv _ hmS, map_inv]
  have hψsurj : ∀ q : Q, ∃ m ∈ M₁, ψ m = q := by
    intro q
    obtain ⟨s, rfl⟩ := hρ q
    obtain ⟨m, hms, hmx, hmc⟩ := hlift s s.2
    have hmS : π m ∈ S := hms ▸ s.2
    refine ⟨m, (hmemM₁ m).mpr ⟨hmS, hmx, hmc⟩, ?_⟩
    rw [hψ m hmS]
    exact congrArg ρ (Subtype.ext hms)
  have hψE : ∀ n ∈ N₁, ψ n ∈ commSubgroup τ := by
    intro n hn
    rw [hN₁def] at hn
    induction hn using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨m, hm, rfl⟩ := hg
      rw [hgenψ m hm]
      exact Subgroup.subset_closure ⟨ψ m, rfl⟩
    | one => rw [hψone]; exact Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
      rw [← hN₁def] at ha hb
      rw [hψmul _ _ (hN₁S a ha) (hN₁S b hb)]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      rw [← hN₁def] at ha
      rw [hψinv _ (hN₁S a ha)]
      exact Subgroup.inv_mem _ iha
  let φ : N₁ →* Q := ρ.comp ((π.comp N₁.subtype).codRestrict S (fun n => hN₁S n n.2))
  have hφ : ∀ n : N₁, φ n = ψ n := fun n => (hψ n (hN₁S n n.2)).symm
  have h9 : 3 ^ 2 ∣ Nat.card N₁ := by
    have h1 : commSubgroup τ ≤ φ.range := by
      unfold commSubgroup
      rw [Subgroup.closure_le]
      rintro _ ⟨y, rfl⟩
      obtain ⟨m, hm, rfl⟩ := hψsurj y
      exact ⟨⟨_, hgen m hm⟩, by rw [hφ]; exact hgenψ m hm⟩
    have h2 := (Subgroup.card_dvd_of_le h1).trans (Subgroup.card_range_dvd φ)
    rw [hE9] at h2
    norm_num
    exact h2
  let c₁ : N₁ := ⟨c, hcN₁⟩
  have hc₁3 : c₁ ^ 3 = 1 := Subtype.ext (by simp [c₁, hc3])
  obtain ⟨P₀, hP₀⟩ := (Hering129KN1.isPGroup_zpowers_of_pow_eq_one hc₁3).exists_le_sylow
  have hcP₀ : c₁ ∈ P₀ := hP₀ (Subgroup.mem_zpowers c₁)
  obtain ⟨n, hnN₁, hnV⟩ := Hering129KN1.exists_inv_mul_conj_mem P₀ htN₁
  set V : Subgroup N0 := (P₀ : Subgroup N₁).map N₁.subtype
  have hVN₁ : V ≤ N₁ := Subgroup.map_subtype_le _
  have hcV : c ∈ V := ⟨c₁, hcP₀, rfl⟩
  have hVp : ∀ v ∈ V, ∃ k : ℕ, v ^ 3 ^ k = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk⟩ := P₀.isPGroup' ⟨w, hw⟩
    refine ⟨k, ?_⟩
    have := congrArg (fun z : ↥(P₀ : Subgroup N₁) => ((z : N₁) : N0)) hk
    simpa using this
  have hψV : ∀ v ∈ V, ψ v ∈ commSubgroup τ := fun v hv => hψE v (hVN₁ hv)
  have hVS : ∀ v ∈ V, π v ∈ S := fun v hv => hN₁S v (hVN₁ hv)
  have hinj : ∀ a ∈ V, ∀ b ∈ V, ψ a = ψ b → a = b := by
    intro a ha b hb hab
    have hw : a⁻¹ * b ∈ V := V.mul_mem (V.inv_mem ha) hb
    obtain ⟨k, hk⟩ := hVp _ hw
    have hwS : π (a⁻¹ * b) ∈ S := hVS _ hw
    have hψ1 : ψ (a⁻¹ * b) = 1 := by
      rw [hψmul _ _ (hVS _ (V.inv_mem ha)) (hVS _ hb), hψinv _ (hVS _ ha), hab, inv_mul_cancel]
    have hS1 : (⟨π (a⁻¹ * b), hwS⟩ : S) = 1 := by
      refine Hering129KN1.eq_one_of_pow_prime_pow_eq_one Nat.prime_three hker ?_ (k := k) ?_
      · rw [MonoidHom.mem_ker, ← hψ _ hwS]
        exact hψ1
      · exact Subtype.ext (by rw [SubmonoidClass.coe_pow, ← map_pow, hk, map_one]; rfl)
    have hT1 : a⁻¹ * b ∈ T :=
      (QuotientGroup.eq_one_iff (a⁻¹ * b)).mp (congrArg Subtype.val hS1)
    have := Hering129KN1.eq_one_of_pow_prime_pow_eq_one Nat.prime_three hT hT1 hk
    rwa [inv_mul_eq_one] at this
  have hVcard : Nat.card V = 9 := by
    have hVP : Nat.card V = Nat.card (P₀ : Subgroup N₁) :=
      Subgroup.card_map_of_injective N₁.subtype_injective
    have h1 : 3 ^ 2 ∣ Nat.card V := hVP ▸ P₀.pow_dvd_card_of_pow_dvd_card h9
    have h2 : Nat.card V ≤ 9 := by
      rw [← hE9]
      refine Nat.card_le_card_of_injective
        (fun v : V => (⟨ψ v, hψV v v.2⟩ : commSubgroup τ)) ?_
      intro v w hvw
      exact Subtype.ext (hinj v v.2 w w.2 (congrArg Subtype.val hvw))
    have h3 : 0 < Nat.card V := Nat.card_pos
    obtain ⟨j, hj⟩ := h1
    norm_num at hj
    omega
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    apply hinj _ (V.mul_mem ha hb) _ (V.mul_mem hb ha)
    rw [hψmul _ _ (hVS _ ha) (hVS _ hb), hψmul _ _ (hVS _ hb) (hVS _ ha)]
    exact hEcomm _ (hψV a ha) _ (hψV b hb)
  have hV3 : ∀ v ∈ V, v ^ 3 = 1 := by
    intro v hv
    apply hinj _ (V.pow_mem hv 3) _ V.one_mem
    rw [hψpow _ (hVS _ hv), hE3 _ (hψV v hv), hψone]
  set u : N0 := n⁻¹ * t with hu
  have huY : u ∈ Yn := Yn.mul_mem (Yn.inv_mem (hN₁Y hnN₁)) htY
  have hux : Commute u x :=
    ((hmemM₁ n).mp (hN₁M₁ hnN₁)).2.1.inv_left.mul_left (show Commute t x from htx)
  have huV : ∀ v ∈ V, u * v * u⁻¹ = v⁻¹ := by
    intro v hv
    have hconj : u * v * u⁻¹ = n⁻¹ * (t * v * t⁻¹) * n := by rw [hu]; group
    have h1 : u * v * u⁻¹ ∈ V := hconj ▸ hnV v hv
    apply hinj _ h1 _ (V.inv_mem hv)
    have hnS : π n ∈ S := hN₁S n hnN₁
    have hvS : π v ∈ S := hVS v hv
    have htvS : π (t * v * t⁻¹) ∈ S := by rw [map_mul, map_mul, map_inv]; exact hSt _ hvS
    have hninv : π n⁻¹ ∈ S := by rw [map_inv]; exact S.inv_mem hnS
    rw [hconj, hψmul _ _ (by rw [map_mul]; exact S.mul_mem hninv htvS) hnS,
      hψmul _ _ hninv htvS, hψinv _ hnS, hψt _ hvS, hψinv _ hvS, hEinv _ (hψV v hv),
      hEcomm _ (Subgroup.inv_mem _ (hψE n hnN₁)) _ (Subgroup.inv_mem _ (hψV v hv)),
      inv_mul_cancel_right]
  obtain ⟨k, hk, hk2⟩ := Hering129KN1.exists_odd_pow_isPGroup_two u
  exact ⟨V, u ^ k, hVN₁.trans hN₁Y,
    ⟨⟨⟨fun a b => Subtype.ext (hVcomm a a.2 b b.2)⟩⟩, hV3⟩, hVcard, hcV,
    fun v hv => hSU (hVS v hv), fun v hv => ((hmemM₁ v).mp (hN₁M₁ (hVN₁ hv))).2.1,
    Yn.pow_mem huY k, hk2, (hux.pow_left k).eq, Hering129KN1.odd_pow_conj_eq_inv (huV c hcV) hk,
    fun v hv => Hering129KN1.odd_pow_conj_eq_inv (huV v hv) hk⟩

end CFSG.RankThree.PartTwo.Sec12
