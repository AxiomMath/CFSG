module

public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Local

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

theorem cjSub_one (A : Subgroup G) : cjSub 1 A = A := by
  ext x
  simp [mem_cjSub]

theorem cjSub_mul (a b : G) (A : Subgroup G) : cjSub (a * b) A = cjSub a (cjSub b A) := by
  ext x
  simp only [mem_cjSub]
  rw [show (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b by group]

@[expose] def conjPerm (M : Subgroup G) (Ω : Set (Subgroup G))
    (hΩ : ∀ m ∈ M, ∀ P ∈ Ω, cjSub m P ∈ Ω) : M →* Equiv.Perm Ω where
  toFun m :=
    { toFun := fun P => ⟨cjSub (m : G) P, hΩ m m.2 P P.2⟩
      invFun := fun P => ⟨cjSub (m : G)⁻¹ P, hΩ _ (M.inv_mem m.2) P P.2⟩
      left_inv := fun P => Subtype.ext (cjSub_inv_cjSub _ _)
      right_inv := fun P => Subtype.ext (cjSub_cjSub_inv _ _) }
  map_one' := by
    ext P
    show _ ∈ cjSub ((1 : M) : G) (P : Subgroup G) ↔ _
    rw [Subgroup.coe_one, cjSub_one]
    rfl
  map_mul' m m' := by
    ext P
    show _ ∈ cjSub ((m : G) * m') (P : Subgroup G) ↔ _ ∈ cjSub (m : G) (cjSub (m' : G) P)
    rw [cjSub_mul]

theorem conjPerm_apply (M : Subgroup G) (Ω : Set (Subgroup G))
    (hΩ : ∀ m ∈ M, ∀ P ∈ Ω, cjSub m P ∈ Ω) (m : M) (P : Ω) :
    ((conjPerm M Ω hΩ m P : Ω) : Subgroup G) = cjSub (m : G) P := rfl

variable [Finite G]

theorem commute_of_forall_mem_normalizer {M X Q K : Subgroup G} (hX : IsA4 X Q) (hXM : X ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (hK : ∀ k ∈ K, ∀ P ∈ syl3 X, k ∈ Subgroup.normalizer (P : Set G)) :
    ∀ k ∈ K, ∀ x ∈ X, k * x = x * k := by
  intro k hk x hx
  have hkX : k ∈ Subgroup.normalizer (X : Set G) := by
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    have hle : X ≤ X.comap (MulAut.conj k).toMonoidHom := by
      refine hX.le_of_forall_syl3_le fun P hP w hw => ?_
      show k * w * k⁻¹ ∈ X
      exact hP.1 ((Subgroup.mem_normalizer_iff.mp (hK k hk P hP) w).mp hw)
    exact hle hy
  set c := k * x * k⁻¹ * x⁻¹ with hc
  have hcX : c ∈ X := X.mul_mem ((Subgroup.mem_normalizer_iff.mp hkX x).mp hx) (X.inv_mem hx)
  have hcK : c ∈ K := by
    have : c = k * (x * k⁻¹ * x⁻¹) := by rw [hc]; group
    rw [this]
    exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hMK (hXM hx)) k⁻¹).mp (K.inv_mem hk))
  have hc1 := hX.eq_one_of_forall_mem_normalizer hcX (hK c hcK)
  calc k * x = c * (x * k) := by rw [hc]; group
    _ = x * k := by rw [hc1, one_mul]

theorem inf_centralizer_eq_bot (S : Sylow 2 G) {M Y : Subgroup G} (hSM : (S : Subgroup G) ≤ M)
    (hF : CharTwo M) (hMY : M ≤ Subgroup.normalizer (Y : Set G))
    (hT : ∀ t ∈ (S : Subgroup G), t ∈ Subgroup.centralizer (Y : Set G) → t = 1) :
    M ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := M ⊓ Subgroup.centralizer (Y : Set G) with hN
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := fun m hm =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hm, normalizer_le_normalizer_centralizer Y (hMY hm)⟩
  refine I4.eq_bot_of_normal_of_coprime_of_le hF inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hMN) ?_
  rw [Nat.coprime_two_left, Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨⟨x, hxN⟩, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
  have hx2 : orderOf x = 2 := by rw [← hx, Subgroup.orderOf_mk]
  have hA : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  obtain ⟨h, hhM, hhT⟩ := exists_conj_le_of_isSylowTwoOf (isSylowTwoOf_of_sylow S hSM)
    ((Subgroup.zpowers_le.mpr hxN).trans inf_le_left) hA
  have hmem : h * x * h⁻¹ ∈ (S : Subgroup G) := hhT (by
    rw [mem_cjSub]
    simp [mul_assoc])
  have hmemN : h * x * h⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hMN hhM) x).mp hxN
  have h1 := hT _ hmem hmemN.2
  have : x = 1 := by
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  rw [this, orderOf_one] at hx2
  norm_num at hx2

theorem eq_one_of_mem_centralizer (S : Sylow 2 G) {Y : Subgroup G}
    (hSY : (S : Subgroup G) ≤ Subgroup.normalizer (Y : Set G)) {z : G}
    (hZ : ∀ x ∈ quasithinOmegaOneCenter (S : Subgroup G), x = 1 ∨ x = z)
    (hz : z ∉ Subgroup.centralizer (Y : Set G)) :
    ∀ t ∈ (S : Subgroup G), t ∈ Subgroup.centralizer (Y : Set G) → t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer (Y : Set G) with hU
  have hSU : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hs, normalizer_le_normalizer_centralizer Y (hSY hs)⟩
  by_contra hne
  push Not at hne
  obtain ⟨t, htS, htC, ht1⟩ := hne
  have hUne : U ≠ ⊥ := fun hb => ht1 (by
    have : t ∈ U := ⟨htS, htC⟩
    rwa [hb, Subgroup.mem_bot] at this)
  obtain ⟨u, huU, hu1, hucomm⟩ := exists_ne_one_commute_of_le_normalizer S.isPGroup'
    (S.isPGroup'.to_le inf_le_left) hUne hSU
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := S.isPGroup'.to_le
    (Subgroup.zpowers_le.mpr huU.1)
  have hdvd : 2 ∣ Nat.card (Subgroup.zpowers u) := by
    obtain ⟨n, hn⟩ := hu2.exists_card_eq
    rcases n with _ | n
    · exfalso
      rw [pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hn
      exact hu1 hn
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨⟨w, hw⟩, hw2⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers u) 2 hdvd
  have hw2' : orderOf w = 2 := by rw [← hw2, Subgroup.orderOf_mk]
  have hwU : w ∈ U := (Subgroup.zpowers_le.mpr huU) hw
  have hwcomm : ∀ s ∈ (S : Subgroup G), s * w = w * s := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_right (hucomm s hs) k).eq
  have hwZ : w ∈ quasithinOmegaOneCenter (S : Subgroup G) := by
    refine Subgroup.subset_closure ⟨⟨hwU.1, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun s hs => hwcomm s hs
    · rw [← hw2']
      exact pow_orderOf_eq_one w
  rcases hZ w hwZ with h1 | h1
  · rw [h1, orderOf_one] at hw2'
    norm_num at hw2'
  · exact hz (h1 ▸ hwU.2)

end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
