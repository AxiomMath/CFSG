module

public import CFSG.Quasithin.Vol2.E2SevenKG1L2
public import CFSG.Quasithin.Background.E2SolvTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped Pointwise

namespace E2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem isPGroup_zpowers_of_pow {a : G} {r : ℕ} (h : a ^ 2 ^ r = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  rintro ⟨g, i, rfl⟩
  refine ⟨r, Subtype.ext ?_⟩
  change (a ^ i) ^ 2 ^ r = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

omit [Finite G] in
private theorem eq_one_of_forall_commute_of_simple {K : Subgroup G} (hs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) {x : G} (hx : x ∈ K) (hc : ∀ y ∈ K, x * y = y * x) :
    x = 1 := by
  have hZ : Subgroup.center ↥K = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
  have hxZ : (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact congrArg Subtype.val hxZ

theorem cjSub_eq_or_eq_of_prod {K K' : Subgroup G} (hs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hcard : Nat.card K = Nat.card K') {u : G}
    (hu : u ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G)) :
    cjSub u K = K ∨ cjSub u K = K' := by
  set A := cjSub u K with hA
  have hmemA : ∀ x, x ∈ A ↔ u⁻¹ * x * u ∈ K := fun x => mem_cjSub
  have hcardA : Nat.card A = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hKN' : K' ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_commute fun a ha b hb => (hcomm b hb a ha).symm
  have hLN : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hKN'
  have hAL : A ≤ K ⊔ K' := by
    intro x hx
    have h1 := (le_sup_left : K ≤ K ⊔ K') ((hmemA x).mp hx)
    have := (Subgroup.mem_normalizer_iff.mp hu _).mp h1
    simpa [mul_assoc] using this
  have hLA : ∀ l ∈ K ⊔ K', ∀ x ∈ A, l * x * l⁻¹ ∈ A := by
    intro l hl x hx
    rw [hmemA] at hx ⊢
    have hl' : u⁻¹ * l * u ∈ K ⊔ K' := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hu) l).mp hl
      simpa using this
    have := (Subgroup.mem_normalizer_iff.mp (hLN hl') _).mp hx
    have e : u⁻¹ * (l * x * l⁻¹) * u =
        (u⁻¹ * l * u) * (u⁻¹ * x * u) * (u⁻¹ * l * u)⁻¹ := by group
    rw [e]
    exact this
  have hnorm : ((A ⊓ K).subgroupOf K).Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨hLA k (le_sup_left (a := K) k.2) _ hx.1, ?_⟩
    exact K.mul_mem (K.mul_mem k.2 hx.2) (K.inv_mem k.2)
  rcases hs.eq_bot_or_eq_top_of_normal ((A ⊓ K).subgroupOf K) with h | h
  ·
    right
    have hAK : A ⊓ K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : ↥K) ∈ (A ⊓ K).subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
    have hcent : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a := by
      intro a ha k hk
      have h1 : a * k * a⁻¹ * k⁻¹ ∈ A ⊓ K := by
        refine ⟨?_, ?_⟩
        · have := A.mul_mem ha (hLA k (le_sup_left (a := K) hk) _ (A.inv_mem ha))
          simpa [mul_assoc] using this
        · exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLN (hAL ha)) k).mp hk) (K.inv_mem hk)
      rw [hAK, Subgroup.mem_bot] at h1
      have := congrArg (· * (k * a)) h1
      simp only [one_mul] at this
      rw [← this]
      group
    have hle : A ≤ K' := by
      intro a ha
      have haL := hAL ha
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K K'
        (le_normalizer_of_commute hcomm)] at haL
      obtain ⟨k, hk, b, hb, rfl⟩ := haL
      change k * b ∈ K'
      have hk1 : k = 1 := by
        apply eq_one_of_forall_commute_of_simple hs hnab hk
        intro y hy
        have h1 := hcent (k * b) ha y hy
        have h2 := hcomm y hy b hb
        calc k * y = k * y * b * b⁻¹ := by group
          _ = k * (y * b) * b⁻¹ := by group
          _ = k * (b * y) * b⁻¹ := by rw [h2]
          _ = (k * b) * y * b⁻¹ := by group
          _ = y * (k * b) * b⁻¹ := by rw [h1]
          _ = y * k := by group
      rw [hk1, one_mul]
      exact hb
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardA, hcard])
  ·
    left
    have hKA : K ≤ A := by
      intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ (A ⊓ K).subgroupOf K := by rw [h]; trivial
      exact (Subgroup.mem_subgroupOf.mp this).1
    exact (Subgroup.eq_of_le_of_card_ge hKA (by rw [hcardA])).symm

theorem kgBenderInnerTwo_of_facts {X T M K : Subgroup G} {t : G} (hP : MinParabolic X T M)
    (ht : t ∈ T) (hKX : K ≤ X) (htK : cjSub t K ≠ K)
    (hXN : X ≤ Subgroup.normalizer ((K ⊔ cjSub t K : Subgroup G) : Set G))
    (hC : X ⊓ Subgroup.centralizer ((K ⊔ cjSub t K : Subgroup G) : Set G) = ⊥)
    (hKK : K ⊓ cjSub t K = ⊥) (hcomm : ⁅K, cjSub t K⁆ = ⊥)
    (hMK : M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hsK : IsSimpleGroup ↥K) (hnabK : ∃ a b : ↥K, a * b ≠ b * a)
    (hnp : IsSylowTwoOf (T ⊓ K) K →
      ¬ IsPGroup 2 ↥(K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)))
    (hagree : ∀ K₀ : Subgroup G, (K₀ = K ∨ K₀ = cjSub t K) → IsSylowTwoOf (T ⊓ K₀) K₀ →
      ∀ u : G, u ∈ Subgroup.normalizer (K₀ : Set G) → (∃ m : ℕ, u ^ 2 ^ m = 1) →
      (∀ b ∈ K₀ ⊓ Subgroup.normalizer ((T ⊓ K₀ : Subgroup G) : Set G),
        u * b * u⁻¹ * b⁻¹ ∈ T ⊓ K₀) →
      ∃ k ∈ K₀, ∀ x ∈ K₀, u * x * u⁻¹ = k * x * k⁻¹)
    (hinv : ∀ K₀ : Subgroup G, (K₀ = K ∨ K₀ = cjSub t K) → IsSylowTwoOf (T ⊓ K₀) K₀ →
      ∀ x ∈ T ⊓ K₀, x ^ 2 = 1 → ∀ y ∈ T ⊓ K₀, x * y = y * x) :
    pCoreOf 2 M ≤ K ⊔ cjSub t K ∧
      ∀ x ∈ T ⊓ (K ⊔ cjSub t K), x ^ 2 = 1 →
        x ∈ Subgroup.centralizer ((T ⊓ (K ⊔ cjSub t K) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' := cjSub t K with hK'def
  set L := K ⊔ K' with hLdef
  have hTX : T ≤ X := hP.isSylow.1
  have htX : t ∈ X := hTX ht
  have hmemK' : ∀ x, x ∈ K' ↔ t⁻¹ * x * t ∈ K := fun x => mem_cjSub
  have hK'X : K' ≤ X := fun x hx => by
    have := X.mul_mem (X.mul_mem htX (hKX ((hmemK' x).mp hx))) (X.inv_mem htX)
    simpa [mul_assoc] using this
  have hLX : L ≤ X := sup_le hKX hK'X
  have hKK'c : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := fun a ha b hb => by
    have h1 := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hLNK : L ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_of_commute fun a ha b hb => (hKK'c b hb a ha).symm)
  have hLNK' : L ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le (le_normalizer_of_commute hKK'c) Subgroup.le_normalizer
  let eK : ↥K' ≃* ↥K :=
    (K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm
  have hcardK' : Nat.card K = Nat.card K' := (Nat.card_congr eK.toEquiv).symm
  have hsK' : IsSimpleGroup ↥K' := (MulEquiv.isSimpleGroup_congr eK).mpr hsK
  have hnabK' : ∃ a b : ↥K', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabK
    refine ⟨eK.symm a, eK.symm b, fun h => hab ?_⟩
    have := congrArg eK h
    simpa using this
  have hTL : IsSylowTwoOf (T ⊓ L) L := A4.isSylowTwoOf_inf_normal hP.isSylow hLX hXN
  have hTK : IsSylowTwoOf (T ⊓ K) K := by
    have := A4.isSylowTwoOf_inf_normal hTL le_sup_left hLNK
    rwa [inf_assoc, inf_of_le_right (le_sup_left : K ≤ L)] at this
  have hTK' : IsSylowTwoOf (T ⊓ K') K' := by
    have := A4.isSylowTwoOf_inf_normal hTL le_sup_right hLNK'
    rwa [inf_assoc, inf_of_le_right (le_sup_right : K' ≤ L)] at this
  have hT2 : IsPGroup 2 T := hP.isSylow.2.1
  have hLprod : ((L : Subgroup G) : Set G) = (K : Set G) * (K' : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K K' (le_normalizer_of_commute hKK'c)
  have hdec : ∀ x ∈ T ⊓ L, ∃ a ∈ T ⊓ K, ∃ b ∈ T ⊓ K', x = a * b := by
    intro x hx
    have hxL : x ∈ (K : Set G) * (K' : Set G) := by
      rw [← hLprod]
      exact hx.2
    obtain ⟨a, ha, b, hb, rfl⟩ := hxL
    obtain ⟨r, hr⟩ := hT2 ⟨a * b, hx.1⟩
    have hr' : (a * b) ^ 2 ^ r = 1 := by simpa using congrArg Subtype.val hr
    rw [(Commute.mul_pow (hKK'c a ha b hb)) (2 ^ r)] at hr'
    have hab1 : a ^ 2 ^ r = (b ^ 2 ^ r)⁻¹ := eq_inv_of_mul_eq_one_left hr'
    have ha1 : a ^ 2 ^ r = 1 := by
      have hmem : a ^ 2 ^ r ∈ K ⊓ K' :=
        ⟨K.pow_mem ha _, hab1 ▸ K'.inv_mem (K'.pow_mem hb _)⟩
      rw [hKK, Subgroup.mem_bot] at hmem
      exact hmem
    have hb1 : b ^ 2 ^ r = 1 := by
      rw [ha1] at hab1
      exact inv_eq_one.mp hab1.symm
    have hxN : a * b ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      exact and_congr ((Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx.1)) z)
        ((Subgroup.mem_normalizer_iff.mp (hLNK hx.2)) z)
    have hbN : b ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
      le_normalizer_of_commute (A := K') (B := T ⊓ K) (fun b hb a ha => (hKK'c a ha.2 b hb).symm) hb
    have haN : a ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      have := Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hbN)
      simpa using this
    have hxN' : a * b ∈ Subgroup.normalizer ((T ⊓ K' : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      exact and_congr ((Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx.1)) z)
        ((Subgroup.mem_normalizer_iff.mp (hLNK' hx.2)) z)
    have haN' : a ∈ Subgroup.normalizer ((T ⊓ K' : Subgroup G) : Set G) :=
      le_normalizer_of_commute (A := K) (B := T ⊓ K') (fun a ha b hb => hKK'c a ha b hb.2) ha
    have hbN' : b ∈ Subgroup.normalizer ((T ⊓ K' : Subgroup G) : Set G) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ haN') hxN'
      simpa [mul_assoc] using this
    have haT := le_of_le_normalizer_of_isSylowTwoOf hTK (isPGroup_zpowers_of_pow ha1)
      (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr haN) (Subgroup.mem_zpowers a)
    have hbT := le_of_le_normalizer_of_isSylowTwoOf hTK' (isPGroup_zpowers_of_pow hb1)
      (Subgroup.zpowers_le.mpr hb) (Subgroup.zpowers_le.mpr hbN') (Subgroup.mem_zpowers b)
    exact ⟨a, haT, b, hbT, rfl⟩
  refine ⟨?_, fun x hx hx2 => ?_⟩
  swap
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec y hy
    have hab2 : a ^ 2 * b ^ 2 = 1 := by
      rw [← (Commute.mul_pow (hKK'c a ha.2 b hb.2)) 2]
      exact hx2
    have ha2 : a ^ 2 = 1 := by
      have hmem : a ^ 2 ∈ K ⊓ K' := ⟨K.pow_mem ha.2 _, by
        rw [eq_inv_of_mul_eq_one_left hab2]
        exact K'.inv_mem (K'.pow_mem hb.2 _)⟩
      rw [hKK, Subgroup.mem_bot] at hmem
      exact hmem
    have hb2 : b ^ 2 = 1 := by
      rw [ha2, one_mul] at hab2
      exact hab2
    have h1 := (hinv K (Or.inl rfl) hTK a ha ha2 a' ha').symm
    have h2 := (hinv K' (Or.inr rfl) hTK' b hb hb2 b' hb').symm
    have h3 := hKK'c a ha.2 b' hb'.2
    have h4 := hKK'c a' ha'.2 b hb.2
    calc a' * b' * (a * b) = a' * (b' * a) * b := by group
      _ = a' * (a * b') * b := by rw [h3]
      _ = (a' * a) * (b' * b) := by group
      _ = (a * a') * (b * b') := by rw [h1, h2]
      _ = a * (a' * b) * b' := by group
      _ = a * (b * a') * b' := by rw [h4]
      _ = a * b * (a' * b') := by group
  intro u hu
  obtain ⟨hMmax, hTM⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  have hMX : M ≤ X := hMmax.le
  have htM : t ∈ M := hTM ht
  have huM : u ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hu
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hTsylM : IsSylowTwoOf T M := isSylowTwoOf_mono hP.isSylow hTM hMX
  have hO2T : pCoreOf 2 M ≤ T := A4.le_of_normal_of_isSylowTwoOf hTsylM
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hO2
  have huT : u ∈ T := hO2T hu
  have huNL : u ∈ Subgroup.normalizer (L : Set G) := hXN (hMX huM)
  obtain ⟨m, hm⟩ := hO2 ⟨u, hu⟩
  have hum : u ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcO2 : ∀ b ∈ M, u * b * u⁻¹ * b⁻¹ ∈ pCoreOf 2 M := by
    intro b hbM
    have h1 := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf
      2 M hbM) u⁻¹).mp ((pCoreOf 2 M).inv_mem hu)
    have := (pCoreOf 2 M).mul_mem hu h1
    simpa [mul_assoc] using this
  have hBM : ∀ b ∈ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G), b ∈ M := fun b hb =>
    (hMK ▸ hb : b ∈ M ⊓ K).1
  have hB'M : ∀ b ∈ K' ⊓ Subgroup.normalizer ((T ⊓ K' : Subgroup G) : Set G), b ∈ M := by
    rintro b ⟨hbK', hbN⟩
    have hcK : t⁻¹ * b * t ∈ K := (hmemK' b).mp hbK'
    have hcN : t⁻¹ * b * t ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have key : ∀ w, w ∈ T ⊓ K ↔ t * w * t⁻¹ ∈ T ⊓ K' := by
        intro w
        constructor
        · rintro ⟨hwT, hwK⟩
          exact ⟨T.mul_mem (T.mul_mem ht hwT) (T.inv_mem ht),
            (hmemK' _).mpr (by simpa [mul_assoc] using hwK)⟩
        · rintro ⟨hwT, hwK⟩
          have hwK' := (hmemK' _).mp hwK
          refine ⟨?_, by simpa [mul_assoc] using hwK'⟩
          have := T.mul_mem (T.mul_mem (T.inv_mem ht) hwT) ht
          simpa [mul_assoc] using this
      rw [key z, key (t⁻¹ * b * t * z * (t⁻¹ * b * t)⁻¹)]
      have e : t * (t⁻¹ * b * t * z * (t⁻¹ * b * t)⁻¹) * t⁻¹ = b * (t * z * t⁻¹) * b⁻¹ := by
        group
      rw [e]
      exact Subgroup.mem_normalizer_iff.mp hbN _
    have := hBM _ ⟨hcK, hcN⟩
    have h2 := M.mul_mem (M.mul_mem htM this) (M.inv_mem htM)
    simpa [mul_assoc] using h2
  rcases cjSub_eq_or_eq_of_prod hsK hnabK hKK'c hcardK' huNL with hKu | hKu
  ·
    have huNK : u ∈ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have : u * z * u⁻¹ ∈ cjSub u K := by rw [mem_cjSub]; simpa [mul_assoc] using hz
        rwa [hKu] at this
      · intro hz
        rw [← hKu, mem_cjSub] at hz
        simpa [mul_assoc] using hz
    have hK'u : cjSub u K' = K' := by
      have hnorm' : u ∈ Subgroup.normalizer ((K' ⊔ K : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact huNL
      rcases cjSub_eq_or_eq_of_prod hsK' hnabK' (fun a ha b hb => (hKK'c b hb a ha).symm)
          hcardK'.symm hnorm' with h | h
      · exact h
      · exfalso
        apply htK
        have h1 : cjSub u K' = cjSub u K := by rw [h, hKu]
        ext x
        constructor
        · intro hx
          have h3 : u * x * u⁻¹ ∈ cjSub u K' := by rw [mem_cjSub]; simpa [mul_assoc] using hx
          rw [h1, mem_cjSub] at h3
          simpa [mul_assoc] using h3
        · intro hx
          have h3 : u * x * u⁻¹ ∈ cjSub u K := by rw [mem_cjSub]; simpa [mul_assoc] using hx
          rw [← h1, mem_cjSub] at h3
          simpa [mul_assoc] using h3
    have huNK' : u ∈ Subgroup.normalizer (K' : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have : u * z * u⁻¹ ∈ cjSub u K' := by rw [mem_cjSub]; simpa [mul_assoc] using hz
        rwa [hK'u] at this
      · intro hz
        rw [← hK'u, mem_cjSub] at hz
        simpa [mul_assoc] using hz
    have huNTK : u ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      exact and_congr ((Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer huT)) z)
        ((Subgroup.mem_normalizer_iff.mp huNK) z)
    have huNTK' : u ∈ Subgroup.normalizer ((T ⊓ K' : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      exact and_congr ((Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer huT)) z)
        ((Subgroup.mem_normalizer_iff.mp huNK') z)
    have hcommK : ∀ b ∈ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G),
        u * b * u⁻¹ * b⁻¹ ∈ T ⊓ K := by
      intro b hb
      have hc1 := hcO2 b (hBM b hb)
      have hc2 : u * b * u⁻¹ * b⁻¹ ∈ K :=
        K.mul_mem ((Subgroup.mem_normalizer_iff.mp huNK b).mp hb.1) (K.inv_mem hb.1)
      have hc3 : u * b * u⁻¹ * b⁻¹ ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huNTK hb.2)
          (Subgroup.inv_mem _ huNTK)) (Subgroup.inv_mem _ hb.2)
      exact le_of_le_normalizer_of_isSylowTwoOf hTK (hO2.to_le (Subgroup.zpowers_le.mpr hc1))
        (Subgroup.zpowers_le.mpr hc2) (Subgroup.zpowers_le.mpr hc3) (Subgroup.mem_zpowers _)
    have hcommK' : ∀ b ∈ K' ⊓ Subgroup.normalizer ((T ⊓ K' : Subgroup G) : Set G),
        u * b * u⁻¹ * b⁻¹ ∈ T ⊓ K' := by
      intro b hb
      have hc1 := hcO2 b (hB'M b hb)
      have hc2 : u * b * u⁻¹ * b⁻¹ ∈ K' :=
        K'.mul_mem ((Subgroup.mem_normalizer_iff.mp huNK' b).mp hb.1) (K'.inv_mem hb.1)
      have hc3 : u * b * u⁻¹ * b⁻¹ ∈ Subgroup.normalizer ((T ⊓ K' : Subgroup G) : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huNTK' hb.2)
          (Subgroup.inv_mem _ huNTK')) (Subgroup.inv_mem _ hb.2)
      exact le_of_le_normalizer_of_isSylowTwoOf hTK' (hO2.to_le (Subgroup.zpowers_le.mpr hc1))
        (Subgroup.zpowers_le.mpr hc2) (Subgroup.zpowers_le.mpr hc3) (Subgroup.mem_zpowers _)
    obtain ⟨k₁, hk₁K, hag₁⟩ := hagree K (Or.inl rfl) hTK u huNK ⟨m, hum⟩ hcommK
    obtain ⟨k₂, hk₂K', hag₂⟩ := hagree K' (Or.inr rfl) hTK' u huNK' ⟨m, hum⟩ hcommK'
    set c := (k₁ * k₂)⁻¹ * u with hc
    have hcomm_of : ∀ x, c * x * c⁻¹ = x → x * c = c * x := by
      intro x h
      calc x * c = c * x * c⁻¹ * c := by rw [h]
        _ = c * x := by group
    have hcK : ∀ x ∈ K, x * c = c * x := by
      intro x hx
      apply hcomm_of
      have h1 := hag₁ x hx
      have h2 := hKK'c x hx k₂ hk₂K'
      calc c * x * c⁻¹ = k₂⁻¹ * (k₁⁻¹ * (u * x * u⁻¹) * k₁) * k₂ := by rw [hc]; group
        _ = k₂⁻¹ * (k₁⁻¹ * (k₁ * x * k₁⁻¹) * k₁) * k₂ := by rw [h1]
        _ = k₂⁻¹ * (x * k₂) := by group
        _ = x := by rw [h2]; group
    have hcK' : ∀ x ∈ K', x * c = c * x := by
      intro x hx
      apply hcomm_of
      have h1 := hag₂ x hx
      have h2 := hKK'c k₁ hk₁K (k₂ * x * k₂⁻¹)
        (K'.mul_mem (K'.mul_mem hk₂K' hx) (K'.inv_mem hk₂K'))
      calc c * x * c⁻¹ = k₂⁻¹ * (k₁⁻¹ * (u * x * u⁻¹) * k₁) * k₂ := by rw [hc]; group
        _ = k₂⁻¹ * (k₁⁻¹ * ((k₂ * x * k₂⁻¹) * k₁)) * k₂ := by rw [h1]; group
        _ = k₂⁻¹ * (k₁⁻¹ * (k₁ * (k₂ * x * k₂⁻¹))) * k₂ := by rw [h2]
        _ = x := by group
    have hcL : c ∈ X ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨X.mul_mem (X.inv_mem (X.mul_mem (hKX hk₁K) (hK'X hk₂K'))) (hMX huM), ?_⟩
      show c ∈ Subgroup.centralizer (L : Set G)
      have hle : L ≤ Subgroup.centralizer ({c} : Set G) := sup_le
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcK x hx))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcK' x hx))
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    rw [hC, Subgroup.mem_bot, hc, inv_mul_eq_one] at hcL
    rw [← hcL]
    exact L.mul_mem (le_sup_left (a := K) hk₁K) (le_sup_right (b := K') hk₂K')
  ·
    exfalso
    apply hnp hTK
    rintro ⟨b, hb⟩
    have hc1 := hcO2 b (hBM b hb)
    obtain ⟨r, hr⟩ := hO2 ⟨_, hc1⟩
    have hr' : (u * b * u⁻¹ * b⁻¹) ^ 2 ^ r = 1 := by simpa using congrArg Subtype.val hr
    have hubK' : u * b * u⁻¹ ∈ K' := by
      rw [← hKu, mem_cjSub]
      simpa [mul_assoc] using hb.1
    have hcm : Commute (u * b * u⁻¹) b⁻¹ :=
      (hKK'c b⁻¹ (K.inv_mem hb.1) _ hubK').symm
    rw [hcm.mul_pow, conj_pow, inv_pow] at hr'
    have hpow : u * b ^ 2 ^ r * u⁻¹ = b ^ 2 ^ r := mul_inv_eq_one.mp hr'
    have hmemK'' : b ^ 2 ^ r ∈ K' := by
      have h1 : u * b ^ 2 ^ r * u⁻¹ ∈ cjSub u K :=
        mem_cjSub.mpr (by simpa [mul_assoc] using K.pow_mem hb.1 (2 ^ r))
      rw [hKu, hpow] at h1
      exact h1
    have hmem : b ^ 2 ^ r ∈ K ⊓ K' := ⟨K.pow_mem hb.1 _, hmemK''⟩
    rw [hKK, Subgroup.mem_bot] at hmem
    exact ⟨r, Subtype.ext (by simpa using hmem)⟩


theorem kgBenderInnerTwoL2_holds : KGBenderInnerTwoL2 := by
  intro G _ _ X T M K t n hP hJ ht hKX htK hXN hC hKK hcomm hKT hn hK hM hMK
  have hK' : IsPSL 2 2 n ↥(cjSub t K) := by
    obtain ⟨hadm, F, h1, h2, hF, ⟨g⟩⟩ := hK
    exact ⟨hadm, F, h1, h2, hF,
      ⟨(K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans g⟩⟩
  have hfam : ∀ K₀ : Subgroup G, (K₀ = K ∨ K₀ = cjSub t K) → IsPSL 2 2 n ↥K₀ := by
    rintro K₀ (rfl | rfl)
    · exact hK
    · exact hK'
  refine kgBenderInnerTwo_of_facts hP ht hKX htK hXN hC hKK hcomm hMK
    (isSimpleGroup_of_isPSL_two hn hK) (exists_mul_ne_mul_of_isPSL_two hn hK)
    (not_isPGroup_normalizer_of_isPSL_two hn hK) ?_ ?_
  · intro K₀ hK₀ hS u huK ⟨m, hum⟩ hcomm₀
    obtain ⟨k, hk, hag⟩ := exists_conj_agree_of_isPSL_two hn (hfam K₀ hK₀) hS huK hum hcomm₀
    exact ⟨k, hk.2, hag⟩
  · intro K₀ hK₀ hS x hx _ y hy
    exact comm_of_isPSL_two hn (hfam K₀ hK₀) hS x hx y hy

end E2

end CFSG.Quasithin
