module

public import CFSG.Quasithin.EmptyFaithful.A38c14Foc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListHat

public section

namespace CFSG.Quasithin.A38c14

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open scoped IsMulCommutative

section Cover

variable {X Y : Type} [Group X] [Group Y]

theorem isSolvable_inf_ker (π : X →* Y) (hker : π.ker ≤ Subgroup.center X) (M : Subgroup X) :
    Group.IsSolvable ↥(π.ker ⊓ M) := by
  have : IsMulCommutative ↥(π.ker ⊓ M) :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp (hker a.2.1)) b.1).symm⟩⟩
  infer_instance

theorem map_mem_lFamily [Finite X] [Finite Y] (π : X →* Y) (hker : π.ker ≤ Subgroup.center X) {T B : Subgroup X}
    (hB : B ∈ lFamily T) : B.map π ∈ lFamily (T.map π) := by
  have h := A312.map_mem_cComp π (isSolvable_inf_ker π hker (B ⊔ T))
    (show B ∈ cComp (B ⊔ T) from hB)
  rw [Subgroup.map_sup] at h
  exact h

theorem map_ne_top_of_central (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    (hX : commutator X = ⊤) {B : Subgroup X} (hB : B ≠ ⊤) : B.map π ≠ ⊤ := by
  intro htop
  apply hB
  have hsup : B ⊔ Subgroup.center X = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup X) = (B.map π).comap π := by rw [htop, Subgroup.comap_top]
      _ = B ⊔ π.ker := Subgroup.comap_map_eq π B
      _ ≤ B ⊔ Subgroup.center X := sup_le_sup_left hker B
  exact eq_top_of_sup_center_eq_top' hX hsup

theorem commutator_eq_top_of_lFamily [Finite X] {T B : Subgroup X} (hB : B ∈ lFamily T) :
    commutator ↥B = ⊤ :=
  Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr
    (perfect_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)))

theorem inf_ker_eq_bot_or_ker_le [Finite X] (π : X →* Y) (hk3 : Nat.card π.ker = 3) (B : Subgroup X) :
    B ⊓ π.ker = ⊥ ∨ π.ker ≤ B := by
  by_cases h : B ⊓ π.ker = ⊥
  · exact Or.inl h
  · right
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
    have hxB : (x : X) ∈ B := x.2.1
    have hxK : (x : X) ∈ π.ker := x.2.2
    have hdvd : orderOf (x : X) ∣ 3 := by
      have h1 := orderOf_dvd_natCard (⟨(x : X), hxK⟩ : ↥π.ker)
      rw [hk3, ← Subgroup.orderOf_coe] at h1
      exact h1
    have hne : orderOf (x : X) ≠ 1 := by
      intro h1
      exact hx1 (Subtype.ext (orderOf_eq_one_iff.mp h1))
    have h3 : orderOf (x : X) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact absurd h1 hne
      · exact h1
    have hzp : Subgroup.zpowers (x : X) ≤ π.ker := Subgroup.zpowers_le.mpr hxK
    have heq : Subgroup.zpowers (x : X) = π.ker :=
      Subgroup.eq_of_le_of_card_ge hzp (by rw [Nat.card_zpowers, h3, hk3])
    rw [← heq]
    exact Subgroup.zpowers_le.mpr hxB

noncomputable def mapEquivOfInfKerEqBot (π : X →* Y) {B : Subgroup X} (h : B ⊓ π.ker = ⊥) :
    ↥B ≃* ↥(B.map π) :=
  MulEquiv.ofBijective (π.subgroupMap B)
    ⟨(injective_iff_map_eq_one _).mpr fun a ha => by
      have h1 : π (a : X) = 1 := by
        have := congrArg Subtype.val ha
        simpa using this
      have h2 : (a : X) ∈ B ⊓ π.ker := ⟨a.2, h1⟩
      rw [h, Subgroup.mem_bot] at h2
      exact Subtype.ext h2, π.subgroupMap_surjective B⟩

theorem card_eq_three_mul_of_ker_le (π : X →* Y) (hk3 : Nat.card π.ker = 3) {B : Subgroup X}
    (hB : π.ker ≤ B) : Nat.card B = 3 * Nat.card (B.map π) := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective (π.subgroupMap_surjective B)
  rw [Subgroup.ker_subgroupMap] at h1
  have h2 : Nat.card (π.ker.subgroupOf B) = 3 := by
    rw [← hk3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem card_eq_of_inf_ker_eq_bot (π : X →* Y) {B : Subgroup X} (h : B ⊓ π.ker = ⊥) :
    Nat.card B = Nat.card (B.map π) :=
  Nat.card_congr (mapEquivOfInfKerEqBot π h).toEquiv

theorem exists_central_order_three [Finite X] (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    (hk3 : Nat.card π.ker = 3) :
    ∃ z : X, z ∈ π.ker ∧ z ∈ Subgroup.center X ∧ orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥π.ker) 3 (dvd_of_eq hk3.symm)
  exact ⟨(x : X), x.2, hker x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem inf_ker_eq_bot_of_card [Finite X] (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    (hk3 : Nat.card π.ker = 3) {B : Subgroup X} (hB : commutator ↥B = ⊤) {m : ℕ} (hm : ¬ 3 ∣ m)
    (hcard : Nat.card (B.map π) = 3 * m) : B ⊓ π.ker = ⊥ := by
  rcases inf_ker_eq_bot_or_ker_le π hk3 B with h | hle
  · exact h
  · exfalso
    have hB9 : Nat.card B = 9 * m := by
      rw [card_eq_three_mul_of_ker_le π hk3 hle, hcard]
      ring
    obtain ⟨z, hzK, hzc, hz3⟩ := exists_central_order_three π hker hk3
    have hzB : z ∈ B := hle hzK
    have hzcB : (⟨z, hzB⟩ : ↥B) ∈ Subgroup.center ↥B := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hzc) g.1)
    exact false_of_central_three hB hm hB9 hzcB (by rw [← hz3, ← Subgroup.orderOf_coe])

theorem ker_le_of_card_nine [Finite X] [Finite Y] (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    (hk3 : Nat.card π.ker = 3) (hX : commutator X = ⊤) {m' : ℕ} (hm' : ¬ 3 ∣ m')
    (hXcard : Nat.card X = 27 * m') {B : Subgroup X} {m : ℕ} (hm : ¬ 3 ∣ m)
    (hcard : Nat.card (B.map π) = 9 * m) : π.ker ≤ B := by
  rcases inf_ker_eq_bot_or_ker_le π hk3 B with h | hle
  swap
  · exact hle
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hBcard : Nat.card B = 9 * m := by rw [card_eq_of_inf_ker_eq_bot π h, hcard]
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 B))
    have hP : Nat.card P = 3 ^ 2 := card_sylow_three P hm (by rw [hBcard]; norm_num)
    have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb => by
      have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := (P : Subgroup B)) hP
      simpa using congrArg Subtype.val (mul_comm (⟨a, ha⟩ : (P : Subgroup B)) ⟨b, hb⟩)
    let P' : Subgroup X := (P : Subgroup B).map B.subtype
    have hP'3 : IsPGroup 3 P' :=
      P.isPGroup'.of_equiv ((P : Subgroup B).equivMapOfInjective B.subtype B.subtype_injective)
    obtain ⟨R, hPR⟩ := hP'3.exists_le_sylow
    obtain ⟨z, hzK, hzc, hz3⟩ := exists_central_order_three π hker hk3
    have hzR : z ∈ R := mem_sylow_three_of_central R hzc hz3
    have hRcard : Nat.card R = 3 ^ 3 := card_sylow_three R hm' (by rw [hXcard]; norm_num)
    have hkerR : π.ker ≤ (R : Subgroup X) := by
      have hzpow : Subgroup.zpowers z = π.ker := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzK) ?_
        rw [Nat.card_zpowers, hz3, hk3]
      rw [← hzpow]
      exact Subgroup.zpowers_le.mpr hzR
    have hR3 : Nat.card (R : Subgroup X) = 3 * Nat.card ((R : Subgroup X).map π) :=
      card_eq_three_mul_of_ker_le π hk3 hkerR
    have hRmap : Nat.card ((R : Subgroup X).map π) = 9 := by
      have : 3 * Nat.card ((R : Subgroup X).map π) = 27 := by rw [← hR3, hRcard]; norm_num
      omega
    have hP'map : Nat.card (P'.map π) = 9 := by
      have hinf : P' ⊓ π.ker = ⊥ := by
        refine eq_bot_iff.mpr ?_
        have hle : P' ⊓ π.ker ≤ B ⊓ π.ker :=
          inf_le_inf_right _ (Subgroup.map_subtype_le _)
        rw [h] at hle
        exact hle
      rw [← card_eq_of_inf_ker_eq_bot π hinf]
      have : Nat.card P' = Nat.card (P : Subgroup B) :=
        Nat.card_congr
          ((P : Subgroup B).equivMapOfInjective B.subtype B.subtype_injective).symm.toEquiv
      rw [this, hP]
      norm_num
    have hPR' : P'.map π ≤ (R : Subgroup X).map π := Subgroup.map_mono hPR
    have heq : P'.map π = (R : Subgroup X).map π :=
      Subgroup.eq_of_le_of_card_ge hPR' (by rw [hRmap, hP'map])
    have hRle : (R : Subgroup X) ≤ P' ⊔ π.ker := by
      intro r hr
      have h1 : π r ∈ (R : Subgroup X).map π := Subgroup.mem_map_of_mem π hr
      rw [← heq] at h1
      have hmem : r ∈ (P'.map π).comap π := h1
      rwa [Subgroup.comap_map_eq] at hmem
    have hRab : ∀ a ∈ (R : Subgroup X), ∀ b ∈ (R : Subgroup X), a * b = b * a := by
      intro a ha b hb
      obtain ⟨p, hp, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hRle ha)
      obtain ⟨p', hp', k', hk', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hRle hb)
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hp
      obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hp'
      have hkz := hker hk
      have hkz' := hker hk'
      have hpp' : Commute (B.subtype u) (B.subtype u') :=
        congrArg Subtype.val (hPab u hu u' hu')
      exact (Commute.mul_right (Commute.mul_left hpp' (Subgroup.mem_center_iff.mp hkz _).symm)
        (Commute.mul_left (Subgroup.mem_center_iff.mp hkz' _)
          (Subgroup.mem_center_iff.mp hkz' _))).eq
    have h1 := central_mem_commutator_eq_one_of_abelian_sylow R
      (fun a ha b hb => hRab a ha b hb) hzc hzR (by rw [hX]; exact Subgroup.mem_top z)
    rw [h1, orderOf_one] at hz3
    exact absurd hz3 (by norm_num)

end Cover

section Hat

theorem center_eq_bot_of_nonabelian {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hS
    have ha : a ∈ Subgroup.center S := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem isHat_of_central_cover {B S : Type} [Group B] [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (hB : commutator B = ⊤) (f : B →* S)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center B) (hk3 : Nat.card f.ker = 3) :
    IsHat B S := by
  have hcenter : Subgroup.center B = f.ker := by
    refine le_antisymm ?_ hker
    intro x hx
    rw [MonoidHom.mem_ker]
    have hfx : f x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨y, rfl⟩ := hf s
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx) y]
    rw [center_eq_bot_of_nonabelian hS, Subgroup.mem_bot] at hfx
    exact hfx
  let e : B ⧸ Subgroup.center B ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hsimple : IsSimpleGroup (B ⧸ Subgroup.center B) := e.isSimpleGroup
  refine ⟨⟨Group.isPerfect_def.mpr hB, hsimple, ?_⟩, ?_, ⟨e⟩⟩
  · obtain ⟨a, b, hab⟩ := hS
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  · rw [hcenter]
    exact hk3

theorem exists_normal_two_lift {B B' : Type} [Group B] [Finite B] [Group B'] [Finite B']
    (f : B →* B') (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center B)
    (hk3 : Nat.card f.ker = 3) (V' : Subgroup B') [V'.Normal] {k : ℕ}
    (hV' : Nat.card V' = 2 ^ k) :
    ∃ (V : Subgroup B) (_ : V.Normal), V.map f = V' ∧ Nat.card V = 2 ^ k ∧ V ⊓ f.ker = ⊥ := by
  classical
  let K : Subgroup B := V'.comap f
  have hKn : K.Normal := inferInstanceAs (V'.comap f).Normal
  have hKle : f.ker ≤ K := fun x hx => by
    show f x ∈ V'
    rw [MonoidHom.mem_ker.mp hx]
    exact V'.one_mem
  have hKmap : K.map f = V' := Subgroup.map_comap_eq_self_of_surjective hf V'
  have hKcard : Nat.card K = 3 * 2 ^ k := by
    rw [card_eq_three_mul_of_ker_le f hk3 hKle, hKmap, hV']
  have hNc : f.ker.subgroupOf K ≤ Subgroup.center ↥K := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hker hn)) g.1)
  have hNn : (f.ker.subgroupOf K).Normal := Subgroup.normal_of_le_center hNc
  have hNcard : Nat.card (f.ker.subgroupOf K) = 3 := by
    rw [← hk3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  have hNidx : (f.ker.subgroupOf K).index = 2 ^ k := by
    have h := Subgroup.card_mul_index (f.ker.subgroupOf K)
    rw [hNcard, hKcard] at h
    omega
  have hcop : Nat.Coprime (Nat.card (f.ker.subgroupOf K)) (f.ker.subgroupOf K).index := by
    rw [hNcard, hNidx]
    exact Nat.Coprime.pow_right k (by norm_num)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = 2 ^ k := by
    have h := hH.card_mul_card
    rw [hNcard, hKcard] at h
    omega
  let V : Subgroup B := H.map K.subtype
  have hVle : V ≤ K := Subgroup.map_subtype_le H
  have hVpow : ∀ x ∈ V, x ^ (2 ^ k) = 1 := by
    rintro _ ⟨h, hh, rfl⟩
    have h1 := pow_card_eq_one' (x := (⟨h, hh⟩ : ↥H))
    rw [hHcard] at h1
    have h2 := congrArg (fun y : ↥H => ((y : ↥K) : B)) h1
    simpa using h2
  have hchar : ∀ x ∈ K, x ^ (2 ^ k) = 1 → x ∈ V := by
    intro x hxK hx
    obtain ⟨⟨n, h⟩, hnh⟩ := hH.2 (⟨x, hxK⟩ : ↥K)
    have hnc : Commute (n : ↥K) (h : ↥K) :=
      (Subgroup.mem_center_iff.mp (hNc n.2) (h : ↥K)).symm
    have hxK' : ((n : ↥K) * (h : ↥K)) = ⟨x, hxK⟩ := hnh
    have h1 : ((n : ↥K) * (h : ↥K)) ^ (2 ^ k) = 1 := by
      rw [hxK']
      exact Subtype.ext hx
    have hhpow : (h : ↥K) ^ (2 ^ k) = 1 := by
      have := pow_card_eq_one' (x := (⟨(h : ↥K), h.2⟩ : ↥H))
      rw [hHcard] at this
      simpa using congrArg (fun y : ↥H => (y : ↥K)) this
    rw [hnc.mul_pow, hhpow, mul_one] at h1
    have hn3 : (n : ↥K) ^ 3 = 1 := by
      have := pow_card_eq_one' (x := (⟨(n : ↥K), n.2⟩ : ↥(f.ker.subgroupOf K)))
      rw [hNcard] at this
      simpa using congrArg (fun y : ↥(f.ker.subgroupOf K) => (y : ↥K)) this
    have hn1 : (n : ↥K) = 1 :=
      (pow_eq_one_iff_of_coprime (a := (n : ↥K)) (m := 2 ^ k) (n := 3)
        (Nat.Coprime.pow_left k (by norm_num))).mp ⟨h1, hn3⟩
    rw [hn1, one_mul] at hxK'
    exact ⟨(h : ↥K), h.2, by simpa using congrArg Subtype.val hxK'⟩
  have hVn : V.Normal := ⟨fun v hv g => by
    have hvK : v ∈ K := hVle hv
    have hgK : g * v * g⁻¹ ∈ K := hKn.conj_mem v hvK g
    refine hchar _ hgK ?_
    rw [conj_pow, hVpow v hv, mul_one, mul_inv_cancel]⟩
  have hVker : V ⊓ f.ker = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rintro x ⟨hxV, hxk⟩
    have h1 : x ^ (2 ^ k) = 1 := hVpow x hxV
    have h2 : x ^ 3 = 1 := by
      have := pow_card_eq_one' (x := (⟨x, hxk⟩ : ↥f.ker))
      rw [hk3] at this
      simpa using congrArg Subtype.val this
    exact (pow_eq_one_iff_of_coprime (a := x) (m := 2 ^ k) (n := 3)
      (Nat.Coprime.pow_left k (by norm_num))).mp ⟨h1, h2⟩
  have hVcard : Nat.card V = 2 ^ k := by
    rw [← hHcard]
    exact Nat.card_congr (H.equivMapOfInjective K.subtype K.subtype_injective).symm.toEquiv
  have hVmapcard : Nat.card V = Nat.card (V.map f) := card_eq_of_inf_ker_eq_bot f hVker
  have hVmap : V.map f = V' := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · calc V.map f ≤ K.map f := Subgroup.map_mono hVle
        _ = V' := hKmap
    · rw [← hVmapcard, hVcard, hV']
  exact ⟨V, hVn, hVmap, hVcard, hVker⟩

theorem isExt_hat_of_central_cover {B B' S : Type} [Group B] [Finite B] [Group B'] [Finite B']
    [Group S] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (hB : commutator B = ⊤)
    (f : B →* B') (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center B)
    (hk3 : Nat.card f.ker = 3) (V' : Subgroup B') [V'.Normal] {k : ℕ}
    (hV' : Nat.card V' = 2 ^ k) (e : B' ⧸ V' ≃* S) :
    ∃ (V : Subgroup B) (_ : V.Normal), Nonempty (↥V ≃* ↥V') ∧ IsHat (B ⧸ V) S := by
  obtain ⟨V, hVn, hVmap, hVcard, hVker⟩ := exists_normal_two_lift f hf hker hk3 V' hV'
  have hVle : V ≤ V'.comap f := fun v hv => by
    show f v ∈ V'
    rw [← hVmap]
    exact Subgroup.mem_map_of_mem f hv
  refine ⟨V, hVn, ⟨(mapEquivOfInfKerEqBot f hVker).trans (MulEquiv.subgroupCongr hVmap)⟩, ?_⟩
  let g : B ⧸ V →* S := e.toMonoidHom.comp (QuotientGroup.map V V' f hVle)
  have hg : Function.Surjective g := by
    intro s
    obtain ⟨q, rfl⟩ := e.surjective s
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, rfl⟩ := hf b'
    exact ⟨QuotientGroup.mk b, by simp [g]⟩
  have hdecomp : ∀ b : B, f b ∈ V' → ∃ z ∈ f.ker, ∃ v ∈ V, b = z * v := by
    intro b hb
    rw [← hVmap] at hb
    obtain ⟨v, hv, hvb⟩ := hb
    refine ⟨b * v⁻¹, ?_, v, hv, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hvb, mul_inv_cancel]
  have hgker : g.ker ≤ Subgroup.center (B ⧸ V) := by
    intro q hq
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : e (QuotientGroup.mk (f b)) = 1 := hq
    have h2 : (QuotientGroup.mk (f b) : B' ⧸ V') = 1 := by
      simpa using h1
    have hfb : f b ∈ V' := (QuotientGroup.eq_one_iff _).mp h2
    obtain ⟨z, hz, v, hv, rfl⟩ := hdecomp b hfb
    have hmk : (QuotientGroup.mk (z * v) : B ⧸ V) = QuotientGroup.mk z := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff v).mpr hv, mul_one]
    rw [hmk, Subgroup.mem_center_iff]
    intro c'
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp (hker hz)) c]
  have hBcard : Nat.card B = 3 * Nat.card B' := by
    have := Subgroup.card_ker_mul_card_of_surjective hf
    rw [hk3] at this
    exact this.symm
  have hB'card : Nat.card B' = Nat.card S * 2 ^ k := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V', hV']
    rw [Nat.card_congr e.toEquiv]
  have hquot : Nat.card (B ⧸ V) = 3 * Nat.card S := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [hVcard, hBcard, hB'card] at h1
    have hpos : 0 < 2 ^ k := by positivity
    have : Nat.card (B ⧸ V) * 2 ^ k = 3 * Nat.card S * 2 ^ k := by
      rw [← h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hgk3 : Nat.card g.ker = 3 := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hg
    rw [hquot] at h1
    have : Finite S := Finite.of_surjective g hg
    have hpos : 0 < Nat.card S := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hperf : Group.IsPerfect B := Group.isPerfect_def.mpr hB
  exact isHat_of_central_cover hS (Group.isPerfect_def.mp inferInstance) g hg hgker hgk3

end Hat

end CFSG.Quasithin.A38c14
