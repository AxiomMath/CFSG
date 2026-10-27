module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8T
public import CFSG.Quasithin.Vol2.Ch12Sec4C8Asm
public import CFSG.Quasithin.Background.E6Eighteen

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique S1248

@[expose] def AS_I_3_1_one_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H P L : Subgroup G), CFSG.SectionRank.IsSQTKCat ↥H →
    P ≤ H → IsPGroup 2 P → Id2519.IsTwoComponentIn L (H ⊓ Subgroup.centralizer (P : Set G)) →
    L ≤ Subgroup.centralizer (oddCoreIn H : Set G) →
    ∃ K : Subgroup G, IsComponentIn K H ∧ L ≤ ⨆ (p : G) (_ : p ∈ P), CFSG.conjugate K p

@[expose] def L2pEmbedFact1248 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K K₁ S : Subgroup Y) (p q : ℕ),
    QuasithinUnique.Ch1.IsFermatOrMersennePrime p →
    QuasithinUnique.Ch1.IsFermatOrMersennePrime q →
    CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 p 1 →
    CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K₁ .PSL 2 q 1 → K ≤ K₁ →
    IsSylowTwoOf S K₁ → S ≤ Subgroup.normalizer (K : Set Y) → K = K₁

namespace S1248

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_bot_of_le {X U U₀ : Subgroup G} (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hXN : X ≤ Subgroup.normalizer (U : Set G)) (hX3 : Nat.card X = 3)
    (hXU : ¬ X ≤ Subgroup.centralizer (U : Set G)) (hU₀ : U₀ ≤ U) (hidx : U₀.relIndex U = 2) :
    X ⊓ Subgroup.centralizer (U₀ : Set G) = ⊥ := by
  have hd : Nat.card ↥(X ⊓ Subgroup.centralizer (U₀ : Set G)) ∣ 3 :=
    hX3 ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
  · exact Subgroup.card_eq_one.1 h1
  exfalso
  have hXC : X ≤ Subgroup.centralizer (U₀ : Set G) :=
    (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hX3])).symm.le.trans inf_le_right
  apply hXU
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hx3 : x ^ 3 = 1 := by
    have := Subgroup.orderOf_dvd_natCard X hx
    rw [hX3] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hxU₀ : ∀ w ∈ U₀, x * w * x⁻¹ = w := fun w hw => by
    rw [(Subgroup.mem_centralizer_iff.1 (hXC hx) w hw).symm]
    group
  have hxu : x * u * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hXN hx) u).1 hu
  have hidx' : (U₀.subgroupOf U).index = 2 := hidx
  have hc : x * u * x⁻¹ * u⁻¹ ∈ U₀ := by
    by_cases huU : u ∈ U₀
    · rw [hxU₀ u huU, mul_inv_cancel]
      exact one_mem _
    · have hxuU₀ : x * u * x⁻¹ ∉ U₀ := fun h => huU (by
        have := hxU₀ _ h
        have e : u = x⁻¹ * (x * u * x⁻¹) * x := by group
        rw [e, show x⁻¹ * (x * u * x⁻¹) * x = x * u * x⁻¹ by
          calc x⁻¹ * (x * u * x⁻¹) * x = x⁻¹ * (x * (x * u * x⁻¹) * x⁻¹) * x := by rw [this]
            _ = x * u * x⁻¹ := by group]
        exact h)
      have hmem := (Subgroup.mul_mem_iff_of_index_two hidx'
        (a := (⟨x * u * x⁻¹, hxu⟩ : ↥U)) (b := (⟨u, hu⟩ : ↥U)⁻¹)).2
      have h' : (⟨x * u * x⁻¹, hxu⟩ : ↥U) * (⟨u, hu⟩ : ↥U)⁻¹ ∈ U₀.subgroupOf U := by
        apply hmem
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_inv]
        rw [Subgroup.inv_mem_iff]
        exact iff_of_false hxuU₀ huU
      exact h'
  set c := x * u * x⁻¹ * u⁻¹ with hcdef
  have hc2 : c * c = 1 := by rw [← sq]; exact hU2 c (hU₀ hc)
  have hxc : x * c * x⁻¹ = c := hxU₀ c hc
  have hx2 : x * x * u * (x * x)⁻¹ = u := by
    have e1 : x * u * x⁻¹ = c * u := by rw [hcdef]; group
    calc x * x * u * (x * x)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by group
      _ = x * (c * u) * x⁻¹ := by rw [e1]
      _ = (x * c * x⁻¹) * (x * u * x⁻¹) := by group
      _ = c * (c * u) := by rw [hxc, e1]
      _ = u := by rw [← mul_assoc, hc2, one_mul]
  have hx4 : x * x * x * x = x := by
    have e : x * x * x * x = x ^ 3 * x := by simp only [pow_succ, pow_zero, one_mul]
    rw [e, hx3, one_mul]
  have hx4u : x * u * x⁻¹ = u := by
    calc x * u * x⁻¹ = (x * x * x * x) * u * (x * x * x * x)⁻¹ := by rw [hx4]
      _ = (x * x) * ((x * x) * u * (x * x)⁻¹) * (x * x)⁻¹ := by group
      _ = u := by rw [hx2, hx2]
  calc u * x = x * u * x⁻¹ * x := by rw [hx4u]
    _ = x * u := by group

theorem relIndex_inf_conj {T L V U : Subgroup G} (hS : Setting G T L V U) {l : G}
    (hlV : l ∈ Subgroup.normalizer (V : Set G)) (hlU : l ∉ Subgroup.normalizer (U : Set G)) :
    (U ⊓ conjSubgroup U l).relIndex U = 2 := by
  have hUlV : conjSubgroup U l ≤ V := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hlV) (l * x * l⁻¹)).1 (hS.le hx)
    have e : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
    rwa [e] at h1
  have hVl : conjSubgroup V l = V := by
    exact QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.2 hlV
  have hidx : (conjSubgroup U l).relIndex V = 2 := by
    rw [← hVl, conjSubgroup, conjSubgroup,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj l⁻¹).injective]
    exact hS.hyper
  have hne : U ≠ conjSubgroup U l := by
    intro h
    apply hlU
    have := QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.1 h.symm
    exact this
  exact relIndex_inf_eq_two hS.le hUlV hS.hyper hidx hne

omit [Finite G] in
theorem le_centralizer_of_inverts {K O : Subgroup G} {z : G} (hz2 : z ^ 2 = 1)
    (hK : ⁅K, Subgroup.zpowers z⁆ = K) (hKO : K ≤ Subgroup.normalizer (O : Set G))
    (hinv : ∀ y ∈ O, z⁻¹ * y * z = y⁻¹) : K ≤ Subgroup.centralizer (O : Set G) := by
  have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
  have hinv' : ∀ y ∈ O, z * y * z⁻¹ = y⁻¹ := fun y hy => by
    have := hinv y hy
    rw [hzz] at this ⊢
    exact this
  rw [← hK, Subgroup.commutator_le]
  intro k hk w hw
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  have hzn : z ^ n = 1 ∨ z ^ n = z := by
    have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    rw [← zpow_mod_orderOf]
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · left
      rw [h, Nat.cast_one, Int.emod_one, zpow_zero]
    · rw [h]
      rcases Int.emod_two_eq_zero_or_one n with h' | h'
      · left
        rw [Nat.cast_two, h', zpow_zero]
      · right
        rw [Nat.cast_two, h', zpow_one]
  rcases hzn with h1 | hz
  · rw [h1, commutatorElement_one_right, one_mul, mul_one]
  · rw [hz]
    have hko : k⁻¹ * o⁻¹ * k ∈ O := by
      have := (Subgroup.mem_normalizer_iff.1 (hKO (K.inv_mem hk)) o⁻¹).1 (O.inv_mem ho)
      simpa using this
    have h1 : z * o * z⁻¹ = o⁻¹ := hinv' o ho
    have h2 : z * (k⁻¹ * o⁻¹ * k) * z⁻¹ = (k⁻¹ * o⁻¹ * k)⁻¹ := hinv' _ hko
    rw [commutatorElement_def]
    have key : k * z * k⁻¹ * z⁻¹ * o * (k * z * k⁻¹ * z⁻¹)⁻¹ = o := by
      calc k * z * k⁻¹ * z⁻¹ * o * (k * z * k⁻¹ * z⁻¹)⁻¹
          = k * z * k⁻¹ * (z⁻¹ * o * z) * k * z⁻¹ * k⁻¹ := by group
        _ = k * z * k⁻¹ * (z * o * z⁻¹) * k * z⁻¹ * k⁻¹ := by rw [hzz]
        _ = k * (z * (k⁻¹ * o⁻¹ * k) * z⁻¹) * k⁻¹ := by rw [h1]; group
        _ = o := by rw [h2]; group
    calc o * (k * z * k⁻¹ * z⁻¹) = (k * z * k⁻¹ * z⁻¹ * o * (k * z * k⁻¹ * z⁻¹)⁻¹) *
        (k * z * k⁻¹ * z⁻¹) := by rw [key]
      _ = k * z * k⁻¹ * z⁻¹ * o := by group

omit [Finite G] in
theorem eq_one_of_commute_simple {K : Subgroup G} (hK : IsSimpleGroup ↥K)
    (hKq : CFSG.IsQuasisimple ↥K) {c : G} (hcK : c ∈ K) (hc : ∀ y ∈ K, y * c = c * y) :
    c = 1 := by
  have hZ : Subgroup.center ↥K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hKq.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have hc : a' * b' = b' * a' := by
        have : a' ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top a'
        exact (Subgroup.mem_center_iff.1 this b').symm
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
  have hmem : (⟨c, hcK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

omit [Finite G] in
theorem comm_of_card_three {A : Subgroup G} (h : Nat.card A = 3) (a b : ↥A) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic ↥A := isCyclic_of_prime_card h
  exact IsCyclic.commGroup.mul_comm a b

omit [Finite G] in
theorem pow_three_of_card {A : Subgroup G} (h : Nat.card A = 3) (a : ↥A) : a ^ 3 = 1 := by
  rw [← h]
  exact pow_card_eq_one'

theorem three_le_pRank_of_commuting {N A B C : Subgroup G} (hA : A ≤ N) (hB : B ≤ N) (hC : C ≤ N)
    (hA3 : Nat.card A = 3) (hB3 : Nat.card B = 3) (hC3 : Nat.card C = 3)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hind : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1) :
    3 ≤ CFSG.Open.pRank 3 N := by
  classical
  have hcBC : ∀ (b : ↥B) (c : ↥C), Commute (B.subtype b) (C.subtype c) := fun b c =>
    hBC b b.2 c c.2
  let fBC : ↥B × ↥C →* G := MonoidHom.noncommCoprod B.subtype C.subtype hcBC
  have hfBC : ∀ x : ↥B × ↥C, fBC x = (x.1 : G) * x.2 := fun x => rfl
  have hcA : ∀ (a : ↥A) (x : ↥B × ↥C), Commute (A.subtype a) (fBC x) := by
    intro a x
    rw [hfBC]
    exact Commute.mul_right (hAB a a.2 x.1 x.1.2) (hAC a a.2 x.2 x.2.2)
  let f : ↥A × (↥B × ↥C) →* G := MonoidHom.noncommCoprod A.subtype fBC hcA
  have hf' : ∀ x : ↥A × (↥B × ↥C), f x = (x.1 : G) * ((x.2.1 : G) * x.2.2) := fun x => rfl
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b, c⟩ h
    have h' : (a : G) * ((b : G) * c) = 1 := (hf' (a, b, c)).symm.trans (MonoidHom.mem_ker.1 h)
    obtain ⟨ha, hb, hc⟩ := hind a a.2 b b.2 c c.2 (by rw [mul_assoc]; exact h')
    rw [Subgroup.mem_bot]
    ext <;> simp [ha, hb, hc]
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) ?_ ?_ ?_ f hf ?_
  · intro x y
    ext
    · exact congrArg Subtype.val (comm_of_card_three hA3 x.1 y.1)
    · exact congrArg Subtype.val (comm_of_card_three hB3 x.2.1 y.2.1)
    · exact congrArg Subtype.val (comm_of_card_three hC3 x.2.2 y.2.2)
  · intro x
    ext
    · exact congrArg Subtype.val (pow_three_of_card hA3 x.1)
    · exact congrArg Subtype.val (pow_three_of_card hB3 x.2.1)
    · exact congrArg Subtype.val (pow_three_of_card hC3 x.2.2)
  · rw [Nat.card_prod, Nat.card_prod, hA3, hB3, hC3]
    norm_num
  · rintro _ ⟨⟨a, b, c⟩, rfl⟩
    rw [hf']
    exact N.mul_mem (hA a.2) (N.mul_mem (hB b.2) (hC c.2))

omit [Finite G] in
theorem card_zpowers_of_orderOf {a : G} (ha : orderOf a = 3) :
    Nat.card (Subgroup.zpowers a) = 3 := by
  rw [Nat.card_zpowers, ha]

omit [Finite G] in
theorem isComponentIn_conj_of_normalizer {W J : Subgroup G}
    (hJ : IsComponentIn J (Subgroup.centralizer (W : Set G))) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    IsComponentIn (CFSG.conjugate J g) (Subgroup.centralizer (W : Set G)) := by
  have h := E6.isComponentIn_conjugate' hJ g
  rwa [QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.2 hg] at h

omit [Finite G] in
theorem isSimpleGroup_conjugate {J : Subgroup G} (hJ : IsSimpleGroup ↥J) (g : G) :
    IsSimpleGroup ↥(CFSG.conjugate J g) :=
  (J.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).symm.isSimpleGroup

omit [Finite G] in
theorem eq_one_of_mul_central {J : Subgroup G} (hs : IsSimpleGroup ↥J)
    (hq : CFSG.IsQuasisimple ↥J) {b d : G} (hb : b ∈ J) (hd : ∀ y ∈ J, y * d = d * y)
    (hdb : d * b = 1) : b = 1 := by
  have hb' : b = d⁻¹ := eq_inv_of_mul_eq_one_right hdb
  refine eq_one_of_commute_simple hs hq hb fun y hy => ?_
  rw [hb']
  have := hd y hy
  calc y * d⁻¹ = d⁻¹ * (d * y) * d⁻¹ := by group
    _ = d⁻¹ * (y * d) * d⁻¹ := by rw [this]
    _ = d⁻¹ * y := by group

omit [Finite G] in
theorem commute_of_commutator_eq_bot {J J' : Subgroup G} (h : ⁅J, J'⁆ = ⊥) {u v : G}
    (hu : u ∈ J) (hv : v ∈ J') : u * v = v * u :=
  (Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hu) v hv).symm

theorem eq_of_three_dvd (hev : CFSG.Open.evenRank G ≤ 2) {W X : Subgroup G} (hW2 : IsPGroup 2 W)
    (hW1 : W ≠ ⊥) (hXN : X ≤ Subgroup.normalizer (W : Set G)) (hX3 : Nat.card X = 3)
    (hXW : X ⊓ Subgroup.centralizer (W : Set G) = ⊥) {K' K'' : Subgroup G}
    (hK' : IsComponentIn K' (Subgroup.centralizer (W : Set G)))
    (hK'' : IsComponentIn K'' (Subgroup.centralizer (W : Set G)))
    (hs' : IsSimpleGroup ↥K') (hs'' : IsSimpleGroup ↥K'')
    (h3' : 3 ∣ Nat.card K') (h3'' : 3 ∣ Nat.card K'') : K' = K'' := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  set C := Subgroup.centralizer (W : Set G) with hCdef
  have hloc : IsTwoLocal (Subgroup.normalizer (W : Set G)) := ⟨W, hW1, hW2, rfl⟩
  have hbound : CFSG.Open.pRank 3 (Subgroup.normalizer (W : Set G)) ≤ 2 :=
    (A1b.pRank_le_evenRank Nat.prime_three (by norm_num) hloc).trans hev
  have hCN : C ≤ Subgroup.normalizer (W : Set G) := Subgroup.centralizer_le_normalizer _
  have hX3p : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hX3, pow_one])
  have hxX3 : ∀ x ∈ X, x ^ 3 = 1 := fun x hx => by
    have := Subgroup.orderOf_dvd_natCard X hx
    rw [hX3] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hmove : ∀ J, IsComponentIn J C → IsSimpleGroup ↥J → 3 ∣ Nat.card J →
      ∀ x ∈ X, x ∉ Subgroup.normalizer (J : Set G) → False := by
    intro J hJ hJs hJ3 x hx hxJ
    have hxW : x ∈ Subgroup.normalizer (W : Set G) := hXN hx
    set J₂ := CFSG.conjugate J x with hJ₂def
    set J₃ := CFSG.conjugate J₂ x with hJ₃def
    have hJ₂ : IsComponentIn J₂ C := isComponentIn_conj_of_normalizer hJ hxW
    have hJ₃ : IsComponentIn J₃ C := isComponentIn_conj_of_normalizer hJ₂ hxW
    have hs₂ : IsSimpleGroup ↥J₂ := isSimpleGroup_conjugate hJs x
    have hs₃ : IsSimpleGroup ↥J₃ := isSimpleGroup_conjugate hs₂ x
    have hq₁ := QuasithinUnique.BenderBranch.isQuasisimple_of_isComponentIn hJ
    have hq₂ := QuasithinUnique.BenderBranch.isQuasisimple_of_isComponentIn hJ₂
    have hq₃ := QuasithinUnique.BenderBranch.isQuasisimple_of_isComponentIn hJ₃
    have hx3 := hxX3 x hx
    have hJ₃e : J₃ = CFSG.conjugate J (x * x) :=
      QuasithinUnique.BenderBranch.conjugate_conjugate J x x
    have h12 : J ≠ J₂ := fun h =>
      hxJ (QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.1 h.symm)
    have h23 : J₂ ≠ J₃ := fun h => h12 (QuasithinUnique.BenderBranch.conjugate_inj.1 h)
    have h13 : J ≠ J₃ := fun h => hxJ (by
      have h' : CFSG.conjugate J (x * x) = J := by rw [← hJ₃e]; exact h.symm
      have hxx := QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.1 h'
      have e : x = (x * x) * (x * x) := by
        calc x = x ^ 3 * x := by rw [hx3, one_mul]
          _ = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul]; group
      rw [e]
      exact Subgroup.mul_mem _ hxx hxx)
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 hJ3
    have ha3 : orderOf (a : G) = 3 := by rw [Subgroup.orderOf_coe, ha]
    set a₂ := x⁻¹ * (a : G) * x with ha₂
    set a₃ := x⁻¹ * a₂ * x with ha₃
    have ha₂J : a₂ ∈ J₂ := by
      rw [hJ₂def, QuasithinUnique.BenderBranch.mem_conjugate_iff, ha₂]
      simp [mul_assoc]
    have ha₃J : a₃ ∈ J₃ := by
      rw [hJ₃def, QuasithinUnique.BenderBranch.mem_conjugate_iff, ha₃]
      simpa [mul_assoc] using ha₂J
    have ho₂ : orderOf a₂ = 3 := by
      rw [ha₂, show x⁻¹ * (a : G) * x = (MulAut.conj x⁻¹) (a : G) by simp,
        MulEquiv.orderOf_eq, ha3]
    have ho₃ : orderOf a₃ = 3 := by
      rw [ha₃, show x⁻¹ * a₂ * x = (MulAut.conj x⁻¹) a₂ by simp,
        MulEquiv.orderOf_eq, ho₂]
    have c12 := (QuasithinUnique.BenderBranch.eq_or_commute_of_isComponentIn hJ hJ₂).resolve_left
      h12
    have c13 := (QuasithinUnique.BenderBranch.eq_or_commute_of_isComponentIn hJ hJ₃).resolve_left
      h13
    have c23 := (QuasithinUnique.BenderBranch.eq_or_commute_of_isComponentIn hJ₂ hJ₃).resolve_left
      h23
    have hA : Subgroup.zpowers (a : G) ≤ J := Subgroup.zpowers_le.2 a.2
    have hB : Subgroup.zpowers a₂ ≤ J₂ := Subgroup.zpowers_le.2 ha₂J
    have hC : Subgroup.zpowers a₃ ≤ J₃ := Subgroup.zpowers_le.2 ha₃J
    have h := three_le_pRank_of_commuting (N := Subgroup.normalizer (W : Set G))
      ((hA.trans hJ.1).trans hCN) ((hB.trans hJ₂.1).trans hCN) ((hC.trans hJ₃.1).trans hCN)
      (card_zpowers_of_orderOf ha3) (card_zpowers_of_orderOf ho₂) (card_zpowers_of_orderOf ho₃)
      (fun u hu v hv => commute_of_commutator_eq_bot c12 (hA hu) (hB hv))
      (fun u hu v hv => commute_of_commutator_eq_bot c13 (hA hu) (hC hv))
      (fun u hu v hv => commute_of_commutator_eq_bot c23 (hB hu) (hC hv)) (by
        intro u hu v hv w hw huvw
        have hw1 : w = 1 := eq_one_of_mul_central hs₃ hq₃ (hC hw) (fun y hy => by
          have e1 := commute_of_commutator_eq_bot c13 (hA hu) hy
          have e2 := commute_of_commutator_eq_bot c23 (hB hv) hy
          calc y * (u * v) = u * y * v := by rw [← mul_assoc, ← e1]
            _ = u * v * y := by rw [mul_assoc, ← e2, ← mul_assoc]) huvw
        rw [hw1, mul_one] at huvw
        have hv1 : v = 1 := eq_one_of_mul_central hs₂ hq₂ (hB hv)
          (fun y hy => (commute_of_commutator_eq_bot c12 (hA hu) hy).symm) huvw
        rw [hv1, mul_one] at huvw
        exact ⟨huvw, hv1, hw1⟩)
    omega
  have hN' : X ≤ Subgroup.normalizer (K' : Set G) := fun x hx => by
    by_contra h
    exact hmove K' hK' hs' h3' x hx h
  have hN'' : X ≤ Subgroup.normalizer (K'' : Set G) := fun x hx => by
    by_contra h
    exact hmove K'' hK'' hs'' h3'' x hx h
  obtain ⟨a, ⟨haK, haX⟩, ha3⟩ := exists_orderOf_three_mem_centralizer hN' hX3p h3'
  obtain ⟨b, ⟨hbK, hbX⟩, hb3⟩ := exists_orderOf_three_mem_centralizer hN'' hX3p h3''
  have c12 := (QuasithinUnique.BenderBranch.eq_or_commute_of_isComponentIn hK' hK'').resolve_left
    hne
  have hq'' := QuasithinUnique.BenderBranch.isQuasisimple_of_isComponentIn hK''
  have hA : Subgroup.zpowers a ≤ K' := Subgroup.zpowers_le.2 haK
  have hB : Subgroup.zpowers b ≤ K'' := Subgroup.zpowers_le.2 hbK
  have haC : Subgroup.zpowers a ≤ Subgroup.centralizer (X : Set G) := Subgroup.zpowers_le.2 haX
  have hbC : Subgroup.zpowers b ≤ Subgroup.centralizer (X : Set G) := Subgroup.zpowers_le.2 hbX
  have h := three_le_pRank_of_commuting (N := Subgroup.normalizer (W : Set G))
    ((hA.trans hK'.1).trans hCN) ((hB.trans hK''.1).trans hCN) hXN
    (card_zpowers_of_orderOf ha3) (card_zpowers_of_orderOf hb3) hX3
    (fun u hu v hv => commute_of_commutator_eq_bot c12 (hA hu) (hB hv))
    (fun u hu v hv => (Subgroup.mem_centralizer_iff.1 (haC hu) v hv).symm)
    (fun u hu v hv => (Subgroup.mem_centralizer_iff.1 (hbC hu) v hv).symm) (by
      intro u hu v hv w hw huvw
      have hwC : w ∈ C := by
        have e : w = (u * v)⁻¹ := eq_inv_of_mul_eq_one_right huvw
        rw [e]
        exact C.inv_mem (C.mul_mem (hK'.1 (hA hu)) (hK''.1 (hB hv)))
      have hw1 : w = 1 := by
        have : w ∈ X ⊓ C := ⟨hw, hwC⟩
        rw [hXW, Subgroup.mem_bot] at this
        exact this
      rw [hw1, mul_one] at huvw
      have hv1 : v = 1 := eq_one_of_mul_central hs'' hq'' (hB hv)
        (fun y hy => (commute_of_commutator_eq_bot c12 (hA hu) hy).symm) huvw
      rw [hv1, mul_one] at huvw
      exact ⟨huvw, hv1, hw1⟩)
  omega

end S1248

open S1248

theorem comp1248Lift_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (hpre : Pre1242) (hinv : InvolFact1248) (h68 : E6.E68Stmt) (hlist : Lemma115_3_List)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hKF : KnownFacts15122Types)
    (hKG1 : L32ListFact1248) (hKG2 : L33ExclusionFact) (hKG3 : HatA67Fact1248)
    (hI31 : AS_I_3_1_one_two) (hKG5 : L2pEmbedFact1248) : Comp1248Lift := by
  intro G _ _ T L V U hS X hXLU hX3 hXC l hl hlU hl2 K hK hKp
  classical
  obtain ⟨z, hF⟩ := S1248.exists_facts h331 h1222 h323 h3228 hpre hS
  have hyp := hS.cx.hyp
  have := hyp.simple
  have hev : CFSG.Open.evenRank G ≤ 2 := hyp.qtke.2.2
  set U₀ := U ⊓ conjSubgroup U l with hU₀def
  have hU₀U : U₀ ≤ U := inf_le_left
  have hidx : U₀.relIndex U = 2 := relIndex_inf_conj hS hl.1 hlU
  have hW₀ : U₀ = U ∨ (U₀ ≤ U ∧ U₀.relIndex U = 2) := Or.inr ⟨hU₀U, hidx⟩
  have hWU : U = U ∨ (U ≤ U ∧ U.relIndex U = 2) := Or.inl rfl
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := fun u hu => hF.cx.sq u (hS.le hu)
  have hXNU : X ≤ Subgroup.normalizer (U : Set G) := hXLU.trans inf_le_right
  have hXNUl : X ≤ Subgroup.normalizer ((conjSubgroup U l : Subgroup G) : Set G) := by
    intro x hx
    have hlx : l * x * l⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hl.2 x).1 hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    have h1 := Subgroup.mem_normalizer_iff.1 (hXNU hlx) (l * y * l⁻¹)
    have e : l * (x * y * x⁻¹) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) * (l * x * l⁻¹)⁻¹ := by
      group
    rw [e]
    exact h1
  have hXNU₀ : X ≤ Subgroup.normalizer (U₀ : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXNU hx, hXNUl hx⟩
  have hXU₀ : X ⊓ Subgroup.centralizer (U₀ : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_le hU2 hXNU hX3 hXC hU₀U hidx
  have hXU : X ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
    have hd : Nat.card ↥(X ⊓ Subgroup.centralizer (U : Set G)) ∣ 3 :=
      hX3 ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exact absurd ((Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [h3, hX3])).symm.le.trans inf_le_right) hXC
  have htype : ∀ {W : Subgroup G}, (W = U ∨ (W ≤ U ∧ W.relIndex U = 2)) →
      X ≤ Subgroup.normalizer (W : Set G) → X ⊓ Subgroup.centralizer (W : Set G) = ⊥ →
      ∀ J, IsComponentIn J (Subgroup.centralizer (W : Set G)) → IsSimpleGroup ↥J ∧
        3 ∣ Nat.card J ∧ ∃ q : ℕ, QuasithinUnique.Ch1.IsFermatOrMersennePrime q ∧
          CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥J .PSL 2 q 1 := by
    intro W hW hXN hXW J hJ
    obtain ⟨hs, q, hq, hqsl⟩ :=
      hF.comp_type_core hinv h68 hlist hF318 h36 h38 hKF hKG1 hKG2 hKG3 hW hXN hX3 hXW hJ
    exact ⟨hs, three_dvd_card_psl2 hqsl, q, hq, hqsl⟩
  have hT2 : IsPGroup 2 V := hyp.sylow.1.to_le hF.cx.le_T
  have huniq : ∀ {W : Subgroup G}, (W = U ∨ (W ≤ U ∧ W.relIndex U = 2)) →
      X ≤ Subgroup.normalizer (W : Set G) → X ⊓ Subgroup.centralizer (W : Set G) = ⊥ →
      ∀ J J', IsComponentIn J (Subgroup.centralizer (W : Set G)) →
        IsComponentIn J' (Subgroup.centralizer (W : Set G)) → J = J' := by
    intro W hW hXN hXW J J' hJ hJ'
    have hWU' : W ≤ U := by
      rcases hW with rfl | ⟨h, -⟩
      · exact le_rfl
      · exact h
    have h1 := htype hW hXN hXW J hJ
    have h2 := htype hW hXN hXW J' hJ'
    exact eq_of_three_dvd hev (hT2.to_le (hWU'.trans hS.le)) (hF.mem_gamma hinv hW).2.1 hXN hX3
      hXW hJ hJ' h1.1 h2.1 h1.2.1 h2.2.1
  have h115₀ := hF.lemma115Hyp hinv hW₀
  have h115 := hF.lemma115Hyp hinv hWU
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQ₀ : IsSylowTwoOf Q (Subgroup.centralizer (U₀ : Set G)) := h115₀.sylow
  have hQU : IsSylowTwoOf Q (Subgroup.centralizer (U : Set G)) := h115.sylow
  obtain ⟨-, hKz, -, -⟩ := h115.component_action hK
  have hKO : K ≤ Subgroup.centralizer
      (oddCoreIn (Subgroup.centralizer (U₀ : Set G)) : Set G) := by
    refine le_centralizer_of_inverts hF.z_sq hKz ?_ h115₀.inverts_oddCoreIn
    exact (hK.1.trans (Subgroup.centralizer_le hU₀U)).trans (le_normalizer_oddCoreIn _)
  have hq := qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hSQ : CFSG.SectionRank.IsSQTKCat ↥(Subgroup.centralizer (U₀ : Set G)) :=
    hq.1 _ h115₀.pCore_ne_bot
  have hUH₀ : U ≤ Subgroup.centralizer (U₀ : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 (hF.V_le_centralizer (hS.le hu)) w (hS.le (hU₀U hw)))
  have hKq := QuasithinUnique.BenderBranch.isQuasisimple_of_isComponentIn hK
  have hK2 : Id2519.IsTwoComponentIn K
      (Subgroup.centralizer (U₀ : Set G) ⊓ Subgroup.centralizer (U : Set G)) := by
    rw [inf_eq_right.2 (Subgroup.centralizer_le hU₀U)]
    exact Id2519.isTwoComponentIn_of_isComponentIn hK (E6.two_dvd_card_of_isQuasisimple hKq)
  obtain ⟨K₁, hK₁, hKK₁⟩ := hI31 G (Subgroup.centralizer (U₀ : Set G)) U K hSQ hUH₀
    (hT2.to_le hS.le) hK2 hKO
  have hVQ : V ≤ Q := le_inf hF.cx.le_T hF.V_le_centralizer
  have hVZ : V ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.le_centralizer_iff.1 inf_le_right
  have hUN : ∀ u ∈ U, CFSG.conjugate K₁ u = K₁ := fun u hu =>
    QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.2
      (E6.mem_normalizer_of_mem_center_sylow hQ₀ hK₁ (hVQ (hS.le hu)) (hVZ (hS.le hu)))
  have hKK₁' : K ≤ K₁ := hKK₁.trans (iSup₂_le fun u hu => (hUN u hu).le)
  obtain ⟨-, -, q, hq', hqsl⟩ := htype hW₀ hXNU₀ hXU₀ K₁ hK₁
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    have hKg := Unc25G2.isComponentIn_conjugate hK (hQU.1 hg)
    exact QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.1
      (huniq hWU hXNU hXU _ _ hKg hK)
  have hS₁ : IsSylowTwoOf (Q ⊓ K₁) K₁ := E6.isSylowTwoOf_inf_of_subnormal' hQ₀ hK₁.1 hK₁.2.2
  obtain ⟨p, hp, hpsl⟩ := hKp
  have hKe : K = K₁ :=
    hKG5 G K K₁ (Q ⊓ K₁) p q hp hq' hpsl hqsl hKK₁' hS₁ (inf_le_left.trans hQK)
  refine ⟨hKe ▸ hK₁, fun K' hK' _ => ?_⟩
  rw [hKe]
  exact huniq hW₀ hXNU₀ hXU₀ K' K₁ hK' hK₁

end CFSG.Quasithin.H13
