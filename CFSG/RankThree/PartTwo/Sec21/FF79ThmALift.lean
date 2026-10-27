module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open scoped Pointwise

theorem exists_fixed_involution {F : Type} [Group F] [Finite F] (σ : F →* F)
    (hσ : ∀ x, σ (σ (σ x)) = x) {m : ℕ} (hF : Nat.card F = 2 * m) (hm2 : ¬ 2 ∣ m)
    (hm3 : ¬ 3 ∣ m) :
    ∃ ζ : F, orderOf ζ = 2 ∧ σ ζ = ζ ∧
      ∀ w : F, orderOf w = 2 → ∃ f : F, f * w * f⁻¹ = ζ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := F)
    omega
  have hord_zpow : ∀ w z : F, orderOf w = 2 → orderOf z = 2 → z ∈ Subgroup.zpowers w → z = w := by
    intro w z hw hz hzw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzw
    rw [← zpow_mod_orderOf, hw] at hz ⊢
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [Nat.cast_ofNat, h] at hz
      simp at hz
    · rw [Nat.cast_ofNat, h]; simp
  have hsyl : ∀ s : F, orderOf s = 2 →
      Nat.card (Subgroup.zpowers s) = 2 ^ (Nat.card F).factorization 2 := by
    intro s hs
    rw [Nat.card_zpowers, hs, hF, Nat.factorization_mul (by norm_num) hm0,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hm2,
      Nat.Prime.factorization_self Nat.prime_two]
    simp
  have hconj : ∀ t w : F, orderOf t = 2 → orderOf w = 2 → ∃ f : F, f * t * f⁻¹ = w := by
    intro t w ht hw
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F (Sylow.ofCard _ (hsyl t ht))
      (Sylow.ofCard _ (hsyl w hw))
    have h1 : g * t * g⁻¹ ∈ ((g • Sylow.ofCard _ (hsyl t ht) : Sylow 2 F) : Subgroup F) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul (G := F) t (MulAut.conj g) _ (Subgroup.mem_zpowers t)
    rw [hg] at h1
    refine ⟨g, hord_zpow w _ hw ?_ h1⟩
    rw [← ht]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t)
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := F) 2
    (by rw [hF]; exact dvd_mul_right 2 m)
  have hinj : Function.Injective σ := fun x y h => by
    have := congrArg (fun z => σ (σ z)) h
    simpa [hσ] using this
  have hσord : ∀ x, orderOf (σ x) = orderOf x := orderOf_injective σ hinj
  have hcardS : Nat.card {x : F // orderOf x = 2} ∣ m := by
    set c : ConjAct F := ConjAct.toConjAct t₀ with hc
    have hO : MulAction.orbit (ConjAct F) t₀ = {x | orderOf x = 2} := by
      ext x
      rw [ConjAct.mem_orbit_conjAct, isConj_iff]
      constructor
      · rintro ⟨f, hf⟩
        show orderOf x = 2
        have key : orderOf (f * x * f⁻¹) = orderOf x :=
          orderOf_injective (MulAut.conj f).toMonoidHom (MulAut.conj f).injective x
        rw [← key, hf, ht₀]
      · intro hx
        obtain ⟨f, hf⟩ := hconj x t₀ hx ht₀
        exact ⟨f, hf⟩
    have hcF : Nat.card (ConjAct F) = 2 * m := hF ▸ Nat.card_congr ConjAct.toConjAct.toEquiv.symm
    have hco : orderOf c = 2 := by
      rw [← ht₀]
      exact orderOf_injective (ConjAct.toConjAct : F ≃* ConjAct F).toMonoidHom
        (ConjAct.toConjAct : F ≃* ConjAct F).injective t₀
    have hle : Subgroup.zpowers c ≤ MulAction.stabilizer (ConjAct F) t₀ := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, hc, ConjAct.smul_def]
      simp
    have h1 := MulAction.index_stabilizer (ConjAct F) t₀
    have h2 := Subgroup.index_dvd_of_le hle
    have h3 : (Subgroup.zpowers c).index = m := by
      have := Subgroup.index_mul_card (H := Subgroup.zpowers c)
      rw [Nat.card_zpowers, hco, hcF] at this
      omega
    rw [h3] at h2
    rw [h1, hO] at h2
    rw [← Nat.card_coe_set_eq] at h2
    exact h2
  haveI : Fintype F := Fintype.ofFinite F
  let e : Equiv.Perm F := ⟨σ, fun x => σ (σ x), fun x => hσ x, fun x => hσ x⟩
  let e' : Equiv.Perm {x : F // orderOf x = 2} :=
    e.subtypePerm (fun x => by show orderOf (σ x) = 2 ↔ _; rw [hσord])
  let f : Function.End {x : F // orderOf x = 2} := fun x => e' x
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [pow_one, pow_succ, pow_succ, pow_one]
    funext x
    apply Subtype.ext
    exact hσ x.1
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  have hS3 : ¬ 3 ∣ Nat.card {x : F // orderOf x = 2} := fun h => hm3 (h.trans hcardS)
  have hpos : 0 < Fintype.card f.fixedPoints := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [h0, ← Nat.card_eq_fintype_card] at hmod
    exact hS3 ((Nat.modEq_zero_iff_dvd).mp hmod)
  obtain ⟨⟨ζ, hζ⟩, hfix⟩ := Fintype.card_pos_iff.mp hpos
  refine ⟨ζ, hζ, ?_, fun w hw => hconj w ζ hw hζ⟩
  have := congrArg Subtype.val hfix
  simpa [f, e', e] using this

theorem exists_lift_element {H : Type} [Group H] [Finite H] {Ē : Type} [Group Ē]
    (ρ : H →* Ē) (σ : H →* H) (hσ : ∀ x, σ (σ (σ x)) = x) (β : Ē →* Ē)
    (hρσ : ∀ h, ρ (σ h) = β (ρ h)) (hodd : Odd (Nat.card ρ.ker)) (h3 : ¬ 3 ∣ Nat.card ρ.ker)
    (y : H) {q : Ē} (hy : ρ y = q) (hβq : β (q ^ 2) = q ^ 2) (hq2 : q ^ 2 ≠ 1) (hq4 : q ^ 4 = 1) :
    ∃ p : H, p ^ 4 = 1 ∧ p ^ 2 ≠ 1 ∧ σ (p ^ 2) = p ^ 2 := by
  classical
  have hord : orderOf (q ^ 2) = 2 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 0) (x := q ^ 2) (by simpa using hq2)
      (by rw [← pow_mul]; simpa using hq4)
    simpa using this
  set F : Subgroup H := (Subgroup.zpowers (q ^ 2)).comap ρ with hFdef
  have hmemF : ∀ x, x ∈ F ↔ ρ x ∈ Subgroup.zpowers (q ^ 2) := fun x => Iff.rfl
  have hσF : ∀ x ∈ F, σ x ∈ F := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hmemF x).mp hx)
    rw [hmemF, hρσ, ← hk, map_zpow, hβq]
    exact zpow_mem (Subgroup.mem_zpowers _) _
  let σF : F →* F := (σ.comp F.subtype).codRestrict F (fun x => hσF x x.2)
  have hσF3 : ∀ x, σF (σF (σF x)) = x := fun x => Subtype.ext (hσ x.1)
  let ρF : F →* Ē := ρ.comp F.subtype
  have hrange : ρF.range = Subgroup.zpowers (q ^ 2) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact x.2
    · intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hy2 : y ^ 2 ∈ F := by
        rw [hmemF, map_pow, hy]
        exact Subgroup.mem_zpowers _
      refine ⟨(⟨y ^ 2, hy2⟩ : F) ^ k, ?_⟩
      simp [ρF, hy]
  have hkerle : ρF.ker.map F.subtype ≤ ρ.ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hdvd : Nat.card ρF.ker ∣ Nat.card ρ.ker := by
    have := Subgroup.card_dvd_of_le hkerle
    rwa [Subgroup.card_map_of_injective F.subtype_injective] at this
  have hcardF : Nat.card F = 2 * Nat.card ρF.ker := by
    have := Subgroup.card_ker_mul_card_range ρF
    rw [hrange, Nat.card_zpowers, hord] at this
    omega
  obtain ⟨ζ, hζ, hζσ, hζc⟩ := exists_fixed_involution σF hσF3 hcardF
    (fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd)))
    (fun h => h3 (h.trans hdvd))
  set m₀ := Nat.card ρ.ker with hm₀
  have hy4 : y ^ 4 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hy, hq4]
  have hy4m : y ^ (4 * m₀) = 1 := by
    have h1 : (⟨y ^ 4, hy4⟩ : ρ.ker) ^ m₀ = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [pow_mul]
    exact h2
  obtain ⟨k, hk⟩ := hodd
  have hρw : ρ ((y ^ m₀) ^ 2) = q ^ 2 := by
    rw [map_pow, map_pow, hy, ← pow_mul, mul_comm, pow_mul, hk, pow_succ, pow_mul,
      show (q ^ 2) ^ 2 = 1 by rw [← pow_mul]; exact hq4]
    simp
  have hwF : (y ^ m₀) ^ 2 ∈ F := by
    rw [hmemF, hρw]
    exact Subgroup.mem_zpowers _
  have hw1 : (⟨(y ^ m₀) ^ 2, hwF⟩ : F) ≠ 1 := fun h => hq2 (by
    rw [← hρw]
    have := congrArg Subtype.val h
    simpa using congrArg ρ this)
  have hw2 : (⟨(y ^ m₀) ^ 2, hwF⟩ : F) ^ 2 = 1 := by
    apply Subtype.ext
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow]
    rw [← pow_mul, ← pow_mul, ← hy4m]
    congr 1
    ring
  obtain ⟨f, hf⟩ := hζc _ (orderOf_eq_prime hw2 hw1)
  have hf' : (f : H) * (y ^ m₀) ^ 2 * (f : H)⁻¹ = (ζ : H) := congrArg Subtype.val hf
  have hζ2 : ζ ^ 2 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hp2 : ((f : H) * y ^ m₀ * (f : H)⁻¹) ^ 2 = (ζ : H) := by
    rw [conj_pow]; exact hf'
  refine ⟨(f : H) * y ^ m₀ * (f : H)⁻¹, ?_, ?_, ?_⟩
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hp2, ← SubmonoidClass.coe_pow, hζ2]
    rfl
  · rw [hp2]
    intro h
    have : ζ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hζ
    omega
  · rw [hp2]
    exact congrArg Subtype.val hζσ

theorem mem_normalizer_of_conj_le {G : Type} [Group G] [Finite G] (U : Subgroup G) (y : G)
    (h : ∀ a ∈ U, y * a * y⁻¹ ∈ U) : y ∈ Subgroup.normalizer (U : Set G) := by
  have hle : U.map (MulAut.conj y).toMonoidHom ≤ U := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have heq : U.map (MulAut.conj y).toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj y).injective).symm)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨h a, fun ha => ?_⟩
  rw [← heq] at ha
  obtain ⟨a', ha', h'⟩ := ha
  have : y * a' * y⁻¹ = y * a * y⁻¹ := h'
  have : a' = a := by simpa using this
  exact this ▸ ha'

theorem inf_eq_bot_of_isPGroup_three {G : Type} [Group G] [Finite G] (N : Subgroup G)
    (U : Subgroup G) (hU : IsPGroup 3 U) (hN : ¬ 3 ∣ Nat.card N) : U ⊓ N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro z ⟨hzU, hzN⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU) ⟨z, hzU⟩
  have h1 : orderOf z = 3 ^ k := by rw [← hk]; exact Subgroup.orderOf_coe (⟨z, hzU⟩ : U)
  have h2 : orderOf z ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hzN
    exact this
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, orderOf_eq_one_iff] at h1
    exact h1
  · exact absurd (dvd_trans (h1 ▸ dvd_pow_self 3 hk0.ne') h2) hN

theorem exists_normalizing_coset {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (U : Subgroup G) (hU : IsPGroup 3 U) (hN : ¬ 3 ∣ Nat.card N) (x : G)
    (hx : ∀ u ∈ U, ∃ u' ∈ U, x * u * x⁻¹ * u'⁻¹ ∈ N) :
    ∃ o ∈ N, o * x ∈ Subgroup.normalizer (U : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V : Subgroup G := U ⊔ N with hV
  have hUV : U ≤ V := le_sup_left
  have hNV : N ≤ V := le_sup_right
  set Q : Subgroup G := U.map (MulAut.conj x).toMonoidHom with hQ
  have hQV : Q ≤ V := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨u', hu', hn⟩ := hx u hu
    have : (MulAut.conj x).toMonoidHom u = (x * u * x⁻¹ * u'⁻¹) * u' := by
      simp [MulAut.conj_apply]
    rw [this]
    exact Subgroup.mul_mem _ (hNV hn) (hUV hu')
  have hcardQ : Nat.card Q = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hbot := inf_eq_bot_of_isPGroup_three N U hU hN
  have hcardV : Nat.card V = Nat.card U * Nat.card N := by
    have h1 : N.relIndex V = N.relIndex U := Subgroup.relIndex_sup_right U N
    have h2 : N.relIndex U = Nat.card U := by
      have : N.subgroupOf U = ⊥ := by
        ext ⟨a, ha⟩
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.mk_eq_one]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have : a ∈ U ⊓ N := ⟨ha, h⟩
          rw [hbot] at this
          exact this
        · rw [h]; exact N.one_mem
      rw [Subgroup.relIndex, this, Subgroup.index_bot]
    have h3 := Subgroup.card_mul_index (H := N.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNV).toEquiv] at h3
    have h4 : Nat.card V = Nat.card N * N.relIndex V := h3.symm
    rw [h4, h1, h2, mul_comm]
  have hidx : ∀ R : Subgroup G, R ≤ V → Nat.card R = Nat.card U →
      (R.subgroupOf V).index = Nat.card N := by
    intro R hR hc
    have h1 := Subgroup.index_mul_card (H := R.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv, hc, hcardV] at h1
    have hUpos : 0 < Nat.card U := Nat.card_pos
    rw [mul_comm (Nat.card U)] at h1
    exact Nat.eq_of_mul_eq_mul_right hUpos h1
  have hP1 : IsPGroup 3 (U.subgroupOf V) := hU.comap_subtype
  have hP2 : IsPGroup 3 (Q.subgroupOf V) := (hU.map _).comap_subtype
  let S1 : Sylow 3 V := hP1.toSylow (by rw [hidx U hUV rfl]; exact hN)
  let S2 : Sylow 3 V := hP2.toSylow (by rw [hidx Q hQV hcardQ]; exact hN)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq V S2 S1
  have hg' : ∀ z : V, z ∈ U.subgroupOf V ↔ g⁻¹ * z * g ∈ Q.subgroupOf V := by
    intro z
    have h1 := congrArg (fun T : Sylow 3 V => (T : Subgroup V)) hg
    simp only [Sylow.coe_subgroup_smul] at h1
    have h2 : (U.subgroupOf V) = MulAut.conj g • (Q.subgroupOf V) := h1.symm
    rw [h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  obtain ⟨u₀, hu₀, o, ho, hgo⟩ := Subgroup.mem_sup_of_normal_right.mp g.2
  refine ⟨o, ho, ?_⟩
  have key : ∀ a ∈ U, (o * x)⁻¹ * a * (o * x) ∈ U := by
    intro a ha
    have hz : u₀ * a * u₀⁻¹ ∈ U := U.mul_mem (U.mul_mem hu₀ ha) (U.inv_mem hu₀)
    have h1 := (hg' ⟨u₀ * a * u₀⁻¹, hUV hz⟩).mp hz
    obtain ⟨u, hu, hux⟩ := (Subgroup.mem_subgroupOf.mp h1)
    have h2 : x * u * x⁻¹ = o⁻¹ * a * o := by
      have := hux
      simp only [MonoidHom.coe_coe, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        MulEquiv.coe_toMonoidHom, ← hgo] at this
      rw [this]; group
    have h3 : u = x⁻¹ * (x * u * x⁻¹) * x := by group
    rw [h3, h2] at hu
    simpa [mul_assoc] using hu
  have := mem_normalizer_of_conj_le U (o * x)⁻¹ (by simpa using key)
  simpa using (Subgroup.inv_mem _ this)

theorem ff79_lift_square {G : Type} [Group G] [Finite G] {L U : Subgroup G} (hUL : U ≤ L)
    (hU3 : IsPGroup 3 U) {Ē : Type} [Group Ē] (π : ↥L →* Ē)
    (hodd : Odd (Nat.card π.ker)) (h3 : ¬ 3 ∣ Nat.card π.ker)
    {b : G} (hb : b ^ 3 = 1) (hbL : b ∈ Nor L) (hbU : b ∈ Nor U) (β : Ē →* Ē)
    (hβ : ∀ (l : G) (hl : l ∈ L) (hl' : b * l * b⁻¹ ∈ L),
      π ⟨b * l * b⁻¹, hl'⟩ = β (π ⟨l, hl⟩))
    {q : Ē} (hq : q ∈ π.range)
    (hqU : ∀ (u : G) (hu : u ∈ U), ∃ (u' : G) (hu' : u' ∈ U),
      q * π ⟨u, hUL hu⟩ * q⁻¹ = π ⟨u', hUL hu'⟩)
    (hβq : β (q ^ 2) = q ^ 2) (hq2 : q ^ 2 ≠ 1) (hq4 : q ^ 4 = 1) :
    ∃ p ∈ L, p ∈ Nor U ∧ p ^ 4 = 1 ∧ p ^ 2 ≠ 1 ∧ b * p ^ 2 * b⁻¹ = p ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconjL : ∀ l, l ∈ L → b * l * b⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hbL l).mp hl
  have hconjU : ∀ u, u ∈ U → b * u * b⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hbU u).mp hu
  have hconjU' : ∀ u, u ∈ U → b⁻¹ * u * b ∈ U := fun u hu => by
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hbU (b⁻¹ * u * b)).mpr
      (by simpa [mul_assoc] using hu)
  let Ũ : Subgroup ↥L := U.subgroupOf L
  obtain ⟨x₀, hx₀⟩ := hq
  obtain ⟨o, ho, hy⟩ : ∃ o ∈ π.ker, o * x₀ ∈ Subgroup.normalizer (Ũ : Set ↥L) := by
    refine exists_normalizing_coset π.ker Ũ hU3.comap_subtype h3 x₀ ?_
    intro u hu
    obtain ⟨u', hu', hqu⟩ := hqU u.1 hu
    refine ⟨⟨u', hUL hu'⟩, hu', ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hx₀, hqu]
    simp
  set y : ↥L := o * x₀ with hydef
  have hπy : π y = q := by
    rw [hydef, map_mul, MonoidHom.mem_ker.mp ho, one_mul, hx₀]
  let H : Subgroup ↥L := Subgroup.normalizer (Ũ : Set ↥L)
  let σ₀ : ↥L →* ↥L :=
    { toFun := fun l => ⟨b * l.1 * b⁻¹, hconjL l.1 l.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun l₁ l₂ => by apply Subtype.ext; simp [mul_assoc] }
  have hσ₀H : ∀ l ∈ H, σ₀ l ∈ H := by
    intro l hl
    apply mem_normalizer_of_conj_le
    intro a ha
    have ha1 : b⁻¹ * a.1 * b ∈ U := hconjU' a.1 ha
    have hmem : (⟨b⁻¹ * a.1 * b, hUL ha1⟩ : ↥L) ∈ Ũ := ha1
    have h1 := (Subgroup.mem_normalizer_iff.mp hl _).mp hmem
    have h2 := hconjU _ h1
    have h3' : b * (l.1 * (b⁻¹ * a.1 * b) * l.1⁻¹) * b⁻¹ = b * l.1 * b⁻¹ * a.1 * (b * l.1 * b⁻¹)⁻¹
      := by group
    show (b * l.1 * b⁻¹ * a.1 * (b * l.1 * b⁻¹)⁻¹) ∈ U
    rw [← h3']
    exact h2
  let σ : H →* H := (σ₀.comp H.subtype).codRestrict H (fun x => hσ₀H x x.2)
  have hσ : ∀ x, σ (σ (σ x)) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    show b * (b * (b * x.1.1 * b⁻¹) * b⁻¹) * b⁻¹ = x.1.1
    have hb3 : b * b * b = 1 := by rw [← hb, pow_succ, pow_succ, pow_one]
    have : b * (b * (b * x.1.1 * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * x.1.1 * (b * b * b)⁻¹ := by
      group
    rw [this, hb3]; simp
  let ρ : H →* Ē := π.comp H.subtype
  have hρσ : ∀ h, ρ (σ h) = β (ρ h) := fun h => hβ h.1.1 h.1.2 _
  have hkerle : ρ.ker.map H.subtype ≤ π.ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hdvd : Nat.card ρ.ker ∣ Nat.card π.ker := by
    have := Subgroup.card_dvd_of_le hkerle
    rwa [Subgroup.card_map_of_injective H.subtype_injective] at this
  obtain ⟨p, hp4, hp2, hσp⟩ := exists_lift_element ρ σ hσ β hρσ (hodd.of_dvd_nat hdvd)
    (fun h => h3 (h.trans hdvd)) ⟨y, hy⟩ hπy hβq hq2 hq4
  have hpN : (p : ↥L) ∈ Subgroup.normalizer (Ũ : Set ↥L) := p.2
  have hpL : ((p : ↥L) : G) ∈ L := SetLike.coe_mem _
  refine ⟨((p : ↥L) : G), hpL, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact (Subgroup.mem_normalizer_iff.mp hpN ⟨h, hUL hh⟩).mp hh
    · intro hh
      have hhL : h ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem hpL) (hUL hh)) hpL
        simpa [mul_assoc] using this
      exact (Subgroup.mem_normalizer_iff.mp hpN ⟨h, hhL⟩).mpr hh
  · have := congrArg (fun z : H => ((z : ↥L) : G)) hp4
    simpa using this
  · intro h
    apply hp2
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · have := congrArg (fun z : H => ((z : ↥L) : G)) hσp
    have e : (((σ (p ^ 2) : H) : ↥L) : G) = b * (((p ^ 2 : H) : ↥L) : G) * b⁻¹ := rfl
    rw [e] at this
    simpa using this

end CFSG.RankThree.PartTwo.Sec21.FF79
