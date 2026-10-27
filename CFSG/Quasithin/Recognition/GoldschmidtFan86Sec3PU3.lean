module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3PU
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Sym3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Norm
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem orderOf_dvd_card_range {A B : Type*} [Group A] [Group B] (f : A →* B) (a : A) :
    orderOf (f a) ∣ Nat.card f.range := by
  have hmem : f a ∈ f.range := f.mem_range.2 ⟨a, rfl⟩
  have := orderOf_dvd_natCard (⟨f a, hmem⟩ : ↥f.range)
  rwa [Subgroup.orderOf_mk (f a) hmem] at this

@[expose] def conjSub {E H : Subgroup G} (hEH : E ≤ H) (y : G) (hy : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hy' : ∀ e ∈ E, y⁻¹ * e * y ∈ E) : ↥(E.subgroupOf H) ≃* ↥(E.subgroupOf H) where
  toFun s := ⟨⟨y * (s : G) * y⁻¹, hEH (hy _ s.2)⟩, hy _ s.2⟩
  invFun s := ⟨⟨y⁻¹ * (s : G) * y, hEH (hy' _ s.2)⟩, hy' _ s.2⟩
  left_inv s := Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  right_inv s := Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  map_mul' s t := Subtype.ext (Subtype.ext (by simp [mul_assoc]))

theorem conjSub_coe {E H : Subgroup G} (hEH : E ≤ H) (y : G) (hy : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hy' : ∀ e ∈ E, y⁻¹ * e * y ∈ E) (s : ↥(E.subgroupOf H)) :
    ((((conjSub hEH y hy hy') s : ↥(E.subgroupOf H)) : ↥H) : G) =
      y * (((s : ↥H)) : G) * y⁻¹ := rfl

theorem conjSub_pow_coe {E H : Subgroup G} (hEH : E ≤ H) (y : G) (hy : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hy' : ∀ e ∈ E, y⁻¹ * e * y ∈ E) (n : ℕ) (s : ↥(E.subgroupOf H)) :
    (((((conjSub hEH y hy hy') ^ n) s : ↥(E.subgroupOf H)) : ↥H) : G) =
      y ^ n * (((s : ↥H)) : G) * (y ^ n)⁻¹ := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    show ((((conjSub hEH y hy hy') ^ n) ((conjSub hEH y hy hy') s) : ↥(E.subgroupOf H)) : G) = _
    rw [ih, conjSub_coe]
    group

namespace ProdSetup

variable {F : FanTree Γ G} {α β : V} {x : G} {H : Subgroup G} (S : ProdSetup F α β x H)

include S

theorem exists_quot_equiv_perm3 (L : LocalFacts F) (hp3 : pval Γ α = 3)
    (hne : ¬ nbrStab Γ G β ≤ nbrStab Γ G α) :
    Nonempty (↥H ⧸ CFSG.Open.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) := by
  have := S.finite_prod
  obtain ⟨φ, -, hφk⟩ := L.perm3 hp3
  let ι : ↥H →* ↥(MulAction.stabilizer G α) := Subgroup.inclusion S.le_stab
  let φ' : ↥H →* Equiv.Perm (Fin 3) := φ.comp ι
  have hker : ∀ h : ↥H, φ' h = 1 ↔ ((h : ↥H) : G) ∈ nbrStab Γ G α := fun h => hφk (ι h)
  have hK2 : IsPGroup 2 (nbrStab Γ G α) := F.nbrStab_isPGroup α
  have hKβ2 : IsPGroup 2 (nbrStab Γ G β) := F.nbrStab_isPGroup β
  have hrange : φ'.range = ⊤ := by
    apply Sym3.eq_top_of_dvd
    · obtain ⟨k, hkβ, hkα⟩ := Set.not_subset.1 hne
      let k' : ↥H := ⟨k, S.nbrStab_le hkβ⟩
      have hz1 : φ' k' ≠ 1 := fun h => hkα ((hker k').1 h)
      obtain ⟨m, hm⟩ := hKβ2 ⟨k, hkβ⟩
      have hkm : k ^ (2 ^ m) = 1 := congrArg Subtype.val hm
      have hzm : φ' k' ^ (2 ^ m) = 1 := by
        rw [← map_pow]
        have : k' ^ (2 ^ m) = 1 := Subtype.ext hkm
        rw [this, map_one]
      have hord : orderOf (φ' k') ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hzm
      obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
      have hj0 : j ≠ 0 := by
        rintro rfl
        simp only [pow_zero] at hjo
        exact hz1 (orderOf_eq_one_iff.1 hjo)
      have h2 : 2 ∣ orderOf (φ' k') := by
        rw [hjo]
        exact dvd_pow_self 2 hj0
      exact h2.trans (orderOf_dvd_card_range φ' k')
    · let x' : ↥H := ⟨x, S.x_mem⟩
      have hz1 : φ' x' ≠ 1 := by
        intro h
        have hxK : x ∈ nbrStab Γ G α := (hker x').1 h
        obtain ⟨m, hm⟩ := hK2 ⟨x, hxK⟩
        have hxm : x ^ (2 ^ m) = 1 := congrArg Subtype.val hm
        have := orderOf_dvd_of_pow_eq_one hxm
        rw [S.ord, hp3] at this
        have h3 : 3 ∣ 2 ^ m := this
        exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
          (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)
      have hz3 : φ' x' ^ 3 = 1 := by
        rw [← map_pow]
        have : x' ^ 3 = 1 := Subtype.ext (by
          have := S.pow_valence_eq_one
          rwa [hp3] at this)
        rw [this, map_one]
      have hord : orderOf (φ' x') = 3 := orderOf_eq_prime hz3 hz1
      have := orderOf_dvd_card_range φ' x'
      rwa [hord] at this
  have hsurj : Function.Surjective φ' := MonoidHom.range_eq_top.1 hrange
  have hMn : (CFSG.Open.pCore 2 ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hkerEq : φ'.ker = CFSG.Open.pCore 2 ↥H := by
    apply le_antisymm
    · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker φ') ?_
      rintro ⟨h, hh⟩
      obtain ⟨m, hm⟩ := hK2 ⟨(h : G), (hker h).1 hh⟩
      refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hm
      simpa using this
    · intro h hh
      have hM2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥H) :=
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        CFSG.LieType.BorelTits.pCore_isPGroup 2
      have hN : (Subgroup.map φ' (CFSG.Open.pCore 2 ↥H)).Normal := hMn.map φ' hsurj
      have hNp : IsPGroup 2 (Subgroup.map φ' (CFSG.Open.pCore 2 ↥H)) := hM2.map φ'
      have hbot := Sym3.eq_bot_of_normal_isPGroup _ hNp
      exact (Subgroup.map_eq_bot_iff _).1 hbot hh
  have : φ'.ker.Normal := MonoidHom.normal_ker φ'
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ' hsurj)⟩

theorem normal_of_valence_three (L : LocalFacts F) (h29 : Sigma3Aut) (hp3 : pval Γ α = 3) :
    ∀ h ∈ H, h * x * h⁻¹ ∈ Subgroup.zpowers x := by
  have hfin := S.finite_prod
  have hsub : nbrStab Γ G β ≤ H := S.nbrStab_le
  by_cases hKα : nbrStab Γ G β ≤ nbrStab Γ G α
  ·
    have heq : nbrStab Γ G β = ballStab Γ G 2 α := by
      rw [← S.inf_eq_ballStab_two L, inf_eq_right.2 hKα]
    have hbot : nbrStab Γ G β = ⊥ := by
      refine F.eq_bot_of_locTrans (Subgroup.normalizer (nbrStab Γ G β : Set G)) S.adj ?_ le_rfl
        ?_ ?_
      · intro u hu
        exact ⟨MulAction.mem_stabilizer_iff.1 (S.nbrStab_le_stab hu),
          MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer β hu)⟩
      · intro a b ha hb
        obtain ⟨g, hg, hga⟩ := F.loc_trans α a b ha hb
        refine ⟨g, ?_, MulAction.mem_stabilizer_iff.1 hg, hga⟩
        rw [heq]
        exact F.mem_normalizer_ballStab_two hg
      · intro a b ha hb
        obtain ⟨g, hg, hga⟩ := F.loc_trans β a b ha hb
        exact ⟨g, F.mem_normalizer_nbrStab hg, MulAction.mem_stabilizer_iff.1 hg, hga⟩
    intro h hh
    obtain ⟨i, k, hk, rfl⟩ := S.mem_prod_iff.1 hh
    have hk1 : k = 1 := Subgroup.mem_bot.1 (hbot ▸ hk)
    rw [hk1]
    have : x ^ i * 1 * x * (x ^ i * 1)⁻¹ = x := by group
    rw [this]
    exact Subgroup.mem_zpowers x
  ·
    have hβ5 : pval Γ β = 5 := by
      have h1 := F.alternating α β S.adj
      have h2 : pval Γ α = Nat.card (Γ.neighborSet α) := rfl
      have h3 : pval Γ β = Nat.card (Γ.neighborSet β) := rfl
      rcases F.valence β with h | h <;> omega
    obtain ⟨y, hy, hyo⟩ := F.exists_orderOf_eq_valence β
    have hy5 : y ^ 5 = 1 := by
      rw [← hβ5, ← hyo]
      exact pow_orderOf_eq_one y
    have hE1 : ∀ e ∈ nbrStab Γ G β, y * e * y⁻¹ ∈ nbrStab Γ G β := fun e he =>
      F.conj_mem_nbrStab_of_stab hy he
    have hE2 : ∀ e ∈ nbrStab Γ G β, y⁻¹ * e * y ∈ nbrStab Γ G β := fun e he => by
      simpa using F.conj_mem_nbrStab_of_stab (inv_mem hy) he
    let f := conjSub hsub y hE1 hE2
    let e : ↥((nbrStab Γ G β).subgroupOf H) ≃* ↥(nbrStab Γ G β) :=
      Subgroup.subgroupOfEquivOfLe hsub
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hf1 : f ≠ 1 := by
      intro h1
      refine F.false_of_centralizes L hy hyo fun k hk => ?_
      let s : ↥((nbrStab Γ G β).subgroupOf H) := ⟨⟨k, hsub hk⟩, hk⟩
      have := congrArg
        (fun φ : ↥((nbrStab Γ G β).subgroupOf H) ≃* ↥((nbrStab Γ G β).subgroupOf H) =>
          ((((φ s) : ↥((nbrStab Γ G β).subgroupOf H)) : ↥H) : G)) h1
      simpa [f, conjSub_coe, s] using this
    have hf5 : orderOf f = 5 := by
      refine orderOf_eq_prime ?_ hf1
      refine MulEquiv.ext fun s => Subtype.ext (Subtype.ext ?_)
      rw [conjSub_pow_coe, hy5]
      simp
    have hquot := S.exists_quot_equiv_perm3 L hp3 hKα
    have hP : IsPGroup 2 ((nbrStab Γ G β).subgroupOf H) :=
      (F.nbrStab_isPGroup β).of_equiv e.symm
    have hcard : Nat.card H = 3 * Nat.card ((nbrStab Γ G β).subgroupOf H) := by
      rw [S.card_eq L, hp3, Nat.card_congr e.toEquiv]
    have hx3 : orderOf (⟨x, S.x_mem⟩ : ↥H) = 3 := by
      rw [Subgroup.orderOf_mk, S.ord, hp3]
    have hno : ∀ K : Subgroup ↥H, K ≤ (nbrStab Γ G β).subgroupOf H →
        (∀ s : ↥((nbrStab Γ G β).subgroupOf H), (s : ↥H) ∈ K →
          (((f s : ↥((nbrStab Γ G β).subgroupOf H)) : ↥H)) ∈ K) → K.Normal → K = ⊥ := by
      intro K hKS hKf hKn
      have hK' : K.map H.subtype ≤ nbrStab Γ G β := by
        rintro _ ⟨k, hk, rfl⟩
        exact Subgroup.mem_subgroupOf.1 (hKS hk)
      have hxK := mem_normalizer_map_of_normal K S.x_mem
      have hfwd : ∀ u ∈ K.map H.subtype, y * u * y⁻¹ ∈ K.map H.subtype := by
        rintro _ ⟨k, hk, rfl⟩
        have := hKf ⟨k, hKS hk⟩ hk
        exact ⟨_, this, by simp [f, conjSub_coe]⟩
      have hpow : ∀ n : ℕ, ∀ u ∈ K.map H.subtype, y ^ n * u * (y ^ n)⁻¹ ∈ K.map H.subtype := by
        intro n
        induction n with
        | zero => intro u hu; simpa using hu
        | succ n ih =>
          intro u hu
          have h1 := hfwd _ (ih u hu)
          have e1 : y ^ (n + 1) * u * (y ^ (n + 1))⁻¹ = y * (y ^ n * u * (y ^ n)⁻¹) * y⁻¹ := by
            group
          rw [e1]
          exact h1
      have hyK : y ∈ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro u
        refine ⟨hfwd u, fun hu => ?_⟩
        have h1 := hpow 4 _ hu
        have e1 : y ^ 4 * (y * u * y⁻¹) * (y ^ 4)⁻¹ = (y ^ 4 * y) * u * (y ^ 4 * y)⁻¹ := by group
        rw [e1, ← pow_succ, hy5] at h1
        simpa using h1
      have hbot := S.toXSetup.eq_bot_of_normalized L hy hyo hK' hxK hyK
      exact (Subgroup.map_eq_bot_iff_of_injective K (Subgroup.subtype_injective H)).1 hbot
    have hnormal := h29 ↥H ((nbrStab Γ G β).subgroupOf H) ⟨x, S.x_mem⟩ f 5 hquot hP hcard hx3
      Nat.prime_five (by norm_num) hf5 hno
    exact fun h hh => conj_mem_zpowers_of_normal S.x_mem hnormal hh

end ProdSetup

end CFSG.Quasithin.Fan86
