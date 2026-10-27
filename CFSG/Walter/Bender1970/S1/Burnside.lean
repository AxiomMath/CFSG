module

public import CFSG.Walter.Bender1970.S1.Rank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Walter

open CFSG.Open CFSG.SectionRank

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_mem_sylow_of_commute_normalizer {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    [IsMulCommutative (T : Subgroup G)] {z : G} (hzT : z ∈ (T : Subgroup G))
    (hzG : z ∈ commutator G)
    (hzN : ∀ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), n * z = z * n) : z = 1 := by
  classical
  let A : Type _ := (T : Subgroup G)
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  let ϕ : (T : Subgroup G) →* A :=
    { toFun := fun x => x
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (T : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ hk
    obtain ⟨n, hn, hconj⟩ :=
      Sylow.conj_eq_normalizer_conj_of_mem T (z ^ k) g₀ (pow_mem hzT k) hk
    rw [hconj]
    have hc : n * z ^ k = z ^ k * n := (Commute.pow_right (hzN n hn) k).eq
    calc n⁻¹ * z ^ k * n = n⁻¹ * (z ^ k * n) := by rw [mul_assoc]
      _ = n⁻¹ * (n * z ^ k) := by rw [hc]
      _ = z ^ k := by rw [inv_mul_cancel_left]
  have htr := ϕ.transfer_eq_pow z key
  have hker : ϕ.transfer z = 1 := Abelianization.commutator_subset_ker ϕ.transfer hzG
  rw [hker] at htr
  have hpow : z ^ (T : Subgroup G).index = 1 := by
    have h := congrArg (fun x : A => ((x : (T : Subgroup G)) : G)) htr
    exact h.symm
  have hord : orderOf z ∣ (T : Subgroup G).index := orderOf_dvd_of_pow_eq_one hpow
  have hordT : orderOf z ∣ Nat.card (T : Subgroup G) := by
    have := orderOf_dvd_natCard (⟨z, hzT⟩ : (T : Subgroup G))
    rwa [Subgroup.orderOf_mk] at this
  have hcop := T.card_coprime_index
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hordT hord)

theorem prod_mem_iff_even_of_index_two {A : Type*} [CommGroup A] {H : Subgroup A}
    (hH : H.index = 2) (s : Finset A) (hs : ∀ x ∈ s, x ∉ H) :
    (∏ x ∈ s, x) ∈ H ↔ Even s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.one_mem]
  | insert a s ha ih =>
    have haH : a ∉ H := hs a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      Subgroup.mul_mem_iff_of_index_two hH,
      ih fun x hx => hs x (Finset.mem_insert_of_mem hx), Nat.even_add_one]
    simp [haH]

@[expose] def omegaOneOfComm (p : ℕ) (X : Subgroup G)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : Subgroup G where
  carrier := {x | x ∈ X ∧ x ^ p = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨X.mul_mem hx hy, by rw [(Commute.mul_pow (hX x hx y hy) p), hx', hy', one_mul]⟩
  one_mem' := ⟨X.one_mem, one_pow p⟩
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨X.inv_mem hx, by rw [inv_pow, hx', inv_one]⟩

omit [Finite G] in
theorem mem_omegaOneOfComm {p : ℕ} {X : Subgroup G} {hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x}
    {x : G} : x ∈ omegaOneOfComm p X hX ↔ x ∈ X ∧ x ^ p = 1 :=
  Iff.rfl

omit [Finite G] in
theorem omegaOneOfComm_le {p : ℕ} (X : Subgroup G) (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    omegaOneOfComm p X hX ≤ X :=
  fun _ hx => hx.1

theorem card_omegaOneOfComm {p : ℕ} (hp : p.Prime) (X : Subgroup G)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXp : IsPGroup p X) :
    Nat.card (omegaOneOfComm p X hX) = p ^ pRank p X := by
  have : Fact p.Prime := ⟨hp⟩
  set Ω := omegaOneOfComm p X hX
  obtain ⟨k, hk⟩ := (hXp.to_le (omegaOneOfComm_le X hX)).exists_card_eq
  have hΩel : IsElemAbelian p Ω :=
    ⟨⟨⟨fun a b => Subtype.ext (hX _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hx.2⟩
  have hle : k ≤ pRank p X := le_pRank hp.one_lt (omegaOneOfComm_le X hX) hΩel hk
  obtain ⟨E, hEX, hE, hcard⟩ := exists_pRank hp.one_lt X
  have hEΩ : E ≤ Ω := fun x hx => ⟨hEX hx, hE.2 x hx⟩
  have hcardle : p ^ pRank p X ≤ p ^ k := by
    rw [← hcard, ← hk]
    exact Subgroup.card_le_of_le hEΩ
  have hge : pRank p X ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 hcardle
  rw [hk, le_antisymm hle hge]

theorem bender1970_1_3_of_le_commutator (T : Sylow 2 G) (hT : IsMulCommutative (T : Subgroup G))
    (hTG : (T : Subgroup G) ≤ commutator G) {R : Subgroup G} (hRT : R ≤ T)
    (hrank : rank (T : Subgroup G) ≤ rank R + 1) {t : G} (ht : t ∈ (T : Subgroup G))
    (ht2 : t ^ 2 = 1) :
    ∃ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), n * t * n⁻¹ ∈ R := by
  classical
  by_contra hcon
  push Not at hcon
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have hcommT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hT.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcommR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy => hcommT x (hRT hx) y (hRT hy)
  set N := Subgroup.normalizer ((T : Subgroup G) : Set G) with hNdef
  set E := omegaOneOfComm 2 (T : Subgroup G) hcommT with hEdef
  have hNE : N ≤ Subgroup.normalizer (E : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hnT := Subgroup.mem_normalizer_iff.mp hn x
    constructor
    · rintro ⟨hxT, hx2⟩
      refine ⟨hnT.1 hxT, ?_⟩
      rw [conj_pow, hx2, mul_one, mul_inv_cancel]
    · rintro ⟨hxT, hx2⟩
      refine ⟨hnT.2 hxT, ?_⟩
      have h := congrArg (fun y => n⁻¹ * y * n) hx2
      simp only [conj_pow, mul_one, inv_mul_cancel] at h
      simpa [mul_assoc] using h
  let _ : MulDistribMulAction N E := Subgroup.conjMulDistribMulActionOfLeNormalizer N E hNE
  have hsmul : ∀ (m : N) (x : E), ((m • x : E) : G) = (m : G) * x * (m : G)⁻¹ := fun _ _ => rfl
  have hEcomm : IsMulCommutative E :=
    ⟨⟨fun a b => Subtype.ext (hcommT _ a.2.1 _ b.2.1)⟩⟩
  let _ : CommGroup E := IsMulCommutative.instCommGroup
  let t' : E := ⟨t, ht, ht2⟩
  set O : Finset E := (Set.toFinite (MulAction.orbit N t')).toFinset with hOdef
  set π : E := ∏ x ∈ O, x with hπdef
  have hOR : ∀ x ∈ O, (x : G) ∉ R := by
    intro x hx
    rw [hOdef, Set.Finite.mem_toFinset, MulAction.mem_orbit_iff] at hx
    obtain ⟨m, rfl⟩ := hx
    rw [hsmul]
    exact hcon m m.2
  have hπN : ∀ m ∈ N, m * (π : G) = (π : G) * m := by
    intro m hm
    have hfix : (⟨m, hm⟩ : N) • π = π := by
      rw [hπdef, Finset.smul_prod']
      refine Finset.prod_nbij' (fun x => (⟨m, hm⟩ : N) • x) (fun x => (⟨m, hm⟩ : N)⁻¹ • x)
        ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [hOdef, Set.Finite.mem_toFinset] at hx ⊢
        obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
        exact MulAction.mem_orbit_iff.mpr ⟨⟨m, hm⟩ * g, mul_smul _ _ _⟩
      · intro x hx
        simp only [hOdef, Set.Finite.mem_toFinset] at hx ⊢
        obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
        exact MulAction.mem_orbit_iff.mpr ⟨(⟨m, hm⟩ : N)⁻¹ * g, mul_smul _ _ _⟩
      · intro x _
        simp
      · intro x _
        simp
      · intro x _
        rfl
    have h := congrArg Subtype.val hfix
    rw [hsmul] at h
    calc m * (π : G) = m * (π : G) * m⁻¹ * m := by group
      _ = (π : G) * m := by rw [h]
  have hπ1 : (π : G) = 1 := by
    have := hT
    exact eq_one_of_mem_sylow_of_commute_normalizer T (π.2.1) (hTG π.2.1) hπN
  have hOodd : ¬ Even O.card := by
    have hcardO : O.card = (MulAction.orbit N t').ncard := by
      rw [hOdef, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    rw [hcardO, ← MulAction.index_stabilizer]
    have hTstab : (T : Subgroup G).subgroupOf N ≤ MulAction.stabilizer N t' := by
      intro m hm
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      rw [hsmul]
      have hmT : (m : G) ∈ (T : Subgroup G) := hm
      rw [hcommT _ hmT _ ht, mul_inv_cancel_right]
    have hdvd : (MulAction.stabilizer N t').index ∣ ((T : Subgroup G).subgroupOf N).index :=
      Subgroup.index_dvd_of_le hTstab
    have hTN : (T : Subgroup G) ≤ N := Subgroup.le_normalizer
    have hrel : ((T : Subgroup G).subgroupOf N).index ∣ (T : Subgroup G).index := by
      rw [← Subgroup.relIndex_mul_index hTN]
      exact dvd_mul_right _ _
    have hTodd : ¬ 2 ∣ (T : Subgroup G).index := T.not_dvd_index
    intro heven
    exact hTodd ((even_iff_two_dvd.mp heven).trans (hdvd.trans hrel))
  set H : Subgroup E := R.subgroupOf E with hHdef
  have hTp : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hRp : IsPGroup 2 R := hTp.to_le hRT
  have hcardE : Nat.card E = 2 ^ pRank 2 (T : Subgroup G) :=
    card_omegaOneOfComm hp2 _ hcommT hTp
  have hcardH : Nat.card H = 2 ^ pRank 2 R := by
    rw [← card_omegaOneOfComm hp2 R hcommR hRp]
    have hset : R ⊓ E = omegaOneOfComm 2 R hcommR := by
      ext x
      constructor
      · rintro ⟨hxR, -, hx2⟩
        exact ⟨hxR, hx2⟩
      · rintro ⟨hxR, hx2⟩
        exact ⟨hxR, hRT hxR, hx2⟩
    rw [← hset, hHdef, ← Subgroup.inf_subgroupOf_right R E]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ⊓ E ≤ E)).toEquiv
  have hrT : rank (T : Subgroup G) = pRank 2 (T : Subgroup G) := rank_eq_pRank_of_isPGroup hp2 hTp
  have hrR : rank R = pRank 2 R := rank_eq_pRank_of_isPGroup hp2 hRp
  have hRle : pRank 2 R ≤ pRank 2 (T : Subgroup G) := pRank_mono hp2.one_lt hRT
  have hidx : H.index * 2 ^ pRank 2 R = 2 ^ pRank 2 (T : Subgroup G) := by
    rw [← hcardH, ← hcardE, mul_comm]
    exact H.card_mul_index
  have hidx' : H.index = 1 ∨ H.index = 2 := by
    rw [hrT, hrR] at hrank
    rcases Nat.lt_or_ge (pRank 2 R) (pRank 2 (T : Subgroup G)) with hlt | hge
    · right
      have heq : pRank 2 (T : Subgroup G) = pRank 2 R + 1 := by omega
      rw [heq, pow_succ] at hidx
      have h2pos : 0 < 2 ^ pRank 2 R := pow_pos (by norm_num) _
      nlinarith [hidx]
    · left
      have heq : pRank 2 (T : Subgroup G) = pRank 2 R := le_antisymm hge hRle
      rw [heq] at hidx
      have h2pos : 0 < 2 ^ pRank 2 R := pow_pos (by norm_num) _
      nlinarith [hidx]
  rcases hidx' with h1 | h2
  ·
    have htop : H = ⊤ := Subgroup.index_eq_one.mp h1
    have htH : t' ∈ H := htop ▸ Subgroup.mem_top t'
    have htR : t ∈ R := Subgroup.mem_subgroupOf.mp htH
    exact hcon 1 N.one_mem (by simpa using htR)
  ·
    have hOH : ∀ x ∈ O, x ∉ H := fun x hx hxH => hOR x hx hxH
    have hπH : π ∉ H := by
      intro hπH
      exact hOodd ((prod_mem_iff_even_of_index_two h2 O hOH).mp hπH)
    apply hπH
    have : π = 1 := Subtype.ext hπ1
    rw [this]
    exact H.one_mem

theorem bender1970_1_3 [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (T : Sylow 2 G)
    (hT : IsMulCommutative (T : Subgroup G)) {R : Subgroup G} (hRT : R ≤ T)
    (hrank : rank R = rank (T : Subgroup G) - 1) {t : G} (ht : t ∈ (T : Subgroup G))
    (ht2 : orderOf t = 2) :
    ∃ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), n * t * n⁻¹ ∈ R := by
  have hcomm : commutator G = ⊤ := by
    have hn : (commutator G).Normal := inferInstance
    rcases hn.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact hab (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top b)) a
        (Subgroup.mem_top a))
    · exact h
  refine bender1970_1_3_of_le_commutator T hT (hcomm ▸ le_top) hRT (by omega) ht ?_
  rw [← ht2]
  exact pow_orderOf_eq_one t

end CFSG.Walter
