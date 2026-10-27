module

public import CFSG.Quasithin.EmptyFaithful.T1515gA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem a7_constWeight_eq_bot : constWeight 7 = ⊥ := by
  ext x
  simp only [AddSubgroup.mem_bot]
  constructor
  · intro hx
    have hsum : ∑ i, (x : Fin 7 → ZMod 2) i = 0 := by
      have := x.2
      simpa [evenWeight] using this
    have h0 : ∀ i, (x : Fin 7 → ZMod 2) i = (x : Fin 7 → ZMod 2) 0 := fun i => hx i 0
    have h1 : ∑ i, (x : Fin 7 → ZMod 2) i = ∑ _i : Fin 7, (x : Fin 7 → ZMod 2) 0 :=
      Finset.sum_congr rfl fun i _ => h0 i
    rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
    have h7 : ∀ a : ZMod 2, (7 : ℕ) • a = a := by decide
    rw [h7] at hsum
    ext i
    rw [h0 i, hsum]
    rfl
  · rintro rfl i j
    rfl

theorem a7_permWeight_eTheta (σ : Equiv.Perm (Fin 7)) (d : Fin 7) :
    permWeight 7 σ (a7ETheta d) = a7ETheta d ↔ σ d = d := by
  constructor
  · intro h
    have h1 := congrArg (fun z : ↥(evenWeight 7) => (z : Fin 7 → ZMod 2) d) h
    simp only [permWeight, a7ETheta, ite_true] at h1
    by_cases hs : σ⁻¹ d = d
    · exact (Equiv.Perm.inv_eq_iff_eq.mp hs).symm
    · exfalso
      have h2 : (if σ⁻¹ d = d then (0 : ZMod 2) else 1) = 0 := h1
      rw [ite_eq_left_iff] at h2
      exact absurd (h2 hs) (by decide)
  · intro h
    apply Subtype.ext
    funext i
    simp only [permWeight, a7ETheta]
    have : σ⁻¹ i = d ↔ i = d := by
      rw [Equiv.Perm.inv_eq_iff_eq, h]
    simp only [this]

theorem a7_comm_mem_Z {G : Type} [Group G] {L : Subgroup G}
    {α : ↥L →* alternatingGroup (Fin 7)} {β : ↥(blockU L) →* Multiplicative (AltHeart 7)}
    (hstr : A7Str L α β) {d : Fin 7} {u : ↥(blockU L)}
    (hu : (QuotientAddGroup.mk (a7ETheta d) : AltHeart 7) = Multiplicative.toAdd (β u)) {l : G}
    (hl : l ∈ L)
    (hd : ((α ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) d = d)
    (hnorm : l * (u : G) * l⁻¹ ∈ blockU L) : l * (u : G) * l⁻¹ * (u : G)⁻¹ ∈ blockZ L := by
  set u' : ↥(blockU L) := ⟨l * (u : G) * l⁻¹, hnorm⟩ with hu'
  have h1 := hstr.2.2.2.2 ⟨l, hl⟩ u u' rfl (a7ETheta d) hu
  rw [(a7_permWeight_eTheta _ d).mpr hd] at h1
  have h2 : β u' = β u := by
    apply Multiplicative.toAdd.injective
    rw [← h1, hu]
  have h3 : β (u' * u⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
  have h4 : u' * u⁻¹ ∈ β.ker := h3
  rw [hstr.2.2.2.1] at h4
  exact Subgroup.mem_subgroupOf.mp h4

theorem a7_comm_of_three {G : Type} [Group G] {L : Subgroup G}
    {α : ↥L →* alternatingGroup (Fin 7)} {β : ↥(blockU L) →* Multiplicative (AltHeart 7)}
    (hshort : IsShort2 L) (hstr : A7Str L α β) {d : Fin 7} {u : ↥(blockU L)}
    (hu : (QuotientAddGroup.mk (a7ETheta d) : AltHeart 7) = Multiplicative.toAdd (β u)) {l : G}
    (hl : l ∈ L) (hd : ((α ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) d = d) {k : ℕ}
    (hk : orderOf l = 3 ^ k) : l * (u : G) = (u : G) * l := by
  have hnorm : l * (u : G) * l⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer hl)) u).mp u.2
  have hc := a7_comm_mem_Z hstr hu hl hd hnorm
  set c : G := l * (u : G) * l⁻¹ * (u : G)⁻¹ with hcdef
  have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc.2 l hl
  have hc2 : c ^ 2 = 1 := C1.blockU_sq hshort c hc.1
  have hlu : l * (u : G) * l⁻¹ = c * (u : G) := by rw [hcdef]; group
  have hpow : ∀ n : ℕ, l ^ n * (u : G) * (l ^ n)⁻¹ = c ^ n * (u : G) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : l * c ^ n * l⁻¹ = c ^ n := by
        have : l * c ^ n = c ^ n * l := (Commute.pow_right (show Commute l c from hcl) n).eq
        rw [this]
        group
      calc l ^ (n + 1) * (u : G) * (l ^ (n + 1))⁻¹
          = l * (l ^ n * (u : G) * (l ^ n)⁻¹) * l⁻¹ := by group
        _ = (l * c ^ n * l⁻¹) * (l * (u : G) * l⁻¹) := by rw [ih]; group
        _ = c ^ (n + 1) * (u : G) := by rw [hcn, hlu]; group
  have h1 := hpow (3 ^ k)
  rw [← hk, pow_orderOf_eq_one, inv_one, mul_one, one_mul] at h1
  have h2 : c ^ orderOf l = 1 := by
    have := h1.symm
    rwa [mul_eq_right] at this
  have hodd : Odd (orderOf l) := by rw [hk]; exact Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  have hc1 : c = 1 := by
    rw [hm, pow_succ, pow_mul, hc2, one_pow, one_mul] at h2
    exact h2
  rw [hc1] at hlu
  have : l * (u : G) = (u : G) * l := by
    have h5 : l * (u : G) * l⁻¹ = (u : G) := by rw [hlu, one_mul]
    calc l * (u : G) = l * (u : G) * l⁻¹ * l := by group
      _ = (u : G) * l := by rw [h5]
  exact this

theorem a7_action_of_mem_bSub {G : Type} [Group G] {S L : Subgroup G} {u : G} (huL : u ∈ L)
    (huS : u ∈ S) (hu2 : u ^ 2 = 1) {v : G} (hv : v ∈ a7BSub S L u) :
    (∀ l ∈ L, v * l * v⁻¹ = l) ∨ (∀ l ∈ L, v * l * v⁻¹ = u * l * u⁻¹) := by
  have hnorm : Subgroup.zpowers u ≤
      Subgroup.normalizer ((S ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer huS)
    have h2 := Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_centralizer L (Subgroup.le_normalizer huL))
    intro x
    simp only [Subgroup.mem_inf]
    rw [h1 x, h2 x]
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (S ⊓ Subgroup.centralizer (L : Set G))
    (Subgroup.zpowers u) hnorm
  have hv' : v ∈ ((S ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) *
      (Subgroup.zpowers u : Set G) := by
    rw [← hmul]
    exact hv
  obtain ⟨c, hc, w, hw, rfl⟩ := hv'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hcL : ∀ x ∈ L, c * x * c⁻¹ = x := fun x hx => by
    have := Subgroup.mem_centralizer_iff.mp hc.2 x hx
    rw [← this]
    group
  have hukL : ∀ l ∈ L, u ^ k * l * (u ^ k)⁻¹ ∈ L := fun l hl =>
    L.mul_mem (L.mul_mem (L.zpow_mem huL k) hl) (L.inv_mem (L.zpow_mem huL k))
  have hconj : ∀ l ∈ L, c * u ^ k * l * (c * u ^ k)⁻¹ = u ^ k * l * (u ^ k)⁻¹ := fun l hl => by
    have := hcL _ (hukL l hl)
    rw [← this]
    group
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    intro l hl
    have h1 : u ^ k = 1 := by
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
      rw [hm, zpow_mul]
      have : u ^ (2 : ℤ) = 1 := by exact_mod_cast hu2
      rw [this, one_zpow]
    rw [hconj l hl, h1]
    group
  · right
    intro l hl
    have h1 : u ^ k = u := by
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      rw [hm, zpow_add, zpow_mul, zpow_one]
      have : u ^ (2 : ℤ) = 1 := by exact_mod_cast hu2
      rw [this, one_zpow, one_mul]
    rw [hconj l hl, h1]

@[expose] def a7Pts (d : Fin 7) : Finset (Fin 7) := Finset.univ.erase d

@[expose] def a7St (d : Fin 7) : Subgroup (alternatingGroup (Fin 7)) :=
  (alternatingGroup.ofSubtype (a7Pts d)).range

theorem a7_mem_St {d : Fin 7} {a : alternatingGroup (Fin 7)} :
    a ∈ a7St d ↔ (a : Equiv.Perm (Fin 7)) d = d := by
  constructor
  · rintro ⟨x, rfl⟩
    show ((alternatingGroup.ofSubtype (a7Pts d) x : alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7)) d = d
    rw [alternatingGroup.coe_ofSubtype]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp [a7Pts])
  · intro h6
    have hmem : ∀ i : Fin 7, (a : Equiv.Perm (Fin 7)) i ∈ a7Pts d ↔ i ∈ a7Pts d := by
      intro i
      simp only [a7Pts, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hi hi'
        apply hi
        rw [hi', h6]
      · intro hi hi'
        apply hi
        apply (a : Equiv.Perm (Fin 7)).injective
        rw [hi', h6]
    have hsupp : ∀ x, (a : Equiv.Perm (Fin 7)) x ≠ x → x ∈ a7Pts d := by
      intro x hx
      simp only [a7Pts, Finset.mem_erase, Finset.mem_univ, and_true]
      intro hx6
      apply hx
      rw [hx6, h6]
    let f : Equiv.Perm ↥(a7Pts d) := (a : Equiv.Perm (Fin 7)).subtypePerm hmem
    have hf : Equiv.Perm.ofSubtype f = (a : Equiv.Perm (Fin 7)) :=
      Equiv.Perm.ofSubtype_subtypePerm hmem hsupp
    have hfs : f ∈ alternatingGroup ↥(a7Pts d) := by
      rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype, hf]
      exact Equiv.Perm.mem_alternatingGroup.1 a.2
    refine ⟨⟨f, hfs⟩, ?_⟩
    apply Subtype.ext
    show ((alternatingGroup.ofSubtype (a7Pts d) ⟨f, hfs⟩ : alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7)) = _
    rw [alternatingGroup.coe_ofSubtype]
    exact hf

theorem a7_card_Pts (d : Fin 7) : Fintype.card ↥(a7Pts d) = 6 := by
  rw [Fintype.card_coe]
  simp [a7Pts]

noncomputable def a7St_equiv (d : Fin 7) : ↥(a7St d) ≃* alternatingGroup (Fin 6) :=
  ((MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).symm).trans
    (Equiv.altCongrHom (Fintype.equivFinOfCardEq (a7_card_Pts d)))

theorem a7_isSimple_alt6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem a7_isSimple_St (d : Fin 7) : IsSimpleGroup ↥(a7St d) :=
  haveI := a7_isSimple_alt6
  (a7St_equiv d).isSimpleGroup

theorem a7_card_St (d : Fin 7) : Nat.card ↥(a7St d) = 360 := by
  rw [Nat.card_congr (a7St_equiv d).toEquiv, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
  decide

theorem a7_eq_top_of_perfect_pquot {H : Type*} [Group H] [Finite H] (hH : commutator H = ⊤)
    (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 (H ⧸ N)) : N = ⊤ := by
  by_contra hne
  have hnt : Nontrivial (H ⧸ N) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hne
  have hnil : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
  have hsolv : Group.IsSolvable (H ⧸ N) := inferInstance
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (H ⧸ N)
  have hperf : commutator (H ⧸ N) = ⊤ := by
    have h1 : (commutator H).map (QuotientGroup.mk' N) = ⊤ := by
      rw [hH, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)] at h1
    exact h1
  exact absurd hperf hlt.ne

theorem a7_eq_top_of_perfect_sup {H : Type*} [Group H] [Finite H] (hH : commutator H = ⊤)
    (N : Subgroup H) [N.Normal] (h : N ⊔ CFSG.pCore 2 H = ⊤) : N = ⊤ := by
  refine a7_eq_top_of_perfect_pquot hH N ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hx : x ∈ N ⊔ CFSG.pCore 2 H := h ▸ Subgroup.mem_top x
    obtain ⟨n, hn, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨p, hp⟩
    refine ⟨k, ?_⟩
    have hpk : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hn1 : (QuotientGroup.mk n : H ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [QuotientGroup.mk_mul, hn1, one_mul, ← QuotientGroup.mk_pow, hpk, QuotientGroup.mk_one]

theorem a7_mem_cComp_of_perfect_simple_quot {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hne : K ≠ ⊥) (hperf : ⁅K, K⁆ = K) (hsub : IsSubnormal K X)
    (hq : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) : K ∈ cComp X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  have hcomm : commutator ↥K = ⊤ := (Subgroup.isPerfect_iff.2 hperf).commutator_eq_top
  refine ⟨hne, hperf, hsub, fun K' hK'K hK'ne hK'perf hK'sub => ?_⟩
  have hK'K' : IsSubnormal K' K := A3.subnormal_of_le_of_le hK'sub hK'K.le (A3.subnormal_le hsub)
  obtain ⟨P, hPK, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt hK'K' hK'K
  let π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hPm : ((P.subgroupOf K).map π).Normal := Subgroup.Normal.map hPn π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((P.subgroupOf K).map π) with h0 | h1
  ·
    have hPQ : P.subgroupOf K ≤ CFSG.pCore 2 ↥K := fun x hx => by
      have : π x ∈ (P.subgroupOf K).map π := Subgroup.mem_map_of_mem π hx
      rw [h0, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    have hK'p : IsPGroup 2 ↥K' := by
      intro y
      have hyK : (y : G) ∈ K := hK'K.le y.2
      have hyP : (⟨(y : G), hyK⟩ : ↥K) ∈ P.subgroupOf K := hK'P y.2
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨⟨(y : G), hyK⟩, hPQ hyP⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥K) => ((z : ↥K) : G)) hk
      simpa using this
    have hnil : Group.IsNilpotent ↥K' := hK'p.isNilpotent
    have hsolv : Group.IsSolvable ↥K' := inferInstance
    have hnt : Nontrivial ↥K' := (Subgroup.nontrivial_iff_ne_bot K').2 hK'ne
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K')
    have hperf' : commutator ↥K' = ⊤ := (Subgroup.isPerfect_iff.2 hK'perf).commutator_eq_top
    exact absurd hperf' hlt.ne
  ·
    have hsup : P.subgroupOf K ⊔ CFSG.pCore 2 ↥K = ⊤ := by
      have := Subgroup.comap_map_eq π (P.subgroupOf K)
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have htop : P.subgroupOf K = ⊤ := a7_eq_top_of_perfect_sup hcomm _ hsup
    exact absurd (Subgroup.subgroupOf_eq_top.mp htop) (not_le_of_gt hPK)

theorem a7_nonab_of_simple {X : Type*} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hc : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hcon }
  exact hc IsSimpleGroup.prime_card

theorem a7_commutator_top_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : commutator X = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h1 : ⁅a, b⁆ ∈ commutator X := Subgroup.commutator_mem_commutator trivial trivial
    rw [hb, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · exact ht

theorem a7_isQuasisimple_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  have hz : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top a) b).symm)
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  refine ⟨Group.isPerfect_def.mpr (a7_commutator_top_of_simple hs hnab), e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem a7_St_perfect (d : Fin 7) : ⁅a7St d, a7St d⁆ = a7St d := by
  have hs := a7_isSimple_St d
  have hcomm : commutator ↥(a7St d) = ⊤ :=
    a7_commutator_top_of_simple hs
      (a7_nonab_of_simple hs (by rw [a7_card_St]; norm_num))
  have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥(a7St d))) (H₂ := ⊤) (a7St d).subtype
  have h2 : (⁅(⊤ : Subgroup ↥(a7St d)), ⊤⁆ : Subgroup ↥(a7St d)) = ⊤ := hcomm
  rw [h2, Subgroup.map_top, Subgroup.range_subtype] at h1
  exact h1.symm

theorem a7_isQuasisimple_alt6 : CFSG.IsQuasisimple (alternatingGroup (Fin 6)) :=
  a7_isQuasisimple_of_simple a7_isSimple_alt6
    (a7_nonab_of_simple a7_isSimple_alt6 (by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
      norm_num [Nat.factorial]))

theorem a7_top_le_oPrimeResidualOf_of_simple {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hs : IsSimpleGroup X) (hpX : p ∣ Nat.card X) :
    (⊤ : Subgroup X) ≤ oPrimeResidualOf p (⊤ : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpX
  have hN : Subgroup.normalClosure ({y} : Set X) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({y} : Set X))
      with h | h
    · exfalso
      have hmem : y ∈ Subgroup.normalClosure ({y} : Set X) := Subgroup.subset_normalClosure rfl
      rw [h, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hy
      exact hp.one_lt.ne hy
    · exact h
  have hle : Subgroup.normalClosure ({y} : Set X) ≤ oPrimeResidualOf p (⊤ : Subgroup X) := by
    rw [Subgroup.normalClosure]
    refine (Subgroup.closure_le _).2 ?_
    intro z hz
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    have hz' : z = c * a * c⁻¹ := hc.symm
    have h := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have hord : orderOf z = p := by rw [hz', h, hy]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [hord, pow_one]⟩
  intro x hx
  have hx' : x ∈ Subgroup.normalClosure ({y} : Set X) := by rw [hN]; exact hx
  exact hle hx'

theorem a7KStep : A7KStep := by
  intro G _ _ L S V₁ α β hshort hstr hSL hUS d u hu hVB h3 hCN
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le L)
  have huL : (u : G) ∈ L := hUL u.2
  have huS : (u : G) ∈ S := hUS u.2
  have hu2 : (u : G) ^ 2 = 1 := C1.blockU_sq hshort u u.2
  obtain ⟨v₀, hv₀V, hv₀L⟩ := IsConcreteLE.not_le_iff_exists.mp h3
  have hv₀act : ∀ l ∈ L, v₀ * l * v₀⁻¹ = (u : G) * l * (u : G)⁻¹ := by
    rcases a7_action_of_mem_bSub huL huS hu2 (hVB hv₀V) with h | h
    · exfalso
      apply hv₀L
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := h l hl
      calc l * v₀ = (v₀ * l * v₀⁻¹) * v₀ := by rw [this]
        _ = v₀ * l := by group
    · exact h
  set C : Subgroup G := L ⊓ Subgroup.centralizer (V₁ : Set G) with hCdef
  have hCL : C ≤ L := inf_le_left
  have hCmem : ∀ l : G, l ∈ C ↔ l ∈ L ∧ l * (u : G) = (u : G) * l := by
    intro l
    constructor
    · rintro ⟨hl, hlC⟩
      refine ⟨hl, ?_⟩
      have h1 : v₀ * l = l * v₀ := Subgroup.mem_centralizer_iff.mp hlC v₀ hv₀V
      have h2 := hv₀act l hl
      have h3' : v₀ * l * v₀⁻¹ = l := by rw [h1]; group
      rw [h3'] at h2
      calc l * (u : G) = ((u : G) * l * (u : G)⁻¹) * (u : G) := by rw [← h2]
        _ = (u : G) * l := by group
    · rintro ⟨hl, hlu⟩
      refine ⟨hl, ?_⟩
      have hB : a7BSub S L (u : G) ≤ Subgroup.centralizer ({l} : Set G) := by
        refine sup_le (fun c hc => ?_) ?_
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp hc.2 l hl).symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact hlu.symm
      show l ∈ Subgroup.centralizer (V₁ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.mp (hB (hVB hv))
  have hfix : ∀ (l : G) (hl : l ∈ L), l * (u : G) = (u : G) * l →
      ((α ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) d = d := by
    intro l hl hlu
    have h1 := hstr.2.2.2.2 ⟨l, hl⟩ u u (by show (u : G) = l * (u : G) * l⁻¹; rw [hlu]; group)
      (a7ETheta d) hu
    rw [← hu] at h1
    have h2 : permWeight 7 ((α ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
        (a7ETheta d) = a7ETheta d := by
      have := QuotientAddGroup.eq.mp h1
      rw [a7_constWeight_eq_bot, AddSubgroup.mem_bot] at this
      exact neg_add_eq_zero.mp this
    exact (a7_permWeight_eTheta _ d).mp h2
  have hαsurj : Function.Surjective α := hstr.1
  have hC3 : ¬ 3 ∣ Nat.card α.ker := by
    rw [hstr.2.1]
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hm]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  set Cg : Subgroup ↥L := C.subgroupOf L with hCg
  have hαC : Cg.map α = a7St d := by
    apply le_antisymm
    · rintro a ⟨l, hl, rfl⟩
      rw [a7_mem_St]
      exact hfix l l.2 ((hCmem l).mp (Subgroup.mem_subgroupOf.mp hl)).2
    · intro a ha
      have hs := a7_isSimple_St d
      have hle := a7_top_le_oPrimeResidualOf_of_simple Nat.prime_three hs
        (by rw [a7_card_St]; norm_num)
      have hgen : oPrimeResidualOf 3 (⊤ : Subgroup ↥(a7St d)) ≤
          (Cg.map α).subgroupOf (a7St d) := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro x ⟨-, k, hk⟩
        have hxo : orderOf (x : alternatingGroup (Fin 7)) = 3 ^ k := by
          rw [Subgroup.orderOf_coe]
          exact hk
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        obtain ⟨l, hlx, n, hn⟩ := CFSG.LieType.CentralExt.exists_pLift_aux (p := 3) hαsurj hC3
          ⟨k, hxo⟩
        have hlG : orderOf (l : G) = 3 ^ n := by rw [Subgroup.orderOf_coe]; exact hn
        have hxd := a7_mem_St.mp x.2
        have hd' : ((α ⟨(l : G), l.2⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) d = d := by
          have : α ⟨(l : G), l.2⟩ = α l := rfl
          rw [this, hlx]
          exact hxd
        have hcomm := a7_comm_of_three hshort hstr hu l.2 hd' hlG
        have hlC : (l : G) ∈ C := (hCmem _).mpr ⟨l.2, hcomm⟩
        show (x : alternatingGroup (Fin 7)) ∈ Cg.map α
        exact ⟨l, Subgroup.mem_subgroupOf.mpr hlC, hlx⟩
      have := hgen (hle (Subgroup.mem_top (⟨a, ha⟩ : ↥(a7St d))))
      exact Subgroup.mem_subgroupOf.mp this
  set Kg : Subgroup ↥L := perfectCore Cg with hKg
  have hαK : Kg.map α = a7St d := by
    rw [hKg, map_perfectCore α Cg, hαC]
    exact perfectCore_eq_self_of_perfect (a7_St_perfect d)
  set K : Subgroup G := Kg.map L.subtype with hK
  have hKeq : K = perfectCore C := by
    rw [hK, hKg, map_perfectCore L.subtype Cg, hCg, Subgroup.map_subgroupOf_eq_of_le hCL]
  have hKL : K ≤ L := Subgroup.map_subtype_le Kg
  have hKperf : ⁅K, K⁆ = K := by
    rw [hKeq]
    exact perfectCore_perfect C
  have hCX : C ≤ Subgroup.centralizer (V₁ : Set G) := inf_le_right
  have hcentNorm : Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    have hgL := hCN hg
    have hgX := Subgroup.le_normalizer hg
    rw [Subgroup.mem_normalizer_iff] at hgL hgX ⊢
    intro x
    simp only [hCdef, Subgroup.mem_inf]
    rw [hgL x, hgX x]
  have hCnorm : (C.subgroupOf (Subgroup.centralizer (V₁ : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hcentNorm
  have hKsub : IsSubnormal K (Subgroup.centralizer (V₁ : Set G)) := by
    rw [hKeq]
    exact A3.subnormal_perfectCore (A3.subnormal_of_normal hCX hCnorm)
  have hSt_ne : a7St d ≠ ⊥ := by
    intro h
    have := a7_card_St d
    rw [h, Subgroup.card_bot] at this
    omega
  have hKne : K ≠ ⊥ := by
    intro h
    have hKg0 : Kg = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h
    rw [hKg0, Subgroup.map_bot] at hαK
    exact hSt_ne hαK.symm
  let φ : ↥K →* alternatingGroup (Fin 7) := α.comp (Subgroup.inclusion hKL)
  have hKg_eq : K.subgroupOf L = Kg := Subgroup.comap_map_eq_self_of_injective L.subtype_injective Kg
  have hφrange : φ.range = a7St d := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      have hx : (⟨(x : G), hKL x.2⟩ : ↥L) ∈ Kg := by
        rw [← hKg_eq]
        exact Subgroup.mem_subgroupOf.mpr x.2
      rw [← hαK]
      exact ⟨_, hx, rfl⟩
    · intro ha
      rw [← hαK] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      have hyK : (y : G) ∈ K := ⟨y, hy, rfl⟩
      exact ⟨⟨y, hyK⟩, rfl⟩
  have hφmem : ∀ x : ↥K, φ x ∈ a7St d := fun x => hφrange ▸ (⟨x, rfl⟩ : φ x ∈ φ.range)
  let φ' : ↥K →* ↥(a7St d) := φ.codRestrict (a7St d) hφmem
  have hφ'surj : Function.Surjective φ' := by
    rintro ⟨a, ha⟩
    rw [← hφrange] at ha
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, Subtype.ext hx⟩
  have hsimple := a7_isSimple_St d
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : φ'.ker = CFSG.pCore 2 ↥K := by
    apply le_antisymm
    · have hpg : IsPGroup 2 ↥φ'.ker := by
        intro x
        have hx1 : α ⟨((x : ↥K) : G), hKL (x : ↥K).2⟩ = 1 := by
          have := MonoidHom.mem_ker.mp x.2
          exact congrArg Subtype.val this
        have hmem : (⟨((x : ↥K) : G), hKL (x : ↥K).2⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
          rw [← hstr.2.1]
          exact hx1
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => (((z : ↥L)) : G)) hk
        simpa using this
      exact le_sSup (show φ'.ker ∈ {K' : Subgroup ↥K | K'.Normal ∧ IsPGroup 2 K'} from
        ⟨inferInstance, hpg⟩)
    · intro x hx
      have hN : ((CFSG.pCore 2 ↥K).map φ').Normal :=
        Subgroup.Normal.map CFSG.pCore_normal φ' hφ'surj
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥K).map φ') with h0 | h1
      · have : φ' x ∈ (CFSG.pCore 2 ↥K).map φ' := Subgroup.mem_map_of_mem φ' hx
        rw [h0, Subgroup.mem_bot] at this
        exact this
      · exfalso
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(a7St d)) 3
          (by rw [a7_card_St]; norm_num)
        have hgm : g ∈ (CFSG.pCore 2 ↥K).map φ' := h1 ▸ Subgroup.mem_top g
        obtain ⟨y, hy, hyg⟩ := hgm
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨y, hy⟩
        have hyk : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
        have hg1 : g ^ 2 ^ k = 1 := by rw [← hyg, ← map_pow, hyk, map_one]
        have h3 : 3 ∣ 2 ^ k := hg ▸ orderOf_dvd_of_pow_eq_one hg1
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        omega
  let e1 : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(a7St d) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ' hφ'surj)
  let e2 : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 6) := e1.trans (a7St_equiv d)
  have hqsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := e1.isSimpleGroup
  exact ⟨K, a7_mem_cComp_of_perfect_simple_quot hKne hKperf hKsub hqsimple,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e2.symm a7_isQuasisimple_alt6, ⟨e2⟩⟩

end CFSG.Quasithin
