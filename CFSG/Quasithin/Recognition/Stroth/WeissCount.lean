module

public import CFSG.Quasithin.Recognition.Stroth.WeissMoufang
public import CFSG.Quasithin.Recognition.F4Index

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin

universe u v w


section Mono

variable {V : Type u} {H : Type v} [Group H] [MulAction H V] {Γ : SimpleGraph V}
  [GraphAction H Γ]

private theorem snoc_noBack {n : ℕ} {p : GPath Γ n} {u : V} (hu : Γ.Adj (p n) u)
    (hp : p.NoBack) (hne : u ≠ p (n - 1)) : (p.snoc u hu).NoBack := by
  intro i hi
  by_cases h : i + 2 ≤ n
  · rw [GPath.snoc_of_le _ _ _ (by omega), GPath.snoc_of_le _ _ _ (by omega)]
    exact hp i h
  · have hi2 : i + 2 = n + 1 := by omega
    have hin : i = n - 1 := by omega
    rw [hi2, GPath.snoc_last, hin, GPath.snoc_of_le _ _ _ (by omega)]
    exact fun h => hne h.symm

private lemma exists_extend_forward (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {L : ℕ} {s : GPath Γ L} (hs : s.NoBack) (hL : 1 ≤ L) :
    ∀ n, L ≤ n → ∃ p : GPath Γ n, p.NoBack ∧ ∀ i, i ≤ L → p i = s i := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨s, hs, fun i _ => rfl⟩
  | succ n hn ih =>
    obtain ⟨p, hp, hps⟩ := ih
    have hadj : Γ.Adj (p n) (p (n - 1)) := by
      have h := (p.adj (n - 1) (by omega)).symm
      rwa [show n - 1 + 1 = n by omega] at h
    obtain ⟨u, hu, hune⟩ := hne (p n) (p (n - 1)) hadj
    exact ⟨p.snoc u hu, snoc_noBack hu hp hune, fun i hi => by
      rw [GPath.snoc_of_le _ _ _ (by omega)]
      exact hps i hi⟩

theorem IsLocallyTrans.mono {s t : ℕ} (hts : t ≤ s)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h : IsLocallyTrans H Γ s) : IsLocallyTrans H Γ t := by
  intro p p' hp hp' h0
  rcases Nat.eq_zero_or_pos t with ht0 | ht
  · subst ht0
    refine ⟨1, ?_⟩
    rw [GPath.one_smul']
    exact GPath.ext' fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      exact h0
  · obtain ⟨q, hqnb, hqp⟩ := exists_extend_forward hne hp ht s hts
    obtain ⟨q', hq'nb, hq'p⟩ := exists_extend_forward hne hp' ht s hts
    have hq0 : q 0 = q' 0 := by
      rw [hqp 0 (Nat.zero_le t), hq'p 0 (Nat.zero_le t)]
      exact h0
    obtain ⟨g, hg⟩ := h q q' hqnb hq'nb hq0
    refine ⟨g, GPath.ext' fun i hi => ?_⟩
    have h1 := (GPath.smul_eq_iff.mp hg) i (by omega)
    rwa [hqp i hi, hq'p i hi] at h1

theorem exists_smul_nbr_of_isLocallyTrans {s : ℕ} (h : IsLocallyTrans H Γ s) (hs : 1 ≤ s)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {v w₁ w₂ : V} (h₁ : Γ.Adj v w₁) (h₂ : Γ.Adj v w₂) :
    ∃ g : H, g • v = v ∧ g • w₁ = w₂ := by
  have h1 : IsLocallyTrans H Γ 1 := h.mono (by omega) hne
  let p : GPath Γ 1 := (GPath.triv v).snoc w₁ h₁
  let p' : GPath Γ 1 := (GPath.triv v).snoc w₂ h₂
  have hp0 : p 0 = v := GPath.snoc_of_le _ _ _ (Nat.zero_le 0)
  have hp1 : p 1 = w₁ := GPath.snoc_last _ _ _
  have hp'0 : p' 0 = v := GPath.snoc_of_le _ _ _ (Nat.zero_le 0)
  have hp'1 : p' 1 = w₂ := GPath.snoc_last _ _ _
  have hp : p.NoBack := fun i hi => absurd hi (by omega)
  have hp' : p'.NoBack := fun i hi => absurd hi (by omega)
  have hstart : p 0 = p' 0 := by rw [hp0, hp'0]
  obtain ⟨g, hg⟩ := h1 p p' hp hp' hstart
  refine ⟨g, ?_, ?_⟩
  · have h := (GPath.smul_eq_iff.mp hg) 0 (by omega)
    rwa [hp0, hp'0] at h
  · have h := (GPath.smul_eq_iff.mp hg) 1 (by omega)
    rwa [hp1, hp'1] at h

theorem exists_smul_nbr_fix_of_isLocallyTrans {s : ℕ} (h : IsLocallyTrans H Γ s) (hs : 2 ≤ s)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {v w x₁ x₂ : V} (hw : Γ.Adj v w) (h₁ : Γ.Adj v x₁) (h₂ : Γ.Adj v x₂)
    (h₁w : x₁ ≠ w) (h₂w : x₂ ≠ w) :
    ∃ g : H, g • v = v ∧ g • w = w ∧ g • x₁ = x₂ := by
  have h2 : IsLocallyTrans H Γ 2 := h.mono (by omega) hne
  let q : GPath Γ 1 := (GPath.triv w).snoc v hw.symm
  have hq0 : q 0 = w := GPath.snoc_of_le _ _ _ (Nat.zero_le 0)
  have hq1 : q 1 = v := GPath.snoc_last _ _ _
  let p : GPath Γ 2 := q.snoc x₁ (hq1 ▸ h₁)
  let p' : GPath Γ 2 := q.snoc x₂ (hq1 ▸ h₂)
  have hp0 : p 0 = w := by rw [GPath.snoc_of_le _ _ _ (Nat.zero_le 1), hq0]
  have hp1 : p 1 = v := by rw [GPath.snoc_of_le _ _ _ (le_refl 1), hq1]
  have hp2 : p 2 = x₁ := GPath.snoc_last _ _ _
  have hp'0 : p' 0 = w := by rw [GPath.snoc_of_le _ _ _ (Nat.zero_le 1), hq0]
  have hp'1 : p' 1 = v := by rw [GPath.snoc_of_le _ _ _ (le_refl 1), hq1]
  have hp'2 : p' 2 = x₂ := GPath.snoc_last _ _ _
  have hp : p.NoBack := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [hp0, hp2]
    exact fun h => h₁w h.symm
  have hp' : p'.NoBack := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [hp'0, hp'2]
    exact fun h => h₂w h.symm
  have hstart : p 0 = p' 0 := by rw [hp0, hp'0]
  obtain ⟨g, hg⟩ := h2 p p' hp hp' hstart
  refine ⟨g, ?_, ?_, ?_⟩
  · have h := (GPath.smul_eq_iff.mp hg) 1 (by omega)
    rwa [hp1, hp'1] at h
  · have h := (GPath.smul_eq_iff.mp hg) 0 (by omega)
    rwa [hp0, hp'0] at h
  · have h := (GPath.smul_eq_iff.mp hg) 2 (by omega)
    rwa [hp2, hp'2] at h

end Mono


section Counting

variable {V : Type u}

private lemma pCore_two_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : ¬ 2 ∣ B.index) : CFSG.pCore 2 G ≤ B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 G).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := B)
  have hQp : IsPGroup 2 ↥((Q : Subgroup B).map B.subtype) := (Q.isPGroup').map B.subtype
  have hQidx : ¬ 2 ∣ ((Q : Subgroup B).map B.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul (Fact.out : Nat.Prime 2) Q.not_dvd_index hB
  let QG : Sylow 2 G := hQp.toSylow hQidx
  have hpc : CFSG.pCore 2 G ≤ (QG : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := G) 2).le_sylow_of_normal QG
  rw [IsPGroup.toSylow_coe] at hpc
  exact hpc.trans (Subgroup.map_subtype_le _)


private theorem stabilizer_index_of_adj {H : Type v} [Group H] [MulAction H V]
    {Γ : SimpleGraph V} [GraphAction H Γ] {v : V}
    (htr : ∀ w₁ w₂ : V, Γ.Adj v w₁ → Γ.Adj v w₂ →
      ∃ g : H, g • v = v ∧ g • w₁ = w₂)
    {u : V} (hu : Γ.Adj v u) :
    (MulAction.stabilizer (MulAction.stabilizer H v) u).index =
      Nat.card (Γ.neighborSet v) := by
  have horbit : MulAction.orbit (MulAction.stabilizer H v) u = Γ.neighborSet v := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      have hg : ((g : MulAction.stabilizer H v) : H) • v = v := by
        simpa [Subgroup.smul_def] using MulAction.mem_stabilizer_iff.mp g.2
      have h := (GraphAction.adj_smul ((g : MulAction.stabilizer H v) : H) v u).mpr hu
      rw [hg] at h
      simpa [Subgroup.smul_def] using h
    · intro hx
      obtain ⟨g, hgv, hgu⟩ := htr u x hu hx
      refine ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hgv⟩, ?_⟩
      simpa [Subgroup.smul_def] using hgu
  rw [MulAction.index_stabilizer, horbit, ← Nat.card_coe_set_eq]

private theorem orbit_stabilizer_eq_sdiff {H : Type v} [Group H] [MulAction H V]
    {Γ : SimpleGraph V} [GraphAction H Γ] {v : V}
    (htr2 : ∀ w x₁ x₂ : V, Γ.Adj v w → Γ.Adj v x₁ → Γ.Adj v x₂ → x₁ ≠ w → x₂ ≠ w →
      ∃ g : H, g • v = v ∧ g • w = w ∧ g • x₁ = x₂)
    {w w' : V} (hw : Γ.Adj v w) (hw' : Γ.Adj v w') (hww' : w ≠ w') :
    MulAction.orbit (MulAction.stabilizer (MulAction.stabilizer H v) w) w' =
      Γ.neighborSet v \ {w} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have hgv : (((g : MulAction.stabilizer (MulAction.stabilizer H v) w) :
      MulAction.stabilizer H v) : H) • v = v := by
      simpa [Subgroup.smul_def] using
        MulAction.mem_stabilizer_iff.mp (g : MulAction.stabilizer
          (MulAction.stabilizer H v) w).1.2
    have hgw : (((g : MulAction.stabilizer (MulAction.stabilizer H v) w) :
      MulAction.stabilizer H v) : H) • w = w := by
      simpa [Subgroup.smul_def] using
        MulAction.mem_stabilizer_iff.mp (g : MulAction.stabilizer
          (MulAction.stabilizer H v) w).2
    constructor
    · have h := (GraphAction.adj_smul (((g : MulAction.stabilizer
          (MulAction.stabilizer H v) w) : MulAction.stabilizer H v) : H) v w').mpr hw'
      rw [hgv] at h
      simpa [Subgroup.smul_def] using h
    · intro h
      have h1 : (((g : MulAction.stabilizer (MulAction.stabilizer H v) w) :
          MulAction.stabilizer H v) : H) • w' = w := by
        simpa [Subgroup.smul_def] using h
      have h2 : (((g : MulAction.stabilizer (MulAction.stabilizer H v) w) :
          MulAction.stabilizer H v) : H) • w' =
          (((g : MulAction.stabilizer (MulAction.stabilizer H v) w) :
            MulAction.stabilizer H v) : H) • w := by
        rw [h1, hgw]
      exact hww' (MulAction.injective _ h2).symm
  · rintro ⟨hx, hxw⟩
    obtain ⟨g, hgv, hgw, hgx⟩ := htr2 w w' x hw hw' hx hww'.symm hxw
    refine ⟨⟨⟨g, MulAction.mem_stabilizer_iff.mpr hgv⟩, ?_⟩, ?_⟩
    · exact MulAction.mem_stabilizer_iff.mpr (by simpa [Subgroup.smul_def] using hgw)
    · simpa [Subgroup.smul_def] using hgx


private lemma exists_odd_factor {K N Z m : ℕ} (hK : Odd K) (hN : ∃ f, N = 2 ^ f)
    (hm : Odd m) (h : K * Z = N * m) : ∃ t, Odd t ∧ Z = N * t := by
  obtain ⟨f, rfl⟩ := hN
  have hcop : Nat.Coprime (2 ^ f) K := hK.coprime_two_left.pow_left f
  have hdvd : 2 ^ f ∣ Z := by
    refine hcop.dvd_of_dvd_mul_right ⟨m, ?_⟩
    rw [mul_comm Z K]
    exact h
  obtain ⟨t, rfl⟩ := hdvd
  have hKt : K * t = m := by
    have h1 : 2 ^ f * (K * t) = 2 ^ f * m := by
      calc 2 ^ f * (K * t) = K * (2 ^ f * t) := by ring
        _ = 2 ^ f * m := h
    exact Nat.mul_left_cancel (pow_pos (by norm_num : (0:ℕ) < 2) f) h1
  refine ⟨t, ?_, rfl⟩
  exact (Nat.odd_mul.mp (hKt ▸ hm)).2

theorem forall_smul_eq_of_card {H : Type v} [Group H] [MulAction H V] {Γ : SimpleGraph V}
    [GraphAction H Γ] {v : V} [Finite (MulAction.stabilizer H v)]
    (htr : ∀ w₁ w₂ : V, Γ.Adj v w₁ → Γ.Adj v w₂ →
      ∃ g : H, g • v = v ∧ g • w₁ = w₂)
    (htr2 : ∀ w x₁ x₂ : V, Γ.Adj v w → Γ.Adj v x₁ → Γ.Adj v x₂ → x₁ ≠ w → x₂ ≠ w →
      ∃ g : H, g • v = v ∧ g • w = w ∧ g • x₁ = x₂)
    {e N : ℕ} (hval : Nat.card (Γ.neighborSet v) = 2 ^ e + 1)
    (hsyl : ∀ P : Sylow 2 (MulAction.stabilizer H v), Nat.card P = 2 ^ e * N)
    (hQ : N ≤ Nat.card (CFSG.pCore 2 (MulAction.stabilizer H v)))
    {w w' : V} (hw : Γ.Adj v w) (hw' : Γ.Adj v w') (hww' : w ≠ w') {g : H}
    (hg : ∃ k, orderOf g = 2 ^ k) (hgv : g • v = v) (hgw : g • w = w) (hgw' : g • w' = w') :
    ∀ u, Γ.Adj v u → g • u = u := by
  intro u hu
  rcases Nat.eq_zero_or_pos e with rfl | he
  ·
    have hN2 : Nat.card (Γ.neighborSet v) = 2 := by simpa using hval
    have hpair : ({w, w'} : Set V) ⊆ Γ.neighborSet v := by
      intro x hx
      rcases hx with rfl | rfl
      · exact hw
      · exact hw'
    have hN_eq : ({w, w'} : Set V) = Γ.neighborSet v := by
      have hfin : Finite ↥(Γ.neighborSet v) :=
        (Nat.card_ne_zero.mp (by rw [hval]; positivity)).2
      refine Set.eq_of_subset_of_ncard_le hpair ?_ (Set.finite_coe_iff.mp hfin)
      rw [← Nat.card_coe_set_eq, hN2]
      simp [hww']
    have hu' : u ∈ ({w, w'} : Set V) := by rw [hN_eq]; exact hu
    rcases (by simpa using hu' : u = w ∨ u = w') with rfl | rfl
    · exact hgw
    · exact hgw'
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let X : Subgroup H := MulAction.stabilizer H v
    haveI hXfin : Finite X := inferInstance
    let Xw : Subgroup X := MulAction.stabilizer X w
    let XW : Subgroup X := Xw ⊓ MulAction.stabilizer X w'
    have hoddK : Odd (2 ^ e + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    have hKnot : ¬ 2 ∣ 2 ^ e + 1 :=
      fun h => (Nat.not_even_iff_odd.mpr hoddK) (even_iff_two_dvd.mpr h)
    have hXw : Xw.index = 2 ^ e + 1 := by
      rw [stabilizer_index_of_adj htr hw, hval]
    have hXw' : (MulAction.stabilizer X w').index = 2 ^ e + 1 := by
      rw [stabilizer_index_of_adj htr hw', hval]
    have hXWle : XW ≤ Xw := inf_le_left
    have hsub : XW.subgroupOf Xw = MulAction.stabilizer Xw w' := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨-, hx⟩
        simpa [Subgroup.smul_def] using hx
      · intro hx
        exact ⟨by simpa [Subgroup.smul_def] using MulAction.mem_stabilizer_iff.mp x.2,
          by simpa [Subgroup.smul_def] using hx⟩
    have hXWrel : XW.relIndex Xw = 2 ^ e := by
      have horbit : MulAction.orbit Xw w' = Γ.neighborSet v \ {w} :=
        orbit_stabilizer_eq_sdiff htr2 hw hw' hww'
      show (XW.subgroupOf Xw).index = 2 ^ e
      rw [hsub, MulAction.index_stabilizer, horbit,
        Set.ncard_sdiff_singleton_of_mem (s := Γ.neighborSet v) hw,
        ← Nat.card_coe_set_eq, hval]
      omega
    have hcardX : Nat.card X = (2 ^ e + 1) * Nat.card Xw := by
      rw [← Subgroup.card_mul_index Xw, hXw, mul_comm]
    have hcardXw : Nat.card Xw = 2 ^ e * Nat.card XW := by
      have h := Subgroup.relIndex_mul_card (H := XW) (K := Xw)
      rw [inf_eq_left.mpr hXWle, hXWrel] at h
      exact h.symm
    have hcardXmain : Nat.card X = (2 ^ e + 1) * (2 ^ e * Nat.card XW) := by
      rw [hcardX, hcardXw]
    obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := X)
    have hPcard : Nat.card P = 2 ^ e * N := hsyl P
    have hPodd : Odd (P : Subgroup X).index :=
      Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using P.not_dvd_index)
    have hcardX2 : Nat.card X = (2 ^ e * N) * (P : Subgroup X).index := by
      rw [← Subgroup.card_mul_index (P : Subgroup X), hPcard]
    have hmain : (2 ^ e + 1) * Nat.card XW = N * (P : Subgroup X).index := by
      have h1 : 2 ^ e * ((2 ^ e + 1) * Nat.card XW) =
          2 ^ e * (N * (P : Subgroup X).index) := by
        calc 2 ^ e * ((2 ^ e + 1) * Nat.card XW)
            = (2 ^ e + 1) * (2 ^ e * Nat.card XW) := by ring
          _ = Nat.card X := hcardXmain.symm
          _ = (2 ^ e * N) * (P : Subgroup X).index := hcardX2
          _ = 2 ^ e * (N * (P : Subgroup X).index) := by ring
      exact Nat.mul_left_cancel (pow_pos (by norm_num) e) h1
    obtain ⟨f, hf⟩ := P.isPGroup'.exists_card_eq
    have hef : e ≤ f := by
      have hdvd : 2 ^ e ∣ 2 ^ f := by
        rw [← hf, hPcard]
        exact dvd_mul_right _ _
      have hle := Nat.le_of_dvd (pow_pos (by norm_num) f) hdvd
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    obtain ⟨gN, hgN⟩ : ∃ gN, N = 2 ^ gN := by
      refine ⟨f - e, ?_⟩
      have h1 : 2 ^ e * N = 2 ^ e * 2 ^ (f - e) := by
        rw [← hPcard, hf, ← pow_add, Nat.add_sub_cancel' hef]
      exact Nat.mul_left_cancel (pow_pos (by norm_num) e) h1
    obtain ⟨t, htodd, hZ⟩ := exists_odd_factor hoddK ⟨gN, hgN⟩ hPodd hmain
    have hpcXw : CFSG.pCore 2 X ≤ Xw := pCore_two_le_of_not_dvd_index (by rw [hXw]; exact hKnot)
    have hpcXw' : CFSG.pCore 2 X ≤ MulAction.stabilizer X w' :=
      pCore_two_le_of_not_dvd_index (by rw [hXw']; exact hKnot)
    have hpcXW : CFSG.pCore 2 X ≤ XW := le_inf hpcXw hpcXw'
    have hpcN : Nat.card (CFSG.pCore 2 X) = N := by
      refine le_antisymm ?_ hQ
      obtain ⟨f', hf'⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2).exists_card_eq
      have hdvd : 2 ^ f' ∣ Nat.card XW := by
        rw [← hf']
        exact Subgroup.card_dvd_of_le hpcXW
      rw [hZ, hgN] at hdvd
      have hcop : Nat.Coprime (2 ^ f') t := htodd.coprime_two_left.pow_left f'
      have hdvd2 : 2 ^ f' ∣ 2 ^ gN := hcop.dvd_of_dvd_mul_right hdvd
      have hf'g : f' ≤ gN := by
        have hle := Nat.le_of_dvd (pow_pos (by norm_num) gN) hdvd2
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
      calc Nat.card (CFSG.pCore 2 X) = 2 ^ f' := hf'
        _ ≤ 2 ^ gN := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hf'g
        _ = N := hgN.symm
    have hgX : g ∈ X := by
      rw [MulAction.mem_stabilizer_iff]
      exact hgv
    let gX : X := ⟨g, hgX⟩
    have hgXw : gX ∈ Xw := by
      rw [MulAction.mem_stabilizer_iff]
      simpa [gX, X, Subgroup.smul_def] using hgw
    have hgXw' : gX ∈ MulAction.stabilizer X w' := by
      rw [MulAction.mem_stabilizer_iff]
      simpa [gX, X, Subgroup.smul_def] using hgw'
    have hgXW : gX ∈ XW := ⟨hgXw, hgXw'⟩
    obtain ⟨k, hk⟩ := hg
    have horderX : orderOf gX = 2 ^ k := by
      rw [← Subgroup.orderOf_coe gX]
      exact hk
    let Y : Subgroup X := Subgroup.zpowers gX
    have hYXW : Y ≤ XW := Subgroup.zpowers_le.mpr hgXW
    have hYp : IsPGroup 2 ↥Y := by
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, horderX]
    haveI : (CFSG.pCore 2 X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hjoinp : IsPGroup 2 ↥(CFSG.pCore 2 X ⊔ Y) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2).to_sup_of_normal_left hYp
    have hjoinle : CFSG.pCore 2 X ⊔ Y ≤ XW := sup_le hpcXW hYXW
    obtain ⟨j, hj⟩ := hjoinp.exists_card_eq
    have hdvd : 2 ^ j ∣ Nat.card XW := by
      rw [← hj]
      exact Subgroup.card_dvd_of_le hjoinle
    rw [hZ, hgN] at hdvd
    have hcop : Nat.Coprime (2 ^ j) t := htodd.coprime_two_left.pow_left j
    have hdvd2 : 2 ^ j ∣ 2 ^ gN := hcop.dvd_of_dvd_mul_right hdvd
    have hjg : j ≤ gN := by
      have hle := Nat.le_of_dvd (pow_pos (by norm_num) gN) hdvd2
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    have hleN : Nat.card ↥(CFSG.pCore 2 X ⊔ Y) ≤ N := by
      rw [hj]
      calc 2 ^ j ≤ 2 ^ gN := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hjg
        _ = N := hgN.symm
    have hgeN : N ≤ Nat.card ↥(CFSG.pCore 2 X ⊔ Y) := by
      rw [← hpcN]
      exact Subgroup.card_le_of_le le_sup_left
    have heqN : Nat.card ↥(CFSG.pCore 2 X ⊔ Y) = N := le_antisymm hleN hgeN
    haveI : Finite ↥(CFSG.pCore 2 X ⊔ Y) := inferInstance
    have hEq : CFSG.pCore 2 X ⊔ Y = CFSG.pCore 2 X := by
      exact (Subgroup.eq_of_le_of_card_ge (H := CFSG.pCore 2 X)
        (K := CFSG.pCore 2 X ⊔ Y) le_sup_left (by rw [heqN, hpcN])).symm
    have hYle : Y ≤ CFSG.pCore 2 X := by
      have h := le_sup_right (a := CFSG.pCore 2 X) (b := Y)
      rwa [hEq] at h
    have hgpc : gX ∈ CFSG.pCore 2 X := hYle (Subgroup.mem_zpowers gX)
    have hpcXu : CFSG.pCore 2 X ≤ MulAction.stabilizer X u :=
      pCore_two_le_of_not_dvd_index (by
        rw [stabilizer_index_of_adj htr hu, hval]
        exact hKnot)
    have hmem : gX ∈ MulAction.stabilizer X u := hpcXu hgpc
    rw [MulAction.mem_stabilizer_iff] at hmem
    simpa [gX, X, Subgroup.smul_def] using hmem

end Counting




section PathStabilizer

theorem eq_one_of_fix_nbPath_of_card (α : RankTwoAmalgam.{u}) {Y : Type w} [Group Y]
    [Finite Y] (c : α.Completion Y) (hc : c.IsFaithful) {j : ℕ}
    (hLT : IsLocallyTransHat α (2 * j + 1))
    (hodd1 : Odd (α.qOne + 1)) (hodd2 : Odd (α.qTwo + 1))
    (hsyl : ∀ (v : α.Γhat) [Finite (MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) v)]
      (P : Sylow 2 (MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) v)),
      Nat.card P = (α.qOne * α.qTwo) ^ j)
    {g : ↥(α.Ghat1 ⊔ α.Ghat2)} {p : GPath α.graphHat (2 * j + 1)} (hp : p.NoBack)
    (hfix : ∀ i, i ≤ 2 * j + 1 → g • p i = p i) (hg : ∃ k, orderOf g = 2 ^ k) : g = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : c.Γ := c.Θ hc (p 0)
  let q : GPath c.graph (2 * j + 1) := (c.graphCovering hc).pathMap p
  have hq : q ∈ GPath.nbPaths c.graph a (2 * j + 1) := by
    refine ⟨?_, ?_⟩
    · simp [q, a, GraphCovering.pathMap_apply]
    · exact ((c.graphCovering hc).noBack_pathMap_iff p).mpr hp
  have htrans : ∀ q₁ q₂ : GPath α.graphHat (2 * j + 1),
      q₁ ∈ GPath.nbPaths α.graphHat (p 0) (2 * j + 1) →
      q₂ ∈ GPath.nbPaths α.graphHat (p 0) (2 * j + 1) →
      ∃ u : ↥(α.Ghat1 ⊔ α.Ghat2), u • p 0 = p 0 ∧ u • q₁ = q₂ := by
    intro q₁ q₂ hq₁ hq₂
    obtain ⟨u, hu⟩ := hLT q₁ q₂ hq₁.2 hq₂.2 (by rw [hq₁.1, hq₂.1])
    refine ⟨u, ?_, hu⟩
    have h0 : u • q₁ 0 = q₂ 0 := by
      simpa [GPath.smul_apply] using
        congrArg (fun r : GPath α.graphHat (2 * j + 1) => r 0) hu
    rwa [hq₁.1, hq₂.1] at h0
  have hT : c.PathTrans a (2 * j + 1) :=
    c.lemma_F33_4 hc (p 0) (2 * j + 1) htrans
  haveI hfin0 : Finite (MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) (p 0)) := by
    let e := (c.stabIso hc (p 0)).equiv
    refine Finite.of_injective (fun x => (e x : ↥(c.φ1.range ⊔ c.φ2.range))) ?_
    intro x y hxy
    exact e.injective (Subtype.ext hxy)
  have hrel := RankTwoAmalgam.Completion.relIndex_stabPath (c := c) hc hT hq
  have hqvodd : Odd (α.qv (CosetGeom.vtype a) + 1) := by
    cases hb : CosetGeom.vtype a
    · simpa [RankTwoAmalgam.qv, hb] using hodd1
    · simpa [RankTwoAmalgam.qv, hb] using hodd2
  have hqvprod : α.qv (CosetGeom.vtype a) * α.qv (!CosetGeom.vtype a) =
      α.qOne * α.qTwo := by
    cases hb : CosetGeom.vtype a <;> simp [RankTwoAmalgam.qv, hb, mul_comm]
  have hpathNum : α.pathNum (CosetGeom.vtype a) (2 * j + 1) =
      (α.qv (CosetGeom.vtype a) + 1) * (α.qOne * α.qTwo) ^ j := by
    rw [RankTwoAmalgam.pathNum_odd, hqvprod]
  have hle : (q.stabPath : Subgroup c.G0) ≤ c.stv a := GPath.stabPath_le_stabilizer q hq.1
  have hrelMul := Subgroup.relIndex_mul_card (H := (q.stabPath : Subgroup c.G0)) (K := c.stv a)
  rw [inf_eq_left.mpr hle, hrel, hpathNum] at hrelMul
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := c.stv a)
  have hPcard : Nat.card P = (α.qOne * α.qTwo) ^ j := by
    let e := (c.stabIso hc (p 0)).equiv
    let P' : Sylow 2 (MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) (p 0)) :=
      P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have h1 : Nat.card P' = (α.qOne * α.qTwo) ^ j := hsyl (p 0) P'
    have h2 : Nat.card P' = Nat.card P := by
      rw [show (P' : Subgroup ↥(MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) (p 0))) =
          (P : Subgroup (c.stv a)).map e.symm.toMonoidHom from
        Sylow.coe_mapSurjective e.symm.surjective P]
      exact Subgroup.card_map_of_injective (K := (P : Subgroup (c.stv a)))
        (f := e.symm.toMonoidHom) e.symm.injective
    rw [← h2]
    exact h1
  have hMpos : 0 < (α.qOne * α.qTwo) ^ j := by
    haveI : Nonempty ↥(P : Subgroup (c.stv a)) :=
      ⟨⟨1, Subgroup.one_mem (P : Subgroup (c.stv a))⟩⟩
    have hPpos : 0 < Nat.card P := Nat.card_pos
    rwa [hPcard] at hPpos
  have hcardStv : Nat.card (c.stv a) =
      Nat.card (q.stabPath : Subgroup c.G0) *
        ((α.qv (CosetGeom.vtype a) + 1) * (α.qOne * α.qTwo) ^ j) := by
    rw [← hrelMul]
    ring
  have hPodd : Odd (P : Subgroup (c.stv a)).index :=
    Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using P.not_dvd_index)
  have hcardStv2 : Nat.card (c.stv a) =
      (α.qOne * α.qTwo) ^ j * (P : Subgroup (c.stv a)).index := by
    rw [← Subgroup.card_mul_index (P : Subgroup (c.stv a)), hPcard]
  have hcancel : Nat.card (q.stabPath : Subgroup c.G0) * (α.qv (CosetGeom.vtype a) + 1) =
      (P : Subgroup (c.stv a)).index := by
    have h1 : (α.qOne * α.qTwo) ^ j *
        (Nat.card (q.stabPath : Subgroup c.G0) * (α.qv (CosetGeom.vtype a) + 1)) =
        (α.qOne * α.qTwo) ^ j * (P : Subgroup (c.stv a)).index := by
      calc (α.qOne * α.qTwo) ^ j *
            (Nat.card (q.stabPath : Subgroup c.G0) * (α.qv (CosetGeom.vtype a) + 1))
          = Nat.card (q.stabPath : Subgroup c.G0) *
            ((α.qv (CosetGeom.vtype a) + 1) * (α.qOne * α.qTwo) ^ j) := by ring
        _ = Nat.card (c.stv a) := hcardStv.symm
        _ = (α.qOne * α.qTwo) ^ j * (P : Subgroup (c.stv a)).index := hcardStv2
    exact Nat.mul_left_cancel hMpos h1
  have hoddStab : Odd (Nat.card (q.stabPath : Subgroup c.G0)) :=
    hPodd.of_dvd_nat ⟨α.qv (CosetGeom.vtype a) + 1, hcancel.symm⟩
  obtain ⟨k, hk⟩ := hg
  have hgmap : c.theta0 hc g ∈ (q.stabPath : Subgroup c.G0) := by
    have hmap := (c.lemma_F33_3 hc (p 0) p rfl).1
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (c.theta0 hc) (GPath.mem_stabPath_iff.mpr hfix)
  have horderStab : orderOf (c.theta0 hc g) ∣ Nat.card (q.stabPath : Subgroup c.G0) :=
    Subgroup.orderOf_dvd_natCard _ hgmap
  have horder2 : orderOf (c.theta0 hc g) ∣ 2 ^ k := by
    rw [← hk]
    exact orderOf_map_dvd (c.theta0 hc) g
  have hcop : Nat.Coprime (Nat.card (q.stabPath : Subgroup c.G0)) (2 ^ k) :=
    hoddStab.coprime_two_right.pow_right k
  have hOrderOne : orderOf (c.theta0 hc g) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderStab horder2
  have htheta1 : c.theta0 hc g = 1 := orderOf_eq_one_iff.mp hOrderOne
  exact (c.stabIso hc (p 0)).inj g (by simpa using hfix 0 (Nat.zero_le _)) htheta1

end PathStabilizer

end CFSG.Quasithin.Stroth
