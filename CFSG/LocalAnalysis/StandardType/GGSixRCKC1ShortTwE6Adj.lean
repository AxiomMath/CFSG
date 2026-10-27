module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerU
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3Done
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split

public section

namespace CFSG.StandardType.RCKC1

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot

local instance rckTwE6Adj_neZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance rckTwE6Adj_neZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance rckTwE6Adj_neZeroTw : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

private theorem rckTwE6Adj_exists_pow_two_eq_one_of_mem_pCoreOf {X : Type*} [Group X]
    {H : Subgroup X} {k : X} (hk : k ∈ pCoreOf 2 H) :
    ∃ b : ℕ, k ^ (2 ^ b) = 1 := by
  have hP : IsPGroup 2 (pCoreOf 2 H) := by
    change IsPGroup 2 ((pCore 2 ↥H).map H.subtype)
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  obtain ⟨b, hb⟩ := hP ⟨k, hk⟩
  exact ⟨b, by simpa using congrArg (Subtype.val) hb⟩

theorem pCoreOf_two_le_of_levi_decomp {G : Type*} [Group G] {C Q M L : Subgroup G}
    (hQM : Q ⊓ M = ⊥) (hMN : M ≤ normalizer (Q : Set G)) (hLC : L ≤ C) (hLM : L ≤ M)
    (hL : ∀ N : Subgroup L, N.Normal → IsPGroup 2 N → N = ⊥)
    (hdec : ∀ g ∈ C, ∃ q ∈ Q, ∃ m ∈ M, g = q * m)
    (h2 : ∀ g ∈ C, ∀ q ∈ Q, ∀ m ∈ M, g = q * m → (∃ b : ℕ, m ^ 2 ^ b = 1) → m ∈ L) :
    pCoreOf 2 C ≤ Q := by
  have hPC : pCoreOf 2 C ≤ C := Subgroup.map_subtype_le (pCore 2 ↥C)
  have hPconj : ∀ c ∈ C, ∀ g ∈ pCoreOf 2 C, c * g * c⁻¹ ∈ pCoreOf 2 C := by
    intro c hc g hg
    exact (mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hc) g).1 hg
  let S : Subgroup G :=
    { carrier := {m | m ∈ M ∧ ∃ q ∈ Q, q * m ∈ pCoreOf 2 C}
      one_mem' := ⟨M.one_mem, 1, Q.one_mem, by simp⟩
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haM, q₁, hq₁, h₁⟩ := ha
        obtain ⟨hbM, q₂, hq₂, h₂⟩ := hb
        refine ⟨M.mul_mem haM hbM, q₁ * (a * q₂ * a⁻¹), Q.mul_mem hq₁ ?_, ?_⟩
        · exact (mem_normalizer_iff.1 (hMN haM) q₂).1 hq₂
        · have e : (q₁ * (a * q₂ * a⁻¹)) * (a * b) = (q₁ * a) * (q₂ * b) := by group
          rw [e]
          exact Subgroup.mul_mem _ h₁ h₂
      inv_mem' := by
        intro a ha
        obtain ⟨haM, q, hq, hqa⟩ := ha
        refine ⟨M.inv_mem haM, a⁻¹ * q⁻¹ * a, ?_, ?_⟩
        · have h := (mem_normalizer_iff.1 (hMN (M.inv_mem haM)) q⁻¹).1 (Q.inv_mem hq)
          simpa using h
        · have e : (a⁻¹ * q⁻¹ * a) * a⁻¹ = (q * a)⁻¹ := by group
          rw [e]
          exact Subgroup.inv_mem _ hqa }
  have hSmem : ∀ m : G, m ∈ S ↔ m ∈ M ∧ ∃ q ∈ Q, q * m ∈ pCoreOf 2 C := fun m => Iff.rfl
  have hsplit : ∀ (q m : G) (n : ℕ), q ∈ Q → m ∈ M →
      ∃ qn ∈ Q, (q * m) ^ n = qn * m ^ n := by
    intro q m n hq hmM
    induction n with
    | zero => exact ⟨1, Q.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨qn, hqn, hqn'⟩ := ih
      have hconj : m ^ n * q * (m ^ n)⁻¹ ∈ Q :=
        (mem_normalizer_iff.1 (Subgroup.pow_mem _ (hMN hmM) n) q).1 hq
      refine ⟨qn * (m ^ n * q * (m ^ n)⁻¹), Q.mul_mem hqn hconj, ?_⟩
      rw [pow_succ, hqn', pow_succ]
      group
  have hS2 : ∀ m ∈ S, ∃ b : ℕ, m ^ 2 ^ b = 1 := by
    intro m hm
    obtain ⟨hmM, q, hq, hqm⟩ := (hSmem m).1 hm
    obtain ⟨b, hb⟩ := rckTwE6Adj_exists_pow_two_eq_one_of_mem_pCoreOf hqm
    obtain ⟨qn, hqn, hqn'⟩ := hsplit q m (2 ^ b) hq hmM
    have hmQ : m ^ 2 ^ b ∈ Q := by
      have e : m ^ 2 ^ b = qn⁻¹ * (q * m) ^ 2 ^ b := by rw [hqn']; group
      rw [e, hb, mul_one]
      exact Q.inv_mem hqn
    have hbot : m ^ 2 ^ b ∈ (⊥ : Subgroup G) := by
      rw [← hQM]
      exact mem_inf.2 ⟨hmQ, Subgroup.pow_mem M hmM _⟩
    exact ⟨b, (mem_bot).1 hbot⟩
  have hSL : S ≤ L := by
    intro m hm
    obtain ⟨hmM, q, hq, hqm⟩ := (hSmem m).1 hm
    have hgC : q * m ∈ C := hPC hqm
    exact h2 (q * m) hgC q hq m hmM rfl (hS2 m ⟨hmM, q, hq, hqm⟩)
  have hLN : L ≤ normalizer (S : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      obtain ⟨hsM, q, hq, hqs⟩ := (hSmem s).1 hs
      refine (hSmem (x * s * x⁻¹)).2
        ⟨M.mul_mem (M.mul_mem (hLM hx) hsM) (M.inv_mem (hLM hx)),
          x * q * x⁻¹, (mem_normalizer_iff.1 (hMN (hLM hx)) q).1 hq, ?_⟩
      have e : (x * q * x⁻¹) * (x * s * x⁻¹) = x * (q * s) * x⁻¹ := by group
      rw [e]
      exact hPconj x (hLC hx) (q * s) hqs
    · intro hs
      obtain ⟨hsM, q, hq, hqs⟩ := (hSmem (x * s * x⁻¹)).1 hs
      have hxL : x⁻¹ ∈ L := Subgroup.inv_mem _ hx
      have hsM' : s ∈ M := by
        have e : s = x⁻¹ * (x * s * x⁻¹) * x := by group
        rw [e]
        exact M.mul_mem (M.mul_mem (hLM hxL) hsM) (hLM hx)
      have hq' : x⁻¹ * q * x ∈ Q := by
        have h := (mem_normalizer_iff.1 (hMN (hLM hxL)) q).1 hq
        simpa using h
      refine (hSmem s).2 ⟨hsM', x⁻¹ * q * x, hq', ?_⟩
      have e : (x⁻¹ * q * x) * s = x⁻¹ * (q * (x * s * x⁻¹)) * x := by group
      rw [e]
      simpa using hPconj x⁻¹ (hLC hxL) (q * (x * s * x⁻¹)) hqs
  have hSN : (S.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSL).2 hLN
  have hS2L : IsPGroup 2 (S.subgroupOf L) := by
    intro x
    have hxS : ((x : ↥L) : G) ∈ S := by
      have h := x.2
      rwa [mem_subgroupOf] at h
    obtain ⟨b, hb⟩ := hS2 ((x : ↥L) : G) hxS
    exact ⟨b, Subtype.ext (Subtype.ext (by simpa using hb))⟩
  have hSbot : S = ⊥ := by
    have hd : Disjoint S L := Subgroup.subgroupOf_eq_bot.1 (hL (S.subgroupOf L) hSN hS2L)
    have h1 : S ⊓ L = ⊥ := hd.eq_bot
    rwa [inf_of_le_left hSL] at h1
  intro g hg
  obtain ⟨q, hq, m, hm, hqm⟩ := hdec g (hPC hg)
  have hmS : m ∈ S := (hSmem m).2 ⟨hm, q, hq, hqm ▸ hg⟩
  rw [hSbot, mem_bot] at hmS
  rw [hqm, hmS, mul_one]
  exact hq

section Torus


variable {K : Type} [Field K]

private theorem rckTwE6Adj_perm_mem_nodes16 {i : Fin TwistTag.E6.tag.rank}
    (hi : i ∈ E6Pilot.nodes16) : TwistTag.E6.perm i ∈ E6Pilot.nodes16 := by
  simp only [E6Pilot.nodes16] at hi ⊢
  have h : ∀ j : Fin TwistTag.E6.tag.rank, j ≠ 0 ∧ j ≠ 5 →
      TwistTag.E6.perm j ≠ 0 ∧ TwistTag.E6.perm j ≠ 5 := by
    decide
  exact h i hi

private theorem rckTwE6Adj_twistHom_mem_parabolicLevi (σ : K →+* K) {t : TwistTag}
    {A : Set (Fin t.tag.rank)} (hA : ∀ i ∈ A, t.perm i ∈ A) {g : ModGL t.tag K}
    (hg : g ∈ parabolicLevi t.tag K A) :
    twistHom t K σ g ∈ parabolicLevi t.tag K A := by
  have hM : parabolicLevi t.tag K A = Subgroup.closure
      (Set.range (fun p : Fin t.tag.rank × Kˣ => torusElt t.tag K p.1 p.2) ∪
        {g | ∃ j ∈ A, ∃ c : K, g = xUnit t.tag K j c ∨ g = yUnit t.tag K j c}) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hM] at hg ⊢
  induction hg using Subgroup.closure_induction'' with
  | mem g hgs =>
    rcases hgs with ⟨⟨i, u⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · rw [twistHom_torusElt]
      exact Subgroup.subset_closure (Or.inl ⟨(t.perm i, Units.map σ.toMonoidHom u), rfl⟩)
    · rw [twistHom_xUnit]
      exact Subgroup.subset_closure (Or.inr ⟨t.perm j, hA j hj, σ c, Or.inl rfl⟩)
    · rw [twistHom_yUnit]
      exact Subgroup.subset_closure (Or.inr ⟨t.perm j, hA j hj, σ c, Or.inr rfl⟩)
  | inv_mem g hgs =>
    rw [map_inv]
    refine Subgroup.inv_mem _ ?_
    rcases hgs with ⟨⟨i, u⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · rw [twistHom_torusElt]
      exact Subgroup.subset_closure (Or.inl ⟨(t.perm i, Units.map σ.toMonoidHom u), rfl⟩)
    · rw [twistHom_xUnit]
      exact Subgroup.subset_closure (Or.inr ⟨t.perm j, hA j hj, σ c, Or.inl rfl⟩)
    · rw [twistHom_yUnit]
      exact Subgroup.subset_closure (Or.inr ⟨t.perm j, hA j hj, σ c, Or.inr rfl⟩)
  | one => simp
  | mul g h hg hh ihg ihh =>
    rw [map_mul]
    exact Subgroup.mul_mem _ ihg ihh

private theorem rckTwE6Adj_yLeviF4_le_parabolicLevi :
    E6Pilot.yLeviF4 K ≤ parabolicLevi .E6 K E6Pilot.nodes16 := by
  have hx : ∀ (i : Fin Tag.E6.rank) (c : K), i ∈ E6Pilot.nodes16 →
      xUnit .E6 K i c ∈ parabolicLevi .E6 K E6Pilot.nodes16 :=
    fun i c hi => Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hi, c, Or.inl rfl⟩)
  have hy : ∀ (i : Fin Tag.E6.rank) (c : K), i ∈ E6Pilot.nodes16 →
      yUnit .E6 K i c ∈ parabolicLevi .E6 K E6Pilot.nodes16 :=
    fun i c hi => Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hi, c, Or.inr rfl⟩)
  have hn1 : (1 : Fin Tag.E6.rank) ∈ E6Pilot.nodes16 := ⟨by decide, by decide⟩
  have hn2 : (2 : Fin Tag.E6.rank) ∈ E6Pilot.nodes16 := ⟨by decide, by decide⟩
  have hn3 : (3 : Fin Tag.E6.rank) ∈ E6Pilot.nodes16 := ⟨by decide, by decide⟩
  have hn4 : (4 : Fin Tag.E6.rank) ∈ E6Pilot.nodes16 := ⟨by decide, by decide⟩
  refine (closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
      rfl | rfl | rfl
    · rw [E6Pilot.f4OrbitXUnit_zero]
      exact hx 1 c hn1
    · rw [E6Pilot.f4OrbitXUnit_one]
      exact hx 3 c hn3
    · rw [E6Pilot.f4OrbitXUnit_two]
      exact Subgroup.mul_mem _ (hx 2 c hn2) (hx 4 c hn4)
  · rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
      rfl | rfl | rfl
    · rw [E6Pilot.f4OrbitYUnit_zero]
      exact hy 1 c hn1
    · rw [E6Pilot.f4OrbitYUnit_one]
      exact hy 3 c hn3
    · rw [E6Pilot.f4OrbitYUnit_two]
      exact Subgroup.mul_mem _ (hy 2 c hn2) (hy 4 c hn4)

theorem rckTwE6_torus_inf_centralizer_le_normalizer_yLeviF4 [CharP K 2] :
    torusGroup .E6 K ⊓
        centralizer ({(E6Pilot.e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) ≤
      normalizer (E6Pilot.yLeviF4 K : Set (ModGL .E6 K)) := by
  intro h hh
  obtain ⟨hhT, hhC⟩ := mem_inf.1 hh
  set n := (E6Pilot.e6RepConj K 1 : ModGL .E6 K) with hn
  set φ : ModGL .E6 K →* ModGL .E6 K := (MulAut.conj n).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj n).injective
  have hE : φ (E6Pilot.e6ASRep K 1 : ModGL .E6 K) = (E6Pilot.e6Rep K 1 : ModGL .E6 K) :=
    E6Pilot.conj_e6RepConj_e6ASRep_one
  have hφT : φ h ∈ torusGroup .E6 K := by
    have h1 : φ h = n * h * n⁻¹ := MulAut.conj_apply n h
    rw [h1]
    exact (mem_normalizer_iff.1 (E6Pilot.coe_e6RepConj_mem_normalizer_torusGroup 1) h).1 hhT
  have hφC : φ h ∈
      centralizer ({(E6Pilot.e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) := by
    rw [mem_centralizer_singleton_iff] at hhC ⊢
    calc φ h * (E6Pilot.e6Rep K 1 : ModGL .E6 K)
        = φ h * φ (E6Pilot.e6ASRep K 1 : ModGL .E6 K) := by rw [hE]
      _ = φ (h * (E6Pilot.e6ASRep K 1 : ModGL .E6 K)) := by rw [map_mul]
      _ = φ ((E6Pilot.e6ASRep K 1 : ModGL .E6 K) * h) := by rw [hhC]
      _ = φ (E6Pilot.e6ASRep K 1 : ModGL .E6 K) * φ h := by rw [map_mul]
      _ = (E6Pilot.e6Rep K 1 : ModGL .E6 K) * φ h := by rw [hE]
  have hmem : φ h ∈ normalizer (E6Pilot.yLeviGL K : Set (ModGL .E6 K)) :=
    E6Pilot.torus_inf_centralizer_le_normalizer_yLeviGL (mem_inf.2 ⟨hφT, hφC⟩)
  have hconj : ∀ y : ModGL .E6 K, φ h * φ y * (φ h)⁻¹ = φ (h * y * h⁻¹) := fun y => by
    rw [map_mul, map_mul, map_inv]
  rw [E6Pilot.yLeviGL_eq_map_yLeviF4] at hmem
  rw [mem_normalizer_iff] at hmem ⊢
  intro x
  constructor
  · intro hx
    have h1 : φ x ∈ (E6Pilot.yLeviF4 K).map φ := ⟨x, hx, rfl⟩
    have h2 := (hmem (φ x)).1 h1
    rw [hconj x] at h2
    exact (Subgroup.mem_map_iff_mem (f := φ) hφinj).1 h2
  · intro hx
    have h1 : φ h * φ x * (φ h)⁻¹ ∈ (E6Pilot.yLeviF4 K).map φ := by
      rw [hconj x]
      exact ⟨h * x * h⁻¹, hx, rfl⟩
    exact (Subgroup.mem_map_iff_mem (f := φ) hφinj).1 ((hmem (φ x)).2 h1)

theorem rckTwE6_pow_card_sub_one_of_mem_torusGroup [Finite K] {h : ModGL .E6 K}
    (hh : h ∈ torusGroup .E6 K) : h ^ (Nat.card K - 1) = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [rootDiagUnit_pow]
  have h1 : l ^ (Nat.card K - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card K (Fintype.ofFinite K)]
    funext i
    refine Units.ext ?_
    rw [Pi.pow_apply, Pi.one_apply, Units.val_pow_eq_pow_val, Units.val_one]
    exact @FiniteField.pow_card_sub_one_eq_one K _ (Fintype.ofFinite K) _
      (Units.ne_zero _)
  rw [h1, rootDiagUnit_one]

theorem rckTwE6_mem_yLeviF4_of_pow_two [Finite K] [CharP K 2] {m : ModGL .E6 K}
    (hm : m ∈ parabolicLevi .E6 K E6Pilot.nodes16)
    (hmy : m ∈ centralizer ({(E6Pilot.e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)))
    {b : ℕ} (hb : m ^ 2 ^ b = 1) : m ∈ E6Pilot.yLeviF4 K := by
  set T := torusGroup .E6 K ⊓
    centralizer ({(E6Pilot.e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) with hTdef
  have hT : T ≤ normalizer (E6Pilot.yLeviF4 K : Set (ModGL .E6 K)) :=
    rckTwE6_torus_inf_centralizer_le_normalizer_yLeviF4
  have hAS : E6Pilot.LeviStabilizerAS K :=
    E6Pilot.leviStabilizerAS_of_P4 fun u hu hc =>
      E6Pilot.mem_yLeviF4_of_mem_parabolicLeviUnipotent hu (mem_centralizer_singleton_iff.1 hc)
  have hSup : m ∈ E6Pilot.yLeviF4 K ⊔ T := hAS m hm hmy
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (E6Pilot.yLeviF4 K) T hT
  change m ∈ (↑(E6Pilot.yLeviF4 K ⊔ T) : Set (ModGL .E6 K)) at hSup
  rw [hcoe] at hSup
  obtain ⟨l, hl, t, ht, hlt⟩ := hSup
  subst hlt
  have htT : t ∈ torusGroup .E6 K := (mem_inf.1 (hTdef ▸ ht)).1
  have hnorm : t ∈ normalizer (E6Pilot.yLeviF4 K : Set (ModGL .E6 K)) := hT ht
  have hmain : ∀ n : ℕ, (l * t) ^ n * (t ^ n)⁻¹ ∈ E6Pilot.yLeviF4 K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have htconj : t ^ n * l * (t ^ n)⁻¹ ∈ E6Pilot.yLeviF4 K :=
        (mem_normalizer_iff.1 (Subgroup.pow_mem _ hnorm n) l).1 hl
      have hstep : (l * t) ^ (n + 1) * (t ^ (n + 1))⁻¹ =
          ((l * t) ^ n * (t ^ n)⁻¹) * (t ^ n * l * (t ^ n)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [hstep]
      exact Subgroup.mul_mem _ ih htconj
  have htL : t ^ 2 ^ b ∈ E6Pilot.yLeviF4 K := by
    have h := hmain (2 ^ b)
    rw [hb, one_mul] at h
    exact inv_mem_iff.1 h
  have ht1 : t ^ (Nat.card K - 1) = 1 :=
    rckTwE6_pow_card_sub_one_of_mem_torusGroup htT
  have hodd : Odd (Nat.card K - 1) := by
    obtain ⟨n, -, hcard⟩ := @FiniteField.card K _ (Fintype.ofFinite K) 2 _
    rw [@Nat.card_eq_fintype_card K (Fintype.ofFinite K), hcard]
    have hnpos : 0 < (n : ℕ) := n.pos
    obtain ⟨k, hk⟩ : ∃ k, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by omega⟩
    rw [hk, pow_succ]
    have hpos : 0 < 2 ^ k := by positivity
    exact ⟨2 ^ k - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ b) (orderOf t) := by
    have hord : orderOf t ∣ Nat.card K - 1 := orderOf_dvd_iff_pow_eq_one.2 ht1
    exact Nat.Coprime.of_dvd_right hord ((Nat.coprime_two_right.2 hodd).pow_right b).symm
  obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime (x := t) (n := 2 ^ b) hcop
  have hmem : t ∈ E6Pilot.yLeviF4 K := by
    rw [← he]
    exact Subgroup.pow_mem _ htL e
  exact Subgroup.mul_mem _ hl hmem

end Torus

section Core


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem rckTwE6_parabolicRadical_le_centralizer (c d : K) :
    parabolicRadical .E6 K E6Pilot.nodes16 ≤
      centralizer ({pinnedX .E6 K E6Pilot.yBetaAS c * pinnedX .E6 K E6Pilot.yAlphaAS d} :
        Set (ModGL .E6 K)) := by
  rw [parabolicRadical, E6Pilot.parabolicRadicalRoots_nodes16]
  refine iSup₂_le fun γ hγ => (closure_le _).2 ?_
  rintro _ ⟨x, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  obtain ⟨h1, h2⟩ := E6Pilot.yRadicalAS_check γ (mem_rootFinset.2 hγ.1) hγ.2
  have hα := mem_rootFinset.1 (E6Pilot.yU5_check.1 E6Pilot.yAlphaAS (by simp [E6Pilot.yU5])).1
  have hβ := mem_rootFinset.1 (E6Pilot.yU5_check.1 E6Pilot.yBetaAS (by simp [E6Pilot.yU5])).1
  exact ((classD4_commute_pinnedX E6Pilot.e6_simplyLaced hγ.1 hβ h2 x c).mul_right
    (classD4_commute_pinnedX E6Pilot.e6_simplyLaced hγ.1 hα h1 x d)).eq

theorem rckTwE6_exists_mul_of_mem_centralizer [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {g : graphFixedRootGroup TwistTag.E6 K σ}
    (hg : g ∈ centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
      Set (graphFixedRootGroup TwistTag.E6 K σ))) :
    ∃ q ∈ (uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
      ∃ m ∈ (parabolicLevi TwistTag.E6.tag K E6Pilot.nodes16).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ), g = q * m := by
  have hCA : graphFixedRootGroup TwistTag.E6 K σ ≤ adjointGroup .E6 K := fun x hx =>
    (graphFixedRootGroup_le _ _ _ hx).1
  have hQA : parabolicRadical .E6 K E6Pilot.nodes16 ≤ adjointGroup .E6 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  have hu : stdRep K 1 = (E6Pilot.e6ASRep K 1 : ModGL .E6 K) := twistedE6ClassU_eq_e6ASRep
  have hgC : (g.1 : ModGL .E6 K) ∈
      centralizer ({(E6Pilot.e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL TwistTag.E6.tag K)) := by
    have hx1 := hg
    rw [mem_centralizer_subtype_iff] at hx1
    have hx' : (g.1 : ModGL .E6 K) ∈
        centralizer ({stdRep K 1} : Set (ModGL TwistTag.E6.tag K)) := hx1
    rw [hu] at hx'
    exact hx'
  have hgP : (g.1 : ModGL .E6 K) ∈ parabolicSubgroup .E6 K E6Pilot.nodes16 := by
    have h1 := E6Pilot.centralizer_e6ASRep_one_le (mem_inf.2 ⟨hgC, hCA g.2⟩)
    have hle : parabolicRadical .E6 K E6Pilot.nodes16 ⊔
        (parabolicLevi .E6 K E6Pilot.nodes16 ⊓
          centralizer ({(E6Pilot.e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL TwistTag.E6.tag K))) ≤
        parabolicSubgroup .E6 K E6Pilot.nodes16 := by
      rw [← parabolicRadical_sup_parabolicLevi (τ := .E6) (K := K) E6Pilot.nodes16]
      exact sup_le_sup_left inf_le_left _
    exact hle h1
  obtain ⟨⟨q, m⟩, ⟨hq, hm, hqm⟩, huniq⟩ :=
    (parabolic_root_radical_Levi_factors TwistTag.E6.tag K E6Pilot.nodes16).2.2.2.2.2.2.1
      (g.1) hgP
  have hF : twistHom TwistTag.E6 K σ (g.1 : ModGL TwistTag.E6.tag K) = g.1 :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ g.2)).2
  have hFq : twistHom TwistTag.E6 K σ q ∈ parabolicRadical .E6 K E6Pilot.nodes16 :=
    twistHom_mem_parabolicRadical_nodes16 σ hq
  have hFm : twistHom TwistTag.E6 K σ m ∈ parabolicLevi .E6 K E6Pilot.nodes16 :=
    rckTwE6Adj_twistHom_mem_parabolicLevi (t := TwistTag.E6) (A := E6Pilot.nodes16) σ
      (fun i hi => rckTwE6Adj_perm_mem_nodes16 hi) hm
  have huniq' := huniq (twistHom TwistTag.E6 K σ q, twistHom TwistTag.E6 K σ m)
    ⟨hFq, hFm, by rw [← hF, hqm, map_mul]⟩
  have hFqq : twistHom TwistTag.E6 K σ q = q := congrArg Prod.fst huniq'
  have hqC : q ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (mem_inf.2
      ⟨parabolicRadical_le_posUnipotent _ hq,
        (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hQA hq, hFqq⟩⟩)
  have hmC : m ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    have e : m = q⁻¹ * (g.1 : ModGL TwistTag.E6.tag K) := by rw [hqm]; group
    rw [e]
    exact mul_mem (inv_mem hqC) g.2
  have hqQ : (⟨q, hqC⟩ : graphFixedRootGroup TwistTag.E6 K σ) ∈
      (uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
    rw [mem_subgroupOf]
    change ((⟨q, hqC⟩ : graphFixedRootGroup TwistTag.E6 K σ) :
      ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K E6Pilot.nodes16 ⊓
        graphFixedRootGroup TwistTag.E6 K σ
    simpa using mem_inf.2 ⟨hq, hqC⟩
  have hmQ : (⟨m, hmC⟩ : graphFixedRootGroup TwistTag.E6 K σ) ∈
      (parabolicLevi TwistTag.E6.tag K E6Pilot.nodes16).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) := by
    rw [mem_subgroupOf]
    simpa using hm
  exact ⟨⟨q, hqC⟩, hqQ, ⟨m, hmC⟩, hmQ, Subtype.ext hqm⟩

theorem rckTwE6_pCoreOf_centralizer_stdRepC_one_le [CharP K 2] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    pCoreOf 2 (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) ≤
      (uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hu : stdRep K 1 = (E6Pilot.e6ASRep K 1 : ModGL .E6 K) := twistedE6ClassU_eq_e6ASRep
  have hLM : (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      (parabolicLevi TwistTag.E6.tag K E6Pilot.nodes16).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) := by
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact rckTwE6Adj_yLeviF4_le_parabolicLevi (mem_inf.1 hx).1
  have hQM : (uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊓
      (parabolicLevi TwistTag.E6.tag K E6Pilot.nodes16).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    rw [mem_subgroupOf] at hx1 hx2
    have hx' : (x : ModGL TwistTag.E6.tag K) ∈ parabolicRadical .E6 K E6Pilot.nodes16 ⊓
        parabolicLevi .E6 K E6Pilot.nodes16 :=
      mem_inf.2 ⟨(mem_inf.1 hx1).1, hx2⟩
    rw [parabolicRadical_inf_parabolicLevi] at hx'
    exact Subtype.ext hx'
  have hMN : (parabolicLevi TwistTag.E6.tag K E6Pilot.nodes16).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) ≤
      normalizer ((uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    have hxN : (x : ModGL TwistTag.E6.tag K) ∈
        normalizer (uRadical σ : Set (ModGL TwistTag.E6.tag K)) :=
      inf_normalizer_le_normalizer_inf (mem_inf.2
        ⟨(parabolicLevi_le_parabolicSubgroup _).trans
          (parabolicSubgroup_le_normalizer_parabolicRadical _) hx, le_normalizer x.2⟩)
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.1 hxN y
  have hLC : (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_centralizer_subtype_iff]
    have h := E6Pilot.yLeviF4_le_centralizer (mem_inf.1 hx).1
    rw [← twistedE6ClassU_eq_e6ASRep] at h
    exact h
  have hL : ∀ N : Subgroup ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)),
      N.Normal → IsPGroup 2 N → N = ⊥ := by
    have hLCu : uLevi σ ≤ graphFixedRootGroup TwistTag.E6 K σ := inf_le_right
    have := isSimpleGroup_uLevi hf hk hK hσ
    have := isPerfect_uLevi hf hk hK hσ
    exact forall_normal_isPGroup_eq_bot_of_mulEquiv' (subgroupOfEquivOfLe hLCu).symm
      fun N hN hp => forall_normal_isPGroup_eq_bot_of_isPerfect N hN hp
  exact pCoreOf_two_le_of_levi_decomp hQM hMN hLC hLM hL
    (fun g hg => rckTwE6_exists_mul_of_mem_centralizer hK hσ hg)
    (fun g hg q hq m hm hgqm hb => by
      obtain ⟨b, hb⟩ := hb
      have hmM : (m : ModGL TwistTag.E6.tag K) ∈ parabolicLevi .E6 K E6Pilot.nodes16 :=
        mem_subgroupOf.1 hm
      have hgC : (g : ModGL TwistTag.E6.tag K) ∈
          centralizer ({(E6Pilot.e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL TwistTag.E6.tag K)) := by
        have hx1 := hg
        rw [mem_centralizer_subtype_iff] at hx1
        have hx' : (g : ModGL TwistTag.E6.tag K) ∈
            centralizer ({stdRep K 1} : Set (ModGL TwistTag.E6.tag K)) := hx1
        rw [hu] at hx'
        exact hx'
      have hqC : (q : ModGL TwistTag.E6.tag K) ∈
          centralizer ({(E6Pilot.e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL TwistTag.E6.tag K)) :=
        E6Pilot.parabolicRadical_nodes16_le_centralizer (mem_inf.1 (mem_subgroupOf.1 hq)).1
      have hgqm' : (g : ModGL TwistTag.E6.tag K) =
          (q : ModGL TwistTag.E6.tag K) * (m : ModGL TwistTag.E6.tag K) :=
        congrArg Subtype.val hgqm
      have hmy : (m : ModGL TwistTag.E6.tag K) ∈
          centralizer ({(E6Pilot.e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL TwistTag.E6.tag K)) := by
        have e : (m : ModGL TwistTag.E6.tag K) =
            (q : ModGL TwistTag.E6.tag K)⁻¹ * (g : ModGL TwistTag.E6.tag K) := by
          rw [hgqm']
          group
        rw [e]
        exact mul_mem (inv_mem hqC) hgC
      have hb' : (m : ModGL TwistTag.E6.tag K) ^ 2 ^ b = 1 := by
        have h : ((m ^ 2 ^ b : graphFixedRootGroup TwistTag.E6 K σ) :
            ModGL TwistTag.E6.tag K) = 1 := congrArg Subtype.val hb
        simpa using h
      have hy : (m : ModGL TwistTag.E6.tag K) ∈ E6Pilot.yLeviF4 K :=
        rckTwE6_mem_yLeviF4_of_pow_two hmM hmy hb'
      exact mem_subgroupOf.2 (mem_inf.2 ⟨hy, m.2⟩))

end Core

end CFSG.StandardType.RCKC1
