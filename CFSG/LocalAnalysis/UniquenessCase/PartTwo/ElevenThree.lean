module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace ElevenThree

theorem conj_mem_cTilde {M V₀ V : Subgroup G} (hMV : M ≤ normalizer (V : Set G))
    (hMV₀ : M ≤ normalizer (V₀ : Set G)) {c m : G} (hc : c ∈ F11.CTilde M V₀ V) (hm : m ∈ M) :
    m⁻¹ * c * m ∈ F11.CTilde M V₀ V := by
  unfold F11.CTilde at hc ⊢
  rw [Subgroup.mem_iInf] at hc ⊢
  intro w
  rw [Subgroup.mem_iInf]
  intro hw
  have hmw : m * w * m⁻¹ ∈ V := (mem_normalizer_iff.1 (hMV hm) w).1 hw
  have hcw := (Subgroup.mem_iInf.1 (hc (m * w * m⁻¹))) hmw
  obtain ⟨hcM, hcN, hcom⟩ := hcw
  refine ⟨M.mul_mem (M.mul_mem (M.inv_mem hm) hcM) hm, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMV₀ hm)) hcN) (hMV₀ hm)
  · have h1 : m⁻¹ * c * m * w * (m⁻¹ * c * m)⁻¹ * w⁻¹ =
        m⁻¹ * (c * (m * w * m⁻¹) * c⁻¹ * (m * w * m⁻¹)⁻¹) * m := by group
    rw [h1]
    exact (mem_normalizer_iff''.1 (hMV₀ hm) _).1 hcom

theorem cTilde_not_le_centralizer {M V₀ V : Subgroup G} (h : InCalV0 M V₀ V) :
    ¬ F11.CTilde M V₀ V ≤ centralizer (V : Set G) := by
  intro hle
  obtain ⟨⟨_, _, hMV₀, _⟩, ⟨_, hVM, hMV, hV⟩, hV₀V, hTI₀, hTI, hclos, hnr⟩ := h
  have hne : V₀ ≠ V := fun h' => hTI (h' ▸ hTI₀)
  obtain ⟨v, hvV, hv0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hV₀V hne)
  have hnr' : ∃ K : Subgroup G, K ≤ M ∧ M ≤ normalizer (K : Set G) ∧
      M ⊓ centralizer (V : Set G) ≤ K ∧
      (∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n) ∧
      ¬ K ≤ centralizer (V : Set G) := by
    by_contra hcon
    exact hnr fun K hKM hMK hCK hn => by_contra fun hK => hcon ⟨K, hKM, hMK, hCK, hn, hK⟩
  obtain ⟨K, hKM, hMK, hCK, ⟨n, hn⟩, hKnot⟩ := hnr'
  have hKs : K ≤ stabTil V₀ V := fun k hk => ⟨hMV (hKM hk), hMV₀ (hKM hk)⟩
  let f : ↥K →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hKs)
  have hfker : (centralizer (V : Set G)).subgroupOf K ≤ f.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    show actTil V₀ V hV (Subgroup.inclusion hKs k) = 1
    rw [actTil_eq_one_iff]
    intro w hw
    have hkc : (k : G) ∈ centralizer (V : Set G) := hk
    have hcomm : w * (k : G) = (k : G) * w := Subgroup.mem_centralizer_iff.1 hkc w hw
    have hk' : ((Subgroup.inclusion hKs k : ↥(stabTil V₀ V)) : G) = (k : G) := rfl
    rw [hk', ← hcomm]
    simp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : f.ker.index ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_of_le hfker
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hp2 : IsPGroup 2 ↥f.range :=
    IsPGroup.of_card ((Subgroup.index_ker f).symm.trans hm)
  let y0 : IntMod V hV := IntMod.mk hV ⟨v, hvV⟩
  have hy0 : mkTil V₀ V hV y0 ≠ 1 := fun h1 =>
    hv0 ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).1 h1)
  have hy0sq : mkTil V₀ V hV y0 ^ 2 = 1 := by
    rw [← map_pow]
    have : y0 ^ 2 = 1 := by
      refine IntMod.val_injective ?_
      rw [pow_two, IntMod.val_mul, IntMod.val_one]
      show v * v = 1
      rw [← pow_two]
      exact hV.2 v hvV
    rw [this, map_one]
  have h2dvd : 2 ∣ Nat.card (Vtil V₀ V hV) := by
    have h1 : orderOf (mkTil V₀ V hV y0) = 2 :=
      orderOf_eq_prime hy0sq hy0
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hfix1 : (1 : Vtil V₀ V hV) ∈ MulAction.fixedPoints ↥f.range (Vtil V₀ V hV) := by
    rw [MulAction.mem_fixedPoints]
    intro φ
    exact map_one (φ : MulAut (Vtil V₀ V hV))
  obtain ⟨b, hb, hb1⟩ := hp2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Vtil V₀ V hV) h2dvd hfix1
  obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV b
  have hy0' : y.val ∉ V₀ := fun h1 =>
    hb1 ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) y).2 h1).symm
  have hyfix : ∀ k ∈ K, k * y.val * k⁻¹ * (y.val)⁻¹ ∈ V₀ := by
    intro k hk
    have h2 : f ⟨k, hk⟩ (mkTil V₀ V hV y) = mkTil V₀ V hV y :=
      (MulAction.mem_fixedPoints.1 hb) ⟨f ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩
    have h3 : actTil V₀ V hV ⟨k, hKs hk⟩ (mkTil V₀ V hV y) = mkTil V₀ V hV y := h2
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h3
    exact h3
  let Y : Subgroup G :=
    { carrier := {w | w ∈ V ∧ ∀ k ∈ K, k * w * k⁻¹ * w⁻¹ ∈ V₀}
      one_mem' := ⟨V.one_mem, fun k _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haV, ha⟩ ⟨hbV, hb'⟩
        refine ⟨V.mul_mem haV hbV, fun k hk => ?_⟩
        have h1 : k * (a * b) * k⁻¹ * (a * b)⁻¹ =
            (k * a * k⁻¹ * a⁻¹) * (a * (k * b * k⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [h1]
        exact V₀.mul_mem (ha k hk) ((mem_normalizer_iff.1 (hMV₀ (hVM haV)) _).1 (hb' k hk))
      inv_mem' := by
        rintro a ⟨haV, ha⟩
        refine ⟨V.inv_mem haV, fun k hk => ?_⟩
        have h1 : k * a⁻¹ * k⁻¹ * a⁻¹⁻¹ = a⁻¹ * (k * a * k⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [h1]
        exact (mem_normalizer_iff''.1 (hMV₀ (hVM haV)) _).1 (V₀.inv_mem (ha k hk)) }
  have hYinv : ∀ m ∈ M, ∀ w ∈ Y, m * w * m⁻¹ ∈ Y := by
    rintro m hm w ⟨hwV, hw⟩
    refine ⟨(mem_normalizer_iff.1 (hMV hm) w).1 hwV, fun k hk => ?_⟩
    have hk' : m⁻¹ * k * m ∈ K := by
      have := (mem_normalizer_iff.1 (hMK (M.inv_mem hm)) k).1 hk
      simpa using this
    have h1 : k * (m * w * m⁻¹) * k⁻¹ * (m * w * m⁻¹)⁻¹ =
        m * ((m⁻¹ * k * m) * w * (m⁻¹ * k * m)⁻¹ * w⁻¹) * m⁻¹ := by group
    rw [h1]
    exact (mem_normalizer_iff.1 (hMV₀ hm) _).1 (hw _ hk')
  have hVY : V ≤ Y := by
    have hy : y.val ∈ Y := ⟨y.val_mem, hyfix⟩
    calc V = Subgroup.closure {x : G | ∃ m ∈ M, x = m * y.val * m⁻¹} :=
          (hclos y.val y.val_mem hy0').symm
      _ ≤ Y := by
        refine (Subgroup.closure_le Y).2 ?_
        rintro _ ⟨m, hm, rfl⟩
        exact hYinv m hm _ hy
  have hKC : K ≤ F11.CTilde M V₀ V := by
    intro k hk
    unfold F11.CTilde
    rw [Subgroup.mem_iInf]
    intro w
    rw [Subgroup.mem_iInf]
    intro hw
    exact ⟨hKM hk, hMV₀ (hKM hk), (hVY hw).2 k hk⟩
  exact hKnot (hKC.trans hle)

private abbrev conjAction (C : Subgroup G) : MulAction ↥C G where
  smul := fun c g => (c : G) * g * (c : G)⁻¹
  one_smul := fun g => by
    show ((1 : ↥C) : G) * g * ((1 : ↥C) : G)⁻¹ = g
    simp
  mul_smul := fun a b g => by
    show ((a * b : ↥C) : G) * g * ((a * b : ↥C) : G)⁻¹ =
      (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹
    simp [mul_assoc]

theorem relIndex_cElt_eq_pow_two {M V₀ V : Subgroup G} (h : InCalV0 M V₀ V)
    (h4 : Nat.card V₀ ≤ 4) {v : G} (hv : v ∈ V) (hv0 : v ∉ V₀) :
    ∃ n ≤ 2, (M ⊓ centralizer ({v} : Set G)).relIndex (F11.CElt M V₀ v) = 2 ^ n := by
  classical
  have hcA := cTilde_not_le_centralizer h
  obtain ⟨⟨_, hV₀M, hMV₀, hV₀E⟩, ⟨_, hVM, hMV, _⟩, hV₀V, _, _, hclos, _⟩ := h
  letI : MulAction ↥(F11.CElt M V₀ v) G := conjAction _
  have hstab : MulAction.stabilizer ↥(F11.CElt M V₀ v) v =
      (M ⊓ centralizer ({v} : Set G)).subgroupOf (F11.CElt M V₀ v) := by
    ext c
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    have hcM : (c : G) ∈ M := c.2.1
    constructor
    · intro hc
      refine ⟨hcM, ?_⟩
      have h1 : (c : G) * v * (c : G)⁻¹ = v := hc
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1
    · rintro ⟨-, hc⟩
      show (c : G) * v * (c : G)⁻¹ = v
      rw [mul_inv_eq_iff_eq_mul]
      exact hc
  have hidx : (M ⊓ centralizer ({v} : Set G)).relIndex (F11.CElt M V₀ v) =
      (MulAction.orbit ↥(F11.CElt M V₀ v) v).ncard := by
    rw [Subgroup.relIndex, ← hstab]
    exact MulAction.index_stabilizer ↥(F11.CElt M V₀ v) v
  have horb : ∀ y, y ∈ MulAction.orbit ↥(F11.CElt M V₀ v) v ↔
      ∃ c ∈ F11.CElt M V₀ v, y = c * v * c⁻¹ := by
    intro y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have hOinv : ∀ c ∈ F11.CElt M V₀ v, ∀ y ∈ MulAction.orbit ↥(F11.CElt M V₀ v) v,
      c * y * c⁻¹ ∈ MulAction.orbit ↥(F11.CElt M V₀ v) v := by
    intro c hc y hy
    obtain ⟨c', hc', rfl⟩ := (horb y).1 hy
    exact (horb _).2 ⟨c * c', Subgroup.mul_mem _ hc hc', by group⟩
  have hOinv' : ∀ c ∈ F11.CElt M V₀ v, ∀ y, c * y * c⁻¹ ∈
      MulAction.orbit ↥(F11.CElt M V₀ v) v → y ∈ MulAction.orbit ↥(F11.CElt M V₀ v) v := by
    intro c hc y hy
    have := hOinv c⁻¹ (Subgroup.inv_mem _ hc) _ hy
    have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
    rwa [e] at this
  let S : Set G := (fun a => a * v) '' (V₀ : Set G)
  have hOS : MulAction.orbit ↥(F11.CElt M V₀ v) v ⊆ S := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := (horb y).1 hy
    obtain ⟨-, -, hcom⟩ := hc
    exact ⟨c * v * c⁻¹ * v⁻¹, hcom, by simp⟩
  have hSinv : ∀ c ∈ F11.CElt M V₀ v, ∀ y ∈ S, c * y * c⁻¹ ∈ S := by
    rintro c hc _ ⟨a, ha, rfl⟩
    obtain ⟨-, hcN, hcom⟩ := hc
    refine ⟨(c * a * c⁻¹) * (c * v * c⁻¹ * v⁻¹),
      V₀.mul_mem ((mem_normalizer_iff.1 hcN a).1 ha) hcom, ?_⟩
    show c * a * c⁻¹ * (c * v * c⁻¹ * v⁻¹) * v = c * (a * v) * c⁻¹
    group
  have hSfin : S.Finite := Set.toFinite S
  have hScard : S.ncard = Nat.card V₀ := by
    rw [Set.ncard_image_of_injective _ (mul_left_injective v)]
    exact (Nat.card_coe_set_eq (V₀ : Set G)).symm
  have hOle : (MulAction.orbit ↥(F11.CElt M V₀ v) v).ncard ≤ 4 :=
    (Set.ncard_le_ncard hOS hSfin).trans (by rw [hScard]; exact h4)
  have hOpos : 0 < (MulAction.orbit ↥(F11.CElt M V₀ v) v).ncard := by
    rw [Set.ncard_pos (Set.toFinite _)]
    exact ⟨v, MulAction.mem_orbit_self v⟩
  have hO3 : (MulAction.orbit ↥(F11.CElt M V₀ v) v).ncard ≠ 3 := by
    intro h3
    have hV₀2 : IsPGroup 2 V₀ := fun g => ⟨1, Subtype.ext (by simpa using hV₀E.2 (g : G) g.2)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hV₀2
    have h3le : 3 ≤ Nat.card V₀ := by
      rw [← hScard, ← h3]
      exact Set.ncard_le_ncard hOS hSfin
    have hV4 : Nat.card V₀ = 4 := by
      have hk2 : k ≤ 2 := by
        by_contra hcon
        push Not at hcon
        have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hcon
        omega
      interval_cases k <;> omega
    have hdiff : (S \ MulAction.orbit ↥(F11.CElt M V₀ v) v).ncard = 1 := by
      rw [Set.ncard_sdiff' hOS hSfin, hScard, hV4, h3]
    obtain ⟨u, hu⟩ := Set.ncard_eq_one.1 hdiff
    have huu : u ∈ S \ MulAction.orbit ↥(F11.CElt M V₀ v) v := by
      rw [hu]
      exact Set.mem_singleton u
    obtain ⟨huS, huO⟩ := huu
    have hfix : ∀ c ∈ F11.CElt M V₀ v, c * u * c⁻¹ = u := by
      intro c hc
      have h1 : c * u * c⁻¹ ∈ S \ MulAction.orbit ↥(F11.CElt M V₀ v) v :=
        ⟨hSinv c hc u huS, fun hO => huO (hOinv' c hc u hO)⟩
      rw [hu] at h1
      exact h1
    obtain ⟨a, ha, hau⟩ := huS
    have huV : u ∈ V := by
      rw [← hau]
      exact V.mul_mem (hV₀V ha) hv
    have hu0 : u ∉ V₀ := by
      intro hu0
      rw [← hau] at hu0
      exact hv0 (by simpa using V₀.mul_mem (V₀.inv_mem ha) hu0)
    have hcl := hclos u huV hu0
    have hCC : F11.CTilde M V₀ V ≤ F11.CElt M V₀ v := fun c hc =>
      (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hc v)) hv
    have hcentr : F11.CTilde M V₀ V ≤ centralizer (V : Set G) := by
      intro c hc
      have hcz : V ≤ centralizer ({c} : Set G) := by
        rw [← hcl]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨m, hm, rfl⟩
        have hmc := hCC (ElevenThree.conj_mem_cTilde hMV hMV₀ hc hm)
        have h1 := hfix _ hmc
        rw [mul_inv_eq_iff_eq_mul] at h1
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        calc m * u * m⁻¹ * c = m * (u * (m⁻¹ * c * m)) * m⁻¹ := by group
          _ = m * ((m⁻¹ * c * m) * u) * m⁻¹ := by rw [h1]
          _ = c * (m * u * m⁻¹) := by group
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.1 (hcz hw)
    exact hcA hcentr
  rw [hidx]
  obtain h | h | h : (MulAction.orbit ↥(F11.CElt M V₀ v) v).ncard = 1 ∨
      (MulAction.orbit ↥(F11.CElt M V₀ v) v).ncard = 2 ∨
      (MulAction.orbit ↥(F11.CElt M V₀ v) v).ncard = 4 := by omega
  · exact ⟨0, by norm_num, by simpa using h⟩
  · exact ⟨1, by norm_num, by simpa using h⟩
  · exact ⟨2, by norm_num, by simpa using h⟩

theorem relIndex_cElt_bot (M : Subgroup G) (v : G) :
    (M ⊓ centralizer ({v} : Set G)).relIndex (F11.CElt M ⊥ v) = 1 := by
  rw [Subgroup.relIndex_eq_one]
  rintro c ⟨hcM, -, hc⟩
  refine Subgroup.mem_inf.2 ⟨hcM, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : c * v * c⁻¹ = v := mul_inv_eq_one.1 (Subgroup.mem_bot.1 hc)
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1

end ElevenThree

theorem r113_holds (D : Data G) :
    ∀ V₀ V : Subgroup G, F11.Hyp11 D V₀ V → Nat.card V₀ ≤ 4 → ∀ v ∈ V, v ∉ V₀ →
      ∃ n ≤ 2, (D.M ⊓ centralizer ({v} : Set G)).relIndex (F11.CElt D.M V₀ v) = 2 ^ n := by
  intro V₀ V hH h4 v hv hv0
  rcases hH.1 with h | ⟨rfl, -⟩
  · exact ElevenThree.relIndex_cElt_eq_pow_two h h4 hv hv0
  · exact ⟨0, by norm_num, by simpa using ElevenThree.relIndex_cElt_bot D.M v⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
