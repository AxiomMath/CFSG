module

public import CFSG.Quasithin.Recognition.RuTypeJ22b

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type*} [Group G]

namespace RuDataN

variable (N : RuDataN G)

abbrev conjU (l : G) : Subgroup G := (ruU N.L N.T).map (MulAut.conj l).toMonoidHom

theorem mem_conjU {l x : G} : x ∈ N.conjU l ↔ l⁻¹ * x * l ∈ ruU N.L N.T := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [mul_assoc] using hu
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem conj_mem_conjU {l u : G} (hu : u ∈ ruU N.L N.T) : l * u * l⁻¹ ∈ N.conjU l :=
  N.mem_conjU.mpr (by simpa [mul_assoc] using hu)

theorem conjU_one : N.conjU 1 = ruU N.L N.T := by
  ext x
  simp

theorem conjU_mul (l m : G) : N.conjU (l * m) = (N.conjU m).map (MulAut.conj l).toMonoidHom := by
  rw [Subgroup.map_map]
  ext x
  simp [mul_assoc]

theorem card_conjU (l : G) : Nat.card (N.conjU l) = Nat.card (ruU N.L N.T) :=
  Subgroup.card_map_of_injective (MulAut.conj l).injective

variable [Finite G]

omit [Finite G] in
theorem eq_S_of_invariant {W : Subgroup G} (hVW : ruV N.L ≤ W) (hWS : W ≤ ruS N.L)
    (hinv : ∀ l ∈ N.L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) (hne : W ≠ ruV N.L) : W = ruS N.L := by
  let X : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    { carrier := {A | ∃ w : ruS N.L, (w : G) ∈ W ∧ N.χ w = Multiplicative.ofAdd A}
      zero_mem' := ⟨1, W.one_mem, by rw [map_one]; rfl⟩
      add_mem' := by
        rintro A B ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
        exact ⟨w * w', W.mul_mem hw hw', by rw [map_mul]; rfl⟩
      neg_mem' := by
        rintro A ⟨w, hw, hwA⟩
        refine ⟨w⁻¹, W.inv_mem hw, ?_⟩
        rw [map_inv, hwA]
        rfl }
  have hXtr : ∀ A ∈ X, A.trace = 0 := by
    rintro A ⟨w, -, hw⟩
    have := N.χ_trace w
    rw [hw] at this
    exact this
  have hXinv : ∀ g : SL(3, ZMod 2), ∀ A ∈ X, stAct g A ∈ X := by
    rintro g A ⟨w, hw, hwA⟩
    obtain ⟨l, rfl⟩ := N.θ_surj g
    have hmem : (l : G) * w * (l : G)⁻¹ ∈ ruS N.L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 N.L l.2) w).mp w.2
    refine ⟨⟨_, hmem⟩, hinv l l.2 w hw, ?_⟩
    rw [N.χ_equiv l w ⟨_, hmem⟩ rfl, hwA, toAdd_ofAdd]
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hne
    refine le_antisymm (fun w hw => ?_) hVW
    have hwA : Multiplicative.toAdd (N.χ ⟨w, hWS hw⟩) ∈ X :=
      ⟨⟨w, hWS hw⟩, hw, by simp⟩
    rw [hbot, AddSubgroup.mem_bot] at hwA
    have : (⟨w, hWS hw⟩ : ruS N.L) ∈ N.χ.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (by rw [hwA, toAdd_one])
    rw [N.χ_ker, Subgroup.mem_subgroupOf] at this
    exact this
  refine le_antisymm hWS fun s hs => ?_
  obtain ⟨w, hw, hwA⟩ := SL3.st_irreducible X hXtr hXinv hXne (N.χ_trace ⟨s, hs⟩)
  have hk : w⁻¹ * ⟨s, hs⟩ ∈ N.χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwA, ofAdd_toAdd]
    exact inv_mul_cancel _
  rw [N.χ_ker, Subgroup.mem_subgroupOf] at hk
  have : s = w * (((w⁻¹ * ⟨s, hs⟩ : ruS N.L)) : G) := by simp
  rw [this]
  exact W.mul_mem hw (hVW hk)

omit [Finite G] in
theorem U_le_Q : ruU N.L N.T ≤ ruQ N.T := N.two.U_le_Q

theorem U_le_S : ruU N.L N.T ≤ ruS N.L := fun u hu =>
  N.toRuData.mem_S_of_centralizes (N.Q_le_L (N.U_le_Q hu)) fun v hv =>
    Subtype.ext_iff.mp (N.U_elem.1.1.1 ⟨u, hu⟩ ⟨v, N.V_le_U hv⟩)

theorem conjU_le_S {l : G} (hl : l ∈ N.L) : N.conjU l ≤ ruS N.L := by
  rintro _ ⟨u, hu, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 N.L hl) u).mp (N.U_le_S hu)

omit [Finite G] in
theorem V_le_conjU {l : G} (hl : l ∈ N.L) : ruV N.L ≤ N.conjU l := by
  intro v hv
  refine N.mem_conjU.mpr (N.V_le_U ?_)
  have := N.toRuData.conj_mem_V (inv_mem hl) hv
  simpa using this

omit [Finite G] in
theorem card_L_div_LT1 : Nat.card N.L = 7 * Nat.card N.LT1 := by
  rw [N.toRuData.card_L, N.card_LT1]
  norm_num

theorem conjU_eq_U_iff {l : G} (hl : l ∈ N.L) : N.conjU l = ruU N.L N.T ↔ l ∈ N.LT1 := by
  constructor
  · intro h
    let X : Subgroup G := N.L ⊓ Subgroup.normalizer (ruU N.L N.T : Set G)
    have hLT1X : N.LT1 ≤ X := fun m hm =>
      ⟨N.LT1_le_L hm, le_normalizer_conjClosure _ _ (N.LT1_le_H hm)⟩
    have hlX : l ∈ X := by
      refine ⟨hl, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩
      constructor
      · intro hx
        rw [← h]
        exact N.conj_mem_conjU hx
      · intro hx
        rw [← h] at hx
        simpa [mul_assoc] using N.mem_conjU.mp hx
    by_contra hlT
    have hXL : X = N.L := by
      have hdvd : Nat.card N.LT1 ∣ Nat.card X := Subgroup.card_dvd_of_le hLT1X
      have hdvd' : Nat.card X ∣ Nat.card N.L := Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨a, ha⟩ := hdvd
      obtain ⟨b, hb⟩ := hdvd'
      have hpos : 0 < Nat.card N.LT1 := Nat.card_pos
      rw [N.card_L_div_LT1, ha, mul_assoc] at hb
      have h7 : a * b = 7 := by
        have := Nat.eq_of_mul_eq_mul_left hpos (show Nat.card N.LT1 * 7 =
          Nat.card N.LT1 * (a * b) by rw [← hb]; ring)
        exact this.symm
      have ha1 : a ≠ 1 := by
        intro ha1
        rw [ha1, mul_one] at ha
        have : X = N.LT1 := (Subgroup.eq_of_le_of_card_ge hLT1X (le_of_eq ha)).symm
        exact hlT (this ▸ hlX)
      have hb1 : b = 1 := by
        have : a ∣ 7 := ⟨b, h7.symm⟩
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp this with h1 | h1
        · exact absurd h1 ha1
        · rw [h1] at h7; omega
      exact Subgroup.eq_of_le_of_card_ge inf_le_left (by
        rw [N.card_L_div_LT1, ha]
        have : a = 7 := by rw [hb1, mul_one] at h7; exact h7
        rw [this, mul_comm])
    have hUS := N.eq_S_of_invariant N.V_le_U N.U_le_S (fun m hm u hu => by
      have hmX : m ∈ X := hXL ▸ hm
      exact (Subgroup.mem_normalizer_iff.mp hmX.2 u).mp hu) (fun e => by
        have := N.toRuData.card_U
        rw [e, N.toRuData.card_V] at this
        omega)
    have := N.toRuData.card_U
    rw [hUS, N.toRuData.card_S] at this
    omega
  · intro hl1
    ext x
    rw [N.mem_conjU]
    constructor
    · intro hx
      have := N.conj_mem_U (N.LT1_le_H hl1) hx
      simpa [mul_assoc] using this
    · intro hx
      have := N.conj_mem_U (inv_mem (N.LT1_le_H hl1)) hx
      simpa using this

theorem conjU_eq_conjU_iff (l l' : N.L) :
    N.conjU l = N.conjU l' ↔ natAct3 (N.θ l) SL3.e0 = natAct3 (N.θ l') SL3.e0 := by
  have key : N.conjU l = N.conjU l' ↔ N.conjU ((l : G)⁻¹ * l') = ruU N.L N.T := by
    rw [N.conjU_mul]
    constructor
    · intro h
      rw [← h, ← N.conjU_mul, inv_mul_cancel, N.conjU_one]
    · intro h
      have e := congrArg (fun X : Subgroup G => X.map (MulAut.conj (l : G)).toMonoidHom) h
      simp only [Subgroup.map_map] at e
      have e2 : (MulAut.conj (l : G)).toMonoidHom.comp (MulAut.conj (l : G)⁻¹).toMonoidHom =
          MonoidHom.id G := MonoidHom.ext fun x => by simp [mul_assoc]
      simp only [← MonoidHom.comp_assoc, e2, MonoidHom.id_comp] at e
      exact e.symm
  rw [key, N.conjU_eq_U_iff (mul_mem (inv_mem l.2) l'.2), mem_pullL]
  constructor
  · rintro ⟨_, h⟩
    have : N.θ ((l : N.L)⁻¹ * l') ∈ SL3.Stab0 := h
    rw [SL3.mem_Stab0, map_mul, map_inv, SL3.natAct3_mul] at this
    have e := congrArg (natAct3 (N.θ l)) this
    rwa [← SL3.natAct3_mul, mul_inv_cancel, SL3.natAct3_one, eq_comm] at e
  · intro h
    refine ⟨mul_mem (inv_mem l.2) l'.2, ?_⟩
    show N.θ ((l : N.L)⁻¹ * l') ∈ SL3.Stab0
    rw [SL3.mem_Stab0, map_mul, map_inv, SL3.natAct3_mul, ← h, ← SL3.natAct3_mul,
      inv_mul_cancel, SL3.natAct3_one]

theorem conjU_ne_U_iff (l : N.L) :
    N.conjU l ≠ ruU N.L N.T ↔ natAct3 (N.θ l) SL3.e0 ≠ SL3.e0 := by
  have := N.conjU_eq_conjU_iff l 1
  rw [OneMemClass.coe_one, N.conjU_one, map_one, SL3.natAct3_one] at this
  exact not_congr this

theorem exists_conjU_eq {l l' : N.L} (hl : N.conjU l ≠ ruU N.L N.T)
    (hl' : N.conjU l' ≠ ruU N.L N.T) : ∃ m ∈ N.LT1, N.conjU (m * l) = N.conjU l' := by
  have hv := (N.conjU_ne_U_iff l).mp hl
  have hv' := (N.conjU_ne_U_iff l').mp hl'
  have hne0 : ∀ g : SL(3, ZMod 2), natAct3 g SL3.e0 ≠ 0 := fun g h => by
    have := congrArg (natAct3 g⁻¹) h
    rw [← SL3.natAct3_mul, inv_mul_cancel, SL3.natAct3_one] at this
    have h0 : natAct3 g⁻¹ 0 = 0 := by simp [natAct3]
    rw [h0] at this
    exact absurd (congrFun this 0) (by decide)
  obtain ⟨g, hg, hgv⟩ := SL3.Stab0_transitive _ _ (hne0 _) hv (hne0 _) hv'
  obtain ⟨m, rfl⟩ := N.θ_surj g
  refine ⟨m, mem_pullL.mpr ⟨m.2, hg⟩, ?_⟩
  have := (N.conjU_eq_conjU_iff (m * l) l').mpr (by rw [map_mul, SL3.natAct3_mul, hgv])
  simpa using this

theorem exists_conjU_not_le_Q : ∃ l ∈ N.L, ¬ N.conjU l ≤ ruQ N.T := by
  by_contra hall
  push Not at hall
  let W : Subgroup G := Subgroup.closure (⋃ l ∈ N.L, (N.conjU l : Set G))
  have hWS : W ≤ ruS N.L := (Subgroup.closure_le _).mpr (Set.iUnion₂_subset fun l hl =>
    N.conjU_le_S hl)
  have hUW : ruU N.L N.T ≤ W := by
    rw [← N.conjU_one]
    exact fun x hx => Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨1, N.L.one_mem, hx⟩)
  have hWinv : ∀ m ∈ N.L, ∀ w ∈ W, m * w * m⁻¹ ∈ W := by
    intro m hm w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, hx⟩ := Set.mem_iUnion₂.mp hx
      refine Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨m * l, mul_mem hm hl, ?_⟩)
      rw [N.conjU_mul]
      exact ⟨x, hx, rfl⟩
    | one => simp
    | mul x y _ _ hx hy => simpa [mul_assoc] using W.mul_mem hx hy
    | inv x _ hx => simpa [mul_assoc] using W.inv_mem hx
  have hWQ : W ≤ ruQ N.T := (Subgroup.closure_le _).mpr (Set.iUnion₂_subset fun l hl =>
    hall l hl)
  have hWeq := N.eq_S_of_invariant (N.V_le_U.trans hUW) hWS hWinv (fun e => by
    have h1 := Subgroup.card_le_of_le hUW
    rw [e, N.toRuData.card_V, N.toRuData.card_U] at h1
    omega)
  apply N.S_ne_Q
  refine Subgroup.eq_of_le_of_card_ge (hWeq ▸ hWQ) ?_
  rw [N.toRuData.card_S, N.toRuData.card_Q]

theorem conjU_not_le_Q {l : G} (hl : l ∈ N.L) (hne : N.conjU l ≠ ruU N.L N.T) :
    ¬ N.conjU l ≤ ruQ N.T := by
  obtain ⟨l₀, hl₀, hQ⟩ := N.exists_conjU_not_le_Q
  have hne₀ : N.conjU l₀ ≠ ruU N.L N.T := fun e => hQ (e ▸ N.U_le_Q)
  obtain ⟨m, hm, hml⟩ := N.exists_conjU_eq (l := ⟨l₀, hl₀⟩) (l' := ⟨l, hl⟩) hne₀ hne
  simp only at hml
  intro hle
  apply hQ
  rw [← hml, N.conjU_mul] at hle
  rintro x hx
  have := hle ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hm' := N.LT1_le_H hm
  have := N.conj_mem_Q (inv_mem hm') this
  simpa [mul_assoc] using this

theorem conj_mem_conjU_of_comm {l c x : G} (hc : c * (l * N.z * l⁻¹) = (l * N.z * l⁻¹) * c)
    (hx : x ∈ N.conjU l) : c * x * c⁻¹ ∈ N.conjU l := by
  rw [N.mem_conjU] at hx ⊢
  have hcH : l⁻¹ * c * l ∈ ruH N.T := N.mem_H_iff_comm.mpr (by
    calc N.z * (l⁻¹ * c * l) = l⁻¹ * ((l * N.z * l⁻¹) * c) * l := by group
      _ = l⁻¹ * (c * (l * N.z * l⁻¹)) * l := by rw [hc]
      _ = l⁻¹ * c * l * N.z := by group)
  have := N.conj_mem_U hcH hx
  have e : l⁻¹ * (c * x * c⁻¹) * l = (l⁻¹ * c * l) * (l⁻¹ * x * l) * (l⁻¹ * c * l)⁻¹ := by group
  rw [e]
  exact this

theorem z_conj_not_mem_Z {l : G} (hl : l ∈ N.L) (hne : N.conjU l ≠ ruU N.L N.T) :
    l * N.z * l⁻¹ ∉ ruZ N.T := by
  intro h
  apply hne
  rw [N.conjU_eq_U_iff hl, ← N.L_inf_H]
  refine ⟨hl, N.mem_H_iff_comm.mpr ?_⟩
  rcases N.mem_Z_iff.mp h with e | e
  · exact absurd (show N.z = 1 by
      have := congrArg (fun y => l⁻¹ * y * l) e
      simpa [mul_assoc] using this) N.z_ne_one
  · calc N.z * l = l * N.z * l⁻¹ * l := by rw [e]
      _ = l * N.z := by group

theorem conjU_inf_Q_not_le_HC {l : G} (hl : l ∈ N.L) (hne : N.conjU l ≠ ruU N.L N.T) :
    ¬ N.conjU l ⊓ ruQ N.T ≤ N.HC := by
  intro hle
  apply N.conjU_not_le_Q hl hne
  intro u hu
  have huH : u ∈ ruH N.T := (N.toRuData.S_le_T.trans N.toRuData.T_le_H) (N.conjU_le_S hl hu)
  have hzU : l * N.z * l⁻¹ ∈ ruU N.L N.T :=
    N.V_le_U (N.toRuData.conj_mem_V hl N.z_mem_V)
  set x := Multiplicative.toAdd (N.ψU ⟨_, hzU⟩) with hx
  have hx0 : x ≠ 0 := by
    intro h0
    apply N.z_conj_not_mem_Z hl hne
    rw [← N.ψU_eq_one_iff ⟨_, hzU⟩]
    exact Multiplicative.toAdd.injective (by rw [← hx, h0, toAdd_one])
  have h1 : N.φ ⟨u, huH⟩ = 1 := by
    refine Sigma.eq_one_of_fix_perp hx0 fun w hw => ?_
    obtain ⟨c, hc⟩ := N.ψQ_surjective (Multiplicative.ofAdd w)
    have hcz : (c : G) * (l * N.z * l⁻¹) = (l * N.z * l⁻¹) * c := by
      have := (N.comm_eq_one_iff c ⟨_, hzU⟩).mpr (by rw [hc, toAdd_ofAdd]; exact hw)
      calc (c : G) * (l * N.z * l⁻¹) =
            (c * (l * N.z * l⁻¹) * (c : G)⁻¹ * (l * N.z * l⁻¹)⁻¹) * (l * N.z * l⁻¹) * c := by
            group
        _ = (l * N.z * l⁻¹) * c := by rw [show (c : G) * (l * N.z * l⁻¹) * (c : G)⁻¹ *
              (l * N.z * l⁻¹)⁻¹ = 1 from this, one_mul]
    have hmemQ : u * c * u⁻¹ ∈ ruQ N.T := N.conj_mem_Q huH c.2
    have hmemX : u * c * u⁻¹ * (c : G)⁻¹ ∈ N.conjU l := by
      have h2 := N.conj_mem_conjU_of_comm hcz (inv_mem hu)
      have := mul_mem hu h2
      simpa [mul_assoc] using this
    have hmemC : u * c * u⁻¹ * (c : G)⁻¹ ∈ N.HC :=
      hle (Subgroup.mem_inf.mpr ⟨hmemX, mul_mem hmemQ (inv_mem c.2)⟩)
    have e1 : N.ψQ ⟨u * c * u⁻¹, hmemQ⟩ = N.ψQ c := by
      have : (⟨u * c * u⁻¹, hmemQ⟩ : ruQ N.T) * c⁻¹ ∈ N.ψQ.ker := by
        rw [N.ψQ_ker, Subgroup.mem_subgroupOf]
        exact hmemC
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this
      exact this
    have e2 := N.ψQ_conj ⟨u, huH⟩ c
    simp only at e2
    rw [e1, hc, toAdd_ofAdd] at e2
    exact e2.symm
  have : (⟨u, huH⟩ : ruH N.T) ∈ N.φ.ker := h1
  rw [N.φ_ker, Subgroup.mem_subgroupOf] at this
  exact this

theorem card_conjU_inf_Q {l : G} (hl : l ∈ N.L) (hne : N.conjU l ≠ ruU N.L N.T) :
    Nat.card ↥(N.conjU l ⊓ ruQ N.T) = 16 := by
  have hX : Nat.card (N.conjU l) = 32 := by rw [N.card_conjU, N.toRuData.card_U]
  obtain ⟨k, hk5, hk⟩ := exists_card_eq_two_pow (inf_le_left : N.conjU l ⊓ ruQ N.T ≤ N.conjU l)
    (show Nat.card (N.conjU l) = 2 ^ 5 by rw [hX]; norm_num)
  have hV : ruV N.L ≤ N.conjU l ⊓ ruQ N.T := le_inf (N.V_le_conjU hl) (N.V_le_U.trans N.U_le_Q)
  have hk3 : 3 ≤ k := by
    have := Subgroup.card_le_of_le hV
    rw [N.toRuData.card_V, hk] at this
    by_contra h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk4 : k ≠ 3 := by
    rintro rfl
    apply N.conjU_inf_Q_not_le_HC hl hne
    have heq : ruV N.L = N.conjU l ⊓ ruQ N.T :=
      Subgroup.eq_of_le_of_card_ge hV (by rw [hk, N.toRuData.card_V]; norm_num)
    rw [← heq]
    exact N.V_le_U.trans N.U_le_HC
  have hk5' : k ≠ 5 := by
    rintro rfl
    apply N.conjU_not_le_Q hl hne
    have heq : N.conjU l ⊓ ruQ N.T = N.conjU l :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hX]; norm_num)
    rw [← heq]
    exact inf_le_right
  have : k = 4 := by omega
  rw [hk, this]
  norm_num

theorem conjU_inf_HC {l : G} (hl : l ∈ N.L) (hne : N.conjU l ≠ ruU N.L N.T) :
    N.conjU l ⊓ N.HC = ruV N.L := by
  have hV : ruV N.L ≤ N.conjU l ⊓ N.HC := le_inf (N.V_le_conjU hl) (N.V_le_U.trans N.U_le_HC)
  have hle : N.conjU l ⊓ N.HC ≤ N.conjU l ⊓ ruQ N.T := inf_le_inf_left _ N.HC_le_Q
  have hne' : N.conjU l ⊓ N.HC ≠ N.conjU l ⊓ ruQ N.T := fun e =>
    N.conjU_inf_Q_not_le_HC hl hne (e ▸ inf_le_right)
  obtain ⟨k, hk4, hk⟩ := exists_card_eq_two_pow hle
    (show Nat.card ↥(N.conjU l ⊓ ruQ N.T) = 2 ^ 4 by rw [N.card_conjU_inf_Q hl hne]; norm_num)
  have hk' : k ≤ 3 := by
    by_contra h
    apply hne'
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [hk, N.card_conjU_inf_Q hl hne, show k = 4 by omega]; norm_num)
  refine (Subgroup.eq_of_le_of_card_ge hV ?_).symm
  rw [hk, N.toRuData.card_V]
  calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk'
    _ = 8 := by norm_num

end RuDataN

end CFSG.Quasithin.RuType
