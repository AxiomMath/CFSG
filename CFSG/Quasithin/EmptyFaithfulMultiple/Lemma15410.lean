module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15410Section
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15410Internal
import CFSG.Quasithin.Vol2.Ch3Basic
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Steps

variable {G : Type*} [Group G] [Finite G]

theorem exists_ne_one_mem_centralizer_of_two_dvd {S V : Subgroup G} (hS : IsPGroup 2 S)
    (hSV : S ≤ Subgroup.normalizer (V : Set G)) (hV : 2 ∣ Nat.card V) :
    ∃ v ∈ V, v ≠ 1 ∧ v ∈ Subgroup.centralizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S V :=
    { smul := fun s v => ⟨(s : G) * v * (s : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hSV s.2) v).mp v.2⟩
      one_smul := fun v => Subtype.ext (by
        change ((1 : S) : G) * v * ((1 : S) : G)⁻¹ = v
        simp)
      mul_smul := fun a b v => Subtype.ext (by
        change ((a * b : S) : G) * v * ((a * b : S) : G)⁻¹ =
          (a : G) * ((b : G) * v * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]) }
  have h1 : (1 : V) ∈ MulAction.fixedPoints S V := fun s => Subtype.ext (by
    change (s : G) * 1 * (s : G)⁻¹ = 1
    simp)
  obtain ⟨v, hv, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hV h1
  refine ⟨v, v.2, fun h => hne (Subtype.ext h.symm), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h : (s : G) * v * s⁻¹ = v := congrArg Subtype.val (hv ⟨s, hs⟩)
  exact mul_inv_eq_iff_eq_mul.mp h

theorem mem_normalizer_centralizer {W : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) := by
  refine A4.mem_normalizer_of_conj_mem fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro w hw
  have hw' : g⁻¹ * w * g ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp hw
    simpa using this
  have h1 := hc _ hw'
  calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * w := by group

theorem not_le_pCoreOf_of_not_le_centralizer {T M X : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTM : T ≤ M) (hTodd : ¬ 2 ∣ T.relIndex M)
    (hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M) (hXM : X ≤ M)
    (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hXZ : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hX3 : Odd ((pCoreOf 2 X).relIndex X))
    (hXV : ¬ X ≤ Subgroup.centralizer (VZ T M : Set G)) :
    ¬ pCoreOf 2 X ≤ pCoreOf 2 M := by
  intro hQM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZ
  set V := VZ T M with hVdef
  obtain ⟨hVc, hVel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hTM hT2 hTodd hF (le_refl Z)
  have hVM : V ≤ pCoreOf 2 M := hVc.trans inf_le_left
  have hRT : pCoreOf 2 M ≤ T := pCoreOf_two_le_of_sylowIn hTM hT2 hTodd
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hXM.trans (le_normalizer_conjClosure Z M)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans (le_normalizer_conjClosure Z M)
  let _ : CommGroup V := commGroupOfElemAbelian hVel
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hVel.2 v v.2)
  have hcV : ∀ (g : Subgroup.normalizer (V : Set G)) (v : V),
      ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ := fun g v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v
  set P := autOn X V with hP
  have hmemP : ∀ φ, φ ∈ P ↔ ∃ g : Subgroup.normalizer (V : Set G), (g : G) ∈ X ∧
      conjAct V g = φ := by
    intro φ
    rw [hP, autOn, Subgroup.mem_map]
    rfl
  have hPodd : Odd (Nat.card P) := by
    rw [hP, card_autOn_eq_relIndex hXN]
    have hle : pCoreOf 2 X ≤ X ⊓ Subgroup.centralizer (V : Set G) := by
      refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X) fun q hq => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp (hVc hv).2 q (hQM hq)).symm
    exact hX3.of_dvd_nat (Subgroup.relIndex_dvd_of_le_left X hle)
  have hdec := (coprime_decomp hPodd hV2 (W := ⊤) fun _ _ _ _ => Subgroup.mem_top _).2
  rw [← commV_eq_commSub, top_inf_eq] at hdec
  have hcne : commV P ≠ ⊥ := by
    intro hbot
    apply hXV
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hφ : conjAct V ⟨g, hXN hg⟩ ∈ P := (hmemP _).mpr ⟨_, hg, rfl⟩
    have h1 : conjAct V ⟨g, hXN hg⟩ ⟨v, hv⟩ * (⟨v, hv⟩ : V)⁻¹ ∈ commV P :=
      Subgroup.subset_closure ⟨_, hφ, _, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
    have h2 := congrArg Subtype.val h1
    rw [hcV] at h2
    calc v * g = (g * v * g⁻¹) * g := by rw [h2]
      _ = g * v := by group
  set U : Subgroup G := (commV P).map V.subtype with hU
  have hTU : T ≤ Subgroup.normalizer (U : Set G) := by
    intro t ht
    refine A4.mem_normalizer_of_conj_mem fun u hu => ?_
    obtain ⟨c, hc, rfl⟩ := hu
    have hτ : ∀ φ ∈ P, conjAct V ⟨t, hTN ht⟩ * φ * (conjAct V ⟨t, hTN ht⟩)⁻¹ ∈ P := by
      intro φ hφ
      obtain ⟨g, hg, rfl⟩ := (hmemP φ).mp hφ
      refine (hmemP _).mpr ⟨⟨t, hTN ht⟩ * g * ⟨t, hTN ht⟩⁻¹, ?_, by
        rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp (hTX ht) g).mp hg
    refine ⟨conjAct V ⟨t, hTN ht⟩ c, apply_mem_commV hτ hc, ?_⟩
    rw [Subgroup.subtype_apply, hcV]
    rfl
  have hU2 : 2 ∣ Nat.card U := by
    rw [hU, Subgroup.card_map_of_injective V.subtype_injective]
    have hp : IsPGroup 2 (commV P) := (isPGroup_two_of_sq_eq_one hV2).to_subgroup _
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hcne (Subgroup.card_eq_one.mp hk)
    exact dvd_pow_self 2 hk0
  obtain ⟨v, hvU, hv1, hvT⟩ := exists_ne_one_mem_centralizer_of_two_dvd hT2 hTU hU2
  obtain ⟨c, hc, rfl⟩ := hvU
  have hcT : (c : G) ∈ T := hRT (hVM c.2)
  have hcZ : (c : G) ∈ Z := Subgroup.subset_closure ⟨⟨hcT, hvT⟩, hVel.2 _ c.2⟩
  have hcfix : c ∈ fixV P := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (hmemP φ).mp hφ
    apply Subtype.ext
    rw [hcV]
    have h1 := Subgroup.mem_centralizer_iff.mp (hXZ hg) _ hcZ
    calc (g : G) * c * (g : G)⁻¹ = c * g * (g : G)⁻¹ := by rw [h1]
      _ = c := by group
  have hmem : c ∈ commV P ⊓ fixV P := ⟨hc, hcfix⟩
  rw [hdec, Subgroup.mem_bot] at hmem
  exact hv1 (by rw [hmem]; rfl)

theorem exists_card_sup_dvd {Y X T : Subgroup G} (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hXTY : X ⊔ T ≤ Subgroup.normalizer (Y : Set G)) (hT2 : IsPGroup 2 T)
    (hY9 : (pCoreOf 2 Y).relIndex Y = 9) (hX3 : (pCoreOf 2 X).relIndex X = 3) :
    ∃ n : ℕ, Nat.card ↥(Y ⊔ (X ⊔ T)) ∣ 27 * 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).exists_card_eq
  obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).exists_card_eq
  obtain ⟨c, hc⟩ := hT2.exists_card_eq
  have hY : Nat.card Y = 9 * 2 ^ a := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 Y) Y
    rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 Y), hY9, ha] at h1
    exact h1.symm
  have hX : Nat.card X = 3 * 2 ^ b := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 X) X
    rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X), hX3, hb] at h1
    exact h1.symm
  have hXT : Nat.card ↥(X ⊔ T) ∣ 3 * 2 ^ b * 2 ^ c := by
    rw [sup_comm, card_sup_eq_of_le_normalizer hTX, hX, ← hc]
    exact Nat.mul_dvd_mul_left _ (Subgroup.relIndex_dvd_card X T)
  refine ⟨a + b + c, ?_⟩
  rw [sup_comm, card_sup_eq_of_le_normalizer hXTY, hY]
  calc 9 * 2 ^ a * Y.relIndex (X ⊔ T) ∣ 9 * 2 ^ a * (3 * 2 ^ b * 2 ^ c) :=
        Nat.mul_dvd_mul_left _ ((Subgroup.relIndex_dvd_card Y (X ⊔ T)).trans hXT)
    _ = 27 * 2 ^ (a + b + c) := by ring

omit [Finite G] in
theorem conj_mem_sectionCentralizer {Y K : Subgroup G} {g c : G}
    (hgY : g ∈ Subgroup.normalizer (Y : Set G)) (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (hc : c ∈ sectionCentralizer Y K) : g * c * g⁻¹ ∈ sectionCentralizer Y K := by
  obtain ⟨hcY, hcK, hcc⟩ := hc
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgY hcY) (Subgroup.inv_mem _ hgY),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgK hcK) (Subgroup.inv_mem _ hgK), fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgY) y).mp hy
    simpa using this
  have h1 := (Subgroup.mem_normalizer_iff.mp hgK _).mp (hcc _ hy')
  convert h1 using 1
  group

omit [Finite G] in
theorem not_isXiMinus_of_five {T Y : Subgroup G} {x : G}
    (h5 : 5 ∣ (pCoreOf 2 Y).relIndex Y) (hxN : x ∈ Subgroup.normalizer (Y : Set G))
    (hx3 : x ^ 3 = 1) (hxY : ∃ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 Y) : ¬ IsXiMinus T Y := by
  rintro ⟨-, h | ⟨-, h⟩⟩
  · have := h 5 Nat.prime_five (h5.trans (Subgroup.relIndex_dvd_card _ _))
    omega
  · have h3 : 3 ∣ (sectionCentralizer Y (pCoreOf 2 Y)).relIndex
        (Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 Y : Set G)) := by
      set N := Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 Y : Set G)
      set C := sectionCentralizer Y (pCoreOf 2 Y)
      have hxN' : x ∈ N := ⟨hxN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hxN⟩
      have hCN : (C.subgroupOf N).Normal :=
        ⟨fun n hn g => conj_mem_sectionCentralizer g.2.1 g.2.2 hn⟩
      have hxC : x ∉ C := by
        rintro ⟨-, -, h⟩
        obtain ⟨y, hy, hxy⟩ := hxY
        exact hxy (h y hy)
      set q : ↥N ⧸ C.subgroupOf N := QuotientGroup.mk ⟨x, hxN'⟩
      have hq1 : q ≠ 1 := by
        rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hxC
      have hq3 : q ^ 3 = 1 := by
        rw [← QuotientGroup.mk_pow, show (⟨x, hxN'⟩ : N) ^ 3 = 1 from Subtype.ext hx3,
          QuotientGroup.mk_one]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hord := orderOf_eq_prime hq3 hq1
      rw [Subgroup.relIndex, Subgroup.index, ← hord]
      exact orderOf_dvd_natCard q
    have := h 3 Nat.prime_three h3
    omega

end Steps

theorem stmt15410_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T) (h3 : Stmt1542Three G T)
    (h4 : Stmt1542Four G T) (h5 : Stmt1545 G T)
    (h137loc : ∀ X : Subgroup G, IsXi T X →
      IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G))) :
    Stmt15410 G T := by
  classical
  intro X hX M hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hXo, hTX, -, p₀, hp₀, hp₀2, hidx⟩, hXZ, -⟩ := hX
  have hXM : X ≤ M := le_sup_left.trans hM.2
  have hTM : T ≤ M := le_sup_right.trans hM.2
  refine le_inf hXM ?_
  by_contra hXV
  set Z := quasithinOmegaOneCenter T with hZ
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hTodd : ∀ K : Subgroup G, T ≤ K → ¬ 2 ∣ T.relIndex K := fun K hTK h =>
    hyp.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTK))
  have hX3 : (pCoreOf 2 X).relIndex X = 3 := by
    have hdvd : p₀ ∣ Nat.card (Subgroup.centralizer (Z : Set G)) :=
      hidx ▸ (Subgroup.relIndex_dvd_card _ _).trans (Subgroup.card_dvd_of_le hXZ)
    rcases h5 p₀ hp₀ hdvd with h | h
    · exact absurd h hp₀2
    · rw [hidx, h]
  have hMs : Group.IsSolvable M := h2 M ⟨hM.1, hTM⟩
  have hR : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM.1.1
  set S : Sylow 2 G := hT2.toSylow hyp.sylow.2 with hSdef
  have hS : (S : Subgroup G) = T := IsPGroup.toSylow_coe hT2 hyp.sylow.2
  have hInHM : InH (S : Subgroup G) M := ⟨hS ▸ hTM, hR⟩
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    charTwo_of_inH hyp.qtke.2.1 S hInHM
  have hRT : pCoreOf 2 M ≤ T := pCoreOf_two_le_of_sylowIn hTM hT2 (hTodd M hTM)
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p M ≤ 2 := fun p hp hp2 =>
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 M hM.1.1).trans
      hyp.qtke.2.2
  have hQ : ¬ pCoreOf 2 X ≤ pCoreOf 2 M :=
    not_le_pCoreOf_of_not_le_centralizer hT2 hTM (hTodd M hTM) hF hXM hTX hXZ
      (by rw [hX3]; decide) hXV
  have hQT : pCoreOf 2 X ≤ T := by
    have h1 : pCoreOf 2 X ≤ pCoreOf 2 (X ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans le_sup_left)
        (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
          (hTX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    exact h1.trans (pCoreOf_two_le_of_sylowIn le_sup_right hT2 (hTodd _ le_sup_right))
  obtain ⟨p, Y, x, hp, hp2, hYM, hMY, hYXi, hYpow, hcard, h9, hxX, hxo, ⟨y₀, hy₀Y, hy₀x⟩,
    -⟩ := exists_xi_of_not_le_pCoreOf hTM hRT hR hMs hrank hXM hXo hX3 hQT hQ
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hO2le : pCoreOf 2 Y ≤ ⁅Y, Y⁆ ⊔ pCoreOf 2 Y := le_sup_right
  have hxY : ∃ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 Y :=
    ⟨y₀, hy₀Y, fun h => hy₀x (hO2le h)⟩
  obtain ⟨h3Z, -, h3plus, h35⟩ := h3 Y hYXi
  have hpdvd : p ∣ (pCoreOf 2 Y).relIndex Y := by
    rcases hcard with ⟨h, -⟩ | h <;> rw [h] <;> exact dvd_pow_self p (by norm_num)
  by_cases hp3 : p = 3
  swap
  ·
    exfalso
    have hp5 : p = 5 := by
      rcases h35 with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [hk] at hpdvd
        exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow hpdvd)) hp3
      · rw [hk] at hpdvd
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow hpdvd)
    exact h3plus ⟨hYXi, not_isXiMinus_of_five (hp5 ▸ hpdvd) (hMY (hXM hxX)) hx3 hxY⟩
  subst hp3
  have hY9 : (pCoreOf 2 Y).relIndex Y = 9 := h9 rfl
  have hcomm : ⁅Y, Y⁆ ≤ pCoreOf 2 Y := by
    rcases hcard with ⟨-, h⟩ | h
    · exact h
    · rw [hY9] at h
      norm_num at h
  have hK₀ : ⁅Y, Y⁆ ⊔ pCoreOf 2 Y = pCoreOf 2 Y := sup_eq_right.mpr hcomm
  have hYXi' := hYXi
  obtain ⟨-, hTY, -, p', -, -, -, -, hirr⟩ := hYXi'
  rw [hK₀] at hirr
  set H := Y ⊔ (X ⊔ T) with hHdef
  have hXTM : X ⊔ T ≤ M := sup_le hXM hTM
  have hHM : H ≤ M := sup_le hYM hXTM
  have hTH : T ≤ H := le_sup_right.trans le_sup_right
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := hHM.trans hMY
  have hRH : pCoreOf 2 M ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRT.trans hTH)
      (hHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hH2 : pCoreOf 2 H ≠ ⊥ := fun h => hR (le_bot_iff.mp (h ▸ hRH))
  have hFH : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H :=
    charTwo_of_le hyp.qtke.2.1 S (hS ▸ hTH) hHM hInHM
  set W := VZ T H with hWdef
  have hWred : IsTwoReducedIn H W :=
    isTwoReducedIn_conjClosure_of_sylowIn hTH hT2 (hTodd H hTH) hFH (le_refl Z)
  obtain ⟨hWc, -⟩ :=
    conjClosure_le_centerOf_pCoreOf_of_sylowIn hTH hT2 (hTodd H hTH) hFH (le_refl Z)
  have hWM : W ≤ pCoreOf 2 M :=
    (conjClosure_mono le_rfl hHM).trans ((conjClosure_le_centerOf_pCoreOf_of_sylowIn hTM hT2
      (hTodd M hTM) hF (le_refl Z)).1.trans inf_le_left)
  have hZW : Z ≤ W := le_conjClosure Z H
  have := hyp.simple
  have hZ1 : Z ≠ ⊥ :=
    quasithinOmegaOneCenter_ne_bot hT2 (hS ▸ sylow_ne_bot hyp.nonabelian S)
  have hW1 : W ≠ ⊥ := fun h => hZ1 (le_bot_iff.mp (h ▸ hZW))
  have hU := h137loc Y hYXi
  have hMN : M = Subgroup.normalizer (Y : Set G) := hU.2 M ⟨hM.1, sup_le hYM hTM⟩
  have hUH : IsUniqueM H M := ⟨⟨hM.1, hHM⟩, fun M' hM' =>
    (hU.2 M' ⟨hM'.1, (sup_le le_sup_left (le_sup_right.trans le_sup_right)).trans hM'.2⟩).trans
      hMN.symm⟩
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := hWred.2.1
  have hO2W : pCoreOf 2 Y ≤ Subgroup.centralizer (W : Set G) := by
    have h1 : pCoreOf 2 Y ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans le_sup_left)
        (hHY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    refine h1.trans ?_
    rw [← Subgroup.le_centralizer_iff]
    exact hWc.trans inf_le_right
  have hYW : Y ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 Y := by
    have hTn : T ≤ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer (W : Set G) :
        Subgroup G) : Set G) := by
      intro t ht
      refine A4.mem_normalizer_of_conj_mem fun g hg => ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hTY ht) g).mp hg.1
      · exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (hHW (hTH ht))) g).mp
          hg.2
    rcases hirr _ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) hO2W) inf_le_left hTn with h | h
    · exact h
    · exfalso
      apply h3Z
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      have hYC : Y ≤ Subgroup.centralizer (W : Set G) := by
        rw [← h]
        exact inf_le_right
      exact hYC.trans (Subgroup.centralizer_le hZW)
  obtain ⟨n, hn⟩ := exists_card_sup_dvd hTX (hXTM.trans hMY) hT2 hY9 hX3
  obtain ⟨hq, hCW2⟩ := two_lt_qhatInt_of_section hWred le_sup_left hHY hYW hY9 hYpow hcomm
    ((le_sup_left.trans le_sup_right : X ≤ H) hxX) hx3 hxY hTH hirr hn
  have hTC : T ⊓ Subgroup.centralizer (W : Set G) =
      pCoreOf 2 (H ⊓ Subgroup.centralizer (W : Set G)) := by
    have hHC : H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (W : Set G) :
        Subgroup G) : Set G) := by
      intro h hh
      refine A4.mem_normalizer_of_conj_mem fun g hg => ⟨?_, ?_⟩
      · exact H.mul_mem (H.mul_mem hh hg.1) (H.inv_mem hh)
      · exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (hHW hh)) g).mp hg.2
    have h1 : H ⊓ Subgroup.centralizer (W : Set G) ≤
        pCoreOf 2 (H ⊓ Subgroup.centralizer (W : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hCW2
    have hCT : H ⊓ Subgroup.centralizer (W : Set G) ≤ T :=
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hHC hCW2).trans
        (pCoreOf_two_le_of_sylowIn hTH hT2 (hTodd H hTH))
    apply le_antisymm
    · exact (inf_le_inf_right _ hTH).trans h1
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (le_inf hCT inf_le_right)
  have hle := h4 H M W ⟨hTH, hH2⟩ hUH hW1 hWred hTC hWM
  exact (not_le.mpr hq) hle

end CFSG.Quasithin.EmptyFaithfulMultiple
