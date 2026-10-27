module

public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G] [Finite G]

namespace A4

theorem pCoreOf_le_centralizer_of_isTwoReducedIn {M V : Subgroup G} (hV : IsTwoReducedIn M V) :
    pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G) := by
  refine hV.2.2.2 (pCoreOf 2 M) (pCoreOf_le 2 M) (le_normalizer_pCoreOf 2 M) fun d hd => ?_
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨d, hd⟩
  exact ⟨k, by rw [show d ^ 2 ^ k = 1 from congrArg Subtype.val hk]; exact Subgroup.one_mem _⟩

omit [Finite G] in
theorem le_pCoreOf_of_isTwoReducedIn {M V : Subgroup G} (hV : IsTwoReducedIn M V) :
    V ≤ pCoreOf 2 M := by
  have hp : IsPGroup 2 V := fun v => ⟨1, Subtype.ext (by simpa using hV.2.2.1.2 v v.2)⟩
  exact le_pCoreOf_of_le_normalizer 2 hV.1 hV.2.1 hp

omit [Finite G] in
theorem isTwoReducedIn_bot (M : Subgroup G) : IsTwoReducedIn M ⊥ := by
  refine ⟨bot_le, ?_, ⟨inferInstance, fun x hx => ?_⟩, fun D _ _ _ => ?_⟩
  · rw [(Subgroup.normalizer_eq_top_iff).mpr Subgroup.normal_bot]
    exact le_top
  · rw [Subgroup.mem_bot.mp hx]
    simp
  · intro d _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Subgroup.mem_bot.mp hh]
    simp

theorem isTwoReducedIn_sup {M V₁ V₂ : Subgroup G} (h₁ : IsTwoReducedIn M V₁)
    (h₂ : IsTwoReducedIn M V₂) : IsTwoReducedIn M (V₁ ⊔ V₂) := by
  have hcomm : ∀ x ∈ V₁, ∀ y ∈ V₂, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (pCoreOf_le_centralizer_of_isTwoReducedIn h₁
      (le_pCoreOf_of_isTwoReducedIn h₂ hy)) x hx
  have hunion : V₁ ⊔ V₂ = Subgroup.closure ((V₁ : Set G) ∪ (V₂ : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hcommJ : IsMulCommutative (V₁ ⊔ V₂ : Subgroup G) := by
    rw [hunion]
    refine Subgroup.isMulCommutative_closure ?_
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact congrArg Subtype.val (h₁.2.2.1.1.is_comm.comm (⟨x, hx⟩ : V₁) ⟨y, hy⟩)
    · exact hcomm x hx y hy
    · exact (hcomm y hy x hx).symm
    · exact congrArg Subtype.val (h₂.2.2.1.1.is_comm.comm (⟨x, hx⟩ : V₂) ⟨y, hy⟩)
  have hsq : ∀ z ∈ V₁ ⊔ V₂, z ^ 2 = 1 := by
    intro z hz
    rw [hunion] at hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact h₁.2.2.1.2 x hx
      · exact h₂.2.2.1.2 x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      rw [← hunion] at hx hy
      have hxy : x * y = y * x :=
        congrArg Subtype.val (hcommJ.is_comm.comm (⟨x, hx⟩ : ↥(V₁ ⊔ V₂)) ⟨y, hy⟩)
      rw [(Commute.mul_pow hxy 2 : (x * y) ^ 2 = x ^ 2 * y ^ 2), ihx, ihy, mul_one]
    | inv x _ ih => rw [inv_pow, ih, inv_one]
  refine ⟨sup_le h₁.1 h₂.1, fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨h₁.2.1 hg, h₂.2.1 hg⟩, ⟨hcommJ, hsq⟩, ?_⟩
  intro D hDM hMD hD
  have key : ∀ V : Subgroup G, V ≤ V₁ ⊔ V₂ → IsTwoReducedIn M V → D ≤ Subgroup.centralizer (V : Set G) := by
    intro V hV hred
    exact hred.2.2.2 D hDM hMD fun d hd => by
      obtain ⟨k, hk⟩ := hD d hd
      exact ⟨k, Subgroup.centralizer_le (fun x hx => hV hx) hk⟩
  exact Subgroup.le_centralizer_iff.mpr (sup_le
    (Subgroup.le_centralizer_iff.mp (key V₁ le_sup_left h₁))
    (Subgroup.le_centralizer_iff.mp (key V₂ le_sup_right h₂)))

omit [Finite G] in
theorem le_twoReducedJoin {M V : Subgroup G} (hV : IsTwoReducedIn M V) : V ≤ twoReducedJoin M :=
  le_iSup₂ (f := fun (V : Subgroup G) (_ : IsTwoReducedIn M V) => V) V hV

theorem isTwoReducedIn_twoReducedJoin (M : Subgroup G) :
    IsTwoReducedIn M (twoReducedJoin M) := by
  obtain ⟨V₀, -, hV₀⟩ := Finite.exists_le_maximal (p := IsTwoReducedIn M) (a := ⊥)
    (isTwoReducedIn_bot M)
  have : twoReducedJoin M = V₀ := by
    refine le_antisymm (iSup₂_le fun V hV => ?_) (le_twoReducedJoin hV₀.1)
    exact le_sup_left.trans (hV₀.2 (isTwoReducedIn_sup hV hV₀.1) le_sup_right)
  rw [this]
  exact hV₀.1

omit [Finite G] in
theorem normalizer_bot_eq_top : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
  Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot

theorem isPGroup_two_of_odd_order_eq_one {K : Subgroup G}
    (h : ∀ a ∈ K, Odd (orderOf a) → a = 1) : IsPGroup 2 K := by
  intro a
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (a : G)).ne'
  refine ⟨k, Subtype.ext ?_⟩
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  have hodd : Odd (orderOf ((a : G) ^ 2 ^ k)) := by
    rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  exact h _ (K.pow_mem a.2 _) hodd

theorem charTwo_of_normal {H N : Subgroup G} (hHN : H ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (H : Set G)) (hN : CharTwo N) : CharTwo H := by
  set Q := pCoreOf 2 N with hQ
  set P := pCoreOf 2 H with hP
  have hHsub : IsSubnormal H N :=
    subnormal_of_normal hHN (Subgroup.normal_subgroupOf_of_le_normalizer hnorm)
  have hPQ : P ≤ Q := pCoreOf_le_of_subnormal 2 hHsub
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 N
  have hHQ : H ⊓ Q ≤ P := le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg) (hNQ (hHN hg)))
    ((pCoreOf_isPGroup 2 N).to_le inf_le_right)
  set K := H ⊓ Subgroup.centralizer (P : Set G) with hK
  have hNP : N ≤ Subgroup.normalizer (P : Set G) :=
    hnorm.trans (normalizer_le_normalizer_pCoreOf 2 H)
  have hKN : N ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    mem_normalizer_inf (hnorm hg) (mem_normalizer_centralizer (hNP hg))
  have hKp : IsPGroup 2 K := by
    refine isPGroup_two_of_odd_order_eq_one fun b hb hodd => ?_
    have hbH : b ∈ H := hb.1
    have hbN : b ∈ N := hHN hbH
    have hnb : b ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [normalizer_bot_eq_top]; trivial
    have hser := commutator_mem_of_series (N := ⊥) (B := P) (D := Q) (a := b) hodd hnb
      (by rw [normalizer_bot_eq_top]; exact le_top) hPQ
      (fun d hd => by
        obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 N ⟨d, hd⟩
        exact ⟨j, by rw [show d ^ 2 ^ j = 1 from congrArg Subtype.val hj]; exact Subgroup.one_mem _⟩)
      (fun d hd => by
        apply hHQ
        refine ⟨?_, ?_⟩
        · have h1 : d * b⁻¹ * d⁻¹ ∈ H :=
            (Subgroup.mem_normalizer_iff.mp (hnorm (pCoreOf_le 2 N hd)) b⁻¹).mp (H.inv_mem hbH)
          have h2 : b * (d * b⁻¹ * d⁻¹) ∈ H := H.mul_mem hbH h1
          have h3 : b * d * b⁻¹ * d⁻¹ = b * (d * b⁻¹ * d⁻¹) := by group
          rw [h3]; exact h2
        · have h1 : b * d * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hNQ hbN) d).mp hd
          exact Q.mul_mem h1 (Q.inv_mem hd))
      (fun x hx => by
        have hxb : x * b = b * x := Subgroup.mem_centralizer_iff.mp hb.2 x hx
        have : b * x * b⁻¹ * x⁻¹ = 1 := by
          rw [← hxb]
          group
        rw [this]; exact Subgroup.one_mem _)
    have hbc : b ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 : b * d * b⁻¹ * d⁻¹ = 1 := Subgroup.mem_bot.mp (hser d hd)
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      calc d * b = (b * d * b⁻¹) * b := by rw [h1]; group
        _ = b * d := by group
    have hbQ : b ∈ Q := hN ⟨hbN, hbc⟩
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 N ⟨b, hbQ⟩
    have hj' : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hcop : Nat.Coprime (orderOf b) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hj'))
  exact fun x hx => hHQ ⟨hx.1, le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hHN) hKN hKp hx⟩

theorem charTwo_of_subnormal {X M : Subgroup G} (hXM : IsSubnormal X M) :
    CharTwo M → CharTwo X := by
  induction hXM with
  | refl K => exact id
  | @step H M' K hle hN hMK ih =>
    intro hK
    exact charTwo_of_normal hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN) (ih hK)

omit [Finite G] in
theorem autOn_conj_mem {V M D : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hDM : D ≤ M) (hMD : M ≤ Subgroup.normalizer (D : Set G)) {a b : MulAut V}
    (ha : a ∈ autOn M V) (hb : b ∈ autOn D V) : a * b * a⁻¹ ∈ autOn D V := by
  obtain ⟨m, rfl⟩ := (mem_autOn_iff hMV).mp ha
  obtain ⟨d, rfl⟩ := (mem_autOn_iff (hDM.trans hMV)).mp hb
  have hmd : (m : G) * d * (m : G)⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hMD m.2) d).mp d.2
  refine (mem_autOn_iff (hDM.trans hMV)).mpr ⟨⟨m * d * (m : G)⁻¹, hmd⟩, ?_⟩
  have e1 : actionOn V D (hDM.trans hMV) ⟨m * d * (m : G)⁻¹, hmd⟩ =
      actionOn V M hMV (m * ⟨d, hDM d.2⟩ * m⁻¹) := rfl
  have e2 : actionOn V D (hDM.trans hMV) d = actionOn V M hMV ⟨d, hDM d.2⟩ := rfl
  rw [e1, e2, map_mul, map_mul, map_inv]

omit [Finite G] in
theorem isTwoReducedIn_of_pCoreOf_autOn_eq_bot {M V : Subgroup G} (hVM : V ≤ M)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hel : IsElemAbelian 2 V)
    (hQ : pCoreOf 2 (autOn M V) = ⊥) : IsTwoReducedIn M V := by
  refine ⟨hVM, hMV, hel, fun D hDM hMD hD => ?_⟩
  have hDV : D ≤ Subgroup.normalizer (V : Set G) := hDM.trans hMV
  have hp : IsPGroup 2 (autOn D V) := by
    rintro ⟨a, ha⟩
    obtain ⟨d, rfl⟩ := (mem_autOn_iff hDV).mp ha
    obtain ⟨k, hk⟩ := hD d d.2
    refine ⟨k, Subtype.ext ?_⟩
    show (actionOn V D hDV d) ^ 2 ^ k = 1
    rw [← map_pow]
    exact (actionOn_eq_one_iff hDV _).mpr hk
  have hDle : autOn D V ≤ pCoreOf 2 (autOn M V) := by
    refine le_pCoreOf_of_le_normalizer 2 (autOn_mono hDM) ?_ hp
    intro a ha
    have key : ∀ a ∈ autOn M V, ∀ b ∈ autOn D V, a * b * a⁻¹ ∈ autOn D V :=
      fun a ha b hb => autOn_conj_mem hMV hDM hMD ha hb
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨fun hb => key a ha b hb, fun hb => ?_⟩
    have := key a⁻¹ (Subgroup.inv_mem _ ha) _ hb
    simpa [mul_assoc] using this
  rw [hQ, le_bot_iff] at hDle
  intro d hd
  have h1 : actionOn V D hDV ⟨d, hd⟩ ∈ autOn D V := (mem_autOn_iff hDV).mpr ⟨⟨d, hd⟩, rfl⟩
  rw [hDle, Subgroup.mem_bot] at h1
  exact (actionOn_eq_one_iff hDV _).mp h1

theorem exists_isTwoReducedIn_of_isXf {X M : Subgroup G} (hX : IsXClass X)
    (hXM : IsSubnormal X M) (hchief : NoncentralTwoChiefFactorsInO2 X) (hv : VY X ≠ ⊥) :
    ∃ V, IsTwoReducedIn M V ∧ ⁅V, X⁆ ≠ ⊥ := by
  have hXX : X = oTwoUpper X := hX.2.1
  have hXM' : X ≤ M := subnormal_le hXM
  set R := pCoreOf 2 M with hR
  set U := omegaOneCenterOf R with hU
  have hUne : ⁅U, X⁆ ≠ ⊥ := (a4_9 hX hXM).mpr hv
  let P : Subgroup G → Prop := fun W =>
    W ≤ U ∧ W ≠ ⊥ ∧ M ≤ Subgroup.normalizer (W : Set G) ∧ ⁅W, X⁆ ≠ ⊥
  have hUP : P U := ⟨le_rfl, fun h => hUne (by rw [h]; exact Subgroup.commutator_bot_left (H₁ := X)),
    fun g hg => normalizer_le_normalizer_omegaOneCenterOf R (le_normalizer_pCoreOf 2 M hg), hUne⟩
  obtain ⟨V, -, hVmin⟩ := exists_minimal_le_subgroup hUP
  obtain ⟨hVU, hVne, hMV, hVX⟩ := hVmin.1
  have hVR : V ≤ R := hVU.trans (omegaOneCenterOf_le R)
  have hRC : R ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hVU.trans ((omegaOneCenterOf_le_centerOf R).trans (centerOf_le_centralizer R)))
  have hO2 : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) :=
    (pCoreOf_le_of_subnormal 2 hXM).trans hRC
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := hXM'.trans hMV
  have hV2 : IsPGroup 2 V := (pCoreOf_isPGroup 2 M).to_le hVR
  have hVel : IsElemAbelian 2 V :=
    ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_omegaOneCenterOf (hVU a.2) (hVU b.2))⟩⟩,
      fun x hx => sq_eq_one_of_mem_omegaOneCenterOf (hVU hx)⟩
  set A := autOn M V with hA
  set Y := autOn X V with hY
  set Q := pCoreOf 2 A with hQ
  have hYY : Y = oTwoUpper Y := by rw [hY, oTwoUpper_autOn hXV, ← hXX]
  have hYA : IsSubnormal Y A := autOn_subnormal hXM
  have hQsig : IsSignalizer A Y Q :=
    ⟨pCoreOf_le 2 A, pCoreOf_isPGroup 2 A, (autOn_mono hXM').trans (le_normalizer_pCoreOf 2 A)⟩
  have hcomm1 : ⁅Y, Q⁆ ≤ pCoreOf 2 Y := a4_2_3 hYY hYA hQsig
  have hcen : pCoreOf 2 Y ≤ centerOf Y := pCoreOf_autOn_le_centerOf hXV hXX hchief hO2
  have hYQ : ⁅Y, Q⁆ = ⊥ := by
    have hQn : Y ≤ Subgroup.normalizer (Q : Set (MulAut V)) :=
      (autOn_mono hXM').trans (le_normalizer_pCoreOf 2 A)
    have hBc : pCoreOf 2 Y ⊓ Q ≤ Subgroup.centralizer (Y : Set (MulAut V)) :=
      inf_le_left.trans (hcen.trans (centerOf_le_centralizer Y))
    have key := commutator_le_of_oTwoUpper (A := Y) (N := ⊥) (B := pCoreOf 2 Y ⊓ Q) (D := Q)
      (by rw [normalizer_bot_eq_top]; exact le_top) (by rw [normalizer_bot_eq_top]; exact le_top)
      inf_le_right
      (fun d hd => by
        obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 A ⟨d, hd⟩
        exact ⟨j, by rw [show d ^ 2 ^ j = 1 from congrArg Subtype.val hj]; exact Subgroup.one_mem _⟩)
      (le_inf hcomm1 (Subgroup.le_normalizer_iff_commutator_le_right.mp hQn))
      (by
        rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hBc).le)
    rw [← hYY] at key
    exact le_bot_iff.mp key
  obtain ⟨D, hDM, hMD, hD2, hDQ', hDQ⟩ := exists_preimage_section hMV (pCoreOf_le 2 A)
    (le_normalizer_pCoreOf 2 A) (pCoreOf_isPGroup 2 A)
  have hDB : ∀ b ∈ D, ∃ k : ℕ, b ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) := fun b hb => by
    obtain ⟨k, hk⟩ := hD2 b hb
    exact ⟨k, hk.2⟩
  have hXD : ⁅X, D⁆ ≤ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.commutator_le.mpr fun x hx d hd => ?_
    have hxM : x ∈ M := hXM' hx
    have hdM : d ∈ M := hDM hd
    have hq : actionOn V M hMV ⟨d, hdM⟩ ∈ Q := hDQ' ⟨d, hdM⟩ hd
    have hy : actionOn V M hMV ⟨x, hxM⟩ ∈ Y := (mem_autOn_iff hXV).mpr ⟨⟨x, hx⟩, rfl⟩
    have hmem := Subgroup.commutator_mem_commutator hy hq
    rw [hYQ, Subgroup.mem_bot] at hmem
    have h1 : actionOn V M hMV (⟨x, hxM⟩ * ⟨d, hdM⟩ * ⟨x, hxM⟩⁻¹ * ⟨d, hdM⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hmem
    exact (actionOn_eq_one_iff hMV _).mp h1
  have hcentW : ¬ X ≤ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
    intro hfix
    have hXC : X ≤ Subgroup.centralizer (V : Set G) :=
      thompson_axb hV2 hXX hXV (hDM.trans hMV) hDB hXD hfix
    exact hVX (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hXC))
  have hW : P (V ⊓ Subgroup.centralizer (D : Set G)) := by
    refine ⟨inf_le_left.trans hVU, ?_, ?_, ?_⟩
    · intro h
      apply hcentW
      rw [h]
      intro x _
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Subgroup.mem_bot.mp hy]
        simp
    · exact fun g hg => mem_normalizer_inf (hMV hg) (mem_normalizer_centralizer (hMD hg))
    · intro h
      exact hcentW (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h))
  have hVW : V ≤ V ⊓ Subgroup.centralizer (D : Set G) := hVmin.2 hW inf_le_left
  have hDV : D ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hVW.trans inf_le_right)
  have hQbot : Q = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨x, hxD, hxq⟩ := hDQ q hq
    have h1 : actionOn V M hMV x = 1 := (actionOn_eq_one_iff hMV _).mpr (hDV hxD)
    rw [Subgroup.mem_bot, ← hxq, h1]
  exact ⟨V, isTwoReducedIn_of_pCoreOf_autOn_eq_bot (hVR.trans (pCoreOf_le 2 M)) hMV hVel hQbot,
    hVX⟩

theorem isXf_of_isTwoReducedIn {X M V : Subgroup G} (hFM : CharTwo M) (hX : X = oTwoUpper X)
    (hXM : IsSubnormal X M) (hV : IsTwoReducedIn M V) (hne : ⁅V, X⁆ ≠ ⊥) : IsXf X := by
  have hXc : IsXClass X := ⟨fun h => hne (by rw [h]; exact Subgroup.commutator_bot_right (H₁ := V)),
    hX, charTwo_of_subnormal hXM hFM⟩
  have hXM' : X ≤ M := subnormal_le hXM
  have hO2M : pCoreOf 2 X ≤ pCoreOf 2 M := pCoreOf_le_of_subnormal 2 hXM
  have hO2C : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_isTwoReducedIn hV
  have hVO : V ≤ pCoreOf 2 M := le_pCoreOf_of_isTwoReducedIn hV
  set S := pCoreOf 2 X ⊔ V with hS
  have hSle : S ≤ pCoreOf 2 M := sup_le hO2M hVO
  have hsig : IsSignalizer M X S :=
    ⟨hSle.trans (pCoreOf_le 2 M), (pCoreOf_isPGroup 2 M).to_le hSle,
      fun x hx => Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨le_normalizer_pCoreOf 2 X hx, hV.2.1 (hXM' hx)⟩⟩
  have hVS : V ≤ Subgroup.centralizer (S : Set G) :=
    Subgroup.le_centralizer_iff.mpr (sup_le (hO2M.trans hO2C)
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.2.2.1.1))
  have hVΩ : V ≤ omegaOneCenterOf S := fun x hx =>
    Subgroup.subset_closure ⟨⟨(le_sup_right : V ≤ S) hx, hVS hx⟩, hV.2.2.1.2 x hx⟩
  have hVS' : VYR X S ≠ ⊥ := fun h =>
    hne (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hVΩ (le_refl X)))
  exact ⟨hXc, (a4_8_5 (A48Hyp.of_self hXc hXM hsig le_sup_left)).mp hVS'⟩

end A4

theorem a4_11 {X M : Subgroup G} (hFM : CharTwo M) (hX : X = oTwoUpper X)
    (hXM : IsSubnormal X M) (hchief : NoncentralTwoChiefFactorsInO2 X) :
    List.TFAE [IsXf X, ∃ V, IsTwoReducedIn M V ∧ ⁅V, X⁆ ≠ ⊥, ⁅twoReducedJoin M, X⁆ ≠ ⊥] := by
  tfae_have 1 → 2 := fun h => A4.exists_isTwoReducedIn_of_isXf h.1 hXM hchief h.2
  tfae_have 2 → 1 := fun ⟨V, hV, hne⟩ => A4.isXf_of_isTwoReducedIn hFM hX hXM hV hne
  tfae_have 2 → 3 := fun ⟨V, hV, hne⟩ h => hne (le_bot_iff.mp
    (h ▸ Subgroup.commutator_mono (A4.le_twoReducedJoin hV) (le_refl X)))
  tfae_have 3 → 2 := fun h => ⟨twoReducedJoin M, A4.isTwoReducedIn_twoReducedJoin M, h⟩
  tfae_finish

end CFSG.Quasithin
