module

public import CFSG.Quasithin.Vol2.Ch12Sec1Swap
public import CFSG.Quasithin.Vol2.Ch12Sec1H91

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace Sec1215

section Sylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_of_le_of_le {P C A : Subgroup G} (hP : IsSylowTwoOf P A) (hPC : P ≤ C)
    (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.2.1, fun hdvd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  have h2 : 2 ∣ P.relIndex A := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem isSylowTwoOf_of_normalizer_le {K S M : Subgroup G} (hSK : S ≤ K)
    (hNM : Subgroup.normalizer (S : Set G) ≤ M) (hSyl : IsSylowTwoOf S (K ⊓ M)) :
    IsSylowTwoOf S K := by
  rw [A4.isSylowTwoOf_iff_maximal] at hSyl ⊢
  refine ⟨hSK, hSyl.2.1, fun P hPK hP hSP => ?_⟩
  have h1 : P ⊓ Subgroup.normalizer (S : Set G) ≤ S :=
    hSyl.2.2 _ (le_inf (inf_le_left.trans hPK) (inf_le_right.trans hNM)) (hP.to_le inf_le_left)
      (le_inf hSP Subgroup.le_normalizer)
  by_contra hne
  have hlt : S.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ S.subgroupOf P := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  have hxNorm : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
    have hxsub : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hSP]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  exact hxnot (Subgroup.mem_subgroupOf.mpr (h1 ⟨x.2, hxNorm⟩))

theorem exists_ne_one_mem_centralizer {P X : Subgroup G} (hP : IsPGroup 2 P) (hXP : X ≤ P)
    (hnorm : P ≤ Subgroup.normalizer (X : Set G)) (hX : X ≠ ⊥) :
    ∃ x ∈ X, x ≠ 1 ∧ x ∈ Subgroup.centralizer (P : Set G) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have : (X.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : X.subgroupOf P ≠ ⊥ := by
    intro h
    apply hX
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hXP hv⟩ : P) ∈ X.subgroupOf P := hv
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(w.1 : P), w.2.1, fun h => hw (Subtype.ext (Subtype.ext h)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have := Subgroup.mem_center_iff.1 w.2.2 ⟨t, ht⟩
  exact congrArg Subtype.val this

theorem padicValNat_card_of_isSylowTwoOf {S H : Subgroup G} (hS : IsSylowTwoOf S H) :
    padicValNat 2 (Nat.card H) = padicValNat 2 (Nat.card S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (S.subgroupOf H).card_mul_index
  have h2 : Nat.card ↥(S.subgroupOf H) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  rw [h2] at h1
  rw [← h1, padicValNat.mul Nat.card_pos.ne' (Subgroup.index_ne_zero_of_finite),
    padicValNat.eq_zero_of_not_dvd hS.2.2, add_zero]

omit [Finite G] in
theorem card_eq_card_inf_centralizer_mul (M : Subgroup G) (x : G) :
    Nat.card M = Nat.card ↥(M ⊓ Subgroup.centralizer ({x} : Set G)) *
      Nat.card {y : G // ∃ m ∈ M, m * x * m⁻¹ = y} := by
  let _ : MulAction ↥M G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp M.subtype)
  have hsmul : ∀ (m : ↥M) (y : G), m • y = (m : G) * y * (m : G)⁻¹ := fun m y => rfl
  have hstab : MulAction.stabilizer ↥M x =
      (M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨m.2, ?_⟩
      calc (m : G) * x = ((m : G) * x * (m : G)⁻¹) * m := by group
        _ = x * m := by rw [h]
    · rintro ⟨-, h⟩
      rw [h, mul_inv_cancel_right]
  have horb : Nat.card (MulAction.orbit ↥M x) =
      Nat.card {y : G // ∃ m ∈ M, m * x * m⁻¹ = y} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun y => by
      rw [MulAction.mem_orbit_iff]
      exact ⟨fun ⟨m, hm⟩ => ⟨m, m.2, hm⟩, fun ⟨m, hm, h⟩ => ⟨⟨m, hm⟩, h⟩⟩
  have h1 := (MulAction.stabilizer ↥M x).card_mul_index
  rw [MulAction.index_stabilizer, hstab] at h1
  rw [← h1, ← horb, Nat.card_coe_set_eq]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

omit [Finite G] in
theorem card_centralizer_conj (g x : G) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨g⁻¹ * y * g, ?_⟩
      invFun := fun y => ⟨g * y * g⁻¹, ?_⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  · have h := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group
  · have h := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group

end Sylow

section One

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

theorem two_mul_card_inf_normalizer (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V]
    {X : Subgroup G} (hXM : X ≤ Subgroup.normalizer (L : Set G)) {x₀ : G} (hx₀ : x₀ ∈ X)
    (hx₀1 : x₀ ∉ Subgroup.normalizer (V₁ : Set G)) :
    2 * Nat.card ↥(X ⊓ Subgroup.normalizer (V₁ : Set G)) = Nat.card X := by
  set H := (X ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf X with hH
  have hidx : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x₀, hx₀⟩, fun b => xor_iff_iff_not.mpr ?_⟩
    simp only [hH, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
    have hb := b.2
    constructor
    · rintro ⟨-, h1⟩ ⟨-, h2⟩
      have h3 := (Subgroup.normalizer (V₁ : Set G)).mul_mem (Subgroup.inv_mem _ h2) h1
      exact hx₀1 (by simpa using h3)
    · intro hb1
      have hb1' : (b : G) ∉ Subgroup.normalizer (V₁ : Set G) := fun h => hb1 ⟨hb, h⟩
      refine ⟨X.mul_mem hb hx₀, Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_⟩
      have h1 := (Sec121Swap.swap_of_hyp121 hyp (hXM hx₀) hx₀1).1 a ha
      have h2 := (Sec121Swap.swap_of_hyp121 hyp (hXM hb) hb1').2 _ h1
      have e : (b : G) * x₀ * a * ((b : G) * x₀)⁻¹ = b * (x₀ * a * x₀⁻¹) * (b : G)⁻¹ := by
        group
      rw [e]
      exact h2
  have h1 := H.card_mul_index
  have h2 : Nat.card H = Nat.card ↥(X ⊓ Subgroup.normalizer (V₁ : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hidx, h2] at h1
  rw [mul_comm]
  exact h1

theorem isSylowTwoOf_inf_normalizer (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V]
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    2 * Nat.card ↥(T ⊓ Subgroup.normalizer (V₁ : Set G)) = Nat.card T ∧
      IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G)) := by
  obtain ⟨t, ht, ht1⟩ := Sec121Swap.exists_mem_not_normalizer hyp hTL
  have hT2 := two_mul_card_inf_normalizer hyp hTL ht ht1
  have hM2 := two_mul_card_inf_normalizer hyp le_rfl (hTL ht) ht1
  have hT₁M₁ : T ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) :=
    inf_le_inf_right _ hTL
  refine ⟨hT2, hT₁M₁, hyp.sylow.1.to_le inf_le_left, fun hdvd => hyp.sylow.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_card (T ⊓ Subgroup.normalizer (V₁ : Set G))
    (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G))
  have h2 := Subgroup.relIndex_mul_card T (Subgroup.normalizer (L : Set G))
  rw [inf_eq_left.mpr hT₁M₁] at h1
  rw [inf_eq_left.mpr hTL] at h2
  have hpos : 0 < Nat.card ↥(T ⊓ Subgroup.normalizer (V₁ : Set G)) := Nat.card_pos
  have hr : T.relIndex (Subgroup.normalizer (L : Set G)) =
      (T ⊓ Subgroup.normalizer (V₁ : Set G)).relIndex
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G)) := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    have h3 : 2 * (T.relIndex (Subgroup.normalizer (L : Set G)) *
        Nat.card ↥(T ⊓ Subgroup.normalizer (V₁ : Set G))) =
        2 * ((T ⊓ Subgroup.normalizer (V₁ : Set G)).relIndex
          (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G)) *
            Nat.card ↥(T ⊓ Subgroup.normalizer (V₁ : Set G))) := by
      rw [h1, hM2, ← h2, ← hT2]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
  have h3 := Subgroup.relIndex_mul_relIndex T (Subgroup.normalizer (L : Set G)) ⊤ hTL le_top
  rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h3
  rw [← h3, hr]
  exact Dvd.dvd.mul_right hdvd _

theorem mem_normalizer_of_mem_centralizer (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V]
    {v : G} (hv : v ∈ V₁) (hv1 : v ≠ 1) {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (hmv : m ∈ Subgroup.centralizer ({v} : Set G)) : m ∈ Subgroup.normalizer (V₁ : Set G) := by
  by_contra h
  have h1 := (Sec121Swap.swap_of_hyp121 hyp hm h).1 v hv
  have h2 : m * v * m⁻¹ = v := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hmv, mul_inv_cancel_right]
  rw [h2] at h1
  have : v ∈ V₁ ⊓ V₂ := ⟨hv, h1⟩
  rw [hyp.inf] at this
  exact hv1 this

theorem le_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : V ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hyp.le
    (Sec121Q.normalizer_le_of_hyp121 hyp) hV2).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTL))

theorem isUniqueM_of_hyp121 (h331 : Stmt3_3_1) (hyp : Hyp121 G T L V V₁ V₂ n)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
      (Subgroup.normalizer (L : Set G)) := by
  have hqs := Sec121Thm.isQuasisimple_of_hyp121 hyp
  have hLT : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun t ht l hl => (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl)
      (le_conjClosure L T)
  obtain ⟨⟨hMmax, -, huniqLT⟩, -⟩ :=
    (h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).2 L hyp.maximal hqs
  rw [hLT] at hMmax huniqLT
  have hQ := setup121Q_holds G T L V V₁ V₂ n hyp hTL
  have hVT := le_of_hyp121 hyp hTL
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hV1 := Sec121Thm.ne_bot_of_hyp121 hyp
  have hQne : T ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥ := by
    intro hbot
    apply hV1
    rw [eq_bot_iff, ← hbot]
    intro v hv
    refine ⟨hVT hv, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := hVe.1
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : ↥V) ⟨v, hv⟩)
  have hNQ : L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    hQ ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hloc : IsTwoLocal (Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) :=
    ⟨_, hQne, hyp.sylow.1.to_le inf_le_left, rfl⟩
  obtain ⟨M'', hM'', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM''eq : M'' = Subgroup.normalizer (L : Set G) := huniqLT M'' hM'' (hNQ.trans hle)
  exact ⟨⟨hMmax, hM''eq ▸ hle⟩, fun M' hM' => huniqLT M' hM'.1 (hNQ.trans hM'.2)⟩

theorem inf_centralizer_ne_bot (hyp : Hyp121 G T L V V₁ V₂ n)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    V₁ ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) ≠ ⊥ := by
  have hn2 : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hVT := le_of_hyp121 hyp hTL
  obtain ⟨x, hx, hx1, hxc⟩ := exists_ne_one_mem_centralizer (hyp.sylow.1.to_le inf_le_left)
    (le_inf (hV₁V.trans hVT) Subgroup.le_normalizer) inf_le_right
    (Sec121Q.ne_bot_of_natural hn2 hnat₁)
  intro h
  have : x ∈ V₁ ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) := ⟨hx, hxc⟩
  rw [h, Subgroup.mem_bot] at this
  exact hx1 this

theorem isSylowTwoOf_of_five (h331 : Stmt3_3_1) (h1213 : Lem1213)
    (hyp : Hyp121 G T L V V₁ V₂ n) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hn : n = 5)
    {v : G} (hv : V₁ ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) = Subgroup.zpowers v) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Subgroup.centralizer ({v} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have := hVe.1
  obtain ⟨-, -, hcV⟩ := Sec1212.card_eq_of_hyp121 hyp
  have hMV := Sec121Q.normalizer_le_of_hyp121 hyp
  have hVT := le_of_hyp121 hyp hTL
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  set T₁ := T ⊓ Subgroup.normalizer (V₁ : Set G) with hT₁
  have hW := h1213 G T L V V₁ V₂ n hyp hn
  have hWT₁ : wClos V 0 T ≤ T₁ :=
    hW.trans (inf_le_inf_left _ ((Subgroup.centralizer_le (by exact_mod_cast hV₁V)).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hSyl : IsSylowIn 2 T ⊤ :=
    ⟨le_top, hyp.sylow.1, by rw [Subgroup.relIndex_top_right]; exact hyp.sylow.2⟩
  have hN1 := e3_15_normalizer hSyl le_top (hyp.sylow.1.to_le inf_le_left) hWT₁
  have h322 : HypE322 T V := ⟨hSyl, hVT, hTL.trans hMV⟩
  have hi : 0 < rk ↥V := by
    unfold rk
    rw [hcV, ← pow_add, padicValNat.prime_pow]
    omega
  have hiw : ((0 : ℕ) : ℕ∞) < wParam T V := by
    have h1 : ((1 : ℕ) : ℕ∞) ≤ wParam T V := le_wParam_of_wClos_le fun j hj => by
      interval_cases j
      exact hW
    exact lt_of_lt_of_le (by norm_num) h1
  have hN2 := (e3_34_two hVe h322 (isUniqueM_of_hyp121 h331 hyp hTL) hi hiw).1
  have hNM : Subgroup.normalizer (T₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := hN1.trans hN2
  have hvmem : v ∈ V₁ ⊓ Subgroup.centralizer (T₁ : Set G) := hv ▸ Subgroup.mem_zpowers v
  have hv1 : v ≠ 1 := by
    intro h1
    apply inf_centralizer_ne_bot hyp hTL
    rw [hv, h1, Subgroup.zpowers_one_eq_bot]
  have hT₁v : T₁ ≤ Subgroup.centralizer ({v} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hvmem.2 t ht
  refine isSylowTwoOf_of_normalizer_le hT₁v hNM ?_
  exact isSylowTwoOf_of_le_of_le (isSylowTwoOf_inf_normalizer hyp hTL).2
    (le_inf hT₁v (inf_le_left.trans hTL))
    (fun m hm => ⟨hm.2, mem_normalizer_of_mem_centralizer hyp hvmem.1 hv1 hm.2 hm.1⟩)

theorem lem1215_one (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1213 : Lem1213) (h1214 : Lem1214)
    (hyp : Hyp121 G T L V V₁ V₂ n) (v : G)
    (hv : V₁ ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) = Subgroup.zpowers v) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Subgroup.centralizer ({v} : Set G)) := by
  rcases hyp.rank with h4 | h5
  · exact h1214 G T L V V₁ V₂ n hyp h4 v hv
  · exact isSylowTwoOf_of_five h331 h1213 hyp
      (Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp).1 h5 hv

end One

section Two

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

theorem not_mem_of_nonsingular (hyp : Hyp121 G T L V V₁ V₂ n) {β : G → G → ZMod 2}
    (hβ : IsDualPairing121 L V₁ V₂ β) {y : G} (hy : IsNonsingular121 V₁ V₂ β y) :
    y ∉ V₁ ∧ y ∉ V₂ := by
  obtain ⟨hβ₁, hβ₂, -, -, -⟩ := hβ
  obtain ⟨a, ha, c, hc, rfl, hac⟩ := hy
  constructor
  · intro h
    obtain ⟨-, rfl⟩ := Sec1212.decomp_unique hyp.inf ha hc h V₂.one_mem (mul_one _).symm
    have := hβ₂ a ha 1 V₂.one_mem 1 V₂.one_mem
    rw [mul_one, hac] at this
    exact absurd this (by decide)
  · intro h
    obtain ⟨rfl, -⟩ := Sec1212.decomp_unique hyp.inf ha hc V₁.one_mem h (one_mul _).symm
    have := hβ₁ 1 V₁.one_mem 1 V₁.one_mem c hc
    rw [mul_one, hac] at this
    exact absurd this (by decide)

theorem two_mul_card_nonsingular (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V]
    {β : G → G → ZMod 2} (hβ : IsDualPairing121 L V₁ V₂ β) :
    2 * Nat.card {y : G // y ∈ V ∧ IsNonsingular121 V₁ V₂ β y} =
      (Nat.card V₁ - 1) * Nat.card V₂ := by
  classical
  have := Fintype.ofFinite ↥V₁
  have := Fintype.ofFinite ↥V₂
  obtain ⟨hβ₁, hβ₂, hnd₁, -, -⟩ := hβ
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have h01 : ∀ e : ZMod 2, ¬ e = 0 → e = 1 := by decide
  have hbij : Nat.card {p : ↥V₁ × ↥V₂ // β p.1 p.2 = 1} =
      Nat.card {y : G // y ∈ V ∧ IsNonsingular121 V₁ V₂ β y} := by
    refine Nat.card_congr (Equiv.ofBijective (fun p => ⟨(p.1.1 : G) * p.1.2,
      V.mul_mem (hV₁V p.1.1.2) (hV₂V p.1.2.2), p.1.1, p.1.1.2, p.1.2, p.1.2.2, rfl, p.2⟩) ⟨?_, ?_⟩)
    · rintro ⟨⟨a, c⟩, hac⟩ ⟨⟨a', c'⟩, hac'⟩ h
      have h1 := congrArg Subtype.val h
      obtain ⟨e1, e2⟩ := Sec1212.decomp_unique hyp.inf a.2 c.2 a'.2 c'.2 h1
      have ea : a = a' := Subtype.ext e1
      have ec : c = c' := Subtype.ext e2
      subst ea ec
      rfl
    · rintro ⟨y, hyV, a, ha, c, hc, rfl, hac⟩
      exact ⟨⟨⟨⟨a, ha⟩, ⟨c, hc⟩⟩, hac⟩, rfl⟩
  have hterm : ∀ a : ↥V₁, 2 * (Finset.univ.filter fun c : ↥V₂ => β a c = 1).card =
      if a = 1 then 0 else Fintype.card ↥V₂ := by
    intro a
    split_ifs with ha
    · rw [ha]
      have : (Finset.univ.filter fun c : ↥V₂ => β ((1 : ↥V₁) : G) c = 1) = ∅ := by
        refine Finset.filter_false_of_mem fun c _ => ?_
        have := hβ₁ 1 V₁.one_mem 1 V₁.one_mem c c.2
        rw [mul_one] at this
        have h0 : β 1 c = 0 := by simpa using this
        simp [h0]
      rw [this, Finset.card_empty]
    · obtain ⟨c₀, hc₀, hc₀1⟩ := hnd₁ a a.2 (fun h => ha (Subtype.ext h))
      have h2 := Sec1212.two_mul_card_filter_eq_zero (fun c : ↥V₂ => β a c)
        (fun c d => hβ₂ a a.2 c c.2 d d.2) (x₀ := ⟨c₀, hc₀⟩) (by rw [hc₀1]; exact one_ne_zero)
      have h3 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun c : ↥V₂ => β a c = 0)
      have h4 : (Finset.univ.filter fun c : ↥V₂ => β a c = 1) =
          Finset.univ.filter fun c : ↥V₂ => ¬ β a c = 0 := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => by rw [h]; exact one_ne_zero, h01 _⟩
      rw [h4]
      rw [Finset.card_univ] at h3
      omega
  have hcount : 2 * Fintype.card {p : ↥V₁ × ↥V₂ // β p.1 p.2 = 1} =
      (Fintype.card ↥V₁ - 1) * Fintype.card ↥V₂ := by
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.mul_sum]
    simp only [← Finset.card_filter]
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, smul_eq_mul]
    have h5 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a : ↥V₁ => a = 1)
    simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.card_singleton,
      Finset.card_univ] at h5
    rw [show (Finset.univ.filter fun a : ↥V₁ => ¬ a = 1).card = Fintype.card ↥V₁ - 1 by omega]
  rw [← hbij, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hcount

theorem lem1215_two (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1211 : Lem1211) (hH91 : LemH91)
    (hyp : Hyp121 G T L V V₁ V₂ n)
    (hone : ∀ v : G, V₁ ⊓ Subgroup.centralizer
        ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) = Subgroup.zpowers v →
      IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Subgroup.centralizer ({v} : Set G)))
    {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) {g : G} (hg : g * v * g⁻¹ = w) :
    ∃ m ∈ Subgroup.normalizer (L : Set G), m * v * m⁻¹ = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn4 : 4 ≤ n := by rcases hyp.rank with h | h <;> omega
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have := hVe.1
  obtain ⟨hTL, -⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have hMV := Sec121Q.normalizer_le_of_hyp121 hyp
  have hVT := le_of_hyp121 hyp hTL
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  obtain ⟨⟨v₁, hv₁⟩, β, hβ, horb⟩ := hH91 G T L V V₁ V₂ n hyp hTL
  obtain ⟨hcard₁, hcard₂, -⟩ := Sec1212.card_eq_of_hyp121 hyp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hyp.sylow.1
  have hTi : ¬ 2 ∣ T.index := hyp.sylow.2
  have hG : padicValNat 2 (Nat.card G) = k := by
    rw [← T.card_mul_index, hk, padicValNat.mul (by positivity) T.index_ne_zero_of_finite,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hTi, add_zero]
  have hM : padicValNat 2 (Nat.card (Subgroup.normalizer (L : Set G))) = k := by
    have h1 := Subgroup.relIndex_mul_card T (Subgroup.normalizer (L : Set G))
    rw [inf_eq_left.mpr hTL] at h1
    have hodd : ¬ 2 ∣ T.relIndex (Subgroup.normalizer (L : Set G)) := fun h => hTi (by
      have h3 := Subgroup.relIndex_mul_relIndex T (Subgroup.normalizer (L : Set G)) ⊤ hTL le_top
      rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h3
      rw [← h3]
      exact Dvd.dvd.mul_right h _)
    rw [← h1, padicValNat.mul (E3.relIndex_ne_zero' _ _) Nat.card_pos.ne',
      padicValNat.eq_zero_of_not_dvd hodd, zero_add, hk, padicValNat.prime_pow]
  set f : G → ℕ := fun x => padicValNat 2 (Nat.card (Subgroup.centralizer ({x} : Set G)))
    with hf
  have hfconj : ∀ m x : G, f (m * x * m⁻¹) = f x := fun m x => by
    simp only [hf, card_centralizer_conj]
  have hfle : ∀ x, f x ≤ k := fun x => by
    rw [← hG]
    exact (padicValNat_dvd_iff_le Nat.card_pos.ne').mp
      (pow_padicValNat_dvd.trans (Subgroup.card_subgroup_dvd_card _))
  have hv₁mem : v₁ ∈ V₁ ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) :=
    hv₁ ▸ Subgroup.mem_zpowers v₁
  have hv₁1 : v₁ ≠ 1 := by
    intro h1
    apply inf_centralizer_ne_bot hyp hTL
    rw [hv₁, h1, Subgroup.zpowers_one_eq_bot]
  have hfv₁ : f v₁ + 1 = k := by
    have h1 := padicValNat_card_of_isSylowTwoOf (hone v₁ hv₁)
    have h2 : padicValNat 2 (2 * Nat.card ↥(T ⊓ Subgroup.normalizer (V₁ : Set G))) = k := by
      rw [(isSylowTwoOf_inf_normalizer hyp hTL).1, hk, padicValNat.prime_pow]
    rw [padicValNat.mul (by norm_num) Nat.card_pos.ne', padicValNat_self] at h2
    simp only [hf]
    rw [h1]
    omega
  have hns₁ : ¬ IsNonsingular121 V₁ V₂ β v₁ := fun h =>
    (not_mem_of_nonsingular hyp hβ h).1 hv₁mem.1
  have hf₃ : ∀ x ∈ V, IsNonsingular121 V₁ V₂ β x → f x + (n - 1) = k := by
    intro x hx hns
    have hx1 : x ≠ 1 := fun h => (not_mem_of_nonsingular hyp hβ hns).1 (h ▸ V₁.one_mem)
    have hCM := h1211 G T L V V₁ V₂ n β hyp hβ x hx hns
    have hos := card_eq_card_inf_centralizer_mul (Subgroup.normalizer (L : Set G)) x
    rw [inf_eq_right.mpr hCM] at hos
    have horb3 : Nat.card {y : G // ∃ m ∈ Subgroup.normalizer (L : Set G), m * x * m⁻¹ = y} =
        Nat.card {y : G // y ∈ V ∧ IsNonsingular121 V₁ V₂ β y} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
      constructor
      · rintro ⟨m, hm, rfl⟩
        have hyV : m * x * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hMV hm) x).mp hx
        have hy1 : m * x * m⁻¹ ≠ 1 := fun h => hx1 (by
          have := congrArg (fun z => m⁻¹ * z * m) h
          simpa [mul_assoc] using this)
        exact ⟨hyV, ((horb x hx _ hyV hx1 hy1).mp ⟨m, hm, rfl⟩).2.mp hns⟩
      · rintro ⟨hyV, hyns⟩
        have hy1 : y ≠ 1 := fun h => (not_mem_of_nonsingular hyp hβ hyns).1 (h ▸ V₁.one_mem)
        have h1 := not_mem_of_nonsingular hyp hβ hns
        have h2 := not_mem_of_nonsingular hyp hβ hyns
        exact (horb x hx y hyV hx1 hy1).mpr
          ⟨iff_of_false (fun h => h.elim h1.1 h1.2) (fun h => h.elim h2.1 h2.2),
            iff_of_true hns hyns⟩
    rw [horb3] at hos
    have hO3 := two_mul_card_nonsingular hyp hβ
    rw [hcard₁, hcard₂] at hO3
    have h2n : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    have hpos : 0 < (2 ^ n - 1) * 2 ^ n := Nat.mul_pos (by omega) (by positivity)
    have hO3ne : Nat.card {y : G // y ∈ V ∧ IsNonsingular121 V₁ V₂ β y} ≠ 0 := by
      intro h
      rw [h, mul_zero] at hO3
      omega
    have hodd : ¬ 2 ∣ 2 ^ n - 1 := by
      intro h
      have h3 := Nat.dvd_sub (dvd_pow_self 2 (by omega : n ≠ 0)) h
      rw [Nat.sub_sub_self h2n.le] at h3
      exact absurd h3 (by norm_num)
    have hv2O3 : padicValNat 2 (Nat.card {y : G // y ∈ V ∧ IsNonsingular121 V₁ V₂ β y}) =
        n - 1 := by
      have h1 : padicValNat 2 (2 * Nat.card {y : G // y ∈ V ∧ IsNonsingular121 V₁ V₂ β y}) =
          n := by
        rw [hO3, padicValNat.mul (by omega) (by positivity), padicValNat.prime_pow,
          padicValNat.eq_zero_of_not_dvd hodd, zero_add]
      rw [padicValNat.mul (by norm_num) hO3ne, padicValNat_self] at h1
      omega
    have h3 := congrArg (padicValNat 2) hos
    rw [hM, padicValNat.mul Nat.card_pos.ne' hO3ne, hv2O3] at h3
    simp only [hf]
    omega
  obtain ⟨z, hzV, hz1, hzT⟩ := exists_ne_one_mem_centralizer hyp.sylow.1 hVT (hTL.trans hMV)
    (Sec121Thm.ne_bot_of_hyp121 hyp)
  have hfz : f z = k := by
    refine le_antisymm (hfle z) ?_
    have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzT t ht
    have h1 := Subgroup.card_dvd_of_le hTz
    rw [hk] at h1
    exact (padicValNat_dvd_iff_le Nat.card_pos.ne').mp h1
  have hz₁ : ¬ (z ∈ V₁ ∨ z ∈ V₂) := by
    intro h1
    have hns : ¬ IsNonsingular121 V₁ V₂ β z := fun h =>
      h1.elim (not_mem_of_nonsingular hyp hβ h).1 (not_mem_of_nonsingular hyp hβ h).2
    obtain ⟨m, -, hm⟩ := (horb v₁ (hV₁V hv₁mem.1) z hzV hv₁1 hz1).mpr
      ⟨iff_of_true (Or.inl hv₁mem.1) h1, iff_of_false hns₁ hns⟩
    have h2 := hfconj m v₁
    rw [hm] at h2
    omega
  have hz₃ : ¬ IsNonsingular121 V₁ V₂ β z := fun h => by
    have := hf₃ z hzV h
    omega
  set ty : G → ℕ := fun x => if (x ∈ V₁ ∨ x ∈ V₂) then 1 else
    if IsNonsingular121 V₁ V₂ β x then n - 1 else 0 with hty
  have hval : ∀ x ∈ V, x ≠ 1 → f x + ty x = k := by
    intro x hx hx1
    by_cases h1 : x ∈ V₁ ∨ x ∈ V₂
    · simp only [hty, h1, ↓reduceIte]
      have hns : ¬ IsNonsingular121 V₁ V₂ β x := fun h =>
        h1.elim (not_mem_of_nonsingular hyp hβ h).1 (not_mem_of_nonsingular hyp hβ h).2
      obtain ⟨m, -, hm⟩ := (horb v₁ (hV₁V hv₁mem.1) x hx hv₁1 hx1).mpr
        ⟨iff_of_true (Or.inl hv₁mem.1) h1, iff_of_false hns₁ hns⟩
      rw [← hm, hfconj]
      exact hfv₁
    · by_cases h3 : IsNonsingular121 V₁ V₂ β x
      · simp only [hty, h1, h3, ↓reduceIte]
        exact hf₃ x hx h3
      · simp only [hty, h1, h3, ↓reduceIte, add_zero]
        obtain ⟨m, -, hm⟩ := (horb z hzV x hx hz1 hx1).mpr
          ⟨iff_of_false hz₁ h1, iff_of_false hz₃ h3⟩
        rw [← hm, hfconj]
        exact hfz
  have hP₁ : ∀ x, (x ∈ V₁ ∨ x ∈ V₂) ↔ ty x = 1 := by
    intro x
    by_cases h1 : x ∈ V₁ ∨ x ∈ V₂
    · simp only [hty, h1, ↓reduceIte]
    · by_cases h3 : IsNonsingular121 V₁ V₂ β x
      · simp only [hty, h1, h3, ↓reduceIte, false_iff]
        omega
      · simp only [hty, h1, h3, ↓reduceIte, false_iff]
        omega
  have hP₃ : ∀ x, IsNonsingular121 V₁ V₂ β x ↔ ty x = n - 1 := by
    intro x
    by_cases h1 : x ∈ V₁ ∨ x ∈ V₂
    · have hns : ¬ IsNonsingular121 V₁ V₂ β x := fun h =>
        h1.elim (not_mem_of_nonsingular hyp hβ h).1 (not_mem_of_nonsingular hyp hβ h).2
      simp only [hty, h1, hns, ↓reduceIte, false_iff]
      omega
    · by_cases h3 : IsNonsingular121 V₁ V₂ β x
      · simp only [hty, h1, h3, ↓reduceIte]
      · simp only [hty, h1, h3, ↓reduceIte, false_iff]
        omega
  have hw1 : w ≠ 1 := fun h => hv1 (by
    rw [← hg] at h
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this)
  have hfvw : f w = f v := by rw [← hg]; exact hfconj g v
  have h1 := hval v hv hv1
  have h2 := hval w hw hw1
  have htv : ty v = ty w := by omega
  refine (horb v hv w hw hv1 hw1).mpr ⟨?_, ?_⟩
  · rw [hP₁, hP₁, htv]
  · rw [hP₃, hP₃, htv]

end Two

end Sec1215

theorem lem1215_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1211 : Lem1211) (h1213 : Lem1213)
    (h1214 : Lem1214) (hH91 : LemH91) : Lem1215 := by
  intro G _ _ T L V V₁ V₂ n hyp
  have hone := Sec1215.lem1215_one h1001 h331 h1213 h1214 hyp
  exact ⟨hone, fun v hv w hw hv1 g hg =>
    Sec1215.lem1215_two h1001 h331 h1211 hH91 hyp hone hv hw hv1 hg⟩

end CFSG.Quasithin.H13
