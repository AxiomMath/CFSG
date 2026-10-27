module

public import CFSG.Quasithin.EmptyFaithful.S153DGen3
public import CFSG.Quasithin.Vol2.Ch11SecCB213
public import CFSG.Quasithin.Vol2.Ch12Sec6L16a
public import CFSG.Quasithin.Vol2.Ch12Sec6L69

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

theorem sub_swap_cases : ∀ f : Fin 8 → ZMod 2,
    (fun i => f i - f (Equiv.swap (0 : Fin 8) 1 i)) = 0 ∨
      (fun i => f i - f (Equiv.swap (0 : Fin 8) 1 i)) = B5FinS8.pv 0 1 := by
  decide +kernel

theorem core_comm_swap (c : ↥(coreMod 8)) :
    c * (coreAct 8 (Equiv.swap 0 1) c)⁻¹ = 1 ∨ c * (coreAct 8 (Equiv.swap 0 1) c)⁻¹ = pe 0 1 := by
  have hcoe : ∀ i, Multiplicative.toAdd
      ((c * (coreAct 8 (Equiv.swap 0 1) c)⁻¹ : ↥(coreMod 8)) : PermMod 8) i =
      Multiplicative.toAdd (c : PermMod 8) i -
        Multiplicative.toAdd (c : PermMod 8) (Equiv.swap (0 : Fin 8) 1 i) := by
    intro i
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coreAct_coe, toAdd_mul, toAdd_inv,
      Pi.add_apply, Pi.neg_apply, permAct_apply, Equiv.swap_inv]
    ring
  rcases sub_swap_cases (Multiplicative.toAdd (c : PermMod 8)) with h | h
  · left
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    rw [hcoe i]
    exact congrFun h i
  · right
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    rw [hcoe i]
    exact congrFun h i

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem comm_eq_of_actsAs_swap {F : Frame126 T L V} (E : S126FE.Frame126E F) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hx : ActsAs F x (Equiv.swap 0 1)) {u : G} (hu : u ∈ V) :
    u * x * u⁻¹ * x⁻¹ = 1 ∨ u * x * u⁻¹ * x⁻¹ = ((E.γ.symm (pe 0 1) : ↥V) : G) := by
  have hy : x * u⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxV _).1 (V.inv_mem hu)
  have hγ := E.act x hxL hxV _ hx ⟨u⁻¹, V.inv_mem hu⟩ ⟨_, hy⟩ rfl
  have hγu : E.γ ⟨u⁻¹, V.inv_mem hu⟩ = (E.γ ⟨u, hu⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  have hcomm : u * x * u⁻¹ * x⁻¹ = ((⟨u, hu⟩ * ⟨_, hy⟩ : ↥V) : G) := by
    simp only [Subgroup.coe_mul]
    group
  have hγc : E.γ (⟨u, hu⟩ * ⟨_, hy⟩) =
      E.γ ⟨u, hu⟩ * (coreAct 8 (Equiv.swap 0 1) (E.γ ⟨u, hu⟩))⁻¹ := by
    rw [map_mul, hγ, hγu, map_inv]
  rcases core_comm_swap (E.γ ⟨u, hu⟩) with h | h
  · left
    have : (⟨u, hu⟩ * ⟨_, hy⟩ : ↥V) = 1 := E.γ.injective (by rw [hγc, h, map_one])
    rw [hcomm, this]
    rfl
  · right
    rw [hcomm]
    congr 1
    apply E.γ.injective
    rw [hγc, h, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem gamma_eq_pe (F : Frame126 T L V) (E : S126FE.Frame126E F) {v : G} (hv : v ∈ V)
    (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hw : wt ((E.γ ⟨v, hv⟩ : ↥(coreMod 8)) : PermMod 8) = 2) : E.γ ⟨v, hv⟩ = pe 0 1 := by
  rw [E.β_eq] at hβ
  have h1 : (QuotientGroup.mk ((pe 0 1)⁻¹ * E.γ ⟨v, hv⟩) : D8) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hβ, inv_mul_cancel]
  rcases (S126FE.mk_eq_one_iff _).1 h1 with h | h
  · exact (inv_mul_eq_one.1 h).symm
  · exfalso
    have h2 : E.γ ⟨v, hv⟩ = pe 0 1 * S126FE.eOm := by
      rw [← h]
      group
    rw [h2] at hw
    exact absurd hw (by decide)

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_normalizer_commutator_of_le {X H K : Subgroup G}
    (hH : X ≤ Subgroup.normalizer (H : Set G)) (hK : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hH hx),
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hK hx)]

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_normalizer_sup_of_le {X A B : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hA hx),
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hB hx)]

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_normalizer_of_commutator_le {W K : Subgroup G} (h : ⁅W, K⁆ ≤ W) :
    K ≤ Subgroup.normalizer (W : Set G) := by
  have key : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
    intro k hk w hw
    have h1 : w * k * w⁻¹ * k⁻¹ ∈ W := by
      have := h (Subgroup.commutator_mem_commutator hw hk)
      rwa [commutatorElement_def] at this
    have e : k * w * k⁻¹ = (w * k * w⁻¹ * k⁻¹)⁻¹ * w := by group
    rw [e]
    exact W.mul_mem (W.inv_mem h1) hw
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨key k hk w, fun hw => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hw
  simpa [mul_assoc] using this

omit [Finite G] [IsMulCommutative ↥V] in
theorem eq_one_or_eq_of_mem_zpowers {e y : G} (he : e * e = 1)
    (hy : y ∈ Subgroup.zpowers e) : y = 1 ∨ y = e := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he]
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [_root_.zpow_mul, h2, _root_.one_zpow]
  · right
    rw [_root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow, one_mul, zpow_one]

omit [IsMulCommutative ↥V] in
theorem normalizer_le_M (h331 : Stmt3_3_1) (hH : Hyp126 G T L V) {W : Subgroup G}
    (hW1 : W ≠ ⊥) (hW2 : IsPGroup 2 ↥W) (hLT : L ⊔ T ≤ Subgroup.normalizer (W : Set G)) :
    Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hyp := hH.hyp
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (⟨W, hW1, hW2, rfl⟩ : IsTwoLocal _)
  rw [← huniq M' hM' (hLT.trans hle)]
  exact hle

omit [IsMulCommutative ↥V] in
theorem V_le_Qv (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) : V ≤ Qv T V := by
  obtain ⟨hVT, hVe⟩ := V_facts h1222 hH
  exact fun x hx => ⟨hVT hx, Subgroup.mem_centralizer_iff.2 fun w hw =>
    (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩ |> congrArg Subtype.val).symm⟩

omit [IsMulCommutative ↥V] in
theorem normalizer_Qv_le_M (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    Subgroup.normalizer (Qv T V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  normalizer_le_M h331 hH
    (fun h => hH.hyp.irrPlus.2.1 (le_bot_iff.1 (h ▸ V_le_Qv h1222 hH)))
    (hH.hyp.sylow.1.to_le inf_le_left) (LT_le_normalizer_Qv h1222 hH)

theorem Rv_le_centralizerSection (hD2 : Lemma12_6_4_5) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    Rv T L v ≤ centralizerSection (L ⊔ T) (Lv L v) (pCoreOf 2 (Lv L v)) := by
  obtain ⟨-, hRvR, -, -, -, -, hRN, hcommR, -⟩ := hD2 G T L V F v Kv S hC
  have hRvRs : Rv T L v ≤ Rsec L Kv S v := hRvR ▸ inf_le_left
  intro r hr
  have hrR := hRvRs hr
  refine ⟨((pCoreOf_le 2 _).trans inf_le_left) hr, hRN hrR,
    normalizer_le_normalizer_pCoreOf 2 _ (hRN hrR), fun x hx => ?_⟩
  have := hcommR (Subgroup.commutator_mem_commutator hx hrR)
  rwa [commutatorElement_def] at this

theorem comm_le_zpowers (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (E : S126FE.Frame126E F) {v : G} (hv : v ∈ V)
    (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {X : Subgroup G}
    (hX : X ≤ centralizerSection (L ⊔ T) (Lv L v) (pCoreOf 2 (Lv L v))) :
    ⁅V, X⁆ ≤ Subgroup.zpowers ((E.γ.symm (pe 0 1) : ↥V) : G) := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  rw [Subgroup.commutator_le]
  intro u hu x hx
  have hxX : x ∈ L ⊔ T := (hX hx).1
  obtain ⟨σ, hσ, rfl | rfl⟩ := actsAs_of_mem_centralizerSection h1222 F hH hv hβ (hX hx)
  · have hxC := mem_centralizer_of_actsAs_one F hVL hLV (hXL hxX) (hXV hxX) hσ
    have h1 : ⁅u, x⁆ = 1 := by
      rw [commutatorElement_def, Subgroup.mem_centralizer_iff.1 hxC u hu]
      group
    rw [h1]
    exact Subgroup.one_mem _
  · rw [commutatorElement_def]
    rcases comm_eq_of_actsAs_swap E (hXL hxX) (hXV hxX) hσ hu with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_comm_comm_of_perfect {Q K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅Q, K⁆ ≤ ⁅⁅Q, K⁆, K⁆ := by
  have hKN : K ≤ Subgroup.normalizer ((⁅⁅Q, K⁆, K⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le (le_normalizer_commutator_of_le hKQ Subgroup.le_normalizer)
      Subgroup.le_normalizer
  have hQN : Q ≤ Subgroup.normalizer ((⁅⁅Q, K⁆, K⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le (le_normalizer_commutator_of_le Subgroup.le_normalizer hQK) hQK
  have h := S153D.commutator_commutator_le_of_rotate (N := ⁅⁅Q, K⁆, K⁆) (A := K) (B := K)
    (C := Q) hKN hKN hQN (le_of_eq (by rw [Subgroup.commutator_comm K Q])) le_rfl
  rwa [hK, Subgroup.commutator_comm K Q] at h

omit [IsMulCommutative ↥V] in
theorem comm_Qv_L_le_V (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V)
    (hL : CFSG.QuasithinUnique.IsShort2 L) : ⁅Qv T V, L⁆ ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have hLp : ⁅L, L⁆ = L := perfect_of_mem_cComp hyp.maximal.1.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hVQ := V_le_Qv h1222 hH
  have hQL : Qv T V ≤ Subgroup.normalizer (L : Set G) := inf_le_left.trans hyp.normalizes
  have hLQ : L ≤ Subgroup.normalizer (Qv T V : Set G) :=
    le_sup_left.trans (LT_le_normalizer_Qv h1222 hH)
  have hQ2 : IsPGroup 2 ↥(Qv T V) := hyp.sylow.1.to_le inf_le_left
  have hCQ : ⁅Qv T V, L⁆ ≤ Qv T V := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    have h1 : l * q⁻¹ * l⁻¹ ∈ Qv T V := (Subgroup.mem_normalizer_iff.1 (hLQ hl) _).1 (inv_mem hq)
    have e : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hq h1
  have hCL : ⁅Qv T V, L⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    have h1 : q * l * q⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hQL hq) _).1 hl
    rw [commutatorElement_def]
    exact mul_mem h1 (inv_mem hl)
  have hCO : ⁅Qv T V, L⁆ ≤ CFSG.QuasithinUnique.blockQ L :=
    le_pCoreOf_of_le_normalizer 2 hCL
      (le_normalizer_commutator_of_le hLQ Subgroup.le_normalizer) (hQ2.to_le hCQ)
  have hCU : ⁅Qv T V, L⁆ ≤ CFSG.QuasithinUnique.blockU L :=
    (le_comm_comm_of_perfect hLp hQL hLQ).trans (Subgroup.commutator_mono hCO le_rfl)
  have hVU : V ≤ CFSG.QuasithinUnique.blockU L :=
    calc V = ⁅V, L⁆ := hVL.symm
      _ ≤ ⁅Qv T V, L⁆ := Subgroup.commutator_mono hVQ le_rfl
      _ ≤ _ := hCU
  have hLQL : L ≤ Subgroup.normalizer (CFSG.QuasithinUnique.blockQ L : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L)
  have hLU : L ≤ Subgroup.normalizer (CFSG.QuasithinUnique.blockU L : Set G) :=
    le_normalizer_commutator_of_le hLQL Subgroup.le_normalizer
  have hLZ : L ≤ Subgroup.normalizer (CFSG.QuasithinUnique.blockZ L : Set G) :=
    B2F.le_normalizer_inf hLU (B2F.le_normalizer_centralizer Subgroup.le_normalizer)
  have hUL : CFSG.QuasithinUnique.blockU L ≤ L :=
    (Subgroup.commutator_mono (pCoreOf_le 2 L) le_rfl).trans hLp.le
  have hVZ : V ⊔ CFSG.QuasithinUnique.blockZ L = CFSG.QuasithinUnique.blockU L := by
    rcases hL.2.2.2.2.2 _ le_sup_right (sup_le hVU inf_le_left) (le_normalizer_sup_of_le hLV hLZ)
      with h | h
    · exfalso
      have hVc : V ≤ Subgroup.centralizer (L : Set G) :=
        (le_sup_left.trans h.le).trans inf_le_right
      exact hV1 (hVL ▸ Subgroup.commutator_eq_bot_iff_le_centralizer.2 hVc)
    · exact h
  have hUC : ⁅CFSG.QuasithinUnique.blockU L, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    rw [← hVZ] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer
      ((inf_le_left.trans hUL).trans hLV) hu
    have hbl : l * b = b * l := Subgroup.mem_centralizer_iff.1 hb.2 l hl
    have e : ⁅a * b, l⁆ = ⁅a, l⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc a * b * l * (a * b)⁻¹ * l⁻¹ = a * (b * l) * b⁻¹ * a⁻¹ * l⁻¹ := by group
        _ = a * (l * b) * b⁻¹ * a⁻¹ * l⁻¹ := by rw [hbl]
        _ = a * l * a⁻¹ * l⁻¹ := by group
    rw [e, ← hVL]
    exact Subgroup.commutator_mem_commutator ha hl
  calc ⁅Qv T V, L⁆ ≤ ⁅⁅Qv T V, L⁆, L⁆ := le_comm_comm_of_perfect hLp hQL hLQ
    _ ≤ ⁅CFSG.QuasithinUnique.blockU L, L⁆ := Subgroup.commutator_mono hCU le_rfl
    _ ≤ V := hUC

theorem sup_le_sup_Rv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) {r : G} (hr : r ∈ Rv T L v) (hrσ : ActsAs F r (Equiv.swap 0 1)) :
    L ⊔ T ≤ L ⊔ Rv T L v := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hrX : r ∈ L ⊔ T := ((pCoreOf_le 2 _).trans inf_le_left) hr
  have key : ∀ y ∈ L ⊔ T, ∀ σ : Equiv.Perm (Fin 8), ActsAs F y σ →
      σ ∈ alternatingGroup (Fin 8) → y ∈ L ⊔ Rv T L v := by
    intro y hy σ hσ hσA
    obtain ⟨l, hl⟩ := S126L19a.psi_surjective F hH ⟨σ, hσA⟩
    have hlσ : psiP F hH l = σ := congrArg Subtype.val hl
    have hl1 : ActsAs F ((l : G)⁻¹ * y) 1 := by
      have := (actsAs_psiP F hH l).inv.mul hσ (hXV hy)
      rwa [hlσ, inv_mul_cancel] at this
    have hlyX : (l : G)⁻¹ * y ∈ L ⊔ T :=
      (L ⊔ T).mul_mem ((le_sup_left : L ≤ L ⊔ T) (L.inv_mem l.2)) hy
    have hlyQ : (l : G)⁻¹ * y ∈ Qv T V := by
      rw [Qv_eq h1222 hH]
      exact ⟨hlyX, mem_centralizer_of_actsAs_one F hVL hLV (hXL hlyX) (hXV hlyX) hl1⟩
    have e : y = l * ((l : G)⁻¹ * y) := by group
    rw [e]
    exact (L ⊔ Rv T L v).mul_mem ((le_sup_left : L ≤ L ⊔ Rv T L v) l.2)
      ((le_sup_right : Rv T L v ≤ L ⊔ Rv T L v) (Qv_le_Rv h1222 hH hv hlyQ))
  intro y hy
  obtain ⟨σ, hσ⟩ := exists_actsAs F hH (hXL hy) (hXV hy)
  by_cases hs : σ ∈ alternatingGroup (Fin 8)
  · exact key y hy σ hσ hs
  · have hσr : σ * Equiv.swap 0 1 ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup] at hs ⊢
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide)]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact absurd h hs
      · rw [h]
        decide
    have hyr := key (y * r) ((L ⊔ T).mul_mem hy hrX) _ (hσ.mul hrσ (hXV hrX)) hσr
    have e : y = y * r * r⁻¹ := by group
    rw [e]
    exact (L ⊔ Rv T L v).mul_mem hyr ((le_sup_right : Rv T L v ≤ L ⊔ Rv T L v) (inv_mem hr))

theorem not_le_Gv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) : ¬ L ≤ Gv v := by
  intro hLv
  have hσA : Equiv.swap (0 : Fin 8) 2 * Equiv.swap 0 1 ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  obtain ⟨l, hl⟩ := S126L19a.psi_surjective F hH ⟨_, hσA⟩
  have hact : ActsAs F l (Equiv.swap (0 : Fin 8) 2 * Equiv.swap 0 1) := by
    have := actsAs_psiP F hH l
    rwa [show psiP F hH l = Equiv.swap (0 : Fin 8) 2 * Equiv.swap 0 1 from
      congrArg Subtype.val hl] at this
  have h := (mem_Gv_iff h1222 F hH hv hβ (Subgroup.le_normalizer l.2)
    (hH.hyp.irrPlus.2.2.1 l.2) hact).1 (hLv l.2)
  revert h
  decide

end S126T2

end CFSG.Quasithin.H13
