module

public import CFSG.Quasithin.Vol2.Ch12Sec6L19b
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 S126L19a S126L19b Equiv
open scoped IsMulCommutative

namespace S126L19c

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

@[expose] noncomputable def Tbar (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    Subgroup ↥(alternatingGroup (Fin 8)) :=
  ((T ⊓ L).subgroupOf L).map (psi F hH)

theorem card_Tbar (F : Frame126 T L V) (hH : Hyp126 G T L V) : Nat.card (Tbar F hH) = 2 ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have hsylTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow (le_sup_right : T ≤ L ⊔ T)) le_sup_left
      (sup_le Subgroup.le_normalizer hyp.normalizes)
  have hp : IsPGroup 2 (Tbar F hH) := by
    have h1 : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
      hsylTL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsylTL.1).symm
    exact h1.map _
  have hidx : ¬ 2 ∣ (Tbar F hH).index := by
    intro h2
    apply hsylTL.2.2
    have h1 := Subgroup.index_map ((T ⊓ L).subgroupOf L) (psi F hH)
    rw [MonoidHom.range_eq_top.2 (psi_surjective F hH), Subgroup.index_top, mul_one] at h1
    have h3 : (((T ⊓ L).subgroupOf L) ⊔ (psi F hH).ker).index ∣
        ((T ⊓ L).subgroupOf L).index := Subgroup.index_dvd_of_le le_sup_left
    change 2 ∣ ((T ⊓ L).subgroupOf L).index
    rw [Tbar, h1] at h2
    exact h2.trans h3
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (Tbar F hH) ⊤ :=
    ⟨le_top, hp, by
      have h := Subgroup.relIndex_top_right (Tbar F hH)
      change ¬ 2 ∣ (Tbar F hH).relIndex ⊤
      rwa [h]⟩
  exact card_of_isSylowTwoOf hS (m := 315)
    (by rw [Subgroup.card_top, card_A8]; norm_num) (by decide)

omit [IsMulCommutative ↥V] in
theorem exists_conjSub_le {M X : Subgroup G} (hT : quasithinIsSylowTwo T) (hTM : T ≤ M)
    (hXM : X ≤ M) (hX : IsPGroup 2 X) : ∃ m ∈ M, B6.conjSub m X ≤ T := by
  obtain ⟨m, hm, hmX⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_conj_mem_of_isPGroup hTM hT.1
    (isSylowTwoOf_of_quasithinIsSylowTwo hT hTM).2.2 hXM hX
  refine ⟨m, hm, fun y hy => ?_⟩
  rw [B6.mem_conjSub] at hy
  have := hmX _ hy
  rwa [show m * (m⁻¹ * y * m) * m⁻¹ = y by group] at this

omit [Finite G] [IsMulCommutative ↥V] in
theorem conjSub_le_of_mem {H K : Subgroup G} {g : G} (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (hHK : H ≤ K) : B6.conjSub g H ≤ K := by
  intro y hy
  rw [B6.mem_conjSub] at hy
  have := (Subgroup.mem_normalizer_iff.1 hgK _).1 (hHK hy)
  rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this

omit [Finite G] [IsMulCommutative ↥V] in
theorem conjSub_normalizer {H K : Subgroup G} (g : G)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    B6.conjSub g H ≤ Subgroup.normalizer (B6.conjSub g K : Set G) := by
  intro y hy
  rw [B6.mem_conjSub] at hy
  rw [Subgroup.mem_normalizer_iff]
  intro k
  rw [B6.mem_conjSub, B6.mem_conjSub]
  have h := Subgroup.mem_normalizer_iff.1 (hHK hy) (g⁻¹ * k * g)
  rw [show g⁻¹ * y * g * (g⁻¹ * k * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * k * y⁻¹) * g by group] at h
  exact h

omit [Finite G] [IsMulCommutative ↥V] in
theorem conjSub_le_normalizer_of_mem {H K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    B6.conjSub g H ≤ Subgroup.normalizer (K : Set G) := by
  have h := conjSub_normalizer g hHK
  rwa [B6.conjSub_eq_self hg] at h

theorem card_image_ge (F : Frame126 T L V) (hH : Hyp126 G T L V) {X : Subgroup G} (hXT : X ≤ T)
    (h2 : X.relIndex T = 2) : 32 ≤ Nat.card (((X ⊓ L).subgroupOf L).map (psi F hH)) := by
  have hc1 := card_eq F hH (inf_le_right : X ⊓ L ≤ L)
  have hc2 := card_eq F hH (inf_le_right : T ⊓ L ≤ L)
  change Nat.card ↥(T ⊓ L) = Nat.card (Tbar F hH) * _ at hc2
  rw [card_Tbar] at hc2
  have hidx : (X ⊓ L).relIndex (T ⊓ L) ≤ 2 := by
    have e : X ⊓ L = X ⊓ (T ⊓ L) := by
      rw [← inf_assoc, inf_of_le_left hXT]
    rw [e]
    calc (X ⊓ (T ⊓ L)).relIndex (T ⊓ L) ≤ X.relIndex (T ⊓ L) * (T ⊓ L).relIndex (T ⊓ L) :=
          Subgroup.relIndex_inf_le
      _ = X.relIndex (T ⊓ L) := by rw [Subgroup.relIndex_self, mul_one]
      _ ≤ X.relIndex T := Subgroup.relIndex_le_of_le_right inf_le_left (by rw [h2]; norm_num)
      _ = 2 := h2
  have hrc := Subgroup.relIndex_mul_card (X ⊓ L) (T ⊓ L)
  have hinf : X ⊓ L ⊓ (T ⊓ L) = X ⊓ L :=
    inf_of_le_left (le_inf (inf_le_left.trans hXT) inf_le_right)
  rw [hinf] at hrc
  have hTX : Nat.card ↥(T ⊓ L) ≤ 2 * Nat.card ↥(X ⊓ L) := by
    rw [← hrc]
    exact Nat.mul_le_mul_right _ hidx
  have hCC : Nat.card ↥(X ⊓ L ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card ↥(T ⊓ L ⊓ Subgroup.centralizer (V : Set G)) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ (inf_le_inf_right _ hXT))
  have hpos : 0 < Nat.card ↥(T ⊓ L ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  rw [hc2, hc1] at hTX
  have h3 : 2 ^ 6 * Nat.card ↥(T ⊓ L ⊓ Subgroup.centralizer (V : Set G)) ≤
      2 * Nat.card (((X ⊓ L).subgroupOf L).map (psi F hH)) *
        Nat.card ↥(T ⊓ L ⊓ Subgroup.centralizer (V : Set G)) :=
    hTX.trans (by rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hCC))
  have h4 := Nat.le_of_mul_le_mul_right h3 hpos
  omega

theorem image_le_normalizer (F : Frame126 T L V) (hH : Hyp126 G T L V) {X Y : Subgroup G}
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    (((X.subgroupOf L).map (psi F hH)).map (alternatingGroup (Fin 8)).subtype) ≤
      Subgroup.normalizer ((((Y.subgroupOf L).map (psi F hH)).map
        (alternatingGroup (Fin 8)).subtype : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) := by
  have h1 : X.subgroupOf L ≤ Subgroup.normalizer ((Y.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hXY hx) y
  have h2 := (Subgroup.map_mono (f := psi F hH) h1).trans (Subgroup.le_normalizer_map _)
  exact (Subgroup.map_mono h2).trans (Subgroup.le_normalizer_map _)

theorem mem_eset {S : Finset (Fin 8)} (i : Fin 8) :
    Multiplicative.toAdd (eset S) i = if i ∈ S then 1 else 0 := rfl

theorem wt_eset (S : Finset (Fin 8)) : wt (eset S) = S.card := by
  unfold wt
  congr 1
  ext i
  rw [Finset.mem_filter, mem_eset]
  by_cases h : i ∈ S <;> simp [h]

omit [Finite G] in
theorem conjSub_L1_le (F : Frame126 T L V) {k : G}
    (hk : B6.conjSub k (Li L F.V1) ≤ L ⊓ Subgroup.normalizer (F.V1 : Set G)) :
    B6.conjSub k (Li L F.V1) ≤ Li L F.V1 := by
  change (Li L F.V1).map (MulAut.conj k).toMonoidHom ≤ Li L F.V1
  rw [Subgroup.map_le_iff_le_comap]
  conv_lhs => rw [L1_eq F]
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  obtain ⟨hxLN, m, hm, hxm⟩ := hx
  have hxL1 : x ∈ Li L F.V1 := Subgroup.subset_closure ⟨hxLN, m, hm, hxm⟩
  have h1 : k * x * k⁻¹ ∈ B6.conjSub k (Li L F.V1) := by
    rw [B6.mem_conjSub]
    simpa [mul_assoc] using hxL1
  refine Subgroup.subset_closure ⟨hk h1, m, hm, ?_⟩
  change (k * x * k⁻¹) ^ m = 1
  rw [conj_pow, hxm]
  group

theorem exists_eq_conjSub (F : Frame126 T L V) (hH : Hyp126 G T L V) {h : G}
    (hYL : B6.conjSub h (Li L F.V1) ≤ L) {S : Finset (Fin 8)} (hS4 : S.card = 4)
    (hS : ∀ y ∈ (((B6.conjSub h (Li L F.V1)).subgroupOf L).map (psi F hH)).map
      (alternatingGroup (Fin 8)).subtype, (∀ i, y i ∈ S ↔ i ∈ S) ∨ (∀ i, y i ∈ S ↔ i ∉ S)) :
    ∃ l ∈ L, B6.conjSub h (Li L F.V1) = B6.conjSub l (Li L F.V1) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  obtain ⟨σ₀, hσ₀⟩ := exists_perm (x := eset {0, 1, 2, 3}) (y := eset S) (k := 4) (by norm_num)
    (by rw [wt_eset]; rfl) (by rw [wt_eset, hS4])
  have hσ₀S : ∀ i, (σ₀ : Perm (Fin 8)) i ∈ S ↔ i.val < 4 := by
    intro i
    have h1 := congrArg (fun x : PermMod 8 => (Multiplicative.toAdd x : Fin 8 → ZMod 2)
      ((σ₀ : Perm (Fin 8)) i)) hσ₀
    simp only [permAct_apply, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply, mem_eset] at h1
    rw [← mem_0123]
    by_cases ha : i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) <;>
      by_cases hb : (σ₀ : Perm (Fin 8)) i ∈ S <;> simp_all
  obtain ⟨l₀, hl₀, hl₀L, hl₀a⟩ := mem_autOn_iff_exists.mp (F.π σ₀).2
  have hl₀act : ActsAs F l₀ σ₀ := actsAs_of_pi F hl₀ σ₀ hl₀a
  have hk : B6.conjSub (l₀⁻¹ * h) (Li L F.V1) ≤ L ⊓ Subgroup.normalizer (F.V1 : Set G) := by
    intro y hy
    rw [B6.conjSub_mul] at hy
    rw [B6.mem_conjSub, inv_inv] at hy
    have hyL : l₀ * y * l₀⁻¹ ∈ L := hYL hy
    have hyL' : y ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem hl₀L) hyL) hl₀L
      rwa [show l₀⁻¹ * (l₀ * y * l₀⁻¹) * l₀ = y by group] at this
    refine ⟨hyL', ?_⟩
    set τ : Perm (Fin 8) := (psi F hH ⟨_, hyL⟩ : Perm (Fin 8)) with hτ
    have hτS := hS τ ⟨psi F hH ⟨_, hyL⟩, ⟨⟨_, hyL⟩, hy, rfl⟩, rfl⟩
    have hact : ActsAs F y ((σ₀ : Perm (Fin 8))⁻¹ * τ * σ₀) := by
      have h1 := ((hl₀act.inv).mul (actsAs_psi F hH ⟨_, hyL⟩) (hLV hyL)).mul hl₀act hl₀
      rwa [show l₀⁻¹ * (l₀ * y * l₀⁻¹) * l₀ = y by group] at h1
    refine mem_normalizer_V1' F (hLV hyL') hact ?_
    rcases hτS with h1 | h1
    · left
      intro i
      rw [← hσ₀S i, ← h1, ← hσ₀S, Perm.mul_apply, Perm.mul_apply, S126Ex.perm_apply_inv]
    · right
      intro i
      have e1 := hσ₀S ((σ₀ : Perm (Fin 8))⁻¹ (τ ((σ₀ : Perm (Fin 8)) i)))
      rw [S126Ex.perm_apply_inv] at e1
      rw [Perm.mul_apply, Perm.mul_apply]
      have e2 := h1 ((σ₀ : Perm (Fin 8)) i)
      rw [hσ₀S] at e2
      constructor
      · intro hi
        by_contra hc
        push Not at hc
        exact (e2.1 (e1.2 hc)) hi
      · intro hi
        by_contra hc
        exact (by omega : ¬ (((σ₀ : Perm (Fin 8))⁻¹ (τ ((σ₀ : Perm (Fin 8)) i))).val < 4))
          (e1.1 (e2.2 hc))
  have hle := conjSub_L1_le F hk
  have heq : B6.conjSub (l₀⁻¹ * h) (Li L F.V1) = Li L F.V1 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [B6.card_conjSub])
  refine ⟨l₀, hl₀L, ?_⟩
  conv_rhs => rw [← heq]
  rw [← B6.conjSub_mul, mul_inv_cancel_left]

section Main

variable (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
  (h3228 : Stmt3_2_2_eight) (hA8 : FactA8SolvNormPartition) {F : Frame126 T L V}
  (E : Frame126E F) (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)

include h331 h1222 h3228 hH hZ in
theorem mem_M_of_normalizer {g : G} (hgN : g ∈ Subgroup.normalizer (Li L F.V1 : Set G))
    (hgM : B6.conjSub g (T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G)) ≤
      Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  set T4 := T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) with hT4def
  set L1 := Li L F.V1 with hL1def
  set M := Subgroup.normalizer (L : Set G) with hM
  have hTL1 : T ≤ Subgroup.normalizer (L1 : Set G) := T_le_normalizer_L1 h1222 hH
  have hXN : B6.conjSub g T4 ≤ M ⊓ Subgroup.normalizer (L1 : Set G) :=
    le_inf hgM (conjSub_le_normalizer_of_mem hgN (inf_le_left.trans hTL1))
  have hX2 : IsPGroup 2 (B6.conjSub g T4) :=
    (hyp.sylow.1.to_le inf_le_left).of_equiv
      (Subgroup.equivMapOfInjective T4 _ (MulAut.conj g).injective)
  obtain ⟨n, hnN, hn⟩ := exists_conjSub_le hyp.sylow (le_inf hyp.normalizes hTL1) hXN hX2
  set g₂ := n * g with hg₂
  have hT4' : B6.conjSub g₂ T4 ≤ T := by
    rw [hg₂, B6.conjSub_mul]
    exact hn
  have hg₂N : g₂ ∈ Subgroup.normalizer (L1 : Set G) := Subgroup.mul_mem _ hnN.2 hgN
  have hidx : (B6.conjSub g₂ T4).relIndex T = 2 := by
    have h1 := Subgroup.relIndex_mul_card (B6.conjSub g₂ T4) T
    have h2 := Subgroup.relIndex_mul_card T4 T
    rw [inf_of_le_left hT4', B6.card_conjSub] at h1
    rw [inf_of_le_left (inf_le_left : T4 ≤ T), relIndex_T4 E h1222 hH hZ] at h2
    have hpos : 0 < Nat.card T4 := Nat.card_pos
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hTN : T ≤ Subgroup.normalizer (B6.conjSub g₂ T4 : Set G) := by
    have hn2 := Subgroup.normal_of_index_eq_two (H := (B6.conjSub g₂ T4).subgroupOf T) hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hT4').1 hn2
  have hR := R1_eq E h1222 hH hZ
  have hRg : B6.conjSub g₂ (Ri T L F.V1) = pCoreOf 2 (L1 ⊔ B6.conjSub g₂ T4) := by
    rw [hR]
    change (pCoreOf 2 (L1 ⊔ T4)).map (MulAut.conj g₂).toMonoidHom = _
    rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv, Subgroup.map_sup]
    congr 2
    exact B6.conjSub_eq_self hg₂N
  have hle : B6.conjSub g₂ (Ri T L F.V1) ≤ Ri T L F.V1 := by
    rw [hRg]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_sup_left hT4' _)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    refine le_trans ?_ (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun t ht => ?_
    exact normalizer_inf_le_sup _ _ ⟨hTL1 ht, hTN ht⟩
  have heq : B6.conjSub g₂ (Ri T L F.V1) = Ri T L F.V1 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [B6.card_conjSub])
  have hg₂R : g₂ ∈ Subgroup.normalizer (Ri T L F.V1 : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 heq
  have hg₂M := (part4 h331 h1222 h3228 F hH).2 hg₂R
  have : g = n⁻¹ * g₂ := by rw [hg₂, inv_mul_cancel_left]
  rw [this]
  exact M.mul_mem (M.inv_mem hnN.1) hg₂M

include h331 h1222 h1228 h3228 hA8 hH hZ in
theorem false_of_conj {g x : G} (hgx : g * ((v4 E : ↥V) : G) * g⁻¹ = x)
    (hCx : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hxL : x ∈ Subgroup.centralizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨-, -, hMV, -⟩ := hall V hyp.irrPlus
  have hMV' : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    hMV.resolve_right hZ
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  set T4 := T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) with hT4def
  set L1 := Li L F.V1 with hL1def
  set M := Subgroup.normalizer (L : Set G) with hM
  have hTL1 : T ≤ Subgroup.normalizer (L1 : Set G) := T_le_normalizer_L1 h1222 hH
  have hYx := conj_le_centralizer (g := g) (L1_le E h1222 hH)
  have hXx := conj_le_centralizer (g := g) (show T4 ≤ Subgroup.centralizer
    ({((v4 E : ↥V) : G)} : Set G) from inf_le_right)
  rw [hgx] at hYx hXx
  have hYM : B6.conjSub g L1 ≤ M := hYx.trans hCx
  have hXM : B6.conjSub g T4 ≤ M := hXx.trans hCx
  have hYL : B6.conjSub g L1 ≤ L := conj_L1_le_L h1222 h1228 F hH hYM
  have hX2 : IsPGroup 2 (B6.conjSub g T4) :=
    (hyp.sylow.1.to_le inf_le_left).of_equiv
      (Subgroup.equivMapOfInjective T4 _ (MulAut.conj g).injective)
  obtain ⟨m, hmM, hm⟩ := exists_conjSub_le hyp.sylow hyp.normalizes hXM hX2
  set g₁ := m * g with hg₁
  have hY₁ : B6.conjSub g₁ L1 ≤ L := by
    rw [hg₁, B6.conjSub_mul]
    exact conjSub_le_of_mem hmM hYL
  have hX₁ : B6.conjSub g₁ T4 ≤ T := by
    rw [hg₁, B6.conjSub_mul]
    exact hm
  have hX₁N : B6.conjSub g₁ T4 ≤ Subgroup.normalizer (B6.conjSub g₁ L1 : Set G) :=
    conjSub_normalizer g₁ (inf_le_left.trans hTL1)
  have hidx : (B6.conjSub g₁ T4).relIndex T = 2 := by
    have h1 := Subgroup.relIndex_mul_card (B6.conjSub g₁ T4) T
    have h2 := Subgroup.relIndex_mul_card T4 T
    rw [inf_of_le_left hX₁, B6.card_conjSub] at h1
    rw [inf_of_le_left (inf_le_left : T4 ≤ T), relIndex_T4 E h1222 hH hZ] at h2
    have hpos : 0 < Nat.card T4 := Nat.card_pos
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  set Ybar : Subgroup (Perm (Fin 8)) :=
    (((B6.conjSub g₁ L1).subgroupOf L).map (psi F hH)).map (alternatingGroup (Fin 8)).subtype
    with hYbar
  set Pbar : Subgroup (Perm (Fin 8)) :=
    (((B6.conjSub g₁ T4 ⊓ L).subgroupOf L).map (psi F hH)).map (alternatingGroup (Fin 8)).subtype
    with hPbar
  have hcY : Nat.card Ybar = Nat.card (((B6.conjSub g₁ L1).subgroupOf L).map (psi F hH)) :=
    Subgroup.card_map_of_injective Subtype.val_injective
  have hcP : Nat.card Pbar = Nat.card (((B6.conjSub g₁ T4 ⊓ L).subgroupOf L).map (psi F hH)) :=
    Subgroup.card_map_of_injective Subtype.val_injective
  obtain ⟨h9, h5⟩ := card_L1 h1222 F hH
  have hcE := card_eq F hH hY₁
  obtain ⟨a, ha⟩ := card_inf_eq_pow h1222 hH hY₁
  rw [B6.card_conjSub, ha] at hcE
  have h9' : 9 ∣ Nat.card Ybar := by
    rw [hcY]
    have hc : Nat.Coprime 9 (2 ^ a) := coprime_pow_two (by decide)
    exact hc.dvd_of_dvd_mul_right (hcE ▸ h9)
  have h5' : ¬ 5 ∣ Nat.card Ybar := by
    rw [hcY]
    intro h
    exact h5 (hcE ▸ Dvd.dvd.mul_right h _)
  have h32 : 32 ≤ Nat.card Pbar := by
    rw [hcP]
    exact card_image_ge F hH hX₁ hidx
  have hP2 : IsPGroup 2 Pbar := by
    have h1 : IsPGroup 2 ((B6.conjSub g₁ T4 ⊓ L).subgroupOf L) :=
      (hyp.sylow.1.to_le (inf_le_left.trans hX₁)).of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    exact (h1.map _).map _
  have hPN : Pbar ≤ Subgroup.normalizer (Ybar : Set (Perm (Fin 8))) :=
    image_le_normalizer F hH (inf_le_left.trans hX₁N)
  obtain ⟨S, hS4, hS⟩ := hA8 Ybar Pbar (Subgroup.map_subtype_le _) h9' h5'
    (Subgroup.map_subtype_le _) hP2 h32 hPN
  obtain ⟨l, hlL, hl⟩ := exists_eq_conjSub F hH hY₁ hS4 hS
  set g' := l⁻¹ * g₁ with hg'
  have hg'N : g' ∈ Subgroup.normalizer (L1 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change B6.conjSub g' L1 = L1
    rw [hg', B6.conjSub_mul, hl, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  have hlM : l ∈ M := Subgroup.le_normalizer hlL
  have hg'M : B6.conjSub g' T4 ≤ M := by
    rw [hg', B6.conjSub_mul]
    exact conjSub_le_of_mem (Subgroup.le_normalizer (M.inv_mem hlM)) (hX₁.trans hyp.normalizes)
  have hg'M' := mem_M_of_normalizer h331 h1222 h3228 E hH hZ hg'N hg'M
  have hgM : g ∈ M := by
    have : g = m⁻¹ * (l * g') := by rw [hg', mul_inv_cancel_left, hg₁, inv_mul_cancel_left]
    rw [this]
    exact M.mul_mem (M.inv_mem hmM) (M.mul_mem hlM hg'M')
  have hgV := hMV' hgM
  obtain ⟨σ, hσ⟩ := exists_actsAs F hH hgM hgV
  have hxV : x ∈ V := by
    rw [← hgx]
    exact conj_mem hgV (v4 E)
  have h1 := hσ (v4 E) ⟨x, hxV⟩ hgx.symm
  rw [beta_v4, (F.β_ker _).2 hxL] at h1
  have h2 := congrArg (dAct σ⁻¹) h1
  rw [map_one, dAct_inv_dAct] at h2
  exact e0123_ne_one h2.symm

end Main

end S126L19c

end CFSG.Quasithin.H13
