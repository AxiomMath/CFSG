module

public import CFSG.Quasithin.Vol2.Ch12Sec6FF
public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Background.F8G2
public import CFSG.Quasithin.Vol2.Ch12Sec6Ex
public import CFSG.Quasithin.Vol2.Ch12Sec6Pm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  Equiv
open scoped IsMulCommutative

namespace S126L1b

variable {G : Type} [Group G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem comm_of_mem {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a :=
  congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)

theorem exists_actsAs_of_mem_L (F : Frame126 T L V) {l : G} (hlL : l ∈ L)
    (hl : l ∈ Subgroup.normalizer (V : Set G)) :
    ∃ σ : ↥(alternatingGroup (Fin 8)),
      conjAct V ⟨l, hl⟩ = ((F.π σ : ↥(autOn L V)) : MulAut ↥V) ∧ ActsAs F l σ := by
  have ha : conjAct V ⟨l, hl⟩ ∈ autOn L V := mem_autOn_iff_exists.mpr ⟨l, hl, hlL, rfl⟩
  obtain ⟨σ, hσ⟩ := F.π_surj ⟨_, ha⟩
  have h : conjAct V ⟨l, hl⟩ = ((F.π σ : ↥(autOn L V)) : MulAut ↥V) := by rw [hσ]
  exact ⟨σ, h, actsAs_of_pi F hl σ h⟩

theorem mem_centralizer_of_mem_L (F : Frame126 T L V) {l : G} (hlL : l ∈ L)
    (hl : l ∈ Subgroup.normalizer (V : Set G)) (h : ActsAs F l 1) :
    l ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨σ, hσ, hact⟩ := exists_actsAs_of_mem_L F hlL hl
  have h1 : σ = 1 := Subtype.ext (hact.unique h hl)
  rw [h1, map_one] at hσ
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h2 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hσ
  change l * v * l⁻¹ = v at h2
  calc v * l = l * v * l⁻¹ * l := by rw [h2]
    _ = l * v := by group

theorem mem_centralizer_of_actsAs_one (F : Frame126 T L V) (hVL : ⁅V, L⁆ = V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {t : G}
    (htL : t ∈ Subgroup.normalizer (L : Set G)) (htV : t ∈ Subgroup.normalizer (V : Set G))
    (ht : ActsAs F t 1) : t ∈ Subgroup.centralizer (V : Set G) := by
  have hc : ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro l hl
    have hlV := hLV hl
    obtain ⟨σ, -, hσ⟩ := exists_actsAs_of_mem_L F hl hlV
    have hcL : t * l * t⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.1 htL l).1 hl) (L.inv_mem hl)
    have hcV : t * l * t⁻¹ * l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htV hlV)
        (Subgroup.inv_mem _ htV)) (Subgroup.inv_mem _ hlV)
    have h1 := ht.commutator hσ htV hlV
    rw [show (1 : Perm (Fin 8)) * σ * 1⁻¹ * (σ : Perm (Fin 8))⁻¹ = 1 by group] at h1
    exact mem_centralizer_of_mem_L F hcL hcV h1
  have hf : ∀ v ∈ V, t * v * t⁻¹ * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro v hv
    have hw : t * v * t⁻¹ ∈ V := conj_mem htV ⟨v, hv⟩
    have h1 := ht ⟨v, hv⟩ ⟨t * v * t⁻¹, hw⟩ rfl
    rw [dAct_one] at h1
    have h2 : F.β (⟨t * v * t⁻¹, hw⟩ * (⟨v, hv⟩ : ↥V)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact (F.β_ker _).1 h2
  have hcomm : ∀ v ∈ V, ∀ l ∈ L, t * (v * l * v⁻¹ * l⁻¹) * t⁻¹ = v * l * v⁻¹ * l⁻¹ := by
    intro v hv l hl
    obtain ⟨f, hfdef⟩ : ∃ f, f = t * v * t⁻¹ * v⁻¹ := ⟨_, rfl⟩
    obtain ⟨c, hcdef⟩ : ∃ c, c = t * l * t⁻¹ * l⁻¹ := ⟨_, rfl⟩
    obtain ⟨w, hwdef⟩ : ∃ w, w = l * v⁻¹ * l⁻¹ := ⟨_, rfl⟩
    have hfV : f ∈ V := by
      rw [hfdef]
      exact V.mul_mem (conj_mem htV ⟨v, hv⟩) (V.inv_mem hv)
    have hfL : f ∈ Subgroup.centralizer (L : Set G) := hfdef ▸ hf v hv
    have hcV : c ∈ Subgroup.centralizer (V : Set G) := hcdef ▸ hc l hl
    have hwV : w ∈ V := by
      rw [hwdef]
      exact conj_mem (hLV hl) ⟨v⁻¹, V.inv_mem hv⟩
    have e1 : t * v * t⁻¹ = f * v := by
      rw [hfdef]
      group
    have e2 : t * l * t⁻¹ = c * l := by
      rw [hcdef]
      group
    have hlf : l * f = f * l := Subgroup.mem_centralizer_iff.1 hfL l hl
    have e3 : l * f⁻¹ * l⁻¹ = f⁻¹ := by
      calc l * f⁻¹ * l⁻¹ = f⁻¹ * (f * l) * f⁻¹ * l⁻¹ := by group
        _ = f⁻¹ * (l * f) * f⁻¹ * l⁻¹ := by rw [hlf]
        _ = f⁻¹ := by group
    have e4 : c * (w * f⁻¹) = w * f⁻¹ * c :=
      (Subgroup.mem_centralizer_iff.1 hcV _ (V.mul_mem hwV (V.inv_mem hfV))).symm
    have e5 : f * (v * w) = v * w * f := comm_of_mem hfV (V.mul_mem hv hwV)
    calc t * (v * l * v⁻¹ * l⁻¹) * t⁻¹
        = (t * v * t⁻¹) * (t * l * t⁻¹) * (t * v * t⁻¹)⁻¹ * (t * l * t⁻¹)⁻¹ := by group
      _ = f * v * (c * l) * (f * v)⁻¹ * (c * l)⁻¹ := by rw [e1, e2]
      _ = f * v * c * (l * v⁻¹ * l⁻¹) * (l * f⁻¹ * l⁻¹) * c⁻¹ := by group
      _ = f * v * (c * (w * f⁻¹)) * c⁻¹ := by rw [e3, ← hwdef]; group
      _ = f * v * (w * f⁻¹ * c) * c⁻¹ := by rw [e4]
      _ = f * (v * w) * f⁻¹ := by group
      _ = v * w := by rw [e5]; group
      _ = v * l * v⁻¹ * l⁻¹ := by rw [hwdef]; group
  have hle : ⁅V, L⁆ ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
    have h1 := hcomm v hv l hl
    symm
    calc t * (v * l * v⁻¹ * l⁻¹) = t * (v * l * v⁻¹ * l⁻¹) * t⁻¹ * t := by group
      _ = v * l * v⁻¹ * l⁻¹ * t := by rw [h1]
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := hle (hVL.symm ▸ hv : v ∈ ⁅V, L⁆)
  rw [Subgroup.mem_centralizer_singleton_iff] at h1
  exact h1

theorem mem_0123 : ∀ i : Fin 8, i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) ↔ i.val < 4 := by
  decide

theorem permAct_eset {σ : Perm (Fin 8)} (hσ : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) :
    permAct 8 σ (eset {0, 1, 2, 3}) = eset {0, 1, 2, 3} := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_apply]
  simp only [eset, toAdd_ofAdd]
  have key : σ⁻¹ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) ↔ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) := by
    have h1 := hσ (σ⁻¹ i)
    rw [S126Ex.perm_apply_inv] at h1
    rw [mem_0123, mem_0123]
    exact h1
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.1 h1) h2
  · exact absurd (key.2 h2) h1
  · rfl

theorem coreAct_X1 {σ : Perm (Fin 8)} (hσ : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4))
    {m : ↥(coreMod 8)} (hm : m ∈ X1) : coreAct 8 σ m ∈ X1 := by
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    change ((coreAct 8 σ x : ↥(coreMod 8)) : PermMod 8) = eset {0, 1, 2, 3}
    have hx' : (x : PermMod 8) = eset {0, 1, 2, 3} := hx
    rw [coreAct_coe, hx', permAct_eset hσ]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem dAct_W1 {σ : Perm (Fin 8)} (hσ : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) {y : D8}
    (hy : y ∈ W1) : dAct σ y ∈ W1 := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
  refine Subgroup.mem_map.2 ⟨coreAct 8 σ m, coreAct_X1 hσ hm, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, dAct_mk]

theorem conj_mem_V1 (F : Frame126 T L V) {g : G} {σ : Perm (Fin 8)}
    (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hg : ActsAs F g σ)
    (hσ : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) {x : G} (hx : x ∈ F.V1) :
    g * x * g⁻¹ ∈ F.V1 := by
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨⟨g * v * g⁻¹, conj_mem hgN v⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap] at hv ⊢
  rw [hg v _ rfl]
  exact dAct_W1 hσ hv

theorem mem_normalizer_V1 (F : Frame126 T L V) {g : G} {σ : Perm (Fin 8)}
    (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hg : ActsAs F g σ)
    (hσ : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) :
    g ∈ Subgroup.normalizer (F.V1 : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_V1 F hgN hg hσ, fun hx => ?_⟩
  have hσ' : ∀ i : Fin 8, (i.val < 4 ↔ (σ⁻¹ i).val < 4) := fun i => by
    have h1 := hσ (σ⁻¹ i)
    rw [S126Ex.perm_apply_inv] at h1
    exact h1.symm
  have h := conj_mem_V1 F (Subgroup.inv_mem _ hgN) hg.inv hσ' hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem exists_mem_L1 [Finite G] (F : Frame126 T L V) {c : Perm (Fin 8)}
    (hc : c ∈ alternatingGroup (Fin 8)) (hc3 : c ^ 3 = 1)
    (hcb : ∀ i : Fin 8, (i.val < 4 ↔ (c i).val < 4)) :
    ∃ l ∈ Li L F.V1, l ∈ Subgroup.normalizer (V : Set G) ∧ ActsAs F l c := by
  obtain ⟨l, hl, hlL, hla⟩ := mem_autOn_iff_exists.mp (F.π ⟨c, hc⟩).2
  have hact : ActsAs F l c := actsAs_of_pi F hl ⟨c, hc⟩ hla
  have hlX : l ∈ L ⊓ Subgroup.normalizer (F.V1 : Set G) := ⟨hlL, mem_normalizer_V1 F hl hact hcb⟩
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper _ hlX
  have hlk : l ^ 2 ^ k ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hl _
  refine ⟨(l ^ 2 ^ k) ^ 2 ^ k, ?_, Subgroup.pow_mem _ hlk _, ?_⟩
  · change _ ∈ oTwoRes _
    rw [oTwoRes_eq_oTwoUpper]
    exact Subgroup.pow_mem _ hk _
  · have h1 := (hact.pow hl (2 ^ k)).pow hlk (2 ^ k)
    have h3 : 2 ^ k * 2 ^ k % 3 = 1 := by
      rw [← mul_pow, Nat.pow_mod]
      norm_num
    have h2 : (c ^ 2 ^ k) ^ 2 ^ k = c := by
      rw [← pow_mul, ← Nat.mod_add_div (2 ^ k * 2 ^ k) 3, pow_add, pow_mul, hc3, one_pow, mul_one,
        h3, pow_one]
    rwa [h2] at h1

theorem mem_E16 [Finite G] (F : Frame126 T L V) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hR1T : Ri T L F.V1 ≤ T) {r : G} (hr : r ∈ Ri T L F.V1) {σ : Perm (Fin 8)}
    (hσ : ActsAs F r σ) : σ ∈ E16 := by
  have hrT := hR1T hr
  have hrV := hTV hrT
  obtain ⟨σ', hσ'P, hσ'⟩ := actsAs_of_mem_T F hrT
  have hσP : PresPart σ := hσ'.unique hσ hrV ▸ hσ'P
  have key : ∀ c : Perm (Fin 8), c ∈ alternatingGroup (Fin 8) → c ^ 3 = 1 →
      (∀ i : Fin 8, (i.val < 4 ↔ (c i).val < 4)) → PresPart (c * σ * c⁻¹ * σ⁻¹) := by
    intro c hc hc3 hcb
    obtain ⟨l, hlL1, hlV, hl⟩ := exists_mem_L1 F hc hc3 hcb
    have hN : l ∈ Subgroup.normalizer (Ri T L F.V1 : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Li L F.V1 ⊔ T) (Subgroup.mem_sup_left hlL1)
    have hx : l * r * l⁻¹ * r⁻¹ ∈ Ri T L F.V1 :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hN r).1 hr) (Subgroup.inv_mem _ hr)
    obtain ⟨ρ, hρP, hρ⟩ := actsAs_of_mem_T F (hR1T hx)
    have h1 := hl.commutator hσ hlV hrV
    rw [hρ.unique h1 (hTV (hR1T hx))] at hρP
    exact hρP
  exact eq_tau_of_comm hσP (key c1 c1_mem c1_pow_three c1_block)
    (key c2 c2_mem c2_pow_three c2_block)

theorem le_centralizer_of_isMaxElemAbelian [Finite G] (F : Frame126 T L V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V) (hVe : IsElemAbelian 2 V)
    (hR1T : Ri T L F.V1 ≤ T) (hVR1 : V ≤ Ri T L F.V1) {A : Subgroup G}
    (hA : IsMaxElemAbelian (Ri T L F.V1) A) : A ≤ Subgroup.centralizer (V : Set G) := by
  have hAT : A ≤ T := hA.1.trans hR1T
  have hN : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (V : Set G) := fun a => hTV (hAT a.2)
  have hex : ∀ a : ↥A, ∃ σ : Perm (Fin 8), ActsAs F a σ := fun a =>
    (actsAs_of_mem_T F (hAT a.2)).imp fun _ h => h.2
  choose φ₀ hφ₀ using hex
  let φ : ↥A →* Perm (Fin 8) :=
    { toFun := φ₀
      map_one' := (hφ₀ 1).unique (ActsAs.one F) (Subgroup.one_mem _)
      map_mul' := fun a b => (hφ₀ (a * b)).unique ((hφ₀ a).mul (hφ₀ b) (hN b)) (hN (a * b)) }
  have hker : ∀ a : ↥A, φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro a
    constructor
    · intro h
      have h1 : ActsAs F a 1 := h ▸ hφ₀ a
      exact mem_centralizer_of_actsAs_one F hVL hLV (hTL (hAT a.2)) (hN a) h1
    · intro h
      have h1 : ActsAs F a 1 := by
        intro v w hw
        have hwv : w = v := Subtype.ext (by
          rw [hw, (Subgroup.mem_centralizer_iff.1 h v v.2).symm]
          group)
        rw [hwv, dAct_one]
      exact (hφ₀ a).unique h1 (hN a)
  have hsub : (A ⊓ Subgroup.centralizer (V : Set G)).subgroupOf A = φ.ker := by
    ext a
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf]
    exact ⟨fun h => (hker a).2 h.2, fun h => ⟨a.2, (hker a).1 h⟩⟩
  have hidx : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A = Nat.card φ.range := by
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
  have hPE : φ.range ≤ E16 := by
    rintro _ ⟨a, rfl⟩
    exact mem_E16 F hTV hR1T (hA.1 a.2) (hφ₀ a)
  have hfix : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card F.β.ker * Nat.card (fixD φ.range) := by
    let X : Subgroup ↥V := (V ⊓ Subgroup.centralizer (A : Set G)).subgroupOf V
    have hX : Nat.card X = Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    let ψ : ↥X →* D8 := F.β.comp X.subtype
    have h1 : Nat.card X = Nat.card ψ.range * Nat.card ψ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    have h2 : Nat.card ψ.ker ≤ Nat.card F.β.ker := by
      refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥X) : ↥V), x.2⟩) fun x y h => ?_
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    have h3 : ψ.range ≤ fixD φ.range := by
      rintro _ ⟨x, rfl⟩ σ ⟨a, rfl⟩
      have hxa : ((x : ↥V) : G) = (a : G) * ((x : ↥V) : G) * (a : G)⁻¹ := by
        have hc := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).2
        rw [Subgroup.mem_centralizer_iff.1 hc a a.2]
        group
      exact (hφ₀ a (x : ↥V) (x : ↥V) hxa).symm
    have h4 := Subgroup.card_le_of_le h3
    rw [← hX, h1, mul_comm]
    exact Nat.mul_le_mul h2 h4
  have hV64 : Nat.card F.β.ker * 64 ≤ Nat.card V := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup F.β.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective F.β F.β_surj).toEquiv, mul_comm]
    exact Nat.mul_le_mul_right _ card_D8
  have hthm := card_le_relIndex_mul_card hVe hVR1 hA
  have h64 : 64 ≤ Nat.card φ.range * Nat.card (fixD φ.range) := by
    have hk : 0 < Nat.card F.β.ker := Nat.card_pos
    have h1 : Nat.card F.β.ker * 64 ≤
        Nat.card F.β.ker * (Nat.card φ.range * Nat.card (fixD φ.range)) := by
      calc Nat.card F.β.ker * 64 ≤ Nat.card V := hV64
        _ ≤ _ := hthm
        _ ≤ Nat.card φ.range * (Nat.card F.β.ker * Nat.card (fixD φ.range)) := by
          rw [hidx]
          exact Nat.mul_le_mul_left _ hfix
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h1 hk
  have hbot := eq_bot_of_le_E16 φ.range hPE h64
  intro a ha
  have h1 : φ ⟨a, ha⟩ ∈ φ.range := ⟨⟨a, ha⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact (hker ⟨a, ha⟩).1 h1

omit [IsMulCommutative ↥V] in
theorem isElemAbelian_of_reduced {X : Subgroup G} (hVX : V ≤ X)
    (hred : IsPrimeReduced 2 (V.subgroupOf X)) : IsElemAbelian 2 V := by
  have := hred.isElementaryAbelian
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h := mul_comm (⟨⟨a, hVX a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩ : ↥(V.subgroupOf X))
      ⟨⟨b, hVX b.2⟩, Subgroup.mem_subgroupOf.mpr b.2⟩
    exact congrArg (fun z : ↥(V.subgroupOf X) => ((z : ↥X) : G)) h
  · have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf X)
      (⟨x, hVX hx⟩ : ↥X) (Subgroup.mem_subgroupOf.mpr hx)
    simpa using congrArg Subtype.val h2

omit [IsMulCommutative ↥V] in
theorem normalizer_le_normalizer_thompsonJ (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (thompsonJ X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have e : B6.conjSub g X = X := B6.conjSub_eq_self hg
  have h1 := B6.thompsonJ_conjSub X g
  rw [e] at h1
  exact h1.symm

theorem part4 [Finite G] (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    thompsonJ (Ri T L F.V1) = thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ∧
      Subgroup.normalizer (Ri T L F.V1 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, hfsu⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hTL := hyp.normalizes
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_reduced (hVT.trans le_sup_right) hred
  have hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G) := by
    obtain ⟨-, -, hO⟩ := h3228 G T L V hfsu
    have hVc : conjClosure V T = V := le_antisymm
      (conjClosure_le fun _ ht v hv => (Subgroup.mem_normalizer_iff.1 (hTV ht) v).1 hv)
      (le_conjClosure V T)
    rwa [hyp.conjClosure_eq, hVc] at hO
  have hL1L : Li L F.V1 ≤ L := (oTwoRes_le _).trans inf_le_left
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hQR1 : T ⊓ Subgroup.centralizer (V : Set G) ≤ Ri T L F.V1 := by
    rw [← hQ]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    · rw [hQ]
      exact inf_le_left.trans le_sup_right
    · exact (sup_le_sup_right hL1L T).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun w hw => comm_of_mem hw hv
  have hVR1 : V ≤ Ri T L F.V1 := (le_inf hVT hVC).trans hQR1
  have hJ : thompsonJ (Ri T L F.V1) ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
    iSup₂_le fun A hA => le_inf (hA.1.trans hR1T)
      (le_centralizer_of_isMaxElemAbelian F hTV hTL hLV hVL hVe hR1T hVR1 hA)
  have hJeq : thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) = thompsonJ (Ri T L F.V1) :=
    B6.thompsonJ_eq_of_le hJ hQR1
  refine ⟨hJeq.symm, ?_⟩
  have hJ1 : thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ≠ ⊥ := by
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian (T ⊓ Subgroup.centralizer (V : Set G))
    have hcard := hA₀.2.2 V (le_inf hVT hVC) hVe
    intro h
    have hA₀1 : A₀ = ⊥ := eq_bot_iff.2 ((B6.le_thompsonJ hA₀).trans h.le)
    rw [hA₀1, Subgroup.card_bot] at hcard
    exact hV1 (Subgroup.eq_bot_of_card_le V hcard)
  have hJ2 : IsPGroup 2 (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))) :=
    hyp.sylow.1.to_le ((B6.thompsonJ_le _).trans inf_le_left)
  have hLTJ : L ⊔ T ≤
      Subgroup.normalizer (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) : Set G) := by
    rw [← hQ]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (normalizer_le_normalizer_thompsonJ _)
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)), hJ1, hJ2, rfl⟩ : IsTwoLocal _)
  have hM'eq := huniq M' hM' (hLTJ.trans hle)
  calc Subgroup.normalizer (Ri T L F.V1 : Set G)
      ≤ Subgroup.normalizer (thompsonJ (Ri T L F.V1) : Set G) :=
        normalizer_le_normalizer_thompsonJ _
    _ = Subgroup.normalizer (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) : Set G) := by
        rw [hJeq]
    _ ≤ M' := hle
    _ = Subgroup.normalizer (L : Set G) := hM'eq

end S126L1b

end CFSG.Quasithin.H13
