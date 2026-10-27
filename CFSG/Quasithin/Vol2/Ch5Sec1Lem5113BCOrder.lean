module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BlockBC
public import CFSG.GH74.KGroups.PSL2
public import CFSG.Walter.ReeOrder.JT.PSL24
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped IsMulCommutative MatrixGroups Matrix Pointwise
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)

namespace BCOrd

variable {G : Type} [Group G]

theorem commutator_le_inf_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, B⁆ ≤ A ⊓ B := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hBA hb) _).mp (A.inv_mem ha)
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact A.mul_mem ha h1
  · have h1 : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hAB ha) b).mp hb
    exact B.mul_mem h1 (B.inv_mem hb)

theorem comm_mem_of_perfect {L Q V : Subgroup G} (hperf : ⁅L, L⁆ = L) (hQL : Q ≤ L)
    (hQV : ⁅Q, L⁆ ≤ V) {r : G} (hr : ∀ ℓ ∈ L, r * ℓ * r⁻¹ * ℓ⁻¹ ∈ Q) :
    ∀ ℓ ∈ L, r * ℓ * r⁻¹ * ℓ⁻¹ ∈ V := by
  have hcomm : ∀ q ∈ Q, ∀ ℓ ∈ L, q * ℓ * q⁻¹ * ℓ⁻¹ ∈ V := fun q hq ℓ hℓ => by
    have h1 := hQV (Subgroup.commutator_mem_commutator hq hℓ)
    rwa [commutatorElement_def] at h1
  set N : Subgroup ↥Q := V.subgroupOf Q with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := hcomm g g.2 n (hQL n.2)
    have e : ((g * n * g⁻¹ : ↥Q) : G) = ((g : G) * n * (g : G)⁻¹ * (n : G)⁻¹) * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact V.mul_mem h1 hn
  let f : ↥L → ↥Q := fun ℓ => ⟨r * ℓ * r⁻¹ * (ℓ : G)⁻¹, hr ℓ ℓ.2⟩
  have hf : ∀ ℓ : ↥L, ((f ℓ : ↥Q) : G) = r * ℓ * r⁻¹ * (ℓ : G)⁻¹ := fun _ => rfl
  let φ : ↥L →* ↥Q ⧸ N :=
    { toFun := fun ℓ => ((f ℓ : ↥Q) : ↥Q ⧸ N)
      map_one' := by
        have h1 : f 1 = 1 := Subtype.ext (by rw [hf]; simp)
        simp only [h1, QuotientGroup.mk_one]
      map_mul' := fun a b => by
        show ((f (a * b) : ↥Q) : ↥Q ⧸ N) = (f a : ↥Q ⧸ N) * (f b : ↥Q ⧸ N)
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, hN, Subgroup.mem_subgroupOf]
        have h1 := V.inv_mem (hcomm _ (Q.inv_mem (f b).2) a a.2)
        convert h1 using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf]
        group }
  have hφ : ∀ ℓ : ↥L, φ ℓ = ((f ℓ : ↥Q) : ↥Q ⧸ N) := fun _ => rfl
  have hab : ∀ x y : ↥L, φ x * φ y = φ y * φ x := by
    intro x y
    rw [hφ, hφ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf]
    have h1 := hcomm _ (Q.inv_mem (f y).2) _ (hQL (Q.inv_mem (f x).2))
    convert h1 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hker : commutator ↥L ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      hab x y]
    group
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have htop : commutator ↥L = ⊤ := Group.IsPerfect.commutator_eq_top
  intro ℓ hℓ
  have h1 : φ ⟨ℓ, hℓ⟩ = 1 := hker (htop ▸ Subgroup.mem_top _)
  rw [hφ, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem exists_mul_mem_centralizer_of_odd [Finite G] {L V : Subgroup G} {c : G}
    (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hcV : ∀ v ∈ V, c * v = v * c)
    (hd : ∀ ℓ ∈ L, ℓ * c * ℓ⁻¹ * c⁻¹ ∈ V)
    (hodd : Odd ((Subgroup.centralizer ({c} : Set G)).relIndex L)) :
    ∃ w ∈ V, ∀ x ∈ L, x * (c * w) = c * w * x := by
  classical
  let _ : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun a b => Subtype.ext (hVc a a.2 b b.2) }
  set H : Subgroup ↥L := (Subgroup.centralizer ({c} : Set G)).subgroupOf L with hH
  let _ : Fintype (↥L ⧸ H) := Fintype.ofFinite _
  let d : ↥L → ↥V := fun ℓ => ⟨(ℓ : G) * c * (ℓ : G)⁻¹ * c⁻¹, hd ℓ ℓ.2⟩
  have hdc : ∀ ℓ : ↥L, ((d ℓ : ↥V) : G) = (ℓ : G) * c * (ℓ : G)⁻¹ * c⁻¹ := fun _ => rfl
  have hdH : ∀ a k : ↥L, k ∈ H → d (a * k) = d a := by
    intro a k hk
    rw [hH, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hk
    have h1 : c * (k : G) = (k : G) * c := hk c (Set.mem_singleton c)
    apply Subtype.ext
    rw [hdc, hdc, Subgroup.coe_mul]
    calc (a : G) * k * c * ((a : G) * k)⁻¹ * c⁻¹ =
        (a : G) * ((k : G) * c) * (k : G)⁻¹ * (a : G)⁻¹ * c⁻¹ := by group
      _ = (a : G) * (c * (k : G)) * (k : G)⁻¹ * (a : G)⁻¹ * c⁻¹ := by rw [h1]
      _ = (a : G) * c * (a : G)⁻¹ * c⁻¹ := by group
  let f : ↥L ⧸ H → ↥V := fun q => d q.out
  have hf : ∀ a : ↥L, f (a : ↥L ⧸ H) = d a := by
    intro a
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H a
    show d (a : ↥L ⧸ H).out = d a
    rw [hk]
    exact hdH a k k.2
  set w : ↥V := ∏ q, f q with hw
  let κ : ↥L → ↥V →* ↥V := fun x =>
    { toFun := fun v => ⟨(x : G) * v * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLV x.2) v).mp v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hκ : ∀ (x : ↥L) (v : ↥V), ((κ x v : ↥V) : G) = (x : G) * v * (x : G)⁻¹ := fun _ _ => rfl
  have hκf : ∀ (x : ↥L) (q : ↥L ⧸ H), κ x (f q) = f (x • q) * (d x)⁻¹ := by
    intro x q
    induction q using QuotientGroup.induction_on with
    | H a =>
      have e : x • (a : ↥L ⧸ H) = ((x * a : ↥L) : ↥L ⧸ H) := rfl
      rw [e, hf, hf]
      apply Subtype.ext
      rw [hκ, Subgroup.coe_mul, Subgroup.coe_inv, hdc, hdc, hdc, Subgroup.coe_mul]
      group
  have hd2 : ∀ x : ↥L, d x * d x = 1 := fun x => Subtype.ext (hV2 _ (d x).2)
  obtain ⟨m, hm⟩ := hodd
  have hcard : Fintype.card (↥L ⧸ H) = 2 * m + 1 := by
    rw [← Nat.card_eq_fintype_card, ← hm]
    rfl
  have hwx : ∀ x : ↥L, κ x w = w * d x := by
    intro x
    rw [hw, map_prod]
    simp_rw [hκf x]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard,
      Fintype.prod_equiv (MulAction.toPerm x) (fun q => f (x • q)) f (fun _ => rfl)]
    congr 1
    have hinv : (d x)⁻¹ = d x := inv_eq_of_mul_eq_one_right (hd2 x)
    rw [hinv, pow_succ, pow_mul, sq, hd2, one_pow, one_mul]
  refine ⟨w, w.2, fun x hx => ?_⟩
  obtain ⟨dd, hdd⟩ : ∃ dd : G, dd = x * c * x⁻¹ * c⁻¹ := ⟨_, rfl⟩
  have h1 : (x : G) * w * x⁻¹ = (w : G) * dd := by
    have := congrArg Subtype.val (hwx ⟨x, hx⟩)
    rw [hκ, Subgroup.coe_mul, hdc] at this
    rw [hdd]
    exact this
  have hdV : dd ∈ V := hdd ▸ hd x hx
  have h2 : dd * c = c * dd := (hcV dd hdV).symm
  have h3 : dd * w = (w : G) * dd := hVc dd hdV w w.2
  have h4 : dd * dd = 1 := hV2 dd hdV
  have hxc : x * c * x⁻¹ = dd * c := by rw [hdd]; group
  calc x * (c * w) = (x * c * x⁻¹) * ((x : G) * w * x⁻¹) * x := by group
    _ = (dd * c) * ((w : G) * dd) * x := by rw [hxc, h1]
    _ = c * (dd * w) * dd * x := by rw [h2]; group
    _ = c * ((w : G) * dd) * dd * x := by rw [h3]
    _ = c * w * (dd * dd) * x := by group
    _ = c * w * x := by rw [h4, mul_one]

theorem mem_of_sl2_invariant {F : Type*} [Field F] (M : AddSubgroup (Fin 2 → F))
    (hM : ∀ g : SL(2, F), ∀ v ∈ M, (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M)
    {v : Fin 2 → F} (hvM : v ∈ M) (hv : v ≠ 0) (u : Fin 2 → F) : u ∈ M := by
  let up : F → SL(2, F) := fun t => ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let ww : SL(2, F) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩
  have hup : ∀ (t : F) (x : Fin 2 → F),
      ((up t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ x = ![x 0 + t * x 1, x 1] := by
    intro t x
    ext i
    fin_cases i <;> simp [up, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hww : ∀ x : Fin 2 → F,
      ((ww : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ x = ![-x 1, x 0] := by
    intro x
    ext i
    fin_cases i <;> simp [ww, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have key : ∀ x ∈ M, x 1 ≠ 0 → ∀ u : Fin 2 → F, u ∈ M := by
    intro x hx hx1 u
    have h1 : ∀ c : F, ![c, 0] ∈ M := by
      intro c
      have h2 := M.sub_mem (hM (up (c / x 1)) x hx) hx
      rw [hup] at h2
      convert h2 using 1
      ext i
      fin_cases i
      · simp [div_mul_cancel₀ c hx1]
      · simp
    have h2 : ∀ c : F, ![0, c] ∈ M := by
      intro c
      have h3 := hM ww _ (h1 c)
      rw [hww] at h3
      convert h3 using 1
      ext i
      fin_cases i <;> simp
    have e : u = ![u 0, 0] + ![0, u 1] := by
      ext i
      fin_cases i <;> simp
    rw [e]
    exact M.add_mem (h1 _) (h2 _)
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      ext i
      fin_cases i
      · exact h0
      · exact hv1
    have hwv := hM ww v hvM
    rw [hww] at hwv
    exact key _ hwv (by simpa using hv0) u
  · exact key v hvM hv1 u

variable {L N S : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)}

theorem injective_of_qcoord (hc : QCoord L N S F ψ Y)
    (hNL : N ⊓ Subgroup.centralizer (L : Set G) = ⊥) : Function.Injective Y := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, hc.ker] at hx
  have hx' : (x : G) ∈ N ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
  rw [hNL, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (Subtype.ext hx')

theorem card_eq_of_qcoord [Finite F] (hc : QCoord L N S F ψ Y) (hYinj : Function.Injective Y) :
    Nat.card N = Nat.card F ^ 2 := by
  rw [Nat.card_congr (Equiv.ofBijective Y ⟨hYinj, hc.surj⟩),
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → F) ≃ (Fin 2 → F)),
    Nat.card_pi]
  simp

theorem le_of_qcoord (hc : QCoord L N S F ψ Y) (hYinj : Function.Injective Y) {W : Subgroup G}
    (hWN : W ≤ N) (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) : N ≤ W := by
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  let MW : AddSubgroup (Fin 2 → F) :=
    { carrier := {v | ∃ x : ↥N, (x : G) ∈ W ∧ Multiplicative.toAdd (Y x) = v}
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, W.mul_mem hx hy, by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, W.one_mem, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x⁻¹, W.inv_mem hx, by rw [map_inv, toAdd_inv]⟩ }
  have hMinv : ∀ g : SL(2, F), ∀ v ∈ MW, (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ MW := by
    rintro g _ ⟨x, hx, rfl⟩
    obtain ⟨n, hnL, hn⟩ := mem_autOn_iff.mp (ψ.symm g).2
    refine ⟨((ψ.symm g : ↥(autOn L N)) : MulAut ↥N) x, ?_, ?_⟩
    · rw [← hn, conjAct_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hLW hnL) x).mp hx
    · rw [hc.intertwine, MulEquiv.apply_symm_apply]
  have hv0 : Multiplicative.toAdd (Y ⟨w₀, hWN hw₀⟩) ≠ 0 := by
    intro h0
    apply hw₀1
    have h1 : Y ⟨w₀, hWN hw₀⟩ = Y 1 := by rw [map_one]; exact toAdd_eq_zero.mp h0
    have h2 := hYinj h1
    exact Subtype.ext (show w₀ = 1 from congrArg Subtype.val h2)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_of_sl2_invariant MW hMinv ⟨⟨w₀, hWN hw₀⟩, hw₀, rfl⟩ hv0
    (Multiplicative.toAdd (Y ⟨y, hy⟩))
  have h1 := hYinj (Multiplicative.toAdd.injective hxy)
  have h2 : (x : G) = y := congrArg Subtype.val h1
  rw [← h2]
  exact hx

theorem card_autOn_eq_of_qcoord [Finite G] [Finite F] (hc : QCoord L N S F ψ Y) (hSL : S ≤ L) :
    Nat.card (autOn S N) = Nat.card F := by
  have hmem : ∀ φ : ↥(autOn S N), (φ : MulAut ↥N) ∈ autOn L N := fun φ =>
    A4.autOn_mono hSL φ.2
  apply le_antisymm
  · refine Nat.card_le_card_of_injective
      (fun φ : ↥(autOn S N) => ((ψ ⟨φ, hmem φ⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1) ?_
    intro φ₁ φ₂ h12
    obtain ⟨b₁, hb₁⟩ := (hc.sylow ⟨φ₁, hmem φ₁⟩).mp φ₁.2
    obtain ⟨b₂, hb₂⟩ := (hc.sylow ⟨φ₂, hmem φ₂⟩).mp φ₂.2
    simp only [hb₁, hb₂, coe_unipSL] at h12
    have h1 : ψ ⟨φ₁, hmem φ₁⟩ = ψ ⟨φ₂, hmem φ₂⟩ := by
      rw [hb₁, hb₂]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at h12
      rw [h12]
    have h2 := congrArg Subtype.val (ψ.injective h1)
    exact Subtype.ext h2
  · have hS : ∀ b : F, (((ψ.symm (unipSL b) : ↥(autOn L N)) : MulAut ↥N)) ∈ autOn S N :=
      fun b => (hc.sylow _).mpr ⟨b, by rw [MulEquiv.apply_symm_apply]⟩
    refine Nat.card_le_card_of_injective (fun b : F => (⟨_, hS b⟩ : ↥(autOn S N))) ?_
    intro b₁ b₂ h12
    have h0 := congrArg Subtype.val h12
    have h1 : ψ.symm (unipSL b₁) = ψ.symm (unipSL b₂) := Subtype.ext h0
    have h2 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1)
      (ψ.symm.injective h1)
    simpa [coe_unipSL] using h2

end BCOrd

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem inf_centralizer_eq_bot_of_omega {n : ℕ} (h : Hyp5_0_1 G T M L n)
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le_normalizer
  by_contra hne
  have hN : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_of_conj_mem fun x hx =>
      ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer L (hTL ht))
          x).mp hx.2⟩
  have h1 := inf_centralizer_ne_bot_of_two hT2 (hT2.to_le inf_le_left) hN hne
  have hX2 : IsPGroup 2 ↥((T ⊓ Subgroup.centralizer (L : Set G)) ⊓
      Subgroup.centralizer (T : Set G)) := hT2.to_le (inf_le_left.trans inf_le_left)
  have hcard : 2 ∣ Nat.card ↥((T ⊓ Subgroup.centralizer (L : Set G)) ⊓
      Subgroup.centralizer (T : Set G)) := by
    rcases hX2.card_eq_or_dvd with h1' | h2'
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1') h1
    · exact h2'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyZ : (y : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨mem_quasithinOmegaOneCenter_iff.mpr
      ⟨y.2.1.1, y.2.2, by rw [← hy']; exact pow_orderOf_eq_one _⟩, y.2.1.2⟩
  rw [hZL, Subgroup.mem_bot] at hyZ
  rw [hyZ, orderOf_one] at hy'
  exact absurd hy' (by norm_num)

theorem card_le_two_pow_seven_of_block (h : Hyp5_0_1 G T M L 2)
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {V' : Subgroup G} (hV' : IsCh5Module T L V') (hnat : IsNatQuotCh5 L V' 2)
    (hL : C126Third (L ⊔ T) T) : Nat.card T ≤ 2 ^ 7 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le_normalizer
  have hred := hV'.isTwoReducedIn
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V' : Set G) := hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V' : Set G) := le_sup_left.trans hLTV
  have hTV : T ≤ Subgroup.normalizer (V' : Set G) := le_sup_right.trans hLTV
  have hVe : IsElemAbelian 2 V' := hred.2.2.1
  have hVcomm : ∀ v ∈ V', ∀ w ∈ V', v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hV2 : ∀ v ∈ V', v * v = 1 := fun v hv => by rw [← sq]; exact hVe.2 v hv
  have hVR2 : V' ≤ reducedAggregate (L ⊔ T) := hV'.le_reducedAggregate
  have hVT : V' ≤ T := hVR2.trans h.reducedAggregate_le_T
  have hS := h.setting516 hD hV'
  have hQV : pCoreOf 2 L ≤ Subgroup.centralizer (V' : Set G) :=
    hS.pCoreOf_le.trans (Subgroup.centralizer_le hVR2)
  have hQT : pCoreOf 2 L ≤ T := h.pCoreOf_le_pCoreOf_sup.trans
    (F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf le_sup_right))
  have hV'ne : V' ≠ ⊥ := fun hb => hV'.2.2 (by rw [hb, Subgroup.commutator_bot_left])
  have hLQ : ¬ L ≤ pCoreOf 2 L := by
    intro hle
    have := h.isSimple
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥L ⧸ CFSG.pCore 2 ↥L)
    apply hq
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [QuotientGroup.eq_one_iff]
      exact (mem_pCore_iff_mem_pCoreOf L y).mpr (hle y.2)
  have hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := h.inf_centralizer_eq_bot_of_omega hZL
  have hVCL : V' ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hCTL]
    exact inf_le_inf_right _ hVT
  obtain ⟨nb, K, -, hK, hKc, hres, -, -⟩ := hL
  have hres2 : twoResidual (L ⊔ T) = L := by
    apply le_antisymm
    · refine twoResidual_le_of_isTwoQuotient le_sup_left h.sup_le_normalizer fun y hy => ?_
      have hy' : y ∈ ((L : Set G) * (T : Set G)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL]
        exact hy
      obtain ⟨l, hl, t, ht, rfl⟩ := hy'
      obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
      have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
      obtain ⟨l', hl', he⟩ := pow_mul_mem_of_mem_normalizer hl (hTL ht) (2 ^ a)
      rw [hta, mul_one] at he
      exact ⟨a, by rw [he]; exact hl'⟩
    · have hNL : twoResidual (L ⊔ T) ⊓ L ≤ L := inf_le_right
      have hnorm : L ≤ Subgroup.normalizer ((twoResidual (L ⊔ T) ⊓ L : Subgroup G) : Set G) :=
        fun l hl => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_twoResidual (L ⊔ T) (Subgroup.mem_sup_left hl),
            Subgroup.le_normalizer hl⟩
      have heq := h.faithful.2.1 _ hNL
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hnorm) fun x hx => by
          obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (L ⊔ T) x (Subgroup.mem_sup_left hx)
          exact ⟨k, hk, L.pow_mem hx _⟩
      exact heq.ge.trans inf_le_left
  have hLK : L = ⨆ i, K i := hres2.symm.trans hres
  obtain ⟨j, hj⟩ : ∃ j, ¬ K j ≤ pCoreOf 2 L := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hLQ (hLK.le.trans (iSup_le hall))
  have hKjL : K j ≤ L := (le_iSup K j).trans hLK.ge
  have hLKj : L ≤ Subgroup.normalizer (K j : Set G) := by
    rw [hLK]
    refine iSup_le fun i => ?_
    by_cases hij : i = j
    · rw [hij]
      exact Subgroup.le_normalizer
    · have hle : K i ≤ Subgroup.centralizer (K j : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hKc i j hij)
      exact fun x hx => mem_normalizer_of_conj_mem fun y hy => by
        rw [← Subgroup.mem_centralizer_iff.mp (hle hx) y hy, mul_inv_cancel_right]
        exact hy
  have hKjeq : K j = L := (h.le_pCoreOf_or_eq hKjL hLKj).resolve_left hj
  obtain ⟨hblk, hJ⟩ := hK j
  rw [hKjeq] at hblk hJ
  obtain ⟨⟨⟨-, -, hUQ, -, hZU, hirr⟩, -, -⟩, -⟩ := hblk
  have hUT : blockU L ≤ T := hUQ.1.trans (inf_le_left.trans hQT)
  have hZb : blockZ L = ⊥ := by
    rw [eq_bot_iff, ← hCTL]
    exact inf_le_inf_right _ hUT
  rw [hZb] at hZU hirr
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    le_normalizer_commutator_of (le_normalizer_pCoreOf 2 L) Subgroup.le_normalizer
  have hV'L : ⁅V', L⁆ ≤ V' ⊓ L :=
    BCOrd.commutator_le_inf_of_le_normalizer (hVT.trans hTL) hLV
  have hVLQ : V' ⊓ L ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf ⟨hLV hl, Subgroup.le_normalizer hl⟩)
    (hT2.to_le (inf_le_left.trans hVT))
  have hUV : blockU L ≤ V' := by
    have hW : blockU L ⊓ V' ≠ ⊥ := by
      intro hb
      apply hV'.2.2
      have hC1 : ⁅V', L⁆ ≤ V' := hV'L.trans inf_le_left
      have hC1N : L ≤ Subgroup.normalizer ((⁅V', L⁆ : Subgroup G) : Set G) :=
        le_normalizer_commutator_of hLV Subgroup.le_normalizer
      have h1 : ⁅⁅V', L⁆, L⁆ ≤ blockU L ⊓ V' := le_inf
        (Subgroup.commutator_mono (hV'L.trans hVLQ) le_rfl)
        ((BCOrd.commutator_le_inf_of_le_normalizer ((hC1.trans hVT).trans hTL) hC1N).trans
          (inf_le_left.trans hC1))
      rw [hb, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
      rw [eq_bot_iff, ← hVCL]
      exact le_inf hC1 h1
    have hLW : L ≤ Subgroup.normalizer ((blockU L ⊓ V' : Subgroup G) : Set G) := fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hLU hl, hLV hl⟩
    rcases hirr (blockU L ⊓ V') bot_le inf_le_left hLW with h1 | h1
    · exact absurd h1 hW
    · exact inf_eq_left.mp h1
  obtain ⟨F, _, _, _, hF, ψ, Y, hc⟩ := hnat.exists_qcoord h.isSylowTwoOf_inf
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have hYinj : Function.Injective Y := BCOrd.injective_of_qcoord hc hVCL
  have hV16 : Nat.card V' = 16 := by rw [BCOrd.card_eq_of_qcoord hc hYinj, hF4]; norm_num
  have hirrV : ∀ W : Subgroup G, W ≤ V' → L ≤ Subgroup.normalizer (W : Set G) → W ≠ ⊥ →
      V' ≤ W := fun W hWV hLW hW => BCOrd.le_of_qcoord hc hYinj hWV hLW hW
  set R := T ⊓ Subgroup.centralizer (V' : Set G) with hRdef
  have hRT : R ≤ T := inf_le_left
  have hRV : ∀ r ∈ R, ∀ v ∈ V', r * v = v * r := fun r hr v hv =>
    (Subgroup.mem_centralizer_iff.mp hr.2 v hv).symm
  have hRL : ∀ r ∈ R, ∀ ℓ ∈ L, r * ℓ * r⁻¹ * ℓ⁻¹ ∈ V' := by
    intro r hr
    refine BCOrd.comm_mem_of_perfect h.commutator_eq (pCoreOf_le 2 L) hUV fun ℓ hℓ => ?_
    refine h.inf_centralizer_le hLV hV'.2.2 ⟨?_, ?_⟩
    · exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL hr.1) ℓ).mp hℓ) (L.inv_mem hℓ)
    · have h1 : ℓ * r⁻¹ * ℓ⁻¹ ∈ Subgroup.centralizer (V' : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer V' (hLV hℓ))
          _).mp (Subgroup.inv_mem _ hr.2)
      have e : r * ℓ * r⁻¹ * ℓ⁻¹ = r * (ℓ * r⁻¹ * ℓ⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hr.2 h1
  have hRcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
    intro r hr s hs
    have hmem : (s * r)⁻¹ * (r * s) ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_inf.mpr
        ⟨T.mul_mem (T.inv_mem (T.mul_mem hs.1 hr.1)) (T.mul_mem hr.1 hs.1), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro ℓ hℓ
      obtain ⟨a, ha⟩ : ∃ a, a = r * ℓ * r⁻¹ * ℓ⁻¹ := ⟨_, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, b = s * ℓ * s⁻¹ * ℓ⁻¹ := ⟨_, rfl⟩
      have haV : a ∈ V' := ha ▸ hRL r hr ℓ hℓ
      have hbV : b ∈ V' := hb ▸ hRL s hs ℓ hℓ
      have hra : r * ℓ = a * ℓ * r := by rw [ha]; group
      have hsb : s * ℓ = b * ℓ * s := by rw [hb]; group
      have hrb : r * b = b * r := hRV r hr b hbV
      have hsa : s * a = a * s := hRV s hs a haV
      have hab : a * b = b * a := hVcomm a haV b hbV
      have h1 : r * s * ℓ = b * a * ℓ * (r * s) := by
        calc r * s * ℓ = r * (s * ℓ) := by group
          _ = r * (b * ℓ * s) := by rw [hsb]
          _ = r * b * ℓ * s := by group
          _ = b * r * ℓ * s := by rw [hrb]
          _ = b * (r * ℓ) * s := by group
          _ = b * (a * ℓ * r) * s := by rw [hra]
          _ = b * a * ℓ * (r * s) := by group
      have h2 : s * r * ℓ = a * b * ℓ * (s * r) := by
        calc s * r * ℓ = s * (r * ℓ) := by group
          _ = s * (a * ℓ * r) := by rw [hra]
          _ = s * a * ℓ * r := by group
          _ = a * s * ℓ * r := by rw [hsa]
          _ = a * (s * ℓ) * r := by group
          _ = a * (b * ℓ * s) * r := by rw [hsb]
          _ = a * b * ℓ * (s * r) := by group
      calc ℓ * ((s * r)⁻¹ * (r * s)) = (s * r)⁻¹ * (s * r * ℓ) * (s * r)⁻¹ * (r * s) := by group
        _ = (s * r)⁻¹ * (a * b * ℓ) * (r * s) := by rw [h2]; group
        _ = (s * r)⁻¹ * (b * a * ℓ) * (r * s) := by rw [hab]
        _ = (s * r)⁻¹ * (r * s * ℓ) * (r * s)⁻¹ * (r * s) := by rw [h1]; group
        _ = (s * r)⁻¹ * (r * s) * ℓ := by group
    rw [hCTL, Subgroup.mem_bot] at hmem
    calc r * s = (s * r) * ((s * r)⁻¹ * (r * s)) := by group
      _ = s * r := by rw [hmem, mul_one]
  have hRsq : ∀ r ∈ R, r * r = 1 := by
    intro r hr
    have hmem : r * r ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨T.mul_mem hr.1 hr.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro ℓ hℓ
      obtain ⟨a, ha⟩ : ∃ a, a = r * ℓ * r⁻¹ * ℓ⁻¹ := ⟨_, rfl⟩
      have haV : a ∈ V' := ha ▸ hRL r hr ℓ hℓ
      have hra : r * ℓ = a * ℓ * r := by rw [ha]; group
      have hrav : r * a = a * r := hRV r hr a haV
      have ha2 : a * a = 1 := hV2 a haV
      have h1 : r * r * ℓ = ℓ * (r * r) := by
        calc r * r * ℓ = r * (r * ℓ) := by group
          _ = r * (a * ℓ * r) := by rw [hra]
          _ = r * a * ℓ * r := by group
          _ = a * r * ℓ * r := by rw [hrav]
          _ = a * (r * ℓ) * r := by group
          _ = a * (a * ℓ * r) * r := by rw [hra]
          _ = (a * a) * ℓ * (r * r) := by group
          _ = ℓ * (r * r) := by rw [ha2, one_mul]
      exact h1.symm
    rw [hCTL, Subgroup.mem_bot] at hmem
    exact hmem
  have hRe : IsElemAbelian 2 R :=
    ⟨⟨⟨fun x y => Subtype.ext (hRcomm x x.2 y y.2)⟩⟩, fun x hx => by rw [sq]; exact hRsq x hx⟩
  obtain ⟨A, hA, hAR⟩ : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ¬ A ≤ R := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hJR : thompsonJ T ≤ R := iSup₂_le fun A hA => hall A hA
    have hLR : ⁅L, R⁆ ≤ V' := by
      rw [Subgroup.commutator_le]
      intro ℓ hℓ r hr
      have h1 := V'.inv_mem (hRL r hr ℓ hℓ)
      rw [commutatorElement_def]
      convert h1 using 1
      group
    apply hLQ
    have hLV' : L ≤ V' := by
      calc L = ⁅L, thompsonJ T⁆ := hJ.symm
        _ ≤ ⁅L, R⁆ := Subgroup.commutator_mono le_rfl hJR
        _ ≤ V' := hLR
    exact fun x hx => hVLQ ⟨hLV' hx, hx⟩
  set S := T ⊓ L with hSdef
  have hAT : A ≤ T := hA.1
  have hAV : A ≤ Subgroup.normalizer (V' : Set G) := hAT.trans hTV
  have hSV : S ≤ Subgroup.normalizer (V' : Set G) := inf_le_left.trans hTV
  have hSL : S ≤ L := inf_le_right
  have hAS : autOn A V' ≤ autOn S V' := by
    intro φ hφ
    obtain ⟨n, hnA, rfl⟩ := mem_autOn_iff.mp hφ
    obtain ⟨s, hs, has⟩ := hS.exists_mul_of_isMaxElemAbelian hVR2 hLTV hc hA hnA
    have hasV : (n : G) * s⁻¹ ∈ Subgroup.centralizer (V' : Set G) :=
      Subgroup.centralizer_le hVR2 has
    have heq : conjAct V' n = conjAct V' ⟨s, hSV hs⟩ := by
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [conjAct_apply_coe, conjAct_apply_coe]
      have h1 := Subgroup.mem_centralizer_iff.mp hasV _
        ((Subgroup.mem_normalizer_iff.mp (hSV hs) v).mp v.2)
      calc (n : G) * v * (n : G)⁻¹ =
          ((n : G) * s⁻¹) * (s * v * s⁻¹) * ((n : G) * s⁻¹)⁻¹ := by group
        _ = (s * v * s⁻¹) * ((n : G) * s⁻¹) * ((n : G) * s⁻¹)⁻¹ := by rw [← h1]
        _ = s * v * s⁻¹ := by group
    rw [heq]
    exact mem_autOn_iff.mpr ⟨_, hs, rfl⟩
  have hautS : Nat.card (autOn S V') ≤ Nat.card F := (BCOrd.card_autOn_eq_of_qcoord hc hSL).le
  obtain ⟨a, haA, haR⟩ := Set.not_subset.mp hAR
  have haV : a ∉ Subgroup.centralizer (V' : Set G) := fun h' => haR ⟨hAT haA, h'⟩
  have hφaS : conjAct V' ⟨a, hAV haA⟩ ∈ autOn S V' := hAS (mem_autOn_iff.mpr ⟨_, haA, rfl⟩)
  obtain ⟨b, hb⟩ := (hc.sylow ⟨_, A4.autOn_mono hSL hφaS⟩).mp hφaS
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply haV
    have h1 : ψ ⟨_, A4.autOn_mono hSL hφaS⟩ = 1 := by
      rw [hb]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_unipSL]
    have h2 := congrArg Subtype.val (ψ.injective (h1.trans (map_one ψ).symm))
    have h3 : conjAct V' 1 = conjAct V' ⟨a, hAV haA⟩ := by rw [map_one]; exact h2.symm
    have h4 := inv_mul_mem_centralizer h3
    simpa using h4
  have hfix : ∀ v : ↥V', (v : G) ∈ Subgroup.centralizer (A : Set G) →
      (Multiplicative.toAdd (Y v)) 1 = 0 := by
    intro v hv
    have h1 := hc.intertwine ⟨_, A4.autOn_mono hSL hφaS⟩ v
    have h2 : (conjAct V' ⟨a, hAV haA⟩) v = v := by
      apply Subtype.ext
      rw [conjAct_apply_coe]
      show a * v * a⁻¹ = v
      rw [Subgroup.mem_centralizer_iff.mp hv a haA, mul_inv_cancel_right]
    simp only at h1
    rw [h2, hb, coe_unipSL] at h1
    have h3 := congrFun h1 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h3
    tauto
  have hcardVA : Nat.card ↥(V' ⊓ Subgroup.centralizer (A : Set G)) ≤ Nat.card F := by
    refine Nat.card_le_card_of_injective
      (fun v : ↥(V' ⊓ Subgroup.centralizer (A : Set G)) =>
        (Multiplicative.toAdd (Y ⟨v, v.2.1⟩)) 0) ?_
    intro v w hvw
    have hv1 := hfix ⟨v, v.2.1⟩ v.2.2
    have hw1 := hfix ⟨w, w.2.1⟩ w.2.2
    have hY : Y ⟨v, v.2.1⟩ = Y ⟨w, w.2.1⟩ := by
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · exact hvw
      · exact hv1.trans hw1.symm
    have h2 := congrArg Subtype.val (hYinj hY)
    exact Subtype.ext h2
  have hFF := card_le_relIndex_mul_card hVe hVT hA
  rw [← card_autOn_eq_relIndex hAV, hV16] at hFF
  have hA4 : 4 ≤ Nat.card (autOn A V') := by
    by_contra hlt
    have hlt' : Nat.card (autOn A V') ≤ 3 := by omega
    have h1 : Nat.card (autOn A V') * Nat.card ↥(V' ⊓ Subgroup.centralizer (A : Set G)) ≤
        3 * 4 := Nat.mul_le_mul hlt' (hcardVA.trans hF4.le)
    omega
  have hAeq : autOn A V' = autOn S V' :=
    Subgroup.eq_of_le_of_card_ge hAS (by rw [hF4] at hautS; omega)
  have hCRA : R ⊓ Subgroup.centralizer (A : Set G) ≤ V' := by
    intro c hcRA
    have hcR : c ∈ R := hcRA.1
    have hcA : c ∈ Subgroup.centralizer (A : Set G) := hcRA.2
    have hcS : ∀ s ∈ S, c * s = s * c := by
      intro s hs
      have h1 : conjAct V' ⟨s, hSV hs⟩ ∈ autOn A V' := by
        rw [hAeq]
        exact mem_autOn_iff.mpr ⟨_, hs, rfl⟩
      obtain ⟨n, hnA, hn⟩ := mem_autOn_iff.mp h1
      have h2 := inv_mul_mem_centralizer hn
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      have h3 : (n : G)⁻¹ * s ∈ R := ⟨T.mul_mem (T.inv_mem (hAT hnA)) hs.1, h2⟩
      have h4 : c * n = n * c := (Subgroup.mem_centralizer_iff.mp hcA n hnA).symm
      have h5 : c * ((n : G)⁻¹ * s) = ((n : G)⁻¹ * s) * c := hRcomm c hcR _ h3
      calc c * s = (c * n) * ((n : G)⁻¹ * s) := by group
        _ = (n * c) * ((n : G)⁻¹ * s) := by rw [h4]
        _ = n * (c * ((n : G)⁻¹ * s)) := by group
        _ = n * (((n : G)⁻¹ * s) * c) := by rw [h5]
        _ = s * c := by group
    have hodd : Odd ((Subgroup.centralizer ({c} : Set G)).relIndex L) := by
      have hSc : S ≤ Subgroup.centralizer ({c} : Set G) := fun s hs => by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact hcS s hs
      have hdvd := Subgroup.relIndex_dvd_of_le_left (L := L) hSc
      have hSodd : Odd (S.relIndex L) :=
        Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h.isSylowTwoOf_inf.2.2)
      exact Odd.of_dvd_nat hSodd hdvd
    have hd : ∀ ℓ ∈ L, ℓ * c * ℓ⁻¹ * c⁻¹ ∈ V' := by
      intro ℓ hℓ
      have h1 := V'.inv_mem (hRL c hcR ℓ hℓ)
      convert h1 using 1
      group
    obtain ⟨w, hwV, hw⟩ := BCOrd.exists_mul_mem_centralizer_of_odd hVcomm hV2 hLV
      (fun v hv => hRV c hcR v hv) hd hodd
    have hcw : c * w ∈ T ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨T.mul_mem hcR.1 (hVT hwV), Subgroup.mem_centralizer_iff.mpr fun x hx => hw x hx⟩
    rw [hCTL, Subgroup.mem_bot] at hcw
    rw [eq_inv_of_mul_eq_one_left hcw]
    exact V'.inv_mem hwV
  have hFF2 := card_le_relIndex_mul_card hRe hRT hA
  have hle1 : (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A ≤ 4 := by
    have h1 : A ⊓ Subgroup.centralizer (V' : Set G) ≤ A ⊓ Subgroup.centralizer (R : Set G) := by
      intro x hx
      refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact hRcomm y hy x ⟨hAT hx.1, hx.2⟩
    have h2 := Subgroup.relIndex_le_of_le_left (L := A) h1 Subgroup.index_ne_zero_of_finite
    rw [← card_autOn_eq_relIndex hAV, hAeq] at h2
    exact h2.trans (hautS.trans hF4.le)
  have hle2 : Nat.card ↥(R ⊓ Subgroup.centralizer (A : Set G)) ≤ 4 :=
    (Subgroup.card_le_of_le (le_inf hCRA inf_le_right)).trans (hcardVA.trans hF4.le)
  have hR16 : Nat.card R ≤ 16 := hFF2.trans (Nat.mul_le_mul hle1 hle2)
  have hkerT : ∀ t ∈ T, (∀ k ∈ L, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 L) →
      t ∈ Subgroup.centralizer (V' : Set G) := by
    intro t ht htk
    have hcommt : ∀ x : G, x ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) ↔
        t * x = x * t := by
      intro x
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · intro hx
        exact hx t (Subgroup.mem_zpowers t)
      · intro hx y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left hx k).eq
    have hzT : Subgroup.zpowers t ≤ T := Subgroup.zpowers_le.mpr ht
    have hW1 := inf_centralizer_ne_bot_of_two (hT2.to_le hzT) (hT2.to_le hVT) (hzT.trans hTV)
      hV'ne
    have hLW : L ≤ Subgroup.normalizer ((V' ⊓ Subgroup.centralizer
        ((Subgroup.zpowers t : Subgroup G) : Set G) : Subgroup G) : Set G) := by
      intro l hl
      refine mem_normalizer_of_conj_mem fun w hw =>
        Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hLV hl) w).mp hw.1, ?_⟩
      rw [hcommt]
      have hw' := (hcommt w).mp hw.2
      have htw : t * w * t⁻¹ = w := by rw [hw', mul_inv_cancel_right]
      have hlw : l * w * l⁻¹ ∈ V' := (Subgroup.mem_normalizer_iff.mp (hLV hl) w).mp hw.1
      have hq' := Subgroup.mem_centralizer_iff.mp (hQV (htk l hl)) _ hlw
      calc t * (l * w * l⁻¹) = (t * l * t⁻¹ * l⁻¹) * (l * (t * w * t⁻¹) * l⁻¹) *
          (t * l * t⁻¹ * l⁻¹)⁻¹ * t := by group
        _ = (t * l * t⁻¹ * l⁻¹) * (l * w * l⁻¹) * (t * l * t⁻¹ * l⁻¹)⁻¹ * t := by rw [htw]
        _ = (l * w * l⁻¹) * (t * l * t⁻¹ * l⁻¹) * (t * l * t⁻¹ * l⁻¹)⁻¹ * t := by rw [← hq']
        _ = l * w * l⁻¹ * t := by group
    have hVW := hirrV _ inf_le_left hLW hW1
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((hcommt v).mp (hVW hv).2).symm
  set ρ : ↥T →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (conjQuotPCore L).comp (Subgroup.inclusion hTL) with hρ
  have hkerρ : ρ.ker ≤ R.subgroupOf T := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    rw [Subgroup.mem_subgroupOf]
    refine ⟨t.2, hkerT t t.2 fun k hk => ?_⟩
    have h1 := congrArg (fun φ : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) =>
      φ (QuotientGroup.mk (⟨k⁻¹, L.inv_mem hk⟩ : ↥L))) ht
    simp only [hρ, MonoidHom.comp_apply, MulAut.one_apply] at h1
    rw [conjQuotPCore_mk, QuotientGroup.eq] at h1
    have h2 := (mem_pCore_iff_mem_pCoreOf L _).mp h1
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    group
  have h120 : Nat.card (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) = 120 := by
    obtain ⟨e0⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 2) 2 2
      (by norm_num) (GaloisField.card 2 2 (by norm_num)) h.lie
    have := CFSG.Walter.JT.isSimpleGroup_of_psl24 e0
    have h60 := CFSG.Walter.JT.card_of_psl24 e0
    obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60
    rw [Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr (Equiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
        (by norm_num))), Nat.card_perm, Nat.card_fin]
    rfl
  have hR8 : R.relIndex T ≤ 8 := by
    have h1 : (R.subgroupOf T).index ≤ ρ.ker.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hkerρ)
    rw [Subgroup.index_ker] at h1
    have hp : IsPGroup 2 ρ.range := hT2.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hdvd : Nat.card ρ.range ∣ 120 := h120 ▸ Subgroup.card_subgroup_dvd_card ρ.range
    rw [hk] at hdvd
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have h3 := dvd_trans h16 hdvd
      norm_num at h3
    have h2 : Nat.card ρ.range ≤ 8 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
        _ = 8 := by norm_num
    exact h1.trans h2
  have hTR := Subgroup.relIndex_mul_card R T
  rw [inf_of_le_left hRT] at hTR
  rw [← hTR]
  calc R.relIndex T * Nat.card R ≤ 8 * 16 := Nat.mul_le_mul hR8 hR16
    _ = 2 ^ 7 := by norm_num

end Hyp5_0_1

theorem stmt5_1_13_bc_order_holds : Stmt5_1_13_bc_order := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m _ _ _ _ _ hZL _ V' hV' _ hnat hL hn
  subst hn
  exact m.hyp.toHyp5_0_1.card_le_two_pow_seven_of_block m.nota.2.1 hZL hV' hnat hL

end CFSG.Quasithin.H13
