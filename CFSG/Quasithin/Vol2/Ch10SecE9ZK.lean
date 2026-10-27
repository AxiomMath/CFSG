module

public import CFSG.Quasithin.Background.SmithB51SL3Coord
public import CFSG.Quasithin.Vol2.Ch10SecBL32
public import CFSG.Quasithin.Vol2.Ch10SecE9ZG

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.Quasithin.B5

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_sup_mul_card_inf (A B : Subgroup V) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have e := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient A B).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h3 : Nat.card ↥(B.subgroupOf A) = Nat.card ↥(A ⊓ B) := by
    rw [← Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have h4 : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h3] at h1
  rw [h4] at h2
  rw [h1, h2, e]
  ring

omit [Finite V] in
theorem mul_inv_mem_of_independent {A B C : Subgroup V} (hAB : A ⊓ (C ⊔ B) = C) {g : MulAut V}
    (hgA : ∀ a ∈ A, g a ∈ A) (hgB : ∀ b ∈ B, g b ∈ B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (h : g (a * b) * (a * b)⁻¹ ∈ C) : g a * a⁻¹ ∈ C := by
  have e0 : g (a * b) * (a * b)⁻¹ = (g a * a⁻¹) * (g b * b⁻¹) := by
    rw [map_mul, mul_inv_rev]
    ac_rfl
  have e : g a * a⁻¹ = g (a * b) * (a * b)⁻¹ * (g b * b⁻¹)⁻¹ := by
    rw [e0, mul_inv_cancel_right]
  rw [← hAB]
  refine ⟨A.mul_mem (hgA a ha) (A.inv_mem ha), ?_⟩
  rw [e]
  exact (C ⊔ B).mul_mem (Subgroup.mem_sup_left h)
    (Subgroup.mem_sup_right (B.inv_mem (B.mul_mem (hgB b hb) (B.inv_mem hb))))

theorem fix_order_four : ∀ A : L32.Γ, A ^ 2 ≠ 1 → A ^ 4 = 1 → ∀ u : Fin 3 → ZMod 2,
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec u = u → u ≠ 0 → ∀ w : Fin 3 → ZMod 2,
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w = w → w = 0 ∨ w = u := by
  decide +kernel

omit [Finite V] in
theorem mul_inv_mem_iff_natAct {L : Subgroup (MulAut V)} {I Z : Subgroup V}
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥L}
    (hreal : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia L I Z π)
    (f : ↥I →* Multiplicative (Fin 3 → ZMod 2)) (hfk : ∀ u : ↥I, f u = 1 ↔ (u : V) ∈ Z)
    (hfe : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥I) (hu : ((π γ : ↥L) : MulAut V) u ∈ I),
      f ⟨_, hu⟩ = natAct (StatedSL 3 (ZMod 2)) γ (f u)) (δ : ↥(StatedSL 3 (ZMod 2))) (x : ↥I) :
    ((π δ : ↥L) : MulAut V) x * (x : V)⁻¹ ∈ Z ↔ natAct (StatedSL 3 (ZMod 2)) δ (f x) = f x := by
  have hx : ((π δ : ↥L) : MulAut V) x ∈ I := hreal.2.2.2.1 (π δ) x x.2
  have hm : ((π δ : ↥L) : MulAut V) x * (x : V)⁻¹ ∈ I := I.mul_mem hx (I.inv_mem x.2)
  have e : f ⟨_, hm⟩ = f ⟨_, hx⟩ * (f x)⁻¹ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [← hfk ⟨_, hm⟩, e, hfe δ x hx]
  exact mul_inv_eq_one

theorem natAct_eq_iff (δ : ↥(StatedSL 3 (ZMod 2))) (m : Multiplicative (Fin 3 → ZMod 2)) :
    natAct (StatedSL 3 (ZMod 2)) δ m = m ↔
      ((δ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (Multiplicative.toAdd m) = Multiplicative.toAdd m := by
  unfold natAct
  constructor
  · intro h
    exact congrArg Multiplicative.toAdd h
  · intro h
    rw [h]
    rfl

omit [Finite V] in
theorem two_copies_fix {L : Subgroup (MulAut V)} {W Z : Subgroup V}
    (hDS : DirectSumOfCopies L W Z (FFModel.nat (StatedSL 3 (ZMod 2))) 2) {g y : MulAut V}
    (hgL : g ∈ L) (hg4 : orderOf g = 4) (hyL : y ∈ L) {u₀ : V} (hu₀ : u₀ ∈ W) (hu₀Z : u₀ ∉ Z)
    (hgu₀ : g u₀ * u₀⁻¹ ∈ Z) (hyu₀ : y u₀ * u₀⁻¹ ∈ Z) {w : V} (hw : w ∈ W)
    (hgw : g w * w⁻¹ ∈ Z) : y w * w⁻¹ ∈ Z := by
  obtain ⟨Ic, π₀, hZI, hind, hsup, hreal₀⟩ := hDS
  let π : ↥(StatedSL 3 (ZMod 2)) →* ↥L := π₀
  have hreal : ∀ j, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia L (Ic j) Z π := hreal₀
  have hI01 : Ic 0 ⊓ (Z ⊔ Ic 1) = Z := by
    have e : (⨆ (j : Fin 2) (_ : j ≠ 0), Ic j) = Ic 1 :=
      le_antisymm (iSup₂_le fun j hj => by rw [show j = 1 by omega])
        (le_iSup₂_of_le (f := fun (j : Fin 2) (_ : j ≠ 0) => Ic j) 1 (by decide) le_rfl)
    simpa [e] using hind 0
  have hI10 : Ic 1 ⊓ (Z ⊔ Ic 0) = Z := by
    have e : (⨆ (j : Fin 2) (_ : j ≠ 1), Ic j) = Ic 0 :=
      le_antisymm (iSup₂_le fun j hj => by rw [show j = 0 by omega])
        (le_iSup₂_of_le (f := fun (j : Fin 2) (_ : j ≠ 1) => Ic j) 0 (by decide) le_rfl)
    simpa [e] using hind 1
  have hW : W = Ic 0 ⊔ Ic 1 := by
    rw [← hsup]
    refine le_antisymm (sup_le ((hZI 0).trans le_sup_left) (iSup_le fun j => ?_))
      (sup_le (le_sup_of_le_right (le_iSup Ic 0)) (le_sup_of_le_right (le_iSup Ic 1)))
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
  have hgI : ∀ j, ∀ x ∈ Ic j, g x ∈ Ic j := fun j x hx => (hreal j).2.2.2.1 ⟨g, hgL⟩ x hx
  have hyI : ∀ j, ∀ x ∈ Ic j, y x ∈ Ic j := fun j x hx => (hreal j).2.2.2.1 ⟨y, hyL⟩ x hx
  have hcomp : ∀ {h : MulAut V}, (∀ j, ∀ x ∈ Ic j, h x ∈ Ic j) → ∀ {a b : V}, a ∈ Ic 0 →
      b ∈ Ic 1 → h (a * b) * (a * b)⁻¹ ∈ Z → h a * a⁻¹ ∈ Z ∧ h b * b⁻¹ ∈ Z := by
    intro h hh a b ha hb hab
    refine ⟨mul_inv_mem_of_independent hI01 (hh 0) (hh 1) ha hb hab,
      mul_inv_mem_of_independent hI10 (hh 1) (hh 0) hb ha (by rwa [mul_comm b a])⟩
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0)
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 3 (ZMod 2)), π γ = ⟨g, hgL⟩ := (hreal 0).1 _
  obtain ⟨η, hη⟩ : ∃ η : ↥(StatedSL 3 (ZMod 2)), π η = ⟨y, hyL⟩ := (hreal 0).1 _
  choose f hfs hfk hfe using fun j => FFC.exists_natMap (hreal j)
  set A : L32.Γ := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm γ with hA
  have hAγ : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (((γ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [← specialLinearGroupEquivStatedSL_coe, hA, MulEquiv.apply_symm_apply]
  have hoA : orderOf A = 4 := by
    rw [hA, MulEquiv.orderOf_eq, ← orderOf_injective π hinj γ, hγ, Subgroup.orderOf_mk, hg4]
  have hA2 : A ^ 2 ≠ 1 := fun h => by
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    omega
  have hA4 : A ^ 4 = 1 := hoA ▸ pow_orderOf_eq_one A
  have hg' : ((π γ : ↥L) : MulAut V) = g := by rw [hγ]
  have hy' : ((π η : ↥L) : MulAut V) = y := by rw [hη]
  have hfixg : ∀ j (x : ↥(Ic j)), g x * (x : V)⁻¹ ∈ Z ↔
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (f j x)) =
        Multiplicative.toAdd (f j x) := fun j x => by
    rw [← hg', mul_inv_mem_iff_natAct (hreal j) (f j) (hfk j) (hfe j), natAct_eq_iff, hAγ]
  have hfixy : ∀ j (x : ↥(Ic j)), y x * (x : V)⁻¹ ∈ Z ↔
      (((η : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (f j x)) =
        Multiplicative.toAdd (f j x) := fun j x => by
    rw [← hy', mul_inv_mem_iff_natAct (hreal j) (f j) (hfk j) (hfe j), natAct_eq_iff]
  rw [hW] at hu₀ hw
  obtain ⟨a₀, ha₀, a₁, ha₁, rfl⟩ := Subgroup.mem_sup.mp hu₀
  obtain ⟨hga₀, hga₁⟩ := hcomp hgI ha₀ ha₁ hgu₀
  obtain ⟨hya₀, hya₁⟩ := hcomp hyI ha₀ ha₁ hyu₀
  have key : ∀ (k : Fin 2) (a : ↥(Ic k)), (a : V) ∉ Z → g a * (a : V)⁻¹ ∈ Z →
      y a * (a : V)⁻¹ ∈ Z → ∀ j (x : ↥(Ic j)), g x * (x : V)⁻¹ ∈ Z → y x * (x : V)⁻¹ ∈ Z := by
    intro k a haZ hga hya j x hgx
    have he0 : Multiplicative.toAdd (f k a) ≠ 0 := fun h => haZ ((hfk k a).mp h)
    rcases fix_order_four A hA2 hA4 _ ((hfixg k a).mp hga) he0 _ ((hfixg j x).mp hgx) with
      h | h
    · exact (hfixy j x).mpr (by rw [h, Matrix.mulVec_zero])
    · exact (hfixy j x).mpr (by rw [h]; exact (hfixy k a).mp hya)
  have hu0 : (a₀ : V) ∉ Z ∨ (a₁ : V) ∉ Z := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hu₀Z (Z.mul_mem hcon.1 hcon.2)
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := Subgroup.mem_sup.mp hw
  obtain ⟨hgw₀, hgw₁⟩ := hcomp hgI hw₀ hw₁ hgw
  have hfin : ∀ j (x : ↥(Ic j)), g x * (x : V)⁻¹ ∈ Z → y x * (x : V)⁻¹ ∈ Z := by
    rcases hu0 with h | h
    · exact key 0 ⟨a₀, ha₀⟩ h hga₀ hya₀
    · exact key 1 ⟨a₁, ha₁⟩ h hga₁ hya₁
  have h0 := hfin 0 ⟨w₀, hw₀⟩ hgw₀
  have h1 := hfin 1 ⟨w₁, hw₁⟩ hgw₁
  have e : y (w₀ * w₁) * (w₀ * w₁)⁻¹ = (y w₀ * w₀⁻¹) * (y w₁ * w₁⁻¹) := by
    rw [map_mul, mul_inv_rev]
    ac_rfl
  rw [e]
  exact Z.mul_mem h0 h1

theorem exists_mem_fixSec_not_mem (hV2 : ∀ v : V, v ^ 2 = 1) {B : Subgroup (MulAut V)}
    (hB : IsPGroup 2 ↥B) {M N : Subgroup V} (hNM : N ≤ M) (hne : N ≠ M)
    (hBM : ∀ b ∈ B, ∀ m ∈ M, b m ∈ M) (hBN : ∀ b ∈ B, ∀ n ∈ N, b n ∈ N) :
    ∃ m ∈ M, m ∉ N ∧ ∀ b ∈ B, b m * m⁻¹ ∈ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥B → ↥M →* ↥M := fun b =>
    { toFun := fun m => ⟨(b : MulAut V) m, hBM b b.2 m m.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hφN : ∀ b, N.subgroupOf M ≤ (N.subgroupOf M).comap (φ b) := fun b m hm =>
    hBN b b.2 _ hm
  let act : ↥B → ↥M ⧸ N.subgroupOf M → ↥M ⧸ N.subgroupOf M := fun b =>
    QuotientGroup.map _ _ (φ b) (hφN b)
  have hact_mk : ∀ b (m : ↥M), act b (QuotientGroup.mk m) = QuotientGroup.mk (φ b m) :=
    fun b m => rfl
  let _ : MulAction ↥B (↥M ⧸ N.subgroupOf M) :=
    { smul := act
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H m => exact congrArg QuotientGroup.mk (Subtype.ext rfl)
      mul_smul := fun a b q => by
        induction q using QuotientGroup.induction_on with
        | H m => exact congrArg QuotientGroup.mk (Subtype.ext rfl) }
  have hQ2 : IsPGroup 2 (↥M ⧸ N.subgroupOf M) :=
    ((isPGroup_two_of_sq_eq_one hV2).to_subgroup M).to_quotient _
  have hdvd : 2 ∣ Nat.card (↥M ⧸ N.subgroupOf M) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hQ2
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      refine le_antisymm hNM fun m hm => ?_
      have h1 : Nat.card (↥M ⧸ N.subgroupOf M) = 1 := by simpa using hn
      have hsub : Subsingleton (↥M ⧸ N.subgroupOf M) := (Nat.card_eq_one_iff_unique.mp h1).1
      have h2 := (QuotientGroup.eq_one_iff (⟨m, hm⟩ : ↥M)).mp
        (Subsingleton.elim (α := ↥M ⧸ N.subgroupOf M) _ _)
      exact Subgroup.mem_subgroupOf.mp h2
    rw [hn]
    exact dvd_pow_self 2 hn0
  have h1 : (1 : ↥M ⧸ N.subgroupOf M) ∈ MulAction.fixedPoints ↥B (↥M ⧸ N.subgroupOf M) :=
    fun b => by
      show act b 1 = 1
      exact map_one _
  obtain ⟨q, hq, hq1⟩ := hB.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hdvd h1
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨m, m.2, fun hm => hq1 ?_, fun b hb => ?_⟩
  · exact ((QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_subgroupOf.mpr hm)).symm
  · have h := hq ⟨b, hb⟩
    change act ⟨b, hb⟩ (QuotientGroup.mk m) = QuotientGroup.mk m at h
    rw [hact_mk, QuotientGroup.eq] at h
    have h' : ((φ ⟨b, hb⟩ m)⁻¹ * m : ↥M) ∈ N.subgroupOf M := h
    rw [Subgroup.mem_subgroupOf] at h'
    have h'' := N.inv_mem h'
    simpa [φ, mul_comm] using h''

omit [Finite V] in
theorem exists_mul_inv_eq_of_mem_sup {L₁ L₂ : Subgroup (MulAut V)} {W C : Subgroup V}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hfixC : ∀ g ∈ L₁ ⊔ L₂, ∀ c ∈ C, g c = c)
    (hL₂W : ∀ b ∈ L₂, ∀ w ∈ W, b w * w⁻¹ ∈ C) {x : MulAut V} (hx : x ∈ L₁ ⊔ L₂) :
    ∃ y ∈ L₁, ∀ w ∈ W, (x w * w⁻¹ ∈ C ↔ y w * w⁻¹ ∈ C) := by
  obtain ⟨y, hy, b, hb, rfl⟩ := LRed4.exists_mul_of_mem_sup_comm hc hx
  refine ⟨y, hy, fun w hw => ?_⟩
  have hbw := hL₂W b hb w hw
  have e : (y * b) w * w⁻¹ = y w * w⁻¹ * (b w * w⁻¹) := by
    have h1 : y (b w * w⁻¹) = b w * w⁻¹ := hfixC y (Subgroup.mem_sup_left hy) _ hbw
    rw [map_mul, map_inv] at h1
    have h2 : (y * b) w = y (b w) := rfl
    rw [h2, ← h1]
    calc y (b w) * w⁻¹ = y (b w) * (y w)⁻¹ * (y w * w⁻¹) := by
          rw [mul_assoc, inv_mul_cancel_left]
      _ = y w * w⁻¹ * (y (b w) * (y w)⁻¹) := mul_comm _ _
  rw [e]
  constructor
  · intro h
    have h3 := C.mul_mem h (C.inv_mem hbw)
    rwa [mul_inv_cancel_right] at h3
  · intro h
    exact C.mul_mem h hbw

theorem fixSec_le_of_piece (hB48 : AsB4_8Three) (hV2 : ∀ v : V, v ^ 2 = 1)
    {L₁ L₂ J S X : Subgroup (MulAut V)} {W W' U : Subgroup V}
    (hJ : L₁ ⊔ L₂ = J) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hs : IsSimpleGroup ↥L₁)
    (hcard : Nat.card ↥L₁ = 168) (hP : B56Piece L₁ W (fixV J))
    (hCW : fixV J ≤ W) (hWW' : W ⊔ W' = ⊤) (hinf : W ⊓ W' = fixV J)
    (hinvW : ∀ g ∈ J, ∀ w ∈ W, g w ∈ W) (hinvW' : ∀ g ∈ J, ∀ w ∈ W', g w ∈ W')
    (hL₂ : commV L₂ ≤ W') (hS2 : IsPGroup 2 ↥S) (hXJ : X ≤ J)
    (hUL : U ≤ commV L₁)
    (hU8 : Nat.card ↥(U ⊔ fixV J) = 8 * Nat.card ↥(fixV J))
    (hSU : ∀ s ∈ S, ∀ u ∈ U ⊔ fixV J, s u ∈ U ⊔ fixV J)
    (hSC : ∀ s ∈ S, ∀ c ∈ fixV J, s c ∈ fixV J)
    (hpt : fixSec S (U ⊔ fixV J) (fixV J) ≤
      fixSec X (U ⊔ fixV J) (fixV J))
    {g : MulAut V} (hgL : g ∈ L₁) (hgS : g ∈ S) (hg4 : orderOf g = 4) :
    fixSec S W (fixV J) ≤ fixSec X W (fixV J) := by
  subst hJ
  set C := fixV (L₁ ⊔ L₂) with hC
  have hfixC : ∀ x ∈ L₁ ⊔ L₂, ∀ c ∈ C, x c = c := fun x hx c hc' => mem_fixV.mp hc' x hx
  have hL₂W : ∀ b ∈ L₂, ∀ w ∈ W, b w * w⁻¹ ∈ C := fun b hb w hw => by
    rw [← hinf]
    exact ⟨W.mul_mem (hinvW b (Subgroup.mem_sup_right hb) w hw) (W.inv_mem hw),
      hL₂ (Subgroup.subset_closure ⟨b, hb, w, rfl⟩)⟩
  have hUW : U ⊔ C ≤ W := sup_le (hUL.trans ?_) hCW
  swap
  · rcases hP with ⟨hWeq, -⟩ | ⟨hWeq, -⟩ | ⟨-, hcW, -⟩
    · exact hWeq ▸ le_sup_left
    · exact hWeq ▸ le_sup_left
    · exact hcW
  have hinvW₁ : ∀ l ∈ L₁, ∀ w ∈ W, l w ∈ W := fun l hl => hinvW l (Subgroup.mem_sup_left hl)
  have hinvW'₁ : ∀ l ∈ L₁, ∀ w ∈ W', l w ∈ W' := fun l hl => hinvW' l (Subgroup.mem_sup_left hl)
  have ha2 : orderOf (g ^ 2) = 2 := by
    rw [orderOf_pow' g two_ne_zero, hg4]
    norm_num
  rintro w ⟨hw, hwS⟩
  refine ⟨hw, fun x hx => ?_⟩
  rcases card_commV_sup_of_piece hcard hP hWW' hinf hinvW'₁ with h8 | ⟨hWeq, hDS⟩
  ·
    have hUeq : U ⊔ C = commV L₁ ⊔ C :=
      Subgroup.eq_of_le_of_card_ge (sup_le_sup_right hUL C) (by rw [h8, hU8])
    have hwU : w ∈ U ⊔ C := by
      rw [hUeq]
      exact mem_commV_sup_of_piece hB48 hV2 hs hP hCW hWW' hinf hinvW₁ hinvW'₁
        (fun l hl => hfixC l (Subgroup.mem_sup_left hl)) (L₁.pow_mem hgL 2) ha2 hw
        (hwS _ (S.pow_mem hgS 2))
    exact (hpt ⟨hwU, hwS⟩).2 x hx
  ·
    have hne : C ≠ U ⊔ C := by
      intro h
      have h1 : Nat.card ↥C = Nat.card ↥(U ⊔ C) := by rw [← h]
      have hpos : 0 < Nat.card ↥C := Nat.card_pos
      omega
    obtain ⟨u₀, hu₀, hu₀C, hu₀S⟩ := exists_mem_fixSec_not_mem hV2 hS2 le_sup_right hne hSU hSC
    have hu₀X := (hpt ⟨hu₀, hu₀S⟩).2
    obtain ⟨y, hyL, hy⟩ := exists_mul_inv_eq_of_mem_sup hc hfixC hL₂W (hXJ hx)
    rw [hy w hw]
    exact two_copies_fix hDS hgL hg4 hyL (hUW hu₀) hu₀C (hu₀S g hgS) ((hy u₀ (hUW hu₀)).mp
      (hu₀X x hx)) hw (hwS g hgS)

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
