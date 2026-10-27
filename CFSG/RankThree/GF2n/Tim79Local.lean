module

public import CFSG.RankThree.GF2n.Tim79Defs
public import CFSG.RankThree.GF2n.Tim79Pair
public import CFSG.RankThree.GF2n.Tim78Lemma218
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement Matrix

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld CFSG.Timmesfeld.RankOne

variable {G : Type} [Group G]

theorem Hyp79.toHyp218 {M V Q : Subgroup G} (H : Hyp79 M V Q) {g : G}
    (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) :
    Tim78.Hyp218 M V Q (Q ⊓ Subgroup.centralizer (V : Set G)) (V ⊔ conjSubgroup g V) g :=
  ⟨H.maxLocal, H.fitting, H.maxAb, H.sq_eq_one, H.ti, hgV, hgQ, H.hQ, rfl, rfl⟩

theorem Hyp79.V_le_Q {M V Q : Subgroup G} (H : Hyp79 M V Q) : V ≤ Q :=
  H.hQ ▸ Tim78.le_inSubgroup_pCore H.maxAb.prop.1 H.maxAb.prop.2.1
    (fun x => ⟨1, Subtype.ext (by simpa using H.sq_eq_one x x.2)⟩)

theorem Hyp79.exists_opposite {M V Q : Subgroup G} (H : Hyp79 M V Q) :
    ∃ g : G, conjSubgroup g V ≠ V ∧ conjSubgroup g V ≤ Q := by
  by_contra hcon
  push Not at hcon
  refine H.ne (le_antisymm (H.gen.le.trans (iSup₂_le fun g hg => ?_)) H.V_le_Q)
  by_cases hgV : conjSubgroup g V = V
  · exact hgV.le
  · exact absurd hg (hcon g hgV)

theorem Hyp79.special [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) :
    ⁅Q, Q⁆ = V ∧ Q ⊓ Subgroup.centralizer (Q : Set G) = V ∧ inSubgroup frattini Q = V := by
  obtain ⟨g, hgV, hgQ⟩ := H.exists_opposite
  obtain ⟨-, -, -, -, hΦ, hZ, hQ', -⟩ := (H.toHyp218 hgV hgQ).conclusions H.q4 rfl
  exact ⟨hQ', hZ, hΦ⟩

private theorem H_le_normalizer_W [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) :
    Q ⊔ conjSubgroup g Q ≤ Subgroup.normalizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G) := by
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  obtain ⟨y, hy⟩ := h.exists_isOpp
  obtain ⟨x, hxW, hxV⟩ := h.exists_conj_eq_V1 hy
  exact sup_le (hPQ.symm.le.trans h.P_le_normalizer_W)
    ((Subgroup.map_mono hPQ.symm.le).trans (h.Pg_le_normalizer_W hxW hxV))

theorem Hyp79.L_facts [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) :
    (V ⊔ conjSubgroup g V ≤ Q ⊓ conjSubgroup g Q) ∧
    (∀ x ∈ Q ⊓ conjSubgroup g Q, ∀ y ∈ Q ⊓ conjSubgroup g Q, x * y = y * x) ∧
    (∀ x ∈ Q ⊓ conjSubgroup g Q, x ^ 2 = 1) ∧
    (∀ h ∈ Q ⊔ conjSubgroup g Q, ∀ l ∈ Q ⊓ conjSubgroup g Q, ⁅h, l⁆ ∈ V ⊔ conjSubgroup g V) := by
  obtain ⟨hQ', -, -⟩ := H.special
  have h := H.toHyp218 hgV hgQ
  obtain ⟨hVQg, -, -, hPQ, -⟩ := h.conclusions H.q4 rfl
  have hinf : V ⊓ conjSubgroup g V = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hgV
  have hQg' : ⁅conjSubgroup g Q, conjSubgroup g Q⁆ = conjSubgroup g V := by
    rw [← hQ']
    exact (Subgroup.map_commutator _ _ _).symm
  have hsq : ∀ a ∈ Q, a ^ 2 ∈ V := fun a ha => h.sq_mem (hPQ.symm.le ha)
  have hsq' : ∀ a ∈ conjSubgroup g Q, a ^ 2 ∈ conjSubgroup g V := by
    intro a ha
    rw [mem_conjSubgroup] at ha ⊢
    rw [show g⁻¹ * a ^ 2 * g = (g⁻¹ * a * g) ^ 2 by rw [pow_two, pow_two]; group]
    exact hsq _ ha
  have hVU : V ⊔ conjSubgroup g V ≤ Q ⊓ conjSubgroup g Q :=
    sup_le (le_inf H.V_le_Q hVQg) (le_inf hgQ (Subgroup.map_mono H.V_le_Q))
  refine ⟨hVU, ?_, ?_, ?_⟩
  · intro x hx y hy
    have h1 : ⁅x, y⁆ ∈ V := hQ' ▸ Subgroup.commutator_mem_commutator hx.1 hy.1
    have h2 : ⁅x, y⁆ ∈ conjSubgroup g V := hQg' ▸ Subgroup.commutator_mem_commutator hx.2 hy.2
    have h3 : ⁅x, y⁆ ∈ V ⊓ conjSubgroup g V := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  · intro x hx
    have h3 : x ^ 2 ∈ V ⊓ conjSubgroup g V := ⟨hsq x hx.1, hsq' x hx.2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact h3
  ·
    have hHW := H_le_normalizer_W H hgV hgQ
    let T : Subgroup G :=
      { carrier := {h | h ∈ Subgroup.normalizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G) ∧
          ∀ l ∈ Q ⊓ conjSubgroup g Q, ⁅h, l⁆ ∈ V ⊔ conjSubgroup g V}
        mul_mem' := fun {a b} ha hb => by
          refine ⟨mul_mem ha.1 hb.1, fun l hl => ?_⟩
          have e : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          refine mul_mem ?_ (ha.2 l hl)
          exact (Subgroup.mem_normalizer_iff.mp ha.1 _).mp (hb.2 l hl) |> fun h' => by
            simpa [mul_assoc] using h'
        one_mem' := ⟨one_mem _, fun l _ => by simp⟩
        inv_mem' := fun {a} ha => by
          refine ⟨inv_mem ha.1, fun l hl => ?_⟩
          have e : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a := by
            simp only [commutatorElement_def]
            group
          rw [e]
          have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem ha.1) _).mp (inv_mem (ha.2 l hl))
          simpa [mul_assoc] using h1 }
    have hQT : Q ≤ T := fun q hq => ⟨hHW (Subgroup.mem_sup_left hq), fun l hl =>
      Subgroup.mem_sup_left (hQ' ▸ Subgroup.commutator_mem_commutator hq hl.1)⟩
    have hQgT : conjSubgroup g Q ≤ T := fun q hq => ⟨hHW (Subgroup.mem_sup_right hq),
      fun l hl => Subgroup.mem_sup_right (hQg' ▸ Subgroup.commutator_mem_commutator hq hl.2)⟩
    exact fun h' hh' l hl => (sup_le hQT hQgT hh').2 l hl

structure NatData (V Q : Subgroup G) (g : G) (n : ℕ) where
  φ : ↥(Q ⊔ conjSubgroup g Q) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  ψ : ↥(V ⊔ conjSubgroup g V) ≃* Multiplicative (Fin 2 → GaloisField 2 n)
  surj : Function.Surjective φ
  ker : φ.ker = (Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)).subgroupOf
    (Q ⊔ conjSubgroup g Q)
  compat : ∀ (z : ↥(Q ⊔ conjSubgroup g Q)) (w w' : ↥(V ⊔ conjSubgroup g V)),
    (w' : G) = (z : G) * w * (z : G)⁻¹ →
      Multiplicative.toAdd (ψ w') =
        (φ z : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ Multiplicative.toAdd (ψ w)
  upper : (Q.subgroupOf (Q ⊔ conjSubgroup g Q)).map φ = upperUnipotent (GaloisField 2 n)
  lower : ((conjSubgroup g Q).subgroupOf (Q ⊔ conjSubgroup g Q)).map φ =
    lowerUnipotent (GaloisField 2 n)
  two : IsPGroup 2 ((Q ⊔ conjSubgroup g Q) ⊓
    Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G) : Subgroup G)
  hV : ∀ w : ↥(V ⊔ conjSubgroup g V), (w : G) ∈ V ↔ Multiplicative.toAdd (ψ w) 1 = 0
  norm : Q ⊔ conjSubgroup g Q ≤ Subgroup.normalizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)

theorem exists_natData [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card V = 2 ^ n ∧ Nonempty (NatData V Q g n) := by
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  obtain ⟨y, hy⟩ := h.exists_isOpp
  obtain ⟨x, hxW, hxV⟩ := h.exists_conj_eq_V1 hy
  obtain ⟨n, hn2, hVn, φ, ψ, hφs, hφker, hcompat, hφP, hφPg, hL2, hVψ⟩ :=
    h.exists_natural hxW hxV hy H.q4 (H := Q ⊔ conjSubgroup g Q) (by rw [hPQ])
  rw [hPQ] at hφP hφPg
  exact ⟨n, hn2, hVn, ⟨⟨φ, ψ, hφs, hφker, hcompat, hφP, hφPg, hL2, hVψ,
    H_le_normalizer_W H hgV hgQ⟩⟩⟩

private theorem diagElt_pow {K : Type*} [Field K] (c : Kˣ) (m : ℕ) :
    ARS.NaturalModule.diagElt c ^ m = ARS.NaturalModule.diagElt (c ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, ARS.NaturalModule.diagElt_one]
  | succ m ih => rw [pow_succ, pow_succ, ih, ARS.NaturalModule.diagElt_mul_diagElt]

private theorem diagElt_injective {K : Type*} [Field K] :
    Function.Injective (ARS.NaturalModule.diagElt : Kˣ → Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro a b hab
  have h00 := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) K =>
    (m : Matrix (Fin 2) (Fin 2) K) 0 0) hab
  simp only [ARS.NaturalModule.coe_diagElt, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h00
  exact Units.ext h00

private theorem orderOf_diagElt {K : Type*} [Field K] (c : Kˣ) :
    orderOf (ARS.NaturalModule.diagElt c) = orderOf c :=
  orderOf_eq_orderOf_iff.mpr fun m => by
    rw [diagElt_pow, ← ARS.NaturalModule.diagElt_one (K := K), diagElt_injective.eq_iff]

namespace NatData

variable {V Q : Subgroup G} {g : G} {n : ℕ} (N : NatData V Q g n)

open scoped _root_.Classical in
private noncomputable def gam : G → GaloisField 2 n := fun v =>
  if h : v ∈ V ⊔ conjSubgroup g V then Multiplicative.toAdd (N.ψ ⟨v, h⟩) 0 else 0

open scoped _root_.Classical in
private noncomputable def psiU : G → GaloisField 2 n := fun u =>
  if h : u ∈ V ⊔ conjSubgroup g V then Multiplicative.toAdd (N.ψ ⟨u, h⟩) 1 else 0

private theorem gam_eq {v : G} (h : v ∈ V ⊔ conjSubgroup g V) :
    N.gam v = Multiplicative.toAdd (N.ψ ⟨v, h⟩) 0 := by
  simp [gam, h]

private theorem psiU_eq {v : G} (h : v ∈ V ⊔ conjSubgroup g V) :
    N.psiU v = Multiplicative.toAdd (N.ψ ⟨v, h⟩) 1 := by
  simp [psiU, h]

private theorem coord_mul {a b : G} (ha : a ∈ V ⊔ conjSubgroup g V) (hb : b ∈ V ⊔ conjSubgroup g V)
    (i : Fin 2) : Multiplicative.toAdd (N.ψ ⟨a * b, mul_mem ha hb⟩) i =
      Multiplicative.toAdd (N.ψ ⟨a, ha⟩) i + Multiplicative.toAdd (N.ψ ⟨b, hb⟩) i := by
  have h : N.ψ ⟨a * b, mul_mem ha hb⟩ = N.ψ ⟨a, ha⟩ * N.ψ ⟨b, hb⟩ := by
    rw [← map_mul]
    rfl
  rw [h, toAdd_mul, Pi.add_apply]

private theorem eq_one_of_toAdd_eq_zero {a : G} (ha : a ∈ V ⊔ conjSubgroup g V)
    (h : Multiplicative.toAdd (N.ψ ⟨a, ha⟩) = 0) : a = 1 := by
  have h1 : N.ψ ⟨a, ha⟩ = 1 := Multiplicative.toAdd.injective (by rw [h]; rfl)
  have h2 : (⟨a, ha⟩ : ↥(V ⊔ conjSubgroup g V)) = 1 := N.ψ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

private theorem gam_add {a b : G} (ha : a ∈ V) (hb : b ∈ V) :
    N.gam (a * b) = N.gam a + N.gam b := by
  have ha' : a ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_left ha
  have hb' : b ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_left hb
  rw [N.gam_eq (mul_mem ha' hb'), N.gam_eq ha', N.gam_eq hb', N.coord_mul ha' hb']

private theorem gam_inj {a : G} (ha : a ∈ V) (h : N.gam a = 0) : a = 1 := by
  have ha' : a ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_left ha
  have h1 := (N.hV ⟨a, ha'⟩).mp ha
  refine N.eq_one_of_toAdd_eq_zero ha' (funext fun i => ?_)
  fin_cases i
  · rw [N.gam_eq ha'] at h
    exact h
  · exact h1

private theorem gam_surj (s : GaloisField 2 n) : ∃ a ∈ V, N.gam a = s := by
  let w : ↥(V ⊔ conjSubgroup g V) := N.ψ.symm (Multiplicative.ofAdd ![s, 0])
  have hw : Multiplicative.toAdd (N.ψ w) = ![s, 0] := by
    simp [w]
  have hwV : (w : G) ∈ V := (N.hV w).mpr (by rw [hw]; rfl)
  refine ⟨w, hwV, ?_⟩
  rw [N.gam_eq w.2]
  show Multiplicative.toAdd (N.ψ w) 0 = s
  rw [hw]
  rfl

private theorem coord_zero_of_mem_U
    (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q)
    (w : ↥(V ⊔ conjSubgroup g V)) (hw : (w : G) ∈ conjSubgroup g V) :
    Multiplicative.toAdd (N.ψ w) 0 = 0 := by
  have hv : ∀ t : GaloisField 2 n, (lowerElt (GaloisField 2 n) t :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ Multiplicative.toAdd (N.ψ w) =
        Multiplicative.toAdd (N.ψ w) := by
    intro t
    have hl : lowerElt (GaloisField 2 n) t ∈ lowerUnipotent (GaloisField 2 n) :=
      (mem_lowerUnipotent_iff _).mpr ⟨t, rfl⟩
    rw [← N.lower] at hl
    obtain ⟨z, hz, hzt⟩ := Subgroup.mem_map.mp hl
    have hzQ : (z : G) ∈ conjSubgroup g Q := Subgroup.mem_subgroupOf.mp hz
    have hcomm := hUc z hzQ w hw
    have h1 := N.compat z w w (by rw [hcomm, mul_inv_cancel_right])
    rw [hzt] at h1
    exact h1.symm
  exact (ARS.NaturalModule.forall_lowerElt_mulVec_eq_iff _).mp hv

private theorem mem_U_iff [Finite G] (hVn : Nat.card V = 2 ^ n) (hn : n ≠ 0)
    (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q)
    (w : ↥(V ⊔ conjSubgroup g V)) :
    (w : G) ∈ conjSubgroup g V ↔ Multiplicative.toAdd (N.ψ w) 0 = 0 := by
  refine ⟨N.coord_zero_of_mem_U hUc w, fun hw0 => ?_⟩
  have hUW : conjSubgroup g V ≤ V ⊔ conjSubgroup g V := le_sup_right
  let f : ↥(conjSubgroup g V) → GaloisField 2 n := fun u =>
    Multiplicative.toAdd (N.ψ ⟨u, hUW u.2⟩) 1
  have hext : ∀ a b : ↥(V ⊔ conjSubgroup g V), Multiplicative.toAdd (N.ψ a) 0 = 0 →
      Multiplicative.toAdd (N.ψ b) 0 = 0 → Multiplicative.toAdd (N.ψ a) 1 =
        Multiplicative.toAdd (N.ψ b) 1 → a = b := by
    intro a b ha hb hab
    apply N.ψ.injective
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact ha.trans hb.symm
    · exact hab
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : ↥(V ⊔ conjSubgroup g V) => (x : G)) (hext ⟨a, hUW a.2⟩ ⟨b, hUW b.2⟩
      (N.coord_zero_of_mem_U hUc _ a.2) (N.coord_zero_of_mem_U hUc _ b.2) hab)
  have hcard : Nat.card (conjSubgroup g V) = Nat.card (GaloisField 2 n) := by
    rw [card_conjSubgroup, hVn, GaloisField.card 2 n hn]
  have hf_bij : Function.Bijective f := hf_inj.bijective_of_nat_card_le hcard.ge
  obtain ⟨u, hu⟩ := hf_bij.2 (Multiplicative.toAdd (N.ψ w) 1)
  have h1 : (⟨u, hUW u.2⟩ : ↥(V ⊔ conjSubgroup g V)) = w :=
    hext _ _ (N.coord_zero_of_mem_U hUc _ u.2) hw0 hu
  rw [← h1]
  exact u.2

private theorem coord_inv {a : G} (ha : a ∈ V ⊔ conjSubgroup g V) (i : Fin 2) :
    Multiplicative.toAdd (N.ψ ⟨a⁻¹, inv_mem ha⟩) i = - Multiplicative.toAdd (N.ψ ⟨a, ha⟩) i := by
  have h : N.ψ ⟨a⁻¹, inv_mem ha⟩ = (N.ψ ⟨a, ha⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [h, toAdd_inv, Pi.neg_apply]

private theorem psiU_add {a b : G} (ha : a ∈ conjSubgroup g V) (hb : b ∈ conjSubgroup g V) :
    N.psiU (a * b) = N.psiU a + N.psiU b := by
  have ha' : a ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_right ha
  have hb' : b ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_right hb
  rw [N.psiU_eq (mul_mem ha' hb'), N.psiU_eq ha', N.psiU_eq hb', N.coord_mul ha' hb']

private theorem psiU_inj (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q)
    {a : G} (ha : a ∈ conjSubgroup g V) (h : N.psiU a = 0) : a = 1 := by
  have ha' : a ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_right ha
  refine N.eq_one_of_toAdd_eq_zero ha' (funext fun i => ?_)
  fin_cases i
  · exact N.coord_zero_of_mem_U hUc ⟨a, ha'⟩ ha
  · rw [N.psiU_eq ha'] at h
    exact h

private theorem psiU_surj [Finite G] (hVn : Nat.card V = 2 ^ n) (hn : n ≠ 0)
    (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q) (s : GaloisField 2 n) :
    ∃ a ∈ conjSubgroup g V, N.psiU a = s := by
  let w : ↥(V ⊔ conjSubgroup g V) := N.ψ.symm (Multiplicative.ofAdd ![0, s])
  have hw : Multiplicative.toAdd (N.ψ w) = ![0, s] := by
    simp [w]
  have hwU : (w : G) ∈ conjSubgroup g V := (N.mem_U_iff hVn hn hUc w).mpr (by rw [hw]; rfl)
  refine ⟨w, hwU, ?_⟩
  rw [N.psiU_eq w.2]
  show Multiplicative.toAdd (N.ψ w) 1 = s
  rw [hw]
  rfl

private theorem exists_t {y : G} (hy : y ∈ Q) :
    ∃ t : GaloisField 2 n, N.φ ⟨y, Subgroup.mem_sup_left hy⟩ = upperElt (GaloisField 2 n) t := by
  have h : N.φ ⟨y, Subgroup.mem_sup_left hy⟩ ∈ upperUnipotent (GaloisField 2 n) := by
    rw [← N.upper]
    exact Subgroup.mem_map_of_mem N.φ (Subgroup.mem_subgroupOf.mpr hy)
  exact (mem_upperUnipotent_iff _).mp h

open scoped _root_.Classical in
private noncomputable def tt : G → GaloisField 2 n := fun y =>
  if hy : y ∈ Q then Classical.choose (N.exists_t hy) else 0

private theorem φ_eq {y : G} (hy : y ∈ Q) :
    N.φ ⟨y, Subgroup.mem_sup_left hy⟩ = upperElt (GaloisField 2 n) (N.tt y) := by
  simp only [tt, dif_pos hy]
  exact Classical.choose_spec (N.exists_t hy)

private theorem tt_add {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) : N.tt (a * b) = N.tt a + N.tt b := by
  apply upperElt_injective (GaloisField 2 n)
  rw [← upperElt_mul, ← N.φ_eq ha, ← N.φ_eq hb, ← N.φ_eq (mul_mem ha hb), ← map_mul]
  rfl

private theorem tt_surj (s : GaloisField 2 n) : ∃ a ∈ Q, N.tt a = s := by
  have h : upperElt (GaloisField 2 n) s ∈ (Q.subgroupOf (Q ⊔ conjSubgroup g Q)).map N.φ := by
    rw [N.upper]
    exact (mem_upperUnipotent_iff _).mpr ⟨s, rfl⟩
  obtain ⟨z, hz, hzs⟩ := Subgroup.mem_map.mp h
  have hzQ : (z : G) ∈ Q := Subgroup.mem_subgroupOf.mp hz
  refine ⟨z, hzQ, ?_⟩
  apply upperElt_injective (GaloisField 2 n)
  rw [← N.φ_eq hzQ]
  exact hzs

private theorem tt_ker [Finite G] (hVn : Nat.card V = 2 ^ n) (hn : n ≠ 0)
    (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q) {a : G} (ha : a ∈ Q) :
    N.tt a = 0 ↔ a ∈ Subgroup.centralizer (conjSubgroup g V : Set G) := by
  have haH : a ∈ Q ⊔ conjSubgroup g Q := Subgroup.mem_sup_left ha
  constructor
  · intro h0
    have h1 : (⟨a, haH⟩ : ↥(Q ⊔ conjSubgroup g Q)) ∈ N.φ.ker := by
      rw [MonoidHom.mem_ker, N.φ_eq ha, h0, upperElt_zero]
    rw [N.ker, Subgroup.mem_subgroupOf] at h1
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp h1 u (Subgroup.mem_sup_right hu)
  · intro hc
    obtain ⟨u₀, hu₀, hψ₀⟩ := N.psiU_surj hVn hn hUc 1
    have hu₀W : u₀ ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_right hu₀
    have hcomm : a * u₀ = u₀ * a := (Subgroup.mem_centralizer_iff.mp hc u₀ hu₀).symm
    have h1 := N.compat ⟨a, haH⟩ ⟨u₀, hu₀W⟩ ⟨u₀, hu₀W⟩ (by
      show u₀ = a * u₀ * a⁻¹
      rw [hcomm, mul_inv_cancel_right])
    rw [N.φ_eq ha, ARS.NaturalModule.upperElt_mulVec] at h1
    have h2 := congrFun h1 0
    have h3 : Multiplicative.toAdd (N.ψ ⟨u₀, hu₀W⟩) 0 = 0 :=
      N.coord_zero_of_mem_U hUc ⟨u₀, hu₀W⟩ hu₀
    have h4 : Multiplicative.toAdd (N.ψ ⟨u₀, hu₀W⟩) 1 = 1 := by
      rw [← N.psiU_eq hu₀W, hψ₀]
    simp only [Matrix.cons_val_zero, h3, h4, mul_one, zero_add] at h2
    exact h2.symm

private theorem comm_aux [Finite G] (hVn : Nat.card V = 2 ^ n) (hn : n ≠ 0)
    (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q) {y u : G}
    (hy : y ∈ Q) (hu : u ∈ conjSubgroup g V) :
    ⁅y, u⁆ ∈ V ∧ N.gam ⁅y, u⁆ = N.tt y * N.psiU u := by
  have huW : u ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_right hu
  have hyH : y ∈ Q ⊔ conjSubgroup g Q := Subgroup.mem_sup_left hy
  have hyu : y * u * y⁻¹ ∈ V ⊔ conjSubgroup g V :=
    (Subgroup.mem_normalizer_iff.mp (N.norm hyH) u).mp huW
  have h1 := N.compat ⟨y, hyH⟩ ⟨u, huW⟩ ⟨y * u * y⁻¹, hyu⟩ rfl
  rw [N.φ_eq hy, ARS.NaturalModule.upperElt_mulVec] at h1
  have hu0 : Multiplicative.toAdd (N.ψ ⟨u, huW⟩) 0 = 0 := N.coord_zero_of_mem_U hUc ⟨u, huW⟩ hu
  have hcomm : ⁅y, u⁆ = y * u * y⁻¹ * u⁻¹ := commutatorElement_def y u
  have hcW : y * u * y⁻¹ * u⁻¹ ∈ V ⊔ conjSubgroup g V := mul_mem hyu (inv_mem huW)
  have c0 := N.coord_mul hyu (inv_mem huW) 0
  have c1 := N.coord_mul hyu (inv_mem huW) 1
  rw [N.coord_inv huW] at c0 c1
  have e0 : Multiplicative.toAdd (N.ψ ⟨y * u * y⁻¹, hyu⟩) 0 =
      N.tt y * Multiplicative.toAdd (N.ψ ⟨u, huW⟩) 1 := by
    have := congrFun h1 0
    simpa [hu0] using this
  have e1 : Multiplicative.toAdd (N.ψ ⟨y * u * y⁻¹, hyu⟩) 1 =
      Multiplicative.toAdd (N.ψ ⟨u, huW⟩) 1 := by
    have := congrFun h1 1
    simpa using this
  have hV1 : Multiplicative.toAdd (N.ψ ⟨y * u * y⁻¹ * u⁻¹, hcW⟩) 1 = 0 := by
    rw [c1, e1, add_neg_cancel]
  refine ⟨?_, ?_⟩
  · rw [hcomm]
    exact (N.hV ⟨_, hcW⟩).mpr hV1
  · rw [hcomm, N.gam_eq hcW, c0, e0, hu0, neg_zero, add_zero, N.psiU_eq huW]

private theorem conj_coord {z : ↥(Q ⊔ conjSubgroup g Q)} {c : (GaloisField 2 n)ˣ}
    (hz : N.φ z = ARS.NaturalModule.diagElt c) {w : G} (hw : w ∈ V ⊔ conjSubgroup g V) :
    ∃ hw' : (z : G) * w * (z : G)⁻¹ ∈ V ⊔ conjSubgroup g V,
      Multiplicative.toAdd (N.ψ ⟨(z : G) * w * (z : G)⁻¹, hw'⟩) =
        ![(c : GaloisField 2 n) * Multiplicative.toAdd (N.ψ ⟨w, hw⟩) 0,
          ((c⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) *
            Multiplicative.toAdd (N.ψ ⟨w, hw⟩) 1] := by
  have hw' : (z : G) * w * (z : G)⁻¹ ∈ V ⊔ conjSubgroup g V :=
    (Subgroup.mem_normalizer_iff.mp (N.norm z.2) w).mp hw
  refine ⟨hw', ?_⟩
  have h1 := N.compat z ⟨w, hw⟩ ⟨_, hw'⟩ rfl
  rw [hz, ARS.NaturalModule.diagElt_mulVec] at h1
  exact h1

private theorem exists_torus [Finite G] {M : Subgroup G}
    (hMV : Subgroup.normalizer (V : Set G) = M) (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hVn : Nat.card V = 2 ^ n) (hn : n ≠ 0)
    (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q) :
    ∃ (τ : G) (a : GaloisField 2 n), τ ∈ M ∧ τ ∈ Q ⊔ conjSubgroup g Q ∧
      τ ∈ Subgroup.normalizer (conjSubgroup g V : Set G) ∧
      orderOf τ = 2 ^ n - 1 ∧ orderOf a = 2 ^ n - 1 ∧
      (∀ v ∈ V, N.gam (τ * v * τ⁻¹) = a * N.gam v) ∧
      (∀ u ∈ conjSubgroup g V, N.psiU (τ * u * τ⁻¹) = a⁻¹ * N.psiU u) ∧
      (∀ y ∈ Q, N.tt (τ * y * τ⁻¹) = a ^ 2 * N.tt y) := by
  classical
  have hKcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn)
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField 2 n)ˣ)
  rw [Nat.card_units, hKcard] at hc
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, hn⟩) odd_one
  have hq1' : 0 < 2 ^ n - 1 := by omega
  obtain ⟨z, hz⟩ := N.surj (ARS.NaturalModule.diagElt c)
  have hdiag : orderOf (N.φ z) = 2 ^ n - 1 := by
    rw [hz, orderOf_diagElt, hc]
  have hdvd : 2 ^ n - 1 ∣ orderOf z := hdiag ▸ orderOf_map_dvd N.φ z
  have hzq : z ^ (2 ^ n - 1) ∈ (Subgroup.centralizer
      ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)).subgroupOf (Q ⊔ conjSubgroup g Q) := by
    rw [← N.ker, MonoidHom.mem_ker, map_pow, ← hdiag, pow_orderOf_eq_one]
  obtain ⟨j, hj⟩ := N.two ⟨((z ^ (2 ^ n - 1) : ↥(Q ⊔ conjSubgroup g Q)) : G),
    ⟨(z ^ (2 ^ n - 1)).2, Subgroup.mem_subgroupOf.mp hzq⟩⟩
  have hj' : z ^ ((2 ^ n - 1) * 2 ^ j) = 1 := by
    rw [pow_mul]
    apply Subtype.ext
    have := congrArg Subtype.val hj
    simpa using this
  have hdvd2 : orderOf z ∣ (2 ^ n - 1) * 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  obtain ⟨d, hd⟩ := hdvd
  have hd2 : d ∣ 2 ^ j := by
    rw [hd] at hdvd2
    exact (Nat.mul_dvd_mul_iff_left hq1').mp hdvd2
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  have hzV : ∀ v ∈ V, (z : G) * v * (z : G)⁻¹ ∈ V := by
    intro v hv
    have hvW : v ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_left hv
    obtain ⟨hw', hψ⟩ := N.conj_coord hz hvW
    have h1 := (N.hV ⟨v, hvW⟩).mp hv
    refine (N.hV ⟨_, hw'⟩).mpr ?_
    rw [hψ]
    simp [h1]
  have hzM : (z : G) ∈ M := hMV ▸ Subgroup.mem_normalizer_fintype hzV
  set τ' : ↥(Q ⊔ conjSubgroup g Q) := z ^ 2 ^ b with hτ'
  have hτ'ord : orderOf τ' = 2 ^ n - 1 := by
    rw [hτ', orderOf_pow' z (by positivity), hd, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (by positivity)]
  set a : (GaloisField 2 n)ˣ := c ^ 2 ^ b with ha
  have hτ'φ : N.φ τ' = ARS.NaturalModule.diagElt a := by
    rw [hτ', map_pow, hz, ha, diagElt_pow]
  have hcop : Nat.Coprime (2 ^ b) (2 ^ n - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have haord : orderOf (a : GaloisField 2 n) = 2 ^ n - 1 := by
    rw [orderOf_units, ha, orderOf_pow' c (by positivity), hc, Nat.Coprime.gcd_eq_one hcop.symm,
      Nat.div_one]
  have hinvcoe : ((a⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) = (a : GaloisField 2 n)⁻¹ :=
    Units.val_inv_eq_inv_val a
  have hτM : ((τ' : ↥(Q ⊔ conjSubgroup g Q)) : G) ∈ M := by
    rw [hτ', Subgroup.coe_pow]
    exact M.pow_mem hzM _
  have hVact : ∀ v ∈ V, ((τ' : G) * v * (τ' : G)⁻¹ ∈ V) ∧
      N.gam ((τ' : G) * v * (τ' : G)⁻¹) = (a : GaloisField 2 n) * N.gam v := by
    intro v hv
    have hvW : v ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_left hv
    obtain ⟨hw', hψ⟩ := N.conj_coord hτ'φ hvW
    have h1 := (N.hV ⟨v, hvW⟩).mp hv
    refine ⟨(N.hV ⟨_, hw'⟩).mpr (by rw [hψ]; simp [h1]), ?_⟩
    rw [N.gam_eq hw', N.gam_eq hvW, hψ]
    simp
  have hUact : ∀ u ∈ conjSubgroup g V, ((τ' : G) * u * (τ' : G)⁻¹ ∈ conjSubgroup g V) ∧
      N.psiU ((τ' : G) * u * (τ' : G)⁻¹) = (a : GaloisField 2 n)⁻¹ * N.psiU u := by
    intro u hu
    have huW : u ∈ V ⊔ conjSubgroup g V := Subgroup.mem_sup_right hu
    obtain ⟨hw', hψ⟩ := N.conj_coord hτ'φ huW
    have h0 := N.coord_zero_of_mem_U hUc ⟨u, huW⟩ hu
    refine ⟨(N.mem_U_iff hVn hn hUc ⟨_, hw'⟩).mpr (by rw [hψ]; simp [h0]), ?_⟩
    rw [N.psiU_eq hw', N.psiU_eq huW, hψ, hinvcoe]
    simp
  have htact : ∀ y ∈ Q, N.tt ((τ' : G) * y * (τ' : G)⁻¹) = (a : GaloisField 2 n) ^ 2 * N.tt y := by
    intro y hy
    have hyτ : (τ' : G) * y * (τ' : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hMQ hτM) y).mp hy
    apply upperElt_injective (GaloisField 2 n)
    rw [← N.φ_eq hyτ]
    have e : (⟨(τ' : G) * y * (τ' : G)⁻¹, Subgroup.mem_sup_left hyτ⟩ : ↥(Q ⊔ conjSubgroup g Q)) =
        τ' * ⟨y, Subgroup.mem_sup_left hy⟩ * τ'⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hτ'φ, N.φ_eq hy,
      ARS.NaturalModule.diagElt_mul_upperElt, mul_inv_cancel_right]
  refine ⟨(τ' : G), (a : GaloisField 2 n), hτM, τ'.2, ?_,
    by rw [Subgroup.orderOf_coe]; exact hτ'ord, haord, fun v hv => (hVact v hv).2,
    fun u hu => (hUact u hu).2, htact⟩
  exact Subgroup.mem_normalizer_fintype fun u hu => (hUact u hu).1

end NatData

private theorem Hyp79.centralizes_conj [Finite G]
    {M V Q : Subgroup G} (H : Hyp79 M V Q) (g : G) :
    ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q := by
  intro q hq u hu
  obtain ⟨-, hZ, -⟩ := H.special
  rw [mem_conjSubgroup] at hq hu
  have hv : g⁻¹ * u * g ∈ Subgroup.centralizer (Q : Set G) := by
    have : g⁻¹ * u * g ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hZ ▸ hu
    exact this.2
  have h1 := Subgroup.mem_centralizer_iff.mp hv _ hq
  have e1 : q * u = g * ((g⁻¹ * q * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
  have e2 : u * q = g * ((g⁻¹ * u * g) * (g⁻¹ * q * g)) * g⁻¹ := by group
  rw [e1, e2, h1]

private noncomputable def NatData.toMulData [Finite G] {V Q : Subgroup G} {g : G} {n : ℕ}
    (N : NatData V Q g n) (hVn : Nat.card V = 2 ^ n) (hn : n ≠ 0)
    (hUc : ∀ q ∈ conjSubgroup g Q, ∀ u ∈ conjSubgroup g V, q * u = u * q) :
    MulData V (conjSubgroup g V) Q (GaloisField 2 n) :=
  ⟨N.gam, N.psiU, N.tt,
    fun a ha b hb => N.gam_add ha hb,
    fun a ha h => N.gam_inj ha h,
    N.gam_surj,
    fun a ha b hb => N.psiU_add ha hb,
    fun a ha h => N.psiU_inj hUc ha h,
    fun s => N.psiU_surj hVn hn hUc s,
    fun a ha b hb => N.tt_add ha hb,
    N.tt_surj,
    fun a ha => N.tt_ker hVn hn hUc ha,
    fun y hy u hu => N.comm_aux hVn hn hUc hy hu⟩

theorem Hyp79.exists_mulData [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) :
    ∃ n : ℕ, Nat.card V = 2 ^ n ∧ Nonempty (MulData V (conjSubgroup g V) Q (GaloisField 2 n)) := by
  obtain ⟨n, hn2, hVn, ⟨N⟩⟩ := exists_natData H hgV hgQ
  exact ⟨n, hVn, ⟨N.toMulData hVn (by omega) (H.centralizes_conj g)⟩⟩

theorem Hyp79.exists_mulData_torus [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) :
    ∃ n : ℕ, Nat.card V = 2 ^ n ∧
      ∃ D : MulData V (conjSubgroup g V) Q (GaloisField 2 n),
        ∃ (τ : G) (a : GaloisField 2 n), τ ∈ M ∧ τ ∈ Q ⊔ conjSubgroup g Q ∧
          τ ∈ Subgroup.normalizer (conjSubgroup g V : Set G) ∧
          orderOf τ = 2 ^ n - 1 ∧ orderOf a = 2 ^ n - 1 ∧
          (∀ v ∈ V, D.γ (τ * v * τ⁻¹) = a * D.γ v) ∧
          (∀ u ∈ conjSubgroup g V, D.ψ (τ * u * τ⁻¹) = a⁻¹ * D.ψ u) ∧
          (∀ y ∈ Q, D.t (τ * y * τ⁻¹) = a ^ 2 * D.t y) := by
  obtain ⟨n, hn2, hVn, ⟨N⟩⟩ := exists_natData H hgV hgQ
  have hn : n ≠ 0 := by omega
  have hUc := H.centralizes_conj g
  have h := H.toHyp218 hgV hgQ
  obtain ⟨τ, a, hτ⟩ := N.exists_torus h.normalizer_eq h.M_le_normalizer_Q hVn hn hUc
  exact ⟨n, hVn, N.toMulData hVn hn hUc, τ, a, hτ⟩

end CFSG.RankThree.GF2n.Tim79
