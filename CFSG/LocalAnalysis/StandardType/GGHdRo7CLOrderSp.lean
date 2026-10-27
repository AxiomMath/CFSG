module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
public import Certificates.Certificate113
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelI
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderSpAux1

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def hdRo7CLOSpAux_reindex {p k : ℕ} (σ : Equiv.Perm (Fin (k+1))) :
    (Fin (k+1) → Multiplicative (ZMod p)) ≃* (Fin (k+1) → Multiplicative (ZMod p)) where
  toFun f := f ∘ σ
  invFun f := f ∘ σ.symm
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp
  map_mul' f g := rfl

private noncomputable def hdRo7CLOSpAux_diag {p k : ℕ} (c : Fin (k+1) → ZMod p)
    (hc : ∀ i, c i * c i = 1) :
    (Fin (k+1) → Multiplicative (ZMod p)) ≃* (Fin (k+1) → Multiplicative (ZMod p)) where
  toFun f := fun i => Multiplicative.ofAdd (c i * Multiplicative.toAdd (f i))
  invFun g := fun i => Multiplicative.ofAdd (c i * Multiplicative.toAdd (g i))
  left_inv f := by
    funext i
    show Multiplicative.ofAdd (c i * (c i * Multiplicative.toAdd (f i))) = f i
    rw [← mul_assoc, hc i, one_mul]
    rfl
  right_inv g := by
    funext i
    show Multiplicative.ofAdd (c i * (c i * Multiplicative.toAdd (g i))) = g i
    rw [← mul_assoc, hc i, one_mul]
    rfl
  map_mul' f g := by
    funext i
    show Multiplicative.ofAdd (c i * (Multiplicative.toAdd (f i) + Multiplicative.toAdd (g i))) =
      Multiplicative.ofAdd (c i * Multiplicative.toAdd (f i)) *
        Multiplicative.ofAdd (c i * Multiplicative.toAdd (g i))
    rw [mul_add]
    rfl

private noncomputable def hdRo7CLOSpAux_coordAut {p k : ℕ} (σ : Equiv.Perm (Fin (k+1)))
    (c : Fin (k+1) → ZMod p) (hc : ∀ i, c i * c i = 1) :
    (Fin (k+1) → Multiplicative (ZMod p)) ≃* (Fin (k+1) → Multiplicative (ZMod p)) :=
  (hdRo7CLOSpAux_reindex (p := p) σ.symm).trans
    (hdRo7CLOSpAux_diag (fun j => c (σ.symm j)) (fun j => hc (σ.symm j)))

private lemma hdRo7CLOSpAux_coordAut_apply {p k : ℕ} (σ : Equiv.Perm (Fin (k+1)))
    (c : Fin (k+1) → ZMod p) (hc : ∀ i, c i * c i = 1)
    (f : Fin (k+1) → Multiplicative (ZMod p)) (i : Fin (k+1)) :
    Multiplicative.toAdd ((hdRo7CLOSpAux_coordAut σ c hc f) (σ i)) =
      c i * Multiplicative.toAdd (f i) := by
  change Multiplicative.toAdd
    (Multiplicative.ofAdd (c (σ.symm (σ i)) * Multiplicative.toAdd (f (σ.symm (σ i))))) =
      c i * Multiplicative.toAdd (f i)
  rw [Equiv.symm_apply_apply]
  rfl

private lemma hdRo7CLOSpAux_coordAut_single {p k : ℕ} (σ : Equiv.Perm (Fin (k+1)))
    (c : Fin (k+1) → ZMod p) (hc : ∀ i, c i * c i = 1) (j : Fin (k+1)) :
    hdRo7CLOSpAux_coordAut σ c hc
        (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) j
          (Multiplicative.ofAdd (1 : ZMod p))) =
      Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) (σ j)
        (Multiplicative.ofAdd (c j)) := by
  let e : Fin (k+1) → Multiplicative (ZMod p) :=
    Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) j
      (Multiplicative.ofAdd (1 : ZMod p))
  change hdRo7CLOSpAux_coordAut σ c hc e =
    Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) (σ j)
      (Multiplicative.ofAdd (c j))
  funext l
  have hlhs : (hdRo7CLOSpAux_coordAut σ c hc e) l =
      Multiplicative.ofAdd (c (σ.symm l) * Multiplicative.toAdd (e (σ.symm l))) := by
    have h := hdRo7CLOSpAux_coordAut_apply σ c hc e (σ.symm l)
    rw [Equiv.apply_symm_apply] at h
    rw [← h]
    rfl
  rw [hlhs]
  dsimp only [e]
  by_cases hl : l = σ j
  · subst hl
    rw [Pi.mulSingle_eq_same, Equiv.symm_apply_apply, Pi.mulSingle_eq_same]
    show Multiplicative.ofAdd (c j * (1 : ZMod p)) = Multiplicative.ofAdd (c j)
    rw [mul_one]
  · rw [Pi.mulSingle_eq_of_ne hl]
    have hne : σ.symm l ≠ j := fun h => hl (by rw [← h, Equiv.apply_symm_apply])
    rw [Pi.mulSingle_eq_of_ne hne]
    show Multiplicative.ofAdd (c (σ.symm l) * (0 : ZMod p)) = 1
    rw [mul_zero]
    rfl

private noncomputable def hdRo7CLOSpAux_zmodZpowersEquiv {G : Type} [Group G] {x : G} (p : ℕ)
    (hxp : x ^ p = 1) (hx : x ≠ 1) (hp : Nat.Prime p) :
    Multiplicative (ZMod p) ≃* Subgroup.zpowers x := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : Multiplicative (ZMod p) →* Subgroup.zpowers x :=
    { toFun := fun m => ⟨x ^ (Multiplicative.toAdd m).val,
        Subgroup.pow_mem _ (Subgroup.mem_zpowers x) (Multiplicative.toAdd m).val⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        show x ^ (Multiplicative.toAdd (a * b)).val =
          x ^ (Multiplicative.toAdd a).val * x ^ (Multiplicative.toAdd b).val
        rw [show Multiplicative.toAdd (a * b) =
            Multiplicative.toAdd a + Multiplicative.toAdd b from rfl,
          ZMod.val_add, ← pow_eq_pow_mod _ hxp, pow_add] }
  have hdom : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]
  have hcod : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx]
  have hne : φ.ker ≠ ⊤ := by
    intro h
    have h1 : φ (Multiplicative.ofAdd (1 : ZMod p)) = 1 := by
      have : Multiplicative.ofAdd (1 : ZMod p) ∈ φ.ker := by
        rw [h]; exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mp this
    have h2 : φ (Multiplicative.ofAdd (1 : ZMod p)) = ⟨x, Subgroup.mem_zpowers x⟩ := by
      apply Subtype.ext
      show x ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = x
      rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p)) = (1 : ZMod p) from rfl,
        ZMod.val_one, pow_one]
    rw [h2] at h1
    exact hx (congrArg Subtype.val h1)
  have hcardker : Nat.card φ.ker = 1 := by
    have hdvd : Nat.card φ.ker ∣ p := by
      have := Subgroup.card_subgroup_dvd_card φ.ker
      rwa [hdom] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact h1
    · exfalso
      apply hne
      exact Subgroup.eq_top_of_card_eq _ (by rw [h1, hdom])
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hcardker
  have hrange : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h := CFSG.StandardType.TableB.card_range_mul_card_ker φ
    rw [hcardker, mul_one, hdom] at h
    rw [h, hcod]
  exact MulEquiv.ofBijective φ ⟨hinj, MonoidHom.range_eq_top.mp hrange⟩

private theorem hdRo7CLOSpAux_count_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L : Subgroup G} (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hsgn : ∀ i : Fin k, ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.sgnAut i f) : G))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.permAut σ f) : G))
    (hnorm : ∀ g : ↥L, (∀ e : ↥(Bs ⊓ L), ∃ e' : ↥(Bs ⊓ L),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', (g : G) * (τT f : G) * (g : G)⁻¹ = (τT f' : G) →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x)
    (hxp : x ^ p = 1) (hxne : x ≠ 1) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hx : x ∈ Bs) :
    2 ^ k * k.factorial ≤ Nat.card (ggAutomizer L Bs) := by
  classical
  haveI : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  let τ : (Fin (k+1) → Multiplicative (ZMod p)) ≃* ↥Bs :=
    hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
  have hcoordModel : C2CoordModel p Bs L k τ :=
    hdRo7CLCoordAux_coordModel_tau_of_dirs p B Bs x L k τT hτT τC Φ hΦ hC hsgn hperm hnorm
      hLx hxp hxne hp hx
  let pairPerm : Equiv.Perm (Fin k) → Equiv.Perm (Fin (k+1)) :=
    fun π => Equiv.Perm.decomposeFin.symm (0, π)
  let pairSign : (Fin k → Bool) → Fin (k+1) → ZMod p :=
    fun b i => Fin.cases 1 (fun j => if b j then -1 else 1) i
  have hPerm0 : ∀ π, pairPerm π 0 = 0 := fun π =>
    Equiv.Perm.decomposeFin_symm_apply_zero 0 π
  have hSign0 : ∀ b, pairSign b 0 = 1 := fun b => rfl
  have hSignSign : ∀ b i, pairSign b i = 1 ∨ pairSign b i = -1 := by
    intro b i
    induction i using Fin.cases with
    | zero => left; rfl
    | succ j =>
      simp only [pairSign, Fin.cases_succ]
      split <;> simp
  have hSignSq : ∀ b i, pairSign b i * pairSign b i = 1 := by
    intro b i
    rcases hSignSign b i with h | h
    · rw [h, one_mul]
    · rw [h]
      exact (neg_mul_neg (1 : ZMod p) 1).trans (one_mul 1)
  let F : Equiv.Perm (Fin k) × (Fin k → Bool) → ↥(ggAutomizer L Bs) := fun q =>
    let σ := pairPerm q.1
    let c := pairSign q.2
    let A := hdRo7CLOSpAux_coordAut σ c (hSignSq q.2)
    let a : MulAut ↥Bs := (τ.symm.trans A).trans τ
    ⟨a, (hcoordModel a).mpr ⟨σ, c, hPerm0 q.1, hSign0 q.2, hSignSign q.2, by
      intro f i
      have hA : a (τ f) = τ (A f) := by
        show τ (A (τ.symm (τ f))) = τ (A f)
        rw [MulEquiv.symm_apply_apply]
      rw [hA, MulEquiv.symm_apply_apply]
      exact hdRo7CLOSpAux_coordAut_apply σ c (hSignSq q.2) f i⟩⟩
  have hinj : Function.Injective F := by
    rintro ⟨π1, b1⟩ ⟨π2, b2⟩ hq
    let A1 := hdRo7CLOSpAux_coordAut (pairPerm π1) (pairSign b1) (hSignSq b1)
    let A2 := hdRo7CLOSpAux_coordAut (pairPerm π2) (pairSign b2) (hSignSq b2)
    let a1 : MulAut ↥Bs := (τ.symm.trans A1).trans τ
    let a2 : MulAut ↥Bs := (τ.symm.trans A2).trans τ
    have ha : a1 = a2 := by
      have h := congrArg Subtype.val hq
      simpa only [F, A1, A2, a1, a2] using h
    have hact1 : ∀ f, a1 (τ f) = τ (A1 f) := by
      intro f
      show τ (A1 (τ.symm (τ f))) = τ (A1 f)
      rw [MulEquiv.symm_apply_apply]
    have hact2 : ∀ f, a2 (τ f) = τ (A2 f) := by
      intro f
      show τ (A2 (τ.symm (τ f))) = τ (A2 f)
      rw [MulEquiv.symm_apply_apply]
    have hsingle : ∀ j, Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) (pairPerm π1 j)
          (Multiplicative.ofAdd (pairSign b1 j)) =
        Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) (pairPerm π2 j)
          (Multiplicative.ofAdd (pairSign b2 j)) := by
      intro j
      have h := DFunLike.congr_fun ha
        (τ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) j
          (Multiplicative.ofAdd (1 : ZMod p))))
      rw [hact1, hact2] at h
      rw [hdRo7CLOSpAux_coordAut_single (pairPerm π1) (pairSign b1) (hSignSq b1) j,
        hdRo7CLOSpAux_coordAut_single (pairPerm π2) (pairSign b2) (hSignSq b2) j] at h
      exact τ.injective h
    have h1z : (1 : ZMod p) ≠ 0 := by
      intro h
      have h1 := congrArg ZMod.val h
      rw [ZMod.val_one, ZMod.val_zero] at h1
      exact one_ne_zero h1
    have hσ : pairPerm π1 = pairPerm π2 := by
      apply Equiv.ext
      intro j
      have h1 := congrFun (hsingle j) (pairPerm π1 j)
      rw [Pi.mulSingle_eq_same] at h1
      by_cases h : (pairPerm π1 : Fin (k+1) → Fin (k+1)) j =
          (pairPerm π2 : Fin (k+1) → Fin (k+1)) j
      · exact h
      · exfalso
        rw [Pi.mulSingle_eq_of_ne (i := pairPerm π2 j) (i' := pairPerm π1 j) h] at h1
        have hzero : pairSign b1 j = 0 := by
          have := congrArg Multiplicative.toAdd h1
          simpa using this
        rcases hSignSign b1 j with hc | hc <;> rw [hc] at hzero
        · exact h1z hzero
        · exact (neg_ne_zero.mpr h1z) hzero
    have hc : pairSign b1 = pairSign b2 := by
      funext j
      have h := hsingle j
      have hσj : ⇑(pairPerm π1) j = ⇑(pairPerm π2) j := congrArg (fun e => ⇑e j) hσ
      rw [hσj] at h
      exact Multiplicative.ofAdd.injective (Pi.mulSingle_injective (pairPerm π2 j) h)
    have hπ : π1 = π2 := by
      have h := Equiv.Perm.decomposeFin.symm.injective hσ
      exact (Prod.ext_iff.mp h).2
    have hb : b1 = b2 := by
      funext j
      have h1 := congrFun hc j.succ
      simp only [pairSign, Fin.cases_succ] at h1
      by_cases hb1 : b1 j <;> by_cases hb2 : b2 j
      · simp [hb1, hb2]
      · exfalso; simp [hb1, hb2] at h1; exact ZMod.neg_one_ne_one h1
      · exfalso; simp [hb1, hb2] at h1; exact ZMod.neg_one_ne_one h1.symm
      · simp [hb1, hb2]
    exact Prod.ext hπ hb
  have hcard : Nat.card (Equiv.Perm (Fin k) × (Fin k → Bool)) = 2 ^ k * k.factorial := by
    rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, Nat.card_fun, Nat.card_fin,
      Nat.card_eq_fintype_card, Fintype.card_bool]
    ring
  calc 2 ^ k * k.factorial = Nat.card (Equiv.Perm (Fin k) × (Fin k → Bool)) := hcard.symm
    _ ≤ Nat.card ↥(ggAutomizer L Bs) := Nat.card_le_card_of_injective F hinj



theorem c2_lorder_sp
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hp3 : p = 3) (hn : 5 ≤ n)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hLlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hn1 : lab.n = 1) (h4 : 4 ≤ lab.rank) :
    2 ^ n * n.factorial ≤ Nat.card (ggAutomizer L Bs) := by
  have hp : Nat.Prime p := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨⟨R, hRgrp, I, θ, hBsN, hperf, hTSC, hCP, hcenter, hI, hBs3⟩, hZL, hinner⟩ :=
    hdRo7CLOSpAux_hinner (K := K) hRig hH lab hlab hLlab htag hn1 h4 hp3
  letI : Group R := hRgrp
  obtain ⟨k, τT, hτTinj, hτTsurj, hsgn, hperm, hnorm⟩ :=
    hdRo7CLCoordAux_signedData_L p B Bs x L D J y K hH R θ hZL hBsN hinner hTSC
  have hcard_inf : Nat.card ↥(Bs ⊓ L) = p ^ lab.rank :=
    hdRo7CLOSpAux_card_inf_pow hH lab hlab hLlab htag hn1 h4 hp3 hBsN hinner
  have hsplit : Nat.card ↥Bs = Nat.card ↥(Bs ⊓ L) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    card_ggBstar_split hH.1.2.1 hZL hBsN hinner
  have hCeq : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hdRo7CLCoordAux_bstar_centralizer_eq hH
  have hCcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hCeq, Nat.card_zpowers,
      orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH)]
  have hcardBs : Nat.card ↥Bs = p ^ (n + 1) := by
    have h1 : Nat.card (Additive ↥Bs) = p ^ (n + 1) := by
      rw [Nat.card_congr ι.toEquiv, Nat.card_congr b.equivFun.toEquiv,
        Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    rw [← h1]
    exact Nat.card_congr (Equiv.refl ↥Bs)
  have hrank : lab.rank = n := by
    have h1 : p ^ (n + 1) = p ^ (lab.rank + 1) := by
      rw [← hcardBs, hsplit, hcard_inf, hCcard, pow_succ]
    have h2 : n + 1 = lab.rank + 1 := Nat.pow_right_injective hp.two_le h1
    omega
  have hk : k = lab.rank :=
    hdRo7CLCoordAux_k_eq_of_card p k lab.rank hp.two_le τT ⟨hτTinj, hτTsurj⟩ hcard_inf
  let τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    (hdRo7CLOSpAux_zmodZpowersEquiv p (hdRo7CLCoordAux_x_pow_eq_one hH)
      (hdRo7CLCoordAux_x_ne_one hH) hp).trans (MulEquiv.subgroupCongr hCeq).symm
  have hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val := by
    intro m
    rfl
  let Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs :=
    hdRo7CLCoordAux_split_equiv p B Bs x L D J y K hH hZL hBsN hinner
  have hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G) := fun t c =>
    congrArg Subtype.val
      (hdRo7CLCoordAux_split_equiv_apply p B Bs x L D J y K hH hZL hBsN hinner t c)
  have hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x := by
    intro g
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp
      (hH.1.tableB_facts.2.2.2.1 g.2)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hcount := hdRo7CLOSpAux_count_le (G := G) (p := p) (B := B) (Bs := Bs) (x := x) (L := L)
    k τT ⟨hτTinj, hτTsurj⟩ τC Φ hΦ
    hC hsgn hperm hnorm hLx (hdRo7CLCoordAux_x_pow_eq_one hH)
    (hdRo7CLCoordAux_x_ne_one hH) hp hp2 hH.1.tableB_facts.2.2.1
  have hkn : k = n := by rw [hk, hrank]
  calc 2 ^ n * n.factorial = 2 ^ k * k.factorial := by rw [hkn]
    _ ≤ Nat.card (ggAutomizer L Bs) := hcount

end CFSG.StandardType.HdRo7C

end
