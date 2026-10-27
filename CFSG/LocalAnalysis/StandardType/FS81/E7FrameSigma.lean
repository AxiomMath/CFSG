module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameK0
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.Timmesfeld
open scoped Matrix

variable {G : Type} [Group G] {K : Subgroup G}

set_option maxRecDepth 100000 in
theorem good_d6_shift : ∀ i j : Fin 6, i ≠ j → ∀ a b c : ZMod 3, c ≠ 0 →
    e7Good (Pi.single i.succ.succ 1 + a • Pi.single 1 1 +
      c • (Pi.single j.succ.succ 1 + b • Pi.single 1 1)) → a + c * b = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e7Good_e1_ones :
    e7Good (Pi.single 1 1 + Fin.cons 0 (Fin.cons 0 (fun _ : Fin 6 => (1 : ZMod 3)))) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem not_e7Good_e0_ones :
    ¬ e7Good (Pi.single 0 1 + Fin.cons 0 (Fin.cons 0 (fun _ : Fin 6 => (1 : ZMod 3)))) := by
  decide +kernel

theorem zpow_eq_pow_val {b : G} (hb : orderOf b = 3) (k : ℤ) :
    b ^ k = b ^ ((k : ZMod 3).val) := by
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_mod_orderOf, hb]

def trEquiv (ψ : ↥L7 ≃* ↥K) {X : Subgroup (ModGL .E7 (ZMod 2))} (hX : X ≤ L7) :
    ↥X ≃* ↥(tr ψ X) :=
  (Subgroup.subgroupOfEquivOfLe hX).symm.trans
    ((X.subgroupOf L7).equivMapOfInjective (K.subtype.comp ψ.toMonoidHom)
      (K.subtype_injective.comp ψ.injective))

theorem coe_trEquiv (ψ : ↥L7 ≃* ↥K) {X : Subgroup (ModGL .E7 (ZMod 2))} (hX : X ≤ L7)
    (x : ↥X) : ((trEquiv ψ hX x : ↥(tr ψ X)) : G) = ((ψ ⟨x, hX x.2⟩ : ↥K) : G) := by
  rw [trEquiv, MulEquiv.trans_apply, Subgroup.coe_equivMapOfInjective_apply]
  congr 2

def conjOn (H : Subgroup G) (g : G) (hg : H.map (MulAut.conj g).toMonoidHom = H) : MulAut ↥H :=
  ((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hg)

theorem coe_conjOn (H : Subgroup G) (g : G) (hg : H.map (MulAut.conj g).toMonoidHom = H)
    (h : ↥H) : ((conjOn H g hg h : ↥H) : G) = g * h * g⁻¹ := by
  change (((MulAut.conj g).subgroupMap H h : ↥(H.map (MulAut.conj g).toMonoidHom)) : G) = _
  rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]

def conjAut (ψ : ↥L7 ≃* ↥K) {X : Subgroup (ModGL .E7 (ZMod 2))} (hX : X ≤ L7) (g : G)
    (hg : (tr ψ X).map (MulAut.conj g).toMonoidHom = tr ψ X) : MulAut ↥X :=
  (trEquiv ψ hX).trans ((conjOn _ g hg).trans (trEquiv ψ hX).symm)

theorem trEquiv_conjAut (ψ : ↥L7 ≃* ↥K) {X : Subgroup (ModGL .E7 (ZMod 2))} (hX : X ≤ L7)
    (g : G) (hg : (tr ψ X).map (MulAut.conj g).toMonoidHom = tr ψ X) (x : ↥X) :
    ((trEquiv ψ hX (conjAut ψ hX g hg x) : ↥(tr ψ X)) : G) =
      g * ((trEquiv ψ hX x : ↥(tr ψ X)) : G) * g⁻¹ := by
  simp only [conjAut, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, coe_conjOn]

theorem map_conj_tr_of_conjAut (ψ : ↥L7 ≃* ↥K) {H X Y : Subgroup (ModGL .E7 (ZMod 2))}
    (hH : H ≤ L7) (hX : X ≤ H) (hY : Y ≤ H) (g : G)
    (hg : (tr ψ H).map (MulAut.conj g).toMonoidHom = tr ψ H)
    (himg : (X.subgroupOf H).map (conjAut ψ hH g hg).toMonoidHom = Y.subgroupOf H) :
    (tr ψ X).map (MulAut.conj g).toMonoidHom = tr ψ Y := by
  ext w
  constructor
  · rintro ⟨_, hx, rfl⟩
    obtain ⟨x, hxX, rfl⟩ := mem_tr.mp hx
    let x' : ↥H := ⟨x, hX hxX⟩
    have hx' : x' ∈ X.subgroupOf H := Subgroup.mem_subgroupOf.mpr hxX
    have hφ : conjAut ψ hH g hg x' ∈ Y.subgroupOf H := by
      rw [← himg]
      exact Subgroup.mem_map_of_mem (conjAut ψ hH g hg).toMonoidHom hx'
    have h := trEquiv_conjAut ψ hH g hg x'
    rw [coe_trEquiv, coe_trEquiv] at h
    refine mem_tr.mpr ⟨⟨_, hH (conjAut ψ hH g hg x').2⟩, hφ, ?_⟩
    rw [h]
    rfl
  · intro hw
    obtain ⟨y, hyY, rfl⟩ := mem_tr.mp hw
    let y' : ↥H := ⟨y, hY hyY⟩
    have hy' : y' ∈ Y.subgroupOf H := Subgroup.mem_subgroupOf.mpr hyY
    rw [← himg] at hy'
    obtain ⟨x', hx', hxy⟩ := hy'
    have h := trEquiv_conjAut ψ hH g hg x'
    rw [coe_trEquiv, coe_trEquiv] at h
    refine ⟨((ψ ⟨x', hH x'.2⟩ : ↥K) : G),
      mem_tr.mpr ⟨⟨x', hH x'.2⟩, Subgroup.mem_subgroupOf.mp hx', rfl⟩, ?_⟩
    change g * ((ψ ⟨x', hH x'.2⟩ : ↥K) : G) * g⁻¹ = _
    rw [← h]
    have hxy' : ((conjAut ψ hH g hg x' : ↥H) : ModGL .E7 (ZMod 2)) = y := congrArg Subtype.val hxy
    exact congrArg (fun w : ↥L7 => ((ψ w : ↥K) : G)) (Subtype.ext hxy')

theorem map_conj_eq_of_forall_commute {X : Subgroup G} {g : G} (h : ∀ x ∈ X, g * x = x * g) :
    X.map (MulAut.conj g).toMonoidHom = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (mem_normalizer_of_forall_commute h)

section Native


variable [Finite G] {b₀ : G} {E : Subgroup G}

theorem b_mem_M (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀) (hF : E7NatFrame) (hC : E7NatCent)
    (ψ : ↥L7 ≃* ↥K) {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0)
    (hψz : ((ψ z : ↥K) : G) = B.b 1) (i : Fin 6) : B.b i.succ.succ ∈ tr ψ M0 := by
  have hz3 := orderOf_z ψ hψz
  have hb₁ord : orderOf (B.b 1) = 3 := B.ord 1
  have hspan : B.span = E := hB.1
  have hEea : CFSG.Open.IsElemAbelian 3 E := hstd.2.1.2.1.2.1
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEea.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hbE : ∀ l, B.b l ∈ E := fun l => hspan ▸ B.b_mem_span l
  have hb₀ : B.b 0 = b₀ := hB.2.1
  obtain ⟨t₀, ht₀, ht₀z⟩ := jn0_exists_inv hF hz hz3
  let t : G := ((ψ ⟨t₀, hF.1 0 ht₀⟩ : ↥K) : G)
  have htJ : t ∈ tr ψ (Jn 0) := (coe_mem_tr_iff ψ _).mpr ht₀
  have htK : t ∈ K := tr_le_K ψ _ htJ
  have htb₁ : t * B.b 1 * t⁻¹ = (B.b 1)⁻¹ := by
    have h : (⟨t₀, hF.1 0 ht₀⟩ : ↥L7) * z * (⟨t₀, hF.1 0 ht₀⟩ : ↥L7)⁻¹ = z⁻¹ :=
      Subtype.ext (by simpa using ht₀z)
    have h' := congrArg (fun w => ((ψ w : ↥K) : G)) h
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h'
    rw [← hψz]
    exact h'
  have htb₀ : t * b₀ * t⁻¹ = b₀ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hstd.2.1.1.2.1 htK)]
    group
  have hdec : ∀ l : Fin 6, ∃ c : ℤ, ∃ m ∈ tr ψ M0, B.b l.succ.succ = B.b 1 ^ c * m := by
    intro l
    have hlK : B.b l.succ.succ ∈ K := hB.2.2 _ (Fin.succ_ne_zero _)
    obtain ⟨c, m, hm, hcm⟩ := exists_zpow_mul_of_commute hC ψ hz hz3 hlK
      (hψz ▸ hcommE _ (hbE _) _ (hbE 1))
    exact ⟨c, m, hm, hψz ▸ hcm⟩
  choose c m hm hcm using hdec
  have htm : ∀ l, t * m l * t⁻¹ = m l := fun l => by
    rw [(Subgroup.mem_centralizer_iff.mp (tr_jn0_le_centralizer ψ htJ) _ (hm l)).symm]
    group
  have htl : ∀ l : Fin 6, t * B.b l.succ.succ * t⁻¹ = B.b 1 ^ (-2 * c l) * B.b l.succ.succ := by
    intro l
    have h1 : t * B.b 1 ^ c l * t⁻¹ = (B.b 1)⁻¹ ^ c l := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, htb₁]
    calc t * B.b l.succ.succ * t⁻¹ = (t * B.b 1 ^ c l * t⁻¹) * (t * m l * t⁻¹) := by
          rw [hcm l]; group
      _ = (B.b 1)⁻¹ ^ c l * m l := by rw [h1, htm]
      _ = B.b 1 ^ (-2 * c l) * (B.b 1 ^ c l * m l) := by
          rw [inv_zpow', ← mul_assoc, ← zpow_add]
          congr 2
          ring
      _ = B.b 1 ^ (-2 * c l) * B.b l.succ.succ := by rw [← hcm l]
  let d : Fin 6 → ZMod 3 := fun l => ((-2 * c l : ℤ) : ZMod 3)
  let col : Fin 8 → Coords 8 := Fin.cases (Pi.single 0 1) (Fin.cases (-Pi.single 1 1)
    fun l => Pi.single l.succ.succ 1 + d l • Pi.single 1 1)
  let T : Matrix (Fin 8) (Fin 8) (ZMod 3) := Matrix.of fun r k => col k r
  have hT : B.Acts t T := by
    intro k
    change t * B.b k * t⁻¹ = B.vec (col k)
    cases k using Fin.cases with
    | zero =>
      rw [hb₀, htb₀]
      change b₀ = B.vec (Pi.single 0 1)
      rw [B.vec_single, hb₀]
    | succ k =>
      cases k using Fin.cases with
      | zero =>
        change t * B.b 1 * t⁻¹ = B.vec (-Pi.single 1 1)
        rw [htb₁, B.vec_neg_eq_inv, B.vec_single]
      | succ l =>
        change t * B.b l.succ.succ * t⁻¹ = B.vec (Pi.single l.succ.succ 1 + d l • Pi.single 1 1)
        rw [htl, B.vec_add, B.vec_single, B.vec_smul_single, zpow_eq_pow_val hb₁ord]
        exact hcommE _ (E.pow_mem (hbE 1) _) _ (hbE _)
  have hTcol : ∀ k, T *ᵥ Pi.single k 1 = col k := fun k => by
    rw [mulVec_single_one_col]
    rfl
  have hd : ∀ j : Fin 6, j ≠ i → ∀ s : ZMod 3, s ≠ 0 → d i + s * d j = 0 := by
    intro j hj s hs
    have hg := (d6_vec i j hj.symm s hs).1
    rw [good_iff_of_acts hrec hT, Matrix.mulVec_add, Matrix.mulVec_smul, hTcol, hTcol] at hg
    exact good_d6_shift i j hj.symm (d i) (d j) s hs (by simpa [col] using hg)
  have hji : i + 1 ≠ i := by
    have : ∀ x : Fin 6, x + 1 ≠ x := by decide
    exact this i
  have hdi : d i = 0 := by
    have h1 := hd (i + 1) hji 1 one_ne_zero
    have h2 := hd (i + 1) hji (-1) (by decide)
    have key : ∀ x y : ZMod 3, x + 1 * y = 0 → x + -1 * y = 0 → x = 0 := by decide
    exact key _ _ h1 h2
  have hci : (c i : ZMod 3) = 0 := by
    have h : ((-2 * c i : ℤ) : ZMod 3) = 0 := hdi
    push_cast at h
    have key : ∀ x : ZMod 3, -2 * x = 0 → x = 0 := by decide
    exact key _ h
  have hpow : B.b 1 ^ c i = 1 := by
    rw [zpow_eq_pow_val hb₁ord, hci, ZMod.val_zero, pow_zero]
  rw [hcm i, hpow, one_mul]
  exact hm i

omit [Finite G] in
theorem vec_mem_M {B : Basis3 G 8} (ψ : ↥L7 ≃* ↥K)
    (hbM : ∀ i : Fin 6, B.b i.succ.succ ∈ tr ψ M0) {v : Coords 8} (h0 : v 0 = 0)
    (h1 : v 1 = 0) : B.vec v ∈ tr ψ M0 := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨l, rfl⟩ := hx
  cases l using Fin.cases with
  | zero =>
    rw [h0, ZMod.val_zero, pow_zero]
    exact Subgroup.one_mem _
  | succ l =>
    cases l using Fin.cases with
    | zero =>
      change B.b 1 ^ (v 1).val ∈ _
      rw [h1, ZMod.val_zero, pow_zero]
      exact Subgroup.one_mem _
    | succ l => exact Subgroup.pow_mem _ (hbM l) _

theorem not_isInner_conjAut_n (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀) (hF : E7NatFrame) (hC : E7NatCent)
    (ψ : ↥L7 ≃* ↥K) {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0)
    (hψz : ((ψ z : ↥K) : G) = B.b 1) {n : G} (hn1 : n * B.b 1 * n⁻¹ = b₀)
    (hnM : (tr ψ M0).map (MulAut.conj n).toMonoidHom = tr ψ M0) :
    ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) n hnM) := by
  rintro ⟨m₀, hm₀⟩
  let m : G := ((ψ ⟨m₀, m₀.2.1⟩ : ↥K) : G)
  have hmK : m ∈ K := (ψ ⟨m₀, m₀.2.1⟩).2
  have hcen : ∀ x ∈ tr ψ M0, (m⁻¹ * n) * x * (m⁻¹ * n)⁻¹ = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_tr.mp hx
    have h := trEquiv_conjAut ψ (inf_le_left : M0 ≤ L7) n hnM ⟨y, hy⟩
    rw [hm₀, coe_trEquiv, coe_trEquiv] at h
    have h' : ((ψ ⟨((MulAut.conj m₀ ⟨(y : ModGL .E7 (ZMod 2)), hy⟩ : ↥M0) : ModGL .E7 (ZMod 2)),
        (MulAut.conj m₀ ⟨(y : ModGL .E7 (ZMod 2)), hy⟩).2.1⟩ : ↥K) : G) =
          m * ((ψ y : ↥K) : G) * m⁻¹ := by
      have he : (⟨((MulAut.conj m₀ ⟨(y : ModGL .E7 (ZMod 2)), hy⟩ : ↥M0) : ModGL .E7 (ZMod 2)),
          (MulAut.conj m₀ ⟨(y : ModGL .E7 (ZMod 2)), hy⟩).2.1⟩ : ↥L7) =
            ⟨m₀, m₀.2.1⟩ * y * (⟨m₀, m₀.2.1⟩ : ↥L7)⁻¹ := Subtype.ext rfl
      rw [he, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h'] at h
    have hyy : (⟨(y : ModGL .E7 (ZMod 2)), (inf_le_left : M0 ≤ L7) hy⟩ : ↥L7) = y := rfl
    rw [hyy] at h
    calc m⁻¹ * n * ((ψ y : ↥K) : G) * (m⁻¹ * n)⁻¹ = m⁻¹ * (n * ((ψ y : ↥K) : G) * n⁻¹) * m := by
          group
      _ = m⁻¹ * (m * ((ψ y : ↥K) : G) * m⁻¹) * m := by rw [← h]
      _ = ((ψ y : ↥K) : G) := by group
  have hbM := b_mem_M hstd hB hrec hF hC ψ hz hψz
  let c : Coords 8 := Fin.cons 0 (Fin.cons 0 (fun _ : Fin 6 => (1 : ZMod 3)))
  have hcM : B.vec c ∈ tr ψ M0 := vec_mem_M ψ hbM rfl rfl
  have hn'1 : (m⁻¹ * n) * B.b 1 * (m⁻¹ * n)⁻¹ = b₀ := by
    have hmb : m⁻¹ * b₀ * m = b₀ := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hstd.2.1.1.2.1 hmK)
      calc m⁻¹ * b₀ * m = m⁻¹ * (b₀ * m) := by group
        _ = m⁻¹ * (m * b₀) := by rw [h]
        _ = b₀ := by group
    calc (m⁻¹ * n) * B.b 1 * (m⁻¹ * n)⁻¹ = m⁻¹ * (n * B.b 1 * n⁻¹) * m := by group
      _ = b₀ := by rw [hn1, hmb]
  have hw : (m⁻¹ * n) * B.vec (Pi.single 1 1 + c) * (m⁻¹ * n)⁻¹ =
      B.vec (Pi.single 0 1 + c) := by
    rw [B.vec_add, B.vec_add, B.vec_single, B.vec_single, hB.2.1]
    calc (m⁻¹ * n) * (B.b 1 * B.vec c) * (m⁻¹ * n)⁻¹ =
        ((m⁻¹ * n) * B.b 1 * (m⁻¹ * n)⁻¹) * ((m⁻¹ * n) * B.vec c * (m⁻¹ * n)⁻¹) := by group
      _ = b₀ * B.vec c := by rw [hn'1, hcen _ hcM]
  have hgood : IsConjLine b₀ (B.line (Pi.single 1 1 + c)) :=
    (hrec.2.1 _ e7Good_e1_ones.ne_zero).mpr e7Good_e1_ones
  have hgood' := isConjLine_map_conj hgood (m⁻¹ * n)
  rw [Basis3.line, MonoidHom.map_zpowers] at hgood'
  change IsConjLine b₀ (Subgroup.zpowers ((m⁻¹ * n) * B.vec (Pi.single 1 1 + c) * (m⁻¹ * n)⁻¹))
    at hgood'
  rw [hw] at hgood'
  have hne : Pi.single 0 1 + c ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [c] at this
  exact not_e7Good_e0_ones ((hrec.2.1 _ hne).mp hgood')

omit [Finite G] in
theorem exists_sigma_mul_of_conj (hH : E7NatHigh) (hC : E7NatCent) (hP : E7NatPsi)
    (ψ : ↥L7 ≃* ↥K) {n : G} (hnM : (tr ψ M0).map (MulAut.conj n).toMonoidHom = tr ψ M0)
    (hφn : ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) n hnM))
    (hK₀ : (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤ Subgroup.centralizer (K : Set G))
    (hn2 : ((tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom).map (MulAut.conj n).toMonoidHom =
      tr ψ (Jn 0)) :
    ∃ m ∈ tr ψ M0, ∃ hσ : (tr ψ M0).map (MulAut.conj (n * m)).toMonoidHom = tr ψ M0,
      ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) (n * m) hσ) ∧
      (tr ψ (Jn 0)).map (MulAut.conj (n * m)).toMonoidHom =
        (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ∧
      ((tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom).map (MulAut.conj (n * m)).toMonoidHom =
        tr ψ (Jn 0) ∧
      (tr ψ (Jn 1)).map (MulAut.conj (n * m)).toMonoidHom = tr ψ (Jn 6) ∧
      (tr ψ (Jn 3)).map (MulAut.conj (n * m)).toMonoidHom = tr ψ (Jn 5) ∧
      (tr ψ (Jn 4)).map (MulAut.conj (n * m)).toMonoidHom = tr ψ (Jn 4) ∧
      (tr ψ (Jn 5)).map (MulAut.conj (n * m)).toMonoidHom = tr ψ (Jn 3) ∧
      (tr ψ (Jn 6)).map (MulAut.conj (n * m)).toMonoidHom = tr ψ (J mu) ∧
      (tr ψ (J mu)).map (MulAut.conj (n * m)).toMonoidHom = tr ψ (J lam) ∧
      (tr ψ (J lam)).map (MulAut.conj (n * m)).toMonoidHom = tr ψ (Jn 1) := by
  obtain ⟨ψFS, hψFS, h1, h3, h4, h5, h6, hmu, hlam⟩ := hP
  obtain ⟨m₁, hm₁⟩ := hC.2.2.2.2.2 _ _ hφn hψFS
  let m : G := ((ψ ⟨m₁, m₁.2.1⟩ : ↥K) : G)
  have hmM : m ∈ tr ψ M0 := (coe_mem_tr_iff ψ _).mpr m₁.2
  have hmK : m ∈ K := tr_le_K ψ M0 hmM
  let σ : G := n * m
  have hmMM : (tr ψ M0).map (MulAut.conj m).toMonoidHom = tr ψ M0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hmM)
  have hσM : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0 := by
    rw [← map_conj_map_conj, hmMM, hnM]
  have hcσ : conjAut ψ (inf_le_left : M0 ≤ L7) σ hσM = ψFS := by
    have hψFS' : ψFS = conjAut ψ (inf_le_left : M0 ≤ L7) n hnM * MulAut.conj m₁ := by
      rw [← hm₁, mul_inv_cancel_left]
    rw [hψFS']
    refine MulEquiv.ext fun x => ?_
    have hinj : Function.Injective (fun y : ↥M0 =>
        ((trEquiv ψ (inf_le_left : M0 ≤ L7) y : ↥(tr ψ M0)) : G)) :=
      Subtype.val_injective.comp (trEquiv ψ inf_le_left).injective
    have key : ((trEquiv ψ (inf_le_left : M0 ≤ L7) (conjAut ψ inf_le_left σ hσM x) :
        ↥(tr ψ M0)) : G) = ((trEquiv ψ (inf_le_left : M0 ≤ L7)
          ((conjAut ψ inf_le_left n hnM * MulAut.conj m₁) x) : ↥(tr ψ M0)) : G) := by
      rw [trEquiv_conjAut, MulAut.mul_apply, trEquiv_conjAut, MulAut.conj_apply, map_mul,
        map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      have hm : ((trEquiv ψ (inf_le_left : M0 ≤ L7) m₁ : ↥(tr ψ M0)) : G) = m := by
        rw [coe_trEquiv]
      rw [hm]
      simp only [σ]
      group
    exact hinj key
  have himg : ∀ {X Y : Subgroup (ModGL .E7 (ZMod 2))} (hX : X ≤ M0) (hY : Y ≤ M0),
      (X.subgroupOf M0).map ψFS.toMonoidHom = Y.subgroupOf M0 →
        (tr ψ X).map (MulAut.conj σ).toMonoidHom = tr ψ Y := fun hX hY h =>
    map_conj_tr_of_conjAut ψ inf_le_left hX hY σ hσM (by rw [hcσ]; exact h)
  have hJM : ∀ i : Fin 7, i ≠ 0 → i ≠ 2 → Jn i ≤ M0 := hH.2.2.2.2.1
  have hmJ : (tr ψ (Jn 0)).map (MulAut.conj m).toMonoidHom = tr ψ (Jn 0) :=
    map_conj_eq_of_forall_commute fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (tr_jn0_le_centralizer ψ hx) m hmM)
  have hmK₀ : ((tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom).map
      (MulAut.conj m).toMonoidHom = (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom :=
    map_conj_eq_of_forall_commute fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hK₀ hx) m hmK)
  refine ⟨m, hmM, hσM, by rw [hcσ]; exact hψFS, ?_, ?_, himg (hJM 1 (by decide) (by decide))
    (hJM 6 (by decide) (by decide)) h1, himg (hJM 3 (by decide) (by decide))
    (hJM 5 (by decide) (by decide)) h3, himg (hJM 4 (by decide) (by decide))
    (hJM 4 (by decide) (by decide)) h4, himg (hJM 5 (by decide) (by decide))
    (hJM 3 (by decide) (by decide)) h5, himg (hJM 6 (by decide) (by decide)) hH.2.2.2.2.2.1 h6,
    himg hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 hmu, himg hH.2.2.2.2.2.2 (hJM 1 (by decide) (by decide))
    hlam⟩
  · rw [← map_conj_map_conj, hmJ]
  · rw [← map_conj_map_conj, hmK₀, hn2]

omit [Finite G] in
theorem exists_sigma_of_conj (hH : E7NatHigh) (hC : E7NatCent) (hP : E7NatPsi)
    (ψ : ↥L7 ≃* ↥K) {n : G} (hnM : (tr ψ M0).map (MulAut.conj n).toMonoidHom = tr ψ M0)
    (hφn : ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) n hnM))
    (hK₀ : (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤ Subgroup.centralizer (K : Set G))
    (hn2 : ((tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom).map (MulAut.conj n).toMonoidHom =
      tr ψ (Jn 0)) :
    ∃ σ : G, ∃ hσ : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0,
      ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) σ hσ) ∧
      (tr ψ (Jn 0)).map (MulAut.conj σ).toMonoidHom =
        (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ∧
      ((tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom).map (MulAut.conj σ).toMonoidHom =
        tr ψ (Jn 0) ∧
      (tr ψ (Jn 1)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 6) ∧
      (tr ψ (Jn 3)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 5) ∧
      (tr ψ (Jn 4)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 4) ∧
      (tr ψ (Jn 5)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 3) ∧
      (tr ψ (Jn 6)).map (MulAut.conj σ).toMonoidHom = tr ψ (J mu) ∧
      (tr ψ (J mu)).map (MulAut.conj σ).toMonoidHom = tr ψ (J lam) ∧
      (tr ψ (J lam)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 1) ∧
      ∃ m ∈ K, σ = n * m := by
  obtain ⟨m, hm, hσ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    exists_sigma_mul_of_conj hH hC hP ψ hnM hφn hK₀ hn2
  exact ⟨n * m, hσ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, m, tr_le_K ψ M0 hm, rfl⟩

theorem exists_sigma (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀) (hF : E7NatFrame) (hH : E7NatHigh)
    (hC : E7NatCent) (hP : E7NatPsi) (ψ : ↥L7 ≃* ↥K) {z : ↥L7}
    (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hψz : ((ψ z : ↥K) : G) = B.b 1)
    (hOut : Subgroup.normalizer (K : Set G) ≤ K ⊔ Subgroup.centralizer (K : Set G))
    (hNK : Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) ≤ Subgroup.normalizer (K : Set G))
    {n : G} (hnE : n ∈ Subgroup.normalizer (B.span : Set G)) (hn1 : n * B.b 1 * n⁻¹ = b₀)
    (hn0 : Subgroup.zpowers (n * b₀ * n⁻¹) = Subgroup.zpowers (B.b 1)) :
    ∃ σ : G, ∃ hσ : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0,
      ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) σ hσ) ∧
      (tr ψ (Jn 0)).map (MulAut.conj σ).toMonoidHom =
        (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ∧
      ((tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom).map (MulAut.conj σ).toMonoidHom =
        tr ψ (Jn 0) ∧
      (tr ψ (Jn 1)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 6) ∧
      (tr ψ (Jn 3)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 5) ∧
      (tr ψ (Jn 4)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 4) ∧
      (tr ψ (Jn 5)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 3) ∧
      (tr ψ (Jn 6)).map (MulAut.conj σ).toMonoidHom = tr ψ (J mu) ∧
      (tr ψ (J mu)).map (MulAut.conj σ).toMonoidHom = tr ψ (J lam) ∧
      (tr ψ (J lam)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 1) ∧
      ∃ m ∈ K, σ = n * m := by
  have hnM := conj_M_eq hstd hB hF hH hC ψ hz hψz hOut hnE hn1 hn0
  have hφn := not_isInner_conjAut_n hstd hB hrec hF hC ψ hz hψz hn1 hnM
  have hK₀ := K0_le_centralizer hstd hB hF hH hC ψ hz hψz hOut hNK hnE hn1 hn0
  have h00 : (Subgroup.zpowers b₀).map (MulAut.conj (n * n)).toMonoidHom =
      Subgroup.zpowers b₀ := by
    rw [← map_conj_map_conj, zpowers_map_conj, hn0, zpowers_map_conj, hn1]
  have hn2 := map_conj_map_conj_tr_jn0 hC ψ
    (hNK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h00)) hnM
  exact exists_sigma_of_conj hH hC hP ψ hnM hφn hK₀ hn2

end Native

end CFSG.StandardType.FrameRoute.FS81.E7Frame
