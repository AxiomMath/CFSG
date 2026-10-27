module

public import CFSG.Quasithin.Vol2.Ch12Sec5Tr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125Tr S125W Matrix
open CFSG.LieType.SteinbergBR.BlockPar CFSG.LocalAnalysis.ComponentInitial.LinearFlag

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125Tr2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def psi (F : Frame125 T L V) : SL5 →* MulAut ↥V :=
  (autOn L V).subtype.comp F.γ.symm.toMonoidHom

omit [Finite G] in
theorem psi_injective (F : Frame125 T L V) : Function.Injective (psi F) :=
  (autOn L V).subtype_injective.comp F.γ.symm.injective

omit [Finite G] in
theorem lbarSub_eq_map (F : Frame125 T L V) (P : Subgroup SL5) : lbarSub F P = P.map (psi F) := by
  rw [lbarSub, Subgroup.map_map]
  rfl

theorem isPGroup_centralizer (hH : Hyp125 G T L V) (hf : S125Ex.Facts125 G T L V) :
    IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨eL⟩ := S125Ex.lbar_equiv hH hf
  have hsimp : IsSimpleGroup ↥(autOn L V) := by
    have := (isSimpleGroup_sl_zmod_two (m := 5) (by norm_num)).1
    exact eL.isSimpleGroup
  have hcard : Nat.card ↥(autOn L V) = 9999360 :=
    (Nat.card_congr eL.toEquiv).trans card_sl_five_zmod_two
  have hO2 : pCoreOf 2 (autOn L V) = ⊥ :=
    pCoreOf_eq_bot_of_simple hsimp (fun hp => by
      obtain ⟨n, hn⟩ := hp.exists_card_eq
      rw [hcard] at hn
      have h24 : n < 24 :=
        (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by rw [← hn]; norm_num)
      interval_cases n <;> norm_num at hn)
  have hsq : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    obtain ⟨e⟩ := hH.quot
    have := (isSimpleGroup_sl_zmod_two (m := 5) (by norm_num)).1
    exact e.isSimpleGroup
  have hker := InternalSec.isPGroup_ker_of_simple hf.normalizes hsq hO2 hf.notCent
  intro x
  obtain ⟨k, hk⟩ := exists_two_pow_mem_of_mem_sup hH.hyp.sylow.1 hH.hyp.normalizes x.2.1
  have hk' : (x : G) ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨hk, Subgroup.pow_mem _ x.2.2 _⟩
  obtain ⟨m, hm⟩ := hker ⟨_, hk'⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val hm
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
  rw [pow_add, pow_mul]
  exact h1

omit [Finite G] in
theorem le_autOn_pCoreOf {X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) {N : Subgroup (MulAut ↥V)}
    (hNX : N ≤ autOn X V) (hNn : ∀ a ∈ autOn X V, ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N) : N ≤ autOn (pCoreOf 2 X) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ X, conjAct V ⟨x, hXV hx⟩ ∈ N}
      one_mem' := ⟨X.one_mem, by
        have : conjAct V ⟨1, hXV X.one_mem⟩ = 1 := map_one (conjAct V)
        rw [this]
        exact N.one_mem⟩
      mul_mem' := fun {x y} ⟨hx, hxN⟩ ⟨hy, hyN⟩ => ⟨X.mul_mem hx hy, by
        have : conjAct V ⟨x * y, hXV (X.mul_mem hx hy)⟩ =
            conjAct V ⟨x, hXV hx⟩ * conjAct V ⟨y, hXV hy⟩ := by
          rw [← map_mul]
          rfl
        rw [this]
        exact N.mul_mem hxN hyN⟩
      inv_mem' := fun {x} ⟨hx, hxN⟩ => ⟨X.inv_mem hx, by
        have : conjAct V ⟨x⁻¹, hXV (X.inv_mem hx)⟩ = (conjAct V ⟨x, hXV hx⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this]
        exact N.inv_mem hxN⟩ }
  have hYX : Y ≤ X := fun _ h => h.1
  have hYn : (Y.subgroupOf X).Normal := by
    constructor
    intro y hy x
    have hyN : conjAct V ⟨(y : G), hXV y.2⟩ ∈ N := (Subgroup.mem_subgroupOf.1 hy).2
    refine ⟨X.mul_mem (X.mul_mem x.2 y.2) (X.inv_mem x.2), ?_⟩
    have e : conjAct V ⟨(x : G) * y * (x : G)⁻¹,
        hXV (X.mul_mem (X.mul_mem x.2 y.2) (X.inv_mem x.2))⟩ =
        conjAct V ⟨x, hXV x.2⟩ * conjAct V ⟨y, hXV y.2⟩ * (conjAct V ⟨x, hXV x.2⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have h1 := hNn _ (mem_autOn_iff_exists.mpr ⟨x, hXV x.2, x.2, rfl⟩) _ hyN
    rw [← e] at h1
    exact h1
  have hY2 : IsPGroup 2 Y := by
    rintro ⟨y, hyX, hyN⟩
    obtain ⟨k, hk⟩ := hN2 ⟨_, hyN⟩
    have hk' : conjAct V ⟨y ^ 2 ^ k, hXV (X.pow_mem hyX _)⟩ = 1 := by
      have h1 := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
      rw [← h1, ← map_pow]
      rfl
    have hc : y ^ 2 ^ k ∈ X ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨X.pow_mem hyX _, ?_⟩
      show y ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h2 := congrArg (fun a : MulAut ↥V => ((a ⟨v, hv⟩ : ↥V) : G)) hk'
      simp only [MulAut.one_apply] at h2
      change y ^ 2 ^ k * v * (y ^ 2 ^ k)⁻¹ = v at h2
      calc v * y ^ 2 ^ k = y ^ 2 ^ k * v * (y ^ 2 ^ k)⁻¹ * y ^ 2 ^ k := by rw [h2]
        _ = y ^ 2 ^ k * v := by group
    obtain ⟨m, hm⟩ := hC ⟨_, hc⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
    rw [pow_add, pow_mul]
    exact h1
  have hYO : Y ≤ pCoreOf 2 X := CFSG.LieType.BorelTits.le_pCoreOf 2 hYX hYn hY2
  intro n hn
  obtain ⟨x, hx, hxX, rfl⟩ := mem_autOn_iff_exists.mp (hNX hn)
  exact mem_autOn_iff_exists.mpr ⟨x, hx, hYO ⟨hxX, hn⟩, rfl⟩

theorem autOn_pCoreOf_props {X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn (pCoreOf 2 X) V ≤ autOn X V ∧
      (∀ a ∈ autOn X V, ∀ n ∈ autOn (pCoreOf 2 X) V, a * n * a⁻¹ ∈ autOn (pCoreOf 2 X) V) ∧
      IsPGroup 2 (autOn (pCoreOf 2 X) V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  refine ⟨A4.autOn_mono hle, ?_, CFSG.Quasithin.isPGroup_autOn
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) (hle.trans hXV)⟩
  intro a ha n hn
  obtain ⟨x, hx, hxX, rfl⟩ := mem_autOn_iff_exists.mp ha
  obtain ⟨y, hy, hyO, rfl⟩ := mem_autOn_iff_exists.mp hn
  have hxy : x * y * x⁻¹ ∈ pCoreOf 2 X :=
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hxX) y).1 hyO
  refine mem_autOn_iff_exists.mpr ⟨x * y * x⁻¹, hXV (hle hxy), hxy, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite G] in
theorem T_le_normalizer_sub [Finite G] (F : Frame125 T L V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (S : Finset (Fin 10))
    (hS : ∀ u : SL5, IsUpperTri u →
      CoordFix S (JonesParshall.wedgeMat (u : Matrix (Fin 5) (Fin 5) (ZMod 2)))) :
    T ≤ Subgroup.normalizer (F.sub S : Set G) := by
  intro t ht
  apply mem_normalizer_of_conj_le
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨u, hu, hact⟩ := F.borel t ht
  let w : ↥V := conjAct V ⟨t, hTV ht⟩ v
  have hw : F.e w = Multiplicative.ofAdd (JonesParshall.wedgeRep u
      (Multiplicative.toAdd (F.e v))) := hact v w rfl
  refine ⟨w, ?_, rfl⟩
  change ∀ k ∉ S, Multiplicative.toAdd (F.e w) k = 0
  rw [hw, toAdd_ofAdd, S125ZV.wedgeRep_apply]
  exact mulVec_vanish (hS u hu) hv

theorem stabGam_of_upperTri {u : SL5} (hu : IsUpperTri u) (k : ℕ) : StabGam k u :=
  fun i j hj hi => hu i j (by
    change j.val < i.val
    omega)

@[expose] noncomputable def theta (F : Frame125 T L V) {d e : ℕ} (hde : d + e = 5) :
    Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2) →* MulAut ↥V :=
  (psi F).comp (reindexSL (ZMod 2) hde).toMonoidHom

omit [Finite G] in
theorem theta_injective (F : Frame125 T L V) {d e : ℕ} (hde : d + e = 5) :
    Function.Injective (theta F hde) :=
  (psi_injective F).comp (reindexSL (ZMod 2) hde).injective

omit [Finite G] in
theorem autOn_mi_eq_theta (F : Frame125 T L V) {S : Finset (Fin 10)} {d e : ℕ}
    (hde : d + e = 5) (hstab : F.IsStab (mi T L (F.sub S)) d) :
    autOn (mi T L (F.sub S)) V = (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2))).map (theta F hde) := by
  rw [autOn_eq_of_isStab hstab, lbarSub_eq_map, ← map_parQ_eq_stabK hde, Subgroup.map_map]
  rfl

theorem lbar_eq (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {S : Finset (Fin 10)} {d e : ℕ}
    (hde : d + e = 5) (hstab : F.IsStab (mi T L (F.sub S)) d)
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))}
    (hres : (CFSG.perfectResidual ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2)))).map parQ.subtype = J) :
    autOn (li L (F.sub S)) V = J.map (theta F hde) := by
  have hXV : L ⊓ Subgroup.normalizer ((F.sub S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (V : Set G) := inf_le_left.trans hLV
  rw [li, autOn_inSubgroup_perfectResidual hXV,
    perfectResidual_map_subtype_congr (autOn_inf_eq_mi F hLV hTV (sub_le F S)),
    perfectResidual_map_subtype_congr (autOn_eq_of_isStab hstab),
    perfectResidual_map_subtype_congr (lbarSub_eq_map F (stabK d)),
    ← map_perfectResidual_subgroup (psi F) (stabK d),
    ← perfectResidual_map_subtype_congr (map_parQ_eq_stabK hde),
    ← map_perfectResidual_subgroup, hres, Subgroup.map_map]
  rfl

omit [Finite G] in
theorem sup_le_mi {W : Subgroup G} (hTW : T ≤ Subgroup.normalizer (W : Set G)) :
    li L W ⊔ T ≤ mi T L W := by
  refine sup_le ?_ (le_inf le_sup_right hTW)
  have h : li L W ≤ L ⊓ Subgroup.normalizer (W : Set G) := Subgroup.map_subtype_le _
  exact h.trans (inf_le_inf_right _ le_sup_left)

theorem uniRad_conj_mem {d e : ℕ} {q r : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)}
    (hq : q ∈ (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))))
    (hr : r ∈ S125Pb.uniRad (Fin d) (Fin e)) : q * r * q⁻¹ ∈ S125Pb.uniRad (Fin d) (Fin e) := by
  have hn : ((S125Pb.uniRad (Fin d) (Fin e)).subgroupOf parQ).Normal := by
    rw [← S125Pb.ker_chi]
    exact MonoidHom.normal_ker _
  have h := hn.conj_mem ⟨r, S125Pb.uniRad_le_parQ hr⟩ (Subgroup.mem_subgroupOf.2 hr) ⟨q, hq⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem rbar_inf_lbar (F : Frame125 T L V) (hH : Hyp125 G T L V) (hf : S125Ex.Facts125 G T L V)
    {S : Finset (Fin 10)} {d e : ℕ} (hde : d + e = 5) (hstab : F.IsStab (mi T L (F.sub S)) d)
    (hTW : T ≤ Subgroup.normalizer ((F.sub S : Subgroup G) : Set G))
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))}
    (hres : (CFSG.perfectResidual ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2)))).map parQ.subtype = J)
    (hUJ : S125Pb.uniRad (Fin d) (Fin e) ≤ J)
    (hO : ∀ N : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)), N ≤ J →
      (N.subgroupOf J).Normal → IsPGroup 2 N → N ≤ S125Pb.uniRad (Fin d) (Fin e)) :
    autOn (ri T L (F.sub S)) V ⊓ autOn (li L (F.sub S)) V =
      (S125Pb.uniRad (Fin d) (Fin e)).map (theta F hde) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := F.sub S with hW
  have hliL : li L W ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hXV : li L W ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (hliL.trans hf.normalizes) hf.T_le
  obtain ⟨hRX, hRn, hR2⟩ := autOn_pCoreOf_props hXV
  have hLb := lbar_eq F hf.normalizes hf.T_le hde hstab hres
  have hLX : autOn (li L W) V ≤ autOn (li L W ⊔ T) V := A4.autOn_mono le_sup_left
  have hXM : autOn (li L W ⊔ T) V ≤ (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2))).map (theta F hde) := by
    rw [← autOn_mi_eq_theta F hde hstab]
    exact A4.autOn_mono (sup_le_mi hTW)
  apply le_antisymm
  · rintro x ⟨hxR, hxL⟩
    rw [hLb] at hxL
    obtain ⟨j, hjJ, rfl⟩ := hxL
    set N : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) :=
      (autOn (ri T L W) V).comap (theta F hde) ⊓ J with hN
    have hNJ : N ≤ J := inf_le_right
    have hNn : (N.subgroupOf J).Normal := by
      constructor
      intro n hn j'
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨?_, J.mul_mem (J.mul_mem j'.2 n.2) (J.inv_mem j'.2)⟩
      change theta F hde ((j' : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) * n *
        (j' : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))⁻¹) ∈ autOn (ri T L W) V
      rw [map_mul, map_mul, map_inv]
      have hj'X : theta F hde j' ∈ autOn (li L W ⊔ T) V := hLX (hLb ▸ ⟨j', j'.2, rfl⟩)
      exact hRn _ hj'X _ hn.1
    have hN2 : IsPGroup 2 N := by
      let φ : ↥N →* ↥(autOn (ri T L W) V) :=
        { toFun := fun n => ⟨theta F hde n, n.2.1⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
      refine hR2.of_injective φ (fun a b h => Subtype.ext (theta_injective F hde ?_))
      have := congrArg (fun x : ↥(autOn (ri T L W) V) => (x : MulAut ↥V)) h
      exact this
    exact ⟨j, hO N hNJ hNn hN2 ⟨hxR, hjJ⟩, rfl⟩
  · have hU2 : IsPGroup 2 ((S125Pb.uniRad (Fin d) (Fin e)).map (theta F hde)) :=
      S125Pb.isPGroup_uniRad.map _
    have hUL : (S125Pb.uniRad (Fin d) (Fin e)).map (theta F hde) ≤ autOn (li L W) V := by
      rw [hLb]
      exact Subgroup.map_mono hUJ
    refine le_inf ?_ hUL
    have hC : IsPGroup 2 ↥((li L W ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) :=
      (isPGroup_centralizer hH hf).to_le (inf_le_inf_right _ (sup_le_sup_right hliL _))
    refine le_autOn_pCoreOf hXV hC (hUL.trans hLX) ?_ hU2
    intro a ha n hn
    obtain ⟨q, hq, rfl⟩ := hXM ha
    obtain ⟨r, hr, rfl⟩ := hn
    exact ⟨q * r * q⁻¹, uniRad_conj_mem hq hr, by rw [map_mul, map_mul, map_inv]⟩

theorem quotSL_of (F : Frame125 T L V) (hH : Hyp125 G T L V) (hf : S125Ex.Facts125 G T L V)
    {S : Finset (Fin 10)} {d e : ℕ} (hde : d + e = 5) (hstab : F.IsStab (mi T L (F.sub S)) d)
    (hTW : T ≤ Subgroup.normalizer ((F.sub S : Subgroup G) : Set G))
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))}
    (hres : (CFSG.perfectResidual ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2)))).map parQ.subtype = J)
    (hUJ : S125Pb.uniRad (Fin d) (Fin e) ≤ J)
    (hO : ∀ N : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)), N ≤ J →
      (N.subgroupOf J).Normal → IsPGroup 2 N → N ≤ S125Pb.uniRad (Fin d) (Fin e))
    {d' : ℕ} [hUn : ((S125Pb.uniRad (Fin d) (Fin e)).subgroupOf J).Normal]
    (hq : Nonempty (↥J ⧸ (S125Pb.uniRad (Fin d) (Fin e)).subgroupOf J ≃*
      Matrix.SpecialLinearGroup (Fin d') (ZMod 2))) :
    QuotSL (li L (F.sub S)) (ri T L (F.sub S)) V d' := by
  set W := F.sub S with hW
  have hliL : li L W ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hXV : li L W ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (hliL.trans hf.normalizes) hf.T_le
  obtain ⟨-, hRn, -⟩ := autOn_pCoreOf_props hXV
  have hLX : autOn (li L W) V ≤ autOn (li L W ⊔ T) V := A4.autOn_mono le_sup_left
  have hLb := lbar_eq F hf.normalizes hf.T_le hde hstab hres
  have hRL := rbar_inf_lbar F hH hf hde hstab hTW hres hUJ hO
  have hnorm : ((autOn (ri T L W) V).subgroupOf (autOn (li L W) V)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hRn _ (hLX g.2) _ hn
  refine ⟨hnorm, ?_⟩
  obtain ⟨q⟩ := hq
  let eJ : ↥J ≃* ↥(autOn (li L W) V) :=
    (J.equivMapOfInjective (theta F hde) (theta_injective F hde)).trans
      (MulEquiv.subgroupCongr hLb.symm)
  have hmap : ((S125Pb.uniRad (Fin d) (Fin e)).subgroupOf J).map eJ.toMonoidHom =
      (autOn (ri T L W) V).subgroupOf (autOn (li L W) V) := by
    ext y
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have h1 : ((eJ j : ↥(autOn (li L W) V)) : MulAut ↥V) = theta F hde j := rfl
      change ((eJ j : ↥(autOn (li L W) V)) : MulAut ↥V) ∈ autOn (ri T L W) V
      rw [h1]
      have : theta F hde j ∈ autOn (ri T L W) V ⊓ autOn (li L W) V :=
        hRL ▸ ⟨j, Subgroup.mem_subgroupOf.1 hj, rfl⟩
      exact this.1
    · intro hy
      have : (y : MulAut ↥V) ∈ (S125Pb.uniRad (Fin d) (Fin e)).map (theta F hde) :=
        hRL ▸ ⟨hy, y.2⟩
      obtain ⟨r, hr, hry⟩ := this
      refine ⟨⟨r, hUJ hr⟩, Subgroup.mem_subgroupOf.2 hr, Subtype.ext ?_⟩
      exact hry
  exact ⟨(QuotientGroup.congr _ _ eJ hmap).symm.trans q⟩

end S125Tr2

end CFSG.Quasithin.H13
