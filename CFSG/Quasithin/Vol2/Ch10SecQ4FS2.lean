module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS1
public import CFSG.Quasithin.Vol2.Ch10SecQ4S4
public import CFSG.Quasithin.Vol2.Ch10SecQ4H5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.Quasithin.H13.LocDblCComp

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem card_quot_of_isAltType {K : Subgroup G} (hKa : IsAltType K 5) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60 := by
  obtain ⟨α, hαs, hαk, -⟩ := hKa
  rw [← SecB.card_alt5, ← hαk]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv

omit [Finite G] in
theorem isQuasisimple_of_isAltType {K : Subgroup G} (hKs : IsShort2 K) (hKa : IsAltType K 5) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
  hKs.2.2.2.1.resolve_right (by rw [card_quot_of_isAltType hKa]; norm_num)

theorem exists_three_elt_block (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) {K : Subgroup G} (hKc : K ∈ cComp H) (hKs : IsShort2 K)
    (hKa : IsAltType K 5) :
    ∃ q ∈ K, orderOf q = 3 ∧ q ∈ fsuM T L ∧
      q ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf T H := (SecB.minParabolic_of_isHStar h331 hyp hH).isSylow
  have hKH := le_of_mem_cComp hKc
  have hSK : IsSylowTwoOf (T ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKc) hT
  have hqs := isQuasisimple_of_isAltType hKs hKa
  obtain ⟨α, hαs, hαk, -⟩ := hKa
  set P := ((T ⊓ K).subgroupOf K).map α with hPdef
  have hP4 : Nat.card P = 4 :=
    card_of_isSylowTwoOf (SecB.isSylowTwoOf_map_of_surjective hSK α hαs)
  have hQK : pCoreOf 2 K ≤ T ⊓ K :=
    le_inf ((A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)).trans
      (pCoreOf_two_le_of_isSylowTwoOf hT)) (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  have hpre : ∀ y : ↥K, α y ∈ P → (y : G) ∈ T ⊓ K := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hk : x⁻¹ * y ∈ α.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [hαk] at hk
    have h2 := hQK (Subgroup.mem_map_of_mem K.subtype hk)
    have e : (y : G) = x * ((x⁻¹ * y : ↥K) : G) := by simp
    rw [e]
    exact (T ⊓ K).mul_mem (Subgroup.mem_subgroupOf.mp hx) h2
  obtain ⟨c, hc3, hc1, hcN⟩ := exists_three_normalizer hP4
  obtain ⟨k, hk⟩ := hαs c
  have hko : orderOf (α k) = 3 := by rw [hk]; exact orderOf_eq_prime hc3 hc1
  set q0 := k ^ (orderOf k / 3) with hq0def
  have hq0 : orderOf q0 = 3 := C10E4.orderOf_pow_div_three α k hko
  have hαqN : α q0 ∈ Subgroup.normalizer (P : Set A5) := by
    rw [hq0def, map_pow, hk]
    exact Subgroup.pow_mem _ hcN _
  have hαqN' : (α q0)⁻¹ ∈ Subgroup.normalizer (P : Set A5) := Subgroup.inv_mem _ hαqN
  have hconj : ∀ (g : ↥K), (α g ∈ Subgroup.normalizer (P : Set A5)) →
      ∀ x ∈ T ⊓ K, (g : G) * x * (g : G)⁻¹ ∈ T ⊓ K := by
    intro g hg x hx
    have hm : (g : G) * x * (g : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem g.2 hx.2) (K.inv_mem g.2)
    refine hpre ⟨_, hm⟩ ?_
    have e : (⟨(g : G) * x * (g : G)⁻¹, hm⟩ : ↥K) = g * ⟨x, hx.2⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp
      ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hqN : (q0 : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj q0 hαqN x, fun h => ?_⟩
    have := hconj q0⁻¹ (by rw [map_inv]; exact hαqN') _ h
    simpa [mul_assoc] using this
  refine ⟨q0, q0.2, by rw [Subgroup.orderOf_coe]; exact hq0, ?_, hqN⟩
  set R := conjClosure (T ⊓ K) T with hR
  have hRT : R ≤ T := conjClosure_le fun s hs x hx => T.mul_mem (T.mul_mem hs hx.1) (T.inv_mem hs)
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := le_normalizer_conjClosure _ _
  have key : ∀ g ∈ K, g ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
      ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hgK hgN r hr
    induction hr using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨s, hs, x, hx, rfl⟩ := hy
      have hKs' : K.map (MulAut.conj s).toMonoidHom ∈ cComp H :=
        H13.LocDbl.map_conj_mem_cComp hKc (Subgroup.le_normalizer (hT.1 hs))
      have hyKs : s * x * s⁻¹ ∈ K.map (MulAut.conj s).toMonoidHom := ⟨x, hx.2, rfl⟩
      by_cases he : K.map (MulAut.conj s).toMonoidHom = K
      · have hy : s * x * s⁻¹ ∈ T ⊓ K :=
          ⟨T.mul_mem (T.mul_mem hs hx.1) (T.inv_mem hs), he ▸ hyKs⟩
        exact le_conjClosure _ _ ((Subgroup.mem_normalizer_iff.mp hgN _).mp hy)
      · have hc := commutator_eq_bot_of_mem_cComp hKc hKs' hKs
          ((Lin2.isShort2_map_equiv_iff (MulAut.conj s) K).mpr hKs) hqs (Ne.symm he)
        have hcomm : g * (s * x * s⁻¹) = (s * x * s⁻¹) * g :=
          (Subgroup.mem_centralizer_iff.mp
            ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) hgK) _ hyKs).symm
        rw [hcomm, mul_inv_cancel_right]
        exact mem_conjClosure hs hx
    | one => simp
    | mul y z _ _ hy hz =>
      have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [e]
      exact R.mul_mem hy hz
    | inv y _ hy =>
      have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [e]
      exact R.inv_mem hy
  have hqR : (q0 : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨key _ q0.2 hqN r, fun h => ?_⟩
    have := key _ (K.inv_mem q0.2) (Subgroup.inv_mem _ hqN) _ h
    simpa [mul_assoc] using this
  set Y := H ⊓ Subgroup.normalizer (R : Set G) with hY
  have hTY : T ≤ Y := le_inf hT.1 hTR
  have hYH : Y < H := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have hHR : H ≤ Subgroup.normalizer (R : Set G) := heq ▸ inf_le_right
    have hR2 : IsPGroup 2 R := hT.2.1.to_le hRT
    have hRO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRT.trans hT.1) hHR hR2
    have hSO : T ⊓ K ≤ pCoreOf 2 K := by
      have hK2 : K ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ K : Subgroup G) : Set G) :=
        fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hx), Subgroup.le_normalizer hx⟩
      refine le_trans (le_inf ((le_conjClosure _ _).trans hRO) inf_le_right) ?_
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hK2
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
    have hPb : P = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : (x : G) ∈ pCoreOf 2 K := hSO (Subgroup.mem_subgroupOf.mp hx)
      obtain ⟨x', hx', hxx⟩ := h1
      have hxe : x' = x := Subtype.ext hxx
      rw [hxe] at hx'
      rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, hαk]
      exact hx'
    rw [hPb, Subgroup.card_bot] at hP4
    omega
  have hYM := C10E4.le_of_isUniqueMaxOver' (SecB.isUniqueMaxOver_of_isHStar h331 hyp hH) hTY hYH
  exact (hYM ⟨hKH q0.2, hqR⟩).2

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
