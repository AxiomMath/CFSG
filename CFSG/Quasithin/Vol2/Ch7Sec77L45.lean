module

public import CFSG.Quasithin.Vol2.Ch7Sec77KQuot
public import CFSG.Quasithin.Vol2.Ch7Sec77LPar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall
public import CFSG.Quasithin.EmptyFaithful.T1515eE

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular upperTriangular flagStabilizer
  normalizer_unitriangular borelOvergroupCuts borel_overgroups flagStabilizer_empty)
open scoped commutatorElement

namespace LFlag

theorem upperTriangular_eq_unitriangular {n : ℕ} :
    upperTriangular n (ZMod 2) = unitriangular n (ZMod 2) :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic.upperTriangular_eq_unitriangular

end LFlag

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem le_normalizer_oPrimeResidualOf_three (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oPrimeResidualOf 3 H : Set G) := by
  intro h hh
  have hc : ∀ g ∈ H, ∀ q ∈ oPrimeResidualOf 3 H, g * q * g⁻¹ ∈ oPrimeResidualOf 3 H := by
    intro g hg q hq
    unfold oPrimeResidualOf at hq ⊢
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxH, k, hk⟩ := hx
      refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), k, ?_⟩
      rw [← hk]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  refine Subgroup.mem_normalizer_iff.2 fun q => ⟨hc h hh q, fun hq => ?_⟩
  have := hc h⁻¹ (H.inv_mem hh) _ hq
  simpa [mul_assoc] using this


omit [Finite G] in
theorem isSylowTwoOf_subgroupOf_top {X : Type*} [Group X] {S H : Subgroup X}
    (hS : IsSylowTwoOf S H) : IsSylowTwoOf (S.subgroupOf H) (⊤ : Subgroup ↥H) := by
  refine ⟨le_top, ?_, ?_⟩
  · have e : ↥(S.subgroupOf H) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hS.1
    exact hS.2.1.of_injective e.toMonoidHom e.injective
  · have h := hS.2.2
    have e : ((S.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).index = (S.subgroupOf H).index :=
      Subgroup.index_comap_of_surjective (S.subgroupOf H) (f := (⊤ : Subgroup ↥H).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    rw [e]
    exact h

omit [Finite G] in
theorem mem_normalizer_centralizer {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun c => ⟨fun hc => ?_, fun hc => ?_⟩
  · refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have h1 : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) v).1 hv
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.1 hc _ h1
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h2]
      _ = g * c * g⁻¹ * v := by group
  · refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have h1 : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hg v).1 hv
    have h2 := Subgroup.mem_centralizer_iff.1 hc _ h1
    have e : v * c = g⁻¹ * ((g * v * g⁻¹) * (g * c * g⁻¹)) * g := by group
    rw [e, h2]
    group

omit [Finite G] in
theorem map_autOn_le_normalizer {V K Z W : Subgroup G} {X : Type*} [Group X]
    (θc : ↥(autOn K V) ≃* X) (hZW : Z ≤ Subgroup.normalizer (W : Set G)) :
    ((autOn Z V).subgroupOf (autOn K V)).map θc.toMonoidHom ≤
      Subgroup.normalizer ((((autOn W V).subgroupOf (autOn K V)).map θc.toMonoidHom :
        Subgroup X) : Set X) := by
  rw [← Subgroup.map_equiv_normalizer_eq]
  refine Subgroup.map_mono fun z hz => Subgroup.mem_normalizer_iff.2 fun w => ⟨fun hw => ?_,
    fun hw => ?_⟩
  · exact CFSG.Quasithin.InternalSec.autOn_normal_of hZW _ hz _ hw
  · have h1 := CFSG.Quasithin.InternalSec.autOn_normal_of hZW _ (Subgroup.inv_mem _ hz) _ hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    have h2 : ((z : MulAut ↥V))⁻¹ * ((z * w * z⁻¹ : ↥(autOn K V)) : MulAut ↥V) *
        ((z : MulAut ↥V))⁻¹⁻¹ ∈ autOn W V := h1
    have e' : ((z : MulAut ↥V))⁻¹ * ((z * w * z⁻¹ : ↥(autOn K V)) : MulAut ↥V) *
        ((z : MulAut ↥V))⁻¹⁻¹ = (w : MulAut ↥V) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rwa [e'] at h2

theorem map_trans_eq {X₁ X₂ : Type*} [Group X₁] [Group X₂] (θc : X₁ ≃* X₂) (ct : X₁ ≃* X₁)
    {Z : Subgroup X₁} (h : Z.map ct.toMonoidHom = Z) :
    (Z.map θc.toMonoidHom).map (θc.symm.trans (ct.trans θc)).toMonoidHom =
      Z.map θc.toMonoidHom := by
  rw [Subgroup.map_map]
  have e : (θc.symm.trans (ct.trans θc)).toMonoidHom.comp θc.toMonoidHom =
      θc.toMonoidHom.comp ct.toMonoidHom := by
    ext x
    simp
  rw [e, ← Subgroup.map_map, h]

theorem exists_coord_sylow {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : 1 ≤ m)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) {S : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) :
    ∃ θc : X ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2),
      S.map θc.toMonoidHom = unitriangular m (ZMod 2) := by
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hS.2.1.map _, ?_⟩
    have h1 := hS.2.2
    rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h1
    rw [show ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index from
      Subgroup.relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact h1
  have hU : IsSylowTwoOf (unitriangular m (ZMod 2)) ⊤ :=
    CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular hm
  obtain ⟨g, -, hg⟩ := hS'.exists_conj hU
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hg, Subgroup.map_map]
  rfl


@[expose] def ExcL45 (T L I : Subgroup G) (θ : G) (Vp H K : Subgroup G) : Prop :=
  ∃ (θc : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
      Subgroup.centralizer (fsuV T I : Set G))))) ≃*
        Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)),
    ((autOn (fsuM T L ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
        (fsuV T I : Set G))))).subgroupOf (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
          Subgroup.centralizer (fsuV T I : Set G)))))).map θc.toMonoidHom =
      flagStabilizer 4 (ZMod 2) {1, 3} ∧
    (∃ (y : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
      (hθN : θ ∈ Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
        Subgroup.centralizer (fsuV T I : Set G))) : Subgroup G) : Set G)),
      LPar.Cfg 4 {1, 3}
        (((autOn (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)))
          (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
            (fsuV T I : Set G))))).subgroupOf (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
              Subgroup.centralizer (fsuV T I : Set G)))))).map θc.toMonoidHom)
        (((autOn (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊓
            Subgroup.centralizer (fsuV T I : Set G))
          (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
            (fsuV T I : Set G))))).subgroupOf (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
              Subgroup.centralizer (fsuV T I : Set G)))))).map θc.toMonoidHom) y ∧
      ((θc.symm y : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓
          Subgroup.centralizer (fsuV T I : Set G)))))) : MulAut ↥(omegaOneCenterOf (pCoreOf 2
            (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))))) =
        conjAct (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))))
          ⟨θ, hθN⟩) ∧
    K ⊔ (T ⊓ Subgroup.centralizer (Vp : Set G)) = H

theorem le_normalizer_sup_of {A B C : Subgroup G}
    (hB : A ≤ Subgroup.normalizer (B : Set G)) (hC : A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  intro a ha
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hle : (B ⊔ C).map (MulAut.conj a).toMonoidHom ≤ B ⊔ C := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (hB ha) b).1 hb
    · rintro _ ⟨c, hc, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (hC ha) c).1 hc
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_mem_autOn {V Z : Subgroup G} {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htZ : t ∈ Subgroup.normalizer (Z : Set G)) {a : MulAut ↥V} (ha : a ∈ autOn Z V) :
    conjAct V ⟨t, htV⟩ * a * (conjAct V ⟨t, htV⟩)⁻¹ ∈ autOn Z V := by
  obtain ⟨g, hgZ, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.1 ha
  rw [← map_inv, ← map_mul, ← map_mul]
  refine CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨_, ?_, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 htZ g).1 hgZ

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem exists_zpow_th_of_odd (hc : S.Coord θ e) {x : G} (hxM : x ∈ fsuM T L)
    (hx0 : x ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
      Subgroup G) : Set G))
    (hxo : Odd (orderOf x)) :
    ∃ j : ℕ, x * (θ ^ j)⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  set X := fsuM T L ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
    Subgroup G) : Set G) with hX
  have hXM : X ≤ fsuM T L := inf_le_left
  have hX1 : X ≤ Subgroup.centralizer ({S.vec e a1} : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_a1_mem_V0 hc)))
  obtain ⟨φ, hφ⟩ := exists_stabHom hc hXM hX1
  set χ : ↥X →* GL (Fin 2) (ZMod 2) := blkHom.comp φ with hχ
  have hcent : ∀ z : ↥X, χ z = 1 → (z : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    intro z hz
    have hb : blk (φ z : SL32) = 1 := by
      have h1 : (χ z : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by rw [hz]; rfl
      rwa [hχ, MonoidHom.comp_apply, coe_blkHom] at h1
    exact mem_centralizer_of_blk (S.hMN (hXM z.2)) (φ z).2 hb (hφ z).symm
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_b1_mem_V0 hc)) z.2.2)
  have hθX : θ ∈ X := ⟨S.L_le_fsuM hc.mem, Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp hv.2⟩
  have hxX : x ∈ X := ⟨hxM, hx0⟩
  have hφθ : (φ ⟨θ, hθX⟩ : SL32) = th0 := SL3One.rho_injective ((hφ ⟨θ, hθX⟩).trans hc.hθ)
  have hφθ3 : φ ⟨θ, hθX⟩ ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hφθ, th0_pow_three, OneMemClass.coe_one])
  have hχθ3 : χ ⟨θ, hθX⟩ ^ 3 = 1 := by
    rw [hχ, MonoidHom.comp_apply, ← map_pow, hφθ3, map_one]
  have hχθ1 : χ ⟨θ, hθX⟩ ≠ 1 := by
    intro h
    have h1 : (χ ⟨θ, hθX⟩ : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by rw [h]; rfl
    rw [hχ, MonoidHom.comp_apply, coe_blkHom, hφθ] at h1
    exact blk_th0_ne_one h1
  have hχx3 : χ ⟨x, hxX⟩ ^ 3 = 1 := by
    have h1 : χ ⟨x, hxX⟩ ^ orderOf x = 1 := by
      rw [← map_pow]
      have : (⟨x, hxX⟩ : ↥X) ^ orderOf x = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, map_one]
    have h2 : χ ⟨x, hxX⟩ ^ Nat.gcd (orderOf x) 6 = 1 :=
      pow_gcd_eq_one.mpr ⟨h1, gl2_pow_six (χ ⟨x, hxX⟩)⟩
    have h3 : Nat.gcd (orderOf x) 6 ∣ 3 := by
      have h4 : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hxo
      have h5 : Nat.gcd (orderOf x) 6 ∣ Nat.gcd (orderOf x) 2 * Nat.gcd (orderOf x) 3 :=
        (Nat.Coprime.gcd_mul (orderOf x) (by norm_num : Nat.Coprime 2 3)).dvd
      rw [h4.gcd_eq_one, one_mul] at h5
      exact h5.trans (Nat.gcd_dvd_right _ _)
    obtain ⟨c, hc'⟩ := h3
    rw [hc', pow_mul, h2, one_pow]
  have hxθ : ∀ j : ℕ, χ ⟨x, hxX⟩ * (χ ⟨θ, hθX⟩ ^ j)⁻¹ = 1 →
      x * (θ ^ j)⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    intro j hj
    have hmem : x * (θ ^ j)⁻¹ ∈ X := X.mul_mem hxX (X.inv_mem (X.pow_mem hθX j))
    refine hcent ⟨_, hmem⟩ ?_
    have e : (⟨x * (θ ^ j)⁻¹, hmem⟩ : ↥X) = ⟨x, hxX⟩ * ((⟨θ, hθX⟩ : ↥X) ^ j)⁻¹ := rfl
    rw [e, map_mul, map_inv, map_pow]
    exact hj
  rcases gl2_cube_cases _ _ hχθ3 hχθ1 hχx3 with h | h | h
  · exact ⟨0, hxθ 0 (by rw [h, pow_zero, inv_one, mul_one])⟩
  · exact ⟨1, hxθ 1 (by rw [pow_one, h, mul_inv_cancel])⟩
  · exact ⟨2, hxθ 2 (by rw [h, pow_two, mul_inv_cancel])⟩

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem oTwoUpper_le_sup :
    oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ≤
      (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊓
        Subgroup.centralizer (fsuV T I : Set G)) ⊔ Subgroup.zpowers θ := by
  have hc := C.conf.hc
  have hθL₀ : θ ∈ oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) :=
    S.th_mem_oTwoUpper hc C.conf.vp_le
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxL, hxV0⟩, hxo⟩
  have hxL₀ : x ∈ oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) :=
    mem_oTwoUpper_of_odd ⟨hxL, hxV0⟩ hxo
  have hx0 : x ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
      Subgroup G) : Set G) := by
    rw [← C.hVp]
    exact hxV0
  obtain ⟨j, hj⟩ := exists_zpow_th_of_odd hc (S.L_le_fsuM hxL) hx0 hxo
  have e : x = x * (θ ^ j)⁻¹ * θ ^ j := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨?_, hj⟩)
    (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers θ j))
  exact Subgroup.mul_mem _ hxL₀ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hθL₀ j))

theorem inf_centralizer_le_and_equiv
    (hC27 : ASC27Statement G)
    (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hC24b : ASC24TwoChar G) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ fsuM T L) {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5)
    (eK : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
      (fsuV T I : Set G))))) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2))) :
    K ⊓ Subgroup.centralizer ((omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
        (fsuV T I : Set G))) : Subgroup G) : Set G) ≤ pCoreOf 2 K ∧
      Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set V' := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hV'
  have hQN := C.Q_le_normalizer h443 hC24a hC24b hF hK hKq hKM
  have hK2 : CharTwo K := CFSG.Quasithin.A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hF
  obtain ⟨⟨h1a, h1b, -⟩, -, -⟩ := hC27 H _ _ K _ C.hypC23 hK hKq hK2
    (fun h => hKM (h.trans inf_le_left)) hQN rfl
  have hKV : K ≤ Subgroup.normalizer (V' : Set G) := le_normalizer_omegaOneCenterOf_sup K Q
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ Q) := by
    have hKn : (K.subgroupOf (K ⊔ Q)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le (Subgroup.le_normalizer) hQN)
    exact CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2
      (CFSG.Quasithin.A4.subnormal_of_normal le_sup_left hKn)
  have hO : pCoreOf 2 K ≤ Subgroup.centralizer (V' : Set G) := fun x hx => (h1a (hOK hx)).2
  have hZ : ∀ c ∈ K ⊓ Subgroup.centralizer (V' : Set G), ∀ k ∈ K, ⁅c, k⁆ ∈ pCoreOf 2 K :=
    fun c hc k hk => by
      have h1 := commutator_mem_of_mem_oTwoZIn (inf_centralizer_le_oTwoZIn_of_c27 h1b hc) hk
      have e1 : ⁅c, k⁆ = (k * c * k⁻¹ * c⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e1]
      exact (pCoreOf 2 K).inv_mem h1
  exact quot_equiv_of_autOn hKV hKq.1 hm eK hO hZ

theorem eq_oPrimeResidualOf_of_sl (hA : A318Facts)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {m : ℕ} (hm : m = 4 ∨ m = 5)
    (eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2))) :
    K = oPrimeResidualOf 3 H := by
  have hP : IsPSL m 2 1 ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) :=
    SLMult.isPSL_of_statedSL_two (m := m) (by omega) (MulEquiv.refl _)
  have hX : A318Exclusion ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) := by
    rcases hm with rfl | rfl
    · exact a318Exclusion_psl42 l34NotL42Fact1515e_of_cert hP
    · exact a318Exclusion_psl52 hP
  exact eq_oPrimeResidualOf_three_of_exclusion hA h36 h38 C.hypC23.sqtk hK hKq eX hX

theorem excL45_of_c27L45
    (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hC24b : ASC24TwoChar G)
    (hA : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hF : CharTwo H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L)
    (h45 : C27L45 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))))) :
    ExcL45 T L I θ Vp H K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := C.conf.hc
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTpdef
  set L₀ := oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) with hL₀def
  set V' := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hV'def
  set Ks := autOn K V' with hKsdef
  obtain ⟨m, hm, ⟨eK⟩⟩ : ∃ m : ℕ, (m = 4 ∨ m = 5) ∧
      Nonempty (↥Ks ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2))) := by
    rcases h45.1 with h | h
    · exact ⟨4, Or.inl rfl, h⟩
    · exact ⟨5, Or.inr rfl, h⟩
  obtain ⟨hCK, ⟨eX⟩⟩ := C.inf_centralizer_le_and_equiv hC27 h443 hC24a hC24b hF hK hKq hKM
    (Or.inr hm) eK
  have hKeq := C.eq_oPrimeResidualOf_of_sl hA h36 h38 hK hKq hm eX
  have hL₀K : L₀ ≤ K := hKeq ▸ C.oTwoUpper_le_oPrimeResidualOf
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := hKeq ▸ le_normalizer_oPrimeResidualOf_three H
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTpH : Tp ≤ H := C.conf.tp_le_H
  have hTpK : Tp ≤ Subgroup.normalizer (K : Set G) := hTpH.trans hHK
  have hTpM : Tp ≤ fsuM T L := inf_le_left.trans S.T_le_fsuM
  have hH : K ⊔ Tp = H := C.min _ (sup_le (hL₀K.trans le_sup_left) le_sup_right)
    (sup_le hKH hTpH) (fun h => hKM (le_sup_left.trans h))
  have hKV : K ≤ Subgroup.normalizer (V' : Set G) := le_normalizer_omegaOneCenterOf_sup K Q
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef, ← S.hQ]
    exact le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hTpV : Tp ≤ Subgroup.normalizer (V' : Set G) :=
    ((le_normalizer_sup_of hTpK (inf_le_left.trans hTQ)).trans
      (normalizer_le_normalizer_pCoreOf (r := 2) (K ⊔ Q))).trans
        (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hθL₀ : θ ∈ L₀ := S.th_mem_oTwoUpper hc C.conf.vp_le
  have hθK : θ ∈ K := hL₀K hθL₀
  have hθN : θ ∈ Subgroup.normalizer (V' : Set G) := hKV hθK
  have hodd1 : ∀ z : G, Odd (orderOf z) → ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
    intro z hz k hk
    have h2 : orderOf z ∣ Nat.gcd (2 ^ k) (orderOf z) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) dvd_rfl
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hz)),
      Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact h2
  have hθ3 : θ ^ 3 = 1 := by
    have h1 : θ ^ 3 ∈ pCoreOf 2 L :=
      inf_centralizer_L_le hc ⟨L.pow_mem hc.mem 3, th_pow_three_mem hc⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, h1⟩
    exact hodd1 _ (Odd.of_dvd_nat hc.odd (orderOf_pow_dvd 3)) k
      (by simpa using congrArg Subtype.val hk)
  have hθV' : θ ∉ Subgroup.centralizer (V' : Set G) := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨θ, hCK ⟨hθK, h⟩⟩
    have hk' : θ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : θ ^ Nat.gcd 3 (2 ^ k) = 1 := (pow_gcd_eq_one).2 ⟨hθ3, hk'⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at h1
    exact th_not_mem hc (h1 ▸ Subgroup.one_mem _)
  have hKn : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
  have hTpKs : IsSylowTwoOf (Tp ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal C.conf.sylH hKH
      hKn.isSubnormal
  have hSs : IsSylowTwoOf (autOn (Tp ⊓ K) V') Ks :=
    CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hTpKs hKV
  obtain ⟨θc, hθc⟩ := exists_coord_sylow (by omega)
    (eK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m (ZMod 2)).symm)
    (isSylowTwoOf_subgroupOf_top hSs)
  have hMHK : fsuM T L ⊓ H ⊓ K = fsuM T L ⊓ K := by rw [inf_assoc, inf_eq_right.2 hKH]
  set Ms := autOn (fsuM T L ⊓ H ⊓ K) V' with hMsdef
  have hMsKs : Ms ≤ Ks := CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le inf_le_right
  have hSMs : autOn (Tp ⊓ K) V' ≤ Ms := CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le
    (le_inf (le_inf (inf_le_left.trans hTpM) (inf_le_left.trans hTpH)) inf_le_right)
  have hNS : Ks ⊓ Subgroup.normalizer ((autOn (Tp ⊓ K) V' : Subgroup _) :
      Set (MulAut ↥V')) ≤ Ms := by
    obtain ⟨-, S₀, hS₀, hN₀⟩ := h45.2.1
    have hS₀Ms : S₀ ≤ Ms := fun x hx => hN₀ ⟨hS₀.1 hx, Subgroup.le_normalizer hx⟩
    obtain ⟨p, hp, hpS⟩ := (CFSG.QuasithinUnique.Lin2.isSylowTwoOf_of_le_of_le hS₀ hS₀Ms
      hMsKs).exists_conj (CFSG.QuasithinUnique.Lin2.isSylowTwoOf_of_le_of_le hSs hSMs hMsKs)
    rintro x ⟨hxK, hxN⟩
    have hpK : p ∈ Ks := hMsKs hp
    have h1 : p⁻¹ * x * p ∈ Ks ⊓ Subgroup.normalizer (S₀ : Set (MulAut ↥V')) := by
      refine ⟨Ks.mul_mem (Ks.mul_mem (Ks.inv_mem hpK) hxK) hpK,
        Subgroup.mem_normalizer_iff.2 fun z => ?_⟩
      have hz : ∀ w, w ∈ S₀ ↔ p * w * p⁻¹ ∈ autOn (Tp ⊓ K) V' := fun w => by
        rw [hpS]
        constructor
        · intro hw
          exact ⟨w, hw, rfl⟩
        · rintro ⟨w', hw', e⟩
          have : w' = w := by
            have e' := congrArg (fun u => p⁻¹ * u * p) e
            simpa [mul_assoc] using e'
          exact this ▸ hw'
      rw [hz z, hz (p⁻¹ * x * p * z * (p⁻¹ * x * p)⁻¹)]
      have e : p * (p⁻¹ * x * p * z * (p⁻¹ * x * p)⁻¹) * p⁻¹ =
          x * (p * z * p⁻¹) * x⁻¹ := by group
      rw [e]
      exact Subgroup.mem_normalizer_iff.1 hxN _
    have h2 := hN₀ h1
    have e : x = p * (p⁻¹ * x * p) * p⁻¹ := by group
    rw [e]
    exact Ms.mul_mem (Ms.mul_mem hp h2) (Ms.inv_mem hp)
  set P'' := (Ms.subgroupOf Ks).map θc.toMonoidHom with hP''def
  have hBP : upperTriangular m (ZMod 2) ≤ P'' := by
    rw [← normalizer_unitriangular, ← hθc,
      ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.subgroupOf_normalizer_eq hSs.1]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hNS ⟨z.2, hz⟩, rfl⟩
  set Icut := borelOvergroupCuts P'' with hIdef
  have hPI : P'' = flagStabilizer m (ZMod 2) Icut :=
    (borel_overgroups P'' hBP).1
  have hIcut : ∀ i ∈ Icut, 1 ≤ i ∧ i < m := fun i ⟨hi, hin, _⟩ => ⟨hi, hin⟩
  have hcent : ∀ x : ↥K, CFSG.QuasithinUnique.Setup.rho V' K hKV x = 1 →
      (x : G) ∈ fsuM T L := fun x hx =>
    C.pCoreOf_le_fsuM hK (hCK ⟨x.2, (CFSG.QuasithinUnique.Setup.rho_eq_one_iff hKV x).1 hx⟩)
  have hle_of : ∀ x : ↥K, CFSG.QuasithinUnique.Setup.rho V' K hKV x ∈ Ms → (x : G) ∈ fsuM T L := by
    intro x hx
    obtain ⟨g, hgM, hgx⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.1 hx
    have hgK : (g : G) ∈ K := hgM.2
    have h1 : CFSG.QuasithinUnique.Setup.rho V' K hKV (⟨g, hgK⟩⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, ← hgx]
      exact inv_mul_cancel _
    have h2 := hcent _ h1
    have e : (x : G) = g * ((⟨g, hgK⟩⁻¹ * x : ↥K) : G) := by simp
    rw [e]
    exact (fsuM T L).mul_mem hgM.1.1 h2
  have hIne : Icut.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, flagStabilizer_empty] at hPI
    apply hKM
    intro x hx
    have hmem : (⟨CFSG.QuasithinUnique.Setup.rho V' K hKV ⟨x, hx⟩,
        (CFSG.QuasithinUnique.Setup.mem_autOn_self_iff hKV).2 ⟨⟨x, hx⟩, rfl⟩⟩ : ↥Ks) ∈
          Ms.subgroupOf Ks := by
      have h1 : θc ⟨_, (CFSG.QuasithinUnique.Setup.mem_autOn_self_iff hKV).2 ⟨⟨x, hx⟩, rfl⟩⟩ ∈
          P'' := hPI ▸ Subgroup.mem_top _
      obtain ⟨z, hz, hzx⟩ := h1
      rwa [θc.injective hzx] at hz
    exact hle_of ⟨x, hx⟩ hmem
  have hNL₀ : ∀ g ∈ fsuM T L, g ∈ Subgroup.centralizer (Vp : Set G) →
      g ∈ Subgroup.normalizer (L₀ : Set G) := by
    intro g hgM hgV
    have hgN : g ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (Vp : Set G) : Subgroup G) :
        Set G) := Subgroup.inf_normalizer_le_normalizer_inf
      ⟨by rw [← S.fsuM_eq]; exact hgM, Subgroup.le_normalizer hgV⟩
    refine Subgroup.mem_normalizer_iff.2 fun z =>
      ⟨fun hz => CFSG.Quasithin.conj_mem_oTwoUpper hgN hz, fun hz => ?_⟩
    have := CFSG.Quasithin.conj_mem_oTwoUpper (Subgroup.inv_mem _ hgN) hz
    simpa [mul_assoc] using this
  set L₀V := L₀ ⊓ Subgroup.centralizer (fsuV T I : Set G) with hL₀Vdef
  have hNL₀V : ∀ g ∈ fsuM T L, g ∈ Subgroup.centralizer (Vp : Set G) →
      g ∈ Subgroup.normalizer (L₀V : Set G) := fun g hgM hgV =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hNL₀ g hgM hgV, mem_normalizer_centralizer (S.hMN hgM)⟩
  have hHVp : H ≤ Subgroup.centralizer (Vp : Set G) := C.conf.hHG
  have hML₀ : fsuM T L ⊓ H ⊓ K ≤ Subgroup.normalizer (L₀ : Set G) := fun g hg =>
    hNL₀ g hg.1.1 (hHVp hg.1.2)
  have hML₀V : fsuM T L ⊓ H ⊓ K ≤ Subgroup.normalizer (L₀V : Set G) := fun g hg =>
    hNL₀V g hg.1.1 (hHVp hg.1.2)
  have hL₀M : L₀ ≤ fsuM T L ⊓ H ⊓ K :=
    le_inf (le_inf ((oTwoUpper_le _).trans (inf_le_left.trans S.L_le_fsuM))
      (le_sup_left.trans C.conf.hLH)) hL₀K
  set X := ((autOn L₀ V').subgroupOf Ks).map θc.toMonoidHom with hXdef
  set Y := ((autOn L₀V V').subgroupOf Ks).map θc.toMonoidHom with hYdef
  have hθs : CFSG.QuasithinUnique.Setup.rho V' K hKV ⟨θ, hθK⟩ ∈ Ks :=
    (CFSG.QuasithinUnique.Setup.mem_autOn_self_iff hKV).2 ⟨_, rfl⟩
  set y := θc ⟨_, hθs⟩ with hydef
  have hρθ1 : CFSG.QuasithinUnique.Setup.rho V' K hKV ⟨θ, hθK⟩ ≠ 1 := fun h =>
    hθV' ((CFSG.QuasithinUnique.Setup.rho_eq_one_iff hKV _).1 h)
  have hcfg : LPar.Cfg m Icut X Y y := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hPI]
      exact Subgroup.map_mono fun z hz =>
        CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le hL₀M hz
    · rw [← hPI]
      exact map_autOn_le_normalizer θc hML₀
    · exact Subgroup.map_mono fun z hz =>
        CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le inf_le_left hz
    · rw [← hPI]
      exact map_autOn_le_normalizer θc hML₀V
    · have h1 : IsPGroup 2 ↥L₀V := (pCoreOf_isPGroup 2 L).to_le fun x hx =>
        inf_centralizer_L_le hc ⟨(oTwoUpper_le _ hx.1).1, hx.2⟩
      have h2 : IsPGroup 2 ↥(autOn L₀V V') := (h1.comap_subtype).map _
      exact (h2.comap_subtype).map _
    · exact ⟨⟨_, hθs⟩, (CFSG.QuasithinUnique.Setup.mem_autOn_iff).2 ⟨_, hθL₀, rfl⟩, rfl⟩
    · have h3 : y ^ 3 = 1 := by
        rw [hydef, ← map_pow]
        have : (⟨_, hθs⟩ : ↥Ks) ^ 3 = 1 := Subtype.ext (by
          simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
          rw [← map_pow]
          have e : (⟨θ, hθK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hθ3)
          rw [e, map_one])
        rw [this, map_one]
      have h1 : y ≠ 1 := fun h => hρθ1 (by
        have := congrArg Subtype.val (θc.injective (h.trans (map_one θc).symm))
        simpa using this)
      exact orderOf_eq_prime h3 h1
    · rintro _ ⟨⟨a, haKs⟩, ha, rfl⟩
      obtain ⟨g, hgL₀, rfl⟩ := (CFSG.QuasithinUnique.Setup.mem_autOn_iff).1 ha
      have hθN0 : Subgroup.zpowers θ ≤ Subgroup.normalizer (L₀V : Set G) :=
        (Subgroup.zpowers_le).2 (hNL₀V θ (S.L_le_fsuM hc.mem)
          (Subgroup.mem_centralizer_iff.2 fun v hv => by
            rw [C.hVp] at hv
            exact (Subgroup.mem_centralizer_singleton_iff.mp hv.2)))
      have h1 : (g : G) ∈ ((L₀V ⊔ Subgroup.zpowers θ : Subgroup G) : Set G) :=
        C.oTwoUpper_le_sup hgL₀
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L₀V _ hθN0] at h1
      obtain ⟨u, hu, z, hz, huz⟩ := h1
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have huN : u ∈ Subgroup.normalizer (V' : Set G) := hKV (hL₀K hu.1)
      have huKs : conjAct V' ⟨u, huN⟩ ∈ Ks :=
        (CFSG.QuasithinUnique.Setup.mem_autOn_iff).2 ⟨_, hL₀K hu.1, rfl⟩
      have e : (⟨conjAct V' g, haKs⟩ : ↥Ks) = ⟨conjAct V' ⟨u, huN⟩, huKs⟩ * ⟨_, hθs⟩ ^ j := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
        rw [show (CFSG.QuasithinUnique.Setup.rho V' K hKV ⟨θ, hθK⟩ : MulAut ↥V') =
          conjAct V' ⟨θ, hθN⟩ from rfl, ← map_zpow, ← map_mul]
        congr 1
        exact Subtype.ext huz.symm
      rw [MulEquiv.coe_toMonoidHom, e, map_mul, map_zpow]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨⟨_, huKs⟩,
          (CFSG.QuasithinUnique.Setup.mem_autOn_iff).2 ⟨_, hu, rfl⟩, rfl⟩)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
  have hcK : ∀ t : ↥Tp, ∀ a ∈ Ks,
      conjAct V' ⟨t, hTpV t.2⟩ * a * (conjAct V' ⟨t, hTpV t.2⟩)⁻¹ ∈ Ks :=
    fun t a ha => conj_mem_autOn (hTpV t.2) (hTpK t.2) ha
  have hinv : ∀ t : ↥Tp, conjAct V' ⟨(t : G)⁻¹, Subgroup.inv_mem _ (hTpV t.2)⟩ =
      (conjAct V' ⟨t, hTpV t.2⟩)⁻¹ := fun t => by
    rw [← map_inv]
    rfl
  have hcK' : ∀ t : ↥Tp, ∀ a ∈ Ks,
      (conjAct V' ⟨t, hTpV t.2⟩)⁻¹ * a * (conjAct V' ⟨t, hTpV t.2⟩)⁻¹⁻¹ ∈ Ks := fun t a ha => by
    have h1 := conj_mem_autOn (Subgroup.inv_mem _ (hTpV t.2)) (Subgroup.inv_mem _ (hTpK t.2)) ha
    rwa [hinv t] at h1
  let ct : ↥Tp → (↥Ks ≃* ↥Ks) := fun t =>
    { toFun := fun a => ⟨_, hcK t a a.2⟩
      invFun := fun a => ⟨_, hcK' t a a.2⟩
      left_inv := fun a => Subtype.ext (by simp only [inv_inv]; group)
      right_inv := fun a => Subtype.ext (by simp only [inv_inv]; group)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hct : ∀ t : ↥Tp, ∀ a : ↥Ks, ((ct t a : ↥Ks) : MulAut ↥V') =
      conjAct V' ⟨t, hTpV t.2⟩ * a * (conjAct V' ⟨t, hTpV t.2⟩)⁻¹ := fun t a => rfl
  have hctZ : ∀ (t : ↥Tp) (Z : Subgroup G), (t : G) ∈ Subgroup.normalizer (Z : Set G) →
      ((autOn Z V').subgroupOf Ks).map (ct t).toMonoidHom = (autOn Z V').subgroupOf Ks := by
    intro t Z htZ
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact conj_mem_autOn (hTpV t.2) htZ ha
    · intro hb
      refine ⟨(ct t).symm b, ?_, (ct t).apply_symm_apply b⟩
      have h1 := conj_mem_autOn (Subgroup.inv_mem _ (hTpV t.2)) (Subgroup.inv_mem _ htZ) hb
      rw [hinv t] at h1
      exact h1
  let α : ↥Tp → MulAut (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := fun t =>
    θc.symm.trans ((ct t).trans θc)
  have hαφ : ∀ (t : ↥Tp) (k : ↥K) (hk : (t : G) * k * (t : G)⁻¹ ∈ K),
      α t (θc ⟨CFSG.QuasithinUnique.Setup.rho V' K hKV k,
        (CFSG.QuasithinUnique.Setup.mem_autOn_self_iff hKV).2 ⟨k, rfl⟩⟩) =
      θc ⟨CFSG.QuasithinUnique.Setup.rho V' K hKV ⟨_, hk⟩,
        (CFSG.QuasithinUnique.Setup.mem_autOn_self_iff hKV).2 ⟨_, rfl⟩⟩ := by
    intro t k hk
    show θc (ct t (θc.symm (θc _))) = _
    rw [MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [hct]
    show conjAct V' ⟨t, hTpV t.2⟩ * conjAct V' ⟨k, hKV k.2⟩ * (conjAct V' ⟨t, hTpV t.2⟩)⁻¹ =
      conjAct V' ⟨_, hKV hk⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  set A : Set (MulAut (Matrix.SpecialLinearGroup (Fin m) (ZMod 2))) := Set.range α with hAdef
  have htTp : ∀ t : ↥Tp, (t : G) ∈ fsuM T L ∧ (t : G) ∈ Subgroup.centralizer (Vp : Set G) ∧
      (t : G) ∈ H := fun t => ⟨hTpM t.2, t.2.2, hTpH t.2⟩
  have hAB : ∀ β ∈ A, (upperTriangular m
      (ZMod 2)).map β.toMonoidHom =
        upperTriangular m (ZMod 2) := by
    rintro _ ⟨t, rfl⟩
    rw [LFlag.upperTriangular_eq_unitriangular,
      ← hθc]
    refine map_trans_eq θc (ct t) (hctZ t _ ?_)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer t.2, hTpK t.2⟩
  have hAQ : ∀ β ∈ A, (flagStabilizer m (ZMod 2)
      Icut).map β.toMonoidHom =
        flagStabilizer m (ZMod 2) Icut := by
    rintro _ ⟨t, rfl⟩
    rw [← hPI]
    refine map_trans_eq θc (ct t) (hctZ t _ ?_)
    obtain ⟨htM, -, htH⟩ := htTp t
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer htM,
        Subgroup.le_normalizer htH⟩, hTpK t.2⟩
  have hAX : ∀ β ∈ A, X.map β.toMonoidHom = X := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨htM, htV, -⟩ := htTp t
    exact map_trans_eq θc (ct t) (hctZ t _ (hNL₀ _ htM htV))
  rcases LPar.slParabolicThreeFact_holds m hm Icut hIcut hIne X Y y hcfg.hXQ hcfg.hQX hcfg.hYX
      hcfg.hQY hcfg.hY2 hcfg.hy hcfg.hy3 hcfg.hXy A hAB hAQ hAX with
    ⟨R, hBR, hRtop, hXR, hRQ, hRA⟩ | ⟨h4, hI13, -⟩
  ·
    exfalso
    let ρ' : ↥K →* ↥Ks := (CFSG.QuasithinUnique.Setup.rho V' K hKV).codRestrict Ks
      fun k => (CFSG.QuasithinUnique.Setup.mem_autOn_self_iff hKV).2 ⟨k, rfl⟩
    let φ : ↥K →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) := θc.toMonoidHom.comp ρ'
    have hφ : ∀ k : ↥K, φ k = θc ⟨CFSG.QuasithinUnique.Setup.rho V' K hKV k,
        (CFSG.QuasithinUnique.Setup.mem_autOn_self_iff hKV).2 ⟨k, rfl⟩⟩ := fun k => rfl
    have hφs : Function.Surjective φ := by
      intro r
      obtain ⟨⟨a, ha⟩, rfl⟩ := θc.surjective r
      obtain ⟨k, rfl⟩ := (CFSG.QuasithinUnique.Setup.mem_autOn_self_iff hKV).1 ha
      exact ⟨k, rfl⟩
    have hφM : ∀ k : ↥K, (k : G) ∈ fsuM T L → φ k ∈
        flagStabilizer m (ZMod 2) Icut := by
      intro k hk
      rw [← hPI]
      exact ⟨_, (CFSG.QuasithinUnique.Setup.mem_autOn_iff).2
        ⟨_, ⟨⟨hk, hKH k.2⟩, k.2⟩, rfl⟩, rfl⟩
    set K₁ := (R.comap φ).map K.subtype with hK₁def
    have hmemK₁ : ∀ k : ↥K, (k : G) ∈ K₁ ↔ φ k ∈ R := fun k => by
      rw [hK₁def, Subgroup.mem_map]
      constructor
      · rintro ⟨k', hk', e⟩
        rw [Subtype.ext e] at hk'
        exact hk'
      · intro h
        exact ⟨k, h, rfl⟩
    have hK₁K : K₁ ≤ K := fun x ⟨k, _, e⟩ => e ▸ k.2
    have hL₀K₁ : L₀ ≤ K₁ := fun x hx => (hmemK₁ ⟨x, hL₀K hx⟩).2 (hXR ⟨_,
      (CFSG.QuasithinUnique.Setup.mem_autOn_iff).2 ⟨_, hx, rfl⟩, rfl⟩)
    have hTpK₁ : Tp ⊓ K ≤ K₁ := fun x hx => (hmemK₁ ⟨x, hx.2⟩).2 (hBR (by
      rw [LFlag.upperTriangular_eq_unitriangular,
        ← hθc]
      exact ⟨_, (CFSG.QuasithinUnique.Setup.mem_autOn_iff).2 ⟨_, hx, rfl⟩, rfl⟩))
    have hTpN : Tp ≤ Subgroup.normalizer (K₁ : Set G) := by
      intro t ht
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have hxK := hK₁K hx
      have hk : t * x * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hTpK ht) x).1 hxK
      refine (hmemK₁ ⟨_, hk⟩).2 ?_
      rw [hφ, ← hαφ ⟨t, ht⟩ ⟨x, hxK⟩ hk, ← hφ]
      have h1 : φ ⟨x, hxK⟩ ∈ R := (hmemK₁ ⟨x, hxK⟩).1 hx
      have h2 : α ⟨t, ht⟩ (φ ⟨x, hxK⟩) ∈ R.map (α ⟨t, ht⟩).toMonoidHom := ⟨_, h1, rfl⟩
      rwa [hRA _ ⟨⟨t, ht⟩, rfl⟩] at h2
    have hH₁ : K₁ ⊔ Tp = H := by
      refine C.min _ (sup_le (hL₀K₁.trans le_sup_left) le_sup_right)
        (sup_le (hK₁K.trans hKH) hTpH) fun hle => hRQ fun r hr => ?_
      obtain ⟨k, rfl⟩ := hφs r
      exact hφM k (hle (Subgroup.mem_sup_left ((hmemK₁ k).2 hr)))
    apply hRtop
    rw [eq_top_iff]
    intro r _
    obtain ⟨k, rfl⟩ := hφs r
    have hk : (k : G) ∈ ((K₁ ⊔ Tp : Subgroup G) : Set G) := hH₁ ▸ hKH k.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K₁ Tp hTpN] at hk
    obtain ⟨k₁, hk₁, t, ht, e⟩ := hk
    have htK : t ∈ K := by
      have e' : t = k₁⁻¹ * k := by rw [← e]; group
      rw [e']
      exact K.mul_mem (K.inv_mem (hK₁K hk₁)) k.2
    have hkK₁ : (k : G) ∈ K₁ := by
      rw [← e]
      exact K₁.mul_mem hk₁ (hTpK₁ ⟨ht, htK⟩)
    exact (hmemK₁ k).1 hkK₁
  · subst h4
    refine ⟨θc, ?_, ⟨y, hθN, ?_, ?_⟩, hH⟩
    · rw [← hMHK, ← hI13]
      exact hPI
    · rw [← hI13]
      exact hcfg
    · rw [hydef, MulEquiv.symm_apply_apply]
      rfl


end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
