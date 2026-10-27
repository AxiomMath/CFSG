module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Assembly
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Z2Central

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.CGT.Timmesfeld75
open CFSG.LieType.BorelTits
open scoped commutatorElement MatrixGroups

theorem str83G4_z1_eq_inf_centralizer
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {V : Subgroup G} (hV : Str83G4V L1 L2 S V a) :
    Z1 L1 L2 S = V ⊓ Subgroup.centralizer (S : Set G) := by
  classical
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨hVZ, hcentral, hnat⟩ := hV
  obtain ⟨hstep, hVH, hVea, hdata⟩ := hnat
  obtain ⟨e, ρ0, φ, hcompat, hφnat⟩ := hdata
  obtain ⟨-, -, hZ2bot, -, hZ2CSeq⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hcore : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hsylow : IsSylowTwoOf S (L2 ⊔ S) := by
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    have hQ : Q1 L2 L1 S = Q2 L1 L2 S := by simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hQ, show L2 ⊔ Q2 L1 L2 S = L2 ⊔ S from hsup2.symm] at h
    exact h
  have hHW : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hVN : L2 ⊔ S ≤ Subgroup.normalizer (V : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hZ2ea : IsElemAbelian 2 (Z2 L1 L2 S) := isElemAbelian_z2
  have hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ (Z2 L1 L2 S)) :=
    isElemAbelian_chiefMod_bot hZ2ea
  letI : CommGroup (Ch3z.chiefMod ⊥ (Z2 L1 L2 S)) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ (Z2 L1 L2 S))) := l2ChiefSectionModule hE
  let hEV := CFSG.Quasithin.isElemAbelian_chiefMod hstep hVH hVea.isPGroup
  letI : CommGroup (Ch3z.chiefMod ⊥ V) := l2ChiefSectionCommGroup hEV
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ V)) := l2ChiefSectionModule hEV
  have hO : pCoreOf 2 (L2 ⊔ S) ≤
      centralizerMod (⊥ : Subgroup G) (L2 ⊔ S) (Z2 L1 L2 S) := by
    intro x hx
    have hxQ : x ∈ Q2 L1 L2 S := hcore ▸ hx
    refine ⟨CFSG.openPCoreOf_le 2 (L2 ⊔ S) hx, ?_, ?_⟩
    · rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top x
    · intro u hu
      have hxu : u * x = x * u := (Subgroup.mem_centralizer_iff.mp (hQ2C hxQ)) u hu
      have h1 : x * u * x⁻¹ * u⁻¹ = 1 := by
        rw [show x * u * x⁻¹ * u⁻¹ = (x * u) * (u * x)⁻¹ by group, hxu, mul_inv_cancel]
      rw [h1]
      exact Subgroup.one_mem ⊥
  let ρW := sectionRep (D14.le_normalizer_bot (L2 ⊔ S)) hHW
    (D14.le_normalizer_bot (Z2 L1 L2 S)) hE hO e
  have hcommV : ∀ x ∈ L2 ⊔ S, ∀ z ∈ Z2 L1 L2 S, x * z * x⁻¹ * z⁻¹ ∈ V :=
    fun x hx z hz => hcentral x hx z hz
  have mem_subZ_general : ∀ x : Additive (Ch3z.chiefMod ⊥ (Z2 L1 L2 S)),
      x ∈ subZ (W := Z2 L1 L2 S) hE V →
      (((chiefModBotMulEquiv (Z2 L1 L2 S)).symm x.toMul : ↥(Z2 L1 L2 S)) : G) ∈ V := by
    intro x hx
    set w : ↥(Z2 L1 L2 S) := (chiefModBotMulEquiv (Z2 L1 L2 S)).symm x.toMul with hw
    have hxw : Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) w) = x := by
      apply Additive.ext
      rw [show (Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) w)).toMul =
        chiefModBotMulEquiv (Z2 L1 L2 S) w from rfl, hw, MulEquiv.apply_symm_apply]
    have hmem : Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) w) ∈
        subZ (W := Z2 L1 L2 S) hE V := by
      rw [hxw]
      exact hx
    exact mem_subZ_iff.mp hmem
  let ιfun : Additive (Ch3z.chiefMod ⊥ V) → Additive (Ch3z.chiefMod ⊥ (Z2 L1 L2 S)) :=
    fun y => Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S)
      ⟨((chiefModBotMulEquiv V).symm y.toMul : ↥V).1,
        hVZ ((chiefModBotMulEquiv V).symm y.toMul).2⟩)
  have ιfun_eq : ∀ y : Additive (Ch3z.chiefMod ⊥ V), ιfun y =
      Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S)
        ⟨((chiefModBotMulEquiv V).symm y.toMul : ↥V).1,
          hVZ ((chiefModBotMulEquiv V).symm y.toMul).2⟩) := fun y => rfl
  have hι_apply : ∀ w : ↥V, ιfun (Additive.ofMul (chiefModBotMulEquiv V w)) =
      Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) ⟨(w : G), hVZ w.2⟩) := by
    intro w
    rw [ιfun_eq]
    apply congrArg Additive.ofMul
    apply congrArg (chiefModBotMulEquiv (Z2 L1 L2 S))
    apply Subtype.ext
    show ((chiefModBotMulEquiv V).symm ((chiefModBotMulEquiv V) w)).1 = (w : G)
    rw [MulEquiv.symm_apply_apply]
  have hι_add : ∀ y y' : Additive (Ch3z.chiefMod ⊥ V), ιfun (y + y') = ιfun y + ιfun y' := by
    intro y y'
    rw [ιfun_eq, ιfun_eq, ιfun_eq]
    rw [show (y + y').toMul = y.toMul * y'.toMul from rfl]
    rw [← ofMul_mul]
    have hmul : chiefModBotMulEquiv (Z2 L1 L2 S)
          ⟨((chiefModBotMulEquiv V).symm y.toMul : ↥V).1,
            hVZ ((chiefModBotMulEquiv V).symm y.toMul).2⟩ *
        chiefModBotMulEquiv (Z2 L1 L2 S)
          ⟨((chiefModBotMulEquiv V).symm y'.toMul : ↥V).1,
            hVZ ((chiefModBotMulEquiv V).symm y'.toMul).2⟩ =
        chiefModBotMulEquiv (Z2 L1 L2 S)
          (⟨((chiefModBotMulEquiv V).symm y.toMul : ↥V).1,
              hVZ ((chiefModBotMulEquiv V).symm y.toMul).2⟩ *
            ⟨((chiefModBotMulEquiv V).symm y'.toMul : ↥V).1,
              hVZ ((chiefModBotMulEquiv V).symm y'.toMul).2⟩) :=
      (map_mul (chiefModBotMulEquiv (Z2 L1 L2 S)) _ _).symm
    rw [hmul]
    apply congrArg Additive.ofMul
    apply congrArg (chiefModBotMulEquiv (Z2 L1 L2 S))
    apply Subtype.ext
    show ((chiefModBotMulEquiv V).symm (y.toMul * y'.toMul) : ↥V).1 =
      ((chiefModBotMulEquiv V).symm y.toMul : ↥V).1 *
        ((chiefModBotMulEquiv V).symm y'.toMul : ↥V).1
    rw [map_mul]
    rfl
  have hι_zero : ιfun 0 = 0 := by
    have hV1 : ((chiefModBotMulEquiv V).symm (1 : Ch3z.chiefMod ⊥ V) : ↥V) = 1 :=
      map_one (chiefModBotMulEquiv V).symm
    have h0 : (Additive.toMul (0 : Additive (Ch3z.chiefMod ⊥ V))) = 1 := rfl
    rw [ιfun_eq, h0, hV1]
    have hone : (⟨((1 : ↥V) : G), hVZ (1 : ↥V).2⟩ : ↥(Z2 L1 L2 S)) = 1 := Subtype.ext rfl
    rw [hone, map_one, ofMul_one]
  let ι : Additive (Ch3z.chiefMod ⊥ V) →ₗ[ZMod 2]
      Additive (Ch3z.chiefMod ⊥ (Z2 L1 L2 S)) :=
    { toFun := ιfun
      map_add' := hι_add
      map_smul' := by
        intro c y
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · simp only [RingHom.id_apply, zero_smul]
          exact hι_zero
        · simp only [RingHom.id_apply, one_smul] }
  have hι_coe : ∀ y, ι y = ιfun y := fun y => rfl
  have hιinj : Function.Injective ι := by
    intro y y' h
    rw [hι_coe, hι_coe] at h
    set v : ↥V := (chiefModBotMulEquiv V).symm y.toMul with hv
    set v' : ↥V := (chiefModBotMulEquiv V).symm y'.toMul with hv'
    have hy : Additive.ofMul (chiefModBotMulEquiv V v) = y := by
      apply Additive.ext
      rw [show (Additive.ofMul (chiefModBotMulEquiv V v)).toMul =
        chiefModBotMulEquiv V v from rfl, hv, MulEquiv.apply_symm_apply]
    have hy' : Additive.ofMul (chiefModBotMulEquiv V v') = y' := by
      apply Additive.ext
      rw [show (Additive.ofMul (chiefModBotMulEquiv V v')).toMul =
        chiefModBotMulEquiv V v' from rfl, hv', MulEquiv.apply_symm_apply]
    have hh : ιfun (Additive.ofMul (chiefModBotMulEquiv V v)) =
        ιfun (Additive.ofMul (chiefModBotMulEquiv V v')) := by
      rw [← hy, ← hy'] at h
      exact h
    rw [hι_apply v, hι_apply v'] at hh
    have h4 := congrArg Additive.toMul hh
    simp only [toMul_ofMul] at h4
    have h3 : (⟨(v : G), hVZ v.2⟩ : ↥(Z2 L1 L2 S)) = ⟨(v' : G), hVZ v'.2⟩ :=
      (MulEquiv.injective (chiefModBotMulEquiv (Z2 L1 L2 S))) h4
    have h5 : v = v' :=
      Subtype.ext (congrArg (fun z : ↥(Z2 L1 L2 S) => (z : G)) h3)
    rw [← hy, ← hy', h5]
  have hι : ∀ (g : SL(2, GaloisField 2 (2 * a + 1)))
      (y : Additive (Ch3z.chiefMod ⊥ V)), ρW g (ι y) = ι (ρ0 g y) := by
    intro g y
    rw [hι_coe, hι_coe]
    obtain ⟨g', rfl⟩ := e.surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥(L2 ⊔ S)) g'
    rw [QuotientGroup.mk'_apply]
    set v : ↥V := (chiefModBotMulEquiv V).symm y.toMul with hv
    have hy : Additive.ofMul (chiefModBotMulEquiv V v) = y := by
      apply Additive.ext
      rw [show (Additive.ofMul (chiefModBotMulEquiv V v)).toMul =
        chiefModBotMulEquiv V v from rfl, hv, MulEquiv.apply_symm_apply]
    have hconjW : (h : G) * (v : G) * (h : G)⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hHW h.2) (v : G)).mp (hVZ v.2)
    have hconjV : (h : G) * (v : G) * (h : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hVN h.2) (v : G)).mp v.2
    rw [← hy]
    have hL : ρW (e (QuotientGroup.mk h)) (ιfun (Additive.ofMul (chiefModBotMulEquiv V v))) =
        Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S)
          ⟨(h : G) * (v : G) * (h : G)⁻¹, hconjW⟩) := by
      rw [hι_apply v, sectionRep_apply, sectionAction_bot_apply]
    have hR : ιfun (ρ0 (e (QuotientGroup.mk h))
        (Additive.ofMul (chiefModBotMulEquiv V v))) =
        Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S)
          ⟨(h : G) * (v : G) * (h : G)⁻¹, hconjW⟩) := by
      rw [hcompat]
      rw [show l2ChiefSectionAction hstep hEV h (chiefModBotMulEquiv V v) =
          chiefModBotMulEquiv V ⟨(h : G) * (v : G) * (h : G)⁻¹, hconjV⟩ from
        chiefModBotMulEquiv_conj hstep hVH hEV h v]
      rw [hι_apply]
    rw [hL, hR]
  let Nsub : Subrepresentation ρW :=
    { toSubmodule := LinearMap.range ι
      apply_mem_toSubmodule := fun g x hx => by
        obtain ⟨y, rfl⟩ := hx
        exact ⟨ρ0 g y, (hι g y).symm⟩ }
  have hrange : LinearMap.range ι = subZ (W := Z2 L1 L2 S) hE V := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [hι_coe]
      set v : ↥V := (chiefModBotMulEquiv V).symm y.toMul with hv
      have hy : Additive.ofMul (chiefModBotMulEquiv V v) = y := by
        apply Additive.ext
        rw [show (Additive.ofMul (chiefModBotMulEquiv V v)).toMul =
          chiefModBotMulEquiv V v from rfl, hv, MulEquiv.apply_symm_apply]
      rw [← hy, hι_apply v]
      exact (mem_subZ_iff' (hVZ v.2)).mpr v.2
    · intro hx
      set w : ↥(Z2 L1 L2 S) := (chiefModBotMulEquiv (Z2 L1 L2 S)).symm x.toMul with hw
      have hxw : Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) w) = x := by
        apply Additive.ext
        rw [show (Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) w)).toMul =
          chiefModBotMulEquiv (Z2 L1 L2 S) w from rfl, hw, MulEquiv.apply_symm_apply]
      refine ⟨Additive.ofMul (chiefModBotMulEquiv V ⟨(w : G), mem_subZ_general x hx⟩), ?_⟩
      rw [hι_coe, hι_apply, hxw]
  have hNsub_sub : Nsub.toSubmodule = subZ (W := Z2 L1 L2 S) hE V := hrange
  have hQ : ∀ (g : SL(2, GaloisField 2 (2 * a + 1)))
      (m : Additive (Ch3z.chiefMod ⊥ (Z2 L1 L2 S))),
      ρW g m - m ∈ Nsub.toSubmodule := by
    intro g m
    have h1 : ρW g m - m ∈ subZ (W := Z2 L1 L2 S) hE V :=
      sectionRep_sub_mem_subZ hHW hO e hcommV g m
    rwa [hNsub_sub]
  have hCbot : Z2 L1 L2 S ⊓ Subgroup.centralizer ((L2 ⊔ S : Subgroup G) : Set G) = ⊥ := by
    rw [hsup2]
    exact hZ2bot
  have hcent : fixedSub ρW ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    set w : ↥(Z2 L1 L2 S) := (chiefModBotMulEquiv (Z2 L1 L2 S)).symm m.toMul with hw
    have hmw : Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) w) = m := by
      apply Additive.ext
      rw [show (Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) w)).toMul =
        chiefModBotMulEquiv (Z2 L1 L2 S) w from rfl, hw, MulEquiv.apply_symm_apply]
    rw [← hmw] at hm
    have htopmap : ((⊤ : Subgroup ↥(L2 ⊔ S)).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L2 ⊔ S)))).map e.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
        Subgroup.map_top_of_surjective _ e.surjective]
    have hsubtop : ((⊤ : Subgroup ↥(L2 ⊔ S)).map (L2 ⊔ S).subtype : Subgroup G) =
        L2 ⊔ S := by
      simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) (L2 ⊔ S)
    have hiff := mem_fixSub_sectionRep_bot_iff (D14.le_normalizer_bot (L2 ⊔ S)) hHW hE hO e
      (⊤ : Subgroup ↥(L2 ⊔ S)) w
    rw [htopmap, hsubtop] at hiff
    have hwC : (w : G) ∈ Subgroup.centralizer ((L2 ⊔ S : Subgroup G) : Set G) := hiff.1 hm
    have hwbot : w = 1 := by
      have hmem : (w : G) ∈
          Z2 L1 L2 S ⊓ Subgroup.centralizer ((L2 ⊔ S : Subgroup G) : Set G) :=
        Subgroup.mem_inf.mpr ⟨w.2, hwC⟩
      rw [hCbot] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    rw [← hmw, hwbot, map_one]
    rfl
  have hNnat : IsNaturalModule Nsub.toRepresentation := by
    let eι : Additive (Ch3z.chiefMod ⊥ V) ≃ₗ[ZMod 2] ↥(LinearMap.range ι) :=
      LinearEquiv.ofInjective ι hιinj
    have heι : ∀ y : Additive (Ch3z.chiefMod ⊥ V),
        ((eι y : ↥(LinearMap.range ι)) : Additive (Ch3z.chiefMod ⊥ (Z2 L1 L2 S))) = ι y :=
      fun y => rfl
    refine ⟨eι.symm.toAddEquiv.trans φ, ?_⟩
    rintro g ⟨x, hx⟩
    have hx' := hx
    obtain ⟨y, hy⟩ := hx'
    have hu : (⟨x, hx⟩ : ↥(LinearMap.range ι)) = ⟨ι y, ⟨y, rfl⟩⟩ := Subtype.ext hy.symm
    rw [hu]
    have h2 : eι (ρ0 g y) = Nsub.toRepresentation g ⟨ι y, ⟨y, rfl⟩⟩ := by
      apply Subtype.ext
      show ι (ρ0 g y) = ρW g (ι y)
      exact (hι g y).symm
    have h1 : eι.symm (Nsub.toRepresentation g ⟨ι y, ⟨y, rfl⟩⟩) = ρ0 g y := by
      rw [← h2, LinearEquiv.symm_apply_apply]
    have h2' : eι.symm (⟨ι y, ⟨y, rfl⟩⟩ : ↥(LinearMap.range ι)) = y := by
      have hys : (⟨ι y, ⟨y, rfl⟩⟩ : ↥(LinearMap.range ι)) = eι y := Subtype.ext rfl
      rw [hys, LinearEquiv.symm_apply_apply]
    have h3 : φ (eι.symm (Nsub.toRepresentation g ⟨ι y, ⟨y, rfl⟩⟩)) = φ (ρ0 g y) := by
      rw [h1]
    show φ (eι.symm (Nsub.toRepresentation g ⟨ι y, ⟨y, rfl⟩⟩)) =
      (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 (2 * a + 1))).mulVec
        (φ (eι.symm (⟨ι y, ⟨y, rfl⟩⟩ : ↥(LinearMap.range ι))))
    rw [h3, hφnat, h2']
  let q : ↥(L2 ⊔ S) →* oTwoQuot ↥(L2 ⊔ S) :=
    QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L2 ⊔ S))
  let ψS : ↥(L2 ⊔ S) →* SL(2, GaloisField 2 (2 * a + 1)) := e.toMonoidHom.comp q
  let A : Subgroup (SL(2, GaloisField 2 (2 * a + 1))) := (S.subgroupOf (L2 ⊔ S)).map ψS
  have hAeq : Subgroup.map e.toMonoidHom (Subgroup.map q (S.subgroupOf (L2 ⊔ S))) = A := by
    rw [Subgroup.map_map]
  obtain ⟨hSH, hSp, hSidx⟩ := id hsylow
  let PH : Sylow 2 ↥(L2 ⊔ S) := (hSp.comap_subtype (K := L2 ⊔ S)).toSylow hSidx
  have hPHcoe : (PH : Subgroup ↥(L2 ⊔ S)) = S.subgroupOf (L2 ⊔ S) := IsPGroup.toSylow_coe _ _
  let Pq : Sylow 2 (oTwoQuot ↥(L2 ⊔ S)) := PH.mapSurjective (f := q)
    (QuotientGroup.mk'_surjective _)
  have hPqcoe : (Pq : Subgroup (oTwoQuot ↥(L2 ⊔ S))) = (S.subgroupOf (L2 ⊔ S)).map q := by
    change ((PH.mapSurjective (f := q) (QuotientGroup.mk'_surjective _) :
      Sylow 2 (oTwoQuot ↥(L2 ⊔ S))) : Subgroup (oTwoQuot ↥(L2 ⊔ S))) =
      (S.subgroupOf (L2 ⊔ S)).map q
    rw [Sylow.coe_mapSurjective, hPHcoe]
  let PA : Sylow 2 (SL(2, GaloisField 2 (2 * a + 1))) := Pq.mapSurjective (f := e.toMonoidHom)
    (by simpa using e.surjective)
  have hPAcoe : (PA : Subgroup (SL(2, GaloisField 2 (2 * a + 1)))) = A := by
    change ((Pq.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective) :
      Sylow 2 (SL(2, GaloisField 2 (2 * a + 1)))) : Subgroup _) = A
    rw [Sylow.coe_mapSurjective, hPqcoe]
    exact hAeq
  obtain ⟨x, hx⟩ := exists_conjSubgroup_utri_eq_of_sylow PA
  have hxA : ∀ g : SL(2, GaloisField 2 (2 * a + 1)),
      g ∈ A ↔ x⁻¹ * g * x ∈ utri (GaloisField 2 (2 * a + 1)) := by
    intro g
    rw [← hPAcoe, ← hx, mem_conjSubgroup]
  have hFcard : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  have hF3 : 3 ≤ Nat.card (GaloisField 2 (2 * a + 1)) := by
    rw [hFcard]
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hL : fixedSub ρW (utri (GaloisField 2 (2 * a + 1))) ≤ Nsub.toSubmodule :=
    lemmaNat_sl2 hF3 ρW Nsub hNnat hQ hcent
  have hfix_le : fixedSub ρW A ≤ Nsub.toSubmodule := by
    intro v hv
    have h1 : ρW x⁻¹ v ∈ fixedSub ρW (utri (GaloisField 2 (2 * a + 1))) := by
      rw [mem_fixedSub]
      intro u hu
      have huA : x * u * x⁻¹ ∈ A := (hxA _).mpr (by
        rw [show x⁻¹ * (x * u * x⁻¹) * x = u by group]
        exact hu)
      have h2 : ρW (x * u * x⁻¹) v = v := mem_fixedSub.mp hv _ huA
      calc ρW u (ρW x⁻¹ v) = ρW x⁻¹ (ρW (x * u * x⁻¹) v) := by
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
            congr 1
            group
        _ = ρW x⁻¹ v := by rw [h2]
    have h3 : ρW x (ρW x⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h3]
    exact Nsub.apply_mem_toSubmodule x (hL h1)
  have hupper : Z1 L1 L2 S ≤ V := by
    rw [← hZ2CSeq]
    intro z hz
    obtain ⟨hz2, hzC⟩ := Subgroup.mem_inf.mp hz
    have hSmap : ((S.subgroupOf (L2 ⊔ S)).map (L2 ⊔ S).subtype : Subgroup G) = S :=
      Subgroup.map_subgroupOf_eq_of_le le_sup_right
    have hmem : Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) ⟨z, hz2⟩) ∈
        fixedSub ρW A := by
      rw [← hAeq]
      exact (mem_fixSub_sectionRep_bot_iff (D14.le_normalizer_bot (L2 ⊔ S)) hHW hE hO e
        (S.subgroupOf (L2 ⊔ S)) ⟨z, hz2⟩).mpr (by rw [hSmap]; exact hzC)
    have hmem' : Additive.ofMul (chiefModBotMulEquiv (Z2 L1 L2 S) ⟨z, hz2⟩) ∈
        subZ (W := Z2 L1 L2 S) hE V := by
      have h := hfix_le hmem
      rwa [hNsub_sub] at h
    exact mem_subZ_iff.mp hmem'
  refine le_antisymm ?_ ?_
  ·
    refine le_inf hupper ?_
    rw [← hZ2CSeq]
    exact inf_le_right
  ·
    intro z hz
    rw [← hZ2CSeq]
    exact Subgroup.mem_inf.mpr ⟨hVZ (Subgroup.mem_inf.mp hz).1, (Subgroup.mem_inf.mp hz).2⟩

theorem str83G4Z1Card_holds :
    Str83G4Z1Card := by
  intro G _ _ L1 L2 S a hfr
  classical
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨V, hV⟩ :=
    str83G3Output_of_z2Central str83G4Z2Central_holds G L1 L2 S a
      ⟨hF, hB, ha, hSz, hL2, hZI⟩
  have heq := str83G4_z1_eq_inf_centralizer ⟨hF, hB, ha, hSz, hL2, hZI⟩ hV
  obtain ⟨-, -, hnat⟩ := hV
  obtain ⟨hstep, hVH, hVea, hdata⟩ := hnat
  obtain ⟨e, ρ0, φ, hcompat, hφnat⟩ := hdata
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hsylow : IsSylowTwoOf S (L2 ⊔ S) := by
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    have hQ : Q1 L2 L1 S = Q2 L1 L2 S := by simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hQ, show L2 ⊔ Q2 L1 L2 S = L2 ⊔ S from hsup2.symm] at h
    exact h
  rw [heq]
  exact l2_chiefStep_fixedLine_card (n := 2 * a + 1) (by omega) hsylow hVH hVea hstep e ρ0
    φ hcompat hφnat

end CFSG.Quasithin.Stroth

end
