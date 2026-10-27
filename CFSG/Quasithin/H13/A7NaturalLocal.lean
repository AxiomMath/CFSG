module

public import CFSG.Quasithin.H13.A7HyperplaneConj
public import CFSG.Quasithin.H13.A7IrrPlus
public import CFSG.Quasithin.H13.A7HyperplaneConfine
public import CFSG.Quasithin.H13.A7SharedCentralCover
public import CFSG.Quasithin.H13.U3Local1332

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB
open scoped Pointwise commutatorElement

section Conj

variable {G : Type*} [Group G]

theorem conjugate_eq_conj_smul (V : Subgroup G) (g : G) :
    CFSG.conjugate V g = MulAut.conj g⁻¹ • V := by
  ext x
  rw [mem_conjugate_iff_mem, mem_conj_smul_iff]

theorem conjugateJoin_eq_conj_smul (V T : Subgroup G) :
    (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) =
      ⨆ (g : G) (_ : MulAut.conj g⁻¹ • V ≤ T), MulAut.conj g⁻¹ • V := by
  simp only [conjugate_eq_conj_smul]

end Conj

section Action

variable {G : Type*} [Group G]

theorem pCoreOf_le_centralizer_of_coord [Finite G] {L V : Subgroup G}
    (hLV : L ≤ normalizer (V : Set G)) (ψ : V ≃* Multiplicative (evenWeight 7))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ) :
    pCoreOf 2 L ≤ centralizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : ∀ a ∈ L, ∃ σ, IsCoordAct ψ a σ := fun a ha => by
    obtain ⟨σ, -, h⟩ := hLact a ha
    exact ⟨σ, h⟩
  set ρ := coordRep ψ hLV hA with hρ
  have himg : ∀ l : L, ρ l ∈ alternatingGroup (Fin 7) := by
    intro l
    obtain ⟨σ, hσ, hact⟩ := hLact l l.2
    rw [IsCoordAct.unique ψ (hLV l.2) (coordRep_spec ψ hLV hA l) hact]
    exact hσ
  have hsurj : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l : L, ρ l = σ := by
    intro σ hσ
    obtain ⟨l, hl, hact⟩ := hLonto σ hσ
    exact ⟨⟨l, hl⟩, IsCoordAct.unique ψ (hLV hl) (coordRep_spec ψ hLV hA ⟨l, hl⟩) hact⟩
  set N : Subgroup (Perm (Fin 7)) := (CFSG.pCore 2 L).map ρ with hN
  have hNA : N ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨l, -, rfl⟩
    exact himg l
  have hN2 : IsPGroup 2 N := (CFSG.pCore_isPGroup (p := 2) (G := L)).map ρ
  have hNbot : N = ⊥ := by
    refine eq_bot_of_isPGroup_of_normal_alternating hNA hN2 fun g hg n hn => ?_
    obtain ⟨l, hl⟩ := hsurj g hg
    obtain ⟨r, hr, hrn⟩ := hn
    refine ⟨l * r * l⁻¹, (CFSG.pCore_normal (p := 2) (G := L)).conj_mem r hr l, ?_⟩
    rw [map_mul, map_mul, map_inv, hl, hrn]
  rw [pCoreOf_eq_map_cfsgPCore]
  rintro _ ⟨r, hr, rfl⟩
  have h1 : ρ r = 1 := by
    have : ρ r ∈ N := ⟨r, hr, rfl⟩
    rwa [hNbot, mem_bot] at this
  exact (coordRep_eq_one_iff ψ hLV hA r).1 h1

theorem commutator_mem_pCoreOf_of_mem_centralizer [Finite G] {L V : Subgroup G}
    (hLV : L ≤ normalizer (V : Set G)) (ψ : V ≃* Multiplicative (evenWeight 7))
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hRV : pCoreOf 2 L ≤ centralizer (V : Set G)) :
    ∀ x ∈ L ⊓ centralizer (V : Set G), ∀ l ∈ L, ⁅x, l⁆ ∈ pCoreOf 2 L := by
  classical
  set C : Subgroup L := (centralizer (V : Set G)).subgroupOf L with hC
  have hCn : C.Normal := by
    constructor
    intro c hc l
    rw [hC, mem_subgroupOf] at hc ⊢
    rw [mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : (l : G)⁻¹ * v * (l : G) ∈ V := by
      have := (mem_normalizer_iff.1 (hLV (inv_mem l.2)) v).1 hv
      simpa using this
    have h1 := hc _ hv'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc v * ((l : G) * c * (l : G)⁻¹)
        = (l : G) * ((l : G)⁻¹ * v * l * c) * (l : G)⁻¹ := by group
      _ = (l : G) * (c * ((l : G)⁻¹ * v * l)) * (l : G)⁻¹ := by rw [h1]
      _ = (l : G) * c * (l : G)⁻¹ * v := by group
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hq
  have hCq : (C.map q).Normal := hCn.map q (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hCq with h | h
  ·
    exfalso
    obtain ⟨l, hl, hact⟩ := hLonto _ threeCycle_mem
    obtain ⟨c, hc, hcl⟩ : q ⟨l, hl⟩ ∈ C.map q := h ▸ mem_top _
    have hr : c⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq]
      exact hcl
    have hrV : ((c⁻¹ * ⟨l, hl⟩ : L) : G) ∈ centralizer (V : Set G) :=
      hRV (by rw [pCoreOf_eq_map_cfsgPCore]; exact ⟨_, hr, rfl⟩)
    have hcV : (c : G) ∈ centralizer (V : Set G) := hc
    have hlV : l ∈ centralizer (V : Set G) := by
      have := mul_mem hcV hrV
      simpa using this
    exact threeCycle_ne_one
      (IsCoordAct.unique ψ (hLV hl) hact (isCoordAct_one_of_mem_centralizer ψ hlV))
  · intro x hx l hl
    have hxC : (⟨x, hx.1⟩ : L) ∈ C := by
      rw [hC, mem_subgroupOf]
      exact hx.2
    have hz : q ⟨x, hx.1⟩ ∈ center (↥L ⧸ CFSG.pCore 2 ↥L) := h ⟨_, hxC, rfl⟩
    have hcomm : q ⁅(⟨x, hx.1⟩ : L), ⟨l, hl⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.1 hz (q ⟨l, hl⟩)).symm
    have hmem : ⁅(⟨x, hx.1⟩ : L), ⟨l, hl⟩⁆ ∈ CFSG.pCore 2 ↥L := by
      rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcomm
    rw [pCoreOf_eq_map_cfsgPCore]
    refine ⟨_, hmem, ?_⟩
    simp [commutatorElement_def]

end Action

section Kernel

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_pCoreOf_two {L : Subgroup G} :
    normalizer (L : Set G) ≤ normalizer (pCoreOf 2 L : Set G) := by
  rw [pCoreOf_eq_map_cfsgPCore]
  intro x hx
  let φ : L ≃* L :=
    { toFun := fun l => ⟨x * l * x⁻¹, (mem_normalizer_iff.1 hx l).1 l.2⟩
      invFun := fun l => ⟨x⁻¹ * l * x, by
        have := (mem_normalizer_iff.1 (inv_mem hx) l).1 l.2
        simpa using this⟩
      left_inv := fun l => Subtype.ext (by simp only; group)
      right_inv := fun l => Subtype.ext (by simp only; group)
      map_mul' := fun a b => Subtype.ext (by
        show x * ((a : G) * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹)
        group) }
  have hchar : (CFSG.pCore 2 ↥L).Characteristic := inferInstance
  have hfix : (CFSG.pCore 2 ↥L).map φ.toMonoidHom = CFSG.pCore 2 ↥L :=
    (characteristic_iff_map_eq.1 hchar) φ
  have key : ∀ y : G, y ∈ (CFSG.pCore 2 ↥L).map L.subtype →
      x * y * x⁻¹ ∈ (CFSG.pCore 2 ↥L).map L.subtype := by
    rintro _ ⟨r, hr, rfl⟩
    have : φ r ∈ CFSG.pCore 2 ↥L := hfix ▸ ⟨r, hr, rfl⟩
    exact ⟨φ r, this, rfl⟩
  have key' : ∀ y : G, y ∈ (CFSG.pCore 2 ↥L).map L.subtype →
      x⁻¹ * y * x⁻¹⁻¹ ∈ (CFSG.pCore 2 ↥L).map L.subtype := by
    rintro _ ⟨r, hr, rfl⟩
    have hfix' : (CFSG.pCore 2 ↥L).map φ.symm.toMonoidHom = CFSG.pCore 2 ↥L :=
      (characteristic_iff_map_eq.1 hchar) φ.symm
    have : φ.symm r ∈ CFSG.pCore 2 ↥L := hfix' ▸ ⟨r, hr, rfl⟩
    refine ⟨φ.symm r, this, ?_⟩
    simp [φ]
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact key y
  · intro hy
    have := key' _ hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this

theorem index_subgroupOf_sup_eq_two_pow [Finite G] {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) :
    ∃ k : ℕ, (L.subgroupOf (L ⊔ T)).index = 2 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := L ⊔ T with hX
  have hXL : X ≤ normalizer (L : Set G) := sup_le le_normalizer hTL
  have hLn : (L.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).2 hXL
  have hq : IsPGroup 2 (↥X ⧸ L.subgroupOf X) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : (x : G) ∈ ((L ⊔ T : Subgroup G) : Set G) := x.2
    rw [coe_mul_of_right_le_normalizer_left L T hTL] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    obtain ⟨k, hk⟩ := hT ⟨b, hb⟩
    refine ⟨k, ?_⟩
    have hbX : b ∈ X := le_sup_right (a := L) hb
    have haX : a ∈ X := le_sup_left (b := T) ha
    have hx' : x = ⟨a, haX⟩ * ⟨b, hbX⟩ := Subtype.ext hab.symm
    have hk' : (⟨b, hbX⟩ : X) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [hx', QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (⟨a, haX⟩ : X)).2 (by rw [mem_subgroupOf]; exact ha), one_mul,
      ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hq
  exact ⟨k, by rw [index_eq_card, hk]⟩

end Kernel

variable {G : Type} [Group G]

theorem A7_natural_local_produces_normalizer_and_solvable_confinement (h331 : Stmt3_3_1)
    [Finite G] (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQTKE : QuasithinUnique.quasithinIsQTKECat G) (T : Sylow 2 G) {L : Subgroup G}
    (hLmax : quasithinIsMaximalLocal (T : Subgroup G) L)
    (_hLf : quasithinIsFaithfulLocal (T : Subgroup G) L)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {V : Subgroup G}
    (hVT : V ≤ (T : Subgroup G)) (hLV : L ≤ normalizer (V : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (ψ : V ≃* Multiplicative (evenWeight 7))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    (hNact : ∀ n ∈ normalizer (V : Set G), ∃ σ, IsCoordAct ψ n σ)
    (hNM : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (hTI : ∀ m ∈ normalizer (L : Set G),
      CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥)
    (hwt2 : ∀ v : V, hammingNorm (vec ψ v) = 2 →
      centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G))
    (hwt4 : ∀ g : G, CFSG.conjugate V g ≠ V → ∀ v : V, (v : G) ∈ CFSG.conjugate V g → v ≠ 1 →
      hammingNorm (vec ψ v) = 4) :
    L ⊔ T ≤ normalizer (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ∧
      V ≠ ⊥ ∧ V ≤ (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) ∧
      (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      U3.UniqueMaxTwoLocal
        (normalizer (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G))
        (normalizer (L : Set G)) ∧
      normalizer ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g :
        Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
      normalizer ((T : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
      ∀ H : Subgroup G, (T : Subgroup G) ≤ H → Group.IsSolvable H →
        H ≤ normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalizer (L : Set G) with hMdef
  set Q : Subgroup G := (T : Subgroup G) ⊓ centralizer (V : Set G) with hQdef
  set W : Subgroup G := ⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g with hWdef
  have hTL : (T : Subgroup G) ≤ M := hTV.trans hNM
  set X : Subgroup G := L ⊔ T with hXdef
  have hXL : X ≤ M := sup_le le_normalizer hTL
  have hXV : X ≤ normalizer (V : Set G) := sup_le hLV hTV
  have hV64 : Nat.card V = 64 := nat_card_of_vec ψ
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    omega
  have hVel : CFSG.IsElementaryAbelian 2 V :=
    { toIsMulCommutative := ⟨⟨fun a b => mul_comm_of_vec ψ a b⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        rw [pow_two]
        exact sq_eq_one_of_vec ψ x }
  have hTI' : ∀ m ∈ M, MulAut.conj m⁻¹ • V = V ∨ V ⊓ (MulAut.conj m⁻¹ • V) = ⊥ := by
    intro m hm
    rw [← conjugate_eq_conj_smul]
    exact hTI m hm
  have hwt4' : ∀ g : G, MulAut.conj g⁻¹ • V ≠ V → ∀ v : V, (v : G) ∈ MulAut.conj g⁻¹ • V →
      v ≠ 1 → hammingNorm (vec ψ v) = 4 := by
    intro g hg v hv hv1
    rw [← conjugate_eq_conj_smul] at hg hv
    exact hwt4 g hg v hv hv1
  obtain ⟨hhyp', hWQ'⟩ := A7_hyperplane_in_Sylow_centralizes_entire_conjugate hVel hV64
    T.isPGroup' hVT hTV hNM ψ hNact hTI' hwt2 hwt4'
  have hhyp : ∀ (g : G) (B : Subgroup G), B ≤ CFSG.conjugate V g ⊓ T →
      B.relIndex (CFSG.conjugate V g) ≤ 2 → ⁅V, CFSG.conjugate V g⁆ = ⊥ := by
    intro g B hB hBi
    rw [conjugate_eq_conj_smul] at hB hBi ⊢
    exact hhyp' g B hB hBi
  have hWQ : W ≤ Q := by
    rw [hWdef, conjugateJoin_eq_conj_smul]
    exact hWQ'
  have hVW : V ≤ W := by
    refine le_iSup₂_of_le (f := fun g (_ : CFSG.conjugate V g ≤ T) => CFSG.conjugate V g) 1
      ?_ ?_
    · rw [conjugate_eq_conj_smul, inv_one, map_one, one_smul]
      exact hVT
    · rw [conjugate_eq_conj_smul, inv_one, map_one, one_smul]
  have hVQ : V ≤ Q := hVW.trans hWQ
  have hQT : Q ≤ (T : Subgroup G) := inf_le_left
  have hQ1 : Q ≠ ⊥ := fun h => hV1 (le_bot_iff.1 (h ▸ hVQ))
  have hQ2 : IsPGroup 2 Q := T.isPGroup'.to_le hQT
  have hW1 : W ≠ ⊥ := fun h => hV1 (le_bot_iff.1 (h ▸ hVW))
  have hW2 : IsPGroup 2 W := hQ2.to_le hWQ
  have hRV : pCoreOf 2 L ≤ centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_coord hLV ψ hLact hLonto
  have hcent0 := commutator_mem_pCoreOf_of_mem_centralizer hLV ψ hLonto hLq hRV
  have hQX : X ≤ normalizer (Q : Set G) := by
    have hLX : L ≤ X := le_sup_left
    have hTX : (T : Subgroup G) ≤ X := le_sup_right
    have hVX : V ≤ X := hVT.trans hTX
    have hRL : pCoreOf 2 L ≤ L := map_subtype_le _
    have hRX : pCoreOf 2 L ≤ X := hRL.trans hLX
    have hLXn : (L.subgroupOf X).Normal :=
      (normal_subgroupOf_iff_le_normalizer hLX).2 hXL
    have hVXn : (V.subgroupOf X).Normal :=
      (normal_subgroupOf_iff_le_normalizer hVX).2 hXV
    have hRXn : ((pCoreOf 2 L).subgroupOf X).Normal :=
      (normal_subgroupOf_iff_le_normalizer hRX).2
        (hXL.trans normalizer_le_normalizer_pCoreOf_two)
    have hLperf : ⁅L, L⁆ = L := hLmax.1.2.1.2.1
    have hLXperf : ⁅L.subgroupOf X, L.subgroupOf X⁆ = L.subgroupOf X := by
      apply map_injective X.subtype_injective
      rw [map_commutator, subgroupOf_map_subtype, inf_eq_left.2 hLX, hLperf]
    obtain ⟨k, hk⟩ := index_subgroupOf_sup_eq_two_pow T.isPGroup' hTL
    let ρ : X →* MulAut (V.subgroupOf X) := MulAut.conjNormal
    have hker : ρ.ker = centralizer ((V.subgroupOf X : Subgroup X) : Set X) := by
      ext x
      rw [MonoidHom.mem_ker, mem_centralizer_iff]
      constructor
      · intro h v hv
        have h1 := congrArg (fun f : MulAut (V.subgroupOf X) => ((f ⟨v, hv⟩ : V.subgroupOf X) : X))
          h
        simp only [ρ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
        calc v * x = x * v * x⁻¹ * x := by rw [h1]
          _ = x * v := by group
      · intro h
        apply MulEquiv.ext
        intro v
        apply Subtype.ext
        simp only [ρ, MulAut.conjNormal_apply, MulAut.one_apply]
        rw [← h v v.2]
        group
    have hRLN : (pCoreOf 2 L).subgroupOf X ≤ L.subgroupOf X ⊓ ρ.ker := by
      intro r hr
      rw [mem_subgroupOf] at hr
      refine mem_inf.2 ⟨by rw [mem_subgroupOf]; exact hRL hr, ?_⟩
      rw [hker, mem_centralizer_iff]
      intro v hv
      rw [SetLike.mem_coe, mem_subgroupOf] at hv
      exact Subtype.ext (mem_centralizer_iff.1 (hRV hr) v hv)
    have hR2 : IsPGroup 2 ((pCoreOf 2 L).subgroupOf X) := by
      have hR : IsPGroup 2 (pCoreOf 2 L) := by
        rw [pCoreOf_eq_map_cfsgPCore]
        exact (CFSG.pCore_isPGroup (p := 2) (G := L)).map L.subtype
      intro r
      obtain ⟨n, hn⟩ := hR ⟨(r : X), r.2⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hn
      simpa using this
    have hcent : ∀ x ∈ L.subgroupOf X ⊓ ρ.ker, ∀ l ∈ L.subgroupOf X,
        ⁅x, l⁆ ∈ (pCoreOf 2 L).subgroupOf X := by
      intro x hx l hl
      rw [mem_inf, hker, mem_subgroupOf] at hx
      rw [mem_subgroupOf] at hl ⊢
      have hxV : (x : G) ∈ centralizer (V : Set G) := by
        rw [mem_centralizer_iff]
        intro v hv
        have := mem_centralizer_iff.1 hx.2 ⟨v, hVX hv⟩
          (show (⟨v, hVX hv⟩ : X) ∈ V.subgroupOf X from hv)
        exact congrArg Subtype.val this
      have := hcent0 (x : G) ⟨hx.1, hxV⟩ (l : G) hl
      simpa [commutatorElement_def] using this
    have hmain := (A7_perfect_central_cover_kernel_has_normal_Sylow_two (X := X)
      (L := L.subgroupOf X) hLXperf hk ρ hRLN hR2 hcent).2
    obtain ⟨Q', -, -, -, -, -, -, hQnormal⟩ := hmain
    have hVcomm : IsMulCommutative (V.subgroupOf X) :=
      ⟨⟨fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        show ((a : X) : G) * ((b : X) : G) = ((b : X) : G) * ((a : X) : G)
        exact congrArg Subtype.val (mul_comm_of_vec ψ ⟨((a : X) : G), a.2⟩ ⟨((b : X) : G), b.2⟩)⟩⟩
    have hVTX : V.subgroupOf X ≤ ((T.subtype hTX : Sylow 2 X) : Subgroup X) := by
      intro v hv
      rw [mem_subgroupOf] at hv
      show v ∈ (T : Subgroup G).subgroupOf X
      rw [mem_subgroupOf]
      exact hVT hv
    obtain ⟨-, -, hn⟩ := hQnormal (T.subtype hTX) (V.subgroupOf X) hVXn hVcomm hVTX hker
    have heq : ((T.subtype hTX : Sylow 2 X) : Subgroup X) ⊓
        centralizer ((V.subgroupOf X : Subgroup X) : Set X) = Q.subgroupOf X := by
      ext x
      simp only [mem_inf, mem_subgroupOf, hQdef, mem_centralizer_iff, SetLike.mem_coe]
      constructor
      · rintro ⟨hxT, hxc⟩
        refine ⟨hxT, fun v hv => ?_⟩
        exact congrArg Subtype.val (hxc ⟨v, hVX hv⟩ hv)
      · rintro ⟨hxT, hxc⟩
        exact ⟨hxT, fun v hv => Subtype.ext (hxc (v : G) hv)⟩
    rw [heq] at hn
    exact (normal_subgroupOf_iff_le_normalizer (hQT.trans le_sup_right)).1 hn
  have hTsyl : quasithinIsSylowTwo (T : Subgroup G) := ⟨T.isPGroup', T.not_dvd_index⟩
  obtain ⟨-, h331B⟩ := h331 G T hs hnab hQTKE hTsyl
  obtain ⟨⟨hMmax, -, huniq⟩, -⟩ := h331B L hLmax hLq
  have hcl : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun _ ht l hl => (mem_normalizer_iff.1 (hTL ht) l).1 hl)
      (le_conjClosure L T)
  rw [hcl] at hMmax huniq
  have hNQ : normalizer (Q : Set G) ≤ M :=
    U3.normalizer_le_of_uniqueMaxTwoLocal huniq hQ1 hQ2 hQX
  have hUQ : U3.UniqueMaxTwoLocal (normalizer (Q : Set G)) M :=
    ⟨hMmax, hNQ, fun M' hM' hQM' => huniq M' hM' (hQX.trans hQM')⟩
  have hVgQ : ∀ g : G, CFSG.conjugate V g ≤ T → CFSG.conjugate V g ≤ Q := fun g hg =>
    (le_iSup₂_of_le (f := fun g (_ : CFSG.conjugate V g ≤ T) => CFSG.conjugate V g) g hg
      le_rfl).trans hWQ
  have hQW : normalizer (Q : Set G) ≤ normalizer (W : Set G) := fun n hn =>
    mem_normalizer_conjugateJoin_of hQT hVgQ hn
  have hWM : normalizer (W : Set G) ≤ M := by
    obtain ⟨M', hM', hle⟩ := U3.exists_maxTwoLocal_le ⟨W, hW1, hW2, rfl⟩
    have hM'eq := huniq M' hM' (hQX.trans (hQW.trans hle))
    rw [hM'eq] at hle
    exact hle
  have hTW : normalizer ((T : Subgroup G) : Set G) ≤ normalizer (W : Set G) := fun n hn =>
    mem_normalizer_conjugateJoin_of le_rfl (fun _ hg => hg) hn
  refine ⟨hQX, hV1, hVW, hWQ, hUQ, hWM, hTW.trans hWM, fun H hTH hH => ?_⟩
  exact A7_hyperplane_conjugates_confine_solvable_Sylow_overgroups T hV1 hVT hVel hWM
    ((Subgroup.centralizer_le_normalizer (V : Set G)).trans hNM) hhyp H hTH hH

end CFSG.Quasithin.H13.A7
