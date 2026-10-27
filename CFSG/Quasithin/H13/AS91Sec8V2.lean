module

public import CFSG.Quasithin.H13.AS91Sec5Line
public import CFSG.Quasithin.H13.AS91Sec8Defs
public import CFSG.Quasithin.H13.AS91Sec8FixOctHolds
public import CFSG.Quasithin.H13.AS91Sec8KDer

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.ASVolI.ChH
open scoped Pointwise

namespace M24G

theorem exists_conj_eq_of_mulEquiv
    (θ : ↥M24g ≃* ↥M24g) :
    ∃ n ∈ M24g, ∀ g : ↥M24g, ((θ g : ↥M24g) : S24) = n * (g : S24) * n⁻¹ := by
  let e : ↥M24g ≃* ↥CFSG.Blueprint.NativeSporadic.M24 :=
    (MulEquiv.subgroupCongr (show M24g =
        CFSG.Blueprint.NativeSporadic.M24.map
          (MulAut.conj CFSG.Monster.Code.bridgeQ⁻¹).toMonoidHom from
      CFSG.Monster.Code.AutPerm_eq_closure.trans CFSG.Monster.Code.bridge_closure_eq_map)).trans
      (Subgroup.equivMapOfInjective CFSG.Blueprint.NativeSporadic.M24
        (MulAut.conj CFSG.Monster.Code.bridgeQ⁻¹).toMonoidHom
        (by simpa only [MulEquiv.coe_toMonoidHom] using
          (MulAut.conj CFSG.Monster.Code.bridgeQ⁻¹).injective)).symm
  have hinnerN : CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥CFSG.Blueprint.NativeSporadic.M24 = ⊤ :=
    CFSG.Sporadic.Schreier.inner_eq_top_of_card_le
      CFSG.Sporadic.Schreier.m24_center_eq_bot' CFSG.Sporadic.Schreier.m24_mulAut_card
  have hθ : θ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥M24g := by
    have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥M24g).map
        (MulAut.congr e).toMonoidHom =
        CFSG.ComponentClassification.OuterAutomorphisms.inner
          ↥CFSG.Blueprint.NativeSporadic.M24 :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
    rw [hinnerN] at hmap
    have hmem : MulAut.congr e θ ∈
        (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥M24g).map
          (MulAut.congr e).toMonoidHom := by
      rw [hmap]
      trivial
    obtain ⟨β, hβ, hβθ⟩ := Subgroup.mem_map.mp hmem
    exact (MulAut.congr e).injective hβθ ▸ hβ
  obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hθ
  refine ⟨(n : ↥M24g), n.2, fun g => ?_⟩
  have h := congrArg (fun f : MulAut ↥M24g => f g) hn
  rw [MulAut.conj_apply] at h
  rw [← h]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem eq_of_forall_smul_sextet
    {U W : Finset (Finset (Fin 24))} (hU : IsSextet U) (hW : IsSextet W)
    (h : ∀ g ∈ M24g, g • U = U → g • W = W) : W = U := by
  obtain ⟨i, hi, -⟩ := xi_existsUnique hU hW
  have hWmem : W ∈ {W' | IsSextet W' ∧ Xi U W' i} := ⟨hW, hi⟩
  have hsub : {W' | IsSextet W' ∧ Xi U W' i} ⊆ {W} := by
    intro W' hW'
    obtain ⟨g, hg, hgU, hgW⟩ := xi_orbit hU hW hW'.1 hi hW'.2
    rw [h g hg hgU] at hgW
    simpa using hgW.symm
  have hle : {W' | IsSextet W' ∧ Xi U W' i}.ncard ≤ 1 := by
    have := Set.ncard_le_ncard hsub
    simpa using this
  have hpos : 0 < {W' | IsSextet W' ∧ Xi U W' i}.ncard := by
    rw [Set.ncard_pos]
    exact ⟨W, hWmem⟩
  have h1 : {W' | IsSextet W' ∧ Xi U W' i}.ncard = 1 := by omega
  rw [ncard_xi hU i] at h1
  have hi0 : i = 0 := by
    fin_cases i <;> simp_all
  have hX : Xi U W 0 := hi0 ▸ hi
  exact hX

end M24G

theorem autImage_subgroupCongr {G : Type*} [Group G] {H K : Subgroup G} (h : H = K) (φ : ↥H ≃* ↥H)
    (C : Subgroup G) :
    autImage ((MulEquiv.subgroupCongr h).symm.trans (φ.trans (MulEquiv.subgroupCongr h))) C =
      autImage φ C := by
  subst h
  rfl

theorem autPres_subgroupCongr {G : Type*} [Group G] {H K : Subgroup G} (h : H = K) (B : Subgroup G)
    (φ : ↥H ≃* ↥H) :
    autPres K B ((MulEquiv.subgroupCongr h).symm.trans (φ.trans (MulEquiv.subgroupCongr h))) ↔
      autPres H B φ := by
  subst h
  rfl

theorem autPres_congr {G : Type*} [Group G] {A B B' : Subgroup G} (h : B = B') (φ : ↥A ≃* ↥A) :
    autPres A B φ ↔ autPres A B' φ := by
  subst h
  rfl

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

@[expose] noncomputable def φM24 (ρ : ResM24 c) : ↥c.G1 →* ↥M24g :=
  ρ.φ.codRestrict M24g ρ.φ_mem

theorem φM24_ker {ρ : ResM24 c} : (φM24 c ρ).ker = c.E.subgroupOf c.G1 := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hh
    have h' : ρ.φ h = 1 := congrArg Subtype.val hh
    rw [← MonoidHom.mem_ker, ρ.ker_eq] at h'
    exact Subgroup.mem_subgroupOf.mp h'
  · intro hh
    have h' : h ∈ ρ.φ.ker := by
      rw [ρ.ker_eq]
      exact Subgroup.mem_subgroupOf.mpr hh
    exact Subtype.ext (MonoidHom.mem_ker.mp h')

theorem φM24_surjective {ρ : ResM24 c} : Function.Surjective (φM24 c ρ) := by
  intro x
  obtain ⟨h, hh⟩ := ρ.exists_φ_eq x.2
  exact ⟨h, Subtype.ext hh⟩

theorem φM24_apply {ρ : ResM24 c} (h : ↥c.G1) : ((φM24 c ρ h : ↥M24g) : S24) = ρ.φ h := rfl

theorem map_G31_φM24 {ρ : ResM24 c} :
    ((c.G3 ⊓ c.G1).subgroupOf c.G1).map (φM24 c ρ) =
      MulAction.stabilizer ↥M24g ρ.U₀ := by
  ext x
  obtain ⟨hx, rfl⟩ := φM24_surjective (c := c) (ρ := ρ) x
  rw [Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨h, hh, hval⟩
    have hh' : (h : G) ∈ c.G3 ⊓ c.G1 := by
      rwa [Subgroup.mem_subgroupOf] at hh
    rw [← hval]
    simpa only [φM24_apply, Subgroup.smul_def] using (ρ.stab₃ h).mp hh'.1
  · intro hxstab
    have hstab : ρ.φ hx • ρ.U₀ = ρ.U₀ := by
      simpa only [φM24_apply, Subgroup.smul_def] using hxstab
    exact ⟨hx, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨(ρ.stab₃ hx).mpr hstab, hx.2⟩), rfl⟩

theorem map_E_of_mulEquiv {ρ : ResM24 c}
    (ψ : ↥c.G1 ≃* ↥c.G1) :
    (c.E.subgroupOf c.G1).map ψ.toMonoidHom = c.E.subgroupOf c.G1 := by
  classical
  haveI hEnorm : (c.E.subgroupOf c.G1).Normal :=
    ⟨fun e he g => by
      rw [Subgroup.mem_subgroupOf] at he ⊢
      exact (Subgroup.mem_normalizer_iff.mp g.2 (e : G)).mp he⟩
  set N : Subgroup ↥c.G1 := (c.E.subgroupOf c.G1).map ψ.toMonoidHom with hN
  have hNnorm : N.Normal := hEnorm.map ψ.toMonoidHom ψ.surjective
  have hQnorm : (N.map (φM24 c ρ)).Normal :=
    hNnorm.map (φM24 c ρ) (φM24_surjective (c := c) (ρ := ρ))
  haveI : IsSimpleGroup ↥M24g := CFSG.Monster.Code.AutPerm_isSimpleGroup
  have hcardM : Nat.card ↥M24g = 244823040 := CFSG.Monster.Code.card_AutPerm
  have hQcard : Nat.card ↥(N.map (φM24 c ρ)) ≤ Nat.card ↥N :=
    Nat.card_le_card_of_surjective
      (fun n : ↥N => (⟨φM24 c ρ n.1, Subgroup.mem_map.mpr ⟨n.1, n.2, rfl⟩⟩ :
        ↥(N.map (φM24 c ρ))))
      (fun x => by
        obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp x.2
        exact ⟨⟨n, hn⟩, Subtype.ext hnx⟩)
  have hcardE : Nat.card ↥(c.E.subgroupOf c.G1) = 2 ^ 11 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.E_le_G1).toEquiv]
    exact c.card_E
  have hcardN : Nat.card ↥N = 2 ^ 11 := by
    rw [hN, Subgroup.card_map_of_injective (f := ψ.toMonoidHom)
      (by simpa only [MulEquiv.coe_toMonoidHom] using ψ.injective)]
    exact hcardE
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (φM24 c ρ)) with hbot | htop
  · have hle : N ≤ c.E.subgroupOf c.G1 := by
      have h := (Subgroup.map_eq_bot_iff N (f := φM24 c ρ)).mp hbot
      rwa [φM24_ker] at h
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardE, hcardN])
  · exfalso
    have htopcard : Nat.card ↥(N.map (φM24 c ρ)) = 244823040 := by
      rw [htop, Nat.card_congr (Subgroup.topEquiv (G := ↥M24g)).toEquiv]
      exact hcardM
    omega

theorem map_conj_G1_of_mem {g : G} (hg : g ∈ c.G1) :
    c.G1.map (MulAut.conj g).toMonoidHom = c.G1 := by
  have hE : c.E.map (MulAut.conj g).toMonoidHom = c.E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  rw [show c.G1 = Subgroup.normalizer (c.E : Set G) from rfl,
    Subgroup.map_equiv_normalizer_eq c.E (MulAut.conj g), hE]

theorem subgroupOf_G12_eq_comap {ρ : ResM24 c} :
    (c.G1 ⊓ c.G2).subgroupOf c.G1 =
      (MulAction.stabilizer ↥M24g ρ.l₀).comap (φM24 c ρ) := by
  ext h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
    Subgroup.mem_inf]
  constructor
  · rintro ⟨-, h2⟩
    simpa only [φM24_apply, Subgroup.smul_def] using (ρ.stab₂ h).mp h2
  · intro h2
    exact ⟨h.2, (ρ.stab₂ h).mpr (by simpa only [φM24_apply, Subgroup.smul_def] using h2)⟩

theorem subgroupOf_preFixOct_eq_comap {ρ : ResM24 c} :
    ρ.preFixOct.subgroupOf c.G1 =
      ((fixOct ρ.l₀).subgroupOf M24g).comap (φM24 c ρ) := by
  rw [ρ.subgroupOf_preFixOct_eq_comap]
  ext h
  rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  rfl

theorem map_comap_eq_of_comp_eq {ρ : ResM24 c} (ψ' : ↥c.G1 ≃* ↥c.G1)
    (hψ' : (φM24 c ρ).comp ψ'.toMonoidHom = φM24 c ρ) (S : Subgroup ↥M24g) :
    (S.comap (φM24 c ρ)).map ψ'.toMonoidHom = S.comap (φM24 c ρ) := by
  have hsymm : ∀ x : ↥c.G1, (φM24 c ρ) (ψ'.symm x) = (φM24 c ρ) x := by
    intro x
    have h := congrArg (fun f : ↥c.G1 →* ↥M24g => f (ψ'.symm x)) hψ'
    rw [MonoidHom.comp_apply] at h
    rw [show ψ'.toMonoidHom (ψ'.symm x) = x from by
      show ψ' (ψ'.symm x) = x
      exact ψ'.apply_symm_apply x] at h
    exact h.symm
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, Subgroup.mem_comap, hsymm x]

theorem map_E_of_comp_eq {ρ : ResM24 c} (ψ' : ↥c.G1 ≃* ↥c.G1)
    (hψ' : (φM24 c ρ).comp ψ'.toMonoidHom = φM24 c ρ) :
    (c.E.subgroupOf c.G1).map ψ'.toMonoidHom = c.E.subgroupOf c.G1 := by
  have h := c.map_comap_eq_of_comp_eq (ρ := ρ) ψ' hψ' (⊥ : Subgroup ↥M24g)
  rw [show (⊥ : Subgroup ↥M24g).comap (φM24 c ρ) = (φM24 c ρ).ker from rfl,
    φM24_ker] at h
  exact h

theorem map_G12_of_comp_eq {ρ : ResM24 c} (ψ' : ↥c.G1 ≃* ↥c.G1)
    (hψ' : (φM24 c ρ).comp ψ'.toMonoidHom = φM24 c ρ) :
    ((c.G1 ⊓ c.G2).subgroupOf c.G1).map ψ'.toMonoidHom =
      (c.G1 ⊓ c.G2).subgroupOf c.G1 := by
  rw [c.subgroupOf_G12_eq_comap]
  exact c.map_comap_eq_of_comp_eq (ρ := ρ) ψ' hψ' _

theorem map_preFixOct_of_comp_eq {ρ : ResM24 c} (ψ' : ↥c.G1 ≃* ↥c.G1)
    (hψ' : (φM24 c ρ).comp ψ'.toMonoidHom = φM24 c ρ) :
    (ρ.preFixOct.subgroupOf c.G1).map ψ'.toMonoidHom =
      ρ.preFixOct.subgroupOf c.G1 := by
  rw [c.subgroupOf_preFixOct_eq_comap]
  exact c.map_comap_eq_of_comp_eq (ρ := ρ) ψ' hψ' _

theorem subgroupOf_K_eq_commutator (r : ResM24T c) (hP : FixOctPerfect) (hS : FixOctSym)
    (hW : FixOctCommW11) :
    c.K.subgroupOf c.G1 =
      ⁅r.preFixOct.subgroupOf c.G1, r.preFixOct.subgroupOf c.G1⁆ ⊔
        ⁅c.E.subgroupOf c.G1, r.preFixOct.subgroupOf c.G1⁆ := by
  apply Subgroup.map_injective c.G1.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le r.preFixOct_le_G1,
    Subgroup.map_subgroupOf_eq_of_le c.E_le_G1,
    Subgroup.map_subgroupOf_eq_of_le c.K_le_G1, ResM24T.K_eq r hP hS hW]

theorem map_K_of_comp_eq (r : ResM24T c) (hP : FixOctPerfect) (hS : FixOctSym)
    (hW : FixOctCommW11) (ψ' : ↥c.G1 ≃* ↥c.G1)
    (hψ' : (φM24 c r.toResM24).comp ψ'.toMonoidHom = φM24 c r.toResM24) :
    (c.K.subgroupOf c.G1).map ψ'.toMonoidHom = c.K.subgroupOf c.G1 := by
  have hP' := c.map_preFixOct_of_comp_eq (ρ := r.toResM24) ψ' hψ'
  have hE' := c.map_E_of_comp_eq (ρ := r.toResM24) ψ' hψ'
  rw [c.subgroupOf_K_eq_commutator r hP hS hW, Subgroup.map_sup, Subgroup.map_commutator,
    Subgroup.map_commutator, hP', hE']

theorem map_subgroupOf_mulAutConj (M : Subgroup G) (hM : M ≤ c.G1) (k : ↥c.G1) :
    (M.map (MulAut.conj (k : G)).toMonoidHom).subgroupOf c.G1 =
      (M.subgroupOf c.G1).map (MulAut.conj k).toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨m, hM hm⟩, Subgroup.mem_subgroupOf.mpr hm, ?_⟩
    apply Subtype.ext
    show (((MulAut.conj k) ⟨m, hM hm⟩ : ↥c.G1) : G) = (x : G)
    rw [MulAut.conj_apply]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_map.mpr ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, ?_⟩
    have hyx' : (((MulAut.conj k) y : ↥c.G1) : G) = (x : G) := congrArg Subtype.val hyx
    rw [MulAut.conj_apply] at hyx'
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] using hyx'

theorem mulAut_conj_mul (n e : ↥c.G1) :
    (MulAut.conj e).trans (MulAut.conj n) = MulAut.conj (n * e) := by
  ext x
  rw [MulEquiv.trans_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem exists_conj_φ_of_mulEquiv {ρ : ResM24 c}
    (ψ : ↥c.G1 ≃* ↥c.G1) (hψ : autPres c.G1 (c.G3 ⊓ c.G1) ψ) :
    ∃ n : ↥c.G1, (n : G) ∈ c.G3 ⊓ c.G1 ∧
      ∀ h : ↥c.G1, ρ.φ (ψ h) = ρ.φ n * ρ.φ h * (ρ.φ n)⁻¹ := by
  classical
  have hE := c.map_E_of_mulEquiv (ρ := ρ) ψ
  let E : Subgroup ↥c.G1 := c.E.subgroupOf c.G1
  haveI hEnorm : E.Normal :=
    ⟨fun e he g => by
      rw [Subgroup.mem_subgroupOf] at he ⊢
      exact (Subgroup.mem_normalizer_iff.mp g.2 (e : G)).mp he⟩
  let θe : ↥c.G1 ⧸ E →* ↥M24g := QuotientGroup.lift E (φM24 c ρ) (by rw [φM24_ker])
  have hθe_inj : Function.Injective θe := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp only [θe]
    rw [QuotientGroup.ker_lift, φM24_ker, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hθe_surj : Function.Surjective θe := by
    intro x
    obtain ⟨h, hh⟩ := φM24_surjective (c := c) (ρ := ρ) x
    exact ⟨QuotientGroup.mk h, by simpa only [θe, QuotientGroup.lift_mk] using hh⟩
  let e : (↥c.G1 ⧸ E) ≃* ↥M24g := MulEquiv.ofBijective θe ⟨hθe_inj, hθe_surj⟩
  have e_mk : ∀ h : ↥c.G1, e (QuotientGroup.mk h) = φM24 c ρ h := by
    intro h
    exact QuotientGroup.lift_mk E (φ := φM24 c ρ) (by rw [φM24_ker]) h
  let θ : ↥M24g ≃* ↥M24g := e.symm.trans ((QuotientGroup.congr E E ψ hE).trans e)
  have θ_apply : ∀ h : ↥c.G1, θ (φM24 c ρ h) = φM24 c ρ (ψ h) := by
    intro h
    have h1 : (e.symm.trans ((QuotientGroup.congr E E ψ hE).trans e)) (e (QuotientGroup.mk h)) =
        φM24 c ρ (ψ h) := by
      have hcongr : (QuotientGroup.congr E E ψ hE) (QuotientGroup.mk h) =
          QuotientGroup.mk (ψ h) := QuotientGroup.congr_mk E E ψ hE h
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply, hcongr]
      exact e_mk (ψ h)
    show (e.symm.trans ((QuotientGroup.congr E E ψ hE).trans e)) (φM24 c ρ h) =
      φM24 c ρ (ψ h)
    rw [← e_mk h]
    exact h1
  obtain ⟨nbar, hnbar_mem, hnbar⟩ := M24G.exists_conj_eq_of_mulEquiv θ
  let nb : ↥M24g := ⟨nbar, hnbar_mem⟩
  have hnb_coe : (nb : S24) = nbar := rfl
  have hSconv : ∀ x : ↥M24g, x ∈ MulAction.stabilizer ↥M24g ρ.U₀ ↔
      ∃ h : ↥c.G1, (h : G) ∈ c.G3 ⊓ c.G1 ∧ φM24 c ρ h = x := by
    intro x
    rw [← map_G31_φM24 (c := c) (ρ := ρ), Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, hval⟩
      exact ⟨h, by rwa [Subgroup.mem_subgroupOf] at hh, hval⟩
    · rintro ⟨h, hh, hval⟩
      exact ⟨h, Subgroup.mem_subgroupOf.mpr hh, hval⟩
  have hSconj : ∀ x ∈ MulAction.stabilizer ↥M24g ρ.U₀,
      nb * x * nb⁻¹ ∈ MulAction.stabilizer ↥M24g ρ.U₀ := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := (hSconv x).mp hx
    have hψh : ((ψ h : ↥c.G1) : G) ∈ c.G3 ⊓ c.G1 := (hψ h).mp hh
    have heq : nb * φM24 c ρ h * nb⁻¹ = φM24 c ρ (ψ h) := by
      have h1 := hnbar (φM24 c ρ h)
      rw [θ_apply h] at h1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hnb_coe]
      exact h1.symm
    rw [heq]
    exact (hSconv _).mpr ⟨ψ h, hψh, rfl⟩
  have hNbar : nb ∈ Subgroup.normalizer
      (MulAction.stabilizer ↥M24g ρ.U₀ : Set ↥M24g) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      rw [Subgroup.mem_comap]
      show (MulAut.conj nb) y ∈ MulAction.stabilizer ↥M24g ρ.U₀
      rw [MulAut.conj_apply]
      exact hSconj y hy
    · exact (Subgroup.card_map_of_injective (f := (MulAut.conj nb).toMonoidHom)
        (by simpa only [MulEquiv.coe_toMonoidHom] using (MulAut.conj nb).injective)).symm.le
  have hfix : ∀ g ∈ M24g, g • ρ.U₀ = ρ.U₀ →
      g • ((nb : S24) • ρ.U₀) = (nb : S24) • ρ.U₀ := by
    intro g hg hgU
    have hgS : (⟨g, hg⟩ : ↥M24g) ∈ MulAction.stabilizer ↥M24g ρ.U₀ := by
      rw [MulAction.mem_stabilizer_iff]
      simpa only [Subgroup.smul_def] using hgU
    have hNbar' : nb⁻¹ ∈ Subgroup.normalizer
        (MulAction.stabilizer ↥M24g ρ.U₀ : Set ↥M24g) := Subgroup.inv_mem _ hNbar
    have hconj : nb⁻¹ * (⟨g, hg⟩ : ↥M24g) * nb ∈
        MulAction.stabilizer ↥M24g ρ.U₀ :=
      (Subgroup.mem_normalizer_iff.mp hNbar' (⟨g, hg⟩ : ↥M24g)).mp hgS
    have hnb : (nb : S24) • ρ.U₀ = (nb : ↥M24g) • ρ.U₀ :=
      (Subgroup.smul_def nb ρ.U₀).symm
    have hstep : g • ((nb : ↥M24g) • ρ.U₀) = ((⟨g, hg⟩ : ↥M24g) * nb) • ρ.U₀ := by
      rw [Subgroup.smul_def, Subgroup.smul_def, Subgroup.coe_mul, mul_smul]
    rw [hnb, hstep]
    have hdecomp : ((⟨g, hg⟩ : ↥M24g) * nb) =
        nb * (nb⁻¹ * (⟨g, hg⟩ : ↥M24g) * nb) := by group
    rw [hdecomp, mul_smul, MulAction.mem_stabilizer_iff.mp hconj]
  have hW : (nb : S24) • ρ.U₀ = ρ.U₀ := by
    have hseq : IsSextet ((nb : S24) • ρ.U₀) :=
      (M24G.isSextet_smul_iff (g := (nb : S24)) nb.2).mpr ρ.isSextet_U₀
    exact M24G.eq_of_forall_smul_sextet (U := ρ.U₀) (W := (nb : S24) • ρ.U₀)
      ρ.isSextet_U₀ hseq hfix
  have hnbS : nb ∈ MulAction.stabilizer ↥M24g ρ.U₀ := by
    rw [MulAction.mem_stabilizer_iff]
    exact hW
  obtain ⟨n, hn_mem, hn_eq⟩ := (hSconv nb).mp hnbS
  refine ⟨n, hn_mem, fun h => ?_⟩
  have h1 := hnbar (φM24 c ρ h)
  rw [θ_apply h] at h1
  have hnbar_eq : ((φM24 c ρ n : ↥M24g) : S24) = nbar := by rw [hn_eq]
  rw [← hnbar_eq] at h1
  simpa only [φM24_apply] using h1

theorem trans_mulAutConj (ψ : ↥c.G1 ≃* ↥c.G1) (i : ↥c.G1) :
    (MulAut.conj i).trans ψ = ψ.trans (MulAut.conj (ψ i)) := by
  ext x
  have h1 : (MulAut.conj i) x = i * x * i⁻¹ := MulAut.conj_apply i x
  show ((ψ ((MulAut.conj i) x) : ↥c.G1) : G) =
    (((MulAut.conj (ψ i)) (ψ x) : ↥c.G1) : G)
  rw [h1, map_mul, map_mul, map_inv, MulAut.conj_apply]

theorem autImage_conjSub_eq {M C : Subgroup G} (hM : M ≤ c.G1) (hMC : M = C)
    (ψ : ↥c.G1 ≃* ↥c.G1) (i j : ↥c.G1)
    (hKL : (C.subgroupOf c.G1).map ψ.toMonoidHom =
      (C.map (MulAut.conj (j : G)).toMonoidHom).subgroupOf c.G1) :
    autImage ψ (conjSub (i : G) M) = conjSub (((ψ i * j : ↥c.G1) : G)) M := by
  have hC : C ≤ c.G1 := hMC ▸ hM
  have hle : M.map (MulAut.conj (((ψ i * j : ↥c.G1) : G))).toMonoidHom ≤ c.G1 := by
    rw [hMC]
    exact (Subgroup.map_mono hC).trans
      (le_of_eq (c.map_conj_G1_of_mem (ψ i * j).2))
  have hsub : ((M.map (MulAut.conj (i : G)).toMonoidHom).subgroupOf c.G1) =
      (M.subgroupOf c.G1).map (MulAut.conj i).toMonoidHom :=
    c.map_subgroupOf_mulAutConj M hM i
  unfold autImage conjSub
  rw [hsub, show (M.map (MulAut.conj (((ψ i * j : ↥c.G1) : G))).toMonoidHom) =
      ((M.map (MulAut.conj (((ψ i * j : ↥c.G1) : G))).toMonoidHom).subgroupOf c.G1).map
        c.G1.subtype from (Subgroup.map_subgroupOf_eq_of_le hle).symm]
  refine (Subgroup.map_injective c.G1.subtype_injective).eq_iff.mpr ?_
  rw [hMC]
  rw [c.map_subgroupOf_mulAutConj C hC ((ψ i * j : ↥c.G1))]
  have h1 : ((C.subgroupOf c.G1).map (MulAut.conj i).toMonoidHom).map ψ.toMonoidHom =
      ((C.subgroupOf c.G1).map ψ.toMonoidHom).map (MulAut.conj (ψ i)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    exact congrArg (fun f : ↥c.G1 →* ↥c.G1 => (C.subgroupOf c.G1).map f)
      (MonoidHom.ext (fun x => by
        have h := congrArg (fun f : ↥c.G1 ≃* ↥c.G1 => f x) (c.trans_mulAutConj ψ i)
        simpa only [MonoidHom.comp_apply, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom]
          using h))
  rw [h1, hKL, c.map_subgroupOf_mulAutConj C hC j, Subgroup.map_map]
  exact congrArg (fun f : ↥c.G1 →* ↥c.G1 => (C.subgroupOf c.G1).map f)
    (MonoidHom.ext (fun x => by
      have h := congrArg (fun f : ↥c.G1 ≃* ↥c.G1 => f x) (c.mulAut_conj_mul (ψ i) j)
      simpa only [MonoidHom.comp_apply, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom] using h))

theorem image_M_y_of_mulEquiv
    (r : ResM24T c) (hP : FixOctPerfect) (hS : FixOctSym) (hW : FixOctCommW11)
    {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0)
    (ψ : ↥c.G1 ≃* ↥c.G1) (hψ : autPres c.G1 (c.G3 ⊓ c.G1) ψ) :
    ∃ j : ↥c.G1, (j : G) ∈ c.G3 ⊓ c.G1 ∧
      ((c.G1 ⊓ c.G2 ⊓ stabilizer G y).subgroupOf c.G1).map ψ.toMonoidHom =
        ((c.G1 ⊓ c.G2 ⊓ stabilizer G y).map
          (MulAut.conj (j : G)).toMonoidHom).subgroupOf c.G1 := by
  classical
  obtain ⟨n, hn_mem, hn_conj⟩ := c.exists_conj_φ_of_mulEquiv (ρ := r.toResM24) ψ hψ
  let ψ' : ↥c.G1 ≃* ↥c.G1 := ψ.trans (MulAut.conj (n⁻¹))
  have hψ'val : ∀ h : ↥c.G1, ψ' h = (n⁻¹ : ↥c.G1) * ψ h * n := by
    intro h
    apply Subtype.ext
    show (((MulAut.conj (n⁻¹)) (ψ h) : ↥c.G1) : G) =
      (((n⁻¹ : ↥c.G1) * ψ h * n : ↥c.G1) : G)
    rw [MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  have hψ'_comp : (φM24 c r.toResM24).comp ψ'.toMonoidHom = φM24 c r.toResM24 := by
    apply MonoidHom.ext
    intro h
    apply Subtype.ext
    change r.toResM24.φ (ψ' h) = r.toResM24.φ h
    rw [hψ'val h, map_mul, map_mul, map_inv, hn_conj h]
    group
  have hE := c.map_E_of_comp_eq (ρ := r.toResM24) ψ' hψ'_comp
  have hG12 := c.map_G12_of_comp_eq (ρ := r.toResM24) ψ' hψ'_comp
  have hpre := c.map_preFixOct_of_comp_eq (ρ := r.toResM24) ψ' hψ'_comp
  have hK := c.map_K_of_comp_eq r hP hS hW ψ' hψ'_comp
  let M : Subgroup G := c.G1 ⊓ c.G2 ⊓ stabilizer G y
  have hMle : M ≤ c.G1 := by
    show c.G1 ⊓ c.G2 ⊓ stabilizer G y ≤ c.G1
    exact (inf_le_left : c.G1 ⊓ c.G2 ⊓ stabilizer G y ≤ c.G1 ⊓ c.G2).trans inf_le_left
  have hMle12 : M ≤ c.G1 ⊓ c.G2 := by
    show c.G1 ⊓ c.G2 ⊓ stabilizer G y ≤ c.G1 ⊓ c.G2
    exact inf_le_left
  let MA : Subgroup ↥c.G1 := M.subgroupOf c.G1
  let UA : Subgroup ↥c.G1 := MA.map ψ'.toMonoidHom
  let U : Subgroup G := UA.map c.G1.subtype
  have hUle : U ≤ c.G1 ⊓ c.G2 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hwM : (w : G) ∈ M := Subgroup.mem_subgroupOf.mp hw
    have hw12 : (w : G) ∈ c.G1 ⊓ c.G2 := (Subgroup.mem_inf.mp hwM).1
    have hψw : ψ' w ∈ (c.G1 ⊓ c.G2).subgroupOf c.G1 := by
      rw [← hG12]
      exact Subgroup.mem_map.mpr ⟨w, Subgroup.mem_subgroupOf.mpr hw12, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hψw
  have hKU : c.K ≤ U := by
    intro k hk
    have hkG1 : k ∈ c.G1 := c.K_le_G1 hk
    let kA : ↥c.G1 := ⟨k, hkG1⟩
    have hkA : kA ∈ c.K.subgroupOf c.G1 := Subgroup.mem_subgroupOf.mpr hk
    have hkA' : kA ∈ (c.K.subgroupOf c.G1).map ψ'.toMonoidHom := by
      rw [hK]
      exact hkA
    obtain ⟨w, hw, hwval⟩ := Subgroup.mem_map.mp hkA'
    have hwM : w ∈ MA := by
      rw [Subgroup.mem_subgroupOf]
      exact c.K_le_G12_stab hy (Subgroup.mem_subgroupOf.mp hw)
    have hwval' : ψ' w = kA := by
      simpa only [MulEquiv.coe_toMonoidHom] using hwval
    have hwU : ψ' w ∈ UA := Subgroup.mem_map.mpr ⟨w, hwM, rfl⟩
    rw [hwval'] at hwU
    exact Subgroup.mem_map.mpr ⟨kA, hwU, rfl⟩
  have hcardU : Nat.card ↥U = Nat.card ↥M := by
    have h1 : Nat.card ↥U = Nat.card ↥UA :=
      Subgroup.card_map_of_injective (f := c.G1.subtype) c.G1.subtype_injective
    have h2 : Nat.card ↥UA = Nat.card ↥MA :=
      Subgroup.card_map_of_injective (f := ψ'.toMonoidHom)
        (by simpa only [MulEquiv.coe_toMonoidHom] using ψ'.injective)
    have h3 : Nat.card ↥MA = Nat.card ↥M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMle).toEquiv
    rw [h1, h2, h3]
  have hUrel : U.relIndex (c.G1 ⊓ c.G2) = 4 := by
    have hMrel : M.relIndex (c.G1 ⊓ c.G2) = 4 := c.relIndex_stab hy hyx
    have h1 := Subgroup.relIndex_mul_card U (c.G1 ⊓ c.G2)
    have h2 := Subgroup.relIndex_mul_card M (c.G1 ⊓ c.G2)
    rw [inf_eq_left.mpr hUle] at h1
    rw [inf_eq_left.mpr hMle12, hMrel] at h2
    rw [hcardU, ← h2] at h1
    exact Nat.mul_right_cancel (Nat.card_pos) h1
  obtain ⟨y', hy', hyx', hUeq⟩ := c.exists_eq_stab_of_relIndex_four hUle hKU hUrel
  obtain ⟨e, he, hey⟩ := c.E_transitive hy hy' hyx hyx'
  have hMe : M.map (MulAut.conj e).toMonoidHom = U := by
    have h := (c.conj_inf_stab he hy).1
    rw [hey] at h
    rw [h, hUeq]
  have hle_Me : M.map (MulAut.conj e).toMonoidHom ≤ c.G1 := by
    refine (Subgroup.map_mono (f := (MulAut.conj e).toMonoidHom) hMle).trans ?_
    rw [c.map_conj_G1_of_mem (c.E_le_G1 he)]
  have hMAψ' : MA.map ψ'.toMonoidHom =
      (M.map (MulAut.conj e).toMonoidHom).subgroupOf c.G1 := by
    apply Subgroup.map_injective c.G1.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle_Me, hMe]
  let eA : ↥c.G1 := ⟨e, c.E_le_G1 he⟩
  let j : ↥c.G1 := n * eA
  have hj_mem : (j : G) ∈ c.G3 ⊓ c.G1 := by
    refine Subgroup.mem_inf.mpr ⟨?_, j.2⟩
    change (n : G) * (eA : G) ∈ c.G3
    exact mul_mem (Subgroup.mem_inf.mp hn_mem).1 (c.E_le_G3 he)
  refine ⟨j, hj_mem, ?_⟩
  have hcomp : ψ.toMonoidHom = (MulAut.conj n).toMonoidHom.comp ψ'.toMonoidHom := by
    apply MonoidHom.ext
    intro h
    apply Subtype.ext
    rw [MonoidHom.comp_apply]
    show (ψ h : G) = (((MulAut.conj n) (ψ' h) : ↥c.G1) : G)
    rw [MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hv : (ψ' h : G) = (n : G)⁻¹ * (ψ h : G) * (n : G) := by
      rw [hψ'val h]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hv]
    group
  calc MA.map ψ.toMonoidHom
      = (MA.map ψ').map (MulAut.conj n).toMonoidHom := by
          rw [hcomp]
          exact (Subgroup.map_map MA (MulAut.conj n).toMonoidHom ψ'.toMonoidHom).symm
    _ = ((M.map (MulAut.conj e).toMonoidHom).subgroupOf c.G1).map
          (MulAut.conj n).toMonoidHom :=
          congrArg (fun K : Subgroup ↥c.G1 => K.map (MulAut.conj n).toMonoidHom) hMAψ'
    _ = (MA.map (MulAut.conj eA).toMonoidHom).map (MulAut.conj n).toMonoidHom :=
          congrArg (fun K : Subgroup ↥c.G1 => K.map (MulAut.conj n).toMonoidHom)
            (c.map_subgroupOf_mulAutConj M hMle eA)
    _ = MA.map (MulAut.conj (n * eA)).toMonoidHom := by
          rw [Subgroup.map_map, ← c.mulAut_conj_mul n eA]
          rfl
    _ = (M.map (MulAut.conj (j : G)).toMonoidHom).subgroupOf c.G1 :=
          (c.map_subgroupOf_mulAutConj M hMle j).symm

theorem autImage_conjSub_of_mulEquiv (hLU : Stmt5_LineU)
    (hJ : HypJ4 G z) (r : ResM24T c) (hP : FixOctPerfect) (hS : FixOctSym) (hW : FixOctCommW11)
    {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0)
    (ψ : ↥c.G1 ≃* ↥c.G1) (hψ : autPres c.G1 (c.G3 ⊓ c.G1) ψ) :
    (∀ i ∈ c.G3 ⊓ c.G1, ∃ j ∈ c.G3 ⊓ c.G1,
      autImage ψ (conjSub (i : G) (c.G1 ⊓ stabilizer G y)) =
        conjSub (j : G) (c.G1 ⊓ stabilizer G y)) ∧
    (∀ i ∈ c.G3 ⊓ c.G1, ∃ j ∈ c.G3 ⊓ c.G1,
      autImage ψ.symm (conjSub (i : G) (c.G1 ⊓ stabilizer G y)) =
        conjSub (j : G) (c.G1 ⊓ stabilizer G y)) := by
  have hMC : c.G1 ⊓ stabilizer G y = c.G1 ⊓ c.G2 ⊓ stabilizer G y :=
    c.inf_stab_eq_of_lineU (hLU G z hJ c y hy hyx)
  have hM : c.G1 ⊓ stabilizer G y ≤ c.G1 := inf_le_left
  have hψsym : autPres c.G1 (c.G3 ⊓ c.G1) ψ.symm := by
    intro a
    simpa using (hψ (ψ.symm a)).symm
  obtain ⟨j, hj, hKL⟩ := c.image_M_y_of_mulEquiv r hP hS hW hy hyx ψ hψ
  obtain ⟨j₂, hj₂, hKL₂⟩ := c.image_M_y_of_mulEquiv r hP hS hW hy hyx ψ.symm hψsym
  constructor
  · intro i hi
    let iA : ↥c.G1 := ⟨i, (Subgroup.mem_inf.mp hi).2⟩
    have hiB : (iA : G) ∈ c.G3 ⊓ c.G1 :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hi).1, iA.2⟩
    have hψi : ((ψ iA : ↥c.G1) : G) ∈ c.G3 ⊓ c.G1 := (hψ iA).mp hiB
    have hmem : ((ψ iA * j : ↥c.G1) : G) ∈ c.G3 ⊓ c.G1 := by
      rw [Subgroup.coe_mul]
      exact mul_mem hψi hj
    exact ⟨((ψ iA * j : ↥c.G1) : G), hmem,
      c.autImage_conjSub_eq hM hMC ψ iA j hKL⟩
  · intro i hi
    let iA : ↥c.G1 := ⟨i, (Subgroup.mem_inf.mp hi).2⟩
    have hiB : (iA : G) ∈ c.G3 ⊓ c.G1 :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hi).1, iA.2⟩
    have hψi : ((ψ.symm iA : ↥c.G1) : G) ∈ c.G3 ⊓ c.G1 := (hψsym iA).mp hiB
    have hmem : ((ψ.symm iA * j₂ : ↥c.G1) : G) ∈ c.G3 ⊓ c.G1 := by
      rw [Subgroup.coe_mul]
      exact mul_mem hψi hj₂
    exact ⟨((ψ.symm iA * j₂ : ↥c.G1) : G), hmem,
      c.autImage_conjSub_eq hM hMC ψ.symm iA j₂ hKL₂⟩

theorem hypV_v2 (hLU : Stmt5_LineU) {G : Type} [Group G] [Finite G] {z : G}
    (hJ : HypJ4 G z) (c : Loc49 G z) (r : ResM24T c) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL)
    (hyx : y ≠ c.x0) :
    ∀ ψ : ↥(stabilizer G c.x0) ≃* ↥(stabilizer G c.x0),
      autPres (stabilizer G c.x0) (c.G3 ⊓ stabilizer G c.x0) ψ →
      ∃ ψ₁ ψ₂ : ↥(stabilizer G c.x0) ≃* ↥(stabilizer G c.x0),
        (∀ i ∈ c.G3 ⊓ stabilizer G c.x0, ∃ j ∈ c.G3 ⊓ stabilizer G c.x0,
          autImage ψ₁ (conjSub i (stabilizer G c.x0 ⊓ stabilizer G y)) =
            conjSub j (stabilizer G c.x0 ⊓ stabilizer G y)) ∧
        (∀ i ∈ c.G3 ⊓ stabilizer G c.x0, ∃ j ∈ c.G3 ⊓ stabilizer G c.x0,
          autImage ψ₁.symm (conjSub i (stabilizer G c.x0 ⊓ stabilizer G y)) =
            conjSub j (stabilizer G c.x0 ⊓ stabilizer G y)) ∧
        autFix (stabilizer G c.x0) (c.G3 ⊓ stabilizer G c.x0) ψ₂ ∧
        ∀ g : ↥(stabilizer G c.x0), ((ψ g : ↥(stabilizer G c.x0)) : G) = ψ₁ (ψ₂ g) := by
  have hP : FixOctPerfect := fixOctPerfect_holds
  have hS : FixOctSym := fixOctSym_holds
  have hW : FixOctCommW11 := fixOctCommW11_holds
  intro ψ hψ
  let e : ↥(stabilizer G c.x0) ≃* ↥c.G1 := MulEquiv.subgroupCongr c.stab_x0
  let ψg : ↥c.G1 ≃* ↥c.G1 := e.symm.trans (ψ.trans e)
  have hB : (c.G3 ⊓ stabilizer G c.x0) = (c.G3 ⊓ c.G1) := by
    rw [c.stab_x0]
  have hψ' : autPres (stabilizer G c.x0) (c.G3 ⊓ c.G1) ψ :=
    (autPres_congr hB ψ).mp hψ
  have hψg : autPres c.G1 (c.G3 ⊓ c.G1) ψg :=
    (autPres_subgroupCongr c.stab_x0 (c.G3 ⊓ c.G1) ψ).mpr hψ'
  obtain ⟨h1, h2⟩ := c.autImage_conjSub_of_mulEquiv hLU hJ r hP hS hW hy hyx ψg hψg
  refine ⟨ψ, MulEquiv.refl _, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hiM : i ∈ stabilizer G c.x0 := (Subgroup.mem_inf.mp hi).2
    let iA : ↥c.G1 := e ⟨i, hiM⟩
    have hiA_val : (iA : G) = i := by
      show ((e ⟨i, hiM⟩ : ↥c.G1) : G) = i
      exact MulEquiv.subgroupCongr_apply c.stab_x0 ⟨i, hiM⟩
    have hiA_mem : (iA : G) ∈ c.G3 ⊓ c.G1 := by
      rw [hiA_val]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hi).1, c.stab_x0 ▸ hiM⟩
    obtain ⟨j, hj, hjeq⟩ := h1 iA hiA_mem
    refine ⟨j, ?_, ?_⟩
    · exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hj).1,
        c.stab_x0.symm ▸ (Subgroup.mem_inf.mp hj).2⟩
    · rw [show (stabilizer G c.x0 ⊓ stabilizer G y) = c.G1 ⊓ stabilizer G y from by
          rw [c.stab_x0],
        ← autImage_subgroupCongr c.stab_x0 ψ (conjSub i (c.G1 ⊓ stabilizer G y)),
        ← hiA_val]
      exact hjeq
  · intro i hi
    have hiM : i ∈ stabilizer G c.x0 := (Subgroup.mem_inf.mp hi).2
    let iA : ↥c.G1 := e ⟨i, hiM⟩
    have hiA_val : (iA : G) = i := by
      show ((e ⟨i, hiM⟩ : ↥c.G1) : G) = i
      exact MulEquiv.subgroupCongr_apply c.stab_x0 ⟨i, hiM⟩
    have hiA_mem : (iA : G) ∈ c.G3 ⊓ c.G1 := by
      rw [hiA_val]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hi).1, c.stab_x0 ▸ hiM⟩
    obtain ⟨j, hj, hjeq⟩ := h2 iA hiA_mem
    refine ⟨j, ?_, ?_⟩
    · exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hj).1,
        c.stab_x0.symm ▸ (Subgroup.mem_inf.mp hj).2⟩
    · rw [show (stabilizer G c.x0 ⊓ stabilizer G y) = c.G1 ⊓ stabilizer G y from by
          rw [c.stab_x0],
        ← autImage_subgroupCongr c.stab_x0 ψ.symm (conjSub i (c.G1 ⊓ stabilizer G y)),
        ← hiA_val]
      exact hjeq
  · intro a _
    rfl
  · intro g
    rfl

end Loc49

end CFSG.Quasithin.H13.AS91
