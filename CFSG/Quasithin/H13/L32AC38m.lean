module

public import CFSG.Quasithin.H13.L32AC38l
public import CFSG.Quasithin.H13.L32AC38j
public import CFSG.Quasithin.Background.C124YZActOdd
public import CFSG.Quasithin.H13.L32AC37d
public import CFSG.Quasithin.H13.L32AC38f

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem exists_perm_hom (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H))
    {K₁ : Subgroup (MulAut (IntMod C.Wt C.hUe))} (hrK : C.ψ.range = K₁) {n : ℕ}
    {π₀ : Equiv.Perm (Fin n) →* ↥K₁} (hπ₀i : Function.Injective π₀)
    (hπ₀s : Function.Surjective π₀) :
    ∃ φ : ↥H →* Equiv.Perm (Fin n), Function.Surjective φ ∧
      (∀ h : ↥H, φ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
      ∀ h : ↥H, ((π₀ (φ h) : ↥K₁) : MulAut (IntMod C.Wt C.hUe)) = C.ψ h := by
  let θ := MulEquiv.ofBijective π₀ ⟨hπ₀i, hπ₀s⟩
  have hψ1 : ∀ h : ↥H, C.ψ h ∈ K₁ := fun h => hrK ▸ ⟨h, rfl⟩
  let ψ₁ : ↥H →* ↥K₁ := C.ψ.codRestrict K₁ hψ1
  have hθ : ∀ h : ↥H, π₀ (θ.symm (ψ₁ h)) = ψ₁ h := fun h => θ.apply_symm_apply _
  refine ⟨θ.symm.toMonoidHom.comp ψ₁, ?_, fun h => ?_, fun h => congrArg Subtype.val (hθ h)⟩
  · intro σ
    obtain ⟨h, hh⟩ : (θ σ : MulAut (IntMod C.Wt C.hUe)) ∈ C.ψ.range := hrK ▸ (θ σ).2
    refine ⟨h, ?_⟩
    show θ.symm (ψ₁ h) = σ
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hh
  · show θ.symm (ψ₁ h) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    constructor
    · intro h1
      exact C.mem_pCoreOf_of_ψ hW h.2 (by
        have := congrArg Subtype.val h1
        exact this)
    · intro h1
      exact Subtype.ext (C.ψ_eq_one_of_mem h1)

theorem false_of_perm_six (h11 : Lemma14_7_11)
    (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H))
    {K₁ : Subgroup (MulAut (IntMod C.Wt C.hUe))} (hrK : C.ψ.range = K₁)
    {π₀ : Equiv.Perm (Fin 6) →* ↥K₁} (hπ₀i : Function.Injective π₀)
    (hπ₀s : Function.Surjective π₀) : False := by
  obtain ⟨φ, hφs, hφk, -⟩ := C.exists_perm_hom hW hrK hπ₀i hπ₀s
  refine (h11 G T L V H C.S).2.2 ⟨φ, hφs, ?_⟩
  ext h
  rw [MonoidHom.mem_ker, hφk]
  exact Subgroup.mem_map_iff_mem H.subtype_injective

theorem false_of_perm_seven (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h2 : Lemma14_7_2) (h4 : Lemma14_7_4_two_three)
    (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H))
    {K₁ : Subgroup (MulAut (IntMod C.Wt C.hUe))} (hrK : C.ψ.range = K₁)
    {π₀ : Equiv.Perm (Fin 7) →* ↥K₁}
    (hπ : (FFModel.symDn 7).RealizesVia K₁ ⊤ ⊥ π₀) : False := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have hπ₀i : Function.Injective π₀ :=
    FFModel.RealizesVia.injective_of_faithful (G64.symDn_faithful (by norm_num)) hπ
  obtain ⟨φ, hφs, hφk, hφψ⟩ := C.exists_perm_hom hW hrK hπ₀i hπ.1
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv (C124.YZ.natKer_odd (by decide)) hπ
  let β : ↥(conjClosure V H) →* ↥(G6.coreMod 7) := E.toMonoidHom.comp (C.tildeHom hW)
  refine not_isS7NaturalSection h1222 h1332 h1334 h2 h4 C.S hV2
    ⟨le_normalizer_conjClosure V H, φ, β, hφs, ?_, ?_, ?_, ?_⟩
  · ext h
    rw [MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  · exact E.surjective.comp (C.tildeHom_surjective hW)
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← C.tildeHom_eq_one_iff hW]
    show E (C.tildeHom hW u) = 1 ↔ _
    exact MulEquiv.map_eq_one_iff E
  · intro h x x' hx'
    apply Subtype.ext
    show (E (C.tildeHom hW x')).1 = G6.permAct 7 (φ h) (E (C.tildeHom hW x)).1
    rw [C.tildeHom_conj hW h x x' hx', ← hφψ h]
    exact hE (φ h) _

theorem false_of_perm_eight (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h4 : Lemma14_7_4_two_three) (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H))
    {K₁ : Subgroup (MulAut (IntMod C.Wt C.hUe))} (hrK : C.ψ.range = K₁)
    {Z : Subgroup (G6.PermMod 8)} {π₀ : Equiv.Perm (Fin 8) →* ↥K₁}
    (hπ₀i : Function.Injective π₀) (hπ : (G64.permModel 8 Z).RealizesVia K₁ ⊤ ⊥ π₀) :
    False := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨-, a, -, -, -, ha, haV, -, -⟩ := S14.exists_basis
  obtain ⟨e, he⟩ := G64.RealizesVia.exists_modEquiv hπ
  set w₀ : IntMod C.Wt C.hUe :=
    IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW (le_conjClosure V H (hV2.2.1 ha))⟩ with hw₀
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e w₀)
  obtain ⟨p, q, r, d, f, g, hpq, hpr, hqr, hdf, hdg, hfg, hd, hf, hg, h1, h2, h3, h4'⟩ :=
    exists_two_triples (le_refl 8) (Multiplicative.toAdd (m.1 : G6.PermMod 8))
  set γ₁ : Equiv.Perm (Fin 8) := Equiv.swap p q * Equiv.swap q r with hγ₁
  set γ₂ : Equiv.Perm (Fin 8) := Equiv.swap d f * Equiv.swap f g with hγ₂
  have hfix : ∀ γ : Equiv.Perm (Fin 8), G6.permAct 8 γ (m.1 : G6.PermMod 8) = m.1 →
      ((π₀ γ : ↥K₁) : MulAut (IntMod C.Wt C.hUe)) w₀ = w₀ := by
    intro γ hγ
    have hmem : G6.permAct 8 γ (m.1 : G6.PermMod 8) ∈ G6.coreMod 8 := by rw [hγ]; exact m.2
    have h5 := he γ w₀ m hmem hm.symm
    apply e.injective
    refine h5.trans ?_
    rw [← hm]
    congr 1
    exact Subtype.ext hγ
  have hf₁ := hfix γ₁ (permAct_cyc3_fix hpq hpr hqr _ h1 h2)
  have hf₂ := hfix γ₂ (permAct_cyc3_fix hdf hdg hfg _ h3 h4')
  have hmemR : ∀ γ : Equiv.Perm (Fin 8),
      ((π₀ γ : ↥K₁) : MulAut (IntMod C.Wt C.hUe)) ∈ C.ψ.range := fun γ => hrK ▸ (π₀ γ).2
  have hpow : ∀ (γ : Equiv.Perm (Fin 8)) (k : ℕ),
      ((π₀ γ : ↥K₁) : MulAut (IntMod C.Wt C.hUe)) ^ k = ((π₀ (γ ^ k) : ↥K₁) : MulAut _) := by
    intro γ k
    rw [map_pow, Subgroup.coe_pow]
  refine C.false_of_e9_fix h1222 h1332 h1334 h4 hV2 hW (hmemR γ₁) (hmemR γ₂) ?_ ?_ ?_ ?_
    ha haV hf₁ hf₂
  · rw [hpow, S153EB6.cyc3_pow hpq hpr hqr, map_one, Subgroup.coe_one]
  · rw [hpow, S153EB6.cyc3_pow hdf hdg hfg, map_one, Subgroup.coe_one]
  · have := (cyc3_commute hd hf hg).eq
    show _ * _ = _ * _
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, this]
  · intro i j hij
    apply cyc3_indep hpq hpr hqr hdf hdg hfg hd hf hg i j
    apply hπ₀i
    rw [map_mul, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← hpow, ← hpow]
    exact hij

end Ctx38

end CFSG.Quasithin.H13.L32A.C
