module

public import CFSG.Quasithin.Recognition.J2RecFrame
public import CFSG.Quasithin.Recognition.J2RecInvol
public import CFSG.Quasithin.Recognition.J2RecSplit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM
open scoped Pointwise

theorem J2Cz.QM.twist_x2x3 : x 2 * x 3 * phiAHom (x 2 * x 3)⁻¹ = z := by decide +kernel

namespace IsTypeH2

variable {G : Type} [Group G] {z : G}

theorem exists_sylow_le_centralizer [Finite G] (h : IsTypeH2 G z) :
    ∃ P : Sylow 2 G, (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G) with hC
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥C))
  set S := (S₀ : Subgroup ↥C).map C.subtype with hS
  have hSsub : S.subgroupOf C = S₀ := by
    rw [hS, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  have hSC : IsSylowTwoOf S C :=
    ⟨Subgroup.map_subtype_le _, S₀.isPGroup'.map _, by rw [hSsub]; exact S₀.not_dvd_index⟩
  obtain ⟨-, hS2, hSidx⟩ := h.isSylowTwoOf_top hSC
  have hSidx' : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hSidx
  exact ⟨hS2.toSylow hSidx', by rw [IsPGroup.toSylow_coe]; exact hSC.1⟩

theorem exists_mem_centralizer_not_isConj [Finite G] (h : IsTypeH2 G z)
    (hcount : involutionClassCount G = 2) :
    ∃ s ∈ Subgroup.centralizer ({z} : Set G), s * s = 1 ∧ s ≠ 1 ∧ ¬ IsConj z s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs2, hs1, hsz⟩ := h.exists_not_isConj hcount
  obtain ⟨P, hPH⟩ := h.exists_sylow_le_centralizer
  have hsp : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hs2 hs1, pow_one])
  obtain ⟨T, hT⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T P
  have h1 : MulAut.conj g s ∈ MulAut.conj g • (T : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hT (Subgroup.mem_zpowers s))
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  have hgs : g * s * g⁻¹ ∈ (P : Subgroup G) := by simpa [MulAut.conj_apply] using h1
  have hss : s * s = 1 := by rwa [pow_two] at hs2
  refine ⟨g * s * g⁻¹, hPH hgs, ?_, ?_, fun h2 => hsz (h2.trans ?_)⟩
  · calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hss]; group
  · intro h3
    apply hs1
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  · exact isConj_iff.mpr ⟨g⁻¹, by group⟩

end IsTypeH2

namespace J2Frame

variable {G : Type} [Group G] {z : G} (F : J2Frame G z)

theorem exists_conj_czAct_eq_phiA {y : ↥(Subgroup.centralizer ({z} : Set G))} (hy2 : y * y = 1)
    (hyQ : (y : G) ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :
    ∃ g : ↥(Subgroup.centralizer ({z} : Set G)), IsTypeH2.czAct F.χ (g * y * g⁻¹) = phiA := by
  set θ : alternatingGroup (Fin 5) →* MulAut QM := L0.subtype.comp lineEquiv.symm.toMonoidHom
    with hθ
  have hθperm : ∀ σ, linePerm (θ σ) = σ := linePerm_lineEquiv_symm
  set σ : alternatingGroup (Fin 5) :=
    ⟨linePerm (IsTypeH2.czAct F.χ y), F.isTypeH2.linePerm_czAct_mem F.χ y⟩ with hσ
  have h1 : linePerm (IsTypeH2.czAct F.χ y * (θ σ)⁻¹) = 1 := by
    show linePermHom (IsTypeH2.czAct F.χ y * (θ σ)⁻¹) = 1
    rw [map_mul, map_inv]
    show linePerm (IsTypeH2.czAct F.χ y) * (linePerm (θ σ))⁻¹ = 1
    rw [hθperm, hσ]
    exact mul_inv_cancel _
  obtain ⟨p, hp⟩ := eq_conj_of_linePerm_eq_one h1
  have hψy : IsTypeH2.czAct F.χ y = MulAut.conj p * θ σ := by
    rw [← hp]
    group
  have hσ1 : (σ : Perm (Fin 5)) ≠ 1 := fun h2 =>
    hyQ (F.isTypeH2.mem_pCoreOf_of_linePerm_eq_one F.χ h2)
  have hσ2 : (σ : Perm (Fin 5)) * σ = 1 := by
    have h2 := congrArg (fun g => linePermHom (IsTypeH2.czAct F.χ g)) hy2
    simp only [map_mul, map_one] at h2
    exact h2
  obtain ⟨π, hπ, hπσ⟩ := exists_conj_pa σ (Perm.mem_alternatingGroup.mp σ.2) hσ2 hσ1
  set πA : alternatingGroup (Fin 5) := ⟨π, Perm.mem_alternatingGroup.mpr hπ⟩ with hπA
  set gπ : ↥(Subgroup.centralizer ({z} : Set G)) := ⟨F.ι πA, F.ι_mem_centralizer πA⟩ with hgπ'
  have hgπ : IsTypeH2.czAct F.χ gπ = θ πA := F.czAct_ι πA _
  set p₁ := θ πA p with hp₁
  have hpa : πA * σ * πA⁻¹ = ⟨pa, pa_mem⟩ := Subtype.ext hπσ
  have hψt₁ : IsTypeH2.czAct F.χ (gπ * y * gπ⁻¹) = MulAut.conj p₁ * phiA := by
    rw [map_mul, map_mul, map_inv, hgπ, hψy, ← lineEquiv_symm_pa]
    have e1 : θ πA * (MulAut.conj p * θ σ) * (θ πA)⁻¹ =
        (θ πA * MulAut.conj p * (θ πA)⁻¹) * (θ πA * θ σ * (θ πA)⁻¹) := by group
    rw [e1, mul_conj_mul_inv, ← map_inv, ← map_mul, ← map_mul, hpa]
    rfl
  have ht₁2 : (gπ * y * gπ⁻¹) * (gπ * y * gπ⁻¹) = 1 := by
    calc (gπ * y * gπ⁻¹) * (gπ * y * gπ⁻¹) = gπ * (y * y) * gπ⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hphiA2 : phiA * phiA = 1 := MulEquiv.ext fun q => phiAHom_phiAHom q
  have hcen : p₁ * phiAHom p₁ = 1 ∨ p₁ * phiAHom p₁ = J2Cz.QM.z := by
    apply central_of_conj_eq_one
    have h2 := congrArg (IsTypeH2.czAct F.χ) ht₁2
    rw [map_mul, hψt₁, map_one] at h2
    have e2 : MulAut.conj p₁ * phiA * (MulAut.conj p₁ * phiA) =
        MulAut.conj p₁ * (phiA * MulAut.conj p₁ * phiA⁻¹) * (phiA * phiA) := by group
    rw [e2, mul_conj_mul_inv, hphiA2, mul_one, ← map_mul] at h2
    exact h2
  obtain ⟨r, hr⟩ := exists_twist p₁ hcen
  obtain ⟨n, -, hn⟩ := IsTypeH2.exists_czAct_eq_conj F.χ r
  refine ⟨n * gπ, ?_⟩
  have e0 : n * gπ * y * (n * gπ)⁻¹ = n * (gπ * y * gπ⁻¹) * n⁻¹ := by group
  rw [e0, map_mul, map_mul, map_inv, hn, hψt₁]
  have e3 : MulAut.conj r * (MulAut.conj p₁ * phiA) * (MulAut.conj r)⁻¹ =
      MulAut.conj r * MulAut.conj p₁ * (phiA * (MulAut.conj r)⁻¹ * phiA⁻¹) * phiA := by group
  rw [e3, ← map_inv, mul_conj_mul_inv, ← map_mul, ← map_mul]
  have e4 : r * p₁ * phiA r⁻¹ = r * p₁ * (phiAHom r)⁻¹ := by
    rw [map_inv]
    rfl
  rw [e4, conj_eq_one_of_central hr, one_mul]

theorem exists_mem_Q_conj_t :
    ∃ n ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), n * F.t * n⁻¹ = z * F.t := by
  refine ⟨F.emb (x 2 * x 3), F.emb_mem _, ?_⟩
  have h1 := F.conj_emb ⟨F.t, F.t_mem_centralizer⟩ (x 2 * x 3)⁻¹
  rw [F.czAct_t] at h1
  have h2 : F.t * F.emb (x 2 * x 3)⁻¹ * F.t⁻¹ = F.emb (phiAHom (x 2 * x 3)⁻¹) := h1
  calc F.emb (x 2 * x 3) * F.t * (F.emb (x 2 * x 3))⁻¹ =
        F.emb (x 2 * x 3) * (F.t * F.emb (x 2 * x 3)⁻¹ * F.t⁻¹) * F.t := by
          rw [map_inv]; group
    _ = F.emb (x 2 * x 3 * phiAHom (x 2 * x 3)⁻¹) * F.t := by rw [h2, ← map_mul]
    _ = z * F.t := by rw [twist_x2x3, F.emb_z]

theorem exists_conj_eq_t {y : G} (hyH : y ∈ Subgroup.centralizer ({z} : Set G))
    (hy2 : y * y = 1) (hyQ : y ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :
    ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * y * g⁻¹ = F.t := by
  obtain ⟨g, hg⟩ := F.exists_conj_czAct_eq_phiA (y := ⟨y, hyH⟩) (Subtype.ext hy2) hyQ
  have h1 : IsTypeH2.czAct F.χ (g * ⟨y, hyH⟩ * g⁻¹ * (⟨F.t, F.t_mem_centralizer⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, hg, F.czAct_t, mul_inv_cancel]
  have hu : (g : G) * y * (g : G)⁻¹ * F.t⁻¹ = 1 ∨ (g : G) * y * (g : G)⁻¹ * F.t⁻¹ = z :=
    F.isTypeH2.eq_one_or_eq_of_czAct_eq_one F.χ h1
  rcases hu with hu | hu
  · refine ⟨g, g.2, ?_⟩
    calc (g : G) * y * (g : G)⁻¹ = (g : G) * y * (g : G)⁻¹ * F.t⁻¹ * F.t := by group
      _ = F.t := by rw [hu, one_mul]
  · obtain ⟨n, hnQ, hn⟩ := F.exists_mem_Q_conj_t
    have hnH := pCoreOf_le 2 _ hnQ
    refine ⟨n⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ hnH) g.2, ?_⟩
    have h2 : (g : G) * y * (g : G)⁻¹ = z * F.t := by
      calc (g : G) * y * (g : G)⁻¹ = (g : G) * y * (g : G)⁻¹ * F.t⁻¹ * F.t := by group
        _ = z * F.t := by rw [hu]
    calc n⁻¹ * g * y * (n⁻¹ * g)⁻¹ = n⁻¹ * ((g : G) * y * (g : G)⁻¹) * n := by group
      _ = n⁻¹ * (n * F.t * n⁻¹) * n := by rw [h2, hn]
      _ = F.t := by group

theorem isConj_of_mem_W {w : G} (hw : w ∈ F.W) (hw1 : w ≠ 1) : IsConj z w :=
  F.isTypeH2.isConj_of_mem_pCoreOf hw.2 (F.mul_self_of_mem_W hw) hw1

theorem exists_conj_eq_t_of_mem_T {g : G} (hg : g ∈ F.T) (hgW : g ∉ F.W) :
    ∃ k ∈ Subgroup.centralizer ({z} : Set G), k * g * k⁻¹ = F.t :=
  F.exists_conj_eq_t hg.2 (F.mul_self_of_mem_T hg) fun hQ => hgW ⟨hg.1, hQ⟩

theorem isPGroup_T : IsPGroup 2 F.T := by
  refine IsPGroup.iff_orderOf.mpr fun g => ?_
  have h1 : orderOf g ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
    rw [pow_one, pow_two]
    exact F.mul_self_of_mem_T g.2))
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact ⟨k, hk⟩

variable [Finite G]

theorem not_isConj_t (hcount : involutionClassCount G = 2) : ¬ IsConj z F.t := by
  obtain ⟨s, hsH, hs2, hs1, hsz⟩ := F.isTypeH2.exists_mem_centralizer_not_isConj hcount
  have hsQ : s ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := fun hQ =>
    hsz (F.isTypeH2.isConj_of_mem_pCoreOf hQ hs2 hs1)
  obtain ⟨g, -, hg⟩ := F.exists_conj_eq_t hsH hs2 hsQ
  intro hzt
  exact hsz (hzt.trans (isConj_iff.mpr ⟨g⁻¹, by rw [← hg]; group⟩))

theorem isConj_z_or_t (hcount : involutionClassCount G = 2) {y : G} (hy2 : y * y = 1)
    (hy1 : y ≠ 1) : IsConj z y ∨ IsConj F.t y := by
  by_contra hne
  push Not at hne
  obtain ⟨hzy, hty⟩ := hne
  set S := {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧ ConjClasses.mk x = c} with hS
  have hsub : ({ConjClasses.mk z, ConjClasses.mk F.t, ConjClasses.mk y} : Set (ConjClasses G)) ⊆
      S := by
    intro c hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨z, F.isTypeH2.sq, F.isTypeH2.ne_one, rfl⟩
    · exact ⟨F.t, by rw [pow_two]; exact F.t_mul_t, F.t_ne_one, rfl⟩
    · exact ⟨y, by rw [pow_two]; exact hy2, hy1, rfl⟩
  have h3 : ({ConjClasses.mk z, ConjClasses.mk F.t, ConjClasses.mk y} :
      Set (ConjClasses G)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    · exact fun h1 => F.not_isConj_t hcount (ConjClasses.mk_eq_mk_iff_isConj.mp h1)
    · exact fun h1 => hzy (ConjClasses.mk_eq_mk_iff_isConj.mp h1)
    · exact fun h1 => hty (ConjClasses.mk_eq_mk_iff_isConj.mp h1)
  have h4 := Set.ncard_le_ncard hsub (Set.toFinite S)
  rw [h3] at h4
  have h5 : S.ncard = 2 := hcount
  omega

theorem not_isConj_of_mem_T (hcount : involutionClassCount G = 2) {g : G} (hg : g ∈ F.T)
    (hgW : g ∉ F.W) : ¬ IsConj z g := by
  obtain ⟨k, -, hk⟩ := F.exists_conj_eq_t_of_mem_T hg hgW
  exact fun h1 => F.not_isConj_t hcount (h1.trans (isConj_iff.mpr ⟨k, hk⟩))

theorem mem_W_of_conj (hcount : involutionClassCount G = 2) {w g : G} (hw : w ∈ F.W)
    (hg : g * w * g⁻¹ ∈ F.T) : g * w * g⁻¹ ∈ F.W := by
  by_cases hw1 : w = 1
  · rw [hw1, mul_one, mul_inv_cancel]
    exact one_mem _
  by_contra hW
  exact F.not_isConj_of_mem_T hcount hg hW
    ((F.isConj_of_mem_W hw hw1).trans (isConj_iff.mpr ⟨g, rfl⟩))

theorem eq_T_of_isPGroup (hcount : involutionClassCount G = 2) {R : Subgroup G}
    (hR : IsPGroup 2 R) (hRX : R ≤ F.X) (hTR : F.T ≤ R) : R = F.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPH⟩ := F.isTypeH2.exists_sylow_le_centralizer
  obtain ⟨P', hRP'⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' P
  have hconj : ∀ r ∈ R, g * r * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    intro r hr
    have h1 : MulAut.conj g r ∈ MulAut.conj g • (P' : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hRP' hr)
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact hPH (by simpa [MulAut.conj_apply] using h1)
  have htR : F.t ∈ R := hTR F.t_mem_T
  have ht'H := hconj F.t htR
  have ht'2 : g * F.t * g⁻¹ * (g * F.t * g⁻¹) = 1 := by
    calc g * F.t * g⁻¹ * (g * F.t * g⁻¹) = g * (F.t * F.t) * g⁻¹ := by group
      _ = 1 := by rw [F.t_mul_t]; group
  have ht'Q : g * F.t * g⁻¹ ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
    intro hQ
    have ht'1 : g * F.t * g⁻¹ ≠ 1 := fun h1 => F.t_ne_one (by
      calc F.t = g⁻¹ * (g * F.t * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
    exact F.not_isConj_t hcount ((F.isTypeH2.isConj_of_mem_pCoreOf hQ ht'2 ht'1).trans
      (isConj_iff.mpr ⟨g⁻¹, by group⟩))
  obtain ⟨k, hkH, hk⟩ := F.exists_conj_eq_t ht'H ht'2 ht'Q
  set m := k * g with hm
  have hmT : ∀ r ∈ R, m * r * m⁻¹ ∈ F.T := by
    intro r hr
    refine ⟨F.mem_X.mpr ?_, ?_⟩
    · have hrt : r * F.t = F.t * r := F.mem_X.mp (hRX hr)
      have hmt : m * F.t * m⁻¹ = F.t := by
        calc m * F.t * m⁻¹ = k * (g * F.t * g⁻¹) * k⁻¹ := by rw [hm]; group
          _ = F.t := hk
      calc m * r * m⁻¹ * F.t = m * r * m⁻¹ * (m * F.t * m⁻¹) := by rw [hmt]
        _ = m * (r * F.t) * m⁻¹ := by group
        _ = m * (F.t * r) * m⁻¹ := by rw [hrt]
        _ = m * F.t * m⁻¹ * (m * r * m⁻¹) := by group
        _ = F.t * (m * r * m⁻¹) := by rw [hmt]
    · have e1 : m * r * m⁻¹ = k * (g * r * g⁻¹) * k⁻¹ := by rw [hm]; group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkH (hconj r hr)) (Subgroup.inv_mem _ hkH)
  have hle : R.map (MulAut.conj m).toMonoidHom ≤ F.T := by
    rintro _ ⟨r, hr, rfl⟩
    exact hmT r hr
  have hcard : Nat.card R ≤ Nat.card F.T := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj m).toMonoidHom)
      (MulAut.conj m).injective]
    exact Subgroup.card_le_of_le hle
  exact (Subgroup.eq_of_le_of_card_ge hTR hcard).symm

@[expose] noncomputable def sylowT (hcount : involutionClassCount G = 2) : Sylow 2 ↥F.X where
  toSubgroup := F.T.subgroupOf F.X
  isPGroup' := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact F.isPGroup_T.of_equiv (Subgroup.subgroupOfEquivOfLe F.T_le_X).symm
  is_maximal' := by
    intro R hR hTR
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : R.map F.X.subtype = F.T := by
      refine F.eq_T_of_isPGroup hcount (hR.map _) (Subgroup.map_subtype_le _) fun g hg => ?_
      exact ⟨⟨g, F.T_le_X hg⟩, hTR (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
    ext g
    constructor
    · intro hg
      have : (g : G) ∈ R.map F.X.subtype := ⟨g, hg, rfl⟩
      rw [h1] at this
      exact Subgroup.mem_subgroupOf.mpr this
    · intro hg
      have : (g : G) ∈ R.map F.X.subtype := by rw [h1]; exact Subgroup.mem_subgroupOf.mp hg
      obtain ⟨g', hg', hgg'⟩ := this
      rwa [← Subtype.ext hgg']

theorem coe_sylowT (hcount : involutionClassCount G = 2) :
    ((F.sylowT hcount : Subgroup ↥F.X)) = F.T.subgroupOf F.X :=
  rfl

theorem exists_mem_X_conj_eq (hcount : involutionClassCount G = 2) {w : G} (hw : w ∈ F.W)
    (hw1 : w ≠ 1) : ∃ u ∈ F.X, u * z * u⁻¹ = w := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (F.isConj_of_mem_W hw hw1)
  set t' := g⁻¹ * F.t * g with ht'
  have hwt : w * F.t = F.t * w := F.mem_X.mp hw.1
  have ht'H : t' ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : z = g⁻¹ * w * g := by rw [← hg]; group
    rw [e1, ht']
    calc g⁻¹ * F.t * g * (g⁻¹ * w * g) = g⁻¹ * (F.t * w) * g := by group
      _ = g⁻¹ * (w * F.t) * g := by rw [hwt]
      _ = g⁻¹ * w * g * (g⁻¹ * F.t * g) := by group
  have ht'2 : t' * t' = 1 := by
    rw [ht']
    calc g⁻¹ * F.t * g * (g⁻¹ * F.t * g) = g⁻¹ * (F.t * F.t) * g := by group
      _ = 1 := by rw [F.t_mul_t]; group
  have ht'Q : t' ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
    intro hQ
    have ht'1 : t' ≠ 1 := fun h1 => F.t_ne_one (by
      calc F.t = g * t' * g⁻¹ := by rw [ht']; group
        _ = 1 := by rw [h1]; group)
    exact F.not_isConj_t hcount ((F.isTypeH2.isConj_of_mem_pCoreOf hQ ht'2 ht'1).trans
      (isConj_iff.mpr ⟨g, by rw [ht']; group⟩))
  obtain ⟨k, hkH, hk⟩ := F.exists_conj_eq_t ht'H ht'2 ht'Q
  refine ⟨g * k⁻¹, F.mem_X.mpr ?_, ?_⟩
  · have e2 : F.t = g * t' * g⁻¹ := by rw [ht']; group
    have e3 : t' = k⁻¹ * F.t * k := by rw [← hk]; group
    calc g * k⁻¹ * F.t = g * (k⁻¹ * F.t * k) * g⁻¹ * (g * k⁻¹) := by group
      _ = g * t' * g⁻¹ * (g * k⁻¹) := by rw [← e3]
      _ = F.t * (g * k⁻¹) := by rw [← e2]
  · have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hkH
    calc g * k⁻¹ * z * (g * k⁻¹)⁻¹ = g * (k⁻¹ * (z * k)) * g⁻¹ := by group
      _ = g * (k⁻¹ * (k * z)) * g⁻¹ := by rw [hkz]
      _ = w := by rw [← hg]; group

end J2Frame

end CFSG.Quasithin
