module

public import CFSG.RankThree.GF2n.Stroth80.Sec10CQtRoot
public import CFSG.RankThree.GF2n.Stroth80.Sec10Fuse

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

private theorem pi_mem_ker_iff (H : StrothHyp M Q Z) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (m : H0 M Z) {h : G} (hh : h ∈ Q) :
    M₀.π h ∈ LinearMap.ker ((φ m : M₀.E →ₗ[K] M₀.E) - 1) ↔ ⁅(m : G), h⁆ ∈ Z := by
  have hmQ : (m : G) * h * (m : G)⁻¹ ∈ Q := conj_mem_Q H m.2.1 hh
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hh hmQ, hφπ m h hh]
  rfl

private theorem sub_one_apply_pi (H : StrothHyp M Q Z) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (m : H0 M Z) {h : G} (hh : h ∈ Q) :
    ((φ m : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π h) = M₀.π ⁅(m : G), h⁆ := by
  have hmQ : (m : G) * h * (m : G)⁻¹ ∈ Q := conj_mem_Q H m.2.1 hh
  rw [commutatorElement_def, M₀.π_mul _ hmQ _ (Q.inv_mem hh), Tim79.QuadModel.pi_inv M₀ hh,
    hφπ m h hh, LinearMap.sub_apply, Module.End.one_apply, sub_eq_add_neg]
  rfl

private theorem card_map_ker_le (hc : Ctx M Q Z B) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) (T S : H0 M Z) (hT : (T : G) = t)
    (hS : (S : G) ∈ Y) :
    Nat.card ↥((LinearMap.ker ((φ T : M₀.E →ₗ[K] M₀.E) - 1)).map
      ((φ S : M₀.E →ₗ[K] M₀.E) - 1)) ≤ Nat.card Z := by
  classical
  have h12 := smith_1_12 hs
  have hQ1 : ∀ h : ↥(Q1 hc t), (h : G) ∈ Q := fun h => ((hc.mem_Q1_iff hs.memM).mp h.2).1
  let ψ : ↥(Q1 hc t) →* Multiplicative M₀.E :=
    { toFun := fun h => Multiplicative.ofAdd (((φ S : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π h))
      map_one' := by simp [Tim79.QuadModel.pi_one M₀]
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul]
        rw [M₀.π_mul a (hQ1 a) b (hQ1 b), map_add]
        rfl }
  have hker : (Ctx.commQ1Hom hc hs.memM).ker ≤ ψ.ker := by
    intro h hh
    rw [Ctx.ker_commQ1Hom, Subgroup.mem_subgroupOf] at hh
    have hK : (h : G) ∈ Kx Q Y := by rw [Kx_eq hs h12]; exact hh
    have hcY := Subgroup.mem_centralizer_iff.mp (Kx_le_centralizer_X hs h12 hK) _ hS
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (((φ S : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π h)) = 1
    rw [sub_one_apply_pi hc.hyp φ hφπ S (hQ1 h), ofAdd_eq_one, commutatorElement_def, hcY,
      mul_inv_cancel_right, mul_inv_cancel, Tim79.QuadModel.pi_one M₀]
  have hψ : Nat.card ψ.range ≤ Nat.card Z := by
    calc Nat.card ψ.range = ψ.ker.index := (Subgroup.index_ker ψ).symm
      _ ≤ (Ctx.commQ1Hom hc hs.memM).ker.index := Subgroup.index_antitone hker
      _ = Nat.card (Ctx.commQ1Hom hc hs.memM).range := Subgroup.index_ker _
      _ ≤ Nat.card Z := Nat.card_le_card_of_injective (fun y => (y.1 : ↥Z))
          (fun a b h => Subtype.ext h)
  have hmem : ∀ d ∈ (LinearMap.ker ((φ T : M₀.E →ₗ[K] M₀.E) - 1)).map
      ((φ S : M₀.E →ₗ[K] M₀.E) - 1), Multiplicative.ofAdd d ∈ ψ.range := by
    intro d hd
    obtain ⟨e, he, hed⟩ := Submodule.mem_map.mp hd
    obtain ⟨h, hh, rfl⟩ := M₀.π_surj e
    have hQ1h : h ∈ Q1 hc t := by
      refine (hc.mem_Q1_iff hs.memM).mpr ⟨hh, ?_⟩
      rw [← hT]
      exact (pi_mem_ker_iff hc.hyp φ hφπ T hh).mp he
    exact ⟨⟨h, hQ1h⟩, by rw [← hed]; rfl⟩
  haveI : Finite M₀.E := Module.finite_of_finite K
  refine le_trans (Nat.card_le_card_of_injective
    (fun d => (⟨Multiplicative.ofAdd (d : M₀.E), hmem d d.2⟩ : ↥ψ.range)) ?_) hψ
  intro a b hab
  have h1 := congrArg (fun x : ↥ψ.range => Multiplicative.toAdd (x : Multiplicative M₀.E)) hab
  exact Subtype.ext h1

private theorem act_comm_of_mem_QB (hc : Ctx M Q Z B) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t)
    {X : Subgroup G} (hX : Ctx M Q Z X) (hXY : X ≤ QB Y) (L S : H0 M Z) (hL : (L : G) ∈ QB X)
    (hS : (S : G) ∈ Y) : φ L * φ S = φ S * φ L := by
  have hne : X ≠ Y := by
    intro hXY'
    obtain ⟨a, ha, ha1⟩ := hX.exists_ne_one
    have h : a ∈ Y ⊓ Q := ⟨hXY' ▸ ha, hX.le ha⟩
    rw [hs.X_inf_Q, Subgroup.mem_bot] at h
    exact ha1 h
  have hYX : Y ≤ QB X := hc.hyp.le_QB_of_le_QB hX.conj hs.conj hne hXY
  have hcomm : ⁅(L : G), (S : G)⁆ ∈ Q :=
    hX.le (IsZConjugate.comm_mem_QB hc.hyp hX.conj hL (hYX hS))
  have h1 : φ ⁅L, S⁆ = 1 := (hφQ _).mpr hcomm
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private theorem comm_mem_Z_of_mem_map (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t)
    {X : Subgroup G} (hX : Ctx M Q Z X) (hXY : X ≤ QB Y) (T S : H0 M Z) (hT : (T : G) ∈ Y)
    (hS : (S : G) ∈ Y)
    (hcard : Nat.card ↥((LinearMap.ker ((φ T : M₀.E →ₗ[K] M₀.E) - 1)).map
      ((φ S : M₀.E →ₗ[K] M₀.E) - 1)) ≤ Nat.card Z) {u : G} (hu : u ∈ Q)
    (hud : M₀.π u ∈ (LinearMap.ker ((φ T : M₀.E →ₗ[K] M₀.E) - 1)).map
      ((φ S : M₀.E →ₗ[K] M₀.E) - 1)) {l : G} (hl : l ∈ QB X ⊓ M) : ⁅l, u⁆ ∈ Z := by
  set L : H0 M Z := ⟨l, hX.LB_le_H0 (Subgroup.mem_sup_right hl)⟩
  have hLS := DFunLike.congr_fun (act_comm_of_mem_QB hc φ hφQ hs hX hXY L S hl.1 hS)
  have hLT := DFunLike.congr_fun (act_comm_of_mem_QB hc φ hφQ hs hX hXY L T hl.1 hT)
  have hL2 : ∀ e, φ L (φ L e) = e := by
    have h1 : φ (L * L) = 1 := (hφQ _).mpr (by
      have := hX.le (IsZConjugate.sq_mem_QB hc.hyp hX.conj hl.1)
      rwa [pow_two] at this)
    intro e
    have := DFunLike.congr_fun h1 e
    rwa [map_mul] at this
  have hinv : ∀ d ∈ (LinearMap.ker ((φ T : M₀.E →ₗ[K] M₀.E) - 1)).map
      ((φ S : M₀.E →ₗ[K] M₀.E) - 1), (φ L : M₀.E →ₗ[K] M₀.E) d ∈
      (LinearMap.ker ((φ T : M₀.E →ₗ[K] M₀.E) - 1)).map ((φ S : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp hd
    refine Submodule.mem_map.mpr ⟨φ L e, ?_, ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at he ⊢
      have h2 : φ T (φ L e) = φ L (φ T e) := (hLT e).symm
      have he' : φ T e = e := sub_eq_zero.mp he
      rw [show ((φ T : M₀.E →ₗ[K] M₀.E) (φ L e)) = φ T (φ L e) from rfl, h2, he', sub_self]
    · have h2 : φ S (φ L e) = φ L (φ S e) := (hLS e).symm
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, h2, map_sub]
  have hcardK : Nat.card ↥((LinearMap.ker ((φ T : M₀.E →ₗ[K] M₀.E) - 1)).map
      ((φ S : M₀.E →ₗ[K] M₀.E) - 1)) ≤ Nat.card K := hD.card ▸ hcard
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hfix := involution_apply_eq_self_of_card_le hcardK (φ L : M₀.E →ₗ[K] M₀.E) hinv hL2 hud
  have hlQ : l * u * l⁻¹ ∈ Q := conj_mem_Q hc.hyp hl.2 hu
  rw [Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hu hlQ]
  exact (hφπ L u hu).trans hfix

theorem Sec10Hyp.comm_mem_Z_of_mem_root (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {μ₁ μ₂ : G}
    (hμ₁ : μ₁ ∈ M) (hμ₂ : μ₂ ∈ M) (hX₁ : conjSubgroup μ₁ B ≤ QB Y)
    (hX₂ : conjSubgroup μ₂ B ≤ QB Y) (hne : conjSubgroup μ₁ B ≠ conjSubgroup μ₂ B) {s : G}
    (hsY : s ∈ Y) {h : G} (hh : h ∈ Q) (hth : ⁅t, h⁆ ∈ Z) : ⁅s, h⁆ ∈ Z := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφQ, -⟩ := exists_actionHom_H0 hc.hyp hD
  have h12 := smith_1_12 hs
  set T : H0 M Z := ⟨t, h12.1 hs.mem⟩
  set S : H0 M Z := ⟨s, h12.1 hsY⟩
  have hcard := card_map_ker_le hc φ hφπ hs T S rfl hsY
  have hud : M₀.π ⁅s, h⁆ ∈ (LinearMap.ker ((φ T : M₀.E →ₗ[K] M₀.E) - 1)).map
      ((φ S : M₀.E →ₗ[K] M₀.E) - 1) :=
    Submodule.mem_map.mpr ⟨M₀.π h, (pi_mem_ker_iff hc.hyp φ hφπ T hh).mpr hth,
      sub_one_apply_pi hc.hyp φ hφπ S hh⟩
  have hu : ⁅s, h⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (conj_mem_Q hc.hyp (h12.1 hsY).1 hh) (Q.inv_mem hh)
  have h1 := H.mem_sup_of_forall_comm_mem h34 hμ₁ hu fun l hl =>
    comm_mem_Z_of_mem_map hc hD φ hφπ hφQ hs (hc.conj_of_mem hμ₁) hX₁ T S hs.mem hsY hcard hu
      hud hl
  have h2 := H.mem_sup_of_forall_comm_mem h34 hμ₂ hu fun l hl =>
    comm_mem_Z_of_mem_map hc hD φ hφπ hφQ hs (hc.conj_of_mem hμ₂) hX₂ T S hs.mem hsY hcard hu
      hud hl
  have hPZ : Q ⊓ QB Y ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h' : a ∈ Z ⊓ QB Y := ⟨ha.2, ha.1.2⟩
    rwa [Z_inf_QB_eq_bot hs h12] at h'
  have hP := hc.hyp.sup_inf_sup_eq (hc.conj_of_mem hμ₁).conj (hc.conj_of_mem hμ₂).conj hne
    (le_inf (hc.conj_of_mem hμ₁).le hX₁) (le_inf (hc.conj_of_mem hμ₂).le hX₂) inf_le_left hPZ
  rw [← hP]
  exact ⟨h1, h2⟩

end CFSG.RankThree.GF2n.Stroth80
