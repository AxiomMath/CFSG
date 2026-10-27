module

public import CFSG.RankThree.GF2n.Stroth80.Sec7IsometryFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7LinAlg
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4PsiCore
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77Meet

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_mem_H0_of_mul_Q (hc : Ctx M Q Z B) {u s : G} (hu : u ∈ H0 M Z)
    (hs1 : s * u⁻¹ ∈ Q) : s ∈ H0 M Z := by
  have hsM : s ∈ M := by
    have h1 : s = (s * u⁻¹) * u := by group
    rw [h1]
    exact M.mul_mem (hc.hyp.Q_normal.1 hs1) hu.1
  refine ⟨hsM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hu.2 z hz
  have h2 := hc.conj_Z_of_mem_Q hs1 hz
  calc z * s = z * ((s * u⁻¹) * u) := by group
    _ = (z * (s * u⁻¹)) * u := by group
    _ = ((s * u⁻¹) * z) * u := by
        have h3 : (s * u⁻¹) * z * (s * u⁻¹)⁻¹ = z := h2
        have h4 : (s * u⁻¹) * z = z * (s * u⁻¹) := by
          calc (s * u⁻¹) * z = ((s * u⁻¹) * z * (s * u⁻¹)⁻¹) * (s * u⁻¹) := by group
            _ = z * (s * u⁻¹) := by rw [h3]
        rw [h4]
    _ = (s * u⁻¹) * (z * u) := by group
    _ = (s * u⁻¹) * (u * z) := by rw [h1]
    _ = s * z := by group

theorem sec7_conj_mem_H0 (hc : Ctx M Q Z B) {g h : G} (hg : g ∈ M) (hh : h ∈ H0 M Z) :
    g * h * g⁻¹ ∈ H0 M Z := by
  refine ⟨M.mul_mem (M.mul_mem hg hh.1) (M.inv_mem hg),
    Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hz' : g⁻¹ * z * g ∈ Z := by
    have : z ∈ conjSubgroup g Z := by rw [hc.conj_Z_eq hg]; exact hz
    exact mem_conjSubgroup.mp this
  have h1 := Subgroup.mem_centralizer_iff.mp hh.2 _ hz'
  calc z * (g * h * g⁻¹) = g * ((g⁻¹ * z * g) * h) * g⁻¹ := by group
    _ = g * (h * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
    _ = g * h * g⁻¹ * z := by group


theorem sec7_pair_psi [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G} {K : Type}
    [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    (ht : t ∈ LB M Q B) (ψ : M₀.E →ₗ[K] M₀.E)
    (hψ : ∀ e, ψ e = (ρ (QuotientGroup.mk (⟨t, hc.LB_le_M ht⟩ : ↥M))).toAdd e - e)
    (hrange : ∀ e, e ∈ LinearMap.range ψ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    {g s : G} (hgM : g ∈ M) (hsM : s ∈ M) (hs1 : s * (g * t * g⁻¹)⁻¹ ∈ Q) :
    ∃ ψs : M₀.E →ₗ[K] M₀.E,
      (∀ e, ψs e = (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd e - e) ∧
      (∀ e, e ∈ LinearMap.range ψs ↔ e ∈ M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t))) ∧
      LinearMap.ker ψs = M₀.B.orthogonal (LinearMap.range ψs) := by
  classical
  have htM : t ∈ M := hc.LB_le_M ht
  have htH : t ∈ H0 M Z := hc.LB_le_H0 ht
  have hguH : g * t * g⁻¹ ∈ H0 M Z := sec7_conj_mem_H0 hc hgM htH
  have hsH : s ∈ H0 M Z := sec7_mem_H0_of_mul_Q hc hguH hs1
  have hsbar : (QuotientGroup.mk ⟨s, hsM⟩ : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨s, hsM⟩, Subgroup.mem_subgroupOf.mpr hsH, rfl⟩
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  let Tl : M₀.E ≃ₗ[K] M₀.E :=
    AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk ⟨s, hsM⟩)).toAdd (hS.lin _ hsbar)
  let ψs : M₀.E →ₗ[K] M₀.E := (Tl : M₀.E →ₗ[K] M₀.E) - 1
  have hψs : ∀ e, ψs e = (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd e - e := fun e => rfl
  refine ⟨ψs, hψs, ?_, sec7_ker_sub_one_eq_perp_range M₀.B hf hr Tl (hS.iso _ hsbar)⟩
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hq' : (g * t * g⁻¹)⁻¹ * s ∈ Q := by
    have h1 := (hc.conj_mem_Q_of_mem_M (M.inv_mem hguM)).1 _ hs1
    have e : (g * t * g⁻¹)⁻¹ * (s * (g * t * g⁻¹)⁻¹) * ((g * t * g⁻¹)⁻¹)⁻¹ =
        (g * t * g⁻¹)⁻¹ * s := by group
    rwa [e] at h1
  have hmk : (QuotientGroup.mk ⟨s, hsM⟩ : Mbar M Q) =
      QuotientGroup.mk ⟨g, hgM⟩ * QuotientGroup.mk ⟨t, htM⟩ * (QuotientGroup.mk ⟨g, hgM⟩)⁻¹ := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have h1 := Q.inv_mem hq'
    simpa using h1
  set ν : M₀.E ≃+ M₀.E := (ρ (QuotientGroup.mk ⟨g, hgM⟩)).toAdd with hν
  have hps : ∀ e, ψs e = ν (ψ (ν.symm e)) := by
    intro e
    rw [hψs, hmk, sec7_psi_conj ρ (QuotientGroup.mk ⟨t, htM⟩) (QuotientGroup.mk ⟨g, hgM⟩) e, hψ]
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  intro e
  have h1 : e ∈ LinearMap.range ψs ↔ ν.symm e ∈ LinearMap.range ψ := by
    constructor
    · rintro ⟨e', rfl⟩
      rw [hps, ν.symm_apply_apply]
      exact LinearMap.mem_range_self ψ _
    · rintro ⟨x, hx⟩
      refine ⟨ν x, ?_⟩
      rw [hps, ν.symm_apply_apply, hx, ν.apply_symm_apply]
  rw [h1, hrange]
  have h2 := sec7_img_conj_iff hc M₀ ρ b hS hgM hZV (ν.symm e)
  rw [← hν, ν.apply_symm_apply] at h2
  exact h2.symm


theorem sec7_pair_card_meet [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    {g : G} (hgM : g ∈ M) (ψs : M₀.E →ₗ[K] M₀.E)
    (hrs : ∀ e, e ∈ LinearMap.range ψs ↔ e ∈ M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t)))
    (hUcard : Nat.card (hc.VtSub hS.model t) = Nat.card K ^ 4) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
        Nat.card K ^ (1 + Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs)) ∧
      Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) ≤ 4 ∧
      (Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) = 4 →
        conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t) := by
  classical
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZVg : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro z hz
    have hz' : z ∈ conjSubgroup g Z := by rw [hc.conj_Z_eq hgM]; exact hz
    exact mem_conjSubgroup.mpr (hZV (mem_conjSubgroup.mp hz'))
  have hZD : Z ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    le_inf hZV hZVg
  have hDQ : Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Q :=
    inf_le_left.trans hVQ
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hfU : Module.finrank K (hc.VtSub hS.model t) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := hc.VtSub hS.model t)
    rw [hUcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have himg : ∀ e, e ∈ M₀.img (Vt M (LB M Q B) B Z t ⊓
      conjSubgroup g (Vt M (LB M Q B) B Z t)) ↔ e ∈ hc.VtSub hS.model t ⊓ LinearMap.range ψs := by
    intro e
    constructor
    · rintro ⟨x, hxD, hxQ, rfl⟩
      exact ⟨(hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hxD.1 hxQ),
        (hrs _).mpr (M₀.pi_mem_img hxD.2 hxQ)⟩
    · rintro ⟨hU, hR⟩
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
      have h1 : x ∈ Vt M (LB M Q B) B Z t :=
        (Tim79.QuadModel.mem_img_iff M₀ hZV hxQ).mp ((hc.mem_VtSub hS.model t).mp hU)
      have h2 : x ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
        (Tim79.QuadModel.mem_img_iff M₀ hZVg hxQ).mp ((hrs _).mp hR)
      exact M₀.pi_mem_img ⟨h1, h2⟩ hxQ
  have hcard1 := Tim79.QuadModel.card_eq M₀ hDQ hZD
  have hcard2 : Nat.card (M₀.img (Vt M (LB M Q B) B Z t ⊓
      conjSubgroup g (Vt M (LB M Q B) B Z t))) =
      Nat.card ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) :=
    Nat.card_congr (Equiv.subtypeEquivRight himg)
  have hcard3 := Module.natCard_eq_pow_finrank (K := K)
    (V := ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs))
  refine ⟨?_, ?_, fun h4 => ?_⟩
  · rw [hcard1, hcard2, hcard3, pow_add, pow_one, ← hS.card]
  · rw [← hfU]
    exact Submodule.finrank_mono inf_le_left
  · have hUR : hc.VtSub hS.model t ⊓ LinearMap.range ψs = hc.VtSub hS.model t :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (h4.trans hfU.symm)
    have hle : Vt M (LB M Q B) B Z t ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      intro x hx
      have hxQ : x ∈ Q := hVQ hx
      have hU : M₀.π x ∈ hc.VtSub hS.model t :=
        (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hx hxQ)
      have hU' : M₀.π x ∈ hc.VtSub hS.model t ⊓ LinearMap.range ψs := by rw [hUR]; exact hU
      exact (Tim79.QuadModel.mem_img_iff M₀ hZVg hxQ).mp ((hrs _).mp hU'.2)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm


theorem sec7_ker_psi_eq_orth [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    (ψ : M₀.E →ₗ[K] M₀.E)
    (hW : ∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0) :
    LinearMap.ker ψ = M₀.B.orthogonal (hc.VtSub hS.model t) := by
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  ext e
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
  rw [LinearMap.mem_ker, ← hW x hxQ]
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun z hz =>
    ⟨hc.Z_le_Q hz, Subgroup.mem_centralizer_iff.mpr fun v hv => by
      have := hc.conj_Z_of_mem_Q (hVQ hv) hz
      calc v * z = (v * z * v⁻¹) * v := by group
        _ = z * v := by rw [this]⟩
  rw [← Tim79.QuadModel.mem_img_iff M₀ hZW hxQ, mem_img_Wt_iff M₀ hS.model.reg hVQ,
    LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h u hu
    exact (LinearMap.BilinForm.isOrtho_def).mpr
      (by rw [Tim79.QuadModel.B_comm, h u hu, neg_zero])
  · intro h v hv
    have := LinearMap.BilinForm.isOrtho_def.mp (h v hv)
    rw [Tim79.QuadModel.B_comm, this, neg_zero]

theorem step77OneMeet_facts_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec7Hyp hc n t → OmegaMinusNat hc t 2 →
      ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q →
      ∃ d : ℕ, d ≤ 4 ∧
        Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
          Nat.card Z ^ (1 + d) ∧
        (d = 4 → conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t) ∧
        ((∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t) → 2 ≤ d) := by
  intro G _ _ M Q Z B hc n t hs hom Z0 hZ0 g hgM s hs1
  classical
  haveI := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hsM : s ∈ M := by
    have h1 : s = (s * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
    rw [h1]
    exact M.mul_mem (hc.hyp.Q_normal.1 hs1) hguM
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, hW, hinj, hA5, hA6⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  obtain ⟨ψs, hψs, hrs, hker⟩ := sec7_pair_psi hc M₀ ρ b hS ht ψ hψ hrange hgM hsM hs1
  obtain ⟨-, hUcard⟩ := sec7_Hset_card h34 hRoot hc hs hom M₀ ρ b hS
  obtain ⟨hc1, hd4, hd⟩ := sec7_pair_card_meet hc M₀ ρ b hS hgM ψs hrs hUcard
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  refine ⟨Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs), hd4, ?_, hd, ?_⟩
  · rw [hc1, ← hS.card]
  intro htame
  have hfR : Module.finrank K (LinearMap.range ψs) = 4 := by
    have hcard : Nat.card (LinearMap.range ψs) = Nat.card K ^ 4 := by
      have h1 : Nat.card (LinearMap.range ψs) = Nat.card (M₀.img (conjSubgroup g
          (Vt M (LB M Q B) B Z t))) :=
        Nat.card_congr (Equiv.subtypeEquivRight hrs)
      rw [h1, sec7_card_img_conj hc M₀ ρ b hS hgM hZV']
      have h2 : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
          Nat.card (hc.VtSub hS.model t) := rfl
      rw [h2, hUcard]
    have h := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range ψs)
    rw [hcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hk1 := sec7_ker_psi_eq_orth hc M₀ ρ b hS ψ hW
  have hmap := sec7_finrank_map_orthogonal M₀.B hf hr ψs hker (hc.VtSub hS.model t)
  have hsub : (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs ≤
      hc.VtSub hS.model t ⊓ LinearMap.range ψs := by
    rintro _ ⟨e, he, rfl⟩
    rw [← hk1] at he
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    have hxW : x ∈ Wt Q (Vt M (LB M Q B) B Z t) := (hW x hxQ).mpr (LinearMap.mem_ker.mp he)
    have hsx : ψs (M₀.π x) = M₀.π ⁅s, x⁆ := by
      have hsxQ : s * x * s⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hsM).1 x hxQ
      have e1 : M₀.π (s * x * s⁻¹) = (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd (M₀.π x) :=
        hS.conj ⟨s, hsM⟩ x hxQ
      have e2 : ⁅s, x⁆ = (s * x * s⁻¹) * x⁻¹ := rfl
      rw [hψs, e2, M₀.π_mul _ hsxQ _ (Q.inv_mem hxQ), M₀.pi_inv hxQ, ← e1, sub_eq_add_neg]
    have hcQ : ⁅s, x⁆ ∈ Q := by
      have e2 : ⁅s, x⁆ = (s * x * s⁻¹) * x⁻¹ := rfl
      rw [e2]
      exact Q.mul_mem ((hc.conj_mem_Q_of_mem_M hsM).1 x hxQ) (Q.inv_mem hxQ)
    refine ⟨(hc.mem_VtSub hS.model t).mpr (hsx ▸ M₀.pi_mem_img (htame x hxW) hcQ),
      LinearMap.mem_range_self ψs _⟩
  have hle := Submodule.finrank_mono hsub
  rw [hmap, hfR] at hle
  omega

end CFSG.RankThree.GF2n.Stroth80
