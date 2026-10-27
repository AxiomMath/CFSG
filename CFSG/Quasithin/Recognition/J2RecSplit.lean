module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.Quasithin.Recognition.J2RecCzAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM
open CFSG.ComponentClassification.PresentationLocal

theorem J2Cz.QM.exists_twist : ∀ p : QM, (p * phiAHom p = 1 ∨ p * phiAHom p = z) →
    ∃ r : QM, r * p * (phiAHom r)⁻¹ = 1 ∨ r * p * (phiAHom r)⁻¹ = z := by
  decide +kernel

theorem J2Cz.exists_conj_pa : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ * σ = 1 → σ ≠ 1 →
    ∃ π : Perm (Fin 5), Perm.sign π = 1 ∧ π * σ * π⁻¹ = pa := by
  decide +kernel

theorem J2Cz.carmichaelPerm_mul_ne_one (k l : CarmichaelIndex 5) :
    carmichaelPerm k * carmichaelPerm l ≠ 1 := by
  intro h1
  have h2 := congrArg (fun π : Perm (Fin 5) => π 0) h1
  simp only [Perm.mul_apply, Perm.one_apply] at h2
  have h3 : carmichaelPerm l 0 = ⟨1, by norm_num⟩ := by
    rw [carmichaelPerm_apply]
    simp
  have h4 : carmichaelPerm k ⟨1, by norm_num⟩ = k.1 := by
    rw [carmichaelPerm_apply]
    simp
  rw [h3, h4] at h2
  have := k.2
  rw [h2] at this
  simp at this

theorem J2Cz.mul_conj_mul_inv (α : MulAut QM) (p : QM) :
    α * MulAut.conj p * α⁻¹ = MulAut.conj (α p) := by
  refine MulEquiv.ext fun q => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem J2Cz.conj_eq_one_of_central {q : QM} (hq : q = 1 ∨ q = z) : MulAut.conj q = 1 := by
  refine MulEquiv.ext fun p => ?_
  rw [MulAut.conj_apply, MulAut.one_apply]
  rcases hq with rfl | rfl
  · group
  · rw [z_comm p]
    group

theorem J2Cz.central_of_conj_eq_one {q : QM} (hq : MulAut.conj q = 1) : q = 1 ∨ q = z := by
  refine eq_of_comm_x q fun j => ?_
  have h1 := DFunLike.congr_fun hq (x j)
  rw [MulAut.conj_apply, MulAut.one_apply] at h1
  calc q * x j = q * x j * q⁻¹ * q := by group
    _ = x j * q := by rw [h1]

section General

variable {G : Type} [Group G]

theorem exists_czAct_eq_conj_of_mulEquiv {P : Subgroup G}
    (χ : ↥(pCoreOf 2 P) ≃* QM) (r : QM) :
    ∃ n : ↥P, (n : G) ∈ pCoreOf 2 P ∧ czActOf χ n = MulAut.conj r := by
  refine ⟨⟨χ.symm r, pCoreOf_le 2 P (χ.symm r).2⟩, (χ.symm r).2, ?_⟩
  rw [czActOf_of_mem χ (χ.symm r).2]
  simp

theorem exists_conj_eq_phiA_of_card {P : Subgroup G} (hchar : CharTwo P)
    (hP : Nat.card P = 1920) (χ : ↥(pCoreOf 2 P) ≃* QM)
    {t : ↥P} (ht2 : t * t = 1) (htQ : (t : G) ∉ pCoreOf 2 P) :
    ∃ u : ↥P, u * u = 1 ∧ czActOf χ u = phiA := by
  set θ : alternatingGroup (Fin 5) →* MulAut QM := L0.subtype.comp lineEquiv.symm.toMonoidHom
    with hθ
  have hθperm : ∀ σ, linePerm (θ σ) = σ := linePerm_lineEquiv_symm
  have hθmem : ∀ σ, θ σ ∈ L0 := fun σ => (lineEquiv.symm σ).2
  set σ : alternatingGroup (Fin 5) := ⟨linePerm (czActOf χ t),
    linePerm_czAct_mem_of_card hchar hP χ t⟩ with hσ
  have h1 : linePerm (czActOf χ t * (θ σ)⁻¹) = 1 := by
    show linePermHom (czActOf χ t * (θ σ)⁻¹) = 1
    rw [map_mul, map_inv]
    show linePerm (czActOf χ t) * (linePerm (θ σ))⁻¹ = 1
    rw [hθperm, hσ]
    exact mul_inv_cancel _
  obtain ⟨p, hp⟩ := eq_conj_of_linePerm_eq_one h1
  have hψt : czActOf χ t = MulAut.conj p * θ σ := by
    rw [← hp]
    group
  have hσ1 : (σ : Perm (Fin 5)) ≠ 1 := fun h2 =>
    htQ (mem_pCoreOf_of_linePerm_eq_one_of_charTwo hchar χ h2)
  have hσ2 : (σ : Perm (Fin 5)) * σ = 1 := by
    have h2 := congrArg (fun g => linePermHom (czActOf χ g)) ht2
    simp only [map_mul, map_one] at h2
    exact h2
  obtain ⟨π, hπ, hπσ⟩ := exists_conj_pa σ (Perm.mem_alternatingGroup.mp σ.2) hσ2 hσ1
  set πA : alternatingGroup (Fin 5) := ⟨π, Perm.mem_alternatingGroup.mpr hπ⟩ with hπA
  obtain ⟨gπ, hgπ⟩ := exists_czAct_eq_of_card hchar hP χ (hθmem πA)
  set p₁ := θ πA p with hp₁
  have hpa : πA * σ * πA⁻¹ = ⟨pa, pa_mem⟩ := Subtype.ext hπσ
  have hψt₁ : czActOf χ (gπ * t * gπ⁻¹) = MulAut.conj p₁ * phiA := by
    rw [map_mul, map_mul, map_inv, hgπ, hψt, ← lineEquiv_symm_pa]
    have e1 : θ πA * (MulAut.conj p * θ σ) * (θ πA)⁻¹ =
        (θ πA * MulAut.conj p * (θ πA)⁻¹) * (θ πA * θ σ * (θ πA)⁻¹) := by group
    rw [e1, mul_conj_mul_inv, ← map_inv, ← map_mul, ← map_mul, hpa]
    rfl
  have ht₁2 : (gπ * t * gπ⁻¹) * (gπ * t * gπ⁻¹) = 1 := by
    calc (gπ * t * gπ⁻¹) * (gπ * t * gπ⁻¹) = gπ * (t * t) * gπ⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hphiA2 : phiA * phiA = 1 := MulEquiv.ext fun q => phiAHom_phiAHom q
  have hcen : p₁ * phiAHom p₁ = 1 ∨ p₁ * phiAHom p₁ = J2Cz.QM.z := by
    apply central_of_conj_eq_one
    have h2 := congrArg (czActOf χ) ht₁2
    rw [map_mul, hψt₁, map_one] at h2
    have e2 : MulAut.conj p₁ * phiA * (MulAut.conj p₁ * phiA) =
        MulAut.conj p₁ * (phiA * MulAut.conj p₁ * phiA⁻¹) * (phiA * phiA) := by group
    rw [e2, mul_conj_mul_inv, hphiA2, mul_one, ← map_mul] at h2
    exact h2
  obtain ⟨r, hr⟩ := exists_twist p₁ hcen
  obtain ⟨n, -, hn⟩ := exists_czAct_eq_conj_of_mulEquiv χ r
  refine ⟨n * (gπ * t * gπ⁻¹) * n⁻¹, ?_, ?_⟩
  · calc n * (gπ * t * gπ⁻¹) * n⁻¹ * (n * (gπ * t * gπ⁻¹) * n⁻¹) =
        n * ((gπ * t * gπ⁻¹) * (gπ * t * gπ⁻¹)) * n⁻¹ := by group
      _ = 1 := by rw [ht₁2]; group
  · rw [map_mul, map_mul, map_inv, hn, hψt₁]
    have e3 : MulAut.conj r * (MulAut.conj p₁ * phiA) * (MulAut.conj r)⁻¹ =
        MulAut.conj r * MulAut.conj p₁ * (phiA * (MulAut.conj r)⁻¹ * phiA⁻¹) * phiA := by
          group
    rw [e3, ← map_inv, mul_conj_mul_inv, ← map_mul, ← map_mul]
    have e4 : r * p₁ * phiA r⁻¹ = r * p₁ * (phiAHom r)⁻¹ := by
      rw [map_inv]
      rfl
    rw [e4, conj_eq_one_of_central hr, one_mul]

theorem exists_complement_of_involution_of_card {P : Subgroup G} (hchar : CharTwo P)
    (hP : Nat.card P = 1920) (χ : ↥(pCoreOf 2 P) ≃* QM) {t : G}
    (htP : t ∈ P) (ht2 : t * t = 1) (htQ : t ∉ pCoreOf 2 P) :
    ∃ L : Subgroup G, L ≤ P ∧ L ⊓ pCoreOf 2 P = ⊥ ∧ Nat.card L = 60 := by
  set θ : alternatingGroup (Fin 5) →* MulAut QM := L0.subtype.comp lineEquiv.symm.toMonoidHom
    with hθ
  have hθperm : ∀ σ, linePerm (θ σ) = σ := linePerm_lineEquiv_symm
  have hθmem : ∀ σ, θ σ ∈ L0 := fun σ => (lineEquiv.symm σ).2
  have hθinj : Function.Injective θ :=
    L0.subtype_injective.comp lineEquiv.symm.injective
  have hθpa : θ ⟨pa, pa_mem⟩ = phiA := lineEquiv_symm_pa
  set zP : ↥P := symmZ χ with hzP
  have hzP2 : zP * zP = 1 := by rw [hzP]; exact symmZ_sq χ
  have hzcomm : ∀ g : ↥P, g * zP = zP * g := fun g => by
    rw [hzP]
    exact Subgroup.mem_center_iff.mp (symmZ_mem_center χ) g
  have hker : ∀ g : ↥P, czActOf χ g = 1 → g = 1 ∨ g = zP := fun g hg => by
    rcases eq_one_or_eq_of_czAct_eq_one_of_charTwo hchar χ hg with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  obtain ⟨u, hu2, hu⟩ := exists_conj_eq_phiA_of_card hchar hP χ
    (t := ⟨t, htP⟩) (Subtype.ext ht2) htQ
  have hy : ∀ k : CarmichaelIndex 5, ∃ y : ↥P,
      czActOf χ y = θ (carmichaelCycle k) ∧ y ^ 3 = 1 := by
    intro k
    obtain ⟨g, hg⟩ := exists_czAct_eq_of_card hchar hP χ (hθmem (carmichaelCycle k))
    have h3 : czActOf χ (g ^ 3) = 1 := by
      rw [map_pow, hg, ← map_pow, carmichaelCycle_pow_three, map_one]
    rcases hker _ h3 with h4 | h4
    · exact ⟨g, hg, h4⟩
    · refine ⟨g * zP, ?_, ?_⟩
      · rw [map_mul, hg, hzP, czActOf_symm_z, mul_one]
      · have hz3 : zP ^ 3 = zP := by rw [pow_succ, pow_two, hzP2, one_mul]
        rw [Commute.mul_pow (hzcomm g) 3, h4, hz3, hzP2]
  choose y hyψ hy3 using hy
  have hyy : ∀ k l, k ≠ l → (y k * y l) ^ 2 = 1 := by
    intro k l hkl
    set c := carmichaelCycle k * carmichaelCycle l with hc
    have hc1 : (c : Perm (Fin 5)) ≠ 1 := carmichaelPerm_mul_ne_one k l
    have hc2 : (c : Perm (Fin 5)) * c = 1 := by
      have := congrArg Subtype.val (carmichaelCycle_mul_sq k l hkl)
      rwa [pow_two] at this
    obtain ⟨π, hπ, hπc⟩ := exists_conj_pa c (Perm.mem_alternatingGroup.mp c.2) hc2 hc1
    set πA : alternatingGroup (Fin 5) := ⟨π, Perm.mem_alternatingGroup.mpr hπ⟩ with hπA
    have hcpa : πA⁻¹ * ⟨pa, pa_mem⟩ * πA = c := by
      have : πA * c * πA⁻¹ = ⟨pa, pa_mem⟩ := Subtype.ext hπc
      rw [← this]
      group
    obtain ⟨g, hg⟩ := exists_czAct_eq_of_card hchar hP χ (hθmem πA⁻¹)
    set w := g * u * g⁻¹ with hw
    have hw2 : w * w = 1 := by
      calc w * w = g * (u * u) * g⁻¹ := by rw [hw]; group
        _ = 1 := by rw [hu2]; group
    have hψw : czActOf χ w = czActOf χ (y k * y l) := by
      have e1 : czActOf χ w = θ (πA⁻¹ * ⟨pa, pa_mem⟩ * πA) := by
        rw [hw, map_mul, map_mul, map_inv, hg, hu, ← hθpa, map_mul, map_mul, map_inv,
          inv_inv]
      rw [e1, hcpa, hc, map_mul, map_mul, hyψ, hyψ]
    have h1 : czActOf χ ((y k * y l)⁻¹ * w) = 1 := by
      rw [map_mul, map_inv, hψw, inv_mul_cancel]
    have h2 : y k * y l = w ∨ y k * y l = w * zP := by
      rcases hker _ h1 with h3 | h3
      · left
        calc y k * y l = y k * y l * ((y k * y l)⁻¹ * w) := by rw [h3, mul_one]
          _ = w := by group
      · right
        calc y k * y l = y k * y l * ((y k * y l)⁻¹ * w) * zP⁻¹ := by
              rw [h3, mul_inv_cancel_right]
          _ = w * zP⁻¹ := by group
          _ = w * zP := by rw [inv_eq_of_mul_eq_one_right hzP2]
    rw [pow_two]
    rcases h2 with h3 | h3 <;> rw [h3]
    · exact hw2
    · calc w * zP * (w * zP) = w * (zP * w) * zP := by group
        _ = w * (w * zP) * zP := by rw [hzcomm w]
        _ = (w * w) * (zP * zP) := by group
        _ = 1 := by rw [hw2, hzP2, one_mul]
  obtain ⟨φ, hφ⟩ := exists_hom_carmichaelCycle (n := 5) (by norm_num) y hy3 hyy
  have hψφ : (czActOf χ).comp φ = θ :=
    hom_ext_carmichaelCycle (n := 5) (by norm_num) fun k => by
      rw [MonoidHom.comp_apply, hφ, hyψ]
  have hφinj : Function.Injective φ := fun a b hab => hθinj (by
    rw [← hψφ, MonoidHom.comp_apply, MonoidHom.comp_apply, hab])
  refine ⟨φ.range.map P.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨⟨_, ⟨σ, rfl⟩, rfl⟩, hgQ⟩
    have h1 : linePerm (czActOf χ (φ σ)) = 1 := by
      have h0 : czActOf χ (φ σ) = MulAut.conj (χ ⟨_, hgQ⟩) := czActOf_of_mem χ hgQ
      rw [h0, linePerm_conj]
    rw [← MonoidHom.comp_apply, hψφ, hθperm] at h1
    have h2 : σ = 1 := Subtype.ext h1
    rw [h2, map_one]
    rfl
  · rw [Subgroup.card_map_of_injective P.subtype_injective,
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm, nat_card_alternatingGroup,
      Nat.card_fin]
    rfl

theorem card_eq_1920_of_quot {P : Subgroup G}
    (hQ : Nonempty (↥(pCoreOf 2 P) ≃* QM))
    (hquot : Nonempty (OTwoQuot P ≃* alternatingGroup (Fin 5))) :
    Nat.card P = 1920 := by
  obtain ⟨χ⟩ := hQ
  obtain ⟨e⟩ := hquot
  have h60 : Nat.card (OTwoQuot P) = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have h32 : Nat.card (CFSG.Open.pCore 2 ↥P) = 32 := by
    have h := Nat.card_congr χ.toEquiv
    unfold pCoreOf at h
    rw [Subgroup.card_map_of_injective P.subtype_injective, card_QM] at h
    exact h
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥P)
  rw [h60, h32] at h
  omega

theorem exists_complement_of_involution_of_le {P : Subgroup G} [Finite P]
    (hQ : Nonempty (↥(pCoreOf 2 P) ≃* QM)) (hchar : CharTwo P)
    (hquot : Nonempty (OTwoQuot P ≃* alternatingGroup (Fin 5)))
    {t : G} (htP : t ∈ P) (ht2 : t * t = 1) (htQ : t ∉ pCoreOf 2 P) :
    ∃ K : Subgroup G, K ≤ P ∧ K ⊓ pCoreOf 2 P = ⊥ ∧ Nat.card K = 60 := by
  obtain ⟨χ⟩ := hQ
  exact exists_complement_of_involution_of_card hchar (card_eq_1920_of_quot ⟨χ⟩ hquot) χ
    htP ht2 htQ

end General

namespace IsTypeH2

variable {G : Type} [Group G] {z : G}

variable (χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM)

theorem exists_czAct_eq_conj (r : QM) :
    ∃ n : ↥(Subgroup.centralizer ({z} : Set G)),
      (n : G) ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ czAct χ n = MulAut.conj r := by
  exact exists_czAct_eq_conj_of_mulEquiv χ r

theorem exists_complement_of_involution (h : IsTypeH2 G z) {t : G}
    (htC : t ∈ Subgroup.centralizer ({z} : Set G)) (ht2 : t * t = 1)
    (htQ : t ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :
    ∃ L : Subgroup G, L ≤ Subgroup.centralizer ({z} : Set G) ∧
      L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = ⊥ ∧ Nat.card L = 60 := by
  obtain ⟨χ, -⟩ := h.exists_equiv_QM
  exact exists_complement_of_involution_of_card h.charTwo h.card_centralizer χ htC ht2 htQ

end IsTypeH2

end CFSG.Quasithin
