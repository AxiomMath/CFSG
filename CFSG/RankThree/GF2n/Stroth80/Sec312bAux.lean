module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClConj
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClReprData
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.mem_normalizer_conj_LB_of_fix {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    {hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)}
    (D : ReprData (Vt M (LB M Q B) B Z t) (Rt M (LB M Q B) t) (hc.CN t) M₀ hS t)
    {m : G} (hm : m ∈ M) (ht : t ∈ conjSubgroup m (LB M Q B))
    (e : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    (heB : ∀ v : M₀.E, v ∈ M₀.img (conjSubgroup m B) ↔ ∃ s : K, v = s • (e : M₀.E))
    (τ : ↥(Rt M (LB M Q B) t)) (a : K) (hτe : D.ρ τ e = a • e) :
    (τ : G) ∈ Subgroup.normalizer (conjSubgroup m (LB M Q B) : Set G) := by
  classical
  have hcC := hc.conj_of_mem hm
  have hsC := sec5Hyp_conj hc hm hs ht
  have hτM : (τ : G) ∈ M := hc.Rt_le_M t τ.2
  have hτH : (τ : G) ∈ H0 M Z := hc.Rt_le_H0 t τ.2
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  rw [← hc.LB_conj hm]
  refine (hcC.mem_normalizer_LB_iff' hsC.width hsC.n_gt hsC.noA2 hτM).mpr ?_
  have hBN : conjSubgroup m B ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hcC.le hu))
  have hZn : ∀ a ∈ M, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := fun a ha z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha) z).mp hz
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hx
  have e1 : (τ : G) * (u * z) * (τ : G)⁻¹ =
      ((τ : G) * u * (τ : G)⁻¹) * ((τ : G) * z * (τ : G)⁻¹) := by group
  rw [e1]
  refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right (hZn _ hτM z hz))
  have huQ : u ∈ Q := hcC.le hu
  have huV : u ∈ Vt M (LB M Q B) B Z t := sec39_conjB_le_Vt hm ht hu
  have hw : M₀.π u ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS :=
    mem_imgSub.mpr (M₀.pi_mem_img huV huQ)
  obtain ⟨s, hs'⟩ := (heB _).mp (M₀.pi_mem_img hu huQ)
  obtain ⟨hw', hρ⟩ := D.ρ_apply τ (φ₀ ⟨τ, hτH⟩) (fun x hx => hφπ ⟨τ, hτH⟩ x hx)
    ⟨M₀.π u, hw⟩
  have hwe : (⟨M₀.π u, hw⟩ : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) = s • e :=
    Subtype.ext hs'
  have h2 : ((D.ρ τ ⟨M₀.π u, hw⟩ : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) : M₀.E) =
      (φ₀ ⟨τ, hτH⟩) (M₀.π u) := by rw [hρ]
  have h3 : D.ρ τ ⟨M₀.π u, hw⟩ = (s * a) • e := by
    rw [hwe, map_smul, hτe, smul_smul]
  rw [h3] at h2
  have h4 : M₀.π ((τ : G) * u * (τ : G)⁻¹) = (s * a) • (e : M₀.E) := by
    rw [hφπ ⟨τ, hτH⟩ u huQ, ← h2]
    rfl
  have hxQ : (τ : G) * u * (τ : G)⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hτM).1 u huQ
  exact (M₀.mem_img_iff (le_sup_right : Z ≤ conjSubgroup m B ⊔ Z) hxQ).mp
    (M₀.img_mono le_sup_left ((heB _).mpr ⟨s * a, h4⟩))


theorem Ctx.CN_conj_eq (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (t : G) :
    (hc.conj_of_mem hm).CN t = hc.CN t := by
  ext x
  rw [Ctx.mem_CN, Ctx.mem_CN, (rt_vt_conj hc hm t).1, (rt_vt_conj hc hm t).2]

theorem Ctx.Rt_le_of_mul_CN (h34 : Stroth34Statement) (ha : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hR : Rt M (LB M Q B) t ≠ LB M Q B) {m : G} (hm : m ∈ M)
    (ht : t ∈ conjSubgroup m (LB M Q B)) {X : Subgroup G}
    (hLX : conjSubgroup m (LB M Q B) ≤ X)
    (hsup : ∀ r ∈ Rt M (LB M Q B) t, ∃ x ∈ X, x⁻¹ * r ∈ hc.CN t) :
    Rt M (LB M Q B) t ≤ X := by
  classical
  have hcC := hc.conj_of_mem hm
  have hsC := sec5Hyp_conj hc hm hs ht
  have hLC : LB M Q (conjSubgroup m B) = conjSubgroup m (LB M Q B) := hc.LB_conj hm
  have hRC : Rt M (LB M Q (conjSubgroup m B)) t = Rt M (LB M Q B) t := (rt_vt_conj hc hm t).1
  have hRC' : Rt M (LB M Q (conjSubgroup m B)) t ≠ LB M Q (conjSubgroup m B) := by
    rw [hRC, hLC]
    intro heq
    apply hR
    have hle : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
    rw [heq] at hle ⊢
    have hc1 : Nat.card (conjSubgroup m (LB M Q B)) = Nat.card (LB M Q B) :=
      card_conjSubgroup m _
    exact (Subgroup.eq_of_le_of_card_ge hle hc1.le).symm
  have hfirst := ha G M Q Z (conjSubgroup m B) hcC n hsC.width hsC.n_gt hsC.noA2 hsC.gen t hsC.mem
    hsC.notQ hRC'
  rw [Ctx.CN_conj_eq hc hm t, hRC, hLC] at hfirst
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have h35C := (stroth_3_5 h34 hcC hsC.width hsC.n_gt hsC.noA2 hsC.gen).2.1
  have hNX : hc.CN t ≤ X := by
    rw [hfirst]
    refine iSup₂_le fun h hh => ?_
    intro l hl'
    obtain ⟨hl, hlN⟩ := Subgroup.mem_inf.mp hl'
    obtain ⟨x, hxX, hxn⟩ := hsup h hh
    set n' : G := x⁻¹ * h with hn'
    have hn'norm : n' ∈ Subgroup.normalizer (conjSubgroup m (LB M Q B) : Set G) := by
      have := hcC.CN_normalizes_conj_LB h35C hsC.mem (h := 1) (Rt M _ t).one_mem
        (show n' ∈ hcC.CN t by rw [Ctx.CN_conj_eq hc hm t]; exact hxn)
      rwa [hLC, conjSubgroup_one] at this
    rw [mem_conjSubgroup] at hl
    have hh' : h = x * n' := by rw [hn']; group
    have e : h⁻¹ * l * h = n'⁻¹ * (x⁻¹ * l * x) * n' := by rw [hh']; group
    rw [e] at hl
    have hy : x⁻¹ * l * x ∈ conjSubgroup m (LB M Q B) := by
      refine (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn'norm) (x⁻¹ * l * x)).mpr ?_
      simpa using hl
    have e2 : l = x * (x⁻¹ * l * x) * x⁻¹ := by group
    rw [e2]
    exact X.mul_mem (X.mul_mem hxX (hLX hy)) (X.inv_mem hxX)
  intro r hr
  obtain ⟨x, hxX, hxn⟩ := hsup r hr
  have : r = x * (x⁻¹ * r) := by group
  rw [this]
  exact X.mul_mem hxX (hNX hxn)

end CFSG.RankThree.GF2n.Stroth80
