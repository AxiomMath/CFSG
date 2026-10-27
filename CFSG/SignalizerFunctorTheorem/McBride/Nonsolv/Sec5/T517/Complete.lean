module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T517.WAut
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Sections
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T517.Key

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517

variable {Γ : Type*} [Group Γ] [Finite Γ]

@[expose] noncomputable def autImage (H X : Subgroup Γ) : Subgroup (MulAut ↥(kOf H)) :=
  (X.subgroupOf H).map (autH H)

theorem mem_autImage_iff {H X : Subgroup Γ} {φ : MulAut ↥(kOf H)} :
    φ ∈ autImage H X ↔ ∃ x : ↥H, (x : Γ) ∈ X ∧ autH H x = φ := by
  simp only [autImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem card_autImage {H X : Subgroup Γ} (hsol : sol H = ⊥) (hXH : X ≤ H) :
    Nat.card ↥(autImage H X) = Nat.card ↥X := by
  rw [autImage, Subgroup.card_map_of_injective (autH_injective hsol)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv

theorem autImage_mono {H X Y : Subgroup Γ} (h : X ≤ Y) : autImage H X ≤ autImage H Y :=
  Subgroup.map_mono (fun _ hx => h hx)

variable {p : ℕ} {H B : Subgroup Γ} {θ : Γ → Subgroup Γ}

namespace Setting

variable (S : Setting p H B θ)

include S

theorem conj_mem_range {φ : MulAut ↥(kOf H)} (hφ : φ ∈ S.thetaAut.range) {b : Γ} (hb : b ∈ B) :
    autH H ⟨b, S.le hb⟩ * φ * (autH H ⟨b, S.le hb⟩)⁻¹ ∈ S.thetaAut.range := by
  rw [S.mem_range_thetaAut_iff] at hφ ⊢
  intro J hJ
  obtain ⟨w, hw, h⟩ := hφ (J.map (MulAut.conj b⁻¹).toMonoidHom) (S.map_conj_mem (inv_mem hb) hJ)
  exact ⟨w, hw, S.actsOn_conj hb hw h⟩

theorem autImage_le_normalizer :
    autImage H B ≤ Subgroup.normalizer (S.thetaAut.range : Set (MulAut ↥(kOf H))) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha k hk
  obtain ⟨y, hyB, rfl⟩ := mem_autImage_iff.mp ha
  exact S.conj_mem_range hk hyB

theorem coprime_range : Nat.Coprime p (Nat.card S.thetaAut.range) := by
  have e : (↥(lcal H) → ↥(thetaOf θ B)) ≃* S.thetaAut.range :=
    MonoidHom.ofInjective S.thetaAut_injective
  rw [← Nat.card_congr e.toEquiv, Nat.card_fun]
  exact Nat.Coprime.pow_right _ S.coprime_thetaOf

theorem actsOn_map_conj {J : Subgroup Γ} {w : Γ} (hw : w ∈ thetaOf θ B) {φ : MulAut ↥(kOf H)}
    {e : Γ} (he : e ∈ B)
    (hcomm : autH H ⟨e, S.le he⟩ * φ = φ * autH H ⟨e, S.le he⟩) (h : ActsOn J w φ) :
    ActsOn (J.map (MulAut.conj e).toMonoidHom) w φ := by
  intro j hj
  have hew : Commute w e :=
    (Subgroup.mem_centralizer_iff.mp (S.thetaOf_le_centralizer hw) e he).symm
  set j₀ : ↥(kOf H) := (autH H ⟨e⁻¹, inv_mem (S.le he)⟩) j with hj₀
  have hj₀J : (j₀ : Γ) ∈ J := by
    obtain ⟨y, hy, hyj⟩ := hj
    have : (j₀ : Γ) = y := by
      show e⁻¹ * (j : Γ) * e⁻¹⁻¹ = y
      rw [← hyj]
      simp [mul_assoc]
    rw [this]
    exact hy
  have hjeq : autH H ⟨e, S.le he⟩ j₀ = j := by
    apply Subtype.ext
    show e * (e⁻¹ * (j : Γ) * e⁻¹⁻¹) * e⁻¹ = j
    group
  have h1 := h j₀ hj₀J
  have h2 : ((φ (autH H ⟨e, S.le he⟩ j₀) : ↥(kOf H)) : Γ) =
      ((autH H ⟨e, S.le he⟩ (φ j₀) : ↥(kOf H)) : Γ) :=
    congrArg (fun m : MulAut ↥(kOf H) => ((m j₀ : ↥(kOf H)) : Γ)) hcomm.symm
  have hjeq' : e * (j₀ : Γ) * e⁻¹ = j := congrArg Subtype.val hjeq
  have h3 : ((φ j : ↥(kOf H)) : Γ) = e * ((φ j₀ : ↥(kOf H)) : Γ) * e⁻¹ := by
    conv_lhs => rw [← hjeq]
    rw [h2]
    rfl
  rw [h3, h1, ← hjeq']
  calc e * (w * (j₀ : Γ) * w⁻¹) * e⁻¹ = (e * w) * (j₀ : Γ) * (w⁻¹ * e⁻¹) := by group
    _ = (w * e) * (j₀ : Γ) * (e⁻¹ * w⁻¹) := by rw [hew.eq.symm, hew.inv_inv.eq]
    _ = w * (e * (j₀ : Γ) * e⁻¹) * w⁻¹ := by group

theorem commute_autH_of_mem_zpowers {φ : MulAut ↥(kOf H)} {b : Γ} (hb : b ∈ B)
    (hφ : φ ∈ Subgroup.centralizer ({autH H ⟨b, S.le hb⟩} : Set (MulAut ↥(kOf H)))) {e : Γ}
    (he : e ∈ Subgroup.zpowers b) :
    autH H ⟨e, S.le (Subgroup.zpowers_le.mpr hb he)⟩ * φ =
      φ * autH H ⟨e, S.le (Subgroup.zpowers_le.mpr hb he)⟩ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  have h1 : Commute φ (autH H ⟨b, S.le hb⟩) := Subgroup.mem_centralizer_singleton_iff.mp hφ
  have h2 : autH H ⟨b ^ n, S.le (Subgroup.zpowers_le.mpr hb he)⟩ =
      (autH H ⟨b, S.le hb⟩) ^ n := by
    rw [← map_zpow]
    rfl
  rw [h2]
  exact (h1.zpow_right n).eq.symm

theorem card_inf_centralizer_le {b : Γ} (hb : b ∈ B) (hb1 : b ≠ 1) :
    Nat.card ↥(S.thetaAut.range ⊓ Subgroup.centralizer
      ({autH H ⟨b, S.le hb⟩} : Set (MulAut ↥(kOf H)))) ≤ Nat.card ↥(thetaOf θ B) ^ p := by
  classical
  have hp := S.prime
  have hB := S.elemAbelian
  have hEB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
  obtain ⟨F, hFB, -, hEF, hsup⟩ :=
    exists_complement_containing hp hB hEB (bot_le : ⊥ ≤ B) (inf_bot_eq (Subgroup.zpowers b))
  have hEcard : Nat.card (Subgroup.zpowers b) = p := by
    have := Fact.mk hp
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hB.2 b hb) hb1
  have hFcard : Nat.card F = p := by
    have h := card_mul_card_complement hB hEB hFB hEF hsup
    rw [hEcard, S.card] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h]; ring)
  obtain ⟨J₀, hJ₀⟩ := S.nonempty
  have hdecomp : ∀ J ∈ lcal H, ∃ e ∈ Subgroup.zpowers b, ∃ f ∈ F,
      J = (J₀.map (MulAut.conj f).toMonoidHom).map (MulAut.conj e).toMonoidHom := by
    intro J hJ
    obtain ⟨c, hc, rfl⟩ := S.trans J₀ hJ₀ J hJ
    have hc' : c ∈ Subgroup.zpowers b ⊔ F := hsup ▸ hc
    obtain ⟨e, he, f, hf, rfl⟩ := (mem_sup_iff_of_commute (fun x hx y hy =>
      comm_of_mem_of_isMulCommutative hB.1 (hEB hx) (hFB hy))).mp hc'
    exact ⟨e, he, f, hf, (map_conj_map_conj J₀ f e).symm⟩
  set C := S.thetaAut.range ⊓ Subgroup.centralizer
    ({autH H ⟨b, S.le hb⟩} : Set (MulAut ↥(kOf H))) with hC
  have hact : ∀ (φ : ↥C) (f : ↥F), ∃ w ∈ thetaOf θ B,
      ActsOn (J₀.map (MulAut.conj (f : Γ)).toMonoidHom) w (φ : MulAut ↥(kOf H)) := fun φ f =>
    (S.mem_range_thetaAut_iff.mp φ.2.1) _ (S.map_conj_mem (hFB f.2) hJ₀)
  let Φ : ↥C → (↥F → ↥(thetaOf θ B)) := fun φ f =>
    ⟨Classical.choose (hact φ f), (Classical.choose_spec (hact φ f)).1⟩
  have hΦ : Function.Injective Φ := by
    intro φ φ' h
    apply Subtype.ext
    apply S.hK.ext_of_forall_mem
    intro J hJ x hx
    obtain ⟨e, he, f, hf, rfl⟩ := hdecomp J hJ
    have hw : Classical.choose (hact φ ⟨f, hf⟩) = Classical.choose (hact φ' ⟨f, hf⟩) :=
      congrArg Subtype.val (congrFun h ⟨f, hf⟩)
    have h1 := S.actsOn_map_conj (Classical.choose_spec (hact φ ⟨f, hf⟩)).1 (hEB he)
      (S.commute_autH_of_mem_zpowers hb φ.2.2 he) (Classical.choose_spec (hact φ ⟨f, hf⟩)).2
    have h2 := S.actsOn_map_conj (Classical.choose_spec (hact φ' ⟨f, hf⟩)).1 (hEB he)
      (S.commute_autH_of_mem_zpowers hb φ'.2.2 he) (Classical.choose_spec (hact φ' ⟨f, hf⟩)).2
    rw [← hw] at h2
    exact Subtype.ext ((h1 ⟨x, S.hK.le hJ hx⟩ hx).trans (h2 ⟨x, S.hK.le hJ hx⟩ hx).symm)
  calc Nat.card ↥C ≤ Nat.card (↥F → ↥(thetaOf θ B)) := Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card ↥(thetaOf θ B) ^ p := by rw [Nat.card_fun, hFcard]

theorem card_apply_eq {b : Γ} (hb : b ∈ B) (hb1 : b ≠ 1) :
    Nat.card ↥(θ b) = Nat.card ↥(thetaOf θ B) ^ p := by
  obtain ⟨e⟩ := S.iso b hb hb1
  rw [← Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin p),
    Fintype.card_fin]

theorem inf_centralizer_eq_autImage {b : Γ} (hb : b ∈ B) (hb1 : b ≠ 1) :
    S.thetaAut.range ⊓ Subgroup.centralizer ({autH H ⟨b, S.le hb⟩} : Set (MulAut ↥(kOf H))) =
      autImage H (θ b) := by
  have hle : autImage H (θ b) ≤ S.thetaAut.range ⊓ Subgroup.centralizer
      ({autH H ⟨b, S.le hb⟩} : Set (MulAut ↥(kOf H))) := by
    intro φ hφ
    obtain ⟨x, hx, rfl⟩ := mem_autImage_iff.mp hφ
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [S.autH_mem_range_iff]
      exact fun J hJ => S.exists_conj_of_mem_apply hb hb1 hx hJ
    · rw [Subgroup.mem_centralizer_singleton_iff]
      show autH H x * autH H ⟨b, S.le hb⟩ = autH H ⟨b, S.le hb⟩ * autH H x
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
        (S.functor.le_centralizer b hb hb1 hx))
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_autImage S.sol_eq_bot (S.le_H b hb hb1), S.card_apply_eq hb hb1]
  exact S.card_inf_centralizer_le hb hb1

theorem range_le_autImage_thetaSup : S.thetaAut.range ≤ autImage H (thetaSup B θ) := by
  have hcomm : IsMulCommutative B := S.elemAbelian.1
  have hA : IsElemAbelian p (autImage H B) := by
    refine ⟨?_, ?_⟩
    · show IsMulCommutative ((B.subgroupOf H).map (autH H))
      infer_instance
    · intro a ha
      obtain ⟨y, hy, rfl⟩ := mem_autImage_iff.mp ha
      rw [← map_pow]
      have : y ^ p = 1 := Subtype.ext (S.elemAbelian.2 y hy)
      rw [this, map_one]
  have hrank : p ^ 2 ≤ Nat.card ↥(autImage H B) := by
    rw [card_autImage S.sol_eq_bot S.le, S.card]
  have hgen := iSup_inf_centralizer S.prime hA hrank S.autImage_le_normalizer S.coprime_range
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  obtain ⟨y, hy, rfl⟩ := mem_autImage_iff.mp ha
  have hy1 : (y : Γ) ≠ 1 := fun h => ha1 (by rw [show y = 1 from Subtype.ext h, map_one])
  exact (S.inf_centralizer_eq_autImage hy hy1).le.trans (autImage_mono (le_thetaSup hy hy1))

theorem thetaSup_le_H : thetaSup B θ ≤ H := thetaSup_le S.le_H

theorem mem_thetaSup_iff {x : Γ} :
    x ∈ thetaSup B θ ↔ ∃ hx : x ∈ H, autH H ⟨x, hx⟩ ∈ S.thetaAut.range := by
  constructor
  · intro hx
    have hle : thetaSup B θ ≤ ((S.thetaAut.range).comap (autH H)).map H.subtype := by
      refine thetaSup_le fun a ha ha1 x hx => ?_
      refine ⟨⟨x, S.le_H a ha ha1 hx⟩, ?_, rfl⟩
      show autH H ⟨x, _⟩ ∈ S.thetaAut.range
      rw [S.autH_mem_range_iff]
      exact fun J hJ => S.exists_conj_of_mem_apply ha ha1 hx hJ
    obtain ⟨y, hy, rfl⟩ := hle hx
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    obtain ⟨y, hy, hyx⟩ := mem_autImage_iff.mp (S.range_le_autImage_thetaSup h)
    have : y = ⟨x, hx⟩ := autH_injective S.sol_eq_bot hyx
    rw [this] at hy
    exact hy

theorem thetaSup_coprime : Nat.Coprime p (Nat.card ↥(thetaSup B θ)) := by
  have h1 : autImage H (thetaSup B θ) ≤ S.thetaAut.range := by
    intro φ hφ
    obtain ⟨x, hx, rfl⟩ := mem_autImage_iff.mp hφ
    exact (S.mem_thetaSup_iff.mp hx).choose_spec
  have h2 : Nat.card ↥(autImage H (thetaSup B θ)) ∣ Nat.card S.thetaAut.range :=
    Subgroup.card_dvd_of_le h1
  rw [card_autImage S.sol_eq_bot S.thetaSup_le_H] at h2
  exact S.coprime_range.coprime_dvd_right h2

theorem thetaSup_inf_centralizer_le {a : Γ} (ha : a ∈ B) (ha1 : a ≠ 1) :
    thetaSup B θ ⊓ Subgroup.centralizer ({a} : Set Γ) ≤ θ a := by
  rintro x hx
  obtain ⟨hxW, hxa⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxH, hxr⟩ := S.mem_thetaSup_iff.mp hxW
  have hmem : autH H ⟨x, hxH⟩ ∈ S.thetaAut.range ⊓ Subgroup.centralizer
      ({autH H ⟨a, S.le ha⟩} : Set (MulAut ↥(kOf H))) := by
    refine Subgroup.mem_inf.mpr ⟨hxr, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show autH H ⟨x, hxH⟩ * autH H ⟨a, S.le ha⟩ = autH H ⟨a, S.le ha⟩ * autH H ⟨x, hxH⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxa)
  rw [S.inf_centralizer_eq_autImage ha ha1] at hmem
  obtain ⟨y, hy, hyx⟩ := mem_autImage_iff.mp hmem
  have : y = ⟨x, hxH⟩ := autH_injective S.sol_eq_bot hyx
  rw [this] at hy
  exact hy

theorem thetaSup_hypB : signalizerMcBrideHypothesisB p (thetaSup B θ) := by
  obtain ⟨b, hb, hb1⟩ := S.exists_ne_one
  refine signalizerMcBrideHypothesisB_iff.mpr ⟨S.prime, S.thetaSup_coprime, ?_⟩
  intro S' _ _ _ hS hnc
  let g : ↥(thetaSup B θ) →* ↥S.thetaAut.range :=
    ((autH H).comp (Subgroup.inclusion S.thetaSup_le_H)).codRestrict _
      (fun x => (S.mem_thetaSup_iff.mp x.2).choose_spec)
  have hg : Function.Injective g := by
    intro _ _ h
    have h' := congrArg Subtype.val h
    exact Subgroup.inclusion_injective S.thetaSup_le_H (autH_injective S.sol_eq_bot h')
  have h1 : IsSectionOf S' (↥(lcal H) → ↥(thetaOf θ B)) :=
    (hS.of_injective g hg).trans
      (IsSectionOf.of_mulEquiv (MonoidHom.ofInjective S.thetaAut_injective))
  obtain ⟨J, hJ⟩ := IsSectionOf.of_pi hnc h1
  exact signalizerMcBrideHypothesisA_of_isSectionOf (S.hypB b hb hb1)
    (isSectionOf_of_le (thetaOf_le_apply hb hb1) hJ) hnc

theorem thetaSup_mem_Msig : thetaSup B θ ∈ Msig p B θ :=
  ⟨S.functor.normalizes_thetaSup, S.thetaSup_coprime,
    fun _ ha ha1 => S.thetaSup_inf_centralizer_le ha ha1, S.thetaSup_hypB⟩

theorem isGreatest_thetaSup : IsGreatest (Msig p B θ) (thetaSup B θ) :=
  ⟨S.thetaSup_mem_Msig, fun _ hX =>
    le_thetaSup_of_mem_signalizers S.prime S.elemAbelian le_rfl S.card.ge hX⟩

end Setting

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517
