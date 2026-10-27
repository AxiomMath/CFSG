module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3Early
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3GeomTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenGen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_14E (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, ¬ c.E ≤ centralizer (c.V : Set G)

namespace Ctx2311

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)

theorem mem_point_of_mem_conj (hPt : ∀ v ∈ c.V, ∃ k ∈ c.N, v ∈ conjSubgroup D.Z k)
    {g v : G} (hv : v ∈ conjSubgroup c.V g) :
    ∃ k ∈ c.N, v ∈ conjSubgroup D.Z (k * g) := by
  rw [mem_conjSubgroup_iff] at hv
  obtain ⟨k, hkN, hkv⟩ := hPt (g * v * g⁻¹) hv
  refine ⟨k, hkN, ?_⟩
  rw [mem_conjSubgroup_iff] at hkv ⊢
  have hfac : (k * g) * v * (k * g)⁻¹ = k * (g * v * g⁻¹) * k⁻¹ := by group
  rw [hfac]
  exact hkv

theorem W_le_centralizer_point (h4 : S23_4 D Ch) (h1930 : H1930 D) (h : G) {d : G}
    (hd : d ∈ conjSubgroup D.Z h) (hdW : d ∈ centralizer (c.W : Set G)) (hd1 : d ≠ 1) :
    c.W ≤ centralizer (conjSubgroup D.Z h : Set G) := by
  have hWT : c.W ≤ D.T := (Ctx2311.W_le_V c).trans (c.V_le_T h4 h1930)
  intro w hw
  have hwp : w * d * w⁻¹ = d := by
    have hcomm := (Subgroup.mem_centralizer_iff.mp hdW) w hw
    rw [hcomm]
    group
  have hinf : conjSubgroup D.Z h ⊓ conjSubgroup (conjSubgroup D.Z h) w ≠ ⊥ := by
    intro hbot
    have hd0 : d ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hd, mem_conjSubgroup_iff.mpr (hwp.symm ▸ hd)⟩
    exact hd1 (Subgroup.mem_bot.mp hd0)
  have hEq : conjSubgroup (conjSubgroup D.Z h) w = conjSubgroup D.Z h :=
    c.conjSubgroup_TI h4 h1930 h w hinf
  have hwN : w ∈ normalizer (conjSubgroup D.Z h : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hEq
  have hw2 : ∃ j : ℕ, orderOf w = 2 ^ j := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp D.sylowM.isPGroup ⟨w, hWT hw⟩
    exact ⟨j, by rw [← Subgroup.orderOf_mk w (hWT hw)]; exact hj⟩
  have hcent := c.conjSubgroup_twoElement_centralizes h4 h1930 h hwN hw2
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hcomm : w * p = p * w := by
    have h := congrArg (fun x => x * w) (hcent p hp)
    simpa [mul_assoc] using h
  exact hcomm.symm

private theorem exists_mem_X_not_mem_M (c : Ctx2311 D Ch) : ∃ x ∈ c.X, x ∉ D.M := by
  by_contra h
  apply c.hXM
  intro x hx
  by_contra hxM
  exact h ⟨x, hx, hxM⟩

private theorem W_eq_sup_conj (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hLine : ∀ k₁ ∈ c.N, ∀ k₂ ∈ c.N, conjSubgroup D.Z k₁ ≠ conjSubgroup D.Z k₂ →
      ∃ k ∈ c.N, conjSubgroup D.Z k₁ ⊔ conjSubgroup D.Z k₂ = conjSubgroup c.W k)
    {x : G} (hxX : x ∈ c.X) (hxM : x ∉ D.M) :
    c.W = D.Z ⊔ conjSubgroup D.Z x := by
  have hxN : x ∈ c.N :=
    ((c.hX.1.2.1.trans (le_sup_left : c.L ≤ c.L ⊔ D.T)).trans
      (Ctx23L.sup_le_N D Ch c.toCtx23L)) hxX
  have hPleW : conjSubgroup D.Z x ≤ c.W := by
    rw [Ctx2311.W, uc22br4_conjClosure_eq c.X D.Z]
    exact le_iSup (fun g : ↥c.X => D.Z.map (MulAut.conj (g : G)).toMonoidHom)
      ⟨x⁻¹, c.X.inv_mem hxX⟩
  have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
    rw [← (h4 h1930 c.toCtx23L).1]
    exact D.normalizer_U_eq
  have hPne : conjSubgroup D.Z x ≠ D.Z := by
    intro h
    exact hxM (hNZ ▸ conjSubgroup_eq_iff_mem_normalizer.mp h)
  have hne : conjSubgroup D.Z (1 : G) ≠ conjSubgroup D.Z x := by
    rw [conjSubgroup_one]
    exact fun h => hPne h.symm
  obtain ⟨k, -, hk⟩ := hLine 1 c.N.one_mem x hxN hne
  rw [conjSubgroup_one] at hk
  have hcard : Nat.card c.W = Nat.card ↥(D.Z ⊔ conjSubgroup D.Z x) := by
    rw [hk, E3.card_conjSubgroup]
  exact (Subgroup.eq_of_le_of_card_ge
    (sup_le (uc22p22v_le_conjClosure c.X D.Z) hPleW) hcard.le).symm

private theorem exists_ne_one_mem_conj (x : G) :
    ∃ p ∈ conjSubgroup D.Z x, p ≠ 1 := by
  have hPne : conjSubgroup D.Z x ≠ ⊥ := by
    intro h
    apply uc22main1_Z_ne_bot D
    have hc := E3.card_conjSubgroup D.Z x
    rw [h] at hc
    simpa using hc.symm
  obtain ⟨p, hp⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  exact ⟨(p : G), p.2, fun h1 => hp (Subtype.ext h1)⟩

private theorem mem_centralizer_conj_of_commutes (c : Ctx2311 D Ch) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) {x a p : G} (hpP : p ∈ conjSubgroup D.Z x) (hp1 : p ≠ 1)
    (haT : a ∈ D.T) (hap : a * p = p * a) :
    a ∈ Subgroup.centralizer (conjSubgroup D.Z x : Set G) := by
  have ha2 : ∃ j : ℕ, orderOf a = 2 ^ j := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp D.sylowM.isPGroup ⟨a, haT⟩
    exact ⟨j, by rw [← Subgroup.orderOf_mk a haT]; exact hj⟩
  have hinf : conjSubgroup D.Z x ⊓ conjSubgroup (conjSubgroup D.Z x) a ≠ ⊥ := by
    intro hbot
    have hpa : a * p * a⁻¹ = p := by rw [hap]; group
    have hp0 : p ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hpP, mem_conjSubgroup_iff.mpr (hpa.symm ▸ hpP)⟩
    exact hp1 (Subgroup.mem_bot.mp hp0)
  have hEq : conjSubgroup (conjSubgroup D.Z x) a = conjSubgroup D.Z x :=
    c.conjSubgroup_TI h4 h1930 x a hinf
  have haN : a ∈ normalizer (conjSubgroup D.Z x : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hEq
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have h := c.conjSubgroup_twoElement_centralizes h4 h1930 x haN ha2 y hy
  calc y * a = (a * y * a⁻¹) * a := by rw [h]
    _ = a * y := by group

private def commutatorHom {A : Subgroup G} (hAT : A ≤ D.T) (hWT : ⁅c.W, D.T⁆ ≤ D.Z)
    {p : G} (hpW : p ∈ c.W) : ↥A →* ↥D.Z where
  toFun a := ⟨⁅p, (a : G)⁆, hWT (Subgroup.commutator_mem_commutator hpW (hAT a.2))⟩
  map_one' := Subtype.ext (by simp [commutatorElement_def])
  map_mul' a b := by
    apply Subtype.ext
    show ⁅p, ((a : G) * (b : G))⁆ = ⁅p, (a : G)⁆ * ⁅p, (b : G)⁆
    have h1 : ⁅p, ((a : G) * (b : G))⁆ =
        ⁅p, (a : G)⁆ * ((a : G) * ⁅p, (b : G)⁆ * (a : G)⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    have h2 : (a : G) * ⁅p, (b : G)⁆ * (a : G)⁻¹ = ⁅p, (b : G)⁆ := by
      have hc := (Subgroup.mem_centralizer_iff.mp
        (uc22main1_T_le_centralizer D (hAT a.2))) ⁅p, (b : G)⁆
        (hWT (Subgroup.commutator_mem_commutator hpW (hAT b.2)))
      rw [← hc]
      group
    rw [h1, h2]

private theorem commutatorHom_apply {A : Subgroup G} (hAT : A ≤ D.T)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z) {p : G} (hpW : p ∈ c.W) (a : ↥A) :
    ((commutatorHom c hAT hWT hpW a : ↥D.Z) : G) = ⁅p, (a : G)⁆ := rfl

private theorem commutatorHom_ker_le (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {A P : Subgroup G} (hAT : A ≤ D.T) (hWT : ⁅c.W, D.T⁆ ≤ D.Z) {p x : G}
    (hpW : p ∈ c.W) (hpP : p ∈ P) (hP : P = conjSubgroup D.Z x) (hp1 : p ≠ 1)
    (hW : c.W = D.Z ⊔ P) :
    ∀ a : ↥A, a ∈ (commutatorHom c hAT hWT hpW).ker →
      (a : G) ∈ A ⊓ centralizer (c.W : Set G) := by
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have hpa : ⁅p, (a : G)⁆ = 1 := by
    have h := congrArg Subtype.val ha
    rw [commutatorHom_apply] at h
    simpa using h
  have hcomm : p * (a : G) = (a : G) * p := by
    have h := hpa
    rw [commutatorElement_def] at h
    calc p * (a : G) = (p * (a : G) * p⁻¹ * (a : G)⁻¹) * ((a : G) * p) := by group
      _ = 1 * ((a : G) * p) := by rw [h]
      _ = (a : G) * p := one_mul _
  have hap : (a : G) * p = p * (a : G) := hcomm.symm
  refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
  have haZ : (a : G) ∈ centralizer (D.Z : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (uc22main1_T_le_centralizer D (hAT a.2))) z hz
  have haP : (a : G) ∈ centralizer (P : Set G) :=
    hP.symm ▸ mem_centralizer_conj_of_commutes c h4 h1930 (hP ▸ hpP) hp1 (hAT a.2) hap
  rw [hW, Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  intro h hh
  rcases hh with hz | hq
  · exact (Subgroup.mem_centralizer_iff.mp haZ) h hz
  · exact (Subgroup.mem_centralizer_iff.mp haP) h hq

theorem card_le_card_Z_mul (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : ⁅c.W, D.T⁆ ≤ D.Z)
    (hLine : ∀ k₁ ∈ c.N, ∀ k₂ ∈ c.N, conjSubgroup D.Z k₁ ≠ conjSubgroup D.Z k₂ →
      ∃ k ∈ c.N, conjSubgroup D.Z k₁ ⊔ conjSubgroup D.Z k₂ = conjSubgroup c.W k)
    {A : Subgroup G} (hAT : A ≤ D.T) :
    Nat.card A ≤ Nat.card D.Z * Nat.card ↥(A ⊓ centralizer (c.W : Set G)) := by
  obtain ⟨x, hxX, hxM⟩ := exists_mem_X_not_mem_M c
  have hW := W_eq_sup_conj c h4 h1930 hLine hxX hxM
  obtain ⟨p, hpP, hp1⟩ := exists_ne_one_mem_conj x
  have hpW : p ∈ c.W := hW.symm ▸ Subgroup.mem_sup_right hpP
  let φ := commutatorHom c hAT hWT hpW
  have hker : ∀ a : ↥A, a ∈ φ.ker → (a : G) ∈ A ⊓ centralizer (c.W : Set G) :=
    commutatorHom_ker_le c h4 h1930 hAT hWT hpW hpP rfl hp1 hW
  have hkermap : φ.ker.map A.subtype ≤ A ⊓ centralizer (c.W : Set G) := by
    rintro - ⟨a, ha, rfl⟩
    exact hker a ha
  have hcardker : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ centralizer (c.W : Set G)) := by
    have h := Subgroup.card_le_of_le hkermap
    rwa [Subgroup.card_map_of_injective (f := A.subtype) (Subtype.coe_injective)] at h
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range ≤ Nat.card D.Z := by
    have h := Subgroup.card_le_of_le (le_top : φ.range ≤ ⊤)
    simpa using h
  calc Nat.card A = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ ≤ Nat.card ↥(A ⊓ centralizer (c.W : Set G)) * Nat.card D.Z :=
        Nat.mul_le_mul hcardker hrange
    _ = Nat.card D.Z * Nat.card ↥(A ⊓ centralizer (c.W : Set G)) := Nat.mul_comm _ _

private theorem le_normalizer_conj_of_centralizes (c : Ctx2311 D Ch)
    {P₁ P₂ : Subgroup G} {k g : G}
    (hW' : P₁ ⊔ P₂ = conjSubgroup c.W (k * g))
    (h₁ : c.W ≤ centralizer (P₁ : Set G))
    (h₂ : c.W ≤ centralizer (P₂ : Set G)) :
    c.W ≤ normalizer (conjSubgroup c.W (k * g) : Set G) := by
  rw [← hW']
  refine (Subgroup.le_centralizer_iff.mpr (sup_le
    (Subgroup.le_centralizer_iff.mp h₁) (Subgroup.le_centralizer_iff.mp h₂))).trans ?_
  exact Subgroup.centralizer_le_normalizer (((P₁ ⊔ P₂ : Subgroup G)) : Set G)

private theorem sup_points_eq_conj_W (c : Ctx2311 D Ch)
    (hLine : ∀ k₁ ∈ c.N, ∀ k₂ ∈ c.N, conjSubgroup D.Z k₁ ≠ conjSubgroup D.Z k₂ →
      ∃ k ∈ c.N, conjSubgroup D.Z k₁ ⊔ conjSubgroup D.Z k₂ = conjSubgroup c.W k)
    {g k₁ k₂ : G} (hk₁ : k₁ ∈ c.N) (hk₂ : k₂ ∈ c.N)
    (hne : conjSubgroup D.Z (k₁ * g) ≠ conjSubgroup D.Z (k₂ * g)) :
    ∃ k ∈ c.N, conjSubgroup D.Z (k₁ * g) ⊔ conjSubgroup D.Z (k₂ * g) =
      conjSubgroup c.W (k * g) := by
  have hne' : conjSubgroup D.Z k₁ ≠ conjSubgroup D.Z k₂ := by
    intro h
    apply hne
    have h' := congrArg (fun A => conjSubgroup A g) h
    rwa [conjSubgroup_conjSubgroup (A := D.Z) (g := k₁) (h := g),
      conjSubgroup_conjSubgroup (A := D.Z) (g := k₂) (h := g)] at h'
  obtain ⟨k, hkN, hk⟩ := hLine k₁ hk₁ k₂ hk₂ hne'
  refine ⟨k, hkN, ?_⟩
  have e₁ : conjSubgroup D.Z (k₁ * g) = conjSubgroup (conjSubgroup D.Z k₁) g :=
    (conjSubgroup_conjSubgroup (A := D.Z) (g := k₁) (h := g)).symm
  have e₂ : conjSubgroup D.Z (k₂ * g) = conjSubgroup (conjSubgroup D.Z k₂) g :=
    (conjSubgroup_conjSubgroup (A := D.Z) (g := k₂) (h := g)).symm
  have e₃ : conjSubgroup c.W (k * g) = conjSubgroup (conjSubgroup c.W k) g :=
    (conjSubgroup_conjSubgroup (A := c.W) (g := k) (h := g)).symm
  have hmap : conjSubgroup (conjSubgroup D.Z k₁ ⊔ conjSubgroup D.Z k₂) g =
      conjSubgroup (conjSubgroup D.Z k₁) g ⊔ conjSubgroup (conjSubgroup D.Z k₂) g :=
    Subgroup.map_sup (conjSubgroup D.Z k₁) (conjSubgroup D.Z k₂)
      (MulAut.conj g⁻¹).toMonoidHom
  rw [e₁, e₂, e₃, ← hk, hmap]

private theorem normalizer_conj_le (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hNW : normalizer (c.W : Set G) ≤ c.N) {k g : G} (hkN : k ∈ c.N) :
    normalizer (conjSubgroup c.W (k * g) : Set G) ≤
      normalizer (conjSubgroup c.V g : Set G) := by
  have hNk : conjSubgroup c.N k = c.N :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hkN)
  have e : conjSubgroup c.N (k * g) = conjSubgroup (conjSubgroup c.N k) g :=
    (conjSubgroup_conjSubgroup (A := c.N) (g := k) (h := g)).symm
  have e' : conjSubgroup c.N g = normalizer (conjSubgroup c.V g : Set G) := by
    rw [← c.normalizer_V_eq h4 h1930]
    exact E3.conjSubgroup_normalizer c.V g
  have h1 := E3.conjSubgroup_mono_left (k * g) hNW
  have h2 : conjSubgroup (normalizer (c.W : Set G)) (k * g) =
      normalizer (conjSubgroup c.W (k * g) : Set G) :=
    E3.conjSubgroup_normalizer c.W (k * g)
  rw [h2, e, hNk, e'] at h1
  exact h1

theorem W_le_normalizer_conj_V (h4 : S23_4 D Ch) (h1930 : H1930 D) (h13 : S23_13 D Ch)
    (hLine : ∀ k₁ ∈ c.N, ∀ k₂ ∈ c.N, conjSubgroup D.Z k₁ ≠ conjSubgroup D.Z k₂ →
      ∃ k ∈ c.N, conjSubgroup D.Z k₁ ⊔ conjSubgroup D.Z k₂ = conjSubgroup c.W k)
    {g k₁ k₂ : G} (hk₁ : k₁ ∈ c.N) (hk₂ : k₂ ∈ c.N)
    (hne : conjSubgroup D.Z (k₁ * g) ≠ conjSubgroup D.Z (k₂ * g))
    (h₁ : c.W ≤ centralizer (conjSubgroup D.Z (k₁ * g) : Set G))
    (h₂ : c.W ≤ centralizer (conjSubgroup D.Z (k₂ * g) : Set G)) :
    c.W ≤ normalizer (conjSubgroup c.V g : Set G) := by
  obtain ⟨k, hkN, hW'⟩ := sup_points_eq_conj_W c hLine hk₁ hk₂ hne
  exact (le_normalizer_conj_of_centralizes c hW' h₁ h₂).trans
    (normalizer_conj_le c h4 h1930 (h13 h1930 c) hkN)

theorem conj_V_le_E (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hPt : ∀ v ∈ c.V, ∃ k ∈ c.N, v ∈ conjSubgroup D.Z k)
    {g z : G} (hzZ : z ∈ D.Z) (hzg : z ∈ conjSubgroup c.V g) (hz1 : z ≠ 1) :
    conjSubgroup c.V g ≤ c.E := by
  obtain ⟨k, hkN, hzP⟩ := mem_point_of_mem_conj c hPt hzg
  have hNZ : normalizer (D.Z : Set G) = D.M := by
    rw [← (h4 h1930 c.toCtx23L).1]
    exact D.normalizer_U_eq
  have hinf : D.Z ⊓ conjSubgroup D.Z (k * g) ≠ ⊥ := by
    intro hbot
    have hz0 : z ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hzZ, hzP⟩
    exact hz1 (Subgroup.mem_bot.mp hz0)
  have hkeq : conjSubgroup D.Z (k * g) = D.Z :=
    (c.Z_right_TI h4 h1930 (k * g)).resolve_left hinf
  have hkgM : k * g ∈ D.M := by
    rw [← hNZ]
    exact conjSubgroup_eq_iff_mem_normalizer.mp hkeq
  have hVk : conjSubgroup c.V (k * g) = conjSubgroup c.V g := by
    rw [← conjSubgroup_conjSubgroup (A := c.V) (g := k) (h := g)]
    congr 1
    exact conjSubgroup_eq_iff_mem_normalizer.mpr
      (uc22p22v_le_normalizer_conjClosure c.N D.Z hkN)
  rw [← hVk]
  rw [show conjSubgroup c.V (k * g) = c.V.map (MulAut.conj ((k * g)⁻¹)) from rfl]
  rw [Ctx23L.E, uc22br4_conjClosure_eq D.M c.V]
  exact le_iSup (fun m : ↥D.M => c.V.map (MulAut.conj (m : G)).toMonoidHom)
    ⟨(k * g)⁻¹, D.M.inv_mem hkgM⟩

end Ctx2311

private theorem card_Z_lt_card_D {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (hn : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hCard : Nat.card c.V = Nat.card D.Z ^ 3) {A : Subgroup G} (hAT : A ≤ D.T) {g : G}
    (hAg : A ≤ conjSubgroup c.V g) (hAm : E3.mQuot (conjSubgroup c.V g) A = 1)
    (hAcard : Nat.card A ≤
      Nat.card D.Z * Nat.card ↥(A ⊓ centralizer (c.W : Set G))) :
    Nat.card D.Z < Nat.card ↥(A ⊓ centralizer (c.W : Set G)) := by
  have hV2 : IsPGroup 2 ↥(conjSubgroup c.V g) :=
    ((c.isElemAbelian_V h4 h1930).map (MulAut.conj g⁻¹).toMonoidHom).isPGroup
  have hVcard : Nat.card (conjSubgroup c.V g) = Nat.card D.Z ^ 3 := by
    rw [E3.card_conjSubgroup, hCard]
  have hA2 : Nat.card (conjSubgroup c.V g) = 2 * Nat.card A := by
    rw [E3.card_eq_two_pow_mul hV2 hAg, hAm, pow_one]
  have h1 : Nat.card D.Z ^ 3 ≤
      2 * (Nat.card D.Z * Nat.card ↥(A ⊓ centralizer (c.W : Set G))) := by
    rw [← hVcard, hA2]
    exact Nat.mul_le_mul_left 2 hAcard
  have hZpos : 0 < Nat.card D.Z := Nat.card_pos
  have hmain : Nat.card D.Z ^ 2 ≤
      2 * Nat.card ↥(A ⊓ centralizer (c.W : Set G)) := by
    refine Nat.le_of_mul_le_mul_left ?_ hZpos
    calc Nat.card D.Z * Nat.card D.Z ^ 2 = Nat.card D.Z ^ 3 := by ring
      _ ≤ 2 * (Nat.card D.Z * Nat.card ↥(A ⊓ centralizer (c.W : Set G))) := h1
      _ = Nat.card D.Z * (2 * Nat.card ↥(A ⊓ centralizer (c.W : Set G))) := by ring
  have hq : 4 ≤ Nat.card D.Z := by
    have hZcard : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
        (c.isElemAbelian_Z h4 h1930)
    rw [hZcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 D.Z := Nat.pow_le_pow_right (by norm_num) hn
  have h2q : 2 * Nat.card D.Z < Nat.card D.Z ^ 2 := by nlinarith
  nlinarith

private theorem exists_two_points {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hPt : ∀ v ∈ c.V, ∃ k ∈ c.N, v ∈ conjSubgroup D.Z k) {A : Subgroup G}
    (hD : Nat.card D.Z < Nat.card ↥(A ⊓ centralizer (c.W : Set G))) {g : G}
    (hAg : A ≤ conjSubgroup c.V g) :
    ∃ k₁ ∈ c.N, ∃ k₂ ∈ c.N,
      conjSubgroup D.Z (k₁ * g) ≠ conjSubgroup D.Z (k₂ * g) ∧
      (∃ d ∈ conjSubgroup D.Z (k₁ * g) ⊓ (A ⊓ centralizer (c.W : Set G)), d ≠ 1) ∧
      (∃ d ∈ conjSubgroup D.Z (k₂ * g) ⊓ (A ⊓ centralizer (c.W : Set G)), d ≠ 1) := by
  have hDne : (A ⊓ centralizer (c.W : Set G)) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(A ⊓ centralizer (c.W : Set G)) = 1 := by rw [hbot]; simp
    have hpos : 0 < Nat.card D.Z := Nat.card_pos
    omega
  obtain ⟨d₁, hd₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  obtain ⟨k₁, hk₁, hd₁P₁⟩ := Ctx2311.mem_point_of_mem_conj c hPt (hAg d₁.2.1)
  have hP₁card : Nat.card (conjSubgroup D.Z (k₁ * g)) = Nat.card D.Z :=
    E3.card_conjSubgroup D.Z (k₁ * g)
  have hnotle : ¬ (A ⊓ centralizer (c.W : Set G)) ≤ conjSubgroup D.Z (k₁ * g) := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    rw [hP₁card] at hcard
    omega
  have hex : ∃ d ∈ (A ⊓ centralizer (c.W : Set G)), d ∉ conjSubgroup D.Z (k₁ * g) := by
    by_contra h
    exact hnotle fun d hd => by
      by_contra hd'
      exact h ⟨d, hd, hd'⟩
  obtain ⟨d₂, hd₂D, hd₂P₁⟩ := hex
  have hd₂1 : d₂ ≠ 1 := fun h => hd₂P₁ (h ▸ (conjSubgroup D.Z (k₁ * g)).one_mem)
  obtain ⟨k₂, hk₂, hd₂P₂⟩ := Ctx2311.mem_point_of_mem_conj c hPt (hAg hd₂D.1)
  refine ⟨k₁, hk₁, k₂, hk₂, ?_, ⟨(d₁ : G), ?_, ?_⟩, ⟨d₂, ?_, hd₂1⟩⟩
  · intro heq
    exact hd₂P₁ (heq ▸ hd₂P₂)
  · exact Subgroup.mem_inf.mpr ⟨hd₁P₁, d₁.2⟩
  · exact fun h => hd₁1 (Subtype.ext h)
  · exact Subgroup.mem_inf.mpr ⟨hd₂P₂, hd₂D⟩

private theorem false_of_gamma {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hPt : ∀ v ∈ c.V, ∃ k ∈ c.N, v ∈ conjSubgroup D.Z k) (hWT : ⁅c.W, D.T⁆ ≤ D.Z)
    {A : Subgroup G} (hAT : A ≤ D.T) {g : G} (hAg : A ≤ conjSubgroup c.V g)
    (hWN : c.W ≤ normalizer (conjSubgroup c.V g : Set G))
    (hEV : c.E ≤ centralizer (c.V : Set G))
    (hAW : ¬ A ≤ centralizer (c.W : Set G)) : False := by
  have hAW' : ∃ a ∈ A, a ∉ centralizer (c.W : Set G) := by
    by_contra h
    exact hAW fun a ha => by
      by_contra ha'
      exact h ⟨a, ha, ha'⟩
  obtain ⟨a, haA, haC⟩ := hAW'
  rw [Subgroup.mem_centralizer_iff] at haC
  push Not at haC
  obtain ⟨w, hwW, haw⟩ := haC
  have hz1 : ⁅w, a⁆ ≠ 1 := by
    intro h
    apply haw
    have h' : w * a * w⁻¹ * a⁻¹ = 1 := h
    calc w * a = (w * a * w⁻¹ * a⁻¹) * (a * w) := by group
      _ = a * w := by rw [h', one_mul]
  have hzZ : ⁅w, a⁆ ∈ D.Z := hWT (Subgroup.commutator_mem_commutator hwW (hAT haA))
  have hzVg : ⁅w, a⁆ ∈ conjSubgroup c.V g := by
    have h1 : w * a * w⁻¹ ∈ conjSubgroup c.V g :=
      (Subgroup.mem_normalizer_iff.mp (hWN hwW) a).mp (hAg haA)
    have h2 : a⁻¹ ∈ conjSubgroup c.V g := (conjSubgroup c.V g).inv_mem (hAg haA)
    simpa [commutatorElement_def] using (conjSubgroup c.V g).mul_mem h1 h2
  have hVgE : conjSubgroup c.V g ≤ c.E :=
    Ctx2311.conj_V_le_E c h4 h1930 hPt hzZ hzVg hz1
  exact hAW ((hAg.trans hVgE).trans
    (hEV.trans (Subgroup.centralizer_le (Ctx2311.W_le_V c))))

theorem s23_14E_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h13 : S23_13 D Ch)
    (hn : H1930 D → ∀ _ : Ctx2311 D Ch, 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNW1 : H1930 D → ∀ c : Ctx2311 D Ch,
      ¬ c.X ⊔ D.T ≤ normalizer (E3.wClos c.V 1 D.T : Set G))
    (hWT : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.W, D.T⁆ ≤ D.Z)
    (hPt : H1930 D → ∀ c : Ctx2311 D Ch, ∀ v ∈ c.V, ∃ k ∈ c.N,
      v ∈ conjSubgroup D.Z k)
    (hLine : H1930 D → ∀ c : Ctx2311 D Ch, ∀ k₁ ∈ c.N, ∀ k₂ ∈ c.N,
      conjSubgroup D.Z k₁ ≠ conjSubgroup D.Z k₂ →
        ∃ k ∈ c.N, conjSubgroup D.Z k₁ ⊔ conjSubgroup D.Z k₂ = conjSubgroup c.W k)
    (hCard : H1930 D → ∀ c : Ctx2311 D Ch, Nat.card c.V = Nat.card D.Z ^ 3)
    (hCW : H1930 D → ∀ c : Ctx2311 D Ch,
      D.T ⊓ centralizer (c.W : Set G) ≤ pCoreOf 2 (c.X ⊔ D.T)) :
    S23_14E D Ch := by
  intro h1930 c hEV
  obtain ⟨A, hAg, hAO⟩ := PartTwo.TwelveEighteen.exists_gammaSet_not_le_pCoreOf
    (V := c.V) (H := c.X ⊔ D.T) (S := D.T) (i := 1)
    (uc22p22ta_isSylowIn D le_sup_right) (hNW1 h1930 c)
  obtain ⟨hAT, g, hAgV, hAm⟩ := hAg
  have hAW : ¬ A ≤ centralizer (c.W : Set G) :=
    fun h => hAO ((le_inf hAT h).trans (hCW h1930 c))
  have hAcard := Ctx2311.card_le_card_Z_mul c h4 h1930 (hWT h1930 c) (hLine h1930 c) hAT
  have hDlt := card_Z_lt_card_D c h4 h1930 (hn h1930 c) (hCard h1930 c) hAT hAgV hAm hAcard
  obtain ⟨k₁, hk₁, k₂, hk₂, hne, ⟨d₁, hd₁, hd₁1⟩, ⟨d₂, hd₂, hd₂1⟩⟩ :=
    exists_two_points c (hPt h1930 c) hDlt hAgV
  have hW₁ := Ctx2311.W_le_centralizer_point c h4 h1930 (k₁ * g) hd₁.1 hd₁.2.2 hd₁1
  have hW₂ := Ctx2311.W_le_centralizer_point c h4 h1930 (k₂ * g) hd₂.1 hd₂.2.2 hd₂1
  have hWN := Ctx2311.W_le_normalizer_conj_V c h4 h1930 h13 (hLine h1930 c)
    hk₁ hk₂ hne hW₁ hW₂
  exact false_of_gamma c h4 h1930 (hPt h1930 c) (hWT h1930 c) hAT hAgV hWN hEV hAW

theorem s23_14_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) (h14E : S23_14E D Ch) :
    S23_14 D Ch := by
  intro h1930 c hphi
  apply h14E h1930 c
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥c.E) :=
    ⟨Ctx2311.isPGroup_E c h1930 h4 h12 (hVK h1930 c)⟩
  have heal : IsElementaryAbelian 2 ↥c.E :=
    (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := ↥c.E) (p := 2)).mp hphi
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvE : v ∈ c.E := uc22p22v_le_conjClosure D.M c.V hv
  exact congrArg Subtype.val (heal.is_comm.comm ⟨v, hvE⟩ ⟨e, he⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22
