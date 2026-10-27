module

public import CFSG.RankThree.GF2n.Stroth80.Sec714ModelStable
public import CFSG.RankThree.GF2n.Stroth80.Sec714ModelScalar
import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
import CFSG.RankThree.GF2n.Stroth80.Sec7EndModel
import CFSG.RankThree.GF2n.Stroth80.Sec37Commuting

public section

namespace CFSG.RankThree.GF2n.Stroth80.S714

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

structure MInputs : Prop where
  h34 : Stroth34Statement
  hRoot : Stroth310RootStatement
  h310chi : Stroth310ChiStatement
  h51 : Stroth51Statement
  h52a : Stroth52aStatement
  h52b : Stroth52bStatement
  hNO : Sec7NOrderStatement
  hZc : Sec7ZCardStatement
  hCRW : Sec7CRWStatement
  hMp : Sec7CentreMpStatement
  hZV : Sec7ZVStatement


section Phi

variable (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) {t r : G} (hs : Sec7Hyp hc n t)
  (hr : Sec7A hc t r)

@[expose] def phiSub : Submodule K (↥(wsub hS t) →ₗ[K] M₀.E) where
  toAddSubmonoid := (deltaGrp I.h310chi I.h52a hS hs hr (hc.CN t) le_rfl).toAddSubmonoid
  smul_mem' := by
    rintro k _ ⟨x, hx, rfl⟩
    obtain ⟨g', hg', hΔ⟩ := exists_delta_smul I.h34 I.hRoot I.h310chi I.h51 I.h52a I.h52b I.hNO
      I.hZc I.hCRW I.hMp hS hs hr (mk_mem_bar x hx) k
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_bar hg'
    exact ⟨y, hy, hΔ.symm.trans (delta_congr hS t rfl _ _)⟩

theorem mem_phiSub {f : ↥(wsub hS t) →ₗ[K] M₀.E} :
    f ∈ phiSub I hS hs hr ↔ ∃ x : ↥M, ∃ hx : (x : G) ∈ hc.CN t,
      f = delta hS t (QuotientGroup.mk x) (mem_bar_H0_of_CN (mk_mem_bar x hx)) := Iff.rfl

@[expose] noncomputable def pre (e : ↥(phiSub I hS hs hr)) : ↥M :=
  Classical.choose ((mem_phiSub I hS hs hr).mp e.2)

theorem pre_mem (e : ↥(phiSub I hS hs hr)) : (pre I hS hs hr e : G) ∈ hc.CN t :=
  (Classical.choose_spec ((mem_phiSub I hS hs hr).mp e.2)).1

theorem pre_spec (e : ↥(phiSub I hS hs hr)) :
    (e : ↥(wsub hS t) →ₗ[K] M₀.E) = delta hS t (QuotientGroup.mk (pre I hS hs hr e))
      (mem_bar_H0_of_CN (mk_mem_bar _ (pre_mem I hS hs hr e))) :=
  (Classical.choose_spec ((mem_phiSub I hS hs hr).mp e.2)).2

theorem delta_mem_phiSub {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    delta hS t g (mem_bar_H0_of_CN hg) ∈ phiSub I hS hs hr := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_bar hg
  exact ⟨x, hx, rfl⟩

end Phi

section Forms

variable (x₀ y₀ : M₀.E)

variable (ρ) in
@[expose] def Fv (g h : Mbar M Q) : K :=
  M₀.B (dmap ρ g x₀) (dmap ρ h y₀) - M₀.B (dmap ρ h x₀) (dmap ρ g y₀)

variable (ρ) in
@[expose] def Qv (g : Mbar M Q) : K := -M₀.B (dmap ρ g x₀) (dmap ρ g y₀)

variable (ρ) in
@[expose] def gammaFun (g : Mbar M Q) : K := M₀.B (dmap ρ g x₀) y₀

omit [Finite G] [Finite K] in
theorem Fv_swap (g h : Mbar M Q) : Fv ρ x₀ y₀ h g = -Fv ρ x₀ y₀ g h := by
  simp only [Fv]
  ring

variable {t r : G}

theorem dlin_facts (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t)
    (hr : Sec7A hc t r) {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    (∀ x y, M₀.B (x + dlin hS g (mem_bar_H0_of_CN hg) x) (y + dlin hS g (mem_bar_H0_of_CN hg) y)
      = M₀.B x y) ∧ (∀ x, dlin hS g (mem_bar_H0_of_CN hg) x ∈ wsub hS t) ∧
      (∀ w ∈ wsub hS t, dlin hS g (mem_bar_H0_of_CN hg) w ∈ hc.VtSub hS.model t) := by
  obtain ⟨-, h2, h3⟩ := dmap_CN_facts I.h310chi I.h52a hS hs hr hg
  exact ⟨dmap_iso hS (mem_bar_H0_of_CN hg), h3, h2⟩

theorem Fv_comb (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t)
    (hr : Sec7A hc t r) {g₁ g₂ g₃ h : Mbar M Q} (hg₁ : g₁ ∈ bar M Q (hc.CN t))
    (hg₂ : g₂ ∈ bar M Q (hc.CN t)) (hg₃ : g₃ ∈ bar M Q (hc.CN t))
    (hh : h ∈ bar M Q (hc.CN t)) {k₁ k₂ : K}
    (hk : delta hS t g₃ (mem_bar_H0_of_CN hg₃) =
      k₁ • delta hS t g₁ (mem_bar_H0_of_CN hg₁) + k₂ • delta hS t g₂ (mem_bar_H0_of_CN hg₂)) :
    Fv ρ x₀ y₀ g₃ h = k₁ * Fv ρ x₀ y₀ g₁ h + k₂ * Fv ρ x₀ y₀ g₂ h ∧
      Fv ρ x₀ y₀ h g₃ = k₁ * Fv ρ x₀ y₀ h g₁ + k₂ * Fv ρ x₀ y₀ h g₂ := by
  obtain ⟨i₁, e₁, w₁⟩ := dlin_facts I hS hs hr hg₁
  obtain ⟨i₂, e₂, w₂⟩ := dlin_facts I hS hs hr hg₂
  obtain ⟨i₃, e₃, w₃⟩ := dlin_facts I hS hs hr hg₃
  obtain ⟨-, eh, -⟩ := dlin_facts I hS hs hr hh
  have hWV : ∀ w ∈ wsub hS t, ∀ v ∈ hc.VtSub hS.model t, M₀.B w v = 0 :=
    fun w hw v hv => bilin_wsub_vsub hS t hw hv
  have hk' : ∀ w ∈ wsub hS t, dlin hS g₃ (mem_bar_H0_of_CN hg₃) w =
      k₁ • dlin hS g₁ (mem_bar_H0_of_CN hg₁) w + k₂ • dlin hS g₂ (mem_bar_H0_of_CN hg₂) w :=
    fun w hw => LinearMap.congr_fun hk ⟨w, hw⟩
  have hc₁ := fun x => bilin_comb i₁ i₂ i₃ e₁ e₂ e₃ w₁ w₂ w₃ hWV hk' x (eh y₀)
  have hc₂ := fun y => bilin_comb i₁ i₂ i₃ e₁ e₂ e₃ w₁ w₂ w₃ hWV hk' y (eh x₀)
  have hskew : ∀ a c, M₀.B a c = -M₀.B c a := fun a c => Tim79.QuadModel.B_comm a c
  simp only [dlin_apply] at hc₁ hc₂
  have hF : ∀ g : Mbar M Q, Fv ρ x₀ y₀ g h =
      M₀.B (dmap ρ g x₀) (dmap ρ h y₀) + M₀.B (dmap ρ g y₀) (dmap ρ h x₀) := fun g => by
    simp only [Fv]
    rw [hskew (dmap ρ h x₀) (dmap ρ g y₀)]
    ring
  have h1 : Fv ρ x₀ y₀ g₃ h = k₁ * Fv ρ x₀ y₀ g₁ h + k₂ * Fv ρ x₀ y₀ g₂ h := by
    rw [hF g₃, hF g₁, hF g₂, hc₁ x₀, hc₂ y₀]
    ring
  refine ⟨h1, ?_⟩
  rw [Fv_swap, h1, Fv_swap x₀ y₀ g₁, Fv_swap x₀ y₀ g₂]
  ring

end Forms

section CommSq

variable {t r : G}

theorem comm_sq_mem_Z0 (I : MInputs) (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    (∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0) ∧ ∀ x ∈ hc.CN t, x ^ 2 ∈ Z0 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨-, -, hcent, hdN⟩ := I.h51 G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat) r hr.mem
    hr.plane _ _ _ _ _ rfl rfl rfl rfl rfl
  obtain ⟨-, -, -, -, -, -, hcomm, hsq, -, -⟩ := hdN
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hle : LB M Q B ⊓ LB M Q (conjSubgroup r B) ≤ Z0 := fun x hx =>
    (hZ0 x).mpr ⟨hLR hx.1, fun s hs' => by
      have h := Q.inv_mem (hcent s hs' x hx)
      rwa [commutatorElement_inv] at h⟩
  exact ⟨fun x hx y hy => hle (hcomm x hx y hy), fun x hx => hle (hsq x hx)⟩

theorem comm_mem_bar_Z0 (I : MInputs) (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g h : Mbar M Q}
    (hg : g ∈ bar M Q (hc.CN t)) (hh : h ∈ bar M Q (hc.CN t)) : ⁅g, h⁆ ∈ bar M Q Z0 := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_bar hg
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_bar hh
  have h1 := (comm_sq_mem_Z0 I hs hr hZ0).1 x hx y hy
  have e : ⁅(QuotientGroup.mk x : Mbar M Q), (QuotientGroup.mk y : Mbar M Q)⁆ =
      QuotientGroup.mk ⁅x, y⁆ := by
    simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [e]
  exact mk_mem_bar _ h1

theorem sq_mem_bar_Z0 (I : MInputs) (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : Mbar M Q}
    (hg : g ∈ bar M Q (hc.CN t)) : g ^ 2 ∈ bar M Q Z0 := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_bar hg
  rw [← QuotientGroup.mk_pow]
  exact mk_mem_bar _ (by simpa using (comm_sq_mem_Z0 I hs hr hZ0).2 x hx)

theorem mem_bar_Rt_of_Z0 {L : Subgroup G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M L t) Q) {z : Mbar M Q} (hz : z ∈ bar M Q Z0) :
    z ∈ bar M Q (Rt M L t) := by
  obtain ⟨zm, hzm, rfl⟩ := exists_of_mem_bar hz
  exact mk_mem_bar zm ((hZ0 zm).mp hzm).1

theorem dmap_Z0_wsub (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {z : Mbar M Q}
    (hz : z ∈ bar M Q Z0) {w : M₀.E} (hw : w ∈ wsub hS t) : dmap ρ z w = 0 := by
  obtain ⟨zm, hzZ0, rfl⟩ := exists_of_mem_bar hz
  obtain ⟨x, hxW, hxQ, rfl⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp hw)
  rw [dmap_pi hS zm hxQ]
  have hcQ : ⁅(zm : G), x⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 zm.2) x).mp hxQ)
      (Q.inv_mem hxQ)
  exact (M₀.π_ker _ hcQ).mpr ((I.hMp G M Q Z B hc n t hs Z0 hZ0 zm hzZ0).2 x hxW)

end CommSq

section Gamma

variable (x₀ y₀ : M₀.E) {t r : G}

theorem gamma_comm (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g h : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) (hh : h ∈ bar M Q (hc.CN t)) :
    gammaFun ρ x₀ y₀ ⁅g, h⁆ = Fv ρ x₀ y₀ g h := by
  obtain ⟨i₁, e₁, w₁⟩ := dlin_facts I hS hs hr hg
  obtain ⟨i₂, e₂, w₂⟩ := dlin_facts I hS hs hr hh
  have hz := comm_mem_bar_Z0 I hs hr hZ0 hg hh
  have hzH : ⁅g, h⁆ ∈ bar M Q (H0 M Z) := mem_bar_H0_of_Rt hc (mem_bar_Rt_of_Z0 hZ0 hz)
  have hP : ∀ x, dlin hS ⁅g, h⁆ hzH x = dlin hS g (mem_bar_H0_of_CN hg)
      (dlin hS h (mem_bar_H0_of_CN hh) x) - dlin hS h (mem_bar_H0_of_CN hh)
      (dlin hS g (mem_bar_H0_of_CN hg) x) := by
    refine comm_formula (fun x => dmap_Z0_wsub I hS hs hZ0 hz (e₁ x))
      (fun x => dmap_Z0_wsub I hS hs hZ0 hz (e₂ x)) fun x => ?_
    simp only [dlin_apply, ← act_eq_add_dmap]
    have e3 : ∀ (a c : Mbar M Q) (v : M₀.E), (ρ (a * c)).toAdd v = (ρ a).toAdd ((ρ c).toAdd v) :=
      fun a c v => by
        rw [map_mul]
        rfl
    rw [← e3, ← e3, ← e3]
    congr 2
    rw [commutatorElement_def]
    group
  have hVW : ∀ v ∈ hc.VtSub hS.model t, ∀ w ∈ wsub hS t, M₀.B v w = 0 :=
    fun v hv w hw => bilin_vsub_wsub hS t hv hw
  have := pair_comm hP i₁ i₂ e₁ e₂ w₁ w₂ hVW x₀ y₀
  simpa only [dlin_apply, gammaFun, Fv] using this

theorem gamma_sq [CharP K 2] (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b)
    (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    gammaFun ρ x₀ y₀ (g ^ 2) = Qv ρ x₀ y₀ g := by
  obtain ⟨i₁, e₁, w₁⟩ := dlin_facts I hS hs hr hg
  have hsqH : g ^ 2 ∈ bar M Q (H0 M Z) := Subgroup.pow_mem _ (mem_bar_H0_of_CN hg) 2
  have hP : ∀ x, (x + dlin hS g (mem_bar_H0_of_CN hg) x) + dlin hS g (mem_bar_H0_of_CN hg)
      (x + dlin hS g (mem_bar_H0_of_CN hg) x) = x + dlin hS (g ^ 2) hsqH x := by
    intro x
    simp only [dlin_apply, ← act_eq_add_dmap]
    rw [pow_two, map_mul]
    rfl
  have hVW : ∀ v ∈ hc.VtSub hS.model t, ∀ w ∈ wsub hS t, M₀.B v w = 0 :=
    fun v hv w hw => bilin_vsub_wsub hS t hv hw
  have := pair_sq hP i₁ e₁ w₁ hVW x₀ y₀
  simpa only [dlin_apply, gammaFun, Qv] using this

theorem Qv_smul (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t)
    (hr : Sec7A hc t r) {g g' : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t))
    (hg' : g' ∈ bar M Q (hc.CN t)) {k : K}
    (hk : delta hS t g' (mem_bar_H0_of_CN hg') = k • delta hS t g (mem_bar_H0_of_CN hg)) :
    Qv ρ x₀ y₀ g' = k ^ 2 * Qv ρ x₀ y₀ g := by
  obtain ⟨i₁, e₁, w₁⟩ := dlin_facts I hS hs hr hg
  obtain ⟨i₃, e₃, w₃⟩ := dlin_facts I hS hs hr hg'
  have hWV : ∀ w ∈ wsub hS t, ∀ v ∈ hc.VtSub hS.model t, M₀.B w v = 0 :=
    fun w hw v hv => bilin_wsub_vsub hS t hw hv
  have hk' : ∀ w ∈ wsub hS t, dlin hS g' (mem_bar_H0_of_CN hg') w =
      k • dlin hS g (mem_bar_H0_of_CN hg) w + (0 : K) • dlin hS g (mem_bar_H0_of_CN hg) w :=
    fun w hw => by
      rw [zero_smul, add_zero]
      exact LinearMap.congr_fun hk ⟨w, hw⟩
  have h1 := bilin_comb i₁ i₁ i₃ e₁ e₁ e₃ w₁ w₁ w₃ hWV hk' x₀ (e₃ y₀)
  have h2 := bilin_comb i₁ i₁ i₃ e₁ e₁ e₃ w₁ w₁ w₃ hWV hk' y₀ (e₁ x₀)
  have hskew : ∀ a c, M₀.B a c = -M₀.B c a := fun a c => Tim79.QuadModel.B_comm a c
  simp only [dlin_apply] at h1 h2
  simp only [Qv]
  rw [h1, hskew (dmap ρ g x₀) (dmap ρ g' y₀), h2, hskew (dmap ρ g y₀) (dmap ρ g x₀)]
  ring

theorem Qv_add [CharP K 2] (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b)
    (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) {g₁ g₂ g₃ : Mbar M Q}
    (hg₁ : g₁ ∈ bar M Q (hc.CN t)) (hg₂ : g₂ ∈ bar M Q (hc.CN t))
    (hg₃ : g₃ ∈ bar M Q (hc.CN t))
    (hk : delta hS t g₃ (mem_bar_H0_of_CN hg₃) =
      delta hS t g₁ (mem_bar_H0_of_CN hg₁) + delta hS t g₂ (mem_bar_H0_of_CN hg₂)) :
    Qv ρ x₀ y₀ g₃ = Qv ρ x₀ y₀ g₁ + Qv ρ x₀ y₀ g₂ + Fv ρ x₀ y₀ g₁ g₂ := by
  obtain ⟨i₁, e₁, w₁⟩ := dlin_facts I hS hs hr hg₁
  obtain ⟨i₂, e₂, w₂⟩ := dlin_facts I hS hs hr hg₂
  obtain ⟨i₃, e₃, w₃⟩ := dlin_facts I hS hs hr hg₃
  have hWV : ∀ w ∈ wsub hS t, ∀ v ∈ hc.VtSub hS.model t, M₀.B w v = 0 :=
    fun w hw v hv => bilin_wsub_vsub hS t hw hv
  have hk' : ∀ w ∈ wsub hS t, dlin hS g₃ (mem_bar_H0_of_CN hg₃) w =
      (1 : K) • dlin hS g₁ (mem_bar_H0_of_CN hg₁) w +
        (1 : K) • dlin hS g₂ (mem_bar_H0_of_CN hg₂) w :=
    fun w hw => by
      rw [one_smul, one_smul]
      exact LinearMap.congr_fun hk ⟨w, hw⟩
  have h1 := bilin_comb i₁ i₂ i₃ e₁ e₂ e₃ w₁ w₂ w₃ hWV hk' x₀ (e₃ y₀)
  have h2 := bilin_comb i₁ i₂ i₃ e₁ e₂ e₃ w₁ w₂ w₃ hWV hk' y₀ (e₁ x₀)
  have h3 := bilin_comb i₁ i₂ i₃ e₁ e₂ e₃ w₁ w₂ w₃ hWV hk' y₀ (e₂ x₀)
  have hskew : ∀ a c, M₀.B a c = -M₀.B c a := fun a c => Tim79.QuadModel.B_comm a c
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  simp only [dlin_apply] at h1 h2 h3
  simp only [Qv, Fv]
  rw [h1, hskew (dmap ρ g₁ x₀) (dmap ρ g₃ y₀), hskew (dmap ρ g₂ x₀) (dmap ρ g₃ y₀), h2, h3,
    hskew (dmap ρ g₁ y₀) (dmap ρ g₁ x₀), hskew (dmap ρ g₂ y₀) (dmap ρ g₁ x₀),
    hskew (dmap ρ g₁ y₀) (dmap ρ g₂ x₀), hskew (dmap ρ g₂ y₀) (dmap ρ g₂ x₀)]
  linear_combination (-(M₀.B (dmap ρ g₁ x₀) (dmap ρ g₂ y₀))) * h2K

end Gamma

section Model

variable (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) {t r : G} (hs : Sec7Hyp hc n t)
  (hr : Sec7A hc t r) (x₀ y₀ : M₀.E)

@[expose] noncomputable def piPhi (g : Mbar M Q) : ↥(phiSub I hS hs hr) := by
  classical
  exact if hg : g ∈ bar M Q (hc.CN t) then
    ⟨delta hS t g (mem_bar_H0_of_CN hg), delta_mem_phiSub I hS hs hr hg⟩ else 0

theorem piPhi_of_mem {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    (piPhi I hS hs hr g : ↥(wsub hS t) →ₗ[K] M₀.E) = delta hS t g (mem_bar_H0_of_CN hg) := by
  simp only [piPhi, dif_pos hg]

@[expose] noncomputable def fPhi (e f : ↥(phiSub I hS hs hr)) : K :=
  Fv ρ x₀ y₀ (QuotientGroup.mk (pre I hS hs hr e)) (QuotientGroup.mk (pre I hS hs hr f))

@[expose] noncomputable def quadPhi (e : ↥(phiSub I hS hs hr)) : K :=
  Qv ρ x₀ y₀ (QuotientGroup.mk (pre I hS hs hr e))

theorem mk_pre_mem (e : ↥(phiSub I hS hs hr)) :
    (QuotientGroup.mk (pre I hS hs hr e) : Mbar M Q) ∈ bar M Q (hc.CN t) :=
  mk_mem_bar _ (pre_mem I hS hs hr e)

theorem delta_pre (e : ↥(phiSub I hS hs hr)) :
    delta hS t (QuotientGroup.mk (pre I hS hs hr e)) (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr e))
      = (e : ↥(wsub hS t) →ₗ[K] M₀.E) := (pre_spec I hS hs hr e).symm

theorem fPhi_comb {e₁ e₂ e₃ : ↥(phiSub I hS hs hr)} {k₁ k₂ : K}
    (h : (e₃ : ↥(wsub hS t) →ₗ[K] M₀.E) = k₁ • (e₁ : ↥(wsub hS t) →ₗ[K] M₀.E) + k₂ • e₂)
    (f : ↥(phiSub I hS hs hr)) :
    fPhi I hS hs hr x₀ y₀ e₃ f = k₁ * fPhi I hS hs hr x₀ y₀ e₁ f +
        k₂ * fPhi I hS hs hr x₀ y₀ e₂ f ∧
      fPhi I hS hs hr x₀ y₀ f e₃ = k₁ * fPhi I hS hs hr x₀ y₀ f e₁ +
        k₂ * fPhi I hS hs hr x₀ y₀ f e₂ := by
  have hk : delta hS t (QuotientGroup.mk (pre I hS hs hr e₃))
      (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr e₃)) =
      k₁ • delta hS t (QuotientGroup.mk (pre I hS hs hr e₁))
        (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr e₁)) +
      k₂ • delta hS t (QuotientGroup.mk (pre I hS hs hr e₂))
        (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr e₂)) := by
    rw [delta_pre, delta_pre, delta_pre, h]
  exact Fv_comb x₀ y₀ I hS hs hr (mk_pre_mem I hS hs hr e₁) (mk_pre_mem I hS hs hr e₂)
    (mk_pre_mem I hS hs hr e₃) (mk_pre_mem I hS hs hr f) hk

@[expose] noncomputable def bilinPhi : LinearMap.BilinForm K ↥(phiSub I hS hs hr) :=
  LinearMap.mk₂ K (fPhi I hS hs hr x₀ y₀)
    (fun e₁ e₂ f => by
      have h := (fPhi_comb I hS hs hr x₀ y₀ (e₁ := e₁) (e₂ := e₂) (e₃ := e₁ + e₂) (k₁ := 1)
        (k₂ := 1) (by simp) f).1
      rw [h]
      ring)
    (fun c e f => by
      have h := (fPhi_comb I hS hs hr x₀ y₀ (e₁ := e) (e₂ := e) (e₃ := c • e) (k₁ := c)
        (k₂ := 0) (by simp) f).1
      rw [h, smul_eq_mul]
      ring)
    (fun e f₁ f₂ => by
      have h := (fPhi_comb I hS hs hr x₀ y₀ (e₁ := f₁) (e₂ := f₂) (e₃ := f₁ + f₂) (k₁ := 1)
        (k₂ := 1) (by simp) e).2
      rw [h]
      ring)
    (fun c e f => by
      have h := (fPhi_comb I hS hs hr x₀ y₀ (e₁ := f) (e₂ := f) (e₃ := c • f) (k₁ := c)
        (k₂ := 0) (by simp) e).2
      rw [h, smul_eq_mul]
      ring)

theorem bilinPhi_apply (e f : ↥(phiSub I hS hs hr)) :
    bilinPhi I hS hs hr x₀ y₀ e f = fPhi I hS hs hr x₀ y₀ e f := rfl

theorem Fv_eq_fPhi {g h : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) (hh : h ∈ bar M Q (hc.CN t)) :
    Fv ρ x₀ y₀ g h = fPhi I hS hs hr x₀ y₀ (piPhi I hS hs hr g) (piPhi I hS hs hr h) := by
  have h1 : delta hS t (QuotientGroup.mk (pre I hS hs hr (piPhi I hS hs hr g)))
      (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr _)) =
      (1 : K) • delta hS t g (mem_bar_H0_of_CN hg) +
        (0 : K) • delta hS t g (mem_bar_H0_of_CN hg) := by
    rw [delta_pre, piPhi_of_mem I hS hs hr hg, one_smul, zero_smul, add_zero]
  have h2 : delta hS t (QuotientGroup.mk (pre I hS hs hr (piPhi I hS hs hr h)))
      (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr _)) =
      (1 : K) • delta hS t h (mem_bar_H0_of_CN hh) +
        (0 : K) • delta hS t h (mem_bar_H0_of_CN hh) := by
    rw [delta_pre, piPhi_of_mem I hS hs hr hh, one_smul, zero_smul, add_zero]
  have e1 := (Fv_comb x₀ y₀ I hS hs hr hg hg (mk_pre_mem I hS hs hr (piPhi I hS hs hr g))
    (mk_pre_mem I hS hs hr (piPhi I hS hs hr h)) h1).1
  have e2 := (Fv_comb x₀ y₀ I hS hs hr hh hh (mk_pre_mem I hS hs hr (piPhi I hS hs hr h)) hg
    h2).2
  simp only [fPhi]
  rw [e1, e2]
  ring

theorem Qv_eq_quadPhi {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    Qv ρ x₀ y₀ g = quadPhi I hS hs hr x₀ y₀ (piPhi I hS hs hr g) := by
  have h1 : delta hS t (QuotientGroup.mk (pre I hS hs hr (piPhi I hS hs hr g)))
      (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr _)) =
      (1 : K) • delta hS t g (mem_bar_H0_of_CN hg) := by
    rw [delta_pre, piPhi_of_mem I hS hs hr hg, one_smul]
  have := Qv_smul x₀ y₀ I hS hs hr hg (mk_pre_mem I hS hs hr (piPhi I hS hs hr g)) h1
  simp only [quadPhi]
  rw [this]
  ring

@[expose] noncomputable def quadModelPhi [CharP K 2] {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hnd : ∀ e, (∀ f, bilinPhi I hS hs hr x₀ y₀ e f = 0) → e = 0) :
    Tim79.QuadModel (bar M Q (hc.CN t)) (bar M Q Z0) K (gammaFun ρ x₀ y₀) where
  E := ↥(phiSub I hS hs hr)
  π := piPhi I hS hs hr
  B := bilinPhi I hS hs hr x₀ y₀
  Qf := quadPhi I hS hs hr x₀ y₀
  π_mul := fun x hx y hy => by
    apply Subtype.ext
    rw [Submodule.coe_add, piPhi_of_mem I hS hs hr (Subgroup.mul_mem _ hx hy),
      piPhi_of_mem I hS hs hr hx, piPhi_of_mem I hS hs hr hy]
    exact delta_mul I.h310chi I.h52a hS hs hr hx hy
  π_surj := fun e => ⟨_, mk_pre_mem I hS hs hr e, Subtype.ext (by
    rw [piPhi_of_mem I hS hs hr (mk_pre_mem I hS hs hr e), delta_pre])⟩
  π_ker := fun x hx => by
    have hxR : x ∈ bar M Q (Rt M (LB M Q B) t) := by
      obtain ⟨m, hm, rfl⟩ := exists_of_mem_bar hx
      exact mk_mem_bar m (Ctx.mem_CN.mp hm).1
    rw [← Subtype.coe_inj, Submodule.coe_zero, piPhi_of_mem I hS hs hr hx,
      delta_congr hS t rfl (mem_bar_H0_of_CN hx) (mem_bar_H0_of_Rt hc hxR)]
    exact delta_eq_zero_iff I.hCRW I.hMp hS hs hZ0 hxR
  comm_mem := fun x hx y hy => comm_mem_bar_Z0 I hs hr hZ0 hx hy
  sq_mem := fun x hx => sq_mem_bar_Z0 I hs hr hZ0 hx
  comm_eq := fun x hx y hy => by
    rw [gamma_comm x₀ y₀ I hS hs hr hZ0 hx hy, bilinPhi_apply]
    exact Fv_eq_fPhi I hS hs hr x₀ y₀ hx hy
  sq_eq := fun x hx => by
    rw [gamma_sq x₀ y₀ I hS hs hr hx]
    exact Qv_eq_quadPhi I hS hs hr x₀ y₀ hx
  alt := fun e => by
    rw [bilinPhi_apply]
    simp only [fPhi, Fv, sub_self]
  nondeg := hnd
  Qf_smul := fun c e => by
    have h1 : delta hS t (QuotientGroup.mk (pre I hS hs hr (c • e)))
        (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr _)) =
        c • delta hS t (QuotientGroup.mk (pre I hS hs hr e))
          (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr e)) := by
      rw [delta_pre, delta_pre, Submodule.coe_smul]
    exact Qv_smul x₀ y₀ I hS hs hr (mk_pre_mem I hS hs hr e) (mk_pre_mem I hS hs hr _) h1
  Qf_add := fun e f => by
    have h1 : delta hS t (QuotientGroup.mk (pre I hS hs hr (e + f)))
        (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr _)) =
        delta hS t (QuotientGroup.mk (pre I hS hs hr e))
          (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr e)) +
        delta hS t (QuotientGroup.mk (pre I hS hs hr f))
          (mem_bar_H0_of_CN (mk_pre_mem I hS hs hr f)) := by
      rw [delta_pre, delta_pre, delta_pre, Submodule.coe_add]
    rw [bilinPhi_apply]
    exact Qv_add x₀ y₀ I hS hs hr (mk_pre_mem I hS hs hr e) (mk_pre_mem I hS hs hr f)
      (mk_pre_mem I hS hs hr _) h1

end Model

section GammaReg

variable {t r : G}

theorem Vt_le_Wt (I : MInputs) (hs : Sec7Hyp hc n t) :
    Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  obtain ⟨-, hWQ1⟩ := I.h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
  rw [hWQ1]
  exact hc.Vt_le_Q1 hs.toSec5.mem

theorem Z0_le_CN (I : MInputs) (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Z0 ≤ hc.CN t := fun z hz =>
  Ctx.mem_CN.mpr ⟨((hZ0 z).mp hz).1, fun v hv =>
    (I.hMp G M Q Z B hc n t hs Z0 hZ0 z hz).2 v (Vt_le_Wt I hs hv)⟩

theorem exists_xy (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t)
    (tm : ↥M) (htm : (tm : G) = t) :
    ∃ x₀ y₀ : M₀.E, M₀.B (dmap ρ (QuotientGroup.mk tm) x₀) y₀ = 1 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨-, hsurj, -⟩ := psi_facts I.h310chi hS hs.toSec5 (Or.inr hs.omegaNat) tm htm
  have hbV : b ∈ hc.VtSub hS.model t := by
    obtain ⟨x, hxB, hxQ, hx⟩ := M₀.mem_img.mp hS.b_img
    exact (hc.mem_VtSub hS.model t).mpr ⟨x, hc.B_le_Vt ht hxB, hxQ, hx⟩
  obtain ⟨x₀, hx₀⟩ := hsurj b hbV
  have hex : ∃ y, M₀.B b y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hS.b_ne (M₀.nondeg b hcon)
  obtain ⟨y, hy⟩ := hex
  refine ⟨x₀, (M₀.B b y)⁻¹ • y, ?_⟩
  rw [hx₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hy]

theorem gammaReg (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t)
    (hr : Sec7A hc t r) (tm : ↥M) (htm : (tm : G) = t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {x₀ y₀ : M₀.E}
    (hxy : M₀.B (dmap ρ (QuotientGroup.mk tm) x₀) y₀ = 1) :
    Tim79.GammaReg (bar M Q (hc.CN t)) (bar M Q Z0) (gammaFun ρ x₀ y₀) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZ0N := Z0_le_CN I hs hZ0
  have hV_le : bar M Q Z0 ≤ bar M Q (hc.CN t) := fun z hz => by
    obtain ⟨zm, hzm, rfl⟩ := exists_of_mem_bar hz
    exact mk_mem_bar zm (hZ0N hzm)
  have hadd : ∀ a ∈ bar M Q Z0, ∀ c ∈ bar M Q Z0,
      gammaFun ρ x₀ y₀ (a * c) = gammaFun ρ x₀ y₀ a + gammaFun ρ x₀ y₀ c := by
    intro a ha c hc'
    obtain ⟨-, -, h3⟩ := dmap_CN_facts I.h310chi I.h52a hS hs hr (hV_le hc')
    simp only [gammaFun]
    rw [dmap_mul, dmap_Z0_wsub I hS hs hZ0 ha (h3 x₀), add_zero, map_add, LinearMap.add_apply]
  obtain ⟨act, hact, hinj, -⟩ := endg_act_data hc hS.model ρ hS.conj
  have hinj' : ∀ a ∈ bar M Q Z0, gammaFun ρ x₀ y₀ a = 0 → a = 1 := by
    intro a ha h0
    obtain ⟨c, hc'⟩ := exists_scalar_of_mem_Z0 I.h310chi I.hZV I.hMp hS hs tm htm hZ0 ha
    have hc0 : c = 0 := by
      have h1 : gammaFun ρ x₀ y₀ a = c := by
        simp only [gammaFun]
        rw [hc' x₀, map_smul, LinearMap.smul_apply, hxy, smul_eq_mul, mul_one]
      rw [← h1, h0]
    refine hinj ?_
    rw [map_one]
    refine Equiv.ext fun e => ?_
    rw [hact, act_eq_add_dmap, hc' e, hc0, zero_smul, add_zero]
    rfl
  have hone : gammaFun ρ x₀ y₀ 1 = 0 := by
    simp only [gammaFun]
    have h1 : dmap ρ (1 : Mbar M Q) x₀ = 0 := dmap_one x₀
    rw [h1, map_zero, LinearMap.zero_apply]
  refine ⟨hV_le, hadd, hinj', fun s => ?_⟩
  have hQZ0 : Q ≤ Z0 := fun x hx => (hZ0 x).mpr ⟨hc.Q_le_Rt ht hx, fun y hy => by
    have hyx : y * x⁻¹ * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 (hc.Rt_le_M t hy)) x⁻¹).mp (Q.inv_mem hx)
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hx hyx⟩
  have hZ0M : Z0 ≤ M := fun z hz => hc.Rt_le_M t ((hZ0 z).mp hz).1
  have hcard := Tim37.card_bar_mul_card_of_le (M := M) hQZ0 hZ0M
  rw [I.hZc G M Q Z B hc n t hs Z0 hZ0] at hcard
  have hcardZ : Nat.card ↥(bar M Q Z0) = Nat.card K := by
    rw [hS.card]
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hQpos
    rw [hcard, mul_comm]
  let f : ↥(bar M Q Z0) → K := fun a => gammaFun ρ x₀ y₀ a
  have hfinj : Function.Injective f := by
    intro a c hac
    have hinv : gammaFun ρ x₀ y₀ (c : Mbar M Q)⁻¹ = -gammaFun ρ x₀ y₀ c := by
      have h1 := hadd _ c.2 _ (Subgroup.inv_mem _ c.2)
      rw [mul_inv_cancel, hone] at h1
      linear_combination -h1
    have h2 := hadd _ a.2 _ (Subgroup.inv_mem _ c.2)
    rw [hinv] at h2
    have h3 : gammaFun ρ x₀ y₀ ((a : Mbar M Q) * (c : Mbar M Q)⁻¹) = 0 := by
      have hac' : gammaFun ρ x₀ y₀ a = gammaFun ρ x₀ y₀ c := hac
      rw [h2, hac']
      ring
    have h4 := hinj' _ (Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ c.2)) h3
    exact Subtype.ext (mul_inv_eq_one.mp h4)
  have hbij : Function.Bijective f := hfinj.bijective_of_nat_card_le (by rw [hcardZ])
  obtain ⟨a, ha⟩ := hbij.2 s
  exact ⟨a, a.2, ha⟩

end GammaReg

section Act

variable {t r : G}

@[expose] def actLin (hS : IsTensorSetup hc n M₀ ρ b) (h : Mbar M Q)
    (hh : h ∈ bar M Q (H0 M Z)) : M₀.E →ₗ[K] M₀.E where
  toFun := (ρ h).toAdd
  map_add' := map_add _
  map_smul' := hS.lin h hh

@[expose] def actW (hS : IsTensorSetup hc n M₀ ρ b) (ht : t ∈ LB M Q B) (h : Mbar M Q)
    (hh : h ∈ bar M Q (Rt M (LB M Q B) t)) : ↥(wsub hS t) →ₗ[K] ↥(wsub hS t) where
  toFun w := ⟨(ρ h).toAdd w, act_mem_wsub hS ht hh w.2⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c w := Subtype.ext (hS.lin h (mem_bar_H0_of_Rt hc hh) c w)

@[expose] def conjHom (hS : IsTensorSetup hc n M₀ ρ b) (ht : t ∈ LB M Q B) (h : Mbar M Q)
    (hh : h ∈ bar M Q (Rt M (LB M Q B) t)) :
    (↥(wsub hS t) →ₗ[K] M₀.E) →ₗ[K] (↥(wsub hS t) →ₗ[K] M₀.E) where
  toFun f := (actLin hS h (mem_bar_H0_of_Rt hc hh)).comp
    (f.comp (actW hS ht h⁻¹ (Subgroup.inv_mem _ hh)))
  map_add' f g := by
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' c f := by
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

theorem conjHom_apply (hS : IsTensorSetup hc n M₀ ρ b) (ht : t ∈ LB M Q B) {h : Mbar M Q}
    (hh : h ∈ bar M Q (Rt M (LB M Q B) t)) (f : ↥(wsub hS t) →ₗ[K] M₀.E) (w : ↥(wsub hS t)) :
    conjHom hS ht h hh f w =
      (ρ h).toAdd (f ⟨(ρ h⁻¹).toAdd w, act_mem_wsub hS ht (Subgroup.inv_mem _ hh) w.2⟩) := rfl

theorem conjHom_congr' (hS : IsTensorSetup hc n M₀ ρ b) (ht : t ∈ LB M Q B) {h h' : Mbar M Q}
    (e : h = h') {hh : h ∈ bar M Q (Rt M (LB M Q B) t)}
    (f : ↥(wsub hS t) →ₗ[K] M₀.E) :
    conjHom hS ht h hh f = conjHom hS ht h' (e ▸ hh) f := by
  subst e
  rfl

theorem conjHom_delta (hS : IsTensorSetup hc n M₀ ρ b) (ht : t ∈ LB M Q B) {h : Mbar M Q}
    (hh : h ∈ bar M Q (Rt M (LB M Q B) t)) {g : Mbar M Q} (hg : g ∈ bar M Q (H0 M Z)) :
    conjHom hS ht h hh (delta hS t g hg) = delta hS t (h * g * h⁻¹)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_bar_H0_of_Rt hc hh) hg)
        (Subgroup.inv_mem _ (mem_bar_H0_of_Rt hc hh))) := by
  refine LinearMap.ext fun w => ?_
  rw [conjHom_apply, delta_conj hS ht hh hg w]

omit [Finite G] [Finite K] in
theorem act_mul_apply' (a c : Mbar M Q) (v : M₀.E) :
    (ρ (a * c)).toAdd v = (ρ a).toAdd ((ρ c).toAdd v) := by
  rw [map_mul]
  rfl

theorem conjHom_mul (hS : IsTensorSetup hc n M₀ ρ b) (ht : t ∈ LB M Q B) {h₁ h₂ : Mbar M Q}
    (hh₁ : h₁ ∈ bar M Q (Rt M (LB M Q B) t)) (hh₂ : h₂ ∈ bar M Q (Rt M (LB M Q B) t))
    (f : ↥(wsub hS t) →ₗ[K] M₀.E) :
    conjHom hS ht (h₁ * h₂) (Subgroup.mul_mem _ hh₁ hh₂) f =
      conjHom hS ht h₁ hh₁ (conjHom hS ht h₂ hh₂ f) := by
  refine LinearMap.ext fun w => ?_
  rw [conjHom_apply, conjHom_apply, conjHom_apply, act_mul_apply']
  have key : (⟨(ρ (h₁ * h₂)⁻¹).toAdd (w : M₀.E), act_mem_wsub hS ht
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ hh₁ hh₂)) w.2⟩ : ↥(wsub hS t)) =
      ⟨(ρ h₂⁻¹).toAdd ((ρ h₁⁻¹).toAdd (w : M₀.E)), act_mem_wsub hS ht
        (Subgroup.inv_mem _ hh₂) (act_mem_wsub hS ht (Subgroup.inv_mem _ hh₁) w.2)⟩ := by
    apply Subtype.ext
    show (ρ (h₁ * h₂)⁻¹).toAdd (w : M₀.E) = (ρ h₂⁻¹).toAdd ((ρ h₁⁻¹).toAdd w)
    rw [mul_inv_rev, act_mul_apply']
  rw [key]

theorem conjHom_one (hS : IsTensorSetup hc n M₀ ρ b) (ht : t ∈ LB M Q B)
    (f : ↥(wsub hS t) →ₗ[K] M₀.E) :
    conjHom hS ht 1 (Subgroup.one_mem _) f = f := by
  refine LinearMap.ext fun w => ?_
  rw [conjHom_apply]
  have e : ∀ v : M₀.E, (ρ (1 : Mbar M Q)).toAdd v = v := fun v => by
    rw [map_one]
    rfl
  have hw : (⟨(ρ (1 : Mbar M Q)⁻¹).toAdd w, act_mem_wsub hS ht
      (Subgroup.inv_mem _ (Subgroup.one_mem _)) w.2⟩ : ↥(wsub hS t)) = w := by
    apply Subtype.ext
    show (ρ (1 : Mbar M Q)⁻¹).toAdd (w : M₀.E) = w
    rw [inv_one, e]
  rw [hw, e]

theorem conjHom_mem (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t)
    (hr : Sec7A hc t r) {h : Mbar M Q}
    (hh : h ∈ bar M Q (Rt M (LB M Q B) t)) {f : ↥(wsub hS t) →ₗ[K] M₀.E}
    (hf : f ∈ phiSub I hS hs hr) : conjHom hS hs.toSec5.mem h hh f ∈ phiSub I hS hs hr := by
  obtain ⟨x, hx, rfl⟩ := hf
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_bar hh
  rw [conjHom_delta]
  have hyx : (QuotientGroup.mk y : Mbar M Q) * QuotientGroup.mk x * (QuotientGroup.mk y)⁻¹ =
      QuotientGroup.mk (y * x * y⁻¹) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [delta_congr hS t hyx _ (mem_bar_H0_of_CN (mk_mem_bar (y * x * y⁻¹)
    (conj_mem_CN hc hs.toSec5.mem hy hx)))]
  exact delta_mem_phiSub I hS hs hr (mk_mem_bar _ (conj_mem_CN hc hs.toSec5.mem hy hx))

variable (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)

@[expose] def conjPhi (h : ↥(bar M Q (Rt M (LB M Q B) t))) :
    ↥(phiSub I hS hs hr) →ₗ[K] ↥(phiSub I hS hs hr) :=
  (conjHom hS hs.toSec5.mem h h.2).restrict fun _ hf => conjHom_mem I hS hs hr h.2 hf

@[expose] noncomputable def psiPhi :
    ↥(bar M Q (Rt M (LB M Q B) t)) →* (↥(phiSub I hS hs hr) ≃ₗ[K] ↥(phiSub I hS hs hr)) where
  toFun h := LinearEquiv.ofLinear (conjPhi I hS hs hr h) (conjPhi I hS hs hr h⁻¹)
    (by
      refine LinearMap.ext fun f => Subtype.ext ?_
      show conjHom hS hs.toSec5.mem (h : Mbar M Q) h.2
        (conjHom hS hs.toSec5.mem ((h⁻¹ : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q) h⁻¹.2
          (f : ↥(wsub hS t) →ₗ[K] M₀.E)) = f
      rw [← conjHom_mul]
      have e : ((h : Mbar M Q) * ((h⁻¹ : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q)) = 1 := by
        simp
      rw [conjHom_congr' hS hs.toSec5.mem e, conjHom_one])
    (by
      refine LinearMap.ext fun f => Subtype.ext ?_
      show conjHom hS hs.toSec5.mem ((h⁻¹ : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q) h⁻¹.2
        (conjHom hS hs.toSec5.mem (h : Mbar M Q) h.2 (f : ↥(wsub hS t) →ₗ[K] M₀.E)) = f
      rw [← conjHom_mul]
      have e : (((h⁻¹ : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q) * (h : Mbar M Q)) = 1 := by
        simp
      rw [conjHom_congr' hS hs.toSec5.mem e, conjHom_one])
  map_one' := by
    refine LinearEquiv.ext fun f => Subtype.ext ?_
    exact conjHom_one hS hs.toSec5.mem (f : ↥(wsub hS t) →ₗ[K] M₀.E)
  map_mul' h₁ h₂ := by
    refine LinearEquiv.ext fun f => Subtype.ext ?_
    exact conjHom_mul hS hs.toSec5.mem h₁.2 h₂.2 (f : ↥(wsub hS t) →ₗ[K] M₀.E)

end Act

section ActProps

variable {t r : G} (I : MInputs) (hS : IsTensorSetup hc n M₀ ρ b) (hs : Sec7Hyp hc n t)
  (hr : Sec7A hc t r)

theorem conj_mem_bar_CN (hs : Sec7Hyp hc n t) {h x : Mbar M Q}
    (hh : h ∈ bar M Q (Rt M (LB M Q B) t)) (hx : x ∈ bar M Q (hc.CN t)) :
    h * x * h⁻¹ ∈ bar M Q (hc.CN t) := by
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_bar hh
  obtain ⟨x', hx', rfl⟩ := exists_of_mem_bar hx
  have e : (QuotientGroup.mk y : Mbar M Q) * QuotientGroup.mk x' * (QuotientGroup.mk y)⁻¹ =
      QuotientGroup.mk (y * x' * y⁻¹) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [e]
  exact mk_mem_bar _ (conj_mem_CN hc hs.toSec5.mem hy hx')

theorem psiPhi_apply_coe (h : ↥(bar M Q (Rt M (LB M Q B) t))) (e : ↥(phiSub I hS hs hr)) :
    ((psiPhi I hS hs hr h e : ↥(phiSub I hS hs hr)) : ↥(wsub hS t) →ₗ[K] M₀.E) =
      conjHom hS hs.toSec5.mem (h : Mbar M Q) h.2 (e : ↥(wsub hS t) →ₗ[K] M₀.E) := rfl

theorem piPhi_conj (h : ↥(bar M Q (Rt M (LB M Q B) t))) {x : Mbar M Q}
    (hx : x ∈ bar M Q (hc.CN t)) :
    piPhi I hS hs hr ((h : Mbar M Q) * x * (h : Mbar M Q)⁻¹) =
      psiPhi I hS hs hr h (piPhi I hS hs hr x) := by
  apply Subtype.ext
  rw [psiPhi_apply_coe, piPhi_of_mem I hS hs hr (conj_mem_bar_CN hs h.2 hx),
    piPhi_of_mem I hS hs hr hx, conjHom_delta]

theorem piPhi_pre (e : ↥(phiSub I hS hs hr)) :
    piPhi I hS hs hr (QuotientGroup.mk (pre I hS hs hr e)) = e := by
  apply Subtype.ext
  rw [piPhi_of_mem I hS hs hr (mk_pre_mem I hS hs hr e), delta_pre]

theorem quadPhi_psi [CharP K 2] (x₀ y₀ : M₀.E) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (h : ↥(bar M Q (Rt M (LB M Q B) t)))
    (e : ↥(phiSub I hS hs hr)) :
    quadPhi I hS hs hr x₀ y₀ (psiPhi I hS hs hr h e) = quadPhi I hS hs hr x₀ y₀ e := by
  set g : Mbar M Q := QuotientGroup.mk (pre I hS hs hr e)
  have hg : g ∈ bar M Q (hc.CN t) := mk_pre_mem I hS hs hr e
  have hcg := conj_mem_bar_CN hs h.2 hg
  have key : psiPhi I hS hs hr h e = piPhi I hS hs hr ((h : Mbar M Q) * g * (h : Mbar M Q)⁻¹) := by
    rw [piPhi_conj I hS hs hr h hg, piPhi_pre]
  have hsq := sq_mem_bar_Z0 I hs hr hZ0 hg
  obtain ⟨zm, hzm, hz⟩ := exists_of_mem_bar hsq
  have hcomm : g ^ 2 * (h : Mbar M Q) = (h : Mbar M Q) * g ^ 2 := by
    rw [← hz]
    exact endg_comm_centre hZ0 (hc.Rt_le_M t) hzm h.2
  have e2 : ((h : Mbar M Q) * g * (h : Mbar M Q)⁻¹) ^ 2 = g ^ 2 := by
    rw [show ((h : Mbar M Q) * g * (h : Mbar M Q)⁻¹) ^ 2 =
      (h : Mbar M Q) * g ^ 2 * (h : Mbar M Q)⁻¹ by rw [pow_two, pow_two]; group, ← hcomm,
      mul_inv_cancel_right]
  calc quadPhi I hS hs hr x₀ y₀ (psiPhi I hS hs hr h e)
      = quadPhi I hS hs hr x₀ y₀ (piPhi I hS hs hr ((h : Mbar M Q) * g * (h : Mbar M Q)⁻¹)) := by
        rw [key]
    _ = Qv ρ x₀ y₀ ((h : Mbar M Q) * g * (h : Mbar M Q)⁻¹) :=
        (Qv_eq_quadPhi I hS hs hr x₀ y₀ hcg).symm
    _ = gammaFun ρ x₀ y₀ (((h : Mbar M Q) * g * (h : Mbar M Q)⁻¹) ^ 2) :=
        (gamma_sq x₀ y₀ I hS hs hr hcg).symm
    _ = gammaFun ρ x₀ y₀ (g ^ 2) := by rw [e2]
    _ = Qv ρ x₀ y₀ g := gamma_sq x₀ y₀ I hS hs hr hg
    _ = quadPhi I hS hs hr x₀ y₀ (piPhi I hS hs hr g) := Qv_eq_quadPhi I hS hs hr x₀ y₀ hg
    _ = quadPhi I hS hs hr x₀ y₀ e := by rw [piPhi_pre]

theorem psiPhi_eq_one (h : ↥(bar M Q (Rt M (LB M Q B) t)))
    (hN : (h : Mbar M Q) ∈ bar M Q (hc.CN t)) : psiPhi I hS hs hr h = 1 := by
  refine LinearEquiv.ext fun e => Subtype.ext ?_
  rw [psiPhi_apply_coe]
  show conjHom hS hs.toSec5.mem (h : Mbar M Q) h.2 (e : ↥(wsub hS t) →ₗ[K] M₀.E) = e
  obtain ⟨x, hx, hex⟩ := (mem_phiSub I hS hs hr).mp e.2
  rw [hex, conjHom_delta]
  have hg : (QuotientGroup.mk x : Mbar M Q) ∈ bar M Q (hc.CN t) := mk_mem_bar x hx
  have hinv : (h : Mbar M Q)⁻¹ ∈ bar M Q (hc.CN t) := Subgroup.inv_mem _ hN
  have h1 := delta_mul I.h310chi I.h52a hS hs hr (Subgroup.mul_mem _ hN hg) hinv
  have h2 := delta_mul I.h310chi I.h52a hS hs hr hN hg
  have h3 := delta_mul I.h310chi I.h52a hS hs hr hN hinv
  have h0 : delta hS t ((h : Mbar M Q) * (h : Mbar M Q)⁻¹)
      (Subgroup.mul_mem _ (mem_bar_H0_of_CN hN) (mem_bar_H0_of_CN hinv)) = 0 := by
    refine LinearMap.ext fun w => ?_
    rw [delta_apply, LinearMap.zero_apply, mul_inv_cancel]
    exact dmap_one (w : M₀.E)
  rw [h0] at h3
  rw [delta_congr hS t rfl _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_bar_H0_of_CN hN)
    (mem_bar_H0_of_CN hg)) (mem_bar_H0_of_CN hinv)), h1, h2,
    add_comm (delta hS t (h : Mbar M Q) _), add_assoc, ← h3, add_zero]

end ActProps

end CFSG.RankThree.GF2n.Stroth80.S714
