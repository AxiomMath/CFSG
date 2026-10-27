module

public import CFSG.Quasithin.MS93.S36SpPair
public import CFSG.Quasithin.MS93.S36SpSyl

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}

namespace SpFrame

variable (d : SpFrame h) {E : Subgroup G} (hEM : E ≤ M) (hE : ∀ e ∈ E, ∃ g, ActsMat d.vec e g)

@[expose] noncomputable def preImg (S : Subgroup (Sp4 d.F)) : Subgroup G :=
  (S.comap (rho d.surj E (hEM.trans d.normU) hE)).map E.subtype

theorem mem_preImg {S : Subgroup (Sp4 d.F)} {x : G} :
    x ∈ d.preImg hEM hE S ↔ x ∈ E ∧ ∃ g ∈ S, ActsMat d.vec x g := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.2, _, he, actsMat_rho d.surj _ hE e⟩
  · rintro ⟨hx, g, hgS, hg⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, rho_eq d.surj _ hE hg]
    exact hgS

theorem preImg_img : d.preImg hEM hE (d.img E hEM hE) = E := by
  refine le_antisymm (fun x hx => ((d.mem_preImg hEM hE).1 hx).1) fun x hx => ?_
  obtain ⟨g, hg⟩ := hE x hx
  exact (d.mem_preImg hEM hE).2 ⟨hx, g, d.actsMat_mem_img hEM hE hx hg, hg⟩

theorem commutator_preImg_le (S₁ S₂ : Subgroup (Sp4 d.F)) :
    ⁅d.preImg hEM hE S₁, d.preImg hEM hE S₂⁆ ≤ d.preImg hEM hE ⁅S₁, S₂⁆ := by
  rw [preImg, preImg, preImg, ← Subgroup.map_commutator]
  refine Subgroup.map_mono ?_
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
  exact Subgroup.commutator_mono (Subgroup.map_comap_le _ _) (Subgroup.map_comap_le _ _)

theorem preImg_bot_le (hET : E ≤ T) : d.preImg hEM hE ⊥ ≤ pCoreOf 2 M := by
  intro x hx
  obtain ⟨hxE, g, hg1, hg⟩ := (d.mem_preImg hEM hE).1 hx
  rw [Subgroup.mem_bot.1 hg1] at hg
  exact mem_pCoreOf_of_mem_trivW h (hET hxE) (mem_trivW_of_actsMat_one h d.ker (hEM hxE) hg)

end SpFrame

namespace PairHyp

variable {d : SpFrame h} {χ : MulAut ↥T} (hp : PairHyp d χ)
include hp

theorem le_centralizer_L {N : Subgroup G} (hNn : M ≤ Subgroup.normalizer (N : Set G))
    (hN : N ≤ tImage χ⁻¹ (pCoreOf 2 M)) : N ≤ Subgroup.centralizer (L : Set G) := by
  have hNY : ⁅N, tImage χ⁻¹ (Z0q M T)⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro n hn y hy
    have := Subgroup.mem_centralizer_iff.1 (tImage_pCoreOf_le_centralizer h χ⁻¹ (hN hn)) y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact this.symm
  have hbot : M ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun m _ =>
    Subgroup.mem_normalizer_iff.2 fun x => by
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro hx
        have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
        rw [this, hx]
        group
  have hNL := comm_le_of_comm_le h (tImage_le _ _) hp.not_tImage_inv_le hNn hbot hNY
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := hNL (Subgroup.commutator_mem_commutator hn hl)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem tImage_le_tImage_Dq {N : Subgroup G} (hNn : M ≤ Subgroup.normalizer (N : Set G))
    (hNQ : N ≤ pCoreOf 2 M) (hN : tImage χ N ≤ pCoreOf 2 M) :
    tImage χ N ≤ tImage χ (Dq M L) := by
  have hNT : N ≤ T := hNQ.trans h.pCore_le
  have h1 : N ≤ tImage χ⁻¹ (pCoreOf 2 M) := (tImage_le_iff χ hNT h.pCore_le).1 hN
  exact S36SP.tImage_mono χ (le_inf hNQ (hp.le_centralizer_L hNn h1))

theorem commutator_le_of_abelian {hPM : tImage χ (pCoreOf 2 M) ≤ M}
    {hP : ∀ x ∈ tImage χ (pCoreOf 2 M), ∃ g, ActsMat d.vec x g}
    (hab : ⁅d.img _ hPM hP, d.img _ hPM hP⁆ = ⊥) :
    ⁅tImage χ (pCoreOf 2 M), tImage χ (pCoreOf 2 M)⁆ ≤ tImage χ (Dq M L) := by
  have h1 : ⁅tImage χ (pCoreOf 2 M), tImage χ (pCoreOf 2 M)⁆ ≤ pCoreOf 2 M := by
    have := d.commutator_preImg_le hPM hP (d.img _ hPM hP) (d.img _ hPM hP)
    rw [d.preImg_img, hab] at this
    exact this.trans (d.preImg_bot_le hPM hP (tImage_le χ _))
  rw [← tImage_commutator χ h.pCore_le h.pCore_le] at h1 ⊢
  exact hp.tImage_le_tImage_Dq
    (le_normalizer_commutator (le_normalizer_pCoreOf M) (le_normalizer_pCoreOf M))
    (commutator_le_of_le le_rfl le_rfl) h1

theorem commutator_commutator_le {hPM : tImage χ (pCoreOf 2 M) ≤ M}
    {hP : ∀ x ∈ tImage χ (pCoreOf 2 M), ∃ g, ActsMat d.vec x g}
    (hcl : ⁅⁅d.img _ hPM hP, d.img _ hPM hP⁆, d.img _ hPM hP⁆ = ⊥) :
    ⁅⁅tImage χ (pCoreOf 2 M), tImage χ (pCoreOf 2 M)⁆, tImage χ (pCoreOf 2 M)⁆ ≤
      tImage χ (Dq M L) := by
  have h1 : ⁅⁅tImage χ (pCoreOf 2 M), tImage χ (pCoreOf 2 M)⁆, tImage χ (pCoreOf 2 M)⁆ ≤
      pCoreOf 2 M := by
    have h2 := d.commutator_preImg_le hPM hP (d.img _ hPM hP) (d.img _ hPM hP)
    have h3 := d.commutator_preImg_le hPM hP ⁅d.img _ hPM hP, d.img _ hPM hP⁆ (d.img _ hPM hP)
    rw [d.preImg_img] at h2 h3
    rw [hcl] at h3
    exact (Subgroup.commutator_mono h2 le_rfl).trans
      (h3.trans (d.preImg_bot_le hPM hP (tImage_le χ _)))
  have hQQ : ⁅pCoreOf 2 M, pCoreOf 2 M⁆ ≤ T :=
    commutator_le_of_le h.pCore_le h.pCore_le
  rw [← tImage_commutator χ h.pCore_le h.pCore_le,
    ← tImage_commutator χ hQQ h.pCore_le] at h1 ⊢
  have hn : M ≤ Subgroup.normalizer
      ((⁅⁅pCoreOf 2 M, pCoreOf 2 M⁆, pCoreOf 2 M⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator
      (le_normalizer_commutator (le_normalizer_pCoreOf M) (le_normalizer_pCoreOf M))
      (le_normalizer_pCoreOf M)
  exact hp.tImage_le_tImage_Dq hn
    (commutator_le_of_le (commutator_le_of_le le_rfl le_rfl) le_rfl) h1

omit hp in
theorem _root_.CFSG.Quasithin.MS93.S36SP.XData.img_eq {E : Subgroup G} {v : V4 d.F}
    (hx : XData d E v) (hEM : E ≤ M) (hE : ∀ e ∈ E, ∃ g, ActsMat d.vec e g) :
    d.img E hEM hE = xPoint (d.F ∙ v) := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨e, he, heg⟩ := (d.mem_img hEM hE).1 hg
    obtain ⟨c, rfl⟩ := hx.mem e he g heg
    exact transv_mem_xPoint v c
  · obtain ⟨c, rfl⟩ := (mem_xPoint_span hx.ne).1 hg
    obtain ⟨e, he, heg⟩ := hx.all c
    exact d.actsMat_mem_img hEM hE he heg

omit hp in
theorem pre_perp_le {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v)
    (hE : ∀ e ∈ tImage χ (Z0q M T), ∃ g, ActsMat d.vec e g) :
    d.pre (perp (d.F ∙ v)) ≤ tImage χ (pCoreOf 2 M) := by
  have hEM : tImage χ (Z0q M T) ≤ M := tImage_le_M h χ _
  have hfix : perp (d.F ∙ v) ≤ fixSp (d.img _ hEM hE) := by
    rw [hx.img_eq hEM hE, fixSp_xPoint (isPoint_span hx.ne)]
  rw [← inf_centralizer_tImage_Z0q h χ]
  exact le_inf ((d.pre_le _).trans ((Uq_le_Z0q h.L_le).trans (Z0q_le_T h)))
    (d.pre_le_centralizer hEM hE hfix)

theorem exists_line {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v)
    {hPM : tImage χ (pCoreOf 2 M) ≤ M}
    {hP : ∀ x ∈ tImage χ (pCoreOf 2 M), ∃ g, ActsMat d.vec x g} :
    ∃ l : Submodule d.F (V4 d.F), IsLine l ∧ d.F ∙ v ≤ l ∧
      (∀ u ∈ d.pre l, ∀ x ∈ tImage χ (pCoreOf 2 M), ⁅u, x⁆ ∈ tImage χ (Dq M L)) ∧
      (∀ g ∈ d.img _ hPM hP, ∀ w ∈ l, mat g *ᵥ w - w ∈ d.F ∙ v) ∧
      (∃ g ∈ d.img _ hPM hP, ∃ w ∈ l, mat g *ᵥ w ≠ w) := by
  set P := tImage χ (pCoreOf 2 M) with hPdef
  set H := d.img _ hPM hP with hH
  have hfixH : fixSp H = d.F ∙ v := hp.fixSp_P hx
  have hE := hp.actsMat_E
  obtain ⟨p', l, hp', hl, hpl, hfix', h1, h2, hcl⟩ :=
    exists_flag_of_isPGroup (d.isPGroup_img hPM hP (tImage_le χ _))
  have hp'v : p' = d.F ∙ v := by
    have hle : p' ≤ d.F ∙ v := by
      rw [← hfixH]
      intro w hw
      rw [mem_fixSp]
      exact fun g hg => hfix' g hg w hw
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hp', finrank_span_singleton hx.ne])
  subst hp'v
  have hl_perp : l ≤ perp (d.F ∙ v) := hl.le_perp.trans (perp_antitone hpl)
  have hlne : l ≠ d.F ∙ v := fun e => by
    have h2' := hl.1
    rw [e, finrank_span_singleton hx.ne] at h2'
    norm_num at h2'
  have hL2 : ∃ g ∈ H, ∃ w ∈ l, mat g *ᵥ w ≠ w := by
    by_contra hcon
    push Not at hcon
    refine hlne (le_antisymm (fun w hw => ?_) hpl)
    rw [← hfixH, mem_fixSp]
    exact fun g hg => hcon g hg w hw
  refine ⟨l, hl, hpl, fun u hu x hxP => ?_, h2, hL2⟩
  have huP : u ∈ P := pre_perp_le hx hE (d.pre_mono hl_perp hu)
  by_cases hcase : H ≤ qPoint (d.F ∙ v)
  · have hab : ⁅H, H⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact qPoint_comm (isPoint_span hx.ne) (hcase hg₁) (hcase hg₂)
    exact hp.commutator_le_of_abelian hab (Subgroup.commutator_mem_commutator huP hxP)
  obtain ⟨g₀, hg₀H, hg₀⟩ := Set.not_subset.1 hcase
  obtain ⟨w, hw, hw'⟩ : ∃ w ∈ perp (d.F ∙ v), mat g₀ *ᵥ w - w ∉ d.F ∙ v := by
    by_contra hcon
    push Not at hcon
    exact hg₀ (mem_qPoint.2 ⟨hfix' g₀ hg₀H, hcon⟩)
  have hspan : l = d.F ∙ v ⊔ d.F ∙ (mat g₀ *ᵥ w - w) := by
    have hle : d.F ∙ v ⊔ d.F ∙ (mat g₀ *ᵥ w - w) ≤ l :=
      sup_le hpl ((Submodule.span_singleton_le_iff_mem _ _).2 (h1 g₀ hg₀H w hw))
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    rw [hl.1, ← Submodule.span_insert]
    exact finrank_span_pair hx.ne hw'
  obtain ⟨huU, hvec⟩ := d.mem_pre.1 hu
  rw [hspan, Submodule.mem_sup] at hvec
  obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := hvec
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy₁
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy₂
  obtain ⟨x₀, hx₀P, hx₀⟩ := (d.mem_img hPM hP).1 hg₀H
  obtain ⟨u₁, hu₁⟩ := d.surj (Multiplicative.ofAdd (b • w))
  have hu₁P : (u₁ : G) ∈ P := by
    refine pre_perp_le hx hE ((d.mem_pre_coe u₁).2 ?_)
    rw [hu₁, toAdd_ofAdd]
    exact Submodule.smul_mem _ _ hw
  have hx₀M := hPM hx₀P
  set c : G := x₀ * u₁ * x₀⁻¹ * (u₁ : G)⁻¹ with hc
  have hcU : c ∈ Uq M T L := mul_mem (conj_mem (d.normU hx₀M) u₁) (inv_mem u₁.2)
  have hcvec := d.toAdd_vec_comm hx₀M hx₀ u₁
  rw [hu₁, toAdd_ofAdd, Matrix.mulVec_smul, ← smul_sub] at hcvec
  have hrU : c⁻¹ * u ∈ Uq M T L := mul_mem (inv_mem hcU) huU
  have hrvec : Multiplicative.toAdd (d.vec ⟨c⁻¹ * u, hrU⟩) ∈ d.F ∙ v := by
    have e : (⟨c⁻¹ * u, hrU⟩ : ↥(Uq M T L)) = (⟨c, hcU⟩ : ↥(Uq M T L))⁻¹ * ⟨u, huU⟩ := rfl
    rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, ← hy, hcvec, neg_add_eq_sub,
      add_sub_cancel_right]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have hrC : c⁻¹ * u ∈ Subgroup.centralizer (P : Set G) :=
    d.pre_le_centralizer hPM hP (hfixH ▸ le_rfl) ((d.mem_pre_coe ⟨_, hrU⟩).2 hrvec)
  have hcP : c ∈ ⁅P, P⁆ := by
    have := Subgroup.commutator_mem_commutator hx₀P hu₁P
    rwa [commutatorElement_def] at this
  have e2 : ⁅u, x⁆ = ⁅c, x⁆ := by
    have hrx : (c⁻¹ * u) * x = x * (c⁻¹ * u) :=
      (Subgroup.mem_centralizer_iff.1 hrC x hxP).symm
    have hu : u = c * (c⁻¹ * u) := by group
    rw [hu]
    simp only [commutatorElement_def]
    calc c * (c⁻¹ * u) * x * (c * (c⁻¹ * u))⁻¹ * x⁻¹ =
        c * ((c⁻¹ * u) * x) * (c⁻¹ * u)⁻¹ * c⁻¹ * x⁻¹ := by group
      _ = c * (x * (c⁻¹ * u)) * (c⁻¹ * u)⁻¹ * c⁻¹ * x⁻¹ := by rw [hrx]
      _ = c * x * c⁻¹ * x⁻¹ := by group
  rw [e2]
  exact hp.commutator_commutator_le hcl (Subgroup.commutator_mem_commutator hcP hxP)

end PairHyp

end CFSG.Quasithin.MS93.S36SP
