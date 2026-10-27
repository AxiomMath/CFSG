module

public import CFSG.Quasithin.Vol2.KGFactL3EvenLevi
public import CFSG.Quasithin.Vol2.KGFactInsp4316Props
public import CFSG.Quasithin.Vol2.KGFactInspBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.Quasithin.Vol2.KGFactL3EvenBorel

public section

namespace CFSG.Quasithin.H13.KGL3Even

open Matrix CFSG.Quasithin.H13.Ch4.KGSL3 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem card_eq_card_map_mul {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G')
    (H : Subgroup G) : Nat.card H = Nat.card (H.map f) * Nat.card ↥(H ⊓ f.ker) := by
  set φ : ↥H →* G' := f.comp H.subtype with hφ
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  have hrange : φ.range = H.map f := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card ↥(H ⊓ f.ker) := by
    have : φ.ker = f.ker.subgroupOf H := by
      ext x
      simp [hφ, Subgroup.mem_subgroupOf]
    rw [this, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h1, hrange, hker, mul_comm]

variable {F : Type} [Field F]

theorem proj_mem_of_mem_centralizer {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ Subgroup.centralizer ((uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F))) :
    proj 3 F g ∈ (uSub : Subgroup (SpecialLinearGroup (Fin 3) F)).map (proj 3 F) := by
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := entries_of_mem_centralizer hg
  set d := (g : Matrix (Fin 3) (Fin 3) F) 2 2 with hd
  have hdet : d ^ 3 = 1 := by
    have h := g.2
    rw [det_fin_three, g0, g1, g2, g3, g4, g5] at h
    linear_combination h
  have hd0 : d ≠ 0 := by
    rintro h0
    rw [h0] at hdet
    norm_num at hdet
  set u : Fˣ := Units.mk0 d hd0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [hu, hdet])
  refine ⟨uSL (d⁻¹ * (g : Matrix (Fin 3) (Fin 3) F) 0 2) (d⁻¹ * (g : Matrix (Fin 3) (Fin 3) F) 1 2),
    ⟨_, _, rfl⟩, ?_⟩
  rw [proj_eq_proj_iff]
  refine ⟨u, hu3, ?_⟩
  change (((uSL _ _)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * g = _
  rw [uSL_inv]
  change uMat _ _ * (g : Matrix (Fin 3) (Fin 3) F) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, g0, g1, g2, g3, g4, g5,
      hu, ← hd] <;> field_simp <;> ring

theorem card_inf_centralizer [Finite F] [CharP F 2] {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hZ : scalars 3 F ≤ K) : ∃ c : ℕ, Nat.card ↥(K ⊓ Subgroup.centralizer
      ((uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) : Set (SpecialLinearGroup (Fin 3) F))) =
        2 ^ c * Nat.card (scalars 3 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ((uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) :
    Set (SpecialLinearGroup (Fin 3) F))
  have h := card_eq_card_map_mul (proj 3 F) (K ⊓ C)
  have hker : (K ⊓ C) ⊓ (proj 3 F).ker = scalars 3 F := by
    rw [ker_proj]
    refine le_antisymm inf_le_right (le_inf (le_inf hZ ?_) le_rfl)
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr fun u _ =>
      (Subgroup.mem_center_iff.mp (scalars_le_center 3 F hz)) u
  have h2 : IsPGroup 2 ((K ⊓ C).map (proj 3 F)) := by
    refine (isPGroup_uSub.map (proj 3 F)).to_le ?_
    rintro _ ⟨g, hg, rfl⟩
    exact proj_mem_of_mem_centralizer hg.2
  obtain ⟨c, hc⟩ := h2.exists_card_eq
  exact ⟨c, by rw [h, hker, hc]⟩

theorem theta_mem_scalars {z : SpecialLinearGroup (Fin 3) F} (hz : z ∈ scalars 3 F) :
    theta z ∈ scalars 3 F := by
  obtain ⟨c, hc, hz⟩ := hz
  refine ⟨c⁻¹, by rw [inv_pow, hc, inv_one], ?_⟩
  change ((jSL * SpecialLinearGroup.transpose z⁻¹ * jSL : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) = _
  change jMat * ((z⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * jMat = _
  have hzi : ((z⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) ((c⁻¹ : Fˣ) : F) := by
    have h1 : (z : Matrix (Fin 3) (Fin 3) F) *
        ((z⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
      congrArg Subtype.val (mul_inv_cancel z)
    rw [hz] at h1
    calc ((z⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        = Matrix.scalar (Fin 3) ((c⁻¹ : Fˣ) : F) * (Matrix.scalar (Fin 3) (c : F) *
            ((z⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
          rw [← mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
            one_mul]
      _ = _ := by rw [h1, mul_one]
  rw [hzi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply]

theorem scalars_le_map_theta :
    scalars 3 F ≤ (scalars 3 F).map (theta (F := F)).toMonoidHom := by
  intro z hz
  exact ⟨theta z, theta_mem_scalars hz, thetaFun_thetaFun z⟩

theorem map_theta_scalars : (scalars 3 F).map (theta (F := F)).toMonoidHom = scalars 3 F := by
  refine le_antisymm ?_ scalars_le_map_theta
  rintro _ ⟨z, hz, rfl⟩
  exact theta_mem_scalars hz

theorem eq_of_two_pow_mul {a b u v : ℕ} (hu : Odd u) (hv : Odd v) (h : 2 ^ a * u = 2 ^ b * v) :
    u = v := by
  rcases le_total a b with hab | hab
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa using h'
    · exfalso
      have : 2 ∣ u := h' ▸ (dvd_pow_self 2 hd.ne').mul_right v
      exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr this)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa using h'
    · exfalso
      have : 2 ∣ v := h' ▸ (dvd_pow_self 2 hd.ne').mul_right u
      exact (Nat.not_even_iff_odd.mpr hv) (even_iff_two_dvd.mpr this)

end CFSG.Quasithin.H13.KGL3Even

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag StatedProj StatedSU
  StatedScalars
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.KGL3Even CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.Ch4.KGSL3 (uSub uSub_comm)
open scoped MatrixGroups

namespace Cfg4316

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X} {n : ℕ} {x : X}

theorem toCfg (h : Cfg4316 S R K n x) : KGInsp43.Cfg S R K n :=
  ⟨h.normal, h.simple, h.cent, h.two_le, h.ne_bot, h.isPGroup, h.le, h.perfect, h.le_normalizer,
    h.normalizer_le, h.chi⟩

theorem core (h : Cfg4316 S R K n x) : ∀ N : Subgroup X, N ≤ K →
    K ≤ Subgroup.normalizer (N : Set X) → IsPGroup 2 N → N ≤ R := fun _ hNK hKN hN2 =>
  (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNK hKN hN2).trans h.core_le

theorem K_ne_bot (h : Cfg4316 S R K n x) : K ≠ ⊥ := by
  intro hb
  have h3 := h.toCfg.three_dvd_card
  rw [hb, Subgroup.card_bot] at h3
  omega

theorem perfect_subgroupOf (h : Cfg4316 S R K n x) :
    ⁅K.subgroupOf S, K.subgroupOf S⁆ = K.subgroupOf S := by
  apply Subgroup.map_injective S.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.le]
  exact h.perfect

theorem eq_of_psl3_two (h : Cfg4316 S R K n x) (hRS : R ≤ S) {e : ℕ} (he : 2 ≤ e)
    (hm : StatedClassicalModel ↥S .PSL 3 2 e) : n = e := by
  obtain ⟨-, F, _, _, hF, ⟨e₁⟩⟩ := hm
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := e)
    (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  let φ : ↥S ≃* projectiveSL 3 F :=
    e₁.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 F)
  have hc₁ := (lconf_subgroupOf hRS h.le h.le_normalizer h.normalizer_le h.core).map φ
  have hR₁2 : IsPGroup 2 ((R.subgroupOf S).map φ.toMonoidHom) :=
    (h.isPGroup.comap_of_injective S.subtype S.subtype_injective).map _
  obtain ⟨g, hg⟩ := exists_conj_le hR₁2
  have hc₂ := hc₁.map (MulAut.conj g)
  set R₂ := ((R.subgroupOf S).map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom with hR₂
  set K₂ := ((K.subgroupOf S).map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom with hK₂
  obtain ⟨hc₀, hmapR, hmapK⟩ := lconf_lift hc₂ hg
  set R₀ := R₂.comap (proj 3 F) ⊓ unitriangular 3 F with hR₀
  set K₀ := K₂.comap (proj 3 F) with hK₀def
  have hK₂card : Nat.card K₂ = Nat.card K := by
    rw [hK₂, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv]
  have hK₂perf : ⁅K₂, K₂⁆ = K₂ := by
    rw [hK₂, ← Subgroup.map_commutator, ← Subgroup.map_commutator, h.perfect_subgroupOf]
  have hR₀1 : R₀ ≠ ⊥ := by
    intro hb
    apply h.ne_bot
    have h1 : R₀.map (proj 3 F) = ⊥ := by rw [hb, Subgroup.map_bot]
    rw [hmapR] at h1
    have h2 : (R.subgroupOf S).map φ.toMonoidHom = ⊥ := by
      rw [← map_map_symm (MulAut.conj g) ((R.subgroupOf S).map φ.toMonoidHom)]
      change R₂.map _ = ⊥
      rw [h1, Subgroup.map_bot]
    have h3 : R.subgroupOf S = ⊥ := by
      rw [← map_map_symm φ (R.subgroupOf S), h2, Subgroup.map_bot]
    rw [← Subgroup.map_subgroupOf_eq_of_le hRS, h3, Subgroup.map_bot]
  have hK₀C : ¬ Comm2 K₀ := by
    intro hC
    have h2 : Comm2 K₂ := hmapK ▸ hC.map (proj 3 F)
    have h3 : Comm2 (K.subgroupOf S) :=
      Comm2.of_map φ (Comm2.of_map (MulAut.conj g) h2)
    have h4' : Comm2 K := by
      have := h3.map S.subtype
      rwa [Subgroup.map_subgroupOf_eq_of_le h.le] at this
    exact not_comm2_of_perfect h.perfect h.K_ne_bot h4'
  have hZK₀ : scalars 3 F ≤ K₀ := by
    intro z hz
    show proj 3 F z ∈ K₂
    rw [(proj_eq_one_iff).mpr hz]
    exact K₂.one_mem
  have hK₀Z : K₀ ≤ ⁅K₀, K₀⁆ ⊔ scalars 3 F := by
    intro k hk
    have hk' : proj 3 F k ∈ ⁅K₂, K₂⁆ := by rw [hK₂perf]; exact hk
    rw [← hmapK, ← Subgroup.map_commutator] at hk'
    obtain ⟨c, hc, hck⟩ := hk'
    have hz : c⁻¹ * k ∈ scalars 3 F := proj_eq_proj_iff.mp hck
    have : k = c * (c⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hz)
  have hK₀card : Nat.card K₀ = Nat.card K * Nat.card (scalars 3 F) := by
    rw [card_eq_card_map_mul (proj 3 F) K₀, hmapK, hK₂card, ker_proj,
      inf_eq_right.mpr hZK₀]
  obtain ⟨K₃, hc₃, hK₃C, hZK₃, hK₃Z, hK₃card⟩ :
      ∃ K₃ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F),
      LConf (uSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) K₃ ∧ ¬ Comm2 K₃ ∧
        scalars 3 F ≤ K₃ ∧ K₃ ≤ ⁅K₃, K₃⁆ ⊔ scalars 3 F ∧ Nat.card K₃ = Nat.card K₀ := by
    rcases unitri_trichotomy hc₀ inf_le_right hR₀1 hK₀C with h1 | h1
    · have hc : LConf (uSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) K₀ := by
        rw [← h1]
        exact hc₀
      exact ⟨K₀, hc, hK₀C, hZK₀, hK₀Z, rfl⟩
    · have hc : LConf (uSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
          (K₀.map theta.toMonoidHom) := by
        have := hc₀.map theta
        rw [h1] at this
        exact this
      refine ⟨K₀.map theta.toMonoidHom, hc, fun hC => hK₀C (Comm2.of_map theta hC),
        scalars_le_map_theta.trans (Subgroup.map_mono hZK₀), ?_,
        Subgroup.card_map_of_injective theta.injective⟩
      have := Subgroup.map_mono (f := theta.toMonoidHom) hK₀Z
      rwa [Subgroup.map_sup, Subgroup.map_commutator, map_theta_scalars] at this
  have hU1 : (uSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ≠ ⊥ := by
    intro hb
    have := card_uSub (F := F)
    rw [hb, Subgroup.card_bot, hF] at this
    have h1 : 1 < (2 ^ e) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    omega
  have hKP : K₃ ≤ planeStab := hc₃.le_normalizer.trans (normalizer_le_planeStab le_rfl hU1)
  have hPK : planeStab ≤ Subgroup.normalizer (K₃ : Set (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    (planeCoord (F := F)).le_normalizer.trans hc₃.normalizer_le
  have hKC : ¬ K₃ ≤ Subgroup.centralizer ((uSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
      Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    intro hC
    apply hK₃C
    intro a ha b hb
    have hKK : ⁅⁅K₃, K₃⁆, ⁅K₃, K₃⁆⁆ ≤ K₃ := by
      have hK1 : ⁅K₃, K₃⁆ ≤ K₃ := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        rw [commutatorElement_def]
        exact K₃.mul_mem (K₃.mul_mem (K₃.mul_mem hx hy) (K₃.inv_mem hx)) (K₃.inv_mem hy)
      exact (Subgroup.commutator_mono hK1 hK1).trans hK1
    exact centralizer_comm (hC (hKK ha)) (hC (hKK hb))
  have himg := rho_image_eq h4 hKP hPK hK₃Z hKC
  have hρ := card_eq_card_map_mul rho (K₃.subgroupOf planeStab)
  rw [himg, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv] at hρ
  have hslcard : Nat.card ↥(slKer : Subgroup (GL (Fin 2) F)) = 2 ^ e * (4 ^ e - 1) := by
    rw [← Nat.card_congr (slEquiv (F := F)).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF, ← pow_mul, mul_comm e 2,
      pow_mul]
    norm_num
  have hkercard : Nat.card ↥(K₃.subgroupOf planeStab ⊓ rho.ker) =
      Nat.card ↥(K₃ ⊓ Subgroup.centralizer
        ((uSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 3) F))) := by
    have hmap : (K₃.subgroupOf planeStab ⊓ rho.ker).map planeStab.subtype =
        K₃ ⊓ Subgroup.centralizer ((uSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
      ext y
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨Subgroup.mem_subgroupOf.mp hy1, (rho_eq_one_iff y).mp (MonoidHom.mem_ker.mp hy2)⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨⟨y, hKP hy1⟩, ⟨Subgroup.mem_subgroupOf.mpr hy1,
          MonoidHom.mem_ker.mpr ((rho_eq_one_iff ⟨y, hKP hy1⟩).mpr hy2)⟩, rfl⟩
    rw [← Subgroup.card_map_of_injective planeStab.subtype_injective, hmap]
  rw [hkercard] at hρ
  obtain ⟨c, hc⟩ := card_inf_centralizer hZK₃
  rw [hc, hK₃card, hK₀card, hslcard] at hρ
  obtain ⟨F', _, _, hF', χ, hχ, hχk⟩ := h.chi
  have hKχ : Nat.card K = Nat.card χ.ker * Nat.card SL(2, F') := by
    have h1 := Subgroup.card_mul_index χ.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hχ, Subgroup.card_top] at h1
    exact h1.symm
  obtain ⟨b, hb⟩ := hχk.exists_card_eq
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card (α := F'),
    hF', hb] at hKχ
  rw [hKχ] at hρ
  have hm0 : 0 < Nat.card (scalars 3 F) := Nat.card_pos
  have h4n : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4n] at hρ
  have hρ' : 2 ^ (b + n) * (4 ^ n - 1) = 2 ^ (e + c) * (4 ^ e - 1) := by
    have : (2 ^ b * (2 ^ n * (4 ^ n - 1))) * Nat.card (scalars 3 F) =
        (2 ^ e * (4 ^ e - 1) * 2 ^ c) * Nat.card (scalars 3 F) := by
      rw [hρ]; ring
    have := Nat.eq_of_mul_eq_mul_right hm0 this
    rw [pow_add, pow_add]
    linarith
  have hodd : ∀ k : ℕ, 1 ≤ k → Odd (4 ^ k - 1) := by
    intro k hk
    have : 4 ≤ 4 ^ k := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h2 : 2 ∣ 4 ^ k := (by norm_num : 2 ∣ 4).trans (dvd_pow_self 4 (by omega))
    rw [Nat.odd_iff]
    omega
  have hn1 : 1 ≤ n := by have := h.two_le; omega
  have := eq_of_two_pow_mul (hodd n hn1) (hodd e (by omega)) hρ'
  have h44 : 4 ^ n = 4 ^ e := by
    have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 1 ≤ 4 ^ e := Nat.one_le_pow _ _ (by norm_num)
    omega
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h44

end Cfg4316

theorem exists_prime_dvd_two_pow_sub_one {e : ℕ} (he : 3 ≤ e) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ∣ 2 ^ e - 1 := by
  have key : ∀ m : ℕ, 3 ≤ m → (2 ^ m) % 3 = 2 →
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ∣ 2 ^ m - 1 := by
    intro m hm hmod
    have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    refine ⟨(2 ^ m - 1).minFac, Nat.minFac_prime (by omega), fun h => ?_, fun h => ?_,
      Nat.minFac_dvd _⟩
    · have h' := Nat.minFac_dvd (2 ^ m - 1)
      rw [h] at h'
      omega
    · have h' := Nat.minFac_dvd (2 ^ m - 1)
      rw [h] at h'
      omega
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' e
  ·
    have hk2 : 2 ≤ k := by omega
    have hdvd : ∀ d : ℕ, d ∣ 2 ^ k - 1 ∨ d ∣ 2 ^ k + 1 → d ∣ 2 ^ e - 1 := by
      intro d hd
      have he' : 2 ^ e - 1 = (2 ^ k + 1) * (2 ^ k - 1) := by
        rw [hk, two_mul, pow_add, ← Nat.sq_sub_sq, sq]
      rw [he']
      rcases hd with hd | hd
      · exact hd.mul_left _
      · exact hd.mul_right _
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
    ·
      have hmod : (2 ^ k) % 3 = 1 := by
        rw [hj]; exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_pow_even_mod j
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      refine ⟨(2 ^ k + 1).minFac, Nat.minFac_prime (by omega), fun h => ?_, fun h => ?_,
        hdvd _ (Or.inr (Nat.minFac_dvd _))⟩
      · have h' := Nat.minFac_dvd (2 ^ k + 1)
        rw [h] at h'
        omega
      · have h' := Nat.minFac_dvd (2 ^ k + 1)
        rw [h] at h'
        omega
    ·
      have hmod : (2 ^ k) % 3 = 2 := by
        rw [hj]; exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_pow_odd_mod j
      obtain ⟨r, hr, hr2, hr3, hrd⟩ := key k (by omega) hmod
      exact ⟨r, hr, hr2, hr3, hdvd r (Or.inl hrd)⟩
  · exact key e he (by rw [hk]; exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_pow_odd_mod k)

theorem two_le_pRank_of_psl3_two {A : Type} [Group A] [Finite A] {e r : ℕ}
    (hm : StatedClassicalModel A .PSL 3 2 e) (hr : r.Prime) (hr3 : r ≠ 3) (hrd : r ∣ 2 ^ e - 1) :
    2 ≤ CFSG.pRank r A := by
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ := hm
  have := Fact.mk hr
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
    (by rw [Nat.card_units, hK]; exact hrd)
  exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_mulEquiv hr e₁
    (CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_torus hr3 hζ (i₀ := (0 : Fin 3))
      (i₁ := 1) (i₂ := 2) (by decide) (by decide) (by decide)
      (CFSG.SectionRank.ClassicalEven.torusDiag_mem_SL
        (CFSG.SectionRank.ClassicalEven.prod_torusVec ζ _ _))
      (CFSG.SectionRank.ClassicalEven.torusDiag_mem_SL
        (CFSG.SectionRank.ClassicalEven.prod_torusVec ζ _ _)))

namespace Cfg4316

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X} {n : ℕ} {x : X}

theorem eq_two_of_psl3_two (h : Cfg4316 S R K n x) (hRS : R ≤ S) {e : ℕ} (he : 2 ≤ e)
    (hm : StatedClassicalModel ↥S .PSL 3 2 e) : n = 2 ∧ e = 2 := by
  have hne := h.eq_of_psl3_two hRS he hm
  subst hne
  refine ⟨?_, ?_⟩ <;> by_contra hne <;>
  · obtain ⟨r, hr, hr2, hr3, hrd⟩ := exists_prime_dvd_two_pow_sub_one (e := n) (by omega)
    have h2 := two_le_pRank_of_psl3_two hm hr hr3 hrd
    have : Fact r.Prime := ⟨hr⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype] at h2
    rcases h.prime r hr hr2 hrd with h1 | ⟨h3, -⟩
    · omega
    · exact hr3 h3

end Cfg4316

end CFSG.Quasithin.H13.KGInsp4316
