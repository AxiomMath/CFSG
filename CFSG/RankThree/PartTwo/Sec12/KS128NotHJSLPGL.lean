module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLEnd
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open KS128NotHJTC (false_of_commute_irreducible isPGroup_zpowers_of_pow_three)
open Matrix

variable {G : Type} [Group G] [Finite G]

theorem exists_heis_trans {a : G} {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) {c x : G}
    (hcK : c ∈ K) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hxc : x * c = c * x)
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx : Sec4.InducesTypeOn K x 3) :
    Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ ∧
    ∃ Fb : Subgroup (K ⧸ aschbacherSolvableCore 3 K), CFSG.Assembly.IsElemAbelian 3 Fb ∧
      Nat.card Fb = 9 ∧ QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ ∈ Fb ∧
      ∀ u ∈ Fb, u ≠ 1 → ∀ v ∈ Fb, v ≠ 1 →
        ∃ nb ∈ Subgroup.normalizer (Fb : Set (K ⧸ aschbacherSolvableCore 3 K)),
          nb * u * nb⁻¹ = v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxN', π, p, f, 𝕂, _, hF, hq, e, y, hyH, hy3, hact⟩ := hx
  set σ := Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) with hσdef
  have hact' : ∀ z : K ⧸ aschbacherSolvableCore 3 K,
      ((e (σ z) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) 𝕂) * (ProjGenLinGroup.mk y)⁻¹ :=
    hact
  have hπ : π = false → UnitaryFieldData p f 𝕂 := fun h => by subst h; exact hF.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hF.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hF hq
  have hsc : ∀ (u : 𝕂ˣ) (A : GL (Fin 3) 𝕂),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  have : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hKq.1
  have : Group.IsPerfect (projImage (slPi π 3 (p ^ f) 𝕂)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv e (center_projImage_eq_bot hF hq)
  set cb : K ⧸ aschbacherSolvableCore 3 K :=
    QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ with hcbdef
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e cb).2
  have hc'3 : (⟨c, hcK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hcb3 : cb ^ 3 = 1 := by rw [hcbdef, ← map_pow, hc'3, map_one]
  have hcb1 : cb ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (isPGroup_zpowers_of_pow_three hc'3) (Subgroup.mem_zpowers _) (Subgroup.one_mem _)
      (by rw [map_one]; exact h1)
    exact hc1 (congrArg Subtype.val h2)
  have hsH : s ∈ glPi π 3 (p ^ f) 𝕂 := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) 𝕂 := by
    intro hsZ
    apply hcb1
    apply e.injective
    apply Subtype.ext
    rw [← hse, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) 𝕂 := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse, ← Subgroup.coe_pow, ← map_pow, hcb3,
      map_one, Subgroup.coe_one]
  have hsdet : (s : Matrix (Fin 3) (Fin 3) 𝕂).det = 1 := ((mem_slPi_iff hπ).mp hs).2
  have hfix : σ cb = cb := by
    rw [hσdef, hcbdef, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, hxc, mul_inv_cancel_right]
  have h1 := hact' cb
  rw [hfix, ← hse] at h1
  have hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) 𝕂 := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1,
      mul_inv_cancel]
  obtain ⟨lam, hlam⟩ := hysZ
  have hys : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * s := by
    rw [hlam]
    group
  rcases eq_or_ne lam 1 with hlam1 | hlam1
  ·
    exfalso
    refine false_of_commute_irreducible hτ hτ1 h3 hsdet hs3 hsZ ?_ hy3.2.2
    rw [hlam1, map_one, one_mul] at hys
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hys]
  have htr := trace_eq_zero_of_conj_eq_scalar_mul hlam1 hys
  have hsZ' : s ∉ zPi π 3 (p ^ f) 𝕂 := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hF hq hτ hτ1 hz)
  have hs3' : s ^ 3 ∈ zPi π 3 (p ^ f) 𝕂 := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3⟩
  have htype : Type123 π (p ^ f) 𝕂 s 1 := by
    rcases type123_exhaust hF hq hsH hsZ' hs3' with h1 | h2 | h3
    · exact h1
    · exact absurd htr (trace_ne_zero_of_type2 hF hq h2)
    · exact absurd ⟨s, hs, fun m _ => rfl⟩ (not_inner_of_type3 hF hq hsH h3)
  obtain ⟨τ', hτ', hτ'1, z, hz, g, hg, hD⟩ := htype
  have hτ'0 : τ' ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hτ'
    exact zero_ne_one hτ'
  have hzs : z ∈ StatedScalars (Fin 3) 𝕂 := mem_statedScalars_of_mem_zPi hF hq hτ' hτ'1 hz
  have hsz : s * z = g * diagTau hτ' * g⁻¹ := by
    rw [← hD]
    group
  have he₁ : ((e cb : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk (g * diagTau hτ' * g⁻¹) := by
    rw [← hse, ← hsz, map_mul, mk_eq_one_iff_mem_statedScalars.mpr hzs, mul_one]
  have hw : g * cycThree * g⁻¹ ∈ slPi π 3 (p ^ f) 𝕂 :=
    conj_mem_slPi hπ hg (cycThree_mem_slPi hπ)
  set x₂ : K ⧸ aschbacherSolvableCore 3 K :=
    e.symm (projOf _ ⟨g * cycThree * g⁻¹, hw⟩) with hx₂
  have he₂ : ((e x₂ : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk (g * cycThree * g⁻¹) := by
    rw [hx₂, MulEquiv.apply_symm_apply, coe_projOf]
  set μ : 𝕂ˣ := Units.mk0 τ' hτ'0 ^ (2 * 1) with hμ
  have hcd : cycThree * diagTau hτ' * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) μ * diagTau hτ' := by
    have := cycThree_pow_conj_diagTau hτ' hτ'0 1
    rwa [pow_one] at this
  have hdc : diagTau hτ' * cycThree * (diagTau hτ')⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * cycThree := by
    have e1 : cycThree * diagTau hτ' * cycThree⁻¹ * (diagTau hτ')⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) μ := by
      rw [hcd]
      group
    have e2 : diagTau hτ' * cycThree * (diagTau hτ')⁻¹ * cycThree⁻¹ =
        (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ := by
      rw [← e1]
      group
    rw [map_inv, ← e2]
    group
  have hμ1 : μ ≠ 1 := by
    intro h1
    apply hτ'1
    have h2 : τ' ^ 2 = 1 := by
      have := congrArg Units.val h1
      rwa [hμ, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
    calc τ' = τ' ^ 3 / τ' ^ 2 := by field_simp
      _ = 1 := by rw [hτ', h2, div_one]
  have hζ1 : μ⁻¹ ≠ 1 := fun h1 => hμ1 (inv_eq_one.mp h1)
  have hmkconj : ∀ w : GL (Fin 3) 𝕂, ProjGenLinGroup.mk (g * w * g⁻¹) =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk w * (ProjGenLinGroup.mk g)⁻¹ := fun w => by
    rw [map_mul, map_mul, map_inv]
  have hx₂1 : x₂ ≠ 1 := by
    intro h1
    apply not_mem_statedScalars_of_heis (y₁ := cycThree) (ζ := μ) hμ1 hcd
    rw [← mk_eq_one_iff_mem_statedScalars]
    have h2 : ((e x₂ : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) = 1 := by
      rw [h1, map_one, Subgroup.coe_one]
    rw [he₂, hmkconj] at h2
    calc ProjGenLinGroup.mk cycThree = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = 1 := by rw [h2]; group
  have hx₂n : x₂ ∉ Subgroup.zpowers cb := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply not_mk_eq_zpow_of_heis (y₁ := diagTau hτ') (y₂ := cycThree) hζ1 hdc k
    have h2 := congrArg (fun m => ((e m : projImage (slPi π 3 (p ^ f) 𝕂)) :
      ProjGenLinGroup (Fin 3) 𝕂)) hk
    simp only [map_zpow, Subgroup.coe_zpow, he₁, he₂, hmkconj] at h2
    rw [conj_zpow] at h2
    rw [map_zpow]
    calc ProjGenLinGroup.mk cycThree = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ') ^ k *
            (ProjGenLinGroup.mk g)⁻¹) * ProjGenLinGroup.mk g := by rw [h2]
      _ = ProjGenLinGroup.mk (diagTau hτ') ^ k := by group
  have hcomm12 : cb * x₂ = x₂ * cb := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, he₁, he₂, hmkconj, hmkconj]
    have R := mk_diagTau_cycThree hτ'
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ') * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) =
        ProjGenLinGroup.mk g * (ProjGenLinGroup.mk (diagTau hτ') * ProjGenLinGroup.mk cycThree) *
          (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk cycThree * ProjGenLinGroup.mk (diagTau hτ')) *
          (ProjGenLinGroup.mk g)⁻¹ := by rw [R]
      _ = ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ') * (ProjGenLinGroup.mk g)⁻¹) := by
        group
  have hx₂3 : x₂ ^ 3 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, he₂, ← map_pow, conj_pow, cycThree_pow_three, mul_one,
      mul_inv_cancel, map_one, map_one, Subgroup.coe_one]
  have hFab : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers cb ⊔ Subgroup.zpowers x₂) :=
    Sec13.isElemAbelian_zpowers_sup hcb3 hx₂3 hcomm12
  have hF9 : Nat.card (Subgroup.zpowers cb ⊔ Subgroup.zpowers x₂ : Subgroup _) = 9 :=
    card_zpowers_sup_zpowers hx₂3 (orderOf_eq_prime hcb3 hcb1) hx₂n hcomm12.symm
  have key := transitive_of_normal_form hF hq
    (L := (⊤ : Subgroup (K ⧸ aschbacherSolvableCore 3 K)))
    (Subgroup.topEquiv.trans e) hτ' hτ'1 hg (x₁ := cb) (x₂ := x₂) (Subgroup.mem_top _)
    (Subgroup.mem_top _) he₁ he₂
  refine ⟨hZ, Subgroup.zpowers cb ⊔ Subgroup.zpowers x₂, hFab, hF9,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers cb), fun u hu hu1 v hv hv1 => ?_⟩
  obtain ⟨nb, ⟨-, hnbN⟩, hnbx⟩ := key u hu hu1 v hv hv1
  exact ⟨nb, hnbN, hnbx⟩

theorem exists_lift_trans {K : Subgroup G} {c : G} (hcK : c ∈ K) (hc3 : c ^ 3 = 1)
    {Fb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)} (hFb : CFSG.Assembly.IsElemAbelian 3 Fb)
    (hFb9 : Nat.card Fb = 9)
    (hcFb : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ ∈ Fb)
    (hT : ∀ u ∈ Fb, u ≠ 1 → ∀ v ∈ Fb, v ≠ 1 →
      ∃ nb ∈ Subgroup.normalizer (Fb : Set (K ⧸ aschbacherSolvableCore 3 K)), nb * u * nb⁻¹ = v) :
    ∃ F : Subgroup G, F ≤ K ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ c ∈ F ∧
      ∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
        ∃ m ∈ K, m ∈ Subgroup.normalizer (F : Set G) ∧ m * u * m⁻¹ = v := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  set c' : K := ⟨c, hcK⟩ with hc'
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hFbp : IsPGroup 3 Fb := fun x => ⟨1, Subtype.ext (by simpa using hFb.2 x x.2)⟩
  obtain ⟨S, hcS, -, hS3, hSF⟩ := Sec13.exists_isPGroup_le_map_eq (M := ⊤) hFbp
    (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
    (isPGroup_zpowers_of_pow_three hc'3) le_top
    (by rw [MonoidHom.map_zpowers]; exact Subgroup.zpowers_le.mpr hcFb)
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hS3
  have hSab : CFSG.Assembly.IsElemAbelian 3 S :=
    Sec13.isElemAbelian_of_injOn π hinj (hSF ▸ hFb)
  have hS9 : Nat.card S = 9 := by rw [← Sec13.card_map_eq_of_injOn π hinj, hSF, hFb9]
  have hN := Sec13.normalizer_map_mk_eq hS3
  rw [hSF] at hN
  refine ⟨S.map K.subtype, Subgroup.map_subtype_le S, Sec13.isElemAbelian_map hSab K.subtype,
    by rw [Subgroup.card_map_of_injective K.subtype_injective, hS9],
    ⟨c', hcS (Subgroup.mem_zpowers c'), rfl⟩, ?_⟩
  rintro _ ⟨s₁, hs₁, rfl⟩ hs₁1 _ ⟨s₂, hs₂, rfl⟩ hs₂1
  have hne : ∀ s ∈ S, (K.subtype s : G) ≠ 1 → π s ≠ 1 := fun s hs hs1 h1 =>
    hs1 (by
      have := hinj hs (Subgroup.one_mem _) (by rw [h1, map_one])
      rw [this, map_one])
  obtain ⟨nb, hnb, hnbe⟩ := hT (π s₁) (hSF ▸ Subgroup.mem_map_of_mem π hs₁) (hne s₁ hs₁ hs₁1)
    (π s₂) (hSF ▸ Subgroup.mem_map_of_mem π hs₂) (hne s₂ hs₂ hs₂1)
  rw [hN] at hnb
  obtain ⟨n, hn, rfl⟩ := hnb
  refine ⟨n, n.2, Sec13.mem_normalizer_map_subtype hn, ?_⟩
  have hns : n * s₁ * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hn s₁).mp hs₁
  have := hinj hns hs₂ (by rw [map_mul, map_mul, map_inv]; exact hnbe)
  simpa using congrArg Subtype.val this

theorem false_of_pgl (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hG1 : Gap125NonCentralBar) (hM : KS128TypeCMove) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) (haB : a ∉ Sec4.thetaQuotCentralizer L)
    (haL : a ∈ L) {K : Subgroup G} (hK : K ∈ lA422 A a) (hcK : c ∈ K) {x : G} (hxA : x ∈ A)
    (hx : Sec4.InducesTypeOn K x 3) : False := by
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  obtain ⟨haA, ha3', -⟩ := Sec13.zpowers_mem_omegaA_iff.mp ha
  have ha1 : a ≠ 1 := ne_one_of_card_zpowers_eq_three ha3'
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hxc : x * c = c * x := congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hxA⟩ ⟨c, h.mem_A⟩)
  obtain ⟨hZ, Fb, hFab, hF9, hcF, hT⟩ :=
    exists_heis_trans hK.1 hcK (hAe.2 c h.mem_A) h.ne_one hxc hx.1 hx
  obtain ⟨F, hFK, hFe, hF9', hcF', hT'⟩ := exists_lift_trans hcK (hAe.2 c h.mem_A) hFab hF9 hcF hT
  exact false_of_transitive h45 hK2 hG1 hM h hSL ha3 haB haL hK.1
    (Proof128.not_mem_of_center_eq_bot hK.1 hZ ha3 ha1) hFK hFe hF9' hcF' hT'

end CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL
