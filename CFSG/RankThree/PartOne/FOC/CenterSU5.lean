module

public import CFSG.RankThree.PartOne.FOC.Cases
public import CFSG.RankThree.PartOne.FOC.SU5Cen
public import CFSG.RankThree.PartOne.FOC.CompPullback
public import CFSG.RankThree.PartOne.FOC.CompGroup
public import CFSG.RankThree.PartOne.S11c.PlaneSU5

public section

namespace CFSG.RankThree.PartOne.FOC

open Matrix CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.Assembly.RankThreeEven (localRank)

theorem quasiFactored_top {G : Type} [Group G] (hq : CFSG.IsQuasisimple G) :
    QuasiFactored (⊤ : Subgroup G) := by
  refine ⟨Unit, fun _ => ⊤, fun _ => ?_, fun _ => le_rfl, fun _ _ _ _ _ => Subgroup.mem_top _,
    fun g _ => ⟨1, g, by simp, fun c _ => by simp, ?_⟩⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  · exact Subgroup.mem_iSup_of_mem () (Subgroup.mem_top _)

theorem fieldInnerCenter :
    FieldInnerCenter := by
  intro H _ _ p J A c u v E hp hp5 hrank hJq hJcat hcover hAN hAe hAcard hcA hc1 hcC huA hvA huJ hE
    huE hfl
  obtain ⟨hpZ, rfl, hZ, n, hn, hmodel⟩ := hcover
  have : Group.IsPerfect ↥J := hJq.1
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := hmodel
  obtain ⟨h5, ⟨ψ0⟩⟩ := KFSU5.exists_su5_iso hZ hn hKcard e
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hKcard, ← pow_mul, mul_comm]⟩
  have heq : unitarySU 2 n K 5 = gamma5 hU := unitarySU_eq_gramSU hU 5
  let ψ : gamma5 hU ≃* J := (MulEquiv.subgroupCongr heq.symm).trans ψ0
  have hperf : Group.IsPerfect (gamma5 hU) :=
    CFSG.RankThree.Classical.isPerfect_gramSU_one hU (by norm_num) (fun hh => absurd hh.1
      (by norm_num))
  have hfinK : Finite K := hU.finite
  have hcenΓ : Nat.card (Subgroup.center (gamma5 hU)) = 5 := by
    calc Nat.card (Subgroup.center (gamma5 hU)) =
        Nat.card ((Subgroup.center (gamma5 hU)).map ψ.toMonoidHom) :=
          (Subgroup.card_map_of_injective ψ.injective).symm
      _ = Nat.card (Subgroup.center J) := by
          rw [CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv ψ]
      _ = 5 := hZ
  have hSq : CFSG.IsQuasisimple ↥(gamma5 hU) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hJq
  have hZc : normOneScalars hU (gamma5 hU) 5 ≤ Subgroup.center (gamma5 hU) :=
    normOneScalars_le_center hU _ 5
  have hZcard : Nat.card (normOneScalars hU (gamma5 hU) 5) = 5 := by
    rw [CFSG.RankThree.Classical.card_normOneScalars_one hU (by norm_num)]
    exact Nat.gcd_eq_left h5
  have hZeq : normOneScalars hU (gamma5 hU) 5 = Subgroup.center (gamma5 hU) :=
    Subgroup.eq_of_le_of_card_ge hZc (by rw [hZcard, hcenΓ])
  have hv5 : v ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian v hvA
  have hcomm : u * v = v * u := congrArg Subtype.val (hAe.is_comm.comm ⟨u, huA⟩ ⟨v, hvA⟩)
  have hvN := hAN hvA
  have huN := hAN huA
  obtain ⟨P, c', hc', hP5, hPconj⟩ : ∃ (P : unit5 hU) (c' : Kˣ), hU.norm (c' : K) = 1 ∧
      (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c' ∧
      ∀ g : gamma5 hU, ((inducedAut ψ v hvN g : gamma5 hU) : GL (Fin 5) K) =
        (P : GL (Fin 5) K) * (g : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹ := by
    by_cases hvJ : v ∈ J
    · set P0 : gamma5 hU := ψ.symm ⟨v, hvJ⟩ with hP0
      have hψP0 : ((ψ P0 : J) : H) = v := by rw [hP0, MulEquiv.apply_symm_apply]
      refine ⟨⟨(P0 : GL (Fin 5) K), ((mem_gramSU_iff_unitary hU).mp P0.2).1⟩, 1, ?_, ?_, ?_⟩
      · simp [UnitaryFieldData.norm]
      · have h1 : P0 ^ 5 = 1 := by
          apply ψ.injective
          apply Subtype.ext
          rw [map_pow, map_one]
          show ((ψ P0 : J) : H) ^ 5 = 1
          rw [hψP0]
          exact hv5
        have h2 := congrArg Subtype.val h1
        rw [Subgroup.coe_pow] at h2
        rw [map_one]
        exact h2
      · intro g
        have h1 := coe_inducedAut ψ v hvN g
        have h2 : inducedAut ψ v hvN g = P0 * g * P0⁻¹ := by
          apply ψ.injective
          apply Subtype.ext
          rw [h1, map_mul, map_mul, map_inv]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hψP0]
        rw [h2]
        simp
    · rcases su5_aut_classification hU h5 hperf hcenΓ (inducedAut ψ v hvN)
          (inducedAut_pow ψ v hvN hv5) with ⟨P, c, hc, hP5, hconj⟩ | ⟨φ, M, hφ5, -, hconj⟩
      · exact ⟨P, c, hc, hP5, hconj⟩
      · exfalso
        have := su5_fcase_loc hU h5 ψ hv5 hvJ hvN φ M hφ5 hconj
        omega
  obtain ⟨j, hjJ, z, hzC, hu_eq⟩ := PlaneInner.exists_mul_of_mem_sup_centralizer huJ
  set jt : gamma5 hU := ψ.symm ⟨j, hjJ⟩ with hjt
  have hψjt : ((ψ jt : J) : H) = j := by rw [hjt, MulEquiv.apply_symm_apply]
  have hθu : ∀ g : gamma5 hU, inducedAut ψ u huN g = jt * g * jt⁻¹ := by
    intro g
    apply ψ.injective
    apply Subtype.ext
    rw [coe_inducedAut ψ u huN g, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hψjt, hu_eq]
    have hzg : ((ψ g : J) : H) * z = z * ((ψ g : J) : H) :=
      Subgroup.mem_centralizer_iff.mp hzC _ (ψ g).2
    calc j * z * ((ψ g : J) : H) * (j * z)⁻¹ = j * (z * ((ψ g : J) : H)) * z⁻¹ * j⁻¹ := by group
      _ = j * (((ψ g : J) : H) * z) * z⁻¹ * j⁻¹ := by rw [hzg]
      _ = j * ((ψ g : J) : H) * j⁻¹ := by group
  have hθcomm : ∀ g : gamma5 hU, inducedAut ψ u huN (inducedAut ψ v hvN g) =
      inducedAut ψ v hvN (inducedAut ψ u huN g) := by
    intro g
    have h1 : inducedAutHom ψ ((⟨u, huN⟩ : Subgroup.normalizer (J : Set H)) * ⟨v, hvN⟩) =
        inducedAutHom ψ ((⟨v, hvN⟩ : Subgroup.normalizer (J : Set H)) * ⟨u, huN⟩) := by
      congr 1
      exact Subtype.ext hcomm
    rw [map_mul, map_mul, inducedAutHom_apply, inducedAutHom_apply] at h1
    exact congrArg (fun θ : gamma5 hU ≃* gamma5 hU => θ g) h1
  have hPU : (P : GL (Fin 5) K) ∈ primeFormUnitary hU ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
    P.2
  have hconj2 : ∀ g : gamma5 hU, (jt : GL (Fin 5) K) * ((P : GL (Fin 5) K) * (g : GL (Fin 5) K) *
      (P : GL (Fin 5) K)⁻¹) * (jt : GL (Fin 5) K)⁻¹ = (P : GL (Fin 5) K) *
        ((jt : GL (Fin 5) K) * (g : GL (Fin 5) K) * (jt : GL (Fin 5) K)⁻¹) * (P : GL (Fin 5) K)⁻¹ := by
    intro g
    have h1 := congrArg (fun x : gamma5 hU => (x : GL (Fin 5) K)) (hθcomm g)
    simp only [hθu, hPconj, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1
  have hcg : ∀ g : gamma5 hU, (P : GL (Fin 5) K) * (jt : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹ *
      (g : GL (Fin 5) K) * ((P : GL (Fin 5) K) * (jt : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹)⁻¹ =
        (jt : GL (Fin 5) K) * (g : GL (Fin 5) K) * (jt : GL (Fin 5) K)⁻¹ := by
    intro g
    have hg' : (P : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) * ((P : GL (Fin 5) K)⁻¹)⁻¹ ∈
        gamma5 hU := conj_mem_gramSU hU _ (inv_mem hPU) g.2
    have h1 := hconj2 ⟨(P : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) * ((P : GL (Fin 5) K)⁻¹)⁻¹, hg'⟩
    simp only [inv_inv] at h1
    calc (P : GL (Fin 5) K) * (jt : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) *
          ((P : GL (Fin 5) K) * (jt : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹)⁻¹
        = (P : GL (Fin 5) K) * ((jt : GL (Fin 5) K) * ((P : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) *
            (P : GL (Fin 5) K)) * (jt : GL (Fin 5) K)⁻¹) * (P : GL (Fin 5) K)⁻¹ := by group
      _ = (jt : GL (Fin 5) K) * ((P : GL (Fin 5) K) * ((P : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) *
            (P : GL (Fin 5) K)) * (P : GL (Fin 5) K)⁻¹) * (jt : GL (Fin 5) K)⁻¹ := h1.symm
      _ = (jt : GL (Fin 5) K) * (g : GL (Fin 5) K) * (jt : GL (Fin 5) K)⁻¹ := by group
  have hajt : (P : GL (Fin 5) K) * (jt : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹ ∈ gamma5 hU :=
    conj_mem_gramSU hU _ hPU jt.2
  set a : gamma5 hU := ⟨(P : GL (Fin 5) K) * (jt : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹, hajt⟩
    with ha
  have hcen : a⁻¹ * jt ∈ Subgroup.center (gamma5 hU) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have h1 := hcg g
    have h2 : (a : GL (Fin 5) K) = (P : GL (Fin 5) K) * (jt : GL (Fin 5) K) *
        (P : GL (Fin 5) K)⁻¹ := rfl
    rw [← h2] at h1
    apply mul_left_cancel (a := (a : GL (Fin 5) K))
    calc (a : GL (Fin 5) K) * ((g : GL (Fin 5) K) * ((a : GL (Fin 5) K)⁻¹ * (jt : GL (Fin 5) K)))
        = ((a : GL (Fin 5) K) * (g : GL (Fin 5) K) * (a : GL (Fin 5) K)⁻¹) * (jt : GL (Fin 5) K) := by
          group
      _ = (jt : GL (Fin 5) K) * (g : GL (Fin 5) K) := by rw [h1]; group
      _ = (a : GL (Fin 5) K) * ((a : GL (Fin 5) K)⁻¹ * (jt : GL (Fin 5) K) * (g : GL (Fin 5) K)) := by
          group
  rw [← hZeq] at hcen
  obtain ⟨c'', hn'', hc5'', hscal⟩ := hcen
  have hrel : ((jt : GL (Fin 5) K))⁻¹ * (P : GL (Fin 5) K) * (jt : GL (Fin 5) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 5) c''⁻¹ * (P : GL (Fin 5) K) := by
    have hs : (P : GL (Fin 5) K) * (jt : GL (Fin 5) K)⁻¹ * (P : GL (Fin 5) K)⁻¹ *
        (jt : GL (Fin 5) K) = Matrix.GeneralLinearGroup.scalar (Fin 5) c'' := by
      rw [← hscal]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show (a : GL (Fin 5) K) = (P : GL (Fin 5) K) * (jt : GL (Fin 5) K) *
        (P : GL (Fin 5) K)⁻¹ from rfl]
      group
    have h1 : (jt : GL (Fin 5) K)⁻¹ * (P : GL (Fin 5) K)⁻¹ * (jt : GL (Fin 5) K) =
        (P : GL (Fin 5) K)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 5) c'' := by
      rw [← hs]
      group
    have h2 := congrArg (fun x : GL (Fin 5) K => x⁻¹) h1
    simp only [_root_.mul_inv_rev, inv_inv] at h2
    rw [map_inv, mul_assoc]
    exact h2
  let ι : gamma5 hU →* H := J.subtype.comp ψ.toMonoidHom
  have hι : Function.Injective ι := fun x y hxy =>
    ψ.injective (Subtype.ext hxy)
  have hιψ : ∀ g, ι g = ((ψ g : J) : H) := fun g => rfl
  have hθv_fix : ∀ g : gamma5 hU, ι g ∈ Subgroup.centralizer ({v} : Set H) ↔
      g ∈ cenSU hU 5 (P : GL (Fin 5) K) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff, mem_cenSU]
    have h1 := coe_inducedAut ψ v hvN g
    constructor
    · intro hg
      have h2 : inducedAut ψ v hvN g = g := by
        apply ψ.injective
        apply Subtype.ext
        rw [h1]
        have : ((ψ g : J) : H) * v = v * ((ψ g : J) : H) := hg
        calc v * ((ψ g : J) : H) * v⁻¹ = ((ψ g : J) : H) * v * v⁻¹ := by rw [this]
          _ = ((ψ g : J) : H) := by group
      have h3 := hPconj g
      rw [h2] at h3
      calc (g : GL (Fin 5) K) * (P : GL (Fin 5) K) = (P : GL (Fin 5) K) * (g : GL (Fin 5) K) *
            (P : GL (Fin 5) K)⁻¹ * (P : GL (Fin 5) K) := by rw [← h3]
        _ = (P : GL (Fin 5) K) * (g : GL (Fin 5) K) := by group
    · intro hg
      have h3 := hPconj g
      have h2 : inducedAut ψ v hvN g = g := by
        apply Subtype.ext
        rw [h3, ← hg]
        group
      have h4 : ((ψ (inducedAut ψ v hvN g) : J) : H) = ((ψ g : J) : H) := by rw [h2]
      rw [h1] at h4
      calc ((ψ g : J) : H) * v = (v * ((ψ g : J) : H) * v⁻¹) * v := by rw [h4]
        _ = v * ((ψ g : J) : H) := by group
  have hN : J ⊓ Subgroup.centralizer ({v} : Set H) = (cenSU hU 5 (P : GL (Fin 5) K)).map ι := by
    ext x
    constructor
    · rintro ⟨hxJ, hxC⟩
      refine ⟨ψ.symm ⟨x, hxJ⟩, (hθv_fix _).mp ?_, ?_⟩
      · have : ι (ψ.symm ⟨x, hxJ⟩) = x := by
          rw [hιψ, MulEquiv.apply_symm_apply]
        rw [this]
        exact hxC
      · rw [hιψ, MulEquiv.apply_symm_apply]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(ψ g).2, (hθv_fix g).mpr hg⟩
  have hE' : IsComponentOf ((cenSU hU 5 (P : GL (Fin 5) K)).map ι) E := by
    rw [← hN]
    exact hE
  have hES := isComponentOf_comap_of_injective ι hι hE'
  have hc2 : c' ^ (2 ^ n + 1) = 1 := (pow_succ_eq_one_iff_norm hU c').mpr hc'
  have hw5 : (c''⁻¹) ^ 5 = 1 := by rw [inv_pow, hc5'', inv_one]
  by_cases hw1 : c''⁻¹ = 1
  ·
    have hjcen : jt ∈ cenSU hU 5 (P : GL (Fin 5) K) := by
      rw [mem_cenSU]
      have h1 := hrel
      rw [hw1, map_one, one_mul] at h1
      calc (jt : GL (Fin 5) K) * (P : GL (Fin 5) K) =
          (jt : GL (Fin 5) K) * ((jt : GL (Fin 5) K)⁻¹ * (P : GL (Fin 5) K) * (jt : GL (Fin 5) K)) := by
            rw [h1]
        _ = (P : GL (Fin 5) K) * (jt : GL (Fin 5) K) := by group
    have hQ : QuasiFactored (cenSU hU 5 (P : GL (Fin 5) K)) := by
      by_cases hsc : ∃ μ : Kˣ, (P : GL (Fin 5) K) = Matrix.GeneralLinearGroup.scalar (Fin 5) μ
      · obtain ⟨μ, hμ⟩ := hsc
        have htop : cenSU hU 5 (P : GL (Fin 5) K) = ⊤ := by
          rw [eq_top_iff]
          intro g _
          rw [mem_cenSU, hμ]
          exact (commute_scalar (ι := Fin 5) μ _).eq
        rw [htop]
        exact quasiFactored_top hSq
      · exact su5_quasiFactored h5 hc2 hP5 (fun μ hμ => hsc ⟨μ, hμ⟩)
    have hmem := hQ.mem_sup_centralizer hES hjcen
    have hEr : E ≤ ι.range := by
      have : E ≤ (cenSU hU 5 (P : GL (Fin 5) K)).map ι := hN ▸ hE.1
      exact this.trans (Subgroup.map_le_range ι _)
    have hmapE : (E.comap ι).map ι = E := Subgroup.map_comap_eq_self hEr
    have hmapC : (Subgroup.centralizer ((E.comap ι : Subgroup (gamma5 hU)) :
        Set (gamma5 hU))).map ι ≤ Subgroup.centralizer (E : Set H) := by
      rintro _ ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : x ∈ (E.comap ι).map ι := by rw [hmapE]; exact hx
      obtain ⟨e', he, rfl⟩ := hx'
      have := Subgroup.mem_centralizer_iff.mp hg e' he
      show ι e' * ι g = ι g * ι e'
      rw [← map_mul, ← map_mul, this]
    have hjin : j ∈ E ⊔ Subgroup.centralizer (E : Set H) := by
      have h1 : ι jt ∈ (E.comap ι ⊔ Subgroup.centralizer ((E.comap ι : Subgroup (gamma5 hU)) :
          Set (gamma5 hU))).map ι := ⟨jt, hmem, rfl⟩
      rw [Subgroup.map_sup, hmapE] at h1
      have h2 : ι jt ∈ E ⊔ Subgroup.centralizer (E : Set H) := sup_le_sup_left hmapC E h1
      have h3 : ι jt = j := hψjt
      rw [h3] at h2
      exact h2
    have hEJ : (E : Set H) ⊆ (J : Set H) := fun x hx => (hE.1 hx).1
    have hzE : z ∈ Subgroup.centralizer (E : Set H) := Subgroup.centralizer_le hEJ hzC
    apply hfl.2.1
    rw [hu_eq]
    exact Subgroup.mul_mem _ hjin (Subgroup.mem_sup_right hzE)
  ·
    exfalso
    have hshift : ((jt⁻¹ : gamma5 hU) : GL (Fin 5) K) * (P : GL (Fin 5) K) *
        ((jt⁻¹ : gamma5 hU) : GL (Fin 5) K)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 5) c''⁻¹ * (P : GL (Fin 5) K) := by
      simp only [Subgroup.coe_inv, inv_inv]
      exact hrel
    have hcommS := su5_comm_of_shift (h := hU) (P := P) h5 hc2 hP5 (g := jt⁻¹) (w := c''⁻¹) hw5
      hw1 hshift
    exact not_commutative_of_isQuasisimple hES.2.1 fun a ha b hb =>
      hcommS a b (hES.1 ha) (hES.1 hb)

end CFSG.RankThree.PartOne.FOC
