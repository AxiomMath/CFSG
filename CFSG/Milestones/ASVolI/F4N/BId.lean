module

public import CFSG.Milestones.ASVolI.F4Small
public import CFSG.Milestones.ASVolI.F4Native
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem burnsideF4nB_map_conj_inv {G : Type*} [Group G] (h : G) (H : Subgroup G) :
    (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have e : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [e, Subgroup.map_id]

set_option linter.unusedSectionVars false


theorem burnsideF4nB_smallImage_eq {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {E : Type} [Group E] (marking : G2Native.SmallModel K ≃* ↥(⊤ : Subgroup E))
    (L : Subgroup (G2Native.Parent K)) :
    (G2Native.smallImage K marking L).map (⊤ : Subgroup E).subtype =
      (L.comap (g2HomC (two_eq_zero_of_card_two hK))).map
        ((burnsideF4h_g2_psi K hK).trans (marking.trans Subgroup.topEquiv)).toMonoidHom := by
  have h2 := two_eq_zero_of_card_two hK
  have hk2 := eq_zero_or_eq_one_of_card_two hK
  set ι := burnsideF4h_g2_iota h2 hk2 with hι
  have hιs : Function.Surjective ι := burnsideF4h_g2_iota_surjective h2 hk2
  have hcomp : (G2Native.derivedInclusion K).comp ι = g2HomC h2 := by
    ext x; rfl
  have hder : G2Native.derivedLocal K L = (L.comap (g2HomC h2)).map ι := by
    have h1 : (L.comap (G2Native.derivedInclusion K)).comap ι = L.comap (g2HomC h2) := by
      rw [Subgroup.comap_comap, hcomp]
    rw [← h1, Subgroup.map_comap_eq_self_of_surjective hιs]
    rfl
  unfold G2Native.smallImage G2Native.smallLocal
  rw [hder, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem burnsideF4nB_ident {p f : ℕ} {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 GLKind.G2d p f ⊤ M₁ M₂) :
    ∃ Φ : U33G ≃* E, u33Data.T.map Φ.toMonoidHom = M₁ ⊓ M₂ ∧
      u33Data.B.map Φ.toMonoidHom = M₁ ∧ u33Data.A.map Φ.toMonoidHom = M₂ := by
  obtain ⟨hp2, -, -⟩ := hyp.model
  subst hp2
  obtain ⟨chart, hBm, hPm, hLm⟩ := hyp.lie_amalgam
  rcases chart.coordinates with ⟨c, hk, -⟩ | ⟨hk, -⟩ |
      ⟨-, -, -, K, fK, finK, hcard, marking, h1, h2', h3, -, -⟩ | ⟨hk, -⟩ |
      ⟨-, e, K', fK', finK', charK', scope, hcase⟩
  · cases c <;> exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · haveI := finK
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime (p := 2)
      (by rw [← Nat.card_eq_fintype_card, hcard])
    have h2eq : (2 : K) = 0 := two_eq_zero_of_card_two hcard
    have hk2 := eq_zero_or_eq_one_of_card_two hcard
    haveI := burnsideF4h_g2_finite_u33
    set Ψ : U33G ≃* E := (burnsideF4h_g2_psi K hcard).trans (marking.trans Subgroup.topEquiv)
      with hΨ
    set S' := (G2Native.positiveBorel K).comap (g2HomC h2eq) with hS'
    set P' := (G2Native.pointParabolic K).comap (g2HomC h2eq) with hP'
    set L' := (G2Native.lineParabolic K).comap (g2HomC h2eq) with hL'
    have eB : M₁ ⊓ M₂ = S'.map Ψ.toMonoidHom := by
      rw [← top_inf_eq (M₁ ⊓ M₂), hBm, h1, burnsideF4nB_smallImage_eq hcard]
    have eP : M₁ = P'.map Ψ.toMonoidHom := by
      rw [← top_inf_eq M₁, hPm, h2', burnsideF4nB_smallImage_eq hcard]
    have eL : M₂ = L'.map Ψ.toMonoidHom := by
      rw [← top_inf_eq M₂, hLm, h3, burnsideF4nB_smallImage_eq hcard]
    have hmapinj : Function.Injective (Subgroup.map Ψ.toMonoidHom) :=
      Subgroup.map_injective Ψ.injective
    have hmaptop : (⊤ : Subgroup U33G).map Ψ.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ Ψ.surjective
    obtain ⟨hSp, hS32⟩ := burnsideF4c_Sg_syl hcard h2eq hk2
    have hcard6048 : Nat.card U33G = 6048 := card_u33Pres
    have hSle : Nat.card S' ∣ 6048 := hcard6048 ▸ Subgroup.card_subgroup_dvd_card S'
    obtain ⟨n, hn⟩ := hSp.exists_card_eq
    have hn5 : n = 5 := by
      rw [hn] at hSle hS32
      have h1' : 5 ≤ n := by
        by_contra hc
        have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h2'' : n ≤ 5 := by
        by_contra hc
        have h64 : 2 ^ 6 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
        have := dvd_trans h64 hSle
        omega
      omega
    have hSi : ¬ 2 ∣ S'.index := by
      have h := Subgroup.card_mul_index S'
      rw [hn, hn5, hcard6048] at h
      have : S'.index = 189 := by omega
      rw [this]; norm_num
    obtain ⟨h, hh⟩ := burnsideF4c_sylow_conj S' u33Data.T hSp hSi u33_syl.1 u33_syl.2
    have hT : u33Data.T = S'.map (MulAut.conj h).toMonoidHom := by
      ext g
      rw [hh g]
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
    have hconjinj : Function.Injective (Subgroup.map (MulAut.conj h).toMonoidHom) :=
      Subgroup.map_injective (MulAut.conj h).injective
    have hconjtop : (⊤ : Subgroup U33G).map (MulAut.conj h).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective
    obtain ⟨z, hz1, hz2, hzφ⟩ := burnsideF4c_exists_z (K := K) h2eq hk2
    have hzc := burnsideF4c_Pg_comm hcard h2eq z hzφ
    set P'' := P'.map (MulAut.conj h).toMonoidHom with hP''
    set L'' := L'.map (MulAut.conj h).toMonoidHom with hL''
    have hTP : u33Data.T ≤ P'' := by
      rw [hT]; exact Subgroup.map_mono (burnsideF4c_le_Pg h2eq)
    have hTL : u33Data.T ≤ L'' := by
      rw [hT]; exact Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
    have hPz : ∀ q ∈ P'', q * (h * z * h⁻¹) = (h * z * h⁻¹) * q := by
      rintro _ ⟨q, hq, rfl⟩
      show h * q * h⁻¹ * (h * z * h⁻¹) = h * z * h⁻¹ * (h * q * h⁻¹)
      calc h * q * h⁻¹ * (h * z * h⁻¹) = h * (q * z) * h⁻¹ := by group
        _ = h * (z * q) * h⁻¹ := by rw [hzc q hq]
        _ = h * z * h⁻¹ * (h * q * h⁻¹) := by group
    have hz1' : h * z * h⁻¹ ≠ 1 := by
      intro h1''
      apply hz1
      have : h * z * h⁻¹ = h * 1 * h⁻¹ := by rw [h1'']; group
      simpa using this
    have hz2' : h * z * h⁻¹ * (h * z * h⁻¹) = 1 := by
      calc h * z * h⁻¹ * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    have hPne : P'' ≠ u33Data.T := by
      intro heq
      have hyP : u33GenPG 4 ∈ P' := burnsideF4c_y_mem hcard h2eq
      have hmem : h * u33GenPG 4 * h⁻¹ ∈ u33Data.T := by
        rw [← heq]
        exact ⟨_, hyP, by simp [MulAut.conj_apply]⟩
      obtain ⟨s, hs, hse⟩ := (hh _).1 hmem
      have hsy : s = u33GenPG 4 := by simpa using hse
      exact burnsideF4c_y_not_mem_Sylow S' hSp (hsy ▸ hs)
    have hPtop : P'' ≠ ⊤ := fun heq =>
      burnsideF4c_u33_no_x P'' hTP (heq ▸ Subgroup.mem_top _) _ hz1' hz2' hPz
    have hPB : P'' = u33Data.B := by
      rcases u33Data.lattice P'' hTP with hc | hc | hc | hc
      · exact absurd hc hPne
      · exact absurd (hc ▸ u33Data.x_mem_A) fun hx =>
          burnsideF4c_u33_no_x P'' hTP hx _ hz1' hz2' hPz
      · exact hc
      · exact absurd hc hPtop
    have hgen : M₁ ⊔ M₂ = ⊤ := hyp.gen
    have hP'top : P' ≠ ⊤ := by
      intro heq
      apply hPtop
      rw [hP'', heq, hconjtop]
    have hLA : L'' = u33Data.A := by
      rcases u33Data.lattice L'' hTL with hc | hc | hc | hc
      · exfalso
        have hLS : L' = S' := by
          apply hconjinj
          rw [← hL'', hc, hT]
        have hM : M₂ ≤ M₁ := by
          rw [eL, hLS, ← eB]; exact inf_le_left
        apply hP'top
        apply hmapinj
        rw [← eP, hmaptop, ← hgen, sup_eq_left.2 hM]
      · exact hc
      · exfalso
        have hLP : L' = P' := by
          apply hconjinj
          rw [← hL'', ← hP'', hc, hPB]
        apply hP'top
        apply hmapinj
        rw [← eP, hmaptop, ← hgen, eL, hLP, ← eP, sup_idem]
      · exfalso
        have hLt : L' = ⊤ := by
          apply hconjinj
          rw [← hL'', hc, hconjtop]
        have hM2 : M₂ = ⊤ := by rw [eL, hLt, hmaptop]
        have hSP : S' = P' := by
          apply hmapinj
          rw [← eB, ← eP, hM2, inf_top_eq]
        apply u33Data.T_ne_B
        rw [← hPB, hT, hP'', hSP]
    refine ⟨(MulAut.conj h⁻¹).trans Ψ, ?_, ?_, ?_⟩
    · have e1 : ((MulAut.conj h⁻¹).trans Ψ).toMonoidHom =
          Ψ.toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom := by
        ext x; rfl
      rw [e1, ← Subgroup.map_map, hT, burnsideF4nB_map_conj_inv, eB]
    · have e1 : ((MulAut.conj h⁻¹).trans Ψ).toMonoidHom =
          Ψ.toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom := by
        ext x; rfl
      rw [e1, ← Subgroup.map_map, ← hPB, hP'', burnsideF4nB_map_conj_inv, eP]
    · have e1 : ((MulAut.conj h⁻¹).trans Ψ).toMonoidHom =
          Ψ.toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom := by
        ext x; rfl
      rw [e1, ← Subgroup.map_map, ← hLA, hL'', burnsideF4nB_map_conj_inv, eL]
  · exact absurd hk (by decide)
  · rcases hcase with ⟨hk, -⟩ | ⟨hk, -⟩ <;> exact absurd hk (by decide)

end CFSG.ASVolI
