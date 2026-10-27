module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso
public import CFSG.LieType.Steinberg.CentralExt.TrialityClosed

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover CFSG.Open

private theorem rckTri_orderOf_eq_two {G : Type*} [Group G] {x : G} (hx1 : x ≠ 1)
    (hx2 : x * x = 1) : orderOf x = 2 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

theorem rckRowIIAtTri_of_modelPair
    (F : Type) [Field F] [Finite F] (σ : F →+* F) (hF : TriField F σ 1)
    (hPair : ∃ (β : Fin (triD4Universal F σ).D.rank → ℤ) (x : (triD4Universal F σ).K)
        (V : Subgroup (triD4Universal F σ).K),
      β ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β ∧
      (triD4Universal F σ).D.rootGroup β = Subgroup.zpowers x ∧ x * x = 1 ∧ x ≠ 1 ∧
      RCKK1Data x V) :
    RCKRowIIAtTri F σ := by
  intro Jb _ _ _ φ hφsurj hφker
  have hcenterU : Subgroup.center (triD4Universal F σ).K = ⊥ := by
    change Subgroup.center (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ) = ⊥
    exact CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
      (q := 2) (by norm_num) (by rw [hF.2.1]; norm_num) (fun c => by simpa using hF.2.2 c)
  have hφker_bot : φ.ker = ⊥ := le_bot_iff.mp (hφker.trans (le_of_eq hcenterU))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hφker_bot
  let e : (triD4Universal F σ).K ≃* Jb := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hcenterJb : Subgroup.center Jb = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_center_iff] at hy
    obtain ⟨u, rfl⟩ := hφsurj y
    have hu : u ∈ Subgroup.center (triD4Universal F σ).K := by
      rw [Subgroup.mem_center_iff]
      intro v
      apply hφinj
      rw [map_mul, map_mul]
      exact hy (φ v)
    rw [hcenterU, Subgroup.mem_bot] at hu
    rw [hu, map_one]
  let mkq : Jb →* Jb ⧸ Subgroup.center Jb := QuotientGroup.mk' (Subgroup.center Jb)
  have hmkqker : mkq.ker = Subgroup.center Jb := QuotientGroup.ker_mk' _
  have hmkqinj : Function.Injective mkq := by
    rw [← MonoidHom.ker_eq_bot_iff, hmkqker, hcenterJb]
  let miso : Jb ≃* Jb ⧸ Subgroup.center Jb :=
    MulEquiv.ofBijective mkq ⟨hmkqinj, QuotientGroup.mk'_surjective _⟩
  obtain ⟨β, x, V, hβ, hlong, hroot, hx2, hx1, hData⟩ := hPair
  have hxroot : x ∈ (triD4Universal F σ).D.rootGroup β := by
    rw [hroot]; exact Subgroup.mem_zpowers x
  have hxord : orderOf x = 2 := rckTri_orderOf_eq_two hx1 hx2
  have hDataQ : RCKK1Data (miso (e x)) ((V.map e.toMonoidHom).map miso.toMonoidHom) :=
    CFSG.StandardType.RCKK1IIp.rckK1Data_map miso
      (CFSG.StandardType.RCKK1IIp.rckK1Data_map e hData)
  refine ⟨miso (e x), (V.map e.toMonoidHom).map miso.toMonoidHom, hDataQ, ?_⟩
  let R : Subgroup Jb := ggRootSub (triD4Universal F σ).D e.toMonoidHom β 1
  let Rm : Subgroup Jb := ggRootSub (triD4Universal F σ).D e.toMonoidHom (-β) 1
  have hRmap : R = ((triD4Universal F σ).D.rootGroup β).map e.toMonoidHom := by
    have h1 : (MulAut.conj (1 : (triD4Universal F σ).K)).toMonoidHom =
        MonoidHom.id (triD4Universal F σ).K := by
      ext y
      simp [MulAut.conj_apply]
    show ggRootSub (triD4Universal F σ).D e.toMonoidHom β 1 = _
    rw [ggRootSub, h1, Subgroup.map_id]
  have hcardR : Nat.card R = 2 := by
    rw [hRmap]
    calc Nat.card (Subgroup.map e.toMonoidHom ((triD4Universal F σ).D.rootGroup β))
        = Nat.card ((triD4Universal F σ).D.rootGroup β) :=
          Subgroup.card_map_of_injective e.injective
      _ = Nat.card (Subgroup.zpowers x) := by rw [hroot]
      _ = 2 := by rw [Nat.card_zpowers, hxord]
  have hpos : GGRootPosJ (⊤ : Subgroup Jb) R Rm := by
    refine Or.inr ⟨F, inferInstance, inferInstance, σ, 1, β, hF, hlong, ?_⟩
    refine ⟨e.toMonoidHom, ?_, ?_, 1, rfl, rfl⟩
    · exact MonoidHom.range_eq_top.mpr e.surjective
    · intro z hz
      rw [MonoidHom.mem_ker] at hz
      have hz1 : z = 1 := e.injective (by
        change e.toMonoidHom z = e.toMonoidHom 1
        rw [hz, map_one])
      rw [hz1]
      exact Subgroup.one_mem _
  refine ⟨R, Rm, hpos, hcardR, ?_⟩
  refine Subgroup.mem_map.mpr ⟨e x, ?_, rfl⟩
  rw [hRmap]
  exact Subgroup.mem_map.mpr ⟨x, hxroot, rfl⟩

end CFSG.StandardType.RCKK1II
