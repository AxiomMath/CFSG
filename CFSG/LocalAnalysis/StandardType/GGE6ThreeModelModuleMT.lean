module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModuleM
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTSpec
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLiftT
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTorusIdx
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLangTorus

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

private lemma mem_coTorus_of_mem_thetaTorus {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω}
    (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) {t : ModGL Tag.E6 Ω}
    (htθ : t ∈ TwistedDiag.thetaTorus Ω (2 ^ n))
    (htQ : g * t * g⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω) :
    t ∈ coTorus Ω (2 ^ n + 1) := by
  by_contra hnot
  refine langTorus_not_le_cgrp hn hK σ hσ Fr hFr h3 hL hζ hζo hD ?_
  have hle : TwistedDiag.thetaTorus Ω (2 ^ n) ≤
      (TwistedDiag.Cgrp K σ.toRingHom Ω).comap (MulAut.conj g).toMonoidHom := by
    refine le_trans (thetaTorus_le_sup_of_not_mem (2 ^ n) htθ hnot) (sup_le ?_ ?_)
    · refine (Subgroup.closure_le _).2 ?_
      rintro y ⟨i, s, hs, rfl⟩
      show (MulAut.conj g) (torusElt Tag.E6 Ω i s) ∈ TwistedDiag.Cgrp K σ.toRingHom Ω
      rw [MulAut.conj_apply]
      exact torusElt_mem_Cgrp hn hK σ hσ Fr hFr h3 hL hζ hD i s hs
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using htQ
  intro x hx
  have hx' := hle hx
  rw [Subgroup.mem_comap] at hx'
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx'

private lemma map_conj_coTorus_le_iSup {n : ℕ} {Ω : Type} [Field Ω] {R : Type} [Group R]
    (g : ModGL Tag.E6 Ω) (Ψ : R →* ModGL Tag.E6 Ω)
    (d : Fin Tag.E6.rank → rootsOfUnity (2 ^ n + 1) Ω →* R)
    (hΨd : ∀ (j : Fin Tag.E6.rank) (s : rootsOfUnity (2 ^ n + 1) Ω),
      Ψ (d j s) = g * torusElt Tag.E6 Ω j (s : Ωˣ) * g⁻¹) :
    (coTorus Ω (2 ^ n + 1)).map (MulAut.conj g).toMonoidHom ≤
      (⨆ j, (d j).range).map Ψ := by
  dsimp only [coTorus]
  rw [MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨y, ⟨i, s, hs, rfl⟩, rfl⟩
  refine Subgroup.mem_map.mpr ⟨d i ⟨s, hs⟩, Subgroup.mem_iSup_of_mem i ⟨⟨s, hs⟩, rfl⟩, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact hΨd i ⟨s, hs⟩

theorem tFrame_cartanGen (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : Nonempty (CartanGen D (rootsOfUnity (2 ^ n + 1) Ω)) := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let Ψ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* ModGL Tag.E6 Ω :=
    (baseChangeGL (algebraMap K Ω) (τ := Tag.E6)).comp
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    have hab' : baseChangeGL (algebraMap K Ω) (a : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap K Ω) (b : ModGL TwistTag.E6.tag K) := hab
    exact Subtype.ext (baseChangeGL_injective (τ := Tag.E6) (R := K) (S := Ω)
      (algebraMap K Ω) hab')
  let f : Fin Tag.E6.rank → rootsOfUnity (2 ^ n + 1) Ω →* ModGL Tag.E6 Ω := fun j => {
    toFun := fun s => g * torusElt Tag.E6 Ω j (s : Ωˣ) * g⁻¹
    map_one' := by
      rw [Subgroup.coe_one, torusElt_one (τ := Tag.E6) (R := Ω) j]
      group
    map_mul' := fun s t => by
      rw [Subgroup.coe_mul, torusElt_mul (τ := Tag.E6) (R := Ω) j]
      group }
  let d : Fin Tag.E6.rank → rootsOfUnity (2 ^ n + 1) Ω →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := fun j =>
    ((MonoidHom.ofInjective hΨinj).symm : Ψ.range →* _).comp
      ((f j).codRestrict Ψ.range (fun s => by
        obtain ⟨r, hr, hrfl⟩ := Subgroup.mem_map.1
          (torusElt_mem_Cgrp hn hK σ hσ Fr hFr h3 hL hζ hD j (s : Ωˣ)
            ((mem_rootsOfUnity (2 ^ n + 1) (s : Ωˣ)).1 s.2))
        exact MonoidHom.mem_range.mpr ⟨⟨r, hr⟩, hrfl⟩))
  have hΨd : ∀ (j : Fin Tag.E6.rank) (s : rootsOfUnity (2 ^ n + 1) Ω),
      Ψ (d j s) = g * torusElt Tag.E6 Ω j (s : Ωˣ) * g⁻¹ := by
    intro j s
    dsimp only [d]
    exact congrArg Subtype.val
      (MulEquiv.apply_symm_apply (MonoidHom.ofInjective hΨinj) _)
  have hcomm : ∀ (j k : Fin Tag.E6.rank) (s t : rootsOfUnity (2 ^ n + 1) Ω),
      d j s * d k t = d k t * d j s := by
    intro j k s t
    apply hΨinj
    simp only [map_mul, hΨd]
    have hmc := torusElt_mul_comm (τ := Tag.E6) (R := Ω) j k (s : Ωˣ) (t : Ωˣ)
    calc (g * torusElt Tag.E6 Ω j (s : Ωˣ) * g⁻¹) *
          (g * torusElt Tag.E6 Ω k (t : Ωˣ) * g⁻¹)
        = g * (torusElt Tag.E6 Ω j (s : Ωˣ) * torusElt Tag.E6 Ω k (t : Ωˣ)) * g⁻¹ := by
          group
      _ = g * (torusElt Tag.E6 Ω k (t : Ωˣ) * torusElt Tag.E6 Ω j (s : Ωˣ)) * g⁻¹ := by
          rw [hmc]
      _ = (g * torusElt Tag.E6 Ω k (t : Ωˣ) * g⁻¹) *
          (g * torusElt Tag.E6 Ω j (s : Ωˣ) * g⁻¹) := by group
  have hconj : ∀ (i j : Fin Tag.E6.rank) (s : rootsOfUnity (2 ^ n + 1) Ω),
      D.nb i * d j s * (D.nb i)⁻¹ = d j s * d i (s ^ (-(Tag.E6.cartan j i))) := by
    intro i j s
    apply hΨinj
    simp only [map_mul, map_inv, hΨd]
    have hnb : Ψ (D.nb i) = g * weylElt Tag.E6 Ω i 1 * g⁻¹ := hD.nb_eq i
    rw [hnb]
    have hcoe : ((s ^ (-(Tag.E6.cartan j i)) : rootsOfUnity (2 ^ n + 1) Ω) : Ωˣ) =
        (s : Ωˣ) ^ (-(Tag.E6.cartan j i)) :=
      MonoidHom.map_zpow (rootsOfUnity (2 ^ n + 1) Ω).subtype s _
    rw [hcoe]
    have hweyl := weylElt_one_mul_torusElt_mul_inv (τ := Tag.E6) (R := Ω) i j (s : Ωˣ)
    calc (g * weylElt Tag.E6 Ω i 1 * g⁻¹) * (g * torusElt Tag.E6 Ω j (s : Ωˣ) * g⁻¹) *
          (g * weylElt Tag.E6 Ω i 1 * g⁻¹)⁻¹
        = g * (weylElt Tag.E6 Ω i 1 * torusElt Tag.E6 Ω j (s : Ωˣ) *
            (weylElt Tag.E6 Ω i 1)⁻¹) * g⁻¹ := by group
      _ = g * (torusElt Tag.E6 Ω j (s : Ωˣ) *
            torusElt Tag.E6 Ω i ((s : Ωˣ) ^ (-(Tag.E6.cartan j i)))) * g⁻¹ := by rw [hweyl]
      _ = (g * torusElt Tag.E6 Ω j (s : Ωˣ) * g⁻¹) *
          (g * torusElt Tag.E6 Ω i ((s : Ωˣ) ^ (-(Tag.E6.cartan j i))) * g⁻¹) := by group
  have htor : D.Tor = ⨆ j, (d j).range := by
    apply le_antisymm
    · intro c hc
      obtain ⟨t, ht_torus, ht_eq⟩ := Subgroup.mem_map.1 ((hD.tor_eq c).1 hc)
      have htconj : g * t * g⁻¹ = Ψ c := by
        have h : MulAut.conj g t = Ψ c := ht_eq
        simpa only [MulAut.conj_apply] using h
      have hmemCg : Ψ c ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
        show baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) ∈
          TwistedDiag.Cgrp K σ.toRingHom Ω
        exact Subgroup.mem_map.mpr ⟨(c : ModGL TwistTag.E6.tag K), c.2, rfl⟩
      obtain ⟨-, hCR, -, -, -⟩ :=
        TwistedDiag.cgrp_facts hn K hK σ.toRingHom hσ h3 Ω Fr hFr
      have hmemRg : g * t * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
        rw [htconj]; exact hCR hmemCg
      have htθ : t ∈ TwistedDiag.thetaFixed Fr :=
        (TwistedDiag.mem_thetaFixed_iff_conj Fr hL.1 hL.2 t).2 hmemRg
      have htt : t ∈ TwistedDiag.thetaTorus Ω (2 ^ n) := by
        rw [← TwistedDiag.torus_inf_thetaFixed Fr hFr]
        exact ⟨ht_torus, htθ⟩
      have htco : t ∈ coTorus Ω (2 ^ n + 1) :=
        mem_coTorus_of_mem_thetaTorus hn hK σ hσ Fr hFr h3 hL hζ hζo hD htt
          (by rw [htconj]; exact hmemCg)
      have hsub := map_conj_coTorus_le_iSup (n := n) g Ψ d hΨd
      have hΨc : Ψ c ∈ (⨆ j, (d j).range).map Ψ := by
        rw [← htconj]
        exact hsub (Subgroup.mem_map.mpr ⟨t, htco, by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩)
      exact (Subgroup.mem_map_iff_mem hΨinj).1 hΨc
    · refine iSup_le fun j => ?_
      rintro x ⟨s, rfl⟩
      refine (hD.tor_eq (d j s)).2 ?_
      show Ψ (d j s) ∈ (torusGroup Tag.E6 Ω).map (MulAut.conj g).toMonoidHom
      rw [hΨd]
      refine Subgroup.mem_map.mpr ⟨torusElt Tag.E6 Ω j (s : Ωˣ),
        torusElt_mem_torusGroup (τ := Tag.E6) (R := Ω) j (s : Ωˣ), ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact ⟨{ d := d, tor_eq := htor, comm := hcomm, conj := hconj }⟩

theorem tFrame_modules (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : D.ModuleOK := by
  obtain ⟨G⟩ := tFrame_cartanGen hn hK σ hσ Fr hFr h3 hL hζ hζo hD
  exact moduleOK_of_cartanGen D (tFrame_center hn hK σ hσ) (tFrame_faithful hn hK σ hσ Fr hFr h3 hL hζ hζo hD)
    (tFrame_weyl hn hK σ hσ Fr hFr h3 hL hζ hζo hD) G

end CFSG.StandardType.E6ThreeModel
