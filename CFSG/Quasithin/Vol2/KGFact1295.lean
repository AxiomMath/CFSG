module

public import CFSG.Quasithin.Vol2.KGFact1295Cls
public import CFSG.Quasithin.Vol2.KGFact1295Red
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Par
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Red
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Red

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open KG1296 KG1297 KG1295 in
theorem parabolicFact1295_holds : ParabolicFact1295 := by
  intro G _ _ X K S B hKX hXN hS hKS ⟨e⟩ hBK hSB hBO ⟨eB⟩ hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSX : S ≤ X := hS.1
  have hS2 : IsPGroup 2 S := hS.2.1
  have hBX : B ≤ X := hBK.trans hKX
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set φ : ↥X →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) := (actBar K).comp (Subgroup.inclusion hXN)
    with hφ
  have hφmem : ∀ (x : ↥X) {H : Subgroup G}, (∀ h ∈ H, (x : G) * h * (x : G)⁻¹ ∈ H) →
      ∀ z ∈ (H.subgroupOf K).map π, φ x z ∈ (H.subgroupOf K).map π := by
    rintro x H hH _ ⟨⟨h, hK⟩, hh, rfl⟩
    exact ⟨⟨(x : G) * h * (x : G)⁻¹, (hXN x.2 h).1 hK⟩, hH h hh, rfl⟩
  have hmapeq : ∀ (α : MulAut (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
      (H : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))),
      (∀ x ∈ H, α x ∈ H) → H.map α.toMonoidHom = H := fun α H h =>
    Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)
      (by rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective])
  obtain ⟨T, hT⟩ := exists_sylow_image hKX hXN hS
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 5) (by norm_num)
  have hesurj : Function.Surjective
      (e.toMonoidHom : _ → Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := e.surjective
  obtain ⟨g, -, hg⟩ := exists_conj_sylow (P := ⊤) (T.mapSurjective hesurj) U₀ le_top le_top
  set ι := e.trans (MulAut.conj g) with hι
  have hιT : (T : Subgroup _).map ι.toMonoidHom = unitriangular 5 (ZMod 2) := by
    rw [← hU₀, ← hg, Sylow.coe_mapSurjective, Subgroup.map_map]
    rfl
  set Bb := barOf K B with hBb
  set B₁ := Bb.map ι.toMonoidHom with hB₁
  have hTB : (T : Subgroup _) ≤ Subgroup.normalizer (Bb : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    rw [hT]
    refine le_normalizer_of_forall ?_
    rintro _ ⟨s, hs, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨s * b * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hSB hs) b).1 hb, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hUB : unitriangular 5 (ZMod 2) ≤
      Subgroup.normalizer (B₁ : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) := by
    rw [← hιT]
    exact map_le_normalizer_map ι hTB
  have hBKO : oTwoUpper (B.subgroupOf K) = B.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [← oTwoUpper_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hBK, hBO]
  have hB₁O : oTwoUpper B₁ = B₁ := by
    rw [hB₁, hBb, barOf, oTwoUpper_map, oTwoUpper_map, hBKO]
  have hB₁mod : Nonempty (ModO2 B₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    obtain ⟨e1⟩ := nonempty_modO2_barOf (K := K) hBK
    obtain ⟨e2⟩ := nonempty_modO2_map ι Bb
    exact ⟨(e2.symm.trans e1.symm).trans eB⟩
  obtain ⟨J, hJU, hB₁J, hJ⟩ := classify hUB hB₁O hB₁mod
  have hJ' : J = {3, 4} ∨ J = {1, 2} := by
    rcases hJ with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      refine hnot ⟨ι, ?_⟩
      show B₁ = _
      rw [hB₁J, h, ← Ct_eq, oTwoUpper_Ct]
  have hinn : ∀ s : ↥X, (s : G) ∈ S → ∃ z, φ s = MulAut.conj z := by
    intro s hs
    set α := MulAut.congr ι (φ s) with hα
    have hαapp : ∀ y, α y = ι (φ s (ι.symm y)) := fun y => rfl
    have hαU : (unitriangular 5 (ZMod 2)).map α.toMonoidHom = unitriangular 5 (ZMod 2) := by
      refine hmapeq α _ fun y hy => ?_
      rw [← hιT] at hy ⊢
      obtain ⟨t, ht, rfl⟩ := hy
      refine ⟨φ s t, ?_, ?_⟩
      · rw [hT] at ht ⊢
        exact hφmem s (H := S) (fun h hh => S.mul_mem (S.mul_mem hs hh) (S.inv_mem hs)) t ht
      · rw [hαapp]
        simp
    have hαB : B₁.map α.toMonoidHom = B₁ := by
      refine hmapeq α _ fun y hy => ?_
      obtain ⟨z, hz, rfl⟩ := hy
      refine ⟨φ s z, hφmem s (H := B)
        (fun h hh => (Subgroup.mem_normalizer_iff.1 (hSB hs) h).1 hh) z hz, ?_⟩
      rw [hαapp]
      simp
    obtain ⟨h, hh⟩ := exists_conj_of_normalizes hJU hJ' α hαU hαB
    refine ⟨ι.symm h, MulEquiv.ext fun z => ?_⟩
    have := congrArg (fun f : MulAut (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) =>
      ι.symm (f (ι z))) hh
    simp only [hαapp, MulEquiv.symm_apply_apply, MulAut.conj_apply, map_mul, map_inv] at this
    rw [MulAut.conj_apply]
    exact this
  have hs5 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (K := ZMod 2)
      (Nat.card_zmod 2) (m := 5) (by norm_num)
  have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := e.isSimpleGroup
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_mulEquiv e CFSG.Quasithin.SLnTwo.center_eq_bot
  obtain ⟨ψ, hψK, hψker, -⟩ := exists_psi_of_inner hKX hXN hKS hinn hZ
  set D := centralizerMod (pCoreOf 2 K) X K with hDdef
  have hnab : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥K ⧸ CFSG.pCore 2 ↥K)
    have hxZ : x ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) :=
      Subgroup.mem_center_iff.2 fun y => hcon y x
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact hx hxZ
  have hD2 : IsPGroup 2 D := by
    have := L1296.isPGroup_centralizerMod hS2 (hSX.trans hXN) hs hnab
    rwa [hKS] at this
  have hDX : D ≤ X := fun x hx => hx.1
  have hDS : D ≤ S := by
    have hDn : (D.subgroupOf X).Normal := by
      have : D.subgroupOf X = ψ.ker := by
        ext x
        rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hψker]
      rw [this]
      infer_instance
    let S₀ : Sylow 2 ↥X := hS2.comap_subtype.toSylow hS.2.2
    have : (Subgroup.comap X.subtype D).Normal := hDn
    have h := IsPGroup.le_sylow_of_normal hD2.comap_subtype S₀
    intro d hd
    exact h (show (⟨d, hDX hd⟩ : ↥X) ∈ D.subgroupOf X from hd)
  set ρ : ↥X →* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) := ι.toMonoidHom.comp ψ with hρ
  have hρ1 : ∀ x : ↥X, ρ x = 1 ↔ ψ x = 1 := fun x => by
    rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hkerS : ∀ x : ↥X, ρ x = 1 → (x : G) ∈ S := fun x hx =>
    hDS ((hψker x).1 ((hρ1 x).1 hx))
  have hker2 : IsPGroup 2 ρ.ker := by
    intro x
    obtain ⟨k, hk⟩ := hD2 ⟨_, (hψker x).1 ((hρ1 x).1 x.2)⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
    exact ⟨⟨k, hKX k.2⟩, hψK k k.2⟩
  have hρs : Function.Surjective ρ := ι.surjective.comp hψs
  have hρS : (S.subgroupOf X).map ρ = unitriangular 5 (ZMod 2) := by
    have hle : unitriangular 5 (ZMod 2) ≤ (S.subgroupOf X).map ρ := by
      rw [← hιT, hT]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨⟨k, hKX k.2⟩, hk, ?_⟩
      rw [hρ, MonoidHom.comp_apply, hψK k k.2]
    have h2 : IsPGroup 2 ((S.subgroupOf X).map ρ) := hS2.comap_subtype.map ρ
    rw [← hU₀] at hle ⊢
    exact U₀.is_maximal' h2 hle
  have hρB : (B.subgroupOf X).map ρ = B₁ := by
    have hψB : (B.subgroupOf X).map ψ = Bb := by
      ext z
      constructor
      · rintro ⟨⟨b, hbX⟩, hb, rfl⟩
        exact ⟨⟨b, hBK hb⟩, hb, (hψK b (hBK hb)).symm⟩
      · rintro ⟨⟨b, hbK⟩, hb, rfl⟩
        exact ⟨⟨b, hKX hbK⟩, hb, hψK b hbK⟩
    rw [hρ, ← Subgroup.map_map, hψB]
  rcases hJ' with rfl | rfl
  · have h := parOut_34
    rw [← hB₁J, ← hρB, ← hρS] at h
    exact exists_of_parOut ρ hρs hker2 hkerS hSX hBX hSB hBO h
  · have h := parOut_12
    rw [← hB₁J, ← hρB, ← hρS] at h
    exact exists_of_parOut ρ hρs hker2 hkerS hSX hBX hSB hBO h

end CFSG.Quasithin.H13
