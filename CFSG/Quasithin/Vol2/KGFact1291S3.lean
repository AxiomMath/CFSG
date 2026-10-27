module

public import CFSG.Quasithin.Vol2.KGFact1291S3SL
public import CFSG.Quasithin.Vol2.KGFact1291S3A7
public import CFSG.Quasithin.Vol2.KGFact1295Cls
public import CFSG.Quasithin.Vol2.KGFact1295Ct
public import CFSG.Quasithin.Vol2.KGFact1296

public section

namespace CFSG.Quasithin.H13

namespace KG1291S

open CFSG.Open CFSG.Quasithin.H13.KG1296 CFSG.Quasithin.H13.KG1297 CFSG.Quasithin.H13.KG1295
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section OTwo

variable {M : Type} [Group M]

theorem oTwoUpper_oTwoUpper (B : Subgroup M) : oTwoUpper (oTwoUpper B) = oTwoUpper B := by
  refine le_antisymm (oTwoUpper_le _) ?_
  rw [oTwoUpper, Subgroup.closure_le]
  intro x hx
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

theorem nonempty_modO2_oTwoUpper [Finite M] {B : Subgroup M} {Q : Type} [Group Q]
    (e : ModO2 B ≃* Q) (hQ : IsSimpleGroup Q) (h2 : ¬ IsPGroup 2 Q) :
    Nonempty (ModO2 (oTwoUpper B) ≃* Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥B) with hπ
  set f : ↥(oTwoUpper B) →* ModO2 B := π.comp (Subgroup.inclusion (oTwoUpper_le B)) with hf
  have hO : ((oTwoUpper B).subgroupOf B).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_oTwoUpper (Subgroup.le_normalizer g.2) hn
  have hrange : f.range = ((oTwoUpper B).subgroupOf B).map π := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion (oTwoUpper_le B) x, x.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hnorm : f.range.Normal := by
    rw [hrange]
    exact hO.map π (QuotientGroup.mk'_surjective _)
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    have hN : (f.range.map e.toMonoidHom).Normal := hnorm.map _ e.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.range.map e.toMonoidHom) with h | h
    · exfalso
      apply h2
      intro q
      obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥B) (e.symm q)
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper B b.2
      refine ⟨k, ?_⟩
      have hmem : π (b ^ 2 ^ k) ∈ f.range := by
        refine ⟨⟨(b : M) ^ 2 ^ k, hk⟩, ?_⟩
        rw [hf, MonoidHom.comp_apply]
        congr 1
      have h1 : e (π (b ^ 2 ^ k)) = 1 := by
        have : e (π (b ^ 2 ^ k)) ∈ f.range.map e.toMonoidHom := ⟨_, hmem, rfl⟩
        rwa [h, Subgroup.mem_bot] at this
      have hq : e (π b) = q := by
        rw [hπ, hb]
        exact e.apply_symm_apply q
      rw [← hq, ← map_pow, ← map_pow]
      exact h1
    · rw [eq_top_iff]
      intro q _
      have hq : e q ∈ f.range.map e.toMonoidHom := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨q', hq', hqq⟩ := hq
      rw [← e.injective hqq]
      exact hq'
  have hker : IsPGroup 2 f.ker := by
    intro x
    have hx : f x = 1 := x.2
    have hmem : Subgroup.inclusion (oTwoUpper_le B) (x : ↥(oTwoUpper B)) ∈ CFSG.pCore 2 ↥B := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)) ⟨_, hmem⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥B) => ((z : ↥B) : M)) hk
    simpa using this
  set f' : ↥(oTwoUpper B) →* ↥(⊤ : Subgroup (ModO2 B)) :=
    Subgroup.topEquiv.symm.toMonoidHom.comp f with hf'
  have hf's : Function.Surjective f' := Subgroup.topEquiv.symm.surjective.comp hsurj
  have hker' : IsPGroup 2 f'.ker := by
    have : f'.ker = f.ker := by
      ext x
      simp [hf']
    rw [this]
    exact hker
  obtain ⟨e1⟩ := nonempty_modO2_equiv f' hf's hker'
  have hbot : CFSG.pCore 2 ↥(⊤ : Subgroup (ModO2 B)) = ⊥ := by
    set N := CFSG.pCore 2 ↥(⊤ : Subgroup (ModO2 B))
    have hN : (N.map ((Subgroup.topEquiv.trans e).toMonoidHom)).Normal :=
      CFSG.pCore_normal.map _ (Subgroup.topEquiv.trans e).surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map ((Subgroup.topEquiv.trans e).toMonoidHom)) with h | h
    · exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.topEquiv.trans e).injective).1 h
    · exfalso
      apply h2
      have h2N : IsPGroup 2 (N.map ((Subgroup.topEquiv.trans e).toMonoidHom)) :=
        CFSG.pCore_isPGroup.map _
      rw [h] at h2N
      exact h2N.of_equiv Subgroup.topEquiv
  exact ⟨e1.trans (((QuotientGroup.quotientMulEquivOfEq hbot).trans
    QuotientGroup.quotientBot).trans (Subgroup.topEquiv.trans e))⟩

end OTwo

variable {G : Type} [Group G]

theorem inner_five_three [Finite G] {X K S B : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hS : QuasithinUnique.IsSylowTwoOf S X)
    (hBK : B ≤ K) (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hinn : ∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B)
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (eB : ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∀ s : ↥X, (s : G) ∈ S →
      ∃ z, (actBar K).comp (Subgroup.inclusion hXN) s = MulAut.conj z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have hB₁mod : Nonempty (ModO2 B₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    obtain ⟨e1⟩ := nonempty_modO2_barOf (K := K) hBK
    obtain ⟨e2⟩ := nonempty_modO2_map ι Bb
    exact ⟨(e2.symm.trans e1.symm).trans eB⟩
  set B₀ := oTwoUpper B₁ with hB₀
  have hUB₀ : unitriangular 5 (ZMod 2) ≤
      Subgroup.normalizer (B₀ : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) :=
    hUB.trans (normalizer_le_normalizer_oTwoUpper B₁)
  have hB₀O : oTwoUpper B₀ = B₀ := oTwoUpper_oTwoUpper B₁
  have hs3 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  have hn2 : ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    intro h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h
    rw [CFSG.QuasithinUnique.Vol2Native.A312L.Seven.card_slThree] at hk
    have h7 : 7 ∣ 2 ^ k := hk ▸ (by norm_num : 7 ∣ 168)
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
      ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h7)
    omega
  have hB₀mod : Nonempty (ModO2 B₀ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    obtain ⟨e1⟩ := hB₁mod
    exact nonempty_modO2_oTwoUpper e1 hs3 hn2
  obtain ⟨J, hJU, hB₀J, hJ⟩ := classify hUB₀ hB₀O hB₀mod
  rcases hJ with hJ | hJ | hJ
  rotate_left 2
  ·
    have hB₀Ct : B₀ = Ct := by rw [hB₀J, hJ, ← Ct_eq, oTwoUpper_Ct]
    have hB₁Ct : B₁ = Ct := by
      refine le_antisymm (fun x hx => mem_Ct_of_normalizes fun y hy => ?_) ?_
      · rw [← hB₀Ct] at hy ⊢
        exact conj_mem_oTwoUpper (Subgroup.le_normalizer hx) hy
      · rw [← hB₀Ct]
        exact oTwoUpper_le B₁
    have hInn : InnClosed Bb := by
      have h1 := innClosed_map ι.symm (hB₁Ct ▸ innClosed_Ct : InnClosed B₁)
      have hBB : B₁.map ι.symm.toMonoidHom = Bb := by
        rw [hB₁, Subgroup.map_map]
        convert Subgroup.map_id Bb
        ext x
        simp
      rwa [hBB] at h1
    exact inner_of_innClosed hKX hXN hBK hSB hinn hInn
  all_goals
  ·
    have hJ' : J = {3, 4} ∨ J = {1, 2} := by first | exact Or.inl hJ | exact Or.inr hJ
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
    have hαB₀ : B₀.map α.toMonoidHom = B₀ := by
      rw [hB₀, ← oTwoUpper_map, hαB]
    obtain ⟨h, hh⟩ := exists_conj_of_normalizes hJU hJ' α hαU hαB₀
    refine ⟨ι.symm h, MulEquiv.ext fun z => ?_⟩
    have := congrArg (fun f : MulAut (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) =>
      ι.symm (f (ι z))) hh
    simp only [hαapp, MulEquiv.symm_apply_apply, MulAut.conj_apply, map_mul, map_inv] at this
    rw [MulAut.conj_apply]
    exact this

end KG1291S

open KG1296 KG1297 KG1291S in
theorem s3OvergroupFact_holds :
    S3OvergroupFact := by
  intro G _ _ X K S B Y hKX hXN hS hKS hiso hBK hSB hBiso hinn hBSY hYX hYne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_sylow_normalizing hKX hXN hS hSB
  obtain ⟨eB⟩ := nonempty_modO2_barOf (K := K) hBK
  have key : ∀ {M : Type} [Group M] (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M),
      (∃ T' : Sylow 2 M, (T' : Subgroup M) ≤
        Subgroup.normalizer (((barOf K B).map e.toMonoidHom : Subgroup M) : Set M)) ∧
      Nonempty (ModO2 B ≃* ModO2 ((barOf K B).map e.toMonoidHom)) := by
    intro M _ e
    have hsurj : Function.Surjective (e.toMonoidHom : (↥K ⧸ CFSG.pCore 2 ↥K) → M) := e.surjective
    refine ⟨⟨T.mapSurjective hsurj, ?_⟩, ?_⟩
    · rw [Sylow.coe_mapSurjective hsurj T]
      exact map_le_normalizer_map e hT
    · obtain ⟨e'⟩ := nonempty_modO2_map e (barOf K B)
      exact ⟨eB.trans e'⟩
  have hBB : ∀ {M : Type} [Group M] (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M),
      ((barOf K B).map e.toMonoidHom).map e.symm.toMonoidHom = barOf K B := by
    intro M _ e
    rw [Subgroup.map_map]
    convert Subgroup.map_id (barOf K B)
    ext x
    simp
  have innOf : ∀ {M : Type} [Group M] (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M),
      InnClosed ((barOf K B).map e.toMonoidHom) → InnClosed (barOf K B) := by
    intro M _ e h
    have := innClosed_map e.symm h
    rwa [hBB e] at this
  have hA7s : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hA7Z : Subgroup.center ↥(alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  have hSL4 := CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (K := ZMod 2)
    (Nat.card_zmod 2) (m := 4) (by norm_num)
  have hSL5 := CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (K := ZMod 2)
    (Nat.card_zmod 2) (m := 5) (by norm_num)
  rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    obtain ⟨-, ⟨e'⟩⟩ := key e
    rcases hBiso with ⟨⟨e3⟩⟩ | ⟨⟨e4⟩⟩
    · have hB' : Nonempty (ModO2 ((barOf K B).map e.toMonoidHom) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := ⟨e'.symm.trans e3⟩
      exact KG1291S.reduction hKX hXN hS hKS hBK
        (inner_of_innClosed hKX hXN hBK hSB hinn (innOf e (innClosed_A7 hB'))) e.isSimpleGroup
        (center_eq_bot_of_mulEquiv e hA7Z) (S3Hyp.of_map e (s3Hyp_A7 hB')) hBSY hYX hYne
    · exact (not_modO2_SL4_of_A7 ⟨e'.symm.trans e4⟩).elim
  ·
    obtain ⟨⟨T', hT'⟩, ⟨e'⟩⟩ := key e
    have hS3 : S3Hyp (barOf K B) := S3Hyp.of_map e (s3Hyp_SL (by norm_num) _)
    have hZ := center_eq_bot_of_mulEquiv e CFSG.Quasithin.SLnTwo.center_eq_bot
    rcases hBiso with ⟨⟨e3⟩⟩ | ⟨⟨e4⟩⟩
    · have hB' : Nonempty (ModO2 ((barOf K B).map e.toMonoidHom) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := ⟨e'.symm.trans e3⟩
      exact KG1291S.reduction hKX hXN hS hKS hBK (inner_of_innClosed hKX hXN hBK hSB hinn
        (innOf e (of_SL (k := 3) (Or.inl rfl) T' hT' hB' 3).1)) e.isSimpleGroup hZ hS3 hBSY
        hYX hYne
    · have hB' : Nonempty (ModO2 ((barOf K B).map e.toMonoidHom) ≃*
          Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := ⟨e'.symm.trans e4⟩
      have htop := eq_top_of_modO2_SL4 hB'
      have hInn : InnClosed ((barOf K B).map e.toMonoidHom) := by
        rw [htop]
        exact (of_top pCoreOf_top_SL4 4).1
      exact KG1291S.reduction hKX hXN hS hKS hBK
        (inner_of_innClosed hKX hXN hBK hSB hinn (innOf e hInn)) e.isSimpleGroup hZ hS3 hBSY hYX
        hYne
  ·
    obtain ⟨⟨T', hT'⟩, ⟨e'⟩⟩ := key e
    have hS3 : S3Hyp (barOf K B) := S3Hyp.of_map e (s3Hyp_SL (by norm_num) _)
    have hZ := center_eq_bot_of_mulEquiv e CFSG.Quasithin.SLnTwo.center_eq_bot
    rcases hBiso with ⟨⟨e3⟩⟩ | ⟨⟨e4⟩⟩
    · exact KG1291S.reduction hKX hXN hS hKS hBK (inner_five_three hKX hXN hS hBK hSB hinn e e3)
        e.isSimpleGroup hZ hS3 hBSY hYX hYne
    · have hB' : Nonempty (ModO2 ((barOf K B).map e.toMonoidHom) ≃*
          Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := ⟨e'.symm.trans e4⟩
      exact KG1291S.reduction hKX hXN hS hKS hBK (inner_of_innClosed hKX hXN hBK hSB hinn
        (innOf e (of_SL (k := 4) (Or.inr rfl) T' hT' hB' 4).1)) e.isSimpleGroup hZ hS3 hBSY
        hYX hYne

end CFSG.Quasithin.H13
