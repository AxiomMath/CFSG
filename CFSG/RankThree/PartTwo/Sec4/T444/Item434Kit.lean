module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltCtx
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Kit

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open Subgroup Item434Alt
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section Layer

variable {G : Type} [Group G] {X : Type*} [Group X]

@[expose] noncomputable def layerQuot (e : layer G ⧸ Subgroup.center (layer G) ≃* X) :
    layer G →* X :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (layer G)))

theorem layerQuot_apply (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (x : layer G) :
    layerQuot e x = e (x : layer G ⧸ Subgroup.center (layer G)) :=
  rfl

theorem layerQuot_surjective (e : layer G ⧸ Subgroup.center (layer G) ≃* X) :
    Function.Surjective (layerQuot e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_layerQuot (e : layer G ⧸ Subgroup.center (layer G) ≃* X) :
    (layerQuot e).ker = Subgroup.center (layer G) := by
  ext x
  rw [MonoidHom.mem_ker, layerQuot, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem layerQuot_injective (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hZ : Subgroup.center (layer G) = ⊥) : Function.Injective (layerQuot e) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_layerQuot, hZ]

theorem quotConj_layerQuot (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (g : G)
    (x : layer G) : quotConj e g (layerQuot e x) = layerQuot e (layerConj G g x) :=
  quotConj_apply_mk e g x

theorem quotConj_eq_conj_layerQuot (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {l : G}
    (hl : l ∈ layer G) : quotConj e l = MulAut.conj (layerQuot e ⟨l, hl⟩) :=
  quotConj_of_mem e hl

theorem ker_quotConj (hL : IsQuasisimple (layer G)) (e : layer G ⧸ Subgroup.center (layer G) ≃* X) :
    (quotConj e).ker = Subgroup.centralizer (layer G : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, quotConj_eq_one_iff hL]

@[expose] noncomputable def layerEquiv (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hZ : Subgroup.center (layer G) = ⊥) : layer G ≃* X :=
  MulEquiv.ofBijective (layerQuot e) ⟨layerQuot_injective e hZ, layerQuot_surjective e⟩

theorem layerEquiv_apply (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hZ : Subgroup.center (layer G) = ⊥) (x : layer G) : layerEquiv e hZ x = layerQuot e x :=
  rfl

@[expose] noncomputable def liftSub (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hZ : Subgroup.center (layer G) = ⊥) (D : Subgroup X) : Subgroup G :=
  (D.map (layerEquiv e hZ).symm.toMonoidHom).map (layer G).subtype

theorem liftSub_le (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hZ : Subgroup.center (layer G) = ⊥) (D : Subgroup X) : liftSub e hZ D ≤ layer G :=
  Subgroup.map_subtype_le _

theorem card_liftSub (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hZ : Subgroup.center (layer G) = ⊥) (D : Subgroup X) :
    Nat.card (liftSub e hZ D) = Nat.card D := by
  rw [liftSub, Subgroup.card_map_of_injective (layer G).subtype_injective,
    Subgroup.card_map_of_injective (layerEquiv e hZ).symm.injective]

theorem isElemAbelian_liftSub (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hZ : Subgroup.center (layer G) = ⊥) {p : ℕ} {D : Subgroup X}
    (hD : CFSG.Assembly.IsElemAbelian p D) : CFSG.Assembly.IsElemAbelian p (liftSub e hZ D) :=
  CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map p _ _
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map p _ D hD)

end Layer

theorem mem_range_conj_of_pow_three {X : Type*} [Group X] (hX : ¬ 3 ∣ Nat.card (Outer X))
    {φ : MulAut X} (hφ : φ ^ 3 = 1) : φ ∈ (MulAut.conj : X →* MulAut X).range := by
  set q := QuotientGroup.mk' (inner X) φ with hq
  have hq3 : q ^ 3 = 1 := by rw [hq, ← map_pow, hφ, map_one]
  have hcop : Nat.Coprime 3 (Nat.card (Outer X)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX
  have hd : orderOf q ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_natCard q)
  have hq1 : q = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq1
  exact hq1

theorem conj_injective_of_center_eq_bot {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : x ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun y => by
    have h1 := congrArg (fun f : MulAut X => f y) hx
    change x * y * x⁻¹ = y at h1
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem isElemAbelian_of_map_injective {X Y : Type*} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Injective f) {p : ℕ} {P : Subgroup X}
    (hP : CFSG.Assembly.IsElemAbelian p (P.map f)) : CFSG.Assembly.IsElemAbelian p P := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val
      (hP.1.is_comm.comm ⟨f a, a, a.2, rfl⟩ ⟨f b, b, b.2, rfl⟩)
  · rw [map_pow, map_one]
    exact hP.2 _ ⟨x, hx, rfl⟩

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem normalizer_le (h : Ctx434Core G A M Q) {B : Subgroup G} (hBA : B ≤ A)
    (hB9 : 9 ≤ Nat.card B) : Subgroup.normalizer (B : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Source.isElemAbelian_of_le h.isE27.1 hBA
  obtain ⟨k, hk⟩ := (h.isE27.isPGroup.to_le hBA).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := B) (n := 2)
    (by rw [hk]; exact pow_dvd_pow 3 hk2)
  have hKe : CFSG.Assembly.IsElemAbelian 3 (K.map B.subtype) :=
    Source.isElemAbelian_of_le hBe (Subgroup.map_subtype_le K)
  have hB2 : 2 ≤ CFSG.Open.pRank 3 B :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three B)
      ⟨_, Subgroup.map_subtype_le K, hKe,
        by rw [Subgroup.card_map_of_injective B.subtype_injective, hK]⟩
  exact (normalizer_le_gamma hBA hB2).trans h.gamma_le

theorem card_le_card_inf_comap (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    {F : Subgroup (MulAut X)} (hFA : F ≤ A.map (quotConj e)) :
    Nat.card F ≤ Nat.card (A ⊓ F.comap (quotConj e) : Subgroup G) := by
  have hmap : (A ⊓ F.comap (quotConj e)).map (quotConj e) = F := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hb.2
    · intro φ hφ
      obtain ⟨a, ha, rfl⟩ := hFA hφ
      exact ⟨a, ⟨ha, hφ⟩, rfl⟩
  calc Nat.card F = Nat.card ((A ⊓ F.comap (quotConj e)).map (quotConj e)) := by rw [hmap]
    _ ≤ Nat.card (A ⊓ F.comap (quotConj e) : Subgroup G) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)

theorem inf_centralizer_layer_eq_bot (h : Ctx434Core G A M Q)
    (hZ : Subgroup.center (layer G) = ⊥) (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    {D : Subgroup X} (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD27 : Nat.card D = 27) :
    A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
  have hle : liftSub e hZ D ≤ layer G := liftSub_le e hZ D
  have he : CFSG.Assembly.IsElemAbelian 3 (liftSub e hZ D) := isElemAbelian_liftSub e hZ hD
  have hc : Nat.card (liftSub e hZ D) = 27 := by rw [card_liftSub, hD27]
  exact Item434Alt.inf_centralizer_layer_eq_bot_of_le (D := liftSub e hZ D) h hZ hle he hc

theorem card_map_quotConj (h : Ctx434Core G A M Q)
    (hC : A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) : Nat.card (A.map (quotConj e)) = 27 := by
  have h27 := card_eq_card_inf_ker_mul_card_map (quotConj e) A
  rw [h.isE27.2, ker_quotConj h.isQuasisimple e, hC, Subgroup.card_bot, one_mul] at h27
  exact h27.symm

theorem isElemAbelian_map_quotConj (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) :
    CFSG.Assembly.IsElemAbelian 3 (A.map (quotConj e)) :=
  CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ A h.isE27.1

theorem centralizer_layer_eq_bot (h : Ctx434Core G A M Q)
    (hC : A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥) :
    Subgroup.centralizer (layer G : Set G) = ⊥ := by
  rcases h.rank3II_4_38 with ⟨hO, hF, -⟩ | ⟨-, h3⟩
  · have hCL : Subgroup.centralizer (layer G : Set G) ≤ layer G := by
      have h' := CFSG.centralizer_generalizedFitting_le G
      rwa [hF] at h'
    have hZ := h.map_center_layer_le_pCore
    rw [hO, le_bot_iff] at hZ
    rw [eq_bot_iff]
    intro x hx
    have hmem : x ∈ layer G ⊓ Subgroup.centralizer (layer G : Set G) := ⟨hCL hx, hx⟩
    rwa [CFSG.GroupTheory.inf_centralizer_eq_map_center, hZ] at hmem
  · rw [hC, Subgroup.card_bot] at h3
    omega

theorem quotConj_injective (h : Ctx434Core G A M Q)
    (hC : A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) : Function.Injective (quotConj e) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_quotConj h.isQuasisimple e, centralizer_layer_eq_bot h hC]

theorem map_comap_conj_eq (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hX : ¬ 3 ∣ Nat.card (Outer X)) :
    ((A.map (quotConj e)).comap (MulAut.conj : X →* MulAut X)).map MulAut.conj =
      A.map (quotConj e) := by
  apply Subgroup.map_comap_eq_self
  rintro _ ⟨a, ha, rfl⟩
  exact mem_range_conj_of_pow_three hX (by rw [← map_pow, h.isE27.1.2 a ha, map_one])

theorem false_of_le_centralizer (h : Ctx434Core G A M Q) {B D : Subgroup G} (hBA : B ≤ A)
    (hB9 : 9 ≤ Nat.card B) (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD81 : 81 ≤ Nat.card D)
    (hDB : D ≤ Subgroup.centralizer (B : Set G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDM : D ≤ M :=
    hDB.trans ((Subgroup.centralizer_le_normalizer _).trans (normalizer_le h hBA hB9))
  obtain ⟨k, hk⟩ := (Sec5.isPGroup_of_isElemAbelian hD).exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := D) (n := 4)
    (by rw [hk]; exact pow_dvd_pow 3 hk4)
  have hKe : CFSG.Assembly.IsElemAbelian 3 (K.map D.subtype) :=
    Source.isElemAbelian_of_le hD (Subgroup.map_subtype_le K)
  have h4 : 4 ≤ CFSG.Open.pRank 3 M :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three M)
      ⟨_, (Subgroup.map_subtype_le K).trans hDM, hKe,
        by rw [Subgroup.card_map_of_injective D.subtype_injective, hK]⟩
  rw [h.pRank_eq] at h4
  omega

theorem false_of_fixed (h : Ctx434Core G A M Q) (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {B : Subgroup G} (hBA : B ≤ A)
    (hB9 : 9 ≤ Nat.card B) {D : Subgroup X} (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hD81 : 81 ≤ Nat.card D) (hfix : ∀ b ∈ B, ∀ d ∈ D, quotConj e b d = d) : False := by
  refine false_of_le_centralizer h hBA hB9 (isElemAbelian_liftSub e hZ hD)
    (by rw [card_liftSub]; exact hD81) ?_
  rintro _ ⟨y, ⟨d, hd, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  set ι := layerEquiv e hZ
  have hconj : layerConj G b (ι.symm d) = ι.symm d := by
    apply layerQuot_injective e hZ
    rw [← quotConj_layerQuot]
    have hd' : layerQuot e (ι.symm d) = d := ι.apply_symm_apply d
    rw [hd', hfix b hb d hd]
  have h1 : b * ((ι.symm d : layer G) : G) * b⁻¹ = ι.symm d := by
    rw [← layerConj_apply_coe, hconj]
  change b * ((ι.symm d : layer G) : G) = ((ι.symm d : layer G) : G) * b
  calc b * ((ι.symm d : layer G) : G) = b * ((ι.symm d : layer G) : G) * b⁻¹ * b := by group
    _ = ((ι.symm d : layer G) : G) * b := by rw [h1]

theorem false_of_normalizer (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hK : ∀ Y : Subgroup (MulAut X), ¬ 3 ∣ Nat.card Y →
      A.map (quotConj e) ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥) : False := by
  obtain ⟨-, hQ3, hAQ⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  have hQC := Item434.inf_centralizer_layer_eq_bot h
  have hQcard : Nat.card (Q.map (quotConj e)) = Nat.card Q := by
    have h1 := card_eq_card_inf_ker_mul_card_map (quotConj e) Q
    rw [ker_quotConj h.isQuasisimple e, hQC, Subgroup.card_bot, one_mul] at h1
    exact h1.symm
  have hY := hK (Q.map (quotConj e)) (by rw [hQcard]; exact hQ3)
    ((Subgroup.map_mono hAQ).trans (Subgroup.le_normalizer_map _))
  apply h.ne_bot
  rw [← Subgroup.card_eq_one, ← hQcard, hY, Subgroup.card_bot]

theorem false_of_normalizer_conj (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {P : Subgroup (MulAut X)}
    (hP : ∀ Y : Subgroup (MulAut X), ¬ 3 ∣ Nat.card Y →
      P ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥)
    (ψ : MulAut X) (hψ : A.map (quotConj e) = P.map (MulAut.conj ψ).toMonoidHom) : False := by
  refine false_of_normalizer h e fun Y hY3 hAY => ?_
  set Y' := Y.map (MulAut.conj ψ⁻¹).toMonoidHom with hY'
  have hY'card : Nat.card Y' = Nat.card Y :=
    Subgroup.card_map_of_injective (MulAut.conj ψ⁻¹).injective
  have hPY : P ≤ Subgroup.normalizer (Y' : Set (MulAut X)) := by
    have h1 := (Subgroup.map_mono (f := (MulAut.conj ψ⁻¹).toMonoidHom) hAY).trans
      (Subgroup.le_normalizer_map (MulAut.conj ψ⁻¹).toMonoidHom)
    rw [hψ, Subgroup.map_map] at h1
    convert h1 using 1
    rw [eq_comm]
    convert Subgroup.map_id P
    ext φ
    simp
  have hY'1 := hP Y' (by rw [hY'card]; exact hY3) hPY
  rw [← Subgroup.card_eq_one, ← hY'card, hY'1, Subgroup.card_bot]

theorem layer_le_of_fixed_gens (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {S : Set X}
    (hS : (⊤ : Subgroup X) ≤ Subgroup.closure S)
    (hgen : ∀ σ ∈ S, Nat.Coprime (orderOf σ) 3 ∧ ∃ F : Subgroup (MulAut X),
      F ≤ A.map (quotConj e) ∧ 9 ≤ Nat.card F ∧ ∀ φ ∈ F, φ σ = σ) :
    layer G ≤ M := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  set φ := layerQuot e with hφ
  have hZ : IsPGroup 3 ((⊤ : Subgroup (layer G)) ⊓ φ.ker : Subgroup (layer G)) := by
    rw [top_inf_eq, hφ, ker_layerQuot]
    exact h.isPGroup_center_layer
  have hcen : ∀ z ∈ (⊤ : Subgroup (layer G)) ⊓ φ.ker, ∀ l ∈ (⊤ : Subgroup (layer G)),
      z * l = l * z := by
    intro z hz l _
    rw [top_inf_eq, hφ, ker_layerQuot] at hz
    exact (Subgroup.mem_center_iff.mp hz l).symm
  set R : Subgroup (layer G) := M.comap (layer G).subtype with hR
  have hlift : ∀ σ ∈ S, σ ∈ R.map φ := by
    intro σ hσ
    obtain ⟨hσ3, F, hFA, hF9, hFfix⟩ := hgen σ hσ
    obtain ⟨x, rfl⟩ := layerQuot_surjective e σ
    obtain ⟨y, -, hyx, hy3⟩ := exists_coprime_lift φ hZ (Subgroup.mem_top x) hσ3
    set B := A ⊓ F.comap (quotConj e) with hB
    have hB9 : 9 ≤ Nat.card B := hF9.trans (card_le_card_inf_comap e hFA)
    have hyB : (y : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hconj : layerConj G b y = y := by
        refine eq_of_coprime_lift φ hZ hcen (Subgroup.mem_top _) (Subgroup.mem_top _) ?_ ?_ hy3
        · rw [hφ, ← quotConj_layerQuot, ← hφ, hyx]
          exact hFfix _ hb.2
        · rw [MulEquiv.orderOf_eq]
          exact hy3
      have h1 : b * (y : G) * b⁻¹ = y := by rw [← layerConj_apply_coe, hconj]
      calc b * (y : G) = b * y * b⁻¹ * b := by group
        _ = y * b := by rw [h1]
    exact ⟨y, (Subgroup.centralizer_le_normalizer _).trans (normalizer_le h inf_le_left hB9) hyB,
      hyx⟩
  have hker : φ.ker ≤ Subgroup.center (layer G) := by rw [hφ, ker_layerQuot]
  have hrange : φ.range ≤ R.map φ := by
    rw [MonoidHom.range_eq_top.mpr (layerQuot_surjective e)]
    exact hS.trans ((Subgroup.closure_le _).mpr hlift)
  have htop := eq_top_of_range_le_map φ hker hrange
  intro x hx
  have hmem : (⟨x, hx⟩ : layer G) ∈ R := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

theorem false_of_fixed_gens (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {S : Set X}
    (hS : (⊤ : Subgroup X) ≤ Subgroup.closure S)
    (hgen : ∀ σ ∈ S, Nat.Coprime (orderOf σ) 3 ∧ ∃ F : Subgroup (MulAut X),
      F ≤ A.map (quotConj e) ∧ 9 ≤ Nat.card F ∧ ∀ φ ∈ F, φ σ = σ) : False :=
  h.not_le (layer_le_of_fixed_gens h e hS hgen)

theorem layer_le_of_normalizer_gens (h : Ctx434Core G A M Q)
    (hC : A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {S : Set X}
    (hS : (⊤ : Subgroup X) ≤ Subgroup.closure S)
    (hgen : ∀ σ ∈ S, ∃ F : Subgroup (MulAut X), F ≤ A.map (quotConj e) ∧ 9 ≤ Nat.card F ∧
      MulAut.conj σ ∈ Subgroup.normalizer (F : Set (MulAut X))) :
    layer G ≤ M := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hinj := quotConj_injective h hC e
  set φ := layerQuot e with hφ
  set R : Subgroup (layer G) := M.comap (layer G).subtype with hR
  have hlift : ∀ σ ∈ S, σ ∈ R.map φ := by
    intro σ hσ
    obtain ⟨F, hFA, hF9, hFN⟩ := hgen σ hσ
    obtain ⟨x, rfl⟩ := layerQuot_surjective e σ
    set B := A ⊓ F.comap (quotConj e) with hB
    have hB9 : 9 ≤ Nat.card B := hF9.trans (card_le_card_inf_comap e hFA)
    have key : ∀ l : layer G, MulAut.conj (φ l) ∈ Subgroup.normalizer (F : Set (MulAut X)) →
        ∀ b ∈ B, (l : G) * b * (l : G)⁻¹ ∈ B := by
      intro l hl b hb
      have hq : quotConj e ((l : G) * b * (l : G)⁻¹) =
          MulAut.conj (φ l) * quotConj e b * (MulAut.conj (φ l))⁻¹ := by
        rw [map_mul, map_mul, map_inv, quotConj_eq_conj_layerQuot e l.2]
      have hmemF : quotConj e ((l : G) * b * (l : G)⁻¹) ∈ F := by
        rw [hq]
        exact (Subgroup.mem_normalizer_iff.mp hl _).mp hb.2
      obtain ⟨a, ha, hae⟩ := hFA hmemF
      have hal : a = (l : G) * b * (l : G)⁻¹ := hinj hae
      exact ⟨hal ▸ ha, hmemF⟩
    have hxN : (x : G) ∈ Subgroup.normalizer (B : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      refine ⟨key x hFN b, fun hb => ?_⟩
      have hinv : MulAut.conj (φ x⁻¹) ∈ Subgroup.normalizer (F : Set (MulAut X)) := by
        rw [map_inv, map_inv]
        exact inv_mem hFN
      have h1 := key x⁻¹ hinv _ hb
      have e1 : ((x⁻¹ : layer G) : G) * ((x : G) * b * (x : G)⁻¹) * ((x⁻¹ : layer G) : G)⁻¹ =
          b := by
        simp only [Subgroup.coe_inv, inv_inv]
        group
      rwa [e1] at h1
    exact ⟨x, normalizer_le h inf_le_left hB9 hxN, rfl⟩
  have hker : φ.ker ≤ Subgroup.center (layer G) := by rw [hφ, ker_layerQuot]
  have hrange : φ.range ≤ R.map φ := by
    rw [MonoidHom.range_eq_top.mpr (layerQuot_surjective e)]
    exact hS.trans ((Subgroup.closure_le _).mpr hlift)
  have htop := eq_top_of_range_le_map φ hker hrange
  intro x hx
  have hmem : (⟨x, hx⟩ : layer G) ∈ R := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

theorem false_of_normalizer_gens (h : Ctx434Core G A M Q)
    (hC : A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {S : Set X}
    (hS : (⊤ : Subgroup X) ≤ Subgroup.closure S)
    (hgen : ∀ σ ∈ S, ∃ F : Subgroup (MulAut X), F ≤ A.map (quotConj e) ∧ 9 ≤ Nat.card F ∧
      MulAut.conj σ ∈ Subgroup.normalizer (F : Set (MulAut X))) : False :=
  h.not_le (layer_le_of_normalizer_gens h hC e hS hgen)

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item434Kit
