module

public import CFSG.Quasithin.Vol2.KGFact1295Red
public import CFSG.Quasithin.Recognition.GoldschmidtBasic
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport

public section

namespace CFSG.Quasithin.H13.KG1291S

open CFSG.Open CFSG.Quasithin.H13.KG1296 CFSG.Quasithin.H13.KG1297 CFSG.Quasithin.H13.KG1295

section Model

variable {M : Type} [Group M]

@[expose] def S3Hyp (B : Subgroup M) : Prop :=
  ∀ (T : Sylow 2 M) (Y : Subgroup M), (T : Subgroup M) ≤ Y → B ≤ Y → Y ≠ ⊤ →
    ∃ H : Subgroup M, (T : Subgroup M) ≤ H ∧ ¬ H ≤ Y ∧ Nonempty (ModO2 H ≃* Equiv.Perm (Fin 3))

theorem S3Hyp.of_map [Finite M] {M' : Type} [Group M'] (e : M ≃* M') {B : Subgroup M}
    (h : S3Hyp (B.map e.toMonoidHom)) : S3Hyp B := by
  intro T Y hTY hBY hY
  have hsurj : Function.Surjective (e.toMonoidHom : M → M') := e.surjective
  have hinj : Function.Injective (e.toMonoidHom : M → M') := e.injective
  have hY' : Y.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.comap e.toMonoidHom) htop
    rwa [Subgroup.comap_map_eq_self_of_injective hinj, Subgroup.comap_top] at this
  have hTY' : ((T.mapSurjective hsurj : Sylow 2 M') : Subgroup M') ≤ Y.map e.toMonoidHom := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hTY
  obtain ⟨H, hTH, hHY, ⟨eH⟩⟩ := h (T.mapSurjective hsurj) (Y.map e.toMonoidHom) hTY'
    (Subgroup.map_mono hBY) hY'
  have hHH : (H.comap e.toMonoidHom).map e.toMonoidHom = H :=
    Subgroup.map_comap_eq_self_of_surjective hsurj H
  refine ⟨H.comap e.toMonoidHom, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    rw [Sylow.coe_mapSurjective] at hTH
    exact hTH
  · intro hle
    apply hHY
    rw [← hHH]
    exact Subgroup.map_mono hle
  · obtain ⟨e'⟩ := nonempty_modO2_map e (H.comap e.toMonoidHom)
    rw [hHH] at e'
    exact ⟨e'.trans eH⟩

theorem nonempty_modO2_top_perm3 {A : Type} [Group A] (e : A ≃* Equiv.Perm (Fin 3)) :
    Nonempty (ModO2 (⊤ : Subgroup A) ≃* Equiv.Perm (Fin 3)) := by
  have hbot : CFSG.pCore 2 ↥(⊤ : Subgroup A) = ⊥ :=
    CFSG.Semidihedral.Local.normal_isPGroup_two_eq_bot (Subgroup.topEquiv.trans e) _
      CFSG.pCore_normal
      CFSG.pCore_isPGroup
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans
    (Subgroup.topEquiv.trans e)⟩

theorem modO2_perm3_of_index_three [Finite M] {H T : Subgroup M} (hTH : T ≤ H)
    (hT2 : IsPGroup 2 T) (hidx : T.relIndex H = 3)
    (hnorm : ¬ H ≤ Subgroup.normalizer (T : Set M)) :
    Nonempty (ModO2 H ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' : Subgroup ↥H := T.subgroupOf H with hT'
  have hidx' : T'.index = 3 := hidx
  have hcore2 : IsPGroup 2 T'.normalCore := by
    have hT'2 : IsPGroup 2 T' := hT2.comap_subtype
    exact hT'2.to_le T'.normalCore_le
  rcases CFSG.Quasithin.gold_normalCore_quotient_equiv hidx' with ⟨hc, -⟩ | ⟨-, ⟨e⟩⟩
  ·
    exfalso
    have hle : T'.normalCore ≤ T' := T'.normalCore_le
    have heq : T'.normalCore = T' := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      have h1 := T'.normalCore.card_mul_index
      have h2 := T'.card_mul_index
      rw [hc] at h1
      rw [hidx'] at h2
      omega
    apply hnorm
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have htH : t ∈ H := hTH ht
      have hn : (T'.normalCore).Normal := T'.normalCore_normal
      have hmem : (⟨t, htH⟩ : ↥H) ∈ T'.normalCore := by rw [heq]; exact ht
      have := hn.conj_mem _ hmem ⟨h, hh⟩
      rw [heq] at this
      exact this
    · intro ht
      have htH : t ∈ H := by
        have := H.mul_mem (H.mul_mem (H.inv_mem hh) (hTH ht)) hh
        simpa [mul_assoc] using this
      have hn : (T'.normalCore).Normal := T'.normalCore_normal
      have hmem : (⟨h * t * h⁻¹, hTH ht⟩ : ↥H) ∈ T'.normalCore := by rw [heq]; exact ht
      have := hn.conj_mem _ hmem ⟨h, hh⟩⁻¹
      rw [heq] at this
      have e1 : ((⟨h, hh⟩ : ↥H)⁻¹ * ⟨h * t * h⁻¹, hTH ht⟩ * (⟨h, hh⟩ : ↥H)⁻¹⁻¹ : ↥H) =
          ⟨t, htH⟩ := by
        apply Subtype.ext
        simp [mul_assoc]
      rw [e1] at this
      exact this
  ·
    set f : ↥H →* ↥(⊤ : Subgroup (Equiv.Perm (Fin 3))) :=
      (Subgroup.topEquiv.symm.toMonoidHom.comp e.toMonoidHom).comp
        (QuotientGroup.mk' T'.normalCore) with hf
    have hfs : Function.Surjective f := by
      intro y
      obtain ⟨q, hq⟩ := e.surjective (Subgroup.topEquiv y)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective T'.normalCore q
      refine ⟨x, ?_⟩
      simp only [hf, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hq, MulEquiv.symm_apply_apply]
    have hker : IsPGroup 2 f.ker := by
      have hk : f.ker = T'.normalCore := by
        ext x
        simp only [hf, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
          MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
      rw [hk]
      exact hcore2
    obtain ⟨e1⟩ := nonempty_modO2_equiv f hfs hker
    obtain ⟨e2⟩ := nonempty_modO2_top_perm3 (MulEquiv.refl (Equiv.Perm (Fin 3)))
    exact ⟨e1.trans e2⟩

end Model

variable {G : Type} [Group G]

section Lift

variable [Finite G] {X : Subgroup G} {M : Type} [Group M] (ρ : ↥X →* M)

theorem exists_of_s3 (hρ : Function.Surjective ρ) (hker2 : IsPGroup 2 ρ.ker) {S Y : Subgroup G}
    (hSX : S ≤ X) {H₀ : Subgroup M} (hSH : (S.subgroupOf X).map ρ ≤ H₀)
    (hHY : ¬ H₀ ≤ (Y.subgroupOf X).map ρ) (hH : Nonempty (ModO2 H₀ ≃* Equiv.Perm (Fin 3))) :
    ∃ H : Subgroup G, S ≤ H ∧ H ≤ X ∧ ¬ H ≤ Y ∧
      Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) := by
  set H : Subgroup G := (H₀.comap ρ).map X.subtype with hHdef
  have hHX : H ≤ X := Subgroup.map_subtype_le _
  have hmemH : ∀ x (hx : x ∈ X), x ∈ H ↔ ρ ⟨x, hx⟩ ∈ H₀ := by
    intro x hx
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact hx'
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hHimg : (H.subgroupOf X).map ρ = H₀ := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmemH x x.2).1 hx
    · intro hz
      obtain ⟨x, rfl⟩ := hρ z
      exact ⟨x, (hmemH x x.2).2 hz, rfl⟩
  refine ⟨H, fun s hs => (hmemH s (hSX hs)).2 (hSH ⟨⟨s, hSX hs⟩, hs, rfl⟩), hHX, ?_, ?_⟩
  · intro hle
    apply hHY
    rw [← hHimg]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X hle)
  · obtain ⟨e⟩ := modO2_img ρ hker2 hHX
    rw [hHimg] at e
    obtain ⟨eH⟩ := hH
    exact ⟨e.trans eH⟩

end Lift

theorem inner_of_innClosed [Finite G] {X K S B : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hBK : B ≤ K)
    (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hinn : ∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B)
    (hInn : InnClosed (barOf K B)) :
    ∀ s : ↥X, (s : G) ∈ S →
      ∃ z, (actBar K).comp (Subgroup.inclusion hXN) s = MulAut.conj z := by
  intro s hs
  obtain ⟨b, hbB, hb⟩ := exists_actBar_eq hKX hXN hBK hSB hinn hInn s hs
  refine ⟨((⟨b, hBK hbB⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K), ?_⟩
  rw [hb]
  exact actBar_of_mem _ (hBK hbB)

theorem reduction [Finite G] {X K S B Y : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hS : QuasithinUnique.IsSylowTwoOf S X)
    (hKS : K ⊔ S = X) (hBK : B ≤ K)
    (hinnK : ∀ s : ↥X, (s : G) ∈ S →
      ∃ z, (actBar K).comp (Subgroup.inclusion hXN) s = MulAut.conj z)
    (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hS3 : S3Hyp (barOf K B))
    (hBSY : B ⊔ S ≤ Y) (hYX : Y ≤ X) (hYne : Y ≠ X) :
    ∃ H : Subgroup G, S ≤ H ∧ H ≤ X ∧ ¬ H ≤ Y ∧
      Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSX : S ≤ X := hS.1
  have hS2 : IsPGroup 2 S := hS.2.1
  have hBX : B ≤ X := hBK.trans hKX
  obtain ⟨ψ, hψK, hψker, -⟩ := exists_psi_of_inner hKX hXN hKS hinnK hZ
  set D := centralizerMod (pCoreOf 2 K) X K with hDdef
  have hnab : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a := by
    have : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) := hs.toNontrivial
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
  have hkerS : ∀ x : ↥X, ψ x = 1 → (x : G) ∈ S := fun x hx => hDS ((hψker x).1 hx)
  have hker2 : IsPGroup 2 ψ.ker := by
    intro x
    obtain ⟨k, hk⟩ := hD2 ⟨_, (hψker x).1 x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
    exact ⟨⟨k, hKX k.2⟩, hψK k k.2⟩
  obtain ⟨T, hT⟩ := exists_sylow_image hKX hXN hS
  have hψS : (S.subgroupOf X).map ψ = T := by
    have hle : (T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ (S.subgroupOf X).map ψ := by
      rw [hT]
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨⟨k, hKX k.2⟩, hk, hψK k k.2⟩
    have h2 : IsPGroup 2 ((S.subgroupOf X).map ψ) := hS2.comap_subtype.map ψ
    exact T.is_maximal' h2 hle
  have hψB : (B.subgroupOf X).map ψ = barOf K B := by
    ext z
    constructor
    · rintro ⟨⟨b, hbX⟩, hb, rfl⟩
      exact ⟨⟨b, hBK hb⟩, hb, (hψK b (hBK hb)).symm⟩
    · rintro ⟨⟨b, hbK⟩, hb, rfl⟩
      exact ⟨⟨b, hKX hbK⟩, hb, hψK b hbK⟩
  set Yb := (Y.subgroupOf X).map ψ with hYb
  have hTY : (T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ Yb := by
    rw [← hψS]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X (le_sup_right.trans hBSY))
  have hBY : barOf K B ≤ Yb := by
    rw [← hψB]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X (le_sup_left.trans hBSY))
  have hYb : Yb ≠ ⊤ := by
    intro htop
    apply hYne
    refine le_antisymm hYX ?_
    have hkerY : ∀ x : ↥X, ψ x = 1 → (x : G) ∈ Y := fun x hx =>
      (le_sup_right.trans hBSY) (hkerS x hx)
    refine le_of_img_le ψ le_rfl hkerY ?_
    rw [← hYb, htop]
    exact le_top
  obtain ⟨H₀, hTH, hHY, hH⟩ := hS3 T Yb hTY hBY hYb
  exact exists_of_s3 ψ hψs hker2 hSX (hψS ▸ hTH) hHY hH

end CFSG.Quasithin.H13.KG1291S
