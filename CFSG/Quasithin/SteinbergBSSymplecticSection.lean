module

public import CFSG.Quasithin.SteinbergBSSymplecticRoots
public import CFSG.Quasithin.SteinbergBSFaithfulSection

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.Quasithin.B6
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.ABGLocalTools
  CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem config_map_injective {A X : Type*} [Group A] [Group X] [Finite A] [Finite X]
    (Ψ : A →* X) (hΨ : Function.Injective Ψ) {N R B : Subgroup A} (hNR : N ⊔ R = ⊤)
    (hR : IsSylowOf 2 R ⊤) (hRB : R ≤ B) (hB : B < ⊤)
    (hBmax : ∀ Y : Subgroup A, R ≤ Y → Y < ⊤ → Y ≤ B) :
    N.map Ψ ⊔ R.map Ψ = Ψ.range ∧ IsSylowOf 2 (R.map Ψ) Ψ.range ∧ R.map Ψ ≤ B.map Ψ ∧
      B.map Ψ < Ψ.range ∧ ∀ Y : Subgroup X, R.map Ψ ≤ Y → Y < Ψ.range → Y ≤ B.map Ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : Ψ.range = (⊤ : Subgroup A).map Ψ := MonoidHom.range_eq_map Ψ
  refine ⟨by rw [← Subgroup.map_sup, hNR, hrange], ?_, map_mono hRB, ?_, ?_⟩
  · rw [hrange]
    exact CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective Ψ hΨ hR
  · rw [hrange]
    exact (map_lt_map_iff_of_injective hΨ).2 hB
  · intro Y hRY hYA
    have h1 : (Y.comap Ψ).map Ψ = Y := map_comap_eq_self hYA.le
    have h2 : R ≤ Y.comap Ψ := map_le_iff_le_comap.1 hRY
    have h3 : Y.comap Ψ < ⊤ := by
      rw [← map_lt_map_iff_of_injective hΨ, h1, ← hrange]
      exact hYA
    rw [← h1]
    exact map_mono (hBmax _ h2 h3)

theorem
qrc_original_single_even_symplectic_section_confines_the_whole_image_to_both_central_root_directions
    {H : Type} [Group H] [Finite H] (T : Sylow 2 H)
    (hTn : ¬ (T : Subgroup H).Normal) {M : Subgroup H} (hTM : (T : Subgroup H) ≤ M)
    (hMH : M < ⊤) (hmax : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M)
    {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVQ : 4 ≤ (V ⊓ pCore 2 H).relIndex V)
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (θ : ↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))) ≃* antiSp F) :
    (antiUnipotentCenter F = rootLong F ⊔ rootShort F ∧ rootLong F ⊓ rootShort F = ⊥ ∧
      (∀ x : antiSp F, x ∈ antiUnipotentCenter F ↔
        x ∈ antiUnipotent F ∧ ∀ y ∈ antiUnipotent F, x * y = y * x) ∧
      (∀ x : antiSp F, x ∈ rootLong F ↔
        ∃ t : F, glMat (x : GL (Fin 4) F) = 1 + Matrix.single 0 3 t) ∧
      (∀ x : antiSp F, x ∈ rootShort F ↔
        ∃ t : F, glMat (x : GL (Fin 4) F) = 1 + Matrix.single 0 2 t + Matrix.single 1 3 t)) ∧
    ∃ ι : H ⧸ kerIn M ⊤ →* MulAut ↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))),
      Function.Injective ι ∧
      (∀ a k, ((ι a k : ↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))) :
        H ⧸ kerIn M ⊤) = a * k * a⁻¹) ∧
      ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))).map ι =
        ComponentClassification.OuterAutomorphisms.inner _ ∧
      (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)) ⊔
        (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) = ⊤ ∧
      ∃ θ' : ↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))) ≃* antiSp F,
        (∃ g : antiSp F, ∀ k, θ' k = g * θ k * g⁻¹) ∧
        (((T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤))).subgroupOf
          ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))).map θ'.toMonoidHom =
            antiUnipotent F ∧
        (V.map (QuotientGroup.mk' (kerIn M ⊤)) ≤
            (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)) ∧
          ((V.map (QuotientGroup.mk' (kerIn M ⊤))).subgroupOf
            ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))).map θ'.toMonoidHom ≤
              antiUnipotentCenter F) ∧
        (V ≤ oddResidualPreimage H ∧ V ⊓ kerIn M ⊤ = V ⊓ pCore 2 H ∧
          Nat.card ↥(V.map (QuotientGroup.mk' (kerIn M ⊤))) = (V ⊓ pCore 2 H).relIndex V) ∧
        (∃ s ∈ (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)), ∃ (h : antiSp F) (j : ℕ),
          Odd j ∧ j < 2 * f ∧ ∀ k, θ' (ι s k) = (MulAut.conj h * minorAut F ^ j) (θ' k)) ∧
        (∀ s ∈ (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)), ∀ (h : antiSp F) (j : ℕ),
          Odd j → (∀ k, θ' (ι s k) = (MulAut.conj h * minorAut F ^ j) (θ' k)) →
          (rootLong F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = rootShort F ∧
          (rootShort F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = rootLong F ∧
          (radA1 F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = radA2 F ∧
          (radA2 F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = radA1 F ∧
          (((V.map (QuotientGroup.mk' (kerIn M ⊤))).subgroupOf
            ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))).map θ'.toMonoidHom ⊓
              rootLong F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom =
            ((V.map (QuotientGroup.mk' (kerIn M ⊤))).subgroupOf
              ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))).map
                θ'.toMonoidHom ⊓ rootShort F) ∧
        ¬ ((V.map (QuotientGroup.mk' (kerIn M ⊤))).subgroupOf
            ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))).map θ'.toMonoidHom ≤
              rootLong F ∧
        ¬ ((V.map (QuotientGroup.mk' (kerIn M ⊤))).subgroupOf
            ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))).map θ'.toMonoidHom ≤
              rootShort F ∧
        ∀ E₁ : Subgroup (H ⧸ kerIn M ⊤), E₁ ≤ (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) →
          (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ≤
            normalizer (E₁ : Set (H ⧸ kerIn M ⊤)) → IsElementaryAbelian 2 ↥E₁ →
          E₁ ≤ (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)) ∧
            (E₁.subgroupOf ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))).map
              θ'.toMonoidHom ≤ antiUnipotentCenter F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZU : antiUnipotentCenter F = rootLong F ⊔ rootShort F ∧ rootLong F ⊓ rootShort F = ⊥ ∧
      (∀ x : antiSp F, x ∈ antiUnipotentCenter F ↔
        x ∈ antiUnipotent F ∧ ∀ y ∈ antiUnipotent F, x * y = y * x) ∧
      (∀ x : antiSp F, x ∈ rootLong F ↔
        ∃ t : F, glMat (x : GL (Fin 4) F) = 1 + Matrix.single 0 3 t) ∧
      (∀ x : antiSp F, x ∈ rootShort F ↔
        ∃ t : F, glMat (x : GL (Fin 4) F) = 1 + Matrix.single 0 2 t + Matrix.single 1 3 t) :=
    ⟨rootLong_sup_rootShort.symm, rootLong_inf_rootShort,
      CFSG.QuasithinUnique.Setup.X7b.mem_antiUnipotentCenter_iff_central, fun _ =>
        mem_rootLong_iff_glMat, fun _ => mem_rootShort_iff_glMat⟩
  refine ⟨hZU, ?_⟩
  have hTsyl : IsSylowTwoOf (T : Subgroup H) ⊤ := ⟨le_top, T.isPGroup', by
    show ¬ 2 ∣ (T : Subgroup H).relIndex ⊤
    rw [relIndex_top_right]
    exact T.not_dvd_index⟩
  obtain ⟨⟨hRJ, hJK⟩, ⟨-, hodd, -⟩, hHKT, ⟨hKn₀, -⟩, hcomp, -⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hTsyl hTn hTM hMH hmax
  revert θ
  set Q := pCore 2 H with hQdef
  set J := kerIn M ⊤ with hJdef
  set π := QuotientGroup.mk' J with hπdef
  set K₀ := oddResidualPreimage H with hK₀def
  set K := K₀.map π with hKdef
  intro θ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hπker : π.ker = J := QuotientGroup.ker_mk' J
  have hQR : Q = CFSG.Open.pCore 2 H := CFSG.pCore_eq_open H 2
  have hKn : K.Normal := hKn₀.map π hπs
  have hmin : ∀ N : Subgroup (H ⧸ J), N.Normal → N ≠ ⊥ → K ≤ N := by
    intro N hN hN1
    have hN' : (N.comap π).Normal := hN.comap π
    have hRN : CFSG.Open.pCore 2 H ≤ N.comap π := fun x hx => by
      have h : x ∈ π.ker := by
        rw [hπker]
        exact hRJ hx
      rw [mem_comap, MonoidHom.mem_ker.1 h]
      exact one_mem N
    have hNJ : ¬ N.comap π ≤ J := by
      intro hle
      apply hN1
      rw [← map_comap_eq_self_of_surjective hπs N, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_bot, ← MonoidHom.mem_ker, hπker]
      exact hle hx
    have h1 := hcomp _ hN' hRN hNJ
    rw [← map_comap_eq_self_of_surjective hπs N]
    exact map_mono h1
  have hKnab : ¬ IsMulCommutative ↥K := by
    intro hc
    have hG : ∀ x y : antiSp F, x * y = y * x := fun x y => by
      have h1 := congrArg θ (hc.is_comm.comm (θ.symm x) (θ.symm y))
      simpa using h1
    have h1 : MulAut.conj (uElt (1 : F) 0 0 0) = MulAut.conj 1 := by
      ext y
      simp [MulAut.conj_apply, hG (uElt 1 0 0 0) y]
    have h2 := (uElt_inj ((CFSG.QuasithinUnique.Setup.X7b.conj_injective h1).trans
      CFSG.QuasithinUnique.Setup.X7b.uElt_zero_eq_one.symm)).1
    exact one_ne_zero h2
  have hCK : centralizer (K : Set (H ⧸ J)) = ⊥ := by
    by_contra hne
    have hCn : (centralizer (K : Set (H ⧸ J))).Normal := ⟨fun c hc g k hk => by
      have hk' : g⁻¹ * k * g ∈ K := by
        have h1 := hKn.conj_mem k hk g⁻¹
        rwa [inv_inv] at h1
      have h1 := mem_centralizer_iff.1 hc _ hk'
      calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * k := by group⟩
    have hKC := hmin _ hCn hne
    exact hKnab ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.1 (hKC b.2) a a.2)⟩⟩
  set ι : H ⧸ J →* MulAut ↥K := MulAut.conjNormal with hιdef
  have hιapp : ∀ a (k : ↥K), ((ι a k : ↥K) : H ⧸ J) = a * k * a⁻¹ := fun a k =>
    MulAut.conjNormal_apply a k
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hCK]
    intro a ha
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : H ⧸ J)) (MonoidHom.mem_ker.1 ha)
    simp only [hιapp, MulAut.one_apply] at h1
    calc k * a = a * k * a⁻¹ * a := by rw [h1]
      _ = a * k := by group
  have hιK : ∀ k (hk : k ∈ K), ι k = MulAut.conj (⟨k, hk⟩ : ↥K) := fun k hk =>
    MulAut.conjNormal_val (h := (⟨k, hk⟩ : ↥K))
  have hKι : K.map ι = ComponentClassification.OuterAutomorphisms.inner ↥K := by
    ext φ
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, (hιK k hk).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, hιK k k.2⟩
  set R := (T : Subgroup H).map π with hRdef
  have hKS : K ⊔ R = ⊤ := by
    rw [hKdef, hRdef, ← Subgroup.map_sup, hHKT, map_top_of_surjective π hπs]
  have hRsyl : IsSylowOf 2 R ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · exact (T.mapSurjective hπs).isPGroup'
    · rw [relIndex_top_right]
      exact (T.mapSurjective hπs).not_dvd_index
  have hJM : J ≤ M := kerIn_le
  have hcomapB : (M.map π).comap π = M := by
    rw [comap_map_eq, hπker, sup_eq_left.2 hJM]
  have hBtop : M.map π < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hMH.ne ?_
    rw [← hcomapB, h, comap_top]
  have hBmax : ∀ Y : Subgroup (H ⧸ J), R ≤ Y → Y < ⊤ → Y ≤ M.map π := by
    intro Y hTY hY
    have h1 : (T : Subgroup H) ≤ Y.comap π := map_le_iff_le_comap.1 hTY
    have h2 : Y.comap π < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hY.ne ?_
      rw [← map_comap_eq_self_of_surjective hπs Y, h, map_top_of_surjective π hπs]
    rw [← map_comap_eq_self_of_surjective hπs Y]
    exact map_mono (hmax _ h1 h2)
  have hVDQ : V ⊓ J = V ⊓ Q := by
    refine le_antisymm (fun v hv => ?_) (inf_le_inf_left V (hQR ▸ hRJ))
    obtain ⟨hvV, hvJ⟩ := mem_inf.1 hv
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨v, hVT hvV⟩
    have hvn : v ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h1 := map_eq_one_of_odd_card hodd (QuotientGroup.mk' (CFSG.Open.pCore 2 H))
      (mem_map_of_mem _ hvJ) hvn
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_inf.2 ⟨hvV, hQR ▸ h1⟩
  set E := V.map π with hEdef
  have hEcard : Nat.card ↥E = (V ⊓ Q).relIndex V := by
    have h1 := card_inf_ker_mul_card_map π V
    rw [hπker, hVDQ] at h1
    have h2 := relIndex_mul_card (V ⊓ Q) V
    rw [inf_eq_left.2 inf_le_left] at h2
    have hpos : 0 < Nat.card ↥(V ⊓ Q) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos ((mul_comm _ _).trans (h1.trans h2.symm))
  have hRE : R ≤ normalizer (E : Set (H ⧸ J)) := by
    refine le_normalizer_of_forall_conj_mem ?_
    rintro _ ⟨t, ht, rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨t * v * t⁻¹, (mem_normalizer_iff.mp (hTV ht) v).mp hv, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hEelem : IsElementaryAbelian 2 ↥E := IsElementaryAbelian.map π
  have hRK : IsSylowOf 2 (R ⊓ K) K :=
    hRsyl.inf_of_le_normalizer le_top (by rw [normalizer_eq_top K])
  have hRK' : IsSylowOf 2 (R.subgroupOf K) ⊤ := by
    rw [← isSylowOf_map_subtype_iff K, subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
      range_subtype]
    exact hRK
  have hUK : IsSylowOf 2 ((R.subgroupOf K).map θ.toMonoidHom) ⊤ := by
    have h1 := CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective θ.toMonoidHom θ.injective hRK'
    rwa [map_top_of_surjective _ θ.surjective] at h1
  have hUstd : IsSylowOf 2 (antiUnipotent F) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1
      CFSG.QuasithinUnique.Setup.X7b.card_and_isSylowTwoOf_antiUnipotent.2
  obtain ⟨x, -, hx⟩ := isSylowOf_exists_map_conj hUstd hUK
  set θ' : ↥K ≃* antiSp F := θ.trans (MulAut.conj x⁻¹) with hθ'
  have hUθ' : (R.subgroupOf K).map θ'.toMonoidHom = antiUnipotent F := by
    have h1 : θ'.toMonoidHom = (MulAut.conj x⁻¹).toMonoidHom.comp θ.toMonoidHom := rfl
    rw [h1, ← Subgroup.map_map, hx]
    have h2 := map_conj_inv_map_conj (antiUnipotent F) x⁻¹
    rwa [inv_inv] at h2
  set Ψ : H ⧸ J →* MulAut (antiSp F) := (MulAut.congr θ').toMonoidHom.comp ι with hΨdef
  have hΨinj : Function.Injective Ψ := (MulAut.congr θ').injective.comp hιinj
  have hΨK : ∀ k (hk : k ∈ K), Ψ k = MulAut.conj (θ' ⟨k, hk⟩) := fun k hk => by
    show MulAut.congr θ' (ι k) = _
    rw [hιK k hk, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  have hΨapp : ∀ a (k : ↥K), Ψ a (θ' k) = θ' (ι a k) := fun a k => by
    show θ' (ι a (θ'.symm (θ' k))) = θ' (ι a k)
    rw [MulEquiv.symm_apply_apply]
  have hΨKmap : K.map Ψ = ComponentClassification.OuterAutomorphisms.inner (antiSp F) := by
    rw [hΨdef, ← Subgroup.map_map, hKι]
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr θ'
  have hmapK : ∀ X : Subgroup (H ⧸ J), X ≤ K →
      X.map Ψ = ((X.subgroupOf K).map θ'.toMonoidHom).map MulAut.conj := by
    intro X hXK
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨θ' ⟨k, hXK hk⟩, ⟨⟨k, hXK hk⟩, hk, rfl⟩, (hΨK k (hXK hk)).symm⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, hΨK k k.2⟩
  have hU : R.map Ψ ⊓ inner (antiSp F) = (antiUnipotent F).map MulAut.conj := by
    rw [← hΨKmap, ← map_inf_eq _ _ _ hΨinj, hmapK _ inf_le_right, inf_subgroupOf_right, hUθ']
  obtain ⟨hKR', hR', hRB', hBA', hBmax'⟩ :=
    config_map_injective Ψ hΨinj hKS hRsyl (map_mono hTM) hBtop hBmax
  rw [hΨKmap] at hKR'
  obtain ⟨s', hs', h₀, j₀, hj₀, hj₀f, hs'eq⟩ :=
    exists_odd_coset_mem hf hF hKR' hR' hRB' hBA' hBmax'
  have hconf : ∀ E₁ : Subgroup (H ⧸ J), E₁ ≤ R → R ≤ normalizer (E₁ : Set (H ⧸ J)) →
      IsElementaryAbelian 2 ↥E₁ →
      E₁ ≤ K ∧ (E₁.subgroupOf K).map θ'.toMonoidHom ≤ antiUnipotentCenter F := by
    intro E₁ hE₁R hRE₁ hE₁
    have hE₁' : IsElementaryAbelian 2 ↥(E₁.map Ψ) := IsElementaryAbelian.map Ψ
    have hRE₁' : R.map Ψ ≤ normalizer (E₁.map Ψ : Set (MulAut (antiSp F))) := by
      refine le_normalizer_of_forall_conj_mem ?_
      rintro _ ⟨r, hr, rfl⟩ _ ⟨e, he, rfl⟩
      exact ⟨r * e * r⁻¹, (mem_normalizer_iff.1 (hRE₁ hr) e).1 he, by
        rw [map_mul, map_mul, map_inv]⟩
    have h1 := symplectic_standard_confinement (by omega) hF hU hs' hj₀ hs'eq (E₁.map Ψ)
      (map_mono hE₁R) hRE₁' hE₁'
    have hE₁K : E₁ ≤ K := fun e he => by
      have h2 : Ψ e ∈ ComponentClassification.OuterAutomorphisms.inner (antiSp F) := by
        obtain ⟨z, -, hz⟩ := h1 (mem_map_of_mem Ψ he)
        exact ⟨z, hz⟩
      rw [← hΨKmap] at h2
      obtain ⟨k, hk, hke⟩ := h2
      rw [← hΨinj hke]
      exact hk
    refine ⟨hE₁K, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    have h2 := h1 (mem_map_of_mem Ψ (mem_subgroupOf.1 hk))
    rw [hΨK k k.2] at h2
    exact (mem_map_iff_mem CFSG.QuasithinUnique.Setup.X7b.conj_injective).1 h2
  have hER : E ≤ R := map_mono hVT
  obtain ⟨hEK, hEZ⟩ := hconf E hER hRE hEelem
  have hVK₀ : V ≤ K₀ := fun v hv => by
    obtain ⟨k, hk, hkv⟩ := hEK (mem_map_of_mem π hv)
    have h1 : k⁻¹ * v ∈ J := by
      rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hkv, inv_mul_cancel]
    have h2 : v = k * (k⁻¹ * v) := by group
    rw [h2]
    exact mul_mem hk (hJK.le h1)
  set E' := (E.subgroupOf K).map θ'.toMonoidHom with hE'def
  have hΨE : E.map Ψ = E'.map MulAut.conj := hmapK E hEK
  have hE'inv : ∀ s ∈ R, E'.map (Ψ s).toMonoidHom = E' := by
    intro s hs
    refine map_eq_of_mem_normalizer_conj CFSG.QuasithinUnique.Setup.X7b.conj_injective ?_
    rw [← hΨE]
    refine le_normalizer_of_forall_conj_mem (S := R.map Ψ) ?_ (mem_map_of_mem Ψ hs)
    rintro _ ⟨r, hr, rfl⟩ _ ⟨e, he, rfl⟩
    exact ⟨r * e * r⁻¹, (mem_normalizer_iff.1 (hRE hr) e).1 he, by
      rw [map_mul, map_mul, map_inv]⟩
  have hE'card : Nat.card ↥E' = Nat.card ↥E := by
    rw [hE'def, Subgroup.card_map_of_injective θ'.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  obtain ⟨s₀, hs₀R, rfl⟩ := hs'
  have hswap₀ := swap_of_mem hU (mem_map_of_mem Ψ hs₀R) hj₀ hs'eq
  refine ⟨ι, hιinj, hιapp, hKι, hKS, θ', ⟨x⁻¹, fun k => rfl⟩, hUθ', ⟨hEK, hEZ⟩,
    ⟨hVK₀, hVDQ, hEcard⟩, ⟨s₀, hs₀R, h₀, j₀, hj₀, hj₀f, fun k => by rw [← hΨapp, hs'eq]⟩,
    ?_, ?_, ?_, hconf⟩
  ·
    intro s hs h j hj hsk
    have hΨs : Ψ s = MulAut.conj h * minorAut F ^ j := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨k, rfl⟩ := θ'.surjective y
      rw [hΨapp, hsk k]
    obtain ⟨h1, h2, h3, h4⟩ := swap_of_mem hU (mem_map_of_mem Ψ hs) hj hΨs
    have h5 := hE'inv s hs
    rw [hΨs] at h1 h2 h3 h4 h5
    refine ⟨h1, h2, h3, h4, ?_⟩
    rw [map_inf_eq _ _ _ (MulEquiv.injective _), h5, h1]
  ·
    intro hle
    have h1 : E' ≤ rootLong F ⊓ rootShort F := by
      refine le_inf hle ?_
      calc E' = E'.map (Ψ s₀).toMonoidHom := (hE'inv s₀ hs₀R).symm
        _ ≤ (rootLong F).map (Ψ s₀).toMonoidHom := map_mono hle
        _ = rootShort F := hswap₀.1
    rw [rootLong_inf_rootShort, le_bot_iff] at h1
    have h2 : Nat.card ↥E' = 1 := by rw [h1, Subgroup.card_bot]
    rw [hE'card, hEcard] at h2
    omega
  ·
    intro hle
    have h1 : E' ≤ rootLong F ⊓ rootShort F := by
      refine le_inf ?_ hle
      calc E' = E'.map (Ψ s₀).toMonoidHom := (hE'inv s₀ hs₀R).symm
        _ ≤ (rootShort F).map (Ψ s₀).toMonoidHom := map_mono hle
        _ = rootLong F := hswap₀.2.1
    rw [rootLong_inf_rootShort, le_bot_iff] at h1
    have h2 : Nat.card ↥E' = 1 := by rw [h1, Subgroup.card_bot]
    rw [hE'card, hEcard] at h2
    omega

end CFSG.Quasithin.SteinbergBS
