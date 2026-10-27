module

public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S152He13A
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverSylowGroup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace He13

variable {G : Type} [Group G] [Finite G] {T Mc M H D : Subgroup G}

theorem vc_centralizes (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h19 : Lemma1519Concl T Mc M) (hH : IsHStar T M H) :
    ∀ k ∈ VZ T Mc, ∀ y ∈ conjClosure (V154 T Mc M) H, k * y = y * k := by
  have hOrd : OrdLE T Mc M := h19.two.2 Mc hq.inM_mc
  have hVcU : VZ T Mc ≤ VZ T M := VZ_le_of_ordLE hOrd
  have hHMc : H ≤ Mc := (h19.three H hH).1.trans (h19.three H hH).2
  exact centralizes_conjClosure (isElemAbelian_VZ hq hM.1.1) (V154_le_VZ T Mc M) hVcU hHMc
    (le_normalizer_VZ T Mc)

theorem not_case1512Six (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h19 : Lemma1519Concl T Mc M) (h15 : Lemma1515Concl T Mc M) (hH : IsHStar T M H)
    (hDY : D ≤ conjClosure (V154 T Mc M) H) (hD : E2.IsExtraspecialPlus 2 D)
    (φ : ↥(conjClosure (V154 T Mc M) H) →* Equiv.Perm (Fin 3)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = D.subgroupOf (conjClosure (V154 T Mc M) H)) :
    ¬ Case1512Six T Mc M := by
  classical
  intro hB
  have hcent := vc_centralizes hq hM h19 hH
  have hVeq : V154 T Mc M = uJ154 T M := V154_eq_uJ hB
  have hcard16 : Nat.card (V154 T Mc M) = 16 := by rw [hVeq]; exact hB.2.2.2.1
  have hidx : (M ⊓ Mc).relIndex M = 3 := hB.2.2.2.2.2.2.2
  have hgen := h15.gen
  have hM0 : m0Of T Mc M ≤ M := preOn_le _ _ _
  have hZK : quasithinOmegaOneCenter T ≤ VZ T Mc := le_conjClosure _ Mc
  have hVY : V154 T Mc M ≤ conjClosure (V154 T Mc M) H := le_conjClosure _ H
  have hNV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hNK : Mc ≤ Subgroup.normalizer (VZ T Mc : Set G) := le_normalizer_VZ T Mc
  have hUab : IsElemAbelian 2 (VZ T M) := isElemAbelian_VZ hq hM.1.1
  have hVU : V154 T Mc M ≤ VZ T M := V154_le_VZ T Mc M
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ quasithinOmegaOneCenter T ⊓ V154 T Mc M, z₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : V154 T Mc M ≤ ⊥ := by
      rw [hgen]
      refine conjClosure_le fun h _ z hz => ?_
      rw [hcon z hz]
      simp
    have hbot : V154 T Mc M = ⊥ := le_bot_iff.mp hle
    rw [hbot, Subgroup.card_bot] at hcard16
    omega
  have hKV_card : Nat.card (VZ T Mc ⊓ V154 T Mc M : Subgroup G) ≤ 2 :=
    card_le_two_of_central_of_extraspecial_s3 hDY hD φ hφs hφk (inf_le_right.trans hVY)
      (fun k hk y hy => hcent k hk.1 y hy)
  have hz₀KV : z₀ ∈ VZ T Mc ⊓ V154 T Mc M := ⟨hZK hz₀.1, hz₀.2⟩
  have hKV : ∀ x ∈ VZ T Mc ⊓ V154 T Mc M, x = 1 ∨ x = z₀ :=
    fun x hx => eq_one_or_eq_of_card_le_two hKV_card hz₀KV hz₀1 hx
  have hfix : ∀ n ∈ M ⊓ Mc, n * z₀ * n⁻¹ = z₀ := by
    intro n hn
    have hmem : n * z₀ * n⁻¹ ∈ VZ T Mc ⊓ V154 T Mc M :=
      ⟨(Subgroup.mem_normalizer_iff.mp (hNK hn.2) z₀).mp (hZK hz₀.1),
        (Subgroup.mem_normalizer_iff.mp (hNV hn.1) z₀).mp hz₀.2⟩
    rcases hKV _ hmem with h1 | h1
    · exfalso
      apply hz₀1
      have : z₀ = n⁻¹ * (n * z₀ * n⁻¹) * n := by group
      rw [this, h1]
      group
    · exact h1
  let N' : Subgroup ↥M := (M ⊓ Mc).subgroupOf M
  have hN'idx : N'.index = 3 := hidx
  let f : ↥M ⧸ N' → G := Quotient.lift (fun m : ↥M => (m : G) * z₀ * (m : G)⁻¹) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ N' := QuotientGroup.leftRel_apply.mp hab
    have hn : ((a⁻¹ * b : ↥M) : G) ∈ M ⊓ Mc := Subgroup.mem_subgroupOf.mp hab'
    have h1 := hfix _ hn
    have hb : (b : G) = (a : G) * ((a⁻¹ * b : ↥M) : G) := by simp
    show (a : G) * z₀ * (a : G)⁻¹ = (b : G) * z₀ * (b : G)⁻¹
    rw [hb]
    calc (a : G) * z₀ * (a : G)⁻¹
        = (a : G) * (((a⁻¹ * b : ↥M) : G) * z₀ * ((a⁻¹ * b : ↥M) : G)⁻¹) * (a : G)⁻¹ := by rw [h1]
      _ = (a : G) * ((a⁻¹ * b : ↥M) : G) * z₀ * ((a : G) * ((a⁻¹ * b : ↥M) : G))⁻¹ := by group)
  have : Fintype (↥M ⧸ N') := Fintype.ofFinite _
  let S : Finset G := Finset.univ.image f
  have hS_card : S.card ≤ 3 := by
    calc S.card ≤ (Finset.univ : Finset (↥M ⧸ N')).card := Finset.card_image_le
      _ = Fintype.card (↥M ⧸ N') := Finset.card_univ
      _ = N'.index := by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
      _ = 3 := hN'idx
  have hSmem : ∀ m ∈ M, m * z₀ * m⁻¹ ∈ S := fun m hm =>
    Finset.mem_image.mpr ⟨(QuotientGroup.mk ⟨m, hm⟩ : ↥M ⧸ N'), Finset.mem_univ _, rfl⟩
  have hSsub : ∀ s ∈ S, ∃ m ∈ M, s = m * z₀ * m⁻¹ := by
    intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨m, m.2, rfl⟩
  have hSV : ∀ s ∈ S, s ∈ V154 T Mc M := by
    intro s hs
    obtain ⟨m, hm, rfl⟩ := hSsub s hs
    exact (Subgroup.mem_normalizer_iff.mp (hNV hm) z₀).mp hz₀.2
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb =>
    comm_of_isElemAbelian hUab (hVU (hSV a ha)) (hVU (hSV b hb))
  have hSsq : ∀ a ∈ S, a ^ 2 = 1 := fun a ha => hUab.2 a (hVU (hSV a ha))
  have hclos := CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.card_closure_le_two_pow S hScomm
    hSsq
  have hVle : V154 T Mc M ≤ Subgroup.closure (S : Set G) := by
    calc V154 T Mc M = conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) (m0Of T Mc M) := hgen
      _ ≤ Subgroup.closure (S : Set G) := by
        refine conjClosure_le fun h hh z hz => ?_
        rcases hKV z ⟨hZK hz.1, hz.2⟩ with rfl | rfl
        · simp
        · exact Subgroup.subset_closure (by exact_mod_cast hSmem h (hM0 hh))
  have h8 : Nat.card (V154 T Mc M) ≤ 8 := by
    calc Nat.card (V154 T Mc M) ≤ Nat.card (Subgroup.closure (S : Set G)) :=
          Subgroup.card_le_of_le hVle
      _ ≤ 2 ^ S.card := hclos
      _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hS_card
      _ = 8 := by norm_num
  omega

theorem card_Z_and_le_centralizer (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h19 : Lemma1519Concl T Mc M) (hH : IsHStar T M H) (hB : ¬ Case1512Six T Mc M)
    (hDY : D ≤ conjClosure (V154 T Mc M) H) (hD : E2.IsExtraspecialPlus 2 D)
    (φ : ↥(conjClosure (V154 T Mc M) H) →* Equiv.Perm (Fin 3)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = D.subgroupOf (conjClosure (V154 T Mc M) H)) :
    Nat.card (quasithinOmegaOneCenter T) = 2 ∧
      Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  classical
  have hcent := vc_centralizes hq hM h19 hH
  have hOrd : OrdLE T Mc M := h19.two.2 Mc hq.inM_mc
  have hVcU : VZ T Mc ≤ VZ T M := VZ_le_of_ordLE hOrd
  have hVeq : V154 T Mc M = VZ T M := V154_eq_VZ hB
  have hKY : VZ T Mc ≤ conjClosure (V154 T Mc M) H := by
    refine hVcU.trans ?_
    rw [← hVeq]
    exact le_conjClosure _ _
  have hcard : Nat.card (VZ T Mc) ≤ 2 :=
    card_le_two_of_central_of_extraspecial_s3 hDY hD φ hφs hφk hKY
      (fun k hk y hy => hcent k hk y hy)
  have hZK : quasithinOmegaOneCenter T ≤ VZ T Mc := le_conjClosure _ Mc
  have hZne : quasithinOmegaOneCenter T ≠ ⊥ := hq.omegaOneCenter_ne_bot
  have hZgt : 1 < Nat.card (quasithinOmegaOneCenter T) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZne
  have hZle : Nat.card (quasithinOmegaOneCenter T) ≤ Nat.card (VZ T Mc) :=
    Subgroup.card_le_of_le hZK
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := by omega
  have hZeq : quasithinOmegaOneCenter T = VZ T Mc :=
    Subgroup.eq_of_le_of_card_ge hZK (by omega)
  refine ⟨hZ2, fun g hg => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  by_cases hz1 : z = 1
  · simp [hz1]
  have hgn : g ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    rw [hZeq]
    exact le_normalizer_VZ T Mc hg
  have hmem : g * z * g⁻¹ ∈ quasithinOmegaOneCenter T :=
    (Subgroup.mem_normalizer_iff.mp hgn z).mp hz
  have hne : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h]
    group
  rcases eq_one_or_eq_of_card_le_two hZ2.le hz hz1 hmem with h | h
  · exact absurd h hne
  · exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem rigid_facts (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h19 : Lemma1519Concl T Mc M) (h15 : Lemma1515Concl T Mc M) (hH : IsHStar T M H)
    (hDY : D ≤ conjClosure (V154 T Mc M) H) (hD : E2.IsExtraspecialPlus 2 D)
    (φ : ↥(conjClosure (V154 T Mc M) H) →* Equiv.Perm (Fin 3)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = D.subgroupOf (conjClosure (V154 T Mc M) H)) :
    ¬ Case1512Six T Mc M ∧ Nat.card (quasithinOmegaOneCenter T) = 2 ∧
      Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hB := not_case1512Six hq hM h19 h15 hH hDY hD φ hφs hφk
  exact ⟨hB, card_Z_and_le_centralizer hq hM h19 hH hB hDY hD φ hφs hφk⟩

end He13

end CFSG.Quasithin
