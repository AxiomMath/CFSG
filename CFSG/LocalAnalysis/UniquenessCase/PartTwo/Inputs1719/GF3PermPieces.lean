module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Witness
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PlaneAbstract
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

private def permPiece (U K : Subgroup G) : Subgroup G :=
  K ⊓ Subgroup.normalizer ((U ⊓ K : Subgroup G) : Set G)

private def permPieceBase (U K : Subgroup G) : Subgroup G :=
  U ⊓ K

private theorem permPieceBase_le_permPiece (U K : Subgroup G) :
    permPieceBase U K ≤ permPiece U K :=
  le_inf inf_le_right (Subgroup.le_normalizer (H := U ⊓ K))

variable [Finite G]

theorem permWitnessAt_of_commuting_pieces (U : Sylow 2 G)
    (𝓕 : Set (Subgroup G))
    (hinv : ∀ φ : MulAut G, (U : Subgroup G).map φ.toMonoidHom = U →
      ∀ K ∈ 𝓕, K.map φ.toMonoidHom ∈ 𝓕)
    (hcomm : ∀ K ∈ 𝓕, ∀ K' ∈ 𝓕, K ≠ K' → ∀ x ∈ K, ∀ y ∈ K', x * y = y * x)
    (hcube : ∀ K ∈ 𝓕, ∀ x ∈ K ⊓ normalizer (((U : Subgroup G) ⊓ K : Subgroup G) : Set G),
      x ^ 3 ∈ (U : Subgroup G) ⊓ K)
    (hab : ∀ K ∈ 𝓕, ∀ x ∈ K ⊓ normalizer (((U : Subgroup G) ⊓ K : Subgroup G) : Set G),
      ∀ y ∈ K ⊓ normalizer (((U : Subgroup G) ⊓ K : Subgroup G) : Set G),
        x * y * x⁻¹ * y⁻¹ ∈ (U : Subgroup G) ⊓ K)
    (hZ2 : ∀ K ∈ 𝓕, ∀ c ∈ K, (∀ y ∈ K, c * y = y * c) → c * c = 1)
    (htwo : ∃ K₁ ∈ 𝓕, ∃ K₂ ∈ 𝓕, K₁ ≠ K₂ ∧
      (∃ a ∈ K₁ ⊓ normalizer (((U : Subgroup G) ⊓ K₁ : Subgroup G) : Set G), orderOf a = 3) ∧
      (∃ b ∈ K₂ ⊓ normalizer (((U : Subgroup G) ⊓ K₂ : Subgroup G) : Set G), orderOf b = 3)) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.PermWitnessAt G (U : Subgroup G) := by
  classical
  let 𝓕s := {K : Subgroup G // K ∈ 𝓕}
  set P : 𝓕s → Subgroup G := fun K => permPiece (U : Subgroup G) K.1 with hP
  set V : 𝓕s → Subgroup G := fun K => permPieceBase (U : Subgroup G) K.1 with hV
  set X : Subgroup G := ⨆ K : 𝓕s, P K with hX
  set R : Subgroup G := ⨆ K : 𝓕s, V K with hR
  have hVU : ∀ K : 𝓕s, V K ≤ (U : Subgroup G) := fun K => inf_le_left
  have hRU : R ≤ (U : Subgroup G) := by rw [hR]; exact iSup_le hVU
  have hR2 : IsPGroup 2 R := U.isPGroup'.to_le hRU
  have hPX : ∀ K : 𝓕s, P K ≤ X := fun K => by
    rw [hX]
    exact le_iSup P K
  have hVX : ∀ K : 𝓕s, V K ≤ X := fun K =>
    (permPieceBase_le_permPiece (U : Subgroup G) K.1).trans (hPX K)
  have hRX : R ≤ X := by rw [hR]; exact iSup_le hVX
  have hP_normalizer : ∀ K : 𝓕s, P K ≤ ⨅ L : 𝓕s,
      Subgroup.normalizer ((V L : Subgroup G) : Set G) := by
    intro K
    refine le_iInf fun L => ?_
    by_cases hKL : K = L
    · subst hKL
      have hPK : P K = permPiece (U : Subgroup G) K.1 := by rw [hP]
      rw [hPK]
      exact inf_le_right
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (V L : Set G))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxP : x ∈ P K := hx
      rw [hP] at hxP
      have hyV : y ∈ V L := hy
      rw [hV] at hyV
      exact (hcomm K.1 K.2 L.1 L.2 (fun h => hKL (Subtype.ext h)) x hxP.1
        y hyV.2).symm
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := by
    rw [hX]
    refine iSup_le fun K => (hP_normalizer K).trans ?_
    rw [hR]
    exact Subgroup.iInf_normalizer_le_normalizer_iSup V
  let R' : Subgroup X := R.subgroupOf X
  have hR'normal : R'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXR
  let Γ := X ⧸ R'
  let π : X →* Γ := QuotientGroup.mk' R'
  set S : 𝓕s → Subgroup Γ := fun K => ((P K).subgroupOf X).map π with hS
  have hS3 : ∀ z ∈ ⋃ K : 𝓕s, (S K : Set Γ), z ^ 3 = 1 := by
    intro z hz
    obtain ⟨K, hzK⟩ := Set.mem_iUnion.mp hz
    obtain ⟨x, hxS, rfl⟩ := Subgroup.mem_map.mp hzK
    have hxP : x.1 ∈ permPiece (U : Subgroup G) K.1 := Subgroup.mem_subgroupOf.mp hxS
    have hx3 : x.1 ^ 3 ∈ V K := hcube K.1 K.2 x.1 hxP
    have hx3R : x.1 ^ 3 ∈ R := le_iSup V K hx3
    have hmemR' : x ^ 3 ∈ R' := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      show x.1 ^ 3 ∈ R
      exact hx3R
    have hπ3 : π (x ^ 3) = 1 := (QuotientGroup.eq_one_iff _).mpr hmemR'
    calc (π x) ^ 3 = π (x ^ 3) := (map_pow π x 3).symm
      _ = 1 := hπ3
  have hScomm : (⋃ K : 𝓕s, (S K : Set Γ)).Pairwise Commute := by
    intro a ha b hb hneπ
    obtain ⟨K, haK⟩ := Set.mem_iUnion.mp ha
    obtain ⟨L, hbL⟩ := Set.mem_iUnion.mp hb
    obtain ⟨x, hxS, rfl⟩ := Subgroup.mem_map.mp haK
    obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp hbL
    have hxP : x.1 ∈ permPiece (U : Subgroup G) K.1 := Subgroup.mem_subgroupOf.mp hxS
    have hyP : y.1 ∈ permPiece (U : Subgroup G) L.1 := Subgroup.mem_subgroupOf.mp hyS
    by_cases hKL : K = L
    · subst hKL
      have hcommG : x.1 * y.1 * x.1⁻¹ * y.1⁻¹ ∈ V K := hab K.1 K.2 x.1 hxP y.1 hyP
      have hcommR : x.1 * y.1 * x.1⁻¹ * y.1⁻¹ ∈ R := le_iSup V K hcommG
      have hmemR' : x * y * x⁻¹ * y⁻¹ ∈ R' := by
        refine Subgroup.mem_subgroupOf.mpr ?_
        show x.1 * y.1 * x.1⁻¹ * y.1⁻¹ ∈ R
        exact hcommR
      have hπ : π (x * y * x⁻¹ * y⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hmemR'
      have h1 : π x * π y * (π x)⁻¹ * (π y)⁻¹ = 1 := by
        simpa only [map_mul, map_inv] using hπ
      have h2 : π x * π y = π y * π x := by
        have h3 : (π x * π y * (π x)⁻¹ * (π y)⁻¹) * (π y * π x) = π x * π y := by
          group
        rw [h1, one_mul] at h3
        exact h3.symm
      exact h2
    · have hcommG : x.1 * y.1 = y.1 * x.1 :=
        hcomm K.1 K.2 L.1 L.2 (fun h => hKL (Subtype.ext h)) x.1 hxP.1 y.1 hyP.1
      have h2 : π x * π y = π y * π x := by
        rw [← map_mul, ← map_mul]
        exact congrArg π (Subtype.ext hcommG)
      exact h2
  set Q : Subgroup Γ := Subgroup.closure (⋃ K : 𝓕s, (S K : Set Γ)) with hQ
  have hQc : IsMulCommutative Q := by
    rw [hQ]
    exact Subgroup.isMulCommutative_closure hScomm
  have hQ3 : ∀ z ∈ Q, z ^ 3 = 1 := by
    rw [hQ]
    intro z hz
    exact CFSG.AGLEmbeddingD2.AltFiveRankTools.pow_eq_one_of_mem_closure_of_pairwise_commute
      hScomm hS3 hz
  have hXmap : ∀ (x : G) (hx : x ∈ X), π ⟨x, hx⟩ ∈ Q := by
    have hclosure : X = Subgroup.closure (⋃ K : 𝓕s, (P K : Set G)) := by
      rw [hX, Subgroup.iSup_eq_closure]
    have hmain : ∀ x : G, x ∈ Subgroup.closure (⋃ K : 𝓕s, (P K : Set G)) →
        x ∈ X ∧ ∀ hx : x ∈ X, π ⟨x, hx⟩ ∈ Q := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ =>
        x ∈ X ∧ ∀ hx : x ∈ X, π ⟨x, hx⟩ ∈ Q) ?_ ?_ ?_ ?_ hx
      · intro y hy
        obtain ⟨K, hyK⟩ := Set.mem_iUnion.mp hy
        have hyX : y ∈ X := hPX K hyK
        refine ⟨hyX, fun hyX' => ?_⟩
        have hyS : (⟨y, hyX'⟩ : X) ∈ (P K).subgroupOf X :=
          Subgroup.mem_subgroupOf.mpr hyK
        exact Subgroup.subset_closure
          (Set.mem_iUnion.mpr ⟨K, Subgroup.mem_map_of_mem π hyS⟩)
      · refine ⟨Subgroup.one_mem X, fun h1 => ?_⟩
        have h : π (⟨1, h1⟩ : X) = 1 := by
          rw [show (⟨1, h1⟩ : X) = 1 from Subtype.ext rfl, map_one]
        rw [h]
        exact Q.one_mem
      · intro a b ha hb haQ hbQ
        refine ⟨X.mul_mem haQ.1 hbQ.1, fun hab => ?_⟩
        have haQ' : π ⟨a, haQ.1⟩ ∈ Q := haQ.2 haQ.1
        have hbQ' : π ⟨b, hbQ.1⟩ ∈ Q := hbQ.2 hbQ.1
        rw [show (⟨a * b, hab⟩ : X) = ⟨a, haQ.1⟩ * ⟨b, hbQ.1⟩ from Subtype.ext rfl, map_mul]
        exact Q.mul_mem haQ' hbQ'
      · intro a ha haQ
        refine ⟨X.inv_mem haQ.1, fun ha' => ?_⟩
        have haQ' : π ⟨a, haQ.1⟩ ∈ Q := haQ.2 haQ.1
        rw [show (⟨a⁻¹, ha'⟩ : X) = (⟨a, haQ.1⟩ : X)⁻¹ from Subtype.ext rfl, map_inv]
        exact Q.inv_mem haQ'
    intro x hx
    have hx' : x ∈ Subgroup.closure (⋃ K : 𝓕s, (P K : Set G)) := by
      rw [← hclosure]
      exact hx
    exact (hmain x hx').2 hx
  have hcubeX : ∀ x ∈ X, x ^ 3 ∈ R := by
    intro x hx
    have hxQ : π ⟨x, hx⟩ ∈ Q := hXmap x hx
    have h3 : (π ⟨x, hx⟩) ^ 3 = 1 := hQ3 _ hxQ
    have hπ3 : π (⟨x ^ 3, X.pow_mem hx 3⟩ : X) = 1 := by
      rw [show (⟨x ^ 3, X.pow_mem hx 3⟩ : X) = (⟨x, hx⟩ : X) ^ 3 from Subtype.ext rfl,
        map_pow, h3]
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hπ3)
  have hcommX : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ R := by
    intro x hx y hy
    have hxQ : π ⟨x, hx⟩ ∈ Q := hXmap x hx
    have hyQ : π ⟨y, hy⟩ ∈ Q := hXmap y hy
    have : IsMulCommutative Q := hQc
    have hcQ : Commute (⟨π ⟨x, hx⟩, hxQ⟩ : Q) ⟨π ⟨y, hy⟩, hyQ⟩ :=
      IsMulCommutative.is_comm.comm _ _
    have hc : Commute (π ⟨x, hx⟩) (π ⟨y, hy⟩) := by
      show π ⟨x, hx⟩ * π ⟨y, hy⟩ = π ⟨y, hy⟩ * π ⟨x, hx⟩
      simpa using congrArg Subtype.val hcQ
    have h1 : π ⟨x, hx⟩ * π ⟨y, hy⟩ * (π ⟨x, hx⟩)⁻¹ * (π ⟨y, hy⟩)⁻¹ = 1 := by
      rw [hc.mul_inv_cancel, mul_inv_cancel]
    have hmemX : x * y * x⁻¹ * y⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)
    have hπ : π (⟨x * y * x⁻¹ * y⁻¹, hmemX⟩ : X) = 1 := by
      rw [show (⟨x * y * x⁻¹ * y⁻¹, hmemX⟩ : X) =
        ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : X)⁻¹ * (⟨y, hy⟩ : X)⁻¹ from Subtype.ext rfl]
      simp only [map_mul, map_inv]
      exact h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hπ)
  have hfix : ∀ φ : MulAut G, (U : Subgroup G).map φ.toMonoidHom = U →
      X.map φ.toMonoidHom = X := by
    intro φ hφ
    have hφsym : (U : Subgroup G).map φ.symm.toMonoidHom = U := by
      have hcomp : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
        ext z
        simp
      have h := congrArg (fun H : Subgroup G => H.map φ.symm.toMonoidHom) hφ
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
      exact h.symm
    have hmapP : ∀ K : 𝓕s, (P K).map φ.toMonoidHom =
        P ⟨K.1.map φ.toMonoidHom, hinv φ hφ K.1 K.2⟩ := by
      intro K
      rw [hP]
      simp only [permPiece]
      rw [Subgroup.map_inf K.1
          (Subgroup.normalizer ((U ⊓ K.1 : Subgroup G) : Set G))
          φ.toMonoidHom φ.injective,
        Subgroup.map_equiv_normalizer_eq (U ⊓ K.1 : Subgroup G) φ,
        Subgroup.map_inf (U : Subgroup G) K.1 φ.toMonoidHom φ.injective, hφ]
    have hreindex : (⨆ K : 𝓕s,
          P ⟨K.1.map φ.toMonoidHom, hinv φ hφ K.1 K.2⟩) = ⨆ K : 𝓕s, P K := by
      apply le_antisymm
      · exact iSup_le fun K => le_iSup P ⟨K.1.map φ.toMonoidHom, hinv φ hφ K.1 K.2⟩
      · refine iSup_le fun L => ?_
        let K : 𝓕s := ⟨L.1.map φ.symm.toMonoidHom, hinv φ.symm hφsym L.1 L.2⟩
        have hLK : (⟨K.1.map φ.toMonoidHom, hinv φ hφ K.1 K.2⟩ : 𝓕s) = L := by
          apply Subtype.ext
          show (L.1.map φ.symm.toMonoidHom).map φ.toMonoidHom = L.1
          rw [Subgroup.map_map]
          have hcomp : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G := by
            ext z
            simp
          rw [hcomp, Subgroup.map_id]
        rw [← hLK]
        exact le_iSup (fun K : 𝓕s =>
          P ⟨K.1.map φ.toMonoidHom, hinv φ hφ K.1 K.2⟩) K
    calc X.map φ.toMonoidHom = (⨆ K : 𝓕s, P K).map φ.toMonoidHom := by rw [hX]
      _ = ⨆ K : 𝓕s, (P K).map φ.toMonoidHom := Subgroup.map_iSup φ.toMonoidHom P
      _ = ⨆ K : 𝓕s, P ⟨K.1.map φ.toMonoidHom, hinv φ hφ K.1 K.2⟩ :=
        iSup_congr fun K => hmapP K
      _ = X := by rw [hreindex, hX]
  obtain ⟨K₁, hK₁, K₂, hK₂, hne, ⟨a, ha, hao⟩, ⟨b, hb, hbo⟩⟩ := htwo
  have haP : a ∈ permPiece (U : Subgroup G) K₁ := ha
  have hbP : b ∈ permPiece (U : Subgroup G) K₂ := hb
  have haK : a ∈ K₁ := haP.1
  have hbK : b ∈ K₂ := hbP.1
  have haX : a ∈ X := hPX ⟨K₁, hK₁⟩ haP
  have hbX : b ∈ X := hPX ⟨K₂, hK₂⟩ hbP
  have hb_not_mem : b ∉ Subgroup.zpowers a := by
    intro hbza
    have hbK₁ : b ∈ K₁ := (Subgroup.zpowers_le.mpr haK) hbza
    have hbcent : ∀ y ∈ K₂, b * y = y * b := fun y hy =>
      hcomm K₁ hK₁ K₂ hK₂ hne b hbK₁ y hy
    have hbb : b * b = 1 := hZ2 K₂ hK₂ b hbK hbcent
    have hdvd : orderOf b ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using hbb
    rw [hbo] at hdvd
    norm_num at hdvd
  let E : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have hE9 : Nat.card E = 9 := by
    have hcommab : Commute a b := hcomm K₁ hK₁ K₂ hK₂ hne a haK b hbK
    obtain ⟨E₀, haE₀, hbE₀, -, hE₀card, hE₀min⟩ :=
      CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.exists_plane_of_commute
        (p := 3) hao hbo hcommab hb_not_mem
    have hEq : E₀ = E := by
      refine le_antisymm
        (hE₀min _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))) ?_
      exact sup_le (Subgroup.zpowers_le.mpr haE₀) (Subgroup.zpowers_le.mpr hbE₀)
    rw [← hEq, hE₀card]
    norm_num
  have hEX : E ≤ X := sup_le (Subgroup.zpowers_le.mpr haX) (Subgroup.zpowers_le.mpr hbX)
  have hER : E ≤ Subgroup.normalizer (R : Set G) := hEX.trans hXR
  obtain ⟨n, hn⟩ := hR2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card E) (Nat.card R) := by
    rw [show Nat.card E = 9 from hE9, hn]
    exact Nat.Coprime.pow (k := 3) (l := 2) 2 n (by norm_num)
  have hdisj : E ⊓ R = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hcard :=
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.card_sup_mul_card_inf_of_le_normalizer
      (G := G) (L := R) (E := E) hER
  rw [sup_comm, inf_comm, mul_comm (Nat.card R), hdisj, Subgroup.card_bot,
    show Nat.card E = 9 from hE9, mul_one] at hcard
  have hcardX : 9 * Nat.card R ≤ Nat.card X := by
    have hle : E ⊔ R ≤ X := sup_le hEX hRX
    have := Subgroup.card_le_of_le hle
    omega
  exact ⟨X, R, hfix, hRU, hRX, hXR, hR2, hcubeX, hcommX, hcardX⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3
