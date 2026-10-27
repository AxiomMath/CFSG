module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQAux

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem beta_apply {G : Type} [Group G] {K : Type} [Field K]
    {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hβ_eq : ∀ b : Bs, β b =
      (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b)))
    (b : Bs) (l : L) :
    β b (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
      θ (QuotientGroup.mk' (Subgroup.center L) ⟨(b : G) * l * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hNL b.2) (l : G)).mp l.2⟩) := by
  classical
  rw [hβ_eq b, e6QTwoMulAutCongrApply, e6QTwoQuotCenterAutHom_mk]
  exact congrArg θ (congrArg (QuotientGroup.mk' (Subgroup.center L))
    (Subtype.ext (e6QTwoBstarConjAction_apply hNL b l)))

private theorem beta_ker_eq {G : Type} [Group G] {K : Type} [Field K]
    {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hperf : commutator ↥L = ⊤)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hβ_eq : ∀ b : Bs, β b =
      (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b))) :
    β.ker = (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
  classical
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hb
    rw [hβ_eq b] at hb
    have hφ1 : e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b) = 1 :=
      (MulAut.congr θ).injective (by rw [hb]; exact (map_one (MulAut.congr θ)).symm)
    have h2 : e6QTwoBstarConjAction hNL b = 1 :=
      e6QTwoQuotCenterAutHom_injective hperf (by rw [hφ1, map_one])
    exact ⟨b.2, (e6QTwoBstarConjAction_eq_one_iff hNL b).mp h2⟩
  · rintro ⟨-, hbC⟩
    have h1 : e6QTwoBstarConjAction hNL b = 1 :=
      (e6QTwoBstarConjAction_eq_one_iff hNL b).mpr hbC
    have h2 : e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b) = 1 := by
      rw [h1, map_one]
    rw [hβ_eq b, h2, map_one]

private theorem beta_card_ker {G : Type} [Group G] {K : Type} [Field K]
    {Bs L : Subgroup G} {x : G}
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hβ_ker : β.ker = (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hx : x ∈ Bs) (hx1 : x ≠ 1) (hBs : IsElemAbelian 3 Bs) :
    Nat.card β.ker = 3 := by
  classical
  rw [hβ_ker]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ Bs)).toEquiv]
  rw [hBL, Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hx) hx1]

private theorem beta_card_range {G : Type} [Group G] {K : Type} [Field K]
    {Bs : Subgroup G}
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hcardKer : Nat.card β.ker = 3) (hcard : Nat.card Bs = 3 ^ 5) :
    Nat.card β.range = 3 ^ 4 := by
  classical
  have hk := Subgroup.card_ker_mul_card_range β
  rw [hcardKer, hcard] at hk
  norm_num at hk ⊢
  omega

private theorem beta_isElemAbelian {G : Type} [Group G] {K : Type} [Field K]
    {Bs : Subgroup G}
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hBs : IsElemAbelian 3 Bs) : IsElemAbelian 3 β.range := by
  classical
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨a', ha'⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨b', hb'⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha', ← hb', ← map_mul, ← map_mul, hBs.1.is_comm.comm a' b']
  · obtain ⟨b', hb'⟩ := MonoidHom.mem_range.mp ha
    rw [← hb', ← map_pow]
    have hb3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hBs.2 (b' : G) b'.2)
    rw [hb3, map_one]

private theorem beta_mem_matConjImage {G : Type} [Group G] {K : Type} [Field K]
    {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hβ_apply : ∀ (b : Bs) (l : L),
      β b (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
        θ (QuotientGroup.mk' (Subgroup.center L) ⟨(b : G) * l * (b : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hNL b.2) (l : G)).mp l.2⟩))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (b : Bs) :
    β b ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenGUSet (Fin 6) K (2 ^ 1)) := by
  classical
  obtain ⟨ψ, hψ, hψind⟩ := hI (b : G)⁻¹ (inv_mem b.2)
  have hβind : LargeEvenInduces θ
      (fun l l' : L => (l' : G) = (b : G) * l * (b : G)⁻¹) (β b) := by
    intro l l' hl'
    have hsub : (⟨(b : G) * (l : G) * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hNL b.2) (l : G)).mp l.2⟩ : L) = l' := by
      apply Subtype.ext
      simpa using hl'.symm
    rw [← hsub]
    exact hβ_apply b l
  have hrel : ∀ l : L, ∃ l' : L, (l' : G) = (b : G) * l * (b : G)⁻¹ := fun l =>
    ⟨⟨_, (Subgroup.mem_normalizer_iff.mp (hNL b.2) (l : G)).mp l.2⟩, rfl⟩
  have hψβ : ψ = β b := by
    apply e6QTwoLargeEvenInducesEqOfForallExists hrel
    · intro l l' hl'
      exact hψind l l' (by rw [inv_inv]; exact hl')
    · exact hβind
  rwa [hψβ] at hψ

private theorem beta_range_le_inndiag {G : Type} [Group G] {K : Type} [Field K]
    [Finite K]
    (hK : Nat.card K = 4) {Bs : Subgroup G}
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hK' : Nat.card K = (2 ^ 1) ^ 2)
    (hβmem : ∀ b : Bs, β b ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenGUSet (Fin 6) K (2 ^ 1))) :
    β.range ≤ InndiagSU.inndiagU (USixTwo.fieldDataFour hK) (by norm_num : 1 ≤ 6) := by
  classical
  rintro φ' ⟨b, rfl⟩
  rw [InndiagSU.mem_inndiagU]
  exact InndiagSU.congr_mem_primeFormD (USixTwo.fieldDataFour hK) (by norm_num : 1 ≤ 6)
    hK' (hβmem b)

private theorem exists_frame_of_beta {G : Type} [Group G] {K : Type} [Field K]
    [Finite K]
    (hK : Nat.card K = 4) {Bs : Subgroup G}
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hK' : Nat.card K = (2 ^ 1) ^ 2)
    (hEea : IsElemAbelian 3 β.range)
    (hEin : β.range ≤ InndiagSU.inndiagU (USixTwo.fieldDataFour hK) (by norm_num : 1 ≤ 6))
    (hEcard : Nat.card β.range = 3 ^ 4) :
    ∃ (Q : GL (Fin 6) K) (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
        (RankThree.PartOne.KCUnitaryModel.idGram K 6)),
      ∀ e ∈ β.range, ∃ σ : Fin 6 → Kˣ, σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
          TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ := by
  classical
  obtain ⟨Q, hQ, hQfr⟩ := TableBUD.exists_frame_inndiag (h := USixTwo.fieldDataFour hK) hK'
    (by norm_num : 3 ≤ 6) (by norm_num : (6, 2 ^ 1) ≠ (3, 2))
    (by norm_num : ¬(6 = 3 ∧ 2 ^ 1 = 2)) (by norm_num : Nat.Prime 3)
    (by norm_num : 3 ∣ 2 ^ 1 + 1) hEea hEin (by rw [hEcard]; norm_num)
  exact ⟨Q, hQ, hQfr⟩

private theorem bstarConjAction_isPGroup {G : Type} [Group G]
    {Bs L : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    IsPGroup 3 (e6QTwoBstarConjAction hNL).range := by
  classical
  rintro ⟨x, hx⟩
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨k, hk⟩ := hBs.isPGroup b
  refine ⟨k, ?_⟩
  apply Subtype.ext
  show x ^ 3 ^ k = 1
  rw [← hb, ← map_pow, hk, map_one]

private theorem frame_act_commute {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {Bs : Subgroup G}
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (σ : e6QTwoTorParamSubgroup (K := K))
    (hnormσ : ∀ k, ((σ.1 k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1)
    (hQfr : ∀ e ∈ β.range, ∃ σ' : Fin 6 → Kˣ, σ' ⟨0, by omega⟩ = 1 ∧
      (∀ k, σ' k ^ 3 = 1) ∧ (∀ k, ((σ' k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ')
    (b : Bs) :
    β b * MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ) =
      MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ) * β b := by
  classical
  obtain ⟨σe, _, _, hσen, hefr⟩ := hQfr (β b) ⟨b, rfl⟩
  refine e6QTwoFrameActMulComm hefr (e6QTwoFrameActFrameTorusHom hK Q hQ σ) hσen hnormσ ?_
  funext k
  rw [Pi.mul_apply, Pi.mul_apply, mul_comm]

private theorem frame_torus_fixed {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hperf : commutator ↥L = ⊤)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hβ_eq : ∀ b : Bs, β b =
      (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b)))
    (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (hQfr : ∀ e ∈ β.range, ∃ σ' : Fin 6 → Kˣ, σ' ⟨0, by omega⟩ = 1 ∧
      (∀ k, σ' k ^ 3 = 1) ∧ (∀ k, ((σ' k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ')
    (σ : e6QTwoTorParamSubgroup (K := K)) :
    ∀ a ∈ (e6QTwoBstarConjAction hNL).range,
      e6QTwoQuotCenterAutHom L a (θ.symm (e6QTwoFrameTorusHom hK Q hQ σ)) =
        θ.symm (e6QTwoFrameTorusHom hK Q hQ σ) := by
  classical
  set r : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    e6QTwoFrameTorusHom hK Q hQ σ
  set q : L ⧸ Subgroup.center L := θ.symm r
  have hθq : θ q = r := θ.apply_symm_apply r
  obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
  have hnormσ : ∀ k, ((σ.1 k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
    intro k
    rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val,
      USixTwo.cube_unit_eq_one hK, Units.val_one]
  intro a ha
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
  have hcommAut := frame_act_commute hK Q hQ σ hnormσ hQfr b
  have hcommL : e6QTwoBstarConjAction hNL b * MulAut.conj l₀ =
      MulAut.conj l₀ * e6QTwoBstarConjAction hNL b := by
    apply e6QTwoQuotCenterAutHom_injective hperf
    have h2 : (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b) *
        MulAut.conj (QuotientGroup.mk' (Subgroup.center L) l₀)) =
        (MulAut.congr θ) (MulAut.conj (QuotientGroup.mk' (Subgroup.center L) l₀) *
          e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b)) := by
      rw [map_mul, map_mul,
        ← e6QTwoMulAutConjCongr θ (QuotientGroup.mk' (Subgroup.center L) l₀), hl₀, hθq,
        ← hβ_eq b]
      exact hcommAut
    rw [map_mul, map_mul, e6QTwoQuotCenterAutHom_conj]
    exact (MulAut.congr θ).injective h2
  have hconj := e6QTwoConjEqConjOfCommute hcommL
  have hmem : l₀ * ((e6QTwoBstarConjAction hNL b)⁻¹ l₀)⁻¹ ∈ Subgroup.center L :=
    e6QTwoMemCenterMulInvOfConjEq hconj
  have hmem' : e6QTwoBstarConjAction hNL b l₀ * l₀⁻¹ ∈ Subgroup.center L := by
    have h' : e6QTwoBstarConjAction hNL b
        (l₀ * ((e6QTwoBstarConjAction hNL b)⁻¹ l₀)⁻¹) ∈ Subgroup.center L := by
      have hmap : e6QTwoBstarConjAction hNL b
          (l₀ * ((e6QTwoBstarConjAction hNL b)⁻¹ l₀)⁻¹) ∈
          (Subgroup.center L).map ((e6QTwoBstarConjAction hNL b) : L →* L) :=
        Subgroup.mem_map_of_mem ((e6QTwoBstarConjAction hNL b) : L →* L) hmem
      rwa [e6QTwoCenterMapMulAut] at hmap
    rwa [map_mul, map_inv, MulAut.apply_inv_self] at h'
  have hmk : QuotientGroup.mk' (Subgroup.center L)
      (e6QTwoBstarConjAction hNL b l₀) = QuotientGroup.mk' (Subgroup.center L) l₀ :=
    e6QTwoMkEqMkOfMemCenter hmem'
  rw [← hl₀]
  exact (e6QTwoQuotCenterAutHom_mk (e6QTwoBstarConjAction hNL b) l₀).trans hmk

private theorem exists_cube_lift {G : Type} [Group G] [Finite G] {K : Type} [Field K]
    [Finite K]
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hA3 : IsPGroup 3 (e6QTwoBstarConjAction hNL).range)
    (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (σ : e6QTwoTorParamSubgroup (K := K))
    (hfixA : ∀ a ∈ (e6QTwoBstarConjAction hNL).range,
      e6QTwoQuotCenterAutHom L a (θ.symm (e6QTwoFrameTorusHom hK Q hQ σ)) =
        θ.symm (e6QTwoFrameTorusHom hK Q hQ σ)) :
    ∃ ℓ : L, (ℓ : G) ∈ Bs ⊓ L ∧
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) ℓ =
        e6QTwoFrameTorusHom hK Q hQ σ := by
  classical
  set r : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    e6QTwoFrameTorusHom hK Q hQ σ
  set q : L ⧸ Subgroup.center L := θ.symm r
  have hθq : θ q = r := θ.apply_symm_apply r
  have hq3 : q ^ 3 = 1 := by
    have hσ3 : σ ^ 3 = 1 := Subtype.ext (funext fun k => USixTwo.cube_unit_eq_one hK (σ.1 k))
    have hr3 : r ^ 3 = 1 := by
      rw [show r = e6QTwoFrameTorusHom hK Q hQ σ from rfl, ← map_pow, hσ3, map_one]
    apply θ.injective
    rw [map_pow, hθq, hr3, map_one]
  have hxb : q ∈ (⊤ : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L)) := by
    rw [Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective (Subgroup.center L))]
    exact Subgroup.mem_top q
  obtain ⟨ℓ, -, hℓq, hℓ3, hℓfix⟩ :=
    e6QTwoExistsFixedCubeLiftCenter hA3 hZ2 (H := ⊤) (fun a _ h _ => Subgroup.mem_top h)
      hxb hfixA hq3
  have hℓ3G : (ℓ : G) ^ 3 = 1 := by
    simpa using congrArg (fun z : L => (z : G)) hℓ3
  have hℓBs : (ℓ : G) ∈ Bs := by
    refine hstar (ℓ : G) ?_ hℓ3G
    rw [Subgroup.mem_centralizer_iff]
    intro g' hg'
    have h1 : e6QTwoBstarConjAction hNL ⟨g', hg'⟩ ℓ = ℓ :=
      hℓfix (e6QTwoBstarConjAction hNL ⟨g', hg'⟩) (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    have h2 : (g' : G) * (ℓ : G) * (g' : G)⁻¹ = (ℓ : G) := by
      rw [← e6QTwoBstarConjAction_apply hNL ⟨g', hg'⟩ ℓ, h1]
    calc g' * (ℓ : G) = ((g' : G) * (ℓ : G) * (g' : G)⁻¹) * g' := by group
      _ = (ℓ : G) * g' := by rw [h2]
  exact ⟨ℓ, ⟨hℓBs, ℓ.2⟩, (congrArg θ hℓq).trans hθq⟩

private theorem image_card_eq {G : Type} [Group G] {K : Type} [Field K]
    {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs) :
    Nat.card ↥(((Bs ⊓ L).subgroupOf L).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))) =
      Nat.card ↥(Bs ⊓ L) := by
  classical
  have hkerπ : (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker =
      Subgroup.center L := by
    ext y
    rw [MonoidHom.mem_ker]
    show θ (y : L ⧸ Subgroup.center L) = 1 ↔ y ∈ Subgroup.center L
    constructor
    · intro hy
      exact (QuotientGroup.eq_one_iff y).mp (θ.injective (by rw [hy, map_one]))
    · intro hy
      have h1 : (y : L ⧸ Subgroup.center L) = 1 := (QuotientGroup.eq_one_iff y).mpr hy
      rw [h1, map_one]
  have hinf : ((Bs ⊓ L).subgroupOf L) ⊓
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = ⊥ := by
    rw [hkerπ, Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyH, hyZ⟩ := Subgroup.mem_inf.mp hy
    rw [Subgroup.mem_subgroupOf] at hyH
    have hy3 : y ^ 3 = 1 := Subtype.ext (hBs.2 (y : G) hyH.1)
    obtain ⟨k, hk⟩ := hZ2 (⟨y, hyZ⟩ : Subgroup.center L)
    have hy2 : y ^ 2 ^ k = 1 := by
      have h' := congrArg (fun z : Subgroup.center L => (z : L)) hk
      simpa using h'
    exact e6QTwoEqOneOfPowThreeOfPowTwo hy3 hy2
  have hcard_sub : Nat.card ↥((Bs ⊓ L).subgroupOf L) = Nat.card ↥(Bs ⊓ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Bs ⊓ L ≤ L)).toEquiv
  have hcardmap : Nat.card ↥(((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))) =
      Nat.card ↥((Bs ⊓ L).subgroupOf L) :=
    card_map_eq_card_of_inf_ker_eq_bot _ hinf
  rw [hcardmap, hcard_sub]

private theorem frame_range_le_image {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (hlift : ∀ σ : e6QTwoTorParamSubgroup (K := K), ∃ ℓ : L, (ℓ : G) ∈ Bs ⊓ L ∧
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) ℓ =
        e6QTwoFrameTorusHom hK Q hQ σ) :
    (e6QTwoFrameTorusHom hK Q hQ).range ≤
      ((Bs ⊓ L).subgroupOf L).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) := by
  classical
  rintro y ⟨σ, rfl⟩
  obtain ⟨ℓ, hℓ, hℓπ⟩ := hlift σ
  exact Subgroup.mem_map.mpr ⟨ℓ, hℓ, hℓπ⟩

private theorem lower_bound {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (hlift : ∀ σ : e6QTwoTorParamSubgroup (K := K), ∃ ℓ : L, (ℓ : G) ∈ Bs ⊓ L ∧
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) ℓ =
        e6QTwoFrameTorusHom hK Q hQ σ) :
    3 ^ 4 ≤ Nat.card ↥(Bs ⊓ L) := by
  classical
  have hcardmap := image_card_eq (θ := θ) hZ2 hBs
  have h1 : Nat.card (e6QTwoFrameTorusHom hK Q hQ).range ≤
      Nat.card ↥(((Bs ⊓ L).subgroupOf L).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))) :=
    Subgroup.card_le_of_le (frame_range_le_image hK Q hQ hlift)
  rw [hcardmap, e6QTwoCardRangeFrameTorusHom hK Q hQ] at h1
  exact h1

private theorem disjoint_zpowers {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian 3 Bs)
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) :
    (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨⟨hyBs, hyL⟩, hyx⟩ := Subgroup.mem_inf.mp hy
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) := by
    rw [← hBL]
    exact inf_le_right
  have hyC : y ∈ Subgroup.centralizer (L : Set G) := hle hyx
  have hyZ : (⟨y, hyL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hyC (l : G) l.2
  have hy3G : y ^ 3 = 1 := hBs.2 y hyBs
  obtain ⟨k, hk⟩ := hZ2 (⟨⟨y, hyL⟩, hyZ⟩ : Subgroup.center L)
  have hy2 : y ^ 2 ^ k = 1 := by
    have h' := congrArg (fun z : Subgroup.center L => ((z : L) : G)) hk
    simpa using h'
  exact e6QTwoEqOneOfPowThreeOfPowTwo hy3G hy2

private theorem upper_bound {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hdisj : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥) :
    Nat.card ↥(Bs ⊓ L) ≤ 3 ^ 4 := by
  classical
  have hx3 : x ^ 3 = 1 := hBs.2 x hx
  have hzx_le : Subgroup.zpowers x ≤ Bs := by
    rw [← hBL]
    exact inf_le_left
  let f : ↥(Bs ⊓ L) × ↥(Subgroup.zpowers x) → ↥Bs := fun p =>
    ⟨p.1.1 * p.2.1, Bs.mul_mem p.1.2.1 (hzx_le p.2.2)⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨y, hy⟩⟩ ⟨⟨a', ha'⟩, ⟨y', hy'⟩⟩ hf
    simp only [f, Subtype.mk.injEq] at hf
    have h1 : y * y'⁻¹ = a⁻¹ * a' := by
      calc y * y'⁻¹ = a⁻¹ * (a * y) * y'⁻¹ := by group
        _ = a⁻¹ * (a' * y') * y'⁻¹ := by rw [hf]
        _ = a⁻¹ * a' := by group
    have h2 : a⁻¹ * a' ∈ Bs ⊓ L :=
      ⟨Bs.mul_mem (Bs.inv_mem ha.1) ha'.1, L.mul_mem (L.inv_mem ha.2) ha'.2⟩
    have h3 : y * y'⁻¹ ∈ Subgroup.zpowers x :=
      Subgroup.mul_mem (H := Subgroup.zpowers x) hy
        (Subgroup.inv_mem (H := Subgroup.zpowers x) hy')
    have h4 : a⁻¹ * a' = 1 := by
      have h4' : a⁻¹ * a' ∈ (Bs ⊓ L) ⊓ Subgroup.zpowers x := ⟨h2, h1 ▸ h3⟩
      rwa [hdisj, Subgroup.mem_bot] at h4'
    have haeq : a = a' := by
      have h : a' = a := by
        calc a' = a * (a⁻¹ * a') := by group
          _ = a := by rw [h4, mul_one]
      exact h.symm
    have hyeq : y = y' := by
      have h5 : y * y'⁻¹ = 1 := by rw [h1, h4]
      calc y = (y * y'⁻¹) * y' := by group
        _ = y' := by rw [h5, one_mul]
    exact Prod.ext (Subtype.ext haeq) (Subtype.ext hyeq)
  have hle := Nat.card_le_card_of_injective f hf_inj
  rw [Nat.card_prod, Nat.card_zpowers, orderOf_eq_prime hx3 hx1, hcard] at hle
  norm_num at hle ⊢
  omega

private theorem image_isElemAbelian {G : Type} [Group G] {K : Type} [Field K]
    {Bs L : Subgroup G} {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    (hBs : IsElemAbelian 3 Bs) :
    IsElemAbelian 3 (((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))) :=
  ((CFSG.Open.IsElemAbelian.mono hBs inf_le_left).subgroupOf L).map
    (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem card_inf_eq_and_exists_map_eq_torU_of_isPGroup (hK : Nat.card K = 4)
    {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ 4 ∧
      ∃ θ' : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
        ((Bs ⊓ L).subgroupOf L).map
          (θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K := by
  classical
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let β : Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    (MulAut.congr θ).toMonoidHom.comp
      ((e6QTwoQuotCenterAutHom L).comp (e6QTwoBstarConjAction hNL))
  have hβ_eq : ∀ b : Bs, β b =
      (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b)) := fun _ => rfl
  have hβ_apply := beta_apply hNL hβ_eq
  have hβ_ker := beta_ker_eq hperf hNL hβ_eq
  have hcardKer := beta_card_ker hβ_ker hBL hx hx1 hBs
  have hEcard := beta_card_range (β := β) hcardKer hcard
  have hEea := beta_isElemAbelian (β := β) hBs
  have hβmem := beta_mem_matConjImage hNL hβ_apply hI
  have hEin := beta_range_le_inndiag hK hK' hβmem
  obtain ⟨Q, hQ, hQfr⟩ := exists_frame_of_beta hK hK' hEea hEin hEcard
  have hA3 := bstarConjAction_isPGroup hBs hNL
  have hlift : ∀ σ : e6QTwoTorParamSubgroup (K := K), ∃ ℓ : L, (ℓ : G) ∈ Bs ⊓ L ∧
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) ℓ =
        e6QTwoFrameTorusHom hK Q hQ σ := fun σ =>
    exists_cube_lift hK hNL hZ2 hstar hA3 Q hQ σ
      (frame_torus_fixed hK hperf hNL hβ_eq Q hQ hQfr σ)
  have hcardmap := image_card_eq (θ := θ) hZ2 hBs
  have hlower := lower_bound hK hZ2 hBs Q hQ hlift
  have hdisj := disjoint_zpowers hBs hZ2 hBL
  have hupper := upper_bound hBs hcard hx hx1 hBL hdisj
  have hEq : Nat.card ↥(Bs ⊓ L) = 3 ^ 4 := le_antisymm hupper hlower
  have hE'ea := image_isElemAbelian (θ := θ) hBs
  have hE'card := hcardmap.trans hEq
  obtain ⟨g, hg⟩ := USixTwo.exists_conj_eq_torU hK hE'ea hE'card
  refine ⟨hEq, ⟨θ.trans (MulAut.conj g), ?_⟩⟩
  have hcomp : (θ.trans (MulAut.conj g)).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center L)) = (MulAut.conj g).toMonoidHom.comp
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) := rfl
  rw [hcomp, ← Subgroup.map_map]
  exact hg

end CFSG.StandardType.E6QTwo

end
