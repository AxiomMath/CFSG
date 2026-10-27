module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAutLQ
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQ
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixInnerAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixInnerAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixInnerAux3

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.StandardType CFSG.StandardType.USixTwo
open USixTwo TorConj TorHomKernel MainProof TorHyperplanes
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

omit [Finite G] in
private theorem inf_inf_zpowers_eq_bot_of_card_six
    {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) :
    (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥ := by
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

private theorem frameTorusHom_fixes_quotient_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {Q : GL (Fin 6) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (hQfr : ∀ e ∈ (e6QTwoSixFrameAction hNL θ).range,
      ∃ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ)
    (σ : e6QTwoTorParamSubgroup (K := K))
    {q : L ⧸ Subgroup.center L} {l₀ : L}
    (hθq : θ q = e6QTwoFrameTorusHom hK Q hQ σ)
    (hl₀ : QuotientGroup.mk' (Subgroup.center L) l₀ = q) :
    ∀ a ∈ (e6QTwoBstarConjAction hNL).range,
      e6QTwoQuotCenterAutHom L a q = q := by
  have hnormσ : ∀ k, ((σ.1 k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
    intro k
    rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val,
      USixTwo.cube_unit_eq_one hK, Units.val_one]
  rintro a ⟨b, rfl⟩
  obtain ⟨σe, _, _, hσen, hefr⟩ := hQfr (e6QTwoSixFrameAction hNL θ b) ⟨b, rfl⟩
  have hcommAut : e6QTwoSixFrameAction hNL θ b * MulAut.conj
      (e6QTwoFrameTorusHom hK Q hQ σ) =
      MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ) *
        e6QTwoSixFrameAction hNL θ b := by
    refine e6QTwoFrameActMulComm hefr (e6QTwoFrameActFrameTorusHom hK Q hQ σ)
      hσen hnormσ ?_
    funext k
    rw [Pi.mul_apply, Pi.mul_apply, mul_comm]
  have hcommL : e6QTwoBstarConjAction hNL b * MulAut.conj l₀ =
      MulAut.conj l₀ * e6QTwoBstarConjAction hNL b := by
    apply e6QTwoQuotCenterAutHom_injective hperf
    have h2 : (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b) *
        MulAut.conj (QuotientGroup.mk' (Subgroup.center L) l₀)) =
        (MulAut.congr θ) (MulAut.conj (QuotientGroup.mk' (Subgroup.center L) l₀) *
          e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b)) := by
      rw [map_mul, map_mul,
        ← e6QTwoMulAutConjCongr θ (QuotientGroup.mk' (Subgroup.center L) l₀), hl₀, hθq,
        ← e6QTwoSixFrameAction_eq hNL θ b]
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
  rw [← hl₀, e6QTwoQuotCenterAutHom_mk, hmk]

private theorem frameTorus_lift_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {Q : GL (Fin 6) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (hQfr : ∀ e ∈ (e6QTwoSixFrameAction hNL θ).range,
      ∃ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ)
    (hA3 : IsPGroup 3 (e6QTwoBstarConjAction hNL).range) :
    ∀ σ : e6QTwoTorParamSubgroup (K := K),
      ∃ ℓ : L, (ℓ : G) ∈ Bs ⊓ L ∧
        piOf (K := K) θ ℓ = e6QTwoFrameTorusHom hK Q hQ σ := by
  intro σ
  let r : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    e6QTwoFrameTorusHom hK Q hQ σ
  let q : L ⧸ Subgroup.center L := θ.symm r
  have hθq : θ q = r := θ.apply_symm_apply r
  obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
  have hfixA : ∀ a ∈ (e6QTwoBstarConjAction hNL).range,
      e6QTwoQuotCenterAutHom L a q = q :=
    frameTorusHom_fixes_quotient_of_card_six hK θ hperf hNL hQ hQfr σ hθq hl₀
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
  refine ⟨ℓ, ⟨hℓBs, ℓ.2⟩, ?_⟩
  show θ (QuotientGroup.mk' (Subgroup.center L) ℓ) = e6QTwoFrameTorusHom hK Q hQ σ
  rw [hℓq, hθq]

private theorem exists_frameTorus_lift_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    ∃ (Q : GL (Fin 6) K)
      (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
        (RankThree.PartOne.KCUnitaryModel.idGram K 6)),
      ∀ σ : e6QTwoTorParamSubgroup (K := K),
        ∃ ℓ : L, (ℓ : G) ∈ Bs ⊓ L ∧
          piOf (K := K) θ ℓ = e6QTwoFrameTorusHom hK Q hQ σ := by
  classical
  have hrange : Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5 :=
    (e6QTwoSixFrameFullDiagonal hK θ hperf hBs hcard hx hBL hNL hI).2.1
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨Q, hQ, hQfr⟩ := TableBUD.exists_frame_inndiag (h := USixTwo.fieldDataFour hK) hK'
    (by norm_num : 3 ≤ 6) (by norm_num : (6, 2 ^ 1) ≠ (3, 2))
    (by norm_num : ¬(6 = 3 ∧ 2 ^ 1 = 2)) (by norm_num : Nat.Prime 3)
    (by norm_num : 3 ∣ 2 ^ 1 + 1)
    (e6QTwoSixFrameAction_isElemAbelian_range hNL θ hBs)
    (e6QTwoSixFrameAction_range_le_inndiag hK hNL θ hI)
    (by rw [hrange]; norm_num)
  have hA3 : IsPGroup 3 (e6QTwoBstarConjAction hNL).range := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨k, hk⟩ := hBs.isPGroup b
    refine ⟨k, ?_⟩
    apply Subtype.ext
    show y ^ 3 ^ k = 1
    rw [← hb, ← map_pow, hk, map_one]
  exact ⟨Q, hQ, frameTorus_lift_of_card_six hK θ hperf hZ2 hstar hNL hQ hQfr hA3⟩

private theorem three_pow_four_le_card_inf_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    3 ^ 4 ≤ Nat.card ↥(Bs ⊓ L) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Q, hQ, hlift⟩ :=
    exists_frameTorus_lift_of_card_six hK θ hperf hZ2 hBs hcard hx hBL hstar hNL hI
  have hkerπ : (piOf (K := K) θ).ker = Subgroup.center L := piOf_ker_aux θ
  have hinf : ((Bs ⊓ L).subgroupOf L) ⊓ (piOf (K := K) θ).ker = ⊥ := by
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
  have hcardmap : Nat.card ↥(((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ)) =
      Nat.card ↥((Bs ⊓ L).subgroupOf L) :=
    card_map_eq_card_of_inf_ker_eq_bot (piOf (K := K) θ) hinf
  have hmap_le : (e6QTwoFrameTorusHom hK Q hQ).range ≤
      ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) := by
    rintro y ⟨σ, rfl⟩
    obtain ⟨ℓ, hℓ, hℓπ⟩ := hlift σ
    exact Subgroup.mem_map.mpr ⟨ℓ, hℓ, hℓπ⟩
  have hlower : 3 ^ 4 ≤ Nat.card ↥(Bs ⊓ L) := by
    have h1 : Nat.card (e6QTwoFrameTorusHom hK Q hQ).range ≤
        Nat.card ↥(((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ)) :=
      Subgroup.card_le_of_le hmap_le
    rw [hcardmap, hcard_sub, e6QTwoCardRangeFrameTorusHom hK Q hQ] at h1
    exact h1
  exact hlower

private theorem card_inf_le_three_pow_four_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 6) (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hdisj : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥) :
    Nat.card ↥(Bs ⊓ L) ≤ 3 ^ 4 := by
  have hx3 : x ^ 3 = 1 := hBs.2 x hx
  have hzx_le : Subgroup.zpowers x ≤ Bs := by
    rw [← hBL]
    exact inf_le_left
  have hC : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) := by
    rw [← hBL]
    exact inf_le_right
  let f : ↥(Bs ⊓ L) × ↥(Subgroup.zpowers x) →
      ↥(Bs ⊓ (L ⊔ Subgroup.centralizer (L : Set G))) := fun p =>
    ⟨p.1.1 * p.2.1, ⟨Bs.mul_mem p.1.2.1 (hzx_le p.2.2),
      Subgroup.mul_mem_sup p.1.2.2 (hC p.2.2)⟩⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨y, hy⟩⟩ ⟨⟨a', ha'⟩, ⟨y', hy'⟩⟩ hf
    have hf' : a * y = a' * y' := congrArg Subtype.val hf
    have h1 : y * y'⁻¹ = a⁻¹ * a' := by
      calc y * y'⁻¹ = a⁻¹ * (a * y) * y'⁻¹ := by group
        _ = a⁻¹ * (a' * y') * y'⁻¹ := by rw [hf']
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
  have hupper : Nat.card ↥(Bs ⊓ L) ≤ 3 ^ 4 := by
    have hle := Nat.card_le_card_of_injective f hf_inj
    have hsup := card_inf_sup_centralizer_of_card_six hK θ hperf hBs hcard hx hBL hNL hI
    rw [Nat.card_prod, Nat.card_zpowers, orderOf_eq_prime hx3 hx1, hsup] at hle
    norm_num at hle ⊢
    omega
  exact hupper

private theorem card_inf_eq_three_pow_four_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ 4 := by
  have hdisj := inf_inf_zpowers_eq_bot_of_card_six hZ2 hBs hBL
  have hlow := three_pow_four_le_card_inf_of_card_six hK θ hperf hZ2 hBs hcard hx hBL
    hstar hNL hI
  have hup := card_inf_le_three_pow_four_of_card_six hK θ hperf hBs hcard hx hx1 hBL
    hNL hI hdisj
  exact le_antisymm hup hlow

private theorem card_map_inf_eq_three_pow_four_of_card_six
    {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hEq : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) :
    Nat.card ↥(((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ)) = 3 ^ 4 := by
  have hkerπ : (piOf (K := K) θ).ker = Subgroup.center L := piOf_ker_aux θ
  have hinf : ((Bs ⊓ L).subgroupOf L) ⊓ (piOf (K := K) θ).ker = ⊥ := by
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
  have hcardmap : Nat.card ↥(((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ)) =
      Nat.card ↥((Bs ⊓ L).subgroupOf L) :=
    card_map_eq_card_of_inf_ker_eq_bot (piOf (K := K) θ) hinf
  rw [hcardmap, hcard_sub, hEq]

omit [Finite G] in
private theorem exists_map_eq_torU_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hBs : IsElemAbelian 3 Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hcardmap : Nat.card ↥(((Bs ⊓ L).subgroupOf L).map
      (piOf (K := K) θ)) = 3 ^ 4) :
    ∃ θ' : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
      ((Bs ⊓ L).subgroupOf L).map
        (θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K ∧
      ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
          (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) ψ := by
  classical
  have hE'ea : IsElemAbelian 3 (((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ)) :=
    ((CFSG.Open.IsElemAbelian.mono hBs inf_le_left).subgroupOf L).map (piOf (K := K) θ)
  obtain ⟨g, hg⟩ := USixTwo.exists_conj_eq_torU hK hE'ea hcardmap
  refine ⟨θ.trans (MulAut.conj g), ?_, ?_⟩
  · have hcomp : (θ.trans (MulAut.conj g)).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center L)) =
        (MulAut.conj g).toMonoidHom.comp (piOf (K := K) θ) := rfl
    rw [hcomp, ← Subgroup.map_map]
    exact hg
  · intro b hb
    obtain ⟨ψ, hψ, hψind⟩ := hI b hb
    exact exists_inducing_conj hK hψ hψind

theorem card_inf_eq_and_exists_map_eq_torU_of_card_six (hK : Nat.card K = 4)
    {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
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
          (θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K ∧
        ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
            (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
          LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) ψ := by
  classical
  have hEq := card_inf_eq_three_pow_four_of_card_six hK θ hperf hZ2 hBs hcard hx hx1 hBL
    hstar hNL hI
  have hcardmap := card_map_inf_eq_three_pow_four_of_card_six θ hZ2 hBs hEq
  exact ⟨hEq, exists_map_eq_torU_of_card_six hK θ hBs hI hcardmap⟩

private theorem psigma_swap_mul_threeA_mul_inv_of_card_six
    (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    Psigma hK (Equiv.swap 0 1) * USixTwo.threeA hω *
        (Psigma hK (Equiv.swap 0 1))⁻¹ = (USixTwo.threeA hω)⁻¹ := by
  let σ : Equiv.Perm (Fin 6) := Equiv.swap 0 1
  calc Psigma hK σ * USixTwo.threeA hω * (Psigma hK σ)⁻¹
      = Psigma hK σ * ↑((torHom hK hω) threeAArg) * (Psigma hK σ)⁻¹ := by
        rw [torHom_threeAArg hK hω]
    _ = ↑((torHom hK hω) (permX σ threeAArg)) := torHom_conj hK hω σ threeAArg
    _ = ↑((torHom hK hω) threeAArg⁻¹) := by
        rw [show permX σ threeAArg = threeAArg⁻¹ from permX_swap01_threeAArg]
    _ = ↑(((torHom hK hω) threeAArg)⁻¹) := by rw [map_inv]
    _ = (↑((torHom hK hω) threeAArg))⁻¹ := rfl
    _ = (USixTwo.threeA hω)⁻¹ := by rw [torHom_threeAArg hK hω]

private theorem normalizer_action_delta_pow_of_card_six
    (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    {a : ↥Bs} {haL : (a : G) ∈ L}
    (hπa : piOf (K := K) θ ⟨a, haL⟩ = USixTwo.threeA hω)
    {n' : ↥L}
    (hn'π : piOf (K := K) θ n' = Psigma hK (Equiv.swap 0 1))
    (hn'N : (n' : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ∀ b : ↥Bs, ∃ k : ℕ,
      b⁻¹ * Subgroup.normalizerMonoidHom Bs ⟨n', hn'N⟩ b = a ^ k := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hmap' : ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) = USixTwo.torU K := hmap
  intro b
  obtain ⟨k, hk⟩ := pi_delta hK hω θ hmap' hBs hI hNL hn'π b
  have hψb : ((b⁻¹ * Subgroup.normalizerMonoidHom Bs ⟨n', hn'N⟩ b : ↥Bs) : G) =
      ((deltaElem hNL n' b : ↥L) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe, deltaElem_coe]
    group
  have hδB : ((deltaElem hNL n' b : ↥L) : G) ∈ Bs := by
    have hnb : (n' : G) * (b : G) * (n' : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hn'N (b : G)).mp b.2
    have heq : (b : G)⁻¹ * (n' : G) * (b : G) * (n' : G)⁻¹ =
        (b : G)⁻¹ * ((n' : G) * (b : G) * (n' : G)⁻¹) := by group
    rw [deltaElem_coe, heq]
    exact Bs.mul_mem (Bs.inv_mem b.2) hnb
  have hδE : deltaElem hNL n' b ∈ (Bs ⊓ L).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hδB, (deltaElem hNL n' b).2⟩
  have hakE : (⟨a, haL⟩ : ↥L) ^ k ∈ (Bs ⊓ L).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨Bs.pow_mem a.2 k, L.pow_mem haL k⟩
  have hπak : piOf (K := K) θ ((⟨a, haL⟩ : ↥L) ^ k) = (USixTwo.threeA hω) ^ k := by
    rw [map_pow, hπa]
  have heqL : deltaElem hNL n' b = (⟨a, haL⟩ : ↥L) ^ k :=
    piOf_inj_inf hZ2 hBs θ hδE hakE (hk.trans hπak.symm)
  refine ⟨k, ?_⟩
  apply Subtype.ext
  rw [hψb]
  have hcoe : ((a ^ k : ↥Bs) : G) = (((⟨a, haL⟩ : ↥L) ^ k : ↥L) : G) := by
    rw [Subgroup.coe_pow, Subgroup.coe_pow]
  rw [hcoe, ← heqL]

private theorem normalizer_action_inverts_of_card_six
    (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs)
    {a : ↥Bs} {haL : (a : G) ∈ L}
    (hπa : piOf (K := K) θ ⟨a, haL⟩ = USixTwo.threeA hω)
    {n' : ↥L}
    (hn'π : piOf (K := K) θ n' = Psigma hK (Equiv.swap 0 1))
    (hn'N : (n' : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    Subgroup.normalizerMonoidHom Bs ⟨n', hn'N⟩ a = a⁻¹ := by
  apply Subtype.ext
  have hleft : ((Subgroup.normalizerMonoidHom Bs ⟨n', hn'N⟩ a : ↥Bs) : G) =
      (n' : G) * (a : G) * (n' : G)⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨n', hn'N⟩ a
  rw [hleft]
  have hmemL : (n' : G) * (a : G) * (n' : G)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem n'.2 haL) (L.inv_mem n'.2)
  have hmemB : (n' : G) * (a : G) * (n' : G)⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hn'N (a : G)).mp a.2
  have hleftE : (⟨(n' : G) * (a : G) * (n' : G)⁻¹, hmemL⟩ : ↥L) ∈
      (Bs ⊓ L).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]; exact ⟨hmemB, hmemL⟩
  have hrightE : (⟨a, haL⟩ : ↥L)⁻¹ ∈ (Bs ⊓ L).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]; exact ⟨Bs.inv_mem a.2, L.inv_mem haL⟩
  have hpi1 : piOf (K := K) θ (⟨(n' : G) * (a : G) * (n' : G)⁻¹, hmemL⟩ : ↥L) =
      (USixTwo.threeA hω)⁻¹ := by
    have hprod : (⟨(n' : G) * (a : G) * (n' : G)⁻¹, hmemL⟩ : ↥L) =
        n' * ⟨a, haL⟩ * n'⁻¹ := Subtype.ext rfl
    rw [hprod, map_mul, map_mul, map_inv, hn'π, hπa,
      psigma_swap_mul_threeA_mul_inv_of_card_six hK hω]
  have hpi2 : piOf (K := K) θ ((⟨a, haL⟩ : ↥L)⁻¹) = (USixTwo.threeA hω)⁻¹ := by
    rw [map_inv, hπa]
  have heqL : (⟨(n' : G) * (a : G) * (n' : G)⁻¹, hmemL⟩ : ↥L) =
      (⟨a, haL⟩ : ↥L)⁻¹ :=
    piOf_inj_inf hZ2 hBs θ hleftE hrightE (hpi1.trans hpi2.symm)
  exact congrArg (fun q : ↥L => (q : G)) heqL

theorem exists_reflection_threeA_of_card_six (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    ∃ (a : ↥Bs) (ha : (a : G) ∈ L), θ (QuotientGroup.mk (⟨a, ha⟩ : L)) = USixTwo.threeA hω ∧
      a ≠ 1 ∧ ∃ ψ ∈ ggAutomizer L Bs, ψ ^ 2 = 1 ∧ ψ a = a⁻¹ ∧
        ∀ b : ↥Bs, b⁻¹ * ψ b ∈ Subgroup.zpowers a := by
  classical
  obtain ⟨a, haL, hπa, ha1, n', hn'π, hn'N⟩ :=
    exists_normalizing_preimage_of_card_six hK hω θ hZ2 hmap hBs hcard hNL hI
  have hθa : θ (QuotientGroup.mk (⟨a, haL⟩ : L)) = USixTwo.threeA hω := hπa
  have hdelta : ∀ b : ↥Bs, ∃ k : ℕ,
      b⁻¹ * Subgroup.normalizerMonoidHom Bs ⟨n', hn'N⟩ b = a ^ k :=
    normalizer_action_delta_pow_of_card_six hK hω θ hZ2 hmap hBs hNL hI hπa hn'π hn'N
  have hψaa : Subgroup.normalizerMonoidHom Bs ⟨n', hn'N⟩ a = a⁻¹ :=
    normalizer_action_inverts_of_card_six hK hω θ hZ2 hBs hπa hn'π hn'N
  let ψ : MulAut ↥Bs := Subgroup.normalizerMonoidHom Bs ⟨n', hn'N⟩
  have hψ2 : ψ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro b
    obtain ⟨j, hj⟩ := hdelta b
    have hcomm : ψ b = b * a ^ j := by
      change Subgroup.normalizerMonoidHom Bs ⟨n', hn'N⟩ b = b * a ^ j
      rw [← hj]; group
    calc ψ (ψ b) = ψ (b * a ^ j) := by rw [hcomm]
      _ = ψ b * (ψ a) ^ j := by rw [map_mul, map_pow]
      _ = ψ b * (a⁻¹) ^ j := by rw [show ψ a = a⁻¹ from hψaa]
      _ = (b * a ^ j) * (a ^ j)⁻¹ := by rw [hcomm, inv_pow]
      _ = b := by group
  have hδZ : ∀ b : ↥Bs, b⁻¹ * ψ b ∈ Subgroup.zpowers a := by
    intro b
    obtain ⟨k, hk⟩ := hdelta b
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨(k : ℤ), by rw [zpow_natCast, hk]⟩
  have hψmem : ψ ∈ ggAutomizer L Bs := by
    apply Subgroup.subset_closure
    refine ⟨(n' : G), n'.2, hn'N, ?_⟩
    intro b
    exact Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨n', hn'N⟩ b
  exact ⟨a, haL, hθa, ha1, ψ, hψmem, hψ2, hψaa, hδZ⟩

end CFSG.StandardType.E6QTwo

end
