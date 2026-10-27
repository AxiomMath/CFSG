module

public import CFSG.RankThree.PartTwo.KFacts.KSL3PiOrder3TypeC
public import CFSG.RankThree.PartTwo.Sec4.LThreePiOn
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped Pointwise

section Tools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem thetaQuotMulAut_eq_conj {x : G} (hN : x ∈ Subgroup.normalizer (L : Set G)) (s : L)
    (hxs : ∀ l : L, x * (l : G) * x⁻¹ = ((s * l * s⁻¹ : L) : G))
    (z : L ⧸ aschbacherSolvableCore 3 L) :
    Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hN⟩) z =
      (s : L ⧸ aschbacherSolvableCore 3 L) * z * (s : L ⧸ aschbacherSolvableCore 3 L)⁻¹ := by
  induction z using QuotientGroup.induction_on with
  | H l =>
    rw [Sec4.thetaQuotMulAut_mk]
    have h1 : (L.normalizerMonoidHom ⟨x, hN⟩ l : L) = s * l * s⁻¹ :=
      Subtype.ext (by rw [Sec4.normalizerMonoidHom_apply_coe]; exact hxs l)
    rw [h1]
    rfl

theorem card_map_mk_eq {K : Type} [Field K] (D : Subgroup (GL (Fin 3) K)) :
    Nat.card (D.map ProjGenLinGroup.mk) =
      Nat.card (D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K))) := by
  have h1 : (ProjGenLinGroup.mk.comp D.subtype).range = D.map ProjGenLinGroup.mk := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h2 : ((QuotientGroup.mk' (StatedScalars (Fin 3) K)).comp D.subtype).range =
      D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h1, ← h2]
  refine Sec4.card_range_eq_of_ker_eq _ _ ?_
  ext d
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  rfl

end Tools

section Construction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {c : G}

theorem exists_typeC_E27 (hK : KFacts.KSL3PiOrder3TypeC) {π : Bool} {p e : ℕ} {K : Type}
    [Field K] (hKf : Sec4.PiField π p e K) (hq : Sec4.ModThree π (p ^ e))
    (h9 : p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)
    (φ : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* projImage (Sec4.slPi π 3 (p ^ e) K))
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hLc : ∀ l ∈ L, l * c = c * l) (hc3 : c ^ 3 = 1) (hcL : c ∉ L)
    {f : G} (hfL : f ∈ L) (hf3 : f ^ 3 = 1) (hf1 : f ≠ 1) :
    ∃ E : Subgroup G, c ∈ E ∧ f ∈ E ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      E ≤ Subgroup.normalizer (L : Set G) ∧
      Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧
      Sec4.IsTypeCOn E L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set P := projImage (Sec4.slPi π 3 (p ^ e) K) with hP
  set f' : ↥L := ⟨f, hfL⟩ with hf'
  have hf'3 : f' ^ 3 = 1 := Subtype.ext (by simpa [hf'] using hf3)
  have hord : orderOf f' = 3 := orderOf_eq_prime hf'3 (fun h1 => hf1 (congrArg Subtype.val h1))
  have hE₀ : IsPGroup 3 (Subgroup.zpowers f') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hinjf := injOn_mk_of_isPGroup Nat.prime_three hE₀
  have hmkf1 : QuotientGroup.mk' θ f' ≠ 1 := by
    intro h1
    apply hf1
    have := hinjf (Subgroup.mem_zpowers f') (one_mem _) (by rw [h1, map_one])
    exact congrArg Subtype.val this
  set x : ProjGenLinGroup (Fin 3) K := (φ (QuotientGroup.mk' θ f') : ProjGenLinGroup (Fin 3) K)
    with hx
  have hxmem : x ∈ P := (φ (QuotientGroup.mk' θ f')).2
  have hx3 : x ^ 3 = 1 := by
    have h1 : φ (QuotientGroup.mk' θ f') ^ 3 = 1 := by rw [← map_pow, ← map_pow, hf'3, map_one,
      map_one]
    rw [hx, ← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hx1 : x ≠ 1 := by
    intro h1
    apply hmkf1
    apply φ.injective
    rw [map_one]
    exact Subtype.ext h1
  obtain ⟨D, hD, hDsl, y, hyD, hyx⟩ := hK π p e K hKf hq h9 x hxmem hx3 hx1
  set MD : Subgroup (ProjGenLinGroup (Fin 3) K) := D.map ProjGenLinGroup.mk with hMD
  have hMDle : MD ≤ P := Subgroup.map_mono hDsl
  set B : Subgroup (↥L ⧸ θ) := (MD.subgroupOf P).comap φ.toMonoidHom with hB
  have hmemB : ∀ z, z ∈ B ↔ (φ z : ProjGenLinGroup (Fin 3) K) ∈ MD := fun z => Iff.rfl
  have hcardMD : Nat.card MD = 9 := by rw [hMD, card_map_mk_eq, hD.2.2.1]
  have hcardB : Nat.card B = 9 := by
    rw [← hcardMD, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMDle).toEquiv]
    exact Nat.card_congr (φ.toEquiv.subtypeEquiv fun z => Iff.rfl)
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hcardB]; norm_num)
  have hfB : QuotientGroup.mk' θ f' ∈ B := (hmemB _).mpr ⟨y, hyD, hyx⟩
  have hBexp : ∀ z ∈ B, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨d, hd, hdz⟩ := (hmemB z).mp hz
    apply φ.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, ← hdz, ← map_pow, map_one, Subgroup.coe_one,
      ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact hD.2.1 d hd
  obtain ⟨S, hE₀S, -, hS3, hSB⟩ := exists_isPGroup_le_map_eq hB3
    (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective θ)]; exact le_top)
    hE₀ le_top (by rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]; exact hfB)
  have hinjS := injOn_mk_of_isPGroup Nat.prime_three hS3
  have hmkS : ∀ s ∈ S, QuotientGroup.mk' θ s ∈ B := fun s hs =>
    hSB ▸ Subgroup.mem_map_of_mem _ hs
  have hcardS : Nat.card S = 9 := by rw [← hcardB, ← hSB, card_map_eq_of_injOn _ hinjS]
  have hBc : IsMulCommutative B :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := B) (by rw [hcardB]; norm_num)
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hSab : CFSG.Assembly.IsElemAbelian 3 S := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun s hs => ?_⟩
    · refine hinjS (S.mul_mem a.2 b.2) (S.mul_mem b.2 a.2) ?_
      simp only [Subgroup.coe_mul, map_mul]
      exact hBcomm _ (hmkS _ a.2) _ (hmkS _ b.2)
    · refine hinjS (S.pow_mem hs 3) S.one_mem ?_
      rw [map_pow, hBexp _ (hmkS s hs), map_one]
  set C : Subgroup G := S.map L.subtype with hC
  have hCL : C ≤ L := Subgroup.map_subtype_le S
  have hCab : CFSG.Assembly.IsElemAbelian 3 C := isElemAbelian_map hSab L.subtype
  have hcardC : Nat.card C = 9 := by
    rw [hC, Subgroup.card_map_of_injective L.subtype_injective, hcardS]
  have hcC : c ∉ C := fun h => hcL (hCL h)
  have hcomm : ∀ a ∈ C, a * c = c * a := fun a ha => hLc a (hCL ha)
  obtain ⟨hEab, hE27⟩ := Sec5.isElemAbelian_sup_zpowers hCab hcC hc3 hcomm
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hLc)
  have hEN : C ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hCL.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr hcN)
  have hzle : Subgroup.zpowers c ≤ Subgroup.normalizer (C : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
    exact Subgroup.mem_centralizer_iff.mpr hcomm
  have hdec : ∀ z ∈ C ⊔ Subgroup.zpowers c, ∃ s ∈ S, ∃ k : ℤ, z = (s : G) * c ^ k := by
    intro z hz
    have hz' : z ∈ (C : Set G) * (Subgroup.zpowers c : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left C _ hzle]
      exact hz
    obtain ⟨_, ⟨s, hs, rfl⟩, w, hw, rfl⟩ := hz'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ⟨s, hs, k, rfl⟩
  have hconj : ∀ (s : L) (k : ℤ) (l : L),
      (s : G) * c ^ k * (l : G) * ((s : G) * c ^ k)⁻¹ = ((s * l * s⁻¹ : L) : G) := by
    intro s k l
    have hck : c ^ k * (l : G) = l * c ^ k := (Commute.zpow_left (hLc l l.2).symm k).eq
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    calc (s : G) * c ^ k * (l : G) * ((s : G) * c ^ k)⁻¹
        = (s : G) * (c ^ k * (l : G)) * (c ^ k)⁻¹ * (s : G)⁻¹ := by group
      _ = (s : G) * ((l : G) * c ^ k) * (c ^ k)⁻¹ * (s : G)⁻¹ := by rw [hck]
      _ = (s : G) * (l : G) * (s : G)⁻¹ := by group
  refine ⟨C ⊔ Subgroup.zpowers c, Subgroup.mem_sup_right (Subgroup.mem_zpowers c),
    Subgroup.mem_sup_left ⟨f', hE₀S (Subgroup.mem_zpowers f'), rfl⟩, hEab,
    by rw [hE27, hcardC], hEN, ?_, ?_⟩
  ·
    ext z
    constructor
    · rintro ⟨hz, hzc⟩
      obtain ⟨s, hs, k, rfl⟩ := hdec z hz
      have hcen : QuotientGroup.mk' θ s ∈ Subgroup.center (↥L ⧸ θ) := by
        rw [Subgroup.mem_center_iff]
        intro w
        induction w using QuotientGroup.induction_on with
        | H l =>
          have h1 := hzc l l.2
          rw [hconj s k l] at h1
          obtain ⟨m, hm, hml⟩ := h1
          have hm' : m = s * l * s⁻¹ * l⁻¹ := Subtype.ext (by simpa using hml)
          rw [hm'] at hm
          have h2 : QuotientGroup.mk' θ (s * l * s⁻¹ * l⁻¹) = 1 :=
            (QuotientGroup.eq_one_iff _).mpr hm
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
            mul_inv_eq_iff_eq_mul] at h2
          exact h2.symm
      rw [hZ, Subgroup.mem_bot] at hcen
      have hs1 : s = 1 := hinjS hs S.one_mem (by rw [hcen, map_one])
      rw [hs1, Subgroup.coe_one, one_mul]
      exact Subgroup.zpow_mem_zpowers c k
    · intro hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine ⟨Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers c k), fun l hl => ?_⟩
      have hck : c ^ k * l = l * c ^ k := (Commute.zpow_left (hLc l hl).symm k).eq
      rw [hck, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  ·
    refine ⟨π, p, e, K, inferInstance, hKf, hq, φ, D, hD, ?_, ?_⟩
    · intro τ hτ
      obtain ⟨z, hzN, hzE, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
      obtain ⟨s, hs, k, rfl⟩ := hdec z hzE
      obtain ⟨d, hd, hdz⟩ := (hmemB _).mp (hmkS s hs)
      refine ⟨d, hd, fun w => ?_⟩
      rw [thetaQuotMulAut_eq_conj hzN s (hconj s k) w, map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hdz]
      rfl
    · intro d hd
      have hdP : ProjGenLinGroup.mk d ∈ P := hMDle ⟨d, hd, rfl⟩
      set w : ↥L ⧸ θ := φ.symm ⟨ProjGenLinGroup.mk d, hdP⟩ with hw
      have hwB : w ∈ B := by
        rw [hmemB, hw, MulEquiv.apply_symm_apply]
        exact ⟨d, hd, rfl⟩
      rw [← hSB] at hwB
      obtain ⟨s, hs, hsw⟩ := hwB
      have hsN : (s : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer s.2
      refine ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨(s : G), hsN,
        Subgroup.mem_sup_left ⟨s, hs, rfl⟩, rfl⟩, fun v => ?_⟩
      rw [thetaQuotMulAut_eq_conj hsN s (fun l => rfl) v]
      change (φ (QuotientGroup.mk' θ s * v * (QuotientGroup.mk' θ s)⁻¹) :
        ProjGenLinGroup (Fin 3) K) = _
      rw [hsw, hw, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl

end Construction

end CFSG.RankThree.PartTwo.Sec15
