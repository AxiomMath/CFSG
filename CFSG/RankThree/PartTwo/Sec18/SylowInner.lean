module

public import CFSG.RankThree.PartTwo.Sec18.SylowFusion
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofStatements
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.WielandtProductBasic
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemRank
import CFSG.RankThree.PartTwo.Sec18.SylowInnerAlt2
import CFSG.RankThree.PartTwo.Sec18.SylowInnerGamma
import CFSG.RankThree.PartTwo.Sec18.SylowInnerH3
import CFSG.RankThree.PartTwo.Sec18.SylowLcUnique
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Late.Item2010
public import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.RankThree.PartTwo.Sec18.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace SylowInner

omit [Finite G] in
theorem mem_map_conj_inv_iff {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem sec18Std_map_conj {A M : Subgroup G} (h : Sec18Std G A M) (y : G) :
    Sec18Std G (A.map (MulAut.conj y).toMonoidHom) (M.map (MulAut.conj y).toMonoidHom) :=
  ⟨h.toPartTwoStanding, h.partTwoS_eq,
    CFSG.RankThree.PartTwo.map_mem_partTwoE (MulAut.conj y) h.mem_partTwoE,
    map_conj_mem_scriptM_gamma h.mem_scriptM y⟩

omit [Finite G] in
theorem map_conj_mem_scriptH {A M H : Subgroup G} (hH : H ∈ scriptH A M) (y : G) :
    H.map (MulAut.conj y).toMonoidHom ∈
      scriptH (A.map (MulAut.conj y).toMonoidHom) (M.map (MulAut.conj y).toMonoidHom) := by
  rw [mem_scriptH_iff_mem_scriptH₀] at hH ⊢
  refine ⟨(map_mem_scriptH₀_iff (MulAut.conj y).toMonoidHom (MulAut.conj y).injective).mpr hH.1,
    fun htop => hH.2 ?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj y).toMonoidHom) (MulAut.conj y).injective
  rw [htop, Subgroup.map_top_of_surjective _ (MulAut.conj y).surjective]

theorem inducesInnerMod_of_mem_sup {L : Subgroup G} {c x : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hx : x ∈ Subgroup.zpowers c ⊔ L) :
    InducesInnerMod x L (CFSG.Open.pCoreOf 2 L) := by
  have hcomm : ∀ w ∈ L, c * w = w * c := fun w hw =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLc hw)).symm
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.zpowers_le]
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    intro w hw
    rw [hcomm w hw, mul_inv_cancel_right]
    exact hw
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := sup_le hcN Subgroup.le_normalizer hx
  have hx' : x ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at hx'
  obtain ⟨z, hz, l, hl, rfl⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨hxN, l, hl, fun w hw => ?_⟩
  have hw' : l * w * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hw) (L.inv_mem hl)
  have hci : c ^ i * (l * w * l⁻¹) = l * w * l⁻¹ * c ^ i :=
    (Commute.zpow_left (show Commute c (l * w * l⁻¹) from hcomm _ hw') i).eq
  have h1 : c ^ i * l * w * (c ^ i * l)⁻¹ * (l * w * l⁻¹)⁻¹ = 1 := by
    calc c ^ i * l * w * (c ^ i * l)⁻¹ * (l * w * l⁻¹)⁻¹
        = c ^ i * (l * w * l⁻¹) * (c ^ i)⁻¹ * (l * w * l⁻¹)⁻¹ := by group
      _ = 1 := by rw [hci]; group
  rw [h1]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem eq_one_of_mem_of_isPGroup_two {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P)
    (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  have h2 : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hd : orderOf x ∣ Nat.gcd (2 ^ n) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n (by norm_num))] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem claim1844Inner_of (h4443 : Sec4.Item4_44_3) (h1812 : Item181_2) (h184 : Item184_1)
    (h182 : Item182Alt1C) : Claim1844Inner := by
  intro G _ _ A M H c hH
  show ∀ g : G, g * c * g⁻¹ ∈ A → ∀ a ∈ A,
    InducesInnerMod (g⁻¹ * a * g) (lc H c) (CFSG.Open.pCoreOf 2 (lc H c))
  intro g hd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1842 := item184_2_of h1812 h184 h182
  have h := hH.toSec18Std
  have : IsSimpleGroup G := h.isSimpleGroup
  set Lc := lc H c with hLcdef
  set O := CFSG.Open.pCoreOf 2 Lc with hOdef
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set B := A ⊓ inSubgroup perfectResidual H with hBdef
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hH).1
  have hc3 : orderOf c = 3 := orderOf_eq_three_of_sec18H h184 hH
  have hLcC : Lc ≤ C := SylowFusion.lc_le_centralizer H c
  have hCN : C ≤ Subgroup.normalizer (Lc : Set G) :=
    (centralizer_le_normalizer_zpowers c).trans (normalizer_zpowers_le_normalizer_lc h1842 hH)
  have hLcp : ⁅Lc, Lc⁆ = Lc := commutator_inSubgroup_perfectResidual _
  have hZ : Subgroup.center (Lc ⧸ CFSG.pCore 2 Lc) = ⊥ :=
    SylowFusion.center_quotient_lc_eq_bot h184 hH
  have hBLc : B ≤ Lc := (inf_lc_eq h1812 h184 hH).ge.trans inf_le_right
  have hAeq : A = Subgroup.zpowers c ⊔ B := eq_zpowers_sup_of_sec18H h1812 h184 hH
  have hB9 : Nat.card B = 9 := card_inf_of_sec18H h1812 h184 hH
  have hcLc : ∀ x ∈ Lc, c * x * c⁻¹ * x⁻¹ ∈ O := fun x hx => by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hLcC hx)).symm, mul_inv_cancel_right,
      mul_inv_cancel]
    exact O.one_mem
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'def
  set M' := M.map (MulAut.conj g⁻¹).toMonoidHom with hM'def
  have hmemA' : ∀ x, x ∈ A' ↔ g * x * g⁻¹ ∈ A := fun x => mem_map_conj_inv_iff
  have h' : Sec18Std G A' M' := sec18Std_map_conj h g⁻¹
  have hA' := isE27_of_mem_partTwoE h'.mem_partTwoE
  have hA'3 : ∀ x ∈ A', x ^ 3 = 1 := hA'.1.2
  have hA'ab : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA'.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcA' : c ∈ A' := (hmemA' c).mpr hd
  have hA'C : A' ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hA'ab x hx c hcA')
  have hA'N : A' ≤ Subgroup.normalizer (Lc : Set G) := hA'C.trans hCN
  have hΓM' : gamma 2 A' ≤ M' := fun x hx => h'.mem_scriptM.2 hx
  have hWM' : Subgroup.normalizer (A' : Set G) ≤ M' :=
    (normalizer_le_gamma le_rfl (by rw [hA'.pRank_eq]; norm_num)).trans hΓM'
  have hA'M' : A' ≤ M' := Subgroup.le_normalizer.trans hWM'
  have hM'top : M' ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot h.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal h'.mem_scriptM.1)
  suffices hall : ∀ x ∈ A', InducesInnerMod x Lc O by
    intro a ha
    exact hall _ ((hmemA' _).mpr (by rwa [show g * (g⁻¹ * a * g) * g⁻¹ = a by group]))
  by_contra hnot
  have hTK : A' ⊔ Lc ≤ Subgroup.normalizer (Lc : Set G) := sup_le hA'N Subgroup.le_normalizer
  have hA'p : IsPGroup 3 A' := fun x => ⟨1, Subtype.ext (by simpa using hA'3 _ x.2)⟩
  obtain ⟨Q, hQ⟩ := (hA'p.comap_subtype : IsPGroup 3 (A'.subgroupOf (A' ⊔ Lc))).exists_le_sylow
  set R := (Q : Subgroup (A' ⊔ Lc : Subgroup G)).map (A' ⊔ Lc).subtype with hR
  have hRT : CFSG.ABGLocalTools.IsSylowOf 3 R (A' ⊔ Lc) := ⟨Q, rfl⟩
  have hA'R : A' ≤ R := fun x hx =>
    ⟨⟨x, le_sup_left (a := A') hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  set S := R ⊓ Lc with hS
  have hSLc : CFSG.ABGLocalTools.IsSylowOf 3 S Lc := hRT.inf_of_le_normalizer le_sup_right hTK
  obtain ⟨y, hyLc, hSy⟩ :=
    exists_map_conj_eq_of_isSylowOf (SylowFusion.isSylowOf_lc h1812 h184 hH) hSLc
  have hmemS : ∀ s ∈ S, ∃ b ∈ B, s = y * b * y⁻¹ := by
    intro s hs
    rw [hSy] at hs
    obtain ⟨b, hb, rfl⟩ := hs
    exact ⟨b, hb, rfl⟩
  have hS3 : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    obtain ⟨b, hb, rfl⟩ := hmemS s hs
    rw [conj_pow, hA3 b hb.1, mul_one, mul_inv_cancel]
  have hSab : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    obtain ⟨b, hb, rfl⟩ := hmemS s hs
    obtain ⟨b', hb', rfl⟩ := hmemS t ht
    calc y * b * y⁻¹ * (y * b' * y⁻¹) = y * (b * b') * y⁻¹ := by group
      _ = y * (b' * b) * y⁻¹ := by rw [hAab b hb.1 b' hb'.1]
      _ = y * b' * y⁻¹ * (y * b * y⁻¹) := by group
  have hS9 : Nat.card S = 9 := by
    rw [hSy, Subgroup.card_map_of_injective (MulAut.conj y).injective, hB9]
  have hSLc' : S ≤ Lc := inf_le_right
  obtain ⟨e, heS, he1, hecomm⟩ : ∃ e ∈ S, e ≠ 1 ∧ ∀ x ∈ A', x * e = e * x := by
    have hSR : S ≤ R := inf_le_left
    have hRS : R ≤ Subgroup.normalizer (S : Set G) := fun r hr =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hr, hTK (hRT.le hr)⟩
    haveI : Group.IsNilpotent R := hRT.isPGroup.isNilpotent
    haveI : (S.subgroupOf R).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSR).mpr hRS
    have hSbot : S.subgroupOf R ≠ ⊥ := by
      intro hbot
      have hS1 : S = ⊥ := by
        rw [eq_bot_iff]
        intro s hs
        have h1 : (⟨s, hSR hs⟩ : R) ∈ S.subgroupOf R := Subgroup.mem_subgroupOf.mpr hs
        rw [hbot, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
      rw [hS1, Subgroup.card_bot] at hS9
      norm_num at hS9
    obtain ⟨⟨z, hzS, hzZ⟩, hz1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hSbot)
    exact ⟨z, Subgroup.mem_subgroupOf.mp hzS, fun h1 => hz1 (Subtype.ext (Subtype.ext h1)),
      fun x hx => congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨x, hA'R hx⟩)⟩
  have heA' : e ∈ A' := Item183NMProof.mem_of_commute_of_sec18Std h' (hS3 e heS) hecomm
  have heLc : e ∈ Lc := hSLc' heS
  obtain ⟨hLcΓ, hcen⟩ := le_gamma_and_mem_zpowers_of_not_inner hA' hA'N hLcp
    (SylowFusion.nonempty_quotient_lc h184 hH) hcA' hc3 hcLc heA' heLc he1 hnot
  have hLcM' : Lc ≤ M' := hLcΓ.trans hΓM'
  obtain ⟨s, hsA, hH₃, hH₃res⟩ := exists_mem_scriptH_lc h1812 h184 h182 h1842 hH
  have hH₃' : Lc ⊔ A ⊔ (Subgroup.zpowers s ⊔ O) ∈ scriptH A M := hH₃
  have hH₃res' : inSubgroup perfectResidual (Lc ⊔ A ⊔ (Subgroup.zpowers s ⊔ O)) = Lc := hH₃res
  set H'' := (Lc ⊔ A ⊔ (Subgroup.zpowers s ⊔ O)).map (MulAut.conj y).toMonoidHom with hH''def
  have h'' := sec18Std_map_conj h y
  have hH'' : H'' ∈ scriptH (A.map (MulAut.conj y).toMonoidHom)
      (M.map (MulAut.conj y).toMonoidHom) := map_conj_mem_scriptH hH₃' y
  have hyN : y ∈ Subgroup.normalizer (Lc : Set G) := Subgroup.le_normalizer hyLc
  have hH''res : inSubgroup perfectResidual H'' = Lc := by
    rw [hH''def, inSubgroup_perfectResidual_map (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective, hH₃res', Late.map_conj_eq_of_mem_normalizer hyN]
  have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp (hLcC hyLc)
  have hc' : y * c * y⁻¹ = c := by rw [hyc, mul_inv_cancel_right]
  have hsc : c * s = s * c := Subgroup.mem_centralizer_iff.mp hsA c hcA
  have hcx : c * (y * s * y⁻¹) = y * s * y⁻¹ * c := by
    calc c * (y * s * y⁻¹) = y * c * y⁻¹ * (y * s * y⁻¹) := by rw [hc']
      _ = y * (c * s) * y⁻¹ := by group
      _ = y * (s * c) * y⁻¹ := by rw [hsc]
      _ = y * s * y⁻¹ * (y * c * y⁻¹) := by group
      _ = y * s * y⁻¹ * c := by rw [hc']
  have hex : e * (y * s * y⁻¹) = y * s * y⁻¹ * e := by
    obtain ⟨b, hb, hbe⟩ := hmemS e heS
    have hsb : b * s = s * b := Subgroup.mem_centralizer_iff.mp hsA b hb.1
    rw [hbe]
    calc y * b * y⁻¹ * (y * s * y⁻¹) = y * (b * s) * y⁻¹ := by group
      _ = y * (s * b) * y⁻¹ := by rw [hsb]
      _ = y * s * y⁻¹ * (y * b * y⁻¹) := by group
  set D := Subgroup.zpowers c ⊔ Subgroup.zpowers e with hD
  have hDA' : D ≤ A' := sup_le (Subgroup.zpowers_le.mpr hcA') (Subgroup.zpowers_le.mpr heA')
  have hec : e ∉ Subgroup.zpowers c := by
    intro hmem
    have hmem' : e ∈ Subgroup.zpowers c ⊓ Lc := ⟨hmem, heLc⟩
    rw [Sec19.Step1914TriProof.zpowers_inf_eq_bot_of_not_mem hc3 (not_mem_lc h184 hH),
      Subgroup.mem_bot] at hmem'
    exact he1 hmem'
  have hD2 : 2 ≤ CFSG.Open.pRank 3 D :=
    Late.two_le_pRank_of_elemAbelian (CFSG.Open.IsElemAbelian.mono hA'.1 hDA')
      (Sec19.Step1914TriProof.nine_le_card_of_mem_of_not_mem hA' hDA' hc3
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e)) hec)
  have hDM' : Subgroup.normalizer (D : Set G) ≤ M' := (normalizer_le_gamma hDA' hD2).trans hΓM'
  have hysN : y * s * y⁻¹ ∈ Subgroup.normalizer (D : Set G) := by
    have hDC : D ≤ Subgroup.centralizer ({y * s * y⁻¹} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcx))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hex))
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    intro z hz
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hDC hz), mul_inv_cancel_right]
    exact hz
  have hH''M' : H'' ≤ M' := by
    rw [hH''def, Subgroup.map_le_iff_le_comap]
    have hLcM'y : Lc ≤ M'.comap (MulAut.conj y).toMonoidHom := fun l hl =>
      hLcM' ((Subgroup.mem_normalizer_iff.mp hyN l).mp hl)
    refine sup_le (sup_le hLcM'y (hAeq.le.trans (sup_le ?_ (hBLc.trans hLcM'y))))
      (sup_le ?_ ((CFSG.LieType.BorelTits.pCoreOf_le 2 Lc).trans hLcM'y))
    · rw [Subgroup.zpowers_le]
      show y * c * y⁻¹ ∈ M'
      rw [hc']
      exact hA'M' hcA'
    · rw [Subgroup.zpowers_le]
      show y * s * y⁻¹ ∈ M'
      exact hDM' hysN
  obtain ⟨K, hK, -, hKalt⟩ :=
    Rem187Bypass.exists_mem_oTwoComponentsIn_of_item4443 h4443 h'' hH'' hH''M' hM'top
  rw [hH''res] at hKalt
  rcases hKalt with hKeq | ⟨⟨eL⟩, J, hJ, hLcM'eq, ⟨eK⟩, -⟩
  swap
  · exact false_of_alt2_of_centralizer_le hLcM' hLcp hK hJ eL hLcM'eq eK (hA'M' hcA')
      (hCN (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) (pow_three_eq_one_of_sec18H hH)
      hcLc hCN
  have hO2M'Lc : CFSG.Open.pCoreOf 2 M' ⊓ Lc ≤ O :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M' (hLcM' hx), Subgroup.le_normalizer hx⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M').to_le inf_le_left)
  have hLcK : Lc ≤ K := hKeq ▸ le_sup_left
  have hSC : ∀ b ∈ S, (∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M') → b = 1 := by
    intro b hb hbk
    have hbLc : b ∈ Lc := hSLc' hb
    have hbO : b ∈ O := SylowFusion.mem_pCoreOf_of_forall_mem hZ hbLc fun x hx =>
      hO2M'Lc ⟨hbk x (hLcK hx),
        Lc.mul_mem (Lc.mul_mem (Lc.mul_mem hbLc hx) (Lc.inv_mem hbLc)) (Lc.inv_mem hx)⟩
    exact eq_one_of_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lc) hbO
      (hS3 b hb)
  have hM'K : M' ≤ Subgroup.normalizer (K : Set G) := fun w hw =>
    Rem187QProof.mem_normalizer_of_localRank
      (pCoreOf_ne_bot_of_isMaximalTwoLocal h'.mem_scriptM.1) hK (hSLc'.trans hLcK) hS3 hSab hS9
      hSC h.toTheoremFourHyp.localRank_three.le hw
  have hO2KM' : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 M' :=
    pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK
  have hM'O : M' ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M' : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M'
  have hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M' := by
    intro k hk
    have hLcON : Lc ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
      hLcK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    have hk' : k ∈ ((Lc ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) := by
      rw [← hKeq]
      exact hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLcON] at hk'
    obtain ⟨l, hl, o, ho, rfl⟩ := hk'
    have hlc : c * l = l * c := (Subgroup.mem_centralizer_singleton_iff.mp (hLcC hl)).symm
    have hoM : o ∈ CFSG.Open.pCoreOf 2 M' := hO2KM' ho
    have h1 : c * o * c⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 M' :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hM'O (hA'M' hcA')) o).mp hoM)
        (Subgroup.inv_mem _ hoM)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hM'O (hLcM' hl)) _).mp h1
    convert h2 using 1
    calc c * (l * o) * c⁻¹ * (l * o)⁻¹ = c * l * o * c⁻¹ * o⁻¹ * l⁻¹ := by group
      _ = l * (c * o * c⁻¹ * o⁻¹) * l⁻¹ := by rw [hlc]; group
  have hWc : ∀ w ∈ Subgroup.normalizer (A' : Set G), w * c * w⁻¹ ∈ Subgroup.zpowers c := by
    intro w hw
    have hwM' : w ∈ M' := hWM' hw
    have hwK : w ∈ Subgroup.normalizer (K : Set G) := hM'K hwM'
    have hwc : w * c * w⁻¹ ∈ A' := (Subgroup.mem_normalizer_iff.mp hw c).mp hcA'
    refine hcen _ hwc fun x hx => ?_
    have hx' : w⁻¹ * x * w ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwK) x).mp (hLcK hx)
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hM'O hwM') _).mp (hcK _ hx')
    have h2 : w * c * w⁻¹ * x * (w * c * w⁻¹)⁻¹ * x⁻¹ ∈ Lc :=
      Lc.mul_mem ((Subgroup.mem_normalizer_iff.mp (hA'N hwc) x).mp hx) (Lc.inv_mem hx)
    have h3 : w * c * w⁻¹ * x * (w * c * w⁻¹)⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 M' := by
      convert h1 using 1
      group
    exact hO2M'Lc ⟨h3, h2⟩
  have hWd : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (g * c * g⁻¹) : Set G) := by
    intro w hw
    have hw' : g⁻¹ * w * g ∈ Subgroup.normalizer (A' : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hmemA', hmemA', show g * (g⁻¹ * w * g * x * (g⁻¹ * w * g)⁻¹) * g⁻¹ =
        w * (g * x * g⁻¹) * w⁻¹ by group]
      exact Subgroup.mem_normalizer_iff.mp hw _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hWc _ hw')
    have hwd : w * (g * c * g⁻¹) * w⁻¹ ∈ Subgroup.zpowers (g * c * g⁻¹) := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
      rw [conj_zpow, hj]
      group
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hwd i
  have hP := planeQ8_of_sec18H h1812 h184 hH
  have hcard_d : Nat.card (Subgroup.zpowers (g * c * g⁻¹)) = 3 := by
    rw [Nat.card_zpowers, ← hc3]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
  rcases Sec13.eq_of_le_of_le_normalizer hP.isElemAbelian hP.card_eq hP.mem hP.eq_sup hP.not_mem
      hP.card_plane hP.commute hP.irreducible (Subgroup.zpowers_le.mpr hd)
      (hP.le_normalizer.trans hWd) hP.le_normalizer_plane with h0 | hdc | hdB | hdA
  · rw [h0, Subgroup.card_bot] at hcard_d
    norm_num at hcard_d
  swap
  · rw [hdB, hP.card_plane] at hcard_d
    norm_num at hcard_d
  swap
  · rw [hdA, hP.card_eq] at hcard_d
    norm_num at hcard_d
  have hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    exact hdc
  have hgiN : g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers c ⊔ Lc : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨Subgroup.inv_mem _ hgN,
      normalizer_zpowers_le_normalizer_lc h1842 hH (Subgroup.inv_mem _ hgN)⟩
  apply hnot
  intro x hx
  apply inducesInnerMod_of_mem_sup hLcC
  have hgx : g * x * g⁻¹ ∈ Subgroup.zpowers c ⊔ Lc :=
    (hAeq.le.trans (sup_le_sup_left hBLc _)) ((hmemA' x).mp hx)
  have h1 := (Subgroup.mem_normalizer_iff.mp hgiN _).mp hgx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

end SylowInner

theorem item184_4_of_item4443
    (h4443 : Sec4.Item4_44_3) (h1812 : Item181_2) (h184 : Item184_1) (h182 : Item182Alt1C) :
    Item184_4 :=
  item184_4_of h1812 h184 (item184_2_of h1812 h184 h182)
    (SylowInner.claim1844Inner_of h4443 h1812 h184 h182)

end CFSG.RankThree.PartTwo.Sec18
