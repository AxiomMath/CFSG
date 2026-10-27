module

public import CFSG.RankThree.PartTwo.Sec20.OneFrontierCleanStatements
import CFSG.RankThree.PartTwo.Sec18.SylowFiveAct
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
import CFSG.RankThree.PartTwo.Sec18.Item1810Act
import CFSG.RankThree.PartTwo.Sec18.Item1810Cent
import CFSG.RankThree.PartTwo.Sec18.Item1810Core
import CFSG.RankThree.PartTwo.Sec18.Item1810Group
import CFSG.RankThree.PartTwo.Sec18.Item1810Weak
import CFSG.RankThree.PartTwo.Sec11.Item113

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

section Certified


variable {A M H : Subgroup G} {c : G}

omit [Finite G] in
private theorem isElemAbelian_of_le {E B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hEB : E ≤ B) : CFSG.Assembly.IsElemAbelian 3 E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => hB.2 y (hEB hy)⟩
  have h := hB.1.is_comm.comm ⟨a, hEB a.2⟩ ⟨b, hEB b.2⟩
  have h2 : (a : G) * b = b * a := congrArg Subtype.val h
  exact h2

theorem conjugatesIn_eq_of_le_normalizer_zpowers (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (h1844 : Item184_4) (h1846 : Item184_6) (hH : Sec18H G A M H c)
    (hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (A : Set G))) :
    conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hcA := (mem_and_commutator_mem_of_sec18H hH).1
  have hc3 := orderOf_eq_three_of_sec18H h184 hH
  have hc3' := pow_three_eq_one_of_sec18H hH
  have hPW : P ≤ Subgroup.normalizer (A : Set G) := hP.le
  have hPp : IsPGroup 3 P := hP.isPGroup
  have hPC : P ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec11.le_centralizer_of_le_normalizer_zpowers hc3 hPp (hPW.trans hWc)
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAP : A ≤ P := by
    obtain ⟨k, hk, hkA⟩ :=
      Item1810Proof.exists_conj_le_of_isSylowOf hP (Subgroup.le_normalizer (H := A)) hAp
    intro a ha
    have h1 := hkA (k * a * k⁻¹) ((Subgroup.mem_normalizer_iff.mp hk a).mp ha)
    have e : k⁻¹ * (k * a * k⁻¹) * k = a := by group
    rwa [e] at h1
  have hself : ∀ y : G, y ^ 3 = 1 → (∀ a ∈ A, a * y = y * a) → y ∈ A :=
    fun y hy hyA => Item183NMProof.mem_of_commute_of_sec18Std hH.toSec18Std hy hyA
  have hF2 : ∀ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ A →
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c := by
    intro g hg
    have hmem : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ∈
        conjugatesIn (Subgroup.zpowers c) A := ⟨⟨g, rfl⟩, hg⟩
    rw [h1844 G A M H c hH] at hmem
    obtain ⟨w, hw, hweq⟩ := hmem
    exact hweq.trans (Item1810Proof.map_conj_eq_self (hWc hw))
  obtain ⟨hΩ, hcΦ⟩ := SylowFive.omegaOne_of_le_normalizer_zpowers h1812 h184 h1842 hH hP hWc
  have hAX : A ≤ omegaOneThree P := Item1810Proof.le_omegaOneThree hAP hA.1.2
  ext F
  rw [Set.mem_singleton_iff]
  constructor
  swap
  · rintro rfl
    exact ⟨⟨1, (Item1810Proof.map_conj_eq_self (Subgroup.one_mem _)).symm⟩,
      Subgroup.zpowers_le.mpr (hAP hcA)⟩
  rintro ⟨⟨g, rfl⟩, hFP⟩
  by_contra hne
  obtain ⟨d, hd⟩ : ∃ d, g * c * g⁻¹ = d := ⟨_, rfl⟩
  have hFd : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers d := by
    rw [MonoidHom.map_zpowers, ← hd]
    rfl
  have hdP : d ∈ P := hFP (hFd ▸ Subgroup.mem_zpowers d)
  have hd3 : d ^ 3 = 1 := by rw [← hd, conj_pow, hc3', mul_one, mul_inv_cancel]
  have hdA : d ∉ A := fun h => hne (hF2 g (by rw [hFd]; exact Subgroup.zpowers_le.mpr h))
  have hdΩ : d ∈ omegaOneThree P := Subgroup.subset_closure ⟨hdP, hd3⟩
  rcases hΩ with hE | hZ
  · have hAeq : A = omegaOneThree P := Subgroup.eq_of_le_of_card_ge hAX (by rw [hE.2, hA.2])
    exact hdA (hAeq ▸ hdΩ)
  set X := omegaOneThree P with hX
  obtain ⟨hX81, hXexp⟩ := Item1810Proof.card_and_pow_three_of_isZ3TimesHeis hZ
  have hXp : IsPGroup 3 X := IsPGroup.of_card (n := 4) (by rw [hX81]; norm_num)
  have hexp : ∀ a ∈ A, (a * d) ^ 3 = 1 := fun a ha => hXexp _ (X.mul_mem (hAX ha) hdΩ)
  have hnc : ∃ a ∈ A, a * d ≠ d * a := by
    by_contra h
    push_neg at h
    exact hdA (hself d hd3 h)
  have hE9 := Item1810Proof.card_inf_centralizer_eq_nine hA.1 hA.2 (hPW hdP) hd3 hexp hnc
  set E := A ⊓ Subgroup.centralizer ({d} : Set G) with hEdef
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := isElemAbelian_of_le hA.1 inf_le_left
  obtain ⟨hDab, hDcard⟩ :=
    Item1810Proof.sup_zpowers_isElemAbelian hEab inf_le_right hd3 fun h => hdA h.1
  set D := E ⊔ Subgroup.zpowers d with hDdef
  have hD27 : Nat.card D = 27 := by rw [hDcard, hE9]
  have hcE : c ∈ E :=
    ⟨hcA, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hPC hdP)).symm⟩
  have hcD : c ∈ D := Subgroup.mem_sup_left hcE
  have hdD : d ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hDP : D ≤ P := sup_le (inf_le_left.trans hAP) (Subgroup.zpowers_le.mpr hdP)
  have hDX : D ≤ X := Item1810Proof.le_omegaOneThree hDP hDab.2
  obtain ⟨hAND, hAD9⟩ := Item1810Proof.le_normalizer_and_card_inf hX81 hAX hDX hA.2 hD27
    fun h => hdA (h ▸ hdD)
  have hPG := h1846 G A M H c hH P hP
  have hSC : P.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({d} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    have h1 : p * c = c * p := Subgroup.mem_centralizer_singleton_iff.mp (hPC hp)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hd]
    change g * p * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * p * g⁻¹)
    calc g * p * g⁻¹ * (g * c * g⁻¹) = g * (p * c) * g⁻¹ := by group
      _ = g * (c * p) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * (g * p * g⁻¹) := by group
  have hSG : CFSG.ABGLocalTools.IsSylowOf 3 (P.map (MulAut.conj g).toMonoidHom) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hPG.card_eq)
  have hDCd : D ≤ Subgroup.centralizer ({d} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hDab.1.is_comm.comm ⟨y, hy⟩ ⟨d, hdD⟩))
  have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 3) (by rw [hD27]; norm_num)
  obtain ⟨k, hk, hkD⟩ :=
    Item1810Proof.exists_conj_le_of_isSylowOf (hSG.of_le hSC le_top) hDCd hDp
  have hxd : d = k * g * c * (k * g)⁻¹ := by
    have h1 : k * d = d * k := Subgroup.mem_centralizer_singleton_iff.mp hk
    calc d = k * d * k⁻¹ := by rw [h1]; group
      _ = k * g * c * (k * g)⁻¹ := by rw [← hd]; group
  have hDxP : D ≤ P.map (MulAut.conj (k * g)).toMonoidHom := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := hkD q hq
    refine ⟨p, hp, ?_⟩
    have hpq' : g * p * g⁻¹ = k⁻¹ * q * k := hpq
    change k * g * p * (k * g)⁻¹ = q
    calc k * g * p * (k * g)⁻¹ = k * (g * p * g⁻¹) * k⁻¹ := by group
      _ = k * (k⁻¹ * q * k) * k⁻¹ := by rw [hpq']
      _ = q := by group
  set x := k * g with hxdef
  have hBX : A.map (MulAut.conj x).toMonoidHom ≤
      omegaOneThree (P.map (MulAut.conj x).toMonoidHom) := by
    rw [Item1810Proof.omegaOneThree_map_conj]
    exact Subgroup.map_mono hAX
  have hDX' : D ≤ omegaOneThree (P.map (MulAut.conj x).toMonoidHom) :=
    Item1810Proof.le_omegaOneThree hDxP hDab.2
  have hX'81 : Nat.card (omegaOneThree (P.map (MulAut.conj x).toMonoidHom)) = 81 := by
    rw [Item1810Proof.omegaOneThree_map_conj,
      Subgroup.card_map_of_injective (MulAut.conj x).injective, ← hX, hX81]
  have hB27 : Nat.card (A.map (MulAut.conj x).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hA.2]
  have hcB : c ∉ A.map (MulAut.conj x).toMonoidHom := by
    rintro ⟨a, ha, hac⟩
    apply hne
    have hac' : x * a * x⁻¹ = c := hac
    have h1 : (Subgroup.zpowers c).map (MulAut.conj x⁻¹).toMonoidHom = Subgroup.zpowers c := by
      refine hF2 x⁻¹ ?_
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      have e : (MulAut.conj x⁻¹).toMonoidHom c = a := by
        change x⁻¹ * c * x⁻¹⁻¹ = a
        rw [← hac']
        group
      rw [e]
      exact ha
    have h2 : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      simpa using (Subgroup.normalizer _).inv_mem
        (Item1810Proof.mem_normalizer_of_map_conj_eq_self h1)
    have h3 := Item1810Proof.map_conj_eq_self h2
    rw [MonoidHom.map_zpowers] at h3
    rw [hFd, hxd]
    exact h3
  obtain ⟨hBND, hBD9⟩ := Item1810Proof.le_normalizer_and_card_inf hX'81 hBX hDX' hB27 hD27
    fun h => hcB (h ▸ hcD)
  have hcomm : ∀ a ∈ A, ∀ e ∈ D, a * e * a⁻¹ * e⁻¹ ≠ c := by
    intro a ha e he hae
    apply hcΦ
    rw [← hae]
    exact Item1810Proof.commutator_mem_frattini hXp (hAX ha) (hDX he)
  exact Item1810Proof.false_of_transvection_pair hDab hD27 hA.1 hA.2 hAND hBND hAD9 hBD9 rfl
    hxd hcA hcD hdD hcB hdA hself hWc
    (fun R hR hAR g hg =>
      Item1810Proof.map_conj_eq_of_isPGroup h1812 h184 h1842 h1844 h1846 hH hWc hR hAR hg)
    hcomm

theorem item1810Hyp_of_item189 (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2)
    (h1844 : Item184_4) (h1846 : Item184_6) (h189 : Item189) : Item1810Hyp := by
  intro G _ _ A M H c hH h187 P hP
  exact conjugatesIn_eq_of_le_normalizer_zpowers h1812 h184 h1842 h1844 h1846 hH
    (h189 G A M H c hH h187).2.1 hP

end Certified

end CFSG.RankThree.PartTwo.Sec18
