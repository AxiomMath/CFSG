module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.ModelSylow
public import CFSG.Quasithin.Background.F6SQTK
import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompPSL2A
import CFSG.LocalAnalysis.GH72.PGammaL2Permutable
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAction
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Vol2.Ch12Sec6KGComp
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open Subgroup CFSG.Quasithin
open CFSG.BenderSuzuki.MatrixGroups
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {p e : ℕ}

private theorem mem_normalizer_zpowers_of_conj {G : Type*} [Group G] {u m : G}
    (h : m * u * m⁻¹ = u ∨ m * u * m⁻¹ = u⁻¹) :
    m ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (m * u * m⁻¹) = Subgroup.zpowers u
  rcases h with h | h
  · rw [h]
  · rw [h, Subgroup.zpowers_inv]

private theorem overgroup_eq_top_or_le_normalizer
    {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq11 : 11 ≤ p ^ f)
    {M : Subgroup (PSL2MatrixGroup F)} {u : PSL2MatrixGroup F} (huM : u ∈ M)
    (hu : orderOf u = (p ^ f + 1) / 2) :
    M = ⊤ ∨ ∀ m ∈ M,
      m ∈ Subgroup.normalizer (Subgroup.zpowers u : Set (PSL2MatrixGroup F)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hodd : Odd (p ^ f) := (hp.out.odd_of_ne_two hp2).pow
  have hn6 : 6 ≤ (p ^ f + 1) / 2 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hcop : Nat.Coprime p ((p ^ f + 1) / 2) :=
    CFSG.Glauberman.Dickson.MaxUp.coprime_half_add hp2 hf0
  have hcop2 : Nat.Coprime ((p ^ f + 1) / 2) ((p ^ f - 1) / 2) := by
    obtain ⟨j, hj⟩ := hodd
    have h1 : (p ^ f + 1) / 2 = j + 1 := by omega
    have h2 : (p ^ f - 1) / 2 = j := by omega
    rw [h1, h2, Nat.coprime_comm]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right j)
  have hord6 : 2 < orderOf u := by rw [hu]; omega
  have hnorm : ∀ m ∈ M, (m * u * m⁻¹ = u ∨ m * u * m⁻¹ = u⁻¹) →
      m ∈ Subgroup.normalizer (Subgroup.zpowers u : Set (PSL2MatrixGroup F)) :=
    fun m _ h => mem_normalizer_zpowers_of_conj h
  have hcomm_case : ∀ {x : PSL2MatrixGroup F}, x ∈ M → (∀ y ∈ M, x * y = y * x) →
      x ∈ Subgroup.normalizer (Subgroup.zpowers u : Set (PSL2MatrixGroup F)) := by
    intro x hx hc
    refine hnorm x hx (Or.inl ?_)
    rw [hc u huM]
    group
  rcases CFSG.Glauberman.Dickson.MaxUp.overgroup_shapes hF hp2 M with
    ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨⟨z, hzc, hz⟩, hc⟩ | ⟨-, hord, -⟩ | ⟨-, -, hord⟩ | ⟨-, -, hord⟩ |
      ⟨⟨m, t, hcard, ht⟩, -⟩ | ⟨m, hm0, hdivf, hcard, hbound⟩ |
      ⟨m, hm0, hm2f, hcard, hbound⟩
  · exact Or.inr fun m hm => hcomm_case hm (hc m hm)
  · exact Or.inr fun m hm => hcomm_case hm (hc m hm)
  ·
    refine Or.inr fun m hm => ?_
    by_cases h1 : 2 < orderOf m
    · exact hnorm m hm (Or.inl (by rw [hc m hm u huM h1 hord6]; group))
    · by_cases h2 : 2 < orderOf (m * u)
      · have hcomm : (m * u) * u = u * (m * u) := hc (m * u) (M.mul_mem hm huM) u huM h2 hord6
        have hmu : m * u = u * m := by
          have h3 : (m * u) * u = (u * m) * u := by
            calc (m * u) * u = u * (m * u) := hcomm
              _ = (u * m) * u := by group
          exact mul_right_cancel h3
        exact hnorm m hm (Or.inl (by rw [hmu]; group))
      · have hm2 : m * m = 1 := by
          have hpos : 0 < orderOf m := orderOf_pos m
          have ho : orderOf m = 1 ∨ orderOf m = 2 := by omega
          rcases ho with h | h
          · have hm1 : m = 1 := by rwa [← orderOf_eq_one_iff]
            rw [hm1, one_mul]
          · have := pow_orderOf_eq_one m
            rwa [h, pow_two] at this
        have hmu2 : (m * u) * (m * u) = 1 := by
          have hpos : 0 < orderOf (m * u) := orderOf_pos (m * u)
          have ho : orderOf (m * u) = 1 ∨ orderOf (m * u) = 2 := by omega
          rcases ho with h | h
          · have hm1 : m * u = 1 := by rwa [← orderOf_eq_one_iff]
            rw [hm1, mul_one]
          · have := pow_orderOf_eq_one (m * u)
            rwa [h, pow_two] at this
        have h1' : (m * u * m) * u = 1 := by
          rw [← hmu2]; group
        have h2' : m * u * m = u⁻¹ := eq_inv_of_mul_eq_one_left h1'
        have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_left hm2
        exact hnorm m hm (Or.inr (by rw [hminv, h2']))
  · exfalso
    rcases hord u huM with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  · exfalso
    rcases hord u huM with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  · exfalso
    rcases hord u huM with h | h | h <;>
      exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  ·
    exfalso
    have hdvd0 : orderOf u ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M huM
    have hdvd' : (p ^ f + 1) / 2 ∣ p ^ m * t := by
      rw [← hu, ← hcard]; exact hdvd0
    have hcop' : Nat.Coprime ((p ^ f + 1) / 2) (p ^ m) :=
      Nat.Coprime.pow_right m hcop.symm
    have hnt : (p ^ f + 1) / 2 ∣ t := hcop'.dvd_of_dvd_mul_left hdvd'
    have hd1 : (p ^ f + 1) / 2 ∣ 1 := by
      have hg : (p ^ f + 1) / 2 ∣ Nat.gcd ((p ^ f + 1) / 2) ((p ^ f - 1) / 2) :=
        Nat.dvd_gcd (dvd_refl _) (hnt.trans ht)
      rwa [Nat.coprime_iff_gcd_eq_one.mp hcop2] at hg
    exact absurd (Nat.le_of_dvd one_pos hd1) (by omega)
  ·
    by_cases hmfeq : m = f
    · subst hmfeq
      refine Or.inl (Subgroup.eq_top_of_card_eq M ?_)
      rw [hcard, CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF hp2, mul_comm 2 m, pow_mul]
    · exfalso
      have h2m : 2 * m ≤ f :=
        CFSG.Glauberman.Dickson.MaxUp.two_mul_le_of_dvd_of_ne hdivf hmfeq hf0
      obtain ⟨k, rfl⟩ := hdivf
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hk2 : 2 ≤ k := by
        rw [mul_comm 2 m] at h2m
        exact Nat.le_of_mul_le_mul_left h2m (by omega)
      have hpm3 : 3 ≤ p ^ m := by
        have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
        have hle : p ≤ p ^ m := by
          simpa using Nat.pow_le_pow_right hp.out.pos hm1
        exact le_trans hp3 hle
      have hge : (p ^ m) * (p ^ m) ≤ p ^ (m * k) := by
        rw [pow_mul]
        calc (p ^ m) * (p ^ m) = (p ^ m) ^ 2 := by ring
          _ ≤ (p ^ m) ^ k := Nat.pow_le_pow_right (by omega) hk2
      have hA : 2 * (p ^ m + 1) < (p ^ m) * (p ^ m) := by nlinarith
      have hkey : 2 * (p ^ m + 1) < p ^ (m * k) + 1 := by nlinarith
      have hlt : p ^ m + 1 < (p ^ (m * k) + 1) / 2 := by omega
      exact absurd (hu ▸ hbound u huM) (by omega)
  ·
    exfalso
    obtain ⟨k, hk⟩ := hm2f
    have hk1 : 0 < k := by
      rcases k with _ | k
      · rw [mul_zero] at hk; exact absurd hk hf0
      · omega
    have h2m : 2 * m ≤ f := by
      rw [hk]
      exact Nat.le_mul_of_pos_right (2 * m) hk1
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hpm3 : 3 ≤ p ^ m := by
      have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
      have hle : p ≤ p ^ m := by
        simpa using Nat.pow_le_pow_right hp.out.pos hm1
      exact le_trans hp3 hle
    have h1 : p ^ m * p ^ m ≤ p ^ f := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right hp.out.pos (by omega)
    have hA : 2 * (p ^ m + 1) < (p ^ m) * (p ^ m) := by nlinarith
    have hkey : 2 * (p ^ m + 1) < p ^ f + 1 := by nlinarith
    have hlt : p ^ m + 1 < (p ^ f + 1) / 2 := by omega
    exact absurd (hu ▸ hbound u huM) (by omega)

private theorem exists_conj_not_mem_normalizer_nonsplit
    {F : Type} [Field F] [Finite F] {p e : ℕ} [hp : Fact p.Prime]
    (hF : Nat.card F = p ^ e) (hp2 : p ≠ 2) (hq9 : 9 < p ^ e) {ν : F} (hν : ¬ IsSquare ν)
    {t : PSL2MatrixGroup F} (ht : orderOf t = 2) :
    ∃ d : PSL2MatrixGroup F, d * t * d⁻¹ ∉
      Subgroup.normalizer (CFSG.PSL2Table.nonsplitTorus ν : Set (PSL2MatrixGroup F)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hqcard : Fintype.card F = p ^ e := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hq5 : 5 ≤ Fintype.card F := by rw [hqcard]; omega
  have ht1 : t ≠ 1 := by intro h; rw [h, orderOf_one] at ht; omega
  have hsimple : IsSimpleGroup (PSL2MatrixGroup F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF]; omega)
  have hTcoatom : IsCoatom
      (Subgroup.normalizer (CFSG.PSL2Table.nonsplitTorus ν : Set (PSL2MatrixGroup F))) :=
    CFSG.Glauberman.Dickson.MaxUp.isCoatom_normalizer_nonsplitTorus hF hp2 (by omega)
      (by omega) (by omega) hν
  by_contra hcon
  push Not at hcon
  have hKle : Subgroup.normalClosure ({t} : Set (PSL2MatrixGroup F)) ≤
      Subgroup.normalizer
        (CFSG.PSL2Table.nonsplitTorus ν : Set (PSL2MatrixGroup F)) := by
    show Subgroup.closure (Group.conjugatesOfSet ({t} : Set _)) ≤ _
    rw [Subgroup.closure_le]
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hyz
    exact hcon c
  have hKtop : Subgroup.normalClosure ({t} : Set (PSL2MatrixGroup F)) = ⊤ := by
    apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
    simp [ht1]
  exact hTcoatom.1 (top_le_iff.mp (by rw [← hKtop]; exact hKle))

private theorem exists_three_conj_closure_eq_psl2 {F : Type}
    [Field F] [Finite F] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e)
    (hq9 : 9 < p ^ e) {t : PSL2MatrixGroup F} (ht : orderOf t = 2) :
    ∃ x y z : PSL2MatrixGroup F,
      Subgroup.closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (PSL2MatrixGroup F)) =
        ⊤ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := CFSG.Glauberman.Dickson.MaxUp.ringChar_ne_two hF hp2
  have hqcard : Fintype.card F = p ^ e := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hq5 : 5 ≤ Fintype.card F := by rw [hqcard]; omega
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, pow_zero] at hq9; omega
    · exact h
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    CFSG.ComponentClassification.AutL2Facts.isOddPrimePower_of hp hp2 he1 hF
  have hq11 : 11 ≤ p ^ e := by
    obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := e)
    omega
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF2
  obtain ⟨w, hwS, hww, hinv, -⟩ :=
    CFSG.Glauberman.Dickson.MaxStructure.normalizer_nonsplitTorus_eq hF2 hq5 hν
  have hw1 : w ≠ 1 := fun h => hwS (h ▸ (CFSG.PSL2Table.nonsplitTorus ν).one_mem)
  have hwinv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hww).symm
  set T : Subgroup (PSL2MatrixGroup F) := CFSG.PSL2Table.nonsplitTorus ν with hT
  have hTcyc : IsCyclic ↥T := CFSG.Glauberman.Dickson.MaxStructure.nonsplitTorus_isCyclic hν
  obtain ⟨u₀, hu₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥T)
  set u : PSL2MatrixGroup F := ((u₀ : ↥T) : PSL2MatrixGroup F) with hu_def
  have hu_mem : u ∈ T := u₀.2
  have hu_card : Nat.card ↥T = (p ^ e + 1) / 2 := by
    rw [hT, CFSG.Glauberman.Dickson.MaxStructure.card_nonsplitTorus_eq hF2 hν, hqcard]
  have huord : orderOf u = (p ^ e + 1) / 2 := by
    rw [hu_def, Subgroup.orderOf_coe, hu₀, hu_card]
  have hgen : Subgroup.zpowers u = T := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu_mem) ?_
    rw [Nat.card_zpowers, huord, ← hu_card]
  have hs2 : (w * u) * (w * u) = 1 := by
    have h1 : w * u * w⁻¹ = u⁻¹ := hinv u hu_mem
    calc (w * u) * (w * u) = (w * u * w) * u := by group
      _ = (w * u * w⁻¹) * u := by rw [hwinv]
      _ = u⁻¹ * u := by rw [h1]
      _ = 1 := inv_mul_cancel u
  have hs2_ne : w * u ≠ 1 := by
    intro h
    apply hwS
    have h1 : w = u⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    exact T.inv_mem hu_mem
  have ht2 : t ^ 2 = 1 := by have h := pow_orderOf_eq_one t; rwa [ht] at h
  have ht1 : t ≠ 1 := by intro h; rw [h, orderOf_one] at ht; omega
  obtain ⟨a, ha⟩ := CFSG.GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F hodd
    w t ⟨hw1, by rw [pow_two]; exact hww⟩ ⟨ht1, ht2⟩
  obtain ⟨b, hb⟩ := CFSG.GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F hodd
    (w * u) t ⟨hs2_ne, by rw [pow_two]; exact hs2⟩ ⟨ht1, ht2⟩
  have hx1 : a⁻¹ * t * a = w := by rw [← ha]; group
  have hy1 : b⁻¹ * t * b = w * u := by rw [← hb]; group
  obtain ⟨d, hd⟩ := exists_conj_not_mem_normalizer_nonsplit hF hp2 hq9 hν ht
  have hNT : Subgroup.normalizer (CFSG.PSL2Table.nonsplitTorus ν : Set (PSL2MatrixGroup F)) =
      Subgroup.normalizer (Subgroup.zpowers u : Set (PSL2MatrixGroup F)) := by
    rw [hgen, hT]
  rw [hNT] at hd
  set M : Subgroup (PSL2MatrixGroup F) :=
    Subgroup.closure ({a⁻¹ * t * a, b⁻¹ * t * b, d * t * d⁻¹} : Set (PSL2MatrixGroup F)) with hM
  have huM : u ∈ M := by
    have h1 : a⁻¹ * t * a ∈ M := Subgroup.subset_closure (by simp)
    have h2 : b⁻¹ * t * b ∈ M := Subgroup.subset_closure (by simp)
    have h3 : (a⁻¹ * t * a) * (b⁻¹ * t * b) = u := by
      rw [hx1, hy1, ← mul_assoc, hww, one_mul]
    rw [← h3]
    exact M.mul_mem h1 h2
  rcases overgroup_eq_top_or_le_normalizer hF hp2 hq11 huM huord with htop | hle
  · exact ⟨a⁻¹, b⁻¹, d, by simpa only [hM, inv_inv] using htop⟩
  · exact absurd (hle (d * t * d⁻¹) (Subgroup.subset_closure (by simp))) hd

private theorem closure_coe_image_eq_of_map {H G : Type*} [Group H] [Group G] {L : Subgroup G}
    (e : ↥L ≃* H) {s : Set ↥L}
    (h : (Subgroup.closure s).map (e : ↥L →* H) = ⊤) :
    Subgroup.closure ((L.subtype : ↥L → G) '' s) = L := by
  have hs : Subgroup.closure s = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : e v ∈ (Subgroup.closure s).map (e : ↥L →* H) := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨w, hw, hwv⟩ := hv
    rwa [e.injective hwv] at hw
  have h2 : Subgroup.closure ((L.subtype : ↥L → G) '' s) = L := by
    rw [← MonoidHom.map_closure (f := (L.subtype : ↥L →* G)), hs]
    ext x
    constructor
    · intro hx; exact Subgroup.map_subtype_le ⊤ hx
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
  exact h2

private theorem mem_normalizer_zpowers_of_conj_mem {G : Type*} [Group G] [Finite G] {x z : G}
    (hx : z * x * z⁻¹ ∈ Subgroup.zpowers x) :
    z ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers]
  exact le_of_eq (MulEquiv.orderOf_eq (MulAut.conj z) x).symm

private theorem map_mem_normalizer_zpowers {H K : Type*} [Group H] [Finite H] [Group K]
    [Finite K] (ι : H →* K) (_hι : Function.Injective ι) {x z : H}
    (hz : z ∈ Subgroup.normalizer (Subgroup.zpowers x : Set H)) :
    ι z ∈ Subgroup.normalizer (Subgroup.zpowers (ι x) : Set K) := by
  have h1 : (Subgroup.zpowers x).map (MulAut.conj z).toMonoidHom = Subgroup.zpowers x :=
    mem_normalizer_iff_map_conj_eq.mp hz
  have hzx : z * x * z⁻¹ ∈ Subgroup.zpowers x := by
    have h := Subgroup.mem_map_of_mem (f := (MulAut.conj z).toMonoidHom)
      (Subgroup.mem_zpowers x)
    rw [h1] at h
    simpa using h
  refine mem_normalizer_zpowers_of_conj_mem ?_
  have h2 : ι (z * x * z⁻¹) ∈ Subgroup.zpowers (ι x) := by
    have h3 : ι (z * x * z⁻¹) ∈ (Subgroup.zpowers x).map ι := ⟨_, hzx, rfl⟩
    rwa [MonoidHom.map_zpowers] at h3
  rwa [map_mul, map_mul, map_inv] at h2

private theorem pgl2_data_of_isPGL2 {A : Type} [Group A] {q : ℕ}
    (hA : CFSG.Quasithin.F6.IsPGL2 q A) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty (A ≃* CFSG.GorensteinWalter.PGL2 F) := by
  obtain ⟨F, hField, hFin, hcard, ⟨eQ⟩⟩ := hA
  have hcs : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) =
      CFSG.Open.StatedScalars (Fin 2) F := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rfl
  exact ⟨F, hField, hFin, hcard,
    ⟨eQ.trans (QuotientGroup.quotientMulEquivOfEq hcs).symm⟩⟩

private theorem card_range_toPGL {F : Type} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ e) (hp2 : p ≠ 2) :
    Nat.card ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range =
      p ^ e * ((p ^ e) ^ 2 - 1) / 2 := by
  have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup (PSL2MatrixGroup F)))
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  calc Nat.card ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
      = Nat.card ↥((⊤ : Subgroup (PSL2MatrixGroup F)).map
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))) := by
        rw [MonoidHom.range_eq_map]
    _ = Nat.card ↥(⊤ : Subgroup (PSL2MatrixGroup F)) := h
    _ = Nat.card (PSL2MatrixGroup F) := Nat.card_congr Subgroup.topEquiv.toEquiv
    _ = p ^ e * ((p ^ e) ^ 2 - 1) / 2 :=
        CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF hp2

private theorem card_pgl2_eq_two_mul_range {F : Type} [Field F] [Finite F] {p e : ℕ}
    [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e) :
    Nat.card (CFSG.GorensteinWalter.PGL2 F) =
      2 * Nat.card ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  have h2 : 2 ∣ (p ^ e) * ((p ^ e) ^ 2 - 1) := by
    have hev : 2 ∣ (p ^ e) ^ 2 - 1 := by
      obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2 |>.pow (n := e)
      refine ⟨2 * j * j + 2 * j, ?_⟩
      rw [hj]
      have h : (2 * j + 1) ^ 2 = 2 * (2 * j * j + 2 * j) + 1 := by ring
      omega
    exact dvd_mul_of_dvd_right hev _
  rw [card_range_toPGL hF hp2, CFSG.GorensteinWalter.pgl2_card_formula F, hF,
    Nat.mul_div_cancel' h2]

private theorem index_range_toPGL {F : Type} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e) :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.index = 2 := by
  have : Finite (CFSG.GorensteinWalter.PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hcard := Subgroup.card_mul_index
    (H := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
  rw [card_pgl2_eq_two_mul_range hp hp2 hF, mul_comm 2] at hcard
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard

private theorem exists_three_conj_closure_eq_of_mulEquiv {G : Type}
    [Group G] {L : Subgroup G} {F : Type} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e) (hq9 : 9 < p ^ e)
    (e : ↥L ≃* PSL2MatrixGroup F) {t : G} (htL : t ∈ L) (ht : orderOf t = 2) :
    ∃ x ∈ L, ∃ y ∈ L, ∃ z ∈ L,
      Subgroup.closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set G) = L := by
  classical
  have htL' : orderOf (e ⟨t, htL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe (⟨t, htL⟩ : ↥L)]
    exact ht
  obtain ⟨x', y', z', hcl⟩ := exists_three_conj_closure_eq_psl2 hp hp2 hF hq9 htL'
  set xL : ↥L := e.symm x' with hxL
  set yL : ↥L := e.symm y' with hyL
  set zL : ↥L := e.symm z' with hzL
  have hEx : e xL = x' := e.apply_symm_apply x'
  have hEy : e yL = y' := e.apply_symm_apply y'
  have hEz : e zL = z' := e.apply_symm_apply z'
  have htE : e ⟨t, htL⟩ = e (⟨t, htL⟩ : ↥L) := rfl
  have hmap : (Subgroup.closure ({xL * ⟨t, htL⟩ * xL⁻¹, yL * ⟨t, htL⟩ * yL⁻¹,
      zL * ⟨t, htL⟩ * zL⁻¹} : Set ↥L)).map (e : ↥L →* PSL2MatrixGroup F) =
      Subgroup.closure ({x' * e ⟨t, htL⟩ * x'⁻¹, y' * e ⟨t, htL⟩ * y'⁻¹,
        z' * e ⟨t, htL⟩ * z'⁻¹} : Set (PSL2MatrixGroup F)) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext w
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hv with rfl | rfl | rfl <;> simp [hEx, hEy, hEz]
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, Or.inl rfl, by simp [hEx]⟩
      · exact ⟨_, Or.inr (Or.inl rfl), by simp [hEy]⟩
      · exact ⟨_, Or.inr (Or.inr rfl), by simp [hEz]⟩
  refine ⟨(xL : G), xL.2, (yL : G), yL.2, (zL : G), zL.2, ?_⟩
  have hcoe := closure_coe_image_eq_of_map e (s := ({xL * ⟨t, htL⟩ * xL⁻¹,
    yL * ⟨t, htL⟩ * yL⁻¹, zL * ⟨t, htL⟩ * zL⁻¹} : Set ↥L)) (by rw [hmap]; exact hcl)
  have hst : ((L.subtype : ↥L → G) '' ({xL * ⟨t, htL⟩ * xL⁻¹, yL * ⟨t, htL⟩ * yL⁻¹,
      zL * ⟨t, htL⟩ * zL⁻¹} : Set ↥L)) =
      ({xL * t * xL⁻¹, yL * t * yL⁻¹, zL * t * zL⁻¹} : Set G) := by
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hv with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, Or.inl rfl, rfl⟩
      · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
  rw [hst] at hcoe
  exact hcoe

omit [Finite G] in
theorem exists_three_conj_closure_eq (hM : LieModel ↥L .PSL 2 p e)
    (hp2 : p ≠ 2) (hq : 9 < p ^ e) {t : G} (htL : t ∈ L) (ht : orderOf t = 2) :
    ∃ x ∈ L, ∃ y ∈ L, ∃ z ∈ L,
      closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set G) = L := by
  obtain ⟨hp, -, -, -, F, instF, instFin, hFcard, hne⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hM
  let : Field F := instF
  let : Finite F := instFin
  obtain ⟨ε⟩ := hne
  exact exists_three_conj_closure_eq_of_mulEquiv hp hp2 hFcard hq ε htL ht

private theorem pgl2_exists_inverted {F : Type} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e) (hq9 : 9 < p ^ e)
    {t : CFSG.GorensteinWalter.PGL2 F} (ht : orderOf t = 2)
    (_htR : t ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    ∃ u' : PSL2MatrixGroup F, orderOf u' = (p ^ e + 1) / 2 ∧
      t * Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u' * t⁻¹ =
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u')⁻¹ := by
  classical
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, pow_zero] at hq9; omega
    · exact h
  have h3 : 3 < Nat.card F := by rw [hF]; omega
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    CFSG.ComponentClassification.AutL2Facts.isOddPrimePower_of hp hp2 he1 hF
  have ht2 : t ^ 2 = 1 := by have h := pow_orderOf_eq_one t; rwa [ht] at h
  have ht1 : t ≠ 1 := by intro h; rw [h, orderOf_one] at ht; omega
  obtain ⟨x, hxord, hxinv⟩ :=
    CFSG.Quasithin.H13.S126C.exists_pglAction_inv_nonsplit hodd h3 ⟨ht1, ht2⟩
  refine ⟨x, by rw [hxord, hF], ?_⟩
  have h := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.toPGL_pglAction F t x
  rw [hxinv, map_inv] at h
  exact h.symm

private theorem pgl2_exists_conj_mul {F : Type} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e) (hq9 : 9 < p ^ e)
    {t : CFSG.GorensteinWalter.PGL2 F} (ht : orderOf t = 2)
    (htR : t ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    {u' : PSL2MatrixGroup F}
    (hinv : t * Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u' * t⁻¹ =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u')⁻¹) :
    ∃ c : CFSG.GorensteinWalter.PGL2 F, c * t * c⁻¹ =
      t * Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u' := by
  classical
  set u := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u' with hu
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, pow_zero] at hq9; omega
    · exact h
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    CFSG.ComponentClassification.AutL2Facts.isOddPrimePower_of hp hp2 he1 hF
  have h3 : 3 < Nat.card F := by rw [hF]; omega
  have hcomm : commutator (CFSG.GorensteinWalter.PGL2 F) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    CFSG.GH72.pgl2_commutator_eq_range_toPGL hodd
  have ht2 : t ^ 2 = 1 := by have h := pow_orderOf_eq_one t; rwa [ht] at h
  have ht1 : t ≠ 1 := by intro h; rw [h, orderOf_one] at ht; omega
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht2)
  have huR : u ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    MonoidHom.mem_range.mpr ⟨u', rfl⟩
  have hconjinv : (t * u) * t = u⁻¹ := by
    have h : t * u * t⁻¹ = u⁻¹ := hinv
    rwa [htinv] at h
  have hs2 : (t * u) * (t * u) = 1 := by
    calc (t * u) * (t * u) = ((t * u) * t) * u := by group
      _ = u⁻¹ * u := by rw [hconjinv]
      _ = 1 := inv_mul_cancel u
  have hs1 : t * u ≠ 1 := by
    intro h
    apply htR
    have ht' : t = u⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [ht']
    exact (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.inv_mem huR
  have hsC : t * u ∉ commutator (CFSG.GorensteinWalter.PGL2 F) := by
    rw [hcomm]
    intro h
    apply htR
    have ht' : t = (t * u) * u⁻¹ := by group
    rw [ht']
    exact (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.mul_mem h
      ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.inv_mem huR)
  have htC : t ∉ commutator (CFSG.GorensteinWalter.PGL2 F) := by rw [hcomm]; exact htR
  have hconj := CFSG.GorensteinWalter.pgl2_outer_involutions_conjugate F hodd h3
    ⟨ht1, ht2⟩ ⟨hs1, by rw [pow_two]; exact hs2⟩ htC hsC
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  exact ⟨c, hc⟩

private theorem pgl2_exists_conj_not_mem_normalizer {F : Type} [Field F] [Finite F] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e) (hq9 : 9 < p ^ e)
    {t : CFSG.GorensteinWalter.PGL2 F} (ht : orderOf t = 2)
    {u' : PSL2MatrixGroup F} (hu' : orderOf u' = (p ^ e + 1) / 2)
    (hinv : t * Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u' * t⁻¹ =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u')⁻¹) :
    ∃ d : CFSG.GorensteinWalter.PGL2 F, d * t * d⁻¹ ∉ Subgroup.normalizer
      (Subgroup.zpowers (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u') :
        Set (CFSG.GorensteinWalter.PGL2 F)) := by
  classical
  set u := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u' with hu
  let : Fact p.Prime := ⟨hp⟩
  have hsimple : IsSimpleGroup (PSL2MatrixGroup F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF]; omega)
  have ht2 : t ^ 2 = 1 := by have h := pow_orderOf_eq_one t; rwa [ht] at h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht2)
  by_contra hcon
  push Not at hcon
  let N : Subgroup (CFSG.GorensteinWalter.PGL2 F) :=
    Subgroup.normalClosure ({t} : Set (CFSG.GorensteinWalter.PGL2 F))
  have hNnormal : N.Normal := Subgroup.normalClosure_normal
  have hNle : N ≤ Subgroup.normalizer
      (Subgroup.zpowers u : Set (CFSG.GorensteinWalter.PGL2 F)) := by
    show Subgroup.closure (Group.conjugatesOfSet ({t} : Set _)) ≤ _
    rw [Subgroup.closure_le]
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hyz
    exact hcon c
  let H : Subgroup (PSL2MatrixGroup F) :=
    N.comap (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))
  have hHN : H.Normal := hNnormal.comap _
  have hoddq : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hdvd2 : 2 ∣ (p ^ e) ^ 2 - 1 := by
    obtain ⟨j, hj⟩ := hoddq
    refine ⟨2 * j * j + 2 * j, ?_⟩
    rw [hj]
    have h : (2 * j + 1) ^ 2 = 2 * (2 * j * j + 2 * j) + 1 := by ring
    omega
  have hq2 : 2 < p ^ e := by omega
  have hfirst : (p ^ e + 1) / 2 < p ^ e := by omega
  have hsecond : p ^ e ≤ p ^ e * ((p ^ e) ^ 2 - 1) / 2 := by
    rw [Nat.mul_div_assoc (p ^ e) hdvd2]
    calc p ^ e = p ^ e * 1 := (mul_one _).symm
      _ ≤ p ^ e * (((p ^ e) ^ 2 - 1) / 2) := by
          refine Nat.mul_le_mul_left _ ?_
          rw [Nat.one_le_div_iff (by norm_num)]
          have h3 : 3 ≤ p ^ e := by omega
          have hsq : 9 ≤ (p ^ e) ^ 2 := by nlinarith
          omega
  rcases hHN.eq_bot_or_eq_top with hbot | htop
  · exfalso
    have htN : t ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton t)
    have hmemN : u * t * u⁻¹ * t⁻¹ ∈ N :=
      N.mul_mem (hNnormal.conj_mem t htN u) (N.inv_mem htN)
    have hconjinv : t * u * t = u⁻¹ := by
      have h : t * u * t⁻¹ = u⁻¹ := hinv
      rwa [htinv] at h
    have heq : u * t * u⁻¹ * t⁻¹ = u * u := by
      have h1 : (t * u * t)⁻¹ = u := by rw [hconjinv, inv_inv]
      calc u * t * u⁻¹ * t⁻¹ = u * t * u⁻¹ * t := by rw [htinv]
        _ = u * (t * u * t)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, htinv]
            group
        _ = u * u := by rw [h1]
    have hu2H : u' ^ 2 ∈ H := by
      show Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) (u' ^ 2) ∈ N
      rw [map_pow, pow_two]
      exact heq ▸ hmemN
    have hu2 : u' ^ 2 = 1 := by
      rw [hbot] at hu2H
      simpa using hu2H
    have hdvd : orderOf u' ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
    rw [hu'] at hdvd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    omega
  · exfalso
    have hnorm : Subgroup.normalizer
        (Subgroup.zpowers u' : Set (PSL2MatrixGroup F)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hxH : x ∈ H := by rw [htop]; exact Subgroup.mem_top x
      have hxN : Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) x ∈ N := hxH
      have hxN' : Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) x ∈
          Subgroup.normalizer (Subgroup.zpowers u : Set (CFSG.GorensteinWalter.PGL2 F)) :=
        hNle hxN
      refine mem_normalizer_zpowers_of_conj_mem ?_
      have hconj : Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) x * u *
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) x)⁻¹ ∈
            Subgroup.zpowers u :=
        (Subgroup.mem_normalizer_iff.mp hxN' u).mp (Subgroup.mem_zpowers u)
      have h3 : Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) (x * u' * x⁻¹) ∈
          (Subgroup.zpowers u').map
            (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) := by
        rw [MonoidHom.map_zpowers, ← hu]
        rw [show Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) (x * u' * x⁻¹) =
          Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) x * u *
            (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) x)⁻¹ by
          rw [map_mul, map_mul, map_inv, hu]]
        exact hconj
      obtain ⟨w, hw, hw'⟩ := h3
      have h4 : x * u' * x⁻¹ ∈ Subgroup.zpowers u' := by
        rw [← Matrix.ProjectiveSpecialLinearGroup.toPGL_injective hw']
        exact hw
      exact h4
    have hnormal : (Subgroup.zpowers u').Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
    rcases hnormal.eq_bot_or_eq_top with hbot | htop2
    · have hu1 : u' = 1 := by
        have h : u' ∈ (⊥ : Subgroup (PSL2MatrixGroup F)) := by
          rw [← hbot]; exact Subgroup.mem_zpowers u'
        simpa using h
      rw [hu1, orderOf_one] at hu'
      omega
    · have hcard : Nat.card ↥(Subgroup.zpowers u') = Nat.card (PSL2MatrixGroup F) := by
        rw [htop2]
        exact Nat.card_congr Subgroup.topEquiv.toEquiv
      rw [Nat.card_zpowers, hu',
        CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF hp2] at hcard
      have hlt : (p ^ e + 1) / 2 < p ^ e * ((p ^ e) ^ 2 - 1) / 2 :=
        lt_of_lt_of_le hfirst hsecond
      omega

private theorem pgl2_closure_eq_top {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e) (hq9 : 9 < p ^ e)
    {t : CFSG.GorensteinWalter.PGL2 F} (_ht : orderOf t = 2)
    (htR : t ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    {u' : PSL2MatrixGroup F} (hu' : orderOf u' = (p ^ e + 1) / 2)
    (hinv : t * Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u' * t⁻¹ =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u')⁻¹)
    {c d : CFSG.GorensteinWalter.PGL2 F}
    (hc : c * t * c⁻¹ = t * Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u')
    (hd : d * t * d⁻¹ ∉ Subgroup.normalizer
      (Subgroup.zpowers (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u') :
        Set (CFSG.GorensteinWalter.PGL2 F))) :
    Subgroup.closure ({1 * t * 1⁻¹, c * t * c⁻¹, d * t * d⁻¹} :
      Set (CFSG.GorensteinWalter.PGL2 F)) = ⊤ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  have hfinP : Finite (CFSG.GorensteinWalter.PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set u := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u' with hu
  set s := c * t * c⁻¹ with hs
  set δ := d * t * d⁻¹ with hδ
  set M : Subgroup (CFSG.GorensteinWalter.PGL2 F) :=
    Subgroup.closure ({1 * t * 1⁻¹, c * t * c⁻¹, d * t * d⁻¹} :
      Set (CFSG.GorensteinWalter.PGL2 F)) with hM
  have htM : t ∈ M := by
    have h : 1 * t * 1⁻¹ ∈ M := Subgroup.subset_closure (by simp)
    simpa using h
  have hsM : s ∈ M := by
    have h : c * t * c⁻¹ ∈ M := Subgroup.subset_closure (by simp)
    simpa [hs] using h
  have hδM : δ ∈ M := by
    have h : d * t * d⁻¹ ∈ M := Subgroup.subset_closure (by simp)
    simpa [hδ] using h
  have hd' : δ ∉ Subgroup.normalizer
      (Subgroup.zpowers u : Set (CFSG.GorensteinWalter.PGL2 F)) := by
    rwa [hδ, hu]
  have huM : u ∈ M := by
    have h1 : u = t⁻¹ * s := by rw [hc]; group
    rw [h1]
    exact M.mul_mem (M.inv_mem htM) hsM
  have huK : u' ∈ M.comap (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) := by
    show Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) u' ∈ M
    rwa [← hu]
  have hq11 : 11 ≤ p ^ e := by
    obtain ⟨j, hj⟩ := (hp.odd_of_ne_two hp2).pow (n := e)
    omega
  rcases overgroup_eq_top_or_le_normalizer hF hp2 hq11 huK hu' with htop | hle
  · have hRle : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ≤ M := by
      intro y hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
      have hx : x ∈ M.comap (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) := by
        rw [htop]; exact Subgroup.mem_top x
      exact hx
    have hidx : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.index = 2 :=
      index_range_toPGL hp hp2 hF
    have hmul : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.relIndex M *
        M.index = 2 := by
      have h := Subgroup.relIndex_mul_index hRle
      rwa [hidx] at h
    have hMne : M.index ≠ 2 := by
      intro h2
      have h1 : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.relIndex M =
          1 := by
        have h := hmul
        rw [h2] at h
        omega
      have hMleR : M ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
        Subgroup.relIndex_eq_one.mp h1
      exact htR (hMleR htM)
    have hdvd : M.index ∣ 2 := ⟨_, by rw [mul_comm]; exact hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Subgroup.index_eq_one.mp h
    · exact absurd h hMne
  · exfalso
    have hidx : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.index = 2 :=
      index_range_toPGL hp hp2 hF
    have hRnormal :
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.Normal :=
      Subgroup.normal_of_index_eq_two hidx
    have hδR : δ ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      intro hδr
      have hconj : d⁻¹ * δ * d ∈
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
        have h := hRnormal.conj_mem δ hδr d⁻¹
        simpa using h
      have heq : d⁻¹ * δ * d = t := by rw [hδ]; group
      exact htR (heq ▸ hconj)
    have hprodR : t * δ ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false htR hδR
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hprodR
    have hyK : y ∈ M.comap (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) := by
      show Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) y ∈ M
      rw [hy]
      exact M.mul_mem htM hδM
    have hynorm : y ∈ Subgroup.normalizer
        (Subgroup.zpowers u' : Set (PSL2MatrixGroup F)) := hle y hyK
    have hmaps : t * δ ∈ Subgroup.normalizer
        (Subgroup.zpowers u : Set (CFSG.GorensteinWalter.PGL2 F)) := by
      have h := map_mem_normalizer_zpowers
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective hynorm
      rwa [hy] at h
    have htN : t ∈ Subgroup.normalizer
        (Subgroup.zpowers u : Set (CFSG.GorensteinWalter.PGL2 F)) :=
      mem_normalizer_zpowers_of_conj (Or.inr hinv)
    have hδnorm : δ ∈ Subgroup.normalizer
        (Subgroup.zpowers u : Set (CFSG.GorensteinWalter.PGL2 F)) := by
      have h1 : t⁻¹ * (t * δ) = δ := by group
      rw [← h1]
      exact mul_mem
        ((Subgroup.normalizer
          (Subgroup.zpowers u : Set (CFSG.GorensteinWalter.PGL2 F))).inv_mem htN)
        hmaps
    exact hd' hδnorm

private theorem pgl2_three_conj {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e) (hq9 : 9 < p ^ e)
    {t : CFSG.GorensteinWalter.PGL2 F} (ht : orderOf t = 2)
    (htR : t ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    ∃ x y z : CFSG.GorensteinWalter.PGL2 F,
      Subgroup.closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} :
        Set (CFSG.GorensteinWalter.PGL2 F)) = ⊤ := by
  obtain ⟨u', hu', hinv⟩ := pgl2_exists_inverted hp hp2 hF hq9 ht htR
  obtain ⟨c, hc⟩ := pgl2_exists_conj_mul hp hp2 hF hq9 ht htR hinv
  obtain ⟨d, hd⟩ := pgl2_exists_conj_not_mem_normalizer hp hp2 hF hq9 ht hu' hinv
  exact ⟨1, c, d, pgl2_closure_eq_top hp hp2 hF hq9 ht htR hu' hinv hc hd⟩

private theorem map_subgroupOf_eq_range {G : Type} [Group G] {A L : Subgroup G} {F : Type}
    [Field F] [Finite F] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ e)
    (hq9 : 9 < p ^ e) (hLA : L ≤ A) (φ : ↥A ≃* CFSG.GorensteinWalter.PGL2 F)
    (hcard : Nat.card ↥L = Nat.card (PSL2MatrixGroup F)) :
    (L.subgroupOf A).map (φ : ↥A →* CFSG.GorensteinWalter.PGL2 F) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hfinP : Finite (CFSG.GorensteinWalter.PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set J : Subgroup (CFSG.GorensteinWalter.PGL2 F) :=
    (L.subgroupOf A).map (φ : ↥A →* CFSG.GorensteinWalter.PGL2 F) with hJ
  have hcardJ : Nat.card ↥J = Nat.card
      ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    have h1 : Nat.card ↥J = Nat.card ↥(L.subgroupOf A) := by
      rw [hJ]
      exact Subgroup.card_map_of_injective φ.injective
    have h2 : Nat.card ↥(L.subgroupOf A) = Nat.card ↥L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv
    rw [h1, h2, hcard, CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF hp2,
      card_range_toPGL hF hp2]
  have hJ2 : J.index = 2 := by
    have hP : Nat.card (CFSG.GorensteinWalter.PGL2 F) = 2 * Nat.card ↥J := by
      rw [card_pgl2_eq_two_mul_range hp hp2 hF, hcardJ]
    have h := Subgroup.card_mul_index J
    rw [hP, mul_comm 2 (Nat.card ↥J)] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, pow_zero] at hq9; omega
    · exact h
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    CFSG.ComponentClassification.AutL2Facts.isOddPrimePower_of hp hp2 he1 hF
  have hRJ : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ≤ J := by
    have hcomm : commutator (CFSG.GorensteinWalter.PGL2 F) ≤ J := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hJ2,
        Subgroup.mul_mem_iff_of_index_two hJ2, Subgroup.mul_mem_iff_of_index_two hJ2,
        Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
      tauto
    rwa [CFSG.GH72.pgl2_commutator_eq_range_toPGL hodd] at hcomm
  exact (Subgroup.eq_of_le_of_card_ge hRJ hcardJ.le).symm

theorem exists_three_conj_closure_eq_of_isPGL2
    (hM : LieModel ↥L .PSL 2 p e) (hp2 : p ≠ 2) (hq : 9 < p ^ e) (hLA : L ≤ A)
    (hA : F6.IsPGL2 (p ^ e) ↥A) {t : G} (htA : t ∈ A) (htL : t ∉ L) (ht : orderOf t = 2) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set G) = L ⊔ zpowers t := by
  classical
  obtain ⟨hp, he1, -, -, F, instF, instFin, hFcard, hne⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hM
  let : Field F := instF
  let : Finite F := instFin
  obtain ⟨ε⟩ := hne
  obtain ⟨F', instF', instFin', hF'card, ⟨φ⟩⟩ := pgl2_data_of_isPGL2 hA
  let : Field F' := instF'
  let : Finite F' := instFin'
  let : Fact p.Prime := ⟨hp⟩
  have hcardL : Nat.card ↥L = Nat.card (PSL2MatrixGroup F) := Nat.card_congr ε.toEquiv
  have hcardFF' : Nat.card (PSL2MatrixGroup F) = Nat.card (PSL2MatrixGroup F') := by
    rw [CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hFcard hp2,
      CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF'card hp2]
  have hcardL' : Nat.card ↥L = Nat.card (PSL2MatrixGroup F') := hcardL.trans hcardFF'
  have hmap : (L.subgroupOf A).map (φ : ↥A →* CFSG.GorensteinWalter.PGL2 F') =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range :=
    map_subgroupOf_eq_range hp hp2 hF'card hq hLA φ hcardL'
  set t' : CFSG.GorensteinWalter.PGL2 F' := φ ⟨t, htA⟩ with ht'def
  have ht' : orderOf t' = 2 := by
    rw [ht'def, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe (⟨t, htA⟩ : ↥A)]
    exact ht
  have ht'R : t' ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range := by
    intro h
    rw [← hmap] at h
    obtain ⟨y, hy, hφy⟩ := Subgroup.mem_map.mp h
    have hy' : y = ⟨t, htA⟩ := φ.injective (hφy.trans ht'def)
    have hmem : y ∈ L.subgroupOf A := hy
    rw [hy', Subgroup.mem_subgroupOf] at hmem
    exact htL hmem
  obtain ⟨x', y', z', hcl⟩ := pgl2_three_conj hp hp2 hF'card hq ht' ht'R
  set xA : ↥A := φ.symm x' with hxA
  set yA : ↥A := φ.symm y' with hyA
  set zA : ↥A := φ.symm z' with hzA
  have hφx : (φ : ↥A →* CFSG.GorensteinWalter.PGL2 F') xA = x' := φ.apply_symm_apply x'
  have hφy : (φ : ↥A →* CFSG.GorensteinWalter.PGL2 F') yA = y' := φ.apply_symm_apply y'
  have hφz : (φ : ↥A →* CFSG.GorensteinWalter.PGL2 F') zA = z' := φ.apply_symm_apply z'
  have ht'm : (φ : ↥A →* CFSG.GorensteinWalter.PGL2 F') ⟨t, htA⟩ = t' := ht'def.symm
  have hmap2 : (Subgroup.closure ({xA * ⟨t, htA⟩ * xA⁻¹, yA * ⟨t, htA⟩ * yA⁻¹,
      zA * ⟨t, htA⟩ * zA⁻¹} : Set ↥A)).map (φ : ↥A →* CFSG.GorensteinWalter.PGL2 F') = ⊤ := by
    rw [MonoidHom.map_closure]
    have himg : (φ : ↥A →* CFSG.GorensteinWalter.PGL2 F') ''
        ({xA * ⟨t, htA⟩ * xA⁻¹, yA * ⟨t, htA⟩ * yA⁻¹, zA * ⟨t, htA⟩ * zA⁻¹} : Set ↥A) =
        ({x' * t' * x'⁻¹, y' * t' * y'⁻¹, z' * t' * z'⁻¹} :
          Set (CFSG.GorensteinWalter.PGL2 F')) := by
      ext w
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨v, hv, rfl⟩
        rcases hv with rfl | rfl | rfl <;>
          simp [map_mul, map_inv, hφx, hφy, hφz, ht'm]
      · rintro (rfl | rfl | rfl)
        · exact ⟨_, Or.inl rfl, by simp only [map_mul, map_inv, hφx, ht'm]⟩
        · exact ⟨_, Or.inr (Or.inl rfl), by simp only [map_mul, map_inv, hφy, ht'm]⟩
        · exact ⟨_, Or.inr (Or.inr rfl), by simp only [map_mul, map_inv, hφz, ht'm]⟩
    rw [himg]
    exact hcl
  have hcoe : Subgroup.closure ((A.subtype : ↥A → G) ''
      ({xA * ⟨t, htA⟩ * xA⁻¹, yA * ⟨t, htA⟩ * yA⁻¹,
        zA * ⟨t, htA⟩ * zA⁻¹} : Set ↥A)) = A :=
    closure_coe_image_eq_of_map φ hmap2
  have hst : ((A.subtype : ↥A → G) '' ({xA * ⟨t, htA⟩ * xA⁻¹, yA * ⟨t, htA⟩ * yA⁻¹,
      zA * ⟨t, htA⟩ * zA⁻¹} : Set ↥A)) =
      ({xA * t * xA⁻¹, yA * t * yA⁻¹, zA * t * zA⁻¹} : Set G) := by
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hv with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, Or.inl rfl, rfl⟩
      · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
  have hsup : L ⊔ Subgroup.zpowers t = A := by
    have hKA : L ⊔ Subgroup.zpowers t ≤ A :=
      sup_le hLA (Subgroup.zpowers_le.mpr htA)
    have hLK : L ≤ L ⊔ Subgroup.zpowers t := le_sup_left
    have hcardA : Nat.card ↥A = 2 * Nat.card ↥L := by
      rw [Nat.card_congr φ.toEquiv, card_pgl2_eq_two_mul_range hp hp2 hF'card,
        card_range_toPGL hF'card hp2,
        ← CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF'card hp2, hcardL']
    have hrel : L.relIndex A = 2 := by
      have h := Subgroup.relIndex_mul_card L A
      rw [inf_eq_left.mpr hLA, hcardA] at h
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
    have hprod := Subgroup.relIndex_mul_relIndex L (L ⊔ Subgroup.zpowers t) A hLK hKA
    have hKnot2 : (L ⊔ Subgroup.zpowers t).relIndex A ≠ 2 := by
      intro h2
      have h1 : L.relIndex (L ⊔ Subgroup.zpowers t) = 1 := by
        have h := hprod
        rw [hrel, h2] at h
        omega
      have hKL : L ⊔ Subgroup.zpowers t ≤ L := Subgroup.relIndex_eq_one.mp h1
      exact htL (hKL (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
    have hK1 : (L ⊔ Subgroup.zpowers t).relIndex A = 1 := by
      have hprod' : L.relIndex (L ⊔ Subgroup.zpowers t) *
          (L ⊔ Subgroup.zpowers t).relIndex A = 2 := by
        rw [hprod, hrel]
      have hdvd : (L ⊔ Subgroup.zpowers t).relIndex A ∣ 2 :=
        ⟨_, by rw [mul_comm]; exact hprod'.symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exact absurd h hKnot2
    have hAK : A ≤ L ⊔ Subgroup.zpowers t := Subgroup.relIndex_eq_one.mp hK1
    exact le_antisymm hKA hAK
  refine ⟨(xA : G), xA.2, (yA : G), yA.2, (zA : G), zA.2, ?_⟩
  rw [hst] at hcoe
  rw [hsup]
  exact hcoe

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
