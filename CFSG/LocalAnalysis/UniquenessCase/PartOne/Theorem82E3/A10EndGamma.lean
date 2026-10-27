module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSylow
import CFSG.GroupTheory.CardMapInfKer
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.GroupTheory.GL52.Basic
import CFSG.RankThree.PartTwo.Sec10.Item104

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

theorem normalizer_le_normalizer_A_of_isPGroup (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {T : Subgroup G} (hT : IsPGroup 3 T)
    (hAT : F.A ≤ T) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (F.A : Set G) := by
  intro n hn
  obtain ⟨g, hgN, hgT⟩ := exists_mem_normalizer_le_map_conj F hNA hT hAT
  have hgA : F.A.map (MulAut.conj g).toMonoidHom = F.A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  have hAle : F.A.map (MulAut.conj n).toMonoidHom ≤
      F.P.map (MulAut.conj g).toMonoidHom := by
    calc F.A.map (MulAut.conj n).toMonoidHom ≤ T.map (MulAut.conj n).toMonoidHom :=
          Subgroup.map_mono hAT
      _ = T := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
      _ ≤ F.P.map (MulAut.conj g).toMonoidHom := hgT
  have hBle : F.A.map (MulAut.conj (g⁻¹ * n)).toMonoidHom ≤ F.P := by
    rw [← Subgroup.map_le_map_iff_of_injective
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective, Subgroup.map_map]
    convert hAle using 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hB : F.A.map (MulAut.conj (g⁻¹ * n)).toMonoidHom = F.A :=
    F.unique _ hBle (F.elemAbelian.map _)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj (g⁻¹ * n)).injective, F.card_A])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc F.A.map (MulAut.conj n).toMonoidHom
      = (F.A.map (MulAut.conj (g⁻¹ * n)).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
    _ = F.A.map (MulAut.conj g).toMonoidHom := by rw [hB]
    _ = F.A := hgA

omit [Finite G] in
private theorem mem_normalizer_of_conj {T : Subgroup G} {n k : G}
    (hkT : ∀ x : G, x ∈ T.map (MulAut.conj n).toMonoidHom ↔ k⁻¹ * x * k ∈ T) :
    k⁻¹ * n ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hmap : x ∈ T ↔ n * x * n⁻¹ ∈ T.map (MulAut.conj n).toMonoidHom := by
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, by
        change (MulAut.conj n) x = n * x * n⁻¹
        rw [MulAut.conj_apply]⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : y = x := by
        have := congrArg (MulAut.conj n⁻¹) hyx
        simpa [MulAut.conj_apply] using this
      rw [← hyx']
      exact hy
  rw [hmap, hkT (n * x * n⁻¹)]
  constructor
  · intro hx
    rwa [show (k⁻¹ * n) * x * (k⁻¹ * n)⁻¹ =
      k⁻¹ * (n * x * n⁻¹) * k by group]
  · intro hx
    rwa [show k⁻¹ * (n * x * n⁻¹) * k =
      (k⁻¹ * n) * x * (k⁻¹ * n)⁻¹ by group]

theorem normalizer_le_of_centralizer_le (F : A10Frame c) (hF : A10Facts F) {Q : Subgroup G}
    (hQA : Q ≤ F.A) (hCQ : Subgroup.centralizer (Q : Set G) ≤ D.M) :
    Subgroup.normalizer (Q : Set G) ≤ D.M := by
  classical
  let C : Subgroup G := Subgroup.centralizer (Q : Set G)
  have hAC : F.A ≤ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (congrArg (fun z : ↥F.A => (z : G))
      (F.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨q, hQA hq⟩)).symm
  obtain ⟨S, hAS⟩ : ∃ S : Sylow 3 ↥C, F.A.subgroupOf C ≤ (S : Subgroup C) :=
    F.elemAbelian.isPGroup.comap_subtype.exists_le_sylow
  let T : Subgroup G := (S : Subgroup C).map C.subtype
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T C := ⟨S, rfl⟩
  have hAT : F.A ≤ T := by
    intro a ha
    exact Subgroup.mem_map.mpr
      ⟨⟨a, hAC ha⟩, hAS (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hTA : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (F.A : Set G) :=
    normalizer_le_normalizer_A_of_isPGroup F hF.normalizer_A hTsyl.isPGroup hAT
  intro n hn
  have hCmap : C.map (MulAut.conj n).toMonoidHom = C := by
    rw [show C = Subgroup.centralizer (Q : Set G) from rfl,
      ← CFSG.GroupTheory.GL52.centralizer_map_conj n Q]
    exact congrArg (fun H : Subgroup G => Subgroup.centralizer (H : Set G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn)
  have hTnsyl : CFSG.ABGLocalTools.IsSylowOf 3
      (T.map (MulAut.conj n).toMonoidHom) C := by
    have h := CFSG.RankThree.PartTwo.Sec10.IsSylowOf.map_conj hTsyl n
    rw [hCmap] at h
    exact h
  obtain ⟨k, hkC, hkT⟩ := hTsyl.exists_mem_conj hTnsyl
  have hks : k⁻¹ * n ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_of_conj hkT
  have hksM : k⁻¹ * n ∈ D.M := hF.normalizer_A (hTA hks)
  have hkM : k ∈ D.M := hCQ hkC
  have hn_eq : n = k * (k⁻¹ * n) := by group
  rw [hn_eq]
  exact D.M.mul_mem hkM hksM

theorem exists_mem_deg_three_or_nine (F : A10Frame c) {Q : Subgroup G} (hQA : Q ≤ F.A)
    (hQ9 : Nat.card Q = 9) :
    ∃ x ∈ Q, F.deg (Subgroup.zpowers x) = 3 ∨ F.deg (Subgroup.zpowers x) = 9 := by
  classical
  have hAM : F.A ≤ D.M := F.A_le_M
  have hQM : Q ≤ D.M := hQA.trans hAM
  let f : ↥D.M →* Equiv.Perm (Fin 10) := F.phiA
  let MQ : Subgroup ↥D.M := Q.subgroupOf D.M
  let B : Subgroup (Equiv.Perm (Fin 10)) := MQ.map f
  have hMQcard : Nat.card MQ = 9 := by
    rw [← hQ9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  have hdisj : MQ ⊓ f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxK⟩ := Subgroup.mem_inf.mp hx
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      have h := F.elemAbelian.2 (x : G) (hQA (Subgroup.mem_subgroupOf.mp hxQ))
      simpa [Subgroup.coe_pow] using h
    have hord3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hordker : orderOf x ∣ Nat.card f.ker := Subgroup.orderOf_dvd_natCard _ hxK
    have hone : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes F.coprime_card_ker_phiA.symm hord3 hordker
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)
  have hBle : B ≤ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hQA (Subgroup.mem_subgroupOf.mp hx))
  have hBcard : Nat.card B = 9 := by
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot f hdisj, hMQcard]
  obtain ⟨y, hyB, hydeg⟩ := A10Perm.exists_mem_card_support_three_or_nine hBle hBcard
  obtain ⟨x, hxMQ, rfl⟩ := Subgroup.mem_map.mp hyB
  have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hxMQ
  refine ⟨(x : G), hxQ, ?_⟩
  have hxL : (x : G) ∈ c.L := F.P_le_L (F.A_le (hQA hxQ))
  have hdeg := F.deg_zpowers_eq hxL
  have hphi : F.phiA ⟨(x : G), c.hyp81.1 hxL⟩ = f x := by
    apply congrArg F.phiA
    exact Subtype.ext rfl
  rw [hdeg, hphi]
  exact hydeg

private theorem card_eq_nine_or_eq_A (F : A10Frame c) {Q : Subgroup G} (hQA : Q ≤ F.A)
    (h2 : 2 ≤ CFSG.Open.pRank 3 Q) : Nat.card Q = 9 ∨ Q = F.A := by
  have hQab : CFSG.Open.IsElemAbelian 3 Q :=
    ⟨IsMulCommutative.of_comm fun a b =>
        Subtype.ext (congrArg (fun z : ↥F.A => (z : G))
          (F.elemAbelian.1.is_comm.comm ⟨(a : G), hQA a.2⟩ ⟨(b : G), hQA b.2⟩)),
      fun x hx => F.elemAbelian.2 x (hQA hx)⟩
  have hQcard : Nat.card Q = 3 ^ CFSG.Open.pRank 3 Q :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hQab
  have hQle : Nat.card Q ≤ 27 := by
    calc Nat.card Q ≤ Nat.card F.A := Subgroup.card_le_of_le hQA
      _ = 27 := F.card_A
  have hk : CFSG.Open.pRank 3 Q ≤ 3 := by
    have h3pow : 3 ^ CFSG.Open.pRank 3 Q ≤ 3 ^ 3 := by
      rw [← hQcard]
      calc Nat.card Q ≤ 27 := hQle
        _ = 3 ^ 3 := by norm_num
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 3)).1 h3pow
  have hpk : CFSG.Open.pRank 3 Q = 2 ∨ CFSG.Open.pRank 3 Q = 3 := by omega
  rcases hpk with hpk | hpk
  · left
    rw [hQcard, hpk]
    norm_num
  · right
    refine Subgroup.eq_of_le_of_card_ge hQA ?_
    rw [F.card_A, hQcard, hpk]
    norm_num

private theorem centralizer_le_of_card_nine (F : A10Frame c) (hF : A10Facts F)
    (h9 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 9 →
      Subgroup.centralizer (B : Set G) ≤ D.M)
    {Q : Subgroup G} (hQA : Q ≤ F.A) (hQ9 : Nat.card Q = 9) :
    Subgroup.centralizer (Q : Set G) ≤ D.M := by
  obtain ⟨x, hxQ, hxdeg⟩ := exists_mem_deg_three_or_nine F hQA hQ9
  rcases hxdeg with hx3 | hx9
  · refine le_trans (Subgroup.centralizer_le (s := ({x} : Set G))
      (t := (Q : Set G)) ?_) (F.centralizer_le_M_of_deg_three hF (hQA hxQ) hx3)
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hxQ
  · have hxA : x ∈ F.A := hQA hxQ
    have hxL : x ∈ c.L := F.P_le_L (F.A_le hxA)
    have hx1 : x ≠ 1 := F.ne_one_of_deg_ne_zero hxL (by rw [hx9]; norm_num)
    have hBcard : Nat.card (Subgroup.zpowers x) = 3 := F.card_zpowers_of_mem_A hxA hx1
    have hBle : Subgroup.zpowers x ≤ F.A := Subgroup.zpowers_le.mpr hxA
    exact le_trans (Subgroup.centralizer_le (s := (Subgroup.zpowers x : Set G))
      (t := (Q : Set G)) (Subgroup.zpowers_le.mpr hxQ))
      (h9 _ hBle hBcard hx9)

theorem rankThreeGamma_two_le_of_centralizer_le (F : A10Frame c) (hF : A10Facts F)
    (h9 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 9 →
      Subgroup.centralizer (B : Set G) ≤ D.M) :
    CFSG.Open.rankThreeGamma 2 3 F.A ≤ D.M := by
  rw [CFSG.Open.rankThreeGamma, CFSG.Open.GLBCore]
  refine sSup_le ?_
  rintro N ⟨Q, hQA, h2, rfl⟩
  rcases card_eq_nine_or_eq_A F hQA h2 with hQ9 | hQAeq
  · exact normalizer_le_of_centralizer_le F hF hQA
      (centralizer_le_of_card_nine F hF h9 hQA hQ9)
  · rw [hQAeq]
    exact hF.normalizer_A

theorem exists_relPPrimeCore_not_le (F : A10Frame c) (hF : A10Facts F)
    (hC9 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 9 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G))) :
    ∃ B ≤ F.A, Nat.card B = 3 ∧ F.deg B = 9 ∧
      ¬ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) ≤ D.M := by
  by_contra h
  have hO : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 9 →
      CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) ≤ D.M := by
    intro B hBA hBcard hBdeg
    by_contra hB
    exact h ⟨B, hBA, hBcard, hBdeg, hB⟩
  have h9 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 9 →
      Subgroup.centralizer (B : Set G) ≤ D.M := by
    intro B hBA hBcard hBdeg
    calc Subgroup.centralizer (B : Set G)
        ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
            CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) :=
          hC9 B hBA hBcard hBdeg
      _ ≤ D.M := sup_le inf_le_right (hO B hBA hBcard hBdeg)
  exact hF.gamma_two (rankThreeGamma_two_le_of_centralizer_le F hF h9)

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
