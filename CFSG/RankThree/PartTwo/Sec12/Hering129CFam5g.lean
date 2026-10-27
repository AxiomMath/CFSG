module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam5d
import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowM12
import CFSG.RankThree.PartTwo.Sec4.Ronan148SNoCQ
import CFSG.RankThree.PartTwo.Sec12.Hering129CRed1

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Ronan148S

namespace Hering129C

section Lift

theorem exists_mem_normalizer_of_map {G H : Type} [Group G] [Finite G] [Group H] (g : G →* H)
    (hg : Function.Surjective g) (T : Subgroup G) (hT : IsPGroup 3 T)
    (hcop : ¬ 3 ∣ Nat.card g.ker) {h : H}
    (hh : h ∈ Subgroup.normalizer ((T.map g : Subgroup H) : Set H)) :
    ∃ n ∈ Subgroup.normalizer (T : Set G), g n = h := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 (↥T)) := ⟨hT⟩
  have hM : g.ker.Normal := g.normal_ker
  have hcop' : Nat.Coprime 3 (Nat.card g.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcop
  obtain ⟨x0, rfl⟩ := hg h
  let e : G ⧸ g.ker ≃* H := QuotientGroup.quotientKerEquivOfSurjective g hg
  have he : ∀ x : G, e (QuotientGroup.mk' g.ker x) = g x := fun x => rfl
  have hmap : (T.map (QuotientGroup.mk' g.ker)).map e.toMonoidHom = T.map g := by
    rw [Subgroup.map_map]
    congr 1
  have hx : QuotientGroup.mk' g.ker x0 ∈ Subgroup.normalizer
      ((T.map (QuotientGroup.mk' g.ker) : Subgroup (G ⧸ g.ker)) : Set (G ⧸ g.ker)) := by
    rw [← hmap, ← Subgroup.map_equiv_normalizer_eq] at hh
    obtain ⟨z, hz, hzx⟩ := hh
    have : z = QuotientGroup.mk' g.ker x0 := by
      apply e.injective
      rw [he]
      exact hzx
    rwa [← this]
  have hnorm := CFSG.normalizer_map_quotient_eq_map_normalizer 3 T g.ker hM hcop'
  simp only at hnorm
  rw [hnorm] at hx
  obtain ⟨n, hn, hnx⟩ := hx
  refine ⟨n, hn, ?_⟩
  have := congrArg e hnx
  rwa [he, he] at this

end Lift

section A6

theorem factorization_three_360 : (360 : ℕ).factorization 3 = 2 := by
  rw [show (360 : ℕ) = 3 ^ 2 * 40 by norm_num,
    Nat.factorization_mul (show (3 : ℕ) ^ 2 ≠ 0 by norm_num) (show (40 : ℕ) ≠ 0 by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 40 by norm_num), add_zero]

theorem mem_map_conj_iff {G : Type*} [Group G] (A : Subgroup G) (x h : G) :
    h ∈ A.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * h * x ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro hh
    exact ⟨x⁻¹ * h * x, hh, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem a6_sylow_normalized (Q' : Sylow 3 (alternatingGroup (Fin 6))) :
    ∃ y : alternatingGroup (Fin 6), y ∈ Subgroup.normalizer
      ((Q' : Subgroup (alternatingGroup (Fin 6))) : Set (alternatingGroup (Fin 6))) ∧
      y * y ∉ (Q' : Subgroup (alternatingGroup (Fin 6))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card A6Q0 = 3 ^ (Nat.card (alternatingGroup (Fin 6))).factorization 3 := by
    rw [card_A6Q0, card_alternatingGroup6, factorization_three_360]
    norm_num
  obtain ⟨x, hx⟩ := Sec4.Item434AltPerm.exists_le_map_conj_of_card hcard Q'.isPGroup'
  have hcard' : Nat.card ↥(A6Q0.map (MulAut.conj x).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, card_A6Q0]
  have hQ'card : Nat.card (Q' : Subgroup (alternatingGroup (Fin 6))) = 9 := by
    rw [Sylow.card_eq_multiplicity, card_alternatingGroup6, factorization_three_360]
    norm_num
  have heq : (Q' : Subgroup (alternatingGroup (Fin 6))) = A6Q0.map (MulAut.conj x).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hx (by omega)
  refine ⟨x * m12y0A * x⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [heq, mem_map_conj_iff, mem_map_conj_iff]
    have h1 := A6Q0_conj (x⁻¹ * z * x)
    have h2 : x⁻¹ * (x * m12y0A * x⁻¹ * z * (x * m12y0A * x⁻¹)⁻¹) * x =
        m12y0A * (x⁻¹ * z * x) * m12y0A⁻¹ := by group
    rw [h2]
    exact h1
  · rw [heq, mem_map_conj_iff]
    have h3 : x⁻¹ * (x * m12y0A * x⁻¹ * (x * m12y0A * x⁻¹)) * x = m12y0A * m12y0A := by group
    rw [h3, mem_A6Q0_iff]
    exact m12y0_sq_not_mem

end A6

section M12


theorem PPair.false_M12 {S Lb : Type} [Group S] [Finite S] [Group Lb] {s : S}
    {J : Subgroup S} {g : ↥J →* Lb} (hS : Nat.card S = 95040)
    (hloc : Toolkit.M12ThreeLocalData S) (h : PPair s J g) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := h.finite_Lb
  have h81 : ¬ 81 ∣ Nat.card S := by
    rw [hS]
    norm_num
  obtain ⟨P0, hP0J, hsP0, -⟩ := h.exists_sylow_le h81
  have hLJ : Nat.card Lb ∣ Nat.card J := Subgroup.card_dvd_of_surjective h.surjective
  have hdvd : Nat.card Lb ∣ 95040 :=
    hLJ.trans ((Subgroup.card_subgroup_dvd_card J).trans (dvd_of_eq hS))
  have hmem := card_mem_typeOrders425 h.quasisimple_Lb (M := 95040) (B := 46) (by norm_num)
    (by norm_num) (isType425_of_isType122 h.type_Lb) hdvd
  have htype : typeOrders425 95040 46 = [1080] := by decide +kernel
  rw [htype] at hmem
  have hL1080 : Nat.card Lb = 1080 := List.mem_singleton.mp hmem
  obtain ⟨f, hf⟩ := exists_surjective_A6 (isType425_of_isType122 h.type_Lb) hL1080
  let T_syl : Sylow 3 J := P0.subtype hP0J
  have hTeq : (T_syl : Subgroup J) = (P0 : Subgroup S).subgroupOf J := rfl
  set T : Subgroup J := (T_syl : Subgroup J) with hT
  have hT3 : IsPGroup 3 T := T_syl.isPGroup'
  let F : J →* alternatingGroup (Fin 6) := f.comp g
  have hF : Function.Surjective F := hf.comp h.surjective
  let Q' : Sylow 3 (alternatingGroup (Fin 6)) := T_syl.mapSurjective hF
  have hQ' : (Q' : Subgroup (alternatingGroup (Fin 6))) = T.map F := rfl
  obtain ⟨y, hyN, hy2⟩ := a6_sylow_normalized Q'
  obtain ⟨l, hl⟩ := hf y
  have hkerf : Nat.card f.ker = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hL1080,
      card_alternatingGroup6] at h1
    omega
  set sJ : J := ⟨s, h.s_mem⟩ with hsJ
  have hsc : ∀ x : J, x * sJ = sJ * x := fun x =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer x.2))
  have hFs : F sJ = 1 := by
    have hz : F sJ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨x, rfl⟩ := hF z
      rw [← map_mul, ← map_mul, hsc x]
    rw [center_alternatingGroup_eq_bot (by norm_num : 4 ≤ 6)] at hz
    exact Subgroup.mem_bot.mp hz
  have hsJ3 : sJ ^ 3 = 1 := by
    apply Subtype.ext
    simpa using (by
      have := pow_orderOf_eq_one s
      rwa [h.orderOf_s] at this : s ^ 3 = 1)
  have hgs1 : g sJ ≠ 1 := by
    intro h1
    have hmemk : sJ ∈ g.ker := h1
    have := eq_one_of_pow_three_pow_of_mem (N := g.ker) h.ker_three hmemk (r := 1)
      (by simpa using hsJ3)
    have hs1 : s = 1 := congrArg Subtype.val this
    have h3 := h.orderOf_s
    rw [hs1, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hgsker : g sJ ∈ f.ker := hFs
  have hgs3 : orderOf (g sJ) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hsJ3, map_one]) hgs1
  have hker_eq : Subgroup.zpowers (g sJ) = f.ker :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgsker)
      (by rw [hkerf, Nat.card_zpowers, hgs3])
  have hsT : sJ ∈ T := by
    show (sJ : S) ∈ (P0 : Subgroup S)
    exact hsP0
  have hkerle : f.ker ≤ T.map g := by
    rw [← hker_eq]
    exact Subgroup.zpowers_le.mpr ⟨sJ, hsT, rfl⟩
  have hcomap : (T.map g).map f = T.map F := Subgroup.map_map _ _ _
  have hlN : l ∈ Subgroup.normalizer ((T.map g : Subgroup Lb) : Set Lb) := by
    have h1 : (T.map g) = ((T.map g).map f).comap f := (Subgroup.comap_map_eq_self hkerle).symm
    rw [h1, ← Subgroup.comap_normalizer_eq_of_surjective _ hf, Subgroup.mem_comap, hl, hcomap]
    exact hyN
  obtain ⟨n, hnN, hgn⟩ := exists_mem_normalizer_of_map g h.surjective T hT3 h.ker_three hlN
  have hnS : (n : S) ∈ Subgroup.normalizer ((P0 : Subgroup S) : Set S) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    by_cases hxJ : x ∈ J
    · have := (Subgroup.mem_normalizer_iff.mp hnN) ⟨x, hxJ⟩
      simpa [hTeq, Subgroup.mem_subgroupOf] using this
    · constructor
      · intro hx
        exact absurd (hP0J hx) hxJ
      · intro hx
        exfalso
        apply hxJ
        have : (n : S)⁻¹ * ((n : S) * x * (n : S)⁻¹) * (n : S) ∈ J :=
          J.mul_mem (J.mul_mem (J.inv_mem n.2) (hP0J hx)) n.2
        simpa [mul_assoc] using this
  obtain ⟨-, hP0card, -, hQ, -⟩ := hloc P0
  have hsq : (n : S) ^ 2 ∈ (P0 : Subgroup S) := by
    have hexp : ∀ g : Subgroup.normalizer ((P0 : Subgroup S) : Set S) ⧸
        (P0 : Subgroup S).subgroupOf (Subgroup.normalizer ((P0 : Subgroup S) : Set S)),
        g ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _)
    have h2 := hexp (QuotientGroup.mk (⟨(n : S), hnS⟩ :
      Subgroup.normalizer ((P0 : Subgroup S) : Set S)))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hnn : n * n ∈ T := by
    show ((n * n : J) : S) ∈ (P0 : Subgroup S)
    simpa [sq] using hsq
  have hFnn : F (n * n) ∈ T.map F := Subgroup.mem_map_of_mem F hnn
  have hFn : F (n * n) = y * y := by
    simp only [F, MonoidHom.comp_apply, map_mul, hgn, hl]
  rw [hFn, ← hQ'] at hFnn
  exact hy2 hFnn

theorem kFCensus46Five_M12 :
    KFCensusOn (fun Q _ => Nonempty (Q ≃* NativeSporadic.Carrier .M12)) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨e0⟩ := hQ
  let e : Q ≃* NativeSporadic.M12 := e0
  have hS : Nat.card Q = 95040 := (Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.Mathieu.card_M12
  exact (ppair_self hD).false_M12 hS (Toolkit.m12ThreeLocalData Q ⟨e⟩)

end M12

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
