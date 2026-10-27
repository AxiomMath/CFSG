module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

section Lift

private theorem s15_Three_card_eq_card_map_mul_card_ker {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (E : Subgroup G) :
    Nat.card E = Nat.card (E.map φ) * Nat.card (E ⊓ φ.ker : Subgroup G) := by
  have h := Subgroup.card_ker_mul_card_range (φ.domRestrict E)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h
  have hker : Nat.card (φ.ker.subgroupOf E) = Nat.card (E ⊓ φ.ker : Subgroup G) := by
    have hm : (φ.ker.subgroupOf E).map E.subtype = E ⊓ φ.ker := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    calc Nat.card (φ.ker.subgroupOf E)
        = Nat.card ((φ.ker.subgroupOf E).map E.subtype) :=
          (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ = Nat.card (E ⊓ φ.ker : Subgroup G) := by rw [hm]
  rw [hker, mul_comm] at h
  exact h.symm

private theorem s15_Three_sylow_conj {H : Type*} [Group H] (g : H) (P : Sylow 3 H) :
    ((g • P : Sylow 3 H) : Subgroup H) = (P : Subgroup H).map (MulAut.conj g).toMonoidHom := by
  apply SetLike.coe_injective
  change ((g • P : Sylow 3 H) : Set H) = _
  rw [Sylow.coe_smul, Subgroup.coe_map]
  rfl

private theorem s15_Three_eq_of_card_eq_three_of_pRank_le_one {H : Type*} [Group H] [Finite H]
    {Q A B : Subgroup H} (hQ : IsPGroup 3 Q) (hr : CFSG.Open.pRank 3 Q ≤ 1)
    (hAQ : A ≤ Q) (hBQ : B ≤ Q) (hA : Nat.card A = 3) (hB : Nat.card B = 3) :
    A = B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C, hCQ, hCp, hCc⟩ : ∃ C : Subgroup H, C ≤ Q ∧ Nat.card C = 3 ∧
      ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c := by
    have hnt : Nontrivial Q := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      exact (by norm_num : 1 < 3).trans_le (hA ▸ Subgroup.card_le_of_le hAQ)
    have hZ : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
    have hdvd : 3 ∣ Nat.card (Subgroup.center Q) :=
      ((hQ.to_subgroup (Subgroup.center Q)).card_eq_or_dvd).resolve_left
        (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    refine ⟨Subgroup.zpowers ((z : Q) : H), ?_, ?_, ?_⟩
    · rw [Subgroup.zpowers_le]
      exact (z : Q).2
    · rw [Nat.card_zpowers, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    · intro c hc q hq
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have h1 : Commute ((z : Q) : H) q :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨q, hq⟩).symm
      exact (h1.zpow_left k).eq
  have key : ∀ X : Subgroup H, X ≤ Q → Nat.card X = 3 → X = C := by
    intro X hXQ hXp
    by_contra hXC
    have hdisj : X ⊓ C = ⊥ := by
      have hdvd : Nat.card ↥(X ⊓ C) ∣ 3 := hXp ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have h2 : X ⊓ C = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hXp])
        exact hXC (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h2) (by rw [hXp, hCp]))
    have hcomm : ∀ (x : X) (c : C), Commute (X.subtype x) (C.subtype c) := fun x c =>
      (hCc c c.2 x (hXQ x.2)).symm
    have hf : Function.Injective (X.subtype.noncommCoprod C.subtype hcomm) :=
      (MonoidHom.noncommCoprod_injective _ _ _).mpr
        ⟨X.subtype_injective, C.subtype_injective, by simpa [disjoint_iff] using hdisj⟩
    haveI hXcyc : IsCyclic X := isCyclic_of_prime_card hXp
    haveI hCcyc : IsCyclic C := isCyclic_of_prime_card hCp
    have h2 := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num)
      (A := ↥X × ↥C) (k := 2)
      (fun a b => Prod.ext (mul_comm' a.1 b.1) (mul_comm' a.2 b.2))
      (fun a => Prod.ext (by simpa [hXp] using pow_card_eq_one' (x := a.1))
        (by simpa [hCp] using pow_card_eq_one' (x := a.2)))
      (by rw [Nat.card_prod, hXp, hCp, sq]) (X.subtype.noncommCoprod C.subtype hcomm) hf
      (H := Q) (by
        rintro _ ⟨⟨x, c⟩, rfl⟩
        exact Q.mul_mem (hXQ x.2) (hCQ c.2))
    omega
  rw [key A hAQ hA, key B hBQ hB]

private theorem s15_Three_exists_conj_le {H : Type*} [Group H] [Finite H]
    (h1 : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 1)
    {A B : Subgroup H} (hA : Nat.card A = 3) (hB : Nat.card B = 3) :
    ∃ h : H, B.map (MulAut.conj h).toMonoidHom ≤ A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [hB, pow_one])
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  obtain ⟨Q, hBQ⟩ := hBp.exists_le_sylow
  haveI : Finite (Sylow 3 H) := Sylow.finite_of_finiteIndex P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  have hPmap : (P : Subgroup H) = Q.map (MulAut.conj g).toMonoidHom := by
    rw [← s15_Three_sylow_conj g Q]
    exact (congrArg (fun S : Sylow 3 H => (S : Subgroup H)) hg).symm
  have hPrank : CFSG.Open.pRank 3 (P : Subgroup H) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
      (le_top : (P : Subgroup H) ≤ ⊤)).trans h1
  have hBconj : B.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup H) := by
    rw [hPmap]
    exact Subgroup.map_mono hBQ
  have hcard : Nat.card (B.map (MulAut.conj g).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB]
  have heq : B.map (MulAut.conj g).toMonoidHom = A :=
    s15_Three_eq_of_card_eq_three_of_pRank_le_one P.isPGroup' hPrank hBconj hAP hcard hA
  exact ⟨g, heq.le⟩

theorem s15_Three_lift_nine {M H : Type} [Group M] [Finite M] [Group H] [Finite H]
    (φ : M →* H) (hφ : Function.Surjective φ) {E : Subgroup M} (hE : IsElemAbelian 3 E)
    {q : ℕ} (hEq : Nat.card E = 3 * q) (hEN : Nat.card (E ⊓ φ.ker : Subgroup M) ≤ 3)
    (hbound : ∀ B : Subgroup H, IsElemAbelian 3 B → Nat.card B ≤ q)
    (hconj : ∀ A B : Subgroup H, IsElemAbelian 3 A → Nat.card A = q → IsElemAbelian 3 B →
      Nat.card B = 3 → ∃ h : H, B.map (MulAut.conj h).toMonoidHom ≤ A)
    {Y : Subgroup H} (hY : IsElemAbelian 3 Y) (hY3 : Nat.card Y = 3) :
    ∃ (F : Subgroup M) (m : M), IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ F ≤ Y.comap φ ∧
      F ≤ E.map (MulAut.conj m).toMonoidHom := by
  have hĒel : IsElemAbelian 3 (E.map φ) := CFSG.SectionRank.isElemAbelian_map hE φ
  have hĒle : Nat.card (E.map φ) ≤ q := hbound (E.map φ) hĒel
  have hmul : Nat.card (E.map φ) * Nat.card (E ⊓ φ.ker : Subgroup M) = 3 * q := by
    rw [← s15_Three_card_eq_card_map_mul_card_ker φ E, hEq]
  have hb3 : Nat.card (E ⊓ φ.ker : Subgroup M) = 3 := by
    have h1 : Nat.card (E.map φ) * Nat.card (E ⊓ φ.ker : Subgroup M) ≤
        Nat.card (E.map φ) * 3 := Nat.mul_le_mul_left _ hEN
    have h2 : Nat.card (E.map φ) * 3 ≤
        Nat.card (E.map φ) * Nat.card (E ⊓ φ.ker : Subgroup M) := by
      rw [hmul, mul_comm 3 q]
      exact Nat.mul_le_mul_right 3 hĒle
    exact Nat.mul_left_cancel Nat.card_pos (le_antisymm h1 h2)
  have hb1 : Nat.card (E.map φ) = q := by
    rw [hb3, mul_comm 3 q] at hmul
    exact Nat.mul_right_cancel (by norm_num : 0 < (3 : ℕ)) hmul
  have hker_le : φ.ker ≤ Y.comap φ := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact Y.one_mem
  obtain ⟨h, hh⟩ := hconj (E.map φ) Y hĒel hb1 hY hY3
  obtain ⟨m, hm⟩ := hφ h⁻¹
  let E' : Subgroup M := E.map (MulAut.conj m).toMonoidHom
  have hE'el : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE _
  have hYle : Y ≤ E'.map φ := by
    intro y hy
    obtain ⟨e, heE, he⟩ := Subgroup.mem_map.mp (hh (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩))
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj m) e, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨e, heE, rfl⟩
    · rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hm]
      rw [he]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hE'ker : Nat.card (E' ⊓ φ.ker : Subgroup M) = 3 := by
    have hE'ker_eq : E' ⊓ φ.ker =
        (E ⊓ φ.ker : Subgroup M).map (MulAut.conj m).toMonoidHom := by
      dsimp only [E']
      rw [Subgroup.map_inf E φ.ker (MulAut.conj m).toMonoidHom (MulAut.conj m).injective]
      exact (congrArg (fun K : Subgroup M => E.map (MulAut.conj m).toMonoidHom ⊓ K)
        (Subgroup.Normal.map_conj_eq (H := φ.ker) m)).symm
    rw [hE'ker_eq, Subgroup.card_map_of_injective (MulAut.conj m).injective]
    exact hb3
  refine ⟨E' ⊓ Y.comap φ, m, hE'el.mono inf_le_left, ?_, inf_le_right, inf_le_left⟩
  have hmap : (E' ⊓ Y.comap φ).map φ = Y := by
    apply le_antisymm
    · exact (Subgroup.map_le_iff_le_comap).mpr inf_le_right
    · intro y hy
      obtain ⟨x, hxE, hx⟩ := Subgroup.mem_map.mp (hYle hy)
      exact Subgroup.mem_map.mpr
        ⟨x, ⟨hxE, Subgroup.mem_comap.mpr (by rw [hx]; exact hy)⟩, hx⟩
  have hker : (E' ⊓ Y.comap φ) ⊓ φ.ker = E' ⊓ φ.ker := by
    rw [inf_assoc, inf_eq_right.mpr hker_le]
  have hFcount := s15_Three_card_eq_card_map_mul_card_ker φ (E' ⊓ Y.comap φ)
  rw [hmap, hY3, hker, hE'ker] at hFcount
  norm_num at hFcount
  exact hFcount

theorem s15_Three_conj_order_three {H : Type} [Group H] [Finite H]
    (h1 : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 1) :
    (∀ B : Subgroup H, IsElemAbelian 3 B → Nat.card B ≤ 3) ∧
      ∀ A B : Subgroup H, IsElemAbelian 3 A → Nat.card A = 3 → IsElemAbelian 3 B →
        Nat.card B = 3 → ∃ h : H, B.map (MulAut.conj h).toMonoidHom ≤ A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨?_, ?_⟩
  · intro B hB
    have hBp : IsPGroup 3 B := hB.isPGroup
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    have hn1 : n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hB hn
    have hnle : n ≤ 1 := hn1.trans h1
    calc Nat.card B = 3 ^ n := hn
      _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hnle
      _ = 3 := by norm_num
  · intro A B _ hA _ hB
    exact s15_Three_exists_conj_le h1 hA hB

end Lift

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
