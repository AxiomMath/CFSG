module

public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Sylow
public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Fusion
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerStructure

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

private theorem eq_or_eq_inv_of_mem_zpowers' {b : H} (hb : orderOf b = 3) {x : H}
    (hx : x ∈ Subgroup.zpowers b) (hx1 : x ≠ 1) : x = b ∨ x = b⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hb] at hx1 ⊢
  have hk : (k % ((3 : ℕ) : ℤ)) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨
      k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with h0 | h0 | h0 <;> rw [h0] at hx1 ⊢
  · exact absurd (zpow_zero b) hx1
  · left; exact zpow_one b
  · right
    have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hb3])

theorem conj_eq_self_of_odd_of_mem_zpowers {b g : H} (hb : orderOf b = 3)
    (hg : Odd (orderOf g)) (hmem : g * b * g⁻¹ ∈ Subgroup.zpowers b) :
    g * b * g⁻¹ = b := by
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hb
  have hne : g * b * g⁻¹ ≠ 1 := by
    intro h1
    apply hb1
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  rcases eq_or_eq_inv_of_mem_zpowers' hb hmem hne with h1 | h2
  · exact h1
  · exfalso
    obtain ⟨q, hq⟩ := hg
    let φ : MulAut H := MulAut.conj g
    have hφb : φ b = b⁻¹ := by simpa [φ] using h2
    have hφ2 : (φ ^ 2) b = b := by
      calc (φ ^ 2) b = φ (φ b) := by rw [pow_two, MulAut.mul_apply]
        _ = φ b⁻¹ := by rw [hφb]
        _ = (φ b)⁻¹ := by simp
        _ = (b⁻¹)⁻¹ := by rw [hφb]
        _ = b := inv_inv b
    have hφn : φ ^ orderOf g = 1 := by
      have hmap : MulAut.conj (g ^ orderOf g) = (MulAut.conj g) ^ orderOf g :=
        map_pow (MulAut.conj : H →* MulAut H) g (orderOf g)
      rw [pow_orderOf_eq_one, map_one] at hmap
      simpa [φ] using hmap.symm
    rw [hq] at hφn
    have h2q : ∀ q : ℕ, ((φ ^ 2) ^ q) b = b := by
      intro q
      induction q with
      | zero => simp
      | succ q ih => rw [pow_succ, MulAut.mul_apply, hφ2, ih]
    have h1 : (φ ^ (2 * q + 1)) b = b := by
      rw [hφn]
      simp
    have h2' : (φ ^ (2 * q + 1)) b = b⁻¹ := by
      calc (φ ^ (2 * q + 1)) b = (φ ^ (2 * q)) (φ b) := by
            rw [pow_succ, MulAut.mul_apply]
        _ = (φ ^ (2 * q)) b⁻¹ := by rw [hφb]
        _ = ((φ ^ (2 * q)) b)⁻¹ := by simp
        _ = (((φ ^ 2) ^ q) b)⁻¹ := by rw [pow_mul]
        _ = b⁻¹ := by rw [h2q q]
    rw [h1] at h2'
    have hb2 : b ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp h2'
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hb2
    rw [hb] at hdvd
    norm_num at hdvd


theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  rw [CFSG.QuasiDihedralFusion.oddCore_eq_pPrimeCore X]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem FS79Hyp.pgroup_le_cen (h : FS79Hyp b t b₁ b₂ J) {S : Subgroup H} (hS : IsPGroup 3 S)
    (hbS : b ∈ S) : S ≤ Cen b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTop : IsPGroup 3 (⊤ : Subgroup ↥S) := hS.of_equiv Subgroup.topEquiv.symm
  let P : Sylow 3 ↥S := hTop.toSylow (by simp [Subgroup.index_top])
  have hPtop : (P : Subgroup ↥S) = ⊤ := rfl
  have hmap : (P : Subgroup ↥S).map S.subtype = S := by
    rw [hPtop, Subgroup.map_top, Subgroup.range_subtype]
  intro g hg
  have hbP : b ∈ (P : Subgroup ↥S).map S.subtype := by
    rw [hmap]
    exact hbS
  have hle : conjBy g (Subgroup.zpowers b) ≤ (P : Subgroup ↥S).map S.subtype := by
    rw [hmap]
    rintro _ ⟨x, hx, rfl⟩
    exact S.mul_mem (S.mul_mem hg ((Subgroup.zpowers_le.mpr hbS) hx)) (S.inv_mem hg)
  have hD := h.weaklyClosed_sylow (M := S) (Subgroup.zpowers_le.mpr hbS) P hbP
    (conjBy g (Subgroup.zpowers b)) ⟨g, rfl⟩ hle
  have hmem : g * b * g⁻¹ ∈ Subgroup.zpowers b := by
    rw [← hD]
    exact ⟨b, Subgroup.mem_zpowers b, by simp [MulAut.conj_apply]⟩
  have hodd : Odd (orderOf g) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨g, hg⟩
    have : orderOf g = 3 ^ k := by
      rw [← Subgroup.orderOf_mk g hg]
      exact hk
    rw [this]
    exact (show Odd 3 by decide).pow
  have hfix := conj_eq_self_of_odd_of_mem_zpowers h.ord_b hodd hmem
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc g * b = (g * b * g⁻¹) * g := by group
    _ = b * g := by rw [hfix]

theorem FS79Hyp.inf_oddCore_eq_bot (h : FS79Hyp b t b₁ b₂ J) :
    J ⊓ CFSG.oddCore H = ⊥ := by
  classical
  obtain ⟨e⟩ := h.J_perm
  set O : Subgroup H := CFSG.oddCore H with hO
  set K : Subgroup H := J ⊓ O with hK
  let Kj : Subgroup ↥J := K.subgroupOf J
  have hKjn : Kj.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨J.mul_mem (J.mul_mem g.2 x.2) (J.inv_mem g.2) , by
      simpa using (CFSG.oddCore_normal H).conj_mem _ hx.2 (g : H)⟩⟩
  let N : Subgroup (Equiv.Perm (Fin 6)) := Kj.map e.toMonoidHom
  haveI hNn : N.Normal := Subgroup.Normal.map hKjn e.toMonoidHom e.surjective
  have hcardN : Nat.card N = Nat.card K := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ≤ J)).toEquiv
  have hKodd : Odd (Nat.card K) :=
    (odd_card_oddCore' H).of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_right : K ≤ O))
  by_cases hN : N = ⊥
  · have hKj : Kj = ⊥ := by
      exact (Subgroup.map_eq_bot_iff_of_injective Kj e.injective).mp hN
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥J) ∈ Kj := hx
    rw [hKj, Subgroup.mem_bot] at hx'
    have := congrArg Subtype.val hx'
    simpa using this
  · exfalso
    have hnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
    have hA := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp) hnt
    have hdvd : Nat.card (alternatingGroup (Fin 6)) ∣ Nat.card N := Subgroup.card_dvd_of_le hA
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup]
      simp [Nat.factorial]
    rw [h360, hcardN] at hdvd
    have h2 : 2 ∣ Nat.card K := (show 2 ∣ 360 by norm_num).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h2)

theorem FS79Hyp.isSylowOf_zpowers_oddCore (h : FS79Hyp b t b₁ b₂ J) (hb : b ∈ CFSG.oddCore H) :
    IsSylowOf 3 (Subgroup.zpowers b) (CFSG.oddCore H) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup H := CFSG.oddCore H with hO
  set B : Subgroup H := Subgroup.closure ({b, b₁, b₂} : Set H) with hB
  set B₁ : Subgroup H := Subgroup.closure ({b₁, b₂} : Set H) with hB₁
  have hbO : Subgroup.zpowers b ≤ O := Subgroup.zpowers_le.mpr hb
  have hcardb : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, h.ord_b]
  have hb3 : IsPGroup 3 (Subgroup.zpowers b) := IsPGroup.of_card (n := 1) (by rw [hcardb]; simp)
  have hA : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf O) :=
    hb3.of_equiv (Subgroup.subgroupOfEquivOfLe hbO).symm
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  set S : Subgroup H := (P : Subgroup ↥O).map O.subtype with hSdef
  have hS3 : IsPGroup 3 S := P.isPGroup'.map O.subtype
  have hSO : S ≤ O := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hbS : b ∈ S := ⟨⟨b, hb⟩, hAP (show (⟨b, hb⟩ : ↥O) ∈ (Subgroup.zpowers b).subgroupOf O from
    Subgroup.mem_zpowers b), rfl⟩
  have hSC : S ≤ Cen b := h.pgroup_le_cen hS3 hbS
  have hSN : S ≤ Nor (Subgroup.zpowers b) := hSC.trans h.cen_le_nor
  obtain ⟨n, hnN, hn⟩ := L14.exists_conj_le_sylowOf (G := H) h.isSylow_B_N hSN hS3
  set S' : Subgroup H := conjBy n S with hS'
  have hS'B : S' ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hn x hx
  have hS'O : S' ≤ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact (CFSG.oddCore_normal H).conj_mem x (hSO hx) n
  have hB₁J : B₁ ≤ J := by
    rw [hB₁, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h.b₁_mem
    · exact h.b₂_mem
  have hB₁B : B₁ ≤ B := by
    rw [hB₁, hB, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hdisj : S' ⊓ B₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ J ⊓ O := ⟨hB₁J hx.2, hS'O hx.1⟩
    rw [h.inf_oddCore_eq_bot] at this
    exact this
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    have hE := h.isElemAb_B
    rw [← hB] at hE
    exact fun x hx y hy =>
      congrArg Subtype.val (hE.1.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcomm : ∀ a ∈ S', ∀ c ∈ B₁, Commute a c := fun a ha c hc =>
    hBcomm a (hS'B ha) c (hB₁B hc)
  have hcardsup := CFSG.card_sup_eq_mul_of_commute S' B₁ hcomm hdisj
  have hsupB : S' ⊔ B₁ ≤ B := sup_le hS'B hB₁B
  have hcardB : Nat.card B = 27 := by
    have hE := h.isElemAb_B
    rw [← hB] at hE
    exact hE.2
  have hcardB₁ : Nat.card B₁ = 9 := by
    rw [hB₁]
    simpa using h.E9.2
  have hle27 : Nat.card ↥(S' ⊔ B₁) ≤ 27 := by
    rw [← hcardB]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hsupB)
  rw [hcardsup, hcardB₁] at hle27
  have hS'3 : Nat.card S' ≤ 3 := by omega
  have hcardS : Nat.card S = Nat.card S' :=
    (Subgroup.card_map_of_injective (K := S) (f := (MulAut.conj n).toMonoidHom)
      (MulAut.conj n).injective).symm
  have hbSle : Subgroup.zpowers b ≤ S := Subgroup.zpowers_le.mpr hbS
  have hSeq : S = Subgroup.zpowers b := by
    symm
    exact Subgroup.eq_of_le_of_card_ge hbSle (by rw [hcardb, hcardS]; exact hS'3)
  refine ⟨hbO, hb3, ?_⟩
  have hrel : (Subgroup.zpowers b).relIndex O = (P : Subgroup ↥O).index := by
    rw [← hSeq, hSdef, Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective O.subtype_injective]
  rw [hrel]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr P.not_dvd_index

end CFSG.RankThree.PartTwo.Sec21.FF81
