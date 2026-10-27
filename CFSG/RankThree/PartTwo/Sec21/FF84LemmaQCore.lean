module

public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaQStrong
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaQA5
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaQQuot
public import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

theorem lemmaQ_sup_eq {X : Type} [Group X] [Finite X] (P A B : Subgroup X) (hP9 : Nat.card P = 9)
    (hA : A ≤ P) (hB : B ≤ P) (hA3 : Nat.card A = 3) (hB3 : Nat.card B = 3) (hAB : A ⊓ B = ⊥) :
    A ⊔ B = P := by
  let f : ↥A × ↥B → ↥P := fun p => ⟨p.1 * p.2, P.mul_mem (hA p.1.2) (hB p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : X) * b = a' * b' := congrArg Subtype.val h
    have hu : (a' : X)⁻¹ * a = b' * (b : X)⁻¹ := by
      calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * ((a : X) * b) * (b : X)⁻¹ := by group
        _ = (a' : X)⁻¹ * ((a' : X) * b') * (b : X)⁻¹ := by rw [h']
        _ = b' * (b : X)⁻¹ := by group
    have h1 : (a' : X)⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, by rw [hu]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at h1
    have hae : a = a' := Subtype.ext h1.symm
    have hbe : b = b' := by
      apply Subtype.ext
      have : (a : X) * b = (a : X) * b' := by rw [h', hae]
      exact mul_left_cancel this
    rw [hae, hbe]
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hA3, hB3, hP9])
  apply le_antisymm (sup_le hA hB)
  intro q hq
  obtain ⟨p, hp⟩ := hbij.2 ⟨q, hq⟩
  have hq' : (q : X) = (p.1 : X) * (p.2 : X) := (congrArg Subtype.val hp).symm
  rw [hq']
  exact Subgroup.mul_mem _ (le_sup_left (a := A) p.1.2) (le_sup_right (b := B) p.2.2)

theorem lemmaQ_conj_of_card_three {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : ¬ 9 ∣ Nat.card Γ)
    (M T : Subgroup Γ) (hM : Nat.card M = 3) (hT : Nat.card T = 3) :
    ∃ g : Γ, ∀ x ∈ T, ∃ m ∈ M, x = g * m * g⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ S : Subgroup Γ, Nat.card S = 3 → ∃ Syl : Sylow 3 Γ, (Syl : Subgroup Γ) = S := by
    intro S hS
    have hpg : IsPGroup 3 S := (IsPGroup.iff_card).2 ⟨1, by rw [hS]; norm_num⟩
    have hdvd : Nat.card Γ = 3 * S.index := by
      have := Subgroup.card_mul_index S
      rw [hS] at this
      exact this.symm
    have hind : ¬ 3 ∣ S.index := fun h => hΓ (by rw [hdvd]; exact Nat.mul_dvd_mul_left 3 h)
    exact ⟨hpg.toSylow hind, rfl⟩
  obtain ⟨S1, hS1⟩ := hsyl M hM
  obtain ⟨S2, hS2⟩ := hsyl T hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ S1 S2
  refine ⟨g, fun x hx => ?_⟩
  have hx2 : x ∈ (S2 : Subgroup Γ) := by rw [hS2]; exact hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hS1] at hx2
  refine ⟨g⁻¹ * x * g, ?_, ?_⟩
  · simpa [MulAut.smul_def, MulAut.conj_apply] using hx2
  · group

theorem lemmaQ_core (hKF1 : FF84KF1) (hKS : FF84KSOut) {X : Type} [Group X] [Finite X]
    (hX : KCore.KGroupNonab InCatalog X) (P A B K : Subgroup X)
    (hP : IsSylowOf 3 P ⊤) (hP9 : Nat.card P = 9) (hA : A ≤ P) (hB : B ≤ P)
    (hA3 : Nat.card A = 3) (hB3 : Nat.card B = 3) (hAB : A ⊓ B = ⊥)
    (hKC : K ≤ CenS B) (hKn : (K.subgroupOf (CenS B)).Normal) (hK60 : Nat.card K = 60)
    (hKs : IsSimpleGroup K) (hAK : A ≤ K) (hiii : ¬ ∃ g : X, conjBy g A = B) :
    (K ⊔ pPrimeCore 3 X).Normal := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPgrp : IsPGroup 3 P := hP.2.1
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    have hbot : A = ⊥ := eq_bot_iff.2 (fun x hx => Subgroup.mem_bot.2 (by
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩))
    rw [hbot, Subgroup.card_bot] at hA3
    norm_num at hA3
  have ha3 : a ^ 3 = 1 := by
    have h := (pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩))
    rw [hA3] at h
    simpa using congrArg Subtype.val h
  have hKa3 : (⟨a, hAK ha⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hKa1 : (⟨a, hAK ha⟩ : K) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  obtain ⟨t, ht⟩ := exists_conj_inv_of_card_sixty hK60 hKa3 hKa1
  have ht' : (t : X) * a * (t : X)⁻¹ = a⁻¹ := by
    have := congrArg Subtype.val ht
    simpa using this
  have htB : ∀ b ∈ B, (t : X) * b = b * (t : X) := by
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.1 (hKC t.2)) b hb).symm
  obtain ⟨hscA, hscB⟩ :=
    lemmaQ_strong_closure P A B hP hP9 hA hB hA3 hB3 hAB hiii (t : X) a ha ha1 ht' htB
  have hsup : A ⊔ B = P := lemmaQ_sup_eq P A B hP9 hA hB hA3 hB3 hAB
  have hquot := lemmaQ_quot_inf_bot hKF1 hKS hX P A B hP hP9 hA hB hA3 hB3 hAB hsup hscA hscB
  have hOcop : Nat.Coprime 3 (Nat.card (pPrimeCore 3 X)) :=
    pPrimeCore_coprime_card (p := 3) (G := X)
  have hO3 : ¬ 3 ∣ Nat.card (pPrimeCore 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hOcop
  have hPO : P ⊓ pPrimeCore 3 X = ⊥ := lemmaQ_inf_eq_bot hPgrp hOcop
  have hBO : B ⊓ pPrimeCore 3 X = ⊥ := eq_bot_iff.2 ((inf_le_inf hB le_rfl).trans hPO.le)
  have hAO : A ⊓ pPrimeCore 3 X = ⊥ := eq_bot_iff.2 ((inf_le_inf hA le_rfl).trans hPO.le)
  set π : X →* X ⧸ pPrimeCore 3 X := QuotientGroup.mk' (pPrimeCore 3 X) with hπdef
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hBbc : Nat.card (B.map π) = 3 := (lemmaQ_card_map _ B hBO).trans hB3
  have hAbc : Nat.card (A.map π) = 3 := (lemmaQ_card_map _ A hAO).trans hA3
  have hPbar9 : Nat.card (P.map π) = 9 := (lemmaQ_card_map _ P hPO).trans hP9
  have hBgrp : IsPGroup 3 B := (IsPGroup.iff_card).2 ⟨1, by rw [hB3]; norm_num⟩
  set NA : Subgroup (X ⧸ pPrimeCore 3 X) :=
    Subgroup.normalClosure ((A.map π : Subgroup _) : Set _) with hNAdef
  set NB : Subgroup (X ⧸ pPrimeCore 3 X) :=
    Subgroup.normalClosure ((B.map π : Subgroup _) : Set _) with hNBdef
  have hNAB : NA ⊓ NB = ⊥ := hquot
  haveI hNAn : NA.Normal := by rw [hNAdef]; infer_instance
  haveI hNBn : NB.Normal := by rw [hNBdef]; infer_instance
  have hKA : K ≤ Subgroup.normalClosure (A : Set X) := by
    let L : Subgroup K := (Subgroup.normalClosure (A : Set X)).subgroupOf K
    rcases hKs.eq_bot_or_eq_top_of_normal L with h | h
    · exfalso
      have hmem : (⟨a, hAK ha⟩ : K) ∈ L :=
        Subgroup.mem_subgroupOf.2 (Subgroup.subset_normalClosure ha)
      rw [h, Subgroup.mem_bot] at hmem
      exact ha1 (congrArg Subtype.val hmem)
    · intro k hk
      have hmem : (⟨k, hk⟩ : K) ∈ L := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hmem
  have hKbarN : K.map π ≤ NA := by
    calc K.map π ≤ (Subgroup.normalClosure (A : Set X)).map π := Subgroup.map_mono hKA
      _ = Subgroup.normalClosure (π '' (A : Set X)) := Subgroup.map_normalClosure _ π hπsurj
      _ = NA := by rw [hNAdef, Subgroup.coe_map]
  have hAN : A.map π ≤ NA := fun x hx => Subgroup.subset_normalClosure hx
  have hNBmem : ∀ b ∈ B.map π, b ∈ NB := fun b hb => Subgroup.subset_normalClosure hb
  have hcomm : ∀ x ∈ NA, ∀ b ∈ B.map π, b * x = x * b := by
    intro x hx b hb
    have h1 : x * b * x⁻¹ * b⁻¹ ∈ NA := by
      have h2 : b * x⁻¹ * b⁻¹ ∈ NA := hNAn.conj_mem _ (NA.inv_mem hx) b
      have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [e]
      exact NA.mul_mem hx h2
    have h2 : x * b * x⁻¹ * b⁻¹ ∈ NB := by
      have h3 : x * b * x⁻¹ ∈ NB := hNBn.conj_mem _ (hNBmem b hb) x
      exact NB.mul_mem h3 (NB.inv_mem (hNBmem b hb))
    have h4 : x * b * x⁻¹ * b⁻¹ ∈ NA ⊓ NB := ⟨h1, h2⟩
    rw [hNAB, Subgroup.mem_bot] at h4
    calc b * x = (x * b * x⁻¹ * b⁻¹)⁻¹ * (x * b) := by group
      _ = x * b := by rw [h4, inv_one, one_mul]
  have hcent : Subgroup.centralizer ((B.map π : Subgroup _) : Set _) = (CenS B).map π :=
    CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hO3 hBgrp
  have hNAc : ∀ n ∈ NA, ∃ c ∈ CenS B, π c = n := by
    intro n hn
    have hn' : n ∈ Subgroup.centralizer ((B.map π : Subgroup _) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hcomm n hn b hb
    rw [hcent] at hn'
    obtain ⟨c, hc, hcn⟩ := Subgroup.mem_map.1 hn'
    exact ⟨c, hc, hcn⟩
  have hKc : ∀ c ∈ CenS B, ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    have := hKn.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hKbarNorm : ∀ n ∈ NA, ∀ k ∈ K.map π, n * k * n⁻¹ ∈ K.map π := by
    intro n hn k hk
    obtain ⟨c, hc, rfl⟩ := hNAc n hn
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.1 hk
    exact Subgroup.mem_map.2 ⟨c * k₀ * c⁻¹, hKc c hc k₀ hk₀, by simp [map_mul, map_inv]⟩
  have hPbarSyl : IsSylowOf 3 (P.map π) ⊤ := lemmaQ_sylow_map P hP hP9 hPO
  let hS0 : Sylow 3 (X ⧸ pPrimeCore 3 X) := hPbarSyl.2.1.toSylow (by
    have := hPbarSyl.2.2
    rw [Subgroup.relIndex_top_right] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 this)
  have hS0coe : (hS0 : Subgroup (X ⧸ pPrimeCore 3 X)) = P.map π :=
    IsPGroup.toSylow_coe _ _
  have hNA9 : ¬ 9 ∣ Nat.card NA := by
    intro h9
    obtain ⟨Q₀, hQ₀⟩ :=
      Sylow.exists_subgroup_card_pow_prime (G := ↥NA) 3 (n := 2) (by simpa using h9)
    set Q : Subgroup (X ⧸ pPrimeCore 3 X) := Q₀.map NA.subtype with hQdef
    have hQcard : Nat.card Q = 9 := by
      rw [hQdef, Subgroup.card_map_of_injective NA.subtype_injective, hQ₀]
      norm_num
    have hQle : Q ≤ NA := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.1 hy
      exact x.2
    have hQ3 : IsPGroup 3 Q := (IsPGroup.iff_card).2 ⟨2, by rw [hQcard]; norm_num⟩
    obtain ⟨R, hQR⟩ := hQ3.exists_le_sylow
    have hS0card : Nat.card (hS0 : Subgroup (X ⧸ pPrimeCore 3 X)) = 9 := by
      rw [hS0coe, hPbar9]
    have hRcard : Nat.card (R : Subgroup (X ⧸ pPrimeCore 3 X)) = 9 := by
      have h1 := Sylow.card_eq_multiplicity R
      have h2 := Sylow.card_eq_multiplicity hS0
      calc Nat.card (R : Subgroup (X ⧸ pPrimeCore 3 X))
          = Nat.card (hS0 : Subgroup (X ⧸ pPrimeCore 3 X)) := by rw [h1, h2]
        _ = 9 := hS0card
    have hQR' : Q = (R : Subgroup (X ⧸ pPrimeCore 3 X)) :=
      Subgroup.eq_of_le_of_card_ge hQR (by rw [hQcard, hRcard])
    have hRNA : (R : Subgroup (X ⧸ pPrimeCore 3 X)) ≤ NA := hQR' ▸ hQle
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (X ⧸ pPrimeCore 3 X) hS0 R
    have hS0NA : (hS0 : Subgroup (X ⧸ pPrimeCore 3 X)) ≤ NA := by
      intro x hx
      have h1 : MulAut.conj g • x ∈ (R : Subgroup (X ⧸ pPrimeCore 3 X)) := by
        rw [← hg, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hx
      have h2 : g * x * g⁻¹ ∈ NA := by
        have := hRNA h1
        rwa [MulAut.smul_def, MulAut.conj_apply] at this
      have h4 := hNAn.conj_mem _ h2 g⁻¹
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at h4
    have hBbarNA : B.map π ≤ NA := by
      intro x hx
      apply hS0NA
      rw [hS0coe]
      exact Subgroup.map_mono hB hx
    have hB0 : B.map π ≤ NA ⊓ NB := le_inf hBbarNA (fun x hx => hNBmem x hx)
    rw [hNAB, le_bot_iff] at hB0
    rw [hB0, Subgroup.card_bot] at hBbc
    norm_num at hBbc
  have hAbNA : Nat.card ↥((A.map π).subgroupOf NA) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hAbc]
  have hconjA : ∀ y : X ⧸ pPrimeCore 3 X, ∀ a' ∈ A.map π, y * a' * y⁻¹ ∈ K.map π := by
    intro y a' ha'
    let T : Subgroup (X ⧸ pPrimeCore 3 X) := (A.map π).map (MulAut.conj y).toMonoidHom
    have hyT : ∀ x ∈ A.map π, y * x * y⁻¹ ∈ T := fun x hx =>
      Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have hTNA : T ≤ NA := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
      have := hNAn.conj_mem x (hAN hx) y
      simpa [MulAut.conj_apply] using this
    have hTc : Nat.card T = 3 :=
      (Subgroup.card_map_of_injective (MulAut.conj y).injective).trans hAbc
    have hTc' : Nat.card ↥(T.subgroupOf NA) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTNA).toEquiv, hTc]
    obtain ⟨g, hg⟩ := lemmaQ_conj_of_card_three (Γ := ↥NA) (by simpa using hNA9)
      ((A.map π).subgroupOf NA) (T.subgroupOf NA) hAbNA hTc'
    have hmemT : (⟨y * a' * y⁻¹, hTNA (hyT a' ha')⟩ : ↥NA) ∈ T.subgroupOf NA :=
      Subgroup.mem_subgroupOf.2 (hyT a' ha')
    obtain ⟨m, hm, hx⟩ := hg _ hmemT
    have hxv : y * a' * y⁻¹ = (g : X ⧸ pPrimeCore 3 X) * (m : X ⧸ pPrimeCore 3 X) *
        ((g : X ⧸ pPrimeCore 3 X))⁻¹ := congrArg Subtype.val hx
    rw [hxv]
    have hmA : (m : X ⧸ pPrimeCore 3 X) ∈ A.map π := Subgroup.mem_subgroupOf.1 hm
    have hmK : (m : X ⧸ pPrimeCore 3 X) ∈ K.map π := Subgroup.map_mono hAK hmA
    exact hKbarNorm _ g.2 _ hmK
  have hNAle : NA ≤ K.map π := by
    rw [hNAdef]
    unfold Subgroup.normalClosure
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨a', ha', hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨y, hy⟩ := isConj_iff.1 hax
    rw [← hy]
    exact hconjA y a' ha'
  have hEq : NA = K.map π := le_antisymm hNAle hKbarN
  have hKbarNormal : (K.map π).Normal := by
    rw [← hEq]
    exact hNAn
  have hfin : K ⊔ pPrimeCore 3 X = (K.map π).comap π := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  rw [hfin]
  exact Subgroup.Normal.comap hKbarNormal π

end CFSG.RankThree.PartTwo.Sec21.FF84
