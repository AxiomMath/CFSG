module

public import CFSG.RankThree.PartTwo.Sec21.FF84S23

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

lemma lemmaQ_inf_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {S N : Subgroup Γ}
    (hS : IsPGroup 3 S) (hcop : Nat.Coprime 3 (Nat.card N)) : S ⊓ N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨k, hk⟩ := hS ⟨x, hx.1⟩
  have hk' : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (⟨x, hx.2⟩ : ↥N) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk'))
  have h2 : orderOf (⟨x, hx.2⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
  have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hcop) h1 h2
  have := orderOf_eq_one_iff.1 h3
  simpa using congrArg Subtype.val this

private lemma lq_card_sup {Γ : Type*} [Group Γ] [Finite Γ] (A B : Subgroup Γ) [B.Normal]
    (h : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_sup_right A B
  have h2 : B.relIndex A = Nat.card A := by
    rw [← Subgroup.inf_relIndex_right B A, inf_comm, h, Subgroup.relIndex_bot_left]
  have h3 := Subgroup.card_mul_index (B.subgroupOf (A ⊔ B))
  have h4 : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h4] at h3
  have h5 : (B.subgroupOf (A ⊔ B)).index = Nat.card A := by
    rw [← h2, ← h1]; rfl
  rw [h5] at h3
  rw [← h3, mul_comm]

open scoped Pointwise in
private lemma lq_conj_into {Γ : Type*} [Group Γ] [Finite Γ] (N S T : Subgroup Γ) [N.Normal]
    (hcop : Nat.Coprime 3 (Nat.card N)) (hS : IsPGroup 3 S) (hT : IsPGroup 3 T)
    (hTle : T ≤ S ⊔ N) : ∃ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSM : S ≤ S ⊔ N := le_sup_left
  have hcardM : Nat.card ↥(S ⊔ N) = Nat.card S * Nat.card N :=
    lq_card_sup S N (lemmaQ_inf_eq_bot hS hcop)
  have hS' : IsPGroup 3 (S.subgroupOf (S ⊔ N)) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hS
    exact IsPGroup.of_card ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv).trans ha)
  obtain ⟨P₁, hP₁le⟩ := hS'.exists_le_sylow
  have hP₁ : (P₁ : Subgroup ↥(S ⊔ N)) = S.subgroupOf (S ⊔ N) := by
    refine (Subgroup.eq_of_le_of_card_ge hP₁le ?_).symm
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 P₁.isPGroup'
    have hdvd : Nat.card (P₁ : Subgroup ↥(S ⊔ N)) ∣ Nat.card S * Nat.card N := by
      rw [← hcardM]; exact Subgroup.card_subgroup_dvd_card _
    rw [ha] at hdvd
    have hdS : 3 ^ a ∣ Nat.card S := (Nat.Coprime.pow_left a hcop).dvd_of_dvd_mul_right hdvd
    rw [ha, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv]
    exact Nat.le_of_dvd Nat.card_pos hdS
  have hT' : IsPGroup 3 (T.subgroupOf (S ⊔ N)) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hT
    exact IsPGroup.of_card ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv).trans ha)
  obtain ⟨P₂, hP₂le⟩ := hT'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(S ⊔ N)) P₁ P₂
  have hconj : ∀ t ∈ T, (g : Γ)⁻¹ * t * (g : Γ) ∈ S := by
    intro t ht
    have htM : t ∈ S ⊔ N := hTle ht
    have h1 : (⟨t, htM⟩ : ↥(S ⊔ N)) ∈ (P₂ : Subgroup ↥(S ⊔ N)) :=
      hP₂le (Subgroup.mem_subgroupOf.2 ht)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : g⁻¹ * (⟨t, htM⟩ : ↥(S ⊔ N)) * g ∈ (P₁ : Subgroup ↥(S ⊔ N)) := by
      simpa [MulAut.smul_def] using h1
    rw [hP₁] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  have hgM : (g : Γ)⁻¹ ∈ S ⊔ N := (S ⊔ N).inv_mem g.2
  have hgmem : (g : Γ)⁻¹ ∈ (S : Set Γ) * (N : Set Γ) := by
    rw [← Subgroup.mul_normal]; exact hgM
  obtain ⟨s₀, hs₀, n₀, hn₀, hgs⟩ := hgmem
  have hgs' : s₀ * n₀ = (g : Γ)⁻¹ := hgs
  refine ⟨n₀, hn₀, fun t ht => ?_⟩
  have e : (g : Γ) = (s₀ * n₀)⁻¹ := by rw [hgs']; simp
  have e2 : n₀ * t * n₀⁻¹ = s₀⁻¹ * ((g : Γ)⁻¹ * t * (g : Γ)) * s₀ := by
    rw [e]; group
  rw [e2]
  exact S.mul_mem (S.mul_mem (S.inv_mem hs₀) (hconj t ht)) hs₀

lemma lemmaQ_card_map {H : Type} [Group H] (O K : Subgroup H) [O.Normal]
    (hK : K ⊓ O = ⊥) : Nat.card (K.map (QuotientGroup.mk' O)) = Nat.card K := by
  have hinj : Function.Injective (fun x : K =>
      (⟨QuotientGroup.mk' O (x : H), Subgroup.mem_map_of_mem _ x.2⟩ :
        K.map (QuotientGroup.mk' O))) := by
    intro x y hxy
    have h1 : QuotientGroup.mk' O (x : H) = QuotientGroup.mk' O (y : H) :=
      congrArg Subtype.val hxy
    have h2 : (x : H)⁻¹ * (y : H) ∈ O := QuotientGroup.eq.1 h1
    have h3 : (x : H)⁻¹ * (y : H) ∈ K ⊓ O := ⟨K.mul_mem (K.inv_mem x.2) y.2, h2⟩
    rw [hK, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3
  have hsurj : Function.Surjective (fun x : K =>
      (⟨QuotientGroup.mk' O (x : H), Subgroup.mem_map_of_mem _ x.2⟩ :
        K.map (QuotientGroup.mk' O))) := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    exact ⟨⟨x, hx⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

theorem lemmaQ_sylow_map {X : Type} [Group X] [Finite X] (P : Subgroup X)
    (hP : IsSylowOf 3 P ⊤) (hP9 : Nat.card P = 9) (hPO : P ⊓ pPrimeCore 3 X = ⊥) :
    IsSylowOf 3 (P.map (QuotientGroup.mk' (pPrimeCore 3 X))) ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hOn : (pPrimeCore 3 X).Normal := pPrimeCore_normal (p := 3) (G := X)
  have hOcop : Nat.Coprime 3 (Nat.card (pPrimeCore 3 X)) :=
    pPrimeCore_coprime_card (p := 3) (G := X)
  have hP3 : Nat.Coprime 3 P.index := by
    have := hP.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hPbar9 : Nat.card (P.map (QuotientGroup.mk' (pPrimeCore 3 X))) = 9 :=
    (lemmaQ_card_map (pPrimeCore 3 X) P hPO).trans hP9
  have hidx : Nat.card (pPrimeCore 3 X) * (P.map (QuotientGroup.mk' (pPrimeCore 3 X))).index =
      P.index := by
    have e1 := Subgroup.card_mul_index (pPrimeCore 3 X)
    have e2 := Subgroup.card_mul_index P
    have e3 := Subgroup.card_mul_index (P.map (QuotientGroup.mk' (pPrimeCore 3 X)))
    rw [hP9] at e2
    rw [hPbar9] at e3
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 9 by norm_num)
    calc 9 * (Nat.card (pPrimeCore 3 X) *
          (P.map (QuotientGroup.mk' (pPrimeCore 3 X))).index)
        = Nat.card (pPrimeCore 3 X) * (9 * (P.map (QuotientGroup.mk' (pPrimeCore 3 X))).index) := by
          ring
      _ = Nat.card (pPrimeCore 3 X) * Nat.card (X ⧸ pPrimeCore 3 X) := by rw [e3]
      _ = Nat.card (pPrimeCore 3 X) * (pPrimeCore 3 X).index := rfl
      _ = Nat.card X := e1
      _ = 9 * P.index := e2.symm
  unfold IsSylowOf
  refine ⟨le_top, (IsPGroup.iff_card).2 ⟨2, hPbar9.trans (by norm_num)⟩, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ hidx) hP3

theorem lemmaQ_quot_inf_bot (hKF1 : FF84KF1) (hKS : FF84KSOut) {X : Type} [Group X] [Finite X]
    (hX : KCore.KGroupNonab InCatalog X) (P A B : Subgroup X) (hP : IsSylowOf 3 P ⊤)
    (hP9 : Nat.card P = 9) (hA : A ≤ P) (hB : B ≤ P) (hA3 : Nat.card A = 3)
    (hB3 : Nat.card B = 3) (hAB : A ⊓ B = ⊥) (hsup : A ⊔ B = P)
    (hscA : IsStronglyClosedIn P (A : Set X)) (hscB : IsStronglyClosedIn P (B : Set X)) :
    Subgroup.normalClosure
        (((A.map (QuotientGroup.mk' (pPrimeCore 3 X)) : Subgroup (X ⧸ pPrimeCore 3 X)) :
          Set (X ⧸ pPrimeCore 3 X))) ⊓
      Subgroup.normalClosure
        (((B.map (QuotientGroup.mk' (pPrimeCore 3 X)) : Subgroup (X ⧸ pPrimeCore 3 X)) :
          Set (X ⧸ pPrimeCore 3 X))) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup X := pPrimeCore 3 X with hOdef
  haveI hOn : O.Normal := pPrimeCore_normal (p := 3) (G := X)
  have hOcop : Nat.Coprime 3 (Nat.card O) := pPrimeCore_coprime_card (p := 3) (G := X)
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπdef
  have hmk : ∀ a b : X, π a = π b ↔ a⁻¹ * b ∈ O := fun a b => QuotientGroup.eq
  have hπO : ∀ x ∈ O, π x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).2 hx
  have hπker : ∀ x : X, π x = 1 → x ∈ O := fun x hx => (QuotientGroup.eq_one_iff x).1 hx
  obtain ⟨-, hPgrp, hP3'⟩ := hP
  have hP3 : Nat.Coprime 3 P.index := by rwa [Subgroup.relIndex_top_right] at hP3'
  have hAP : A ≤ P := hA
  have hBP : B ≤ P := hB
  have hPO : P ⊓ O = ⊥ := lemmaQ_inf_eq_bot hPgrp hOcop
  have hKinf : ∀ K : Subgroup X, K ≤ P → K ⊓ O = ⊥ := fun K hKP =>
    eq_bot_iff.2 ((inf_le_inf hKP le_rfl).trans hPO.le)
  have hK' : KCore.KGroupNonab InCatalog (X ⧸ O) :=
    KCore.KGroupNonab.quotient CFSG.Assembly.inCatalog_isoInvariant hX O
  have hbot : pPrimeCore 3 (X ⧸ O) = ⊥ :=
    pPrimeCore_quotient_eq_bot (G := X) (p := 3) Nat.prime_three
  have hPbar9 : Nat.card (P.map π) = 9 := (lemmaQ_card_map O P hPO).trans hP9
  have hP1bar : Nat.card (A.map π) = 3 := (lemmaQ_card_map O A (hKinf A hAP)).trans hA3
  have hP2bar : Nat.card (B.map π) = 3 := (lemmaQ_card_map O B (hKinf B hBP)).trans hB3
  have hidx : Nat.card O * (P.map π).index = P.index := by
    have e1 := Subgroup.card_mul_index O
    have e2 := Subgroup.card_mul_index P
    have e3 := Subgroup.card_mul_index (P.map π)
    rw [hP9] at e2
    rw [hPbar9] at e3
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 9 by norm_num)
    calc 9 * (Nat.card O * (P.map π).index) = Nat.card O * (9 * (P.map π).index) := by ring
      _ = Nat.card O * Nat.card (X ⧸ O) := by rw [e3]
      _ = Nat.card O * O.index := rfl
      _ = Nat.card X := e1
      _ = 9 * P.index := e2.symm
  have hPbarSyl : IsSylowOf 3 (P.map π) ⊤ := by
    unfold IsSylowOf
    refine ⟨le_top, (IsPGroup.iff_card).2 ⟨2, hPbar9.trans (by norm_num)⟩, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ hidx) hP3
  have hsc : ∀ Q : Subgroup X, IsStronglyClosedIn P (Q : Set X) →
      IsStronglyClosedIn (P.map π) ((Q.map π : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
    intro Q hQsc
    obtain ⟨hQsub, hQcl⟩ := hQsc
    unfold IsStronglyClosedIn
    refine ⟨?_, ?_⟩
    · intro a ha
      have ha' : a ∈ Q.map π := ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha'
      exact Subgroup.mem_map_of_mem π (hQsub hy)
    · intro a ha g hg
      have ha' : a ∈ Q.map π := ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha'
      obtain ⟨g₀, rfl⟩ : ∃ g₀ : X, π g₀ = g := QuotientGroup.mk'_surjective O g
      obtain ⟨u, hu_def⟩ : ∃ u : X, u = g₀⁻¹ * y * g₀ := ⟨_, rfl⟩
      have hπu : π u ∈ P.map π := by
        rw [hu_def, map_mul, map_mul, map_inv]; exact hg
      obtain ⟨p, hp, hpu⟩ := Subgroup.mem_map.1 hπu
      have ho : p⁻¹ * u ∈ O := (hmk p u).1 hpu
      have huPO : u ∈ P ⊔ O := by
        rw [← mul_inv_cancel_left p u]
        exact Subgroup.mul_mem _ ((le_sup_left : P ≤ P ⊔ O) hp) ((le_sup_right : O ≤ P ⊔ O) ho)
      obtain ⟨k, hk⟩ := hPgrp ⟨y, hQsub hy⟩
      have hyk : y ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have huk : u ^ (3 ^ k) = 1 := by
        rw [hu_def, show g₀⁻¹ * y * g₀ = g₀⁻¹ * y * (g₀⁻¹)⁻¹ by simp, conj_pow, hyk]
        simp
      have hzp : IsPGroup 3 (Subgroup.zpowers u) := by
        obtain ⟨j, -, hj⟩ :=
          (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one huk)
        exact (IsPGroup.iff_card).2 ⟨j, by rw [Nat.card_zpowers, hj]⟩
      obtain ⟨n, hnO, hnP⟩ := lq_conj_into O P (Subgroup.zpowers u) hOcop hPgrp hzp
        (Subgroup.zpowers_le.2 huPO)
      have hcut : n * u * n⁻¹ ∈ P := hnP u (Subgroup.mem_zpowers u)
      have hgP : (g₀ * n⁻¹)⁻¹ * y * (g₀ * n⁻¹) ∈ P := by
        have e : (g₀ * n⁻¹)⁻¹ * y * (g₀ * n⁻¹) = n * u * n⁻¹ := by
          rw [hu_def]; group
        rw [e]; exact hcut
      have hgQ : (g₀ * n⁻¹)⁻¹ * y * (g₀ * n⁻¹) ∈ Q := hQcl y hy (g₀ * n⁻¹) hgP
      have hfin := Subgroup.mem_map_of_mem π hgQ
      have heq : π ((g₀ * n⁻¹)⁻¹ * y * (g₀ * n⁻¹)) = (π g₀)⁻¹ * π y * π g₀ := by
        have hπn : π n = 1 := hπO n hnO
        simp [map_mul, map_inv, hπn]
      rw [heq] at hfin
      exact hfin
  have hbar_sup : A.map π ⊔ B.map π = P.map π := by
    rw [← Subgroup.map_sup, hsup]
  have hbar_inf : A.map π ⊓ B.map π = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro z ⟨hz1, hz2⟩
    obtain ⟨a, ha1, rfl⟩ := Subgroup.mem_map.1 hz1
    obtain ⟨b, hb2, hab⟩ := Subgroup.mem_map.1 hz2
    have hab' : a⁻¹ * b ∈ O := (hmk a b).1 hab.symm
    have hab2 : a⁻¹ * b ∈ P ⊓ O :=
      ⟨P.mul_mem (P.inv_mem (hAP ha1)) (hBP hb2), hab'⟩
    rw [hPO, Subgroup.mem_bot, inv_mul_eq_one] at hab2
    have haI : a ∈ A ⊓ B := ⟨ha1, by rw [hab2]; exact hb2⟩
    rw [hAB, Subgroup.mem_bot] at haI
    rw [haI, map_one]
  have hfinal := ff84_2_3_reduced_of hKF1 hKS (X ⧸ O) hK' hbot (P.map π) (A.map π) (B.map π)
    hPbarSyl hPbar9 hP1bar hP2bar hbar_sup hbar_inf (hsc A hscA) (hsc B hscB)
  exact hfinal

end CFSG.RankThree.PartTwo.Sec21.FF84
