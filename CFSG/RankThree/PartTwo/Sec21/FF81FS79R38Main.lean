module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38Q

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)

namespace R38K

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}
variable {S : Std b t b₁ b₂ J} {A₁ : Subgroup J6.S6} {c₀ : J6.S6} {J₁ : Subgroup J6.S6}

theorem Zsub_two_mem_Asub (Fr : Frame A₁ c₀ J₁) {x : H} (hx : x ∈ Zsub S A₁) {k : ℕ}
    (hk : x ^ (2 ^ k) = 1) : x ∈ Asub S A₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o, ho, a, ha, rfl⟩ := mem_Zsub_iff.mp hx
  have hcomm : Commute o a := mem_C1_iff.mp (L14.Opp_le 2 _ ho) a ha
  have ha2 : a ^ (2 ^ (k + 1)) = 1 := by
    have : a ^ 2 = 1 := by rw [pow_two]; exact Asub_sq (S := S) Fr a ha
    rw [pow_succ', pow_mul, this, one_pow]
  have hk' : (o * a) ^ (2 ^ (k + 1)) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
  rw [hcomm.mul_pow, ha2, mul_one] at hk'
  have : o = 1 := eq_one_of_pow_prime_pow (L14.Opp_coprime 2 _) ho hk'
  rw [this, one_mul]
  exact ha

theorem case_false (hR1K : KF_FS79Prop2OneK) (hK : KCore.KGroupNonab InCatalog H)
    (Fr : Frame A₁ c₀ J₁) (hcop : Nat.Coprime 3 (Nat.card (O1 S A₁))) (hbO : b ∉ O1 S A₁)
    (hC₁ : CtlEq b (S.ι c₀)) (hC₂ : CtlEq b (b * S.ι c₀)) (hC₃ : CtlEq b (b * (S.ι c₀)⁻¹))
    (hO₁ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (S.ι c₀))))))
    (hO₂ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * S.ι c₀))))))
    (hO₃ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * (S.ι c₀)⁻¹)))))) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  have D := qdata (S := S) Fr hcop hC₁ hC₂ hC₃ hO₁ hO₂ hO₃
  haveI hN : ((Zsub S A₁).subgroupOf (Nor (Asub S A₁))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using D.Z_norm (g : H) g.2 (n : H) hn⟩
  obtain ⟨O, hZO, hOΓ, hOn, hO6, hdec⟩ := D.conclusionP
    (fun G _ _ => KCore.KGroupNonab InCatalog G) (fun G _ _ hG => hR1K G hG)
    (kGroupNonab_quotient hK _ _)
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hbΓ : b ∈ Nor (Asub S A₁) := b_mem_Nor Fr
  have hbO' : b ∈ Nor O := Subgroup.mem_normalizer_fintype fun o ho => hOn b hbΓ o ho
  set U : Subgroup H := O ⊔ Subgroup.zpowers b with hU
  have hOU : O ≤ U := le_sup_left
  have hbU : b ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hZU : Zsub S A₁ ≤ U := hZO.trans hOU
  have hUn : ∀ g ∈ Nor (Asub S A₁), ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    obtain ⟨o, ho, n, hn, rfl⟩ := hdec g hg
    obtain ⟨o', ho', i, rfl⟩ := mem_sup_zpowers_of_mem_nor hbO' hu
    have e : (o * n) * (o' * b ^ i) * (o * n)⁻¹ =
        o * ((n * o' * n⁻¹) * (n * b ^ i * n⁻¹)) * o⁻¹ := by group
    rw [e]
    have h1 : n * o' * n⁻¹ ∈ U := hOU (hOn n hn.1 o' ho')
    have h2 : n * b ^ i * n⁻¹ ∈ Subgroup.zpowers b ⊔ Zsub S A₁ :=
      (Subgroup.mem_normalizer_iff.mp hn.2 (b ^ i)).mp
        (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i))
    have h2' : n * b ^ i * n⁻¹ ∈ U := (sup_le (le_sup_right) hZU) h2
    exact U.mul_mem (U.mul_mem (hOU ho) (U.mul_mem h1 h2')) (U.inv_mem (hOU ho))
  set V : Subgroup H := U ⊓ C1 S A₁ with hV
  have hVn : ∀ g ∈ Nor (Asub S A₁), ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
    ⟨hUn g hg v hv.1, Nor_conj_C1 hg hv.2⟩
  have hAZ : Asub S A₁ ≤ Zsub S A₁ := Asub_le_Zsub
  have hAV : Asub S A₁ ≤ V := fun a ha => ⟨hZU (hAZ ha), Asub_le_C1 Fr ha⟩
  have hbV : b ∈ V := ⟨hbU, b_mem_C1⟩
  have hV2 : ∀ x ∈ V, ∀ k : ℕ, x ^ (2 ^ k) = 1 → x ∈ Asub S A₁ := by
    intro x hx k hk
    have hxU := hx.1
    obtain ⟨o', ho', i, hxeq⟩ := mem_sup_zpowers_of_mem_nor hbO' hxU
    have hβ : b ^ i ∈ Nor (Asub S A₁) := (Nor _).zpow_mem hbΓ i
    have hx3O : x ^ 3 ∈ O := by
      have hβ3 : (b ^ i) ^ 3 = 1 :=
        pow_three_of_mem_zpowers hb3 (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i)
      have h1 : (b ^ i) * o' * (b ^ i)⁻¹ ∈ O := hOn _ hβ o' ho'
      have h2 : (b ^ i) * ((b ^ i) * o' * (b ^ i)⁻¹) * (b ^ i)⁻¹ ∈ O := hOn _ hβ _ h1
      have e : x ^ 3 = o' * ((b ^ i) * o' * (b ^ i)⁻¹) *
          ((b ^ i) * ((b ^ i) * o' * (b ^ i)⁻¹) * (b ^ i)⁻¹) * (b ^ i) ^ 3 := by
        rw [hxeq, pow_three', pow_three']
        group
      rw [e, hβ3, mul_one]
      exact O.mul_mem (O.mul_mem ho' h1) h2
    obtain ⟨m, hm6, hmZ⟩ := hO6 _ hx3O
    have hm2 : Nat.Coprime m 2 := (Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 6) hm6).symm
    have hx3Z : x ^ 3 ∈ Zsub S A₁ := by
      have hord : orderOf (x ^ 3) ∣ 2 ^ k := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
      obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime
        (Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right k hm2))
      rw [← hm']
      exact (Zsub S A₁).pow_mem hmZ m'
    have hxZ : x ∈ Zsub S A₁ := by
      have hord : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime (n := 3)
        (Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right k (by norm_num)))
      rw [← hm']
      exact (Zsub S A₁).pow_mem hx3Z m'
    exact Zsub_two_mem_Asub Fr hxZ hk
  have hZc : ∀ v ∈ V, ∀ a ∈ Asub S A₁, v * a = a * v := fun v hv a ha => mem_C1_iff.mp hv.2 a ha
  have hcop' : ∀ v ∈ V, ∃ m : ℕ, Nat.Coprime 2 m ∧ v ^ m ∈ Asub S A₁ := by
    intro v hv
    obtain ⟨k, m, hm, hmk⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf v)
      (orderOf_pos v).ne'
    refine ⟨m, Nat.coprime_two_left.mpr hm, hV2 (v ^ m) (V.pow_mem hv m) k ?_⟩
    rw [← pow_mul, mul_comm, ← hmk]
    exact pow_orderOf_eq_one v
  obtain ⟨W, hWV, hWA, hWdec, hWc⟩ := exists_central_complement_p (p := 2) hAV hZc
    (isPGroup_Asub Fr) hcop'
  have hWb : b ∈ W := mem_complement_of_coprime_orderOf_p hZc (isPGroup_Asub Fr) hWV hWdec hWc hbV
    (by rw [h.ord_b]; norm_num)
  have hWO : W ≤ O1 S A₁ := by
    refine L14.le_Opp_of_normalized (hWV.trans inf_le_right) ?_ hWc
    intro g hg x hx
    exact conj_mem_complement_p hZc (isPGroup_Asub Fr) hWV hWdec hWc hx
      (hVn g (C1_le_Nor hg) x (hWV hx))
  exact hbO (hWO hWb)

theorem frame_r38 (hR1K : KF_FS79Prop2OneK) (hK : KCore.KGroupNonab InCatalog H)
    (S : Std b t b₁ b₂ J) {A₁ : Subgroup J6.S6} {c₀ : J6.S6} {J₁ : Subgroup J6.S6}
    (Fr : Frame A₁ c₀ J₁)
    (hC₁ : CtlEq b (S.ι c₀)) (hC₂ : CtlEq b (b * S.ι c₀)) (hC₃ : CtlEq b (b * (S.ι c₀)⁻¹))
    (hO₁ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (S.ι c₀))))))
    (hO₂ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * S.ι c₀))))))
    (hO₃ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * (S.ι c₀)⁻¹)))))) :
    R38Stmt b (A₁.map S.ι) := by
  by_cases hb : b ∈ O1 S A₁
  · exact r38_of_b_mem_O1 S Fr hb
  · rcases b_mem_O1_or_coprime S Fr with hb' | hcop
    · exact absurd hb' hb
    · exact (case_false hR1K hK Fr hcop hb hC₁ hC₂ hC₃ hO₁ hO₂ hO₃).elim

end R38K

end CFSG.RankThree.PartTwo.Sec21.FF81
