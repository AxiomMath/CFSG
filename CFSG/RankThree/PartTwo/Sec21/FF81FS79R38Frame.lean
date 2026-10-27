module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38Fin
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38E9

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

namespace R38K

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

section Basic

variable (S : Std b t b₁ b₂ J) (A₁ : Subgroup J6.S6)

noncomputable abbrev Asub : Subgroup H := A₁.map S.ι

noncomputable abbrev C1 : Subgroup H := CenS (Asub S A₁)

noncomputable abbrev O1 : Subgroup H := Opp 2 (C1 S A₁)

variable {S A₁}

theorem Asub_le_J : Asub S A₁ ≤ J := by
  rintro _ ⟨s, -, rfl⟩
  exact S.ι_mem s

theorem ι_mem_Asub {s : J6.S6} (hs : s ∈ A₁) : S.ι s ∈ Asub S A₁ := ⟨s, hs, rfl⟩

theorem Asub_sq {c₀ : J6.S6} {J₁ : Subgroup J6.S6} (Fr : Frame A₁ c₀ J₁) :
    ∀ a ∈ Asub S A₁, a * a = 1 := by
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_mul, Fr.sq s hs, map_one]

theorem Asub_comm {c₀ : J6.S6} {J₁ : Subgroup J6.S6} (Fr : Frame A₁ c₀ J₁) :
    ∀ a ∈ Asub S A₁, ∀ a' ∈ Asub S A₁, a * a' = a' * a := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
  rw [← map_mul, ← map_mul, Fr.comm s hs s' hs']

theorem Asub_le_C1 {c₀ : J6.S6} {J₁ : Subgroup J6.S6} (Fr : Frame A₁ c₀ J₁) :
    Asub S A₁ ≤ C1 S A₁ := fun a ha =>
  Subgroup.mem_centralizer_iff.mpr fun a' ha' => (Asub_comm Fr a' ha' a ha)

theorem mem_C1_iff {x : H} : x ∈ C1 S A₁ ↔ ∀ a ∈ Asub S A₁, x * a = a * x := by
  constructor
  · intro hx a ha
    exact (Subgroup.mem_centralizer_iff.mp hx a ha).symm
  · intro h
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => (h a ha).symm

theorem C1_le_Nor : C1 S A₁ ≤ Nor (Asub S A₁) := fun x hx =>
  mem_Nor_of_comm_all fun a ha => mem_C1_iff.mp hx a ha

theorem C1_inf_J {c₀ : J6.S6} {J₁ : Subgroup J6.S6} (Fr : Frame A₁ c₀ J₁) {x : H} (hxJ : x ∈ J)
    (hx : x ∈ C1 S A₁) : x ∈ Asub S A₁ := by
  obtain ⟨σ, rfl⟩ := S.exists_ι hxJ
  refine ⟨σ, Fr.cen σ fun s hs => ?_, rfl⟩
  apply S.ι_injective
  rw [map_mul, map_mul]
  exact mem_C1_iff.mp hx _ (ι_mem_Asub hs)

theorem b_mem_C1 : b ∈ C1 S A₁ := by
  rw [mem_C1_iff]
  rintro _ ⟨s, -, rfl⟩
  exact (S.ι_comm_b s).symm

theorem t_mem_C1 : t ∈ C1 S A₁ := by
  rw [mem_C1_iff]
  rintro _ ⟨s, -, rfl⟩
  exact (S.ι_comm_t s).symm

theorem K_le_C1 : Opp 3 (Nor (Subgroup.zpowers b)) ≤ C1 S A₁ := by
  intro k hk
  rw [mem_C1_iff]
  rintro _ ⟨s, -, rfl⟩
  exact S.hyp.K_comm_J hk (S.ι_mem s)

theorem Nor_conj_C1 {g x : H} (hg : g ∈ Nor (Asub S A₁)) (hx : x ∈ C1 S A₁) :
    g * x * g⁻¹ ∈ C1 S A₁ := by
  rw [mem_C1_iff]
  intro a ha
  have h1 : g⁻¹ * a * g⁻¹⁻¹ ∈ Asub S A₁ :=
    (Subgroup.mem_normalizer_iff.mp ((Nor _).inv_mem hg) a).mp ha
  have h2 := mem_C1_iff.mp hx _ h1
  calc g * x * g⁻¹ * a = g * (x * (g⁻¹ * a * g⁻¹⁻¹)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * a * g⁻¹⁻¹) * x) * g⁻¹ := by rw [h2]
    _ = a * (g * x * g⁻¹) := by group

theorem O1_le_Opp_Nor : O1 S A₁ ≤ Opp 2 (Nor (Asub S A₁)) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  L14.Opp_le_Opp_of_normalized C1_le_Nor (fun _ hg _ hc => Nor_conj_C1 hg hc)

theorem Nor_conj_O1 {g o : H} (hg : g ∈ Nor (Asub S A₁)) (ho : o ∈ O1 S A₁) :
    g * o * g⁻¹ ∈ O1 S A₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : g * o * g⁻¹ ∈ Opp 2 (Nor (Asub S A₁)) := L14.Opp_conj_mem hg (O1_le_Opp_Nor ho)
  have h2 : g * o * g⁻¹ ∈ C1 S A₁ := Nor_conj_C1 hg (L14.Opp_le 2 _ ho)
  have hle : Opp 2 (Nor (Asub S A₁)) ⊓ C1 S A₁ ≤ O1 S A₁ := by
    refine L14.le_Opp_of_normalized inf_le_right ?_ ?_
    · intro g' hg' x hx
      exact ⟨L14.Opp_conj_mem (C1_le_Nor hg') hx.1,
        (C1 S A₁).mul_mem ((C1 S A₁).mul_mem hg' hx.2) ((C1 S A₁).inv_mem hg')⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (L14.Opp_coprime 2 _)
  exact hle ⟨h1, h2⟩

end Basic

section Part1

variable (S : Std b t b₁ b₂ J) {A₁ : Subgroup J6.S6} {c₀ : J6.S6} {J₁ : Subgroup J6.S6}

theorem cen_decomp (h : FS79Hyp b t b₁ b₂ J) {p : H} (hp : p ∈ Cen b) :
    ∃ k ∈ Opp 3 (Nor (Subgroup.zpowers b)), ∃ i : ℤ, ∃ j ∈ J, p = k * b ^ i * j := by
  have hpN : p ∈ Nor (Subgroup.zpowers b) := fs79_cen_le_nor_zpowers b hp
  obtain ⟨k, hk, y, hy, j, hj, hpkyj⟩ := h.nor_decomp hpN
  have hpb : p * b = b * p := Subgroup.mem_centralizer_singleton_iff.mp hp
  have hkb : k * b = b * k := Ctl34.K_comm_b h hk
  have hjb : j * b = b * j := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj)
  have hyb : y * b = b * y := by
    rw [hpkyj] at hpb
    have e : k * (y * b) * j = k * (b * y) * j := by
      calc k * (y * b) * j = k * y * (b * j) := by group
        _ = k * y * (j * b) := by rw [hjb]
        _ = k * y * j * b := by group
        _ = b * (k * y * j) := hpb
        _ = (b * k) * y * j := by group
        _ = (k * b) * y * j := by rw [hkb]
        _ = k * (b * y) * j := by group
    exact mul_right_cancel (mul_left_cancel (a := k) (by simpa [mul_assoc] using e))
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (h.mem_zpowers_of_comm hy hyb)
  exact ⟨k, hk, i, j, hj, hpkyj⟩

theorem pgroup_eq_zpowers (Fr : Frame A₁ c₀ J₁) {P : Subgroup H} (hP : IsPGroup 3 P)
    (hbP : b ∈ P) (hPC : P ≤ C1 S A₁) : P = Subgroup.zpowers b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  apply le_antisymm
  · intro x hx
    have hxcen : x ∈ Cen b := h.pgroup_le_cen hP hbP hx
    obtain ⟨κ, hκ, i, j, hj, rfl⟩ := cen_decomp h hxcen
    have hκC : κ ∈ C1 S A₁ := K_le_C1 hκ
    have hbiC : b ^ i ∈ C1 S A₁ := (C1 S A₁).zpow_mem b_mem_C1 i
    have hjC : j ∈ C1 S A₁ := by
      have h1 : (κ * b ^ i)⁻¹ * (κ * b ^ i * j) ∈ C1 S A₁ :=
        (C1 S A₁).mul_mem ((C1 S A₁).inv_mem ((C1 S A₁).mul_mem hκC hbiC)) (hPC hx)
      simpa [mul_assoc] using h1
    have hjA : j ∈ Asub S A₁ := C1_inf_J Fr hj hjC
    have hj2 : j * j = 1 := Asub_sq Fr j hjA
    obtain ⟨m, hm⟩ := hP ⟨_, hx⟩
    have hm' : (κ * b ^ i * j) ^ (3 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    have hxN : (κ * b ^ i * j) ^ (3 ^ (m + 1)) = 1 := by
      rw [pow_succ, pow_mul, hm', one_pow]
    have hκb : κ * b = b * κ := Ctl34.K_comm_b h hκ
    have hκbi : Commute κ (b ^ i) := (Commute.zpow_right (show Commute κ b from hκb) i)
    have hκj : Commute κ j := S.hyp.K_comm_J hκ hj
    have hbij : Commute (b ^ i) j := by
      have : j * b = b * j := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj)
      exact (Commute.zpow_left (show Commute b j from this.symm) i)
    have hc1 : Commute (κ * b ^ i) j := hκj.mul_left hbij
    have hpow : (κ * b ^ i * j) ^ (3 ^ (m + 1)) =
        κ ^ (3 ^ (m + 1)) * (b ^ i) ^ (3 ^ (m + 1)) * j ^ (3 ^ (m + 1)) := by
      rw [hc1.mul_pow, hκbi.mul_pow]
    have hbiN : (b ^ i) ^ (3 ^ (m + 1)) = 1 := by
      have h3 : (b ^ i) ^ 3 = 1 :=
        pow_three_of_mem_zpowers hb3 (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i)
      rw [pow_succ', pow_mul, h3, one_pow]
    have hjN : j ^ (3 ^ (m + 1)) = j := by
      obtain ⟨q, hq⟩ : Odd (3 ^ (m + 1)) := Odd.pow (by decide)
      have hj2' : j ^ 2 = 1 := by rw [pow_two]; exact hj2
      rw [hq, pow_succ, pow_mul, hj2', one_pow, one_mul]
    rw [hpow, hbiN, hjN, mul_one] at hxN
    have hκN : κ ^ (3 ^ (m + 1)) = j⁻¹ := eq_inv_of_mul_eq_one_left hxN
    have hj1 : j = 1 := by
      have h1 : j⁻¹ = 1 := h.eq_one_of_comm_J (J.inv_mem hj) (fun j' hj' => by
        rw [← hκN]
        exact ((show Commute κ j' from S.hyp.K_comm_J hκ hj').pow_left _).eq)
      simpa using h1
    have hκ1 : κ = 1 := by
      refine eq_one_of_pow_three_pow (L14.Opp_coprime 3 _) hκ (m := m + 1) ?_
      rw [hκN, hj1, inv_one]
    rw [hκ1, hj1, one_mul, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i
  · exact Subgroup.zpowers_le.mpr hbP

theorem isSylowOf_b (Fr : Frame A₁ c₀ J₁) : IsSylowOf 3 (Subgroup.zpowers b) (C1 S A₁) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  have hbC : Subgroup.zpowers b ≤ C1 S A₁ := Subgroup.zpowers_le.mpr b_mem_C1
  have hcardb : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, h.ord_b]
  have hb3g : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [hcardb]; simp)
  have hA : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf (C1 S A₁)) :=
    hb3g.of_equiv (Subgroup.subgroupOfEquivOfLe hbC).symm
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  set S₀ : Subgroup H := (P : Subgroup ↥(C1 S A₁)).map (C1 S A₁).subtype with hS₀
  have hS₀3 : IsPGroup 3 S₀ := P.isPGroup'.map (C1 S A₁).subtype
  have hS₀C : S₀ ≤ C1 S A₁ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hbS₀ : b ∈ S₀ := ⟨⟨b, b_mem_C1⟩,
    hAP (show (⟨b, b_mem_C1⟩ : ↥(C1 S A₁)) ∈ (Subgroup.zpowers b).subgroupOf (C1 S A₁) from
      Subgroup.mem_zpowers b), rfl⟩
  have hSeq : S₀ = Subgroup.zpowers b := pgroup_eq_zpowers S Fr hS₀3 hbS₀ hS₀C
  refine ⟨hbC, hb3g, ?_⟩
  have hrel : (Subgroup.zpowers b).relIndex (C1 S A₁) = (P : Subgroup ↥(C1 S A₁)).index := by
    rw [← hSeq, hS₀, Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (C1 S A₁).subtype_injective]
  rw [hrel]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr P.not_dvd_index

theorem isSylowOf_of_le {P K H' : Subgroup H} (hP : IsSylowOf 3 P H') (hPK : P ≤ K)
    (hKH : K ≤ H') : IsSylowOf 3 P K := by
  refine ⟨hPK, hP.2.1, ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P K H' hPK hKH
  exact Nat.Coprime.coprime_dvd_right (Dvd.intro _ h1) hP.2.2

theorem b_mem_O1_or_coprime (Fr : Frame A₁ c₀ J₁) :
    b ∈ O1 S A₁ ∨ Nat.Coprime 3 (Nat.card (O1 S A₁)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hc : Nat.Coprime 3 (Nat.card (O1 S A₁))
  · exact Or.inr hc
  left
  have h := S.hyp
  have hd : 3 ∣ Nat.card (O1 S A₁) := by
    by_contra hnd
    exact hc ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(O1 S A₁)) 3 hd
  have hxo : orderOf (x : H) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hx3 : (x : H) ^ 3 = 1 := by
    rw [← hxo]
    exact pow_orderOf_eq_one _
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := by
    intro h1
    have := h.ord_b
    rw [h1, orderOf_one] at this
    omega
  have hxC : (x : H) ∈ C1 S A₁ := L14.Opp_le 2 _ x.2
  obtain ⟨k, hkC, hk⟩ := L14.exists_conj_le_sylowOf (isSylowOf_b S Fr)
    (Subgroup.zpowers_le.mpr hxC) (isPGroup_zpowers_of_pow_three hx3)
  have hkx : k * (x : H) * k⁻¹ ∈ Subgroup.zpowers b := hk x (Subgroup.mem_zpowers _)
  have hkxO : k * (x : H) * k⁻¹ ∈ O1 S A₁ := L14.Opp_conj_mem hkC x.2
  have hne : k * (x : H) * k⁻¹ ≠ 1 := by
    intro h1
    have : (x : H) = 1 := by
      calc (x : H) = k⁻¹ * (k * (x : H) * k⁻¹) * k := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hxo
    omega
  rcases eq_or_inv_of_mem_zpowers_of_pow_three hb3 hb1 hkx hne with h1 | h1
  · have h2 := hkxO
    rw [h1] at h2
    exact h2
  · have h2 : (k * (x : H) * k⁻¹)⁻¹ ∈ O1 S A₁ := (O1 S A₁).inv_mem hkxO
    rw [h1, inv_inv] at h2
    exact h2

theorem r38_of_b_mem_O1 (Fr : Frame A₁ c₀ J₁) (hb : b ∈ O1 S A₁) :
    R38Stmt b (Asub S A₁) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := S.hyp
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hsylO : IsSylowOf 3 (Subgroup.zpowers b) (O1 S A₁) :=
    isSylowOf_of_le (isSylowOf_b S Fr) (Subgroup.zpowers_le.mpr hb) (L14.Opp_le 2 _)
  unfold R38Stmt
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨o, ho, m, hm, rfl⟩
    exact (Nor _).mul_mem (L14.Opp_le 2 _ ho) hm.2
  · intro g hg
    have hgb : g * b * g⁻¹ ∈ O1 S A₁ := Nor_conj_O1 hg hb
    have hp3 : IsPGroup 3 (Subgroup.zpowers (g * b * g⁻¹)) := by
      refine isPGroup_zpowers_of_pow_three ?_
      calc (g * b * g⁻¹) ^ 3 = g * b ^ 3 * g⁻¹ := by rw [conj_pow]
        _ = 1 := by rw [hb3]; group
    obtain ⟨k, hkO, hk⟩ := L14.exists_conj_le_sylowOf hsylO
      (Subgroup.zpowers_le.mpr hgb) hp3
    have hkgb : k * (g * b * g⁻¹) * k⁻¹ ∈ Subgroup.zpowers b := hk _ (Subgroup.mem_zpowers _)
    have hkgN : k * g ∈ Nor (Subgroup.zpowers b) :=
      mem_Nor_zpowers_of_conj (by simpa [mul_assoc] using hkgb)
    have hkA : k ∈ Nor (Asub S A₁) := C1_le_Nor (L14.Opp_le 2 _ hkO)
    exact ⟨k⁻¹, O1_le_Opp_Nor ((O1 S A₁).inv_mem hkO), k * g,
      ⟨hkgN, (Nor _).mul_mem hkA hg⟩, by group⟩

end Part1

end R38K

end CFSG.RankThree.PartTwo.Sec21.FF81
