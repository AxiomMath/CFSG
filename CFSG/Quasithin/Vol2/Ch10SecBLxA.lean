module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkG

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.BLx

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_blockQ_of_sq_mem (hAS : Ch11.SecH.AS_I_1_3_L2) {Y : Subgroup G} (hperf : ⁅Y, Y⁆ = Y)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ 2)
    (α : ↥Y →* Matrix.SpecialLinearGroup (Fin 2) F) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥Y) (hcard : Nat.card (blockQ Y) = 2 * Nat.card (blockU Y))
    {y : G} (hy : y ∈ Y) (hy2 : y ^ 2 ∈ blockU Y) : y ∈ blockQ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUQ : blockU Y ≤ blockQ Y :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (C1.le_normalizer_blockQ Y)
  have hUX : blockU Y ≤ Y := hUQ.trans (C1.blockQ_le Y)
  set N := (blockU Y).subgroupOf Y
  have hNn : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUX).mpr (C1.le_normalizer_blockU Y)
  set Q := CFSG.pCore 2 ↥Y
  have hNQ : N ≤ Q := fun x hx => (mem_blockQ_iff x).mp (hUQ hx)
  set Zq := Q.map (QuotientGroup.mk' N)
  have hZn : Zq.Normal := (CFSG.pCore_normal (p := 2) (G := ↥Y)).map _
    (QuotientGroup.mk'_surjective N)
  have hZc : Zq ≤ Subgroup.center (↥Y ⧸ N) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    change ((y : G) * q)⁻¹ * (q * y) ∈ blockU Y
    have e : ((y : G) * q)⁻¹ * (q * y) = ⁅(q : G)⁻¹, (y : G)⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator (inv_mem ((mem_blockQ_iff q).mpr hq)) (inv_mem y.2)
  have e : (↥Y ⧸ N) ⧸ Zq ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientQuotientEquivQuotient N Q hNQ).trans
      ((QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hαs))
  have hperf' : Group.IsPerfect (↥Y ⧸ N) := by
    have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
    infer_instance
  rcases hAS 2 le_rfl F (by rw [Nat.card_eq_fintype_card, hF]) (↥Y ⧸ N) hperf' Zq hZc ⟨e⟩ with
    h0 | ⟨-, -, hinv⟩
  · exfalso
    have hQN : Q ≤ N := by
      intro q hq
      have : QuotientGroup.mk' N q ∈ Zq := ⟨q, hq, rfl⟩
      rwa [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hle : blockQ Y ≤ blockU Y := fun x hx =>
      hQN ((mem_blockQ_iff ⟨x, C1.blockQ_le Y hx⟩).mp hx)
    have h1 := Subgroup.card_le_of_le hle
    have h2 : 0 < Nat.card (blockU Y) := Nat.card_pos
    omega
  · have h2 : (QuotientGroup.mk' N ⟨y, hy⟩) ^ 2 = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hy2
    obtain ⟨q, hq, hqa⟩ := hinv _ h2
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hqa
    have h := Q.mul_mem hq (hNQ hqa)
    rw [mul_inv_cancel_left] at h
    exact (mem_blockQ_iff ⟨y, hy⟩).mpr h

variable {T S X Y V : Subgroup G} {b : G}

theorem card_blockQ_of_shape (m : Mem T S X Y V b 2) (hU : blockU Y ≤ V)
    (hcard : Nat.card (blockQ Y) = 2 * Nat.card (blockU Y)) :
    blockU Y = V ∧ Nat.card V = 16 ∧ Nat.card (blockQ Y) = 32 := by
  have hUV := (block_of_natData m.hn m.perf m.char m.nat hU).2.2.2
  have hV : Nat.card V = 16 := by rw [m.nat.card]; norm_num
  exact ⟨hUV, hV, by rw [hcard, hUV, hV]⟩

theorem mem_blockQ_of_sq_eq_one (hAS : Ch11.SecH.AS_I_1_3_L2) (m : Mem T S X Y V b 2)
    (hcard : Nat.card (blockQ Y) = 2 * Nat.card (blockU Y)) {y : G} (hy : y ∈ Y)
    (hy2 : y ^ 2 = 1) : y ∈ blockQ Y := by
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := m.nat.nat
  exact mem_blockQ_of_sq_mem hAS m.perf hF α hαs hαk hcard hy (by rw [hy2]; exact one_mem _)

theorem commutator_inf_eq (hAS : Ch11.SecH.AS_I_1_3_L2) (m : Mem T S X Y V b 2)
    (hU : blockU Y ≤ V) (hcard : Nat.card (blockQ Y) = 2 * Nat.card (blockU Y)) :
    ⁅S ⊓ Y, Subgroup.zpowers b⁆ = S ⊓ Y ∧ Nat.card ↥(S ⊓ Y) = 2 ^ 7 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUV, hV, hQ⟩ := card_blockQ_of_shape m hU hcard
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := m.nat.nat
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hsq := sq_ne_one m.hn α hαk m.bY m.bo
  set P := S ⊓ Y
  have hP2 : IsPGroup 2 P := m.T2.to_le (inf_le_left.trans m.ST)
  have hbP : b ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨m.bS, Subgroup.le_normalizer m.bY⟩
  set C := ⁅P, Subgroup.zpowers b⁆
  have hCP : C ≤ P := commutator_zpowers_le hbP
  have hCY : C ≤ Y := hCP.trans inf_le_right
  have hQP : blockQ Y ≤ P := EscapingLocal.pCoreOf_le_of_isSylowTwoOf m.syl
  have hαP := card_map_sylow (by norm_num) hF α hαs m.syl
  have hαC : (C.subgroupOf Y).map α = (P.subgroupOf Y).map α :=
    le_antisymm (Subgroup.map_mono fun _ hx =>
      Subgroup.mem_subgroupOf.mpr (hCP (Subgroup.mem_subgroupOf.mp hx)))
      (map_le_map_commutator α m.bY hsq hP2 hbP)
  have hVC : V ≤ C := le_commutator_of_fix (m.nat.le.trans hQP) (m.nat.norm m.bY)
    fun x hx hxb => m.nat.eq_one_of_fix m.bY m.b_odd.2 m.b_odd.1 hx
      (by rw [← hxb, mul_inv_cancel_right])
  have hCQ : C ⊓ blockQ Y = blockQ Y := by
    by_contra hne
    have hVle : V ≤ C ⊓ blockQ Y := le_inf hVC m.nat.le
    have hd1 : Nat.card V ∣ Nat.card ↥(C ⊓ blockQ Y) := Subgroup.card_dvd_of_le hVle
    have hd2 : Nat.card ↥(C ⊓ blockQ Y) ∣ Nat.card (blockQ Y) :=
      Subgroup.card_dvd_of_le inf_le_right
    have hne' : Nat.card ↥(C ⊓ blockQ Y) ≠ Nat.card (blockQ Y) := fun h =>
      hne (Subgroup.eq_of_le_of_card_ge inf_le_right h.ge)
    have hpos : 0 < Nat.card ↥(C ⊓ blockQ Y) := Nat.card_pos
    have hle32 := Nat.le_of_dvd (by rw [hQ]; norm_num) hd2
    rw [hV] at hd1
    rw [hQ] at hle32 hne'
    have h16 : Nat.card ↥(C ⊓ blockQ Y) = 16 := by omega
    have hCQV : C ⊓ blockQ Y = V := (Subgroup.eq_of_le_of_card_ge hVle (by rw [h16, hV])).symm
    have hne1 : (C.subgroupOf Y).map α ≠ ⊥ := by
      intro h
      rw [hαC] at h
      rw [h, Subgroup.card_bot] at hαP
      norm_num at hαP
    obtain ⟨⟨_, y, hyC, rfl⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne1
    have hαy : α y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hcC : (y : G) ∈ C := Subgroup.mem_subgroupOf.mp hyC
    have hcQ : (y : G) ∉ blockQ Y := fun h =>
      hαy ((MonoidHom.mem_ker).mp (hαk ▸ (mem_blockQ_iff y).mp h))
    obtain ⟨j, hj⟩ := hP2 ⟨(y : G), hCP hcC⟩
    have hj' : (y : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hex : ∃ i, (y : G) ^ 2 ^ i ∈ V := ⟨j, by rw [hj']; exact V.one_mem⟩
    have hspec : (y : G) ^ 2 ^ Nat.find hex ∈ V := Nat.find_spec hex
    have hi₀ : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0, pow_zero, pow_one] at hspec
      exact hcQ (m.nat.le hspec)
    have hmin : (y : G) ^ 2 ^ (Nat.find hex - 1) ∉ V := Nat.find_min hex (by omega)
    have hd2 : ((y : G) ^ 2 ^ (Nat.find hex - 1)) ^ 2 ∈ blockU Y := by
      rw [hUV, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi₀)]
      exact hspec
    have hdQ := mem_blockQ_of_sq_mem hAS m.perf hF α hαs hαk hcard (Y.pow_mem y.2 _) hd2
    have hdm : (y : G) ^ 2 ^ (Nat.find hex - 1) ∈ C ⊓ blockQ Y := ⟨C.pow_mem hcC _, hdQ⟩
    rw [hCQV] at hdm
    exact hmin hdm
  have hCcard : Nat.card C = 2 ^ 7 := by
    rw [card_eq_mul α hαk hCY, hαC, hαP, hCQ, hQ]; norm_num
  have hPcard : Nat.card P = 2 ^ 7 := by
    rw [card_eq_mul α hαk inf_le_right, hαP, inf_eq_right.mpr hQP, hQ]; norm_num
  exact ⟨Subgroup.eq_of_le_of_card_ge hCP (by rw [hCcard, hPcard]), hPcard⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.BLx
