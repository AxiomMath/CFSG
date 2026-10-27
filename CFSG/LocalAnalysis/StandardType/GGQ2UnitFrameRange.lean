module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitDiag

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom det_diagHom)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem not_three_dvd_card_center {G : Type*} [Group G] {H : Subgroup G}
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) :
    ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥H) := by
  have hle : (Subgroup.center ↥H).map H.subtype ≤ Subgroup.centralizer (H : Set G) := by
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨c, hc, rfl⟩ := hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h2 := congrArg H.subtype (Subgroup.mem_center_iff.mp hc (⟨h, hh⟩ : ↥H))
    simpa only [map_mul, Subgroup.subtype_apply] using h2
  have hdvd : Nat.card ↥(Subgroup.center ↥H) ∣
      Nat.card ↥(Subgroup.centralizer (H : Set G)) := by
    rw [← Subgroup.card_map_of_injective (f := H.subtype) H.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  exact fun h => hC3 (h.trans hdvd)

private lemma ufr_center_pow_three_eq_one {G : Type*} [Group G] {H : Subgroup G}
    {z : ↥H} (hz : z ∈ Subgroup.center ↥H) (hz3 : z ^ 3 = 1)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) : z = 1 := by
  have h3 : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥H) := not_three_dvd_card_center hC3
  have hord3 : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz3
  have hord : orderOf z ∣ Nat.card ↥(Subgroup.center ↥H) :=
    Subgroup.orderOf_dvd_natCard _ hz
  have hone : orderOf z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord3 with h | h
    · exact h
    · exact absurd (h ▸ hord) h3
  exact orderOf_eq_one_iff.mp hone

private lemma ufr_sum_add_const {N : ℕ} (u : UnitRaw.W N) (c : UnitRaw.F) :
    ∑ i, (u i + c) = ∑ i, u i + (N : UnitRaw.F) * c := by
  simp [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private lemma ufr_mem_heart_iff {N : ℕ} (u : UnitRaw.W N) :
    (UnitRaw.oneLine N).mkQ u ∈ UnitRaw.heart N ↔
      ∃ c : UnitRaw.F, ∑ i, u i + (N : UnitRaw.F) * c = 0 := by
  rw [UnitRaw.heart, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwq⟩
    rw [LinearMap.mem_ker, UnitRaw.sumFun_apply] at hw
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hwq
    obtain ⟨c, hc⟩ := (UnitRaw.mem_oneLine (w - u)).mp hwq
    refine ⟨c, ?_⟩
    have hw' : w = u + fun _ : Fin N => c := by
      rw [← sub_add_cancel w u, hc, add_comm]
    have hsum : ∑ i, (u + fun _ : Fin N => c) i = ∑ i, u i + (N : UnitRaw.F) * c := by
      simpa only [Pi.add_apply] using ufr_sum_add_const u c
    rw [hw', hsum] at hw
    exact hw
  · rintro ⟨c, hc⟩
    refine ⟨u + fun _ : Fin N => c, ?_, ?_⟩
    · rw [LinearMap.mem_ker, UnitRaw.sumFun_apply]
      have hsum : ∑ i, (u + fun _ : Fin N => c) i = ∑ i, u i + (N : UnitRaw.F) * c := by
        simpa only [Pi.add_apply] using ufr_sum_add_const u c
      rw [hsum]
      exact hc
    · rw [map_add]
      have hz : (UnitRaw.oneLine N).mkQ (fun _ : Fin N => c) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (UnitRaw.mem_oneLine _).mpr ⟨c, rfl⟩
      rw [hz, add_zero]

private lemma ufr_range_dichotomy (N : ℕ) (R : AddSubgroup (UnitRaw.Vfull N))
    (hR : (UnitRaw.heart N).toAddSubgroup ≤ R) :
    R = ⊤ ∨ (3 ∣ N ∧ R = (UnitRaw.heart N).toAddSubgroup) := by
  have hheart0 : ∀ (u : UnitRaw.W N), (N : UnitRaw.F) = 0 →
      ((UnitRaw.oneLine N).mkQ u ∈ UnitRaw.heart N ↔ ∑ i, u i = 0) := by
    intro u hN0
    rw [ufr_mem_heart_iff u]
    constructor
    · rintro ⟨c, hc⟩
      simpa [hN0] using hc
    · intro h
      exact ⟨0, by simpa [hN0] using h⟩
  by_cases h3 : 3 ∣ N
  · by_cases hReq : R = (UnitRaw.heart N).toAddSubgroup
    · exact Or.inr ⟨h3, hReq⟩
    · refine Or.inl (eq_top_iff.mpr fun v _ => ?_)
      have hN0 : (N : UnitRaw.F) = 0 := (ZMod.natCast_eq_zero_iff N 3).mpr h3
      have hlt : (UnitRaw.heart N).toAddSubgroup < R := lt_of_le_of_ne hR (Ne.symm hReq)
      obtain ⟨v₀, hv₀R, hv₀h⟩ := Set.exists_of_ssubset hlt
      obtain ⟨u₀, rfl⟩ := (UnitRaw.oneLine N).mkQ_surjective v₀
      have hs₀ : ∑ i, u₀ i ≠ 0 := fun h0 =>
        hv₀h (by simpa [Submodule.mem_toAddSubgroup] using (hheart0 u₀ hN0).mpr h0)
      obtain ⟨u, rfl⟩ := (UnitRaw.oneLine N).mkQ_surjective v
      set k : UnitRaw.F := (∑ i, u i) * (∑ i, u₀ i)⁻¹ with hk
      have hsumk : ∑ i, (k • u₀) i = k * ∑ i, u₀ i := by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
      have hsub : ∑ i, (u - k • u₀) i = ∑ i, u i - ∑ i, (k • u₀) i := by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      have hzero : ∑ i, (u - k • u₀) i = 0 := by
        rw [hsub, hsumk, hk]
        have hkey : (∑ i, u i) * (∑ i, u₀ i)⁻¹ * ∑ i, u₀ i = ∑ i, u i := by
          rw [mul_assoc, inv_mul_cancel₀ hs₀, mul_one]
        rw [hkey, sub_self]
      have hmemR : (UnitRaw.oneLine N).mkQ (u - k • u₀) ∈ R :=
        hR (by rw [Submodule.mem_toAddSubgroup]; exact (hheart0 _ hN0).mpr hzero)
      have hsmul : k • (UnitRaw.oneLine N).mkQ u₀ ∈ R := by
        have h1 : k • (UnitRaw.oneLine N).mkQ u₀ ∈
            (AddSubgroup.toZModSubmodule 3 R : Submodule (ZMod 3) (UnitRaw.Vfull N)) :=
          Submodule.smul_mem _ k ((AddSubgroup.mem_toZModSubmodule 3).mpr hv₀R)
        exact (AddSubgroup.mem_toZModSubmodule 3).mp h1
      have hdecomp : (UnitRaw.oneLine N).mkQ u =
          (UnitRaw.oneLine N).mkQ (u - k • u₀) + k • (UnitRaw.oneLine N).mkQ u₀ := by
        rw [← map_smul, ← map_add]
        congr 1
        abel
      rw [hdecomp]
      exact R.add_mem hmemR hsmul
  · left
    have hN0 : (N : UnitRaw.F) ≠ 0 := fun h0 => h3 ((ZMod.natCast_eq_zero_iff N 3).mp h0)
    refine eq_top_iff.mpr fun v _ => ?_
    obtain ⟨u, rfl⟩ := (UnitRaw.oneLine N).mkQ_surjective v
    apply hR
    rw [Submodule.mem_toAddSubgroup]
    refine (ufr_mem_heart_iff u).mpr ⟨-(∑ i, u i) * (N : UnitRaw.F)⁻¹, ?_⟩
    have hkey : (N : UnitRaw.F) * (-(∑ i, u i) * (N : UnitRaw.F)⁻¹) = -(∑ i, u i) := by
      field_simp
    rw [hkey, add_neg_cancel]

theorem UnitFrame.exists_lift_centralizing {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {N : ℕ} {K : Type} [Field K] [Finite K] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* Kˣ} (fr : UnitFrame H E hEN K N ζ)
    (hUF : UnitaryFieldData 2 1 K) (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)))
    {w : UnitRaw.W N} (hw : ∑ i, w i = 0) :
    ∃ g : ↥H, g ^ 3 = 1 ∧
      fr.π g = LargeEvenProjMk _ ⟨diagOf ζ w, diagOf_mem_unitarySU ζ hUF hw⟩ ∧
      (g : G) ∈ Subgroup.centralizer (E : Set G) := by
  classical
  set t : ↥(unitarySU 2 1 K N) := ⟨diagOf ζ w, diagOf_mem_unitarySU ζ hUF hw⟩ with ht
  set s : LargeEvenProj (unitarySU 2 1 K N) := LargeEvenProjMk _ t with hs
  have ht3 : t ^ 3 = 1 := by
    apply Subtype.ext
    show (diagOf ζ w : GL (Fin N) K) ^ 3 = 1
    exact diagOf_pow_three ζ w
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← map_pow, ht3, map_one]
  obtain ⟨h₀, hh₀⟩ := fr.surj s
  set m : ℕ := Nat.card ↥(Subgroup.center ↥H) with hm
  have hm3 : ¬ 3 ∣ m := not_three_dvd_card_center hC3
  have hker : h₀ ^ 3 ∈ fr.π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hh₀, hs3]
  have hcen : h₀ ^ 3 ∈ Subgroup.center ↥H := fr.ker_le hker
  have hpow : (h₀ ^ 3) ^ m = 1 := by
    have h : (⟨h₀ ^ 3, hcen⟩ : ↥(Subgroup.center ↥H)) ^ m = 1 := by
      simp [m]
    simpa using congrArg Subtype.val h
  set g : ↥H := h₀ ^ (m ^ 2) with hg
  have hg3 : g ^ 3 = 1 := by
    have h1 : g ^ 3 = (h₀ ^ 3) ^ (m * m) := by
      rw [hg, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [h1, pow_mul, hpow, one_pow]
  have hm2 : m ^ 2 % 3 = 1 := by
    have hmne : m % 3 ≠ 0 := fun h => hm3 (Nat.dvd_of_mod_eq_zero h)
    rw [Nat.pow_mod]
    rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h | h <;> rw [h]
  have hπg : fr.π g = s := by
    rw [hg, map_pow, hh₀]
    calc s ^ (m ^ 2) = s ^ (m ^ 2 % 3) := pow_eq_pow_mod (m ^ 2) hs3
      _ = s ^ 1 := by rw [hm2]
      _ = s := pow_one s
  have hgG : (g : G) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg3
  have hcent : (g : G) ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨w_b, hw_b⟩ :=
      (UnitRaw.oneLine N).mkQ_surjective (fr.ι (Additive.ofMul (⟨b, hb⟩ : ↥E)))
    obtain ⟨hDb, hDb'⟩ := fr.intertwine (⟨b, hb⟩ : ↥E) w_b hw_b
    set x : ↥H := H.normalizerMonoidHom ⟨b, hEN hb⟩ g with hx
    have hπx : fr.π x = s := by
      have h1 : fr.π x = TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w_b, hDb⟩ s := by
        rw [hx, hDb' g, hπg]
      rw [h1, hs, TableBUD.projConj_mk_coe]
      congr 1
      apply Subtype.ext
      rw [CFSG.StandardType.normalizerMonoidHom_coe]
      show (diagOf ζ w_b : GL (Fin N) K) * (diagOf ζ w : GL (Fin N) K) *
        (diagOf ζ w_b : GL (Fin N) K)⁻¹ = diagOf ζ w
      rw [diagOf_comm ζ w_b w, mul_assoc, mul_inv_cancel, mul_one]
    have hkerx : x * g⁻¹ ∈ fr.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπx, hπg, mul_inv_cancel]
    have hcenterx : x * g⁻¹ ∈ Subgroup.center ↥H := fr.ker_le hkerx
    have hx3 : x ^ 3 = 1 := by
      have hval : (x : G) = b * (g : G) * b⁻¹ := by
        rw [hx, CFSG.StandardType.normalizerMonoidHom_coe]
      apply Subtype.ext
      show (x : G) ^ 3 = 1
      rw [hval]
      calc (b * (g : G) * b⁻¹) ^ 3 = MulAut.conj b ((g : G) ^ 3) := by
            rw [map_pow, MulAut.conj_apply]
        _ = 1 := by rw [hgG, map_one]
    have hc3 : (x * g⁻¹) ^ 3 = 1 := by
      have hcg : Commute (x * g⁻¹) g :=
        (Subgroup.mem_center_iff.mp hcenterx g).symm
      have hx' : x = (x * g⁻¹) * g := by group
      have hcalc : x ^ 3 = (x * g⁻¹) ^ 3 * g ^ 3 := by
        calc x ^ 3 = ((x * g⁻¹) * g) ^ 3 := by
              conv_lhs => rw [hx']
          _ = (x * g⁻¹) ^ 3 * g ^ 3 := hcg.mul_pow 3
      rw [hx3, hg3, mul_one] at hcalc
      exact hcalc.symm
    have hcx : x * g⁻¹ = 1 := ufr_center_pow_three_eq_one hcenterx hc3 hC3
    have hxg : x = g := mul_inv_eq_one.mp hcx
    have hxG : (x : G) = b * (g : G) * b⁻¹ := by
      rw [hx, CFSG.StandardType.normalizerMonoidHom_coe]
    have hgconj : b * (g : G) * b⁻¹ = (g : G) := by
      rw [← hxG, hxg]
    exact mul_inv_eq_iff_eq_mul.mp hgconj
  exact ⟨g, hg3, hπg, hcent⟩

private lemma ufr_lift {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ}
    {K : Type} [Field K] [Finite K] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* Kˣ} (fr : UnitFrame H E hEN K N ζ)
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 5 ≤ N)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)))
    {w : UnitRaw.W N} (hw : ∑ i, w i = 0) :
    ∃ e : ↥E, fr.ι (Additive.ofMul e) = (UnitRaw.oneLine N).mkQ w := by
  classical
  have hUF : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  have hN4 : 4 ≤ N := by omega
  obtain ⟨g, hg3, hπg, hcent⟩ := fr.exists_lift_centralizing hUF hC3 hw
  set t : ↥(unitarySU 2 1 K N) := ⟨diagOf ζ w, diagOf_mem_unitarySU ζ hUF hw⟩ with ht
  set s : LargeEvenProj (unitarySU 2 1 K N) := LargeEvenProjMk _ t with hs
  have hgG : (g : G) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg3
  have hgE : (g : G) ∈ E := hSC (g : G) hcent hgG
  refine ⟨⟨(g : G), hgE⟩, ?_⟩
  obtain ⟨w', hw'⟩ :=
    (UnitRaw.oneLine N).mkQ_surjective (fr.ι (Additive.ofMul (⟨(g : G), hgE⟩ : ↥E)))
  rw [← hw']
  obtain ⟨hD', hD'eq⟩ := fr.intertwine (⟨(g : G), hgE⟩ : ↥E) w' hw'
  have hDw : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    diagOf_mem_normalizer ζ hUF w
  have hmain : TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ =
      TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hDw⟩ := by
    apply MulEquiv.ext
    intro y
    obtain ⟨h', rfl⟩ := fr.surj y
    have hstep : fr.π (H.normalizerMonoidHom ⟨(g : G), hEN hgE⟩ h') =
        s * fr.π h' * s⁻¹ := by
      have h1 : H.normalizerMonoidHom ⟨(g : G), hEN hgE⟩ h' =
          (⟨(g : G), g.2⟩ : ↥H) * h' * (⟨(g : G), g.2⟩ : ↥H)⁻¹ := by
        apply Subtype.ext
        rw [CFSG.StandardType.normalizerMonoidHom_coe]
        rfl
      have h2 : fr.π (⟨(g : G), g.2⟩ : ↥H) = s := by
        rw [show (⟨(g : G), g.2⟩ : ↥H) = g from Subtype.ext rfl]
        exact hπg
      rw [h1, map_mul, map_mul, map_inv, h2]
    have hstep2 : TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hDw⟩ (fr.π h') =
        s * fr.π h' * s⁻¹ := by
      have hconj : TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hDw⟩ = MulAut.conj s := by
        rw [TableB.projConj_of_mem (unitarySU 2 1 K N) (diagOf ζ w)
          (diagOf_mem_unitarySU ζ hUF hw), hs, ht]
        rfl
      rw [hconj, MulAut.conj_apply]
    calc TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ (fr.π h')
        = fr.π (H.normalizerMonoidHom ⟨(g : G), hEN hgE⟩ h') := (hD'eq h').symm
      _ = s * fr.π h' * s⁻¹ := hstep
      _ = TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hDw⟩ (fr.π h') := hstep2.symm
  have hEq : TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, diagOf_mem_normalizer ζ hUF w⟩ =
      TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', diagOf_mem_normalizer ζ hUF w'⟩ := by
    rw [show (⟨diagOf ζ w, diagOf_mem_normalizer ζ hUF w⟩ :
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
        ⟨diagOf ζ w, hDw⟩ from Subtype.ext rfl,
      show (⟨diagOf ζ w', diagOf_mem_normalizer ζ hUF w'⟩ :
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
        ⟨diagOf ζ w', hD'⟩ from Subtype.ext rfl]
    exact hmain.symm
  exact ((projConj_diagOf_eq_iff ζ hUF hK hζ hN4 w w').mp hEq).symm

theorem unitFrameRange_holds : UnitFrameRange := by
  intro G _ _ H E N K _ _ hEN ζ fr hK hζ hN hSC hC3
  classical
  have hheart : (UnitRaw.heart N).toAddSubgroup ≤ fr.ι.range := by
    intro v hv
    rw [Submodule.mem_toAddSubgroup, UnitRaw.heart, Submodule.mem_map] at hv
    obtain ⟨w, hw, hwv⟩ := hv
    rw [LinearMap.mem_ker, UnitRaw.sumFun_apply] at hw
    obtain ⟨e, he⟩ := ufr_lift fr hK hζ hN hSC hC3 hw
    exact AddMonoidHom.mem_range.mpr ⟨Additive.ofMul e, by rw [he, hwv]⟩
  rcases ufr_range_dichotomy N fr.ι.range hheart with h | ⟨h3, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨h3, h⟩

end CFSG.StandardType.GGQ2Frame.UnitPlacement

end
