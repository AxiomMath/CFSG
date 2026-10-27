module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofExcl
public import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofInner
public import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofSeven
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofRed
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofCube
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofSyl
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

namespace ONLoc

theorem exists_ne_comm_of_card_27 {M Q : Type*} [Group M] [Finite M] [Group Q] [Finite Q]
    (π : M →* Q) (hker : ¬ 3 ∣ Nat.card π.ker) (hQq : IsQuasisimple Q)
    (htc : Sec4.IsTripleCover Q (alternatingGroup (Fin 7))) {T : Subgroup M}
    (hT : Nat.card T = 27) : ∃ t₁ ∈ T, ∃ t₂ ∈ T, t₁ * t₂ ≠ t₂ * t₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Nat.card Q = 7560 := Res9ON.card_of_isTripleCover_a7 htc
  have hinj : Function.Injective (π.domRestrict T) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    have ht' : (t : M) ∈ π.ker := ht
    have h1 : orderOf (t : M) ∣ Nat.card π.ker := by
      have := Subgroup.orderOf_dvd_natCard π.ker ht'
      exact this
    have h2 : orderOf t ∣ 27 := hT ▸ orderOf_dvd_natCard t
    rw [Subgroup.orderOf_coe] at h1
    have h3 : Nat.Coprime (orderOf t) (Nat.card π.ker) := by
      have h4 : Nat.Coprime 27 (Nat.card π.ker) := by
        rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
        exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker)
      exact Nat.Coprime.coprime_dvd_left h2 h4
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h1)
  have hcard : Nat.card (T.map π) = 27 := by
    rw [← MonoidHom.domRestrict_range, ← hT]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : (T.map π).index = 280 := by
    have h := (T.map π).index_mul_card
    rw [hcard, hQ] at h
    omega
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Subgroup.center Q, z ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : Subgroup.center Q = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
    have h3 := htc.1
    rw [hbot, Subgroup.card_bot] at h3
    omega
  have hz3 : orderOf z = 3 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center Q)) (x := ⟨z, hzZ⟩)
    rw [htc.1] at h
    exact orderOf_eq_prime (congrArg Subtype.val h) hz1
  obtain ⟨q₁, hq₁, q₂, hq₂, hq⟩ := Res9ON.exists_ne_comm_of_isPerfect hQq.1 hzZ hz3
    (by rw [hidx]; norm_num)
  obtain ⟨t₁, ht₁, rfl⟩ := hq₁
  obtain ⟨t₂, ht₂, rfl⟩ := hq₂
  refine ⟨t₁, ht₁, t₂, ht₂, fun h => hq ?_⟩
  rw [← map_mul, ← map_mul, h]

end ONLoc

theorem kf148ONA7_holds :
    KF148ONA7 := by
  intro Γ _ _ A L K N e hA heA he1 hLe hAL hLq hON3 hKL hAK hNK hNn hAN hN3 hqN htcN hsecN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := ↥L ⧸ aschbacherSolvableCore 3 ↥L with hXdef
  set Θ := inSubgroup (aschbacherSolvableCore 3) L with hΘdef
  have hZ3 : Nat.card (Subgroup.center X) = 3 := hON3.1
  obtain ⟨ψ⟩ := hON3.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  set σ := thetaQuotientAction 3 hAL with hσdef
  have hσ3 : ∀ a : ↥A, σ a ^ 3 = 1 := fun a => by
    rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (hA3 a a.2), map_one]
  have hinner : ∀ a : ↥A, ∃ x : X, σ a = MulAut.conj x := fun a =>
    Res9ON.exists_conj_of_pow_three_ON hLq hON3 (σ a) (hσ3 a)
  have hle : σ.range ≤ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := hinner a
    exact ⟨x, hx.symm⟩
  set P : Subgroup X := σ.range.comap (MulAut.conj : X →* MulAut X) with hPdef
  have hZP : Subgroup.center X ≤ P := fun z hz => by
    show MulAut.conj z ∈ σ.range
    rw [Res9ON.conj_eq_one_of_mem_center hz]
    exact σ.range.one_mem
  have hKΘ : K ⊓ Θ ≤ N := Res9ON.inf_theta_le hKL hqN htcN
  have hker : ∀ a : ↥A, a ∈ σ.ker ↔ (a : Γ) ∈ Subgroup.zpowers e := by
    intro a
    rw [mem_ker_thetaQuotientAction_iff]
    constructor
    · intro h
      have hsc : (a : Γ) ∈ Late.sectionCentralizer A K N := by
        refine ⟨a.2, fun k hk => ?_⟩
        have h2 : (a : Γ) * k * (a : Γ)⁻¹ * k⁻¹ ∈ K :=
          K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAK a.2) k).mp hk) (K.inv_mem hk)
        exact hKΘ ⟨h2, h k (hKL hk)⟩
      rw [hsecN] at hsc
      exact hsc
    · rintro ⟨n, hn⟩ y hy
      have hey : e * y = y * e := (Subgroup.mem_centralizer_singleton_iff.mp (hLe hy)).symm
      have hc : (a : Γ) * y = y * a := by
        rw [← hn]
        exact ((Commute.zpow_left hey n).eq)
      rw [hc, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hzeA : Subgroup.zpowers e ≤ A := Subgroup.zpowers_le.mpr heA
  have hkercard : Nat.card σ.ker = 3 := by
    have hkerEq : σ.ker = (Subgroup.zpowers e).subgroupOf A := by
      ext a
      rw [Subgroup.mem_subgroupOf]
      exact hker a
    rw [hkerEq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzeA).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime (hA3 e heA) he1]
  have hrange9 : Nat.card σ.range = 9 := by
    have h1 := Res9ON.card_eq_card_ker_mul_card_range σ
    rw [hA.2, hkercard] at h1
    omega
  have hP27 : Nat.card P = 27 := by
    set ι := (MulAut.conj : X →* MulAut X).domRestrict P with hιdef
    have hιrange : ι.range = σ.range := by
      rw [hιdef, MonoidHom.domRestrict_range, hPdef, Subgroup.map_comap_eq_self hle]
    have hιker : Nat.card ι.ker = 3 := by
      have hk : ι.ker = (Subgroup.center X).subgroupOf P := by
        ext x
        rw [hιdef, MonoidHom.ker_domRestrict, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          MonoidHom.mem_ker]
        exact ⟨Res9ON.mem_center_of_conj_eq_one, Res9ON.conj_eq_one_of_mem_center⟩
      rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ3]
    rw [Res9ON.card_eq_card_ker_mul_card_range ι, hιker, hιrange, hrange9]
  set f : ↥K →* X :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).comp (Subgroup.inclusion hKL) with hfdef
  have hfker : f.ker ≤ N.subgroupOf K := by
    intro k hk
    have h1 : (Subgroup.inclusion hKL k : ↥L) ∈ aschbacherSolvableCore 3 ↥L := by
      rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hk
      exact hk
    exact hKΘ ⟨k.2, ⟨_, h1, rfl⟩⟩
  set M : Subgroup X := f.range with hMdef
  set e1 := QuotientGroup.quotientKerEquivRange f with he1def
  have hfker' : f.ker ≤ (QuotientGroup.mk' (N.subgroupOf K)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hfker
  set hM : ↥M →* ↥K ⧸ N.subgroupOf K :=
    (QuotientGroup.lift f.ker (QuotientGroup.mk' (N.subgroupOf K)) hfker').comp
      e1.symm.toMonoidHom with hhMdef
  have hMe1 : ∀ k : ↥K, hM (e1 (k : ↥K ⧸ f.ker)) = (k : ↥K ⧸ N.subgroupOf K) := by
    intro k
    rw [hhMdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      QuotientGroup.lift_mk]
    rfl
  have hhMsurj : Function.Surjective hM := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf K) q
    exact ⟨e1 (k : ↥K ⧸ f.ker), hMe1 k⟩
  have he1val : ∀ k : ↥K, ((e1 (k : ↥K ⧸ f.ker) : ↥M) : X) = f k := fun k => rfl
  have hKN7560 : Nat.card (↥K ⧸ N.subgroupOf K) = 7560 := Res9ON.card_of_isTripleCover_a7 htcN
  have hkerN : ¬ 3 ∣ Nat.card hM.ker := by
    set φ : ↥K →* ↥M := e1.toMonoidHom.comp (QuotientGroup.mk' f.ker) with hφdef
    have hle' : hM.ker ≤ (N.subgroupOf K).map φ := by
      intro m hm
      obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective f.ker (e1.symm m)
      have hmk : m = e1 (k : ↥K ⧸ f.ker) := by
        rw [← QuotientGroup.mk'_apply, hk, MulEquiv.apply_symm_apply]
      have hkN : k ∈ N.subgroupOf K := by
        rw [MonoidHom.mem_ker, hmk, hMe1] at hm
        exact (QuotientGroup.eq_one_iff k).mp hm
      exact ⟨k, hkN, hmk.symm⟩
    have h1 : Nat.card hM.ker ∣ Nat.card N := by
      have h2 := Subgroup.card_dvd_of_le hle'
      have h3 := Subgroup.card_map_dvd (N.subgroupOf K) φ
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv] at h3
      exact h2.trans h3
    exact fun h3 => hN3 (h3.trans h1)
  have hkerM : ¬ 3 ∣ Nat.card (hM.ker.map M.subtype) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hkerN
  set π := QuotientGroup.mk' (Subgroup.center X) with hπdef
  have hcommZ : ∀ T : Subgroup X, IsPGroup 3 T → ∀ s ∈ T, ∀ t ∈ T,
      s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center X := by
    intro T hT s hs t ht
    obtain ⟨S, hTS, -, hSel⟩ := Res9ON.exists_elemAbelian_le_ON ψ (hT.map π)
    have hst : π s * π t = π t * π s :=
      congrArg Subtype.val (hSel.1.is_comm.comm ⟨π s, hTS ⟨s, hs, rfl⟩⟩ ⟨π t, hTS ⟨t, ht, rfl⟩⟩)
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπdef, map_mul, map_mul,
      map_mul, map_inv, map_inv, hst]
    group
  have hZM : Subgroup.center X ≤ M := by
    have h27 : 3 ^ 3 ∣ Nat.card ↥M := by
      rw [Res9ON.card_eq_card_ker_mul_card_range hM, MonoidHom.range_eq_top.mpr hhMsurj,
        Subgroup.card_top, hKN7560]
      exact dvd_mul_of_dvd_right (by norm_num) _
    obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime 3 h27
    obtain ⟨t₁, ht₁, t₂, ht₂, h12⟩ := ONLoc.exists_ne_comm_of_card_27 hM hkerN hqN htcN
      (by rw [hT]; norm_num)
    have hTp : IsPGroup 3 (T.map M.subtype) := IsPGroup.of_card (n := 3) (by
      rw [Subgroup.card_map_of_injective M.subtype_injective, hT])
    set c : X := (t₁ : X) * t₂ * (t₁ : X)⁻¹ * (t₂ : X)⁻¹ with hcdef
    have hcZ : c ∈ Subgroup.center X :=
      hcommZ _ hTp _ ⟨t₁, ht₁, rfl⟩ _ ⟨t₂, ht₂, rfl⟩
    have hcM : c ∈ M := M.mul_mem (M.mul_mem (M.mul_mem t₁.2 t₂.2) (M.inv_mem t₁.2))
      (M.inv_mem t₂.2)
    have hc1 : (⟨c, hcZ⟩ : Subgroup.center X) ≠ 1 := by
      intro h1
      apply h12
      have h2 : c = 1 := congrArg Subtype.val h1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      have h3 : (t₁ : X) * t₂ * (t₁ : X)⁻¹ * (t₂ : X)⁻¹ = 1 := h2
      calc (t₁ : X) * t₂ = (t₁ : X) * t₂ * (t₁ : X)⁻¹ * (t₂ : X)⁻¹ * (t₂ * t₁) := by group
        _ = t₂ * t₁ := by rw [h3, one_mul]
    have htop := zpowers_eq_top_of_prime_card hZ3 hc1
    intro z hz
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top (⟨z, hz⟩ :
      Subgroup.center X))
    have hz' : z = c ^ n := by
      have h1 := congrArg Subtype.val hn
      simpa using h1.symm
    rw [hz']
    exact zpow_mem hcM n
  have h21 : ∀ w h : X, w ∉ M → (∃ k : ℕ, w ^ 3 ^ k = 1) → orderOf h = 7 → w * h = h * w →
      False := fun w h hwM ⟨k, hk⟩ hh hc =>
    ONLoc.false_of_commute_seven hLq.1 hON3 hk (fun hz => hwM (hZM hz)) hh hc
  obtain ⟨v, g, hv7, hv1, hgv⟩ := ONLoc.exists_seven_of_isTripleCover htcN
  have hσf : ∀ (a : ↥A) (k : ↥K), σ a (f k) = f ⟨(a : Γ) * k * (a : Γ)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hAK a.2) k).mp k.2⟩ := fun _ _ => rfl
  have hPnM : ∀ p ∈ P, p ∈ Subgroup.normalizer (M : Set X) := by
    intro p hp
    obtain ⟨a, ha⟩ := hp
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := hn
    have h1 : p * f k * p⁻¹ = σ a (f k) := by rw [ha, MulAut.conj_apply]
    rw [SetLike.mem_coe, h1, hσf]
    exact ⟨_, rfl⟩
  have hPnN : ∀ p ∈ P, p ∈ Subgroup.normalizer ((hM.ker.map M.subtype : Subgroup X) : Set X) := by
    intro p hp
    obtain ⟨a, ha⟩ := hp
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨m, hm, rfl⟩ := hn
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective f.ker (e1.symm m)
    have hmk : m = e1 (k : ↥K ⧸ f.ker) := by
      rw [← QuotientGroup.mk'_apply, hk, MulEquiv.apply_symm_apply]
    have hm' : hM m = 1 := hm
    have hkN : (k : Γ) ∈ N := by
      rw [hmk, hMe1] at hm'
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff k).mp hm')
    set k' : ↥K := ⟨(a : Γ) * k * (a : Γ)⁻¹, (Subgroup.mem_normalizer_iff.mp (hAK a.2) k).mp k.2⟩
      with hk'def
    have hk'N : k' ∈ N.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hAN a.2) k).mp hkN)
    have h1 : p * (m : X) * p⁻¹ = f k' := by
      rw [hmk, he1val, show p * f k * p⁻¹ = σ a (f k) by rw [ha, MulAut.conj_apply], hσf]
    rw [SetLike.mem_coe, Subgroup.coe_subtype, h1]
    refine ⟨e1 (k' : ↥K ⧸ f.ker), ?_, he1val k'⟩
    show hM (e1 (k' : ↥K ⧸ f.ker)) = 1
    rw [hMe1]
    exact (QuotientGroup.eq_one_iff k').mpr hk'N
  have hPM : P ≤ M := by
    intro p hp
    have hp27 : p ^ 3 ^ 3 = 1 := by
      have h1 := pow_card_eq_one' (G := ↥P) (x := ⟨p, hp⟩)
      rw [hP27] at h1
      exact congrArg Subtype.val h1
    exact ONLoc.mem_of_normalizes_seven hM hhMsurj hkerM hKN7560 hv7 hv1 hgv h21 hp27
      (hPnM p hp) (hPnN p hp)
  obtain ⟨x₁, hx₁, x₂, hx₂, h12⟩ := ONLoc.exists_ne_comm_of_card_27 hM hkerN hqN htcN
    (T := P.subgroupOf M) (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hP27])
  have h12' : (x₁ : X) * x₂ ≠ x₂ * x₁ := fun h => h12 (Subtype.ext h)
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨T, hPT, hT81, hTel⟩ := Res9ON.exists_elemAbelian_le_ON ψ (hPp.map π)
  set S := T.comap π with hSdef
  have hPS : P ≤ S := fun x hx => hPT ⟨x, hx, rfl⟩
  have hZS : Subgroup.center X ≤ S := fun z hz => by
    show π z ∈ T
    rw [hπdef, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
    exact T.one_mem
  have hS243 : Nat.card S = 243 := by
    set ι := π.domRestrict S with hιdef
    have hιrange : ι.range = T := by
      rw [hιdef, MonoidHom.domRestrict_range, hSdef,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    have hιker : Nat.card ι.ker = 3 := by
      have hk : ι.ker = (Subgroup.center X).subgroupOf S := by
        rw [hιdef, MonoidHom.ker_domRestrict, hπdef, QuotientGroup.ker_mk']
      rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv, hZ3]
    rw [Res9ON.card_eq_card_ker_mul_card_range ι, hιker, hιrange, hT81]
  have hScomm : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center X := by
    intro s hs t ht
    have hst : π s * π t = π t * π s :=
      congrArg Subtype.val (hTel.1.is_comm.comm ⟨π s, hs⟩ ⟨π t, ht⟩)
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπdef, map_mul, map_mul,
      map_mul, map_inv, map_inv, hst]
    group
  have hS3 : ∀ s ∈ S, s ^ 3 ∈ Subgroup.center X := by
    intro s hs
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπdef, map_pow]
    exact hTel.2 _ hs
  obtain ⟨r, hrS, hr3, hrP, hrc⟩ := Res9ON.exists_pow_three_eq_one_centralizes le_rfl hZ3 hZP
    hP27 (Subgroup.mem_subgroupOf.mp hx₁) (Subgroup.mem_subgroupOf.mp hx₂) h12' hPS hS243 hScomm
    hS3
  have hrfix : ∀ a : ↥A, σ a r = r := by
    intro a
    obtain ⟨x, hx⟩ := hinner a
    have hxP : x ∈ P := by
      show MulAut.conj x ∈ σ.range
      rw [← hx]
      exact ⟨a, rfl⟩
    rw [hx, MulAut.conj_apply, hrc x hxP, mul_inv_cancel_right]
  set α : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL) with hαdef
  have hαθ : ∀ a : ↥A, ∀ n ∈ aschbacherSolvableCore 3 ↥L,
      α a n ∈ aschbacherSolvableCore 3 ↥L := by
    intro a n hn
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (aschbacherSolvableCore 3 ↥L).Characteristic) (α a)
    rw [← hmap]
    exact ⟨n, hn, rfl⟩
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hlift := Semidihedral.Principal.coprime_fixed_point_lifting 3 hA.isPGroup α
    (aschbacherSolvableCore 3 ↥L) hαθ hθ3
  have hrmem : r ∈ {q : X | ∀ a : ↥A, Semidihedral.Principal.CoprimeFixedPoint.quotientAction α
      (aschbacherSolvableCore 3 ↥L) hαθ a q = q} := by
    intro a
    have hq : ∀ q : X, Semidihedral.Principal.CoprimeFixedPoint.quotientAction α
        (aschbacherSolvableCore 3 ↥L) hαθ a q = σ a q := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H y => rfl
    rw [hq]
    exact hrfix a
  rw [hlift] at hrmem
  obtain ⟨c, hcfix, hcr⟩ := hrmem
  have hcA : ∀ a ∈ A, a * (c : Γ) = c * a := by
    intro a ha
    have h1 : a * (c : Γ) * a⁻¹ = c := congrArg Subtype.val (hcfix ⟨a, ha⟩)
    calc a * (c : Γ) = a * c * a⁻¹ * a := by group
      _ = c * a := by rw [h1]
  obtain ⟨k, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 3 (by norm_num)
  set x₀ : ↥L := c ^ m with hx₀def
  have hx₀k : x₀ ^ 3 ^ k = 1 := by
    rw [hx₀def, ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hmkx₀ : ((x₀ : ↥L) : X) = r ^ m := by
    rw [hx₀def, QuotientGroup.mk_pow, ← hcr]
    rfl
  have hr1 : r ≠ 1 := fun h => hrP (h ▸ P.one_mem)
  have hro : orderOf r = 3 := orderOf_eq_prime hr3 hr1
  have hrm : r ^ m ≠ 1 := fun h => hm3 (hro ▸ orderOf_dvd_of_pow_eq_one h)
  have hx₀3 : x₀ ^ 3 = 1 := by
    have h1 : x₀ ^ 3 ∈ aschbacherSolvableCore 3 ↥L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmkx₀, ← pow_mul, mul_comm, pow_mul,
        hr3, one_pow]
    have h2 : orderOf (x₀ ^ 3) ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
      Subgroup.orderOf_dvd_natCard _ h1
    have h3 : orderOf (x₀ ^ 3) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hx₀k, one_pow])
    have h4 : Nat.Coprime (orderOf (x₀ ^ 3)) (Nat.card (aschbacherSolvableCore 3 ↥L)) :=
      Nat.Coprime.coprime_dvd_left h3
        (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3))
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h4 h2)
  have hx₀1 : x₀ ≠ 1 := fun h => hrm (by rw [← hmkx₀, h]; rfl)
  refine ⟨(x₀ : Γ), ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hx : (x₀ : Γ) = (c : Γ) ^ m := by rw [hx₀def, Subgroup.coe_pow]
    rw [hx]
    exact (Commute.pow_right (hcA a ha) m).eq
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx₀3 hx₀1
  · intro hxA
    have hσx : σ ⟨(x₀ : Γ), hxA⟩ = MulAut.conj ((x₀ : ↥L) : X) := by
      ext q
      induction q using QuotientGroup.induction_on with
      | H y =>
        rw [Res9ON.thetaQuotientAction_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
          ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        rfl
    have hrmP : r ^ m ∈ P := by
      show MulAut.conj (r ^ m) ∈ σ.range
      rw [← hmkx₀, ← hσx]
      exact ⟨_, rfl⟩
    have hcop : (orderOf r).Coprime m := by
      rw [hro]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
    have hzp : Subgroup.zpowers (r ^ m) = Subgroup.zpowers r := by
      refine Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers r) m)) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow hcop]
    exact hrP (Subgroup.zpowers_le.mpr hrmP (hzp ▸ Subgroup.mem_zpowers r))

end CFSG.RankThree.PartTwo.Sec14
