module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltModule
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltSix
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltCycle
public import CFSG.Alternating.Multipliers.Main
public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

open CFSG.Quasithin Equiv
open scoped commutatorElement

section NineOne

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem five_le_of_altCover (hperf : commutator X = ⊤) (hZ : Subgroup.center X ≠ ⊥) {n : ℕ}
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) : 5 ≤ n := by
  by_contra hn
  push Not at hn
  have : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have : Group.IsSolvable (X ⧸ Subgroup.center X) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Group.IsSolvable (Subgroup.center X) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  have : Group.IsSolvable X := Group.isSolvable_of_ker_le_range (Subgroup.center X).subtype
    (QuotientGroup.mk' (Subgroup.center X)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have : Group.IsPerfect X := Group.isPerfect_def.mpr hperf
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
  have : Nontrivial X := nontrivial_of_ne z 1 fun h => hz1 (Subtype.ext h)
  exact Group.IsPerfect.not_isSolvable X ‹Group.IsSolvable X›

theorem card_center_eq_three_of_altCover (hperf : commutator X = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center X))) (hZ : Subgroup.center X ≠ ⊥) {n : ℕ}
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) :
    Nat.card (Subgroup.center X) = 3 ∧ (n = 6 ∨ n = 7) := by
  have hn5 := five_le_of_altCover hperf hZ e
  have : Group.IsPerfect X := Group.isPerfect_def.mpr hperf
  let π : X →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hne1 : Nat.card (Subgroup.center X) ≠ 1 := fun h =>
    hZ (Subgroup.eq_bot_of_card_eq _ h)
  by_cases h8 : 8 ≤ n
  · exfalso
    have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier this π hπ hker.le
    rw [hker, CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup h8] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact hne1 h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  · push Not at h8
    have hb := CFSG.SectionRank.alternating_small_odd_cover_bound hn5 (by omega) π hπ hker.le
      (by rwa [hker])
    rw [hker] at hb
    have h567 : n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases h567 with rfl | rfl | rfl
    · exact absurd (hb.1 (Or.inl rfl)) hZ
    · rcases hb.2 (Or.inl rfl) with h | h
      · exact absurd h hne1
      · exact ⟨h, Or.inl rfl⟩
    · rcases hb.2 (Or.inr rfl) with h | h
      · exact absurd h hne1
      · exact ⟨h, Or.inr rfl⟩

omit [Finite X] in
theorem isQuasisimple_of_alt6 (hperf : commutator X = ⊤)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) : CFSG.IsQuasisimple X := by
  have : Group.IsPerfect X := Group.isPerfect_def.mpr hperf
  have hs : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  refine ⟨this, hs, ?_⟩
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isMulCommutative (X ⧸ Subgroup.center X) ⟨⟨h⟩⟩

end NineOne

theorem isHat_alt6_of_altCover {W : Type} [CommGroup W] [Finite W] [Nontrivial W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hperf : commutator ↥L = ⊤)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (hZ : Subgroup.center ↥L ≠ ⊥)
    {n : ℕ} (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n))
    {t : MulAut W} (htL : ∀ l ∈ L, t * l * t⁻¹ ∈ L) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) :
    IsHat ↥L ↥(alternatingGroup (Fin 6)) ∧ Nat.card W = 2 ^ 6 := by
  classical
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) fun f g h => MulEquiv.ext (congrFun h)
  have hfixV : ∀ {g : MulAut W} {v : W}, v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
    CFSG.Quasithin.mem_fixV_zpowers_iff_apply
  have hn5 := five_le_of_altCover hperf hZ e
  obtain ⟨hZ3, hn⟩ := card_center_eq_three_of_altCover hperf hodd hZ e
  have hZpow : ∀ c ∈ Subgroup.center ↥L, c ^ 3 = 1 := fun c hc => by
    have := orderOf_dvd_natCard (⟨c, hc⟩ : ↥(Subgroup.center ↥L))
    rw [hZ3] at this
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp this)
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
  have hz1' : (z : MulAut W) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hzc : ∀ g ∈ L, g * (z : MulAut W) = (z : MulAut W) * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨g, hg⟩)
  have hz3 : (z : MulAut W) ^ 3 = 1 := by simpa using congrArg Subtype.val (hZpow z hzZ)
  have hzinv : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers (z : MulAut W)),
      g u ∈ fixV (Subgroup.zpowers (z : MulAut W)) := fun g hg u hu => by
    rw [hfixV] at hu ⊢
    calc (z : MulAut W) (g u) = ((z : MulAut W) * g) u := rfl
      _ = (g * (z : MulAut W)) u := by rw [hzc g hg]
      _ = g u := by rw [MulAut.mul_apply, hu]
  have hfix : fixV (Subgroup.zpowers (z : MulAut W)) = ⊥ := by
    rcases hirr _ hzinv with h | h
    · exact h
    · exfalso
      refine hz1' (MulEquiv.ext fun w => ?_)
      exact hfixV.mp (h ▸ Subgroup.mem_top w)
  let a0 : Fin n := ⟨0, by omega⟩
  let a1 : Fin n := ⟨1, by omega⟩
  let a2 : Fin n := ⟨2, by omega⟩
  have hc3 : (swap a0 a1 * swap a0 a2).IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same (by simp [a0, a1, Fin.ext_iff])
      (by simp [a0, a2, Fin.ext_iff]) (by simp [a1, a2, Fin.ext_iff])
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm ⟨_, hc3.mem_alternatingGroup⟩)
  have hxc : ((e x : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle := by
    rw [hx, MulEquiv.apply_symm_apply]
    exact hc3
  have hmkz : ∀ (y : ↥L), ∀ c ∈ Subgroup.center ↥L,
      (QuotientGroup.mk (y * c) : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk y := fun y c hc => by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).mpr hc, mul_one]
  have hcard : ∀ y : ↥L, ((e y : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle →
      Nat.card ↥(fixV (Subgroup.zpowers (y : MulAut W))) =
        Nat.card ↥(fixV (Subgroup.zpowers (x : MulAut W))) := fun y hy => by
    obtain ⟨g, hg⟩ := exists_conj_of_isThreeCycle hn hperf hZ3 e hxc hy
    rw [← hg]
    exact card_fixV_zpowers_conj (g : MulAut W) (x : MulAut W)
  have hxz : (x : MulAut W) * z = z * x := hzc x x.2
  have hx3 : (x : MulAut W) ^ 3 = 1 := by
    simpa using congrArg Subtype.val (pow_three_eq_one_of_isThreeCycle hn5 hZ3 e hxc)
  obtain ⟨k, hk⟩ := exists_card_eq_four_pow hW hz3
    (U := fixV (Subgroup.zpowers (x : MulAut W)))
    (fun u hu => by
      rw [hfixV] at hu ⊢
      calc (x : MulAut W) ((z : MulAut W) u) = ((x : MulAut W) * z) u := rfl
        _ = ((z : MulAut W) * x) u := by rw [hxz]
        _ = (z : MulAut W) u := by rw [MulAut.mul_apply, hu])
    (fun u _ hu => by
      have h1 : u ∈ fixV (Subgroup.zpowers (z : MulAut W)) := hfixV.mpr hu
      rw [hfix] at h1
      exact (Subgroup.mem_bot).mp h1)
  have hlift : ∀ i : ℕ, ((e (QuotientGroup.mk (x * z ^ i)) : alternatingGroup (Fin n)) :
      Perm (Fin n)).IsThreeCycle := fun i => by
    rw [hmkz x (z ^ i) (Subgroup.pow_mem _ hzZ i)]
    exact hxc
  have hc1 := hcard (x * z ^ 1) (hlift 1)
  have hc2 := hcard (x * z ^ 2) (hlift 2)
  have e1 : ((x * z ^ 1 : ↥L) : MulAut W) = (x : MulAut W) * z := by simp
  have e2 : ((x * z ^ 2 : ↥L) : MulAut W) = (x : MulAut W) * (z : MulAut W) ^ 2 := by simp
  rw [e1] at hc1
  rw [e2] at hc2
  have hW3 : Nat.card W = 4 ^ (3 * k) := by
    rw [card_eq_mul_mul_of_fpf hW hxz hx3 hz3 hfix, hc1, hc2, hk]
    ring
  have hW6k : Nat.card W = 2 ^ (6 * k) := by
    rw [hW3, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : Nat.card W = 1 := by rw [hW3]; rfl
    exact (Finite.one_lt_card (α := W)).ne' h1
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have htt' : ∀ g : MulAut W, t * (t * g * t⁻¹) * t⁻¹ = g := fun g => by
    calc t * (t * g * t⁻¹) * t⁻¹ = (t * t) * g * (t * t)⁻¹ := by group
      _ = g := by rw [htt, one_mul, inv_one, mul_one]
  let α : MulAut ↥L :=
    { toFun := fun l => ⟨t * l * t⁻¹, htL l l.2⟩
      invFun := fun l => ⟨t * l * t⁻¹, htL l l.2⟩
      left_inv := fun l => Subtype.ext (htt' l)
      right_inv := fun l => Subtype.ext (htt' l)
      map_mul' := fun a b => Subtype.ext (by
        change t * ((a : MulAut W) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹)
        group) }
  have hα : ∀ l : ↥L, ((α l : ↥L) : MulAut W) = t * l * t⁻¹ := fun l => rfl
  have hα2 : α * α = 1 := MulEquiv.ext fun l => Subtype.ext (htt' l)
  have hidx_dvd : (fixV (Subgroup.zpowers t)).index ∣ 2 ^ (6 * k) :=
    hW6k ▸ Subgroup.index_dvd_card _
  obtain ⟨j, hj6, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx_dvd
  have hmj : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) = j := by
    rw [E3.mQuot, Subgroup.relIndex_top_right, hj, padicValNat.prime_pow]
  rw [hmj] at hm
  have hk1 : k = 1 := by
    by_cases hout : ∀ y : ↥L, α ≠ MulAut.conj y
    ·
      have hinv : ∀ c ∈ Subgroup.center ↥L, α c = c⁻¹ := by
        rcases hn with rfl | rfl
        · exact inv_center_of_not_inner_six ⟨isQuasisimple_of_alt6 hperf e, hZ3, ⟨e⟩⟩ α hα2 hout
        · exact inv_center_of_not_inner_seven hperf hZ3 e α hout
      have htz : t * (z : MulAut W) * t⁻¹ = (z : MulAut W)⁻¹ := congrArg Subtype.val (hinv z hzZ)
      have hidx := index_fixV_of_inv_fpf hW hz3 hfix htt htz hW3
      rw [hj] at hidx
      have : j = 3 * k := Nat.pow_right_injective le_rfl hidx
      omega
    ·
      push Not at hout
      obtain ⟨l, hl⟩ := hout
      have hconj : ∀ g : ↥L,
          t * (g : MulAut W) * t⁻¹ = (l : MulAut W) * g * (l : MulAut W)⁻¹ := fun g => by
        have := congrArg (fun f : MulAut ↥L => ((f g : ↥L) : MulAut W)) hl
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
        exact (hα g).symm.trans this
      have hlZ : l ∉ Subgroup.center ↥L := by
        intro hlc
        have htc : ∀ g ∈ L, t * g = g * t := fun g hg => by
          have h1 := hconj ⟨g, hg⟩
          have h2 : (l : MulAut W) * g = g * l :=
            (congrArg Subtype.val (Subgroup.mem_center_iff.mp hlc ⟨g, hg⟩)).symm
          have h3 : t * g * t⁻¹ = g := by
            rw [h1, h2, mul_inv_cancel_right]
          calc t * g = t * g * t⁻¹ * t := by group
            _ = g * t := by rw [h3]
        have hinvt : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers t), g u ∈ fixV (Subgroup.zpowers t) :=
          fun g hg u hu => by
            rw [hfixV] at hu ⊢
            calc t (g u) = (t * g) u := rfl
              _ = (g * t) u := by rw [htc g hg]
              _ = g u := by rw [MulAut.mul_apply, hu]
        rcases hirr _ hinvt with h | h
        · rw [h, Subgroup.index_bot, hW6k] at hj
          have : j = 6 * k := (Nat.pow_right_injective le_rfl hj).symm
          omega
        · have ht1 : t = 1 := MulEquiv.ext fun w => hfixV.mp (h ▸ Subgroup.mem_top w)
          rw [ht1, orderOf_one] at ht2
          exact absurd ht2 (by decide)
      have hl2 : l ^ 2 ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 : MulAut.conj l * MulAut.conj l = 1 := by rw [← hl]; exact hα2
        have h2 := congrArg (fun f : MulAut ↥L => f g) h1
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h2
        calc g * l ^ 2 = (l * (l * g * l⁻¹) * l⁻¹) * l ^ 2 := by rw [h2]
          _ = l ^ 2 * g := by rw [pow_two]; group
      obtain ⟨y, hy, hly⟩ := exists_isThreeCycle_conj_eq_inv hn hZ3 e hl2 hlZ
      have hty : t * (y : MulAut W) * t⁻¹ = (y : MulAut W)⁻¹ := by
        rw [hconj y]
        exact congrArg Subtype.val hly
      have htz : t * (z : MulAut W) = z * t := by
        have h1 := hconj z
        have h2 : (l : MulAut W) * z * (l : MulAut W)⁻¹ = z := by
          rw [hzc l l.2, mul_inv_cancel_right]
        rw [h2] at h1
        calc t * (z : MulAut W) = t * z * t⁻¹ * t := by group
          _ = z * t := by rw [h1]
      have hyz : (y : MulAut W) * z = z * y := hzc y y.2
      have hy3 : (y : MulAut W) ^ 3 = 1 := by
        simpa using congrArg Subtype.val (pow_three_eq_one_of_isThreeCycle hn5 hZ3 e hy)
      have hle := card_fixV_le_index_of_inv hW hyz hy3 hz3 hfix htt hty htz
      have hyc : ((e (QuotientGroup.mk (y * z)) : alternatingGroup (Fin n)) :
          Perm (Fin n)).IsThreeCycle := by
        rw [hmkz y z hzZ]
        exact hy
      have h4 : Nat.card ↥(fixV (Subgroup.zpowers ((y : MulAut W) * (z : MulAut W)))) =
          4 ^ k := by
        have := hcard (y * z) hyc
        rw [show ((y * z : ↥L) : MulAut W) = (y : MulAut W) * z from rfl] at this
        rw [this, hk]
      rw [h4, hj, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at hle
      have : 2 * k ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
      omega
  subst hk1
  have hW64 : Nat.card W = 2 ^ 6 := by rw [hW6k]
  have hn6 : n = 6 := by
    rcases hn with h | h
    · exact h
    · exfalso
      subst h
      obtain ⟨x', u, hx', hu2, hu1, hux⟩ := exists_isThreeCycle_commute_involution hZ3 e
      have hx'3 : (x' : MulAut W) ^ 3 = 1 := by
        simpa using congrArg Subtype.val (pow_three_eq_one_of_isThreeCycle hn5 hZ3 e hx')
      have hc4 : ∀ i : ℕ,
          Nat.card ↥(fixV (Subgroup.zpowers ((x' : MulAut W) * (z : MulAut W) ^ i))) = 4 := by
        intro i
        have hyc : ((e (QuotientGroup.mk (x' * z ^ i)) : alternatingGroup (Fin 7)) :
            Perm (Fin 7)).IsThreeCycle := by
          rw [hmkz x' (z ^ i) (Subgroup.pow_mem _ hzZ i)]
          exact hx'
        have := hcard (x' * z ^ i) hyc
        rw [show ((x' * z ^ i : ↥L) : MulAut W) = (x' : MulAut W) * (z : MulAut W) ^ i by simp]
          at this
        rw [this, hk, pow_one]
      have hu : (u : MulAut W) * u = 1 := by
        simpa [pow_two] using congrArg Subtype.val hu2
      have hu1' := eq_one_of_card_fixV_eq_four hW (hzc x' x'.2) hx'3 hz3 hfix
        (congrArg Subtype.val hux) (hzc u u.2) hu (by simpa using hc4 0) (by simpa using hc4 1)
        (hc4 2)
      exact hu1 (Subtype.ext hu1')
  subst hn6
  exact ⟨⟨isQuasisimple_of_alt6 hperf e, hZ3, ⟨e⟩⟩, hW64⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

end
