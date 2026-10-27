module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFixNormal
public import Certificates.Certificate725007
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowLiftGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main
public import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Bridge.J2Excl CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.Quasithin.B45Exc.HSRu

private theorem j2A_card_image_le_sixteen
    {W : Type} [CommGroup W] [Finite W]
    {Q : Subgroup (MulAut W)} (ψ : ↥Q →* ↥j2R) (hψ : Function.Injective ψ)
    {A : Subgroup (MulAut W)} (hAQ : A ≤ Q) (hAel : IsElemAbelian2 A) :
    Nat.card A ≤ 2 ^ 4 := by
  let B : Subgroup ↥j2R := (A.subgroupOf Q).map ψ
  have hcard : Nat.card B = Nat.card A := by
    rw [Subgroup.card_map_of_injective hψ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv]
  rw [← hcard]
  refine j2_rank_R B ?_ ?_
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    have hab : a * b = b * a := by
      apply Subtype.ext
      exact hAel.1 _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb)
    rw [← map_mul, ← map_mul, hab]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have haa : a * a = 1 := by
      apply Subtype.ext
      simpa [sq] using hAel.2 _ (Subgroup.mem_subgroupOf.1 ha)
    rw [← map_mul, haa, map_one]

private theorem j2A_nat_card_eq_sixteen
    {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (ψL : Lift L Y j2R j2P) {A : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet 4 Y) : Nat.card A = 16 := by
  have hle : Nat.card A ≤ 2 ^ 4 :=
    j2A_card_image_le_sixteen ψL.hom ψL.inj (hA.1.trans le_sup_right) hA.2.2.1
  have hApg : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hcardpow : Nat.card A = 2 ^ E3.mQuot A ⊥ := by
    rw [← E3.relIndex_eq_two_pow hApg ⊥, Subgroup.relIndex_bot_left]
  have hm4 : 4 ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
  have hmle : E3.mQuot A ⊥ ≤ 4 := by
    rw [hcardpow] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  rw [hcardpow, show E3.mQuot A ⊥ = 4 from by omega]
  norm_num

private theorem j2A_fixV_zpowers_eq {W : Type} [CommGroup W] [Finite W]
    {Y : Subgroup (MulAut W)} {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 4 Y)
    (hAcard : Nat.card A = 16) {x : MulAut W} (hx : x ∈ A) (hx1 : x ≠ 1) :
    fixV (Subgroup.zpowers x) = fixV A := by
  have hx2 : x * x = 1 := by
    simpa [sq] using hA.2.2.1.2 x hx
  have hxord : orderOf x = 2 := orderOf_eq_prime (by simpa [sq] using hx2) hx1
  have hcardzx : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers, hxord]
  have hle : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.2 hx
  have hrel : (Subgroup.zpowers x).relIndex A = 8 := by
    have h := Subgroup.relIndex_mul_card (Subgroup.zpowers x) A
    rw [inf_eq_left.2 hle, hcardzx, hAcard] at h
    omega
  have hmq : E3.mQuot A (Subgroup.zpowers x) = 3 := by
    rw [E3.mQuot, hrel, show (8 : ℕ) = 2 ^ 3 from rfl, padicValNat.prime_pow]
  exact hA.2.2.2 (Subgroup.zpowers x) hle (by rw [hmq]; norm_num)

private theorem j2A_e16_image_pair
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (ψL : Lift L Y j2R j2P) {A : Subgroup (MulAut W)} (hAQ : A ≤ L ⊔ Y)
    (hAel : IsElemAbelian2 A) (hAcard : Nat.card A = 16) :
    ∃ d₀ ∈ (A.subgroupOf (L ⊔ Y)).map (j2R.subtype.comp ψL.hom),
      ∃ e₀ ∈ (A.subgroupOf (L ⊔ Y)).map (j2R.subtype.comp ψL.hom), d₀ ≠ 1 ∧ e₀ ≠ 1 ∧
        j2P ≤ Subgroup.closure
          (((j2P ⊓ Subgroup.centralizer {d₀} : Subgroup (Equiv.Perm (Fin 315))) :
            Set (Equiv.Perm (Fin 315))) ∪
            (j2P ⊓ Subgroup.centralizer {e₀} : Subgroup (Equiv.Perm (Fin 315)))) := by
  let φ : ↥(L ⊔ Y) →* Equiv.Perm (Fin 315) := j2R.subtype.comp ψL.hom
  have hφinj : Function.Injective φ := j2R.subtype_injective.comp ψL.inj
  let B₀ : Subgroup (Equiv.Perm (Fin 315)) := (A.subgroupOf (L ⊔ Y)).map φ
  have hB0R : B₀ ≤ j2R := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact (ψL.hom a).2
  have hcommB : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    have hab : a * b = b * a := by
      apply Subtype.ext
      exact hAel.1 _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb)
    rw [← map_mul, ← map_mul, hab]
  have hsqB : ∀ x ∈ B₀, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have haa : a * a = 1 := by
      apply Subtype.ext
      simpa [sq] using hAel.2 _ (Subgroup.mem_subgroupOf.1 ha)
    rw [← map_mul, haa, map_one]
  have hcardB : Nat.card B₀ = 16 := by
    rw [Subgroup.card_map_of_injective hφinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv, hAcard]
  obtain ⟨d₀, hd₀B, e₀, he₀B, hd₀1, he₀1, hgenP⟩ :=
    Certificates.certificate725007 B₀ hB0R hcommB hsqB hcardB
  exact ⟨d₀, by simpa [B₀, φ] using hd₀B, e₀, by simpa [B₀, φ] using he₀B,
    hd₀1, he₀1, hgenP⟩

private theorem j2A_pullback_gen_centralizers
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (ψL : Lift L Y j2R j2P) {A : Subgroup (MulAut W)} (hAY : A ≤ Y)
    {d₀ e₀ : Equiv.Perm (Fin 315)}
    (hd₀ : d₀ ∈ (A.subgroupOf (L ⊔ Y)).map (j2R.subtype.comp ψL.hom))
    (he₀ : e₀ ∈ (A.subgroupOf (L ⊔ Y)).map (j2R.subtype.comp ψL.hom))
    (hd₀1 : d₀ ≠ 1) (he₀1 : e₀ ≠ 1)
    (hgenP : j2P ≤ Subgroup.closure
      (((j2P ⊓ Subgroup.centralizer {d₀} : Subgroup (Equiv.Perm (Fin 315))) :
        Set (Equiv.Perm (Fin 315))) ∪
        (j2P ⊓ Subgroup.centralizer {e₀} : Subgroup (Equiv.Perm (Fin 315))))) :
    ∃ d ∈ A, ∃ e ∈ A, d ≠ 1 ∧ e ≠ 1 ∧
      L ≤ Subgroup.closure (((Subgroup.centralizer {d} : Subgroup (MulAut W)) :
        Set (MulAut W)) ∪ (Subgroup.centralizer {e} : Subgroup (MulAut W))) := by
  obtain ⟨dQ, hdQ, hdφ⟩ := Subgroup.mem_map.1 hd₀
  obtain ⟨eQ, heQ, heφ⟩ := Subgroup.mem_map.1 he₀
  have hdA : (dQ : MulAut W) ∈ A := Subgroup.mem_subgroupOf.1 hdQ
  have heA : (eQ : MulAut W) ∈ A := Subgroup.mem_subgroupOf.1 heQ
  have hdY : (dQ : MulAut W) ∈ Y := hAY hdA
  have heY : (eQ : MulAut W) ∈ Y := hAY heA
  have hd1 : (dQ : MulAut W) ≠ 1 := by
    intro h
    apply hd₀1
    rw [← hdφ]
    have hdQ1 : dQ = 1 := Subtype.ext h
    rw [hdQ1, map_one]
  have he1 : (eQ : MulAut W) ≠ 1 := by
    intro h
    apply he₀1
    rw [← heφ]
    have heQ1 : eQ = 1 := Subtype.ext h
    rw [heQ1, map_one]
  have hd₀eq : ((ψL.hom ⟨(dQ : MulAut W), Subgroup.mem_sup_right hdY⟩ : ↥j2R) :
      Equiv.Perm (Fin 315)) = d₀ := by
    rw [← hdφ, show (⟨(dQ : MulAut W), Subgroup.mem_sup_right hdY⟩ : ↥(L ⊔ Y)) = dQ from
      Subtype.ext rfl]
    rfl
  have he₀eq : ((ψL.hom ⟨(eQ : MulAut W), Subgroup.mem_sup_right heY⟩ : ↥j2R) :
      Equiv.Perm (Fin 315)) = e₀ := by
    rw [← heφ, show (⟨(eQ : MulAut W), Subgroup.mem_sup_right heY⟩ : ↥(L ⊔ Y)) = eQ from
      Subtype.ext rfl]
    rfl
  have hgen : j2P ≤ Subgroup.closure
      (((j2P ⊓ Subgroup.centralizer {((ψL.hom ⟨(dQ : MulAut W),
        Subgroup.mem_sup_right hdY⟩ : ↥j2R) : Equiv.Perm (Fin 315))} :
          Subgroup (Equiv.Perm (Fin 315))) : Set (Equiv.Perm (Fin 315))) ∪
        (j2P ⊓ Subgroup.centralizer {((ψL.hom ⟨(eQ : MulAut W),
          Subgroup.mem_sup_right heY⟩ : ↥j2R) : Equiv.Perm (Fin 315))} :
          Subgroup (Equiv.Perm (Fin 315)))) := by
    simpa [← hd₀eq, ← he₀eq] using hgenP
  exact ⟨(dQ : MulAut W), hdA, (eQ : MulAut W), heA, hd1, he1,
    W4Row.le_closure_centralizer_of_lift ψL hdY heY hgen⟩

private theorem j2A_exists_gen_centralizers
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (ψL : Lift L Y j2R j2P) {A : Subgroup (MulAut W)} (hAY : A ≤ Y)
    (hAQ : A ≤ L ⊔ Y) (hAel : IsElemAbelian2 A) (hAcard : Nat.card A = 16) :
    ∃ d ∈ A, ∃ e ∈ A, d ≠ 1 ∧ e ≠ 1 ∧
      L ≤ Subgroup.closure (((Subgroup.centralizer {d} : Subgroup (MulAut W)) :
        Set (MulAut W)) ∪ (Subgroup.centralizer {e} : Subgroup (MulAut W))) := by
  obtain ⟨d₀, hd₀, e₀, he₀, hd₀1, he₀1, hgenP⟩ :=
    j2A_e16_image_pair ψL hAQ hAel hAcard
  exact j2A_pullback_gen_centralizers ψL hAY hd₀ he₀ hd₀1 he₀1 hgenP

theorem w4Thm11_1RowA_J2_holds :
    W4Thm11_1RowA .J2 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨eQ⟩ := hs
  rw [show tableA .J2 = 3 from rfl]
  refine CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty Y 3 ?_
  intro A hA
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hperf : Group.IsPerfect ↥L := hq.1
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have hZ : Subgroup.center ↥L = ⊥ :=
    W4Row.center_eq_bot_of_o2Trivial_of_cover hperf hO2 eQ j2_cover
  obtain ⟨Φ, hΦ⟩ := j2_aut_model
  let ψL : Lift L Y j2R j2P :=
    W4Row.liftOfFstar hLY hF hperf hY eQ hZ j2P_le_R Φ j2EquivC hΦ
  have hAcard : Nat.card A = 16 := j2A_nat_card_eq_sixteen ψL hA
  obtain ⟨d, hdA, e, heA, hd1, he1, hgen⟩ :=
    j2A_exists_gen_centralizers ψL hA.1 (hA.1.trans le_sup_right) hA.2.2.1 hAcard
  have hfixd : fixV (Subgroup.zpowers d) = fixV A :=
    j2A_fixV_zpowers_eq hA hAcard hdA hd1
  have hfixe : fixV (Subgroup.zpowers e) = fixV A :=
    j2A_fixV_zpowers_eq hA hAcard heA he1
  have hd2 : d * d = 1 := by
    simpa [sq] using hA.2.2.1.2 d hdA
  exact hd1 (W4Row.eq_one_of_le_closure_centralizer hW' hLY hLn hF hO2 (hA.1 hdA) hd2
    (hfixd.trans hfixe.symm) hgen)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
