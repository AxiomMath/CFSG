module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelMono
public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitGL
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private lemma s16n9b_case4_aut_stab_of_map_eq {W : Subgroup T} {φ : MulAut T}
    (h : W.map φ.toMonoidHom = W) : φ ∈ stabSub W := by
  intro u
  constructor
  · intro hu
    have hu' : φ u ∈ W.map φ.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := φ.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : φ u ∈ W.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [h] at hu'
    exact hu'

private lemma s16n9b_case4_aut_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private lemma s16n9b_case4_aut_dParam_seven : dParam 7 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private lemma s16n9b_case4_aut_two_pow_dParam {p : ℕ} (hp : p = 3 ∨ p = 7) :
    2 ^ dParam p = p + 1 := by
  rcases hp with rfl | rfl
  · rw [s16n9b_case4_aut_dParam_three]; norm_num
  · rw [s16n9b_case4_aut_dParam_seven]; norm_num

theorem s16n9b_case4_aut_index_le {p : ℕ} (hp : p = 3 ∨ p = 7) (hT : ∀ t : T, t ^ 2 = 1)
    {Y : Subgroup T} (hY : rk ↥Y = dParam p) {F : Subgroup (MulAut T)} (hF : IsElemAbelian p F)
    (hFY : ∀ f ∈ F, Y.map f.toMonoidHom = Y) :
    Nat.card F ≤ p * Nat.card ↥(F ⊓ centSub Y) := by
  classical
  haveI : Fintype ↥Y := Fintype.ofFinite ↥Y
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hcardY : Nat.card ↥Y = p + 1 := by
    rw [card_eq_two_pow hT Y, hY, s16n9b_case4_aut_two_pow_dParam hp]
  have hFY' : F ≤ stabSub Y := fun f hf => s16n9b_case4_aut_stab_of_map_eq (hFY f hf)
  have hle : Nat.card (autSub F Y) ≤ p := by
    let S : Set ↥Y := {y | y ≠ 1}
    have hcardS : Fintype.card S = p - 1 + 1 := by
      show Fintype.card {y : ↥Y // y ≠ 1} = p - 1 + 1
      rw [Fintype.card_subtype_compl (fun y : ↥Y => y = 1),
        Fintype.card_subtype_eq (1 : ↥Y), Fintype.card_eq_nat_card, hcardY]
      omega
    let eS : S ≃ Fin (p - 1 + 1) := Fintype.equivFinOfCardEq hcardS
    let ρ : MulAut ↥Y →* Equiv.Perm S :=
      { toFun := fun g => Equiv.Perm.subtypePerm (g : ↥Y ≃ ↥Y) (fun y => by
          have hy1 : g y = 1 ↔ y = 1 := by
            calc g y = 1 ↔ g y = g 1 := by rw [map_one]
              _ ↔ y = 1 := g.injective.eq_iff
          exact not_congr hy1)
        map_one' := Equiv.ext (fun x => Subtype.ext rfl)
        map_mul' := by intro g h; exact Equiv.ext (fun x => Subtype.ext rfl) }
    have hρinj : Function.Injective ρ := by
      intro g h hgh
      ext y
      by_cases hy : y = 1
      · simp [hy]
      · have h2 := congrArg (fun (σ : Equiv.Perm S) => ((σ ⟨y, hy⟩ : S) : ↥Y)) hgh
        dsimp only [ρ] at h2
        simpa using h2
    let eρ : Equiv.Perm S ≃* Equiv.Perm (Fin (p - 1 + 1)) := eS.permCongrHom
    let H : Subgroup (Equiv.Perm (Fin (p - 1 + 1))) :=
      (autSub F Y).map (eρ.toMonoidHom.comp ρ)
    have hHcard : Nat.card H = Nat.card (autSub F Y) := by
      show Nat.card ((autSub F Y).map (eρ.toMonoidHom.comp ρ)) = Nat.card (autSub F Y)
      exact Subgroup.card_map_of_injective (eρ.injective.comp hρinj)
    have hFstab : IsPGroup p ↥(F.subgroupOf (stabSub Y)) := by
      obtain ⟨n, hn⟩ := (IsElemAbelian.isPGroup hF).exists_card_dvd_pow
      refine IsPGroup.of_card_dvd_pow (n := n) ?_
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFY').toEquiv]
    have hHp : IsPGroup p H :=
      (hFstab.map (resHom Y)).map (eρ.toMonoidHom.comp ρ)
    have hbound : Nat.card H ≤ p :=
      CFSG.StandardType.LinModel.card_le_of_isPGroup_perm hprime (m := p - 1)
        (by have := hprime.two_le; omega) hHp
    rwa [hHcard] at hbound
  have hcardF : Nat.card F = Nat.card (autSub F Y) * Nat.card ↥(F ⊓ centSub Y) :=
    (card_autSub_mul hFY').symm
  rw [hcardF]
  exact Nat.mul_le_mul_right _ hle

theorem s16n9b_case4_aut_supp {p n : ℕ} (hp : p = 3 ∨ p = 7) (hT : ∀ t : T, t ^ 2 = 1)
    {F : Subgroup (MulAut T)} (hF : IsElemAbelian p F) (hn : p ^ n ≤ Nat.card F) {ι : Type}
    (Y : ι → Subgroup T) (S : Finset ι) (hY : ∀ i ∈ S, rk ↥(Y i) = dParam p)
    (hFY : ∀ i ∈ S, ∀ f ∈ F, (Y i).map f.toMonoidHom = Y i) (hS : S.card < n) :
    ∃ ψ ∈ F, orderOf ψ = p ∧ ∀ i ∈ S, ∀ y ∈ Y i, ψ y = y := by
  classical
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have claim : ∀ (S : Finset ι), (∀ i ∈ S, rk ↥(Y i) = dParam p) →
      (∀ i ∈ S, ∀ f ∈ F, (Y i).map f.toMonoidHom = Y i) →
      ∃ F' : Subgroup (MulAut T), F' ≤ F ∧
        (∀ i ∈ S, ∀ f ∈ F', ∀ y ∈ Y i, f y = y) ∧
        Nat.card F ≤ p ^ S.card * Nat.card F' := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _ _
      exact ⟨F, le_rfl, by simp, by simp⟩
    · intro j S hj ih hY' hFY'
      obtain ⟨F', hF'le, hF'fix, hF'card⟩ := ih
        (fun i hi => hY' i (Finset.mem_insert_of_mem hi))
        (fun i hi => hFY' i (Finset.mem_insert_of_mem hi))
      have hYj : rk ↥(Y j) = dParam p := hY' j (Finset.mem_insert_self j S)
      have hF'ea : IsElemAbelian p F' := IsElemAbelian.mono hF hF'le
      have hF'Yj : ∀ f ∈ F', (Y j).map f.toMonoidHom = Y j :=
        fun f hf => hFY' j (Finset.mem_insert_self j S) f (hF'le hf)
      have hidx := s16n9b_case4_aut_index_le hp hT hYj hF'ea hF'Yj
      refine ⟨F' ⊓ centSub (Y j), inf_le_left.trans hF'le, ?_, ?_⟩
      · intro i hi f hf y hy
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact (mem_centSub.mp hf.2) y hy
        · exact hF'fix i hi f hf.1 y hy
      · rw [Finset.card_insert_of_notMem hj]
        calc Nat.card F ≤ p ^ S.card * Nat.card F' := hF'card
          _ ≤ p ^ S.card * (p * Nat.card ↥(F' ⊓ centSub (Y j))) :=
              Nat.mul_le_mul_left _ hidx
          _ = p ^ (S.card + 1) * Nat.card ↥(F' ⊓ centSub (Y j)) := by ring
  obtain ⟨F', hF'le, hF'fix, hF'card⟩ := claim S hY hFY
  have hpn : p ^ (S.card + 1) ≤ p ^ S.card * Nat.card F' :=
    (Nat.pow_le_pow_right (by have := hprime.two_le; omega) (by omega : S.card + 1 ≤ n)).trans
      (hn.trans hF'card)
  have hp_le : p ≤ Nat.card F' := by
    have hpos : 0 < p ^ S.card := pow_pos (by have := hprime.two_le; omega) _
    rw [pow_succ] at hpn
    exact Nat.le_of_mul_le_mul_left hpn hpos
  have hne : F' ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card F' = 1 := by rw [hbot]; simp
    have := hprime.two_le
    omega
  obtain ⟨ψ, hψne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨ψ.1, hF'le ψ.2, ?_, fun i hi y hy => hF'fix i hi ψ.1 ψ.2 y hy⟩
  haveI : Fact p.Prime := ⟨hprime⟩
  exact orderOf_eq_prime (hF.2 ψ.1 (hF'le ψ.2)) (fun h => hψne (Subtype.ext h))

theorem s16n9b_case4_aut_norm7 (hT : ∀ t : T, t ^ 2 = 1) {Y : Subgroup T} (hY : rk ↥Y = 3)
    {Q : Subgroup (MulAut T)} (hQ : IsPGroup 7 ↥Q) (hQY : ∀ q ∈ Q, Y.map q.toMonoidHom = Y)
    {φ : MulAut T} (hφ : ∃ a : ℕ, orderOf φ = 2 ^ a) (hφY : Y.map φ.toMonoidHom = Y)
    (hφQ : Q.map (MulAut.conj φ).toMonoidHom = Q) (hφ1 : ∃ y ∈ Y, φ y ≠ y) :
    ∀ q ∈ Q, ∀ y ∈ Y, q y = y := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨q, hqQ, y, hyY, hqy⟩ := hcon
  have hQY' : Q ≤ stabSub Y := fun q hq => s16n9b_case4_aut_stab_of_map_eq (hQY q hq)
  have hφY' : φ ∈ stabSub Y := s16n9b_case4_aut_stab_of_map_eq hφY
  have hcardY : Nat.card ↥Y = 8 := by
    rw [card_eq_two_pow hT Y, hY]; norm_num
  have h2Y : ∀ v : ↥Y, v * v = 1 := by
    intro v
    apply Subtype.ext
    show (v : T) * (v : T) = 1
    rw [← pow_two]
    exact hT v.1
  obtain ⟨e⟩ := CFSG.OddStandard.ChengHeld.GL32Inv.mulAut_mulEquiv_GL3 hcardY h2Y
  have hcardMulAut : Nat.card (MulAut ↥Y) = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.ComponentClassification.GHarris.card_GL32_gh
  let Qb : Subgroup (MulAut ↥Y) := autSub Q Y
  have hqb_ne : resHom Y ⟨q, hQY' hqQ⟩ ≠ 1 := by
    intro h1
    have h2 := congrArg (fun (σ : MulAut ↥Y) => ((σ ⟨y, hyY⟩ : ↥Y) : T)) h1
    simp only [MulAut.one_apply] at h2
    rw [resHom_apply] at h2
    exact hqy h2
  have hQb_ne : Qb ≠ ⊥ := by
    intro hbot
    have hmem : resHom Y ⟨q, hQY' hqQ⟩ ∈ Qb :=
      mem_autSub.mpr ⟨⟨q, hQY' hqQ⟩, hqQ, rfl⟩
    rw [hbot] at hmem
    exact hqb_ne (Subgroup.mem_bot.mp hmem)
  have hQb_dvd : Nat.card Qb ∣ Nat.card Q := by
    show Nat.card (autSub Q Y) ∣ Nat.card Q
    rw [← card_autSub_mul hQY']
    exact dvd_mul_right _ _
  obtain ⟨m, hm⟩ := hQ.exists_card_dvd_pow
  have hQb_pgroup : IsPGroup 7 ↥Qb :=
    IsPGroup.of_card_dvd_pow (n := m) (hQb_dvd.trans hm)
  have hQb_card : Nat.card Qb = 7 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 7)).mp hQb_pgroup
    have hkpos : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      exact hQb_ne (Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero]))
    have hk1 : k = 1 := by
      have hdvd168 : 7 ^ k ∣ 168 := by
        rw [← hk]
        have h := Subgroup.card_subgroup_dvd_card Qb
        rwa [hcardMulAut] at h
      have hle : k ≤ 1 := by
        by_contra h
        have hk2 : 2 ≤ k := by omega
        exact (by norm_num : ¬ (7 ^ 2 ∣ 168)) ((pow_dvd_pow 7 hk2).trans hdvd168)
      omega
    rw [hk, hk1, pow_one]
  let P : Subgroup (GL (Fin 3) (ZMod 2)) := Qb.map e.toMonoidHom
  have hPcard : Nat.card P = 7 := by
    show Nat.card (Qb.map e.toMonoidHom) = 7
    rw [Subgroup.card_map_of_injective e.injective, hQb_card]
  have hNcard : Nat.card (normalizer (P : Set (GL (Fin 3) (ZMod 2)))) = 21 :=
    CFSG.ComponentClassification.GMS78.card_normalizer_eq_of_card_eq_seven_GL32 hPcard
  let φb : MulAut ↥Y := resHom Y ⟨φ, hφY'⟩
  have hQb_conj : Qb.map (MulAut.conj φb).toMonoidHom = Qb := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro x ⟨z, hz, rfl⟩
      obtain ⟨g, hgQ, hgq⟩ := mem_autSub.mp hz
      rw [← hgq]
      have hconjQ : MulAut.conj φ (g : MulAut T) ∈ Q := by
        have hmem : MulAut.conj φ (g : MulAut T) ∈ Q.map (MulAut.conj φ).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨(g : MulAut T), hgQ, rfl⟩
        rwa [hφQ] at hmem
      have hstab : MulAut.conj φ (g : MulAut T) ∈ stabSub Y := by
        rw [MulAut.conj_apply]
        exact (stabSub Y).mul_mem ((stabSub Y).mul_mem hφY' g.2) ((stabSub Y).inv_mem hφY')
      have hg_eq : (⟨MulAut.conj φ (g : MulAut T), hstab⟩ : stabSub Y) =
          ⟨φ, hφY'⟩ * g * ⟨φ, hφY'⟩⁻¹ := by
        apply Subtype.ext
        show MulAut.conj φ (g : MulAut T) = φ * (g : MulAut T) * φ⁻¹
        rw [MulAut.conj_apply]
      have hres : (MulAut.conj φb).toMonoidHom (resHom Y g) =
          resHom Y ⟨MulAut.conj φ (g : MulAut T), hstab⟩ := by
        show MulAut.conj φb (resHom Y g) =
          resHom Y ⟨MulAut.conj φ (g : MulAut T), hstab⟩
        rw [hg_eq, MulAut.conj_apply, show φb = resHom Y ⟨φ, hφY'⟩ from rfl,
          map_mul, map_mul, map_inv]
      rw [hres]
      exact mem_autSub.mpr ⟨⟨MulAut.conj φ (g : MulAut T), hstab⟩, hconjQ, rfl⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj φb).injective]
  have hφb_norm : e φb ∈ normalizer (P : Set (GL (Fin 3) (ZMod 2))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (Qb.map e.toMonoidHom).map (MulAut.conj (e φb)).toMonoidHom =
      Qb.map e.toMonoidHom
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj (e φb)).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp (MulAut.conj φb).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        map_mul, map_inv]
    rw [hcomp, ← Subgroup.map_map, hQb_conj]
  have horder21 : orderOf (e φb) ∣ 21 := by
    rw [← hNcard]
    exact Subgroup.orderOf_dvd_natCard (normalizer (P : Set (GL (Fin 3) (ZMod 2)))) hφb_norm
  obtain ⟨a, ha⟩ := hφ
  have horder2 : orderOf (e φb) ∣ 2 ^ a := by
    have h1 : orderOf φb ∣ orderOf φ := by
      have h := orderOf_map_dvd (resHom Y) ⟨φ, hφY'⟩
      rwa [Subgroup.orderOf_mk] at h
    have h2 : orderOf (e φb) ∣ orderOf φb := orderOf_map_dvd e.toMonoidHom φb
    have h3 : orderOf φb ∣ 2 ^ a := by rw [← ha]; exact h1
    exact h2.trans h3
  have hcop : Nat.Coprime 21 (2 ^ a) := (by norm_num : Nat.Coprime 21 2).pow_right a
  have hg1 : orderOf (e φb) = 1 := by
    have hdvd : orderOf (e φb) ∣ Nat.gcd 21 (2 ^ a) := Nat.dvd_gcd horder21 horder2
    rw [hcop.gcd_eq_one] at hdvd
    exact Nat.dvd_one.mp hdvd
  have he1 : e φb = 1 := orderOf_eq_one_iff.mp hg1
  have hφb1 : φb = 1 := e.injective (by rw [he1, map_one])
  obtain ⟨y0, hy0Y, hφy0⟩ := hφ1
  have hval : ((resHom Y ⟨φ, hφY'⟩ ⟨y0, hy0Y⟩ : ↥Y) : T) = φ y0 :=
    resHom_apply Y ⟨φ, hφY'⟩ ⟨y0, hy0Y⟩
  have hval0 : ((resHom Y ⟨φ, hφY'⟩ ⟨y0, hy0Y⟩ : ↥Y) : T) = y0 := by
    rw [show resHom Y ⟨φ, hφY'⟩ = 1 from hφb1]
    rfl
  rw [hval] at hval0
  exact hφy0 hval0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
