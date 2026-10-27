module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.Quasithin.Vol2.Ch10SecQ6SzB
public import CFSG.CGT.Timmesfeld75.OddCenter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem exists_autQuot {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : BarSituation X S) {A : Subgroup (MulAut X)} (hA : IsElemAbelian 2 A) :
    ∃ A' : Subgroup (MulAut (X ⧸ Subgroup.center X)),
      IsElemAbelian 2 A' ∧ Nat.card A' = Nat.card A := by
  have hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp =>
    le_bot_iff.1 (hS.pCore_eq_bot ▸ CFSG.LieType.BorelTits.le_pCore 2 hN hp)
  have hodd : Odd (Nat.card (Subgroup.center X)) := CFSG.CGT.Timmesfeld75.odd_card_center hO2
  have hconj : ∀ (g x : X), CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x →
      CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (g * x * g⁻¹) := by
    intro g x hx
    refine ⟨fun h => hx.1 ?_, ?_⟩
    · have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [← this, h]
      group
    · have : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
      rw [this, hx.2]
      group
  haveI hnormal : (Subgroup.closure
      {x : X | CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x}).Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hconj g x hx)
    | one => simpa using Subgroup.one_mem _
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  have hgen : Subgroup.closure {x : X | CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x} = ⊤ := by
    rw [eq_top_iff, ← hS.normalClosure_eq_top]
    refine Subgroup.normalClosure_le_normal fun s hs => ?_
    by_cases h1 : s = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨h1, by simpa [pow_two] using hS.elemAbelian.2 s hs⟩
  have hker :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull.characteristic_quotient_ker_eq_bot
      (Subgroup.center X) hodd le_rfl hgen
  have hinj : Function.Injective
      (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient (Subgroup.center X)) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  refine ⟨A.map (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient (Subgroup.center X)),
    ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, Subgroup.card_map_of_injective hinj⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    apply Subtype.ext
    show (x : MulAut (X ⧸ Subgroup.center X)) * y = y * x
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_pow, hA.2 a ha, map_one]

theorem card_le_two_pow_of_isL2Gp {Y : Type} [Group Y] {n : ℕ} (hY : IsL2Gp Y n)
    {A : Subgroup (MulAut Y)} (hA : IsElemAbelian 2 A) : Nat.card A ≤ 2 ^ n := by
  obtain ⟨F, _, hFin, hF, ⟨e⟩⟩ := hY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n :=
    Nat.one_le_iff_ne_zero.2 (Nat.one_lt_two_pow_iff.1 (hF ▸ Finite.one_lt_card))
  haveI : CharP F 2 := by
    classical
    letI : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
  let ψ : MulAut Y ≃* MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.congr e
  have hc : ∀ a ∈ A.map ψ.toMonoidHom, ∀ b ∈ A.map ψ.toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have h2 : ∀ a ∈ A.map ψ.toMonoidHom, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hA.2 a ha, map_one]
  have key := CFSG.Quasithin.Vol2.Ch10.SecD.C10P06.card_le_of_elem_aut (K := F) hF hn
    (F := A.map ψ.toMonoidHom) hc h2
  rw [Subgroup.card_map_of_injective ψ.injective, hF] at key
  exact key

theorem card_le_two_pow_of_isSzGp {Y : Type} [Group Y] {n : ℕ}
    (hY : IsSzGp Y n) {A : Subgroup (MulAut Y)} (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 ^ n := by
  obtain ⟨-, a, ha, F, _, hFin, rfl, hF, ⟨e⟩⟩ := hY
  let ψ : MulAut Y ≃* MulAut ↥(CFSG.Blueprint.suzukiGroup a F) := MulAut.congr e
  have hc : ∀ x ∈ A.map ψ.toMonoidHom, ∀ y ∈ A.map ψ.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have h2 : ∀ x ∈ A.map ψ.toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← pow_two, hA.2 x hx, map_one]
  have key := CFSG.Quasithin.Vol2.Ch10.SecD.C10P06.card_le_of_elem_aut_sz ha hF
    (A := A.map ψ.toMonoidHom) hc h2
  rwa [Subgroup.card_map_of_injective ψ.injective] at key

theorem card_eq_of_suzukiRoot {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : BarSituation X S) (g1 : W3Lem85TwoGap1) {n : ℕ}
    (hX : IsSzGp (X ⧸ Subgroup.center X) n) (hR : IsSuzukiRootGroup X S) :
    Nat.card S = 2 ^ n := by
  obtain ⟨T, hT⟩ := hR
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp =>
    le_bot_iff.1 (hS.pCore_eq_bot ▸ CFSG.LieType.BorelTits.le_pCore 2 hN hp)
  have hodd : Odd (Nat.card (Subgroup.center X)) := CFSG.CGT.Timmesfeld75.odd_card_center hO2
  have hTZ : (T : Subgroup X) ⊓ Subgroup.center X = ⊥ := by
    have h2 : IsPGroup 2 ↥((T : Subgroup X) ⊓ Subgroup.center X) :=
      T.isPGroup'.to_le inf_le_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h2
    have hdvd : Nat.card ↥((T : Subgroup X) ⊓ Subgroup.center X) ∣
        Nat.card (Subgroup.center X) := Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hk0
      have h2d : 2 ∣ Nat.card (Subgroup.center X) := (dvd_pow_self 2 hk0).trans (hk ▸ hdvd)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2d)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hinj : Function.Injective (π.comp (T : Subgroup X).subtype) := by
    intro x y hxy
    have h1 : ((x : X)⁻¹ * y : X) ∈ Subgroup.center X := by
      have := QuotientGroup.eq.1 hxy
      exact this
    have h2 : ((x : X)⁻¹ * y : X) ∈ (T : Subgroup X) := T.mul_mem (T.inv_mem x.2) y.2
    have h3 : ((x : X)⁻¹ * y : X) ∈ (T : Subgroup X) ⊓ Subgroup.center X := ⟨h2, h1⟩
    rw [hTZ, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3
  let T' : Sylow 2 (X ⧸ Subgroup.center X) := T.mapSurjective hπ
  have hT' : (T' : Subgroup (X ⧸ Subgroup.center X)) = (T : Subgroup X).map π := rfl
  let e : ↥(T : Subgroup X) ≃* ↥(T' : Subgroup (X ⧸ Subgroup.center X)) :=
    MulEquiv.ofBijective
      ((π.comp (T : Subgroup X).subtype).codRestrict (T' : Subgroup (X ⧸ Subgroup.center X))
        fun x => ⟨x, x.2, rfl⟩)
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => by
        obtain ⟨x, hx, hxy⟩ := y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  have h1 : Nat.card S = Nat.card (Subgroup.center ↥(T : Subgroup X)) := by
    have hSeq : S = (Subgroup.center ↥(T : Subgroup X)).map (T : Subgroup X).subtype := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · intro hx
        obtain ⟨hxT, hxc⟩ := (hT x).1 hx
        refine ⟨⟨x, hxT⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
        exact Subtype.ext (hxc y y.2).symm
      · rintro ⟨z, hz, rfl⟩
        refine (hT _).2 ⟨z.2, fun y hy => ?_⟩
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz ⟨y, hy⟩).symm)
    rw [hSeq]
    exact Subgroup.card_map_of_injective (T : Subgroup X).subtype_injective
  rw [h1, Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact g1.2 _ n hX T'

end CFSG.LocalAnalysis.WeakClosure81

end
