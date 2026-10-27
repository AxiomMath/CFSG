module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FCentralLift
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianFixedPointFreeLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
public import CFSG.GroupTheory.PCore.SolvableRadical
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Card
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Alpha
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (autBar2 autBar2_apply_mk_coe)

theorem exists_fpf_subgroup_of_abelian_preimage
    {H S A : Type} [Group H] [Finite H] [Group S] [CommGroup A] [Finite A]
    {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (π : H →* S) (hπ : Function.Surjective π)
    (β : MulAut H) (θ : MulAut S) (hβr : β ^ r = 1)
    (hequiv : ∀ x, π (β x) = θ (π x))
    (hAq : IsPGroup q A) (hAc : ¬ IsCyclic A)
    (κ : A →* A) (hκ : ∀ a, κ a = a → a = 1)
    (ι : A →* S) (hι : Function.Injective ι)
    (hθι : ∀ a, θ (ι a) = ι (κ a))
    (hpre : IsMulCommutative ↥(ι.range.comap π)) :
    ∃ P : Subgroup H, IsMulCommutative ↥P ∧ IsPGroup q ↥P ∧ ¬ IsCyclic ↥P ∧
      ∃ γ : ↥P →* ↥P, (∀ x, γ x = x → x = 1) ∧
        ∀ x : ↥P, β (x : H) = (γ x : H) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact r.Prime := ⟨hr⟩
  let E : Subgroup H := ι.range.comap π
  let : IsMulCommutative ↥E := hpre
  have hEβle : E.map β.toMonoidHom ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := hx
    refine ⟨κ a, ?_⟩
    change ι (κ a) = π (β x)
    rw [hequiv, ← ha, hθι]
  have hEβ : E.map β.toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hEβle (by rw [Subgroup.card_map_of_injective β.injective])
  let βE : MulAut ↥E := (β.subgroupMap E).trans (MulEquiv.subgroupCongr hEβ)
  have hβE : ∀ x : ↥E, (βE x : H) = β (x : H) := fun _ => rfl
  let eA : A ≃* ↥ι.range := MulEquiv.ofBijective ι.rangeRestrict
    ⟨fun a a' h => hι (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  let f : ↥E →* A := eA.symm.toMonoidHom.comp
    ((π.comp E.subtype).codRestrict ι.range fun x => x.2)
  have hfπ : ∀ x : ↥E, ι (f x) = π (x : H) := fun x =>
    congrArg Subtype.val (eA.apply_symm_apply _)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x, hx⟩ := hπ (ι a)
    refine ⟨⟨x, ⟨a, hx.symm⟩⟩, ?_⟩
    apply hι
    rw [hfπ]
    exact hx
  have hfβ : ∀ x : ↥E, f (βE x) = κ (f x) := by
    intro x
    apply hι
    rw [hfπ, hβE, hequiv, ← hfπ, hθι]
  obtain ⟨Q⟩ : Nonempty (Sylow q ↥E) := inferInstance
  have hQchar : (Q : Subgroup ↥E).Characteristic :=
    Sylow.characteristic_of_normal Q (Subgroup.normal_of_comm _)
  have hQβ : (Q : Subgroup ↥E).map βE.toMonoidHom = Q :=
    Subgroup.characteristic_iff_map_eq.1 hQchar βE
  let βQ : MulAut ↥(Q : Subgroup ↥E) :=
    (βE.subgroupMap (Q : Subgroup ↥E)).trans (MulEquiv.subgroupCongr hQβ)
  have hβQ : ∀ x : ↥(Q : Subgroup ↥E), (βQ x : H) = β (x : H) := fun _ => rfl
  let fQ : ↥(Q : Subgroup ↥E) →* A := f.comp (Q : Subgroup ↥E).subtype
  have hfQ : Function.Surjective fQ := by
    intro a
    have htop : ((Q.mapSurjective hf : Sylow q A) : Subgroup A) = ⊤ :=
      ((Q.mapSurjective hf).is_maximal' (hAq.to_subgroup ⊤) le_top).symm
    have ha : a ∈ ((Q.mapSurjective hf : Sylow q A) : Subgroup A) := by
      rw [htop]
      exact mem_top _
    rw [Sylow.coe_mapSurjective] at ha
    obtain ⟨x, hx, hxa⟩ := ha
    exact ⟨⟨x, hx⟩, hxa⟩
  have hfQβ : ∀ x : ↥(Q : Subgroup ↥E), fQ (βQ x) = κ (fQ x) :=
    fun x => hfβ (x : ↥E)
  have hβQr : βQ ^ r = 1 := by
    ext x
    have hpow : ∀ n : ℕ, ∀ y : ↥(Q : Subgroup ↥E),
        ((βQ ^ n) y : H) = (β ^ n) (y : H) := by
      intro n
      induction n with
      | zero => intro y; rfl
      | succ n ih =>
        intro y
        rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ih, hβQ]
    simpa [hβr] using hpow r x
  have hβQ1 : βQ ≠ 1 := by
    intro h1
    have hAone : ∀ a : A, a = 1 := by
      intro a
      obtain ⟨x, rfl⟩ := hfQ a
      apply hκ
      rw [← hfQβ, h1, MulAut.one_apply]
    have : Subsingleton A := ⟨fun a b => (hAone a).trans (hAone b).symm⟩
    exact hAc isCyclic_of_subsingleton
  have hquot : ¬ IsCyclic (↥(Q : Subgroup ↥E) ⧸ fQ.ker) := fun h =>
    hAc ((MulEquiv.isCyclic (QuotientGroup.quotientKerEquivOfSurjective fQ hfQ)).1 h)
  have hfix : ∀ x : ↥(Q : Subgroup ↥E), βQ x = x → x ∈ fQ.ker := by
    intro x hx
    exact MonoidHom.mem_ker.2 (hκ _ ((hfQβ x).symm.trans (congrArg fQ hx)))
  obtain ⟨B, hBβ, hBq, hBc, _, γ, hγ, hβγ⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.AbelianFixedPointFreeLift.exists_invariant_fpf_noncyclic_map_quotient_of_abelian
      (inferInstance : IsMulCommutative ↥(Q : Subgroup ↥E)) Q.isPGroup' fQ.ker βQ
      (orderOf_eq_prime hβQr hβQ1) hr hqr hfix hquot
  let j : ↥B →* H := E.subtype.comp ((Q : Subgroup ↥E).subtype.comp B.subtype)
  have hj : Function.Injective j :=
    E.subtype_injective.comp ((Q : Subgroup ↥E).subtype_injective.comp B.subtype_injective)
  let ej : ↥B ≃* j.range := MulEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => hj (show j x = j y from congrArg (fun z : j.range => (z : H)) h),
      j.rangeRestrict_surjective⟩
  let γ' : ↥j.range →* ↥j.range := ej.toMonoidHom.comp (γ.comp ej.symm.toMonoidHom)
  refine ⟨j.range, ?_, hBq.of_surjective ej.toMonoidHom ej.surjective,
    fun h => hBc ((MulEquiv.isCyclic ej).2 h), γ', ?_, ?_⟩
  · refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    obtain ⟨x', rfl⟩ := ej.surjective x
    obtain ⟨y', rfl⟩ := ej.surjective y
    change j (x' * y') = j (y' * x')
    exact congrArg j (mul_comm' x' y')
  · intro x hx
    obtain ⟨y, rfl⟩ := ej.surjective x
    have hy : γ y = y := ej.injective (by simpa [γ'] using hx)
    simpa using congrArg ej (hγ y hy)
  · intro x
    obtain ⟨y, rfl⟩ := ej.surjective x
    have hγej : γ' (ej y) = ej (γ y) := by simp [γ']
    rw [hγej]
    change β (j y) = j (γ y)
    exact (hβQ (y : ↥(Q : Subgroup ↥E))).symm.trans
      (congrArg (fun z : ↥(Q : Subgroup ↥E) => (z : H)) (hβγ y))

theorem uc22s2114r4f_exists_central_bar2_map
    {G : Type} [Group G] [Finite G] {M L : Subgroup G} (hL : L ∈ calC M) :
    ∃ π : Bar2 L →* BarInf L, Function.Surjective π ∧ π.ker ≤ center (Bar2 L) ∧
      ∀ (b : G) (hb : b ∈ normalizer (L : Set G)) (x : Bar2 L),
        π (autBar2 (L := L) (N := ⊤) ⟨b, ⟨trivial, hb⟩⟩ x) =
          inducedBarInfAutHom L ⟨b, hb⟩ (π x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : Bar2 L →* BarInf L := QuotientGroup.map (CFSG.pCore 2 ↥L)
    (CFSG.solvableRadical ↥L) (MonoidHom.id ↥L) (CFSG.pCore_le_solvableRadical 2 ↥L)
  have hπmk : ∀ x : ↥L, π (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) =
      QuotientGroup.mk' (CFSG.solvableRadical ↥L) x := fun _ => rfl
  refine ⟨π, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L) y
    exact ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥L) x, hπmk x⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
    have hx : x ∈ CFSG.solvableRadical ↥L := by
      apply (QuotientGroup.eq_one_iff x).1
      exact hy
    rw [← uc22p21k_map_solvableRadical_eq_center hL.2.2]
    exact mem_map_of_mem _ hx
  · intro b hb y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
    change π (autBar2 (L := L) (N := ⊤) ⟨b, ⟨mem_top b, hb⟩⟩
      (QuotientGroup.mk x)) =
        inducedBarInfAutHom L ⟨b, hb⟩ (π (QuotientGroup.mk x))
    rw [autBar2_apply_mk_coe]
    rfl

theorem uc22s2114r4f_false_of_abelian_preimage
    {G : Type} [Group G] [Finite G] {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h74 : F07.R74Card D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    {b : G} (hbB : b ∈ c.B0) (hbL : b ∈ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig)
    {X : Subgroup (BarInf L)} (hXp : IsPGroup p ↥X) (hXc : ¬ IsCyclic ↥X)
    (hXfix : ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x)
    (π : Bar2 L →* BarInf L) (hπ : Function.Surjective π)
    (hequiv : ∀ x, π (autBar2 (L := L) (N := ⊤) ⟨b, ⟨trivial, hbL⟩⟩ x) =
      inducedBarInfAutHom L ⟨b, hbL⟩ (π x))
    {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) (hqr : q ≠ r)
    {A : Type} [CommGroup A] [Finite A] (hAq : IsPGroup q A) (hAc : ¬ IsCyclic A)
    (κ : A →* A) (hκ : ∀ a, κ a = a → a = 1)
    (ι : A →* BarInf L) (hι : Function.Injective ι)
    (hθι : ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a))
    (hpre : IsMulCommutative ↥(ι.range.comap π)) : False := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact r.Prime := ⟨hr⟩
  let β := autBar2 (L := L) (N := ⊤) ⟨b, ⟨trivial, hbL⟩⟩
  have hβr : β ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, ⟨trivial, hbL⟩⟩ : ↥(⊤ ⊓ normalizer (L : Set G))) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  obtain ⟨P, hPcomm, hPq, hPc, γ, hγ, hβγ⟩ :=
    exists_fpf_subgroup_of_abelian_preimage hq hr hqr π hπ β
      (inducedBarInfAutHom L ⟨b, hbL⟩) hβr hequiv hAq hAc κ hκ ι hι hθι hpre
  let hPcgroup : CommGroup ↥P :=
    { toGroup := inferInstance, mul_comm := hPcomm.is_comm.comm }
  obtain ⟨ψ, hψ, hψL, hbψ⟩ := uc22s2114r4f_exists_lift_bar2 hbL hr (by omega) hbr
    (by omega) hPq P.subtype P.subtype_injective γ hβγ
  have hN := uc22s2112r2_normalizer hH c hL.1.le hbB (by rw [hbr]; exact hr)
  have : Fact p.Prime := ⟨hp⟩
  have hbP : IsPGroup r ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbr, pow_one])
  have hC := uc22s2114r3f_two_le_pRank_centralizer (zpowers_le.2 hbL) hbP hrK hp2 hXp hXc
    (uc22s2114r3f_fix_zpowers hbL hXfix)
  have hpN : 1 < CFSG.Open.pRank p (normalizer ((zpowers b : Subgroup G) : Set G) ⊓ D.M) := by
    have := hC.trans (CFSG.SectionRank.pRank_mono hp.one_lt ((inf_le_inf_left L
      (centralizer_le (Set.singleton_subset_iff.2 (mem_zpowers b)))).trans hN.2.2.2))
    omega
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hpσ
  have h74b := h74 p _ ⟨hp, hp2, hsp, hN.1, hN.2.1, hpN⟩
  have h2 := @uc22s2114r3f_two_lt_card G _ _ D q r hq (by omega) hr (by omega) hqr
    (↥P) hPcgroup (by infer_instance) hPq hPc γ hγ ψ hψ
    (fun a => hL.1.le (hψL a)) b (c.hBM hbB) hbr hbψ
  have hle := Subgroup.card_le_of_le (inf_le_inf_left (F07.Q7 D) hN.2.2.1)
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
