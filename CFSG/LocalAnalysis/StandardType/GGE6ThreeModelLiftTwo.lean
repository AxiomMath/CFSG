module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelBody
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.StandardType.U63TB

variable {R : Type} [Group R] {L' : Type} [Group L'] [Finite L']

private lemma twoSub_eq_one_of_odd {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (hN : N ≤ Subgroup.center G) {z : G}
    (hz : z ∈ twoSub N hN) (hodd : Odd (orderOf z)) : z = 1 := by
  rw [mem_twoSub] at hz
  have hdvd : orderOf z ∣ 2 ^ Nat.card G := orderOf_dvd_of_pow_eq_one hz.2
  have hcop : Nat.Coprime (orderOf z) (2 ^ Nat.card G) :=
    (hodd.coprime_two_right).pow_right (Nat.card G)
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd)

private lemma twoSub_eq_one_of_odd_pow {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (hN : N ≤ Subgroup.center G) {z : G} {m : ℕ}
    (hz : z ∈ twoSub N hN) (hm : Odd m) (hzm : z ^ m = 1) : z = 1 :=
  twoSub_eq_one_of_odd hN hz (hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hzm))

private lemma odd_orderOf_mul_of_commute {G : Type} [Group G] {s t : G}
    (h : Commute s t) (hs : Odd (orderOf s)) (ht : Odd (orderOf t)) :
    Odd (orderOf (s * t)) :=
  (Nat.odd_mul.mpr ⟨hs, ht⟩).of_dvd_nat h.orderOf_mul_dvd_mul_orderOf

theorem model_descent {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : ψ.ker = Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAle : A ≤ presZ (twoSub ψ.ker hker))
    (hbar : ModelOdd (psi1 hker).ker (redSub hker hAle).range) :
    GGE6ThreeWeylModel ψ.ker A := by
  classical
  let Z2 : Subgroup L' := twoSub ψ.ker hker
  haveI : Z2.Normal := twoSub_normal hker
  haveI : Finite (MulAut (L' ⧸ Z2)) :=
    Finite.of_injective (fun φ : MulAut (L' ⧸ Z2) => (φ : L' ⧸ Z2 → L' ⧸ Z2))
      DFunLike.coe_injective
  obtain ⟨Φb, Tb, wb, hBody, hTbodd⟩ := hbar
  obtain ⟨hΦbinj, hΦbrange, hComm, hZodd, hFix, hNorm, hCob, hAct, hInn, hAut10, hAut11, hOdd12⟩ :=
    hBody
  let Φ : A →* Multiplicative (Fin 6 → ZMod 3) := Φb.comp (redSub hker hAle).rangeRestrict
  have hΦ_apply : ∀ a : A, Φ a = Φb ⟨redSub hker hAle a, ⟨a, rfl⟩⟩ := fun _ => rfl
  have hInj : Function.Injective Φ := by
    intro a b hab
    apply redSub_injective hker hAle hperf
    exact congrArg Subtype.val (hΦbinj hab)
  have hRange : Φ.range = Φb.range := by
    rw [show Φ = Φb.comp (redSub hker hAle).rangeRestrict from rfl]
    rw [← MonoidHom.map_range Φb (redSub hker hAle).rangeRestrict]
    rw [MonoidHom.range_eq_top_of_surjective _ (MonoidHom.rangeRestrict_surjective _)]
    exact (MonoidHom.range_eq_map Φb).symm
  have hRange' : Φ.range = ⊤ ∨
      ∀ x : Fin 6 → ZMod 3, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6 := by
    rcases hΦbrange with h | h
    · exact Or.inl (by rw [hRange, h])
    · exact Or.inr (fun x => by rw [hRange]; exact h x)
  have hPcomm : ∀ s t : L', (s : L' ⧸ Z2) ∈ Tb → (t : L' ⧸ Z2) ∈ Tb →
      Odd (orderOf t) → s * t = t * s := by
    intro s t hs ht htodd
    have hst : (s : L' ⧸ Z2) * (t : L' ⧸ Z2) = (t : L' ⧸ Z2) * (s : L' ⧸ Z2) :=
      hComm _ hs _ ht
    have hc : s * t * s⁻¹ * t⁻¹ ∈ Z2 := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hst]
      group
    have hct : Commute (s * t * s⁻¹ * t⁻¹) t :=
      (commute_iff_eq _ _).mpr ((Subgroup.mem_center_iff.mp (twoSub_le_center hker hc) t).symm)
    have h1 : (s * t * s⁻¹) ^ orderOf t = 1 := by
      rw [show s * t * s⁻¹ = (MulAut.conj s) t from (MulAut.conj_apply s t).symm, ← map_pow,
        pow_orderOf_eq_one, map_one]
    have h2 : (s * t * s⁻¹ * t⁻¹) * t = s * t * s⁻¹ := by group
    have hcm : (s * t * s⁻¹ * t⁻¹) ^ orderOf t = 1 := by
      have hmul : ((s * t * s⁻¹ * t⁻¹) * t) ^ orderOf t =
          (s * t * s⁻¹ * t⁻¹) ^ orderOf t := by
        rw [hct.mul_pow, pow_orderOf_eq_one, mul_one]
      rw [← hmul, h2, h1]
    have hc1 : s * t * s⁻¹ * t⁻¹ = 1 := twoSub_eq_one_of_odd_pow hker hc htodd hcm
    have hconj : s * t * s⁻¹ = t := by rw [← h2, hc1, one_mul]
    have := congrArg (fun x => x * s) hconj
    simpa using this
  let S : Subgroup L' :=
    { carrier := {x | (x : L' ⧸ Z2) ∈ Tb ∧ Odd (orderOf x)}
      one_mem' := ⟨by rw [QuotientGroup.mk_one]; exact Tb.one_mem, by rw [orderOf_one]; decide⟩
      mul_mem' := by
        rintro s t ⟨hs, hso⟩ ⟨ht, hto⟩
        refine ⟨?_, ?_⟩
        · rw [QuotientGroup.mk_mul]; exact Tb.mul_mem hs ht
        · exact odd_orderOf_mul_of_commute ((commute_iff_eq _ _).mpr (hPcomm s t hs ht hto)) hso hto
      inv_mem' := by
        rintro s ⟨hs, hso⟩
        refine ⟨?_, ?_⟩
        · rw [QuotientGroup.mk_inv]; exact Tb.inv_mem hs
        · rwa [orderOf_inv] }
  have hSmem : ∀ x, x ∈ S ↔ (x : L' ⧸ Z2) ∈ Tb ∧ Odd (orderOf x) := fun _ => Iff.rfl
  have hSbot : ∀ x ∈ S, x ∈ Z2 → x = 1 := by
    intro x hx hxz
    exact twoSub_eq_one_of_odd hker hxz ((hSmem x).mp hx).2
  have hlift : ∀ tb ∈ Tb, ∃ t ∈ S, (t : L' ⧸ Z2) = tb := by
    intro tb htb
    have hrodd : Odd (orderOf tb) := hTbodd tb htb
    obtain ⟨t0, ht0⟩ := QuotientGroup.mk_surjective tb
    by_cases hr : orderOf tb = 1
    · refine ⟨1, S.one_mem, ?_⟩
      rw [show tb = 1 from orderOf_eq_one_iff.mp hr, QuotientGroup.mk_one]
    · have hne0 : orderOf tb ≠ 0 := by
        intro h0
        rw [h0] at hrodd
        obtain ⟨k, hk⟩ := hrodd
        omega
      have hr1 : 1 < orderOf tb := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hne0, hr⟩
      have hcop : Nat.Coprime (2 ^ Nat.card L') (orderOf tb) :=
        hrodd.coprime_two_left.pow_left (Nat.card L')
      obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr1
      have hpow : tb ^ (2 ^ Nat.card L' * u) = tb := by
        rw [← pow_mod_orderOf tb (2 ^ Nat.card L' * u), hu, pow_one]
      refine ⟨t0 ^ (2 ^ Nat.card L' * u), (hSmem _).mpr ⟨?_, ?_⟩, ?_⟩
      · rw [QuotientGroup.mk_pow, ht0, hpow]; exact htb
      · have ht0r : (t0 ^ orderOf tb) ^ (2 ^ Nat.card L') = 1 := by
          have hz : t0 ^ orderOf tb ∈ Z2 := by
            rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ht0, pow_orderOf_eq_one]
          exact ((mem_twoSub hker).mp hz).2
        have htpow : (t0 ^ (2 ^ Nat.card L' * u)) ^ orderOf tb = 1 := by
          rw [← pow_mul, show (2 ^ Nat.card L' * u) * orderOf tb =
              (2 ^ Nat.card L' * orderOf tb) * u by ring, pow_mul,
            show 2 ^ Nat.card L' * orderOf tb = orderOf tb * 2 ^ Nat.card L' by ring,
            pow_mul, ht0r, one_pow]
        exact hrodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one htpow)
      · rw [QuotientGroup.mk_pow, ht0, hpow]
  have hex : ∀ i : Fin 6, ∃ n : L', (n : L' ⧸ Z2) = wb i ∧
      ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹ := by
    intro i
    exact exists_lift_W hker hA hAle (fun a₁ ha₁ =>
      ⟨(hCob i a₁ ha₁).2, fun a₁' ha₁' => hFix a₁' ha₁' _ (hCob i a₁ ha₁).1⟩)
  choose w hw using hex
  have hnorm_quot : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      MulAut.conj (n : L' ⧸ Z2) ∈
        Subgroup.normalizer (((redSub hker hAle).range : Subgroup (MulAut (L' ⧸ Z2))) :
          Set (MulAut (L' ⧸ Z2))) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype (fun x hx => ?_)
    obtain ⟨a, rfl⟩ := hx
    have hmem : MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hn a.1).mp a.2
    exact ⟨⟨_, hmem⟩, redSub_conj_triple hker hAle n a hmem⟩
  have hCommS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    exact hPcomm s t ((hSmem s).mp hs).1 ((hSmem t).mp ht).1 ((hSmem t).mp ht).2
  have hZoddS : ∀ z ∈ ψ.ker, Odd (orderOf z) → z ∈ S := by
    intro z hz hzo
    refine (hSmem z).mpr ⟨?_, hzo⟩
    have hzq : (z : L' ⧸ Z2) ∈ (psi1 hker).ker := (mem_ker_psi1 hker).mpr hz
    have hdvd : orderOf (z : L' ⧸ Z2) ∣ orderOf z := by
      simpa [QuotientGroup.mk'_apply] using orderOf_map_dvd (QuotientGroup.mk' Z2) z
    exact hZodd _ hzq (hzo.of_dvd_nat hdvd)
  have hFixS : ∀ a ∈ A, ∀ t ∈ S, a t = t := by
    intro a ha t ht
    have hatq : ((a : MulAut L') t : L' ⧸ Z2) = (t : L' ⧸ Z2) := by
      rw [← redSub_mk hker hAle ⟨a, ha⟩ t]
      exact hFix (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ (t : L' ⧸ Z2)
        ((hSmem t).mp ht).1
    have hatS : (a : MulAut L') t ∈ S := by
      refine (hSmem _).mpr ⟨?_, ?_⟩
      · rw [hatq]; exact ((hSmem t).mp ht).1
      · rw [show orderOf ((a : MulAut L') t) = orderOf t from
          MulEquiv.orderOf_eq (a : MulAut L') t]
        exact ((hSmem t).mp ht).2
    have hz : (a : MulAut L') t * t⁻¹ ∈ Z2 := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hatq, mul_inv_cancel]
    have hz1 : (a : MulAut L') t * t⁻¹ = 1 :=
      hSbot _ (S.mul_mem hatS (S.inv_mem ht)) hz
    have := congrArg (fun x => x * t) hz1
    simpa using this
  have hNormS : ∀ i, ∀ t ∈ S, w i * t * (w i)⁻¹ ∈ S := by
    intro i t ht
    refine (hSmem _).mpr ⟨?_, ?_⟩
    · have h1 : ((w i * t * (w i)⁻¹ : L') : L' ⧸ Z2) =
          wb i * (t : L' ⧸ Z2) * (wb i)⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, (hw i).1]
      rw [h1]; exact hNorm i _ ((hSmem t).mp ht).1
    · rw [show orderOf (w i * t * (w i)⁻¹) = orderOf t from
        MulEquiv.orderOf_eq (MulAut.conj (w i)) t]
      exact ((hSmem t).mp ht).2
  have hCobS : ∀ i, ∀ a ∈ A, w i * (a (w i))⁻¹ ∈ S ∧ (w i * (a (w i))⁻¹) ^ 3 = 1 := by
    intro i a ha
    have hcube : (w i * (a (w i))⁻¹) ^ 3 = 1 := ((hw i).2 a ha).1
    refine ⟨(hSmem _).mpr ⟨?_, ?_⟩, hcube⟩
    · have haq : ((a (w i) : L') : L' ⧸ Z2) = redSub hker hAle ⟨a, ha⟩ (wb i) := by
        rw [← (hw i).1]
        exact (redSub_mk hker hAle ⟨a, ha⟩ (w i)).symm
      have h1 : ((w i * (a (w i))⁻¹ : L') : L' ⧸ Z2) =
          wb i * (redSub hker hAle ⟨a, ha⟩ (wb i))⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (hw i).1, haq]
      rw [h1]
      exact (hCob i (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).1
    · exact (show Odd 3 by decide).of_dvd_nat (orderOf_dvd_of_pow_eq_one hcube)
  have hActS : ∀ i (a : A), ∃ b : A,
      MulAut.conj (w i) * (a : MulAut L') * (MulAut.conj (w i))⁻¹ = b ∧
        Multiplicative.toAdd (Φ b) = adRefl .E6 3 i (Multiplicative.toAdd (Φ a)) := by
    intro i a
    obtain ⟨bb, hbb1, hbb2⟩ := hAct i ⟨redSub hker hAle a, ⟨a, rfl⟩⟩
    obtain ⟨b, hb⟩ := bb.2
    have hbb' : redHom Z2 ⟨b.1, hAle b.2⟩ = (bb : MulAut (L' ⧸ Z2)) :=
      (redSub_eq hker hAle b) ▸ hb
    have hcong : (conjP Z2 (w i) * ⟨a.1, hAle a.2⟩ * (conjP Z2 (w i))⁻¹ : presZ Z2) =
        ⟨b.1, hAle b.2⟩ := by
      apply redHom_injective Z2 (twoSub_le_center hker) hperf
      rw [map_mul, map_mul, map_inv, redHom_conjP, hbb', (hw i).1]
      simpa only [redSub_eq] using hbb1
    refine ⟨b, ?_, ?_⟩
    · have hval : MulAut.conj (w i) * (a : MulAut L') * (MulAut.conj (w i))⁻¹ = b.1 :=
        congrArg Subtype.val hcong
      exact hval
    · have hbb2' : (⟨redSub hker hAle b, ⟨b, rfl⟩⟩ : (redSub hker hAle).range) = bb :=
        Subtype.ext hb
      rw [hΦ_apply b, hΦ_apply a]
      exact (congrArg (fun z => Multiplicative.toAdd (Φb z)) hbb2').trans hbb2
  have hInnS : ∀ x ∈ NoOffRest.hypE6, ∃ t ∈ S, t ^ 3 = 1 ∧ ∃ b : A,
      MulAut.conj t = (b : MulAut L') ∧ Multiplicative.toAdd (Φ b) = x := by
    intro x hx
    obtain ⟨tb, htbT, htb3, bb, hbbconj, hbbx⟩ := hInn x hx
    obtain ⟨t, htS, htlift⟩ := hlift tb htbT
    refine ⟨t, htS, ?_, ?_⟩
    · have hcube_mem : t ^ 3 ∈ Z2 := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, htlift, htb3]
      exact hSbot _ (S.pow_mem htS 3) hcube_mem
    · obtain ⟨b, hb⟩ := bb.2
      have hbb' : (⟨redSub hker hAle b, ⟨b, rfl⟩⟩ : (redSub hker hAle).range) = bb := by
        apply Subtype.ext
        exact hb
      refine ⟨b, ?_, ?_⟩
      · have hcong : (conjP Z2 t : presZ Z2) = ⟨b.1, hAle b.2⟩ := by
          apply redHom_injective Z2 (twoSub_le_center hker) hperf
          rw [redHom_conjP, htlift]
          rw [show redHom Z2 ⟨b.1, hAle b.2⟩ = (bb : MulAut (L' ⧸ Z2)) from
            (redSub_eq hker hAle b) ▸ hb]
          exact hbbconj
        exact congrArg Subtype.val hcong
      · rw [hΦ_apply b]
        exact (congrArg (fun z => Multiplicative.toAdd (Φb z)) hbb').trans hbbx
  have hAut10S : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ u : WeylGroup .E6, ∀ a b : A,
        (b : MulAut L') = MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹ →
          Multiplicative.toAdd (Φ b) = adAct .E6 3 u (Multiplicative.toAdd (Φ a)) := by
    intro n hn
    obtain ⟨u, hu⟩ := hAut10 (n : L' ⧸ Z2) (hnorm_quot n hn)
    refine ⟨u, fun a b hab => ?_⟩
    have hprem : redSub hker hAle b =
        MulAut.conj (n : L' ⧸ Z2) * redSub hker hAle a * (MulAut.conj (n : L' ⧸ Z2))⁻¹ := by
      have hmem : MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hn (a : MulAut L')).mp a.2
      have h2 : (⟨MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹, hmem⟩ : A) = b :=
        Subtype.ext hab.symm
      rw [← h2]
      exact redSub_conj_triple hker hAle n a hmem
    have := hu ⟨redSub hker hAle a, ⟨a, rfl⟩⟩ ⟨redSub hker hAle b, ⟨b, rfl⟩⟩ hprem
    rwa [hΦ_apply b, hΦ_apply a]
  have hAut11S : ∀ α : MulAut L', α ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ (c : ZMod 3) (u : WeylGroup .E6), c ≠ 0 ∧ ∀ a b : A,
        (b : MulAut L') = α * (a : MulAut L') * α⁻¹ →
          Multiplicative.toAdd (Φ b) = c • adAct .E6 3 u (Multiplicative.toAdd (Φ a)) := by
    intro α hα
    have hpres : α ∈ presZ Z2 := by
      intro z hz
      refine ⟨?_, ?_⟩
      · rw [hZ, Subgroup.mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := α.surjective g
        calc α g' * α z = α (g' * z) := (map_mul α g' z).symm
          _ = α (z * g') := by rw [Subgroup.mem_center_iff.mp (twoSub_le_center hker hz) g']
          _ = α z * α g' := map_mul α z g'
      · rw [← map_pow, hz.2, map_one]
    let αb : MulAut (L' ⧸ Z2) := redHom Z2 ⟨α, hpres⟩
    have hb : αb ∈ Subgroup.normalizer (((redSub hker hAle).range : Subgroup (MulAut (L' ⧸ Z2))) :
        Set (MulAut (L' ⧸ Z2))) := by
      refine Subgroup.mem_normalizer_fintype (fun x hx => ?_)
      obtain ⟨a, rfl⟩ := hx
      have hmem : α * a.1 * α⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hα a.1).mp a.2
      refine ⟨⟨_, hmem⟩, ?_⟩
      have heq : (⟨α * a.1 * α⁻¹, hAle hmem⟩ : presZ Z2) =
          ⟨α, hpres⟩ * ⟨a.1, hAle a.2⟩ * ⟨α, hpres⟩⁻¹ := Subtype.ext rfl
      calc redSub hker hAle ⟨α * a.1 * α⁻¹, hmem⟩
          = redHom Z2 ⟨α * a.1 * α⁻¹, hAle hmem⟩ := rfl
        _ = redHom Z2 (⟨α, hpres⟩ * ⟨a.1, hAle a.2⟩ * ⟨α, hpres⟩⁻¹) := by rw [heq]
        _ = αb * redSub hker hAle a * αb⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            rfl
    obtain ⟨c, u, hc, hu⟩ := hAut11 αb hb
    refine ⟨c, u, hc, fun a b hab => ?_⟩
    have hprem : redSub hker hAle b = αb * redSub hker hAle a * αb⁻¹ := by
      have hmem : α * (a : MulAut L') * α⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hα (a : MulAut L')).mp a.2
      have h2 : (⟨α * (a : MulAut L') * α⁻¹, hmem⟩ : A) = b := Subtype.ext hab.symm
      rw [← h2]
      have heq : (⟨α * a.1 * α⁻¹, hAle hmem⟩ : presZ Z2) =
          ⟨α, hpres⟩ * ⟨a.1, hAle a.2⟩ * ⟨α, hpres⟩⁻¹ := Subtype.ext rfl
      calc redSub hker hAle ⟨α * a.1 * α⁻¹, hmem⟩
          = redHom Z2 ⟨α * a.1 * α⁻¹, hAle hmem⟩ := rfl
        _ = redHom Z2 (⟨α, hpres⟩ * ⟨a.1, hAle a.2⟩ * ⟨α, hpres⟩⁻¹) := by rw [heq]
        _ = αb * redSub hker hAle a * αb⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            rfl
    have := hu ⟨redSub hker hAle a, ⟨a, rfl⟩⟩ ⟨redSub hker hAle b, ⟨b, rfl⟩⟩ hprem
    rwa [hΦ_apply b, hΦ_apply a]
  have hOddS : Odd (Nat.card ψ.ker) → (∀ i, w i * w i = 1) ∧
      ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        ∃ v ∈ Subgroup.closure (Set.range w), n * v⁻¹ ∈ S := by
    intro hkodd
    have hZ2bot : Z2 = ⊥ := by
      apply le_antisymm _ bot_le
      intro z hz
      rw [Subgroup.mem_bot]
      exact twoSub_eq_one_of_odd hker hz
        (hkodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard ψ.ker hz.1))
    have hsq : ∀ i, w i * w i = 1 := by
      intro i
      have h1 := (hOdd12 (odd_card_ker_psi1 hker)).1 i
      have hmem : w i * w i ∈ Z2 := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, (hw i).1, h1]
      rw [hZ2bot, Subgroup.mem_bot] at hmem
      exact hmem
    refine ⟨hsq, fun n hn => ?_⟩
    obtain ⟨vb, hvb_closure, hvb_T⟩ :=
      (hOdd12 (odd_card_ker_psi1 hker)).2 (n : L' ⧸ Z2) (hnorm_quot n hn)
    have hmap : Subgroup.closure (Set.range wb) =
        (Subgroup.closure (Set.range w)).map (QuotientGroup.mk' Z2) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨w i, ⟨i, rfl⟩, (hw i).1⟩
      · rintro ⟨y, ⟨i, rfl⟩, hy⟩
        refine ⟨i, ?_⟩
        rw [QuotientGroup.mk'_apply] at hy
        rw [← hy, ← (hw i).1]
    have hmemmap : vb ∈ (Subgroup.closure (Set.range w)).map (QuotientGroup.mk' Z2) := by
      rw [← hmap]; exact hvb_closure
    obtain ⟨v, hv_closure, hvq⟩ := hmemmap
    rw [QuotientGroup.mk'_apply] at hvq
    refine ⟨v, hv_closure, (hSmem _).mpr ⟨?_, ?_⟩⟩
    · have h1 : ((n * v⁻¹ : L') : L' ⧸ Z2) = (n : L' ⧸ Z2) * vb⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hvq]
      rw [h1]; exact hvb_T
    · have hmemT : ((n * v⁻¹ : L') : L' ⧸ Z2) ∈ Tb := by
        have h1 : ((n * v⁻¹ : L') : L' ⧸ Z2) = (n : L' ⧸ Z2) * vb⁻¹ := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hvq]
        rw [h1]; exact hvb_T
      have hoddq : Odd (orderOf ((n * v⁻¹ : L') : L' ⧸ Z2)) := hTbodd _ hmemT
      have hinj : Function.Injective (QuotientGroup.mk' Z2) := by
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ2bot]
      have hEq := orderOf_injective (QuotientGroup.mk' Z2) hinj (n * v⁻¹)
      rw [QuotientGroup.mk'_apply] at hEq
      rw [← hEq]; exact hoddq
  exact ⟨Φ, S, w, hInj, hRange', hCommS, hZoddS, hFixS, hNormS, hCobS, hActS, hInnS,
    hAut10S, hAut11S, hOddS⟩

end CFSG.StandardType.E6ThreeModel
