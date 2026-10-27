module

public import CFSG.RankThree.PartOne.N143.GroupLemmas
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.RankThree.PartOne.N143

open scoped Pointwise

section Aux

variable {X : Type} [Group X] [Finite X]

theorem card_le_three_mul_inf_centralizer (V : Subgroup X) (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hexp : ∀ a ∈ V, a ^ 3 = 1) (hV : Nat.card V = 9) (S : Subgroup X) (hS : IsPGroup 3 S)
    (hnorm : ∀ y ∈ S, ∀ v ∈ V, y * v * y⁻¹ ∈ V) :
    Nat.card S ≤ 3 * Nat.card (S ⊓ Subgroup.centralizer (V : Set X) : Subgroup X) := by
  have hel : CFSG.IsElementaryAbelian 3 V := Torsion37.isElementaryAbelian_of_forall hcomm hexp
  have hle : S ≤ Subgroup.normalizer (V : Set X) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun n hn => hnorm y hy n hn
  let ρ : S →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hle)
  have h1 := card_le_three_mul_ker V hV hS ρ
  have h2 : Nat.card ρ.ker ≤ Nat.card (S ⊓ Subgroup.centralizer (V : Set X) : Subgroup X) := by
    have hsub : ρ.ker.map S.subtype ≤ S ⊓ Subgroup.centralizer (V : Set X) := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show (y : X) ∈ Subgroup.centralizer (V : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hρ : ρ y = 1 := hy
      have := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : X)) hρ
      simp only [ρ, MonoidHom.comp_apply] at this
      have h3 : y * v = v * y := by
        have : (y : X) * v * (y : X)⁻¹ = v := this
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      exact h3.symm
    calc Nat.card ρ.ker = Nat.card (ρ.ker.map S.subtype) :=
          (Subgroup.card_map_of_injective S.subtype_injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hsub
  exact h1.trans (Nat.mul_le_mul_left _ h2)


theorem mem_Pst_of_threePow {H : Type} [Group H] [Finite H] (hH : Nat.card H = 54)
    (Pst : Subgroup H) (hPcard : Nat.card Pst = 27) (hPmem : ∀ y : H, y ∈ Pst ↔ y ^ 3 = 1)
    {y : H} {n : ℕ} (hy : y ^ (3 ^ n) = 1) : y ∈ Pst := by
  have hnorm : Pst.Normal := ⟨fun m hm g => by
    rw [hPmem] at hm ⊢
    rw [conj_pow, hm, mul_one, mul_inv_cancel]⟩
  have hQcard : Nat.card (H ⧸ Pst) = 2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup Pst
    rw [hH, hPcard] at this
    omega
  have h2 : (QuotientGroup.mk y : H ⧸ Pst) ^ 2 = 1 := by
    rw [← hQcard]
    exact pow_card_eq_one'
  have h3 : (QuotientGroup.mk y : H ⧸ Pst) ^ (3 ^ n) = 1 := by
    rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one]
  have hcop : Nat.Coprime 2 (3 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have hd : orderOf (QuotientGroup.mk y : H ⧸ Pst) ∣ Nat.gcd 2 (3 ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [hcop] at hd
  have h1 : (QuotientGroup.mk y : H ⧸ Pst) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  exact (QuotientGroup.eq_one_iff y).1 h1

theorem factorization_three_fifty_four_mul (m : ℕ) (hm : m ≠ 0) :
    (54 * m).factorization 3 = 3 + m.factorization 3 := by
  rw [Nat.factorization_mul (by norm_num) hm, Finsupp.add_apply]
  have : (Nat.factorization 54) 3 = 3 := by decide +kernel
  rw [this]

end Aux

theorem caseA_false {X H : Type} [Group X] [Finite X] [Group H] [Finite H] (π : X →* H)
    (hπ : Function.Surjective π) (hH : Nat.card H = 54) (Pst : Subgroup H)
    (hPcard : Nat.card Pst = 27) (hPmem : ∀ y : H, y ∈ Pst ↔ y ^ 3 = 1) (zH : H) (hzH3 : zH ^ 3 = 1)
    (hzH1 : zH ≠ 1) (z : X) (hz3 : z ^ 3 = 1) (hzπ : π z = zH) {ι : Type} [Finite ι] [Nonempty ι]
    (A : ι → Subgroup H) (hAcard : ∀ i, Nat.card (A i) = 9)
    (hAP : ∀ i, A i ≤ Pst) (V : ι → Subgroup X) (hVker : ∀ i, V i ≤ π.ker)
    (hVcomm : ∀ i, ∀ a ∈ V i, ∀ b ∈ V i, a * b = b * a) (hVexp : ∀ i, ∀ a ∈ V i, a ^ 3 = 1)
    (hVcard : ∀ i, Nat.card (V i) = 9)
    (hVnormK : ∀ i, ∀ x ∈ π.ker, ∀ v ∈ V i, x * v * x⁻¹ ∈ V i)
    (hVnorm : ∀ i, ∀ y : X, π y ∈ A i → ∀ v ∈ V i, y * v * y⁻¹ ∈ V i)
    (hLemA : ∀ i, ∀ y : X, π y ∈ A i → π y ∉ Subgroup.zpowers zH → ∃ v ∈ V i, y * v * y⁻¹ ≠ v)
    (hcover : ∀ y ∈ Pst, y ∉ Subgroup.zpowers zH → ∃ i, y ∈ A i)
    (hconj : ∀ (x : X) (i : ι), ∃ j, ∀ v ∈ V i, x * v * x⁻¹ ∈ V j)
    (hrank : ∀ E : Subgroup X, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 3 = 1) →
      (∀ e ∈ E, π e ∈ Subgroup.zpowers zH) → Nat.card E ≤ 27) : False := by
  classical
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z : Subgroup H := Subgroup.zpowers zH with hZdef
  set K : Subgroup X := π.ker with hKdef
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Nat.card_zpowers]
    exact orderOf_eq_prime hzH3 hzH1
  have hzZ : π z ∈ Z := by
    rw [hzπ]
    exact Subgroup.mem_zpowers zH
  have hzpg : IsPGroup 3 (Subgroup.zpowers z) := by
    have hord : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show orderOf z ∣ 3 ^ 1 from by simpa using hord)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨P, hzP⟩ := hzpg.exists_le_sylow
  set P' : Subgroup X := (P : Subgroup X) with hP'
  have hP'pg : IsPGroup 3 P' := P.isPGroup'
  have hzmem : z ∈ P' := hzP (Subgroup.mem_zpowers z)
  have hXcard : Nat.card X = 54 * Nat.card K := by
    have h := card_eq_range_mul_ker π
    rw [MonoidHom.range_eq_top_of_surjective π hπ, Subgroup.card_top, hH] at h
    exact h
  have hKpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hPcard' : Nat.card P' = 27 * 3 ^ (Nat.card K).factorization 3 := by
    have := P.card_eq_multiplicity
    rw [hXcard, factorization_three_fifty_four_mul _ hKpos, pow_add] at this
    simpa using this
  set v := (Nat.card K).factorization 3 with hv
  have hQle : Nat.card (P' ⊓ K : Subgroup X) ≤ 3 ^ v := by
    have hpgQ : IsPGroup 3 (P' ⊓ K : Subgroup X) := hP'pg.to_le inf_le_left
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hpgQ
    have hdvd : 3 ^ a ∣ Nat.card K := by
      rw [← ha]
      exact Subgroup.card_dvd_of_le inf_le_right
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hKpos).1 hdvd
    rw [ha]
    exact Nat.pow_le_pow_right (by norm_num) this
  have hmapPst : P'.map π ≤ Pst := by
    have hpgm : IsPGroup 3 (P'.map π) := hP'pg.map π
    intro y hy
    obtain ⟨n, hn⟩ := hpgm ⟨y, hy⟩
    refine mem_Pst_of_threePow hH Pst hPcard hPmem (n := n) ?_
    simpa using congrArg Subtype.val hn
  have hmapLe : Nat.card (P'.map π) ≤ 27 := hPcard ▸ Subgroup.card_le_of_le hmapPst
  have hcnt : Nat.card P' = Nat.card (P'.map π) * Nat.card (P' ⊓ K : Subgroup X) :=
    card_eq_map_mul_inf_ker π P'
  rw [hPcard'] at hcnt
  have h3v : 0 < 3 ^ v := by positivity
  have hQeq : Nat.card (P' ⊓ K : Subgroup X) = 3 ^ v := by
    by_contra hne
    have hlt : Nat.card (P' ⊓ K : Subgroup X) < 3 ^ v := lt_of_le_of_ne hQle hne
    have : Nat.card (P'.map π) * Nat.card (P' ⊓ K : Subgroup X) < 27 * 3 ^ v := by
      calc _ ≤ 27 * Nat.card (P' ⊓ K : Subgroup X) := Nat.mul_le_mul_right _ hmapLe
        _ < 27 * 3 ^ v := Nat.mul_lt_mul_of_pos_left hlt (by norm_num)
    omega
  have hmap27 : Nat.card (P'.map π) = 27 := by
    rw [hQeq] at hcnt
    exact (Nat.eq_of_mul_eq_mul_right h3v hcnt).symm
  have hmapEq : P'.map π = Pst :=
    Subgroup.eq_of_le_of_card_ge hmapPst (by rw [hmap27, hPcard])
  set R0 : Subgroup X := P' ⊓ Z.comap π with hR0
  have hKcomapA : ∀ i, K ≤ (A i).comap π := fun i k hk => by
    have : π k = 1 := hk
    show π k ∈ A i
    rw [this]
    exact (A i).one_mem
  have hKcomapZ : K ≤ Z.comap π := fun k hk => by
    have : π k = 1 := hk
    show π k ∈ Z
    rw [this]
    exact Z.one_mem
  have hzR0 : z ∈ R0 := ⟨hzmem, hzZ⟩
  have hR0K : R0 ⊓ K = P' ⊓ K := by
    ext x
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, hKcomapZ h3⟩, h3⟩
  have hR0map : R0.map π = Z := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · rw [hZdef, Subgroup.zpowers_le]
      exact ⟨z, hzR0, hzπ⟩
  have hR0card : Nat.card R0 = 3 * 3 ^ v := by
    have this : Nat.card R0 = Nat.card (R0.map π) * Nat.card (R0 ⊓ K : Subgroup X) :=
      card_eq_map_mul_inf_ker π R0
    rw [hR0map, hZcard, hR0K, hQeq] at this
    exact this
  have hPi_card : ∀ i, Nat.card (P' ⊓ (A i).comap π : Subgroup X) = 9 * 3 ^ v := by
    intro i
    have hmapi : (P' ⊓ (A i).comap π).map π = A i := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
        exact hx
      · intro a ha
        have : a ∈ P'.map π := by
          rw [hmapEq]
          exact hAP i ha
        obtain ⟨u, hu, rfl⟩ := this
        exact ⟨u, ⟨hu, ha⟩, rfl⟩
    have hKi : (P' ⊓ (A i).comap π) ⊓ K = P' ⊓ K := by
      ext x
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, hKcomapA i h3⟩, h3⟩
    have this : Nat.card (P' ⊓ (A i).comap π : Subgroup X) =
        Nat.card ((P' ⊓ (A i).comap π).map π) *
          Nat.card ((P' ⊓ (A i).comap π) ⊓ K : Subgroup X) :=
      card_eq_map_mul_inf_ker π (P' ⊓ (A i).comap π)
    rw [hmapi, hAcard i, hKi, hQeq] at this
    exact this
  have hVP : ∀ i, V i ≤ P' := fun i => by
    have hVpg : IsPGroup 3 (V i) := fun g => ⟨1, by
      apply Subtype.ext
      simpa using hVexp i g g.2⟩
    have hQpg : IsPGroup 3 (P' ⊓ K : Subgroup X) := hP'pg.to_le inf_le_left
    have hQnorm : (P' ⊓ K : Subgroup X) ≤ Subgroup.normalizer (V i : Set X) := fun x hx =>
      Subgroup.mem_normalizer_fintype fun n hn => hVnormK i x hx.2 n hn
    have hsup : IsPGroup 3 (V i ⊔ (P' ⊓ K) : Subgroup X) :=
      hVpg.to_sup_of_normal_left' hQpg hQnorm
    have hsupK : V i ⊔ (P' ⊓ K) ≤ K := sup_le (hVker i) inf_le_right
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hsup
    have hdvd : 3 ^ a ∣ Nat.card K := by
      rw [← ha]
      exact Subgroup.card_dvd_of_le hsupK
    have hav := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hKpos).1 hdvd
    have hle : Nat.card (V i ⊔ (P' ⊓ K) : Subgroup X) ≤ Nat.card (P' ⊓ K : Subgroup X) := by
      rw [ha, hQeq]
      exact Nat.pow_le_pow_right (by norm_num) hav
    have heq : (P' ⊓ K : Subgroup X) = V i ⊔ (P' ⊓ K) :=
      Subgroup.eq_of_le_of_card_ge le_sup_right hle
    exact (le_sup_left.trans heq.ge).trans inf_le_left
  have hVR0 : ∀ i, V i ≤ R0 := fun i x hx => by
    refine ⟨hVP i hx, ?_⟩
    show π x ∈ Z
    rw [show π x = 1 from hVker i hx]
    exact Z.one_mem
  have hCi_le : ∀ i, (P' ⊓ (A i).comap π) ⊓ Subgroup.centralizer (V i : Set X) ≤ R0 := by
    intro i y hy
    obtain ⟨⟨hyP, hyA⟩, hyC⟩ := hy
    refine ⟨hyP, ?_⟩
    show π y ∈ Z
    by_contra hnZ
    obtain ⟨v, hv, hne⟩ := hLemA i y hyA hnZ
    apply hne
    have := Subgroup.mem_centralizer_iff.1 hyC v hv
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hCi_ge : ∀ i, 3 * 3 ^ v ≤
      Nat.card ((P' ⊓ (A i).comap π) ⊓ Subgroup.centralizer (V i : Set X) : Subgroup X) := by
    intro i
    have hpg : IsPGroup 3 (P' ⊓ (A i).comap π : Subgroup X) := hP'pg.to_le inf_le_left
    have h := card_le_three_mul_inf_centralizer (V i) (hVcomm i) (hVexp i) (hVcard i) _ hpg
      (fun y hy v hv => hVnorm i y hy.2 v hv)
    rw [hPi_card i] at h
    omega
  have hCi_eq : ∀ i,
      (P' ⊓ (A i).comap π) ⊓ Subgroup.centralizer (V i : Set X) = R0 := fun i =>
    Subgroup.eq_of_le_of_card_ge (hCi_le i) (by rw [hR0card]; exact hCi_ge i)
  have hR0cent : ∀ i, ∀ y ∈ R0, ∀ w ∈ V i, w * y = y * w := by
    intro i y hy w hw
    have : y ∈ (P' ⊓ (A i).comap π) ⊓ Subgroup.centralizer (V i : Set X) := by
      rw [hCi_eq i]
      exact hy
    exact Subgroup.mem_centralizer_iff.1 this.2 w hw
  set S : Set X := ⋃ i, (V i : Set X) with hS
  set Vc : Subgroup X := Subgroup.closure S with hVc
  have hmemS : ∀ a ∈ S, ∃ i, a ∈ V i := by
    intro a ha
    obtain ⟨_, ⟨i, rfl⟩, hai⟩ := ha
    exact ⟨i, hai⟩
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, hai⟩ := hmemS a ha
    obtain ⟨j, hbj⟩ := hmemS b hb
    exact (hR0cent j a (hVR0 i hai) b hbj).symm
  have hSexp : ∀ a ∈ S, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨i, hai⟩ := hmemS a ha
    exact hVexp i a hai
  obtain ⟨hVccomm, hVcexp⟩ := closure_comm_exp' (p := 3) S hScomm hSexp
  have hSsub : S ⊆ (Vc : Set X) := Subgroup.subset_closure
  have hViLe : ∀ i, V i ≤ Vc := fun i x hx =>
    Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, hx⟩)
  have hVcKer : Vc ≤ K := (Subgroup.closure_le _).2 fun a ha => by
    obtain ⟨i, hai⟩ := hmemS a ha
    exact hVker i hai
  have hzScomm : ∀ a ∈ S, a * z = z * a := by
    intro a ha
    obtain ⟨i, hai⟩ := hmemS a ha
    exact hR0cent i z hzR0 a hai
  have hzcomm : ∀ a ∈ Vc, a * z = z * a := by
    intro a ha
    have hle : Vc ≤ Subgroup.centralizer {z} := (Subgroup.closure_le _).2 fun b hb => by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hzScomm b hb).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) z rfl).symm
  set S' : Set X := S ∪ {z} with hS'
  have hS'comm : ∀ a ∈ S', ∀ b ∈ S', a * b = b * a := by
    intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hScomm a ha b hb
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact hzScomm a ha
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact (hzScomm b hb).symm
    · rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
  have hS'exp : ∀ a ∈ S', a ^ 3 = 1 := by
    intro a ha
    rcases ha with ha | ha
    · exact hSexp a ha
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hz3
  obtain ⟨hEcomm, hEexp⟩ := closure_comm_exp' (p := 3) S' hS'comm hS'exp
  set E : Subgroup X := Subgroup.closure S' with hE
  have hEπ : ∀ e ∈ E, π e ∈ Z := by
    have hle : E ≤ Z.comap π := (Subgroup.closure_le _).2 fun a ha => by
      rcases ha with ha | ha
      · obtain ⟨i, hai⟩ := hmemS a ha
        show π a ∈ Z
        rw [show π a = 1 from hVker i hai]
        exact Z.one_mem
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hzZ
    exact fun e he => hle he
  have hErank : Nat.card E ≤ 27 := hrank E hEcomm hEexp hEπ
  have hzVc : z ∉ Vc := fun h => hzH1 (by rw [← hzπ]; exact hVcKer h)
  have hsup := Planes.card_sup_zpowers Nat.prime_three Vc hz3 hzVc hzcomm
  have hsupLe : Vc ⊔ Subgroup.zpowers z ≤ E :=
    sup_le (Subgroup.closure_mono Set.subset_union_left)
      (Subgroup.zpowers_le.2 (Subgroup.subset_closure (Or.inr rfl)))
  have hVcle : Nat.card Vc ≤ 9 := by
    have := Subgroup.card_le_of_le hsupLe
    rw [hsup] at this
    omega
  have hVeq : ∀ i, V i = Vc := fun i =>
    Subgroup.eq_of_le_of_card_ge (hViLe i) (by rw [hVcard i]; exact hVcle)
  have hVi0 : ∀ i, V i = V i₀ := fun i => (hVeq i).trans (hVeq i₀).symm
  have hPnorm : ∀ x ∈ P', ∀ w ∈ V i₀, x * w * x⁻¹ ∈ V i₀ := by
    intro x _ w hw
    obtain ⟨j, hj⟩ := hconj x i₀
    rw [← hVi0 j]
    exact hj w hw
  have hKP := card_le_three_mul_inf_centralizer (V i₀) (hVcomm i₀) (hVexp i₀) (hVcard i₀) P'
    hP'pg hPnorm
  set KP : Subgroup X := P' ⊓ Subgroup.centralizer (V i₀ : Set X) with hKP'
  have hKPge : 9 * 3 ^ v ≤ Nat.card KP := by
    rw [hPcard'] at hKP
    omega
  have hKPcnt : Nat.card KP = Nat.card (KP.map π) * Nat.card (KP ⊓ K : Subgroup X) :=
    card_eq_map_mul_inf_ker π KP
  have hKPK : Nat.card (KP ⊓ K : Subgroup X) ≤ 3 ^ v := by
    have : KP ⊓ K ≤ P' ⊓ K := inf_le_inf_right _ inf_le_left
    exact (Subgroup.card_le_of_le this).trans hQeq.le
  have hmapKP : 9 ≤ Nat.card (KP.map π) := by
    by_contra hlt
    push Not at hlt
    have h8 : Nat.card KP ≤ 8 * 3 ^ v := by
      rw [hKPcnt]
      calc _ ≤ 8 * Nat.card (KP ⊓ K : Subgroup X) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 8 * 3 ^ v := Nat.mul_le_mul_left _ hKPK
    omega
  have hexists : ∃ y ∈ KP, π y ∉ Z := by
    by_contra hall
    push Not at hall
    have hle : KP.map π ≤ Z := by
      rintro _ ⟨y, hy, rfl⟩
      exact hall y hy
    have := Subgroup.card_le_of_le hle
    rw [hZcard] at this
    omega
  obtain ⟨y, hyKP, hyZ⟩ := hexists
  have hyPst : π y ∈ Pst := by
    rw [← hmapEq]
    exact ⟨y, hyKP.1, rfl⟩
  obtain ⟨i, hi⟩ := hcover (π y) hyPst hyZ
  obtain ⟨w, hw, hne⟩ := hLemA i y hi hyZ
  apply hne
  have hw' : w ∈ V i₀ := by
    rw [← hVi0 i]
    exact hw
  have := Subgroup.mem_centralizer_iff.1 hyKP.2 w hw'
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm


theorem caseA_false_range {X H : Type} [Group X] [Finite X] [Group H] (π : X →* H)
    (hR : Nat.card π.range = 54) (Pst : Subgroup H) (hPR : Pst ≤ π.range)
    (hPcard : Nat.card Pst = 27) (hPmem : ∀ y ∈ π.range, y ∈ Pst ↔ y ^ 3 = 1) (zH : H)
    (hzH3 : zH ^ 3 = 1) (hzH1 : zH ≠ 1) (z : X) (hz3 : z ^ 3 = 1) (hzπ : π z = zH)
    {ι : Type} [Finite ι] [Nonempty ι] (A : ι → Subgroup H) (hAcard : ∀ i, Nat.card (A i) = 9)
    (hAP : ∀ i, A i ≤ Pst) (V : ι → Subgroup X) (hVker : ∀ i, V i ≤ π.ker)
    (hVcomm : ∀ i, ∀ a ∈ V i, ∀ b ∈ V i, a * b = b * a) (hVexp : ∀ i, ∀ a ∈ V i, a ^ 3 = 1)
    (hVcard : ∀ i, Nat.card (V i) = 9)
    (hVnormK : ∀ i, ∀ x ∈ π.ker, ∀ v ∈ V i, x * v * x⁻¹ ∈ V i)
    (hVnorm : ∀ i, ∀ y : X, π y ∈ A i → ∀ v ∈ V i, y * v * y⁻¹ ∈ V i)
    (hLemA : ∀ i, ∀ y : X, π y ∈ A i → π y ∉ Subgroup.zpowers zH → ∃ v ∈ V i, y * v * y⁻¹ ≠ v)
    (hcover : ∀ y ∈ Pst, y ∉ Subgroup.zpowers zH → ∃ i, y ∈ A i)
    (hconj : ∀ (x : X) (i : ι), ∃ j, ∀ v ∈ V i, x * v * x⁻¹ ∈ V j)
    (hrank : ∀ E : Subgroup X, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 3 = 1) →
      (∀ e ∈ E, π e ∈ Subgroup.zpowers zH) → Nat.card E ≤ 27) : False := by
  classical
  set R : Subgroup H := π.range with hRdef
  let π' : X →* ↥R := π.rangeRestrict
  have hπ' : Function.Surjective π' := π.rangeRestrict_surjective
  have : Finite ↥R := Finite.of_surjective π' hπ'
  have hker : π'.ker = π.ker := MonoidHom.ker_rangeRestrict π
  have hπ'val : ∀ x : X, ((π' x : ↥R) : H) = π x := fun x => rfl
  have hzR : zH ∈ R := ⟨z, hzπ⟩
  have hzmem : ∀ y : ↥R, y ∈ Subgroup.zpowers (⟨zH, hzR⟩ : ↥R) ↔ (y : H) ∈ Subgroup.zpowers zH := by
    intro y
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa using congrArg Subtype.val hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext (by simpa using hi)⟩
  refine caseA_false π' hπ' hR (Pst.subgroupOf R) ?_ ?_ ⟨zH, hzR⟩ ?_ ?_ z hz3 ?_
    (fun i => (A i).subgroupOf R) ?_ ?_ V ?_ hVcomm hVexp hVcard ?_ ?_ ?_ ?_ ?_ ?_
  · rw [card_subgroupOf_of_le hPR]
    exact hPcard
  · intro y
    rw [Subgroup.mem_subgroupOf, hPmem y y.2]
    constructor
    · intro h
      exact Subtype.ext (by simpa using h)
    · intro h
      simpa using congrArg Subtype.val h
  · exact Subtype.ext hzH3
  · intro h
    exact hzH1 (congrArg Subtype.val h)
  · exact Subtype.ext hzπ
  · intro i
    rw [card_subgroupOf_of_le ((hAP i).trans hPR)]
    exact hAcard i
  · intro i y hy
    exact (hAP i) hy
  · intro i
    rw [hker]
    exact hVker i
  · intro i x hx v hv
    rw [hker] at hx
    exact hVnormK i x hx v hv
  · intro i y hy v hv
    exact hVnorm i y hy v hv
  · intro i y hy hnz
    refine hLemA i y hy fun h => hnz ?_
    exact (hzmem (π' y)).2 h
  · intro y hy hnz
    obtain ⟨i, hi⟩ := hcover y hy fun h => hnz ((hzmem y).2 h)
    exact ⟨i, hi⟩
  · exact hconj
  · intro E hc he hπE
    exact hrank E hc he fun e heE => (hzmem (π' e)).1 (hπE e heE)


end CFSG.RankThree.PartOne.N143
