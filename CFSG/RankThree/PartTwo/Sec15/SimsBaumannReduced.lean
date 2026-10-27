module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannCases
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

variable {X : Type} [Group X] [Finite X]

private theorem sbred_oResidual_normal (Y : Type*) [Group Y] : (oResidual 2 Y).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ?_
    have h : orderOf (g * y * g⁻¹) = orderOf y := by
      simpa using (MulAut.conj g).orderOf_eq y
    change Nat.Coprime (orderOf (g * y * g⁻¹)) 2
    rw [h]
    exact hy
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using Subgroup.mul_mem _ ihx ihy
  | inv x _ ih => simpa [mul_assoc] using Subgroup.inv_mem _ ih

private theorem sbred_exists_pow_mem {Y : Type*} [Group Y] [Finite Y] (y : Y) :
    ∃ a : ℕ, y ^ 2 ^ a ∈ oResidual 2 Y := by
  obtain ⟨a, m, hm, hmn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨a, Subgroup.subset_closure ?_⟩
  have hdvd : orderOf (y ^ 2 ^ a) ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hmn, pow_orderOf_eq_one])
  exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr hm)

private theorem sbred_pCore_quotient (Y : Type*) [Group Y] :
    CFSG.pCore 2 (Y ⧸ CFSG.pCore 2 Y) = ⊥ := by
  set N : Subgroup Y := CFSG.pCore 2 Y with hN
  set K : Subgroup Y := (CFSG.pCore 2 (Y ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := Y ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := Y) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

private theorem sbred_centralizer_normal {Y : Type*} [Group Y] (N : Subgroup Y) [hN : N.Normal] :
    (Subgroup.centralizer (N : Set Y)).Normal := by
  refine ⟨fun c hc g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro n hn
  have hn' : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
  have key := hc _ hn'
  calc n * (g * c * g⁻¹) = g * ((g⁻¹ * n * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * n := by group

private theorem sbred_mem_of_pow {Y : Type*} [Group Y] (N : Subgroup Y) [N.Normal] {x d : Y}
    {n k : ℕ} (hn : Nat.Coprime n 2) (hx : x ^ n ∈ N) (hd : d ^ 2 ^ k ∈ N)
    (hxd : d⁻¹ * x ∈ N) : x ∈ N := by
  have h1 : (x : Y ⧸ N) = d := (QuotientGroup.eq.mpr hxd).symm
  have h2 : (x : Y ⧸ N) ^ n = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hx
  have h3 : (x : Y ⧸ N) ^ 2 ^ k = 1 := by
    rw [h1, ← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hd
  have h4 : orderOf (x : Y ⧸ N) ∣ Nat.gcd n (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [(Nat.Coprime.pow_right k hn).gcd_eq_one] at h4
  have h5 : (x : Y ⧸ N) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  exact (QuotientGroup.eq_one_iff x).mp h5

private theorem sbred_odd_of_centralizer {Y : Type*} [Group Y] [Finite Y]
    (hY : CFSG.pCore 2 Y = ⊥) {c : Y}
    (hc : c ∈ Subgroup.centralizer (oResidual 2 Y : Set Y)) : Nat.Coprime (orderOf c) 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hLn : (oResidual 2 Y).Normal := sbred_oResidual_normal Y
  haveI hCn : (Subgroup.centralizer (oResidual 2 Y : Set Y)).Normal :=
    sbred_centralizer_normal (oResidual 2 Y)
  set C := Subgroup.centralizer (oResidual 2 Y : Set Y)
  have hp : IsPGroup 2 (Y ⧸ oResidual 2 Y) := by
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨a, ha⟩ := sbred_exists_pow_mem y
    exact ⟨a, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact ha⟩
  haveI : Group.IsNilpotent (Y ⧸ oResidual 2 Y) := hp.isNilpotent
  let f : C →* Y ⧸ oResidual 2 Y := (QuotientGroup.mk' (oResidual 2 Y)).comp C.subtype
  have hker : f.ker ≤ Subgroup.center C := by
    intro x hx
    have hxL : (x : Y) ∈ oResidual 2 Y := by
      rw [MonoidHom.mem_ker] at hx
      exact (QuotientGroup.eq_one_iff _).mp hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp g.2) x hxL).symm
  haveI : Group.IsNilpotent C := Subgroup.isNilpotent_of_ker_le_center f hker
  by_contra hodd
  have h2 : 2 ∣ orderOf c := by
    rw [Nat.coprime_two_right, Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    exact hodd
  have heo : orderOf (c ^ (orderOf c / 2)) = 2 := orderOf_pow_orderOf_div (orderOf_pos c).ne' h2
  have heC : c ^ (orderOf c / 2) ∈ C := C.pow_mem hc _
  have he'o : orderOf (⟨c ^ (orderOf c / 2), heC⟩ : C) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact heo
  have hz : IsPGroup 2 (Subgroup.zpowers (⟨c ^ (orderOf c / 2), heC⟩ : C)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he'o, pow_one])
  obtain ⟨P, hP⟩ := hz.exists_le_sylow
  have hPC : P.map C.subtype ≤ CFSG.pCore 2 Y := Sylow.map_le_pCore hCn inferInstance 2 P
  rw [hY] at hPC
  have hmem : c ^ (orderOf c / 2) ∈ P.map C.subtype :=
    ⟨⟨c ^ (orderOf c / 2), heC⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  have he1 : c ^ (orderOf c / 2) = 1 := Subgroup.mem_bot.mp (hPC hmem)
  rw [he1, orderOf_one] at heo
  exact absurd heo (by norm_num)

private theorem sbred_omegaOneCenterOf_normal {Y : Type*} [Group Y] (R : Subgroup Y)
    [hR : R.Normal] : (CFSG.Quasithin.omegaOneCenterOf R).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    have hc : g * y * g⁻¹ ∈ Subgroup.centralizer (R : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : g⁻¹ * r * g ∈ R := by simpa using hR.conj_mem r hr g⁻¹
      have key := Subgroup.mem_centralizer_iff.mp hy.1.2 _ hr'
      calc r * (g * y * g⁻¹) = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by rw [key]
        _ = g * y * g⁻¹ * r := by group
    have hsq : (g * y * g⁻¹) ^ 2 = 1 := by
      calc (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := conj_pow
        _ = 1 := by rw [hy.2]; group
    exact Subgroup.subset_closure ⟨⟨hR.conj_mem y hy.1.1 g, hc⟩, hsq⟩
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using Subgroup.mul_mem _ ihx ihy
  | inv x _ ih => simpa [mul_assoc] using Subgroup.inv_mem _ ih

private theorem sbred_omegaOneCenterOf_le {Y : Type*} [Group Y] (R : Subgroup Y) :
    CFSG.Quasithin.omegaOneCenterOf R ≤ CFSG.Quasithin.centerOf R :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

private theorem sbred_isElemAbelian {Y : Type*} [Group Y] (R : Subgroup Y) :
    CFSG.Open.IsElemAbelian 2 (CFSG.Quasithin.omegaOneCenterOf R) := by
  have hle := sbred_omegaOneCenterOf_le R
  have hcomm : ∀ x ∈ CFSG.Quasithin.omegaOneCenterOf R, ∀ y ∈ CFSG.Quasithin.omegaOneCenterOf R,
      x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hle hy).2 x (hle hx).1
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (hcomm x hx y hy) 2, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem isTwoReducedIn_W315 (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    CFSG.Quasithin.IsTwoReducedIn ⊤ (W315 X) := by
  haveI hWn : (W315 X).Normal := sbred_omegaOneCenterOf_normal (CFSG.pCore 2 X)
  refine ⟨le_top, (Subgroup.normalizer_eq_top_iff.mpr hWn).ge,
    sbred_isElemAbelian (CFSG.pCore 2 X), ?_⟩
  intro D _ hDN hD
  have hDn : D.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hDN)
  haveI hCWn : (Subgroup.centralizer (W315 X : Set X)).Normal := sbred_centralizer_normal _
  have hQC : CFSG.pCore 2 X ≤ Subgroup.centralizer (W315 X : Set X) := by
    intro q hq'
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact ((Subgroup.mem_centralizer_iff.mp (sbred_omegaOneCenterOf_le _ hw).2) q hq').symm
  have hLC : ¬ oResidual 2 X ≤ Subgroup.centralizer (W315 X : Set X) := by
    intro h
    refine hWL ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h
  have hLbn : (oResidual 2 (X ⧸ CFSG.pCore 2 X)).Normal := sbred_oResidual_normal _
  have hDb : (D.map (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal :=
    hDn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.component_normal_subgroup
      (K := oResidual 2 (X ⧸ CFSG.pCore 2 X)) ⟨hq, hLbn.isSubnormal⟩ hDb with h | h
  ·
    exfalso
    refine hLC ?_
    rw [oResidual, Subgroup.closure_le]
    intro x hx
    have hxL : QuotientGroup.mk' (CFSG.pCore 2 X) x ∈ oResidual 2 (X ⧸ CFSG.pCore 2 X) :=
      Subgroup.subset_closure (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ x) hx)
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp (h hxL)
    obtain ⟨k, hk⟩ := hD d hd
    have hdx' : (d : X ⧸ CFSG.pCore 2 X) = x := hdx
    exact sbred_mem_of_pow _ hx (by rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _) hk
      (hQC (QuotientGroup.eq.mp hdx'))
  ·
    intro d hd
    obtain ⟨k, hk⟩ := hD d hd
    rw [Subgroup.commutator_comm] at h
    have hDc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hodd := sbred_odd_of_centralizer (sbred_pCore_quotient X)
      (hDc (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 X)) hd))
    have hdr : d ^ orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) d) ∈ CFSG.pCore 2 X := by
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 X)) (d ^ orderOf
          (QuotientGroup.mk' (CFSG.pCore 2 X) d)) = 1 := by
        rw [map_pow, pow_orderOf_eq_one]
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact sbred_mem_of_pow _ hodd (hQC hdr) hk (by simp)

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
